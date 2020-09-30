#![feature(box_syntax, box_patterns, bindings_after_at, move_ref_pattern)]

use core::ops::RangeInclusive;
use core::option::Option::{
    None as Uninit,
    Some as Init,
};

/// The compilation target is either big or little endian.
#[derive(Clone, Copy)]
pub enum Endian {
    Big,
    Little,
}

/// Represents a type's layout.
#[derive(Clone)]
pub enum Layout {
    /// An `Atom` is any layout that isn't a `Sum` or `Prod`.
    Atom(LayoutAtom),
    /// A `Sum` represents a choice between two alternative layouts.
    Sum(Box<Layout>, Box<Layout>),
    /// A `Prod` represents a sequence of two successive layouts.
    Prod(Box<Layout>, Box<Layout>),
}

#[derive(Clone)]
pub enum LayoutAtom {
    /// An uninhabited type.
    Void,
    /// A zero-sized type.
    Epsilon,
    /// A byte.
    Byte(Option<RangeInclusive<u8>>),
}

#[derive(Clone, Copy)]
pub struct Params {
    pub endian: Endian,
}

pub fn transmutable(src: Layout, dst: Layout, params: Params) -> bool {
    use Layout::*;
    use LayoutAtom::*;

    match (src, dst) {
        // If the `src` is a choice between two layouts, both must be
        // transmutable into `dst`.
        (Sum(box l, box r), dst) =>
            transmutable(l, dst.clone(), params)
              && transmutable(r, dst, params),

        // If the `dst` is a choice between two layouts, at least one of the
        // layouts must be transmutable from the `dst`.
        //
        // Unfortunately, this rule alone is overly-restrictive in cases where
        // the `dst` variants could be combined. Consider transmuting the `src`:
        //    `Bytes(1, Initialized { min: 0, max: 255 })`
        // ...into the `dst`:
        // ```
        //    Sum(
        //      Bytes(1, Initialized { min:   0, max: 127 }),
        //      Bytes(1, Initialized { min: 128, max: 255 }))
        // ```
        //
        // The `src` is not transmutable into either variant of the `dst` when
        // considered independently. TODO: How to account for this?
        (src, Sum(box l, box r)) =>
            transmutable(src.clone(), l, params)
              || transmutable(src, r, params),

        // The `Void` layout is transmutable into anything.
        //
        // Unfortunately, this rule alone is overly-restrictive in cases where
        // `Void` is not at the 'front' of the layout. TODO: an `is_uninhabited`
        // predicate.
        (Prod(box Atom(Void), box _src_t), _dst@Prod(..)) =>
            true,

        // The `Void` layout is *not* transmutable *from* anything.
        (Prod(..), Prod(box Atom(Void), ..)) =>
            false,

        (Prod(box Atom(Byte(ref src_kind)), src_t)
        ,Prod(box Atom(Byte(ref dst_kind)), dst_t)) =>
            (match (src_kind, dst_kind) {
                // Initialized Bytes cannot be constructed
                // from Uninitialized Bytes
                (Uninit, Init(..)) => false,

                // UninitializedBbytes can be constructed from
                // either Initialized Bytes or Uninitialized bytes
                (Uninit, Uninit) | (Init(..), Uninit) => true,

                // Initialized Bytes are transmutable only into
                // Initialized Bytes whose validity subsumes src.
                (Init(src), Init(dst)) => (src.start() >= dst.start() && src.end() <= dst.end()),
            }) && transmutable(*src_t, *dst_t, params),

        /* algebraic transformations of src and dst */
        // these tactics are applied only if none of the previous tactics are
        // applicable, to avoid cyclic transformations
        
        // distribute src
        (Prod(a, box Sum(b, c)), dst) | (Prod(box Sum(b, c), a), dst) =>
            transmutable(Sum(box Prod(a.clone(), b), box Prod(a, c)), dst, params),

        // distribute dst
        (src, Prod(a, box Sum(b, c))) | (src, Prod(box Sum(b, c), a)) =>
            transmutable(src, Sum(box Prod(a.clone(), b), box Prod(a, c)), params),

        // wrap atom in prod with epsilon
        (src@Atom(..), dst) =>
            transmutable(Prod(box src, box Atom(Epsilon)), dst, params),

        // wrap atom in prod with epsilon
        (src, dst@Atom(..)) =>
            transmutable(src, Prod(box dst, box Atom(Epsilon)), params),

        // remove epsilon from src
        (Prod(box Atom(Epsilon), box l), dst) | (Prod(box l, box Atom(Epsilon)), dst) =>
            transmutable(l, dst, params),

        // remove epsilon from dst
        (src, Prod(box Atom(Epsilon), box l)) | (src, Prod(box l, box Atom(Epsilon))) =>
            transmutable(src, l, params),

        // re-associate src
        (Prod(box Prod(a, b), c), dst) =>
            transmutable(Prod(a, box Prod(b, c)), dst, params),

        // re-associate dst
        (src, Prod(box Prod(a, b), c)) =>
            transmutable(src, Prod(a, box Prod(b, c)), params),
    }
}
