#![feature(box_syntax, box_patterns, bindings_after_at, move_ref_pattern)]

use core::num::NonZeroU8;
use core::cmp::Ordering::{*};
use core::convert::TryInto;

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

#[derive(Clone, Copy)]
pub enum LayoutAtom {
    /// An uninhabited type.
    Void,
    /// A zero-sized type.
    Epsilon,
    /// A non-empty sequence of bytes.
    Bytes(NonZeroU8, BytesKind),
}

#[derive(Clone, Copy)]
pub enum BytesKind {
    // Uninitialized bytes.
    Uninitialized,
    // Initialized bytes whose bit-valid patterns lie between min and max.
    Initialized {
        min: u128,
        max: u128,
    },
}

impl LayoutAtom {
    /// Consumes bytes of some length `l` and an index `n` less than `l`,
    /// and splits the bytes into a Prod where the first component has 
    /// length equal `n`, and the second component has length `l - n`.
    pub fn split_bytes_at(&self, n: NonZeroU8, endian: Endian) -> Layout {
        use Layout::*;
        use LayoutAtom::*;
        use BytesKind::*;
    
        let (len, kind) =
            if let Bytes(len, kind) = self {
                (*len, *kind)
            } else {
                panic!("Not bytes!")
            };

        assert!(n < len, "index out of bounds");
        
        match (kind, endian) {
            (Uninitialized, _) =>
                Prod(box Atom(Bytes(n, Uninitialized)),
                     box Atom(Bytes((len.get() - n.get()).try_into().unwrap(), Uninitialized))),
            
            (Initialized { min, max }, Endian::Big) => {
                todo!("split the bytes!")
            },

            (Initialized { min, max }, Endian::Little) => {
                let max_l = (1 << (n.get() * 8)) - 1;
                let shift = n.get() * 8;

                if max <= max_l {
                    Prod(
                        box Atom(Bytes(n, Initialized {min, max})),
                        box Atom(Bytes(n, Initialized {min: 0, max: 0})))
                } else if min <= max_l {
                    Sum(
                        box Prod(
                            box Atom(Bytes(n, Initialized {min, max: max_l})),
                            box Atom(Bytes(n, Initialized {min: 0, max: (max - max_l) >> shift}))),
                        box Sum(
                            box Prod(
                                box Atom(Bytes(n, Initialized {min: 0, max: max_l})),
                                box Atom(Bytes(n, Initialized {min: 1, max: (max - max_l) >> shift}))),
                            box Prod(
                                box Atom(Bytes(n, Initialized {min: 0, max: max - ((max >> shift) << shift) })),
                                box Atom(Bytes(n, Initialized {min: 0, max: max >> shift})))))
                } else {
                    let min_r = (min + (1 << shift - 1)) >> shift;
                    Sum(
                        box Prod(
                            box Atom(Bytes(n, Initialized {min: 0, max: max_l})),
                            box Atom(Bytes(n, Initialized {min: min_r, max: (max - max_l) >> shift}))),
                        box Prod(
                            box Atom(Bytes(n, Initialized {min: 0, max: max - ((max >> shift) << shift)})),
                            box Atom(Bytes(n, Initialized {min: min_r, max: max >> shift}))))
                }
            }
        }
    }
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
        (Prod(box Atom(Void), box src_t), dst@Prod(..)) =>
            true,

        // The `Void` layout is *not* transmutable *from* anything.
        (Prod(..), Prod(box Atom(Void), ..)) =>
            false,

        (Prod(box Atom(src_h@Bytes(src_len, ref src_kind)), src_t)
        ,Prod(box Atom(dst_h@Bytes(dst_len, ref dst_kind)), dst_t)) =>
            match src_len.cmp(&dst_len) {
                // If the lengths of the Bytes are equal, their transmutability
                // depends on respective validity.
                Equal => {
                    use BytesKind::*;
                    (match (src_kind, dst_kind) {
                        // Initialized Bytes cannot be constructed
                        // from Uninitialized Bytes
                        (Uninitialized, Initialized{..}) => false,
                        
                        // UninitializedBbytes can be constructed from
                        // either Initialized Bytes or Uninitialized bytes
                        (Uninitialized, Uninitialized) |
                        (Initialized{..}, Uninitialized) => true,

                        // Initialized Bytes are transmutable only into
                        // Initialized Bytes whose validity subsumes src.
                        (Initialized { min: src_min, max: src_max},
                         Initialized { min: dst_min, max: dst_max}) => 
                            src_min >= dst_min && src_max <= dst_max,
                    }) && (transmutable(*src_t, *dst_t, params))
                },
                // If the lengths of the Bytes are inequal, we split the longer
                // Bytes into a layout where the first component is the size of
                // the shorter Bytes.
                // The `src` is smaller:
                Less => {
                    let diff = dst_len.get() - src_len.get();
                    let dst_h = dst_h.split_bytes_at(diff.try_into().unwrap(), params.endian);
                    transmutable(
                        Prod(box Atom(src_h), src_t),
                        Prod(box dst_h, dst_t),
                        params)
                },
                // The `dst` is smaller:
                Greater => {
                    let diff = src_len.get() - dst_len.get();
                    let src_h = src_h.split_bytes_at(diff.try_into().unwrap(), params.endian);
                    transmutable(
                        Prod(box src_h, src_t),
                        Prod(box Atom(dst_h), dst_t),
                        params)
                },
            },

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