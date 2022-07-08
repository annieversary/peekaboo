//! Peekable iterator that allows to peek the next `N` elements without consuming them.
//!
//! It's `no_std` compatible by default. It also doesn't perform any allocations.
//!
//! # Examples
//!
//! Basic usage:
//!
//! ```
//! use peekaboo::*;
//! let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
//! // create an iterator that allows us to peek at the next 4 element
//! let mut iter = xs.iter().peekable_n::<4>();
//!
//! // peek() lets us see into the future
//! assert_eq!(iter.peek::<1>(), Some(&&1));
//! assert_eq!(iter.peek::<3>(), Some(&&3));
//!
//! // the iterator will not advance until we call `next`
//! assert_eq!(iter.next(), Some(&1));
//! assert_eq!(iter.next(), Some(&2));
//! ```

#![no_std]

use core::iter::FusedIterator;

/// An iterator that allows to peek the next `N` elements without consuming them.
///
/// Note that the underlying iterator is still advanced when [`peek`] or
/// [`peek_mut`] are called for the first time: In order to retrieve the
/// next element, [`next`] is called on the underlying iterator, hence any
/// side effects (i.e. anything other than fetching the next value) of
/// the [`next`] method will occur.
///
/// It is similar to [`core::iter::Peekable`], but it allows to peek further into the iterator.
///
/// `N` has to be greater than 0, but there is no upper bound.
///
/// This `struct` is created by the [`peekable_n`] method on [`IteratorExt`]. See its
/// documentation for more.
///
/// [`peek`]: Peekable::peek
/// [`peek_mut`]: Peekable::peek_mut
/// [`core::iter::Peekable`]: core::iter::Peekable
/// [`peekable_n`]: IteratorExt::peekable_n
/// [`IteratorExt`]: trait.IteratorExt.html
/// [`next`]: Iterator::next
#[derive(Clone, Debug)]
pub struct Peekable<I: Iterator, const N: usize> {
    /// Underlying Iterator
    iter: I,
    /// Remember peeked values, even if they were None.
    peeked: [Option<Option<I::Item>>; N],
}

struct Assert<const L: usize, const R: usize>;
#[allow(dead_code)]
impl<const L: usize, const R: usize> Assert<L, R> {
    pub const GREATER_EQ: usize = L - R;
    pub const LESS_EQ: usize = R - L;
    pub const NOT_EQ: isize = 0 / (R as isize - L as isize);
    pub const EQ: usize = (R - L) + (L - R);
    pub const GREATER: usize = L - R - 1;
    pub const LESS: usize = R - L - 1;
}

impl<I: Iterator, const N: usize> Peekable<I, N> {
    /// Creates an iterator that allows to peek the next `N` elements.
    ///
    /// See the documentation for [`Peekable`] for more information.
    ///
    /// # Fails to compile
    ///
    /// It will fail to compile if `N` is 0.
    ///
    /// ```compile_fail
    /// # use peekaboo::*;
    /// let mut iter = core::iter::empty::<u32>().peekable_n::<0>();
    /// ```
    ///
    /// You will see an error similar to:
    ///
    /// ```text
    /// evaluation of `peekaboo::Assert::<0_usize, 0_usize>::NOT_EQ` failed
    /// attempt to divide `0_isize` by zero
    /// ```
    ///
    /// [`Peekable`]: struct.Peekable.html
    pub fn new(iter: I) -> Self {
        let _ = Assert::<N, 0>::NOT_EQ;

        Self {
            iter,
            peeked: [(); N].map(|_| None),
        }
    }

    /// Returns a reference to the nth next() value without advancing the iterator.
    ///
    /// Like [`next`], if there is a value, it is wrapped in a `Some(T)`.
    /// But if the iteration is over, `None` is returned.
    ///
    /// Note that `peek::<1>()` is equivalent to [`core::iter::Peekable::peek`].
    /// This is to maintain consistency with commonly defined `peek2`, `peek3` methods.
    /// Therefore, `peek::<0>()` is not allowed, and will cause a panic.
    ///
    /// Because `peek()` returns a reference, and many iterators iterate over
    /// references, there can be a possibly confusing situation where the
    /// return value is a double reference.
    ///
    /// # Fails to compile
    ///
    /// It will fail to compile if `IDX` is 0 or if `IDX > N`.
    ///
    /// ```compile_fail
    /// # use peekaboo::*;
    /// let mut iter = core::iter::empty::<u32>().peekable_n::<4>();
    /// let _ = iter.peek::<5>();
    /// ```
    ///
    /// You will see an error similar to:
    ///
    /// ```text
    /// error[E0080]: evaluation of `peekaboo::Assert::<5_usize, 4_usize>::LESS_EQ` failed
    /// attempt to compute `4_usize - 5_usize`, which would overflow
    /// ```
    ///
    /// [`next`]: Iterator::next
    /// [`core::iter::Peekable::peek`]: core::iter::Peekable::peek
    pub fn peek<const IDX: usize>(&mut self) -> Option<&<I as Iterator>::Item> {
        let _ = Assert::<IDX, 0>::NOT_EQ;
        // trying to peek out of bounds. please use Peekable<I, IDX + 1> instead
        let _ = Assert::<IDX, N>::LESS_EQ;

        let idx = IDX - 1;

        let iter = &mut self.iter;
        for i in 0..idx {
            if self.peeked[i].is_none() {
                self.peeked[i] = Some(iter.next());
            }
        }
        self.peeked[idx].get_or_insert_with(|| iter.next()).as_ref()
    }

    /// Returns a mutable reference to the nth next() value without advancing the iterator.
    ///
    /// Like [`next`], if there is a value, it is wrapped in a `Some(T)`.
    /// But if the iteration is over, `None` is returned.
    ///
    /// Note that `peek_mut::<1>()` is equivalent to [`core::iter::Peekable::peek_mut`].
    /// This is to maintain consistency with commonly defined `peek2_mut`, `peek3_mut` methods.
    /// Therefore, `peek::<0>()` is not allowed, and will cause a panic.
    ///
    /// Because `peek_mut()` returns a reference, and many iterators iterate over
    /// references, there can be a possibly confusing situation where the
    /// return value is a double reference.
    ///
    /// # Fails to compile
    ///
    /// It will fail to compile if `IDX` is 0 or if `IDX > N`.
    ///
    /// ```compile_fail
    /// # use peekaboo::*;
    /// let mut iter = core::iter::empty::<u32>().peekable_n::<4>();
    /// let _ = iter.peek_mut::<5>();
    /// ```
    ///
    /// You will see an error similar to:
    ///
    /// ```text
    /// error[E0080]: evaluation of `peekaboo::Assert::<5_usize, 4_usize>::LESS_EQ` failed
    /// attempt to compute `4_usize - 5_usize`, which would overflow
    /// ```
    ///
    /// [`next`]: Iterator::next
    /// [`core::iter::Peekable::peek_mut`]: core::iter::Peekable::peek_mut
    pub fn peek_mut<const IDX: usize>(&mut self) -> Option<&mut <I as Iterator>::Item> {
        let _ = Assert::<IDX, 0>::NOT_EQ;
        // trying to peek out of bounds. please use Peekable<I, IDX + 1> instead
        let _ = Assert::<IDX, N>::LESS_EQ;

        let idx = IDX - 1;

        let iter = &mut self.iter;
        for i in 0..idx {
            if self.peeked[i].is_none() {
                self.peeked[i] = Some(iter.next());
            }
        }
        self.peeked[idx].get_or_insert_with(|| iter.next()).as_mut()
    }

    /// Returns an array with references to the nth next() values without advancing the iterator.
    ///
    /// This method exists because `peek` takes `&mut self`, so the following does not work:
    ///
    /// ```compile_fail
    /// # use peekaboo::*;
    /// let mut iter = core::iter::empty::<u32>().peekable_n::<4>();
    /// let peek1 = iter.peek::<1>();
    /// let peek2 = iter.peek::<2>();
    /// # assert_eq!(peek1, peek2);
    /// ```
    ///
    /// Instead, use:
    ///
    /// ```
    /// # use peekaboo::*;
    /// let mut iter = core::iter::empty::<()>().peekable_n::<4>();
    /// let [peek1, peek2] = iter.peek_multiple::<2>();
    /// # assert_eq!(peek1, peek2);
    /// ```
    ///
    /// # Fails to compile
    ///
    /// It will fail to compile if `IDX` is 0 or if `IDX > N`.
    ///
    /// ```compile_fail
    /// # use peekaboo::*;
    /// let mut iter = core::iter::empty::<u32>().peekable_n::<4>();
    /// let _ = iter.peek_multiple::<5>();
    /// ```
    ///
    /// You will see an error similar to:
    ///
    /// ```text
    /// error[E0080]: evaluation of `peekaboo::Assert::<5_usize, 4_usize>::LESS_EQ` failed
    /// attempt to compute `4_usize - 5_usize`, which would overflow
    /// ```
    pub fn peek_multiple<const IDX: usize>(&mut self) -> [Option<&<I as Iterator>::Item>; IDX] {
        let _ = Assert::<IDX, 0>::NOT_EQ;
        // trying to peek out of bounds. please use Peekable<I, IDX + 1> instead
        let _ = Assert::<IDX, N>::LESS_EQ;

        let mut res = [(); IDX].map(|_| None);
        // fill peeked with the values
        let _ = self.peek::<IDX>();

        for i in 0..IDX {
            res[i] = self.peeked[i]
                .as_ref()
                .expect("peeked to be filled with Some up to IDX")
                .as_ref();
        }

        res
    }

    /// Consume and return the next value of this iterator if a condition is true.
    ///
    /// If `func` returns `true` for the next value of this iterator, consume and return it.
    /// Otherwise, return `None`.
    pub fn next_if(&mut self, func: impl FnOnce(&I::Item) -> bool) -> Option<I::Item> {
        match self.next() {
            Some(matched) if func(&matched) => Some(matched),
            other => {
                self.peeked[..].rotate_right(1);
                self.peeked[0] = Some(other);
                None
            }
        }
    }

    /// Consume and return the next item if it is equal to `expected`.
    pub fn next_if_eq<T>(&mut self, expected: &T) -> Option<I::Item>
    where
        T: ?Sized,
        I::Item: PartialEq<T>,
    {
        self.next_if(|next| next == expected)
    }

    fn shift(&mut self) {
        self.peeked[..].rotate_left(1);
        self.peeked[N - 1] = None;
    }
}

impl<I: Iterator, const N: usize> Iterator for Peekable<I, N> {
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<I::Item> {
        let v = self.peeked[0].take();
        self.shift();
        match v {
            Some(v) => v,
            None => self.iter.next(),
        }
    }

    #[inline]
    fn count(self) -> usize {
        let mut count = 0;
        for i in 0..N {
            match self.peeked[i] {
                Some(None) => {}
                Some(Some(_)) => count += 1,
                None => return count + self.iter.count(),
            }
        }

        count + self.iter.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<I::Item> {
        for i in 0..N {
            let c = self.peeked[0].take();
            self.shift();
            match c {
                Some(v @ Some(_)) if n == i => return v,
                Some(Some(_)) => {}
                Some(None) => return None,
                None => return self.iter.nth(n - i),
            }
        }

        self.iter.nth(n - N)
    }

    #[inline]
    fn last(mut self) -> Option<I::Item> {
        let mut last = None;
        for _ in 0..N {
            let c = self.peeked[0].take();
            self.shift();
            match c {
                Some(None) => return None,
                Some(v) => last = v.or(last),
                None => {}
            };
        }

        self.iter.last().or(last)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut count = 0;

        for i in 0..N {
            match self.peeked[i] {
                Some(None) => return (count, Some(count)),
                Some(Some(_)) => count += 1,
                None => {}
            }
        }

        let (lo, hi) = self.iter.size_hint();
        let lo = lo.saturating_add(count);
        let hi = match hi {
            Some(x) => x.checked_add(count),
            None => None,
        };
        (lo, hi)
    }

    // try is still unstable
    // #[inline]
    // fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
    // where
    //     Self: Sized,
    //     F: FnMut(B, Self::Item) -> R,
    //     R: std::ops::Try<Output = B>,
    // {
    //     let acc = match self.peeked.take() {
    //         Some(None) => return try { init },
    //         Some(Some(v)) => f(init, v)?,
    //         None => init,
    //     };
    //     self.iter.try_fold(acc, f)
    // }

    #[inline]
    fn fold<Acc, Fold>(mut self, init: Acc, mut fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let mut acc = init;
        for i in 0..N {
            match self.peeked[i].take() {
                Some(None) => return acc,
                Some(Some(v)) => acc = fold(acc, v),
                None => {}
            }
        }
        self.iter.fold(acc, fold)
    }
}

impl<I, const N: usize> DoubleEndedIterator for Peekable<I, N>
where
    I: DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // match self.peeked.as_mut() {
        //     Some(v @ Some(_)) => self.iter.next_back().or_else(|| v.take()),
        //     Some(None) => None,
        //     None => self.iter.next_back(),
        // }

        for i in (0..N).rev() {
            if let Some(v) = self.peeked[i].as_mut() {
                if v.is_none() {
                    return None;
                }
                return self.iter.next_back().or_else(|| v.take());
            }
        }

        self.iter.next_back()
    }

    // #[inline]
    // fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
    // where
    //     Self: Sized,
    //     F: FnMut(B, Self::Item) -> R,
    //     R: Try<Output = B>,
    // {
    //     match self.peeked.take() {
    //         Some(None) => try { init },
    //         Some(Some(v)) => match self.iter.try_rfold(init, &mut f).branch() {
    //             ControlFlow::Continue(acc) => f(acc, v),
    //             ControlFlow::Break(r) => {
    //                 self.peeked = Some(Some(v));
    //                 R::from_residual(r)
    //             }
    //         },
    //         None => self.iter.try_rfold(init, f),
    //     }
    // }

    #[inline]
    fn rfold<Acc, Fold>(mut self, init: Acc, mut fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let mut acc = self.iter.rfold(init, &mut fold);
        for i in 0..N {
            match self.peeked[i].take() {
                Some(None) => return acc,
                Some(Some(v)) => {
                    acc = fold(acc, v);
                }
                None => {}
            }
        }
        acc
    }
}

impl<I: ExactSizeIterator, const N: usize> ExactSizeIterator for Peekable<I, N> {}
impl<I: FusedIterator, const N: usize> FusedIterator for Peekable<I, N> {}

/// Trait extension that provides [`peekable_n`] for [`Iterator`]s
///
/// [`peekable_n`]: IteratorExt::peekable_n
/// [`Iterator`]: core::iter::Iterator
pub trait IteratorExt {
    /// Creates an iterator that allows to peek the next `N` elements.
    ///
    /// See the documentation for [`Peekable`] for more information.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0.
    ///
    /// [`Peekable`]: struct.Peekable.html
    fn peekable_n<const N: usize>(self) -> Peekable<Self, N>
    where
        Self: Sized + Iterator;
}
impl<I: Iterator> IteratorExt for I {
    fn peekable_n<const N: usize>(self) -> Peekable<Self, N> {
        Peekable::new(self)
    }
}
