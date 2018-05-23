//! A generic, `no_std`, space-efficient buddy allocator over `Allocatable` values. _This is not a
//! memory allocator_.
//!
//! NOTE: Requires `liballoc`, so stuck on nightly for now.

#![no_std]
#![feature(alloc)]

extern crate alloc;

use alloc::{BTreeSet, Vec};
use core::ops::{Shl, BitXor};

/// Types that have a multiplicative identity value.
pub trait One {
    /// Return the 1 value.
    fn one() -> Self;
}

/// A buddy allocator implementation.
///
/// The allocator allocates values of type `T`, where `T: Allocatable`. For example, `T` could be
/// `usize` or some form of ID number.
pub struct BuddyAllocator<T>
where
    T: One,
    T: Ord,
    T: Copy,
    T: Shl<usize, Output=T> + BitXor<Output = T>,
{
    /// The free lists ("bins"). Bin `i` contains allocations of size `1 << i`. The number of bins
    /// determines the maximum allocation size.
    bins: Vec<BTreeSet<T>>,
}

impl<T> BuddyAllocator<T>
where
    T: One,
    T: Ord,
    T: Copy,
    T: Shl<usize, Output=T> + BitXor<Output = T>,
{
    /// Create a new buddy allocator over the given range of values. `start` _and_ `end` are
    /// inclusive.
    pub fn new(start: T, end: T, nbins: u8) -> Self {
        let mut bins = Vec::with_capacity(nbins as usize);
        for _ in 0..nbins {
            bins.push(BTreeSet::new());
        }

        let mut new = BuddyAllocator { bins };

        new.extend(start, end);

        new
    }

    /// Add the given range to the buddy allocator. `start` _and_ `end` are inclusive.
    /// TODO: maybe this has to be contiguous? Otherwise, how do we tell if there is a whole? Maybe
    /// by size of allocations?
    pub fn extend(&mut self, start: T, end: T) {
        //TODO: recursively decompose into powers of two.
        //TODO: split large block sizes into size of last bin.
    }

    /// Allocate at least `n` values from the allocator.
    ///
    /// Returns `None` if there is not enough memory to satisfy the request.
    pub fn alloc(&mut self, n: usize) -> Option<T> {
        // Find the bin we need
        let order = Self::order_of(n);

        // Get a value from the given bin.
        self.get_from_bin(order)
    }

    /// Free the given element(s) to the allocator.
    pub fn free(&mut self, val: T, n: usize) {
        // Find the bin we need
        let order = Self::order_of(n);

        // Sanity check
        assert!(order < self.bins.len());

        // Check if the buddy is free. If so, remove it and increase the order of `val`
        let order =
            if self.bins[order].remove(&BuddyAllocator::buddy_of(val, order)) {
                order + 1
            } else {
                order
            };

        // Insert into the proper tier
        self.bins[order].insert(val);
    }

    /// Helper to get the buddy value of the given value
    fn buddy_of(val: T, order: usize) -> T {
        val ^ (T::one() << order)
    }

    /// Helper to get the order for a given allocation size.
    fn order_of(n: usize) -> usize {
        // Defend against overflow
        assert!(n.leading_zeros() > 0);

        // Round `n` up to the next power of two.
        let n = if n.is_power_of_two() {
            n
        } else {
            n.next_power_of_two()
        };

        // Log_2(n) = # of trailing zeros b/c n is a power of 2
        n.trailing_zeros() as usize
    }

    /// Helper to recursively try to allocate a block of values of the given size.
    ///
    /// Returns `None` if no such block exists.
    fn get_from_bin(&mut self, order: usize) -> Option<T> {
        // If the order is too large, we are out of luck.
        if order >= self.bins.len() {
            return None;
        }

        // If bin `order` has elements, take the first one and return it.
        if let Some(&val) = { self.bins[order].iter().next() } {
            return self.bins[order].take(&val);
        }

        // Otherwise, split a larger block
        if let Some(val) = self.get_from_bin(order + 1) {
            // We got a block, and it is twice as large as what we need.
            let second_half = BuddyAllocator::buddy_of(val, order);

            // Free the second half
            self.free(second_half, 1 << order);

            // Return the first half
            Some(val)
        } else {
            // No allocation was big enough. OOM!
            None
        }
    }
}

macro_rules! impl_one {
    ($ty:ident) => {
        impl One for $ty {
            fn one() -> $ty { 1 }
        }
    }
}

impl_one!(usize);
impl_one!(isize);

impl_one!(u128);
impl_one!(i128);

impl_one!(u64);
impl_one!(i64);

impl_one!(u32);
impl_one!(i32);

impl_one!(u16);
impl_one!(i16);

impl_one!(u8);
impl_one!(i8);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_simple() {
        let mut a = BuddyAllocator::new(0, 511, 10);

        // check initial state
        assert_eq!(a.bins.len(), 10);
        assert_eq!(a.bins[9].len(), 1);
        assert!(a.bins[9].contains(&0));
        for i in 0..9 {
            assert_eq!(a.bins[i].len(), 0);
        }

        // allocate 1
        let alloced = a.alloc(1);
        assert_eq!(alloced, Some(0));

        // check state after alloc
        assert_eq!(a.bins[9].len(), 0);

        assert_eq!(a.bins[8].len(), 1);
        assert!(a.bins[8].contains(&256));

        assert_eq!(a.bins[7].len(), 1);
        assert!(a.bins[7].contains(&128));

        assert_eq!(a.bins[6].len(), 1);
        assert!(a.bins[6].contains(&64));

        assert_eq!(a.bins[5].len(), 1);
        assert!(a.bins[5].contains(&32));

        assert_eq!(a.bins[4].len(), 1);
        assert!(a.bins[4].contains(&16));

        assert_eq!(a.bins[3].len(), 1);
        assert!(a.bins[3].contains(&8));

        assert_eq!(a.bins[2].len(), 1);
        assert!(a.bins[2].contains(&4));

        assert_eq!(a.bins[1].len(), 1);
        assert!(a.bins[1].contains(&2));

        assert_eq!(a.bins[0].len(), 1);
        assert!(a.bins[0].contains(&1));

        // free allocation
        a.free(0, 1);

        // check final state
        assert_eq!(a.bins.len(), 10);
        assert_eq!(a.bins[9].len(), 1);
        assert!(a.bins[9].contains(&0));
        for i in 0..9 {
            assert_eq!(a.bins[i].len(), 0);
        }
    }

    // TODO: test with small number of bins

    // TODO: test extend
}
