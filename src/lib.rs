//! A generic, `no_std`, space-efficient buddy allocator over `Allocatable` values. _This is not a
//! memory allocator_.
//!
//! NOTE: Requires `liballoc`, so stuck on nightly for now.

#![no_std]
#![feature(alloc)]

extern crate alloc;

use alloc::{BTreeSet, Vec};
use core::{cmp, fmt::Debug, ops::{Add, BitAnd, Shl, BitXor}, mem};

/// Types that have an additive identity value.
pub trait Zero {
    /// Return the 0 value.
    fn zero() -> Self;
}

/// Types that have a multiplicative identity value.
pub trait One {
    /// Return the 1 value.
    fn one() -> Self;
}

/// A buddy allocator implementation.
///
/// The allocator allocates values of type `T`, where `T: Allocatable`. For example, `T` could be
/// `usize` or some form of ID number.
#[derive(Debug)]
pub struct BuddyAllocator<T>
where
    T: Zero + One,
    T: Ord,
    T: Copy,
    T: Debug,
    T: Shl<usize, Output = T>,
    T: Add<usize, Output = T>,
    T: BitAnd<usize, Output = T>,
    T: BitXor<Output = T>,
{
    /// The free lists ("bins"). Bin `i` contains allocations of size `1 << i`. The number of bins
    /// determines the maximum allocation size.
    bins: Vec<BTreeSet<T>>,
}

impl<T> BuddyAllocator<T>
where
    T: Zero + One,
    T: Ord,
    T: Copy,
    T: Debug,
    T: Shl<usize, Output = T>,
    T: Add<usize, Output = T>,
    T: BitAnd<usize, Output = T>,
    T: BitXor<Output = T>,
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
    ///
    /// Conceptually this basically the same as `free` but it breaks down irregularly-sized or
    /// irregularly-aligned blocks into aligned, power-of-2-sized blocks.
    pub fn extend(&mut self, start: T, end: T) {
        // This method proceeds in two phases:
        // 1. Decompose the given range into well-formed blocks. A well-formed block is aligned to
        //    its size, and has a size that is a power of two.
        // 2. Add all of the decomposed blocks to the allocator.

        /////////////
        // Phase 1 //
        /////////////

        // The list of well-formed blocks
        let mut blocks = Vec::new();

        // The next value to be handled
        let mut next = start;

        // Keep going until we have handled the whole range
        while next <= end {
            // Find the max order for which the alignment of `next` will suffice. This implies that
            // for all orders `o < order`, the alignment of `next` will suffice for `o`.
            let order = BuddyAllocator::alignment_of(next);

            // Max order: the maximum order that fits between `next` and `end` (inclusive).
            let max_order = self.max_order(next, end);

            // The order of our next block must be...
            let blk_order = [order, max_order, self.bins.len()-1].iter().cloned().min().unwrap();

            // Now we have a well-formed block!
            blocks.push((next, blk_order));

            next = next + (1usize << blk_order);
        }

        panic!("{:?}", blocks);

        /////////////
        // Phase 2 //
        /////////////

        // Go through all of our well-formed blocks and free them
        for (start, order) in blocks.into_iter() {
            self.free(start, 1usize << order);
        }
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
        let buddy = BuddyAllocator::buddy_of(val, order);
        let (val, order) =
            if self.bins[order].remove(&buddy) {
                // should insert the whole block!
                let val = cmp::min(val, buddy);
                (val, order + 1)
            } else {
                (val, order)
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

    /// Helper to get the alignment of the given allocation
    fn alignment_of(val: T) -> usize {
        let mut align = 0; // start with min align
        while align < 8 * mem::size_of::<usize>() {
            // if bit `align+1` of `val` is 0, then is `val` is `align+1`-aligned
            let bit = val & (1usize << align);
            if bit == T::zero() {
                align += 1;
            } else {
                break;
            }
        }
        align
    }

    /// Helper to get the maximum order allocation that will fit between `start` and `end`,
    /// inclusive.
    fn max_order(&self, start: T, end: T) -> usize {
        // Start with the largest order
        let mut order = self.bins.len()-1;

        loop {
            let size = 1usize << order;

            // Round `start` up to the nearest `size`-aligned allocation.
            let round_start = start & (size - 1);

            // Is such a block inside the interval?
            if round_start + size > end {
                // Too big. Shrink size.
                order -= 1;
            } else {
                // It fits!
                break;
            }
        }

        order
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

macro_rules! impl_one_zero {
    ($ty:ident) => {
        impl One for $ty {
            fn one() -> $ty { 1 }
        }

        impl Zero for $ty {
            fn zero() -> $ty { 0 }
        }
    }
}

impl_one_zero!(usize);
impl_one_zero!(isize);

impl_one_zero!(u128);
impl_one_zero!(i128);

impl_one_zero!(u64);
impl_one_zero!(i64);

impl_one_zero!(u32);
impl_one_zero!(i32);

impl_one_zero!(u16);
impl_one_zero!(i16);

impl_one_zero!(u8);
impl_one_zero!(i8);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_simple() {
        let mut a = BuddyAllocator::new(0, 511, 10);

        // check initial state
        assert_eq!(a.bins.len(), 10);
        assert_eq!(a.bins[9].len(), 1);
        panic!("{:#?}", a);
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
