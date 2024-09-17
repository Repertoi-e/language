//! # Bucket Vector
//!
//! 100% `unsafe` Rust free!
//!
//! ## Description
//!
//! An array data structure that organizes its elements into a set of buckets
//! of fixed-capacity in order to guarantee that mutations to the bucket vector
//! never moves elements.
//!
//! This is comparable to a `Vec<Box<T>>` but a lot more efficient.
//!
//! ## Under the Hood
//!
//! The `BucketArray` is really just a vector of `Bucket` instances.
//! Whenever an element is pushed to the `BucketArray` the element is pushed onto
//! the last `Bucket` if it isn't filled, yet.
//! If the last `Bucket` is filled a new `Bucket` is pushed onto the `BucketArray`
//! with a new capacity determined by the used bucket vector configuration.
//!
//! This way the `BucketArray` never moves elements around upon inserting new elements
//! in order to preserve references. When a normal `Vec` is modified it can potentially
//! invalidate references because of reallocation of the internal buffer which
//! might cause severe bugs if references to the internal elements are stored
//! outside the `Vec`. Note that normally Rust prevents such situations so the
//! `BucketArray` is mainly used in the area of `unsafe` Rust where a developer
//! actively decides that they want or need pinned references into another data
//! structure.
//!
//! For the same reasons as stated above the `BucketArray` does not allow to remove
//! or swap elements.
//!
//! ## Example
//!
//! Looking at an example `BucketArray<i32>` with the following configuration:
//!
//! - `start_capacity := 1`
//! - `growth_rate := 2`
//!
//! We have already pushed the elements `A`,.., `K` onto it.
//!
//! ```no_compile
//! [ [A], [B, C], [D, E, F, G], [H, I, J, K, _, _, _, _] ]
//! ```
//!
//! Where `_` refers to a vacant bucket entry.
//!
//! Pushing another `L`,.., `O` onto the same `BucketArray` results in:
//!
//! ```no_compile
//! [ [A], [B, C], [D, E, F, G], [H, I, J, K, L, M, N, O] ]
//! ```
//!
//! So we are full on capacity for all buckets.
//! The next time we push another element onto the `BucketArray` it will create a new `Bucket` with a capacity of `16` since `growth_rate == 2` and our current latest bucket already has a capacity of `8`.
//!
//! ```no_compile
//! [ [A], [B, C], [D, E, F, G], [H, I, J, K, L, M, N, O], [P, 15 x _] ]
//! ```
//!
//! Where `15 x _` denotes 15 consecutive vacant entries.

mod bucket;
mod iter;

use bumpalo::Bump;

use self::bucket::Bucket;
pub use self::iter::{IntoIter, Iter, IterMut};

/// # Formulas
///
/// ## Definitions
///
/// In the following we define
///
/// - `N := START_CAPACITY` and
/// - `a := GROWTH_RATE`
///
/// ## Bucket Capacity
///
/// ### For `a != 1`:
///
/// The total capacity of all buckets until bucket `i` (not including `i`)
/// is expressed as:
///
/// ```no_compile
/// capacity_until(i) := N * (a^i - 1) / (a-1)
/// ```
///
/// The capacity of the `i`th bucket is then calculated by:
///
/// ```no_compile
/// capacity(i) := floor(capacity_until(i+1)) - floor(capacity_until(i))
/// ```
///
/// Where `floor: f64 -> f64` rounds the `f64` down to the next even `f64`
/// for positive `f64`.
///
/// Note that `capacity(i)` is approximately `capacity(i)' := N * a^i`.
///
/// ### For `a == 1`:
///
/// This case is trivial and all buckets are equally sized to have a
/// capacity of `N`.
///
/// ## Accessing Elements by Index
///
/// Accessing the `i`th element of a `BucketArray` can be expressed by the
/// following formulas:
///
/// ### For `a != 1`:
///
/// First we define the inverted capacity function for which
/// `1 == capacity(i) * inv_capacity(i)` forall `i`.
/// ```no_compile
/// inv_capacity(i) = ceil(log(1 + (i + 1) * (a - 1) / N, a)) - 1
/// ```
/// Where `ceil: f64 -> f64` rounds the `f64` up to the next even `f64`
/// for positive `f64`.
///
/// Having this the `bucket_index` and the `entry_index` inside the bucket
/// indexed by `bucket_index` is expressed as:
/// ```no_compile
/// bucket_index(i) = inv_capacity(i)
/// entry_index(i) = i - floor(capacity_until(bucket_index(i)))
/// ```
///
/// ### For `a == 1`:
///
/// This case is very easy and we can simply calculate the `bucket_index` and
/// `entry_index` by:
///
/// ```no_compile
/// bucket_index(i) = i / N
/// entry_index(i) = i % N
/// ```

const STARTING_CAPACITY: usize = 8000;
const GROWTH_RATE: usize = 1;

#[derive(Debug)]
pub struct BucketArray<'bump, T> {
    len: usize,
    buckets: Vec<Bucket<'bump, T>, &'bump Bump>,
    bump: &'bump Bump // The bump arena memory is allocated to 
}

impl<'bump, T> IntoIterator for BucketArray<'bump, T> {
    type Item = T;
    type IntoIter = IntoIter<'bump, T>;

    fn into_iter(self) -> Self::IntoIter { IntoIter::new(self) }
}

impl<'bump, T> IntoIterator for &'bump BucketArray<'bump, T> {
    type Item = &'bump T;
    type IntoIter = Iter<'bump, T>;

    fn into_iter(self) -> Self::IntoIter { Iter::new(self)}
}

impl<'bump, T> IntoIterator for &'bump mut BucketArray<'bump, T> {
    type Item = &'bump mut T;
    type IntoIter = IterMut<'bump, T>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut::new(self)
    }
}

impl<'bump, T> Clone for BucketArray<'bump, T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            len: self.len,
            buckets: self.buckets.clone(),
            bump: self.bump
        }
    }
}

impl<'bump, T> PartialEq for BucketArray<'bump, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool { self.iter().zip(other.iter()).all(|(lhs, rhs)| lhs == rhs) }
}

impl<'bump, T> Eq for BucketArray<'bump, T> where T: Eq {}

impl<'bump, T> core::cmp::PartialOrd for BucketArray<'bump, T>
where
    T: core::cmp::PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        for (lhs, rhs) in self.iter().zip(other.iter()) {
            match lhs.partial_cmp(rhs) {
                Some(core::cmp::Ordering::Equal) => (),
                non_eq => return non_eq,
            }
        }
        self.len.partial_cmp(&other.len)
    }
}

impl<'bump, T> core::cmp::Ord for BucketArray<'bump, T>
where
    T: core::cmp::Ord,
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        for (lhs, rhs) in self.iter().zip(other.iter()) {
            match lhs.cmp(rhs) {
                core::cmp::Ordering::Equal => (),
                non_eq => return non_eq,
            }
        }
        self.len.cmp(&other.len)
    }
}

impl<'bump, T> core::hash::Hash for BucketArray<'bump, T>
where
    T: core::hash::Hash,
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        for elem in self.iter() {
            elem.hash(state);
        }
    }
}

impl<'bump, T> BucketArray<'bump, T> {
    pub fn new_in(bump: &'bump Bump) -> Self {
        Self {
            len: 0,
            buckets: Vec::<_, &'bump Bump>::new_in(&bump),
            bump: bump,
        }
    }

    pub fn iter(&self) -> Iter<T> { Iter::new(self) }
    pub fn iter_mut(&'bump mut self) -> IterMut<T> { IterMut::new(self) }

    pub fn first(&self) -> Option<&T> {
        if self.buckets.is_empty() { return None }
        Some(&self.buckets[0][0])
    }

    pub fn first_mut(&mut self) -> Option<&mut T> {
        if self.buckets.is_empty() { return None }
        Some(&mut self.buckets[0][0])
    }

    pub fn last(&self) -> Option<&T> {
        if self.buckets.is_empty() { return None }
        let len_buckets = self.buckets.len();
        let len_entries = self.buckets[len_buckets - 1].entries.len();
        Some(&self.buckets[len_buckets - 1][len_entries - 1])
    }

    pub fn last_mut(&mut self) -> Option<&mut T> {
        if self.buckets.is_empty() { return None }
        let len_buckets = self.buckets.len();
        let len_entries = self.buckets[len_buckets - 1].entries.len();
        Some(&mut self.buckets[len_buckets - 1][len_entries - 1])
    }
}

impl<'bump, T> BucketArray<'bump, T>
{
    // Returns the total capacity of all buckets up to (and including) the bucket indexed by `index`.
    pub fn total_capacity(index: usize) -> usize
    {
        if GROWTH_RATE == 1 {
            (index / STARTING_CAPACITY + 1) * STARTING_CAPACITY
        } else {
            STARTING_CAPACITY * (GROWTH_RATE.pow(index as u32) - 1) / (GROWTH_RATE - 1)
        }
    }

    /// Returns the capacity of the indexed bucket.
    pub fn bucket_capacity(index: usize) -> usize
    {
        if GROWTH_RATE == 1 {
            STARTING_CAPACITY
        } else {
            let next_total_capacity = Self::total_capacity(index + 1);
            let total_capacity = Self::total_capacity(index);
            next_total_capacity - total_capacity
        }
    }

    // Returns the bucket index and its internal entry index for the given bucket vector index into an element.
    pub fn bucket_entry_indices(&self, index: usize) -> Option<(usize, usize)> {
        if index >= self.len {
            return None;
        }
        if GROWTH_RATE == 1{
            let x = index / STARTING_CAPACITY;
            let y = index % STARTING_CAPACITY;
            Some((x, y))
        } else {
            // Non-trivial case: Buckets are unequally sized.
            let f_inv = 1.0 + (index + 1) as f64 * (GROWTH_RATE as f64 - 1.0) / STARTING_CAPACITY as f64;
            let off_x = if GROWTH_RATE == 2 {
                f64::log2(f_inv)
            } else {
                f64::log(f_inv, GROWTH_RATE as f64)
            };
            let x = f64::ceil(off_x) as usize - 1;
            let y = index - Self::total_capacity(x);
            Some((x, y))
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.bucket_entry_indices(index)
            .and_then(|(x, y)| self.buckets[x].entries.get(y))
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.bucket_entry_indices(index)
            .and_then(move |(x, y)| self.buckets[x].entries.get_mut(y))
    }
}

impl<'bump, T> BucketArray<'bump, T> {
    fn push_bucket(&mut self, new_value: T) {
        let len_buckets = self.buckets.len();
        let new_capacity = Self::bucket_capacity(len_buckets);
        let mut new_bucket = Bucket::new_in(new_capacity, self.bump);
        new_bucket.push(new_value);
        self.buckets.push(new_bucket);
        self.len += 1;
    }

    pub fn push(&mut self, new_value: T) {
        if let Some(bucket) = self.buckets.last_mut() {
            if bucket.entries.len() < bucket.entries.capacity() {
                bucket.push(new_value);
                self.len += 1;
                return;
            }
        }
        self.push_bucket(new_value);
    }

    pub fn push_get(&mut self, new_value: T) -> (usize, &mut T) {
        let index = self.len;
        self.push(new_value);
        
        let len_buckets = self.buckets.len();
        let len_entries = self.buckets[len_buckets - 1].entries.len();

        (index, &mut self.buckets[len_buckets - 1][len_entries - 1])
    }
}

impl<'bump, T> core::iter::Extend<T> for BucketArray<'bump, T>
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push(item)
        }
    }
}