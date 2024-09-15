use super::{Bucket, BucketArray};

use bumpalo::collections::vec;

#[derive(Debug, Clone)]
pub struct Iter<'bump, T, const C: usize, const G: usize> {
    buckets: core::slice::Iter<'bump, Bucket<'bump, T>>, // Buckets iterator.
    front_iter: Option<core::slice::Iter<'bump, T>>, // Front iterator for `next`.
    back_iter: Option<core::slice::Iter<'bump, T>>, // Back iterator for `next_back`.
    
    // Number of elements that are to be yielded by the iterator.
    len: usize, 
}

impl<'bump, T, const C: usize, const G: usize> Iter<'bump, T, C, G> {
    pub(crate) fn new(arr: &'bump BucketArray<'bump, T, C, G>) -> Self {
        Self {
            buckets: arr.buckets.iter(),
            front_iter: None,
            back_iter: None,
            len: arr.len,
        }
    }
}

impl<'bump, T, const C: usize, const G: usize> Iterator for Iter<'bump, T, C, G> {
    type Item = &'bump T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ref mut front_iter) = self.front_iter {
                if let front @ Some(_) = front_iter.next() {
                    self.len -= 1;
                    return front;
                }
            }
            match self.buckets.next() {
                None => {
                    self.len -= 1;
                    return self.back_iter.as_mut()?.next();
                }
                Some(bucket) => self.front_iter = Some(bucket.iter()),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'bump, T, const C: usize, const G: usize> DoubleEndedIterator for Iter<'bump, T, C, G> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ref mut back_iter) = self.back_iter {
                if let back @ Some(_) = back_iter.next_back() {
                    self.len -= 1;
                    return back;
                }
            }
            match self.buckets.next_back() {
                None => {
                    self.len -= 1;
                    return self.front_iter.as_mut()?.next_back();
                }
                Some(bucket) => self.back_iter = Some(bucket.iter()),
            }
        }
    }
}

#[derive(Debug)]
pub struct IterMut<'bump, T, const C: usize, const G: usize> {
    buckets: core::slice::IterMut<'bump, Bucket<'bump, T>>, // Buckets iterator used by forward iteration.
    front_iter: Option<core::slice::IterMut<'bump, T>>, // Front iterator for `next`.
    back_iter: Option<core::slice::IterMut<'bump, T>>, // Back iterator for `next_back`.

    // Number of elements that are to be yielded by the iterator.
    len: usize,
}

impl<'bump, T, const C: usize, const G: usize> IterMut<'bump, T, C, G> {
    pub(crate) fn new(arr: &'bump mut BucketArray<'bump, T, C, G>) -> Self {
        let len = arr.len;
        Self {
            buckets: arr.buckets.iter_mut(),
            front_iter: None,
            back_iter: None,
            len,
        }
    }
}

impl<'bump, T, const C: usize, const G: usize> Iterator for IterMut<'bump, T, C, G> {
    type Item = &'bump mut T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ref mut front_iter) = self.front_iter {
                if let front @ Some(_) = front_iter.next() {
                    self.len -= 1;
                    return front;
                }
            }
            match self.buckets.next() {
                None => {
                    self.len -= 1;
                    return self.back_iter.as_mut()?.next();
                }
                Some(bucket) => self.front_iter = Some(bucket.iter_mut()),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'bump, T, const C: usize, const G: usize> DoubleEndedIterator for IterMut<'bump, T, C, G> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ref mut back_iter) = self.back_iter {
                if let back @ Some(_) = back_iter.next_back() {
                    self.len -= 1;
                    return back;
                }
            }
            match self.buckets.next_back() {
                None => {
                    self.len -= 1;
                    return self.front_iter.as_mut()?.next_back();
                }
                Some(bucket) => self.back_iter = Some(bucket.iter_mut()),
            }
        }
    }
}

#[derive(Debug)]
pub struct IntoIter<'bump, T, const C: usize, const G: usize> {
    buckets: vec::IntoIter<'bump, Bucket<'bump, T>>, // Buckets iterator used by forward iteration.
    front_iter: Option<vec::IntoIter<'bump, T>>, // Front iterator for `next`.
    back_iter: Option<vec::IntoIter<'bump, T>>, // Back iterator for `next_back`.
    
    // Number of elements that are to be yielded by the iterator.
    len: usize,
}

impl<'bump, T, const C: usize, const G: usize> IntoIter<'bump, T, C, G> {
    pub(crate) fn new(arr: BucketArray<'bump, T, C, G>) -> Self {
        let len = arr.len;
        Self {
            buckets: arr.buckets.into_iter(),
            front_iter: None,
            back_iter: None,
            len,
        }
    }
}

impl<'bump, T, const C: usize, const G: usize> Iterator for IntoIter<'bump, T, C, G> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ref mut front_iter) = self.front_iter {
                if let front @ Some(_) = front_iter.next() {
                    self.len -= 1;
                    return front;
                }
            }
            match self.buckets.next() {
                None => {
                    self.len -= 1;
                    return self.back_iter.as_mut()?.next();
                }
                Some(bucket) => self.front_iter = Some(bucket.into_iter()),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'bump, T, const C: usize, const G: usize> DoubleEndedIterator for IntoIter<'bump, T, C, G> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ref mut back_iter) = self.back_iter {
                if let back @ Some(_) = back_iter.next_back() {
                    self.len -= 1;
                    return back;
                }
            }
            match self.buckets.next_back() {
                None => {
                    self.len -= 1;
                    return self.front_iter.as_mut()?.next_back();
                }
                Some(bucket) => self.back_iter = Some(bucket.into_iter()),
            }
        }
    }
}
