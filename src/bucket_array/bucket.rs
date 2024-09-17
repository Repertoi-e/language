use std::vec::IntoIter;

use bumpalo::Bump;

#[derive(Debug, Clone)]
pub struct Bucket<'bump, T> {
    pub entries: Vec<T, &'bump Bump>,
}

impl<'bump, T> Bucket<'bump, T> {
    pub fn new_in(capacity: usize, bump: &'bump Bump) -> Self {
        Bucket { entries: Vec::<T, &Bump>::with_capacity_in(capacity, bump) }
    }

    pub fn push(&mut self, new_value: T) {
        // Note that this panic should never happen since the entry is only ever
        // accessed by its outer bucket array that checks before pushing.
        if self.entries.len() == self.entries.capacity() {
            panic!("entry is already filled to capacity")
        }
        self.entries.push(new_value);
    }

    pub fn iter(&self) -> core::slice::Iter<T> { self.entries.iter() }
    pub fn iter_mut(&mut self) -> core::slice::IterMut<T> { self.entries.iter_mut() }
}

impl<'bump, T> IntoIterator for Bucket<'bump, T> {
    type Item = T;
    type IntoIter = IntoIter<T, &'bump Bump>;
    fn into_iter(self) -> Self::IntoIter { self.entries.into_iter() }
}

impl<'bump, T> core::ops::Index<usize> for Bucket<'bump, T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output { self.entries.get(index).expect("index out of bounds") }
}

impl<'bump, T> core::ops::IndexMut<usize> for Bucket<'bump, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output { self.entries.get_mut(index).expect("index out of bounds") }
}