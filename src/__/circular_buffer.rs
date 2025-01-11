use bumpalo::Bump;


/// Represents a FIFO `CircularBuffer<T>` data structure.
///
/// This structure is a limited capacity queue, with optional provisions
/// for default values. Under normal circumstances, the `size` of the
/// queue grows until it reaches its `capacity`, at which point any
/// further additions push out its oldest member.
///
/// If default values are specified, then the `size` of the queue
/// is always equal to its `capacity`, with empty slots occupied by the
/// specified default value.
///
/// # Type parameters
/// - `T`: Any type that implements the `Clone` trait.
///
/// # Examples
///
/// ```
/// # use queues::*;
/// # fn main() {
/// let mut cbuf = CircularBuffer::<isize>::new(3);
/// let mut cbuf_def = CircularBuffer::with_default(3, 0isize);
///
/// // Check sizes
/// assert_eq!(cbuf.len(), 0);
/// assert_eq!(cbuf_def.len(), 3);
///
/// // Add elements
/// cbuf.add(6);
/// cbuf_def.add(7);
///
/// // Peek at the next element scheduled for removal
/// assert_eq!(cbuf.peek().unwrap(), 6);
/// assert_eq!(cbuf_def.peek().unwrap(), 0);
/// # }
/// ```
#[derive(Debug)]
pub struct CircularBuffer<'bump, T: Clone> {
    queue: Vec<T, &'bump Bump>,
    capacity: usize,
}

impl<'bump, T: Clone> CircularBuffer<'bump, T> {
    /// Default `CircularBuffer<T>` initializer
    ///
    /// # Returns
    /// A new, empty `CircularBuffer<T>`
    ///
    /// # Examples
    ///
    /// ```
    /// # use queues::*;
    /// let cbuf: CircularBuffer<isize> = CircularBuffer::new(3);
    /// assert_eq!(cbuf.len(), 0);
    /// assert_eq!(cbuf.capacity(), 3);
    /// ```
    pub fn new_in(capacity: usize, bump: &Bump) -> CircularBuffer<T> 
    where 
        T : Default
    {
        CircularBuffer {
            queue: Vec::<T, _>::with_capacity_in(capacity, bump),
            capacity,
        }
    }

    /// Gets the capacity of the `CircularBuffer<T>`
    ///
    /// # Returns
    /// The number of allowed elements in the buffer
    ///
    /// # Examples
    ///
    /// ```
    /// # use queues::CircularBuffer;
    /// let mut cbuf: CircularBuffer<isize> = CircularBuffer::new(3);
    /// assert_eq!(cbuf.capacity(), 3);
    /// ```
    pub fn capacity(&self) -> usize {
        self.capacity
    }
}

impl<'bump, T: Clone> CircularBuffer<'bump, T> {
    /// Adds an element to a circular buffer
    ///
    /// # Parameters
    /// - `val`: Value to add to the buffer
    ///
    /// # Returns
    /// - `Ok(Some(T))`: The oldest value in the buffer, in case the addition causes an overflow.
    /// - `Ok(None)`: Nothing, if the buffer has room for the added element
    ///
    /// # Examples
    ///
    /// ```
    /// # use queues::*;
    /// let mut cbuf: CircularBuffer<isize> = CircularBuffer::new(3);
    /// let mut cbuf_def = CircularBuffer::with_default(3, 5isize);
    /// assert_eq!(cbuf.add(42), Ok(None));
    /// assert_eq!(cbuf_def.add(42), Ok(Some(5)));
    /// ```
    pub fn add(&mut self, val: T) -> &mut T {
        if self.queue.len() < self.capacity {
            self.queue.push(val);
            self.queue.last_mut().unwrap()
        } else {
            let t = self.queue.first_mut().unwrap();
            *t = val;
            t
        }
    }

    /// Removes an element from the circular buffer and returns it.
    ///
    /// For circular buffers with default values, removing an element will add
    /// a new default value into the buffer.
    ///
    /// # Returns
    /// - `Ok(T)`: The oldest element in the buffer
    /// - `Error`
    ///
    /// # Errors
    /// Returns an error if an attempt is made to remove an element from
    /// an empty buffer
    ///
    /// # Examples
    ///
    /// ```
    /// # use queues::*;
    /// let mut cbuf: CircularBuffer<isize> = CircularBuffer::new(3);
    /// cbuf.add(42);
    /// assert_eq!(cbuf.remove(), Ok(42));
    /// assert_eq!(cbuf.len(), 0);
    ///
    /// let mut cbuf_def = CircularBuffer::with_default(3, 4isize);
    /// cbuf_def.add(42);
    /// assert_eq!(cbuf_def.remove(), Ok(4));
    /// ```
    pub fn remove(&mut self) -> Result<T, &str> {
        if !self.queue.is_empty() {
            Ok(self.queue.remove(0usize))
        } else {
            Err("The buffer is empty")
        }
    }

    /// Peek at the head of the circular buffer
    ///
    /// # Returns
    /// - `Ok(T)`: The next element scheduled for removal from the buffer
    /// - `Error`
    ///
    /// # Errors
    /// Returns an error if an attempt is made to peek into an empty buffer
    ///
    /// # Examples
    ///
    /// ```
    /// # use queues::*;
    /// let mut cbuf: CircularBuffer<isize> = CircularBuffer::new(3);
    /// cbuf.add(42);
    /// assert_eq!(cbuf.peek(), Ok(42));
    /// ```
    pub fn peek(&self) -> Result<T, &str> { self.peek_nth(0) }

    /// Peek at the nth element of the circular buffer
    ///
    /// # Returns
    /// - `Ok(T)`: The nth element scheduled for removal from the buffer
    /// - `Error`
    ///
    /// # Errors
    /// Returns an error if an attempt is made to peek into items which don't exist
    ///
    /// # Examples
    ///
    /// ```
    /// # use queues::*;
    /// let mut cbuf: CircularBuffer<isize> = CircularBuffer::new(3);
    /// cbuf.add(42);
    /// assert_eq!(cbuf.peek_nth(0), Ok(42));
    /// ```
    pub fn peek_nth(&self, i: usize) -> Result<T, &str> {
        match self.queue.get(i) {
            Some(val) => Ok(val.clone()),
            None => Err("Index out of bounds"),
        }
    }

    /// Gets the size of the circular buffer
    ///
    /// # Returns
    /// The number of elements in the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use queues::*;
    /// let mut cbuf: CircularBuffer<isize> = CircularBuffer::new(3);
    /// assert_eq!(cbuf.len(), 0);
    /// cbuf.add(42);
    /// assert_eq!(cbuf.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.queue.len()
    }
}
