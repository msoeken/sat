use std::{
    iter::repeat,
    ops::{Index, IndexMut},
};

#[derive(Default)]
struct Block<T: Default> {
    tag: bool,
    linkf: usize,
    linkb: usize,
    kval: usize,
    data: T,
}

pub struct AllocatedBlock<'a, T: Default> {
    memory: &'a mut BuddyMemory<T>,
    address: usize,
}

impl<T: Default> AllocatedBlock<'_, T> {
    pub fn iter(&self) -> AllocatedBlockIter<'_, T> {
        AllocatedBlockIter {
            block: self,
            current: 0,
        }
    }
}

impl<T: Default> Index<usize> for AllocatedBlock<'_, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.memory.memory[self.address + index].data
    }
}

impl<T: Default> IndexMut<usize> for AllocatedBlock<'_, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.memory.memory[self.address + index].data
    }
}

pub struct AllocatedBlockIter<'a, T: Default> {
    block: &'a AllocatedBlock<'a, T>,
    current: usize,
}

impl<'a, T: Default> Iterator for AllocatedBlockIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < (1 << self.block.memory.memory[self.block.address].kval) {
            self.current += 1;
            Some(&self.block[self.current - 1])
        } else {
            None
        }
    }
}

pub struct BuddyMemory<T: Default> {
    m: usize,
    memory: Vec<Block<T>>,
}

impl<T: Default> BuddyMemory<T> {
    pub fn new(m: usize) -> Self {
        // The first 2ᵐ elements are for data blocks; the last m + 1 elements
        // are list heads for AVAIL
        let mut memory: Vec<_> = repeat(())
            .map(|_| Block::default())
            .take((1 << m) + m + 1)
            .collect();

        // fill meta-information into first and only available block
        memory[0].linkf = (1 << m) + m;
        memory[0].linkb = (1 << m) + m;
        memory[0].tag = true;
        memory[0].kval = m;

        // setup list heads
        memory[(1 << m) + m].linkf = 0;
        memory[(1 << m) + m].linkb = 0;
        for k in 0..m {
            memory[(1 << m) + k].linkf = (1 << m) + k;
            memory[(1 << m) + k].linkb = (1 << m) + k;
        }

        Self { m, memory }
    }

    fn loc_avail(&self, k: usize) -> usize {
        assert!(k <= self.m);

        (1 << self.m) + k
    }

    pub fn reserve(&mut self, k: usize) -> AllocatedBlock<T> {
        // R1. [Find block.]
        let mut j = (k..=self.m)
            .find(|&j| self.memory[(1 << self.m) + j].linkf != (1 << self.m) + j)
            .expect("no more available blocks of sufficient size");

        // R2. [Remove from list.]
        let loc_j = self.loc_avail(j);
        let location = self.memory[loc_j].linkf;
        let block = self.memory[location].linkf;
        self.memory[loc_j].linkf = block;
        self.memory[block].linkb = self.loc_avail(j);
        self.memory[location].tag = false;
        self.memory[location].kval = k;

        // R3. [Split required?]
        while j != k {
            // R4. [Split.]
            j -= 1;
            let loc_j = self.loc_avail(j);

            // get buddy
            let block = location + (1 << j);
            self.memory[block].tag = true;
            self.memory[block].kval = j;
            self.memory[block].linkf = loc_j;
            self.memory[block].linkb = loc_j;
            self.memory[loc_j].linkf = block;
            self.memory[loc_j].linkb = block;
        }

        AllocatedBlock {
            memory: self,
            address: location,
        }
    }

    pub fn free(&mut self, location: usize) {
        let mut k = self.memory[location].kval;
        let mut location = location;

        loop {
            let buddy = location ^ (1 << k);

            if (k == self.m) || !self.memory[buddy].tag || self.memory[buddy].kval != k {
                break;
            }

            // S2. [Combine with buddy.]
            let linkb = self.memory[buddy].linkb;
            self.memory[linkb].linkf = self.memory[buddy].linkf;

            let linkf = self.memory[buddy].linkf;
            self.memory[linkf].linkb = self.memory[buddy].linkb;

            k += 1;
            if buddy < location {
                location = buddy;
            }
        }

        // S3. [Put on list.]
        self.memory[location].tag = true;
        let loc_k = self.loc_avail(k);
        // get first block in AVAIL[k]; insert block before
        let first = self.memory[loc_k].linkf;
        self.memory[location].linkf = first;
        self.memory[first].linkb = location;
        self.memory[location].kval = k;
        self.memory[location].linkb = loc_k;
        self.memory[loc_k].linkf = location;
    }
}

#[cfg(test)]
mod tests {
    use super::BuddyMemory;

    #[test]
    fn test_buddy_memory() {
        let mut mem = BuddyMemory::<u32>::new(3);

        let mut block = mem.reserve(2);
        assert_eq!(block[0], 0);
        block[0] = 42;
        block[1] = 21;
        block[2] = 17;
        block[3] = 12;
        assert_eq!(block[0], 42);

        for (idx, &val) in block.iter().enumerate() {
            match idx {
                0 => assert_eq!(val, 42),
                1 => assert_eq!(val, 21),
                2 => assert_eq!(val, 17),
                3 => assert_eq!(val, 12),
                _ => unreachable!(),
            }
        }

        assert_eq!(block.address, 0);
        assert_eq!(mem.reserve(1).address, 4);
        assert_eq!(mem.reserve(0).address, 6);
        assert_eq!(mem.reserve(0).address, 7);

        mem.free(0);

        assert_eq!(mem.reserve(1).address, 0);
        assert_eq!(mem.reserve(1).address, 2);
    }
}
