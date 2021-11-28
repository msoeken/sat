use std::{
    iter::repeat,
    ops::{Index, IndexMut},
};

#[derive(Default)]
pub struct Block<T: Default> {
    linkf: u32,
    linkb: u32,
    _kval: u32,
    data: T,
}

impl<T: Default> Block<T> {
    pub fn kval(&self) -> u32 {
        self._kval >> 1
    }

    pub fn set_kval(&mut self, k: u32) {
        self._kval = (self._kval & 1) + (k << 1);
    }

    pub fn tag(&self) -> bool {
        (self._kval & 1) == 1
    }

    pub fn set_tag(&mut self, tag: bool) {
        self._kval = (self._kval & !1) + if tag { 1 } else { 0 };
    }
}

pub struct AllocatedBlock<'a, T: Default> {
    memory: &'a mut BuddyMemory<T>,
    address: u32,
}

impl<'a, T: Default> AllocatedBlock<'a, T> {
    pub fn new(memory: &'a mut BuddyMemory<T>, address: u32) -> Self {
        Self { memory, address }
    }

    pub fn address(&self) -> u32 {
        self.address
    }

    pub fn iter(&self) -> AllocatedBlockIter<'_, T> {
        AllocatedBlockIter {
            block: self,
            current: 0,
        }
    }
}

impl<'a, T: Default> Index<u32> for AllocatedBlock<'a, T> {
    type Output = T;

    fn index(&self, index: u32) -> &Self::Output {
        &self.memory[self.address + index].data
    }
}

impl<T: Default> IndexMut<u32> for AllocatedBlock<'_, T> {
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        &mut self.memory[self.address + index].data
    }
}

pub struct AllocatedBlockIter<'a, T: Default> {
    block: &'a AllocatedBlock<'a, T>,
    current: u32,
}

impl<'a, T: Default> Iterator for AllocatedBlockIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < (1 << self.block.memory[self.block.address].kval()) {
            self.current += 1;
            Some(&self.block[self.current - 1])
        } else {
            None
        }
    }
}

pub struct BuddyMemory<T: Default> {
    m: u32,
    memory: Vec<Block<T>>,
}

impl<T: Default> BuddyMemory<T> {
    pub fn new(m: u32) -> Self {
        // The first 2ᵐ elements are for data blocks; the last m + 1 elements
        // are list heads for AVAIL
        let mut memory: Vec<_> = repeat(())
            .map(|_| Block::default())
            .take(((1 << m) + m + 1) as usize)
            .collect();

        // fill meta-information into first and only available block
        memory[0].linkf = (1 << m) + m;
        memory[0].linkb = (1 << m) + m;
        memory[0].set_tag(true);
        memory[0].set_kval(m);

        // setup list heads
        memory[((1 << m) + m) as usize].linkf = 0;
        memory[((1 << m) + m) as usize].linkb = 0;
        for k in 0..m {
            memory[((1 << m) + k) as usize].linkf = (1 << m) + k;
            memory[((1 << m) + k) as usize].linkb = (1 << m) + k;
        }

        Self { m, memory }
    }

    fn loc_avail(&self, k: u32) -> u32 {
        assert!(k <= self.m);

        (1 << self.m) + k
    }

    pub fn reserve<'a>(&'a mut self, k: u32) -> AllocatedBlock<'a, T> {
        // R1. [Find block.]
        let mut j = (k..=self.m)
            .find(|&j| self[(1 << self.m) + j].linkf != (1 << self.m) + j)
            .expect("no more available blocks of sufficient size");

        // R2. [Remove from list.]
        let loc_j = self.loc_avail(j);
        let location = self[loc_j].linkf;
        let block = self[location].linkf;
        self[loc_j].linkf = block;
        self[block].linkb = self.loc_avail(j);
        self[location].set_tag(false);
        self[location].set_kval(k);

        // R3. [Split required?]
        while j != k {
            // R4. [Split.]
            j -= 1;
            let loc_j = self.loc_avail(j);

            // get buddy
            let block = location + (1 << j);
            self[block].set_tag(true);
            self[block].set_kval(j);
            self[block].linkf = loc_j;
            self[block].linkb = loc_j;
            self[loc_j].linkf = block;
            self[loc_j].linkb = block;
        }

        AllocatedBlock::new(self, location)
    }

    pub fn free(&mut self, location: u32) {
        let mut k = self[location].kval();
        let mut location = location;

        loop {
            let buddy = location ^ (1 << k);

            if (k == self.m) || !self[buddy].tag() || self[buddy].kval() != k {
                break;
            }

            // S2. [Combine with buddy.]
            let linkb = self[buddy].linkb;
            self[linkb].linkf = self[buddy].linkf;

            let linkf = self[buddy].linkf;
            self[linkf].linkb = self[buddy].linkb;

            k += 1;
            if buddy < location {
                location = buddy;
            }
        }

        // S3. [Put on list.]
        self[location].set_tag(true);
        let loc_k = self.loc_avail(k);
        // get first block in AVAIL[k]; insert block before
        let first = self[loc_k].linkf;
        self[location].linkf = first;
        self[first].linkb = location;
        self[location].set_kval(k);
        self[location].linkb = loc_k;
        self[loc_k].linkf = location;
    }
}

impl<T: Default> Index<u32> for BuddyMemory<T> {
    type Output = Block<T>;

    fn index(&self, index: u32) -> &Self::Output {
        &self.memory[index as usize]
    }
}

impl<T: Default> IndexMut<u32> for BuddyMemory<T> {
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        &mut self.memory[index as usize]
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
