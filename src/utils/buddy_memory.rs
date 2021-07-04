use std::iter::repeat;

#[derive(Default)]
struct Block<T: Default> {
    tag: bool,
    linkf: usize,
    linkb: usize,
    kval: usize,
    data: T,
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

    pub fn reserve(&mut self, k: usize) -> usize {
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

        location
    }

    pub fn free(&mut self, location: usize) {
        let mut k = self.memory[location].kval;
        let mut L = location;

        loop {
            let buddy = L ^ (1 << k);

            if (k == self.m) || !self.memory[buddy].tag || self.memory[buddy].kval != k {
                break;
            }

            // S2. [Combine with buddy.]
            let linkb = self.memory[buddy].linkb;
            self.memory[linkb].linkf = self.memory[buddy].linkf;

            let linkf = self.memory[buddy].linkf;
            self.memory[linkf].linkb = self.memory[buddy].linkb;

            k += 1;
            if buddy < L {
                L = buddy;
            }
        }

        // S3. [Put on list.]
        self.memory[L].tag = true;
        let loc_k = self.loc_avail(k);
        let block = self.memory[loc_k].linkf;
        self.memory[L].linkf = block;
        self.memory[block].linkb = L;
        self.memory[L].kval = k;
        self.memory[L].linkb = loc_k;
        self.memory[loc_k].linkf = L;
    }
}

#[cfg(test)]
mod tests {
    use super::BuddyMemory;

    #[test]
    fn test_buddy_memory() {
        let mut mem = BuddyMemory::<u32>::new(3);

        assert_eq!(mem.reserve(2), 0);
        assert_eq!(mem.reserve(1), 4);
        assert_eq!(mem.reserve(0), 6);
        assert_eq!(mem.reserve(0), 7);

        mem.free(0);

        assert_eq!(mem.reserve(1), 0);
        assert_eq!(mem.reserve(1), 2);
    }
}
