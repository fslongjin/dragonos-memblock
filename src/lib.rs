use spin::{Mutex, MutexGuard};
use system_error::SystemError;

use misc::{PhysAddr, PhysMemoryArea};

mod misc;

pub const INITIAL_MEMORY_REGIONS_NUM: usize = 128;

/// 初始内存区域
static MEM_BLOCK_MANAGER: MemBlockManager = MemBlockManager::new();

/// 内存区域管理器
#[derive(Debug)]
pub struct MemBlockManager {
    inner: Mutex<InnerMemBlockManager>,
}

#[derive(Debug)]
struct InnerMemBlockManager {
    /// 初始内存区域
    ///
    /// 用于记录内核启动时的内存布局, 这些区域保持升序、不重叠
    initial_memory_regions: [PhysMemoryArea; INITIAL_MEMORY_REGIONS_NUM],
    initial_memory_regions_num: usize,
}

impl MemBlockManager {
    const fn new() -> Self {
        Self {
            inner: Mutex::new(InnerMemBlockManager {
                initial_memory_regions: [PhysMemoryArea::DEFAULT; INITIAL_MEMORY_REGIONS_NUM],
                initial_memory_regions_num: 0,
            }),
        }
    }

    /// 添加内存区域
    ///
    /// 如果添加的区域与已有区域有重叠，会将重叠的区域合并
    pub fn add_block(&self, block: PhysMemoryArea) -> Result<(), SystemError> {
        if block.size == 0 {
            return Ok(());
        }
        let mut inner = self.inner.lock();
        if inner.initial_memory_regions_num >= INITIAL_MEMORY_REGIONS_NUM {
            panic!("Too many memory regions!");
        }

        // 特判第一个区域
        if inner.initial_memory_regions_num == 0 {
            inner.initial_memory_regions[0] = block;
            inner.initial_memory_regions_num += 1;
            return Ok(());
        }

        // 先计算需要添加的区域数量
        let blocks_to_add = self
            .do_add_block(&mut inner, block, false)
            .expect("Failed to count blocks to add!");

        if inner.initial_memory_regions_num + blocks_to_add > INITIAL_MEMORY_REGIONS_NUM {
            eprintln!("Too many memory regions!");
            return Err(SystemError::ENOMEM);
        }

        // 然后添加区域
        self.do_add_block(&mut inner, block, true)
            .expect("Failed to add block!");

        return Ok(());
    }

    fn do_add_block(
        &self,
        inner: &mut MutexGuard<'_, InnerMemBlockManager>,
        block: PhysMemoryArea,
        insert: bool,
    ) -> Result<usize, SystemError> {
        let mut base = block.base;
        let end = block.base + block.size;
        let mut i = 0;
        let mut start_index = -1;
        let mut end_index = -1;

        let mut num_to_add = 0;

        while i < inner.initial_memory_regions_num {
            let range_base = inner.initial_memory_regions[i].base;
            let range_end =
                inner.initial_memory_regions[i].base + inner.initial_memory_regions[i].size;

            if range_base >= end {
                break;
            }
            if range_end <= base {
                i += 1;
                continue;
            }

            // 有重叠

            if range_base > base {
                num_to_add += 1;
                if insert {
                    if start_index == -1 {
                        start_index = i as isize;
                    }
                    end_index = (i + 1) as isize;
                    self.do_insert_area(inner, i, base, range_base - base);
                    i += 1;
                }
            }

            i += 1;
            base = core::cmp::min(range_end, end);
        }

        if base < end {
            num_to_add += 1;
            if insert {
                if start_index == -1 {
                    start_index = i as isize;
                }
                end_index = (i + 1) as isize;
                self.do_insert_area(inner, i, base, end - base);
            }
        }

        if num_to_add == 0 {
            return Ok(0);
        }

        if insert {
            self.do_merge_blocks(inner, start_index, end_index);
        }
        return Ok(num_to_add);
    }

    fn do_insert_area(
        &self,
        inner: &mut MutexGuard<'_, InnerMemBlockManager>,
        index: usize,
        base: PhysAddr,
        size: usize,
    ) {
        let copy_elements = inner.initial_memory_regions_num - index;
        inner
            .initial_memory_regions
            .copy_within(index..index + copy_elements, index + 1);
        inner.initial_memory_regions[index] = PhysMemoryArea::new(base, size);
        inner.initial_memory_regions_num += 1;
    }

    fn do_merge_blocks(
        &self,
        inner: &mut MutexGuard<'_, InnerMemBlockManager>,
        start_index: isize,
        mut end_index: isize,
    ) {
        let mut i = 0;
        if start_index > 0 {
            i = start_index - 1;
        }
        end_index = core::cmp::min(end_index, inner.initial_memory_regions_num as isize - 1);

        while i < end_index {
            {
                let next_base = inner.initial_memory_regions[(i + 1) as usize].base;
                let next_size = inner.initial_memory_regions[(i + 1) as usize].size;
                let this = &mut inner.initial_memory_regions[i as usize];

                if this.base + this.size != next_base {
                    // BUG_ON(this->base + this->size > next->base);
                    i += 1;
                    continue;
                }
                this.size += next_size;
            }
            // 移动后面的区域
            let copy_elements = inner.initial_memory_regions_num - (i + 2) as usize;
            inner.initial_memory_regions.copy_within(
                (i + 2) as usize..(i as usize + 2 + copy_elements),
                (i + 1) as usize,
            );

            inner.initial_memory_regions_num -= 1;
            end_index -= 1;
        }
    }

    /// 移除内存区域
    ///
    /// 如果移除的区域与已有区域有重叠，会将重叠的区域分割
    pub fn remove_block(&self, block: PhysMemoryArea) -> Result<(), SystemError> {
        if block.size == 0 {
            return Ok(());
        }
        let mut inner = self.inner.lock();
        if inner.initial_memory_regions_num == 0 {
            return Ok(());
        }

        let (start_index, end_index) = self
            .isolate_range(&mut inner, block.base, block.size)
            .expect("Failed to isolate range!");

        for i in (start_index..end_index).rev() {
            self.do_remove_region(&mut inner, i);
        }
        return Ok(());
    }

    fn do_remove_region(&self, inner: &mut MutexGuard<'_, InnerMemBlockManager>, index: usize) {
        let copy_elements = inner.initial_memory_regions_num - index - 1;
        inner
            .initial_memory_regions
            .copy_within(index + 1..index + 1 + copy_elements, index);

        inner.initial_memory_regions_num -= 1;

        if inner.initial_memory_regions_num == 0 {
            inner.initial_memory_regions[0].base = PhysAddr::new(0);
            inner.initial_memory_regions[0].size = 0;
        }
    }

    fn isolate_range(
        &self,
        inner: &mut MutexGuard<'_, InnerMemBlockManager>,
        base: PhysAddr,
        size: usize,
    ) -> Result<(usize, usize), SystemError> {
        let end = base + size;

        let mut idx = 0;

        let mut start_index = 0;
        let mut end_index = 0;

        if size == 0 {
            return Ok((0, 0));
        }

        while idx < inner.initial_memory_regions_num {
            let range_base = inner.initial_memory_regions[idx].base;
            let range_end = range_base + inner.initial_memory_regions[idx].size;

            if range_base >= end {
                break;
            }
            if range_end <= base {
                idx = idx.checked_add(1).unwrap_or(0);
                continue;
            }

            if range_base < base {
                // regions[idx] intersects from below
                inner.initial_memory_regions[idx].base = base;
                inner.initial_memory_regions[idx].size -= base - range_base;
                self.do_insert_area(inner, idx, range_base, base - range_base);
            } else if range_end > end {
                // regions[idx] intersects from above
                inner.initial_memory_regions[idx].base = end;
                inner.initial_memory_regions[idx].size -= end - range_base;

                self.do_insert_area(inner, idx, range_base, end - range_base);
                if idx == 0 {
                    idx = usize::MAX;
                } else {
                    idx -= 1;
                }
            } else {
                // regions[idx] is inside the range, record it
                if end_index == 0 {
                    start_index = idx;
                }
                end_index = idx + 1;
            }

            idx = idx.checked_add(1).unwrap_or(0);
        }

        return Ok((start_index, end_index));
    }

    #[cfg(test)]
    fn get_initial_memory_regions(&self) -> usize {
        let inner = self.inner.lock();
        return inner.initial_memory_regions_num;
    }

    #[cfg(test)]
    fn get_initial_memory_region(&self, index: usize) -> PhysMemoryArea {
        let inner = self.inner.lock();
        return inner.initial_memory_regions[index];
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_add_no_block() {
        let manager = MemBlockManager::new();

        assert_eq!(manager.get_initial_memory_regions(), 0);
    }

    #[test]
    fn test_add_one_block() {
        let manager = MemBlockManager::new();

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 1000)
        );
    }

    // 添加2个紧邻的区域
    #[test]
    fn test_add_two_blocks_near() {
        let manager = MemBlockManager::new();

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 1000))
            .expect("Failed to add block!");
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2000), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
    }

    // 添加2个不紧邻的区域
    #[test]
    fn test_add_two_blocks_not_near() {
        let manager = MemBlockManager::new();

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(5000), 1000))
            .expect("Failed to add block!");
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 3000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 3000)
        );

        assert_eq!(
            manager.get_initial_memory_region(1),
            PhysMemoryArea::new(PhysAddr::new(5000), 1000)
        );
    }

    /// 区域A，B，C
    ///
    ///     ----- -----
    ///     | A | | B |
    ///     ----- -----
    /// ------
    /// | C  |
    /// ------
    #[test]
    fn test_add_three_blocks_1() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 1200))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2000), 500))
            .expect("Failed to add block!");
        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(4000), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 1500)
        );
    }

    /// 区域A，B，C
    ///
    ///    ----  -----  
    ///   | A |  | B |  
    ///   -----  -----  
    /// -----------------
    /// | C             |
    /// -----------------
    #[test]
    fn test_add_three_blocks_2() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 3000))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1500), 500))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2500), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 3000)
        );
    }

    /// 区域A，B，C
    ///
    ///    ----  -----  
    ///   | A |  | B |  
    ///   -----  -----  
    ///     -----------------
    ///     | C             |
    ///     -----------------
    #[test]
    fn test_add_three_blocks_3() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(800), 3000))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 500))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 3300)
        );
    }

    /// 区域A，B，C
    ///
    ///    ----  -----  
    ///   | A |  | B |  
    ///   -----  -----  
    ///     ----------
    ///     | C      |
    ///     ----------
    #[test]
    fn test_add_three_blocks_4() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(800), 3000))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 500))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2000), 1800))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 3300)
        );
    }

    /// 区域A，B，C
    ///
    ///    ----  -----  
    ///   | A |  | B |  
    ///   -----  -----  
    ///     ---------
    ///     | C     |
    ///     ---------
    #[test]
    fn test_add_three_blocks_5() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(800), 2900))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 500))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2000), 1800))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 3300)
        );
    }

    /// 区域A，B，C
    ///
    ///    ----  -----  
    ///   | A |  | B |  
    ///   -----  -----  
    ///     ------
    ///     | C  |
    ///     ------
    #[test]
    fn test_add_three_blocks_6() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 1500))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 800))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2500), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 3000)
        );
    }

    /// 区域A，B，C
    ///
    ///    ----  -----  
    ///   | A |  | B |  
    ///   -----  -----  
    ///     -----
    ///     | C |
    ///     -----
    #[test]
    fn test_add_three_blocks_7() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 1400))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 800))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2500), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 1900)
        );

        assert_eq!(
            manager.get_initial_memory_region(1),
            PhysMemoryArea::new(PhysAddr::new(2500), 1000)
        );
    }

    /// 区域A，B，C
    ///
    ///    ----  -----  
    ///   | A |  | B |  
    ///   -----  -----  
    ///     ---
    ///     |C|
    ///     ---
    #[test]
    fn test_add_three_blocks_8() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 300))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 800))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2500), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 800)
        );

        assert_eq!(
            manager.get_initial_memory_region(1),
            PhysMemoryArea::new(PhysAddr::new(2500), 1000)
        );
    }

    /// 区域A，B，C
    ///
    ///    ----  -----  
    ///   | A |  | B |  
    ///   -----  -----  
    ///    ---
    ///    |C|
    ///    ---
    #[test]
    fn test_add_three_blocks_9() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 200))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 800))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2500), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 800)
        );

        assert_eq!(
            manager.get_initial_memory_region(1),
            PhysMemoryArea::new(PhysAddr::new(2500), 1000)
        );
    }

    /// 区域A，B，C
    ///
    ///    ----     -----  
    ///   | A |     | B |  
    ///   -----     -----  
    ///         ---
    ///         |C|
    ///         ---
    #[test]
    fn test_add_three_blocks_10() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1400), 200))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 800))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2500), 1000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 3);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 800)
        );

        assert_eq!(
            manager.get_initial_memory_region(1),
            PhysMemoryArea::new(PhysAddr::new(1400), 200)
        );

        assert_eq!(
            manager.get_initial_memory_region(2),
            PhysMemoryArea::new(PhysAddr::new(2500), 1000)
        );
    }

    /// 区域A，B，C,D
    ///
    ///    ----  -----  -----
    ///   | A |  | B |  | D |
    ///   -----  -----  -----
    /// -----------
    /// | C       |
    /// -----------
    #[test]
    fn test_add_four_blocks_1() {
        let manager = MemBlockManager::new();

        // C
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 2000))
            .expect("Failed to add block!");
        // A
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1500), 500))
            .expect("Failed to add block!");

        // B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(2500), 1000))
            .expect("Failed to add block!");

        // D
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(4000), 500))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);

        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2500)
        );

        assert_eq!(
            manager.get_initial_memory_region(1),
            PhysMemoryArea::new(PhysAddr::new(4000), 500)
        );
    }

    /// 区域A，C
    ///
    ///    --------------  
    ///   |       A      |  
    ///   ----------------  
    ///
    /// 移除 C
    ///         ---
    ///         |C|
    ///         ---
    #[test]
    fn test_remove_block_1() {
        let manager = MemBlockManager::new();

        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 2000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(1500), 500))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 500)
        );
        assert_eq!(
            manager.get_initial_memory_region(1),
            PhysMemoryArea::new(PhysAddr::new(2000), 1000)
        );
    }

    /// 区域A，C
    ///
    ///    --------------  
    ///   |       A      |  
    ///   ----------------  
    ///
    /// 移除 C
    ///                     ---
    ///                     |C|
    ///                     ---
    #[test]
    fn test_remove_block_2() {
        let manager = MemBlockManager::new();

        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 2000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(3500), 500))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
    }

    /// 区域A，C
    ///
    ///    --------------  
    ///   |       A      |  
    ///   ----------------  
    ///
    /// 移除 C
    ///                  ---
    ///                  |C|
    ///                  ---
    #[test]
    fn test_remove_block_3() {
        let manager = MemBlockManager::new();

        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 2000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(3000), 500))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
    }

    /// 区域A，C
    ///
    ///    --------------  
    ///   |       A      |  
    ///   ----------------  
    ///
    /// 移除 C
    ///                 -----
    ///                 | C |
    ///                 -----
    #[test]
    fn test_remove_block_4() {
        let manager = MemBlockManager::new();
        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 2000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(2800), 500))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 1800)
        );
    }

    /// 区域A，C
    ///
    ///      --------------  
    ///     |       A      |  
    ///     ----------------  
    ///
    /// 移除 C
    ///   ---
    ///   |C|
    ///   ---
    #[test]
    fn test_remove_block_5() {
        let manager = MemBlockManager::new();

        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 2000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(500), 500))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
    }

    /// 区域A，C
    ///
    ///      --------------  
    ///     |       A      |  
    ///     ----------------  
    ///
    /// 移除 C
    ///   -----
    ///   | C |
    ///   -----
    #[test]
    fn test_remove_block_6() {
        let manager = MemBlockManager::new();

        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 2000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(500), 700))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1200), 1800)
        );
    }

    /// 区域A，B，C
    ///
    ///          --------------  
    ///         |       A      |  
    ///         ----------------  
    ///
    /// 移除 C
    ///   -----
    ///   | C |
    ///   -----
    #[test]
    fn test_remove_block_7() {
        let manager = MemBlockManager::new();

        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1000), 2000))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(500), 300))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(1000), 2000)
        );
    }

    /// 区域A，C
    ///
    ///    ------     -------  
    ///   |  A  |     |  B  |  
    ///   -------     -------  
    ///
    /// 移除 C
    ///           ---
    ///           |C|
    ///           ---
    #[test]
    fn test_remove_block_8() {
        let manager = MemBlockManager::new();

        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 500))
            .expect("Failed to add block!");
        // 添加B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1500), 500))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);
  
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(1200), 100))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 500)
        );
        assert_eq!(
            manager.get_initial_memory_region(1),
            PhysMemoryArea::new(PhysAddr::new(1500), 500)
        );
    }

    /// 区域A，C
    ///
    ///    ------     -------  
    ///   |  A  |     |  B  |  
    ///   -------     -------  
    ///
    /// 移除 C
    ///        -----------
    ///        |    C    |
    ///        -----------
    #[test]
    fn test_remove_block_9() {
        let manager = MemBlockManager::new();

        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 500))
            .expect("Failed to add block!");
        // 添加B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1500), 500))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);
  
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(600), 1000))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 100)
        );
        assert_eq!(
            manager.get_initial_memory_region(1),
            PhysMemoryArea::new(PhysAddr::new(1600), 400)
        );
    }

    /// 区域A，C
    ///
    ///    ------     -------  
    ///   |  A  |     |  B  |  
    ///   -------     -------  
    ///
    /// 移除 C
    ///             -----------
    ///             |    C    |
    ///             -----------
    #[test]
    fn test_remove_block_10() {
        let manager = MemBlockManager::new();

        // 添加A

        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(500), 500))
            .expect("Failed to add block!");
        // 添加B
        manager
            .add_block(PhysMemoryArea::new(PhysAddr::new(1500), 500))
            .expect("Failed to add block!");

        assert_eq!(manager.get_initial_memory_regions(), 2);
  
        // 移除C

        manager
            .remove_block(PhysMemoryArea::new(PhysAddr::new(1200), 1000))
            .expect("Failed to remove block!");

        assert_eq!(manager.get_initial_memory_regions(), 1);
        assert_eq!(
            manager.get_initial_memory_region(0),
            PhysMemoryArea::new(PhysAddr::new(500), 500)
        );
        
    }
}
