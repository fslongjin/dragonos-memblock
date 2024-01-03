
/// 物理内存地址
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd, Hash)]
#[repr(transparent)]
pub struct PhysAddr(usize);

impl PhysAddr {
    #[inline(always)]
    pub const fn new(address: usize) -> Self {
        Self(address)
    }

    /// @brief 获取物理地址的值
    #[inline(always)]
    pub fn data(&self) -> usize {
        self.0
    }

    /// @brief 将物理地址加上一个偏移量
    #[inline(always)]
    pub fn add(self, offset: usize) -> Self {
        Self(self.0 + offset)
    }

    /// @brief 判断物理地址是否按照指定要求对齐
    #[inline(always)]
    pub fn check_aligned(&self, align: usize) -> bool {
        return self.0 & (align - 1) == 0;
    }

    #[inline(always)]
    pub fn is_null(&self) -> bool {
        return self.0 == 0;
    }
}

impl std::fmt::Debug for PhysAddr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "PhysAddr({:#x})", self.0)
    }
}

impl core::ops::Add<usize> for PhysAddr {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: usize) -> Self::Output {
        return Self(self.0 + rhs);
    }
}

impl core::ops::AddAssign<usize> for PhysAddr {
    #[inline(always)]
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl core::ops::Add<PhysAddr> for PhysAddr {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: PhysAddr) -> Self::Output {
        return Self(self.0 + rhs.0);
    }
}

impl core::ops::AddAssign<PhysAddr> for PhysAddr {
    #[inline(always)]
    fn add_assign(&mut self, rhs: PhysAddr) {
        self.0 += rhs.0;
    }
}

impl core::ops::BitOrAssign<usize> for PhysAddr {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: usize) {
        self.0 |= rhs;
    }
}

impl core::ops::BitOrAssign<PhysAddr> for PhysAddr {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: PhysAddr) {
        self.0 |= rhs.0;
    }
}

impl core::ops::Sub<usize> for PhysAddr {
    type Output = Self;

    #[inline(always)]
    fn sub(self, rhs: usize) -> Self::Output {
        return Self(self.0 - rhs);
    }
}

impl core::ops::SubAssign<usize> for PhysAddr {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: usize) {
        self.0 -= rhs;
    }
}

impl core::ops::Sub<PhysAddr> for PhysAddr {
    type Output = usize;

    #[inline(always)]
    fn sub(self, rhs: PhysAddr) -> Self::Output {
        return self.0 - rhs.0;
    }
}

impl core::ops::SubAssign<PhysAddr> for PhysAddr {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: PhysAddr) {
        self.0 -= rhs.0;
    }
}



/// @brief 物理内存区域
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PhysMemoryArea {
    /// 物理基地址
    pub base: PhysAddr,
    /// 该区域的物理内存大小
    pub size: usize,
}

impl PhysMemoryArea {
    pub const DEFAULT: Self = Self {
        base: PhysAddr::new(0),
        size: 0,
    };

    pub fn new(base: PhysAddr, size: usize) -> Self {
        Self { base, size }
    }

   
}

impl Default for PhysMemoryArea {
    fn default() -> Self {
        return Self::DEFAULT;
    }
}