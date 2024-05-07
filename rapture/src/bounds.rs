#[derive(Clone, Copy)]
pub struct Bounds {
    pub(crate) base: usize,
    pub(crate) top: usize
}

impl Bounds {
    pub fn size(&self) -> usize {
        self.top - self.base
    }

    pub fn from_ref<T>(r: &T) -> Self where T: ?Sized {
        let base = r as *const T as *const () as usize;
        Self {
            base: base,
            top: base + std::mem::size_of_val(r)
        }
    }

    pub fn from_ptr<T>(p: *const T) -> Self {
        let base = p as usize;
        Self {
            base: base,
            top: base + std::mem::size_of::<T>()
        }
    }

    pub unsafe fn from_ptr_unsized<T>(p: *const T) -> Self where T: ?Sized {
        let base = p as *const() as usize;
        Self {
            base: base,
            top: base + std::mem::size_of_val(&*p)
        }
    }

    pub fn from_ptr_custom_size_offset(p: *const (), offset: usize, unit_size: usize) -> Self {
        let base = p as usize + offset;
        Self {
            base: base,
            top: base + unit_size
        }
    }

    pub fn size_fits<T>(&self) -> bool {
        self.size() >= std::mem::size_of::<T>()
    }

    pub fn in_bounds<T>(&self, addr: usize) -> bool {
        let obj_top = addr + std::mem::size_of::<T>();
        self.base <= addr && obj_top <= self.top
    }

    pub fn contains(&self, other: &Self) -> bool {
        self.base <= other.base && self.top >= other.top
    }

    pub fn intersects(&self, other: &Self) -> bool {
        (self.base < other.top && other.top <= self.top) || (self.base <= other.base && other.base < self.top)
    }
}
