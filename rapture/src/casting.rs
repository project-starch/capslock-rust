use std::any::TypeId;

pub trait DefaultMemoryCheckable {
    fn mem_valid(mem: &[u8]) -> bool;
}

impl<T> DefaultMemoryCheckable for &T where T: ?Sized {
    fn mem_valid(_mem: &[u8]) -> bool {
        false
    }
}

pub trait MemoryCheckable {
    fn mem_valid(mem: &[u8]) -> bool;
}

impl MemoryCheckable for bool {
    fn mem_valid(mem: &[u8]) -> bool {
        mem.len() > 0 && mem[0] < 2
    }
}

macro_rules! always_true_impl_memorycheckable {
    ($t:ty) => {
        impl MemoryCheckable for $t {
            fn mem_valid(_mem: &[u8]) -> bool {
                true
            }
        }
    }
}

// These following can just get valid values out of anything
always_true_impl_memorycheckable!{f32}
always_true_impl_memorycheckable!{f64}
always_true_impl_memorycheckable!{i128}
always_true_impl_memorycheckable!{i16}
always_true_impl_memorycheckable!{i32}
always_true_impl_memorycheckable!{i64}
always_true_impl_memorycheckable!{i8}
always_true_impl_memorycheckable!{isize}
always_true_impl_memorycheckable!{u128}
always_true_impl_memorycheckable!{u16}
always_true_impl_memorycheckable!{u32}
always_true_impl_memorycheckable!{u64}
always_true_impl_memorycheckable!{u8}
always_true_impl_memorycheckable!{usize}

pub struct TypeChecker {
    last_mut_ref_type: TypeId
}

impl TypeChecker {
    pub fn new<T>() -> Self where T: 'static + ?Sized {
        Self {
            last_mut_ref_type: TypeId::of::<T>()
        }
    }

    pub fn attempt_ref_checkable<T>(&mut self, bytes: &[u8], mutable: bool) -> bool where T: 'static + ?Sized + MemoryCheckable {
        let new_type_id = TypeId::of::<T>();
        if new_type_id == self.last_mut_ref_type || T::mem_valid(bytes) {
            if mutable {
                self.last_mut_ref_type = new_type_id;
            }
            true
        } else {
            false
        }
    }

    pub fn attempt_ref<T>(&self, _mutable: bool) -> bool where T: 'static + ?Sized {
        let new_type_id = TypeId::of::<T>();
        new_type_id == self.last_mut_ref_type
    }
}
