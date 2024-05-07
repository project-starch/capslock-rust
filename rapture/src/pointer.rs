use std::ops::Deref;
use std::arch::asm;
use crate::bounds::Bounds;
use crate::casting::{MemoryCheckable};

// TODO: Implement all instances where the capability box is currently being cloned

pub trait IndexMutBound {
    fn index_mut_bound<T>(&mut self, offset:usize, unit_size:usize);
}

pub trait HasRawInner {
    type RawInnerType : ?Sized;
    fn get_inner(&self) -> *const Self::RawInnerType;
}

// dynamic lifetime pointer with bounds
pub struct DLTBoundedPointer<T> where T: ?Sized {
    inner: *const T
    // owned object, should we use Rc<RefCell> for BorrowStack?
}

impl<T> DLTBoundedPointer<T> where T: Sized {
    pub unsafe fn offset(&self, idx: isize) -> Self {
        Self {
            inner: self.inner.offset(idx)
        }
    }

    pub unsafe fn to_offset(&mut self, idx: isize) {
        self.inner = self.inner.offset(idx);
    }
}

impl<T> DLTBoundedPointer<T> where T: Sized + MemoryCheckable {
    pub fn safe_offset(&self, idx: isize) -> Self {
        panic!("Unable to change offset!");
    }

    pub fn safe_to_offset(&mut self, idx: isize) {
        panic!("Unable to change offset!");
    }
}

// TODO: memory leak in case of box-backed pointer not handled now
// TODO: use-after-free check not there yet
impl<T> DLTBoundedPointer<T> where T: ?Sized + 'static {
    // TODO: expand this from original bounded ptr
    pub fn from_slt<'a>(slt_ptr: &DLTBoundedPointer<T>) -> Self {
        Self {
            inner: slt_ptr.inner
        }
    }

    // pub fn from_type<T>(item: T) -> Self {
    //     Self::from_box(Box::new(item))
    // }

    // pub fn from_slice(vec: Vec<T>) -> Self {
    //     Self::from_box(vec.into_boxed_slice())
    // }

    // this is going to leak the heap memory from the Box
    pub fn from_box(boxed: Box<T>) -> Self {
        let bounds = Bounds::from_ref(boxed.as_ref());
        let raw_ptr = Box::into_raw(boxed);
        // we need to create a new borrow stack now because it is no longer backed
        // by an owned object on stack
        Self {
            inner: raw_ptr as *const T
        }
    }

    pub fn reborrow(&self) -> Self {
        Self {
            inner: self.inner
        }
    }

    // This returns something with unbounded lifetime
    pub fn reborrow_slt(&self) -> DLTBoundedPointer<T> {
        // TODO: perform necessary checks and actions
        // TODO: expand this from original bounded ptr
        DLTBoundedPointer {
            inner: self.inner
        }
    }

    pub fn reborrow_slt_custom_bound(&self, bounds: Bounds) -> DLTBoundedPointer<T> {
        // TODO: perform necessary checks and actions
        // TODO: expand this from original bounded ptr
        DLTBoundedPointer {
            inner: self.inner
        }
    }

    /*pub fn to_box(&self) -> Box<T> {
        // this is considered a write
        self.ref_manager.borrow_stack.borrow_mut().invalidate(self.ref_manager.borrow_id);
        unsafe { Box::<T>::from_raw(self.inner as *mut T) }
    }

    pub fn free(&self) {
        let _ = self.to_box();
    }*/

    pub unsafe fn cast_to<U>(&self) -> DLTBoundedPointer<U> where U: Sized {
        DLTBoundedPointer {
            inner: self.inner as *const U
        }
    }

    // pub fn safe_cast_to<U>(&self) -> Option<DLTBoundedPointer<U>> where U: Sized {
        // if self.bounds.in_bounds::<U>(self.inner as *const () as usize) {
        //     Some(DLTBoundedPointer {
        //         inner: self.inner as *const U
        //     })
        // } else {
        //     None
        // }
    // }
}

impl<'a, T> Deref for DLTBoundedPointer<T> where T: ?Sized {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.inner }
    }
}

impl<T> IndexMutBound for MutDLTBoundedPointer<T> where T: ?Sized {
    fn index_mut_bound<T_>(&mut self, offset: usize, unit_size: usize){
        //let total_offset = offset * unit_size;
        //let deref_bounds = Bounds::from_ptr_custom_size_offset(self.inner as *const (), total_offset, unit_size);
        //assert!(self.ref_manager.borrow_stack.borrow().is_available(self.ref_manager.borrow_id, deref_bounds));
        //unsafe { &mut *(self.inner.byte_offset(total_offset as isize) as *mut T_) }
        println!("input received for deref, offset: {}, unit size: {}", offset, unit_size);
        if offset == 0 && unit_size == 0 {return;}
        let size = offset + unit_size - 1;
        let mem_offset = offset;
        unsafe {
            let mut capab_ptr = self.capability.as_mut_ptr() as *mut i128;
            let mut returned_ptr: *mut T_;
            asm!(
                ".insn i 0x5b, 0x3, t0, 0({capab_ptr})",
                ".insn r 0x5b, 0x1, 0x43, x0, t0, x0",
    
                "lb t1, 0(t0)",
                ".insn r 0x5b, 0x1, 0xc, t0, t0, {size}",
                "lb t1, 0(t0)",

                "li t2, -1",
                "mul {size}, {size}, t2",
                ".insn r 0x5b, 0x1, 0xc, t0, t0, {size}",

                ".insn r 0x5b, 0x1, 0xc, t0, t0, {mem_offset}",
                ".insn r 0x5b, 0x1, 0x4, {returned_ptr}, t0, x2",
    
                capab_ptr = inout(reg) capab_ptr,
                size = in(reg) size,
                mem_offset = in(reg) mem_offset,
                returned_ptr = out(reg) returned_ptr,
                out("t0") _,
                );
                println!("revocation capability {}", *(capab_ptr));
        }
    }
}

pub struct MutDLTBoundedPointer<T> where T: ?Sized {
    inner: *mut T,
    capability: Box<[u8; 16]>
}

impl<T> MutDLTBoundedPointer<T> where T: Sized {
    pub unsafe fn offset(&self, idx: isize) -> Self {
        Self {
            inner: self.inner.offset(idx),
            capability: self.capability.clone()
        }
    }

    pub unsafe fn to_offset(&mut self, idx: isize) {
        self.inner = self.inner.offset(idx);
    }
}

impl<T> MutDLTBoundedPointer<T> where T: Sized + MemoryCheckable {
    pub fn safe_offset(&self, idx: isize) -> Self {
        panic!("Unable to change offset!");
    }

    pub fn safe_to_offset(&mut self, idx: isize) {
        panic!("Unable to change offset!");
    }
}

impl<T> MutDLTBoundedPointer<T> where T: ?Sized + 'static + Clone {
    pub fn from_ref(item_ref: &mut T) -> Self {
        Self::from_box(Box::new(item_ref.clone()))
    }

    // pub fn from_slice(vec: Vec<T>) -> Self {
    //     Self::from_box(vec.into_boxed_slice())
    // }
}

// impl<T> MutDLTBoundedPointer<T> where T: ?Sized + 'static + Default {
//     pub fn from_type(item_ref: &mut T) -> Self {
//         // let mut item = *item_ref;
//         let mut replacement = T::new();
//         Self::from_box(Box::new(std::mem::replace(item_ref, replacement)))
//     }

//     // pub fn from_slice(vec: Vec<T>) -> Self {
//     //     Self::from_box(vec.into_boxed_slice())
//     // }
// }

impl<T> MutDLTBoundedPointer<T> where T: ?Sized + 'static {
    // TODO: expand this from original bounded ptr
    pub fn from_slt<'a>(slt_ptr: &MutDLTBoundedPointer<T>) -> Self {
        Self {
            inner: slt_ptr.inner,
            capability: slt_ptr.capability.clone()
        }
    }

    // this is going to leak the heap memory from the Box
    pub fn from_box(boxed: Box<T>) -> Self {
        let bounds = Bounds::from_ref(boxed.as_ref());
        let raw_ptr = Box::into_raw(boxed);
        // we need to create a new borrow stack now because it is no longer backed
        // by an owned object on stack
        let mut capab = Box::new([0u8; 16]);
        let mut capab_ptr = capab.as_mut_ptr() as *mut i128;
        println!("capab_ptr {}", capab_ptr as usize);
        unsafe {
            // TODO: remove all instances where GENCAP is used.
            // We currently convert the raw pointer to the box to a capability with GENCAP each time the box is used.
            // Eventually, this capab box should be accessed with a capablity, so GENCAP can be avoided.
            asm!(
                "mv t0, {base}",
                "mv t1, {top}",
                ".insn r 0x5b, 0x1, 0x40, t2, t0, t1",
                ".insn r 0x5b, 0x1, 0x43, x0, t2, x0",
                "addi t1, {capab_ptr}, 16",
                ".insn r 0x5b, 0x1, 0x40, {capab_ptr}, {capab_ptr}, t1",
                ".insn r 0x5b, 0x1, 0x43, x0, {capab_ptr}, x0",
                ".insn s 0x5b, 0x4, t2, 0({capab_ptr})",
                ".insn r 0x5b, 0x1, 0x43, x0, x0, x0",
                base = in(reg) bounds.base,
                top = in(reg) bounds.top,
                capab_ptr = inout(reg) capab_ptr,
                out("t0") _,
                out("t1") _,
                out("t2") _,
            );
            println!("base {}, top {}", bounds.base, bounds.top);
            println!("output {}", *(capab_ptr));
        }
        Self {
            inner: raw_ptr,
            capability: capab
        }
    }

    pub fn reborrow(&self) -> DLTBoundedPointer<T> {
        DLTBoundedPointer {
            inner: self.inner,
        }
    }

    pub fn reborrow_mut(&mut self) -> MutDLTBoundedPointer<T> {
        let mut borrowed_capab = Box::new([0u8; 16]);
        let mut borrowed_capab_ptr = borrowed_capab.as_mut_ptr() as *mut i128;
        unsafe {
            let mut capab_ptr = self.capability.as_mut_ptr() as *mut i128;
            asm!(
            ".insn i 0x5b, 0x3, t0, 0({capab_ptr})",
            ".insn r 0x5b, 0x1, 0x43, x0, t0, x0",

            ".insn r 0x5b, 0b001, 0b0001000, t1, t0, x0",
            ".insn r 0x5b, 0x1, 0x43, x0, t1, x0",

            ".insn s 0x5b, 0x4, t0, 0({borrowed_capab_ptr})",
            ".insn r 0x5b, 0x1, 0x43, x0, {borrowed_capab_ptr}, x0",

            ".insn s 0x5b, 0x4, t1, 0({capab_ptr})",
            ".insn r 0x5b, 0x1, 0x43, x0, {capab_ptr}, x0",

            capab_ptr = inout(reg) capab_ptr,
            borrowed_capab_ptr = inout(reg) borrowed_capab_ptr,
            out("t0") _,
            out("t1") _,   
            );

            println!("revocation capability {}", *(capab_ptr));
            println!("borrowed capability {}", *(borrowed_capab_ptr));
        }
        MutDLTBoundedPointer {
            inner: self.inner,
            capability: borrowed_capab
        }
    }

    pub fn reborrow_slt(&self) -> MutDLTBoundedPointer<T> {
        // TODO: expand this from original bounded ptr
        MutDLTBoundedPointer {
            inner: self.inner,
            capability: self.capability.clone()
        }
    }

    pub fn reborrow_slt_custom_bound(&self, bounds: Bounds) -> MutDLTBoundedPointer<T> {
        // TODO: perform necessary checks and actions
        // TODO: expand this from original bounded ptr
        MutDLTBoundedPointer {
            inner: self.inner,
            capability: self.capability.clone()
        }
    }

    pub fn invalidate(&mut self) {
        println!("A capability of type: {:?} is being invalidated!", std::any::type_name_of_val(&self));
        let mut capab_ptr = self.capability.as_mut_ptr() as *mut i128;
        unsafe {
            println!("capability before invalidate {}", *(capab_ptr));

            // obtaining the type bits from the capability (removed for the sake of localising the solultion to pure assembly, as much as possible)

            // let mut capab_type = (*(capab_ptr)).clone();
            // capab_type = capab_type << 34;
            // capab_type = capab_type >> (128 - 3);

            let mut capab_type: i8;
            asm!(
                ".insn i 0x5b, 0x3, t0, 0({capab_ptr})",
                ".insn r 0x5b, 0x1, 0x4, t3, t0, x1",
                "mv {capab_type}, t3",
                capab_ptr = in(reg) capab_ptr,
                capab_type = out(reg) capab_type,
                out("t0") _,
                out("t3") _,
            );

            println!("type before revoking {}", capab_type);

            if capab_type == 0b010 {
                asm!(
                    ".insn i 0x5b, 0x3, t0, 0({capab_ptr})",
                    ".insn r 0x5b, 0b001, 0b0000000, x0, t0, x0",
                    ".insn r 0x5b, 0x1, 0x43, x0, t0, x0",
                    ".insn s 0x5b, 0x4, t0, 0({capab_ptr})",
                    ".insn r 0x5b, 0x1, 0x4, t3, t0, x1",
                    "mv {capab_type}, t3",
                    capab_type = out(reg) capab_type,
                    capab_ptr = inout(reg) capab_ptr,
                    out("t0") _,
                    out("t3") _,
                );
                println!("capability after revoke {}", *(capab_ptr));
            }

            // capab_type = (*(capab_ptr)).clone();
            // capab_type = capab_type << 34;
            // capab_type = capab_type >> (128 - 3);

            println!("type after revoking {}", capab_type);

            asm!(
            ".insn i 0x5b, 0x3, t0, 0({capab_ptr})",
            ".insn r 0x5b, 0x1, 0x43, x0, t0, x0",
            ".insn r 0x5b, 0b001, 0b0001011, x0, t0, x0",
            ".insn r 0x5b, 0x1, 0x43, x0, t0, x0",
            ".insn s 0x5b, 0x4, t0, 0({capab_ptr})",
            ".insn r 0x5b, 0x1, 0x43, x0, x0, x0",
            capab_ptr = inout(reg) capab_ptr,
            out("t0") _,
            );
            println!("capability after invalidate {}", *(capab_ptr));
        }
    }

    pub fn split(&mut self, offset:usize) -> [MutDLTBoundedPointer<T>; 2] {
        let mut left_capab = Box::new([0u8; 16]);
        let mut left_capab_ptr = left_capab.as_mut_ptr() as *mut i128;
        let mut right_capab = Box::new([0u8; 16]);
        let mut right_capab_ptr = right_capab.as_mut_ptr() as *mut i128;
        unsafe {
            let mut capab_ptr = self.capability.as_mut_ptr() as *mut i128;
            asm!(
            ".insn i 0x5b, 0x3, t0, 0({capab_ptr})",
            ".insn r 0x5b, 0x1, 0x43, x0, t0, x0",

            ".insn r 0x5b, 0b001, 0b0001000, t1, t0, x0",
            ".insn r 0x5b, 0x1, 0x43, x0, t1, x0",

            ".insn s 0x5b, 0x4, t1, 0({capab_ptr})",
            ".insn r 0x5b, 0x1, 0x43, x0, {capab_ptr}, x0",

            ".insn r 0x5b, 0x1, 0x4, t3, t0, x3",
            "add t3, {offset}, t3",

            ".insn r 0x5b, 0b001, 0b0000110, t2, t0, t3",
            ".insn r 0x5b, 0x1, 0x43, x0, t0, x0",
            ".insn r 0x5b, 0x1, 0x43, x0, t2, x0",
            ".insn r 0x5b, 0x1, 0x43, x0, t3, x0",

            ".insn s 0x5b, 0x4, t0, 0({left_capab_ptr})",
            ".insn r 0x5b, 0x1, 0x43, x0, {left_capab_ptr}, x0",

            ".insn s 0x5b, 0x4, t2, 0({right_capab_ptr})",
            ".insn r 0x5b, 0x1, 0x43, x0, {right_capab_ptr}, x0",

            capab_ptr = inout(reg) capab_ptr,
            left_capab_ptr = inout(reg) left_capab_ptr,
            right_capab_ptr = inout(reg) right_capab_ptr,
            offset = in(reg) offset,
            out("t0") _,
            out("t1") _,
            out("t2") _,
            out("t3") _,
            );

            println!("revocation capability {}", *(capab_ptr));
            println!("left capability {}", *(left_capab_ptr));
            println!("right capability {}", *(right_capab_ptr));
        }
        [
        MutDLTBoundedPointer {
            inner: self.inner,
            capability: left_capab
        },
        MutDLTBoundedPointer {
            inner: self.inner,
            capability: right_capab
        }
        ]
    }

    /*pub fn to_box(&self) -> Box<T> {
        // this is considered a write
        self.ref_manager.borrow_stack.borrow_mut().invalidate(self.ref_manager.borrow_id);
        unsafe { Box::<T>::from_raw(self.inner as *mut T) }
    }

    pub fn free(&self) {
        let _ = self.to_box();
    }*/

    pub unsafe fn cast_to<U>(&self) -> MutDLTBoundedPointer<U> where U: Sized {
        MutDLTBoundedPointer {
            inner: self.inner as *mut U,
            capability: self.capability.clone()
        }
    }

    // pub fn safe_cast_to<U>(&self) -> Option<MutDLTBoundedPointer<U>> where U: Sized {
        // if self.bounds.in_bounds::<U>(self.inner as *const () as usize) {
        //     Some(MutDLTBoundedPointer {
        //         inner: self.inner as *mut U,
        //         capability: self.capability.clone()
        //     })
        // } else {
        //     None
        // }
    // }
}

#[macro_export]
macro_rules! dlt_index {
    ($e:expr, $i:expr, $t:ty) => {
        *$e.index_mut_bound::<$t>($i, std::mem::size_of::<$t>())
    };
}
pub use dlt_index;

#[macro_export]
macro_rules! dlt_offset {
    ($e:expr, $i:expr) => {
        *$e.index_mut_bound::<i8>($i, std::mem::size_of::<i8>())
    };
}
pub use dlt_offset;

#[macro_export]
macro_rules! dlt_deref {
    ($e:expr, $t:ty) => {
        *$e.index_mut_bound::<$t>(0, std::mem::size_of::<$t>())
    };
}
pub use dlt_deref;

#[macro_export]
macro_rules! dlt_box {
    ($e:expr) => {
        MutDLTBoundedPointer::from_box(Box::new($e))
    };
}
pub use dlt_box;

#[macro_export]
macro_rules! dlt_slice {
    ($e:expr) => {
        MutDLTBoundedPointer::from_box($e.into_boxed_slice())
    };
}
pub use dlt_slice;