use std::{arch::asm, mem};

pub fn create_capab<T>(ptr: *mut T) -> *mut T {
    let base = ptr as *const i32 as *const () as usize;
    let top = base + mem::size_of::<T>();
    unsafe {
        let mut returned_ptr: *mut T = std::ptr::null_mut();
        asm!(
            "mv t0, {base}",
            "mv t1, {top}",
            // ".insn r 0x5b, 0x1, 0x4, {returned_ptr}, t0, x2", // LCC
            ".insn r 0x5b, 0x1, 0x4, t3, {ptr}, x8", // LCC 
            "bnez t3, 42", // If t3 is not 0, that means it is 1, which means it is already a capab, and hence skip the GENCAP
            ".insn r 0x5b, 0x1, 0x40, t2, t0, t1",  // GENCAP
            "42: .insn r 0x5b, 0x1, 0x43, x0, t2, x0", // PRINT
            "mv {returned_ptr}, t2",
            base = in(reg) base,
            top = in(reg) top,
            ptr = in(reg) ptr,
            returned_ptr = out(reg) returned_ptr,
        );
        returned_ptr
    }
}

pub fn debug_print<T: std::fmt::Debug>(ptr: *mut T) {
    unsafe {
        println!("ptr: {:?}", ptr);
        println!("*ptr: {:?}", *ptr);
    }
}