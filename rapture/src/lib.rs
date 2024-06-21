use std::{arch::asm, mem};

pub fn create_capab_from_ptr<T>(ptr: *mut T) -> *mut T {
    println!("\nIn function create_capab_from_ptr");
    let base = ptr as *const T as *const () as usize;
    let top = base + mem::size_of::<T>();
    unsafe {
        let mut returned_ptr: *mut T = std::ptr::null_mut();
        asm!(
            "mv t0, {base}",
            "mv t1, {top}",
            // ".insn r 0x5b, 0x1, 0x4, {returned_ptr}, t0, x2", // LCC
            "mv t2, {ptr}",
            ".insn r 0x5b, 0x1, 0x4, t3, t2, x8", // LCC 
            "bnez t3, 42", // If t3 is not 0, that means it is 1, which means it is already a capab, and hence skip the GENCAP
            ".insn r 0x5b, 0x1, 0x40, t2, t0, t1",  // GENCAP
            "42: .insn r 0x5b, 0x1, 0x43, x0, t2, x0", // PRINT -- just to test what the capab is after this call (for debugging purposes)
            "mv {returned_ptr}, t2",
            base = in(reg) base,
            top = in(reg) top,
            ptr = in(reg) ptr,
            returned_ptr = out(reg) returned_ptr,
        );
        returned_ptr
    }
}

pub fn create_capab_from_ref<T>(ref_: &T) -> &mut T {
    println!("\nIn function create_capab_from_ref");
    let ptr = ref_ as *const T as *mut T;
    unsafe {
        let returned_ptr = create_capab_from_ptr(ptr);
        &mut *returned_ptr
    }
}

pub fn borrow_mut<T>(ptr: *mut T) -> *mut T {
    println!("\nIn function borrow_mut");
    // CSBORROWMUT: .insn r 0x5b, 0x1, 0b1100, rd, rs1, x0;      rs1 = source capab, rd = destination capab
    unsafe {
        let mut returned_ptr: *mut T = std::ptr::null_mut();
        asm!(
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- just to see what the source capab is before borrowing
            ".insn r 0x5b, 0x1, 0b1100, {returned_ptr}, {ptr}, x0", // CSBORROWMUT
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- just to see that the source capab has now changed
            ".insn r 0x5b, 0x1, 0x43, x0, {returned_ptr}, x0",  // PRINT -- just to see that the borrow happened successfully
            returned_ptr = out(reg) returned_ptr,
            ptr = in(reg) ptr,
        );
        returned_ptr
    }
}

pub fn borrow<T>(ptr: *mut T) -> *const T {
    println!("\nIn function borrow");
    // CSBORROW: .insn r 0x5b, 0x1, 0b1000, rd, rs1, x0;      rs1 = source capab, rd = destination capab
    unsafe {
        let mut returned_ptr: *const T = std::ptr::null();
        asm!(
            ".insn r 0x5b, 0x1, 0b1000, {returned_ptr}, {ptr}, x0", // CSBORROW
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- just to see that the source capab has now changed
            ".insn r 0x5b, 0x1, 0x43, x0, {returned_ptr}, x0",  // PRINT -- just to see that the borrow happened successfully
            returned_ptr = out(reg) returned_ptr,
            ptr = in(reg) ptr,
        );
        returned_ptr
    }
}

pub fn revoke<T>(ptr: *mut T) {
    println!("\nIn function revoke");
    unsafe {
        asm!(
            ".insn r 0x5b, 0b001, 0b0000000, x0, {ptr}, x0",    // REVOKE
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- testing that revoke happened
            ptr = in(reg) ptr,
        );
    }
}

pub fn debug_print_ptr<T: std::fmt::Debug>(ptr: *mut T) {
    println!("\nIn function debug_print");
    unsafe {
        asm!(
            ".insn r 0x5b, 0x1, 0x4, t3, {ptr}, x8", // LCC
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT - Raw value of the ptr
            ".insn r 0x5b, 0x1, 0x43, x0, t3, x0",           // PRINT - Is it a capab?
            ptr = in(reg) ptr,
        );
        println!("*ptr: {:?}", *ptr);
    }
}

pub fn debug_print_ref<T: std::fmt::Debug>(refr: &mut T) {
    let ptr = refr as *mut T;
    debug_print_ptr(ptr);
}

pub fn deref_print(ptr: *mut i32) {
    println!("Deref print: *ptr = {}", unsafe{*ptr});
}