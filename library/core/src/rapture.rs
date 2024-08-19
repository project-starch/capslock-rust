use crate::arch::asm;

/// Create a capability from a pointer
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn create_capab_from_ptr<T>(ptr: *mut T) -> *mut T {
    let base = ptr as *const T as *const () as usize;
    let top = base + crate::mem::size_of::<T>();
    unsafe {
        let mut returned_ptr: *mut T;
        asm!(
            "mv t0, {base}",
            "mv t1, {top}",
            // ".insn r 0x5b, 0x1, 0x4, {returned_ptr}, t0, x2", // LCC
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0", // PRINT -- just to test what the capab is before this call (for debugging purposes)
            "mv t2, {ptr}",
            ".insn r 0x5b, 0x1, 0x4, t3, t2, x8", // LCC
            "bnez t3, 8f", // If t3 is not 0, that means it is 1, which means it is already a capab, and hence skip the GENCAP
            ".insn r 0x5b, 0x1, 0x40, t2, t0, t1",  // GENCAP
            "8: .insn r 0x5b, 0x1, 0x43, x0, t2, x0", // PRINT -- just to test what the capab is after this call (for debugging purposes)
            "mv {returned_ptr}, t2",
            ".insn r 0x5b, 0x1, 0x43, x0, {returned_ptr}, x0", // PRINT -- just to test what the capab is after this call (for debugging purposes)
            base = in(reg) base,
            top = in(reg) top,
            ptr = in(reg) ptr,
            returned_ptr = out(reg) returned_ptr,
            // Clobber
            out("t0") _,
            out("t1") _,
            out("t2") _,
            out("t3") _,
        );
        returned_ptr
    }
}

/// Create a capability from a reference
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn create_capab_from_ref<T>(ref_: &T) -> &mut T {
    let ptr = ref_ as *const T as *mut T;
    unsafe {
        let returned_ptr = create_capab_from_ptr(ptr);
        &mut *returned_ptr
    }
}


/// Create a capability from a shared reference
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn create_capab_from_shared_ref<T>(ref_: &T) -> &T {
    let ptr = ref_ as *const T as *mut T;
    unsafe {
        let returned_ptr = create_capab_from_ptr(ptr);
        &*returned_ptr
    }
}

/// Mutably borrow from a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow_mut<T>(ptr: *mut T) -> *mut T {
    // CSBORROWMUT: .insn r 0x5b, 0x1, 0b1100, rd, rs1, x0;      rs1 = source capab, rd = destination capab
    unsafe {
        let mut returned_ptr;
        asm!(
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- to see what the source capab is before borrowing
            ".insn r 0x5b, 0x1, 0x4, t0, {ptr}, x8",            // LCC -- to check that the source is indeed a capab
            "beqz t0, 16f",                                      // If t0 is 0, that means it is not a capab, and hence skip the CSBORROWMUT
            ".insn r 0x5b, 0x1, 0b1100, {returned_ptr}, {ptr}, x0", // CSBORROWMUT
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- to see that the source capab has now changed
            "j 8f",                                              // Skip the mv instruction in this case
            "16: mv {returned_ptr}, {ptr}",                     // If it is not a capab, then just return the ptr as is
            "8:.insn r 0x5b, 0x1, 0x43, x0, {returned_ptr}, x0",  // PRINT -- just to see whether the borrow happened
            returned_ptr = out(reg) returned_ptr,
            ptr = in(reg) ptr,
            // Clobber
            out("t0") _,
        );
        returned_ptr
    }
}

/// Immutably borrow from a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow<T>(ptr: *mut T) -> *const T {
    // CSBORROW: .insn r 0x5b, 0x1, 0b1000, rd, rs1, x0;      rs1 = source capab, rd = destination capab
    unsafe {
        let mut returned_ptr;
        asm!(
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- to see what the source capab is before borrowing
            ".insn r 0x5b, 0x1, 0x4, t0, {ptr}, x8",            // LCC -- to check that the source is indeed a capab
            "beqz t0, 16f",                                      // If t0 is 0, that means it is not a capab, and hence skip the CSBORROW
            ".insn r 0x5b, 0x1, 0b1000, {returned_ptr}, {ptr}, x0", // CSBORROW
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- to see that the source capab has now changed
            "j 8f",                                              // Skip the mv instruction in this case
            "16: mv {returned_ptr}, {ptr}",                     // If it is not a capab, then just return the ptr as is
            "8:.insn r 0x5b, 0x1, 0x43, x0, {returned_ptr}, x0",  // PRINT -- just to see whether the borrow happened
            returned_ptr = out(reg) returned_ptr,
            ptr = in(reg) ptr,
            // Clobber
            out("t0") _,
        );
        returned_ptr
    }
}

/// Convert a capability into a raw pointer (if it is a capability)
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn scrub<T>(ptr: *mut T) -> *mut T {
    let mut returned_ptr : *mut T;
    unsafe {
        asm!(
            ".insn r 0x5b, 0x1, 0x4, t0, {ptr}, x8",
            "mv {returned_ptr}, {ptr}",
            "beqz t0, 1f",
            ".insn r 0x5b, 0x1, 0x4, {returned_ptr}, {ptr}, x2",
            "1: nop",
            returned_ptr = out(reg) returned_ptr,
            ptr = in(reg) ptr,
            out("t0") _
        );
    }
    returned_ptr
}

/// Invalidate a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn invalidate<T>(ptr: *mut T) {
    // csdrop            0001011 .....    ..... 001 ..... 1011011 @r
    unsafe {
        asm!(
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- seeing the capab before revoking
            // ".insn r 0x5b, 0x1, 0x4, t0, {ptr}, x8",            // LCC -- to check that the source is indeed a capab
            // "beqz t0, 12f",                                      // If t0 is 0, that means it is not a capab, and hence skip the DROP
            ".insn r 0x5b, 0b001, 0b0001011, x0, {ptr}, x0",    // DROP
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT -- testing that revoke happened; this PRINT only happens if the revoke happened
            // "12:",                                             // Label for skipping the DROP
            ptr = in(reg) ptr,
        );
    }
}

/// Prints debug info about a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn debug_print_ptr<T>(ptr: *mut T) {
    unsafe {
        asm!(
            ".insn r 0x5b, 0x1, 0x4, t3, {ptr}, x8", // LCC
            ".insn r 0x5b, 0x1, 0x43, x0, {ptr}, x0",           // PRINT - Raw value of the ptr ".insn r 0x5b, 0x1, 0x43, x0, t3, x0",           // PRINT - Is it a capab?
            "lb t0, 0({ptr})",                                 // Load the first byte using the capab
            ptr = in(reg) ptr,
            // Clobber
            out("t3") _,
        );
    }
}