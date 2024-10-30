use crate::arch::asm;

#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn create_capab_from_ptr_unsized<T>(ptr: *mut T, size : usize) -> *mut T where T : ?Sized {
    let base = ptr.addr();
    let top = base + size;
    unsafe {
        let returned_addr: usize;
        asm!(
            ".insn r 0x5b, 0x1, 0x40, {addr}, {base}, {top}",  // GENCAP
            // "8: .insn r 0x5b, 0x1, 0x43, x0, t2, x0", // PRINT -- just to test what the capab is after this call (for debugging purposes)
            // ".insn r 0x5b, 0x1, 0x43, x0, {returned_addr}, x0", // PRINT -- just to test what the capab is after this call (for debugging purposes)
            base = in(reg) base,
            top = in(reg) top,
            addr = out(reg) returned_addr,
        );
        ptr.with_addr(returned_addr)
    }
}

#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow_mut_ref<T>(r: &mut T) -> &mut T where T : ?Sized {
    unsafe { &mut *borrow_mut(r as *mut T) }
}


#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow_ref<T>(r: &T) -> &T where T : ?Sized {
    unsafe { &*borrow(r as *const T as *mut T) }
}

/// Mutably borrow from a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow_mut<T>(ptr: *mut T) -> *mut T where T : ?Sized {
    // CSBORROWMUT: .insn r 0x5b, 0x1, 0b1100, rd, rs1, x0;      rs1 = source capab, rd = destination capab
    // debug_print_ptr(core::ptr::null::<u64>().with_addr(0x44) as *mut u64);
    // let size = crate::mem::size_of::<T>();
    let size = crate::mem::size_of_val(unsafe {&*ptr});
    unsafe {
        let addr = ptr.addr();
        let returned_addr : usize;
        asm!(
            ".insn r 0x5b, 0x1, 0b1100, {returned_addr}, {addr}, {size}", // CSBORROWMUT
            returned_addr = out(reg) returned_addr,
            addr = in(reg) addr,
            size = in(reg) size,
        );
        ptr.with_addr(returned_addr)
    }
}

/// Immutably borrow from a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow<T>(ptr: *mut T) -> *const T where T : ?Sized {
    // CSBORROW: .insn r 0x5b, 0x1, 0b1000, rd, rs1, x0;      rs1 = source capab, rd = destination capab
    // debug_print_ptr(core::ptr::null::<u64>() as *mut u64);
    // let size = crate::mem::size_of::<T>();
    let size = crate::mem::size_of_val(unsafe {&*ptr});
    unsafe {
        let addr = ptr.addr();
        let returned_addr : usize;
        asm!(
            // ".insn r 0x5b, 0x1, 0x43, x0, {addr}, x0",           // PRINT -- to see what the source capab is before borrowing
            ".insn r 0x5b, 0x1, 0b1000, {returned_addr}, {addr}, {size}", // CSBORROW
            returned_addr = out(reg) returned_addr,
            addr = in(reg) addr,
            size = in(reg) size,
        );
        ptr.with_addr(returned_addr)
    }
}

/// Convert a capability into a raw pointer (if it is a capability)
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn scrub<T>(ptr: *mut T) -> *mut T where T : ?Sized {
    let returned_addr : usize;
    unsafe {
        let addr = ptr.addr();
        asm!(
            ".insn r 0x5b, 0x1, 0x4, {returned_addr}, {addr}, x2",
            returned_addr = out(reg) returned_addr,
            addr = in(reg) addr,
        );
    }
    ptr.with_addr(returned_addr)
}

/// Invalidate a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn invalidate<T>(ptr: *mut T) where T : ?Sized {
    // csdrop            0001011 .....    ..... 001 ..... 1011011 @r
    unsafe {
        let addr = ptr.addr();
        asm!(
            // ".insn r 0x5b, 0x1, 0x43, x0, {addr}, x0",           // PRINT -- seeing the capab before revoking
            // ".insn r 0x5b, 0x1, 0x4, t0, {addr}, x8",            // LCC -- to check that the source is indeed a capab
            // "beqz t0, 12f",                                      // If t0 is 0, that means it is not a capab, and hence skip the DROP
            ".insn r 0x5b, 0b001, 0b0001011, x0, {addr}, x0",    // DROP
            // ".insn r 0x5b, 0x1, 0x43, x0, {addr}, x0",           // PRINT -- testing that revoke happened; this PRINT only happens if the revoke happened
            // "12:",                                             // Label for skipping the DROP
            addr = in(reg) addr,
        );
    }
}

/// Prints debug info about a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn debug_print_ptr<T>(ptr: *mut T) where T : ?Sized {
    unsafe {
        let addr = ptr.addr();
        asm!(
            ".insn r 0x5b, 0x1, 0x4, t3, {addr}, x8", // LCC
            ".insn r 0x5b, 0x1, 0x43, x0, {addr}, x0",           // PRINT - Raw value of the addr ".insn r 0x5b, 0x1, 0x43, x0, t3, x0",           // PRINT - Is it a capab?
            // "lb t0, 0({addr})",                                 // Load the first byte using the capab
            addr = in(reg) addr,
            // Clobber
            out("t3") _,
        );
    }
}