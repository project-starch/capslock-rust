use crate::arch::asm;

#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn create_capab_from_ptr_unsized<T>(ptr: *mut T, size : usize) -> *mut T where T : ?Sized {
    let base = ptr.addr();
    let top = base + size;
    unsafe {
        let returned_addr: usize;
        asm!(
            ".insn r 0x5b, 0x1, 0x40, {addr}, {base}, {top}",  // GENCAP
            ".insn r 0x5b, 0x1, 0b1101, x0, {addr}, x0", // mark as UnsafeCell
            base = in(reg) base,
            top = in(reg) top,
            addr = out(reg) returned_addr,
        );
        ptr.with_addr(returned_addr)
    }
}

#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn shrink<T>(ptr: *const T, is_foreign : bool) -> *const T where T : ?Sized {
    let size = if is_foreign { 0 } else { crate::mem::size_of_val(unsafe {&*ptr}) };
    let returned_addr : usize;
    unsafe {
        let addr = ptr.addr();
        asm!(
            ".insn r 0x5b, 0x1, 0b1, {returned_addr}, {addr}, {size}", // CSBORROWMUT
            returned_addr = out(reg) returned_addr,
            addr = in(reg) addr,
            size = in(reg) size,
        );
    }
    ptr.with_addr(returned_addr)
}

#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn shrink_mut<T>(ptr: *mut T, is_foreign : bool) -> *mut T where T : ?Sized {
    shrink(ptr as *const T, is_foreign) as *mut T
}

#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn shrink_mut_ref<T>(r: &mut T, is_foreign : bool) -> &mut T where T : ?Sized {
    unsafe { &mut *shrink_mut(r as *mut T, is_foreign) }
}

#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn shrink_ref<T>(r: &T, is_foreign : bool) -> &T where T : ?Sized {
    unsafe { &*shrink(r as *const T, is_foreign) }
}

#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow_mut_ref<T>(r: &mut T, pointer_type : u8, is_foreign : bool) -> &mut T where T : ?Sized {
    unsafe { &mut *borrow_mut(r as *mut T, pointer_type, is_foreign) }
}


#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow_ref<T>(r: &T, pointer_type : u8, is_foreign : bool) -> &T where T : ?Sized {
    unsafe { &*borrow(r as *const T as *mut T, pointer_type, is_foreign) }
}

/// Mutably borrow from a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow_mut<T>(ptr: *mut T, pointer_type : u8, is_foreign : bool) -> *mut T where T : ?Sized {
    let size = if is_foreign { 0 } else { crate::mem::size_of_val(unsafe {&*ptr}) };
    let returned_addr : usize;
    unsafe {
        let addr = ptr.addr();
        asm!(
            ".insn r 0x5b, 0x1, 0b1100, {returned_addr}, {addr}, {size}", // CSBORROWMUT
            returned_addr = out(reg) returned_addr,
            addr = in(reg) addr,
            size = in(reg) size,
        );
    }
    if pointer_type != 0 {
        unsafe {
            asm!(
                ".insn r 0x5b, 0x1, 0b1101, x0, {addr}, {pointer_type}",
                addr = in(reg) returned_addr,
                pointer_type = in(reg) pointer_type,
            );
        }
    }
    ptr.with_addr(returned_addr)
}

/// Immutably borrow from a capability
#[stable(feature = "core_primitive", since = "1.43.0")]
pub fn borrow<T>(ptr: *mut T, pointer_type : u8, is_foreign : bool) -> *const T where T : ?Sized {
    let size = if is_foreign { 0 } else { crate::mem::size_of_val(unsafe {&*ptr}) };
    let returned_addr : usize;
    unsafe {
        let addr = ptr.addr();
        asm!(
            ".insn r 0x5b, 0x1, 0b1000, {returned_addr}, {addr}, {size}", // CSBORROW
            returned_addr = out(reg) returned_addr,
            addr = in(reg) addr,
            size = in(reg) size,
        );
    }
    if pointer_type != 0 {
        unsafe {
            asm!(
                ".insn r 0x5b, 0x1, 0b1101, x0, {addr}, {pointer_type}",
                addr = in(reg) returned_addr,
                pointer_type = in(reg) pointer_type,
            );
        }
    }
    ptr.with_addr(returned_addr)
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
    unsafe {
        let addr = ptr.addr();
        asm!(
            ".insn r 0x5b, 0b001, 0b0001011, x0, {addr}, x0",    // DROP
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
            addr = in(reg) addr,
            out("t3") _,
        );
    }
}