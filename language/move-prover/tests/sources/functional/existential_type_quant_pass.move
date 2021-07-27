address 0x2 {
module S1 {
    struct S<X: store> has key {
        x: X,
        v: u64,
    }

    public fun publish<X: store>(addr: signer, x: X) {
        move_to<S<X>>(&addr, S { x, v: 0 });
        move_to<S<u8>>(&addr, S { x: 0, v: 1 });
    }

    // I1
    invariant
        exists t: type:
            exists<S<t>>(@0x22) ==> global<S<t>>(@0x22).v == 0;

    // I2: this should not verify
    // invariant
    //    exists t: type:
    //        exists<S<t>>(@0x23) ==> global<S<t>>(@0x23).v == 1;
}

module S2 {
    struct S<X: store> has key {
        x: X,
        v: u64,
    }

    public fun publish<X: store>(addr: signer, x: X) {
        move_to<S<u8>>(&addr, S { x: 0, v: 1 });
        move_to<S<X>>(&addr, S { x, v: 0 });
    }

    // I1: this should not verify
    // invariant
    //    exists t: type:
    //        exists<S<t>>(@0x22) ==> global<S<t>>(@0x22).v == 0;

    // I2
    invariant
        exists t: type:
            exists<S<t>>(@0x23) ==> global<S<t>>(@0x23).v == 1;
}
}
