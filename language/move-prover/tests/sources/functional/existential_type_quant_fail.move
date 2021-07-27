address 0x2 {
module S {
    struct S<X: store> has key {
        x: X,
        v: u64,
    }

    public fun set_x<X: store>(addr: address) acquires S {
        let r = borrow_global_mut<S<X>>(addr);
        *&mut r.v = 0;
    }

    public fun set_u64(addr: address) acquires S {
        let r = borrow_global_mut<S<u64>>(addr);
        *&mut r.v = 1;
    }

    public fun publish_x<X: store>(addr: signer, x: X) {
        move_to<S<X>>(&addr, S { x, v: 0 });
    }

    public fun publish_u64(addr: signer, x: u64) {
        move_to<S<u64>>(&addr, S { x, v: 1 });
    }

    // I1
    invariant
        exists t: type:
            exists<S<t>>(@0x22) ==> global<S<t>>(@0x22).v == 0;

    // I2
    invariant
        exists t: type:
            exists<S<t>>(@0x23) ==> global<S<t>>(@0x23).v == 1;

    // I1 SHOULD NOT verify in `set_u64`, an evidence is here:
    // - suppose that the global state contains a single memory cell:
    //   `0x22 -> S<u64> { x: _, v: 0 }`
    //   hence the base case satisfies
    // - run `set_u64`, get `0x22 -> S<u64> { x: _, v: 1 }` in the end,
    //   this invariant is violated
    //
    // I1 SHOULD NOT verify in `publish_u64`, an evidence is here:
    // - suppose that the global state contains no memory cells:
    //   hence the base case satisfies
    // - run `publish_u64`, get `0x22 -> S<u64> { x: _, v: 1 }` in the end,
    //   this invariant is violated

    // I2 SHOULD NOT verify in `set_x`, an evidence is here:
    // - suppose that the global state contains a single memory cell:
    //   `0x23 -> S<#0> { x: _, v: 1 }`
    //   hence the base case satisfies
    // - run `set_x<#0>`, get `0x23 -> S<#0> { x: _, v: 0 }` in the end,
    //   this invariant is violated
    //
    // I2 SHOULD NOT verify in `publish_x`, an evidence is here:
    // - suppose that the global state contains no single memory cells:
    //   hence the base case satisfies
    // - run `set_x<#0>`, get `0x23 -> S<#0> { x: _, v: 0 }` in the end,
    //   this invariant is violated
}
}
