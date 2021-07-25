address 0x2 {
module S {
    struct S<X: store> has key {
        x: X,
        v: u64,
    }

	public fun publish_x<X: store>(account: signer, x: X) {
	    move_to(&account, S { x, v: 0 })
	}

    public fun publish_u64(account: signer, x: u64) {
        move_to(&account, S { x, v: 1 })
    }

    // I1: this should verify, an evidence is X := bool
    invariant
        exists t: type:
            exists<S<t>>(@0x22) ==> global<S<t>>(@0x22).v == 0;

    // I2: this should not verify, x := u64 does not guarantee S<u64>.v == 1
    invariant
        exists t: type:
            exists<S<t>>(@0x23) ==> global<S<t>>(@0x23).v == 1;
}
}
