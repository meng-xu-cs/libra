module 0x42::M {
    use Std::Signer;

    struct S<X: store> has key { x: X }

    public fun extract<X: store>(account: signer, x: X) {
        move_to<S<X>>(&account, S { x });
        move_to<S<u8>>(&account, S { x: 0 });
    }
    spec extract {
        aborts_if exists<S<X>>(Signer::spec_address_of(account));
        aborts_if exists<S<u8>>(Signer::spec_address_of(account));

        // TODO: besides the above aborts_if conditions, this function
        // also aborts if the type parameter `X` is instantiated with `u8`.
        // This additional abort condition is not captured by the spec.
    }
}

module 0x42::N {
    use Std::Signer;

    struct S<X: store + drop> has key { x: X }

    public fun extract<X: store + drop>(account: signer, x: X) acquires S {
        move_to<S<u8>>(&account, S { x: 0 });
        let r = borrow_global_mut<S<X>>(Signer::address_of(&account));
        *&mut r.x = x;
    }
    spec extract {
        aborts_if exists<S<u8>>(Signer::spec_address_of(account));
        aborts_if !exists<S<X>>(Signer::spec_address_of(account));
        ensures global<S<u8>>(Signer::spec_address_of(account)).x == 0;

        // TODO: there are two issues with the spec
        // 1) the second `aborts_if` condition is necessary only when X != u8
        // 2) the `ensures` condition might not hold, as `extract<u8>(_, 1)`
        //    will violate the `ensures` condition.
    }
}
