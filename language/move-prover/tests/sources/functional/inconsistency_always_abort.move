// flag: --check-inconsistency
// flag: --unconditional-abort-as-inconsistency
module 0x42::Inconsistency {
    // There is an inconsistent assumption in the verification of this function
    // because it always aborts.
    fun always_abort() {
        abort 0
    }
    spec always_abort {
        ensures false;
    }

    // Hiding the function behind some trivial if-else branch does not work
    fun always_abort_if_else(x: u64): bool {
        if (x == x) {
            abort 0
        } else {
            return true
        }
    }
    spec always_abort_if_else {
        ensures result == false;
    }

    // Calling an opaque function that unconditionally abort is also an
    // inconsistency
    fun always_abort_opaque() {}
    spec always_abort_opaque {
        pragma verify = false;
        pragma opaque;
        aborts_if true;
    }

    fun call_always_abort_opaque() {
        always_abort_opaque()
    }
    spec call_always_abort_opaque {
        ensures 1 == 2;
    }
}
