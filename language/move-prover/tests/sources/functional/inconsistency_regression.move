// flag: --check-inconsistency
module 0x42::Inconsistency {
    // This opaque function has the false post-condition, so it introduces an
    // inconsistency.
    fun inconsistent_opaque() {
    }
    spec inconsistent_opaque {
        pragma verify=false;
        pragma opaque;
        ensures false;
    }

    // There is an inconsistent assumption in the verification of this function
    // because it calls an inconsistent opaque function.
    fun call_inconsistent_opaque() {
        inconsistent_opaque();
    }
    spec call_inconsistent_opaque {
        ensures false;
    }
}

// NOTE: the inconsistency check did not report any inconsistency without the
// --unconditional-abort-as-inconsistency flag. Furthermore, the whole program
// verifies, where it should not.
//
// The reason can be found in the transformed bytecode after inconsistency
// check instrumentation:
//
// [variant verification[inconsistency_]]
// fun Inconsistency::call_inconsistent_opaque() {
//      var $t0: bool
//      var $t1: num
//      # >> opaque call: Inconsistency::inconsistent_opaque()
//   0: nop
//   1: opaque begin: Inconsistency::inconsistent_opaque()
//   2: havoc[val]($t0)
//   3: if ($t0) goto 4 else goto 7
//   4: label L4
//   5: trace_abort($t1)
//   6: goto 14
//   7: label L3
//   8: assume false
//   9: opaque end: Inconsistency::inconsistent_opaque()
//  10: label L1
//      # VC: post-condition does not hold at demo.move:14:9+14
//  11: assert false
//      # VC: expected to fail at demo.move:13:5+60
//  12: assert false  <-- instrumented and is verified
//  13: return ()
//  14: label L2
//      # VC: expected to fail at demo.move:13:5+60
//  15: assert false  <-- instrumented but does not verify
//  16: abort($t1)
// }
//
// As long as one of the instrumented `assert false` do not verify, the
// inconsistency check is considered to pass. In this case, the `assert false`
// on line 15 does not verify and hence, fooled the inconsistency checker that
// the program above does not have an inconsistency, and hide the real
// inconsistency which could be detected by line 12.
