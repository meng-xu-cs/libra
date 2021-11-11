module 0x42::TestSome {
    spec fun spec_fun_choice(x: u64): u64 {
        choose y: u64 where y >= (x + 42)
    }
    fun with_spec_fun_choice(x: u64): u64 {
        x + 42
    }
    spec with_spec_fun_choice {
        ensures result <= spec_fun_choice(x);
    }
}
