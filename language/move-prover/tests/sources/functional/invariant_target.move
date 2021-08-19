// flag: --dependency=tests/sources/functional/invariant_target_dep.move
module 0x2::Version {
    use 0x2::Config;

    struct Version has copy, drop, store {
        num: u64
    }

    public fun put_version(addr: signer) {
        Config::put(addr, Version { num: 1 });
    }

    public fun set_version(addr: address, num: u64) {
        let old_version = Config::get<Version>(addr);
        assert(old_version.num < num, 42);
        Config::set(addr, Version { num });
    }

    spec module {
        invariant
            forall addr: address where exists<Config::Config<Version>>(addr):
                global<Config::Config<Version>>(addr).payload.num != 0;
    }
}
