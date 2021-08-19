module 0x2::Config {
    struct Config<T: copy + drop + store> has key, store {
        payload: T
    }

    public fun put<T: copy + drop + store>(addr: signer, payload: T) {
        move_to(&addr, Config { payload });
    }

    public fun set<T: copy + drop + store>(addr: address, payload: T)
    acquires Config {
        let cfg = borrow_global_mut<Config<T>>(addr);
        cfg.payload = payload;
    }

    public fun get<T: copy + drop + store>(addr: address): T
    acquires Config {
        *&borrow_global<Config<T>>(addr).payload
    }
}
