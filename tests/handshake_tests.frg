#lang forge

open "../models/core_handshake.frg"

-- Static Unit Tests)
test expect {
    dh_is_satisfiable: { dh_rules } for exactly 2 PrivateKey, exactly 2 PublicKey, exactly 1 SharedSecret is sat
    
    init_is_satisfiable: { init } for exactly 3 Node, exactly 2 PrivateKey, exactly 2 PublicKey, exactly 1 SharedSecret is sat
}

-- Temporal Trace Verification)

-- successful_handshake_state
pred successful_handshake_state {
    some ss: SharedSecret | {
        ss in Alice.knows
        ss in Bob.knows
        ss not in Eve.knows
    }
}

pred can_complete_handshake {
    traces
    eventually successful_handshake_state
}

test expect {
    verify_handshake_possible: {
        can_complete_handshake
    } for exactly 3 Node, exactly 2 PrivateKey, exactly 2 PublicKey, exactly 1 SharedSecret, 2 Message is sat
}