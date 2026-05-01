#lang forge

open "../models/core_handshake.frg"

-- Static Unit Tests)
test expect {
    crypto_is_satisfiable: { 
        crypto_properties 
    } for exactly 3 Node, exactly 3 PrivateKey, exactly 3 PublicKey, exactly 1 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey is sat
    
    init_is_satisfiable: { 
        init 
    } for exactly 3 Node, exactly 3 PrivateKey, exactly 3 PublicKey, exactly 1 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey is sat
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
    } for exactly 3 Node, exactly 12 Key, exactly 4 PrivateKey, exactly 4 PublicKey, exactly 2 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey, exactly 4 Message is sat
}

-- 1. Vacuity Checks 

pred can_execute_ratchet {
    traces
    eventually { some s, r: Node | execute_ratchet_and_send[s, r] }
}

pred can_send_encrypted_data {
    traces
    eventually { some s, r: Node, d: Data, aes: AESKey, hmac: HMACKey | send_encrypted_data[s, r, d, aes, hmac] }
}

test expect {
    -- Ratcheting
    verify_ratchet_possible: { can_execute_ratchet } for exactly 3 Node, 6 Key, 4 Message is sat
    
    -- Encrypt-then-MAC 
    verify_encryption_possible: { can_send_encrypted_data } for exactly 3 Node, 6 Key, 4 Message, exactly 1 Data, exactly 1 Ciphertext is sat
}


-- 2. Adversary Capability Tests 

pred eve_can_mitm {
    traces
    eventually { some m: Message, fake_pub: PublicKey | spoof_key_message[m, fake_pub] }
}

pred eve_can_derive_keys {
    traces
    eventually { eve_computes_keys }
}

test expect {
    verify_eve_can_spoof: { eve_can_mitm } for exactly 3 Node, 6 Key, 4 Message is sat
    
    verify_eve_can_derive: { eve_can_derive_keys } for exactly 3 Node, 6 Key, 4 Message is sat
}


-- 3. Security Property Assertions

test expect {
    mitm_is_possible_without_signatures: { 
        find_active_attack 
    } for exactly 3 Node, exactly 12 Key, exactly 4 PrivateKey, exactly 4 PublicKey, exactly 2 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey, exactly 4 Message is sat
    
    passive_eavesdropping_fails: { 
        find_passive_attack 
    } for exactly 3 Node, exactly 12 Key, exactly 4 PrivateKey, exactly 4 PublicKey, exactly 2 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey, exactly 4 Message is unsat
}