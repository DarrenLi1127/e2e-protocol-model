#lang forge

open "../models/core_handshake.frg"

/* =========================================================================
   STATIC UNIT TESTS
   Ensure the basic static properties of the cryptography and initial 
   state are logically satisfiable.
   ========================================================================= */
test expect {
    crypto_math_is_satisfiable: { 
        crypto_properties 
    } for exactly 3 Node, exactly 3 PrivateKey, exactly 3 PublicKey, exactly 1 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey is sat
    
    initial_state_is_satisfiable: { 
        init 
    } for exactly 3 Node, exactly 3 PrivateKey, exactly 3 PublicKey, exactly 1 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey is sat
}


/* =========================================================================
   [PHASE 1] THE HAPPY PATH (LIVENESS & NORMAL EXECUTION)
   -------------------------------------------------------------------------
   We must prove that the protocol actually works when there is no active 
   attacker (no spoofing). In a "normal" scenario, Alice and Bob should 
   be able to complete a handshake, derive keys, and exchange encrypted data.
   ========================================================================= */

-- Verify that Ratchet updates are possible
pred can_execute_ratchet {
    traces
    eventually { some s, r: Node | execute_ratchet_and_send[s, r] }
}

-- Verify that End-to-End Encrypted Communication is possible without MITM
pred normal_communication_works_without_mitm {
    traces
    -- Constraint: Eve is strictly passive here. No spoofing allowed.
    always (no m: Message, pub: PublicKey | spoof_key_message[m, pub])
    
    -- Goal: A complete cycle of encrypted data transmission succeeds
    eventually {
        some m: Message, d: Data | {
            m.sender = Alice
            m.receiver = Bob
            receive_encrypted_data[Bob, m]
            m.cipher_payload.content = d
        }
    }
}

test expect {
    verify_ratchet_is_possible: { can_execute_ratchet } for exactly 3 Node, 6 Key, 4 Message is sat
    verify_end_to_end_communication: { normal_communication_works_without_mitm } for exactly 3 Node, exactly 12 Key, exactly 4 PrivateKey, exactly 4 PublicKey, exactly 2 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey, exactly 4 Message is sat
}


/* =========================================================================
   [PHASE 2] PASSIVE ATTACKER (EAVESDROPPING)
   -------------------------------------------------------------------------
   Demonstrate that the protocol is SECURE against a passive attacker.
   If Eve only eavesdrops (intercepts messages without altering them), 
   she cannot derive the symmetric keys used by Alice and Bob.
   ========================================================================= */
test expect {
    -- We expect this to be UNSAT: Eve cannot find the AES key just by listening.
    passive_eavesdropping_fails_to_break_encryption: { 
        find_passive_attack 
    } for exactly 3 Node, exactly 12 Key, exactly 4 PrivateKey, exactly 4 PublicKey, exactly 2 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey, exactly 4 Message is unsat
}


/* =========================================================================
   [PHASE 3] ACTIVE ATTACKER (MAN-IN-THE-MIDDLE)
   -------------------------------------------------------------------------
   *VULNERABILITY DEMONSTRATION*
   Because our base Diffie-Hellman handshake lacks Digital Signatures 
   (authentication), an active attacker can spoof key messages.
   This proves that Eve CAN successfully perform a MITM attack and trick 
   Bob into using an AES key that Eve knows.
   ========================================================================= */

-- Ensure Eve actually has the capability to intercept and derive keys
pred eve_capabilities {
    traces
    eventually { some m: Message, fake_pub: PublicKey | spoof_key_message[m, fake_pub] }
    eventually { eve_computes_keys }
}

test expect {
    verify_eve_has_mitm_capabilities: { eve_capabilities } for exactly 3 Node, 6 Key, 4 Message is sat

    -- We expect this to be SAT: Eve successfully executes the MITM attack.
    active_mitm_attack_is_successful_without_signatures: { 
        find_active_attack 
    } for exactly 3 Node, exactly 12 Key, exactly 4 PrivateKey, exactly 4 PublicKey, exactly 2 SharedSecret, exactly 1 AESKey, exactly 1 HMACKey, exactly 4 Message is sat
}


/* =========================================================================
   [PHASE 4] FORWARD SECRECY (POST-COMPROMISE SECURITY)
   -------------------------------------------------------------------------
   Even though the protocol is vulnerable to MITM during the initial 
   handshake, its ratcheting mechanism provides Forward Secrecy.
   If a node is compromised (private key stolen) AFTER a ratchet update, 
   past shared secrets remain safe from the attacker.
   ========================================================================= */
test expect {
    forward_secrecy_protects_past_keys: {
        forward_secrecy_holds
    } is checked
}