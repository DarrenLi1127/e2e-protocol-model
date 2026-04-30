#lang forge


option problem_type temporal
option max_tracelength 7 


abstract sig Bool {}
one sig True, False extends Bool {}

-- Network participants
abstract sig Node {
    var knows: set Key,
    var current_priv: lone PrivateKey, 
    var last_other_pub: lone PublicKey,
    var needs_ratchet: one Bool 
}
one sig Alice, Bob, Eve extends Node {}

-- Cryptographic keys
abstract sig Key {}

sig PrivateKey extends Key { owner: one Node }
sig PublicKey extends Key { paired_with: one PrivateKey }
sig SharedSecret extends Key {} 

sig AESKey extends Key {}                  
sig HMACKey extends Key {}                 

sig Data {} 

-- Encrypted payload
sig Ciphertext {
    content: one Data,
    encrypted_by: one AESKey 
}

-- Network message packet
sig Message {
    sender: one Node,
    receiver: one Node,
    key_payload: lone Key,                 
    cipher_payload: lone Ciphertext,       
    mac_tag: lone HMACKey                  
}

-- Ensure messages are well-formed (either handshake or data, never both)
pred well_formed_messages {
    all m: Message | 
        (one m.key_payload and no m.cipher_payload and no m.mac_tag) or 
        (no m.key_payload and one m.cipher_payload and one m.mac_tag)
}

one sig Network {
    var msgs: set Message
}

-- CRYPTOGRAPHIC MATH ABSTRACTIONS

one sig CryptoMath {
    combine: set PrivateKey -> PublicKey -> SharedSecret, 
    hkdf_aes: set SharedSecret -> AESKey,                 
    hkdf_hmac: set SharedSecret -> HMACKey                
}

pred crypto_properties {
    -- 1-to-1 mapping
    all priv: PrivateKey, pub: PublicKey | one CryptoMath.combine[priv][pub]
    
    -- DH Commutativity
    all privA, privB: PrivateKey, pubA, pubB: PublicKey |
        (pubA.paired_with = privA and pubB.paired_with = privB) implies
            CryptoMath.combine[privA][pubB] = CryptoMath.combine[privB][pubA]
            
    -- HKDF completeness
    all ss: SharedSecret | one CryptoMath.hkdf_aes[ss] and one CryptoMath.hkdf_hmac[ss]
}


-- INITIAL STATE

pred init {
    no Network.msgs 
    crypto_properties
    
    all n: Node {
        n.knows = {k: PrivateKey | k.owner = n} + PublicKey
        no n.current_priv
        no n.last_other_pub
        n.needs_ratchet = False
    }
}


-- TRANSITIONS (HONEST NODES)

-- Initiate connection
pred send_initial_key[s: Node, r: Node, pub: PublicKey] {
    pub.paired_with in s.knows
    s.needs_ratchet = False 

    some m: Message | {
        m.sender = s
        m.receiver = r
        m.key_payload = pub
        no m.cipher_payload
        no m.mac_tag
        Network.msgs' = Network.msgs + m  
    }
    current_priv' = current_priv ++ (s -> pub.paired_with)
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
    knows' = knows 
}

-- Receive key and prepare for ratchet
pred receive_and_trigger_ratchet[n: Node, m: Message] {
    m in Network.msgs 
    m.receiver = n
    one m.key_payload 
    
    let received_pub = m.key_payload | {
        received_pub != n.last_other_pub => {
            needs_ratchet' = needs_ratchet ++ (n -> True)
        } else {
            needs_ratchet' = needs_ratchet
        }
        last_other_pub' = last_other_pub ++ (n -> received_pub)
    }
    
    current_priv' = current_priv
    knows' = knows + (n -> m.key_payload)
    Network.msgs' = Network.msgs - m  
}

-- Execute ratchet and ensure forward secrecy
pred execute_ratchet_and_send[s: Node, r: Node] {
    s.needs_ratchet = True 
    some s.last_other_pub
    
    some new_priv: PrivateKey, new_pub: PublicKey, m: Message | {
        new_priv.owner = s
        new_pub.paired_with = new_priv
        
        current_priv' = current_priv ++ (s -> new_priv)
        needs_ratchet' = needs_ratchet ++ (s -> False)
        last_other_pub' = last_other_pub
        
        let new_ss = CryptoMath.combine[new_priv][s.last_other_pub] |
        let new_aes = CryptoMath.hkdf_aes[new_ss] |
        let new_hmac = CryptoMath.hkdf_hmac[new_ss] | {
            -- Forward Secrecy: Erase old state
            knows' = knows - (s -> SharedSecret) - (s -> AESKey) - (s -> HMACKey) 
                           + (s -> new_ss) + (s -> new_aes) + (s -> new_hmac) + (s -> new_priv) + (s -> new_pub)
        }
        
        m.sender = s
        m.receiver = r
        m.key_payload = new_pub
        no m.cipher_payload
        no m.mac_tag
        Network.msgs' = Network.msgs + m
    }
}

-- Send data using Encrypt-then-MAC
pred send_encrypted_data[s: Node, r: Node, d: Data, aes: AESKey, hmac: HMACKey] {
    s.needs_ratchet = False 
    aes in s.knows      
    hmac in s.knows

    some c: Ciphertext, m: Message | {
        c.content = d
        c.encrypted_by = aes  
        
        m.sender = s
        m.receiver = r
        no m.key_payload
        m.cipher_payload = c
        m.mac_tag = hmac      
        Network.msgs' = Network.msgs + m  
    }
    
    current_priv' = current_priv
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
    knows' = knows
}

-- Receive data: Verify HMAC first, then decrypt
pred receive_encrypted_data[n: Node, m: Message] {
    m in Network.msgs
    m.receiver = n
    one m.cipher_payload
    
    m.mac_tag in n.knows 
    m.cipher_payload.encrypted_by in n.knows
    
    Network.msgs' = Network.msgs - m
    
    current_priv' = current_priv
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
    knows' = knows
}

-- TRANSITIONS (ATTACKER - EVE)

-- Passive eavesdropping
pred intercept_message[m: Message] {
    m in Network.msgs 
    one m.key_payload implies knows' = knows + (Eve -> m.key_payload) else knows' = knows
    Network.msgs' = Network.msgs 
    current_priv' = current_priv
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
}

-- Active Man-In-The-Middle attack
pred spoof_key_message[m: Message, fake_pub: PublicKey] {
    m in Network.msgs
    one m.key_payload
    fake_pub in Eve.knows 
    
    some fake_m: Message | {
        fake_m.sender = m.sender       
        fake_m.receiver = m.receiver
        fake_m.key_payload = fake_pub  
        no fake_m.cipher_payload
        no fake_m.mac_tag
        Network.msgs' = (Network.msgs - m) + fake_m
    }
    knows' = knows + (Eve -> m.key_payload)
    current_priv' = current_priv
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
}

-- Eve derives keys from intercepted materials
pred eve_computes_keys {
    some priv: PrivateKey, pub: PublicKey | {
        priv in Eve.knows
        pub in Eve.knows
        let ss = CryptoMath.combine[priv][pub] |
        let aes = CryptoMath.hkdf_aes[ss] |
        let hmac = CryptoMath.hkdf_hmac[ss] | {
            aes not in Eve.knows
            knows' = knows + (Eve -> ss) + (Eve -> aes) + (Eve -> hmac)
        }
    }
    Network.msgs' = Network.msgs
    current_priv' = current_priv
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
}

-- Allow time to pass
pred do_nothing {
    Network.msgs' = Network.msgs  
    knows' = knows
    current_priv' = current_priv
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
}


-- SYSTEM EVOLUTION & SECURITY PROOFS

pred system_step {
    (some s, r: Node, pub: PublicKey | send_initial_key[s, r, pub]) or
    (some n: Node, m: Message | receive_and_trigger_ratchet[n, m]) or
    (some s, r: Node | execute_ratchet_and_send[s, r]) or
    (some s, r: Node, d: Data, aes: AESKey, hmac: HMACKey | send_encrypted_data[s, r, d, aes, hmac]) or
    (some n: Node, m: Message | receive_encrypted_data[n, m]) or
    (some m: Message | intercept_message[m]) or 
    (some m: Message, fake_pub: PublicKey | spoof_key_message[m, fake_pub]) or
    eve_computes_keys or
    do_nothing
}

pred traces {
    init
    always well_formed_messages
    always system_step
}

-- Proof 1: Protocol is safe against passive eavesdroppers
pred find_passive_attack {
    traces
    always (no m: Message, pub: PublicKey | spoof_key_message[m, pub])
    eventually (some k: AESKey | k in Eve.knows)
}

-- Proof 2: Protocol is vulnerable to active MITM attacks without signatures
pred find_active_attack {
    traces
    -- Force a real conversation to happen
    eventually (some pub: PublicKey | send_initial_key[Alice, Bob, pub])
    -- Eve must steal a key that Bob actually uses
    eventually (some k: AESKey | k in Eve.knows and k in Bob.knows)
}

run { 
    find_active_attack 
} for exactly 3 Node, 9 Key, 4 Message, 1 Data, 1 Ciphertext