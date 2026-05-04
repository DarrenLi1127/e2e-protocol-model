#lang forge


/* =========================================================================
   E2E PROTOCOL ANALYSIS MODEL
   Goal: Analyze the security of an unauthenticated Diffie-Hellman handshake 
   in an E2E protocol (Passive Eavesdropping vs. Active MITM).
   ========================================================================= */

option problem_type temporal
option max_tracelength 7 

option run_sterling "vis.js"

abstract sig Bool {}
one sig True, False extends Bool {}

-- Network participants
abstract sig Node {
    var knows: set Key, -- The knowledge base of the node
    var current_priv: lone PrivateKey, -- The current private key
    var last_other_pub: lone PublicKey, -- The last public key received from the other party
    var needs_ratchet: one Bool  -- Flag to indicate if a key update (ratchet) is needed
}
one sig Alice, Bob, Eve extends Node {}

-- Cryptographic keys
abstract sig Key {}

sig PrivateKey extends Key { owner: one Node }
sig PublicKey extends Key { paired_with: one PrivateKey }
sig SharedSecret extends Key {} 

sig AESKey extends Key {} -- for symmetric encryption              
sig HMACKey extends Key {} -- for message authentication, tagging encrypted messages                 

sig Data {} -- Abstraction of plaintext

-- Encrypted payload
sig Ciphertext {
    content: one Data,
    encrypted_by: one AESKey 
}

-- Network message packet
sig Message {
    sender: one Node,
    receiver: one Node,
    key_payload: lone Key,           -- for handshake messages (PublicKey)           
    cipher_payload: lone Ciphertext, -- for data messages (Ciphertext)      
    mac_tag: lone HMACKey            -- for data integrity (HMACKey)     
}

-- a message is either a key exchange message or a data message, but not both
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
    combine: set PrivateKey -> PublicKey -> SharedSecret, -- Diffie-Hellman algorithm: combine(privA, pubB) = combine(privB, pubA)
    hkdf_aes: set SharedSecret -> AESKey,                 
    hkdf_hmac: set SharedSecret -> HMACKey                
}

pred crypto_properties {
    -- 1-to-1 mapping
    all priv: PrivateKey, pub: PublicKey | one CryptoMath.combine[priv][pub]
    
    -- DH Commutativity g^ab = g^ba
    all privA, privB: PrivateKey, pubA, pubB: PublicKey |
        (pubA.paired_with = privA and pubB.paired_with = privB) implies
            CryptoMath.combine[privA][pubB] = CryptoMath.combine[privB][pubA]
            
    -- HKDF completeness
    all ss: SharedSecret | one CryptoMath.hkdf_aes[ss] and one CryptoMath.hkdf_hmac[ss]
}

-- INITIAL STATE
pred init {
    no Network.msgs -- No messages in transit at the start
    crypto_properties
    
    all n: Node {
        n.knows = {k: PrivateKey | k.owner = n} + PublicKey -- Each node initially knows its own private key and all public keys
        no n.current_priv -- No active private key in use at the start
        no n.last_other_pub 
        n.needs_ratchet = False
    }
}

-- TRANSITIONS (HONEST NODES)

-- Initiate connection
pred send_initial_key[s: Node, r: Node, pub: PublicKey] {
    pub.paired_with in s.knows -- s must know the private key corresponding to the public key it sends
    s.needs_ratchet = False 

    some m: Message | {
        m.sender = s
        m.receiver = r
        m.key_payload = pub
        -- No cipher or MAC in handshake messages
        no m.cipher_payload
        no m.mac_tag
        Network.msgs' = Network.msgs + m  
    }
    current_priv' = current_priv ++ (s -> pub.paired_with) -- Update current private key for s
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
    knows' = knows 
}

-- Receive key, compute shared secret (if possible), and prepare for ratchet
pred receive_and_trigger_ratchet[n: Node, m: Message] {
    m in Network.msgs -- m must be in transit
    m.receiver = n
    one m.key_payload -- must be a handshake message with a public key
    
    let received_pub = m.key_payload | {
        -- check if the received public key is different from the last one
        received_pub != n.last_other_pub implies {
            needs_ratchet' = needs_ratchet ++ (n -> True)
        } else {
            needs_ratchet' = needs_ratchet
        }
        last_other_pub' = last_other_pub ++ (n -> received_pub)
        
        -- if the node has a private key
        (some n.current_priv) implies {
            let priv = n.current_priv |
            let ss = CryptoMath.combine[priv][received_pub] |
            let aes = CryptoMath.hkdf_aes[ss] |
            let hmac = CryptoMath.hkdf_hmac[ss] | {
                knows' = knows + (n -> received_pub) + (n -> ss) + (n -> aes) + (n -> hmac)
            } -- If the node can compute the shared secret, it learns the new public key, shared secret, and derived keys
        } else {
            knows' = knows + (n -> received_pub)
        }
    }
    
    current_priv' = current_priv
    Network.msgs' = Network.msgs - m  
}

-- Execute ratchet and ensure forward secrecy
pred execute_ratchet_and_send[s: Node, r: Node] {
    s.needs_ratchet = True 
    some s.last_other_pub
    
    -- new key pair generation
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
    s.needs_ratchet = False -- at the time of sending data, we assume the ratchet has been executed if needed
    aes in s.knows 
    hmac in s.knows

    some c: Ciphertext, m: Message | {
        c.content = d
        c.encrypted_by = aes  
        
        m.sender = s
        m.receiver = r
        no m.key_payload -- data messages do not carry key payloads
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
    
    m.mac_tag in n.knows -- Must know the correct HMAC key to verify integrity
    m.cipher_payload.encrypted_by in n.knows -- Must know the correct AES key to decrypt
    
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
    -- if there is a key payload, Eve learns it by intercepting the message
    one m.key_payload implies knows' = knows + (Eve -> m.key_payload) else knows' = knows
    -- Eve does not alter the message, so it remains in transit for the honest receiver
    Network.msgs' = Network.msgs 
    current_priv' = current_priv
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
}

-- Active Man-In-The-Middle attack during the handshake
pred spoof_key_message[m: Message, fake_pub: PublicKey] {
    m in Network.msgs
    one m.key_payload
    fake_pub in Eve.knows 
    
    -- Eve replaces the original key message with a fake one containing a public key she controls
    some fake_m: Message | {
        fake_m.sender = m.sender --eve spoofs the sender as the original sender       
        fake_m.receiver = m.receiver -- eve spoofs the receiver as the original receiver
        fake_m.key_payload = fake_pub  -- Eve injects her own public key
        no fake_m.cipher_payload
        no fake_m.mac_tag
        Network.msgs' = (Network.msgs - m) + fake_m -- Eve replaces the original message with the spoofed one
    }
    knows' = knows + (Eve -> m.key_payload)
    current_priv' = current_priv
    last_other_pub' = last_other_pub
    needs_ratchet' = needs_ratchet
}

-- Eve can derives keys from intercepted materials
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

-- If a node is compromised, Eve learns its current private key and any AES keys it knows, but not past shared secrets due to forward secrecy.
pred node_compromised[n: Node] {
    some priv: n.current_priv, aes: n.knows & AESKey | {
        knows' = knows + (Eve -> priv) + (Eve -> aes)
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

-- Define all possible system actions (honest behavior + attacker actions)
pred system_step {
    (some s, r: Node, pub: PublicKey | send_initial_key[s, r, pub]) or
    (some n: Node, m: Message | receive_and_trigger_ratchet[n, m]) or
    (some s, r: Node | execute_ratchet_and_send[s, r]) or
    (some s, r: Node, d: Data, aes: AESKey, hmac: HMACKey | send_encrypted_data[s, r, d, aes, hmac]) or
    (some n: Node, m: Message | receive_encrypted_data[n, m]) or
    (some m: Message | intercept_message[m]) or 
    (some m: Message, fake_pub: PublicKey | spoof_key_message[m, fake_pub]) or
    eve_computes_keys or
    (some n: Node | node_compromised[n]) or
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
    -- no spoofing messages and physical node compromises
    always (no m: Message, pub: PublicKey | spoof_key_message[m, pub])
    always (no n: Node | node_compromised[n])
    
    eventually {
        some k: AESKey | {
            k in Alice.knows
            k in Bob.knows
            k in Eve.knows
            
            -- Eve can not just guess the AES key without the shared secret, so she must have derived it from intercepted materials
            not (some priv: PrivateKey, pub: PublicKey | 
                priv.owner = Eve and 
                CryptoMath.hkdf_aes[CryptoMath.combine[priv][pub]] = k
            )
        }
    }
}

-- Proof 2: Protocol is vulnerable to active MITM attacks without signatures
pred find_active_attack {
    traces
    always (no n: Node | node_compromised[n])
    eventually (some pub: PublicKey | send_initial_key[Alice, Bob, pub]) -- make sure the attack starts with Alice sending a key message to Bob
    eventually (some k: AESKey | k in Eve.knows and k in Bob.knows) -- Eve successfully tricks Bob into using an AES key that Eve knows
}

-- Proof 3: Forward Secrecy ensures past keys are safe if a node is compromised later
pred forward_secrecy_holds {
    traces implies {
        -- make sure there is no spoofing of key messages, so we can focus on the forward secrecy property
        always (no m: Message, pub: PublicKey | spoof_key_message[m, pub]) implies {
            
            always {
                -- For every node s and every AES key k
                all s: Node, k: AESKey | s != Eve implies {
                    
                    -- when key is deleted
                    (k in s.knows and k not in s.knows') implies {
                        
                        -- Eve never learns the deleted key, even if she compromises the node after the deletion
                        always (k not in Eve.knows)
                    }
                }
            }
        }
    }
}
-- Demonstrate Active Attack (Clear visual trace)
// run { find_active_attack } for exactly 3 Node, 9 Key, 4 Message, 1 Data, 1 Ciphertext

-- Verify Passive Safety (Expect UNSAT)
run { find_passive_attack } for exactly 3 Node, 5 Key, 3 Message, 1 Data, 1 Ciphertext

-- Verify Forward Secrecy (Expect UNSAT)
check { forward_secrecy_holds } for exactly 3 Node, 5 Key, 4 Message, 1 Data, 1 Ciphertext