#lang forge

option problem_type temporal

-- Static Entities

abstract sig Node {
    var knows: set Key
}
one sig Alice, Bob, Eve extends Node {}

abstract sig Key {}

sig PrivateKey extends Key {
    owner: one Node
}

sig PublicKey extends Key {
    paired_with: one PrivateKey
}

sig Message {
    sender: one Node,
    receiver: one Node,
    payload: one Key 
}

-- Temporal State)
one sig Network {
    var msgs: set Message
}

sig SharedSecret extends Key {}

-- 用关系逻辑抽象密码学运算
one sig CryptoMath {
    combine: set PrivateKey -> PublicKey -> SharedSecret
}

-- 定义 DH 密钥交换的核心数学属性
pred dh_properties {
    -- 1. 函数约束：每一对合法的公私钥组合，必定对应唯一一个 (exactly one) 共享密钥
    all priv: PrivateKey, pub: PublicKey |
        one CryptoMath.combine[priv][pub]
        
    -- 2. 强制满足交换律：combine(PrivA, PubB) == combine(PrivB, PubA)
    all privA, privB: PrivateKey, pubA, pubB: PublicKey |
        (pubA.paired_with = privA and pubB.paired_with = privB) implies
            CryptoMath.combine[privA][pubB] = CryptoMath.combine[privB][pubA]
}


-- Initial State
pred init {
    no Network.msgs 
    dh_properties
    
    all n: Node {
        n.knows = {k: PrivateKey | k.owner = n} + PublicKey
    }
}

-- Transitions / Actions
pred send_message[s: Node, r: Node, k: Key] {
    k in s.knows
    
    some m: Message | {
        m.sender = s
        m.receiver = r
        m.payload = k
        Network.msgs' = Network.msgs + m  
    }
    knows' = knows 
}

pred receive_message[r: Node, m: Message] {
    m in Network.msgs 
    m.receiver = r
    
    knows' = knows + (r -> m.payload)
    Network.msgs' = Network.msgs - m  
}

pred intercept_message[m: Message] {
    m in Network.msgs 
    
    knows' = knows + (Eve -> m.payload)
    Network.msgs' = Network.msgs 
}

pred derive_secret[n: Node, priv: PrivateKey, pub: PublicKey] {
    priv in n.knows
    pub in n.knows
    
    let ss = CryptoMath.combine[priv][pub] | {
        knows' = knows + (n -> ss)
    }
    Network.msgs' = Network.msgs  
}

pred do_nothing {
    Network.msgs' = Network.msgs  
    knows' = knows
}

-- System Evolution
pred system_step {
    -- 在任何一个时间步，以下动作中有且仅有一个发生
    (some s, r: Node, k: Key | send_message[s, r, k]) or
    (some r: Node, m: Message | receive_message[r, m]) or
    (some m: Message | intercept_message[m]) or
    (some n: Node, priv: PrivateKey, pub: PublicKey | derive_secret[n, priv, pub]) or 
    do_nothing
}
-- Trace
pred traces {
    init
    always system_step
}

run {
    traces
} for exactly 3 Node, exactly 3 PrivateKey, exactly 3 PublicKey, 4 Message