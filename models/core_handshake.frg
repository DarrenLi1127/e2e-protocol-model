#lang forge

-- Static Entities

abstract sig Node {
    -- 这是一个动态关系：每个节点当前拥有的知识库 (Keys)
    -- var 关键字表示它在不同的时间步会发生变化
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
var sig Network in Message {}


-- Initial State)
pred init {
    no Network
    
    -- each node knows its own private key and all public keys
    all n: Node {
        n.knows = {k: PrivateKey | k.owner = n} + PublicKey
    }
}

-- Transitions / Actions

pred send_message[s: Node, r: Node, k: Key] {
    k in s.knows
    
    -- create a new message m with sender s, receiver r, and payload k, and add it to the network
    some m: Message | {
        m.sender = s
        m.receiver = r
        m.payload = k
        Network' = Network + m 
    }
    
    knows' = knows 
}

pred receive_message[r: Node, m: Message] {
    m in Network
    m.receiver = r
    
    knows' = knows + (r -> m.payload)
    Network' = Network - m
}

-- attempt to intercept a message in transit (Eve's action)
pred intercept_message[m: Message] {
    -- m ust be in the network for Eve to intercept it
    m in Network
    
    knows' = knows + (Eve -> m.payload)
    Network' = Network
}

-- 动作 4：无事发生 (Stutter step)
-- 在 Temporal Logic 中，必须允许系统保持不变，防止死锁
pred do_nothing {
    Network' = Network
    knows' = knows
}

-- ==========================================
-- 系统演进规则 (System Evolution)
-- ==========================================
pred transition {
    -- 在任何一个时间步，以下动作中有且仅有一个发生
    (some s, r: Node, k: Key | send_message[s, r, k]) or
    (some r: Node, m: Message | receive_message[r, m]) or
    (some m: Message | intercept_message[m]) or
    do_nothing
}

-- 定义整个系统的运行轨迹 (Trace)
pred traces {
    init
    always transition
}

run {
    traces
} for exactly 3 Node, exactly 3 PrivateKey, exactly 3 PublicKey, 4 Message