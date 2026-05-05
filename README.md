# README: E2E Protocol Analysis Model

## 1. Project Goals & Modeling Choices
**Goal:** Our primary goal is to verify the security of an unauthenticated Diffie-Hellman handshake in an E2E protocol system. We analyze vulnerabilities to Passive Eavesdropping and Active Man-in-the-Middle (MITM) attacks when digital signatures are not applied.

**The Three Buckets:**
* **Core:** The temporal state machine for Diffie-Hellman, key ratcheting logic, and network message transitions (send/receive).
* **Closely Related:** Dolev-Yao adversary capabilities, including message interception, spoofing, and the derivation of keys from intercepted material.
* **Unrelated:** Network routing, detailed implementations of HKDF, and long-term key storage.

## 2. Design Tradeoffs & Assumptions
* **Representation:** We abstract cryptographic keys (e.g., `PrivateKey`, `PublicKey`) to keep the SAT solver efficient. We used `lone` and `set` relations to represent a node's knowledge base, and it allowed us to model how nodes interact with each other over time.
* **Assumptions:** We assume a Dolev-Yao network model where the attacker (Eve) can intercept or spoof messages. We limited the `max_tracelength` to 7 to prevent state-space explosion while still allowing enough steps for a full handshake and a ratchet update.
* **Limits:** While our model successfully proves that the system is resilient against passive eavesdropping and guarantees forward secrecy, it is intentionally limited to a Diffie-Hellman handshake without authentication. Consequently, it does not currently model timestamps or replay protection. Our primary focus remained on demonstrating the inherent MITM vulnerability within the transition logic before implementing higher-level security.

## 3. How the Model Works & Execution
* **Running the model:** 
    1. `racket models/core_handshake.frg` for model
    1. `racket tests/handshake_tests.frg` for testing
    2. Paste code from `visualizer/vis.js` into sterling script `svg` option for visualization.

## 4. Insights & Outcomes
A major lesson we learned was the importance of scope management. Initially, we kept getting trivial UNSAT errors and it was frustrating until we realized our `PrivateKey` count was too low. Because our `execute_ratchet_and_send` logic creates brand-new keys to ensure forward secrecy, the solver ran out of atoms to use. We fixed this by providing a larger "pool" of keys (e.g., `exactly 12 Key`), giving the model enough room to work.


**Future Plan:** Our next goal is to implement digital signatures for authentication. By adding a `sig_payload` and enforcing signature checks in the transition logic, we plan to prevent our system from MITM attacks.

## 5. Collaborators & AI Use
**Collaborators:** 
* Haoyang Li
* Yifan Sun

**AI Use Disclosure:**
We used AI (ChatGPT/Gemini) to brainstorm the initial framework for the model. AI was also used to debug complex "Solving" timeouts by suggesting more specific scope constraints and to provide a basic template for our custom visualizer.