# The Erdős Ternary Conjecture: Formal Statement of the Gap

## 1. The Mathematical Problem

**Conjecture (Erdős, 1979).** For every natural number $r \notin \{0, 2, 8\}$, the binary expansion $2^r$ contains the digit 2 in its ternary (base-3) expansion.

Formally: $\forall r \in \mathbb{N},\; r \ne 0 \wedge r \ne 2 \wedge r \ne 8 \implies \exists p \in \mathbb{N},\; \text{digit}_3(2^r, p) = 2$.

The negation uses the Cantor set: $n$ is in the Cantor set iff every ternary digit of $n$ is 0 or 1. So the conjecture becomes:

$$\forall r \notin \{0,2,8\},\quad \neg\,\text{memCantorNat}(2^r)$$

where $\text{memCantorNat}(n) \iff \forall k,\; \text{digit}_3(n,k) \ne 2$.

---

## 2. Definitions

### 2.1 Ternary digits

$$\text{digit}_3(n, k) = (n / 3^k) \% 3$$

`BridgeCompute.lean:20`, `Lifting.lean:8` (`ternaryDigit` is identical).

### 2.2 Period

$$u_K = 2 \cdot 3^{K-1}$$

This is the multiplicative order of 2 modulo $3^K$. Concretely, $2^{u_K} \equiv 1 \pmod{3^K}$, so $2^r \bmod 3^K$ is periodic in $r$ with period $u_K$.

`BridgeCompute.lean:26`.

### 2.3 Trailing digit-2 test

$$\text{hasTrailingDigit2}(v, K) = \bigvee_{i=0}^{K-1} \bigl[(v / 3^i) \% 3 = 2\bigr]$$

Returns `true` iff $v$ has a digit 2 among its first $K$ ternary digits.

`BridgeCompute.lean:76`.

### 2.4 The survivor set $N_K$

$$N_K = \bigl\{r \in [0, u_K) : \text{hasTrailingDigit2}(2^r \bmod 3^K,\; K) = \text{false}\bigr\}$$

A number $r$ survives at level $K$ if $2^r \bmod 3^K$ has no digit 2 in positions $0, 1, \ldots, K-1$.

`BridgeCompute.lean:88` (`computeNK`), `BridgeCompute.lean:133` (`computeNKFast`, equivalent).

**Key notation:** $r \in N_K$ means $r$ survives the digit-2-free filter at level $K$.

### 2.5 The Cantor set membership

$$\text{memCantorNat}(n) \iff \forall k \in \mathbb{N},\; \text{digit}_3(n, k) \ne 2$$

`Narkiewicz.lean:33`.

**Relationship:** $\text{memCantorNat}(2^r) \implies r \in N_K$ for all $K$ (since if $2^r$ has no digit 2 anywhere, it has none in positions $0$ through $K-1$). The converse is false for any finite $K$.

---

## 3. The Lifting Structure (Proved in Lifting.lean, 0 sorry)

### 3.1 The 2-to-1 lifting theorem

**Theorem (nkf_inductive).** For $K \ge 1$:

$$|N_{K+1}| = 2 \cdot |N_K|$$

`Lifting.lean:449`.

**Theorem (nk_size).** For $K \ge 1$:

$$|N_K| = 2^{K-1}$$

`Lifting.lean:480`.

### 3.2 How the lifting works

The proof of `nkf_inductive` decomposes $[0, u_{K+1})$ into three blocks of length $u_K$:

$$[0, u_{K+1}) = [0, u_K) \;\cup\; [u_K, 2u_K) \;\cup\; [2u_K, 3u_K)$$

since $u_{K+1} = 3 u_K$.

For each $s \in N_K$ and each offset $q \in \{0, 1, 2\}$, the candidate $r = q \cdot u_K + s$ belongs to $[0, u_{K+1})$. The filter test at level $K+1$ splits into:

1. **Trailing digits** (positions $0$ through $K-1$): preserved from level $K$. If $s$ survived at level $K$, all three candidates $q \cdot u_K + s$ survive the trailing test at level $K+1$.

2. **The new digit** (position $K$): this is $\text{kthDigit}(K, s, q)$, the $K$-th ternary digit of $2^{q \cdot u_K + s}$. Since $2^{u_K} \equiv 1 + 3^K \pmod{3^{K+1}}$:

$$\text{kthDigit}(K, s, q) = \text{digit}_3(2^s, K) + q \cdot (2^s \% 3) \pmod{3}$$

**Theorem (exactly_one_digit2).** For each $s$ that survived at level $K$, the three values $\text{kthDigit}(K, s, 0), \text{kthDigit}(K, s, 1), \text{kthDigit}(K, s, 2)$ form an arithmetic progression modulo 3 with common difference $2^s \% 3$, and exactly one of them equals 2.

`Lifting.lean:260`.

**Theorem (exactly_two_lifts).** Therefore exactly two of the three candidates have no digit 2 at position $K$, so:

$$\#\{q \in \{0,1,2\} : q \cdot u_K + s \in N_{K+1}\} = 2$$

for each $s \in N_K$.

`Lifting.lean:322`.

### 3.3 The three permanent survivors

**Theorem.** $r = 0$, $r = 2$, and $r = 8$ belong to every $N_K$ (for $K \ge 1$), and satisfy $\text{memCantorNat}(2^r)$.

- $2^0 = 1$: all ternary digits are 0 or 1. `Lifting.lean:506`.
- $2^2 = 4 = 11_3$: all ternary digits are 0 or 1. `Lifting.lean:512`.
- $2^8 = 256$: all ternary digits are 0 or 1. `Lifting.lean:519`.

The three known permanent survivors are $0, 2, 8$. Proving that there are no other permanent survivors — i.e., $\bigcap_K N_K = \{0, 2, 8\}$ — is equivalent to the Erdős conjecture.

### 3.4 The backward contrapositive

**Contrapositive of the conjecture:**

$$\text{memCantorNat}(2^r) \implies r \in \{0, 2, 8\}$$

This is equivalent to the original conjecture (since $r = 0, 2, 8$ do satisfy $\text{memCantorNat}(2^r)$).

---

## 4. The Finite Bridge Infrastructure (Proved in BridgeCompute/BridgeMiddle/BridgeK*)

For specific values $K \in \{5, 6, \ldots, 18\}$, we have:

**Theorem (bridge_K{K}_not_cantor).** For each $K \in \{13, 14, 15, 16, 17, 18\}$:

$$r \in N_K \wedge r \notin \{0, 2, 8\} \implies \neg\,\text{memCantorNat}(2^r)$$

These are proved via `checkBridgeCantorPow2 K = true`, which verifies by `native_decide` that every $r \in N_K$ with $r \notin \{0,2,8\}$ has a digit 2 in positions $0$ through $49$ of $2^r \bmod 3^{50}$.

`BridgeUniform.lean:140-168`.

For $K \in \{5, \ldots, 12\}$, similar bridges exist using `BridgeCompute` (K=5..9) and `BridgeMiddle` (K=10..12).

**Additional verified result:** For $r < 1001$, $r \notin \{0,2,8\}$, $r \in N_K$ (any $K \ge 5$):

$$\neg\,\text{memCantorNat}(2^r)$$

`BridgeUniform.lean:348` (`bridge_small_n`), proved via `all_nine_to_1000_not_cantor` which uses `native_decide` on explicit lists.

---

## 5. Monotonicity (Proved in BridgeUniform.lean)

**Theorem (NK_mono).** For $K_1 \le K_2$ and $r < u_{K_1}$:

$$r \in N_{K_2} \implies r \in N_{K_1}$$

`BridgeUniform.lean:86`.

**Interpretation:** Membership in $N_K$ is downward-monotone in $K$, provided $r$ stays within the period of the lower level. If $2^r \bmod 3^{K_2}$ has no digit 2 in positions $0, \ldots, K_2-1$, then certainly it has none in positions $0, \ldots, K_1-1$ (since $K_1 \le K_2$).

**Critical hypothesis:** The bound $r < u_{K_1}$ is essential. Without it, the monotonicity does not apply.

---

## 6. The Proof Architecture of `erdos_ternary`

The current (incomplete) proof follows this chain:

```
erdos_ternary (for all r ∉ {0,2,8})
  ↓  (exists_K_ge5: pick K = r+5 so r < uK)
bridge_first_period_all (for all K ≥ 5)
  ↓  (case split on K)
bridge_all_K_digit2
  ↓
┌─ K ≤ 9:    BridgeCompute (native_decide, K=5..9)
├─ K ∈ {10,11,12}: BridgeMiddle
├─ K ∈ {13,14,15,16,17}: bridge_K{K}_not_cantor (native_decide)
├─ K = 18:   bridge_K18_not_cantor (native_decide)
└─ K ≥ 18:   ostrowski_invariant ← THE GAP
```

### 6.1 How `ostrowski_invariant` dispatches

For $K \ge 18$, the proof of `ostrowski_invariant` splits:

| Case | Condition | Mechanism | Status |
|------|-----------|-----------|--------|
| A | $r < u_{18}$ | NK_mono to $K=18$, then bridge_K18 | Valid |
| B | $r < 1001$ | bridge_small_n (finite computation) | Valid |
| C | $r \ge u_{18} \wedge K > 18$ | **Missing argument** | **BROKEN** |

Case C attempts to use `absurd` with `NK_mono` requiring $r < u_{18}$, but the context contains $r \ge u_{18}$. The `omega` tactic cannot prove $r < u_{18}$ from $r \ge u_{18}$. This is a genuine type error: the subterm `NK_mono h18le' (by omega) hr` does not type-check.

---

## 7. The Precise Mathematical Gap

### 7.1 Statement of the missing lemma

**Definition (the gap).** We need:

$$\boxed{\texttt{Global Bridge:}\quad \forall K > 18,\; \forall r \in N_K,\; r \notin \{0,2,8\} \implies \neg\,\text{memCantorNat}(2^r)}$$

under the sole assumption that such $K$ and $r$ exist (i.e., $r \in [0, u_K)$).

Note: this is the statement with the **weakest possible** hypotheses. We do NOT need $r < u_{18}$; we do NOT need $r < 1001$. We need it for all $r \in N_K$ with $K > 18$.

### 7.2 Why NK_mono cannot close this

NK_mono gives: $r \in N_K \wedge r < u_{K_1} \implies r \in N_{K_1}$.

To reduce from $K > 18$ to $K_1 = 18$, we need $r < u_{18} = 2 \cdot 3^{17} = 258{,}280{,}326$.

For $r \ge u_{18}$, this path is blocked. We cannot use any existing bridge $K_1 \le 18$ because they all require $r < u_{K_1} \le u_{18}$.

### 7.3 What the infinite staircase objection means

If we tried to close the gap by adding a bridge at $K = 19$:

- For $r < u_{19}$: the $K=19$ bridge handles it.
- For $r \ge u_{19}$: we need a $K=20$ bridge.
- For $r \ge u_{20}$: we need a $K=21$ bridge.
- ...

This creates an infinite descent that never terminates. **Every finite bridge introduces a new unbounded case.**

The gap is not a matter of computational capacity. It requires a qualitative argument that works for all $K > 18$ simultaneously.

---

## 8. What We Know About the Survivor Tree

### 8.1 The binary tree structure

At each level $K \to K+1$, each survivor $s \in N_K$ produces exactly 2 children in $N_{K+1}$. The children are $\{q_1 \cdot u_K + s, \; q_2 \cdot u_K + s\}$ where $q_1, q_2 \in \{0, 1, 2\}$ are the two offsets whose $K$-th digit is not 2.

This defines a complete binary tree of depth $K - K_0$ rooted at $N_{K_0}$.

### 8.2 Which branches survive to infinity

The three known infinite survivors $\{0, 2, 8\}$ persist at every level. Their ternary expansions are:

- $r = 0$: $2^0 = 1 = 1_3$, digits $\{0, 1\}$ only.
- $r = 2$: $2^2 = 4 = 11_3$, digits $\{0, 1\}$ only.
- $r = 8$: $2^8 = 256 = 100111_3$... wait, $256 = 1 \cdot 243 + 0 \cdot 81 + 0 \cdot 27 + 1 \cdot 9 + 1 \cdot 3 + 1 = 100111_3$, digits $\{0, 1\}$ only.

### 8.3 What the gap requires

We need to show that no other branch survives to infinity. Equivalently:

**For every $r \notin \{0, 2, 8\}$, there exists some finite $K$ such that $r \notin N_K$.**

This is equivalent to the original conjecture by the contrapositive.

---

## 9. Available Lemmas and Their Hypotheses

### 9.1 Lifting infrastructure (all proved, 0 sorry)

| Lemma | Hypotheses | Conclusion | File:Line |
|-------|-----------|------------|-----------|
| `pow2_uK_mod` | $K \ge 1$ | $2^{u_K} \bmod 3^{K+1} = 1 + 3^K$ | Lifting.lean:47 |
| `kthDigit_step` | $K \ge 1$, $r < u_K$ | $\text{kthDigit}(K, r, 1) = (\text{kthDigit}(K, r, 0) + 2^r\%3) \% 3$ | Lifting.lean:150 |
| `kthDigit_step_2` | $K \ge 1$, $r < u_K$ | $\text{kthDigit}(K, r, 2) = (\text{kthDigit}(K, r, 0) + 2 \cdot (2^r\%3)) \% 3$ | Lifting.lean:175 |
| `digits_arithmetic_progression` | $K \ge 1$, $r < u_K$ | Both step relations simultaneously | Lifting.lean:201 |
| `exactly_one_digit2` | $K \ge 1$, $r < u_K$, trailing-free at $K$ | Exactly one of the three $K$-th digits equals 2 | Lifting.lean:260 |
| `exactly_two_lifts` | $K \ge 1$, $r < u_K$, trailing-free at $K$ | Exactly 2 of 3 candidates survive to $K+1$ | Lifting.lean:322 |
| `trail_ext_general` | $K \ge 1$ | Trailing digits at positions $0..K-1$ are preserved under $r \to q \cdot u_K + r$ | Lifting.lean:382 |
| `nkf_fiber` | $K \ge 1$, $s < u_K$ | Fiber count = 2 if $s \in N_K$, else 0 | Lifting.lean:409 |
| `nkf_inductive` | $K \ge 1$ | $|N_{K+1}| = 2|N_K|$ | Lifting.lean:449 |
| `nk_size` | $K \ge 1$ | $|N_K| = 2^{K-1}$ | Lifting.lean:480 |

### 9.2 Bridge results (proved via native_decide)

| Lemma | Hypotheses | Conclusion | File:Line |
|-------|-----------|------------|-----------|
| `bridge_K{K}_not_cantor` | $r \in N_K$, $r \notin \{0,2,8\}$ | $\neg\text{memCantorNat}(2^r)$ | BridgeUniform.lean:140-168 |
| `bridge_small_n` | $K \ge 5$, $r \in N_K$, $r \notin \{0,2,8\}$, $r < 1001$ | $\neg\text{memCantorNat}(2^r)$ | BridgeUniform.lean:348 |
| `NK_mono` | $K_1 \le K_2$, $r < u_{K_1}$ | $r \in N_{K_2} \implies r \in N_{K_1}$ | BridgeUniform.lean:86 |

### 9.3 Characterization results (proved in Lifting.lean)

| Lemma | Hypotheses | Conclusion | File:Line |
|-------|-----------|------------|-----------|
| `two_pow_zero_no_digit2` | none | $\forall p,\; \text{digit}_3(1, p) \ne 2$ | Lifting.lean:506 |
| `two_pow_two_no_digit2` | none | $\forall p,\; \text{digit}_3(4, p) \ne 2$ | Lifting.lean:512 |
| `two_pow_eight_no_digit2` | none | $\forall p,\; \text{digit}_3(256, p) \ne 2$ | Lifting.lean:519 |

---

## 10. Precise Statement of the Research Target

### 10.1 The lemma that would close the gap

**Theorem A (Global Non-Persistence).** For all $K \ge 5$ and all $r \in N_K$ with $r \notin \{0, 2, 8\}$:

$$\neg\,\text{memCantorNat}(2^r)$$

This does NOT require $r < u_{18}$, does NOT require $r < 1001$, and does NOT require any bound on $r$ relative to $u_K$.

### 10.2 Equivalently

**Theorem A'.** The set $\bigcap_{K \ge 1} N_K = \{0, 2, 8\}$.

### 10.3 What Theorem A implies

If Theorem A is proved, then:
- `ostrowski_invariant` becomes: immediate from Theorem A.
- `bridge_first_period_all` becomes: immediate from Theorem A.
- `erdos_ternary` becomes: immediate from Theorem A + `exists_K_ge5`.

### 10.4 Potential attack directions

**Direction 1: Carry-packet analysis.** The digits of $2^r$ at position $K$ are determined by carries from lower positions. If one can show that for $r \notin \{0,2,8\}$, the carry pattern eventually forces a digit 2, the conjecture follows.

**Direction 2: p-adic orbit structure.** The sequence $2^r \bmod 3^K$ as a function of $r$ follows a $p$-adic orbit. Characterizing which orbits avoid digit 2 entirely may show only three do.

**Direction 3: Density / growth argument.** Since $|N_K| = 2^{K-1}$ but $u_K = 2 \cdot 3^{K-1}$, the density of $N_K$ in $[0, u_K)$ is $(2/3)^{K-1} \to 0$. A survivor at level $K$ must satisfy increasingly restrictive conditions. Proving these conditions cannot all be satisfied simultaneously for $r \notin \{0,2,8\}$ would close the gap.

**Direction 4: Transfer to a dynamical system.** The map $r \mapsto (q, s)$ where $r = q \cdot u_K + s$ defines a dynamical system on the survivor tree. Proving this system has no periodic orbits other than those corresponding to $\{0, 2, 8\}$ would suffice.

---

## 11. Current Status Summary

| Component | Status | Location |
|-----------|--------|----------|
| Ternary digit extraction | Proved (0 sorry) | BridgeCompute.lean |
| Period $u_K = 2 \cdot 3^{K-1}$ | Definition | BridgeCompute.lean:26 |
| $N_K$ definition | Proved (0 sorry) | BridgeCompute.lean:88 |
| $2^{u_K} \bmod 3^{K+1} = 1 + 3^K$ | Proved (0 sorry) | Lifting.lean:47 |
| Exactly-one-digit-2 mechanism | Proved (0 sorry) | Lifting.lean:260 |
| Exactly-two surviving lifts | Proved (0 sorry) | Lifting.lean:322 |
| $|N_K| = 2^{K-1}$ | Proved (0 sorry) | Lifting.lean:480 |
| NK monotonicity (with bound) | Proved (0 sorry) | BridgeUniform.lean:86 |
| Finite bridges $K = 5, \ldots, 18$ | Proved (native_decide) | BridgeCompute/BridgeK* |
| $r < 1001$ bridge | Proved (native_decide) | BridgeUniform.lean:348 |
| $r = 0, 2, 8$ are permanent | Proved (0 sorry) | Lifting.lean:506-523 |
| **Global non-persistence** | **NOT PROVED** | **THE GAP** |
| `ostrowski_invariant` (third branch) | **INVALID** (type error) | BridgeUniform.lean:189-193 |

**Bottom line:** The entire finite machinery is solid. The gap is precisely the passage from finite verification to the infinite statement. This is the known difficulty of the Erdős problem.
