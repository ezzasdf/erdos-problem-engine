# Mass-1 Birth/Death Process Under Saye Recursion — Census & Verdict

**Date:** 2026-08-25 (Route 1, Phase A)
**Script:** `verify_middle/ostrowski_birthdeath_census.py` (+ depth probes j≤300)

---

## Setup

Classes of `r ∈ N_K` by Ostrowski mass `m(r) = Σ_{k≥5} b_k(r)`:

| class | definition | where it lives |
|---|---|---|
| SP | `r ∈ {0,2,8}` | every level (always exactly 3) |
| Z  | `m=0`, not special (`r ≤ 18`) | only K = 3, 4 |
| O  | `m=1` (`r = q_j+ℓ`, j≥5, ℓ≤18) | K = 4..11 only |
| T  | `m ≥ 2` | K = 4..∞ |

Edges: child `r' = p + i·u_K`, `i ∈ {0(self), 1(shift1), 2(shift2)}`; Saye's
lemma kills exactly one branch per parent via
`d_{K+1}(2^p) + i·d₁(p) ≢ 2 (mod 3)`.

## Complete census results (K = 1..16, exhaustive)

O-population per level: 0,0,0,3,8,6,8,6,5,3,1,**0**,0,0,0,0.
All **8 births** and **11 deaths** ever observed:

```
BIRTHS (child <- parent @edge, entering level K):
  K=4:  20<-2@1(SP)   24<-6@1(Z)    26<-8@1(SP)
  K=5:  96<-42@1(T)   72<-18@1(Z)
  K=7:  486<-0@1(SP)  488<-2@1(SP)  494<-8@1(SP)

DEATHS (self-child fails entering K+1; childrenMasses):
  K=6:  96[3,5] 78[5,3]        K=7: 74[3,2]
  K=8:  20[7,6] 486[6,7]       K=9: 494[13,7]
  K=10: 80[14,6] 488[10,21]    K=11: 24[22,10] 26[23,10]
  K=12: 72[23,12]              <-- last O node ever
```

Every edge label in every birth is **i = 1**; no i=2 birth ever occurred.

---

## Precise lemma statements with evidence status

**Lemma A (Form characterization) — PROVABLE (pure greedy algebra).**
For `j ≥ 5`, `0 ≤ ℓ ≤ 18`: the canonical Ostrowski representation of
`q_j + ℓ` has `b_j = 1` and `b_k = 0` for all `k ≥ 5, k ≠ j`. Conversely
`Σ_{k≥5} b_k(r) = 1` iff `r = q_j + ℓ` uniquely.
*Proof sketch:* `q_{j+1} = a_{j+1}q_j + q_{j-1} > q_j + 18` for j≥5
(checked: needs `(a_{j+1}-1)q_j ≤ 18 - q_{j-1}`, impossible since either
a_{j+1}≥2 gives LHS ≥ q_j = 19 > 18, or a_{j+1}=1 forces q_{j-1} ≥ 19 > 18
for j≥6, and j=5 has a_6=3). Greedy top index is therefore exactly j.

**Lemma B (exact-2 branching) — already formalizable from SayeLemma.**

**Rule R2′ (shifted-child rule) — TRUE for all transitions K→K+1, K ≥ 5.**
Every shifted child (i∈{1,2}) of an O node lands in T. Verified on all 48
shifted edges out of O nodes across transitions 5→6 .. 15→16 (zero
exceptions; minimum child mass seen: 2).
*Exceptions confined to transition 4→5, exactly three:*
`20→74, 24→78, 26→80` (the only O→O shifted edges in existence).

**Rule R3′ (birth-source rule) — TRUE for all transitions entering K ≥ 7.**
Every birth into O has parent ∈ {0,2,8} with edge i=1. Verified: the only
three such births are `486←0, 488←2, 494←8`.
*Exceptions confined to entering K ≤ 5, fully enumerated above*
(includes Z-parents 6, 18 and a T-parent 42 — so parent class alone does
NOT determine child class in general).

**Consequence (conditional theorem):**
`(R2′ ∧ R3′ hold at every level ≥ 5) ⟹ S_K = ∅ for all K ≥ 12`,
since the last birth enters at K=7 and the last death occurs entering K=12.
Both hypotheses are per-level checkable statements — strictly better
decomposed than the current monolithic `ostrowski_invariant` axiom.

---

## Why this does NOT yield a closed finite-state transition system

1. **Non-locality.** Births depend on whether `q_j + ℓ ∈ N_{K+1}` for
   unbounded j — global Diophantine data, not a finite state carried along
   edges. The early census proves locality fails: Z- and T-parents produced
   O-children at entering-K ≤ 5.

2. **The closure hypothesis R3′-forever is pseudo-random.** An accidental
   future birth = a range-restricted survivor `q_j+ℓ` with survival depth
   D ≥ reach K_r. Probed exhaustively j = 9..300 (**5,620 forms**): ZERO.
   Accident-rate heuristic (P(B_M) ≈ (1/2)(2/3)^{M-1}, correlated over the
   19 ℓ-values): **≈ 0.26 expected accidental survivors in the entire tail
   j ≥ 9** (naive independence bound: 1.66). Observing zero is consistent;
   but no finite-state or periodicity argument can certify the tail — the CF
   of log₃2 is aperiodic and `q_j mod u_K` equidistributes.

3. Therefore the honest decomposition is:
   - `S_K = ∅` for `12 ≤ K ≤ 16`: exhaustive fact (this census).
   - `S_K = ∅` for all K ≥ 17: open; equivalent to excluding ~0.26 expected
     pseudo-random events — plausibly TRUE but currently unprovable by the
     tools in this repository.

---

## Recommended use of these results

1. Formalize **Lemma A** in Lean (sorry-free, pure algebra) — upgrades the
   meaning of the invariant: `ostrowski_invariant` becomes "no element of
   the hardwired N_K lists has form q_j+ℓ", i.e., a *list-checkable*
   property instead of an abstract coefficient condition.
2. Formalize the **conditional theorem** (R2′ ∧ R3′ ⟹ S_K=∅, K≥12) so the
   axiom is replaced by two explicitly named per-level hypotheses.
3. Do NOT attempt to prove R2′/R3′ uniformly now; document them as the
   sharp frontier, with this census as evidence.
