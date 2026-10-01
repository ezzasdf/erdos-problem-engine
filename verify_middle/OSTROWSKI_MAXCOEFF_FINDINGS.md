# Ostrowski Max-Coefficient Test — Findings

**Date:** 2026-08-25
**Purpose:** Checkpoint Step 2 — kill or confirm the stronger Ostrowski invariant
`max_{k≥5} b_k(r) ≥ 2` for all non-special `r ∈ N_K \ {0,2,8}`, before touching Lean.

**Scripts:** `ostrowski_maxcoeff_test.py`, `ostrowski_m1_anatomy.py`, `ostrowski_sum_invariant.py`

---

## Verdict on the checkpoint hypothesis

### 1. `max_{k≥5} b_k(r) ≥ 2` is **KILLED**

Counterexamples with M(r) = max_{k≥5} b_k(r) = 1 exist at every tested K:

| K | \|N_K \ {0,2,8}\| | #M=1 | min M |
|-----|------|------|-------|
| 10  | 509    | 14 | 1 |
| 11  | 1021   | 20 | 1 |
| 12  | 2045   | 35 | 1 |
| 13  | 4093   | 37 | 1 |
| 14  | 8189   | 27 | 1 |
| 15  | 16381  | 14 | 1 |
| 16  | 32765  | 26 | 1 |

The M=1 set churns across levels (residues enter and drop) but never empties;
a stable core of **4 residues survives every level K=10..15**: `{1134, 1644,
24806, 26432}`.

### 2. But the exceptions are *spread*, not *weak* — anatomy of the core

| r | active positions k≥5 | coefficients | low part (<19) |
|------|----------------------|--------------|----------------|
| 1134 | {6, 9}               | all 1        | 15             |
| 1644 | {5, 7, 8, 9}         | all 1        | 2              |
| 24806| {6, 10}              | all 1        | 14             |
| 26432| {6, 7, 8, 9, 10}     | all 1        | 17             |

Every persistent exception uses **several distinct convergent denominators,
one copy each**. This immediately suggests testing total mass instead of max.

---

## The replacement invariant: `Σ_{k≥5} b_k(r) ≥ 2` — CONFIRMED

Total Ostrowski mass above q₅=19 over non-special residues:

| K | min Σ_{k≥5} b_k | #violations (sum=1) |
|-----|------|------|
| 10  | 1 | 3 |
| 11  | 1 | 1 |
| **12** | **2** | **0** |
| **13** | **2** | **0** |
| **14** | **2** | **0** |
| **15** | **2** | **0** |
| **16** | **2** | **0** |

Zero violations across ~65,000 residues for K = 12..16 — exactly the range
(K ≥ 13) where the Lean `ostrowski_invariant` axiom currently stands, with
K=12 available as formal base case.

### Equivalent reformulation (important for proof design)

Greedy canonical representation gives remaining < q_i after processing
position i, so the "low part" built from q₀..q₄ is always ≤ 18. Hence:

```
Σ_{k≥5} b_k(r) = 1  ⟺  r = q_k + ℓ  for some k ≥ 5 and 0 ≤ ℓ ≤ 18.
```

So the confirmed invariant says:

> **No non-special trailing survivor lies within distance 18 of any single
> convergent denominator q_k (k ≥ 5).**

Special values {0, 2, 8} have zero high mass (pure low parts), which matches:
the invariant cleanly separates exactly {0,2,8} from everything else in N_K.

---

## Logical role pinned down (do NOT skip this)

The coefficient condition is **not sufficient alone**. φ⁻¹(C₃₀) has positive
measure ≈ C·(2/3)³⁰ ≈ 5.3×10⁻⁶, so equidistribution guarantees integers with
large coefficients landing inside it. Direct scan (r < 300,000):

- r = **26379**, r = **116655**: Σ_{k≥5} b_k ≥ 2 **and** inside φ⁻¹(C₃₀).
  Both FAIL the trailing condition B_K for all K=5..15 (checked directly).

Therefore the correct theorem shape is the joint chain:

```
r ∈ N_K \ {0,2,8}   AND   Σ_{k≥5} b_k(r) ≥ 2
        ⟹ explicit displacement bound on {rα}
        ⟹ {r·log₃2} ∉ φ⁻¹(C₃₀)
        ⟹ 2^r has ternary digit 2
```

The coefficient condition is the middle link; N_K membership carries real
content too. Neither alone suffices.

---

## Distribution behavior as K grows (checkpoint item 4)

- Mass of M(r) drifts upward with K (e.g., K=15 distribution extends to M=31,
  vs cap ~23 for K≤14), consistent with |N_K| = 2^{K−1} growth while u_K
  grows by ×3 — residues reach higher convergent denominators.
- The M=1 tail does not vanish: 35 → 37 → 27 → 14 → 26 (non-monotone,
  persistent). Any proof strategy relying on "coefficients get large"
  is wrong; the correct target is the mass/count formulation.
- #nnz=1 (single distinct active position) shrinks to 1 residue by K=15/16 —
  near-dead but not provably dead; another reason mass ≥ 2 (which allows
  nnz=1 with coefficient 2... no wait: nnz=1 with b_k=1 gives sum=1, killed;
  nnz=1 with b_k≥2 gives sum≥2 ✓) is the robust formulation.

---

## Consequence test status (checkpoint item 5)

Separation {rα} ∉ φ⁻¹(C₃₀) is universal over non-special N_K regardless of
any coefficient statistic (30595/30595 + more at K=16) — so correlation cannot
distinguish mechanisms. What the data supports:

- sum ≥ 2 is *consistent* with separation and *necessary-looking*
  (no counterexample in ~65K residues);
- standalone insufficiency proven by explicit counterexamples (above);
- an actual proof needs the **explicit displacement argument**:
  {q_k α} ≈ (−1)^k / q_{k+1} bounds each unit of high mass's contribution;
  combined with the Saye-tree constraint linking N_K membership to the
  coefficient pattern, one must derive a lower bound on distance from
  φ⁻¹(C₃₀). Not yet constructed — this is Step 3 work.

---

## Recommended next actions

1. **Adopt `Σ_{k≥5} b_k(r) ≥ 2` as the working invariant** (replaces the
   weaker `∃k≥5 b_k≥1`, which is nearly vacuous given q₅=19).
2. Prove it structurally via Saye recursion: show that if r ∈ N_K has
   high-mass form q_k+ℓ, its surviving extensions in N_{K+1} cannot stay
   in that form (empirically the M=1 set churns — extensions of q_k+ℓ die).
   Python first: trace the family trees of the 4 core exceptions.
3. Then build the displacement lemma: quantify how ≥2 units of high mass
   plus low-part structure push {rα} out of the (explicitly described)
   interval union φ⁻¹(C₃₀).
4. Only then formalize; do not add any new axiom.

---

# STEP 3 RESULTS (2026-08-25, later session)

**Scripts:** `ostrowski_family_trees.py` + inline probes (survival-depth scan)

## 1. Saye family trees — the mass-1 population is fully enumerable

Saye structure verified exactly at every level K=5..15: every r' ∈ N_{K+1}
has parent r' mod u_K ∈ N_K, and every parent has **exactly 2** surviving
children (of {r, r+u_K, r+2u_K}).

Across all levels K=5..16 only **eleven distinct mass-1 residues ever exist**
(all forms q_j + ℓ, j ≤ 8):

```
20=q[5]+1   24=q[5]+5    26=q[5]+7
72=q[6]+7   74=q[6]+9    78=q[6]+13  80=q[6]+15
96=q[7]+12
486=q[8]+1  488=q[8]+3   494=q[8]+9
```

Key dynamics:
- **Self-persistence:** a mass-1 value persists as itself (child i=0) until
  its trailing check B_K fails; e.g. 72 survives K=6..11 then dies.
- **Catastrophic death:** when the self-child fails, the two shifted children
  jump to masses 6–23 (never 1). Observed in all 11 death events.
- **Births from special parents:** 486/488/494 = u₆ + {0,2,8} — new mass-1
  nodes are born when a shifted child of a *special* (mass-0) node lands on
  q_j+ℓ form.
- Last survivor: **72**, dies entering K=12 (final children masses [12, 23]).

## 2. IMPORTANT CORRECTION — universal exclusion is FALSE

The hoped theorem "∀ j≥5, ℓ≤18: q_j+ℓ ∉ N₁₂" was probed for j=5..150:
**8 violations of B₁₂ at large j** (j = 32, 47, 48, 85, 87, 88, 142×2).
Hit rate 8/2280 vs memoryless expectation 13.2 — roughly pseudo-random.

These do NOT violate the actual invariant because N_K only contains
r < u_K (level range), but they destroy any proof strategy based on
excluding q_j+ℓ from trailing-Cantor status *unconditionally*.

## 3. Range-restricted truth — survival depth vs reachability

Define for a candidate form f = q_j+ℓ:
- reach K_r(f) = min{K : u_K > f}
- survival depth D(f) = max{K : B_K(f)} (monotone, computable)

f belongs to some N_K ⟺ D(f) ≥ K_r(f). Probed j=5..80, ℓ=0..18 (1444
candidates, depths up to K=70):

> **The ONLY violators are the eleven forms above (all j ≤ 8).**
> For every j = 9..80: D(f) < K_r(f) with margins growing ~linearly in j.

Corrected theorem shape (empirically exact through massive probing):

> The only integers of form q_j+ℓ (j≥5, ℓ≤18) that ever belong to any N_K
> are the 11 values above, whose membership tops out at K ≤ 11.

This is a *finiteness* statement — consistent with the Borel–Cantelli
heuristic Σⱼ P(B_{K(j)}) < ∞ — hence far more plausible as a provable
target than universal exclusion.

## 4. Displacement feature mining — NEGATIVE result

Over all non-special residues K=12..15 (30,708 rows):
- Pearson(f₂, ·): mass 0.03/-0.01, nnz ≤0.04, maxb ≤0.03, jtop ≤0.02 —
  **essentially zero**; low part weakly positive 0.10–0.12.
- mean f₂ ≈ 2.08 stable; max f₂ = 23 (7-digit margin below C₃₀ window).

Interpretation: separation depth behaves like a feature-independent geometric
random variable. There is **no measurable "coefficient magnitude pushes
{rα} out of C₃₀" mechanism**. Also note: under pure randomness,
P(separation failure) ≈ C(2/3)³⁰ ≈ 5×10⁻⁶ × 65K residues ≈ 0.34 expected
failures — observing 0 is unsurprising, so separation alone carries little
statistical content. The bridge's real content is the joint shrinkage
(Phase 12), not marginal separation.

## 5. Strategic assessment after Steps 2–3

What survives:
- `Σ_{k≥5} b_k(r) ≥ 2` for all non-special r ∈ N_K, K≥12: empirically
  perfect (~65K residues + exhaustive S_K=∅ for K=12..16).
- Reformulation lemma (pure algebra, Lean-friendly):
  sum=1 ⟺ ∃ j≥5, ℓ≤18 : r = q_j + ℓ.
- Finiteness of the mass-1 population with explicit witness list (11 values).

What blocks a cheap proof:
- Any uniform-K argument must control survival depth D(q_j+ℓ) for **unbounded
  j**, i.e. 3-adic behavior of convergent denominators mod 3^K — no
  periodicity available (CF of log₃2 is aperiodic). This is genuine open-
  problem difficulty resurfacing.
- The displacement-magnitude mechanism is empirically dead; do not chase it.

Recommended next investigations (in order):
1. **Shifted-children rule**: verify/prove "shifted children of a mass-1 node
   never have mass 1" (held in all 11 death events). Combined with the birth
   characterization (births = shifted children of special nodes landing on
   q_j+ℓ), S_K becomes a two-sided birth-death process that might be closed
   by a finite induction over the *special-parent subtree* rather than over
   unbounded j.
2. If (1) stalls: fall back to strengthening BridgeUniform differently —
   e.g. prove the K=12 base case with the sum-invariant wired in as a
   *theorem over the hardwired NK_12 list* (finite, kernel-safe via mod-3^M
   checks like BridgeMiddle), and treat K≥13 uniformity as the explicitly
   stated open frontier rather than an axiom.

## Artifacts

- `verify_middle/ostrowski_maxcoeff_test.py` — main K=10..15 test
- `verify_middle/ostrowski_m1_anatomy.py` — exception anatomy + alternatives
- `verify_middle/ostrowski_sum_invariant.py` — K=16 validation + logical role
- `verify_middle/ostrowski_family_trees.py` — Saye trees + feature mining
