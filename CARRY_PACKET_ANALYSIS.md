# Spencer's Carry-Packet Approach: Translation to Lifting Tree

## The Core Identity

Spencer reduces the problem to powers of 4 (since odd powers of 2 end in digit 2).

The key identity: **4^e = 3R_e + 1** where **R_e = (4^e - 1)/3**.

This means: ternary(4^e) = ternary(R_e) followed by a final 1.

So: 4^e has no digit 2 ⟺ R_e has no digit 2.

## The Self-Overlap

To go from R_e to R_{e+1}:
```
R_{e+1} = 4R_e + 1 = R_e + 3R_e + 1
```

In ternary: **4R_e = R_e + 3R_e** is a self-overlap (adding R_e to its left-shift).

## Carry Packets

When we add R_e to 3R_e (R_e shifted left by 1), carry propagates through overlapping digits.

A **carry packet** is a block of consecutive digit-2 entries that propagates leftward.

**Primitive carry packets**: Minimal patterns that can survive the self-overlap without producing digit 2.

## Spencer's Classification

The paper classifies all primitive carry packets and shows:

1. Most carry-compatible artifacts carry **persistent non-dyadic cofactors** (like 5 or 7).
2. Ternary scaling cannot remove those cofactors.
3. The **only nontrivial packet** that is both carry-admissible and dyadically pure is **2101_3 = 64**.

## The Unique Packet

**2101_3 = 64** produces **100111_3 = 256** after multiplication by 4.

Verification:
```
4 · 64 = 256
2101_3 = 2·27 + 1·9 + 0·3 + 1 = 64
100111_3 = 243 + 9 + 3 + 1 = 256
```

## Non-Recurrence

Spencer shows this packet cannot recur at a higher separated ternary scale:
- Any separated reuse has the form 64(1 + 3^s)
- For s ≥ 2, the factor (1 + 3^s) has a non-dyadic cofactor
- The adjacent case is the known transition 64 → 256
- The next quadrupling produces 1101221_3 (has digit 2)

## Translation to Lifting Tree

### The R_e Sequence

```
R_0 = 0 = 0_3 (trivial)
R_1 = 1 = 1_3 ✓
R_2 = 5 = 12_3 ✗ (digit 2)
R_3 = 21 = 210_3 ✗ (digit 2)
R_4 = 85 = 10011_3 ✓
R_5 = 341 = 110121_3 ✗ (digit 2)
```

### The Lifting Tree for R_e

Define: S_K = {e < u_K : R_e mod 3^K has no digit 2}

The tree S_K is:
- S_1 = {0, 1} (R_0 = 0, R_1 = 1)
- S_2 = {0, 1} (R_2 = 5 = 12_3 has digit 2)
- S_3 = {0, 1} (R_3 = 21 = 210_3 has digit 2)
- S_4 = {0, 1, 4} (R_4 = 85 = 10011_3 no digit 2)
- S_5 = {0, 1, 4} (R_5 = 341 = 110121_3 has digit 2)

### The Gap

The carry packet analysis shows that R_4 = 10011_3 does NOT have the packet 2101_3, so 4R_4 = 110121_3 has digit 2.

But R_1 = 1_3 is a trivial packet that survives the multiplication by 4.

The question: why does R_4 survive (have no digit 2) even though it doesn't have the packet 2101_3?

### The Key Insight

The carry packet analysis is about LOCAL digit patterns, not GLOBAL survival.

The packet 2101_3 = 64 is the only LOCAL pattern that can survive the multiplication by 4 without producing digit 2.

But R_4 = 10011_3 has a different GLOBAL structure that also survives.

So the carry packet analysis is necessary but not sufficient.

### What's Missing

The GLOBAL argument: why does R_4 = 10011_3 survive even though it doesn't have the packet 2101_3?

The answer might be: R_4 = 10011_3 is a COMBINATION of smaller packets that together survive the multiplication by 4.

But the carry packet analysis doesn't capture this combination.

## The Attack Strategy

### Step 1: Formalize the Carry Packet Analysis

Define:
- Carry packets as ternary digit patterns
- The self-overlap operation R_e + 3R_e
- The survival condition (no digit 2 in the result)

### Step 2: Classify All Surviving Patterns

Show that the only R_e values that survive the multiplication by 4 without producing digit 2 are:
- R_0 = 0 (trivial)
- R_1 = 1 (trivial)
- R_4 = 85 (the unique nontrivial survivor)

### Step 3: Prove Non-Recurrence

Show that R_4 = 85 cannot be extended to a larger survivor:
- R_5 = 341 has digit 2
- R_e for e > 4 all have digit 2

### Step 4: Connect to the Lifting Tree

Show that the lifting tree N_K for 2^r is equivalent to the lifting tree S_K for R_e, up to the reduction r = 2e.

### Step 5: Prove the Global Theorem

Show that ∩_K N_K = {0, 2, 8} by showing that ∩_K S_K = {0, 1, 4}.

## The Hard Part

The GLOBAL argument is still missing. The carry packet analysis shows that certain LOCAL patterns cannot survive, but it doesn't show that ALL patterns outside the packet 2101_3 cannot survive.

The gap between LOCAL and GLOBAL is exactly the Erdős conjecture.

## Possible Approaches

### Approach 1: Induction on e

Try to prove by induction on e that R_e has digit 2 for all e > 4.

Problem: The induction step is unclear. R_{e+1} = 4R_e + 1, but the carry structure of 4R_e depends on the specific digits of R_e.

### Approach 2: Density Argument

Show that the set of R_e values with no digit 2 has density 0.

Problem: Density 0 doesn't mean empty. The Erdős conjecture is stronger than density 0.

### Approach 3: Structural Argument

Show that the carry packet structure forces digit 2 to appear after a bounded number of steps.

Problem: The bound is r-dependent and not known to be uniform.

### Approach 4: 3-Adic Analysis

Use the 3-adic logarithm to study the dynamics of R_e in ℤ₃.

Problem: The ergodic argument gives almost-everywhere results, not every result.

## Conclusion

Spencer's carry-packet approach provides the LOCAL obstruction. The missing piece is the GLOBAL argument that connects the local obstructions to the global conjecture.

The attack strategy is:
1. Formalize the carry packet analysis in Lean
2. Classify all surviving patterns
3. Prove non-recurrence
4. Connect to the lifting tree
5. Prove the global theorem

The hard part is step 5: the global argument. This is exactly the Erdős conjecture.
