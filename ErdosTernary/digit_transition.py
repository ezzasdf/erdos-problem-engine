#!/usr/bin/env python3
"""
Key question: does 2^(uK) mod 3^(K+c) have digits that are 
INDEPENDENT of K for large enough K?

If the digit pattern of 2^(uK) at positions K..K+c-1 is the same 
for all K ≥ K_0, then the lifting transition is a fixed finite 
automaton.
"""
from collections import defaultdict

def uk(K):
    return 2 * (3 ** (K - 1))

def ternary_digits(val, n):
    digits = []
    v = val
    for _ in range(n):
        digits.append(v % 3)
        v //= 3
    return digits

# ============================================================
# STEP 1: Does the digit pattern of 2^(uK) stabilize?
# ============================================================
print("="*80)
print("STEP 1: Digit pattern of 2^(uK) at positions K..K+c")
print("Does it depend on K for large K?")
print("="*80)

MAX_C = 15

for c in range(1, MAX_C + 1):
    patterns = {}
    for K in range(1, 15):
        u = uk(K)
        modulus = 3 ** (K + c)
        val = pow(2, u, modulus)
        digits = ternary_digits(val, K + c)
        pattern = tuple(digits[K:K+c])
        patterns[K] = pattern
    
    # Check if all patterns agree for K >= some threshold
    vals = list(patterns.values())
    all_same = len(set(vals)) == 1
    same_from = None
    for threshold in range(1, 15):
        subset = [patterns[K] for K in range(threshold, 15)]
        if len(set(subset)) == 1:
            same_from = threshold
            break
    
    print(f"c={c:2d}: pattern K=1..14:")
    for K in range(1, 11):
        print(f"    K={K:2d}: {patterns[K]}")
    print(f"    ALL SAME from K={same_from}" if same_from else f"    NOT all same")
    print()

# ============================================================
# STEP 2: The transition function
# ============================================================
print("\n" + "="*80)
print("STEP 2: Transition function for digits under lifting")
print("="*80)

print("""
Given state s = digits of 2^r at positions K..K+c-1.
The three lifts produce:
  state_0 = digits of 2^r at positions K..K+c-1     (= s itself)
  state_1 = digits of 2^(r+uK) at positions K..K+c-1
  state_2 = digits of 2^(r+2uK) at positions K..K+c-1

The transition: s -> {state_1, state_2} (the two survivors)
                (state_0 is the base, which may or may not survive)

Let's compute these for a range of states.
""")

# For a fixed K, compute all transitions
K = 10
u = uk(K)
c = 6  # Look at 6 digits above K
modulus_state = 3 ** (K + c)
modulus_full = 3 ** (K + c + 5)  # Extra precision for carries

print(f"Transitions at K={K}, window={c} digits (positions {K}..{K+c-1}):")

# Compute 2^(uK) mod 3^(K+c+5) — the multiplier
multiplier = pow(2, u, modulus_full)

# For each possible state, compute the transition
# State = digits of 2^r at positions K..K+c-1
# But the transition also depends on X = 2^r mod 3^K

# So the FULL state is (X, digits_at_K_to_K+c-1)
# But digits_at_K_to_K+c-1 is determined by X mod 3^(K+c)

# Actually, 2^r mod 3^(K+c) determines everything
# So the state IS 2^r mod 3^(K+c)

# But we want a K-INDEPENDENT state. The question is:
# does the transition depend only on the digits, not on K?

# Let's test: for K=10 and K=11, do the same digit patterns
# produce the same child digit patterns?

def compute_children(K, r, c):
    """Compute the digit states of the two children of r at level K."""
    u = uk(K)
    modulus = 3 ** (K + c + 5)  # Extra precision
    val = pow(2, r, modulus)
    mult = pow(2, u, modulus)
    
    children = []
    for j in [1, 2]:  # The two surviving lifts (j=0 is the base)
        child_r = r + j * u
        child_val = (val * pow(mult, j, modulus)) % modulus
        child_digits = ternary_digits(child_val, K + c + 5)
        # Extract digits at positions K+1..K+c (shifted up by 1 level)
        new_state = tuple(child_digits[K+1:K+1+c])
        children.append((child_r, new_state))
    
    return children

# Test K=10 vs K=11
for K_test in [10, 11, 12]:
    nk = []
    period = uk(K_test)
    modulus_k = 3 ** K_test
    for r in range(period):
        p = pow(2, r, modulus_k)
        v = p
        has2 = False
        for _ in range(K_test):
            if v % 3 == 2:
                has2 = True
                break
            v //= 3
        if not has2:
            nk.append(r)
    
    print(f"\nK={K_test}: |N_K|={len(nk)}, checking transitions...")
    
    # Check: for states that are the same, are children the same?
    state_to_children = {}
    all_ok = True
    for r in nk[:100]:  # Sample first 100
        modulus = 3 ** (K_test + c)
        val = pow(2, r, modulus)
        state = tuple(ternary_digits(val, K_test + c)[K_test:K_test+c])
        
        children = compute_children(K_test, r, c)
        child_states = [ch[1] for ch in children]
        
        if state in state_to_children:
            if state_to_children[state] != child_states:
                all_ok = False
                print(f"  INCONSISTENT: state {state} maps to {child_states} but previously {state_to_children[state]}")
        else:
            state_to_children[state] = child_states
    
    print(f"  Consistent transitions: {all_ok}")
    print(f"  Unique states: {len(state_to_children)}")

# ============================================================
# STEP 3: K-independent transition
# ============================================================
print("\n" + "="*80)
print("STEP 3: K-independent transition test")
print("="*80)

# The question: if two different K values produce the same digit state,
# do they produce the same children?

# The answer depends on whether the MULTIPLIER 2^(uK) has the same
# digits at positions K..K+c-1 for different K.

# From Part 1, we saw that the digits stabilize for large K.
# Let's check if the transition is truly K-independent.

K_ref = 10
c = 6
u_ref = uk(K_ref)
mult_full = pow(2, u_ref, 3 ** (K_ref + c + 5))

# Compute children of a specific state
r_test = 0  # 2^0 = 1
modulus = 3 ** (K_ref + c + 5)
val = pow(2, r_test, modulus)
state_ref = tuple(ternary_digits(val, K_ref + c)[K_ref:K_ref+c])

print(f"Reference: K={K_ref}, r={r_test}, state={state_ref}")

for j in [1, 2]:
    child_val = (val * pow(mult_full, j, modulus)) % modulus
    child_digits = ternary_digits(child_val, K_ref + c + 5)
    child_state = tuple(child_digits[K_ref+1:K_ref+1+c])
    print(f"  Lift j={j}: child state = {child_state}")

# ============================================================
# STEP 4: The ACTUAL transition table
# ============================================================
print("\n" + "="*80)
print("STEP 4: Complete transition table (K=10, c=6)")
print("="*80)

K = 10
c = 6
period = uk(K)
modulus_state = 3 ** (K + c)
modulus_full = 3 ** (K + c + 5)
mult = pow(2, uk(K), modulus_full)

# Compute N_K
nk = []
modulus_k = 3 ** K
for r in range(period):
    p = pow(2, r, modulus_k)
    v = p
    has2 = False
    for _ in range(K):
        if v % 3 == 2:
            has2 = True
            break
        v //= 3
    if not has2:
        nk.append(r)

# For each state, compute transitions
transitions = defaultdict(lambda: {'children': [], 'base_survives': 0, 'digit2_count': 0})

for r in nk:
    val = pow(2, r, modulus_full)
    state = tuple(ternary_digits(val, K + c)[K:K+c])
    
    # Check if base survives (j=0)
    base_digits = ternary_digits(val, K + c + 5)
    base_has_digit2_at_K = (base_digits[K] == 2)
    
    # Check children
    child_states = []
    for j in [1, 2]:
        child_val = (val * pow(mult, j, modulus_full)) % modulus_full
        child_digits = ternary_digits(child_val, K + c + 5)
        child_state = tuple(child_digits[K+1:K+1+c])
        child_has_digit2 = any(d == 2 for d in child_digits[K+1:K+c+2])
        child_states.append((child_state, child_has_digit2))
    
    # Which ones survive?
    survivors = []
    if not base_has_digit2_at_K:
        survivors.append('base')
    for j, (cs, has2) in enumerate(child_states):
        if not has2:
            survivors.append(f'child{j+1}')
    
    transitions[state]['children'] = child_states
    transitions[state]['survivors'] = survivors
    if base_has_digit2_at_K:
        transitions[state]['digit2_count'] += 1
    for _, has2 in child_states:
        if has2:
            transitions[state]['digit2_count'] += 1

print(f"Total unique states at K={K}: {len(transitions)}")
print(f"\nTransition table (showing which survive and digit-2 status):")

for state in sorted(transitions.keys())[:20]:
    info = transitions[state]
    child_info = [(cs[:4], has2) for cs, has2 in info['children']]
    print(f"  state={list(state)}  children={child_info}  survivors={info['survivors']}")

# Count: how many states have digit 2 in their own window?
states_with_digit2 = sum(1 for s in transitions if any(d == 2 for d in s))
print(f"\nStates with digit 2 in own window: {states_with_digit2}/{len(transitions)}")
