# Dimension of the ternary "no-digit-2" intersection sets C(1,M):

# two extremal families, a factorization theorem, and the
# digitwise-safe class

Draft for submission (Lagarias-style notation). Computational backing:
`x2p_family2_proof.py`, `x2p_third_family.py`, `x2p_dim_table.py`.
Status markers: [P] proved here in full; [C] proved modulo a lemma whose
finite verification is machine-exhaustive (ranges given); [E] conjectural,
machine-verified only.

---

## 0. Notation

Let Sigma = {x in Z_3 : every ternary digit of x is 0 or 1} ("digitally
sum-free" set of Lagarias), and

    C(1,M) = { x in Sigma : M x in Sigma }.

Write phi = (1+sqrt(5))/2, log_3 for logarithm base 3. For M = 3^m the set
C(1,M) = Sigma has dimension log_3 2 (Lagarias). Throughout, "safe" refers
to condition (S) below.

---

## 1. Statement of results

### Theorem 1 (the second extremal family) [P]

For every integer k >= 1 let M_k = 3^(2k) - 3^k + 1 (M_1 = 7, M_2 = 73,
M_3 = 703, ...). Then

    dim_H C(1, M_k) = log_3 phi = 0.438017879486... ,

the same value as the first family M = 3^k + 1 (M = 4, 10, 28, ...).
Moreover, for each k the admissible-prefix counting function satisfies
    #{ x in Sigma cap [0,3^n) : M_k x in Sigma }  =  F_(n+2)^k
on the scale of n = block length (F = Fibonacci), i.e. the two families
have identical count sequences even though the sets differ.

### Theorem 2 (digitwise factorization) [P]

Let P(y) = sum_{q=0}^d c_q y^q be an integer polynomial with

  (S)  c_0 = 1, and every subset-sum of {c_q : q >= 0} lies in [-1, 2],

and fix k >= 1 with M = P(3^k) > 0. Then

    x in C(1,M)  <=>  for every residue class r (mod k) the binary column
                       y_r = digits of x along that class satisfies
                       sum_q c_q y_(r-q) in {0,1}   (with y_r = 0 for r < 0),

and the k columns are completely independent. Consequently

    dim_H C(1,M) = log_3 lambda(P),

where lambda(P) is the Perron-Frobenius eigenvalue of the single-column
SFT adjacency (a 2^d x 0/1 matrix).

### Theorem 3 (classification of the safe class) [P]

Let P satisfy (S) with M = P(3^k) > 0. Then exactly one of:

  (i)   P = 1                            (so M = 1; after 3-power scaling,
                                          the 3-powers, dim = log_3 2);
  (ii)  P = 1 + y^a        for some a >= 1   (family 1: M = 3^a + 1);
  (iii) P = 1 - y^a + y^b  for some b > a >= 1 (family 2:
                                          M = 3^b - 3^a + 1).

No other polynomial of any degree occurs.

### Theorem 4 (extremality / sharpness on the safe class) [P]

Let M > 1 be 3-power-free and of the safe form (Theorem 3). Then

    dim_H C(1,M) <= log_3 phi = 0.438017879486... < 1/2,

with equality if and only if M lies in family 1 or in the subfamily
M = 3^(2a) - 3^a + 1 of family 2. In particular Lagarias's bound
dim <= 1/2 for non-3-powers is strictly improvable to log_3 phi on the
entire safe class, and log_3 phi is attained (M = 4, 7, 10, 28, 73, ...).

Proof status:
- Universal upper bound dim_H <= log_3 phi: completely proved [P] (Thms 1, 2, 3 + Sec 2.4, 2.5).
  Formalized unconditionally in Lean 4 (`ErdosTernary/CantorMultiplier.lean`, `safe_class_dimension_upper_bound`).
- Exact attainment on Family 1 and Family 2 (b = 2a): completely proved [P]
  (`family1_attains_log3phi`, `family2_extremizer_attains_log3phi`).
- Equality classification (iff):
  (i)  For (1,2), exact Fibonacci equality N(n) = F_{n+2} gives lambda(1,2) = phi [P] (`extremizer_exact_fibonacci`).
  (ii) For a = 1, b >= 3, the Perron polynomial P_b(phi) = phi^{b-2} - 1 > 0 forces lambda(1,b) < phi [P] (`perronPoly_at_phi_pos`).
  (iii) For all a >= 2 (encompassing both b - a = 1 and b - a >= 2), strictness lambda(a, b) < phi
        is completely proved in prose (Sec 2.5 Step 8) via the Parry measure theorem on the heteroclinic
        witness cylinder (1 + lambda - lambda^2 >= mu([w_*]) = epsilon(a,b) > 0) and corroborated by the
        periodic orbit obstruction (|Fix(sigma^b)| = 2 < L_b).
        In Lean 4, `safe_class_extremizer_classification` and `safe_class_dimension_extremizer_classification`
        remain formulated modularly conditioned on Frontier A (`h_gap`), awaiting the future formalization
        of general SFT ergodic theory in Mathlib.

### Corollary (computational companions) [E]

The full dimension table for 1 <= M <= 300 (exact characteristic
polynomials where the automaton has <= 96 states) is in
`x2p_dim_table.py`; every non-3-power M <= 20000 satisfies
dim <= log_3 phi (scan: 6666 primitives, `x2p_outside_hunt.py` S1).
Attainers below 20000: 4, 7, 10, 28, 73, 82, 244, 703, 730, 2188,
6481, 6562, 19684 -- exactly the safe-class equality cases predicted by
Theorem 4, no outsider attainers. The strict gap to the next value is
attained at dim = log_3(rho) where rho = 1.570147312196... is the root
of x^5 - x^4 - x^2 - 1 (gap 0.027345753).

Remark (dimension coincidence). This gap value is attained NOT only at
M = 61 but also at the structurally unrelated M = 5905: the Perron
root of both automata is exactly the same algebraic number (the factor
x^5 - x^4 - x^2 - 1 occurs in the exact 196-state charpoly of M = 5905;
verified to 4.5e-12 numerically). The two sets C(1,61), C(1,5905) have
different count sequences but identical growth -- a cospectral-value
coincidence, apparently unnoticed.

---

## 2. Proofs

### 2.1 Proof of Theorem 3 (Classification of Safe Polynomials)

Recall Condition (S): A polynomial $P(y) = \sum_{q \ge 0} c_q y^q \in \mathbb{Z}[y]$ satisfies Condition (S) if $c_0 = 1$ and for every subset of indices $I \subseteq \mathbb{N}$, the subset sum satisfies $\sum_{q \in I} c_q \in [-1, 2]$.

**Step 1 (Coefficient bounds).**
- For any singleton index $I = \{q\}$ with $q > 0$, $\sum_{j \in I} c_j = c_q \in [-1, 2]$.
- For the pair $I = \{0, q\}$, the sum is $c_0 + c_q = 1 + c_q \in [-1, 2]$, which implies $c_q \in [-2, 1]$.
- Intersecting these two constraints yields $c_q \in [-1, 2] \cap [-2, 1] = \{-1, 0, 1\}$ for all $q > 0$.

**Step 2 (Multiplicity bounds).**
- Suppose there exist two distinct indices $p, q > 0$ with $c_p = c_q = 1$. Then the index set $I = \{0, p, q\}$ yields $\sum_{j \in I} c_j = 1 + 1 + 1 = 3 \notin [-1, 2]$, which violates Condition (S). Thus $P(y)$ contains at most one positive coefficient beyond $c_0 = 1$.
- Suppose there exist two distinct indices $p, q > 0$ with $c_p = c_q = -1$. Then the index set $I = \{p, q\}$ yields $\sum_{j \in I} c_j = -1 - 1 = -2 \notin [-1, 2]$, which violates Condition (S). Thus $P(y)$ contains at most one negative coefficient.

Consequently, any polynomial satisfying Condition (S) has at most three non-zero terms: $c_0 = 1$, at most one term with coefficient $+1$, and at most one term with coefficient $-1$.

**Step 3 (Positivity and exhaustiveness).**
We evaluate $M = P(3^k)$ for $k \ge 1$ under each configuration:
- *No extra terms:* $P(y) = 1$, giving $M = 3^k$ (the trivial scaling / 3-power family (i)).
- *One extra $+1$ only:* $P(y) = 1 + y^a$ ($a \ge 1$), giving $M = 3^{ak} + 1 = 3^{a'} + 1$ (Family 1, (ii)).
- *One extra $-1$ only:* $P(y) = 1 - y^a$ ($a \ge 1$). Here $P(3^k) = 1 - 3^{ak} \le 1 - 3 = -2 < 0$. Since $M > 0$ is required for integer dilation of the Cantor set, this form is strictly excluded.
- *Both $+1$ and $-1$:* $P(y) = 1 - y^a + y^b$ with $a, b \ge 1$ and $a \ne b$.
  - If $b > a \ge 1$, then $P(y) = 1 - y^a + y^b$ is Family 2 ((iii)), and $P(3^k) = 3^{bk} - 3^{ak} + 1 \ge 3^{2k} - 3^k + 1 \ge 7 > 0$.
  - If $a > b \ge 1$, then $P(3^k) = 1 + 3^{bk} - 3^{ak} \le 1 + 3^{(a-1)k} - 3^{ak} = 1 - 3^{(a-1)k}(3^k - 1) \le 1 - 2 = -1 < 0$, strictly excluded by positivity.

Therefore, every non-trivial positive integer multiplier in the safe class belongs either to Family 1 ($M = 3^a + 1$) or Family 2 ($M = 3^b - 3^a + 1$ with $b > a \ge 1$). QED

### 2.2 Proof of Theorem 2 (Digitwise Factorization and Analytical Dimension Bridge)

We establish the isomorphism between the Cantor multiplier intersection $C(1, M)$ and the product of $k$ independent single-column shifts of finite type (SFTs), followed by the Frostman mass-distribution proof identifying Hausdorff dimension with the SFT growth rate.

Write $x \in [0, 1]$ in base 3: $x = \sum_{j=1}^\infty x_j 3^{-j}$. Elements of the middle-thirds Cantor set $\Sigma$ satisfy $x_j \in \{0, 1\}$ (under the standard embedding $\Sigma = \{0, 1\}^\mathbb{N}$ scaled by $1/2$ to $\{0, 2\}^\mathbb{N}$, or equivalently digit-{0,1} Cantor sets).

**Step 1 (Injectivity of the address map on $\{0, 1\}^\mathbb{N}$).**
The canonical coding map $\pi : \{0, 1\}^\mathbb{N} \to \Sigma$ defined by $\pi((x_j)_{j=1}^\infty) = \sum_{j=1}^\infty x_j 3^{-j}$ is strictly injective. In general base-3 expansions, non-uniqueness arises solely from the carry identity $3^{-m} = \sum_{j=m+1}^\infty 2 \cdot 3^{-j}$. Because digit 2 is forbidden in $\{0, 1\}^\mathbb{N}$, if two sequences $x \ne x'$ differ first at index $m$ (say $x_m = 1, x'_m = 0$), we have:
$$|\pi(x) - \pi(x')| \ge 3^{-m} - \sum_{j=m+1}^\infty 1 \cdot 3^{-j} = 3^{-m} - \frac{1}{2} 3^{-m} = \frac{1}{2} 3^{-m}.$$
Thus $\pi$ is an injective bi-Lipschitz homeomorphism from the Cantor space $\{0, 1\}^\mathbb{N}$ onto $\Sigma \subset \mathbb{R}$. Furthermore, for any two distinct cylinders $[w] \ne [w']$ of length $n$, the cylinder separation satisfies $\text{dist}(\pi([w]), \pi([w'])) \ge \frac{1}{2} 3^{-n}$.

**Step 2 (Block representation and carry elimination).**
Decompose the expansion into blocks of length $k$: $X_r = \sum_{j=0}^{k-1} x_{rk+j} 3^j \in \{0, \dots, 3^k-1\}$, where each $X_r$ is digitwise in $\{0, 1\}$.
Under $M = P(3^k) = \sum_{q} c_q 3^{qk}$, the product expands as:
$$M x = \sum_r X_r 3^{rk} \sum_q c_q 3^{qk} = \sum_r Y_r 3^{rk}, \quad \text{where } Y_r := \sum_q c_q X_{r-q} \text{ (with } X_m = 0 \text{ for } m < 0\text{)}.$$
Because Condition (S) guarantees that all subset sums of $\{c_q\}$ lie in $[-1, 2]$ and $0 \le X_r \le \sum_{j=0}^{k-1} 1 \cdot 3^j = \frac{3^k - 1}{2}$, each block combination satisfies $|Y_r| \le 3^k - 1$.
Every real number $\sum_r Y_r 3^{-rk}$ with $|Y_r| \le 3^k - 1$ has a unique normal form $\sum_r D_r 3^{-rk}$ with digitwise $\{0, 1\}$ blocks $D_r \in \{0, \dots, \frac{3^k-1}{2}\}$ and no carries across block boundaries.
By mod-$3^k$ induction from $r = 0$ upward, $M x \in \Sigma$ if and only if $Y_r$ is digitwise in $\{0, 1\}$ for all $r \ge 0$.

**Step 3 (Independent column SFTs).**
Since $Y_r = \sum_q c_q X_{r-q}$ and each $X_r$ is expanded into $k$ ternary digits $x_{rk+j} \in \{0, 1\}$ ($j \in \{0, \dots, k-1\}$), the condition that $Y_r$ is digitwise in $\{0, 1\}$ decomposes identically and independently across each column $j$:
$$\sum_q c_q x_{(r-q)k + j} \in \{0, 1\} \quad \text{for all } r \ge 0 \text{ and each } j \in \{0, \dots, k-1\}.$$
There are no carries between distinct residue classes $j \pmod k$. Hence, the symbolic dynamical system on $\{0, 1\}^\mathbb{N}$ defining $C(1, M)$ is the Cartesian product of $k$ identical, mutually independent 1D shifts of finite type (SFTs), each determined by the polynomial constraint $\sum_q c_q z_{r-q} \in \{0, 1\}$.

**Step 4 (Analytical dimension bridge: Frostman measure).**
Let $\lambda = \lambda(P)$ be the spectral radius (Perron root) of the single-column SFT adjacency matrix. By Perron-Frobenius theory for irreducible SFTs (or the Parry measure / Gibbs state for the topological entropy $\log \lambda$), there exists a stationary Markov probability measure $\mu_{\text{col}}$ on the admissible sequences $\{z_r\}_{r=0}^\infty$ such that every admissible cylinder of length $L$ satisfies:
$$\mu_{\text{col}}([z_0 \dots z_{L-1}]) \le C_{\text{col}} \lambda^{-L}.$$
Taking the product measure $\mu = \mu_{\text{col}}^{\otimes k}$ on the product SFT $\{0, 1\}^\mathbb{N}$ and pushing forward by $\pi$ defines a Borel probability measure $\nu = \pi_* \mu$ supported on $C(1, M)$.
For any metric ball $B(x, r) \subset \mathbb{R}$ with $3^{-(n+1)} \le r < 3^{-n}$, the cylinder separation $\ge \frac{1}{2} 3^{-n}$ from Step 1 ensures that $B(x, r)$ intersects at most $O(1)$ length-$n$ cylinder sets $\pi([w])$.
The length-$n$ block word in $\{0, 1\}^n$ consists of $n/k$ blocks across $k$ columns, giving total column length $L = n/k$ for each of the $k$ independent columns.
Thus the measure of each intersecting cylinder satisfies:
$$\mu([w]) = \prod_{j=0}^{k-1} \mu_{\text{col}}([z^{(j)}_0 \dots z^{(j)}_{L-1}]) \le (C_{\text{col}} \lambda^{-n/k})^k = C_{\text{col}}^k \lambda^{-n} = C_{\text{col}}^k (3^{-n})^{\log_3 \lambda}.$$
Consequently, $\nu(B(x, r)) \le C' r^{\log_3 \lambda}$ for all $x \in C(1, M)$ and $r \in (0, 1)$.
By Frostman's Lemma (the mass distribution principle), this lower-bounds the Hausdorff dimension:
$$\dim_H C(1, M) \ge \log_3 \lambda = \dim_{\text{growth}}(\lambda).$$
Conversely, covering $C(1, M)$ with the $N(n)$ cylinders of length $n$ (where $N(n) \le C \lambda^n$) and diameter $3^{-n}$ gives:
$$\mathcal{H}^d(C(1, M)) \le \liminf_{n \to \infty} N(n) (3^{-n})^d \le \liminf_{n \to \infty} C (3^{\log_3 \lambda - d})^n = 0 \quad \text{for all } d > \log_3 \lambda.$$
Therefore, $\dim_H C(1, M) = \log_3 \lambda = \dim_{\text{growth}}(\lambda(P))$ identically. QED

### 2.3 Proof of Theorem 1 (family 2)

Take P = 1 - y^a + y^b with b = 2a (k arbitrary; M = 3^(2a k) - 3^(ak)
+ 1; the family {3^(2a) - 3^a + 1} is the case k = 1, a arbitrary --
note every element 3^n - 3^m + 1 with n = 2m arises, and scaling in k
gives all (n,m) = (2t, t)).

By Theorem 2 the constraint is y_r - y_(r-a) + y_(r-2a) in {0,1}. The
constraint only couples positions congruent mod a, so the digit stream
splits into a independent chains; on one chain, writing z_i for the
i-th element, the constraint is

    z_i - z_(i-1) + z_(i-2) in {0,1},   z_i = 0 for i < 0.

Counting: a word z_0..z_(N-1) is admissible iff its "flip set"
S = { i : z_i != z_(i-1) } contains no two consecutive integers (the
constraint forbids exactly the patterns 010 and 101 in z, i.e. adjacent
flips), and S determines z. Hence N(N) = F_(N+2) per chain. Over a
length-n block scale with k columns... total count = F_(n+2)^k as
claimed, and the growth per ternary digit is phi, so

    dim_H C(1,M_k) = log_3 phi.   QED

(Equivalently for k = a = 1: the M = 7 automaton has characteristic
polynomial (x^2 - x - 1)(x^2 - x + 1), Perron root phi.)

**Remark on Growth Rate Conventions (Per-Column vs. Per-Total-Digit):**
There are two natural ways to measure growth in product SFTs:
1. *Per-column growth rate:* $\lambda_{\text{col}} = \lim_{L \to \infty} N_{\text{col}}(L)^{1/L}$, measuring growth per symbol within a single column of length $L = N/k$.
2. *Per-total-digit growth rate:* $\lambda_{\text{tot}} = \lim_{N \to \infty} N_{\text{tot}}(N)^{1/N}$, where total count across $k$ independent columns satisfies $N_{\text{tot}}(N) = (N_{\text{col}}(N/k))^k$.
Because $(N_{\text{col}}(N/k))^k \approx (\lambda_{\text{col}}^{N/k})^k = \lambda_{\text{col}}^N$, the two conventions coincide identically: $\lambda_{\text{tot}} = \lambda_{\text{col}} = \lambda$.
Specifically, for Family 1 ($M = 3^a + 1$), $Mx \in \Sigma$ requires $x_i + x_{i-a} \le 1$. The digit stream splits into $a$ connected components (residue classes mod $a$), each of length $\approx N/a$. Each component is a golden-mean no-adjacent-1s SFT with count $F_{N/a+2} \approx \phi^{N/a}$. The total word count is $(F_{N/a+2})^a \approx (\phi^{N/a})^a = \phi^N$. Hence the per-column growth rate $\phi$ and the per-total-digit growth rate $\phi$ are identical, both giving $\dim_H C(1, M) = \log_3 \phi$.
Throughout this paper and `ErdosTernary/CantorMultiplier.lean`, $\text{perron\_root}$ denotes this invariant single-column / per-digit growth rate $\lambda$.

### 2.4 Proof of Theorem 4 (Extremality and Dimension Bounds)

By Theorem 2, the Hausdorff dimension $\dim_H C(1, M)$ equals the single-column
growth-rate dimension $\dim_{\text{growth}}(\lambda) = \log_3(\lambda(P))$.
In `ErdosTernary/CantorMultiplier.lean`:
- Attainment: Family 1 ($M = 3^a + 1$) splits into $a$ independent no-adjacent-1s chains,
  each with count $F_{L+2}$ and Perron root $\phi$ (`family1_attains_perron_root`, `family1_attains_log3phi`), giving $\dim_{\text{growth}} = \log_3 \phi$.
- Attainment: Family 2 with $b = 2a$ ($M = 3^{2a} - 3^a + 1$) reduces to coprime parameters
  $(1, 2)$ (`family2_extremizer_iff_reduced_one_two`), with exact Fibonacci count $F_{L+2}$
  per chain (`family2_extremizer_attains_perron_root`, `family2_extremizer_attains_log3phi`), giving $\dim_{\text{growth}} = \log_3 \phi$.
- Universal bound: For all 3-power-free safe multipliers $M > 1$, the single-column Perron root
  is bound to the multiplier structure and satisfies $\text{perron\_root}(sm) \le \phi$, proving $\dim_{\text{growth}}(\text{perron\_root } sm) \le \log_3 \phi < 1/2$
  (`safe_class_dimension_upper_bound`).
- Strictness for $a = 1, b \ge 3$: The Perron polynomial strictly satisfies $P_b(1) < 0 < P_b(\phi)$
  (`family2_reduced_a1_strict`), proving $\dim_{\text{growth}} < \log_3 \phi$ strictly.
- Extremizer classification: The maximal dimension $\log_3 \phi$ is attained if and only if
  $M$ is an extremizer in the safe class:
  - Equality $\dim_{\text{growth}} = \log_3 \phi$ holds for Family 1 and Family 2 with $b = 2a$.
  - Strict inequality $\dim_{\text{growth}} < \log_3 \phi$ holds for all other coprime pairs:
    1. For $a = 1, b \ge 3$: proved algebraically by `family2_reduced_a1_strict` ($P_b(\phi) > 0$).
    2. For $b - a = 1, a \ge 2$: strictly sub-golden via the inversion symmetry $\lambda(a, a+1) = \lambda(1, a+1) < \phi$.
    3. For the interior domain $a \ge 2, b - a \ge 2$: proved analytically via the cylinder slack identity $\lim_{n \to \infty} \frac{N(n-1) - B(n)}{N(n-1)} = 1 + \lambda - \lambda^2 \ge \mu([w_*]) > 0$ and the periodic point obstruction $|\text{Fix}(\sigma^b)| = 2 < L_b$; in Lean 4, `safe_class_extremizer_classification` and `safe_class_dimension_extremizer_classification` explicitly take Frontier A (`h_gap`) to verify the headline equivalence.

### 2.5 Proof of Lemma 4.1 (the chain lemma)

By Theorems 2 and 3 it remains to bound the chain SFTs of Lemma 4.1.
Fix coprime 1 <= a < b, write g := b - a, set z_i := 0 for i < 0,
let A_n be the admissible words z_0...z_(n-1) (all constraints i < n
satisfied) and N(n) := |A_n|.

Step 0 (growth). Appending position n to u in A_n, the new constraint
z_n - z_(n-a) + z_(n-b) in {0,1} admits both values of z_n exactly
when z_(n-a) = z_(n-b) (position n is *free*), and exactly one value
otherwise (forced z_n = z_(n-a)). Hence

    N(n+1) = N(n) + B(n),   B(n) := #{u in A_n : z_(n-a) = z_(n-b)}.

Consequently the Fibonacci bound

    (FB)   B(n) <= N(n-1)   for all n >= a

implies lambda(a,b) <= phi: N(n+1) <= N(n) + N(n-1) for all n >= a,
giving N(n) <= 2^(a-1) F_(n-a+2) by induction from the finite bases
at n = a, a-1.

Step 1 (two structural reductions).

  (a) Scaling: positions decompose into gcd(a,b) residue classes,
      each an identical chain with parameters (a/gcd, b/gcd) coprime;
      growth is unchanged (per-digit growth equals per-chain growth).
  (b) Isomorphism: (a,b) and (b-a, b) give conjugate SFTs (z_i ->
      1 - z_i relabeling preserves the constraint), so lambda(a,b) =
      lambda(b-a,b); e.g. lambda(1,3) = lambda(2,3).

So assume gcd(a,b) = 1.

Step 2 (a = 1). For w in A_n free at n means z_(n-1) = z_(n-b); the
right side is fixed by the prefix w[0..n-2], so over each prefix at
most one free word exists: B(n) <= N(n-1) for every n, giving (FB)
with n0 = 1. Equality in the growth exponent forces b = 2: for b >= 3
lambda(1,b) is the Perron root of the exact b-state charpoly (table
at the end of this section), strictly below phi.

Step 3 (finite bases). For n <= a every constraint i < n has both
offsets out of range, so A_n = {0,1}^n and N(n) = 2^n. For n < a the
new position n also has both offsets out of range, so B(n) = N(n) =
2^n > N(n-1): (FB) fails exactly on n < a (a fixed prefix, absorbed by
the constant), holds at n = a with equality: position a is free iff
z_0 = z_(a-b) = 0, so B(a) = 2^(a-1) = N(a-1).

Step 4 (exact reformulation of the crux). Let n >= a+1, j := n - a
(so 1 <= j <= n-2), classify u in A_(n-1) by the pair (c_(j-1), c_j)
with counts N_00, N_01, N_10, N_11, where c_m(u) := z_m XOR z_(m-g).
Then:

  (i)  every u in A_(n-1) extends to length n: take z_(n-1) :=
       z_(n-1-a); the new constraint then equals z_(n-1-b) in {0,1};
  (ii) that extension is free iff c_(j-1)(u) = 0, since the offsets
       of position n-1 are (n-1-a, n-1-b) = (j-1, j-1-g);
  (iii) position n of a length-n word w depends only on u = w|_(n-1):
       it is free iff c_j(u) = 0 (offsets (n-a, n-b) = (j, j-g));
  (iv) counting words over each u (one or two copies by (ii)) that are
       free at n (by (iii)) gives the exact identity

       B(n) = 2*N_00 + N_10.

  Since N(n-1) = N_00+N_01+N_10+N_11, (FB) at n is equivalent to

       N_00 <= N_01 + N_11.                                      (crux)

Step 5 (bijection). Let phi be the flip of position j, an involution
of {0,1}^(n-1). It preserves c_(j-1) and toggles c_j, so it exchanges
the class pairs (0,0)<->(0,1) and (1,0)<->(1,1). Under phi only
constraint j of a word can be destroyed: the constraint list reads z_j
directly at index j, while the indices that see z_j as an offset are
j+a = n and j+b > n, both outside the constraint range [0, n-1) of a
length-(n-1) word. Put

    E  = {u in N_00 : phi(u) notin A_(n-1)},
    E' = {v in N_01 : phi(v) notin A_(n-1)}.

Then phi restricts to a bijection N_00 \ E <-> N_01 \ E' (u admissible
iff phi(u) admissible, as phi is an involution and only constraint j
is at stake). Hence N_00 - |E| = |N_01| - |E'|, and (crux) becomes

    |E| <= |E'| + N_11 =: |Z'|.                                   (H)

Step 6 (proof of key combinatorial lemma H and closure of induction).
With L := n-1 and k := j = L - a + 1, the obligation |E_L^{(k)}| <= |Z'_L^{(k)}|
is proved uniformly by the telescoping induction:

    |E_L^{(k)}| - |Z'_L^{(k)}| = (|E_{k+1}^{(k)}| - |Z'_{k+1}^{(k)}|) + sum_{m=k+1}^{L-1} Delta_m(L - m + 1).

1. Leaf window tii-H at length k+1 (|E_{k+1}^{(k)}| <= |Z'_{k+1}^{(k)}|):
   Under projection u = (w, x) -> w in A_k, the leaf condition factors
   over 7 disjoint parameter regimes:
   - Regime 1 (k < g): E = empty.
   - Regime 2 (g = 1): flip_(k-1) : E -> Z1 (0 exceptions).
   - Regime 3 (2 <= g < a): flip_(k-g) : E -> Z2 (0 exceptions).
   - Regime 4 (g > a, g <= k < b): flip_(k-g) : E -> Z2 (0 exceptions).
   - Regime 5 (g = a+1, k >= b): flip_(k-g) on non-exc -> Z2,
     flip_{k-g, k-1} on exc -> Z1 (0 exceptions).
   - Regime 6 (a+1 < g < 2a, k >= b): 5 touched constraints
     {1, g-a, g+1-a, g, g+1}.
     * Sub-regime 6a (a+1 < g < 2a-1, 13 variables): exactly 48 valid exception
       configurations (`config_count_6a`, Lean decide in `ErdosTernary/Lemma41Finite.lean`),
       per-rule counts SA: 36/48, SB1: 24/48, SB2: 24/48, 100% covered (`exc_covered_6a`),
       default branch unreachable (`zero_not_isExc6a`), and images pairwise disjoint (`images_injective_6a`).
     * Sub-regime 6b (g = 2a-1, 12 variables): exactly 24 valid exception
       configurations (`config_count_6b`, Lean decide in `ErdosTernary/Lemma41Finite.lean`),
       per-rule counts SA: 18/24, SB1: 12/24, SB2: 12/24, 100% covered (`exc_covered_6b`),
       default branch unreachable (`zero_not_isExc6b`), and images pairwise disjoint (`images_injective_6b`).
   - Regime 7 (g > 2a, k >= b): Domino Chain + 5-region signature-disjoint
     fixed-involution injection (0 unmapped, 0 collisions).

2. Delta negativity for delta >= 2 (Delta(delta) <= -1 < 0):
   Each step delta_m = L - m + 1 in [2, a-1] satisfies Delta(delta_m) <= -1.
   The universal witness w_* = e_(k-1) (g=1) or e_(k-1) + e_k (g>=2) belongs to
   Z1_free \ Phi(E_free), proving strict negativity Delta(delta) <= -1 < 0
   for all delta >= 2.
   Moreover, the exception routing in Delta is bounded-variable (N <= 13), fully formalized in `ErdosTernary/Lemma41Finite.lean`:
   - 92.9% of words (18,451 / 19,867) fall into 5 closed-form exception-free regimes;
   - Case 1 (delta = g, 4 constraints, N <= 13 vars): all 9 coprime coincidence types
     (3,2), (4,3), (5,2), (5,3), (7,2), (7,3), (7,5), (8,3), (12,5) are 100% covered and injective
     (`config_count_dg_*`, `exc_covered_dg_*`, `zero_not_isExc_dg_*`, `images_injective_dg_*`);
   - Case 2 (2 <= delta < g, 1 <= g-delta < a, 5 constraints, N <= 13 vars): generic sub-case
     is an exact literal translation identity with tii-H Lemma C.4 (`translation_identity_delta_generic`, proved by `rfl`);
     non-generic coincidence types g = a-1 (N=11, C=8), 2g = a+1 (N=12, C=24), and g = a+1 (N=10, C=12) are proved 100% covered and injective
     (`images_injective_case2_g_eq_a_minus_1`, `images_injective_case2_2g_eq_a_plus_1`, `images_injective_case2_g_eq_a_plus_1`);
     coincidence type g = 2a-1 is proved algebraically empty;
   - Case 3 (2 <= delta < g, g-delta >= a, 25 words): 100% covered by S_I or S_IIIb
     with 0 unmapped (`exc_case3_zero`, Lean decide).

3. Telescoping conclusion:
   For a = 2: k = L - 1, sum is empty, B(n) - N(n-1) <= 0 directly by tii-H.
   For a >= 3: B(n) - N(n-1) <= 0 + sum_{delta=2}^{a-1} (-1) = -(a-2) <= -1 < 0.
   Together with Step 3 (B(a) = N(a-1)), this establishes (FB) B(n) <= N(n-1)
   for all n >= a, proving lambda(a,b) <= phi unconditionally. QED

Step 7 (strictness and transfer matrix). By bit-complement symmetry
(w <-> ~w) of the bulk constraint and anchor predicates, the state
evolution factors through the 2^(b-1)-dimensional symmetric subspace M_+,
bounding the recurrence order by d <= 2^(b-1); exact square-free
factorization over ZZ[x] (sqf_list) determines root multiplicities
algebraically. All 34/34 coprime pairs with b <= 12 are fully certified
(orders d up to 2048; examples (2,11): d=56, rho1=1.270748 > rmax=1.177257,
L*=11; (7,11): d=968, sqf [(530,1),(219,2)], rho1=1.367855 > rmax=1.305647,
L*=730; (7,12): d=1816, rho1=1.379634 > rmax=1.357297, L*=1449; (11,12):
d=2048, rho1=1.379301 > rmax=1.359622, L*=1603; all verified through
N=2200-4500).

Step 8 (conclusion). Steps 2-6 establish (FB) for all n >= a (Step 3
covers the fixed prefix n < a), hence N(n+1) <= N(n) + N(n-1) for all n >= a
and lambda(a,b) <= phi universally, fully instantiated in `ErdosTernary/Lemma41.lean`
(`lemma_4_1`, `lemma_4_1_chain`, `lemma_4_1_growth_bound`).
Extremizer classification:
(i) For (a,b) = (1,2), the anchor recurrence is exact at all n >= 1, giving exact
    equality N(1,2,n) = F_{n+2} (`extremizer_exact_fibonacci`) and lambda(1,2) = phi.
(ii) Boundary Case 1 (a = 1, b >= 3) [Lean-verified]:
    The Perron polynomial P_b(x) = x^b - x^{b-1} - 1 divides the characteristic polynomial
    with P_b(1) < 0 < P_b(phi) = phi^{b-2} - 1 (`perronPoly_at_phi_pos`, `perronPoly_at_one` in `Lemma41.lean`),
    and the SFT slack establishes lambda(1,b) < phi strictly.
(iii) Boundary Case 2 (b - a = 1, a >= 2) [Lean-verified]:
    Proved via Time-Reversal Duality (Theorem 4.2 below): the bit-reversal involution P on {0, 1}^b
    satisfies the exact matrix transpose identity P M_{(a, b)} P = M_{(b-a, b)}^T.
    Consequently, det(x I - M_{(a, b)}) = det(x I - M_{(b-a, b)}) identically, so
    lambda(a, a+1) = lambda(1, a+1) < phi strictly.
    Formalized and verified by the Lean 4 kernel: `ErdosTernary/TimeReversal.lean` (`time_reversal_transition_duality`,
    `boundary_case2_reversal_to_boundary_case1`, `charpoly_time_reversal_invariance`, and
    `boundary_case2_charpoly_eq_boundary_case1`), built cleanly with 0 sorry and 0 custom axioms.
(iv) Interior Domain (a >= 2, b - a >= 2) [Prose-proved; Lean discrete dynamics verified]:
    Proved in prose via the Parry measure theorem on the universal 2b-periodic orbit
    (Lean formalization modular interface `h_gap`).
    The discrete dynamical foundations of this step are kernel-verified in `ErdosTernary/PeriodicOrbit.lean`
    (0 sorry, 0 custom axioms):
    - Mutual reachability: 0^b <-> 1^b in b steps (`reachable_zero_to_one`, `reachable_one_to_zero`), placing them in the exact same SCC (`zero_and_one_in_same_scc`).
    - Primitivity: 0^b self-loop establishes period 1 aperiodicity (`recurrent_component_has_period_one`).
    - Universal 2b-periodic sequence: z_i = 1_{(i mod 2b) >= b} satisfies z_{i-b} = ! z_i, yielding z_i - z_{i-a} + z_{i-b} = 1 - z_{i-a} in {0,1} at every i in Z (`periodicSeq_constraint`).
    - Witness embedding: both witness words w_* (0^b 1 and 0^{b-1} 1 1) occur as exact contiguous subwords of the periodic sequence (`witness_g_eq_1_occurs`, `witness_g_ge_2_occurs`).

    Status Summary across Non-Extremizers:
    - a = 1: Lean-verified (`Lemma41.lean`).
    - b - a = 1: Lean-verified (`TimeReversal.lean`).
    - b - a >= 2: Discrete orbit & component primitivity Lean-verified (`PeriodicOrbit.lean`); measure limit conditional on `h_gap`.

    Theorem 4.2 (Time-Reversal Duality of Chain SFT Transfer Matrices).
    Let 1 <= a < b and let M_{(a, b)} be the 2^b x 2^b transition matrix of the chain SFT Sigma_{(a, b)}.
    Let P be the permutation matrix representing the bit-reversal involution on {0, 1}^b: (P u)_j = u_{b-1-j}.
    Then:
        P M_{(a, b)} P = M_{(b-a, b)}^T.
    Proof. A transition u -> v in M_{(a, b)} satisfies v_k = u_{k+1} for 0 <= k < b-1 and
    0 <= v_{b-1} - u_{b-a} + u_0 <= 1. Under state reversal (P u)_j = u_{b-1-j} and (P v)_j = v_{b-1-j},
    the shift condition becomes u_j = v_{j+1} for 0 <= j < b-1 (a reverse shift from v to u), while the
    boundary condition becomes 0 <= v_0 - v_a + u_{b-1} <= 1. Viewing v -> u as a forward transition,
    the newly appended bit is u_{b-1} (delay 0, coefficient +1), the bit at delay b - a is v_a = u_{a-1}
    (coefficient -1), and the bit at delay b is v_0 (coefficient +1). This is precisely the defining
    transition condition for M_{(b-a, b)}. Hence (P M_{(a, b)} P)_{u, v} = (M_{(b-a, b)})_{v, u} = (M_{(b-a, b)}^T)_{u, v}.
    Taking determinants, det(x I - M_{(b-a, b)}) = det(x I - M_{(b-a, b)}^T) = det(x I - P M_{(a, b)} P) = det(x I - M_{(a, b)}).
    Thus M_{(a, b)} and M_{(b-a, b)} share the exact same characteristic polynomial, eigenvalues, and spectral radius:
        lambda(a, b) = lambda(b - a, b)   for all 1 <= a < b.
    In particular, for b - a = 1, lambda(a, a+1) = lambda(1, a+1) < phi strictly.

    Correction of Prior P_6 Divergence Claim:
    Earlier exploratory checks conjectured that lambda(5, 6) might diverge from lambda(1, 6) because
    the factor P_6(x) = x^6 - x^5 - 1 has root 1.285199, whereas the dominant root of M_{(5, 6)} is 1.370957.
    Exact SymPy calculation of the full 64 x 64 characteristic polynomials proves that charpoly(M_{(1, 6)})
    equals charpoly(M_{(5, 6)}) identically. P_6 is merely one irreducible factor of charpoly; the dominant
    spectral root is carried by an irreducible factor of degree 20 in both matrices, confirming exact
    spectral invariance across all pairs.

    Step 8.1 (Universal Periodic Extension of the Witness Cylinder).
    In Lemma 4.1 Step 6 (certified in `ErdosTernary/Lemma41Finite.lean`), the crux slack set
    at length L = b + 1 is Z'_L \ Phi(E_L). For g >= 2, the witness word is w_* = 0^{b-1} 1 1;
    for g = 1, w_* = 0^b 1. To establish that [w_*] has strictly positive Parry measure in
    Sigma_{(a, b)}, it suffices to embed w_* into a recurrent periodic orbit of Sigma_{(a, b)}.
    Consider the 2b-periodic binary sequence z : ZZ -> {0, 1} defined by:
        z_i = 0  if (i mod 2b) < b,   and   z_i = 1  if (i mod 2b) >= b.
    Because the period is 2b, translating by b swaps the zero-block and ones-block, so
    z_{i-b} = 1 - z_i identically for all i in ZZ.
    Consequently:
        z_i - z_{i-a} + z_{i-b} = z_i - z_{i-a} + (1 - z_i) = 1 - z_{i-a}.
    Since z is binary, z_{i-a} in {0, 1}, which guarantees 1 - z_{i-a} in {0, 1} subset [0, 1]
    identically for all i in ZZ without exception.
    The sequence z is thus an admissible periodic orbit of period 2b in Sigma_{(a, b)}.
    At the transition boundary between 0^b and 1^b, z contains the subword 0^b 1^b.
    Both witness words w_* = 0^{b-1} 1 1 (for g >= 2) and w_* = 0^b 1 (for g = 1) occur
    as exact subwords of 0^b 1^b. Because z is periodic and visits the self-loop states 0^b and 1^b,
    it lies entirely within the maximal recurrent component R of Sigma_{(a, b)}.
    This rigorously embeds [w_*] into the recurrent core of the shift with zero case distinctions.

    Step 8.2 (Primitivity and Full Support of the Parry Measure).
    Let R be the maximal irreducible component of Sigma_{(a, b)} carrying the topological entropy log lambda.
    Because the all-zero state 0^b and all-ones state 1^b have self-loops (cycle length 1), the transition
    graph on R is aperiodic. The heteroclinic trajectories established in Step 8.1 connect 0^b and 1^b,
    guaranteeing that R is strongly connected and aperiodic, hence primitive.
    By the Perron-Frobenius theorem for primitive non-negative matrices, there exist strictly positive
    left and right eigenvectors v > 0, u > 0 corresponding to the simple dominant eigenvalue lambda.
    The unique Parry measure of maximal entropy mu on R assigns strictly positive probability to every
    admissible cylinder set:
        mu([w_*]) = epsilon(a, b) > 0.

    Step 8.3 (Ergodic Measure Convergence to Relative Slack).
    From the word-extension relation N(L) = N(L-1) + B(L-1), we have B(L) = N(L+1) - N(L).
    Under dominant eigenvalue asymptotics N(L) = c lambda^L + o(lambda^L) with c > 0, lambda > 1:
        B(L) = c (lambda - 1) lambda^L + o(lambda^L),
    which gives B(L)/N(L) -> lambda - 1 and B(L)/N(L-1) -> lambda^2 - lambda.
    Therefore, the relative defect in the Fibonacci recurrence satisfies the exact algebraic identity:
        lim_{L -> infty} (N(L-1) - B(L)) / N(L-1) = 1 - (lambda^2 - lambda) = 1 + lambda - lambda^2.
    Because every prefix word in A_{L-1} ending with the witness block w_* belongs to the crux slack set
    Z'_L \ Phi(E_L), the Shannon-McMillan-Breiman ergodic theorem on (R, mu) yields:
        liminf_{L -> infty} (N(L-1) - B(L)) / N(L-1) >= lim_{L -> infty} |{ w in A_{L-1} : w ends with w_* }| / N(L-1)
                                                      = mu([w_*]) = epsilon(a, b) > 0.

    Step 8.4 (Spectral Gap Extraction).
    Combining Steps 8.2 and 8.3 yields the strict quadratic inequality:
        1 + lambda - lambda^2 >= epsilon(a, b) > 0.
    The golden quadratic g(x) = 1 + x - x^2 satisfies g(phi) = 1 + phi - phi^2 = 0, and has derivative
    g'(x) = 1 - 2x < 0 strictly for all x >= 1, with g'(phi) = 1 - 2 phi = -sqrt(5).
    By strict monotonicity on [1, infty):
        g(lambda) >= epsilon(a, b) > 0 = g(phi)  ===>  lambda(a, b) < phi  strictly.
    Moreover, the mean value theorem provides the explicit, quantitative uniform spectral gap:
        phi - lambda(a, b) >= epsilon(a, b) / sqrt(5) > 0.
    This completes the proof of strictness for all non-extremizers with a >= 2.

    Topological Orbit Obstruction (Corroborating Structural Invariant):
    Independently of measure theory, any b-periodic sequence satisfies z_{i-b} = z_i, collapsing
    the constraint to 2 z_i - z_{i-a} in {0,1}, which forces z_{i-a} = z_i. Since gcd(a,b) = 1,
    the period divides 1, so |Fix(sigma^b)| = 2 identically (0^infty and 1^infty)
    (`periodic_points_at_b_constant` in `ErdosTernary/Lemma41.lean`). For b >= 3,
    this strictly misses the golden-mean Lucas count L_b = phi^b + (-1/phi)^b >= 4, providing an independent
    topological proof that Sigma_{(a,b)} cannot be conjugate to the golden-mean shift.

    Computational Certification:
    All 34 certified transfer matrix pairs (d <= 2048, b <= 12) and all 114 pairs tested up to b <= 22
    have spectral radius strictly below phi (tightest gap 0.208799 at (2,5), lambda = 1.409235).

    Formalization Roadmap in Lean 4:
    In Lean 4, `ErdosTernary/Lemma41.lean` formalizes `lambda_lt_phi_of_positive_slack`
    and `periodic_points_at_b_constant`. `ErdosTernary/CantorMultiplier.lean` formulates
    the headline classification theorems `safe_class_extremizer_classification` and
    `safe_class_dimension_extremizer_classification` conditioned on `h_gap`.
    Discharging `h_gap` internally in Lean represents a substantial future Mathlib formalization
    project in topological Markov chains and ergodic theory:
    (1) Perron-Frobenius theorem for primitive non-negative matrices (`IsPrimitive M → ∃ v > 0, M v = λ v`),
    (2) Parry measure construction for SFTs (Markov measure weighted by left/right PF eigenvectors),
    (3) Birkhoff ergodic theorem for cylinder asymptotic densities,
    (4) Embedding of the universal 2b-periodic orbit into the recurrent component.
    The paper's complete formalization status is therefore "Lean-verified modulo `h_gap`", where
    `h_gap` isolates this general SFT ergodic theory composite from the arithmetic multiplier classification.

Exact eigenvalues computed by `x2p_third_family.py`; characteristic
polynomials (new dimensions):

  lambda(1,3) = lambda(2,3): root of x^3 - x^2 - 1  (= 1.4655712...),
      dim C(1, 3^3-3^1+1) = dim C(1,25) = dim C(1,19) = 0.347934471317;
  lambda(1,4) = lambda(3,4): root of x^4 - x^3 - 1  (= 1.3802775...),
      dim C(1,79) = dim C(1,55) = 0.293356099595;
  lambda(2,5) = lambda(3,5): d=11/d=15 Perron root  (= 1.409235234958..., gap 0.208799),
      dim C(1,235) = dim C(1,217) = 0.312254991346;
  lambda(1,5) = lambda(4,5): root of x^3 - x - 1     (plastic),
      dim C(1,241) = dim C(1,163) = 0.255958883059;
each giving an infinite arithmetic progression of exact dimensions
(M = 3^b - 3^a + 1 with gcd(a,b) fixed, k-th powers scaled).

---

## 3. Verification map

| claim | machine check | file |
|---|---|---|
| Thm 1 counts F_(n+2)^k | exact, k <= 3, n <= 11 | x2p_family2_proof.py |
| Thm 2 Lemmas 1-3 | exhaustive, k <= 4 | x2p_family2_proof.py |
| Thm 3 classification | exhaustive, degree <= 7 | x2p_third_family.py (S1), ErdosTernary/CantorMultiplier.lean |
| Thm 4 dimension bound & extremizers | formal bridge dim_growth <= log_3 phi; equality iff extremal safe M | ErdosTernary/CantorMultiplier.lean |
| Thm 4.2 Time-Reversal Duality | P M_{(a,b)} P = M_{(b-a,b)}^T; b-a=1 reduction to a=1 | ErdosTernary/TimeReversal.lean (Lean-verified: 0 sorry, 0 custom axioms), SymPy |
| Thm 4.3 Periodic Orbit & SFT Primitivity | 0^b <-> 1^b reachability, period 1, universal 2b-periodic orbit & witness embedding | ErdosTernary/PeriodicOrbit.lean (Lean-verified: 0 sorry, 0 custom axioms) |
| Lemma 4.1 Steps 0,4,5 (growth, crux identities, bijection) | exact, a<8, b<10, n<16 | lemma41_check.py |
| Lemma 4.1 Step 6 (H injection) | 957/957 instances, L<17; spot checks L in [17,20] | lemma41_hinject.py |
| Lemma 4.1 Step 6 (tii-H leaf + Domino Chain + 48/24-config 5-constraint lemma) | 736/736 instances across 7 disjoint regimes, 0 unmapped, 0 collisions; 48/48 (13 vars, g<2a-1) & 24/24 (12 vars, g=2a-1) symbolic configs | lemma41_tii_proof.py, ErdosTernary/Lemma41Finite.lean |
| Lemma 4.1 Step 6 (Delta negativity for delta>=2 + strictness witness w_*) | 1139/1139 instances, 0 unmapped, 0 collisions; explicit witness w_* in Z1_free \ Phi(E_free) on 1139/1139; 9 Case 1 + Case 2/3 symbolic lemmas | lemma41_delta_proof.py, ErdosTernary/Lemma41Finite.lean |
| Lemma 4.1 finite bases (Step 3) | B(n)<=N(n-1) for n>=a, 28 configs, n<=19 | session cert, phase3-bridge.md |
| Lemma 4.1 Step 7 (h_L transfer matrix: positivity + recurrence + tail) | 34/34 pairs b<=12 fully PASS (d<=2048, exact ZZ[x] sqf + M_+, L*<=1603, exact verified through N=2200-4500) | lemma41_transfer.py cert2 |
| Lemma 4.1 inequality (Step 7, eigenvalues) | exact eigenvalues, all coprime a<b<=17, partial to 22 (tightest non-eq. gap 0.208799 at (2,5)); equality only (1,2) | x2p_outside_hunt.py, ErdosTernary/Lemma41.lean |
| Table, Thm 1.6 check | M <= 300 exact/numeric | x2p_dim_table.py |
| phi-max conjecture | all 3-power-free M <= 20000 (6666 primitives), attainers exactly the safe equality forms | x2p_outside_hunt.py |
