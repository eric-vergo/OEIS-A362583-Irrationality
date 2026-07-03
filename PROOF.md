# PROOF.md — Informal source of truth

> **This document is the informal source of truth for the formalization.**
> It transcribes §2 of the project specification
> (`a362583-lean-irrationality-spec.md`, prime_race repo, 2026-07-03) verbatim in
> mathematical content. **Every lemma in the Lean code must cite its label from
> this document** (A, B1–B5, C, D0a–D0d, D1–D4, case c ≠ 0 steps 1–3, §2.7).
> If a mathematical gap is found here, stop and report — do not patch with
> axioms or weaken statements silently.

---

## 2. The proof to formalize (complete informal argument)

### 2.1 Route decision — read this before questioning the architecture

The obvious proofs of irrationality run through either (i) Littlewood 1914: $\pi(y;4,3) - \pi(y;4,1) = \Omega_\pm(\sqrt y \log\log\log y / \log y)$, or (ii) Shiu 2000 / Banks–Freiberg–Maynard: arbitrarily long runs of consecutive primes in a fixed class mod 4. Both are far beyond feasible formalization (explicit formula / Maier matrices / multidimensional sieve; none of it in or near Mathlib).

Neither is needed. Eventual periodicity of $(b_k)$ implies the very rigid statement $S(y) = c\,\pi(y) + O(1)$ for a rational constant $c$. Refuting **that** requires only mere *non-degeneracy* of the race, not quantitative oscillation, and non-degeneracy has the self-contained proof in Step D below. Its only nontrivial imports are: analytic continuation of $L(s,\chi_4)$, $L(1,\chi_4)\ne 0$, Euler products, $\sum 1/p = \infty$, and the identity theorem — all in current Mathlib. **No PNT, no PNT-in-APs, no zero-free regions, no functional equation.**

Provenance note: Steps A–C are standard. Step D is the classical "prime-square term" mechanism behind $\Omega$-results for real characters (cf. Montgomery–Vaughan Ch. 15 territory), specialized to the weakest usable statement and assembled for this project. Estimated soundness ≈95%. **Phase 0 mandates an independent re-derivation before coding.**

### 2.2 Theorem

**Theorem.** $x \notin \mathbb{Q}$.

Proof structure: A (infinitude) → B (rational ⇒ bits eventually periodic) → C (periodic ⇒ linear race) → D (no linear race) → contradiction.

### 2.3 Step A — both residue classes are infinite

**(A)** There are infinitely many primes $\equiv 1 \pmod 4$ and infinitely many $\equiv 3 \pmod 4$. (Mathlib: Dirichlet's theorem, or the elementary special cases which Mathlib also has in some form.) Hence $(b_k)$ contains infinitely many $0$s and infinitely many $1$s.

### 2.4 Step B — rational ⇒ eventually periodic bits

Define tails $t_k := \sum_{j > k} b_j 2^{k-j}$ for $k \ge 0$ (so $t_0 = x$). Then:

1. **(B1)** $t_k \in (0,1)$ strictly, for every $k$ — infinitely many later $1$s gives $t_k > 0$; infinitely many later $0$s gives $t_k < 1$. (Uses Step A.)
2. **(B2)** Recurrence: $t_k = (b_{k+1} + t_{k+1})/2$. Consequences, given (B1): if $b_{k+1} = 1$ then $t_k \in (1/2, 1)$; if $b_{k+1} = 0$ then $t_k \in (0, 1/2)$. In particular $t_k \ne 1/2$ always, and **$t_k$ determines $b_{k+1}$** ($b_{k+1} = 1 \iff t_k > 1/2$) **and hence $t_{k+1} = 2t_k - b_{k+1}$.**
3. **(B3)** $2^k x = (\text{integer}) + t_k$ with $t_k \in (0,1)$, so $t_k = \operatorname{fract}(2^k x)$.
4. **(B4)** If $x = a/b$ with $b \ge 1$, then $t_k = \operatorname{fract}(2^k a / b) \in \{0, 1/b, \ldots, (b-1)/b\}$ — finitely many values. Pigeonhole: $\exists\, m < n$ with $t_m = t_n$.
5. **(B5)** By (B2) and induction, $t_{m+i} = t_{n+i}$ and $b_{m+i} = b_{n+i}$ for all $i \ge 1$. So $(b_k)$ is eventually periodic with period $P = n - m$ from index $m+1$.

Note this **dodges general digit-expansion theory entirely** — no need for a rational ⟺ periodic-digits library (which Mathlib likely lacks; audit item M14).

### 2.5 Step C — eventually periodic ⇒ linear race

**(C)** Suppose $b_{k+P} = b_k$ for all $k \ge N$, with $j$ ones among $b_N, \ldots, b_{N+P-1}$. Then for $m \ge N$:

$$\#\{k \le m : b_k = 1\} = \tfrac{j}{P}\, m + O_{N,P}(1),$$

hence $\sum_{k \le m} \chi(p_k) = m - 2\#\{\text{ones} \le m\} = c\,m + O(1)$ with $c = (P - 2j)/P \in [-1,1] \cap \mathbb{Q}$.

For any $y \ge 3$, with $m = \pi(y) - 1$ (number of odd primes $\le y$): $S(y) = \sum_{k \le m} \chi(p_k)$, so

$$S(y) = c\,\pi(y) + O(1).$$

(All-ones and all-zeros patterns are just $c = -1$ and $c = +1$; no separate case needed.)

Bookkeeping burden: translating between "$k$-th odd prime" (`Nat.nth`) and "primes $\le y$" (`Nat.primeCounting` / `Nat.count`). Mathlib's `nth`/`count` Galois connection covers this (audit item M7).

### 2.6 Step D — the race is never linear (main analytic theorem)

**Theorem (raceSum_not_linear).** There do not exist $c \in \mathbb{R}$, $C \ge 0$ with $|S(y) - c\,\pi(y)| \le C$ for all $y$.

Throughout, for a prime $p$ and $\mathrm{Re}\,s > 0$: $|\chi(p)p^{-s}| \le 2^{-\mathrm{Re}\,s} < 1$, so $-\log(1 - \chi(p)p^{-s}) = \sum_{k \ge 1} \chi(p)^k p^{-ks}/k$ is valid termwise. Define the three pieces (whenever they converge):

- $A(s) := \sum_p \chi(p)\, p^{-s}$  (the $k=1$ layer)
- $B(s) := \tfrac12 \sum_p \chi(p)^2\, p^{-2s} = \tfrac12 \sum_{p \text{ odd}} p^{-2s}$  (the $k=2$ layer; $\chi(p)^2 = 1$ for odd $p$)
- $T(s) := \sum_p \sum_{k \ge 3} \chi(p)^k\, p^{-ks}/k$  (the $k \ge 3$ layer)

**Shared facts (no hypothesis needed):**

- **(D0a)** $B$ converges absolutely and is holomorphic on $\Omega := \{\mathrm{Re}\,s > 1/2\}$; for real $s \downarrow 1/2^+$, $B(s) \to +\infty$. *(Terms increase monotonically as $s$ decreases; for any $M$ pick a finite prime set with $\tfrac12\sum p^{-1} > 2M$, possible since $\sum_p 1/p = \infty$ — audit item M5.)*
- **(D0b)** $T$ converges absolutely and is holomorphic on $\Omega$, with a **uniform** bound there: $|T(s)| \le (1 - 2^{-1/2})^{-1} \sum_{n\ge2} n^{-3/2} =: K < \infty$, since $\sum_{k\ge3} p^{-k\sigma} \le p^{-3\sigma}(1-p^{-\sigma})^{-1}$ and $3\sigma > 3/2$.
- **(D0c)** For $\mathrm{Re}\,s > 1$ everything converges absolutely; rearrangement gives $\sum_p\bigl(-\log(1-\chi(p)p^{-s})\bigr) = A(s) + B(s) + T(s)$, and by the Euler product for Dirichlet L-series (audit item M4):
  $$\exp\bigl(A(s) + B(s) + T(s)\bigr) = L(s, \chi) \qquad (\mathrm{Re}\,s > 1).$$
- **(D0d)** $L := $ the analytically continued $L(\cdot, \chi_4)$ is entire ($\chi_4$ nonprincipal) and agrees with the Dirichlet series on $\mathrm{Re}\,s > 1$ (audit item M2). It is continuous with finite value at every point; $L(1,\chi_4) \ne 0$ (audit item M3; classically $L(1,\chi_4) = \pi/4$, but only nonvanishing is needed).

**Case $c \ne 0$.** Assume $|S(y) - c\,\pi(y)| \le C$. Work with real $s \in (1, 2]$, where $A$ and $P(s) := \sum_p p^{-s}$ converge absolutely.

1. **(c≠0 step 1)** Discrete Abel summation applied to coefficients $\chi(p) - c$ against weights $p^{-s}$ (bounded partial sums $|S(y) - c\pi(y)| \le C$; weights positive decreasing, telescoping) gives $|A(s) - c\,P(s)| \le 2C$ uniformly on $(1,2]$.
2. **(c≠0 step 2)** $P(s) \to +\infty$ as $s \downarrow 1$ (monotone limit; $\sum 1/p = \infty$). Hence $|A(s)| \to \infty$.
3. **(c≠0 step 3)** But for real $s > 1$ the Euler product is a product of positive reals, so (D0c) reads $A(s) = \log L(s,\chi) - B(s) - T(s)$, and as $s \downarrow 1$: $L(s,\chi) \to L(1,\chi) \ne 0$ so $\log L$ stays bounded; $B, T$ are continuous and finite at $1$. So $A(s)$ stays bounded. Contradiction. ∎

**Case $c = 0$.** Assume $|S(y)| \le C$ for all $y$.

1. **(D1)** $A$ converges on $\Omega$ and is holomorphic there, with the uniform real-segment bound $|A(s)| \le 3C$ for real $s \in (1/2, 2]$.
   *Convergence + bound:* discrete Abel/summation-by-parts: $\sum_{p \le Y}\chi(p)p^{-s} = S(Y)Y^{-s} + \sum_{n < Y} S(n)\,(n^{-s} - (n+1)^{-s})$; for real $s > 0$ the increments are positive and telescope to $\le 2^{-s}$, giving the bound and Cauchy convergence.
   *Holomorphy:* the finite partial sums are entire and converge **locally uniformly** on $\Omega$ (tail bound via the same summation-by-parts, using $|n^{-s} - (n+1)^{-s}| \le |s|\, n^{-\mathrm{Re}\,s - 1}$, a small lemma via FTC); a locally uniform limit of holomorphic functions is holomorphic (audit item M9). This is new-lemma N1 (§5).
2. **(D2)** $G := A + B + T$ is holomorphic on $\Omega$ (D1 + D0a + D0b), and $\exp(G) = L$ on $\{\mathrm{Re}\,s > 1\}$ (D0c, noting the Dirichlet series = $L$ there by D0d).
3. **(D3)** $\Omega$ is open, connected; $\exp\circ G$ and $L$ are both holomorphic on $\Omega$ and agree on the nonempty open subset $\{\mathrm{Re}\,s>1\}$. By the identity theorem (audit item M8): $\exp(G(s)) = L(s,\chi)$ **for all $s \in \Omega$**.
4. **(D4)** Take real $s \downarrow 1/2^+$: $\;|L(s,\chi)| = e^{\mathrm{Re}\,G(s)} \ge e^{B(s) - 3C - K} \to \infty$ by D0a. But $L$ is continuous at $1/2$ with a finite value (D0d). Contradiction. ∎

*(Sanity: the argument in Case $c=0$ shows bounded race ⇒ $\log L(s,\chi_4)$ continues past $\mathrm{Re}\,s = 1/2$ minus an explicit divergent term — the standard reason real characters cannot have an $O(1)$ race. If the Phase-0 re-derivation finds any gap, the most likely locations are: the locally-uniform tail bound in D1, and the rearrangement hygiene in D0c. Check those hardest.)*

### 2.7 Assembly

**(§2.7)** Suppose $x \in \mathbb{Q}$. Step B (using A) ⇒ bits eventually periodic ⇒ Step C ⇒ $S(y) = c\,\pi(y) + O(1)$ ⇒ contradicts Step D. Hence `Irrational x`. ∎

---

## Independent re-derivation (Phase 0b) — PENDING

*This section is a placeholder. Phase 0b requires an independent re-derivation of
Step D from scratch, checking especially D1's tail bound and D0c's rearrangement
hygiene, before any proof code is written. Any gap found ⇒ stop and report to Eric.*
