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

## Independent re-derivation (Phase 0b) — VERIFIED

> **Provenance.** Two mathematician agents independently derived Step D from the
> theorem statement plus the Available-facts list only (firewalled from §2.6):
> Derivation A (integral Abel summation, DCT-free) and Derivation B (integral
> Abel summation with a dominated-convergence truncation). A referee pass then
> adversarially checked A, B, and §2.6 against each other, attacking hardest at
> the spec's self-flagged weak points (D1's locally-uniform tail bound; D0c's
> rearrangement hygiene) and at branch handling of the complex logarithm.
> **Verdict: all three are sound; no mathematical gap found.** The two spec
> flags were independently verified (details below). The consolidated argument
> here is the variant recommended for formalization; deltas versus §2.6/A/B and
> route decisions follow it.

### Consolidated Step D (formalization-ready variant, cross-labeled to §2.6)

Assume, for contradiction, $c \in \mathbb{R}$, $C \ge 0$ with $|S(y) - c\,\pi(y)| \le C$ for all $y$. Since $S = \pi = 0$ for $y < 2$ and both are step functions jumping only at (integer) primes, the hypothesis is equivalent to its restriction to integers $\ge 2$ — this is also why the Lean statement over `N : ℕ` matches the informal "for all real $y$". Write $\sigma := \mathrm{Re}\,s$, $\Omega := \{\sigma > 1/2\}$, and $\mathrm{Log}$ for the principal complex logarithm.

**Lemma R1 (divergence transfer; supports D0a and both endgames).** Let $E$ be a set of primes with $\sum_{p \in E, p \le N} 1/p$ unbounded in $N$, and $a > 0$. Then $Q(u) := \sum_{p\in E} p^{-au}$ converges for real $u > 1/a$, and for every $M$ there is $\delta > 0$ with $Q(u) > M$ for all $u \in (1/a, 1/a + \delta)$.
*Proof.* Convergence by comparison with $\sum n^{-au}$, $au > 1$. Given $M$: pick $N$ with $\sum_{p\in E, p\le N} 1/p > M + 1$ (possible by hypothesis — the only use of M5); the finite sum $u \mapsto \sum_{p\in E, p\le N} p^{-au}$ is continuous and exceeds $M+1$ at $u = 1/a$, so it exceeds $M$ on some $(1/a, 1/a+\delta)$; positivity of the discarded terms gives $Q(u) \ge$ this finite sum. ∎
*Instances:* $a=1$, $E$ = all primes ($P(s) := \sum_p p^{-s}$); $a=2$, $E$ = odd primes ($\sum_{p \text{ odd}, p\le N} 1/p = \sum_{p\le N} 1/p - 1/2$, still unbounded), giving via $B(s) = \tfrac12 Q(2s)$: for every $M$ there is $\delta_B > 0$ with $B(s) > M$ on $(1/2, 1/2 + \delta_B)$. Note the consumers need only a **single point** $s^*$, not a limit — no filter/`Tendsto` machinery.

**Lemma R2 (log series with branch pin; supports the §2.6 preamble and D0c).** For $|z| \le 1/2$: $-\mathrm{Log}(1-z) = \sum_{k\ge1} z^k/k$ (absolutely convergent). Two verified proofs:
*(i) [Derivation A]* $g(z) := \sum_{k\ge1} z^k/k$ satisfies $\bigl((1-z)e^{g(z)}\bigr)' \equiv 0$ on the unit disc, value $1$ at $0$, so $e^{-g(z)} = 1-z$; then $|{\mathrm{Im}}(-g(z))| \le |g(z)| \le \sum_k 2^{-k} = 1 < \pi$ pins the branch: $-g(z) - \mathrm{Log}(1-z) \in 2\pi i\mathbb{Z}$ with imaginary part in $(-1-\pi, 1+\pi) \subset (-2\pi, 2\pi)$, hence $= 0$.
*(ii) [Derivation B]* $1 - z$ lies in the open right half-plane $\subset \mathbb{C}\setminus(-\infty,0]$ where $\mathrm{Log}$ is holomorphic with derivative $1/w$; both sides have derivative $1/(1-z)$ on the disc and vanish at $0$ (valid for all $|z| < 1$).
Use whichever matches Mathlib's `Complex.log` Taylor-series API (audit item; see route decisions). All uses have $|z| = |\chi(p)p^{-s}| \le 2^{-\sigma} < 1/2$ since only $\sigma > 1$ is ever needed.

**(D0a)** $B(s) := \tfrac12\sum_{p\text{ odd}} p^{-2s}$: partial sums entire; on compact $K \subset \Omega$ with $\sigma_0 := \min_K \sigma > 1/2$, the tail is $\le \tfrac12\sum_{n>N} n^{-2\sigma_0} \to 0$ ($2\sigma_0 > 1$), so $B_N \to B$ locally uniformly and $B$ is holomorphic on $\Omega$ (M9). For real $s$: $B(s) \ge 0$, and $B(s) \le C_B := \tfrac12\sum_{n\ge3} n^{-2}$ for $s \ge 1$. Blow-up at $1/2^+$: the R1 instance above. *(Verified; the parenthetical in §2.6 should read "finite set of odd primes" — or absorb the $p=2$ term $\tfrac14$ into the $2M$ slack. Cosmetic.)*

**(D0b)** $t_p(s) := \sum_{k\ge3}\chi(p)^k p^{-ks}/k$: geometric tail gives $|t_p(s)| \le \tfrac13 p^{-3\sigma}(1-p^{-\sigma})^{-1}$ for $\sigma > 0$, and each $t_p$ is holomorphic on $\{\sigma > 0\}$ (uniform geometric tails + M9). On $\sigma \ge 1/2$: $|t_p(s)| \le (\kappa/3)\,p^{-3/2} =: M_p$ with $\kappa := (1-2^{-1/2})^{-1}$; $\sum_p M_p \le (\kappa/3)\sum_{n\ge2} n^{-3/2} =: C_T < \infty$. Weierstrass M-test: $T := \sum_p t_p$ is holomorphic on $\Omega$ with $|T(s)| \le C_T$ on $\sigma \ge 1/2$, real on real $s$. *(Spec's $K = 3C_T$ drops the $1/k \le 1/3$ factor — both correct.)*

**(D0c) — per-p split, no double-sum rearrangement.** For $\sigma > 1$ and each $p$, put $z_p := \chi(p)p^{-s}$, $|z_p| \le 2^{-\sigma} < 1/2$. R2 gives the **exact per-p identity**
$$-\mathrm{Log}(1-z_p) = \chi(p)p^{-s} + \tfrac12\chi(p)^2 p^{-2s} + t_p(s),$$
(splitting the $k{=}1,2$ terms off a convergent series and calling the remainder $t_p(s)$ is definitional — no rearrangement). Each of the three prime-indexed series converges absolutely (dominations $p^{-\sigma}$, $\tfrac12 p^{-2\sigma}$, $\tfrac13 p^{-3\sigma}(1-p^{-\sigma})^{-1}$), so **linearity of three convergent series** gives $\sum_p -\mathrm{Log}(1-z_p) = A_{\mathrm{ser}}(s) + B(s) + T(s)$, with $A_{\mathrm{ser}}(s) := \sum_p \chi(p)p^{-s}$ and $\chi(2)^2 = 0$, $\chi(p)^2 = 1$ (p odd) identifying the middle piece as $B$. With the exp-form Euler product (M4): $\exp(A_{\mathrm{ser}} + B + T) = L$ on $\{\sigma>1\}$. *(This replaces §2.6's "rearrangement" — sound as stated there, but the per-p route needs no absolutely-summable-double-family machinery, directly shrinking risk R4.)*

**(D0d)** As §2.6 (Mathlib M2/M3): $L$ entire, $=$ Dirichlet series on $\sigma>1$, $L(1) \ne 0$.

**Case $c \ne 0$** *(= §2.6 c≠0 steps 1–3)*. Work with real $s \in (1,2]$.
1. Discrete Abel with coefficients $a_n := (\chi_4(n) - c)\cdot\mathbb{1}_{\text{prime}}(n)$, partial sums $R(n) = S(n) - c\,\pi(n)$, $|R| \le C$, $R(1) = 0$: for integer $N \ge 2$,
$$\textstyle\sum_{p\le N}(\chi(p)-c)p^{-s} = R(N)N^{-s} + \sum_{n=2}^{N-1} R(n)\,(n^{-s}-(n+1)^{-s}).$$
For real $s > 0$ the increments are positive and telescope to $2^{-s} - N^{-s}$, so the modulus is $\le C N^{-s} + C(2^{-s} - N^{-s}) = C\,2^{-s}$; letting $N\to\infty$ (both series converge absolutely for $s > 1$): $|A_{\mathrm{ser}}(s) - c\,P(s)| \le C\,2^{-s} \le C/2$. *(Verified; spec's $2C$ is a safe over-estimate.)*
2. Real-axis logarithm without branch issues: for real $s>1$ all of $A_{\mathrm{ser}}, B, T$ are real, so $L(s) = e^{\text{real}} > 0$ and $\ln L(s) = A_{\mathrm{ser}}(s)+B(s)+T(s)$ by **injectivity of real** $\exp$ (no complex log inverted). $L(1) > 0$: limit of the positive values $L(1+1/n)$ is real $\ge 0$ and $\ne 0$ by M3. Extreme values of the continuous positive $L$ on $[1,2]$: $|\ln L| \le K_L$ there; hence $|A_{\mathrm{ser}}(s)| \le K_L + C_B + C_T =: K$ on $(1,2]$.
3. If $c \ne 0$: $|c|P(s) \le K + C/2$ on $(1,2]$, but R1 ($a=1$) supplies a single $s^* \in (1,2]$ with $P(s^*) > (K + C/2 + 1)/|c|$. Contradiction. Hence $c = 0$ and $|S(y)| \le C$ for all $y$.

**(D1)** Define the **by-parts series** on $\{\sigma > 0\}$:
$$\tilde A(s) := \textstyle\sum_{n\ge2} S(n)\,\bigl(n^{-s}-(n+1)^{-s}\bigr).$$
- *Increment lemma (= audit item M12):* $n^{-s}-(n+1)^{-s} = s\int_n^{n+1} t^{-s-1}\,dt$ (FTC on real/imaginary parts), so $|n^{-s}-(n+1)^{-s}| \le |s|\,n^{-\sigma-1}$. **Verified correct** — this was the spec's first flagged weak point.
- *Holomorphy:* on compact $K \subset \{\sigma>0\}$ with $\sigma_0 := \min_K \sigma$, $M_K := \max_K|s|$: terms are dominated by $C M_K n^{-\sigma_0-1}$, summable; Weierstrass M-test gives locally uniform convergence of the entire partial sums, and M9 gives $\tilde A$ holomorphic on $\{\sigma>0\} \supset \Omega$. **Verified** — the spec's locally-uniform tail bound closes exactly as sketched.
- *Real-segment bound:* for real $s > 0$ the increments are positive and telescope: $|\tilde A(s)| \le C\,2^{-s} \le C$ on $(1/2,2]$, and $\tilde A(s)$ is real. *(Spec's $3C$ safe.)*
- *Identification:* for $\sigma > 1$ and integer $Y$: $\sum_{p\le Y}\chi(p)p^{-s} = S(Y)Y^{-s} + \sum_{n=2}^{Y-1}S(n)(n^{-s}-(n+1)^{-s})$; the boundary term $\to 0$, so $\tilde A = A_{\mathrm{ser}}$ on $\{\sigma>1\}$.

**(D2)** $G := \tilde A + B + T$ is holomorphic on $\Omega$; $\exp\circ G$ is holomorphic on $\Omega$ and equals $L$ on $\{\sigma>1\}$ (D0c + D0d + identification).

**(D3)** $\Omega$ is open and convex, hence connected; $\exp\circ G$ and $L|_\Omega$ are holomorphic and agree on the nonempty open $\{\sigma>1\}$; the identity theorem (M8) gives $\exp(G) = L$ on all of $\Omega$.

**(D4) — single-point form.** $L$ is continuous at $1/2$ (entire): pick $\delta_0 \in (0, 1/2)$ with $|L(s)| < M_0 := |L(1/2)| + 1$ for $|s - 1/2| < \delta_0$. R1 ($a = 2$, odd primes) with threshold $\ln M_0 + C + C_T$ gives $\delta_B > 0$; set $s^* := 1/2 + \tfrac12\min(\delta_0, \delta_B) \in (1/2, 1)$. Then $\tilde A(s^*), T(s^*)$ are real with $|\tilde A| \le C$, $|T| \le C_T$, so
$$|L(s^*)| = e^{\mathrm{Re}\,G(s^*)} \ge e^{B(s^*) - C - C_T} > e^{\ln M_0} = M_0,$$
contradicting $|L(s^*)| < M_0$. ∎ *(Equivalent to §2.6's $s \downarrow 1/2^+$ limit, but needs no filters — retires risk R7.)*

### Deltas: spec §2.6 vs Derivation A vs Derivation B

| Aspect | Spec §2.6 | Derivation A | Derivation B | Consolidated choice |
|---|---|---|---|---|
| Abel summation | **Discrete** over $n \in \mathbb{N}$ (D1, c≠0 step 1) | **Integral** $s\int_2^\infty W(t)t^{-s-1}dt$, DCT-free (L3: exact finite identity + integral additivity) | **Integral**, DCT with $R(\min(y,N))$ domination trick (Lemma 2) — trick verified valid | Discrete (see route decisions) |
| $k{=}1$ continuation object | implicit via by-parts tail | $A(s) := s\int_2^\infty S\,t^{-s-1}dt$ | $G(s) := s\int_2^\infty S\,y^{-s-1}dy$, holomorphy via step-function truncations $G_N$ | $\tilde A$ := the by-parts series itself |
| D0c split | "rearrangement" (reads as double-sum Fubini) | per-p exact split + linearity of 3 series | absolutely summable double family, then partition $\{k{=}1\},\{k{=}2\},\{k{\ge}3\}$ (summability established **before** regrouping — checked) | A's per-p split |
| Branch pin for $-\mathrm{Log}(1-z)=\sum z^k/k$ | asserted in preamble ("valid termwise", $\mathrm{Re}\,s>0$) | proved on $\vert z\vert\le1/2$: exp-inversion pinned by $\vert\mathrm{Im}\vert \le 1 < \pi$ | proved on $\vert z\vert<1$ via $\mathrm{Log}'(w) = 1/w$ on slit plane (no exp-inversion) | R2, both routes recorded; audit Mathlib form |
| $\log L$ on real axis | "product of positive reals" | real-$\exp$ injectivity (P5) | real-$\exp$ bijectivity (6.1) | same fact, made explicit |
| Forcing $c=0$ | $\vert A - cP\vert \le 2C$ vs $P \to \infty$ | $\le C\,2^{-s}$, single $s^*$ | $\le C/2$, single $s^*$ | single $s^*$; constant $C\,2^{-s}$ |
| Endgame at $1/2$ | limit $s \downarrow 1/2^+$ | single point $s^*$ (P12) | single point $s^*$ (Step F) | single point $s^*$ |
| $T$: domain / bound | $\Omega$; $K = (1-2^{-1/2})^{-1}\sum n^{-3/2}$ | $\{\sigma>0\}$ per-$p$, $\Omega$ for $T$; $C_T = K/3$ | $\{\sigma>1/3\}$, bound $25/3$ on $\sigma \ge 2/5$ (extra generality, unneeded) | $\Omega$, constant $C_T$ |
| Real-segment $\vert A\vert$ bound | $3C$ | $C\,2^{-s} \le C$ | $C$ | $C$ (spec's $3C$ safe) |

All differences are **route/constant differences, not correctness differences**: every variant of every step was checked sound.

### Verdict and route decisions for the formalization

**VERDICT: SOUND.** No gap in §2.6, Derivation A, or Derivation B. Specifically, for the spec's two self-flagged weak points: (1) D1's increment bound and locally-uniform tail argument are correct and complete-able exactly as sketched; (2) D0c's rearrangement is correct as stated *and* avoidable entirely via the per-p split. No hidden nonvanishing of $L$ on $(1/2, 1)$ is assumed anywhere — $\exp(G) = L$ is *derived* from the boundedness hypothesis via the identity theorem, and $L(1) \ne 0$ is used exactly once (case $c \ne 0$, step 2). The only quantitative prime input is $\sum_p 1/p = \infty$, used exactly twice (R1 instances).

Route decisions (feeding Phases 1 and 4):

1. **D1/N1 via discrete Abel summation** (as specced), restructured so the continuation is *defined* as the by-parts series $\tilde A$: the analysis quarantines into the single FTC increment lemma (M12), and the rest is `Finset.sum_Ioc_by_parts` index work, positive telescoping, and a Weierstrass M-test feeding `TendstoLocallyUniformlyOn.differentiableOn` — no measurability of $S$ as a function of a real variable, no `IntegrableOn` side goals, no improper-integral limits, no DCT. **Fallback** (decide at audit item M10): Derivation A's L3 via `Mathlib/NumberTheory/AbelSummation.lean` (`sum_mul_eq_sub_sub_integral_mul` + limit forms) — the identity comes pre-built, at the cost of integrability/measurability side conditions at each of the three call sites; prefer it only if the by-parts index gymnastics blow past ~1 day. If the integral fallback is taken, formalize A's DCT-free proof shape, not B's DCT truncation (fewer moving parts).
2. **D0c via the per-p split** (Derivation A's P3), not double-sum rearrangement: shrinks risk R4 from `tsum_sigma` gymnastics to "subtract two terms from a convergent series, then add three series".
3. **Branch pin (R2) is a real proof obligation** the spec preamble glosses: audit whether Mathlib has $-\log(1-z) = \sum z^k/k$ for `Complex.log` (look near `EulerProduct`/`LogTaylor`-adjacent files; add as audit item M16). If present, done; if not, formalize R2 route (ii) if `Complex.log` differentiability on the slit plane has convenient API, else route (i) (needs only `Complex.exp` facts + the $2\pi i\mathbb{Z}$ pin).
4. **Single-point endgames** everywhere (P8/P12-style $s^*$): the Lean proof never needs `Filter.Tendsto` toward $1^+$ or $1/2^+$ — risk R7 is retired. R1's statement should be phrased as "∀ M, ∃ s ∈ (lo, hi), Q(s) > M"-with-δ, consumed by direct instantiation.
5. **Constants:** keep the spec's generous $2C$, $3C$, $K$ in Lean statements (weakest sufficient bounds formalize fastest); the sharp values verified here ($C\,2^{-s}$, $C_T = K/3$) are available if any inequality gets tight.
6. Two cosmetic spec fixes, no re-lock needed: D0a's parenthetical should say "finite set of **odd** primes" (or note the $p{=}2$ slack); the preamble's "valid termwise for $\mathrm{Re}\,s > 0$" over-claims the domain actually used ($\sigma > 1$, where $|z_p| < 1/2$) — true as stated (R2 route (ii)) but the $\sigma>1$ instance is all that is consumed.
