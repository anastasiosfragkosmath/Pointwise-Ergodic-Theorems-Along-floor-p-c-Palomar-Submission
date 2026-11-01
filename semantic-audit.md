# Semantic comparison with the paper

This report compares the statements in [`FractionalPrimes/PaperTheorems.lean`](FractionalPrimes/PaperTheorems.lean) with [*Pointwise Ergodic Theorems Along $\lfloor p^c\rfloor$ for Every $c>1$*](fractionalpowersofprimesfinal.tex). The author-supplied manuscript and [bibliography](fractionalprimesbib.bib) are included.

Throughout, $c>1$ is noninteger, $1<p<\infty$, $(X,\mathcal B,\nu,T)$ is a sigma-finite measure-preserving system, and $f\in L^p(X)$.

## Variational estimate

Theorem `t:maintheorem` corresponds to `prime_power_variation`. It proves

```math
\bigl\|\mathcal V^r(A_N^c f:N\ge1)\bigr\|_{L^p(X)}
\lesssim_{c,p,r}\|f\|_{L^p(X)},\qquad r>2,
```

with $A_N^c f$ defined explicitly in the [README](README.md). The constant is quantified before the system and observable, so it depends only on $c,p,r$. The variation is homogeneous: Lean takes the supremum over all finite strictly increasing chains of positive integer cutoffs.

`FractionalExponent` records the precise exponent range. The real parameters $p$ and $r$ satisfy `1 < p` and `2 < r`. `Final.System` represents a sigma-finite measure-preserving system, and `floorTime` agrees with the integer floor in the paper at every summation index.

## Prime convergence

The author selected the pointwise conclusion of Corollary `cor:prime-convergence` for the submitted statement. `prime_average_convergence` gives one function $g$ such that

```math
A_N^c f(x)\longrightarrow g(x),\qquad
P_N^c f(x)\longrightarrow g(x)
```

for almost every $x\in X$. It also gives

```math
\frac1M\sum_{j=1}^M f\!\left(T^{\lfloor p_j^c\rfloor}x\right)
\longrightarrow g(x)
```

almost everywhere, where $p_j$ is the $j$-th prime. These are the three a.e. conclusions in the core theorem, submission wrapper, independent Challenge, and paper-facing theorem.

The prime cutoff starts at $N=2$, and the enumerated family has exactly $M$ terms. Lean's zero-based enumeration starts with `Nat.nth Nat.Prime 0 = 2`. All families have the same limit. The proof establishes the conclusion for every real $p>1$ under the system and observable hypotheses above.

## Möbius-weighted convergence

Theorem `t:mobius-convergence` corresponds to `mobius_logarithmic_convergence`. For every $A>1$, the asserted decay is

```math
\frac1N\sum_{n=1}^N\mu(n)f\!\left(T^{\lfloor n^c\rfloor}x\right)
=o\!\left((\log N)^{-A}\right)
\qquad(N\to\infty)
```

for almost every $x\in X$. Lean records the equivalent limit

```math
\lim_{N\to\infty}\frac{(\log N)^A}{N}
\sum_{n=1}^N\mu(n)f\!\left(T^{\lfloor n^c\rfloor}x\right)=0.
```

The weight is Mathlib's Möbius function. The finite sum runs from $1$ to $N$ and has normalization $1/N$. Positive cutoffs include $N=1$; this initial term does not affect the limit.

## Proof correspondence

The variation proof uses the long/short decomposition and transfers the resulting bounds through finite forward-orbit cutoffs. Their input and output lengths are $R+L+1$ and $R+1$, giving the exact boundary ratio $(R+L+1)/(R+1)$ before taking $R\to\infty$.

Prime convergence uses the checked higher-prime-power remainder, Abel summation, and prime normalization. The Möbius argument combines arithmetic decay with sparse long scales and summable weighted short blocks, then covers every positive integer cutoff, including repeated sparse scales.

The paper-facing theorems reuse these checked core proofs. The independent statement review is in `FinalChallengeStatements.lean`; `Challenge.lean` and `FinalSolution.lean` are the configured statement/proof pair. The preceding a.e.-only statement/proof pair passed Linux sandbox Comparator with all three configured kernels. Subsequent removal of unused statement-file definitions leaves the compared claims unchanged; local compilation passed, and a fresh sandbox Comparator run of the cleaned file is pending. The [verification report](verification-report.md) records the exact checked snapshot and the separate local checks for the paper-facing declarations.
