# Lean verification of "Pointwise Ergodic Theorems Along `⌊pᶜ⌋` for Every `c>1`"

A Lean 4 + Mathlib formalization of the principal variational and pointwise results in Anastasios Fragkos's *Pointwise Ergodic Theorems Along* $`\lfloor p^c\rfloor`$ *for Every* $`c>1`$.

- [Paper](fractionalpowersofprimesfinal.tex)
- [Bibliography](fractionalprimesbib.bib)

## Main results

Let $c>1$ be noninteger and $1<p<\infty$. Let $(X,\mathcal B,\nu,T)$ be a sigma-finite measure-preserving system and $f\in L^p(X)$. Write

```math
\begin{aligned}
A_N^c f(x)&=\frac1N\sum_{n=1}^N\Lambda(n)f\!\left(T^{\lfloor n^c\rfloor}x\right),
&&N\ge1,\\
P_N^c f(x)&=\frac1{\pi(N)}\sum_{\substack{q\le N\\q\text{ prime}}}
f\!\left(T^{\lfloor q^c\rfloor}x\right),
&&N\ge2.
\end{aligned}
```

Here $\Lambda$ is the von Mangoldt function, $\pi(N)$ counts the primes up to $N$, and $\mu$ below denotes the Möbius function.

**Variational estimate.** For every $r>2$,

```math
\bigl\|\mathcal V^r(A_N^c f:N\ge1)\bigr\|_{L^p(X)}
\lesssim_{c,p,r}\|f\|_{L^p(X)}.
```

**Almost-everywhere convergence.** The averages $A_N^c f$ and $P_N^c f$ converge almost everywhere to the same limit. The averages over the first $M$ primes,

```math
\frac1M\sum_{j=1}^M f\!\left(T^{\lfloor p_j^c\rfloor}x\right),
```

converge almost everywhere to that limit as well, where $p_j$ is the $j$-th prime.

**Möbius-weighted convergence.** For every $A>1$,

```math
\frac1N\sum_{n=1}^N\mu(n)f\!\left(T^{\lfloor n^c\rfloor}x\right)
=o\!\left((\log N)^{-A}\right)
\qquad(N\to\infty)
```

for almost every $x\in X$.

## Main Lean declarations

The paper-facing statements are collected in [`FractionalPrimes.PaperTheorems`](FractionalPrimes/PaperTheorems.lean):

- `FractionalPrimes.PaperTheorems.prime_power_variation`
- `FractionalPrimes.PaperTheorems.prime_average_convergence`
- `FractionalPrimes.PaperTheorems.mobius_logarithmic_convergence`

The [semantic audit](semantic-audit.md) describes their correspondence with the paper. The submitted convergence declaration records the pointwise conclusion of the prime-convergence corollary.

## Build and verify

Use the toolchain selected by `lean-toolchain` and the dependencies pinned in `lake-manifest.json`:

```sh
lake exe cache get
lake build
lake build FractionalPrimes.PaperTheorems
python3 scripts/audit_sources.py --allow-challenge-placeholders
python3 scripts/audit_axioms.py --already-built
python3 scripts/audit_attribution.py
```

The source-policy checks prohibit placeholders and proof-bypass mechanisms in the completed proof sources. The independent `Challenge.lean` contains the three author-approved statement-only placeholders. Its statements are compared with the proofs exported through `Solution.lean`, using `comparator.json`.

The [verification report](verification-report.md) records the local checks and the exact scope of the earlier independent-kernel verification. The pre-cleanup a.e.-only snapshot passed sandboxed Comparator in Ubuntu with Con-ron, NanoDa, and Lean’s default kernel. The later cleanup passed the GitHub Lean build; a fresh Comparator run of the current statement files remains pending.

## Navigation

- [Paper-facing theorem statements](FractionalPrimes/PaperTheorems.lean)
- [Local verification report](verification-report.md)
- [Semantic comparison with the paper](semantic-audit.md)

## License and acknowledgments

The project code and documentation are licensed under [Apache-2.0](LICENSE). Third-party sources retain their original credits and licenses; see [THIRD-PARTY.md](THIRD-PARTY.md), [NOTICE](NOTICE), [ACKNOWLEDGMENTS.md](ACKNOWLEDGMENTS.md), and [software citations](CITATIONS.bib).
