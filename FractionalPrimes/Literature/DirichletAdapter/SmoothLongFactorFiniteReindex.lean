module

public import FractionalPrimes.Literature.DirichletAdapter.LongFactorResidueReduction
public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownConvolution
import Mathlib.Tactic

/-! Exact finite restriction of a smooth Heath--Brown factor sum to the
reduced residue class obtained after fixing the other factors. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- After the other factors have product `m`, a finite weighted sum of one
smooth Heath--Brown factor over `m*n ≡ a (mod q)` is exactly the sum over the
single reduced residue class modulo `q / gcd(m,q)`. The finite set can be the
factor's support window; the weight is left arbitrary for later quadrature. -/
theorem smoothHeathBrownFactor_fixedProduct_sum_reindex
    {X z : ℝ} (f : SmoothHeathBrownFactor X) (S : Finset ℕ)
    (w : ℕ → ℂ) (m q a n₀ : ℕ) (hq : 0 < q)
    (hsol : m * n₀ ≡ a [MOD q]) :
    (∑ n ∈ S.filter (fun n => m * n ≡ a [MOD q]),
      ((smoothHeathBrownFactorFunction z f n : ℝ) : ℂ) * w n) =
    ∑ n ∈ S.filter (fun n => n ≡ n₀ [MOD q / Nat.gcd m q]),
      ((smoothHeathBrownFactorFunction z f n : ℝ) : ℂ) * w n := by
  classical
  have hfilters :
      S.filter (fun n => m * n ≡ a [MOD q]) =
        S.filter (fun n => n ≡ n₀ [MOD q / Nat.gcd m q]) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hres⟩
      exact ⟨hn,
        (mul_congruence_iff_reduced_residue m q a n₀ hq hsol n).mp hres⟩
    · rintro ⟨hn, hres⟩
      exact ⟨hn,
        (mul_congruence_iff_reduced_residue m q a n₀ hq hsol n).mpr hres⟩
  rw [hfilters]

#print axioms smoothHeathBrownFactor_fixedProduct_sum_reindex

/-- If fixing the other factors makes the target congruence insoluble, its
finite weighted smooth-factor contribution is zero. -/
theorem smoothHeathBrownFactor_fixedProduct_sum_eq_zero_of_no_solution
    {X z : ℝ} (f : SmoothHeathBrownFactor X) (S : Finset ℕ)
    (w : ℕ → ℂ) (m q a : ℕ)
    (hno : ∀ n : ℕ, ¬ m * n ≡ a [MOD q]) :
    (∑ n ∈ S.filter (fun n => m * n ≡ a [MOD q]),
      ((smoothHeathBrownFactorFunction z f n : ℝ) : ℂ) * w n) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro n hn
  have hn' := (Finset.mem_filter.mp hn).2
  exact (hno n hn').elim

#print axioms smoothHeathBrownFactor_fixedProduct_sum_eq_zero_of_no_solution

end FractionalPrimes.Literature.DirichletAdapter

end
