module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownRetention
public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
noncomputable section

/-- At the source large-X threshold, any retained component has a
positive dyadic exponent sum. This extracts the argument already used
locally in the large-factor exclusion proof. -/
theorem smoothHeathBrownRetainedExponentSum_pos
    {X : ℝ} (hX : (2 : ℝ) ^ 35 ≤ X)
    {fs : List (SmoothHeathBrownFactor X)}
    (hlen : fs.length ≤ 20) (hne : fs ≠ [])
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fs) :
    0 < smoothHeathBrownExponentSum fs := by
  have hX0 : 0 ≤ X := by positivity
  have hwindow := smoothHeathBrownSupportRetained_scale_bounds
    hlen hne hX0 hret
  have hXlo : (2 : ℝ) ^ 13 ≤ X / (2 : ℝ) ^ 22 := by
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 22)).2
    calc
      (2 : ℝ) ^ 13 * (2 : ℝ) ^ 22 = (2 : ℝ) ^ 35 := by
        rw [← pow_add]
      _ ≤ X := hX
  have hPlo : (2 : ℝ) ^ 13 ≤ smoothHeathBrownScaleProduct fs :=
    hXlo.trans hwindow.1
  by_contra hnot
  have hzero : smoothHeathBrownExponentSum fs = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [smoothHeathBrownScaleProduct_eq_two_pow_exponentSum, hzero] at hPlo
  norm_num at hPlo

#print axioms smoothHeathBrownRetainedExponentSum_pos
end
end FractionalPrimes.Literature.DirichletAdapter
