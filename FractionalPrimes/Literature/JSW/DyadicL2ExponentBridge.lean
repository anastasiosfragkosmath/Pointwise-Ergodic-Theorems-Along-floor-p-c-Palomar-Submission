module

public import FractionalPrimes.Literature.JSW.DyadicAverageL2Expansion

/-! Exponent-polymorphic L2 dyadic expansion, avoiding dependent casts of Lp operators. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

def dyadicDifferenceLpAt
    {P : ENNReal} [Fact (1 ≤ P)] (hP : P = 2)
    {f : ℝ → ℂ} (hf : MemLp f P volume) (j : ℤ) : Lp ℂ P (volume : Measure ℝ) := by
  have hmem : MemLp (dyadicDifference j f) P volume := by
    subst P
    exact memLp_dyadicDifference_two_of_memLp hf j
  exact hmem.toLp (dyadicDifference j f)

theorem dyadicDifferenceLpAt_hasSum
    {P : ENNReal} [Fact (1 ≤ P)] (hP : P = 2)
    {f : ℝ → ℂ} (hf : MemLp f P volume) :
    HasSum (fun j : ℤ => dyadicDifferenceLpAt hP hf j) (hf.toLp f) := by
  subst P
  exact dyadicDifferenceL2Vector_hasSum hf

theorem dyadicDifferenceLpAt_parseval
    {P : ENNReal} [Fact (1 ≤ P)] (hP : P = 2)
    {f : ℝ → ℂ} (hf : MemLp f P volume) :
    HasSum (fun j : ℤ => ‖dyadicDifferenceLpAt hP hf j‖^2) (‖hf.toLp f‖^2) := by
  subst P
  exact dyadicDifferenceL2Vector_parseval hf

theorem dyadicDifferenceLpAt_ae_eq
    {P : ENNReal} [Fact (1 ≤ P)] (hP : P = 2)
    {f : ℝ → ℂ} (hf : MemLp f P volume) (j : ℤ) :
    (dyadicDifferenceLpAt hP hf j : ℝ → ℂ) =ᵐ[volume] dyadicDifference j f := by
  unfold dyadicDifferenceLpAt
  exact MemLp.coeFn_toLp _

#print axioms dyadicDifferenceLpAt_hasSum
#print axioms dyadicDifferenceLpAt_parseval
end
end FractionalPrimes.Literature.JSW
end
