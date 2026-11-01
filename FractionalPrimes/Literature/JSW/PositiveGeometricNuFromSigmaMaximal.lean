module

public import FractionalPrimes.Literature.JSW.PositiveAllScaleMaximalAdapter
public import FractionalPrimes.Literature.JSW.PositiveMaximalPsiAdapters

/-! The smooth ψ maximal bound closes the second input of the abstract
geometric ν vector transfer at every exponent above one. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

def geometricPsiMaximalConstant (q : ℝ) : ℝ :=
  (4 * lpNorm φ ∞ volume) *
    ((6 * q * 2 ^ (q - 1) / (q - 1)) ^ (1 / q))

theorem geometricPsiMaximalConstant_nonneg {q : ℝ} (hq : 1 < q) :
    0 ≤ geometricPsiMaximalConstant q := by
  dsimp [geometricPsiMaximalConstant]
  apply mul_nonneg
  · exact mul_nonneg (by norm_num) lpNorm_nonneg
  · apply Real.rpow_nonneg
    apply div_nonneg
    · positivity
    · linarith

/-- Upper-exponent source geometric ν bound from the all-scale maximal
bound for the rough σ family and the checked smooth ψ maximal bound. -/
theorem finiteGeometricNuVector_upper_of_sigmaMaximal
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b p q Bσ : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hb : 1 < b) (hp : 2 < p) (hpq : (p / 2).HolderConjugate q)
    (hBσ : 0 ≤ Bσ)
    (hMaxσ : GeometricAdjointMaximalBound σ b q Bσ)
    (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hstrong : ∀ i, StronglyMeasurable (f i)) :
    lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
      (localizedSquareNuLpConvolution hSupp p b (by linarith) (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤
      (Real.sqrt Bσ + Real.sqrt (geometricPsiMaximalConstant q)) *
        lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i => f i x))
          (ENNReal.ofReal p) volume := by
  have hq : 1 < q := hpq.symm.lt
  exact finiteGeometricNuVector_upper_of_maximal hSupp hp hpq κ f hf hstrong
    Bσ (geometricPsiMaximalConstant q) hBσ
    (geometricPsiMaximalConstant_nonneg hq)
    (fun g hg => geometricAdjointMaximalBound_finite hMaxσ κ g hg)
    (fun g hg => by
      simpa [geometricPsiMaximalConstant] using
        (finiteGeometricPsiPositiveMaximalBound hSupp hb hq κ g hg))

#print axioms geometricPsiMaximalConstant_nonneg
#print axioms finiteGeometricNuVector_upper_of_sigmaMaximal

/-- Lower-exponent source geometric ν bound from the all-scale σ maximal
bound at the adjoint exponent and the checked smooth ψ bound. -/
theorem finiteGeometricNuVector_lower_of_sigmaMaximal
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b p q s Bσ : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hb : 1 < b) (hp : 1 < p) (hpq : p.HolderConjugate q)
    (hq : 2 < q) (hqs : (q / 2).HolderConjugate s)
    (hBσ : 0 ≤ Bσ)
    (hMaxσ : GeometricAdjointMaximalBound σ b s Bσ)
    (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hstrong : ∀ i, StronglyMeasurable (f i)) :
    lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
      (localizedSquareNuLpConvolution hSupp p b hp (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤
      (Real.sqrt Bσ + Real.sqrt (geometricPsiMaximalConstant s)) *
        lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i => f i x))
          (ENNReal.ofReal p) volume := by
  have hs : 1 < s := hqs.symm.lt
  exact finiteGeometricNuVector_lower_of_maximal hSupp hp hpq hq hqs
    κ f hf hstrong Bσ (geometricPsiMaximalConstant s) hBσ
    (geometricPsiMaximalConstant_nonneg hs)
    (fun g hg => geometricAdjointMaximalBound_finite hMaxσ κ g hg)
    (fun g hg => by
      simpa [geometricPsiMaximalConstant] using
        (finiteGeometricPsiPositiveMaximalBound hSupp hb hs κ g hg))

#print axioms finiteGeometricNuVector_lower_of_sigmaMaximal

end

end FractionalPrimes.Literature.JSW

end
