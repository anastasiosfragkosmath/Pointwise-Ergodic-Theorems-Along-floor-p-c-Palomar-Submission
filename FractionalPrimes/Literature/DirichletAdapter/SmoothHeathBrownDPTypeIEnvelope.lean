module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownDPSourceComponentTransfer
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorSourceIdentity

@[expose] public section
noncomputable section
namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open MeasureTheory
open scoped BigOperators

/-- The source cpow and real-log Mellin conventions agree at every positive
integer. This keeps the Type-I estimate's frequency unchanged. -/
theorem mellinDirichletMonomial_eq_sourceTwist
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    mellinDirichletMonomial n t = (n : ℂ) ^ smoothDyadicTwistExponent t := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  unfold mellinDirichletMonomial smoothDyadicTwistExponent
  congr 1
  push_cast
  ring

/-- The actual component Mellin polynomial is exactly the literal source
residue sum. The cutoff proves finite support even for arbitrary g. -/
theorem smoothHeathBrownComponentMellin_eq_sourceTsum
    {X : ℝ} (hX : 3 ≤ X) (q a : ℕ) (g : ℕ → ℝ) (t : ℝ) :
    smoothHeathBrownComponentOuterCutoffMellinPolynomial X q (a : ℤ) g t =
      ∑' n : ℕ, if n ≡ a [MOD q] then
        (g n : ℂ) * (n : ℂ) ^ smoothDyadicTwistExponent t *
          (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0 := by
  classical
  have hXp : 0 < X := by linarith
  have hcut (n : ℕ) (hn : n ∉ mellinWindowSupportIndices X) :
      polynomialOuterCutoff ((n : ℝ) / X) = 0 := by
    by_contra hne
    have hs := polynomialOuterCutoff_support_subset hne
    have heq : ((n : ℝ) / X) * X = n := div_mul_cancel₀ _ hXp.ne'
    have hwindow : X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X := by
      constructor <;> nlinarith [hs.1, hs.2]
    apply hn
    exact (mellinIntervalIndices_mem_iff (by positivity : 0 ≤ X / 2) n).mpr hwindow
  rw [tsum_eq_sum (s := mellinWindowSupportIndices X)]
  · unfold smoothHeathBrownComponentOuterCutoffMellinPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := by
      have hmem := (Finset.mem_filter.mp hn).1
      exact (Finset.mem_Icc.mp hmem).1
    rw [mellinDirichletMonomial_eq_sourceTwist n hnpos t]
    by_cases hr : n ≡ a [MOD q]
    · have hrZ : Int.ModEq (q : ℤ) (n : ℤ) (a : ℤ) := Int.natCast_modEq_iff.mpr hr
      simp only [smoothHeathBrownComponentOuterCutoffCoefficient, hrZ,
        if_true, mul_one, Complex.ofReal_mul, hr]
      ring
    · have hrZ : ¬ Int.ModEq (q : ℤ) (n : ℤ) (a : ℤ) := by
        simpa only [Int.natCast_modEq_iff] using hr
      simp [smoothHeathBrownComponentOuterCutoffCoefficient, hrZ, hr]
  · intro n hn
    simp [hcut n hn]

#print axioms smoothHeathBrownComponentMellin_eq_sourceTsum

/-- A uniform bound on the source tails bounds the exact compact envelope,
since its normalization T₀/U is at most one throughout the source range. -/
theorem dirichletMeanEnvelopeOfA_X_le_of_uniformTailBound
    (F : ℝ → ℂ) {T0 W K : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hbound : ∀ U ∈ Set.Icc T0 (T0 * W ^ 4),
      (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U}, ‖F t‖) ≤ K) :
    dirichletMeanEnvelopeOfA_X F T0 W ≤ K := by
  have hT : 0 < T0 := by linarith
  have hpow : (1 : ℝ) ≤ W ^ (4 : ℕ) := one_le_pow₀ (by linarith : (1 : ℝ) ≤ W)
  have hTend : T0 ≤ T0 * W ^ (4 : ℕ) := by nlinarith only [hpow, hT]
  apply csSup_le (Set.Nonempty.image _ (Set.nonempty_Icc.mpr hTend))
  rintro _ ⟨U, hU, rfl⟩
  have hUpos : 0 < U := hT.trans_le hU.1
  have hscale : T0 / U ≤ 1 := (div_le_one hUpos).mpr hU.1
  calc
    _ ≤ 1 * K := mul_le_mul hscale (hbound U hU)
      (integral_nonneg (fun _ => norm_nonneg _)) zero_le_one
    _ = K := one_mul _

/-- The long Type-I estimate now applies directly to the exact source
component envelope, with its original coefficient, cutoff and residue. -/
theorem smoothHeathBrownTypeIComponentEnvelope_le
    {X : ℝ} (B D η : ℝ)
    (hX : smoothLongFactorTypeIThreshold B D η ≤ X)
    (fs : List (SmoothHeathBrownFactor X)) (s : Fin fs.length)
    (hcount : fs.length ≤ 20)
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fs)
    (hlong : (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get s))
    (hlog : fs.countP smoothHeathBrownTypeILogFactor ≤ 1)
    (q a : ℕ) (hq : 0 < q) (T0 W : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) (hj : 2 ≤ j)
    (hWdef : W = (Real.log X) ^ D) (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hT : T0 ≤ X ^ ((3 / 8 : ℝ) - η))
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ B)
    (c : ℝ) (hc : |c| ≤ (2 : ℝ) ^ 10) :
    dirichletMeanEnvelopeOfA_X
      (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q (a : ℤ)
        (fun n => c * smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X) fs n)) T0 W ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * smoothDyadicC j) * Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  obtain ⟨hXlarge, hlarge⟩ := smoothLongFactorTypeIThreshold_conditions B D η X hX
  have hXthree : 3 ≤ X := by linarith
  apply dirichletMeanEnvelopeOfA_X_le_of_uniformTailBound _ hW hWT
  intro U hU
  have hUupper : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ) :=
    hU.2.trans (mul_le_mul_of_nonneg_right hT (by positivity))
  have hmean := smoothHeathBrownRetainedTypeISourceTsum_mean_le_K_of_largeX
    hXlarge fs s hcount hret hlong q a hq W U η B D j hη hB hD hj
    hWdef hW (hWT.trans hU.1) hUupper hqlog hlarge hlog c hc
  have hident : ∀ t : ℝ,
      smoothHeathBrownComponentOuterCutoffMellinPolynomial X q (a : ℤ)
        (fun n => c * smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X) fs n) t =
      ∑' n : ℕ, if n ≡ a [MOD q] then
        (c : ℂ) * (smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X) fs n : ℂ) *
          (n : ℂ) ^ smoothDyadicTwistExponent t *
            (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0 := by
    intro t
    rw [smoothHeathBrownComponentMellin_eq_sourceTsum hXthree]
    simp only [Complex.ofReal_mul]
  simpa only [hident] using hmean

#print axioms smoothHeathBrownTypeIComponentEnvelope_le

/-- The grouping Type-I weight is precisely the long-factor scale condition
used by the unconditional source estimate. -/
theorem smoothHeathBrownGroupingWeight_longScale
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hE : 0 < smoothHeathBrownExponentSum fs) (i : Fin fs.length)
    (hi : (3 / 8 : ℝ) ≤ (smoothHeathBrownExponentGrouping fs hE).weight i) :
    (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get i) := by
  have hlog : 0 < Real.log (smoothHeathBrownScaleProduct fs) := by
    rw [smoothHeathBrownScaleProduct_eq_two_pow_exponentSum, Real.log_pow]
    exact mul_pos (by exact_mod_cast hE) (Real.log_pos (by norm_num))
  rw [smoothHeathBrownExponentGrouping_weight_eq_log] at hi
  apply (Real.log_le_log_iff
    (Real.rpow_pos_of_pos (smoothHeathBrownScaleProduct_pos fs) _)
    (smoothHeathBrownFactorScale_pos _)).mp
  rw [Real.log_rpow (smoothHeathBrownScaleProduct_pos fs)]
  exact (le_div_iff₀ hlog).mp hi

/-- The exact per-component dichotomy, retaining the IImaj predicate rather
than replacing it with a condition assumed of every label. -/
theorem smoothHeathBrown_longScale_or_IImaj
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hE : 0 < smoothHeathBrownExponentSum fs) :
    (∃ i : Fin fs.length,
      (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
        smoothHeathBrownFactorScale (fs.get i)) ∨
      (smoothHeathBrownExponentGrouping fs hE).IImaj (5 / 8) := by
  rcases majorGroupingFiveEighths (smoothHeathBrownExponentGrouping fs hE) with hI | hII
  · obtain ⟨i, hi⟩ := hI
    exact Or.inl ⟨i, smoothHeathBrownGroupingWeight_longScale fs hE i (by norm_num at hi ⊢; exact hi)⟩
  · exact Or.inr hII

theorem smoothHeathBrownMobiusLabel_typeIEnvelope_le
    {X : ℝ} (B D η : ℝ)
    (hX : smoothLongFactorTypeIThreshold B D η ≤ X)
    (ν : SmoothHeathBrownMobiusLabel X)
    (s : Fin (smoothHeathBrownMobiusLabelFactors ν).length)
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) (smoothHeathBrownMobiusLabelFactors ν))
    (hlong : (smoothHeathBrownScaleProduct (smoothHeathBrownMobiusLabelFactors ν)) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale ((smoothHeathBrownMobiusLabelFactors ν).get s))
    (q a : ℕ) (hq : 0 < q) (T0 W : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) (hj : 2 ≤ j)
    (hWdef : W = (Real.log X) ^ D) (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hT : T0 ≤ X ^ ((3 / 8 : ℝ) - η))
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ B) :
    dirichletMeanEnvelopeOfA_X
      (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q (a : ℤ)
        (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν)) T0 W ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * smoothDyadicC j) * Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  have h := smoothHeathBrownTypeIComponentEnvelope_le B D η hX
    (smoothHeathBrownMobiusLabelFactors ν) s (smoothHeathBrownMobiusFactorCount ν).2
    hret hlong (smoothHeathBrownMobiusLabelFactors_typeILogCount_le_one ν)
    q a hq T0 W j hη hB hD hj hWdef hW hWT hT hqlog
    (dyadicBinomialCoefficient ν.1) (smoothHeathBrownComponentCoefficient_abs_le ν.1)
  have hg : (fun n => dyadicBinomialCoefficient ν.1 *
      smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
        (smoothHeathBrownMobiusLabelFactors ν) n) =
      (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν : ℕ → ℝ) := by
    funext n
    exact (smoothHeathBrownMobiusComponent_apply _ ν n).symm
  rw [hg] at h
  exact h

theorem smoothHeathBrownVonMangoldtLabel_typeIEnvelope_le
    {X : ℝ} (B D η : ℝ)
    (hX : smoothLongFactorTypeIThreshold B D η ≤ X)
    (ν : SmoothHeathBrownVonMangoldtLabel X)
    (s : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length)
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) (smoothHeathBrownVonMangoldtLabelFactors ν))
    (hlong : (smoothHeathBrownScaleProduct (smoothHeathBrownVonMangoldtLabelFactors ν)) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale ((smoothHeathBrownVonMangoldtLabelFactors ν).get s))
    (q a : ℕ) (hq : 0 < q) (T0 W : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) (hj : 2 ≤ j)
    (hWdef : W = (Real.log X) ^ D) (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hT : T0 ≤ X ^ ((3 / 8 : ℝ) - η))
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ B) :
    dirichletMeanEnvelopeOfA_X
      (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q (a : ℤ)
        (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν)) T0 W ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * smoothDyadicC j) * Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  have h := smoothHeathBrownTypeIComponentEnvelope_le B D η hX
    (smoothHeathBrownVonMangoldtLabelFactors ν) s (smoothHeathBrownVonMangoldtFactorCount ν).2
    hret hlong (smoothHeathBrownVonMangoldtLabelFactors_typeILogCount_le_one ν)
    q a hq T0 W j hη hB hD hj hWdef hW hWT hT hqlog
    (dyadicBinomialCoefficient ν.1) (smoothHeathBrownComponentCoefficient_abs_le ν.1)
  have hg : (fun n => dyadicBinomialCoefficient ν.1 *
      smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
        (smoothHeathBrownVonMangoldtLabelFactors ν) n) =
      (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν : ℕ → ℝ) := by
    funext n
    exact (smoothHeathBrownVonMangoldtComponent_apply _ ν n).symm
  rw [hg] at h
  exact h

#print axioms smoothHeathBrown_longScale_or_IImaj
#print axioms smoothHeathBrownMobiusLabel_typeIEnvelope_le
#print axioms smoothHeathBrownVonMangoldtLabel_typeIEnvelope_le

theorem smoothHeathBrownRawComponentMellin_eq_scaledProduct
    {X : ℝ} (hX : 3 ≤ X) (fs : List (SmoothHeathBrownFactor X))
    (hlen : 0 < fs.length) (q : ℕ) (hq : 0 < q) (a : ℤ) (c t : ℝ) :
    smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
      (fun n => c * smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X) fs n) t =
      ((c : ℂ) * (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)) *
        (mellinSeparationProductWindowData
          (fun i : Fin fs.length => smoothHeathBrownNormalizedMellinFactor
            (z := dyadicMobiusCutoff X) (fs.get i)) q a X hX).A_X t := by
  apply smoothHeathBrownSourceComponentMellin_eq_scaledProductWindowData hX hlen hq
  intro n hn
  rw [Complex.ofReal_mul,
    smoothHeathBrownConvolutionFactors_eq_scaledMellinArithmeticProduct hX fs n]
  rw [mellinSeparationArithmeticProduct_eq_tupleConvolution]
  ring

theorem sourceDirichletT0_le_typeIUpper
    {X H η : ℝ} (hX : 0 < X) (hH : X ^ ((5 / 8 : ℝ) + η) ≤ H) :
    X / H ≤ X ^ ((3 / 8 : ℝ) - η) := by
  rw [show (3 / 8 : ℝ) - η = 1 - ((5 / 8 : ℝ) + η) by ring,
    Real.rpow_sub hX, Real.rpow_one]
  exact div_le_div_of_nonneg_left hX.le (Real.rpow_pos_of_pos hX _) hH

#print axioms smoothHeathBrownRawComponentMellin_eq_scaledProduct
end FractionalPrimes.Literature.DirichletAdapter
