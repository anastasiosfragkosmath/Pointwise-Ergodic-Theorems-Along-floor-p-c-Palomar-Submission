module
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixPointwiseBound
public import FractionalPrimes.Literature.Twisted.SelectedComponentBoundedScale
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTaggedComponentAPI
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWTaggedComponentAPI
public import FractionalPrimes.Literature.Uniformity.ArchimedeanTwist
@[expose] public section
noncomputable section
namespace FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

 theorem boundedScaleLogarithmicAbsorption
    {X X₀ a B : ℝ} (hX : 1 < X) (hXX₀ : X ≤ X₀)
    (ha : 0 ≤ a) (hB : 0 ≤ B) :
    B ≤ (B * (Real.log X₀) ^ a) * (Real.log X) ^ (-a) := by
  have hL : 0 < Real.log X := Real.log_pos hX
  have hlog : Real.log X ≤ Real.log X₀ := Real.log_le_log (by linarith) hXX₀
  have hp := Real.rpow_le_rpow hL.le hlog ha
  have hpow : 0 < (Real.log X) ^ a := Real.rpow_pos_of_pos hL a
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ hpow).2 (mul_le_mul_of_nonneg_left hp hB)

/-- Bounded-scale part of the exact source PTW envelope estimate. -/
theorem mobiusSelectedPTWEnvelope_boundedScale
    {X H : ℕ} {X₀ a Q T : ℝ} (hX : 3 ≤ X)
    (hXX₀ : (X : ℝ) ≤ X₀) (hHX : H ≤ X)
    (ha : 0 ≤ a) (hQ : 1 ≤ Q)
    (ν : MobiusDyadicLabel (X : ℝ)) :
    residuePrefixEnvelope X H
      (fun n => complexPositiveIntegerZeroExtension (selectedMobiusPTWRawDyadicComponent ν) n *
        archimedeanTwist T (n : ℝ)) Q ≤
      (selectedComponentBoundedScaleConstant X₀ * (Real.log X₀) ^ a) *
        (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
  have hXR : (3 : ℝ) ≤ X := by exact_mod_cast hX
  have hB : 0 ≤ selectedComponentBoundedScaleConstant X₀ := by
    unfold selectedComponentBoundedScaleConstant
    have : 0 ≤ Real.log (8 * X₀) := Real.log_nonneg (by linarith)
    positivity
  have hEnv := residuePrefixEnvelope_le_pointwise X H
    (fun n => complexPositiveIntegerZeroExtension (selectedMobiusPTWRawDyadicComponent ν) n *
      archimedeanTwist T (n : ℝ)) hQ hB
  have hbound : residuePrefixEnvelope X H
      (fun n => complexPositiveIntegerZeroExtension (selectedMobiusPTWRawDyadicComponent ν) n *
        archimedeanTwist T (n : ℝ)) Q ≤
      (H : ℝ) * selectedComponentBoundedScaleConstant X₀ := by
    apply hEnv
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := by omega
    have hnX₀ : (n : ℝ) ≤ 2 * X₀ := by
      have hnR : (n : ℝ) ≤ (X : ℝ) + H := by exact_mod_cast hn'.2
      have hHR : (H : ℝ) ≤ X := by exact_mod_cast hHX
      linarith
    rw [norm_mul, norm_archimedeanTwist_eq_one, mul_one,
      complexPositiveIntegerZeroExtension_natCast _ ⟨n, hnpos⟩]
    simpa [selectedMobiusPTWRawDyadicComponent, Complex.norm_real, Real.norm_eq_abs] using
      mobiusDyadicComponent_abs_le_boundedScale hXR hXX₀ ν hnpos hnX₀
  have habs := boundedScaleLogarithmicAbsorption (by linarith : (1 : ℝ) < X)
    hXX₀ ha hB
  calc
    _ ≤ (H : ℝ) * selectedComponentBoundedScaleConstant X₀ := hbound
    _ ≤ (H : ℝ) * ((selectedComponentBoundedScaleConstant X₀ *
        (Real.log X₀) ^ a) * (Real.log (X : ℝ)) ^ (-a)) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ = _ := by ring

#print axioms mobiusSelectedPTWEnvelope_boundedScale
/-- Bounded-scale part of the exact source PTW envelope estimate. -/
theorem vonMangoldtSelectedPTWEnvelope_boundedScale
    {X H : ℕ} {X₀ a Q T : ℝ} (hX : 3 ≤ X)
    (hXX₀ : (X : ℝ) ≤ X₀) (hHX : H ≤ X)
    (ha : 0 ≤ a) (hQ : 1 ≤ Q)
    (ν : VonMangoldtDyadicLabel (X : ℝ)) :
    residuePrefixEnvelope X H
      (fun n => complexPositiveIntegerZeroExtension (selectedVonMangoldtPTWRawDyadicComponent ν) n *
        archimedeanTwist T (n : ℝ)) Q ≤
      (selectedComponentBoundedScaleConstant X₀ * (Real.log X₀) ^ a) *
        (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
  have hXR : (3 : ℝ) ≤ X := by exact_mod_cast hX
  have hB : 0 ≤ selectedComponentBoundedScaleConstant X₀ := by
    unfold selectedComponentBoundedScaleConstant
    have : 0 ≤ Real.log (8 * X₀) := Real.log_nonneg (by linarith)
    positivity
  have hEnv := residuePrefixEnvelope_le_pointwise X H
    (fun n => complexPositiveIntegerZeroExtension (selectedVonMangoldtPTWRawDyadicComponent ν) n *
      archimedeanTwist T (n : ℝ)) hQ hB
  have hbound : residuePrefixEnvelope X H
      (fun n => complexPositiveIntegerZeroExtension (selectedVonMangoldtPTWRawDyadicComponent ν) n *
        archimedeanTwist T (n : ℝ)) Q ≤
      (H : ℝ) * selectedComponentBoundedScaleConstant X₀ := by
    apply hEnv
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := by omega
    have hnX₀ : (n : ℝ) ≤ 2 * X₀ := by
      have hnR : (n : ℝ) ≤ (X : ℝ) + H := by exact_mod_cast hn'.2
      have hHR : (H : ℝ) ≤ X := by exact_mod_cast hHX
      linarith
    rw [norm_mul, norm_archimedeanTwist_eq_one, mul_one,
      complexPositiveIntegerZeroExtension_natCast _ ⟨n, hnpos⟩]
    simpa [selectedVonMangoldtPTWRawDyadicComponent, Complex.norm_real, Real.norm_eq_abs] using
      vonMangoldtDyadicComponent_abs_le_boundedScale hXR hXX₀ ν hnpos hnX₀
  have habs := boundedScaleLogarithmicAbsorption (by linarith : (1 : ℝ) < X)
    hXX₀ ha hB
  calc
    _ ≤ (H : ℝ) * selectedComponentBoundedScaleConstant X₀ := hbound
    _ ≤ (H : ℝ) * ((selectedComponentBoundedScaleConstant X₀ *
        (Real.log X₀) ^ a) * (Real.log (X : ℝ)) ^ (-a)) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ = _ := by ring

#print axioms vonMangoldtSelectedPTWEnvelope_boundedScale
end FractionalPrimes.Literature.DirichletMean
end
