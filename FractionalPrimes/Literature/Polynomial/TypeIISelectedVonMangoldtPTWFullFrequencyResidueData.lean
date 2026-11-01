module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWTaggedLiveAggregate
public import FractionalPrimes.Literature.Twisted.FullFrequencyMellinData
public import FractionalPrimes.Literature.Twisted.SelectedComponentMass
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixEnvelope
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
@[expose] public section

/-! Full-frequency Mellin data for an actual von Mangoldt dyadic-component
residue prefix. The residue filter is the same integer-modulus predicate as
the source prefix, and the vertical twist is retained exactly. -/

noncomputable section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- The exact norm-one Mellin and residue weight in a selected von Mangoldt
component prefix. -/
def selectedVonMangoldtPTWResiduePrefixWeight
    (q : ℕ) (residue : ℤ) (T : ℝ) (n : ℕ) : ℂ :=
  archimedeanTwist T (n : ℝ) *
    if Int.ModEq (q : ℤ) (n : ℤ) residue then 1 else 0

/-- The selected von Mangoldt component coefficient in the residue prefix,
written with its source zero-extension and the exact norm-one weight. -/
def selectedVonMangoldtPTWResiduePrefixCoefficient
    {X : ℝ} (ν : VonMangoldtDyadicLabel X) (q : ℕ) (residue : ℤ)
    (T : ℝ) (n : ℕ) : ℂ :=
  complexPositiveIntegerZeroExtension
      (selectedVonMangoldtPTWRawDyadicComponent ν) (n : ℤ) *
    selectedVonMangoldtPTWResiduePrefixWeight q residue T n

theorem selectedVonMangoldtPTWResiduePrefixWeight_norm_le_one
    (q : ℕ) (residue : ℤ) (T : ℝ) (n : ℕ) :
    ‖selectedVonMangoldtPTWResiduePrefixWeight q residue T n‖ ≤ 1 := by
  by_cases hres : Int.ModEq (q : ℤ) (n : ℤ) residue
  · simp [selectedVonMangoldtPTWResiduePrefixWeight, hres,
      norm_archimedeanTwist_eq_one]
  · simp [selectedVonMangoldtPTWResiduePrefixWeight, hres]

theorem selectedVonMangoldtPTW_archimedeanTwist_eq_natCast_cpow
    {n : ℕ} (hn : 0 < n) (T : ℝ) :
    archimedeanTwist T (n : ℝ) =
      (n : ℂ) ^ (Complex.I * (T : ℂ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
    rw [hcast]
    exact (Complex.ofReal_log hnR.le).symm
  unfold archimedeanTwist
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  congr 1
  push_cast
  ring

/-- The exact coefficient convention on the positive natural integers:
source component, `ZMod q` residue indicator, and the `n^(iT)` twist. -/
theorem selectedVonMangoldtPTWResiduePrefixCoefficient_eq_zmod_cpow
    {X : ℝ} (ν : VonMangoldtDyadicLabel X) (q : ℕ) (residue : ℤ)
    (T : ℝ) {n : ℕ} (hn : 0 < n) :
    selectedVonMangoldtPTWResiduePrefixCoefficient ν q residue T n =
      if (n : ZMod q) = (residue : ZMod q) then
        toComplexArithmeticFunction (selectedVonMangoldtPTWRawDyadicComponent ν) n *
          (n : ℂ) ^ (Complex.I * (T : ℂ))
      else 0 := by
  have hraw :
      complexPositiveIntegerZeroExtension
          (selectedVonMangoldtPTWRawDyadicComponent ν) (n : ℤ) =
        toComplexArithmeticFunction (selectedVonMangoldtPTWRawDyadicComponent ν) n := by
    rw [complexPositiveIntegerZeroExtension_natCast
      (selectedVonMangoldtPTWRawDyadicComponent ν) ⟨n, hn⟩]
    exact (toComplexArithmeticFunction_apply
      (selectedVonMangoldtPTWRawDyadicComponent ν) ⟨n, hn⟩).symm
  by_cases hres : (n : ZMod q) = (residue : ZMod q)
  · have hresInt : (((n : ℤ) : ZMod q) = (residue : ZMod q) : Prop) := by
      simpa only [Int.cast_natCast] using hres
    have hmod : Int.ModEq (q : ℤ) (n : ℤ) residue :=
      (ZMod.intCast_eq_intCast_iff (n : ℤ) residue q).mp hresInt
    rw [selectedVonMangoldtPTWResiduePrefixCoefficient,
      selectedVonMangoldtPTWResiduePrefixWeight, hraw, if_pos hmod,
      selectedVonMangoldtPTW_archimedeanTwist_eq_natCast_cpow hn]
    simp only [hres, if_true]
    ring
  · have hresInt : ¬ (((n : ℤ) : ZMod q) = (residue : ZMod q)) := by
      simpa only [Int.cast_natCast] using hres
    have hmod : ¬ Int.ModEq (q : ℤ) (n : ℤ) residue := by
      intro h
      exact hres (by
        exact_mod_cast
          (ZMod.intCast_eq_intCast_iff (n : ℤ) residue q).2 h)
    rw [selectedVonMangoldtPTWResiduePrefixCoefficient,
      selectedVonMangoldtPTWResiduePrefixWeight, hraw, if_neg hmod, if_neg hres]
    simp

/-- The Mellin and selected-positive interval encodings have the same
positive integer points. -/
theorem vonMangoldtMellinIntervalIndices_eq_selectedPositiveInterval
    (x h : ℝ) :
    mellinIntervalIndices x (x + h) = selectedPositiveInterval x h := by
  ext n
  simp only [mellinIntervalIndices, selectedPositiveInterval,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hnlo, hnceil⟩, hx⟩
    refine ⟨⟨hnlo, ?_⟩, hx⟩
    have hupper : (n : ℝ) ≤ x + h := hx.2
    have hmax : (n : ℝ) ≤ max 0 (x + h) :=
      hupper.trans (le_max_right _ _)
    exact Nat.le_floor hmax
  · rintro ⟨⟨hnlo, hnfloor⟩, hx⟩
    refine ⟨⟨hnlo, ?_⟩, hx⟩
    have hupper : (n : ℝ) ≤ x + h := hx.2
    exact_mod_cast hupper.trans (Nat.le_ceil (x + h))

theorem selectedVonMangoldtPTWResidueCoefficient_support
    {X : ℝ} {ν : VonMangoldtDyadicLabel X}
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X))
    {q : ℕ} {residue : ℤ} {T : ℝ} {n : ℕ}
    (ha : selectedVonMangoldtPTWResiduePrefixCoefficient
      ν q residue T n ≠ 0) :
    X / (2 : ℝ) ^ 21 < (n : ℝ) ∧
      (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
  have hcomponent :
      vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0 := by
    intro hz
    have hraw :
        complexPositiveIntegerZeroExtension
          (selectedVonMangoldtPTWRawDyadicComponent ν) (n : ℤ) = 0 := by
      by_cases hn : 0 < n
      · rw [complexPositiveIntegerZeroExtension_natCast
          (selectedVonMangoldtPTWRawDyadicComponent ν) ⟨n, hn⟩]
        simp [selectedVonMangoldtPTWRawDyadicComponent, hz]
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        simp [complexPositiveIntegerZeroExtension]
    apply ha
    simp [selectedVonMangoldtPTWResiduePrefixCoefficient, hraw]
  exact vonMangoldtDyadicComponent_support_bounds hν hcomponent

private theorem selectedVonMangoldtPTWResiduePrefixCoefficient_eq_cast_mul_weight
    {X : ℝ} (ν : VonMangoldtDyadicLabel X) (q : ℕ) (residue : ℤ)
    (T : ℝ) {n : ℕ} (hn : 0 < n) :
    selectedVonMangoldtPTWResiduePrefixCoefficient ν q residue T n =
      (((vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n : ℝ) : ℂ) *
        selectedVonMangoldtPTWResiduePrefixWeight q residue T n) := by
  rw [selectedVonMangoldtPTWResiduePrefixCoefficient,
    complexPositiveIntegerZeroExtension_natCast
      (selectedVonMangoldtPTWRawDyadicComponent ν) ⟨n, hn⟩]
  rfl

/-- Full-frequency Mellin data for the exact selected von Mangoldt
residue-prefix coefficient. Its local mass uses the checked component-mass
estimate with the norm-one Mellin/residue weight. -/
noncomputable def selectedVonMangoldtPTWFullFrequencyResidueData
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    {ν : VonMangoldtDyadicLabel X}
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X))
    (H : ℝ) (hH : 0 < H) (hHX : H ≤ X)
    (q : ℕ) (residue : ℤ) (T : ℝ) : FullFrequencyMellinData := by
  have hX : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  have hXpos : 0 < X := by linarith
  have harg : (1 : ℝ) < (2 : ℝ) ^ 22 * X := by nlinarith
  have hlog : 0 < Real.log ((2 : ℝ) ^ 22 * X) := Real.log_pos harg
  have hKpos : 0 < selectedComponentK X := by
    unfold selectedComponentK
    positivity
  have h0pos : 0 < selectedComponentH0 X := by
    unfold selectedComponentH0
    exact Real.rpow_pos_of_pos (mul_pos (by positivity) hXpos) _
  have h0sqrt : selectedComponentH0 X ≤ Real.sqrt X :=
    selectedComponentH0_le_sqrt hXlarge
  have hsqrtX : Real.sqrt X ≤ X := by
    have hsqrt0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    have hsqrtSq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hXpos.le
    nlinarith
  have hweight : ∀ n,
      ‖selectedVonMangoldtPTWResiduePrefixWeight q residue T n‖ ≤ 1 := by
    intro n
    exact selectedVonMangoldtPTWResiduePrefixWeight_norm_le_one q residue T n
  have hsupport : ∀ n,
      selectedVonMangoldtPTWResiduePrefixCoefficient ν q residue T n ≠ 0 →
        X / (2 : ℝ) ^ 21 < (n : ℝ) ∧
          (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
    intro n hn
    exact selectedVonMangoldtPTWResidueCoefficient_support hν hn
  have hmass : ∀ (x h : ℝ), 0 ≤ h →
      (∑ n ∈ mellinIntervalIndices x (x + h),
        ‖selectedVonMangoldtPTWResiduePrefixCoefficient ν q residue T n‖) ≤
        selectedComponentK X * (h + selectedComponentH0 X) := by
    intro x h hh
    have hm := selectedComponentLocalMass_weighted X hXlarge
    have hmν := hm.2 ν hν
      (selectedVonMangoldtPTWResiduePrefixWeight q residue T) hweight x h hh
    rw [vonMangoldtMellinIntervalIndices_eq_selectedPositiveInterval x h]
    calc
      (∑ n ∈ selectedPositiveInterval x h,
          ‖selectedVonMangoldtPTWResiduePrefixCoefficient ν q residue T n‖) =
        ∑ n ∈ selectedPositiveInterval x h,
          ‖((vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n : ℝ) : ℂ) *
            selectedVonMangoldtPTWResiduePrefixWeight q residue T n‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnpos := (selectedPositiveInterval_mem_iff x h hh n).mp hn |>.1
          rw [selectedVonMangoldtPTWResiduePrefixCoefficient_eq_cast_mul_weight
            ν q residue T hnpos]
      _ ≤ selectedComponentK X * (h + selectedComponentH0 X) := hmν
  exact fullFrequencyMellinData X H (selectedComponentK X)
    (selectedComponentH0 X)
    (selectedVonMangoldtPTWResiduePrefixCoefficient ν q residue T)
    hX hH hHX hKpos.le h0pos (h0sqrt.trans hsqrtX) hsupport hmass

/-- On the full-frequency support, the constructed datum has the exact
coefficient formula used by the generic finite allocation identity. -/
theorem selectedVonMangoldtPTWFullFrequencyResidueData_coefficient_eq
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    {ν : VonMangoldtDyadicLabel X}
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X))
    (H : ℝ) (hH : 0 < H) (hHX : H ≤ X)
    (q : ℕ) (residue : ℤ) (T : ℝ)
    {n : ℕ} (hn : n ∈ fullFrequencySupportIndices X) :
    (selectedVonMangoldtPTWFullFrequencyResidueData
        hXlarge hν H hH hHX q residue T).a n =
      if (n : ZMod q) = (residue : ZMod q) then
        toComplexArithmeticFunction (selectedVonMangoldtPTWRawDyadicComponent ν) n *
          (n : ℂ) ^ (Complex.I * (T : ℂ))
      else 0 := by
  have hleft : 0 ≤ X / (2 : ℝ) ^ 21 := by positivity
  have hmem := (mellinIntervalIndices_mem_iff hleft n).1 hn
  have hnR : 0 < (n : ℝ) := lt_of_le_of_lt hleft hmem.1
  have hnpos : 0 < n := by exact_mod_cast hnR
  unfold selectedVonMangoldtPTWFullFrequencyResidueData
  simp only [fullFrequencyMellinData]
  exact selectedVonMangoldtPTWResiduePrefixCoefficient_eq_zmod_cpow
    ν q residue T hnpos

#print axioms selectedVonMangoldtPTW_archimedeanTwist_eq_natCast_cpow
#print axioms selectedVonMangoldtPTWResiduePrefixCoefficient_eq_zmod_cpow
#print axioms selectedVonMangoldtPTWFullFrequencyResidueData
#print axioms selectedVonMangoldtPTWFullFrequencyResidueData_coefficient_eq

end FractionalPrimes.Literature.DirichletMean

end
