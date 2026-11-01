module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFullFrequencySourcePremises
public import FractionalPrimes.Literature.Twisted.SelectedComponentMass
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixEnvelope
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
@[expose] public section

/-! The full-frequency datum for one selected Möbius component is built from
the exact residue-prefix summand used by the PTW envelope. The residue
restriction is the same `Int.ModEq` filter as `residuePrefixSum`; the Mellin
frequency shift is carried by the source archimedean twist. -/

noncomputable section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- The norm-one weight in the selected Möbius PTW residue prefix: source
frequency twist times the exact integer-modulus residue indicator. -/
def selectedMobiusPTWResiduePrefixWeight
    (q : ℕ) (residue : ℤ) (T : ℝ) (n : ℕ) : ℂ :=
  archimedeanTwist T (n : ℝ) *
    if Int.ModEq (q : ℤ) (n : ℤ) residue then 1 else 0

/-- The coefficient whose finite sums are the summands of the selected
component residue-prefix envelope. It is the exact zero-extension source
weight from `RestrictedPTWSelection.twistedPrefix`, restricted by the same
residue predicate used in `residuePrefixSum`. -/
def selectedMobiusPTWResiduePrefixCoefficient
    {X : ℝ} (ν : MobiusDyadicLabel X) (q : ℕ) (residue : ℤ)
    (T : ℝ) (n : ℕ) : ℂ :=
  complexPositiveIntegerZeroExtension
      (selectedMobiusPTWRawDyadicComponent ν) (n : ℤ) *
    selectedMobiusPTWResiduePrefixWeight q residue T n

theorem selectedMobiusPTWResiduePrefixWeight_norm_le_one
    (q : ℕ) (residue : ℤ) (T : ℝ) (n : ℕ) :
    ‖selectedMobiusPTWResiduePrefixWeight q residue T n‖ ≤ 1 := by
  by_cases hres : Int.ModEq (q : ℤ) (n : ℤ) residue
  · simp [selectedMobiusPTWResiduePrefixWeight, hres,
      norm_archimedeanTwist_eq_one]
  · simp [selectedMobiusPTWResiduePrefixWeight, hres]

theorem selectedMobiusPTW_archimedeanTwist_eq_natCast_cpow
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

/-- The exact coefficient formula needed by the finite nonunit allocation:
the PTW residue-prefix coefficient is the selected raw component, filtered
by `ZMod q`, and multiplied by the natural-integer `n^(iT)` twist. -/
theorem selectedMobiusPTWResiduePrefixCoefficient_eq_zmod_cpow
    {X : ℝ} (ν : MobiusDyadicLabel X) (q : ℕ) (residue : ℤ)
    (T : ℝ) {n : ℕ} (hn : 0 < n) :
    selectedMobiusPTWResiduePrefixCoefficient ν q residue T n =
      if (n : ZMod q) = (residue : ZMod q) then
        toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) n *
          (n : ℂ) ^ (Complex.I * (T : ℂ))
      else 0 := by
  have hraw :
      complexPositiveIntegerZeroExtension
          (selectedMobiusPTWRawDyadicComponent ν) (n : ℤ) =
        toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) n := by
    rw [complexPositiveIntegerZeroExtension_natCast
      (selectedMobiusPTWRawDyadicComponent ν) ⟨n, hn⟩]
    exact (toComplexArithmeticFunction_apply
      (selectedMobiusPTWRawDyadicComponent ν) ⟨n, hn⟩).symm
  by_cases hres : (n : ZMod q) = (residue : ZMod q)
  · have hresInt : (((n : ℤ) : ZMod q) = (residue : ZMod q) : Prop) := by
      simpa only [Int.cast_natCast] using hres
    have hmod : Int.ModEq (q : ℤ) (n : ℤ) residue :=
      (ZMod.intCast_eq_intCast_iff (n : ℤ) residue q).mp hresInt
    rw [selectedMobiusPTWResiduePrefixCoefficient,
      selectedMobiusPTWResiduePrefixWeight, hraw, if_pos hmod,
      selectedMobiusPTW_archimedeanTwist_eq_natCast_cpow hn]
    simp only [hres, if_true]
    ring
  · have hresInt : ¬ (((n : ℤ) : ZMod q) = (residue : ZMod q)) := by
      simpa only [Int.cast_natCast] using hres
    have hmod : ¬ Int.ModEq (q : ℤ) (n : ℤ) residue := by
      intro h
      exact hres (by
        exact_mod_cast
          (ZMod.intCast_eq_intCast_iff (n : ℤ) residue q).2 h)
    rw [selectedMobiusPTWResiduePrefixCoefficient,
      selectedMobiusPTWResiduePrefixWeight, hraw, if_neg hmod, if_neg hres]
    simp

/-- The two finite interval encodings use the same positive integer points. -/
theorem mellinIntervalIndices_eq_selectedPositiveInterval
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

theorem selectedMobiusPTWResidueCoefficient_support
    {X : ℝ} {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    {q : ℕ} {residue : ℤ} {T : ℝ} {n : ℕ}
    (ha : selectedMobiusPTWResiduePrefixCoefficient ν q residue T n ≠ 0) :
    X / (2 : ℝ) ^ 21 < (n : ℝ) ∧
      (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
  have hcomponent : mobiusDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0 := by
    intro hz
    have hraw :
        complexPositiveIntegerZeroExtension
          (selectedMobiusPTWRawDyadicComponent ν) (n : ℤ) = 0 := by
      by_cases hn : 0 < n
      · rw [complexPositiveIntegerZeroExtension_natCast
          (selectedMobiusPTWRawDyadicComponent ν) ⟨n, hn⟩]
        simp [selectedMobiusPTWRawDyadicComponent, hz]
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        simp [complexPositiveIntegerZeroExtension]
    apply ha
    rw [selectedMobiusPTWResiduePrefixCoefficient, hraw]
    simp
  exact mobiusDyadicComponent_support_bounds hν hcomponent

private theorem selectedMobiusPTWResiduePrefixCoefficient_eq_cast_mul_weight
    {X : ℝ} (ν : MobiusDyadicLabel X) (q : ℕ) (residue : ℤ)
    (T : ℝ) {n : ℕ} (hn : 0 < n) :
    selectedMobiusPTWResiduePrefixCoefficient ν q residue T n =
      (((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n : ℝ) : ℂ) *
        selectedMobiusPTWResiduePrefixWeight q residue T n) := by
  rw [selectedMobiusPTWResiduePrefixCoefficient,
    complexPositiveIntegerZeroExtension_natCast
      (selectedMobiusPTWRawDyadicComponent ν) ⟨n, hn⟩]
  rfl

/-- Full-frequency Mellin data for the exact selected source residue-prefix
coefficient. Its local mass is supplied by the checked selected-component
mass theorem with the norm-one Mellin/residue weight. -/
noncomputable def selectedMobiusPTWFullFrequencyResidueData
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
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
      ‖selectedMobiusPTWResiduePrefixWeight q residue T n‖ ≤ 1 := by
    intro n
    exact selectedMobiusPTWResiduePrefixWeight_norm_le_one q residue T n
  have hsupport : ∀ n,
      selectedMobiusPTWResiduePrefixCoefficient ν q residue T n ≠ 0 →
        X / (2 : ℝ) ^ 21 < (n : ℝ) ∧
          (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
    intro n hn
    exact selectedMobiusPTWResidueCoefficient_support hν hn
  have hmass : ∀ (x h : ℝ), 0 ≤ h →
      (∑ n ∈ mellinIntervalIndices x (x + h),
        ‖selectedMobiusPTWResiduePrefixCoefficient ν q residue T n‖) ≤
        selectedComponentK X * (h + selectedComponentH0 X) := by
    intro x h hh
    have hm := selectedComponentLocalMass_weighted X hXlarge
    have hmν := hm.1 ν hν
      (selectedMobiusPTWResiduePrefixWeight q residue T) hweight x h hh
    rw [mellinIntervalIndices_eq_selectedPositiveInterval x h]
    calc
      (∑ n ∈ selectedPositiveInterval x h,
          ‖selectedMobiusPTWResiduePrefixCoefficient ν q residue T n‖) =
        ∑ n ∈ selectedPositiveInterval x h,
          ‖((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n : ℝ) : ℂ) *
            selectedMobiusPTWResiduePrefixWeight q residue T n‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnpos :=
            (selectedPositiveInterval_mem_iff x h hh n).mp hn |>.1
          rw [selectedMobiusPTWResiduePrefixCoefficient_eq_cast_mul_weight
            ν q residue T hnpos]
      _ ≤ selectedComponentK X * (h + selectedComponentH0 X) := hmν
  exact fullFrequencyMellinData X H (selectedComponentK X)
    (selectedComponentH0 X)
    (selectedMobiusPTWResiduePrefixCoefficient ν q residue T)
    hX hH hHX hKpos.le h0pos (h0sqrt.trans hsqrtX) hsupport hmass

/-- On the exact full-frequency support, the constructed datum has the
coefficient formula required by the generic nonunit allocation theorem. -/
theorem selectedMobiusPTWFullFrequencyResidueData_coefficient_eq
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    (H : ℝ) (hH : 0 < H) (hHX : H ≤ X)
    (q : ℕ) (residue : ℤ) (T : ℝ)
    {n : ℕ} (hn : n ∈ fullFrequencySupportIndices X) :
    (selectedMobiusPTWFullFrequencyResidueData hXlarge hν H hH hHX
        q residue T).a n =
      if (n : ZMod q) = (residue : ZMod q) then
        toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) n *
          (n : ℂ) ^ (Complex.I * (T : ℂ))
      else 0 := by
  have hX : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  have hleft : 0 ≤ X / (2 : ℝ) ^ 21 := by positivity
  have hmem := (mellinIntervalIndices_mem_iff hleft n).1 hn
  have hnR : 0 < (n : ℝ) := lt_of_le_of_lt hleft hmem.1
  have hnpos : 0 < n := by exact_mod_cast hnR
  unfold selectedMobiusPTWFullFrequencyResidueData
  simp only [fullFrequencyMellinData]
  exact selectedMobiusPTWResiduePrefixCoefficient_eq_zmod_cpow
    ν q residue T hnpos

/-- Apply the previously checked allocation-premise package to the actual
residue-prefix data. This source-facing entry point has no free coefficient
identity premise: the coefficient formula follows from the data definition. -/
theorem selectedMobiusPTW_fullFrequencyAllocationPremises_of_residuePrefix
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α)
    (H : ℝ) (hH : 0 < H) (hHX : H ≤ X)
    (q : ℕ) (residue : ℤ) (T : ℝ) :
    let d := selectedMobiusPTWFullFrequencyResidueData hXlarge hν H hH hHX
      q residue T
    let a₁ := toComplexArithmeticFunction
      (groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ)
        (selectedDyadicFactors (mobiusLabelFactors ν) W.I))
    let a₂ := toComplexArithmeticFunction
      (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
        (selectedDyadicFactors (mobiusLabelFactors ν) W.J))
    let a₃ := toComplexArithmeticFunction
      (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
        (selectedDyadicFactors (mobiusLabelFactors ν) W.J'))
    let N₁ := Nat.ceil (decompositionC * X ^ W.gamma)
    let N₂ := Nat.ceil (decompositionC * X ^ W.eta)
    let N₃ := Nat.ceil (decompositionC * X ^ W.eta')
    0 < N₁ ∧ 0 < N₂ ∧ 0 < N₃ ∧
      (∀ n, a₁ n ≠ 0 → n ≤ N₁) ∧
      (∀ n, a₂ n ≠ 0 → n ≤ N₂) ∧
      (∀ n, a₃ n ≠ 0 → n ≤ N₃) ∧
      (∀ n ∈ fullFrequencySupportIndices d.X,
        d.a n = if (n : ZMod q) = (residue : ZMod q) then
          (a₁ * a₂ * a₃) n * (n : ℂ) ^ (Complex.I * (T : ℂ)) else 0) ∧
      (∀ n, (a₁ * a₂ * a₃) n ≠ 0 →
        n ∈ fullFrequencySupportIndices d.X) ∧
      (∀ n ∈ fullFrequencySupportIndices d.X, n ≤ N₁ * N₂ * N₃) := by
  let d := selectedMobiusPTWFullFrequencyResidueData hXlarge hν H hH hHX
    q residue T
  have hdX : d.X = X := rfl
  have hcoeff : ∀ n ∈ fullFrequencySupportIndices d.X,
      d.a n =
        if (n : ZMod q) = (residue : ZMod q) then
          toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) n *
            (n : ℂ) ^ (Complex.I * (T : ℂ))
        else 0 := by
    intro n hn
    have hnX : n ∈ fullFrequencySupportIndices X := by
      simpa only [hdX] using hn
    have h := selectedMobiusPTWFullFrequencyResidueData_coefficient_eq
      hXlarge hν H hH hHX q residue T hnX
    simpa only [d] using h
  simpa only [d] using selectedMobiusPTW_fullFrequencyAllocationPremises
    (by
      have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
      exact hbase.trans hXlarge)
    hν W d hdX residue T hcoeff

#print axioms selectedMobiusPTW_archimedeanTwist_eq_natCast_cpow
#print axioms selectedMobiusPTWResiduePrefixCoefficient_eq_zmod_cpow
#print axioms selectedMobiusPTWFullFrequencyResidueData
#print axioms selectedMobiusPTWFullFrequencyResidueData_coefficient_eq
#print axioms selectedMobiusPTW_fullFrequencyAllocationPremises_of_residuePrefix

end FractionalPrimes.Literature.DirichletMean

end
