module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTaggedLiveAggregate
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFiniteMellinIdentity
public import FractionalPrimes.Literature.Polynomial.PolynomialMellinSeparation
public import FractionalPrimes.Literature.Twisted.SelectedComponentMass
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWRetainedBlocks
public import Mathlib.Tactic
@[expose] public section

/-! Source-derived coefficient, support, and cutoff premises for applying the
generic full-frequency finite Mellin allocation identity to one selected
Möbius type-II component. -/

noncomputable section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

private theorem selectedMobiusPTW_fullFrequencyFactorization
    {X : ℝ} {ν : MobiusDyadicLabel X}
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α) :
    toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) =
      toComplexArithmeticFunction
          (groupedDyadicFactor (dyadicMobiusCutoff X)
            (dyadicBinomialCoefficient ν.1 : ℂ)
            (selectedDyadicFactors (mobiusLabelFactors ν) W.I)) *
        toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
            (selectedDyadicFactors (mobiusLabelFactors ν) W.J)) *
        toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
            (selectedDyadicFactors (mobiusLabelFactors ν) W.J')) := by
  have hleft := mellinSeparation_toComplexArithmeticFunction_convolution
    W.v (complexPositiveDirichletConvolution W.a W.b1)
  have hright := mellinSeparation_toComplexArithmeticFunction_convolution
    W.a W.b1
  calc
    toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) =
        toComplexArithmeticFunction
          (complexPositiveDirichletConvolution W.v
            (complexPositiveDirichletConvolution W.a W.b1)) := by
      rw [W.factorization]
    _ = toComplexArithmeticFunction W.v *
          toComplexArithmeticFunction
            (complexPositiveDirichletConvolution W.a W.b1) := hleft
    _ = toComplexArithmeticFunction W.v *
          (toComplexArithmeticFunction W.a * toComplexArithmeticFunction W.b1) := by
      rw [hright]
    _ = toComplexArithmeticFunction W.v * toComplexArithmeticFunction W.a *
          toComplexArithmeticFunction W.b1 := by ring
    _ = _ := by rw [W.v_eq, W.a_eq, W.b1_eq]

/-- The exact raw selected-component coefficient identity lifts through the
source type-II factorization to the coefficient hypothesis of the generic
finite nonunit Mellin allocation theorem. The residue, vertical twist, and
support index set remain unchanged. -/
theorem selectedMobiusPTW_fullFrequencyCoefficient_eq_groupProduct
    {X : ℝ} {ν : MobiusDyadicLabel X}
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α)
    (d : FullFrequencyMellinData) {q : ℕ}
    (residue : ℤ) (T : ℝ)
    (hrawCoeff : ∀ n ∈ fullFrequencySupportIndices d.X,
      d.a n =
        if (n : ZMod q) = (residue : ZMod q) then
          toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) n *
            (n : ℂ) ^ (Complex.I * (T : ℂ))
        else 0) :
    ∀ n ∈ fullFrequencySupportIndices d.X,
      d.a n =
        if (n : ZMod q) = (residue : ZMod q) then
          (toComplexArithmeticFunction
              (groupedDyadicFactor (dyadicMobiusCutoff X)
                (dyadicBinomialCoefficient ν.1 : ℂ)
                (selectedDyadicFactors (mobiusLabelFactors ν) W.I)) *
            toComplexArithmeticFunction
              (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
                (selectedDyadicFactors (mobiusLabelFactors ν) W.J)) *
            toComplexArithmeticFunction
              (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
                (selectedDyadicFactors (mobiusLabelFactors ν) W.J'))) n *
              (n : ℂ) ^ (Complex.I * (T : ℂ))
        else 0 := by
  intro n hn
  have hfac := selectedMobiusPTW_fullFrequencyFactorization W
  simpa only [← hfac] using hrawCoeff n hn

/-- The selected three-group product is supported inside the precise
full-frequency annulus `(X/2^21,2^22 X]` from `ltw:absolute-data`. This uses
the original dyadic Möbius component support, not a wider product-of-group
interval. -/
theorem selectedMobiusPTW_fullFrequencyProduct_support
    {X : ℝ} (hX : 3 ≤ X) {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α) :
    ∀ n,
      (toComplexArithmeticFunction
          (groupedDyadicFactor (dyadicMobiusCutoff X)
            (dyadicBinomialCoefficient ν.1 : ℂ)
            (selectedDyadicFactors (mobiusLabelFactors ν) W.I)) *
        toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
            (selectedDyadicFactors (mobiusLabelFactors ν) W.J)) *
        toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
            (selectedDyadicFactors (mobiusLabelFactors ν) W.J'))) n ≠ 0 →
      n ∈ fullFrequencySupportIndices X := by
  intro n hn
  have hfac := selectedMobiusPTW_fullFrequencyFactorization W
  have hraw :
      toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) n ≠ 0 := by
    rw [hfac]
    exact hn
  have hnpos : 0 < n := by
    by_contra hnnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnnot
    subst n
    apply hraw
    simp [toComplexArithmeticFunction]
  have hraw' : selectedMobiusPTWRawDyadicComponent ν ⟨n, hnpos⟩ ≠ 0 := by
    rw [toComplexArithmeticFunction_apply
      (selectedMobiusPTWRawDyadicComponent ν) ⟨n, hnpos⟩] at hraw
    exact hraw
  have hcomponent :
      mobiusDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0 := by
    intro hz
    apply hraw'
    simp [selectedMobiusPTWRawDyadicComponent, hz]
  have hbounds := mobiusDyadicComponent_support_bounds hν hcomponent
  have hleft : 0 ≤ X / (2 : ℝ) ^ 21 := by positivity
  unfold fullFrequencySupportIndices
  exact (mellinIntervalIndices_mem_iff hleft n).2 hbounds

private theorem selectedMobiusPTW_decompositionC_ge_one :
    1 ≤ decompositionC := by
  have h200 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
  have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
  change (1 : ℝ) ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
  calc
    1 = 1 * 1 := by norm_num
    _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
      mul_le_mul h200 h81 (by norm_num) (by positivity)

/-- Exact factor support cutoffs and positivity for the three natural
ceilings used by the common finite allocation. -/
theorem selectedMobiusPTW_fullFrequencyFactorCutoffs
    {X : ℝ} (hX : 3 ≤ X) {ν : MobiusDyadicLabel X}
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α) :
    let N₁ := Nat.ceil (decompositionC * X ^ W.gamma)
    let N₂ := Nat.ceil (decompositionC * X ^ W.eta)
    let N₃ := Nat.ceil (decompositionC * X ^ W.eta')
    0 < N₁ ∧ 0 < N₂ ∧ 0 < N₃ ∧
      (∀ n, toComplexArithmeticFunction
          (groupedDyadicFactor (dyadicMobiusCutoff X)
            (dyadicBinomialCoefficient ν.1 : ℂ)
            (selectedDyadicFactors (mobiusLabelFactors ν) W.I)) n ≠ 0 →
        n ≤ N₁) ∧
      (∀ n, toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
            (selectedDyadicFactors (mobiusLabelFactors ν) W.J)) n ≠ 0 →
        n ≤ N₂) ∧
      (∀ n, toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
            (selectedDyadicFactors (mobiusLabelFactors ν) W.J')) n ≠ 0 →
        n ≤ N₃) := by
  dsimp
  have hXpos : 0 < X := by linarith
  have hC : 1 ≤ decompositionC := selectedMobiusPTW_decompositionC_ge_one
  have hsupp₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ)
        (selectedDyadicFactors (mobiusLabelFactors ν) W.I))
      (decompositionC⁻¹ * X ^ W.gamma)
      (decompositionC * X ^ W.gamma) := by
    simpa only [← W.v_eq] using W.v_support
  have hsupp₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
        (selectedDyadicFactors (mobiusLabelFactors ν) W.J))
      (decompositionC⁻¹ * X ^ W.eta)
      (decompositionC * X ^ W.eta) := by
    simpa only [← W.a_eq] using W.a_support
  have hsupp₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
        (selectedDyadicFactors (mobiusLabelFactors ν) W.J'))
      (decompositionC⁻¹ * X ^ W.eta')
      (decompositionC * X ^ W.eta') := by
    simpa only [← W.b1_eq] using W.b1_support
  have hpos₁ : 0 < decompositionC * X ^ W.gamma :=
    mul_pos (lt_of_lt_of_le (by norm_num) hC)
      (Real.rpow_pos_of_pos hXpos W.gamma)
  have hpos₂ : 0 < decompositionC * X ^ W.eta :=
    mul_pos (lt_of_lt_of_le (by norm_num) hC)
      (Real.rpow_pos_of_pos hXpos W.eta)
  have hpos₃ : 0 < decompositionC * X ^ W.eta' :=
    mul_pos (lt_of_lt_of_le (by norm_num) hC)
      (Real.rpow_pos_of_pos hXpos W.eta')
  refine ⟨Nat.ceil_pos.mpr hpos₁, Nat.ceil_pos.mpr hpos₂,
    Nat.ceil_pos.mpr hpos₃, ?_, ?_, ?_⟩
  · intro n hn
    have hcut := selectedMobiusPTW_allocated_cutoff_of_group_support
      hC (by norm_num : 1 ≤ (1 : ℕ)) hsupp₁ (by simpa using hn)
    simpa using hcut
  · intro n hn
    have hcut := selectedMobiusPTW_allocated_cutoff_of_group_support
      hC (by norm_num : 1 ≤ (1 : ℕ)) hsupp₂ (by simpa using hn)
    simpa using hcut
  · intro n hn
    have hcut := selectedMobiusPTW_allocated_cutoff_of_group_support
      hC (by norm_num : 1 ≤ (1 : ℕ)) hsupp₃ (by simpa using hn)
    simpa using hcut

/-- The product of the three source ceiling cutoffs dominates the upper
endpoint `2^22 X` of the full-frequency support. -/
theorem selectedMobiusPTW_fullFrequencyProduct_cutoff
    {X : ℝ} (hX : 3 ≤ X) {ν : MobiusDyadicLabel X}
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α) :
    let N₁ := Nat.ceil (decompositionC * X ^ W.gamma)
    let N₂ := Nat.ceil (decompositionC * X ^ W.eta)
    let N₃ := Nat.ceil (decompositionC * X ^ W.eta')
    ∀ n ∈ fullFrequencySupportIndices X, n ≤ N₁ * N₂ * N₃ := by
  dsimp
  intro n hn
  have hXpos : 0 < X := by linarith
  have hC200 : (2 : ℝ) ^ 200 ≤ decompositionC := by
    change (2 : ℝ) ^ 200 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
    calc
      (2 : ℝ) ^ 200 = (2 : ℝ) ^ 200 * 1 := by ring
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul_of_nonneg_left
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 81)) (by positivity)
  have hCcube : (2 : ℝ) ^ 22 ≤ decompositionC ^ 3 := by
    calc
      (2 : ℝ) ^ 22 ≤ (2 : ℝ) ^ 600 :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)
      _ = ((2 : ℝ) ^ 200) ^ 3 := by rw [← pow_mul]
      _ ≤ decompositionC ^ 3 :=
        pow_le_pow_left₀ (by positivity) hC200 3
  have hMproduct :
      (X ^ W.gamma) * (X ^ W.eta) * (X ^ W.eta') = X := by
    rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos,
      W.exponent_sum, Real.rpow_one]
  have hN₁ : decompositionC * X ^ W.gamma ≤
      (Nat.ceil (decompositionC * X ^ W.gamma) : ℝ) := Nat.le_ceil _
  have hN₂ : decompositionC * X ^ W.eta ≤
      (Nat.ceil (decompositionC * X ^ W.eta) : ℝ) := Nat.le_ceil _
  have hN₃ : decompositionC * X ^ W.eta' ≤
      (Nat.ceil (decompositionC * X ^ W.eta') : ℝ) := Nat.le_ceil _
  have hfacProd : decompositionC ^ 3 * X ≤
      ((Nat.ceil (decompositionC * X ^ W.gamma) : ℝ) *
        (Nat.ceil (decompositionC * X ^ W.eta) : ℝ) *
        (Nat.ceil (decompositionC * X ^ W.eta' : ℝ))) := by
    calc
      decompositionC ^ 3 * X =
          decompositionC ^ 3 *
            ((X ^ W.gamma) * (X ^ W.eta) * (X ^ W.eta')) := by
        exact congrArg (fun y : ℝ => decompositionC ^ 3 * y) hMproduct.symm
      _ = (decompositionC * X ^ W.gamma) *
            (decompositionC * X ^ W.eta) *
            (decompositionC * X ^ W.eta') := by ring
      _ ≤ (Nat.ceil (decompositionC * X ^ W.gamma) : ℝ) *
            (Nat.ceil (decompositionC * X ^ W.eta) : ℝ) *
            (Nat.ceil (decompositionC * X ^ W.eta' : ℝ) : ℝ) := by
        have h12 := mul_le_mul hN₁ hN₂
          (by positivity : 0 ≤ decompositionC * X ^ W.eta)
          (by positivity : 0 ≤ (Nat.ceil (decompositionC * X ^ W.gamma) : ℝ))
        have h123 := mul_le_mul h12 hN₃
          (by positivity : 0 ≤ decompositionC * X ^ W.eta')
          (by positivity : 0 ≤
            (Nat.ceil (decompositionC * X ^ W.gamma) : ℝ) *
              (Nat.ceil (decompositionC * X ^ W.eta) : ℝ))
        simpa [mul_assoc] using h123
  have hfull : (2 : ℝ) ^ 22 * X ≤
      ((Nat.ceil (decompositionC * X ^ W.gamma) : ℝ) *
        (Nat.ceil (decompositionC * X ^ W.eta) : ℝ) *
        (Nat.ceil (decompositionC * X ^ W.eta' : ℝ) : ℝ)) :=
    (mul_le_mul_of_nonneg_right hCcube hXpos.le).trans hfacProd
  have hupper : (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
    have hm := (mellinIntervalIndices_mem_iff
      (by positivity : 0 ≤ X / (2 : ℝ) ^ 21) n).1 hn
    exact hm.2
  have hcast : (n : ℝ) ≤
      ((Nat.ceil (decompositionC * X ^ W.gamma) *
        Nat.ceil (decompositionC * X ^ W.eta) *
        Nat.ceil (decompositionC * X ^ W.eta') : ℕ) : ℝ) := by
    calc
      (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := hupper
      _ ≤ _ := by
        have hcastProd :
            ((Nat.ceil (decompositionC * X ^ W.gamma) *
              Nat.ceil (decompositionC * X ^ W.eta) *
              Nat.ceil (decompositionC * X ^ W.eta') : ℕ) : ℝ) =
              (Nat.ceil (decompositionC * X ^ W.gamma) : ℝ) *
                (Nat.ceil (decompositionC * X ^ W.eta) : ℝ) *
                (Nat.ceil (decompositionC * X ^ W.eta') : ℝ) := by
          push_cast
          ring
        rw [hcastProd]
        exact hfull
  exact_mod_cast hcast

/-- The exact three generic finite-allocation premises, bundled for one
selected source witness. `hrawCoeff` is solely the coefficient convention of
the full-frequency data; the selected factorization, annular support, and
common cutoff are proved here. -/
theorem selectedMobiusPTW_fullFrequencyAllocationPremises
    {X : ℝ} (hX : 3 ≤ X) {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α)
    (d : FullFrequencyMellinData) (hdX : d.X = X)
    {q : ℕ} (residue : ℤ) (T : ℝ)
    (hrawCoeff : ∀ n ∈ fullFrequencySupportIndices d.X,
      d.a n =
        if (n : ZMod q) = (residue : ZMod q) then
          toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) n *
            (n : ℂ) ^ (Complex.I * (T : ℂ))
        else 0) :
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
      (∀ n ∈ fullFrequencySupportIndices d.X,
        n ≤ N₁ * N₂ * N₃) := by
  have hcut := selectedMobiusPTW_fullFrequencyFactorCutoffs hX W
  have hcoeff := selectedMobiusPTW_fullFrequencyCoefficient_eq_groupProduct
    W d residue T hrawCoeff
  have hsupport := selectedMobiusPTW_fullFrequencyProduct_support hX hν W
  have hproductCut := selectedMobiusPTW_fullFrequencyProduct_cutoff hX W
  refine ⟨hcut.1, hcut.2.1, hcut.2.2.1, hcut.2.2.2.1,
    hcut.2.2.2.2.1, hcut.2.2.2.2.2, ?_, ?_, ?_⟩
  · intro n hn
    simpa only [hdX] using hcoeff n (by simpa only [hdX] using hn)
  · intro n hn
    simpa only [hdX] using hsupport n hn
  · intro n hn
    have hXsupport : n ∈ fullFrequencySupportIndices X := by
      simpa only [hdX] using hn
    simpa only [hdX] using hproductCut n hXsupport

#print axioms selectedMobiusPTW_fullFrequencyCoefficient_eq_groupProduct
#print axioms selectedMobiusPTW_fullFrequencyProduct_support
#print axioms selectedMobiusPTW_fullFrequencyFactorCutoffs
#print axioms selectedMobiusPTW_fullFrequencyProduct_cutoff
#print axioms selectedMobiusPTW_fullFrequencyAllocationPremises

end FractionalPrimes.Literature.DirichletMean

end
