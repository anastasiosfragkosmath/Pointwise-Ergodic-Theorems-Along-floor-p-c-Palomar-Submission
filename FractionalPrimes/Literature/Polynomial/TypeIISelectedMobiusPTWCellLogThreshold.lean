module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFixedWitnessAssembly
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import Mathlib.Tactic
@[expose] public section

/-! Cellwise quotient-log bookkeeping for the selected-Möbius PTW source
transfer. The threshold below controls only the source exponent margin; it is
separate from the uncapped-kernel power/log absorption threshold. -/

noncomputable section

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.Twisted

/-- A logarithmic threshold for the source margin `E_X/log X`. The first
entry absorbs the fixed decomposition constant; the second controls
`a log log X` by `log X`. -/
noncomputable def selectedMobiusPTWCellLogThreshold (a eps : ℝ) : ℝ :=
  max (max 1 ((3 * Real.log (2 * decompositionC)) / (eps / 2400)))
    ((2 * a / (eps / 2400)) ^ 2)

/-- Above the explicit cell-log threshold, the exact source error
`E_X=3 log(2C)+a log log X` is at most `eps/1200 * log X`. -/
theorem selectedMobiusPTW_cellSourceLogBudget_of_threshold
    {X a eps : ℝ} (ha : 0 ≤ a) (heps : 0 < eps)
    (hX : Real.exp (selectedMobiusPTWCellLogThreshold a eps) ≤ X) :
    3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X) ≤ eps / 1200 * Real.log X := by
  let δ : ℝ := eps / 2400
  let L : ℝ := Real.log X
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hthreshold : selectedMobiusPTWCellLogThreshold a eps ≤ L := by
    have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
    have hlog := Real.log_le_log (Real.exp_pos _) hX
    simpa only [Real.log_exp] using hlog
  have hLone : 1 ≤ L := by
    have hTfirst : max 1
        ((3 * Real.log (2 * decompositionC)) / (eps / 2400)) ≤
          selectedMobiusPTWCellLogThreshold a eps := le_max_left _ _
    have hTone : 1 ≤ selectedMobiusPTWCellLogThreshold a eps :=
      le_trans (le_max_left _ _) hTfirst
    exact le_trans hTone hthreshold
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hLnonneg : 0 ≤ L := hLpos.le
  have hCdecomp : 1 ≤ decompositionC := by
    change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
    have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul h2 h81 (by norm_num) (by positivity)
  have hC₀ : 1 ≤ (2 * decompositionC : ℝ) := by nlinarith
  have hC₀log : 0 ≤ Real.log (2 * decompositionC) := Real.log_nonneg hC₀
  have hA : (3 * Real.log (2 * decompositionC)) / δ ≤ L := by
    have hTfirst : max 1
        ((3 * Real.log (2 * decompositionC)) / (eps / 2400)) ≤
          selectedMobiusPTWCellLogThreshold a eps := le_max_left _ _
    have hA' : (3 * Real.log (2 * decompositionC)) / (eps / 2400) ≤
        max 1 ((3 * Real.log (2 * decompositionC)) / (eps / 2400)) :=
      le_max_right _ _
    have hA'' := le_trans hA' hTfirst
    simpa [δ] using le_trans hA'' hthreshold
  have hA' : 3 * Real.log (2 * decompositionC) ≤ δ * L := by
    have hmul := (div_le_iff₀ hδ).mp hA
    nlinarith
  have hB : (2 * a / δ) ^ 2 ≤ L := by
    exact le_trans (le_max_right _ _) hthreshold
  have hratioNonneg : 0 ≤ 2 * a / δ := by positivity
  have hroot : 2 * a / δ ≤ Real.sqrt L :=
    (Real.le_sqrt hratioNonneg hLnonneg).2 hB
  have hrootMul : 2 * a ≤ δ * Real.sqrt L := by
    simpa [mul_comm] using (div_le_iff₀ hδ).mp hroot
  have hlogRoot : Real.log L ≤ 2 * Real.sqrt L := by
    have h := Real.log_le_rpow_div hLnonneg (by norm_num : 0 < (1 / 2 : ℝ))
    have hpow : L ^ (1 / 2 : ℝ) = Real.sqrt L := by
      rw [Real.sqrt_eq_rpow]
    rw [hpow] at h
    calc
      Real.log L ≤ Real.sqrt L / (1 / 2 : ℝ) := h
      _ = 2 * Real.sqrt L := by field_simp
  have hloga : a * Real.log L ≤ δ * L := by
    have hmul := mul_le_mul_of_nonneg_left hlogRoot ha
    have hrootL : 2 * a * Real.sqrt L ≤ δ * L := by
      calc
        2 * a * Real.sqrt L ≤ (δ * Real.sqrt L) * Real.sqrt L :=
          mul_le_mul_of_nonneg_right hrootMul (Real.sqrt_nonneg L)
        _ = δ * (Real.sqrt L) ^ 2 := by ring
        _ = δ * L := by rw [Real.sq_sqrt hLnonneg]
    nlinarith
  have hbudget :
      3 * Real.log (2 * decompositionC) + a * Real.log L ≤
        2 * δ * L := by
    nlinarith [hA', hloga]
  change 3 * Real.log (2 * decompositionC) + a * Real.log L ≤
    eps / 1200 * L
  calc
    3 * Real.log (2 * decompositionC) + a * Real.log L ≤
        2 * δ * L := hbudget
    _ = eps / 1200 * L := by dsimp [δ]; ring

/-- A live cell's own quotient base inherits the exact source exponent margin.
The lower geometry input is to be supplied only after a nonzero term has
selected this cell; no quotient geometry is required for zero cells. -/
theorem selectedMobiusPTW_liveCellLogConditions_of_threshold
    {X Y a eps : ℝ}
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hXlog : Real.exp (selectedMobiusPTWCellLogThreshold a eps) ≤ X)
    (hYlower : X ^ (1 / 2 : ℝ) ≤ Y) :
    3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X) ≤ Real.log X / 2 ∧
      2 * (3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X)) / Real.log Y ≤ eps / 300 ∧
      (2 : ℝ) ^ 16 ≤ Y := by
  have hXpos : 0 < X := by
    have hbase : (0 : ℝ) < (2 : ℝ) ^ 120 := by positivity
    exact lt_of_lt_of_le hbase hXlarge
  have hXone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have hlogXone : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans
      (by
        have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
        exact h3.trans hXlarge)
  have hE := selectedMobiusPTW_cellSourceLogBudget_of_threshold
    (X := X) ha heps0 hXlog
  have hEhalf : 3 * Real.log (2 * decompositionC) +
      a * Real.log (Real.log X) ≤ Real.log X / 2 := by
    have hepsbound : eps / 1200 ≤ (1 / 2 : ℝ) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hepsbound hlogXpos.le
    exact hE.trans (by nlinarith [hmul])
  have hYpos : 0 < Y := by
    have hpowpos : 0 < X ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hXpos _
    exact lt_of_lt_of_le hpowpos hYlower
  have hlogYlower : Real.log X / 2 ≤ Real.log Y := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hXpos _) hYlower
    rw [Real.log_rpow hXpos] at h
    nlinarith [h]
  have hlogYpos : 0 < Real.log Y := by nlinarith
  have hdev : 2 * (3 * Real.log (2 * decompositionC) +
      a * Real.log (Real.log X)) / Real.log Y ≤ eps / 300 := by
    apply (div_le_iff₀ hlogYpos).2
    have hleft : 2 * (3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X)) ≤ eps / 600 * Real.log X := by
      nlinarith [hE]
    have hright : eps / 600 * Real.log X ≤ eps / 300 * Real.log Y := by
      nlinarith [heps0, hlogYlower]
    exact hleft.trans hright
  have hpow32 : (2 : ℝ) ^ 32 ≤ X := by
    exact (by norm_num : (2 : ℝ) ^ 32 ≤ (2 : ℝ) ^ 120).trans hXlarge
  have hpowRoot : ((2 : ℝ) ^ 16) ^ 2 ≤ X := by
    calc
      ((2 : ℝ) ^ 16) ^ 2 = (2 : ℝ) ^ 32 := by norm_num
      _ ≤ X := hpow32
  have hroot : (2 : ℝ) ^ 16 ≤ Real.sqrt X :=
    (Real.le_sqrt (by positivity) hXpos.le).2 hpowRoot
  have hYlarge : (2 : ℝ) ^ 16 ≤ Y := by
    have hYsqrt : Real.sqrt X ≤ Y := by
      simpa only [Real.sqrt_eq_rpow] using hYlower
    exact hroot.trans hYsqrt
  exact ⟨hEhalf, hdev, hYlarge⟩

/-- The source-support adapter for a live allocated cell. The selected
I/J/J' and exponents stay fixed, and the quotient base is formed from this
cell's own dyadic indices. In particular, the lower-base hypothesis is
obtained only after supplying a nonzero witness for this cell. -/
theorem selectedMobiusPTW_actualAllocatedCell_logConditions_of_live
    {X z : ℝ} {d Q q : ℕ} {eps a : ℝ}
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hXlog : Real.exp (selectedMobiusPTWCellLogThreshold a eps) ≤ X)
    (hd : 0 < d) (hQ : 0 < Q) (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (γ η η' : ℝ) (hγsum : γ + η + η' = 1)
    (c : ℂ) (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length)) (T : ℝ) (j k l : ℕ)
    (hSupport₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs I))
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hSupport₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η))
    (hSupport₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η'))
    (hLive : ∃ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q)
      (t : ℝ),
      selectedMobiusPTWActualAllocatedWindowTerm (z := z) (q := q) c
        (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
        (selectedDyadicFactors fs J') r χ T γ η η' j k l t ≠ 0) :
    3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X) ≤ Real.log X / 2 ∧
      2 * (3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X)) /
        Real.log ((((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
          ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
          ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ))
          ≤ eps / 300 ∧
      (2 : ℝ) ^ 16 ≤
        (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
          ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
          ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) := by
  let Y : ℝ :=
    (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
      ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
      ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ)
  have hE := selectedMobiusPTW_cellSourceLogBudget_of_threshold
    (X := X) ha heps0 hXlog
  have hXgtone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos hXgtone
  have hEhalf : 3 * Real.log (2 * decompositionC) +
      a * Real.log (Real.log X) ≤ Real.log X / 2 := by
    have hepsbound : eps / 1200 ≤ (1 / 2 : ℝ) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hepsbound hlogXpos.le
    exact hE.trans (by nlinarith [hmul])
  have hgeom := selectedMobiusPTW_actualAllocatedCell_sourceQuotientGeometry_of_live
    a γ η η' hXlarge ha hd hQ hqfactor hqlog hEhalf hγsum c fs I J J'
    T j k l hSupport₁ hSupport₂ hSupport₃ hLive
  have hconditions := selectedMobiusPTW_liveCellLogConditions_of_threshold
    hXlarge ha heps0 heps hXlog hgeom.1
  rcases hconditions with ⟨hEhalf', hdev, hYlarge⟩
  exact ⟨hEhalf', by simpa [Y] using hdev, by simpa [Y] using hYlarge⟩

end FractionalPrimes.Literature.DirichletMean

#print axioms FractionalPrimes.Literature.DirichletMean.selectedMobiusPTW_cellSourceLogBudget_of_threshold
#print axioms FractionalPrimes.Literature.DirichletMean.selectedMobiusPTW_liveCellLogConditions_of_threshold
#print axioms FractionalPrimes.Literature.DirichletMean.selectedMobiusPTW_actualAllocatedCell_logConditions_of_live
