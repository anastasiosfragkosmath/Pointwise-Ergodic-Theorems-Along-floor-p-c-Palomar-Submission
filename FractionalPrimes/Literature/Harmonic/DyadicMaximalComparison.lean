module

public import FractionalPrimes.LpAverages
public import FractionalPrimes.VariationBasics
public import FractionalPrimes.DiscreteLpBridge
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option maxHeartbeats 600000

/-!
# The elementary dyadic comparison for unweighted fractional averages

This file isolates the positive-average comparison used in the maximal part
of `ha:dyadic`. It retains the exact finite `[1,N]` averages and dyadic
endpoint convention.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes
open MeasureTheory
open scoped ENNReal

/-- The exact `[1,N]` formula for the integer-shift average. -/
private theorem unweightedAverage_integerShift_apply
    (c : ℝ) (f : ℤ → ℂ) (N : Scale) (x : ℤ) :
    unweightedAverage integerShiftSystem c f N x =
      (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
        f (x - floorPower c n) := by
  simp [unweightedAverage, weightedAverage, integerShiftSystem_iterate_apply]

/-- The dyadic scale corresponding to the paper's index `k ≥ 0`. -/
def unweightedDyadicScale (k : ℕ) : Scale :=
  ⟨2 ^ k, by positivity⟩

/-- The unweighted averages along exactly the paper's dyadic scales. -/
noncomputable def unweightedDyadicFamily (c : ℝ) (f : ℤ → ℂ) :
    Scale → ℤ → ℂ := fun s =>
  unweightedAverage integerShiftSystem c f
    (unweightedDyadicScale (s.1 - 1))

/-- The pointwise all-scale maximal function, with the supremum taken in the
extended nonnegative reals. -/
noncomputable def unweightedIntegerMaximal (c : ℝ) (f : ℤ → ℂ) :
    ℤ → ℝ≥0∞ := fun x =>
  ⨆ N : Scale, ENNReal.ofReal ‖unweightedAverage integerShiftSystem c f N x‖

/-- The integer model's average is bounded by the average of the pointwise
absolute values, with the exact finite normalization. -/
theorem unweightedAverage_integerShift_norm_le_absAverage
    (c : ℝ) (f : ℤ → ℂ) (N : Scale) (x : ℤ) :
    ‖unweightedAverage integerShiftSystem c f N x‖ ≤
      ‖unweightedAverage integerShiftSystem c (fun y => (‖f y‖ : ℂ)) N x‖ := by
  rw [unweightedAverage_integerShift_apply,
    unweightedAverage_integerShift_apply]
  have hsum :
      ‖∑ n ∈ Finset.Icc 1 N.1, f (x - floorPower c n)‖ ≤
        ∑ n ∈ Finset.Icc 1 N.1, ‖f (x - floorPower c n)‖ := norm_sum_le _ _
  have hright :
      ‖∑ n ∈ Finset.Icc 1 N.1, (‖f (x - floorPower c n)‖ : ℂ)‖ =
        ∑ n ∈ Finset.Icc 1 N.1, ‖f (x - floorPower c n)‖ := by
    rw [← Complex.ofReal_sum]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun n hn => norm_nonneg _)]
  have hcoef : ‖(N.1 : ℂ)⁻¹‖ = (N.1 : ℝ)⁻¹ := by
    simp [norm_inv]
  rw [norm_mul]
  rw [norm_mul]
  rw [hcoef]
  rw [hright]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Every average between consecutive dyadic endpoints is pointwise bounded
by twice the next dyadic average of the absolute input. -/
theorem unweightedAverage_integerShift_norm_le_two_nextDyadic
    (c : ℝ) (f : ℤ → ℂ) (N : Scale) (k : ℕ) (x : ℤ)
    (hlo : 2 ^ k ≤ N.1) (hhi : N.1 ≤ 2 ^ (k + 1)) :
    ‖unweightedAverage integerShiftSystem c f N x‖ ≤
      2 * ‖unweightedAverage integerShiftSystem c
        (fun y => (‖f y‖ : ℂ)) (unweightedDyadicScale (k + 1)) x‖ := by
  let M : Scale := unweightedDyadicScale (k + 1)
  have hM : M.1 = 2 ^ (k + 1) := rfl
  have hNleM : N.1 ≤ M.1 := by rw [hM]; exact hhi
  have hsum :
      (∑ n ∈ Finset.Icc 1 N.1, ‖f (x - floorPower c n)‖) ≤
        ∑ n ∈ Finset.Icc 1 M.1, ‖f (x - floorPower c n)‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc (by omega) hNleM
    · intro n hn hnot
      exact norm_nonneg _
  have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hMpos : 0 < (M.1 : ℝ) := by exact_mod_cast M.2
  have hMN : (M.1 : ℝ) ≤ 2 * N.1 := by
    have hmnNat : 2 ^ (k + 1) ≤ 2 * N.1 := by
      rw [pow_succ]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 hlo
    rw [hM]
    exact_mod_cast hmnNat
  have hcoef : (N.1 : ℝ)⁻¹ ≤ 2 * (M.1 : ℝ)⁻¹ := by
    calc
      (N.1 : ℝ)⁻¹ = (1 : ℝ) / N.1 := by rw [one_div]
      _ ≤ 2 / M.1 := (div_le_div_iff₀ hNpos hMpos).2 (by nlinarith)
      _ = 2 * (M.1 : ℝ)⁻¹ := by rw [div_eq_mul_inv]
  calc
    ‖unweightedAverage integerShiftSystem c f N x‖ ≤
        (N.1 : ℝ)⁻¹ *
          ∑ n ∈ Finset.Icc 1 N.1, ‖f (x - floorPower c n)‖ :=
      by
        rw [unweightedAverage_integerShift_apply]
        rw [norm_mul]
        calc
          ‖(↑N.1 : ℂ)⁻¹‖ *
              ‖∑ n ∈ Finset.Icc 1 N.1, f (x - floorPower c n)‖ ≤
              ‖(↑N.1 : ℂ)⁻¹‖ *
                ∑ n ∈ Finset.Icc 1 N.1, ‖f (x - floorPower c n)‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
          _ = _ := by simp
    _ ≤ (N.1 : ℝ)⁻¹ *
          ∑ n ∈ Finset.Icc 1 M.1, ‖f (x - floorPower c n)‖ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2 * (M.1 : ℝ)⁻¹ *
          ∑ n ∈ Finset.Icc 1 M.1, ‖f (x - floorPower c n)‖ := by
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 2 * ‖unweightedAverage integerShiftSystem c
        (fun y => (‖f y‖ : ℂ)) M x‖ := by
      rw [unweightedAverage_integerShift_apply]
      rw [norm_mul]
      have hcoefM : ‖(M.1 : ℂ)⁻¹‖ = (M.1 : ℝ)⁻¹ := by
        simp [norm_inv]
      rw [hcoefM]
      have hnonneg :
          0 ≤ ∑ n ∈ Finset.Icc 1 M.1, ‖f (x - floorPower c n)‖ :=
        Finset.sum_nonneg fun n hn => norm_nonneg _
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnonneg]
      ring

/-- The first value and the homogeneous variation control every value in a
dyadic family, with its positive-integer scale reindexing made explicit. -/
theorem enorm_unweightedDyadicFamily_le_base_add_variation
    (c r : ℝ) (f : ℤ → ℂ) (x : ℤ) (hr : 0 < r) (s : Scale) :
    ENNReal.ofReal ‖unweightedDyadicFamily c f s x‖ ≤
      ENNReal.ofReal ‖unweightedDyadicFamily c f ⟨1, by omega⟩ x‖ +
        rVariationFun r (unweightedDyadicFamily c f) x := by
  let U : Scale → ℂ := fun t => unweightedDyadicFamily c f t x
  have hbase : (⟨1, by omega⟩ : Scale) ≤ s := by
    change 1 ≤ s.1
    have hspos : 0 < s.1 := by exact_mod_cast s.2
    omega
  rcases eq_or_lt_of_le hbase with heq | hlt
  · rw [← heq]
    exact le_add_of_nonneg_right bot_le
  · have hvariation := enorm_sub_le_rVariation r hr U hlt
    have htriangle : ‖U s‖ ≤ ‖U s - U ⟨1, by omega⟩‖ + ‖U ⟨1, by omega⟩‖ := by
      calc
        ‖U s‖ = ‖(U s - U ⟨1, by omega⟩) + U ⟨1, by omega⟩‖ := by
          congr 1
          abel
        _ ≤ ‖U s - U ⟨1, by omega⟩‖ + ‖U ⟨1, by omega⟩‖ := norm_add_le _ _
    calc
      ENNReal.ofReal ‖U s‖ ≤
          ENNReal.ofReal (‖U s - U ⟨1, by omega⟩‖ + ‖U ⟨1, by omega⟩‖) :=
        ENNReal.ofReal_le_ofReal htriangle
      _ = ENNReal.ofReal ‖U s - U ⟨1, by omega⟩‖ +
          ENNReal.ofReal ‖U ⟨1, by omega⟩‖ := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      _ ≤ rVariation r U + ENNReal.ofReal ‖U ⟨1, by omega⟩‖ :=
        add_le_add hvariation le_rfl
      _ = ENNReal.ofReal ‖unweightedDyadicFamily c f ⟨1, by omega⟩ x‖ +
          rVariationFun r (unweightedDyadicFamily c f) x := by
        rw [rVariationFun_apply]
        simp [U, add_comm]

/-- The all-scale maximal function is controlled pointwise by the first
dyadic value and dyadic variation. This is the positive-average comparison
in the maximal part of `ha:dyadic`. -/
theorem unweightedIntegerMaximal_le_dyadic_variation
    (c r : ℝ) (f : ℤ → ℂ) (x : ℤ) (hr : 0 < r) :
    unweightedIntegerMaximal c f x ≤
      2 * (ENNReal.ofReal ‖unweightedDyadicFamily c
          (fun y => (‖f y‖ : ℂ)) ⟨1, by omega⟩ x‖ +
        rVariationFun r (unweightedDyadicFamily c
          (fun y => (‖f y‖ : ℂ))) x) := by
  let g : ℤ → ℂ := fun y => (‖f y‖ : ℂ)
  let V : Scale → ℤ → ℂ := unweightedDyadicFamily c g
  have hdyadic (N : Scale) :
      ∃ k : ℕ, 2 ^ k ≤ N.1 ∧ N.1 ≤ 2 ^ (k + 1) := by
    let k := Nat.log2 N.1
    have hNne : N.1 ≠ 0 := N.2.ne'
    have hlo : 2 ^ Nat.log2 N.1 ≤ N.1 := by
      simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hNne
    have hhi' : N.1 < 2 ^ (Nat.log2 N.1 + 1) := by
      simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N.1
    exact ⟨k, by simpa [k] using hlo, (by simpa [k] using hhi'.le)⟩
  apply iSup_le
  intro N
  obtain ⟨k, hlo, hhi⟩ := hdyadic N
  let s : Scale := ⟨k + 2, by omega⟩
  have hfamily : V s =
      unweightedAverage integerShiftSystem c g (unweightedDyadicScale (k + 1)) := by
    funext y
    simp [V, s, unweightedDyadicFamily, unweightedDyadicScale]
  have hcomparison := unweightedAverage_integerShift_norm_le_two_nextDyadic
    c f N k x hlo hhi
  have hbasevar := enorm_unweightedDyadicFamily_le_base_add_variation
    c r g x hr s
  have hcomparisonENN :
      ENNReal.ofReal ‖unweightedAverage integerShiftSystem c f N x‖ ≤
        2 * ENNReal.ofReal ‖V s x‖ := by
    calc
      _ ≤ ENNReal.ofReal (2 * ‖unweightedAverage integerShiftSystem c g
          (unweightedDyadicScale (k + 1)) x‖) :=
        ENNReal.ofReal_le_ofReal hcomparison
      _ = 2 * ENNReal.ofReal ‖V s x‖ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hfamily]
        norm_num
  calc
    ENNReal.ofReal ‖unweightedAverage integerShiftSystem c f N x‖ ≤
        2 * ENNReal.ofReal ‖V s x‖ := hcomparisonENN
    _ ≤ 2 * (ENNReal.ofReal ‖V ⟨1, by omega⟩ x‖ +
        rVariationFun r V x) := by
      exact mul_le_mul_of_nonneg_left hbasevar (by norm_num)
    _ = 2 * (ENNReal.ofReal ‖unweightedDyadicFamily c g ⟨1, by omega⟩ x‖ +
        rVariationFun r (unweightedDyadicFamily c g) x) := rfl

/-- The maximal estimate follows from the corresponding dyadic variation
estimate on the absolute input. This is the final assembly step in the
maximal part of `ha:dyadic`. -/
theorem unweightedIntegerMaximal_eLpNorm_le_of_dyadicVariation
    {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (c : ℝ)
    (f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ))
    (C : ℝ≥0∞)
    (hvariation :
      eLpNorm
        (rVariationFun r (unweightedDyadicFamily c
          (fun x => (‖(f : ℤ → ℂ) x‖ : ℂ))))
        (ENNReal.ofReal p) Measure.count ≤
          C * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count) :
    eLpNorm (unweightedIntegerMaximal c (f : ℤ → ℂ))
        (ENNReal.ofReal p) Measure.count ≤
      2 * (1 + C) * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  let g : ℤ → ℂ := fun x => (‖(f : ℤ → ℂ) x‖ : ℂ)
  let base : ℤ → ℂ := unweightedDyadicFamily c g ⟨1, by omega⟩
  let A : ℤ → ℝ≥0∞ := fun x => ENNReal.ofReal ‖base x‖
  let W : ℤ → ℝ≥0∞ := rVariationFun r (unweightedDyadicFamily c g)
  have hpP : 1 ≤ P := by
    dsimp [P]
    exact (ENNReal.one_le_ofReal).2 (by linarith)
  letI : Fact (1 ≤ P) := ⟨hpP⟩
  have hg : AEStronglyMeasurable g Measure.count := AEStronglyMeasurable.of_discrete
  have hf : AEStronglyMeasurable (f : ℤ → ℂ) Measure.count :=
    AEStronglyMeasurable.of_discrete
  have hnormInput : eLpNorm g P Measure.count = eLpNorm (f : ℤ → ℂ) P Measure.count := by
    rw [← eLpNorm_norm g hg, ← eLpNorm_norm (f : ℤ → ℂ) hf]
    congr 1
    funext x
    simp [g, Complex.norm_real]
  have hfloorOne : floorPower c 1 = 1 := by
    simp [floorPower, Real.one_rpow]
  have hbaseEq : base = fun x => g (x - 1) := by
    funext x
    change unweightedAverage integerShiftSystem c g (⟨1, by omega⟩ : Scale) x = _
    rw [unweightedAverage_integerShift_apply]
    simp [hfloorOne]
  have hmp : MeasurePreserving (MeasurableEquiv.addLeft (-1 : ℤ))
      Measure.count Measure.count :=
    measurePreserving_add_left Measure.count (-1)
  have hshiftEq : (fun x : ℤ => g (x - 1)) =
      g ∘ MeasurableEquiv.addLeft (-1 : ℤ) := by
    funext x
    simp [MeasurableEquiv.addLeft, sub_eq_add_neg, add_comm]
  have hbaseNorm : eLpNorm base P Measure.count ≤ eLpNorm g P Measure.count := by
    rw [hbaseEq, hshiftEq]
    exact (eLpNorm_comp_measurePreserving hg hmp).le
  have hbase : eLpNorm A P Measure.count ≤ eLpNorm (f : ℤ → ℂ) P Measure.count := by
    have hAeq : A = ENNReal.ofReal ∘ (fun x => ‖base x‖) := by
      funext x
      rfl
    rw [hAeq, eLpNorm_ofReal]
    · calc
        eLpNorm (fun x => ‖base x‖) P Measure.count =
            eLpNorm base P Measure.count := eLpNorm_norm base
              AEStronglyMeasurable.of_discrete
        _ ≤ eLpNorm g P Measure.count := hbaseNorm
        _ = eLpNorm (f : ℤ → ℂ) P Measure.count := hnormInput
    · exact Filter.Eventually.of_forall fun x => norm_nonneg (base x)
  have hvariation' : eLpNorm W P Measure.count ≤
      C * eLpNorm (f : ℤ → ℂ) P Measure.count := by
    simpa [P, W, g] using hvariation
  have hpoint : ∀ x : ℤ,
      unweightedIntegerMaximal c (f : ℤ → ℂ) x ≤ 2 * (A x + W x) := by
    intro x
    simpa [A, W, g, base] using
      unweightedIntegerMaximal_le_dyadic_variation c r (f : ℤ → ℂ) x hr
  have hmajor :
      eLpNorm (unweightedIntegerMaximal c (f : ℤ → ℂ)) P Measure.count ≤
        eLpNorm (fun x => 2 * (A x + W x)) P Measure.count := by
    apply eLpNorm_mono_enorm_ae AEStronglyMeasurable.of_discrete
    filter_upwards with x
    simpa only [enorm_eq_self] using hpoint x
  calc
    eLpNorm (unweightedIntegerMaximal c (f : ℤ → ℂ)) P Measure.count ≤
        eLpNorm (fun x => 2 * (A x + W x)) P Measure.count := hmajor
    _ = eLpNorm (fun x => (A x + W x) + (A x + W x)) P Measure.count := by
      congr 1
      funext x
      simp [two_mul]
    _ ≤ eLpNorm (fun x => A x + W x) P Measure.count +
        eLpNorm (fun x => A x + W x) P Measure.count :=
      eLpNorm_add_le (p := P) (μ := Measure.count)
        (f := fun x => A x + W x) (g := fun x => A x + W x) hpP
    _ ≤ (eLpNorm A P Measure.count + eLpNorm W P Measure.count) +
        (eLpNorm A P Measure.count + eLpNorm W P Measure.count) := by
      exact add_le_add
        (eLpNorm_add_le (p := P) (μ := Measure.count) (f := A) (g := W) hpP)
        (eLpNorm_add_le (p := P) (μ := Measure.count) (f := A) (g := W) hpP)
    _ ≤ (eLpNorm (f : ℤ → ℂ) P Measure.count +
          C * eLpNorm (f : ℤ → ℂ) P Measure.count) +
        (eLpNorm (f : ℤ → ℂ) P Measure.count +
          C * eLpNorm (f : ℤ → ℂ) P Measure.count) := by
      exact add_le_add (add_le_add hbase hvariation')
        (add_le_add hbase hvariation')
    _ = 2 * (1 + C) * eLpNorm (f : ℤ → ℂ) P Measure.count := by ring

end FractionalPrimes.Literature.Harmonic

end
