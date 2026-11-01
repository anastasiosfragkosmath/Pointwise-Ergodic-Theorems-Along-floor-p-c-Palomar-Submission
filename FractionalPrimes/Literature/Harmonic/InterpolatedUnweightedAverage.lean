module

public import FractionalPrimes.LpAverages
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Interpolation of the unweighted averages in time

The family is defined on `Lᵖ` by bundling the finite averages as continuous
linear maps. At integer times it is exactly the existing `unweightedAverage`.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- The positive dyadic rational times used by the short-variation theorem:
`m * 2^(-v)` with `m > 0` and `v ≥ 0`. The reciprocal form is exactly the
same real number and keeps the natural exponent explicit. -/
def interpolatedUnweightedTimeSet : Set ℝ :=
  {t | ∃ m : ℕ, 0 < m ∧ ∃ v : ℕ, t = (m : ℝ) / (2 : ℝ) ^ v}

theorem interpolatedUnweightedTimeSet_pos {t : ℝ}
    (ht : t ∈ interpolatedUnweightedTimeSet) : 0 < t := by
  rcases ht with ⟨m, hm, v, rfl⟩
  positivity

/-- The `Lᵖ` isometry induced by one iterate of the measure-preserving
system. -/
noncomputable def floorPowerShiftLpCLM {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : InvertibleSystem X) (c : ℝ) (n : ℕ) :
    Lp ℂ p S.μ →L[ℂ] Lp ℂ p S.μ :=
  (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
    (μ := S.μ) (μb := S.μ) ℂ
    (S.iterate (floorPower c n))
    (InvertibleSystem.measurePreserving_integerIterate S
      (floorPower c n))).toContinuousLinearMap

/-- The finite unweighted average `B_N` as a continuous linear map on every
`Lᵖ`, `1 ≤ p ≤ ∞`. -/
noncomputable def unweightedAverageLpCLM {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : InvertibleSystem X) (c : ℝ) (N : Scale) :
    Lp ℂ p S.μ →L[ℂ] Lp ℂ p S.μ :=
  (N.1 : ℂ)⁻¹ •
    ∑ n ∈ Finset.Icc 1 N.1, floorPowerShiftLpCLM (p := p) S c n

/-- The bundled average agrees almost everywhere with the source's
function-valued unweighted average. -/
theorem unweightedAverageLpCLM_apply_ae {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : InvertibleSystem X) (c : ℝ) (N : Scale)
    (f : Lp ℂ p S.μ) :
    (unweightedAverageLpCLM (p := p) S c N f : X → ℂ) =ᵐ[S.μ]
      unweightedAverage S c (f : X → ℂ) N := by
  rw [unweightedAverage_eq_smul_sum_shift_floorPower]
  rw [unweightedAverageLpCLM]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  have hsum := Lp.coeFn_finsetSum (Finset.Icc 1 N.1)
    (fun n => floorPowerShiftLpCLM (p := p) S c n f)
  have hsmul := Lp.coeFn_smul (N.1 : ℂ)⁻¹
    (∑ n ∈ Finset.Icc 1 N.1, floorPowerShiftLpCLM (p := p) S c n f)
  have hshift (n : ℕ) :
      (floorPowerShiftLpCLM (p := p) S c n f : X → ℂ) =ᵐ[S.μ]
        S.shift (floorPower c n) (f : X → ℂ) := by
    change (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
      (μ := S.μ) (μb := S.μ) ℂ
      (S.iterate (floorPower c n))
      (InvertibleSystem.measurePreserving_integerIterate S
        (floorPower c n)) f : X → ℂ) =ᵐ[S.μ]
        S.shift (floorPower c n) (f : X → ℂ)
    filter_upwards [Lp.coeFn_compMeasurePreserving f
      (InvertibleSystem.measurePreserving_integerIterate S (floorPower c n))]
      with x hx
    simpa [InvertibleSystem.shift] using hx
  have hterm : ∀ n,
      (floorPowerShiftLpCLM (p := p) S c n f : X → ℂ) =ᵐ[S.μ]
        S.shift (floorPower c n) (f : X → ℂ) := hshift
  filter_upwards [hsmul, hsum, ae_all_iff.2 hterm] with x hsmul hsum hterm
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul ⊢
  rw [hsmul, hsum]
  congr 1
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact hterm n

/-- Every finite unweighted average is a contraction on `Lᵖ` for `p ≥ 1`. -/
theorem unweightedAverageLpCLM_norm_le_one {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : InvertibleSystem X) (c : ℝ) (N : Scale) :
    ‖unweightedAverageLpCLM (p := p) S c N‖ ≤ 1 := by
  classical
  have hshift (n : ℕ) : ‖floorPowerShiftLpCLM (p := p) S c n‖ ≤ 1 := by
    change ‖(Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
      (μ := S.μ) (μb := S.μ) ℂ
      (S.iterate (floorPower c n))
      (InvertibleSystem.measurePreserving_integerIterate S
        (floorPower c n))).toContinuousLinearMap‖ ≤ 1
    exact LinearIsometry.norm_toContinuousLinearMap_le
      (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
        (μ := S.μ) (μb := S.μ) ℂ
        (S.iterate (floorPower c n))
        (InvertibleSystem.measurePreserving_integerIterate S
          (floorPower c n)))
  have hNcomplex : (N.1 : ℂ) ≠ 0 := by exact_mod_cast N.2.ne'
  calc
    ‖unweightedAverageLpCLM (p := p) S c N‖ ≤
        ‖(N.1 : ℂ)⁻¹‖ *
          ∑ n ∈ Finset.Icc 1 N.1, ‖floorPowerShiftLpCLM (p := p) S c n‖ := by
      rw [unweightedAverageLpCLM, norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(N.1 : ℂ)⁻¹‖ * ∑ _n ∈ Finset.Icc 1 N.1, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro n hn
      exact hshift n
    _ = 1 := by
      have hcard :
          (∑ _n ∈ Finset.Icc 1 N.1, (1 : ℝ)) = N.1 := by
        simp [Nat.card_Icc]
      rw [hcard, norm_inv]
      have hcast : ‖(N.1 : ℂ)‖ = (N.1 : ℝ) := by simp
      rw [hcast]
      have hNreal : (N.1 : ℝ) ≠ 0 := by exact_mod_cast N.2.ne'
      field_simp

/-- The paper's interpolation `\widetilde B_t` on `Lᵖ`. For `0<t≤1` it is
`B₁`; above one it linearly interpolates `B_floor(t)` and `B_(floor(t)+1)`.
The coefficients are real, regarded as complex scalars on the complex
`Lᵖ` space. -/
noncomputable def interpolatedUnweightedAverage {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : InvertibleSystem X) (c t : ℝ) (ht : 0 < t) :
    Lp ℂ p S.μ →L[ℂ] Lp ℂ p S.μ := by
  classical
  by_cases ht1 : t ≤ 1
  · exact unweightedAverageLpCLM (p := p) S c ⟨1, by norm_num⟩
  · let N : ℕ := ⌊t⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      have hgt : (1 : ℝ) < t := by
        by_contra hnot
        exact ht1 (le_of_not_gt hnot)
      exact Nat.le_floor (by exact_mod_cast hgt.le)
    let a : ℝ := t - (N : ℝ)
    exact ((1 - a : ℝ) : ℂ) •
        unweightedAverageLpCLM (p := p) S c ⟨N, by omega⟩ +
      (a : ℝ) • unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩

theorem interpolatedUnweightedAverage_at_integer {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : InvertibleSystem X) (c : ℝ)
    (N : ℕ) (hN : 1 ≤ N) :
    interpolatedUnweightedAverage (p := p) S c (N : ℝ) (by positivity) =
      unweightedAverageLpCLM (p := p) S c ⟨N, by omega⟩ := by
  classical
  by_cases hN1 : N = 1
  · subst N
    simp [interpolatedUnweightedAverage]
  · have hgt : (1 : ℝ) < (N : ℝ) := by
      have hN2 : 2 ≤ N := by omega
      exact_mod_cast hN2
    simp only [interpolatedUnweightedAverage, not_le_of_gt hgt]
    have hfloor : (⌊(N : ℝ)⌋₊ : ℝ) = N := by simp
    rw [hfloor]
    norm_num
    exact zero_smul ℝ
      (unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩)

/-- Between consecutive integers the interpolation fraction lies in `[0,1]`. -/
private theorem natFloorInterpolationFraction_bounds {t : ℝ} (ht : 1 < t) :
    0 ≤ t - (⌊t⌋₊ : ℝ) ∧ t - (⌊t⌋₊ : ℝ) ≤ 1 := by
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hnext : t < (⌊t⌋₊ : ℝ) + 1 := by
    exact_mod_cast (Nat.lt_floor_add_one t)
  constructor <;> linarith

/-- The interpolated averages remain contractions because their two
coefficients are nonnegative and sum to one. -/
theorem interpolatedUnweightedAverage_norm_le_one {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : InvertibleSystem X) (c t : ℝ) (ht : 0 < t) :
    ‖interpolatedUnweightedAverage (p := p) S c t ht‖ ≤ 1 := by
  classical
  by_cases ht1 : t ≤ 1
  · simp only [interpolatedUnweightedAverage, dif_pos ht1]
    exact unweightedAverageLpCLM_norm_le_one (p := p) S c ⟨1, by norm_num⟩
  · have htgt : (1 : ℝ) < t := by
      by_contra hnot
      exact ht1 (le_of_not_gt hnot)
    let N : ℕ := ⌊t⌋₊
    let a : ℝ := t - (N : ℝ)
    have hN : 1 ≤ N := by
      dsimp [N]
      exact Nat.le_floor (by exact_mod_cast htgt.le)
    have ha := natFloorInterpolationFraction_bounds htgt
    have hBN := unweightedAverageLpCLM_norm_le_one (p := p) S c ⟨N, by omega⟩
    have hBN1 := unweightedAverageLpCLM_norm_le_one (p := p) S c ⟨N + 1, by omega⟩
    simp only [interpolatedUnweightedAverage, dif_neg ht1]
    calc
      ‖((1 - a : ℝ) : ℂ) • unweightedAverageLpCLM (p := p) S c
            ⟨N, by omega⟩ +
          (a : ℝ) • unweightedAverageLpCLM (p := p) S c
            ⟨N + 1, by omega⟩‖ ≤
        ‖((1 - a : ℝ) : ℂ) • unweightedAverageLpCLM (p := p) S c
            ⟨N, by omega⟩‖ +
          ‖(a : ℝ) • unweightedAverageLpCLM (p := p) S c
            ⟨N + 1, by omega⟩‖ := norm_add_le _ _
      _ ≤ |1 - a| + |a| := by
        rw [norm_smul, norm_smul]
        calc
          ‖((1 - a : ℝ) : ℂ)‖ *
                ‖unweightedAverageLpCLM (p := p) S c ⟨N, by omega⟩‖ +
              ‖(a : ℝ)‖ *
                ‖unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩‖ ≤
            |1 - a| * 1 + |a| * 1 := by
              apply add_le_add
              · rw [Complex.norm_real, Real.norm_eq_abs]
                exact mul_le_mul_of_nonneg_left hBN (abs_nonneg _)
              · rw [Real.norm_eq_abs]
                exact mul_le_mul_of_nonneg_left hBN1 (abs_nonneg _)
          _ = |1 - a| + |a| := by ring
      _ = 1 := by
        have ha0 : 0 ≤ a := by dsimp [a, N]; exact ha.1
        have ha1 : a ≤ 1 := by dsimp [a, N]; exact ha.2
        rw [abs_of_nonneg (by linarith : 0 ≤ 1 - a), abs_of_nonneg ha0]
        ring

end

end FractionalPrimes

end
