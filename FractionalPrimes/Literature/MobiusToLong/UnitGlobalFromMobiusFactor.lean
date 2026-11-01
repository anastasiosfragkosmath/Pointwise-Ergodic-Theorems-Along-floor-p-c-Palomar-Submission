module
public import FractionalPrimes.Literature.MobiusToLong.MobiusResidueCharacterBound
public import FractionalPrimes.Literature.MobiusToLong.VonMangoldtResidueCharacterBound
@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.MobiusToLong
open FractionalPrimes.Literature.Reciprocal

namespace FractionalPrimes.Literature.MobiusToLong

private theorem abs_real_sub_eq_complex_norm_sub (x y : ℝ) :
    |x - y| = ‖(x : ℂ) - (y : ℂ)‖ := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The real Möbius sum in the unit residue class `a (mod q)` through the
real cutoff `Y`, with the paper's inclusive `n ≤ Y` convention. -/
def mobiusUnitResidueSumReal (q : ℕ) (a : ℤ) (Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
    (if (a : ZMod q) = ((n : ℤ) : ZMod q) then
      (ArithmeticFunction.moebius n : ℝ) else 0)

/-- The real von Mangoldt sum in the unit residue class `a (mod q)` through
the real cutoff `Y`, with the paper's inclusive `n ≤ Y` convention. -/
def vonMangoldtUnitResidueSumReal (q : ℕ) (a : ℤ) (Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
    (if (a : ZMod q) = ((n : ℤ) : ZMod q) then
      vonMangoldtWeight n else 0)

/-- The exact unit-class Siegel–Walfisz property `USW` from
`lal:unit-global`, including its shared constant for both arithmetic sums. -/
def UnitGlobalProperty : Prop :=
  ∀ (K B : ℝ), 0 < K → 0 < B →
    ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 3 ≤ Y →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log Y) ^ B →
          ∀ a : ℤ, IsCoprime a (q : ℤ) →
            |mobiusUnitResidueSumReal q a Y| ≤
                C * Y * (Real.log Y) ^ (-K) ∧
              |vonMangoldtUnitResidueSumReal q a Y -
                  Y / (q.totient : ℝ)| ≤ C * Y * (Real.log Y) ^ (-K)

theorem mobiusUnitResidueSumReal_complex_eq {q : ℕ} (a : ℤ) (Y : ℝ) :
    (mobiusUnitResidueSumReal q a Y : ℂ) =
      ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (if (a : ZMod q) = ((n : ℤ) : ZMod q) then
          (ArithmeticFunction.moebius n : ℂ) else 0) := by
  rw [mobiusUnitResidueSumReal, Complex.ofReal_sum]
  simp only [Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : (a : ZMod q) = (n : ZMod q)
  · simp [h, Complex.ofReal_intCast]
  · simp [h, Complex.ofReal_intCast]

theorem vonMangoldtUnitResidueSumReal_complex_eq {q : ℕ} (a : ℤ) (Y : ℝ) :
    (vonMangoldtUnitResidueSumReal q a Y : ℂ) =
      ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (if (a : ZMod q) = ((n : ℤ) : ZMod q) then
          (vonMangoldtWeight n : ℂ) else 0) := by
  rw [vonMangoldtUnitResidueSumReal, Complex.ofReal_sum]
  simp only [Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : (a : ZMod q) = (n : ZMod q)
  · simp [h]
  · simp [h]

/-- The exact `MUF → USW` unit-class implication, with one constant uniform
in both `q`, `Y`, `a` and both estimates, as required by `lal:unit-global`. -/
theorem unitGlobalProperty_of_MUF (hMUF : MobiusUniformity) :
    UnitGlobalProperty := by
  intro K B hK hB
  obtain ⟨Cμ, hCμ, hMobius⟩ :=
    mobiusUnitResidueSum_norm_le_of_MUF hMUF hK hB
  obtain ⟨CΛ, hCΛ, hLambda⟩ :=
    vonMangoldtUnitResidueSum_error_norm_le_of_MUF hMUF hK hB
  let C : ℝ := max Cμ CΛ
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le (by linarith : 0 < Cμ) (le_max_left Cμ CΛ)
  refine ⟨C, hC, ?_⟩
  intro Y hY q hq hqY a ha
  letI : NeZero q := ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)⟩
  have hYpos : 0 < Y := by linarith
  have hlogpos : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlognonneg : 0 ≤ Real.log Y := hlogpos.le
  have hpow : 0 ≤ (Real.log Y) ^ (-K) := Real.rpow_nonneg hlognonneg _
  have hfactor : 0 ≤ Y * (Real.log Y) ^ (-K) :=
    mul_nonneg hYpos.le hpow
  have hμ := hMobius (q := q) hq hY a ha hqY
  have hΛ := hLambda (q := q) hq hY a ha hqY
  have hquotcast : ((Y / (q.totient : ℝ) : ℝ) : ℂ) =
      (Y : ℂ) / (q.totient : ℂ) := by
    rw [Complex.ofReal_div]
    norm_cast
  have hΛnorm :
      |vonMangoldtUnitResidueSumReal q a Y - Y / (q.totient : ℝ)| =
        ‖(vonMangoldtUnitResidueSumReal q a Y : ℂ) -
          (Y : ℂ) / (q.totient : ℂ)‖ := by
    have h := abs_real_sub_eq_complex_norm_sub
      (vonMangoldtUnitResidueSumReal q a Y) (Y / (q.totient : ℝ))
    rw [hquotcast] at h
    exact h
  have hμreal :
      |mobiusUnitResidueSumReal q a Y| ≤ Cμ * Y * (Real.log Y) ^ (-K) := by
    calc
      |mobiusUnitResidueSumReal q a Y| =
          ‖(mobiusUnitResidueSumReal q a Y : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖∑ n ∈ Finset.Icc 1 (Nat.floor Y),
            (if (a : ZMod q) = ((n : ℤ) : ZMod q) then
              (ArithmeticFunction.moebius n : ℂ) else 0)‖ := by
            rw [mobiusUnitResidueSumReal_complex_eq]
      _ ≤ Cμ * Y * (Real.log Y) ^ (-K) := hμ
  have hΛreal :
      |vonMangoldtUnitResidueSumReal q a Y - Y / (q.totient : ℝ)| ≤
          CΛ * Y * Real.rpow (Real.log Y) (-K) := by
    calc
      |vonMangoldtUnitResidueSumReal q a Y - Y / (q.totient : ℝ)| =
          ‖(vonMangoldtUnitResidueSumReal q a Y : ℂ) -
              (Y : ℂ) / (q.totient : ℂ)‖ := hΛnorm
      _ = ‖(∑ n ∈ Finset.Icc 1 (Nat.floor Y),
            (if (a : ZMod q) = ((n : ℤ) : ZMod q) then
              (vonMangoldtWeight n : ℂ) else 0)) -
              ((Y : ℂ) / (q.totient : ℂ))‖ := by
            rw [vonMangoldtUnitResidueSumReal_complex_eq]
      _ ≤ CΛ * Y * Real.rpow (Real.log Y) (-K) := hΛ
  have hscaleμ : Cμ * Y * (Real.log Y) ^ (-K) ≤
      C * Y * (Real.log Y) ^ (-K) := by
    calc
      Cμ * Y * (Real.log Y) ^ (-K) =
          Cμ * (Y * (Real.log Y) ^ (-K)) := by ring
      _ ≤ C * (Y * (Real.log Y) ^ (-K)) := by
        apply mul_le_mul_of_nonneg_right _ hfactor
        dsimp [C]
        exact le_max_left Cμ CΛ
      _ = C * Y * (Real.log Y) ^ (-K) := by ring
  have hscaleΛ : CΛ * Y * Real.rpow (Real.log Y) (-K) ≤
      C * Y * Real.rpow (Real.log Y) (-K) := by
    calc
      CΛ * Y * Real.rpow (Real.log Y) (-K) =
          CΛ * (Y * Real.rpow (Real.log Y) (-K)) := by ring
      _ ≤ C * (Y * Real.rpow (Real.log Y) (-K)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hYpos.le
          (Real.rpow_nonneg hlognonneg _))
        dsimp [C]
        exact le_max_right Cμ CΛ
      _ = C * Y * Real.rpow (Real.log Y) (-K) := by ring
  exact ⟨le_trans hμreal hscaleμ, le_trans hΛreal hscaleΛ⟩

#print axioms unitGlobalProperty_of_MUF

end FractionalPrimes.Literature.MobiusToLong
