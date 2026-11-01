module
public import FractionalPrimes.Literature.MobiusToLong.UnitGlobalFromMobiusFactor
public import FractionalPrimes.Literature.MobiusToLong.ReciprocalMobiusMoments
@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.MobiusToLong

namespace FractionalPrimes.Literature.LongArithmetic

/-- The Möbius sum over the integer interval `(X, X+L]` in one residue class. -/
def unitMobiusIntervalSum (q : ℕ) (a : ℤ) (X L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (X + L),
    if (a : ZMod q) = ((n : ℤ) : ZMod q) then
      (ArithmeticFunction.moebius n : ℝ) else 0

/-- The von Mangoldt sum over the integer interval `(X, X+L]` in one residue
class. -/
def unitVonMangoldtIntervalSum (q : ℕ) (a : ℤ) (X L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (X + L),
    if (a : ZMod q) = ((n : ℤ) : ZMod q) then
      vonMangoldtWeight n else 0

private theorem unitMobiusIntervalSum_eq_prefix_difference
    (q : ℕ) (a : ℤ) (X L : ℕ) :
    unitMobiusIntervalSum q a X L =
      mobiusUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
        mobiusUnitResidueSumReal q a (X : ℝ) := by
  rw [unitMobiusIntervalSum, sum_Ioc_eq_sum_Icc_sub_of_le
    (Nat.le_add_right X L)]
  simp only [mobiusUnitResidueSumReal, Nat.floor_natCast]

private theorem unitVonMangoldtIntervalSum_eq_prefix_difference
    (q : ℕ) (a : ℤ) (X L : ℕ) :
    unitVonMangoldtIntervalSum q a X L =
      vonMangoldtUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
        vonMangoldtUnitResidueSumReal q a (X : ℝ) := by
  rw [unitVonMangoldtIntervalSum, sum_Ioc_eq_sum_Icc_sub_of_le
    (Nat.le_add_right X L)]
  simp only [vonMangoldtUnitResidueSumReal, Nat.floor_natCast]

/-- The direct unit-class part of `lal:long-of-unit`: USW controls both
interval sums after subtracting the exact von Mangoldt main term. The same
USW constant works for both bounds. -/
theorem unitIntervalBounds_of_USW
    (hUSW : UnitGlobalProperty) {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R)
    {X L q : ℕ} (hX : 3 ≤ X)
    (hXL : (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ))
    (hLX : L ≤ X) (hq : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B)
    (a : ℤ) (ha : IsCoprime a (q : ℤ)) :
    ∃ C : ℝ, 0 < C ∧
      |unitMobiusIntervalSum q a X L| ≤
        3 * C * L * (Real.log (X : ℝ)) ^ (-A) ∧
      |unitVonMangoldtIntervalSum q a X L -
          (L : ℝ) / (q.totient : ℝ)| ≤
        3 * C * L * (Real.log (X : ℝ)) ^ (-A) := by
  let K : ℝ := A + R + 2
  have hK : 0 < K := by dsimp [K]; linarith
  obtain ⟨C, hC, hprefix⟩ := hUSW K B hK hB
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by linarith
  have hLle : (L : ℝ) ≤ (X : ℝ) := by exact_mod_cast hLX
  have hLnonneg : 0 ≤ (L : ℝ) := by positivity
  have hYle : ((X + L : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
    rw [Nat.cast_add]
    nlinarith
  have hYge3 : (3 : ℝ) ≤ ((X + L : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    nlinarith
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogXone : 1 ≤ Real.log (X : ℝ) := by
    have hexp1 : Real.exp 1 < 3 := by
      have h := Real.exp_one_lt_d9
      norm_num at h ⊢
      linarith
    apply (Real.le_log_iff_exp_le hXpos).2
    exact le_trans (le_of_lt hexp1) hXreal
  have hlogMono : Real.log (X : ℝ) ≤
      Real.log ((X + L : ℕ) : ℝ) := by
    apply Real.log_le_log hXpos
    rw [Nat.cast_add]
    exact le_add_of_nonneg_right (by positivity)
  have hlogYpos : 0 < Real.log ((X + L : ℕ) : ℝ) :=
    lt_of_lt_of_le hlogXpos hlogMono
  have hqY : (q : ℝ) ≤ (Real.log ((X + L : ℕ) : ℝ)) ^ B := by
    exact hqX.trans (Real.rpow_le_rpow hlogXpos.le hlogMono hB.le)
  have hKneg : -K ≤ 0 := by linarith
  have hpowMono :
      (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) ≤
        (Real.log (X : ℝ)) ^ (-K) :=
    Real.rpow_le_rpow_of_nonpos hlogXpos hlogMono hKneg
  have hpowerFinal :
      (Real.log (X : ℝ)) ^ (-K) * (Real.log (X : ℝ)) ^ R ≤
        (Real.log (X : ℝ)) ^ (-A) := by
    rw [← Real.rpow_add hlogXpos]
    have hexp : -K + R = -A - 2 := by dsimp [K]; ring
    rw [hexp]
    exact Real.rpow_le_rpow_of_exponent_le hlogXone (by linarith)
  have hXLmul : (X : ℝ) ≤ (L : ℝ) *
      (Real.log (X : ℝ)) ^ R := by
    have hcancel : (Real.log (X : ℝ)) ^ (-R) *
        (Real.log (X : ℝ)) ^ R = 1 := by
      rw [← Real.rpow_add hlogXpos]
      have : -R + R = 0 := by ring
      rw [this, Real.rpow_zero]
    have hmul := mul_le_mul_of_nonneg_right hXL
      (Real.rpow_nonneg hlogXpos.le R)
    calc
      (X : ℝ) = (X : ℝ) *
          ((Real.log (X : ℝ)) ^ (-R) * (Real.log (X : ℝ)) ^ R) := by
            rw [hcancel, mul_one]
      _ = ((X : ℝ) * (Real.log (X : ℝ)) ^ (-R)) *
          (Real.log (X : ℝ)) ^ R := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ R := hmul
  have hfinalScale : (X : ℝ) *
      (Real.log (X : ℝ)) ^ (-K) ≤
        (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
    calc
      (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) ≤
          ((L : ℝ) * (Real.log (X : ℝ)) ^ R) *
            (Real.log (X : ℝ)) ^ (-K) :=
        mul_le_mul_of_nonneg_right hXLmul
          (Real.rpow_nonneg hlogXpos.le _)
      _ = (L : ℝ) *
          ((Real.log (X : ℝ)) ^ (-K) * (Real.log (X : ℝ)) ^ R) := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) :=
        mul_le_mul_of_nonneg_left hpowerFinal hLnonneg
  letI : NeZero q := ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)⟩
  have hμX : |mobiusUnitResidueSumReal q a (X : ℝ)| ≤
      C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
    exact (hprefix (X : ℝ) (by exact_mod_cast hX) q hq hqX a ha).1
  have hμY :
      |mobiusUnitResidueSumReal q a ((X + L : ℕ) : ℝ)| ≤
        C * ((X + L : ℕ) : ℝ) *
          (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) := by
    exact (hprefix ((X + L : ℕ) : ℝ) hYge3 q hq hqY a ha).1
  have hΛX :
      |vonMangoldtUnitResidueSumReal q a (X : ℝ) -
          (X : ℝ) / (q.totient : ℝ)| ≤
        C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
    exact (hprefix (X : ℝ) (by exact_mod_cast hX) q hq hqX a ha).2
  have hΛY :
      |vonMangoldtUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
          ((X + L : ℕ) : ℝ) / (q.totient : ℝ)| ≤
        C * ((X + L : ℕ) : ℝ) *
          (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) := by
    exact (hprefix ((X + L : ℕ) : ℝ) hYge3 q hq hqY a ha).2
  have hμscale : 3 * C * (X : ℝ) *
      (Real.log (X : ℝ)) ^ (-K) ≤
        3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
    have hCpos : 0 ≤ C := le_of_lt hC
    calc
      3 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) =
          3 * C * ((X : ℝ) * (Real.log (X : ℝ)) ^ (-K)) := by ring
      _ ≤ 3 * C * ((L : ℝ) * (Real.log (X : ℝ)) ^ (-A)) :=
        mul_le_mul_of_nonneg_left hfinalScale (by positivity)
      _ = 3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by ring
  refine ⟨C, hC, ?_, ?_⟩
  · rw [unitMobiusIntervalSum_eq_prefix_difference]
    calc
      |mobiusUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
          mobiusUnitResidueSumReal q a (X : ℝ)| ≤
        |mobiusUnitResidueSumReal q a ((X + L : ℕ) : ℝ)| +
          |mobiusUnitResidueSumReal q a (X : ℝ)| := abs_sub _ _
      _ ≤ 3 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
        have hYbound :
            C * ((X + L : ℕ) : ℝ) *
                (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) ≤
              2 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
          calc
            _ ≤ C * (2 * (X : ℝ)) *
                (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) := by
                  apply mul_le_mul_of_nonneg_right
                  · exact mul_le_mul_of_nonneg_left hYle (le_of_lt hC)
                  · exact Real.rpow_nonneg hlogYpos.le _
            _ ≤ C * (2 * (X : ℝ)) *
                (Real.log (X : ℝ)) ^ (-K) := by
                  apply mul_le_mul_of_nonneg_left hpowMono
                  positivity
            _ = 2 * C * (X : ℝ) *
                (Real.log (X : ℝ)) ^ (-K) := by ring
        calc
          _ ≤ C * ((X + L : ℕ) : ℝ) *
                (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) +
              C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) :=
            add_le_add hμY hμX
          _ ≤ 2 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) +
              C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) :=
            add_le_add hYbound le_rfl
          _ = 3 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by ring
      _ ≤ 3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := hμscale
  · rw [unitVonMangoldtIntervalSum_eq_prefix_difference]
    have hlin :
        (vonMangoldtUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
            vonMangoldtUnitResidueSumReal q a (X : ℝ)) -
          (L : ℝ) / (q.totient : ℝ) =
        (vonMangoldtUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
            ((X + L : ℕ) : ℝ) / (q.totient : ℝ)) -
          (vonMangoldtUnitResidueSumReal q a (X : ℝ) -
            (X : ℝ) / (q.totient : ℝ)) := by
      push_cast
      ring
    rw [hlin]
    calc
      _ ≤
        |vonMangoldtUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
            ((X + L : ℕ) : ℝ) / (q.totient : ℝ)| +
          |vonMangoldtUnitResidueSumReal q a (X : ℝ) -
            (X : ℝ) / (q.totient : ℝ)| := abs_sub _ _
      _ ≤ 3 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
        have hYbound :
            C * ((X + L : ℕ) : ℝ) *
                (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) ≤
              2 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
          calc
            _ ≤ C * (2 * (X : ℝ)) *
                (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) := by
                  apply mul_le_mul_of_nonneg_right
                  · exact mul_le_mul_of_nonneg_left hYle (le_of_lt hC)
                  · exact Real.rpow_nonneg hlogYpos.le _
            _ ≤ C * (2 * (X : ℝ)) *
                (Real.log (X : ℝ)) ^ (-K) := by
                  apply mul_le_mul_of_nonneg_left hpowMono
                  positivity
            _ = 2 * C * (X : ℝ) *
                (Real.log (X : ℝ)) ^ (-K) := by ring
        calc
          _ ≤ C * ((X + L : ℕ) : ℝ) *
                (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) +
              C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) :=
            add_le_add hΛY hΛX
          _ ≤ 2 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) +
              C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) :=
            add_le_add hYbound le_rfl
          _ = 3 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by ring
      _ ≤ 3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := hμscale

#print axioms unitIntervalBounds_of_USW

end FractionalPrimes.Literature.LongArithmetic

end
