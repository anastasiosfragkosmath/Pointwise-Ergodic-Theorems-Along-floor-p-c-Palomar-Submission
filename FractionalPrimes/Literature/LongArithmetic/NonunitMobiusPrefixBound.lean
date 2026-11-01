module
public import FractionalPrimes.Literature.LongArithmetic.MobiusResidueUnitReduction
public import FractionalPrimes.Literature.LongArithmetic.UnitGlobalIntervalBounds
@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.MobiusToLong

namespace FractionalPrimes.Literature.LongArithmetic

/-- The natural-modulus and `ZMod`-indicator conventions for a residue
class agree when the natural representative lies in `[0,q)`. -/
theorem mobiusResidueSumReal_eq_mobiusUnitResidueSumReal
    {q a : ℕ} (hq : 0 < q) (ha : a < q) (Y : ℝ) :
    mobiusResidueSumReal q a Y =
      mobiusUnitResidueSumReal q (a : ℤ) Y := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  unfold mobiusResidueSumReal mobiusResidueSumNat
    mobiusUnitResidueSumReal
  apply Finset.sum_congr rfl
  intro n hn
  have hres :
      ((a : ℤ) : ZMod q) = ((n : ℤ) : ZMod q) ↔ n % q = a := by
    rw [ZMod.intCast_eq_intCast_iff']
    have hmodNat : a % q = n % q ↔ n % q = a := by
      rw [Nat.mod_eq_of_lt ha]
      omega
    rw [← Int.natCast_mod, ← Int.natCast_mod]
    exact_mod_cast hmodNat
  simp only [hres]

/-- The exact USW prefix estimate for a residue class after the gcd
reduction. The hypotheses `Y/g ≥ 3` and `q ≤ log(Y/g)^(B+1)` are precisely
the transformed range conditions used in the `lal:long-of-unit` source
argument. No squarefreeness assumption is needed: nonsquarefree gcds give a
zero sum by `mobiusResidueUnitReduction`. -/
theorem nonunitMobiusPrefixBound_of_USW
    (hUSW : UnitGlobalProperty) {K B : ℝ}
    (hK : 0 < K) (hB : 0 < B)
    {q a : ℕ} (hq : 0 < q) (ha : a < q) {Y : ℝ}
    (hYg : 3 ≤ Y / (Nat.gcd a q : ℝ))
    (hqYg : (q : ℝ) ≤
      (Real.log (Y / (Nat.gcd a q : ℝ))) ^ (B + 1)) :
    ∃ C : ℝ, 0 < C ∧
      |mobiusResidueSumReal q a Y| ≤
        (Nat.gcd a q : ℝ) * C *
          (Y / (Nat.gcd a q : ℝ)) *
            (Real.log (Y / (Nat.gcd a q : ℝ))) ^ (-K) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  let g : ℕ := Nat.gcd a q
  let R : Finset ℕ := mobiusResidueUnitRemainders q a
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_right a hq
  have hgposR : 0 < (g : ℝ) := by exact_mod_cast hgpos
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hgpos.ne')
  have hYlower : 3 * (g : ℝ) ≤ Y :=
    (le_div_iff₀ hgposR).mp hYg
  have hYone : 1 ≤ Y := by nlinarith
  have hYglog : 0 < Real.log (Y / (g : ℝ)) :=
    Real.log_pos (by linarith)
  obtain ⟨C, hC, hprefix⟩ :=
    hUSW K (B + 1) hK (by linarith : 0 < B + 1)
  have hred := mobiusResidueUnitReduction hq ha Y hYone
  refine ⟨C, hC, ?_⟩
  by_cases hsq : Squarefree g
  · obtain ⟨hcard, hdecomp⟩ := hred.2 (by simpa [g] using hsq)
    rw [hdecomp]
    rw [Finset.mul_sum]
    have hterm (b : ℕ) (hb : b ∈ R) :
        |(ArithmeticFunction.moebius g : ℝ) *
            mobiusResidueSumReal q b (Y / (g : ℝ))| ≤
          C * (Y / (g : ℝ)) *
            (Real.log (Y / (g : ℝ))) ^ (-K) := by
      have hb' : b ∈ mobiusResidueUnitRemainders q a := by
        simpa [R] using hb
      have hbmem : b ∈ (Finset.range q).filter
          (fun b => Nat.Coprime b q ∧
            b % (q / Nat.gcd a q) = a / Nat.gcd a q) := by
        simpa [mobiusResidueUnitRemainders] using hb'
      have hbq : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hbmem).1
      have hbcop : Nat.Coprime b q := (Finset.mem_filter.mp hbmem).2.1
      have hbcopZ : IsCoprime (b : ℤ) (q : ℤ) := by
        rw [Int.isCoprime_iff_nat_coprime]
        simpa using hbcop
      have hunit := hprefix (Y / (g : ℝ)) hYg q hq1 hqYg
        (b : ℤ) hbcopZ
      rw [mobiusResidueSumReal_eq_mobiusUnitResidueSumReal hq hbq]
      have hmu : |(ArithmeticFunction.moebius g : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := g))
      have hsumBound := hunit.1
      rw [abs_mul]
      calc
        |(ArithmeticFunction.moebius g : ℝ)| *
            |mobiusUnitResidueSumReal q (b : ℤ) (Y / (g : ℝ))| ≤
          1 * |mobiusUnitResidueSumReal q (b : ℤ) (Y / (g : ℝ))| :=
            mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ ≤ 1 * (C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K)) :=
            mul_le_mul_of_nonneg_left hsumBound (by norm_num)
        _ = C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K) := by ring
    have hsum :
        |∑ b ∈ R, (ArithmeticFunction.moebius g : ℝ) *
            mobiusResidueSumReal q b (Y / (g : ℝ))| ≤
          ∑ b ∈ R, C * (Y / (g : ℝ)) *
            (Real.log (Y / (g : ℝ))) ^ (-K) := by
      calc
        _ ≤ ∑ b ∈ R, |(ArithmeticFunction.moebius g : ℝ) *
              mobiusResidueSumReal q b (Y / (g : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b ∈ R, C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K) :=
          Finset.sum_le_sum fun b hb => hterm b (by simpa [R] using hb)
    have hMnonneg : 0 ≤ C * (Y / (g : ℝ)) *
        (Real.log (Y / (g : ℝ))) ^ (-K) := by positivity
    have hcardR : (R.card : ℝ) ≤ (g : ℝ) := by
      exact_mod_cast (by simpa [R, g] using hcard)
    calc
      |∑ b ∈ R, (ArithmeticFunction.moebius g : ℝ) *
          mobiusResidueSumReal q b (Y / (g : ℝ))| ≤
          (R.card : ℝ) *
            (C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K)) := by
        simpa [R] using hsum
      _ ≤ (g : ℝ) *
            (C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K)) :=
        mul_le_mul_of_nonneg_right hcardR hMnonneg
      _ = (Nat.gcd a q : ℝ) * C *
            (Y / (Nat.gcd a q : ℝ)) *
              (Real.log (Y / (Nat.gcd a q : ℝ))) ^ (-K) := by
        dsimp [g]
        ring
  · have hzero : mobiusResidueSumReal q a Y = 0 :=
      hred.1 (by simpa [g] using hsq)
    rw [hzero]
    simp only [abs_zero]
    positivity

end FractionalPrimes.Literature.LongArithmetic
