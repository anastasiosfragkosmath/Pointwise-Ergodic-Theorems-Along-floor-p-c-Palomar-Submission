module
public import FractionalPrimes.Literature.MobiusToLong.ResidueCharacterExpansion
public import FractionalPrimes.Literature.Reciprocal.GlobalCharacterMobius
public import FractionalPrimes.Literature.LongArithmetic.ShiftedCharacterMobiusSeries
@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.Twisted

namespace FractionalPrimes.Literature.MobiusToLong

/-- The Möbius sum in a unit residue class is exactly its finite Dirichlet
character average.  This is the Möbius part of the `MUF → USW` argument. -/
theorem mobiusResidueSum_eq_characterAverage {q : ℕ} [NeZero q] (hq : 0 < q)
    (a : ℤ) (ha : IsCoprime a (q : ℤ)) (Y : ℝ) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
      (if (a : ZMod q) = ((n : ℤ) : ZMod q) then
        (ArithmeticFunction.moebius n : ℂ) else 0)) =
      (∑ χ : BlueprintCharacter q,
        star (evalInt χ a) * globalMobiusCharacterSum χ Y) /
          (q.totient : ℂ) := by
  rw [finiteResidueSum_eq_character_average hq a ha
    (Finset.Icc 1 (Nat.floor Y)) (fun n => (ArithmeticFunction.moebius n : ℂ))]
  congr 1
  apply Finset.sum_congr rfl
  intro χ hχ
  congr 1
  simp only [globalMobiusCharacterSum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have hn' := Finset.mem_Icc.mp hn
    omega
  rw [globalMobiusCharacterCoefficient_eq χ hn0]
  rw [dirichletCharacterNatHom_apply_of_ne_zero χ hn0]
  simp [evalInt]

/-- The exact Möbius unit-class estimate in `lal:unit-global`, conditionally
derived from the already formalized zero-frequency `MUF` character bound.
The uniform character estimate is averaged using the exact cardinality
`|X_q| = φ(q)`. -/
theorem mobiusUnitResidueSum_norm_le_of_MUF
    (hMUF : MobiusUniformity) {K B : ℝ} (hK : 0 < K) (hB : 0 < B)
    :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {q : ℕ} [NeZero q] (hq : 1 ≤ q) {Y : ℝ} (hY : 3 ≤ Y)
        (a : ℤ) (ha : IsCoprime a (q : ℤ))
        (hqY : (q : ℝ) ≤ (Real.log Y) ^ B),
        ‖∑ n ∈ Finset.Icc 1 (Nat.floor Y),
          (if (a : ZMod q) = ((n : ℤ) : ZMod q) then
            (ArithmeticFunction.moebius n : ℂ) else 0)‖ ≤
          C * Y * (Real.log Y) ^ (-K) := by
  obtain ⟨C, hC, hglobal⟩ := globalCharacterMobius hMUF hK hB
  refine ⟨C, hC, ?_⟩
  intro q inst hq Y hY a ha hqY
  have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hφnat : 0 < q.totient := Nat.totient_pos.mpr hqpos
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast hφnat
  have haUnit : IsUnit (a : ZMod q) :=
    (ZMod.coe_int_isUnit_iff_isCoprime a q).2 (isCoprime_comm.mpr ha)
  rw [mobiusResidueSum_eq_characterAverage hqpos a ha Y]
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hφ).2
  calc
    ‖∑ χ : BlueprintCharacter q,
        star (evalInt χ a) * globalMobiusCharacterSum χ Y‖ ≤
        ∑ χ : BlueprintCharacter q,
          ‖star (evalInt χ a) * globalMobiusCharacterSum χ Y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ χ : BlueprintCharacter q, C * Y * (Real.log Y) ^ (-K) := by
      apply Finset.sum_le_sum
      intro χ hχ
      have hchar : ‖evalInt χ a‖ = 1 := by
        simpa [evalInt] using (unit_value_norm χ haUnit)
      calc
        ‖star (evalInt χ a) * globalMobiusCharacterSum χ Y‖ =
            ‖evalInt χ a‖ * ‖globalMobiusCharacterSum χ Y‖ := by
          rw [norm_mul, norm_star]
        _ = ‖globalMobiusCharacterSum χ Y‖ := by rw [hchar]; norm_num
        _ ≤ C * Y * (Real.log Y) ^ (-K) := hglobal χ hY hq hqY
    _ = (q.totient : ℝ) * (C * Y * (Real.log Y) ^ (-K)) := by
      simp [blueprintCharacters_card]
    _ = C * Y * (Real.log Y) ^ (-K) * (q.totient : ℝ) := by ring

end FractionalPrimes.Literature.MobiusToLong

#print axioms FractionalPrimes.Literature.MobiusToLong.finiteResidueSum_eq_character_average
#print axioms FractionalPrimes.Literature.MobiusToLong.mobiusResidueSum_eq_characterAverage
#print axioms FractionalPrimes.Literature.MobiusToLong.mobiusUnitResidueSum_norm_le_of_MUF
