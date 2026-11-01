module

public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeHyperbolaSplit
public import FractionalPrimes.Literature.MobiusToLong.ElementaryLogarithmicSums

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.MobiusToLong

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Twisted
open Finset

/-- The short-factor part of the character-twisted von Mangoldt hyperbola
split is bounded by the periodic logarithmic-sum estimate. The cutoff remains
`floor √x`, and each inner sum retains `floor (x/d)`. -/
theorem nonprincipalCharacterSmallFactorBound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ principalCharacter q) {x : ℝ} (hx : 9 ≤ x) :
    ‖∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
        characterMobiusCoefficient χ d *
          (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
            dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ))‖ ≤
      2 * (q : ℝ) * Real.sqrt x * Real.log x := by
  classical
  have hxone : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hqnonneg : 0 ≤ (q : ℝ) := by positivity
  have hsqrt_le_x : Real.sqrt x ≤ x :=
    Real.sqrt_le_self_iff.mpr (Or.inr hxone)
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x))) :
      ‖characterMobiusCoefficient χ d *
          (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
            dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ))‖ ≤
        2 * (q : ℝ) * Real.log x := by
    have hd' := Finset.mem_Icc.mp hd
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd'.1
    have hdreal1 : 1 ≤ (d : ℝ) := by exact_mod_cast hd'.1
    have hdleRoot : (d : ℝ) ≤ Real.sqrt x := by
      calc
        (d : ℝ) ≤ (Nat.floor (Real.sqrt x) : ℝ) := by exact_mod_cast hd'.2
        _ ≤ Real.sqrt x := Nat.floor_le (by positivity)
    let y : ℝ := x / (d : ℝ)
    have hyone : 1 ≤ y := by
      dsimp [y]
      apply (le_div_iff₀ hdpos).2
      simpa using hdleRoot.trans hsqrt_le_x
    have hyx : y ≤ x := by
      dsimp [y]
      apply (div_le_iff₀ hdpos).2
      nlinarith [hxone, hdreal1]
    have hlogy_nonneg : 0 ≤ Real.log y := Real.log_nonneg hyone
    have hlogy_le : Real.log y ≤ Real.log x :=
      Real.log_le_log (by linarith [hyone]) hyx
    have hconvert :
        (∑ m ∈ Finset.Icc 1 (Nat.floor y),
          dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ)) =
        ∑ m ∈ Finset.Icc 1 (Nat.floor y),
          evalInt χ (m : ℤ) * (Real.log (m : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : m ≠ 0 := by
        have hm' := Finset.mem_Icc.mp hm
        omega
      rw [dirichletCharacterNatHom_apply_of_ne_zero χ hm0]
      simp [evalInt]
    have hlogsum := nonprincipal_character_log_sum_Icc_floor_norm_le χ hχ hyone
    have hinner :
        ‖∑ m ∈ Finset.Icc 1 (Nat.floor y),
          dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ)‖ ≤
            2 * (q : ℝ) * Real.log x := by
      calc
        _ = ‖∑ m ∈ Finset.Icc 1 (Nat.floor y),
              evalInt χ (m : ℤ) * (Real.log (m : ℝ) : ℂ)‖ := by rw [hconvert]
        _ ≤ 2 * (q : ℝ) * Real.log y := hlogsum
        _ ≤ 2 * (q : ℝ) * Real.log x :=
          mul_le_mul_of_nonneg_left hlogy_le (by positivity)
    have hd0 : d ≠ 0 := by omega
    have hcoeff : ‖characterMobiusCoefficient χ d‖ ≤ 1 := by
      rw [characterMobiusCoefficient_eq, norm_mul]
      have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      have hχd := dirichletCharacterNatHom_norm_le_one χ hd0
      calc
        ‖(ArithmeticFunction.moebius d : ℂ)‖ *
            ‖dirichletCharacterNatHom χ d‖ ≤ 1 * 1 :=
          mul_le_mul hμ hχd (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hxone
    calc
      _ = ‖characterMobiusCoefficient χ d‖ *
            ‖∑ m ∈ Finset.Icc 1 (Nat.floor y),
              dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ)‖ := by
        rw [norm_mul]
      _ ≤ ‖characterMobiusCoefficient χ d‖ *
            (2 * (q : ℝ) * Real.log x) :=
          mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
      _ ≤ 1 * (2 * (q : ℝ) * Real.log x) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = 2 * (q : ℝ) * Real.log x := by ring
  have hsum :
      ‖∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
          characterMobiusCoefficient χ d *
            (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
              dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ))‖ ≤
        ∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
          2 * (q : ℝ) * Real.log x := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
            ‖characterMobiusCoefficient χ d *
              (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
                dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun d hd => hterm d hd
  have hcoeffsum :
      (∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
        2 * (q : ℝ) * Real.log x) =
      (Nat.floor (Real.sqrt x) : ℝ) * (2 * (q : ℝ) * Real.log x) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hfloor : (Nat.floor (Real.sqrt x) : ℝ) ≤ Real.sqrt x :=
    Nat.floor_le (by positivity)
  have hconst : 0 ≤ 2 * (q : ℝ) * Real.log x :=
    mul_nonneg (mul_nonneg (by norm_num) hqnonneg) (Real.log_nonneg hxone)
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
          2 * (q : ℝ) * Real.log x := hsum
    _ = (Nat.floor (Real.sqrt x) : ℝ) * (2 * (q : ℝ) * Real.log x) := hcoeffsum
    _ ≤ Real.sqrt x * (2 * (q : ℝ) * Real.log x) :=
      mul_le_mul_of_nonneg_right hfloor hconst
    _ = 2 * (q : ℝ) * Real.sqrt x * Real.log x := by ring

end FractionalPrimes.Literature.MobiusToLong

end
