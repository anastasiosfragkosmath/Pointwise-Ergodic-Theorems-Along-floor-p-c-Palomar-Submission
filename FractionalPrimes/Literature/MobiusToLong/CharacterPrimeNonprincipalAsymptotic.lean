module
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeNonprincipalSplitBound
public import FractionalPrimes.Literature.MobiusToLong.PrincipalPrimeSumFromMobius
@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.MobiusToLong

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.Twisted
open Finset

/-- The nonprincipal branch of `lml:character-primes`, uniformly on the full
real range and for moduli bounded by a fixed logarithmic power. The constant
depends only on the MUF witness and on K,B, not on x, q, or χ. -/
theorem nonprincipalCharacterPrimeSumFromMobius
    (hMUF : MobiusUniformity) {K B : ℝ} (hK : 0 < K) (hB : 0 < B) :
    ∃ CΛ : ℝ, 0 < CΛ ∧
      ∀ x : ℝ, 3 ≤ x →
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
          (hχ : χ ≠ principalCharacter q)
          (hq : (q : ℝ) ≤ (Real.log x) ^ B),
          ‖∑ n ∈ Finset.Icc 1 (Nat.floor x),
            (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n‖ ≤
            CΛ * x * Real.rpow (Real.log x) (-K) := by
  have hE : 0 < K + 4 := by linarith
  obtain ⟨C₁, hC₁, hSplit⟩ :=
    nonprincipalCharacterPrimeSumHyperbolaBound hMUF
      (E := K + 4) (B := B) hE hB
  obtain ⟨x₁, hx₁9, hx₁log, hGrowth⟩ :=
    exists_principalPrime_large_threshold (K + B)
  let xExp : ℝ := Real.exp ((2 : ℝ) ^ (B + 1))
  let x₀ : ℝ := max x₁ xExp
  have hx₀9 : 9 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hx₁9 (le_max_left _ _)
  have hx₀log : 4 ≤ Real.log x₀ := by
    have hx₁pos : 0 < x₁ := by linarith
    have hx₁x₀ : x₁ ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
    exact hx₁log.trans (Real.log_le_log hx₁pos hx₁x₀)
  let Cbig : ℝ := 1 + (2 : ℝ) ^ (K + 6) * C₁
  let Csmall : ℝ := (1 + Real.log x₀) * Real.rpow (Real.log x₀) K
  let CΛ : ℝ := max Cbig Csmall
  have hCΛpos : 0 < CΛ := by
    apply lt_of_lt_of_le _ (le_max_left Cbig Csmall)
    dsimp [Cbig]
    positivity
  refine ⟨CΛ, hCΛpos, ?_⟩
  intro x hx q inst χ hχ hq
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hLnonneg : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsum_norm_le :
      ‖∑ n ∈ Finset.Icc 1 (Nat.floor x),
          (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n‖ ≤
        x * Real.log x := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x),
            ‖(vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n :=
          Finset.sum_le_sum fun n hn => by
            have hn' := Finset.mem_Icc.mp hn
            have hn0 : n ≠ 0 := by omega
            have hχn := dirichletCharacterNatHom_norm_le_one χ hn0
            calc
              ‖(vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n‖ =
                  vonMangoldtWeight n *
                    ‖dirichletCharacterNatHom χ n‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (vonMangoldtWeight_nonneg n)]
              _ ≤ vonMangoldtWeight n * 1 :=
                mul_le_mul_of_nonneg_left hχn (vonMangoldtWeight_nonneg n)
              _ = vonMangoldtWeight n := by ring
      _ ≤ x * Real.log x := vonMangoldt_Icc_floor_le hx
  by_cases hxlarge : x₀ ≤ x
  · have hx₁x : x₁ ≤ x :=
      le_trans (show x₁ ≤ x₀ by dsimp [x₀]; exact le_max_left _ _) hxlarge
    have hx9 : 9 ≤ x := hx₁9.trans hx₁x
    have hxExp : Real.exp ((2 : ℝ) ^ (B + 1)) ≤ x := by
      exact le_trans (show xExp ≤ x₀ by dsimp [x₀]; exact le_max_right _ _) hxlarge
    have hloglarge : (2 : ℝ) ^ (B + 1) ≤ Real.log x :=
      (Real.le_log_iff_exp_le hxpos).2 hxExp
    have hLge4 : 4 ≤ Real.log x :=
      hx₁log.trans (Real.log_le_log (by linarith) hx₁x)
    have hLge1 : 1 ≤ Real.log x := by linarith
    have hGrowthX :
        4 * Real.rpow (Real.log x) (K + B + 1) ≤ Real.sqrt x := by
      simpa [show K + B + 1 = (K + B) + 1 by ring] using
        hGrowth x hx₁x
    have hqpow :
        (q : ℝ) * Real.rpow (Real.log x) (K + 1) ≤
          Real.rpow (Real.log x) (K + B + 1) := by
      have hq' : (q : ℝ) ≤ Real.rpow (Real.log x) B := by
        simpa using hq
      calc
        (q : ℝ) * Real.rpow (Real.log x) (K + 1) ≤
            Real.rpow (Real.log x) B * Real.rpow (Real.log x) (K + 1) :=
          mul_le_mul_of_nonneg_right hq'
            (Real.rpow_nonneg hLnonneg (K + 1))
        _ = Real.rpow (Real.log x) (B + (K + 1)) :=
          (Real.rpow_add hLpos B (K + 1)).symm
        _ = Real.rpow (Real.log x) (K + B + 1) := by
          congr 1
          ring
    have hsmallFactor :
        2 * (q : ℝ) * Real.rpow (Real.log x) (K + 1) ≤ Real.sqrt x := by
      calc
        2 * (q : ℝ) * Real.rpow (Real.log x) (K + 1) =
            2 * ((q : ℝ) * Real.rpow (Real.log x) (K + 1)) := by ring
        _ ≤ 2 * Real.rpow (Real.log x) (K + B + 1) :=
          mul_le_mul_of_nonneg_left hqpow (by norm_num)
        _ ≤ 4 * Real.rpow (Real.log x) (K + B + 1) :=
          mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4)
            (Real.rpow_nonneg hLnonneg _)
        _ ≤ Real.sqrt x := hGrowthX
    have hprod :
        Real.rpow (Real.log x) (K + 1) * Real.rpow (Real.log x) (-K) =
          Real.log x := by
      calc
        _ = Real.rpow (Real.log x) ((K + 1) + (-K)) :=
          (Real.rpow_add hLpos (K + 1) (-K)).symm
        _ = Real.log x := by
          rw [show (K + 1) + (-K) = 1 by ring]
          norm_num [Real.rpow_one]
    have hlogAbsorb :
        2 * (q : ℝ) * Real.log x ≤
          Real.sqrt x * Real.rpow (Real.log x) (-K) := by
      calc
        2 * (q : ℝ) * Real.log x =
            2 * (q : ℝ) *
              (Real.rpow (Real.log x) (K + 1) *
                Real.rpow (Real.log x) (-K)) := by
          rw [hprod]
        _ = (2 * (q : ℝ) * Real.rpow (Real.log x) (K + 1)) *
              Real.rpow (Real.log x) (-K) := by ring
        _ ≤ Real.sqrt x * Real.rpow (Real.log x) (-K) :=
          mul_le_mul_of_nonneg_right hsmallFactor
            (Real.rpow_nonneg hLnonneg _)
    have hsmallAbsorb :
        2 * (q : ℝ) * Real.sqrt x * Real.log x ≤
          x * Real.rpow (Real.log x) (-K) := by
      calc
        2 * (q : ℝ) * Real.sqrt x * Real.log x =
            Real.sqrt x * (2 * (q : ℝ) * Real.log x) := by ring
        _ ≤ Real.sqrt x *
            (Real.sqrt x * Real.rpow (Real.log x) (-K)) :=
          mul_le_mul_of_nonneg_left hlogAbsorb (Real.sqrt_nonneg x)
        _ = x * Real.rpow (Real.log x) (-K) := by
          rw [← mul_assoc, ← pow_two, Real.sq_sqrt hxpos.le]
    have hlongPow :
        Real.rpow (Real.log x) (2 - (K + 4)) ≤
          Real.rpow (Real.log x) (-K) :=
      Real.rpow_le_rpow_of_exponent_le hLge1 (by linarith)
    have hlongAbsorb :
        (2 : ℝ) ^ ((K + 4) + 2) * C₁ * x *
            Real.rpow (Real.log x) (2 - (K + 4)) ≤
          (2 : ℝ) ^ (K + 6) * C₁ * x *
            Real.rpow (Real.log x) (-K) := by
      have hpow : (2 : ℝ) ^ ((K + 4) + 2) = (2 : ℝ) ^ (K + 6) := by
        congr 1
        ring
      rw [hpow]
      exact mul_le_mul_of_nonneg_left hlongPow
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) (K + 6))
          (by linarith [hC₁])) hxpos.le)
    have hraw := hSplit hx9 hloglarge (χ := χ) hχ hq
    have hlargeTotal :
        ‖∑ n ∈ Finset.Icc 1 (Nat.floor x),
            (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n‖ ≤
          Cbig * x * Real.rpow (Real.log x) (-K) := by
      calc
        _ ≤ 2 * (q : ℝ) * Real.sqrt x * Real.log x +
              (2 : ℝ) ^ ((K + 4) + 2) * C₁ * x *
                Real.rpow (Real.log x) (2 - (K + 4)) := hraw
        _ ≤ x * Real.rpow (Real.log x) (-K) +
              (2 : ℝ) ^ (K + 6) * C₁ * x *
                Real.rpow (Real.log x) (-K) :=
          add_le_add hsmallAbsorb hlongAbsorb
        _ = Cbig * x * Real.rpow (Real.log x) (-K) := by
          dsimp [Cbig]
          ring
    have hCbigCΛ : Cbig ≤ CΛ := le_max_left _ _
    calc
      _ ≤ Cbig * x * Real.rpow (Real.log x) (-K) := hlargeTotal
      _ ≤ CΛ * x * Real.rpow (Real.log x) (-K) := by
        have hfac : 0 ≤ x * Real.rpow (Real.log x) (-K) :=
          mul_nonneg hxpos.le (Real.rpow_nonneg hLnonneg _)
        calc
          Cbig * x * Real.rpow (Real.log x) (-K) =
              Cbig * (x * Real.rpow (Real.log x) (-K)) := by ring
          _ ≤ CΛ * (x * Real.rpow (Real.log x) (-K)) :=
            mul_le_mul_of_nonneg_right hCbigCΛ hfac
          _ = CΛ * x * Real.rpow (Real.log x) (-K) := by ring
  · have hxle : x ≤ x₀ := le_of_not_ge hxlarge
    have hx₀pos : 0 < x₀ := by linarith [hx₀9]
    have hlog₀pos : 0 < Real.log x₀ := Real.log_pos (by linarith [hx₀9])
    have hlogle : Real.log x ≤ Real.log x₀ :=
      Real.log_le_log (by linarith) hxle
    have hpowle :
        Real.rpow (Real.log x) K ≤ Real.rpow (Real.log x₀) K :=
      Real.rpow_le_rpow hLnonneg hlogle hK.le
    have hfactor :
        (1 + Real.log x) * Real.rpow (Real.log x) K ≤ Csmall := by
      dsimp [Csmall]
      calc
        (1 + Real.log x) * Real.rpow (Real.log x) K ≤
            (1 + Real.log x₀) * Real.rpow (Real.log x) K :=
          mul_le_mul_of_nonneg_right (add_le_add_right hlogle 1)
            (Real.rpow_nonneg hLnonneg K)
        _ ≤ (1 + Real.log x₀) * Real.rpow (Real.log x₀) K :=
          mul_le_mul_of_nonneg_left hpowle (by linarith [hlogle])
    have hpowNeg : 0 ≤ Real.rpow (Real.log x) (-K) :=
      Real.rpow_nonneg hLnonneg _
    have hprod :
        Real.rpow (Real.log x) K * Real.rpow (Real.log x) (-K) = 1 := by
      calc
        _ = Real.rpow (Real.log x) (K + (-K)) :=
          (Real.rpow_add hLpos K (-K)).symm
        _ = 1 := by
          rw [show K + (-K) = 0 by ring]
          norm_num [Real.rpow_zero]
    have hfactorAbsorb :
        1 + Real.log x ≤ Csmall * Real.rpow (Real.log x) (-K) := by
      calc
        1 + Real.log x =
            (1 + Real.log x) *
              (Real.rpow (Real.log x) K *
                Real.rpow (Real.log x) (-K)) := by
          rw [hprod]
          ring
        _ = ((1 + Real.log x) * Real.rpow (Real.log x) K) *
              Real.rpow (Real.log x) (-K) := by ring
        _ ≤ Csmall * Real.rpow (Real.log x) (-K) :=
          mul_le_mul_of_nonneg_right hfactor hpowNeg
    have hsmallRange :
        ‖∑ n ∈ Finset.Icc 1 (Nat.floor x),
            (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n‖ ≤
          Csmall * x * Real.rpow (Real.log x) (-K) := by
      calc
        _ ≤ x * Real.log x := hsum_norm_le
        _ ≤ x * (1 + Real.log x) :=
          mul_le_mul_of_nonneg_left (by linarith) hxpos.le
        _ ≤ x * (Csmall * Real.rpow (Real.log x) (-K)) :=
          mul_le_mul_of_nonneg_left hfactorAbsorb hxpos.le
        _ = Csmall * x * Real.rpow (Real.log x) (-K) := by ring
    have hCsmallCΛ : Csmall ≤ CΛ := le_max_right _ _
    calc
      _ ≤ Csmall * x * Real.rpow (Real.log x) (-K) := hsmallRange
      _ ≤ CΛ * x * Real.rpow (Real.log x) (-K) := by
        have hfac : 0 ≤ x * Real.rpow (Real.log x) (-K) :=
          mul_nonneg hxpos.le hpowNeg
        calc
          Csmall * x * Real.rpow (Real.log x) (-K) =
              Csmall * (x * Real.rpow (Real.log x) (-K)) := by ring
          _ ≤ CΛ * (x * Real.rpow (Real.log x) (-K)) :=
            mul_le_mul_of_nonneg_right hCsmallCΛ hfac
          _ = CΛ * x * Real.rpow (Real.log x) (-K) := by ring

end FractionalPrimes.Literature.MobiusToLong
