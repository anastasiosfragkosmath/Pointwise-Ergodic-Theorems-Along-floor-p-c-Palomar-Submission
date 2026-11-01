module
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeCorrectionIdentity
public import FractionalPrimes.Literature.MobiusToLong.PrincipalPrimeSumFromMobius
@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.MobiusToLong

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.Twisted
open Finset

/-- The principal-character branch of `lml:character-primes`, including the
exact finite correction for primes dividing the modulus and the full real
cutoff range. -/
theorem principalCharacterPrimeSumFromMobius
    (hMUF : MobiusUniformity) {K B : ℝ} (hK : 0 < K) (hB : 0 < B) :
    ∃ CΛ : ℝ, 0 < CΛ ∧
      ∀ x : ℝ, 3 ≤ x →
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
          (hχ : χ = principalCharacter q)
          (hq : (q : ℝ) ≤ (Real.log x) ^ B),
          ‖(∑ n ∈ Finset.Icc 1 (Nat.floor x),
              (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n) -
            (x : ℂ)‖ ≤ CΛ * x * Real.rpow (Real.log x) (-K) := by
  obtain ⟨C₀, hC₀, hPrime⟩ := principalPrimeSumFromMobius hMUF hK
  obtain ⟨x₁, hx₁9, hx₁log, hGrowth⟩ :=
    exists_principalPrime_large_threshold (K + 1)
  let A : ℝ := B / Real.log 2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hApos : 0 < A := by dsimp [A]; positivity
  let x₀ : ℝ := max x₁ (A ^ 2)
  have hx₀9 : 9 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hx₁9 (le_max_left _ _)
  have hx₀log : 4 ≤ Real.log x₀ := by
    have hx₁pos : 0 < x₁ := by linarith
    have hx₁x₀ : x₁ ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
    exact hx₁log.trans (Real.log_le_log hx₁pos hx₁x₀)
  let Cbig : ℝ := C₀ + 1
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
  let P : ℝ := ∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n
  let S : ℝ := ∑ n ∈ Finset.Icc 1 (Nat.floor x),
    vonMangoldtWeight n * (if Nat.Coprime n q then (1 : ℝ) else 0)
  let M : ℝ := P - S
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
  have hcharSum :
      (∑ n ∈ Finset.Icc 1 (Nat.floor x),
          (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n) =
        (S : ℂ) := by
    dsimp [S]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    rw [principalCharacterNatHom_eq_coprime_indicator χ hχ hn0]
    by_cases hcop : Nat.Coprime n q
    · rw [if_pos hcop, if_pos hcop]
      simp
    · rw [if_neg hcop, if_neg hcop]
      simp
  have hq1 : 1 ≤ q := by
    have hqne : q ≠ 0 := NeZero.ne q
    omega
  have hmissing := principalCharacterMissingMass_le hx hq1
  have hMnonneg : 0 ≤ M := by
    simpa [P, S, M] using hmissing.1
  have hMmod : M ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log x := by
    simpa [P, S, M] using hmissing.2
  have hdecomp :
      (∑ n ∈ Finset.Icc 1 (Nat.floor x),
          (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n) -
          (x : ℂ) = (((P - x) - M : ℝ) : ℂ) := by
    rw [hcharSum]
    have hreal : S - x = (P - x) - M := by
      dsimp [M]
      ring
    exact_mod_cast hreal
  by_cases hxlarge : x₀ ≤ x
  · have hx₁x : x₁ ≤ x :=
      le_trans (show x₁ ≤ x₀ by dsimp [x₀]; exact le_max_left _ _) hxlarge
    have hx9 : 9 ≤ x := hx₁9.trans hx₁x
    have hLge4 : 4 ≤ Real.log x :=
      hx₁log.trans (Real.log_le_log (by linarith) hx₁x)
    have hA2x : A ^ 2 ≤ x :=
      le_trans (show A ^ 2 ≤ x₀ by dsimp [x₀]; exact le_max_right _ _) hxlarge
    have hAsqrt : A ≤ Real.sqrt x := by
      calc
        A = Real.sqrt (A ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hApos]
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hA2x
    have hGrowthX :
        4 * Real.rpow (Real.log x) (K + 2) ≤ Real.sqrt x := by
      simpa [show K + 2 = (K + 1) + 1 by ring] using hGrowth x hx₁x
    have hlogLnonneg : 0 ≤ Real.log (Real.log x) :=
      Real.log_nonneg (by linarith)
    have hlogLle : Real.log (Real.log x) ≤ Real.log x := by
      have h := Real.log_le_sub_one_of_pos hLpos
      linarith
    have hqlog : Real.log (q : ℝ) ≤ B * Real.log (Real.log x) := by
      have hq' : (q : ℝ) ≤ Real.rpow (Real.log x) B := by
        simpa using hq
      calc
        Real.log (q : ℝ) ≤ Real.log (Real.rpow (Real.log x) B) :=
          Real.log_le_log (by positivity) hq'
        _ = B * Real.log (Real.log x) := Real.log_rpow hLpos B
    have hqlogDiv :
        Real.log (q : ℝ) / Real.log 2 ≤ A * Real.log (Real.log x) := by
      calc
        Real.log (q : ℝ) / Real.log 2 ≤
            (B * Real.log (Real.log x)) / Real.log 2 :=
          div_le_div_of_nonneg_right hqlog hlog2pos.le
        _ = A * Real.log (Real.log x) := by dsimp [A]; ring
    have hMlog : M ≤ A * Real.log x * Real.log (Real.log x) := by
      calc
        M ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log x := hMmod
        _ ≤ (A * Real.log (Real.log x)) * Real.log x :=
          mul_le_mul_of_nonneg_right hqlogDiv hLnonneg
        _ = A * Real.log x * Real.log (Real.log x) := by ring
    have hpowGrowth :
        Real.rpow (Real.log x) (K + 2) ≤ Real.sqrt x / 4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      nlinarith [hGrowthX]
    have hAlogPow : A * Real.rpow (Real.log x) (K + 2) ≤ x := by
      calc
        A * Real.rpow (Real.log x) (K + 2) ≤ A * (Real.sqrt x / 4) :=
          mul_le_mul_of_nonneg_left hpowGrowth hApos.le
        _ ≤ x := by
          have hAsqrtProd : A * Real.sqrt x ≤ x := by
            calc
              A * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
                mul_le_mul_of_nonneg_right hAsqrt (Real.sqrt_nonneg x)
              _ = x := by rw [← pow_two, Real.sq_sqrt hxpos.le]
          nlinarith [hAsqrtProd]
    have hpowKprod :
        Real.rpow (Real.log x) (K + 2) * Real.rpow (Real.log x) (-K) =
          (Real.log x) ^ 2 := by
      calc
        _ = Real.rpow (Real.log x) ((K + 2) + (-K)) :=
          (Real.rpow_add hLpos (K + 2) (-K)).symm
        _ = Real.rpow (Real.log x) (2 : ℝ) := by congr 1 <;> ring
        _ = (Real.log x) ^ 2 := Real.rpow_two _
    have hMabsorb : M ≤ x * Real.rpow (Real.log x) (-K) := by
      have hMquadratic : M ≤ A * (Real.log x) ^ 2 := by
        calc
          M ≤ A * Real.log x * Real.log (Real.log x) := hMlog
          _ ≤ A * Real.log x * Real.log x :=
            mul_le_mul_of_nonneg_left hlogLle
              (mul_nonneg hApos.le hLnonneg)
          _ = A * (Real.log x) ^ 2 := by ring
      calc
        M ≤ A * (Real.log x) ^ 2 := hMquadratic
        _ = A * (Real.rpow (Real.log x) (K + 2) *
              Real.rpow (Real.log x) (-K)) := by
          rw [hpowKprod]
        _ = (A * Real.rpow (Real.log x) (K + 2)) *
              Real.rpow (Real.log x) (-K) := by ring
        _ ≤ x * Real.rpow (Real.log x) (-K) :=
          mul_le_mul_of_nonneg_right hAlogPow
            (Real.rpow_nonneg hLnonneg _)
    have hP : |P - x| ≤ C₀ * x * Real.rpow (Real.log x) (-K) := by
      simpa [P] using hPrime x hx
    have hlarge :
        ‖(∑ n ∈ Finset.Icc 1 (Nat.floor x),
            (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n) -
            (x : ℂ)‖ ≤ Cbig * x * Real.rpow (Real.log x) (-K) := by
      calc
        _ = |(P - x) - M| := by
          rw [hdecomp, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |P - x| + |M| := by
          simpa using abs_sub_le (P - x) 0 M
        _ = |P - x| + M := by rw [abs_of_nonneg hMnonneg]
        _ ≤ C₀ * x * Real.rpow (Real.log x) (-K) +
              x * Real.rpow (Real.log x) (-K) :=
          add_le_add hP hMabsorb
        _ = Cbig * x * Real.rpow (Real.log x) (-K) := by
          dsimp [Cbig]
          ring
    have hCbigCΛ : Cbig ≤ CΛ := le_max_left _ _
    calc
      _ ≤ Cbig * x * Real.rpow (Real.log x) (-K) := hlarge
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
        ‖(∑ n ∈ Finset.Icc 1 (Nat.floor x),
            (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n) -
            (x : ℂ)‖ ≤ Csmall * x * Real.rpow (Real.log x) (-K) := by
      calc
        _ ≤ x * (1 + Real.log x) := by
          calc
            _ ≤ ‖∑ n ∈ Finset.Icc 1 (Nat.floor x),
                  (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n‖ +
                ‖(x : ℂ)‖ := norm_sub_le _ _
            _ ≤ x * Real.log x + x := by
              apply add_le_add hsum_norm_le
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos.le]
            _ = x * (1 + Real.log x) := by ring
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
