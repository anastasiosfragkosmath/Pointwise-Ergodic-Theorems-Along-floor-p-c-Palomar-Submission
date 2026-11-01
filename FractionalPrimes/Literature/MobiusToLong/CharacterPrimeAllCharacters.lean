module
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeNonprincipalAsymptotic
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimePrincipalAsymptotic
@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.MobiusToLong

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.Twisted
open Finset

/-- All logarithmically bounded characters satisfy the prime-sum estimate,
with the principal term included exactly when the character is principal. -/
theorem characterPrimeSumFromMobius
    (hMUF : MobiusUniformity) {K B : ℝ} (hK : 0 < K) (hB : 0 < B) :
    ∃ CΛ : ℝ, 0 < CΛ ∧
      ∀ x : ℝ, 3 ≤ x →
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
          (hq : (q : ℝ) ≤ (Real.log x) ^ B),
          ‖(∑ n ∈ Finset.Icc 1 (Nat.floor x),
              (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n) -
            (if χ = principalCharacter q then (x : ℂ) else 0)‖ ≤
            CΛ * x * Real.rpow (Real.log x) (-K) := by
  obtain ⟨Cnp, hCnp, hNonprincipal⟩ :=
    nonprincipalCharacterPrimeSumFromMobius hMUF hK hB
  obtain ⟨Cp, hCp, hPrincipal⟩ :=
    principalCharacterPrimeSumFromMobius hMUF hK hB
  let CΛ : ℝ := max Cnp Cp
  have hCΛpos : 0 < CΛ := by
    exact lt_of_lt_of_le hCnp (le_max_left Cnp Cp)
  refine ⟨CΛ, hCΛpos, ?_⟩
  intro x hx q inst χ hq
  have hxpos : 0 < x := by linarith
  have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hfac : 0 ≤ x * Real.rpow (Real.log x) (-K) :=
    mul_nonneg hxpos.le (Real.rpow_nonneg hlognonneg _)
  by_cases hχ : χ = principalCharacter q
  · have hbound := hPrincipal x hx (χ := χ) hχ hq
    have hCpCΛ : Cp ≤ CΛ := le_max_right _ _
    calc
      _ ≤ Cp * x * Real.rpow (Real.log x) (-K) := by
        simpa [hχ] using hbound
      _ ≤ CΛ * x * Real.rpow (Real.log x) (-K) := by
        calc
          Cp * x * Real.rpow (Real.log x) (-K) =
              Cp * (x * Real.rpow (Real.log x) (-K)) := by ring
          _ ≤ CΛ * (x * Real.rpow (Real.log x) (-K)) :=
            mul_le_mul_of_nonneg_right hCpCΛ hfac
          _ = CΛ * x * Real.rpow (Real.log x) (-K) := by ring
  · have hbound := hNonprincipal x hx (χ := χ) hχ hq
    have hCnpCΛ : Cnp ≤ CΛ := le_max_left _ _
    calc
      _ = ‖∑ n ∈ Finset.Icc 1 (Nat.floor x),
            (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n‖ := by
        simp [hχ]
      _ ≤ Cnp * x * Real.rpow (Real.log x) (-K) := hbound
      _ ≤ CΛ * x * Real.rpow (Real.log x) (-K) := by
        calc
          Cnp * x * Real.rpow (Real.log x) (-K) =
              Cnp * (x * Real.rpow (Real.log x) (-K)) := by ring
          _ ≤ CΛ * (x * Real.rpow (Real.log x) (-K)) :=
            mul_le_mul_of_nonneg_right hCnpCΛ hfac
          _ = CΛ * x * Real.rpow (Real.log x) (-K) := by ring

end FractionalPrimes.Literature.MobiusToLong
