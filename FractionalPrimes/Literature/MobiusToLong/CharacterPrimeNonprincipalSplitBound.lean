module
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeHyperbolaSplit
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeSmallHalf
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeLargeHalfBound
@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.MobiusToLong

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.Twisted
open Finset

/-- The nonprincipal character-prime sum is bounded by the sum of the exact
short and strict large pieces of its square-root hyperbola decomposition.
Both pieces retain the blueprint's real floor cutoffs. -/
theorem nonprincipalCharacterPrimeSumHyperbolaBound
    (hMUF : MobiusUniformity) {E B : ℝ} (hE : 0 < E) (hB : 0 < B) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ {x : ℝ} (_hx : 9 ≤ x)
        (_hlog : (2 : ℝ) ^ (B + 1) ≤ Real.log x)
        {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
        (_hχ : χ ≠ principalCharacter q)
        (_hq : (q : ℝ) ≤ (Real.log x) ^ B),
        ‖∑ n ∈ Finset.Icc 1 (Nat.floor x),
          (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n‖ ≤
          2 * (q : ℝ) * Real.sqrt x * Real.log x +
            (2 : ℝ) ^ (E + 2) * C₁ * x * (Real.log x) ^ (2 - E) := by
  obtain ⟨C₁, hC₁, hLarge⟩ :=
    characterPrimeLargeFactorBound hMUF hE hB
  refine ⟨C₁, hC₁, ?_⟩
  intro x hx hlog q inst χ hχ hq
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsqrtle : Real.sqrt x ≤ x :=
    Real.sqrt_le_self_iff.mpr (Or.inr hxone)
  have hcut : x / Real.sqrt x = Real.sqrt x := by
    calc
      x / Real.sqrt x = (Real.sqrt x) ^ 2 / Real.sqrt x := by
        rw [Real.sq_sqrt hxpos.le]
      _ = Real.sqrt x := by field_simp [ne_of_gt hsqrtpos]
  let S : ℂ :=
    ∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
      characterMobiusCoefficient χ d *
        (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
          dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ))
  let T : ℂ :=
    ∑ m ∈ Finset.Icc 1 (Nat.floor (x / Real.sqrt x)),
      dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ) *
        (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
          (Nat.floor (x / (m : ℝ))), characterMobiusCoefficient χ d)
  have hsplit := characterPrimeHyperbolaSplit χ hsqrtpos hsqrtle
  rw [hcut] at hsplit
  have hsplit' :
      (∑ n ∈ Finset.Icc 1 (Nat.floor x),
        (vonMangoldtWeight n : ℂ) * dirichletCharacterNatHom χ n) = S + T := by
    simpa [S, T] using hsplit
  have hsmall : ‖S‖ ≤ 2 * (q : ℝ) * Real.sqrt x * Real.log x := by
    simpa [S] using nonprincipalCharacterSmallFactorBound χ hχ hx
  have hlarge :
      ‖T‖ ≤ (2 : ℝ) ^ (E + 2) * C₁ * x * (Real.log x) ^ (2 - E) := by
    simpa [T] using hLarge hx hlog (χ := χ) hq
  calc
    _ = ‖S + T‖ := by rw [hsplit']
    _ ≤ ‖S‖ + ‖T‖ := norm_add_le _ _
    _ ≤ 2 * (q : ℝ) * Real.sqrt x * Real.log x +
          (2 : ℝ) ^ (E + 2) * C₁ * x * (Real.log x) ^ (2 - E) :=
      add_le_add hsmall hlarge

end FractionalPrimes.Literature.MobiusToLong
