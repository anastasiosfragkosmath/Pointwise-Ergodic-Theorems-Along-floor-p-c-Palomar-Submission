module
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeHyperbolaSplit
public import FractionalPrimes.Literature.MobiusToLong.MobiusLargeHalf
@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.MobiusToLong

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.Twisted
open Finset

/-- The strict large-factor part of the character-twisted von Mangoldt
hyperbola split is controlled by the global Möbius-character estimate. The
real cutoffs and strict lower endpoint `floor √x` are retained exactly. -/
theorem characterPrimeLargeFactorBound
    (hMUF : MobiusUniformity) {E B : ℝ} (hE : 0 < E) (hB : 0 < B) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ {x : ℝ} (_hx : 9 ≤ x)
        (_hlog : (2 : ℝ) ^ (B + 1) ≤ Real.log x)
        {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
        (_hq : (q : ℝ) ≤ (Real.log x) ^ B),
        ‖∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
            dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ) *
              (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
                  (Nat.floor (x / (m : ℝ))),
                characterMobiusCoefficient χ d)‖ ≤
          (2 : ℝ) ^ (E + 2) * C₁ * x * (Real.log x) ^ (2 - E) := by
  obtain ⟨C₁, hC₁, hLarge⟩ := largeMobiusHyperbolaHalf hMUF hE hB
  refine ⟨C₁, hC₁, ?_⟩
  intro x hx hlog q inst χ hq
  have hinner (m : ℕ)
      (hm : m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x))) :
      (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
          (Nat.floor (x / (m : ℝ))), characterMobiusCoefficient χ d) =
        ∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
          (Nat.floor (x / (m : ℝ))), globalMobiusCharacterCoefficient χ d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < d := by
      have hd' := Finset.mem_Ioc.mp hd
      omega
    rw [characterMobiusCoefficient_eq,
      globalMobiusCharacterCoefficient_eq χ (Nat.ne_of_gt hdpos)]
  have hrewrite :
      (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
          dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ) *
            (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
                (Nat.floor (x / (m : ℝ))), characterMobiusCoefficient χ d)) =
        ∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
          dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ) *
            (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
                (Nat.floor (x / (m : ℝ))), globalMobiusCharacterCoefficient χ d) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hinner m hm]
  have hbound := hLarge hx hlog (χ := χ) hq
  calc
    _ = ‖∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
          dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ) *
            (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
                (Nat.floor (x / (m : ℝ))), globalMobiusCharacterCoefficient χ d)‖ := by
      rw [hrewrite]
    _ ≤ (2 : ℝ) ^ (E + 2) * C₁ * x * (Real.log x) ^ (2 - E) := hbound

end FractionalPrimes.Literature.MobiusToLong

end
