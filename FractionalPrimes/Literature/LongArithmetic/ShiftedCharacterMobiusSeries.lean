module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import FractionalPrimes.Literature.LongArithmetic.MobiusFilteredSeries

@[expose] public section

noncomputable section

open scoped ArithmeticFunction.Moebius LSeries.notation

namespace FractionalPrimes.Literature.LongArithmetic

/-- Evaluate a Dirichlet character on natural numbers, using the zero-valued
extension at `0`.  The separate `n = 0` case preserves the Dirichlet-series
convention even at modulus one, where `ZMod 1` is a singleton. -/
def dirichletCharacterNatHom {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else χ (n : ZMod q)
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    simp [hm, hn, hmn, Nat.cast_mul, map_mul]

@[simp]
theorem dirichletCharacterNatHom_apply_of_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : n ≠ 0) :
    dirichletCharacterNatHom χ n = χ (n : ZMod q) := by
  simp [dirichletCharacterNatHom, hn]

theorem dirichletCharacterNatHom_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : n ≠ 0) :
    ‖dirichletCharacterNatHom χ n‖ ≤ 1 := by
  rw [dirichletCharacterNatHom_apply_of_ne_zero χ hn]
  exact χ.norm_le_one _

/-- The coefficient of the series in `lrc:twisted-rectangle`, including its
frequency twist.  The `LSeries` definition omits the term at zero. -/
def shiftedCharacterMobiusCoefficient {q : ℕ} [NeZero q]
    (r : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  mobiusMultiplierCoefficient r (dirichletCharacterNatHom χ) n *
    (n : ℂ) ^ (-((t : ℂ) * Complex.I))

/-- The frequency twist in the paper is exactly the translation
`s ↦ s + it` in the L-series variable. -/
theorem shiftedCharacterMobiusLSeries_eq {q : ℕ} [NeZero q]
    (r : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (s : ℂ) :
    LSeries (shiftedCharacterMobiusCoefficient r χ t) s =
      LSeries (mobiusMultiplierCoefficient r (dirichletCharacterNatHom χ))
        (s + (t : ℂ) * Complex.I) := by
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [shiftedCharacterMobiusCoefficient, div_eq_mul_inv,
      mobiusMultiplierCoefficient]
    rw [← Complex.cpow_neg, ← Complex.cpow_neg]
    let z : ℂ := (n : ℂ)
    have hz : z ≠ 0 := by
      dsimp [z]
      exact Nat.cast_ne_zero.mpr hn
    have hpow : z ^ (-((t : ℂ) * Complex.I)) * z ^ (-s) =
        z ^ (-(s + (t : ℂ) * Complex.I)) := by
      calc
        z ^ (-((t : ℂ) * Complex.I)) * z ^ (-s) =
            z ^ (-((t : ℂ) * Complex.I) + -s) := by
              rw [Complex.cpow_add _ _ hz]
        _ = z ^ (-(s + (t : ℂ) * Complex.I)) := by congr 1; ring
    calc
      _ = (ArithmeticFunction.moebius (r * n) : ℂ) *
          (dirichletCharacterNatHom χ n) *
          (z ^ (-((t : ℂ) * Complex.I)) * z ^ (-s)) := by ring
      _ = _ := by rw [hpow]

/-- Exact shifted-character specialization of the checked Möbius Euler-factor
identity.  This is the Dirichlet-series factorization required to identify the
explicit analytic extension in `lrc:twisted-rectangle`; the pole-aware
reciprocal continuation is handled separately. -/
theorem shiftedCharacterMobiusDirichletSeries_eq {q : ℕ} [NeZero q]
    (r : ℕ) (hr : r ≠ 0) (χ : DirichletCharacter ℂ q) (t : ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (shiftedCharacterMobiusCoefficient r χ t) s =
      (ArithmeticFunction.moebius r : ℂ) *
        mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ)
          (s + (t : ℂ) * Complex.I) *
        ∏ p ∈ mobiusPrimeDivisors r,
          (mobiusEulerFactor (dirichletCharacterNatHom χ)
            (s + (t : ℂ) * Complex.I) p)⁻¹ := by
  rw [shiftedCharacterMobiusLSeries_eq]
  have hs' : 1 < (s + (t : ℂ) * Complex.I).re := by
    simpa using hs
  exact mobiusMultiplierDirichletSeries_eq r hr
    (dirichletCharacterNatHom χ)
    (fun n hn => dirichletCharacterNatHom_norm_le_one χ hn) hs'

#print axioms dirichletCharacterNatHom
#print axioms shiftedCharacterMobiusLSeries_eq
#print axioms shiftedCharacterMobiusDirichletSeries_eq

end FractionalPrimes.Literature.LongArithmetic

end
