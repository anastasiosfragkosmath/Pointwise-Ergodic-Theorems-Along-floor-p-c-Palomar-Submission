module
public import FractionalPrimes.Literature.Reciprocal.GlobalCharacterMobius
@[expose] public section

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

/-- The exact scalar high-height Möbius factor proposition `ltw:mobius-factor-task`.

The reciprocal branch already defines this contract as `MobiusUniformity`.
Its real endpoints encode every half-open interval `(u,v] ⊆ (L,2L]` by
`L ≤ u ≤ v ≤ 2L`; `twistedMobiusRectangleCoefficient` supplies
`μ(r n) χ(n) n^(-it)`, and `inverseSqrtWeight` supplies `n^(-1/2)`.
This declaration names the proposition and does not assert that the analytic
estimate has been proved unconditionally. -/
abbrev mobiusHighHeightFactorGoal : Prop :=
  FractionalPrimes.Literature.Reciprocal.MobiusUniformity

/-- For positive `n`, the coefficient and inverse-square-root weight in the
real-endpoint contract combine to the source's single complex power
`n^(-1/2-it)`. -/
theorem mobiusHighHeightFactorCoefficient_eq
    {q : ℕ} [NeZero q] (r : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ)
    {n : ℕ} (hn : 0 < n) :
    FractionalPrimes.Literature.Reciprocal.twistedMobiusRectangleCoefficient
        r χ t n *
      FractionalPrimes.Literature.Reciprocal.inverseSqrtWeight (n : ℝ) =
    (ArithmeticFunction.moebius (r * n) : ℂ) * χ (n : ZMod q) *
      (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hhalf : (n : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    have hleft : (n : ℂ) ^ (-(1 / 2 : ℂ)) =
        Complex.exp ((-(1 / 2 : ℂ)) * (Real.log (n : ℝ) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero hnC, Complex.ofReal_log hnR.le]
      congr 1
      push_cast
      ring
    have hright : ((Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        Complex.exp ((-(1 / 2 : ℂ)) * (Real.log (n : ℝ) : ℂ)) := by
      have hrpow := Real.rpow_def_of_pos hnR (-(1 / 2 : ℝ))
      calc
        _ = ((Real.exp (Real.log (n : ℝ) * (-(1 / 2 : ℝ))) : ℝ) : ℂ) :=
          congrArg Complex.ofReal hrpow
        _ = Complex.exp ((-(1 / 2 : ℂ)) * (Real.log (n : ℝ) : ℂ)) := by
          rw [Complex.ofReal_exp]
          congr 1
          push_cast
          ring
    exact hleft.trans hright.symm
  have htwist : (n : ℂ) ^ (-((t : ℂ) * Complex.I)) =
      Complex.exp ((-Complex.I * (t : ℂ)) * (Real.log (n : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hnC, Complex.ofReal_log hnR.le]
    congr 1
    push_cast
    ring
  have hsplit :
      (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
        FractionalPrimes.Literature.Reciprocal.inverseSqrtWeight (n : ℝ) *
          (n : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
    rw [show (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
        (-(1 / 2 : ℂ)) + (-((t : ℂ) * Complex.I)) by ring,
      Complex.cpow_add _ _ hnC, hhalf,
      FractionalPrimes.Literature.Reciprocal.inverseSqrtWeight, htwist]
    norm_num
  rw [FractionalPrimes.Literature.Reciprocal.twistedMobiusRectangleCoefficient,
    FractionalPrimes.Literature.LongArithmetic.shiftedCharacterMobiusCoefficient,
    FractionalPrimes.Literature.LongArithmetic.mobiusMultiplierCoefficient,
    FractionalPrimes.Literature.LongArithmetic.dirichletCharacterNatHom_apply_of_ne_zero
      χ hn0]
  calc
    ((ArithmeticFunction.moebius (r * n) : ℂ) * χ (n : ZMod q) *
        (n : ℂ) ^ (-((t : ℂ) * Complex.I))) *
        FractionalPrimes.Literature.Reciprocal.inverseSqrtWeight (n : ℝ) =
      (ArithmeticFunction.moebius (r * n) : ℂ) * χ (n : ZMod q) *
        (FractionalPrimes.Literature.Reciprocal.inverseSqrtWeight (n : ℝ) *
          (n : ℂ) ^ (-((t : ℂ) * Complex.I))) := by ring
    _ = (ArithmeticFunction.moebius (r * n) : ℂ) * χ (n : ZMod q) *
        (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) := by rw [← hsplit]

/-- The named blueprint contract is definitionally the existing real-endpoint
form of MUF used by the reciprocal estimates. -/
theorem mobiusHighHeightFactorGoal_iff_MobiusUniformity :
    mobiusHighHeightFactorGoal ↔
      FractionalPrimes.Literature.Reciprocal.MobiusUniformity := Iff.rfl

#print axioms mobiusHighHeightFactorGoal_iff_MobiusUniformity
#print axioms mobiusHighHeightFactorCoefficient_eq

end FractionalPrimes.Literature.Twisted

