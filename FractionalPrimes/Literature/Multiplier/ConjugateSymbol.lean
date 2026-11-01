module

public import FractionalPrimes.Literature.Multiplier.Data
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Conjugating periodic multiplier data

The dual `p > 2` branch of `lp:main` applies the already established
low-exponent estimate to the conjugate symbol. This file verifies that
complex conjugation preserves every hypothesis and the same constant `D`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-- Over a real scalar variable, complex conjugation commutes with every
iterated derivative. -/
theorem iteratedDeriv_star_real (n : ℕ) (f : ℝ → ℂ) :
    iteratedDeriv n (fun x => star (f x)) =
      fun x => star (iteratedDeriv n f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      exact deriv.star'

/-- The complex-conjugate lift of a periodic multiplier satisfies the same
two-derivative symbol hypotheses with exactly the same bound `D`. -/
theorem SymbolData.conjugate {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    SymbolData (fun x => star (m x)) D where
  measurable := by
    simpa [Function.comp_def] using
      Complex.continuous_conj.measurable.comp h.measurable
  bounded := by
    obtain ⟨C, hC⟩ := h.bounded
    exact ⟨C, fun x => by simpa using hC x⟩
  periodic := by
    intro x
    exact congrArg (star : ℂ → ℂ) (h.periodic x)
  smoothOnPuncturedTorus := by
    simpa [Function.comp_def] using
      Complex.conjCLE.contDiff.comp_contDiffOn h.smoothOnPuncturedTorus
  seamValue := congrArg (star : ℂ → ℂ) h.seamValue
  seamFirstDerivative := by
    simpa only [deriv.star] using
      congrArg (star : ℂ → ℂ) h.seamFirstDerivative
  seamSecondDerivative := by
    have hleft := congrFun (iteratedDeriv_star_real 2 m) (-(1 / 2 : ℝ))
    have hright := congrFun (iteratedDeriv_star_real 2 m) (1 / 2 : ℝ)
    rw [hleft, hright]
    exact congrArg (star : ℂ → ℂ) h.seamSecondDerivative
  weightedDerivativeBound := by
    intro ξ hξ0 hξhalf
    have hbound := h.weightedDerivativeBound ξ hξ0 hξhalf
    have hiter := congrFun (iteratedDeriv_star_real 2 m) ξ
    rw [deriv.star, hiter]
    simpa [norm_mul] using hbound

/-- The quotient lift of the conjugate symbol is pointwise the complex
conjugate of the original torus symbol. -/
theorem torusSymbol_conjugate {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (ξ : Torus) :
    torusSymbol (h.conjugate) ξ = star (torusSymbol h ξ) := by
  induction ξ using QuotientAddGroup.induction_on with
  | H x =>
      rw [torusSymbol_coe (h.conjugate) x, torusSymbol_coe h x]

/-- The `L∞` representatives of the two torus symbols are conjugate almost
everywhere. -/
theorem torusSymbolLp_conjugate_coeFn {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) :
    (torusSymbolLp (h.conjugate) : Torus → ℂ) =ᵐ[torusHaar]
      fun ξ => star ((torusSymbolLp h : Torus → ℂ) ξ) := by
  filter_upwards [torusSymbolLp_coeFn (h.conjugate), torusSymbolLp_coeFn h]
    with ξ hleft hright
  calc
    (torusSymbolLp (h.conjugate) : Torus → ℂ) ξ =
        torusSymbol (h.conjugate) ξ := hleft
    _ = star (torusSymbol h ξ) := torusSymbol_conjugate h ξ
    _ = star ((torusSymbolLp h : Torus → ℂ) ξ) := by rw [← hright]

/-- Multiplication by the conjugate symbol is adjoint to multiplication by
the original symbol on circle `L²`. -/
private theorem inner_torusSymbolLp_smul {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (F G : Lp ℂ 2 torusHaar) :
    inner ℂ G (torusSymbolLp h • F) =
      inner ℂ (torusSymbolLp (h.conjugate) • G) F := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [torusSymbolLp_conjugate_coeFn h,
      Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (torusSymbolLp h) F,
      Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
        (torusSymbolLp (h.conjugate)) G] with ξ hconj hmul hcmul
  have hmul' : (torusSymbolLp h • F : Lp ℂ 2 torusHaar) ξ =
      (torusSymbolLp h : Torus → ℂ) ξ * (F : Torus → ℂ) ξ := by
    change (torusSymbolLp h • F : Lp ℂ 2 torusHaar) ξ = _
    simpa only [Pi.smul_apply', smul_eq_mul] using hmul
  have hcmul' :
      (torusSymbolLp (h.conjugate) • G : Lp ℂ 2 torusHaar) ξ =
        (torusSymbolLp (h.conjugate) : Torus → ℂ) ξ * (G : Torus → ℂ) ξ := by
    change (torusSymbolLp (h.conjugate) • G : Lp ℂ 2 torusHaar) ξ = _
    simpa only [Pi.smul_apply', smul_eq_mul] using hcmul
  simp only [RCLike.inner_apply, hmul', hcmul', hconj, map_mul]
  simp only [starRingEnd_apply, star_star]
  ring

/-- The `ℓ²` multiplier with conjugate symbol is the Hilbert-space adjoint
of the original multiplier, with Lean's conjugate-linear-first pairing
convention. -/
theorem inner_TmL2_conjugate_adjoint {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (f g : lp (fun _ : ℤ => ℂ) 2) :
    inner ℂ g (TmL2 h f) =
      inner ℂ (TmL2 (h.conjugate) g) f := by
  simp only [TmL2]
  calc
    inner ℂ g
        (sequenceToCircleL2.symm
          (torusSymbolLp h • sequenceToCircleL2 f)) =
      inner ℂ (sequenceToCircleL2 g)
        (torusSymbolLp h • sequenceToCircleL2 f) := by
          simpa only [LinearIsometryEquiv.symm_apply_apply] using
            sequenceToCircleL2.symm.inner_map_map (sequenceToCircleL2 g)
              (torusSymbolLp h • sequenceToCircleL2 f)
    _ = inner ℂ (torusSymbolLp (h.conjugate) • sequenceToCircleL2 g)
        (sequenceToCircleL2 f) :=
          inner_torusSymbolLp_smul h (sequenceToCircleL2 f) (sequenceToCircleL2 g)
    _ = inner ℂ
        (sequenceToCircleL2.symm
          (torusSymbolLp (h.conjugate) • sequenceToCircleL2 g)) f := by
          simpa only [LinearIsometryEquiv.symm_apply_apply] using
            (sequenceToCircleL2.symm.inner_map_map
              (torusSymbolLp (h.conjugate) • sequenceToCircleL2 g)
              (sequenceToCircleL2 f)).symm

end

end FractionalPrimes.Literature.Multiplier
