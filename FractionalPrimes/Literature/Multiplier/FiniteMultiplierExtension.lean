module

public import FractionalPrimes.Literature.Multiplier.FiniteMultiplierNorm
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The bounded multiplier extension from finite inputs

The canonical multiplier map on finitely supported sequences has a unique
continuous linear extension to sequence `ℓᵖ`. The dense map is the exact
Finsupp inclusion, and the extension agrees with the original multiplier on
every finite input.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open scoped ENNReal

noncomputable section

/-- The bounded extension of the canonical finite-input multiplier map to
sequence `ℓᵖ`. -/
def finiteMultiplierLpExtension
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
  (finiteMultiplierLpMap (p := p) h hp1).extendOfNorm
    (finiteSupportLpInclusion (P := ENNReal.ofReal p))

/-- The finite-input norm estimate supplies the bound required by
`LinearMap.extendOfNorm`. -/
private theorem finiteMultiplierLpMap_uniform_bound
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    ∀ f : ℤ →₀ ℂ,
      ‖finiteMultiplierLpMap (p := p) h hp1 f‖ ≤
        (finiteMultiplierLpNormConstant p * D) *
          ‖finiteSupportLpInclusion (P := ENNReal.ofReal p) f‖ := by
  intro f
  exact finiteMultiplierLpMap_norm_le h hp1 f

/-- On every finitely supported input, the extension recovers the canonical
finite-input multiplier map. -/
theorem finiteMultiplierLpExtension_apply_finite
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (f : ℤ →₀ ℂ) :
    finiteMultiplierLpExtension h hp1
        (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) =
      finiteMultiplierLpMap (p := p) h hp1 f := by
  let e := finiteSupportLpInclusion (P := ENNReal.ofReal p)
  have hdense : DenseRange e :=
    finiteSupportLpInclusion_denseRange (P := ENNReal.ofReal p)
      ENNReal.ofReal_ne_top
  have hbound := finiteMultiplierLpMap_uniform_bound h hp1
  unfold finiteMultiplierLpExtension
  exact LinearMap.extendOfNorm_eq
    (f := finiteMultiplierLpMap (p := p) h hp1) (e := e)
    hdense ⟨finiteMultiplierLpNormConstant p * D, hbound⟩ f

/-- The continuous extension satisfies the same operator norm bound on every
sequence `ℓᵖ` input. -/
theorem finiteMultiplierLpExtension_norm_le
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    ‖finiteMultiplierLpExtension h hp1 F‖ ≤
      finiteMultiplierLpNormConstant p * D * ‖F‖ := by
  let e := finiteSupportLpInclusion (P := ENNReal.ofReal p)
  have hdense : DenseRange e :=
    finiteSupportLpInclusion_denseRange (P := ENNReal.ofReal p)
      ENNReal.ofReal_ne_top
  have hbound := finiteMultiplierLpMap_uniform_bound h hp1
  unfold finiteMultiplierLpExtension
  exact LinearMap.norm_extendOfNorm_apply_le
    (f := finiteMultiplierLpMap (p := p) h hp1) (e := e)
    hdense (finiteMultiplierLpNormConstant p * D) hbound F

/-- The extension operator has norm at most the source-order multiplier
constant times `D`. -/
theorem finiteMultiplierLpExtension_opNorm_le
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    ‖finiteMultiplierLpExtension h hp1‖ ≤
      finiteMultiplierLpNormConstant p * D := by
  let e := finiteSupportLpInclusion (P := ENNReal.ofReal p)
  have hdense : DenseRange e :=
    finiteSupportLpInclusion_denseRange (P := ENNReal.ofReal p)
      ENNReal.ofReal_ne_top
  have hbound := finiteMultiplierLpMap_uniform_bound h hp1
  have hC : 0 ≤ finiteMultiplierLpNormConstant p * D :=
    mul_nonneg (finiteMultiplierLpNormConstant_nonneg hp1) h.D_nonneg
  unfold finiteMultiplierLpExtension
  exact LinearMap.opNorm_extendOfNorm_le
    (f := finiteMultiplierLpMap (p := p) h hp1) (e := e)
    hdense hC hbound

/-- The extension is the unique continuous linear map on sequence `ℓᵖ`
whose restriction along finite-support inclusion is the canonical
finite-input multiplier map. -/
theorem finiteMultiplierLpExtension_unique
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (G : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))
    (hG : G.toLinearMap.comp
      (finiteSupportLpInclusion (P := ENNReal.ofReal p)) =
        finiteMultiplierLpMap (p := p) h hp1) :
    finiteMultiplierLpExtension h hp1 = G := by
  let e := finiteSupportLpInclusion (P := ENNReal.ofReal p)
  have hdense : DenseRange e :=
    finiteSupportLpInclusion_denseRange (P := ENNReal.ofReal p)
      ENNReal.ofReal_ne_top
  have hbound := finiteMultiplierLpMap_uniform_bound h hp1
  unfold finiteMultiplierLpExtension
  exact LinearMap.extendOfNorm_unique
    (f := finiteMultiplierLpMap (p := p) h hp1) (e := e)
    hdense (finiteMultiplierLpNormConstant p * D) hbound G hG

end

end FractionalPrimes.Literature.Multiplier
