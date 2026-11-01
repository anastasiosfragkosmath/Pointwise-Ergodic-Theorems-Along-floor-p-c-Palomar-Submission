module

public import FractionalPrimes.Literature.JSW.RoughSquareBootstrap

/-! Strong endpoint interpolation on precisely the source bounded-input
domain. Global linearity outside this domain is unnecessary. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem boundedVector_strongEndpoint_interpolation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s₀ p s₁ A₀ A₁ : ℝ}
    (T : Variation.LayerCakeInput (volume : Measure ℝ) → ℝ → E)
    (hmeas : ∀ f, Measurable (fun x => ‖T f x‖))
    (hsub : ∀ f g (hfg : Variation.LayerCakeAdmissible volume (f.1 + g.1)) x,
      ‖T ⟨f.1 + g.1, hfg⟩ x‖ ≤ ‖T f x‖ + ‖T g x‖)
    (hhom : ∀ f (c : ℝ) (_hc : 0 ≤ c)
      (hcf : Variation.LayerCakeAdmissible volume (c • f.1)) x,
      ‖T ⟨c • f.1, hcf⟩ x‖ = c * ‖T f x‖)
    (hs₀ : 1 ≤ s₀) (h₀ : s₀ < p) (h₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hStrong₀ : ∀ f,
      eLpNorm (fun x => ‖T f x‖) (ENNReal.ofReal s₀) volume ≤
        ENNReal.ofReal A₀ * eLpNorm f.1 (ENNReal.ofReal s₀) volume)
    (hStrong₁ : ∀ f,
      eLpNorm (fun x => ‖T f x‖) (ENNReal.ofReal s₁) volume ≤
        ENNReal.ofReal A₁ * eLpNorm f.1 (ENNReal.ofReal s₁) volume)
    (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    eLpNorm (fun x => ‖T f x‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (weakTypeInterpolationConstant s₀ p s₁ *
        A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
        A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁) *
          eLpNorm f.1 (ENNReal.ofReal p) volume := by
  let U : WeakTypeInterpolationOperator volume s₀ s₁ A₀ A₁ := {
    apply := fun g x => ‖T g x‖
    measurable_apply := hmeas
    nonneg_apply := fun g x => norm_nonneg _
    subadditive := hsub
    positive_homogeneous := hhom
    weak_s₀ := fun g t ht => roughSquare_strongEndpoint_weak
      (by linarith) hA₀ T hStrong₀ g t ht
    weak_s₁ := fun g t ht => roughSquare_strongEndpoint_weak
      (by linarith) hA₁ T hStrong₁ g t ht }
  exact weakTypeInterpolation U hs₀ h₀ h₁ hA₀ hA₁ f

#print axioms boundedVector_strongEndpoint_interpolation
end
end FractionalPrimes.Literature.JSW
end
