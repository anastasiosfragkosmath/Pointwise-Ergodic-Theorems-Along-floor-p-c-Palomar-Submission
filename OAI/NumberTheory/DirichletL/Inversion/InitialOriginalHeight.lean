/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Inversion/InitialOriginalHeight.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Inversion.InitialTotalFourier
@[expose] public section

namespace OAI

noncomputable section

open scoped Classical SchwartzMap ContDiff FourierTransform
namespace SevenEighths.InverseInitialOriginalHeight
open InverseMoment InverseInitialProfile InverseInitialProfileBounds FourierBridge
open JointLogSeparation CompletedHeight

theorem child_eq_normTwisted (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=normTwistedSource W θ:=by
  rw [childLogTest_eq_clipped]
  funext x
  simp only [clippedSource,normTwistedSource,one_mul]

theorem child_support (W:ℝ→ℂ)(θ:ℝ):
    Function.support (childLogTest W θ)⊆Function.support W:=by
  rw [child_eq_normTwisted]
  exact normTwistedSource_support W θ

theorem child_smooth (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    ContDiff ℝ ∞ (childLogTest W θ):=by
  rw [child_eq_normTwisted]
  exact CanonicalRowCompletion.normTwistedSource_contDiff W a b ha hs hW θ

theorem logSchwartz_child (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    CubicReflectionKernel.logSchwartz (childLogTest W θ) a b ha
      ((child_support W θ).trans hs) (child_smooth W a b ha hs hW θ)=
    frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) θ:=by
  ext x
  simp only [CubicReflectionKernel.logSchwartz_apply,childLogTest,
    frequencyTwist_apply,Real.log_exp]
  ring

end SevenEighths.InverseInitialOriginalHeight

end

end OAI
