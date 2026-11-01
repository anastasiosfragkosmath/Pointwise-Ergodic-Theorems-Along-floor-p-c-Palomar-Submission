/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Detector/InitialSubseries.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Detector.InitialFubini
@[expose] public section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

abbrev RawHighIndex := NonzeroFrequency×((Ideal O×Ideal O)×Ideal O)

def rawHighEmbedding (p : RawHighIndex) : FullHighIndex := (p.1,(p.2.1,(p.2.2,1)))

lemma rawHighEmbedding_injective : Function.Injective rawHighEmbedding := by
  rintro ⟨h,⟨ij,k⟩⟩ ⟨h',⟨ij',k'⟩⟩ he
  simpa only [rawHighEmbedding,Prod.mk.injEq,and_true] using he

theorem initialHigh_integral_tsum_subseries {ι : Type*} [Countable ι]
    (e : ι→FullHighIndex) (he : Function.Injective e)
    (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) :
    (∫p,∑'i : ι, initialHighOnLines S D η mask σ υ ξ (e i) p*T p ∂heightMeasure)=
      ∑'i : ι, ∫p,initialHighOnLines S D η mask σ υ ξ (e i) p*T p ∂heightMeasure := by
  let F := fun i p=>initialHighOnLines S D η mask σ υ ξ (e i) p*T p
  have hb (i : ι) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ (e i)*‖T p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ (e i) p) (norm_nonneg _)
  have hF (i : ι) : Integrable (F i) heightMeasure := by
    apply (hT.norm.const_mul (initialHighMajorant σ υ ξ (e i))).mono'
    · exact (initialHighOnLines_continuous S D η mask σ υ ξ (e i)).aestronglyMeasurable.mul hT.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : ι=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=>integral_nonneg (fun _=>norm_nonneg _))
      (fun i=>?_) (((initialHighMajorant_summable σ υ ξ hσ hυ hξ).comp_injective he).mul_right
        (∫p,‖T p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hT.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

end SevenEighths.ProbePhysical
end

end OAI
