/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceNormalization.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePool
@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced
local notation "O"=>ActualEisensteinCubic.O

theorem scalar_norm (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀:ℝ)(hK:0<K)(_hA₀:0<A₀)(_hB₀:0<B₀):
    ‖scalar C D hC E K A₀ B₀‖=
      ‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖*Real.sqrt A₀*Real.sqrt B₀):=by
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero
      (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hk:0<K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos he)
  unfold scalar
  rw [norm_mul,norm_div,norm_mul,
    norm_canonicalNormalizedGauss (activePrime C D) (activeCoprime C D) (activeGood C D hC)
      (fun P=>common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=>netExponent_lt_six _ _)]
  simp only [mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hk,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
