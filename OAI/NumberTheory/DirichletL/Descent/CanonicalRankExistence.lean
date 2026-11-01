/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Descent/CanonicalRankExistence.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceInduction
public import OAI.NumberTheory.DirichletL.Inversion.CanonicalReferenceThreshold
@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment

theorem actual_rank_reference_cutoffs : RankReferenceCutoffs :=by
  intro lo hi hlo hhi
  obtain ⟨Vlog,Alog,hA,hAe,hcompact,hsupport,hbox,hone,hzero⟩:=
    exists_canonical_reference_cutoff lo hi
  exact ⟨Vlog,Alog,hbox,hone⟩

theorem actual_rank_reference_thresholds : RankReferenceThresholds :=by
  intro eta heta hi Alog window
  exact eventually_canonical_reference_gates hi Alog window eta heta

theorem canonical_rank_energy_exists
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤cstar/100000)(hetad:eta≤cutoff/32)
    (n:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    RankEnergyExists n L cstar cutoff eta K W :=
  rank_energy_exists_all_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    L cstar cutoff eta K hL hcstar hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW

theorem canonical_marked_energy_exists
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=
  canonical_energy_exists_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    Mcap Fcap c eps hM hF hc heps K W lo hi hlo hhi hsW

end SevenEighths.InverseMoment

end

end OAI
