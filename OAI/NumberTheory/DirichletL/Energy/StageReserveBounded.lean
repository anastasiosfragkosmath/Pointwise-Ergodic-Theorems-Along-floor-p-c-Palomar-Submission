/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Energy/StageReserveBounded.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Energy.StageReserve
@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyStageReserve

theorem exists_bounded_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,Mcap+Bmask+xi,C,hd,hxi,hs,hC,hxr,le_refl _,by linarith,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  apply le_trans _ (hledger e he Z hZ s hwidth α w hw)
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hLp:0≤Mcap+Bmask+xi:=by linarith
  gcongr

end SevenEighths.CenteredMomentEnergyStageReserveBounded

end

end OAI
