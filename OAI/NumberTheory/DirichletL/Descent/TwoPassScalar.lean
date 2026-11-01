/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Descent/TwoPassScalar.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Descent.FirstTwoPassEnergy
@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment

theorem two_pass_scalar (C Cz Ct Γ A Z F M r ell eta tau _pi epsFirst loss Lcap saving lossFinal H:ℝ)
    (hC:0≤C)(hCz:0≤Cz)(hCt:0≤Ct)(hA:0≤A)(hZ:1≤Z)(hH:1≤H)
    (hM:M-ell≤F)
    (hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal)
    (hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal)
    (htail: -saving≤F+lossFinal):
    Cz*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))+
      C*Γ^2*(1+A)*Z^(F+loss)*H*Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)+Ct*Γ^2*Z^(-saving)≤
    (C+Cz+Ct)*Γ^2*(1+A)*H*Z^(F+lossFinal) :=by
  have hz:0<Z:=lt_of_lt_of_le zero_lt_one hZ
  have hP:=Real.rpow_le_rpow_of_exponent_le hZ (show M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta)≤F+lossFinal by linarith)
  have hT:=Real.rpow_le_rpow_of_exponent_le hZ htail
  have hR:=Real.rpow_le_rpow_of_exponent_le hZ (show F+loss+((2*Lcap+15*eta+tau)*epsFirst+epsFirst)≤F+lossFinal by linarith)
  have hlarge:1≤(1+A)*H:=one_le_mul_of_one_le_of_one_le (by linarith) hH
  have hp:Cz*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))≤Cz*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    apply (mul_le_mul_of_nonneg_left hP (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using mul_le_mul_of_nonneg_left hlarge (show 0≤Cz*Γ^2 by positivity)
  have ht:Ct*Γ^2*Z^(-saving)≤Ct*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    apply (mul_le_mul_of_nonneg_left hT (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using mul_le_mul_of_nonneg_left hlarge (show 0≤Ct*Γ^2 by positivity)
  have hr:C*Γ^2*(1+A)*Z^(F+loss)*H*Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)≤
      C*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    calc
      _=C*Γ^2*((1+A)*H)*Z^(F+loss+((2*Lcap+15*eta+tau)*epsFirst+epsFirst)):=by simp only [Real.rpow_add hz];ring
      _≤_:=mul_le_mul_of_nonneg_left hR (by positivity)
  nlinarith [add_le_add (add_le_add hp hr) ht]

end SevenEighths.InverseMoment

end

end OAI
