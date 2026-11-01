/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Descent/PhysicalBlockBudget.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingMass
public import OAI.NumberTheory.DirichletL.Descent.PhysicalExponents
@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem second_source_scalar_norm (Y E V X : ℝ)
    (hY : 0<Y) (hE : 0<E) (hV : 0<V) (hX : 0<X) (a : ℂ) :
    ‖(Y:ℂ)*a*((E*V*X:ℝ):ℂ)⁻¹‖ = ‖a‖*(Y/(E*V*X)) := by
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,abs_of_pos (by positivity : 0<E*V*X)]
  ring

theorem physical_block_rpow_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ) /
        (Z^θ*Z^v*Z^(secondFormalColumn r A B t g v)) * Real.exp (6*(η*Real.log Z))) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hZpos : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_physical_scalar Z hZpos]
  have hexp : Real.exp ((9/2:ℝ)*(η*Real.log Z))=Z^((9/2:ℝ)*η) := by
    rw [Real.rpow_def_of_pos hZpos]
    congr 1
    ring
  rw [hexp,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hb := physical_step_energy_exponent M r ell V δ A B R j t g θ v η τ π ε
    (max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v) hclip
  nlinarith

theorem physical_block_scalar_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (ray : ℂ) (C : ℝ) (hC : 0≤C)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    C * Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Real.exp (6*(η*Real.log Z)) *
        ‖((Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ):ℝ):ℂ)*ray*
          ((Z^θ*Z^v*Z^(secondFormalColumn r A B t g v):ℝ):ℂ)⁻¹‖) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    C*‖ray‖*Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_source_scalar_norm _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left
    (physical_block_rpow_budget Z hZ M r ell V δ A B R j t g θ v η τ π ε εmass hclip hεmass)
    (mul_nonneg hC (norm_nonneg ray))
  convert hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
