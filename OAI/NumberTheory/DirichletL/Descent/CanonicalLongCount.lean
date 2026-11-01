/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Descent/CanonicalLongCount.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongBins
@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open CanonicalRowCompletion SecondPassArithmetic

theorem actual_cube_bin_count (b L eps:ℝ)(hb:0≤b)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀X Z:ℝ,0≤X→1≤Z→X≤Z^L→
      ((cubeLogRange b X).card:ℝ)^2≤C*Z^eps := by
  have hLp:0<L+1:=by linarith
  have hd:0<3*eps/(L+1):=by positivity
  obtain ⟨C,hC,hh⟩:=cubeLogRange_sq_small_power b (3*eps/(L+1)) hb hd
  refine ⟨C,hC,?_⟩
  intro X Z hX hZ hXL
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hscale:(Z^((L+1)/3))^3=Z^(L+1) := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    ring
  have hpow:(Z^((L+1)/3))^(3*eps/(L+1))=Z^eps := by
    rw [←Real.rpow_mul hz.le]
    congr 1
    field_simp
  have hbnd:=hh X (Z^((L+1)/3)) hX (Real.one_le_rpow hZ (by positivity))
    (by rw [hscale];exact hXL.trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)))
  simpa only [hpow] using hbnd

end SevenEighths.InverseMoment

end

end OAI
