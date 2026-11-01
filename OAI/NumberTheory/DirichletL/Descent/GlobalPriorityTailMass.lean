/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Descent/GlobalPriorityTailMass.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassWeighted
@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseMomentGlobalPrincipalMass
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem original_tail_mass (Jmax : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(Z L : ℝ),
    1≤Z → 0≤L → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^L) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^L) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^L) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^L) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^L) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,primeProductNorm p (principalSupport extra negative x))≤C*Z^(13*L) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z L hZ hL hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^L) (Z^L) (Z^L) (Z^L) 1
    (Real.one_le_rpow hZ hL) (by positivity) (by positivity) (by positivity)
    (by norm_num) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  simp only [Real.rpow_one] at hh
  apply hh.trans_eq
  have he : Z^(13*L)=(Z^L)^13 := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    norm_num
    ring
  rw [he]
  norm_num
  ring

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI
