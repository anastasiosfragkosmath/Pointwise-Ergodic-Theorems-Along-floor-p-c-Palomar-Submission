/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Detector/RawArithmetic.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Detector.RawIndexGrouping
@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def rawArithmeticSeries (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) : ℂ :=
  ∑'p : RawHighIndex,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
    x w z (rawHighEmbedding p)

lemma rawHighCoefficient_outer_support (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : RawHighIndex)
    (hp : fullHighCoefficient S D η mask x w z (rawHighEmbedding p)≠0) :
    Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2 := by
  have hb : bareIdealHighCoefficient η p.1.val p.2.1.1 p.2.1.2 p.2.2 1≠0 := by
    intro hz
    exact hp (by simp only [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,bareIdealHighSummand,hz,mul_zero,zero_mul])
  have hs : Supported p.2.2 := by
    unfold bareIdealHighCoefficient at hb
    split_ifs at hb with hh
    · exact hh.2.2.2.1
    · exact False.elim (hb rfl)
  refine ⟨hs,?_⟩
  by_contra hn
  exact hp (by simp [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,highIdealMask,hn])

lemma rawArithmeticSeries_eq_sourceRaw (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) :
    rawArithmeticSeries S D η C x w z=
      ∑'i : SourceRawIndex S,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
        x w z (sourceRawEmbedding S i) := by
  unfold rawArithmeticSeries sourceRawEmbedding
  change _ = ∑'i : {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}, _
  symm
  apply tsum_subtype_eq_of_support_subset (f:=fun p : RawHighIndex=>
    fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val)) x w z (rawHighEmbedding p))
    (s:={p : RawHighIndex | Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2})
  intro p hp
  exact rawHighCoefficient_outer_support S D η _ x w z p hp

end SevenEighths.ProbePhysical
end

end OAI
