/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Descent/SecondCanonicalChild.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Descent.ActualSecondEnergy
public import OAI.NumberTheory.DirichletL.Descent.SecondFixedFamily
@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem primaryGenerator_primeProduct
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) (S : Finset ι) (v : ι → ℕ) :
    primaryGenerator (Ideal.span {primeProduct p S v}) = primeProduct p S v := by
  apply primaryGenerator_span _ (primeProduct_ne_zero p hp S v)
  unfold primeProduct
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have hpow : ConcretePrimeRowBridge.goodLambda^2 ∣ p i^v i-1 := by
      simpa only [one_pow] using (hpr i).trans (sub_dvd_pow_sub_pow (p i) 1 (v i))
    have he : p i^v i*(∏ j ∈ S,p j^v j)-1 =
        (p i^v i-1)*(∏ j ∈ S,p j^v j)+((∏ j ∈ S,p j^v j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hpow _) ih

def actualSecondPuncture (m : Eis) (γ : OuterTriple) : Eis :=
  (m*primaryGenerator γ.q0)*primaryGenerator γ.residual

def actualSecondRawLabel {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  ((∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor * ∏ i ∈ x.second.overlap,p i

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_mask_span (F : Finset ι) (Ψ : Eis →* ℂ)
    (m₁ m₂ f k : Eis) (he : Ideal.span {m₁}=Ideal.span {m₂})
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m₁ f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m₂ f k slots lists a W X :=
  fixedChildRow_congr_mask_span p hp hcop hg F Ψ he _ f k

theorem actual_second_puncture_span
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) :
    Ideal.span (Set.singleton (((m*b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
      secondExpansionQuotient p x.second))) =
    Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} := by
  let b0 := b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  change Ideal.span {(m*b0)*secondExpansionQuotient p x.second} =
    Ideal.span {(m*primaryGenerator (Ideal.span {b0}))*
      primaryGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor))}
  have hb0 : primaryGenerator (Ideal.span {b0}) = b0 := by
    change primaryGenerator (Ideal.span (Set.singleton b0)) = b0
    exact primaryGenerator_primeProduct p hp hpr _ _
  rw [hb0,
    sourceIdeal_gen p hp hpr,secondExpansionQuotient_of_subset p x.second hE]
  simp only [←Ideal.span_singleton_mul_span_singleton,secondMaskQuotient_span,
    FiniteGaussPhase.span_finset_prod]

theorem actual_second_generator_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    ∃ u v : Eisˣ,
      actualSecondRawLabel p x = (u:Eis)*primaryGenerator (actualSecondChild p u v x).2.1 ∧
      primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
        primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor =
        (v:Eis)*(primaryGenerator (sourceIdeal p x.firstDivisor)*primaryGenerator (sourceIdeal p x.second.divisor)) := by
  let L := (markedSecondOriginal p x).J * sourceIdeal p x.firstCommon *
    sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap
  have hs (S : Finset ι) : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) S} = sourceIdeal p S := by
    simp only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,sourceIdeal]
    exact (FiniteGaussPhase.span_finset_prod S p).symm
  have hl : Ideal.span {actualSecondRawLabel p x} = L := by
    unfold actualSecondRawLabel L
    simp only [←Ideal.span_singleton_mul_span_singleton,hs,sourceIdeal,markedSecondOriginal,cubeSecondSource]
    ring
  have hgp (S : Finset ι) : primaryGenerator (sourceIdeal p S) ≠ 0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hL : primaryGenerator L ≠ 0 := by
    dsimp only [L]
    rw [primaryGenerator_mul,primaryGenerator_mul,primaryGenerator_mul]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (hgp _)) (hgp _)) (hgp _)
    let j := jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
    change primaryGenerator (Ideal.span {j}) ≠ 0
    have hj : primaryGenerator (Ideal.span {j}) = j := by
      change primaryGenerator (Ideal.span (Set.singleton j)) = j
      exact primaryGenerator_primeProduct p hp hpr _ _
    rw [hj]
    exact primeProduct_ne_zero p hp _ _
  obtain ⟨u,v,hu,hv⟩ := exists_second_generator_sectors (actualSecondRawLabel p x)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor)
    L (sourceIdeal p x.firstDivisor) (sourceIdeal p x.second.divisor)
    hl (hs _) (hs _) hL (hgp _) (hgp _)
  exact ⟨u,v,hu,hv⟩

theorem actual_second_canonical_child
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
    finiteCanonicalMarkedRow p hp hcop hg F Ψ
      ((m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)*secondExpansionQuotient p x.second)
      (actualSecondRawLabel p x)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
        primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor * k)
      slots lists a W X =
    secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
      slots lists a (fun _ => W) X
      (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hu,hv⟩ := actual_second_generator_sectors p hp hpr x
  refine ⟨u,v,?_⟩
  intro F Ψ m k slots lists a W X
  rw [secondCanonical_generator_transport p hp hcop hg F Ψ _ _ _ _ _ _ _ _ u v hu hv]
  exact finiteCanonicalMarkedRow_mask_span p hp hcop hg F Ψ _ _ _ _
    (actual_second_puncture_span p hp hpr x hE u v m) slots lists a W X

end
end SevenEighths.InverseMoment

end OAI
