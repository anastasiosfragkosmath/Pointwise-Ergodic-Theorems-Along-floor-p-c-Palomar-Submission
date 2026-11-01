module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupSmallGroupSourceInterval
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupTrilinearInstantiation
public import Mathlib.Tactic
@[expose] public section

/-! A narrow source adapter from the checked selected-group interval branch to
the actual residue-restricted three-block trilinear theorem.  The alignment
between the source-selected group and the first group in the block partition
is kept explicit, since the current source interval theorem does not export
that relation. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.LargeValues

/-- Apply the scalar uncapped trilinear estimate to actual residue-restricted
smooth Heath--Brown blocks, using the exact source short-interval branch for
the first block.  The scale, exponent and time-window hypotheses are the
corresponding checked outputs of the three-group geometry lemmas.  The
alignment hypothesis says that the group selected by the source interval
branch is the first group of this particular block partition. -/
theorem smoothHeathBrownThreeGroupActualResidue_trilinear_of_sourceBranch
    {X z B κ D W U : ℝ}
    (hX : 3 ≤ X)
    (fsList : List (SmoothHeathBrownFactor X))
    (q : ℕ) (residue : Fin fsList.length → ℕ) (u : ℝ)
    (I₁ I₂ I₃ : Finset (Fin fsList.length))
    (selected : Fin fsList.length)
    (hI₁card : I₁.card ≤ 20) (hI₂card : I₂.card ≤ 20)
    (hI₃card : I₃.card ≤ 20)
    (_hbranchSelected : selected ∈ I₁)
    (_hbranchCard : I₁.card ≤ 20)
    (_hbranchScaleLower : X ^ (1 / 100 : ℝ) ≤
      smoothHeathBrownFactorScale (fsList.get selected))
    (_hbranchScaleUpper : smoothHeathBrownFactorScale (fsList.get selected) ≤
      (2 : ℝ) ^ 11 * Real.sqrt X)
    (hbranch : ∀ (h : ℤ) (L x y : ℝ) {q' : ℕ},
      1 ≤ q' → (q' : ℝ) ≤ (Real.log X) ^ B →
      (residue' : Fin fsList.length → ℕ) → residue' selected < q' →
      (s : ℝ) → (Real.log X) ^ D / 2 ≤ |s| → |s| ≤ X →
      L = (2 : ℝ) ^ h *
        (∏ i ∈ I₁, smoothHeathBrownFactorScale (fsList.get i)) →
      -(I₁.card : ℤ) ≤ h ∧ h < (I₁.card : ℤ) →
      L ≤ x → x ≤ y → y ≤ 2 * L →
      ‖∑ n ∈ factorExtractionRealInterval x y,
        (∏ i : I₁,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q' (residue' i.val) (fsList.get i.val)) n *
          (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (s : ℂ))‖ ≤
        Real.sqrt L * (Real.log X) ^ (-κ))
    (h₁ h₂ h₃ : ℤ) (L₁ L₂ L₃ Y eps : ℝ)
    (hblock₁ : L₁ = (2 : ℝ) ^ h₁ *
      (∏ i ∈ I₁, smoothHeathBrownFactorScale (fsList.get i)))
    (_hblock₂ : L₂ = (2 : ℝ) ^ h₂ *
      (∏ i ∈ I₂, smoothHeathBrownFactorScale (fsList.get i)))
    (_hblock₃ : L₃ = (2 : ℝ) ^ h₃ *
      (∏ i ∈ I₃, smoothHeathBrownFactorScale (fsList.get i)))
    (hshift₁ : -(I₁.card : ℤ) ≤ h₁ ∧ h₁ < (I₁.card : ℤ))
    (_hshift₂ : -(I₂.card : ℤ) ≤ h₂ ∧ h₂ < (I₂.card : ℤ))
    (_hshift₃ : -(I₃.card : ℤ) ≤ h₃ ∧ h₃ < (I₃.card : ℤ))
    (hL₁two : 2 ≤ L₁) (hL₂two : 2 ≤ L₂) (hL₃two : 2 ≤ L₃)
    (hYlarge : (2 : ℝ) ^ 16 ≤ Y)
    (hYprod : Y = L₁ * L₂ * L₃)
    (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hαlower : 1 / 4 - eps / 100 ≤ Real.log L₁ / Real.log Y)
    (hαupper : Real.log L₁ / Real.log Y ≤ 1 / 2 + eps / 100)
    (hβγ : |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
      1 / 4 + eps / 100)
    (hWtwo : 2 ≤ W) (hWU : W ≤ U)
    (hUupper : U ≤ Y ^ ((3 / 8 : ℝ) - eps))
    (hlogX : 2 ≤ Real.log X) (hκ : 0 < κ)
    (hshiftedWindow : ∀ t : ℝ,
      (W ≤ |t| ∧ |t| ≤ U) →
      (Real.log X) ^ D / 2 ≤ |t - u| ∧ |t - u| ≤ X)
    (_hu : |u| ≤ W / 2)
    (hq : 1 ≤ q) (hqlog : (q : ℝ) ≤ (Real.log X) ^ B)
    (hresidue : residue selected < q) :
    ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) (fun i => fsList.get i) I₁ q residue L₁ u) t *
        factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) (fun i => fsList.get i) I₂ q residue L₂ u) t *
        factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) (fun i => fsList.get i) I₃ q residue L₃ u) t‖ ≤
      J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
        Real.sqrt Y *
        (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
          Y ^ (-eps / 16 : ℝ)) := by
  classical
  let E : Set ℝ := {t : ℝ | W ≤ |t| ∧ |t| ≤ U}
  let factors : Fin fsList.length → SmoothHeathBrownFactor X :=
    fun i => fsList.get i
  have hlogXpos : 0 < Real.log X := by linarith
  have hdelta0' : 0 < (Real.log X) ^ (-κ) :=
    Real.rpow_pos_of_pos hlogXpos _
  have hdelta1 : (Real.log X) ^ (-κ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (by linarith)
  have hEmeas : MeasurableSet E := by
    have hleft : MeasurableSet {t : ℝ | W ≤ |t|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    have hright : MeasurableSet {t : ℝ | |t| ≤ U} :=
      measurableSet_le continuous_abs.measurable measurable_const
    change MeasurableSet
      ({t : ℝ | W ≤ |t|} ∩ {t : ℝ | |t| ≤ U})
    exact hleft.inter hright
  have hEsubset : E ⊆ Set.Icc (-U) U := by
    intro t ht
    rw [Set.mem_Icc]
    exact abs_le.mp ht.2
  have hL₁pos : 0 < L₁ := by linarith
  have hshort : ∀ t ∈ E,
      ‖∑ n ∈ factorExtractionRealInterval L₁ (2 * L₁),
        (∏ i : I₁,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (factors i.val)) n *
          (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * ((t - u : ℝ) : ℂ))‖ ≤
        (Real.log X) ^ (-κ) * Real.sqrt L₁ := by
    intro t ht
    have hfrequency := hshiftedWindow t ht
    have hsource := hbranch h₁ L₁ L₁ (2 * L₁) hq hqlog residue hresidue
      (t - u) hfrequency.1 hfrequency.2 hblock₁ hshift₁
      le_rfl (by linarith [hL₁pos]) le_rfl
    have hsource' := hsource
    simpa [factors, mul_comm] using hsource'
  simpa [E, factors] using
    smoothHeathBrownThreeGroupResidueBlock_trilinearUncapped
      (z := z) (K := fsList.length) hX factors I₁ I₂ I₃
      hI₁card hI₂card hI₃card q residue u L₁ L₂ L₃ Y eps U
      ((Real.log X) ^ (-κ)) E hL₁pos (by linarith) (by linarith)
      hL₁two hL₂two hL₃two hYlarge hYprod heps0 heps
      (by linarith) hUupper hαlower hαupper hβγ hdelta0' hdelta1
      hEmeas hEsubset hshort

#print axioms smoothHeathBrownThreeGroupActualResidue_trilinear_of_sourceBranch

end FractionalPrimes.Literature.DirichletAdapter

end
