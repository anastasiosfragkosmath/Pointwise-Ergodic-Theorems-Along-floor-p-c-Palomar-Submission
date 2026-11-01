module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownAlignedThreeGroupSmallGroupSource
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupSourceBranchTrilinear
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupBlockExponentBounds
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupBlockTimeWindow
public import Mathlib.Tactic
@[expose] public section

/-! Exact discrete `lda:dp-from-muf` integral branch for an already recovered
`IImaj` witness.  The theorem combines its fixed first group and selected
source interval estimate with the checked block-scale, exponent, and time
window adapters before applying the actual-residue uncapped trilinear bound.
The component-group partition is never reselected. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.LargeValues

/-- The source three-group integral estimate on the exact partition returned
by `smoothHeathBrownThreeGroupSmallGroupSourceInterval_onIImajWitness`.
Every block scale, exponent display, and shifted time range is supplied by
the checked geometric adapters; the only arithmetic short-interval input is
the selected-group branch for this same first group. -/
theorem smoothHeathBrownThreeGroupActualResidueDPIntegral_of_sourceWitness
    {X z B κ D η W U : ℝ}
    (hX3 : 3 ≤ X)
    (fsList : List (SmoothHeathBrownFactor X))
    (hlen : fsList.length ≤ 20)
    (I J J' : Finset (Fin fsList.length))
    (selected : Fin fsList.length)
    (hIJ : Disjoint I J) (hIJ' : Disjoint I J') (hJJ' : Disjoint J J')
    (hcover : I ∪ J ∪ J' = Finset.univ)
    (hE : 0 < smoothHeathBrownExponentSum fsList)
    (hIlo : (1 / 4 : ℝ) ≤
      subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I)
    (hIhi : subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ≤
      1 / 2)
    (hgap : |subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J -
      subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J'| ≤
        1 / 4)
    (hselected : selected ∈ I)
    (hIcard : I.card ≤ 20) (hJcard : J.card ≤ 20) (hJ'card : J'.card ≤ 20)
    (hNlo : X ^ (1 / 100 : ℝ) ≤
      smoothHeathBrownFactorScale (fsList.get selected))
    (hNhi : smoothHeathBrownFactorScale (fsList.get selected) ≤
      (2 : ℝ) ^ 11 * Real.sqrt X)
    (hsource : ∀ (h : ℤ) (L x y : ℝ) {q' : ℕ},
      1 ≤ q' → (q' : ℝ) ≤ (Real.log X) ^ B →
      (residue' : Fin fsList.length → ℕ) → residue' selected < q' →
      (s : ℝ) → (Real.log X) ^ D / 2 ≤ |s| → |s| ≤ X →
      L = (2 : ℝ) ^ h *
        (∏ i ∈ I, smoothHeathBrownFactorScale (fsList.get i)) →
      -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ) →
      L ≤ x → x ≤ y → y ≤ 2 * L →
      ‖∑ n ∈ factorExtractionRealInterval x y,
        (∏ i : I,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q' (residue' i.val) (fsList.get i.val)) n *
          (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (s : ℂ))‖ ≤
        Real.sqrt L * (Real.log X) ^ (-κ))
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (_hB : 0 < B) (hκ : 0 < κ) (hD : 2 * κ + 10 ≤ D)
    (hη : 0 < η) (hηsmall : η < 3 / 16)
    (hlogThreshold : 10 ^ 6 / η ≤ Real.log X)
    (hPwindow : X / (2 : ℝ) ^ 22 ≤ smoothHeathBrownScaleProduct fsList ∧
      smoothHeathBrownScaleProduct fsList ≤ (2 : ℝ) ^ 22 * X)
    (h₁ h₂ h₃ : ℤ)
    (hh₁ : -(I.card : ℤ) ≤ h₁ ∧ h₁ < I.card)
    (hh₂ : -(J.card : ℤ) ≤ h₂ ∧ h₂ < J.card)
    (hh₃ : -(J'.card : ℤ) ≤ h₃ ∧ h₃ < J'.card)
    (hW : W = (Real.log X) ^ D)
    (hWlower : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hlarge :
      (2 / (η / 2)) * Real.log
        ((2 : ℝ) ^ (42 * ((3 / 8 : ℝ) - η / 2)) *
          logAbsorptionM (η / 2) (4 * D)) ≤ Real.log X)
    (u : ℝ) (hu : |u| ≤ W / 2)
    (q : ℕ) (residue : Fin fsList.length → ℕ)
    (hq : 1 ≤ q) (hqlog : (q : ℝ) ≤ (Real.log X) ^ B)
    (hresidue : residue selected < q) :
    let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
    let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
    let S₃ := smoothHeathBrownSubgroupScaleProduct fsList J'
    let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
    let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
    let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
    let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
    let eps := η / 2
    ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) (fun i => fsList.get i) I q residue L₁ u) t *
        factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) (fun i => fsList.get i) J q residue L₂ u) t *
        factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) (fun i => fsList.get i) J' q residue L₃ u) t‖ ≤
      FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
        (Real.log (4 * Y)) ^ (b 20 + 3) *
        Real.sqrt Y * (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
          Y ^ (-eps / 16 : ℝ)) := by
  classical
  let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
  let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
  let S₃ := smoothHeathBrownSubgroupScaleProduct fsList J'
  let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
  let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
  let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
  let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
  let eps : ℝ := η / 2
  have hXnonneg : 0 ≤ X := by linarith
  have hlogX : 2 ≤ Real.log X := by
    have hratio : 2 ≤ 10 ^ 6 / η := by
      apply (le_div_iff₀ hη).2
      nlinarith [hηsmall]
    exact le_trans hratio hlogThreshold
  have hDnonneg : 0 ≤ D := by linarith
  have hIratio :
      (1 / 4 : ℝ) ≤ Real.log S₁ /
          Real.log (smoothHeathBrownScaleProduct fsList) ∧
      Real.log S₁ / Real.log (smoothHeathBrownScaleProduct fsList) ≤ 1 / 2 := by
    constructor
    · rw [← smoothHeathBrownSubgroupWeightSum_eq_log_ratio fsList hE I]
      exact hIlo
    · rw [← smoothHeathBrownSubgroupWeightSum_eq_log_ratio fsList hE I]
      exact hIhi
  have hJKbalance :
      |Real.log S₂ / Real.log (smoothHeathBrownScaleProduct fsList) -
        Real.log S₃ / Real.log (smoothHeathBrownScaleProduct fsList)| ≤
          1 / 4 := by
    rw [← smoothHeathBrownSubgroupWeightSum_eq_log_ratio fsList hE J,
      ← smoothHeathBrownSubgroupWeightSum_eq_log_ratio fsList hE J']
    exact hgap
  have hLtwoRaw := smoothHeathBrownThreeDyadicBlockScales_ge_two
    fsList hlen hXscale hη hηsmall hlogThreshold I J J' hIJ hIJ' hJJ' hcover
    hPwindow hIratio hJKbalance h₁ h₂ h₃ hh₁ hh₂ hh₃
  have hLtwo : 2 ≤ L₁ ∧ 2 ≤ L₂ ∧ 2 ≤ L₃ := by
    simpa [L₁, L₂, L₃, S₁, S₂, S₃] using hLtwoRaw
  have hYwindowRaw := smoothHeathBrownThreeDyadicBlockProductScale_componentWindow
    fsList hlen I J J' hIJ hIJ' hJJ' hcover hPwindow h₁ h₂ h₃ hh₁ hh₂ hh₃
  have hYlower : X / (2 : ℝ) ^ 42 ≤ Y := by
    simpa [Y, L₁, L₂, L₃, S₁, S₂, S₃] using hYwindowRaw.1
  have hYlargeRaw := smoothHeathBrownThreeGroupBlockTimeWindow
    (X := X) (η := η) (D := D) (W := W) (U := U) (Y := Y)
    (T₀ := (Real.log X) ^ D / 2) (t := U) (u := u)
    hXscale hη hηsmall hDnonneg hW hWlower hWU hU hYlower hlarge rfl
    (by
      have hUpos : 0 ≤ U := le_trans (by linarith : 0 ≤ W) hWU
      constructor
      · rw [abs_of_nonneg hUpos]
        exact hWU
      · rw [abs_of_nonneg hUpos]
    )
    hu
  rcases hYlargeRaw with ⟨hYlarge, hUtwo, hUupper, _, _, _⟩
  have hYprod : Y = L₁ * L₂ * L₃ := by
    simp [Y, L₁, L₂, L₃, S₁, S₂, S₃,
      smoothHeathBrownThreeDyadicBlockProductScale,
      smoothHeathBrownDyadicBlockScale]
  have hblock₁ : L₁ = (2 : ℝ) ^ h₁ *
      (∏ i ∈ I, smoothHeathBrownFactorScale (fsList.get i)) := by
    rfl
  have hblock₂ : L₂ = (2 : ℝ) ^ h₂ *
      (∏ i ∈ J, smoothHeathBrownFactorScale (fsList.get i)) := by
    rfl
  have hblock₃ : L₃ = (2 : ℝ) ^ h₃ *
      (∏ i ∈ J', smoothHeathBrownFactorScale (fsList.get i)) := by
    rfl
  have hexpRaw := smoothHeathBrownThreeGroupBlockExponentBounds
    fsList hlen hXscale hη hηsmall hlogThreshold I J J' hIJ hIJ' hJJ'
    hcover hPwindow hIratio hJKbalance h₁ h₂ h₃ hh₁ hh₂ hh₃
  have hexp :
      (1 / 4 : ℝ) - η / 200 ≤ Real.log L₁ / Real.log Y ∧
      Real.log L₁ / Real.log Y ≤ 1 / 2 + η / 200 ∧
      |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
        1 / 4 + η / 200 := by
    simpa [L₁, L₂, L₃, Y, S₁, S₂, S₃] using hexpRaw
  have hexp₁ : (1 / 4 : ℝ) - eps / 100 ≤ Real.log L₁ / Real.log Y := by
    dsimp [eps]
    nlinarith [hexp.1]
  have hexp₂ : Real.log L₁ / Real.log Y ≤ 1 / 2 + eps / 100 := by
    dsimp [eps]
    nlinarith [hexp.2.1]
  have hexp₃ :
      |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
        1 / 4 + eps / 100 := by
    calc
      |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
          1 / 4 + η / 200 := hexp.2.2
      _ = 1 / 4 + eps / 100 := by dsimp [eps]; ring
  have htimeShifted : ∀ t : ℝ,
      (W ≤ |t| ∧ |t| ≤ U) →
      (Real.log X) ^ D / 2 ≤ |t - u| ∧ |t - u| ≤ X := by
    intro t ht
    have htime := smoothHeathBrownThreeGroupBlockTimeWindow
      (X := X) (η := η) (D := D) (W := W) (U := U) (Y := Y)
      (T₀ := (Real.log X) ^ D / 2) (t := t) (u := u)
      hXscale hη hηsmall hDnonneg hW hWlower hWU hU hYlower hlarge rfl ht hu
    rcases htime with ⟨_, _, _, _, hlow, hhigh⟩
    exact ⟨hlow, hhigh⟩
  have htri := smoothHeathBrownThreeGroupActualResidue_trilinear_of_sourceBranch
    (X := X) (z := z) (B := B) (κ := κ) (D := D)
    (W := W) (U := U) hX3 fsList q residue u I J J' selected
    hIcard hJcard hJ'card hselected hIcard hNlo hNhi hsource
    h₁ h₂ h₃ L₁ L₂ L₃ Y eps hblock₁ hblock₂ hblock₃ hh₁ hh₂ hh₃
    hLtwo.1 hLtwo.2.1 hLtwo.2.2 hYlarge hYprod
    (by dsimp [eps]; positivity)
    (by dsimp [eps]; linarith [hηsmall])
    hexp₁ hexp₂ hexp₃ hWlower hWU hUupper hlogX hκ htimeShifted hu
    hq hqlog hresidue
  simpa [S₁, S₂, S₃, L₁, L₂, L₃, Y, eps] using htri

/-- Source-facing `lda:dp-from-muf` integral branch.  It consumes the
partition and selected factor returned by the witness-preserving small-group
theorem and leaves all three dyadic shifts quantified over their exact source
ranges, so the result can be summed over the finite block decomposition.  The
residue condition remains attached to the selected factor, as in the source. -/
theorem smoothHeathBrownThreeGroupActualResidueDPIntegral_of_IImaj
    {B κ D η : ℝ} (hB : 0 < B) (hκ : 0 < κ)
    (hD : 2 * κ + 10 ≤ D) (hη : 0 < η) (hηsmall : η < 3 / 16) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fsList : List (SmoothHeathBrownFactor X)) →
        fsList.length ≤ 20 → fsList ≠ [] →
        smoothHeathBrownSupportRetained
          (X := X) (z := dyadicMobiusCutoff X) fsList →
        (hE : 0 < smoothHeathBrownExponentSum fsList) →
        (smoothHeathBrownExponentGrouping fsList hE).IImaj (5 / 8) →
        ∃ I J J' : Finset (Fin fsList.length), ∃ selected : Fin fsList.length,
          Disjoint I J ∧ Disjoint I J' ∧ Disjoint J J' ∧
          I ∪ J ∪ J' = Finset.univ ∧
          (1 / 4 : ℝ) ≤
            subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ∧
          subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ≤
            1 / 2 ∧
          |subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J -
            subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J'| ≤
              1 / 4 ∧
          selected ∈ I ∧ I.card ≤ 20 ∧ J.card ≤ 20 ∧ J'.card ≤ 20 ∧
          X ^ (1 / 100 : ℝ) ≤
            smoothHeathBrownFactorScale (fsList.get selected) ∧
          smoothHeathBrownFactorScale (fsList.get selected) ≤
            (2 : ℝ) ^ 11 * Real.sqrt X ∧
          ∀ {W U : ℝ},
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ U →
          U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ) →
          (u : ℝ) → |u| ≤ W / 2 →
          (q : ℕ) → 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          (residue : Fin fsList.length → ℕ) →
          (residue selected < q →
            ∀ (h₁ h₂ h₃ : ℤ),
            (-(I.card : ℤ) ≤ h₁ ∧ h₁ < I.card) →
            (-(J.card : ℤ) ≤ h₂ ∧ h₂ < J.card) →
            (-(J'.card : ℤ) ≤ h₃ ∧ h₃ < J'.card) →
            let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
            let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
            let S₃ := smoothHeathBrownSubgroupScaleProduct fsList J'
            let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
            let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
            let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
            let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
            let eps := η / 2
            ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
              ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
                  (smoothHeathBrownResidueGroupBlockTwistedCoefficient
                    (z := z) (fun i => fsList.get i) I q residue L₁ u) t *
                factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
                  (smoothHeathBrownResidueGroupBlockTwistedCoefficient
                    (z := z) (fun i => fsList.get i) J q residue L₂ u) t *
                factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
                  (smoothHeathBrownResidueGroupBlockTwistedCoefficient
                    (z := z) (fun i => fsList.get i) J' q residue L₃ u) t‖ ≤
              FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
                (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
                (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
                  Y ^ (-eps / 16 : ℝ))) := by
  obtain ⟨Cμ, Xsource, hCμ, hXsourceThree, hsourceOutput⟩ :=
    smoothHeathBrownThreeGroupSmallGroupSourceInterval_onIImajWitness
      (B := B) (K := κ) (D := D) hB hκ hD
  let Rlog : ℝ := 10 ^ 6 / η
  let Rlarge : ℝ := (2 / (η / 2)) * Real.log
    ((2 : ℝ) ^ (42 * ((3 / 8 : ℝ) - η / 2)) *
      logAbsorptionM (η / 2) (4 * D))
  let R := max Rlog Rlarge
  let X₀ := max Xsource (max ((2 : ℝ) ^ 200) (Real.exp R))
  have hX₀three : 3 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans hXsourceThree (le_max_left _ _)
  refine ⟨Cμ, X₀, hCμ, hX₀three, ?_⟩
  intro X z hX₀X hz fsList hlen hfsne hret hE hIImaj
  have hXsource : Xsource ≤ X := by
    exact le_trans (le_max_left _ _) hX₀X
  have hXscale : (2 : ℝ) ^ 200 ≤ X := by
    have hpowX₀ : (2 : ℝ) ^ 200 ≤ X₀ := by
      dsimp [X₀]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact hpowX₀.trans hX₀X
  have hexpRX₀ : Real.exp R ≤ X₀ := by
    dsimp [X₀]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hexpRX : Real.exp R ≤ X := hexpRX₀.trans hX₀X
  have hRlelog : R ≤ Real.log X := by
    have hlog := Real.log_le_log (Real.exp_pos R) hexpRX
    simpa using hlog
  have hRlelog' : max Rlog Rlarge ≤ Real.log X := by
    simpa [R] using hRlelog
  have hlogThreshold : 10 ^ 6 / η ≤ Real.log X := by
    simpa [Rlog] using
      (le_trans (le_max_left Rlog Rlarge) hRlelog')
  have hlarge : (2 / (η / 2)) * Real.log
      ((2 : ℝ) ^ (42 * ((3 / 8 : ℝ) - η / 2)) *
        logAbsorptionM (η / 2) (4 * D)) ≤ Real.log X := by
    simpa [Rlarge] using
      (le_trans (le_max_right Rlog Rlarge) hRlelog')
  have hX3 : 3 ≤ X := le_trans hX₀three hX₀X
  obtain ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover,
      hIlo, hIhi, hgap, hselected, hIcard, hNlo, hNhi, hsource⟩ :=
    hsourceOutput hXsource hz fsList hlen hfsne hret hE hIImaj
  have hJcard : J.card ≤ 20 := by
    exact le_trans (Finset.card_le_card (Finset.subset_univ J)) (by simpa using hlen)
  have hJ'card : J'.card ≤ 20 := by
    exact le_trans (Finset.card_le_card (Finset.subset_univ J')) (by simpa using hlen)
  have hXnonneg : 0 ≤ X := by linarith
  have hPbounds := smoothHeathBrownSupportRetained_scale_bounds
    hlen hfsne hXnonneg hret
  have hPwindow : X / (2 : ℝ) ^ 22 ≤ smoothHeathBrownScaleProduct fsList ∧
      smoothHeathBrownScaleProduct fsList ≤ (2 : ℝ) ^ 22 * X := by
    constructor
    · simpa [div_eq_mul_inv, mul_comm] using hPbounds.1
    · exact hPbounds.2
  refine ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover,
    hIlo, hIhi, hgap, hselected, hIcard, hJcard, hJ'card, hNlo, hNhi, ?_⟩
  intro W U hW hWlower hWU hU u hu q hq hqlog residue hresidue h₁ h₂ h₃
    hh₁ hh₂ hh₃
  exact smoothHeathBrownThreeGroupActualResidueDPIntegral_of_sourceWitness
    (X := X) (z := z) (B := B) (κ := κ) (D := D) (η := η)
    (W := W) (U := U) hX3 fsList hlen I J J' selected
    hIJ hIJ' hJJ' hcover hE hIlo hIhi hgap hselected hIcard hJcard hJ'card
    hNlo hNhi hsource hXscale hB hκ hD hη hηsmall hlogThreshold hPwindow
    h₁ h₂ h₃ hh₁ hh₂ hh₃ hW hWlower hWU hU hlarge u hu q
    residue hq hqlog hresidue

#print axioms smoothHeathBrownThreeGroupActualResidueDPIntegral_of_sourceWitness
#print axioms smoothHeathBrownThreeGroupActualResidueDPIntegral_of_IImaj

end FractionalPrimes.Literature.DirichletAdapter

end
