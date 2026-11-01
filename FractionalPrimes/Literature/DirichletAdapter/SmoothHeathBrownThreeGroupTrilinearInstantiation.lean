module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownResidueGroupDivisorEnvelope
public import FractionalPrimes.Literature.Polynomial.TypeIIGroupedFactorTrilinearBridge
public import FractionalPrimes.Literature.Polynomial.ShortIntervalTrilinearUncapped
public import Mathlib.Tactic
@[expose] public section

/-! Exact coefficient and source-frequency adapters for applying the scalar
`ldm:uncapped` trilinear theorem to three actual residue-restricted smooth
Heath--Brown group blocks. The selected-group short-interval estimate remains
an explicit input, as in `lda:dp-from-muf`.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.LargeValues
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The exact residue-restricted arithmetic convolution coefficient of one
selected group, restricted to the half-open Dirichlet block `(L,2L]`. -/
noncomputable def smoothHeathBrownResidueGroupBlockCoefficient
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L : ℝ) (n : ℕ) : ℂ :=
  if n ∈ dirichletIndices L then
    (∏ i : I,
      smoothHeathBrownResidueFactorArithmeticFunction (z := z)
        q (residue i.val) (fs i.val)) n
  else 0

/-- The source frequency shift is represented by the exact unit coefficient
twist `n^(iu)`. -/
noncomputable def smoothHeathBrownResidueGroupBlockTwistedCoefficient
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L u : ℝ) (n : ℕ) : ℂ :=
  smoothHeathBrownResidueGroupBlockCoefficient (z := z) fs I q residue L n *
    factorTwistMultiplier u n

/-- Every actual residue-restricted group block satisfies the exact `C=20`
coefficient hypothesis of the scalar trilinear theorem, including an
arbitrary unit-frequency shift. -/
theorem smoothHeathBrownResidueGroupBlock_factorCoefficientBound
    {X z : ℝ} (hX : 3 ≤ X) {K : ℕ}
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (hI : I.card ≤ 20)
    (q : ℕ) (residue : Fin K → ℕ) (L u : ℝ) (hL : 0 < L) :
    factorCoefficientBound 20 L
      (smoothHeathBrownResidueGroupBlockTwistedCoefficient (z := z)
        fs I q residue L u) := by
  intro n hn
  have hLbound : L < (n : ℝ) := by
    have hn' := (Finset.mem_filter.mp hn).2
    exact hn'
  have hnposReal : 0 < (n : ℝ) := lt_trans hL hLbound
  have hnpos : 0 < n := by exact_mod_cast hnposReal
  have hgroup := smoothHeathBrownResidueGroupCoefficient_norm_le_divisorSquareTwenty
    (z := z) hX fs I hI q residue ⟨n, hnpos⟩
  change ‖smoothHeathBrownResidueGroupBlockCoefficient (z := z) fs I q residue L n *
    factorTwistMultiplier u n‖ ≤ _
  rw [norm_mul, factorTwistMultiplier_norm, mul_one]
  simpa [smoothHeathBrownResidueGroupBlockCoefficient, hn] using hgroup

/-- The twisted polynomial of a residue-restricted group block is exactly its
source Mellin interval sum, with the original half-open endpoints and the
frequency shifted from `t` to `t-u`. -/
theorem smoothHeathBrownResidueGroupBlock_factorPolynomial_eq_sourceInterval
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L u t : ℝ) (hL : 0 < L) :
    factorPolynomial L
        (smoothHeathBrownResidueGroupBlockTwistedCoefficient (z := z)
          fs I q residue L u) t =
      ∑ n ∈ factorExtractionRealInterval L (2 * L),
        (∏ i : I,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (fs i.val)) n *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * ((t - u : ℝ) : ℂ)) := by
  classical
  let g : ℕ → ℂ := smoothHeathBrownResidueGroupBlockCoefficient
    (z := z) fs I q residue L
  have hcoeff :
      smoothHeathBrownResidueGroupBlockTwistedCoefficient (z := z)
          fs I q residue L u =
        selectedGroupTrilinearCoeff (1 : ℝ) 1 g (fun _ => 1) u := by
    funext n
    simp [smoothHeathBrownResidueGroupBlockTwistedCoefficient,
      smoothHeathBrownResidueGroupBlockCoefficient, g,
      selectedGroupTrilinearCoeff, Nat.one_mul]
  rw [hcoeff]
  rw [factorPolynomial_eq_selectedGroupMellinBlock hL (by norm_num : 0 < (1 : ℝ))
    (r := 1) g (fun _ => 1) (t := t) (T := u)]
  norm_num
  have hindices : dirichletIndices L = factorExtractionRealInterval L (2 * L) :=
    dirichletIndices_eq_factorExtractionRealInterval hL.le
  apply Finset.sum_congr rfl
  intro n hn
  have hnindices : n ∈ dirichletIndices L := by rw [hindices]; exact hn
  have hnwindow :=
    (mem_factorExtractionRealInterval (by linarith : 0 ≤ L)
      (by positivity : 0 ≤ 2 * L) n).mp hn
  have hnposReal : 0 < (n : ℝ) := lt_trans hL hnwindow.1
  have hnpos : 0 < n := by exact_mod_cast hnposReal
  simp [g, smoothHeathBrownResidueGroupBlockCoefficient, hnindices,
    factorExtractionMellinWeight, hnpos]

/-- The three-group source short-interval input, when applied to actual
residue-restricted group blocks, gives the distinguished small-factor
hypothesis in `ldm:uncapped`. The other two block coefficients satisfy the
same exact divisor envelope, so the scalar trilinear conclusion follows.

The exponent and time-window hypotheses are the exact outputs required from
the checked three-group block geometry and `smoothHeathBrownThreeGroupBlockTimeWindow`.
-/
theorem smoothHeathBrownThreeGroupResidueBlock_trilinearUncapped
    {X z : ℝ} {K : ℕ} (hX : 3 ≤ X)
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I₁ I₂ I₃ : Finset (Fin K))
    (hI₁ : I₁.card ≤ 20) (hI₂ : I₂.card ≤ 20) (hI₃ : I₃.card ≤ 20)
    (q : ℕ) (residue : Fin K → ℕ) (u : ℝ)
    (L₁ L₂ L₃ Y eps T delta : ℝ) (E : Set ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃)
    (hL₁two : 2 ≤ L₁) (hL₂two : 2 ≤ L₂) (hL₃two : 2 ≤ L₃)
    (hY : (2 : ℝ) ^ 16 ≤ Y) (hYprod : Y = L₁ * L₂ * L₃)
    (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hT0 : 2 ≤ T) (hTupper : T ≤ Y ^ ((3 / 8 : ℝ) - eps))
    (hαlower : 1 / 4 - eps / 100 ≤ Real.log L₁ / Real.log Y)
    (hαupper : Real.log L₁ / Real.log Y ≤ 1 / 2 + eps / 100)
    (hβγ : |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
      1 / 4 + eps / 100)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hEmeas : MeasurableSet E)
    (hEsubset : E ⊆ Set.Icc (-T) T)
    (hShort : ∀ t ∈ E,
      ‖∑ n ∈ factorExtractionRealInterval L₁ (2 * L₁),
        (∏ i : I₁,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (fs i.val)) n *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * ((t - u : ℝ) : ℂ))‖ ≤
        delta * Real.sqrt L₁) :
    (∫ t in E,
      ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) fs I₁ q residue L₁ u) t *
        factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) fs I₂ q residue L₂ u) t *
        factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) fs I₃ q residue L₃ u) t‖) ≤
      J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
        (delta ^ (1 / 16 : ℝ) + Y ^ (-eps / 16 : ℝ)) := by
  let alpha : ℝ := Real.log L₁ / Real.log Y
  let beta : ℝ := Real.log L₂ / Real.log Y
  let gamma : ℝ := Real.log L₃ / Real.log Y
  have hYpos : 0 < Y := by
    have hYlowerPos : 0 < (2 : ℝ) ^ 16 := by positivity
    exact lt_of_lt_of_le hYlowerPos hY
  have hYgt1 : 1 < Y := by
    have hpow : 1 < (2 : ℝ) ^ 16 := by norm_num
    linarith
  have hlogYpos : 0 < Real.log Y := Real.log_pos hYgt1
  have hLnonneg : 0 ≤ Real.log L₁ ∧ 0 ≤ Real.log L₂ ∧ 0 ≤ Real.log L₃ := by
    exact ⟨Real.log_nonneg (by linarith), Real.log_nonneg (by linarith),
      Real.log_nonneg (by linarith)⟩
  have hα0 : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg hLnonneg.1 hlogYpos.le
  have hβ0 : 0 ≤ beta := by
    dsimp [beta]
    exact div_nonneg hLnonneg.2.1 hlogYpos.le
  have hγ0 : 0 ≤ gamma := by
    dsimp [gamma]
    exact div_nonneg hLnonneg.2.2 hlogYpos.le
  have hlogProd : Real.log Y = Real.log L₁ + Real.log L₂ + Real.log L₃ := by
    calc
      Real.log Y = Real.log (L₁ * L₂ * L₃) := by rw [hYprod]
      _ = Real.log (L₁ * L₂) + Real.log L₃ :=
        Real.log_mul (ne_of_gt (mul_pos hL₁ hL₂)) (ne_of_gt hL₃)
      _ = Real.log L₁ + Real.log L₂ + Real.log L₃ := by
        rw [Real.log_mul (ne_of_gt hL₁) (ne_of_gt hL₂)]
  have hsum : alpha + beta + gamma = 1 := by
    dsimp [alpha, beta, gamma]
    rw [hlogProd]
    calc
      Real.log L₁ / (Real.log L₁ + Real.log L₂ + Real.log L₃) +
          Real.log L₂ / (Real.log L₁ + Real.log L₂ + Real.log L₃) +
          Real.log L₃ / (Real.log L₁ + Real.log L₂ + Real.log L₃) =
        (Real.log L₁ + Real.log L₂ + Real.log L₃) /
          (Real.log L₁ + Real.log L₂ + Real.log L₃) := by ring
      _ = 1 := by
        have hden : 0 < Real.log L₁ + Real.log L₂ + Real.log L₃ := by
          rw [← hlogProd]
          exact hlogYpos
        exact div_self (ne_of_gt hden)
  have hL₁pow : Y ^ alpha = L₁ := by
    rw [Real.rpow_def_of_pos hYpos]
    rw [show Real.log Y * alpha = Real.log L₁ by
      dsimp [alpha]
      field_simp]
    exact Real.exp_log hL₁
  have hL₂pow : Y ^ beta = L₂ := by
    rw [Real.rpow_def_of_pos hYpos]
    rw [show Real.log Y * beta = Real.log L₂ by
      dsimp [beta]
      field_simp]
    exact Real.exp_log hL₂
  have hL₃pow : Y ^ gamma = L₃ := by
    rw [Real.rpow_def_of_pos hYpos]
    rw [show Real.log Y * gamma = Real.log L₃ by
      dsimp [gamma]
      field_simp]
    exact Real.exp_log hL₃
  let c₁ := smoothHeathBrownResidueGroupBlockTwistedCoefficient
    (z := z) fs I₁ q residue L₁ u
  let c₂ := smoothHeathBrownResidueGroupBlockTwistedCoefficient
    (z := z) fs I₂ q residue L₂ u
  let c₃ := smoothHeathBrownResidueGroupBlockTwistedCoefficient
    (z := z) fs I₃ q residue L₃ u
  have hc₁L : factorCoefficientBound 20 L₁ c₁ := by
    simpa [c₁] using
      smoothHeathBrownResidueGroupBlock_factorCoefficientBound
        hX fs I₁ hI₁ q residue L₁ u hL₁
  have hc₂L : factorCoefficientBound 20 L₂ c₂ := by
    simpa [c₂] using
      smoothHeathBrownResidueGroupBlock_factorCoefficientBound
        hX fs I₂ hI₂ q residue L₂ u hL₂
  have hc₃L : factorCoefficientBound 20 L₃ c₃ := by
    simpa [c₃] using
      smoothHeathBrownResidueGroupBlock_factorCoefficientBound
        hX fs I₃ hI₃ q residue L₃ u hL₃
  have hc₁ : factorCoefficientBound 20 (Y ^ alpha) c₁ := by
    simpa [hL₁pow] using hc₁L
  have hc₂ : factorCoefficientBound 20 (Y ^ beta) c₂ := by
    simpa [hL₂pow] using hc₂L
  have hc₃ : factorCoefficientBound 20 (Y ^ gamma) c₃ := by
    simpa [hL₃pow] using hc₃L
  have hsmall : ∀ t ∈ E,
      ‖factorPolynomial (Y ^ alpha) c₁ t‖ ≤ delta * Real.sqrt (Y ^ alpha) := by
    intro t ht
    have hsource := hShort t ht
    rw [show (Y ^ alpha) = L₁ by exact hL₁pow,
      show c₁ = smoothHeathBrownResidueGroupBlockTwistedCoefficient
        fs I₁ q residue L₁ u by rfl]
    rw [smoothHeathBrownResidueGroupBlock_factorPolynomial_eq_sourceInterval
      (z := z) fs I₁ q residue L₁ u t hL₁]
    have heq :
        (∑ n ∈ factorExtractionRealInterval L₁ (2 * L₁),
          (∏ i : I₁,
            smoothHeathBrownResidueFactorArithmeticFunction (z := z)
              q (residue i.val) (fs i.val)) n *
            (factorExtractionMellinWeight (fun _ => 1) (t - u) n)) =
        ∑ n ∈ factorExtractionRealInterval L₁ (2 * L₁),
          (∏ i : I₁,
            smoothHeathBrownResidueFactorArithmeticFunction (z := z)
              q (residue i.val) (fs i.val)) n *
            (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * ((t - u : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnwindow :=
        (mem_factorExtractionRealInterval (by linarith : 0 ≤ L₁)
          (by positivity : 0 ≤ 2 * L₁) n).mp hn
      have hnpositiveReal : 0 < (n : ℝ) := lt_trans hL₁ hnwindow.1
      have hnpositive : 0 < n := by exact_mod_cast hnpositiveReal
      simp [factorExtractionMellinWeight, hnpositive]
    simpa [heq] using hsource
  exact trilinearUncapped 20 Y eps T alpha beta gamma delta E c₁ c₂ c₃
    hY heps0 heps hT0 hTupper hα0 hβ0 hγ0 hsum
    (by simpa [alpha] using hαlower) (by simpa [alpha] using hαupper)
    (by simpa [beta, gamma] using hβγ) hdelta0 hdelta1 hEmeas hEsubset
    hc₁ hc₂ hc₃ hsmall

#print axioms smoothHeathBrownResidueGroupBlock_factorCoefficientBound
#print axioms smoothHeathBrownResidueGroupBlock_factorPolynomial_eq_sourceInterval
#print axioms smoothHeathBrownThreeGroupResidueBlock_trilinearUncapped

end FractionalPrimes.Literature.DirichletAdapter

end
