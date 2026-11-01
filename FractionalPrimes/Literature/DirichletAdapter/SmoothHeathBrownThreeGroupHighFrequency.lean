module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupTrilinearInstantiation
public import FractionalPrimes.Literature.Polynomial.ShortIntervalTrilinearTheorem
public import FractionalPrimes.Literature.Polynomial.TrilinearWithoutPointwiseCaps
public import Mathlib.Tactic
@[expose] public section

/-! The large Fourier-shift branch of the finite three-group DP estimate.
After normalizing each grouped block by the exact divisor-moment factor
`Z 20 Y`, the pointwise caps are elementary and the capped trilinear theorem
applies with `delta = 1`. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open MeasureTheory
open FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.LargeValues
open FractionalPrimes.Literature.Twisted

private theorem smoothGroupFactorPolynomial_div_const
    (N : ℝ) (coeff : ℕ → ℂ) (z : ℂ) :
    factorPolynomial N (fun n => coeff n / z) =
      fun t => factorPolynomial N coeff t / z := by
  classical
  funext t
  unfold factorPolynomial FractionalPrimes.Literature.LargeValues.dirichletPolynomial
  calc
    (∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
        FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
            (fun n => coeff n / z)) n t) =
      ∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
        FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)
          n t / z := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [FractionalPrimes.Literature.LargeValues.dirichletTerm,
          FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff,
          div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ = _ := by rw [Finset.sum_div]

private theorem smoothGroupZ_ge_one {Y : ℝ}
    (hY : (2 : ℝ) ^ 16 ≤ Y) :
    1 ≤ Z 20 Y := by
  have hYpos : 0 < Y := by positivity
  have hexp : Real.exp 1 ≤ 4 * Y := by
    calc
      Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      _ ≤ 4 * Y := by nlinarith
  have hlog : 1 ≤ Real.log (4 * Y) := by
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    simpa using h
  rw [Z]
  calc
    1 = 1 * 1 := by ring
    _ ≤ (2 : ℝ) ^ (2 ^ 20 + 1) *
        (Real.log (4 * Y)) ^ (2 ^ 20 - 1) := by
      apply mul_le_mul
      · exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      · exact one_le_pow₀ hlog
      · positivity
      · positivity

/-- For any real shift `u`, an actual three-group residue block has the
source high-frequency mean bound. This is the `|u| > W/2` branch: no
short-interval arithmetic premise is used. The exact normalization is
`Z 20 Y` for each of the three grouped polynomials, and the result restores
the factor `Z 20 Y ^ 3`. -/
theorem smoothHeathBrownThreeGroupHighFrequency_actualResidue
    {X z : ℝ} {K : ℕ}
    (hX : 3 ≤ X)
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I₁ I₂ I₃ : Finset (Fin K))
    (hI₁ : I₁.card ≤ 20) (hI₂ : I₂.card ≤ 20) (hI₃ : I₃.card ≤ 20)
    (q : ℕ) (residue : Fin K → ℕ) (u : ℝ)
    (L₁ L₂ L₃ Y eps T : ℝ) (E : Set ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃)
    (hL₁two : 2 ≤ L₁) (hL₂two : 2 ≤ L₂) (hL₃two : 2 ≤ L₃)
    (hY : (2 : ℝ) ^ 16 ≤ Y) (hYprod : Y = L₁ * L₂ * L₃)
    (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hTtwo : 2 ≤ T) (hTupper : T ≤ Y ^ ((3 / 8 : ℝ) - eps))
    (hαlower : 1 / 4 - eps / 100 ≤ Real.log L₁ / Real.log Y)
    (hαupper : Real.log L₁ / Real.log Y ≤ 1 / 2 + eps / 100)
    (hβγ : |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
      1 / 4 + eps / 100)
    (hEmeas : MeasurableSet E)
    (hEsubset : E ⊆ Set.Icc (-T) T) :
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
      Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
        Real.sqrt Y * (1 + Y ^ (-eps / 16 : ℝ)) := by
  classical
  let a : ℝ := Real.log L₁ / Real.log Y
  let b₁ : ℝ := Real.log L₂ / Real.log Y
  let c : ℝ := Real.log L₃ / Real.log Y
  let coeff₁ : ℕ → ℂ :=
    smoothHeathBrownResidueGroupBlockTwistedCoefficient (z := z) fs I₁ q residue L₁ u
  let coeff₂ : ℕ → ℂ :=
    smoothHeathBrownResidueGroupBlockTwistedCoefficient (z := z) fs I₂ q residue L₂ u
  let coeff₃ : ℕ → ℂ :=
    smoothHeathBrownResidueGroupBlockTwistedCoefficient (z := z) fs I₃ q residue L₃ u
  let z₀ : ℂ := (Z 20 Y : ℂ)
  let coeff₁' : ℕ → ℂ := fun n => coeff₁ n / z₀
  let coeff₂' : ℕ → ℂ := fun n => coeff₂ n / z₀
  let coeff₃' : ℕ → ℂ := fun n => coeff₃ n / z₀
  have hYpos : 0 < Y := by positivity
  have hYgt : 1 < Y := by
    have hp : 1 < (2 : ℝ) ^ 16 := by norm_num
    linarith
  have hlogYpos : 0 < Real.log Y := Real.log_pos hYgt
  have hZ : 1 ≤ Z 20 Y := smoothGroupZ_ge_one hY
  have hZpos : 0 < Z 20 Y := lt_of_lt_of_le (by norm_num) hZ
  have hz : z₀ ≠ 0 := by
    dsimp [z₀]
    exact Complex.ofReal_ne_zero.mpr hZpos.ne'
  have hznorm : ‖z₀‖ = Z 20 Y := by
    simp [z₀, abs_of_pos hZpos]
  have hlogProd : Real.log Y = Real.log L₁ + Real.log L₂ + Real.log L₃ := by
    calc
      Real.log Y = Real.log (L₁ * L₂ * L₃) := by rw [hYprod]
      _ = Real.log (L₁ * L₂) + Real.log L₃ :=
        Real.log_mul (ne_of_gt (mul_pos hL₁ hL₂)) (ne_of_gt hL₃)
      _ = Real.log L₁ + Real.log L₂ + Real.log L₃ := by
        rw [Real.log_mul (ne_of_gt hL₁) (ne_of_gt hL₂)]
  have hsum : a + b₁ + c = 1 := by
    dsimp [a, b₁, c]
    rw [hlogProd]
    have hden : Real.log L₁ + Real.log L₂ + Real.log L₃ ≠ 0 := by
      rw [← hlogProd]
      exact hlogYpos.ne'
    field_simp
  have hpow₁ : Y ^ a = L₁ := by
    rw [Real.rpow_def_of_pos hYpos]
    rw [show Real.log Y * a = Real.log L₁ by
      dsimp [a]
      field_simp]
    exact Real.exp_log hL₁
  have hpow₂ : Y ^ b₁ = L₂ := by
    rw [Real.rpow_def_of_pos hYpos]
    rw [show Real.log Y * b₁ = Real.log L₂ by
      dsimp [b₁]
      field_simp]
    exact Real.exp_log hL₂
  have hpow₃ : Y ^ c = L₃ := by
    rw [Real.rpow_def_of_pos hYpos]
    rw [show Real.log Y * c = Real.log L₃ by
      dsimp [c]
      field_simp]
    exact Real.exp_log hL₃
  have hcoeff₁ : factorCoefficientBound 20 L₁ coeff₁ := by
    simpa [coeff₁] using
      smoothHeathBrownResidueGroupBlock_factorCoefficientBound
        hX fs I₁ hI₁ q residue L₁ u hL₁
  have hcoeff₂ : factorCoefficientBound 20 L₂ coeff₂ := by
    simpa [coeff₂] using
      smoothHeathBrownResidueGroupBlock_factorCoefficientBound
        hX fs I₂ hI₂ q residue L₂ u hL₂
  have hcoeff₃ : factorCoefficientBound 20 L₃ coeff₃ := by
    simpa [coeff₃] using
      smoothHeathBrownResidueGroupBlock_factorCoefficientBound
        hX fs I₃ hI₃ q residue L₃ u hL₃
  have hcoeff₁' : factorCoefficientBound 20 L₁ coeff₁' :=
    factorCoefficientBound_of_norm_le hcoeff₁ (by
      intro n hn
      change ‖coeff₁ n / z₀‖ ≤ ‖coeff₁ n‖
      rw [norm_div, hznorm]
      exact div_le_self (norm_nonneg _) hZ)
  have hcoeff₂' : factorCoefficientBound 20 L₂ coeff₂' :=
    factorCoefficientBound_of_norm_le hcoeff₂ (by
      intro n hn
      change ‖coeff₂ n / z₀‖ ≤ ‖coeff₂ n‖
      rw [norm_div, hznorm]
      exact div_le_self (norm_nonneg _) hZ)
  have hcoeff₃' : factorCoefficientBound 20 L₃ coeff₃' :=
    factorCoefficientBound_of_norm_le hcoeff₃ (by
      intro n hn
      change ‖coeff₃ n / z₀‖ ≤ ‖coeff₃ n‖
      rw [norm_div, hznorm]
      exact div_le_self (norm_nonneg _) hZ)
  have hL₁Y : L₁ ≤ Y := by
    have h23 : 1 ≤ L₂ * L₃ := by
      calc
        1 ≤ 2 * 2 := by norm_num
        _ ≤ L₂ * L₃ := mul_le_mul hL₂two hL₃two (by norm_num) (by linarith)
    rw [hYprod]
    calc
      L₁ = L₁ * 1 := by ring
      _ ≤ L₁ * (L₂ * L₃) := mul_le_mul_of_nonneg_left h23 hL₁.le
      _ = L₁ * L₂ * L₃ := by ring
  have hL₂Y : L₂ ≤ Y := by
    have h13 : 1 ≤ L₁ * L₃ := by
      calc
        1 ≤ 2 * 2 := by norm_num
        _ ≤ L₁ * L₃ := mul_le_mul hL₁two hL₃two (by norm_num) (by linarith)
    rw [hYprod]
    calc
      L₂ = 1 * L₂ := by ring
      _ ≤ (L₁ * L₃) * L₂ := mul_le_mul_of_nonneg_right h13 hL₂.le
      _ = L₁ * L₂ * L₃ := by ring
  have hL₃Y : L₃ ≤ Y := by
    have h12 : 1 ≤ L₁ * L₂ := by
      calc
        1 ≤ 2 * 2 := by norm_num
        _ ≤ L₁ * L₂ := mul_le_mul hL₁two hL₂two (by norm_num) (by linarith)
    rw [hYprod]
    calc
      L₃ = 1 * L₃ := by ring
      _ ≤ (L₁ * L₂) * L₃ := mul_le_mul_of_nonneg_right h12 hL₃.le
      _ = L₁ * L₂ * L₃ := by ring
  have hraw₁ := factorPolynomial_norm_le_Z_sqrt 20 coeff₁ hY hL₁two hL₁Y hcoeff₁
  have hraw₂ := factorPolynomial_norm_le_Z_sqrt 20 coeff₂ hY hL₂two hL₂Y hcoeff₂
  have hraw₃ := factorPolynomial_norm_le_Z_sqrt 20 coeff₃ hY hL₃two hL₃Y hcoeff₃
  have hdiv₁ := smoothGroupFactorPolynomial_div_const L₁ coeff₁ z₀
  have hdiv₂ := smoothGroupFactorPolynomial_div_const L₂ coeff₂ z₀
  have hdiv₃ := smoothGroupFactorPolynomial_div_const L₃ coeff₃ z₀
  have hdiv₁' (t : ℝ) :
      factorPolynomial L₁ coeff₁' t = factorPolynomial L₁ coeff₁ t / z₀ := by
    simpa [coeff₁'] using congrFun hdiv₁ t
  have hdiv₂' (t : ℝ) :
      factorPolynomial L₂ coeff₂' t = factorPolynomial L₂ coeff₂ t / z₀ := by
    simpa [coeff₂'] using congrFun hdiv₂ t
  have hdiv₃' (t : ℝ) :
      factorPolynomial L₃ coeff₃' t = factorPolynomial L₃ coeff₃ t / z₀ := by
    simpa [coeff₃'] using congrFun hdiv₃ t
  have hcap₁ : ∀ t : ℝ,
      ‖factorPolynomial (Y ^ a) coeff₁' t‖ ≤ Real.sqrt (Y ^ a) := by
    intro t
    rw [hpow₁]
    change ‖factorPolynomial L₁ coeff₁' t‖ ≤ Real.sqrt L₁
    rw [hdiv₁' t, norm_div, hznorm]
    calc
      ‖factorPolynomial L₁ coeff₁ t‖ / Z 20 Y ≤
          (Z 20 Y * Real.sqrt L₁) / Z 20 Y :=
        div_le_div_of_nonneg_right (hraw₁ t) hZpos.le
      _ = Real.sqrt L₁ := by field_simp [hZpos.ne']
  have hcap₂ : ∀ t : ℝ,
      ‖factorPolynomial (Y ^ b₁) coeff₂' t‖ ≤ Real.sqrt (Y ^ b₁) := by
    intro t
    rw [hpow₂]
    change ‖factorPolynomial L₂ coeff₂' t‖ ≤ Real.sqrt L₂
    rw [hdiv₂' t, norm_div, hznorm]
    calc
      ‖factorPolynomial L₂ coeff₂ t‖ / Z 20 Y ≤
          (Z 20 Y * Real.sqrt L₂) / Z 20 Y :=
        div_le_div_of_nonneg_right (hraw₂ t) hZpos.le
      _ = Real.sqrt L₂ := by field_simp [hZpos.ne']
  have hcap₃ : ∀ t : ℝ,
      ‖factorPolynomial (Y ^ c) coeff₃' t‖ ≤ Real.sqrt (Y ^ c) := by
    intro t
    rw [hpow₃]
    change ‖factorPolynomial L₃ coeff₃' t‖ ≤ Real.sqrt L₃
    rw [hdiv₃' t, norm_div, hznorm]
    calc
      ‖factorPolynomial L₃ coeff₃ t‖ / Z 20 Y ≤
          (Z 20 Y * Real.sqrt L₃) / Z 20 Y :=
        div_le_div_of_nonneg_right (hraw₃ t) hZpos.le
      _ = Real.sqrt L₃ := by field_simp [hZpos.ne']
  have hcoeff₁pow : factorCoefficientBound 20 (Y ^ a) coeff₁' := by
    simpa only [hpow₁] using hcoeff₁'
  have hcoeff₂pow : factorCoefficientBound 20 (Y ^ b₁) coeff₂' := by
    simpa only [hpow₂] using hcoeff₂'
  have hcoeff₃pow : factorCoefficientBound 20 (Y ^ c) coeff₃' := by
    simpa only [hpow₃] using hcoeff₃'
  have htri := trilinearFiveEighths 20 Y T eps a b₁ c 1
    coeff₁' coeff₂' coeff₃' E hY hTtwo heps0 heps hTupper
    (by dsimp [a]; exact div_nonneg (Real.log_nonneg (by linarith [hL₁two])) hlogYpos.le)
    (by dsimp [b₁]; exact div_nonneg (Real.log_nonneg (by linarith [hL₂two])) hlogYpos.le)
    (by dsimp [c]; exact div_nonneg (Real.log_nonneg (by linarith [hL₃two])) hlogYpos.le)
    hsum hαlower hαupper hβγ (by norm_num) (by norm_num)
    hEmeas hEsubset hcoeff₁pow hcoeff₂pow hcoeff₃pow
    (by intro t ht; simpa using hcap₁ t)
    (by intro t ht; simpa using hcap₂ t)
    (by intro t ht; simpa using hcap₃ t)
    (by intro t ht; simpa using hcap₁ t)
  have hrestore₁ : ∀ t : ℝ,
      factorPolynomial L₁ coeff₁ t = factorPolynomial L₁ coeff₁' t * z₀ := by
    intro t
    rw [hdiv₁' t]
    field_simp [hz]
  have hrestore₂ : ∀ t : ℝ,
      factorPolynomial L₂ coeff₂ t = factorPolynomial L₂ coeff₂' t * z₀ := by
    intro t
    rw [hdiv₂' t]
    field_simp [hz]
  have hrestore₃ : ∀ t : ℝ,
      factorPolynomial L₃ coeff₃ t = factorPolynomial L₃ coeff₃' t * z₀ := by
    intro t
    rw [hdiv₃' t]
    field_simp [hz]
  have hnorm (t : ℝ) :
      ‖factorPolynomial L₁ coeff₁ t * factorPolynomial L₂ coeff₂ t *
          factorPolynomial L₃ coeff₃ t‖ =
        (Z 20 Y) ^ 3 *
          ‖factorPolynomial L₁ coeff₁' t * factorPolynomial L₂ coeff₂' t *
            factorPolynomial L₃ coeff₃' t‖ := by
    rw [hrestore₁ t, hrestore₂ t, hrestore₃ t]
    simp only [norm_mul, hznorm]
    ring
  have hfun :
      (fun t : ℝ =>
        ‖factorPolynomial L₁ coeff₁ t * factorPolynomial L₂ coeff₂ t *
            factorPolynomial L₃ coeff₃ t‖) =
      (fun t : ℝ => (Z 20 Y) ^ 3 *
        ‖factorPolynomial L₁ coeff₁' t * factorPolynomial L₂ coeff₂' t *
          factorPolynomial L₃ coeff₃' t‖) := funext hnorm
  change (∫ t in E,
      ‖factorPolynomial (Y ^ a) coeff₁ t *
        factorPolynomial (Y ^ b₁) coeff₂ t *
        factorPolynomial (Y ^ c) coeff₃ t‖) ≤
      Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
        Real.sqrt Y * (1 + Y ^ (-eps / 16 : ℝ))
  rw [hpow₁, hpow₂, hpow₃]
  rw [hfun, integral_const_mul]
  have htri' :
      (∫ t in E,
        ‖factorPolynomial L₁ coeff₁' t *
          factorPolynomial L₂ coeff₂' t *
          factorPolynomial L₃ coeff₃' t‖) ≤
        J 20 * Real.log (4 * Y) ^ (b 20 + 3) * Real.sqrt Y *
          (1 + Y ^ (-eps / 16 : ℝ)) := by
    simpa [hpow₁, hpow₂, hpow₃] using htri
  calc
    (Z 20 Y) ^ 3 *
        (∫ t in E,
          ‖factorPolynomial L₁ coeff₁' t *
            factorPolynomial L₂ coeff₂' t *
            factorPolynomial L₃ coeff₃' t‖) ≤
      (Z 20 Y) ^ 3 *
        (J 20 * Real.log (4 * Y) ^ (b 20 + 3) * Real.sqrt Y *
          (1 + Y ^ (-eps / 16 : ℝ))) :=
        mul_le_mul_of_nonneg_left htri' (by positivity)
    _ = Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
        Real.sqrt Y * (1 + Y ^ (-eps / 16 : ℝ)) := by ring

#print axioms smoothHeathBrownThreeGroupHighFrequency_actualResidue

end FractionalPrimes.Literature.DirichletAdapter

end
