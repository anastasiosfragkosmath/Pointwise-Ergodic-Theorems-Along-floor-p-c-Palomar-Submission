module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedAllocationTrilinearK
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWAllocatedScale

/-! Exact allocated-scale geometry and the conditional blockwise uncapped
estimate for one retained selected-Möbius PTW block. -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 4000000

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- Reparameterizing a positive length by its logarithmic exponent is exact. -/
theorem selectedMobiusPTW_length_eq_rpow_log
    {Y M : ℝ} (hY : 1 < Y) (hM : 0 < M) :
    Y ^ (Real.log M / Real.log Y) = M := by
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  rw [Real.rpow_def_of_pos (by linarith : 0 < Y)]
  calc
    Real.exp (Real.log Y * (Real.log M / Real.log Y)) =
        Real.exp (Real.log M) := by
          congr 1
          field_simp [ne_of_gt hlogY]
    _ = M := Real.exp_log hM

/-- The numerical geometry together with the two nondistinguished allocated
lengths. This records that all three uncapped exponents are the logarithmic
lengths of the actual quotient scales. -/
structure SelectedMobiusPTWAllocatedGeometry (eps Y U : ℝ) where
  uncapped : SelectedPTWAllocationGeometry eps Y U
  M₂ : ℝ
  M₃ : ℝ
  hM₂ : M₂ = Y ^ uncapped.beta
  hM₃ : M₃ = Y ^ uncapped.gamma

/-- Retained source scales and the divisor allocation produce the exact
allocated logarithmic exponents used by `ldm:uncapped`. The source threshold
`hdev` is left explicit; the theorem does not silently replace allocated
exponents by their unallocated source values. -/
def selectedMobiusPTW_allocated_uncapped_geometry
    {X C₀ ℓ a eps U γ₁ γ₂ γ₃ N₁ N₂ N₃ r₁ r₂ r₃ d
      M₁ M₂ M₃ Y : ℝ}
    (hX : 1 < X) (hℓ : ℓ = Real.log X) (hℓone : 1 ≤ ℓ)
    (ha : 0 ≤ a) (hC₀ : 1 ≤ C₀)
    (hγsum : γ₁ + γ₂ + γ₃ = 1)
    (hγ₁lo : 1 / 4 ≤ γ₁) (hγ₁hi : γ₁ ≤ 1 / 2)
    (hγ₂lo : 0 ≤ γ₂) (hγ₃lo : 0 ≤ γ₃)
    (hγgap : |γ₂ - γ₃| ≤ 1 / 4)
    (hN₁lower : C₀⁻¹ * X ^ γ₁ ≤ N₁)
    (hN₁upper : N₁ ≤ C₀ * X ^ γ₁)
    (hN₂lower : C₀⁻¹ * X ^ γ₂ ≤ N₂)
    (hN₂upper : N₂ ≤ C₀ * X ^ γ₂)
    (hN₃lower : C₀⁻¹ * X ^ γ₃ ≤ N₃)
    (hN₃upper : N₃ ≤ C₀ * X ^ γ₃)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hr₁one : 1 ≤ r₁) (hr₂one : 1 ≤ r₂) (hr₃one : 1 ≤ r₃)
    (hd : 1 ≤ d) (halloc : r₁ * r₂ * r₃ = d)
    (hr₁d : r₁ ≤ d) (hr₂d : r₂ ≤ d) (hr₃d : r₃ ≤ d)
    (hdbound : d ≤ ℓ ^ a)
    (hM₁ : M₁ = N₁ / r₁) (hM₂ : M₂ = N₂ / r₂)
    (hM₃ : M₃ = N₃ / r₃) (hY : Y = M₁ * M₂ * M₃)
    (hE : 3 * Real.log C₀ + a * Real.log ℓ ≤ ℓ / 2)
    (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hdev : 2 * (3 * Real.log C₀ + a * Real.log ℓ) /
        Real.log Y ≤ eps / 300)
    (hU0 : 2 ≤ U) (hU : U ≤ Y ^ (3 / 8 - eps)) :
    SelectedMobiusPTWAllocatedGeometry eps Y U := by
  let alpha := Real.log M₁ / Real.log Y
  let beta := Real.log M₂ / Real.log Y
  let gamma := Real.log M₃ / Real.log Y
  have hgeom := selectedMobiusPTW_allocated_length_log_geometry
    hX hℓ hℓone ha hC₀ hγsum
    hN₁lower hN₁upper hN₂lower hN₂upper hN₃lower hN₃upper
    hr₁ hr₂ hr₃ hr₁one hr₂one hr₃one hd halloc hr₁d hr₂d hr₃d
    hdbound (le_trans (by norm_num) hγ₁lo) hγ₂lo hγ₃lo
    hM₁ hM₂ hM₃ hY hE
  rcases hgeom with ⟨hYpos, hYlower, hYlog, hsum, hdev₁, hdev₂, hdev₃⟩
  have hYone : 1 < Y := by
    have hXhalf : 1 < X ^ (1 / 2 : ℝ) := by
      apply Real.one_lt_rpow (by linarith : 1 < X)
      norm_num
    exact lt_of_lt_of_le hXhalf hYlower
  have hM₁pos : 0 < M₁ := by
    rw [hM₁]
    have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) hC₀
    have hXpos : 0 < X := by linarith
    have hN₁pos : 0 < N₁ := by
      exact lt_of_lt_of_le
        (mul_pos (inv_pos.mpr hC₀pos) (Real.rpow_pos_of_pos hXpos γ₁))
        hN₁lower
    exact div_pos hN₁pos hr₁
  have hM₂pos : 0 < M₂ := by
    rw [hM₂]
    have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) hC₀
    have hXpos : 0 < X := by linarith
    have hN₂pos : 0 < N₂ := by
      exact lt_of_lt_of_le
        (mul_pos (inv_pos.mpr hC₀pos) (Real.rpow_pos_of_pos hXpos γ₂))
        hN₂lower
    exact div_pos hN₂pos hr₂
  have hM₃pos : 0 < M₃ := by
    rw [hM₃]
    have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) hC₀
    have hXpos : 0 < X := by linarith
    have hN₃pos : 0 < N₃ := by
      exact lt_of_lt_of_le
        (mul_pos (inv_pos.mpr hC₀pos) (Real.rpow_pos_of_pos hXpos γ₃))
        hN₃lower
    exact div_pos hN₃pos hr₃
  have hlogY : 0 < Real.log Y := Real.log_pos hYone
  have hαdev : |alpha - γ₁| ≤ eps / 300 := by
    dsimp [alpha]
    exact hdev₁.trans hdev
  have hβdev : |beta - γ₂| ≤ eps / 300 := by
    dsimp [beta]
    exact hdev₂.trans hdev
  have hγdev : |gamma - γ₃| ≤ eps / 300 := by
    dsimp [gamma]
    exact hdev₃.trans hdev
  have hγ₂lower : 1 / 8 ≤ γ₂ := by
    have hgap := abs_le.mp hγgap
    nlinarith [hγsum, hγ₁hi]
  have hγ₃lower : 1 / 8 ≤ γ₃ := by
    have hgap := abs_le.mp hγgap
    nlinarith [hγsum, hγ₁hi]
  have hepssmall : eps / 300 ≤ 1 / 8 := by
    nlinarith [heps]
  have hα0 : 0 ≤ alpha := by
    have hdev' := abs_le.mp hαdev
    linarith [hγ₁lo]
  have hβ0 : 0 ≤ beta := by
    have hdev' := abs_le.mp hβdev
    linarith [hγ₂lower]
  have hγ0 : 0 ≤ gamma := by
    have hdev' := abs_le.mp hγdev
    linarith [hγ₃lower]
  have hαlow : 1 / 4 - eps / 100 ≤ alpha := by
    have hdev' := abs_le.mp hαdev
    linarith [hγ₁lo, heps0]
  have hαhigh : alpha ≤ 1 / 2 + eps / 100 := by
    have hdev' := abs_le.mp hαdev
    linarith [hγ₁hi, heps0]
  have hβγ : |beta - gamma| ≤ 1 / 4 + eps / 100 := by
    have hβ' := abs_le.mp hβdev
    have hγ' := abs_le.mp hγdev
    have hgap := abs_le.mp hγgap
    rw [abs_le]
    constructor <;> linarith [heps0]
  have hsum' : alpha + beta + gamma = 1 := by
    dsimp [alpha, beta, gamma]
    exact hsum
  have hM₁pow : M₁ = Y ^ alpha := by
    dsimp [alpha]
    exact (selectedMobiusPTW_length_eq_rpow_log hYone hM₁pos).symm
  have hM₂pow : M₂ = Y ^ beta := by
    dsimp [beta]
    exact (selectedMobiusPTW_length_eq_rpow_log hYone hM₂pos).symm
  have hM₃pow : M₃ = Y ^ gamma := by
    dsimp [gamma]
    exact (selectedMobiusPTW_length_eq_rpow_log hYone hM₃pos).symm
  refine ⟨?_, M₂, M₃, ?_, ?_⟩
  · exact ⟨alpha, beta, gamma, M₁, hM₁pos, hM₁pow,
      heps0, heps, hU0, hU, hα0, hβ0, hγ0, hsum', hαlow, hαhigh, hβγ⟩
  · simpa [beta] using hM₂pow
  · simpa [gamma] using hM₃pow

private theorem selectedPTW_divisorCoefficient_two_ge_one'
    {r : ℕ} (hr : 0 < r) : 1 ≤ divisorCoefficient 2 r := by
  have heq : divisorCoefficient 2 r = r.divisors.card := by
    change (ArithmeticFunction.zeta ^ 2) r = r.divisors.card
    rw [show (2 : ℕ) = 1 + 1 by omega, pow_succ, pow_one,
      ArithmeticFunction.mul_zeta_apply]
    calc
      (∑ d ∈ r.divisors, ArithmeticFunction.zeta d) =
          ∑ d ∈ r.divisors, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact ArithmeticFunction.zeta_apply_ne
          (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
      _ = r.divisors.card := by simp
  rw [heq]
  have hmem : 1 ∈ r.divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd r, Nat.ne_of_gt hr⟩
  exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨1, hmem⟩)

private theorem selectedPTWFactorScale_ge_one'
    {X : ℝ} (hX : 3 ≤ X) {r : ℕ} (hr : 0 < r) :
    1 ≤ selectedPTWFactorScale X r := by
  have hlog := log_eightX_gt_one hX
  have hdivNat := selectedPTW_divisorCoefficient_two_ge_one' hr
  have hdiv : 1 ≤ (divisorCoefficient 2 r : ℝ) := by exact_mod_cast hdivNat
  have hpow : 1 ≤ (divisorCoefficient 2 r : ℝ) ^ 20 := one_le_pow₀ hdiv
  have hbase : 1 ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) := by
    nlinarith [hlog]
  have hbaseNonneg : 0 ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) := by
    positivity
  unfold selectedPTWFactorScale
  calc
    1 ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) := hbase
    _ = ((2 : ℝ) ^ 10 * Real.log (8 * X)) * 1 := by ring
    _ ≤ ((2 : ℝ) ^ 10 * Real.log (8 * X)) *
        (divisorCoefficient 2 r : ℝ) ^ 20 :=
      mul_le_mul_of_nonneg_left hpow hbaseNonneg

/-- One retained allocated three-group block satisfies the exact uncapped
`ldm:trilinear` integral bound at the quotient base `Y`. The three coefficient
normalizations are the literal source scales `2^10 log(8X) d₂(rᵢ)^20`; the
frequency window and first-factor Mellin estimate are retained as explicit
inputs. The geometry object is supplied by
`selectedMobiusPTW_allocated_uncapped_geometry`. -/
theorem selectedMobiusPTW_allocated_block_uncapped
    {X Y U eps a Tfreq z : ℝ}
    (c : ℂ) (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    (r₁ r₂ r₃ : ℕ) (χ₁ χ₂ χ₃ : ℕ → ℂ)
    (geometry : SelectedMobiusPTWAllocatedGeometry eps Y U)
    (hXsrc : 3 ≤ X) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : fs₁.length ≤ 20) (hlen₂ : fs₂.length ≤ 20)
    (hlen₃ : fs₃.length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight fs₁ ≤ Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight fs₂ ≤ Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight fs₃ ≤ Real.log (8 * X))
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hr₃ : 1 ≤ r₃)
    (hY : (2 : ℝ) ^ 16 ≤ Y)
    (hδ0 : 0 < (Real.log X) ^ (-20 * a))
    (hδ : (Real.log X) ^ (-20 * a) ≤ 1)
    (hχ₁ : ∀ n, ‖χ₁ n‖ ≤ 1) (hχ₂ : ∀ n, ‖χ₂ n‖ ≤ 1)
    (hχ₃ : ∀ n, ‖χ₃ n‖ ≤ 1)
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hblock : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖∑ n ∈ factorExtractionRealInterval
          geometry.uncapped.M (2 * geometry.uncapped.M),
        toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
            (r₁ * n) * factorExtractionMellinWeight χ₁ s n‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt geometry.uncapped.M) :
    (∫ t in Set.Icc (-U) U,
      ‖((selectedPTWFactorScale X r₁ *
          selectedPTWFactorScale X r₂ *
            selectedPTWFactorScale X r₃ : ℝ) : ℂ) *
        (factorPolynomial (Y ^ geometry.uncapped.alpha)
            (selectedGroupTrilinearCoeff
              (selectedPTWFactorScale X r₁) r₁
              (fun n => toComplexArithmeticFunction
                (groupedDyadicFactor z c fs₁) n) χ₁ Tfreq) t *
          factorPolynomial (Y ^ geometry.uncapped.beta)
            (selectedGroupTrilinearCoeff
              (selectedPTWFactorScale X r₂) r₂
              (fun n => toComplexArithmeticFunction
                (dyadicConvolutionPositiveComplex z fs₂) n) χ₂ Tfreq) t *
          factorPolynomial (Y ^ geometry.uncapped.gamma)
            (selectedGroupTrilinearCoeff
              (selectedPTWFactorScale X r₃) r₃
              (fun n => toComplexArithmeticFunction
                (dyadicConvolutionPositiveComplex z fs₃) n) χ₃ Tfreq) t)‖) ≤
      selectedPTWFactorScale X r₁ * selectedPTWFactorScale X r₂ *
        selectedPTWFactorScale X r₃ *
        (J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y *
            (((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
              Y ^ (-eps / 16 : ℝ))) := by
  classical
  let G := geometry.uncapped
  let B₁ := selectedPTWFactorScale X r₁
  let B₂ := selectedPTWFactorScale X r₂
  let B₃ := selectedPTWFactorScale X r₃
  have hB₁ : 1 ≤ B₁ := selectedPTWFactorScale_ge_one' hXsrc
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hr₁)
  have hB₂ : 1 ≤ B₂ := selectedPTWFactorScale_ge_one' hXsrc
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hr₂)
  have hB₃ : 1 ≤ B₃ := selectedPTWFactorScale_ge_one' hXsrc
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hr₃)
  have hB₁pos : 0 < B₁ := lt_of_lt_of_le (by norm_num) hB₁
  have hB₂pos : 0 < B₂ := lt_of_lt_of_le (by norm_num) hB₂
  have hB₃pos : 0 < B₃ := lt_of_lt_of_le (by norm_num) hB₃
  have hscale₁ : (2 : ℝ) ^ 10 * Real.log (8 * X) *
      (divisorCoefficient 2 r₁ : ℝ) ^ 20 ≤ B₁ := by
    dsimp [B₁, selectedPTWFactorScale]
    rfl
  have hscale₂ : (2 : ℝ) ^ 10 * Real.log (8 * X) *
      (divisorCoefficient 2 r₂ : ℝ) ^ 20 ≤ B₂ := by
    dsimp [B₂, selectedPTWFactorScale]
    rfl
  have hscale₃ : (2 : ℝ) ^ 10 * Real.log (8 * X) *
      (divisorCoefficient 2 r₃ : ℝ) ^ 20 ≤ B₃ := by
    dsimp [B₃, selectedPTWFactorScale]
    rfl
  have hE : MeasurableSet (Set.Icc (-U) U) := measurableSet_Icc
  have hEsub : Set.Icc (-U) U ⊆ Set.Icc (-U) U := fun _ ht => ht
  have hbound := selectedDyadicGroupAllocationTrilinearIntegral_bound
    Y eps U G.alpha G.beta G.gamma X a G.M B₁ B₂ B₃ Tfreq z
    (Set.Icc (-U) U) c fs₁ fs₂ fs₃ r₁ r₂ r₃ χ₁ χ₂ χ₃
    hXsrc hc hlen₁ hlen₂ hlen₃ hweight₁ hweight₂ hweight₃
    hr₁ hr₂ hr₃ hscale₁ hscale₂ hscale₃
    G.hM G.hMpow hB₁ hB₁pos hB₂pos hB₃pos hY G.heps0 G.heps
    G.hU0 G.hU G.ha0 G.hb0 G.hc0 G.hsum G.haLow G.haHigh G.hbc
    hδ0 hδ hE hEsub hχ₁ hχ₂ hχ₃ hfreq hblock
  simpa [G, B₁, B₂, B₃] using hbound

#print axioms selectedMobiusPTW_length_eq_rpow_log
#print axioms selectedMobiusPTW_allocated_uncapped_geometry
#print axioms selectedMobiusPTW_allocated_block_uncapped

end FractionalPrimes.Literature.DirichletMean

end
