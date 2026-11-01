module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWLogBudget
public import FractionalPrimes.Literature.Twisted.AbsoluteTransferInputs
public import FractionalPrimes.Literature.Twisted.PrefixTwistRange
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import Mathlib.Tactic

/-! The finite transfer from a uniform full-frequency integral bound to the
long-prefix normalized estimate in the selected Möbius PTW argument. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The source smoothing scale `W=(log X)^(10a)`. -/
def selectedMobiusPTWTransferW (X a : ℝ) : ℝ :=
  (Real.log X) ^ (10 * a)

/-- The exponent in the source full-frequency integral bound, before the
factor `(1+log W)` in absolute transfer contributes one further logarithm. -/
def selectedMobiusPTWSourceIntegralExponent (a : ℝ) : ℝ :=
  (selectedMobiusPTWLogExponent : ℝ) + 3 - 5 * a / 4 + a / 500

/-- A threshold that supplies the exact prefix-range threshold and the
additional `log`-power comparison needed for `h₀ W² ≤ h`. -/
noncomputable def selectedMobiusPTWTransferGrowthThreshold
    (a eta : ℝ) : ℝ :=
  max (prefixTwistRangeThreshold a eta)
    (Real.exp ((2 / (1 / 8 + eta)) *
      Real.log (logAbsorptionM (1 / 8 + eta) (22 * a))))

/-- Above the explicit growth threshold, the exact source mass and prefix
length comparisons hold, including the power comparison that ensures
`h₀ W² ≤ h` for every prefix `h ≥ H(log X)^(-2a)`. -/
theorem selectedMobiusPTWTransferGrowth_of_threshold
    {a eta X : ℝ}
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta : 0 < eta)
    (hX : selectedMobiusPTWTransferGrowthThreshold a eta ≤ X) :
    2 ≤ Real.log X ∧
      (2 : ℝ) ^ 120 ≤ X ∧
      (Real.log X) ^ (22 * a) ≤ X ^ (1 / 8 + eta) := by
  have ha2 : 2 ≤ a := by
    have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
    have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
    exact h2.trans ha
  have hprefix : prefixTwistRangeThreshold a eta ≤ X :=
    (le_max_left _ _).trans hX
  have hX120 : (2 : ℝ) ^ 120 ≤ X :=
    (le_max_left _ _).trans hprefix
  have hXpos : 0 < X := by positivity
  have hlogThreshold :
      Real.exp (prefixTwistLogThreshold a eta) ≤ X :=
    (le_max_right _ _).trans hprefix
  have hlog : prefixTwistLogThreshold a eta ≤ Real.log X := by
    have hle : Real.exp (prefixTwistLogThreshold a eta) ≤ Real.exp (Real.log X) := by
      simpa [Real.exp_log hXpos] using hlogThreshold
    exact Real.exp_le_exp.mp hle
  have hlog2 : 2 ≤ Real.log X :=
    (le_max_left _ _).trans hlog
  have hgrowthThreshold :
      Real.exp ((2 / (1 / 8 + eta)) *
        Real.log (logAbsorptionM (1 / 8 + eta) (22 * a))) ≤ X :=
    (le_max_right _ _).trans hX
  have hgrowthLog :
      (2 / (1 / 8 + eta)) *
        Real.log (logAbsorptionM (1 / 8 + eta) (22 * a)) ≤ Real.log X := by
    have hle :
        Real.exp ((2 / (1 / 8 + eta)) *
          Real.log (logAbsorptionM (1 / 8 + eta) (22 * a))) ≤
        Real.exp (Real.log X) := by
      simpa [Real.exp_log hXpos] using hgrowthThreshold
    exact Real.exp_le_exp.mp hle
  have hgrowth := log_absorption_bound
    (a := 1 / 8 + eta) (b := 22 * a) (K := 1) (X := X)
    (by positivity) (by positivity) (by norm_num) (by linarith [hX120])
    (by simpa [one_mul] using hgrowthLog)
  have hgrowth' : (Real.log X) ^ (22 * a) ≤ X ^ (1 / 8 + eta) := by
    simpa [one_mul] using hgrowth
  exact ⟨hlog2, hX120, hgrowth'⟩

private theorem selectedMobiusPTWTransferW_sq
    {X a : ℝ} (hlog : 0 ≤ Real.log X) :
    selectedMobiusPTWTransferW X a ^ 2 = (Real.log X) ^ (20 * a) := by
  rw [selectedMobiusPTWTransferW,
    (Real.rpow_mul_natCast hlog (10 * a) 2).symm]
  congr 1
  ring

/-- A bound for the source symmetric integral, uniform over the precise
full-frequency window, bounds its attained envelope with no extra dyadic
loss. -/
theorem selectedMobiusPTWEnvelope_le_of_uniformIccIntegral
    (d : FullFrequencyMellinData) {T0 W B : ℝ}
    (hT0 : 0 < T0) (hW : 2 ≤ W) (hB : 0 ≤ B)
    (hIntegral : ∀ U ∈ Set.Icc T0 (T0 * W ^ 4),
      (∫ t in Set.Icc (-U) U,
        ‖fullFrequencyMellinPolynomial d t‖ ∂volume) ≤ B) :
    fullFrequencyEnvelope d T0 W ≤ B := by
  obtain ⟨U, hU, hEq, _hmax⟩ :=
    fullFrequencyEnvelope_hasMaximum d hT0 hW
  have hUpos : 0 < U := lt_of_lt_of_le hT0 hU.1
  have hratio0 : 0 ≤ T0 / U := div_nonneg hT0.le hUpos.le
  have hratio1 : T0 / U ≤ 1 :=
    (div_le_iff₀ hUpos).2 (by simpa using hU.1)
  have hset : {t : ℝ | |t| ≤ U} = Set.Icc (-U) U := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    exact abs_le
  have hI : fullFrequencyAbsoluteIntegral d U ≤ B := by
    unfold fullFrequencyAbsoluteIntegral
    rw [hset]
    exact hIntegral U hU
  rw [← hEq]
  change (T0 / U) * fullFrequencyAbsoluteIntegral d U ≤ B
  calc
    (T0 / U) * fullFrequencyAbsoluteIntegral d U ≤ (T0 / U) * B :=
      mul_le_mul_of_nonneg_left hI hratio0
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hratio1 hB
    _ = B := one_mul B

/-- Apply the exact source absolute-transfer theorem to full-frequency data,
then the source logarithmic budget. The sole integral premise is the uniform
full-frequency bound supplied by the preceding selected-group source
assembly; `K₀` and `C₁` are retained unchanged, including their divisor and
allocation costs. -/
theorem selectedMobiusPTWAbsoluteTransfer_of_uniformSourceIntegral
    (d : FullFrequencyMellinData)
    {a eta H K₀ C₁ : ℝ}
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta : 0 < eta)
    (hX : selectedMobiusPTWTransferGrowthThreshold a eta ≤ d.X)
    (hHlarge : d.X ^ (5 / 8 + eta) ≤ H)
    (hprefix : H * (Real.log d.X) ^ (-2 * a) ≤ d.H)
    (hh0 : d.h0 = selectedComponentH0 d.X)
    (hK : d.K ≤ K₀ * (Real.log d.X) ^
      (selectedMobiusPTWComponentExponent : ℝ))
    (hK₀ : 0 ≤ K₀) (hC₁ : 0 ≤ C₁)
    (hIntegral : ∀ U ∈ Set.Icc (d.X / d.H)
        ((d.X / d.H) * selectedMobiusPTWTransferW d.X a ^ 4),
      (∫ t in Set.Icc (-U) U,
        ‖fullFrequencyMellinPolynomial d t‖ ∂volume) ≤
        C₁ * Real.sqrt d.X * (Real.log d.X) ^
          selectedMobiusPTWSourceIntegralExponent a) :
    ‖fullFrequencyMellinMean d‖ ≤
      selectedMobiusPTWLongPrefixConstant a
        FractionalPrimes.polynomialKernelM1 K₀ C₁ *
          (Real.log d.X) ^ (-a) := by
  have hgrowth := selectedMobiusPTWTransferGrowth_of_threshold ha heta hX
  have hlog2 : 2 ≤ Real.log d.X := hgrowth.1
  have hX120 : (2 : ℝ) ^ 120 ≤ d.X := hgrowth.2.1
  have hXpos : 0 < d.X := by linarith [d.X_lower]
  have hlogpos : 0 < Real.log d.X := by linarith
  have hlogone : 1 ≤ Real.log d.X := by linarith
  have ha2 : 2 ≤ a := by
    have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
    have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
    exact h2.trans ha
  let L : ℝ := Real.log d.X
  let W : ℝ := selectedMobiusPTWTransferW d.X a
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hLnonneg : 0 ≤ L := by linarith [hL]
  have hWsq : W ^ 2 = L ^ (20 * a) := by
    dsimp [W, L]
    exact selectedMobiusPTWTransferW_sq (X := d.X) (a := a) hlogpos.le
  have hWge2 : 2 ≤ W := by
    have hexp : 2 ≤ 10 * a := by nlinarith
    have hpow : L ^ (2 : ℝ) ≤ L ^ (10 * a) :=
      Real.rpow_le_rpow_of_exponent_le hL hexp
    have hLsq : 4 ≤ L ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      nlinarith [sq_nonneg (L - 2)]
    have hLtoW : (4 : ℝ) ≤ (Real.log d.X) ^ (10 * a) := by
      dsimp [L] at hpow hLsq ⊢
      exact hLsq.trans hpow
    change 2 ≤ (Real.log d.X) ^ (10 * a)
    linarith
  have hWpos : 0 < W := lt_of_lt_of_le (by norm_num) hWge2
  have hH0le : d.h0 ≤ Real.sqrt d.X := by
    rw [hh0]
    exact selectedComponentH0_le_sqrt hX120
  have hgrowthPower : L ^ (22 * a) ≤ d.X ^ (1 / 8 + eta) := by
    simpa [L] using hgrowth.2.2
  have hprefixScale :
      Real.sqrt d.X * L ^ (20 * a) ≤
        d.X ^ (5 / 8 + eta) * L ^ (-2 * a) := by
    have hfactorNonneg : 0 ≤ Real.sqrt d.X * L ^ (-2 * a) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hgrowthPower hfactorNonneg
    have hsqrtPow : Real.sqrt d.X * d.X ^ (1 / 8 + eta) =
        d.X ^ (5 / 8 + eta) := by
      calc
        Real.sqrt d.X * d.X ^ (1 / 8 + eta) =
            d.X ^ (1 / 2 : ℝ) * d.X ^ (1 / 8 + eta) := by
              rw [Real.sqrt_eq_rpow]
        _ = d.X ^ ((1 / 2 : ℝ) + (1 / 8 + eta)) :=
          (Real.rpow_add (by linarith [d.X_lower] : 0 < d.X) _ _).symm
        _ = d.X ^ (5 / 8 + eta) := by congr 1 <;> ring
    have hlogPow : L ^ (-2 * a) * L ^ (22 * a) = L ^ (20 * a) := by
      calc
        L ^ (-2 * a) * L ^ (22 * a) = L ^ ((-2 * a) + (22 * a)) :=
          (Real.rpow_add hLpos _ _).symm
        _ = L ^ (20 * a) := by congr 1 <;> ring
    calc
      Real.sqrt d.X * L ^ (20 * a) =
          (Real.sqrt d.X * L ^ (-2 * a)) * L ^ (22 * a) := by
            rw [← hlogPow]
            ring
      _ ≤ (Real.sqrt d.X * L ^ (-2 * a)) *
          d.X ^ (1 / 8 + eta) := hmul
      _ = (Real.sqrt d.X * d.X ^ (1 / 8 + eta)) * L ^ (-2 * a) := by ring
      _ = d.X ^ (5 / 8 + eta) * L ^ (-2 * a) := by rw [hsqrtPow]
  have hlength : d.h0 * W ^ 2 ≤ d.H := by
    rw [hWsq]
    calc
      d.h0 * L ^ (20 * a) ≤ Real.sqrt d.X * L ^ (20 * a) :=
        mul_le_mul_of_nonneg_right hH0le (Real.rpow_nonneg hLnonneg _)
      _ ≤ d.X ^ (5 / 8 + eta) * L ^ (-2 * a) := hprefixScale
      _ ≤ H * L ^ (-2 * a) :=
        mul_le_mul_of_nonneg_right hHlarge (Real.rpow_nonneg hLnonneg _)
      _ ≤ d.H := by simpa [L, mul_comm] using hprefix
  have hBnonneg :
      0 ≤ C₁ * Real.sqrt d.X * L ^
        selectedMobiusPTWSourceIntegralExponent a := by
    positivity
  have hEnvelope := selectedMobiusPTWEnvelope_le_of_uniformIccIntegral d
    (div_pos hXpos d.H_pos) hWge2 hBnonneg (by
      intro U hU
      exact hIntegral U (by simpa [W] using hU))
  have htransfer := absoluteShortIntervalTransfer d hWge2 hlength
  have hM1nonneg : 0 ≤ FractionalPrimes.polynomialKernelM1 := by
    unfold FractionalPrimes.polynomialKernelM1
    exact integral_nonneg fun u =>
      mul_nonneg (abs_nonneg u)
        (FractionalPrimes.polynomialKernelRho_nonneg u)
  have hWpow : W ^ 2 = L ^ (20 * a) := hWsq
  have hfirst : d.K / W ^ 2 ≤
      K₀ * L ^ ((selectedMobiusPTWComponentExponent : ℝ) - 20 * a) := by
    have hpow :
        L ^ ((selectedMobiusPTWComponentExponent : ℝ) - 20 * a) * W ^ 2 =
          L ^ (selectedMobiusPTWComponentExponent : ℝ) := by
      rw [hWpow]
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    apply (div_le_iff₀ (pow_pos hWpos 2)).2
    calc
      d.K ≤ K₀ * L ^ (selectedMobiusPTWComponentExponent : ℝ) := hK
      _ = (K₀ * L ^
            ((selectedMobiusPTWComponentExponent : ℝ) - 20 * a)) * W ^ 2 := by
            rw [← hpow]
            ring
  have hlogL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
  have h10log :
      10 * a * Real.log L ≤ 10 * a * (L - 1) :=
    mul_le_mul_of_nonneg_left hlogL (by positivity)
  have hlogW : 1 + Real.log W ≤ (1 + 10 * a) * L := by
    have hlogWeq : Real.log W = 10 * a * Real.log L := by
      dsimp [W, selectedMobiusPTWTransferW, L]
      rw [Real.log_rpow hlogpos]
    rw [hlogWeq]
    nlinarith
  have hpowAdd :
      L * L ^ selectedMobiusPTWSourceIntegralExponent a =
        L ^ (selectedMobiusPTWSourceIntegralExponent a + 1) := by
    calc
      L * L ^ selectedMobiusPTWSourceIntegralExponent a =
          L ^ (1 : ℝ) * L ^ selectedMobiusPTWSourceIntegralExponent a := by
            rw [Real.rpow_one]
      _ = L ^ (1 + selectedMobiusPTWSourceIntegralExponent a) :=
        (Real.rpow_add hLpos _ _).symm
      _ = _ := by congr 1 <;> ring
  have hsecond :
      (1 + Real.log W) / Real.sqrt d.X *
        fullFrequencyEnvelope d (d.X / d.H) W ≤
        (1 + 10 * a) * C₁ * L ^
          ((selectedMobiusPTWLogExponent : ℝ) + 4 -
            5 * a / 4 + a / 500) := by
    have hsqrt : 0 < Real.sqrt d.X := Real.sqrt_pos.2 hXpos
    have hlogWnonneg : 0 ≤ Real.log W :=
      Real.log_nonneg (by linarith [hWge2])
    have hratio0 : 0 ≤ (1 + Real.log W) / Real.sqrt d.X :=
      div_nonneg (by linarith) (Real.sqrt_nonneg d.X)
    have hratio :
        (1 + Real.log W) / Real.sqrt d.X ≤
          ((1 + 10 * a) * L) / Real.sqrt d.X :=
      div_le_div_of_nonneg_right hlogW (Real.sqrt_nonneg d.X)
    have hscaleNonneg : 0 ≤ C₁ * Real.sqrt d.X *
        L ^ selectedMobiusPTWSourceIntegralExponent a := by positivity
    calc
      _ ≤ ((1 + Real.log W) / Real.sqrt d.X) *
          (C₁ * Real.sqrt d.X *
            L ^ selectedMobiusPTWSourceIntegralExponent a) :=
        mul_le_mul_of_nonneg_left hEnvelope hratio0
      _ ≤ (((1 + 10 * a) * L) / Real.sqrt d.X) *
          (C₁ * Real.sqrt d.X *
            L ^ selectedMobiusPTWSourceIntegralExponent a) :=
        mul_le_mul_of_nonneg_right hratio hscaleNonneg
      _ = (1 + 10 * a) * C₁ *
          (L * L ^ selectedMobiusPTWSourceIntegralExponent a) := by
        field_simp [hsqrt.ne']
      _ = (1 + 10 * a) * C₁ *
          L ^ (selectedMobiusPTWSourceIntegralExponent a + 1) := by
        rw [hpowAdd]
      _ = (1 + 10 * a) * C₁ *
          L ^ ((selectedMobiusPTWLogExponent : ℝ) + 4 -
            5 * a / 4 + a / 500) := by
        congr 2
        dsimp [selectedMobiusPTWSourceIntegralExponent]
        ring
  have hterms : d.K / W ^ 2 +
      (1 + Real.log W) / Real.sqrt d.X *
        fullFrequencyEnvelope d (d.X / d.H) W ≤
        K₀ * L ^ ((selectedMobiusPTWComponentExponent : ℝ) - 20 * a) +
          (1 + 10 * a) * C₁ *
            L ^ ((selectedMobiusPTWLogExponent : ℝ) + 4 -
              5 * a / 4 + a / 500) :=
    add_le_add hfirst hsecond
  have hpref :
      0 ≤ (2 : ℝ) ^ 36 *
        (1 + FractionalPrimes.polynomialKernelM1) := by positivity
  have hmain := selectedMobiusPTW_longPrefixScalarBound
    ha hL hM1nonneg hK₀ hC₁
  calc
    ‖fullFrequencyMellinMean d‖ ≤
        (2 : ℝ) ^ 36 *
          (1 + FractionalPrimes.polynomialKernelM1) *
          (d.K / W ^ 2 +
            (1 + Real.log W) / Real.sqrt d.X *
              fullFrequencyEnvelope d (d.X / d.H) W) := by
      simpa [W, L] using htransfer
    _ ≤ (2 : ℝ) ^ 36 *
          (1 + FractionalPrimes.polynomialKernelM1) *
          (K₀ * L ^ ((selectedMobiusPTWComponentExponent : ℝ) - 20 * a) +
            (1 + 10 * a) * C₁ *
              L ^ ((selectedMobiusPTWLogExponent : ℝ) + 4 -
                5 * a / 4 + a / 500)) :=
      mul_le_mul_of_nonneg_left hterms hpref
    _ ≤ selectedMobiusPTWLongPrefixConstant a
          FractionalPrimes.polynomialKernelM1 K₀ C₁ * L ^ (-a) := hmain

#print axioms selectedMobiusPTWTransferGrowth_of_threshold
#print axioms selectedMobiusPTWEnvelope_le_of_uniformIccIntegral
#print axioms selectedMobiusPTWAbsoluteTransfer_of_uniformSourceIntegral

end FractionalPrimes.Literature.DirichletMean

end
