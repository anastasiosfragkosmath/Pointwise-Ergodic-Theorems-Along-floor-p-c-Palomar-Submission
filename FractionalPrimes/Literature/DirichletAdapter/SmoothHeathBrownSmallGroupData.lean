module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothGroupSubsetReindex
public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownConvolution
public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownRetention
public import FractionalPrimes.Literature.Uniformity.HeathBrownIdentity
public import FractionalPrimes.Literature.Twisted.ShiftedConvolutionFactorExtraction
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic

/-!
# Finite data for a selected smooth Heath--Brown group

This module instantiates the finite transfer's scale, support window, and
other-factor mass from the actual tagged smooth Heath--Brown factors.  The
selected factor's short-interval cancellation remains an explicit premise.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The finite source window `(N/2,2N]` for a tagged smooth factor. -/
noncomputable def smoothHeathBrownFactorFiniteSupport
    {X : ℝ} (f : SmoothHeathBrownFactor X) : Finset ℕ :=
  factorExtractionDyadicInterval (smoothHeathBrownFactorScale f / 2) ∪
    factorExtractionDyadicInterval (smoothHeathBrownFactorScale f)

/-- The actual smooth Heath--Brown factor coefficient, with the possible
logarithm divided by the source normalization `4 log X`. -/
noncomputable def smoothHeathBrownNormalizedFactorCoefficient
    {X z : ℝ} (f : SmoothHeathBrownFactor X) (n : ℕ) : ℝ :=
  match f with
  | .theta j => smoothHeathBrownThetaFactor j n
  | .logarithm j =>
      smoothHeathBrownLogFactor j n / (4 * Real.log X)
  | .mobius j => smoothHeathBrownMobiusFactor z j n

/-- The normalized coefficient is exactly the source factor function, with
the advertised scalar applied only to the logarithmic tag. -/
theorem smoothHeathBrownNormalizedFactorCoefficient_eq
    {X z : ℝ} (f : SmoothHeathBrownFactor X) (n : ℕ) :
    smoothHeathBrownNormalizedFactorCoefficient (z := z) f n =
      match f with
      | .theta _ => smoothHeathBrownFactorFunction z f n
      | .logarithm _ => smoothHeathBrownFactorFunction z f n /
          (4 * Real.log X)
      | .mobius _ => smoothHeathBrownFactorFunction z f n := by
  cases f <;> rfl

private theorem smoothHeathBrownScaleIndex_scale_le_eightX
    {X : ℝ} (hX : 3 ≤ X) (j : SmoothHeathBrownScaleIndex X) :
    (2 : ℝ) ^ j.val ≤ 8 * X := by
  have hXpos : 0 < X := by linarith
  have harg : 1 ≤ 4 * X := by nlinarith
  have hlogbnonneg : 0 ≤ Real.logb 2 (4 * X) := by
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg harg) (Real.log_pos (by norm_num)).le
  have hceil :
      (smoothHeathBrownDepth X : ℝ) < Real.logb 2 (4 * X) + 1 := by
    dsimp [smoothHeathBrownDepth]
    exact Nat.ceil_lt_add_one hlogbnonneg
  have hjNat : j.val ≤ smoothHeathBrownDepth X := by omega
  have hjReal :
      (j.val : ℝ) < Real.logb 2 (4 * X) + 1 := by
    exact lt_of_le_of_lt (by exact_mod_cast hjNat) hceil
  have hlog8 : Real.logb 2 (8 * X) = Real.logb 2 (4 * X) + 1 := by
    rw [show 8 * X = (2 : ℝ) * (4 * X) by ring,
      Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by positivity : (4 * X) ≠ 0)]
    rw [Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))]
    ring
  have hjLog : (j.val : ℝ) < Real.logb 2 (8 * X) := by
    rw [hlog8]
    exact hjReal
  have hpow : (2 : ℝ) ^ (j.val : ℝ) < 8 * X :=
    (Real.lt_logb_iff_rpow_lt (by norm_num : 1 < (2 : ℝ))
      (by positivity : 0 < 8 * X)).mp hjLog
  exact le_of_lt (by simpa only [Real.rpow_natCast] using hpow)

theorem smoothHeathBrownFactorScale_le_eightX
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X) :
    smoothHeathBrownFactorScale f ≤ 8 * X := by
  cases f with
  | theta j => exact smoothHeathBrownScaleIndex_scale_le_eightX hX j
  | logarithm j => exact smoothHeathBrownScaleIndex_scale_le_eightX hX j
  | mobius j => exact smoothHeathBrownScaleIndex_scale_le_eightX hX j

/-- The union of the two exact dyadic intervals is the inverse-square-root
mass window used for one smooth factor. -/
theorem smoothHeathBrownFactorFiniteSupport_eq_massWindow
    {X : ℝ} (f : SmoothHeathBrownFactor X) :
    smoothHeathBrownFactorFiniteSupport f =
      smoothFactorMassWindow (smoothHeathBrownFactorScale f) := by
  have hN := smoothHeathBrownFactorScale_ge_one f
  have hNnonneg : 0 ≤ smoothHeathBrownFactorScale f := by linarith
  ext n
  rw [smoothHeathBrownFactorFiniteSupport, Finset.mem_union,
    mem_factorExtractionDyadicInterval (by positivity),
    mem_factorExtractionDyadicInterval (by positivity),
    mem_smoothFactorMassWindow hNnonneg]
  constructor
  · rintro (⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
    · refine ⟨hlo, ?_⟩
      rw [show 2 * (smoothHeathBrownFactorScale f / 2) =
        smoothHeathBrownFactorScale f by ring] at hhi
      nlinarith [hNnonneg]
    · exact ⟨lt_trans (by linarith :
        smoothHeathBrownFactorScale f / 2 < smoothHeathBrownFactorScale f) hlo,
        hhi⟩
  · rintro ⟨hlo, hhi⟩
    by_cases hle : (n : ℝ) ≤ smoothHeathBrownFactorScale f
    · left
      refine ⟨hlo, ?_⟩
      rw [show 2 * (smoothHeathBrownFactorScale f / 2) =
        smoothHeathBrownFactorScale f by ring]
      exact hle
    · right
      exact ⟨lt_of_not_ge hle, hhi⟩

/-- Every nonzero normalized smooth factor coefficient lies in its exact
dyadic source window. -/
theorem smoothHeathBrownNormalizedFactorCoefficient_support
    {X z : ℝ} (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hne : smoothHeathBrownNormalizedFactorCoefficient (z := z) f n ≠ 0) :
    n ∈ smoothHeathBrownFactorFiniteSupport f := by
  have hNpos : 0 < smoothHeathBrownFactorScale f := by
    have h := smoothHeathBrownFactorScale_ge_one f
    linarith
  have htheta :
      smoothDyadicTheta ((n : ℝ) / smoothHeathBrownFactorScale f) ≠ 0 := by
    cases f with
    | theta j =>
        intro hz
        change smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) = 0 at hz
        apply hne
        have hn0 : n ≠ 0 := by
          intro hz0
          subst n
          simp [smoothHeathBrownNormalizedFactorCoefficient,
            smoothHeathBrownThetaFactor] at hne
        simp [smoothHeathBrownNormalizedFactorCoefficient,
          smoothHeathBrownThetaFactor, hn0, hz]
    | logarithm j =>
        intro hz
        change smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) = 0 at hz
        apply hne
        have hn0 : n ≠ 0 := by
          intro hz0
          subst n
          simp [smoothHeathBrownNormalizedFactorCoefficient,
            smoothHeathBrownLogFactor] at hne
        simp [smoothHeathBrownNormalizedFactorCoefficient,
          smoothHeathBrownLogFactor, hn0, hz]
    | mobius j =>
        intro hz
        change smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) = 0 at hz
        apply hne
        have hn0 : n ≠ 0 := by
          intro hz0
          subst n
          simp [smoothHeathBrownNormalizedFactorCoefficient,
            smoothHeathBrownMobiusFactor] at hne
        simp [smoothHeathBrownNormalizedFactorCoefficient,
          smoothHeathBrownMobiusFactor, hn0, hz]
  have hlo : (1 / 2 : ℝ) <
      (n : ℝ) / smoothHeathBrownFactorScale f := by
    by_contra h
    exact htheta (smoothDyadicTheta_eq_zero_of_le_half (le_of_not_gt h))
  have hhi : (n : ℝ) / smoothHeathBrownFactorScale f < 2 := by
    by_contra h
    exact htheta (smoothDyadicTheta_eq_zero_of_two_le (le_of_not_gt h))
  have hwindow : smoothHeathBrownFactorScale f / 2 < (n : ℝ) ∧
      (n : ℝ) < 2 * smoothHeathBrownFactorScale f := by
    constructor
    · have hmul := mul_lt_mul_of_pos_right hlo hNpos
      have hcancel :
          ((n : ℝ) / smoothHeathBrownFactorScale f) *
              smoothHeathBrownFactorScale f = (n : ℝ) :=
        div_mul_cancel₀ _ hNpos.ne'
      nlinarith [hmul, hcancel]
    · exact (div_lt_iff₀ hNpos).mp hhi
  rw [smoothHeathBrownFactorFiniteSupport, Finset.mem_union,
    mem_factorExtractionDyadicInterval (by positivity),
    mem_factorExtractionDyadicInterval (by positivity)]
  by_cases hnle : (n : ℝ) ≤ smoothHeathBrownFactorScale f
  · left
    exact ⟨hwindow.1, by nlinarith⟩
  · right
    exact ⟨lt_of_not_ge hnle, le_of_lt hwindow.2⟩

private theorem smoothHeathBrown_log_sixteenX_le_four_logX
    {X : ℝ} (hX : 3 ≤ X) : Real.log (16 * X) ≤ 4 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hXcube : (16 : ℝ) ≤ X ^ 3 := by
    calc
      16 ≤ 3 ^ 3 := by norm_num
      _ ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
  have harg : 16 * X ≤ X ^ 4 := by
    calc
      16 * X ≤ X ^ 3 * X := mul_le_mul_of_nonneg_right hXcube hXpos.le
      _ = X ^ 4 := by ring
  have hlog := Real.log_le_log (by positivity : 0 < 16 * X) harg
  have hlogpow : Real.log (X ^ 4) = 4 * Real.log X := by
    rw [Real.log_pow X 4]
    norm_num
  rw [hlogpow] at hlog
  exact hlog

/-- The source normalized coefficient has modulus at most one throughout its
finite support window. The logarithmic tag uses the exact 4 log X
normalization from the smooth Heath--Brown decomposition. -/
theorem smoothHeathBrownNormalizedFactorCoefficient_abs_le_one
    {X z : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hn : n ∈ smoothHeathBrownFactorFiniteSupport f) :
    |smoothHeathBrownNormalizedFactorCoefficient (z := z) f n| ≤ 1 := by
  have hN := smoothHeathBrownFactorScale_ge_one f
  have hwindow := (mem_smoothFactorMassWindow (by linarith :
    0 ≤ smoothHeathBrownFactorScale f) n).mp
      (by rw [← smoothHeathBrownFactorFiniteSupport_eq_massWindow]; exact hn)
  have hnpos : 0 < n := by
    have hreal : 0 < (n : ℝ) :=
      lt_trans (by positivity : 0 < smoothHeathBrownFactorScale f / 2)
        hwindow.1
    exact_mod_cast hreal
  have hthetaNonneg := smoothDyadicTheta_nonneg
    ((n : ℝ) / smoothHeathBrownFactorScale f)
  have hthetaLe := smoothDyadicTheta_le_one
    ((n : ℝ) / smoothHeathBrownFactorScale f)
  cases f with
  | theta j =>
      have hthetaNonneg' :
          0 ≤ smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) := by
        simpa [smoothHeathBrownFactorScale] using hthetaNonneg
      have hthetaLe' :
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≤ 1 := by
        simpa [smoothHeathBrownFactorScale] using hthetaLe
      simpa [smoothHeathBrownNormalizedFactorCoefficient,
        smoothHeathBrownThetaFactor, hnpos.ne'] using
          (calc
            |smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)| =
                smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) :=
                  abs_of_nonneg hthetaNonneg'
            _ ≤ 1 := hthetaLe')
  | mobius j =>
      have hthetaNonneg' :
          0 ≤ smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) := by
        simpa [smoothHeathBrownFactorScale] using hthetaNonneg
      have hthetaLe' :
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≤ 1 := by
        simpa [smoothHeathBrownFactorScale] using hthetaLe
      have hmu : |truncatedMobius z n| ≤ 1 := by
        by_cases hcut : (n : ℝ) ≤ z
        · rw [truncatedMobius_apply_of_le hcut]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
        · rw [truncatedMobius_apply_of_not_le hcut]
          simp
      have hmul :
          |truncatedMobius z n *
              smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hthetaNonneg']
        calc
          |truncatedMobius z n| *
              smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≤
              1 * 1 :=
            mul_le_mul hmu hthetaLe' hthetaNonneg' (by norm_num)
          _ = 1 := by ring
      simpa [smoothHeathBrownNormalizedFactorCoefficient,
        smoothHeathBrownMobiusFactor, hnpos.ne'] using hmul
  | logarithm j =>
      have hXpos : 0 < X := by linarith
      have hscale :
          smoothHeathBrownFactorScale (SmoothHeathBrownFactor.logarithm j) ≤
            8 * X :=
        smoothHeathBrownFactorScale_le_eightX hX (.logarithm j)
      have hnUpper : (n : ℝ) ≤ 16 * X := by
        calc
          (n : ℝ) ≤
              2 * smoothHeathBrownFactorScale (.logarithm j) := hwindow.2
          _ ≤ 2 * (8 * X) := by nlinarith [hscale]
          _ = 16 * X := by ring
      have hlogUpper : Real.log (n : ℝ) ≤ 4 * Real.log X := by
        exact (Real.log_le_log (by exact_mod_cast hnpos) hnUpper).trans
          (smoothHeathBrown_log_sixteenX_le_four_logX hX)
      have hlogNonneg : 0 ≤ Real.log (n : ℝ) :=
        Real.log_natCast_nonneg n
      have hdenom : 0 < 4 * Real.log X := by
        have hlogX : 0 < Real.log X := Real.log_pos (by linarith : 1 < X)
        positivity
      have hthetaNonneg' :
          0 ≤ smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) := by
        simpa [smoothHeathBrownFactorScale] using hthetaNonneg
      have hthetaLe' :
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≤ 1 := by
        simpa [smoothHeathBrownFactorScale] using hthetaLe
      have hcoeffNonneg : 0 ≤ Real.log (n : ℝ) *
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) :=
        mul_nonneg hlogNonneg hthetaNonneg'
      have hcoeffLe : Real.log (n : ℝ) *
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≤ 4 * Real.log X := by
        calc
          Real.log (n : ℝ) *
              smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≤
              Real.log (n : ℝ) :=
            mul_le_of_le_one_right hlogNonneg hthetaLe'
          _ ≤ 4 * Real.log X := hlogUpper
      have hratio : 0 ≤
          (Real.log (n : ℝ) *
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) /
              (4 * Real.log X) ∧
          (Real.log (n : ℝ) *
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) /
              (4 * Real.log X) ≤ 1 := by
        constructor
        · exact div_nonneg hcoeffNonneg hdenom.le
        · exact (div_le_one hdenom).2 hcoeffLe
      simpa [smoothHeathBrownNormalizedFactorCoefficient,
        smoothHeathBrownLogFactor, hnpos.ne', ArithmeticFunction.log_apply]
        using abs_le.mpr ⟨by linarith [hratio.1], hratio.2⟩

/-- The inverse-square-root normalized coefficient attached to an actual
smooth Heath--Brown factor and an auxiliary bounded complex weight. -/
noncomputable def smoothHeathBrownWeightedFactorCoefficient
    {X z : ℝ} (f : SmoothHeathBrownFactor X) (ω : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Complex.ofReal
      (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n) * ω n) /
    (Real.sqrt (n : ℝ) : ℂ)

/-- A normalized smooth Heath--Brown factor has absolute weighted mass at
most five times the square root of its source scale. The only added
coefficient input is the pointwise unit bound on the auxiliary weight. -/
theorem smoothHeathBrownWeightedFactorMass
    {X z : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (ω : ℕ → ℂ)
    (hω : ∀ n ∈ smoothHeathBrownFactorFiniteSupport f, ‖ω n‖ ≤ 1) :
    (∑ n ∈ smoothHeathBrownFactorFiniteSupport f,
      ‖smoothHeathBrownWeightedFactorCoefficient (z := z) f ω n‖) ≤
      5 * Real.sqrt (smoothHeathBrownFactorScale f) := by
  let g : ℕ → ℂ := fun n =>
    Complex.ofReal (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n) *
      ω n
  have hN : 1 ≤ smoothHeathBrownFactorScale f :=
    smoothHeathBrownFactorScale_ge_one f
  have hg : ∀ n ∈ smoothFactorMassWindow (smoothHeathBrownFactorScale f),
      ‖g n‖ ≤ 1 := by
    intro n hn
    have hmem : n ∈ smoothHeathBrownFactorFiniteSupport f := by
      rw [smoothHeathBrownFactorFiniteSupport_eq_massWindow]
      exact hn
    have hcoef :=
      smoothHeathBrownNormalizedFactorCoefficient_abs_le_one
        (z := z) hX f hmem
    have hweight := hω n hmem
    dsimp [g]
    rw [norm_mul, Complex.norm_real]
    calc
      |smoothHeathBrownNormalizedFactorCoefficient (z := z) f n| *
          ‖ω n‖ ≤ 1 * 1 :=
        mul_le_mul hcoef hweight (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hmass := smoothFactorInverseSqrtMass hN g hg
  rw [← smoothHeathBrownFactorFiniteSupport_eq_massWindow] at hmass
  calc
    (∑ n ∈ smoothHeathBrownFactorFiniteSupport f,
      ‖smoothHeathBrownWeightedFactorCoefficient (z := z) f ω n‖) =
      ∑ n ∈ smoothHeathBrownFactorFiniteSupport f,
        ‖g n‖ / Real.sqrt (n : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [smoothHeathBrownWeightedFactorCoefficient, show
            (Complex.ofReal
                (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n) *
                ω n) = g n by rfl, norm_div]
          have hroot : ‖(Real.sqrt (n : ℝ) : ℂ)‖ = Real.sqrt (n : ℝ) := by
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
          rw [hroot]
    _ ≤ 5 * Real.sqrt (smoothHeathBrownFactorScale f) := by
      simpa [g] using hmass

/-- The subset-indexed finite transfer with the actual normalized smooth
Heath--Brown factors as coefficients. All complementary-factor mass and
support hypotheses are discharged from their source definitions; the
selected factor's short-interval cancellation remains the explicit input
hShort. -/
theorem smoothHeathBrownSubsetWideSupportFiniteTransfer
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fs.length)) (selected : Fin fs.length)
    (hselected : selected ∈ I) (hcount : I.card ≤ 20) (h : ℤ)
    (L ε x y : ℝ) (ω : Fin fs.length → ℕ → ℂ)
    (hL : L = (2 : ℝ) ^ h *
      (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)))
    (hh : -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ))
    (hε : 0 ≤ ε) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hω : ∀ i n, ‖ω i n‖ ≤ 1)
    (hShort : ∀ M : ℝ,
      (M = smoothHeathBrownFactorScale (fs.get selected) / 2 ∨
        M = smoothHeathBrownFactorScale (fs.get selected)) →
      ∀ u v : ℝ, 0 ≤ u →
        Set.Ioc u v ⊆ Set.Ioc M (2 * M) →
        ‖∑ n ∈
            FractionalPrimes.Literature.Twisted.factorExtractionRealInterval
              u v,
            smoothHeathBrownWeightedFactorCoefficient (z := z)
              (fs.get selected) (ω selected) n‖ ≤ ε * Real.sqrt M) :
    ‖smoothGroupSubsetConvolutionSum I
        (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
        (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
          (fs.get i) (ω i) n) x y‖ ≤
      (2 : ℝ) ^ 11 * 5 ^ 19 * ε * Real.sqrt L := by
  let N : Fin fs.length → ℝ :=
    fun i => smoothHeathBrownFactorScale (fs.get i)
  let S : Fin fs.length → Finset ℕ :=
    fun i => smoothHeathBrownFactorFiniteSupport (fs.get i)
  let a : Fin fs.length → ℕ → ℂ :=
    fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
      (fs.get i) (ω i) n
  have hN : ∀ i ∈ I, 0 < N i := by
    intro i hi
    dsimp [N]
    have hscale := smoothHeathBrownFactorScale_ge_one (fs.get i)
    exact lt_of_lt_of_le (by norm_num : 0 < (1 : ℝ)) hscale
  have hL' : L = (2 : ℝ) ^ h * (∏ i ∈ I, N i) := by
    simpa [N] using hL
  have hSelected : S selected =
      FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
          (N selected / 2) ∪
        FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
          (N selected) := by
    simp [S, N, smoothHeathBrownFactorFiniteSupport]
  have hPositive : ∀ i ∈ I, ∀ n, n ∈ S i → 0 < n := by
    intro i hi n hn
    have hNnonneg : 0 ≤ N i := (hN i hi).le
    have hmem : n ∈ smoothFactorMassWindow (N i) := by
      rw [← smoothHeathBrownFactorFiniteSupport_eq_massWindow]
      exact hn
    have hwindow := (mem_smoothFactorMassWindow hNnonneg n).mp hmem
    have hhalf : 0 < N i / 2 := div_pos (hN i hi) (by norm_num)
    have hreal : 0 < (n : ℝ) := lt_trans hhalf hwindow.1
    exact_mod_cast hreal
  have hOtherMass : ∀ i ∈ I.erase selected,
      (∑ n ∈ S i, ‖a i n‖) ≤ 5 * Real.sqrt (N i) := by
    intro i hi
    have hweight : ∀ n ∈ S i, ‖ω i n‖ ≤ 1 := by
      intro n hn
      exact hω i n
    simpa [N, S, a] using
      (smoothHeathBrownWeightedFactorMass hX (fs.get i) (ω i) hweight)
  have hShort' : ∀ M : ℝ,
      (M = N selected / 2 ∨ M = N selected) →
      ∀ u v : ℝ, 0 ≤ u →
        Set.Ioc u v ⊆ Set.Ioc M (2 * M) →
        ‖∑ n ∈
            FractionalPrimes.Literature.Twisted.factorExtractionRealInterval
              u v, a selected n‖ ≤ ε * Real.sqrt M := by
    intro M hM u v hu hI
    have hM' :
        M = smoothHeathBrownFactorScale (fs.get selected) / 2 ∨
          M = smoothHeathBrownFactorScale (fs.get selected) := by
      simpa [N] using hM
    simpa [a] using hShort M hM' u v hu hI
  exact smoothGroupSubsetWideSupportFiniteTransfer
    I selected hselected hcount h N L ε x y S a hN hL' hh hε hx hxy
    hSelected hPositive hOtherMass hShort'

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownNormalizedFactorCoefficient_abs_le_one
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownWeightedFactorMass
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownSubsetWideSupportFiniteTransfer
