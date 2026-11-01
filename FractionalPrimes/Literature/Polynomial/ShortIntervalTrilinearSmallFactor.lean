module

public import FractionalPrimes.Literature.Polynomial.DirichletMeanConstants
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The small-factor contribution in the proof of `ldm:trilinear`.
The factor-and-square level theorem is kept as its exact mean-square
component, so this file does not duplicate the worker-owned `ldm:power-levels`
proof.

Blueprint: `expanded-blueprint.tex:5862-5934`.
Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-mean-closure.tex:222-247`.
-/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.DirichletMean

noncomputable section

private lemma maxPairExponentBound
    (t u v : ℝ)
    (ht : t ≤ 3 / 8)
    (hu : u ≤ 1 / 2 + 3 / 1600)
    (hv : v ≤ 1 / 2 + 3 / 1600)
    (huv : u + v ≤ 7 / 8 + 3 / 1600) :
    max t u + max t v ≤ 15 / 16 := by
  by_cases htu : t ≤ u
  · by_cases htv : t ≤ v
    · rw [max_eq_right htu, max_eq_right htv]
      linarith
    · have hvt : v ≤ t := (lt_of_not_ge htv).le
      rw [max_eq_right htu, max_eq_left hvt]
      linarith
  · have hut : u ≤ t := (lt_of_not_ge htu).le
    by_cases htv : t ≤ v
    · rw [max_eq_left hut, max_eq_right htv]
      linarith
    · have hvt : v ≤ t := (lt_of_not_ge htv).le
      rw [max_eq_left hut, max_eq_left hvt]
      linarith

/-- The source length hypotheses imply the pairwise exponent bound used on
the part where one factor has modulus at most one. -/
theorem trilinearPairExponentBounds
    (ε a b c : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 3 / 16)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hsum : a + b + c = 1)
    (haLower : 1 / 4 - ε / 100 ≤ a)
    (haUpper : a ≤ 1 / 2 + ε / 100)
    (hdiff : |b - c| ≤ 1 / 4 + ε / 100) :
    let t := 3 / 8 - ε
    max t a + max t b ≤ 15 / 16 ∧
      max t a + max t c ≤ 15 / 16 ∧
      max t b + max t c ≤ 15 / 16 := by
  dsimp
  have heps : ε / 100 ≤ 3 / 1600 := by nlinarith
  have hbc : b + c = 1 - a := by linarith
  have hba : 1 / 8 - 3 / 1600 ≤ b := by
    have hdifflo : -(1 / 4 + ε / 100) ≤ b - c := (abs_le.mp hdiff).1
    linarith
  have hca : 1 / 8 - 3 / 1600 ≤ c := by
    have hdiffhi : b - c ≤ 1 / 4 + ε / 100 := (abs_le.mp hdiff).2
    linarith
  have haa : 1 / 8 - 3 / 1600 ≤ a := by linarith
  have habove : a ≤ 1 / 2 + 3 / 1600 := by linarith
  have hbUpper : b ≤ 1 / 2 + 3 / 1600 := by
    have hdiffhi : b - c ≤ 1 / 4 + ε / 100 := (abs_le.mp hdiff).2
    linarith
  have hcUpper : c ≤ 1 / 2 + 3 / 1600 := by
    have hdifflo : -(1 / 4 + ε / 100) ≤ b - c := (abs_le.mp hdiff).1
    linarith
  have hpab : a + b ≤ 7 / 8 + 3 / 1600 := by linarith
  have hpac : a + c ≤ 7 / 8 + 3 / 1600 := by linarith
  have hpbc : b + c ≤ 7 / 8 + 3 / 1600 := by linarith
  have ht : 3 / 8 - ε ≤ 3 / 8 := by linarith
  exact ⟨maxPairExponentBound _ _ _ ht habove hbUpper hpab,
    maxPairExponentBound _ _ _ ht habove hcUpper hpac,
    maxPairExponentBound _ _ _ ht hbUpper hcUpper hpbc⟩

private lemma pairLengthGrowthBound
    (X T ε v w : ℝ)
    (hX : 1 ≤ X) (hT : 0 ≤ T) (hε0 : 0 ≤ ε)
    (hTupper : T ≤ X ^ (3 / 8 - ε))
    (hv : v ≤ 1 / 2 + 3 / 1600)
    (hw : w ≤ 1 / 2 + 3 / 1600)
    (hvw : v + w ≤ 7 / 8 + 3 / 1600) :
    Real.sqrt ((T + X ^ v) * (T + X ^ w)) ≤ 2 * X ^ ((15 : ℝ) / 32) := by
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  let t := 3 / 8 - ε
  have ht : t ≤ 3 / 8 := by dsimp [t]; linarith
  have hmax : max t v + max t w ≤ 15 / 16 :=
    maxPairExponentBound t v w ht hv hw hvw
  have hpowV : X ^ v ≤ X ^ (max t v) :=
    Real.rpow_le_rpow_of_exponent_le hX (le_max_right t v)
  have hpowW : X ^ w ≤ X ^ (max t w) :=
    Real.rpow_le_rpow_of_exponent_le hX (le_max_right t w)
  have hpowT_V : X ^ t ≤ X ^ (max t v) :=
    Real.rpow_le_rpow_of_exponent_le hX (le_max_left t v)
  have hpowT_W : X ^ t ≤ X ^ (max t w) :=
    Real.rpow_le_rpow_of_exponent_le hX (le_max_left t w)
  have hsumV : T + X ^ v ≤ 2 * X ^ (max t v) := by
    dsimp [t] at hTupper ⊢
    nlinarith [hTupper, hpowV, hpowT_V]
  have hsumW : T + X ^ w ≤ 2 * X ^ (max t w) := by
    dsimp [t] at hTupper ⊢
    nlinarith [hTupper, hpowW, hpowT_W]
  have hprod : (T + X ^ v) * (T + X ^ w) ≤
      (2 * X ^ (max t v)) * (2 * X ^ (max t w)) :=
    mul_le_mul hsumV hsumW (by positivity) (by positivity)
  have hExp : (max t v + max t w) / 2 ≤ 15 / 32 := by linarith
  have hroot : Real.sqrt ((2 * X ^ (max t v)) * (2 * X ^ (max t w))) =
      2 * X ^ ((max t v + max t w) / 2) := by
    have hpower : X ^ (max t v) * X ^ (max t w) =
        X ^ (max t v + max t w) := by
      rw [Real.rpow_add hXpos]
    have hrewrite :
        (2 * X ^ (max t v)) * (2 * X ^ (max t w)) =
          4 * X ^ (max t v + max t w) := by
      rw [show (2 * X ^ (max t v)) * (2 * X ^ (max t w)) =
          4 * (X ^ (max t v) * X ^ (max t w)) by ring, hpower]
    rw [hrewrite, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)
      nlinarith [Real.sqrt_nonneg (4 : ℝ)]
    rw [hsqrt4, Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]
    rw [show (max t v + max t w) * (1 / (2 : ℝ)) =
      (max t v + max t w) / 2 by ring]
  calc
    Real.sqrt ((T + X ^ v) * (T + X ^ w)) ≤
        Real.sqrt ((2 * X ^ (max t v)) * (2 * X ^ (max t w))) :=
      Real.sqrt_le_sqrt hprod
    _ = 2 * X ^ ((max t v + max t w) / 2) := hroot
    _ ≤ 2 * X ^ ((15 : ℝ) / 32) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX hExp) (by norm_num)

/-- On a measurable part of the short interval where one factor is at most
one, Cauchy--Schwarz and the exact mean-square components of
`ldm:power-levels` give the source `2 K_C L_X^{b_C} X^{15/32}` bound.
The two mean-square estimates are explicit premises so this checkpoint stays
disjoint from the worker proving that level theorem. -/
theorem trilinearSmallFactorIntegralBound
    (C : ℕ) (X T ε Nleft Nright vleft vright : ℝ)
    (Fsmall Fleft Fright : ℝ → ℂ) (E : Set ℝ)
    (hX : 2 ^ 16 ≤ X) (hT : 2 ≤ T)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 3 / 16)
    (hTupper : T ≤ X ^ (3 / 8 - ε))
    (hNleft : Nleft = X ^ vleft) (hNright : Nright = X ^ vright)
    (hvleft : vleft ≤ 1 / 2 + 3 / 1600)
    (hvright : vright ≤ 1 / 2 + 3 / 1600)
    (hpair : vleft + vright ≤ 7 / 8 + 3 / 1600)
    (hEmeas : MeasurableSet E)
    (hEsubset : E ⊆ Set.Icc (-T) T)
    (hsmall : ∀ t ∈ E, ‖Fsmall t‖ ≤ 1)
    (hcontSmall : Continuous Fsmall) (hcontLeft : Continuous Fleft)
    (hcontRight : Continuous Fright)
    (hmeanLeft : ∫ t in Set.Icc (-T) T, ‖Fleft t‖ ^ 2 ∂volume ≤
      K C * Real.log (4 * X) ^ b C * (T + Nleft))
    (hmeanRight : ∫ t in Set.Icc (-T) T, ‖Fright t‖ ^ 2 ∂volume ≤
      K C * Real.log (4 * X) ^ b C * (T + Nright)) :
    ∫ t in E, ‖Fsmall t * Fleft t * Fright t‖ ∂volume ≤
      2 * K C * Real.log (4 * X) ^ b C * X ^ ((15 : ℝ) / 32) := by
  classical
  let I := Set.Icc (-T) T
  let μI : Measure ℝ := volume.restrict I
  let μE : Measure ℝ := volume.restrict E
  let gLeft : ℝ → ℝ := fun t => ‖Fleft t‖
  let gRight : ℝ → ℝ := fun t => ‖Fright t‖
  let kL : ℝ := K C * Real.log (4 * X) ^ b C
  have hXone : 1 ≤ X := by
    have h16 : (1 : ℝ) ≤ 2 ^ 16 := by norm_num
    exact h16.trans hX
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXone
  have hLpos : 0 < Real.log (4 * X) := by
    apply Real.log_pos
    nlinarith
  have hKpos : 0 < K C := (constants_positive C).2.2.1
  have hkLpos : 0 < kL := by
    dsimp [kL]
    positivity
  have hkLnonneg : 0 ≤ kL := hkLpos.le
  have hμmono : μE ≤ μI := by
    dsimp [μE, μI, I]
    exact Measure.restrict_mono_set volume hEsubset
  have hcontLeftSq : Continuous (fun t : ℝ => gLeft t ^ 2) := by
    dsimp [gLeft]
    exact hcontLeft.norm.pow 2
  have hcontRightSq : Continuous (fun t : ℝ => gRight t ^ 2) := by
    dsimp [gRight]
    exact hcontRight.norm.pow 2
  have hleftSqI : Integrable (fun t : ℝ => gLeft t ^ 2) μI := by
    dsimp [μI, I]
    exact hcontLeftSq.continuousOn.integrableOn_compact isCompact_Icc
  have hrightSqI : Integrable (fun t : ℝ => gRight t ^ 2) μI := by
    dsimp [μI, I]
    exact hcontRightSq.continuousOn.integrableOn_compact isCompact_Icc
  have hleftLpI : MemLp gLeft 2 μI := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    exact hleftSqI
  have hrightLpI : MemLp gRight 2 μI := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    exact hrightSqI
  have hleftLpE : MemLp gLeft 2 μE := hleftLpI.mono_measure hμmono
  have hrightLpE : MemLp gRight 2 μE := hrightLpI.mono_measure hμmono
  have hleftLpE' : MemLp gLeft (ENNReal.ofReal 2) μE := by
    simpa using hleftLpE
  have hrightLpE' : MemLp gRight (ENNReal.ofReal 2) μE := by
    simpa using hrightLpE
  have hleftMeanI : ∫ t, gLeft t ^ 2 ∂μI ≤ kL * (T + Nleft) := by
    simpa [μI, I, gLeft, kL] using hmeanLeft
  have hrightMeanI : ∫ t, gRight t ^ 2 ∂μI ≤ kL * (T + Nright) := by
    simpa [μI, I, gRight, kL] using hmeanRight
  have hleftMeanE : ∫ t, gLeft t ^ 2 ∂μE ≤ kL * (T + Nleft) := by
    calc
      (∫ t, gLeft t ^ 2 ∂μE) ≤ ∫ t, gLeft t ^ 2 ∂μI :=
        MeasureTheory.integral_mono_measure hμmono
          (Filter.Eventually.of_forall fun t => sq_nonneg (gLeft t)) hleftSqI
      _ ≤ kL * (T + Nleft) := hleftMeanI
  have hrightMeanE : ∫ t, gRight t ^ 2 ∂μE ≤ kL * (T + Nright) := by
    calc
      (∫ t, gRight t ^ 2 ∂μE) ≤ ∫ t, gRight t ^ 2 ∂μI :=
        MeasureTheory.integral_mono_measure hμmono
          (Filter.Eventually.of_forall fun t => sq_nonneg (gRight t)) hrightSqI
      _ ≤ kL * (T + Nright) := hrightMeanI
  have hprodI : Integrable
      (fun t : ℝ => ‖Fsmall t * Fleft t * Fright t‖) μI := by
    have hcont : Continuous (fun t : ℝ => ‖Fsmall t * Fleft t * Fright t‖) := by
      fun_prop
    dsimp [μI, I]
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hpairI : Integrable (fun t : ℝ => gLeft t * gRight t) μI := by
    have hcont : Continuous (fun t : ℝ => gLeft t * gRight t) := by
      dsimp [gLeft, gRight]
      fun_prop
    dsimp [μI, I]
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hprodE : Integrable
      (fun t : ℝ => ‖Fsmall t * Fleft t * Fright t‖) μE := hprodI.mono_measure hμmono
  have hpairE : Integrable (fun t : ℝ => gLeft t * gRight t) μE := hpairI.mono_measure hμmono
  have hpoint (t : ℝ) (ht : t ∈ E) :
      ‖Fsmall t * Fleft t * Fright t‖ ≤ gLeft t * gRight t := by
    rw [norm_mul, norm_mul]
    dsimp [gLeft, gRight]
    have hs := hsmall t ht
    have hnonneg : 0 ≤ ‖Fleft t‖ * ‖Fright t‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right hs hnonneg]
  have hmonoIntegral :
      ∫ t in E, ‖Fsmall t * Fleft t * Fright t‖ ∂volume ≤
        ∫ t in E, gLeft t * gRight t ∂volume := by
    exact MeasureTheory.setIntegral_mono_on hprodE hpairE hEmeas hpoint
  have hcs :
      (∫ t, gLeft t * gRight t ∂μE) ≤
        (∫ t, gLeft t ^ 2 ∂μE) ^ (1 / 2 : ℝ) *
          (∫ t, gRight t ^ 2 ∂μE) ^ (1 / 2 : ℝ) := by
    simpa [gLeft, gRight, Real.rpow_natCast] using
      (integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μE) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun t => norm_nonneg (Fleft t))
      (Filter.Eventually.of_forall fun t => norm_nonneg (Fright t))
      hleftLpE' hrightLpE')
  have hcsSqrt :
      (∫ t, gLeft t * gRight t ∂μE) ≤
        Real.sqrt (∫ t, gLeft t ^ 2 ∂μE) *
          Real.sqrt (∫ t, gRight t ^ 2 ∂μE) := by
    simpa only [Real.sqrt_eq_rpow] using hcs
  have hsqrtBounds :
      Real.sqrt (∫ t, gLeft t ^ 2 ∂μE) *
          Real.sqrt (∫ t, gRight t ^ 2 ∂μE) ≤
        Real.sqrt (kL * (T + Nleft)) * Real.sqrt (kL * (T + Nright)) := by
    exact mul_le_mul
      (Real.sqrt_le_sqrt hleftMeanE) (Real.sqrt_le_sqrt hrightMeanE)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hrootProduct :
      Real.sqrt (kL * (T + Nleft)) * Real.sqrt (kL * (T + Nright)) =
        kL * Real.sqrt ((T + Nleft) * (T + Nright)) := by
    have hNleftPos : 0 < Nleft := by
      rw [hNleft]
      exact Real.rpow_pos_of_pos hXpos _
    have hTleft : 0 ≤ T + Nleft := by linarith
    rw [Real.sqrt_mul hkLnonneg, Real.sqrt_mul hkLnonneg]
    calc
      (Real.sqrt kL * Real.sqrt (T + Nleft)) *
          (Real.sqrt kL * Real.sqrt (T + Nright)) =
          (Real.sqrt kL) ^ 2 *
            (Real.sqrt (T + Nleft) * Real.sqrt (T + Nright)) := by ring
      _ = kL * Real.sqrt ((T + Nleft) * (T + Nright)) := by
        rw [Real.sq_sqrt hkLnonneg, ← Real.sqrt_mul hTleft]
  have hlength := pairLengthGrowthBound X T ε vleft vright hXone
    (by linarith) hε0 hTupper (by simpa [hNleft] using hvleft)
    (by simpa [hNright] using hvright) (by simpa [hNleft, hNright] using hpair)
  have hlengthN :
      Real.sqrt ((T + Nleft) * (T + Nright)) ≤ 2 * X ^ ((15 : ℝ) / 32) := by
    rw [hNleft, hNright]
    exact hlength
  calc
    (∫ t in E, ‖Fsmall t * Fleft t * Fright t‖ ∂volume) ≤
        ∫ t in E, gLeft t * gRight t ∂volume := hmonoIntegral
    _ = ∫ t, gLeft t * gRight t ∂μE := rfl
    _ ≤ Real.sqrt (∫ t, gLeft t ^ 2 ∂μE) *
        Real.sqrt (∫ t, gRight t ^ 2 ∂μE) := hcsSqrt
    _ ≤ Real.sqrt (kL * (T + Nleft)) * Real.sqrt (kL * (T + Nright)) := hsqrtBounds
    _ = kL * Real.sqrt ((T + Nleft) * (T + Nright)) := hrootProduct
    _ ≤ kL * (2 * X ^ ((15 : ℝ) / 32)) :=
      mul_le_mul_of_nonneg_left hlengthN hkLnonneg
    _ = 2 * K C * Real.log (4 * X) ^ b C * X ^ ((15 : ℝ) / 32) := by
      dsimp [kL]
      ring

end

#print axioms FractionalPrimes.Literature.DirichletMean.trilinearPairExponentBounds
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearSmallFactorIntegralBound

end FractionalPrimes.Literature.DirichletMean

end
