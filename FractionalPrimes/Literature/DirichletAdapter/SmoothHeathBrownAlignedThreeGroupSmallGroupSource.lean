module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupSmallGroupSourceInterval
public import Mathlib.Tactic
@[expose] public section

set_option maxRecDepth 4096

/-! A witness-preserving version of the checked `lda:small-group` source
branch.  It destructs the approved `IImaj` witness once, chooses the
distinguished factor inside that exact first group, and keeps the same group
through the residue-restricted interval estimate. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

private theorem smoothHeathBrownFixedGroupHasLargeWeight
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hE : 0 < smoothHeathBrownExponentSum fs)
    (I : Finset (Fin fs.length)) (hIcard : I.card ≤ 20)
    (hIlo : (1 / 4 : ℝ) ≤
      subsetWeightSum (smoothHeathBrownExponentGrouping fs hE) I) :
    ∃ i ∈ I, (1 / 80 : ℝ) ≤
      (smoothHeathBrownExponentGrouping fs hE).weight i := by
  classical
  let w := smoothHeathBrownExponentGrouping fs hE
  have hInonempty : I.Nonempty := by
    by_contra h
    have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hIempty, subsetWeightSum] at hIlo
    norm_num at hIlo
  by_contra hnot
  push_neg at hnot
  have hsumlt : subsetWeightSum w I < (I.card : ℝ) / 80 := by
    calc
      subsetWeightSum w I < ∑ i ∈ I, (1 / 80 : ℝ) := by
        apply Finset.sum_lt_sum
        · intro i hi
          exact le_of_lt (hnot i hi)
        · obtain ⟨i, hi⟩ := hInonempty
          exact ⟨i, hi, hnot i hi⟩
      _ = (I.card : ℝ) / 80 := by simp [div_eq_mul_inv]
  have hIcardR : (I.card : ℝ) ≤ 20 := by exact_mod_cast hIcard
  have hsumUpper : (I.card : ℝ) / 80 ≤ 1 / 4 := by nlinarith
  have hIlo' : (1 / 4 : ℝ) ≤ subsetWeightSum w I := by
    simpa [w] using hIlo
  linarith

private theorem smoothHeathBrownFixedGroupFactorScaleBounds
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hlen : fs.length ≤ 20)
    (hX : (2 : ℝ) ^ 200 ≤ X)
    (hP : X / (2 : ℝ) ^ 22 ≤ smoothHeathBrownScaleProduct fs ∧
      smoothHeathBrownScaleProduct fs ≤ (2 : ℝ) ^ 22 * X)
    (hE : 0 < smoothHeathBrownExponentSum fs)
    (I : Finset (Fin fs.length))
    (hIlo : (1 / 4 : ℝ) ≤
      subsetWeightSum (smoothHeathBrownExponentGrouping fs hE) I)
    (hIhi : subsetWeightSum (smoothHeathBrownExponentGrouping fs hE) I ≤
      1 / 2) :
    ∃ selected ∈ I,
      X ^ (1 / 100 : ℝ) ≤
        smoothHeathBrownFactorScale (fs.get selected) ∧
      smoothHeathBrownFactorScale (fs.get selected) ≤
        (2 : ℝ) ^ 11 * Real.sqrt X := by
  classical
  have hIcard : I.card ≤ 20 := by
    exact le_trans (Finset.card_le_card (Finset.subset_univ I)) (by simpa using hlen)
  let P := smoothHeathBrownScaleProduct fs
  let w := smoothHeathBrownExponentGrouping fs hE
  have hXpos : 0 < X := by
    have hp : 0 < (2 : ℝ) ^ 200 := by positivity
    linarith
  have hXone : 1 ≤ X := by
    have hp : 1 ≤ (2 : ℝ) ^ 200 := by norm_num
    exact le_trans hp hX
  have hPone : 1 ≤ P := by
    dsimp [P]
    have hlow : 1 ≤ X / (2 : ℝ) ^ 22 := by
      have hdiv : (2 : ℝ) ^ 200 / (2 : ℝ) ^ 22 ≤
          X / (2 : ℝ) ^ 22 :=
        div_le_div_of_nonneg_right hX (by positivity)
      have heq : (2 : ℝ) ^ 200 / (2 : ℝ) ^ 22 = (2 : ℝ) ^ 178 := by
        norm_num
      rw [heq] at hdiv
      linarith
    exact hlow.trans hP.1
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hPone
  let C : ℝ := (2 : ℝ) ^ 22
  have hCpos : 0 < C := by positivity
  have hC5 : C ^ 5 ≤ X := by
    have heq : C ^ 5 = (2 : ℝ) ^ 110 := by
      dsimp [C]
      norm_num [pow_mul]
    rw [heq]
    have hp : (2 : ℝ) ^ 110 ≤ (2 : ℝ) ^ 200 := by norm_num
    exact hp.trans hX
  have hCroot : C ^ (1 / 80 : ℝ) ≤
      X ^ (1 / 400 : ℝ) := by
    have hroot := Real.rpow_le_rpow
      (by positivity : 0 ≤ C ^ 5) hC5 (by norm_num : 0 ≤ (1 / 400 : ℝ))
    calc
      C ^ (1 / 80 : ℝ) = C ^ ((5 : ℝ) * (1 / 400 : ℝ)) := by
        congr 1 <;> norm_num
      _ = (C ^ 5) ^ (1 / 400 : ℝ) := by
        rw [Real.rpow_mul hCpos.le (5 : ℝ) (1 / 400 : ℝ)]
        rw [← Real.rpow_natCast C 5]
        rfl
      _ ≤ X ^ (1 / 400 : ℝ) := hroot
  have hrootComparison :
      1 ≤ ((C ^ (1 / 80 : ℝ))⁻¹) *
        X ^ (1 / 400 : ℝ) := by
    calc
      1 = (C ^ (1 / 80 : ℝ))⁻¹ * C ^ (1 / 80 : ℝ) := by field_simp
      _ ≤ (C ^ (1 / 80 : ℝ))⁻¹ *
          X ^ (1 / 400 : ℝ) :=
        mul_le_mul_of_nonneg_left hCroot (inv_nonneg.mpr (Real.rpow_pos_of_pos hCpos _).le)
  have hminScale : X ^ (1 / 100 : ℝ) ≤
      (C⁻¹ * X) ^ (1 / 80 : ℝ) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hCpos.le) hXpos.le,
      Real.inv_rpow hCpos.le]
    have hXsplit : X ^ (1 / 100 : ℝ) * X ^ (1 / 400 : ℝ) =
        X ^ (1 / 80 : ℝ) := by
      rw [← Real.rpow_add hXpos]
      congr 1 <;> norm_num
    calc
      X ^ (1 / 100 : ℝ) = X ^ (1 / 100 : ℝ) * 1 := by ring
      _ ≤ X ^ (1 / 100 : ℝ) * ((C ^ (1 / 80 : ℝ))⁻¹ *
          X ^ (1 / 400 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrootComparison
          (Real.rpow_nonneg hXpos.le _)
      _ = (C ^ (1 / 80 : ℝ))⁻¹ *
          (X ^ (1 / 100 : ℝ) * X ^ (1 / 400 : ℝ)) := by ring
      _ = (C ^ (1 / 80 : ℝ))⁻¹ * X ^ (1 / 80 : ℝ) := by rw [hXsplit]
  have hPmin : (C⁻¹ * X) ^ (1 / 80 : ℝ) ≤ P ^ (1 / 80 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    simpa [C, div_eq_mul_inv, mul_comm] using hP.1
  have hPmax : P ^ (1 / 2 : ℝ) ≤
      ((2 : ℝ) ^ 22 * X) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hPpos.le hP.2 (by norm_num)
  have hPmaxSqrt : ((2 : ℝ) ^ 22 * X) ^ (1 / 2 : ℝ) =
      (2 : ℝ) ^ 11 * Real.sqrt X := by
    calc
      ((2 : ℝ) ^ 22 * X) ^ (1 / 2 : ℝ) =
          Real.sqrt ((2 : ℝ) ^ 22 * X) := by rw [← Real.sqrt_eq_rpow]
      _ = Real.sqrt ((2 : ℝ) ^ 22) * Real.sqrt X := by
        rw [Real.sqrt_mul (by positivity)]
      _ = (2 : ℝ) ^ 11 * Real.sqrt X := by
        have hsquare : (2 : ℝ) ^ 22 = ((2 : ℝ) ^ 11) ^ 2 := by
          norm_num [pow_mul]
        rw [show Real.sqrt ((2 : ℝ) ^ 22) = (2 : ℝ) ^ 11 by
          rw [hsquare]
          rw [Real.sqrt_sq_eq_abs]
          norm_num]
  obtain ⟨i, hiI, hiweight⟩ :=
    smoothHeathBrownFixedGroupHasLargeWeight fs hE I hIcard hIlo
  have hiWeightSum : w.weight i ≤ subsetWeightSum w I := by
    change w.weight i ≤ ∑ j ∈ I, w.weight j
    exact Finset.single_le_sum (fun j hj => w.weight_nonneg j) hiI
  have hscaleEq : smoothHeathBrownFactorScale (fs.get i) = P ^ w.weight i := by
    dsimp [P, w]
    exact smoothHeathBrownFactorScale_eq_scaleProduct_rpow_groupWeight fs hE i
  refine ⟨i, hiI, ?_, ?_⟩
  · rw [hscaleEq]
    calc
      X ^ (1 / 100 : ℝ) ≤ (C⁻¹ * X) ^ (1 / 80 : ℝ) := hminScale
      _ ≤ P ^ (1 / 80 : ℝ) := hPmin
      _ ≤ P ^ w.weight i := Real.rpow_le_rpow_of_exponent_le hPone hiweight
  · rw [hscaleEq]
    calc
      P ^ w.weight i ≤ P ^ subsetWeightSum w I :=
        Real.rpow_le_rpow_of_exponent_le hPone hiWeightSum
      _ ≤ P ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hPone (by simpa [w] using hIhi)
      _ ≤ ((2 : ℝ) ^ 22 * X) ^ (1 / 2 : ℝ) := hPmax
      _ = (2 : ℝ) ^ 11 * Real.sqrt X := hPmaxSqrt

private theorem smoothHeathBrownAlignedThetaLogBlockConstant_le
    {X : ℝ} (f : SmoothHeathBrownFactor X)
    (hbranch : (∃ j : SmoothHeathBrownScaleIndex X, f = .theta j) ∨
      (∃ j : SmoothHeathBrownScaleIndex X, f = .logarithm j)) :
    smoothHeathBrownFreeFactorBlockConstant f ≤
      smoothHeathBrownThetaLogSelectedGroupBlockConstant := by
  have hphase : 0 ≤ periodicLogPhaseConstant (1 / 200 : ℝ) 1 := by
    unfold periodicLogPhaseConstant
    exact le_trans (by norm_num) (le_max_left _ _)
  rcases hbranch with htheta | hlog
  · rcases htheta with ⟨j, hj⟩
    rw [hj]
    change (2 : ℝ) ^ 11 * 5 ^ 19 * 5 *
        periodicLogPhaseConstant (1 / 200) 1 ≤
      (2 : ℝ) ^ 11 * 5 ^ 19 * 6 *
        periodicLogPhaseConstant (1 / 200) 1
    nlinarith
  · rcases hlog with ⟨j, hj⟩
    rw [hj]
    rfl

private theorem smoothHeathBrownAlignedThetaLogThresholds
    {X B K : ℝ} (f : SmoothHeathBrownFactor X)
    (hbranch : (∃ j : SmoothHeathBrownScaleIndex X, f = .theta j) ∨
      (∃ j : SmoothHeathBrownScaleIndex X, f = .logarithm j))
    (hR : smoothHeathBrownThreeGroupSmallGroupLogThreshold B K ≤
      Real.log X) :
    (2 / periodicLogPhaseSaving (1 / 200) 1) *
        Real.log (2 * smoothHeathBrownFreeFactorBlockConstant f *
          logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) ≤
      Real.log X ∧
    (2 * Real.sqrt 2 * smoothHeathBrownFreeFactorBlockConstant f) ^
        (1 / 5 : ℝ) ≤ Real.log X := by
  have hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j := by
    intro j hmobius
    rcases hbranch with htheta | hlog
    · rcases htheta with ⟨jθ, hjθ⟩
      rw [hjθ] at hmobius
      cases hmobius
    · rcases hlog with ⟨jlog, hjlog⟩
      rw [hjlog] at hmobius
      cases hmobius
  have hC : 1 ≤ smoothHeathBrownFreeFactorBlockConstant f :=
    smoothHeathBrownFreeFactorBlockConstant_ge_one f hfree
  have hCupper := smoothHeathBrownAlignedThetaLogBlockConstant_le f hbranch
  have hdelta : 0 < periodicLogPhaseSaving (1 / 200) 1 := by
    unfold periodicLogPhaseSaving
    positivity
  have hMpos : 0 < logAbsorptionM
      (periodicLogPhaseSaving (1 / 200) 1) K :=
    lt_of_lt_of_le (by norm_num) one_le_logAbsorptionM
  have harg : 0 < 2 * smoothHeathBrownFreeFactorBlockConstant f *
      logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K := by
    positivity
  have hargUpper :
      2 * smoothHeathBrownFreeFactorBlockConstant f *
        logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K ≤
      2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant *
        logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCupper (by norm_num)) hMpos.le
  have hlogarg := Real.log_le_log harg hargUpper
  have hpolyCompare :
      (2 / periodicLogPhaseSaving (1 / 200) 1) *
        Real.log (2 * smoothHeathBrownFreeFactorBlockConstant f *
          logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) ≤
      (2 / periodicLogPhaseSaving (1 / 200) 1) *
        Real.log (2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant *
          logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) :=
    mul_le_mul_of_nonneg_left hlogarg (by positivity)
  have hbaseCompare :
      2 * Real.sqrt 2 * smoothHeathBrownFreeFactorBlockConstant f ≤
        2 * Real.sqrt 2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant :=
    mul_le_mul_of_nonneg_left hCupper (by positivity)
  have htailCompare := Real.rpow_le_rpow
    (by positivity : 0 ≤ 2 * Real.sqrt 2 *
      smoothHeathBrownFreeFactorBlockConstant f)
    hbaseCompare (by norm_num : 0 ≤ (1 / 5 : ℝ))
  have hpolyMax :
      (2 / periodicLogPhaseSaving (1 / 200) 1) *
          Real.log (2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant *
            logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) ≤
        smoothHeathBrownThreeGroupSmallGroupLogThreshold B K := by
    unfold smoothHeathBrownThreeGroupSmallGroupLogThreshold
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have htailMax :
      (2 * Real.sqrt 2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant) ^
          (1 / 5 : ℝ) ≤ smoothHeathBrownThreeGroupSmallGroupLogThreshold B K := by
    unfold smoothHeathBrownThreeGroupSmallGroupLogThreshold
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  constructor
  · exact le_trans hpolyCompare (le_trans hpolyMax hR)
  · exact le_trans htailCompare (le_trans htailMax hR)

/-- Witness-preserving `lda:small-group` source output.  The returned `I` is
the first member of the exact `IImaj` partition passed as `hgroup`; the
selected factor and every interval estimate use that same `I`. -/
theorem smoothHeathBrownThreeGroupSmallGroupSourceInterval_onIImajWitness
    {B K D : ℝ} (hB : 0 < B) (hK : 0 < K)
    (hD : 2 * K + 10 ≤ D) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fs : List (SmoothHeathBrownFactor X)) →
        fs.length ≤ 20 → fs ≠ [] →
        smoothHeathBrownSupportRetained
          (X := X) (z := dyadicMobiusCutoff X) fs →
        (hE : 0 < smoothHeathBrownExponentSum fs) →
        (smoothHeathBrownExponentGrouping fs hE).IImaj (5 / 8) →
        ∃ I J J' : Finset (Fin fs.length), ∃ selected : Fin fs.length,
          Disjoint I J ∧ Disjoint I J' ∧ Disjoint J J' ∧
          I ∪ J ∪ J' = Finset.univ ∧
          (1 / 4 : ℝ) ≤
            subsetWeightSum (smoothHeathBrownExponentGrouping fs hE) I ∧
          subsetWeightSum (smoothHeathBrownExponentGrouping fs hE) I ≤
            1 / 2 ∧
          |subsetWeightSum (smoothHeathBrownExponentGrouping fs hE) J -
            subsetWeightSum (smoothHeathBrownExponentGrouping fs hE) J'| ≤
              1 / 4 ∧
          selected ∈ I ∧ I.card ≤ 20 ∧
          X ^ (1 / 100 : ℝ) ≤
            smoothHeathBrownFactorScale (fs.get selected) ∧
          smoothHeathBrownFactorScale (fs.get selected) ≤
            (2 : ℝ) ^ 11 * Real.sqrt X ∧
          ∀ (h : ℤ) (L x y : ℝ) {q : ℕ},
            1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
            (residue : Fin fs.length → ℕ) → residue selected < q →
            (t : ℝ) → (Real.log X) ^ D / 2 ≤ |t| → |t| ≤ X →
            L = (2 : ℝ) ^ h *
              (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)) →
            -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ) →
            L ≤ x → x ≤ y → y ≤ 2 * L →
            ‖∑ n ∈ factorExtractionRealInterval x y,
                (∏ i : I,
                  smoothHeathBrownResidueFactorArithmeticFunction (z := z)
                    q (residue i.val) (fs.get i.val)) n *
                  (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
              Real.sqrt L * (Real.log X) ^ (-K) := by
  obtain ⟨Cμ, Xbase, hCμ, hXbase3, hMUFSource⟩ :=
    smoothHeathBrownMobiusSelectedGroupSourceInterval_of_scaleBounds_OAISource
      hB hK
  let R := smoothHeathBrownThreeGroupSmallGroupLogThreshold B K
  let X₀ := max Xbase (max ((2 : ℝ) ^ 200) (Real.exp R))
  have hX₀three : 3 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans hXbase3 (le_max_left _ _)
  refine ⟨Cμ, X₀, hCμ, hX₀three, ?_⟩
  intro X z hX₀X hz fs hlen hfsne hret hE hgroup
  have hXbaseX : Xbase ≤ X :=
    le_trans (le_max_left _ _) hX₀X
  have hXscale : (2 : ℝ) ^ 200 ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX₀X
  have hExpRX : Real.exp R ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX₀X
  have hlogR : R ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos R) hExpRX
    simpa using h
  have hRtwo : 2 ≤ R := by
    dsimp [R, smoothHeathBrownThreeGroupSmallGroupLogThreshold]
    exact le_max_left _ _
  have hlog : 2 ≤ Real.log X := le_trans hRtwo hlogR
  have hqLarge : (2 / (1 / 400 : ℝ)) *
      Real.log (logAbsorptionM (1 / 400) B) ≤ Real.log X := by
    have hRmod : (2 / (1 / 400 : ℝ)) *
        Real.log (logAbsorptionM (1 / 400) B) ≤ R := by
      dsimp [R, smoothHeathBrownThreeGroupSmallGroupLogThreshold]
      exact le_trans (le_max_left _ _)
        (le_max_right _ _)
    exact le_trans hRmod hlogR
  rcases hgroup with ⟨I, J, J', hIJ, hIJ', hJJ', hcover,
    hIlo, hIhi, hgap⟩
  norm_num at hIlo hIhi hgap
  have hXnonneg : 0 ≤ X := by linarith
  have hPbounds := smoothHeathBrownSupportRetained_scale_bounds
    hlen hfsne hXnonneg hret
  have hPwindow : X / (2 : ℝ) ^ 22 ≤ smoothHeathBrownScaleProduct fs ∧
      smoothHeathBrownScaleProduct fs ≤ (2 : ℝ) ^ 22 * X := by
    constructor
    · simpa [div_eq_mul_inv, mul_comm] using hPbounds.1
    · exact hPbounds.2
  obtain ⟨selected, hselected, hNlo, hNhi⟩ :=
    smoothHeathBrownFixedGroupFactorScaleBounds fs hlen hXscale hPwindow hE
      I hIlo hIhi
  have hIcard : I.card ≤ 20 := by
    calc
      I.card ≤ (Finset.univ : Finset (Fin fs.length)).card :=
        Finset.card_le_card (Finset.subset_univ I)
      _ = fs.length := by simp
      _ ≤ 20 := hlen
  refine ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover, ?_, ?_, ?_,
    hselected, hIcard, hNlo, hNhi, ?_⟩
  · exact hIlo
  · exact hIhi
  · exact hgap
  intro h L x y q hq hqlog residue hresidue t hT0t htX hL hh hLx hxy hy
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hXpos : 0 < X := by
    have hp : 0 < (2 : ℝ) ^ 200 := by positivity
    linarith
  have hscalePos : ∀ i ∈ I,
      0 < smoothHeathBrownFactorScale (fs.get i) := by
    intro i hi
    have hscale := smoothHeathBrownFactorScale_ge_one (fs.get i)
    linarith
  have hscaleProductPos : 0 <
      ∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i) :=
    Finset.prod_pos fun i hi => hscalePos i hi
  have hLpos : 0 < L := by
    rw [hL]
    exact mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) h)
      hscaleProductPos
  have hx : 0 ≤ x := le_trans (le_of_lt hLpos) hLx
  have hdelta : 0 < periodicLogPhaseSaving (1 / 200) 1 := by
    unfold periodicLogPhaseSaving
    positivity
  have hC : 1 ≤ smoothHeathBrownThetaLogSelectedGroupBlockConstant := by
    unfold smoothHeathBrownThetaLogSelectedGroupBlockConstant
    have hphase : 64 ≤ periodicLogPhaseConstant (1 / 200 : ℝ) 1 := by
      unfold periodicLogPhaseConstant
      exact le_max_left _ _
    nlinarith [hphase]
  cases htag : fs.get selected with
  | theta j =>
      have hbranch : (∃ j : SmoothHeathBrownScaleIndex X,
          fs.get selected = .theta j) ∨
        (∃ j : SmoothHeathBrownScaleIndex X,
          fs.get selected = .logarithm j) := Or.inl ⟨j, htag⟩
      have hthresholds := smoothHeathBrownAlignedThetaLogThresholds
        (fs.get selected) hbranch hlogR
      have htheta := smoothHeathBrownThetaLogSelectedSubsetSourceInterval_logDecay
        (z := z) (I := I) (selected := selected) (hselected := hselected)
        (hcount := hIcard) hbranch residue hresidue hXscale hB hK hD hlog
        hqPos hqlog hqLarge (T0 := (Real.log X) ^ D / 2) rfl hT0t htX
        hNlo hNhi h hL hh hLx hxy hy hthresholds.1 hthresholds.2
      simpa [smoothHeathBrownThetaLogSourceResidueFactor,
        smoothHeathBrownResidueFactorArithmeticFunction] using htheta
  | logarithm j =>
      have hbranch : (∃ j : SmoothHeathBrownScaleIndex X,
          fs.get selected = .theta j) ∨
        (∃ j : SmoothHeathBrownScaleIndex X,
          fs.get selected = .logarithm j) := Or.inr ⟨j, htag⟩
      have hthresholds := smoothHeathBrownAlignedThetaLogThresholds
        (fs.get selected) hbranch hlogR
      have hlogarithm :=
        smoothHeathBrownThetaLogSelectedSubsetSourceInterval_logDecay
          (z := z) (I := I) (selected := selected) (hselected := hselected)
          (hcount := hIcard) hbranch residue hresidue hXscale hB hK hD hlog
          hqPos hqlog hqLarge (T0 := (Real.log X) ^ D / 2) rfl hT0t htX
          hNlo hNhi h hL hh hLx hxy hy hthresholds.1 hthresholds.2
      simpa [smoothHeathBrownThetaLogSourceResidueFactor,
        smoothHeathBrownResidueFactorArithmeticFunction] using hlogarithm
  | mobius j =>
      have hNlo' : X ^ (1 / 100 : ℝ) ≤
          smoothHeathBrownFactorScale (.mobius j) := by
        rw [← htag]
        exact hNlo
      have hNhi' : smoothHeathBrownFactorScale (.mobius j) ≤
          (2 : ℝ) ^ 11 * Real.sqrt X := by
        rw [← htag]
        exact hNhi
      have hmobius := hMUFSource hXbaseX hz fs I selected j htag
        hselected hIcard h L x y hq hqlog residue hresidue t htX
        hNlo' hNhi' hL hh hx hxy
      calc
        _ ≤ (Real.log X) ^ (-K) * Real.sqrt L := hmobius.2
        _ = Real.sqrt L * (Real.log X) ^ (-K) := by ring

#print axioms smoothHeathBrownThreeGroupSmallGroupSourceInterval_onIImajWitness

end FractionalPrimes.Literature.DirichletAdapter

end
