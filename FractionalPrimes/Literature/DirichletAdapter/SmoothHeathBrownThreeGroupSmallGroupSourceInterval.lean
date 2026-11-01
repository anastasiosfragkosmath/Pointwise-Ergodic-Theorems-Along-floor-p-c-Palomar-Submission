module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThetaLogSelectedGroupSourceInterval
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupMobiusSourceInterval
public import Mathlib.Tactic
@[expose] public section

/-! Assemble the checked theta/log and Möbius source interval estimates at
the selected factor supplied by the approved retained three-group selector.
The resulting theorem has one source statement for all three factor tags. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- Uniform block prefactor for the two periodic theta/log branches.  The
logarithmic factor has the larger interval cost, namely six. -/
noncomputable def smoothHeathBrownThetaLogSelectedGroupBlockConstant : ℝ :=
  (2 : ℝ) ^ 11 * 5 ^ 19 * 6 * periodicLogPhaseConstant (1 / 200) 1

/-- A single logarithmic threshold that simultaneously supplies the modulus
bound and the two periodic-error absorption inequalities for either
theta/log tag. -/
noncomputable def smoothHeathBrownThreeGroupSmallGroupLogThreshold
    (B K : ℝ) : ℝ :=
  max 2
    (max ((2 / (1 / 400 : ℝ)) *
        Real.log (logAbsorptionM (1 / 400) B))
      (max ((2 / periodicLogPhaseSaving (1 / 200) 1) *
          Real.log (2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant *
            logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K))
        ((2 * Real.sqrt 2 *
          smoothHeathBrownThetaLogSelectedGroupBlockConstant) ^
            (1 / 5 : ℝ))))

private theorem smoothHeathBrownThetaLogSelectedGroupBlockConstant_le
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

private theorem smoothHeathBrownThetaLogSelectedGroupThresholds
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
  have hfree : ∀ j : SmoothHeathBrownScaleIndex X,
      f ≠ .mobius j := by
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
  have hCupper := smoothHeathBrownThetaLogSelectedGroupBlockConstant_le
    f hbranch
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
        2 * Real.sqrt 2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant := by
    exact mul_le_mul_of_nonneg_left hCupper (by positivity)
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
    change
      (2 / periodicLogPhaseSaving (1 / 200) 1) *
          Real.log (2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant *
            logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) ≤
        max 2
          (max ((2 / (1 / 400 : ℝ)) *
              Real.log (logAbsorptionM (1 / 400) B))
            (max ((2 / periodicLogPhaseSaving (1 / 200) 1) *
                Real.log (2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant *
                  logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K))
              ((2 * Real.sqrt 2 *
                smoothHeathBrownThetaLogSelectedGroupBlockConstant) ^
                  (1 / 5 : ℝ))))
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have htailMax :
      (2 * Real.sqrt 2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant) ^
          (1 / 5 : ℝ) ≤ smoothHeathBrownThreeGroupSmallGroupLogThreshold B K := by
    unfold smoothHeathBrownThreeGroupSmallGroupLogThreshold
    change
      (2 * Real.sqrt 2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant) ^
          (1 / 5 : ℝ) ≤
        max 2
          (max ((2 / (1 / 400 : ℝ)) *
              Real.log (logAbsorptionM (1 / 400) B))
            (max ((2 / periodicLogPhaseSaving (1 / 200) 1) *
                Real.log (2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant *
                  logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K))
              ((2 * Real.sqrt 2 *
                smoothHeathBrownThetaLogSelectedGroupBlockConstant) ^
                  (1 / 5 : ℝ))))
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  constructor
  · exact le_trans hpolyCompare (le_trans hpolyMax hR)
  · exact le_trans htailCompare (le_trans htailMax hR)

/-- The source-faithful three-tag `lda:small-group` interval estimate under
the approved retained three-group data. The same selected group and selected
factor work in all cases: the checked OAISource Möbius interval branch handles
the Möbius tag, while the theta and normalized-log tags use the residue-phase
finite transfer and the two absorbed periodic errors. -/
theorem smoothHeathBrownThreeGroupSmallGroupSourceInterval_of_OAISource
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
        ∃ I : Finset (Fin fs.length), ∃ selected : Fin fs.length,
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
    smoothHeathBrownThreeGroupMobiusSourceInterval_of_OAISource hB hK
  let R := smoothHeathBrownThreeGroupSmallGroupLogThreshold B K
  let X₀ := max Xbase (max ((2 : ℝ) ^ 200) (Real.exp R))
  have hX₀three : 3 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans hXbase3 (le_max_left _ _)
  refine ⟨Cμ, X₀, hCμ, hX₀three, ?_⟩
  intro X z hX₀X hz fs hlen hfsne hret hE hgroup
  have hXbaseX : Xbase ≤ X :=
    le_trans (le_max_left _ _) hX₀X
  have hXscale : (2 : ℝ) ^ 200 ≤ X := by
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX₀X
  have hExpRX : Real.exp R ≤ X := by
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX₀X
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
      change
        (2 / (1 / 400 : ℝ)) * Real.log (logAbsorptionM (1 / 400) B) ≤
          max 2
            (max ((2 / (1 / 400 : ℝ)) *
                Real.log (logAbsorptionM (1 / 400) B))
              (max ((2 / periodicLogPhaseSaving (1 / 200) 1) *
                  Real.log (2 * smoothHeathBrownThetaLogSelectedGroupBlockConstant *
                    logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K))
                ((2 * Real.sqrt 2 *
                  smoothHeathBrownThetaLogSelectedGroupBlockConstant) ^
                    (1 / 5 : ℝ))))
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact le_trans hRmod hlogR
  obtain ⟨I, selected, hselected, hIcard, hNlo, hNhi, hMrange,
      hmobiusSource⟩ :=
    hMUFSource hXbaseX hz fs hlen hfsne hret hE hgroup
  refine ⟨I, selected, hselected, hIcard, hNlo, hNhi, ?_⟩
  intro h L x y q hq hqLog residue hresidue t hT0t htX hL hh hLx hxy hy
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
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
      have hthresholds := smoothHeathBrownThetaLogSelectedGroupThresholds
        (fs.get selected) hbranch hlogR
      have htheta := smoothHeathBrownThetaLogSelectedSubsetSourceInterval_logDecay
        (z := z) (I := I) (selected := selected) (hselected := hselected)
        (hcount := hIcard) hbranch residue hresidue hXscale hB hK hD hlog
        hqPos hqLog hqLarge (T0 := (Real.log X) ^ D / 2) rfl hT0t htX
        hNlo hNhi h hL hh hLx hxy hy hthresholds.1 hthresholds.2
      simpa [smoothHeathBrownThetaLogSourceResidueFactor,
        smoothHeathBrownResidueFactorArithmeticFunction] using htheta
  | logarithm j =>
      have hbranch : (∃ j : SmoothHeathBrownScaleIndex X,
          fs.get selected = .theta j) ∨
        (∃ j : SmoothHeathBrownScaleIndex X,
          fs.get selected = .logarithm j) := Or.inr ⟨j, htag⟩
      have hthresholds := smoothHeathBrownThetaLogSelectedGroupThresholds
        (fs.get selected) hbranch hlogR
      have hlogarithm :=
        smoothHeathBrownThetaLogSelectedSubsetSourceInterval_logDecay
          (z := z) (I := I) (selected := selected) (hselected := hselected)
          (hcount := hIcard) hbranch residue hresidue hXscale hB hK hD hlog
          hqPos hqLog hqLarge (T0 := (Real.log X) ^ D / 2) rfl hT0t htX
          hNlo hNhi h hL hh hLx hxy hy hthresholds.1 hthresholds.2
      simpa [smoothHeathBrownThetaLogSourceResidueFactor,
        smoothHeathBrownResidueFactorArithmeticFunction] using hlogarithm
  | mobius j =>
      have hmobius := hmobiusSource j htag h L x y hq hqLog residue
        hresidue t htX hL hh hx hxy
      calc
        _ ≤ (Real.log X) ^ (-K) * Real.sqrt L := hmobius.2
        _ = Real.sqrt L * (Real.log X) ^ (-K) := by ring

#print axioms smoothHeathBrownThreeGroupSmallGroupSourceInterval_of_OAISource

end FractionalPrimes.Literature.DirichletAdapter

end
