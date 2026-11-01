module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupBlockGeometry
import Mathlib.Tactic

/-! Source instantiation of the normalized logarithmic quotient estimate in
the three-group part of `lda:dp-from-muf`. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The three block exponents differ from their selected-group exponents by
at most `80 log 2 / log X`, as in the source proof of `lda:dp-from-muf`. -/
theorem smoothHeathBrownThreeGroupBlockNormalizedExponentErrors
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hlen : fs.length ≤ 20)
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hlogX84 : 84 * Real.log 2 ≤ Real.log X)
    (I J K : Finset (Fin fs.length))
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K)
    (hcover : I ∪ J ∪ K = Finset.univ)
    (hPwindow : X / (2 : ℝ) ^ 22 ≤ smoothHeathBrownScaleProduct fs ∧
      smoothHeathBrownScaleProduct fs ≤ (2 : ℝ) ^ 22 * X)
    (h₁ h₂ h₃ : ℤ)
    (hh₁ : -(I.card : ℤ) ≤ h₁ ∧ h₁ < I.card)
    (hh₂ : -(J.card : ℤ) ≤ h₂ ∧ h₂ < J.card)
    (hh₃ : -(K.card : ℤ) ≤ h₃ ∧ h₃ < K.card) :
    let S₁ := smoothHeathBrownSubgroupScaleProduct fs I
    let S₂ := smoothHeathBrownSubgroupScaleProduct fs J
    let S₃ := smoothHeathBrownSubgroupScaleProduct fs K
    let P := smoothHeathBrownScaleProduct fs
    let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
    let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
    let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
    let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
    |Real.log L₁ / Real.log Y - Real.log S₁ / Real.log P| ≤
        80 * Real.log 2 / Real.log X ∧
    |Real.log L₂ / Real.log Y - Real.log S₂ / Real.log P| ≤
        80 * Real.log 2 / Real.log X ∧
    |Real.log L₃ / Real.log Y - Real.log S₃ / Real.log P| ≤
        80 * Real.log 2 / Real.log X := by
  classical
  let S₁ := smoothHeathBrownSubgroupScaleProduct fs I
  let S₂ := smoothHeathBrownSubgroupScaleProduct fs J
  let S₃ := smoothHeathBrownSubgroupScaleProduct fs K
  let P := smoothHeathBrownScaleProduct fs
  let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
  let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
  let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
  let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
  have hXpos : 0 < X := by
    have hpow : 0 < (2 : ℝ) ^ 200 := by positivity
    linarith
  have hPpos : 0 < P := by
    dsimp [P]
    exact smoothHeathBrownScaleProduct_pos fs
  have hSpos : 0 < S₁ ∧ 0 < S₂ ∧ 0 < S₃ := by
    have hpos (T : Finset (Fin fs.length)) :
        0 < smoothHeathBrownSubgroupScaleProduct fs T :=
      Finset.prod_pos fun i hi => smoothHeathBrownFactorScale_pos (fs.get i)
    exact ⟨by simpa [S₁] using hpos I,
      by simpa [S₂] using hpos J, by simpa [S₃] using hpos K⟩
  have hSone : 1 ≤ S₁ ∧ 1 ≤ S₂ ∧ 1 ≤ S₃ := by
    have hone (T : Finset (Fin fs.length)) :
        1 ≤ smoothHeathBrownSubgroupScaleProduct fs T := by
      rw [smoothHeathBrownSubgroupScaleProduct_eq_two_pow_exponent]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact ⟨by simpa [S₁] using hone I,
      by simpa [S₂] using hone J, by simpa [S₃] using hone K⟩
  have hPfactor : P = S₁ * S₂ * S₃ := by
    dsimp [P, S₁, S₂, S₃]
    exact smoothHeathBrownScaleProduct_eq_threeSubgroupScaleProducts
      fs I J K hIJ hIK hJK hcover
  have hSleP : S₁ ≤ P ∧ S₂ ≤ P ∧ S₃ ≤ P := by
    rcases hSone with ⟨hS₁one, hS₂one, hS₃one⟩
    rw [hPfactor]
    have h₂₃ : 1 ≤ S₂ * S₃ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hS₂one) (sub_nonneg.mpr hS₃one)]
    have h₁₃ : 1 ≤ S₁ * S₃ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hS₁one) (sub_nonneg.mpr hS₃one)]
    have h₁₂ : 1 ≤ S₁ * S₂ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hS₁one) (sub_nonneg.mpr hS₂one)]
    refine ⟨?_, ?_, ?_⟩
    · calc
        S₁ = S₁ * 1 := by ring
        _ ≤ S₁ * (S₂ * S₃) := mul_le_mul_of_nonneg_left h₂₃ hSpos.1.le
        _ = S₁ * S₂ * S₃ := by ring
    · calc
        S₂ = 1 * S₂ := by ring
        _ ≤ (S₁ * S₃) * S₂ := mul_le_mul_of_nonneg_right h₁₃ hSpos.2.1.le
        _ = S₁ * S₂ * S₃ := by ring
    · calc
        S₃ = 1 * S₃ := by ring
        _ ≤ (S₁ * S₂) * S₃ := mul_le_mul_of_nonneg_right h₁₂ hSpos.2.2.le
        _ = S₁ * S₂ * S₃ := by ring
  have hSlogBound :
      0 ≤ Real.log S₁ ∧ Real.log S₁ ≤ Real.log P ∧
      0 ≤ Real.log S₂ ∧ Real.log S₂ ≤ Real.log P ∧
      0 ≤ Real.log S₃ ∧ Real.log S₃ ≤ Real.log P := by
    rcases hSone with ⟨hS₁one, hS₂one, hS₃one⟩
    rcases hSleP with ⟨hS₁P, hS₂P, hS₃P⟩
    refine ⟨Real.log_nonneg hS₁one, Real.log_le_log hSpos.1 hS₁P,
      Real.log_nonneg hS₂one, Real.log_le_log hSpos.2.1 hS₂P,
      Real.log_nonneg hS₃one, Real.log_le_log hSpos.2.2 hS₃P⟩
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogPlo : Real.log X - 22 * Real.log 2 ≤ Real.log P := by
    have h := (Real.log_le_log_iff
        (div_pos hXpos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 22)) hPpos).2
      (by simpa [P] using hPwindow.1)
    rw [Real.log_div hXpos.ne' (by positivity : (2 : ℝ) ^ 22 ≠ 0),
      Real.log_pow] at h
    norm_num at h
    linarith
  have hlogPpos : 0 < Real.log P := by
    have hlog2pos84 : 0 < 84 * Real.log 2 := mul_pos (by norm_num) hlog2pos
    have hlogXpos : 0 < Real.log X := lt_of_lt_of_le hlog2pos84 hlogX84
    have hlogPbig : 62 * Real.log 2 ≤ Real.log P := by
      linarith [hlogPlo, hlogX84]
    exact lt_of_lt_of_le (mul_pos (by norm_num) hlog2pos) hlogPbig
  have hPfactorR : P = S₁ * (S₂ * S₃) := by rw [hPfactor]; ring
  have hPfactorLog :
      Real.log P = Real.log S₁ + Real.log S₂ + Real.log S₃ := by
    rw [hPfactorR, Real.log_mul (hSpos.1.ne')
      (mul_ne_zero hSpos.2.1.ne' hSpos.2.2.ne'),
      Real.log_mul hSpos.2.1.ne' hSpos.2.2.ne']
    ring
  have hYfactor :=
    smoothHeathBrownThreeDyadicBlockProductScale_eq_shiftedComponentScale
      fs I J K hIJ hIK hJK hcover h₁ h₂ h₃
  have hYpos : 0 < Y := by
    change 0 < smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
    rw [hYfactor]
    exact mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) (h₁ + h₂ + h₃))
      (smoothHeathBrownScaleProduct_pos fs)
  have hYwindow :=
    smoothHeathBrownThreeDyadicBlockProductScale_componentWindow fs hlen
      I J K hIJ hIK hJK hcover hPwindow h₁ h₂ h₃ hh₁ hh₂ hh₃
  have hYlogLo : Real.log X - 42 * Real.log 2 ≤ Real.log Y := by
    have h := (Real.log_le_log_iff
        (div_pos hXpos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 42)) hYpos).2
      (by simpa [Y] using hYwindow.1)
    rw [Real.log_div hXpos.ne' (by positivity : (2 : ℝ) ^ 42 ≠ 0),
      Real.log_pow] at h
    norm_num at h
    linarith
  have hYlogHalf : Real.log X / 2 ≤ Real.log Y := by
    linarith [hYlogLo, hlogX84]
  have hYlogpos : 0 < Real.log Y := by
    have hlogXpos : 0 < Real.log X :=
      lt_of_lt_of_le (mul_pos (by norm_num) hlog2pos) hlogX84
    exact lt_of_lt_of_le (half_pos hlogXpos) hYlogHalf
  have hlogL₁ : Real.log L₁ = (h₁ : ℝ) * Real.log 2 + Real.log S₁ := by
    dsimp [L₁, smoothHeathBrownDyadicBlockScale]
    rw [Real.log_mul (zpow_ne_zero _ (by norm_num)) hSpos.1.ne',
      Real.log_zpow]
  have hlogL₂ : Real.log L₂ = (h₂ : ℝ) * Real.log 2 + Real.log S₂ := by
    dsimp [L₂, smoothHeathBrownDyadicBlockScale]
    rw [Real.log_mul (zpow_ne_zero _ (by norm_num)) hSpos.2.1.ne',
      Real.log_zpow]
  have hlogL₃ : Real.log L₃ = (h₃ : ℝ) * Real.log 2 + Real.log S₃ := by
    dsimp [L₃, smoothHeathBrownDyadicBlockScale]
    rw [Real.log_mul (zpow_ne_zero _ (by norm_num)) hSpos.2.2.ne',
      Real.log_zpow]
  have hdisjUnion : Disjoint (I ∪ J) K := by
    rw [Finset.disjoint_left]
    intro i hi hk
    rcases Finset.mem_union.mp hi with hiI | hiJ
    · exact (Finset.disjoint_left.mp hIK) hiI hk
    · exact (Finset.disjoint_left.mp hJK) hiJ hk
  have hcardSum : I.card + J.card + K.card = fs.length := by
    have hcardAll := Finset.card_union_of_disjoint hdisjUnion
    rw [hcover, Finset.card_univ, Fintype.card_fin] at hcardAll
    rw [Finset.card_union_of_disjoint hIJ] at hcardAll
    exact hcardAll.symm
  have hcardSumLe : I.card + J.card + K.card ≤ 20 := by
    rw [hcardSum]
    exact hlen
  have hshift : -(20 : ℤ) ≤ h₁ + h₂ + h₃ ∧
      h₁ + h₂ + h₃ ≤ 20 := by omega
  have htotalAbs : |((h₁ + h₂ + h₃ : ℤ) : ℝ)| ≤ 20 := by
    have h : |h₁ + h₂ + h₃| ≤ (20 : ℤ) := abs_le.mpr hshift
    exact_mod_cast h
  have hcardI : I.card ≤ 20 := by omega
  have hcardJ : J.card ≤ 20 := by omega
  have hcardK : K.card ≤ 20 := by omega
  have h₁abs : |(h₁ : ℝ)| ≤ (I.card : ℝ) := by
    have h : |h₁| ≤ (I.card : ℤ) := abs_le.mpr ⟨hh₁.1, le_of_lt hh₁.2⟩
    exact_mod_cast h
  have h₂abs : |(h₂ : ℝ)| ≤ (J.card : ℝ) := by
    have h : |h₂| ≤ (J.card : ℤ) := abs_le.mpr ⟨hh₂.1, le_of_lt hh₂.2⟩
    exact_mod_cast h
  have h₃abs : |(h₃ : ℝ)| ≤ (K.card : ℝ) := by
    have h : |h₃| ≤ (K.card : ℤ) := abs_le.mpr ⟨hh₃.1, le_of_lt hh₃.2⟩
    exact_mod_cast h
  have h₁shift : |Real.log L₁ - Real.log S₁| ≤ 20 * Real.log 2 := by
    rw [hlogL₁]
    calc
      |(h₁ : ℝ) * Real.log 2 + Real.log S₁ - Real.log S₁| =
          |(h₁ : ℝ) * Real.log 2| := by congr 1 <;> ring
      _ = |(h₁ : ℝ)| * Real.log 2 := by
          rw [abs_mul, abs_of_pos hlog2pos]
      _ ≤ (I.card : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h₁abs hlog2pos.le
      _ ≤ 20 * Real.log 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcardI) hlog2pos.le
  have h₂shift : |Real.log L₂ - Real.log S₂| ≤ 20 * Real.log 2 := by
    rw [hlogL₂]
    calc
      |(h₂ : ℝ) * Real.log 2 + Real.log S₂ - Real.log S₂| =
          |(h₂ : ℝ) * Real.log 2| := by congr 1 <;> ring
      _ = |(h₂ : ℝ)| * Real.log 2 := by
          rw [abs_mul, abs_of_pos hlog2pos]
      _ ≤ (J.card : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h₂abs hlog2pos.le
      _ ≤ 20 * Real.log 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcardJ) hlog2pos.le
  have h₃shift : |Real.log L₃ - Real.log S₃| ≤ 20 * Real.log 2 := by
    rw [hlogL₃]
    calc
      |(h₃ : ℝ) * Real.log 2 + Real.log S₃ - Real.log S₃| =
          |(h₃ : ℝ) * Real.log 2| := by congr 1 <;> ring
      _ = |(h₃ : ℝ)| * Real.log 2 := by
          rw [abs_mul, abs_of_pos hlog2pos]
      _ ≤ (K.card : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h₃abs hlog2pos.le
      _ ≤ 20 * Real.log 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcardK) hlog2pos.le
  have hlogY : Real.log Y =
      ((h₁ + h₂ + h₃ : ℤ) : ℝ) * Real.log 2 + Real.log P := by
    change Real.log
      (smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃) = _
    rw [hYfactor, Real.log_mul (zpow_ne_zero _ (by norm_num)) hPpos.ne',
      Real.log_zpow]
  have hYshift : |Real.log P - Real.log Y| ≤ 20 * Real.log 2 := by
    rw [hlogY]
    calc
      |Real.log P -
          ((h₁ + h₂ + h₃ : ℤ) * Real.log 2 + Real.log P)| =
          |((h₁ + h₂ + h₃ : ℤ) : ℝ)| * Real.log 2 := by
            rw [show Real.log P -
              ((h₁ + h₂ + h₃ : ℤ) * Real.log 2 + Real.log P) =
                -((h₁ + h₂ + h₃ : ℤ) : ℝ) * Real.log 2 by ring,
              abs_mul, abs_neg, abs_of_pos hlog2pos]
      _ ≤ 20 * Real.log 2 :=
          mul_le_mul_of_nonneg_right htotalAbs hlog2pos.le
  have hlogXpos : 0 < Real.log X :=
    lt_of_lt_of_le (mul_pos (by norm_num) hlog2pos) hlogX84
  have herr₁ := smoothHeathBrownNormalizedLogRatioError
    hlogPpos hYlogpos hlog2pos.le hlogXpos hSlogBound.1 hSlogBound.2.1
    h₁shift hYshift hYlogHalf
  have herr₂ := smoothHeathBrownNormalizedLogRatioError
    hlogPpos hYlogpos hlog2pos.le hlogXpos hSlogBound.2.2.1
    hSlogBound.2.2.2.1 h₂shift hYshift hYlogHalf
  have herr₃ := smoothHeathBrownNormalizedLogRatioError
    hlogPpos hYlogpos hlog2pos.le hlogXpos hSlogBound.2.2.2.2.1
    hSlogBound.2.2.2.2.2 h₃shift hYshift hYlogHalf
  simpa [S₁, S₂, S₃, P, L₁, L₂, L₃, Y] using ⟨herr₁, herr₂, herr₃⟩

#print axioms smoothHeathBrownThreeGroupBlockNormalizedExponentErrors

end FractionalPrimes.Literature.DirichletAdapter

end
