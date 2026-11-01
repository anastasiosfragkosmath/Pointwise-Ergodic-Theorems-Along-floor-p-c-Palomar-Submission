module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownRetention
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownSmallGroupData
import Mathlib.Tactic

/-! Exact scale bookkeeping for the three-group block decomposition in
`lda:dp-from-muf`. This file is discrete and contains no harmonic estimates. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- A dyadic block scale based at a selected subgroup scale. -/
def smoothHeathBrownDyadicBlockScale (S : ℝ) (h : ℤ) : ℝ :=
  (2 : ℝ) ^ h * S

/-- Product scale of three dyadic blocks. -/
def smoothHeathBrownThreeDyadicBlockProductScale
    (S₁ S₂ S₃ : ℝ) (h₁ h₂ h₃ : ℤ) : ℝ :=
  smoothHeathBrownDyadicBlockScale S₁ h₁ *
    smoothHeathBrownDyadicBlockScale S₂ h₂ *
    smoothHeathBrownDyadicBlockScale S₃ h₃

/-- The component scale factors exactly over a disjoint three-way partition
of its factor positions. -/
theorem smoothHeathBrownScaleProduct_eq_threeSubgroupScaleProducts
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I J K : Finset (Fin fs.length))
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K)
    (hcover : I ∪ J ∪ K = Finset.univ) :
    smoothHeathBrownScaleProduct fs =
      smoothHeathBrownSubgroupScaleProduct fs I *
        smoothHeathBrownSubgroupScaleProduct fs J *
          smoothHeathBrownSubgroupScaleProduct fs K := by
  have hdisjUnion : Disjoint (I ∪ J) K := by
    rw [Finset.disjoint_left]
    intro i hi hk
    rcases Finset.mem_union.mp hi with hiI | hiJ
    · exact (Finset.disjoint_left.mp hIK) hiI hk
    · exact (Finset.disjoint_left.mp hJK) hiJ hk
  have hsum :
      (smoothHeathBrownSubgroupExponent fs I : ℕ) +
        smoothHeathBrownSubgroupExponent fs J +
          smoothHeathBrownSubgroupExponent fs K =
        smoothHeathBrownExponentSum fs := by
    dsimp [smoothHeathBrownSubgroupExponent, smoothHeathBrownExponentSum]
    calc
      (∑ i ∈ I, smoothHeathBrownFactorExponent (fs.get i)) +
          (∑ i ∈ J, smoothHeathBrownFactorExponent (fs.get i)) +
          (∑ i ∈ K, smoothHeathBrownFactorExponent (fs.get i)) =
          (∑ i ∈ I ∪ J, smoothHeathBrownFactorExponent (fs.get i)) +
            (∑ i ∈ K, smoothHeathBrownFactorExponent (fs.get i)) := by
              rw [Finset.sum_union hIJ]
      _ = ∑ i ∈ (I ∪ J) ∪ K,
          smoothHeathBrownFactorExponent (fs.get i) :=
            (Finset.sum_union hdisjUnion).symm
      _ = ∑ i : Fin fs.length, smoothHeathBrownFactorExponent (fs.get i) := by
            rw [hcover]
      _ = _ := rfl
  calc
    smoothHeathBrownScaleProduct fs =
        (2 : ℝ) ^ smoothHeathBrownExponentSum fs :=
      smoothHeathBrownScaleProduct_eq_two_pow_exponentSum fs
    _ = (2 : ℝ) ^ (smoothHeathBrownSubgroupExponent fs I +
          smoothHeathBrownSubgroupExponent fs J +
            smoothHeathBrownSubgroupExponent fs K) := by rw [← hsum]
    _ = (2 : ℝ) ^ smoothHeathBrownSubgroupExponent fs I *
          (2 : ℝ) ^ smoothHeathBrownSubgroupExponent fs J *
            (2 : ℝ) ^ smoothHeathBrownSubgroupExponent fs K := by
          rw [← pow_add, ← pow_add]
    _ = smoothHeathBrownSubgroupScaleProduct fs I *
          smoothHeathBrownSubgroupScaleProduct fs J *
            smoothHeathBrownSubgroupScaleProduct fs K := by
          rw [← smoothHeathBrownSubgroupScaleProduct_eq_two_pow_exponent,
            ← smoothHeathBrownSubgroupScaleProduct_eq_two_pow_exponent,
            ← smoothHeathBrownSubgroupScaleProduct_eq_two_pow_exponent]

/-- The three shifted dyadic blocks multiply to the original component scale
times the single dyadic shift determined by the sum of the three shifts. -/
theorem smoothHeathBrownThreeDyadicBlockProductScale_eq_shiftedComponentScale
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I J K : Finset (Fin fs.length))
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K)
    (hcover : I ∪ J ∪ K = Finset.univ)
    (h₁ h₂ h₃ : ℤ) :
    smoothHeathBrownThreeDyadicBlockProductScale
        (smoothHeathBrownSubgroupScaleProduct fs I)
        (smoothHeathBrownSubgroupScaleProduct fs J)
        (smoothHeathBrownSubgroupScaleProduct fs K) h₁ h₂ h₃ =
      (2 : ℝ) ^ (h₁ + h₂ + h₃) * smoothHeathBrownScaleProduct fs := by
  calc
    _ = ((2 : ℝ) ^ h₁ * (2 : ℝ) ^ h₂ * (2 : ℝ) ^ h₃) *
        (smoothHeathBrownSubgroupScaleProduct fs I *
          smoothHeathBrownSubgroupScaleProduct fs J *
          smoothHeathBrownSubgroupScaleProduct fs K) := by
          simp [smoothHeathBrownThreeDyadicBlockProductScale,
            smoothHeathBrownDyadicBlockScale]
          ring
    _ = (2 : ℝ) ^ (h₁ + h₂ + h₃) *
        (smoothHeathBrownSubgroupScaleProduct fs I *
          smoothHeathBrownSubgroupScaleProduct fs J *
          smoothHeathBrownSubgroupScaleProduct fs K) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (2 : ℝ) ^ (h₁ + h₂ + h₃) * smoothHeathBrownScaleProduct fs := by
          rw [smoothHeathBrownScaleProduct_eq_threeSubgroupScaleProducts
            fs I J K hIJ hIK hJK hcover]

/-- The source product window transfers to the three shifted block product
with the exact `2^20` loss from the total number of factor positions. -/
theorem smoothHeathBrownThreeDyadicBlockProductScale_componentWindow
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hlen : fs.length ≤ 20)
    (I J K : Finset (Fin fs.length))
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K)
    (hcover : I ∪ J ∪ K = Finset.univ)
    (hPwindow : X / (2 : ℝ) ^ 22 ≤ smoothHeathBrownScaleProduct fs ∧
      smoothHeathBrownScaleProduct fs ≤ (2 : ℝ) ^ 22 * X)
    (h₁ h₂ h₃ : ℤ)
    (hh₁ : -(I.card : ℤ) ≤ h₁ ∧ h₁ < I.card)
    (hh₂ : -(J.card : ℤ) ≤ h₂ ∧ h₂ < J.card)
    (hh₃ : -(K.card : ℤ) ≤ h₃ ∧ h₃ < K.card) :
    X / (2 : ℝ) ^ 42 ≤
        smoothHeathBrownThreeDyadicBlockProductScale
          (smoothHeathBrownSubgroupScaleProduct fs I)
          (smoothHeathBrownSubgroupScaleProduct fs J)
          (smoothHeathBrownSubgroupScaleProduct fs K) h₁ h₂ h₃ ∧
      smoothHeathBrownThreeDyadicBlockProductScale
          (smoothHeathBrownSubgroupScaleProduct fs I)
          (smoothHeathBrownSubgroupScaleProduct fs J)
          (smoothHeathBrownSubgroupScaleProduct fs K) h₁ h₂ h₃ ≤
        (2 : ℝ) ^ 42 * X := by
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
  have hcardLe : I.card + J.card + K.card ≤ 20 := by
    rw [hcardSum]
    exact hlen
  have hshift : -(20 : ℤ) ≤ h₁ + h₂ + h₃ ∧
      h₁ + h₂ + h₃ ≤ 20 := by
    omega
  have hpowLower : (2 : ℝ) ^ (-(20 : ℤ)) ≤ (2 : ℝ) ^ (h₁ + h₂ + h₃) :=
    zpow_le_zpow_right₀ (by norm_num) hshift.1
  have hpowUpper : (2 : ℝ) ^ (h₁ + h₂ + h₃) ≤ (2 : ℝ) ^ (20 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hshift.2
  have hPpos : 0 < smoothHeathBrownScaleProduct fs :=
    smoothHeathBrownScaleProduct_pos fs
  have hYfactor :=
    smoothHeathBrownThreeDyadicBlockProductScale_eq_shiftedComponentScale
      fs I J K hIJ hIK hJK hcover h₁ h₂ h₃
  have hYlower :
      (2 : ℝ) ^ (-(20 : ℤ)) * (X / (2 : ℝ) ^ 22) ≤
        smoothHeathBrownThreeDyadicBlockProductScale
          (smoothHeathBrownSubgroupScaleProduct fs I)
          (smoothHeathBrownSubgroupScaleProduct fs J)
          (smoothHeathBrownSubgroupScaleProduct fs K) h₁ h₂ h₃ := by
    rw [hYfactor]
    calc
      (2 : ℝ) ^ (-(20 : ℤ)) * (X / (2 : ℝ) ^ 22) ≤
          (2 : ℝ) ^ (-(20 : ℤ)) * smoothHeathBrownScaleProduct fs :=
        mul_le_mul_of_nonneg_left hPwindow.1 (by positivity)
      _ ≤ (2 : ℝ) ^ (h₁ + h₂ + h₃) * smoothHeathBrownScaleProduct fs :=
        mul_le_mul_of_nonneg_right hpowLower hPpos.le
  have hYupper :
      smoothHeathBrownThreeDyadicBlockProductScale
          (smoothHeathBrownSubgroupScaleProduct fs I)
          (smoothHeathBrownSubgroupScaleProduct fs J)
          (smoothHeathBrownSubgroupScaleProduct fs K) h₁ h₂ h₃ ≤
        (2 : ℝ) ^ (20 : ℤ) * ((2 : ℝ) ^ 22 * X) := by
    rw [hYfactor]
    calc
      (2 : ℝ) ^ (h₁ + h₂ + h₃) * smoothHeathBrownScaleProduct fs ≤
          (2 : ℝ) ^ (20 : ℤ) * smoothHeathBrownScaleProduct fs :=
        mul_le_mul_of_nonneg_right hpowUpper hPpos.le
      _ ≤ (2 : ℝ) ^ (20 : ℤ) * ((2 : ℝ) ^ 22 * X) :=
        mul_le_mul_of_nonneg_left hPwindow.2 (by positivity)
  have hlowConst :
      (2 : ℝ) ^ (-(20 : ℤ)) * (X / (2 : ℝ) ^ 22) =
        X / (2 : ℝ) ^ 42 := by
    norm_num [zpow_neg]
    ring
  have hhighConst :
      (2 : ℝ) ^ (20 : ℤ) * ((2 : ℝ) ^ 22 * X) =
        (2 : ℝ) ^ 42 * X := by
    norm_num [zpow_natCast]
    ring
  constructor
  · rw [← hlowConst]
    exact hYlower
  · rw [← hhighConst]
    exact hYupper

/-- Under the source group-balance hypotheses, each shifted group block has
lower endpoint at least `2`. The only large-`X` input used here is the source
component window together with the stated logarithmic threshold. -/
theorem smoothHeathBrownThreeDyadicBlockScales_ge_two
    {X η : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hlen : fs.length ≤ 20)
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hη : 0 < η) (hηsmall : η < 3 / 16)
    (hlogThreshold : 10 ^ 6 / η ≤ Real.log X)
    (I J K : Finset (Fin fs.length))
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K)
    (hcover : I ∪ J ∪ K = Finset.univ)
    (hPwindow : X / (2 : ℝ) ^ 22 ≤ smoothHeathBrownScaleProduct fs ∧
      smoothHeathBrownScaleProduct fs ≤ (2 : ℝ) ^ 22 * X)
    (hIratio : (1 / 4 : ℝ) ≤
        Real.log (smoothHeathBrownSubgroupScaleProduct fs I) /
          Real.log (smoothHeathBrownScaleProduct fs) ∧
      Real.log (smoothHeathBrownSubgroupScaleProduct fs I) /
          Real.log (smoothHeathBrownScaleProduct fs) ≤ 1 / 2)
    (hJKbalance :
      |Real.log (smoothHeathBrownSubgroupScaleProduct fs J) /
          Real.log (smoothHeathBrownScaleProduct fs) -
        Real.log (smoothHeathBrownSubgroupScaleProduct fs K) /
          Real.log (smoothHeathBrownScaleProduct fs)| ≤ 1 / 4)
    (h₁ h₂ h₃ : ℤ)
    (hh₁ : -(I.card : ℤ) ≤ h₁ ∧ h₁ < I.card)
    (hh₂ : -(J.card : ℤ) ≤ h₂ ∧ h₂ < J.card)
    (hh₃ : -(K.card : ℤ) ≤ h₃ ∧ h₃ < K.card) :
    2 ≤ smoothHeathBrownDyadicBlockScale
          (smoothHeathBrownSubgroupScaleProduct fs I) h₁ ∧
    2 ≤ smoothHeathBrownDyadicBlockScale
          (smoothHeathBrownSubgroupScaleProduct fs J) h₂ ∧
    2 ≤ smoothHeathBrownDyadicBlockScale
          (smoothHeathBrownSubgroupScaleProduct fs K) h₃ := by
  let S₁ := smoothHeathBrownSubgroupScaleProduct fs I
  let S₂ := smoothHeathBrownSubgroupScaleProduct fs J
  let S₃ := smoothHeathBrownSubgroupScaleProduct fs K
  let P := smoothHeathBrownScaleProduct fs
  let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
  let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
  let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
  have hXpos : 0 < X := by
    have hpow : 0 < (2 : ℝ) ^ 200 := by positivity
    linarith
  have hXgt1 : 1 < X := by
    have hpow : 1 < (2 : ℝ) ^ 200 := by norm_num
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
  have hlog2le1 : Real.log 2 ≤ 1 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).2
    have h := Real.add_one_le_exp 1
    norm_num at h ⊢
    linarith
  have hηle1 : η ≤ 1 := by linarith
  have hinvη : 1 ≤ (1 : ℝ) / η :=
    (le_div_iff₀ hη).2 (by nlinarith)
  have hlogXlarge : (10 ^ 6 : ℝ) ≤ Real.log X := by
    have hbound : (10 ^ 6 : ℝ) ≤ (10 ^ 6 : ℝ) / η := by
      calc
        (10 ^ 6 : ℝ) = (10 ^ 6 : ℝ) * 1 := by ring
        _ ≤ (10 ^ 6 : ℝ) * ((1 : ℝ) / η) :=
          mul_le_mul_of_nonneg_left hinvη (by norm_num : (0 : ℝ) ≤ (10 ^ 6 : ℝ))
        _ = (10 ^ 6 : ℝ) / η := by ring
    exact le_trans hbound hlogThreshold
  have hPlogLo : Real.log X - 22 * Real.log 2 ≤ Real.log P := by
    have h := (Real.log_le_log_iff
        (div_pos hXpos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 22)) hPpos).2
      (by simpa [P] using hPwindow.1)
    rw [Real.log_div hXpos.ne' (by positivity : (2 : ℝ) ^ 22 ≠ 0),
      Real.log_pow] at h
    norm_num at h
    linarith
  have hPlogBig : 168 * Real.log 2 ≤ Real.log P := by
    nlinarith [hPlogLo, hlogXlarge, hlog2le1]
  have hlogPpos : 0 < Real.log P :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 168) hlog2pos) hPlogBig
  have hPfactorLog :
      Real.log P = Real.log S₁ + Real.log S₂ + Real.log S₃ := by
    have hPfactorR : P = S₁ * (S₂ * S₃) := by rw [hPfactor]; ring
    rw [hPfactorR, Real.log_mul (hSpos.1.ne')
      (mul_ne_zero hSpos.2.1.ne' hSpos.2.2.ne'),
      Real.log_mul hSpos.2.1.ne' hSpos.2.2.ne']
    ring
  have hIlog :
      (1 / 4 : ℝ) * Real.log P ≤ Real.log S₁ ∧
      Real.log S₁ ≤ (1 / 2 : ℝ) * Real.log P := by
    rcases hIratio with ⟨hlo, hhi⟩
    constructor
    · exact (le_div_iff₀ hlogPpos).mp hlo
    · exact (div_le_iff₀ hlogPpos).mp hhi
  have hbalanceParts := abs_le.mp hJKbalance
  have hratioDiff :
      Real.log S₂ / Real.log P - Real.log S₃ / Real.log P =
        (Real.log S₂ - Real.log S₃) / Real.log P := by
    field_simp [hlogPpos.ne']
  rw [hratioDiff] at hbalanceParts
  have hdiffLo : -(1 / 4 : ℝ) * Real.log P ≤ Real.log S₂ - Real.log S₃ := by
    have h := (le_div_iff₀ hlogPpos).mp hbalanceParts.1
    exact h
  have hdiffHi : Real.log S₂ - Real.log S₃ ≤
      (1 / 4 : ℝ) * Real.log P := by
    have h := (div_le_iff₀ hlogPpos).mp hbalanceParts.2
    exact h
  have hsumJK :
      (1 / 2 : ℝ) * Real.log P ≤ Real.log S₂ + Real.log S₃ := by
    linarith only [hPfactorLog, hIlog.2]
  have hS₂logLo : (1 / 8 : ℝ) * Real.log P ≤ Real.log S₂ := by
    linarith only [hsumJK, hdiffLo]
  have hS₃logLo : (1 / 8 : ℝ) * Real.log P ≤ Real.log S₃ := by
    linarith only [hsumJK, hdiffHi]
  have hcardSum : I.card + J.card + K.card = fs.length := by
    have hdisjUnion : Disjoint (I ∪ J) K := by
      rw [Finset.disjoint_left]
      intro i hi hk
      rcases Finset.mem_union.mp hi with hiI | hiJ
      · exact (Finset.disjoint_left.mp hIK) hiI hk
      · exact (Finset.disjoint_left.mp hJK) hiJ hk
    have hcardAll := Finset.card_union_of_disjoint hdisjUnion
    rw [hcover, Finset.card_univ, Fintype.card_fin] at hcardAll
    rw [Finset.card_union_of_disjoint hIJ] at hcardAll
    exact hcardAll.symm
  have hcardSumLe : I.card + J.card + K.card ≤ 20 := by
    rw [hcardSum]
    exact hlen
  have h₁low : -(20 : ℤ) ≤ h₁ := by omega
  have h₂low : -(20 : ℤ) ≤ h₂ := by omega
  have h₃low : -(20 : ℤ) ≤ h₃ := by omega
  have h₁lowR : -(20 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast h₁low
  have h₂lowR : -(20 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast h₂low
  have h₃lowR : -(20 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast h₃low
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
  have hshift₁ : -(20 : ℝ) * Real.log 2 ≤ (h₁ : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right h₁lowR hlog2pos.le
  have hshift₂ : -(20 : ℝ) * Real.log 2 ≤ (h₂ : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right h₂lowR hlog2pos.le
  have hshift₃ : -(20 : ℝ) * Real.log 2 ≤ (h₃ : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right h₃lowR hlog2pos.le
  have hPquarter : 21 * Real.log 2 ≤ (1 / 8 : ℝ) * Real.log P := by
    nlinarith only [hPlogBig]
  have hS₁logLo : (1 / 8 : ℝ) * Real.log P ≤ Real.log S₁ := by
    have hstep : (1 / 8 : ℝ) * Real.log P ≤ (1 / 4 : ℝ) * Real.log P :=
      mul_le_mul_of_nonneg_right (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
        hlogPpos.le
    exact le_trans hstep hIlog.1
  have hlogL₁lower : Real.log 2 ≤ Real.log L₁ := by
    rw [hlogL₁]
    calc
      Real.log 2 ≤ (1 / 8 : ℝ) * Real.log P - 20 * Real.log 2 := by
        linarith only [hPquarter]
      _ ≤ (h₁ : ℝ) * Real.log 2 + Real.log S₁ := by
        linarith only [hS₁logLo, hshift₁]
  have hlogL₂lower : Real.log 2 ≤ Real.log L₂ := by
    rw [hlogL₂]
    calc
      Real.log 2 ≤ (1 / 8 : ℝ) * Real.log P - 20 * Real.log 2 := by
        linarith only [hPquarter]
      _ ≤ (h₂ : ℝ) * Real.log 2 + Real.log S₂ := by
        linarith only [hS₂logLo, hshift₂]
  have hlogL₃lower : Real.log 2 ≤ Real.log L₃ := by
    rw [hlogL₃]
    calc
      Real.log 2 ≤ (1 / 8 : ℝ) * Real.log P - 20 * Real.log 2 := by
        linarith only [hPquarter]
      _ ≤ (h₃ : ℝ) * Real.log 2 + Real.log S₃ := by
        linarith only [hS₃logLo, hshift₃]
  have hLpos : 0 < L₁ ∧ 0 < L₂ ∧ 0 < L₃ := by
    dsimp [L₁, L₂, L₃, smoothHeathBrownDyadicBlockScale]
    exact ⟨mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) h₁) hSpos.1,
      mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) h₂) hSpos.2.1,
      mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) h₃) hSpos.2.2⟩
  have hL₁ : 2 ≤ L₁ :=
    (Real.log_le_log_iff (by norm_num) hLpos.1).1 hlogL₁lower
  have hL₂ : 2 ≤ L₂ :=
    (Real.log_le_log_iff (by norm_num) hLpos.2.1).1 hlogL₂lower
  have hL₃ : 2 ≤ L₃ :=
    (Real.log_le_log_iff (by norm_num) hLpos.2.2).1 hlogL₃lower
  exact ⟨by simpa [L₁, S₁] using hL₁,
    by simpa [L₂, S₂] using hL₂,
    by simpa [L₃, S₃] using hL₃⟩

/-- A normalized logarithmic quotient changes by at most `80 t / z` when
both its numerator and denominator move by at most `20 t`, provided the
original numerator lies between zero and the original denominator and the
new denominator is at least `z/2`. -/
theorem smoothHeathBrownNormalizedLogRatioError
    {a b c d t z : ℝ}
    (hb : 0 < b) (hd : 0 < d) (ht : 0 ≤ t) (hz : 0 < z)
    (hc : 0 ≤ c) (hcb : c ≤ b)
    (hNumeratorShift : |a - c| ≤ 20 * t)
    (hDenominatorShift : |b - d| ≤ 20 * t)
    (hDenominatorLower : z / 2 ≤ d) :
    |a / d - c / b| ≤ 80 * t / z := by
  have hidentity :
      a / d - c / b = ((a - c) * b + c * (b - d)) / (d * b) := by
    field_simp [hb.ne', hd.ne']
    ring
  have hnum :
      |(a - c) * b + c * (b - d)| ≤ 40 * t * b := by
    calc
      |(a - c) * b + c * (b - d)| ≤
          |a - c| * b + c * |b - d| := by
            calc
              _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul, abs_of_pos hb, abs_of_nonneg hc]
      _ ≤ 20 * t * b + c * (20 * t) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hNumeratorShift hb.le)
              (mul_le_mul_of_nonneg_left hDenominatorShift hc)
      _ ≤ 20 * t * b + b * (20 * t) := by
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_right hcb (by positivity))
      _ = 40 * t * b := by ring
  have hfirst :
      |(a - c) * b + c * (b - d)| / (d * b) ≤ 40 * t / d := by
    apply (div_le_iff₀ (mul_pos hd hb)).2
    calc
      |(a - c) * b + c * (b - d)| ≤ 40 * t * b := hnum
      _ = (40 * t / d) * (d * b) := by field_simp [hd.ne']
  have hcross : 40 * t * z ≤ 80 * t * d := by
    have h := mul_le_mul_of_nonneg_left hDenominatorLower
      (by positivity : (0 : ℝ) ≤ 80 * t)
    nlinarith [h]
  have hsecond : 40 * t / d ≤ 80 * t / z := by
    exact (div_le_div_iff₀ hd hz).2 hcross
  calc
    |a / d - c / b| =
        |(a - c) * b + c * (b - d)| / (d * b) := by
          rw [hidentity, abs_div, abs_of_pos (mul_pos hd hb)]
    _ ≤ 40 * t / d := hfirst
    _ ≤ 80 * t / z := hsecond

#print axioms smoothHeathBrownScaleProduct_eq_threeSubgroupScaleProducts
#print axioms smoothHeathBrownThreeDyadicBlockProductScale_eq_shiftedComponentScale
#print axioms smoothHeathBrownThreeDyadicBlockProductScale_componentWindow
#print axioms smoothHeathBrownThreeDyadicBlockScales_ge_two
#print axioms smoothHeathBrownNormalizedLogRatioError

end FractionalPrimes.Literature.DirichletAdapter

end
