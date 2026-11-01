module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupBlockExponentErrors
import Mathlib.Tactic

/-! The source `η/200` display bounds obtained from the normalized exponent
error estimate and the explicit logarithmic threshold in `lda:dp-from-muf`. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The three-group block exponents obey the source display bounds. Here
`ε = η/2`, so the blueprint's `ε/100` allowance is `η/200`. -/
theorem smoothHeathBrownThreeGroupBlockExponentBounds
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
    let S₁ := smoothHeathBrownSubgroupScaleProduct fs I
    let S₂ := smoothHeathBrownSubgroupScaleProduct fs J
    let S₃ := smoothHeathBrownSubgroupScaleProduct fs K
    let P := smoothHeathBrownScaleProduct fs
    let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
    let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
    let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
    let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
    (1 / 4 : ℝ) - η / 200 ≤ Real.log L₁ / Real.log Y ∧
    Real.log L₁ / Real.log Y ≤ 1 / 2 + η / 200 ∧
    |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
      1 / 4 + η / 200 := by
  classical
  let S₁ := smoothHeathBrownSubgroupScaleProduct fs I
  let S₂ := smoothHeathBrownSubgroupScaleProduct fs J
  let S₃ := smoothHeathBrownSubgroupScaleProduct fs K
  let P := smoothHeathBrownScaleProduct fs
  let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
  let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
  let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
  let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
  have hXgt1 : 1 < X := by
    have hpow : 1 < (2 : ℝ) ^ 200 := by norm_num
    linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos hXgt1
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
  have hlogX84 : 84 * Real.log 2 ≤ Real.log X := by
    calc
      84 * Real.log 2 ≤ 84 := by
        calc
          84 * Real.log 2 = Real.log 2 * 84 := by ring
          _ ≤ 1 * 84 := mul_le_mul_of_nonneg_right hlog2le1
            (by norm_num : (0 : ℝ) ≤ 84)
          _ = 84 := by ring
      _ ≤ 10 ^ 6 := by norm_num
      _ ≤ Real.log X := hlogXlarge
  have hηlogX : (10 ^ 6 : ℝ) ≤ η * Real.log X := by
    have h := (div_le_iff₀ hη).mp hlogThreshold
    nlinarith [h]
  have hconstant : 32000 * Real.log 2 ≤ η * Real.log X := by
    calc
      32000 * Real.log 2 ≤ 32000 :=
        by
          calc
            32000 * Real.log 2 = Real.log 2 * 32000 := by ring
            _ ≤ 1 * 32000 := mul_le_mul_of_nonneg_right hlog2le1
              (by norm_num : (0 : ℝ) ≤ 32000)
            _ = 32000 := by ring
      _ ≤ 10 ^ 6 := by norm_num
      _ ≤ η * Real.log X := hηlogX
  have herrSmall : 80 * Real.log 2 / Real.log X ≤ η / 400 := by
    apply (div_le_iff₀ hlogXpos).2
    nlinarith [hconstant]
  have herrors := smoothHeathBrownThreeGroupBlockNormalizedExponentErrors
    fs hlen hXscale hlogX84 I J K hIJ hIK hJK hcover hPwindow h₁ h₂ h₃
      hh₁ hh₂ hh₃
  have h₁err := abs_le.mp herrors.1
  have h₂err := abs_le.mp herrors.2.1
  have h₃err := abs_le.mp herrors.2.2
  have hIlo :
      (1 / 4 : ℝ) - η / 200 ≤ Real.log L₁ / Real.log Y := by
    have h := hIratio.1
    linarith [h₁err.1, herrSmall]
  have hIhi :
      Real.log L₁ / Real.log Y ≤ (1 / 2 : ℝ) + η / 200 := by
    have h := hIratio.2
    linarith [h₁err.2, herrSmall]
  have hJKparts := abs_le.mp hJKbalance
  have hJKlo : -(1 / 4 : ℝ) ≤
      Real.log (smoothHeathBrownSubgroupScaleProduct fs J) /
        Real.log (smoothHeathBrownScaleProduct fs) -
      Real.log (smoothHeathBrownSubgroupScaleProduct fs K) /
        Real.log (smoothHeathBrownScaleProduct fs) := hJKparts.1
  have hJKhi :
      Real.log (smoothHeathBrownSubgroupScaleProduct fs J) /
        Real.log (smoothHeathBrownScaleProduct fs) -
      Real.log (smoothHeathBrownSubgroupScaleProduct fs K) /
        Real.log (smoothHeathBrownScaleProduct fs) ≤ 1 / 4 := hJKparts.2
  have hJKblock :
      |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
        1 / 4 + η / 200 := by
    apply abs_le.mpr
    constructor <;> linarith [hJKlo, hJKhi, h₂err.1, h₂err.2,
      h₃err.1, h₃err.2, herrSmall]
  exact ⟨hIlo, hIhi, hJKblock⟩

#print axioms smoothHeathBrownThreeGroupBlockExponentBounds

end FractionalPrimes.Literature.DirichletAdapter

end
