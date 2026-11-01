module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupBlockExponentBounds
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
import Mathlib.Tactic

/-! The next scalar input after the block exponent display in
`lda:dp-from-muf`: a power/log threshold puts the block time interval in the
`ldm:uncapped` range and keeps the shifted frequency in the selected-group
range. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- Transfer the source upper time bound to the three-block product scale.
The same explicit `lu:elementary-growth` threshold also ensures the endpoint
condition needed to evaluate the selected-group estimate at `t-u`. -/
theorem smoothHeathBrownThreeGroupBlockTimeWindow
    {X η D W U Y T₀ t u : ℝ}
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hη : 0 < η) (hηsmall : η < 3 / 16)
    (hD : 0 ≤ D)
    (hW : W = (Real.log X) ^ D)
    (hWlower : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hYlower : X / (2 : ℝ) ^ 42 ≤ Y)
    (hlarge :
      (2 / (η / 2)) * Real.log
        ((2 : ℝ) ^ (42 * ((3 / 8 : ℝ) - η / 2)) *
          FractionalPrimes.Literature.Uniformity.logAbsorptionM
            (η / 2) (4 * D)) ≤ Real.log X)
    (hT₀ : T₀ = (Real.log X) ^ D / 2)
    (ht : W ≤ |t| ∧ |t| ≤ U)
    (hu : |u| ≤ W / 2) :
    (2 : ℝ) ^ 16 ≤ Y ∧ 2 ≤ U ∧
      U ≤ Y ^ ((3 / 8 : ℝ) - η / 2) ∧
      U + W / 2 ≤ X ∧
      T₀ ≤ |t - u| ∧ |t - u| ≤ X := by
  let e : ℝ := (3 / 8 : ℝ) - η / 2
  let α : ℝ := (3 / 8 : ℝ) - η
  let κ : ℝ := (2 : ℝ) ^ (42 * e)
  have hXone : 1 ≤ X := by
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := by norm_num
    exact le_trans hpow hXscale
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXone
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hepos : 0 < e := by
    dsimp [e]
    linarith [hηsmall]
  have hehalf : e ≤ (1 / 2 : ℝ) := by
    dsimp [e]
    linarith [hη]
  have hαpos : 0 ≤ α := by
    dsimp [α]
    linarith [hηsmall]
  have hκge : 1 ≤ κ := by
    dsimp [κ]
    exact Real.one_le_rpow (by norm_num) (by dsimp [e]; linarith [hηsmall])
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκge
  have hlarge' :
      (2 / (η / 2)) * Real.log
        (κ * FractionalPrimes.Literature.Uniformity.logAbsorptionM
          (η / 2) (4 * D)) ≤ Real.log X := by
    simpa [κ, e] using hlarge
  have hpoly :=
    FractionalPrimes.Literature.Uniformity.log_absorption_bound
      (a := η / 2) (b := 4 * D) (K := κ) (X := X)
      (by positivity) (by positivity) hκge hXone hlarge'
  have hW4 : W ^ (4 : ℕ) = (Real.log X) ^ (4 * D) := by
    calc
      W ^ (4 : ℕ) = ((Real.log X) ^ D) ^ (4 : ℝ) := by
        rw [hW]
        exact (Real.rpow_natCast ((Real.log X) ^ D) 4).symm
      _ = (Real.log X) ^ (D * 4) :=
        (Real.rpow_mul hlogXpos.le D 4).symm
      _ = (Real.log X) ^ (4 * D) := by congr 1; ring
  have hlogpow_nonneg : 0 ≤ (Real.log X) ^ (4 * D) :=
    Real.rpow_nonneg hlogXpos.le _
  have hlogpow_le : (Real.log X) ^ (4 * D) ≤ X ^ (η / 2) := by
    have hmul : (Real.log X) ^ (4 * D) ≤
        κ * (Real.log X) ^ (4 * D) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hκge) hlogpow_nonneg]
    exact le_trans hmul hpoly
  have hW4_le : W ^ (4 : ℕ) ≤ X ^ (η / 2) := by
    rw [hW4]
    exact hlogpow_le
  have hlogpow_div : (Real.log X) ^ (4 * D) ≤ X ^ (η / 2) / κ := by
    apply (le_div_iff₀ hκpos).2
    nlinarith [hpoly]
  have hκpow : ((2 : ℝ) ^ 42) ^ e = κ := by
    simpa [κ] using
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) 42 e).symm
  have hpowerprod : X ^ α * X ^ (η / 2) = X ^ e := by
    calc
      X ^ α * X ^ (η / 2) = X ^ (α + η / 2) :=
        (Real.rpow_add hXpos α (η / 2)).symm
      _ = X ^ e := by congr 1; dsimp [α, e]; ring
  have hscaledPower :
      X ^ α * (Real.log X) ^ (4 * D) ≤ (X / (2 : ℝ) ^ 42) ^ e := by
    calc
      X ^ α * (Real.log X) ^ (4 * D) ≤
          X ^ α * (X ^ (η / 2) / κ) :=
        mul_le_mul_of_nonneg_left hlogpow_div (Real.rpow_nonneg hXpos.le _)
      _ = X ^ e / κ := by
        calc
          X ^ α * (X ^ (η / 2) / κ) =
              (X ^ α * X ^ (η / 2)) / κ := by ring
          _ = X ^ e / κ := by rw [hpowerprod]
      _ = (X / (2 : ℝ) ^ 42) ^ e := by
        symm
        calc
          (X / (2 : ℝ) ^ 42) ^ e =
              X ^ e / ((2 : ℝ) ^ 42) ^ e :=
            Real.div_rpow hXpos.le (by positivity) e
          _ = X ^ e / κ := by rw [hκpow]
  have hYbase_nonneg : 0 ≤ X / (2 : ℝ) ^ 42 := by positivity
  have hYbase_le : X / (2 : ℝ) ^ 42 ≤ Y := hYlower
  have hYpow : (X / (2 : ℝ) ^ 42) ^ e ≤ Y ^ e :=
    Real.rpow_le_rpow hYbase_nonneg hYbase_le hepos.le
  have hUscale : U ≤ X ^ e := by
    calc
      U ≤ X ^ α * W ^ (4 : ℕ) := hU
      _ ≤ X ^ α * X ^ (η / 2) :=
        mul_le_mul_of_nonneg_left hW4_le (Real.rpow_nonneg hXpos.le _)
      _ = X ^ e := by
        rw [← Real.rpow_add hXpos]
        congr 1
        dsimp [α, e]
        ring
  have hUleY : U ≤ Y ^ e := by
    calc
      U ≤ X ^ α * W ^ (4 : ℕ) := hU
      _ = X ^ α * (Real.log X) ^ (4 * D) := by rw [hW4]
      _ ≤ (X / (2 : ℝ) ^ 42) ^ e := hscaledPower
      _ ≤ Y ^ e := hYpow
  have hWleW4 : W ≤ W ^ (4 : ℕ) := by
    have hWone : 1 ≤ W := by linarith
    have hWcube : 1 ≤ W ^ (3 : ℕ) := one_le_pow₀ hWone
    calc
      W = W * 1 := by ring
      _ ≤ W * W ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_left hWcube (by linarith : 0 ≤ W)
      _ = W ^ (4 : ℕ) := by ring
  have hWscale : W ≤ X ^ (η / 2) := le_trans hWleW4 hW4_le
  have hWsqrt : W ≤ Real.sqrt X := by
    calc
      W ≤ X ^ (η / 2) := hWscale
      _ ≤ X ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone (by linarith [hηsmall])
      _ = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
  have hUsqrt : U ≤ Real.sqrt X := by
    calc
      U ≤ X ^ e := hUscale
      _ ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hXone hehalf
      _ = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
  have hWhalf : W / 2 ≤ Real.sqrt X := by
    linarith [hWsqrt, hWlower]
  have hXge4 : 4 ≤ X := by
    have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ 200 := by norm_num
    exact le_trans hpow hXscale
  have hsqrtSquare : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt (by linarith)
  have hsqrtge2 : 2 ≤ Real.sqrt X := by nlinarith [hsqrtSquare]
  have hdoubleSqrt : 2 * Real.sqrt X ≤ X := by
    have hprod := mul_nonneg (sub_nonneg.mpr hsqrtge2) (Real.sqrt_nonneg X)
    nlinarith [hprod, hsqrtSquare]
  have hUplus : U + W / 2 ≤ X := by
    calc
      U + W / 2 ≤ Real.sqrt X + Real.sqrt X := add_le_add hUsqrt hWhalf
      _ = 2 * Real.sqrt X := by ring
      _ ≤ X := hdoubleSqrt
  have hYlarge : (2 : ℝ) ^ 16 ≤ Y := by
    have hX58 : (2 : ℝ) ^ 58 ≤ X := by
      have hpow : (2 : ℝ) ^ 58 ≤ (2 : ℝ) ^ 200 := by norm_num
      exact le_trans hpow hXscale
    have hlow : (2 : ℝ) ^ 16 ≤ X / (2 : ℝ) ^ 42 := by
      calc
        (2 : ℝ) ^ 16 = (2 : ℝ) ^ 58 / (2 : ℝ) ^ 42 := by norm_num
        _ ≤ X / (2 : ℝ) ^ 42 :=
          div_le_div_of_nonneg_right hX58 (by positivity)
    exact le_trans hlow hYlower
  have hT₀eqW : T₀ = W / 2 := by rw [hT₀, hW]
  have hShiftLow : W / 2 ≤ |t - u| := by
    have htriangle : |t| ≤ |t - u| + |u| := by
      calc
        |t| = |(t - u) + u| := by congr 1; ring
        _ ≤ |t - u| + |u| := abs_add_le _ _
    linarith [ht.1, hu, htriangle]
  have hShiftHigh : |t - u| ≤ X := by
    calc
      |t - u| ≤ |t| + |u| := by
        calc
          |t - u| = |t + (-u)| := by congr 1
          _ ≤ |t| + |-u| := abs_add_le _ _
          _ = |t| + |u| := by rw [abs_neg]
      _ ≤ U + W / 2 := add_le_add ht.2 hu
      _ ≤ X := hUplus
  refine ⟨hYlarge, le_trans hWlower hWU, ?_, hUplus, ?_, hShiftHigh⟩
  · simpa [e] using hUleY
  · rw [hT₀eqW]
    exact hShiftLow

#print axioms smoothHeathBrownThreeGroupBlockTimeWindow

end FractionalPrimes.Literature.DirichletAdapter

end
