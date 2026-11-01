module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorFrequencyContinuity
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorFrequencyDomain
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorScaleThreshold
public import Mathlib.Tactic

/-! Continuous integration and final power bookkeeping for `lda:type-i`. -/

@[expose] public section

open MeasureTheory intervalIntegral

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The exact two-tail envelope is bounded by the two powers appearing in
the approved Type-I conclusion once `U≤X`. -/
theorem smoothLongFactor_twoTailEnvelope_le_finalPowers
    (X W U η C : ℝ) (j : ℕ)
    (hX : 0 < X) (hW : 0 < W) (hWU : W ≤ U)
    (hUX : U ≤ X) (hC : 0 ≤ C) (hj : 2 ≤ j) :
    C * (2 * (W ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) +
      2 * U * X ^ (-(j : ℝ) * η / 4)) ≤
      2 * C * (W ^ (1 - (j : ℝ)) +
        X ^ (1 - (j : ℝ) * η / 4)) := by
  have hjreal : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hden : 1 ≤ (j : ℝ) - 1 := by linarith
  have hWpow : 0 ≤ W ^ (1 - (j : ℝ)) := by positivity
  have hXpow : 0 ≤ X ^ (-(j : ℝ) * η / 4) := by positivity
  have htail : W ^ (1 - (j : ℝ)) / ((j : ℝ) - 1) ≤
      W ^ (1 - (j : ℝ)) := by
    exact (div_le_self hWpow hden)
  have hUterm : U * X ^ (-(j : ℝ) * η / 4) ≤
      X ^ (1 - (j : ℝ) * η / 4) := by
    have hpow : X * X ^ (-(j : ℝ) * η / 4) =
        X ^ (1 - (j : ℝ) * η / 4) := by
      calc
        X * X ^ (-(j : ℝ) * η / 4) =
            X ^ (1 : ℝ) * X ^ (-(j : ℝ) * η / 4) := by simp
        _ = X ^ ((1 : ℝ) + (-(j : ℝ) * η / 4)) := by
          rw [Real.rpow_add hX]
        _ = X ^ (1 - (j : ℝ) * η / 4) := by congr 1; ring
    rw [← hpow]
    exact mul_le_mul_of_nonneg_right hUX hXpow
  have hsum :
      2 * (W ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) +
          2 * U * X ^ (-(j : ℝ) * η / 4) ≤
        2 * (W ^ (1 - (j : ℝ)) +
          X ^ (1 - (j : ℝ) * η / 4)) := by
    nlinarith [htail, hUterm]
  calc
    _ ≤ C * (2 * (W ^ (1 - (j : ℝ)) +
        X ^ (1 - (j : ℝ) * η / 4))) :=
      mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by ring

/-- The exact source component is now integrated over the paper's
two-sided frequency domain. The scale-ratio and `U≤X` inputs are supplied
by the blueprint's large-`X` threshold in the next specialization. -/
theorem smoothHeathBrownTypeISourceComponent_mean_le_powerEnvelope
    {X z : ℝ} (hX : 3 ≤ X) (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius i)
    (hcount : fs.length ≤ 20)
    (q a : ℕ) (hq : 0 < q) (W U η : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (hW : 2 ≤ W) (hWU : W ≤ U) (hUX : U ≤ X)
    (hlog : fs.countP smoothHeathBrownTypeILogFactor ≤ 1)
    (c : ℝ) (hc : |c| ≤ (2 : ℝ) ^ 10)
    (hratio : (q : ℝ) * (1 + U) /
      smoothHeathBrownFactorScale (fs.get selected) ≤ X ^ (-(η / 4))) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖) ≤
      2 * ((2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt (smoothHeathBrownScaleProduct fs)) *
        Twisted.smoothDyadicC j) *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  let C : ℝ := (2 : ℝ) ^ 10 * (4 * Real.log X) *
    (5 ^ 19 * Real.sqrt (smoothHeathBrownScaleProduct fs)) *
      Twisted.smoothDyadicC j
  let δ : ℝ := X ^ (-(j : ℝ) * η / 4)
  have hC : 0 ≤ C := by
    dsimp [C, Twisted.smoothDyadicC]
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hWpos : 0 < W := by linarith
  have hfneg : IntervalIntegrable (fun t : ℝ =>
      ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖) volume (-U) (-W) :=
    smoothHeathBrownTypeISourceFactorizedComponentSum_norm_intervalIntegrable
      fs selected q a c (-U) (-W)
  have hfpos : IntervalIntegrable (fun t : ℝ =>
      ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖) volume W U :=
    smoothHeathBrownTypeISourceFactorizedComponentSum_norm_intervalIntegrable
      fs selected q a c W U
  have hbound (t : ℝ) (htW : W ≤ |t|) (htU : |t| ≤ U) :
      ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖ ≤
        C * (|t| ^ (-(j : ℝ)) + δ) := by
    have htone : 1 ≤ |t| := by linarith
    have hpoint := smoothHeathBrownTypeISourceComponent_norm_le_powerEnvelope
      (z := z) hX fs selected hfree hcount q a hq t U η j hj
      htone htU hlog c hc hratio
    convert hpoint using 1 <;> ring
  have hmean := smoothLongFactor_frequencyDomain_integral_le_envelope
    W U δ C j hWpos hWU hδ hC hj
    (fun t : ℝ => ‖smoothHeathBrownTypeISourceFactorizedComponentSum
      (z := z) fs selected q a t c‖) hfneg hfpos hbound
  have hfinal := smoothLongFactor_twoTailEnvelope_le_finalPowers
    X W U η C j (by linarith) hWpos hWU hUX hC hj
  exact hmean.trans hfinal

/-- Insert the retained support window and the explicit large-`X`
logarithmic threshold into the integrated Type-I component estimate. -/
theorem smoothHeathBrownRetainedTypeISourceComponent_mean_le
    {X z : ℝ} (hX : 3 ≤ X) (hXexp : Real.exp 1 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius i)
    (hcount : fs.length ≤ 20)
    (hret : smoothHeathBrownSupportRetained (X := X) (z := z) fs)
    (hlong : (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected))
    (q a : ℕ) (hqpos : 0 < q) (W U η B D : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hj : 2 ≤ j) (hWdef : W = (Real.log X) ^ D)
    (hW : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hq : (q : ℝ) ≤ (Real.log X) ^ B)
    (hlarge :
      (2 / (3 * η / 4)) * Real.log
        ((2 : ℝ) ^ (23 : ℕ) *
          Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D)) ≤ Real.log X)
    (hlog : fs.countP smoothHeathBrownTypeILogFactor ≤ 1)
    (c : ℝ) (hc : |c| ≤ (2 : ℝ) ^ 10) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖) ≤
      2 * ((2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt (smoothHeathBrownScaleProduct fs)) *
        Twisted.smoothDyadicC j) *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  have hscale := smoothHeathBrownSupportRetained_selectedTypeIScaleBounds
    (z := z) (by linarith : 0 ≤ X) fs selected hcount hret hlong
  have hUone : 1 ≤ U := by linarith
  have hratio := smoothLongFactor_scale_ratio_le_power
    X W U (smoothHeathBrownFactorScale (fs.get selected)) η B D q
    hX hη hB hD hWdef hUone hU hscale.1 hq hlarge
  have hUX := smoothLongFactor_frequency_upper_le_X_of_threshold
    X W U η B D hX hXexp hη hB hD hWdef hU hlarge
  exact smoothHeathBrownTypeISourceComponent_mean_le_powerEnvelope
    (z := z) hX fs selected hfree hcount q a hqpos W U η j
    hj hW hWU hUX hlog c hc hratio

/-- The blueprint's advertised `K_j` dominates every source scalar and
the factor-count/scale losses in the integrated Type-I component. -/
theorem smoothLongFactor_sourceCoefficient_le_advertisedConstant
    (X P S Cj : ℝ) (hX : 3 ≤ X)
    (hP : Real.sqrt P ≤ (2 : ℝ) ^ 11 * Real.sqrt X)
    (hS : 0 ≤ S) (hCj : 0 ≤ Cj) :
    2 * ((2 : ℝ) ^ 10 * (4 * Real.log X) *
      (5 ^ 19 * Real.sqrt P) * Cj) * S ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * Cj) * Real.sqrt X *
        Real.log X * S := by
  have hlog : 0 ≤ Real.log X := (Real.log_pos (by linarith)).le
  have hnum : (2 : ℝ) ^ 24 * 5 ^ 19 ≤ (2 : ℝ) ^ 40 * 5 ^ 20 := by
    norm_num
  calc
    2 * ((2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt P) * Cj) * S ≤
      2 * ((2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * ((2 : ℝ) ^ 11 * Real.sqrt X)) * Cj) * S := by
      gcongr
    _ = ((2 : ℝ) ^ 24 * 5 ^ 19) * Cj * Real.sqrt X *
        Real.log X * S := by ring
    _ ≤ ((2 : ℝ) ^ 40 * 5 ^ 20) * Cj * Real.sqrt X *
        Real.log X * S := by
      gcongr
    _ = _ := by ring

/-- The exact advertised Type-I constant for a retained, factorized
smooth Heath--Brown component. Identification with the original
convolution-coefficient sum is handled separately. -/
theorem smoothHeathBrownRetainedTypeISourceComponent_mean_le_K
    {X z : ℝ} (hX : 3 ≤ X) (hXexp : Real.exp 1 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius i)
    (hcount : fs.length ≤ 20)
    (hret : smoothHeathBrownSupportRetained (X := X) (z := z) fs)
    (hlong : (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected))
    (q a : ℕ) (hqpos : 0 < q) (W U η B D : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hj : 2 ≤ j) (hWdef : W = (Real.log X) ^ D)
    (hW : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hq : (q : ℝ) ≤ (Real.log X) ^ B)
    (hlarge :
      (2 / (3 * η / 4)) * Real.log
        ((2 : ℝ) ^ (23 : ℕ) *
          Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D)) ≤ Real.log X)
    (hlog : fs.countP smoothHeathBrownTypeILogFactor ≤ 1)
    (c : ℝ) (hc : |c| ≤ (2 : ℝ) ^ 10) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖) ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) *
        Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  have hscale := smoothHeathBrownSupportRetained_selectedTypeIScaleBounds
    (z := z) (by linarith : 0 ≤ X) fs selected hcount hret hlong
  have hmean := smoothHeathBrownRetainedTypeISourceComponent_mean_le
    hX hXexp fs selected hfree hcount hret hlong q a hqpos W U η B D j
    hη hB hD hj hWdef hW hWU hU hq hlarge hlog c hc
  have hS : 0 ≤ W ^ (1 - (j : ℝ)) +
      X ^ (1 - (j : ℝ) * η / 4) := by positivity
  have hCj : 0 ≤ Twisted.smoothDyadicC j := by
    unfold Twisted.smoothDyadicC
    positivity
  exact hmean.trans (smoothLongFactor_sourceCoefficient_le_advertisedConstant
    X (smoothHeathBrownScaleProduct fs)
    (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4))
    (Twisted.smoothDyadicC j) hX hscale.2 hS hCj)

#print axioms smoothLongFactor_twoTailEnvelope_le_finalPowers
#print axioms smoothHeathBrownTypeISourceComponent_mean_le_powerEnvelope
#print axioms smoothHeathBrownRetainedTypeISourceComponent_mean_le
#print axioms smoothLongFactor_sourceCoefficient_le_advertisedConstant
#print axioms smoothHeathBrownRetainedTypeISourceComponent_mean_le_K

end FractionalPrimes.Literature.DirichletAdapter

end
