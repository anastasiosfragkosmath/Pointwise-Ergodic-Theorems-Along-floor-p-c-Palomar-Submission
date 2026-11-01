module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorPointwiseEnvelope
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorMeanScale

/-! The source component's pointwise Type-I envelope. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The source-normalized component, after the exact quadrature scale
threshold, has the blueprint's two-term pointwise envelope. -/
theorem smoothHeathBrownTypeISourceComponent_norm_le_powerEnvelope
    {X z : ℝ} (hX : 3 ≤ X) (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius i)
    (hcount : fs.length ≤ 20)
    (q a : ℕ) (hq : 0 < q) (t U η : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (htone : 1 ≤ |t|) (htU : |t| ≤ U)
    (hlog : fs.countP smoothHeathBrownTypeILogFactor ≤ 1)
    (c : ℝ) (hc : |c| ≤ (2 : ℝ) ^ 10)
    (hratio : (q : ℝ) * (1 + U) /
      smoothHeathBrownFactorScale (fs.get selected) ≤ X ^ (-(η / 4))) :
    ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖ ≤
      (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt (smoothHeathBrownScaleProduct fs)) *
        (Twisted.smoothDyadicC j *
          (|t| ^ (-(j : ℝ)) + X ^ (-(j : ℝ) * η / 4))) := by
  let N := smoothHeathBrownFactorScale (fs.get selected)
  let P := ∏ i : Fin fs.length, smoothHeathBrownFactorScale (fs.get i)
  have hN : 0 < N := smoothHeathBrownFactorScale_pos (fs.get selected)
  have hP : 0 ≤ P := by
    dsimp [P]
    apply Finset.prod_nonneg
    intro i _
    exact (smoothHeathBrownFactorScale_pos (fs.get i)).le
  have hU : 0 ≤ U := le_trans (abs_nonneg t) htU
  have hErr := smoothLongFactor_quadratureError_le_power
    X N U η t q j (by linarith) hN hU hq (by omega) htU hratio
  have htail :
      |t| ^ (-(j : ℝ)) +
        (q : ℝ) ^ (j - 1) * ((1 + |t|) / N) ^ j ≤
      |t| ^ (-(j : ℝ)) + X ^ (-(j : ℝ) * η / 4) :=
    by simpa [add_comm] using
      (add_le_add_left hErr (|t| ^ (-(j : ℝ))))
  have hbase := smoothHeathBrownTypeISourceFactorizedComponentSum_norm_le_coarse
    (z := z) hX fs selected hfree hcount q a hq t j hj htone hlog c hc
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hC : 0 ≤ Twisted.smoothDyadicC j := by
    unfold Twisted.smoothDyadicC
    positivity
  have hfront :
      0 ≤ (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt (P / N)) *
        (Twisted.smoothDyadicC j * Real.sqrt N) := by
    positivity
  calc
    ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖ ≤
      (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt (P / N)) *
        (Twisted.smoothDyadicC j * Real.sqrt N) *
        (|t| ^ (-(j : ℝ)) +
          (q : ℝ) ^ (j - 1) * ((1 + |t|) / N) ^ j) := by
      convert hbase using 1 <;> ring
    _ ≤ (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt (P / N)) *
        (Twisted.smoothDyadicC j * Real.sqrt N) *
        (|t| ^ (-(j : ℝ)) + X ^ (-(j : ℝ) * η / 4)) :=
      mul_le_mul_of_nonneg_left htail hfront
    _ = (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt (smoothHeathBrownScaleProduct fs)) *
        (Twisted.smoothDyadicC j *
          (|t| ^ (-(j : ℝ)) + X ^ (-(j : ℝ) * η / 4))) := by
      have hsqrt := smoothLongFactor_sqrt_ratio_mul_sqrt P N hP hN
      have hprod : P = smoothHeathBrownScaleProduct fs := by
        dsimp [P, smoothHeathBrownScaleProduct]
        rw [← List.prod_ofFn]
        congr 1
        simpa [List.get_eq_getElem] using
          (List.ofFn_getElem_eq_map fs smoothHeathBrownFactorScale).symm
      rw [← hprod]
      calc
        _ = (2 : ℝ) ^ 10 * (4 * Real.log X) *
            5 ^ 19 * (Real.sqrt (P / N) * Real.sqrt N) *
            (Twisted.smoothDyadicC j *
              (|t| ^ (-(j : ℝ)) + X ^ (-(j : ℝ) * η / 4))) := by ring
        _ = _ := by rw [hsqrt]; ring

#print axioms smoothHeathBrownTypeISourceComponent_norm_le_powerEnvelope

end FractionalPrimes.Literature.DirichletAdapter

end
