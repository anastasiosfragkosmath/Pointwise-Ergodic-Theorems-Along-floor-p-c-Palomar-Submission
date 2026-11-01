module

public import FractionalPrimes.Literature.MSZ.LocalizedInterpolation

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped BigOperators ENNReal

/-! Bridges between the real-valued square-function witnesses in the
approved MSZ data and the extended-valued square function used by the
localized interpolation endpoint. -/

/-- Under pointwise square summability, the real square function and the
extended-valued square function have exactly the same `ENNReal` value. -/
theorem localInterpolation_realSquare_eq_extendedSquare
    (a : ℤ → ℤ → ℂ) (x : ℤ)
    (hsummable : Summable (fun h : ℤ => ‖a x h‖ ^ 2)) :
    ENNReal.ofReal (Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2)) =
      localInterpolationExtendedSquareFunction a x := by
  have hsum :
      (∑' h : ℤ, ENNReal.ofReal (‖a x h‖ ^ 2)) =
        ENNReal.ofReal (∑' h : ℤ, ‖a x h‖ ^ 2) :=
    (ENNReal.ofReal_tsum_of_nonneg
      (fun h => sq_nonneg (‖a x h‖)) hsummable).symm
  have htsumNonneg : 0 ≤ ∑' h : ℤ, ‖a x h‖ ^ 2 :=
    tsum_nonneg fun h => sq_nonneg (‖a x h‖)
  change ENNReal.ofReal (Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2)) =
    (∑' h : ℤ, ENNReal.ofReal (‖a x h‖ ^ 2)) ^ (1 / 2 : ℝ)
  rw [hsum,
    ENNReal.ofReal_rpow_of_nonneg htsumNonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)),
    ← Real.sqrt_eq_rpow]

/-- Convert a full-domain real square-function witness into the exact
extended-valued witness required by `localizedInterpolation`. The summability
hypothesis identifies its real square function with the extended definition;
the exponent and operator norm bound are unchanged. -/
theorem localInterpolation_realSquareWitness_to_extended
    {p P : ℝ} (S : ℤ → ((ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ)))
    (hSummable : ∀ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ∀ x : ℤ, Summable (fun h : ℤ => ‖S h (F : ℤ → ℂ) x‖ ^ 2))
    (hSquare : ∀ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ∃ G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
        (∀ x : ℤ, G x = Real.sqrt
          (∑' h : ℤ, ‖S h (F : ℤ → ℂ) x‖ ^ 2)) ∧
        ‖G‖ ≤ P * ‖F‖) :
    ∀ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ∃ G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
        (∀ x, 0 ≤ G x) ∧
        (∀ x, ENNReal.ofReal (G x) =
          localInterpolationExtendedSquareFunction
            (fun x h => S h (F : ℤ → ℂ) x) x) ∧
        ‖G‖ ≤ P * ‖F‖ := by
  intro F
  obtain ⟨G, hG, hGnorm⟩ := hSquare F
  refine ⟨G, ?_, ?_⟩
  · intro x
    rw [hG x]
    exact Real.sqrt_nonneg _
  · constructor
    · intro x
      calc
        ENNReal.ofReal (G x) =
            ENNReal.ofReal (Real.sqrt
              (∑' h : ℤ, ‖S h (F : ℤ → ℂ) x‖ ^ 2)) :=
          congrArg ENNReal.ofReal (hG x)
        _ = localInterpolationExtendedSquareFunction
            (fun x h => S h (F : ℤ → ℂ) x) x :=
          localInterpolation_realSquare_eq_extendedSquare
            (fun x h => S h (F : ℤ → ℂ) x) x (hSummable F x)
    · exact hGnorm

end FractionalPrimes.Literature.MSZ

end
