module

public import FractionalPrimes.Literature.Harmonic.SquareFunctionL2Tonelli

/-! Assemble the source localized square estimate from the increment energy. -/

@[expose] public section

open scoped ENNReal BigOperators

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

noncomputable def localizedIncrementFamily
    (c : ℝ) (hc : 1 < c) (j : ℤ) (l : ℕ)
    (f : lp (fun _ : ℤ => ℂ) 2) (i : ℤ × Fin (2 ^ l)) :
    lp (fun _ : ℤ => ℂ) 2 :=
  localizedInterpolatedAverageL2 c
      (localizedDyadicLeftTime i.1 l i.2.val + localizedDyadicMesh i.1 l)
      (localizedDyadicRightTime_pos i.1 l i.2.val)
      (localizedSignedFrequencyProjectionL2 c hc (j + i.1) f) -
    localizedInterpolatedAverageL2 c
      (localizedDyadicLeftTime i.1 l i.2.val)
      (localizedDyadicLeftTime_pos i.1 l i.2.val)
      (localizedSignedFrequencyProjectionL2 c hc (j + i.1) f)

/-- The exact double-index component family is summable in squared
`ℓ²` norm, with the source localized-increment energy bound. -/
theorem localizedIncrementFamily_energy
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    Summable (fun i : ℤ × Fin (2 ^ l) =>
      ‖localizedIncrementFamily c hc j l f i‖ ^ 2) ∧
    (∑' i : ℤ × Fin (2 ^ l),
      ‖localizedIncrementFamily c hc j l f i‖ ^ 2) ≤
      (2 ^ l : ℝ) *
        (localizedUnweightedIncrementConstant c hc hcNon *
          min ((2 : ℝ) ^ (-(l : ℤ)))
            (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|))) ^ 2 *
          (frequencyProjectionFiniteSquareFunctionBound 2 * ‖f‖) ^ 2 := by
  classical
  let term : ℤ → Fin (2 ^ l) → ℝ := fun k m =>
    ‖localizedIncrementFamily c hc j l f (k, m)‖ ^ 2
  have hcount := localizedIncrementCountableMeshEnergyBound
    c hc hcNon j l f
  have houter : Summable (fun k : ℤ => ∑' m : Fin (2 ^ l), term k m) := by
    simpa [term, localizedIncrementFamily, tsum_fintype] using hcount.1
  have hproduct : Summable (fun i : ℤ × Fin (2 ^ l) => term i.1 i.2) := by
    apply (summable_prod_of_nonneg (fun i : ℤ × Fin (2 ^ l) => sq_nonneg _)).2
    exact ⟨fun k => Summable.of_finite, houter⟩
  have hbound : (∑' k : ℤ, ∑' m : Fin (2 ^ l), term k m) ≤
      (2 ^ l : ℝ) *
        (localizedUnweightedIncrementConstant c hc hcNon *
          min ((2 : ℝ) ^ (-(l : ℤ)))
            (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|))) ^ 2 *
          (frequencyProjectionFiniteSquareFunctionBound 2 * ‖f‖) ^ 2 := by
    simpa [term, localizedIncrementFamily, tsum_fintype] using hcount.2
  constructor
  · exact hproduct
  · calc
      (∑' i : ℤ × Fin (2 ^ l),
        ‖localizedIncrementFamily c hc j l f i‖ ^ 2) =
          ∑' k : ℤ, ∑' m : Fin (2 ^ l), term k m := by
            exact hproduct.tsum_prod
      _ ≤ _ := hbound

#print axioms localizedIncrementFamily_energy

/-- The paper's pointwise square function has an `ℓ²` representative
with the exact unnormalized energy estimate. -/
theorem localizedIncrementSquareFunction_memLp_energy
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    ∃ G : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ, G x = localizedUnweightedIncrementSquareFunction
        c hc hcNon j l f x) ∧
      ‖G‖ ^ 2 ≤
        (2 ^ l : ℝ) *
          (localizedUnweightedIncrementConstant c hc hcNon *
            min ((2 : ℝ) ^ (-(l : ℤ)))
              (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|))) ^ 2 *
            (frequencyProjectionFiniteSquareFunctionBound 2 * ‖f‖) ^ 2 := by
  let v := localizedIncrementFamily c hc j l f
  have hv := localizedIncrementFamily_energy c hc hcNon j l f
  obtain ⟨G, hGpoint, hGnorm⟩ := lpSquareFunction_norm_sq v hv.1
  refine ⟨G, ?_, ?_⟩
  · intro x
    rw [hGpoint x]
    rfl
  · rw [hGnorm]
    exact hv.2

#print axioms localizedIncrementSquareFunction_memLp_energy

/-- Exact dyadic rescaling of the minimum in the `ha:square` coefficient. -/
theorem localizedDyadicMin_rescale (l : ℕ) (a : ℝ) :
    min ((2 : ℝ) ^ (-(l : ℤ))) (Real.rpow 2 (-a)) =
      (2 : ℝ) ^ (-(l : ℤ)) *
        min 1 (Real.rpow 2 ((l : ℝ) - a)) := by
  let x : ℝ := (2 : ℝ) ^ (-(l : ℤ))
  let t : ℝ := Real.rpow 2 ((l : ℝ) - a)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hprod : x * t = Real.rpow 2 (-a) := by
    dsimp [x, t]
    rw [← Real.rpow_intCast (2 : ℝ) (-(l : ℤ))]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  calc
    min x (Real.rpow 2 (-a)) = min x (x * t) := by rw [hprod]
    _ = x * min 1 t := by
      rw [mul_min_of_nonneg 1 t hx]
      simp

#print axioms localizedDyadicMin_rescale

/-- Squaring the source dyadic square-root normalization. -/
theorem localizedDyadicScale_square (l : ℕ) :
    (2 ^ l : ℝ) * ((2 : ℝ) ^ (-(l : ℤ))) ^ 2 =
      (Real.rpow 2 (-(l : ℝ) / 2)) ^ 2 := by
  have hroot : (Real.rpow 2 (-(l : ℝ) / 2)) ^ 2 =
      ((2 : ℝ) ^ l)⁻¹ := by
    calc
      (Real.rpow 2 (-(l : ℝ) / 2)) ^ 2 =
          Real.rpow 2 ((-(l : ℝ) / 2) * 2) := by
            rw [← Real.rpow_natCast]
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
              (-(l : ℝ) / 2) 2).symm
      _ = Real.rpow 2 (-(l : ℝ)) := by congr 1; ring
      _ = ((2 : ℝ) ^ l)⁻¹ := by
        calc
          Real.rpow 2 (-(l : ℝ)) = (Real.rpow 2 (l : ℝ))⁻¹ :=
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (l : ℝ)
          _ = ((2 : ℝ) ^ l)⁻¹ := by
            rw [← Real.rpow_natCast (2 : ℝ) l]
            rfl
  rw [hroot]
  have hpow : (2 : ℝ) ^ (-(l : ℤ)) = ((2 : ℝ) ^ l)⁻¹ := by simp
  rw [hpow]
  have hne : (2 : ℝ) ^ l ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

#print axioms localizedDyadicScale_square

/-- The exact normalized localized square estimate in the approved
`ha:square` lemma. -/
theorem localizedSquareEstimate
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    ∃ G : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ, G x = localizedUnweightedIncrementSquareFunction
        c hc hcNon j l f x) ∧
      ‖G‖ ≤ Real.rpow 2 (-(l : ℝ) / 2) *
        localizedSquareCoefficient c hc hcNon j l * ‖f‖ := by
  obtain ⟨G, hGpoint, hGenergy⟩ :=
    localizedIncrementSquareFunction_memLp_energy c hc hcNon j l f
  let R : ℝ := Real.rpow 2 (-(l : ℝ) / 2)
  let D : ℝ := localizedUnweightedIncrementConstant c hc hcNon
  let L : ℝ := frequencyProjectionFiniteSquareFunctionBound 2
  let M : ℝ := min 1
    (Real.rpow 2 ((l : ℝ) - localizedIncrementSigma c * |(j : ℝ)|))
  have hD0 : 0 ≤ D := by
    dsimp [D, localizedUnweightedIncrementConstant]
    exact le_trans (by norm_num : 0 ≤ (4 : ℝ)) (le_max_left _ _)
  have hL0 : 0 ≤ L := by
    dsimp [L, frequencyProjectionFiniteSquareFunctionBound]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (frequencyProjectionSignedLpBound_nonneg (by norm_num))
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact le_min (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hB0 : 0 ≤ R * (D * L * M) * ‖f‖ := by positivity
  have hscale :
      (2 ^ l : ℝ) *
        (D * min ((2 : ℝ) ^ (-(l : ℤ)))
          (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|))) ^ 2 *
        (L * ‖f‖) ^ 2 =
          (R * (D * L * M) * ‖f‖) ^ 2 := by
    have hexp : -localizedIncrementSigma c * |(j : ℝ)| =
        -(localizedIncrementSigma c * |(j : ℝ)|) := by ring
    rw [hexp]
    rw [localizedDyadicMin_rescale l
      (localizedIncrementSigma c * |(j : ℝ)|)]
    change (2 ^ l : ℝ) *
      (D * ((2 : ℝ) ^ (-(l : ℤ)) * M)) ^ 2 *
        (L * ‖f‖) ^ 2 = (R * (D * L * M) * ‖f‖) ^ 2
    calc
      _ = ((2 ^ l : ℝ) * ((2 : ℝ) ^ (-(l : ℤ))) ^ 2) *
          (D * L * M * ‖f‖) ^ 2 := by ring
      _ = R ^ 2 * (D * L * M * ‖f‖) ^ 2 := by
        rw [localizedDyadicScale_square l]
      _ = _ := by ring
  have hBsquare : ‖G‖ ^ 2 ≤ (R * (D * L * M) * ‖f‖) ^ 2 := by
    calc
      ‖G‖ ^ 2 ≤ (2 ^ l : ℝ) *
          (D * min ((2 : ℝ) ^ (-(l : ℤ)))
            (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|))) ^ 2 *
          (L * ‖f‖) ^ 2 := hGenergy
      _ = _ := hscale
  refine ⟨G, hGpoint, ?_⟩
  change ‖G‖ ≤ R * (D * L * M) * ‖f‖
  nlinarith [norm_nonneg G]

#print axioms localizedSquareEstimate

end

end FractionalPrimes.Literature.Harmonic

namespace FractionalPrimes

open Literature.Harmonic

/-- The complete paper-facing `ha:square` estimate and coefficient
summability, with the exact dyadic normalization. -/
theorem localizedSquareSummability
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c) :
    (∀ (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2),
      ∃ G : lp (fun _ : ℤ => ℝ) 2,
        (∀ x : ℤ, G x = localizedUnweightedIncrementSquareFunction
          c hc hcNon j l f x) ∧
        ‖G‖ ≤ Real.rpow 2 (-(l : ℝ) / 2) *
          localizedSquareCoefficient c hc hcNon j l * ‖f‖) ∧
    (∀ (epsilon rho : ℝ), 0 < epsilon → epsilon < rho →
      Summable (fun z : ℕ × ℤ =>
        Real.rpow 2 (-epsilon * (z.1 : ℝ)) *
          (localizedSquareCoefficient c hc hcNon z.2 z.1) ^ rho)) := by
  constructor
  · intro j l f
    exact Literature.Harmonic.localizedSquareEstimate c hc hcNon j l f
  · intro epsilon rho hepsilon hepsilonRho
    exact Literature.Harmonic.localizedSquareCoefficient_summable
      c hc hcNon epsilon rho hepsilon hepsilonRho

#print axioms localizedSquareSummability

end FractionalPrimes

end
