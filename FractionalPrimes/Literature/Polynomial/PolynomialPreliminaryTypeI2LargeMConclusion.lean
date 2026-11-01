module

public import FractionalPrimes.Literature.Polynomial.PolynomialPreliminaryTypeI2LargeMRecurrenceStep

/-!
# Completed large-scale preliminary Type-I₂ coefficient conclusion

This module joins the checked common-denominator direction rectangle to the
finite coefficient descent.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Hyperbola
open FractionalPrimes.Literature.Uniformity

/-- Once the three source scale inequalities have been established, the
large-`M` weighted hyperbola correlation yields the exact preliminary
Type-I₂ monomial and binomial conclusions. -/
theorem preliminaryTypeI2LargeMFromGeometricData
    (g : HyperbolaGeometricData) (hgK₀ : g.K₀ = 2)
    (d : ℕ) (hd : 1 ≤ d)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (q₀ : ℕ) (hq₀ : 1 ≤ q₀)
    (hq₀bound : (q₀ : ℝ) ≤ δ⁻¹)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hlarge : δ * g.H ≤
      ‖∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension β₂ p.2 *
            unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖)
    (hLlarge : typeI2CapitalZ d δ⁻¹ < g.L0)
    (hscale36 : 36 < (typeI2T (δ⁻¹))⁻¹ * g.L0)
    (hscale : g.H / 16 ≤ g.L0 ^ 2 * (g.Q : ℝ) *
      (typeI2LargeMRecurrenceNTwo g.X g.M g.Q : ℝ)) :
    ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ typeI2J d δ⁻¹ ∧
      polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
          (Int.floor g.X) g.H ≤ typeI2J d δ⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        g.H ^ j * realDistanceToIntegers
          ((r : ℝ) *
            (phaseCenteredAt P (Int.floor g.X)).coeff j) ≤
          typeI2J d δ⁻¹ := by
  obtain ⟨S, v, hv, hvB, hdensity, hS, hdata⟩ :=
    preliminaryTypeI2LargeMDenseDirectionRectangle
      g hgK₀ d hd δ hδ hδle q₀ hq₀ hq₀bound β₁ β₂ hTV₁ hTV₂
      Λ hΛ P hP hlarge
  have hN₁ : 1 ≤ g.Q := Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne'
  have hXpos : 0 < g.X := lt_of_lt_of_le zero_lt_one g.X_ge_one
  have hMpos : 0 < g.M := lt_of_lt_of_le zero_lt_one g.M_ge_one
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hN₂ : 1 ≤ typeI2LargeMRecurrenceNTwo g.X g.M g.Q := by
    apply Nat.succ_le_iff.mpr
    dsimp [typeI2LargeMRecurrenceNTwo]
    apply Nat.ceil_pos.mpr
    have hEpos : 0 < (typeI2EValue : ℝ) := by
      norm_num [typeI2EValue, typeI2KZeroValue]
    exact mul_pos (mul_pos hEpos (div_pos hXpos (sq_pos_of_pos hMpos))) hQpos
  have hinverse : ∀ i ∈ S,
      ∃ D : TypeI2LargeMInverseProgressionData
        g d δ q₀ P i.2 i.1, D.v = v := by
    intro i hi
    rcases hdata i hi with
      ⟨_hcop, _hq, _hqhi, _ha, _hahi, _hτq, _hamlo, _hamhi, D, hDv⟩
    exact ⟨D, hDv⟩
  exact preliminaryTypeI2LargeM_coefficientConclusion
    hd hP hδ hδle hq₀ hq₀bound hv hvB hN₁ hN₂
    hLlarge hscale36 hscale S hS hdensity hinverse

/-- The complete preliminary scalar Type-I₂ inverse estimate, with the exact
short-length alternative and the source's `J_d` coefficient budget. -/
theorem preliminaryTypeI2Inverse
    (d : ℕ) (hd : 1 ≤ d)
    (X H M δ : ℝ) (J : Set ℝ)
    (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hroot : Real.rpow X (1 / 3 : ℝ) ≤ H) (hHX : H ≤ X)
    (hMhalf : (1 / 2 : ℝ) ≤ M)
    (hMupper : M ≤ 2 * Real.sqrt X)
    (hJconvex : Set.OrdConnected J)
    (hJsubset : J ⊆ Set.Ioc M (2 * M))
    (hδ : 0 < δ)
    (hδsmall : δ < min (1 / 2) ((Real.log X)⁻¹))
    (q₀ : ℕ) (hq₀ : 1 ≤ q₀)
    (hq₀bound : (q₀ : ℝ) ≤ δ⁻¹)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = hyperbolaLatticeSet X H J)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hlarge : δ * H ≤
      ‖∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension β₂ p.2 *
            unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖) :
    H ≤ typeI2J d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) ∨
      ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ typeI2J d δ⁻¹ ∧
        polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
            (Int.floor X) H ≤ typeI2J d δ⁻¹ ∧
        ∀ j, 1 ≤ j → j ≤ d →
          H ^ j * realDistanceToIntegers
            ((r : ℝ) *
              (phaseCenteredAt P (Int.floor X)).coeff j) ≤
            typeI2J d δ⁻¹ := by
  by_cases hlength :
      H ≤ typeI2J d δ⁻¹ * Real.rpow X (1 / 3 : ℝ)
  · exact Or.inl hlength
  · right
    have hlength' :
        typeI2J d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) < H :=
      lt_of_not_ge hlength
    by_cases hMsmall : M < 2 * Real.sqrt (Real.sqrt (H * X))
    · exact preliminaryTypeI2SmallMFromLattice
        d hd X H M δ J hX hH hHX hMhalf hδ hδsmall hMsmall
        hJsubset Λ hΛ β₁ β₂ q₀ (by omega) hq₀bound hTV₁ hTV₂
        P hP
        (fun p => unitFrequencyPhase
          (P.eval ((p.1 : ℝ) * (p.2 : ℝ))))
        (by intro p hp; rfl) (by simpa using hlarge) hlength'
    · have hMlarge : 2 * Real.sqrt (Real.sqrt (H * X)) ≤ M :=
        le_of_not_gt hMsmall
      have hδhalf : δ < 1 / 2 :=
        lt_of_lt_of_le hδsmall (min_le_left _ _)
      have hδle : δ ≤ 1 := by linarith
      have hx : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
      obtain ⟨g, hgK₀, hgX, hgH, hgM, hgJ, hgQ⟩ :=
        preliminaryTypeI2LargeMGeometricData_of_nonexception
          d δ⁻¹ X H M J hx (by linarith) hH hroot hHX hMupper
          hJconvex hJsubset hMlarge hlength'
      subst X
      subst H
      subst M
      subst J
      have hΛg : (Λ : Set (ℤ × ℤ)) = g.lattice := by
        simpa [HyperbolaGeometricData.lattice] using hΛ
      have hLlarge₀ := preliminaryTypeI2LargeM_scale_gt_capitalZ
        d δ⁻¹ g.X g.H g.M hx g.X_ge_one g.H_ge_one hMlarge hlength'
      rw [← hgQ] at hLlarge₀
      have hLlarge : typeI2CapitalZ d δ⁻¹ < g.L0 := by
        simpa [HyperbolaGeometricData.L0] using hLlarge₀
      have hscale36₀ :=
        preliminaryTypeI2LargeM_inverseT_mul_scale_gt_thirtySix
          d δ⁻¹ g.X g.H g.M (inv_pos.mpr hδ)
          g.X_ge_one g.H_ge_one hMlarge hlength'
      rw [← hgQ] at hscale36₀
      have hscale36 : 36 < (typeI2T δ⁻¹)⁻¹ * g.L0 := by
        simpa [HyperbolaGeometricData.L0] using hscale36₀
      have hscalePair :=
        preliminaryTypeI2LargeM_recurrenceScaleProduct_lower
          g.X g.H g.M g.X_ge_one g.H_ge_one hMlarge
      have hscale₀ := hscalePair.1.trans hscalePair.2
      rw [← hgQ] at hscale₀
      have hscale : g.H / 16 ≤ g.L0 ^ 2 * (g.Q : ℝ) *
          (typeI2LargeMRecurrenceNTwo g.X g.M g.Q : ℝ) := by
        simpa [HyperbolaGeometricData.L0,
          typeI2LargeMRecurrenceNOne] using hscale₀
      exact preliminaryTypeI2LargeMFromGeometricData
        g hgK₀ d hd δ hδ hδle q₀ hq₀ hq₀bound
        β₁ β₂ hTV₁ hTV₂ Λ hΛg P hP hlarge
        hLlarge hscale36 hscale

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeMFromGeometricData
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2Inverse

