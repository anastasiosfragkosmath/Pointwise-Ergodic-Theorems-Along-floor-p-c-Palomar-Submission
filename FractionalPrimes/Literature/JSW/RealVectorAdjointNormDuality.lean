module

public import FractionalPrimes.Literature.JSW.RealAdjointNormDuality

/-!
# Real-linear vector-to-vector adjoint norm duality

The same finite-exponent pairing argument applies when both the domain
and range are complex Hilbert spaces.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace FractionalPrimes.Literature.JSW

noncomputable section

theorem lpRealVectorAdjointOperator_norm_eq
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
    ∀ (T : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ))
      (S : Lp H₂ (ENNReal.ofReal q) (volume : Measure ℝ) →L[ℝ]
        Lp H₁ (ENNReal.ofReal q) (volume : Measure ℝ)),
      (∀ f g,
        (∫ x, inner ℂ ((T f : Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ)) x)
            ((g : Lp H₂ (ENNReal.ofReal q) (volume : Measure ℝ)) x) ∂volume) =
          ∫ x, inner ℂ ((f : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ)) x)
            ((S g : Lp H₁ (ENNReal.ofReal q) (volume : Measure ℝ)) x) ∂volume) →
      ‖T‖ = ‖S‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
  intro T S hadj
  apply le_antisymm
  · apply T.opNorm_le_bound (norm_nonneg S)
    intro f₀
    have hnonempty :
        (lpElementDualPairingValues q (T f₀)).Nonempty := by
      refine ⟨0, 0, ?_, ?_⟩
      · change (eLpNorm ((0 : Lp H₂ (ENNReal.ofReal q) volume) : ℝ → H₂)
            (ENNReal.ofReal q) volume).toReal ≤ 1
        rw [← Lp.norm_def]
        simp
      · simp
    have hdual := lpNorm_eq_sSup_lpElementDualPairingValues hpq (T f₀)
    change ‖T f₀‖ ≤ ‖S‖ * ‖f₀‖
    rw [show ‖T f₀‖ =
        lpNorm (T f₀ : ℝ → H₂) (ENNReal.ofReal p) volume by rfl,
      hdual]
    apply csSup_le hnonempty
    rintro a ⟨g, hgOne, rfl⟩
    have hgOne' : ‖g‖ ≤ 1 := by exact hgOne
    have hholder := norm_integral_inner_le_lpNorm_mul_lpNorm hpq
      (Lp.memLp f₀) (Lp.memLp (S g))
    change ‖∫ x, inner ℂ ((f₀ : ℝ → H₁) x) ((S g : ℝ → H₁) x) ∂volume‖ ≤
      ‖f₀‖ * ‖S g‖ at hholder
    calc
      ‖∫ x, inner ℂ ((T f₀ : ℝ → H₂) x) ((g : ℝ → H₂) x) ∂volume‖ =
          ‖∫ x, inner ℂ ((f₀ : ℝ → H₁) x) ((S g : ℝ → H₁) x) ∂volume‖ :=
        congrArg norm (hadj f₀ g)
      _ ≤ ‖f₀‖ * ‖S g‖ := hholder
      _ ≤ ‖f₀‖ * (‖S‖ * ‖g‖) :=
        mul_le_mul_of_nonneg_left (S.le_opNorm g) (norm_nonneg f₀)
      _ ≤ ‖f₀‖ * (‖S‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgOne' (norm_nonneg S))
          (norm_nonneg f₀)
      _ = ‖S‖ * ‖f₀‖ := by ring
  · apply S.opNorm_le_bound (norm_nonneg T)
    intro g₀
    have hnonempty :
        (lpElementDualPairingValues p (S g₀)).Nonempty := by
      refine ⟨0, 0, ?_, ?_⟩
      · change (eLpNorm ((0 : Lp H₁ (ENNReal.ofReal p) volume) : ℝ → H₁)
            (ENNReal.ofReal p) volume).toReal ≤ 1
        rw [← Lp.norm_def]
        simp
      · simp
    have hdual := lpNorm_eq_sSup_lpElementDualPairingValues hpq.symm (S g₀)
    change ‖S g₀‖ ≤ ‖T‖ * ‖g₀‖
    rw [show ‖S g₀‖ =
        lpNorm (S g₀ : ℝ → H₁) (ENNReal.ofReal q) volume by rfl,
      hdual]
    apply csSup_le hnonempty
    rintro a ⟨f₀, hfOne, rfl⟩
    have hfOne' : ‖f₀‖ ≤ 1 := by exact hfOne
    have hconj :
        ‖∫ x, inner ℂ ((S g₀ : ℝ → H₁) x) ((f₀ : ℝ → H₁) x) ∂volume‖ =
          ‖∫ x, inner ℂ ((f₀ : ℝ → H₁) x) ((S g₀ : ℝ → H₁) x) ∂volume‖ := by
      have hint :
          (∫ x, inner ℂ ((S g₀ : ℝ → H₁) x) ((f₀ : ℝ → H₁) x) ∂volume) =
            conj (∫ x, inner ℂ ((f₀ : ℝ → H₁) x)
              ((S g₀ : ℝ → H₁) x) ∂volume) := by
        rw [← integral_conj]
        apply integral_congr_ae
        filter_upwards [] with x
        exact (inner_conj_symm _ _).symm
      rw [hint]
      exact RCLike.norm_conj _
    have hholder := norm_integral_inner_le_lpNorm_mul_lpNorm hpq
      (Lp.memLp (T f₀)) (Lp.memLp g₀)
    change ‖∫ x, inner ℂ ((T f₀ : ℝ → H₂) x) ((g₀ : ℝ → H₂) x) ∂volume‖ ≤
      ‖T f₀‖ * ‖g₀‖ at hholder
    calc
      ‖∫ x, inner ℂ ((S g₀ : ℝ → H₁) x) ((f₀ : ℝ → H₁) x) ∂volume‖ =
          ‖∫ x, inner ℂ ((f₀ : ℝ → H₁) x) ((S g₀ : ℝ → H₁) x) ∂volume‖ :=
        hconj
      _ = ‖∫ x, inner ℂ ((T f₀ : ℝ → H₂) x) ((g₀ : ℝ → H₂) x) ∂volume‖ :=
        congrArg norm (hadj f₀ g₀).symm
      _ ≤ ‖T f₀‖ * ‖g₀‖ := hholder
      _ ≤ (‖T‖ * ‖f₀‖) * ‖g₀‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm f₀) (norm_nonneg g₀)
      _ ≤ (‖T‖ * 1) * ‖g₀‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfOne' (norm_nonneg T))
          (norm_nonneg g₀)
      _ = ‖T‖ * ‖g₀‖ := by ring

/-- An upper bound for the vector adjoint transfers with the same constant
to the operator at the conjugate exponent. -/
theorem lpRealVectorAdjoint_bound_transfer
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {p q C : ℝ} (hpq : p.HolderConjugate q) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
    ∀ (T : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ))
      (S : Lp H₂ (ENNReal.ofReal q) (volume : Measure ℝ) →L[ℝ]
        Lp H₁ (ENNReal.ofReal q) (volume : Measure ℝ)),
      (∀ f g,
        (∫ x, inner ℂ ((T f : Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ)) x)
            ((g : Lp H₂ (ENNReal.ofReal q) (volume : Measure ℝ)) x) ∂volume) =
          ∫ x, inner ℂ ((f : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ)) x)
            ((S g : Lp H₁ (ENNReal.ofReal q) (volume : Measure ℝ)) x) ∂volume) →
      0 ≤ C → (∀ g, ‖S g‖ ≤ C * ‖g‖) → ∀ f, ‖T f‖ ≤ C * ‖f‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
  intro T S hAdj hC hS f
  have hnorm := lpRealVectorAdjointOperator_norm_eq hpq T S hAdj
  have hSNorm : ‖S‖ ≤ C := S.opNorm_le_bound hC hS
  calc
    ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
    _ = ‖S‖ * ‖f‖ := by rw [hnorm]
    _ ≤ C * ‖f‖ :=
      mul_le_mul_of_nonneg_right hSNorm (norm_nonneg f)

#print axioms lpRealVectorAdjointOperator_norm_eq
#print axioms lpRealVectorAdjoint_bound_transfer

end

end FractionalPrimes.Literature.JSW

end

