module

public import FractionalPrimes.Literature.Polynomial.PolynomialDirichletMeanEnvelope

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open MeasureTheory
open scoped BigOperators

/-- The source envelope written directly for its finite Mellin polynomial.
This form is useful for source components, which share an outer-window
parameter range but do not individually come from the original arithmetic
coefficient family. -/
noncomputable def dirichletMeanEnvelopeOfA_X
    (A : ℝ → ℂ) (T0 W : ℝ) : ℝ :=
  sSup ((fun U : ℝ => (T0 / U) *
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U}, ‖A t‖)) ''
      Set.Icc T0 (T0 * W ^ 4))

/-- The source Mellin-window envelope depends only on the `A_X` field. -/
theorem dirichletMeanEnvelope_eq_ofA_X
    (w : MellinWindowData) (T0 W : ℝ) :
    dirichletMeanEnvelope w T0 W =
      dirichletMeanEnvelopeOfA_X w.A_X T0 W := rfl

/-- The source mean envelope is subadditive under an exact finite expansion
of its Mellin polynomial.  This is the envelope-level component accumulation
step: all component data use the same `T0`, `W`, and closed endpoint range. -/
theorem dirichletMeanEnvelope_le_sum_of_finite_A_X_expansion
    {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (w : MellinWindowData) (components : ι → MellinWindowData)
    (hA : ∀ t : ℝ, w.A_X t = ∑ i ∈ J, (components i).A_X t)
    (hAcont : Continuous w.A_X)
    (hComponentsCont : ∀ i, Continuous (components i).A_X)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelope w T0 W ≤
      ∑ i ∈ J, dirichletMeanEnvelope (components i) T0 W := by
  classical
  obtain ⟨V, hV, hEq, hmax⟩ :=
    dirichletMeanEnvelope_hasMaximum w hAcont hW hWT
  let E : Set ℝ := {t : ℝ | W ≤ |t| ∧ |t| ≤ V}
  have hEmeas : MeasurableSet E := by
    have hleft : MeasurableSet {t : ℝ | W ≤ |t|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    have hright : MeasurableSet {t : ℝ | |t| ≤ V} :=
      measurableSet_le continuous_abs.measurable measurable_const
    change MeasurableSet
      ({t : ℝ | W ≤ |t|} ∩ {t : ℝ | |t| ≤ V})
    exact hleft.inter hright
  have hEclosed : IsClosed E := by
    change IsClosed ((fun t : ℝ => |t|) ⁻¹' Set.Icc W V)
    exact isClosed_Icc.preimage continuous_abs
  have hEsubset : E ⊆ Set.Icc (-V) V := by
    intro t ht
    exact abs_le.mp ht.2
  have hEcompact : IsCompact E :=
    isCompact_Icc.of_isClosed_subset hEclosed hEsubset
  have hLeftInt : IntegrableOn (fun t : ℝ => ‖w.A_X t‖) E :=
    (continuous_norm.comp hAcont).continuousOn.integrableOn_compact hEcompact
  have hComponentInt (i : ι) :
      IntegrableOn (fun t : ℝ => ‖(components i).A_X t‖) E :=
    (continuous_norm.comp (hComponentsCont i)).continuousOn.integrableOn_compact
      hEcompact
  have hRightInt : IntegrableOn
      (fun t : ℝ => ∑ i ∈ J, ‖(components i).A_X t‖) E := by
    apply integrable_finsetSum J
    intro i hi
    exact hComponentInt i
  have hnorm (t : ℝ) :
      ‖w.A_X t‖ ≤ ∑ i ∈ J, ‖(components i).A_X t‖ := by
    rw [hA t]
    exact norm_sum_le _ _
  have htailE :
      (∫ t in E, ‖w.A_X t‖) ≤
        ∑ i ∈ J, ∫ t in E, ‖(components i).A_X t‖ := by
    calc
      (∫ t in E, ‖w.A_X t‖) ≤
          ∫ t in E, ∑ i ∈ J, ‖(components i).A_X t‖ :=
        setIntegral_mono_on hLeftInt hRightInt hEmeas (by
          intro t ht
          exact hnorm t)
      _ = ∑ i ∈ J, ∫ t in E, ‖(components i).A_X t‖ := by
        rw [integral_finsetSum]
        intro i hi
        exact hComponentInt i
  have htail : dirichletAbsoluteTailIntegral w W V ≤
      ∑ i ∈ J, dirichletAbsoluteTailIntegral (components i) W V := by
    simpa [dirichletAbsoluteTailIntegral, E] using htailE
  have hVpos : 0 < V := by
    have hWpos : 0 < W := by linarith
    exact lt_of_lt_of_le hWpos (le_trans hWT hV.1)
  have hobjective : dirichletMeanEnvelopeObjective w T0 W V ≤
      ∑ i ∈ J, dirichletMeanEnvelope (components i) T0 W := by
    have hscale : 0 ≤ T0 / V :=
      div_nonneg (le_trans (by linarith : 0 ≤ W) hWT) hVpos.le
    calc
      dirichletMeanEnvelopeObjective w T0 W V =
          (T0 / V) * dirichletAbsoluteTailIntegral w W V := rfl
      _ ≤ (T0 / V) *
          (∑ i ∈ J,
            dirichletAbsoluteTailIntegral (components i) W V) :=
        mul_le_mul_of_nonneg_left htail hscale
      _ = ∑ i ∈ J,
          dirichletMeanEnvelopeObjective (components i) T0 W V := by
        rw [Finset.mul_sum]
        rfl
      _ ≤ ∑ i ∈ J, dirichletMeanEnvelope (components i) T0 W := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨_, _, _, hComponentMax⟩ :=
          dirichletMeanEnvelope_hasMaximum (components i)
            (hComponentsCont i) hW hWT
        exact hComponentMax V hV
  calc
    dirichletMeanEnvelope w T0 W =
        dirichletMeanEnvelopeObjective w T0 W V := hEq.symm
    _ ≤ ∑ i ∈ J, dirichletMeanEnvelope (components i) T0 W := hobjective

/-- Function-level version of finite envelope subadditivity. The component
polynomials may be arbitrary continuous Mellin polynomials; the common
source window metadata is supplied by `w`. -/
theorem dirichletMeanEnvelopeOfA_X_le_sum_of_finite_expansion
    {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (w : MellinWindowData) (components : ι → ℝ → ℂ)
    (hA : ∀ t : ℝ, w.A_X t = ∑ i ∈ J, components i t)
    (hAcont : Continuous w.A_X)
    (hComponentsCont : ∀ i, Continuous (components i))
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelopeOfA_X w.A_X T0 W ≤
      ∑ i ∈ J, dirichletMeanEnvelopeOfA_X (components i) T0 W := by
  let componentData : ι → MellinWindowData := fun i =>
    { w with A_X := components i }
  have hsum : ∀ t : ℝ,
      w.A_X t = ∑ i ∈ J, (componentData i).A_X t := by
    intro t
    simpa [componentData] using hA t
  have hcomponents : ∀ i, Continuous (componentData i).A_X := by
    intro i
    exact hComponentsCont i
  have hbound := dirichletMeanEnvelope_le_sum_of_finite_A_X_expansion
    J w componentData hsum hAcont hcomponents hW hWT
  simpa [dirichletMeanEnvelope_eq_ofA_X, componentData] using hbound

#print axioms dirichletMeanEnvelope_le_sum_of_finite_A_X_expansion
#print axioms dirichletMeanEnvelopeOfA_X_le_sum_of_finite_expansion

end FractionalPrimes.Literature.Polynomial

end
