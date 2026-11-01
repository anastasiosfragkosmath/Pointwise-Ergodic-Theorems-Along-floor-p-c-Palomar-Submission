module
public import FractionalPrimes.Final.ForwardOrbitCutoff
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory
open FractionalPrimes.Literature.Ergodic
open FractionalPrimes.Literature.Variation
open scoped ENNReal
noncomputable section

theorem aemeasurable_forwardKernelOperator {X : Type*} [MeasurableSpace X]
    (S : System X) (K : ℤ →₀ ℂ) (f : X → ℂ)
    (hf : AEStronglyMeasurable f S.μ) :
    AEMeasurable (forwardKernelOperator S K f) S.μ := by
  classical
  unfold forwardKernelOperator
  apply Finset.aemeasurable_fun_sum
  intro m hm
  exact ((hf.comp_measurePreserving (S.measurePreserving_iterate m.toNat)).const_mul (K m)).aemeasurable

theorem aemeasurable_forwardKernelVariation {I X : Type*} [LinearOrder I]
    [Countable I] [MeasurableSpace X] (S : System X) (r : ℝ)
    (K : I → ℤ →₀ ℂ) (f : X → ℂ) (hf : AEStronglyMeasurable f S.μ) :
    AEMeasurable (forwardKernelVariation S r K f) S.μ := by
  apply aemeasurable_orderedRVariationFun S.μ r
  intro i
  exact aemeasurable_forwardKernelOperator S (K i) f hf

theorem aemeasurable_comp_forwardIterate {X : Type*} [MeasurableSpace X]
    (S : System X) (n : ℕ) (F : X → ℝ≥0∞) (hF : AEMeasurable F S.μ) :
    AEMeasurable (fun x => F (S.T^[n] x)) S.μ := by
  have hp := S.measurePreserving_iterate n
  have hm : AEMeasurable F (S.μ.map S.T^[n]) := by rw [hp.map_eq]; exact hF
  exact hm.comp_measurable hp.measurable

theorem forwardOrbitCutoff_moment_eq_sum
    {X : Type*} [MeasurableSpace X] (S : System X)
    (f : X → ℂ) (N : ℕ) (x : X) (q : ℝ) (hq : 0 < q) :
    ∫⁻ j, ‖forwardOrbitCutoff S f N x j‖ₑ ^ q
        ∂(Measure.count : Measure ℤ) =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) 0,
        ‖f (S.T^[(-j).toNat] x)‖ₑ ^ q := by
  have hfun : (fun j : ℤ => ‖forwardOrbitCutoff S f N x j‖ₑ ^ q) =
      (Finset.Icc (-(N : ℤ)) 0 : Set ℤ).indicator
        (fun j => ‖f (S.T^[(-j).toNat] x)‖ₑ ^ q) := by
    funext j
    by_cases hj : j ∈ Finset.Icc (-(N : ℤ)) 0
    · have hjS : j ∈ (Finset.Icc (-(N : ℤ)) 0 : Set ℤ) := by simpa using hj
      rw [Set.indicator_of_mem hjS]
      simp [forwardOrbitCutoff, hj]
    · have hjS : j ∉ (Finset.Icc (-(N : ℤ)) 0 : Set ℤ) := by simpa using hj
      rw [Set.indicator_of_notMem hjS]
      simp [forwardOrbitCutoff, hj, hq]
  rw [hfun, lintegral_indicator_count_Icc_eq_sum]

/-- Pointwise moment domination on a finite central orbit segment, before
integrating over the system. -/
theorem forwardOrbitCutoff_central_moment_le
    {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (S : System X) (p r : ℝ≥0∞) (K : I → ℤ →₀ ℂ)
    (C : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hdisc : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p r K g ≤
        C * extendedLpNorm (Measure.count : Measure ℤ) p (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (R L : ℕ) (x : X)
    (hL : ∀ i m, m ∈ (K i).support → 0 ≤ m ∧ m ≤ (L : ℤ)) :
    ∑ j ∈ Finset.Icc (-(R : ℤ)) 0,
        forwardKernelVariation S r.toReal K f (S.T^[(-j).toNat] x) ^ p.toReal ≤
      C ^ p.toReal *
        ∑ j ∈ Finset.Icc (-((R + L : ℕ) : ℤ)) 0,
          ‖f (S.T^[(-j).toNat] x)‖ₑ ^ p.toReal := by
  let g := forwardOrbitCutoff S f (R + L) x
  have hg : (Function.support g).Finite := by
    simpa [g] using forwardOrbitCutoff_support_finite S f (R + L) x
  have hdiscMoment := finiteKernelDiscreteVariation_moment_le p r K C hp0 hptop
    g (hdisc g hg)
  have hpoint : ∀ j : ℤ,
      (Finset.Icc (-(R : ℤ)) 0 : Set ℤ).indicator
        (fun j => forwardKernelVariation S r.toReal K f
          (S.T^[(-j).toNat] x) ^ p.toReal) j ≤
        finiteKernelDiscreteVariation r.toReal K g j ^ p.toReal := by
    intro j
    by_cases hj : j ∈ Finset.Icc (-(R : ℤ)) 0
    · have hjS : j ∈ (Finset.Icc (-(R : ℤ)) 0 : Set ℤ) := by simpa using hj
      rw [Set.indicator_of_mem hjS]
      rw [← variation_forwardOrbitCutoff S r.toReal K f R L hL j hj x]
    · have hjS : j ∉ (Finset.Icc (-(R : ℤ)) 0 : Set ℤ) := by simpa using hj
      rw [Set.indicator_of_notMem hjS]
      exact bot_le
  have hcentral := MeasureTheory.lintegral_mono
    (μ := (Measure.count : Measure ℤ)) hpoint
  rw [lintegral_indicator_count_Icc_eq_sum] at hcentral
  calc
    _ ≤ ∫⁻ j, finiteKernelDiscreteVariation r.toReal K g j ^ p.toReal
          ∂(Measure.count : Measure ℤ) := hcentral
    _ ≤ C ^ p.toReal * ∫⁻ j, ‖g j‖ₑ ^ p.toReal
          ∂(Measure.count : Measure ℤ) := hdiscMoment
    _ = _ := by
      change C ^ p.toReal *
        (∫⁻ j, ‖forwardOrbitCutoff S f (R + L) x j‖ₑ ^ p.toReal
          ∂(Measure.count : Measure ℤ)) = _
      rw [forwardOrbitCutoff_moment_eq_sum S f (R + L) x p.toReal
        (ENNReal.toReal_pos hp0 hptop)]

/-- Integrating the finite central estimate transfers its two moment sums to
the system measure. -/
theorem forwardKernelVariation_moment_scaled
    {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (S : System X) (p r : ℝ≥0∞) (K : I → ℤ →₀ ℂ)
    (C : ℝ≥0∞) (hp1 : 1 ≤ p) (hpTop : p < ∞)
    (hdisc : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p r K g ≤
        C * extendedLpNorm (Measure.count : Measure ℤ) p (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (hf : AEStronglyMeasurable f S.μ) (R L : ℕ)
    (hL : ∀ i m, m ∈ (K i).support → 0 ≤ m ∧ m ≤ (L : ℤ)) :
    (Finset.Icc (-(R : ℤ)) 0).card *
        ∫⁻ x, forwardKernelVariation S r.toReal K f x ^ p.toReal ∂S.μ ≤
      C ^ p.toReal *
        ((Finset.Icc (-((R + L : ℕ) : ℤ)) 0).card *
          ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂S.μ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hptop : p ≠ ∞ := ne_of_lt hpTop
  let V := forwardKernelVariation S r.toReal K f
  let vMoment : X → ℝ≥0∞ := fun x => V x ^ p.toReal
  let fMoment : X → ℝ≥0∞ := fun x => ‖f x‖ₑ ^ p.toReal
  have hV : AEMeasurable V S.μ :=
    aemeasurable_forwardKernelVariation S r.toReal K f hf
  have hvMoment : AEMeasurable vMoment S.μ := by
    exact AEMeasurable.comp_aemeasurable
      (ENNReal.continuous_rpow_const (y := p.toReal)).measurable.aemeasurable
      (by simpa [vMoment] using hV)
  have hnorm : AEMeasurable (fun x => ‖f x‖ₑ) S.μ := hf.enorm
  have hfMoment : AEMeasurable fMoment S.μ := by
    exact AEMeasurable.comp_aemeasurable
      (ENNReal.continuous_rpow_const (y := p.toReal)).measurable.aemeasurable
      (by simpa [fMoment] using hnorm)
  let center := Finset.Icc (-(R : ℤ)) 0
  let outer := Finset.Icc (-((R + L : ℕ) : ℤ)) 0
  have hcenterComp : ∀ j ∈ center,
      AEMeasurable (fun x => vMoment (S.T^[(-j).toNat] x)) S.μ := by
    intro j hj
    exact aemeasurable_comp_forwardIterate S (-j).toNat vMoment hvMoment
  have houterComp : ∀ j ∈ outer,
      AEMeasurable (fun x => fMoment (S.T^[(-j).toNat] x)) S.μ := by
    intro j hj
    exact aemeasurable_comp_forwardIterate S (-j).toNat fMoment hfMoment
  have hcenterIntegral :
      ∫⁻ x, ∑ j ∈ center, vMoment (S.T^[(-j).toNat] x) ∂S.μ =
        (center.card : ℝ≥0∞) * ∫⁻ x, vMoment x ∂S.μ := by
    rw [MeasureTheory.lintegral_finsetSum' center hcenterComp]
    calc
      _ = ∑ j ∈ center, ∫⁻ x, vMoment x ∂S.μ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact lintegral_comp_forwardIterate S (-j).toNat vMoment hvMoment
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have houterIntegral :
      ∫⁻ x, ∑ j ∈ outer, fMoment (S.T^[(-j).toNat] x) ∂S.μ =
        (outer.card : ℝ≥0∞) * ∫⁻ x, fMoment x ∂S.μ := by
    rw [MeasureTheory.lintegral_finsetSum' outer houterComp]
    calc
      _ = ∑ j ∈ outer, ∫⁻ x, fMoment x ∂S.μ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact lintegral_comp_forwardIterate S (-j).toNat fMoment hfMoment
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hpoint : ∀ x,
      (∑ j ∈ center, vMoment (S.T^[(-j).toNat] x)) ≤
        C ^ p.toReal * ∑ j ∈ outer, fMoment (S.T^[(-j).toNat] x) := by
    intro x
    simpa [center, outer, V, vMoment, fMoment] using
      forwardOrbitCutoff_central_moment_le S p r K C hp0 hptop hdisc
        f R L x hL
  have hIntegral := MeasureTheory.lintegral_mono (μ := S.μ) hpoint
  rw [hcenterIntegral, MeasureTheory.lintegral_const_mul'' _
    (by
      have hs : AEMeasurable (fun x => ∑ j ∈ outer, fMoment (S.T^[(-j).toNat] x)) S.μ :=
        Finset.aemeasurable_fun_sum outer fun j hj => houterComp j hj
      exact hs)] at hIntegral
  rw [houterIntegral] at hIntegral
  simpa [center, outer, V, vMoment, fMoment, mul_assoc] using hIntegral


#print axioms forwardKernelVariation_moment_scaled
end
end FractionalPrimes.Final
