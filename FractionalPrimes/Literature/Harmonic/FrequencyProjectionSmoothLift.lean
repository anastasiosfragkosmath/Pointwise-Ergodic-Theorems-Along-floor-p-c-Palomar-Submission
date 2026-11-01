module

public import FractionalPrimes.Literature.Harmonic.FrequencyResolutionSquareFunction

/-!
# Smooth periodic lift of the frequency projections

The real representative is smooth and constant near both ends of its
half-open fundamental interval. This file verifies that its periodic
extension is smooth at the seam as well as inside each interval.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.Multiplier

noncomputable section

theorem frequencyProjectionPeriodicLift_eq_shift
    (c : ℝ) (h k : ℤ) {ξ : ℝ}
    (hξ : ξ - (k : ℝ) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :
    frequencyProjectionPeriodicLift c h ξ =
      (frequencyProjectionSymbolRepresentative c h (ξ - (k : ℝ)) : ℂ) := by
  unfold frequencyProjectionPeriodicLift
  have hmod :
      toIocMod (by norm_num : (0 : ℝ) < 1) (-(1 / 2 : ℝ)) ξ =
        ξ - (k : ℝ) := by
    apply (toIocMod_eq_iff (by norm_num : (0 : ℝ) < 1)).2
    constructor
    · simpa only [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by ring] using hξ
    · refine ⟨k, ?_⟩
      simp [zsmul_eq_mul]
  rw [hmod]

/-- On a neighborhood of every seam, the periodic lift is literally
constant. This is stronger than matching two derivatives at the seam. -/
private theorem frequencyProjectionPeriodicLift_eq_seamValue
    {c : ℝ} (hc : 1 < c) (h k : ℤ) {ξ : ℝ}
    (hξ : (k : ℝ) + 3 / 8 < ξ ∧ ξ < (k : ℝ) + 5 / 8) :
    frequencyProjectionPeriodicLift c h ξ =
      ((if h = 0 then 1 else 0 : ℝ) : ℂ) := by
  by_cases hside : ξ ≤ (k : ℝ) + 1 / 2
  · have hmem : ξ - (k : ℝ) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      constructor <;> linarith [hξ.1]
    rw [frequencyProjectionPeriodicLift_eq_shift c h k hmem]
    have habs : 3 / 8 < |ξ - (k : ℝ)| := by
      rw [abs_of_pos (by linarith [hξ.1])]
      linarith [hξ.1]
    rw [frequencyProjectionSymbolRepresentative_eq_seamValue hc h habs]
  · have hmem : ξ - ((k + 1 : ℤ) : ℝ) ∈
        Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      constructor <;> push_cast <;> linarith [hξ.2]
    rw [frequencyProjectionPeriodicLift_eq_shift c h (k + 1) hmem]
    have habs : 3 / 8 < |ξ - ((k + 1 : ℤ) : ℝ)| := by
      rw [abs_of_neg (by push_cast; linarith [hξ.2])]
      push_cast
      linarith [hξ.2]
    rw [frequencyProjectionSymbolRepresentative_eq_seamValue hc h habs]

/-- Every point has either an interior representative chart or a seam
neighborhood on which the projection lift is constant. -/
theorem frequencyProjectionPeriodicLift_contDiffAt
    {c : ℝ} (hc : 1 < c) (h : ℤ) (ξ : ℝ) :
    ContDiffAt ℝ 2 (frequencyProjectionPeriodicLift c h) ξ := by
  let k : ℤ := toIocDiv (by norm_num : (0 : ℝ) < 1) (-(1 / 2 : ℝ)) ξ
  let y : ℝ := toIocMod (by norm_num : (0 : ℝ) < 1) (-(1 / 2 : ℝ)) ξ
  have hy : y ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    have hy' := toIocMod_mem_Ioc
      (by norm_num : (0 : ℝ) < 1) (-(1 / 2 : ℝ)) ξ
    simpa only [y, show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by ring] using hy'
  have hxy : ξ - (k : ℝ) = y := by
    dsimp [k, y]
    simp [toIocMod, zsmul_eq_mul]
  rcases lt_or_eq_of_le hy.2 with hyInner | hySeam
  · let U : Set ℝ := {z | z - (k : ℝ) ∈
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)}
    have hUopen : IsOpen U :=
      isOpen_Ioo.preimage (continuous_id.sub continuous_const)
    have hξU : ξ ∈ U := by
      change ξ - (k : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
      rw [hxy]
      exact ⟨hy.1, hyInner⟩
    have hEv : frequencyProjectionPeriodicLift c h =ᶠ[nhds ξ]
        fun z => (frequencyProjectionSymbolRepresentative c h
          (z - (k : ℝ)) : ℂ) := by
      filter_upwards [hUopen.mem_nhds hξU] with z hz
      exact frequencyProjectionPeriodicLift_eq_shift c h k
        ⟨hz.1, hz.2.le⟩
    have hrep : ContDiff ℝ 2 (fun z : ℝ =>
        (frequencyProjectionSymbolRepresentative c h z : ℂ)) := by
      exact Complex.ofRealCLM.contDiff.comp
        ((frequencyProjectionSymbolRepresentative_contDiff c h).of_le (by norm_num))
    have hshift : ContDiff ℝ 2 (fun z : ℝ => z - (k : ℝ)) := by fun_prop
    exact (hrep.comp hshift).contDiffAt.congr_of_eventuallyEq hEv
  · have hξeq : ξ = (k : ℝ) + 1 / 2 := by linarith [hxy]
    let U : Set ℝ := Set.Ioo ((k : ℝ) + 3 / 8) ((k : ℝ) + 5 / 8)
    have hξU : ξ ∈ U := by
      dsimp [U]
      rw [hξeq]
      constructor <;> norm_num
    have hEv : frequencyProjectionPeriodicLift c h =ᶠ[nhds ξ]
        fun _ => ((if h = 0 then 1 else 0 : ℝ) : ℂ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hξU] with z hz
      exact frequencyProjectionPeriodicLift_eq_seamValue hc h k hz
    exact contDiffAt_const.congr_of_eventuallyEq hEv

/-- The exact smooth-lift hypothesis required by the periodic Mikhlin
adapter, including the seam. -/
theorem frequencyProjectionPeriodicLift_contDiffOn_punctured
    {c : ℝ} (hc : 1 < c) (h : ℤ) :
    ContDiffOn ℝ 2 (frequencyProjectionPeriodicLift c h)
      puncturedTorusLift := by
  intro ξ hξ
  exact (frequencyProjectionPeriodicLift_contDiffAt hc h ξ).contDiffWithinAt

/-- The first derivative of any one-periodic real lift is one-periodic. -/
theorem deriv_periodic_one (m : ℝ → ℂ) (hm : Function.Periodic m 1)
    (ξ : ℝ) : deriv m (ξ + 1) = deriv m ξ := by
  have hfun : (fun z : ℝ => m (z + 1)) = m := funext hm
  have hderiv := congrArg (fun f : ℝ → ℂ => deriv f ξ) hfun
  simpa only [deriv_comp_add_const] using hderiv

/-- The second iterated derivative of any one-periodic real lift is
one-periodic. -/
theorem iteratedDeriv_two_periodic_one (m : ℝ → ℂ)
    (hm : Function.Periodic m 1) (ξ : ℝ) :
    iteratedDeriv 2 m (ξ + 1) = iteratedDeriv 2 m ξ := by
  have hfun : (fun z : ℝ => m (z + 1)) = m := funext hm
  have hderiv := congrArg (fun f : ℝ → ℂ => iteratedDeriv 2 f ξ) hfun
  simpa only [iteratedDeriv_comp_add_const] using hderiv

end

end FractionalPrimes.Literature.Harmonic

end
