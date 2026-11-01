module

public import FractionalPrimes.Literature.Twisted.SmoothDyadicCutoff
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Joint parameter regularity of smooth dyadic profiles

The fixed-parameter profile is in `SmoothDyadicCutoff`. This file exposes its
parameter dependence so compactness can be applied to the exact profile norms.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

open MeasureTheory
open FractionalPrimes.Literature.Polynomial
open scoped ContDiff Topology

/-- The profile viewed jointly in its three real parameters and its real input. -/
def smoothDyadicHJoint (x : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  if 0 < x.2 then
    smoothDyadicTheta x.2 * polynomialOuterCutoff (x.1.1 * x.2) *
      (x.1.2.1 + x.1.2.2 * Real.log x.2)
  else 0

theorem smoothDyadicHJoint_eq (v a b u : ℝ) :
    smoothDyadicHJoint ((v, a, b), u) = smoothDyadicH v a b u := rfl

theorem smoothDyadicHJoint_contDiff :
    ContDiff ℝ ∞ smoothDyadicHJoint := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x.2
  · let F : (ℝ × ℝ × ℝ) × ℝ → ℝ := fun y =>
      smoothDyadicTheta y.2 * polynomialOuterCutoff (y.1.1 * y.2) *
        (y.1.2.1 + y.1.2.2 * Real.log y.2)
    have htheta : ContDiffAt ℝ ∞ (fun y : (ℝ × ℝ × ℝ) × ℝ =>
        smoothDyadicTheta y.2) x := by
      exact ContDiffAt.comp x smoothDyadicTheta_contDiff.contDiffAt contDiffAt_snd
    have hlog : ContDiffAt ℝ ∞ (fun y : (ℝ × ℝ × ℝ) × ℝ =>
        Real.log y.2) x := by
      exact ContDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne') contDiffAt_snd
    have hcut : ContDiffAt ℝ ∞ (fun y : (ℝ × ℝ × ℝ) × ℝ =>
        polynomialOuterCutoff (y.1.1 * y.2)) x := by
      fun_prop
    have hweight : ContDiffAt ℝ ∞ (fun y : (ℝ × ℝ × ℝ) × ℝ =>
        y.1.2.1 + y.1.2.2 * Real.log y.2) x := by
      fun_prop
    have hraw : ContDiffAt ℝ ∞ F x := by
      dsimp [F]
      fun_prop
    have heq : smoothDyadicHJoint =ᶠ[𝓝 x] F := by
      have hpos : ∀ᶠ y : (ℝ × ℝ × ℝ) × ℝ in 𝓝 x, 0 < y.2 :=
        continuous_snd.continuousAt.eventually (Ioi_mem_nhds hx)
      filter_upwards [hpos] with y hy
      simp [smoothDyadicHJoint, F, hy]
    exact hraw.congr_of_eventuallyEq heq
  · have hxlow : x.2 < (1 / 2 : ℝ) := by
      by_contra h
      have hhalf : (1 / 2 : ℝ) ≤ x.2 := le_of_not_gt h
      linarith
    have heq : smoothDyadicHJoint =ᶠ[𝓝 x] fun _ : (ℝ × ℝ × ℝ) × ℝ => 0 := by
      have hbelow : ∀ᶠ y : (ℝ × ℝ × ℝ) × ℝ in 𝓝 x, y.2 < (1 / 2 : ℝ) :=
        continuous_snd.continuousAt.eventually (Iio_mem_nhds hxlow)
      filter_upwards [hbelow] with y hy
      simp [smoothDyadicHJoint,
        smoothDyadicTheta_eq_zero_of_le_half (le_of_lt hy)]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq heq

/-- Repeated derivatives in the profile variable, represented as partial
Fréchet derivatives of the joint profile. -/
def smoothDyadicHPartial : ℕ → ((ℝ × ℝ × ℝ) × ℝ) → ℝ
  | 0 => smoothDyadicHJoint
  | n + 1 => fun x =>
      fderiv ℝ (smoothDyadicHPartial n) x ((0 : ℝ × ℝ × ℝ), (1 : ℝ))

theorem smoothDyadicHPartial_contDiff (i : ℕ) :
    ContDiff ℝ ∞ (smoothDyadicHPartial i) := by
  induction i with
  | zero => exact smoothDyadicHJoint_contDiff
  | succ i ih =>
      have hderiv : ContDiff ℝ ∞
          (fun z : ((ℝ × ℝ × ℝ) × ℝ) × ((ℝ × ℝ × ℝ) × ℝ) =>
            fderiv ℝ (smoothDyadicHPartial i) z.1 z.2) := by
        exact ih.contDiff_fderiv_apply (by simp)
      have hline : ContDiff ℝ ∞
          (fun x : (ℝ × ℝ × ℝ) × ℝ =>
            (x, ((0 : ℝ × ℝ × ℝ), (1 : ℝ)))) := by
        fun_prop
      exact hderiv.comp hline

/-- The joint partial derivative agrees with the iterated derivative of every
fixed-parameter profile. -/
theorem smoothDyadicHPartial_eq_iteratedDeriv (i : ℕ) (p : ℝ × ℝ × ℝ) (u : ℝ) :
    smoothDyadicHPartial i (p, u) =
      iteratedDeriv i (fun w => smoothDyadicHJoint (p, w)) u := by
  induction i generalizing p u with
  | zero => simp [smoothDyadicHPartial, iteratedDeriv_zero]
  | succ i ih =>
      rw [smoothDyadicHPartial, iteratedDeriv_succ]
      have hfun :
          iteratedDeriv i (fun z => smoothDyadicHJoint (p, z)) =
            (fun w => smoothDyadicHPartial i (p, w)) := by
        funext w
        exact (ih p w).symm
      rw [hfun]
      have hD : DifferentiableAt ℝ (smoothDyadicHPartial i) (p, u) :=
        (smoothDyadicHPartial_contDiff i).differentiable (by simp) (p, u)
      have hjoint : HasFDerivAt (smoothDyadicHPartial i)
          (fderiv ℝ (smoothDyadicHPartial i) (p, u)) (p, u) := hD.hasFDerivAt
      have hline : HasFDerivAt (fun w : ℝ => (p, w))
          (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) ℝ) u :=
        hasFDerivAt_prodMk_right p u
      have hcomp := hjoint.comp_hasDerivAt u hline.hasDerivAt
      have hderiv := hcomp.deriv
      simpa [Function.comp_def] using hderiv.symm

/-- Fixed-parameter iterated derivatives vary continuously jointly with all
three parameters and the profile variable. -/
theorem smoothDyadicHIterated_joint_continuous (i : ℕ) :
    Continuous (fun x : (ℝ × ℝ × ℝ) × ℝ =>
      iteratedDeriv i
        (fun u => smoothDyadicH x.1.1 x.1.2.1 x.1.2.2 u) x.2) := by
  have heq :
      (fun x : (ℝ × ℝ × ℝ) × ℝ =>
        iteratedDeriv i
          (fun u => smoothDyadicH x.1.1 x.1.2.1 x.1.2.2 u) x.2) =
        smoothDyadicHPartial i := by
    funext x
    rw [smoothDyadicHPartial_eq_iteratedDeriv]
    have hprofile :
        (fun u : ℝ => smoothDyadicHJoint (x.1, u)) =
          (fun u => smoothDyadicH x.1.1 x.1.2.1 x.1.2.2 u) := by
      funext u
      exact smoothDyadicHJoint_eq x.1.1 x.1.2.1 x.1.2.2 u
    rw [hprofile]
  rw [heq]
  exact (smoothDyadicHPartial_contDiff i).continuous

private theorem iteratedDeriv_tsupport_subset (i : ℕ) (f : ℝ → ℝ) :
    tsupport (iteratedDeriv i f) ⊆ tsupport f := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

theorem smoothDyadicHIterated_support_subset (v a b : ℝ) (i : ℕ) :
    Function.support (iteratedDeriv i (smoothDyadicH v a b)) ⊆
      Set.Icc (1 / 2 : ℝ) 2 := by
  calc
    Function.support (iteratedDeriv i (smoothDyadicH v a b))
        ⊆ tsupport (iteratedDeriv i (smoothDyadicH v a b)) := by
          change Function.support (iteratedDeriv i (smoothDyadicH v a b)) ⊆
            closure (Function.support (iteratedDeriv i (smoothDyadicH v a b)))
          exact subset_closure
    _ ⊆ tsupport (smoothDyadicH v a b) :=
      iteratedDeriv_tsupport_subset i (smoothDyadicH v a b)
    _ ⊆ Set.Icc (1 / 2 : ℝ) 2 :=
      closure_minimal (smoothDyadicH_support_subset v a b) isClosed_Icc

/-- All parameters share the same support interval for every profile
derivative. -/
theorem smoothDyadicHPartial_support_subset (i : ℕ) :
    Function.support (smoothDyadicHPartial i) ⊆
      Set.univ ×ˢ Set.Icc (1 / 2 : ℝ) 2 := by
  intro x hx
  constructor
  · trivial
  · have hderiv :
        iteratedDeriv i
          (fun u => smoothDyadicH x.1.1 x.1.2.1 x.1.2.2 u) x.2 ≠ 0 := by
      change smoothDyadicHPartial i (x.1, x.2) ≠ 0 at hx
      rw [smoothDyadicHPartial_eq_iteratedDeriv] at hx
      exact hx
    exact smoothDyadicHIterated_support_subset
      x.1.1 x.1.2.1 x.1.2.2 i hderiv

/-- The `L¹` norm of an order-`i` profile derivative, as a function of all
three profile parameters. -/
noncomputable def smoothDyadicHDerivativeL1 (i : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  ∫ u : ℝ, ‖iteratedDeriv i
    (fun w => smoothDyadicH p.1 p.2.1 p.2.2 w) u‖ ∂volume

theorem smoothDyadicHDerivativeL1_continuous (i : ℕ) :
    Continuous (smoothDyadicHDerivativeL1 i) := by
  let F : (ℝ × ℝ × ℝ) → ℝ → ℝ := fun p u =>
    ‖iteratedDeriv i (fun w => smoothDyadicH p.1 p.2.1 p.2.2 w) u‖
  have hF : Continuous F.uncurry := by
    change Continuous (fun x : (ℝ × ℝ × ℝ) × ℝ =>
      ‖iteratedDeriv i
        (fun w => smoothDyadicH x.1.1 x.1.2.1 x.1.2.2 w) x.2‖)
    exact (smoothDyadicHIterated_joint_continuous i).norm
  have hparam : Continuous (fun p : ℝ × ℝ × ℝ =>
      ∫ u in Set.Icc (1 / 2 : ℝ) 2, F p u ∂volume) :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  have hEq : smoothDyadicHDerivativeL1 i = fun p =>
      ∫ u in Set.Icc (1 / 2 : ℝ) 2, F p u ∂volume := by
    funext p
    change (∫ u : ℝ, F p u ∂volume) =
      ∫ u in Set.Icc (1 / 2 : ℝ) 2, F p u ∂volume
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    intro u hu
    have hzero : iteratedDeriv i
        (fun w => smoothDyadicH p.1 p.2.1 p.2.2 w) u = 0 := by
      by_contra hne
      have hmem : (p, u) ∈ Function.support (smoothDyadicHPartial i) := by
        change smoothDyadicHPartial i (p, u) ≠ 0
        rw [smoothDyadicHPartial_eq_iteratedDeriv]
        exact hne
      have hinterval := smoothDyadicHPartial_support_subset i hmem
      exact hu hinterval.2
    simp [F, hzero]
  rw [hEq]
  exact hparam

/-- The exact compact parameter box in `lda:smooth-data`. -/
def smoothDyadicProfileParameterBox : Set (ℝ × ℝ × ℝ) :=
  Set.Icc (3 / 8 : ℝ) 5 ×ˢ
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)

theorem smoothDyadicProfileParameterBox_isCompact :
    IsCompact smoothDyadicProfileParameterBox := by
  exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem smoothDyadicProfileParameterBox_nonempty :
    smoothDyadicProfileParameterBox.Nonempty := by
  refine ⟨((3 / 8 : ℝ), 0, 0), ?_⟩
  norm_num [smoothDyadicProfileParameterBox]

/-- The exact binomially weighted derivative sum defining `A_j`. -/
noncomputable def smoothDyadicAObjective (j : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (Nat.choose j i : ℝ) * smoothDyadicHDerivativeL1 i p

theorem smoothDyadicAObjective_continuous (j : ℕ) :
    Continuous (smoothDyadicAObjective j) := by
  unfold smoothDyadicAObjective
  exact continuous_finsetSum (Finset.range (j + 1)) fun i _ =>
    continuous_const.mul (smoothDyadicHDerivativeL1_continuous i)

theorem smoothDyadicAObjective_hasMaximum (j : ℕ) :
    ∃ p ∈ smoothDyadicProfileParameterBox,
      IsMaxOn (smoothDyadicAObjective j) smoothDyadicProfileParameterBox p :=
  smoothDyadicProfileParameterBox_isCompact.exists_isMaxOn
    smoothDyadicProfileParameterBox_nonempty
    (smoothDyadicAObjective_continuous j).continuousOn

noncomputable def smoothDyadicAArgmax (j : ℕ) : ℝ × ℝ × ℝ :=
  Classical.choose (smoothDyadicAObjective_hasMaximum j)

theorem smoothDyadicAArgmax_spec (j : ℕ) :
    smoothDyadicAArgmax j ∈ smoothDyadicProfileParameterBox ∧
      IsMaxOn (smoothDyadicAObjective j) smoothDyadicProfileParameterBox
        (smoothDyadicAArgmax j) :=
  Classical.choose_spec (smoothDyadicAObjective_hasMaximum j)

/-- The exact maximum constant `A_j` from `lda:smooth-data`. -/
noncomputable def smoothDyadicA (j : ℕ) : ℝ :=
  smoothDyadicAObjective j (smoothDyadicAArgmax j)

theorem smoothDyadicA_isMaximum (j : ℕ)
    (p : ℝ × ℝ × ℝ) (hp : p ∈ smoothDyadicProfileParameterBox) :
    smoothDyadicAObjective j p ≤ smoothDyadicA j :=
  smoothDyadicAArgmax_spec j |>.2 hp

/-- The log-scale profile whose derivative norms define `B_j`. -/
noncomputable def smoothDyadicMellinH (p : ℝ × ℝ × ℝ) (w : ℝ) : ℝ :=
  Real.exp (w / 2) *
    smoothDyadicH p.1 p.2.1 p.2.2 (Real.exp w)

/-- Joint-parameter form of the log-scale profile. -/
def smoothDyadicMellinHJoint (x : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  Real.exp (x.2 / 2) * smoothDyadicHJoint (x.1, Real.exp x.2)

theorem smoothDyadicMellinHJoint_eq (p : ℝ × ℝ × ℝ) (w : ℝ) :
    smoothDyadicMellinHJoint (p, w) = smoothDyadicMellinH p w := rfl

theorem smoothDyadicMellinHJoint_contDiff :
    ContDiff ℝ ∞ smoothDyadicMellinHJoint := by
  have harg : ContDiff ℝ ∞
      (fun x : (ℝ × ℝ × ℝ) × ℝ => (x.1, Real.exp x.2)) := by
    fun_prop
  have hinner : ContDiff ℝ ∞
      (fun x : (ℝ × ℝ × ℝ) × ℝ =>
        smoothDyadicHJoint (x.1, Real.exp x.2)) := by
    change ContDiff ℝ ∞ (smoothDyadicHJoint ∘
      (fun x : (ℝ × ℝ × ℝ) × ℝ => (x.1, Real.exp x.2)))
    exact smoothDyadicHJoint_contDiff.comp harg
  have houter : ContDiff ℝ ∞
      (fun x : (ℝ × ℝ × ℝ) × ℝ => Real.exp (x.2 / 2)) := by
    fun_prop
  change ContDiff ℝ ∞ (fun x : (ℝ × ℝ × ℝ) × ℝ =>
    Real.exp (x.2 / 2) * smoothDyadicHJoint (x.1, Real.exp x.2))
  exact houter.mul hinner

/-- Repeated `w`-derivatives represented as joint partial Fréchet
derivatives. -/
def smoothDyadicMellinPartial : ℕ → ((ℝ × ℝ × ℝ) × ℝ) → ℝ
  | 0 => smoothDyadicMellinHJoint
  | n + 1 => fun x =>
      fderiv ℝ (smoothDyadicMellinPartial n) x ((0 : ℝ × ℝ × ℝ), (1 : ℝ))

theorem smoothDyadicMellinPartial_contDiff (i : ℕ) :
    ContDiff ℝ ∞ (smoothDyadicMellinPartial i) := by
  induction i with
  | zero => exact smoothDyadicMellinHJoint_contDiff
  | succ i ih =>
      have hderiv : ContDiff ℝ ∞
          (fun z : ((ℝ × ℝ × ℝ) × ℝ) × ((ℝ × ℝ × ℝ) × ℝ) =>
            fderiv ℝ (smoothDyadicMellinPartial i) z.1 z.2) := by
        exact ih.contDiff_fderiv_apply (by simp)
      have hline : ContDiff ℝ ∞
          (fun x : (ℝ × ℝ × ℝ) × ℝ =>
            (x, ((0 : ℝ × ℝ × ℝ), (1 : ℝ)))) := by
        fun_prop
      exact hderiv.comp hline

theorem smoothDyadicMellinPartial_eq_iteratedDeriv
    (i : ℕ) (p : ℝ × ℝ × ℝ) (w : ℝ) :
    smoothDyadicMellinPartial i (p, w) =
      iteratedDeriv i (fun y => smoothDyadicMellinHJoint (p, y)) w := by
  induction i generalizing p w with
  | zero => simp [smoothDyadicMellinPartial, iteratedDeriv_zero]
  | succ i ih =>
      rw [smoothDyadicMellinPartial, iteratedDeriv_succ]
      have hfun :
          iteratedDeriv i (fun y => smoothDyadicMellinHJoint (p, y)) =
            (fun y => smoothDyadicMellinPartial i (p, y)) := by
        funext y
        exact (ih p y).symm
      rw [hfun]
      have hD : DifferentiableAt ℝ (smoothDyadicMellinPartial i) (p, w) :=
        (smoothDyadicMellinPartial_contDiff i).differentiable (by simp) (p, w)
      have hjoint : HasFDerivAt (smoothDyadicMellinPartial i)
          (fderiv ℝ (smoothDyadicMellinPartial i) (p, w)) (p, w) := hD.hasFDerivAt
      have hline : HasFDerivAt (fun y : ℝ => (p, y))
          (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) ℝ) w :=
        hasFDerivAt_prodMk_right p w
      have hcomp := hjoint.comp_hasDerivAt w hline.hasDerivAt
      have hderiv := hcomp.deriv
      simpa [Function.comp_def] using hderiv.symm

theorem smoothDyadicMellinIterated_joint_continuous (i : ℕ) :
    Continuous (fun x : (ℝ × ℝ × ℝ) × ℝ =>
      iteratedDeriv i (fun w => smoothDyadicMellinH x.1 w) x.2) := by
  have heq :
      (fun x : (ℝ × ℝ × ℝ) × ℝ =>
        iteratedDeriv i (fun w => smoothDyadicMellinH x.1 w) x.2) =
        smoothDyadicMellinPartial i := by
    funext x
    rw [smoothDyadicMellinPartial_eq_iteratedDeriv]
    have hprofile :
        (fun w : ℝ => smoothDyadicMellinHJoint (x.1, w)) =
          (fun w => smoothDyadicMellinH x.1 w) := by
      funext w
      exact smoothDyadicMellinHJoint_eq x.1 w
    rw [hprofile]
  rw [heq]
  exact (smoothDyadicMellinPartial_contDiff i).continuous

theorem smoothDyadicH_eq_zero_of_two_le {v a b u : ℝ}
    (hu : 2 ≤ u) : smoothDyadicH v a b u = 0 := by
  by_cases hpos : 0 < u
  · simp [smoothDyadicH, hpos,
      smoothDyadicTheta_eq_zero_of_two_le hu]
  · simp [smoothDyadicH, hpos]

theorem smoothDyadicMellinH_eq_zero_of_lt_lower
    (p : ℝ × ℝ × ℝ) {w : ℝ}
    (hw : w < Real.log (1 / 2 : ℝ)) : smoothDyadicMellinH p w = 0 := by
  have hexp : Real.exp w < (1 / 2 : ℝ) := by
    calc
      Real.exp w < Real.exp (Real.log (1 / 2 : ℝ)) :=
        Real.exp_lt_exp.mpr hw
      _ = (1 / 2 : ℝ) := Real.exp_log (by norm_num)
  rw [smoothDyadicMellinH]
  rw [smoothDyadicH_eq_zero_of_le_half (le_of_lt hexp)]
  simp

theorem smoothDyadicMellinH_eq_zero_of_upper_lt
    (p : ℝ × ℝ × ℝ) {w : ℝ}
    (hw : Real.log 2 < w) : smoothDyadicMellinH p w = 0 := by
  have hexp : 2 < Real.exp w := by
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ < Real.exp w := Real.exp_lt_exp.mpr hw
  rw [smoothDyadicMellinH]
  rw [smoothDyadicH_eq_zero_of_two_le (le_of_lt hexp)]
  simp

theorem smoothDyadicMellinH_support_subset (p : ℝ × ℝ × ℝ) :
    Function.support (smoothDyadicMellinH p) ⊆
      Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log 2) := by
  intro w hw
  rw [Function.mem_support] at hw
  constructor
  · by_contra h
    exact hw (smoothDyadicMellinH_eq_zero_of_lt_lower p
      (lt_of_not_ge h))
  · by_contra h
    exact hw (smoothDyadicMellinH_eq_zero_of_upper_lt p
      (lt_of_not_ge h))

theorem smoothDyadicMellinIterated_support_subset
    (p : ℝ × ℝ × ℝ) (i : ℕ) :
    Function.support (iteratedDeriv i (smoothDyadicMellinH p)) ⊆
      Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log 2) := by
  calc
    Function.support (iteratedDeriv i (smoothDyadicMellinH p))
        ⊆ tsupport (iteratedDeriv i (smoothDyadicMellinH p)) := by
          change Function.support (iteratedDeriv i (smoothDyadicMellinH p)) ⊆
            closure (Function.support (iteratedDeriv i (smoothDyadicMellinH p)))
          exact subset_closure
    _ ⊆ tsupport (smoothDyadicMellinH p) :=
      iteratedDeriv_tsupport_subset i (smoothDyadicMellinH p)
    _ ⊆ Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log 2) :=
      closure_minimal (smoothDyadicMellinH_support_subset p) isClosed_Icc

theorem smoothDyadicMellinPartial_support_subset (i : ℕ) :
    Function.support (smoothDyadicMellinPartial i) ⊆
      Set.univ ×ˢ Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log 2) := by
  intro x hx
  constructor
  · trivial
  · have hderiv :
        iteratedDeriv i (fun w => smoothDyadicMellinH x.1 w) x.2 ≠ 0 := by
      change smoothDyadicMellinPartial i (x.1, x.2) ≠ 0 at hx
      rw [smoothDyadicMellinPartial_eq_iteratedDeriv] at hx
      exact hx
    exact smoothDyadicMellinIterated_support_subset x.1 i hderiv

/-- The `L¹` norm of an order-`i` log-scale profile derivative. -/
noncomputable def smoothDyadicMellinDerivativeL1
    (i : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  ∫ w : ℝ, ‖iteratedDeriv i (smoothDyadicMellinH p) w‖ ∂volume

theorem smoothDyadicMellinDerivativeL1_continuous (i : ℕ) :
    Continuous (smoothDyadicMellinDerivativeL1 i) := by
  let F : (ℝ × ℝ × ℝ) → ℝ → ℝ := fun p w =>
    ‖iteratedDeriv i (smoothDyadicMellinH p) w‖
  have hF : Continuous F.uncurry := by
    change Continuous (fun x : (ℝ × ℝ × ℝ) × ℝ =>
      ‖iteratedDeriv i (smoothDyadicMellinH x.1) x.2‖)
    exact (smoothDyadicMellinIterated_joint_continuous i).norm
  have hparam : Continuous (fun p : ℝ × ℝ × ℝ =>
      ∫ w in Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log 2), F p w ∂volume) :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  have hEq : smoothDyadicMellinDerivativeL1 i = fun p =>
      ∫ w in Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log 2), F p w ∂volume := by
    funext p
    change (∫ w : ℝ, F p w ∂volume) =
      ∫ w in Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log 2), F p w ∂volume
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    intro w hw
    have hzero : iteratedDeriv i (smoothDyadicMellinH p) w = 0 := by
      by_contra hne
      have hmem : (p, w) ∈ Function.support (smoothDyadicMellinPartial i) := by
        change smoothDyadicMellinPartial i (p, w) ≠ 0
        rw [smoothDyadicMellinPartial_eq_iteratedDeriv]
        exact hne
      have hinterval := smoothDyadicMellinPartial_support_subset i hmem
      exact hw hinterval.2
    simp [F, hzero]
  rw [hEq]
  exact hparam

/-- The exact profile norm objective defining `B_j`. -/
noncomputable def smoothDyadicBObjective (j : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  smoothDyadicMellinDerivativeL1 j p

theorem smoothDyadicBObjective_continuous (j : ℕ) :
    Continuous (smoothDyadicBObjective j) :=
  smoothDyadicMellinDerivativeL1_continuous j

theorem smoothDyadicBObjective_hasMaximum (j : ℕ) :
    ∃ p ∈ smoothDyadicProfileParameterBox,
      IsMaxOn (smoothDyadicBObjective j) smoothDyadicProfileParameterBox p :=
  smoothDyadicProfileParameterBox_isCompact.exists_isMaxOn
    smoothDyadicProfileParameterBox_nonempty
    (smoothDyadicBObjective_continuous j).continuousOn

noncomputable def smoothDyadicBArgmax (j : ℕ) : ℝ × ℝ × ℝ :=
  Classical.choose (smoothDyadicBObjective_hasMaximum j)

theorem smoothDyadicBArgmax_spec (j : ℕ) :
    smoothDyadicBArgmax j ∈ smoothDyadicProfileParameterBox ∧
      IsMaxOn (smoothDyadicBObjective j) smoothDyadicProfileParameterBox
        (smoothDyadicBArgmax j) :=
  Classical.choose_spec (smoothDyadicBObjective_hasMaximum j)

/-- The exact maximum constant `B_j` from `lda:smooth-data`. -/
noncomputable def smoothDyadicB (j : ℕ) : ℝ :=
  smoothDyadicBObjective j (smoothDyadicBArgmax j)

theorem smoothDyadicB_isMaximum (j : ℕ)
    (p : ℝ × ℝ × ℝ) (hp : p ∈ smoothDyadicProfileParameterBox) :
    smoothDyadicBObjective j p ≤ smoothDyadicB j :=
  smoothDyadicBArgmax_spec j |>.2 hp

/-- The explicit coefficient `C_j` prescribed in `lda:smooth-data`. -/
noncomputable def smoothDyadicC (j : ℕ) : ℝ :=
  (2 : ℝ) ^ (j + 4) * ((j + 1 : ℕ) : ℝ) ^ j *
    max 1 (max (smoothDyadicA j) (smoothDyadicB j))

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicHJoint_contDiff
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicHIterated_joint_continuous
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicHDerivativeL1_continuous
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicA_isMaximum
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicMellinHJoint_contDiff
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicMellinIterated_joint_continuous
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicMellinDerivativeL1_continuous
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicB_isMaximum
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicC
