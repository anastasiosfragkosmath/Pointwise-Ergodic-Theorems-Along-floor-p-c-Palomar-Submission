module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletIntegrability
public import Mathlib.Analysis.MellinTransform

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Complex

namespace FractionalPrimes.Literature.Reciprocal

/-- The nonprincipal partial-sum kernel, extended by zero below its integral
domain so it can be treated as a Mellin-transform input. -/
def nonprincipalContinuedDirichletKernel {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  if (1 : ℝ) < t then continuedDirichletPartialSumFormula χ t else 0

/-- The total function underlying the nonprincipal continued-L branch. -/
def nonprincipalContinuedDirichletLCore {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  s * ∫ t : ℝ in Ioi (1 : ℝ),
    continuedDirichletPartialSumFormula χ t * (t : ℂ) ^ (-(s + 1))

theorem nonprincipalContinuedDirichletL_eq_core {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    (s : ℂ) (hs : 0 < s.re) :
    nonprincipalContinuedDirichletL χ hχ s hs = nonprincipalContinuedDirichletLCore χ s := rfl

private theorem nonprincipalContinuedDirichletKernel_measurable {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) :
    Measurable (nonprincipalContinuedDirichletKernel χ) := by
  unfold nonprincipalContinuedDirichletKernel
  exact Measurable.ite measurableSet_Ioi
    (measurable_continuedDirichletPartialSumFormula χ) measurable_const

private theorem nonprincipalContinuedDirichletKernel_norm_le {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    (t : ℝ) :
    ‖nonprincipalContinuedDirichletKernel χ t‖ ≤ (q : ℝ) := by
  by_cases ht : (1 : ℝ) < t
  · have hbound := continuedDirichletPartialSum_norm_le_modulus χ hχ t (le_of_lt ht)
    simpa [nonprincipalContinuedDirichletKernel, ht,
      continuedDirichletPartialSum, continuedDirichletPartialSumFormula] using hbound
  · simp [nonprincipalContinuedDirichletKernel, ht]

private theorem nonprincipalContinuedDirichletKernel_memLp_top {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q) :
    MemLp (nonprincipalContinuedDirichletKernel χ) ⊤ := by
  exact memLp_top_of_bound
    (nonprincipalContinuedDirichletKernel_measurable χ).aestronglyMeasurable
    (q : ℝ)
    (Filter.Eventually.of_forall (nonprincipalContinuedDirichletKernel_norm_le χ hχ))

private theorem nonprincipalContinuedDirichletKernel_isBigO_atTop {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q) :
    nonprincipalContinuedDirichletKernel χ =O[atTop]
      (fun t : ℝ => t ^ (-0 : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨(q : ℝ), Filter.Eventually.of_forall fun t => ?_⟩
  simpa using
    nonprincipalContinuedDirichletKernel_norm_le χ hχ t

private theorem nonprincipalContinuedDirichletKernel_isBigO_nhdsGT_zero
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) (b : ℝ) :
    nonprincipalContinuedDirichletKernel χ =O[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩
  have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hev] with t ht
  simp [nonprincipalContinuedDirichletKernel, not_lt_of_ge ht.le]

private theorem mellin_nonprincipalContinuedDirichletKernel_eq_integral
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) (s : ℂ) :
    mellin (nonprincipalContinuedDirichletKernel χ) (-s) =
      ∫ t : ℝ in Ioi (1 : ℝ),
        continuedDirichletPartialSumFormula χ t * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num)) ?_]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (1 : ℝ) < t at ht
    simp only [smul_eq_mul, nonprincipalContinuedDirichletKernel, if_pos ht]
    rw [show -s - 1 = -(s + 1) by ring, mul_comm]
  · intro t ht
    have hnot : ¬ (1 : ℝ) < t := by
      simpa using ht.2
    simp [nonprincipalContinuedDirichletKernel, hnot]

theorem nonprincipalContinuedDirichletL_differentiableAt {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (nonprincipalContinuedDirichletLCore χ) s := by
  have hloc : LocallyIntegrableOn (nonprincipalContinuedDirichletKernel χ) (Ioi 0) :=
    (nonprincipalContinuedDirichletKernel_memLp_top χ hχ).locallyIntegrable le_top
      |>.locallyIntegrableOn _
  have hf_top := nonprincipalContinuedDirichletKernel_isBigO_atTop χ hχ
  have hb : (-s).re - 1 < (-s).re := by linarith
  have hf_bot := nonprincipalContinuedDirichletKernel_isBigO_nhdsGT_zero χ ((-s).re - 1)
  have hs_top : (-s).re < 0 := by simpa only [Complex.neg_re] using neg_lt_zero.mpr hs
  have hmellin : DifferentiableAt ℂ
      (fun z : ℂ => mellin (nonprincipalContinuedDirichletKernel χ) (-z)) s := by
    have hdiff := mellin_differentiableAt_of_isBigO_rpow
      (f := nonprincipalContinuedDirichletKernel χ) (s := -s)
      hloc hf_top hs_top hf_bot hb
    exact hdiff.comp s differentiableAt_id.neg
  have hprod : DifferentiableAt ℂ
      (fun z : ℂ => z * mellin (nonprincipalContinuedDirichletKernel χ) (-z)) s :=
    differentiableAt_id.mul hmellin
  have hfun : (fun z : ℂ => nonprincipalContinuedDirichletLCore χ z) =
      fun z : ℂ => z * mellin (nonprincipalContinuedDirichletKernel χ) (-z) := by
    funext z
    simp only [nonprincipalContinuedDirichletLCore]
    rw [← mellin_nonprincipalContinuedDirichletKernel_eq_integral χ z]
  change DifferentiableAt ℂ (fun z : ℂ => nonprincipalContinuedDirichletLCore χ z) s
  rw [hfun]
  exact hprod

end FractionalPrimes.Literature.Reciprocal

end
