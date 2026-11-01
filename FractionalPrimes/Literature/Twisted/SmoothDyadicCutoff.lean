module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Data.List.Sort
public import FractionalPrimes.Literature.Polynomial.PolynomialSmoothMeanDecay

/-!
# The smooth dyadic partition cutoff

This file formalizes the smooth step and the elementary support and total
variation properties of `θ(u) = η(u) - η(2u)` from blueprint item
`lda:smooth-data`.  Profile integral constants are handled separately.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

open MeasureTheory Filter
open scoped ContDiff Topology
open FractionalPrimes.Literature.Polynomial

/-- The exact smooth step `b(u)/(b(u)+b(1-u))` from `lup:kernel-data`.
Mathlib's `Real.smoothTransition` uses this formula. -/
def smoothDyadicStep (u : ℝ) : ℝ := Real.smoothTransition u

/-- The decreasing transition `η(u)=1-s(u-1)` in `lda:smooth-data`. -/
def smoothDyadicEta (u : ℝ) : ℝ := 1 - smoothDyadicStep (u - 1)

/-- The fixed dyadic partition profile `θ(u)=η(u)-η(2u)`. -/
def smoothDyadicTheta (u : ℝ) : ℝ :=
  smoothDyadicEta u - smoothDyadicEta (2 * u)

@[fun_prop]
theorem smoothDyadicStep_contDiff : ContDiff ℝ ∞ smoothDyadicStep := by
  unfold smoothDyadicStep
  exact Real.smoothTransition.contDiff

@[fun_prop]
theorem smoothDyadicEta_contDiff : ContDiff ℝ ∞ smoothDyadicEta := by
  unfold smoothDyadicEta smoothDyadicStep
  fun_prop

@[fun_prop]
theorem smoothDyadicTheta_contDiff : ContDiff ℝ ∞ smoothDyadicTheta := by
  unfold smoothDyadicTheta
  fun_prop

theorem smoothDyadicStep_nonneg (u : ℝ) : 0 ≤ smoothDyadicStep u :=
  Real.smoothTransition.nonneg u

theorem smoothDyadicStep_le_one (u : ℝ) : smoothDyadicStep u ≤ 1 :=
  Real.smoothTransition.le_one u

theorem smoothDyadicStep_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    smoothDyadicStep u = 0 :=
  Real.smoothTransition.zero_of_nonpos hu

theorem smoothDyadicStep_one_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    smoothDyadicStep u = 1 :=
  Real.smoothTransition.one_of_one_le hu

theorem smoothDyadicEta_antitone : Antitone smoothDyadicEta := by
  intro x y hxy
  unfold smoothDyadicEta smoothDyadicStep
  have hs := Real.smoothTransition.monotone (sub_le_sub_right hxy 1)
  linarith

theorem smoothDyadicEta_nonneg (u : ℝ) : 0 ≤ smoothDyadicEta u := by
  unfold smoothDyadicEta smoothDyadicStep
  linarith [Real.smoothTransition.le_one (u - 1)]

theorem smoothDyadicEta_le_one (u : ℝ) : smoothDyadicEta u ≤ 1 := by
  unfold smoothDyadicEta smoothDyadicStep
  linarith [Real.smoothTransition.nonneg (u - 1)]

theorem smoothDyadicEta_eq_one_of_le_one {u : ℝ} (hu : u ≤ 1) :
    smoothDyadicEta u = 1 := by
  unfold smoothDyadicEta smoothDyadicStep
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem smoothDyadicEta_eq_zero_of_two_le {u : ℝ} (hu : 2 ≤ u) :
    smoothDyadicEta u = 0 := by
  unfold smoothDyadicEta smoothDyadicStep
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem smoothDyadicTheta_nonneg (u : ℝ) : 0 ≤ smoothDyadicTheta u := by
  by_cases hu : u ≤ 1
  · rw [smoothDyadicTheta, smoothDyadicEta_eq_one_of_le_one hu]
    linarith [smoothDyadicEta_le_one (2 * u)]
  · have hu1 : 1 < u := lt_of_not_ge hu
    have hmul : u ≤ 2 * u := by linarith
    have hanti := smoothDyadicEta_antitone hmul
    unfold smoothDyadicTheta
    linarith

theorem smoothDyadicTheta_le_one (u : ℝ) : smoothDyadicTheta u ≤ 1 := by
  unfold smoothDyadicTheta
  linarith [smoothDyadicEta_le_one u, smoothDyadicEta_nonneg (2 * u)]

theorem smoothDyadicTheta_eq_zero_of_le_half {u : ℝ}
    (hu : u ≤ (1 / 2 : ℝ)) : smoothDyadicTheta u = 0 := by
  unfold smoothDyadicTheta
  rw [smoothDyadicEta_eq_one_of_le_one (by linarith),
    smoothDyadicEta_eq_one_of_le_one (by linarith)]
  ring

theorem smoothDyadicTheta_eq_zero_of_two_le {u : ℝ}
    (hu : 2 ≤ u) : smoothDyadicTheta u = 0 := by
  unfold smoothDyadicTheta
  rw [smoothDyadicEta_eq_zero_of_two_le hu,
    smoothDyadicEta_eq_zero_of_two_le (by linarith)]
  ring

/-- The support of the smooth dyadic profile is contained in its exact
source interval `[1/2,2]`. -/
theorem smoothDyadicTheta_support_subset :
    Function.support smoothDyadicTheta ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
  intro u hu
  rw [Function.mem_support] at hu
  constructor
  · by_contra h
    exact hu (smoothDyadicTheta_eq_zero_of_le_half (le_of_not_ge h))
  · by_contra h
    exact hu (smoothDyadicTheta_eq_zero_of_two_le (le_of_not_ge h))

/-- The exact profile `H_{v,a,b}` from `lda:smooth-data`, extended by zero
to nonpositive arguments. -/
def smoothDyadicH (v a b u : ℝ) : ℝ :=
  if 0 < u then
    smoothDyadicTheta u * polynomialOuterCutoff (v * u) *
      (a + b * Real.log u)
  else 0

theorem smoothDyadicH_eq_zero_of_le_half {v a b u : ℝ}
    (hu : u ≤ (1 / 2 : ℝ)) : smoothDyadicH v a b u = 0 := by
  by_cases hpos : 0 < u
  · simp [smoothDyadicH, hpos,
      smoothDyadicTheta_eq_zero_of_le_half hu]
  · simp [smoothDyadicH, hpos]

theorem smoothDyadicH_support_subset (v a b : ℝ) :
    Function.support (smoothDyadicH v a b) ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
  intro u hu
  rw [Function.mem_support] at hu
  by_cases hpos : 0 < u
  · have htheta : smoothDyadicTheta u ≠ 0 := by
      intro hzero
      apply hu
      simp [smoothDyadicH, hpos, hzero]
    exact smoothDyadicTheta_support_subset htheta
  · simp [smoothDyadicH, hpos] at hu

theorem smoothDyadicH_contDiff (v a b : ℝ) :
    ContDiff ℝ ∞ (smoothDyadicH v a b) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : 0 < u
  · let F : ℝ → ℝ := fun x =>
      smoothDyadicTheta x * polynomialOuterCutoff (v * x) *
        (a + b * Real.log x)
    have htheta : ContDiffAt ℝ ∞ smoothDyadicTheta u :=
      smoothDyadicTheta_contDiff.contDiffAt
    have hlog : ContDiffAt ℝ ∞ Real.log u :=
      Real.contDiffAt_log.mpr hu.ne'
    have hweight : ContDiffAt ℝ ∞ (fun x => a + b * Real.log x) u := by
      fun_prop
    have hcut : ContDiffAt ℝ ∞
        (fun x => polynomialOuterCutoff (v * x)) u := by
      fun_prop
    have hraw : ContDiffAt ℝ ∞ F u := by
      dsimp [F]
      fun_prop
    have heq : smoothDyadicH v a b =ᶠ[𝓝 u] F := by
      filter_upwards [Ioi_mem_nhds hu] with x hx
      have hxpos : 0 < x := hx
      simp [smoothDyadicH, F, hxpos]
    exact hraw.congr_of_eventuallyEq heq
  · have hbelow : u < 1 / 2 := by
      by_contra h
      have hhalf : (1 / 2 : ℝ) ≤ u := le_of_not_gt h
      linarith
    have heq : smoothDyadicH v a b =ᶠ[𝓝 u] fun _ : ℝ => 0 := by
      filter_upwards [Iio_mem_nhds hbelow] with x hx
      exact smoothDyadicH_eq_zero_of_le_half (le_of_lt hx)
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq heq

theorem smoothDyadicH_hasCompactSupport (v a b : ℝ) :
    HasCompactSupport (smoothDyadicH v a b) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact smoothDyadicH_support_subset v a b

private theorem smoothDyadicHIterated_hasCompactSupport
    (v a b : ℝ) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j (smoothDyadicH v a b)) := by
  induction j with
  | zero => simpa [iteratedDeriv_zero] using smoothDyadicH_hasCompactSupport v a b
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

private theorem smoothDyadicHIterated_continuous
    (v a b : ℝ) (j : ℕ) :
    Continuous (iteratedDeriv j (smoothDyadicH v a b)) :=
  ContDiff.continuous_iteratedDeriv j (smoothDyadicH_contDiff v a b) (by simp)

/-- Every profile derivative norm in the definition of `A_j` is integrable. -/
theorem smoothDyadicHIterated_norm_integrable
    (v a b : ℝ) (j : ℕ) :
    Integrable (fun u : ℝ => ‖iteratedDeriv j (smoothDyadicH v a b) u‖) :=
  (smoothDyadicHIterated_continuous v a b j).norm.integrable_of_hasCompactSupport
    (smoothDyadicHIterated_hasCompactSupport v a b j).norm

def smoothDyadicVariationAux (f : ℝ → ℝ) (prev : ℝ) : List ℝ → ℝ
  | [] => 0
  | x :: xs => |f x - f prev| + smoothDyadicVariationAux f x xs

/-- Finite total variation sampled on an ordered list. -/
def smoothDyadicFiniteVariation (f : ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | x :: xs => smoothDyadicVariationAux f x xs

theorem smoothDyadicVariationAux_le_first
    (f : ℝ → ℝ) (hf : Antitone f) (hnonneg : ∀ x, 0 ≤ f x) :
    ∀ (a : ℝ) (xs : List ℝ),
      List.Pairwise (· ≤ ·) (a :: xs) →
      smoothDyadicVariationAux f a xs ≤ f a := by
  intro a xs
  induction xs generalizing a with
  | nil =>
      intro _
      simp [smoothDyadicVariationAux]
      exact hnonneg a
  | cons b xs ih =>
      intro hsorted
      have hab : a ≤ b := hsorted.rel_head_tail (by simp)
      have htailSorted : List.Pairwise (· ≤ ·) (b :: xs) := hsorted.tail
      have htail := ih b htailSorted
      simp only [smoothDyadicVariationAux]
      have hdiff : |f b - f a| = f a - f b := by
        rw [abs_of_nonpos (sub_nonpos.mpr (hf hab))]
        ring
      rw [hdiff]
      linarith

theorem smoothDyadicFiniteVariation_le_one_of_antitone
    (f : ℝ → ℝ) (hf : Antitone f)
    (hnonneg : ∀ x, 0 ≤ f x) (hleOne : ∀ x, f x ≤ 1)
    (l : List ℝ) (hl : List.Pairwise (· ≤ ·) l) :
    smoothDyadicFiniteVariation f l ≤ 1 := by
  cases l with
  | nil => simp [smoothDyadicFiniteVariation]
  | cons a xs =>
      change smoothDyadicVariationAux f a xs ≤ 1
      have h := smoothDyadicVariationAux_le_first f hf hnonneg a xs hl
      exact h.trans (hleOne a)

theorem smoothDyadicFiniteVariation_sub_le
    (f g : ℝ → ℝ) (l : List ℝ) :
    smoothDyadicFiniteVariation (fun x => f x - g x) l ≤
      smoothDyadicFiniteVariation f l + smoothDyadicFiniteVariation g l := by
  cases l with
  | nil => simp [smoothDyadicFiniteVariation]
  | cons a xs =>
      change smoothDyadicVariationAux (fun x => f x - g x) a xs ≤ _
      induction xs generalizing a with
      | nil => simp [smoothDyadicVariationAux, smoothDyadicFiniteVariation]
      | cons b xs ih =>
          simp only [smoothDyadicVariationAux, smoothDyadicFiniteVariation]
          have hfirst :
              |(f b - g b) - (f a - g a)| ≤
                |f b - f a| + |g b - g a| := by
            calc
              |(f b - g b) - (f a - g a)| =
                  |(f b - f a) - (g b - g a)| := by congr 1 <;> ring
              _ ≤ |f b - f a| + |g b - g a| := abs_sub _ _
          have htail := ih b
          simp only [smoothDyadicFiniteVariation] at htail
          linarith

theorem smoothDyadicTheta_variation_on_ordered_list_le_two
    (l : List ℝ) (hl : List.Pairwise (· ≤ ·) l) :
    smoothDyadicFiniteVariation smoothDyadicTheta l ≤ 2 := by
  have hsub := smoothDyadicFiniteVariation_sub_le
    smoothDyadicEta (fun u => smoothDyadicEta (2 * u)) l
  have hfirst : smoothDyadicFiniteVariation smoothDyadicEta l ≤ 1 :=
    smoothDyadicFiniteVariation_le_one_of_antitone smoothDyadicEta
      smoothDyadicEta_antitone smoothDyadicEta_nonneg smoothDyadicEta_le_one l hl
  have hdoubleAnti : Antitone (fun u => smoothDyadicEta (2 * u)) := by
    intro x y hxy
    exact smoothDyadicEta_antitone (by linarith)
  have hdoubleNonneg : ∀ u, 0 ≤ smoothDyadicEta (2 * u) :=
    fun u => smoothDyadicEta_nonneg (2 * u)
  have hdoubleLeOne : ∀ u, smoothDyadicEta (2 * u) ≤ 1 :=
    fun u => smoothDyadicEta_le_one (2 * u)
  have hsecond :
      smoothDyadicFiniteVariation (fun u => smoothDyadicEta (2 * u)) l ≤ 1 :=
    smoothDyadicFiniteVariation_le_one_of_antitone
      (fun u => smoothDyadicEta (2 * u)) hdoubleAnti
      hdoubleNonneg hdoubleLeOne l hl
  have htheta :
      smoothDyadicFiniteVariation smoothDyadicTheta l ≤
        smoothDyadicFiniteVariation smoothDyadicEta l +
          smoothDyadicFiniteVariation (fun u => smoothDyadicEta (2 * u)) l := by
    change smoothDyadicFiniteVariation
      (fun u => smoothDyadicEta u - smoothDyadicEta (2 * u)) l ≤ _
    exact hsub
  linarith

/-- Total variation on the real line, defined as the supremum of the finite
variation sums over all finite nondecreasing sample lists. -/
noncomputable def smoothDyadicThetaTotalVariation : ℝ :=
  sSup {v : ℝ | ∃ l : List ℝ,
    List.Pairwise (· ≤ ·) l ∧ v = smoothDyadicFiniteVariation smoothDyadicTheta l}

theorem smoothDyadicTheta_totalVariation_le_two :
    smoothDyadicThetaTotalVariation ≤ 2 := by
  unfold smoothDyadicThetaTotalVariation
  apply csSup_le
  · exact ⟨0, ⟨[], by simp, by simp [smoothDyadicFiniteVariation]⟩⟩
  · intro v hv
    rcases hv with ⟨l, hl, rfl⟩
    exact smoothDyadicTheta_variation_on_ordered_list_le_two l hl

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicTheta_support_subset
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicTheta_contDiff
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicTheta_nonneg
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicTheta_le_one
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicTheta_variation_on_ordered_list_le_two
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicTheta_totalVariation_le_two
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicH_support_subset
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicH_contDiff
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicH_hasCompactSupport
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicHIterated_norm_integrable
