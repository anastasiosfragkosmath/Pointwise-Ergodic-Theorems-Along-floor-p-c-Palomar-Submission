module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownConvolution
public import FractionalPrimes.Literature.Uniformity.ArithmeticGrouping
public import FractionalPrimes.Literature.Polynomial.PolynomialSmoothMeanDecay
public import Mathlib.Tactic

/-!
# Support retention for the smooth Heath--Brown components

This file develops the source support filter and scale-product bookkeeping
for `lda:smooth-hb`, starting with the support of an individual factor.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open Finset
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The dyadic scale attached to a smooth Heath--Brown factor. -/
def smoothHeathBrownFactorScale {X : ℝ} :
    SmoothHeathBrownFactor X → ℝ
  | .theta j => (2 : ℝ) ^ j.val
  | .logarithm j => (2 : ℝ) ^ j.val
  | .mobius j => (2 : ℝ) ^ j.val

/-- The natural-number exponent specifying a smooth dyadic factor's scale. -/
def smoothHeathBrownFactorExponent {X : ℝ} :
    SmoothHeathBrownFactor X → ℕ
  | .theta j => j.val
  | .logarithm j => j.val
  | .mobius j => j.val

/-- The product of the dyadic scales in a labelled component. -/
def smoothHeathBrownScaleProduct {X : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) : ℝ :=
  (fs.map smoothHeathBrownFactorScale).prod

/-- Total dyadic exponent, counted with factor multiplicity. -/
def smoothHeathBrownExponentSum {X : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) : ℕ :=
  ∑ i : Fin fs.length, smoothHeathBrownFactorExponent (fs.get i)

/-- Product of scales over a labelled subset of factor positions. -/
def smoothHeathBrownSubgroupScaleProduct {X : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) (S : Finset (Fin fs.length)) : ℝ :=
  ∏ i ∈ S, smoothHeathBrownFactorScale (fs.get i)

/-- Sum of natural scale exponents over a labelled subset of factor positions. -/
def smoothHeathBrownSubgroupExponent {X : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) (S : Finset (Fin fs.length)) : ℕ :=
  ∑ i ∈ S, smoothHeathBrownFactorExponent (fs.get i)

private theorem smoothHeathBrown_factorScale_eq_powExponent {X : ℝ}
    (f : SmoothHeathBrownFactor X) :
    smoothHeathBrownFactorScale f =
      (2 : ℝ) ^ smoothHeathBrownFactorExponent f := by
  cases f <;> rfl

private theorem smoothHeathBrown_prod_two_pow_eq_sum
    {α : Type*} (s : Finset α) (e : α → ℕ) :
    (∏ i ∈ s, (2 : ℝ) ^ e i) = (2 : ℝ) ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      rw [← pow_add]

theorem smoothHeathBrownFactorScale_pos {X : ℝ}
    (f : SmoothHeathBrownFactor X) : 0 < smoothHeathBrownFactorScale f := by
  cases f <;> simp [smoothHeathBrownFactorScale]

theorem smoothHeathBrownFactorScale_ge_one {X : ℝ}
    (f : SmoothHeathBrownFactor X) : 1 ≤ smoothHeathBrownFactorScale f := by
  cases f <;> simp [smoothHeathBrownFactorScale] <;>
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem smoothHeathBrownScaleProduct_pos {X : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) :
    0 < smoothHeathBrownScaleProduct fs := by
  induction fs with
  | nil => simp [smoothHeathBrownScaleProduct]
  | cons f fs ih =>
      simp only [smoothHeathBrownScaleProduct, List.map_cons, List.prod_cons]
      exact mul_pos (smoothHeathBrownFactorScale_pos f) ih

private theorem smoothHeathBrownScaleProduct_eq_finset_prod {X : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) :
    smoothHeathBrownScaleProduct fs =
      ∏ i : Fin fs.length, smoothHeathBrownFactorScale (fs.get i) := by
  unfold smoothHeathBrownScaleProduct
  rw [← List.prod_ofFn]
  congr 1
  have h := List.ofFn_getElem_eq_map fs smoothHeathBrownFactorScale
  simpa [List.get_eq_getElem] using h.symm

theorem smoothHeathBrownScaleProduct_eq_two_pow_exponentSum {X : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) :
    smoothHeathBrownScaleProduct fs =
      (2 : ℝ) ^ smoothHeathBrownExponentSum fs := by
  rw [smoothHeathBrownScaleProduct_eq_finset_prod]
  simp_rw [smoothHeathBrown_factorScale_eq_powExponent]
  exact smoothHeathBrown_prod_two_pow_eq_sum
    (Finset.univ : Finset (Fin fs.length))
    (fun i => smoothHeathBrownFactorExponent (fs.get i))

theorem smoothHeathBrownSubgroupScaleProduct_eq_two_pow_exponent
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (S : Finset (Fin fs.length)) :
    smoothHeathBrownSubgroupScaleProduct fs S =
      (2 : ℝ) ^ smoothHeathBrownSubgroupExponent fs S := by
  unfold smoothHeathBrownSubgroupScaleProduct smoothHeathBrownSubgroupExponent
  simp_rw [smoothHeathBrown_factorScale_eq_powExponent]
  exact smoothHeathBrown_prod_two_pow_eq_sum S
    (fun i => smoothHeathBrownFactorExponent (fs.get i))

private theorem smoothHeathBrownFactorFunction_support_bounds {X z : ℝ}
    (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hne : smoothHeathBrownFactorFunction z f n ≠ 0) :
    smoothHeathBrownFactorScale f / 2 < (n : ℝ) ∧
      (n : ℝ) < 2 * smoothHeathBrownFactorScale f := by
  cases f with
  | theta j =>
      have hn : n ≠ 0 := by
        by_contra h
        subst n
        simp [smoothHeathBrownFactorFunction, smoothHeathBrownThetaFactor] at hne
      have htheta :
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≠ 0 := by
        intro hzero
        apply hne
        simp [smoothHeathBrownFactorFunction, smoothHeathBrownThetaFactor, hn,
          hzero]
      have hscale : 0 < (2 : ℝ) ^ j.val := by positivity
      have hlow : (1 / 2 : ℝ) < (n : ℝ) / (2 : ℝ) ^ j.val := by
        by_contra h
        exact htheta (smoothDyadicTheta_eq_zero_of_le_half (le_of_not_gt h))
      have hupp : (n : ℝ) / (2 : ℝ) ^ j.val < 2 := by
        by_contra h
        exact htheta (smoothDyadicTheta_eq_zero_of_two_le (le_of_not_gt h))
      constructor
      · have hmul := mul_lt_mul_of_pos_right hlow hscale
        have hcancel :
            ((n : ℝ) / (2 : ℝ) ^ j.val) * (2 : ℝ) ^ j.val = (n : ℝ) :=
          div_mul_cancel₀ _ hscale.ne'
        calc
          smoothHeathBrownFactorScale (.theta j) / 2 =
              (1 / 2 : ℝ) * (2 : ℝ) ^ j.val := by
                simp [smoothHeathBrownFactorScale]
                ring
          _ < (n : ℝ) := by nlinarith [hmul, hcancel]
      · simpa [smoothHeathBrownFactorScale] using
          (div_lt_iff₀ hscale).mp hupp
  | logarithm j =>
      have hn : n ≠ 0 := by
        by_contra h
        subst n
        simp [smoothHeathBrownFactorFunction, smoothHeathBrownLogFactor] at hne
      have htheta :
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≠ 0 := by
        intro hzero
        apply hne
        simp [smoothHeathBrownFactorFunction, smoothHeathBrownLogFactor, hn,
          hzero]
      have hscale : 0 < (2 : ℝ) ^ j.val := by positivity
      have hlow : (1 / 2 : ℝ) < (n : ℝ) / (2 : ℝ) ^ j.val := by
        by_contra h
        exact htheta (smoothDyadicTheta_eq_zero_of_le_half (le_of_not_gt h))
      have hupp : (n : ℝ) / (2 : ℝ) ^ j.val < 2 := by
        by_contra h
        exact htheta (smoothDyadicTheta_eq_zero_of_two_le (le_of_not_gt h))
      constructor
      · have hmul := mul_lt_mul_of_pos_right hlow hscale
        have hcancel :
            ((n : ℝ) / (2 : ℝ) ^ j.val) * (2 : ℝ) ^ j.val = (n : ℝ) :=
          div_mul_cancel₀ _ hscale.ne'
        calc
          smoothHeathBrownFactorScale (.logarithm j) / 2 =
              (1 / 2 : ℝ) * (2 : ℝ) ^ j.val := by
                simp [smoothHeathBrownFactorScale]
                ring
          _ < (n : ℝ) := by nlinarith [hmul, hcancel]
      · simpa [smoothHeathBrownFactorScale] using
          (div_lt_iff₀ hscale).mp hupp
  | mobius j =>
      have hn : n ≠ 0 := by
        by_contra h
        subst n
        simp [smoothHeathBrownFactorFunction, smoothHeathBrownMobiusFactor] at hne
      have htheta :
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≠ 0 := by
        intro hzero
        apply hne
        simp [smoothHeathBrownFactorFunction, smoothHeathBrownMobiusFactor, hn,
          hzero]
      have hscale : 0 < (2 : ℝ) ^ j.val := by positivity
      have hlow : (1 / 2 : ℝ) < (n : ℝ) / (2 : ℝ) ^ j.val := by
        by_contra h
        exact htheta (smoothDyadicTheta_eq_zero_of_le_half (le_of_not_gt h))
      have hupp : (n : ℝ) / (2 : ℝ) ^ j.val < 2 := by
        by_contra h
        exact htheta (smoothDyadicTheta_eq_zero_of_two_le (le_of_not_gt h))
      constructor
      · have hmul := mul_lt_mul_of_pos_right hlow hscale
        have hcancel :
            ((n : ℝ) / (2 : ℝ) ^ j.val) * (2 : ℝ) ^ j.val = (n : ℝ) :=
          div_mul_cancel₀ _ hscale.ne'
        calc
          smoothHeathBrownFactorScale (.mobius j) / 2 =
              (1 / 2 : ℝ) * (2 : ℝ) ^ j.val := by
                simp [smoothHeathBrownFactorScale]
                ring
          _ < (n : ℝ) := by nlinarith [hmul, hcancel]
      · simpa [smoothHeathBrownFactorScale] using
          (div_lt_iff₀ hscale).mp hupp

private theorem smoothHeathBrown_mul_apply_ne_zero
    {f g : ArithmeticFunction ℝ} {n : ℕ} (hne : (f * g) n ≠ 0) :
    ∃ x ∈ n.divisorsAntidiagonal, f x.1 ≠ 0 ∧ g x.2 ≠ 0 := by
  rw [ArithmeticFunction.mul_apply] at hne
  by_contra hnone
  have hterms : ∀ x ∈ n.divisorsAntidiagonal,
      f x.1 = 0 ∨ g x.2 = 0 := by
    intro x hx
    by_cases hf : f x.1 = 0
    · exact Or.inl hf
    · right
      by_contra hg
      exact hnone ⟨x, hx, hf, hg⟩
  have hsum :
      (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rcases hterms x hx with hf | hg
    · simp [hf]
    · simp [hg]
  exact hne hsum

theorem smoothHeathBrownConvolutionFactors_support_bounds {X z : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) (hfs : fs ≠ []) {n : ℕ}
    (hne : smoothHeathBrownConvolutionFactors z fs n ≠ 0) :
    smoothHeathBrownScaleProduct fs <
        (2 : ℝ) ^ fs.length * (n : ℝ) ∧
      (n : ℝ) < (2 : ℝ) ^ fs.length * smoothHeathBrownScaleProduct fs := by
  induction fs generalizing n with
  | nil => contradiction
  | cons f fs ih =>
      cases fs with
      | nil =>
          have hfactor : smoothHeathBrownFactorFunction z f n ≠ 0 := by
            simpa [smoothHeathBrownConvolutionFactors] using hne
          have hb := smoothHeathBrownFactorFunction_support_bounds f hfactor
          have hnpos : 0 < (n : ℝ) :=
            lt_trans (div_pos (smoothHeathBrownFactorScale_pos f) (by norm_num)) hb.1
          constructor
          · simp [smoothHeathBrownScaleProduct]
            nlinarith
          · simpa [smoothHeathBrownScaleProduct] using hb.2
      | cons g gs =>
          have hmul :
              (smoothHeathBrownFactorFunction z f *
                smoothHeathBrownConvolutionFactors z (g :: gs)) n ≠ 0 := by
            simpa [smoothHeathBrownConvolutionFactors] using hne
          obtain ⟨x, hx, hfirst, htail⟩ :=
            smoothHeathBrown_mul_apply_ne_zero hmul
          have hfirstBounds := smoothHeathBrownFactorFunction_support_bounds f hfirst
          have htailBounds := ih (by simp) htail
          have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
          have hpairReal : (n : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by
            exact_mod_cast hpair.symm
          have hxposNat : 0 < x.1 :=
            Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx)
          have hyposNat : 0 < x.2 :=
            Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)
          have hxpos : 0 < (x.1 : ℝ) := by exact_mod_cast hxposNat
          have hypos : 0 < (x.2 : ℝ) := by exact_mod_cast hyposNat
          have htailPos : 0 < smoothHeathBrownScaleProduct (g :: gs) :=
            smoothHeathBrownScaleProduct_pos (g :: gs)
          have hscalePos : 0 < smoothHeathBrownFactorScale f :=
            smoothHeathBrownFactorScale_pos f
          constructor
          · have hfirstLower :
                smoothHeathBrownFactorScale f < 2 * (x.1 : ℝ) := by
              linarith [hfirstBounds.1]
            have hlow :
                smoothHeathBrownFactorScale f *
                    smoothHeathBrownScaleProduct (g :: gs) <
                  (2 : ℝ) ^ ((g :: gs).length + 1) *
                    ((x.1 : ℝ) * (x.2 : ℝ)) := by
              calc
                smoothHeathBrownFactorScale f *
                    smoothHeathBrownScaleProduct (g :: gs) <
                  (2 * (x.1 : ℝ)) * smoothHeathBrownScaleProduct (g :: gs) :=
                    mul_lt_mul_of_pos_right hfirstLower htailPos
                _ < (2 * (x.1 : ℝ)) *
                    ((2 : ℝ) ^ (g :: gs).length * (x.2 : ℝ)) :=
                  mul_lt_mul_of_pos_left htailBounds.1 (by positivity)
                _ = (2 : ℝ) ^ ((g :: gs).length + 1) *
                    ((x.1 : ℝ) * (x.2 : ℝ)) := by
                  rw [pow_succ]
                  ring
            have hlen : (g :: gs).length + 1 = (f :: g :: gs).length := by
              simp
            rw [smoothHeathBrownScaleProduct, List.map_cons, List.prod_cons,
              List.length_cons]
            rw [hpairReal]
            exact hlow
          · have hupp :
                ((x.1 : ℝ) * (x.2 : ℝ)) <
                  (2 : ℝ) ^ ((g :: gs).length + 1) *
                    (smoothHeathBrownFactorScale f *
                      smoothHeathBrownScaleProduct (g :: gs)) := by
              calc
                (x.1 : ℝ) * (x.2 : ℝ) <
                    (2 * smoothHeathBrownFactorScale f) * (x.2 : ℝ) :=
                  mul_lt_mul_of_pos_right hfirstBounds.2 hypos
                _ < (2 * smoothHeathBrownFactorScale f) *
                    ((2 : ℝ) ^ (g :: gs).length *
                      smoothHeathBrownScaleProduct (g :: gs)) :=
                  mul_lt_mul_of_pos_left htailBounds.2
                    (by positivity)
                _ = (2 : ℝ) ^ ((g :: gs).length + 1) *
                    (smoothHeathBrownFactorScale f *
                      smoothHeathBrownScaleProduct (g :: gs)) := by
                  rw [pow_succ]
                  ring
            rw [smoothHeathBrownScaleProduct, List.map_cons, List.prod_cons,
              List.length_cons]
            exact hpairReal ▸ hupp

/-- A component is retained precisely when its convolution is nonzero at a
positive integer in the support interval of the outer cutoff. -/
def smoothHeathBrownSupportRetained {X z : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) : Prop :=
  ∃ n : ℕ,
    (3 / 4 : ℝ) * X ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (5 / 2 : ℝ) * X ∧
      smoothHeathBrownConvolutionFactors z fs n ≠ 0

/-- The retained Möbius labels, filtered by the support of their component. -/
noncomputable def smoothHeathBrownMobiusRetainedLabels (X : ℝ) :
    Finset (SmoothHeathBrownMobiusLabel X) := by
  classical
  exact Finset.univ.filter fun ν =>
    smoothHeathBrownSupportRetained (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownMobiusLabelFactors ν)

/-- The retained von Mangoldt labels, filtered by the support of their
component. -/
noncomputable def smoothHeathBrownVonMangoldtRetainedLabels (X : ℝ) :
    Finset (SmoothHeathBrownVonMangoldtLabel X) := by
  classical
  exact Finset.univ.filter fun ν =>
    smoothHeathBrownSupportRetained (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownVonMangoldtLabelFactors ν)

/-- Every retained list has its source scale-product window. The interval
constants are the exact `[3X/4,5X/2]` support window and `2^22` loss. -/
theorem smoothHeathBrownSupportRetained_scale_bounds {X z : ℝ}
    {fs : List (SmoothHeathBrownFactor X)}
    (hlen : fs.length ≤ 20)
    (hfsne : fs ≠ [])
    (hX : 0 ≤ X)
    (hfs : smoothHeathBrownSupportRetained (X := X) (z := z) fs) :
    X / (2 : ℝ) ^ 22 ≤ smoothHeathBrownScaleProduct fs ∧
      smoothHeathBrownScaleProduct fs ≤ (2 : ℝ) ^ 22 * X := by
  obtain ⟨n, hnlo, hnhi, hne⟩ := hfs
  have hb := smoothHeathBrownConvolutionFactors_support_bounds fs hfsne hne
  have hA : (2 : ℝ) ^ fs.length ≤ (2 : ℝ) ^ 20 :=
    pow_le_pow_right₀ (by norm_num) hlen
  have hP : 0 ≤ smoothHeathBrownScaleProduct fs :=
    (smoothHeathBrownScaleProduct_pos fs).le
  have hscalePowPos : 0 < (2 : ℝ) ^ fs.length := by positivity
  constructor
  · have hlower :
        (3 / 4 : ℝ) * X < (2 : ℝ) ^ 20 *
          smoothHeathBrownScaleProduct fs := by
      calc
        (3 / 4 : ℝ) * X ≤ (n : ℝ) := hnlo
        _ < (2 : ℝ) ^ fs.length * smoothHeathBrownScaleProduct fs := hb.2
        _ ≤ (2 : ℝ) ^ 20 * smoothHeathBrownScaleProduct fs :=
          mul_le_mul_of_nonneg_right hA hP
    norm_num at hlower ⊢
    nlinarith [hlower, hX]
  · have hupper :
        smoothHeathBrownScaleProduct fs < (2 : ℝ) ^ 20 *
          ((5 / 2 : ℝ) * X) := by
      calc
        smoothHeathBrownScaleProduct fs <
            (2 : ℝ) ^ fs.length * (n : ℝ) := hb.1
        _ ≤ (2 : ℝ) ^ fs.length * ((5 / 2 : ℝ) * X) :=
          mul_le_mul_of_nonneg_left hnhi hscalePowPos.le
        _ ≤ (2 : ℝ) ^ 20 * ((5 / 2 : ℝ) * X) :=
          mul_le_mul_of_nonneg_right hA
            (mul_nonneg (by norm_num) hX)
    norm_num at hupper ⊢
    nlinarith [hupper, hX]

theorem smoothHeathBrownMobiusRetained_scale_bounds {X : ℝ}
    (hX : 3 ≤ X) {ν : SmoothHeathBrownMobiusLabel X}
    (hν : ν ∈ smoothHeathBrownMobiusRetainedLabels X) :
    X / (2 : ℝ) ^ 22 ≤
        smoothHeathBrownScaleProduct (smoothHeathBrownMobiusLabelFactors ν) ∧
      smoothHeathBrownScaleProduct (smoothHeathBrownMobiusLabelFactors ν) ≤
        (2 : ℝ) ^ 22 * X := by
  classical
  have hmem : smoothHeathBrownSupportRetained (X := X)
      (z := dyadicMobiusCutoff X) (smoothHeathBrownMobiusLabelFactors ν) :=
    (Finset.mem_filter.mp hν).2
  have hfsne : smoothHeathBrownMobiusLabelFactors ν ≠ [] := by
    intro hnil
    have hlen := (smoothHeathBrownMobiusFactorCount ν).1
    rw [hnil] at hlen
    simp at hlen
  exact smoothHeathBrownSupportRetained_scale_bounds
    (X := X) (z := dyadicMobiusCutoff X)
    (fs := smoothHeathBrownMobiusLabelFactors ν)
    (smoothHeathBrownMobiusFactorCount ν).2 hfsne (by linarith) hmem

theorem smoothHeathBrownVonMangoldtRetained_scale_bounds {X : ℝ}
    (hX : 3 ≤ X) {ν : SmoothHeathBrownVonMangoldtLabel X}
    (hν : ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X) :
    X / (2 : ℝ) ^ 22 ≤
        smoothHeathBrownScaleProduct (smoothHeathBrownVonMangoldtLabelFactors ν) ∧
      smoothHeathBrownScaleProduct (smoothHeathBrownVonMangoldtLabelFactors ν) ≤
        (2 : ℝ) ^ 22 * X := by
  classical
  have hmem : smoothHeathBrownSupportRetained (X := X)
      (z := dyadicMobiusCutoff X) (smoothHeathBrownVonMangoldtLabelFactors ν) :=
    (Finset.mem_filter.mp hν).2
  have hfsne : smoothHeathBrownVonMangoldtLabelFactors ν ≠ [] := by
    intro hnil
    have hlen := (smoothHeathBrownVonMangoldtFactorCount ν).1
    rw [hnil] at hlen
    simp at hlen
  exact smoothHeathBrownSupportRetained_scale_bounds
    (X := X) (z := dyadicMobiusCutoff X)
    (fs := smoothHeathBrownVonMangoldtLabelFactors ν)
    (smoothHeathBrownVonMangoldtFactorCount ν).2 hfsne (by linarith) hmem

/-- Multiplication by the outer cutoff makes the support-based label filter
exact in the Möbius expansion. -/
theorem smoothHeathBrownMobiusRetainedExpansion {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    polynomialOuterCutoff ((n : ℝ) / X) *
        (ArithmeticFunction.moebius n : ℝ) =
      ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
        polynomialOuterCutoff ((n : ℝ) / X) *
          smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n := by
  classical
  let ζ := polynomialOuterCutoff ((n : ℝ) / X)
  let R := smoothHeathBrownMobiusRetainedLabels X
  by_cases hζ : ζ = 0
  · simp [ζ, hζ]
  · have hXpos : 0 < X := by linarith
    have hsupp : (n : ℝ) / X ∈ Set.Icc (3 / 4 : ℝ) (5 / 2 : ℝ) := by
      exact polynomialOuterCutoff_support_subset (by
        simpa [ζ, Function.mem_support] using hζ)
    have hnlo : (3 / 4 : ℝ) * X ≤ (n : ℝ) :=
      (le_div_iff₀ hXpos).mp hsupp.1
    have hnhi : (n : ℝ) ≤ (5 / 2 : ℝ) * X :=
      (div_le_iff₀ hXpos).mp hsupp.2
    have hexp := smoothHeathBrownMobiusExpansion hX hn hnX
    have hsum :
        (∑ ν ∈ R, ζ * smoothHeathBrownMobiusComponent
            (dyadicMobiusCutoff X) ν n) =
          ∑ ν : SmoothHeathBrownMobiusLabel X,
            ζ * smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro ν hν hνnot
      have hnot : ν ∉ R := hνnot
      have hconv :
          smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
            (smoothHeathBrownMobiusLabelFactors ν) n = 0 := by
        by_contra hconv
        have hRetained : ν ∈ smoothHeathBrownMobiusRetainedLabels X := by
          rw [smoothHeathBrownMobiusRetainedLabels, Finset.mem_filter]
          constructor
          · simp
          · exact ⟨n, hnlo, hnhi, hconv⟩
        exact hnot hRetained
      simp [smoothHeathBrownMobiusComponent_apply, hconv]
    calc
      ζ * (ArithmeticFunction.moebius n : ℝ) =
          ζ * (∑ ν : SmoothHeathBrownMobiusLabel X,
            smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n) := by
              rw [hexp]
      _ = ∑ ν : SmoothHeathBrownMobiusLabel X,
            ζ * smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n := by
              rw [Finset.mul_sum]
      _ = ∑ ν ∈ R, ζ * smoothHeathBrownMobiusComponent
            (dyadicMobiusCutoff X) ν n := hsum.symm

/-- Multiplication by the outer cutoff makes the support-based label filter
exact in the von Mangoldt expansion. -/
theorem smoothHeathBrownVonMangoldtRetainedExpansion {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    polynomialOuterCutoff ((n : ℝ) / X) * ArithmeticFunction.vonMangoldt n =
      ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
        polynomialOuterCutoff ((n : ℝ) / X) *
          smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν n := by
  classical
  let ζ := polynomialOuterCutoff ((n : ℝ) / X)
  let R := smoothHeathBrownVonMangoldtRetainedLabels X
  by_cases hζ : ζ = 0
  · simp [ζ, hζ]
  · have hXpos : 0 < X := by linarith
    have hsupp : (n : ℝ) / X ∈ Set.Icc (3 / 4 : ℝ) (5 / 2 : ℝ) := by
      exact polynomialOuterCutoff_support_subset (by
        simpa [ζ, Function.mem_support] using hζ)
    have hnlo : (3 / 4 : ℝ) * X ≤ (n : ℝ) :=
      (le_div_iff₀ hXpos).mp hsupp.1
    have hnhi : (n : ℝ) ≤ (5 / 2 : ℝ) * X :=
      (div_le_iff₀ hXpos).mp hsupp.2
    have hexp := smoothHeathBrownVonMangoldtExpansion hX hn hnX
    have hsum :
        (∑ ν ∈ R, ζ * smoothHeathBrownVonMangoldtComponent
            (dyadicMobiusCutoff X) ν n) =
          ∑ ν : SmoothHeathBrownVonMangoldtLabel X,
            ζ * smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν n := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro ν hν hνnot
      have hnot : ν ∉ R := hνnot
      have hconv :
          smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
            (smoothHeathBrownVonMangoldtLabelFactors ν) n = 0 := by
        by_contra hconv
        have hRetained : ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X := by
          rw [smoothHeathBrownVonMangoldtRetainedLabels, Finset.mem_filter]
          constructor
          · simp
          · exact ⟨n, hnlo, hnhi, hconv⟩
        exact hnot hRetained
      simp [smoothHeathBrownVonMangoldtComponent_apply, hconv]
    calc
      ζ * ArithmeticFunction.vonMangoldt n =
          ζ * (∑ ν : SmoothHeathBrownVonMangoldtLabel X,
            smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν n) := by
              rw [hexp]
      _ = ∑ ν : SmoothHeathBrownVonMangoldtLabel X,
            ζ * smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν n := by
              rw [Finset.mul_sum]
      _ = ∑ ν ∈ R, ζ * smoothHeathBrownVonMangoldtComponent
            (dyadicMobiusCutoff X) ν n := hsum.symm

/-- Normalized exponent weights for a nonempty scale list. These are the
source weights `log(Nᵢ)/log(P)` because all scales are powers of two. -/
noncomputable def smoothHeathBrownExponentGrouping
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hE : 0 < smoothHeathBrownExponentSum fs) :
    GroupingPredicates fs.length where
  weight i :=
    (smoothHeathBrownFactorExponent (fs.get i) : ℝ) /
      (smoothHeathBrownExponentSum fs : ℝ)
  positive_length := by
    cases fs with
    | nil => simp [smoothHeathBrownExponentSum] at hE
    | cons f fs => simp
  weight_nonneg i := by
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  weight_sum_eq_one := by
    have hsumCast :
        (∑ i : Fin fs.length,
          (smoothHeathBrownFactorExponent (fs.get i) : ℝ)) =
          (smoothHeathBrownExponentSum fs : ℝ) := by
      simp only [smoothHeathBrownExponentSum, Nat.cast_sum]
    change (∑ i ∈ (Finset.univ : Finset (Fin fs.length)),
      (smoothHeathBrownFactorExponent (fs.get i) : ℝ) /
        (smoothHeathBrownExponentSum fs : ℝ)) = 1
    rw [← Finset.sum_div]
    rw [hsumCast]
    exact div_self (by exact_mod_cast (Nat.ne_of_gt hE))

theorem smoothHeathBrownExponentGrouping_weight_eq_log
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hE : 0 < smoothHeathBrownExponentSum fs) (i : Fin fs.length) :
    (smoothHeathBrownExponentGrouping fs hE).weight i =
      Real.log (smoothHeathBrownFactorScale (fs.get i)) /
        Real.log (smoothHeathBrownScaleProduct fs) := by
  have hnum :
      Real.log (smoothHeathBrownFactorScale (fs.get i)) =
        (smoothHeathBrownFactorExponent (fs.get i) : ℝ) * Real.log 2 := by
    rw [smoothHeathBrown_factorScale_eq_powExponent, Real.log_pow]
  have hden :
      Real.log (smoothHeathBrownScaleProduct fs) =
        (smoothHeathBrownExponentSum fs : ℝ) * Real.log 2 := by
    rw [smoothHeathBrownScaleProduct_eq_two_pow_exponentSum, Real.log_pow]
  dsimp [smoothHeathBrownExponentGrouping]
  change (smoothHeathBrownFactorExponent (fs.get i) : ℝ) /
      (smoothHeathBrownExponentSum fs : ℝ) =
        Real.log (smoothHeathBrownFactorScale (fs.get i)) /
          Real.log (smoothHeathBrownScaleProduct fs)
  rw [hnum, hden]
  have hEpos : 0 < (smoothHeathBrownExponentSum fs : ℝ) := by
    exact_mod_cast hE
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [ne_of_gt hEpos, hlog2]

theorem smoothHeathBrownSubgroupWeightSum_eq_log_ratio
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hE : 0 < smoothHeathBrownExponentSum fs)
    (S : Finset (Fin fs.length)) :
    subsetWeightSum (smoothHeathBrownExponentGrouping fs hE) S =
      Real.log (smoothHeathBrownSubgroupScaleProduct fs S) /
        Real.log (smoothHeathBrownScaleProduct fs) := by
  have hsubNum :
      (∑ i ∈ S,
        (smoothHeathBrownFactorExponent (fs.get i) : ℝ)) =
        (smoothHeathBrownSubgroupExponent fs S : ℝ) := by
    simp [smoothHeathBrownSubgroupExponent, Nat.cast_sum]
  have hsubLog :
      Real.log (smoothHeathBrownSubgroupScaleProduct fs S) =
        (smoothHeathBrownSubgroupExponent fs S : ℝ) * Real.log 2 := by
    rw [smoothHeathBrownSubgroupScaleProduct_eq_two_pow_exponent, Real.log_pow]
  have htotalLog :
      Real.log (smoothHeathBrownScaleProduct fs) =
        (smoothHeathBrownExponentSum fs : ℝ) * Real.log 2 := by
    rw [smoothHeathBrownScaleProduct_eq_two_pow_exponentSum, Real.log_pow]
  have hEpos : 0 < (smoothHeathBrownExponentSum fs : ℝ) := by
    exact_mod_cast hE
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  calc
    subsetWeightSum (smoothHeathBrownExponentGrouping fs hE) S =
        (smoothHeathBrownSubgroupExponent fs S : ℝ) /
          (smoothHeathBrownExponentSum fs : ℝ) := by
            change (∑ i ∈ S,
              (smoothHeathBrownFactorExponent (fs.get i) : ℝ) /
                (smoothHeathBrownExponentSum fs : ℝ)) = _
            calc
              _ =
                  (∑ i ∈ S,
                    (smoothHeathBrownFactorExponent (fs.get i) : ℝ)) /
                    (smoothHeathBrownExponentSum fs : ℝ) := by
                      rw [← Finset.sum_div]
              _ = (smoothHeathBrownSubgroupExponent fs S : ℝ) /
                    (smoothHeathBrownExponentSum fs : ℝ) := by rw [hsubNum]
    _ = Real.log (smoothHeathBrownSubgroupScaleProduct fs S) /
          Real.log (smoothHeathBrownScaleProduct fs) := by
            rw [hsubLog, htotalLog]
            field_simp

private theorem smoothHeathBrown_subsetWeightSum_union
    {k : ℕ} (w : GroupingPredicates k) {A B : Finset (Fin k)}
    (hdisj : Disjoint A B) :
    subsetWeightSum w (A ∪ B) =
      subsetWeightSum w A + subsetWeightSum w B := by
  unfold subsetWeightSum
  rw [Finset.sum_union hdisj]

private theorem smoothHeathBrown_subsetWeightSum_univ
    {k : ℕ} (w : GroupingPredicates k) :
    subsetWeightSum w (Finset.univ : Finset (Fin k)) = 1 := by
  simpa [subsetWeightSum] using w.weight_sum_eq_one

/-- The exact source dichotomy for the normalized logarithmic scales:
either one factor has weight at least `3/8`, or three nonempty groups have
the source major type-II scale balance. -/
theorem smoothHeathBrownScaleGroupingAlternatives {X : ℝ}
    (fs : List (SmoothHeathBrownFactor X))
    (hE : 0 < smoothHeathBrownExponentSum fs) :
    (∃ i : Fin fs.length,
      (3 / 8 : ℝ) ≤
        Real.log (smoothHeathBrownFactorScale (fs.get i)) /
          Real.log (smoothHeathBrownScaleProduct fs)) ∨
    (∃ I J K : Finset (Fin fs.length),
      Disjoint I J ∧ Disjoint I K ∧ Disjoint J K ∧
      I ∪ J ∪ K = Finset.univ ∧
      ((1 / 4 : ℝ) ≤
          Real.log (smoothHeathBrownSubgroupScaleProduct fs I) /
            Real.log (smoothHeathBrownScaleProduct fs) ∧
        Real.log (smoothHeathBrownSubgroupScaleProduct fs I) /
            Real.log (smoothHeathBrownScaleProduct fs) ≤ 1 / 2) ∧
      |Real.log (smoothHeathBrownSubgroupScaleProduct fs J) /
          Real.log (smoothHeathBrownScaleProduct fs) -
        Real.log (smoothHeathBrownSubgroupScaleProduct fs K) /
          Real.log (smoothHeathBrownScaleProduct fs)| ≤ 1 / 4 ∧
      I.Nonempty ∧ J.Nonempty ∧ K.Nonempty) := by
  let w := smoothHeathBrownExponentGrouping fs hE
  have hgroup := majorGroupingFiveEighths w
  rcases hgroup with hI | hII
  · rcases hI with ⟨i, hi⟩
    left
    refine ⟨i, ?_⟩
    have hweight : w.weight i =
        Real.log (smoothHeathBrownFactorScale (fs.get i)) /
          Real.log (smoothHeathBrownScaleProduct fs) := by
      simpa [w] using smoothHeathBrownExponentGrouping_weight_eq_log fs hE i
    norm_num at hi ⊢
    change (3 / 8 : ℝ) ≤
      Real.log (smoothHeathBrownFactorScale (fs.get i)) /
        Real.log (smoothHeathBrownScaleProduct fs)
    rw [← hweight]
    exact hi
  · rcases hII with ⟨I, J, K, hIJ, hIK, hJK, hcover,
      hIlow, hIhigh, hbalance⟩
    have hIlow' : (1 / 4 : ℝ) ≤ subsetWeightSum w I := by
      norm_num at hIlow
      exact hIlow
    have hIhigh' : subsetWeightSum w I ≤ (1 / 2 : ℝ) := by
      norm_num at hIhigh
      exact hIhigh
    have hbalance' :
        |subsetWeightSum w J - subsetWeightSum w K| ≤ (1 / 4 : ℝ) := by
      norm_num at hbalance
      exact hbalance
    have hdisjUnion : Disjoint (I ∪ J) K := by
      rw [Finset.disjoint_left]
      intro i hi hk
      rcases Finset.mem_union.mp hi with hiI | hiJ
      · exact (Finset.disjoint_left.mp hIK) hiI hk
      · exact (Finset.disjoint_left.mp hJK) hiJ hk
    have hsumAll : subsetWeightSum w I + subsetWeightSum w J +
        subsetWeightSum w K = 1 := by
      calc
        subsetWeightSum w I + subsetWeightSum w J + subsetWeightSum w K =
            subsetWeightSum w (I ∪ J) + subsetWeightSum w K := by
              rw [smoothHeathBrown_subsetWeightSum_union w hIJ]
        _ = subsetWeightSum w ((I ∪ J) ∪ K) :=
              (smoothHeathBrown_subsetWeightSum_union w hdisjUnion).symm
        _ = subsetWeightSum w Finset.univ := by rw [hcover]
        _ = 1 := smoothHeathBrown_subsetWeightSum_univ w
    have hsumJKlo :
        (1 / 2 : ℝ) ≤ subsetWeightSum w J + subsetWeightSum w K := by
      linarith [hsumAll, hIhigh']
    have hbalanceParts := abs_le.mp hbalance'
    have hJlo : (1 / 8 : ℝ) ≤ subsetWeightSum w J := by
      linarith [hsumJKlo, hbalanceParts.1]
    have hKlo : (1 / 8 : ℝ) ≤ subsetWeightSum w K := by
      linarith [hsumJKlo, hbalanceParts.2]
    have hIne : I.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hEq
      rw [hEq] at hIlow'
      simp [subsetWeightSum] at hIlow'
      norm_num at hIlow'
    have hJne : J.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hEq
      rw [hEq] at hJlo
      simp [subsetWeightSum] at hJlo
      norm_num at hJlo
    have hKne : K.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hEq
      rw [hEq] at hKlo
      simp [subsetWeightSum] at hKlo
      norm_num at hKlo
    have hIlog := smoothHeathBrownSubgroupWeightSum_eq_log_ratio fs hE I
    have hJlog := smoothHeathBrownSubgroupWeightSum_eq_log_ratio fs hE J
    have hKlog := smoothHeathBrownSubgroupWeightSum_eq_log_ratio fs hE K
    right
    refine ⟨I, J, K, hIJ, hIK, hJK, hcover, ?_, ?_, hIne, hJne, hKne⟩
    · constructor
      · rw [← hIlog]
        exact hIlow'
      · rw [← hIlog]
        exact hIhigh'
    · rw [← hJlog, ← hKlog]
      exact hbalance'

/-- The fixed cutoff `z=(4X)^(1/10)` is small enough for the source's
large-scale Möbius exclusion once `X≥2^35`. -/
theorem smoothHeathBrownLarge_cutoff_power_bound {X : ℝ}
    (hX : (2 : ℝ) ^ 35 ≤ X) :
    (2 * dyadicMobiusCutoff X) ^ 8 ≤ (X / (2 : ℝ) ^ 22) ^ 3 := by
  let z := dyadicMobiusCutoff X
  have hX0 : 0 ≤ X := by
    have hpow : 0 < (2 : ℝ) ^ 35 := by positivity
    linarith
  have hz10 : z ^ 10 = 4 * X := by
    dsimp [z]
    exact dyadicMobiusCutoff_pow hX0
  have hX11 : (2 : ℝ) ^ 378 ≤ X ^ 11 := by
    calc
      (2 : ℝ) ^ 378 ≤ (2 : ℝ) ^ 385 :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = ((2 : ℝ) ^ 35) ^ 11 := by rw [← pow_mul]
      _ ≤ X ^ 11 := pow_le_pow_left₀ (by positivity) hX 11
  have hz40 : z ^ 40 = (4 * X) ^ 4 := by
    change z ^ (10 * 4) = (4 * X) ^ 4
    rw [pow_mul, hz10]
  have hmul :
      (2 * z) ^ 40 * ((2 : ℝ) ^ 22) ^ 15 ≤ X ^ 15 := by
    have hleft :
        (2 * z) ^ 40 * ((2 : ℝ) ^ 22) ^ 15 =
          (2 : ℝ) ^ 378 * X ^ 4 := by
      rw [mul_pow, hz40, mul_pow]
      have hfour : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [hfour, ← pow_mul]
      have hcoeff :
          (2 : ℝ) ^ 40 * (2 : ℝ) ^ (2 * 4) * (2 : ℝ) ^ (22 * 15) =
            (2 : ℝ) ^ 378 := by
        rw [← pow_add, ← pow_add]
      have hpow22 : ((2 : ℝ) ^ 22) ^ 15 = (2 : ℝ) ^ (22 * 15) := by
        rw [pow_mul]
      calc
        (2 : ℝ) ^ 40 * ((2 : ℝ) ^ (2 * 4) * X ^ 4) *
            ((2 : ℝ) ^ 22) ^ 15 =
            ((2 : ℝ) ^ 40 * (2 : ℝ) ^ (2 * 4) *
              (2 : ℝ) ^ (22 * 15)) * X ^ 4 := by rw [hpow22]; ring
        _ = (2 : ℝ) ^ 378 * X ^ 4 := by rw [hcoeff]
    rw [hleft]
    calc
      (2 : ℝ) ^ 378 * X ^ 4 = X ^ 4 * (2 : ℝ) ^ 378 := by ring
      _ ≤ X ^ 4 * X ^ 11 :=
        mul_le_mul_of_nonneg_left hX11 (pow_nonneg hX0 4)
      _ = X ^ 15 := by rw [← pow_add]
  have hfive :
      ((2 * z) ^ 8) ^ 5 ≤ ((X / (2 : ℝ) ^ 22) ^ 3) ^ 5 := by
    have hleftPow : ((2 * z) ^ 8) ^ 5 = (2 * z) ^ 40 := by
      rw [← pow_mul]
    have hrightPow :
        ((X / (2 : ℝ) ^ 22) ^ 3) ^ 5 =
          X ^ 15 / ((2 : ℝ) ^ 22) ^ 15 := by
      rw [← pow_mul, div_pow]
    rw [hleftPow, hrightPow]
    apply (le_div_iff₀ (by positivity : 0 < ((2 : ℝ) ^ 22) ^ 15)).2
    simpa [mul_comm] using hmul
  have hleftNonneg : 0 ≤ (2 * z) ^ 8 := by positivity
  have hrightNonneg : 0 ≤ (X / (2 : ℝ) ^ 22) ^ 3 := by positivity
  exact (pow_le_pow_iff_left₀ hleftNonneg hrightNonneg (by norm_num)).mp hfive

private theorem smoothHeathBrownConvolution_mem_nonzero_factor
    {X z : ℝ} {fs : List (SmoothHeathBrownFactor X)} {n : ℕ}
    (hne : smoothHeathBrownConvolutionFactors z fs n ≠ 0)
    {f : SmoothHeathBrownFactor X} (hf : f ∈ fs) :
    ∃ m : ℕ, smoothHeathBrownFactorFunction z f m ≠ 0 := by
  induction fs generalizing n f with
  | nil => simp at hf
  | cons g gs ih =>
      have hmul :
          (smoothHeathBrownFactorFunction z g *
            smoothHeathBrownConvolutionFactors z gs) n ≠ 0 := by
        simpa [smoothHeathBrownConvolutionFactors] using hne
      obtain ⟨x, hx, hhead, htail⟩ := smoothHeathBrown_mul_apply_ne_zero hmul
      rcases List.mem_cons.mp hf with hfg | hftail
      · subst f
        exact ⟨x.1, hhead⟩
      · exact ih htail hftail

/-- At sufficiently large `X`, a retained component cannot have a factor
of relative logarithmic scale at least `3/8` that is still a truncated
Möbius factor. -/
theorem smoothHeathBrownLargeFactor_not_mobius {X : ℝ}
    (hX : (2 : ℝ) ^ 35 ≤ X)
    {fs : List (SmoothHeathBrownFactor X)}
    (hlen : fs.length ≤ 20)
    (hfsne : fs ≠ [])
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fs)
    (i : Fin fs.length)
    (hi : (3 / 8 : ℝ) ≤
      Real.log (smoothHeathBrownFactorScale (fs.get i)) /
        Real.log (smoothHeathBrownScaleProduct fs)) :
    ∀ j : SmoothHeathBrownScaleIndex X, fs.get i ≠ .mobius j := by
  have hX0 : 0 ≤ X := by
    have hpos : 0 < (2 : ℝ) ^ 35 := by positivity
    linarith
  have hscaleWindow := smoothHeathBrownSupportRetained_scale_bounds
    hlen hfsne hX0 hret
  have hXlo : (2 : ℝ) ^ 13 ≤ X / (2 : ℝ) ^ 22 := by
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 22)).2
    calc
      (2 : ℝ) ^ 13 * (2 : ℝ) ^ 22 = (2 : ℝ) ^ 35 := by
        rw [← pow_add]
      _ ≤ X := hX
  have hPlo : (2 : ℝ) ^ 13 ≤ smoothHeathBrownScaleProduct fs :=
    le_trans hXlo hscaleWindow.1
  have hEpos : 0 < smoothHeathBrownExponentSum fs := by
    by_contra hnot
    have hzero : smoothHeathBrownExponentSum fs = 0 := Nat.eq_zero_of_not_pos hnot
    rw [smoothHeathBrownScaleProduct_eq_two_pow_exponentSum, hzero] at hPlo
    norm_num at hPlo
  have hweight := smoothHeathBrownExponentGrouping_weight_eq_log fs hEpos i
  have hw : (3 / 8 : ℝ) ≤
      (smoothHeathBrownFactorExponent (fs.get i) : ℝ) /
        (smoothHeathBrownExponentSum fs : ℝ) := by
    have hwi : (3 / 8 : ℝ) ≤
        (smoothHeathBrownExponentGrouping fs hEpos).weight i := by
      rw [hweight]
      exact hi
    simpa [smoothHeathBrownExponentGrouping] using hwi
  have hEreal : 0 < (smoothHeathBrownExponentSum fs : ℝ) := by
    exact_mod_cast hEpos
  have hnatReal :
      3 * (smoothHeathBrownExponentSum fs : ℝ) ≤
        8 * (smoothHeathBrownFactorExponent (fs.get i) : ℝ) := by
    have hmul := (le_div_iff₀ hEreal).mp hw
    nlinarith
  have hnat :
      3 * smoothHeathBrownExponentSum fs ≤
        8 * smoothHeathBrownFactorExponent (fs.get i) := by
    exact_mod_cast hnatReal
  have hpow :
      (2 : ℝ) ^ (3 * smoothHeathBrownExponentSum fs) ≤
        (2 : ℝ) ^ (8 * smoothHeathBrownFactorExponent (fs.get i)) :=
    pow_le_pow_right₀ (by norm_num) hnat
  have hPpow : smoothHeathBrownScaleProduct fs ^ 3 =
      (2 : ℝ) ^ (3 * smoothHeathBrownExponentSum fs) := by
    calc
      smoothHeathBrownScaleProduct fs ^ 3 =
          ((2 : ℝ) ^ smoothHeathBrownExponentSum fs) ^ 3 := by
            rw [smoothHeathBrownScaleProduct_eq_two_pow_exponentSum]
      _ = (2 : ℝ) ^ (smoothHeathBrownExponentSum fs * 3) := by
            rw [← pow_mul]
      _ = (2 : ℝ) ^ (3 * smoothHeathBrownExponentSum fs) := by
            congr 1
            omega
  have hNpow : smoothHeathBrownFactorScale (fs.get i) ^ 8 =
      (2 : ℝ) ^ (8 * smoothHeathBrownFactorExponent (fs.get i)) := by
    calc
      smoothHeathBrownFactorScale (fs.get i) ^ 8 =
          ((2 : ℝ) ^ smoothHeathBrownFactorExponent (fs.get i)) ^ 8 := by
            rw [smoothHeathBrown_factorScale_eq_powExponent]
      _ = (2 : ℝ) ^ (smoothHeathBrownFactorExponent (fs.get i) * 8) := by
            rw [← pow_mul]
      _ = (2 : ℝ) ^ (8 * smoothHeathBrownFactorExponent (fs.get i)) := by
            congr 1
            omega
  have hP_le_N : smoothHeathBrownScaleProduct fs ^ 3 ≤
      smoothHeathBrownFactorScale (fs.get i) ^ 8 := by
    rw [hPpow, hNpow]
    exact hpow
  have hscaleLowerCube :
      (X / (2 : ℝ) ^ 22) ^ 3 ≤ smoothHeathBrownScaleProduct fs ^ 3 :=
    pow_le_pow_left₀ (by positivity) hscaleWindow.1 3
  have hcut := smoothHeathBrownLarge_cutoff_power_bound hX
  intro j hEq
  obtain ⟨_, _, _, hconv⟩ := hret
  obtain ⟨m, hm⟩ := smoothHeathBrownConvolution_mem_nonzero_factor
    hconv (List.get_mem fs i)
  have hmobiusFactor : smoothHeathBrownFactorFunction
      (dyadicMobiusCutoff X) (.mobius j) m ≠ 0 := by
    rw [← hEq]
    exact hm
  have hfactorBounds := smoothHeathBrownFactorFunction_support_bounds
    (.mobius j) hmobiusFactor
  have hmne : m ≠ 0 := by
    intro hmzero
    subst m
    simp [smoothHeathBrownFactorFunction, smoothHeathBrownMobiusFactor]
      at hmobiusFactor
  have hmu : truncatedMobius (dyadicMobiusCutoff X) m ≠ 0 := by
    intro hzero
    apply hmobiusFactor
    simp [smoothHeathBrownFactorFunction, smoothHeathBrownMobiusFactor,
      hmne, hzero]
  have hmle : (m : ℝ) ≤ dyadicMobiusCutoff X := by
    by_contra h
    exact hmu (truncatedMobius_apply_of_not_le h)
  have hlargeN : smoothHeathBrownFactorScale (.mobius j) <
      2 * dyadicMobiusCutoff X := by
    have hmUpper : (m : ℝ) < 2 * dyadicMobiusCutoff X := by
      nlinarith [hfactorBounds.1, hmle]
    nlinarith [hfactorBounds.1, hmUpper]
  have hlargePow : smoothHeathBrownFactorScale (.mobius j) ^ 8 <
      (2 * dyadicMobiusCutoff X) ^ 8 :=
    pow_lt_pow_left₀ hlargeN
      (smoothHeathBrownFactorScale_pos (.mobius j)).le (by norm_num)
  have hP_le_N' := hP_le_N
  rw [hEq] at hP_le_N'
  linarith [hscaleLowerCube, hP_le_N', hlargePow, hcut]

/-- Exact retained scale dichotomy: a large factor is non-Möbius, or three
nonempty scale groups satisfy the prescribed source balance. -/
theorem smoothHeathBrownRetainedScaleAlternatives {X : ℝ}
    (hX : (2 : ℝ) ^ 35 ≤ X)
    {fs : List (SmoothHeathBrownFactor X)}
    (hlen : fs.length ≤ 20)
    (hfsne : fs ≠ [])
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fs) :
    (∃ i : Fin fs.length,
      (3 / 8 : ℝ) ≤
        Real.log (smoothHeathBrownFactorScale (fs.get i)) /
          Real.log (smoothHeathBrownScaleProduct fs) ∧
        (∀ j : SmoothHeathBrownScaleIndex X, fs.get i ≠ .mobius j)) ∨
    (∃ I J K : Finset (Fin fs.length),
      Disjoint I J ∧ Disjoint I K ∧ Disjoint J K ∧
      I ∪ J ∪ K = Finset.univ ∧
      ((1 / 4 : ℝ) ≤
          Real.log (smoothHeathBrownSubgroupScaleProduct fs I) /
            Real.log (smoothHeathBrownScaleProduct fs) ∧
        Real.log (smoothHeathBrownSubgroupScaleProduct fs I) /
            Real.log (smoothHeathBrownScaleProduct fs) ≤ 1 / 2) ∧
      |Real.log (smoothHeathBrownSubgroupScaleProduct fs J) /
          Real.log (smoothHeathBrownScaleProduct fs) -
        Real.log (smoothHeathBrownSubgroupScaleProduct fs K) /
          Real.log (smoothHeathBrownScaleProduct fs)| ≤ 1 / 4 ∧
      I.Nonempty ∧ J.Nonempty ∧ K.Nonempty) := by
  have hX0 : 0 ≤ X := by
    have hpos : 0 < (2 : ℝ) ^ 35 := by positivity
    linarith
  have hwindow := smoothHeathBrownSupportRetained_scale_bounds
    hlen hfsne hX0 hret
  have hXlo : (2 : ℝ) ^ 13 ≤ X / (2 : ℝ) ^ 22 := by
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 22)).2
    calc
      (2 : ℝ) ^ 13 * (2 : ℝ) ^ 22 = (2 : ℝ) ^ 35 := by
        rw [← pow_add]
      _ ≤ X := hX
  have hPgt : 1 < smoothHeathBrownScaleProduct fs := by
    have hone : 1 < (2 : ℝ) ^ 13 := by norm_num
    exact lt_of_lt_of_le hone (le_trans hXlo hwindow.1)
  have hEpos : 0 < smoothHeathBrownExponentSum fs := by
    by_contra hnot
    have hzero : smoothHeathBrownExponentSum fs = 0 := Nat.eq_zero_of_not_pos hnot
    rw [smoothHeathBrownScaleProduct_eq_two_pow_exponentSum, hzero] at hPgt
    norm_num at hPgt
  rcases smoothHeathBrownScaleGroupingAlternatives fs hEpos with hI | hII
  · rcases hI with ⟨i, hi⟩
    exact Or.inl ⟨i, hi,
      smoothHeathBrownLargeFactor_not_mobius hX hlen hfsne hret i hi⟩
  · exact Or.inr hII

end

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownConvolutionFactors_support_bounds
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusRetainedExpansion
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownScaleGroupingAlternatives
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownLargeFactor_not_mobius
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownRetainedScaleAlternatives
