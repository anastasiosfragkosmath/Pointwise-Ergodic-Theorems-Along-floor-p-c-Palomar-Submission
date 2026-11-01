module

public import FractionalPrimes.Literature.Twisted.SelectedVonMangoldtGroupCoefficientBound
public import FractionalPrimes.Literature.Twisted.ShiftedConvolutionSmallFactor
public import FractionalPrimes.Literature.Twisted.CharacterEvalNorm

/-!
# Truncated factor extraction for a selected von Mangoldt group

This is the finite, source-faithful transfer from local estimates on one
selected factor to a group sum over an arbitrary half-open interval. The
local cancellation estimate is an explicit hypothesis. The other factors
contribute at most the unique logarithmic mass `log (8 * X)`.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

private def selectedExtractionTupleFinCongr {k l r : ℕ}
    (e : Fin k ≃ Fin l) :
    divisorFactorTuples k r ≃ divisorFactorTuples l r where
  toFun d := ⟨fun i => d.1 (e.symm i), by
    calc
      (∏ i : Fin l, (d.1 (e.symm i)).1) =
          ∏ i : Fin k, (d.1 i).1 :=
        Fintype.prod_equiv e.symm _ _ (by intro i; rfl)
      _ = r := d.2⟩
  invFun d := ⟨fun i => d.1 (e i), by
    calc
      (∏ i : Fin k, (d.1 (e i)).1) =
          ∏ i : Fin l, (d.1 i).1 :=
        Fintype.prod_equiv e _ _ (by intro i; rfl)
      _ = r := d.2⟩
  left_inv d := by
    apply Subtype.ext
    funext i
    simp
  right_inv d := by
    apply Subtype.ext
    funext i
    simp

private theorem selectedExtractionTupleFinCongr_coordinate
    {k l r : ℕ} (e : Fin k ≃ Fin l)
    (d : divisorFactorTuples k r) (i : Fin l) :
    ((selectedExtractionTupleFinCongr e d).1 i) = d.1 (e.symm i) := rfl

private theorem selectedExtractionTupleFinCongr_residual
    {k l r : ℕ} (e : Fin k ≃ Fin l)
    (he : ∀ i j : Fin k, e i ≤ e j ↔ i ≤ j)
    (d : divisorFactorTuples k r) (i : Fin l) :
    factorExtractionAllocationResidual (selectedExtractionTupleFinCongr e d) i =
      factorExtractionAllocationResidual d (e.symm i) := by
  classical
  have hprod :
      (∏ j ∈ Finset.Iic i,
        ((selectedExtractionTupleFinCongr e d).1 j).1) =
      ∏ j ∈ Finset.Iic (e.symm i), (d.1 j).1 := by
    refine Finset.prod_bij (fun j _ => e.symm j) ?_ ?_ ?_ ?_
    · intro j hj
      apply Finset.mem_Iic.mpr
      apply (he (e.symm j) (e.symm i)).mp
      simpa using (Finset.mem_Iic.mp hj)
    · intro j₁ hj₁ j₂ hj₂ hEq
      exact e.symm.injective hEq
    · intro b hb
      refine ⟨e b, ?_, ?_⟩
      · apply Finset.mem_Iic.mpr
        have hb' : b ≤ e.symm i := Finset.mem_Iic.mp hb
        have hbe : e b ≤ e (e.symm i) := (he b (e.symm i)).mpr hb'
        simpa using hbe
      · simp
    · intro j hj
      rfl
  simp only [factorExtractionAllocationResidual]
  rw [hprod]

private theorem selectedExtractionTupleFinCongr_residual_of_cast
    {k l r : ℕ} (e : Fin k ≃ Fin l)
    (he : ∀ i j : Fin k, e i ≤ e j ↔ i ≤ j)
    (d : divisorFactorTuples k r) (i : Fin l) :
    factorExtractionAllocationResidual (selectedExtractionTupleFinCongr e d) i =
      factorExtractionAllocationResidual d (e.symm i) :=
  selectedExtractionTupleFinCongr_residual e he d i

private theorem selectedExtraction_dyadicInterval_real_bounds {j n : ℕ}
    (h : inDyadicInterval j n) :
    dyadicScale j < (n : ℝ) ∧ (n : ℝ) ≤ 2 * dyadicScale j := by
  by_cases hj : j = 0
  · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h.1
    have hnle : n ≤ 1 := by
      simpa [inDyadicInterval, dyadicUpperNat, hj] using h.2
    have hn : n = 1 := by omega
    simp [dyadicScale, hj, hn]
    norm_num
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hscale : dyadicScale j = (dyadicLowerNat j : ℝ) := by
      simp [dyadicScale, dyadicLowerNat, hj]
    have hjEq : j.pred + 1 = j := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hjpos
    have hpow : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ j.pred := by
      calc
        (2 : ℝ) ^ j = (2 : ℝ) ^ (j.pred + 1) :=
          congrArg (fun k : ℕ => (2 : ℝ) ^ k) hjEq.symm
        _ = (2 : ℝ) ^ j.pred * 2 := by rw [pow_succ]
        _ = 2 * (2 : ℝ) ^ j.pred := by ring
    have hupper : (dyadicUpperNat j : ℝ) = 2 * dyadicScale j := by
      simp only [dyadicUpperNat, Nat.cast_pow, Nat.cast_ofNat]
      rw [hpow, dyadicScale, if_neg hj]
    constructor
    · rw [hscale]
      exact_mod_cast h.1
    · rw [← hupper]
      exact_mod_cast h.2

private theorem selectedExtraction_factor_support_bounds {X z : ℝ}
    (f : DyadicArithmeticFactor X) {n : ℕ}
    (hne : dyadicFactorFunction z f n ≠ 0) :
    dyadicFactorScale f < (n : ℝ) ∧
      (n : ℝ) ≤ 2 * dyadicFactorScale f := by
  cases f with
  | one j =>
      have hI : inDyadicInterval j.val.val n := by
        by_contra hI
        apply hne
        simp [dyadicFactorFunction, dyadicOneFactor_apply, hI]
      exact selectedExtraction_dyadicInterval_real_bounds hI
  | logarithm j =>
      have hI : inDyadicInterval j.val.val n := by
        by_contra hI
        apply hne
        simp [dyadicFactorFunction, dyadicLogFactor_apply, hI]
      exact selectedExtraction_dyadicInterval_real_bounds hI
  | mobius j =>
      have hI : inDyadicInterval j.val.val n := by
        by_contra hI
        apply hne
        simp [dyadicFactorFunction, dyadicMobiusFactor_apply, hI]
      exact selectedExtraction_dyadicInterval_real_bounds hI

private theorem selectedExtraction_factorScale_pos {X : ℝ}
    (f : DyadicArithmeticFactor X) : 0 < dyadicFactorScale f := by
  cases f with
  | one j =>
      by_cases hj : j.val.val = 0 <;>
        simp [dyadicFactorScale, dyadicScale, hj] <;> positivity
  | logarithm j =>
      by_cases hj : j.val.val = 0 <;>
        simp [dyadicFactorScale, dyadicScale, hj] <;> positivity
  | mobius j =>
      by_cases hj : j.val.val = 0 <;>
        simp [dyadicFactorScale, dyadicScale, hj] <;> positivity

private theorem selectedExtraction_factorMass_ge_one
    {X : ℝ} (hX : 3 ≤ X) (f : DyadicArithmeticFactor X) :
    1 ≤ dyadicFactorMassWeight f := by
  cases f with
  | one j => simp [dyadicFactorMassWeight]
  | mobius j => simp [dyadicFactorMassWeight]
  | logarithm j =>
      dsimp [dyadicFactorMassWeight]
      exact (log_eightX_gt_one hX).le

/-- The selected von Mangoldt group sum retains an arbitrary half-open
cutoff. Exact gcd allocations and support intersections are handled by the
checked generic factor-extraction theorem. The only analytic input is the
explicit local estimate `hshort` for the selected factor and every
allocation. -/
theorem selectedVonMangoldtGroup_truncatedFactorExtraction
    {X z t ε x y : ℝ} (hX : 3 ≤ X)
    (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    (i₀ : Fin (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length)
    {r Q : ℕ} (hr : 1 ≤ r) (χ : BlueprintCharacter Q)
    (hε : 0 ≤ ε) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hshort : ∀ d : divisorFactorTuples
        (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length r,
      ∀ u v : ℝ, 0 ≤ u →
      Set.Ioc u v ⊆ Set.Ioc
        (dyadicFactorScale
          ((selectedDyadicFactors (vonMangoldtLabelFactors ν) I).get i₀) /
            ((d.1 i₀).1 : ℝ))
        (2 * (dyadicFactorScale
          ((selectedDyadicFactors (vonMangoldtLabelFactors ν) I).get i₀) /
            ((d.1 i₀).1 : ℝ))) →
      ‖∑ m ∈ factorExtractionRealInterval u v,
        factorExtractionAllocatedFactor
          (fun j n => dyadicFactorComplexFunction z
            ((selectedDyadicFactors (vonMangoldtLabelFactors ν) I).get j) n)
          (fun j => (d.1 j).1)
          (fun j => factorExtractionAllocationResidual d j)
          (factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) t) i₀ m‖ ≤
        ε * Real.sqrt
          (dyadicFactorScale
            ((selectedDyadicFactors (vonMangoldtLabelFactors ν) I).get i₀) /
              ((d.1 i₀).1 : ℝ))) :
    ‖(dyadicBinomialCoefficient ν.1 : ℂ) *
      ∑ n ∈ factorExtractionRealInterval x y,
        dyadicFactorComplexProduct z
          (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) (r * n) *
          factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) t n‖ ≤
      (2 : ℝ) ^ 10 *
        (3 : ℝ) ^
          ((selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length - 1) *
        (divisorFunction
          (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length
          ⟨r, lt_of_lt_of_le (by decide) hr⟩ : ℝ) *
        ε * Real.sqrt
          (dyadicFactorScaleProduct
            (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) /
              (r : ℝ)) * Real.log (8 * X) := by
  classical
  let factors := selectedDyadicFactors (vonMangoldtLabelFactors ν) I
  let cfactors : List (ArithmeticFunction ℂ) :=
    factors.map (dyadicFactorComplexFunction z)
  have hlen : cfactors.length = factors.length := by simp [cfactors]
  let e : Fin cfactors.length ≃ Fin factors.length := finCongr hlen
  let k := cfactors.length
  let N : Fin k → ℝ := fun j => dyadicFactorScale (factors.get (e j))
  let B : Fin k → ℝ := fun j => dyadicFactorMassWeight (factors.get (e j))
  let χnat : ℕ → ℂ := fun m => evalInt χ (m : ℤ)
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  have hN : ∀ j, 0 < N j := by
    intro j
    exact selectedExtraction_factorScale_pos (factors.get (e j))
  have hB : ∀ j, 0 ≤ B j := by
    intro j
    exact dyadicFactorMassWeight_nonneg hX (factors.get (e j))
  have hε' : 0 ≤ ε := hε
  have hcoeff : ∀ j n, ‖cfactors.get j n‖ ≤ B j := by
    intro j n
    have hget : cfactors.get j =
        dyadicFactorComplexFunction z (factors.get (e j)) := by
      simp [cfactors, e, k]
    rw [hget]
    simpa [B, dyadicFactorComplexFunction,
      Complex.norm_real, Real.norm_eq_abs] using
        dyadicFactorFunction_abs_le_massWeight hX z (factors.get (e j)) n
  have hsupport : ∀ j n, cfactors.get j n ≠ 0 →
      N j < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N j := by
    intro j n hne
    have hget : cfactors.get j =
        dyadicFactorComplexFunction z (factors.get (e j)) := by
      simp [cfactors, e, k]
    rw [hget] at hne
    have hne' :
        ((dyadicFactorFunction z (factors.get (e j)) n : ℝ) : ℂ) ≠ 0 := by
      simpa [dyadicFactorComplexFunction] using hne
    have hreal : dyadicFactorFunction z (factors.get (e j)) n ≠ 0 := by
      intro hz0
      apply hne'
      exact_mod_cast hz0
    simpa [N] using
      selectedExtraction_factor_support_bounds (factors.get (e j)) hreal
  have hχnorm : ∀ m, 0 < m → ‖χnat m‖ ≤ 1 := by
    intro m hm
    exact evalInt_norm_le_one χ (m : ℤ)
  have hχone : χnat 1 = 1 := by simp [χnat, evalInt]
  have hχmul : ∀ m n, χnat (m * n) = χnat m * χnat n := by
    intro m n
    simp [χnat, evalInt, Int.cast_mul]
  have heOrder : ∀ i j : Fin cfactors.length, e i ≤ e j ↔ i ≤ j := by
    intro i j
    rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val]
    simp [e]
  have hcfget (j : Fin cfactors.length) :
      cfactors.get j = dyadicFactorComplexFunction z (factors.get (e j)) := by
    simp [cfactors, e]
  have hshort' : ∀ d : divisorFactorTuples cfactors.length r,
      ∀ u v : ℝ, 0 ≤ u →
      Set.Ioc u v ⊆ Set.Ioc
        (N (e.symm i₀) / ((d.1 (e.symm i₀)).1 : ℝ))
        (2 * (N (e.symm i₀) / ((d.1 (e.symm i₀)).1 : ℝ))) →
      ‖∑ m ∈ factorExtractionRealInterval u v,
        factorExtractionAllocatedFactor
          (fun j n => cfactors.get j n)
          (fun j => (d.1 j).1)
          (fun j => factorExtractionAllocationResidual d j)
          (factorExtractionMellinWeight χnat t) (e.symm i₀) m‖ ≤
        ε * Real.sqrt
          (N (e.symm i₀) / ((d.1 (e.symm i₀)).1 : ℝ)) := by
    intro d u v hu hsub
    let d₀ : divisorFactorTuples factors.length r :=
      selectedExtractionTupleFinCongr e d
    have hdcoord (j : Fin cfactors.length) : d₀.1 (e j) = d.1 j := by
      change d.1 (e.symm (e j)) = d.1 j
      simp
    have hdresid (j : Fin cfactors.length) :
        factorExtractionAllocationResidual d₀ (e j) =
          factorExtractionAllocationResidual d j := by
      simpa [Function.comp] using
        (selectedExtractionTupleFinCongr_residual e heOrder d (e j))
    have hdi : (d₀.1 i₀).1 = (d.1 (e.symm i₀)).1 := by
      simpa [e] using
        congrArg Subtype.val
          (selectedExtractionTupleFinCongr_coordinate e d i₀)
    have hNi : N (e.symm i₀) = dyadicFactorScale (factors.get i₀) := by
      simp [N]
    have hsub' : Set.Ioc u v ⊆ Set.Ioc
        (dyadicFactorScale (factors.get i₀) /
          ((d₀.1 i₀).1 : ℝ))
        (2 * (dyadicFactorScale (factors.get i₀) /
          ((d₀.1 i₀).1 : ℝ))) := by
      simpa [hdi, hNi] using hsub
    have hsource := hshort d₀ u v hu hsub'
    have hterms (m : ℕ) :
        factorExtractionAllocatedFactor
          (fun j n => cfactors.get j n)
          (fun j => (d.1 j).1)
          (fun j => factorExtractionAllocationResidual d j)
          (factorExtractionMellinWeight χnat t) (e.symm i₀) m =
        factorExtractionAllocatedFactor
          (fun j n => dyadicFactorComplexFunction z (factors.get j) n)
          (fun j => (d₀.1 j).1)
          (fun j => factorExtractionAllocationResidual d₀ j)
          (factorExtractionMellinWeight χnat t) i₀ m := by
      have heq : e (e.symm i₀) = i₀ := e.apply_symm_apply i₀
      have hcoord := hdcoord (e.symm i₀)
      have hres := hdresid (e.symm i₀)
      rw [heq] at hcoord hres
      simp only [factorExtractionAllocatedFactor]
      rw [show cfactors.get (e.symm i₀) =
          dyadicFactorComplexFunction z (factors.get i₀) from by
            simpa [heq] using hcfget (e.symm i₀)]
      simp only [e.apply_symm_apply, hcoord]
      simp [hres]
    have hsum := congrArg
      (fun f : ℕ → ℂ => ∑ m ∈ factorExtractionRealInterval u v, f m)
      (funext hterms)
    rw [hsum]
    simpa only [hNi, hdi] using hsource
  have hsmall := shiftedConvolutionSmallFactor
    cfactors hr0 (e.symm i₀) N B χnat t ε hN hB hε'
    hcoeff hsupport hχnorm hχone hχmul hshort' hx hxy
  have hmass := selectedVonMangoldtGroup_massWeight_le hX ν I
  have hBprod : ∏ j ∈ Finset.univ.erase (e.symm i₀), B j ≤
      Real.log (8 * X) := by
    have hsub : Finset.univ.erase (e.symm i₀) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hdrop := Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun j _ => dyadicFactorMassWeight_nonneg hX (factors.get (e j)))
      (fun j _ _ => selectedExtraction_factorMass_ge_one hX
        (factors.get (e j)))
    have hprodAll : (∏ j : Fin cfactors.length, B j) =
        dyadicFactorsMassWeight factors := by
      calc
        (∏ j : Fin cfactors.length, B j) =
            ∏ j : Fin factors.length,
              dyadicFactorMassWeight (factors.get j) :=
          Fintype.prod_equiv e _ _ (by intro j; rfl)
        _ = dyadicFactorsMassWeight factors := by
          simpa [dyadicFactorsMassWeight, List.get_eq_getElem] using
            (Fin.prod_univ_fun_getElem factors dyadicFactorMassWeight)
    calc
      ∏ j ∈ Finset.univ.erase (e.symm i₀), B j ≤
          ∏ j : Fin cfactors.length, B j := by
            simpa [B] using hdrop
      _ = dyadicFactorsMassWeight factors := hprodAll
      _ ≤ Real.log (8 * X) := by
            simpa [factors] using hmass
  have hNprod : (∏ j : Fin cfactors.length, N j) =
      dyadicFactorScaleProduct factors := by
    calc
      (∏ j : Fin cfactors.length, N j) =
          ∏ j : Fin factors.length,
            dyadicFactorScale (factors.get j) :=
        Fintype.prod_equiv e _ _ (by intro j; rfl)
      _ = dyadicFactorScaleProduct factors := by
        simpa [dyadicFactorScaleProduct, List.get_eq_getElem] using
          (Fin.prod_univ_fun_getElem factors dyadicFactorScale)
  have hsmallCore :
      ‖∑ n ∈ factorExtractionRealInterval x y,
        dyadicFactorComplexProduct z factors (r * n) *
          factorExtractionMellinWeight χnat t n‖ ≤
        (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) * ε *
        Real.sqrt ((∏ j : Fin cfactors.length, N j) / (r : ℝ)) *
          ∏ j ∈ Finset.univ.erase (e.symm i₀), B j := by
    simpa [cfactors, factors, k, dyadicFactorComplexProduct, N, hlen] using hsmall
  have hsmallCore' :
      ‖∑ n ∈ factorExtractionRealInterval x y,
        dyadicFactorComplexProduct z factors (r * n) *
          factorExtractionMellinWeight χnat t n‖ ≤
        (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) * ε *
          Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) *
          ∏ j ∈ Finset.univ.erase (e.symm i₀), B j := by
    simpa only [hNprod] using hsmallCore
  have hLnonneg : 0 ≤
      (3 : ℝ) ^ (factors.length - 1) *
        (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) * ε *
        Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) := by
    positivity
  have hsmallLog :
      ‖∑ n ∈ factorExtractionRealInterval x y,
        dyadicFactorComplexProduct z factors (r * n) *
          factorExtractionMellinWeight χnat t n‖ ≤
        (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) * ε *
          Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) *
          Real.log (8 * X) := by
    calc
      _ ≤ (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) * ε *
          Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) *
          ∏ j ∈ Finset.univ.erase (e.symm i₀), B j := hsmallCore'
      _ ≤ (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) * ε *
          Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) *
          Real.log (8 * X) :=
            mul_le_mul_of_nonneg_left hBprod hLnonneg
  have hc : ‖(dyadicBinomialCoefficient ν.1 : ℂ)‖ ≤ (2 : ℝ) ^ 10 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      dyadicBinomialCoefficient_abs_le ν.1
  have hbound : ‖(dyadicBinomialCoefficient ν.1 : ℂ)‖ *
      ‖∑ n ∈ factorExtractionRealInterval x y,
        dyadicFactorComplexProduct z factors (r * n) *
          factorExtractionMellinWeight χnat t n‖ ≤
      (2 : ℝ) ^ 10 *
        ((3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) * ε *
          Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) *
          Real.log (8 * X)) := by
    calc
      _ ≤ (2 : ℝ) ^ 10 *
          ‖∑ n ∈ factorExtractionRealInterval x y,
            dyadicFactorComplexProduct z factors (r * n) *
              factorExtractionMellinWeight χnat t n‖ :=
            mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmallLog (by positivity)
  change ‖(dyadicBinomialCoefficient ν.1 : ℂ) * _‖ ≤ _
  calc
    _ ≤ (2 : ℝ) ^ 10 *
        ((3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) * ε *
          Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) *
          Real.log (8 * X)) := by
            rw [norm_mul]
            exact hbound
    _ = (2 : ℝ) ^ 10 *
        (3 : ℝ) ^ (factors.length - 1) *
        (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) * ε *
        Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) *
        Real.log (8 * X) := by ring
    _ = _ := by simp [factors]

/-- Intersecting a real half-open interval with the product cutoff
`r * n ≤ z` is exactly the half-open interval ending at
`min y (z / r)`. This keeps the real endpoint convention while converting
the product cutoff to the selected group variable. -/
theorem factorExtractionRealInterval_mulUpperCutoff_eq
    {x y z : ℝ} {r : ℕ} (hr : 0 < r) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hz : 0 ≤ z) :
    (factorExtractionRealInterval x y).filter
        (fun n => ((r * n : ℕ) : ℝ) ≤ z) =
      factorExtractionRealInterval x (min y (z / (r : ℝ))) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hy : 0 ≤ y := le_trans hx hxy
  have hy' : 0 ≤ min y (z / (r : ℝ)) :=
    le_min hy (div_nonneg hz hrR.le)
  ext n
  simp only [Finset.mem_filter]
  rw [mem_factorExtractionRealInterval hx hy,
    mem_factorExtractionRealInterval hx hy']
  constructor
  · rintro ⟨⟨hnx, hny⟩, hcut⟩
    have hcutR : (n : ℝ) * (r : ℝ) ≤ z := by
      simpa [Nat.cast_mul, mul_comm] using hcut
    have hnz : (n : ℝ) ≤ z / (r : ℝ) :=
      (le_div_iff₀ hrR).2 hcutR
    exact ⟨hnx, le_min hny hnz⟩
  · rintro ⟨hnx, hny⟩
    rcases le_min_iff.mp hny with ⟨hny, hnz⟩
    refine ⟨⟨hnx, hny⟩, ?_⟩
    have hcutR : (n : ℝ) * (r : ℝ) ≤ z :=
      (le_div_iff₀ hrR).1 hnz
    simpa [Nat.cast_mul, mul_comm] using hcutR

/-- The corresponding finite-sum identity for any coefficient sequence. -/
theorem factorExtractionRealInterval_mulUpperCutoff_sum_eq
    {x y z : ℝ} {r : ℕ} (hr : 0 < r) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hz : 0 ≤ z) (F : ℕ → ℂ) :
    (∑ n ∈ factorExtractionRealInterval x y,
      if ((r * n : ℕ) : ℝ) ≤ z then F n else 0) =
    ∑ n ∈ factorExtractionRealInterval x (min y (z / (r : ℝ))), F n := by
  rw [← Finset.sum_filter,
    factorExtractionRealInterval_mulUpperCutoff_eq hr hx hxy hz]

/-- Norm bounds on the shortened interval transfer unchanged to the sum
with the explicit product cutoff. -/
theorem factorExtractionRealInterval_mulUpperCutoff_norm_le
    {x y z A : ℝ} {r : ℕ} (hr : 0 < r) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hz : 0 ≤ z) (c : ℂ) (F : ℕ → ℂ)
    (hbound : ‖c * ∑ n ∈
        factorExtractionRealInterval x (min y (z / (r : ℝ))), F n‖ ≤ A) :
    ‖c * ∑ n ∈ factorExtractionRealInterval x y,
        if ((r * n : ℕ) : ℝ) ≤ z then F n else 0‖ ≤ A := by
  rw [factorExtractionRealInterval_mulUpperCutoff_sum_eq hr hx hxy hz]
  exact hbound

#print axioms selectedVonMangoldtGroup_truncatedFactorExtraction
#print axioms factorExtractionRealInterval_mulUpperCutoff_eq
#print axioms factorExtractionRealInterval_mulUpperCutoff_sum_eq
#print axioms factorExtractionRealInterval_mulUpperCutoff_norm_le

end FractionalPrimes.Literature.Twisted

end
