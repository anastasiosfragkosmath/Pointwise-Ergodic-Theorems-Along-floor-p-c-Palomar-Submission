module

public import FractionalPrimes.Literature.JSW.VectorDuality
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Translation continuity for uniform step functions

This file formalizes the exact translation estimate in `lj:step-translation`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

private def uniformStepCell (h : ℝ) (j : ℤ) : Set ℝ :=
  Set.Ico ((j : ℝ) * h) (((j + 1 : ℤ) : ℝ) * h)

private def uniformStepBoundary (h t : ℝ) (j : ℤ) : Set ℝ :=
  Set.Ico ((j : ℝ) * h) ((j : ℝ) * h + t)

private theorem uniformStep_cell_cover {h : ℝ} (hh : 0 < h) :
    (⋃ j : ℤ, uniformStepCell h j) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  let j : ℤ := Int.floor (x / h)
  refine ⟨j, ?_⟩
  have hlow : (j : ℝ) ≤ x / h := Int.floor_le _
  have hupp : x / h < (j : ℝ) + 1 := Int.lt_floor_add_one _
  rw [uniformStepCell, Set.mem_Ico]
  constructor
  · exact (le_div_iff₀ hh).mp (by simpa [j] using hlow)
  · exact (div_lt_iff₀ hh).mp (by simp [j])

private theorem uniformStep_cell_index_unique {h : ℝ} (hh : 0 < h) {x : ℝ}
    {j k : ℤ} (hj : x ∈ uniformStepCell h j) (hk : x ∈ uniformStepCell h k) : j = k := by
  have hj' : j = Int.floor (x / h) := by
    symm
    apply (Int.floor_eq_iff).2
    rw [uniformStepCell, Set.mem_Ico] at hj
    constructor
    · apply (le_div_iff₀ hh).2
      simpa using hj.1
    · apply (div_lt_iff₀ hh).2
      simpa using hj.2
  have hk' : k = Int.floor (x / h) := by
    symm
    apply (Int.floor_eq_iff).2
    rw [uniformStepCell, Set.mem_Ico] at hk
    constructor
    · apply (le_div_iff₀ hh).2
      simpa using hk.1
    · apply (div_lt_iff₀ hh).2
      simpa using hk.2
  exact hj'.trans hk'.symm

private theorem uniformStep_cell_pairwise_disjoint {h : ℝ} (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint (fun j : ℤ => uniformStepCell h j)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hj hk
  exact hjk (uniformStep_cell_index_unique hh hj hk)

private theorem uniformStep_boundary_subset_cell {h t : ℝ}
    (hth : t ≤ h) (j : ℤ) :
    uniformStepBoundary h t j ⊆ uniformStepCell h j := by
  intro x hx
  rw [uniformStepBoundary, Set.mem_Ico] at hx
  rw [uniformStepCell, Set.mem_Ico]
  constructor
  · exact hx.1
  · have : (j : ℝ) * h + t ≤ (j : ℝ) * h + h := by linarith
    have hx' : x < (j : ℝ) * h + t := hx.2
    have hcast : (((j + 1 : ℤ) : ℝ) * h) = (j : ℝ) * h + h := by
      push_cast
      ring
    rw [hcast]
    linarith

private theorem uniformStep_boundary_pairwise_disjoint {h t : ℝ}
    (hh : 0 < h) (hth : t ≤ h) :
    Pairwise (Function.onFun Disjoint (fun j : ℤ => uniformStepBoundary h t j)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hj hk
  have hcellj := uniformStep_boundary_subset_cell hth j hj
  have hcellk := uniformStep_boundary_subset_cell hth k hk
  exact hjk (uniformStep_cell_index_unique hh hcellj hcellk)

private theorem integral_Ico_const_real {a b v : ℝ} (hab : a ≤ b) :
    (∫ _x in Set.Ico a b, v ∂(volume : Measure ℝ)) = (b - a) * v := by
  rw [integral_const]
  simp [sub_nonneg.mpr hab]

private theorem integral_uniformStep_cell_const {h : ℝ} (hh : 0 < h)
    (j : ℤ) (v : ℝ) :
    (∫ _x in uniformStepCell h j, v ∂(volume : Measure ℝ)) = h * v := by
  have hend : ((j + 1 : ℤ) : ℝ) * h = (j : ℝ) * h + h := by
    push_cast
    ring
  have hle : (j : ℝ) * h ≤ ((j + 1 : ℤ) : ℝ) * h := by
    rw [hend]
    linarith
  rw [uniformStepCell, integral_Ico_const_real hle, hend]
  ring

private theorem integral_uniformStep_boundary_const {h t : ℝ}
    (ht : 0 ≤ t) (j : ℤ) (v : ℝ) :
    (∫ _x in uniformStepBoundary h t j, v ∂(volume : Measure ℝ)) = t * v := by
  have hle : (j : ℝ) * h ≤ (j : ℝ) * h + t := by linarith
  rw [uniformStepBoundary, integral_Ico_const_real hle]
  ring

private theorem dyadicStepTranslation_nonneg {h t : ℝ} (hh : 0 < h)
    (ht : 0 ≤ t) (hth : t ≤ h) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume)
    (hstep : ∀ j : ℤ, ∃ c : ℂ, ∀ x, x ∈ uniformStepCell h j → g x = c) :
    lpNorm (fun x => g (x - t) - g x) 2 volume ≤
      2 * Real.sqrt (t / h) * lpNorm g 2 volume := by
  classical
  let c : ℤ → ℂ := fun j => Classical.choose (hstep j)
  have hc (j : ℤ) : ∀ x, x ∈ uniformStepCell h j → g x = c j :=
    Classical.choose_spec (hstep j)
  have hG : Integrable (fun x => ‖g x‖ ^ 2) volume :=
    hg.integrable_norm_pow (by norm_num)
  have hshift : MemLp (fun x => g (x - t)) 2 volume :=
    hg.comp_measurePreserving (measurePreserving_sub_right volume t)
  have hd : MemLp (fun x => g (x - t) - g x) 2 volume := hshift.sub hg
  have hD : Integrable (fun x => ‖g (x - t) - g x‖ ^ 2) volume :=
    hd.integrable_norm_pow (by norm_num)
  have hcell (j : ℤ) :
      (∫ x in uniformStepCell h j, ‖g x‖ ^ 2 ∂(volume : Measure ℝ)) =
        h * ‖c j‖ ^ 2 := by
    calc
      _ = ∫ x in uniformStepCell h j, ‖c j‖ ^ 2 ∂(volume : Measure ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        change ‖g x‖ ^ 2 = ‖c j‖ ^ 2
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hc j x hx)
      _ = h * ‖c j‖ ^ 2 := integral_uniformStep_cell_const hh j _
  have hcellHasSum :
      HasSum (fun j : ℤ => h * ‖c j‖ ^ 2)
        (∫ x, ‖g x‖ ^ 2 ∂(volume : Measure ℝ)) := by
    have hInt : IntegrableOn (fun x => ‖g x‖ ^ 2)
        (⋃ j : ℤ, uniformStepCell h j) volume := by
      rw [uniformStep_cell_cover hh]
      exact hG.integrableOn
    have hsum := hasSum_integral_iUnion
      (fun j : ℤ => measurableSet_Ico)
      (uniformStep_cell_pairwise_disjoint hh) hInt
    have hcover := uniformStep_cell_cover hh
    have hcover' : (⋃ j : ℤ, Set.Ico ((j : ℝ) * h)
        (((j + 1 : ℤ) : ℝ) * h)) = Set.univ := by
      simpa [uniformStepCell] using hcover
    have hsum' : HasSum
        (fun j : ℤ => h * ‖c j‖ ^ 2)
        (∫ x, ‖g x‖ ^ 2 ∂volume) := by
      have hsumCoeff := hsum.congr_fun (fun j => (hcell j).symm)
      have hsetInt :
          (∫ x in ⋃ j : ℤ, Set.Ico ((j : ℝ) * h)
            (((j + 1 : ℤ) : ℝ) * h), ‖g x‖ ^ 2 ∂volume) =
            ∫ x, ‖g x‖ ^ 2 ∂volume := by
        rw [hcover']
        simp
      rw [hsetInt] at hsumCoeff
      exact hsumCoeff
    exact hsum'
  have hcoeff : Summable (fun j : ℤ => ‖c j‖ ^ 2) := by
    have hs := hcellHasSum.summable.mul_left h⁻¹
    exact hs.congr fun j => by
      field_simp [hh.ne']
  have hcoeffShift : Summable (fun j : ℤ => ‖c (j - 1)‖ ^ 2) := by
    exact hcoeff.comp_injective (by
      intro i j hij
      change i - 1 = j - 1 at hij
      omega)
  have hshiftTsum :
      (∑' j : ℤ, ‖c (j - 1)‖ ^ 2) = ∑' j : ℤ, ‖c j‖ ^ 2 := by
    simpa [sub_eq_add_neg] using
      (Equiv.tsum_eq (Equiv.addRight (-1 : ℤ)) (fun j : ℤ => ‖c j‖ ^ 2))
  have hcoeffHasSum : HasSum (fun j : ℤ => ‖c j‖ ^ 2)
      (h⁻¹ * ∫ x, ‖g x‖ ^ 2 ∂(volume : Measure ℝ)) := by
    have hs := hcellHasSum.mul_left h⁻¹
    exact hs.congr_fun (fun j => by field_simp [hh.ne'])
  let B : Set ℝ := ⋃ j : ℤ, uniformStepBoundary h t j
  have hBmeas : MeasurableSet B := by
    exact MeasurableSet.iUnion fun j => measurableSet_Ico
  have hzero : ∀ x, x ∉ B → g (x - t) = g x := by
    intro x hx
    have hxin : x ∈ ⋃ j : ℤ, uniformStepCell h j := by
      rw [uniformStep_cell_cover hh]
      trivial
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxin
    have hxcell : x ∈ uniformStepCell h j := hj
    have hxnot : x ∉ uniformStepBoundary h t j := by
      intro hxj
      exact hx (Set.mem_iUnion.mpr ⟨j, hxj⟩)
    rw [uniformStepCell, Set.mem_Ico] at hxcell
    change ¬ x ∈ Set.Ico ((j : ℝ) * h) ((j : ℝ) * h + t) at hxnot
    rw [Set.mem_Ico] at hxnot
    have hxleft : (j : ℝ) * h ≤ x := hxcell.1
    have hxright : x < ((j + 1 : ℤ) : ℝ) * h := hxcell.2
    have hxafter : (j : ℝ) * h + t ≤ x := by
      by_contra hnot
      have hxlt : x < (j : ℝ) * h + t := lt_of_not_ge hnot
      exact hxnot ⟨hxleft, hxlt⟩
    have hxminusleft : (j : ℝ) * h ≤ x - t := by linarith
    have hxminusright : x - t < ((j + 1 : ℤ) : ℝ) * h := by linarith
    have hc1 := hc j x ⟨hxleft, hxright⟩
    have hc2 := hc j (x - t) ⟨hxminusleft, hxminusright⟩
    rw [hc1, hc2]
  have hzeroInt :
      (∫ x in Bᶜ, ‖g (x - t) - g x‖ ^ 2 ∂(volume : Measure ℝ)) = 0 := by
    apply setIntegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with x hx
    simp [hzero x hx]
  have hsumB :
      HasSum (fun j : ℤ => t * ‖c (j - 1) - c j‖ ^ 2)
        (∫ x in B, ‖g (x - t) - g x‖ ^ 2 ∂(volume : Measure ℝ)) := by
    have hIntB : IntegrableOn (fun x => ‖g (x - t) - g x‖ ^ 2) B volume :=
      hD.integrableOn
    have hsum := hasSum_integral_iUnion
      (fun j : ℤ => measurableSet_Ico)
      (uniformStep_boundary_pairwise_disjoint hh hth) hIntB
    have hstrip (j : ℤ) :
        (∫ x in uniformStepBoundary h t j,
          ‖g (x - t) - g x‖ ^ 2 ∂(volume : Measure ℝ)) =
          t * ‖c (j - 1) - c j‖ ^ 2 := by
      calc
        _ = ∫ x in uniformStepBoundary h t j,
              ‖c (j - 1) - c j‖ ^ 2 ∂(volume : Measure ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ico
          intro x hx
          change ‖g (x - t) - g x‖ ^ 2 = ‖c (j - 1) - c j‖ ^ 2
          change x ∈ Set.Ico ((j : ℝ) * h) ((j : ℝ) * h + t) at hx
          rw [Set.mem_Ico] at hx
          have hxcell : x ∈ uniformStepCell h j :=
            uniformStep_boundary_subset_cell hth j ⟨hx.1, hx.2⟩
          have hxprev : x - t ∈ uniformStepCell h (j - 1) := by
            rw [uniformStepCell, Set.mem_Ico]
            constructor
            · have hcast : ((j - 1 : ℤ) : ℝ) * h = (j : ℝ) * h - h := by
                push_cast
                ring
              rw [hcast]
              linarith
            · have hcast : (((j - 1 : ℤ) + 1 : ℤ) : ℝ) * h = (j : ℝ) * h := by
                push_cast
                ring
              rw [hcast]
              linarith
          rw [hc (j - 1) (x - t) hxprev, hc j x hxcell]
        _ = t * ‖c (j - 1) - c j‖ ^ 2 :=
          integral_uniformStep_boundary_const ht j _
    have hsum' : HasSum
        (fun j : ℤ => t * ‖c (j - 1) - c j‖ ^ 2)
        (∫ x in B, ‖g (x - t) - g x‖ ^ 2 ∂volume) := by
      change HasSum
        (fun j : ℤ => t * ‖c (j - 1) - c j‖ ^ 2)
        (∫ x in ⋃ j : ℤ, uniformStepBoundary h t j,
          ‖g (x - t) - g x‖ ^ 2 ∂volume)
      exact hsum.congr_fun (fun j => (hstrip j).symm)
    exact hsum'
  have hglobalD :
      (∫ x, ‖g (x - t) - g x‖ ^ 2 ∂(volume : Measure ℝ)) =
        ∑' j : ℤ, t * ‖c (j - 1) - c j‖ ^ 2 := by
    calc
      _ = ∫ x in univ, ‖g (x - t) - g x‖ ^ 2 ∂(volume : Measure ℝ) := by simp
      _ = ∫ x in B ∪ Bᶜ, ‖g (x - t) - g x‖ ^ 2 ∂(volume : Measure ℝ) := by
        have hset : B ∪ Bᶜ = Set.univ := Set.union_compl_self B
        rw [hset]
      _ = (∫ x in B, ‖g (x - t) - g x‖ ^ 2 ∂volume) +
          ∫ x in Bᶜ, ‖g (x - t) - g x‖ ^ 2 ∂volume :=
        setIntegral_union (by
          rw [Set.disjoint_left]
          intro x hx hxc
          exact hxc hx) (MeasurableSet.compl hBmeas)
          hD.integrableOn hD.integrableOn
      _ = ∑' j : ℤ, t * ‖c (j - 1) - c j‖ ^ 2 := by rw [hzeroInt, hsumB.tsum_eq]; simp
  have hterm (j : ℤ) :
      t * ‖c (j - 1) - c j‖ ^ 2 ≤
        2 * t * (‖c (j - 1)‖ ^ 2 + ‖c j‖ ^ 2) := by
    have hnorm := norm_sub_le (c (j - 1)) (c j)
    have hsumSq :
        ‖c (j - 1) - c j‖ ^ 2 ≤
          2 * (‖c (j - 1)‖ ^ 2 + ‖c j‖ ^ 2) := by
      have hsum : 0 ≤ ‖c (j - 1)‖ + ‖c j‖ := by positivity
      have hdif : 0 ≤ ‖c (j - 1) - c j‖ := norm_nonneg _
      have hprod := mul_nonneg (sub_nonneg.mpr hnorm) (add_nonneg hsum hdif)
      have hupper : ‖c (j - 1) - c j‖ ^ 2 ≤
          (‖c (j - 1)‖ + ‖c j‖) ^ 2 := by nlinarith [hprod]
      have hsumUpper : (‖c (j - 1)‖ + ‖c j‖) ^ 2 ≤
          2 * ((‖c (j - 1)‖) ^ 2 + (‖c j‖) ^ 2) := by
        nlinarith [sq_nonneg (‖c (j - 1)‖ - ‖c j‖)]
      exact hupper.trans hsumUpper
    calc
      t * ‖c (j - 1) - c j‖ ^ 2 ≤
          t * (2 * (‖c (j - 1)‖ ^ 2 + ‖c j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsumSq ht
      _ = 2 * t * (‖c (j - 1)‖ ^ 2 + ‖c j‖ ^ 2) := by ring
  have hsumR : Summable (fun j : ℤ => 2 * t *
      (‖c (j - 1)‖ ^ 2 + ‖c j‖ ^ 2)) := by
    exact (hcoeffShift.add hcoeff).mul_left (2 * t)
  have hsumle := Summable.tsum_le_tsum hterm hsumB.summable hsumR
  have henergy :
      (∫ x, ‖g (x - t) - g x‖ ^ 2 ∂(volume : Measure ℝ)) ≤
        4 * (t / h) * ∫ x, ‖g x‖ ^ 2 ∂(volume : Measure ℝ) := by
    calc
      _ = ∑' j : ℤ, t * ‖c (j - 1) - c j‖ ^ 2 := hglobalD
      _ ≤ ∑' j : ℤ, 2 * t * (‖c (j - 1)‖ ^ 2 + ‖c j‖ ^ 2) := hsumle
      _ = 4 * t * ∑' j : ℤ, ‖c j‖ ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_add hcoeffShift hcoeff, hshiftTsum]
        ring
      _ = 4 * (t / h) * ∫ x, ‖g x‖ ^ 2 ∂(volume : Measure ℝ) := by
        rw [hcoeffHasSum.tsum_eq]
        field_simp [hh.ne']
  have hnormFormula {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
      lpNorm f 2 volume = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(volume : Measure ℝ)) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
    norm_num [Real.sqrt_eq_rpow]
  have hformulaG := hnormFormula hg
  have hformulaD := hnormFormula hd
  have hr : 0 ≤ t / h := div_nonneg ht hh.le
  have hRhs : 0 ≤ 2 * Real.sqrt (t / h) * lpNorm g 2 volume :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) lpNorm_nonneg
  have hnormGsq : (lpNorm g 2 volume) ^ 2 =
      ∫ x, ‖g x‖ ^ 2 ∂(volume : Measure ℝ) := by
    rw [hformulaG, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg ‖g x‖)]
  have hsqRhs :
      (2 * Real.sqrt (t / h) * lpNorm g 2 volume) ^ 2 =
        4 * (t / h) * ∫ x, ‖g x‖ ^ 2 ∂(volume : Measure ℝ) := by
    calc
      _ = 4 * (Real.sqrt (t / h)) ^ 2 * (lpNorm g 2 volume) ^ 2 := by ring
      _ = 4 * (t / h) * (lpNorm g 2 volume) ^ 2 := by rw [Real.sq_sqrt hr]
      _ = 4 * (t / h) * ∫ x, ‖g x‖ ^ 2 ∂(volume : Measure ℝ) := by rw [hnormGsq]
  rw [hformulaD]
  exact (Real.sqrt_le_iff).2 ⟨hRhs, by rw [hsqRhs]; exact henergy⟩

private theorem lpNorm_translate_sub {g : ℝ → ℂ} (hg : MemLp g 2 volume) (s : ℝ) :
    lpNorm (fun x => g (x - s)) 2 volume = lpNorm g 2 volume := by
  calc
    lpNorm (fun x => g (x - s)) 2 volume =
        (eLpNorm (fun x => g (x - s)) 2 volume).toReal := rfl
    _ = (eLpNorm g 2 volume).toReal := by
      congr 1
      exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
        (measurePreserving_sub_right volume s)
    _ = lpNorm g 2 volume := rfl

private theorem lpNorm_translate_add {g : ℝ → ℂ} (hg : MemLp g 2 volume) (s : ℝ) :
    lpNorm (fun x => g (x + s)) 2 volume = lpNorm g 2 volume := by
  calc
    lpNorm (fun x => g (x + s)) 2 volume =
        (eLpNorm (fun x => g (x + s)) 2 volume).toReal := rfl
    _ = (eLpNorm g 2 volume).toReal := by
      congr 1
      exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
        (measurePreserving_add_right volume s)
    _ = lpNorm g 2 volume := rfl

/-- The `L²` translation modulus for functions constant on the half-open
uniform cells `[j*h,(j+1)*h)`, with the exact constant in `lj:step-translation`. -/
theorem dyadicStepTranslation {h : ℝ} (hh : 0 < h) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume)
    (hstep : ∀ j : ℤ, ∃ c : ℂ, ∀ x,
      x ∈ Set.Ico ((j : ℝ) * h) (((j + 1 : ℤ) : ℝ) * h) → g x = c)
    (t : ℝ) :
    lpNorm (fun x => g (x - t) - g x) 2 volume ≤
      2 * Real.sqrt (min 1 (|t| / h)) * lpNorm g 2 volume := by
  by_cases hlarge : h ≤ |t|
  · have hshift : MemLp (fun x => g (x - t)) 2 volume :=
      hg.comp_measurePreserving (measurePreserving_sub_right volume t)
    have hmin : min 1 (|t| / h) = 1 := by
      apply min_eq_left
      apply (le_div_iff₀ hh).2
      simpa using hlarge
    calc
      lpNorm (fun x => g (x - t) - g x) 2 volume ≤
          lpNorm (fun x => g (x - t)) 2 volume + lpNorm g 2 volume :=
        lpNorm_sub_le hshift (by norm_num)
      _ = 2 * Real.sqrt (min 1 (|t| / h)) * lpNorm g 2 volume := by
        rw [lpNorm_translate_sub hg t, hmin]
        simp only [Real.sqrt_one]
        ring
  · have habs : |t| < h := lt_of_not_ge hlarge
    have hratio : |t| / h ≤ 1 := by
      apply (div_le_iff₀ hh).2
      simpa using habs.le
    have hmin : min 1 (|t| / h) = |t| / h := min_eq_right hratio
    by_cases ht : 0 ≤ t
    · have htle : t ≤ h := by simpa [abs_of_nonneg ht] using habs.le
      have hminT : min 1 (t / h) = t / h := by
        apply min_eq_right
        apply (div_le_iff₀ hh).2
        simpa [abs_of_nonneg ht] using habs.le
      have hcoef : t / h = min 1 (|t| / h) := by
        calc
          t / h = min 1 (t / h) := hminT.symm
          _ = min 1 (|t| / h) := by rw [abs_of_nonneg ht]
      calc
        lpNorm (fun x => g (x - t) - g x) 2 volume ≤
            2 * Real.sqrt (t / h) * lpNorm g 2 volume :=
          dyadicStepTranslation_nonneg hh ht htle hg
            (by simpa [uniformStepCell] using hstep)
        _ = 2 * Real.sqrt (min 1 (|t| / h)) * lpNorm g 2 volume := by
          rw [hcoef]
    · have htneg : t < 0 := lt_of_not_ge ht
      let s : ℝ := -t
      have hs : s = |t| := by simp [s, abs_of_neg htneg]
      have hspos : 0 ≤ s := by rw [hs]; positivity
      have hsle : s ≤ h := by rw [hs]; exact habs.le
      have hstep' : ∀ j : ℤ, ∃ c : ℂ, ∀ x,
          x ∈ uniformStepCell h j → g x = c := by
        simpa [uniformStepCell] using hstep
      have hsmall := dyadicStepTranslation_nonneg hh hspos hsle hg hstep'
      let d : ℝ → ℂ := fun x => g (x - s) - g x
      have hd : MemLp d 2 volume := by
        change MemLp (fun x => g (x - s) - g x) 2 volume
        exact (hg.comp_measurePreserving (measurePreserving_sub_right volume s)).sub hg
      have hfun : (fun x => g (x + s) - g x) = fun x => -d (x + s) := by
        funext x
        simp [d]
      have hnorm : lpNorm (fun x => g (x + s) - g x) 2 volume = lpNorm d 2 volume := by
        rw [hfun]
        calc
          lpNorm (fun x => -d (x + s)) 2 volume =
              lpNorm (-(fun x => d (x + s))) 2 volume := by rfl
          _ = lpNorm (fun x => d (x + s)) 2 volume := lpNorm_neg _ _ _
          _ = lpNorm d 2 volume := lpNorm_translate_add hd s
      have htarget : (fun x => g (x - t) - g x) = fun x => g (x + s) - g x := by
        funext x
        simp [s, sub_eq_add_neg]
      rw [htarget, hnorm]
      calc
        lpNorm d 2 volume ≤ 2 * Real.sqrt (s / h) * lpNorm g 2 volume := hsmall
        _ = 2 * Real.sqrt (min 1 (|t| / h)) * lpNorm g 2 volume := by
          rw [hs, hmin]

#print axioms FractionalPrimes.Literature.JSW.dyadicStepTranslation

end

end FractionalPrimes.Literature.JSW

end
