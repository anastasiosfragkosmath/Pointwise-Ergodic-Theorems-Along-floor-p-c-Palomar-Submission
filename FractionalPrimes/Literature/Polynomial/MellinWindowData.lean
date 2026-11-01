module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open MeasureTheory

open scoped BigOperators

/-! Exact finite Dirichlet and Mellin-window data from `lup:window-data`.
The fixed real kernel density is an explicit input so the definitions can be
instantiated by the single kernel chosen in `lup:kernel-data`. -/

/-- The finite natural-index set for a half-open real interval `(x,y]`. -/
noncomputable def mellinIntervalIndices (x y : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.ceil y)).filter fun n => x < (n : ℝ) ∧ (n : ℝ) ≤ y

/-- The coefficient-support indices `(X/2,3X]`. -/
noncomputable def mellinWindowSupportIndices (X : ℝ) : Finset ℕ :=
  mellinIntervalIndices (X / 2) (3 * X)

/-- The averaging indices `(X,X+H]`. -/
noncomputable def mellinWindowAverageIndices (X H : ℝ) : Finset ℕ :=
  mellinIntervalIndices X (X + H)

/-- The real-log convention for the complex monomial `n^(-1/2-it)`. -/
noncomputable def mellinDirichletMonomial (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp
    ((((-1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) *
      ((Real.log (n : ℝ) : ℝ) : ℂ))

/-- The real-log convention for `x^(1/2+it)` on positive real bases. -/
noncomputable def mellinHalfItPower (x t : ℝ) : ℂ :=
  Complex.exp
    ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
      ((Real.log x : ℝ) : ℂ))

/-- The real factor `n^(-1/2)`, written using the real natural logarithm. -/
noncomputable def mellinRealHalfPower (n : ℕ) : ℝ :=
  Real.exp (-Real.log (n : ℝ) / 2)

/-- Real convolution in the convention `(f*g)(x)=∫f(u)g(x-u)du`. -/
noncomputable def mellinRealConvolution
    (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u, f u * g (x - u) ∂volume

/-- The real Mellin denominator is never zero for real `t`. -/
theorem mellinWindowDenominator_ne_zero (t : ℝ) :
    ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

/-- The assumptions and all displayed objects in the finite Dirichlet and
Mellin-window definition. -/
structure MellinWindowData where
  rho : ℝ → ℝ
  X : ℝ
  H : ℝ
  B : ℝ
  a : ℕ → ℂ
  X_lower : 3 ≤ X
  H_pos : 0 < H
  H_upper : H ≤ X
  B_nonneg : 0 ≤ B
  coefficient_support : ∀ n, 0 < n → a n ≠ 0 →
    X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X
  coefficient_bound : ∀ n, 0 < n → ‖a n‖ ≤ B
  A_X : ℝ → ℂ
  N_H : ℂ
  h_H : ℝ → ℝ
  K_H : ℝ → ℂ
  rho_T : ℝ → ℝ → ℝ
  S_H_T : ℝ → ℂ

/-- Package the finite Dirichlet polynomial, normalized interval mean, sharp
logarithmic window, Mellin kernel, scaled smoothing density, and smoothed
finite sum with the source's exact supports and normalizations. -/
noncomputable def mellinWindowData
    (rho : ℝ → ℝ) (X H B : ℝ) (a : ℕ → ℂ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hB : 0 ≤ B)
    (hsupport : ∀ n, 0 < n → a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X)
    (hbound : ∀ n, 0 < n → ‖a n‖ ≤ B) : MellinWindowData := by
  let hfun : ℝ → ℝ := fun u =>
    Real.exp (u / 2) / H *
      if Real.log X < u ∧ u ≤ Real.log (X + H) then 1 else 0
  let rhofun : ℝ → ℝ → ℝ := fun T u => T * rho (T * u)
  let Afun : ℝ → ℂ := fun t =>
    ∑ n ∈ mellinWindowSupportIndices X,
      a n * mellinDirichletMonomial n t
  let Nfun : ℂ :=
    (↑(H⁻¹) : ℂ) *
      ∑ n ∈ mellinWindowAverageIndices X H, a n
  let Kfun : ℝ → ℂ := fun t =>
    (mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
      ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
  let Sfun : ℝ → ℂ := fun T =>
    ∑ n ∈ mellinWindowSupportIndices X,
      a n * (↑(mellinRealHalfPower n) : ℂ) *
        ↑(mellinRealConvolution hfun (rhofun T) (Real.log (n : ℝ)))
  exact
    { rho := rho
      X := X
      H := H
      B := B
      a := a
      X_lower := hX
      H_pos := hH
      H_upper := hHX
      B_nonneg := hB
      coefficient_support := hsupport
      coefficient_bound := hbound
      A_X := Afun
      N_H := Nfun
      h_H := hfun
      K_H := Kfun
      rho_T := rhofun
      S_H_T := Sfun }

/-- Membership in a finite Mellin interval is exactly its real half-open
condition when the left endpoint is nonnegative. -/
theorem mellinIntervalIndices_mem_iff {x y : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    n ∈ mellinIntervalIndices x y ↔ x < (n : ℝ) ∧ (n : ℝ) ≤ y := by
  unfold mellinIntervalIndices
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · rintro ⟨hxn, hny⟩
    have hnposR : 0 < (n : ℝ) := lt_of_le_of_lt hx hxn
    have hnpos : 0 < n := by exact_mod_cast hnposR
    have hceilR : (n : ℝ) ≤ (Nat.ceil y : ℝ) := hny.trans (Nat.le_ceil y)
    have hceil : n ≤ Nat.ceil y := by exact_mod_cast hceilR
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hceil⟩, ⟨hxn, hny⟩⟩

/-- Integer points in a half-open real interval have the usual length-plus-one
bound, including when either endpoint is integral. -/
theorem mellinIntervalIndices_card_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ((mellinIntervalIndices x y).card : ℝ) ≤ y - x + 1 := by
  let I : Finset ℕ := Finset.Icc (Nat.floor x + 1) (Nat.floor y)
  have hsub : mellinIntervalIndices x y ⊆ I := by
    intro n hn
    have hnxy := (mellinIntervalIndices_mem_iff hx n).1 hn
    have hxfl : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx
    have hflnR : (Nat.floor x : ℝ) < (n : ℝ) := lt_of_le_of_lt hxfl hnxy.1
    have hfln : Nat.floor x < n := by exact_mod_cast hflnR
    have hyfl : n ≤ Nat.floor y := Nat.le_floor hnxy.2
    exact Finset.mem_Icc.mpr ⟨by omega, hyfl⟩
  have hcardI : I.card = Nat.floor y - Nat.floor x := by
    dsimp [I]
    simp [Nat.card_Icc]
  have hfloorMono : Nat.floor x ≤ Nat.floor y := Nat.floor_mono hxy
  have hcardCast : (I.card : ℝ) =
      (Nat.floor y : ℝ) - (Nat.floor x : ℝ) := by
    rw [hcardI, Nat.cast_sub hfloorMono]
  have hcardle : (mellinIntervalIndices x y).card ≤ I.card := Finset.card_le_card hsub
  calc
    ((mellinIntervalIndices x y).card : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hcardle
    _ = (Nat.floor y : ℝ) - (Nat.floor x : ℝ) := hcardCast
    _ ≤ y - x + 1 := by
      have hyfl : (Nat.floor y : ℝ) ≤ y := Nat.floor_le (le_trans hx hxy)
      have hxlt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
      linarith

/-- The integer band between two endpoint positions, with the same
open-left, closed-right convention. -/
noncomputable def mellinEndpointBandIndices (x y : ℝ) : Finset ℕ :=
  mellinIntervalIndices (min x y) (max x y)

/-- The symmetric difference of two finite half-open integer intervals. -/
noncomputable def mellinIntervalDifferenceIndices
    (x y x' y' : ℝ) : Finset ℕ :=
  (mellinIntervalIndices x y \ mellinIntervalIndices x' y') ∪
    (mellinIntervalIndices x' y' \ mellinIntervalIndices x y)

/-- A change of interval membership can only occur in one of the two bands
between corresponding endpoints. -/
theorem mellinIntervalDifference_subset_endpointBands
    {x y x' y' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (hy : 0 ≤ y) (hy' : 0 ≤ y') :
    mellinIntervalDifferenceIndices x y x' y' ⊆
      mellinEndpointBandIndices x x' ∪ mellinEndpointBandIndices y y' := by
  intro n hn
  change n ∈
    (mellinIntervalIndices x y \ mellinIntervalIndices x' y') ∪
      (mellinIntervalIndices x' y' \ mellinIntervalIndices x y) at hn
  have hnmem := Finset.mem_union.mp hn
  rcases hnmem with hleft | hright
  · have hleft' := Finset.mem_sdiff.mp hleft
    have hxy := (mellinIntervalIndices_mem_iff hx n).1 hleft'.1
    have hnnot : ¬(n ∈ mellinIntervalIndices x' y') := hleft'.2
    by_cases hlow : x' < (n : ℝ)
    · have hnupper : ¬((n : ℝ) ≤ y') := by
        intro hu
        exact hnnot ((mellinIntervalIndices_mem_iff hx' n).2 ⟨hlow, hu⟩)
      have hy'lt : y' < (n : ℝ) := lt_of_not_ge hnupper
      apply Finset.mem_union.mpr
      right
      exact (mellinIntervalIndices_mem_iff (le_min hy hy') n).2
        ⟨lt_of_le_of_lt (min_le_right y y') hy'lt,
          le_trans hxy.2 (le_max_left y y')⟩
    · have hnupper : (n : ℝ) ≤ x' := le_of_not_gt hlow
      apply Finset.mem_union.mpr
      left
      exact (mellinIntervalIndices_mem_iff (le_min hx hx') n).2
        ⟨lt_of_le_of_lt (min_le_left x x') hxy.1,
          le_trans hnupper (le_max_right x x')⟩
  · have hright' := Finset.mem_sdiff.mp hright
    have hxy := (mellinIntervalIndices_mem_iff hx' n).1 hright'.1
    have hnnot : ¬(n ∈ mellinIntervalIndices x y) := hright'.2
    by_cases hlow : x < (n : ℝ)
    · have hnupper : ¬((n : ℝ) ≤ y) := by
        intro hu
        exact hnnot ((mellinIntervalIndices_mem_iff hx n).2 ⟨hlow, hu⟩)
      have hylt : y < (n : ℝ) := lt_of_not_ge hnupper
      apply Finset.mem_union.mpr
      right
      exact (mellinIntervalIndices_mem_iff (le_min hy hy') n).2
        ⟨lt_of_le_of_lt (min_le_left y y') hylt,
          le_trans hxy.2 (le_max_right y y')⟩
    · have hnupper : (n : ℝ) ≤ x := le_of_not_gt hlow
      apply Finset.mem_union.mpr
      left
      exact (mellinIntervalIndices_mem_iff (le_min hx hx') n).2
        ⟨lt_of_le_of_lt (min_le_right x x') hxy.1,
          le_trans hnupper (le_max_left x x')⟩

/-- The symmetric difference count is bounded by the two endpoint
displacements, with the endpoint corrections retained. -/
theorem mellinIntervalDifference_card_le
    {x y x' y' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (hy : 0 ≤ y) (hy' : 0 ≤ y') :
    ((mellinIntervalDifferenceIndices x y x' y').card : ℝ) ≤
      |x - x'| + |y - y'| + 2 := by
  have hsub := mellinIntervalDifference_subset_endpointBands hx hx' hy hy'
  have hcardle := Finset.card_le_card hsub
  have hbandx := mellinIntervalIndices_card_le (le_min hx hx') min_le_max
  have hbandy := mellinIntervalIndices_card_le (le_min hy hy') min_le_max
  have hunion := Finset.card_union_le
      (mellinEndpointBandIndices x x') (mellinEndpointBandIndices y y')
  have hbandxabs : max x x' - min x x' = |x - x'| := by
    rcases le_total x x' with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      linarith
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  have hbandyabs : max y y' - min y y' = |y - y'| := by
    rcases le_total y y' with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      linarith
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  calc
    ((mellinIntervalDifferenceIndices x y x' y').card : ℝ) ≤
        ((mellinEndpointBandIndices x x' ∪
          mellinEndpointBandIndices y y').card : ℝ) := by exact_mod_cast hcardle
    _ ≤ (mellinEndpointBandIndices x x').card +
          (mellinEndpointBandIndices y y').card := by exact_mod_cast hunion
    _ ≤ (max x x' - min x x' + 1) + (max y y' - min y y' + 1) := by
      dsimp [mellinEndpointBandIndices] at hbandx hbandy ⊢
      exact add_le_add hbandx hbandy
    _ = |x - x'| + |y - y'| + 2 := by rw [hbandxabs, hbandyabs]; ring

/-- The indicator of the source's half-open real interval, sampled at natural
indices. -/
noncomputable def mellinIntervalIndicator (x y : ℝ) (n : ℕ) : ℝ :=
  if x < (n : ℝ) ∧ (n : ℝ) ≤ y then 1 else 0

/-- Boolean test for whether two sharp interval indicators differ. -/
noncomputable def mellinIntervalsDiffer (x y x' y' : ℝ) (n : ℕ) : Bool := by
  classical
  exact decide
    (((x < (n : ℝ) ∧ (n : ℝ) ≤ y) ∧ ¬(x' < (n : ℝ) ∧ (n : ℝ) ≤ y')) ∨
      ((x' < (n : ℝ) ∧ (n : ℝ) ≤ y') ∧ ¬(x < (n : ℝ) ∧ (n : ℝ) ≤ y)))

/-- The finite sharp-window difference summand. -/
noncomputable def mellinShiftWindowTerm
    (w : MellinWindowData) (v : ℝ) (n : ℕ) : ℂ :=
  (w.a n) *
    ↑(Real.exp (-v / 2) *
      mellinIntervalIndicator (w.X * Real.exp v)
        ((w.X + w.H) * Real.exp v) n -
      mellinIntervalIndicator w.X (w.X + w.H) n)

/-- Summing a real interval indicator over a finite set gives the number of
retained indices. -/
theorem mellinIntervalIndicator_sum_eq_card
    (S : Finset ℕ) (x y : ℝ) :
    (∑ n ∈ S, mellinIntervalIndicator x y n) =
      (S.filter fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y).card := by
  classical
  change (∑ n ∈ S,
    if x < (n : ℝ) ∧ (n : ℝ) ≤ y then (1 : ℝ) else 0) = _
  exact Finset.sum_boole _ _

/-- The absolute difference of two zero-one interval indicators is the
indicator of their symmetric difference. -/
theorem mellinIntervalIndicator_abs_sub_eq
    (x y x' y' : ℝ) (n : ℕ) :
    |mellinIntervalIndicator x y n - mellinIntervalIndicator x' y' n| =
      if mellinIntervalsDiffer x y x' y' n = true then 1 else 0 := by
  classical
  by_cases h₁ : x < (n : ℝ) ∧ (n : ℝ) ≤ y <;>
    by_cases h₂ : x' < (n : ℝ) ∧ (n : ℝ) ≤ y' <;>
    simp [mellinIntervalIndicator, mellinIntervalsDiffer, h₁, h₂]

/-- The sum of absolute indicator differences equals the symmetric-difference
count. -/
theorem mellinIntervalIndicator_abs_sub_sum_eq_card
    (S : Finset ℕ) (x y x' y' : ℝ) :
    (∑ n ∈ S,
      |mellinIntervalIndicator x y n - mellinIntervalIndicator x' y' n|) =
      (S.filter fun n : ℕ => mellinIntervalsDiffer x y x' y' n = true).card := by
  classical
  simp_rw [mellinIntervalIndicator_abs_sub_eq]
  exact Finset.sum_boole _ _

/-- The Boolean indicator test agrees with membership in the finite symmetric
difference when all interval endpoints are nonnegative. -/
theorem mellinIntervalsDiffer_eq_true_iff_mem_difference
    {x y x' y' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (n : ℕ) :
    mellinIntervalsDiffer x y x' y' n = true ↔
      n ∈ mellinIntervalDifferenceIndices x y x' y' := by
  classical
  unfold mellinIntervalsDiffer
  rw [decide_eq_true_eq]
  unfold mellinIntervalDifferenceIndices
  rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
  rw [(mellinIntervalIndices_mem_iff hx n),
    (mellinIntervalIndices_mem_iff hx' n)]

/-- Restricting the absolute indicator difference to a finite coefficient set
cannot increase the full symmetric-difference count. -/
theorem mellinIntervalIndicator_abs_sub_sum_le_difference_card
    (S : Finset ℕ) {x y x' y' : ℝ}
    (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    (∑ n ∈ S,
      |mellinIntervalIndicator x y n - mellinIntervalIndicator x' y' n|) ≤
      (mellinIntervalDifferenceIndices x y x' y').card := by
  rw [mellinIntervalIndicator_abs_sub_sum_eq_card]
  have hsub :
      (S.filter fun n : ℕ => mellinIntervalsDiffer x y x' y' n = true) ⊆
        mellinIntervalDifferenceIndices x y x' y' := by
    intro n hn
    exact (mellinIntervalsDiffer_eq_true_iff_mem_difference hx hx' n).1
      (Finset.mem_filter.mp hn).2
  exact_mod_cast Finset.card_le_card hsub

/-- The total mass of a sampled interval indicator is at most its full integer
point count. -/
theorem mellinIntervalIndicator_sum_le_interval_card
    (S : Finset ℕ) {x y : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ S, mellinIntervalIndicator x y n) ≤
      (mellinIntervalIndices x y).card := by
  rw [mellinIntervalIndicator_sum_eq_card]
  have hsub :
      (S.filter fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y) ⊆
        mellinIntervalIndices x y := by
    intro n hn
    exact (mellinIntervalIndices_mem_iff hx n).2 (Finset.mem_filter.mp hn).2
  exact_mod_cast Finset.card_le_card hsub

/-- The source support contains at most `3X` positive integer indices. -/
theorem mellinWindowSupportIndices_card_le (w : MellinWindowData) :
    ((mellinWindowSupportIndices w.X).card : ℝ) ≤ 3 * w.X := by
  have hX : 0 ≤ w.X := by linarith [w.X_lower]
  have hcard := mellinIntervalIndices_card_le (x := w.X / 2) (y := 3 * w.X)
    (by positivity) (by linarith [w.X_lower])
  dsimp [mellinWindowSupportIndices] at hcard ⊢
  have hXlower : 3 ≤ w.X := w.X_lower
  linarith

/-- The source averaging window contains at most `4X/3` integer indices. -/
theorem mellinWindowAverageIndices_card_le (w : MellinWindowData) :
    ((mellinWindowAverageIndices w.X w.H).card : ℝ) ≤ 4 * w.X / 3 := by
  have hcard := mellinIntervalIndices_card_le (x := w.X) (y := w.X + w.H)
    (by linarith [w.X_lower]) (by linarith [w.H_pos])
  dsimp [mellinWindowAverageIndices] at hcard ⊢
  have hX : 3 ≤ w.X := w.X_lower
  have hHX : w.H ≤ w.X := w.H_upper
  linarith

/-- On a unit shift, the two interval endpoints move by at most the real
exponential displacement bound. -/
theorem mellinShiftEndpointDisplacement_le {X H v : ℝ}
    (hX : 0 ≤ X) (hH : 0 ≤ H) (hHX : H ≤ X) (hv : |v| ≤ 1) :
    |X * Real.exp v - X| +
      |(X + H) * Real.exp v - (X + H)| ≤ 6 * X * |v| := by
  have hexp : |Real.exp v - 1| ≤ 2 * |v| := Real.abs_exp_sub_one_le hv
  have hdispX : |X * Real.exp v - X| ≤ X * (2 * |v|) := by
    rw [show X * Real.exp v - X = X * (Real.exp v - 1) by ring,
      abs_mul, abs_of_nonneg hX]
    exact mul_le_mul_of_nonneg_left hexp hX
  have hY : 0 ≤ X + H := by linarith
  have hYle : X + H ≤ 2 * X := by linarith
  have hdispY :
      |(X + H) * Real.exp v - (X + H)| ≤ (X + H) * (2 * |v|) := by
    rw [show (X + H) * Real.exp v - (X + H) =
      (X + H) * (Real.exp v - 1) by ring, abs_mul, abs_of_nonneg hY]
    exact mul_le_mul_of_nonneg_left hexp hY
  calc
    |X * Real.exp v - X| +
        |(X + H) * Real.exp v - (X + H)| ≤
      X * (2 * |v|) + (X + H) * (2 * |v|) := add_le_add hdispX hdispY
    _ ≤ 6 * X * |v| := by nlinarith [abs_nonneg v]

/-- The exponential prefactor is bounded by three for shifts of size at most
one. -/
theorem mellinShiftPrefactor_le_three {v : ℝ} (hv : |v| ≤ 1) :
    Real.exp (-v / 2) ≤ 3 := by
  have hv' : -v / 2 ≤ 1 := by
    have := abs_le.mp hv
    linarith
  calc
    Real.exp (-v / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr hv'
    _ ≤ 3 := Real.exp_one_lt_three.le

/-- The scalar prefactor differs from one by at most the shift size. -/
theorem mellinShiftPrefactor_sub_one_abs_le {v : ℝ} (hv : |v| ≤ 1) :
    |Real.exp (-v / 2) - 1| ≤ |v| := by
  have hv' : |-v / 2| ≤ 1 := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg v]
  have h := Real.abs_exp_sub_one_le hv'
  have hhalf : |-v / 2| = |v| / 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hhalf] at h
  nlinarith

/-- Uniform error for translating and renormalizing the sharp Mellin window.
The sum is restricted to the exact coefficient support `(X/2,3X]`. -/
theorem shiftedWindowError (w : MellinWindowData) (v : ℝ) :
    ‖∑ n ∈ mellinWindowSupportIndices w.X,
      mellinShiftWindowTerm w v n‖ ≤
      w.B * (32 * w.X * |v| + 8) := by
  classical
  let S := mellinWindowSupportIndices w.X
  let c := Real.exp (-v / 2)
  let A : ℕ → ℝ := fun n => mellinIntervalIndicator
    (w.X * Real.exp v) ((w.X + w.H) * Real.exp v) n
  let D : ℕ → ℝ := fun n => mellinIntervalIndicator w.X (w.X + w.H) n
  have hX0 : 0 ≤ w.X := by linarith [w.X_lower]
  have hH0 : 0 ≤ w.H := le_of_lt w.H_pos
  have hc0 : 0 ≤ c := by dsimp [c]; exact (Real.exp_pos _).le
  have hA01 (n : ℕ) : A n = 0 ∨ A n = 1 := by
    by_cases hn : w.X * Real.exp v < (n : ℝ) ∧
        (n : ℝ) ≤ (w.X + w.H) * Real.exp v
    · right
      simp [A, mellinIntervalIndicator, hn]
    · left
      simp [A, mellinIntervalIndicator, hn]
  have hD01 (n : ℕ) : D n = 0 ∨ D n = 1 := by
    by_cases hn : w.X < (n : ℝ) ∧ (n : ℝ) ≤ w.X + w.H
    · right
      simp [D, mellinIntervalIndicator, hn]
    · left
      simp [D, mellinIntervalIndicator, hn]
  have hDnonneg (n : ℕ) : 0 ≤ D n := by
    rcases hD01 n with h | h <;> simp [h]
  have hcoeff (n : ℕ) (hn : n ∈ S) : ‖w.a n‖ ≤ w.B := by
    have hmem := (mellinIntervalIndices_mem_iff (by linarith [w.X_lower]) n).1 hn
    have hhalf : 0 < w.X / 2 := by linarith [w.X_lower]
    have hnreal : 0 < (n : ℝ) :=
      lt_trans hhalf hmem.1
    have hnpos : 0 < n := by exact_mod_cast hnreal
    exact w.coefficient_bound n hnpos
  have hscalar (n : ℕ) :
      |c * A n - D n| ≤ c * |A n - D n| + |c - 1| * D n := by
    have hiden : c * A n - D n = c * (A n - D n) + (c - 1) * D n := by ring
    rw [hiden]
    calc
      |c * (A n - D n) + (c - 1) * D n| ≤
          |c * (A n - D n)| + |(c - 1) * D n| := abs_add_le _ _
      _ = c * |A n - D n| + |c - 1| * D n := by
        rw [abs_mul, abs_of_nonneg hc0, abs_mul, abs_of_nonneg (hDnonneg n)]
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖mellinShiftWindowTerm w v n‖ ≤
        w.B * (c * |A n - D n| + |c - 1| * D n) := by
    rw [mellinShiftWindowTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖w.a n‖ * |c * A n - D n| ≤ w.B * |c * A n - D n| :=
        mul_le_mul_of_nonneg_right (hcoeff n hn) (abs_nonneg _)
      _ ≤ w.B * (c * |A n - D n| + |c - 1| * D n) :=
        mul_le_mul_of_nonneg_left (hscalar n) w.B_nonneg
  have hDcount : (∑ n ∈ S, D n) ≤ 4 * w.X / 3 := by
    calc
      (∑ n ∈ S, D n) ≤ (mellinIntervalIndices w.X (w.X + w.H)).card := by
        dsimp [D]
        exact mellinIntervalIndicator_sum_le_interval_card S (by linarith [w.X_lower])
      _ = (mellinWindowAverageIndices w.X w.H).card := rfl
      _ ≤ 4 * w.X / 3 := mellinWindowAverageIndices_card_le w
  by_cases hv : |v| ≤ 1
  · have hshiftEndpoints0 : 0 ≤ w.X * Real.exp v := by positivity
    have hshiftEndpoints1 : 0 ≤ (w.X + w.H) * Real.exp v := by positivity
    have hdiffCount : (∑ n ∈ S, |A n - D n|) ≤
        6 * w.X * |v| + 2 := by
      calc
        (∑ n ∈ S, |A n - D n|) ≤
            (mellinIntervalDifferenceIndices w.X (w.X + w.H)
              (w.X * Real.exp v) ((w.X + w.H) * Real.exp v)).card := by
          dsimp [A, D]
          simpa only [abs_sub_comm] using
              (mellinIntervalIndicator_abs_sub_sum_le_difference_card S
                hX0 hshiftEndpoints0)
        _ ≤ |w.X - w.X * Real.exp v| +
            |w.X + w.H - (w.X + w.H) * Real.exp v| + 2 :=
          mellinIntervalDifference_card_le
            (by linarith [w.X_lower]) hshiftEndpoints0
            (by linarith [w.X_lower, w.H_pos]) hshiftEndpoints1
        _ ≤ 6 * w.X * |v| + 2 := by
          have hdisp := mellinShiftEndpointDisplacement_le hX0 hH0 w.H_upper hv
          have hdisp' := add_le_add_right hdisp 2
          simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using hdisp'
    have hc3 : c ≤ 3 := by
      dsimp [c]
      exact mellinShiftPrefactor_le_three hv
    have hcm1 : |c - 1| ≤ |v| := by
      dsimp [c]
      exact mellinShiftPrefactor_sub_one_abs_le hv
    have hdiff0 : 0 ≤ ∑ n ∈ S, |A n - D n| := by positivity
    have hD0 : 0 ≤ ∑ n ∈ S, D n := Finset.sum_nonneg fun n hn => hDnonneg n
    have hfactor :
        (∑ n ∈ S, w.B * (c * |A n - D n| + |c - 1| * D n)) =
          w.B * (c * (∑ n ∈ S, |A n - D n|) +
            |c - 1| * (∑ n ∈ S, D n)) := by
      calc
        _ = S.sum (fun n =>
            (w.B * c) * |A n - D n| + (w.B * |c - 1|) * D n) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = (w.B * c) * (∑ n ∈ S, |A n - D n|) +
            (w.B * |c - 1|) * (∑ n ∈ S, D n) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = _ := by ring
    have hinside :
        c * (∑ n ∈ S, |A n - D n|) +
          |c - 1| * (∑ n ∈ S, D n) ≤
        3 * (6 * w.X * |v| + 2) + |v| * (4 * w.X / 3) := by
      exact add_le_add
        (le_trans (mul_le_mul_of_nonneg_right hc3 hdiff0)
          (mul_le_mul_of_nonneg_left hdiffCount (by norm_num)))
        (le_trans (mul_le_mul_of_nonneg_right hcm1 hD0)
          (mul_le_mul_of_nonneg_left hDcount (abs_nonneg v)))
    have hnumeric :
        3 * (6 * w.X * |v| + 2) + |v| * (4 * w.X / 3) ≤
          32 * w.X * |v| + 8 := by
      have hX : 0 ≤ w.X := hX0
      have hv0 : 0 ≤ |v| := abs_nonneg v
      nlinarith
    calc
      ‖∑ n ∈ S, mellinShiftWindowTerm w v n‖ ≤
          ∑ n ∈ S, ‖mellinShiftWindowTerm w v n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S,
          w.B * (c * |A n - D n| + |c - 1| * D n) :=
        Finset.sum_le_sum fun n hn => hterm n hn
      _ = w.B * (c * (∑ n ∈ S, |A n - D n|) +
            |c - 1| * (∑ n ∈ S, D n)) := hfactor
      _ ≤ w.B * (3 * (6 * w.X * |v| + 2) + |v| * (4 * w.X / 3)) :=
        mul_le_mul_of_nonneg_left hinside w.B_nonneg
      _ ≤ w.B * (32 * w.X * |v| + 8) :=
        mul_le_mul_of_nonneg_left hnumeric w.B_nonneg
  · have hvlarge : 1 < |v| := lt_of_not_ge hv
    have hshiftCount : (∑ n ∈ S, c * A n) ≤ 2 * (S.card : ℝ) := by
      calc
        (∑ n ∈ S, c * A n) ≤ ∑ n ∈ S, (2 : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          rcases hA01 n with hzero | hone
          · rw [hzero]
            simp
          · rw [hone]
            have hcond : w.X * Real.exp v < (n : ℝ) ∧
                (n : ℝ) ≤ (w.X + w.H) * Real.exp v := by
              by_contra hnot
              have hz : A n = 0 := by simp [A, mellinIntervalIndicator, hnot]
              simp [hz] at hone
            have hmem := (mellinIntervalIndices_mem_iff (by linarith [w.X_lower]) n).1 hn
            have hnpos : 0 < (n : ℝ) :=
              lt_trans (by linarith [w.X_lower]) hmem.1
            have hcSq : c ^ 2 = Real.exp (-v) := by
              dsimp [c]
              rw [pow_two]
              rw [← Real.exp_add]
              congr 1; ring
            have hexpcancel : Real.exp v * Real.exp (-v) = 1 := by
              rw [← Real.exp_add]
              simp
            have hupper : (n : ℝ) * Real.exp (-v) ≤ w.X + w.H := by
              have hmul := mul_le_mul_of_nonneg_right hcond.2
                (le_of_lt (Real.exp_pos (-v)))
              calc
                (n : ℝ) * Real.exp (-v) ≤
                    ((w.X + w.H) * Real.exp v) * Real.exp (-v) := hmul
                _ = w.X + w.H := by rw [mul_assoc, hexpcancel, mul_one]
            have hcSqLe : c ^ 2 ≤ (w.X + w.H) / (n : ℝ) := by
              apply (le_div_iff₀ hnpos).2
              rw [hcSq]
              nlinarith [hupper]
            have hratio : (w.X + w.H) / (n : ℝ) < 4 := by
              apply (div_lt_iff₀ hnpos).2
              nlinarith [hmem.1, w.H_upper]
            have hcSqLt : c ^ 2 < 4 := lt_of_le_of_lt hcSqLe hratio
            have hcLe : c ≤ 2 := by nlinarith [sq_nonneg (c - 2)]
            simpa [hone] using hcLe
        _ = 2 * (S.card : ℝ) := by simp; ring
    have hlargeScalar (n : ℕ) :
        |c * A n - D n| ≤ c * A n + D n := by
      calc
        |c * A n - D n| = |c * A n + -D n| := by rw [sub_eq_add_neg]
        _ ≤ |c * A n| + |-D n| := abs_add_le _ _
        _ = c * A n + D n := by
          rw [abs_mul, abs_of_nonneg hc0, abs_of_nonneg (by
            rcases hA01 n with h | h <;> simp [h]), abs_neg,
            abs_of_nonneg (hDnonneg n)]
    have htermLarge (n : ℕ) (hn : n ∈ S) :
        ‖mellinShiftWindowTerm w v n‖ ≤ w.B * (c * A n + D n) := by
      rw [mellinShiftWindowTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        ‖w.a n‖ * |c * A n - D n| ≤ w.B * |c * A n - D n| :=
          mul_le_mul_of_nonneg_right (hcoeff n hn) (abs_nonneg _)
        _ ≤ w.B * (c * A n + D n) :=
          mul_le_mul_of_nonneg_left (hlargeScalar n) w.B_nonneg
    have hsupportCount : (S.card : ℝ) ≤ 3 * w.X := by
      dsimp [S]
      exact mellinWindowSupportIndices_card_le w
    have hlargeInside :
        (∑ n ∈ S, c * A n) + (∑ n ∈ S, D n) ≤ 8 * w.X := by
      have hsumA := hshiftCount
      have hsumD := hDcount
      have hcard := hsupportCount
      nlinarith
    calc
      ‖∑ n ∈ S, mellinShiftWindowTerm w v n‖ ≤
          ∑ n ∈ S, ‖mellinShiftWindowTerm w v n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S, w.B * (c * A n + D n) :=
        Finset.sum_le_sum fun n hn => htermLarge n hn
      _ = w.B * ((∑ n ∈ S, c * A n) + (∑ n ∈ S, D n)) := by
        calc
          _ = S.sum (fun n => (w.B * c) * A n + w.B * D n) := by
            apply Finset.sum_congr rfl
            intro n hn
            ring
          _ = (w.B * c) * (∑ n ∈ S, A n) + w.B * (∑ n ∈ S, D n) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ = _ := by
            rw [← Finset.mul_sum (s := S) (f := fun n => A n) c]
            ring
      _ ≤ w.B * (8 * w.X) := mul_le_mul_of_nonneg_left hlargeInside w.B_nonneg
      _ ≤ w.B * (32 * w.X * |v| + 8) := by
        apply mul_le_mul_of_nonneg_left _ w.B_nonneg
        nlinarith [w.X_lower, abs_nonneg v, hvlarge]

/-- The denominator including the interval length is nonzero as well. -/
theorem mellinWindowFullDenominator_ne_zero
    (w : MellinWindowData) (t : ℝ) :
    (↑w.H : ℂ) *
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast w.H_pos.ne'
  · exact mellinWindowDenominator_ne_zero t

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.mellinWindowData
#print axioms FractionalPrimes.Literature.Polynomial.mellinWindowDenominator_ne_zero
#print axioms FractionalPrimes.Literature.Polynomial.mellinWindowFullDenominator_ne_zero
#print axioms FractionalPrimes.Literature.Polynomial.shiftedWindowError
