module

public import FractionalPrimes.Literature.Harmonic.FrequencyProjection
public import FractionalPrimes.Literature.Harmonic.MikhlinAdapter
public import FractionalPrimes.Literature.Harmonic.FiniteSignMoment

/-!
# Frequency resolution and square function (`ha:lp`)

This file starts the source-faithful resolution lemma with its exact support
and finite telescoping assertions. The sequence-space operators and the
Littlewood--Paley estimate are developed below these finite symbol facts.
-/

@[expose] public section

open scoped BigOperators ContDiff FourierTransform

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.Multiplier

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The real 1-periodic lift of a torus frequency projection, using the
half-open representative interval `(-1/2,1/2]`. -/
def frequencyProjectionPeriodicLift (c : ℝ) (h : ℤ) (ξ : ℝ) : ℂ :=
  (frequencyProjectionSymbolRepresentative c h
    (toIocMod (by norm_num : (0 : ℝ) < 1) (-(1 / 2 : ℝ)) ξ) : ℂ)

theorem frequencyProjectionPeriodicLift_periodic (c : ℝ) (h : ℤ) :
    Function.Periodic (frequencyProjectionPeriodicLift c h) 1 := by
  intro ξ
  simp [frequencyProjectionPeriodicLift, toIocMod_add_right]

theorem frequencyProjectionPeriodicLift_eq_torusSymbol
    (c : ℝ) (h : ℤ) (ξ : ℝ) :
    frequencyProjectionPeriodicLift c h ξ =
      (frequencyProjectionSymbol c h (ξ : Torus) : ℂ) := by
  let y : ℝ := toIocMod (by norm_num : (0 : ℝ) < 1) (-(1 / 2 : ℝ)) ξ
  have hy : y ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    have hy' : y ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
      dsimp [y]
      exact toIocMod_mem_Ioc (by norm_num : (0 : ℝ) < 1) (-(1 / 2 : ℝ)) ξ
    simpa only [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by ring] using hy'
  have hcoe : (y : Torus) = (ξ : Torus) := by
    have hyval : y = ξ -
        toIocDiv (by norm_num : (0 : ℝ) < 1) (-(1 / 2 : ℝ)) ξ • (1 : ℝ) := by
      rfl
    rw [hyval]
    simp only [AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_period,
      zsmul_zero, sub_zero]
  rw [frequencyProjectionPeriodicLift, ← hcoe,
    frequencyProjectionSymbol_coe (c := c) (h := h) hy]

/-- The topological support of the fixed cutoff, and hence of each of its
first two derivatives, lies in the closed support interval of the bump. -/
theorem frequencyProjectionCutoff_tsupport_subset_Icc :
    tsupport frequencyProjectionCutoff ⊆ Set.Icc (-(3 / 8 : ℝ)) (3 / 8) := by
  have hnonzero_support :
      Function.support frequencyProjectionCutoff ⊆ Set.Icc (-(3 / 8 : ℝ)) (3 / 8) := by
    intro ξ hξ
    have hne : frequencyProjectionCutoff ξ ≠ 0 := by
      simpa [Function.mem_support] using hξ
    have habs : |ξ| ≤ 3 / 8 := by
      by_contra hnot
      exact hne (frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs ξ
        (lt_of_not_ge hnot))
    exact abs_le.mp habs
  rw [tsupport]
  exact closure_minimal hnonzero_support isClosed_Icc

/-- First derivative of the fixed scaled cutoff. -/
theorem frequencyProjectionCutoff_deriv (ξ : ℝ) :
    deriv frequencyProjectionCutoff ξ =
      (1 / 2 : ℝ) * deriv ψ (ξ / 2) := by
  have hfun : frequencyProjectionCutoff = fun x : ℝ => ψ ((1 / 2 : ℝ) * x) := by
    funext x
    change ψ (x / 2) = ψ ((1 / 2 : ℝ) * x)
    congr 1
    ring
  rw [hfun, deriv_comp_mul_left]
  rw [show (1 / 2 : ℝ) * ξ = ξ / 2 by ring]
  rfl

/-- Second derivative of the fixed scaled cutoff. -/
theorem frequencyProjectionCutoff_iteratedDeriv_two (ξ : ℝ) :
    iteratedDeriv 2 frequencyProjectionCutoff ξ =
      (1 / 4 : ℝ) * iteratedDeriv 2 ψ (ξ / 2) := by
  have hfun : frequencyProjectionCutoff = fun x : ℝ => ψ ((1 / 2 : ℝ) * x) := by
    funext x
    change ψ (x / 2) = ψ ((1 / 2 : ℝ) * x)
    congr 1
    ring
  rw [hfun]
  calc
    iteratedDeriv 2 (fun x : ℝ => ψ ((1 / 2 : ℝ) * x)) ξ =
        (1 / 2 : ℝ) ^ 2 * iteratedDeriv 2 ψ ((1 / 2 : ℝ) * ξ) := by
      rw [iteratedDeriv_comp_const_mul (n := 2)
        (ψ_contDiff.of_le (by norm_num)) (1 / 2 : ℝ)]
    _ = (1 / 4 : ℝ) * iteratedDeriv 2 ψ (ξ / 2) := by
      rw [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num,
        show (1 / 2 : ℝ) * ξ = ξ / 2 by ring]

/-- The first derivative is bounded by the exact derivative supremum fixed
for the source cutoff. -/
theorem frequencyProjectionCutoff_deriv_norm_le (ξ : ℝ) :
    ‖deriv frequencyProjectionCutoff ξ‖ ≤ ψDerivSup / 2 := by
  rw [frequencyProjectionCutoff_deriv, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * ‖deriv ψ (ξ / 2)‖ ≤
        (1 / 2 : ℝ) * ψDerivSup :=
      mul_le_mul_of_nonneg_left (norm_deriv_ψ_le_sup _) (by norm_num)
    _ = ψDerivSup / 2 := by ring

/-- The second derivative is bounded by the exact second derivative
supremum fixed for the source cutoff. -/
theorem frequencyProjectionCutoff_iteratedDeriv_two_norm_le (ξ : ℝ) :
    ‖iteratedDeriv 2 frequencyProjectionCutoff ξ‖ ≤ ψSecondDerivSup / 4 := by
  rw [frequencyProjectionCutoff_iteratedDeriv_two, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  calc
    (1 / 4 : ℝ) * ‖iteratedDeriv 2 ψ (ξ / 2)‖ ≤
        (1 / 4 : ℝ) * ψSecondDerivSup :=
      mul_le_mul_of_nonneg_left (norm_iteratedDeriv_two_ψ_le_sup _) (by norm_num)
    _ = ψSecondDerivSup / 4 := by ring

/-- Derivative scaling for each dyadic cutoff term. -/
theorem frequencyProjectionScaledCutoff_deriv (a ξ : ℝ) :
    deriv (fun x : ℝ => frequencyProjectionCutoff (a * x)) ξ =
      a * deriv frequencyProjectionCutoff (a * ξ) := by
  simpa [smul_eq_mul] using deriv_comp_mul_left a frequencyProjectionCutoff ξ

/-- Second derivative scaling for each dyadic cutoff term. -/
theorem frequencyProjectionScaledCutoff_iteratedDeriv_two (a ξ : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff (a * x)) ξ =
      a ^ 2 * iteratedDeriv 2 frequencyProjectionCutoff (a * ξ) := by
  simpa using congrFun
    (iteratedDeriv_comp_const_mul (n := 2)
      (frequencyProjectionCutoff_contDiff.of_le (by norm_num)) a) ξ

/-- Nonzero first derivative can occur only in the cutoff support. -/
theorem frequencyProjectionCutoff_deriv_support_bound {ξ : ℝ}
    (hξ : deriv frequencyProjectionCutoff ξ ≠ 0) : |ξ| ≤ 3 / 8 := by
  have hs : ξ ∈ Function.support (deriv frequencyProjectionCutoff) := by
    simpa [Function.mem_support] using hξ
  have hs' : ξ ∈ tsupport (deriv frequencyProjectionCutoff) := subset_closure hs
  have ht : ξ ∈ tsupport frequencyProjectionCutoff :=
    (tsupport_deriv_subset (f := frequencyProjectionCutoff)) hs'
  exact abs_le.mpr (frequencyProjectionCutoff_tsupport_subset_Icc ht)

/-- The first derivative vanishes throughout the closed plateau, including
its boundary; the boundary case follows from the local-extremum derivative
test. -/
theorem frequencyProjectionCutoff_deriv_eq_zero_of_abs_le {ξ : ℝ}
    (hξ : |ξ| ≤ 1 / 4) : deriv frequencyProjectionCutoff ξ = 0 := by
  have hcut : frequencyProjectionCutoff ξ = 1 :=
    frequencyProjectionCutoff_eq_one_of_abs_le ξ hξ
  have hmax : IsLocalMax frequencyProjectionCutoff ξ := by
    change ∀ᶠ y in nhds ξ, frequencyProjectionCutoff y ≤ frequencyProjectionCutoff ξ
    filter_upwards with y
    rw [hcut]
    exact frequencyProjectionCutoff_le_one y
  exact hmax.deriv_eq_zero

/-- Nonzero first derivative lies strictly outside the plateau. -/
theorem frequencyProjectionCutoff_deriv_lower_support_bound {ξ : ℝ}
    (hξ : deriv frequencyProjectionCutoff ξ ≠ 0) : 1 / 4 < |ξ| := by
  by_contra hnot
  exact hξ (frequencyProjectionCutoff_deriv_eq_zero_of_abs_le (le_of_not_gt hnot))

/-- The closed support of the first derivative is the closed transition
annulus. -/
theorem frequencyProjectionCutoff_deriv_tsupport_annulus :
    tsupport (deriv frequencyProjectionCutoff) ⊆
      {ξ : ℝ | |ξ| ∈ Set.Icc (1 / 4 : ℝ) (3 / 8 : ℝ)} := by
  have hsupport : Function.support (deriv frequencyProjectionCutoff) ⊆
      {ξ : ℝ | |ξ| ∈ Set.Icc (1 / 4 : ℝ) (3 / 8 : ℝ)} := by
    intro ξ hξ
    have hne : deriv frequencyProjectionCutoff ξ ≠ 0 := by
      simpa [Function.mem_support] using hξ
    exact Set.mem_Icc.mpr ⟨(frequencyProjectionCutoff_deriv_lower_support_bound hne).le,
      frequencyProjectionCutoff_deriv_support_bound hne⟩
  have hclosed : IsClosed
      {ξ : ℝ | |ξ| ∈ Set.Icc (1 / 4 : ℝ) (3 / 8 : ℝ)} := by
    exact isClosed_Icc.preimage continuous_abs
  rw [tsupport]
  exact closure_minimal hsupport hclosed

/-- The second derivative is also confined to the closed transition annulus.
This follows because the support of a derivative lies in the topological
support of its input. -/
theorem frequencyProjectionCutoff_iteratedDeriv_two_support_annulus
    {ξ : ℝ} (hξ : iteratedDeriv 2 frequencyProjectionCutoff ξ ≠ 0) :
    |ξ| ∈ Set.Icc (1 / 4 : ℝ) (3 / 8 : ℝ) := by
  have hs : ξ ∈ Function.support (iteratedDeriv 2 frequencyProjectionCutoff) := by
    simpa [Function.mem_support] using hξ
  have hs' : ξ ∈ Function.support (deriv (deriv frequencyProjectionCutoff)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hs
  have hs'' : ξ ∈ tsupport (deriv (deriv frequencyProjectionCutoff)) := subset_closure hs'
  have ht : ξ ∈ tsupport (deriv frequencyProjectionCutoff) :=
    (tsupport_deriv_subset (f := deriv frequencyProjectionCutoff)) hs''
  exact frequencyProjectionCutoff_deriv_tsupport_annulus ht

/-- Nonzero second derivative can occur only in the cutoff support. -/
theorem frequencyProjectionCutoff_iteratedDeriv_two_support_bound {ξ : ℝ}
    (hξ : iteratedDeriv 2 frequencyProjectionCutoff ξ ≠ 0) : |ξ| ≤ 3 / 8 := by
  have hs : ξ ∈ Function.support (iteratedDeriv 2 frequencyProjectionCutoff) := by
    simpa [Function.mem_support] using hξ
  have hs' : ξ ∈ Function.support (deriv (deriv frequencyProjectionCutoff)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hs
  have hs'' : ξ ∈ tsupport (deriv (deriv frequencyProjectionCutoff)) := subset_closure hs'
  have ht : ξ ∈ tsupport (deriv frequencyProjectionCutoff) :=
    (tsupport_deriv_subset (f := deriv frequencyProjectionCutoff)) hs''
  have ht' : ξ ∈ tsupport frequencyProjectionCutoff :=
    (tsupport_deriv_subset (f := frequencyProjectionCutoff)) ht
  exact abs_le.mpr (frequencyProjectionCutoff_tsupport_subset_Icc ht')

/-- The weighted first derivative of a scaled cutoff is independent of the
scale whenever it is nonzero. -/
theorem frequencyProjectionScaledCutoff_weightedDeriv_le
    {a ξ : ℝ} (ha : 0 < a)
    (hne : deriv (fun x : ℝ => frequencyProjectionCutoff (a * x)) ξ ≠ 0) :
    ‖ξ * deriv (fun x : ℝ => frequencyProjectionCutoff (a * x)) ξ‖ ≤
      (3 / 8 : ℝ) * (ψDerivSup / 2) := by
  rw [frequencyProjectionScaledCutoff_deriv]
  have hscaled : a * deriv frequencyProjectionCutoff (a * ξ) ≠ 0 := by
    simpa [frequencyProjectionScaledCutoff_deriv] using hne
  have hderiv : deriv frequencyProjectionCutoff (a * ξ) ≠ 0 := by
    intro hz
    apply hscaled
    rw [hz]
    ring
  have harg := frequencyProjectionCutoff_deriv_support_bound hderiv
  calc
    ‖ξ * (a * deriv frequencyProjectionCutoff (a * ξ))‖ =
        |a * ξ| * ‖deriv frequencyProjectionCutoff (a * ξ)‖ := by
      calc
        ‖ξ * (a * deriv frequencyProjectionCutoff (a * ξ))‖ =
            |ξ| * (|a| * ‖deriv frequencyProjectionCutoff (a * ξ)‖) := by
          simp only [norm_mul, Real.norm_eq_abs]
        _ = |a * ξ| * ‖deriv frequencyProjectionCutoff (a * ξ)‖ := by
          rw [abs_mul, abs_of_pos ha]
          ring
    _ ≤ (3 / 8 : ℝ) * (ψDerivSup / 2) :=
      mul_le_mul harg (frequencyProjectionCutoff_deriv_norm_le _)
        (by positivity) (by positivity [ψDerivSup_nonneg])

/-- The derivative support of a positive dilation is confined to the fixed
transition annulus after rescaling. -/
theorem frequencyProjectionScaledCutoff_support_bounds
    {a ξ : ℝ} (ha : 0 < a)
    (hne : deriv (fun x : ℝ => frequencyProjectionCutoff (a * x)) ξ ≠ 0) :
    1 / 4 < |a * ξ| ∧ |a * ξ| ≤ 3 / 8 := by
  have hscaled : a * deriv frequencyProjectionCutoff (a * ξ) ≠ 0 := by
    simpa [frequencyProjectionScaledCutoff_deriv] using hne
  have hderiv : deriv frequencyProjectionCutoff (a * ξ) ≠ 0 := by
    intro hz
    apply hscaled
    rw [hz]
    ring
  exact ⟨frequencyProjectionCutoff_deriv_lower_support_bound hderiv,
    frequencyProjectionCutoff_deriv_support_bound hderiv⟩

/-- The second derivative support of a positive dilation lies in the same
closed transition annulus. -/
theorem frequencyProjectionScaledCutoff_iteratedDerivTwo_support_bounds
    {a ξ : ℝ} (ha : 0 < a)
    (hne : iteratedDeriv 2
      (fun x : ℝ => frequencyProjectionCutoff (a * x)) ξ ≠ 0) :
    |a * ξ| ∈ Set.Icc (1 / 4 : ℝ) (3 / 8 : ℝ) := by
  have hscaled : a ^ 2 * iteratedDeriv 2 frequencyProjectionCutoff (a * ξ) ≠ 0 := by
    simpa [frequencyProjectionScaledCutoff_iteratedDeriv_two] using hne
  have hderiv : iteratedDeriv 2 frequencyProjectionCutoff (a * ξ) ≠ 0 := by
    intro hz
    apply hscaled
    rw [hz]
    ring
  exact frequencyProjectionCutoff_iteratedDeriv_two_support_annulus hderiv

/-- The exact positive dyadic scale used by the resolution symbols. -/
def frequencyProjectionDyadicScale (c : ℝ) (j : ℕ) : ℝ :=
  Real.rpow 2 ((j : ℝ) * c)

/-- The cutoff at the `j`th exact dyadic scale. -/
def frequencyProjectionDilationCutoff (c : ℝ) (j : ℕ) (ξ : ℝ) : ℝ :=
  frequencyProjectionCutoff (frequencyProjectionDyadicScale c j * ξ)

/-- Smoothness of each dilated cutoff, used when differentiating the finite
signed expansion. -/
theorem frequencyProjectionDilationCutoff_contDiff (c : ℝ) (j : ℕ) :
    ContDiff ℝ (∞ : ℕ∞ω) (frequencyProjectionDilationCutoff c j) := by
  change ContDiff ℝ (∞ : ℕ∞ω)
    (frequencyProjectionCutoff ∘ fun x : ℝ => frequencyProjectionDyadicScale c j * x)
  exact frequencyProjectionCutoff_contDiff.comp (by fun_prop)

/-- The natural-index version of the source symbol is the adjacent-scale
difference of the dilated cutoffs, including the inhomogeneous term. -/
theorem frequencyProjectionSymbolRepresentative_nat
    (c ξ : ℝ) (h : ℕ) :
    frequencyProjectionSymbolRepresentative c (h : ℤ) ξ =
      if h = 0 then 1 - frequencyProjectionDilationCutoff c 0 ξ
      else frequencyProjectionDilationCutoff c (h - 1) ξ -
        frequencyProjectionDilationCutoff c h ξ := by
  by_cases hh : h = 0
  · subst h
    simp [frequencyProjectionSymbolRepresentative,
      frequencyProjectionDilationCutoff, frequencyProjectionDyadicScale]
  · have hhpos : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr hh
    have hcast : ((h : ℤ) : ℝ) = (h : ℝ) := by norm_cast
    have hsubcast : ((h : ℤ) : ℝ) - 1 = ((h - 1 : ℕ) : ℝ) := by
      rw [hcast]
      norm_cast
    have hne : (h : ℤ) ≠ 0 := by omega
    simp only [frequencyProjectionSymbolRepresentative,
      if_neg (by omega : ¬ (h : ℤ) < 0), if_neg hne]
    simp only [if_neg hh]
    rw [hsubcast, hcast]
    rfl

/-- Finite randomized source symbols, represented on the real fundamental
interval before periodic extension. -/
def finiteFrequencyProjectionSignedSymbol
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ h ∈ Finset.range (N + 1),
    ε h * frequencyProjectionSymbolRepresentative c (h : ℤ) ξ

/-- Extend a finite sign sequence by zero beyond its truncation. -/
def frequencyProjectionSignExtension (N : ℕ) (ε : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ N then ε j else 0

/-- Adjacent differences of the zero-extended sign sequence. -/
def frequencyProjectionSignDifference (N : ℕ) (ε : ℕ → ℝ) (j : ℕ) : ℝ :=
  frequencyProjectionSignExtension N ε (j + 1) -
    frequencyProjectionSignExtension N ε j

/-- Discrete summation by parts rewrites a finite signed resolution as a
constant plus adjacent differences of the dilated cutoffs. -/
theorem finiteFrequencyProjectionSignedSymbol_expansion
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) (ξ : ℝ) :
    finiteFrequencyProjectionSignedSymbol c N ε ξ =
      ε 0 + ∑ j ∈ Finset.range (N + 1),
        frequencyProjectionSignDifference N ε j *
          frequencyProjectionDilationCutoff c j ξ := by
  induction N with
  | zero =>
      simp [finiteFrequencyProjectionSignedSymbol,
        frequencyProjectionSymbolRepresentative_nat,
        frequencyProjectionSignDifference, frequencyProjectionSignExtension,
        frequencyProjectionDilationCutoff]
      ring
  | succ N ih =>
      have hcoeff (j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
          frequencyProjectionSignDifference (N + 1) ε j =
            frequencyProjectionSignDifference N ε j +
              (if j = N then ε (N + 1) else 0) := by
        have hjle : j ≤ N := by simpa using Finset.mem_range.mp hj
        by_cases hEq : j = N
        · subst j
          simp [frequencyProjectionSignDifference, frequencyProjectionSignExtension]
          ring
        · have hjlt : j < N := by omega
          have hj1 : j + 1 ≤ N := by omega
          simp [frequencyProjectionSignDifference, frequencyProjectionSignExtension,
            hjle, hj1, hEq]
          omega
      have hsumCoeff :
          (∑ j ∈ Finset.range (N + 1),
            frequencyProjectionSignDifference (N + 1) ε j *
              frequencyProjectionDilationCutoff c j ξ) =
            (∑ j ∈ Finset.range (N + 1),
              frequencyProjectionSignDifference N ε j *
                frequencyProjectionDilationCutoff c j ξ) +
              ε (N + 1) * frequencyProjectionDilationCutoff c N ξ := by
        calc
          _ = ∑ j ∈ Finset.range (N + 1),
                (frequencyProjectionSignDifference N ε j +
                  (if j = N then ε (N + 1) else 0)) *
                    frequencyProjectionDilationCutoff c j ξ := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hcoeff j hj]
          _ = (∑ j ∈ Finset.range (N + 1),
                frequencyProjectionSignDifference N ε j *
                  frequencyProjectionDilationCutoff c j ξ) +
                ∑ j ∈ Finset.range (N + 1),
                  (if j = N then ε (N + 1) else 0) *
                    frequencyProjectionDilationCutoff c j ξ := by
              simp_rw [add_mul]
              rw [Finset.sum_add_distrib]
          _ = (∑ j ∈ Finset.range (N + 1),
                frequencyProjectionSignDifference N ε j *
                  frequencyProjectionDilationCutoff c j ξ) +
                ε (N + 1) * frequencyProjectionDilationCutoff c N ξ := by
              congr 1
              have hsingle := Finset.sum_eq_single N
                (s := Finset.range (N + 1))
                (f := fun j => (if j = N then ε (N + 1) else 0) *
                  frequencyProjectionDilationCutoff c j ξ)
                (fun j hj hne => by simp [hne])
                (fun hnot => by exact (hnot (by simp)).elim)
              simpa using hsingle
      have hlast : frequencyProjectionSignDifference (N + 1) ε (N + 1) =
          -ε (N + 1) := by
        simp [frequencyProjectionSignDifference, frequencyProjectionSignExtension]
      have hsource :
          finiteFrequencyProjectionSignedSymbol c (N + 1) ε ξ =
            finiteFrequencyProjectionSignedSymbol c N ε ξ +
              ε (N + 1) * (frequencyProjectionDilationCutoff c N ξ -
                frequencyProjectionDilationCutoff c (N + 1) ξ) := by
        rw [finiteFrequencyProjectionSignedSymbol, Finset.sum_range_succ,
          finiteFrequencyProjectionSignedSymbol]
        rw [frequencyProjectionSymbolRepresentative_nat]
        have hpos : N + 1 ≠ 0 := by omega
        simp [hpos, frequencyProjectionSymbolRepresentative_nat]
      have hsumNext :
          (∑ j ∈ Finset.range (N + 1 + 1),
            frequencyProjectionSignDifference (N + 1) ε j *
              frequencyProjectionDilationCutoff c j ξ) =
            (∑ j ∈ Finset.range (N + 1),
              frequencyProjectionSignDifference (N + 1) ε j *
                frequencyProjectionDilationCutoff c j ξ) +
              frequencyProjectionSignDifference (N + 1) ε (N + 1) *
                frequencyProjectionDilationCutoff c (N + 1) ξ := by
        rw [Finset.sum_range_succ]
      rw [hsource, ih, hsumNext, hsumCoeff, hlast]
      ring

/-- Sign differences in the finite summation-by-parts expansion have size at
most two. -/
theorem frequencyProjectionSignDifference_abs_le_two
    (N : ℕ) (ε : ℕ → ℝ) (hε : ∀ h ≤ N, |ε h| = 1) (j : ℕ) :
    |frequencyProjectionSignDifference N ε j| ≤ 2 := by
  by_cases hj : j ≤ N
  · by_cases hj1 : j + 1 ≤ N
    · simp [frequencyProjectionSignDifference, frequencyProjectionSignExtension,
        hj, hj1]
      calc
        |ε (j + 1) - ε j| ≤ |ε (j + 1)| + |ε j| := abs_sub _ _
        _ = 2 := by rw [hε (j + 1) hj1, hε j hj]; norm_num
    · have hjlt : j < N + 1 := by omega
      have hjEq : j = N := by omega
      subst j
      simp [frequencyProjectionSignDifference, frequencyProjectionSignExtension]
      rw [hε N le_rfl]
      norm_num
  · have hj1 : ¬ j + 1 ≤ N := by omega
    simp [frequencyProjectionSignDifference, frequencyProjectionSignExtension,
      hj, hj1]

/-- The derivative of a finite signed symbol is the finite sum of the
derivatives of the dilated cutoffs with the adjacent-difference
coefficients. -/
theorem finiteFrequencyProjectionSignedSymbol_deriv
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) (ξ : ℝ) :
    deriv (fun x : ℝ => finiteFrequencyProjectionSignedSymbol c N ε x) ξ =
      ∑ j ∈ Finset.range (N + 1),
        frequencyProjectionSignDifference N ε j *
          deriv (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j * x)) ξ := by
  have hfun : (fun x : ℝ => finiteFrequencyProjectionSignedSymbol c N ε x) =
      fun x => ε 0 + ∑ j ∈ Finset.range (N + 1),
        frequencyProjectionSignDifference N ε j *
          frequencyProjectionDilationCutoff c j x := by
    funext x
    exact finiteFrequencyProjectionSignedSymbol_expansion c N ε x
  rw [hfun, deriv_const_add]
  rw [deriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [deriv_const_mul_field]
    rfl
  · intro j hj
    have hterm : ContDiff ℝ (∞ : ℕ∞ω)
        (fun x : ℝ => frequencyProjectionSignDifference N ε j *
          frequencyProjectionDilationCutoff c j x) :=
      contDiff_const.mul (frequencyProjectionDilationCutoff_contDiff c j)
    exact (hterm.differentiable (by norm_num)).differentiableAt

/-- The second derivative of the finite signed symbol has the corresponding
second-derivative expansion. -/
theorem finiteFrequencyProjectionSignedSymbol_iteratedDeriv_two
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) (ξ : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => finiteFrequencyProjectionSignedSymbol c N ε x) ξ =
      ∑ j ∈ Finset.range (N + 1),
        frequencyProjectionSignDifference N ε j *
          iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j * x)) ξ := by
  have hfun : (fun x : ℝ => finiteFrequencyProjectionSignedSymbol c N ε x) =
      fun x => ε 0 + ∑ j ∈ Finset.range (N + 1),
        frequencyProjectionSignDifference N ε j *
          frequencyProjectionDilationCutoff c j x := by
    funext x
    exact finiteFrequencyProjectionSignedSymbol_expansion c N ε x
  rw [hfun, iteratedDeriv_const_add (by norm_num : 0 < 2)]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    have hterm : ContDiff ℝ (∞ : ℕ∞ω)
        (fun x : ℝ => frequencyProjectionSignDifference N ε j *
          frequencyProjectionDilationCutoff c j x) :=
      contDiff_const.mul (frequencyProjectionDilationCutoff_contDiff c j)
    calc
      iteratedDeriv 2 (fun x : ℝ => frequencyProjectionSignDifference N ε j *
          frequencyProjectionDilationCutoff c j x) ξ =
        frequencyProjectionSignDifference N ε j *
          iteratedDeriv 2 (frequencyProjectionDilationCutoff c j) ξ :=
        iteratedDeriv_const_mul (n := 2)
          (c := frequencyProjectionSignDifference N ε j)
          (f := frequencyProjectionDilationCutoff c j)
          ((frequencyProjectionDilationCutoff_contDiff c j).contDiffAt.of_le
            (by norm_num : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)))
      _ = frequencyProjectionSignDifference N ε j *
          iteratedDeriv 2 (fun x : ℝ =>
            frequencyProjectionCutoff (frequencyProjectionDyadicScale c j * x)) ξ := by
        rfl
  · intro j hj
    have hterm : ContDiff ℝ (∞ : ℕ∞ω)
        (fun x : ℝ => frequencyProjectionSignDifference N ε j *
          frequencyProjectionDilationCutoff c j x) :=
      contDiff_const.mul (frequencyProjectionDilationCutoff_contDiff c j)
    exact hterm.contDiffAt.of_le (by norm_num : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))

/-- Distinct positive dyadic scales have disjoint derivative-transition
annuli when `c>1`. -/
theorem frequencyProjectionScaledCutoff_derivatives_disjoint
    {c ξ : ℝ} (hc : 1 < c) {j k : ℕ} (hjk : j < k)
    (hj : deriv (fun x : ℝ => frequencyProjectionCutoff
      (frequencyProjectionDyadicScale c j * x)) ξ ≠ 0)
    (hk : deriv (fun x : ℝ => frequencyProjectionCutoff
      (frequencyProjectionDyadicScale c k * x)) ξ ≠ 0) : False := by
  let aj := frequencyProjectionDyadicScale c j
  let ak := frequencyProjectionDyadicScale c k
  have haj : 0 < aj := by
    dsimp [aj, frequencyProjectionDyadicScale]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hak : 0 < ak := by
    dsimp [ak, frequencyProjectionDyadicScale]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hjs := frequencyProjectionScaledCutoff_support_bounds haj hj
  have hks := frequencyProjectionScaledCutoff_support_bounds hak hk
  have hjkR : (j : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hjk
  have hdiff : 1 ≤ (k : ℝ) - (j : ℝ) := by linarith
  have hc0 : 0 < c := by linarith
  have hexp : 1 < ((k : ℝ) - (j : ℝ)) * c := by
    have hmul := mul_le_mul_of_nonneg_right hdiff hc0.le
    linarith
  let ratio := Real.rpow 2 (((k : ℝ) - (j : ℝ)) * c)
  have hratio : 2 < ratio := by
    dsimp [ratio]
    calc
      (2 : ℝ) = Real.rpow 2 1 := (Real.rpow_one 2).symm
      _ < Real.rpow 2 (((k : ℝ) - (j : ℝ)) * c) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  have hratioPos : 0 < ratio := by
    dsimp [ratio]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hscale : ak = aj * ratio := by
    dsimp [ak, aj, ratio, frequencyProjectionDyadicScale]
    rw [show (k : ℝ) * c = (j : ℝ) * c + ((k : ℝ) - (j : ℝ)) * c by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hscaledAbs : |ak * ξ| = |aj * ξ| * ratio := by
    rw [show ak * ξ = (aj * ξ) * ratio by rw [hscale]; ring,
      abs_mul, abs_of_pos hratioPos]
  have hbasePos : 0 < |aj * ξ| := lt_trans (by norm_num) hjs.1
  have hlarge : 1 / 2 < |aj * ξ| * ratio := by
    calc
      (1 / 2 : ℝ) = 2 * (1 / 4 : ℝ) := by norm_num
      _ < 2 * |aj * ξ| := by nlinarith [hjs.1]
      _ < ratio * |aj * ξ| := mul_lt_mul_of_pos_right hratio hbasePos
      _ = |aj * ξ| * ratio := by ring
  rw [hscaledAbs] at hks
  linarith [hks.2, hlarge]

/-- A finite linear combination of dyadically dilated first derivatives has
the uniform weighted bound required for the first Mikhlin seminorm. -/
theorem finiteFrequencyProjectionScaledDerivative_weighted_le
    {c ξ : ℝ} (hc : 1 < c) (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j ≤ N, |a j| ≤ 2) :
    ‖ξ * ∑ j ∈ Finset.range (N + 1),
      a j * deriv (fun x : ℝ => frequencyProjectionCutoff
        (frequencyProjectionDyadicScale c j * x)) ξ‖ ≤
      2 * ((3 / 8 : ℝ) * (ψDerivSup / 2)) := by
  classical
  let active : Finset ℕ := (Finset.range (N + 1)).filter fun j =>
    deriv (fun x : ℝ => frequencyProjectionCutoff
      (frequencyProjectionDyadicScale c j * x)) ξ ≠ 0
  by_cases hactive : active.Nonempty
  · let j₀ := active.min' hactive
    have hj₀mem : j₀ ∈ active := active.min'_mem hactive
    have hj₀range : j₀ ∈ Finset.range (N + 1) := (Finset.mem_filter.mp hj₀mem).1
    have hj₀active : deriv (fun x : ℝ => frequencyProjectionCutoff
        (frequencyProjectionDyadicScale c j₀ * x)) ξ ≠ 0 :=
      (Finset.mem_filter.mp hj₀mem).2
    have hsum :
        (∑ j ∈ Finset.range (N + 1),
          a j * deriv (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j * x)) ξ) =
          a j₀ * deriv (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j₀ * x)) ξ := by
      apply Finset.sum_eq_single_of_mem j₀ hj₀range
      intro j hjrange hjne
      by_cases hjzero : deriv (fun x : ℝ => frequencyProjectionCutoff
          (frequencyProjectionDyadicScale c j * x)) ξ = 0
      · simp [hjzero]
      · have hjmem : j ∈ active := Finset.mem_filter.mpr ⟨hjrange, hjzero⟩
        have hjactive := (Finset.mem_filter.mp hjmem).2
        have hfalse : False := by
          rcases lt_or_gt_of_ne hjne with hlt | hgt
          · exact frequencyProjectionScaledCutoff_derivatives_disjoint
              hc hlt hjactive hj₀active
          · exact frequencyProjectionScaledCutoff_derivatives_disjoint
              hc hgt hj₀active hjactive
        exact hfalse.elim
    have hj₀bound : j₀ ≤ N := by
      have := Finset.mem_range.mp hj₀range
      omega
    have hcoeff := ha j₀ hj₀bound
    have hweight := frequencyProjectionScaledCutoff_weightedDeriv_le
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
        ((j₀ : ℝ) * c)) hj₀active
    rw [hsum]
    calc
      ‖ξ * (a j₀ * deriv (fun x : ℝ => frequencyProjectionCutoff
          (frequencyProjectionDyadicScale c j₀ * x)) ξ)‖ =
          |a j₀| * ‖ξ * deriv (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j₀ * x)) ξ‖ := by
        simp only [norm_mul, Real.norm_eq_abs]
        ring
      _ ≤ 2 * ((3 / 8 : ℝ) * (ψDerivSup / 2)) := by
        calc
          |a j₀| * ‖ξ * deriv (fun x : ℝ => frequencyProjectionCutoff
              (frequencyProjectionDyadicScale c j₀ * x)) ξ‖ ≤
              2 * ‖ξ * deriv (fun x : ℝ => frequencyProjectionCutoff
                (frequencyProjectionDyadicScale c j₀ * x)) ξ‖ :=
            mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
          _ ≤ 2 * ((3 / 8 : ℝ) * (ψDerivSup / 2)) :=
            mul_le_mul_of_nonneg_left hweight (by norm_num)
  · have hsum :
        (∑ j ∈ Finset.range (N + 1),
          a j * deriv (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j * x)) ξ) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjzero : deriv (fun x : ℝ => frequencyProjectionCutoff
          (frequencyProjectionDyadicScale c j * x)) ξ = 0 := by
        by_contra hne
        exact hactive ⟨j, Finset.mem_filter.mpr ⟨hj, hne⟩⟩
      simp [hjzero]
    rw [hsum]
    simp
    positivity [ψDerivSup_nonneg]

/-- Distinct positive dyadic scales also have disjoint supports for their
second derivatives. -/
theorem frequencyProjectionScaledCutoff_iteratedDerivTwo_disjoint
    {c ξ : ℝ} (hc : 1 < c) {j k : ℕ} (hjk : j < k)
    (hj : iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
      (frequencyProjectionDyadicScale c j * x)) ξ ≠ 0)
    (hk : iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
      (frequencyProjectionDyadicScale c k * x)) ξ ≠ 0) : False := by
  let aj := frequencyProjectionDyadicScale c j
  let ak := frequencyProjectionDyadicScale c k
  have haj : 0 < aj := by
    dsimp [aj, frequencyProjectionDyadicScale]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hak : 0 < ak := by
    dsimp [ak, frequencyProjectionDyadicScale]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hjs := frequencyProjectionScaledCutoff_iteratedDerivTwo_support_bounds haj hj
  have hks := frequencyProjectionScaledCutoff_iteratedDerivTwo_support_bounds hak hk
  have hjkR : (j : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hjk
  have hdiff : 1 ≤ (k : ℝ) - (j : ℝ) := by linarith
  have hc0 : 0 < c := by linarith
  have hexp : 1 < ((k : ℝ) - (j : ℝ)) * c := by
    have hmul := mul_le_mul_of_nonneg_right hdiff hc0.le
    linarith
  let ratio := Real.rpow 2 (((k : ℝ) - (j : ℝ)) * c)
  have hratio : 2 < ratio := by
    dsimp [ratio]
    calc
      (2 : ℝ) = Real.rpow 2 1 := (Real.rpow_one 2).symm
      _ < Real.rpow 2 (((k : ℝ) - (j : ℝ)) * c) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  have hratioPos : 0 < ratio := by
    dsimp [ratio]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hscale : ak = aj * ratio := by
    dsimp [ak, aj, ratio, frequencyProjectionDyadicScale]
    rw [show (k : ℝ) * c = (j : ℝ) * c + ((k : ℝ) - (j : ℝ)) * c by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hscaledAbs : |ak * ξ| = |aj * ξ| * ratio := by
    rw [show ak * ξ = (aj * ξ) * ratio by rw [hscale]; ring,
      abs_mul, abs_of_pos hratioPos]
  have hbasePos : 0 < |aj * ξ| := by
    have hlow := hjs.1
    exact lt_of_lt_of_le (by norm_num) hlow
  have hlarge : 1 / 2 < |aj * ξ| * ratio := by
    calc
      (1 / 2 : ℝ) = 2 * (1 / 4 : ℝ) := by norm_num
      _ ≤ 2 * |aj * ξ| := by nlinarith [hjs.1]
      _ < ratio * |aj * ξ| := mul_lt_mul_of_pos_right hratio hbasePos
      _ = |aj * ξ| * ratio := by ring
  rw [hscaledAbs] at hks
  linarith [hks.2, hlarge]

/-- The weighted second derivative of a scaled cutoff is independent of the
scale whenever it is nonzero. -/
theorem frequencyProjectionScaledCutoff_weightedIteratedDerivTwo_le
    {a ξ : ℝ} (ha : 0 < a)
    (hne : iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff (a * x)) ξ ≠ 0) :
    ‖ξ ^ 2 * iteratedDeriv 2
      (fun x : ℝ => frequencyProjectionCutoff (a * x)) ξ‖ ≤
      (3 / 8 : ℝ) ^ 2 * (ψSecondDerivSup / 4) := by
  rw [frequencyProjectionScaledCutoff_iteratedDeriv_two]
  have hscaled : a ^ 2 * iteratedDeriv 2 frequencyProjectionCutoff (a * ξ) ≠ 0 := by
    simpa [frequencyProjectionScaledCutoff_iteratedDeriv_two] using hne
  have hderiv : iteratedDeriv 2 frequencyProjectionCutoff (a * ξ) ≠ 0 := by
    intro hz
    apply hscaled
    rw [hz]
    ring
  have harg := frequencyProjectionCutoff_iteratedDeriv_two_support_bound hderiv
  have hargSq : |a * ξ| ^ 2 ≤ (3 / 8 : ℝ) ^ 2 := by
    nlinarith [abs_nonneg (a * ξ), harg]
  calc
    ‖ξ ^ 2 * (a ^ 2 * iteratedDeriv 2 frequencyProjectionCutoff (a * ξ))‖ =
        |a * ξ| ^ 2 *
          ‖iteratedDeriv 2 frequencyProjectionCutoff (a * ξ)‖ := by
      calc
        _ = |ξ| ^ 2 * (|a| ^ 2 *
              ‖iteratedDeriv 2 frequencyProjectionCutoff (a * ξ)‖) := by
          simp only [norm_mul, Real.norm_eq_abs, abs_pow]
        _ = |a * ξ| ^ 2 *
              ‖iteratedDeriv 2 frequencyProjectionCutoff (a * ξ)‖ := by
          rw [abs_mul, abs_of_pos ha]
          ring
    _ ≤ (3 / 8 : ℝ) ^ 2 * (ψSecondDerivSup / 4) :=
      mul_le_mul hargSq (frequencyProjectionCutoff_iteratedDeriv_two_norm_le _)
        (by positivity) (by positivity [ψSecondDerivSup_nonneg])

/-- A finite linear combination of dyadically dilated second derivatives has
the uniform weighted bound required for the second Mikhlin seminorm. -/
theorem finiteFrequencyProjectionScaledIteratedDerivTwo_weighted_le
    {c ξ : ℝ} (hc : 1 < c) (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j ≤ N, |a j| ≤ 2) :
    ‖ξ ^ 2 * ∑ j ∈ Finset.range (N + 1),
      a j * iteratedDeriv 2
        (fun x : ℝ => frequencyProjectionCutoff
          (frequencyProjectionDyadicScale c j * x)) ξ‖ ≤
      2 * ((3 / 8 : ℝ) ^ 2 * (ψSecondDerivSup / 4)) := by
  classical
  let active : Finset ℕ := (Finset.range (N + 1)).filter fun j =>
    iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
      (frequencyProjectionDyadicScale c j * x)) ξ ≠ 0
  by_cases hactive : active.Nonempty
  · let j₀ := active.min' hactive
    have hj₀mem : j₀ ∈ active := active.min'_mem hactive
    have hj₀range : j₀ ∈ Finset.range (N + 1) := (Finset.mem_filter.mp hj₀mem).1
    have hj₀active : iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
        (frequencyProjectionDyadicScale c j₀ * x)) ξ ≠ 0 :=
      (Finset.mem_filter.mp hj₀mem).2
    have hsum :
        (∑ j ∈ Finset.range (N + 1),
          a j * iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j * x)) ξ) =
          a j₀ * iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j₀ * x)) ξ := by
      apply Finset.sum_eq_single_of_mem j₀ hj₀range
      intro j hjrange hjne
      by_cases hjzero : iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
          (frequencyProjectionDyadicScale c j * x)) ξ = 0
      · simp [hjzero]
      · have hjmem : j ∈ active := Finset.mem_filter.mpr ⟨hjrange, hjzero⟩
        have hjactive := (Finset.mem_filter.mp hjmem).2
        have hfalse : False := by
          rcases lt_or_gt_of_ne hjne with hlt | hgt
          · exact frequencyProjectionScaledCutoff_iteratedDerivTwo_disjoint
              hc hlt hjactive hj₀active
          · exact frequencyProjectionScaledCutoff_iteratedDerivTwo_disjoint
              hc hgt hj₀active hjactive
        exact hfalse.elim
    have hj₀bound : j₀ ≤ N := by
      have := Finset.mem_range.mp hj₀range
      omega
    have hcoeff := ha j₀ hj₀bound
    have hweight := frequencyProjectionScaledCutoff_weightedIteratedDerivTwo_le
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
        ((j₀ : ℝ) * c)) hj₀active
    rw [hsum]
    calc
      ‖ξ ^ 2 * (a j₀ * iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
          (frequencyProjectionDyadicScale c j₀ * x)) ξ)‖ =
          |a j₀| * ‖ξ ^ 2 * iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j₀ * x)) ξ‖ := by
        simp only [norm_mul, Real.norm_eq_abs]
        ring
      _ ≤ 2 * ((3 / 8 : ℝ) ^ 2 * (ψSecondDerivSup / 4)) := by
        calc
          |a j₀| * ‖ξ ^ 2 * iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
              (frequencyProjectionDyadicScale c j₀ * x)) ξ‖ ≤
              2 * ‖ξ ^ 2 * iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
                (frequencyProjectionDyadicScale c j₀ * x)) ξ‖ :=
            mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
          _ ≤ 2 * ((3 / 8 : ℝ) ^ 2 * (ψSecondDerivSup / 4)) :=
            mul_le_mul_of_nonneg_left hweight (by norm_num)
  · have hsum :
        (∑ j ∈ Finset.range (N + 1),
          a j * iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
            (frequencyProjectionDyadicScale c j * x)) ξ) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjzero : iteratedDeriv 2 (fun x : ℝ => frequencyProjectionCutoff
          (frequencyProjectionDyadicScale c j * x)) ξ = 0 := by
        by_contra hne
        exact hactive ⟨j, Finset.mem_filter.mpr ⟨hj, hne⟩⟩
      simp [hjzero]
    rw [hsum]
    simp
    positivity [ψSecondDerivSup_nonneg]

/-- A nonzero inhomogeneous low-frequency symbol lies outside the cutoff's
plateau. -/
theorem frequencyProjectionSymbolRepresentative_support_zero
    (c ξ : ℝ)
    (hs : frequencyProjectionSymbolRepresentative c 0 ξ ≠ 0) :
    1 / 4 < |ξ| := by
  by_contra hξ
  have hcut := frequencyProjectionCutoff_eq_one_of_abs_le ξ (le_of_not_gt hξ)
  have hzero : frequencyProjectionSymbolRepresentative c 0 ξ = 0 := by
    simp [frequencyProjectionSymbolRepresentative, hcut]
  exact hs hzero

/-- For each positive dyadic index, the support lies in the annulus stated in
`ha:lp`. The lower edge is strict because both cutoff arguments lie on the
constant-one plateau below it; the upper edge is strict because both lie
outside the cutoff support above it. -/
theorem frequencyProjectionSymbolRepresentative_support_positive
    {c : ℝ} (hc : 1 < c) {h : ℤ} (hh : 1 ≤ h) {ξ : ℝ}
    (hs : frequencyProjectionSymbolRepresentative c h ξ ≠ 0) :
    (1 / 4 : ℝ) * Real.rpow 2 (-((h : ℝ) * c)) < |ξ| ∧
      |ξ| < (1 / 2 : ℝ) * Real.rpow 2 (-(((h : ℝ) - 1) * c)) := by
  let a : ℝ := Real.rpow 2 (((h : ℝ) - 1) * c)
  let b : ℝ := Real.rpow 2 ((h : ℝ) * c)
  have hhR : 1 ≤ (h : ℝ) := by exact_mod_cast hh
  have hc0 : 0 < c := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  have hnotneg : ¬ h < 0 := by omega
  have hnezero : h ≠ 0 := by omega
  have hlow : (1 / 4 : ℝ) * b⁻¹ < |ξ| := by
    by_contra hξ
    have hξ' : |ξ| ≤ (1 / 4 : ℝ) * b⁻¹ := le_of_not_gt hξ
    have hargB : |b * ξ| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_pos hb]
      calc
        b * |ξ| ≤ b * ((1 / 4 : ℝ) * b⁻¹) := mul_le_mul_of_nonneg_left hξ' hb.le
        _ = 1 / 4 := by field_simp [ne_of_gt hb]
    have hargA : |a * ξ| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_pos ha]
      calc
        a * |ξ| ≤ a * ((1 / 4 : ℝ) * b⁻¹) := mul_le_mul_of_nonneg_left hξ' ha.le
        _ ≤ b * ((1 / 4 : ℝ) * b⁻¹) :=
          mul_le_mul_of_nonneg_right hab (by positivity)
        _ = 1 / 4 := by field_simp [ne_of_gt hb]
    have hcutA := frequencyProjectionCutoff_eq_one_of_abs_le (a * ξ) hargA
    have hcutB := frequencyProjectionCutoff_eq_one_of_abs_le (b * ξ) hargB
    have hzero : frequencyProjectionSymbolRepresentative c h ξ = 0 := by
      unfold frequencyProjectionSymbolRepresentative
      rw [if_neg hnotneg, if_neg hnezero, hcutA, hcutB]
      ring
    exact hs hzero
  have hhigh : |ξ| < (1 / 2 : ℝ) * a⁻¹ := by
    by_contra hξ
    have hξ' : (1 / 2 : ℝ) * a⁻¹ ≤ |ξ| := le_of_not_gt hξ
    have hargA : 3 / 8 < |a * ξ| := by
      rw [abs_mul, abs_of_pos ha]
      have hmul := mul_le_mul_of_nonneg_right hξ' ha.le
      have honehalf : (1 / 2 : ℝ) ≤ a * |ξ| := by
        calc
          (1 / 2 : ℝ) = (1 / 2 : ℝ) * a⁻¹ * a := by field_simp [ne_of_gt ha]
          _ ≤ |ξ| * a := hmul
          _ = a * |ξ| := by ring
      linarith
    have hargB : 3 / 8 < |b * ξ| := by
      rw [abs_mul, abs_of_pos hb]
      have hmul := mul_le_mul_of_nonneg_right hξ' hb.le
      have honehalf : (1 / 2 : ℝ) ≤ a * |ξ| := by
        calc
          (1 / 2 : ℝ) = (1 / 2 : ℝ) * a⁻¹ * a := by field_simp [ne_of_gt ha]
          _ ≤ |ξ| * a := mul_le_mul_of_nonneg_right hξ' ha.le
          _ = a * |ξ| := by ring
      have hscale : a * |ξ| ≤ b * |ξ| := mul_le_mul_of_nonneg_right hab (abs_nonneg ξ)
      calc
        (3 / 8 : ℝ) < 1 / 2 := by norm_num
        _ ≤ a * |ξ| := honehalf
        _ ≤ b * |ξ| := hscale
    have hcutA := frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs (a * ξ) hargA
    have hcutB := frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs (b * ξ) hargB
    have hzero : frequencyProjectionSymbolRepresentative c h ξ = 0 := by
      unfold frequencyProjectionSymbolRepresentative
      rw [if_neg hnotneg, if_neg hnezero, hcutA, hcutB]
      ring
    exact hs hzero
  constructor
  · have hinv : Real.rpow 2 (-((h : ℝ) * c)) = b⁻¹ := by
      dsimp [b]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hinv]
    exact hlow
  · have hinv : Real.rpow 2 (-(((h : ℝ) - 1) * c)) = a⁻¹ := by
      dsimp [a]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hinv]
    exact hhigh

/-- The source support bounds on fundamental representatives of the torus. -/
theorem frequencyProjectionSymbol_support_zero
    {c ξ : ℝ}
    (hξ : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))
    (hs : frequencyProjectionSymbol c 0 ξ ≠ 0) :
    1 / 4 < |ξ| := by
  rw [frequencyProjectionSymbol_coe (c := c) (h := 0) hξ] at hs
  exact frequencyProjectionSymbolRepresentative_support_zero c ξ hs

theorem frequencyProjectionSymbol_support_positive
    {c ξ : ℝ} (hc : 1 < c) {h : ℤ} (hh : 1 ≤ h)
    (hξ : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))
    (hs : frequencyProjectionSymbol c h ξ ≠ 0) :
    (1 / 4 : ℝ) * Real.rpow 2 (-((h : ℝ) * c)) < |ξ| ∧
      |ξ| < (1 / 2 : ℝ) * Real.rpow 2 (-(((h : ℝ) - 1) * c)) := by
  rw [frequencyProjectionSymbol_coe (c := c) (h := h) hξ] at hs
  exact frequencyProjectionSymbolRepresentative_support_positive hc hh hs

/-- Two distinct positive projection symbols cannot both be supported at a
frequency when their indices differ by at least two. -/
theorem frequencyProjectionPositiveSupport_indices_adjacent
    {c ξ : ℝ} {h k : ℤ} (hc : 1 < c) (hh : 1 ≤ h) (hk : 1 ≤ k)
    (hgap : h + 2 ≤ k)
    (hhξ : frequencyProjectionSymbolRepresentative c h ξ ≠ 0)
    (hkξ : frequencyProjectionSymbolRepresentative c k ξ ≠ 0) : False := by
  have hhSupport := frequencyProjectionSymbolRepresentative_support_positive hc hh hhξ
  have hkSupport := frequencyProjectionSymbolRepresentative_support_positive hc hk hkξ
  have hcast : (h : ℝ) + 1 ≤ (k : ℝ) - 1 := by
    exact_mod_cast (show h + 1 ≤ k - 1 by omega)
  have hc0 : 0 < c := by linarith
  have hExp : -(((k : ℝ) - 1) * c) ≤ -(((h : ℝ) + 1) * c) := by
    have := mul_le_mul_of_nonneg_right hcast hc0.le
    linarith
  have hRpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) hExp
  have hsplit : -(((h : ℝ) + 1) * c) = -((h : ℝ) * c) + -c := by ring
  have hsmall : Real.rpow 2 (-c) < 1 / 2 := by
    calc
      Real.rpow 2 (-c) < Real.rpow 2 (-1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 1 / 2 := by
        calc
          Real.rpow 2 (-1) = (2 : ℝ)⁻¹ := Real.rpow_neg_one 2
          _ = 1 / 2 := by norm_num
  have hstep :
      (1 / 2 : ℝ) * Real.rpow 2 (-(((h : ℝ) + 1) * c)) <
        (1 / 4 : ℝ) * Real.rpow 2 (-((h : ℝ) * c)) := by
    have hsum : Real.rpow 2 (-((h : ℝ) * c) + -c) =
        Real.rpow 2 (-((h : ℝ) * c)) * Real.rpow 2 (-c) :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
    rw [hsplit, hsum]
    have hpos : 0 < Real.rpow 2 (-((h : ℝ) * c)) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  have hupper_le_lower :
      (1 / 2 : ℝ) * Real.rpow 2 (-(((k : ℝ) - 1) * c)) <
        (1 / 4 : ℝ) * Real.rpow 2 (-((h : ℝ) * c)) := by
    calc
      (1 / 2 : ℝ) * Real.rpow 2 (-(((k : ℝ) - 1) * c)) ≤
          (1 / 2 : ℝ) * Real.rpow 2 (-(((h : ℝ) + 1) * c)) :=
        mul_le_mul_of_nonneg_left hRpow (by norm_num)
      _ < (1 / 4 : ℝ) * Real.rpow 2 (-((h : ℝ) * c)) := hstep
  linarith [hhSupport.1, hkSupport.2, hupper_le_lower]

/-- The inhomogeneous index zero cannot overlap any positive index at least
two. -/
theorem frequencyProjectionZeroPositiveSupport_no_gap
    {c ξ : ℝ} {k : ℤ} (hc : 1 < c) (hk : 2 ≤ k)
    (hzero : frequencyProjectionSymbolRepresentative c 0 ξ ≠ 0)
    (hkξ : frequencyProjectionSymbolRepresentative c k ξ ≠ 0) : False := by
  have hzeroSupport := frequencyProjectionSymbolRepresentative_support_zero c ξ hzero
  have hkSupport := frequencyProjectionSymbolRepresentative_support_positive hc
    (by omega : 1 ≤ k) hkξ
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hc0 : 0 < c := by linarith
  have hbase : 1 ≤ (k : ℝ) - 1 := by linarith
  have hprod : 1 < ((k : ℝ) - 1) * c := by
    have hmul := mul_le_mul_of_nonneg_right hbase hc0.le
    linarith
  have hscale : Real.rpow 2 (-(((k : ℝ) - 1) * c)) < 1 / 2 := by
    calc
      Real.rpow 2 (-(((k : ℝ) - 1) * c)) < Real.rpow 2 (-1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 1 / 2 := by
        calc
          Real.rpow 2 (-1) = (2 : ℝ)⁻¹ := Real.rpow_neg_one 2
          _ = 1 / 2 := by norm_num
  have hupper : (1 / 2 : ℝ) *
      Real.rpow 2 (-(((k : ℝ) - 1) * c)) < 1 / 4 := by
    calc
      (1 / 2 : ℝ) * Real.rpow 2 (-(((k : ℝ) - 1) * c)) <
          (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_left hscale (by norm_num)
      _ = 1 / 4 := by norm_num
  linarith [hzeroSupport, hkSupport.2, hupper]

/-- The finite set of active inhomogeneous projections among indices `0` to
`N`, at a fixed frequency. -/
def frequencyProjectionActiveIndices (c ξ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun h =>
    frequencyProjectionSymbolRepresentative c (h : ℤ) ξ ≠ 0

/-- At each nonzero frequency at most two symbols in the inhomogeneous
resolution are nonzero. This is the finite overlap bound used for uniform
randomized multiplier estimates. -/
theorem frequencyProjectionActiveIndices_card_le_two
    {c ξ : ℝ} (hc : 1 < c) (N : ℕ) :
    (frequencyProjectionActiveIndices c ξ N).card ≤ 2 := by
  classical
  let A := frequencyProjectionActiveIndices c ξ N
  by_cases hzero : frequencyProjectionSymbolRepresentative c 0 ξ ≠ 0
  · have hsubset : A ⊆ ({0, 1} : Finset ℕ) := by
      intro n hn
      have hnActive : frequencyProjectionSymbolRepresentative c (n : ℤ) ξ ≠ 0 :=
        (Finset.mem_filter.mp hn).2
      by_cases hn0 : n = 0
      · simp [hn0]
      · by_cases hn1 : n = 1
        · simp [hn1]
        · have hnlarge : 2 ≤ n := by omega
          have hfalse := frequencyProjectionZeroPositiveSupport_no_gap hc
            (show 2 ≤ (n : ℤ) by exact_mod_cast hnlarge) hzero hnActive
          exact hfalse.elim
    calc
      A.card ≤ ({0, 1} : Finset ℕ).card := Finset.card_le_card hsubset
      _ = 2 := by simp
  · by_cases hA : A.Nonempty
    · let m := A.min' hA
      have hmMem : m ∈ A := A.min'_mem hA
      have hmActive : frequencyProjectionSymbolRepresentative c (m : ℤ) ξ ≠ 0 :=
        (Finset.mem_filter.mp hmMem).2
      have hmPositive : 1 ≤ m := by
        by_contra hm
        have hm0 : m = 0 := by omega
        exact hzero (by simpa [m, hm0] using hmActive)
      have hsubset : A ⊆ ({m, m + 1} : Finset ℕ) := by
        intro n hn
        have hmn : m ≤ n := A.min'_le n hn
        have hnActive : frequencyProjectionSymbolRepresentative c (n : ℤ) ξ ≠ 0 :=
          (Finset.mem_filter.mp hn).2
        have hnle : n ≤ m + 1 := by
          by_contra hnot
          have hgapNat : m + 2 ≤ n := by omega
          have hgap : (m : ℤ) + 2 ≤ (n : ℤ) := by exact_mod_cast hgapNat
          have hmPosZ : 1 ≤ (m : ℤ) := by exact_mod_cast hmPositive
          have hnPosZ : 1 ≤ (n : ℤ) := by omega
          exact (frequencyProjectionPositiveSupport_indices_adjacent
            hc hmPosZ hnPosZ hgap hmActive hnActive).elim
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases heq : n = m
        · simp [heq]
        · right
          omega
      calc
        A.card ≤ ({m, m + 1} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 2 := Finset.card_pair (by omega)
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      change A.card ≤ 2
      simp [hAempty]

/-- Every symbol in the inhomogeneous resolution has absolute value at most
one, by the fixed cutoff's range bound. -/
theorem frequencyProjectionSymbolRepresentative_abs_le_one
    (c ξ : ℝ) (h : ℕ) :
    |frequencyProjectionSymbolRepresentative c (h : ℤ) ξ| ≤ 1 := by
  by_cases hzero : h = 0
  · subst h
    change |1 - frequencyProjectionCutoff ξ| ≤ 1
    rw [abs_le]
    constructor
    · have hcut := frequencyProjectionCutoff_le_one ξ
      linarith
    · have hcut := frequencyProjectionCutoff_nonneg ξ
      linarith
  · have hpos : 0 < (h : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
    have hne : (h : ℤ) ≠ 0 := by omega
    simp only [frequencyProjectionSymbolRepresentative,
      if_neg (by omega : ¬ (h : ℤ) < 0), if_neg hne]
    change |frequencyProjectionCutoff
        (Real.rpow 2 ((((h : ℤ) : ℝ) - 1) * c) * ξ) -
      frequencyProjectionCutoff (Real.rpow 2 (((h : ℤ) : ℝ) * c) * ξ)| ≤ 1
    rw [abs_le]
    constructor
    · have hfirst := frequencyProjectionCutoff_nonneg
        (Real.rpow 2 ((((h : ℤ) : ℝ) - 1) * c) * ξ)
      have hsecond := frequencyProjectionCutoff_le_one
        (Real.rpow 2 (((h : ℤ) : ℝ) * c) * ξ)
      linarith
    · have hfirst := frequencyProjectionCutoff_le_one
        (Real.rpow 2 ((((h : ℤ) : ℝ) - 1) * c) * ξ)
      have hsecond := frequencyProjectionCutoff_nonneg
        (Real.rpow 2 (((h : ℤ) : ℝ) * c) * ξ)
      linarith

/-- Finite signed sums of the source symbols have the uniform zeroth-order
bound supplied by the overlap count. -/
theorem finiteFrequencyProjectionSignedSymbol_abs_le_two
    {c ξ : ℝ} (hc : 1 < c) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) :
    |∑ h ∈ Finset.range (N + 1),
      ε h * frequencyProjectionSymbolRepresentative c (h : ℤ) ξ| ≤ 2 := by
  classical
  let active := frequencyProjectionActiveIndices c ξ N
  have hterm (h : ℕ) (hh : h ∈ Finset.range (N + 1)) :
      |ε h * frequencyProjectionSymbolRepresentative c (h : ℤ) ξ| ≤
        if frequencyProjectionSymbolRepresentative c (h : ℤ) ξ ≠ 0 then 1 else 0 := by
    by_cases hs : frequencyProjectionSymbolRepresentative c (h : ℤ) ξ = 0
    · simp [hs]
    · have hsign : |ε h| = 1 := by
        apply hε
        simp only [Finset.mem_range] at hh
        omega
      have hbound := frequencyProjectionSymbolRepresentative_abs_le_one c ξ h
      rw [if_pos hs]
      simpa only [abs_mul, hsign, one_mul] using hbound
  calc
    |∑ h ∈ Finset.range (N + 1),
        ε h * frequencyProjectionSymbolRepresentative c (h : ℤ) ξ| ≤
        ∑ h ∈ Finset.range (N + 1),
          |ε h * frequencyProjectionSymbolRepresentative c (h : ℤ) ξ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ Finset.range (N + 1),
          if frequencyProjectionSymbolRepresentative c (h : ℤ) ξ ≠ 0 then 1 else 0 :=
      Finset.sum_le_sum fun h hh => hterm h hh
    _ = (active.card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [active, frequencyProjectionActiveIndices]
    _ ≤ 2 := by
      exact_mod_cast frequencyProjectionActiveIndices_card_le_two hc N

/-- The finite partial sums telescope exactly, including the inhomogeneous
index zero. -/
theorem frequencyProjectionSymbolRepresentative_sum_range
    (c ξ : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
        frequencyProjectionSymbolRepresentative c (k : ℤ) ξ) =
      1 - frequencyProjectionCutoff (Real.rpow 2 ((N : ℝ) * c) * ξ) := by
  induction N with
  | zero =>
      simp [frequencyProjectionSymbolRepresentative, Real.rpow_zero]
  | succ N ih =>
      have hN0 : (↑(N + 1 : ℕ) : ℤ) ≠ 0 := by omega
      have hNn : ¬ (↑(N + 1 : ℕ) : ℤ) < 0 := by omega
      have hcast : ((↑(N + 1 : ℕ) : ℤ) : ℝ) = (N : ℝ) + 1 := by norm_num
      have hterm :
          frequencyProjectionSymbolRepresentative c (↑(N + 1 : ℕ) : ℤ) ξ =
            frequencyProjectionCutoff (Real.rpow 2 ((N : ℝ) * c) * ξ) -
              frequencyProjectionCutoff (Real.rpow 2 ((N : ℝ) * c + c) * ξ) := by
        simp only [frequencyProjectionSymbolRepresentative, if_neg hNn, if_neg hN0]
        rw [hcast]
        have hpow₁ : ((N : ℝ) + 1 - 1) * c = (N : ℝ) * c := by ring
        have hpow₂ : ((N : ℝ) + 1) * c = (N : ℝ) * c + c := by ring
        rw [congrArg (Real.rpow 2) hpow₁, congrArg (Real.rpow 2) hpow₂]
      rw [Finset.sum_range_succ, ih, hterm]
      have hexp : (N : ℝ) * c + c = c * (1 + (N : ℝ)) := by ring
      have hrpow : Real.rpow 2 ((N : ℝ) * c + c) =
          Real.rpow 2 (c * (1 + (N : ℝ))) := congrArg (Real.rpow 2) hexp
      have hnextExp : ((N + 1 : ℕ) : ℝ) * c = c * (1 + (N : ℝ)) := by
        push_cast
        ring
      have hnextRpow : Real.rpow 2 (((N + 1 : ℕ) : ℝ) * c) =
          Real.rpow 2 (c * (1 + (N : ℝ))) := congrArg (Real.rpow 2) hnextExp
      rw [hrpow, hnextRpow]
      ring

end

end FractionalPrimes.Literature.Harmonic

end
