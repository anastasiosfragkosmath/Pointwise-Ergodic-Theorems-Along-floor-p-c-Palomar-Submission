module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownNormalizedFactorMass
public import FractionalPrimes.Literature.DirichletAdapter.SmoothFactorMass
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

/-! Exact weighted-mass bookkeeping for the outer factors in the long-factor
Type-I branch. -/

@[expose] public section

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The inverse-square-root absolute mass of one normalized smooth
Heath--Brown factor, including an auxiliary coefficient of modulus at most
one. -/
noncomputable def smoothHeathBrownTypeIFactorMass
    {X z : ℝ} (f : SmoothHeathBrownFactor X) (ω : ℕ → ℂ) : ℝ :=
  ∑ n ∈ smoothHeathBrownFactorFiniteSupport f,
    ‖smoothHeathBrownWeightedFactorCoefficient (z := z) f ω n‖

/-- Every source-normalized factor has weighted mass at most `5 sqrt N`.
The logarithmic tag is normalized by exactly `4 log X`; Möbius truncation
and the theta cutoff retain their source definitions. -/
theorem smoothHeathBrownTypeIFactorMass_le
    {X z : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (ω : ℕ → ℂ)
    (hω : ∀ n ∈ smoothHeathBrownFactorFiniteSupport f, ‖ω n‖ ≤ 1) :
    smoothHeathBrownTypeIFactorMass (z := z) f ω ≤
      5 * Real.sqrt (smoothHeathBrownFactorScale f) := by
  simpa [smoothHeathBrownTypeIFactorMass] using
    (smoothHeathBrownWeightedFactorMass (z := z) hX f ω hω)

#print axioms smoothHeathBrownTypeIFactorMass_le

/-- The number of logarithmic tags in a finite smooth component. -/
noncomputable def smoothHeathBrownTypeILogFactorCount
    {X : ℝ} {k : ℕ} (fs : Fin k → SmoothHeathBrownFactor X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i =>
    (match fs i with
    | .logarithm _ => true
    | _ => false) = true)).card

/-- The normalized absolute masses of all factors except the selected
long factor multiply to at most `5^19 sqrt(P/N_selected)`. -/
theorem smoothHeathBrownTypeIOuterFactorMassProduct
    {X z : ℝ} (hX : 3 ≤ X) {k : ℕ} (hk : k ≤ 20)
    (fs : Fin k → SmoothHeathBrownFactor X) (selected : Fin k)
    (ω : Fin k → ℕ → ℂ)
    (hω : ∀ i n, n ∈ smoothHeathBrownFactorFiniteSupport (fs i) →
      ‖ω i n‖ ≤ 1) :
    (∏ i ∈ Finset.univ.erase selected,
      smoothHeathBrownTypeIFactorMass (z := z) (fs i) (ω i)) ≤
      5 ^ 19 * Real.sqrt
        ((∏ i : Fin k, smoothHeathBrownFactorScale (fs i)) /
          smoothHeathBrownFactorScale (fs selected)) := by
  let N : Fin k → ℝ := fun i => smoothHeathBrownFactorScale (fs i)
  let mass : Fin k → ℝ := fun i =>
    smoothHeathBrownTypeIFactorMass (z := z) (fs i) (ω i)
  have hN : ∀ i, 0 < N i := by
    intro i
    dsimp [N]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (smoothHeathBrownFactorScale_ge_one (fs i))
  have hmass : ∀ i, 0 ≤ mass i := by
    intro i
    dsimp [mass, smoothHeathBrownTypeIFactorMass]
    exact Finset.sum_nonneg fun n hn => norm_nonneg _
  have hmassBound : ∀ i, i ≠ selected → mass i ≤ 5 * Real.sqrt (N i) := by
    intro i hi
    dsimp [mass, N]
    apply smoothHeathBrownTypeIFactorMass_le (z := z) hX (fs i) (ω i)
    intro n hn
    exact hω i n hn
  simpa [N, mass] using
    (smoothOtherFactorMassProduct hk selected N mass hN hmass hmassBound)

#print axioms smoothHeathBrownTypeIOuterFactorMassProduct

/-- A factor is tagged logarithmic exactly in the second branch of the
source smooth Heath--Brown decomposition. -/
def smoothHeathBrownTypeILogFactor
    {X : ℝ} (f : SmoothHeathBrownFactor X) : Bool :=
  match f with
  | .logarithm _ => true
  | _ => false

theorem smoothHeathBrownTypeILogFactorCount_eq_filter_card
    {X : ℝ} {k : ℕ} (fs : Fin k → SmoothHeathBrownFactor X) :
    smoothHeathBrownTypeILogFactorCount fs =
      (Finset.univ.filter
        (fun i => smoothHeathBrownTypeILogFactor (fs i) = true)).card := by
  classical
  rfl

/-- If a component has at most one logarithmic factor, restoring its exact
`4 log X` normalization and its source coefficient `c` costs at most
`2^10 * 4 log X`. The normalized outer-factor product remains the exact
`5^19 sqrt(P/N)` quantity. -/
theorem smoothHeathBrownTypeIOuterFactorMassProduct_with_source_scalars
    {X z : ℝ} (hX : 3 ≤ X) {k : ℕ} (hk : k ≤ 20)
    (fs : Fin k → SmoothHeathBrownFactor X) (selected : Fin k)
    (ω : Fin k → ℕ → ℂ)
    (hω : ∀ i n, n ∈ smoothHeathBrownFactorFiniteSupport (fs i) →
      ‖ω i n‖ ≤ 1)
    (hlog : smoothHeathBrownTypeILogFactorCount fs ≤ 1)
    (c : ℝ) (hc : |c| ≤ (2 : ℝ) ^ 10) :
    |c| * (4 * Real.log X) ^ smoothHeathBrownTypeILogFactorCount fs *
      (∏ i ∈ Finset.univ.erase selected,
        smoothHeathBrownTypeIFactorMass (z := z) (fs i) (ω i)) ≤
      (2 : ℝ) ^ 10 * (4 * Real.log X) * 5 ^ 19 * Real.sqrt
        ((∏ i : Fin k, smoothHeathBrownFactorScale (fs i)) /
          smoothHeathBrownFactorScale (fs selected)) := by
  have hXpos : 0 < X := by linarith
  have hlogXone : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact le_of_lt (lt_of_lt_of_le Real.exp_one_lt_three hX)
  have hLpos : 0 < 4 * Real.log X := by positivity
  have hLone : 1 ≤ 4 * Real.log X := by linarith
  have hpower :
      (4 * Real.log X) ^ smoothHeathBrownTypeILogFactorCount fs ≤
        4 * Real.log X := by
    have hcount : smoothHeathBrownTypeILogFactorCount fs = 0 ∨
        smoothHeathBrownTypeILogFactorCount fs = 1 := by omega
    rcases hcount with hzero | hone
    · simp [hzero]
      exact hLone
    · simp [hone]
  have hmass := smoothHeathBrownTypeIOuterFactorMassProduct
    (z := z) hX hk fs selected ω hω
  have hmassNonneg :
      0 ≤ ∏ i ∈ Finset.univ.erase selected,
        smoothHeathBrownTypeIFactorMass (z := z) (fs i) (ω i) := by
    apply Finset.prod_nonneg
    intro i hi
    unfold smoothHeathBrownTypeIFactorMass
    exact Finset.sum_nonneg fun n hn => norm_nonneg _
  calc
    |c| * (4 * Real.log X) ^ smoothHeathBrownTypeILogFactorCount fs *
        (∏ i ∈ Finset.univ.erase selected,
          smoothHeathBrownTypeIFactorMass (z := z) (fs i) (ω i)) =
      (|c| * (4 * Real.log X) ^ smoothHeathBrownTypeILogFactorCount fs) *
        (∏ i ∈ Finset.univ.erase selected,
          smoothHeathBrownTypeIFactorMass (z := z) (fs i) (ω i)) := by ring
    _ ≤ ((2 : ℝ) ^ 10 * (4 * Real.log X)) *
        (∏ i ∈ Finset.univ.erase selected,
          smoothHeathBrownTypeIFactorMass (z := z) (fs i) (ω i)) := by
      apply mul_le_mul_of_nonneg_right _ hmassNonneg
      exact mul_le_mul hc hpower (by positivity) (by positivity)
    _ ≤ ((2 : ℝ) ^ 10 * (4 * Real.log X)) *
        (5 ^ 19 * Real.sqrt
          ((∏ i : Fin k, smoothHeathBrownFactorScale (fs i)) /
            smoothHeathBrownFactorScale (fs selected))) :=
      mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (by positivity) hLpos.le)
    _ = (2 : ℝ) ^ 10 * (4 * Real.log X) * 5 ^ 19 * Real.sqrt
        ((∏ i : Fin k, smoothHeathBrownFactorScale (fs i)) /
          smoothHeathBrownFactorScale (fs selected)) := by ring

#print axioms smoothHeathBrownTypeIOuterFactorMassProduct_with_source_scalars

end FractionalPrimes.Literature.DirichletAdapter

end
