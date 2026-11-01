module

public import FractionalPrimes.Core
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.List.Defs

/-!
# Arithmetic progressions, maximal sums, and inhomogeneous total variation

This file implements blueprint item `lu:ap-tv`.  The finite variation is
inhomogeneous: it includes the supremum norm as well as the sum of consecutive
increments.  The infinite-set variation is the extended nonnegative supremum
over finite subsets.  This is distinct from the homogeneous `r`-variation
used for averaging operators elsewhere in the project.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open scoped ENNReal

noncomputable section

/-- The finite progression `{a + j d : 0 ≤ j < L}`.  Positivity of `d` is
stored in the predicate `isFiniteArithmeticProgression`; `L = 0` gives the
empty progression. -/
def arithmeticProgressionPoints (a : ℤ) (d : ℕ) (_hd : 0 < d) (L : ℕ) : Finset ℤ :=
  (Finset.range L).image (fun j : ℕ => a + (j : ℤ) * (d : ℤ))

@[simp] theorem arithmeticProgressionPoints_empty (a : ℤ) (d : ℕ) (hd : 0 < d) :
    arithmeticProgressionPoints a d hd 0 = ∅ := by
  simp [arithmeticProgressionPoints]

/-- A finite subset of the integers is an arithmetic progression with a
strictly positive natural step. -/
def isFiniteArithmeticProgression (P : Finset ℤ) : Prop :=
  ∃ a : ℤ, ∃ d : ℕ, ∃ hd : 0 < d, ∃ L : ℕ,
    arithmeticProgressionPoints a d hd L = P

/-- All arithmetic progressions contained in the finite set `I`.  In the
blueprint this family is used with a finite integer interval `I`. -/
noncomputable def arithmeticProgressionsWithin (I : Finset ℤ) : Finset (Finset ℤ) := by
  classical
  exact I.powerset.filter isFiniteArithmeticProgression

/-- A finite integer interval, represented by its first integer and its
number of terms.  Length zero represents the empty interval. -/
structure FiniteIntegerInterval where
  start : ℤ
  length : ℕ

/-- The points in a finite integer interval.  This is the step-one case of
`arithmeticProgressionPoints`. -/
def FiniteIntegerInterval.points (I : FiniteIntegerInterval) : Finset ℤ :=
  arithmeticProgressionPoints I.start 1 (by norm_num) I.length

@[simp] theorem FiniteIntegerInterval.points_empty (a : ℤ) :
    FiniteIntegerInterval.points ⟨a, 0⟩ = ∅ := by
  simp [FiniteIntegerInterval.points, arithmeticProgressionPoints]

theorem FiniteIntegerInterval.points_isFiniteArithmeticProgression
    (I : FiniteIntegerInterval) : isFiniteArithmeticProgression I.points := by
  exact ⟨I.start, 1, by norm_num, I.length, rfl⟩

/-- The whole carrier interval is itself one of the progressions in its
maximal-sum family. -/
theorem FiniteIntegerInterval.points_mem_arithmeticProgressionsWithin
    (I : FiniteIntegerInterval) :
    I.points ∈ arithmeticProgressionsWithin I.points := by
  classical
  rw [arithmeticProgressionsWithin, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.Subset.rfl, I.points_isFiniteArithmeticProgression⟩

theorem empty_mem_arithmeticProgressionsWithin (I : Finset ℤ) :
    ∅ ∈ arithmeticProgressionsWithin I := by
  classical
  rw [arithmeticProgressionsWithin, Finset.mem_filter]
  refine ⟨Finset.empty_mem_powerset I, ?_⟩
  exact ⟨0, 1, by norm_num, 0, by simp [arithmeticProgressionPoints]⟩

theorem arithmeticProgressionsWithin_nonempty (I : Finset ℤ) :
    (arithmeticProgressionsWithin I).Nonempty :=
  ⟨∅, empty_mem_arithmeticProgressionsWithin I⟩

/-- Extend a function on the interval by zero outside its domain.  Every
progression in `arithmeticProgressionsWithin I` is a subset of `I`, so the
extension does not alter any sum in the maximal definition. -/
def extendByZero (I : Finset ℤ) (f : {n : ℤ // n ∈ I} → ℂ) (n : ℤ) : ℂ :=
  if hn : n ∈ I then f ⟨n, hn⟩ else 0

theorem sum_extendByZero_eq_of_subset (I P : Finset ℤ)
    (f : {n : ℤ // n ∈ I} → ℂ) (hPI : P ⊆ I) :
    (∑ x ∈ P.attach, extendByZero I f x.1) =
      ∑ x ∈ P.attach, f ⟨x.1, hPI x.2⟩ := by
  apply Finset.sum_congr rfl
  intro x hx
  simp [extendByZero, hPI x.2]

/-- The maximum of the absolute progression sums over all arithmetic
progressions contained in `I`.  The empty progression is included, so the
finite family is nonempty and the maximum exists. -/
def progressionMaximalSum (I : FiniteIntegerInterval)
    (f : {n : ℤ // n ∈ I.points} → ℂ) : ℝ :=
  (arithmeticProgressionsWithin I.points).sup'
    (arithmeticProgressionsWithin_nonempty I.points)
    (fun P => ‖∑ n ∈ P, extendByZero I.points f n‖)

/-- The maximum of `‖g(nᵢ)‖` on a finite ordered list, represented by a fold
whose empty value is zero. -/
def listSupNorm (g : ℤ → ℂ) (ns : List ℤ) : ℝ :=
  (ns.map fun n => ‖g n‖).foldl max 0

/-- The sum of the increments between successive entries of a finite ordered
list. -/
def listAdjacentVariation (g : ℤ → ℂ) (ns : List ℤ) : ℝ :=
  (ns.consecutivePairs.map fun p => ‖g p.2 - g p.1‖).sum

/-- Inhomogeneous total variation on a finite ordered subset of `ℤ`: the
maximum pointwise norm plus the sum of the norms of consecutive increments.
The sorted list gives the unique increasing order; for the empty set both
terms are zero. -/
def finiteOrderedTotalVariation (P : Finset ℤ) (g : ℤ → ℂ) : ℝ :=
  listSupNorm g (P.sort (· ≤ ·)) + listAdjacentVariation g (P.sort (· ≤ ·))

@[simp] theorem finiteOrderedTotalVariation_empty (g : ℤ → ℂ) :
    finiteOrderedTotalVariation ∅ g = 0 := by
  simp [finiteOrderedTotalVariation, listSupNorm, listAdjacentVariation]

private theorem list_foldl_max_nonneg (l : List ℝ) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simpa using hb
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih
      exact le_trans hb (le_max_left b x)

private theorem list_sum_nonneg {l : List ℝ} (hl : ∀ x ∈ l, 0 ≤ x) :
    0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : 0 ≤ x := hl x (by simp)
      have hxs : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hl y (by simp [hy])
      simpa only [List.sum_cons] using add_nonneg hx (ih hxs)

theorem finiteOrderedTotalVariation_nonneg (P : Finset ℤ) (g : ℤ → ℂ) :
    0 ≤ finiteOrderedTotalVariation P g := by
  unfold finiteOrderedTotalVariation listSupNorm listAdjacentVariation
  apply add_nonneg
  · exact list_foldl_max_nonneg _ (le_rfl)
  · apply list_sum_nonneg
    intro p hp
    rcases List.mem_map.mp hp with ⟨pair, hpair, rfl⟩
    exact norm_nonneg _

/-- Total variation on an arbitrary ordered subset of `ℤ`, valued in
`[0,+∞]`: take the supremum of the finite inhomogeneous variations over all
finite subsets.  The use of `ℝ≥0∞` retains infinite values and its standard
multiplication convention includes `0 * ∞ = 0`. -/
def orderedTotalVariation (P : Set ℤ) (g : ℤ → ℂ) : ℝ≥0∞ :=
  ⨆ F : {F : Finset ℤ // ∀ n ∈ F, n ∈ P},
    ENNReal.ofReal (finiteOrderedTotalVariation F.1 g)

/-- The integer residue class `a + qℤ`. -/
def integerResidueClass (q a : ℕ) : Set ℤ :=
  {n | ∃ k : ℤ, n = (a : ℤ) + (q : ℤ) * k}

/-- Inhomogeneous residue-class total variation.  The hypothesis `0 < q`
matches the blueprint's modulus range `q ≥ 1`; `Finset.range q` enumerates
the residues `0, …, q-1`. -/
def residueClassTotalVariation (P : Set ℤ) (g : ℤ → ℂ) (q : ℕ)
    (_hq : 0 < q) : ℝ≥0∞ :=
  ∑ a ∈ Finset.range q,
    orderedTotalVariation (P ∩ integerResidueClass q a) g

/-- The positive-integer specialization of the residue-class inhomogeneous
variation.  Its finite restrictions include each residue class's supremum
norm term. -/
def positiveIntegerResidueTotalVariation (g : ℤ → ℂ) (q : ℕ) (hq : 0 < q) :
    ℝ≥0∞ :=
  residueClassTotalVariation {n : ℤ | 0 < n} g q hq

/-- The aggregate implementation of blueprint item `lu:ap-tv`.  Its fields
are exactly the finite progression, maximal sum, finite and infinite
inhomogeneous variations, and residue-class variation defined above. -/
structure ProgressionMaximalAndTV where
  progressionPoints : (a : ℤ) → (d : ℕ) → 0 < d → (L : ℕ) → Finset ℤ
  progressionFamily : Finset ℤ → Finset (Finset ℤ)
  intervalPoints : FiniteIntegerInterval → Finset ℤ
  maximalSum : (I : FiniteIntegerInterval) →
    ({n : ℤ // n ∈ intervalPoints I} → ℂ) → ℝ
  finiteVariation : Finset ℤ → (ℤ → ℂ) → ℝ
  infiniteVariation : Set ℤ → (ℤ → ℂ) → ℝ≥0∞
  residueVariation : (P : Set ℤ) → (g : ℤ → ℂ) → (q : ℕ) → 0 < q → ℝ≥0∞
  positiveIntegerResidueVariation : (g : ℤ → ℂ) → (q : ℕ) → 0 < q → ℝ≥0∞

/-- The forward-manifest declaration for the exact objects in `lu:ap-tv`. -/
def progressionMaximalAndTV : ProgressionMaximalAndTV where
  progressionPoints := fun a d hd L => arithmeticProgressionPoints a d hd L
  progressionFamily := arithmeticProgressionsWithin
  intervalPoints := FiniteIntegerInterval.points
  maximalSum := progressionMaximalSum
  finiteVariation := finiteOrderedTotalVariation
  infiniteVariation := orderedTotalVariation
  residueVariation := residueClassTotalVariation
  positiveIntegerResidueVariation := positiveIntegerResidueTotalVariation

#print progressionMaximalAndTV
#print axioms progressionMaximalAndTV
#print axioms progressionMaximalSum
#print axioms finiteOrderedTotalVariation
#print axioms orderedTotalVariation
#print axioms residueClassTotalVariation

end

end FractionalPrimes.Literature.Uniformity
