module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFullFrequencyResidueData
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWTaggedComponentAPI
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixMellinIndices
public import FractionalPrimes.Literature.Twisted.PrefixTwistRange
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open scoped BigOperators
namespace FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- Source short-prefix estimate in the exact integer/residue convention. -/
theorem mobiusSelectedPTWShortPrefix
    {X H m : ℕ} {a η : ℝ}
    (ha : (prefixTwistBeta : ℝ) < a) (hη : 0 < η)
    (hX : prefixTwistRangeThreshold a η ≤ (X : ℝ))
    (hHlo : (X : ℝ) ^ (5 / 8 + η) ≤ (H : ℝ))
    (hHX : H ≤ X)
    (hm : (m : ℝ) ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-2 * a))
    (ν : MobiusDyadicLabel (X : ℝ))
    (hν : ν ∈ mobiusDyadicLabels (X : ℝ) (dyadicMobiusCutoff (X : ℝ)))
    (T : ℝ) (q b : ℕ) :
    ‖residuePrefixSum X m q b
      (fun n => complexPositiveIntegerZeroExtension (selectedMobiusPTWRawDyadicComponent ν) n *
        archimedeanTwist T (n : ℝ))‖ ≤
      (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
  classical
  let u : ℕ → ℂ := fun n =>
    if Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ) then 1 else 0
  have hu : ∀ n, ‖u n‖ ≤ 1 := by
    intro n
    dsimp [u]
    split_ifs <;> simp
  have hsmall := (prefixAndTwistSeparation ha hη hX hHlo
    (by exact_mod_cast hHX)).2.2.1 ν hν T 1 0 u hu
      (X : ℝ) (m : ℝ) (by positivity) hm
  have hEq : residuePrefixSum X m q b
      (fun n => complexPositiveIntegerZeroExtension (selectedMobiusPTWRawDyadicComponent ν) n *
        archimedeanTwist T (n : ℝ)) =
      ∑ n ∈ selectedPositiveInterval (X : ℝ) (m : ℝ),
        (mobiusDyadicComponent (dyadicMobiusCutoff (X : ℝ)) ν n : ℂ) *
          selectedComponentModulatedWeight T 1 0 u n := by
    rw [residuePrefixSum_eq_mellinWindowSum, mellinWindowAverageIndices,
      mellinIntervalIndices_eq_selectedPositiveInterval]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos := ((selectedPositiveInterval_mem_iff (X : ℝ) (m : ℝ)
      (by positivity) n).mp hn).1
    rw [complexPositiveIntegerZeroExtension_natCast _ ⟨n, hnpos⟩]
    simp [selectedMobiusPTWRawDyadicComponent, selectedComponentModulatedWeight, u, Nat.mod_one]
  rw [hEq]
  exact hsmall

#print axioms mobiusSelectedPTWShortPrefix
/-- Source short-prefix estimate in the exact integer/residue convention. -/
theorem vonMangoldtSelectedPTWShortPrefix
    {X H m : ℕ} {a η : ℝ}
    (ha : (prefixTwistBeta : ℝ) < a) (hη : 0 < η)
    (hX : prefixTwistRangeThreshold a η ≤ (X : ℝ))
    (hHlo : (X : ℝ) ^ (5 / 8 + η) ≤ (H : ℝ))
    (hHX : H ≤ X)
    (hm : (m : ℝ) ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-2 * a))
    (ν : VonMangoldtDyadicLabel (X : ℝ))
    (hν : ν ∈ vonMangoldtDyadicLabels (X : ℝ) (dyadicMobiusCutoff (X : ℝ)))
    (T : ℝ) (q b : ℕ) :
    ‖residuePrefixSum X m q b
      (fun n => complexPositiveIntegerZeroExtension (selectedVonMangoldtPTWRawDyadicComponent ν) n *
        archimedeanTwist T (n : ℝ))‖ ≤
      (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
  classical
  let u : ℕ → ℂ := fun n =>
    if Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ) then 1 else 0
  have hu : ∀ n, ‖u n‖ ≤ 1 := by
    intro n
    dsimp [u]
    split_ifs <;> simp
  have hsmall := (prefixAndTwistSeparation ha hη hX hHlo
    (by exact_mod_cast hHX)).2.2.2.1 ν hν T 1 0 u hu
      (X : ℝ) (m : ℝ) (by positivity) hm
  have hEq : residuePrefixSum X m q b
      (fun n => complexPositiveIntegerZeroExtension (selectedVonMangoldtPTWRawDyadicComponent ν) n *
        archimedeanTwist T (n : ℝ)) =
      ∑ n ∈ selectedPositiveInterval (X : ℝ) (m : ℝ),
        (vonMangoldtDyadicComponent (dyadicMobiusCutoff (X : ℝ)) ν n : ℂ) *
          selectedComponentModulatedWeight T 1 0 u n := by
    rw [residuePrefixSum_eq_mellinWindowSum, mellinWindowAverageIndices,
      mellinIntervalIndices_eq_selectedPositiveInterval]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos := ((selectedPositiveInterval_mem_iff (X : ℝ) (m : ℝ)
      (by positivity) n).mp hn).1
    rw [complexPositiveIntegerZeroExtension_natCast _ ⟨n, hnpos⟩]
    simp [selectedVonMangoldtPTWRawDyadicComponent, selectedComponentModulatedWeight, u, Nat.mod_one]
  rw [hEq]
  exact hsmall

#print axioms vonMangoldtSelectedPTWShortPrefix
end FractionalPrimes.Literature.DirichletMean
