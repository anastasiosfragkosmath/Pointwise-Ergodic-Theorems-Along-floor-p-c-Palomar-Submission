module
public import FractionalPrimes.Literature.Reciprocal.GlobalCharacterMobius
@[expose] public section

open Finset

namespace FractionalPrimes.Literature.Reciprocal

/-- Exact half-open real-cutoff interval identity for the global Möbius
character prefix, with the blueprint's `(floor u, floor v]` convention. -/
theorem globalMobiusCharacterInterval_eq_sub
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {u v : ℝ} (_hu : 0 ≤ u) (huv : u ≤ v) :
    (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
        globalMobiusCharacterCoefficient χ n) =
      globalMobiusCharacterSum χ v - globalMobiusCharacterSum χ u := by
  rw [globalMobiusCharacterSum, globalMobiusCharacterSum]
  have hfloor : Nat.floor u ≤ Nat.floor v := Nat.floor_mono huv
  have hunion : Finset.Icc 1 (Nat.floor v) =
      Finset.Icc 1 (Nat.floor u) ∪ Finset.Ioc (Nat.floor u) (Nat.floor v) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (Nat.floor u))
      (Finset.Ioc (Nat.floor u) (Nat.floor v)) := by
    apply Finset.disjoint_left.mpr
    intro n hn₁ hn₂
    simp only [Finset.mem_Icc] at hn₁
    simp only [Finset.mem_Ioc] at hn₂
    omega
  have hsum := congrArg (fun s : Finset ℕ =>
    ∑ n ∈ s, globalMobiusCharacterCoefficient χ n) hunion
  rw [Finset.sum_union hdisj] at hsum
  rw [hsum]
  abel

end FractionalPrimes.Literature.Reciprocal
