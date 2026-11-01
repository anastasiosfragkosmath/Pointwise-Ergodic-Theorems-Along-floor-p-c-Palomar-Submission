module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalAndTV
public import Mathlib.Algebra.Order.GroupWithZero.Finset

/-!
# Absolute homogeneity of the finite progression maximal sum

This file proves the absolute-homogeneity clause of `lu:maximal-basic` for
the exact finite-integer-interval maximal sum defined in
`ProgressionMaximalAndTV.lean`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

noncomputable section

/-- The progression maximal sum is absolutely homogeneous in its complex
input function.  The interval domain and progression family are unchanged. -/
theorem progressionMaximalSum_smul (I : FiniteIntegerInterval) (c : ℂ)
    (f : {n : ℤ // n ∈ I.points} → ℂ) :
    progressionMaximalSum I (fun n => c * f n) =
      ‖c‖ * progressionMaximalSum I f := by
  let F := arithmeticProgressionsWithin I.points
  let H := arithmeticProgressionsWithin_nonempty I.points
  let base (P : Finset ℤ) := ‖∑ n ∈ P, extendByZero I.points f n‖
  let scaled (P : Finset ℤ) :=
    ‖∑ n ∈ P, extendByZero I.points (fun x => c * f x) n‖
  have hsum (P : Finset ℤ) :
      (∑ n ∈ P, extendByZero I.points (fun x => c * f x) n) =
        c * (∑ n ∈ P, extendByZero I.points f n) := by
    have hext (n : ℤ) :
        extendByZero I.points (fun x => c * f x) n =
          c * extendByZero I.points f n := by
      by_cases hn : n ∈ I.points <;> simp [extendByZero, hn]
    simp_rw [hext]
    rw [Finset.mul_sum]
  have hpoint (P : Finset ℤ) : scaled P = ‖c‖ * base P := by
    dsimp [scaled, base]
    rw [hsum, norm_mul]
  change F.sup' H scaled = ‖c‖ * F.sup' H base
  calc
    F.sup' H scaled = F.sup' H (fun P => ‖c‖ * base P) := by
      apply Finset.sup'_congr H rfl
      intro P hP
      exact hpoint P
    _ = ‖c‖ * F.sup' H base := by
      symm
      exact Finset.mul₀_sup' (norm_nonneg c) base F H

end

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.progressionMaximalSum_smul
