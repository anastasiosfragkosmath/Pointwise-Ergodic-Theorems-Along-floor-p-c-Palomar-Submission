module

public import FractionalPrimes.ArithmeticBasicsCore
public import Mathlib.Algebra.Polynomial.Taylor

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

/-- For a positive shift, the overlap of an integer interval with its translate
back by that shift is again an integer interval. On that overlap, the shifted
polynomial phase is exactly the Taylor finite difference. This packages the
interval and phase identities used in the scalar Weyl induction. -/
theorem scalarWeyl_shiftedIco_taylorPhase
    (N h : ℕ) (hh : h ∈ Finset.Ico 1 N)
    (lo hi : ℤ)
    (hJ : Finset.Ico lo hi ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    (P : Polynomial ℝ) :
    Finset.Ico lo hi ∩
        Finset.Ico (lo - (h : ℤ)) (hi - (h : ℤ)) =
      Finset.Ico lo (hi - (h : ℤ)) ∧
    (Finset.Ico lo hi).filter (fun n : ℤ =>
        n + (h : ℤ) ∈ Finset.Ico lo hi) =
      Finset.Ico lo (hi - (h : ℤ)) ∧
    Finset.Ico lo (hi - (h : ℤ)) ⊆ Finset.Icc (1 : ℤ) (N : ℤ) ∧
    (∀ n : ℤ,
      unitFrequencyPhase
          ((Polynomial.taylor (h : ℝ) P - P).eval (n : ℝ)) =
        unitFrequencyPhase
          (P.eval ((n : ℝ) + (h : ℝ)) - P.eval (n : ℝ))) := by
  classical
  have hhNonneg : (0 : ℤ) ≤ (h : ℤ) := by
    have hhlo : 1 ≤ h := (Finset.mem_Ico.mp hh).1
    exact_mod_cast (show 0 ≤ h by omega)
  have hintersection :
      Finset.Ico lo hi ∩
          Finset.Ico (lo - (h : ℤ)) (hi - (h : ℤ)) =
        Finset.Ico lo (hi - (h : ℤ)) := by
    ext n
    simp only [Finset.mem_inter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hnlo, _⟩, ⟨_, hshiftHi⟩⟩
      exact ⟨hnlo, hshiftHi⟩
    · rintro ⟨hnlo, hnhi⟩
      refine ⟨⟨hnlo, ?_⟩, ⟨?_, hnhi⟩⟩ <;> omega
  have hinterval :
      (Finset.Ico lo hi).filter (fun n : ℤ =>
          n + (h : ℤ) ∈ Finset.Ico lo hi) =
        Finset.Ico lo (hi - (h : ℤ)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hnlo, hnhi⟩, ⟨_, hshiftHi⟩⟩
      exact ⟨hnlo, by omega⟩
    · rintro ⟨hnlo, hnhi⟩
      refine ⟨⟨hnlo, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
  refine ⟨hintersection, hinterval, ?_, ?_⟩
  · rw [← hinterval]
    exact (Finset.filter_subset _ _).trans hJ
  · intro n
    apply congrArg unitFrequencyPhase
    simp only [Polynomial.eval_sub, Polynomial.taylor_eval]

end FractionalPrimes.Literature.Polynomial
