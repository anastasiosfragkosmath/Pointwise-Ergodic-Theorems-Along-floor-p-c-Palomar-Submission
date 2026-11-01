module

public import FractionalPrimes.Literature.Hyperbola.GeometricData
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

/-- Finite Dirichlet approximation with a reduced integer numerator and
positive integer denominator. The numerator may have either sign or be zero. -/
theorem finiteDirichletApproximation (s : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ a q : ℤ,
      Nat.Coprime a.natAbs q.natAbs ∧
      1 ≤ q ∧ q ≤ (Q : ℤ) ∧
      |s - (a : ℝ) / (q : ℝ)| < 1 / ((Q : ℝ) * (q : ℝ)) := by
  obtain ⟨p, hp, hpden⟩ := Real.exists_rat_abs_sub_le_and_den_le s hQ
  have hdenpos : 0 < (p.den : ℝ) := by exact_mod_cast p.den_pos
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hdenlt : (Q : ℝ) * (p.den : ℝ) <
      ((Q + 1 : ℕ) : ℝ) * (p.den : ℝ) := by
    have hQlt : (Q : ℝ) < ((Q + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self Q
    exact mul_lt_mul_of_pos_right hQlt hdenpos
  have hstrict :
      1 / (((Q + 1 : ℕ) : ℝ) * (p.den : ℝ)) <
        1 / ((Q : ℝ) * (p.den : ℝ)) := by
    exact one_div_lt_one_div_of_lt (mul_pos hQpos hdenpos) hdenlt
  have hp' : |s - (p.num : ℝ) / (p.den : ℝ)| ≤
      1 / (((Q + 1 : ℕ) : ℝ) * (p.den : ℝ)) := by
    simpa [Rat.cast_def] using hp
  refine ⟨p.num, (p.den : ℤ), ?_, ?_, ?_, ?_⟩
  · simpa using p.reduced
  · exact_mod_cast p.den_pos
  · exact_mod_cast hpden
  · calc
      |s - (p.num : ℝ) / (p.den : ℝ)| ≤
          1 / (((Q + 1 : ℕ) : ℝ) * (p.den : ℝ)) := hp'
      _ < 1 / ((Q : ℝ) * (p.den : ℝ)) := hstrict

end FractionalPrimes.Literature.Hyperbola
