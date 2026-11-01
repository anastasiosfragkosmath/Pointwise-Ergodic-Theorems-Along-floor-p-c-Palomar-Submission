module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

/-- Remove the coefficient at the prescribed top index `d`, leaving a
polynomial supported strictly below `d`. If `P` has smaller degree already,
the truncation is `P` itself; this case distinction is necessary because
`natDegree P` need not equal the source's degree bound `d`. -/
noncomputable def scalarWeyl_topMonomialTruncation (d : ℕ) (P : Polynomial ℝ) :
    Polynomial ℝ :=
  if P.natDegree = d then P.eraseLead else P

/-- The top-monomial truncation has degree at most `d-1`, preserves every
coefficient below `d`, and reconstructs `P` after adding back its degree-`d`
term. The statement includes the edge case `d=0`. -/
theorem scalarWeyl_topMonomialTruncation_spec
    (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ d) :
    let Plo := scalarWeyl_topMonomialTruncation d P
    Plo.natDegree ≤ d - 1 ∧
      (∀ j, j < d → P.coeff j = Plo.coeff j) ∧
      Plo.coeff d = 0 ∧
      P = Plo + Polynomial.C (P.coeff d) * Polynomial.X ^ d := by
  classical
  dsimp only
  by_cases hdeg : P.natDegree = d
  · have hPlo : scalarWeyl_topMonomialTruncation d P = P.eraseLead := by
      simp [scalarWeyl_topMonomialTruncation, hdeg]
    have hdegree :
        (scalarWeyl_topMonomialTruncation d P).natDegree ≤ d - 1 := by
      calc
        (scalarWeyl_topMonomialTruncation d P).natDegree =
            P.eraseLead.natDegree := by rw [hPlo]
        _ ≤ P.natDegree - 1 := Polynomial.eraseLead_natDegree_le P
        _ = d - 1 := by rw [hdeg]
    have hlow : ∀ j, j < d →
        P.coeff j = (scalarWeyl_topMonomialTruncation d P).coeff j := by
      intro j hj
      rw [hPlo]
      exact (Polynomial.eraseLead_coeff_of_ne j (by omega)).symm
    have htop : (scalarWeyl_topMonomialTruncation d P).coeff d = 0 := by
      rw [hPlo]
      simpa [hdeg] using (Polynomial.eraseLead_coeff_natDegree (f := P))
    have hlead : P.leadingCoeff = P.coeff d := by
      simp [Polynomial.leadingCoeff, hdeg]
    have hdecomp :
        P = scalarWeyl_topMonomialTruncation d P +
          Polynomial.C (P.coeff d) * Polynomial.X ^ d := by
      calc
        P = P.eraseLead + Polynomial.C P.leadingCoeff *
            Polynomial.X ^ P.natDegree :=
          (Polynomial.eraseLead_add_C_mul_X_pow P).symm
        _ = scalarWeyl_topMonomialTruncation d P +
            Polynomial.C (P.coeff d) * Polynomial.X ^ d := by
          rw [← hPlo, hdeg, hlead]
    exact ⟨hdegree, hlow, htop, hdecomp⟩
  · have hdeglt : P.natDegree < d := by omega
    have hPlo : scalarWeyl_topMonomialTruncation d P = P := by
      simp [scalarWeyl_topMonomialTruncation, hdeg]
    have htopCoeff : P.coeff d = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hdeglt
    have hdegree :
        (scalarWeyl_topMonomialTruncation d P).natDegree ≤ d - 1 := by
      rw [hPlo]
      omega
    have hlow : ∀ j, j < d →
        P.coeff j = (scalarWeyl_topMonomialTruncation d P).coeff j := by
      intro j hj
      rw [hPlo]
    have htop : (scalarWeyl_topMonomialTruncation d P).coeff d = 0 := by
      rw [hPlo]
      exact htopCoeff
    have hdecomp :
        P = scalarWeyl_topMonomialTruncation d P +
          Polynomial.C (P.coeff d) * Polynomial.X ^ d := by
      rw [hPlo, htopCoeff]
      simp
    exact ⟨hdegree, hlow, htop, hdecomp⟩

end FractionalPrimes.Literature.Polynomial
