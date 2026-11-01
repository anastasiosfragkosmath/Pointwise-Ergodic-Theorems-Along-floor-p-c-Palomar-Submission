module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownDPComponentAccumulation
public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Polynomial
noncomputable section

/-- The natural representative of the source's arbitrary integer residue. -/
def dpResidueRepresentative (q : ℕ) (a : ℤ) : ℕ :=
  (a % (q : ℤ)).toNat

theorem smoothHeathBrownComponentOuterCutoffCoefficient_residueRepresentative
    {q : ℕ} (hq : 0 < q) (X : ℝ) (a : ℤ) (g : ℕ → ℝ) (n : ℕ) :
    smoothHeathBrownComponentOuterCutoffCoefficient X q a g n =
      smoothHeathBrownComponentOuterCutoffCoefficient X q
        (dpResidueRepresentative q a : ℤ) g n := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hmod : 0 ≤ a % (q : ℤ) := Int.emod_nonneg a (by omega)
  unfold smoothHeathBrownComponentOuterCutoffCoefficient dpResidueRepresentative
  simp only [Int.toNat_of_nonneg hmod, Int.ModEq]
  by_cases h : (n : ℤ) % (q : ℤ) = a % (q : ℤ) <;> simp [h]

theorem smoothHeathBrownComponentOuterCutoffMellinPolynomial_residueRepresentative
    {q : ℕ} (hq : 0 < q) (X : ℝ) (a : ℤ) (g : ℕ → ℝ) (t : ℝ) :
    smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a g t =
      smoothHeathBrownComponentOuterCutoffMellinPolynomial X q
        (dpResidueRepresentative q a : ℤ) g t := by
  unfold smoothHeathBrownComponentOuterCutoffMellinPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [smoothHeathBrownComponentOuterCutoffCoefficient_residueRepresentative hq]

theorem dirichletMeanEnvelopeOfA_X_residueRepresentative
    {q : ℕ} (hq : 0 < q) (X T0 W : ℝ) (a : ℤ) (g : ℕ → ℝ) :
    dirichletMeanEnvelopeOfA_X
      (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a g) T0 W =
      dirichletMeanEnvelopeOfA_X
        (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q
          (dpResidueRepresentative q a : ℤ) g) T0 W := by
  have hfun :
      smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a g =
        smoothHeathBrownComponentOuterCutoffMellinPolynomial X q
          (dpResidueRepresentative q a : ℤ) g := by
    funext t
    exact smoothHeathBrownComponentOuterCutoffMellinPolynomial_residueRepresentative
      hq X a g t
  rw [hfun]

#print axioms smoothHeathBrownComponentOuterCutoffCoefficient_residueRepresentative
#print axioms smoothHeathBrownComponentOuterCutoffMellinPolynomial_residueRepresentative
#print axioms dirichletMeanEnvelopeOfA_X_residueRepresentative
end
end FractionalPrimes.Literature.DirichletAdapter
