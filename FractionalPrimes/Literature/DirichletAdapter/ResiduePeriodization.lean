module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Data.Int.ModEq
public import Mathlib.Topology.ContinuousMap.CompactlySupported

@[expose] public section

/-!
# Residue-lattice periodization

This file records the exact integer reindexing at the lattice point `x = 0` for the
periodization used in the high-order residue quadrature argument.  It is a discrete identity;
the Fourier estimates and the quadrature bound are handled separately.
-/

open scoped CompactlySupported

/-- The integers in the residue class `b` modulo `q`. -/
abbrev ResidueLattice (q b : ℤ) := {n : ℤ // n ≡ b [ZMOD q]}

/-- Reindex the integer parameter in `b + q*m` by the corresponding residue class. -/
def residueLatticeEquiv (q b : ℤ) (hq : 1 ≤ q) : ℤ ≃ ResidueLattice q b where
  toFun m := ⟨b + q * m, by
    rw [Int.modEq_iff_dvd]
    refine ⟨-m, ?_⟩
    ring⟩
  invFun n := (n.1 - b) / q
  left_inv m := by
    dsimp
    rw [show b + q * m - b = q * m by ring]
    exact Int.mul_ediv_cancel_left _ (by omega)
  right_inv n := by
    apply Subtype.ext
    dsimp
    have hdiv : q ∣ b - n.1 := Int.modEq_iff_dvd.mp n.2
    have hdiv' : q ∣ n.1 - b := by
      simpa [sub_eq_add_neg] using (Int.dvd_neg.mpr hdiv)
    calc
      b + q * ((n.1 - b) / q) = b + ((n.1 - b) / q) * q := by rw [mul_comm]
      _ = b + (n.1 - b) := by rw [Int.ediv_mul_cancel hdiv']
      _ = n.1 := by ring

/-- The residue-lattice periodization of a compactly supported continuous function. -/
noncomputable def residueLatticePeriodization (F : C_c(ℝ, ℂ)) (q b : ℤ) (x : ℝ) : ℂ :=
  ∑' m : ℤ, F ((b : ℝ) + (q : ℝ) * ((m : ℝ) + x))

/-- At `x = 0`, periodization is exactly the sum over the integers in the residue class.

No analytic estimate or Fourier normalization is used in this identity. -/
theorem residueLatticePeriodization_zero (F : C_c(ℝ, ℂ)) (q b : ℤ) (hq : 1 ≤ q) :
    residueLatticePeriodization F q b 0 =
      ∑' n : ResidueLattice q b, F (n.1 : ℝ) := by
  unfold residueLatticePeriodization
  rw [← (residueLatticeEquiv q b hq).tsum_eq (fun n : ResidueLattice q b => F (n.1 : ℝ))]
  congr 1
  funext m
  simp [residueLatticeEquiv]

end
