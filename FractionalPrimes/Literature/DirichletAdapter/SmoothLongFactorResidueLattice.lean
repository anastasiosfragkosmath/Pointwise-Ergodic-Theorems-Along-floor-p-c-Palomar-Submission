module

public import FractionalPrimes.Literature.DirichletAdapter.HighOrderResidueQuadrature
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorFiniteReindex
import Mathlib.Tactic

/-! Exact conversion between natural-number progression sums from the
long-factor decomposition and the integer residue-lattice sums used by the
generic quadrature theorem. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open scoped CompactlySupported

/-- The nonnegative points of an integer residue lattice are in bijection
with natural numbers in the same integer congruence class. -/
def nonnegResidueLatticeEquiv (q b : ℤ) :
    {x : ResidueLattice q b // 0 ≤ x.1} ≃
      {n : ℕ // (n : ℤ) ≡ b [ZMOD q]} where
  toFun x := ⟨x.1.1.toNat, by
    have hcast : ((x.1.1.toNat : ℤ)) = x.1.1 :=
      Int.toNat_of_nonneg x.2
    change ((x.1.1.toNat : ℤ)) ≡ b [ZMOD q]
    rw [hcast]
    exact x.1.2⟩
  invFun n := ⟨⟨n.1, n.2⟩, by positivity⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change (x.1.1.toNat : ℤ) = x.1.1
    exact Int.toNat_of_nonneg x.2
  right_inv n := by
    apply Subtype.ext
    simp

/-- A compactly supported profile that vanishes on the negative half-line has
the same sum over an integer residue lattice as over its natural-number
points. -/
theorem residueLattice_tsum_eq_natCastClass_tsum
    (F : C_c(ℝ, ℂ)) (q b : ℤ)
    (hF : ∀ x : ℝ, x < 0 → F x = 0) :
    (∑' x : ResidueLattice q b, F (x.1 : ℝ)) =
      ∑' n : {n : ℕ // (n : ℤ) ≡ b [ZMOD q]}, F (n.1 : ℝ) := by
  classical
  let P : Set (ResidueLattice q b) := {x | 0 ≤ x.1}
  have hpoint (x : ResidueLattice q b) :
      P.indicator (fun y : ResidueLattice q b => F (y.1 : ℝ)) x =
        F (x.1 : ℝ) := by
    by_cases hx : x ∈ P
    · simp [hx]
    · have hxnonneg : ¬ 0 ≤ x.1 := by simpa [P] using hx
      have hxneg : x.1 < 0 := lt_of_not_ge hxnonneg
      have hreal : (x.1 : ℝ) < 0 := by exact_mod_cast hxneg
      simp [hx, hF (x.1 : ℝ) hreal]
  have hfun (x : P) :
      F (x.1.1 : ℝ) =
        F (((nonnegResidueLatticeEquiv q b x).1 : ℕ) : ℝ) := by
    congr 1
    have hcast :
        (((nonnegResidueLatticeEquiv q b x).1 : ℕ) : ℤ) = x.1.1 :=
      Int.toNat_of_nonneg x.2
    exact_mod_cast hcast.symm
  calc
    (∑' x : ResidueLattice q b, F (x.1 : ℝ)) =
        ∑' x : ResidueLattice q b,
          P.indicator (fun y : ResidueLattice q b => F (y.1 : ℝ)) x := by
      apply tsum_congr
      intro x
      exact (hpoint x).symm
    _ = ∑' x : P, F (x.1.1 : ℝ) := by
      exact (tsum_subtype (s := P)
        (f := fun y : ResidueLattice q b => F (y.1 : ℝ))).symm
    _ = ∑' x : P,
          F (((nonnegResidueLatticeEquiv q b x).1 : ℕ) : ℝ) := by
      apply tsum_congr
      intro x
      exact hfun x
    _ = ∑' n : {n : ℕ // (n : ℤ) ≡ b [ZMOD q]}, F (n.1 : ℝ) := by
      exact (nonnegResidueLatticeEquiv q b).tsum_eq
        (fun n => F (n.1 : ℝ))

#print axioms residueLattice_tsum_eq_natCastClass_tsum

/-- The natural-number solutions of the fixed-factor congruence give exactly
the integer residue-lattice sum at the reduced modulus. -/
theorem smoothHeathBrown_fixedProduct_tsum_reindex_to_residueLattice
    (F : C_c(ℝ, ℂ)) (m q a n₀ : ℕ) (hq : 0 < q)
    (hsol : m * n₀ ≡ a [MOD q])
    (hF : ∀ x : ℝ, x < 0 → F x = 0) :
    1 ≤ q / Nat.gcd m q ∧
      q / Nat.gcd m q ≤ q ∧
        (∑' n : {n : ℕ // m * n ≡ a [MOD q]}, F (n.1 : ℝ)) =
          ∑' n : ResidueLattice
            ((q / Nat.gcd m q : ℕ) : ℤ) (n₀ : ℤ), F (n.1 : ℝ) := by
  classical
  let q' : ℕ := q / Nat.gcd m q
  have hq'pos : 0 < q' := by
    dsimp [q']
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq (Nat.gcd_dvd_right m q)
    · exact Nat.gcd_pos_of_pos_right m hq
  have hq' : 1 ≤ q' := by omega
  let A := {n : ℕ // m * n ≡ a [MOD q]}
  let B := {n : ℕ // n ≡ n₀ [MOD q']}
  let C := {n : ℕ // (n : ℤ) ≡ (n₀ : ℤ) [ZMOD (q' : ℤ)]}
  let eAB : A ≃ B := {
    toFun := fun n => ⟨n.1,
      (mul_congruence_iff_reduced_residue m q a n₀ hq hsol n.1).mp n.2⟩
    invFun := fun n => ⟨n.1,
      (mul_congruence_iff_reduced_residue m q a n₀ hq hsol n.1).mpr n.2⟩
    left_inv := fun n => by apply Subtype.ext; rfl
    right_inv := fun n => by apply Subtype.ext; rfl }
  let eBC : B ≃ C := {
    toFun := fun n => ⟨n.1, (Int.natCast_modEq_iff).2 n.2⟩
    invFun := fun n => ⟨n.1, (Int.natCast_modEq_iff).1 n.2⟩
    left_inv := fun n => by apply Subtype.ext; rfl
    right_inv := fun n => by apply Subtype.ext; rfl }
  refine ⟨hq', mul_congruence_reduced_modulus_le m q, ?_⟩
  calc
    (∑' n : A, F (n.1 : ℝ)) =
        ∑' n : B, F (n.1 : ℝ) := eAB.tsum_eq (fun n => F (n.1 : ℝ))
    _ = ∑' n : C, F (n.1 : ℝ) := eBC.tsum_eq (fun n => F (n.1 : ℝ))
    _ = ∑' n : ResidueLattice (q' : ℤ) (n₀ : ℤ), F (n.1 : ℝ) := by
      symm
      exact residueLattice_tsum_eq_natCastClass_tsum F (q' : ℤ) (n₀ : ℤ) hF

#print axioms smoothHeathBrown_fixedProduct_tsum_reindex_to_residueLattice

end FractionalPrimes.Literature.DirichletAdapter

end
