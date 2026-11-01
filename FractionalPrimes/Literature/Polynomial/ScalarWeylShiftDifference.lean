module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

/-- A finite difference of a degree-`d` polynomial has degree at most
`d-1`, and its coefficient at `d-1` is the source's `d α_d h`. This is the
polynomial input needed to apply the degree-`d-1` Weyl induction hypothesis
to each shift. -/
theorem scalarWeyl_shiftDifference_spec
    (d : ℕ) (hd : 2 ≤ d) (P : Polynomial ℝ)
    (hP : P.natDegree ≤ d) (h : ℤ) :
    let ΔP := Polynomial.taylor (h : ℝ) P - P
    ΔP.natDegree ≤ d - 1 ∧
      ΔP.coeff (d - 1) = (d : ℝ) * P.coeff d * (h : ℝ) := by
  let T : Polynomial ℝ := Polynomial.taylor (h : ℝ) P
  let ΔP : Polynomial ℝ := T - P
  have hTdegree : T.natDegree ≤ d := by
    simpa [T] using hP
  have hTtop : T.coeff d = P.coeff d := by
    by_cases hdeg : P.natDegree = d
    · calc
        T.coeff d = T.coeff P.natDegree := by rw [← hdeg]
        _ = P.leadingCoeff := by
          simpa [T] using Polynomial.coeff_taylor_natDegree (h : ℝ) P
        _ = P.coeff d := by simp [Polynomial.leadingCoeff, hdeg]
    · have hlt : P.natDegree < d := by omega
      have hTlt : T.natDegree < d := by
        simpa [T] using hlt
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hTlt,
        Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
  have hΔdegree : ΔP.natDegree ≤ d := by
    dsimp [ΔP]
    simpa only [max_self] using
      Polynomial.natDegree_sub_le_of_le hTdegree hP
  have hΔtop : ΔP.coeff d = 0 := by
    dsimp [ΔP]
    rw [Polynomial.coeff_sub, hTtop]
    ring
  have hΔdegree' : ΔP.natDegree ≤ d - 1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hdn
    by_cases hnd : n = d
    · simpa [hnd] using hΔtop
    · have hdn' : d < n := by omega
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hΔdegree.trans_lt hdn')
  let H : Polynomial ℝ := Polynomial.hasseDeriv (d - 1) P
  have hHdegree : H.natDegree ≤ 1 := by
    have hder := Polynomial.natDegree_hasseDeriv_le P (d - 1)
    have hsub : P.natDegree - (d - 1) ≤ d - (d - 1) :=
      Nat.sub_le_sub_right hP (d - 1)
    dsimp [H]
    omega
  have hHlinear : H = Polynomial.C (H.coeff 1) * Polynomial.X +
      Polynomial.C (H.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hHdegree
  have hHzero : H.coeff 0 = P.coeff (d - 1) := by
    dsimp [H]
    rw [Polynomial.hasseDeriv_coeff]
    simp [Nat.choose_self]
  have hHone : H.coeff 1 = (d : ℝ) * P.coeff d := by
    dsimp [H]
    rw [Polynomial.hasseDeriv_coeff]
    have hindex : 1 + (d - 1) = d := by omega
    rw [hindex]
    have hchoose : Nat.choose d (d - 1) = d := by
      calc
        Nat.choose d (d - 1) =
            Nat.choose ((d - 1) + 1) (d - 1) := by congr 1 <;> omega
        _ = (d - 1) + 1 := Nat.choose_succ_self_right _
        _ = d := by omega
    rw [hchoose]
  have hHeval : H.eval (h : ℝ) = H.coeff 1 * (h : ℝ) + H.coeff 0 := by
    calc
      H.eval (h : ℝ) =
          (Polynomial.C (H.coeff 1) * Polynomial.X +
            Polynomial.C (H.coeff 0)).eval (h : ℝ) :=
        congrArg (fun Q : Polynomial ℝ => Q.eval (h : ℝ)) hHlinear
      _ = H.coeff 1 * (h : ℝ) + H.coeff 0 := by simp
  have hTlow : T.coeff (d - 1) =
      (d : ℝ) * P.coeff d * (h : ℝ) + P.coeff (d - 1) := by
    calc
      T.coeff (d - 1) = H.eval (h : ℝ) := by
        simpa [T, H] using
          Polynomial.taylor_coeff (h : ℝ) P (d - 1)
      _ = H.coeff 1 * (h : ℝ) + H.coeff 0 := hHeval
      _ = (d : ℝ) * P.coeff d * (h : ℝ) + P.coeff (d - 1) := by
        rw [hHone, hHzero]
  have hΔlow : ΔP.coeff (d - 1) =
      (d : ℝ) * P.coeff d * (h : ℝ) := by
    dsimp [ΔP]
    rw [Polynomial.coeff_sub, hTlow]
    ring
  constructor
  · simpa only [T, ΔP] using hΔdegree'
  · simpa only [T, ΔP, Polynomial.coeff_sub] using hΔlow

end FractionalPrimes.Literature.Polynomial
