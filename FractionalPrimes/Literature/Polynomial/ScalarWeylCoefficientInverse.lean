module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylInductionDensity
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

/-- Invert the affine substitution `n = c + r*k` on every nonconstant
coefficient below degree `d`. The inserted factor `r^(d-1)` makes each
coefficient multiplying the transformed coefficient an integer. -/
theorem scalarWeyl_affineCoefficient_inverse
    {d j : ℕ} (hd : 2 ≤ d) (hj : 1 ≤ j) (hjd : j < d)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d - 1)
    (c : ℤ) (r : ℕ) (hr : 0 < r) :
    (r : ℝ) ^ (d - 1) * P.coeff j =
      ∑ i ∈ Finset.Icc j (d - 1),
        (Nat.choose i j : ℝ) * (r : ℝ) ^ (d - 1 - i) *
          (-(c : ℝ)) ^ (i - j) *
          (P.comp (Polynomial.C (r : ℝ) * Polynomial.X +
            Polynomial.C (c : ℝ))).coeff i := by
  let ρ : ℝ := (r : ℝ)
  let ξ : ℝ := (c : ℝ)
  let Q : Polynomial ℝ :=
    P.comp (Polynomial.C ρ * Polynomial.X + Polynomial.C ξ)
  let L : Polynomial ℝ := Polynomial.C ρ⁻¹ *
    (Polynomial.X - Polynomial.C ξ)
  change ρ ^ (d - 1) * P.coeff j =
    ∑ i ∈ Finset.Icc j (d - 1),
      (Nat.choose i j : ℝ) * ρ ^ (d - 1 - i) *
        (-ξ) ^ (i - j) * Q.coeff i
  have hρ : ρ ≠ 0 := by
    dsimp [ρ]
    exact_mod_cast (Nat.ne_of_gt hr)
  have hInv : P = Q.comp L := by
    dsimp [Q, L]
    simp only [Polynomial.comp_assoc, Polynomial.add_comp,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hρ,
      Polynomial.C_1, one_mul, sub_add_cancel, Polynomial.comp_X]
  have hQdeg : Q.natDegree ≤ d - 1 := by
    dsimp [Q, ρ, ξ]
    exact scalarWeyl_affineSubstitution_degree P hP c r
  have hQlt : Q.natDegree < d := by omega
  have hQsum :
      Q.sum (fun i a => Polynomial.C a * L ^ i) =
        ∑ i ∈ Finset.range d, Polynomial.C (Q.coeff i) * L ^ i := by
    exact Polynomial.sum_over_range' Q (by intro i; simp) d hQlt
  have hcoeffRange :
      P.coeff j =
        ∑ i ∈ Finset.range d,
          (Polynomial.C (Q.coeff i) * L ^ i).coeff j := by
    calc
      P.coeff j = (Q.comp L).coeff j := by rw [hInv]
      _ = (Q.sum (fun i a => Polynomial.C a * L ^ i)).coeff j := by
        rw [Polynomial.comp_eq_sum_left]
      _ = (∑ i ∈ Finset.range d, Polynomial.C (Q.coeff i) * L ^ i).coeff j := by
        rw [hQsum]
      _ = ∑ i ∈ Finset.range d,
          (Polynomial.C (Q.coeff i) * L ^ i).coeff j := by
        rw [Polynomial.finsetSum_coeff]
  have hL :
      L = Polynomial.C ρ⁻¹ *
        (Polynomial.X + Polynomial.C (-ξ)) := by
    dsimp [L]
    simp [sub_eq_add_neg]
  have hterm (i : ℕ) :
      (Polynomial.C (Q.coeff i) * L ^ i).coeff j =
        Q.coeff i * ρ⁻¹ ^ i * (-ξ) ^ (i - j) * (i.choose j : ℝ) := by
    rw [hL, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
    ring
  have hcoeffRange' :
      P.coeff j =
        ∑ i ∈ Finset.range d,
          Q.coeff i * ρ⁻¹ ^ i * (-ξ) ^ (i - j) * (i.choose j : ℝ) := by
    calc
      P.coeff j =
          ∑ i ∈ Finset.range d,
            (Polynomial.C (Q.coeff i) * L ^ i).coeff j := hcoeffRange
      _ = ∑ i ∈ Finset.range d,
            Q.coeff i * ρ⁻¹ ^ i * (-ξ) ^ (i - j) * (i.choose j : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i
  have hpow (i : ℕ) (hi : i < d) :
      ρ ^ (d - 1) * ρ⁻¹ ^ i = ρ ^ (d - 1 - i) := by
    have hi' : i ≤ d - 1 := by omega
    rw [inv_pow, ← pow_sub₀ ρ hρ hi']
  have hscaledRange :
      ρ ^ (d - 1) * P.coeff j =
        ∑ i ∈ Finset.range d,
          (i.choose j : ℝ) * ρ ^ (d - 1 - i) *
            (-ξ) ^ (i - j) * Q.coeff i := by
    calc
      ρ ^ (d - 1) * P.coeff j =
          ρ ^ (d - 1) *
            (∑ i ∈ Finset.range d,
              Q.coeff i * ρ⁻¹ ^ i * (-ξ) ^ (i - j) *
                (i.choose j : ℝ)) := by rw [hcoeffRange']
      _ = ∑ i ∈ Finset.range d,
            ρ ^ (d - 1) *
              (Q.coeff i * ρ⁻¹ ^ i * (-ξ) ^ (i - j) *
                (i.choose j : ℝ)) := by rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range d,
            (i.choose j : ℝ) * ρ ^ (d - 1 - i) *
              (-ξ) ^ (i - j) * Q.coeff i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < d := Finset.mem_range.mp hi
        calc
          ρ ^ (d - 1) *
              (Q.coeff i * ρ⁻¹ ^ i * (-ξ) ^ (i - j) *
                (i.choose j : ℝ)) =
              (i.choose j : ℝ) *
                (ρ ^ (d - 1) * ρ⁻¹ ^ i) *
                (-ξ) ^ (i - j) * Q.coeff i := by ring
          _ = (i.choose j : ℝ) * ρ ^ (d - 1 - i) *
                (-ξ) ^ (i - j) * Q.coeff i := by rw [hpow i hi']
  have hIccSubset : Finset.Icc j (d - 1) ⊆ Finset.range d := by
    intro i hi
    rcases Finset.mem_Icc.mp hi with ⟨hji, hid⟩
    exact Finset.mem_range.mpr (by omega)
  have hrestrict :
      (∑ i ∈ Finset.Icc j (d - 1),
        (i.choose j : ℝ) * ρ ^ (d - 1 - i) *
          (-ξ) ^ (i - j) * Q.coeff i) =
      ∑ i ∈ Finset.range d,
        (i.choose j : ℝ) * ρ ^ (d - 1 - i) *
          (-ξ) ^ (i - j) * Q.coeff i := by
    apply Finset.sum_subset hIccSubset
    intro i hi hnot
    have hid : i ≤ d - 1 := by
      have hi' : i < d := Finset.mem_range.mp hi
      omega
    have hij : i < j := by
      by_contra hnotlt
      have hji : j ≤ i := Nat.le_of_not_gt hnotlt
      exact hnot (Finset.mem_Icc.mpr ⟨hji, hid⟩)
    rw [Nat.choose_eq_zero_of_lt hij]
    simp
  calc
    ρ ^ (d - 1) * P.coeff j =
        ∑ i ∈ Finset.range d,
          (i.choose j : ℝ) * ρ ^ (d - 1 - i) *
            (-ξ) ^ (i - j) * Q.coeff i := hscaledRange
    _ = ∑ i ∈ Finset.Icc j (d - 1),
          (i.choose j : ℝ) * ρ ^ (d - 1 - i) *
            (-ξ) ^ (i - j) * Q.coeff i := hrestrict.symm

end FractionalPrimes.Literature.Polynomial
