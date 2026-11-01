module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylLongBranchCoefficientPackage
public import FractionalPrimes.Literature.Polynomial.ScalarWeylShortLength

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

set_option maxHeartbeats 600000 in
/-- The degree-`d` induction step in the approved scalar Weyl inverse
theorem. It joins the short-length `q = 1` case to the long-branch argument,
using only the degree-`d-1` inverse theorem as its induction hypothesis. -/
theorem scalarWeyl_degreeStep
    {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (lo hi : ℤ)
    (hJsubset : Finset.Ico lo hi ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    (hlarge : δ * (N : ℝ) ≤
      ‖∑ n ∈ Finset.Ico lo hi, unitFrequencyPhase (P.eval (n : ℝ))‖)
    (hIH : ∀ {M : ℕ}, 1 ≤ M →
      ∀ {ε : ℝ}, 0 < ε → ε < 1 / 2 →
      ∀ (Q : Polynomial ℝ), Q.natDegree ≤ d - 1 →
        ∀ K : Finset ℤ,
          (∃ a b : ℤ, K = Finset.Ico a b) →
          K ⊆ Finset.Icc (1 : ℤ) (M : ℤ) →
          ε * (M : ℝ) ≤
            ‖∑ n ∈ K, unitFrequencyPhase (Q.eval (n : ℝ))‖ →
          ∃ q : ℕ,
            1 ≤ q ∧
            (q : ℝ) ≤
              (weylBoundPolynomial (d - 1)).eval₂
                (Nat.castRingHom ℝ) ε⁻¹ ∧
            (∀ j, 1 ≤ j → j ≤ d - 1 →
              (M : ℝ) ^ j * realDistanceToIntegers
                ((q : ℝ) * Q.coeff j) ≤
                  (weylBoundPolynomial (d - 1)).eval₂
                    (Nat.castRingHom ℝ) ε⁻¹)) :
    ∃ q : ℕ,
      1 ≤ q ∧
      (q : ℝ) ≤ (weylBoundPolynomial d).eval₂
        (Nat.castRingHom ℝ) δ⁻¹ ∧
      (∀ j, 1 ≤ j → j ≤ d →
        (N : ℝ) ^ j * realDistanceToIntegers
          ((q : ℝ) * P.coeff j) ≤
            (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹) := by
  let η : ℝ := δ ^ 2 / 8
  let B : ℝ :=
    (weylBoundPolynomial (d - 1)).eval₂ (Nat.castRingHom ℝ) η⁻¹
  let σ : ℝ := η / (2 * B)
  let R : ℝ := 32 * (d : ℝ) * B * (σ⁻¹) ^ 2
  let V : ℝ := 1 + 8 * R
  let D : ℝ :=
    (weylBoundPolynomial (d - 1)).eval₂ (Nat.castRingHom ℝ)
      (4 * V / δ)
  have hη : η = δ ^ 2 / 8 := rfl
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηhalf : η < 1 / 2 := by
    rw [hη]
    nlinarith [hδhalf]
  have hηle : η ≤ 1 := le_of_lt (hηhalf.trans (by norm_num))
  have hηinv : 1 ≤ η⁻¹ := (one_le_inv₀ hηpos).2 hηle
  have hB : 1 ≤ B := by
    exact (weylBoundPowerControl (d - 1) (by omega) η⁻¹ hηinv).1
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hσ : σ = η / (2 * B) := rfl
  have hRformula : R = 32 * (d : ℝ) * B * (σ⁻¹) ^ 2 := rfl
  have hRnonneg : 0 ≤ R := by dsimp [R]; positivity

  let f : ℕ →+* ℝ := Nat.castRingHom ℝ
  let x : ℝ := δ⁻¹
  have hηinv' : η⁻¹ = 8 * (δ ^ 2)⁻¹ := by
    rw [hη]
    field_simp [ne_of_gt hδ]
  have hBdef : B = (weylBoundPolynomialB d).eval₂ f x := by
    rw [weylBoundPolynomialB, Polynomial.eval₂_comp]
    dsimp [B, f, x]
    simp [Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_pow, hηinv']
  have hRpoly : (weylBoundPolynomialR d).eval₂ f x =
      (8192 * (d : ℝ)) * x ^ 4 *
        ((weylBoundPolynomialB d).eval₂ f x) ^ 3 := by
    simp [weylBoundPolynomialR, f, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_pow]
  have hRnumeric : 32 * (d : ℝ) * B * (σ⁻¹) ^ 2 =
      (8192 * (d : ℝ)) * x ^ 4 * B ^ 3 := by
    rw [hσ]
    dsimp [η, x]
    field_simp [ne_of_gt hδ, ne_of_gt hBpos]
    ring
  have hRdef : R = (weylBoundPolynomialR d).eval₂ f δ⁻¹ := by
    calc
      R = 32 * (d : ℝ) * B * (σ⁻¹) ^ 2 := hRformula
      _ = (8192 * (d : ℝ)) * x ^ 4 * B ^ 3 := hRnumeric
      _ = (8192 * (d : ℝ)) * x ^ 4 *
          ((weylBoundPolynomialB d).eval₂ f x) ^ 3 := by rw [← hBdef]
      _ = (weylBoundPolynomialR d).eval₂ f x := hRpoly.symm
      _ = (weylBoundPolynomialR d).eval₂ f δ⁻¹ := by rfl
  have hDdef : D = (weylBoundPolynomialD d).eval₂ f δ⁻¹ := by
    have hDpoly : (weylBoundPolynomialD d).eval₂ f x =
        (weylBoundPolynomial (d - 1)).eval₂ f
          (4 * x * (1 + 8 * R)) := by
      rw [weylBoundPolynomialD, Polynomial.eval₂_comp]
      simp [f, x, Polynomial.eval₂_mul, Polynomial.eval₂_add,
        Polynomial.eval₂_X, hRdef]
    have hDarg : 4 * x * (1 + 8 * R) = 4 * V / δ := by
      dsimp [x, V]
      field_simp [ne_of_gt hδ]
    calc
      D = (weylBoundPolynomial (d - 1)).eval₂ f (4 * V / δ) := rfl
      _ = (weylBoundPolynomial (d - 1)).eval₂ f
          (4 * x * (1 + 8 * R)) := by
            exact congrArg
              (fun y : ℝ => (weylBoundPolynomial (d - 1)).eval₂ f y)
              hDarg.symm
      _ = (weylBoundPolynomialD d).eval₂ f x := hDpoly.symm
      _ = (weylBoundPolynomialD d).eval₂ f δ⁻¹ := by rfl
  have hNlong : 4 * R ≤ (N : ℝ) ∨ (N : ℝ) < 4 * R :=
    le_or_gt _ _
  rcases hNlong with hNlong | hNshort
  · exact scalarWeyl_longBranch_coefficientPackage
      hd hN hδ hδhalf hη hB hσ hRformula hNlong hRdef hDdef
      P hP lo hi hJsubset hlarge
      (by
        intro M hM Q hQ K hK hKsubset hηpos' hηhalf' hlarge'
        obtain ⟨q, hq, hqB, hcoeff⟩ :=
          hIH (M := M) hM (ε := η) hηpos' hηhalf' Q hQ K
            hK hKsubset hlarge'
        refine ⟨q, hq, ?_, ?_⟩
        · simpa [B] using hqB
        · intro j hj hjd
          simpa [B] using hcoeff j hj (by omega))
      hIH
  · apply scalarWeyl_shortLength_case d N hd hN hδ hδhalf P
    simpa [hRdef] using hNshort

end FractionalPrimes.Literature.Polynomial
