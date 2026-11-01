module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylInductionClosure
public import FractionalPrimes.Literature.Polynomial.ScalarWeylLongBranchResidueInduction

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

set_option maxHeartbeats 600000 in
/-- Package the long-branch residue induction output into the complete
degree-`d` coefficient conclusion. The hypotheses `hRformula`, `hRdef`, and
`hDdef` are the source recursive identities for the named constants; the
downstream scalar-Weyl helpers use those exact recursive polynomials. -/
theorem scalarWeyl_longBranch_coefficientPackage
    {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    {δ η B σ R D : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hη : η = δ ^ 2 / 8) (hB : 1 ≤ B)
    (hσ : σ = η / (2 * B))
    (hRformula : R = 32 * (d : ℝ) * B * (σ⁻¹) ^ 2)
    (hNlong : 4 * R ≤ (N : ℝ))
    (hRdef : R =
      (weylBoundPolynomialR d).eval₂ (Nat.castRingHom ℝ) δ⁻¹)
    (hDdef : D =
      (weylBoundPolynomialD d).eval₂ (Nat.castRingHom ℝ) δ⁻¹)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (lo hi : ℤ)
    (hJsubset : Finset.Ico lo hi ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    (hlarge : δ * (N : ℝ) ≤
      ‖∑ n ∈ Finset.Ico lo hi, unitFrequencyPhase (P.eval (n : ℝ))‖)
    (hIHη : ∀ {M : ℕ}, 1 ≤ M →
      ∀ (Q : Polynomial ℝ), Q.natDegree ≤ d - 1 →
        ∀ K : Finset ℤ,
          (∃ a b : ℤ, K = Finset.Ico a b) →
          K ⊆ Finset.Icc (1 : ℤ) (M : ℤ) →
          0 < η → η < 1 / 2 →
          η * (M : ℝ) ≤
            ‖∑ n ∈ K, unitFrequencyPhase (Q.eval (n : ℝ))‖ →
          ∃ q : ℕ,
            1 ≤ q ∧ (q : ℝ) ≤ B ∧
            (∀ j, 1 ≤ j → j ≤ d - 1 →
              (M : ℝ) ^ j * realDistanceToIntegers
                ((q : ℝ) * Q.coeff j) ≤ B))
    (hIHfull : ∀ {M : ℕ}, 1 ≤ M →
      ∀ {ε : ℝ}, 0 < ε → ε < 1 / 2 →
      ∀ (Q : Polynomial ℝ), Q.natDegree ≤ d - 1 →
        ∀ K : Finset ℤ,
          (∃ a b : ℤ, K = Finset.Ico a b) →
          K ⊆ Finset.Icc (1 : ℤ) (M : ℤ) →
          ε * (M : ℝ) ≤
            ‖∑ n ∈ K, unitFrequencyPhase (Q.eval (n : ℝ))‖ →
          ∃ s : ℕ,
            1 ≤ s ∧
            (s : ℝ) ≤
              (weylBoundPolynomial (d - 1)).eval₂
                (Nat.castRingHom ℝ) ε⁻¹ ∧
            (∀ i, 1 ≤ i → i ≤ d - 1 →
              (M : ℝ) ^ i * realDistanceToIntegers
                ((s : ℝ) * Q.coeff i) ≤
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
  classical
  let Plo : Polynomial ℝ := scalarWeyl_topMonomialTruncation d P
  let V : ℝ := 1 + 8 * R
  let f : ℕ →+* ℝ := Nat.castRingHom ℝ
  let x : ℝ := δ⁻¹
  have hR_eval : (weylBoundPolynomialR d).eval₂ f x = R := by
    simpa [f, x] using hRdef.symm
  have hD_eval : (weylBoundPolynomialD d).eval₂ f x =
      (weylBoundPolynomial (d - 1)).eval₂ f
        (4 * x * (1 + 8 * R)) := by
    rw [weylBoundPolynomialD, Polynomial.eval₂_comp]
    simp [f, x, Polynomial.eval₂_mul, Polynomial.eval₂_add,
      Polynomial.eval₂_X, hR_eval]
  have hDarg : 4 * x * (1 + 8 * R) = 4 * V / δ := by
    dsimp [x, V]
    field_simp [ne_of_gt hδ]
  have hDmatch :
      (weylBoundPolynomial (d - 1)).eval₂ f (4 * V / δ) = D := by
    calc
      (weylBoundPolynomial (d - 1)).eval₂ f (4 * V / δ) =
          (weylBoundPolynomial (d - 1)).eval₂ f
            (4 * x * (1 + 8 * R)) := by
              exact congrArg
                (fun y : ℝ => (weylBoundPolynomial (d - 1)).eval₂ f y)
                hDarg.symm
      _ = (weylBoundPolynomialD d).eval₂ f x := hD_eval.symm
      _ = D := by simpa [f, x] using hDdef.symm

  have hlong := scalarWeyl_longBranch_residueInductionInput
    hd hN hδ hδhalf hη hB hσ hRformula hNlong P hP
    lo hi hJsubset hlarge hIHη hIHfull
  obtain ⟨r, a, k, b, N', c, K, Q, s, hr, hrR, hnear, hk,
    hprefixSubset, happrox, hprefixLarge, hb, hselected, hN'ceil,
    hN'pos, hN'lower, hN'upper, hcdef, hKdef, hQdef, hKsubset,
    hQdegree, hKinterval, hs, hsBound, hβ⟩ := hlong

  have htrunc := scalarWeyl_topMonomialTruncation_spec d P hP
  have hPlo : Plo.natDegree ≤ d - 1 := by simpa [Plo] using htrunc.1
  have hLowCoeff : ∀ j, 1 ≤ j → j < d → P.coeff j = Plo.coeff j := by
    intro j hj hjd
    simpa [Plo] using htrunc.2.1 j hjd
  have hDmatch' :
      (weylBoundPolynomial (d - 1)).eval₂ f
          (4 * (1 + 8 * R) / δ) = D := by
    simpa [V] using hDmatch
  have hDupper : (s : ℝ) ≤ D := by
    simpa only [f, hDmatch'] using hsBound
  have hβD : ∀ i, 1 ≤ i → i < d →
      realDistanceToIntegers
          ((s : ℝ) *
            (Plo.comp (Polynomial.C (r : ℝ) * Polynomial.X +
              Polynomial.C (c : ℝ))).coeff i) ≤
        D / ((N' : ℝ) ^ i) := by
    intro i hi hid
    simpa only [f, hDmatch', hQdef] using hβ i hi hid
  have hrnonnegR : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hrN : (r : ℝ) ≤ (N : ℝ) := by
    have h4rR : 4 * (r : ℝ) ≤ 4 * R := by nlinarith [hrR]
    have h4rN : 4 * (r : ℝ) ≤ (N : ℝ) := h4rR.trans hNlong
    nlinarith [h4rN]
  have hcCast : (c : ℝ) = (b : ℝ) - (r : ℝ) := by
    rw [hcdef]
    push_cast
    ring
  have hbnonnegR : (0 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast (show (0 : ℤ) ≤ b by
      have := Finset.mem_Icc.mp hb
      omega)
  have hbrR : (b : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hb).2
  have hcBounds : -(r : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ (r : ℝ) := by
    rw [hcCast]
    constructor <;> linarith
  have hc : |(c : ℝ)| ≤ (r : ℝ) := abs_le.mpr hcBounds
  have hcontrol := scalarWeyl_longInductionCoefficientControl
    hd hδ hδhalf hN hr hs hrR hrN hDupper hRdef hDdef hN'lower
    c hc P Plo hPlo hLowCoeff hnear hβD
  exact scalarWeyl_joinLongCoefficientBounds P
    ⟨s * r ^ (d - 1), hcontrol.1, hcontrol.2.1,
      hcontrol.2.2.1, hcontrol.2.2.2⟩

end FractionalPrimes.Literature.Polynomial
