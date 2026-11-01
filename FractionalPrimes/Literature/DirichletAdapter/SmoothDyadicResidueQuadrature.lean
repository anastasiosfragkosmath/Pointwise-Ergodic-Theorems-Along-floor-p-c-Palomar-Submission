module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothDyadicSourceCompact

/-! Assembly of the two exact analytic pieces of special-profile residue
quadrature, before the blueprint's `C_j` constant is factored out. -/

@[expose] public section

open MeasureTheory
open scoped ContDiff CompactlySupported

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The approved `C_j` dominates exactly the mean and derivative
coefficients occurring in the two-term estimate. -/
theorem smoothDyadicC_dominates_B_and_A (j : ℕ) :
    Twisted.smoothDyadicB j ≤ Twisted.smoothDyadicC j ∧
      4 * (2 : ℝ) ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) *
          Twisted.smoothDyadicA j ≤ Twisted.smoothDyadicC j := by
  let R : ℝ := max 1 (max (Twisted.smoothDyadicA j) (Twisted.smoothDyadicB j))
  let K : ℝ := (2 : ℝ) ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j)
  have hA : Twisted.smoothDyadicA j ≤ R :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hB : Twisted.smoothDyadicB j ≤ R :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hR : 0 ≤ R := by
    have := (le_max_left (1 : ℝ) (max (Twisted.smoothDyadicA j)
      (Twisted.smoothDyadicB j)))
    dsimp [R]
    linarith
  have hK : 1 ≤ K := by
    have h2 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    have hbase : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 j
    have hJ : (1 : ℝ) ≤ (((j + 1 : ℕ) : ℝ) ^ j) := one_le_pow₀ hbase
    dsimp [K]
    nlinarith
  have hC : Twisted.smoothDyadicC j = 8 * K * R := by
    calc
      Twisted.smoothDyadicC j =
          (2 : ℝ) ^ (j + 4) * (((j + 1 : ℕ) : ℝ) ^ j) * R := rfl
      _ = (8 * (2 : ℝ) ^ (j + 1)) * (((j + 1 : ℕ) : ℝ) ^ j) * R := by
        rw [show j + 4 = (j + 1) + 3 by omega, pow_add]
        rw [show (2 : ℝ) ^ 3 = 8 by norm_num]
        ring
      _ = 8 * K * R := by dsimp [K]; ring
  constructor
  · rw [hC]
    nlinarith [mul_nonneg (by linarith : 0 ≤ K) hR]
  · rw [hC]
    calc
      4 * (2 : ℝ) ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) *
          Twisted.smoothDyadicA j = 4 * K * Twisted.smoothDyadicA j := by
            dsimp [K]
            ring
      _ ≤ 8 * K * R := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ K) (sub_nonneg.mpr hA),
          mul_nonneg (by linarith : 0 ≤ K) hR]

/-- The source-facing estimate with its two original coefficient terms
still displayed separately. -/
theorem smoothDyadicResidueQuadrature_twoTerms
    (N t : ℝ) (p : ℝ × ℝ × ℝ) (q : ℕ) (b : ℤ) (j : ℕ)
    (hN : 1 ≤ N) (hp : p ∈ Twisted.smoothDyadicProfileParameterBox)
    (hq : 1 ≤ q) (hj : 2 ≤ j) (ht : 1 ≤ |t|) :
    ‖∑' n : ResidueLattice (q : ℤ) b,
      Twisted.smoothDyadicQuadratureSource N t p (n.1 : ℝ)‖ ≤
      4 * (q : ℝ) ^ (j - 1) *
        (N ^ ((1 / 2 : ℝ) - (j : ℝ)) *
          (2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j) *
          Twisted.smoothDyadicA j) +
      (q : ℝ)⁻¹ * (Real.sqrt N * (Twisted.smoothDyadicB j / |t| ^ j)) := by
  have hNpos : 0 < N := by linarith
  have htne : t ≠ 0 := by
    intro h
    simp [h] at ht
    linarith
  let F : C_c(ℝ, ℂ) := smoothDyadicQuadratureSourceCompact N t p hNpos
  have hF : (F : ℝ → ℂ) = Twisted.smoothDyadicQuadratureSource N t p := rfl
  have hquad := highOrderResidueQuadrature F
    (by rw [hF]; exact Twisted.smoothDyadicQuadratureSource_contDiff p hNpos)
    q hq b j hj
  have hderiv := Twisted.smoothDyadicQuadratureSource_derivativeL1_le
    p j hN hj ht hp
  have hmean := smoothDyadicQuadratureSource_integral_le_B
    j N t p hNpos hp htne
  rw [hF] at hquad
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  calc
    ‖∑' n : ResidueLattice (q : ℤ) b,
        Twisted.smoothDyadicQuadratureSource N t p (n.1 : ℝ)‖ =
      ‖((∑' n : ResidueLattice (q : ℤ) b,
          Twisted.smoothDyadicQuadratureSource N t p (n.1 : ℝ)) -
          (q : ℝ)⁻¹ • ∫ x : ℝ,
            Twisted.smoothDyadicQuadratureSource N t p x ∂volume) +
          (q : ℝ)⁻¹ • ∫ x : ℝ,
            Twisted.smoothDyadicQuadratureSource N t p x ∂volume‖ := by
        congr 1
        abel
    _ ≤ ‖((∑' n : ResidueLattice (q : ℤ) b,
          Twisted.smoothDyadicQuadratureSource N t p (n.1 : ℝ)) -
          (q : ℝ)⁻¹ • ∫ x : ℝ,
            Twisted.smoothDyadicQuadratureSource N t p x ∂volume)‖ +
          ‖(q : ℝ)⁻¹ • ∫ x : ℝ,
            Twisted.smoothDyadicQuadratureSource N t p x ∂volume‖ :=
        norm_add_le _ _
    _ ≤ _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hqpos)]
      gcongr
      · exact hquad.trans (by gcongr)

/-- Algebraic comparison of the exact two-term estimate with the
single constant specified by the approved blueprint. -/
theorem smoothDyadicResidueQuadrature_twoTerms_le_C
    (N t : ℝ) (q j : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    4 * (q : ℝ) ^ (j - 1) *
        (N ^ ((1 / 2 : ℝ) - (j : ℝ)) *
          (2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j) *
          Twisted.smoothDyadicA j) +
      (q : ℝ)⁻¹ * (Real.sqrt N * (Twisted.smoothDyadicB j / |t| ^ j)) ≤
      Twisted.smoothDyadicC j * Real.sqrt N *
        ((q : ℝ)⁻¹ * |t| ^ (-(j : ℝ)) +
          (q : ℝ) ^ (j - 1) * ((1 + |t|) / N) ^ j) := by
  let Q : ℝ := q
  let S : ℝ := Real.sqrt N
  let U : ℝ := |t|
  let V : ℝ := 1 + |t|
  let K : ℝ := (2 : ℝ) ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j)
  let A : ℝ := Twisted.smoothDyadicA j
  let B : ℝ := Twisted.smoothDyadicB j
  let C : ℝ := Twisted.smoothDyadicC j
  have hNpos : 0 < N := by linarith
  have hQpos : 0 < Q := by dsimp [Q]; exact_mod_cast hq
  have hUpos : 0 < U := by dsimp [U]; linarith
  have hCB := (smoothDyadicC_dominates_B_and_A j).1
  have hCA := (smoothDyadicC_dominates_B_and_A j).2
  have hD : N ^ ((1 / 2 : ℝ) - (j : ℝ)) *
      (K * V ^ j) * A = S * (K * A * (V / N) ^ j) := by
    rw [Real.rpow_sub hNpos, ← Real.sqrt_eq_rpow, Real.rpow_natCast]
    dsimp [S]
    rw [div_pow]
    field_simp
  have hphase : B / U ^ j = U ^ (-(j : ℝ)) * B := by
    rw [Real.rpow_neg hUpos.le, Real.rpow_natCast]
    ring
  have hQnonneg : 0 ≤ Q⁻¹ * U ^ (-(j : ℝ)) := by positivity
  have hVnonneg : 0 ≤ Q ^ (j - 1) * (V / N) ^ j := by positivity
  have hfirst : Q⁻¹ * U ^ (-(j : ℝ)) * B ≤
      Q⁻¹ * U ^ (-(j : ℝ)) * C :=
    mul_le_mul_of_nonneg_left hCB hQnonneg
  have hsecond : (Q ^ (j - 1) * (V / N) ^ j) * (4 * K * A) ≤
      (Q ^ (j - 1) * (V / N) ^ j) * C := by
    apply mul_le_mul_of_nonneg_left _ hVnonneg
    dsimp [K, A, C]
    nlinarith [hCA]
  change 4 * Q ^ (j - 1) * (N ^ ((1 / 2 : ℝ) - (j : ℝ)) *
      (K * V ^ j) * A) + Q⁻¹ * (S * (B / U ^ j)) ≤
    C * S * (Q⁻¹ * U ^ (-(j : ℝ)) + Q ^ (j - 1) * (V / N) ^ j)
  rw [hD, hphase]
  calc
    4 * Q ^ (j - 1) * (S * (K * A * (V / N) ^ j)) +
        Q⁻¹ * (S * (U ^ (-(j : ℝ)) * B)) =
      S * (Q⁻¹ * U ^ (-(j : ℝ)) * B +
        (Q ^ (j - 1) * (V / N) ^ j) * (4 * K * A)) := by ring
    _ ≤ S * (Q⁻¹ * U ^ (-(j : ℝ)) * C +
        (Q ^ (j - 1) * (V / N) ^ j) * C) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (Real.sqrt_nonneg N)
    _ = C * S * (Q⁻¹ * U ^ (-(j : ℝ)) +
        Q ^ (j - 1) * (V / N) ^ j) := by ring

/-- The source-facing second inequality of `lda:quadrature`, with the
approved `C_j`, arbitrary residue, and no coprimality hypothesis. -/
theorem smoothDyadicResidueQuadrature
    (N t : ℝ) (p : ℝ × ℝ × ℝ) (q : ℕ) (b : ℤ) (j : ℕ)
    (hN : 1 ≤ N) (hp : p ∈ Twisted.smoothDyadicProfileParameterBox)
    (hq : 1 ≤ q) (hj : 2 ≤ j) (ht : 1 ≤ |t|) :
    ‖∑' n : ResidueLattice (q : ℤ) b,
      Twisted.smoothDyadicQuadratureSource N t p (n.1 : ℝ)‖ ≤
      Twisted.smoothDyadicC j * Real.sqrt N *
        ((q : ℝ)⁻¹ * |t| ^ (-(j : ℝ)) +
          (q : ℝ) ^ (j - 1) * ((1 + |t|) / N) ^ j) := by
  exact (smoothDyadicResidueQuadrature_twoTerms N t p q b j hN hp hq hj ht).trans
    (smoothDyadicResidueQuadrature_twoTerms_le_C N t q j hN hq ht)

#print axioms smoothDyadicResidueQuadrature_twoTerms
#print axioms smoothDyadicResidueQuadrature_twoTerms_le_C
#print axioms smoothDyadicResidueQuadrature

end FractionalPrimes.Literature.DirichletAdapter

end
