module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseB3

/-!
# The second recurrence step in the bilinear polynomial inverse theorem

This file isolates the recurrence application used at one coefficient in the
descending induction of blueprint item `lbi:inverse-theorem`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

open _root_.Polynomial

/-- The monomial to which the second polynomial recurrence is applied. -/
def bilinearSecondRecurrencePolynomial (a : ℝ) (j : ℕ) : Polynomial ℝ :=
  monomial (j - 1) a

theorem bilinearSecondRecurrencePolynomial_eval
    (a x : ℝ) (j : ℕ) :
    (bilinearSecondRecurrencePolynomial a j).eval x = a * x ^ (j - 1) := by
  simp [bilinearSecondRecurrencePolynomial]

theorem bilinearSecondRecurrencePolynomial_coeff
    (a : ℝ) (j : ℕ) :
    (bilinearSecondRecurrencePolynomial a j).coeff (j - 1) = a := by
  simp [bilinearSecondRecurrencePolynomial]

theorem bilinearSecondRecurrencePolynomial_natDegree_le
    (a : ℝ) (d j : ℕ) (hjd : j ≤ d) :
    (bilinearSecondRecurrencePolynomial a j).natDegree ≤ d := by
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- Abstract one-coefficient form of the second recurrence.  A dense subset
of the one-indexed range on which `a u^(j-1)` is small modulo one produces a
single integer multiplier and the exact loss from the recurrence theorem. -/
theorem bilinearSecondRecurrence_core
    (d j N : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d)
    (δ ε V a : ℝ)
    (hN : 1 ≤ N)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ / 64)
    (hTlarge : recurrenceBudgetT d δ⁻¹ ≤ (N : ℝ))
    (hRbound : recurrenceBudgetR d δ⁻¹ ≤ V)
    (U : Finset ℕ)
    (hUrange : U ⊆ Finset.Icc 1 N)
    (hUcard : 2 * δ * (N : ℝ) ≤ (U.card : ℝ))
    (happrox : ∀ u ∈ U,
      realDistanceToIntegers (a * (u : ℝ) ^ (j - 1)) ≤ ε) :
    ∃ b : ℕ, 1 ≤ b ∧ (b : ℝ) ≤ V ∧
      realDistanceToIntegers ((b : ℝ) * a) ≤
        V * ε / (N : ℝ) ^ (j - 1) := by
  classical
  let P : Polynomial ℝ := bilinearSecondRecurrencePolynomial a j
  let Good : ℕ → Prop := fun u =>
    realDistanceToIntegers (P.eval (u : ℝ)) ≤ ε
  let goodSet : Finset ℕ :=
    (Finset.range N).filter fun n => Good (n + 1)
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hPdeg : P.natDegree ≤ d := by
    simpa [P] using bilinearSecondRecurrencePolynomial_natDegree_le a d j hjd
  have hUbounds : ∀ u ∈ U, 0 < u ∧ u ≤ 0 + N := by
    intro u hu
    have huIcc := Finset.mem_Icc.mp (hUrange hu)
    omega
  have hUGood : ∀ u ∈ U, Good (u - 0) := by
    intro u hu
    dsimp [Good, P]
    rw [bilinearSecondRecurrencePolynomial_eval]
    simpa using happrox u hu
  have hUcardNat : U.card ≤ goodSet.card := by
    dsimp [goodSet]
    exact card_le_oneIndexed_range_filter_of_window U 0 N Good
      hUbounds hUGood
  have hUcardReal : (U.card : ℝ) ≤ (goodSet.card : ℝ) := by
    exact_mod_cast hUcardNat
  have hgood : δ * (N : ℝ) ≤ (goodSet.card : ℝ) := by
    calc
      δ * (N : ℝ) ≤ 2 * δ * (N : ℝ) := by
        have hnonneg : 0 ≤ δ * (N : ℝ) := by positivity
        linarith
      _ ≤ (U.card : ℝ) := hUcard
      _ ≤ (goodSet.card : ℝ) := hUcardReal
  have hgood' : δ * (N : ℝ) ≤
      (((Finset.range N).filter
        (fun n : ℕ => realDistanceToIntegers
          (P.eval ((n + 1 : ℕ) : ℝ)) ≤ ε)).card : ℝ) := by
    simpa [goodSet, Good] using hgood
  obtain ⟨b, hb, hbR, hbcoeff⟩ :=
    polynomialRecurrence (d := d) (N := N) hN hδ hδhalf
      hε hεδ P hPdeg hgood' hTlarge
  refine ⟨b, hb, hbR.trans hRbound, ?_⟩
  have hcoefficient := hbcoeff (j - 1) (by omega)
  rw [show P.coeff (j - 1) = a by
    simpa [P] using bilinearSecondRecurrencePolynomial_coeff a j] at hcoefficient
  apply (le_div_iff₀ (pow_pos hNpos (j - 1))).2
  calc
    realDistanceToIntegers ((b : ℝ) * a) * (N : ℝ) ^ (j - 1) =
        (N : ℝ) ^ (j - 1) *
          realDistanceToIntegers ((b : ℝ) * a) := by ring
    _ ≤ recurrenceBudgetR d δ⁻¹ * ε := hcoefficient
    _ ≤ V * ε := mul_le_mul_of_nonneg_right hRbound hε

/-- The definition `V₂=T_d(Z₂)+R_d(Z₂)` simultaneously dominates both
budgets required by the second recurrence. -/
theorem bilinearSecondRecurrence_budget_bounds
    (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    recurrenceBudgetT d ((bilinearInverseZTwo d ρ⁻¹)⁻¹)⁻¹ ≤
        bilinearInverseVTwo d ρ⁻¹ ∧
      recurrenceBudgetR d ((bilinearInverseZTwo d ρ⁻¹)⁻¹)⁻¹ ≤
        bilinearInverseVTwo d ρ⁻¹ := by
  have hx : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hvalues := bilinearInverseBudget_values d hd ρ⁻¹ hx
  have hZTwo : 2 < bilinearInverseZTwo d ρ⁻¹ :=
    hvalues.2.2.2.2.1
  have hT := recurrenceBudgetT_ge_one d hd
    (bilinearInverseZTwo d ρ⁻¹) hZTwo.le
  have hR := recurrenceBudgetR_ge_one d hd
    (bilinearInverseZTwo d ρ⁻¹) hZTwo.le
  have hV : bilinearInverseVTwo d ρ⁻¹ =
      recurrenceBudgetT d (bilinearInverseZTwo d ρ⁻¹) +
        recurrenceBudgetR d (bilinearInverseZTwo d ρ⁻¹) := by
    rw [bilinearInverseVTwo_eval, bilinearRecurrenceG_eval]
  rw [inv_inv]
  constructor
  · rw [hV]
    linarith
  · rw [hV]
    linarith

/-- The exact source budget makes the B3 error small enough for the second
recurrence.  This is the numerical inequality
`C_d A e/(r s^j) ≤ δ₂/64` isolated from the recurrence invocation. -/
theorem bilinearSecondRecurrence_epsilon_le
    (d j : ℕ) (hd : 1 ≤ d) (hj : 2 ≤ j)
    (X H L M ρ e : ℝ)
    (hL : 0 < L) (hM : 0 < M) (hH : 0 < H)
    (hX : X = L * M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (hZr : bilinearInverseZ d ρ⁻¹ ≤ H / L)
    (hZs : bilinearInverseZ d ρ⁻¹ ≤ H / M)
    (he : 0 ≤ e) (heE : e ≤ bilinearInverseE d ρ⁻¹) :
    (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ * e *
        M ^ (j - 1) * X / H ^ (j + 1) ≤
      (bilinearInverseZTwo d ρ⁻¹)⁻¹ / 64 := by
  let C : ℝ := bilinearInverseCValue d
  let A : ℝ := bilinearInverseA d ρ⁻¹
  let E : ℝ := bilinearInverseE d ρ⁻¹
  let ZTwo : ℝ := bilinearInverseZTwo d ρ⁻¹
  let Z : ℝ := bilinearInverseZ d ρ⁻¹
  let r : ℝ := H / L
  let s : ℝ := H / M
  have hx : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  rcases bilinearInverseBudget_values d hd ρ⁻¹ hx with
    ⟨hB, hZOne, hVOne, hA, hZTwo, hVTwo, hC, hE, hZ⟩
  have hC0 : 0 ≤ C := by dsimp [C]; linarith
  have hA0 : 0 ≤ A := by dsimp [A]; linarith
  have hE0 : 0 ≤ E := by dsimp [E]; linarith
  have hZTwoPos : 0 < ZTwo := by dsimp [ZTwo]; linarith
  have hZpos : 0 < Z := by dsimp [Z]; linarith
  have hr : Z ≤ r := by simpa [Z, r] using hZr
  have hs : Z ≤ s := by simpa [Z, s] using hZs
  have hrpos : 0 < r := hZpos.trans_le hr
  have hspos : 0 < s := hZpos.trans_le hs
  have hsone : 1 ≤ s := by
    have : (8 : ℝ) ≤ Z := by simpa [Z] using hZ
    linarith
  have hsPow : s ≤ s ^ j := by
    nth_rewrite 1 [← pow_one s]
    exact pow_le_pow_right₀ hsone (by omega)
  have hZsq_rs : Z ^ 2 ≤ r * s ^ j := by
    calc
      Z ^ 2 = Z * Z := by ring
      _ ≤ r * s := mul_le_mul hr hs (by linarith) (by linarith)
      _ ≤ r * s ^ j := mul_le_mul_of_nonneg_left hsPow hrpos.le
  have hdenPos : 0 < r * s ^ j := mul_pos hrpos (pow_pos hspos j)
  have hnum : C * A * e ≤ C * A * E := by
    exact mul_le_mul_of_nonneg_left (by simpa [E] using heE)
      (mul_nonneg hC0 hA0)
  have hnum0 : 0 ≤ C * A * E := by positivity
  have hdom : 64 * C * A * E * ZTwo ≤ Z := by
    simpa [C, A, E, ZTwo, Z] using
      (bilinearInverseZ_dominates d hd ρ⁻¹ hx).2.2.2.1
  have hZleSq : Z ≤ Z ^ 2 := by nlinarith
  have hdomSq : 64 * C * A * E * ZTwo ≤ Z ^ 2 := hdom.trans hZleSq
  have hscale :
      M ^ (j - 1) * X / H ^ (j + 1) = 1 / (r * s ^ j) := by
    have hMpow : M ^ (j - 1) * M = M ^ j := by
      rw [← pow_succ]
      congr 2
      omega
    have hHpow : H ^ (j + 1) = H ^ j * H := by rw [pow_succ]
    dsimp [r, s]
    rw [hX, hHpow, div_pow]
    field_simp [hL.ne', hM.ne', hH.ne', pow_ne_zero]
    rw [hMpow]
  have hright : ZTwo⁻¹ / 64 = 1 / (64 * ZTwo) := by
    field_simp [hZTwoPos.ne']
  calc
    (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ * e *
          M ^ (j - 1) * X / H ^ (j + 1) =
        C * A * e / (r * s ^ j) := by
      change C * A * e * M ^ (j - 1) * X / H ^ (j + 1) =
        C * A * e / (r * s ^ j)
      calc
        C * A * e * M ^ (j - 1) * X / H ^ (j + 1) =
            (C * A * e) * (M ^ (j - 1) * X / H ^ (j + 1)) := by ring
        _ = C * A * e / (r * s ^ j) := by rw [hscale]; ring
    _ ≤ C * A * E / (r * s ^ j) :=
      div_le_div₀ (by positivity) hnum hdenPos le_rfl
    _ ≤ C * A * E / Z ^ 2 :=
      div_le_div₀ hnum0 le_rfl (sq_pos_of_pos hZpos) hZsq_rs
    _ ≤ 1 / (64 * ZTwo) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hZpos)
        (mul_pos (by norm_num) hZTwoPos)).2
      nlinarith
    _ = (bilinearInverseZTwo d ρ⁻¹)⁻¹ / 64 := by
      simpa [ZTwo] using hright.symm

/-- Exact second recurrence at one coefficient index in the bilinear inverse
argument.  The conclusion is the update used in the descending induction. -/
theorem bilinearSecondRecurrence_for_degree
    (d j : ℕ) (hd : 1 ≤ d) (hj : 2 ≤ j) (hjd : j ≤ d)
    (X H L M ρ e a : ℝ)
    (hL : 0 < L) (hM : 1 ≤ M) (hH : 0 < H)
    (hX : X = L * M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (hZr : bilinearInverseZ d ρ⁻¹ ≤ H / L)
    (hZs : bilinearInverseZ d ρ⁻¹ ≤ H / M)
    (hrM : H / L ≤ M)
    (he : 0 ≤ e) (heE : e ≤ bilinearInverseE d ρ⁻¹)
    (U : Finset ℕ)
    (hUrange : U ⊆ Finset.Icc 1 (bilinearSecondRecurrenceLength M))
    (hUcard :
      2 * (bilinearInverseZTwo d ρ⁻¹)⁻¹ *
          (bilinearSecondRecurrenceLength M : ℝ) ≤ (U.card : ℝ))
    (happrox : ∀ u ∈ U,
      realDistanceToIntegers (a * (u : ℝ) ^ (j - 1)) ≤
        (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ * e *
          M ^ (j - 1) * X / H ^ (j + 1)) :
    ∃ b : ℕ, 1 ≤ b ∧
      (b : ℝ) ≤ bilinearInverseVTwo d ρ⁻¹ ∧
      realDistanceToIntegers ((b : ℝ) * a) ≤
        bilinearInverseVTwo d ρ⁻¹ *
          (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ * e *
            X / H ^ (j + 1) := by
  let N : ℕ := bilinearSecondRecurrenceLength M
  let δ : ℝ := (bilinearInverseZTwo d ρ⁻¹)⁻¹
  let ε : ℝ :=
    (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ * e *
      M ^ (j - 1) * X / H ^ (j + 1)
  let V : ℝ := bilinearInverseVTwo d ρ⁻¹
  have hMpos : 0 < M := by linarith
  have hXpos : 0 < X := by rw [hX]; positivity
  have hNbounds := bilinearSecondRecurrenceLength_bounds M hM
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := hM.trans hNbounds.1
    exact_mod_cast this
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  rcases bilinearInverse_auxiliary_densities d hd ρ hρ hρhalf with
    ⟨hδOne, hδOneHalf, hδ, hδHalf⟩
  have hx : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hvalues := bilinearInverseBudget_values d hd ρ⁻¹ hx
  have hA0 : 0 ≤ bilinearInverseA d ρ⁻¹ := by
    linarith [hvalues.2.2.2.1]
  have hC0 : 0 ≤ (bilinearInverseCValue d : ℝ) := by
    linarith [hvalues.2.2.2.2.2.2.1]
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεδ : ε ≤ δ / 64 := by
    dsimp [ε, δ]
    exact bilinearSecondRecurrence_epsilon_le d j hd hj X H L M ρ e
      hL hMpos hH hX hρ hρhalf hZr hZs he heE
  rcases bilinearSecondRecurrence_budget_bounds d hd ρ hρ hρhalf with
    ⟨hTbudget, hRbudget⟩
  have hVleZ : bilinearInverseVTwo d ρ⁻¹ ≤ bilinearInverseZ d ρ⁻¹ :=
    (bilinearInverseZ_dominates d hd ρ⁻¹ hx).2.1
  have hTlarge : recurrenceBudgetT d δ⁻¹ ≤ (N : ℝ) := by
    calc
      recurrenceBudgetT d δ⁻¹ ≤ V := by simpa [δ, V] using hTbudget
      _ ≤ bilinearInverseZ d ρ⁻¹ := by simpa [V] using hVleZ
      _ ≤ H / L := hZr
      _ ≤ M := hrM
      _ ≤ (N : ℝ) := hNbounds.1
  have hRbound : recurrenceBudgetR d δ⁻¹ ≤ V := by
    simpa [δ, V] using hRbudget
  obtain ⟨b, hb, hbV, hberror⟩ :=
    bilinearSecondRecurrence_core d j N (by omega) hjd δ ε V a hN
      (by simpa [δ] using hδ) (by simpa [δ] using hδHalf) hε hεδ
      hTlarge hRbound U (by simpa [N] using hUrange)
      (by simpa [N, δ] using hUcard)
      (by simpa [ε] using happrox)
  refine ⟨b, hb, by simpa [V] using hbV, ?_⟩
  have hV0 : 0 ≤ V := by
    dsimp [V]
    linarith [hvalues.2.2.2.2.2.1]
  have hpow : M ^ (j - 1) ≤ (N : ℝ) ^ (j - 1) :=
    pow_le_pow_left₀ hMpos.le hNbounds.1 (j - 1)
  let K : ℝ := V * (bilinearInverseCValue d : ℝ) *
    bilinearInverseA d ρ⁻¹ * e * X / H ^ (j + 1)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hscale :
      V * ε / (N : ℝ) ^ (j - 1) ≤ K := by
    apply (div_le_iff₀ (pow_pos hNpos (j - 1))).2
    dsimp [ε, K]
    calc
      V * ((bilinearInverseCValue d : ℝ) *
            bilinearInverseA d ρ⁻¹ * e * M ^ (j - 1) * X /
              H ^ (j + 1)) =
          K * M ^ (j - 1) := by dsimp [K]; ring
      _ ≤ K * (N : ℝ) ^ (j - 1) :=
        mul_le_mul_of_nonneg_left hpow hK0
  exact hberror.trans (by simpa [K, V] using hscale)

#print axioms bilinearSecondRecurrencePolynomial_eval
#print axioms bilinearSecondRecurrencePolynomial_coeff
#print axioms bilinearSecondRecurrencePolynomial_natDegree_le
#print axioms bilinearSecondRecurrence_core
#print axioms bilinearSecondRecurrence_budget_bounds
#print axioms bilinearSecondRecurrence_epsilon_le
#print axioms bilinearSecondRecurrence_for_degree

end

end FractionalPrimes.Literature.Polynomial
