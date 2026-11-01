module

public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrence
public import FractionalPrimes.Literature.Polynomial.PolynomialProductRecurrenceBudgets

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

private theorem card_filter_product_eq_sum_card_filter
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (G : α → β → Prop) [DecidableRel G] :
    ((s ×ˢ t).filter (fun p : α × β => G p.1 p.2)).card =
      ∑ q ∈ s, (t.filter (G q)).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- A density of good pairs leaves at least half that density of rows, each
carrying half the original column density. -/
private theorem many_dense_rows
    {N₁ N₂ : ℕ} (hN₂ : 1 ≤ N₂) {σ : ℝ} (hσ : 0 < σ)
    (G : ℕ → ℕ → Prop) [DecidableRel G]
    (hgood : σ * (N₁ : ℝ) * (N₂ : ℝ) ≤
      ((((Finset.range N₁ ×ˢ Finset.range N₂).filter
        (fun p : ℕ × ℕ => G p.1 p.2)).card : ℕ) : ℝ)) :
    σ * (N₁ : ℝ) / 2 ≤
      ((((Finset.range N₁).filter (fun q =>
        σ * (N₂ : ℝ) / 2 ≤
          ((((Finset.range N₂).filter (G q)).card : ℕ) : ℝ))).card : ℕ) : ℝ) := by
  classical
  let S : Finset ℕ := Finset.range N₁
  let T : Finset ℕ := Finset.range N₂
  let row : ℕ → ℝ := fun q => (((T.filter (G q)).card : ℕ) : ℝ)
  let dense : ℕ → Prop := fun q => σ * (N₂ : ℝ) / 2 ≤ row q
  let Good : Finset ℕ := S.filter dense
  let Bad : Finset ℕ := S.filter (fun q => ¬ dense q)
  have hcardReal :
      (((((S ×ˢ T).filter (fun p : ℕ × ℕ => G p.1 p.2)).card : ℕ) : ℝ)) =
        ∑ q ∈ S, row q := by
    rw [card_filter_product_eq_sum_card_filter]
    simp [row]
  have hmass : σ * (N₁ : ℝ) * (N₂ : ℝ) ≤ ∑ q ∈ S, row q := by
    rw [← hcardReal]
    simpa [S, T] using hgood
  have hsplit : (∑ q ∈ S, row q) =
      (∑ q ∈ Good, row q) + ∑ q ∈ Bad, row q := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := S) (p := dense) (f := row)]
  by_contra hnot
  have hGoodlt : (Good.card : ℝ) < σ * (N₁ : ℝ) / 2 := by
    have hlt := lt_of_not_ge hnot
    simpa [S, T, row, dense, Good] using hlt
  have hrowBound (q : ℕ) (_hq : q ∈ S) : row q ≤ (N₂ : ℝ) := by
    dsimp [row]
    have hNat : (T.filter (G q)).card ≤ N₂ := by
      simpa [T] using Finset.card_filter_le T (G q)
    exact_mod_cast hNat
  have hgoodSum : (∑ q ∈ Good, row q) ≤ (Good.card : ℝ) * (N₂ : ℝ) := by
    calc
      (∑ q ∈ Good, row q) ≤ ∑ _q ∈ Good, (N₂ : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact hrowBound q (Finset.filter_subset _ _ hq)
      _ = (Good.card : ℝ) * (N₂ : ℝ) := by simp
  have hbadSum : (∑ q ∈ Bad, row q) ≤
      (Bad.card : ℝ) * (σ * (N₂ : ℝ) / 2) := by
    calc
      (∑ q ∈ Bad, row q) ≤
          ∑ _q ∈ Bad, (σ * (N₂ : ℝ) / 2) := by
        apply Finset.sum_le_sum
        intro q hq
        have hnDense : ¬ dense q := Finset.mem_filter.mp hq |>.2
        exact le_of_lt (lt_of_not_ge hnDense)
      _ = (Bad.card : ℝ) * (σ * (N₂ : ℝ) / 2) := by simp
  have hcardBad : (Bad.card : ℝ) ≤ (N₁ : ℝ) := by
    have hsub : Bad ⊆ S := Finset.filter_subset _ _
    calc
      (Bad.card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (N₁ : ℝ) := by simp [S]
  have hsumUpper : (∑ q ∈ S, row q) <
      σ * (N₁ : ℝ) * (N₂ : ℝ) := by
    rw [hsplit]
    calc
      (∑ q ∈ Good, row q) + ∑ q ∈ Bad, row q ≤
          (Good.card : ℝ) * (N₂ : ℝ) +
            (Bad.card : ℝ) * (σ * (N₂ : ℝ) / 2) :=
        add_le_add hgoodSum hbadSum
      _ < (σ * (N₁ : ℝ) / 2) * (N₂ : ℝ) +
          (N₁ : ℝ) * (σ * (N₂ : ℝ) / 2) := by
        apply add_lt_add_of_lt_of_le
        · exact mul_lt_mul_of_pos_right hGoodlt (by exact_mod_cast hN₂)
        · exact mul_le_mul_of_nonneg_right hcardBad (by positivity)
      _ = σ * (N₁ : ℝ) * (N₂ : ℝ) := by ring
  linarith

/-- A finite-valued denominator map whose positive values are bounded by a
real number `A` has a fiber of relative size at least `1/A`. -/
private theorem exists_large_denominator_fiber
    {α : Type*} [DecidableEq α] (S : Finset α) (rmap : α → ℕ)
    (A : ℝ) (hA : 1 ≤ A)
    (hrpos : ∀ x ∈ S, 1 ≤ rmap x)
    (hrbound : ∀ x ∈ S, (rmap x : ℝ) ≤ A) :
    ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ A ∧
      (S.card : ℝ) / A ≤ ((S.filter fun x => rmap x = r).card : ℝ) := by
  classical
  let T : Finset ℕ := Finset.Icc 1 ⌊A⌋₊
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hfloor : 1 ≤ ⌊A⌋₊ := Nat.le_floor (by simpa using hA)
  have hTnonempty : T.Nonempty := by
    exact ⟨1, by simp [T, hfloor]⟩
  have hmaps : ∀ x ∈ S, rmap x ∈ T := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hrpos x hx, Nat.le_floor (hrbound x hx)⟩
  have hTcard : (T.card : ℝ) ≤ A := by
    have hcard : T.card = ⌊A⌋₊ := by
      simp [T, Nat.card_Icc]
    rw [hcard]
    exact Nat.floor_le (le_trans (by norm_num) hA)
  have hsum : T.card • ((S.card : ℝ) / A) ≤
      ∑ _x ∈ S, (1 : ℝ) := by
    rw [nsmul_eq_mul]
    calc
      (T.card : ℝ) * ((S.card : ℝ) / A) ≤
          A * ((S.card : ℝ) / A) :=
        mul_le_mul_of_nonneg_right hTcard (by positivity)
      _ = (S.card : ℝ) := by field_simp [ne_of_gt hApos]
      _ = ∑ _x ∈ S, (1 : ℝ) := by simp
  obtain ⟨r, hrT, hrlarge⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := S) (t := T) (f := rmap) (w := fun _ => (1 : ℝ))
      hmaps hTnonempty hsum
  refine ⟨r, (Finset.mem_Icc.mp hrT).1, ?_, ?_⟩
  · exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hrT).2).trans
      (Nat.floor_le (le_trans (by norm_num) hA))
  · simpa using hrlarge

/-- The one-coordinate recurrence step, with the source's explicit short
range alternative. -/
private theorem one_coordinate_recurrence
    {j N q : ℕ} (hj : 1 ≤ j) (hN : 1 ≤ N) (hq : 1 ≤ q)
    {δ ε θ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ / 64)
    (hgood : δ * (N : ℝ) ≤
      (((Finset.range N).filter (fun a : ℕ =>
        realDistanceToIntegers
          (θ * (q : ℝ) ^ j * ((a + 1 : ℕ) : ℝ) ^ j) ≤ ε)).card : ℝ)) :
    ∃ r : ℕ, 1 ≤ r ∧
      (r : ℝ) ≤ recurrenceBudgetR j (δ⁻¹) +
        recurrenceBudgetT j (δ⁻¹) ^ j ∧
      (N : ℝ) ^ j * realDistanceToIntegers
          ((r : ℝ) * θ * (q : ℝ) ^ j) ≤
        (recurrenceBudgetR j (δ⁻¹) +
          recurrenceBudgetT j (δ⁻¹) ^ j) * ε := by
  classical
  let R : ℝ := recurrenceBudgetR j (δ⁻¹)
  let T : ℝ := recurrenceBudgetT j (δ⁻¹)
  let A : ℝ := R + T ^ j
  have hx2 : 2 ≤ δ⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hδ).2 (by nlinarith [hδhalf])
  have hR : 1 ≤ R := by
    exact recurrenceBudgetR_ge_one j hj (δ⁻¹) hx2
  have hT : 1 ≤ T := by
    exact recurrenceBudgetT_ge_one j hj (δ⁻¹) hx2
  have hA : 1 ≤ A := by
    dsimp [A]
    have hTpow : 0 ≤ T ^ j := by positivity
    linarith
  by_cases hlong : T ≤ (N : ℝ)
  · let P : Polynomial ℝ :=
      Polynomial.C (θ * (q : ℝ) ^ j) * Polynomial.X ^ j
    have hPdeg : P.natDegree ≤ j := by
      dsimp [P]
      exact Polynomial.natDegree_C_mul_X_pow_le _ _
    have hgoodP : δ * (N : ℝ) ≤
        (((Finset.range N).filter (fun a : ℕ =>
          realDistanceToIntegers (P.eval ((a + 1 : ℕ) : ℝ)) ≤ ε)).card : ℝ) := by
      simpa [P] using hgood
    obtain ⟨r, hrpos, hrR, hrcoeff⟩ :=
      polynomialRecurrence hN hδ hδhalf hε hεδ P hPdeg hgoodP hlong
    have hRA : recurrenceBudgetR j (δ⁻¹) ≤ A := by
      dsimp [A, R]
      exact le_add_of_nonneg_right (by positivity)
    refine ⟨r, hrpos, ?_, ?_⟩
    · change (r : ℝ) ≤ A
      exact hrR.trans hRA
    · have hjcoeff := hrcoeff j le_rfl
      have hcoeff : P.coeff j = θ * (q : ℝ) ^ j := by
        rw [show P = Polynomial.C (θ * (q : ℝ) ^ j) *
          Polynomial.X ^ j from rfl, Polynomial.coeff_C_mul_X_pow]
        simp
      rw [hcoeff] at hjcoeff
      change (N : ℝ) ^ j * realDistanceToIntegers
          ((r : ℝ) * θ * (q : ℝ) ^ j) ≤ A * ε
      simpa [mul_assoc] using hjcoeff.trans
        (mul_le_mul_of_nonneg_right hRA hε)
  · have hNltT : (N : ℝ) < T := lt_of_not_ge hlong
    have hthreshold : 0 < δ * (N : ℝ) := by
      exact mul_pos hδ (by exact_mod_cast hN)
    have hcardposReal : 0 <
        (((Finset.range N).filter (fun a : ℕ =>
          realDistanceToIntegers
            (θ * (q : ℝ) ^ j * ((a + 1 : ℕ) : ℝ) ^ j) ≤ ε)).card : ℝ) :=
      hthreshold.trans_le hgood
    have hcardpos : 0 <
        ((Finset.range N).filter (fun a : ℕ =>
          realDistanceToIntegers
            (θ * (q : ℝ) ^ j * ((a + 1 : ℕ) : ℝ) ^ j) ≤ ε)).card := by
      exact_mod_cast hcardposReal
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardpos
    rcases Finset.mem_filter.mp ha with ⟨haN, hagood⟩
    have haOne : 1 ≤ a + 1 := by omega
    have haLeN : a + 1 ≤ N := by
      exact Finset.mem_range.mp haN
    let r : ℕ := (a + 1) ^ j
    have hrpos : 1 ≤ r := by
      dsimp [r]
      exact Nat.one_le_pow _ _ haOne
    have harT : ((a + 1 : ℕ) : ℝ) ≤ T := by
      have : (((a + 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by exact_mod_cast haLeN
      exact this.trans hNltT.le
    have hrT : (r : ℝ) ≤ T ^ j := by
      dsimp [r]
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
        (pow_le_pow_left₀ (by positivity) harT j)
    have hTA : T ^ j ≤ A := by
      dsimp [A]
      exact le_add_of_nonneg_left (by linarith [hR])
    refine ⟨r, hrpos, ?_, ?_⟩
    · change (r : ℝ) ≤ A
      exact hrT.trans hTA
    · have hphase : (r : ℝ) * θ * (q : ℝ) ^ j =
          θ * (q : ℝ) ^ j * ((a + 1 : ℕ) : ℝ) ^ j := by
        dsimp [r]
        simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        ring
      rw [hphase]
      calc
        (N : ℝ) ^ j * realDistanceToIntegers
            (θ * (q : ℝ) ^ j * ((a + 1 : ℕ) : ℝ) ^ j) ≤
            (N : ℝ) ^ j * ε :=
          mul_le_mul_of_nonneg_left hagood (by positivity)
        _ ≤ T ^ j * ε := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hNltT.le j) hε
        _ ≤ A * ε := by
          exact mul_le_mul_of_nonneg_right hTA hε

/-- The second pass of the product argument uses the one-coordinate lemma
with multiplier one; specializing it here keeps later elaboration small. -/
private theorem one_coordinate_recurrence_one
    {j N : ℕ} (hj : 1 ≤ j) (hN : 1 ≤ N)
    {δ ε θ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ / 64)
    (hgood : δ * (N : ℝ) ≤
      (((Finset.range N).filter (fun a : ℕ =>
        realDistanceToIntegers
          (θ * ((a + 1 : ℕ) : ℝ) ^ j) ≤ ε)).card : ℝ)) :
    ∃ r : ℕ, 1 ≤ r ∧
      (r : ℝ) ≤ recurrenceBudgetR j (δ⁻¹) +
        recurrenceBudgetT j (δ⁻¹) ^ j ∧
      (N : ℝ) ^ j * realDistanceToIntegers ((r : ℝ) * θ) ≤
        (recurrenceBudgetR j (δ⁻¹) +
          recurrenceBudgetT j (δ⁻¹) ^ j) * ε := by
  have h := one_coordinate_recurrence (q := 1) hj hN (by norm_num)
    hδ hδhalf hε hεδ
    (by simpa using hgood)
  simpa using h

private theorem inv_half (σ : ℝ) (hσ : 0 < σ) :
    (σ / 2)⁻¹ = 2 * σ⁻¹ := by
  field_simp [ne_of_gt hσ]

private theorem inv_quarter_product (σ A : ℝ)
    (hσ : 0 < σ) (hA : 0 < A) :
    (σ / (4 * A))⁻¹ = 4 * A * σ⁻¹ := by
  field_simp [ne_of_gt hσ, ne_of_gt hA]

private theorem product_recurrence_finish
    {j N₁ N₂ r₀ : ℕ} (hj : 1 ≤ j) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    {σ ε θ : ℝ} (hσ : 0 < σ) (hσhalf : σ < 1 / 2)
    (hε : 0 ≤ ε)
    (hεA : ε ≤
      σ / (256 * productRecurrenceA j σ⁻¹ ^ 2))
    (hr₀pos : 1 ≤ r₀)
    (hr₀A : (r₀ : ℝ) ≤ productRecurrenceA j σ⁻¹)
    (hgoodSecond :
      (σ / (4 * productRecurrenceA j σ⁻¹)) * (N₁ : ℝ) ≤
        (((Finset.range N₁).filter (fun q : ℕ =>
          realDistanceToIntegers
            (((r₀ : ℝ) * θ) * ((q + 1 : ℕ) : ℝ) ^ j) ≤
                productRecurrenceA j σ⁻¹ * ε / (N₂ : ℝ) ^ j)).card : ℝ)) :
    ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ productRecurrenceB j σ⁻¹ ∧
      realDistanceToIntegers ((r : ℝ) * θ) ≤
        productRecurrenceB j σ⁻¹ * ε /
          (((N₁ : ℝ) * (N₂ : ℝ)) ^ j) := by
  let z : ℝ := σ⁻¹
  let A : ℝ := productRecurrenceA j z
  let C : ℝ := recurrenceBudgetR j (4 * A * z) +
    recurrenceBudgetT j (4 * A * z) ^ j
  let B : ℝ := productRecurrenceB j z
  let σ₁ : ℝ := σ / (4 * A)
  let ε₁ : ℝ := A * ε / (N₂ : ℝ) ^ j
  have hz2 : 2 ≤ z := by
    dsimp [z]
    rw [← one_div]
    exact (le_div_iff₀ hσ).2 (by nlinarith [hσhalf])
  have hA : 1 ≤ A := productRecurrenceA_ge_one j hj z hz2
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hA0 : 0 ≤ A := hApos.le
  have hεA' : ε ≤ σ / (256 * A ^ 2) := by
    simpa [A, z] using hεA
  have hgoodSecond' : σ₁ * (N₁ : ℝ) ≤
      (((Finset.range N₁).filter (fun q : ℕ =>
        realDistanceToIntegers
          (((r₀ : ℝ) * θ) * ((q + 1 : ℕ) : ℝ) ^ j) ≤ ε₁)).card : ℝ) := by
    simpa [σ₁, ε₁, A, z] using hgoodSecond
  have hσ₁ : 0 < σ₁ := by
    dsimp [σ₁]
    positivity
  have hσ₁half : σ₁ < 1 / 2 := by
    have hden : (4 : ℝ) ≤ 4 * A := by nlinarith
    have hσ₁le : σ₁ ≤ σ / 4 := by
      dsimp [σ₁]
      exact div_le_div_of_nonneg_left hσ.le (by norm_num) hden
    linarith
  have hε₁ : 0 ≤ ε₁ := by
    dsimp [ε₁]
    positivity
  have hN₂powOne : 1 ≤ (N₂ : ℝ) ^ j := by
    have hN₂real : (1 : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast hN₂
    exact one_le_pow₀ hN₂real
  have hAε : A * ε ≤ σ / (256 * A) := by
    calc
      A * ε ≤ A * (σ / (256 * A ^ 2)) :=
        mul_le_mul_of_nonneg_left hεA' hA0
      _ = σ / (256 * A) := by
        field_simp [ne_of_gt hApos]
  have hε₁small : ε₁ ≤ σ₁ / 64 := by
    calc
      ε₁ ≤ A * ε := by
        dsimp [ε₁]
        exact div_le_self (mul_nonneg hA0 hε) hN₂powOne
      _ ≤ σ / (256 * A) := hAε
      _ = σ₁ / 64 := by
        dsimp [σ₁]
        field_simp [ne_of_gt hApos]
        ring
  have hr₁exists : ∃ r : ℕ, 1 ≤ r ∧
      (r : ℝ) ≤ recurrenceBudgetR j (σ₁⁻¹) +
        recurrenceBudgetT j (σ₁⁻¹) ^ j ∧
      (N₁ : ℝ) ^ j * realDistanceToIntegers
          ((r : ℝ) * ((r₀ : ℝ) * θ)) ≤
        (recurrenceBudgetR j (σ₁⁻¹) +
          recurrenceBudgetT j (σ₁⁻¹) ^ j) * ε₁ :=
    one_coordinate_recurrence_one hj hN₁
      hσ₁ hσ₁half hε₁ hε₁small hgoodSecond'
  rcases hr₁exists with ⟨r₁, hr₁pos, hr₁C, hr₁err⟩
  have hinv₁ : σ₁⁻¹ = 4 * A * z := by
    dsimp [σ₁, z]
    exact inv_quarter_product σ A hσ hApos
  have hr₁C' : (r₁ : ℝ) ≤ C := by
    simpa [C, hinv₁] using hr₁C
  have hr₁err' : (N₁ : ℝ) ^ j * realDistanceToIntegers
      ((r₁ : ℝ) * ((r₀ : ℝ) * θ)) ≤ C * ε₁ := by
    simpa [C, hinv₁] using hr₁err
  have hB : B = A * C := by
    dsimp [B, C, A, z]
    rw [productRecurrenceB_eval]
  let r : ℕ := r₀ * r₁
  refine ⟨r, Nat.mul_pos hr₀pos hr₁pos, ?_, ?_⟩
  · rw [show productRecurrenceB j σ⁻¹ = B by rfl, hB]
    dsimp [r]
    simpa [mul_comm] using mul_le_mul hr₀A hr₁C' (by positivity) hA0
  · have hN₂powpos : 0 < (N₂ : ℝ) ^ j := by positivity
    have hmult : ((N₁ : ℝ) * (N₂ : ℝ)) ^ j *
        realDistanceToIntegers ((r : ℝ) * θ) ≤ B * ε := by
      have hscaled := mul_le_mul_of_nonneg_left hr₁err'
        (show 0 ≤ (N₂ : ℝ) ^ j by positivity)
      rw [hB]
      dsimp [ε₁] at hscaled
      have hcancel : (N₂ : ℝ) ^ j *
          (C * (A * ε / (N₂ : ℝ) ^ j)) = A * C * ε := by
        field_simp [ne_of_gt hN₂powpos]
      rw [hcancel] at hscaled
      simpa [r, mul_pow, mul_comm, mul_left_comm, mul_assoc] using hscaled
    have hdenpos : 0 < ((N₁ : ℝ) * (N₂ : ℝ)) ^ j := by positivity
    apply (le_div_iff₀ hdenpos).2
    simpa [B, z, mul_comm] using hmult

/-- Recurrence on many product pairs, including both short-coordinate
branches, with the exact budgets of blueprint `lpi:product-recurrence`. -/
theorem productRecurrence
    {j N₁ N₂ : ℕ} (hj : 1 ≤ j) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    {σ ε θ : ℝ} (hσ : 0 < σ) (hσhalf : σ < 1 / 2)
    (hε : 0 ≤ ε)
    (hεupper : ε ≤
      1 / (256 * σ⁻¹ * productRecurrenceA j σ⁻¹ ^ 2))
    (hgood : σ * (N₁ : ℝ) * (N₂ : ℝ) ≤
      ((((Finset.range N₁ ×ˢ Finset.range N₂).filter
        (fun p : ℕ × ℕ => realDistanceToIntegers
          (θ * (((p.1 + 1 : ℕ) : ℝ) * ((p.2 + 1 : ℕ) : ℝ)) ^ j) ≤
            ε)).card : ℕ) : ℝ)) :
    ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ productRecurrenceB j σ⁻¹ ∧
      realDistanceToIntegers ((r : ℝ) * θ) ≤
        productRecurrenceB j σ⁻¹ * ε /
          (((N₁ : ℝ) * (N₂ : ℝ)) ^ j) := by
  classical
  let z : ℝ := σ⁻¹
  let A : ℝ := productRecurrenceA j z
  let G : ℕ → ℕ → Prop := fun q a =>
    realDistanceToIntegers
      (θ * (((q + 1 : ℕ) : ℝ) * ((a + 1 : ℕ) : ℝ)) ^ j) ≤ ε
  let S : Finset ℕ := (Finset.range N₁).filter (fun q =>
    σ / 2 * (N₂ : ℝ) ≤
      (((Finset.range N₂).filter (G q)).card : ℝ))
  have hz2 : 2 ≤ z := by
    dsimp [z]
    rw [← one_div]
    exact (le_div_iff₀ hσ).2 (by nlinarith [hσhalf])
  have hA : 1 ≤ A := by
    exact productRecurrenceA_ge_one j hj z hz2
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hA0 : 0 ≤ A := hApos.le
  have hA2 : 1 ≤ A ^ 2 := by
    simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hA 2)
  have hεA : ε ≤ σ / (256 * A ^ 2) := by
    calc
      ε ≤ 1 / (256 * σ⁻¹ * productRecurrenceA j σ⁻¹ ^ 2) := hεupper
      _ = σ / (256 * A ^ 2) := by
        dsimp [A, z]
        field_simp [ne_of_gt hσ]
  have hεsigma : ε ≤ σ / 256 := by
    exact hεA.trans
      (div_le_div_of_nonneg_left hσ.le (by norm_num)
        (by nlinarith [hA2]))
  have hrowEpsilon : ε ≤ (σ / 2) / 64 := by
    linarith
  have hrows : σ / 2 * (N₁ : ℝ) ≤ (S.card : ℝ) := by
    have h := many_dense_rows hN₂ hσ G (by simpa [G] using hgood)
    simpa [S, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hrow (q : ℕ) (hq : q ∈ S) :
      ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ A ∧
        (N₂ : ℝ) ^ j * realDistanceToIntegers
            ((r : ℝ) * θ * ((q + 1 : ℕ) : ℝ) ^ j) ≤ A * ε := by
    have hqdense := (Finset.mem_filter.mp hq).2
    have hqpos : 1 ≤ q + 1 := by omega
    have hgoodq : σ / 2 * (N₂ : ℝ) ≤
        (((Finset.range N₂).filter (fun a : ℕ =>
          realDistanceToIntegers
            (θ * (((q + 1 : ℕ) : ℝ) ^ j) *
              ((a + 1 : ℕ) : ℝ) ^ j) ≤ ε)).card : ℝ) := by
      simpa [G, mul_pow, mul_assoc] using hqdense
    have hw := one_coordinate_recurrence hj hN₂ hqpos
      (show 0 < σ / 2 by positivity)
      (show σ / 2 < 1 / 2 by linarith)
      hε hrowEpsilon hgoodq
    simpa [A, z, productRecurrenceA_eval, inv_half σ hσ] using hw
  let rmap : ℕ → ℕ := fun q =>
    if hq : q ∈ S then Classical.choose (hrow q hq) else 1
  have hrmapSpec (q : ℕ) (hq : q ∈ S) :
      1 ≤ rmap q ∧ (rmap q : ℝ) ≤ A ∧
        (N₂ : ℝ) ^ j * realDistanceToIntegers
            ((rmap q : ℝ) * θ * ((q + 1 : ℕ) : ℝ) ^ j) ≤ A * ε := by
    dsimp [rmap]
    rw [dif_pos hq]
    exact Classical.choose_spec (hrow q hq)
  have hr₀exists : ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ A ∧
      (S.card : ℝ) / A ≤
        ((S.filter fun q => rmap q = r).card : ℝ) :=
    exists_large_denominator_fiber S rmap A hA
      (fun q hq => (hrmapSpec q hq).1)
      (fun q hq => (hrmapSpec q hq).2.1)
  rcases hr₀exists with ⟨r₀, hr₀pos, hr₀A, hr₀fiber⟩
  let S₀ : Finset ℕ := S.filter (fun q => rmap q = r₀)
  let σ₁ : ℝ := σ / (4 * A)
  let ε₁ : ℝ := A * ε / (N₂ : ℝ) ^ j
  have hS₀dense : σ₁ * (N₁ : ℝ) ≤ (S₀.card : ℝ) := by
    have hquarter : σ * (N₁ : ℝ) / 4 ≤ σ * (N₁ : ℝ) / 2 := by
      have hprod : 0 ≤ σ * (N₁ : ℝ) :=
        mul_nonneg hσ.le (by positivity)
      linarith
    have hrows' : σ * (N₁ : ℝ) / 2 ≤ (S.card : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hrows
    calc
      σ₁ * (N₁ : ℝ) = (σ * (N₁ : ℝ) / 4) / A := by
        dsimp [σ₁]
        field_simp [ne_of_gt hApos]
      _ ≤ (σ * (N₁ : ℝ) / 2) / A :=
        div_le_div_of_nonneg_right hquarter hA0
      _ ≤ (S.card : ℝ) / A :=
        div_le_div_of_nonneg_right hrows' hA0
      _ ≤ (S₀.card : ℝ) := by simpa [S₀] using hr₀fiber
  have hN₂powpos : 0 < (N₂ : ℝ) ^ j := by
    positivity
  have hS₀sub : S₀ ⊆ (Finset.range N₁).filter (fun q : ℕ =>
      realDistanceToIntegers
        (((r₀ : ℝ) * θ) * (1 : ℝ) ^ j *
          ((q + 1 : ℕ) : ℝ) ^ j) ≤ ε₁) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqS, hqr⟩
    have hqRange := (Finset.mem_filter.mp hqS).1
    have herr := (hrmapSpec q hqS).2.2
    rw [hqr] at herr
    apply Finset.mem_filter.mpr
    refine ⟨hqRange, ?_⟩
    have hdiv : realDistanceToIntegers
        ((r₀ : ℝ) * θ * ((q + 1 : ℕ) : ℝ) ^ j) ≤ ε₁ := by
      apply (le_div_iff₀ hN₂powpos).2
      simpa [ε₁, mul_comm, mul_left_comm, mul_assoc] using herr
    simpa using hdiv
  have hgoodSecond : σ₁ * (N₁ : ℝ) ≤
      (((Finset.range N₁).filter (fun q : ℕ =>
        realDistanceToIntegers
          (((r₀ : ℝ) * θ) * (1 : ℝ) ^ j *
            ((q + 1 : ℕ) : ℝ) ^ j) ≤ ε₁)).card : ℝ) := by
    have hcardNat := Finset.card_le_card hS₀sub
    have hcardReal : (S₀.card : ℝ) ≤
        (((Finset.range N₁).filter (fun q : ℕ =>
          realDistanceToIntegers
            (((r₀ : ℝ) * θ) * (1 : ℝ) ^ j *
              ((q + 1 : ℕ) : ℝ) ^ j) ≤ ε₁)).card : ℝ) := by
      exact_mod_cast hcardNat
    exact hS₀dense.trans hcardReal
  apply product_recurrence_finish hj hN₁ hN₂ hσ hσhalf hε
      (by simpa [A, z] using hεA) hr₀pos
      (by simpa [A, z] using hr₀A)
  simpa [σ₁, ε₁, A, z] using hgoodSecond

end FractionalPrimes.Literature.Polynomial
