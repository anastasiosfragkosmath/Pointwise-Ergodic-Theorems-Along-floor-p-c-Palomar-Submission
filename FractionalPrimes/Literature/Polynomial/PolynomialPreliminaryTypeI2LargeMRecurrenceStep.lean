module

public import FractionalPrimes.Literature.Polynomial.PolynomialProductRecurrenceOneIndexed
public import FractionalPrimes.Literature.Polynomial.PolynomialPreliminaryTypeI2LargeMDescent
public import FractionalPrimes.Literature.Polynomial.PolynomialPreliminaryTypeI2LargeMAssembly

/-!
# One degree of the large-M Type-I₂ descent

This module isolates the exact handoff from the direction-wise leading
coefficient bounds to the two-coordinate product recurrence theorem.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Hyperbola

private theorem recurrenceStep_natPolynomialEval_nonneg
    (p : Polynomial ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)

/-- Every one-indexed point of an inverse-progression witness lies in the
original hyperbola strip.  The base is shifted back by one spacing so that
the polynomial index runs through `1,…,N` exactly. -/
theorem TypeI2LargeMInverseProgressionData.oneIndexed_strip
    {g : HyperbolaGeometricData} {d : ℕ} {δ : ℝ} {q₀ : ℕ}
    {P : Polynomial ℝ} {a q : ℕ}
    (D : TypeI2LargeMInverseProgressionData g d δ q₀ P a q) :
    ∀ k ∈ Finset.Icc 1 D.N,
      g.X <
          (((D.z.1 - (q₀ : ℤ) * (q : ℤ) : ℤ) : ℝ) +
              (((q₀ : ℤ) * (q : ℤ) : ℤ) : ℝ) * (k : ℝ)) *
            (((D.z.2 + (q₀ : ℤ) * (a : ℤ) : ℤ) : ℝ) -
              (((q₀ : ℤ) * (a : ℤ) : ℤ) : ℝ) * (k : ℝ)) ∧
        (((D.z.1 - (q₀ : ℤ) * (q : ℤ) : ℤ) : ℝ) +
              (((q₀ : ℤ) * (q : ℤ) : ℤ) : ℝ) * (k : ℝ)) *
            (((D.z.2 + (q₀ : ℤ) * (a : ℤ) : ℤ) : ℝ) -
              (((q₀ : ℤ) * (a : ℤ) : ℤ) : ℝ) * (k : ℝ)) ≤
          g.X + g.H := by
  classical
  intro k hk
  have hkBounds := Finset.mem_Icc.mp hk
  let j : Fin D.N := ⟨k - 1, by omega⟩
  have hp :
      (D.z.1 + ((j.val : ℕ) : ℤ) * ((q₀ : ℤ) * (q : ℤ)),
        D.z.2 - ((j.val : ℕ) : ℤ) * ((q₀ : ℤ) * (a : ℤ))) ∈
        latticeProgression D.z ((q₀ : ℤ) * (q : ℤ))
          ((q₀ : ℤ) * (a : ℤ)) D.N D.hN := by
    unfold latticeProgression
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ j, rfl⟩
  have hlat := D.progression_subset_lattice (by simpa using hp)
  dsimp [HyperbolaGeometricData.lattice, hyperbolaLatticeSet] at hlat
  rcases hlat with ⟨_hJ, hlow, hupp⟩
  have hkSubCast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hkBounds.1]
    norm_num
  constructor
  · convert hlow using 1 <;> dsimp [j] <;> push_cast <;>
      rw [hkSubCast] <;> ring
  · convert hupp using 1 <;> dsimp [j] <;> push_cast <;>
      rw [hkSubCast] <;> ring

/-- The Type-I₂ progression parameter is in the domain required by the
inverse and recurrence budget lemmas. -/
theorem typeI2T_ge_two (x : ℝ) (hx : 1 ≤ x) :
    2 ≤ typeI2T x := by
  rw [typeI2T_eval]
  have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
  norm_num [typeI2BZeroValue, typeI2GValue, typeI2CPointValue,
    typeI2CLineValue, typeI2EValue, typeI2DValue, typeI2KZeroValue]
  nlinarith

/-- The initial denominator budget is at least one on the source domain. -/
theorem typeI2B_ge_one (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ typeI2B d x := by
  rw [typeI2B_eval]
  exact inverseBoundG_ge_one (2 * d) (typeI2T x) (typeI2T_ge_two x hx)

/-- The reciprocal-density budget `z` is strictly larger than two. -/
theorem typeI2Zeta_gt_two (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    2 < typeI2Zeta d x := by
  rw [typeI2Zeta_eval]
  have hB := typeI2B_ge_one d x hx
  have hx6 : 1 ≤ x ^ 6 := one_le_pow₀ hx
  have hprod : 1 ≤ typeI2B d x * x ^ 6 := by
    simpa only [one_mul] using
      (mul_le_mul hB hx6 (by norm_num) (by linarith))
  have hconstant : (2 : ℝ) <
      16 * (typeI2BZeroValue : ℝ) ^ 2 * (typeI2GValue : ℝ) ^ 2 := by
    norm_num [typeI2BZeroValue, typeI2GValue, typeI2CPointValue,
      typeI2CLineValue, typeI2EValue, typeI2DValue, typeI2KZeroValue]
  calc
    (2 : ℝ) <
        16 * (typeI2BZeroValue : ℝ) ^ 2 * (typeI2GValue : ℝ) ^ 2 :=
      hconstant
    _ = (16 * (typeI2BZeroValue : ℝ) ^ 2 *
          (typeI2GValue : ℝ) ^ 2) * 1 := by ring
    _ ≤ (16 * (typeI2BZeroValue : ℝ) ^ 2 *
          (typeI2GValue : ℝ) ^ 2) * (typeI2B d x * x ^ 6) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 16 * typeI2B d x * (typeI2BZeroValue : ℝ) ^ 2 *
          (typeI2GValue : ℝ) ^ 2 * x ^ 6 := by ring

theorem typeI2Zeta_ge_two (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    2 ≤ typeI2Zeta d x :=
  (typeI2Zeta_gt_two d x hx).le

/-- The density selected in the fixed-denominator rectangle is exactly the
reciprocal of the approved Type-I₂ budget `z`. -/
theorem typeI2LargeMSigma_eq_inv_typeI2Zeta
    (d : ℕ) (delta : ℝ) (hdelta : 0 < delta) (hdeltaLe : delta ≤ 1) :
    typeI2LargeMSigma d delta = (typeI2Zeta d delta⁻¹)⁻¹ := by
  have hx : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta).2 hdeltaLe
  have hBpos : 0 < typeI2B d delta⁻¹ :=
    lt_of_lt_of_le zero_lt_one (typeI2B_ge_one d delta⁻¹ hx)
  rw [typeI2Zeta_eval]
  dsimp [typeI2LargeMSigma, typeI2LargeMKappa]
  norm_num [typeI2BZeroValue, typeI2GValue, typeI2CPointValue,
    typeI2CLineValue, typeI2EValue, typeI2DValue, typeI2KZeroValue]
  field_simp [ne_of_gt hdelta, ne_of_gt hBpos]
  ring

theorem typeI2LargeMSigma_pos
    (d : ℕ) (delta : ℝ) (hdelta : 0 < delta) (hdeltaLe : delta ≤ 1) :
    0 < typeI2LargeMSigma d delta := by
  rw [typeI2LargeMSigma_eq_inv_typeI2Zeta d delta hdelta hdeltaLe]
  apply inv_pos.mpr
  exact lt_trans (by norm_num) <|
    typeI2Zeta_gt_two d delta⁻¹ ((one_le_inv₀ hdelta).2 hdeltaLe)

theorem typeI2LargeMSigma_lt_half
    (d : ℕ) (delta : ℝ) (hdelta : 0 < delta) (hdeltaLe : delta ≤ 1) :
    typeI2LargeMSigma d delta < 1 / 2 := by
  rw [typeI2LargeMSigma_eq_inv_typeI2Zeta d delta hdelta hdeltaLe,
    inv_eq_one_div]
  have hz := typeI2Zeta_gt_two d delta⁻¹
    ((one_le_inv₀ hdelta).2 hdeltaLe)
  have hzpos : 0 < typeI2Zeta d delta⁻¹ := lt_trans (by norm_num) hz
  apply (div_lt_div_iff₀ hzpos (by norm_num)).2
  nlinarith

/-- The aggregate `A` budget dominates each degree appearing in the descent. -/
theorem productRecurrenceA_le_typeI2A
    (d l : ℕ) (hl : 1 ≤ l) (hld : l ≤ d)
    (x : ℝ) (hx : 1 ≤ x) :
    productRecurrenceA l (typeI2Zeta d x) ≤ typeI2A d x := by
  rw [typeI2A_eval]
  have hz : 2 ≤ typeI2Zeta d x := typeI2Zeta_ge_two d x hx
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 d) :
      0 ≤ productRecurrenceA j (typeI2Zeta d x) := by
    have hjone : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact le_trans zero_le_one (productRecurrenceA_ge_one j hjone _ hz)
  have hsum := Finset.single_le_sum hterm
    (show l ∈ Finset.Icc 1 d by simp [hl, hld])
  linarith

/-- The aggregate `R` budget dominates each product-recurrence denominator. -/
theorem productRecurrenceB_le_typeI2R
    (d l : ℕ) (hl : 1 ≤ l) (hld : l ≤ d)
    (x : ℝ) (hx : 1 ≤ x) :
    productRecurrenceB l (typeI2Zeta d x) ≤ typeI2R d x := by
  rw [typeI2R_eval]
  have hz : 2 ≤ typeI2Zeta d x := typeI2Zeta_ge_two d x hx
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 d) :
      0 ≤ productRecurrenceB j (typeI2Zeta d x) := by
    have hjone : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact le_trans zero_le_one (productRecurrenceB_ge_one j hjone _ hz)
  have hsum := Finset.single_le_sum hterm
    (show l ∈ Finset.Icc 1 d by simp [hl, hld])
  linarith

theorem typeI2A_ge_one (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ typeI2A d x := by
  rw [typeI2A_eval]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro j hj
  have hjone : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  exact le_trans zero_le_one <|
    productRecurrenceA_ge_one j hjone _ (typeI2Zeta_ge_two d x hx)

theorem typeI2R_ge_one (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ typeI2R d x := by
  rw [typeI2R_eval]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro j hj
  have hjone : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  exact le_trans zero_le_one <|
    productRecurrenceB_ge_one j hjone _ (typeI2Zeta_ge_two d x hx)

theorem typeI2C_ge_one (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    1 ≤ typeI2C d x := by
  rw [typeI2C_eval]
  have ht0 : 0 ≤ typeI2T x :=
    recurrenceStep_natPolynomialEval_nonneg typeI2TPolynomial x hx
  have hterm : 0 ≤ (d : ℝ) * (2592 * typeI2T x ^ 2) ^ d := by
    positivity
  linarith

/-- The existing source budget `C` absorbs the residue-progression factor
`q₀^(2l)`.  This is the standalone correction required because the checked
ordinary pigeonhole theorem has spacing `q₀(q,-a)`. -/
theorem typeI2_residueSpacingPower_le_C
    (d l q₀ : ℕ) (hl : 1 ≤ l) (hld : l ≤ d)
    (x : ℝ) (hx : 1 ≤ x) (hq₀ : (q₀ : ℝ) ≤ x) :
    (q₀ : ℝ) ^ (2 * l) ≤ typeI2C d x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hq0 : 0 ≤ (q₀ : ℝ) := Nat.cast_nonneg q₀
  have hqpow : (q₀ : ℝ) ^ (2 * l) ≤ x ^ (2 * l) :=
    pow_le_pow_left₀ hq0 hq₀ (2 * l)
  have hxpow : x ^ (2 * l) ≤ x ^ (2 * d) :=
    pow_le_pow_right₀ hx (Nat.mul_le_mul_left 2 hld)
  have hxCube : x ≤ x ^ 3 := by
    have hxSq : 1 ≤ x ^ 2 := one_le_pow₀ hx
    calc
      x = x * 1 := by ring
      _ ≤ x * x ^ 2 := mul_le_mul_of_nonneg_left hxSq hx0
      _ = x ^ 3 := by ring
  have hxT : x ≤ typeI2T x := by
    rw [typeI2T_eval]
    have hcoef : (1 : ℝ) ≤
        4 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) := by
      norm_num [typeI2BZeroValue, typeI2GValue, typeI2CPointValue,
        typeI2CLineValue, typeI2EValue, typeI2DValue, typeI2KZeroValue]
    calc
      x ≤ x ^ 3 := hxCube
      _ = 1 * x ^ 3 := by ring
      _ ≤ (4 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ)) *
          x ^ 3 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hx0 3)
  have hxSqT : x ^ 2 ≤ typeI2T x ^ 2 :=
    pow_le_pow_left₀ hx0 hxT 2
  have hbase : x ^ 2 ≤ 2592 * typeI2T x ^ 2 := by
    calc
      x ^ 2 ≤ typeI2T x ^ 2 := hxSqT
      _ ≤ 2592 * typeI2T x ^ 2 := by
        have htSq : 0 ≤ typeI2T x ^ 2 := sq_nonneg _
        nlinarith
  have hpower : x ^ (2 * d) ≤ (2592 * typeI2T x ^ 2) ^ d := by
    calc
      x ^ (2 * d) = (x ^ 2) ^ d := by rw [pow_mul]
      _ ≤ (2592 * typeI2T x ^ 2) ^ d :=
        pow_le_pow_left₀ (sq_nonneg x) hbase d
  rw [typeI2C_eval]
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (hl.trans hld)
  have hterm : 0 ≤ (2592 * typeI2T x ^ 2) ^ d := by positivity
  calc
    (q₀ : ℝ) ^ (2 * l) ≤ x ^ (2 * l) := hqpow
    _ ≤ x ^ (2 * d) := hxpow
    _ ≤ (2592 * typeI2T x ^ 2) ^ d := hpower
    _ ≤ 1 + (d : ℝ) * (2592 * typeI2T x ^ 2) ^ d := by
      nlinarith

/-- Every recursive denominator/error budget is at least one. -/
theorem typeI2W_ge_one
    (d k : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ typeI2W d k x := by
  induction k with
  | zero => simpa using typeI2B_ge_one d x hx
  | succ k ih =>
      rw [typeI2W_succ_eval]
      have hpow : (1 : ℝ) ≤ 16 ^ d + 1 := by
        have hnonneg : 0 ≤ (16 : ℝ) ^ d := by positivity
        linarith
      have hR := typeI2R_ge_one d x hx
      have hC := typeI2C_ge_one d x (le_trans zero_le_one hx)
      have hWsq : 1 ≤ typeI2W d k x ^ 2 := one_le_pow₀ ih
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hpow hR) hC) hWsq

/-- The recursive Type-I₂ budgets increase with the descent counter. -/
theorem typeI2W_monotone
    (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    Monotone (fun k => typeI2W d k x) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [typeI2W_succ_eval]
  have hWone := typeI2W_ge_one d k x hx
  have hWsq : typeI2W d k x ≤ typeI2W d k x ^ 2 := by nlinarith
  have hpow : (1 : ℝ) ≤ 16 ^ d + 1 := by
    have hnonneg : 0 ≤ (16 : ℝ) ^ d := by positivity
    linarith
  have hfactor : 1 ≤
      (16 ^ d + 1 : ℝ) * typeI2R d x * typeI2C d x :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hpow (typeI2R_ge_one d x hx))
      (typeI2C_ge_one d x (le_trans zero_le_one hx))
  calc
    typeI2W d k x ≤ typeI2W d k x ^ 2 := hWsq
    _ = 1 * typeI2W d k x ^ 2 := by ring
    _ ≤ ((16 ^ d + 1 : ℝ) * typeI2R d x * typeI2C d x) *
        typeI2W d k x ^ 2 :=
      mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)

theorem typeI2W_le_final
    (d k : ℕ) (hk : k ≤ d) (x : ℝ) (hx : 1 ≤ x) :
    typeI2W d k x ≤ typeI2W d d x :=
  typeI2W_monotone d x hx hk

/-- The approved preliminary Type-I₂ budget `J_d` absorbs the final
monomial-to-binomial loss `E_d W_d`. -/
theorem inverseBoundE_mul_typeI2W_le_typeI2J
    (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    (inverseBoundEValue d : ℝ) * typeI2W d d x ≤ typeI2J d x := by
  have hI : 0 ≤ inverseBoundI d (x ^ 2) := by
    exact recurrenceStep_natPolynomialEval_nonneg
      (inverseBoundIPolynomial d) (x ^ 2) (sq_nonneg x)
  have hW : 0 ≤ typeI2W d d x :=
    le_trans zero_le_one (typeI2W_ge_one d d x hx)
  have hE : 0 ≤ (inverseBoundEValue d : ℝ) := by
    exact_mod_cast (le_trans (by omega : 0 ≤ 1) (inverseBoundE_ge_one d))
  rw [typeI2J_eval]
  apply mul_le_mul_of_nonneg_left _ hE
  nlinarith [sq_nonneg (inverseBoundI d (x ^ 2)),
    sq_nonneg (typeI2CapitalZ d x)]

/-- One source-exact recurrence step.  A dense positive direction rectangle
carrying the normalized leading-coefficient error yields a new multiplier
with denominator `(L²N₁N₂)^l`. -/
theorem preliminaryTypeI2LargeM_oneDegreeRecurrence
    {l N₁ N₂ : ℕ} (hl : 1 ≤ l) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    {sigma L C W theta : ℝ}
    (hsigma : 0 < sigma) (hsigmaHalf : sigma < 1 / 2)
    (hL : 0 < L) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hsmall : C * W ^ 2 / L ^ (2 * l) ≤
      1 / (256 * sigma⁻¹ * productRecurrenceA l sigma⁻¹ ^ 2))
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ Finset.Icc 1 N₁ ×ˢ Finset.Icc 1 N₂)
    (hdensity : sigma * (N₁ : ℝ) * (N₂ : ℝ) ≤ (S.card : ℝ))
    (hdirection : ∀ p ∈ S,
      L ^ (2 * l) * realDistanceToIntegers
        (theta * (((p.1 : ℝ) * (p.2 : ℝ)) ^ l)) ≤ C * W ^ 2) :
    ∃ w : ℕ, 1 ≤ w ∧
      (w : ℝ) ≤ productRecurrenceB l sigma⁻¹ ∧
      realDistanceToIntegers ((w : ℝ) * theta) ≤
        productRecurrenceB l sigma⁻¹ * C * W ^ 2 /
          ((L ^ 2 * (N₁ : ℝ) * (N₂ : ℝ)) ^ l) := by
  have hepsilon : 0 ≤ C * W ^ 2 / L ^ (2 * l) := by positivity
  have hgood : ∀ p ∈ S,
      realDistanceToIntegers
        (theta * (((p.1 : ℝ) * (p.2 : ℝ)) ^ l)) ≤
          C * W ^ 2 / L ^ (2 * l) := by
    intro p hp
    apply (le_div_iff₀ (pow_pos hL (2 * l))).2
    simpa [mul_comm] using hdirection p hp
  obtain ⟨w, hw, hwB, hwerror⟩ := productRecurrence_oneIndexed
    hl hN₁ hN₂ hsigma hsigmaHalf hepsilon hsmall S hS hdensity hgood
  refine ⟨w, hw, hwB, ?_⟩
  calc
    realDistanceToIntegers ((w : ℝ) * theta) ≤
        productRecurrenceB l sigma⁻¹ * (C * W ^ 2 / L ^ (2 * l)) /
          (((N₁ : ℝ) * (N₂ : ℝ)) ^ l) := hwerror
    _ = productRecurrenceB l sigma⁻¹ * C * W ^ 2 /
          ((L ^ 2 * (N₁ : ℝ) * (N₂ : ℝ)) ^ l) := by
      have hN₁pos : 0 < (N₁ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₁)
      have hN₂pos : 0 < (N₂ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₂)
      field_simp [ne_of_gt hL, ne_of_gt hN₁pos, ne_of_gt hN₂pos]
      ring

/-- The exact small-error inequality needed to invoke product recurrence.
The two dominance hypotheses are separated because they are the finite-sum
and recursive-budget invariants proved independently in the descent. -/
theorem preliminaryTypeI2LargeM_recurrenceEpsilon_le
    (d l step : ℕ) (hl : 1 ≤ l)
    (x L : ℝ) (hx : 0 ≤ x)
    (hLlarge : typeI2CapitalZ d x < L)
    (hzpos : 0 < typeI2Zeta d x)
    (hAlpos : 0 < productRecurrenceA l (typeI2Zeta d x))
    (hAl : productRecurrenceA l (typeI2Zeta d x) ≤ typeI2A d x)
    (hW : typeI2W d step x ≤ typeI2W d d x) :
    typeI2C d x * typeI2W d step x ^ 2 / L ^ (2 * l) ≤
      1 / (256 * typeI2Zeta d x *
        productRecurrenceA l (typeI2Zeta d x) ^ 2) := by
  have ht0 : 0 ≤ typeI2T x :=
    recurrenceStep_natPolynomialEval_nonneg typeI2TPolynomial x hx
  have hA0 : 0 ≤ typeI2A d x :=
    recurrenceStep_natPolynomialEval_nonneg (typeI2APolynomial d) x hx
  have hC0 : 0 ≤ typeI2C d x :=
    recurrenceStep_natPolynomialEval_nonneg (typeI2CPolynomial d) x hx
  have hW0 : 0 ≤ typeI2W d step x :=
    recurrenceStep_natPolynomialEval_nonneg (typeI2WPolynomial d step) x hx
  have hWd0 : 0 ≤ typeI2W d d x :=
    recurrenceStep_natPolynomialEval_nonneg (typeI2WPolynomial d d) x hx
  have hZone : 1 ≤ typeI2CapitalZ d x :=
    typeI2CapitalZ_ge_one d x hx
  have hLone : 1 ≤ L := hZone.trans hLlarge.le
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hAsq : productRecurrenceA l (typeI2Zeta d x) ^ 2 ≤
      typeI2A d x ^ 2 :=
    (sq_le_sq₀ hAlpos.le hA0).2 hAl
  have hWsq : typeI2W d step x ^ 2 ≤ typeI2W d d x ^ 2 :=
    (sq_le_sq₀ hW0 hWd0).2 hW
  have hpair :
      productRecurrenceA l (typeI2Zeta d x) ^ 2 *
          typeI2W d step x ^ 2 ≤
        typeI2A d x ^ 2 * typeI2W d d x ^ 2 :=
    mul_le_mul hAsq hWsq (sq_nonneg _) (sq_nonneg _)
  have hdominated :
      256 * typeI2Zeta d x *
          productRecurrenceA l (typeI2Zeta d x) ^ 2 *
          typeI2C d x * typeI2W d step x ^ 2 ≤
        256 * typeI2Zeta d x * typeI2A d x ^ 2 *
          typeI2C d x * typeI2W d d x ^ 2 := by
    have hfactor : 0 ≤ 256 * typeI2Zeta d x * typeI2C d x := by
      positivity
    calc
      256 * typeI2Zeta d x *
            productRecurrenceA l (typeI2Zeta d x) ^ 2 *
            typeI2C d x * typeI2W d step x ^ 2 =
          (256 * typeI2Zeta d x * typeI2C d x) *
            (productRecurrenceA l (typeI2Zeta d x) ^ 2 *
              typeI2W d step x ^ 2) := by ring
      _ ≤ (256 * typeI2Zeta d x * typeI2C d x) *
            (typeI2A d x ^ 2 * typeI2W d d x ^ 2) :=
        mul_le_mul_of_nonneg_left hpair hfactor
      _ = 256 * typeI2Zeta d x * typeI2A d x ^ 2 *
            typeI2C d x * typeI2W d d x ^ 2 := by ring
  have hthreshold :
      256 * typeI2Zeta d x * typeI2A d x ^ 2 *
          typeI2C d x * typeI2W d d x ^ 2 ≤
        typeI2CapitalZ d x := by
    rw [typeI2CapitalZ_eval]
    linarith
  have hpower : L ≤ L ^ (2 * l) := by
    have hexponent : 1 ≤ 2 * l := by omega
    simpa using pow_le_pow_right₀ hLone hexponent
  have hnumerator :
      256 * typeI2Zeta d x *
          productRecurrenceA l (typeI2Zeta d x) ^ 2 *
          typeI2C d x * typeI2W d step x ^ 2 ≤
        L ^ (2 * l) :=
    hdominated.trans (hthreshold.trans (hLlarge.le.trans hpower))
  have hdenpos : 0 < 256 * typeI2Zeta d x *
      productRecurrenceA l (typeI2Zeta d x) ^ 2 := by positivity
  apply (div_le_iff₀ (pow_pos hLpos (2 * l))).2
  rw [show (1 : ℝ) /
      (256 * typeI2Zeta d x *
        productRecurrenceA l (typeI2Zeta d x) ^ 2) * L ^ (2 * l) =
      L ^ (2 * l) /
        (256 * typeI2Zeta d x *
          productRecurrenceA l (typeI2Zeta d x) ^ 2) by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring]
  apply (le_div_iff₀ hdenpos).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hnumerator

/-- The source budget definitions discharge both dominance hypotheses in the
small-error estimate. -/
theorem preliminaryTypeI2LargeM_recurrenceEpsilon_le_typeI2Budgets
    (d l step : ℕ) (hl : 1 ≤ l) (hld : l ≤ d) (hstep : step ≤ d)
    (x L : ℝ) (hx : 1 ≤ x)
    (hLlarge : typeI2CapitalZ d x < L) :
    typeI2C d x * typeI2W d step x ^ 2 / L ^ (2 * l) ≤
      1 / (256 * typeI2Zeta d x *
        productRecurrenceA l (typeI2Zeta d x) ^ 2) := by
  apply preliminaryTypeI2LargeM_recurrenceEpsilon_le
    d l step hl x L (le_trans zero_le_one hx) hLlarge
  · exact lt_trans (by norm_num) (typeI2Zeta_gt_two d x hx)
  · exact lt_of_lt_of_le zero_lt_one <|
      productRecurrenceA_ge_one l hl _ (typeI2Zeta_ge_two d x hx)
  · exact productRecurrenceA_le_typeI2A d l hl hld x hx
  · exact typeI2W_le_final d step hstep x hx

/-- The same small-error estimate written in the selected density parameter
`sigma`, exactly as required by `productRecurrence`. -/
theorem preliminaryTypeI2LargeM_recurrenceEpsilon_le_sigma
    (d l step : ℕ) (hl : 1 ≤ l) (hld : l ≤ d) (hstep : step ≤ d)
    (delta L : ℝ) (hdelta : 0 < delta) (hdeltaLe : delta ≤ 1)
    (hLlarge : typeI2CapitalZ d delta⁻¹ < L) :
    typeI2C d delta⁻¹ * typeI2W d step delta⁻¹ ^ 2 / L ^ (2 * l) ≤
      1 / (256 * (typeI2LargeMSigma d delta)⁻¹ *
        productRecurrenceA l (typeI2LargeMSigma d delta)⁻¹ ^ 2) := by
  rw [typeI2LargeMSigma_eq_inv_typeI2Zeta d delta hdelta hdeltaLe,
    inv_inv]
  exact preliminaryTypeI2LargeM_recurrenceEpsilon_le_typeI2Budgets
    d l step hl hld hstep delta⁻¹ L
      ((one_le_inv₀ hdelta).2 hdeltaLe) hLlarge

/-- A complete product-recurrence update at one degree, with every local
budget replaced by the approved aggregate Type-I₂ budgets. -/
theorem preliminaryTypeI2LargeM_oneDegreeRecurrence_typeI2
    {d l step N₁ N₂ : ℕ}
    (hl : 1 ≤ l) (hld : l ≤ d) (hstep : step ≤ d)
    (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (delta L theta : ℝ) (hdelta : 0 < delta) (hdeltaLe : delta ≤ 1)
    (hLlarge : typeI2CapitalZ d delta⁻¹ < L)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ Finset.Icc 1 N₁ ×ˢ Finset.Icc 1 N₂)
    (hdensity :
      2 * typeI2LargeMSigma d delta * (N₁ : ℝ) * (N₂ : ℝ) ≤
        (S.card : ℝ))
    (hdirection : ∀ p ∈ S,
      L ^ (2 * l) * realDistanceToIntegers
        (theta * (((p.1 : ℝ) * (p.2 : ℝ)) ^ l)) ≤
          typeI2C d delta⁻¹ * typeI2W d step delta⁻¹ ^ 2) :
    ∃ w : ℕ, 1 ≤ w ∧
      (w : ℝ) ≤ typeI2R d delta⁻¹ ∧
      realDistanceToIntegers ((w : ℝ) * theta) ≤
        typeI2R d delta⁻¹ * typeI2C d delta⁻¹ *
          typeI2W d step delta⁻¹ ^ 2 /
            ((L ^ 2 * (N₁ : ℝ) * (N₂ : ℝ)) ^ l) := by
  let sigma : ℝ := typeI2LargeMSigma d delta
  have hsigma : 0 < sigma := by
    simpa [sigma] using typeI2LargeMSigma_pos d delta hdelta hdeltaLe
  have hsigmaHalf : sigma < 1 / 2 := by
    simpa [sigma] using typeI2LargeMSigma_lt_half d delta hdelta hdeltaLe
  have hx : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta).2 hdeltaLe
  have hLone : 1 ≤ L :=
    (typeI2CapitalZ_ge_one d delta⁻¹ (le_trans zero_le_one hx)).trans
      hLlarge.le
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hC0 : 0 ≤ typeI2C d delta⁻¹ :=
    recurrenceStep_natPolynomialEval_nonneg (typeI2CPolynomial d) delta⁻¹
      (le_trans zero_le_one hx)
  have hW0 : 0 ≤ typeI2W d step delta⁻¹ :=
    recurrenceStep_natPolynomialEval_nonneg (typeI2WPolynomial d step) delta⁻¹
      (le_trans zero_le_one hx)
  have hsmall : typeI2C d delta⁻¹ * typeI2W d step delta⁻¹ ^ 2 /
        L ^ (2 * l) ≤
      1 / (256 * sigma⁻¹ * productRecurrenceA l sigma⁻¹ ^ 2) := by
    simpa [sigma] using
      preliminaryTypeI2LargeM_recurrenceEpsilon_le_sigma
        d l step hl hld hstep delta L hdelta hdeltaLe hLlarge
  have hdensity' : sigma * (N₁ : ℝ) * (N₂ : ℝ) ≤
      (S.card : ℝ) := by
    have hbase : 0 ≤ sigma * (N₁ : ℝ) * (N₂ : ℝ) := by positivity
    have hdouble : sigma * (N₁ : ℝ) * (N₂ : ℝ) ≤
        2 * sigma * (N₁ : ℝ) * (N₂ : ℝ) := by nlinarith
    exact hdouble.trans (by simpa [sigma] using hdensity)
  obtain ⟨w, hw, hwLocal, hwError⟩ :=
    preliminaryTypeI2LargeM_oneDegreeRecurrence
      hl hN₁ hN₂ hsigma hsigmaHalf hLpos hC0 hW0 hsmall
      S hS hdensity' hdirection
  have hsigmaInv : sigma⁻¹ = typeI2Zeta d delta⁻¹ := by
    dsimp [sigma]
    rw [typeI2LargeMSigma_eq_inv_typeI2Zeta d delta hdelta hdeltaLe,
      inv_inv]
  rw [hsigmaInv] at hwLocal hwError
  have hBdom := productRecurrenceB_le_typeI2R d l hl hld delta⁻¹ hx
  refine ⟨w, hw, hwLocal.trans hBdom, ?_⟩
  have hnum :
      productRecurrenceB l (typeI2Zeta d delta⁻¹) *
          typeI2C d delta⁻¹ * typeI2W d step delta⁻¹ ^ 2 ≤
        typeI2R d delta⁻¹ * typeI2C d delta⁻¹ *
          typeI2W d step delta⁻¹ ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBdom hC0) (sq_nonneg _)
  exact hwError.trans <|
    div_le_div_of_nonneg_right hnum (by positivity)

/-- The numerical normalization used immediately after product recurrence:
if the recurrence scale is at least `H / 16`, then an error with denominator
`scale^l` becomes an `H^l`-normalized error with loss at most `16^d` for
`l ≤ d`. -/
theorem preliminaryTypeI2LargeM_normalizeRecurrenceError
    {d l : ℕ} (hld : l ≤ d)
    {H scale A error : ℝ}
    (hH : 0 < H) (hscale : H / 16 ≤ scale)
    (hA : 0 ≤ A) (herror : error ≤ A / scale ^ l) :
    H ^ l * error ≤ 16 ^ d * A := by
  have hscalePos : 0 < scale :=
    lt_of_lt_of_le (div_pos hH (by norm_num)) hscale
  have hHscale : H ≤ 16 * scale := by
    nlinarith
  have hpow : H ^ l ≤ (16 * scale) ^ l :=
    pow_le_pow_left₀ hH.le hHscale l
  have h16pow : (16 : ℝ) ^ l ≤ 16 ^ d :=
    pow_le_pow_right₀ (by norm_num) hld
  have hHpow : H ^ l ≤ 16 ^ d * scale ^ l := by
    calc
      H ^ l ≤ (16 * scale) ^ l := hpow
      _ = 16 ^ l * scale ^ l := by rw [mul_pow]
      _ ≤ 16 ^ d * scale ^ l :=
        mul_le_mul_of_nonneg_right h16pow (pow_nonneg hscalePos.le l)
  have hmul := mul_le_mul_of_nonneg_left herror (pow_nonneg hH.le l)
  calc
    H ^ l * error ≤ H ^ l * (A / scale ^ l) := hmul
    _ = (H ^ l * A) / scale ^ l := by ring
    _ ≤ ((16 ^ d * scale ^ l) * A) / scale ^ l :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hHpow hA) (pow_nonneg hscalePos.le l)
    _ = 16 ^ d * A := by
      field_simp [ne_of_gt hscalePos]

/-- The complete one-degree Type-I₂ recurrence update in the paper's
`H^l` normalization.  This is the exact combination of product recurrence
with the scale inequality `L² N₁ N₂ ≥ H/16`. -/
theorem preliminaryTypeI2LargeM_oneDegreeRecurrence_typeI2_normalized
    {d l step N₁ N₂ : ℕ}
    (hl : 1 ≤ l) (hld : l ≤ d) (hstep : step ≤ d)
    (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (delta L H theta : ℝ)
    (hdelta : 0 < delta) (hdeltaLe : delta ≤ 1)
    (hLlarge : typeI2CapitalZ d delta⁻¹ < L)
    (hH : 0 < H)
    (hscale : H / 16 ≤ L ^ 2 * (N₁ : ℝ) * (N₂ : ℝ))
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ Finset.Icc 1 N₁ ×ˢ Finset.Icc 1 N₂)
    (hdensity :
      2 * typeI2LargeMSigma d delta * (N₁ : ℝ) * (N₂ : ℝ) ≤
        (S.card : ℝ))
    (hdirection : ∀ p ∈ S,
      L ^ (2 * l) * realDistanceToIntegers
        (theta * (((p.1 : ℝ) * (p.2 : ℝ)) ^ l)) ≤
          typeI2C d delta⁻¹ * typeI2W d step delta⁻¹ ^ 2) :
    ∃ w : ℕ, 1 ≤ w ∧
      (w : ℝ) ≤ typeI2R d delta⁻¹ ∧
      H ^ l * realDistanceToIntegers ((w : ℝ) * theta) ≤
        16 ^ d * typeI2R d delta⁻¹ * typeI2C d delta⁻¹ *
          typeI2W d step delta⁻¹ ^ 2 := by
  obtain ⟨w, hw, hwR, hwError⟩ :=
    preliminaryTypeI2LargeM_oneDegreeRecurrence_typeI2
      hl hld hstep hN₁ hN₂ delta L theta hdelta hdeltaLe hLlarge
      S hS hdensity hdirection
  refine ⟨w, hw, hwR, ?_⟩
  have hx : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta).2 hdeltaLe
  have hA : 0 ≤ typeI2R d delta⁻¹ * typeI2C d delta⁻¹ *
      typeI2W d step delta⁻¹ ^ 2 := by
    have hR := typeI2R_ge_one d delta⁻¹ hx
    have hC := typeI2C_ge_one d delta⁻¹ (le_trans zero_le_one hx)
    positivity
  simpa [mul_assoc] using
    preliminaryTypeI2LargeM_normalizeRecurrenceError hld hH hscale hA hwError

/-- The recursion for `W` simultaneously absorbs the newly obtained
coefficient error and the multiplication of every old bound by `w ≤ R`.
These are the two numerical inequalities used in the descending invariant. -/
theorem typeI2W_succ_controls_recurrence
    (d step : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    16 ^ d * typeI2R d x * typeI2C d x * typeI2W d step x ^ 2 ≤
        typeI2W d (step + 1) x ∧
      typeI2R d x * typeI2W d step x ≤
        typeI2W d (step + 1) x := by
  have hR : 1 ≤ typeI2R d x := typeI2R_ge_one d x hx
  have hC : 1 ≤ typeI2C d x :=
    typeI2C_ge_one d x (le_trans zero_le_one hx)
  have hW : 1 ≤ typeI2W d step x := typeI2W_ge_one d step x hx
  have hWsq : typeI2W d step x ≤ typeI2W d step x ^ 2 := by
    nlinarith
  have hbase : 0 ≤
      typeI2R d x * typeI2C d x * typeI2W d step x ^ 2 := by
    positivity
  rw [typeI2W_succ_eval]
  constructor
  · nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) d]
  · calc
      typeI2R d x * typeI2W d step x ≤
          typeI2R d x * typeI2W d step x ^ 2 :=
        mul_le_mul_of_nonneg_left hWsq (le_trans zero_le_one hR)
      _ ≤ typeI2R d x * typeI2C d x * typeI2W d step x ^ 2 := by
        have hleft : 0 ≤ typeI2R d x * typeI2W d step x ^ 2 := by
          positivity
        nlinarith
      _ ≤ (16 ^ d + 1 : ℝ) * typeI2R d x * typeI2C d x *
          typeI2W d step x ^ 2 := by
        have hfactor : 1 ≤ (16 ^ d + 1 : ℝ) := by
          have hp : 0 ≤ (16 : ℝ) ^ d := pow_nonneg (by norm_num) d
          linarith
        calc
          typeI2R d x * typeI2C d x * typeI2W d step x ^ 2 =
              1 * (typeI2R d x * typeI2C d x *
                typeI2W d step x ^ 2) := by ring
          _ ≤ (16 ^ d + 1 : ℝ) *
                (typeI2R d x * typeI2C d x *
                  typeI2W d step x ^ 2) :=
            mul_le_mul_of_nonneg_right hfactor hbase
          _ = (16 ^ d + 1 : ℝ) * typeI2R d x * typeI2C d x *
                typeI2W d step x ^ 2 := by ring

/-- The same recursion absorbs an old coefficient or denominator multiplied
by any integer of size at most `R*C`.  This is the residue-spacing-aware form
needed after restoring the omitted `q₀^(2l)` factor. -/
theorem typeI2W_succ_controls_RC
    (d step : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    typeI2R d x * typeI2C d x * typeI2W d step x ≤
      typeI2W d (step + 1) x := by
  have hR : 0 ≤ typeI2R d x :=
    le_trans zero_le_one (typeI2R_ge_one d x hx)
  have hC : 0 ≤ typeI2C d x :=
    le_trans zero_le_one (typeI2C_ge_one d x (le_trans zero_le_one hx))
  have hW : 1 ≤ typeI2W d step x := typeI2W_ge_one d step x hx
  have hWsq : typeI2W d step x ≤ typeI2W d step x ^ 2 := by
    nlinarith
  have hbase : 0 ≤
      typeI2R d x * typeI2C d x * typeI2W d step x ^ 2 := by
    positivity
  rw [typeI2W_succ_eval]
  calc
    typeI2R d x * typeI2C d x * typeI2W d step x ≤
        typeI2R d x * typeI2C d x * typeI2W d step x ^ 2 :=
      mul_le_mul_of_nonneg_left hWsq (mul_nonneg hR hC)
    _ = 1 * (typeI2R d x * typeI2C d x *
          typeI2W d step x ^ 2) := by ring
    _ ≤ (16 ^ d + 1 : ℝ) *
          (typeI2R d x * typeI2C d x *
            typeI2W d step x ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hbase
      have hp : 0 ≤ (16 : ℝ) ^ d := pow_nonneg (by norm_num) d
      linarith
    _ = (16 ^ d + 1 : ℝ) * typeI2R d x * typeI2C d x *
          typeI2W d step x ^ 2 := by ring

/-- The finite invariant used in the descending coefficient induction.  At
degree `l`, `s` is a positive multiple of the original denominator `v`, is
bounded by `W_step`, and every coefficient strictly above `l` already has
the required `H`-normalized circle-distance bound. -/
structure TypeI2LargeMDescentState
    (P : Polynomial ℝ) (d l step : ℕ) (x H : ℝ) (v : ℕ) where
  s : ℕ
  s_pos : 1 ≤ s
  v_dvd_s : v ∣ s
  s_upper : (s : ℝ) ≤ typeI2W d step x
  higher_error : ∀ j ∈ Finset.Ico (l + 1) (d + 1),
    H ^ j * realDistanceToIntegers ((s : ℝ) * P.coeff j) ≤
      typeI2W d step x

/-- One inverse-progression witness supplies the corrected direction-wise
leading-coefficient error used by product recurrence.  The actual progression
spacing is `q₀(q,-a)`, so the conclusion retains the factor `q₀^(2l)` that is
absent from the corresponding displayed line of the blueprint proof. -/
theorem TypeI2LargeMInverseProgressionData.leadingError_of_descentState
    {g : HyperbolaGeometricData} {d : ℕ} {δ : ℝ} {q₀ : ℕ}
    {P : Polynomial ℝ} {a q : ℕ}
    (D : TypeI2LargeMInverseProgressionData g d δ q₀ P a q)
    {l step : ℕ}
    (hP : P.natDegree ≤ d) (hl : 1 ≤ l) (hld : l ≤ d)
    (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hq₀ : 1 ≤ q₀) (ha : 1 ≤ a) (hq : 1 ≤ q)
    (hscale36 : 36 < (typeI2T (δ⁻¹))⁻¹ * g.L0)
    (state : TypeI2LargeMDescentState
      (phaseCenteredAt P (Int.floor g.X)) d l step δ⁻¹ g.H D.v) :
    g.L0 ^ (2 * l) * realDistanceToIntegers
        (((q₀ : ℝ) ^ (2 * l) *
            ((state.s : ℝ) *
              (phaseCenteredAt P (Int.floor g.X)).coeff l)) *
          (((q : ℝ) * (a : ℝ)) ^ l)) ≤
      typeI2C d δ⁻¹ * typeI2W d step δ⁻¹ ^ 2 := by
  let p : Polynomial ℝ := phaseCenteredAt P (Int.floor g.X)
  let m₀ : ℤ := D.z.1 - (q₀ : ℤ) * (q : ℤ)
  let n₀ : ℤ := D.z.2 + (q₀ : ℤ) * (a : ℤ)
  let qstep : ℤ := (q₀ : ℤ) * (q : ℤ)
  let astep : ℤ := (q₀ : ℤ) * (a : ℤ)
  have hx : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδle
  have ht : 0 < typeI2T (δ⁻¹) :=
    lt_of_lt_of_le (by norm_num) (typeI2T_ge_two δ⁻¹ hx)
  have hKreal : (36 : ℝ) ≤ (D.N : ℝ) :=
    (hscale36.trans_le D.scale_lower).le
  have hK : 36 ≤ D.N := by exact_mod_cast hKreal
  have hLpos : 0 < g.L0 := by
    have hHpos : 0 < g.H := lt_of_lt_of_le zero_lt_one g.H_ge_one
    have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
    have hMpos : 0 < g.M := lt_of_lt_of_le zero_lt_one g.M_ge_one
    dsimp [HyperbolaGeometricData.L0]
    positivity
  have hLK : g.L0 ≤ typeI2T (δ⁻¹) * (D.N : ℝ) := by
    calc
      g.L0 = typeI2T (δ⁻¹) *
          ((typeI2T (δ⁻¹))⁻¹ * g.L0) := by
        field_simp [ne_of_gt ht]
      _ ≤ typeI2T (δ⁻¹) * (D.N : ℝ) :=
        mul_le_mul_of_nonneg_left D.scale_lower ht.le
  have hp : p.natDegree ≤ d := by
    simpa [p] using
      phaseCenteredAt_natDegree_le P hP (Int.floor g.X)
  have hstrip : ∀ n ∈ Finset.Icc 1 D.N,
      g.X < ((m₀ : ℝ) + (qstep : ℝ) * (n : ℝ)) *
          ((n₀ : ℝ) - (astep : ℝ) * (n : ℝ)) ∧
        ((m₀ : ℝ) + (qstep : ℝ) * (n : ℝ)) *
          ((n₀ : ℝ) - (astep : ℝ) * (n : ℝ)) ≤ g.X + g.H := by
    simpa [m₀, n₀, qstep, astep] using D.oneIndexed_strip
  obtain ⟨quotient, hquotient⟩ := state.v_dvd_s
  have hsq : (state.s : ℤ) = (D.v : ℤ) * (quotient : ℤ) := by
    exact_mod_cast hquotient
  have hvReal : (1 : ℝ) ≤ (D.v : ℝ) := by exact_mod_cast D.v_pos
  have hquotientReal : (quotient : ℝ) ≤ (state.s : ℝ) := by
    have hsReal : (state.s : ℝ) = (D.v : ℝ) * (quotient : ℝ) := by
      exact_mod_cast hquotient
    rw [hsReal]
    nlinarith [show (0 : ℝ) ≤ quotient by positivity]
  have hquotientW : |((quotient : ℤ) : ℝ)| ≤
      typeI2W d step δ⁻¹ := by
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ quotient by positivity)] using
      hquotientReal.trans state.s_upper
  have hW : 1 ≤ typeI2W d step δ⁻¹ :=
    typeI2W_ge_one d step δ⁻¹ hx
  have hBW : typeI2B d δ⁻¹ ≤ typeI2W d step δ⁻¹ := by
    calc
      typeI2B d δ⁻¹ = typeI2W d 0 δ⁻¹ :=
        (typeI2W_zero_eval d δ⁻¹).symm
      _ ≤ typeI2W d step δ⁻¹ :=
        typeI2W_monotone d δ⁻¹ hx (Nat.zero_le step)
  have hphaseComp :
      p.comp (hyperbolaCenteredProductPolynomial
          m₀ n₀ qstep astep (Int.floor g.X)) =
        P.comp (hyperbolaProductPolynomial m₀ n₀ qstep astep) := by
    simpa [p] using
      phaseCenteredAt_comp_hyperbolaCenteredProductPolynomial
        P m₀ n₀ qstep astep (Int.floor g.X)
  have horiginal :
      g.L0 ^ (2 * l) * realDistanceToIntegers
        ((D.v : ℝ) *
          (p.comp (hyperbolaCenteredProductPolynomial
            m₀ n₀ qstep astep (Int.floor g.X))).coeff (2 * l)) ≤
        typeI2B d δ⁻¹ := by
    rw [hphaseComp]
    simpa [m₀, n₀, qstep, astep] using
      D.coefficient_error (2 * l) (by omega) (by omega)
  have hqstep : qstep ≠ 0 := by
    have hpos : (0 : ℤ) < qstep := by
      dsimp [qstep]
      exact mul_pos (by exact_mod_cast hq₀) (by exact_mod_cast hq)
    exact ne_of_gt hpos
  have hastep : astep ≠ 0 := by
    have hpos : (0 : ℤ) < astep := by
      dsimp [astep]
      exact mul_pos (by exact_mod_cast hq₀) (by exact_mod_cast ha)
    exact ne_of_gt hpos
  have herror :=
    hyperbolaCenteredProductPolynomial_truncation_comp_error_le_typeI2C
      p m₀ n₀ qstep astep D.N hK g.X g.H g.L0 δ⁻¹
      g.H_ge_one hLpos.le hx hLK hstrip hp hld
      (state.s : ℤ) (D.v : ℤ) (quotient : ℤ) hsq (2 * l)
      hW hquotientW hBW horiginal state.higher_error
  rw [hyperbolaCenteredProductPolynomial_truncation_topDistance
    p m₀ n₀ qstep astep (Int.floor g.X) l hl hqstep hastep
      ((state.s : ℤ) : ℝ)] at herror
  have hbase : (qstep : ℝ) * (astep : ℝ) =
      (q₀ : ℝ) ^ 2 * ((q : ℝ) * (a : ℝ)) := by
    dsimp [qstep, astep]
    push_cast
    ring
  have harg :
      (((qstep : ℝ) * (astep : ℝ)) ^ l) *
          (((state.s : ℤ) : ℝ) * p.coeff l) =
        ((q₀ : ℝ) ^ (2 * l) *
            ((state.s : ℝ) *
              (phaseCenteredAt P (Int.floor g.X)).coeff l)) *
          (((q : ℝ) * (a : ℝ)) ^ l) := by
    rw [hbase, mul_pow, pow_mul]
    simp only [Int.cast_natCast, p]
    ring
  rw [harg] at herror
  exact herror

/-- The initial state is `s=v`, with no coefficient above degree `d`. -/
def typeI2LargeMDescentState_initial
    (P : Polynomial ℝ) (d : ℕ) (x H : ℝ) (v : ℕ)
    (hv : 1 ≤ v) (hvB : (v : ℝ) ≤ typeI2B d x) :
    TypeI2LargeMDescentState P d d 0 x H v := by
  refine ⟨v, hv, dvd_rfl, ?_, ?_⟩
  · simpa using hvB
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    omega

/-- Multiplying a descent state by the recurrence output `w` gives the next
state.  The new degree uses the normalized recurrence estimate; all old
degrees use integer-multiple subadditivity of circle distance. -/
def TypeI2LargeMDescentState.mulRecurrence
    {P : Polynomial ℝ} {d l step : ℕ} {x H : ℝ} {v : ℕ}
    (state : TypeI2LargeMDescentState P d l step x H v)
    (hl : 1 ≤ l) (hx : 1 ≤ x) (hH : 0 ≤ H)
    (w : ℕ) (hw : 1 ≤ w) (hwR : (w : ℝ) ≤ typeI2R d x)
    (hnew : H ^ l * realDistanceToIntegers
      ((w : ℝ) * ((state.s : ℝ) * P.coeff l)) ≤
        16 ^ d * typeI2R d x * typeI2C d x *
          typeI2W d step x ^ 2) :
    TypeI2LargeMDescentState P d (l - 1) (step + 1) x H v := by
  let s' : ℕ := w * state.s
  have hbudget := typeI2W_succ_controls_recurrence d step x hx
  have hR0 : 0 ≤ typeI2R d x := le_trans zero_le_one (typeI2R_ge_one d x hx)
  have hW0 : 0 ≤ typeI2W d step x :=
    le_trans zero_le_one (typeI2W_ge_one d step x hx)
  have hsUpper : (s' : ℝ) ≤ typeI2W d (step + 1) x := by
    calc
      (s' : ℝ) = (w : ℝ) * (state.s : ℝ) := by
        simp [s']
      _ ≤ typeI2R d x * typeI2W d step x :=
        mul_le_mul hwR state.s_upper (Nat.cast_nonneg _) hR0
      _ ≤ typeI2W d (step + 1) x := hbudget.2
  refine
    { s := s'
      s_pos := Nat.mul_pos hw state.s_pos
      v_dvd_s := dvd_mul_of_dvd_right state.v_dvd_s w
      s_upper := hsUpper
      higher_error := ?_ }
  intro j hj
  have hjRange : l ≤ j ∧ j ≤ d := by
    simp only [Finset.mem_Ico] at hj
    omega
  by_cases hjl : j = l
  · subst j
    simpa [s', mul_assoc] using hnew.trans hbudget.1
  · have hjOld : j ∈ Finset.Ico (l + 1) (d + 1) := by
      simp only [Finset.mem_Ico]
      omega
    have hdist := realDistanceToIntegers_int_mul_le (w : ℤ)
      ((state.s : ℝ) * P.coeff j)
    have hscaled :
        H ^ j * realDistanceToIntegers
            ((s' : ℝ) * P.coeff j) ≤
          (w : ℝ) *
            (H ^ j * realDistanceToIntegers
              ((state.s : ℝ) * P.coeff j)) := by
      calc
        H ^ j * realDistanceToIntegers ((s' : ℝ) * P.coeff j) =
            H ^ j * realDistanceToIntegers
              ((w : ℝ) * ((state.s : ℝ) * P.coeff j)) := by
                congr 2
                simp [s', mul_assoc]
        _ ≤ H ^ j *
            (|(w : ℝ)| * realDistanceToIntegers
              ((state.s : ℝ) * P.coeff j)) :=
          mul_le_mul_of_nonneg_left hdist (pow_nonneg hH j)
        _ = (w : ℝ) *
            (H ^ j * realDistanceToIntegers
              ((state.s : ℝ) * P.coeff j)) := by
          rw [abs_of_nonneg (Nat.cast_nonneg w)]
          ring
    calc
      H ^ j * realDistanceToIntegers ((s' : ℝ) * P.coeff j) ≤
          (w : ℝ) *
            (H ^ j * realDistanceToIntegers
              ((state.s : ℝ) * P.coeff j)) := hscaled
      _ ≤ (w : ℝ) * typeI2W d step x :=
        mul_le_mul_of_nonneg_left (state.higher_error j hjOld)
          (Nat.cast_nonneg w)
      _ ≤ typeI2R d x * typeI2W d step x :=
        mul_le_mul_of_nonneg_right hwR hW0
      _ ≤ typeI2W d (step + 1) x := hbudget.2

/-- Residue-spacing-aware invariant update.  It permits the multiplier
`m=w*q₀^(2l)`, whose size is bounded by `R*C`, while keeping the same
`W_{step+1}` target. -/
def TypeI2LargeMDescentState.mulRecurrenceWithC
    {P : Polynomial ℝ} {d l step : ℕ} {x H : ℝ} {v : ℕ}
    (state : TypeI2LargeMDescentState P d l step x H v)
    (hl : 1 ≤ l) (hx : 1 ≤ x) (hH : 0 ≤ H)
    (m : ℕ) (hm : 1 ≤ m)
    (hmRC : (m : ℝ) ≤ typeI2R d x * typeI2C d x)
    (hnew : H ^ l * realDistanceToIntegers
      ((m : ℝ) * ((state.s : ℝ) * P.coeff l)) ≤
        16 ^ d * typeI2R d x * typeI2C d x *
          typeI2W d step x ^ 2) :
    TypeI2LargeMDescentState P d (l - 1) (step + 1) x H v := by
  let s' : ℕ := m * state.s
  have hbudgetNew := (typeI2W_succ_controls_recurrence d step x hx).1
  have hbudgetOld := typeI2W_succ_controls_RC d step x hx
  have hRC0 : 0 ≤ typeI2R d x * typeI2C d x := by
    exact mul_nonneg
      (le_trans zero_le_one (typeI2R_ge_one d x hx))
      (le_trans zero_le_one
        (typeI2C_ge_one d x (le_trans zero_le_one hx)))
  have hW0 : 0 ≤ typeI2W d step x :=
    le_trans zero_le_one (typeI2W_ge_one d step x hx)
  have hsUpper : (s' : ℝ) ≤ typeI2W d (step + 1) x := by
    calc
      (s' : ℝ) = (m : ℝ) * (state.s : ℝ) := by simp [s']
      _ ≤ (typeI2R d x * typeI2C d x) * typeI2W d step x :=
        mul_le_mul hmRC state.s_upper (Nat.cast_nonneg _) hRC0
      _ = typeI2R d x * typeI2C d x * typeI2W d step x := by ring
      _ ≤ typeI2W d (step + 1) x := hbudgetOld
  refine
    { s := s'
      s_pos := Nat.mul_pos hm state.s_pos
      v_dvd_s := dvd_mul_of_dvd_right state.v_dvd_s m
      s_upper := hsUpper
      higher_error := ?_ }
  intro j hj
  have hjRange : l ≤ j ∧ j ≤ d := by
    simp only [Finset.mem_Ico] at hj
    omega
  by_cases hjl : j = l
  · subst j
    simpa [s', mul_assoc] using hnew.trans hbudgetNew
  · have hjOld : j ∈ Finset.Ico (l + 1) (d + 1) := by
      simp only [Finset.mem_Ico]
      omega
    have hdist := realDistanceToIntegers_int_mul_le (m : ℤ)
      ((state.s : ℝ) * P.coeff j)
    have hscaled :
        H ^ j * realDistanceToIntegers
            ((s' : ℝ) * P.coeff j) ≤
          (m : ℝ) *
            (H ^ j * realDistanceToIntegers
              ((state.s : ℝ) * P.coeff j)) := by
      calc
        H ^ j * realDistanceToIntegers ((s' : ℝ) * P.coeff j) =
            H ^ j * realDistanceToIntegers
              ((m : ℝ) * ((state.s : ℝ) * P.coeff j)) := by
                congr 2
                simp [s', mul_assoc]
        _ ≤ H ^ j *
            (|(m : ℝ)| * realDistanceToIntegers
              ((state.s : ℝ) * P.coeff j)) :=
          mul_le_mul_of_nonneg_left hdist (pow_nonneg hH j)
        _ = (m : ℝ) *
            (H ^ j * realDistanceToIntegers
              ((state.s : ℝ) * P.coeff j)) := by
          rw [abs_of_nonneg (Nat.cast_nonneg m)]
          ring
    calc
      H ^ j * realDistanceToIntegers ((s' : ℝ) * P.coeff j) ≤
          (m : ℝ) *
            (H ^ j * realDistanceToIntegers
              ((state.s : ℝ) * P.coeff j)) := hscaled
      _ ≤ (m : ℝ) * typeI2W d step x :=
        mul_le_mul_of_nonneg_left (state.higher_error j hjOld)
          (Nat.cast_nonneg m)
      _ ≤ (typeI2R d x * typeI2C d x) *
          typeI2W d step x :=
        mul_le_mul_of_nonneg_right hmRC hW0
      _ = typeI2R d x * typeI2C d x * typeI2W d step x := by ring
      _ ≤ typeI2W d (step + 1) x := hbudgetOld
/-- One complete source-specific successor in the Type-I₂ coefficient
descent: product recurrence supplies `w`, and the finite invariant is updated
from degree `l` to degree `l-1`. -/
theorem preliminaryTypeI2LargeM_descentStep
    {P : Polynomial ℝ} {d l step N₁ N₂ : ℕ} {v : ℕ}
    (delta L H : ℝ)
    (state : TypeI2LargeMDescentState P d l step delta⁻¹ H v)
    (hl : 1 ≤ l) (hld : l ≤ d) (hstep : step ≤ d)
    (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hdelta : 0 < delta) (hdeltaLe : delta ≤ 1)
    (hLlarge : typeI2CapitalZ d delta⁻¹ < L)
    (hH : 0 < H)
    (hscale : H / 16 ≤ L ^ 2 * (N₁ : ℝ) * (N₂ : ℝ))
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ Finset.Icc 1 N₁ ×ˢ Finset.Icc 1 N₂)
    (hdensity :
      2 * typeI2LargeMSigma d delta * (N₁ : ℝ) * (N₂ : ℝ) ≤
        (S.card : ℝ))
    (hdirection : ∀ p ∈ S,
      L ^ (2 * l) * realDistanceToIntegers
        (((state.s : ℝ) * P.coeff l) *
          (((p.1 : ℝ) * (p.2 : ℝ)) ^ l)) ≤
            typeI2C d delta⁻¹ * typeI2W d step delta⁻¹ ^ 2) :
    ∃ w : ℕ,
      ∃ next : TypeI2LargeMDescentState
        P d (l - 1) (step + 1) delta⁻¹ H v,
        1 ≤ w ∧ (w : ℝ) ≤ typeI2R d delta⁻¹ ∧
          next.s = w * state.s := by
  obtain ⟨w, hw, hwR, hnew⟩ :=
    preliminaryTypeI2LargeM_oneDegreeRecurrence_typeI2_normalized
      hl hld hstep hN₁ hN₂ delta L H
        ((state.s : ℝ) * P.coeff l)
      hdelta hdeltaLe hLlarge hH hscale S hS hdensity hdirection
  let next := state.mulRecurrence hl
    ((one_le_inv₀ hdelta).2 hdeltaLe) hH.le w hw hwR hnew
  refine ⟨w, next, hw, hwR, ?_⟩
  simp [next, TypeI2LargeMDescentState.mulRecurrence]

/-- Corrected one-step descent for the actual spacing `q₀(q,-a)` returned
by ordinary pigeonholing.  Product recurrence is applied to
`q₀^(2l) s α_l`; the existing `C` budget absorbs this extra integer factor,
so the approved `W` recursion and theorem statement remain unchanged. -/
theorem preliminaryTypeI2LargeM_descentStep_residueSpacing
    {P : Polynomial ℝ} {d l step N₁ N₂ : ℕ} {v : ℕ}
    (delta L H : ℝ) (q₀ : ℕ)
    (state : TypeI2LargeMDescentState P d l step delta⁻¹ H v)
    (hl : 1 ≤ l) (hld : l ≤ d) (hstep : step ≤ d)
    (hq₀ : 1 ≤ q₀) (hq₀bound : (q₀ : ℝ) ≤ delta⁻¹)
    (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hdelta : 0 < delta) (hdeltaLe : delta ≤ 1)
    (hLlarge : typeI2CapitalZ d delta⁻¹ < L)
    (hH : 0 < H)
    (hscale : H / 16 ≤ L ^ 2 * (N₁ : ℝ) * (N₂ : ℝ))
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ Finset.Icc 1 N₁ ×ˢ Finset.Icc 1 N₂)
    (hdensity :
      2 * typeI2LargeMSigma d delta * (N₁ : ℝ) * (N₂ : ℝ) ≤
        (S.card : ℝ))
    (hdirection : ∀ p ∈ S,
      L ^ (2 * l) * realDistanceToIntegers
        (((q₀ : ℝ) ^ (2 * l) *
            ((state.s : ℝ) * P.coeff l)) *
          (((p.1 : ℝ) * (p.2 : ℝ)) ^ l)) ≤
            typeI2C d delta⁻¹ * typeI2W d step delta⁻¹ ^ 2) :
    ∃ w m : ℕ,
      ∃ next : TypeI2LargeMDescentState
        P d (l - 1) (step + 1) delta⁻¹ H v,
        1 ≤ w ∧ (w : ℝ) ≤ typeI2R d delta⁻¹ ∧
          m = w * q₀ ^ (2 * l) ∧ next.s = m * state.s := by
  obtain ⟨w, hw, hwR, hnew⟩ :=
    preliminaryTypeI2LargeM_oneDegreeRecurrence_typeI2_normalized
      hl hld hstep hN₁ hN₂ delta L H
        ((q₀ : ℝ) ^ (2 * l) * ((state.s : ℝ) * P.coeff l))
      hdelta hdeltaLe hLlarge hH hscale S hS hdensity hdirection
  let m : ℕ := w * q₀ ^ (2 * l)
  have hqpowPos : 1 ≤ q₀ ^ (2 * l) := one_le_pow₀ hq₀
  have hm : 1 ≤ m := Nat.mul_pos hw hqpowPos
  have hx : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta).2 hdeltaLe
  have hqpowC : (q₀ : ℝ) ^ (2 * l) ≤ typeI2C d delta⁻¹ :=
    typeI2_residueSpacingPower_le_C d l q₀ hl hld delta⁻¹ hx hq₀bound
  have hmRC : (m : ℝ) ≤
      typeI2R d delta⁻¹ * typeI2C d delta⁻¹ := by
    calc
      (m : ℝ) = (w : ℝ) * (q₀ : ℝ) ^ (2 * l) := by simp [m]
      _ ≤ typeI2R d delta⁻¹ * typeI2C d delta⁻¹ :=
        mul_le_mul hwR hqpowC (by positivity)
          (le_trans zero_le_one (typeI2R_ge_one d delta⁻¹ hx))
  have hnew' : H ^ l * realDistanceToIntegers
      ((m : ℝ) * ((state.s : ℝ) * P.coeff l)) ≤
        16 ^ d * typeI2R d delta⁻¹ * typeI2C d delta⁻¹ *
          typeI2W d step delta⁻¹ ^ 2 := by
    simpa [m, mul_assoc] using hnew
  let next := state.mulRecurrenceWithC hl hx hH.le m hm hmRC hnew'
  refine ⟨w, m, next, hw, hwR, rfl, ?_⟩
  simp [next, TypeI2LargeMDescentState.mulRecurrenceWithC]

/-- The complete one-degree successor built directly from the common-
denominator inverse-progression data on a dense direction rectangle. -/
theorem preliminaryTypeI2LargeM_descentStep_inverseData
    {g : HyperbolaGeometricData} {d l step N₁ N₂ v q₀ : ℕ}
    {δ : ℝ} {P : Polynomial ℝ}
    (state : TypeI2LargeMDescentState
      (phaseCenteredAt P (Int.floor g.X)) d l step δ⁻¹ g.H v)
    (hP : P.natDegree ≤ d) (hl : 1 ≤ l) (hld : l ≤ d)
    (hstep : step ≤ d)
    (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hq₀ : 1 ≤ q₀) (hq₀bound : (q₀ : ℝ) ≤ δ⁻¹)
    (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hLlarge : typeI2CapitalZ d δ⁻¹ < g.L0)
    (hscale36 : 36 < (typeI2T (δ⁻¹))⁻¹ * g.L0)
    (hscale : g.H / 16 ≤ g.L0 ^ 2 * (N₁ : ℝ) * (N₂ : ℝ))
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ Finset.Icc 1 N₁ ×ˢ Finset.Icc 1 N₂)
    (hdensity :
      2 * typeI2LargeMSigma d δ * (N₁ : ℝ) * (N₂ : ℝ) ≤
        (S.card : ℝ))
    (hinverse : ∀ i ∈ S,
      ∃ D : TypeI2LargeMInverseProgressionData
        g d δ q₀ P i.2 i.1, D.v = v) :
    Nonempty (TypeI2LargeMDescentState
      (phaseCenteredAt P (Int.floor g.X)) d (l - 1) (step + 1)
        δ⁻¹ g.H v) := by
  have hdirection : ∀ i ∈ S,
      g.L0 ^ (2 * l) * realDistanceToIntegers
        (((q₀ : ℝ) ^ (2 * l) *
            ((state.s : ℝ) *
              (phaseCenteredAt P (Int.floor g.X)).coeff l)) *
          (((i.1 : ℝ) * (i.2 : ℝ)) ^ l)) ≤
        typeI2C d δ⁻¹ * typeI2W d step δ⁻¹ ^ 2 := by
    intro i hi
    have hiBox := Finset.mem_product.mp (hS hi)
    have hq : 1 ≤ i.1 := (Finset.mem_Icc.mp hiBox.1).1
    have ha : 1 ≤ i.2 := (Finset.mem_Icc.mp hiBox.2).1
    rcases hinverse i hi with ⟨D, hDv⟩
    subst v
    have hlead := D.leadingError_of_descentState hP hl hld hδ hδle
      hq₀ ha hq hscale36 state
    exact hlead
  obtain ⟨_w, _m, next, _hw, _hwR, _hm, _hnext⟩ :=
    preliminaryTypeI2LargeM_descentStep_residueSpacing
      δ g.L0 g.H q₀ state hl hld hstep hq₀ hq₀bound
      hN₁ hN₂ hδ hδle hLlarge
      (lt_of_lt_of_le zero_lt_one g.H_ge_one) hscale
      S hS hdensity hdirection
  exact ⟨next⟩

/-- Finite downward iteration of the checked inverse-data successor.  A state
at degree `l` and step `d-l` reaches degree zero at the approved final budget
`W_d`. -/
theorem preliminaryTypeI2LargeM_finishDescent_inverseData
    {g : HyperbolaGeometricData} {d l N₁ N₂ v q₀ : ℕ}
    {δ : ℝ} {P : Polynomial ℝ}
    (state : TypeI2LargeMDescentState
      (phaseCenteredAt P (Int.floor g.X)) d l (d - l) δ⁻¹ g.H v)
    (hld : l ≤ d)
    (hP : P.natDegree ≤ d)
    (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hq₀ : 1 ≤ q₀) (hq₀bound : (q₀ : ℝ) ≤ δ⁻¹)
    (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hLlarge : typeI2CapitalZ d δ⁻¹ < g.L0)
    (hscale36 : 36 < (typeI2T (δ⁻¹))⁻¹ * g.L0)
    (hscale : g.H / 16 ≤ g.L0 ^ 2 * (N₁ : ℝ) * (N₂ : ℝ))
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ Finset.Icc 1 N₁ ×ˢ Finset.Icc 1 N₂)
    (hdensity :
      2 * typeI2LargeMSigma d δ * (N₁ : ℝ) * (N₂ : ℝ) ≤
        (S.card : ℝ))
    (hinverse : ∀ i ∈ S,
      ∃ D : TypeI2LargeMInverseProgressionData
        g d δ q₀ P i.2 i.1, D.v = v) :
    Nonempty (TypeI2LargeMDescentState
      (phaseCenteredAt P (Int.floor g.X)) d 0 d δ⁻¹ g.H v) := by
  induction l with
  | zero =>
      simpa using
        (show Nonempty (TypeI2LargeMDescentState
          (phaseCenteredAt P (Int.floor g.X)) d 0 d δ⁻¹ g.H v) from
          ⟨state⟩)
  | succ l ih =>
      have hl : 1 ≤ l + 1 := by omega
      have hl_le : l ≤ d := by omega
      obtain ⟨next⟩ := preliminaryTypeI2LargeM_descentStep_inverseData
        state hP hl hld (by omega) hδ hδle hq₀ hq₀bound
        hN₁ hN₂ hLlarge hscale36 hscale S hS hdensity hinverse
      have hstep : d - (l + 1) + 1 = d - l := by omega
      have next' : TypeI2LargeMDescentState
          (phaseCenteredAt P (Int.floor g.X)) d l (d - l) δ⁻¹ g.H v := by
        simpa [hstep] using next
      exact ih next' hl_le

/-- A completed descent state gives the source's common integer multiplier,
all centered monomial bounds, and the binomial seminorm bound, each absorbed
by the approved `J_d` budget. -/
theorem TypeI2LargeMDescentState.finalCoefficientBounds
    {P : Polynomial ℝ} {d v : ℕ} {x H : ℝ} {Y : ℤ}
    (state : TypeI2LargeMDescentState
      (phaseCenteredAt P Y) d 0 d x H v)
    (hd : 1 ≤ d) (hP : P.natDegree ≤ d)
    (hx : 1 ≤ x) (hH : 1 ≤ H) :
    ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ typeI2J d x ∧
      polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
          Y H ≤ typeI2J d x ∧
      ∀ j, 1 ≤ j → j ≤ d →
        H ^ j * realDistanceToIntegers
          ((r : ℝ) * (phaseCenteredAt P Y).coeff j) ≤ typeI2J d x := by
  let r : ℤ := state.s
  have hr : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast state.s_pos
  have hWJ : typeI2W d d x ≤ typeI2J d x := by
    have hEone : 1 ≤ (inverseBoundEValue d : ℝ) := by
      exact_mod_cast inverseBoundE_ge_one d
    have hW0 : 0 ≤ typeI2W d d x :=
      le_trans zero_le_one (typeI2W_ge_one d d x hx)
    calc
      typeI2W d d x = 1 * typeI2W d d x := by ring
      _ ≤ (inverseBoundEValue d : ℝ) * typeI2W d d x :=
        mul_le_mul_of_nonneg_right hEone hW0
      _ ≤ typeI2J d x := inverseBoundE_mul_typeI2W_le_typeI2J d x hx
  have hrUpper : (r : ℝ) ≤ typeI2J d x := by
    exact state.s_upper.trans hWJ
  have hmonoW : ∀ j ∈ Finset.Icc 1 d,
      H ^ j * realDistanceToIntegers
        ((r : ℝ) * (phaseCenteredAt P Y).coeff j) ≤ typeI2W d d x := by
    intro j hj
    have hj' : j ∈ Finset.Ico (0 + 1) (d + 1) := by
      simp only [Finset.mem_Icc, Finset.mem_Ico] at hj ⊢
      omega
    simpa [r] using state.higher_error j hj'
  have hbinW :
      polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
          Y H ≤ (inverseBoundEValue d : ℝ) * typeI2W d d x := by
    exact monomialToBinomialControl d hd Y H hH P
      (fun j => (phaseCenteredAt P Y).coeff j)
      (phaseCenteredAt_monomial_expansion P hP Y)
      r hr (typeI2W d d x) hmonoW
  refine ⟨r, hr, hrUpper,
    hbinW.trans (inverseBoundE_mul_typeI2W_le_typeI2J d x hx), ?_⟩
  intro j hj hjd
  exact (hmonoW j (Finset.mem_Icc.mpr ⟨hj, hjd⟩)).trans hWJ

/-- The dense common-denominator rectangle, together with the checked
large-scale inequalities, yields the full monomial and binomial conclusion
of the large-`M` preliminary Type-I₂ branch. -/
theorem preliminaryTypeI2LargeM_coefficientConclusion
    {g : HyperbolaGeometricData} {d N₁ N₂ v q₀ : ℕ}
    {δ : ℝ} {P : Polynomial ℝ}
    (hd : 1 ≤ d) (hP : P.natDegree ≤ d)
    (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hq₀ : 1 ≤ q₀) (hq₀bound : (q₀ : ℝ) ≤ δ⁻¹)
    (hv : 1 ≤ v) (hvB : (v : ℝ) ≤ typeI2B d δ⁻¹)
    (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hLlarge : typeI2CapitalZ d δ⁻¹ < g.L0)
    (hscale36 : 36 < (typeI2T (δ⁻¹))⁻¹ * g.L0)
    (hscale : g.H / 16 ≤ g.L0 ^ 2 * (N₁ : ℝ) * (N₂ : ℝ))
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ Finset.Icc 1 N₁ ×ˢ Finset.Icc 1 N₂)
    (hdensity :
      2 * typeI2LargeMSigma d δ * (N₁ : ℝ) * (N₂ : ℝ) ≤
        (S.card : ℝ))
    (hinverse : ∀ i ∈ S,
      ∃ D : TypeI2LargeMInverseProgressionData
        g d δ q₀ P i.2 i.1, D.v = v) :
    ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ typeI2J d δ⁻¹ ∧
      polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
          (Int.floor g.X) g.H ≤ typeI2J d δ⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        g.H ^ j * realDistanceToIntegers
          ((r : ℝ) *
            (phaseCenteredAt P (Int.floor g.X)).coeff j) ≤
          typeI2J d δ⁻¹ := by
  have hx : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδle
  let initial₀ := typeI2LargeMDescentState_initial
    (phaseCenteredAt P (Int.floor g.X)) d δ⁻¹ g.H v hv hvB
  have initial : TypeI2LargeMDescentState
      (phaseCenteredAt P (Int.floor g.X)) d d (d - d) δ⁻¹ g.H v := by
    simpa [initial₀] using initial₀
  obtain ⟨final⟩ := preliminaryTypeI2LargeM_finishDescent_inverseData
    initial (le_refl d) hP hδ hδle hq₀ hq₀bound hN₁ hN₂
    hLlarge hscale36 hscale S hS hdensity hinverse
  exact final.finalCoefficientBounds hd hP hx g.H_ge_one

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_oneDegreeRecurrence
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_recurrenceEpsilon_le
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_recurrenceEpsilon_le_sigma
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_oneDegreeRecurrence_typeI2
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_normalizeRecurrenceError
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_oneDegreeRecurrence_typeI2_normalized
#print axioms FractionalPrimes.Literature.Polynomial.typeI2W_succ_controls_recurrence
#print axioms FractionalPrimes.Literature.Polynomial.typeI2LargeMDescentState_initial
#print axioms FractionalPrimes.Literature.Polynomial.TypeI2LargeMDescentState.mulRecurrence
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_descentStep
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_residueSpacingPower_le_C
#print axioms FractionalPrimes.Literature.Polynomial.typeI2W_succ_controls_RC
#print axioms FractionalPrimes.Literature.Polynomial.TypeI2LargeMDescentState.mulRecurrenceWithC
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_descentStep_residueSpacing
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_descentStep_inverseData
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_finishDescent_inverseData
#print axioms FractionalPrimes.Literature.Polynomial.TypeI2LargeMDescentState.finalCoefficientBounds
#print axioms FractionalPrimes.Literature.Polynomial.inverseBoundE_mul_typeI2W_le_typeI2J
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_coefficientConclusion
#print axioms FractionalPrimes.Literature.Polynomial.TypeI2LargeMInverseProgressionData.leadingError_of_descentState
#print axioms FractionalPrimes.Literature.Polynomial.typeI2LargeMSigma_eq_inv_typeI2Zeta
