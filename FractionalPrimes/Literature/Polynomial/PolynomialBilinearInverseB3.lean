module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseSecondSetup

/-!
# Formula (B3) in the bilinear polynomial inverse theorem

This file isolates the circle-distance estimate used by every successor step
of the descending coefficient recurrence in blueprint item
`lbi:inverse-theorem`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

/-- Formula (B1) split into its `i=j` term and the strictly higher-degree
tail. -/
theorem bilinearGammaLinearCoefficient_eq_head_add_tail
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (ν : ℕ → ℝ)
    (hj : 1 ≤ j) (hjd : j ≤ d) (hνtop : ν (d + 1) = 0)
    (u : ℝ) :
    bilinearGammaLinearCoefficient X ell0 d j ν u =
      u ^ (j - 1) * bilinearDerivativeCoefficient X ν j +
        u ^ (j - 1) * ∑ i ∈ Finset.Icc (j + 1) d,
          (i.choose j : ℝ) * ((ell0 : ℝ) * u - X) ^ (i - j) *
            bilinearDerivativeCoefficient X ν i := by
  rw [bilinearGammaLinearCoefficient_eq X ell0 d j ν hj hjd hνtop u]
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hjd]
  rw [Finset.sum_insert (by simp)]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero]
  ring

/-- Normalization of one higher-coefficient term to the scale occurring in
(B3). -/
theorem bilinearB3_tail_scale_identity
    (H M X e : ℝ) (i j : ℕ) (hji : j ≤ i) (hH : 0 < H) :
    (2 * M) ^ (j - 1) * (44 * H) ^ (i - j) *
        (e * X / H ^ (i + 1)) =
      2 ^ (j - 1) * 44 ^ (i - j) *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by
  have hexp : (i - j) + (j + 1) = i + 1 := by omega
  have hpow : H ^ (i + 1) = H ^ (i - j) * H ^ (j + 1) := by
    rw [← pow_add, hexp]
  rw [mul_pow, mul_pow, hpow]
  field_simp [ne_of_gt hH]

/-- A single strictly higher-degree contribution is bounded by a uniform
multiple of the target (B3) scale. -/
theorem bilinearB3_tail_term_le
    (d j i u : ℕ) (h0 : ℤ) (H M X e : ℝ)
    (hj : 1 ≤ j) (hji : j ≤ i) (hid : i ≤ d)
    (hH : 0 < H) (hM : 0 < M) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hu : (u : ℝ) ≤ 2 * M) (hh0 : |(h0 : ℝ)| ≤ 44 * H) :
    |((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j) : ℤ) : ℝ))| *
        (e * X / H ^ (i + 1)) ≤
      2 ^ (2 * d) * 44 ^ d *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by
  have hu0 : 0 ≤ (u : ℝ) := by positivity
  have h2M0 : 0 ≤ 2 * M := by positivity
  have h44H0 : 0 ≤ 44 * H := by positivity
  have herror0 : 0 ≤ e * X / H ^ (i + 1) := by positivity
  have hbase0 : 0 ≤ e * M ^ (j - 1) * X / H ^ (j + 1) := by positivity
  have huPow : (u : ℝ) ^ (j - 1) ≤ (2 * M) ^ (j - 1) :=
    pow_le_pow_left₀ hu0 hu _
  have hhPow : |(h0 : ℝ)| ^ (i - j) ≤ (44 * H) ^ (i - j) :=
    pow_le_pow_left₀ (abs_nonneg _) hh0 _
  have hchooseNat : i.choose j ≤ 2 ^ i := Nat.choose_le_two_pow i j
  have hchoose : (i.choose j : ℝ) ≤ (2 : ℝ) ^ d := by
    calc
      (i.choose j : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) := by exact_mod_cast hchooseNat
      _ = (2 : ℝ) ^ i := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hid
  have htwoPow : (2 : ℝ) ^ (j - 1) ≤ (2 : ℝ) ^ d :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hfortyFourPow : (44 : ℝ) ^ (i - j) ≤ (44 : ℝ) ^ d :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have htwoMul : (2 : ℝ) ^ d * (2 : ℝ) ^ d = (2 : ℝ) ^ (2 * d) := by
    rw [← pow_add]
    congr 1
    omega
  have habs :
      |((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j) : ℤ) : ℝ))| =
        (u : ℝ) ^ (j - 1) * (i.choose j : ℝ) *
          |(h0 : ℝ)| ^ (i - j) := by
    push_cast
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
    simp
  rw [habs]
  calc
    (u : ℝ) ^ (j - 1) * (i.choose j : ℝ) *
          |(h0 : ℝ)| ^ (i - j) * (e * X / H ^ (i + 1)) ≤
        (2 * M) ^ (j - 1) * (2 : ℝ) ^ d *
          (44 * H) ^ (i - j) * (e * X / H ^ (i + 1)) := by
      gcongr
    _ = (2 : ℝ) ^ d *
        ((2 * M) ^ (j - 1) * (44 * H) ^ (i - j) *
          (e * X / H ^ (i + 1))) := by ring
    _ = (2 : ℝ) ^ d *
        ((2 : ℝ) ^ (j - 1) * (44 : ℝ) ^ (i - j) *
          (e * M ^ (j - 1) * X / H ^ (j + 1))) := by
      rw [bilinearB3_tail_scale_identity H M X e i j hji hH]
    _ ≤ (2 : ℝ) ^ d *
        ((2 : ℝ) ^ d * (44 : ℝ) ^ d *
          (e * M ^ (j - 1) * X / H ^ (j + 1))) := by
      gcongr
    _ = (((2 : ℝ) ^ d * (2 : ℝ) ^ d) * (44 : ℝ) ^ d) *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by ring
    _ = 2 ^ (2 * d) * 44 ^ d *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by
      rw [htwoMul]

/-- The deliberately generous source constant `C_d` absorbs the number of
higher-degree terms and their uniform binomial/geometric factor. -/
theorem bilinearB3_uniform_factor_le_CValue (d : ℕ) :
    (d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d ≤
      (bilinearInverseCValue d : ℝ) := by
  have htwo : (2 : ℝ) ^ (2 * d) ≤ (2 : ℝ) ^ (2 * d + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [bilinearInverseCValue]
  push_cast
  calc
    (d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d ≤
        (d + 1 : ℝ) * 2 ^ (2 * d + 2) * 44 ^ d := by
      gcongr
    _ = 2 ^ (2 * d + 2) * (d + 1 : ℝ) * 44 ^ d := by ring

/-- The sharper raw tail constant, retaining the factor-four slack built
into `C_d`. -/
theorem bilinearB3_tail_sum_raw_le
    (d j u : ℕ) (h0 : ℤ) (H M X e : ℝ)
    (hj : 1 ≤ j) (hjd : j ≤ d)
    (hH : 0 < H) (hM : 0 < M) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hu : (u : ℝ) ≤ 2 * M) (hh0 : |(h0 : ℝ)| ≤ 44 * H) :
    (∑ i ∈ Finset.Icc (j + 1) d,
        |((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j) : ℤ) : ℝ))| *
          (e * X / H ^ (i + 1))) ≤
      ((d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d) *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by
  let S := Finset.Icc (j + 1) d
  let K : ℝ := 2 ^ (2 * d) * 44 ^ d
  let scale : ℝ := e * M ^ (j - 1) * X / H ^ (j + 1)
  have hscale0 : 0 ≤ scale := by dsimp [scale]; positivity
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hcardNat : S.card ≤ d + 1 := by
    dsimp [S]
    simp [Nat.card_Icc]
    omega
  have hcard : (S.card : ℝ) ≤ d + 1 := by exact_mod_cast hcardNat
  calc
    (∑ i ∈ Finset.Icc (j + 1) d,
        |((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j) : ℤ) : ℝ))| *
          (e * X / H ^ (i + 1))) =
        ∑ i ∈ S,
          |((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j) : ℤ) : ℝ))| *
            (e * X / H ^ (i + 1)) := by rfl
    _ ≤ ∑ _i ∈ S, K * scale := by
      apply Finset.sum_le_sum
      intro i hi
      have hiData := Finset.mem_Icc.mp hi
      simpa [K, scale] using bilinearB3_tail_term_le d j i u h0 H M X e
        hj (by omega) hiData.2 hH hM hX he hu hh0
    _ = (S.card : ℝ) * (K * scale) := by simp [Finset.sum_const]
    _ ≤ (d + 1 : ℝ) * (K * scale) := by
      exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hK0 hscale0)
    _ = ((d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d) *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by
      dsimp [K, scale]
      ring

/-- The head contribution and the raw tail constant together are absorbed by
the exact source constant `C_d A` for every `A ≥ 1`. -/
theorem bilinearB3_head_tail_factor_le
    (d : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    A + (d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d ≤
      (bilinearInverseCValue d : ℝ) * A := by
  let D : ℝ := (d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d
  have hD : 1 ≤ D := by
    dsimp [D]
    have hd1Nat : 1 ≤ d + 1 := by omega
    have hd1 : 1 ≤ (d + 1 : ℝ) := by exact_mod_cast hd1Nat
    have h2 : 1 ≤ (2 : ℝ) ^ (2 * d) := one_le_pow₀ (by norm_num)
    have h44 : 1 ≤ (44 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hd1 h2) h44
  have hC : (bilinearInverseCValue d : ℝ) = 4 * D := by
    dsimp [D, bilinearInverseCValue]
    push_cast
    have hpow : (2 : ℝ) ^ (2 * d + 2) = 4 * (2 : ℝ) ^ (2 * d) := by
      rw [pow_add]
      norm_num
      ring
    rw [hpow]
    ring
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hDA0 : 0 ≤ D * A := mul_nonneg (zero_le_one.trans hD) hA0
  have hAle : A ≤ D * A := by
    calc
      A = 1 * A := by ring
      _ ≤ D * A := mul_le_mul_of_nonneg_right hD hA0
  have hDle : D ≤ D * A := by
    calc
      D = D * 1 := by ring
      _ ≤ D * A := mul_le_mul_of_nonneg_left hA (zero_le_one.trans hD)
  dsimp [D] at hD hC ⊢
  calc
    A + (d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d ≤
        ((d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d) * A +
          ((d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d) * A :=
      add_le_add hAle hDle
    _ ≤ 4 * (((d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d) * A) := by
      nlinarith
    _ = (bilinearInverseCValue d : ℝ) * A := by
      rw [hC]
      ring

/-- Summing all higher-degree terms still fits inside the exact source
constant `C_d`. -/
theorem bilinearB3_tail_sum_le
    (d j u : ℕ) (h0 : ℤ) (H M X e : ℝ)
    (hj : 1 ≤ j) (hjd : j ≤ d)
    (hH : 0 < H) (hM : 0 < M) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hu : (u : ℝ) ≤ 2 * M) (hh0 : |(h0 : ℝ)| ≤ 44 * H) :
    (∑ i ∈ Finset.Icc (j + 1) d,
        |((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j) : ℤ) : ℝ))| *
          (e * X / H ^ (i + 1))) ≤
      (bilinearInverseCValue d : ℝ) *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by
  let S := Finset.Icc (j + 1) d
  let K : ℝ := 2 ^ (2 * d) * 44 ^ d
  let scale : ℝ := e * M ^ (j - 1) * X / H ^ (j + 1)
  have hscale0 : 0 ≤ scale := by dsimp [scale]; positivity
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hcardNat : S.card ≤ d + 1 := by
    dsimp [S]
    simp [Nat.card_Icc]
    omega
  have hcard : (S.card : ℝ) ≤ d + 1 := by exact_mod_cast hcardNat
  calc
    (∑ i ∈ Finset.Icc (j + 1) d,
        |((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j) : ℤ) : ℝ))| *
          (e * X / H ^ (i + 1))) =
        ∑ i ∈ S,
          |((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j) : ℤ) : ℝ))| *
            (e * X / H ^ (i + 1)) := by rfl
    _ ≤ ∑ _i ∈ S, K * scale := by
      apply Finset.sum_le_sum
      intro i hi
      have hiData := Finset.mem_Icc.mp hi
      simpa [K, scale] using bilinearB3_tail_term_le d j i u h0 H M X e
        hj (by omega) hiData.2 hH hM hX he hu hh0
    _ = (S.card : ℝ) * (K * scale) := by simp [Finset.sum_const]
    _ ≤ (d + 1 : ℝ) * (K * scale) := by
      exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hK0 hscale0)
    _ = ((d + 1 : ℝ) * K) * scale := by ring
    _ ≤ (bilinearInverseCValue d : ℝ) * scale :=
      mul_le_mul_of_nonneg_right
        (by
          dsimp [K]
          calc
            (d + 1 : ℝ) * (2 ^ (2 * d) * 44 ^ d) =
                (d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d := by ring
            _ ≤ (bilinearInverseCValue d : ℝ) :=
              bilinearB3_uniform_factor_le_CValue d) hscale0
    _ = (bilinearInverseCValue d : ℝ) *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by rfl

/-- Circle distance of the whole strictly higher-degree tail. -/
theorem bilinearB3_tail_distance_le
    (d j u t q₀ : ℕ) (h0 : ℤ) (X H M e : ℝ)
    (hj : 1 ≤ j) (hjd : j ≤ d)
    (hH : 0 < H) (hM : 0 < M) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hu : (u : ℝ) ≤ 2 * M) (hh0 : |(h0 : ℝ)| ≤ 44 * H)
    (ν : ℕ → ℝ)
    (hhigher : ∀ i ∈ Finset.Icc (j + 1) d,
      realDistanceToIntegers
          (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i) ≤
        e * X / H ^ (i + 1)) :
    realDistanceToIntegers
        (∑ i ∈ Finset.Icc (j + 1) d,
          ((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) *
              h0 ^ (i - j) : ℤ) : ℝ)) *
            (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i)) ≤
      (bilinearInverseCValue d : ℝ) *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by
  have hweighted := realDistanceToIntegers_intWeightedSum_le
    (Finset.Icc (j + 1) d)
    (fun i => (u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j))
    (fun i => (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i))
    (fun i => e * X / H ^ (i + 1)) hhigher
  exact hweighted.trans
    (bilinearB3_tail_sum_le d j u h0 H M X e hj hjd hH hM hX he hu hh0)

/-- Circle distance of the higher-degree tail with the factor-four slack
retained. -/
theorem bilinearB3_tail_distance_raw_le
    (d j u t q₀ : ℕ) (h0 : ℤ) (X H M e : ℝ)
    (hj : 1 ≤ j) (hjd : j ≤ d)
    (hH : 0 < H) (hM : 0 < M) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hu : (u : ℝ) ≤ 2 * M) (hh0 : |(h0 : ℝ)| ≤ 44 * H)
    (ν : ℕ → ℝ)
    (hhigher : ∀ i ∈ Finset.Icc (j + 1) d,
      realDistanceToIntegers
          (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i) ≤
        e * X / H ^ (i + 1)) :
    realDistanceToIntegers
        (∑ i ∈ Finset.Icc (j + 1) d,
          ((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) *
              h0 ^ (i - j) : ℤ) : ℝ)) *
            (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i)) ≤
      ((d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d) *
        (e * M ^ (j - 1) * X / H ^ (j + 1)) := by
  have hweighted := realDistanceToIntegers_intWeightedSum_le
    (Finset.Icc (j + 1) d)
    (fun i => (u : ℤ) ^ (j - 1) * (i.choose j : ℤ) * h0 ^ (i - j))
    (fun i => (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i))
    (fun i => e * X / H ^ (i + 1)) hhigher
  exact hweighted.trans
    (bilinearB3_tail_sum_raw_le d j u h0 H M X e
      hj hjd hH hM hX he hu hh0)

/-- Algebraic form used for the circle subtraction: the desired `j`th term
is the first-recurrence term minus the strictly higher-degree tail. -/
theorem bilinearB3_head_eq_local_sub_tail
    (X : ℝ) (ell0 : ℤ) (d j u t q₀ : ℕ) (ν : ℕ → ℝ) (h0 : ℤ)
    (hj : 1 ≤ j) (hjd : j ≤ d) (hνtop : ν (d + 1) = 0)
    (hoffset : (ell0 : ℝ) * (u : ℝ) - X = (h0 : ℝ)) :
    (((t * q₀ : ℕ) : ℝ) * (u : ℝ) ^ (j - 1) *
        bilinearDerivativeCoefficient X ν j) =
      (t : ℝ) * ((q₀ : ℝ) *
        bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ)) -
      ∑ i ∈ Finset.Icc (j + 1) d,
        ((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) *
            h0 ^ (i - j) : ℤ) : ℝ)) *
          (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i) := by
  have hsplit := bilinearGammaLinearCoefficient_eq_head_add_tail
    X ell0 d j ν hj hjd hνtop (u : ℝ)
  have htail :
      (∑ i ∈ Finset.Icc (j + 1) d,
        ((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) *
            h0 ^ (i - j) : ℤ) : ℝ)) *
          (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i)) =
        (((t * q₀ : ℕ) : ℝ) * (u : ℝ) ^ (j - 1)) *
          ∑ i ∈ Finset.Icc (j + 1) d,
            (i.choose j : ℝ) * ((ell0 : ℝ) * (u : ℝ) - X) ^ (i - j) *
              bilinearDerivativeCoefficient X ν i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    rw [hoffset]
    ring
  rw [hsplit, htail]
  push_cast
  ring

/-- Formula (B3): the first-recurrence local estimate, the exact integer
offset identity, and the already controlled higher coefficients imply the
uniform error used in the second recurrence. -/
theorem bilinearFirstToSecondRecurrence_error
    (d j u t q₀ : ℕ) (X H M A e : ℝ) (ell0 h0 : ℤ) (ν : ℕ → ℝ)
    (hj : 1 ≤ j) (hjd : j ≤ d) (hνtop : ν (d + 1) = 0)
    (hH : 0 < H) (hM : 0 < M) (hX : 0 ≤ X)
    (hA : 1 ≤ A) (he : 0 ≤ e) (hte : (t : ℝ) ≤ e)
    (hu : (u : ℝ) ≤ 2 * M)
    (hoffset : (ell0 : ℝ) * (u : ℝ) - X = (h0 : ℝ))
    (hh0 : |(h0 : ℝ)| ≤ 44 * H)
    (hfirst : realDistanceToIntegers
        ((q₀ : ℝ) * bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ)) ≤
      A * M ^ (j - 1) * X / H ^ (j + 1))
    (hhigher : ∀ i ∈ Finset.Icc (j + 1) d,
      realDistanceToIntegers
          (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i) ≤
        e * X / H ^ (i + 1)) :
    realDistanceToIntegers
        (((t * q₀ : ℕ) : ℝ) * (u : ℝ) ^ (j - 1) *
          bilinearDerivativeCoefficient X ν j) ≤
      (bilinearInverseCValue d : ℝ) * A * e *
        M ^ (j - 1) * X / H ^ (j + 1) := by
  let scale : ℝ := M ^ (j - 1) * X / H ^ (j + 1)
  let D : ℝ := (d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d
  have hscale0 : 0 ≤ scale := by dsimp [scale]; positivity
  have hfirst' : realDistanceToIntegers
        ((q₀ : ℝ) * bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ)) ≤
      A * scale := by
    calc
      realDistanceToIntegers
          ((q₀ : ℝ) * bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ)) ≤
        A * M ^ (j - 1) * X / H ^ (j + 1) := hfirst
      _ = A * scale := by
        dsimp [scale]
        ring
  have hlocalMul := realDistanceToIntegers_int_mul_le (t : ℤ)
    ((q₀ : ℝ) * bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ))
  have hlocal :
      realDistanceToIntegers
          ((t : ℝ) * ((q₀ : ℝ) *
            bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ))) ≤
        A * e * scale := by
    calc
      realDistanceToIntegers
          ((t : ℝ) * ((q₀ : ℝ) *
            bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ))) ≤
          |(t : ℝ)| * realDistanceToIntegers
            ((q₀ : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ)) := hlocalMul
      _ = (t : ℝ) * realDistanceToIntegers
            ((q₀ : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ)) := by
        rw [abs_of_nonneg (Nat.cast_nonneg t)]
      _ ≤ (t : ℝ) * (A * scale) := by
        apply mul_le_mul_of_nonneg_left
        · exact hfirst'
        · positivity
      _ ≤ e * (A * scale) := by
        exact mul_le_mul_of_nonneg_right hte (mul_nonneg (zero_le_one.trans hA) hscale0)
      _ = A * e * scale := by ring
  have htail := bilinearB3_tail_distance_raw_le
    d j u t q₀ h0 X H M e hj hjd hH hM hX he hu hh0 ν hhigher
  have htail' :
      realDistanceToIntegers
          (∑ i ∈ Finset.Icc (j + 1) d,
            ((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) *
                h0 ^ (i - j) : ℤ) : ℝ)) *
              (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i)) ≤
        D * (e * scale) := by
    calc
      realDistanceToIntegers
          (∑ i ∈ Finset.Icc (j + 1) d,
            ((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) *
                h0 ^ (i - j) : ℤ) : ℝ)) *
              (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i)) ≤
        ((d + 1 : ℝ) * 2 ^ (2 * d) * 44 ^ d) *
          (e * M ^ (j - 1) * X / H ^ (j + 1)) := htail
      _ = D * (e * scale) := by
        dsimp [D, scale]
        ring
  have hidentity := bilinearB3_head_eq_local_sub_tail
    X ell0 d j u t q₀ ν h0 hj hjd hνtop hoffset
  rw [hidentity]
  calc
    realDistanceToIntegers
        ((t : ℝ) * ((q₀ : ℝ) *
            bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ)) -
          ∑ i ∈ Finset.Icc (j + 1) d,
            ((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) *
                h0 ^ (i - j) : ℤ) : ℝ)) *
              (((t * q₀ : ℕ) : ℝ) * bilinearDerivativeCoefficient X ν i)) ≤
        realDistanceToIntegers
            ((t : ℝ) * ((q₀ : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j ν (u : ℝ))) +
          realDistanceToIntegers
            (∑ i ∈ Finset.Icc (j + 1) d,
              ((((u : ℤ) ^ (j - 1) * (i.choose j : ℤ) *
                  h0 ^ (i - j) : ℤ) : ℝ)) *
                (((t * q₀ : ℕ) : ℝ) *
                  bilinearDerivativeCoefficient X ν i)) :=
      realDistanceToIntegers_sub_le _ _
    _ ≤ A * e * scale + D * (e * scale) := by
      exact add_le_add hlocal htail'
    _ = (A + D) * (e * scale) := by ring
    _ ≤ ((bilinearInverseCValue d : ℝ) * A) * (e * scale) :=
      mul_le_mul_of_nonneg_right
        (bilinearB3_head_tail_factor_le d A hA) (mul_nonneg he hscale0)
    _ = (bilinearInverseCValue d : ℝ) * A * e *
        M ^ (j - 1) * X / H ^ (j + 1) := by
      dsimp [scale]
      ring

#print axioms bilinearGammaLinearCoefficient_eq_head_add_tail
#print axioms bilinearB3_tail_term_le
#print axioms bilinearB3_tail_sum_le
#print axioms bilinearB3_tail_distance_le
#print axioms bilinearB3_head_eq_local_sub_tail
#print axioms bilinearFirstToSecondRecurrence_error

end


end FractionalPrimes.Literature.Polynomial
