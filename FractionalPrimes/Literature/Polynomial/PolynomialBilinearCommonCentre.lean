module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearWindowEnergy

/-!
# A common bilinear integer centre and coefficient algebra

This file formalizes blueprint item `lbi:common-centre`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

noncomputable section

/-- The common left-index origin `ell₀ = floor (X/u - 21s)`. -/
def bilinearCommonLeftBase (X s : ℝ) (u : ℕ) : ℤ :=
  Int.floor (X / (u : ℝ) - 21 * s)

/-- The common left-index length `N₀ = ceil (24s)`. -/
def bilinearCommonLeftLength (s : ℝ) : ℕ := Nat.ceil (24 * s)

/-- The paper's centered presentation
`P(t) = \sum_{i=0}^d ν_i (t-X)^i`. -/
def bilinearCenteredPhase (X : ℝ) (d : ℕ) (ν : ℕ → ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.C (ν i) * (Polynomial.X - Polynomial.C X) ^ i

/-- The polynomial
`Γ_j(z) = z^j \sum_{i=j}^d choose(i,j) ν_i (ell₀ z-X)^(i-j)`. -/
def bilinearGammaPolynomial (X : ℝ) (ell0 : ℤ)
    (d j : ℕ) (ν : ℕ → ℝ) : Polynomial ℝ :=
  Polynomial.X ^ j *
    ∑ i ∈ Finset.Icc j d,
      Polynomial.C ((i.choose j : ℝ) * ν i) *
        (Polynomial.C (ell0 : ℝ) * Polynomial.X - Polynomial.C X) ^ (i - j)

/-- The centered coefficients of `t P'(t)` used in the bilinear descent. -/
def bilinearDerivativeCoefficient (X : ℝ) (ν : ℕ → ℝ) (i : ℕ) : ℝ :=
  (i : ℝ) * ν i + (i + 1 : ℕ) * X * ν (i + 1)

private theorem bilinearCommon_coeff_affine_pow
    {a b : ℝ} (ha : a ≠ 0) (n j : ℕ) :
    ((Polynomial.C b + Polynomial.C a * Polynomial.X) ^ n).coeff j =
      (n.choose j : ℝ) * a ^ j * b ^ (n - j) := by
  have hfactor :
      Polynomial.C b + Polynomial.C a * Polynomial.X =
        Polynomial.C a * (Polynomial.X + Polynomial.C (b / a)) := by
    rw [mul_add, ← Polynomial.C_mul]
    field_simp [ha]
    ring
  rw [hfactor, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  by_cases hj : j ≤ n
  · have hpow : a ^ n = a ^ j * a ^ (n - j) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    rw [hpow, div_pow]
    field_simp [ha]
  · have hlt : n < j := Nat.lt_of_not_ge hj
    simp [Nat.choose_eq_zero_of_lt hlt]

@[simp]
theorem bilinearGammaPolynomial_eval (X : ℝ) (ell0 : ℤ)
    (d j : ℕ) (ν : ℕ → ℝ) (z : ℝ) :
    (bilinearGammaPolynomial X ell0 d j ν).eval z =
      z ^ j * ∑ i ∈ Finset.Icc j d,
        (i.choose j : ℝ) * ν i * ((ell0 : ℝ) * z - X) ^ (i - j) := by
  simp only [bilinearGammaPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_C]
  apply congr_arg (z ^ j * ·)
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  simp

/-- The degree-`j` coefficient after the affine substitution
`t ↦ (ell₀+t)m` is the paper's `Γ_j(m)`. -/
theorem bilinearCenteredPhase_comp_coeff
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (ν : ℕ → ℝ)
    (m : ℕ) (hm : 0 < m) :
    ((bilinearCenteredPhase X d ν).comp
      (Polynomial.C ((ell0 : ℝ) * (m : ℝ)) +
        Polynomial.C (m : ℝ) * Polynomial.X)).coeff j =
      (bilinearGammaPolynomial X ell0 d j ν).eval (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [bilinearGammaPolynomial_eval]
  unfold bilinearCenteredPhase
  rw [Polynomial.sum_comp, Polynomial.finsetSum_coeff]
  have hterm (i : ℕ) :
      ((Polynomial.C (ν i) * (Polynomial.X - Polynomial.C X) ^ i).comp
        (Polynomial.C ((ell0 : ℝ) * (m : ℝ)) +
          Polynomial.C (m : ℝ) * Polynomial.X)).coeff j =
        (i.choose j : ℝ) * ν i * (m : ℝ) ^ j *
          ((ell0 : ℝ) * (m : ℝ) - X) ^ (i - j) := by
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp]
    rw [Polynomial.coeff_C_mul]
    have hbase :
        Polynomial.C ((ell0 : ℝ) * (m : ℝ)) +
              Polynomial.C (m : ℝ) * Polynomial.X - Polynomial.C X =
          Polynomial.C ((ell0 : ℝ) * (m : ℝ) - X) +
              Polynomial.C (m : ℝ) * Polynomial.X := by
      rw [Polynomial.C_sub]
      ring
    rw [hbase, bilinearCommon_coeff_affine_pow hmR]
    ring
  simp_rw [hterm]
  have hrange : Finset.range (d + 1) = Finset.Icc 0 d := by
    ext i
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hrange]
  calc
    (∑ i ∈ Finset.Icc 0 d,
        (i.choose j : ℝ) * ν i * (m : ℝ) ^ j *
          ((ell0 : ℝ) * (m : ℝ) - X) ^ (i - j)) =
        ∑ i ∈ Finset.Icc j d,
          (i.choose j : ℝ) * ν i * (m : ℝ) ^ j *
            ((ell0 : ℝ) * (m : ℝ) - X) ^ (i - j) := by
      symm
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_Icc] at hi ⊢
        exact ⟨Nat.zero_le _, hi.2⟩
      · intro i hi hni
        have hij : i < j := by
          simp only [Finset.mem_Icc] at hi hni
          omega
        simp [Nat.choose_eq_zero_of_lt hij]
    _ = (m : ℝ) ^ j * ∑ i ∈ Finset.Icc j d,
          (i.choose j : ℝ) * ν i *
            ((ell0 : ℝ) * (m : ℝ) - X) ^ (i - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Subtracting the two affine substitutions gives exactly
`Γ_j(m)-Γ_j(m')` in degree `j`. -/
theorem bilinearCommonCentre_phase_coefficient
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (ν : ℕ → ℝ)
    (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') :
    (((bilinearCenteredPhase X d ν).comp
        (Polynomial.C ((ell0 : ℝ) * (m : ℝ)) +
          Polynomial.C (m : ℝ) * Polynomial.X)) -
      ((bilinearCenteredPhase X d ν).comp
        (Polynomial.C ((ell0 : ℝ) * (m' : ℝ)) +
          Polynomial.C (m' : ℝ) * Polynomial.X))).coeff j =
      (bilinearGammaPolynomial X ell0 d j ν).eval (m : ℝ) -
        (bilinearGammaPolynomial X ell0 d j ν).eval (m' : ℝ) := by
  rw [Polynomial.coeff_sub,
    bilinearCenteredPhase_comp_coeff X ell0 d j ν m hm,
    bilinearCenteredPhase_comp_coeff X ell0 d j ν m' hm']

private theorem bilinearCommon_Icc_eq_image_range
    (j d : ℕ) (hjd : j ≤ d) :
    Finset.Icc j d =
      (Finset.range (d - j + 1)).image (fun k => j + k) := by
  ext i
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hji, hid⟩
    refine ⟨i - j, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨k, hk, rfl⟩
    omega

private theorem bilinearGammaPolynomial_eq_offset_sum
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (ν : ℕ → ℝ)
    (hjd : j ≤ d) :
    bilinearGammaPolynomial X ell0 d j ν =
      Polynomial.X ^ j *
        ∑ k ∈ Finset.range (d - j + 1),
          Polynomial.C (((j + k).choose j : ℝ) * ν (j + k)) *
            (Polynomial.C (ell0 : ℝ) * Polynomial.X - Polynomial.C X) ^ k := by
  unfold bilinearGammaPolynomial
  rw [bilinearCommon_Icc_eq_image_range j d hjd, Finset.sum_image]
  · simp
  · intro k hk k' hk' hEq
    exact Nat.add_left_cancel hEq

private theorem bilinearGammaPolynomial_derivative_eval
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (ν : ℕ → ℝ)
    (hjd : j ≤ d) (u : ℝ) :
    (bilinearGammaPolynomial X ell0 d j ν).derivative.eval u =
      ∑ k ∈ Finset.range (d - j + 1),
        ((j + k).choose j : ℝ) * ν (j + k) *
          ((j : ℝ) * u ^ (j - 1) * ((ell0 : ℝ) * u - X) ^ k +
            u ^ j * (k : ℝ) * (ell0 : ℝ) *
              ((ell0 : ℝ) * u - X) ^ (k - 1)) := by
  rw [bilinearGammaPolynomial_eq_offset_sum X ell0 d j ν hjd,
    Finset.mul_sum, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.derivative_mul, Polynomial.derivative_X_pow,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.derivative_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_zero, Polynomial.eval_one]
  ring

private theorem bilinearCommon_natCast_mul_pow_pred (k : ℕ) (h : ℝ) :
    (k : ℝ) * h * h ^ (k - 1) = (k : ℝ) * h ^ k := by
  cases k with
  | zero => simp
  | succ k => simp [pow_succ]; ring

/-- The finite reindexing identity used for the `X ν_{i+1}` contribution
in (B1).  The last term on the right vanishes by the source convention
`ν_{d+1}=0`. -/
private theorem bilinearCommon_shifted_sum
    (j n : ℕ) (X h : ℝ) (ν : ℕ → ℝ)
    (hνtop : ν (j + n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 1),
        ((j + k).choose j : ℝ) * ν (j + k) * (k : ℝ) * X * h ^ (k - 1)) =
      ∑ k ∈ Finset.range (n + 1),
        ((j + k).choose j : ℝ) * (j + k + 1 : ℕ) * X *
          ν (j + k + 1) * h ^ k := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
  have hlast :
      ((j + n).choose j : ℝ) * (j + n + 1 : ℕ) * X *
          ν (j + n + 1) * h ^ n = 0 := by
    rw [hνtop]
    ring
  rw [hlast]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hchooseNat := Nat.choose_mul_succ_eq (j + k) j
  have hsub : j + k + 1 - j = k + 1 := by omega
  rw [hsub] at hchooseNat
  have hchoose :
      (((j + k).choose j : ℕ) : ℝ) * (j + k + 1 : ℕ) =
        (((j + k + 1).choose j : ℕ) : ℝ) * (k + 1 : ℕ) := by
    exact_mod_cast hchooseNat
  rw [show j + (k + 1) = j + k + 1 by omega,
    show k + 1 - 1 = k by omega]
  calc
    ((j + k + 1).choose j : ℝ) * ν (j + k + 1) * (k + 1 : ℕ) * X * h ^ k =
        (((j + k + 1).choose j : ℝ) * (k + 1 : ℕ)) *
          (ν (j + k + 1) * X * h ^ k) := by ring
    _ = (((j + k).choose j : ℝ) * (j + k + 1 : ℕ)) *
          (ν (j + k + 1) * X * h ^ k) := by rw [← hchoose]
    _ = ((j + k).choose j : ℝ) * (j + k + 1 : ℕ) * X *
          ν (j + k + 1) * h ^ k := by ring

private theorem bilinearCommon_derivative_sum_identity
    (j n : ℕ) (hj : 1 ≤ j) (X : ℝ) (ell0 : ℤ)
    (u : ℝ) (ν : ℕ → ℝ) (hνtop : ν (j + n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 1),
        ((j + k).choose j : ℝ) * ν (j + k) *
          ((j : ℝ) * u ^ (j - 1) * ((ell0 : ℝ) * u - X) ^ k +
            u ^ j * (k : ℝ) * (ell0 : ℝ) *
              ((ell0 : ℝ) * u - X) ^ (k - 1))) =
      u ^ (j - 1) *
        ∑ k ∈ Finset.range (n + 1),
          ((j + k).choose j : ℝ) * ((ell0 : ℝ) * u - X) ^ k *
            bilinearDerivativeCoefficient X ν (j + k) := by
  let h : ℝ := (ell0 : ℝ) * u - X
  have hupow : u ^ j = u ^ (j - 1) * u := by
    calc
      u ^ j = u ^ ((j - 1) + 1) := by rw [Nat.sub_add_cancel hj]
      _ = u ^ (j - 1) * u := by rw [pow_succ]
  have huell : u * (ell0 : ℝ) = h + X := by
    dsimp [h]
    ring
  have hpoint (k : ℕ) :
      ((j + k).choose j : ℝ) * ν (j + k) *
          ((j : ℝ) * u ^ (j - 1) * h ^ k +
            u ^ j * (k : ℝ) * (ell0 : ℝ) * h ^ (k - 1)) =
        u ^ (j - 1) *
          (((j + k).choose j : ℝ) * (j + k : ℕ) * ν (j + k) * h ^ k +
            ((j + k).choose j : ℝ) * ν (j + k) * (k : ℝ) * X *
              h ^ (k - 1)) := by
    calc
      ((j + k).choose j : ℝ) * ν (j + k) *
          ((j : ℝ) * u ^ (j - 1) * h ^ k +
            u ^ j * (k : ℝ) * (ell0 : ℝ) * h ^ (k - 1)) =
          u ^ (j - 1) * (((j + k).choose j : ℝ) * ν (j + k) *
            ((j : ℝ) * h ^ k + (k : ℝ) * (u * (ell0 : ℝ)) * h ^ (k - 1))) := by
        rw [hupow]
        ring
      _ = u ^ (j - 1) * (((j + k).choose j : ℝ) * ν (j + k) *
            ((j : ℝ) * h ^ k + (k : ℝ) * (h + X) * h ^ (k - 1))) := by
        rw [huell]
      _ = u ^ (j - 1) * (((j + k).choose j : ℝ) * ν (j + k) *
            ((j : ℝ) * h ^ k +
              ((k : ℝ) * h * h ^ (k - 1) +
                (k : ℝ) * X * h ^ (k - 1)))) := by ring
      _ = u ^ (j - 1) *
          (((j + k).choose j : ℝ) * (j + k : ℕ) * ν (j + k) * h ^ k +
            ((j + k).choose j : ℝ) * ν (j + k) * (k : ℝ) * X *
              h ^ (k - 1)) := by
        rw [bilinearCommon_natCast_mul_pow_pred k h]
        push_cast
        ring
  simp_rw [show (ell0 : ℝ) * u - X = h by rfl, hpoint]
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    bilinearCommon_shifted_sum j n X h ν hνtop]
  apply congr_arg (fun z : ℝ => u ^ (j - 1) * z)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold bilinearDerivativeCoefficient
  push_cast
  ring

/-- The degree-one coefficient of `Γ_j(u+t)`. -/
def bilinearGammaLinearCoefficient (X : ℝ) (ell0 : ℤ)
    (d j : ℕ) (ν : ℕ → ℝ) (u : ℝ) : ℝ :=
  ((bilinearGammaPolynomial X ell0 d j ν).comp
    (Polynomial.C u + Polynomial.X)).coeff 1

/-- Formula (B1): the linear coefficient of `Γ_j(u+t)` is the stated
finite sum of the derivative coefficients `A_i`. -/
theorem bilinearGammaLinearCoefficient_eq
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (ν : ℕ → ℝ)
    (hj : 1 ≤ j) (hjd : j ≤ d) (hνtop : ν (d + 1) = 0)
    (u : ℝ) :
    bilinearGammaLinearCoefficient X ell0 d j ν u =
      u ^ (j - 1) * ∑ i ∈ Finset.Icc j d,
        (i.choose j : ℝ) * ((ell0 : ℝ) * u - X) ^ (i - j) *
          bilinearDerivativeCoefficient X ν i := by
  let G := bilinearGammaPolynomial X ell0 d j ν
  have hshift : Polynomial.C u + Polynomial.X =
      Polynomial.X + Polynomial.C u := by ring
  have hcoeff :
      bilinearGammaLinearCoefficient X ell0 d j ν u =
        G.derivative.eval u := by
    unfold bilinearGammaLinearCoefficient
    rw [hshift, ← Polynomial.taylor_apply, Polynomial.taylor_coeff_one]
  rw [hcoeff]
  have hνoffset : ν (j + (d - j) + 1) = 0 := by
    rw [Nat.add_sub_of_le hjd]
    exact hνtop
  calc
    G.derivative.eval u =
        ∑ k ∈ Finset.range (d - j + 1),
          ((j + k).choose j : ℝ) * ν (j + k) *
            ((j : ℝ) * u ^ (j - 1) * ((ell0 : ℝ) * u - X) ^ k +
              u ^ j * (k : ℝ) * (ell0 : ℝ) *
                ((ell0 : ℝ) * u - X) ^ (k - 1)) := by
      exact bilinearGammaPolynomial_derivative_eval X ell0 d j ν hjd u
    _ = u ^ (j - 1) *
        ∑ k ∈ Finset.range (d - j + 1),
          ((j + k).choose j : ℝ) * ((ell0 : ℝ) * u - X) ^ k *
            bilinearDerivativeCoefficient X ν (j + k) :=
      bilinearCommon_derivative_sum_identity j (d - j) hj X ell0 u ν hνoffset
    _ = u ^ (j - 1) * ∑ i ∈ Finset.Icc j d,
        (i.choose j : ℝ) * ((ell0 : ℝ) * u - X) ^ (i - j) *
          bilinearDerivativeCoefficient X ν i := by
      apply congr_arg (fun z : ℝ => u ^ (j - 1) * z)
      rw [bilinearCommon_Icc_eq_image_range j d hjd, Finset.sum_image]
      · simp
      · intro k hk k' hk' hEq
        exact Nat.add_left_cancel hEq

/-- If the centre `X` is an integer, the common-centre error is the cast of
an integer, exactly as required by the circle-norm descent. -/
theorem bilinearCommonCentre_offset_intCast
    (X0 ell0 : ℤ) (u : ℕ) :
    (ell0 : ℝ) * (u : ℝ) - (X0 : ℝ) =
      ((ell0 * (u : ℤ) - X0 : ℤ) : ℝ) := by
  push_cast
  ring

private theorem bilinearCommon_windowRadius_bounds (r : ℝ) (hr : 1 ≤ r) :
    4 * r ≤ (bilinearWindowRadius r : ℝ) ∧
      (bilinearWindowRadius r : ℝ) ≤ 5 * r := by
  constructor
  · exact Nat.le_ceil (4 * r)
  · have hlt : (bilinearWindowRadius r : ℝ) < 4 * r + 1 := by
      dsimp [bilinearWindowRadius]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith

/-- The exact interval estimates used to shift every contributing left index
to the same integer interval `{1,...,N₀}`. -/
theorem bilinearCommonCentre_index_bounds
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (u m : ℕ) (hu : u ∈ bilinearWindowCenters M)
    (hm : m ∈ bilinearWindow M (H / L) u)
    (ell : ℤ)
    (hell : X < (ell : ℝ) * (m : ℝ) ∧
      (ell : ℝ) * (m : ℝ) ≤ X + H) :
    1 ≤ ell - bilinearCommonLeftBase X (H / M) u ∧
      ell - bilinearCommonLeftBase X (H / M) u ≤
        (bilinearCommonLeftLength (H / M) : ℤ) ∧
      (bilinearCommonLeftLength (H / M) : ℝ) ≤ 25 * (H / M) ∧
      |(bilinearCommonLeftBase X (H / M) u : ℝ) * (u : ℝ) - X| ≤ 44 * H := by
  have hXpos : 0 < X := by rw [hX]; positivity
  have hHpos : 0 < H := by
    have hLH : L ≤ H := by simpa using (le_div_iff₀ hL).mp hr
    linarith
  have hrpos : 0 < H / L := by positivity
  have hspos : 0 < H / M := by positivity
  have huData := (mem_bilinearWindowCenters M u).mp hu
  have hmData := (mem_bilinearWindow M (H / L) u m).mp hm
  have hmRight := (mem_bilinearRightSet M m).mp hmData.1
  have huPosNat : 0 < u := by omega
  have hmPosNat : 0 < m := by omega
  have huPos : 0 < (u : ℝ) := by exact_mod_cast huPosNat
  have hmPos : 0 < (m : ℝ) := by exact_mod_cast hmPosNat
  have hMleH : M ≤ H := by
    have := (le_div_iff₀ hM).mp hs
    simpa using this
  have hR := bilinearCommon_windowRadius_bounds (H / L) (by linarith)
  have hmu : (m : ℝ) - (u : ℝ) ≤
      (bilinearWindowRadius (H / L) : ℝ) := by
    have hmle : (m : ℝ) ≤
        (u : ℝ) + (bilinearWindowRadius (H / L) : ℝ) := by
      exact_mod_cast hmData.2.2
    linarith
  have hmu5 : (m : ℝ) - (u : ℝ) ≤ 5 * (H / L) := hmu.trans hR.2
  have hdenLower : M ^ 2 / 2 < (u : ℝ) * (m : ℝ) := by
    have huLower := huData.2.1
    have hmLower := hmRight.2.1
    nlinarith [mul_pos (sub_pos.mpr hmLower) huPos]
  have hdiffIdentity :
      X / (u : ℝ) - X / (m : ℝ) =
        X * ((m : ℝ) - (u : ℝ)) / ((u : ℝ) * (m : ℝ)) := by
    field_simp [huPos.ne', hmPos.ne']
  have hnumBound : X * ((m : ℝ) - (u : ℝ)) ≤ 5 * H * M := by
    have hmuNonneg : 0 ≤ (m : ℝ) - (u : ℝ) := by
      have hum : (u : ℝ) < (m : ℝ) := by exact_mod_cast hmData.2.1
      linarith
    calc
      X * ((m : ℝ) - (u : ℝ)) ≤ X * (5 * (H / L)) :=
        mul_le_mul_of_nonneg_left hmu5 hXpos.le
      _ = 5 * H * M := by rw [hX]; field_simp [hL.ne']
  have hdiffUpper : X / (u : ℝ) - X / (m : ℝ) < 21 * (H / M) := by
    rw [hdiffIdentity]
    apply (div_lt_iff₀ (mul_pos huPos hmPos)).2
    have htarget : 5 * H * M <
        21 * (H / M) * ((u : ℝ) * (m : ℝ)) := by
      have hscale : 10 * H * M <
          21 * (H / M) * ((u : ℝ) * (m : ℝ)) := by
        calc
          10 * H * M = 20 * (H / M) * (M ^ 2 / 2) := by
            field_simp [hM.ne']
            ring
          _ < 20 * (H / M) * ((u : ℝ) * (m : ℝ)) := by
            exact mul_lt_mul_of_pos_left hdenLower (by positivity)
          _ < 21 * (H / M) * ((u : ℝ) * (m : ℝ)) := by
            nlinarith [mul_pos (show 0 < H / M by positivity)
              (mul_pos huPos hmPos)]
      have hfiveTen : 5 * H * M < 10 * H * M := by
        nlinarith [mul_pos hHpos hM]
      exact hfiveTen.trans hscale
    exact hnumBound.trans_lt htarget
  let ell0 := bilinearCommonLeftBase X (H / M) u
  let N0 := bilinearCommonLeftLength (H / M)
  have hell0Le : (ell0 : ℝ) ≤ X / (u : ℝ) - 21 * (H / M) := by
    dsimp [ell0, bilinearCommonLeftBase]
    exact Int.floor_le _
  have hell0Lower : X / (u : ℝ) - 21 * (H / M) < (ell0 : ℝ) + 1 := by
    dsimp [ell0, bilinearCommonLeftBase]
    exact Int.lt_floor_add_one _
  have hell0Xm : (ell0 : ℝ) < X / (m : ℝ) := by
    calc
      (ell0 : ℝ) ≤ X / (u : ℝ) - 21 * (H / M) := hell0Le
      _ < X / (m : ℝ) := by linarith
  have hXdivmLtEll : X / (m : ℝ) < (ell : ℝ) := by
    exact (div_lt_iff₀ hmPos).2 (by simpa [mul_comm] using hell.1)
  have hell0ell : ell0 < ell := by exact_mod_cast (hell0Xm.trans hXdivmLtEll)
  have hshiftLower : 1 ≤ ell - ell0 := by omega
  have hellUpper : (ell : ℝ) ≤ X / (u : ℝ) + 2 * (H / M) := by
    have hdivm : (ell : ℝ) ≤ (X + H) / (m : ℝ) :=
      (le_div_iff₀ hmPos).2 (by simpa [mul_comm] using hell.2)
    have hdivu : (X + H) / (m : ℝ) ≤ (X + H) / (u : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) huPos
      exact_mod_cast (Nat.le_of_lt hmData.2.1)
    have hHu : H / (u : ℝ) ≤ 2 * (H / M) := by
      apply (div_le_iff₀ huPos).2
      have huLower := huData.2.1
      have hHM : H = (H / M) * M := by field_simp [hM.ne']
      calc
        H = (H / M) * M := hHM
        _ ≤ (H / M) * (2 * (u : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hspos.le
        _ = 2 * (H / M) * (u : ℝ) := by ring
    calc
      (ell : ℝ) ≤ (X + H) / (m : ℝ) := hdivm
      _ ≤ (X + H) / (u : ℝ) := hdivu
      _ = X / (u : ℝ) + H / (u : ℝ) := by ring
      _ ≤ X / (u : ℝ) + 2 * (H / M) := by linarith
  have hshiftUpperReal : ((ell - ell0 : ℤ) : ℝ) < 24 * (H / M) := by
    rw [Int.cast_sub]
    linarith
  have hN0Lower : 24 * (H / M) ≤ (N0 : ℝ) := by
    dsimp [N0, bilinearCommonLeftLength]
    exact Nat.le_ceil _
  have hshiftUpper : ell - ell0 ≤ (N0 : ℤ) := by
    have hlt : ((ell - ell0 : ℤ) : ℝ) < (N0 : ℝ) :=
      hshiftUpperReal.trans_le hN0Lower
    exact_mod_cast hlt.le
  have hN0Upper : (N0 : ℝ) ≤ 25 * (H / M) := by
    have hceilLt : (N0 : ℝ) < 24 * (H / M) + 1 := by
      dsimp [N0, bilinearCommonLeftLength]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith
  have hoffsetNonpos : (ell0 : ℝ) * (u : ℝ) - X ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_right hell0Le huPos.le
    have hsnonneg : 0 ≤ 21 * (H / M) * (u : ℝ) := by positivity
    calc
      (ell0 : ℝ) * (u : ℝ) - X ≤
          (X / (u : ℝ) - 21 * (H / M)) * (u : ℝ) - X := by linarith
      _ = -(21 * (H / M) * (u : ℝ)) := by
        field_simp [huPos.ne']
        ring
      _ ≤ 0 := neg_nonpos.mpr hsnonneg
  have hoffsetUpper : X - (ell0 : ℝ) * (u : ℝ) ≤ 44 * H := by
    have hraw : X - (ell0 : ℝ) * (u : ℝ) <
        (21 * (H / M) + 1) * (u : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hell0Lower huPos
      field_simp [huPos.ne'] at hmul ⊢
      linarith
    have huUpper := huData.2.2
    have hcoef0 : 0 ≤ 21 * (H / M) + 1 := by positivity
    have hbound : (21 * (H / M) + 1) * (u : ℝ) ≤
        (21 * (H / M) + 1) * (2 * M) :=
      mul_le_mul_of_nonneg_left huUpper hcoef0
    have hidentity : (21 * (H / M) + 1) * (2 * M) = 42 * H + 2 * M := by
      field_simp [hM.ne']
      ring
    rw [hidentity] at hbound
    linarith
  have habs : |(ell0 : ℝ) * (u : ℝ) - X| ≤ 44 * H := by
    rw [abs_of_nonpos hoffsetNonpos]
    linarith
  exact ⟨hshiftLower, hshiftUpper, hN0Upper, habs⟩

/-- Blueprint lemma `lbi:common-centre`, with the interval bounds, both exact
coefficient identities, and the conditional integrality assertion bundled
together. -/
theorem bilinearCommonCentre
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (u : ℕ) (hu : u ∈ bilinearWindowCenters M)
    (d : ℕ) (ν : ℕ → ℝ) (hνtop : ν (d + 1) = 0) :
    (∀ (m : ℕ), m ∈ bilinearWindow M (H / L) u →
      ∀ ell : ℤ,
        X < (ell : ℝ) * (m : ℝ) ∧
          (ell : ℝ) * (m : ℝ) ≤ X + H →
        1 ≤ ell - bilinearCommonLeftBase X (H / M) u ∧
          ell - bilinearCommonLeftBase X (H / M) u ≤
            (bilinearCommonLeftLength (H / M) : ℤ) ∧
          (bilinearCommonLeftLength (H / M) : ℝ) ≤ 25 * (H / M) ∧
          |(bilinearCommonLeftBase X (H / M) u : ℝ) * (u : ℝ) - X| ≤ 44 * H) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ d →
      ∀ (m m' : ℕ),
        m ∈ bilinearWindow M (H / L) u →
        m' ∈ bilinearWindow M (H / L) u →
        (((bilinearCenteredPhase X d ν).comp
            (Polynomial.C ((bilinearCommonLeftBase X (H / M) u : ℝ) * (m : ℝ)) +
              Polynomial.C (m : ℝ) * Polynomial.X)) -
          ((bilinearCenteredPhase X d ν).comp
            (Polynomial.C ((bilinearCommonLeftBase X (H / M) u : ℝ) * (m' : ℝ)) +
              Polynomial.C (m' : ℝ) * Polynomial.X))).coeff j =
          (bilinearGammaPolynomial X (bilinearCommonLeftBase X (H / M) u)
              d j ν).eval (m : ℝ) -
            (bilinearGammaPolynomial X (bilinearCommonLeftBase X (H / M) u)
              d j ν).eval (m' : ℝ)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ d →
      bilinearGammaLinearCoefficient X
          (bilinearCommonLeftBase X (H / M) u) d j ν (u : ℝ) =
        (u : ℝ) ^ (j - 1) * ∑ i ∈ Finset.Icc j d,
          (i.choose j : ℝ) *
            ((bilinearCommonLeftBase X (H / M) u : ℝ) * (u : ℝ) - X) ^ (i - j) *
              bilinearDerivativeCoefficient X ν i) ∧
    (∀ X0 : ℤ, X = (X0 : ℝ) →
      ∃ h0 : ℤ,
        (bilinearCommonLeftBase X (H / M) u : ℝ) * (u : ℝ) - X = (h0 : ℝ)) := by
  constructor
  · intro m hm ell hell
    exact bilinearCommonCentre_index_bounds X H L M hL hM hX hr hs u m hu hm ell hell
  constructor
  · intro j hj hjd m m' hm hm'
    have hmPos : 0 < m := by
      have hright := (mem_bilinearWindow M (H / L) u m).mp hm |>.1
      have hone := (mem_bilinearRightSet M m).mp hright |>.1
      omega
    have hm'Pos : 0 < m' := by
      have hright := (mem_bilinearWindow M (H / L) u m').mp hm' |>.1
      have hone := (mem_bilinearRightSet M m').mp hright |>.1
      omega
    exact bilinearCommonCentre_phase_coefficient X
      (bilinearCommonLeftBase X (H / M) u) d j ν m m' hmPos hm'Pos
  constructor
  · intro j hj hjd
    exact bilinearGammaLinearCoefficient_eq X
      (bilinearCommonLeftBase X (H / M) u) d j ν hj hjd hνtop (u : ℝ)
  · intro X0 hXint
    refine ⟨bilinearCommonLeftBase X (H / M) u * (u : ℤ) - X0, ?_⟩
    rw [hXint]
    exact bilinearCommonCentre_offset_intCast X0
      (bilinearCommonLeftBase (X0 : ℝ) (H / M) u) u

end

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.bilinearCommonCentre
#print axioms FractionalPrimes.Literature.Polynomial.bilinearGammaLinearCoefficient_eq
#print axioms FractionalPrimes.Literature.Polynomial.bilinearCommonCentre_phase_coefficient

