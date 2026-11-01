module

public import FractionalPrimes.Literature.Polynomial.PolynomialInverseBudgets
public import FractionalPrimes.Literature.Polynomial.ScalarWeylCoefficientInverse
public import FractionalPrimes.Literature.Polynomial.ScalarWeylInverse
public import FractionalPrimes.Literature.Polynomial.ScalarWeylWeightedDistance
public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalAndTV
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open FractionalPrimes.Literature.Uniformity
open _root_.Polynomial

private theorem sumIcoOne_eq_sumRange_progression {M : Type*} [AddCommMonoid M]
    (N : ℕ) (F : ℤ → M) :
    (∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1), F n) =
      ∑ k ∈ Finset.range N, F (1 + (k : ℤ)) := by
  have hIco : Finset.Ico (1 : ℤ) ((N : ℤ) + 1) =
      (Finset.range N).map
        (Nat.castEmbedding.trans (addLeftEmbedding (1 : ℤ))) := by
    simpa using Int.Ico_eq_finset_map (1 : ℤ) ((N : ℤ) + 1)
  rw [hIco, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]

/-- Reindex a positive-step finite arithmetic progression by the one-based
integer interval used by `scalarWeylInverse`. -/
theorem sum_arithmeticProgressionPoints_eq_sumIco
    {M : Type*} [AddCommMonoid M]
    (a : ℤ) (s : ℕ) (hs : 0 < s) (K : ℕ) (F : ℤ → M) :
    (∑ n ∈ arithmeticProgressionPoints a s hs K, F n) =
      ∑ k ∈ Finset.Ico (1 : ℤ) ((K : ℤ) + 1),
        F ((a - (s : ℤ)) + (s : ℤ) * k) := by
  classical
  have hinj : Set.InjOn
      (fun k : ℕ => a + (k : ℤ) * (s : ℤ)) (↑(Finset.range K)) := by
    intro i hi j hj hij
    have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    have : (i : ℤ) = (j : ℤ) := by
      apply mul_right_cancel₀ hs0
      linarith
    exact_mod_cast this
  rw [arithmeticProgressionPoints, Finset.sum_image hinj]
  rw [sumIcoOne_eq_sumRange_progression]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ring

/-- A positive-step progression has exactly as many points as indices. -/
theorem card_arithmeticProgressionPoints
    (a : ℤ) (s : ℕ) (hs : 0 < s) (K : ℕ) :
    (arithmeticProgressionPoints a s hs K).card = K := by
  classical
  have hinj : Set.InjOn
      (fun k : ℕ => a + (k : ℤ) * (s : ℤ)) (↑(Finset.range K)) := by
    intro i hi j hj hij
    have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    have : (i : ℤ) = (j : ℤ) := by
      apply mul_right_cancel₀ hs0
      linarith
    exact_mod_cast this
  rw [arithmeticProgressionPoints, Finset.card_image_of_injOn hinj,
    Finset.card_range]

private theorem realDistanceToIntegers_le_half_progression (t : ℝ) :
    realDistanceToIntegers t ≤ 1 / 2 := by
  rw [realDistanceToIntegers_eq_abs_centered]
  exact abs_le.mpr ⟨(centeredFrequency_mem t).1,
    le_of_lt (centeredFrequency_mem t).2⟩

private theorem progressionPhaseSum_norm_le_card
    (P : Polynomial ℝ) (J : Finset ℤ) :
    ‖∑ n ∈ J, unitFrequencyPhase (P.eval (n : ℝ))‖ ≤ (J.card : ℝ) := by
  calc
    ‖∑ n ∈ J, unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        ∑ n ∈ J, ‖unitFrequencyPhase (P.eval (n : ℝ))‖ := norm_sum_le _ _
    _ = (J.card : ℝ) := by simp [norm_unitFrequencyPhase]

/-- Geometry forced by a long, populous arithmetic progression contained in
`(x,x+h]`.  The origin is shifted one step left so that its indices are
`1,...,K`, exactly as in the scalar Weyl theorem. -/
theorem arithmeticProgression_long_geometry
    (a : ℤ) (s : ℕ) (hs : 0 < s) (K : ℕ)
    (x h ρ : ℝ) (hh : 1 ≤ h) (hρ : 0 < ρ)
    (hlong : 4 / ρ < h)
    (hKlower : ρ * h ≤ (K : ℝ))
    (hsubset : ∀ n ∈ arithmeticProgressionPoints a s hs K,
      x < (n : ℝ) ∧ (n : ℝ) ≤ x + h) :
    1 ≤ K ∧
      (K : ℝ) ≤ 2 * h ∧
      (s : ℝ) ≤ 2 / ρ ∧
      (s : ℝ) < h ∧
      |(((a - (s : ℤ)) : ℤ) : ℝ) - (Int.floor x : ℝ)| ≤ 2 * h := by
  have hhpos : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hfour : 4 < ρ * h := by
    have hmul := mul_lt_mul_of_pos_left hlong hρ
    have hρne : ρ ≠ 0 := ne_of_gt hρ
    calc
      4 = ρ * (4 / ρ) := by field_simp
      _ < ρ * h := hmul
  have hKfour : 4 < (K : ℝ) := lt_of_lt_of_le hfour hKlower
  have hKpos : 0 < K := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 4) hKfour)
  have hKone : 1 ≤ K := hKpos
  have haMem : a ∈ arithmeticProgressionPoints a s hs K := by
    rw [arithmeticProgressionPoints]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hKpos, by simp⟩
  have hlastIndex : K - 1 ∈ Finset.range K := Finset.mem_range.mpr (by omega)
  have hlastMem : a + ((K - 1 : ℕ) : ℤ) * (s : ℤ) ∈
      arithmeticProgressionPoints a s hs K := by
    rw [arithmeticProgressionPoints]
    exact Finset.mem_image.mpr ⟨K - 1, hlastIndex, rfl⟩
  have haBounds := hsubset a haMem
  have hlastBounds := hsubset
    (a + ((K - 1 : ℕ) : ℤ) * (s : ℤ)) hlastMem
  have hspan : ((K - 1 : ℕ) : ℝ) * (s : ℝ) ≤ h := by
    have hcast :
        ((a + ((K - 1 : ℕ) : ℤ) * (s : ℤ) : ℤ) : ℝ) =
          (a : ℝ) + ((K - 1 : ℕ) : ℝ) * (s : ℝ) := by norm_num
    rw [hcast] at hlastBounds
    linarith
  have hsoneReal : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hKm1le : ((K - 1 : ℕ) : ℝ) ≤ h := by
    calc
      ((K - 1 : ℕ) : ℝ) = ((K - 1 : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((K - 1 : ℕ) : ℝ) * (s : ℝ) :=
        mul_le_mul_of_nonneg_left hsoneReal (by positivity)
      _ ≤ h := hspan
  have hKcast : (K : ℝ) = ((K - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hKone]
    norm_num
  have hKupperOne : (K : ℝ) ≤ h + 1 := by linarith
  have hKupper : (K : ℝ) ≤ 2 * h := by linarith
  have hKm1half : (K : ℝ) / 2 ≤ ((K - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hKone]
    norm_num
    linarith
  have hhalfSpan : ((K : ℝ) / 2) * (s : ℝ) ≤ h := by
    exact (mul_le_mul_of_nonneg_right hKm1half (by positivity)).trans hspan
  have hρSpan : (ρ * h / 2) * (s : ℝ) ≤ h := by
    exact (mul_le_mul_of_nonneg_right
      (by linarith [hKlower] : ρ * h / 2 ≤ (K : ℝ) / 2)
      (by positivity)).trans hhalfSpan
  have hρs : ρ * (s : ℝ) ≤ 2 := by
    have hcancel : h * (ρ * (s : ℝ)) ≤ h * 2 := by
      nlinarith [hρSpan]
    exact le_of_mul_le_mul_left (by simpa [mul_assoc] using hcancel) hhpos
  have hsUpper : (s : ℝ) ≤ 2 / ρ := by
    exact (le_div_iff₀ hρ).2 (by simpa [mul_comm] using hρs)
  have hslt : (s : ℝ) < h := by
    have htwofour : 2 / ρ < 4 / ρ := by
      have hinvpos : 0 < ρ⁻¹ := inv_pos.mpr hρ
      simp only [div_eq_mul_inv]
      nlinarith
    have htwo : 2 / ρ < h := htwofour.trans hlong
    exact hsUpper.trans_lt htwo
  have hfloorLe : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have hxFloor : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
  have hcUpper : (((a - (s : ℤ)) : ℤ) : ℝ) - (Int.floor x : ℝ) ≤ 2 * h := by
    norm_num
    linarith
  have hcLower : -(2 * h) ≤
      (((a - (s : ℤ)) : ℤ) : ℝ) - (Int.floor x : ℝ) := by
    norm_num
    linarith
  exact ⟨hKone, hKupper, hsUpper, hslt, abs_le.mpr ⟨hcLower, hcUpper⟩⟩

/-- Exact inverse coefficient identity between a polynomial centred at `Y`
and the same polynomial sampled on the integer affine map `c+s*t`.  The
factor `s^d` makes every coefficient on the right integral. -/
theorem progression_centeredAffineCoefficient_inverse
    {d j : ℕ} (hd : 1 ≤ d) (hj : 1 ≤ j) (hjd : j ≤ d)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (Y c : ℤ) (s q : ℕ) (hs : 0 < s) :
    (((q * s ^ d : ℕ) : ℝ) *
        (P.comp (X + C (Y : ℝ))).coeff j) =
      ∑ i ∈ Finset.Icc j d,
        ((((Nat.choose i j : ℤ) * (s : ℤ) ^ (d - i) *
          (Y - c) ^ (i - j) : ℤ) : ℝ) *
            ((q : ℝ) *
              (P.comp (C (s : ℝ) * X + C (c : ℝ))).coeff i)) := by
  let A : Polynomial ℝ := P.comp (X + C (Y : ℝ))
  let Q : Polynomial ℝ := P.comp (C (s : ℝ) * X + C (c : ℝ))
  have hAdeg : A.natDegree ≤ d := by
    have hdeg := scalarWeyl_affineSubstitution_degree
      (d := d + 1) P (by simpa using hP) Y 1
    simpa [A] using hdeg
  have hcomp :
      A.comp (C (s : ℝ) * X + C ((c - Y : ℤ) : ℝ)) = Q := by
    dsimp [A, Q]
    rw [Polynomial.comp_assoc]
    congr 1
    simp
    ring
  have hinv := scalarWeyl_affineCoefficient_inverse
    (d := d + 1) (j := j) (by omega) hj (by omega)
    A hAdeg (c - Y) s hs
  rw [hcomp] at hinv
  have hinv' :
      (s : ℝ) ^ d * A.coeff j =
        ∑ i ∈ Finset.Icc j d,
          (Nat.choose i j : ℝ) * (s : ℝ) ^ (d - i) *
            ((Y : ℝ) - (c : ℝ)) ^ (i - j) * Q.coeff i := by
    simpa [sub_eq_add_neg] using hinv
  change (((q * s ^ d : ℕ) : ℝ) * A.coeff j) =
    ∑ i ∈ Finset.Icc j d,
      ((((Nat.choose i j : ℤ) * (s : ℤ) ^ (d - i) *
        (Y - c) ^ (i - j) : ℤ) : ℝ) * ((q : ℝ) * Q.coeff i))
  calc
    ((q * s ^ d : ℕ) : ℝ) * A.coeff j =
        (q : ℝ) * ((s : ℝ) ^ d * A.coeff j) := by norm_num; ring
    _ = (q : ℝ) *
        (∑ i ∈ Finset.Icc j d,
          (Nat.choose i j : ℝ) * (s : ℝ) ^ (d - i) *
            ((Y : ℝ) - (c : ℝ)) ^ (i - j) * Q.coeff i) := by rw [hinv']
    _ = ∑ i ∈ Finset.Icc j d,
        (q : ℝ) * ((Nat.choose i j : ℝ) * (s : ℝ) ^ (d - i) *
          ((Y : ℝ) - (c : ℝ)) ^ (i - j) * Q.coeff i) := by
      rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.Icc j d,
        ((((Nat.choose i j : ℤ) * (s : ℤ) ^ (d - i) *
          (Y - c) ^ (i - j) : ℤ) : ℝ) * ((q : ℝ) * Q.coeff i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      ring

private theorem progression_inverse_weight_bound
    {d j i : ℕ} (hji : j ≤ i) (hid : i ≤ d)
    {h K z s B c₀ : ℝ}
    (hh : 1 ≤ h) (hK : 0 < K) (hz : 1 ≤ z)
    (hs0 : 0 ≤ s) (hs : s ≤ 2 * z)
    (hc : |c₀| ≤ 2 * h) (hratio : h / K ≤ z)
    (hB : 0 ≤ B) :
    h ^ j *
        ((Nat.choose i j : ℝ) * s ^ (d - i) * |c₀| ^ (i - j)) *
        (B / K ^ i) ≤
      8 ^ d * B * z ^ (2 * d) := by
  have hh0 : 0 ≤ h := le_trans (by norm_num) hh
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz
  have htwoz : 1 ≤ 2 * z := by nlinarith
  have hchooseNat : Nat.choose i j ≤ 2 ^ d :=
    (Nat.choose_le_two_pow i j).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) hid)
  have hchoose : (Nat.choose i j : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast hchooseNat
  have hsPow : s ^ (d - i) ≤ (2 * z) ^ d := by
    calc
      s ^ (d - i) ≤ (2 * z) ^ (d - i) :=
        pow_le_pow_left₀ hs0 hs _
      _ ≤ (2 * z) ^ d := pow_le_pow_right₀ htwoz (Nat.sub_le d i)
  have hcPow : |c₀| ^ (i - j) ≤ (2 * h) ^ (i - j) :=
    pow_le_pow_left₀ (abs_nonneg c₀) hc _
  have hratio0 : 0 ≤ h / K := by positivity
  have hratioPow : (h / K) ^ i ≤ z ^ d := by
    calc
      (h / K) ^ i ≤ z ^ i := pow_le_pow_left₀ hratio0 hratio _
      _ ≤ z ^ d := pow_le_pow_right₀ hz hid
  have htwoPow : (2 : ℝ) ^ (i - j) ≤ 2 ^ d :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      ((Nat.sub_le i j).trans hid)
  have hhpow : h ^ j * h ^ (i - j) = h ^ i := by
    rw [← pow_add, Nat.add_sub_of_le hji]
  have hscaleEq :
      h ^ j * (2 * h) ^ (i - j) / K ^ i =
        2 ^ (i - j) * (h / K) ^ i := by
    rw [mul_pow, div_pow]
    calc
      h ^ j * (2 ^ (i - j) * h ^ (i - j)) / (K ^ i) =
          2 ^ (i - j) * (h ^ j * h ^ (i - j)) / K ^ i := by ring
      _ = 2 ^ (i - j) * h ^ i / K ^ i := by rw [hhpow]
      _ = 2 ^ (i - j) * (h ^ i / K ^ i) := by ring
  have hscale :
      h ^ j * |c₀| ^ (i - j) / K ^ i ≤ 2 ^ d * z ^ d := by
    calc
      h ^ j * |c₀| ^ (i - j) / K ^ i ≤
          h ^ j * (2 * h) ^ (i - j) / K ^ i := by
        gcongr
      _ = 2 ^ (i - j) * (h / K) ^ i := hscaleEq
      _ ≤ 2 ^ d * z ^ d :=
        mul_le_mul htwoPow hratioPow (by positivity) (by positivity)
  calc
    h ^ j *
          ((Nat.choose i j : ℝ) * s ^ (d - i) * |c₀| ^ (i - j)) *
          (B / K ^ i) =
        (Nat.choose i j : ℝ) * s ^ (d - i) * B *
          (h ^ j * |c₀| ^ (i - j) / K ^ i) := by ring
    _ ≤ 2 ^ d * (2 * z) ^ d * B * (2 ^ d * z ^ d) := by
      gcongr
    _ = 8 ^ d * B * z ^ (2 * d) := by
      rw [show (2 * z) ^ d = 2 ^ d * z ^ d by rw [mul_pow]]
      rw [show (8 : ℝ) ^ d = 2 ^ d * 2 ^ d * 2 ^ d by
        rw [show (8 : ℝ) = 2 * 2 * 2 by norm_num, mul_pow, mul_pow]]
      rw [show z ^ (2 * d) = z ^ d * z ^ d by
        rw [show 2 * d = d + d by omega, pow_add]]
      ring

/-- The quantitative coefficient-transport estimate used in the long
progression branch.  It is separated from the Weyl invocation so the exact
integer affine identity and the numerical budget can be checked in isolation. -/
theorem progression_centeredCoefficient_bound
    {d j K s q : ℕ} (hd : 1 ≤ d) (hj : 1 ≤ j) (hjd : j ≤ d)
    (hK : 1 ≤ K) (hs : 0 < s)
    {h z B : ℝ} (hh : 1 ≤ h) (hz : 1 ≤ z)
    (hsUpper : (s : ℝ) ≤ 2 * z)
    (Y c : ℤ) (hc : |(Y : ℝ) - (c : ℝ)| ≤ 2 * h)
    (hratio : h / (K : ℝ) ≤ z) (hB : 0 ≤ B)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hβ : ∀ i, 1 ≤ i → i ≤ d →
      (K : ℝ) ^ i * realDistanceToIntegers
        ((q : ℝ) * (P.comp (C (s : ℝ) * X + C (c : ℝ))).coeff i) ≤ B) :
    h ^ j * realDistanceToIntegers
        (((q * s ^ d : ℕ) : ℝ) *
          (P.comp (X + C (Y : ℝ))).coeff j) ≤
      (d + 1 : ℝ) * 8 ^ d * B * z ^ (2 * d) := by
  classical
  let S : Finset ℕ := Finset.Icc j d
  let m : ℕ → ℤ := fun i =>
    (Nat.choose i j : ℤ) * (s : ℤ) ^ (d - i) * (Y - c) ^ (i - j)
  let β : ℕ → ℝ := fun i =>
    (q : ℝ) * (P.comp (C (s : ℝ) * X + C (c : ℝ))).coeff i
  let ε : ℕ → ℝ := fun i => B / (K : ℝ) ^ i
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hε (i : ℕ) (hi : i ∈ S) :
      realDistanceToIntegers (β i) ≤ ε i := by
    rcases Finset.mem_Icc.mp hi with ⟨hji, hid⟩
    apply (le_div_iff₀ (pow_pos hKreal i)).2
    simpa [β, ε, mul_comm] using hβ i (by omega) hid
  have hweighted := realDistanceToIntegers_intWeightedSum_le S m β ε hε
  have hidCoeffs := progression_centeredAffineCoefficient_inverse
    hd hj hjd P hP Y c s q hs
  have hidentity :
      (((q * s ^ d : ℕ) : ℝ) *
          (P.comp (X + C (Y : ℝ))).coeff j) =
        ∑ i ∈ S, (m i : ℝ) * β i := by
    simpa [S, m, β] using hidCoeffs
  have hdist :
      realDistanceToIntegers
          (((q * s ^ d : ℕ) : ℝ) *
            (P.comp (X + C (Y : ℝ))).coeff j) ≤
        ∑ i ∈ S, |(m i : ℝ)| * ε i := by
    rw [hidentity]
    exact hweighted
  have hmAbs (i : ℕ) :
      |(m i : ℝ)| =
        (Nat.choose i j : ℝ) * (s : ℝ) ^ (d - i) *
          |(Y : ℝ) - (c : ℝ)| ^ (i - j) := by
    dsimp [m]
    push_cast
    rw [abs_mul, abs_mul, abs_pow]
    rw [abs_of_nonneg (Nat.cast_nonneg (Nat.choose i j))]
    rw [abs_of_nonneg (Nat.cast_nonneg s)]
    rw [abs_pow]
  have hterm (i : ℕ) (hi : i ∈ S) :
      h ^ j * (|(m i : ℝ)| * ε i) ≤
        8 ^ d * B * z ^ (2 * d) := by
    rcases Finset.mem_Icc.mp hi with ⟨hji, hid⟩
    rw [hmAbs]
    dsimp [ε]
    simpa [mul_assoc] using
      progression_inverse_weight_bound hji hid hh hKreal hz
        (by positivity) hsUpper hc hratio hB
  have hsum :
      h ^ j * (∑ i ∈ S, |(m i : ℝ)| * ε i) ≤
        ∑ i ∈ S, 8 ^ d * B * z ^ (2 * d) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hcard : (S.card : ℝ) ≤ d + 1 := by
    dsimp [S]
    rw [Nat.card_Icc]
    exact_mod_cast Nat.sub_le (d + 1) j
  have hcommon : 0 ≤ 8 ^ d * B * z ^ (2 * d) := by positivity
  calc
    h ^ j * realDistanceToIntegers
          (((q * s ^ d : ℕ) : ℝ) *
            (P.comp (X + C (Y : ℝ))).coeff j) ≤
        h ^ j * (∑ i ∈ S, |(m i : ℝ)| * ε i) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ ≤ ∑ i ∈ S, 8 ^ d * B * z ^ (2 * d) := hsum
    _ = (S.card : ℝ) * (8 ^ d * B * z ^ (2 * d)) := by simp
    _ ≤ (d + 1 : ℝ) * (8 ^ d * B * z ^ (2 * d)) :=
      mul_le_mul_of_nonneg_right hcard hcommon
    _ = (d + 1 : ℝ) * 8 ^ d * B * z ^ (2 * d) := by ring

/-- Scalar inverse theorem on an arbitrary finite subprogression of
`(x,x+h]`, with the exact approved budget `G_d`.  Coefficients are centred at
the integer `floor x`, as required by the paper and blueprint. -/
theorem progressionPhaseInverse
    (d : ℕ) (hd : 1 ≤ d)
    (h : ℝ) (hh : 1 ≤ h) (x : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (J : Finset ℤ) (hJAP : isFiniteArithmeticProgression J)
    (hJsubset : ∀ n ∈ J, x < (n : ℝ) ∧ (n : ℝ) ≤ x + h)
    (hlarge : ρ * h ≤
      ‖∑ n ∈ J, unitFrequencyPhase (P.eval (n : ℝ))‖) :
    ∃ r : ℕ,
      1 ≤ r ∧
      (r : ℝ) ≤ inverseBoundG d ρ⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        h ^ j * realDistanceToIntegers
          ((r : ℝ) * (P.comp (X + C (Int.floor x : ℝ))).coeff j) ≤
            inverseBoundG d ρ⁻¹ := by
  classical
  rcases hJAP with ⟨a, s, hs, K, rfl⟩
  let z : ℝ := ρ⁻¹
  let B : ℝ := inverseBoundF d (4 * z)
  have hρone : ρ < 1 := hρhalf.trans (by norm_num)
  have hzTwo : 2 < z := by
    have htwo : 2 < 1 / ρ := (lt_div_iff₀ hρ).2 (by nlinarith)
    simpa [z, one_div] using htwo
  have hz : 2 ≤ z := hzTwo.le
  have hzOne : 1 ≤ z := by linarith
  have hfourz : 1 ≤ 4 * z := by nlinarith
  have hBcontrol := weylBoundPowerControl d hd (4 * z) hfourz
  have hB : 1 ≤ B := by simpa [B, inverseBoundF] using hBcontrol.1
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hGeval :
      inverseBoundG d z =
        (4 * z) ^ d + (d + 1 : ℝ) * 8 ^ d * B * z ^ (2 * d) + 1 := by
    simpa [B] using inverseBoundG_eval d z
  by_cases hshort : h ≤ 4 / ρ
  · refine ⟨1, by norm_num, ?_, ?_⟩
    · simpa [z] using inverseBoundG_ge_one d z hz
    · intro j hj hjd
      have hupper : h ≤ 4 * z := by simpa [z, div_eq_mul_inv] using hshort
      have hh0 : 0 ≤ h := le_trans (by norm_num) hh
      have hpow : h ^ j ≤ (4 * z) ^ d := by
        calc
          h ^ j ≤ (4 * z) ^ j := pow_le_pow_left₀ hh0 hupper _
          _ ≤ (4 * z) ^ d := pow_le_pow_right₀ hfourz hjd
      have hdist := realDistanceToIntegers_le_half_progression
        ((P.comp (X + C (Int.floor x : ℝ))).coeff j)
      have hprod :
          h ^ j * realDistanceToIntegers
              ((P.comp (X + C (Int.floor x : ℝ))).coeff j) ≤
            (4 * z) ^ d := by
        calc
          h ^ j * realDistanceToIntegers
                ((P.comp (X + C (Int.floor x : ℝ))).coeff j) ≤
              h ^ j * (1 / 2) :=
            mul_le_mul_of_nonneg_left hdist (by positivity)
          _ ≤ h ^ j := by
            have : (0 : ℝ) ≤ h ^ j := by positivity
            nlinarith
          _ ≤ (4 * z) ^ d := hpow
      have hout : h ^ j * realDistanceToIntegers
            ((P.comp (X + C (Int.floor x : ℝ))).coeff j) ≤
          inverseBoundG d z := by
        rw [hGeval]
        have hlargeTerm :
            0 ≤ (d + 1 : ℝ) * 8 ^ d * B * z ^ (2 * d) := by positivity
        linarith
      simpa only [Nat.cast_one, one_mul, z] using hout
  · have hlong : 4 / ρ < h := lt_of_not_ge hshort
    have hKlower : ρ * h ≤ (K : ℝ) := by
      calc
        ρ * h ≤
            ‖∑ n ∈ arithmeticProgressionPoints a s hs K,
              unitFrequencyPhase (P.eval (n : ℝ))‖ := hlarge
        _ ≤ ((arithmeticProgressionPoints a s hs K).card : ℝ) :=
          progressionPhaseSum_norm_le_card P _
        _ = (K : ℝ) := by rw [card_arithmeticProgressionPoints]
    obtain ⟨hK, hKupper, hsUpperDiv, hslt, hc⟩ :=
      arithmeticProgression_long_geometry a s hs K x h ρ hh hρ hlong
        hKlower hJsubset
    let c : ℤ := a - (s : ℤ)
    let Y : ℤ := Int.floor x
    let Q : Polynomial ℝ := P.comp (C (s : ℝ) * X + C (c : ℝ))
    have hsUpper : (s : ℝ) ≤ 2 * z := by
      simpa [z, div_eq_mul_inv] using hsUpperDiv
    have hc' : |(Y : ℝ) - (c : ℝ)| ≤ 2 * h := by
      simpa [Y, c, abs_sub_comm] using hc
    have hQdeg : Q.natDegree ≤ d := by
      have hdeg := scalarWeyl_affineSubstitution_degree
        (d := d + 1) P (by simpa using hP) c s
      simpa [Q] using hdeg
    have hinterval :
        Finset.Ico (1 : ℤ) ((K : ℤ) + 1) ⊆
          Finset.Icc (1 : ℤ) (K : ℤ) := by
      intro n hn
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hn ⊢
      omega
    have hsum :
        (∑ k ∈ Finset.Ico (1 : ℤ) ((K : ℤ) + 1),
          unitFrequencyPhase (Q.eval (k : ℝ))) =
        ∑ n ∈ arithmeticProgressionPoints a s hs K,
          unitFrequencyPhase (P.eval (n : ℝ)) := by
      rw [sum_arithmeticProgressionPoints_eq_sumIco]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      rw [show Q.eval (k : ℝ) =
          P.eval ((c : ℝ) + (s : ℝ) * (k : ℝ)) by
        exact scalarWeyl_affineSubstitution_eval P c s k]
      congr 1
      dsimp [c]
      push_cast
      ring
    have hδpos : 0 < ρ / 4 := by positivity
    have hδhalf : ρ / 4 < 1 / 2 := by nlinarith
    have hδlarge : (ρ / 4) * (K : ℝ) ≤
        ‖∑ k ∈ Finset.Ico (1 : ℤ) ((K : ℤ) + 1),
          unitFrequencyPhase (Q.eval (k : ℝ))‖ := by
      calc
        (ρ / 4) * (K : ℝ) ≤ ρ * h := by
          have := mul_le_mul_of_nonneg_left hKupper (le_of_lt hρ)
          nlinarith
        _ ≤ ‖∑ n ∈ arithmeticProgressionPoints a s hs K,
            unitFrequencyPhase (P.eval (n : ℝ))‖ := hlarge
        _ = ‖∑ k ∈ Finset.Ico (1 : ℤ) ((K : ℤ) + 1),
            unitFrequencyPhase (Q.eval (k : ℝ))‖ := by rw [hsum]
    obtain ⟨q, hq, hqBound, hqCoeffs⟩ :=
      scalarWeylInverse d K hd hK hδpos hδhalf Q hQdeg
        1 ((K : ℤ) + 1) hinterval hδlarge
    have hδinv : (ρ / 4)⁻¹ = 4 * z := by
      dsimp [z]
      field_simp [ne_of_gt hρ]
    have hqB : (q : ℝ) ≤ B := by
      simpa [B, inverseBoundF, hδinv] using hqBound
    have hqCoeffs' : ∀ i, 1 ≤ i → i ≤ d →
        (K : ℝ) ^ i * realDistanceToIntegers
          ((q : ℝ) * Q.coeff i) ≤ B := by
      intro i hi hid
      simpa [B, inverseBoundF, hδinv] using hqCoeffs i hi hid
    have hratio : h / (K : ℝ) ≤ z := by
      have hz0 : 0 ≤ z := by linarith
      have hscale : h ≤ z * (K : ℝ) := by
        calc
          h = z * (ρ * h) := by
            dsimp [z]
            field_simp [ne_of_gt hρ]
          _ ≤ z * (K : ℝ) := mul_le_mul_of_nonneg_left hKlower hz0
      exact (div_le_iff₀ (by exact_mod_cast (show 0 < K by omega))).2
        (by simpa [mul_comm] using hscale)
    have hsPow : (s : ℝ) ^ d ≤ (2 * z) ^ d :=
      pow_le_pow_left₀ (by positivity) hsUpper _
    have hrPre : ((q * s ^ d : ℕ) : ℝ) ≤ B * (2 * z) ^ d := by
      norm_num
      exact mul_le_mul hqB hsPow (by positivity) hB0
    have hbase : 2 * z ≤ 8 * z ^ 2 := by nlinarith [hzOne]
    have hpowBig : (2 * z) ^ d ≤ 8 ^ d * z ^ (2 * d) := by
      calc
        (2 * z) ^ d ≤ (8 * z ^ 2) ^ d :=
          pow_le_pow_left₀ (by positivity) hbase _
        _ = 8 ^ d * z ^ (2 * d) := by
          rw [mul_pow, ← pow_mul]
    have hmainTerm :
        B * (2 * z) ^ d ≤
          (d + 1 : ℝ) * 8 ^ d * B * z ^ (2 * d) := by
      calc
        B * (2 * z) ^ d ≤ B * (8 ^ d * z ^ (2 * d)) :=
          mul_le_mul_of_nonneg_left hpowBig hB0
        _ ≤ (d + 1 : ℝ) * (B * (8 ^ d * z ^ (2 * d))) := by
          have hdOne : (1 : ℝ) ≤ d + 1 := by exact_mod_cast (show 1 ≤ d + 1 by omega)
          have hnonneg : 0 ≤ B * (8 ^ d * z ^ (2 * d)) := by positivity
          nlinarith
        _ = (d + 1 : ℝ) * 8 ^ d * B * z ^ (2 * d) := by ring
    refine ⟨q * s ^ d, ?_, ?_, ?_⟩
    · have hspow : 1 ≤ s ^ d := Nat.one_le_pow d s hs
      simpa using Nat.mul_le_mul hq hspow
    · change ((q * s ^ d : ℕ) : ℝ) ≤ inverseBoundG d z
      rw [hGeval]
      have hfirst : 0 ≤ (4 * z) ^ d := by positivity
      linarith [hrPre.trans hmainTerm]
    · intro j hj hjd
      have hcoeff := progression_centeredCoefficient_bound
        hd hj hjd hK hs hh hzOne hsUpper Y c hc' hratio hB0 P hP
        (by simpa [Q] using hqCoeffs')
      change h ^ j * realDistanceToIntegers
          (((q * s ^ d : ℕ) : ℝ) *
            (P.comp (X + C (Y : ℝ))).coeff j) ≤ inverseBoundG d z
      rw [hGeval]
      have hfirst : 0 ≤ (4 * z) ^ d := by positivity
      linarith

end FractionalPrimes.Literature.Polynomial
