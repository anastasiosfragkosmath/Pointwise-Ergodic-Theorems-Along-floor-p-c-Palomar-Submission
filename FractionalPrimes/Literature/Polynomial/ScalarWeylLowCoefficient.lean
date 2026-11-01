module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylCoefficientInverse
public import FractionalPrimes.Literature.Polynomial.ScalarWeylWeightedDistance
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

/-- Source-specialized low-coefficient estimate after affine inversion.
The induction bounds are stated at `N'`; the hypothesis `N/r ≤ N'`
transfers them to the scale `(r/N)^i`. The cap `r ≤ N` is the source
consequence of `r ≤ R ≤ N/4`. -/
theorem scalarWeyl_lowCoefficientBound
    {d j N N' r s : ℕ} {D R : ℝ}
    (hd : 2 ≤ d) (hj : 1 ≤ j) (hjd : j < d)
    (hN : 1 ≤ N) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hrR : (r : ℝ) ≤ R) (hrN : (r : ℝ) ≤ (N : ℝ))
    (hsD : (s : ℝ) ≤ D)
    (hN'lower : (N : ℝ) / (r : ℝ) ≤ (N' : ℝ))
    (c : ℤ) (hc : |(c : ℝ)| ≤ (r : ℝ))
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d - 1)
    (hβ : ∀ i, 1 ≤ i → i < d →
      realDistanceToIntegers
        ((s : ℝ) *
          (P.comp (Polynomial.C (r : ℝ) * Polynomial.X +
            Polynomial.C (c : ℝ))).coeff i) ≤
        D / ((N' : ℝ) ^ i)) :
    realDistanceToIntegers
      (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff j) ≤
      (2 : ℝ) ^ d * D * R ^ (d - 1) / ((N : ℝ) ^ j) := by
  classical
  let Q : Polynomial ℝ :=
    P.comp (Polynomial.C (r : ℝ) * Polynomial.X + Polynomial.C (c : ℝ))
  let S : Finset ℕ := Finset.Icc j (d - 1)
  let u : ℝ := (r : ℝ) / (N : ℝ)
  let m : ℕ → ℤ := fun i =>
    (Nat.choose i j : ℤ) * (r : ℤ) ^ (d - 1 - i) *
      (-(c : ℤ)) ^ (i - j)
  have hd' : d - 1 = (d - 2) + 1 := by omega
  have hrPosNat : 0 < r := by omega
  have hrPos : 0 < (r : ℝ) := by exact_mod_cast hrPosNat
  have hNPosNat : 0 < N := by omega
  have hNPos : 0 < (N : ℝ) := by exact_mod_cast hNPosNat
  have hDNonneg : 0 ≤ D := by
    have hsReal : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    linarith
  have hrNonneg : 0 ≤ (r : ℝ) := by positivity
  have hRNonneg : 0 ≤ R := by
    have hrReal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have huNonneg : 0 ≤ u := by dsimp [u]; positivity
  have huLeOne : u ≤ 1 := by
    dsimp [u]
    exact (div_le_one hNPos).2 hrN
  have hRPow : (r : ℝ) ^ (d - 1) ≤ R ^ (d - 1) :=
    pow_le_pow_left₀ hrNonneg hrR _
  have hqCast : ((s * r ^ (d - 1) : ℕ) : ℝ) =
      (s : ℝ) * (r : ℝ) ^ (d - 1) := by
    push_cast
    ring
  have hNratioPow (i : ℕ) :
      ((N : ℝ) / (r : ℝ)) ^ i ≤ (N' : ℝ) ^ i :=
    pow_le_pow_left₀ (le_of_lt (div_pos hNPos hrPos)) hN'lower _
  have hbetaScaled (i : ℕ) (hiLo : 1 ≤ i) (hiHi : i < d) :
      realDistanceToIntegers ((s : ℝ) * Q.coeff i) ≤ D * u ^ i := by
    have hrecip :
        1 / ((N' : ℝ) ^ i) ≤ 1 / (((N : ℝ) / (r : ℝ)) ^ i) :=
      one_div_le_one_div_of_le
        (pow_pos (div_pos hNPos hrPos) i) (hNratioPow i)
    calc
      realDistanceToIntegers ((s : ℝ) * Q.coeff i) ≤
          D / ((N' : ℝ) ^ i) := by
        simpa [Q] using hβ i hiLo hiHi
      _ = D * (1 / ((N' : ℝ) ^ i)) := by ring
      _ ≤ D * (1 / (((N : ℝ) / (r : ℝ)) ^ i)) :=
        mul_le_mul_of_nonneg_left hrecip hDNonneg
      _ = D * u ^ i := by
        congr 1
        dsimp [u]
        rw [div_pow, div_pow]
        field_simp [ne_of_gt (pow_pos hNPos i),
          ne_of_gt (pow_pos hrPos i)]
        <;> ring
  have hMemBounds (i : ℕ) (hi : i ∈ S) :
      j ≤ i ∧ i ≤ d - 1 := by
    exact Finset.mem_Icc.mp hi
  have hbetaOnS (i : ℕ) (hi : i ∈ S) :
      realDistanceToIntegers ((s : ℝ) * Q.coeff i) ≤ D * u ^ i := by
    have hb := hMemBounds i hi
    apply hbetaScaled i
    · omega
    · omega
  have hmCast (i : ℕ) :
      (m i : ℝ) = (Nat.choose i j : ℝ) * (r : ℝ) ^ (d - 1 - i) *
        (-(c : ℝ)) ^ (i - j) := by
    dsimp [m]
    push_cast
    ring
  have hinv := scalarWeyl_affineCoefficient_inverse
    hd hj hjd P hP c r hrPosNat
  have hidentity :
      ((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff j =
        ∑ i ∈ S, (m i : ℝ) * ((s : ℝ) * Q.coeff i) := by
    rw [hqCast]
    calc
      (s : ℝ) * (r : ℝ) ^ (d - 1) * P.coeff j =
          (s : ℝ) *
            (∑ i ∈ S,
              (Nat.choose i j : ℝ) * (r : ℝ) ^ (d - 1 - i) *
                (-(c : ℝ)) ^ (i - j) * Q.coeff i) := by
        rw [show Q = P.comp
          (Polynomial.C (r : ℝ) * Polynomial.X + Polynomial.C (c : ℝ))
          from rfl]
        simpa only [mul_assoc] using
          congrArg (fun x : ℝ => (s : ℝ) * x) hinv
      _ = ∑ i ∈ S,
            (s : ℝ) *
              ((Nat.choose i j : ℝ) * (r : ℝ) ^ (d - 1 - i) *
                (-(c : ℝ)) ^ (i - j) * Q.coeff i) := by
        rw [Finset.mul_sum]
      _ = ∑ i ∈ S, (m i : ℝ) * ((s : ℝ) * Q.coeff i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hmCast]
        ring
  have hweighted := realDistanceToIntegers_intWeightedSum_le
      S m (fun i => (s : ℝ) * Q.coeff i) (fun i => D * u ^ i) hbetaOnS
  have hdistInv :
      realDistanceToIntegers
          (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff j) ≤
        ∑ i ∈ S, |(m i : ℝ)| * (D * u ^ i) := by
    calc
      realDistanceToIntegers
          (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff j) =
          realDistanceToIntegers
            (∑ i ∈ S, (m i : ℝ) * ((s : ℝ) * Q.coeff i)) := by
              rw [hidentity]
      _ ≤ ∑ i ∈ S, |(m i : ℝ)| * (D * u ^ i) := hweighted
  have hchooseSum :
      (∑ i ∈ S, Nat.choose i j) = Nat.choose d (j + 1) := by
    have hlast : d - 1 + 1 = d := by omega
    simpa [S, hlast] using Nat.sum_Icc_choose (d - 1) j
  have hchooseBound : Nat.choose d (j + 1) ≤ 2 ^ d := by
    calc
      Nat.choose d (j + 1) ≤
          ∑ i ∈ Finset.range (d + 1), Nat.choose d i :=
        Finset.single_le_sum
          (fun i hi => Nat.zero_le (Nat.choose d i))
          (Finset.mem_range.mpr (by omega))
      _ = 2 ^ d := Nat.sum_range_choose d
  have hchooseSumReal :
      (∑ i ∈ S, (Nat.choose i j : ℝ)) =
        (Nat.choose d (j + 1) : ℝ) := by
    calc
      (∑ i ∈ S, (Nat.choose i j : ℝ)) =
          ((∑ i ∈ S, Nat.choose i j : ℕ) : ℝ) := by norm_cast
      _ = (Nat.choose d (j + 1) : ℝ) := by rw [hchooseSum]
  have hchooseBoundReal :
      (Nat.choose d (j + 1) : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast hchooseBound
  have hNjPos : 0 < (N : ℝ) ^ j := pow_pos hNPos _
  have hCNonneg : 0 ≤ D * R ^ (d - 1) / (N : ℝ) ^ j := by
    positivity
  have hpowj : (r : ℝ) ^ (d - 1 - j) * (r : ℝ) ^ j =
      (r : ℝ) ^ (d - 1) := by
    calc
      (r : ℝ) ^ (d - 1 - j) * (r : ℝ) ^ j =
          (r : ℝ) ^ ((d - 1 - j) + j) := by rw [← pow_add]
      _ = (r : ℝ) ^ (d - 1) := by congr 1 <;> omega
  have hnormal :
      (D * (r : ℝ) ^ (d - 1 - j)) * u ^ j =
        D * (r : ℝ) ^ (d - 1) / (N : ℝ) ^ j := by
    dsimp [u]
    rw [div_pow]
    field_simp [ne_of_gt hNjPos]
    rw [mul_assoc, hpowj]
  have hterm (i : ℕ) (hi : i ∈ S) :
      |(m i : ℝ)| * (D * u ^ i) ≤
        (Nat.choose i j : ℝ) *
          (D * (R : ℝ) ^ (d - 1) / (N : ℝ) ^ j) := by
    have hb := hMemBounds i hi
    have hcomb :
        (r : ℝ) ^ (d - 1 - i) * (r : ℝ) ^ (i - j) =
          (r : ℝ) ^ (d - 1 - j) := by
      calc
        (r : ℝ) ^ (d - 1 - i) * (r : ℝ) ^ (i - j) =
            (r : ℝ) ^ ((d - 1 - i) + (i - j)) := by rw [← pow_add]
        _ = (r : ℝ) ^ (d - 1 - j) := by congr 1 <;> omega
    have huPow : u ^ i ≤ u ^ j :=
      pow_le_pow_of_le_one huNonneg huLeOne (by omega)
    have hmAbs :
        |(m i : ℝ)| ≤
          (Nat.choose i j : ℝ) * (r : ℝ) ^ (d - 1 - i) *
            (r : ℝ) ^ (i - j) := by
      have hchoose : 0 ≤ (Nat.choose i j : ℝ) := by positivity
      have hrpow : 0 ≤ (r : ℝ) ^ (d - 1 - i) := pow_nonneg hrNonneg _
      have hcpow : |(c : ℝ)| ^ (i - j) ≤ (r : ℝ) ^ (i - j) :=
        pow_le_pow_left₀ (abs_nonneg _) hc _
      rw [hmCast, abs_mul, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (pow_nonneg hrNonneg _), abs_pow, abs_neg]
      exact mul_le_mul_of_nonneg_left hcpow (mul_nonneg hchoose hrpow)
    calc
      |(m i : ℝ)| * (D * u ^ i) ≤
          ((Nat.choose i j : ℝ) * (r : ℝ) ^ (d - 1 - i) *
            (r : ℝ) ^ (i - j)) * (D * u ^ i) :=
        mul_le_mul_of_nonneg_right hmAbs
          (mul_nonneg hDNonneg (pow_nonneg huNonneg _))
      _ = ((Nat.choose i j : ℝ) * D) *
          ((r : ℝ) ^ (d - 1 - i) * (r : ℝ) ^ (i - j)) * u ^ i := by ring
      _ = ((Nat.choose i j : ℝ) * D) *
          (r : ℝ) ^ (d - 1 - j) * u ^ i := by rw [hcomb]
      _ ≤ ((Nat.choose i j : ℝ) * D) *
          (r : ℝ) ^ (d - 1 - j) * u ^ j := by
        apply mul_le_mul_of_nonneg_left huPow
        positivity
      _ = (Nat.choose i j : ℝ) *
          (D * (r : ℝ) ^ (d - 1 - j) * u ^ j) := by ring
      _ = (Nat.choose i j : ℝ) *
          (D * (r : ℝ) ^ (d - 1) / (N : ℝ) ^ j) := by rw [hnormal]
      _ ≤ (Nat.choose i j : ℝ) *
          (D * R ^ (d - 1) / (N : ℝ) ^ j) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRPow hDNonneg) (le_of_lt hNjPos)
  have hsumBound :
      (∑ i ∈ S, |(m i : ℝ)| * (D * u ^ i)) ≤
        (2 : ℝ) ^ d * (D * R ^ (d - 1) / (N : ℝ) ^ j) := by
    calc
      (∑ i ∈ S, |(m i : ℝ)| * (D * u ^ i)) ≤
          ∑ i ∈ S, (Nat.choose i j : ℝ) *
            (D * R ^ (d - 1) / (N : ℝ) ^ j) :=
        Finset.sum_le_sum fun i hi => hterm i hi
      _ = (∑ i ∈ S, (Nat.choose i j : ℝ)) *
          (D * R ^ (d - 1) / (N : ℝ) ^ j) := by rw [Finset.sum_mul]
      _ = (Nat.choose d (j + 1) : ℝ) *
          (D * R ^ (d - 1) / (N : ℝ) ^ j) := by rw [hchooseSumReal]
      _ ≤ (2 : ℝ) ^ d *
          (D * R ^ (d - 1) / (N : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_right hchooseBoundReal hCNonneg
  calc
    realDistanceToIntegers
        (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff j) ≤
        (2 : ℝ) ^ d * (D * R ^ (d - 1) / (N : ℝ) ^ j) :=
      hdistInv.trans hsumBound
    _ = (2 : ℝ) ^ d * D * R ^ (d - 1) / (N : ℝ) ^ j := by ring

end FractionalPrimes.Literature.Polynomial
