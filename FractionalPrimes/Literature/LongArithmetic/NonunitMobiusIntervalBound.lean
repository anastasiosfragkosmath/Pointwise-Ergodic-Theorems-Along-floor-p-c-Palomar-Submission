module
public import FractionalPrimes.Literature.LongArithmetic.NonunitMobiusPrefixBound
@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.MobiusToLong

namespace FractionalPrimes.Literature.LongArithmetic

/-- The Möbius sum on the natural interval `(X,X+L]` in residue class
`a mod q`. -/
def mobiusResidueIntervalSumNat (q a X L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (X + L),
    if n % q = a then (ArithmeticFunction.moebius n : ℝ) else 0

private theorem mobiusResidueIntervalSumNat_eq_prefix_difference
    (q a X L : ℕ) :
    mobiusResidueIntervalSumNat q a X L =
      mobiusResidueSumReal q a ((X + L : ℕ) : ℝ) -
        mobiusResidueSumReal q a (X : ℝ) := by
  rw [mobiusResidueIntervalSumNat,
    sum_Ioc_eq_sum_Icc_sub_of_le (Nat.le_add_right X L)]
  simp only [mobiusResidueSumReal, mobiusResidueSumNat, Nat.floor_natCast]

private theorem mobiusResiduePrefixBound_of_unitUSW
    {K B C : ℝ} (hC : 0 < C)
    (hprefix : ∀ (Y : ℝ), 3 ≤ Y → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (Real.log Y) ^ (B + 1) →
      ∀ a : ℤ, IsCoprime a (q : ℤ) →
        |mobiusUnitResidueSumReal q a Y| ≤
          C * Y * (Real.log Y) ^ (-K))
    {q a : ℕ} (hq : 0 < q) (ha : a < q) {Y : ℝ}
    (hYg : 3 ≤ Y / (Nat.gcd a q : ℝ))
    (hqYg : (q : ℝ) ≤
      (Real.log (Y / (Nat.gcd a q : ℝ))) ^ (B + 1)) :
    |mobiusResidueSumReal q a Y| ≤
      (Nat.gcd a q : ℝ) * C *
        (Y / (Nat.gcd a q : ℝ)) *
          (Real.log (Y / (Nat.gcd a q : ℝ))) ^ (-K) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  let g : ℕ := Nat.gcd a q
  let R : Finset ℕ := mobiusResidueUnitRemainders q a
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_right a hq
  have hgposR : 0 < (g : ℝ) := by exact_mod_cast hgpos
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hgpos.ne')
  have hYlower : 3 * (g : ℝ) ≤ Y :=
    (le_div_iff₀ hgposR).mp hYg
  have hYone : 1 ≤ Y := by nlinarith
  have hYglog : 0 < Real.log (Y / (g : ℝ)) :=
    Real.log_pos (by linarith)
  have hred := mobiusResidueUnitReduction hq ha Y hYone
  by_cases hsq : Squarefree g
  · obtain ⟨hcard, hdecomp⟩ := hred.2 (by simpa [g] using hsq)
    rw [hdecomp, Finset.mul_sum]
    have hterm (b : ℕ) (hb : b ∈ R) :
        |(ArithmeticFunction.moebius g : ℝ) *
            mobiusResidueSumReal q b (Y / (g : ℝ))| ≤
          C * (Y / (g : ℝ)) *
            (Real.log (Y / (g : ℝ))) ^ (-K) := by
      have hb' : b ∈ mobiusResidueUnitRemainders q a := by
        simpa [R] using hb
      have hbmem : b ∈ (Finset.range q).filter
          (fun b => Nat.Coprime b q ∧
            b % (q / Nat.gcd a q) = a / Nat.gcd a q) := by
        simpa [mobiusResidueUnitRemainders] using hb'
      have hbq : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hbmem).1
      have hbcop : Nat.Coprime b q := (Finset.mem_filter.mp hbmem).2.1
      have hbcopZ : IsCoprime (b : ℤ) (q : ℤ) := by
        rw [Int.isCoprime_iff_nat_coprime]
        simpa using hbcop
      have hunit := hprefix (Y / (g : ℝ)) hYg q hq1 hqYg
        (b : ℤ) hbcopZ
      rw [mobiusResidueSumReal_eq_mobiusUnitResidueSumReal hq hbq]
      have hmu : |(ArithmeticFunction.moebius g : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := g))
      rw [abs_mul]
      calc
        |(ArithmeticFunction.moebius g : ℝ)| *
            |mobiusUnitResidueSumReal q (b : ℤ) (Y / (g : ℝ))| ≤
          1 * |mobiusUnitResidueSumReal q (b : ℤ) (Y / (g : ℝ))| :=
            mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ ≤ 1 * (C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K)) :=
            mul_le_mul_of_nonneg_left hunit (by norm_num)
        _ = C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K) := by ring
    have hsum :
        |∑ b ∈ R, (ArithmeticFunction.moebius g : ℝ) *
            mobiusResidueSumReal q b (Y / (g : ℝ))| ≤
          ∑ b ∈ R, C * (Y / (g : ℝ)) *
            (Real.log (Y / (g : ℝ))) ^ (-K) := by
      calc
        _ ≤ ∑ b ∈ R, |(ArithmeticFunction.moebius g : ℝ) *
              mobiusResidueSumReal q b (Y / (g : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b ∈ R, C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K) :=
          Finset.sum_le_sum fun b hb => hterm b (by simpa [R] using hb)
    have hMnonneg : 0 ≤ C * (Y / (g : ℝ)) *
        (Real.log (Y / (g : ℝ))) ^ (-K) := by positivity
    have hcardR : (R.card : ℝ) ≤ (g : ℝ) := by
      exact_mod_cast (by simpa [R, g] using hcard)
    calc
      |∑ b ∈ R, (ArithmeticFunction.moebius g : ℝ) *
          mobiusResidueSumReal q b (Y / (g : ℝ))| ≤
          (R.card : ℝ) *
            (C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K)) := by
        simpa [R] using hsum
      _ ≤ (g : ℝ) *
            (C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K)) :=
        mul_le_mul_of_nonneg_right hcardR hMnonneg
      _ = (Nat.gcd a q : ℝ) * C *
            (Y / (Nat.gcd a q : ℝ)) *
              (Real.log (Y / (Nat.gcd a q : ℝ))) ^ (-K) := by
        dsimp [g]
        ring
  · have hzero : mobiusResidueSumReal q a Y = 0 :=
      hred.1 (by simpa [g] using hsq)
    rw [hzero]
    simp only [abs_zero]
    positivity

/-- The source-order nonunit Möbius interval estimate. The endpoint quotient
conditions and half-log comparisons are exactly the consequences of (L1) in
the Astra proof. The single constant is chosen once from `USW(K,B+1)` and is
used at both endpoints. -/
theorem nonunitMobiusIntervalBound_of_USW
    (hUSW : UnitGlobalProperty) {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R)
    {X L q a : ℕ} (hX : 3 ≤ X)
    (hXL : (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ))
    (hLX : L ≤ X) (hq : 0 < q) (ha : a < q)
    (hXg : 3 ≤ (X : ℝ) / (Nat.gcd a q : ℝ))
    (hXplusLg : 3 ≤ ((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))
    (hqXg : (q : ℝ) ≤
      (Real.log ((X : ℝ) / (Nat.gcd a q : ℝ))) ^ (B + 1))
    (hqXplusLg : (q : ℝ) ≤
      (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (B + 1))
    (hlogXg : Real.log (X : ℝ) / 2 ≤
      Real.log ((X : ℝ) / (Nat.gcd a q : ℝ)))
    (hlogXplusLg : Real.log (X : ℝ) / 2 ≤
      Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) :
    ∃ C : ℝ, 0 < C ∧
      |mobiusResidueIntervalSumNat q a X L| ≤
        3 * 2 ^ (A + R + 2) * C * (L : ℝ) *
          (Real.log (X : ℝ)) ^ (-A) := by
  let K : ℝ := A + R + 2
  have hK : 0 < K := by dsimp [K]; linarith
  obtain ⟨C, hC, hprefix⟩ :=
    hUSW K (B + 1) hK (by linarith : 0 < B + 1)
  have hunitPrefix : ∀ (Y : ℝ), 3 ≤ Y → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (Real.log Y) ^ (B + 1) →
      ∀ a : ℤ, IsCoprime a (q : ℤ) →
        |mobiusUnitResidueSumReal q a Y| ≤
          C * Y * (Real.log Y) ^ (-K) := by
    intro Y hY q hq hqY a ha
    exact (hprefix Y hY q hq hqY a ha).1
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  have hgposNat : 0 < Nat.gcd a q := Nat.gcd_pos_of_pos_right a hq
  have hgpos : 0 < (Nat.gcd a q : ℝ) := by exact_mod_cast hgposNat
  have hXreal : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by linarith
  have hLleX : (L : ℝ) ≤ (X : ℝ) := by exact_mod_cast hLX
  have hXplusLle : ((X + L : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
    rw [Nat.cast_add]
    nlinarith
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogXone : 1 ≤ Real.log (X : ℝ) := by
    have hexp1 : Real.exp 1 < 3 := by
      have h := Real.exp_one_lt_d9
      norm_num at h ⊢
      linarith
    apply (Real.le_log_iff_exp_le hXpos).2
    exact le_trans hexp1.le hXreal
  have hhalfPos : 0 < Real.log (X : ℝ) / 2 := by positivity
  have hKneg : -K ≤ 0 := by linarith
  have hscale : (Real.log (X : ℝ) / 2) ^ (-K) =
      2 ^ K * (Real.log (X : ℝ)) ^ (-K) := by
    rw [Real.div_rpow hlogXpos.le (by norm_num) (-K)]
    rw [Real.rpow_neg hlogXpos.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) K]
    field_simp
  have hlogXgpow :
      (Real.log ((X : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) ≤
        (Real.log (X : ℝ) / 2) ^ (-K) :=
    Real.rpow_le_rpow_of_nonpos hhalfPos hlogXg hKneg
  have hlogXplusLgpow :
      (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) ≤
        (Real.log (X : ℝ) / 2) ^ (-K) :=
    Real.rpow_le_rpow_of_nonpos hhalfPos hlogXplusLg hKneg
  have hprefixX := mobiusResiduePrefixBound_of_unitUSW
    hC hunitPrefix hq ha hXg hqXg
  have hprefixXplusL := mobiusResiduePrefixBound_of_unitUSW
    hC hunitPrefix hq ha hXplusLg hqXplusLg
  have hprefixX' :
      |mobiusResidueSumReal q a (X : ℝ)| ≤
        C * (X : ℝ) *
          (Real.log ((X : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) := by
    calc
      _ ≤ (Nat.gcd a q : ℝ) * C *
            ((X : ℝ) / (Nat.gcd a q : ℝ)) *
              (Real.log ((X : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) := hprefixX
      _ = C * (X : ℝ) *
            (Real.log ((X : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) := by
        field_simp [ne_of_gt hgpos]
  have hprefixXplusL' :
      |mobiusResidueSumReal q a ((X + L : ℕ) : ℝ)| ≤
        C * ((X + L : ℕ) : ℝ) *
          (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) := by
    calc
      _ ≤ (Nat.gcd a q : ℝ) * C *
            (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ)) *
              (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) :=
        hprefixXplusL
      _ = C * ((X + L : ℕ) : ℝ) *
            (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) := by
        field_simp [ne_of_gt hgpos]
  have hprefixXbound :
      |mobiusResidueSumReal q a (X : ℝ)| ≤
        2 ^ K * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
    calc
      _ ≤ C * (X : ℝ) *
          (Real.log ((X : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) := hprefixX'
      _ ≤ C * (X : ℝ) *
          (Real.log (X : ℝ) / 2) ^ (-K) :=
        mul_le_mul_of_nonneg_left hlogXgpow (by positivity)
      _ = 2 ^ K * C * (X : ℝ) *
          (Real.log (X : ℝ)) ^ (-K) := by rw [hscale]; ring
  have hprefixXplusLbound :
      |mobiusResidueSumReal q a ((X + L : ℕ) : ℝ)| ≤
        2 ^ K * C * (2 * (X : ℝ)) * (Real.log (X : ℝ)) ^ (-K) := by
    calc
      _ ≤ C * ((X + L : ℕ) : ℝ) *
          (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) :=
        hprefixXplusL'
      _ ≤ C * (2 * (X : ℝ)) *
          (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hXplusLle (le_of_lt hC)
        · exact Real.rpow_nonneg (Real.log_nonneg (by linarith [hXplusLg])) _
      _ ≤ C * (2 * (X : ℝ)) * (Real.log (X : ℝ) / 2) ^ (-K) :=
        mul_le_mul_of_nonneg_left hlogXplusLgpow (by positivity)
      _ = 2 ^ K * C * (2 * (X : ℝ)) *
          (Real.log (X : ℝ)) ^ (-K) := by rw [hscale]; ring
  have hinterval :
      |mobiusResidueIntervalSumNat q a X L| ≤
        3 * 2 ^ K * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
    rw [mobiusResidueIntervalSumNat_eq_prefix_difference]
    calc
      _ ≤ |mobiusResidueSumReal q a ((X + L : ℕ) : ℝ)| +
          |mobiusResidueSumReal q a (X : ℝ)| := abs_sub _ _
      _ ≤ 2 ^ K * C * (2 * (X : ℝ)) * (Real.log (X : ℝ)) ^ (-K) +
          2 ^ K * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) :=
        add_le_add hprefixXplusLbound hprefixXbound
      _ = 3 * 2 ^ K * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by ring
  have hcancel :
      (Real.log (X : ℝ)) ^ (-R) * (Real.log (X : ℝ)) ^ R = 1 := by
    rw [← Real.rpow_add hlogXpos]
    have : -R + R = 0 := by ring
    rw [this, Real.rpow_zero]
  have hXLmul : (X : ℝ) ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ R := by
    have hmul := mul_le_mul_of_nonneg_right hXL
      (Real.rpow_nonneg hlogXpos.le R)
    calc
      (X : ℝ) = (X : ℝ) *
          ((Real.log (X : ℝ)) ^ (-R) * (Real.log (X : ℝ)) ^ R) := by
            rw [hcancel, mul_one]
      _ = ((X : ℝ) * (Real.log (X : ℝ)) ^ (-R)) *
          (Real.log (X : ℝ)) ^ R := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ R := hmul
  have hpowerFinal :
      (Real.log (X : ℝ)) ^ (-K) * (Real.log (X : ℝ)) ^ R ≤
        (Real.log (X : ℝ)) ^ (-A) := by
    rw [← Real.rpow_add hlogXpos]
    have hexp : -K + R = -A - 2 := by dsimp [K]; ring
    rw [hexp]
    exact Real.rpow_le_rpow_of_exponent_le hlogXone (by linarith)
  have hfinalScale : (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) ≤
      (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
    calc
      _ ≤ ((L : ℝ) * (Real.log (X : ℝ)) ^ R) *
          (Real.log (X : ℝ)) ^ (-K) :=
        mul_le_mul_of_nonneg_right hXLmul
          (Real.rpow_nonneg hlogXpos.le _)
      _ = (L : ℝ) *
          ((Real.log (X : ℝ)) ^ (-K) * (Real.log (X : ℝ)) ^ R) := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) :=
        mul_le_mul_of_nonneg_left hpowerFinal (by positivity)
  refine ⟨C, hC, ?_⟩
  calc
    |mobiusResidueIntervalSumNat q a X L| ≤
        3 * 2 ^ K * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := hinterval
    _ = (3 * 2 ^ K * C) *
          ((X : ℝ) * (Real.log (X : ℝ)) ^ (-K)) := by ring
    _ ≤ (3 * 2 ^ K * C) *
          ((L : ℝ) * (Real.log (X : ℝ)) ^ (-A)) :=
      mul_le_mul_of_nonneg_left hfinalScale (by positivity)
    _ = 3 * 2 ^ (A + R + 2) * C * (L : ℝ) *
          (Real.log (X : ℝ)) ^ (-A) := by simp [K] <;> ring

end FractionalPrimes.Literature.LongArithmetic
