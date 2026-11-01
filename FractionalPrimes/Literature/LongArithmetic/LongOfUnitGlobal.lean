module
public import FractionalPrimes.Literature.LongArithmetic.NonunitMobiusIntervalBound
public import FractionalPrimes.Literature.LongArithmetic.NonunitVonMangoldtBound
public import FractionalPrimes.Literature.LongArithmetic.UnitGlobalIntervalBounds
public import FractionalPrimes.Literature.LongArithmetic.CramerResidueModelReduction
public import FractionalPrimes.Literature.LongArithmetic.LongOfUnitThreshold
public import FractionalPrimes.CramerDensityAtScale
public import FractionalPrimes.Literature.Uniformity.CramerShortDivisor
@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.MobiusToLong

namespace FractionalPrimes.Literature.LongArithmetic

/-- The finite set of moduli in the exact LONG range. The ceiling makes the
set finite, and the filter retains precisely the real cutoff condition. -/
def longModuliRange (X : ℕ) (B : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.ceil ((Real.log (X : ℝ)) ^ B))).filter
    (fun q => (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B)

theorem mem_longModuliRange_iff {X q : ℕ} {B : ℝ} :
    q ∈ longModuliRange X B ↔
      1 ≤ q ∧ (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B := by
  simp only [longModuliRange, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hq1, _⟩, hqX⟩
    exact ⟨hq1, hqX⟩
  · rintro ⟨hq1, hqX⟩
    refine ⟨⟨hq1, ?_⟩, hqX⟩
    exact_mod_cast hqX.trans (Nat.le_ceil ((Real.log (X : ℝ)) ^ B))

/-- The natural-index Möbius interval sum used in the LONG maximum. -/
def longMobiusResidueIntervalSum (q a X L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (X + L),
    if n % q = a then (ArithmeticFunction.moebius n : ℝ) else 0

/-- For the canonical natural representative `a<q`, the natural-modulus
interval sum in the LONG maximum is exactly the `ZMod`-indicator sum used by
the unit-class USW estimate. -/
theorem longMobiusResidueIntervalSum_eq_unit
    {q a X L : ℕ} (hq : 0 < q) (ha : a < q) :
    longMobiusResidueIntervalSum q a X L =
      unitMobiusIntervalSum q (a : ℤ) X L := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  unfold longMobiusResidueIntervalSum unitMobiusIntervalSum
  apply Finset.sum_congr rfl
  intro n hn
  have hres :
      ((a : ℤ) : ZMod q) = ((n : ℤ) : ZMod q) ↔ n % q = a := by
    rw [ZMod.intCast_eq_intCast_iff']
    have hmodNat : a % q = n % q ↔ n % q = a := by
      rw [Nat.mod_eq_of_lt ha]
      omega
    rw [← Int.natCast_mod, ← Int.natCast_mod]
    exact_mod_cast hmodNat
  simp only [hres]

/-- The natural-index interval sum of `Λ - Cr_X` in one residue class. -/
def longLambdaCramerResidueIntervalSum (q a X L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (X + L),
    if n % q = a then
      vonMangoldtWeight n -
        paperShortBlockCramerWeight (X : ℝ) (n : ℤ)
    else 0

/-- A natural remainder equality in a canonical residue representative
is the exact integer congruence used by the Cramér and nonunit bounds. -/
theorem longNatResidue_modEq {q a n : ℕ} (ha : a < q)
    (hres : n % q = a) :
    (n : ℤ) ≡ (a : ℤ) [ZMOD (q : ℤ)] := by
  apply Int.natCast_modEq_iff.mpr
  change n % q = a % q
  rwa [Nat.mod_eq_of_lt ha]

/-- The non-coprime alternative in the LONG finite maximum is exactly
the integer-gcd condition used by the nonunit arithmetic lemmas. -/
theorem longNoncoprime_gcd_gt_one {q a : ℕ} (hq : 0 < q)
    (hnot : ¬ Nat.Coprime a q) :
    1 < Int.gcd (a : ℤ) (q : ℤ) := by
  have hgpos : 0 < Nat.gcd a q := Nat.gcd_pos_of_pos_right a hq
  have hne : Nat.gcd a q ≠ 1 := by
    simpa only [Nat.Coprime] using hnot
  have hg : 1 < Nat.gcd a q := by omega
  simpa [Int.gcd_def] using hg

/-- The natural-index von Mangoldt interval sum in one residue class, before
subtracting the Cramér model. This is the natural-residue form of
`unitVonMangoldtIntervalSum` used in the common-constant unit family. -/
def longVonMangoldtResidueIntervalSum (q a X L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (X + L),
    if n % q = a then vonMangoldtWeight n else 0

/-- For the canonical representative `a<q`, the natural-modulus von
Mangoldt interval sum is exactly the `ZMod`-indicator interval sum. -/
theorem longVonMangoldtResidueIntervalSum_eq_unit
    {q a X L : ℕ} (hq : 0 < q) (ha : a < q) :
    longVonMangoldtResidueIntervalSum q a X L =
      unitVonMangoldtIntervalSum q (a : ℤ) X L := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  unfold longVonMangoldtResidueIntervalSum unitVonMangoldtIntervalSum
  apply Finset.sum_congr rfl
  intro n hn
  have hres :
      ((a : ℤ) : ZMod q) = ((n : ℤ) : ZMod q) ↔ n % q = a := by
    rw [ZMod.intCast_eq_intCast_iff']
    have hmodNat : a % q = n % q ↔ n % q = a := by
      rw [Nat.mod_eq_of_lt ha]
      omega
    rw [← Int.natCast_mod, ← Int.natCast_mod]
    exact_mod_cast hmodNat
  simp only [hres]

/-- The natural-index Cramér model sum in one residue class is exactly the
integer-floor sum appearing in `cramerResidueMean`. The interval remains
`(X, X+L]` on both sides. -/
theorem longCramerNaturalResidueSum_eq_real
    {q a X L : ℕ} (ha : a < q) :
    (∑ n ∈ Finset.Ioc X (X + L),
      if n % q = a then
        paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0) =
    (∑ n ∈ (Finset.Ioc (Int.floor (X : ℝ))
        (Int.floor ((X : ℝ) + (L : ℝ)))).filter
          (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]),
        paperShortBlockCramerWeight (X : ℝ) n) := by
  have hfloorX : Int.floor (X : ℝ) = (X : ℤ) := by
    exact_mod_cast (Int.floor_natCast X)
  have hfloorY : Int.floor ((X : ℝ) + (L : ℝ)) = ((X + L : ℕ) : ℤ) := by
    rw [← Nat.cast_add]
    exact_mod_cast (Int.floor_natCast (X + L))
  rw [hfloorX, hfloorY, ← Finset.sum_filter]
  have hfilter :
      (Finset.Ioc X (X + L)).filter (fun n => n % q = a) =
        {n ∈ Finset.Ioc X (X + L) | n ≡ a [MOD q]} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hnI, hmod⟩
      refine ⟨hnI, ?_⟩
      change n % q = a % q
      rw [Nat.mod_eq_of_lt ha]
      exact hmod
    · rintro ⟨hnI, hmod⟩
      refine ⟨hnI, ?_⟩
      change n % q = a % q at hmod
      rw [Nat.mod_eq_of_lt ha] at hmod
      exact hmod
  rw [hfilter]
  rw [← Nat.Ioc_filter_modEq_cast (a := X) (b := X + L) (v := a) (r := q)]
  rw [Finset.sum_map]
  rfl

/-- The natural-index `Λ-Cr_X` interval sum is the difference of the
von Mangoldt residue sum and the corresponding Cramér-model sum. -/
theorem longLambdaCramerResidueIntervalSum_eq_vonMangoldt_sub_model
    (q a X L : ℕ) :
    longLambdaCramerResidueIntervalSum q a X L =
      longVonMangoldtResidueIntervalSum q a X L -
        (∑ n ∈ Finset.Ioc X (X + L),
          if n % q = a then
            paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0) := by
  unfold longLambdaCramerResidueIntervalSum longVonMangoldtResidueIntervalSum
  simp_rw [← Finset.sum_filter]
  rw [Finset.sum_sub_distrib]

/-- In a nonunit residue class, all prime divisors of `q` lie below the
strict Cramér cutoff, so the model vanishes pointwise on the interval. -/
theorem longLambdaCramerResidueIntervalSum_eq_vonMangoldt_nonunit
    {q a X L : ℕ} (ha : a < q)
    (hnonunit : 1 < Int.gcd (a : ℤ) (q : ℤ))
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q →
      (p : ℝ) < paperShortBlockCutoff (X : ℝ)) :
    longLambdaCramerResidueIntervalSum q a X L =
      longVonMangoldtResidueIntervalSum q a X L := by
  unfold longLambdaCramerResidueIntervalSum
    longVonMangoldtResidueIntervalSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hres : n % q = a
  · have hmod := longNatResidue_modEq ha hres
    have hzero : paperShortBlockCramerWeight (X : ℝ) (n : ℤ) = 0 := by
      simpa [paperShortBlockCramerWeight] using
        paperCramerWeight_eq_zero_of_nonunitResidue
          (paperShortBlockCutoff (X : ℝ)) q (a : ℤ) (n : ℤ)
          hnonunit hsmall hmod
    simp [hres, hzero]
  · simp [hres]

/-- The checked nonunit von Mangoldt bound applied to the exact half-open
natural interval and its canonical residue representative. -/
theorem longNonunitVonMangoldtIntervalBound
    {q a X L : ℕ} (hX : 3 ≤ X) (hq : 1 ≤ q) (ha : a < q)
    (hnonunit : 1 < Int.gcd (a : ℤ) (q : ℤ)) :
    0 ≤ longVonMangoldtResidueIntervalSum q a X L ∧
      longVonMangoldtResidueIntervalSum q a X L ≤
        (Real.log (q : ℝ) / Real.log 2) *
          Real.log ((X + L : ℕ) : ℝ) := by
  let S : Finset ℕ := (Finset.Ioc X (X + L)).filter
    (fun n => n % q = a)
  have hS : S ⊆ Finset.Icc 1
      (Nat.floor (((X + L : ℕ) : ℝ))) := by
    intro n hn
    have hnI : n ∈ Finset.Ioc X (X + L) :=
      (Finset.mem_filter.mp hn).1
    simp only [Finset.mem_Icc, Nat.floor_natCast]
    have hnBounds := Finset.mem_Ioc.mp hnI
    omega
  have hres : ∀ n ∈ S,
      (n : ℤ) ≡ (a : ℤ) [ZMOD (q : ℤ)] := by
    intro n hn
    exact longNatResidue_modEq ha (Finset.mem_filter.mp hn).2
  have hsum : longVonMangoldtResidueIntervalSum q a X L =
      ∑ n ∈ S, vonMangoldtWeight n := by
    unfold longVonMangoldtResidueIntervalSum S
    rw [Finset.sum_filter]
  have hY : (2 : ℝ) ≤ ((X + L : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 ≤ X + L)
  have hbound := nonunitVonMangoldtSubsumBound
    (Y := ((X + L : ℕ) : ℝ)) hY hq hnonunit S hS hres
  simpa only [hsum] using hbound

/-- The two exact cutoff inequalities in (L1) supply the scale and strict
prime-divisor hypotheses required by `cramerResidueMean`. -/
theorem longCramerResidueCutoff_of_threshold
    {X : ℝ} (hX : 3 ≤ X) {B : ℝ} {q : ℕ}
    (hq : 1 ≤ q) (hqX : (q : ℝ) ≤ (Real.log X) ^ B)
    (hprimeScale : (Real.log X) ^ B <
      Real.exp ((Real.log X) ^ (1 / 10 : ℝ)))
    (hintervalScale : (Real.log X) ^ (1 / 10 : ℝ) ≤ Real.log X / 16) :
    paperShortBlockCutoff X ≤ X ^ (1 / 16 : ℝ) ∧
      ∀ p : ℕ, p.Prime → p ∣ q →
        (p : ℝ) < paperShortBlockCutoff X := by
  have hXpos : 0 < X := by linarith
  have hscale : paperShortBlockCutoff X ≤ X ^ (1 / 16 : ℝ) := by
    rw [paperShortBlockCutoff]
    have hpow : X ^ (1 / 16 : ℝ) = Real.exp (Real.log X / 16) := by
      rw [Real.rpow_def_of_pos hXpos]
      congr 1
      ring
    rw [hpow]
    exact Real.exp_le_exp.mpr hintervalScale
  refine ⟨hscale, ?_⟩
  intro p hp hpq
  have hpqNat : p ≤ q := Nat.le_of_dvd (by omega) hpq
  have hpqReal : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpqNat
  calc
    (p : ℝ) ≤ (q : ℝ) := hpqReal
    _ ≤ (Real.log X) ^ B := hqX
    _ < Real.exp ((Real.log X) ^ (1 / 10 : ℝ)) := hprimeScale
    _ = paperShortBlockCutoff X := by rfl

/-- Both exact gcd-quotient endpoint hypotheses consumed by the checked
nonunit Möbius interval family. The inequalities are obtained uniformly
from the two corresponding (L1) clauses and `gcd(a,q) ≤ q`. -/
theorem longNonunitEndpointHypotheses
    {X L q a : ℕ} {B : ℝ} (hX : 3 ≤ X) (hq : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B)
    (hB : 0 < B)
    (hBlog : B * Real.log (Real.log (X : ℝ)) ≤
      Real.log (X : ℝ) / 2)
    (hhalf : max (Real.log 3) (2 ^ B) ≤
      Real.log (X : ℝ) / 2) :
    (3 ≤ (X : ℝ) / (Nat.gcd a q : ℝ) ∧
      (q : ℝ) ≤
        (Real.log ((X : ℝ) / (Nat.gcd a q : ℝ))) ^ (B + 1) ∧
      Real.log (X : ℝ) / 2 ≤
        Real.log ((X : ℝ) / (Nat.gcd a q : ℝ))) ∧
    (3 ≤ ((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ) ∧
      (q : ℝ) ≤
        (Real.log (((X + L : ℕ) : ℝ) /
          (Nat.gcd a q : ℝ))) ^ (B + 1) ∧
      Real.log (X : ℝ) / 2 ≤
        Real.log (((X + L : ℕ) : ℝ) /
          (Nat.gcd a q : ℝ))) := by
  have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hgpos : 0 < Nat.gcd a q := Nat.gcd_pos_of_pos_right a hqpos
  have hg1 : (1 : ℝ) ≤ (Nat.gcd a q : ℝ) := by exact_mod_cast hgpos
  have hgq : (Nat.gcd a q : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.gcd_le_right a hqpos
  have hXreal : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have ht : 0 < Real.log (X : ℝ) := Real.log_pos (by
    exact_mod_cast (by omega : 1 < X))
  have hY : (X : ℝ) ≤ ((X + L : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right X L
  exact ⟨longNonunitEndpointRange hXreal le_rfl hg1 hgq hqX
      hB ht hBlog hhalf,
    longNonunitEndpointRange hXreal hY hg1 hgq hqX
      hB ht hBlog hhalf⟩

/-- The exact large-scale nonunit `Λ-Cr_X` interval estimate after all
three source ingredients: strict-cutoff model vanishing, the nonunit
von Mangoldt subsum bound, and the mixed (L1) absorption clause. -/
theorem longNonunitLambdaCramerIntervalBound_of_L1
    {A B R : ℝ} {X L q a : ℕ}
    (hX : 3 ≤ X)
    (hXL : (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ))
    (hLX : L ≤ X) (hq : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B)
    (hprimeScale : (Real.log (X : ℝ)) ^ B <
      Real.exp ((Real.log (X : ℝ)) ^ (1 / 10 : ℝ)))
    (hintervalScale : (Real.log (X : ℝ)) ^ (1 / 10 : ℝ) ≤
      Real.log (X : ℝ) / 16)
    (hmixed :
      (B * Real.log (Real.log (X : ℝ)) / Real.log 2) *
          (Real.log (X : ℝ) + Real.log 2) ≤
        Real.exp (Real.log (X : ℝ)) *
          (Real.log (X : ℝ)) ^ (-A - R))
    (ha : a < q) (hnonunit : 1 < Int.gcd (a : ℤ) (q : ℤ)) :
    |longLambdaCramerResidueIntervalSum q a X L| ≤
      (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hcutoff := longCramerResidueCutoff_of_threshold
    hXreal hq hqX hprimeScale hintervalScale
  have hmodelZero :=
    longLambdaCramerResidueIntervalSum_eq_vonMangoldt_nonunit
      (L := L) ha hnonunit hcutoff.2
  obtain ⟨hLambdaNonneg, hLambdaBound⟩ :=
    longNonunitVonMangoldtIntervalBound (L := L) hX hq ha hnonunit
  have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hLXreal : (L : ℝ) ≤ (X : ℝ) := by exact_mod_cast hLX
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hAbsorb := longNonunitLambdaAbsorption
    hXreal hLnonneg hLXreal hXL hqreal hqX hmixed
  rw [hmodelZero, abs_of_nonneg hLambdaNonneg]
  exact hLambdaBound.trans (by
    simpa only [Nat.cast_add] using hAbsorb)

/-- The first and last L1 decay clauses absorb the two exact error terms in
`cramerResidueMean` when `y=X^(1/16)`. -/
theorem longCramerMeanError_le_of_L1
    {A R X H φ : ℝ} (hX : 3 ≤ X) (hH : 0 < H)
    (hXL : X * (Real.log X) ^ (-R) ≤ H)
    (hφ : 1 ≤ φ)
    (hfirst : sieveD *
      Real.exp (-(Real.log X) ^ (9 / 10 : ℝ) / 16) ≤
        (Real.log X) ^ (-A))
    (hsecond : Real.exp 13 * (Real.log X) ^ (R + 2 / 5 : ℝ) *
      Real.exp (-15 * Real.log X / 16) ≤ (Real.log X) ^ (-A)) :
    sieveD * (H / φ) *
        Real.exp (-(Real.log (X ^ (1 / 16 : ℝ)) /
          Real.log (paperShortBlockCutoff X))) +
      paperCramerDensity (paperShortBlockCutoff X) * X ^ (1 / 16 : ℝ) ≤
        2 * H * (Real.log X) ^ (-A) := by
  have hXpos : 0 < X := by linarith
  have htpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hφpos : 0 < φ := by linarith
  have htNonneg : 0 ≤ Real.log X := htpos.le
  have hcutLog : Real.log (paperShortBlockCutoff X) =
      (Real.log X) ^ (1 / 10 : ℝ) := by
    rw [paperShortBlockCutoff, Real.log_exp]
  have hpowLog : Real.log (X ^ (1 / 16 : ℝ)) =
      (1 / 16 : ℝ) * Real.log X := by
    rw [Real.log_rpow hXpos]
  have hrpowSub : (Real.log X) ^ (9 / 10 : ℝ) =
      (Real.log X) / (Real.log X) ^ (1 / 10 : ℝ) := by
    rw [show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num,
      Real.rpow_sub htpos, Real.rpow_one]
  have hratio :
      Real.log (X ^ (1 / 16 : ℝ)) /
          Real.log (paperShortBlockCutoff X) =
        (Real.log X) ^ (9 / 10 : ℝ) / 16 := by
    rw [hpowLog, hcutLog, hrpowSub]
    field_simp
    <;> ring
  have herrorExp :
      Real.exp (-(Real.log (X ^ (1 / 16 : ℝ)) /
          Real.log (paperShortBlockCutoff X))) =
        Real.exp (-(Real.log X) ^ (9 / 10 : ℝ) / 16) := by
    rw [hratio]
    congr 1
    ring
  have hfirstBound : sieveD * (H / φ) *
        Real.exp (-(Real.log (X ^ (1 / 16 : ℝ)) /
          Real.log (paperShortBlockCutoff X))) ≤
        H * (Real.log X) ^ (-A) := by
    rw [herrorExp]
    have hdiv : H / φ ≤ H := by
      apply (div_le_iff₀ hφpos).2
      nlinarith
    calc
      _ = (sieveD *
            Real.exp (-(Real.log X) ^ (9 / 10 : ℝ) / 16)) * (H / φ) := by ring
      _ ≤ (Real.log X) ^ (-A) * (H / φ) :=
        mul_le_mul_of_nonneg_right hfirst (div_nonneg hH.le hφpos.le)
      _ ≤ (Real.log X) ^ (-A) * H :=
        mul_le_mul_of_nonneg_left hdiv (Real.rpow_nonneg htNonneg _)
      _ = H * (Real.log X) ^ (-A) := by ring
  have hdensity : paperCramerDensity (paperShortBlockCutoff X) ≤
      Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ) :=
    paperCramerDensity_at_cutoff_scale hX
  have hXexp : Real.exp (Real.log X) = X := Real.exp_log hXpos
  have hyExp : X ^ (1 / 16 : ℝ) =
      Real.exp (Real.log X / 16) := by
    rw [Real.rpow_def_of_pos hXpos]
    congr 1
    ring
  have hsplit : Real.exp (Real.log X / 16) =
      X * Real.exp (-15 * Real.log X / 16) := by
    calc
      _ = Real.exp (Real.log X + (-15 * Real.log X / 16)) := by
        congr 1
        ring
      _ = Real.exp (Real.log X) * Real.exp (-15 * Real.log X / 16) :=
        Real.exp_add _ _
      _ = X * Real.exp (-15 * Real.log X / 16) := by rw [hXexp]
  have hcancel : (Real.log X) ^ (-R) * (Real.log X) ^ R = 1 := by
    rw [← Real.rpow_add htpos]
    have hzero : -R + R = 0 := by ring
    rw [hzero, Real.rpow_zero]
  have hXle : X ≤ H * (Real.log X) ^ R := by
    have hmul := mul_le_mul_of_nonneg_right hXL
      (Real.rpow_nonneg htNonneg R)
    calc
      X = X * ((Real.log X) ^ (-R) * (Real.log X) ^ R) := by
        rw [hcancel, mul_one]
      _ = (X * (Real.log X) ^ (-R)) * (Real.log X) ^ R := by ring
      _ ≤ H * (Real.log X) ^ R := hmul
  have hsecondBound :
      paperCramerDensity (paperShortBlockCutoff X) * X ^ (1 / 16 : ℝ) ≤
        H * (Real.log X) ^ (-A) := by
    calc
      _ ≤ (Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ)) *
          X ^ (1 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right hdensity (Real.rpow_nonneg hXpos.le _)
      _ = Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ) *
          (X * Real.exp (-15 * Real.log X / 16)) := by rw [hyExp, hsplit]
      _ ≤ Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ) *
          (H * (Real.log X) ^ R * Real.exp (-15 * Real.log X / 16)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hXle (Real.exp_nonneg _)) (by positivity)
      _ = H * (Real.exp 13 *
          ((Real.log X) ^ (2 / 5 : ℝ) * (Real.log X) ^ R) *
            Real.exp (-15 * Real.log X / 16)) := by ring
      _ = H * (Real.exp 13 * (Real.log X) ^ ((2 / 5 : ℝ) + R) *
          Real.exp (-15 * Real.log X / 16)) := by
        rw [← Real.rpow_add htpos]
      _ = H * (Real.exp 13 * (Real.log X) ^ (R + 2 / 5 : ℝ) *
          Real.exp (-15 * Real.log X / 16)) := by
        congr 2
        ring
      _ ≤ H * (Real.log X) ^ (-A) :=
        mul_le_mul_of_nonneg_left hsecond hH.le
  calc
    _ ≤ H * (Real.log X) ^ (-A) + H * (Real.log X) ^ (-A) :=
      add_le_add hfirstBound hsecondBound
    _ = 2 * H * (Real.log X) ^ (-A) := by ring

/-- The first finite maximum in the exact definition of LONG. Residues are
represented by their unique natural representatives `0 ≤ a < q`. -/
def longMobiusResidueMaximum (X L : ℕ) (B : ℝ) : ℝ :=
  (((longModuliRange X B).sup fun q =>
    (Finset.range q).sup fun a =>
      (⟨|longMobiusResidueIntervalSum q a X L|,
        abs_nonneg _⟩ : NNReal)) : NNReal)

/-- The second finite maximum in the exact definition of LONG. -/
def longLambdaCramerResidueMaximum (X L : ℕ) (B : ℝ) : ℝ :=
  (((longModuliRange X B).sup fun q =>
    (Finset.range q).sup fun a =>
      (⟨|longLambdaCramerResidueIntervalSum q a X L|,
        abs_nonneg _⟩ : NNReal)) : NNReal)

private theorem unitMobiusIntervalSum_eq_prefix_difference
    (q : ℕ) (a : ℤ) (X L : ℕ) :
    unitMobiusIntervalSum q a X L =
      mobiusUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
        mobiusUnitResidueSumReal q a (X : ℝ) := by
  rw [unitMobiusIntervalSum,
    sum_Ioc_eq_sum_Icc_sub_of_le (Nat.le_add_right X L)]
  simp only [mobiusUnitResidueSumReal, Nat.floor_natCast]

private theorem unitVonMangoldtIntervalSum_eq_prefix_difference
    (q : ℕ) (a : ℤ) (X L : ℕ) :
    unitVonMangoldtIntervalSum q a X L =
      vonMangoldtUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
        vonMangoldtUnitResidueSumReal q a (X : ℝ) := by
  rw [unitVonMangoldtIntervalSum,
    sum_Ioc_eq_sum_Icc_sub_of_le (Nat.le_add_right X L)]
  simp only [vonMangoldtUnitResidueSumReal, Nat.floor_natCast]

/-- A common-constant endpoint-to-interval estimate. It isolates the exact
`3 C` endpoint accounting used in the LONG unit-class assembly. -/
private theorem long_two_endpoint_error
    {A R K C : ℝ} {X L : ℕ} {eX eY : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hC : 0 < C) (hX : 3 ≤ X)
    (hXL : (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ))
    (hLX : L ≤ X) (hK : K = A + R + 2)
    (heX : |eX| ≤ C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K))
    (heY : |eY| ≤ C * ((X + L : ℕ) : ℝ) *
      (Real.log ((X + L : ℕ) : ℝ)) ^ (-K)) :
    |eY - eX| ≤ 3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hLle : (L : ℝ) ≤ (X : ℝ) := by exact_mod_cast hLX
  have hYle : ((X + L : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
    rw [Nat.cast_add]
    nlinarith
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos (by
    have : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith)
  have hlogXone : 1 ≤ Real.log (X : ℝ) := by
    have hXge3 : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hexp1 : Real.exp 1 < 3 := by
      have h := Real.exp_one_lt_d9
      norm_num at h ⊢
      linarith
    exact (Real.le_log_iff_exp_le hXreal).2 (le_trans hexp1.le hXge3)
  have hlogMono : Real.log (X : ℝ) ≤
      Real.log ((X + L : ℕ) : ℝ) := by
    apply Real.log_le_log hXreal
    rw [Nat.cast_add]
    exact le_add_of_nonneg_right (by positivity)
  have hlogYpos : 0 < Real.log ((X + L : ℕ) : ℝ) :=
    lt_of_lt_of_le hlogXpos hlogMono
  have hKneg : -K ≤ 0 := by rw [hK]; linarith
  have hpowMono :
      (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) ≤
        (Real.log (X : ℝ)) ^ (-K) :=
    Real.rpow_le_rpow_of_nonpos hlogXpos hlogMono hKneg
  have hYbound : C * ((X + L : ℕ) : ℝ) *
      (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) ≤
        2 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
    calc
      _ ≤ C * (2 * (X : ℝ)) *
          (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hYle (le_of_lt hC)
        · exact Real.rpow_nonneg hlogYpos.le _
      _ ≤ C * (2 * (X : ℝ)) * (Real.log (X : ℝ)) ^ (-K) := by
        exact mul_le_mul_of_nonneg_left hpowMono (by positivity)
      _ = 2 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by ring
  have hcancel : (Real.log (X : ℝ)) ^ (-R) *
      (Real.log (X : ℝ)) ^ R = 1 := by
    rw [← Real.rpow_add hlogXpos]
    have hzero : -R + R = 0 := by ring
    rw [hzero, Real.rpow_zero]
  have hXLmul : (X : ℝ) ≤
      (L : ℝ) * (Real.log (X : ℝ)) ^ R := by
    have hmul := mul_le_mul_of_nonneg_right hXL
      (Real.rpow_nonneg hlogXpos.le R)
    calc
      (X : ℝ) = (X : ℝ) *
          ((Real.log (X : ℝ)) ^ (-R) *
            (Real.log (X : ℝ)) ^ R) := by rw [hcancel, mul_one]
      _ = ((X : ℝ) * (Real.log (X : ℝ)) ^ (-R)) *
          (Real.log (X : ℝ)) ^ R := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ R := hmul
  have hpowerFinal :
      (Real.log (X : ℝ)) ^ (-K) *
          (Real.log (X : ℝ)) ^ R ≤
        (Real.log (X : ℝ)) ^ (-A) := by
    rw [← Real.rpow_add hlogXpos, hK]
    have hexp : -(A + R + 2) + R = -A - 2 := by ring
    rw [hexp]
    exact Real.rpow_le_rpow_of_exponent_le hlogXone (by linarith)
  have hfinalScale : (X : ℝ) *
      (Real.log (X : ℝ)) ^ (-K) ≤
        (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
    calc
      _ ≤ ((L : ℝ) * (Real.log (X : ℝ)) ^ R) *
          (Real.log (X : ℝ)) ^ (-K) :=
        mul_le_mul_of_nonneg_right hXLmul
          (Real.rpow_nonneg hlogXpos.le _)
      _ = (L : ℝ) * ((Real.log (X : ℝ)) ^ (-K) *
          (Real.log (X : ℝ)) ^ R) := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) :=
        mul_le_mul_of_nonneg_left hpowerFinal (by positivity)
  calc
    |eY - eX| ≤ |eY| + |eX| := abs_sub _ _
    _ ≤ 3 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
      calc
        _ ≤ C * ((X + L : ℕ) : ℝ) *
              (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) +
            C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) :=
          add_le_add heY heX
        _ ≤ 2 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) +
            C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) :=
          add_le_add hYbound le_rfl
        _ = 3 * C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by ring
    _ = 3 * C * ((X : ℝ) * (Real.log (X : ℝ)) ^ (-K)) := by ring
    _ ≤ 3 * C * ((L : ℝ) * (Real.log (X : ℝ)) ^ (-A)) :=
      mul_le_mul_of_nonneg_left hfinalScale (by positivity)
    _ = 3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by ring

/-- The squarefree gcd reduction with a *fixed* unit-prefix constant. This is
the explicit-witness form needed to keep a single USW constant while applying
the reduction at both LONG interval endpoints. -/
theorem mobiusResiduePrefixBound_of_fixedUnitUSW
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
  let Rset : Finset ℕ := mobiusResidueUnitRemainders q a
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
    have hterm (b : ℕ) (hb : b ∈ Rset) :
        |(ArithmeticFunction.moebius g : ℝ) *
            mobiusResidueSumReal q b (Y / (g : ℝ))| ≤
          C * (Y / (g : ℝ)) *
            (Real.log (Y / (g : ℝ))) ^ (-K) := by
      have hb' : b ∈ mobiusResidueUnitRemainders q a := by
        simpa [Rset] using hb
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
        |∑ b ∈ Rset, (ArithmeticFunction.moebius g : ℝ) *
            mobiusResidueSumReal q b (Y / (g : ℝ))| ≤
          ∑ b ∈ Rset, C * (Y / (g : ℝ)) *
            (Real.log (Y / (g : ℝ))) ^ (-K) := by
      calc
        _ ≤ ∑ b ∈ Rset, |(ArithmeticFunction.moebius g : ℝ) *
              mobiusResidueSumReal q b (Y / (g : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b ∈ Rset, C * (Y / (g : ℝ)) *
              (Real.log (Y / (g : ℝ))) ^ (-K) :=
          Finset.sum_le_sum fun b hb => hterm b hb
    have hMnonneg : 0 ≤ C * (Y / (g : ℝ)) *
        (Real.log (Y / (g : ℝ))) ^ (-K) := by positivity
    have hcardR : (Rset.card : ℝ) ≤ (g : ℝ) := by
      exact_mod_cast (by simpa [Rset, g] using hcard)
    calc
      |∑ b ∈ Rset, (ArithmeticFunction.moebius g : ℝ) *
          mobiusResidueSumReal q b (Y / (g : ℝ))| ≤
          (Rset.card : ℝ) * (C * (Y / (g : ℝ)) *
            (Real.log (Y / (g : ℝ))) ^ (-K)) := by
        simpa [Rset] using hsum
      _ ≤ (g : ℝ) * (C * (Y / (g : ℝ)) *
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

/-- A single constant from `USW(K,B+1)` controls every nonunit Möbius prefix
sum in the exact gcd-reduced range. -/
theorem nonunitMobiusResiduePrefixFamily_of_USW
    (hUSW : UnitGlobalProperty) {K B : ℝ}
    (hK : 0 < K) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q a : ℕ), 0 < q → a < q → ∀ Y : ℝ,
        3 ≤ Y / (Nat.gcd a q : ℝ) →
        (q : ℝ) ≤
          (Real.log (Y / (Nat.gcd a q : ℝ))) ^ (B + 1) →
        |mobiusResidueSumReal q a Y| ≤
          (Nat.gcd a q : ℝ) * C *
            (Y / (Nat.gcd a q : ℝ)) *
              (Real.log (Y / (Nat.gcd a q : ℝ))) ^ (-K) := by
  obtain ⟨C, hC, hprefix⟩ := hUSW K (B + 1) hK (by linarith : 0 < B + 1)
  have hunitPrefix : ∀ (Y : ℝ), 3 ≤ Y → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (Real.log Y) ^ (B + 1) →
      ∀ a : ℤ, IsCoprime a (q : ℤ) →
        |mobiusUnitResidueSumReal q a Y| ≤
          C * Y * (Real.log Y) ^ (-K) := by
    intro Y hY q hq hqY a ha
    exact (hprefix Y hY q hq hqY a ha).1
  refine ⟨C, hC, ?_⟩
  intro q a hq ha Y hYg hqYg
  exact mobiusResiduePrefixBound_of_fixedUnitUSW hC hunitPrefix hq ha hYg hqYg

private theorem long_two_endpoint_scaled_error
    {A R K M : ℝ} {X L : ℕ} {eX eY : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hX : 3 ≤ X)
    (hXL : (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ))
    (hLX : L ≤ X) (hK : K = A + R + 2) (hM : 0 ≤ M)
    (heX : |eX| ≤ M * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K))
    (heY : |eY| ≤ 2 * M * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K)) :
    |eY - eX| ≤ 3 * M * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos (by
    have : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith)
  have hlogXone : 1 ≤ Real.log (X : ℝ) := by
    have hXge3 : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hexp1 : Real.exp 1 < 3 := by
      have h := Real.exp_one_lt_d9
      norm_num at h ⊢
      linarith
    exact (Real.le_log_iff_exp_le hXreal).2 (le_trans hexp1.le hXge3)
  have hcancel : (Real.log (X : ℝ)) ^ (-R) *
      (Real.log (X : ℝ)) ^ R = 1 := by
    rw [← Real.rpow_add hlogXpos]
    have hzero : -R + R = 0 := by ring
    rw [hzero, Real.rpow_zero]
  have hXLmul : (X : ℝ) ≤
      (L : ℝ) * (Real.log (X : ℝ)) ^ R := by
    have hmul := mul_le_mul_of_nonneg_right hXL
      (Real.rpow_nonneg hlogXpos.le R)
    calc
      (X : ℝ) = (X : ℝ) *
          ((Real.log (X : ℝ)) ^ (-R) *
            (Real.log (X : ℝ)) ^ R) := by rw [hcancel, mul_one]
      _ = ((X : ℝ) * (Real.log (X : ℝ)) ^ (-R)) *
          (Real.log (X : ℝ)) ^ R := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ R := hmul
  have hpowerFinal :
      (Real.log (X : ℝ)) ^ (-K) *
          (Real.log (X : ℝ)) ^ R ≤
        (Real.log (X : ℝ)) ^ (-A) := by
    rw [← Real.rpow_add hlogXpos, hK]
    have hexp : -(A + R + 2) + R = -A - 2 := by ring
    rw [hexp]
    exact Real.rpow_le_rpow_of_exponent_le hlogXone (by linarith)
  have hfinalScale : (X : ℝ) *
      (Real.log (X : ℝ)) ^ (-K) ≤
        (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
    calc
      _ ≤ ((L : ℝ) * (Real.log (X : ℝ)) ^ R) *
          (Real.log (X : ℝ)) ^ (-K) :=
        mul_le_mul_of_nonneg_right hXLmul
          (Real.rpow_nonneg hlogXpos.le _)
      _ = (L : ℝ) * ((Real.log (X : ℝ)) ^ (-K) *
          (Real.log (X : ℝ)) ^ R) := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) :=
        mul_le_mul_of_nonneg_left hpowerFinal (by positivity)
  calc
    |eY - eX| ≤ |eY| + |eX| := abs_sub _ _
    _ ≤ 3 * M * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
      calc
        _ ≤ 2 * M * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) +
              M * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := add_le_add heY heX
        _ = 3 * M * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by ring
    _ = 3 * M * ((X : ℝ) * (Real.log (X : ℝ)) ^ (-K)) := by ring
    _ ≤ 3 * M * ((L : ℝ) * (Real.log (X : ℝ)) ^ (-A)) :=
      mul_le_mul_of_nonneg_left hfinalScale (by positivity)
    _ = 3 * M * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by ring

/-- The nonunit Möbius interval estimate with one constant chosen before all
interval, modulus, and residue parameters. The quotient and half-log hypotheses
are exactly those in the source-order interval adapter. -/
theorem nonunitMobiusIntervalBound_family_of_USW
    (hUSW : UnitGlobalProperty) {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X L q a : ℕ), 3 ≤ X →
        (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ) →
        L ≤ X → 0 < q → a < q →
        3 ≤ (X : ℝ) / (Nat.gcd a q : ℝ) →
        3 ≤ ((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ) →
        (q : ℝ) ≤
          (Real.log ((X : ℝ) / (Nat.gcd a q : ℝ))) ^ (B + 1) →
        (q : ℝ) ≤
          (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (B + 1) →
        Real.log (X : ℝ) / 2 ≤
          Real.log ((X : ℝ) / (Nat.gcd a q : ℝ)) →
        Real.log (X : ℝ) / 2 ≤
          Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ)) →
        |mobiusResidueIntervalSumNat q a X L| ≤
          3 * 2 ^ (A + R + 2) * C * (L : ℝ) *
            (Real.log (X : ℝ)) ^ (-A) := by
  let K : ℝ := A + R + 2
  have hK : 0 < K := by dsimp [K]; linarith
  obtain ⟨C, hC, hprefix⟩ :=
    nonunitMobiusResiduePrefixFamily_of_USW hUSW hK hB
  refine ⟨C, hC, ?_⟩
  intro X L q a hX hXL hLX hq ha hXg hXplusLg hqXg hqXplusLg
    hlogXg hlogXplusLg
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
  have hprefixX := hprefix q a hq ha (X : ℝ) hXg hqXg
  have hprefixXplusL := hprefix q a hq ha ((X + L : ℕ) : ℝ)
    hXplusLg hqXplusLg
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
      _ ≤ C * (X : ℝ) * (Real.log (X : ℝ) / 2) ^ (-K) :=
        mul_le_mul_of_nonneg_left hlogXgpow (by positivity)
      _ = 2 ^ K * C * (X : ℝ) *
          (Real.log (X : ℝ)) ^ (-K) := by rw [hscale]; ring
  have hprefixXplusLbound :
      |mobiusResidueSumReal q a ((X + L : ℕ) : ℝ)| ≤
        2 ^ K * C * (2 * (X : ℝ)) *
          (Real.log (X : ℝ)) ^ (-K) := by
    calc
      _ ≤ C * ((X + L : ℕ) : ℝ) *
          (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) :=
        hprefixXplusL'
      _ ≤ C * (2 * (X : ℝ)) *
          (Real.log (((X + L : ℕ) : ℝ) / (Nat.gcd a q : ℝ))) ^ (-K) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hXplusLle (le_of_lt hC)
        · exact Real.rpow_nonneg (Real.log_nonneg (by linarith [hXplusLg])) _
      _ ≤ C * (2 * (X : ℝ)) *
          (Real.log (X : ℝ) / 2) ^ (-K) :=
        mul_le_mul_of_nonneg_left hlogXplusLgpow (by positivity)
      _ = 2 ^ K * C * (2 * (X : ℝ)) *
          (Real.log (X : ℝ)) ^ (-K) := by rw [hscale]; ring
  have hcancel : (Real.log (X : ℝ)) ^ (-R) *
      (Real.log (X : ℝ)) ^ R = 1 := by
    rw [← Real.rpow_add hlogXpos]
    have hzero : -R + R = 0 := by ring
    rw [hzero, Real.rpow_zero]
  have hXLmul : (X : ℝ) ≤
      (L : ℝ) * (Real.log (X : ℝ)) ^ R := by
    have hmul := mul_le_mul_of_nonneg_right hXL
      (Real.rpow_nonneg hlogXpos.le R)
    calc
      (X : ℝ) = (X : ℝ) *
          ((Real.log (X : ℝ)) ^ (-R) *
            (Real.log (X : ℝ)) ^ R) := by rw [hcancel, mul_one]
      _ = ((X : ℝ) * (Real.log (X : ℝ)) ^ (-R)) *
          (Real.log (X : ℝ)) ^ R := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ R := hmul
  have hpowerFinal :
      (Real.log (X : ℝ)) ^ (-K) *
          (Real.log (X : ℝ)) ^ R ≤
        (Real.log (X : ℝ)) ^ (-A) := by
    rw [← Real.rpow_add hlogXpos]
    have hexp : -K + R = -A - 2 := by dsimp [K]; ring
    rw [hexp]
    exact Real.rpow_le_rpow_of_exponent_le hlogXone (by linarith)
  have hfinalScale : (X : ℝ) *
      (Real.log (X : ℝ)) ^ (-K) ≤
        (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
    calc
      _ ≤ ((L : ℝ) * (Real.log (X : ℝ)) ^ R) *
          (Real.log (X : ℝ)) ^ (-K) :=
        mul_le_mul_of_nonneg_right hXLmul
          (Real.rpow_nonneg hlogXpos.le _)
      _ = (L : ℝ) * ((Real.log (X : ℝ)) ^ (-K) *
          (Real.log (X : ℝ)) ^ R) := by ring
      _ ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) :=
        mul_le_mul_of_nonneg_left hpowerFinal (by positivity)
  let M : ℝ := 2 ^ K * C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hXerr : |mobiusResidueSumReal q a (X : ℝ)| ≤
      M * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
    simpa [M, mul_assoc] using hprefixXbound
  have hYerr : |mobiusResidueSumReal q a ((X + L : ℕ) : ℝ)| ≤
      2 * M * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) := by
    calc
      _ ≤ 2 ^ K * C * (2 * (X : ℝ)) *
          (Real.log (X : ℝ)) ^ (-K) := hprefixXplusLbound
      _ = 2 * M * (X : ℝ) *
          (Real.log (X : ℝ)) ^ (-K) := by dsimp [M]; ring
  have hKvalue : K = A + R + 2 := by rfl
  have hinterval := long_two_endpoint_scaled_error hA hR hX hXL hLX
    hKvalue hM hXerr hYerr
  have hdiff : mobiusResidueIntervalSumNat q a X L =
      mobiusResidueSumReal q a ((X + L : ℕ) : ℝ) -
        mobiusResidueSumReal q a (X : ℝ) := by
    rw [mobiusResidueIntervalSumNat,
      sum_Ioc_eq_sum_Icc_sub_of_le (Nat.le_add_right X L)]
    simp only [mobiusResidueSumReal, mobiusResidueSumNat, Nat.floor_natCast]
  rw [hdiff]
  have hinterval' : |mobiusResidueSumReal q a ((X + L : ℕ) : ℝ) -
      mobiusResidueSumReal q a (X : ℝ)| ≤
      3 * M * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := hinterval
  calc
    |mobiusResidueSumReal q a ((X + L : ℕ) : ℝ) -
        mobiusResidueSumReal q a (X : ℝ)| ≤
      3 * M * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := hinterval'
    _ = 3 * 2 ^ (A + R + 2) * C * (L : ℝ) *
          (Real.log (X : ℝ)) ^ (-A) := by dsimp [M, K]; ring

/-- The source-order nonunit Möbius interval estimate above one finite
threshold, with its USW constant chosen before `X,L,q,a`. The exact endpoint
hypotheses are supplied by (L1), not added to this conclusion. -/
theorem longNonunitMobiusIntervalBound_family_large
    (hUSW : UnitGlobalProperty) {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) :
    ∃ t₀ C : ℝ, 2 ≤ t₀ ∧ 0 < C ∧
      ∀ (X L q a : ℕ), 3 ≤ X →
        t₀ ≤ Real.log (X : ℝ) →
        (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ) →
        L ≤ X → 1 ≤ q →
        (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B → a < q →
        |longMobiusResidueIntervalSum q a X L| ≤
          3 * 2 ^ (A + R + 2) * C * (L : ℝ) *
            (Real.log (X : ℝ)) ^ (-A) := by
  obtain ⟨t₀, ht₀, hthreshold⟩ :=
    longNonunitMobiusElementaryThreshold B hB
  obtain ⟨C, hC, hbound⟩ :=
    nonunitMobiusIntervalBound_family_of_USW hUSW hA hB hR
  refine ⟨t₀, C, ht₀, hC, ?_⟩
  intro X L q a hX htX hXL hLX hq hqX ha
  have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  obtain ⟨hBlog, hhalf⟩ := hthreshold _ htX
  obtain ⟨⟨hXg, hqXg, hlogXg⟩,
      ⟨hYg, hqYg, hlogYg⟩⟩ :=
    longNonunitEndpointHypotheses hX hq hqX hB hBlog hhalf
  have hresult := hbound X L q a hX hXL hLX hqpos ha
    hXg hYg hqXg hqYg hlogXg hlogYg
  simpa only [longMobiusResidueIntervalSum,
    mobiusResidueIntervalSumNat] using hresult

/-- The unit-class interval estimates with one constant chosen before the
interval, modulus, and residue parameters. This is the quantifier placement
needed to pass from USW to the finite maxima in LONG. -/
theorem unitIntervalBounds_family_of_USW
    (hUSW : UnitGlobalProperty) {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X L q : ℕ), 3 ≤ X →
        (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ) →
        L ≤ X → 1 ≤ q →
        (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B →
        ∀ a : ℤ, IsCoprime a (q : ℤ) →
          |unitMobiusIntervalSum q a X L| ≤
              3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) ∧
            |unitVonMangoldtIntervalSum q a X L -
                (L : ℝ) / (q.totient : ℝ)| ≤
              3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  let K : ℝ := A + R + 2
  have hK : 0 < K := by dsimp [K]; linarith
  obtain ⟨C, hC, hprefix⟩ := hUSW K B hK hB
  refine ⟨C, hC, ?_⟩
  intro X L q hX hXL hLX hq hqX a ha
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by linarith
  have hYge3 : (3 : ℝ) ≤ ((X + L : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    nlinarith [show (0 : ℝ) ≤ (L : ℝ) by positivity]
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogMono : Real.log (X : ℝ) ≤
      Real.log ((X + L : ℕ) : ℝ) := by
    apply Real.log_le_log hXpos
    rw [Nat.cast_add]
    exact le_add_of_nonneg_right (by positivity)
  have hqY : (q : ℝ) ≤
      (Real.log ((X + L : ℕ) : ℝ)) ^ B := by
    exact hqX.trans (Real.rpow_le_rpow hlogXpos.le hlogMono hB.le)
  letI : NeZero q := ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)⟩
  have hμX : |mobiusUnitResidueSumReal q a (X : ℝ)| ≤
      C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) :=
    (hprefix (X : ℝ) hXreal q hq hqX a ha).1
  have hμY : |mobiusUnitResidueSumReal q a ((X + L : ℕ) : ℝ)| ≤
      C * ((X + L : ℕ) : ℝ) *
        (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) :=
    (hprefix ((X + L : ℕ) : ℝ) hYge3 q hq hqY a ha).1
  have hΛX :
      |vonMangoldtUnitResidueSumReal q a (X : ℝ) -
          (X : ℝ) / (q.totient : ℝ)| ≤
        C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-K) :=
    (hprefix (X : ℝ) hXreal q hq hqX a ha).2
  have hΛY :
      |vonMangoldtUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
          ((X + L : ℕ) : ℝ) / (q.totient : ℝ)| ≤
        C * ((X + L : ℕ) : ℝ) *
          (Real.log ((X + L : ℕ) : ℝ)) ^ (-K) :=
    (hprefix ((X + L : ℕ) : ℝ) hYge3 q hq hqY a ha).2
  have hKvalue : K = A + R + 2 := by rfl
  have hMu := long_two_endpoint_error hA hR hC hX hXL hLX hKvalue hμX hμY
  have hLambda := long_two_endpoint_error hA hR hC hX hXL hLX hKvalue hΛX hΛY
  constructor
  · rw [unitMobiusIntervalSum_eq_prefix_difference]
    exact hMu
  · rw [unitVonMangoldtIntervalSum_eq_prefix_difference]
    have hlin :
        (vonMangoldtUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
            vonMangoldtUnitResidueSumReal q a (X : ℝ)) -
          (L : ℝ) / (q.totient : ℝ) =
        (vonMangoldtUnitResidueSumReal q a ((X + L : ℕ) : ℝ) -
            ((X + L : ℕ) : ℝ) / (q.totient : ℝ)) -
          (vonMangoldtUnitResidueSumReal q a (X : ℝ) -
            (X : ℝ) / (q.totient : ℝ)) := by
      push_cast
      ring
    rw [hlin]
    exact hLambda

/-- The common-constant unit interval bounds in LONG's natural residue
representatives. The same USW witness controls both the Möbius interval sum
and the von Mangoldt interval sum after subtracting its exact `L/φ(q)` main
term. -/
theorem longUnitResidueIntervalBounds_family_of_USW
    (hUSW : UnitGlobalProperty) {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X L q : ℕ), 3 ≤ X →
        (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ) →
        L ≤ X → 1 ≤ q →
        (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B →
        ∀ a < q, Nat.Coprime a q →
          |longMobiusResidueIntervalSum q a X L| ≤
              3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) ∧
            |longVonMangoldtResidueIntervalSum q a X L -
                (L : ℝ) / (q.totient : ℝ)| ≤
              3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  obtain ⟨C, hC, hunit⟩ := unitIntervalBounds_family_of_USW
    hUSW hA hB hR
  refine ⟨C, hC, ?_⟩
  intro X L q hX hXL hLX hq hqX a ha hcop
  have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hcopZ : IsCoprime (a : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    exact hcop
  have hunitBounds := hunit X L q hX hXL hLX hq hqX (a : ℤ) hcopZ
  rw [longMobiusResidueIntervalSum_eq_unit hqpos ha,
    longVonMangoldtResidueIntervalSum_eq_unit hqpos ha]
  exact hunitBounds

/-- The Cramér-model half of the coprime LONG interval estimate, separated
from the USW witness so one constant can be chosen before all classes. -/
theorem longCramerNaturalResidueBound_of_L1
    {A B R : ℝ} {X L q a : ℕ} (hX : 3 ≤ X)
    (hXL : (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ))
    (hq : 1 ≤ q) (hqX : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B)
    (hprimeScale : (Real.log (X : ℝ)) ^ B <
      Real.exp ((Real.log (X : ℝ)) ^ (1 / 10 : ℝ)))
    (hintervalScale : (Real.log (X : ℝ)) ^ (1 / 10 : ℝ) ≤
      Real.log (X : ℝ) / 16)
    (hfirst : sieveD * Real.exp
      (-(Real.log (X : ℝ)) ^ (9 / 10 : ℝ) / 16) ≤
        (Real.log (X : ℝ)) ^ (-A))
    (hsecond : Real.exp 13 * (Real.log (X : ℝ)) ^ (R + 2 / 5 : ℝ) *
      Real.exp (-15 * Real.log (X : ℝ) / 16) ≤
        (Real.log (X : ℝ)) ^ (-A))
    (ha : a < q) (hcop : Nat.Coprime a q) :
    |(∑ n ∈ Finset.Ioc X (X + L),
        if n % q = a then
          paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0) -
      (L : ℝ) / (Nat.totient q : ℝ)| ≤
      2 * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  have hXReal : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hXpos : 0 < (X : ℝ) := by linarith
  have hpowPos : 0 < (Real.log (X : ℝ)) ^ (-R) :=
    Real.rpow_pos_of_pos hlogXpos _
  have hLpos : 0 < (L : ℝ) :=
    lt_of_lt_of_le (mul_pos hXpos hpowPos) hXL
  have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hphi : 1 ≤ (Nat.totient q : ℝ) := by
    have hphiNat : 0 < Nat.totient q := Nat.totient_pos.mpr hqpos
    exact_mod_cast hphiNat
  have hcutoff := longCramerResidueCutoff_of_threshold
    hXReal hq hqX hprimeScale hintervalScale
  have hcopGcd : Int.gcd (a : ℤ) (q : ℤ) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime]
    exact hcop
  have hmodel := cramerResidueMean (X : ℝ) (L : ℝ)
    ((X : ℝ) ^ (1 / 16 : ℝ)) q (a : ℤ)
    hXReal hLpos hqpos hcutoff.1 hcutoff.2
  have hcr := hmodel.2 hcopGcd
  rw [← longCramerNaturalResidueSum_eq_real ha] at hcr
  have hcrError := longCramerMeanError_le_of_L1 hXReal hLpos hXL
    hphi hfirst hsecond
  exact hcr.trans hcrError

/-- The exact coprime `Λ-Cr_X` pointwise estimate from the L1 clauses.
The same common unit constant `C` is retained, and the Cramér contribution
is absorbed with the unchanged `sieveD` and density terms. -/
theorem longCoprimeLambdaCramerIntervalBound_of_L1
    (hUSW : FractionalPrimes.Literature.MobiusToLong.UnitGlobalProperty)
    {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R)
    {X L q a : ℕ} (hX : 3 ≤ X)
    (hXL : (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ))
    (hLX : L ≤ X) (hq : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B)
    (hprimeScale : (Real.log (X : ℝ)) ^ B <
      Real.exp ((Real.log (X : ℝ)) ^ (1 / 10 : ℝ)))
    (hintervalScale : (Real.log (X : ℝ)) ^ (1 / 10 : ℝ) ≤
      Real.log (X : ℝ) / 16)
    (hfirst : sieveD * Real.exp
      (-(Real.log (X : ℝ)) ^ (9 / 10 : ℝ) / 16) ≤
        (Real.log (X : ℝ)) ^ (-A))
    (hsecond : Real.exp 13 * (Real.log (X : ℝ)) ^ (R + 2 / 5 : ℝ) *
      Real.exp (-15 * Real.log (X : ℝ) / 16) ≤
        (Real.log (X : ℝ)) ^ (-A))
    (ha : a < q) (hcop : Nat.Coprime a q) :
    ∃ C : ℝ, 0 < C ∧
      |longLambdaCramerResidueIntervalSum q a X L| ≤
        (3 * C + 2) * (L : ℝ) *
          (Real.log (X : ℝ)) ^ (-A) := by
  obtain ⟨C, hC, hunit⟩ :=
    longUnitResidueIntervalBounds_family_of_USW hUSW hA hB hR
  refine ⟨C, hC, ?_⟩
  have hXReal : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hXpos : 0 < (X : ℝ) := by linarith
  have hpowPos : 0 < (Real.log (X : ℝ)) ^ (-R) :=
    Real.rpow_pos_of_pos hlogXpos _
  have hLpos : 0 < (L : ℝ) :=
    lt_of_lt_of_le (mul_pos hXpos hpowPos) hXL
  have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hphi : 1 ≤ (Nat.totient q : ℝ) := by
    have hphiNat : 0 < Nat.totient q := Nat.totient_pos.mpr hqpos
    exact_mod_cast hphiNat
  have hcutoff := longCramerResidueCutoff_of_threshold
    hXReal hq hqX hprimeScale hintervalScale
  have hcopGcd : Int.gcd (a : ℤ) (q : ℤ) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime]
    exact hcop
  have hmodel := cramerResidueMean (X : ℝ) (L : ℝ)
    ((X : ℝ) ^ (1 / 16 : ℝ)) q (a : ℤ)
    hXReal hLpos hqpos hcutoff.1 hcutoff.2
  have hcr := hmodel.2 hcopGcd
  rw [← longCramerNaturalResidueSum_eq_real ha] at hcr
  have hcrError := longCramerMeanError_le_of_L1 hXReal hLpos hXL
    hphi hfirst hsecond
  have hcrBound :
      |(∑ n ∈ Finset.Ioc X (X + L),
          if n % q = a then
            paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0) -
        (L : ℝ) / (Nat.totient q : ℝ)| ≤
        2 * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) :=
    hcr.trans hcrError
  have hunitBounds := hunit X L q hX hXL hLX hq hqX a ha hcop
  have hlin :
      longVonMangoldtResidueIntervalSum q a X L -
          (∑ n ∈ Finset.Ioc X (X + L),
            if n % q = a then
              paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0) =
        (longVonMangoldtResidueIntervalSum q a X L -
            (L : ℝ) / (Nat.totient q : ℝ)) -
          ((∑ n ∈ Finset.Ioc X (X + L),
              if n % q = a then
                paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0) -
            (L : ℝ) / (Nat.totient q : ℝ)) := by ring
  rw [longLambdaCramerResidueIntervalSum_eq_vonMangoldt_sub_model,
    hlin]
  calc
    |(longVonMangoldtResidueIntervalSum q a X L -
        (L : ℝ) / (Nat.totient q : ℝ)) -
      ((∑ n ∈ Finset.Ioc X (X + L),
          if n % q = a then
            paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0) -
        (L : ℝ) / (Nat.totient q : ℝ))| ≤
      |longVonMangoldtResidueIntervalSum q a X L -
          (L : ℝ) / (q.totient : ℝ)| +
        |(∑ n ∈ Finset.Ioc X (X + L),
            if n % q = a then
              paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0) -
          (L : ℝ) / (Nat.totient q : ℝ)| := abs_sub _ _
    _ ≤ 3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) +
        2 * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) :=
      add_le_add hunitBounds.2 hcrBound
    _ = (3 * C + 2) * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by ring

/-- The coprime `Λ−Cr_X` bound with a single USW witness chosen before every
interval, modulus, and residue class. This is the quantifier order required
by the finite LONG maxima. -/
theorem longCoprimeLambdaCramerIntervalBound_family_large
    (hUSW : UnitGlobalProperty) {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) :
    ∃ t₀ C : ℝ, 2 ≤ t₀ ∧ 0 < C ∧
      ∀ (X L q a : ℕ), 3 ≤ X →
        t₀ ≤ Real.log (X : ℝ) →
        (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ) →
        L ≤ X → 1 ≤ q →
        (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B → a < q →
        Nat.Coprime a q →
        |longLambdaCramerResidueIntervalSum q a X L| ≤
          (3 * C + 2) * (L : ℝ) *
            (Real.log (X : ℝ)) ^ (-A) := by
  have hD : 0 ≤ sieveD := by
    unfold sieveD
    exact (Real.exp_pos 2).le.trans (le_max_right _ _)
  obtain ⟨t₀, ht₀, hthreshold⟩ :=
    longCoprimeCramerL1Threshold A B R sieveD hA hB hR hD
  obtain ⟨C, hC, hunit⟩ :=
    longUnitResidueIntervalBounds_family_of_USW hUSW hA hB hR
  refine ⟨t₀, C, ht₀, hC, ?_⟩
  intro X L q a hX htX hXL hLX hq hqX ha hcop
  obtain ⟨hprime, hinter, hfirst, hsecond⟩ :=
    hthreshold (Real.log (X : ℝ)) htX
  have hcr := longCramerNaturalResidueBound_of_L1
    hX hXL hq hqX hprime hinter hfirst hsecond ha hcop
  have hLambda := (hunit X L q hX hXL hLX hq hqX a ha hcop).2
  let M : ℝ := ∑ n ∈ Finset.Ioc X (X + L),
    if n % q = a then
      paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0
  have hcrM : |M - (L : ℝ) / (Nat.totient q : ℝ)| ≤
      2 * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := hcr
  have hlin : longLambdaCramerResidueIntervalSum q a X L =
      (longVonMangoldtResidueIntervalSum q a X L -
          (L : ℝ) / (Nat.totient q : ℝ)) -
        (M - (L : ℝ) / (Nat.totient q : ℝ)) := by
    rw [longLambdaCramerResidueIntervalSum_eq_vonMangoldt_sub_model]
    dsimp [M]
    ring
  rw [hlin]
  calc
    |(longVonMangoldtResidueIntervalSum q a X L -
        (L : ℝ) / (Nat.totient q : ℝ)) -
      (M - (L : ℝ) / (Nat.totient q : ℝ))| ≤
      |longVonMangoldtResidueIntervalSum q a X L -
        (L : ℝ) / (Nat.totient q : ℝ)| +
        |M - (L : ℝ) / (Nat.totient q : ℝ)| := abs_sub _ _
    _ ≤ 3 * C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) +
        2 * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) :=
      add_le_add hLambda hcrM
    _ = (3 * C + 2) * (L : ℝ) *
        (Real.log (X : ℝ)) ^ (-A) := by ring

/-- A pointwise bound on all modulus/residue pairs bounds the corresponding
finite LONG maximum. The filtered modulus range and natural residue
representatives are exactly those in `LongGlobalProperty`. -/
theorem longMobiusResidueMaximum_le_of_pointwise
    (X L : ℕ) (B M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ q ∈ longModuliRange X B, ∀ a < q,
      |longMobiusResidueIntervalSum q a X L| ≤ M) :
    longMobiusResidueMaximum X L B ≤ M := by
  have hsup : (longModuliRange X B).sup (fun q =>
      (Finset.range q).sup (fun a =>
        (⟨|longMobiusResidueIntervalSum q a X L|,
          abs_nonneg _⟩ : NNReal))) ≤ (⟨M, hM⟩ : NNReal) := by
    apply Finset.sup_le
    intro q hq
    apply Finset.sup_le
    intro a ha
    exact_mod_cast hbound q hq a (Finset.mem_range.mp ha)
  unfold longMobiusResidueMaximum
  exact_mod_cast hsup

/-- The corresponding pointwise-to-maximum adapter for the interval
`Λ-Cr_X` sums. -/
theorem longLambdaCramerResidueMaximum_le_of_pointwise
    (X L : ℕ) (B M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ q ∈ longModuliRange X B, ∀ a < q,
      |longLambdaCramerResidueIntervalSum q a X L| ≤ M) :
    longLambdaCramerResidueMaximum X L B ≤ M := by
  have hsup : (longModuliRange X B).sup (fun q =>
      (Finset.range q).sup (fun a =>
        (⟨|longLambdaCramerResidueIntervalSum q a X L|,
          abs_nonneg _⟩ : NNReal))) ≤ (⟨M, hM⟩ : NNReal) := by
    apply Finset.sup_le
    intro q hq
    apply Finset.sup_le
    intro a ha
    exact_mod_cast hbound q hq a (Finset.mem_range.mp ha)
  unfold longLambdaCramerResidueMaximum
  exact_mod_cast hsup

/-- The elementary Möbius pointwise bound in the bounded-`X` part of
`lal:long-of-unit`. The exact half-open interval contains `L` integers. -/
theorem longMobiusResidueMaximum_le_length (X L : ℕ) (B : ℝ) :
    longMobiusResidueMaximum X L B ≤ (L : ℝ) := by
  have hpoint : ∀ q ∈ longModuliRange X B, ∀ a < q,
      |longMobiusResidueIntervalSum q a X L| ≤ (L : ℝ) := by
    intro q hq a ha
    unfold longMobiusResidueIntervalSum
    calc
      |∑ n ∈ Finset.Ioc X (X + L),
          if n % q = a then (ArithmeticFunction.moebius n : ℝ) else 0| ≤
        ∑ n ∈ Finset.Ioc X (X + L),
          |if n % q = a then (ArithmeticFunction.moebius n : ℝ) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc X (X + L), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hres : n % q = a
        · simp only [if_pos hres]
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
        · simp [hres]
      _ = (L : ℝ) := by
        simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul,
          mul_one]
        rw [Nat.card_Ioc]
        simp
  exact longMobiusResidueMaximum_le_of_pointwise X L B (L : ℝ)
    (by positivity) hpoint

/-- The elementary pointwise input for the bounded-`X` branch of
`lal:long-of-unit`. -/
theorem longLambdaCramerWeight_abs_le_elementary
    {X L n : ℕ} (hX : 3 ≤ X) (hn : n ∈ Finset.Ioc X (X + L)) :
    |vonMangoldtWeight n -
        paperShortBlockCramerWeight (X : ℝ) (n : ℤ)| ≤
      Real.log ((X + L : ℕ) : ℝ) +
        Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) := by
  have hnNat : n ≤ X + L := (Finset.mem_Ioc.mp hn).2
  have hnLower : X < n := (Finset.mem_Ioc.mp hn).1
  have hnPos : (0 : ℝ) < n := by
    have hnPosNat : 0 < n := by omega
    exact_mod_cast hnPosNat
  have hlog : Real.log (n : ℝ) ≤
      Real.log ((X + L : ℕ) : ℝ) :=
    Real.log_le_log hnPos (by exact_mod_cast hnNat)
  have hΛ : |vonMangoldtWeight n| ≤
      Real.log ((X + L : ℕ) : ℝ) := by
    rw [abs_of_nonneg (vonMangoldtWeight_nonneg n)]
    exact (vonMangoldtWeight_le_log (n := n)).trans hlog
  have hCr : |paperShortBlockCramerWeight (X : ℝ) (n : ℤ)| ≤
      Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) := by
    exact (FractionalPrimes.Literature.Uniformity.cramerWeight_abs_le_density
      (X : ℝ) (n : ℤ)).trans
      (by simpa only [paperShortBlockCutoff] using
        paperCramerDensity_at_cutoff_scale (show (3 : ℝ) ≤ X by exact_mod_cast hX))
  exact (abs_sub _ _).trans (add_le_add hΛ hCr)

/-- The bounded-`X` estimate before replacing its logarithms by the
uniform threshold constant from the approved blueprint. -/
theorem longLambdaCramerResidueMaximum_le_elementary
    (X L : ℕ) (B : ℝ) (hX : 3 ≤ X) :
    longLambdaCramerResidueMaximum X L B ≤
      (L : ℝ) * (Real.log ((X + L : ℕ) : ℝ) +
        Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) := by
  let M : ℝ := Real.log ((X + L : ℕ) : ℝ) +
    Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)
  have hM : 0 ≤ M := by
    dsimp [M]
    have hsum : (1 : ℝ) ≤ ((X + L : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ X + L by omega)
    have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    exact add_nonneg (Real.log_nonneg hsum)
      (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (Real.log_nonneg hXone) _))
  have hpoint : ∀ q ∈ longModuliRange X B, ∀ a < q,
      |longLambdaCramerResidueIntervalSum q a X L| ≤
        (L : ℝ) * M := by
    intro q hq a ha
    unfold longLambdaCramerResidueIntervalSum
    calc
      |∑ n ∈ Finset.Ioc X (X + L),
          if n % q = a then
            vonMangoldtWeight n -
              paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0| ≤
        ∑ n ∈ Finset.Ioc X (X + L),
          |if n % q = a then
            vonMangoldtWeight n -
              paperShortBlockCramerWeight (X : ℝ) (n : ℤ) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc X (X + L), M := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hres : n % q = a
        · simpa only [if_pos hres, M] using
            longLambdaCramerWeight_abs_le_elementary hX hn
        · simp [hres, hM]
      _ = (L : ℝ) * M := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Nat.card_Ioc]
        simp
  exact longLambdaCramerResidueMaximum_le_of_pointwise
    X L B ((L : ℝ) * M) (mul_nonneg (by positivity) hM) hpoint

/-- The two elementary monotonicity comparisons in the bounded-`X`
branch of the approved LONG proof. -/
theorem longSmallLogBounds (X L : ℕ) (t₀ : ℝ)
    (hX : 3 ≤ X) (hLX : L ≤ X)
    (htX : Real.log (X : ℝ) ≤ t₀) :
    Real.log ((X + L : ℕ) : ℝ) ≤ Real.log (2 * Real.exp t₀) ∧
      (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) ≤ t₀ ^ (2 / 5 : ℝ) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hlogXnonneg : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXone
  have hXexp : (X : ℝ) ≤ Real.exp t₀ := by
    calc
      (X : ℝ) = Real.exp (Real.log (X : ℝ)) := (Real.exp_log hXpos).symm
      _ ≤ Real.exp t₀ := Real.exp_le_exp.mpr htX
  have hsum : ((X + L : ℕ) : ℝ) ≤ 2 * Real.exp t₀ := by
    have hLreal : (L : ℝ) ≤ X := by exact_mod_cast hLX
    push_cast
    linarith
  have hsumpos : (0 : ℝ) < ((X + L : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < X + L by omega)
  constructor
  · exact Real.log_le_log hsumpos hsum
  · exact Real.rpow_le_rpow hlogXnonneg htX (by norm_num)

/-- Power scaling for the bounded-`X` constant in `lal:long-of-unit`. -/
theorem longSmallPowerScaling {A t₀ : ℝ} {X : ℕ}
    (hA : 0 < A) (hX : 3 ≤ X)
    (htX : Real.log (X : ℝ) ≤ t₀) :
    1 ≤ t₀ ^ A * (Real.log (X : ℝ)) ^ (-A) := by
  have hXone : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hpowpos : 0 < (Real.log (X : ℝ)) ^ A :=
    Real.rpow_pos_of_pos hlogXpos _
  have hpow : (Real.log (X : ℝ)) ^ A ≤ t₀ ^ A :=
    Real.rpow_le_rpow hlogXpos.le htX hA.le
  rw [Real.rpow_neg hlogXpos.le]
  calc
    1 = (Real.log (X : ℝ)) ^ A *
          ((Real.log (X : ℝ)) ^ A)⁻¹ := by
          exact (mul_inv_cancel₀ hpowpos.ne').symm
    _ ≤ t₀ ^ A * ((Real.log (X : ℝ)) ^ A)⁻¹ :=
      mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr hpowpos.le)

/-- The exact bounded-`X` constant displayed in the approved proof
of `lal:long-of-unit`. -/
theorem longGlobalSmallBound {A B t₀ : ℝ} {X L : ℕ}
    (hA : 0 < A) (ht₀ : 2 ≤ t₀) (hX : 3 ≤ X)
    (htX : Real.log (X : ℝ) ≤ t₀) (hLX : L ≤ X) :
    longMobiusResidueMaximum X L B +
        longLambdaCramerResidueMaximum X L B ≤
      (t₀ ^ A * (1 + Real.log (2 * Real.exp t₀) +
        Real.exp 13 * t₀ ^ (2 / 5 : ℝ))) *
          (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  let M₀ : ℝ := 1 + Real.log (2 * Real.exp t₀) +
    Real.exp 13 * t₀ ^ (2 / 5 : ℝ)
  have hE : 1 ≤ 2 * Real.exp t₀ := by
    have he := Real.add_one_le_exp t₀
    linarith
  have hM₀ : 0 ≤ M₀ := by
    dsimp [M₀]
    have hlog : 0 ≤ Real.log (2 * Real.exp t₀) := Real.log_nonneg hE
    have hpow : 0 ≤ t₀ ^ (2 / 5 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  obtain ⟨hlog, hpow⟩ := longSmallLogBounds X L t₀ hX hLX htX
  have hweight : Real.log ((X + L : ℕ) : ℝ) +
      Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) ≤
      Real.log (2 * Real.exp t₀) +
        Real.exp 13 * t₀ ^ (2 / 5 : ℝ) :=
    add_le_add hlog (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _))
  have hpre : longMobiusResidueMaximum X L B +
      longLambdaCramerResidueMaximum X L B ≤ (L : ℝ) * M₀ := by
    calc
      _ ≤ (L : ℝ) + (L : ℝ) *
          (Real.log ((X + L : ℕ) : ℝ) +
            Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) :=
        add_le_add (longMobiusResidueMaximum_le_length X L B)
          (longLambdaCramerResidueMaximum_le_elementary X L B hX)
      _ ≤ (L : ℝ) + (L : ℝ) *
          (Real.log (2 * Real.exp t₀) +
            Real.exp 13 * t₀ ^ (2 / 5 : ℝ)) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hweight (by positivity))
      _ = (L : ℝ) * M₀ := by dsimp [M₀]; ring
  have hscale := longSmallPowerScaling hA hX htX
  have hMscale : M₀ ≤ (t₀ ^ A * M₀) *
      (Real.log (X : ℝ)) ^ (-A) := by
    calc
      M₀ = M₀ * 1 := by ring
      _ ≤ M₀ * (t₀ ^ A * (Real.log (X : ℝ)) ^ (-A)) :=
        mul_le_mul_of_nonneg_left hscale hM₀
      _ = (t₀ ^ A * M₀) * (Real.log (X : ℝ)) ^ (-A) := by ring
  calc
    _ ≤ (L : ℝ) * M₀ := hpre
    _ ≤ (L : ℝ) * ((t₀ ^ A * M₀) *
        (Real.log (X : ℝ)) ^ (-A)) :=
      mul_le_mul_of_nonneg_left hMscale (by positivity)
    _ = (t₀ ^ A * (1 + Real.log (2 * Real.exp t₀) +
        Real.exp 13 * t₀ ^ (2 / 5 : ℝ))) *
          (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
      dsimp [M₀]
      ring

/-- The large-`X` part of `lal:long-of-unit`, including both finite
maxima and the coprime/nonunit case split for `Λ−Cr_X`. One threshold
and one output constant are chosen before `X,L` and all residue classes. -/
theorem longGlobalLarge_of_USW
    (hUSW : UnitGlobalProperty) {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) :
    ∃ t₀ C : ℝ, 2 ≤ t₀ ∧ 0 < C ∧
      ∀ (X L : ℕ), 3 ≤ X →
        t₀ ≤ Real.log (X : ℝ) →
        (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ) →
        L ≤ X →
        longMobiusResidueMaximum X L B +
            longLambdaCramerResidueMaximum X L B ≤
          C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  obtain ⟨tMu, CMu, htMu, hCMu, hMu⟩ :=
    longNonunitMobiusIntervalBound_family_large hUSW hA hB hR
  obtain ⟨tLam, CLam, htLam, hCLam, hLam⟩ :=
    longCoprimeLambdaCramerIntervalBound_family_large hUSW hA hB hR
  have hD : 0 ≤ sieveD := by
    unfold sieveD
    exact (Real.exp_pos 2).le.trans (le_max_right _ _)
  obtain ⟨tL1, htL1, hL1⟩ :=
    longOfUnitL1Threshold A B R sieveD hA hB hR hD
  let t₀ : ℝ := max tMu (max tLam tL1)
  let C : ℝ := 3 * 2 ^ (A + R + 2) * CMu + (3 * CLam + 2)
  have ht₀ : 2 ≤ t₀ := htMu.trans (le_max_left _ _)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨t₀, C, ht₀, hC, ?_⟩
  intro X L hX htX hXL hLX
  have htMuX : tMu ≤ Real.log (X : ℝ) :=
    (le_max_left _ _).trans htX
  have htLamX : tLam ≤ Real.log (X : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans htX)
  have htL1X : tL1 ≤ Real.log (X : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans htX)
  obtain ⟨hprime, hinter, _, _, hmixed, _, _⟩ :=
    hL1 (Real.log (X : ℝ)) htL1X
  let T : ℝ := (L : ℝ) * (Real.log (X : ℝ)) ^ (-A)
  let MMu : ℝ := 3 * 2 ^ (A + R + 2) * CMu * T
  let MLam : ℝ := (3 * CLam + 2) * T
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hMMu : 0 ≤ MMu := by dsimp [MMu]; positivity
  have hMLam : 0 ≤ MLam := by dsimp [MLam]; positivity
  have hMuPoint : ∀ q ∈ longModuliRange X B, ∀ a < q,
      |longMobiusResidueIntervalSum q a X L| ≤ MMu := by
    intro q hqMem a ha
    obtain ⟨hq, hqX⟩ := mem_longModuliRange_iff.mp hqMem
    have h := hMu X L q a hX htMuX hXL hLX hq hqX ha
    simpa [MMu, T, mul_assoc] using h
  have hLamPoint : ∀ q ∈ longModuliRange X B, ∀ a < q,
      |longLambdaCramerResidueIntervalSum q a X L| ≤ MLam := by
    intro q hqMem a ha
    obtain ⟨hq, hqX⟩ := mem_longModuliRange_iff.mp hqMem
    by_cases hcop : Nat.Coprime a q
    · have h := hLam X L q a hX htLamX hXL hLX
        hq hqX ha hcop
      simpa [MLam, T, mul_assoc] using h
    · have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
      have hnon := longNoncoprime_gcd_gt_one hqpos hcop
      have h := longNonunitLambdaCramerIntervalBound_of_L1
        hX hXL hLX hq hqX hprime hinter hmixed ha hnon
      have hcoeff : 1 ≤ 3 * CLam + 2 := by linarith
      calc
        |longLambdaCramerResidueIntervalSum q a X L| ≤ T := by
          simpa [T] using h
        _ ≤ MLam := by
          dsimp [MLam]
          nlinarith [hT]
  have hMuMax := longMobiusResidueMaximum_le_of_pointwise
    X L B MMu hMMu hMuPoint
  have hLamMax := longLambdaCramerResidueMaximum_le_of_pointwise
    X L B MLam hMLam hLamPoint
  calc
    longMobiusResidueMaximum X L B +
        longLambdaCramerResidueMaximum X L B ≤ MMu + MLam :=
      add_le_add hMuMax hLamMax
    _ = C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
      dsimp [MMu, MLam, C, T]
      ring

/-- Lean form of the exact `LONG` contract in `lup:scalar-analytic-tasks`.
The finite suprema range over exactly `1 ≤ q ≤ (log X)^B` and `0 ≤ a < q`. -/
def LongGlobalProperty : Prop :=
  ∀ (A B R : ℝ), 0 < A → 0 < B → 0 < R →
    ∃ C : ℝ, 0 < C ∧
      ∀ (X L : ℕ), 3 ≤ X →
        (X : ℝ) * (Real.log (X : ℝ)) ^ (-R) ≤ (L : ℝ) →
        L ≤ X →
          longMobiusResidueMaximum X L B +
              longLambdaCramerResidueMaximum X L B ≤
            C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A)

/-- Exact `USW → LONG` implication from `lal:long-of-unit`, with the
approved strict Cramér model and both nonunit residue cases. -/
theorem longOfUnitGlobal (hUSW : UnitGlobalProperty) :
    LongGlobalProperty := by
  intro A B R hA hB hR
  obtain ⟨t₀, Clarge, ht₀, hClarge, hlarge⟩ :=
    longGlobalLarge_of_USW hUSW hA hB hR
  let C₀ : ℝ := t₀ ^ A * (1 + Real.log (2 * Real.exp t₀) +
    Real.exp 13 * t₀ ^ (2 / 5 : ℝ))
  let C : ℝ := max C₀ Clarge
  have hC : 0 < C := hClarge.trans_le (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro X L hX hXL hLX
  have hXone : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hT : 0 ≤ (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hlogXpos.le _)
  by_cases hscale : t₀ ≤ Real.log (X : ℝ)
  · have hbound := hlarge X L hX hscale hXL hLX
    calc
      longMobiusResidueMaximum X L B +
          longLambdaCramerResidueMaximum X L B ≤
        Clarge * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := hbound
      _ = Clarge * ((L : ℝ) * (Real.log (X : ℝ)) ^ (-A)) := by ring
      _ ≤ C * ((L : ℝ) * (Real.log (X : ℝ)) ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_right C₀ Clarge) hT
      _ = C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by ring
  · have htX : Real.log (X : ℝ) ≤ t₀ := le_of_lt (lt_of_not_ge hscale)
    have hbound : longMobiusResidueMaximum X L B +
        longLambdaCramerResidueMaximum X L B ≤
          C₀ * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
      simpa only [C₀] using longGlobalSmallBound hA ht₀ hX htX hLX
    calc
      longMobiusResidueMaximum X L B +
          longLambdaCramerResidueMaximum X L B ≤
        C₀ * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := hbound
      _ = C₀ * ((L : ℝ) * (Real.log (X : ℝ)) ^ (-A)) := by ring
      _ ≤ C * ((L : ℝ) * (Real.log (X : ℝ)) ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_left C₀ Clarge) hT
      _ = C * (L : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by ring

end FractionalPrimes.Literature.LongArithmetic

#print axioms FractionalPrimes.Literature.LongArithmetic.longNonunitEndpointHypotheses
#print axioms FractionalPrimes.Literature.LongArithmetic.longNonunitMobiusIntervalBound_family_large
#print axioms FractionalPrimes.Literature.LongArithmetic.longNonunitLambdaCramerIntervalBound_of_L1
#print axioms FractionalPrimes.Literature.LongArithmetic.longCramerNaturalResidueBound_of_L1
#print axioms FractionalPrimes.Literature.LongArithmetic.longCoprimeLambdaCramerIntervalBound_family_large
#print axioms FractionalPrimes.Literature.LongArithmetic.longGlobalLarge_of_USW
#print axioms FractionalPrimes.Literature.LongArithmetic.longGlobalSmallBound
#print axioms FractionalPrimes.Literature.LongArithmetic.longOfUnitGlobal

end
