module

public import FractionalPrimes.Literature.Uniformity.TypeMonotonicity
public import FractionalPrimes.CramerDensityAtScale
public import FractionalPrimes.RosserWeights
public import FractionalPrimes.Literature.Uniformity.StretchedExponentialAbsorption

/-! Exact real short divisor sums and scale prerequisites for
blueprint `lucr:short-divisor` and `lucr:approximation`.
Source: approved blueprint 4627–4711; Astra `cramer-typeI.tex`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

noncomputable section

/-- The real short divisor sum at the real cutoff, with positive divisors. -/
def shortDivisorSum (Y : ℝ) (b : ℕ → ℝ) (n : PositiveInteger) : ℝ :=
  ∑ d ∈ n.1.divisors, if 0 < d ∧ (d : ℝ) ≤ Y then b d else 0

theorem shortDivisorSum_complex (Y : ℝ) (b : ℕ → ℝ) (n : PositiveInteger) :
    (shortDivisorSum Y b n : ℂ) =
      arithmeticShortDivisorSum Y (fun d => (b d.1 : ℂ)) n := by
  simp only [shortDivisorSum, arithmeticShortDivisorSum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : 0 < d <;> by_cases hy : (d : ℝ) ≤ Y <;> simp [hp, hy]

theorem shortDivisorSum_eq_rosserSum (Y : ℝ) (b : ℕ → ℝ)
    (n : PositiveInteger) :
    shortDivisorSum Y b n = ∑ d ∈ rosserPositiveDivisorsBelow Y n.1, b d := by
  have hsets : n.1.divisors.filter (fun d : ℕ => 0 < d ∧ (d : ℝ) ≤ Y) =
      rosserPositiveDivisorsBelow Y n.1 := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, rosserPositiveDivisorsBelow,
      Finset.mem_range, Nat.lt_add_one_iff]
    constructor
    · rintro ⟨⟨hd, hn⟩, hp, hy⟩
      exact ⟨(Nat.le_floor_iff' (Nat.ne_of_gt hp)).2 hy, hp, hd⟩
    · rintro ⟨hy, hp, hd⟩
      exact ⟨⟨hd, Nat.ne_of_gt n.2⟩, hp,
        (Nat.le_floor_iff' (Nat.ne_of_gt hp)).1 hy⟩
  rw [shortDivisorSum, ← hsets, Finset.sum_filter]

/-- Total natural-index adapter to the paper's positive-integer sum. -/
def shortDivisorSumNat (Y : ℝ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  if hn : 0 < n then shortDivisorSum Y b ⟨n, hn⟩ else 0

theorem shortDivisorSumNat_eq_rosserSum (Y : ℝ) (b : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) :
    shortDivisorSumNat Y b n =
      ∑ d ∈ rosserPositiveDivisorsBelow Y n, b d := by
  simp only [shortDivisorSumNat, dif_pos hn]
  exact shortDivisorSum_eq_rosserSum Y b ⟨n, hn⟩

/-- The integer interval used by the short-block sieve has exactly `H`
points and is represented by the same real interval. -/
theorem cramerShortInterval_card (X H : ℕ) :
    (Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).card = H := by
  rw [Int.card_Ioc]
  simp

theorem cramerShortInterval_real_mem (X H : ℕ) (n : ℤ) :
    n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) ↔
      (n : ℝ) ∈ Set.Ioc (X : ℝ) ((X + H : ℕ) : ℝ) := by
  simp only [Finset.mem_Ioc, Set.mem_Ioc]
  exact ⟨fun h => ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩,
    fun h => ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩⟩

theorem cramerShortInterval_convex (X H : ℕ) :
    ∀ x ∈ Set.Ioc (X : ℝ) ((X + H : ℕ) : ℝ),
      ∀ y ∈ Set.Ioc (X : ℝ) ((X + H : ℕ) : ℝ),
        ∀ t : ℝ, x ≤ t → t ≤ y →
          t ∈ Set.Ioc (X : ℝ) ((X + H : ℕ) : ℝ) := by
  intro x hx y hy t hxt hty
  exact ⟨lt_of_lt_of_le hx.1 hxt, le_trans hty hy.2⟩

/-- The paper's natural-number short block and the interval sieve's integer
short block have identical finite sums, with both endpoints preserved. -/
theorem cramerShortInterval_sum_nat_eq_int {M : Type*} [AddCommMonoid M]
    (X H : ℕ) (f : ℤ → M) :
    (∑ n ∈ Finset.Ioc X (X + H), f (n : ℤ)) =
      ∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ), f n := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
  · intro n hn m hm heq
    exact_mod_cast heq
  · intro n hn
    have hn0 : 0 ≤ n := le_trans (by exact_mod_cast (Nat.zero_le X))
      (le_of_lt (Finset.mem_Ioc.mp hn).1)
    refine ⟨n.toNat, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
      exact ⟨by exact_mod_cast (hcast.symm ▸ (Finset.mem_Ioc.mp hn).1),
        by exact_mod_cast (hcast.symm ▸ (Finset.mem_Ioc.mp hn).2)⟩
    · exact Int.toNat_of_nonneg hn0
  · intro n hn
    rfl

/-- Direct specialization of the verified absolute interval sieve to the
integer short block. The density and cutoff are still generic here. -/
theorem cramerRosserUpperIntervalError (X H : ℕ) (w y : ℝ)
    (hH : 1 ≤ H) (hw : 2 ≤ w) (hwy : w ≤ y)
    (hyH : y ≤ (H : ℝ) ^ (1 / 10 : ℝ)) :
    (∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
      |((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        ((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d)|) / (H : ℝ) ≤
      sieveConstant * Real.exp (-Real.log y / Real.log w) := by
  have h := rosserFundamentalInterval
    (S := Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ))
    (J := Set.Ioc (X : ℝ) ((X + H : ℕ) : ℝ))
    (L := H) (w := w) (y := y)
    (cramerShortInterval_real_mem X H)
    (cramerShortInterval_convex X H)
    (cramerShortInterval_card X H) hH hw hwy hyH
  exact h.2.2.2.2.2

/-- The precise large-log threshold used in the approved approximation proof. -/
theorem cramerThreshold_rpow_le (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t)
    (hthreshold : δ ^ (-(10 / 9 : ℝ)) ≤ t) :
    t ^ (1 / 10 : ℝ) ≤ δ * t := by
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hthreshold
    (by norm_num : (0 : ℝ) ≤ 9 / 10)
  have hleft : (δ ^ (-(10 / 9 : ℝ))) ^ (9 / 10 : ℝ) = δ⁻¹ := by
    rw [← Real.rpow_mul hδ.le]
    norm_num [Real.rpow_neg_one]
  rw [hleft] at hpow
  have hone : 1 ≤ δ * t ^ (9 / 10 : ℝ) := by
    calc
      1 = δ * δ⁻¹ := (mul_inv_cancel₀ hδ.ne').symm
      _ ≤ δ * t ^ (9 / 10 : ℝ) := mul_le_mul_of_nonneg_left hpow hδ.le
  calc
    t ^ (1 / 10 : ℝ) ≤ (δ * t ^ (9 / 10 : ℝ)) * t ^ (1 / 10 : ℝ) :=
      by simpa using mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg ht.le _)
    _ = δ * t := by
      rw [mul_assoc, ← Real.rpow_add ht]
      norm_num

/-- The upper sieve level fits the interval length with the exact exponents
`delta ≤ 1/16` and `H ≥ X^(5/8)`. -/
theorem cramerSieveLevel_le_length (X H δ : ℝ) (hX : 1 ≤ X)
    (hδ : δ ≤ 1 / 16) (hH : X ^ (5 / 8 : ℝ) ≤ H) :
    X ^ δ ≤ H ^ (1 / 10 : ℝ) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  calc
    X ^ δ ≤ X ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX hδ
    _ = (X ^ (5 / 8 : ℝ)) ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_mul hX0]
      norm_num
    _ ≤ H ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hH (by norm_num)

theorem cramerCutoff_le_sieveLevel (X δ : ℝ) (hX : 1 < X) (hδ : 0 < δ)
    (hthreshold : δ ^ (-(10 / 9 : ℝ)) ≤ Real.log X) :
    Real.exp ((Real.log X) ^ (1 / 10 : ℝ)) ≤ X ^ δ := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < X)]
  apply Real.exp_le_exp.mpr
  simpa [mul_comm] using
    cramerThreshold_rpow_le δ (Real.log X) hδ (Real.log_pos hX) hthreshold

/-- The sieve exponential becomes exactly the stretched exponential in
the approved proof. -/
theorem cramerSieveExponent_eq (X δ : ℝ) (hX : 1 < X) :
    Real.log (X ^ δ) /
      Real.log (paperShortBlockCutoff X) =
        δ * (Real.log X) ^ (9 / 10 : ℝ) := by
  have hp : 0 < X := by linarith
  have ht : 0 < Real.log X := Real.log_pos hX
  have ht0 : 0 ≤ Real.log X := ht.le
  rw [Real.log_rpow hp, paperShortBlockCutoff, Real.log_exp]
  have hnz : (Real.log X) ^ (1 / 10 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos ht _).ne'
  calc
    δ * Real.log X / (Real.log X) ^ (1 / 10 : ℝ) =
        δ * (Real.log X / (Real.log X) ^ (1 / 10 : ℝ)) := by ring
    _ = δ * (Real.log X) ^ (9 / 10 : ℝ) := by
      congr 1
      apply (div_eq_iff hnz).2
      rw [← Real.rpow_add ht]
      norm_num

theorem cramerCutoff_ge_two (X : ℝ) (hX : 3 ≤ X) :
    2 ≤ paperShortBlockCutoff X := by
  have hlog : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le (by linarith : 0 < X)).2
      (Real.exp_one_lt_three.le.trans hX)
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp 1
    norm_num at hh ⊢
    exact hh
  exact he.trans (Real.exp_le_exp.mpr
    (Real.one_le_rpow hlog (by norm_num)))

/-- All three scale hypotheses needed by Rosser's interval theorem follow
from exactly the assumptions in the approved approximation theorem. -/
theorem cramerRosserScale (X H δ : ℝ) (hX : 3 ≤ X)
    (hδ : 0 < δ) (hδle : δ ≤ 1 / 16)
    (hH : X ^ (5 / 8 : ℝ) ≤ H)
    (ht : max (Real.log 3) (δ ^ (-(10 / 9 : ℝ))) ≤ Real.log X) :
    2 ≤ paperShortBlockCutoff X ∧
      paperShortBlockCutoff X ≤ X ^ δ ∧
      X ^ δ ≤ H ^ (1 / 10 : ℝ) := by
  exact ⟨cramerCutoff_ge_two X hX,
    cramerCutoff_le_sieveLevel X δ (by linarith) hδ
      ((le_max_right _ _).trans ht),
    cramerSieveLevel_le_length X H δ (by linarith) hδle hH⟩

/-- The prescribed coefficients depend only on `X` and `delta`. The bounded
range uses zero coefficients, as required by the approved proof. -/
def cramerShortDivisorCoefficient (X δ : ℝ) (d : ℕ) : ℝ :=
  if max (Real.log 3) (δ ^ (-(10 / 9 : ℝ))) ≤ Real.log X then
    paperCramerDensity (paperShortBlockCutoff X) *
      rosserAllSUpperCoefficient (paperShortBlockCutoff X) (X ^ δ) d
  else 0

theorem cramerShortDivisorCoefficient_support (X δ : ℝ) (hX : 3 ≤ X)
    (hδ : 0 < δ) (d : ℕ) (hd : cramerShortDivisorCoefficient X δ d ≠ 0) :
    0 < d ∧ (d : ℝ) ≤ X ^ δ := by
  unfold cramerShortDivisorCoefficient at hd
  split_ifs at hd with ht
  · have hlog : 1 ≤ Real.log X :=
      (Real.le_log_iff_exp_le (by linarith : 0 < X)).2
        (Real.exp_one_lt_three.le.trans hX)
    have hcut : 2 ≤ paperShortBlockCutoff X := by
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        have hh := Real.add_one_le_exp 1
        norm_num at hh ⊢
        exact hh
      exact he.trans (Real.exp_le_exp.mpr
        (Real.one_le_rpow hlog (by norm_num)))
    have hlevel : paperShortBlockCutoff X ≤ X ^ δ :=
      cramerCutoff_le_sieveLevel X δ (by linarith) hδ
        ((le_max_right _ _).trans ht)
    have hnz : rosserAllSUpperCoefficient (paperShortBlockCutoff X) (X ^ δ) d ≠ 0 :=
      fun hh => hd (by rw [hh, mul_zero])
    have hd0 : d ≠ 0 := by
      intro hh
      subst d
      exact hnz (by simp [rosserAllSUpperCoefficient, rosserXi_zero])
    refine ⟨Nat.pos_of_ne_zero hd0, ?_⟩
    by_contra hbound
    exact hnz ((rosserAllSCoefficient_eq_zero_of_ge hcut hlevel d
      (le_of_lt (lt_of_not_ge hbound))).2)
  · exact (hd rfl).elim

theorem cramerShortDivisorCoefficient_abs_le (X δ : ℝ) (hX : 3 ≤ X) (d : ℕ) :
    |cramerShortDivisorCoefficient X δ d| ≤
      Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ) := by
  have hdensity : 0 ≤ paperCramerDensity (paperShortBlockCutoff X) := by
    unfold paperCramerDensity
    positivity
  have hb := rosserAllSCoefficient_bounds
    (z := paperShortBlockCutoff X) (y := X ^ δ) d
  have habs : |rosserAllSUpperCoefficient (paperShortBlockCutoff X) (X ^ δ) d| ≤ 1 :=
    abs_le.mpr hb.2.2
  unfold cramerShortDivisorCoefficient
  split_ifs
  · rw [abs_mul, abs_of_nonneg hdensity]
    calc
      _ ≤ paperCramerDensity (paperShortBlockCutoff X) * 1 :=
        mul_le_mul_of_nonneg_left habs hdensity
      _ ≤ Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ) := by
        simpa [paperShortBlockCutoff] using paperCramerDensity_at_cutoff_scale hX
  · simp only [abs_zero]
    exact mul_nonneg (Real.exp_pos 13).le (Real.rpow_nonneg (by
      apply Real.log_nonneg
      linarith) _)

/-- The Rosser error with the paper's fixed coefficient family and
location-dependent Cramér model, in the large-log branch. -/
theorem cramerLargeLogIntervalError (X H : ℕ) (δ : ℝ)
    (hX : 3 ≤ X) (hδ : 0 < δ) (hδle : δ ≤ 1 / 16)
    (hH : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ))
    (ht : max (Real.log 3) (δ ^ (-(10 / 9 : ℝ))) ≤ Real.log (X : ℝ)) :
    (∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
      |paperShortBlockCramerWeight X n -
        ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n.natAbs,
          cramerShortDivisorCoefficient X δ d|) / (H : ℝ) ≤
      sieveConstant * Real.exp (-(δ * (Real.log X) ^ (9 / 10 : ℝ))) := by
  have hXreal : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hscale := cramerRosserScale (X : ℝ) (H : ℝ) δ hXreal hδ hδle hH ht
  have hHpos : 1 ≤ H := by
    have hxpow : 1 ≤ (X : ℝ) ^ (5 / 8 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ X by omega)) (by norm_num)
    have hh : (1 : ℝ) ≤ H := hxpow.trans hH
    exact_mod_cast hh
  have hbase := cramerRosserUpperIntervalError X H
    (paperShortBlockCutoff X) ((X : ℝ) ^ δ)
    hHpos hscale.1 hscale.2.1 hscale.2.2
  have hsum (n : ℤ) :
      (∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n.natAbs,
        cramerShortDivisorCoefficient X δ d) =
      paperCramerDensity (paperShortBlockCutoff X) *
        (∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n.natAbs,
          rosserAllSUpperCoefficient (paperShortBlockCutoff X) ((X : ℝ) ^ δ) d) := by
    simp [cramerShortDivisorCoefficient, ht, Finset.mul_sum]
  simp_rw [hsum]
  have hexp : -Real.log ((X : ℝ) ^ δ) /
      Real.log (paperShortBlockCutoff X) =
        -(δ * (Real.log X) ^ (9 / 10 : ℝ)) := by
    rw [neg_div, cramerSieveExponent_eq (X : ℝ) δ
      (by exact_mod_cast (show 1 < X by omega))]
  rw [hexp] at hbase
  have hcast : ((X + H : ℕ) : ℤ) = (X : ℤ) + (H : ℤ) := by omega
  rw [hcast] at hbase
  convert hbase using 1 <;>
    simp only [Nat.cast_add, paperShortBlockCramerWeight, paperCramerWeight,
      paperCramerDensity, paperPrimeProduct, ite_mul, mul_one, mul_zero] <;> rfl

/-- Pointwise bound in the bounded-log branch where the approved proof
chooses all divisor coefficients to be zero. -/
theorem cramerWeight_abs_le_density (X : ℝ) (n : ℤ) :
    |paperShortBlockCramerWeight X n| ≤
      paperCramerDensity (paperShortBlockCutoff X) := by
  have hR : 0 ≤ paperCramerDensity (paperShortBlockCutoff X) := by
    unfold paperCramerDensity
    positivity
  simp only [paperShortBlockCramerWeight, paperCramerWeight]
  split_ifs <;> simp [abs_of_nonneg hR, hR]

theorem cramerZeroFamilyIntervalError (X H : ℕ) :
    ∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
      |paperShortBlockCramerWeight X n| ≤
        (H : ℝ) * paperCramerDensity (paperShortBlockCutoff X) := by
  calc
    _ ≤ ∑ _n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
          paperCramerDensity (paperShortBlockCutoff X) := by
            apply Finset.sum_le_sum
            intro n hn
            exact cramerWeight_abs_le_density X n
    _ = (H : ℝ) * paperCramerDensity (paperShortBlockCutoff X) := by
      simp [cramerShortInterval_card, nsmul_eq_mul]

/-- Exact bounded-log conversion with the exponent in the approved
constant, valid without enlarging the constant. -/
theorem cramerBoundedLogPower (A t T : ℝ) (hA : 0 < A)
    (ht : 0 < t) (hT : t ≤ T) :
    t ^ (2 / 5 : ℝ) ≤ T ^ (A + 2 / 5) * t ^ (-A) := by
  have hTpos : 0 < T := lt_of_lt_of_le ht hT
  have hpow : t ^ (A + 2 / 5) ≤ T ^ (A + 2 / 5) :=
    Real.rpow_le_rpow ht.le hT (by linarith)
  have hneg : 0 ≤ t ^ (-A) := (Real.rpow_pos_of_pos ht _).le
  calc
    t ^ (2 / 5 : ℝ) = t ^ (A + 2 / 5) * t ^ (-A) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    _ ≤ T ^ (A + 2 / 5) * t ^ (-A) :=
      mul_le_mul_of_nonneg_right hpow hneg

/-- The bounded-log branch of the approved Cramér approximation, with
its literal second constant and its prescribed zero coefficients. -/
theorem cramerBoundedLogIntervalError (A δ : ℝ) (X H : ℕ)
    (hA : 0 < A) (hX : 3 ≤ X)
    (hsmall : Real.log (X : ℝ) <
      max (Real.log 3) (δ ^ (-(10 / 9 : ℝ)))) :
    (∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
      |paperShortBlockCramerWeight X n -
        ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n.natAbs,
          cramerShortDivisorCoefficient X δ d|) ≤
      Real.exp 13 *
        (max (Real.log 3) (δ ^ (-(10 / 9 : ℝ)))) ^ (A + 2 / 5) *
          (H : ℝ) * (Real.log X) ^ (-A) := by
  let t : ℝ := Real.log X
  let T : ℝ := max (Real.log 3) (δ ^ (-(10 / 9 : ℝ)))
  have ht : 0 < t := by
    dsimp [t]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hcoeff (d : ℕ) : cramerShortDivisorCoefficient X δ d = 0 := by
    simp [cramerShortDivisorCoefficient, T, t, not_le.mpr hsmall]
  have hR := paperCramerDensity_at_cutoff_scale
    (X := (X : ℝ)) (by exact_mod_cast hX)
  have hpow := cramerBoundedLogPower A t T hA ht hsmall.le
  calc
    _ = ∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
          |paperShortBlockCramerWeight X n| := by simp [hcoeff]
    _ ≤ (H : ℝ) * paperCramerDensity (paperShortBlockCutoff X) :=
      cramerZeroFamilyIntervalError X H
    _ ≤ (H : ℝ) * (Real.exp 13 * t ^ (2 / 5 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [paperShortBlockCutoff, t] using hR
      · positivity
    _ ≤ Real.exp 13 * T ^ (A + 2 / 5) * (H : ℝ) * t ^ (-A) := by
      have hh : (H : ℝ) * Real.exp 13 * t ^ (2 / 5 : ℝ) ≤
          (H : ℝ) * Real.exp 13 * (T ^ (A + 2 / 5) * t ^ (-A)) := by
        apply mul_le_mul_of_nonneg_left hpow
        positivity
      convert hh using 1 <;> ring

/-- The large-log interval estimate after exact stretched-exponential
absorption, still retaining the fixed `X,delta` coefficients. -/
theorem cramerLargeLogAbsorbedIntervalError (A δ : ℝ) (X H : ℕ)
    (hA : 0 < A) (hX : 3 ≤ X) (hδ : 0 < δ) (hδle : δ ≤ 1 / 16)
    (hH : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ))
    (hlarge : max (Real.log 3) (δ ^ (-(10 / 9 : ℝ))) ≤ Real.log (X : ℝ)) :
    (∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
      |paperShortBlockCramerWeight X n -
        ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n.natAbs,
          cramerShortDivisorCoefficient X δ d|) ≤
      sieveConstant *
        (10 * A / (9 * Real.exp 1 * δ)) ^ (10 * A / 9) *
          (H : ℝ) * (Real.log X) ^ (-A) := by
  have ht : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hHpos : 0 < (H : ℝ) := by
    have hxpow : 0 < (X : ℝ) ^ (5 / 8 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < X by omega)) _
    exact lt_of_lt_of_le hxpow hH
  have hC : 0 ≤ sieveConstant := by
    unfold sieveConstant sieveD
    have hh := le_max_right sieveD₀ (Real.exp 2)
    have he := Real.exp_pos 2
    positivity
  have hbase := cramerLargeLogIntervalError X H δ hX hδ hδle hH hlarge
  have hsum := (div_le_iff₀ hHpos).mp hbase
  have habs := stretchedExponentialAbsorption A δ (Real.log X) hA hδ ht
  calc
    _ ≤ (sieveConstant * Real.exp (-(δ * (Real.log X) ^ (9 / 10 : ℝ)))) * H := hsum
    _ ≤ (sieveConstant *
        ((10 * A / (9 * Real.exp 1 * δ)) ^ (10 * A / 9) *
          (Real.log X) ^ (-A))) * H := by
      gcongr
      exact habs
    _ = sieveConstant *
        (10 * A / (9 * Real.exp 1 * δ)) ^ (10 * A / 9) *
          (H : ℝ) * (Real.log X) ^ (-A) := by ring

/-- The literal constant displayed in the approved blueprint. -/
def cramerApproximationConstant (A δ : ℝ) : ℝ :=
  max
    (sieveConstant *
      (10 * A / (9 * Real.exp 1 * δ)) ^ (10 * A / 9))
    (Real.exp 13 *
      (max (Real.log 3) (δ ^ (-(10 / 9 : ℝ)))) ^ (A + 2 / 5))

/-- The two interval branches assembled with the approved explicit
constant. This is the integer-index form; the positive-integer `T_b`
presentation is the remaining bridge to the full blueprint theorem. -/
theorem cramerApproximationIntervalBound (A δ : ℝ) (X H : ℕ)
    (hA : 0 < A) (hX : 3 ≤ X) (hδ : 0 < δ)
    (hδle : δ ≤ 1 / 16)
    (hH : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ)) :
    (∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
      |paperShortBlockCramerWeight X n -
        ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n.natAbs,
          cramerShortDivisorCoefficient X δ d|) ≤
      cramerApproximationConstant A δ * (H : ℝ) *
        (Real.log X) ^ (-A) := by
  have ht : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hHnonneg : 0 ≤ (H : ℝ) := by positivity
  by_cases hlarge :
      max (Real.log 3) (δ ^ (-(10 / 9 : ℝ))) ≤ Real.log (X : ℝ)
  · have hbound := cramerLargeLogAbsorbedIntervalError A δ X H
      hA hX hδ hδle hH hlarge
    calc
      _ ≤ sieveConstant *
          (10 * A / (9 * Real.exp 1 * δ)) ^ (10 * A / 9) *
            (H : ℝ) * (Real.log X) ^ (-A) := hbound
      _ ≤ cramerApproximationConstant A δ * (H : ℝ) *
          (Real.log X) ^ (-A) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hHnonneg
        · exact (Real.rpow_pos_of_pos ht _).le
  · have hsmall : Real.log (X : ℝ) <
        max (Real.log 3) (δ ^ (-(10 / 9 : ℝ))) := lt_of_not_ge hlarge
    have hbound := cramerBoundedLogIntervalError A δ X H hA hX hsmall
    calc
      _ ≤ Real.exp 13 *
          (max (Real.log 3) (δ ^ (-(10 / 9 : ℝ)))) ^ (A + 2 / 5) *
            (H : ℝ) * (Real.log X) ^ (-A) := hbound
      _ ≤ cramerApproximationConstant A δ * (H : ℝ) *
          (Real.log X) ^ (-A) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hHnonneg
        · exact (Real.rpow_pos_of_pos ht _).le

/-- Blueprint `lucr:approximation`: exact fixed coefficients, support,
size, and short-interval error on positive natural indices. -/
theorem cramerShortDivisorApproximation (A δ : ℝ) (X H : ℕ)
    (hA : 0 < A) (hX : 3 ≤ X) (hδ : 0 < δ)
    (hδle : δ ≤ 1 / 16)
    (hH : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ)) :
    ∃ b : ℕ → ℝ,
      (∀ d, b d ≠ 0 → 0 < d ∧ (d : ℝ) ≤ (X : ℝ) ^ δ) ∧
      (∀ d, |b d| ≤ Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ)) ∧
      (∑ n ∈ Finset.Ioc X (X + H),
        |paperShortBlockCramerWeight X (n : ℤ) -
          shortDivisorSumNat ((X : ℝ) ^ δ) b n|) ≤
        cramerApproximationConstant A δ * (H : ℝ) *
          (Real.log X) ^ (-A) := by
  refine ⟨cramerShortDivisorCoefficient X δ, ?_, ?_, ?_⟩
  · intro d hd
    exact cramerShortDivisorCoefficient_support X δ (by exact_mod_cast hX) hδ d hd
  · intro d
    exact cramerShortDivisorCoefficient_abs_le X δ (by exact_mod_cast hX) d
  · have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc X (X + H)) :
        shortDivisorSumNat ((X : ℝ) ^ δ)
          (cramerShortDivisorCoefficient X δ) n =
        ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n,
          cramerShortDivisorCoefficient X δ d := by
      exact shortDivisorSumNat_eq_rosserSum _ _ n
        (lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hn).1)
    calc
      _ = ∑ n ∈ Finset.Ioc X (X + H),
          |paperShortBlockCramerWeight X (n : ℤ) -
            ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n,
              cramerShortDivisorCoefficient X δ d| := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [hpoint n hn]
      _ = ∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
          |paperShortBlockCramerWeight X n -
            ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n.natAbs,
              cramerShortDivisorCoefficient X δ d| := by
              simpa only [Int.natAbs_natCast] using
                cramerShortInterval_sum_nat_eq_int X H (fun n : ℤ =>
                  |paperShortBlockCramerWeight X n -
                    ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ δ) n.natAbs,
                      cramerShortDivisorCoefficient X δ d|)
      _ ≤ cramerApproximationConstant A δ * (H : ℝ) *
          (Real.log X) ^ (-A) :=
            cramerApproximationIntervalBound A δ X H hA hX hδ hδle hH

end
end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.shortDivisorSum_complex
#print axioms FractionalPrimes.Literature.Uniformity.cramerThreshold_rpow_le
#print axioms FractionalPrimes.Literature.Uniformity.cramerSieveLevel_le_length
#print axioms FractionalPrimes.Literature.Uniformity.cramerCutoff_le_sieveLevel
#print axioms FractionalPrimes.Literature.Uniformity.shortDivisorSum_eq_rosserSum
#print axioms FractionalPrimes.Literature.Uniformity.cramerShortDivisorCoefficient_support
#print axioms FractionalPrimes.Literature.Uniformity.cramerShortDivisorCoefficient_abs_le
#print axioms FractionalPrimes.Literature.Uniformity.cramerShortInterval_card
#print axioms FractionalPrimes.Literature.Uniformity.cramerRosserUpperIntervalError
#print axioms FractionalPrimes.Literature.Uniformity.cramerSieveExponent_eq
#print axioms FractionalPrimes.Literature.Uniformity.cramerRosserScale
#print axioms FractionalPrimes.Literature.Uniformity.cramerLargeLogIntervalError
#print axioms FractionalPrimes.Literature.Uniformity.cramerZeroFamilyIntervalError
#print axioms FractionalPrimes.Literature.Uniformity.cramerBoundedLogPower
#print axioms FractionalPrimes.Literature.Uniformity.cramerBoundedLogIntervalError
#print axioms FractionalPrimes.Literature.Uniformity.cramerLargeLogAbsorbedIntervalError
#print axioms FractionalPrimes.Literature.Uniformity.cramerApproximationIntervalBound
#print axioms FractionalPrimes.Literature.Uniformity.cramerShortInterval_sum_nat_eq_int
#print axioms FractionalPrimes.Literature.Uniformity.cramerShortDivisorApproximation
