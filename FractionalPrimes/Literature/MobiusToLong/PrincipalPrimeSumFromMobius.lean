module
public import FractionalPrimes.Literature.Reciprocal.GlobalCharacterMobius
public import FractionalPrimes.Literature.LongArithmetic.ShiftedCharacterMobiusSeries
public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter
public import FractionalPrimes.Literature.MobiusToLong.ReciprocalMobiusMoments
public import FractionalPrimes.Literature.MobiusToLong.MobiusReciprocalMomentValue
public import FractionalPrimes.Literature.MobiusToLong.MobiusLogMomentValue
public import FractionalPrimes.Literature.MobiusToLong.PrincipalPrimeHyperbolaSplit
public import FractionalPrimes.Literature.MobiusToLong.PrincipalPrimeSmallRange
public import FractionalPrimes.Literature.MobiusToLong.MobiusLargeHalf
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import FractionalPrimes.ArithmeticBasicsAnalytic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
@[expose] public section

noncomputable section

open Filter
open scoped Topology
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Twisted

namespace FractionalPrimes.Literature.MobiusToLong

/-- The modulus-one global character Möbius sum is exactly the scalar
Möbius summatory function. This is the adapter needed to feed the conditional
global character estimate into the two ordered Möbius-moment theorems. -/
theorem globalMobiusCharacterSum_modulus_one_eq_mobiusSummatory
    (χ : DirichletCharacter ℂ 1) (x : ℝ) :
    globalMobiusCharacterSum χ x = (mobiusSummatory x : ℂ) := by
  have hχ : χ = principalCharacter 1 := modulus_one_character_eq_principal χ
  have hχnat {n : ℕ} (hn : n ≠ 0) : dirichletCharacterNatHom χ n = 1 := by
    rw [dirichletCharacterNatHom_apply_of_ne_zero χ hn, hχ, principalCharacter]
    have hncast : (n : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hncast]
    exact MulChar.one_apply isUnit_one
  rw [globalMobiusCharacterSum, mobiusSummatory, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have hn' := Finset.mem_Icc.mp hn
    omega
  rw [globalMobiusCharacterCoefficient_eq χ hn0, hχnat hn0]
  simp

/-- The scalar Mertens premise required by `lml:mobius-moments`, obtained
from the checked global character estimate at exponent parameter `B = 1` and
the modulus-one character. The same witness `C` is retained. -/
theorem scalarMobiusMertensBound_of_MUF
    (hMUF : MobiusUniformity) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R) := by
  obtain ⟨C, hC, hglobal⟩ :=
    globalCharacterMobius hMUF hR (by norm_num : 0 < (1 : ℝ))
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith
  have hexp1 : Real.exp 1 < 3 := by
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hlog : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hxpos).2
    exact hexp1.le.trans hx
  have hlogB : ((1 : ℕ) : ℝ) ≤ (Real.log x) ^ (1 : ℝ) := by
    simpa using hlog
  have hchar := hglobal (χ := (1 : DirichletCharacter ℂ 1)) (x := x)
    hx (by norm_num) hlogB
  rw [globalMobiusCharacterSum_modulus_one_eq_mobiusSummatory
    (1 : DirichletCharacter ℂ 1) x] at hchar
  simpa [Complex.norm_real, Real.norm_eq_abs] using hchar

/-- Pass the checked finite unweighted tail bound to the exact ordered limit
zero, retaining the real `Nat.floor` cutoff. -/
theorem principalPrime_unweighted_infinite_tail_bound {R C D : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C) (hD : 3 ≤ D)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    |∑ n ∈ Finset.Icc 1 (Nat.floor D),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤
      C * (2 * Real.rpow (Real.log D) (-R) +
        Real.rpow (Real.log D) (1 - R) / (R - 1)) := by
  let A : ℝ → ℝ := fun Y =>
    ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
      (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)
  have hA : Tendsto A atTop (𝓝 0) := by
    have hseq := reciprocalMobiusPartialSum_tendsto_zero hR hC hM
    have hreal := hseq.comp (tendsto_nat_floor_atTop (α := ℝ))
    change Tendsto (fun Y : ℝ => reciprocalMobiusPartialSum (Nat.floor Y))
      atTop (𝓝 0) at hreal
    simpa [A, reciprocalMobiusPartialSum] using hreal
  have htail_eventually : ∀ᶠ Y : ℝ in atTop,
      |A Y - A D| ≤ C * (2 * Real.rpow (Real.log D) (-R) +
        Real.rpow (Real.log D) (1 - R) / (R - 1)) := by
    filter_upwards [eventually_ge_atTop D] with Y hDY
    have htail := mobius_reciprocal_finite_uniform_tail_bound hR hC hD hDY hM
    have hsplit :
        (∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) = A Y - A D := by
      simpa [A] using
        (sum_Ioc_eq_sum_Icc_sub_of_le (Nat.floor_mono hDY)
          (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)))
    rw [hsplit] at htail
    exact htail
  have hAbs : Tendsto (fun Y : ℝ => |A Y - A D|) atTop (𝓝 |A D|) := by
    have hsub := hA.sub_const (A D)
    simpa using hsub.abs
  simpa [A] using le_of_tendsto hAbs htail_eventually

/-- Pass the checked finite logarithmically weighted tail bound to the exact
ordered limit `-1`, preserving the real `Nat.floor` cutoff. -/
theorem principalPrime_weighted_infinite_tail_bound {R C D : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C) (hD : 3 ≤ D)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    |(∑ n ∈ Finset.Icc 1 (Nat.floor D),
        (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) + 1| ≤
      3 * C * Real.rpow (Real.log D) (2 - R) := by
  let A : ℝ → ℝ := fun Y =>
    ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
      (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)
  have hA : Tendsto A atTop (𝓝 (-1)) := by
    have hseq := mobiusLogReciprocalPartialSum_tendsto_neg_one hR hC hM
    have hreal := hseq.comp (tendsto_nat_floor_atTop (α := ℝ))
    change Tendsto (fun Y : ℝ => mobiusLogReciprocalPartialSum (Nat.floor Y))
      atTop (𝓝 (-1)) at hreal
    simpa [A, mobiusLogReciprocalPartialSum] using hreal
  have htail_eventually : ∀ᶠ Y : ℝ in atTop,
      |A Y - A D| ≤ 3 * C * Real.rpow (Real.log D) (2 - R) := by
    filter_upwards [eventually_ge_atTop D] with Y hDY
    have htail := mobius_log_reciprocal_finite_uniform_tail_bound
      hR hC hD hDY hM
    have hsplit :
        (∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) =
            A Y - A D := by
      simpa [A] using
        (sum_Ioc_eq_sum_Icc_sub_of_le (Nat.floor_mono hDY)
          (fun n : ℕ =>
            (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)))
    rw [hsplit] at htail
    exact htail
  have hAbs : Tendsto (fun Y : ℝ => |A Y - A D|) atTop
      (𝓝 |(-1 : ℝ) - A D|) := by
    have hsub := hA.sub_const (A D)
    simpa using hsub.abs
  have hlim := le_of_tendsto hAbs htail_eventually
  have habs : |(-1 : ℝ) - A D| = |A D + 1| := by
    calc
      |(-1 : ℝ) - A D| = |-(A D + 1)| := by congr 1 <;> ring
      _ = |A D + 1| := abs_neg _
  calc
    |(∑ n ∈ Finset.Icc 1 (Nat.floor D),
        (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) + 1|
        = |A D + 1| := by simp [A]
    _ = |(-1 : ℝ) - A D| := habs.symm
    _ ≤ 3 * C * Real.rpow (Real.log D) (2 - R) := hlim

/-- At modulus one, the complex expression controlled by the large-half
lemma is the real complementary hyperbola sum from the finite split. -/
theorem principalPrime_largeHalf_sum_eq_ofReal {x : ℝ} (hx : 9 ≤ x) :
    (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
      dirichletCharacterNatHom (1 : DirichletCharacter ℂ 1) m *
        (Real.log (m : ℝ) : ℂ) *
        (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
            (Nat.floor (x / (m : ℝ))),
          globalMobiusCharacterCoefficient (1 : DirichletCharacter ℂ 1) d)) =
      ((∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (Real.sqrt x)),
        Real.log (m : ℝ) *
          (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
              (Nat.floor (x / (m : ℝ))),
            mobiusRealCoefficient d) : ℝ) : ℂ) := by
  have hxpos : 0 < x := by linarith
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsqrt3 : 3 ≤ Real.sqrt x := by
    have hsqrt9 : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc
      (3 : ℝ) = Real.sqrt 9 := hsqrt9.symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hfloor_sqrt : 3 ≤ Nat.floor (Real.sqrt x) :=
    Nat.le_floor (by exact_mod_cast hsqrt3)
  have hcut : x / Real.sqrt x = Real.sqrt x := by
    calc
      x / Real.sqrt x = (Real.sqrt x) ^ 2 / Real.sqrt x := by
        rw [Real.sq_sqrt hxpos.le]
      _ = Real.sqrt x := by field_simp [ne_of_gt hsqrtpos]
  have hfloor_cut : Nat.floor (x / Real.sqrt x) = Nat.floor (Real.sqrt x) :=
    congrArg Nat.floor hcut
  have hχeq : (1 : DirichletCharacter ℂ 1) = principalCharacter 1 :=
    modulus_one_character_eq_principal _
  have hchar {n : ℕ} (hn : n ≠ 0) :
      dirichletCharacterNatHom (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [dirichletCharacterNatHom_apply_of_ne_zero _ hn, hχeq, principalCharacter]
    have hncast : (n : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hncast]
    exact MulChar.one_apply isUnit_one
  rw [hfloor_cut]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := by
    have hm' := Finset.mem_Icc.mp hm
    omega
  have hinner :
      (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
          (Nat.floor (x / (m : ℝ))),
        globalMobiusCharacterCoefficient (1 : DirichletCharacter ℂ 1) d) =
        ((∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
            (Nat.floor (x / (m : ℝ))),
          mobiusRealCoefficient d : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < d := by
      have hd' := Finset.mem_Ioc.mp hd
      omega
    rw [globalMobiusCharacterCoefficient_eq _ (Nat.ne_of_gt hdpos), hchar (Nat.ne_of_gt hdpos)]
    simp [mobiusRealCoefficient]
  rw [hchar (Nat.ne_of_gt hmpos), hinner]
  simp [Complex.ofReal_mul]

/-- A large threshold where the logarithmic error from the small half is
absorbed by the square-root scale, with the source's exact factor four. -/
theorem exists_principalPrime_large_threshold (K : ℝ) :
    ∃ x₁ : ℝ, 9 ≤ x₁ ∧ 4 ≤ Real.log x₁ ∧
      ∀ x : ℝ, x₁ ≤ x →
        4 * Real.rpow (Real.log x) (K + 1) ≤ Real.sqrt x := by
  have hlittle :
      (fun x : ℝ => Real.log x ^ (K + 1)) =o[atTop]
        fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop (K + 1) (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound := (Asymptotics.isLittleO_iff.mp hlittle)
    (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hbound
  let x₁ := max (max x₀ 9) (Real.exp 4)
  refine ⟨x₁, ?_, ?_, ?_⟩
  · exact le_trans (le_max_right x₀ 9) (le_max_left (max x₀ 9) (Real.exp 4))
  · have hexp4 : Real.exp 4 ≤ x₁ := le_max_right _ _
    have hx₁pos : 0 < x₁ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 9)
      (le_trans (le_max_right x₀ 9) (le_max_left (max x₀ 9) (Real.exp 4)))
    exact (Real.le_log_iff_exp_le hx₁pos).2 hexp4
  · intro x hx
    have hx₀x : x₀ ≤ x := le_trans (le_trans (le_max_left x₀ 9)
      (le_max_left (max x₀ 9) (Real.exp 4))) hx
    have hx9 : 9 ≤ x := le_trans
      (le_trans (le_max_right x₀ 9) (le_max_left (max x₀ 9) (Real.exp 4))) hx
    have hnorm := hx₀ x hx₀x
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hlogpow : 0 ≤ Real.log x ^ (K + 1) := Real.rpow_nonneg hlog _
    have hxpow : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg hlogpow, Real.norm_of_nonneg hxpow] at hnorm
    calc
      4 * Real.rpow (Real.log x) (K + 1) ≤ x ^ (1 / 2 : ℝ) := by
        change 4 * Real.log x ^ (K + 1) ≤ x ^ (1 / 2 : ℝ)
        nlinarith [hnorm]
      _ = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

/-- The finite real-cutoff von Mangoldt sum is bounded by `x log x`. -/
theorem vonMangoldt_Icc_floor_le {x : ℝ} (hx : 3 ≤ x) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) ≤
      x * Real.log x := by
  have hxone : 1 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hfloor : (Nat.floor x : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hsum :
      (∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) ≤
        ∑ n ∈ Finset.Icc 1 (Nat.floor x), Real.log x := by
    apply Finset.sum_le_sum
    intro n hn
    have hnI := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hnI.1)
    have hnle : (n : ℝ) ≤ x := by
      have hnleNat : n ≤ Nat.floor x := hnI.2
      have hnleCast : (n : ℝ) ≤ (Nat.floor x : ℝ) := by exact_mod_cast hnleNat
      exact hnleCast.trans hfloor
    exact (vonMangoldtWeight_le_log (n := n)).trans (Real.log_le_log hnpos hnle)
  calc
    (∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) ≤
        ∑ n ∈ Finset.Icc 1 (Nat.floor x), Real.log x := hsum
    _ = (Nat.floor x : ℝ) * Real.log x := by
      simp [Finset.sum_const, Nat.card_Icc]
    _ ≤ x * Real.log x := mul_le_mul_of_nonneg_right hfloor hlog

/-- The bounded-range absolute error estimate at a real cutoff. -/
theorem vonMangoldt_Icc_floor_abs_sub_x_le {x : ℝ} (hx : 3 ≤ x) :
    |(∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) - x| ≤
      x * (1 + Real.log x) := by
  have hxone : 1 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hsum_nonneg :
      0 ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n := by
    apply Finset.sum_nonneg
    intro n hn
    exact vonMangoldtWeight_nonneg n
  have hsum_le := vonMangoldt_Icc_floor_le hx
  rw [abs_le]
  constructor <;> nlinarith [hsum_nonneg, hsum_le]

/-- Convert the complex logarithmic weighted sum at natural indices into the
real sum. This is the realification step needed for the modulus-one
large-half estimate. -/
theorem norm_sum_complexLog_nat_eq_abs_realLog_sum
    (s : Finset ℕ) (t : ℕ → Finset ℕ) (f : ℕ → ℝ) :
    ‖∑ n ∈ s, Complex.log (n : ℂ) * ∑ d ∈ t n, (f d : ℂ)‖ =
      |∑ n ∈ s, Real.log (n : ℝ) * ∑ d ∈ t n, f d| := by
  have hsum :
      (∑ n ∈ s, Complex.log (n : ℂ) * ∑ d ∈ t n, (f d : ℂ)) =
        ((∑ n ∈ s, Real.log (n : ℝ) * ∑ d ∈ t n, f d : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Complex.natCast_log]
    simp only [Complex.ofReal_mul, Complex.ofReal_sum]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs]

set_option maxHeartbeats 500000 in
/-- The principal-prime main term follows from MUF, the exact ordered Möbius
moments, the logarithmic small-half estimate, and the uniform large-half
bound. -/
theorem principalPrimeSumFromMobius (hMUF : MobiusUniformity)
    {K : ℝ} (hK : 0 < K) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ x : ℝ, 3 ≤ x →
      |(∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) - x| ≤
        C₀ * x * Real.rpow (Real.log x) (-K) := by
  let R : ℝ := K + 4
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hR3 : 3 < R := by dsimp [R]; linarith
  obtain ⟨Cₛ, hCₛ, hMₛ⟩ := scalarMobiusMertensBound_of_MUF hMUF hRpos
  obtain ⟨Cₗ, hCₗ, hLarge⟩ := largeMobiusHyperbolaHalf hMUF hRpos
    (by norm_num : 0 < (1 : ℝ))
  let C₂ : ℝ := max Cₛ Cₗ
  have hC₂ : 1 ≤ C₂ := by dsimp [C₂]; exact le_max_of_le_left hCₛ
  have hCₛC₂ : Cₛ ≤ C₂ := le_max_left _ _
  have hCₗC₂ : Cₗ ≤ C₂ := le_max_right _ _
  have hM₂ : ∀ y : ℝ, 3 ≤ y →
      |mobiusSummatory y| ≤ C₂ * y * Real.rpow (Real.log y) (-R) := by
    intro y hy
    have hypos : 0 < y := by linarith
    have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hpow : 0 ≤ Real.rpow (Real.log y) (-R) := Real.rpow_nonneg hlog _
    have hcoef : Cₛ * y ≤ C₂ * y := mul_le_mul_of_nonneg_right hCₛC₂ hypos.le
    calc
      |mobiusSummatory y| ≤ Cₛ * y * Real.rpow (Real.log y) (-R) := hMₛ y hy
      _ ≤ C₂ * y * Real.rpow (Real.log y) (-R) :=
        mul_le_mul_of_nonneg_right hcoef hpow
  obtain ⟨x₁, hx₁9, hx₁log, hAbsorb⟩ := exists_principalPrime_large_threshold K
  let Cbig : ℝ := (2 : ℝ) ^ (R + 3) * C₂ + 1
  let Csmall : ℝ := (1 + Real.log x₁) * Real.rpow (Real.log x₁) K
  let C₀ : ℝ := max Cbig Csmall
  have hC₀pos : 0 < C₀ := by
    apply lt_of_lt_of_le _ (le_max_left Cbig Csmall)
    dsimp [Cbig]
    positivity
  have hCbig : Cbig ≤ C₀ := le_max_left _ _
  have hCsmall : Csmall ≤ C₀ := le_max_right _ _
  refine ⟨C₀, hC₀pos, ?_⟩
  intro x hx
  let P : ℝ := ∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n
  by_cases hxlarge : x₁ ≤ x
  · have hx9 : 9 ≤ x := le_trans hx₁9 hxlarge
    have hxpos : 0 < x := by linarith
    have hxone : 1 ≤ x := by linarith
    have hlog4 : 4 ≤ Real.log x := by
      have hx₁pos : 0 < x₁ := by linarith
      exact hx₁log.trans (Real.log_le_log hx₁pos hxlarge)
    have hlogpos : 0 < Real.log x := by linarith
    have hlognonneg : 0 ≤ Real.log x := hlogpos.le
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hsqrt3 : 3 ≤ Real.sqrt x := by
      have hsqrt9 : Real.sqrt (9 : ℝ) = 3 := by
        rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num,
          Real.sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      calc
        (3 : ℝ) = Real.sqrt 9 := hsqrt9.symm
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx9
    have hsqrtle : Real.sqrt x ≤ x :=
      Real.sqrt_le_self_iff.mpr (Or.inr hxone)
    have hcut : x / Real.sqrt x = Real.sqrt x := by
      calc
        x / Real.sqrt x = (Real.sqrt x) ^ 2 / Real.sqrt x := by
          rw [Real.sq_sqrt hxpos.le]
        _ = Real.sqrt x := by field_simp [ne_of_gt hsqrtpos]
    have hDlog : Real.log (Real.sqrt x) = Real.log x / 2 :=
      Real.log_sqrt hxpos.le
    let L : ℝ := Real.log (Real.sqrt x)
    have hlogxL : Real.log x = 2 * L := by dsimp [L]; rw [hDlog]; ring
    have hLge2 : 2 ≤ L := by
      have hscaled : 4 ≤ 2 * L := by
        rw [← hlogxL]
        exact hlog4
      linarith
    have hLge1 : 1 ≤ L := by linarith
    have hLpos : 0 < L := by linarith
    have hLnonneg : 0 ≤ L := hLpos.le
    have hLpow : 0 ≤ Real.rpow L (2 - R) := Real.rpow_nonneg hLnonneg _
    have hM₂x := hM₂
    have hA :
        |∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
          mobiusRealCoefficient d / (d : ℝ)| ≤
        C₂ * (2 * Real.rpow L (-R) + Real.rpow L (1 - R) / (R - 1)) := by
      simpa [mobiusRealCoefficient, L] using
        (principalPrime_unweighted_infinite_tail_bound hR3 hC₂ hsqrt3 hM₂)
    have hB :
        |(∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
          mobiusRealCoefficient d * Real.log (d : ℝ) / (d : ℝ)) + 1| ≤
        3 * C₂ * Real.rpow L (2 - R) := by
      simpa [mobiusRealCoefficient, L] using
        (principalPrime_weighted_infinite_tail_bound hR3 hC₂ hsqrt3 hM₂)
    let A : ℝ := ∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
      mobiusRealCoefficient d / (d : ℝ)
    let B : ℝ := ∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
      mobiusRealCoefficient d * Real.log (d : ℝ) / (d : ℝ)
    let S : ℝ := ∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
      mobiusRealCoefficient d *
        (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))), Real.log (m : ℝ))
    let T : ℝ := ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
      Real.log (m : ℝ) *
        (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
          (Nat.floor (x / (m : ℝ))), mobiusRealCoefficient d)
    have hA' : |A| ≤ C₂ *
        (2 * Real.rpow L (-R) + Real.rpow L (1 - R) / (R - 1)) := by
      simpa [A] using hA
    have hB' : |B + 1| ≤ 3 * C₂ * Real.rpow L (2 - R) := by
      simpa [B] using hB
    have hLpow1 : L * Real.rpow L (-R) = Real.rpow L (1 - R) := by
      calc
        L * Real.rpow L (-R) = Real.rpow L 1 * Real.rpow L (-R) := by
          exact congrArg (fun z : ℝ => z * Real.rpow L (-R))
            (Real.rpow_one L).symm
        _ = Real.rpow L (1 + (-R)) := (Real.rpow_add hLpos 1 (-R)).symm
        _ = Real.rpow L (1 - R) := by congr 1 <;> ring
    have hLpow2 : L * Real.rpow L (1 - R) = Real.rpow L (2 - R) := by
      calc
        L * Real.rpow L (1 - R) = Real.rpow L 1 * Real.rpow L (1 - R) := by
          exact congrArg (fun z : ℝ => z * Real.rpow L (1 - R))
            (Real.rpow_one L).symm
        _ = Real.rpow L (1 + (1 - R)) := (Real.rpow_add hLpos 1 (1 - R)).symm
        _ = Real.rpow L (2 - R) := by congr 1 <;> ring
    have hden : 0 < R - 1 := by linarith
    have hrat : 2 / (R - 1) ≤ 1 := by
      rw [div_le_iff₀ hden]
      linarith
    have hpowMinus : Real.rpow L (-R) ≤ Real.rpow L (1 - R) :=
      Real.rpow_le_rpow_of_exponent_le hLge1 (by linarith)
    have hpowMid : Real.rpow L (1 - R) ≤ Real.rpow L (2 - R) :=
      Real.rpow_le_rpow_of_exponent_le hLge1 (by linarith)
    have hAweighted :
        (Real.log x - 1) * |A| ≤ 5 * C₂ * Real.rpow L (2 - R) := by
      have hu0 : 0 ≤ Real.log x - 1 := by linarith
      have hu2 : Real.log x - 1 ≤ 2 * L := by rw [hlogxL]; linarith
      calc
        (Real.log x - 1) * |A| ≤ (2 * L) * |A| :=
          mul_le_mul_of_nonneg_right hu2 (abs_nonneg _)
        _ ≤ (2 * L) *
            (C₂ * (2 * Real.rpow L (-R) + Real.rpow L (1 - R) / (R - 1))) :=
          mul_le_mul_of_nonneg_left hA' (by positivity)
        _ = C₂ * (4 * (L * Real.rpow L (-R)) +
            (2 / (R - 1)) * (L * Real.rpow L (1 - R))) := by ring
        _ = C₂ * (4 * Real.rpow L (1 - R) +
            (2 / (R - 1)) * Real.rpow L (2 - R)) := by
          rw [hLpow1, hLpow2]
        _ ≤ C₂ * (4 * Real.rpow L (2 - R) +
            1 * Real.rpow L (2 - R)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C₂)
          exact add_le_add
            (mul_le_mul_of_nonneg_left hpowMid (by norm_num))
            (mul_le_mul_of_nonneg_right hrat hLpow)
        _ = 5 * C₂ * Real.rpow L (2 - R) := by ring
    have hu0 : 0 ≤ Real.log x - 1 := by linarith
    have hAweighted' : |Real.log x - 1| * |A| ≤
        5 * C₂ * Real.rpow L (2 - R) := by
      rw [abs_of_nonneg hu0]
      exact hAweighted
    have hinner :
        |(Real.log x - 1) * A - (B + 1)| ≤
          |Real.log x - 1| * |A| + |B + 1| := by
      calc
        |(Real.log x - 1) * A - (B + 1)| =
            |(Real.log x - 1) * A + -(B + 1)| := by rw [sub_eq_add_neg]
        _ ≤ |(Real.log x - 1) * A| + |-(B + 1)| :=
          abs_add_le _ _
        _ = |(Real.log x - 1) * A| + |B + 1| := by rw [abs_neg]
        _ = |Real.log x - 1| * |A| + |B + 1| := by rw [abs_mul]
    have hHdiff (H : ℝ) (hH : H = x * ((Real.log x - 1) * A - B)) :
        |H - x| ≤ 8 * C₂ * x * Real.rpow L (2 - R) := by
      have hEq : H - x = x * ((Real.log x - 1) * A - (B + 1)) := by
        rw [hH]
        ring
      rw [hEq, abs_mul, abs_of_nonneg hxpos.le]
      calc
        x * |(Real.log x - 1) * A - (B + 1)| ≤
            x * (|Real.log x - 1| * |A| + |B + 1|) :=
          mul_le_mul_of_nonneg_left hinner hxpos.le
        _ ≤ x * (5 * C₂ * Real.rpow L (2 - R) +
              3 * C₂ * Real.rpow L (2 - R)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add hAweighted' hB') hxpos.le
        _ = 8 * C₂ * x * Real.rpow L (2 - R) := by ring
    have hpowlog : Real.rpow (Real.log x) (2 - R) =
        Real.rpow 2 (2 - R) * Real.rpow L (2 - R) := by
      rw [hlogxL]
      change (2 * L) ^ (2 - R) = 2 ^ (2 - R) * L ^ (2 - R)
      exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hLnonneg
    have hcoeff : Real.rpow 2 (R + 2) * Real.rpow 2 (2 - R) = 16 := by
      change (2 : ℝ) ^ (R + 2) * (2 : ℝ) ^ (2 - R) = 16
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) (R + 2) (2 - R)]
      have he : R + 2 + (2 - R) = (4 : ℝ) := by ring
      rw [he]
      norm_num
    have hVbound :
        |x * ((Real.log x - 1) * A - B) - x| ≤
          Real.rpow 2 (R + 2) * C₂ * x * Real.rpow (Real.log x) (2 - R) := by
      have h := hHdiff _ rfl
      calc
        |x * ((Real.log x - 1) * A - B) - x| ≤
            8 * C₂ * x * Real.rpow L (2 - R) := h
        _ ≤ 16 * C₂ * x * Real.rpow L (2 - R) := by
          nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ C₂) hxpos.le) hLpow]
        _ = Real.rpow 2 (R + 2) * C₂ * x *
              (Real.rpow 2 (2 - R) * Real.rpow L (2 - R)) := by
          calc
            16 * C₂ * x * Real.rpow L (2 - R) =
                Real.rpow 2 (R + 2) * Real.rpow 2 (2 - R) * C₂ * x *
                  Real.rpow L (2 - R) := by rw [← hcoeff]
            _ = Real.rpow 2 (R + 2) * C₂ * x *
                  (Real.rpow 2 (2 - R) * Real.rpow L (2 - R)) := by ring
        _ = Real.rpow 2 (R + 2) * C₂ * x *
              Real.rpow (Real.log x) (2 - R) := by rw [← hpowlog]
    have hlogparam : Real.rpow 2 (1 + 1) ≤ Real.log x := by
      norm_num
      exact hlog4
    have hqparam : (1 : ℝ) ≤ Real.rpow (Real.log x) (1 : ℝ) := by
      simpa [Real.rpow_one] using (by linarith : (1 : ℝ) ≤ Real.log x)
    have hlargeComplex := hLarge hx9 hlogparam
      (χ := (1 : DirichletCharacter ℂ 1)) (by simpa using hqparam)
    rw [principalPrime_largeHalf_sum_eq_ofReal hx9] at hlargeComplex
    have hlargeReal :
        |∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
          Real.log (m : ℝ) *
            (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
              (Nat.floor (x / (m : ℝ))), mobiusRealCoefficient d)| ≤
          Real.rpow 2 (R + 2) * Cₗ * x * Real.rpow (Real.log x) (2 - R) := by
      rw [← norm_sum_complexLog_nat_eq_abs_realLog_sum
        (s := Finset.Icc 1 (Nat.floor (Real.sqrt x)))
        (t := fun m => Finset.Ioc (Nat.floor (Real.sqrt x))
          (Nat.floor (x / (m : ℝ)))) (f := mobiusRealCoefficient)]
      simpa using hlargeComplex
    have hlargeC₂ : |T| ≤
        Real.rpow 2 (R + 2) * C₂ * x * Real.rpow (Real.log x) (2 - R) := by
      have hpref : Real.rpow 2 (R + 2) * Cₗ ≤ Real.rpow 2 (R + 2) * C₂ :=
        mul_le_mul_of_nonneg_left hCₗC₂
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (R + 2))
      calc
        |T| ≤ Real.rpow 2 (R + 2) * Cₗ * x *
            Real.rpow (Real.log x) (2 - R) := by simpa [T] using hlargeReal
        _ ≤ Real.rpow 2 (R + 2) * C₂ * x *
            Real.rpow (Real.log x) (2 - R) := by
          calc
            _ = (Real.rpow 2 (R + 2) * Cₗ) *
                  (x * Real.rpow (Real.log x) (2 - R)) := by ring
            _ ≤ (Real.rpow 2 (R + 2) * C₂) *
                  (x * Real.rpow (Real.log x) (2 - R)) :=
                mul_le_mul_of_nonneg_right hpref
                  (mul_nonneg hxpos.le
                    (Real.rpow_nonneg hlognonneg (2 - R)))
            _ = _ := by ring
    have hsplit := principalPrimeHyperbolaSplit hsqrtpos hsqrtle
    rw [hcut] at hsplit
    have hsplit' : P = S + T := by simpa [P, S, T] using hsplit
    have hsmallApprox := principalPrimeSmallRangeApproximation (x := x) hx
    have hsmall :
        |S - x * ((Real.log x - 1) * A - B)| ≤
          4 * Real.sqrt x * Real.log x := by
      simpa [S, A, B, mobiusRealCoefficient] using hsmallApprox
    have hdecomp : P - x =
        (S - x * ((Real.log x - 1) * A - B)) +
          (x * ((Real.log x - 1) * A - B) - x) + T := by
      rw [hsplit']
      ring
    have htotal :
        |P - x| ≤ Real.rpow 2 (R + 3) * C₂ * x *
            Real.rpow (Real.log x) (2 - R) + 4 * Real.sqrt x * Real.log x := by
      have hdouble : 2 * Real.rpow 2 (R + 2) = Real.rpow 2 (R + 3) := by
        change 2 * (2 : ℝ) ^ (R + 2) = (2 : ℝ) ^ (R + 3)
        calc
          2 * (2 : ℝ) ^ (R + 2) = (2 : ℝ) ^ 1 * (2 : ℝ) ^ (R + 2) := by
            norm_num
          _ = (2 : ℝ) ^ (1 + (R + 2)) :=
            (Real.rpow_add (by norm_num : 0 < (2 : ℝ)) 1 (R + 2)).symm
          _ = (2 : ℝ) ^ (R + 3) := by congr 1 <;> ring
      calc
        |P - x| =
            |(S - x * ((Real.log x - 1) * A - B)) +
              (x * ((Real.log x - 1) * A - B) - x) + T| := by rw [hdecomp]
        _ ≤ |S - x * ((Real.log x - 1) * A - B)| +
              |x * ((Real.log x - 1) * A - B) - x| + |T| := by
          calc
            _ ≤ |(S - x * ((Real.log x - 1) * A - B)) +
                  (x * ((Real.log x - 1) * A - B) - x)| + |T| := abs_add_le _ _
            _ ≤ _ := add_le_add_left (abs_add_le _ _) _
        _ ≤ 4 * Real.sqrt x * Real.log x +
              (Real.rpow 2 (R + 2) * C₂ * x * Real.rpow (Real.log x) (2 - R)) +
              (Real.rpow 2 (R + 2) * C₂ * x * Real.rpow (Real.log x) (2 - R)) :=
          add_le_add (add_le_add hsmall hVbound) hlargeC₂
        _ = 4 * Real.sqrt x * Real.log x +
              (2 * Real.rpow 2 (R + 2)) * C₂ * x *
                Real.rpow (Real.log x) (2 - R) := by ring
        _ = Real.rpow 2 (R + 3) * C₂ * x *
              Real.rpow (Real.log x) (2 - R) + 4 * Real.sqrt x * Real.log x := by
          rw [hdouble]
          ring
    have hlogexp : Real.rpow (Real.log x) (2 - R) ≤
        Real.rpow (Real.log x) (-K) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Real.log x)
        (by dsimp [R]; linarith)
    have hpowNeg : 0 ≤ Real.rpow (Real.log x) (-K) :=
      Real.rpow_nonneg hlognonneg _
    have hmulAbsorb := mul_le_mul_of_nonneg_right
      (hAbsorb x hxlarge) (Real.rpow_nonneg hlognonneg (-K))
    have hprod : Real.rpow (Real.log x) (K + 1) *
        Real.rpow (Real.log x) (-K) = Real.log x := by
      calc
        _ = Real.rpow (Real.log x) ((K + 1) + (-K)) :=
          (Real.rpow_add hlogpos (K + 1) (-K)).symm
        _ = Real.log x := by congr 1 <;> norm_num [Real.rpow_one] <;> ring
    have hlogAbsorb : 4 * Real.log x ≤
        Real.sqrt x * Real.rpow (Real.log x) (-K) := by
      calc
        4 * Real.log x =
            (4 * Real.rpow (Real.log x) (K + 1)) *
              Real.rpow (Real.log x) (-K) := by
          calc
            4 * Real.log x =
                4 * (Real.rpow (Real.log x) (K + 1) *
                  Real.rpow (Real.log x) (-K)) :=
              congrArg (fun z : ℝ => 4 * z) hprod.symm
            _ = (4 * Real.rpow (Real.log x) (K + 1)) *
                  Real.rpow (Real.log x) (-K) := by ring
        _ ≤ Real.sqrt x * Real.rpow (Real.log x) (-K) := hmulAbsorb
    have herrorAbsorb : 4 * Real.sqrt x * Real.log x ≤
        x * Real.rpow (Real.log x) (-K) := by
      calc
        4 * Real.sqrt x * Real.log x =
            Real.sqrt x * (4 * Real.log x) := by ring
        _ ≤ Real.sqrt x *
            (Real.sqrt x * Real.rpow (Real.log x) (-K)) :=
          mul_le_mul_of_nonneg_left hlogAbsorb (Real.sqrt_nonneg x)
        _ = x * Real.rpow (Real.log x) (-K) := by
          rw [← mul_assoc, ← pow_two, Real.sq_sqrt hxpos.le]
    have hlargeAbsorb :
        Real.rpow 2 (R + 3) * C₂ * x * Real.rpow (Real.log x) (2 - R) ≤
          Real.rpow 2 (R + 3) * C₂ * x * Real.rpow (Real.log x) (-K) :=
      mul_le_mul_of_nonneg_left hlogexp
        (mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (R + 3))
            (by linarith))
          hxpos.le)
    calc
      |P - x| ≤ Real.rpow 2 (R + 3) * C₂ * x *
          Real.rpow (Real.log x) (2 - R) + 4 * Real.sqrt x * Real.log x := htotal
      _ ≤ Real.rpow 2 (R + 3) * C₂ * x *
            Real.rpow (Real.log x) (-K) + x * Real.rpow (Real.log x) (-K) :=
        add_le_add hlargeAbsorb herrorAbsorb
      _ = Cbig * x * Real.rpow (Real.log x) (-K) := by
        dsimp [Cbig]
        ring
      _ ≤ C₀ * x * Real.rpow (Real.log x) (-K) := by
        have hfac : 0 ≤ x * Real.rpow (Real.log x) (-K) :=
          mul_nonneg hxpos.le hpowNeg
        have h := mul_le_mul_of_nonneg_right hCbig hfac
        nlinarith [h]
  · have hxle : x ≤ x₁ := le_of_not_ge hxlarge
    have hxpos : 0 < x := by linarith
    have hxone : 1 ≤ x := by linarith
    have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg hxone
    have hlogx1pos : 0 < Real.log x₁ := by linarith
    have hlogle : Real.log x ≤ Real.log x₁ :=
      Real.log_le_log (by linarith) hxle
    have hpowle : Real.rpow (Real.log x) K ≤
        Real.rpow (Real.log x₁) K :=
      Real.rpow_le_rpow hlognonneg hlogle hK.le
    have hfactor :
        (1 + Real.log x) * Real.rpow (Real.log x) K ≤ Csmall := by
      dsimp [Csmall]
      calc
        (1 + Real.log x) * Real.rpow (Real.log x) K ≤
            (1 + Real.log x₁) * Real.rpow (Real.log x) K :=
          mul_le_mul_of_nonneg_right (add_le_add_right hlogle 1)
            (Real.rpow_nonneg hlognonneg K)
        _ ≤ (1 + Real.log x₁) * Real.rpow (Real.log x₁) K :=
          mul_le_mul_of_nonneg_left hpowle (by linarith)
    have hpowNeg : 0 ≤ Real.rpow (Real.log x) (-K) :=
      Real.rpow_nonneg hlognonneg _
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hprod : Real.rpow (Real.log x) K *
        Real.rpow (Real.log x) (-K) = 1 := by
      change (Real.log x) ^ K * (Real.log x) ^ (-K) = 1
      rw [← Real.rpow_add hlogpos K (-K)]
      simp
    have hmajor : 1 + Real.log x ≤ Csmall *
        Real.rpow (Real.log x) (-K) := by
      calc
        1 + Real.log x =
            ((1 + Real.log x) * Real.rpow (Real.log x) K) *
              Real.rpow (Real.log x) (-K) := by
          rw [mul_assoc, hprod, mul_one]
        _ ≤ Csmall * Real.rpow (Real.log x) (-K) :=
          mul_le_mul_of_nonneg_right hfactor hpowNeg
    calc
      |P - x| ≤ x * (1 + Real.log x) := by
        simpa [P] using vonMangoldt_Icc_floor_abs_sub_x_le hx
      _ ≤ x * (Csmall * Real.rpow (Real.log x) (-K)) :=
        mul_le_mul_of_nonneg_left hmajor hxpos.le
      _ = Csmall * x * Real.rpow (Real.log x) (-K) := by ring
      _ ≤ C₀ * x * Real.rpow (Real.log x) (-K) := by
        have hfac : 0 ≤ x * Real.rpow (Real.log x) (-K) :=
          mul_nonneg hxpos.le hpowNeg
        have h := mul_le_mul_of_nonneg_right hCsmall hfac
        nlinarith [h]

end FractionalPrimes.Literature.MobiusToLong

end
