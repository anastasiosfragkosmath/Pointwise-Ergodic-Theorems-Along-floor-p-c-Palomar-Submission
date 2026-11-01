module

public import FractionalPrimes.Literature.Polynomial.ResiduePrefixEnvelope
public import FractionalPrimes.Literature.Uniformity.CramerShortDivisor
public import FractionalPrimes.CramerDensityAtScale
public import FractionalPrimes.ArithmeticBasics
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Prefix bounds from ordinary full-interval residue cancellation

This is the deterministic `lup:prefix-of-full` layer.  Its input records
only ordinary, unphased residue sums on full intervals.  The short-prefix
case is controlled directly by the source pointwise bounds.
-/

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open scoped BigOperators

/-- Uniform cancellation on complete ordinary residue intervals, in the
same fixed-residue form implied by the source's sum-of-two-maxima statement.
No polynomial phases occur in this contract. -/
def ordinaryFullResidueCancellationTask : Prop :=
  ∀ A B η : ℝ, (hA : 0 < A) → (hB : 0 < B) →
    (hη : 0 < η) → (hη₃ : η < 3 / 16) →
      ∃ C_F : ℝ, 0 < C_F ∧
        ∀ X H : ℕ, 3 ≤ X →
          (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
          (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B →
            ∀ a : ℕ, a < q →
              ‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖ +
                ‖residuePrefixSum X H q a
                  (fun n => (paperLambda n : ℂ) -
                    (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
                C_F * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ)

private theorem realIntegerInterval_nat_eq_Ioc
    (X H : ℕ) :
    realIntegerInterval (X : ℝ) (H : ℝ) =
      Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) := by
  ext n
  rw [mem_realIntegerInterval_iff]
  simp only [Finset.mem_Ioc]
  constructor <;> intro hn <;> exact ⟨by exact_mod_cast hn.1,
    by exact_mod_cast hn.2⟩

private theorem realIntegerInterval_intLength_card
    (X H : ℕ) :
    ((realIntegerInterval (X : ℝ) (H : ℝ)).card : ℝ) = (H : ℝ) := by
  rw [realIntegerInterval_nat_eq_Ioc]
  exact_mod_cast
    FractionalPrimes.Literature.Uniformity.cramerShortInterval_card X H

/-- Trivial combined pointwise control for a short residue prefix.  The
constant is the one used in the source proof: `μ` costs one `log X`, and
`Λ-Cr_X` costs at most `(exp 13 + 2) log X` on `n ≤ 2X`. -/
theorem residuePrefixComponents_pointwiseBounds
    (X m q a : ℕ) (hX : 3 ≤ X) (hm : m ≤ X) :
    ‖residuePrefixSum X m q a (fun n => (paperMu n : ℂ))‖ ≤
        (m : ℝ) * Real.log (X : ℝ) ∧
      ‖residuePrefixSum X m q a
        (fun n => (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
        (Real.exp 13 + 2) * (m : ℝ) * Real.log (X : ℝ) := by
  classical
  let I := realIntegerInterval (X : ℝ) (m : ℝ)
  have hXr : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by linarith
  have hXone : 1 ≤ (X : ℝ) := by linarith
  have hlogXone : 1 ≤ Real.log (X : ℝ) := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans hXr
  have hlogXpos : 0 < Real.log (X : ℝ) := lt_of_lt_of_le (by norm_num) hlogXone
  have hmreal : (m : ℝ) ≤ (X : ℝ) := by exact_mod_cast hm
  have htwoX : (X : ℝ) + (m : ℝ) ≤ 2 * (X : ℝ) := by linarith
  have hlog2X : Real.log (2 * (X : ℝ)) ≤ 2 * Real.log (X : ℝ) := by
    have hlog2 : Real.log 2 ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by norm_num) (by linarith [hXr])
    rw [Real.log_mul (by norm_num) hXpos.ne']
    linarith
  have hpowlog : (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) ≤ Real.log (X : ℝ) := by
    calc
      (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) ≤
          (Real.log (X : ℝ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogXone (by norm_num)
      _ = Real.log (X : ℝ) := by rw [Real.rpow_one]
  have hmodelBound : paperCramerDensity (paperShortBlockCutoff (X : ℝ)) ≤
      Real.exp 13 * Real.log (X : ℝ) := by
    have h := paperCramerDensity_at_cutoff_scale hXr
    calc
      paperCramerDensity (paperShortBlockCutoff (X : ℝ)) ≤
          Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) := by
            simpa [paperShortBlockCutoff] using h
      _ ≤ Real.exp 13 * Real.log (X : ℝ) :=
        mul_le_mul_of_nonneg_left hpowlog (by positivity)
  have hmu :
      ‖residuePrefixSum X m q a (fun n => (paperMu n : ℂ))‖ ≤ (m : ℝ) := by
    have hcard := realIntegerInterval_intLength_card X m
    unfold residuePrefixSum
    calc
      ‖∑ n ∈ I.filter (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]),
          (paperMu n : ℂ)‖ ≤
        ∑ n ∈ I.filter (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]),
          ‖(paperMu n : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ I.filter (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]),
          (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hmem := (mem_realIntegerInterval_iff (X : ℝ) (m : ℝ) n).1
          (Finset.mem_filter.mp hn).1
        have hnpos : 1 ≤ n := by
          have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
            have hXcast : (3 : ℝ) ≤ (X : ℝ) := hXr
            linarith [hmem.1]
          exact_mod_cast hnreal
        exact_mod_cast paperMu_abs_le_one hnpos
      _ = ((I.filter (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)] )).card : ℝ) := by
        simp
      _ ≤ (I.card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
      _ = (m : ℝ) := hcard
  have hlam :
      ‖residuePrefixSum X m q a
        (fun n => (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
        (Real.exp 13 + 2) * (m : ℝ) * Real.log (X : ℝ) := by
    have hcard := realIntegerInterval_intLength_card X m
    unfold residuePrefixSum
    calc
      ‖∑ n ∈ I.filter (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]),
          ((paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
        ∑ n ∈ I.filter (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]),
          ‖(paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ I.filter (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]),
          ((Real.exp 13 + 2) * Real.log (X : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hmem := (mem_realIntegerInterval_iff (X : ℝ) (m : ℝ) n).1
          (Finset.mem_filter.mp hn).1
        have hnpos : 1 ≤ n := by
          have hnreal : (1 : ℝ) ≤ (n : ℝ) := by linarith [hmem.1]
          exact_mod_cast hnreal
        have hnupper : (n : ℝ) ≤ 2 * (X : ℝ) := by
          have := hmem.2
          linarith
        have hLambdaBounds := paperLambda_bounds hnpos
        have hLambdaAbs : |paperLambda n| ≤ Real.log (2 * (X : ℝ)) := by
          rw [abs_of_nonneg hLambdaBounds.1]
          exact hLambdaBounds.2.trans (Real.log_le_log (by positivity) hnupper)
        have hCr :=
          FractionalPrimes.Literature.Uniformity.cramerWeight_abs_le_density
            (X : ℝ) n
        have hCr' : |paperShortBlockCramerWeight (X : ℝ) n| ≤
            Real.exp 13 * Real.log (X : ℝ) := hCr.trans hmodelBound
        have hnorm : ‖(paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ)‖ =
            |paperLambda n - paperShortBlockCramerWeight (X : ℝ) n| := by
          calc
            ‖(paperLambda n : ℂ) -
                (paperShortBlockCramerWeight (X : ℝ) n : ℂ)‖ =
              ‖((paperLambda n - paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)‖ := by
                congr 1
                push_cast
                ring
            _ = |paperLambda n - paperShortBlockCramerWeight (X : ℝ) n| := by
              rw [Complex.norm_real, Real.norm_eq_abs]
        rw [hnorm]
        calc
          |paperLambda n - paperShortBlockCramerWeight (X : ℝ) n| ≤
              |paperLambda n| +
                |paperShortBlockCramerWeight (X : ℝ) n| := abs_sub _ _
          _ ≤ Real.log (2 * (X : ℝ)) +
              Real.exp 13 * Real.log (X : ℝ) := add_le_add hLambdaAbs hCr'
          _ ≤ (Real.exp 13 + 2) * Real.log (X : ℝ) := by nlinarith
      _ = ((I.filter (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)] )).card : ℝ) *
          ((Real.exp 13 + 2) * Real.log (X : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (I.card : ℝ) *
          ((Real.exp 13 + 2) * Real.log (X : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Finset.card_filter_le _ _
        · positivity
      _ = (Real.exp 13 + 2) * (m : ℝ) * Real.log (X : ℝ) := by
        rw [hcard]
        ring
  have hmu' : ‖residuePrefixSum X m q a (fun n => (paperMu n : ℂ))‖ ≤
      (m : ℝ) * Real.log (X : ℝ) := by
    calc
      _ ≤ (m : ℝ) := hmu
      _ ≤ (m : ℝ) * Real.log (X : ℝ) := by
        have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
        calc
          (m : ℝ) = (m : ℝ) * 1 := by ring
          _ ≤ (m : ℝ) * Real.log (X : ℝ) :=
            mul_le_mul_of_nonneg_left hlogXone hmnonneg
  exact ⟨hmu', hlam⟩

/-- The source's combined trivial short-prefix estimate. -/
theorem residuePrefixPair_pointwiseBound
    (X m q a : ℕ) (hX : 3 ≤ X) (hm : m ≤ X) :
    ‖residuePrefixSum X m q a (fun n => (paperMu n : ℂ))‖ +
      ‖residuePrefixSum X m q a
        (fun n => (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
      (Real.exp 13 + 3) * (m : ℝ) * Real.log (X : ℝ) := by
  obtain ⟨hmu, hlam⟩ := residuePrefixComponents_pointwiseBounds X m q a hX hm
  calc
    _ ≤ (m : ℝ) * Real.log (X : ℝ) +
        (Real.exp 13 + 2) * (m : ℝ) * Real.log (X : ℝ) :=
      add_le_add hmu hlam
    _ = (Real.exp 13 + 3) * (m : ℝ) * Real.log (X : ℝ) := by ring

private theorem exists_log_rpow_le_rpow
    (M s : ℝ) (hM : 0 < M) (hs : 0 < s) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → (Real.log X) ^ M ≤ X ^ s := by
  let e : ℝ := s / (M + 1)
  have he : 0 < e := by dsimp [e]; positivity
  have hevent := FractionalPrimes.eventually_log_le_const_mul_rpow he
    (by norm_num : 0 < (1 : ℝ))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hevent
  let X₀ := max 3 T
  refine ⟨X₀, le_max_left _ _, ?_⟩
  intro X hX₀
  have hX3 : 3 ≤ X := le_trans (le_max_left _ _) hX₀
  have hXT : T ≤ X := le_trans (le_max_right _ _) hX₀
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog : Real.log X ≤ X ^ e := by
    have h := hT X hXT
    simpa [one_mul] using h
  have hpow : (Real.log X) ^ M ≤ (X ^ e) ^ M :=
    Real.rpow_le_rpow hlogpos.le hlog hM.le
  have hpow' : (X ^ e) ^ M = X ^ (e * M) := by
    rw [Real.rpow_mul hXpos.le]
  have hexp : e * M ≤ s := by
    dsimp [e]
    have hden : 0 < M + 1 := by linarith
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith
  calc
    (Real.log X) ^ M ≤ (X ^ e) ^ M := hpow
    _ = X ^ (e * M) := hpow'
    _ ≤ X ^ s := Real.rpow_le_rpow_of_exponent_le hXone hexp

set_option maxHeartbeats 1000000 in
/-- The exact deterministic prefix-of-full implication in the approved
blueprint.  The input is ordinary unphased residue cancellation on full
intervals; the output is the two source prefix envelopes. -/
theorem polynomialMajorArcTask_of_ordinaryFullResidueCancellation
    (hFull : ordinaryFullResidueCancellationTask) : polynomialMajorArcTask := by
  intro A B η hA hB hη hη₃
  have hA1 : 0 < A + 1 := by linarith
  have hη2 : 0 < η / 2 := by linarith
  have hη2₃ : η / 2 < 3 / 16 := by linarith
  obtain ⟨C_F, hC_F, hFullData⟩ :=
    hFull (A + 1) B (η / 2) hA1 hB hη2 hη2₃
  have hM : 0 < A + 3 := by linarith
  obtain ⟨X₀, hX₀, hlogPower⟩ :=
    exists_log_rpow_le_rpow (A + 3) (η / 2) hM hη2
  let Cmain : ℝ := 2 * C_F + (Real.exp 13 + 3)
  let Csmall : ℝ := (Real.exp 13 + 3) * (Real.log X₀) ^ (A + 1)
  let C : ℝ := max Cmain Csmall
  have hCmain : 0 < Cmain := by dsimp [Cmain]; positivity
  have hCsmall : 0 < Csmall := by
    dsimp [Csmall]
    have hX₀pos : 0 < X₀ := by linarith [hX₀]
    have hlogX₀pos : 0 < Real.log X₀ := Real.log_pos (by linarith [hX₀])
    positivity
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le hCmain (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro X H hX hHlower hHupper
  let Xr : ℝ := (X : ℝ)
  let Hr : ℝ := (H : ℝ)
  let ell : ℝ := Real.log Xr
  let Q : ℝ := ell ^ B
  let tau : ℝ := Hr * ell ^ (-(A + 3))
  have hXr : 3 ≤ Xr := by
    change (3 : ℝ) ≤ (X : ℝ)
    exact_mod_cast hX
  have hXpos : 0 < Xr := by linarith [hXr]
  have hXone : 1 ≤ Xr := by linarith [hXr]
  have hellone : 1 ≤ ell := by
    dsimp [ell, Xr]
    apply (Real.le_log_iff_exp_le (by positivity : 0 < (X : ℝ))).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hX)
  have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hellone
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact Real.one_le_rpow hellone hB.le
  have hHleXpow : Hr ≤ Xr := by
    have hexp : 1 - η ≤ (1 : ℝ) := by linarith
    have hpow : Xr ^ (1 - η) ≤ Xr := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hXone hexp
    exact hHupper.trans hpow
  have hHleX : H ≤ X := by
    change (H : ℝ) ≤ (X : ℝ) at hHleXpow
    exact_mod_cast hHleXpow
  have hlogX₀pos : 0 < Real.log X₀ := Real.log_pos (by linarith [hX₀])
  have hEnvelopeBound :
      X₀ ≤ Xr → ∀ (w : ℤ → ℂ) (K : ℝ), 0 ≤ K →
        (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Q →
          ∀ a : ℕ, a < q → ∀ m : ℕ,
            Xr ^ ((5 / 8 : ℝ) + η / 2) ≤ (m : ℝ) →
            (m : ℝ) ≤ Xr ^ (1 - η / 2) →
            ‖residuePrefixSum X m q a w‖ ≤
              C_F * (m : ℝ) * ell ^ (-(A + 1))) →
        (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Q →
          ∀ a : ℕ, a < q → ∀ m : ℕ, m ≤ H →
            ‖residuePrefixSum X m q a w‖ ≤
              K * (m : ℝ) * ell) →
        residuePrefixEnvelope X H w Q ≤ (C_F + K) * Hr * ell ^ (-A) := by
    intro hXlarge w K hK hFullTerm hPointTerm
    obtain ⟨q, a, m, hq, hqQ, ha, hm, hEq⟩ :=
      residuePrefixEnvelope_attained X H w Q hQ
    rw [hEq]
    by_cases hlarge : tau ≤ (m : ℝ)
    · have hlogPowerX : ell ^ (A + 3) ≤ Xr ^ (η / 2) := by
        have h := hlogPower Xr hXlarge
        simpa [ell, Xr] using h
      have htargetProd :
          Xr ^ ((5 / 8 : ℝ) + η / 2) * ell ^ (A + 3) ≤ Hr := by
        calc
          Xr ^ ((5 / 8 : ℝ) + η / 2) * ell ^ (A + 3) ≤
              Xr ^ ((5 / 8 : ℝ) + η / 2) * Xr ^ (η / 2) :=
            mul_le_mul_of_nonneg_left hlogPowerX
              (Real.rpow_nonneg hXpos.le _)
          _ = Xr ^ ((5 / 8 : ℝ) + η) := by
            rw [← Real.rpow_add hXpos]
            congr 1
            ring
          _ ≤ Hr := by simpa [Xr, Hr] using hHlower
      have hMpos : 0 < (A + 3 : ℝ) := hM
      have hlogMpos : 0 < ell ^ (A + 3) := Real.rpow_pos_of_pos hellpos _
      have htauEq : tau = Hr / ell ^ (A + 3) := by
        dsimp [tau]
        rw [Real.rpow_neg hellpos.le]
        ring
      have htargetTau : Xr ^ ((5 / 8 : ℝ) + η / 2) ≤ tau := by
        rw [htauEq]
        exact (le_div_iff₀ hlogMpos).2 htargetProd
      have hmLower := htargetTau.trans hlarge
      have hEtaExp : 1 - η ≤ 1 - η / 2 := by linarith
      have hUpperHalf : Hr ≤ Xr ^ (1 - η / 2) :=
        hHupper.trans (Real.rpow_le_rpow_of_exponent_le hXone hEtaExp)
      have hmUpper : (m : ℝ) ≤ Xr ^ (1 - η / 2) :=
        (Nat.cast_le.mpr hm).trans hUpperHalf
      have hTerm := hFullTerm q hq hqQ a ha m hmLower hmUpper
      have hmcast : (m : ℝ) ≤ Hr := Nat.cast_le.mpr hm
      have hpowA : ell ^ (-(A + 1)) ≤ ell ^ (-A) :=
        Real.rpow_le_rpow_of_exponent_le hellone (by linarith)
      have hfullScale :
          C_F * (m : ℝ) * ell ^ (-(A + 1)) ≤
            (C_F + K) * Hr * ell ^ (-A) := by
        calc
          C_F * (m : ℝ) * ell ^ (-(A + 1)) ≤
              C_F * Hr * ell ^ (-(A + 1)) := by
                apply mul_le_mul_of_nonneg_right
                · exact mul_le_mul_of_nonneg_left hmcast hC_F.le
                · exact Real.rpow_nonneg hellpos.le _
          _ ≤ C_F * Hr * ell ^ (-A) :=
            mul_le_mul_of_nonneg_left hpowA (by positivity)
          _ ≤ (C_F + K) * Hr * ell ^ (-A) := by
            have hfactor : 0 ≤ Hr * ell ^ (-A) :=
              mul_nonneg (by exact_mod_cast (Nat.cast_nonneg H))
                (Real.rpow_nonneg hellpos.le _)
            calc
              C_F * Hr * ell ^ (-A) = C_F * (Hr * ell ^ (-A)) := by ring
              _ ≤ (C_F + K) * (Hr * ell ^ (-A)) :=
                mul_le_mul_of_nonneg_right (by linarith [hK]) hfactor
              _ = (C_F + K) * Hr * ell ^ (-A) := by ring
      exact hTerm.trans hfullScale
    · have hsmall : (m : ℝ) < tau := lt_of_not_ge hlarge
      have hPoint := hPointTerm q hq hqQ a ha m hm
      have hsmallScale : (m : ℝ) * ell ≤ Hr * ell ^ (-A) := by
        have hstep₁ : (m : ℝ) * ell ≤ tau * ell :=
          mul_le_mul_of_nonneg_right hsmall.le hellpos.le
        have hpowProd : ell ^ (-(A + 3)) * ell = ell ^ (-(A + 2)) := by
          calc
            ell ^ (-(A + 3)) * ell =
                ell ^ (-(A + 3)) * ell ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = ell ^ (-(A + 3) + 1) :=
              (Real.rpow_add hellpos (-(A + 3)) 1).symm
            _ = ell ^ (-(A + 2)) := by congr 1 <;> ring
        have hstep₂ : tau * ell = Hr * ell ^ (-(A + 2)) := by
          calc
            tau * ell = Hr * (ell ^ (-(A + 3)) * ell) := by dsimp [tau]; ring
            _ = Hr * ell ^ (-(A + 2)) := by rw [hpowProd]
        have hpow : ell ^ (-(A + 2)) ≤ ell ^ (-A) :=
          Real.rpow_le_rpow_of_exponent_le hellone (by linarith)
        calc
          (m : ℝ) * ell ≤ tau * ell := hstep₁
          _ = Hr * ell ^ (-(A + 2)) := hstep₂
          _ ≤ Hr * ell ^ (-A) :=
            mul_le_mul_of_nonneg_left hpow (by exact_mod_cast (Nat.cast_nonneg H))
      calc
        ‖residuePrefixSum X m q a w‖ ≤ K * (m : ℝ) * ell := hPoint
        _ ≤ K * Hr * ell ^ (-A) := by
          have hKmul := mul_le_mul_of_nonneg_left hsmallScale hK
          nlinarith [hKmul]
        _ ≤ (C_F + K) * Hr * ell ^ (-A) := by
          have hp : 0 ≤ Hr * ell ^ (-A) :=
            mul_nonneg (by exact_mod_cast (Nat.cast_nonneg H))
              (Real.rpow_nonneg hellpos.le _)
          calc
            K * Hr * ell ^ (-A) = K * (Hr * ell ^ (-A)) := by ring
            _ ≤ (C_F + K) * (Hr * ell ^ (-A)) :=
              mul_le_mul_of_nonneg_right (by linarith [hC_F]) hp
            _ = (C_F + K) * Hr * ell ^ (-A) := by ring
  have hMuPoint :
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Q →
        ∀ a : ℕ, a < q → ∀ m : ℕ, m ≤ H →
          ‖residuePrefixSum X m q a (fun n => (paperMu n : ℂ))‖ ≤
            1 * (m : ℝ) * ell := by
    intro q hq hqQ a ha m hm
    simpa using (residuePrefixComponents_pointwiseBounds X m q a hX
      (le_trans hm hHleX)).1
  have hLambdaPoint :
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Q →
        ∀ a : ℕ, a < q → ∀ m : ℕ, m ≤ H →
          ‖residuePrefixSum X m q a
              (fun n => (paperLambda n : ℂ) -
                (paperShortBlockCramerWeight Xr n : ℂ))‖ ≤
            (Real.exp 13 + 2) * (m : ℝ) * ell := by
    intro q hq hqQ a ha m hm
    have h := (residuePrefixComponents_pointwiseBounds X m q a hX
      (le_trans hm hHleX)).2
    simpa [Xr, ell] using h
  have hMuFull :
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Q →
        ∀ a : ℕ, a < q → ∀ m : ℕ,
          Xr ^ ((5 / 8 : ℝ) + η / 2) ≤ (m : ℝ) →
          (m : ℝ) ≤ Xr ^ (1 - η / 2) →
          ‖residuePrefixSum X m q a (fun n => (paperMu n : ℂ))‖ ≤
            C_F * (m : ℝ) * ell ^ (-(A + 1)) := by
    intro q hq hqQ a ha m hml hmu
    have h := hFullData X m hX hml hmu q hq hqQ a ha
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans h
  have hLambdaFull :
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Q →
        ∀ a : ℕ, a < q → ∀ m : ℕ,
          Xr ^ ((5 / 8 : ℝ) + η / 2) ≤ (m : ℝ) →
          (m : ℝ) ≤ Xr ^ (1 - η / 2) →
          ‖residuePrefixSum X m q a
              (fun n => (paperLambda n : ℂ) -
                (paperShortBlockCramerWeight Xr n : ℂ))‖ ≤
            C_F * (m : ℝ) * ell ^ (-(A + 1)) := by
    intro q hq hqQ a ha m hml hmu
    have h := hFullData X m hX hml hmu q hq hqQ a ha
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans h
  by_cases hXlarge : X₀ ≤ Xr
  · have hMuEnv := hEnvelopeBound hXlarge (fun n => (paperMu n : ℂ)) 1
      (by norm_num) hMuFull hMuPoint
    have hLambdaEnv := hEnvelopeBound hXlarge
      (fun n => (paperLambda n : ℂ) -
        (paperShortBlockCramerWeight Xr n : ℂ))
      (Real.exp 13 + 2) (by positivity) hLambdaFull hLambdaPoint
    calc
      residuePrefixEnvelope X H (fun n => (paperMu n : ℂ)) Q +
          residuePrefixEnvelope X H
            (fun n => (paperLambda n : ℂ) -
              (paperShortBlockCramerWeight Xr n : ℂ)) Q ≤
        ((C_F + 1) + (C_F + (Real.exp 13 + 2))) * Hr * ell ^ (-A) := by
          calc
            _ ≤ (C_F + 1) * Hr * ell ^ (-A) +
                (C_F + (Real.exp 13 + 2)) * Hr * ell ^ (-A) :=
                  add_le_add hMuEnv hLambdaEnv
            _ = ((C_F + 1) + (C_F + (Real.exp 13 + 2))) *
                Hr * ell ^ (-A) := by ring
      _ = Cmain * Hr * ell ^ (-A) := by
        dsimp [Cmain]
        ring
      _ ≤ C * Hr * ell ^ (-A) := by
        have hmain : Cmain ≤ C := le_max_left Cmain Csmall
        have hHmain : Cmain * Hr ≤ C * Hr :=
          mul_le_mul_of_nonneg_right hmain (by exact_mod_cast (Nat.cast_nonneg H))
        exact mul_le_mul_of_nonneg_right hHmain (Real.rpow_nonneg hellpos.le _)
  · have hXlt : Xr < X₀ := lt_of_not_ge hXlarge
    obtain ⟨qμ, aμ, mμ, hqμ, hqQμ, haμ, hmμ, hEqμ⟩ :=
      residuePrefixEnvelope_attained X H (fun n => (paperMu n : ℂ)) Q hQ
    obtain ⟨qΛ, aΛ, mΛ, hqΛ, hqQΛ, haΛ, hmΛ, hEqΛ⟩ :=
      residuePrefixEnvelope_attained X H
        (fun n => (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight Xr n : ℂ)) Q hQ
    have hMuSmall := (residuePrefixComponents_pointwiseBounds X mμ qμ aμ hX
      (le_trans hmμ hHleX)).1
    have hLambdaSmall := (residuePrefixComponents_pointwiseBounds X mΛ qΛ aΛ hX
      (le_trans hmΛ hHleX)).2
    have hlogle : ell ≤ Real.log X₀ := Real.log_le_log hXpos hXlt.le
    have hpowle : ell ^ (A + 1) ≤ (Real.log X₀) ^ (A + 1) :=
      Real.rpow_le_rpow hellpos.le hlogle (by linarith)
    have hidentity : ell ^ (-A) * ell ^ (A + 1) = ell := by
      calc
        ell ^ (-A) * ell ^ (A + 1) = ell ^ (-A + (A + 1)) :=
          (Real.rpow_add hellpos _ _).symm
        _ = ell := by rw [show -A + (A + 1) = 1 by ring, Real.rpow_one]
    have hMuEnv :
        residuePrefixEnvelope X H (fun n => (paperMu n : ℂ)) Q ≤ Hr * ell := by
      rw [hEqμ]
      exact (hMuSmall.trans (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hmμ) hellpos.le))
    have hLambdaEnv :
        residuePrefixEnvelope X H
            (fun n => (paperLambda n : ℂ) -
              (paperShortBlockCramerWeight Xr n : ℂ)) Q ≤
          (Real.exp 13 + 2) * Hr * ell := by
      rw [hEqΛ]
      calc
        ‖residuePrefixSum X mΛ qΛ aΛ
            (fun n => (paperLambda n : ℂ) -
              (paperShortBlockCramerWeight Xr n : ℂ))‖ ≤
          (Real.exp 13 + 2) * (mΛ : ℝ) * ell := hLambdaSmall
        _ ≤ (Real.exp 13 + 2) * Hr * ell := by
          have hmass := mul_le_mul_of_nonneg_left
            (Nat.cast_le.mpr hmΛ) (by positivity : 0 ≤ Real.exp 13 + 2)
          exact mul_le_mul_of_nonneg_right hmass hellpos.le
    have hsmallTotal :
        residuePrefixEnvelope X H (fun n => (paperMu n : ℂ)) Q +
          residuePrefixEnvelope X H
            (fun n => (paperLambda n : ℂ) -
              (paperShortBlockCramerWeight Xr n : ℂ)) Q ≤
          (Real.exp 13 + 3) * Hr * ell := by
      calc
        _ ≤ Hr * ell + (Real.exp 13 + 2) * Hr * ell :=
          add_le_add hMuEnv hLambdaEnv
        _ = (Real.exp 13 + 3) * Hr * ell := by ring
    calc
      residuePrefixEnvelope X H (fun n => (paperMu n : ℂ)) Q +
          residuePrefixEnvelope X H
            (fun n => (paperLambda n : ℂ) -
              (paperShortBlockCramerWeight Xr n : ℂ)) Q ≤
        (Real.exp 13 + 3) * Hr * ell := hsmallTotal
      _ = (Real.exp 13 + 3) * Hr * (ell ^ (-A) * ell ^ (A + 1)) := by
        rw [hidentity]
      _ ≤ (Real.exp 13 + 3) * Hr *
            (ell ^ (-A) * (Real.log X₀) ^ (A + 1)) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left hpowle
          exact Real.rpow_nonneg hellpos.le _
        · positivity
      _ = Csmall * Hr * ell ^ (-A) := by
        dsimp [Csmall]
        ring
      _ ≤ C * Hr * ell ^ (-A) := by
        have hsmallC : Csmall ≤ C := le_max_right Cmain Csmall
        have hHsmall : Csmall * Hr ≤ C * Hr :=
          mul_le_mul_of_nonneg_right hsmallC
            (by exact_mod_cast (Nat.cast_nonneg H))
        calc
          Csmall * Hr * ell ^ (-A) ≤ C * Hr * ell ^ (-A) :=
            mul_le_mul_of_nonneg_right hHsmall (Real.rpow_nonneg hellpos.le _)

#print axioms polynomialMajorArcTask_of_ordinaryFullResidueCancellation

#print axioms residuePrefixComponents_pointwiseBounds
#print axioms residuePrefixPair_pointwiseBound
#print axioms exists_log_rpow_le_rpow

end FractionalPrimes.Literature.Polynomial
