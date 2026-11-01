module
public import FractionalPrimes.ArithmeticShortRemainderOAIAdapter
@[expose] public section

/-!
# Finite small-scale closure for the arithmetic remainder

The checked conditional assembly in `ArithmeticShortRemainderAssembly` gives
the source estimate above an eventual threshold.  The approved blueprint
states it for every `K ≥ 3`, explicitly absorbing the finitely many smaller
scales into the constant.  This file carries out that elementary finite-scale
closure while retaining the exact DP and restricted-PTW premises.
-/

namespace FractionalPrimes

open scoped BigOperators
open FractionalPrimes.Literature.Polynomial

private noncomputable def shortRemainderSmallEnvelope (K : ℝ) : ℝ :=
  1 + Real.log (2 * K) + Real.exp ((Real.log (2 * K)) ^ (1 / 10 : ℝ))

/-- Uniform trivial bound for the exact full-block sums when the ambient scale
is at most `Ktop`.  The bound uses the source `μ` and `Λ−Cr_Xv` coefficients,
and counts the same half-open blocks as `ar:partition`. -/
private theorem shortRemainderSmallScaleTrivialBound {c : ℝ}
    (Ktop K K' : ℕ) (hK : 3 ≤ K) (hKK' : K ≤ K')
    (hK'2 : K' ≤ 2 * K) (hKtop : K ≤ Ktop) (ξ : ℝ) :
    let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
    let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
    (∑ v ∈ Finset.range q,
      ‖∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
        (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
          (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
        (K : ℝ) * shortRemainderSmallEnvelope (Ktop : ℝ) ∧
    (∑ v ∈ Finset.range q,
      ‖∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
        ((paperLambda (n : ℤ) -
          paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ)
            (n : ℤ) : ℝ) : ℂ) * unitFrequencyPhase
          (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
        (K : ℝ) * shortRemainderSmallEnvelope (Ktop : ℝ) := by
  classical
  dsimp only
  let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
  let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
  let Btop : ℝ := shortRemainderSmallEnvelope (Ktop : ℝ)
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKtopreal : (3 : ℝ) ≤ (Ktop : ℝ) := le_trans hKreal (by exact_mod_cast hKtop)
  have h2Ktoppos : 0 < 2 * (Ktop : ℝ) := by positivity
  have hlogtop : 0 ≤ Real.log (2 * (Ktop : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hBtoppos : 0 < Btop := by
    dsimp [Btop, shortRemainderSmallEnvelope]
    have he : 0 ≤ Real.exp ((Real.log (2 * (Ktop : ℝ))) ^ (1 / 10 : ℝ)) :=
      Real.exp_nonneg _
    linarith
  have hBtopone : 1 ≤ Btop := by
    dsimp [Btop, shortRemainderSmallEnvelope]
    have he : 0 ≤ Real.exp ((Real.log (2 * (Ktop : ℝ))) ^ (1 / 10 : ℝ)) :=
      Real.exp_nonneg _
    linarith
  by_cases hHpos : 0 < H
  · have hqeq : q = (K' - K) / H := by
      dsimp [q]
      exact natFloor_div_natCast_eq_div _ _
    have hqH : q * H ≤ K' - K := by
      rw [hqeq]
      exact Nat.div_mul_le_self _ _
    have hqK : q * H ≤ K := le_trans hqH (by omega)
    have hqKreal : (q : ℝ) * (H : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hqK
    have hblockX : ∀ v : ℕ, v < q →
        let Xv : ℕ := K + v * H
        Xv + H ≤ 2 * K := by
      intro v hv
      let Xv : ℕ := K + v * H
      have hstep : v * H + H ≤ q * H := by
        have h := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hv)
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using h
      have hXvH' : Xv + H = K + (v * H + H) := by
        dsimp [Xv]
        omega
      calc
        Xv + H = K + (v * H + H) := hXvH'
        _ ≤ K + q * H := Nat.add_le_add_left hstep K
        _ ≤ K + (K' - K) := Nat.add_le_add_left hqH K
        _ = K' := by omega
        _ ≤ 2 * K := hK'2
    have hMuBlock : ∀ v ∈ Finset.range q,
        ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H),
          (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
            (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
          (H : ℝ) * Btop := by
      intro v hv
      have hvlt : v < q := Finset.mem_range.mp hv
      let Xv : ℕ := K + v * H
      have hXvH := hblockX v hvlt
      have hXvK : K ≤ Xv := by dsimp [Xv]; omega
      have hnterm : ∀ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H),
          ‖(paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
            (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤ Btop := by
        intro n hn
        have hnI := Finset.mem_Ico.mp hn
        have hlo : K + 1 + v * H = Xv + 1 := by dsimp [Xv]; omega
        have hhi : K + 1 + (v + 1) * H = Xv + H + 1 := by
          dsimp [Xv]
          rw [Nat.succ_mul]
          omega
        rw [hlo, hhi] at hnI
        have hn3 : 3 ≤ n := by omega
        have hmu := paperMu_abs_le_one (n := (n : ℤ)) (by omega)
        have hmuR : |(paperMu (n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hmu
        have hmuC : ‖(paperMu (n : ℤ) : ℂ)‖ ≤ Btop := by
          have hmuC' : ‖(paperMu (n : ℤ) : ℂ)‖ ≤ 1 := by
            simpa only [Complex.norm_intCast] using hmuR
          exact hmuC'.trans (by linarith [hBtopone])
        rw [norm_mul, norm_unitFrequencyPhase, mul_one]
        exact hmuC
      have hcard :
          (Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H)).card = H := by
        rw [Nat.card_Ico]
        rw [Nat.succ_mul]
        omega
      calc
        _ ≤ ∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H), Btop := by
          calc
            _ ≤ ∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H),
                ‖(paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
                  (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ := norm_sum_le _ _
            _ ≤ _ := Finset.sum_le_sum (by
              intro n hn
              exact hnterm n hn)
        _ = (H : ℝ) * Btop := by
          simp [Finset.sum_const, nsmul_eq_mul, hcard]
    have hLambdaBlock : ∀ v ∈ Finset.range q,
        ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H),
          ((paperLambda (n : ℤ) -
            paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ)
              (n : ℤ) : ℝ) : ℂ) * unitFrequencyPhase
            (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
          (H : ℝ) * Btop := by
      intro v hv
      have hvlt : v < q := Finset.mem_range.mp hv
      let Xv : ℕ := K + v * H
      have hXvH := hblockX v hvlt
      have hXvK : K ≤ Xv := by dsimp [Xv]; omega
      have hXvTop : Xv ≤ 2 * Ktop := by omega
      have hXToptop : Xv + H ≤ 2 * Ktop := by omega
      have hXvreal : (3 : ℝ) ≤ (Xv : ℝ) := by
        exact_mod_cast (le_trans hK hXvK)
      have hlogBase : 0 < Real.log (Xv : ℝ) :=
        Real.log_pos (by linarith [hXvreal])
      have hlogBaseOne : 1 ≤ Real.log (Xv : ℝ) := by
        have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
        exact le_trans hlog3.le
          (Real.log_le_log (by norm_num) hXvreal)
      have hlogTop : Real.log (Xv : ℝ) ≤ Real.log (2 * (Ktop : ℝ)) :=
        Real.log_le_log (by linarith [hXvreal]) (by exact_mod_cast hXvTop)
      have hcutoff : 2 ≤ paperShortBlockCutoff (Xv : ℝ) := by
        have hpow : 1 ≤ (Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ) :=
          Real.one_le_rpow hlogBaseOne (by norm_num)
        dsimp [paperShortBlockCutoff]
        exact le_trans Real.exp_one_gt_two.le
          (Real.exp_le_exp.mpr hpow)
      have hdensity :=
        (paperCramerDensity_bounds hcutoff).2
      have hpowMono :
          (Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ) ≤
            (Real.log (2 * (Ktop : ℝ))) ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow hlogBase.le hlogTop (by norm_num)
      have hnterm : ∀ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H),
          ‖((paperLambda (n : ℤ) -
            paperShortBlockCramerWeight (Xv : ℝ) (n : ℤ) : ℝ) : ℂ) *
              unitFrequencyPhase
                (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤ Btop := by
        intro n hn
        have hnI := Finset.mem_Ico.mp hn
        have hlo : K + 1 + v * H = Xv + 1 := by dsimp [Xv]; omega
        have hhi : K + 1 + (v + 1) * H = Xv + H + 1 := by
          dsimp [Xv]
          rw [Nat.succ_mul]
          omega
        rw [hlo, hhi] at hnI
        have hn3 : 3 ≤ n := by omega
        have hnTop : n ≤ 2 * Ktop := le_trans (by omega) hXToptop
        have hnRealPos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hnRealTop : (n : ℝ) ≤ 2 * (Ktop : ℝ) := by
          exact_mod_cast hnTop
        have hlambdaBounds :=
          paperLambda_bounds (n := (n : ℤ)) (by omega)
        have hlogn : Real.log (n : ℝ) ≤ Real.log (2 * (Ktop : ℝ)) :=
          Real.log_le_log hnRealPos hnRealTop
        have hlambdaAbs : |paperLambda (n : ℤ)| ≤
            Real.log (2 * (Ktop : ℝ)) := by
          rw [abs_of_nonneg hlambdaBounds.1]
          exact hlambdaBounds.2.trans hlogn
        have hcramerAbs :
            |paperShortBlockCramerWeight (Xv : ℝ) (n : ℤ)| ≤
              Real.exp ((Real.log (2 * (Ktop : ℝ))) ^ (1 / 10 : ℝ)) := by
          calc
            _ ≤ paperCramerDensity
                (paperShortBlockCutoff (Xv : ℝ)) :=
              FractionalPrimes.Literature.Uniformity.cramerWeight_abs_le_density
                (Xv : ℝ) (n : ℤ)
            _ ≤ paperShortBlockCutoff (Xv : ℝ) := hdensity
            _ ≤ Real.exp ((Real.log (2 * (Ktop : ℝ))) ^ (1 / 10 : ℝ)) := by
              dsimp [paperShortBlockCutoff]
              exact Real.exp_le_exp.mpr hpowMono
        have habs :
            |paperLambda (n : ℤ) -
              paperShortBlockCramerWeight (Xv : ℝ) (n : ℤ)| ≤
              Real.log (2 * (Ktop : ℝ)) +
                Real.exp ((Real.log (2 * (Ktop : ℝ))) ^ (1 / 10 : ℝ)) :=
          (abs_sub _ _).trans (add_le_add hlambdaAbs hcramerAbs)
        rw [norm_mul, norm_unitFrequencyPhase, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
        exact habs.trans (by dsimp [Btop, shortRemainderSmallEnvelope]; linarith)
      have hcard :
          (Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H)).card = H := by
        rw [Nat.card_Ico]
        rw [Nat.succ_mul]
        omega
      calc
        _ ≤ ∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H), Btop := by
          calc
            _ ≤ ∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H),
                ‖((paperLambda (n : ℤ) -
                  paperShortBlockCramerWeight (Xv : ℝ) (n : ℤ) : ℝ) : ℂ) *
                  unitFrequencyPhase
                    (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ := norm_sum_le _ _
            _ ≤ _ := Finset.sum_le_sum (by
              intro n hn
              exact hnterm n hn)
        _ = (H : ℝ) * Btop := by
          simp [Finset.sum_const, nsmul_eq_mul, hcard]
    constructor
    · calc
        _ ≤ ∑ v ∈ Finset.range q, (H : ℝ) * Btop :=
          Finset.sum_le_sum hMuBlock
        _ = (q : ℝ) * (H : ℝ) * Btop := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
        _ ≤ (K : ℝ) * Btop :=
          mul_le_mul_of_nonneg_right hqKreal (le_of_lt hBtoppos)
    · calc
        _ ≤ ∑ v ∈ Finset.range q, (H : ℝ) * Btop :=
          Finset.sum_le_sum hLambdaBlock
        _ = (q : ℝ) * (H : ℝ) * Btop := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
        _ ≤ (K : ℝ) * Btop :=
          mul_le_mul_of_nonneg_right hqKreal (le_of_lt hBtoppos)
  · have hHzero : H = 0 := by omega
    simp [H, hHzero]
    exact mul_nonneg (by positivity) (le_of_lt hBtoppos)

/-- The exact all-`K ≥ 3` short-remainder conclusion of `ar:short-remainder`,
conditional only on the still-explicit scalar DP and restricted PTW inputs.
The checked OAI E1 route supplies MUF; the eventual estimate is extended to
the finitely many smaller `K` by the source's stated constant enlargement. -/
theorem arithmeticShortRemainderAllScalesOf_OAISource_DP_PTW {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ K K' : ℕ, 3 ≤ K → K ≤ K' → K' ≤ 2 * K →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
        let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
        (∑ v ∈ Finset.range q,
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H),
            (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
          C * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) ∧
        (∑ v ∈ Finset.range q,
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H),
            ((paperLambda (n : ℤ) -
              paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ)
                (n : ℤ) : ℝ) : ℂ) * unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
          C * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
  classical
  obtain ⟨Clarge, hClarge, K₀, hK₀, hlarge⟩ :=
    arithmeticShortRemainderOf_OAISource_DP_PTW hc hcNon hDP hPTW A hA
  let Btop : ℝ := shortRemainderSmallEnvelope (K₀ : ℝ)
  let Csmall : ℝ := Btop * (Real.log (K₀ : ℝ)) ^ A
  let C : ℝ := Clarge + Csmall
  have hK₀real : (3 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
  have hlogK₀ : 0 < Real.log (K₀ : ℝ) := Real.log_pos (by linarith)
  have hBtop : 0 < Btop := by
    dsimp [Btop, shortRemainderSmallEnvelope]
    have hlog : 0 ≤ Real.log (2 * (K₀ : ℝ)) :=
      Real.log_nonneg (by linarith)
    have he : 0 ≤ Real.exp ((Real.log (2 * (K₀ : ℝ))) ^ (1 / 10 : ℝ)) :=
      Real.exp_nonneg _
    linarith
  have hCsmall : 0 < Csmall := by
    dsimp [Csmall]
    positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro K K' hK hKK' hK'2 ξ hξlo hξhi
  dsimp only
  let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
  let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
  by_cases hlargeK : K₀ ≤ K
  · have hlargeAt := hlarge K K' hlargeK hKK' hK'2 ξ hξlo hξhi
    dsimp only at hlargeAt
    rcases hlargeAt with ⟨hMu, hLambda⟩
    have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hlogKpos : 0 < Real.log (K : ℝ) := Real.log_pos (by linarith [hKreal])
    have hfactor : 0 ≤ (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg hlogKpos.le _)
    have hClargeC : Clarge ≤ C := by dsimp [C]; linarith [hCsmall]
    have hlargeFactor :
        Clarge * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) ≤
          C * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      calc
        _ = Clarge * ((K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ)) := by ring
        _ ≤ C * ((K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ)) :=
          mul_le_mul_of_nonneg_right hClargeC hfactor
        _ = _ := by ring
    constructor
    · exact hMu.trans hlargeFactor
    · exact hLambda.trans hlargeFactor
  · have hKlt : K < K₀ := by omega
    have hKleK₀ : K ≤ K₀ := hKlt.le
    have hsmall := shortRemainderSmallScaleTrivialBound
      (c := c) K₀ K K' hK hKK' hK'2 hKleK₀ ξ
    dsimp only at hsmall
    have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hlogKpos : 0 < Real.log (K : ℝ) := Real.log_pos (by linarith [hKreal])
    have hlogK₀pos : 0 < Real.log (K₀ : ℝ) := hlogK₀
    have hlogle : Real.log (K : ℝ) ≤ Real.log (K₀ : ℝ) :=
      Real.log_le_log (by linarith [hKreal]) (by exact_mod_cast hKleK₀)
    have hpowle : (Real.log (K : ℝ)) ^ A ≤ (Real.log (K₀ : ℝ)) ^ A :=
      Real.rpow_le_rpow hlogKpos.le hlogle hA.le
    have hratio :
        1 ≤ (Real.log (K₀ : ℝ)) ^ A * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      rw [Real.rpow_neg hlogKpos.le]
      have hinv : 0 ≤ ((Real.log (K : ℝ)) ^ A)⁻¹ :=
        inv_nonneg.mpr (Real.rpow_nonneg hlogKpos.le A)
      calc
        1 = (Real.log (K : ℝ)) ^ A * ((Real.log (K : ℝ)) ^ A)⁻¹ := by
          field_simp
        _ ≤ (Real.log (K₀ : ℝ)) ^ A * ((Real.log (K : ℝ)) ^ A)⁻¹ :=
          mul_le_mul_of_nonneg_right hpowle hinv
    have hBtopRatio : Btop ≤ Csmall * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      calc
        Btop = Btop * 1 := by ring
        _ ≤ Btop * ((Real.log (K₀ : ℝ)) ^ A *
              (Real.log (K : ℝ)) ^ (-A : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio (le_of_lt hBtop)
        _ = Csmall * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
          dsimp [Csmall]
          ring
    have hpowNonneg : 0 ≤ (Real.log (K : ℝ)) ^ (-A : ℝ) :=
      Real.rpow_nonneg hlogKpos.le _
    have hCsmallC : Csmall ≤ C := by dsimp [C]; linarith [hClarge]
    have hBtoC : Btop ≤ C * (Real.log (K : ℝ)) ^ (-A : ℝ) :=
      hBtopRatio.trans (mul_le_mul_of_nonneg_right hCsmallC hpowNonneg)
    have hKreal : 0 ≤ (K : ℝ) := by positivity
    have hfinalFactor :
        (K : ℝ) * Btop ≤ C * (K : ℝ) *
          (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      calc
        _ ≤ (K : ℝ) * (C * (Real.log (K : ℝ)) ^ (-A : ℝ)) :=
          mul_le_mul_of_nonneg_left hBtoC hKreal
        _ = C * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by ring
    rcases hsmall with ⟨hMu, hLambda⟩
    exact ⟨hMu.trans hfinalFactor, hLambda.trans hfinalFactor⟩

end FractionalPrimes

#print axioms FractionalPrimes.arithmeticShortRemainderAllScalesOf_OAISource_DP_PTW
