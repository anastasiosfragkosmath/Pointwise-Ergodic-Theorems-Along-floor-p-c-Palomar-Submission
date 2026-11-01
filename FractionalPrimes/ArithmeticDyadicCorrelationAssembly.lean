module
public import FractionalPrimes.ArithmeticShortRemainderAllScales
public import FractionalPrimes.CramerBlockCorrelation
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalSourceCorrelationBound
public import FractionalPrimes.Chebyshev
@[expose] public section

/-!
# Dyadic arithmetic correlation assembly (`ar:dyadic-correlation`)

This file combines the all-scale conditional short-remainder estimate with
the checked single-block Cramér estimate, and handles the terminal interval
left by the source partition.  The scalar Dirichlet and restricted PTW tasks
remain explicit inputs through the short-remainder theorem.
-/

set_option maxHeartbeats 5000000

namespace FractionalPrimes

open scoped BigOperators
open FractionalPrimes.Literature.Polynomial

private theorem exists_log_le_rpow_at_two_mul {s : ℝ} (hs : 0 < s) :
    ∃ K₀ : ℝ, 3 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      Real.log (2 * K) ≤ (2 * K) ^ s := by
  have hlittle := (paper_log_rpow_isLittleO_rpow (a := 1) hs).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hlittle
  let K₀ : ℝ := max 3 (B / 2)
  refine ⟨K₀, le_max_left _ _, ?_⟩
  intro K hK
  have hK3 : 3 ≤ K := le_trans (le_max_left _ _) hK
  have hBK : B ≤ 2 * K := by
    have hBK2 : B / 2 ≤ K := le_trans (le_max_right _ _) hK
    linarith
  have hbound := hB (2 * K) hBK
  have hlog : 0 ≤ Real.log (2 * K) := Real.log_nonneg (by linarith)
  have hpow : 0 ≤ (2 * K) ^ s := Real.rpow_nonneg (by positivity) s
  have hbound' : Real.log (2 * K) ≤ (2 * K) ^ s := by
    have h' : ‖Real.log (2 * K)‖ ≤ ‖(2 * K) ^ s‖ := by
      simpa [Real.rpow_one] using hbound
    rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hpow] at h'
    exact h'
  exact hbound'

private theorem exists_exp_log_rpow_le_rpow_at_two_mul
    {ρ s : ℝ} (hρ : 0 < ρ) (hρlt : ρ < 1) (hs : 0 < s) :
    ∃ K₀ : ℝ, 3 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      Real.exp ((Real.log (2 * K)) ^ ρ) ≤ (2 * K) ^ s := by
  have hlittle := (paper_exp_log_rpow_isLittleO_rpow
    (ρ := ρ) (b := s) hρ hρlt hs).bound
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hlittle
  let K₀ : ℝ := max 3 (B / 2)
  refine ⟨K₀, le_max_left _ _, ?_⟩
  intro K hK
  have hK3 : 3 ≤ K := le_trans (le_max_left _ _) hK
  have hBK : B ≤ 2 * K := by
    have hBK2 : B / 2 ≤ K := le_trans (le_max_right _ _) hK
    linarith
  have hbound := hB (2 * K) hBK
  have hlog : 0 ≤ Real.log (2 * K) := Real.log_nonneg (by linarith)
  have hleft : 0 ≤ Real.exp ((Real.log (2 * K)) ^ ρ) := Real.exp_nonneg _
  have hright : 0 ≤ (2 * K) ^ s := Real.rpow_nonneg (by positivity) s
  have hbound' : Real.exp ((Real.log (2 * K)) ^ ρ) ≤ (2 * K) ^ s := by
    have h' :
        ‖Real.exp ((Real.log (2 * K)) ^ ρ)‖ ≤ ‖(2 * K) ^ s‖ := by
      simpa using hbound
    rw [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright] at h'
    exact h'
  exact hbound'

private theorem exists_exp_fifth_log_decay_le_log_rpow {A : ℝ} (hA : 0 < A) :
    ∃ K₀ : ℝ, 3 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      Real.exp (-((Real.log K) ^ (1 / 5 : ℝ))) ≤
        (Real.log K) ^ (-A : ℝ) := by
  let N : ℕ := Nat.ceil (5 * A) + 1
  have hN : 5 * A ≤ (N : ℝ) := by
    dsimp [N]
    have hceil := Nat.le_ceil (5 * A)
    exact_mod_cast (show 5 * A ≤ (Nat.ceil (5 * A) : ℝ) + 1 by linarith)
  have hlim : Filter.Tendsto
      (fun t : ℝ => t ^ N * Real.exp (-t)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hsmall : ∀ᶠ t : ℝ in Filter.atTop,
      t ^ N * Real.exp (-t) ≤ 1 := by
    filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht
    exact ht.le
  have htend : Filter.Tendsto
      (fun K : ℝ => (Real.log K) ^ (1 / 5 : ℝ)) Filter.atTop Filter.atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      Real.tendsto_log_atTop
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hsmall
  have hTcomp : ∀ᶠ K : ℝ in Filter.atTop,
      T ≤ (Real.log K) ^ (1 / 5 : ℝ) :=
    htend.eventually (Filter.eventually_ge_atTop T)
  have hsmallK : ∀ᶠ K : ℝ in Filter.atTop,
      ((Real.log K) ^ (1 / 5 : ℝ)) ^ N *
        Real.exp (-((Real.log K) ^ (1 / 5 : ℝ))) ≤ 1 := by
    filter_upwards [hTcomp] with K hTK
    exact hT _ hTK
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hsmallK
  let K₀ : ℝ := max 3 B
  refine ⟨K₀, le_max_left _ _, ?_⟩
  intro K hK
  have hK3 : 3 ≤ K := le_trans (le_max_left _ _) hK
  have hB' : B ≤ K := le_trans (le_max_right _ _) hK
  let L : ℝ := Real.log K
  let t : ℝ := L ^ (1 / 5 : ℝ)
  have hlogpos : 0 < L := by dsimp [L]; exact Real.log_pos (by linarith [hK3])
  have hlogone : 1 ≤ L := by
    have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
    dsimp [L]
    exact le_trans hlog3.le (Real.log_le_log (by norm_num) hK3)
  have htge : 1 ≤ t := by
    dsimp [t]
    exact Real.one_le_rpow hlogone (by norm_num)
  have hteq : t ^ (5 * A) = L ^ A := by
    dsimp [t]
    rw [← Real.rpow_mul hlogpos.le (1 / 5 : ℝ) (5 * A)]
    congr 1
    ring
  have htN : t ^ (5 * A) ≤ t ^ (N : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hN
  have hsmallAt := hB K hB'
  have hsmallAt' :
      ((Real.log K) ^ (1 / 5 : ℝ)) ^ (N : ℝ) *
        Real.exp (-((Real.log K) ^ (1 / 5 : ℝ))) ≤ 1 := by
    simpa only [Real.rpow_natCast] using hsmallAt
  have hprod : (Real.log K) ^ A *
      Real.exp (-((Real.log K) ^ (1 / 5 : ℝ))) ≤ 1 := by
    calc
      _ = ((Real.log K) ^ (1 / 5 : ℝ)) ^ (5 * A) *
          Real.exp (-((Real.log K) ^ (1 / 5 : ℝ))) := by rw [hteq]
      _ ≤ ((Real.log K) ^ (1 / 5 : ℝ)) ^ (N : ℝ) *
          Real.exp (-((Real.log K) ^ (1 / 5 : ℝ))) := by
        exact mul_le_mul_of_nonneg_right htN (Real.exp_nonneg _)
      _ ≤ 1 := hsmallAt'
  have hpowpos : 0 < (Real.log K) ^ A := Real.rpow_pos_of_pos hlogpos A
  have htarget : Real.exp (-((Real.log K) ^ (1 / 5 : ℝ))) ≤
      ((Real.log K) ^ A)⁻¹ := by
    calc
      _ = (Real.exp (-((Real.log K) ^ (1 / 5 : ℝ))) *
          (Real.log K) ^ A) * ((Real.log K) ^ A)⁻¹ := by
        field_simp
      _ ≤ 1 * ((Real.log K) ^ A)⁻¹ :=
        mul_le_mul_of_nonneg_right (by simpa [mul_comm] using hprod)
          (inv_nonneg.mpr hpowpos.le)
      _ = ((Real.log K) ^ A)⁻¹ := by ring
  rw [Real.rpow_neg hlogpos.le]
  exact htarget

private theorem exists_rpow_decay_beats_log_power {A γ : ℝ}
    (hγ : 0 < γ) :
    ∃ K₀ : ℝ, 3 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      K ^ (1 - γ) ≤ K * (Real.log K) ^ (-A : ℝ) := by
  have hlittle := (paper_log_rpow_isLittleO_rpow
    (a := A) (b := γ / 2) (by linarith)).bound
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hlittle
  let K₀ : ℝ := max 3 B
  refine ⟨K₀, le_max_left _ _, ?_⟩
  intro K hK
  have hK3 : 3 ≤ K := le_trans (le_max_left _ _) hK
  have hBK : B ≤ K := le_trans (le_max_right _ _) hK
  have hKpos : 0 < K := by linarith
  have hlogpos : 0 < Real.log K := Real.log_pos (by linarith)
  have hlogge1 : 1 ≤ Real.log K := by
    have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
    exact le_trans hlog3.le (Real.log_le_log (by norm_num) hK3)
  have hbound := hB K hBK
  have hbound' : (Real.log K) ^ A ≤ K ^ (γ / 2) := by
    have h' : ‖(Real.log K) ^ A‖ ≤ ‖K ^ (γ / 2)‖ := by
      simpa [Real.rpow_one] using hbound
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hKpos.le _)] at h'
    exact h'
  have hinv : (K ^ (γ / 2))⁻¹ ≤ ((Real.log K) ^ A)⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos hKpos (γ / 2))
      (Real.rpow_pos_of_pos hlogpos A)).2 hbound'
  have hKinv : K ^ (-(γ / 2)) = (K ^ (γ / 2))⁻¹ := by
    rw [Real.rpow_neg hKpos.le]
  have hloginv : (Real.log K) ^ (-A) = ((Real.log K) ^ A)⁻¹ := by
    rw [Real.rpow_neg hlogpos.le]
  have hsmall : K ^ (-(γ / 2)) ≤ (Real.log K) ^ (-A : ℝ) := by
    rw [hKinv, hloginv]
    exact hinv
  have hexp : -γ ≤ -(γ / 2) := by linarith
  have hdecay : K ^ (-γ) ≤ K ^ (-(γ / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
  have hKdecay : K ^ (-γ) ≤ (Real.log K) ^ (-A : ℝ) := hdecay.trans hsmall
  calc
    K ^ (1 - γ) = K * K ^ (-γ) := by
      rw [show 1 - γ = 1 + (-γ) by ring, Real.rpow_add hKpos]
      simp [Real.rpow_one]
    _ ≤ K * (Real.log K) ^ (-A : ℝ) :=
      mul_le_mul_of_nonneg_left hKdecay hKpos.le

end FractionalPrimes

namespace FractionalPrimes

open FractionalPrimes.Literature.Polynomial

private theorem natIoc_eq_natIco_succ (a b : ℕ) :
    Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

private theorem shortBlockIco_eq (K H v : ℕ) :
    Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H) =
      Finset.Ico (K + v * H + 1) (K + v * H + H + 1) := by
  have hlo : K + 1 + v * H = K + v * H + 1 := by omega
  have hhi : K + 1 + (v + 1) * H = K + v * H + H + 1 := by
    rw [Nat.succ_mul]
    omega
  rw [hlo, hhi]

private theorem shortBlockRealInterval_sum_eq_natIco
    {M : Type*} [AddCommMonoid M] (K H v : ℕ) (f : ℤ → M) :
    (∑ n ∈ realIntegerInterval ((K + v * H : ℕ) : ℝ) (H : ℝ), f n) =
      ∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
        f (n : ℤ) := by
  calc
    _ = ∑ n ∈ Finset.Ico (K + v * H + 1) (K + v * H + H + 1),
        f (n : ℤ) := by
      rw [FractionalPrimes.Literature.Polynomial.realIntegerInterval_sum_eq_nat_Ioc]
      rw [natIoc_eq_natIco_succ]
    _ = _ := by rw [← shortBlockIco_eq K H v]

/-- The exact dyadic cancellation proposition from the approved blueprint,
conditional on the source Dirichlet task and restricted polynomial PTW task.
The OAI E1 route supplies Möbius uniformity inside the all-scale
short-remainder estimate. -/
theorem dyadicArithmeticCorrelationOf_OAISource_DP_PTW {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ K K' : ℕ, 3 ≤ K → K ≤ K' → K' ≤ 2 * K →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖∑ n ∈ Finset.Ioc K K',
            ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
              unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ +
        ‖∑ n ∈ Finset.Ioc K K',
            (paperMu (n : ℤ) : ℂ) *
              unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
          C * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
  classical
  let p := arithmeticParameters c
  let θ : ℝ := p.θ
  let δ : ℝ := p.δ
  let s : ℝ := δ / 64
  let γ : ℝ := δ / 16
  obtain ⟨Cshort, hCshort, hshort⟩ :=
    arithmeticShortRemainderAllScalesOf_OAISource_DP_PTW hc hcNon
      hDP hPTW (A + 1) (by linarith)
  obtain ⟨Cc, hCc, hcramer⟩ := cramerBlockCorrelation hc hcNon
  dsimp only at hcramer
  obtain ⟨Kpart, hKpart, hpartition⟩ :=
    exists_arithmetic_shortBlock_partition hc
  obtain ⟨Kfloor, hfloor⟩ :=
    exists_natFloor_rpow_block_threshold (arithmeticParameters_theta_pos hc)
  obtain ⟨Kexp, hKexp, hexpSub⟩ :=
    exists_exp_log_rpow_le_rpow_at_two_mul
      (ρ := 3 / 10) (s := s) (by norm_num) (by norm_num) (by
        dsimp [s, δ, p, arithmeticParameters]
        positivity)
  obtain ⟨Klog, hKlog, hlogSub⟩ :=
    exists_log_le_rpow_at_two_mul (s := s) (by
      dsimp [s, δ, p, arithmeticParameters]
      positivity)
  obtain ⟨Kdecay, hKdecay, hdecay⟩ :=
    exists_exp_fifth_log_decay_le_log_rpow hA
  have hδpos : 0 < δ := by
    have hη := arithmeticParameters_eta_pos_lt_one hc
    dsimp only at hη
    change 0 < (arithmeticParameters c).η / 4
    exact div_pos hη.1 (by norm_num)
  have hδlt : δ < 1 := by
    have hη := arithmeticParameters_eta_pos_lt_one hc
    dsimp only at hη
    change (arithmeticParameters c).η / 4 < 1
    linarith [hη.2]
  have hγpos : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨Kpower, hKpower, hpower⟩ :=
    exists_rpow_decay_beats_log_power (A := A) (γ := γ) hγpos
  let Kinner : ℝ := max (Kpart : ℝ) (max (Kfloor : ℝ)
      (max Kexp (max Klog (max Kdecay Kpower))))
  let Kbig : ℝ := max 3 Kinner
  have hKbig3 : 3 ≤ Kbig := by dsimp [Kbig]; exact le_max_left _ _
  let Csmall : ℝ := (2 + Real.log (2 * Kbig)) * (Real.log Kbig) ^ A
  let Cpower : ℝ := Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) +
    3 * (2 : ℝ) ^ s
  let C : ℝ := 2 * Cshort + Cc + Cpower + Csmall
  have hKbigLog : 0 < Real.log Kbig := Real.log_pos (by linarith [hKbig3])
  have hCsmall : 0 < Csmall := by
    dsimp [Csmall]
    have hlog2 : 0 ≤ Real.log (2 * Kbig) := Real.log_nonneg (by linarith)
    positivity
  have hCpower : 0 ≤ Cpower := by
    dsimp [Cpower]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    linarith [hCshort, hCsmall, hCc]
  refine ⟨C, hC, ?_⟩
  intro K K' hK hKK' hK'2 ξ hξlo hξhi
  have hKreal : 3 ≤ (K : ℝ) := by exact_mod_cast hK
  have hKlogpos : 0 < Real.log (K : ℝ) := Real.log_pos (by linarith)
  have hKlogone : 1 ≤ Real.log (K : ℝ) := by
    have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
    exact le_trans hlog3.le (Real.log_le_log (by norm_num) hKreal)
  by_cases hlarge : Kbig ≤ (K : ℝ)
  · -- Large scales: use the source partition, short-remainder estimate,
    -- Cramér block estimate, and the explicit terminal interval.
    let H : ℕ := Nat.floor ((K : ℝ) ^ θ)
    let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
    let r : ℕ := (K' - K) % H
    have hKinner : Kinner ≤ (K : ℝ) := by
      change max 3 Kinner ≤ (K : ℝ) at hlarge
      exact (le_max_right 3 Kinner).trans hlarge
    have hKpartR : (Kpart : ℝ) ≤ (K : ℝ) := by
      exact (le_max_left _ _).trans hKinner
    have hKfloorR : (Kfloor : ℝ) ≤ (K : ℝ) := by
      have hrest : max (Kfloor : ℝ)
          (max Kexp (max Klog (max Kdecay Kpower))) ≤ Kinner :=
        le_max_right _ _
      exact (le_max_left _ _).trans (hrest.trans hKinner)
    have hKpartNat : Kpart ≤ K := by exact_mod_cast hKpartR
    have hKfloorNat : Kfloor ≤ K := by exact_mod_cast hKfloorR
    have hHfloor := hfloor K hKfloorNat
    have hHpos : 0 < H := by simpa [H, θ, p] using hHfloor.1
    have hHlower : (K : ℝ) ^ θ / 2 ≤ (H : ℝ) := by
      simpa [H, θ, p] using hHfloor.2.1
    have hHupper : (H : ℝ) ≤ (K : ℝ) ^ θ := by
      simpa [H, θ, p] using hHfloor.2.2
    have hdata := hpartition K hKpartNat K' hKK' hK'2
    dsimp only [H, q, r] at hdata
    rcases hdata with ⟨hdecomp, _hdisj, hremCard, hrlt, hqbound, hblocks⟩
    have hqeq : q = (K' - K) / H := by
      dsimp [q]
      exact natFloor_div_natCast_eq_div _ _
    have hqH : q * H ≤ K' - K := by
      rw [hqeq]
      exact Nat.div_mul_le_self _ _
    have hqHle : q * H ≤ K := by omega
    have hqr := natFloor_intervalQuotient_decomposition hKK' hHpos
    dsimp only [q, r] at hqr
    rcases hqr with ⟨hK'eq, hrlt'⟩
    have hshortAt := hshort K K' hK hKK' hK'2 ξ hξlo hξhi
    dsimp only [H, q] at hshortAt
    rcases hshortAt with ⟨hshortMu, hshortLambda⟩
    let L : ℝ := Real.log (K : ℝ)
    let E0 : ℝ := Real.exp (-(L ^ (1 / 5 : ℝ)))
    let Rsub : ℝ := (2 * (K : ℝ)) ^ s
    have hL : 1 ≤ L := by simpa [L] using hKlogone
    have hKexpThreshold : Kexp ≤ (K : ℝ) := by
      exact (le_max_left _ _).trans <| (le_max_right _ _).trans <|
        (le_max_right _ _).trans hKinner
    have hKlogThreshold : Klog ≤ (K : ℝ) := by
      exact (le_max_left _ _).trans <| (le_max_right _ _).trans <|
        (le_max_right _ _).trans <| (le_max_right _ _).trans hKinner
    have hKdecayThreshold : Kdecay ≤ (K : ℝ) := by
      exact (le_max_left _ _).trans <| (le_max_right _ _).trans <|
        (le_max_right _ _).trans <| (le_max_right _ _).trans <|
          (le_max_right _ _).trans hKinner
    have hKpowerThreshold : Kpower ≤ (K : ℝ) := by
      exact (le_max_right _ _).trans <| (le_max_right _ _).trans <|
        (le_max_right _ _).trans <| (le_max_right _ _).trans <|
          (le_max_right _ _).trans hKinner
    have hExpAtK := hexpSub (K : ℝ) hKexpThreshold
    have hLogAtK := hlogSub (K : ℝ) hKlogThreshold
    have hDecayAtK := hdecay (K : ℝ) hKdecayThreshold
    have hPowerAtK := hpower (K : ℝ) hKpowerThreshold
    have hthetaDelta : 1 - θ = δ / 4 := by
      dsimp [θ, δ, p, arithmeticParameters]
      ring
    have hcrDelta :
        ((1 / 100 : ℝ) /
          (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4 = δ := by
      rw [Real.rpow_natCast]
      norm_num [δ, p, arithmeticParameters, Nat.cast_pow]
    have hqbound' : (q : ℝ) ≤ 2 * (K : ℝ) ^ (δ / 4) := by
      calc
        (q : ℝ) ≤ 2 * (K : ℝ) ^ (1 - θ) := by
          simpa [q, θ, p] using hqbound
        _ = 2 * (K : ℝ) ^ (δ / 4) := by rw [hthetaDelta]
    have hqHreal : (q : ℝ) * (H : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hqHle
    have hRsubPos : 0 < Rsub := by dsimp [Rsub]; positivity
    have hRsubOne : 1 ≤ Rsub := by
      dsimp [Rsub]
      have hbase : (1 : ℝ) ≤ 2 * (K : ℝ) := by nlinarith [hKreal]
      exact Real.one_le_rpow hbase
        (by positivity)
    have hLogAtK2 : Real.log (2 * (K : ℝ)) ≤ Rsub := by
      simpa [Rsub] using hLogAtK
    have hExpAtK2 : Real.exp ((Real.log (2 * (K : ℝ)) ^ (3 / 10 : ℝ))) ≤ Rsub := by
      simpa [Rsub] using hExpAtK
    have hDecayFactor : E0 ≤ L ^ (-A : ℝ) := by
      simpa [E0, L] using hDecayAtK
    have hlogshort : (Real.log (K : ℝ)) ^ (-(A + 1 : ℝ)) ≤
        (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hKlogone (by linarith)
    have hShortFactor :
        Cshort * (K : ℝ) * (Real.log (K : ℝ)) ^ (-(A + 1 : ℝ)) ≤
          Cshort * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      exact mul_le_mul_of_nonneg_left hlogshort (by positivity)

    -- The blockwise Cramér bound is first put into a common form using
    -- monotonicity of the two logarithmic cutoffs and the density estimate.
    have hCramerBlocks :
        (∑ v ∈ Finset.range q,
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
            ((paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ) (n : ℤ) - 1 : ℝ) : ℂ) *
              unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
          Cc * (K : ℝ) * E0 +
            Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) * (K : ℝ) ^ (1 - γ) := by
      have hKge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
      have hExp2 : δ / 4 + 2 * s ≤ 1 - γ := by
        dsimp [s, γ]
        nlinarith [hδlt]
      have hExp3 : 1 - δ + δ / 4 + 2 * s ≤ 1 - γ := by
        dsimp [s, γ]
        nlinarith [hδpos]
      have hExp4 : 1 - δ + δ / 4 ≤ 1 - γ := by
        dsimp [γ]
        nlinarith [hδpos]
      have hExpRsub : 2 * s ≤ 1 - γ := by
        dsimp [s, γ]
        nlinarith [hδpos, hδlt]
      have hExpRsubK : 1 - δ + 2 * s ≤ 1 - γ := by
        dsimp [s, γ]
        nlinarith [hδpos]
      have hExpKpow : 1 - δ ≤ 1 - γ := by
        dsimp [γ]
        nlinarith [hδpos]
      have hRsubSq : Rsub ^ 2 =
          (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (2 * s) := by
        dsimp [Rsub]
        calc
          ((2 * (K : ℝ)) ^ s) ^ 2 =
              (2 * (K : ℝ)) ^ s * (2 * (K : ℝ)) ^ s := by rw [pow_two]
          _ =
              (2 * (K : ℝ)) ^ (s + s) := by
            rw [← Real.rpow_add (by positivity : 0 < 2 * (K : ℝ))]
          _ = (2 : ℝ) ^ (s + s) * (K : ℝ) ^ (s + s) :=
            Real.mul_rpow (by norm_num) (by positivity)
          _ = (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (2 * s) := by
            congr 2 <;> ring
      have hRsub2 :
          Rsub ^ 2 ≤ (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - γ) := by
        rw [hRsubSq]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hKge1 hExpRsub) (by positivity)
      have hRsub2K :
          Rsub ^ 2 * (K : ℝ) ^ (1 - δ) ≤
            (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - γ) := by
        rw [hRsubSq]
        calc
          _ = (2 : ℝ) ^ (2 * s) *
              ((K : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - δ)) := by ring
          _ = (2 : ℝ) ^ (2 * s) *
              (K : ℝ) ^ (2 * s + (1 - δ)) := by
            rw [← Real.rpow_add (by positivity : 0 < (K : ℝ))]
          _ = (2 : ℝ) ^ (2 * s) *
              (K : ℝ) ^ (1 - δ + 2 * s) := by
            congr 2 <;> ring
          _ ≤ (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - γ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hKge1 hExpRsubK) (by positivity)
      have hKpow :
          (K : ℝ) ^ (1 - δ) ≤ (K : ℝ) ^ (1 - γ) :=
        Real.rpow_le_rpow_of_exponent_le hKge1 hExpKpow
      have hCrEach : ∀ v ∈ Finset.range q,
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
            ((paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ)
              (n : ℤ) - 1 : ℝ) : ℂ) *
              unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
            Cc * ((H : ℝ) * E0 + Rsub ^ 2 +
              2 * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
              (K : ℝ) ^ (1 - δ)) := by
        intro v hv
        have hvlt : v < q := Finset.mem_range.mp hv
        let Xv : ℕ := K + v * H
        have hstep : (v + 1) * H ≤ q * H :=
          Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hvlt)
        have hXvH : Xv + H ≤ 2 * K := by
          have hXvH' : Xv + H = K + (v + 1) * H := by
            dsimp [Xv]
            rw [Nat.succ_mul]
            omega
          calc
            Xv + H = K + (v + 1) * H := hXvH'
            _ ≤ K + q * H := Nat.add_le_add_left hstep K
            _ ≤ K + (K' - K) := Nat.add_le_add_left hqH K
            _ = K' := by omega
            _ ≤ 2 * K := hK'2
        have hXvK : K ≤ Xv := by dsimp [Xv]; omega
        have hXv3 : 3 ≤ Xv := le_trans hK hXvK
        have hXvTop : Xv ≤ 2 * K := le_trans (Nat.le_add_right Xv H) hXvH
        have hXvReal : (3 : ℝ) ≤ (Xv : ℝ) := by exact_mod_cast hXv3
        have hXvRealK : (K : ℝ) ≤ (Xv : ℝ) := by exact_mod_cast hXvK
        have hXvRealTop : (Xv : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hXvTop
        have hlogXpos : 0 < Real.log (Xv : ℝ) :=
          Real.log_pos (by linarith only [hXvReal])
        have hlogXone : 1 ≤ Real.log (Xv : ℝ) := by
          have hlog3 : 1 < Real.log 3 := by linarith only [Real.log_three_gt_d9]
          exact le_trans hlog3.le (Real.log_le_log (by norm_num) hXvReal)
        have hlogKX : Real.log (K : ℝ) ≤ Real.log (Xv : ℝ) :=
          Real.log_le_log (by linarith only [hKreal]) hXvRealK
        have hlogXTop : Real.log (Xv : ℝ) ≤ Real.log (2 * (K : ℝ)) :=
          Real.log_le_log (by linarith only [hXvReal]) hXvRealTop
        have hXcut := hblocks v hvlt
        rcases hXcut with ⟨_hHlow, _hHup, hysieve, _hTaylor⟩
        have hCram := hcramer K Xv H hK hXvK hXvH
          (by exact_mod_cast hHpos) hysieve ξ
        let fc : ℤ → ℂ := fun n =>
          ((paperShortBlockCramerWeight (Xv : ℝ) n - 1 : ℝ) : ℂ) *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))
        have hsum := shortBlockRealInterval_sum_eq_natIco K H v fc
        have hsumXv :
            (∑ n ∈ realIntegerInterval (Xv : ℝ) (H : ℝ), fc n) =
              ∑ n ∈ Finset.Ico (K + 1 + v * H)
                (K + 1 + (v + 1) * H), fc (n : ℤ) := by
          simpa [Xv, Nat.cast_add, Nat.cast_mul] using hsum
        have hCramIco :
            ‖∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
              fc (n : ℤ)‖ ≤
              Cc * ((H : ℝ) *
                    Real.exp (-((Real.log (Xv : ℝ)) ^ (1 / 5 : ℝ))) +
                  paperCramerDensity
                    (Real.exp ((Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ))) *
                    Real.exp ((Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ)) +
                  paperCramerDensity
                    (Real.exp ((Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ))) *
                    (K : ℝ) ^ (1 - δ) *
                    (1 + Real.log
                      (Real.exp ((Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ)))) +
                  (K : ℝ) ^ (1 - δ)) := by
          rw [← hsumXv]
          have hCram' := hCram
          rw [hcrDelta] at hCram'
          simpa only [fc, paperShortBlockCramerWeight,
            paperShortBlockCutoff] using hCram'
        let Rv := paperCramerDensity
          (Real.exp ((Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ)))
        let Yv := Real.exp ((Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ))
        have hwv : 2 ≤ Real.exp ((Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ)) := by
          have hpow : 1 ≤ (Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ) :=
            Real.one_le_rpow hlogXone (by norm_num)
          exact le_trans Real.exp_one_gt_two.le
            (Real.exp_le_exp.mpr hpow)
        have hRv : Rv ≤ Real.exp ((Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ)) :=
          (paperCramerDensity_bounds hwv).2
        have hpow01 :
            (Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ) ≤
              (Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlogXone (by norm_num)
        have hRvSub : Rv ≤ Rsub := by
          calc
            Rv ≤ Real.exp ((Real.log (Xv : ℝ)) ^ (1 / 10 : ℝ)) := hRv
            _ ≤ Yv := Real.exp_le_exp.mpr hpow01
            _ ≤ Real.exp ((Real.log (2 * (K : ℝ)) ^ (3 / 10 : ℝ))) :=
              Real.exp_le_exp.mpr
                (Real.rpow_le_rpow hlogXpos.le hlogXTop (by norm_num))
            _ ≤ Rsub := hExpAtK2
        have hYvSub : Yv ≤ Rsub := by
          calc
            Yv = Real.exp ((Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ)) := rfl
            _ ≤ Real.exp ((Real.log (2 * (K : ℝ)) ^ (3 / 10 : ℝ)) ) :=
              Real.exp_le_exp.mpr
                (Real.rpow_le_rpow hlogXpos.le hlogXTop (by norm_num))
            _ ≤ Rsub := hExpAtK2
        have hlogYv : Real.log Yv ≤ Rsub := by
          have hpowLog : (Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ) ≤
              Real.log (2 * (K : ℝ)) :=
            (show (Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ) ≤
                Real.log (Xv : ℝ) by
              simpa only [Real.rpow_one] using
                Real.rpow_le_rpow_of_exponent_le hlogXone
                  (by norm_num : (3 / 10 : ℝ) ≤ 1)).trans hlogXTop
          calc
            Real.log Yv = (Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ) := by
              simp [Yv, Real.log_exp]
            _ ≤ Real.log (2 * (K : ℝ)) := hpowLog
            _ ≤ Rsub := hLogAtK2
        have hlogYvOne : 1 + Real.log Yv ≤ 2 * Rsub := by
          have hYge : 1 ≤ Rsub := hRsubOne
          have hlogBound : Real.log Yv ≤ Rsub := hlogYv
          linarith
        have hlogYvNonneg : 0 ≤ 1 + Real.log Yv := by
          have hpowNonneg : 0 ≤ (Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ) :=
            Real.rpow_nonneg hlogXpos.le _
          have hYge : 1 ≤ Yv := by
            dsimp [Yv]
            exact Real.one_le_exp hpowNonneg
          have hlogNonneg : 0 ≤ Real.log Yv := Real.log_nonneg hYge
          linarith
        have hExpDecayX :
            Real.exp (-((Real.log (Xv : ℝ)) ^ (1 / 5 : ℝ))) ≤ E0 := by
          have hlogXpow : (Real.log (K : ℝ)) ^ (1 / 5 : ℝ) ≤
              (Real.log (Xv : ℝ)) ^ (1 / 5 : ℝ) :=
            Real.rpow_le_rpow hKlogpos.le hlogKX (by norm_num)
          have hneg := neg_le_neg hlogXpow
          have hbase :
              -((Real.log (Xv : ℝ)) ^ (1 / 5 : ℝ)) ≤
                -((Real.log (K : ℝ)) ^ (1 / 5 : ℝ)) := hneg
          simpa [E0, L] using Real.exp_le_exp.mpr hbase
        have hbaseTerms :
            (H : ℝ) * Real.exp (-((Real.log (Xv : ℝ)) ^ (1 / 5 : ℝ))) +
              Rv * Yv + Rv * (K : ℝ) ^ (1 - δ) * (1 + Real.log Yv) +
                (K : ℝ) ^ (1 - δ) ≤
            (H : ℝ) * E0 + Rsub ^ 2 +
              2 * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
                (K : ℝ) ^ (1 - δ) := by
          have hKpnon : 0 ≤ (K : ℝ) ^ (1 - δ) :=
            Real.rpow_nonneg (by positivity) _
          have hHnon : 0 ≤ (H : ℝ) := by positivity
          have hRY : Rv * Yv ≤ Rsub * Rsub := by
            calc
              Rv * Yv ≤ Rsub * Yv :=
                mul_le_mul_of_nonneg_right hRvSub (by positivity)
              _ ≤ Rsub * Rsub :=
                mul_le_mul_of_nonneg_left hYvSub (by positivity)
          have hRlog :
              Rv * (K : ℝ) ^ (1 - δ) * (1 + Real.log Yv) ≤
                Rsub * (K : ℝ) ^ (1 - δ) * (2 * Rsub) := by
            calc
              _ = Rv * ((K : ℝ) ^ (1 - δ) * (1 + Real.log Yv)) := by ring
              _ ≤ Rsub * ((K : ℝ) ^ (1 - δ) * (1 + Real.log Yv)) :=
                mul_le_mul_of_nonneg_right hRvSub
                  (mul_nonneg hKpnon hlogYvNonneg)
              _ = Rsub * (K : ℝ) ^ (1 - δ) * (1 + Real.log Yv) := by ring
              _ ≤ Rsub * (K : ℝ) ^ (1 - δ) * (2 * Rsub) :=
                mul_le_mul_of_nonneg_left hlogYvOne
                  (mul_nonneg hRsubPos.le hKpnon)
          calc
            _ ≤ (H : ℝ) * E0 + Rsub * Rsub +
                Rsub * (K : ℝ) ^ (1 - δ) * (2 * Rsub) +
                  (K : ℝ) ^ (1 - δ) := by
              exact add_le_add (add_le_add (add_le_add
                (mul_le_mul_of_nonneg_left hExpDecayX hHnon) hRY) hRlog) le_rfl
            _ = _ := by ring
        have hCramIco' := hCramIco.trans
          (mul_le_mul_of_nonneg_left hbaseTerms hCc)
        simpa [fc, Rv, Yv, Xv, Nat.cast_add, Nat.cast_mul] using hCramIco'
      have hsumEach := Finset.sum_le_sum hCrEach
      have hsumConst :
          (∑ v ∈ Finset.range q,
            Cc * ((H : ℝ) * E0 + Rsub ^ 2 +
              2 * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
              (K : ℝ) ^ (1 - δ))) =
            (q : ℝ) * Cc * ((H : ℝ) * E0 + Rsub ^ 2 +
              2 * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
              (K : ℝ) ^ (1 - δ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      have hsumExpand :
          (q : ℝ) * Cc * ((H : ℝ) * E0 + Rsub ^ 2 +
            2 * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
            (K : ℝ) ^ (1 - δ)) =
            Cc * ((q : ℝ) * (H : ℝ) * E0 + (q : ℝ) * Rsub ^ 2 +
              2 * (q : ℝ) * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
              (q : ℝ) * (K : ℝ) ^ (1 - δ)) := by ring
      have hsumEach' :
          (∑ i ∈ Finset.range q,
            ‖∑ n ∈ Finset.Ico (K + 1 + i * H) (K + 1 + (i + 1) * H),
              ((paperShortBlockCramerWeight ((K + i * H : ℕ) : ℝ)
                (n : ℤ) - 1 : ℝ) : ℂ) *
                unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
            (q : ℝ) * Cc * ((H : ℝ) * E0 + Rsub ^ 2 +
              2 * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
              (K : ℝ) ^ (1 - δ)) := by
        calc
          _ ≤ ∑ i ∈ Finset.range q,
              Cc * ((H : ℝ) * E0 + Rsub ^ 2 +
                2 * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
                (K : ℝ) ^ (1 - δ)) := hsumEach
          _ = _ := hsumConst
      rw [hsumExpand] at hsumEach'
      have hterm2 :
          (q : ℝ) * Rsub ^ 2 ≤
            2 * (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - γ) := by
        calc
          _ ≤ 2 * (K : ℝ) ^ (δ / 4) * Rsub ^ 2 :=
            mul_le_mul_of_nonneg_right hqbound' (by positivity)
          _ = 2 * (2 : ℝ) ^ (2 * s) *
              ((K : ℝ) ^ (δ / 4) * (K : ℝ) ^ (2 * s)) := by
            rw [hRsubSq]
            ring
          _ = 2 * (2 : ℝ) ^ (2 * s) *
              (K : ℝ) ^ (δ / 4 + 2 * s) := by
            rw [← Real.rpow_add (by positivity : 0 < (K : ℝ))]
          _ ≤ 2 * (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - γ) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hKge1 hExp2) (by positivity)
      have hterm3 :
          2 * (q : ℝ) * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) ≤
            4 * (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - γ) := by
        have hqbound2 : (2 : ℝ) * (q : ℝ) ≤
            4 * (K : ℝ) ^ (δ / 4) := by
          calc
            _ ≤ 2 * (2 * (K : ℝ) ^ (δ / 4)) :=
              mul_le_mul_of_nonneg_left hqbound' (by norm_num)
            _ = _ := by ring
        calc
          _ ≤ 4 * (K : ℝ) ^ (δ / 4) * Rsub ^ 2 *
              (K : ℝ) ^ (1 - δ) := by
            calc
              _ = ((2 : ℝ) * (q : ℝ)) *
                  (Rsub ^ 2 * (K : ℝ) ^ (1 - δ)) := by ring
              _ ≤ (4 * (K : ℝ) ^ (δ / 4)) *
                  (Rsub ^ 2 * (K : ℝ) ^ (1 - δ)) :=
                mul_le_mul_of_nonneg_right hqbound2
                  (mul_nonneg (sq_nonneg Rsub)
                    (Real.rpow_nonneg (by positivity) (1 - δ)))
              _ = _ := by ring
          _ = 4 * (2 : ℝ) ^ (2 * s) *
              ((K : ℝ) ^ (δ / 4) * (K : ℝ) ^ (2 * s) *
                (K : ℝ) ^ (1 - δ)) := by
            rw [hRsubSq]
            ring
          _ = 4 * (2 : ℝ) ^ (2 * s) *
              (K : ℝ) ^ (1 - δ + δ / 4 + 2 * s) := by
            rw [← Real.rpow_add (by positivity : 0 < (K : ℝ))]
            rw [← Real.rpow_add (by positivity : 0 < (K : ℝ))]
            congr 2 <;> ring
          _ ≤ 4 * (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - γ) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hKge1 hExp3) (by positivity)
      have hterm4 :
          (q : ℝ) * (K : ℝ) ^ (1 - δ) ≤
            2 * (K : ℝ) ^ (1 - γ) := by
        calc
          _ ≤ 2 * (K : ℝ) ^ (δ / 4) * (K : ℝ) ^ (1 - δ) :=
            mul_le_mul_of_nonneg_right hqbound' (Real.rpow_nonneg (by positivity) _)
          _ = 2 * ((K : ℝ) ^ (δ / 4) * (K : ℝ) ^ (1 - δ)) := by ring
          _ = 2 * (K : ℝ) ^ (1 - δ + δ / 4) := by
            rw [← Real.rpow_add (by positivity : 0 < (K : ℝ))]
            congr 2 <;> ring
          _ ≤ 2 * (K : ℝ) ^ (1 - γ) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hKge1 hExp4) (by norm_num)
      have hterm1 : (q : ℝ) * (H : ℝ) * E0 ≤ (K : ℝ) * E0 :=
        mul_le_mul_of_nonneg_right hqHreal (Real.exp_nonneg _)
      have hsumTerms :
          (q : ℝ) * (H : ℝ) * E0 + (q : ℝ) * Rsub ^ 2 +
            2 * (q : ℝ) * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
              (q : ℝ) * (K : ℝ) ^ (1 - δ) ≤
          (K : ℝ) * E0 +
            (6 * (2 : ℝ) ^ (2 * s) + 2) * (K : ℝ) ^ (1 - γ) := by
        calc
          _ ≤ (K : ℝ) * E0 +
              2 * (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - γ) +
              4 * (2 : ℝ) ^ (2 * s) * (K : ℝ) ^ (1 - γ) +
              2 * (K : ℝ) ^ (1 - γ) := by
            linarith [hterm1, hterm2, hterm3, hterm4]
          _ = _ := by ring
      calc
        _ ≤ Cc * ((q : ℝ) * (H : ℝ) * E0 + (q : ℝ) * Rsub ^ 2 +
              2 * (q : ℝ) * Rsub ^ 2 * (K : ℝ) ^ (1 - δ) +
              (q : ℝ) * (K : ℝ) ^ (1 - δ)) := hsumEach'
        _ ≤ Cc * ((K : ℝ) * E0 +
              (6 * (2 : ℝ) ^ (2 * s) + 2) * (K : ℝ) ^ (1 - γ)) :=
          mul_le_mul_of_nonneg_left hsumTerms hCc
        _ = Cc * (K : ℝ) * E0 +
              Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) * (K : ℝ) ^ (1 - γ) := by ring

    -- Apply the exact partition to each of the two arithmetic coefficient
    -- sequences, keeping the final remainder separate.
    let fMu : ℕ → ℂ := fun n =>
      (paperMu (n : ℤ) : ℂ) *
        unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))
    let fLambda : ℕ → ℂ := fun n =>
      ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
        unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))
    let remMu : ℂ := ∑ n ∈ Finset.Ico (K + 1 + q * H)
      (K + 1 + q * H + r), fMu n
    let remLambda : ℂ := ∑ n ∈ Finset.Ico (K + 1 + q * H)
      (K + 1 + q * H + r), fLambda n
    have hdecompMu :
        (∑ n ∈ Finset.Ioc K K', fMu n) =
          (∑ v ∈ Finset.range q,
            ∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H), fMu n) + remMu := by
      rw [natIoc_eq_natIco_succ]
      simpa [remMu, fMu] using hdecomp fMu
    have hdecompLambda :
        (∑ n ∈ Finset.Ioc K K', fLambda n) =
          (∑ v ∈ Finset.range q,
            ∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H), fLambda n) + remLambda := by
      rw [natIoc_eq_natIco_succ]
      simpa [remLambda, fLambda] using hdecomp fLambda
    -- Convert the two source short-remainder estimates into full-block
    -- bounds, and keep the terminal interval as a separate error.
    let remainder : Finset ℕ := Finset.Ico (K + 1 + q * H)
      (K + 1 + q * H + r)
    let lambdaShortBlock (v : ℕ) : ℂ :=
      ∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
        ((paperLambda (n : ℤ) -
          paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ) (n : ℤ) : ℝ) : ℂ) *
          unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))
    let lambdaCramerBlock (v : ℕ) : ℂ :=
      ∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
        ((paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ) (n : ℤ) - 1 : ℝ) : ℂ) *
          unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))
    have hlambdaBlockSplit : ∀ v : ℕ,
        (∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
          fLambda n) = lambdaShortBlock v + lambdaCramerBlock v := by
      intro v
      dsimp [fLambda, lambdaShortBlock, lambdaCramerBlock]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      rw [← add_mul]
      congr 1
      push_cast
      ring
    have hlambdaBlockSums :
        (∑ v ∈ Finset.range q,
          ∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H), fLambda n) =
          (∑ v ∈ Finset.range q, lambdaShortBlock v) +
            ∑ v ∈ Finset.range q, lambdaCramerBlock v := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      exact hlambdaBlockSplit v
    have hshortMuSum :
        (∑ v ∈ Finset.range q,
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H), fMu n‖) ≤
          Cshort * (K : ℝ) * L ^ (-A : ℝ) := by
      simpa [fMu] using hshortMu.trans hShortFactor
    have hshortLambdaSum :
        (∑ v ∈ Finset.range q, ‖lambdaShortBlock v‖) ≤
          Cshort * (K : ℝ) * L ^ (-A : ℝ) := by
      simpa [lambdaShortBlock] using hshortLambda.trans hShortFactor
    have hcramerBlockSum :
        (∑ v ∈ Finset.range q, ‖lambdaCramerBlock v‖) ≤
          Cc * (K : ℝ) * E0 +
            Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) * (K : ℝ) ^ (1 - γ) := by
      simpa [lambdaCramerBlock] using hCramerBlocks
    have hremainderCard : (remainder.card : ℝ) ≤ (H : ℝ) := by
      have hlt : remainder.card < H := by
        simpa [remainder] using hremCard
      exact_mod_cast hlt.le
    have hnRemainder {n : ℕ} (hn : n ∈ remainder) : K + 1 ≤ n ∧ n ≤ K' := by
      have hn' : K + 1 + q * H ≤ n ∧ n < K + 1 + q * H + r :=
        Finset.mem_Ico.mp (by simpa [remainder] using hn)
      constructor
      · omega
      · have hupper : K + 1 + q * H + r = K' + 1 := by
          have hK'eq' : K' = K + q * H + r := by
            simpa [q, r] using hK'eq
          rw [hK'eq']
          omega
        omega
    have hmuRemainderTerm {n : ℕ} (hn : n ∈ remainder) : ‖fMu n‖ ≤ 1 := by
      have hnNat : 1 ≤ n := by
        have hnstart := (hnRemainder hn).1
        omega
      have hnInt : 1 ≤ (n : ℤ) := by exact_mod_cast hnNat
      dsimp [fMu]
      rw [norm_mul, norm_unitFrequencyPhase, mul_one, Complex.norm_intCast]
      exact_mod_cast paperMu_abs_le_one hnInt
    have hlambdaRemainderTerm {n : ℕ} (hn : n ∈ remainder) :
        ‖fLambda n‖ ≤ 1 + Real.log (2 * (K : ℝ)) := by
      have hnNat : 1 ≤ n := by
        have hnstart := (hnRemainder hn).1
        omega
      have hnInt : 1 ≤ (n : ℤ) := by exact_mod_cast hnNat
      have hbound := paperLambda_bounds hnInt
      have hnTop : (n : ℝ) ≤ 2 * (K : ℝ) := by
        have hnK' := (hnRemainder hn).2
        exact_mod_cast le_trans hnK' hK'2
      have hlog : Real.log (n : ℝ) ≤ Real.log (2 * (K : ℝ)) :=
        Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hnTop
      have habs : |paperLambda (n : ℤ) - 1| ≤
          1 + Real.log (2 * (K : ℝ)) := by
        calc
          |paperLambda (n : ℤ) - 1| ≤
              |paperLambda (n : ℤ)| + |(1 : ℝ)| := abs_sub _ _
          _ = paperLambda (n : ℤ) + 1 := by
            rw [abs_of_nonneg hbound.1, abs_one]
          _ ≤ Real.log (n : ℝ) + 1 := by
            calc
              _ = 1 + paperLambda (n : ℤ) := by ring
              _ ≤ 1 + Real.log (n : ℝ) := by
                simpa [add_comm] using add_le_add_left hbound.2 1
              _ = _ := by ring
          _ ≤ 1 + Real.log (2 * (K : ℝ)) := by
            calc
              _ = 1 + Real.log (n : ℝ) := by ring
              _ ≤ 1 + Real.log (2 * (K : ℝ)) := by
                simpa [add_comm] using add_le_add_left hlog 1
      dsimp [fLambda]
      rw [norm_mul, norm_unitFrequencyPhase, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact habs
    have hremMu : ‖remMu‖ ≤ (H : ℝ) := by
      dsimp [remMu]
      calc
        _ ≤ ∑ n ∈ remainder, ‖fMu n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ remainder, (1 : ℝ) :=
          Finset.sum_le_sum (by intro n hn; exact hmuRemainderTerm hn)
        _ = (remainder.card : ℝ) := by simp
        _ ≤ (H : ℝ) := hremainderCard
    have hremLambda :
        ‖remLambda‖ ≤ (H : ℝ) * (1 + Real.log (2 * (K : ℝ))) := by
      dsimp [remLambda]
      calc
        _ ≤ ∑ n ∈ remainder, ‖fLambda n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ remainder, (1 + Real.log (2 * (K : ℝ))) :=
          Finset.sum_le_sum (by intro n hn; exact hlambdaRemainderTerm hn)
        _ = (remainder.card : ℝ) * (1 + Real.log (2 * (K : ℝ))) := by
          simp [Finset.sum_const, nsmul_eq_mul] <;> ring
        _ ≤ (H : ℝ) * (1 + Real.log (2 * (K : ℝ))) := by
          have hlogNonneg : 0 ≤ Real.log (2 * (K : ℝ)) :=
            Real.log_nonneg (by linarith [hKreal])
          exact mul_le_mul_of_nonneg_right hremainderCard
            (add_nonneg (by norm_num) hlogNonneg)
    have hremTotal : ‖remLambda‖ + ‖remMu‖ ≤
        3 * (2 : ℝ) ^ s * (K : ℝ) ^ (1 - γ) := by
      have htwoPlus : 2 + Real.log (2 * (K : ℝ)) ≤ 3 * Rsub := by
        calc
          2 + Real.log (2 * (K : ℝ)) ≤ 2 + Rsub :=
            by simpa [add_comm] using add_le_add_left hLogAtK2 2
          _ ≤ 3 * Rsub := by nlinarith [hRsubOne]
      have htwoPlusNonneg : 0 ≤ 2 + Real.log (2 * (K : ℝ)) := by
        have hbase : (1 : ℝ) ≤ 2 * (K : ℝ) := by nlinarith [hKreal]
        have hlogNonneg : 0 ≤ Real.log (2 * (K : ℝ)) :=
          Real.log_nonneg hbase
        linarith
      have hthetaS : θ + s ≤ 1 - γ := by
        have hθeq : θ = 1 - δ / 4 := by linarith [hthetaDelta]
        dsimp [s, γ]
        rw [hθeq]
        nlinarith [hδpos]
      have hHpow : (H : ℝ) ≤ (K : ℝ) ^ θ := hHupper
      calc
        _ ≤ (H : ℝ) * (2 + Real.log (2 * (K : ℝ))) := by
          calc
            _ ≤ (H : ℝ) * (1 + Real.log (2 * (K : ℝ))) + (H : ℝ) :=
              add_le_add hremLambda hremMu
            _ = _ := by ring
        _ ≤ (K : ℝ) ^ θ * (3 * Rsub) := by
          calc
            _ ≤ (K : ℝ) ^ θ *
                (2 + Real.log (2 * (K : ℝ))) :=
              mul_le_mul_of_nonneg_right hHpow htwoPlusNonneg
            _ ≤ (K : ℝ) ^ θ * (3 * Rsub) :=
              mul_le_mul_of_nonneg_left htwoPlus
                (Real.rpow_nonneg (by positivity) θ)
        _ = 3 * (2 : ℝ) ^ s * (K : ℝ) ^ (θ + s) := by
          dsimp [Rsub]
          calc
            _ = 3 * (2 : ℝ) ^ s *
                ((K : ℝ) ^ θ * (K : ℝ) ^ s) := by
              rw [Real.mul_rpow (by norm_num) (by positivity)]
              ring
            _ = _ := by
              rw [← Real.rpow_add (by positivity : 0 < (K : ℝ))]
        _ ≤ 3 * (2 : ℝ) ^ s * (K : ℝ) ^ (1 - γ) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by linarith [hKreal]) hthetaS)
            (by positivity)
    have hfullMu :
        ‖∑ n ∈ Finset.Ioc K K', fMu n‖ ≤
          Cshort * (K : ℝ) * L ^ (-A : ℝ) + ‖remMu‖ := by
      rw [hdecompMu]
      calc
        _ ≤ ‖∑ v ∈ Finset.range q,
              ∑ n ∈ Finset.Ico (K + 1 + v * H)
                (K + 1 + (v + 1) * H), fMu n‖ + ‖remMu‖ := norm_add_le _ _
        _ ≤ (∑ v ∈ Finset.range q,
              ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
                (K + 1 + (v + 1) * H), fMu n‖) + ‖remMu‖ := by
          exact add_le_add (norm_sum_le _ _ ) le_rfl
        _ ≤ _ := add_le_add hshortMuSum le_rfl
    have hcramerLog :
        Cc * (K : ℝ) * E0 +
            Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) * (K : ℝ) ^ (1 - γ) ≤
          (Cc + Cc * (6 * (2 : ℝ) ^ (2 * s) + 2)) *
            (K : ℝ) * L ^ (-A : ℝ) := by
      have hdecayTerm : Cc * (K : ℝ) * E0 ≤
          Cc * (K : ℝ) * L ^ (-A : ℝ) :=
        mul_le_mul_of_nonneg_left hDecayFactor (mul_nonneg hCc (by positivity))
      have hpowerCoeffNonneg :
          0 ≤ Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) := by positivity
      have hpowerTerm :
          Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) * (K : ℝ) ^ (1 - γ) ≤
            Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) *
              (K : ℝ) * L ^ (-A : ℝ) :=
        by
          have h := mul_le_mul_of_nonneg_left hPowerAtK hpowerCoeffNonneg
          simpa [mul_assoc] using h
      calc
        _ ≤ Cc * (K : ℝ) * L ^ (-A : ℝ) +
            Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) *
              (K : ℝ) * L ^ (-A : ℝ) := add_le_add hdecayTerm hpowerTerm
        _ = _ := by ring
    have hremLog : ‖remLambda‖ + ‖remMu‖ ≤
        3 * (2 : ℝ) ^ s * (K : ℝ) * L ^ (-A : ℝ) := by
      have hremCoeffNonneg : 0 ≤ 3 * (2 : ℝ) ^ s := by positivity
      calc
        _ ≤ 3 * (2 : ℝ) ^ s * (K : ℝ) ^ (1 - γ) := hremTotal
        _ ≤ 3 * (2 : ℝ) ^ s * (K : ℝ) * L ^ (-A : ℝ) :=
          by
            have h := mul_le_mul_of_nonneg_left hPowerAtK hremCoeffNonneg
            simpa [mul_assoc] using h
    have hfullLambda :
        ‖∑ n ∈ Finset.Ioc K K', fLambda n‖ ≤
          Cshort * (K : ℝ) * L ^ (-A : ℝ) +
            (Cc + Cc * (6 * (2 : ℝ) ^ (2 * s) + 2)) *
              (K : ℝ) * L ^ (-A : ℝ) + ‖remLambda‖ := by
      rw [hdecompLambda]
      calc
        _ ≤ ‖∑ v ∈ Finset.range q,
              ∑ n ∈ Finset.Ico (K + 1 + v * H)
                (K + 1 + (v + 1) * H), fLambda n‖ + ‖remLambda‖ := norm_add_le _ _
        _ ≤ (‖∑ v ∈ Finset.range q, lambdaShortBlock v‖ +
              ‖∑ v ∈ Finset.range q, lambdaCramerBlock v‖) + ‖remLambda‖ := by
          rw [hlambdaBlockSums]
          exact add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ((∑ v ∈ Finset.range q, ‖lambdaShortBlock v‖) +
              (∑ v ∈ Finset.range q, ‖lambdaCramerBlock v‖)) + ‖remLambda‖ := by
          gcongr <;> exact norm_sum_le _ _
        _ ≤ (Cshort * (K : ℝ) * L ^ (-A : ℝ) +
              (Cc * (K : ℝ) * E0 +
                Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) * (K : ℝ) ^ (1 - γ))) +
                ‖remLambda‖ := by
          gcongr <;> assumption
        _ ≤ _ := by
          have h := hcramerLog
          linarith
    have htotal :
        ‖∑ n ∈ Finset.Ioc K K', fLambda n‖ +
            ‖∑ n ∈ Finset.Ioc K K', fMu n‖ ≤
          C * (K : ℝ) * L ^ (-A : ℝ) := by
      have hsum :
          ‖∑ n ∈ Finset.Ioc K K', fLambda n‖ +
              ‖∑ n ∈ Finset.Ioc K K', fMu n‖ ≤
            2 * Cshort * ((K : ℝ) * L ^ (-A : ℝ)) +
              (Cc + Cc * (6 * (2 : ℝ) ^ (2 * s) + 2)) *
                ((K : ℝ) * L ^ (-A : ℝ)) + ‖remLambda‖ + ‖remMu‖ := by
        calc
          _ ≤ (Cshort * (K : ℝ) * L ^ (-A : ℝ) +
                (Cc + Cc * (6 * (2 : ℝ) ^ (2 * s) + 2)) *
                  (K : ℝ) * L ^ (-A : ℝ) + ‖remLambda‖) +
              (Cshort * (K : ℝ) * L ^ (-A : ℝ) + ‖remMu‖) :=
            add_le_add hfullLambda hfullMu
          _ = _ := by ring
      have hcoeff :
          2 * Cshort + Cc + Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) +
              3 * (2 : ℝ) ^ s ≤ C := by
        dsimp [C, Cpower]
        linarith [hCsmall]
      have hfac : 0 ≤ (K : ℝ) * L ^ (-A : ℝ) := by positivity
      calc
        _ ≤ (2 * Cshort + Cc +
              Cc * (6 * (2 : ℝ) ^ (2 * s) + 2)) *
                ((K : ℝ) * L ^ (-A : ℝ)) +
              3 * (2 : ℝ) ^ s * (K : ℝ) * L ^ (-A : ℝ) := by
          calc
            _ ≤ (2 * Cshort + Cc +
                  Cc * (6 * (2 : ℝ) ^ (2 * s) + 2)) *
                    ((K : ℝ) * L ^ (-A : ℝ)) +
                  (‖remLambda‖ + ‖remMu‖) := by
              convert hsum using 1 <;> ring
            _ ≤ _ := add_le_add_right hremLog _
            _ = _ := by ring
        _ ≤ C * (K : ℝ) * L ^ (-A : ℝ) := by
          calc
            _ = (2 * Cshort + Cc +
                Cc * (6 * (2 : ℝ) ^ (2 * s) + 2) +
                  3 * (2 : ℝ) ^ s) * ((K : ℝ) * L ^ (-A : ℝ)) := by ring
            _ ≤ C * ((K : ℝ) * L ^ (-A : ℝ)) :=
              mul_le_mul_of_nonneg_right hcoeff hfac
            _ = _ := by ring
    simpa [fLambda, fMu, L] using htotal
  · -- The source explicitly absorbs the finite set of smaller scales.
    have hKlt : (K : ℝ) < Kbig := lt_of_not_ge hlarge
    have hKleBig : (K : ℝ) ≤ Kbig := hKlt.le
    have hnPoint : ∀ n ∈ Finset.Ioc K K',
        ‖((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ +
          ‖(paperMu (n : ℤ) : ℂ) *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
          2 + Real.log (2 * Kbig) := by
      intro n hn
      have hnmem := Finset.mem_Ioc.mp hn
      have hnNat : 1 ≤ n := by omega
      have hnInt : 1 ≤ (n : ℤ) := by exact_mod_cast hnNat
      have hlambda := paperLambda_bounds hnInt
      have hmu := paperMu_abs_le_one hnInt
      have hnTop : (n : ℝ) ≤ 2 * Kbig := by
        have hnK' := hnmem.2
        have hnat : n ≤ 2 * K := le_trans hnK' hK'2
        calc
          (n : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hnat
          _ ≤ 2 * Kbig := by nlinarith [hKleBig]
      have hlog := Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hnTop
      have hlambdaAbs : |paperLambda (n : ℤ) - 1| ≤ 1 + Real.log (2 * Kbig) := by
        calc
          |paperLambda (n : ℤ) - 1| ≤
              |paperLambda (n : ℤ)| + |(1 : ℝ)| := abs_sub _ _
          _ = paperLambda (n : ℤ) + 1 := by
            rw [abs_of_nonneg hlambda.1, abs_one]
          _ ≤ 1 + Real.log (2 * Kbig) := by
            calc
              paperLambda (n : ℤ) + 1 = 1 + paperLambda (n : ℤ) := by ring
              _ ≤ 1 + Real.log (n : ℝ) := by
                simpa [add_comm] using add_le_add_left hlambda.2 1
              _ ≤ 1 + Real.log (2 * Kbig) := by
                simpa [add_comm] using add_le_add_left hlog 1
      have hmuC : ‖(paperMu (n : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast hmu
      simp only [norm_mul, norm_unitFrequencyPhase, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      calc
        |paperLambda (n : ℤ) - 1| + ‖(paperMu (n : ℤ) : ℂ)‖ ≤
            (1 + Real.log (2 * Kbig)) + 1 := add_le_add hlambdaAbs hmuC
        _ = 2 + Real.log (2 * Kbig) := by ring
    have hsmallCard : (Finset.Ioc K K').card ≤ K := by
      calc
        (Finset.Ioc K K').card =
            (Finset.Ico (K + 1) (K' + 1)).card := by
          rw [natIoc_eq_natIco_succ]
        _ = (K' + 1) - (K + 1) := by rw [Nat.card_Ico]
        _ = K' - K := by omega
        _ ≤ K := by omega
    have hsmallNorms :
        ‖∑ n ∈ Finset.Ioc K K',
            ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
              unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ +
          ‖∑ n ∈ Finset.Ioc K K',
            (paperMu (n : ℤ) : ℂ) *
              unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
            (Finset.Ioc K K').card * (2 + Real.log (2 * Kbig)) := by
      calc
        _ ≤ (∑ n ∈ Finset.Ioc K K',
              ‖((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
                unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) +
              ∑ n ∈ Finset.Ioc K K',
                ‖(paperMu (n : ℤ) : ℂ) *
                  unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ :=
          add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
        _ = ∑ n ∈ Finset.Ioc K K',
              (‖((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
                  unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ +
                ‖(paperMu (n : ℤ) : ℂ) *
                  unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) := by
          rw [← Finset.sum_add_distrib]
        _ ≤ ∑ n ∈ Finset.Ioc K K', (2 + Real.log (2 * Kbig)) :=
          Finset.sum_le_sum (by intro n hn; exact hnPoint n hn)
        _ = (Finset.Ioc K K').card * (2 + Real.log (2 * Kbig)) := by
          simp [Finset.sum_const, nsmul_eq_mul] <;> ring
    have hlogBigOne : 1 ≤ Real.log Kbig := by
      have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
      exact le_trans hlog3.le (Real.log_le_log (by norm_num) hKbig3)
    have hlogMon : Real.log (K : ℝ) ≤ Real.log Kbig :=
      Real.log_le_log (by linarith [hKreal]) hKleBig
    have hpowMon : (Real.log (K : ℝ)) ^ A ≤ (Real.log Kbig) ^ A :=
      Real.rpow_le_rpow hKlogpos.le hlogMon hA.le
    have hscale : 1 ≤ (Real.log Kbig) ^ A *
        (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      rw [Real.rpow_neg hKlogpos.le]
      have hpos : 0 < (Real.log (K : ℝ)) ^ A :=
        Real.rpow_pos_of_pos hKlogpos A
      calc
        1 = (Real.log (K : ℝ)) ^ A * ((Real.log (K : ℝ)) ^ A)⁻¹ := by
          field_simp
        _ ≤ (Real.log Kbig) ^ A * ((Real.log (K : ℝ)) ^ A)⁻¹ :=
          mul_le_mul_of_nonneg_right hpowMon (inv_nonneg.mpr hpos.le)
    have hsmallConst : 2 + Real.log (2 * Kbig) ≤
        Csmall * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      dsimp [Csmall]
      have hcoefNonneg : 0 ≤ 2 + Real.log (2 * Kbig) := by
        have hbase : (1 : ℝ) ≤ 2 * Kbig := by nlinarith [hKbig3]
        have hlog := Real.log_nonneg hbase
        linarith
      calc
        _ = (2 + Real.log (2 * Kbig)) * 1 := by ring
        _ ≤ (2 + Real.log (2 * Kbig)) *
              ((Real.log Kbig) ^ A * (Real.log (K : ℝ)) ^ (-A : ℝ)) :=
          mul_le_mul_of_nonneg_left hscale hcoefNonneg
        _ = _ := by ring
    have hsmallTotal :
        ‖∑ n ∈ Finset.Ioc K K',
            ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
              unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ +
          ‖∑ n ∈ Finset.Ioc K K',
            (paperMu (n : ℤ) : ℂ) *
              unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
            C * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      calc
        _ ≤ (Finset.Ioc K K').card * (2 + Real.log (2 * Kbig)) :=
          hsmallNorms
        _ ≤ (K : ℝ) * (2 + Real.log (2 * Kbig)) := by
          have hcoefNonneg : 0 ≤ 2 + Real.log (2 * Kbig) := by
            have hbase : (1 : ℝ) ≤ 2 * Kbig := by nlinarith [hKbig3]
            have hlog := Real.log_nonneg hbase
            linarith
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hsmallCard) hcoefNonneg
        _ ≤ (K : ℝ) * (Csmall * (Real.log (K : ℝ)) ^ (-A : ℝ)) :=
          mul_le_mul_of_nonneg_left hsmallConst (by positivity)
        _ = Csmall * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by ring
        _ ≤ C * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
          have hCsmallLE : Csmall ≤ C := by
            dsimp [C]
            linarith [hCpower, hCshort]
          calc
            _ = Csmall * ((K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ)) := by ring
            _ ≤ C * ((K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ)) :=
              mul_le_mul_of_nonneg_right hCsmallLE (by positivity)
            _ = _ := by ring
    simpa using hsmallTotal

end FractionalPrimes
