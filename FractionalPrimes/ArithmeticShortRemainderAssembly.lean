module
public import FractionalPrimes.ArithmeticShortRemainderConditional
public import FractionalPrimes.ArithmeticShortRemainderScalar
public import FractionalPrimes.FixedCutoffBoundaryComparison
public import FractionalPrimes.ShortRemainderBlockSummation
public import FractionalPrimes.CramerBlockCorrelation
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalSourceCorrelationBound
public import FractionalPrimes.Literature.Uniformity.CramerShortDivisor
public import FractionalPrimes.Chebyshev
@[expose] public section

set_option maxHeartbeats 1000000

namespace FractionalPrimes

open scoped BigOperators
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity

private theorem eventually_log_le_rpow_of_pos {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x ^ s := by
  have hlittle := (paper_log_rpow_isLittleO_rpow (a := 1) hs).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun x hx => hx⟩, hlittle]
    with x hx hbound
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxpow : 0 ≤ x ^ s := Real.rpow_nonneg (by linarith) s
  have hbound' : ‖Real.log x‖ ≤ ‖x ^ s‖ := by
    simpa [Real.rpow_one] using hbound
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hxpow] at hbound'
  exact hbound'

private theorem eventually_exp_log_tenth_le_rpow_of_pos {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp ((Real.log x) ^ (1 / 10 : ℝ)) ≤ x ^ s := by
  have hlittle := (paper_exp_log_rpow_isLittleO_rpow
    (ρ := 1 / 10) (b := s) (by norm_num) (by norm_num) hs).bound
      (by norm_num : (0 : ℝ) < 1)
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun x hx => hx⟩, hlittle]
    with x hx hbound
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hleft : 0 ≤ Real.exp ((Real.log x) ^ (1 / 10 : ℝ)) := Real.exp_nonneg _
  have hright : 0 ≤ x ^ s := Real.rpow_nonneg (by linarith) s
  have hbound' :
      ‖Real.exp ((Real.log x) ^ (1 / 10 : ℝ))‖ ≤ ‖x ^ s‖ := by
    simpa using hbound
  rw [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright] at hbound'
  exact hbound'

private theorem exists_rpow_decay_beats_log_power {A γ : ℝ}
    (hγ : 0 < γ) :
    ∃ K₀ : ℝ, 3 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      K ^ (1 - γ) ≤ K * (Real.log K) ^ (-A : ℝ) := by
  have hlittle := (paper_log_rpow_isLittleO_rpow
    (a := A) (b := γ / 2) (by linarith)).bound
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hlittle
  let K₀ : ℝ := max 3 B
  refine ⟨K₀, by dsimp [K₀]; exact le_max_left _ _, ?_⟩
  intro K hK
  have hKge : 3 ≤ K := le_trans (by dsimp [K₀]; exact le_max_left _ _) hK
  have hBge : B ≤ K := le_trans (by dsimp [K₀]; exact le_max_right _ _) hK
  have hKpos : 0 < K := by linarith
  have hlogpos : 0 < Real.log K := Real.log_pos (by linarith)
  have hlogge1 : 1 ≤ Real.log K := by
    have hlog3 : 1 < Real.log 3 := by
      have h := Real.log_three_gt_d9
      nlinarith
    exact le_trans hlog3.le (Real.log_le_log (by norm_num) hKge)
  have hbound := hB K hBge
  have hlognonneg : 0 ≤ Real.log K := hlogpos.le
  have hpowNonneg : 0 ≤ K ^ (γ / 2) := Real.rpow_nonneg hKpos.le _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlognonneg _),
    Real.norm_of_nonneg hpowNonneg] at hbound
  have hbound' : (Real.log K) ^ A ≤ K ^ (γ / 2) := by simpa using hbound
  have hinv : (K ^ (γ / 2))⁻¹ ≤ ((Real.log K) ^ A)⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos hKpos (γ / 2))
      (Real.rpow_pos_of_pos hlogpos A)).2 hbound'
  have hKinv : K ^ (-(γ / 2)) = (K ^ (γ / 2))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hKpos)]
  have hloginv : (Real.log K) ^ (-A) = ((Real.log K) ^ A)⁻¹ := by
    rw [Real.rpow_neg hlogpos.le]
  have hsmall : K ^ (-(γ / 2)) ≤ (Real.log K) ^ (-A) := by
    rw [hKinv, hloginv]
    exact hinv
  have hexp : -γ ≤ -(γ / 2) := by linarith
  have hdecay : K ^ (-γ) ≤ K ^ (-(γ / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
  have hKdecay : K ^ (-γ) ≤ (Real.log K) ^ (-A) := hdecay.trans hsmall
  calc
    K ^ (1 - γ) = K * K ^ (-γ) := by
      rw [show 1 - γ = 1 + (-γ) by ring, Real.rpow_add hKpos]
      simp [Real.rpow_one]
    _ ≤ K * (Real.log K) ^ (-A : ℝ) :=
      mul_le_mul_of_nonneg_left hKdecay hKpos.le

private noncomputable def shortRemainderSizeFactor (K : ℝ) : ℝ :=
  1 + Real.log (2 * K) +
    Real.exp ((Real.log (2 * K)) ^ (1 / 10 : ℝ))

private theorem shortRemainder_nonempty_interval {X H : ℕ} (hH : 0 < H) :
    (realIntegerInterval (X : ℝ) (H : ℝ)).Nonempty := by
  have hcard := realIntegerInterval_nat_card X H
  have hpos : 0 < (realIntegerInterval (X : ℝ) (H : ℝ)).card := by omega
  exact Finset.card_pos.mp hpos

private theorem shortRemainder_ioc_eq_ico {a b : ℕ} :
    Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

private theorem shortRemainder_blockIco_eq (K H v : ℕ) :
    Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H) =
      Finset.Ico (K + v * H + 1) (K + v * H + H + 1) := by
  have hlo : K + 1 + v * H = K + v * H + 1 := by omega
  have hhi : K + 1 + (v + 1) * H = K + v * H + H + 1 := by
    rw [Nat.succ_mul]
    omega
  rw [hlo, hhi]

private theorem shortRemainderRealInterval_sum_eq_natBlockIco
    {M : Type*} [AddCommMonoid M] (X H : ℕ) (f : ℤ → M) :
    (∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), f n) =
      ∑ n ∈ Finset.Ico (X + 1) (X + H + 1), f (n : ℤ) := by
  rw [realIntegerInterval_sum_eq_nat_Ioc]
  rw [shortRemainder_ioc_eq_ico]

private theorem shortRemainder_mobius_sup_le {K X H : ℕ}
    (hK : 3 ≤ K) (hX : K ≤ X) (hH : 0 < H) :
    polynomialCorrelationSupNorm (realIntegerInterval (X : ℝ) (H : ℝ))
      (fun n => (paperMu n : ℂ))
      (shortRemainder_nonempty_interval hH) ≤
        shortRemainderSizeFactor (K : ℝ) := by
  classical
  let I : Finset ℤ := realIntegerInterval (X : ℝ) (H : ℝ)
  have hI : I.Nonempty := shortRemainder_nonempty_interval hH
  have hKge1 : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (show 1 ≤ K by omega)
  have hlog : 0 ≤ Real.log (2 * (K : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hU : 1 ≤ shortRemainderSizeFactor (K : ℝ) := by
    dsimp [shortRemainderSizeFactor]
    have he : 0 ≤ Real.exp ((Real.log (2 * (K : ℝ))) ^ (1 / 10 : ℝ)) := Real.exp_nonneg _
    linarith
  have hpoint : ∀ n ∈ I, ‖(paperMu n : ℂ)‖ ≤ 1 := by
    intro n hn
    have hnI := (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) n).mp hn
    have hn3R : (3 : ℝ) ≤ (n : ℝ) := by
      have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      have hXreal : (K : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      linarith [hnI.1]
    have hn3 : (3 : ℤ) ≤ n := by exact_mod_cast hn3R
    have hmu := paperMu_abs_le_one (n := n) (by omega)
    have hmuR : |(paperMu n : ℝ)| ≤ 1 := by exact_mod_cast hmu
    simpa only [Complex.norm_intCast] using hmuR
  calc
    _ ≤ 1 := by
      unfold polynomialCorrelationSupNorm
      apply Finset.sup'_le
      intro n hn
      exact hpoint n hn
    _ ≤ shortRemainderSizeFactor (K : ℝ) := hU

private theorem shortRemainder_lambdaModel_sup_le {K X H : ℕ}
    (hK : 3 ≤ K) (hX : K ≤ X) (hXupper : X ≤ 2 * K)
    (hH : 0 < H) (hXH : X + H ≤ 2 * K) :
    polynomialCorrelationSupNorm (realIntegerInterval (X : ℝ) (H : ℝ))
      (fun n => ((paperLambda n -
        paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ))
      (shortRemainder_nonempty_interval hH) ≤
        shortRemainderSizeFactor (K : ℝ) := by
  classical
  let I : Finset ℤ := realIntegerInterval (X : ℝ) (H : ℝ)
  have hI : I.Nonempty := shortRemainder_nonempty_interval hH
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hXreal : (K : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXupperR : (X : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hXupper
  have hXHreal : (X : ℝ) + (H : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hXH
  have hlog2K : 0 ≤ Real.log (2 * (K : ℝ)) :=
    Real.log_nonneg (by linarith [hKreal])
  have hU : Real.log (2 * (K : ℝ)) +
      Real.exp ((Real.log (2 * (K : ℝ))) ^ (1 / 10 : ℝ)) ≤
        shortRemainderSizeFactor (K : ℝ) := by
    dsimp [shortRemainderSizeFactor]
    linarith
  have hpoint : ∀ n ∈ I,
      ‖((paperLambda n -
        paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)‖ ≤
          shortRemainderSizeFactor (K : ℝ) := by
    intro n hn
    have hnI := (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) n).mp hn
    have hn3R : (3 : ℝ) ≤ (n : ℝ) := by linarith [hnI.1, hXreal, hKreal]
    have hnUpperR : (n : ℝ) ≤ 2 * (K : ℝ) := by linarith [hnI.2, hXHreal]
    have hn3 : (3 : ℤ) ≤ n := by exact_mod_cast hn3R
    have hlambdaBounds := paperLambda_bounds (n := n) (by omega)
    have hlogn : Real.log (n : ℝ) ≤ Real.log (2 * (K : ℝ)) :=
      Real.log_le_log (by linarith) hnUpperR
    have hLambdaAbs : |paperLambda n| ≤ Real.log (2 * (K : ℝ)) := by
      rw [abs_of_nonneg hlambdaBounds.1]
      exact hlambdaBounds.2.trans hlogn
    have hlogXone : 1 ≤ Real.log (X : ℝ) := by
      have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
      exact le_trans hlog3.le
        (Real.log_le_log (by norm_num) (le_trans hKreal hXreal))
    have hcut2 : 2 ≤ paperShortBlockCutoff (X : ℝ) := by
      have hpow : 1 ≤ (Real.log (X : ℝ)) ^ (1 / 10 : ℝ) :=
        Real.one_le_rpow hlogXone (by norm_num)
      dsimp [paperShortBlockCutoff]
      exact le_trans Real.exp_one_gt_two.le (Real.exp_le_exp.mpr hpow)
    have hdensity := (paperCramerDensity_bounds (w := paperShortBlockCutoff (X : ℝ)) hcut2).2
    have hlogXle : Real.log (X : ℝ) ≤ Real.log (2 * (K : ℝ)) :=
      Real.log_le_log (by linarith [hKreal, hXreal]) hXupperR
    have hpowle :
        (Real.log (X : ℝ)) ^ (1 / 10 : ℝ) ≤
          (Real.log (2 * (K : ℝ))) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by linarith [hlogXone]) hlogXle (by norm_num)
    have hcramer :
        |paperShortBlockCramerWeight (X : ℝ) n| ≤
          Real.exp ((Real.log (2 * (K : ℝ))) ^ (1 / 10 : ℝ)) := by
      exact (cramerWeight_abs_le_density (X : ℝ) n).trans <| by
        calc
          paperCramerDensity (paperShortBlockCutoff (X : ℝ)) ≤
              paperShortBlockCutoff (X : ℝ) := hdensity
          _ ≤ Real.exp ((Real.log (2 * (K : ℝ))) ^ (1 / 10 : ℝ)) :=
              Real.exp_le_exp.mpr (by simpa [paperShortBlockCutoff] using hpowle)
    have hrealabs :
        |paperLambda n - paperShortBlockCramerWeight (X : ℝ) n| ≤
          Real.log (2 * (K : ℝ)) +
            Real.exp ((Real.log (2 * (K : ℝ))) ^ (1 / 10 : ℝ)) :=
      (abs_sub _ _).trans (add_le_add hLambdaAbs hcramer)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hrealabs.trans hU
  change I.sup' hI (fun n =>
    ‖((paperLambda n -
      paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)‖) ≤ _
  apply Finset.sup'_le
  intro n hn
  exact hpoint n hn

private theorem shortRemainderLocalFloorBound {c : ℝ} (hc : 1 < c)
    {K X H : ℕ} (hK : 3 ≤ K) (hX : K ≤ X) (hH : 0 < H)
    (hXH : X + H ≤ 2 * K)
    (hHupper : (H : ℝ) ≤ (K : ℝ) ^ (arithmeticParameters c).θ)
    (ξ : ℝ) (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (hM : 2 ≤ Nat.floor ((K : ℝ) ^ (arithmeticParameters c).η))
    (w : ℤ → ℂ) (R U : ℝ)
    (hCorr : polynomialCorrelation ((arithmeticParameters c).k + 1)
        (realIntegerInterval (X : ℝ) (H : ℝ)) w ≤ R)
    (hSup : polynomialCorrelationSupNorm
        (realIntegerInterval (X : ℝ) (H : ℝ)) w
        (shortRemainder_nonempty_interval hH) ≤ U) :
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase
          (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
      (12 * max 1
        (4 * Real.pi * |(descPochhammer ℝ
          ((arithmeticParameters c).k + 1)).eval c|)) *
        Real.log (2 * (K : ℝ)) *
          ((H : ℝ) * R + U *
            ((∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
                floorBoundaryKernel
                  (Nat.floor ((K : ℝ) ^ (arithmeticParameters c).η)) hM
                  ((n : ℝ) ^ c)) +
              (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) := by
  classical
  let I : Finset ℤ := realIntegerInterval (X : ℝ) (H : ℝ)
  let M : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).η)
  let S : ℂ := ∑ n ∈ I,
    w n * unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))
  let B : ℝ := ∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)
  have hI : I.Nonempty := shortRemainder_nonempty_interval hH
  have hcard : I.card = H := by
    simpa [I] using realIntegerInterval_nat_card X H
  have hcardR : (I.card : ℝ) = (H : ℝ) := by exact_mod_cast hcard
  have hHposR : 0 < (H : ℝ) := by exact_mod_cast hH
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : 0 < (K : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (2 * (K : ℝ)) :=
    Real.log_nonneg (by linarith [hKreal])
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun n hn => floorBoundaryKernel_nonneg M hM _
  have hBavg : 0 ≤ B / (H : ℝ) := div_nonneg hBnonneg hHposR.le
  have hKterm : 0 ≤ (K : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg hKpos.le _
  have hinside :
      polynomialCorrelation ((arithmeticParameters c).k + 1) I w +
        polynomialCorrelationSupNorm I w hI *
          (B / (H : ℝ) + (K : ℝ) ^ (-2 : ℝ)) ≤
      R + U * (B / (H : ℝ) + (K : ℝ) ^ (-2 : ℝ)) := by
    exact add_le_add hCorr (mul_le_mul_of_nonneg_right hSup
      (add_nonneg hBavg hKterm))
  let Cc : ℝ := 12 * max 1
    (4 * Real.pi * |(descPochhammer ℝ
      ((arithmeticParameters c).k + 1)).eval c|)
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hCcLog : 0 ≤ Cc * Real.log (2 * (K : ℝ)) := mul_nonneg hCc hlog
  have hlocal := localWeightedPolynomialReduction_of_cutoff_ge_two
    (c := c) (K := (K : ℝ)) (X := (X : ℝ)) (H := (H : ℝ)) (ξ := ξ)
    hc (by exact_mod_cast (by omega : 1 ≤ K)) (by exact_mod_cast hX)
    (by exact_mod_cast hH) (by exact_mod_cast hXH) hHupper hξlo hξhi
    hI w hM
  have hlocal' :
      ‖S / (I.card : ℂ)‖ ≤
        Cc * Real.log (2 * (K : ℝ)) *
          (polynomialCorrelation ((arithmeticParameters c).k + 1) I w +
            polynomialCorrelationSupNorm I w hI *
              (B / (H : ℝ) + (K : ℝ) ^ (-2 : ℝ))) := by
    simpa [I, M, S, B, Cc, hcardR] using hlocal
  have hlocalBound :
      ‖S / (I.card : ℂ)‖ ≤
        Cc * Real.log (2 * (K : ℝ)) *
          (R + U * (B / (H : ℝ) + (K : ℝ) ^ (-2 : ℝ))) :=
    hlocal'.trans (mul_le_mul_of_nonneg_left hinside hCcLog)
  have hdivNorm : ‖S / (I.card : ℂ)‖ = ‖S‖ / (H : ℝ) := by
    rw [norm_div]
    simp [hcard]
  have hnormScale : ‖S‖ = (H : ℝ) * ‖S / (I.card : ℂ)‖ := by
    rw [hdivNorm]
    field_simp
  calc
    _ = (H : ℝ) * ‖S / (I.card : ℂ)‖ := by simpa [S] using hnormScale
    _ ≤ (H : ℝ) *
        (Cc * Real.log (2 * (K : ℝ)) *
          (R + U * (B / (H : ℝ) + (K : ℝ) ^ (-2 : ℝ)))) :=
      mul_le_mul_of_nonneg_left hlocalBound hHposR.le
    _ = Cc * Real.log (2 * (K : ℝ)) *
        ((H : ℝ) * R + U * (B + (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) := by
      dsimp [Cc]
      field_simp [hHposR.ne']
      <;> ring
    _ = _ := by
      simp [Cc, B, I, M]

private theorem shortRemainderTrivialBlockBound {c : ℝ}
    {K X H : ℕ} (hH : 0 < H) (ξ : ℝ) (w : ℤ → ℂ)
    (hSup : polynomialCorrelationSupNorm
      (realIntegerInterval (X : ℝ) (H : ℝ)) w
      (shortRemainder_nonempty_interval hH) ≤
        shortRemainderSizeFactor (K : ℝ)) :
    ‖∑ n ∈ Finset.Ico (X + 1) (X + H + 1),
        w (n : ℤ) * unitFrequencyPhase
          (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
      (H : ℝ) * shortRemainderSizeFactor (K : ℝ) := by
  classical
  let I : Finset ℤ := realIntegerInterval (X : ℝ) (H : ℝ)
  have hI : I.Nonempty := shortRemainder_nonempty_interval hH
  have hpoint : ∀ n ∈ I,
      ‖w n * unitFrequencyPhase
        (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
        shortRemainderSizeFactor (K : ℝ) := by
    intro n hn
    have hweight := norm_le_polynomialCorrelationSupNorm (I := I) (w := w) hI hn
    have hphase := norm_unitFrequencyPhase
      (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))
    rw [norm_mul, hphase]
    have hweight' := hweight.trans hSup
    simpa using hweight'
  have hnorm :
      ‖∑ n ∈ I, w n * unitFrequencyPhase
        (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
        ∑ n ∈ I, shortRemainderSizeFactor (K : ℝ) := by
    calc
      _ ≤ ∑ n ∈ I, ‖w n * unitFrequencyPhase
          (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ I, shortRemainderSizeFactor (K : ℝ) :=
        Finset.sum_le_sum hpoint
  have hsumConst :
      (∑ _n ∈ I, shortRemainderSizeFactor (K : ℝ)) =
        (H : ℝ) * shortRemainderSizeFactor (K : ℝ) := by
    simp [I, Finset.sum_const, nsmul_eq_mul, realIntegerInterval_nat_card,
      mul_comm]
  have hconvert :
      (∑ n ∈ Finset.Ico (X + 1) (X + H + 1),
        w (n : ℤ) * unitFrequencyPhase
          (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) =
      ∑ n ∈ I, w n * unitFrequencyPhase
        (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)) := by
    dsimp [I]
    symm
    exact shortRemainderRealInterval_sum_eq_natBlockIco X H
      (fun n => w n * unitFrequencyPhase
        (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)))
  rw [hconvert]
  exact hnorm.trans_eq hsumConst

private theorem shortRemainderTrivialBlockSums {c : ℝ}
    {K K' : ℕ} (hK : 3 ≤ K) (hKK' : K ≤ K') (hK'2 : K' ≤ 2 * K)
    (ξ : ℝ) :
    let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
    let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
    (∑ v ∈ Finset.range q,
      ‖∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
        (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
          (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
      (K : ℝ) * shortRemainderSizeFactor (K : ℝ) ∧
    (∑ v ∈ Finset.range q,
      ‖∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H),
        ((paperLambda (n : ℤ) -
          paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ) (n : ℤ) : ℝ) : ℂ) *
          unitFrequencyPhase
            (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
      (K : ℝ) * shortRemainderSizeFactor (K : ℝ) := by
  classical
  dsimp only
  let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
  let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
  let U : ℝ := shortRemainderSizeFactor (K : ℝ)
  have hUpos : 0 ≤ U := by
    have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hlog : 0 ≤ Real.log (2 * (K : ℝ)) :=
      Real.log_nonneg (by linarith [hKreal])
    dsimp [U, shortRemainderSizeFactor]
    positivity
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
    have hmuBlock : ∀ v ∈ Finset.range q,
        ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H),
          (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
            (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
          (H : ℝ) * U := by
      intro v hv
      have hvlt : v < q := Finset.mem_range.mp hv
      let Xv : ℕ := K + v * H
      have hstep : v * H + H ≤ q * H := by
        have h := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hvlt)
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using h
      have hXvH : Xv + H ≤ 2 * K := by
        have hXvH' : Xv + H = K + (v * H + H) := by
          dsimp [Xv]
          omega
        calc
          Xv + H = K + (v * H + H) := hXvH'
          _ ≤ K + q * H := Nat.add_le_add_left hstep K
          _ ≤ K + (K' - K) := Nat.add_le_add_left hqH K
          _ = K' := by omega
          _ ≤ 2 * K := hK'2
      have hXvK : K ≤ Xv := by dsimp [Xv]; omega
      have hXv2 : Xv ≤ 2 * K := le_trans (Nat.le_add_right Xv H) hXvH
      have hsup := shortRemainder_mobius_sup_le hK hXvK hHpos
      have htrivial := shortRemainderTrivialBlockBound
        (c := c) (K := K) (X := Xv) (H := H) hHpos ξ
        (fun n => (paperMu n : ℂ)) hsup
      have hset := shortRemainder_blockIco_eq K H v
      rw [hset]
      simpa [U] using htrivial
    have hlambdaBlock : ∀ v ∈ Finset.range q,
        ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H),
          ((paperLambda (n : ℤ) -
            paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ)
              (n : ℤ) : ℝ) : ℂ) * unitFrequencyPhase
            (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
          (H : ℝ) * U := by
      intro v hv
      have hvlt : v < q := Finset.mem_range.mp hv
      let Xv : ℕ := K + v * H
      have hstep : v * H + H ≤ q * H := by
        have h := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hvlt)
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using h
      have hXvH : Xv + H ≤ 2 * K := by
        have hXvH' : Xv + H = K + (v * H + H) := by
          dsimp [Xv]
          omega
        calc
          Xv + H = K + (v * H + H) := hXvH'
          _ ≤ K + q * H := Nat.add_le_add_left hstep K
          _ ≤ K + (K' - K) := Nat.add_le_add_left hqH K
          _ = K' := by omega
          _ ≤ 2 * K := hK'2
      have hXvK : K ≤ Xv := by dsimp [Xv]; omega
      have hXv2 : Xv ≤ 2 * K := le_trans (Nat.le_add_right Xv H) hXvH
      have hsup := shortRemainder_lambdaModel_sup_le hK hXvK hXv2 hHpos hXvH
      have htrivial := shortRemainderTrivialBlockBound
        (c := c) (K := K) (X := Xv) (H := H) hHpos ξ
        (fun n => ((paperLambda n -
          paperShortBlockCramerWeight (Xv : ℝ) n : ℝ) : ℂ)) hsup
      have hset := shortRemainder_blockIco_eq K H v
      rw [hset]
      simpa [U, Xv] using htrivial
    constructor
    · calc
        _ ≤ ∑ v ∈ Finset.range q, (H : ℝ) * U :=
          Finset.sum_le_sum hmuBlock
        _ = (q : ℝ) * (H : ℝ) * U := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
        _ ≤ (K : ℝ) * U :=
          mul_le_mul_of_nonneg_right hqKreal hUpos
    · calc
        _ ≤ ∑ v ∈ Finset.range q, (H : ℝ) * U :=
          Finset.sum_le_sum hlambdaBlock
        _ = (q : ℝ) * (H : ℝ) * U := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
        _ ≤ (K : ℝ) * U :=
          mul_le_mul_of_nonneg_right hqKreal hUpos
  · have hHzero : H = 0 := by omega
    have hqzero : q = 0 := by
      dsimp [q]
      rw [natFloor_div_natCast_eq_div]
      simp [H, hHzero]
    simp [H, q, hHzero]
    exact mul_nonneg (by positivity) (by simpa [U] using hUpos)

private theorem arithmeticParameters_eta_eq_source (c : ℝ) :
    (arithmeticParameters c).η = (1 / 100 : ℝ) /
      (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) := by
  simp only [arithmeticParameters]
  congr 2
  norm_cast

private theorem shortRemainder_log_ratio_bound {K X A : ℝ}
    (hK : 3 ≤ K) (hX : K ≤ X) (hA : 0 < A) :
    Real.log (2 * K) * (Real.log X) ^ (-(A + 2)) ≤
      2 * (Real.log K) ^ (-A) := by
  have hKpos : 0 < K := by linarith
  have hXpos : 0 < X := by linarith
  have hlogKpos : 0 < Real.log K := Real.log_pos (by linarith)
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogKge1 : 1 ≤ Real.log K := by
    have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
    exact le_trans hlog3.le (Real.log_le_log (by norm_num) hK)
  have hlogXgeK : Real.log K ≤ Real.log X :=
    Real.log_le_log (by linarith) hX
  have hlog2le1 : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_two_lt_d9]
  have hlog2K : Real.log (2 * K) ≤ 2 * Real.log K := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hKpos.ne']
    nlinarith
  have hposExp : 0 < A + 2 := by linarith
  have hpow : (Real.log K) ^ (A + 2) ≤ (Real.log X) ^ (A + 2) :=
    Real.rpow_le_rpow hlogKpos.le hlogXgeK hposExp.le
  have hnegpow : (Real.log X) ^ (-(A + 2)) ≤
      (Real.log K) ^ (-(A + 2)) := by
    rw [Real.rpow_neg hlogXpos.le, Real.rpow_neg hlogKpos.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hlogXpos (A + 2))
      (Real.rpow_pos_of_pos hlogKpos (A + 2))).2 hpow
  calc
    Real.log (2 * K) * (Real.log X) ^ (-(A + 2)) ≤
        (2 * Real.log K) * (Real.log K) ^ (-(A + 2)) :=
      mul_le_mul hlog2K hnegpow
        (Real.rpow_nonneg hlogXpos.le _) (by positivity)
    _ = 2 * ((Real.log K) ^ (1 : ℝ) *
        (Real.log K) ^ (-(A + 2))) := by rw [Real.rpow_one]; ring
    _ = 2 * (Real.log K) ^ (1 + (-(A + 2))) := by
      rw [← Real.rpow_add hlogKpos]
    _ = 2 * (Real.log K) ^ (-A - 1) := by congr 2 <;> ring
    _ ≤ 2 * (Real.log K) ^ (-A) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlogKge1 (by linarith))
        (by norm_num)

/-- The complete source size factor in `ar:short-remainder` is eventually
absorbed by the spare `K^(η/4)` power. This keeps the exact cutoff
`exp((log(2K))^(1/10))` in the statement. -/
theorem exists_shortRemainder_UK_log_power {c : ℝ} (hc : 1 < c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ K₀ : ℝ, 3 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      (1 + Real.log (2 * K) +
        Real.exp ((Real.log (2 * K)) ^ (1 / 10 : ℝ))) *
          Real.log (2 * K) ≤ K ^ (η / 4) := by
  dsimp only
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  have hηpos : 0 < η := by dsimp [η, j]; positivity
  let δ : ℝ := η / 32
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hlogEvent := eventually_log_le_rpow_of_pos hδpos
  have hexpEvent := eventually_exp_log_tenth_le_rpow_of_pos hδpos
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
    (Filter.Eventually.and hlogEvent hexpEvent)
  obtain ⟨Kpow, hKpow, hlargeKpow⟩ :=
    exists_real_rpow_threshold (C := 3 * (2 : ℝ) ^ (η / 16))
      (s := 3 * η / 16) (by positivity)
  let K₀ : ℝ := max 3 (max B Kpow)
  have hK₀ : 3 ≤ K₀ := by dsimp [K₀]; exact le_max_left _ _
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK
  have hKge : 3 ≤ K := le_trans hK₀ hK
  have hKpos : 0 < K := by linarith
  have hBtwo : B ≤ 2 * K := by
    have hmax : max B Kpow ≤ K := by
      dsimp [K₀] at hK
      exact le_trans (le_max_right _ _) hK
    exact le_trans (le_trans (le_max_left _ _) hmax) (by linarith)
  have hKpow' : Kpow ≤ K := by
    have hK' : max B Kpow ≤ K := by
      dsimp [K₀] at hK
      exact le_trans (le_max_right _ _) hK
    exact le_trans (le_max_right _ _) hK'
  have hsource := hB (2 * K) hBtwo
  rcases hsource with ⟨hlog, hexp⟩
  have hlogpos : 0 ≤ Real.log (2 * K) := Real.log_nonneg (by linarith [hKge])
  have hpowpos : 1 ≤ (2 * K) ^ δ := Real.one_le_rpow (by linarith [hKge]) hδpos.le
  have hU : 1 + Real.log (2 * K) +
      Real.exp ((Real.log (2 * K)) ^ (1 / 10 : ℝ)) ≤ 3 * (2 * K) ^ δ := by
    nlinarith [hlog, hexp, hpowpos]
  have hprod :
      (1 + Real.log (2 * K) +
        Real.exp ((Real.log (2 * K)) ^ (1 / 10 : ℝ))) *
          Real.log (2 * K) ≤ 3 * (2 * K) ^ (2 * δ) := by
    calc
      _ ≤ (3 * (2 * K) ^ δ) * (2 * K) ^ δ :=
        mul_le_mul hU hlog hlogpos (by positivity)
      _ = 3 * (2 * K) ^ (2 * δ) := by
        calc
          3 * (2 * K) ^ δ * (2 * K) ^ δ =
              3 * ((2 * K) ^ δ * (2 * K) ^ δ) := by ring
          _ = 3 * (2 * K) ^ (δ + δ) := by
            rw [← Real.rpow_add (by linarith [hKge])]
          _ = 3 * (2 * K) ^ (2 * δ) := by congr 2 <;> ring
  have hKscale : 3 * (2 : ℝ) ^ (η / 16) ≤ K ^ (3 * η / 16) := by
    exact hlargeKpow K hKpow'
  have hconvert :
      3 * (2 * K) ^ (2 * δ) ≤ K ^ (η / 4) := by
    have hmulrpow : (2 * K) ^ (2 * δ) = (2 : ℝ) ^ (2 * δ) * K ^ (2 * δ) :=
      Real.mul_rpow (by norm_num) hKpos.le
    rw [show 2 * δ = η / 16 by dsimp [δ]; ring] at hmulrpow ⊢
    rw [hmulrpow]
    calc
      3 * ((2 : ℝ) ^ (η / 16) * K ^ (η / 16)) =
          (3 * (2 : ℝ) ^ (η / 16)) * K ^ (η / 16) := by ring
      _ ≤ K ^ (3 * η / 16) * K ^ (η / 16) :=
        mul_le_mul_of_nonneg_right hKscale (by positivity)
      _ = K ^ (η / 4) := by
        rw [← Real.rpow_add hKpos]
        congr 1
        ring
  exact hprod.trans hconvert


theorem arithmeticShortRemainderOf_MUF_DP_PTW {c : ℝ} (hc : 1 < c)
    (hcNon : NonIntegral c)
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    (hDP : FractionalPrimes.Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : FractionalPrimes.Literature.Polynomial.restrictedPolynomialTwistedTask)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, 3 ≤ K₀ ∧
      ∀ K K' : ℕ, K₀ ≤ K → K ≤ K' → K' ≤ 2 * K →
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
  let p := arithmeticParameters c
  have hη : 0 < p.η ∧ p.η < 1 := by
    simpa [p] using arithmeticParameters_eta_pos_lt_one hc
  have hγ : 0 < p.η / 4 := div_pos hη.1 (by norm_num)
  have hηsource : p.η =
      (1 / 100 : ℝ) /
        (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
          (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) := by
    simpa [p] using arithmeticParameters_eta_eq_source c
  obtain ⟨Cuniform, hCuniform, hUniform⟩ :=
    shortBlockPolynomialCorrelationsOf_MUF_DP_PTW hc hMUF hDP hPTW
      (A + 2) (by linarith)
  let Cc : ℝ := 12 * max 1
    (4 * Real.pi * |(descPochhammer ℝ (p.k + 1)).eval c|)
  let Cbig : ℝ := Cc * (2 * Cuniform + 25)
  have hCc : 0 < Cc := by dsimp [Cc]; positivity
  have hCbig : 0 < Cbig := by
    dsimp [Cbig]
    positivity
  obtain ⟨Kscale, hKscale0, hScale⟩ :=
    exists_arithmetic_shortBlock_scale_package hc
  obtain ⟨Kagg, hKagg0, hAggregation⟩ :=
    exists_arithmetic_fullBlock_nonnegative_sum_le hc
  obtain ⟨Kfloor, hFloor⟩ :=
    exists_natFloor_rpow_block_threshold (arithmeticParameters_theta_pos hc)
  obtain ⟨KboundR, hKboundR0, hBoundary⟩ :=
    fixedCutoffBoundaryPrefix hc hcNon
  obtain ⟨KukR, hKukR0, hUK⟩ := exists_shortRemainder_UK_log_power hc
  obtain ⟨KdecR, hKdecR0, hDecay⟩ :=
    exists_rpow_decay_beats_log_power hγ
  let Kbound : ℕ := Nat.ceil KboundR
  let Kuk : ℕ := Nat.ceil KukR
  let Kdec : ℕ := Nat.ceil KdecR
  have hKboundCast : KboundR ≤ (Kbound : ℝ) := by
    exact_mod_cast (Nat.le_ceil KboundR)
  have hKukCast : KukR ≤ (Kuk : ℝ) := by
    exact_mod_cast (Nat.le_ceil KukR)
  have hKdecCast : KdecR ≤ (Kdec : ℝ) := by
    exact_mod_cast (Nat.le_ceil KdecR)
  have hKbound3 : 3 ≤ Kbound := by
    exact_mod_cast hKboundR0.trans hKboundCast
  have hKuk3 : 3 ≤ Kuk := by
    exact_mod_cast hKukR0.trans hKukCast
  have hKdec3 : 3 ≤ Kdec := by
    exact_mod_cast hKdecR0.trans hKdecCast
  let Karith : ℕ := max Kscale (max Kagg Kfloor)
  let Kreal : ℕ := max Kbound (max Kuk Kdec)
  let Kbase : ℕ := max Karith Kreal
  let K₀ : ℕ := max 3 Kbase
  have hK₀ : 3 ≤ K₀ := by dsimp [K₀]; exact le_max_left _ _
  refine ⟨Cbig, hCbig, K₀, hK₀, ?_⟩
  intro K K' hK₀K hKK' hK'2 ξ hξlo hξhi
  dsimp only
  let H : ℕ := Nat.floor ((K : ℝ) ^ p.θ)
  let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
  by_cases hKlarge : K₀ ≤ K
  · have hKbase : Kbase ≤ K := by
      dsimp [K₀] at hKlarge
      exact le_trans (le_max_right _ _) hKlarge
    have hKarith : Karith ≤ K := le_trans (le_max_left _ _) hKbase
    have hKreal : Kreal ≤ K := le_trans (le_max_right _ _) hKbase
    have hKscale : Kscale ≤ K := le_trans (le_max_left _ _) hKarith
    have hKagg : Kagg ≤ K := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hKarith)
    have hKfloor : Kfloor ≤ K := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hKarith)
    have hKbound : Kbound ≤ K := le_trans (le_max_left _ _) hKreal
    have hKuk : Kuk ≤ K := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hKreal)
    have hKdec : Kdec ≤ K := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hKreal)
    have hKboundReal : KboundR ≤ (K : ℝ) :=
      hKboundCast.trans (by exact_mod_cast hKbound)
    have hKukReal : KukR ≤ (K : ℝ) := hKukCast.trans (by exact_mod_cast hKuk)
    have hKdecReal : KdecR ≤ (K : ℝ) := hKdecCast.trans (by exact_mod_cast hKdec)
    have hKreal3 : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (hK₀.trans hK₀K)
    have hKnat3 : 3 ≤ K := by exact_mod_cast hKreal3
    have hHpos : 0 < H := by
      have h := hFloor K hKfloor
      simpa [H, p] using h.1
    have hHupper : (H : ℝ) ≤ (K : ℝ) ^ p.θ := by
      dsimp [H]
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    let M : ℕ := Nat.floor ((K : ℝ) ^ p.η)
    have hBoundaryAt := hBoundary (K : ℝ) hKboundReal
    dsimp only at hBoundaryAt
    rcases hBoundaryAt with ⟨hMsource, hBoundaryAvgSource⟩
    have hM : 2 ≤ M := by
      simpa [M, p, hηsource] using hMsource
    have hBoundaryAvg :
        (1 / (2 * (K : ℝ))) *
          (∑ n ∈ realIntegerInterval 0 (2 * (K : ℝ)),
            floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤
          12 * (2 * (K : ℝ)) ^ (-p.η / 2) := by
      simpa [M, p, hηsource] using hBoundaryAvgSource
    have h2Kpos : 0 < 2 * (K : ℝ) := by positivity
    have hBoundarySum :
        (∑ n ∈ realIntegerInterval 0 (2 * (K : ℝ)),
          floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤
          12 * (2 * (K : ℝ)) * (2 * (K : ℝ)) ^ (-p.η / 2) := by
      calc
        _ = (2 * (K : ℝ)) *
            ((1 / (2 * (K : ℝ))) *
              ∑ n ∈ realIntegerInterval 0 (2 * (K : ℝ)),
                floorBoundaryKernel M hM ((n : ℝ) ^ c)) := by
                  field_simp
        _ ≤ (2 * (K : ℝ)) *
            (12 * (2 * (K : ℝ)) ^ (-p.η / 2)) :=
          mul_le_mul_of_nonneg_left hBoundaryAvg h2Kpos.le
        _ = 12 * (2 * (K : ℝ)) *
            (2 * (K : ℝ)) ^ (-p.η / 2) := by ring
    have hUKAt := hUK (K : ℝ) hKukReal
    have hUKbound :
        shortRemainderSizeFactor (K : ℝ) * Real.log (2 * (K : ℝ)) ≤
          (K : ℝ) ^ (p.η / 4) := by
      simpa [shortRemainderSizeFactor, p, hηsource] using hUKAt
    have hDecayAt := hDecay (K : ℝ) hKdecReal
    have hDecayBound :
        (K : ℝ) ^ (1 - p.η / 4) ≤
          (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      simpa [p] using hDecayAt
    have hscaleAt := hScale K hKscale K' hKK' hK'2
    dsimp only at hscaleAt
    rcases hscaleAt with ⟨_hrscale, _hqscale, hblocks⟩
    have hAggAt := hAggregation K hKagg K' hKK' hK'2
    dsimp only at hAggAt
    have hqeq : q = (K' - K) / H := by
      dsimp [q]
      exact natFloor_div_natCast_eq_div _ _
    have hqH : q * H ≤ K' - K := by
      rw [hqeq]
      exact Nat.div_mul_le_self _ _
    have hqK : q * H ≤ K := le_trans hqH (by omega)
    have hqKreal : (q : ℝ) * (H : ℝ) ≤ (K : ℝ) := by exact_mod_cast hqK
    let f : ℕ → ℝ := fun n =>
      floorBoundaryKernel M hM ((n : ℝ) ^ c)
    have hf : ∀ n, 0 ≤ f n := by
      intro n
      exact floorBoundaryKernel_nonneg M hM ((n : ℝ) ^ c)
    have hAggBoundary := hAggAt f hf
    have hsubset :
        Finset.Ico (K + 1) (K' + 1) ⊆ Finset.Ico 1 (2 * K + 1) := by
      intro n hn
      simp only [Finset.mem_Ico] at hn ⊢
      omega
    have hprefixNat := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro n _ht _hnot
      exact hf n)
    have hrealNat :
        (∑ n ∈ realIntegerInterval 0 (2 * (K : ℝ)),
          floorBoundaryKernel M hM ((n : ℝ) ^ c)) =
          ∑ n ∈ Finset.Ico 1 (2 * K + 1), f n := by
      simpa [f] using
        shortRemainderRealInterval_sum_eq_natBlockIco 0 (2 * K)
          (fun n => floorBoundaryKernel M hM ((n : ℝ) ^ c))
    have hBoundaryBlocks :
        (∑ v ∈ Finset.range q,
          ∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H), f n) ≤
          12 * (2 * (K : ℝ)) * (2 * (K : ℝ)) ^ (-p.η / 2) := by
      calc
        _ ≤ ∑ n ∈ Finset.Ico (K + 1) (K' + 1), f n := hAggBoundary
        _ ≤ ∑ n ∈ Finset.Ico 1 (2 * K + 1), f n := hprefixNat
        _ = ∑ n ∈ realIntegerInterval 0 (2 * (K : ℝ)),
              floorBoundaryKernel M hM ((n : ℝ) ^ c) := hrealNat.symm
        _ ≤ 12 * (2 * (K : ℝ)) * (2 * (K : ℝ)) ^ (-p.η / 2) := hBoundarySum
    let L : ℝ := Real.log (2 * (K : ℝ))
    let U : ℝ := shortRemainderSizeFactor (K : ℝ)
    let Lp : ℝ := (Real.log (K : ℝ)) ^ (-(A + 2))
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      exact Real.log_nonneg (by linarith [hKreal3])
    have hUnonneg : 0 ≤ U := by
      dsimp [U, shortRemainderSizeFactor]
      have hlognonneg : 0 ≤ Real.log (2 * (K : ℝ)) := hLnonneg
      positivity
    have hBsumNonneg : 0 ≤
        ∑ v ∈ Finset.range q,
          ∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H), f n :=
      Finset.sum_nonneg fun v hv => Finset.sum_nonneg (by
        intro n hn
        exact hf n)
    have hKlog : 0 < Real.log (K : ℝ) := Real.log_pos (by linarith [hKreal3])
    have hKlogge1 : 1 ≤ Real.log (K : ℝ) := by
      have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
      exact le_trans hlog3.le (Real.log_le_log (by norm_num) hKreal3)
    have hlogratio :
        L * Lp ≤ 2 * (Real.log (K : ℝ)) ^ (-A) := by
      simpa [L, Lp] using
        shortRemainder_log_ratio_bound hKreal3 (by linarith) hA
    have hUKL : U * L ≤ (K : ℝ) ^ (p.η / 4) := by
      simpa [U, L] using hUKbound
    have hHposR : 0 < (H : ℝ) := by exact_mod_cast hHpos
    have hKpos : 0 < (K : ℝ) := by linarith
    have hBvEq : ∀ v : ℕ,
        (∑ n ∈ realIntegerInterval ((K + v * H : ℕ) : ℝ) (H : ℝ),
          floorBoundaryKernel M hM ((n : ℝ) ^ c)) =
        ∑ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H), f n := by
      intro v
      have hset := shortRemainder_blockIco_eq K H v
      calc
        _ = ∑ n ∈ Finset.Ico (K + v * H + 1)
              (K + v * H + H + 1), f n := by
          simpa [f] using
            (shortRemainderRealInterval_sum_eq_natBlockIco
              (K + v * H) H
              (fun n => floorBoundaryKernel M hM ((n : ℝ) ^ c)))
        _ = ∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H), f n := by rw [← hset]
    have hBlockCommon : ∀ v ∈ Finset.range q,
        ∀ w : ℤ → ℂ,
          polynomialCorrelation ((p.k + 1))
              (realIntegerInterval ((K + v * H : ℕ) : ℝ) (H : ℝ)) w ≤
            Cuniform * ((Real.log ((K + v * H : ℕ) : ℝ)) ^ (-(A + 2))) →
          polynomialCorrelationSupNorm
              (realIntegerInterval ((K + v * H : ℕ) : ℝ) (H : ℝ)) w
              (shortRemainder_nonempty_interval hHpos) ≤ U →
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H),
            w (n : ℤ) * unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
            Cc * L *
              ((H : ℝ) * Cuniform * Lp + U *
                ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                    (K + 1 + (v + 1) * H), f n) +
                  (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) := by
      intro v hv w hCorr hSup
      let Xv : ℕ := K + v * H
      have hvlt := Finset.mem_range.mp hv
      have hstep : v * H + H ≤ q * H := by
        have h := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hvlt)
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using h
      have hXvH : Xv + H ≤ 2 * K := by
        have hXvH' : Xv + H = K + (v * H + H) := by
          dsimp [Xv]
          omega
        calc
          Xv + H = K + (v * H + H) := hXvH'
          _ ≤ K + q * H := Nat.add_le_add_left hstep K
          _ ≤ K + (K' - K) := Nat.add_le_add_left hqH K
          _ = K' := by omega
          _ ≤ 2 * K := hK'2
      have hXvK : K ≤ Xv := by dsimp [Xv]; omega
      have hXv2 : Xv ≤ 2 * K := le_trans (Nat.le_add_right Xv H) hXvH
      have hXv3 : 3 ≤ Xv := le_trans (by omega : 3 ≤ K) hXvK
      have hblockBounds := hblocks v hvlt
      rcases hblockBounds with ⟨hLower, hUpper, _hCut, _hTaylor⟩
      have hCorrData := hUniform Xv H hXv3 hLower hUpper
      let Rv : ℝ := Cuniform *
        (Real.log (Xv : ℝ)) ^ (-(A + 2))
      have hCorr' : polynomialCorrelation (p.k + 1)
          (realIntegerInterval (Xv : ℝ) (H : ℝ)) w ≤ Rv := by
        dsimp [Rv]
        exact hCorr
      have hSup' : polynomialCorrelationSupNorm
          (realIntegerInterval (Xv : ℝ) (H : ℝ)) w
          (shortRemainder_nonempty_interval hHpos) ≤ U := hSup
      have hLocal := shortRemainderLocalFloorBound hc
        hKnat3 hXvK hHpos hXvH hHupper ξ hξlo hξhi hM w Rv U hCorr' hSup'
      have hLocal' := hLocal
      rw [hBvEq v] at hLocal'
      have hlogXv : Real.log (K : ℝ) ≤ Real.log (Xv : ℝ) :=
        Real.log_le_log (by linarith [hKreal3])
          (show (K : ℝ) ≤ (Xv : ℝ) by exact_mod_cast hXvK)
      have hRatio := shortRemainder_log_ratio_bound hKreal3
        (show (K : ℝ) ≤ (Xv : ℝ) by exact_mod_cast hXvK) hA
      have hRvBound :
          Rv ≤ Cuniform * Lp := by
        dsimp [Rv, Lp]
        have hlogKpos : 0 < Real.log (K : ℝ) := hKlog
        have hlogXpos : 0 < Real.log (Xv : ℝ) :=
          lt_of_lt_of_le hKlog hlogXv
        have hpow : (Real.log (K : ℝ)) ^ (A + 2) ≤
            (Real.log (Xv : ℝ)) ^ (A + 2) :=
          Real.rpow_le_rpow hlogKpos.le hlogXv (by linarith)
        have hneg : (Real.log (Xv : ℝ)) ^ (-(A + 2)) ≤
            (Real.log (K : ℝ)) ^ (-(A + 2)) := by
          rw [Real.rpow_neg hlogXpos.le, Real.rpow_neg hlogKpos.le]
          exact (inv_le_inv₀
            (Real.rpow_pos_of_pos hlogXpos (A + 2))
            (Real.rpow_pos_of_pos hlogKpos (A + 2))).2 hpow
        exact mul_le_mul_of_nonneg_left hneg (le_of_lt hCuniform)
      have hHnonneg : 0 ≤ (H : ℝ) := by positivity
      have hinside :
          (H : ℝ) * Rv + U *
              ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n) +
                (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)) ≤
          (H : ℝ) * Cuniform * Lp + U *
              ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n) +
                (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)) := by
        calc
          _ ≤ (H : ℝ) * (Cuniform * Lp) + U *
                ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                    (K + 1 + (v + 1) * H), f n) +
                  (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left hRvBound hHnonneg) le_rfl
          _ = _ := by ring
      have hCoeff : 0 ≤ Cc * L := mul_nonneg (le_of_lt hCc) hLnonneg
      have hCommon := hLocal'.trans
        (mul_le_mul_of_nonneg_left hinside hCoeff)
      have hlogScale : (Real.log (K : ℝ)) ^ (-(A + 2)) = Lp := by
        rfl
      have hsumConvert :
          (∑ n ∈ realIntegerInterval (Xv : ℝ) (H : ℝ),
            w n * unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) =
          ∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H),
            w (n : ℤ) * unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)) := by
        calc
          _ = ∑ n ∈ Finset.Ico (Xv + 1) (Xv + H + 1),
              w (n : ℤ) * unitFrequencyPhase
                (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)) := by
            simpa using shortRemainderRealInterval_sum_eq_natBlockIco Xv H
              (fun n => w n * unitFrequencyPhase
                (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)))
          _ = _ := by
            rw [← shortRemainder_blockIco_eq K H v]
      rw [hsumConvert] at hCommon
      simpa [Xv, Rv, U, L, Lp, hlogScale] using hCommon
    -- The two source weights have the same uniform polynomial-correlation bound.
    have hMuBlock : ∀ v ∈ Finset.range q,
        ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H),
          (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
            (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
          Cc * L *
            ((H : ℝ) * Cuniform * Lp + U *
              ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n) +
                (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) := by
      intro v hv
      let Xv : ℕ := K + v * H
      have hvlt := Finset.mem_range.mp hv
      have hstep : v * H + H ≤ q * H := by
        have h := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hvlt)
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using h
      have hXvH : Xv + H ≤ 2 * K := by
        have hXvH' : Xv + H = K + (v * H + H) := by dsimp [Xv]; omega
        calc
          Xv + H = K + (v * H + H) := hXvH'
          _ ≤ K + q * H := Nat.add_le_add_left hstep K
          _ ≤ K + (K' - K) := Nat.add_le_add_left hqH K
          _ = K' := by omega
          _ ≤ 2 * K := hK'2
      have hXvK : K ≤ Xv := by dsimp [Xv]; omega
      have hXv2 : Xv ≤ 2 * K := le_trans (Nat.le_add_right Xv H) hXvH
      have hsup := shortRemainder_mobius_sup_le hKnat3 hXvK hHpos
      have hCorrData := hUniform Xv H (by exact le_trans (by omega) hXvK)
        (by
          have hblockBounds := hblocks v hvlt
          exact hblockBounds.1)
        (by
          have hblockBounds := hblocks v hvlt
          exact hblockBounds.2.1)
      let Rv : ℝ := Cuniform * (Real.log (Xv : ℝ)) ^ (-(A + 2))
      have hCorr : polynomialCorrelation (p.k + 1)
          (realIntegerInterval (Xv : ℝ) (H : ℝ)) (fun n => (paperMu n : ℂ)) ≤ Rv := by
        dsimp [Rv]
        exact hCorrData.1
      have hSup : polynomialCorrelationSupNorm
          (realIntegerInterval (Xv : ℝ) (H : ℝ)) (fun n => (paperMu n : ℂ))
          (shortRemainder_nonempty_interval hHpos) ≤ U := by
        simpa [U] using hsup
      exact hBlockCommon v hv (fun n => (paperMu n : ℂ)) hCorr hSup
    have hLambdaBlock : ∀ v ∈ Finset.range q,
        ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H),
          ((paperLambda (n : ℤ) -
            paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ)
              (n : ℤ) : ℝ) : ℂ) * unitFrequencyPhase
            (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
          Cc * L *
            ((H : ℝ) * Cuniform * Lp + U *
              ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n) +
                (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) := by
      intro v hv
      let Xv : ℕ := K + v * H
      have hvlt := Finset.mem_range.mp hv
      have hstep : v * H + H ≤ q * H := by
        have h := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hvlt)
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using h
      have hXvH : Xv + H ≤ 2 * K := by
        have hXvH' : Xv + H = K + (v * H + H) := by dsimp [Xv]; omega
        calc
          Xv + H = K + (v * H + H) := hXvH'
          _ ≤ K + q * H := Nat.add_le_add_left hstep K
          _ ≤ K + (K' - K) := Nat.add_le_add_left hqH K
          _ = K' := by omega
          _ ≤ 2 * K := hK'2
      have hXvK : K ≤ Xv := by dsimp [Xv]; omega
      have hXv2 : Xv ≤ 2 * K := le_trans (Nat.le_add_right Xv H) hXvH
      have hsup := shortRemainder_lambdaModel_sup_le hKnat3 hXvK hXv2 hHpos hXvH
      have hCorrData := hUniform Xv H (by exact le_trans (by omega) hXvK)
        (by
          have hblockBounds := hblocks v hvlt
          exact hblockBounds.1)
        (by
          have hblockBounds := hblocks v hvlt
          exact hblockBounds.2.1)
      let Rv : ℝ := Cuniform * (Real.log (Xv : ℝ)) ^ (-(A + 2))
      have hCorr : polynomialCorrelation (p.k + 1)
          (realIntegerInterval (Xv : ℝ) (H : ℝ))
          (fun n => ((paperLambda n -
            paperShortBlockCramerWeight (Xv : ℝ) n : ℝ) : ℂ)) ≤ Rv := by
        dsimp [Rv]
        exact hCorrData.2
      have hSup : polynomialCorrelationSupNorm
          (realIntegerInterval (Xv : ℝ) (H : ℝ))
          (fun n => ((paperLambda n -
            paperShortBlockCramerWeight (Xv : ℝ) n : ℝ) : ℂ))
          (shortRemainder_nonempty_interval hHpos) ≤ U := by
        simpa [U] using hsup
      simpa [Xv] using
        (hBlockCommon v hv
          (fun n => ((paperLambda n -
            paperShortBlockCramerWeight (Xv : ℝ) n : ℝ) : ℂ)) hCorr hSup)
    have hsumConst :
        (∑ v ∈ Finset.range q, (H : ℝ) * Cuniform * Lp) =
          (q : ℝ) * (H : ℝ) * Cuniform * Lp := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    have hsumErrorConst :
        (∑ v ∈ Finset.range q, (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)) =
          (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    have hsumError :
        (∑ v ∈ Finset.range q,
          U * ((∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H), f n) +
            (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) =
          U * ((∑ v ∈ Finset.range q,
                ∑ n ∈ Finset.Ico (K + 1 + v * H)
                    (K + 1 + (v + 1) * H), f n) +
              (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsumErrorConst]
    have hsumBlockFormula :
        (∑ v ∈ Finset.range q,
          ((H : ℝ) * Cuniform * Lp + U *
            ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                (K + 1 + (v + 1) * H), f n) +
              (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)))) =
          (q : ℝ) * (H : ℝ) * Cuniform * Lp +
            U * ((∑ v ∈ Finset.range q,
                  ∑ n ∈ Finset.Ico (K + 1 + v * H)
                      (K + 1 + (v + 1) * H), f n) +
                (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)) := by
      rw [Finset.sum_add_distrib, hsumConst, hsumError]
    have hsumMuCommon :
        (∑ v ∈ Finset.range q,
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H),
            (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
          Cc * L *
            ((q : ℝ) * (H : ℝ) * Cuniform * Lp +
              U * ((∑ v ∈ Finset.range q,
                    ∑ n ∈ Finset.Ico (K + 1 + v * H)
                        (K + 1 + (v + 1) * H), f n) +
                  (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) := by
      calc
        _ ≤ ∑ v ∈ Finset.range q,
            Cc * L * ((H : ℝ) * Cuniform * Lp + U *
              ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n) +
                (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) :=
          Finset.sum_le_sum hMuBlock
        _ = Cc * L *
            ((q : ℝ) * (H : ℝ) * Cuniform * Lp +
              U * ((∑ v ∈ Finset.range q,
                    ∑ n ∈ Finset.Ico (K + 1 + v * H)
                        (K + 1 + (v + 1) * H), f n) +
                  (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) := by
          calc
            _ = Cc * L * (∑ v ∈ Finset.range q,
                ((H : ℝ) * Cuniform * Lp + U *
                  ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                      (K + 1 + (v + 1) * H), f n) +
                    (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)))) := by
              rw [← Finset.mul_sum]
            _ = _ := congrArg (fun z : ℝ => Cc * L * z) hsumBlockFormula
    have hsumLambdaCommon :
        (∑ v ∈ Finset.range q,
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H),
            ((paperLambda (n : ℤ) -
              paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ)
                (n : ℤ) : ℝ) : ℂ) * unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
          Cc * L *
            ((q : ℝ) * (H : ℝ) * Cuniform * Lp +
              U * ((∑ v ∈ Finset.range q,
                    ∑ n ∈ Finset.Ico (K + 1 + v * H)
                        (K + 1 + (v + 1) * H), f n) +
                  (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) := by
      calc
        _ ≤ ∑ v ∈ Finset.range q,
            Cc * L * ((H : ℝ) * Cuniform * Lp + U *
              ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n) +
                (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) :=
          Finset.sum_le_sum hLambdaBlock
        _ = Cc * L *
            ((q : ℝ) * (H : ℝ) * Cuniform * Lp +
              U * ((∑ v ∈ Finset.range q,
                    ∑ n ∈ Finset.Ico (K + 1 + v * H)
                        (K + 1 + (v + 1) * H), f n) +
                  (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) := by
          calc
            _ = Cc * L * (∑ v ∈ Finset.range q,
                ((H : ℝ) * Cuniform * Lp + U *
                  ((∑ n ∈ Finset.Ico (K + 1 + v * H)
                      (K + 1 + (v + 1) * H), f n) +
                    (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)))) := by
              rw [← Finset.mul_sum]
            _ = _ := congrArg (fun z : ℝ => Cc * L * z) hsumBlockFormula
    have hCorrTotal :
        Cc * L * ((q : ℝ) * (H : ℝ) * Cuniform * Lp) ≤
          2 * Cc * Cuniform * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      have hCpositive : 0 ≤ Cc * Cuniform := mul_nonneg hCc.le hCuniform.le
      calc
        _ = Cc * Cuniform * ((q : ℝ) * (H : ℝ)) * (L * Lp) := by ring
        _ = (Cc * Cuniform) *
            (((q : ℝ) * (H : ℝ)) * (L * Lp)) := by ring
        _ ≤ (Cc * Cuniform) *
            ((K : ℝ) * (2 * (Real.log (K : ℝ)) ^ (-A : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hqKreal hlogratio (by positivity) (by positivity))
            hCpositive
        _ = Cc * Cuniform * (K : ℝ) *
            (2 * (Real.log (K : ℝ)) ^ (-A : ℝ)) := by ring
        _ = 2 * Cc * Cuniform * (K : ℝ) *
            (Real.log (K : ℝ)) ^ (-A : ℝ) := by ring
    have hBoundaryError :
        Cc * L * U *
            (∑ v ∈ Finset.range q,
              ∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n) ≤
          24 * Cc * (K : ℝ) ^ (1 - p.η / 4) := by
      have hsmallTwo :
          (2 * (K : ℝ)) ^ (-p.η / 2) ≤ (K : ℝ) ^ (-p.η / 2) := by
        rw [show 2 * (K : ℝ) = (2 : ℝ) * (K : ℝ) by ring,
          Real.mul_rpow (by norm_num) hKpos.le]
        calc
          (2 : ℝ) ^ (-p.η / 2) * (K : ℝ) ^ (-p.η / 2) ≤
              1 * (K : ℝ) ^ (-p.η / 2) := by
                exact mul_le_mul_of_nonneg_right
                  (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [hη.1]))
                  (Real.rpow_nonneg hKpos.le _)
          _ = (K : ℝ) ^ (-p.η / 2) := by ring
      have hBsum := hBoundaryBlocks
      have hBsum' :
          (∑ v ∈ Finset.range q,
            ∑ n ∈ Finset.Ico (K + 1 + v * H)
                (K + 1 + (v + 1) * H), f n) ≤
            12 * (2 * (K : ℝ)) * (K : ℝ) ^ (-p.η / 2) := by
        calc
          _ ≤ 12 * (2 * (K : ℝ)) *
              (2 * (K : ℝ)) ^ (-p.η / 2) := hBsum
          _ ≤ 12 * (2 * (K : ℝ)) * (K : ℝ) ^ (-p.η / 2) := by
            exact mul_le_mul_of_nonneg_left hsmallTwo (by positivity)
      have hProduct := mul_le_mul hUKL hBsum' hBsumNonneg (by positivity)
      calc
        _ = Cc * ((U * L) *
            (∑ v ∈ Finset.range q,
              ∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n)) := by ring
        _ ≤ Cc * ((K : ℝ) ^ (p.η / 4) *
            (12 * (2 * (K : ℝ)) * (K : ℝ) ^ (-p.η / 2))) :=
          mul_le_mul_of_nonneg_left hProduct hCc.le
        _ = 12 * Cc * ((K : ℝ) ^ (p.η / 4) *
            (2 * (K : ℝ)) * (K : ℝ) ^ (-p.η / 2)) := by ring
        _ ≤ 24 * Cc * (K : ℝ) ^ (1 - p.η / 4) := by
          have hprod :
              (K : ℝ) ^ (p.η / 4) *
                (2 * (K : ℝ)) * (K : ℝ) ^ (-p.η / 2) ≤
              2 * (K : ℝ) ^ (1 - p.η / 4) := by
            exact shortRemainderBoundaryPowerProduct hKpos
          calc
            _ ≤ 12 * Cc *
                (2 * (K : ℝ) ^ (1 - p.η / 4)) :=
              mul_le_mul_of_nonneg_left hprod (by positivity)
            _ = 24 * Cc * (K : ℝ) ^ (1 - p.η / 4) := by ring
    have hTaylorError :
        Cc * L * U * (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ) ≤
          Cc * (K : ℝ) ^ (1 - p.η / 4) := by
      have hqHreal' : (q : ℝ) * (H : ℝ) ≤ (K : ℝ) := hqKreal
      have hsmall :
          (K : ℝ) ^ (p.η / 4) * (K : ℝ) * (K : ℝ) ^ (-2 : ℝ) ≤
            (K : ℝ) ^ (1 - p.η / 4) :=
        shortRemainderTaylorPowerProduct (by linarith [hKreal3]) hη.2.le
      calc
        _ = Cc * (U * L) * ((q : ℝ) * (H : ℝ)) *
            (K : ℝ) ^ (-2 : ℝ) := by ring
        _ ≤ Cc * (K : ℝ) ^ (p.η / 4) * (K : ℝ) *
            (K : ℝ) ^ (-2 : ℝ) := by
          have hUL := hUKL
          calc
            _ ≤ Cc * (K : ℝ) ^ (p.η / 4) *
                ((q : ℝ) * (H : ℝ)) * (K : ℝ) ^ (-2 : ℝ) := by
                  gcongr
            _ ≤ Cc * (K : ℝ) ^ (p.η / 4) * (K : ℝ) *
                (K : ℝ) ^ (-2 : ℝ) := by
                  gcongr
        _ = Cc * ((K : ℝ) ^ (p.η / 4) * (K : ℝ) *
            (K : ℝ) ^ (-2 : ℝ)) := by ring
        _ ≤ Cc * (K : ℝ) ^ (1 - p.η / 4) :=
          mul_le_mul_of_nonneg_left hsmall hCc.le
    have hPowerAbsorb :
        Cc * (K : ℝ) ^ (1 - p.η / 4) ≤
          Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) :=
      by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hDecayBound hCc.le
    have herrorBound :
        Cc * L * U * (∑ v ∈ Finset.range q,
              ∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n) +
          Cc * L * U * (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ) ≤
          25 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
      have hT := hTaylorError.trans hPowerAbsorb
      have hB' :
          Cc * L * U * (∑ v ∈ Finset.range q,
              ∑ n ∈ Finset.Ico (K + 1 + v * H)
                  (K + 1 + (v + 1) * H), f n) ≤
            24 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
        calc
          _ ≤ 24 * Cc * (K : ℝ) ^ (1 - p.η / 4) := hBoundaryError
          _ ≤ 24 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) :=
            by
              simpa [mul_assoc] using
                mul_le_mul_of_nonneg_left hDecayBound (by positivity)
      have hT' :
          Cc * L * U * (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ) ≤
            Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := hT
      calc
        _ ≤ 24 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) +
            Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) :=
              add_le_add hB' hT'
        _ = 25 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by ring
    constructor
    · have hsum := hsumMuCommon
      have hfull :
          Cc * L * ((q : ℝ) * (H : ℝ) * Cuniform * Lp +
            U * ((∑ v ∈ Finset.range q,
                  ∑ n ∈ Finset.Ico (K + 1 + v * H)
                      (K + 1 + (v + 1) * H), f n) +
                (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) ≤
            2 * Cc * Cuniform * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) +
              25 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
        calc
          _ = Cc * L * ((q : ℝ) * (H : ℝ) * Cuniform * Lp) +
              (Cc * L * U * (∑ v ∈ Finset.range q,
                ∑ n ∈ Finset.Ico (K + 1 + v * H)
                    (K + 1 + (v + 1) * H), f n) +
              Cc * L * U * (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)) := by ring
          _ ≤ 2 * Cc * Cuniform * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) +
              25 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) :=
            add_le_add hCorrTotal herrorBound
      exact hsum.trans (by
        calc
          _ ≤ 2 * Cc * Cuniform * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) +
              25 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := hfull
          _ = Cbig * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
                dsimp [Cbig]
                ring)
    · have hsum := hsumLambdaCommon
      have hfull :
          Cc * L * ((q : ℝ) * (H : ℝ) * Cuniform * Lp +
            U * ((∑ v ∈ Finset.range q,
                  ∑ n ∈ Finset.Ico (K + 1 + v * H)
                      (K + 1 + (v + 1) * H), f n) +
                (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ))) ≤
            2 * Cc * Cuniform * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) +
              25 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
        calc
          _ = Cc * L * ((q : ℝ) * (H : ℝ) * Cuniform * Lp) +
              (Cc * L * U * (∑ v ∈ Finset.range q,
                ∑ n ∈ Finset.Ico (K + 1 + v * H)
                    (K + 1 + (v + 1) * H), f n) +
              Cc * L * U * (q : ℝ) * (H : ℝ) * (K : ℝ) ^ (-2 : ℝ)) := by ring
          _ ≤ 2 * Cc * Cuniform * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) +
              25 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) :=
            add_le_add hCorrTotal herrorBound
      exact hsum.trans (by
        calc
          _ ≤ 2 * Cc * Cuniform * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) +
              25 * Cc * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := hfull
          _ = Cbig * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
                dsimp [Cbig]
                ring)
  · omega


end FractionalPrimes
