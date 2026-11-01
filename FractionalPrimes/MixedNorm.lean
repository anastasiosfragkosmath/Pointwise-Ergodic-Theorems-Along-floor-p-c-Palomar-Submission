module

public import FractionalPrimes.VariationMonotonicity
public import FractionalPrimes.VariationBlocks
public import FractionalPrimes.LongShortVariation
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Mixed norm estimates

Finite scalar inequalities used in the mixed-norm part of the long/short
variation argument.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

/-- P1-compatible port of the ENNReal scalar homogeneity identity for the
primed `Lᵖ` seminorm. Mathlib's historical P0 name for this fact is not
present at the blueprint's P1 pin. -/
private theorem eLpNorm'_const_mul_ennreal_local {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {q : ℝ} {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hq_pos : 0 < q) (hf : AEStronglyMeasurable f μ) :
    eLpNorm' (fun x => c * f x) q μ = c * eLpNorm' f q μ := by
  simp [eLpNorm', lintegral_const_mul'' _ (hf.aemeasurable.pow_const q),
    ENNReal.mul_rpow_of_nonneg (z := q⁻¹) (c ^ q) _ (by simp [hq_pos.le]),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    hq_pos.ne']

/-- P1-compatible scalar homogeneity for the extended-nonnegative-valued
`Lᵖ` norm. -/
private theorem eLpNorm_const_mul_ennreal_local {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => c * f x) p μ = c * eLpNorm f p μ := by
  have hcf := (hf.aemeasurable.const_mul c).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf, hcf]
  rcases eq_or_ne p ∞ with rfl | hp'
  · simp only [eLpNorm_exponent_top hf, eLpNorm_exponent_top hcf,
      eLpNormEssSup, enorm_eq_self, ENNReal.essSup_const_mul]
  simp only [eLpNorm_eq_eLpNorm' hp hp' hf, eLpNorm_eq_eLpNorm' hp hp' hcf]
  exact eLpNorm'_const_mul_ennreal_local (ENNReal.toReal_pos hp hp') hf

theorem eLpNorm_tsum_le_tsum_eLpNorm {α ι E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [CompleteSpace E] [Countable ι]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ι → α → E)
    (hmem : ∀ i, MemLp (f i) p μ)
    (hsum : (∑' i, eLpNorm (f i) p μ) ≠ ∞) :
    eLpNorm (fun x => ∑' i, f i x) p μ ≤ ∑' i, eLpNorm (f i) p μ := by
  let _ : Fact (1 ≤ p) := ⟨hp⟩
  let F : ι → Lp E p μ := fun i => (hmem i).toLp (f i)
  have hFsum : (∑' i, ‖F i‖ₑ) ≠ ∞ := by
    simpa [F, Lp.enorm_toLp] using hsum
  have hcoe := Lp.coeFn_tsum hFsum
  have hterms : ∀ᵐ x ∂μ, ∀ i, f i x = F i x := by
    rw [ae_all_iff]
    intro i
    exact (hmem i).coeFn_toLp.symm
  have hseries : (fun x => ∑' i, f i x) =ᵐ[μ] fun x => (∑' i, F i) x := by
    filter_upwards [hterms, hcoe] with x hx hsumx
    rw [tsum_congr hx]
    exact hsumx.symm
  calc
    eLpNorm (fun x => ∑' i, f i x) p μ =
        eLpNorm (fun x => (∑' i, F i) x) p μ :=
      eLpNorm_congr_ae hseries
    _ = ‖∑' i, F i‖ₑ := (Lp.enorm_def _).symm
    _ ≤ ∑' i, ‖F i‖ₑ := enorm_tsum_le_tsum_enorm
    _ = ∑' i, eLpNorm (f i) p μ := by simp [F, Lp.enorm_toLp]

theorem eLpNorm_tsum_norm_le_tsum_eLpNorm {α ι E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [Countable ι] {p : ℝ≥0∞}
    (hp : 1 ≤ p) (f : ι → α → E)
    (hmem : ∀ i, MemLp (f i) p μ)
    (hsum : (∑' i, eLpNorm (f i) p μ) ≠ ∞) :
    eLpNorm (fun x => ∑' i, ‖f i x‖) p μ ≤ ∑' i, eLpNorm (f i) p μ := by
  have hnorm : ∀ i, MemLp (fun x => ‖f i x‖) p μ := fun i => (hmem i).norm
  have hnormEq (i : ι) :
      eLpNorm (fun x => ‖f i x‖) p μ = eLpNorm (f i) p μ :=
    eLpNorm_norm (f i) (hmem i).aestronglyMeasurable
  have hsumNorm : (∑' i, eLpNorm (fun x => ‖f i x‖) p μ) ≠ ∞ := by
    rw [tsum_congr hnormEq]
    exact hsum
  have hle := eLpNorm_tsum_le_tsum_eLpNorm hp (fun i x => (‖f i x‖ : ℝ))
    hnorm hsumNorm
  calc
    eLpNorm (fun x => ∑' i, ‖f i x‖) p μ ≤
        ∑' i, eLpNorm (fun x => ‖f i x‖) p μ := hle
    _ = ∑' i, eLpNorm (f i) p μ := by rw [tsum_congr hnormEq]

/-- For `0 < p ≤ 2`, the pointwise `ℓ²` square sum raised to `p/2` is
bounded by the `ℓᵖ` power sum. -/
theorem finiteENNReal_squareSum_rpow_le {ι : Type*} (s : Finset ι)
    (a : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    (∑ i ∈ s, (a i) ^ (2 : ℝ)) ^ (p / 2) ≤
      ∑ i ∈ s, (a i) ^ p := by
  have hroot := finiteENNReal_rpow_sum_mono_exponent s a hp hp2
  have hpow := ENNReal.rpow_le_rpow hroot hp.le
  calc
    (∑ i ∈ s, (a i) ^ (2 : ℝ)) ^ (p / 2) =
        (∑ i ∈ s, (a i) ^ (2 : ℝ)) ^ ((1 / 2 : ℝ) * p) := by
          congr 1
          ring
    _ ≤ ((∑ i ∈ s, (a i) ^ p) ^ (1 / p)) ^ p := by
          simpa only [← ENNReal.rpow_mul] using hpow
    _ = ∑ i ∈ s, (a i) ^ p := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- Integrate a pointwise finite-sum majorant by integrating its summands. -/
theorem lintegral_le_finset_sum_of_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (f : ι → α → ℝ≥0∞) (g : α → ℝ≥0∞)
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    (hfg : ∀ x, g x ≤ ∑ i ∈ s, f i x) :
    ∫⁻ x, g x ∂μ ≤ ∑ i ∈ s, ∫⁻ x, f i x ∂μ := by
  calc
    ∫⁻ x, g x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ :=
      lintegral_mono_ae (by filter_upwards with x; exact hfg x)
    _ = ∑ i ∈ s, ∫⁻ x, f i x ∂μ := lintegral_finsetSum' s hf

/-- The finite pointwise square-sum estimate also holds after integration. -/
theorem lintegral_squareSum_rpow_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (f : ι → α → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    ∫⁻ x, (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ ≤
      ∑ i ∈ s, ∫⁻ x, (f i x) ^ p ∂μ := by
  apply lintegral_le_finset_sum_of_le μ s (fun i x => (f i x) ^ p)
    (fun x => (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (p / 2))
    (fun i hi => by
      have hfi := hf i hi
      fun_prop)
  intro x
  exact finiteENNReal_squareSum_rpow_le s (fun i => f i x) hp hp2

/-- The `p ≤ 2` finite mixed-norm estimate in powered `eLpNorm` form. -/
theorem eLpNorm_squareSum_rpow_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (f : ι → α → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    (eLpNorm (fun x => (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) μ) ^ p ≤
      ∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ p := by
  let g : α → ℝ≥0∞ := fun x => (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  have hg : AEStronglyMeasurable g μ := by
    dsimp [g]
    fun_prop
  have hpq : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hp).ne'
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hleft : eLpNorm g (ENNReal.ofReal p) μ =
      (∫⁻ x, (g x) ^ p ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpq hptop hg]
    simp [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  have hright (i : ι) (hi : i ∈ s) :
      eLpNorm (f i) (ENNReal.ofReal p) μ =
        (∫⁻ x, (f i x) ^ p ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpq hptop (hf i hi)]
    simp [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  calc
    (eLpNorm g (ENNReal.ofReal p) μ) ^ p = ∫⁻ x, (g x) ^ p ∂μ := by
      rw [hleft, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
    _ ≤ ∑ i ∈ s, ∫⁻ x, (f i x) ^ p ∂μ := by
      convert lintegral_squareSum_rpow_le μ s f hp hp2
        (fun i hi => (hf i hi).aemeasurable) using 1
      · congr 1
        funext x
        dsimp [g]
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
    _ = ∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ p := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hright i hi, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne',
        ENNReal.rpow_one]

/-- The finite mixed-norm estimate for `0 < p ≤ 2`. -/
theorem eLpNorm_squareSum_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (f : ι → α → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    eLpNorm (fun x => (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) μ ≤
      (∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ p) ^ (1 / p) := by
  apply (ENNReal.rpow_le_rpow_iff hp).mp
  calc
    (eLpNorm (fun x => (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) μ) ^ p ≤
        ∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ p :=
      eLpNorm_squareSum_rpow_le μ s f hp hp2 hf
    _ = ((∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ p) ^
        (1 / p : ℝ)) ^ p := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- The finite mixed-norm estimate for `p ≥ 2`, using Minkowski in `L^(p/2)`. -/
theorem eLpNorm_squareSum_le_ge_two {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (f : ι → α → ℝ≥0∞)
    {p : ℝ} (hp2 : 2 ≤ p)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    eLpNorm (fun x => (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) μ ≤
      (∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  let g : α → ℝ≥0∞ := fun x => (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  let q : ℝ≥0∞ := ENNReal.ofReal (p / 2)
  have hp : 0 < p := lt_of_lt_of_le (by norm_num) hp2
  have hq1 : 1 ≤ q := by
    change 1 ≤ ENNReal.ofReal (p / 2)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hqexp : q * ENNReal.ofReal 2 = ENNReal.ofReal p := by
    change ENNReal.ofReal (p / 2) * ENNReal.ofReal 2 = ENNReal.ofReal p
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ p / 2)]
    congr 1
    ring
  have hg : AEStronglyMeasurable g μ := by
    dsimp [g]
    fun_prop
  have hsum : AEStronglyMeasurable (fun x => ∑ i ∈ s, (f i x) ^ (2 : ℝ)) μ := by
    fun_prop
  have hsquare : (eLpNorm g (ENNReal.ofReal p) μ) ^ (2 : ℝ) ≤
      ∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ (2 : ℝ) := by
    calc
      (eLpNorm g (ENNReal.ofReal p) μ) ^ (2 : ℝ) =
          eLpNorm (fun x => ∑ i ∈ s, (f i x) ^ (2 : ℝ)) q μ := by
        have hpoint : (fun x => ∑ i ∈ s, (f i x) ^ (2 : ℝ)) =ᵐ[μ]
            (fun x => ‖g x‖ₑ ^ (2 : ℝ)) := by
          filter_upwards with x
          dsimp [g]
          rw [← ENNReal.rpow_mul]
          rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
        rw [eLpNorm_congr_ae hpoint,
          eLpNorm_enorm_rpow g hg (by norm_num : 0 < (2 : ℝ)), hqexp]
      _ ≤ ∑ i ∈ s, eLpNorm (fun x => (f i x) ^ (2 : ℝ)) q μ := by
        have hsumfun : (∑ i ∈ s, fun x => (f i x) ^ (2 : ℝ)) =
            (fun x => ∑ i ∈ s, (f i x) ^ (2 : ℝ)) := by
          funext x
          simp
        rw [← hsumfun]
        exact eLpNorm_sum_le hq1
      _ = ∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ (2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa only [enorm_eq_self, hqexp] using
          (eLpNorm_enorm_rpow (f i) (hf i hi) (p := q)
            (q := 2) (by norm_num : 0 < (2 : ℝ)))
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (2 : ℝ))).mp
  calc
    (eLpNorm g (ENNReal.ofReal p) μ) ^ (2 : ℝ) ≤
        ∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ (2 : ℝ) := hsquare
    _ = ((∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ)) ^ (2 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num

/-- The complete finite-family mixed-norm estimate with `q = min(p, 2)`. -/
theorem eLpNorm_squareSum_mixed {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (f : ι → α → ℝ≥0∞)
    {p : ℝ} (hp : 1 < p)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    eLpNorm (fun x => (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) μ ≤
      (∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ) ^ min p 2) ^
        (1 / min p 2) := by
  by_cases hp2 : p ≤ 2
  · simpa [min_eq_left hp2] using
      (eLpNorm_squareSum_le μ s f (lt_trans (by norm_num) hp) hp2 hf)
  · have h2p : 2 ≤ p := le_of_not_ge hp2
    simpa [min_eq_right h2p] using
      (eLpNorm_squareSum_le_ge_two μ s f h2p hf)

/-- Finite sparse-block square functions satisfy the mixed-norm estimate. -/
theorem eLpNorm_finiteSparseBlockSquare_mixed {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : ℕ → Scale) (F : Scale → X → ℂ) (t : Finset ℕ)
    {p : ℝ} (hp : 1 < p) (hF : ∀ N, AEMeasurable (F N) μ) :
    eLpNorm (fun x =>
      (∑ k ∈ t, (rVariationOnFun 2 F
        (Set.Icc (s k) (s (k + 1))) x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) μ ≤
      (∑ k ∈ t, (eLpNorm (rVariationOnFun 2 F
        (Set.Icc (s k) (s (k + 1)))) (ENNReal.ofReal p) μ) ^ min p 2) ^
        (1 / min p 2) := by
  apply eLpNorm_squareSum_mixed μ t
  · exact hp
  · intro k hk
    exact (aemeasurable_rVariationOnFun μ 2 F
      (Set.Icc (s k) (s (k + 1))) hF).aestronglyMeasurable

/-- The pointwise `ℓ²` to `ℓᵖ` comparison extends to countable ENNReal
families when `0 < p ≤ 2`. -/
theorem ennreal_tsum_square_rpow_le {a : ℕ → ℝ≥0∞} {p : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2) :
    (∑' k, (a k) ^ (2 : ℝ)) ^ (p / 2) ≤ ∑' k, (a k) ^ p := by
  let c : ℝ := p / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hpow_mono := ENNReal.strictMono_rpow_of_pos hc
  have hpow_surj := (ENNReal.rpow_left_bijective hc.ne').2
  let iso := hpow_mono.orderIsoOfSurjective _ hpow_surj
  have hpow_iSup : (⨆ s : Finset ℕ, ∑ k ∈ s, (a k) ^ (2 : ℝ)) ^ c =
      ⨆ s : Finset ℕ, (∑ k ∈ s, (a k) ^ (2 : ℝ)) ^ c := by
    change iso (⨆ s : Finset ℕ, ∑ k ∈ s, (a k) ^ (2 : ℝ)) = _
    exact iso.map_iSup fun s => ∑ k ∈ s, (a k) ^ (2 : ℝ)
  calc
    (∑' k, (a k) ^ (2 : ℝ)) ^ (p / 2) =
        (⨆ s : Finset ℕ, ∑ k ∈ s, (a k) ^ (2 : ℝ)) ^ c := by
          rw [ENNReal.tsum_eq_iSup_sum]
    _ = ⨆ s : Finset ℕ, (∑ k ∈ s, (a k) ^ (2 : ℝ)) ^ c := hpow_iSup
    _ ≤ ∑' k, (a k) ^ p := iSup_le fun s => by
      calc
        (∑ k ∈ s, (a k) ^ (2 : ℝ)) ^ c ≤ ∑ k ∈ s, (a k) ^ p := by
          simpa [c] using finiteENNReal_squareSum_rpow_le s a hp hp2
        _ ≤ ∑' k, (a k) ^ p := ENNReal.sum_le_tsum s

/-- The countable `p ≤ 2` mixed-norm estimate in powered `eLpNorm` form. -/
theorem eLpNorm_tsumSquare_rpow_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℝ≥0∞) {p : ℝ} (hp : 0 < p)
    (hp2 : p ≤ 2) (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    (eLpNorm (fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) μ) ^ p ≤
        ∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ p := by
  let g : α → ℝ≥0∞ := fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  have hpq : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hterm (k : ℕ) : AEMeasurable (fun x => (f k x) ^ p) μ := by fun_prop
  have hsquare (k : ℕ) : AEMeasurable (fun x => (f k x) ^ (2 : ℝ)) μ := by fun_prop
  have hsum : AEMeasurable (fun x => ∑' k, (f k x) ^ (2 : ℝ)) μ :=
    AEMeasurable.tsum hsquare
  have hg : AEStronglyMeasurable g μ := by
    have hpow : AEMeasurable g μ := by
      change AEMeasurable ((fun a : ℝ≥0∞ => a ^ (1 / 2 : ℝ)) ∘
        (fun x => ∑' k, (f k x) ^ (2 : ℝ))) μ
      exact AEMeasurable.comp_aemeasurable
        (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).measurable.aemeasurable hsum
    exact hpow.aestronglyMeasurable
  have hleft : eLpNorm g (ENNReal.ofReal p) μ =
      (∫⁻ x, (g x) ^ p ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpq hptop hg]
    simp [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  have hright (k : ℕ) : eLpNorm (f k) (ENNReal.ofReal p) μ =
      (∫⁻ x, (f k x) ^ p ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpq hptop (hf k)]
    simp [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  calc
    (eLpNorm g (ENNReal.ofReal p) μ) ^ p = ∫⁻ x, (g x) ^ p ∂μ := by
      rw [hleft, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
    _ ≤ ∫⁻ x, ∑' k, (f k x) ^ p ∂μ := by
      apply lintegral_mono_ae
      filter_upwards with x
      calc
        g x ^ p = (∑' k, (f k x) ^ (2 : ℝ)) ^ (p / 2) := by
          dsimp [g]
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
        _ ≤ ∑' k, (f k x) ^ p :=
          ennreal_tsum_square_rpow_le (a := fun k => f k x) (p := p) hp hp2
    _ = ∑' k, ∫⁻ x, (f k x) ^ p ∂μ := lintegral_tsum hterm
    _ = ∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ p := by
      apply tsum_congr
      intro k
      rw [hright k, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne',
        ENNReal.rpow_one]

/-- The countable finite-exponent mixed-norm estimate for `0 < p ≤ 2`. -/
theorem eLpNorm_tsumSquare_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℝ≥0∞) {p : ℝ} (hp : 0 < p)
    (hp2 : p ≤ 2) (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNorm (fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) μ ≤
        (∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ p) ^ (1 / p) := by
  apply (ENNReal.rpow_le_rpow_iff hp).mp
  calc
    (eLpNorm (fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) μ) ^ p ≤
        ∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ p :=
      eLpNorm_tsumSquare_rpow_le μ f hp hp2 hf
    _ = ((∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ p) ^
        (1 / p : ℝ)) ^ p := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- The countable `p ≥ 2` mixed-norm estimate in powered form, by monotone
convergence over finite partial square sums. -/
theorem eLpNorm_tsumSquare_rpow_le_ge_two {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℝ≥0∞) {p : ℝ} (hp2 : 2 ≤ p)
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    (eLpNorm (fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) μ) ^ (2 : ℝ) ≤
        ∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ (2 : ℝ) := by
  let q : ℝ := p / 2
  let H : α → ℝ≥0∞ := fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  let W : Finset ℕ → α → ℝ≥0∞ := fun s x =>
    (∑ k ∈ s, (f k x) ^ (2 : ℝ)) ^ q
  have hp : 0 < p := lt_of_lt_of_le (by norm_num) hp2
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by dsimp [q]; linarith)
  have hpq : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hH : AEStronglyMeasurable H μ := by
    have hsquare (k : ℕ) : AEMeasurable (fun x => (f k x) ^ (2 : ℝ)) μ := by fun_prop
    have hsum : AEMeasurable (fun x => ∑' k, (f k x) ^ (2 : ℝ)) μ :=
      AEMeasurable.tsum hsquare
    have hpow : AEMeasurable H μ := by
      change AEMeasurable ((fun a : ℝ≥0∞ => a ^ (1 / 2 : ℝ)) ∘
        (fun x => ∑' k, (f k x) ^ (2 : ℝ))) μ
      exact AEMeasurable.comp_aemeasurable
        (ENNReal.continuous_rpow_const.measurable.aemeasurable) hsum
    exact hpow.aestronglyMeasurable
  have hWmeas (s : Finset ℕ) : AEMeasurable (W s) μ := by
    dsimp [W]
    fun_prop
  have hWdir : Directed (· ≤ ·) W := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x
      apply ENNReal.rpow_le_rpow ?_ (le_of_lt hq)
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (by intro i hi h; positivity)
    · intro x
      apply ENNReal.rpow_le_rpow ?_ (le_of_lt hq)
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (by intro i hi h; positivity)
  have hWpoint (x : α) : (∑' k, (f k x) ^ (2 : ℝ)) ^ q = ⨆ s, W s x := by
    rw [ENNReal.tsum_eq_iSup_sum]
    let iso := (ENNReal.strictMono_rpow_of_pos hq).orderIsoOfSurjective _
      (ENNReal.rpow_left_bijective hq.ne').2
    change iso (⨆ s : Finset ℕ, ∑ k ∈ s, (f k x) ^ (2 : ℝ)) = _
    exact iso.map_iSup fun s => ∑ k ∈ s, (f k x) ^ (2 : ℝ)
  have hMCT : ∫⁻ x, ⨆ s, W s x ∂μ = ⨆ s, ∫⁻ x, W s x ∂μ :=
    lintegral_iSup_directed hWmeas hWdir
  have hleft : eLpNorm H (ENNReal.ofReal p) μ =
      (∫⁻ x, (H x) ^ p ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpq hptop hH]
    simp [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  have hfinite (s : Finset ℕ) :
      (eLpNorm (fun x => (∑ k ∈ s, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) μ) ^ (2 : ℝ) ≤
      ∑ k ∈ s, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ (2 : ℝ) := by
    have h := eLpNorm_squareSum_le_ge_two μ s f hp2 (fun k hk => hf k)
    calc
      _ ≤ ((∑ k ∈ s, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
      _ = ∑ k ∈ s, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ (2 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
  have hIntpow (s : Finset ℕ) :
      (∫⁻ x, W s x ∂μ) ^ (2 / p) =
        (eLpNorm (fun x => (∑ k ∈ s, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) μ) ^ (2 : ℝ) := by
    have hGs : AEStronglyMeasurable
        (fun x => (∑ k ∈ s, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) μ := by fun_prop
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpq hptop hGs]
    simp only [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
    rw [← ENNReal.rpow_mul]
    congr 1
    · apply lintegral_congr_ae
      filter_upwards with x
      dsimp [W, q]
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    · ring
  have hc : 0 < 2 / p := by positivity
  have hpowiSup : (⨆ s : Finset ℕ, ∫⁻ x, W s x ∂μ) ^ (2 / p) =
      ⨆ s : Finset ℕ, (∫⁻ x, W s x ∂μ) ^ (2 / p) := by
    let iso := (ENNReal.strictMono_rpow_of_pos hc).orderIsoOfSurjective _
      (ENNReal.rpow_left_bijective hc.ne').2
    change iso (⨆ s : Finset ℕ, ∫⁻ x, W s x ∂μ) = _
    exact iso.map_iSup fun s => ∫⁻ x, W s x ∂μ
  have hleftEq :
      (eLpNorm H (ENNReal.ofReal p) μ) ^ (2 : ℝ) =
        (∫⁻ x, ⨆ s, W s x ∂μ) ^ (2 / p) := by
    rw [hleft, ← ENNReal.rpow_mul]
    congr 1
    · apply lintegral_congr_ae
      filter_upwards with x
      rw [← hWpoint x]
      dsimp [H]
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    · ring
  calc
    (eLpNorm H (ENNReal.ofReal p) μ) ^ (2 : ℝ) =
        (⨆ s : Finset ℕ, ∫⁻ x, W s x ∂μ) ^ (2 / p) := by
          rw [hleftEq, hMCT]
    _ = ⨆ s : Finset ℕ, (∫⁻ x, W s x ∂μ) ^ (2 / p) := hpowiSup
    _ = ⨆ s : Finset ℕ,
        (eLpNorm (fun x => (∑ k ∈ s, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) μ) ^ (2 : ℝ) := by
          congr 1
          funext s
          exact hIntpow s
    _ ≤ ∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ (2 : ℝ) := iSup_le fun s =>
          (hfinite s).trans (ENNReal.sum_le_tsum s)

/-- The countable finite-exponent mixed-norm estimate for `p ≥ 2`. -/
theorem eLpNorm_tsumSquare_le_ge_two {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℝ≥0∞) {p : ℝ} (hp2 : 2 ≤ p)
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNorm (fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) μ ≤
        (∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (2 : ℝ))).mp
  calc
    (eLpNorm (fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) μ) ^ (2 : ℝ) ≤
        ∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ (2 : ℝ) :=
      eLpNorm_tsumSquare_rpow_le_ge_two μ f hp2 hf
    _ = ((∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ)) ^ (2 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num

/-- The countable mixed-norm inequality with the blueprint's `q = min(p,2)`. -/
theorem eLpNorm_tsumSquare_mixed {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℝ≥0∞) {p : ℝ} (hp : 1 < p)
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNorm (fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) μ ≤
        (∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ min p 2) ^
          (1 / min p 2) := by
  by_cases hp2 : p ≤ 2
  · simpa [min_eq_left hp2] using
      eLpNorm_tsumSquare_le μ f (lt_trans (by norm_num) hp) hp2 hf
  · have h2p : 2 ≤ p := le_of_not_ge hp2
    simpa [min_eq_right h2p] using eLpNorm_tsumSquare_le_ge_two μ f h2p hf

/-- The countable sparse-block square function satisfies the mixed-norm bound. -/
theorem eLpNorm_sparseBlockSquare_mixed {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : ℕ → Scale) (F : Scale → X → ℂ)
    {p : ℝ} (hp : 1 < p) (hF : ∀ N, AEMeasurable (F N) μ) :
    eLpNorm (fun x =>
      (∑' k, (rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1))) x) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ)) (ENNReal.ofReal p) μ ≤
      (∑' k, (eLpNorm (rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1))) )
        (ENNReal.ofReal p) μ) ^ min p 2) ^ (1 / min p 2) := by
  apply eLpNorm_tsumSquare_mixed μ (fun k x =>
    rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1))) x) hp
  intro k
  exact (aemeasurable_rVariationOnFun μ 2 F
    (Set.Icc (s k) (s (k + 1))) hF).aestronglyMeasurable

/-- The global long/short variation inequality yields the corresponding Lp
reduction, with the square-function term controlled by the mixed-norm bound. -/
theorem eLpNorm_longShort_reduction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : ℕ → Scale)
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    (F : Scale → X → ℂ) {p r : ℝ} (hp : 1 < p) (hr2 : 2 ≤ r)
    (hF : ∀ N, AEMeasurable (F N) μ) :
    eLpNorm (rVariationFun r F) (ENNReal.ofReal p) μ ≤
      3 * eLpNorm (rVariationFun r (fun K : Scale => F (s (K.1 - 1))))
          (ENNReal.ofReal p) μ +
        3 * (∑' k, (eLpNorm (rVariationOnFun 2 F
          (Set.Icc (s k) (s (k + 1)))) (ENNReal.ofReal p) μ) ^ min p 2) ^
          (1 / min p 2) := by
  let Long : X → ℝ≥0∞ := rVariationFun r (fun K : Scale => F (s (K.1 - 1)))
  let Block : ℕ → X → ℝ≥0∞ := fun k =>
    rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1)))
  let Square : X → ℝ≥0∞ := fun x =>
    (∑' k, (Block k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  have hglobal : AEStronglyMeasurable (rVariationFun r F) μ :=
    (aemeasurable_rVariationFun μ r F hF).aestronglyMeasurable
  have hLong : AEStronglyMeasurable Long μ := by
    apply (aemeasurable_rVariationFun μ r _ _).aestronglyMeasurable
    intro N
    exact hF (s (N.1 - 1))
  have hBlock (k : ℕ) : AEMeasurable (Block k) μ := by
    exact aemeasurable_rVariationOnFun μ 2 F (Set.Icc (s k) (s (k + 1))) hF
  have hSquare : AEStronglyMeasurable Square μ := by
    have hsquare (k : ℕ) : AEMeasurable (fun x => (Block k x) ^ (2 : ℝ)) μ := by
      fun_prop
    have hsum : AEMeasurable (fun x => ∑' k, (Block k x) ^ (2 : ℝ)) μ :=
      AEMeasurable.tsum hsquare
    have hpow : AEMeasurable Square μ := by
      change AEMeasurable ((fun a : ℝ≥0∞ => a ^ (1 / 2 : ℝ)) ∘
        (fun x => ∑' k, (Block k x) ^ (2 : ℝ))) μ
      exact AEMeasurable.comp_aemeasurable
        ENNReal.continuous_rpow_const.measurable.aemeasurable hsum
    exact hpow.aestronglyMeasurable
  have hpoint (x : X) : rVariationFun r F x ≤ 3 * Long x + 3 * Square x := by
    have h := rVariation_le_sparse_and_blockSquare hs0 hs hUnbounded
      (fun N => F N x) hr2
    simpa [Long, Square, Block, rVariationFun_apply, rVariationOnFun] using h
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  calc
    eLpNorm (rVariationFun r F) (ENNReal.ofReal p) μ ≤
        eLpNorm (fun x => 3 * Long x + 3 * Square x)
          (ENNReal.ofReal p) μ :=
      eLpNorm_mono_enorm_ae hglobal (by filter_upwards with x; exact hpoint x)
    _ ≤ eLpNorm (fun x => 3 * Long x) (ENNReal.ofReal p) μ +
        eLpNorm (fun x => 3 * Square x) (ENNReal.ofReal p) μ := by
      exact eLpNorm_add_le hp1
    _ = 3 * eLpNorm Long (ENNReal.ofReal p) μ +
        3 * eLpNorm Square (ENNReal.ofReal p) μ := by
      rw [eLpNorm_const_mul_ennreal_local hLong, eLpNorm_const_mul_ennreal_local hSquare]
    _ ≤ 3 * eLpNorm Long (ENNReal.ofReal p) μ +
        3 * (∑' k, (eLpNorm (Block k) (ENNReal.ofReal p) μ) ^ min p 2) ^
          (1 / min p 2) := by
      gcongr
      exact eLpNorm_tsumSquare_mixed μ Block hp
        (fun k => (hBlock k).aestronglyMeasurable)

/-- Direct `L^p` form of the pointwise long/short reduction, before applying
the mixed-norm estimate to the short square function. -/
theorem eLpNorm_longShort_reduction_direct {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : ℕ → Scale)
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    (F : Scale → X → ℂ) {p r : ℝ} (hp : 1 < p) (hr2 : 2 ≤ r)
    (hF : ∀ N, AEMeasurable (F N) μ) :
    eLpNorm (rVariationFun r F) (ENNReal.ofReal p) μ ≤
      3 * eLpNorm (rVariationFun r (fun K : Scale => F (s (K.1 - 1))))
          (ENNReal.ofReal p) μ +
        3 * eLpNorm (fun x =>
          (∑' k, (rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1))) x) ^
            (2 : ℝ)) ^ (1 / 2 : ℝ)) (ENNReal.ofReal p) μ := by
  let Long : X → ℝ≥0∞ := rVariationFun r (fun K : Scale => F (s (K.1 - 1)))
  let Block : ℕ → X → ℝ≥0∞ := fun k =>
    rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1)))
  let Square : X → ℝ≥0∞ := fun x =>
    (∑' k, (Block k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  have hglobal : AEStronglyMeasurable (rVariationFun r F) μ :=
    (aemeasurable_rVariationFun μ r F hF).aestronglyMeasurable
  have hLong : AEStronglyMeasurable Long μ := by
    apply (aemeasurable_rVariationFun μ r _ _).aestronglyMeasurable
    intro N
    exact hF (s (N.1 - 1))
  have hBlock (k : ℕ) : AEMeasurable (Block k) μ :=
    aemeasurable_rVariationOnFun μ 2 F (Set.Icc (s k) (s (k + 1))) hF
  have hSquare : AEStronglyMeasurable Square μ := by
    have hsquare (k : ℕ) : AEMeasurable (fun x => (Block k x) ^ (2 : ℝ)) μ := by
      fun_prop
    have hsum : AEMeasurable (fun x => ∑' k, (Block k x) ^ (2 : ℝ)) μ :=
      AEMeasurable.tsum hsquare
    have hpow : AEMeasurable Square μ := by
      change AEMeasurable ((fun a : ℝ≥0∞ => a ^ (1 / 2 : ℝ)) ∘
        (fun x => ∑' k, (Block k x) ^ (2 : ℝ))) μ
      exact AEMeasurable.comp_aemeasurable
        ENNReal.continuous_rpow_const.measurable.aemeasurable hsum
    exact hpow.aestronglyMeasurable
  have hpoint (x : X) : rVariationFun r F x ≤ 3 * Long x + 3 * Square x := by
    have h := rVariation_le_sparse_and_blockSquare hs0 hs hUnbounded
      (fun N => F N x) hr2
    simpa [Long, Square, Block, rVariationFun_apply, rVariationOnFun] using h
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  calc
    eLpNorm (rVariationFun r F) (ENNReal.ofReal p) μ ≤
        eLpNorm (fun x => 3 * Long x + 3 * Square x)
          (ENNReal.ofReal p) μ :=
      eLpNorm_mono_enorm_ae hglobal (by filter_upwards with x; exact hpoint x)
    _ ≤ eLpNorm (fun x => 3 * Long x) (ENNReal.ofReal p) μ +
        eLpNorm (fun x => 3 * Square x) (ENNReal.ofReal p) μ :=
      eLpNorm_add_le hp1
    _ = 3 * eLpNorm Long (ENNReal.ofReal p) μ +
        3 * eLpNorm Square (ENNReal.ofReal p) μ := by
      rw [eLpNorm_const_mul_ennreal_local hLong, eLpNorm_const_mul_ennreal_local hSquare]

end FractionalPrimes
