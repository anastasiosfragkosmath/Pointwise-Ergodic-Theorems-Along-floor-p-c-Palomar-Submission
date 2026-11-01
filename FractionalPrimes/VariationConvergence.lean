module

public import FractionalPrimes.VariationBasics
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Finite `Lᵖ` norm of a nonnegative extended-real function, at a positive
finite exponent, implies that the function is finite almost everywhere. -/
theorem ae_lt_top_of_memLp_ennreal {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ} (hp : 0 < p) (V : X → ℝ≥0∞)
    (hV : MemLp V (ENNReal.ofReal p) μ) : ∀ᵐ x ∂μ, V x < ∞ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hlin : ∫⁻ x, ‖V x‖ₑ ^ p ∂μ < ∞ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop
      hV.aestronglyMeasurable).mp hV
    simpa [ENNReal.toReal_ofReal (le_of_lt hp)] using h
  have hpow : ∀ᵐ x ∂μ, ‖V x‖ₑ ^ p < ∞ :=
    ae_lt_top'
      ((ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable
        hV.aemeasurable.enorm) hlin.ne
  filter_upwards [hpow] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos hp).mp (by simpa using hx)

/-- On a positive finite exponent, an ENNReal-valued `Lᵖ` function's `toReal`
representative is also in `Lᵖ`. -/
theorem memLp_toReal_of_memLp_ennreal {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ} (hp : 0 < p) (V : X → ℝ≥0∞)
    (hV : MemLp V (ENNReal.ofReal p) μ) :
    MemLp (fun x => (V x).toReal) (ENNReal.ofReal p) μ := by
  have hfinite := ae_lt_top_of_memLp_ennreal hp V hV
  have hmeas : AEStronglyMeasurable (fun x => (V x).toReal) μ :=
    hV.aemeasurable.ennreal_toReal.aestronglyMeasurable
  apply hV.congr_enorm hmeas
  filter_upwards [hfinite] with x hx
  calc
    ‖V x‖ₑ = V x := by simp
    _ = ENNReal.ofReal ((V x).toReal) := (ENNReal.ofReal_toReal hx.ne).symm
    _ = ‖(V x).toReal‖ₑ := by
      rw [← ofReal_norm, Real.norm_of_nonneg (ENNReal.toReal_nonneg)]

/-- The natural scalar majorant formed from an `Lᵖ` first term and an
`Lᵖ`-finite ENNReal variation remains in `Lᵖ`. -/
theorem memLp_norm_add_toReal_of_memLp_ennreal {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ} (hp : 0 < p) (V : X → ℝ≥0∞) (f : X → ℂ)
    (hV : MemLp V (ENNReal.ofReal p) μ)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun x => ‖f x‖ + (V x).toReal) (ENNReal.ofReal p) μ := by
  exact hf.norm.add (memLp_toReal_of_memLp_ennreal hp V hV)

/-- The powered factor-two majorant used for dominated `Lᵖ` convergence is
integrable when the initial term and variation are in `Lᵖ`. -/
theorem lintegral_rpow_two_norm_add_toReal_lt_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ}
    (hp : 0 < p) (V : X → ℝ≥0∞) (f : X → ℂ)
    (hV : MemLp V (ENNReal.ofReal p) μ)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    ∫⁻ x, (ENNReal.ofReal (2 * (‖f x‖ + (V x).toReal))).rpow p ∂μ < ∞ := by
  have hG : MemLp (fun x => 2 * (‖f x‖ + (V x).toReal))
      (ENNReal.ofReal p) μ :=
    (memLp_norm_add_toReal_of_memLp_ennreal hp V f hV hf).const_mul 2
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hlin := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop
    hG.aestronglyMeasurable).mp hG
  have hpow : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal (le_of_lt hp)
  have hcongr : ∀ x,
      (ENNReal.ofReal (2 * (‖f x‖ + (V x).toReal))).rpow p =
        ‖2 * (‖f x‖ + (V x).toReal)‖ₑ ^ (ENNReal.ofReal p).toReal := by
    intro x
    have hg : 0 ≤ 2 * (‖f x‖ + (V x).toReal) :=
      mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)
    rw [ENNReal.rpow_eq_pow, hpow, ← ofReal_norm, Real.norm_of_nonneg hg]
  rw [lintegral_congr_ae (ae_of_all μ hcongr)]
  exact hlin

private def scaleSucc (N : Scale) : Scale :=
  ⟨N.1 + 1, Nat.succ_pos _⟩

private theorem lt_scaleSucc (N : Scale) : N < scaleSucc N := by
  change N.1 < N.1 + 1
  omega

private theorem exists_separated_pairs_of_not_cauchy (u : Scale → ℂ)
    (hcauchy : ¬ CauchySeq u) :
    ∃ ε > 0, ∀ N : Scale, ∃ m n : Scale,
      N ≤ m ∧ m < n ∧ ε ≤ ‖u n - u m‖ := by
  rw [Metric.cauchySeq_iff] at hcauchy
  push Not at hcauchy
  obtain ⟨ε, hε, hbad⟩ := hcauchy
  refine ⟨ε, hε, fun N => ?_⟩
  obtain ⟨m, hmN, n, hnN, hmn⟩ := hbad N
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact ⟨m, n, hmN, hlt, by
      simpa [dist_eq_norm, norm_sub_rev] using hmn⟩
  · subst n
    simp only [dist_self] at hmn
    linarith
  · exact ⟨n, m, hnN, hgt, by simpa [dist_eq_norm] using hmn⟩

private theorem exists_interlaced_pairs {u : Scale → ℂ} {ε : ℝ}
    (hpairs : ∀ N : Scale, ∃ m n : Scale,
      N ≤ m ∧ m < n ∧ ε ≤ ‖u n - u m‖) :
    ∃ p : ℕ → Scale × Scale,
      (∀ k, (p k).1 < (p k).2) ∧
        (∀ k, (p k).2 < (p (k + 1)).1) ∧
          ∀ k, ε ≤ ‖u (p k).2 - u (p k).1‖ := by
  classical
  choose left right hleft hlt hsep using hpairs
  let base : Scale := ⟨1, Nat.succ_pos 0⟩
  let p : ℕ → Scale × Scale := Nat.rec (left base, right base)
    (fun _ q => (left (scaleSucc q.2), right (scaleSucc q.2)))
  refine ⟨p, ?_, ?_, ?_⟩
  · intro k
    cases k with
    | zero => simpa [p] using hlt base
    | succ k => simpa [p] using hlt (scaleSucc (p k).2)
  · intro k
    simpa [p] using (lt_scaleSucc (p k).2).trans_le (hleft (scaleSucc (p k).2))
  · intro k
    cases k with
    | zero => simpa [p] using hsep base
    | succ k => simpa [p] using hsep (scaleSucc (p k).2)

private theorem interlaced_pairs_strictMono (p : ℕ → Scale × Scale)
    (hwithin : ∀ k, (p k).1 < (p k).2)
    (hbetween : ∀ k, (p k).2 < (p (k + 1)).1) :
    ∃ t : ℕ → Scale, StrictMono t ∧
      (∀ k, t (2 * k) = (p k).1) ∧
        ∀ k, t (2 * k + 1) = (p k).2 := by
  let t : ℕ → Scale := fun n =>
    if n % 2 = 0 then (p (n / 2)).1 else (p (n / 2)).2
  have ht_succ : ∀ n, t n < t (n + 1) := by
    intro n
    rcases n.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hmod0 : (k + k) % 2 = 0 := by omega
      have hdiv0 : (k + k) / 2 = k := by omega
      have hmod1 : (k + k + 1) % 2 ≠ 0 := by omega
      have hdiv1 : (k + k + 1) / 2 = k := by omega
      simpa [t, hmod0, hdiv0, hmod1, hdiv1] using hwithin k
    · have hmod0 : (2 * k + 1) % 2 ≠ 0 := by omega
      have hdiv0 : (2 * k + 1) / 2 = k := by omega
      have hmod1 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have hdiv1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      simpa [t, hmod0, hdiv0, hmod1, hdiv1] using hbetween k
  refine ⟨t, strictMono_nat_of_lt_succ ht_succ, ?_, ?_⟩
  · intro k
    have hmod : (2 * k) % 2 = 0 := by omega
    have hdiv : (2 * k) / 2 = k := by omega
    simp [t, hmod, hdiv]
  · intro k
    have hdiv : (2 * k + 1) / 2 = k := by omega
    simp [t, hdiv]

private def evenIndex (K : ℕ) : Fin K ↪ Fin (2 * K) where
  toFun j := ⟨2 * j.1, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    change 2 * i.1 = 2 * j.1 at hval
    omega

private theorem evenIndex_castSucc_apply (K : ℕ) (j : Fin K) :
    ((evenIndex K j).castSucc : ℕ) = 2 * j.1 := by
  rfl

private theorem evenIndex_succ_apply (K : ℕ) (j : Fin K) :
    ((evenIndex K j).succ : ℕ) = 2 * j.1 + 1 := by
  rfl

private theorem rpow_sum_lower_bound_of_interlaced {u : Scale → ℂ} {r ε : ℝ}
    (hr : 0 < r) (p : ℕ → Scale × Scale) (t : ℕ → Scale)
    (heven : ∀ k, t (2 * k) = (p k).1)
    (hodd : ∀ k, t (2 * k + 1) = (p k).2)
    (hsep : ∀ k, ε ≤ ‖u (p k).2 - u (p k).1‖) (K : ℕ) :
    (K : ℝ≥0∞) * (ENNReal.ofReal ε).rpow r ≤
      ∑ i : Fin (2 * K),
        (ENNReal.ofReal ‖u (t i.succ) - u (t i.castSucc)‖).rpow r := by
  classical
  let f : Fin (2 * K) → ℝ≥0∞ := fun i =>
    (ENNReal.ofReal ‖u (t i.succ) - u (t i.castSucc)‖).rpow r
  let s : Finset (Fin (2 * K)) := Finset.univ.map (evenIndex K)
  have hterm : ∀ j : Fin K, (ENNReal.ofReal ε).rpow r ≤ f (evenIndex K j) := by
    intro j
    have hnorm : ε ≤ ‖u (t ((evenIndex K j).succ : ℕ)) -
        u (t ((evenIndex K j).castSucc : ℕ))‖ := by
      rw [evenIndex_succ_apply, evenIndex_castSucc_apply, hodd, heven]
      exact hsep j.1
    dsimp [f]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hnorm) hr.le
  calc
    (K : ℝ≥0∞) * (ENNReal.ofReal ε).rpow r =
        ∑ _j : Fin K, (ENNReal.ofReal ε).rpow r := by simp [nsmul_eq_mul]
    _ ≤ ∑ j : Fin K, f (evenIndex K j) := Finset.sum_le_sum fun j _ => hterm j
    _ = ∑ i ∈ s, f i := by
      simp [s]
    _ ≤ ∑ i : Fin (2 * K), f i :=
      Finset.sum_le_sum_of_subset_of_nonneg (by simp [s]) (by
        intro i _ _
        exact bot_le)
    _ = ∑ i : Fin (2 * K),
        (ENNReal.ofReal ‖u (t i.succ) - u (t i.castSucc)‖).rpow r := rfl

private theorem rpow_chain_sum_le_rVariation_rpow {u : Scale → ℂ} {r : ℝ}
    (hr : 0 < r) (t : ℕ → Scale) (ht : StrictMono t) (K : ℕ) :
    (∑ i : Fin (2 * K),
      (ENNReal.ofReal ‖u (t i.succ) - u (t i.castSucc)‖).rpow r) ≤
        (rVariation r u) ^ r := by
  let chain : StrictScaleChain (2 * K) :=
    { index := fun i => t i
      strictMono := ht.comp Fin.val_strictMono }
  have hchain' :
      (∑ i : Fin (2 * K),
        (ENNReal.ofReal ‖u (t i.succ) - u (t i.castSucc)‖).rpow r).rpow r⁻¹ ≤
          rVariation r u := by
    rw [rVariation_eq]
    exact le_iSup_of_le (2 * K) (le_iSup_of_le chain le_rfl)
  have hchainPow :
      (∑ i : Fin (2 * K),
        (ENNReal.ofReal ‖u (t i.succ) - u (t i.castSucc)‖).rpow r) ^ r⁻¹ ≤
          rVariation r u := by
    simpa only [ENNReal.rpow_eq_pow] using hchain'
  have hpow := ENNReal.rpow_le_rpow hchainPow hr.le
  simpa only [ENNReal.rpow_inv_rpow hr.ne'] using hpow

/-- Finite positive-exponent homogeneous variation forces convergence along the
positive integer scales. -/
theorem exists_tendsto_of_rVariation_ne_top (r : ℝ) (hr : 0 < r) (u : Scale → ℂ)
    (hfinite : rVariation r u ≠ ∞) :
    ∃ z : ℂ, Filter.Tendsto u Filter.atTop (nhds z) := by
  classical
  apply cauchySeq_tendsto_of_complete
  by_contra hcauchy
  obtain ⟨ε, hε, hpairs⟩ := exists_separated_pairs_of_not_cauchy u hcauchy
  obtain ⟨p, hwithin, hbetween, hsep⟩ := exists_interlaced_pairs hpairs
  obtain ⟨t, ht, heven, hodd⟩ := interlaced_pairs_strictMono p hwithin hbetween
  let a : ℝ≥0∞ := (ENNReal.ofReal ε).rpow r
  have ha : a ≠ 0 := by
    apply (ENNReal.rpow_eq_zero_iff_of_pos hr).not.mpr
    exact (ENNReal.ofReal_pos.mpr hε).ne'
  have hvarpow : (rVariation r u) ^ r ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hr.le hfinite
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_mul_gt ha hvarpow
  have hlower := rpow_sum_lower_bound_of_interlaced hr p t heven hodd hsep K
  have hupper := rpow_chain_sum_le_rVariation_rpow (u := u) hr t ht K
  exact (not_lt_of_ge (hlower.trans hupper) (by simpa [a] using hK))

/-- The same convergence conclusion with the finite-variation hypothesis written as `< ∞`. -/
theorem exists_tendsto_of_rVariation_lt_top (r : ℝ) (hr : 0 < r) (u : Scale → ℂ)
    (hfinite : rVariation r u < ∞) :
    ∃ z : ℂ, Filter.Tendsto u Filter.atTop (nhds z) :=
  exists_tendsto_of_rVariation_ne_top r hr u hfinite.ne

/-- Homogeneous variation controls every increment relative to an arbitrary base scale. -/
theorem enorm_sub_le_rVariation_of_base (r : ℝ) (hr : 0 < r) (u : Scale → ℂ)
    (base N : Scale) :
    ENNReal.ofReal ‖u N - u base‖ ≤ rVariation r u := by
  rcases lt_trichotomy base N with hlt | heq | hgt
  · exact enorm_sub_le_rVariation r hr u hlt
  · subst N
    simp
  · simpa [norm_sub_rev] using enorm_sub_le_rVariation r hr u hgt

/-- With finite variation, the anchored increment bound has its usual real-valued form. -/
theorem norm_sub_le_rVariation_toReal_of_base (r : ℝ) (hr : 0 < r) (u : Scale → ℂ)
    (hfinite : rVariation r u ≠ ∞) (base N : Scale) :
    ‖u N - u base‖ ≤ (rVariation r u).toReal := by
  rw [← ENNReal.toReal_ofReal (norm_nonneg _)]
  exact (ENNReal.toReal_le_toReal (by simp) hfinite).mpr
    (enorm_sub_le_rVariation_of_base r hr u base N)

/-- Pointwise finite variation gives convergence of a family of complex-valued functions. -/
theorem exists_tendsto_of_rVariationFun_ne_top {X : Type*} (r : ℝ) (hr : 0 < r)
    (F : Scale → X → ℂ) (x : X) (hfinite : rVariationFun r F x ≠ ∞) :
    ∃ z : ℂ, Filter.Tendsto (fun N : Scale => F N x) Filter.atTop (nhds z) := by
  rw [rVariationFun_apply] at hfinite
  exact exists_tendsto_of_rVariation_ne_top r hr (fun N => F N x) hfinite

/-- An `Lᵖ`-finite pointwise variation function implies almost-everywhere
convergence of the underlying complex sequence. -/
theorem ae_exists_tendsto_of_rVariationFun_memLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (F : Scale → X → ℂ)
    (hV : MemLp (rVariationFun r F) (ENNReal.ofReal p) μ) :
    ∀ᵐ x ∂μ, ∃ z : ℂ,
      Filter.Tendsto (fun N : Scale => F N x) Filter.atTop (nhds z) := by
  have hfinite := ae_lt_top_of_memLp_ennreal hp (rVariationFun r F) hV
  filter_upwards [hfinite] with x hx
  exact exists_tendsto_of_rVariationFun_ne_top r hr F x hx.ne

/-- Pointwise finite variation controls every member of a family by an arbitrary anchor. -/
theorem norm_le_norm_base_add_rVariationFun_toReal {X : Type*} (r : ℝ) (hr : 0 < r)
    (F : Scale → X → ℂ) (x : X) (hfinite : rVariationFun r F x ≠ ∞)
    (base N : Scale) :
    ‖F N x‖ ≤ ‖F base x‖ + (rVariationFun r F x).toReal := by
  have hinc := norm_sub_le_rVariation_toReal_of_base r hr (fun M => F M x) (by
    simpa only [rVariationFun_apply] using hfinite) base N
  calc
    ‖F N x‖ = ‖(F N x - F base x) + F base x‖ := by
      congr 1
      ring
    _ ≤ ‖F N x - F base x‖ + ‖F base x‖ := norm_add_le _ _
    _ ≤ (rVariationFun r F x).toReal + ‖F base x‖ := add_le_add hinc le_rfl
    _ = ‖F base x‖ + (rVariationFun r F x).toReal := add_comm _ _

/-- Almost-everywhere domination of every sequence member by the initial
member and the pointwise variation. -/
theorem ae_forall_norm_le_base_add_rVariationFun_toReal_of_memLp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (F : Scale → X → ℂ)
    (hV : MemLp (rVariationFun r F) (ENNReal.ofReal p) μ) :
    ∀ᵐ x ∂μ, ∀ N : Scale,
      ‖F N x‖ ≤ ‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal := by
  have hfinite := ae_lt_top_of_memLp_ennreal hp (rVariationFun r F) hV
  filter_upwards [hfinite] with x hx
  intro N
  exact norm_le_norm_base_add_rVariationFun_toReal r hr F x hx.ne ⟨1, by omega⟩ N

/-- Every member of the sequence is in `Lᵖ` when the first member and the
pointwise variation are in `Lᵖ` and the sequence is a.e. measurable. -/
theorem memLp_each_of_rVariationFun_memLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (F : Scale → X → ℂ)
    (hFmeas : ∀ N, AEStronglyMeasurable (F N) μ)
    (hV : MemLp (rVariationFun r F) (ENNReal.ofReal p) μ)
    (hFone : MemLp (F ⟨1, by omega⟩) (ENNReal.ofReal p) μ) :
    ∀ N, MemLp (F N) (ENNReal.ofReal p) μ := by
  have hmajorant : MemLp
      (fun x => 2 * (‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal))
      (ENNReal.ofReal p) μ := by
    exact (memLp_norm_add_toReal_of_memLp_ennreal hp
      (rVariationFun r F) (F ⟨1, by omega⟩) hV hFone).const_mul 2
  have hdom := ae_forall_norm_le_base_add_rVariationFun_toReal_of_memLp
    hp hr F hV
  intro N
  apply hmajorant.of_le (hFmeas N)
  filter_upwards [hdom] with x hx
  have hM : 0 ≤ ‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal :=
    add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  calc
    ‖F N x‖ ≤ ‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal := hx N
    _ ≤ ‖2 * (‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal)‖ := by
      rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) hM)]
      nlinarith

/-- Select a strongly measurable representative of the a.e. limit along the
positive integer scales, with the same initial-term-plus-variation bound. -/
theorem exists_stronglyMeasurable_limit_of_rVariationFun_memLp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (F : Scale → X → ℂ)
    (hFmeas : ∀ N, AEStronglyMeasurable (F N) μ)
    (hV : MemLp (rVariationFun r F) (ENNReal.ofReal p) μ) :
    ∃ g : X → ℂ, StronglyMeasurable g ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun n : ℕ => F ⟨n + 1, by omega⟩ x)
        Filter.atTop (nhds (g x))) ∧
      (∀ᵐ x ∂μ, ‖g x‖ ≤ ‖F ⟨1, by omega⟩ x‖ +
        (rVariationFun r F x).toReal) := by
  let scaleNat (n : ℕ) : Scale := ⟨n + 1, by omega⟩
  have hscaleNat : Filter.Tendsto scaleNat Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [Filter.eventually_ge_atTop N.1] with n hn
    exact show N ≤ scaleNat n by
      change N.1 ≤ n + 1
      omega
  have haeSeq := ae_exists_tendsto_of_rVariationFun_memLp hp hr F hV
  have haeNat : ∀ᵐ x ∂μ, ∃ z : ℂ,
      Filter.Tendsto (fun n : ℕ => F (scaleNat n) x) Filter.atTop (nhds z) := by
    filter_upwards [haeSeq] with x hx
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, hz.comp hscaleNat⟩
  obtain ⟨g, hgStrong, hgLim⟩ :=
    exists_stronglyMeasurable_limit_of_tendsto_ae
      (fun n => hFmeas (scaleNat n)) haeNat
  have hdom := ae_forall_norm_le_base_add_rVariationFun_toReal_of_memLp
    hp hr F hV
  refine ⟨g, hgStrong, hgLim, ?_⟩
  filter_upwards [hgLim, hdom] with x hxlim hxdom
  have hnorm := hxlim.norm
  apply le_of_tendsto_of_tendsto' hnorm tendsto_const_nhds
  intro n
  exact hxdom (scaleNat n)

/-- The positive-scale sequence converges in `Lᵖ` when its pointwise
variation and initial member are in `Lᵖ` and all terms are a.e. measurable. -/
theorem exists_limit_and_tendsto_eLpNorm_of_rVariationFun_memLp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p r : ℝ}
    (hp : 1 ≤ p) (hr : 0 < r) (F : Scale → X → ℂ)
    (hFmeas : ∀ N, AEStronglyMeasurable (F N) μ)
    (hV : MemLp (rVariationFun r F) (ENNReal.ofReal p) μ)
    (hFone : MemLp (F ⟨1, by omega⟩) (ENNReal.ofReal p) μ) :
    ∃ g : X → ℂ, StronglyMeasurable g ∧
      MemLp g (ENNReal.ofReal p) μ ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun n : ℕ => F ⟨n + 1, by omega⟩ x)
        Filter.atTop (nhds (g x))) ∧
      Filter.Tendsto
        (fun n : ℕ => eLpNorm (fun x => F ⟨n + 1, by omega⟩ x - g x)
          (ENNReal.ofReal p) μ) Filter.atTop (nhds 0) := by
  let scaleNat (n : ℕ) : Scale := ⟨n + 1, by omega⟩
  have hscaleNat : Filter.Tendsto scaleNat Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [Filter.eventually_ge_atTop N.1] with n hn
    exact show N ≤ scaleNat n by
      change N.1 ≤ n + 1
      omega
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hmajorant : MemLp
      (fun x => 2 * (‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal))
      (ENNReal.ofReal p) μ :=
    (memLp_norm_add_toReal_of_memLp_ennreal hp0
      (rVariationFun r F) (F ⟨1, by omega⟩) hV hFone).const_mul 2
  have ⟨g, hgStrong, hgLim, hgBound⟩ :=
    exists_stronglyMeasurable_limit_of_rVariationFun_memLp hp0 hr F hFmeas hV
  have hgMemLp : MemLp g (ENNReal.ofReal p) μ := by
    apply hmajorant.of_le hgStrong.aestronglyMeasurable
    filter_upwards [hgBound] with x hx
    have hM : 0 ≤ ‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal :=
      add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
    calc
      ‖g x‖ ≤ ‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal := hx
      _ ≤ ‖2 * (‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal)‖ := by
        rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) hM)]
        nlinarith
  have hpENN0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hpENNtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpToReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal (le_of_lt hp0)
  let G : ℕ → X → ℝ≥0∞ := fun n x =>
    ‖F (scaleNat n) x - g x‖ₑ ^ p
  let B : X → ℝ≥0∞ := fun x =>
    (ENNReal.ofReal (2 * (‖F ⟨1, by omega⟩ x‖ +
      (rVariationFun r F x).toReal))).rpow p
  have hBfin : ∫⁻ x, B x ∂μ < ∞ :=
    lintegral_rpow_two_norm_add_toReal_lt_top hp0 (rVariationFun r F)
      (F ⟨1, by omega⟩) hV hFone
  have hGmeas : ∀ n, AEMeasurable (G n) μ := by
    intro n
    exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable
      (((hFmeas (scaleNat n)).sub hgStrong.aestronglyMeasurable).enorm)
  have hGdom : ∀ n, G n ≤ᵐ[μ] B := by
    intro n
    have hseqDom := ae_forall_norm_le_base_add_rVariationFun_toReal_of_memLp
      hp0 hr F hV
    filter_upwards [hseqDom, hgBound] with x hx hlim
    have hM : 0 ≤ ‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal :=
      add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
    have hdiff : ‖F (scaleNat n) x - g x‖ ≤
        2 * (‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal) := by
      calc
        ‖F (scaleNat n) x - g x‖ ≤ ‖F (scaleNat n) x‖ + ‖g x‖ := norm_sub_le _ _
        _ ≤ (‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal) +
            (‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal) :=
          add_le_add (hx (scaleNat n)) hlim
        _ = 2 * (‖F ⟨1, by omega⟩ x‖ + (rVariationFun r F x).toReal) := by ring
    dsimp [G, B]
    apply ENNReal.rpow_le_rpow _ hp0.le
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hdiff
  have hGlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => G n x) Filter.atTop (nhds 0) := by
    filter_upwards [hgLim] with x hx
    let ψ : ℂ → ℝ≥0∞ := fun z => (ENNReal.ofReal ‖z - g x‖).rpow p
    have hψ : Continuous ψ := by
      dsimp [ψ]
      exact ENNReal.continuous_rpow_const.comp
        (ENNReal.continuous_ofReal.comp (continuous_norm.comp
          (continuous_id.sub continuous_const)))
    have hψ0 : ψ (g x) = 0 := by
      simp [ψ, ENNReal.zero_rpow_of_pos hp0]
    have h := hψ.continuousAt.tendsto.comp hx
    rw [hψ0] at h
    have hfun : (fun n => G n x) = ψ ∘ (fun n => F (scaleNat n) x) := by
      funext n
      simp [G, ψ, ofReal_norm]
    rw [hfun]
    exact h
  have hInt := tendsto_lintegral_of_dominated_convergence' B hGmeas hGdom
    hBfin.ne hGlim
  have hInt0 : Filter.Tendsto (fun n => ∫⁻ x, G n x ∂μ)
      Filter.atTop (nhds 0) := by
    simpa [G] using hInt
  have hNormFormula (n : ℕ) :
      eLpNorm (fun x => F (scaleNat n) x - g x) (ENNReal.ofReal p) μ =
        (∫⁻ x, G n x ∂μ) ^ (1 / p) := by
    change eLpNorm (F (scaleNat n) - g) (ENNReal.ofReal p) μ = _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpENN0 hpENNtop
      (((hFmeas (scaleNat n)).sub hgStrong.aestronglyMeasurable))]
    simp [G, hpToReal]
  have hRoot := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0 |>.comp hInt0
  have hpRoot : 0 < 1 / p := one_div_pos.mpr hp0
  have hRoot0 : Filter.Tendsto (fun n => (∫⁻ x, G n x ∂μ) ^ (1 / p))
      Filter.atTop (nhds 0) := by
    convert hRoot using 1
    · funext n
      rfl
    · exact congrArg nhds (ENNReal.zero_rpow_of_pos hpRoot).symm
  refine ⟨g, hgStrong, hgMemLp, hgLim, ?_⟩
  convert hRoot0 using 1
  funext n
  exact hNormFormula n

end

end FractionalPrimes
