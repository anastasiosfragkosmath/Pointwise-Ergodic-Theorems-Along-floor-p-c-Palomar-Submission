module

public import FractionalPrimes.Literature.Multiplier.WeakType
public import FractionalPrimes.FiniteInterpolationSplit
public import FractionalPrimes.FiniteOutputLayercake
public import FractionalPrimes.FiniteMomentExhaustion
public import FractionalPrimes.InterpolationWeightedLayercake

/-!
# Layer-cake interpolation for the periodic multiplier (`lp:interpolation`)

The first step is the exact strict-level distribution estimate after the
finite high/low input split.  The high part uses the weak `(1,1)` endpoint;
the low part uses the `ℓ²` endpoint and Chebyshev.  The cutoff equality case
belongs to the low part, as in the approved blueprint.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem weakStrongInterpolation_level_ncard_sq_le
    (u : lp (fun _ : ℤ => ℂ) 2) (r : ℝ) (hr : 0 < r) :
    (Set.ncard {x : ℤ | r < ‖u x‖} : ℝ) * r ^ 2 ≤ ‖u‖ ^ 2 := by
  let v : Lp ℂ 2 (Measure.count : Measure ℤ) := lpToCountLp u
  let rN : NNReal := ⟨r, le_of_lt hr⟩
  have hrNpos : 0 < rN := by exact_mod_cast hr
  let E : Set ℤ := {x | r < ‖u x‖}
  let G : Set ℤ := {x | rN ≤ ‖(v : ℤ → ℂ) x‖₊}
  have hmem : MemLp (v : ℤ → ℂ) 2 Measure.count := by
    rw [show (v : ℤ → ℂ) = (u : ℤ → ℂ) by
      funext x
      exact lpToCountLp_apply u x]
    exact memLp_count_of_meml2 u
  have hfiniteG : G.Finite := by
    apply (Measure.count_apply_lt_top).mp
    simpa [G] using hmem.meas_ge_lt_top (by norm_num) (by norm_num)
      (ne_of_gt hrNpos)
  have hsub : E ⊆ G := by
    intro x hx
    have hcoord : (v : ℤ → ℂ) x = u x := lpToCountLp_apply u x
    change rN ≤ ‖(v : ℤ → ℂ) x‖₊
    rw [hcoord]
    change rN ≤ ‖(u : ℤ → ℂ) x‖₊
    exact_mod_cast le_of_lt hx
  have hfiniteE : E.Finite := hfiniteG.subset hsub
  have hcheb := MeasureTheory.mul_meas_ge_le_pow_eLpNorm'
    (Measure.count : Measure ℤ) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (f := (v : ℤ → ℂ)) (rN : ℝ≥0∞)
  have hset : {x : ℤ | (rN : ℝ≥0∞) ≤ ‖(v : ℤ → ℂ) x‖ₑ} = G := by
    ext x
    simp [G]
  rw [hset] at hcheb
  have hcardCount : (E.ncard : ℝ≥0∞) ≤ Measure.count G := by
    have h : Measure.count E ≤ Measure.count G := measure_mono hsub
    simpa [Measure.count_apply_finite E hfiniteE,
      Set.ncard_eq_toFinset_card E hfiniteE] using h
  have hcardEnn : (rN : ℝ≥0∞) ^ 2 * (E.ncard : ℝ≥0∞) ≤
      eLpNorm (v : ℤ → ℂ) 2 Measure.count ^ 2 := by
    calc
      _ ≤ (rN : ℝ≥0∞) ^ 2 * Measure.count G :=
        mul_le_mul_of_nonneg_left hcardCount (sq_nonneg (rN : ℝ≥0∞))
      _ ≤ _ := by simpa using hcheb
  have heLpNormLt : eLpNorm (v : ℤ → ℂ) 2 Measure.count < ∞ := hmem.eLpNorm_lt_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.pow_ne_top heLpNormLt.ne) hcardEnn
  have hnorm : (eLpNorm (v : ℤ → ℂ) 2 Measure.count).toReal = ‖u‖ := by
    rw [← Lp.norm_def v]
    change ‖lpToCountLp u‖ = ‖u‖
    exact lpToCountLpIsometry.norm_map u
  have hcardReal : (E.ncard : ℝ) = ((E.ncard : ℝ≥0∞).toReal) := by simp
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ← hcardReal, ENNReal.coe_toReal, hnorm] at hreal
  have hrN : (rN : ℝ) = r := rfl
  rw [hrN] at hreal
  have htarget : (E.ncard : ℝ) * r ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith [hreal]
  simpa [E] using htarget

private theorem weakStrongInterpolation_level_set_finite
    (u : lp (fun _ : ℤ => ℂ) 2) (r : ℝ) (hr : 0 < r) :
    {x : ℤ | r < ‖u x‖}.Finite := by
  let v : Lp ℂ 2 (Measure.count : Measure ℤ) := lpToCountLp u
  let rN : NNReal := ⟨r, le_of_lt hr⟩
  have hrNpos : 0 < rN := by exact_mod_cast hr
  let E : Set ℤ := {x | r < ‖u x‖}
  let G : Set ℤ := {x | rN ≤ ‖(v : ℤ → ℂ) x‖₊}
  have hmem : MemLp (v : ℤ → ℂ) 2 Measure.count := by
    rw [show (v : ℤ → ℂ) = (u : ℤ → ℂ) by
      funext x
      exact lpToCountLp_apply u x]
    exact memLp_count_of_meml2 u
  have hfiniteG : G.Finite := by
    apply (Measure.count_apply_lt_top).mp
    simpa [G] using hmem.meas_ge_lt_top (by norm_num) (by norm_num)
      (ne_of_gt hrNpos)
  have hsub : E ⊆ G := by
    intro x hx
    have hcoord : (v : ℤ → ℂ) x = u x := lpToCountLp_apply u x
    change rN ≤ ‖(v : ℤ → ℂ) x‖₊
    rw [hcoord]
    change rN ≤ ‖(u : ℤ → ℂ) x‖₊
    exact_mod_cast le_of_lt hx
  exact hfiniteG.subset hsub

private theorem weakStrongInterpolation_discreteL2_sum_of_support_subset
    (f : ℤ → ℂ) (s : Finset ℤ)
    (hsub : Function.support f ⊆ (s : Set ℤ)) :
    discreteL2NormSq f = ∑ k ∈ s, ‖f k‖ ^ 2 := by
  rw [discreteL2NormSq]
  apply tsum_eq_sum (s := s)
  intro k hk
  have hzero : f k = 0 := by
    by_contra hne
    exact hk (hsub (Function.mem_support.mpr hne))
  simp [hzero]

private theorem weakStrongInterpolation_finiteL2_support_subset
    (s : Finset ℤ) (f : ℤ → ℂ) :
    Function.support (finiteIntegerSequenceL2 s f : ℤ → ℂ) ⊆ (s : Set ℤ) := by
  intro k hk
  by_contra hnot
  have hnotFinset : k ∉ s := by simpa using hnot
  have hzero : finiteIntegerSequenceL2 s f k = 0 := by
    rw [finiteIntegerSequenceL2_apply]
    simp [hnotFinset]
  exact (Function.mem_support.mp hk) hzero

private theorem weakStrongInterpolation_finiteL2_hasFiniteSupport
    (s : Finset ℤ) (f : ℤ → ℂ) :
    (finiteIntegerSequenceL2 s f : ℤ → ℂ).HasFiniteSupport := by
  apply s.finite_toSet.subset
  exact weakStrongInterpolation_finiteL2_support_subset s f

/-- The exact low/high strict-level estimate with the blueprint's original
finite-support domain. The weak and strong endpoint hypotheses range only
over Finsupp inputs. The low filter is inclusive at the cutoff, while the
high filter is strict, and the constants are unchanged. -/
theorem weakStrongInterpolation_finsupp_low_high_distribution
    (U : (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2)
    (hweak : ∀ f : ℤ →₀ ℂ, ∀ r : ℝ, 0 < r →
      (Set.ncard {x : ℤ | r < ‖U f x‖} : ℝ) ≤
        W / r * discreteL1Norm (f : ℤ → ℂ))
    (hstrong : ∀ f : ℤ →₀ ℂ,
      ‖U f‖ ≤ ‖finiteSequenceL2 f‖)
    (f : ℤ →₀ ℂ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (Set.ncard {x : ℤ | threshold < ‖U f x‖} : ℝ) ≤
      2 * W / threshold * (∑ k ∈ f.support,
        if threshold < ‖f k‖ then ‖f k‖ else 0) +
      4 / threshold ^ 2 * (∑ k ∈ f.support,
        if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) := by
  classical
  let low : ℤ →₀ ℂ := f.filter (fun k => ‖f k‖ ≤ threshold)
  let high : ℤ →₀ ℂ := f.filter (fun k => ¬ ‖f k‖ ≤ threshold)
  let lowFn : ℤ → ℂ := low
  let highFn : ℤ → ℂ := high
  have hsplit : f = low + high := by
    dsimp [low, high]
    simpa [not_le] using
      (Finsupp.filter_add_filter_not f (fun k => ‖f k‖ ≤ threshold)).symm
  have hUdecomp : U f = U low + U high := by
    calc
      U f = U (low + high) := by rw [hsplit]
      _ = U low + U high := map_add U low high
  have hlowSupport : Function.support lowFn ⊆ (f.support : Set ℤ) := by
    intro k hk
    have hmem : k ∈ low.support :=
      Finsupp.mem_support_iff.mpr (Function.mem_support.mp hk)
    rw [Finsupp.support_filter] at hmem
    exact (Finset.mem_filter.mp hmem).1
  have hhighSupport : Function.support highFn ⊆ (f.support : Set ℤ) := by
    intro k hk
    have hmem : k ∈ high.support :=
      Finsupp.mem_support_iff.mpr (Function.mem_support.mp hk)
    rw [Finsupp.support_filter] at hmem
    exact (Finset.mem_filter.mp hmem).1
  have hlowFinite : lowFn.HasFiniteSupport := low.hasFiniteSupport
  have hhighFinite : highFn.HasFiniteSupport := high.hasFiniteSupport
  have hlowL2 : finiteSequenceL2 low =
      finiteIntegerSequenceL2 hlowFinite.toFinset lowFn := by
    apply lp.ext
    funext k
    rw [finiteIntegerSequenceL2_apply, finiteSequenceL2_apply]
    by_cases hk : k ∈ hlowFinite.toFinset
    · simp [lowFn, hk]
    · have hzero : lowFn k = 0 := by
        change low k = 0
        by_contra hne
        exact hk (hlowFinite.mem_toFinset.mpr (Function.mem_support.mpr hne))
      simp [lowFn, hk, hzero]
  have hlowMoment : ‖finiteSequenceL2 low‖ ^ 2 =
      ∑ k ∈ f.support, if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0 := by
    rw [hlowL2,
      finiteIntegerSequenceL2_norm_sq_eq_discreteL2NormSq lowFn hlowFinite,
      weakStrongInterpolation_discreteL2_sum_of_support_subset
        lowFn f.support hlowSupport]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : ‖f k‖ ≤ threshold
    · simp [lowFn, low, Finsupp.filter_apply, h]
    · simp [lowFn, low, Finsupp.filter_apply, h]
  have hhighMass : discreteL1Norm highFn =
      ∑ k ∈ f.support, if threshold < ‖f k‖ then ‖f k‖ else 0 := by
    rw [discreteL1Norm_eq_sum_of_support_subset highFn f.support hhighSupport]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : threshold < ‖f k‖
    · simp [highFn, high, Finsupp.filter_apply, not_le, h]
    · have hle : ‖f k‖ ≤ threshold := le_of_not_gt h
      simp [highFn, high, Finsupp.filter_apply, not_le, hle]
  let lowLevel : Set ℤ := {x | threshold / 2 < ‖U low x‖}
  let highLevel : Set ℤ := {x | threshold / 2 < ‖U high x‖}
  let level : Set ℤ := {x | threshold < ‖U f x‖}
  have hlowFiniteLevel : lowLevel.Finite := by
    simpa [lowLevel] using weakStrongInterpolation_level_set_finite
      (U low) (threshold / 2) (by positivity)
  have hhighFiniteLevel : highLevel.Finite := by
    simpa [highLevel] using weakStrongInterpolation_level_set_finite
      (U high) (threshold / 2) (by positivity)
  have hlevels : level ⊆ lowLevel ∪ highLevel := by
    intro x hx
    by_cases hlow : threshold / 2 < ‖U low x‖
    · exact Or.inl hlow
    · by_cases hhigh : threshold / 2 < ‖U high x‖
      · exact Or.inr hhigh
      · have hlowBound : ‖U low x‖ ≤ threshold / 2 := le_of_not_gt hlow
        have hhighBound : ‖U high x‖ ≤ threshold / 2 := le_of_not_gt hhigh
        have hpoint : U f x = U low x + U high x := by
          exact congrArg (fun g : lp (fun _ : ℤ => ℂ) 2 => g x) hUdecomp
        have hbound : ‖U f x‖ ≤ threshold := by
          rw [hpoint]
          calc
            ‖U low x + U high x‖ ≤ ‖U low x‖ + ‖U high x‖ := norm_add_le _ _
            _ ≤ threshold / 2 + threshold / 2 := add_le_add hlowBound hhighBound
            _ = threshold := by ring
        exact False.elim ((not_lt_of_ge hbound) hx)
  have hunionFinite : (lowLevel ∪ highLevel).Finite :=
    hlowFiniteLevel.union hhighFiniteLevel
  have hcountUnion : (Set.ncard level : ℝ) ≤
      (Set.ncard lowLevel : ℝ) + (Set.ncard highLevel : ℝ) := by
    calc
      (Set.ncard level : ℝ) ≤ Set.ncard (lowLevel ∪ highLevel) := by
        exact_mod_cast Set.ncard_le_ncard hlevels hunionFinite
      _ ≤ Set.ncard lowLevel + Set.ncard highLevel := by
        exact_mod_cast Set.ncard_union_le lowLevel highLevel
  have hlowCheb := weakStrongInterpolation_level_ncard_sq_le
    (U low) (threshold / 2) (by positivity)
  have hlowStrongSq : ‖U low‖ ^ 2 ≤ ‖finiteSequenceL2 low‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg (U low))
      (norm_nonneg (finiteSequenceL2 low))).2 (hstrong low)
  have hlowCount : (Set.ncard lowLevel : ℝ) ≤
      4 / threshold ^ 2 * (∑ k ∈ f.support,
        if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) := by
    have hden : 0 < (threshold / 2) ^ 2 := sq_pos_of_pos (by positivity)
    have hbound : (Set.ncard lowLevel : ℝ) ≤
        ‖finiteSequenceL2 low‖ ^ 2 / (threshold / 2) ^ 2 := by
      apply (le_div_iff₀ hden).2
      calc
        (Set.ncard lowLevel : ℝ) * (threshold / 2) ^ 2 ≤ ‖U low‖ ^ 2 := by
          simpa [lowLevel] using hlowCheb
        _ ≤ ‖finiteSequenceL2 low‖ ^ 2 := hlowStrongSq
    rw [hlowMoment] at hbound
    have hcoef : (∑ k ∈ f.support,
          if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) /
          (threshold / 2) ^ 2 =
        4 / threshold ^ 2 * (∑ k ∈ f.support,
          if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) := by
      field_simp [ne_of_gt hthreshold]
      ring
    rw [hcoef] at hbound
    exact hbound
  have hhighWeak := hweak high (threshold / 2) (by positivity)
  have hhighL1 : discreteL1Norm (high : ℤ → ℂ) =
      ∑ k ∈ f.support, if threshold < ‖f k‖ then ‖f k‖ else 0 := by
    simpa [highFn] using hhighMass
  have hhighCount : (Set.ncard highLevel : ℝ) ≤
      2 * W / threshold * (∑ k ∈ f.support,
        if threshold < ‖f k‖ then ‖f k‖ else 0) := by
    have hfactor : W / (threshold / 2) = 2 * W / threshold := by
      field_simp [ne_of_gt hthreshold]
    have hhighWeak' := hhighWeak
    rw [hfactor, hhighL1] at hhighWeak'
    simpa [highLevel] using hhighWeak'
  dsimp [level]
  calc
    (Set.ncard {x : ℤ | threshold < ‖U f x‖} : ℝ) ≤
        (Set.ncard lowLevel : ℝ) + (Set.ncard highLevel : ℝ) := hcountUnion
    _ ≤ 2 * W / threshold * (∑ k ∈ f.support,
          if threshold < ‖f k‖ then ‖f k‖ else 0) +
        4 / threshold ^ 2 * (∑ k ∈ f.support,
          if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) := by
      simpa [add_comm] using add_le_add hlowCount hhighCount

/-- The exact low/high strict-level estimate needed by `lp:interpolation`.
The operator is linear on `ℓ²`, obeys the weak `(1,1)` endpoint on finite
inputs, and is contractive on `ℓ²`. The high cutoff is strict and the low
cutoff is inclusive, with the blueprint constants unchanged. -/
theorem weakStrongInterpolation_low_high_distribution
    (U : lp (fun _ : ℤ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2)
    (hweak : ∀ u : lp (fun _ : ℤ => ℂ) 2,
      (u : ℤ → ℂ).HasFiniteSupport → ∀ r : ℝ, 0 < r →
        (Set.ncard {x : ℤ | r < ‖U u x‖} : ℝ) ≤
          W / r * discreteL1Norm (u : ℤ → ℂ))
    (hstrong : ∀ u : lp (fun _ : ℤ => ℂ) 2,
      (u : ℤ → ℂ).HasFiniteSupport → ‖U u‖ ≤ ‖u‖)
    (s : Finset ℤ) (f : ℤ → ℂ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (Set.ncard {x : ℤ |
      threshold < ‖U (finiteIntegerSequenceL2 s f) x‖} : ℝ) ≤
      2 * W / threshold * (∑ k ∈ s,
        if threshold < ‖f k‖ then ‖f k‖ else 0) +
      4 / threshold ^ 2 * (∑ k ∈ s,
        if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) := by
  classical
  let lowFn : ℤ → ℂ := finiteLowPart s threshold f
  let highFn : ℤ → ℂ := finiteHighPart s threshold f
  let input : lp (fun _ : ℤ => ℂ) 2 := finiteIntegerSequenceL2 s f
  have hlowSupport : Function.support lowFn ⊆ (s : Set ℤ) := by
    intro k hk
    by_contra hnot
    have hnotFinset : k ∉ s := by simpa using hnot
    have hzero : lowFn k = 0 := by
      simpa [lowFn] using
        finiteLowPart_eq_zero_of_not_mem s threshold f hnotFinset
    exact (Function.mem_support.mp hk) hzero
  have hhighSupport : Function.support highFn ⊆ (s : Set ℤ) := by
    intro k hk
    by_contra hnot
    have hnotFinset : k ∉ s := by simpa using hnot
    have hzero : highFn k = 0 := by
      simpa [highFn] using
        finiteHighPart_eq_zero_of_not_mem s threshold f hnotFinset
    exact (Function.mem_support.mp hk) hzero
  have hlowFinite : lowFn.HasFiniteSupport := by
    apply s.finite_toSet.subset
    exact hlowSupport
  have hhighFinite : highFn.HasFiniteSupport := by
    apply s.finite_toSet.subset
    exact hhighSupport
  let low : lp (fun _ : ℤ => ℂ) 2 :=
    finiteIntegerSequenceL2 hlowFinite.toFinset lowFn
  let high : lp (fun _ : ℤ => ℂ) 2 :=
    finiteIntegerSequenceL2 hhighFinite.toFinset highFn
  have hlowRep : (low : ℤ → ℂ) = lowFn := by
    funext k
    change finiteIntegerSequenceL2 hlowFinite.toFinset lowFn k = lowFn k
    rw [finiteIntegerSequenceL2_apply]
    by_cases hk : k ∈ hlowFinite.toFinset
    · simp [hk]
    · have hzero : lowFn k = 0 := by
        by_contra hne
        exact hk (hlowFinite.mem_toFinset.mpr (Function.mem_support.mpr hne))
      simp [hk, hzero]
  have hhighRep : (high : ℤ → ℂ) = highFn := by
    funext k
    change finiteIntegerSequenceL2 hhighFinite.toFinset highFn k = highFn k
    rw [finiteIntegerSequenceL2_apply]
    by_cases hk : k ∈ hhighFinite.toFinset
    · simp [hk]
    · have hzero : highFn k = 0 := by
        by_contra hne
        exact hk (hhighFinite.mem_toFinset.mpr (Function.mem_support.mpr hne))
      simp [hk, hzero]
  have hsplit : input = low + high := by
    apply lp.ext
    funext k
    simp only [lp.coeFn_add]
    change finiteIntegerSequenceL2 s f k = (low : ℤ → ℂ) k + (high : ℤ → ℂ) k
    rw [hlowRep, hhighRep]
    simpa [lowFn, highFn] using
        finiteIntegerSequenceL2_eq_finiteLowPart_add_finiteHighPart s threshold f k
  have hUdecomp : U input = U low + U high := by
    calc
      U input = U (low + high) := by rw [hsplit]
      _ = U low + U high := map_add U low high
  have hlowMoment : ‖low‖ ^ 2 =
      ∑ k ∈ s, if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0 := by
    change ‖finiteIntegerSequenceL2 hlowFinite.toFinset
      (finiteLowPart s threshold f)‖ ^ 2 = _
    rw [finiteIntegerSequenceL2_norm_sq_eq_discreteL2NormSq
        (finiteLowPart s threshold f) hlowFinite,
      weakStrongInterpolation_discreteL2_sum_of_support_subset
        (finiteLowPart s threshold f) s hlowSupport,
      sum_norm_sq_finiteLowPart, Finset.sum_filter]
  have hhighL2Support : Function.support (high : ℤ → ℂ) ⊆ (s : Set ℤ) := by
    intro k hk
    have hne : highFn k ≠ 0 := by
      simpa only [hhighRep] using (Function.mem_support.mp hk)
    exact hhighSupport (Function.mem_support.mpr hne)
  have hhighL2Finite : (high : ℤ → ℂ).HasFiniteSupport := by
    exact weakStrongInterpolation_finiteL2_hasFiniteSupport
      hhighFinite.toFinset highFn
  have hlowL2Finite : (low : ℤ → ℂ).HasFiniteSupport := by
    exact weakStrongInterpolation_finiteL2_hasFiniteSupport
      hlowFinite.toFinset lowFn
  have hhighMass : discreteL1Norm (high : ℤ → ℂ) =
      ∑ k ∈ s, if threshold < ‖f k‖ then ‖f k‖ else 0 := by
    rw [discreteL1Norm_eq_sum_of_support_subset (high : ℤ → ℂ) s
      hhighL2Support]
    rw [hhighRep]
    change (∑ k ∈ s, ‖finiteHighPart s threshold f k‖) = _
    rw [sum_norm_finiteHighPart, Finset.sum_filter]
  let lowLevel : Set ℤ := {x | threshold / 2 < ‖U low x‖}
  let highLevel : Set ℤ := {x | threshold / 2 < ‖U high x‖}
  let level : Set ℤ := {x | threshold < ‖U input x‖}
  have hlowFiniteLevel : lowLevel.Finite := by
    simpa [lowLevel] using weakStrongInterpolation_level_set_finite
      (U low) (threshold / 2) (by positivity)
  have hhighFiniteLevel : highLevel.Finite := by
    simpa [highLevel] using weakStrongInterpolation_level_set_finite
      (U high) (threshold / 2) (by positivity)
  have hlevels : level ⊆ lowLevel ∪ highLevel := by
    intro x hx
    by_cases hlow : threshold / 2 < ‖U low x‖
    · exact Or.inl hlow
    · by_cases hhigh : threshold / 2 < ‖U high x‖
      · exact Or.inr hhigh
      · have hlowBound : ‖U low x‖ ≤ threshold / 2 := le_of_not_gt hlow
        have hhighBound : ‖U high x‖ ≤ threshold / 2 := le_of_not_gt hhigh
        have hpoint : U input x = U low x + U high x := by
          exact congrArg (fun g : lp (fun _ : ℤ => ℂ) 2 => g x) hUdecomp
        have hbound : ‖U input x‖ ≤ threshold := by
          rw [hpoint]
          calc
            ‖U low x + U high x‖ ≤ ‖U low x‖ + ‖U high x‖ := norm_add_le _ _
            _ ≤ threshold / 2 + threshold / 2 := add_le_add hlowBound hhighBound
            _ = threshold := by ring
        exact False.elim ((not_lt_of_ge hbound) hx)
  have hunionFinite : (lowLevel ∪ highLevel).Finite := hlowFiniteLevel.union hhighFiniteLevel
  have hcountUnion : (Set.ncard level : ℝ) ≤
      (Set.ncard lowLevel : ℝ) + (Set.ncard highLevel : ℝ) := by
    calc
      (Set.ncard level : ℝ) ≤ Set.ncard (lowLevel ∪ highLevel) := by
        exact_mod_cast Set.ncard_le_ncard hlevels hunionFinite
      _ ≤ Set.ncard lowLevel + Set.ncard highLevel := by
        exact_mod_cast Set.ncard_union_le lowLevel highLevel
  have hlowCheb := weakStrongInterpolation_level_ncard_sq_le
    (U low) (threshold / 2) (by positivity)
  have hlowStrongSq : ‖U low‖ ^ 2 ≤ ‖low‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg (U low)) (norm_nonneg low)).2
      (hstrong low hlowL2Finite)
  have hlowCount : (Set.ncard lowLevel : ℝ) ≤
      4 / threshold ^ 2 * (∑ k ∈ s,
        if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) := by
    have hden : 0 < (threshold / 2) ^ 2 := sq_pos_of_pos (by positivity)
    have hbound : (Set.ncard lowLevel : ℝ) ≤ ‖low‖ ^ 2 / (threshold / 2) ^ 2 := by
      apply (le_div_iff₀ hden).2
      calc
        (Set.ncard lowLevel : ℝ) * (threshold / 2) ^ 2 ≤ ‖U low‖ ^ 2 := by
          simpa [lowLevel] using hlowCheb
        _ ≤ ‖low‖ ^ 2 := hlowStrongSq
    rw [hlowMoment] at hbound
    have hcoef : (∑ k ∈ s, if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) /
        (threshold / 2) ^ 2 =
        4 / threshold ^ 2 * (∑ k ∈ s,
          if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) := by
      field_simp [ne_of_gt hthreshold]
      ring
    rw [hcoef] at hbound
    exact hbound
  have hhighWeak := hweak high hhighL2Finite
    (threshold / 2) (by positivity)
  have hhighCount : (Set.ncard highLevel : ℝ) ≤
      2 * W / threshold * (∑ k ∈ s,
        if threshold < ‖f k‖ then ‖f k‖ else 0) := by
    have hfactor : W / (threshold / 2) = 2 * W / threshold := by
      field_simp [ne_of_gt hthreshold]
    simpa [highLevel, hhighMass, hfactor] using hhighWeak
  dsimp [level]
  calc
    (Set.ncard {x : ℤ | threshold < ‖U input x‖} : ℝ) ≤
        (Set.ncard lowLevel : ℝ) + (Set.ncard highLevel : ℝ) := hcountUnion
    _ ≤ 2 * W / threshold * (∑ k ∈ s,
          if threshold < ‖f k‖ then ‖f k‖ else 0) +
        4 / threshold ^ 2 * (∑ k ∈ s,
          if ‖f k‖ ≤ threshold then ‖f k‖ ^ 2 else 0) := by
      simpa [add_comm] using add_le_add hlowCount hhighCount

/-- Convert the checked real strict-level estimate into the finite-output
ENNReal distribution format used by the generic weighted layer-cake theorem.
The split scale is exactly one, so the low cutoff is inclusive at `t` and
the high cutoff is strict above `t`. The operator and both endpoint hypotheses
have the blueprint's finite-support domain. -/
private theorem weakStrongInterpolation_weighted_distribution
    {p : ℝ}
    (U : (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2)
    (hweak : ∀ f : ℤ →₀ ℂ, ∀ r : ℝ, 0 < r →
      (Set.ncard {x : ℤ | r < ‖U f x‖} : ℝ) ≤
        W / r * discreteL1Norm (f : ℤ → ℂ))
    (hstrong : ∀ f : ℤ →₀ ℂ,
      ‖U f‖ ≤ ‖finiteSequenceL2 f‖)
    (f : ℤ →₀ ℂ) (out : Finset ℤ) :
    ∀ t : ℝ, 0 < t →
      ((out.filter fun k => t < ‖U f k‖).card : ℝ≥0∞) *
          ENNReal.ofReal (t ^ (p - 1)) ≤
        4 * ENNReal.ofReal (1 : ℝ) *
            (∑ k ∈ f.support,
              if ‖f k‖ ≤ t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
              ENNReal.ofReal t ^ (p - 3) +
          2 * ENNReal.ofReal W *
            (∑ k ∈ f.support, if t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
              ENNReal.ofReal t ^ (p - 2) := by
  classical
  intro t ht
  let level : Set ℤ := {x | t < ‖U f x‖}
  let outputLevel : Finset ℤ := out.filter fun k => t < ‖U f k‖
  let lowMoment : ℝ := ∑ k ∈ f.support, if ‖f k‖ ≤ t then ‖f k‖ ^ 2 else 0
  let highMoment : ℝ := ∑ k ∈ f.support, if t < ‖f k‖ then ‖f k‖ else 0
  have hlevelFinite : level.Finite := by
    simpa [level] using weakStrongInterpolation_level_set_finite (U f) t ht
  have houtputSubset : outputLevel ⊆ hlevelFinite.toFinset := by
    intro k hk
    have hkLevel : k ∈ level := by
      have hmem := (Finset.mem_filter.mp hk).2
      simpa [level] using hmem
    exact hlevelFinite.mem_toFinset.mpr hkLevel
  have houtputCardNat : outputLevel.card ≤ hlevelFinite.toFinset.card :=
    Finset.card_le_card houtputSubset
  have houtputCardReal : (outputLevel.card : ℝ) ≤ (level.ncard : ℝ) := by
    calc
      (outputLevel.card : ℝ) ≤ (hlevelFinite.toFinset.card : ℝ) := by
        exact_mod_cast houtputCardNat
      _ = (level.ncard : ℝ) := by
        rw [Set.ncard_eq_toFinset_card level hlevelFinite]
  have hrealBound : (outputLevel.card : ℝ) ≤
      2 * W / t * highMoment + 4 / t ^ 2 * lowMoment := by
    calc
      (outputLevel.card : ℝ) ≤ (level.ncard : ℝ) := houtputCardReal
      _ ≤ 2 * W / t * highMoment + 4 / t ^ 2 * lowMoment := by
        simpa [level, highMoment, lowMoment] using
          weakStrongInterpolation_finsupp_low_high_distribution
            U hweak hstrong f ht
  have hdivTwo : t ^ (p - 1) / t ^ 2 = t ^ (p - 3) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_sub ht]
    congr 1
    ring
  have hdivOne : t ^ (p - 1) / t = t ^ (p - 2) := by
    calc
      t ^ (p - 1) / t = t ^ (p - 1) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((p - 1) - 1) := (Real.rpow_sub ht (p - 1) 1).symm
      _ = t ^ (p - 2) := by congr 1; ring
  have hweightedReal :
      (outputLevel.card : ℝ) * t ^ (p - 1) ≤
        4 * lowMoment * t ^ (p - 3) + 2 * W * highMoment * t ^ (p - 2) := by
    have hmul := mul_le_mul_of_nonneg_right hrealBound
      (Real.rpow_nonneg ht.le (p - 1))
    calc
      (outputLevel.card : ℝ) * t ^ (p - 1) ≤
          (2 * W / t * highMoment + 4 / t ^ 2 * lowMoment) * t ^ (p - 1) := hmul
      _ = 4 * lowMoment * t ^ (p - 3) + 2 * W * highMoment * t ^ (p - 2) := by
        rw [add_mul]
        rw [show (2 * W / t * highMoment) * t ^ (p - 1) =
            2 * W * highMoment * (t ^ (p - 1) / t) by ring]
        rw [show (4 / t ^ 2 * lowMoment) * t ^ (p - 1) =
            4 * lowMoment * (t ^ (p - 1) / t ^ 2) by ring]
        rw [hdivOne, hdivTwo]
        ring
  have hlowNonneg : 0 ≤ lowMoment := by
    dsimp [lowMoment]
    apply Finset.sum_nonneg
    intro k hk
    by_cases h : ‖f k‖ ≤ t <;> simp [h]
  have hhighNonneg : 0 ≤ highMoment := by
    dsimp [highMoment]
    apply Finset.sum_nonneg
    intro k hk
    by_cases h : t < ‖f k‖ <;> simp [h]
  have hWpos : 0 < W := by
    rw [W_eq, H₀_eq, A_eq]
    nlinarith [B_pos]
  have hlowENN :
      (∑ k ∈ f.support,
        if ‖f k‖ ≤ t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) =
        ENNReal.ofReal lowMoment := by
    dsimp [lowMoment]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro k hk
      by_cases h : ‖f k‖ ≤ t <;> simp [h]
    · intro k hk
      by_cases h : ‖f k‖ ≤ t <;> simp [h]
  have hhighENN :
      (∑ k ∈ f.support,
        if t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) =
        ENNReal.ofReal highMoment := by
    dsimp [highMoment]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro k hk
      by_cases h : t < ‖f k‖ <;> simp [h]
    · intro k hk
      by_cases h : t < ‖f k‖ <;> simp [h]
  have hleft :
      (outputLevel.card : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 1)) =
        ENNReal.ofReal ((outputLevel.card : ℝ) * t ^ (p - 1)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hlowRhs :
      4 * ENNReal.ofReal (1 : ℝ) *
          (∑ k ∈ f.support,
            if ‖f k‖ ≤ t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
            ENNReal.ofReal t ^ (p - 3) =
        ENNReal.ofReal (4 * lowMoment * t ^ (p - 3)) := by
    calc
      _ = ENNReal.ofReal 4 * ENNReal.ofReal lowMoment *
          ENNReal.ofReal (t ^ (p - 3)) := by
        rw [show (4 : ℝ≥0∞) * ENNReal.ofReal (1 : ℝ) = ENNReal.ofReal 4 by norm_num,
          hlowENN, ENNReal.ofReal_rpow_of_pos ht]
      _ = ENNReal.ofReal (4 * lowMoment) * ENNReal.ofReal (t ^ (p - 3)) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = ENNReal.ofReal (4 * lowMoment * t ^ (p - 3)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * lowMoment)]
  have hhighRhs :
      2 * ENNReal.ofReal W *
          (∑ k ∈ f.support, if t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
            ENNReal.ofReal t ^ (p - 2) =
        ENNReal.ofReal (2 * W * highMoment * t ^ (p - 2)) := by
    calc
      _ = ENNReal.ofReal (2 * W) * ENNReal.ofReal highMoment *
          ENNReal.ofReal (t ^ (p - 2)) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          hhighENN, ENNReal.ofReal_rpow_of_pos ht]
      _ = ENNReal.ofReal (2 * W * highMoment) * ENNReal.ofReal (t ^ (p - 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * W)]
      _ = ENNReal.ofReal (2 * W * highMoment * t ^ (p - 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * W * highMoment)]
  have hlowTermNonneg : 0 ≤ 4 * lowMoment * t ^ (p - 3) := by
    exact mul_nonneg (mul_nonneg (by positivity) hlowNonneg)
      (Real.rpow_nonneg ht.le (p - 3))
  have hhighTermNonneg : 0 ≤ 2 * W * highMoment * t ^ (p - 2) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hWpos.le) hhighNonneg)
      (Real.rpow_nonneg ht.le (p - 2))
  have hsumENN :
      ENNReal.ofReal (4 * lowMoment * t ^ (p - 3)) +
        ENNReal.ofReal (2 * W * highMoment * t ^ (p - 2)) =
      ENNReal.ofReal (4 * lowMoment * t ^ (p - 3) +
        2 * W * highMoment * t ^ (p - 2)) := by
    exact (ENNReal.ofReal_add hlowTermNonneg hhighTermNonneg).symm
  have hboundENN :
      ENNReal.ofReal ((outputLevel.card : ℝ) * t ^ (p - 1)) ≤
        ENNReal.ofReal (4 * lowMoment * t ^ (p - 3) +
          2 * W * highMoment * t ^ (p - 2)) :=
    (ENNReal.ofReal_le_ofReal_iff (add_nonneg hlowTermNonneg hhighTermNonneg)).2
      hweightedReal
  change (outputLevel.card : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 1)) ≤ _
  calc
    (outputLevel.card : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 1)) =
        ENNReal.ofReal ((outputLevel.card : ℝ) * t ^ (p - 1)) := hleft
    _ ≤ ENNReal.ofReal (4 * lowMoment * t ^ (p - 3) +
        2 * W * highMoment * t ^ (p - 2)) := hboundENN
    _ = ENNReal.ofReal (4 * lowMoment * t ^ (p - 3)) +
        ENNReal.ofReal (2 * W * highMoment * t ^ (p - 2)) := hsumENN.symm
    _ = _ := by rw [← hlowRhs, ← hhighRhs]

/-- The finite-output p-moment estimate for the blueprint's finite-support
operator, with the exact coefficient from layer-cake interpolation. -/
theorem weakStrongInterpolation_finite_output_pMoment_le
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (U : (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2)
    (hweak : ∀ f : ℤ →₀ ℂ, ∀ r : ℝ, 0 < r →
      (Set.ncard {x : ℤ | r < ‖U f x‖} : ℝ) ≤
        W / r * discreteL1Norm (f : ℤ → ℂ))
    (hstrong : ∀ f : ℤ →₀ ℂ,
      ‖U f‖ ≤ ‖finiteSequenceL2 f‖)
    (f : ℤ →₀ ℂ) (out : Finset ℤ) :
    (∑ k ∈ out, ‖U f k‖ ^ p) ≤
      (2 * W * p / (p - 1) + 4 * p / (2 - p)) *
        (∑ k ∈ f.support, ‖f k‖ ^ p) := by
  classical
  let g : ℤ → ℂ := fun k => U f k
  let inputMoment : ℝ := ∑ k ∈ f.support, ‖f k‖ ^ p
  let lowMoment : ℝ :=
    ∑ k ∈ f.support, (1 : ℝ) ^ (2 - p) * ‖f k‖ ^ p / (2 - p)
  let highMoment : ℝ :=
    ∑ k ∈ f.support, (1 : ℝ) ^ (1 - p) * ‖f k‖ ^ p / (p - 1)
  let coefficient : ℝ := 2 * W * p / (p - 1) + 4 * p / (2 - p)
  have hENN := finite_weighted_distribution_integral_le
    (p := p) (a := (1 : ℝ)) hp1 hp2 (by norm_num : (0 : ℝ) < 1)
    (ENNReal.ofReal W) (ENNReal.ofReal (1 : ℝ))
    f.support out (f : ℤ → ℂ) g
    (by
      intro t ht
      simpa [g] using
        weakStrongInterpolation_weighted_distribution
          (p := p) U hweak hstrong f out t ht)
  have hLayercake := finiteOutput_pMoment_eq_weighted_layercake
    (lt_trans zero_lt_one hp1) out g
  have hWpos : 0 < W := by
    rw [W_eq, H₀_eq, A_eq]
    nlinarith [B_pos]
  have hpPos : 0 < p := lt_trans zero_lt_one hp1
  have hinputNonneg : 0 ≤ inputMoment := by
    dsimp [inputMoment]
    apply Finset.sum_nonneg
    intro k hk
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hlowENN :
      (∑ k ∈ f.support, ENNReal.ofReal
        ((1 : ℝ) ^ (2 - p) * ‖f k‖ ^ p / (2 - p))) =
        ENNReal.ofReal lowMoment := by
    dsimp [lowMoment]
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro k hk
    positivity
  have hhighENN :
      (∑ k ∈ f.support, ENNReal.ofReal
        ((1 : ℝ) ^ (1 - p) * ‖f k‖ ^ p / (p - 1))) =
        ENNReal.ofReal highMoment := by
    dsimp [highMoment]
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro k hk
    positivity
  have hENNmoment := hENN
  rw [hlowENN, hhighENN] at hENNmoment
  have hleft :
      (∑ k ∈ out, ‖g k‖ₑ ^ p) =
        ENNReal.ofReal (∑ k ∈ out, ‖g k‖ ^ p) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpPos.le]
    · intro k hk
      exact Real.rpow_nonneg (norm_nonneg _) _
  have hlowFactor : lowMoment = (1 / (2 - p)) * inputMoment := by
    dsimp [lowMoment, inputMoment]
    calc
      (∑ k ∈ f.support,
          (1 : ℝ) ^ (2 - p) * ‖f k‖ ^ p / (2 - p)) =
          ∑ k ∈ f.support, (1 / (2 - p)) * ‖f k‖ ^ p := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Real.one_rpow]
        ring
      _ = (1 / (2 - p)) * ∑ k ∈ f.support, ‖f k‖ ^ p := by
        rw [← Finset.mul_sum]
  have hhighFactor : highMoment = (1 / (p - 1)) * inputMoment := by
    dsimp [highMoment, inputMoment]
    calc
      (∑ k ∈ f.support,
          (1 : ℝ) ^ (1 - p) * ‖f k‖ ^ p / (p - 1)) =
          ∑ k ∈ f.support, (1 / (p - 1)) * ‖f k‖ ^ p := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Real.one_rpow]
        ring
      _ = (1 / (p - 1)) * ∑ k ∈ f.support, ‖f k‖ ^ p := by
        rw [← Finset.mul_sum]
  have hlowNonneg : 0 ≤ lowMoment := by
    dsimp [lowMoment]
    apply Finset.sum_nonneg
    intro k hk
    positivity
  have hhighNonneg : 0 ≤ highMoment := by
    dsimp [highMoment]
    apply Finset.sum_nonneg
    intro k hk
    positivity
  have hlowProduct :
      4 * ENNReal.ofReal (1 : ℝ) * ENNReal.ofReal lowMoment =
        ENNReal.ofReal (4 * lowMoment) := by
    rw [show (4 : ℝ≥0∞) * ENNReal.ofReal (1 : ℝ) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hhighProduct :
      2 * ENNReal.ofReal W * ENNReal.ofReal highMoment =
        ENNReal.ofReal (2 * W * highMoment) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * W)]
  have hsumENN :
      ENNReal.ofReal (4 * lowMoment) + ENNReal.ofReal (2 * W * highMoment) =
        ENNReal.ofReal (4 * lowMoment + 2 * W * highMoment) := by
    exact (ENNReal.ofReal_add
      (mul_nonneg (by norm_num) hlowNonneg)
      (mul_nonneg (mul_nonneg (by norm_num) hWpos.le) hhighNonneg)).symm
  have hrealRhs :
      p * (4 * lowMoment + 2 * W * highMoment) = coefficient * inputMoment := by
    rw [hlowFactor, hhighFactor]
    dsimp [coefficient]
    ring
  have hRhsENN :
      ENNReal.ofReal p *
        (4 * ENNReal.ofReal (1 : ℝ) * ENNReal.ofReal lowMoment +
          2 * ENNReal.ofReal W * ENNReal.ofReal highMoment) =
        ENNReal.ofReal (coefficient * inputMoment) := by
    rw [hlowProduct, hhighProduct, hsumENN,
      ← ENNReal.ofReal_mul (le_of_lt hpPos), hrealRhs]
  have hbound :
      ENNReal.ofReal (∑ k ∈ out, ‖g k‖ ^ p) ≤
        ENNReal.ofReal (coefficient * inputMoment) := by
    calc
      ENNReal.ofReal (∑ k ∈ out, ‖g k‖ ^ p) =
          ∑ k ∈ out, ‖g k‖ₑ ^ p := hleft.symm
      _ = ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi (0 : ℝ),
            ((out.filter fun k => t < ‖g k‖).card : ℝ≥0∞) *
              ENNReal.ofReal (t ^ (p - 1)) := hLayercake
      _ ≤ ENNReal.ofReal p *
          (4 * ENNReal.ofReal (1 : ℝ) * ENNReal.ofReal lowMoment +
            2 * ENNReal.ofReal W * ENNReal.ofReal highMoment) := by
        exact mul_le_mul_of_nonneg_left hENNmoment (by positivity)
      _ = ENNReal.ofReal (coefficient * inputMoment) := hRhsENN
  have hcoefNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hnonneg : 0 ≤ coefficient * inputMoment :=
    mul_nonneg hcoefNonneg hinputNonneg
  have hrealBound := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hbound
  simpa [g, inputMoment, coefficient] using hrealBound

/-- Separates the p-th root of the total moment into coefficient and input
roots. This normalization is kept distinct from the exhaustion theorem. -/
private theorem weakStrongInterpolation_rpow_mul
    {p C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) :
    (C * M) ^ (1 / p) = C ^ (1 / p) * M ^ (1 / p) :=
  Real.mul_rpow hC hM

/-- A finite-support input produces a full sequence `lp` representative of
the operator output. Its norm is bounded by the p-th root of the total
coefficient-times-input-moment estimate. -/
theorem weakStrongInterpolation_exists_finite_input_lp
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (U : (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2)
    (hweak : ∀ f : ℤ →₀ ℂ, ∀ r : ℝ, 0 < r →
      (Set.ncard {x : ℤ | r < ‖U f x‖} : ℝ) ≤
        W / r * discreteL1Norm (f : ℤ → ℂ))
    (hstrong : ∀ f : ℤ →₀ ℂ,
      ‖U f‖ ≤ ‖finiteSequenceL2 f‖)
    (f : ℤ →₀ ℂ) :
    ∃ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ((F : ℤ → ℂ) = fun k => U f k) ∧
      ‖F‖ ≤
        ((2 * W * p / (p - 1) + 4 * p / (2 - p)) *
          (∑ k ∈ f.support, ‖f k‖ ^ p)) ^ (1 / p) := by
  classical
  let coefficient : ℝ := 2 * W * p / (p - 1) + 4 * p / (2 - p)
  let inputMoment : ℝ := ∑ k ∈ f.support, ‖f k‖ ^ p
  let totalMoment : ℝ := coefficient * inputMoment
  let output : ℤ → ℂ := fun k => U f k
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hpReal : 0 < p := lt_trans zero_lt_one hp1
  have hp0 : P ≠ 0 := by
    dsimp [P]
    exact ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  have hPto : P.toReal = p := by
    dsimp [P]
    exact ENNReal.toReal_ofReal hpReal.le
  have hWpos : 0 < W := by
    rw [W_eq, H₀_eq, A_eq]
    nlinarith [B_pos]
  have hCoefficientNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hInputMomentNonneg : 0 ≤ inputMoment := by
    dsimp [inputMoment]
    apply Finset.sum_nonneg
    intro k hk
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hTotalMomentNonneg : 0 ≤ totalMoment := by
    dsimp [totalMoment]
    exact mul_nonneg hCoefficientNonneg hInputMomentNonneg
  have hfinite : ∀ out : Finset ℤ,
      ∑ k ∈ out, ‖output k‖ ^ P.toReal ≤ totalMoment := by
    intro out
    rw [hPto]
    simpa [output, coefficient, inputMoment, totalMoment] using
      weakStrongInterpolation_finite_output_pMoment_le
        hp1 hp2 U hweak hstrong f out
  let F : lp (fun _ : ℤ => ℂ) P :=
    lpOfUniformFiniteMomentBound hp0 hpTop output hTotalMomentNonneg hfinite
  have hnorm := lpOfUniformFiniteMomentBound_norm_le
    hp0 hpTop output hTotalMomentNonneg hfinite
  rw [hPto] at hnorm
  refine ⟨F, ?_, ?_⟩
  · funext k
    simpa [F, output] using
      lpOfUniformFiniteMomentBound_apply
        hp0 hpTop output hTotalMomentNonneg hfinite k
  · simpa [F, output, totalMoment, coefficient, inputMoment] using hnorm

/-- The blueprint's full-output interpolation bound for a finitely supported
input. The operator and both endpoint hypotheses retain their finite-support
domain. -/
theorem weakStrongInterpolation
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (U : (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2)
    (hweak : ∀ f : ℤ →₀ ℂ, ∀ r : ℝ, 0 < r →
      (Set.ncard {x : ℤ | r < ‖U f x‖} : ℝ) ≤
        W / r * discreteL1Norm (f : ℤ → ℂ))
    (hstrong : ∀ f : ℤ →₀ ℂ,
      ‖U f‖ ≤ ‖finiteSequenceL2 f‖)
    (f : ℤ →₀ ℂ) :
    ∃ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ((F : ℤ → ℂ) = fun k => U f k) ∧
      ‖F‖ ≤
        (2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p) *
          (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p) := by
  classical
  let coefficient : ℝ := 2 * W * p / (p - 1) + 4 * p / (2 - p)
  let inputMoment : ℝ := ∑ k ∈ f.support, ‖f k‖ ^ p
  have hWpos : 0 < W := by
    rw [W_eq, H₀_eq, A_eq]
    nlinarith [B_pos]
  have hCoefficientNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hInputMomentNonneg : 0 ≤ inputMoment := by
    dsimp [inputMoment]
    apply Finset.sum_nonneg
    intro k hk
    exact Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨F, hF, hFNorm⟩ :=
    weakStrongInterpolation_exists_finite_input_lp hp1 hp2 U hweak hstrong f
  refine ⟨F, hF, ?_⟩
  calc
    ‖F‖ ≤ (coefficient * inputMoment) ^ (1 / p) := by
      simpa [coefficient, inputMoment] using hFNorm
    _ = coefficient ^ (1 / p) * inputMoment ^ (1 / p) :=
      weakStrongInterpolation_rpow_mul hCoefficientNonneg hInputMomentNonneg
    _ = (2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p) *
        (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p) := by
      simp [coefficient, inputMoment]

end

end FractionalPrimes.Literature.Multiplier
