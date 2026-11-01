module

public import FractionalPrimes.Literature.JSW.DyadicFiniteVectorCZ
public import FractionalPrimes.Literature.JSW.VectorDuality
public import FractionalPrimes.Literature.JSW.WeakTypeInterpolation
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Module.Projective

/-!
# The enlarged bad-cell union in the weak-CZ argument

This file isolates the exact factor-nine measure estimate used after the
finite-vector dyadic decomposition.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option maxHeartbeats 1000000

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Restriction to a measurable set is a contractive linear map on
vector-valued `L²`.  This is the operator needed to turn the `L²` sum of bad
outputs into the `L²` sum of their restrictions off the enlarged bad region. -/
noncomputable def dyadicWeakCZ_L2_restrict
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E : Set ℝ) (hE : MeasurableSet E) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] Lp H 2 (volume : Measure ℝ) := by
  let L : Lp H 2 (volume : Measure ℝ) →ₗ[ℝ] Lp H 2 (volume : Measure ℝ) := {
    toFun := fun f => ((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f)
    map_add' := by
      intro f g
      apply Lp.ext
      have hleft := ((Lp.memLp (f + g)).indicator hE.nullMeasurableSet).coeFn_toLp
      have hright :
          (((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f) +
            ((Lp.memLp g).indicator hE.nullMeasurableSet).toLp (E.indicator g)) =ᵐ[(volume : Measure ℝ)]
            (E.indicator f + E.indicator g) := by
        filter_upwards [Lp.coeFn_add
            (((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f))
            (((Lp.memLp g).indicator hE.nullMeasurableSet).toLp (E.indicator g)),
          ((Lp.memLp f).indicator hE.nullMeasurableSet).coeFn_toLp,
          ((Lp.memLp g).indicator hE.nullMeasurableSet).coeFn_toLp] with x hadd hf hg
        calc
          ((((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f) +
            ((Lp.memLp g).indicator hE.nullMeasurableSet).toLp (E.indicator g)) : Lp H 2 volume) x =
              ((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f) x +
                ((Lp.memLp g).indicator hE.nullMeasurableSet).toLp (E.indicator g) x := hadd
          _ = E.indicator f x + E.indicator g x := by rw [hf, hg]
          _ = (E.indicator f + E.indicator g) x := rfl
      filter_upwards [hleft, hright, Lp.coeFn_add f g] with x hleft hright hfg
      calc
        (((Lp.memLp (f + g)).indicator hE.nullMeasurableSet).toLp (E.indicator (f + g))) x =
            E.indicator (f + g) x := hleft
        _ = E.indicator (fun y => f y + g y) x := by
          by_cases hx : x ∈ E
          · simpa only [Set.indicator_of_mem hx, Pi.add_apply] using hfg
          · simp [Set.indicator, hx]
        _ = (E.indicator f + E.indicator g) x :=
          congrFun (Set.indicator_add E f g) x
        _ = (((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f) +
            ((Lp.memLp g).indicator hE.nullMeasurableSet).toLp (E.indicator g)) x := hright.symm
    map_smul' := by
      intro c f
      apply Lp.ext
      have hleft := ((Lp.memLp (c • f)).indicator hE.nullMeasurableSet).coeFn_toLp
      have hright :
          c • ((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f) =ᵐ[(volume : Measure ℝ)]
            c • E.indicator f := by
        filter_upwards [Lp.coeFn_smul c
            (((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f)),
          ((Lp.memLp f).indicator hE.nullMeasurableSet).coeFn_toLp] with x hsmul hf
        calc
          (c • ((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f)) x =
              c • ((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f) x := hsmul
          _ = c • E.indicator f x := by rw [hf]
          _ = (c • E.indicator f) x := rfl
      filter_upwards [hleft, hright, Lp.coeFn_smul c f] with x hleft hright hcf
      calc
        (((Lp.memLp (c • f)).indicator hE.nullMeasurableSet).toLp (E.indicator (c • f))) x =
            E.indicator (c • f) x := hleft
        _ = c • E.indicator f x := by
          by_cases hx : x ∈ E <;> simp [Set.indicator, hx, hcf]
        _ = (c • E.indicator f) x := rfl
        _ = (c • ((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f)) x :=
          hright.symm
  }

  exact L.mkContinuous 1 (by
    intro f
    change ‖((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f)‖ ≤ 1 * ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    simpa only [one_mul] using ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
      (eLpNorm_indicator_le f hE.nullMeasurableSet))

/-- Restricting each term of a summable `L²` family to the same measurable
set preserves summability. -/
theorem dyadicWeakCZ_restrict_L2_summable
    {ι H : Type*} [Countable ι] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E : Set ℝ) (hE : MeasurableSet E)
    (u : ι → Lp H 2 (volume : Measure ℝ)) (hu : Summable u) :
    Summable (fun i => dyadicWeakCZ_L2_restrict E hE (u i)) := by
  exact (dyadicWeakCZ_L2_restrict E hE).summable hu

/-- Two limits in measure of the same sequence agree almost everywhere.
This is the uniqueness step needed to identify the L² limit of bad outputs
with the L¹ pointwise sum obtained off the enlarged bad region. -/
theorem ae_eq_of_tendstoInMeasure
    {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [T2Space E]
    {μ : Measure α} {f : ℕ → α → E} {u v : α → E}
    (hu : TendstoInMeasure μ f Filter.atTop u)
    (hv : TendstoInMeasure μ f Filter.atTop v) : u =ᵐ[μ] v := by
  obtain ⟨ns, hns, huAE⟩ := hu.exists_seq_tendsto_ae
  have hv' : TendstoInMeasure μ (fun n => f (ns n)) atTop v :=
    hv.comp hns.tendsto_atTop
  obtain ⟨ms, hms, hvAE⟩ := hv'.exists_seq_tendsto_ae
  have huAE' : ∀ᵐ x ∂μ,
      Tendsto (fun n => f (ns (ms n)) x) Filter.atTop (𝓝 (u x)) := by
    filter_upwards [huAE] with x hx
    exact hx.comp hms.tendsto_atTop
  filter_upwards [huAE', hvAE] with x hux hvx
  exact tendsto_nhds_unique hux hvx

/-- If the same sequence of functions converges in both `L¹` and `L²`, its
two limits agree almost everywhere. This identifies the L² operator limit
with the L¹ sum obtained from the off-support estimates. -/
theorem ae_eq_of_l1_l2_limits_of_same_functions
    {α H : Type*} [MeasurableSpace α] [NormedAddCommGroup H]
    {μ : Measure α} {s : ℕ → α → H}
    (hs₁ : ∀ n, MemLp (s n) 1 μ) (hs₂ : ∀ n, MemLp (s n) 2 μ)
    {u₁ : Lp H 1 μ} {u₂ : Lp H 2 μ}
    (h₁ : Tendsto (fun n => (hs₁ n).toLp (s n)) Filter.atTop (𝓝 u₁))
    (h₂ : Tendsto (fun n => (hs₂ n).toLp (s n)) Filter.atTop (𝓝 u₂)) :
    (u₁ : α → H) =ᵐ[μ] (u₂ : α → H) := by
  apply ae_eq_of_tendstoInMeasure
    (tendstoInMeasure_of_tendsto_Lp h₁)
  apply TendstoInMeasure.congr_left (f := fun n => (hs₂ n).toLp (s n))
    (f' := fun n => (hs₁ n).toLp (s n)) ?_
    (tendstoInMeasure_of_tendsto_Lp h₂)
  intro n
  filter_upwards [(hs₁ n).coeFn_toLp, (hs₂ n).coeFn_toLp] with x h₁x h₂x
  exact h₂x.trans h₁x.symm

/-- If one family of functions has summable `L¹` and `L²` representatives,
then its sums over any cofinal sequence of finite index sets have the same
almost-everywhere limit in the two spaces.  The finite sums here are literally
the same pointwise functions in both `L¹` and `L²`; this is the bridge between
the `L²` bad-output sum and its `L¹` off-support series. -/
theorem ae_eq_of_l1_l2_summable_same_partial_sums
    {α H ι : Type*} [MeasurableSpace α] [NormedAddCommGroup H]
    [Countable ι] {μ : Measure α} (s : ι → α → H)
    (hs₁ : ∀ i, MemLp (s i) 1 μ) (hs₂ : ∀ i, MemLp (s i) 2 μ)
    (F : ℕ → Finset ι) (hF : Tendsto F atTop atTop)
    (hSum₁ : Summable (fun i => (hs₁ i).toLp (s i)))
    (hSum₂ : Summable (fun i => (hs₂ i).toLp (s i))) :
    ∀ᵐ x ∂μ,
      (((∑' i, (hs₁ i).toLp (s i)) : Lp H 1 μ) : α → H) x =
        (((∑' i, (hs₂ i).toLp (s i)) : Lp H 2 μ) : α → H) x := by
  let partialSum : ℕ → α → H := fun n x => ∑ i ∈ F n, s i x
  have hpartial₁ (n : ℕ) : MemLp (partialSum n) 1 μ := by
    dsimp [partialSum]
    exact memLp_finsetSum (F n) (fun i _ => hs₁ i)
  have hpartial₂ (n : ℕ) : MemLp (partialSum n) 2 μ := by
    dsimp [partialSum]
    exact memLp_finsetSum (F n) (fun i _ => hs₂ i)
  have hEmbed₁ (n : ℕ) :
      (hpartial₁ n).toLp (partialSum n) =
        ∑ i ∈ F n, (hs₁ i).toLp (s i) := by
    apply Lp.ext
    have hterms : ∀ᵐ x ∂μ, ∀ i,
        (hs₁ i).toLp (s i) x = s i x := by
      rw [ae_all_iff]
      intro i
      exact (hs₁ i).coeFn_toLp
    have hsum :
        (∑ i ∈ F n, (hs₁ i).toLp (s i)) =ᵐ[μ]
          (fun x => ∑ i ∈ F n, s i x) := by
      have hLpSum := Lp.coeFn_fun_finsetSum (F n)
        (fun i => (hs₁ i).toLp (s i))
      filter_upwards [hLpSum, hterms] with x hLpSum hx
      calc
        (∑ i ∈ F n, (hs₁ i).toLp (s i)) x =
            ∑ i ∈ F n, (hs₁ i).toLp (s i) x := hLpSum
        _ = ∑ i ∈ F n, s i x :=
          Finset.sum_congr rfl (fun i hi => hx i)
    filter_upwards [(hpartial₁ n).coeFn_toLp, hsum] with x hpartial hsum
    exact hpartial.trans hsum.symm
  have hEmbed₂ (n : ℕ) :
      (hpartial₂ n).toLp (partialSum n) =
        ∑ i ∈ F n, (hs₂ i).toLp (s i) := by
    apply Lp.ext
    have hterms : ∀ᵐ x ∂μ, ∀ i,
        (hs₂ i).toLp (s i) x = s i x := by
      rw [ae_all_iff]
      intro i
      exact (hs₂ i).coeFn_toLp
    have hsum :
        (∑ i ∈ F n, (hs₂ i).toLp (s i)) =ᵐ[μ]
          (fun x => ∑ i ∈ F n, s i x) := by
      have hLpSum := Lp.coeFn_fun_finsetSum (F n)
        (fun i => (hs₂ i).toLp (s i))
      filter_upwards [hLpSum, hterms] with x hLpSum hx
      calc
        (∑ i ∈ F n, (hs₂ i).toLp (s i)) x =
            ∑ i ∈ F n, (hs₂ i).toLp (s i) x := hLpSum
        _ = ∑ i ∈ F n, s i x :=
          Finset.sum_congr rfl (fun i hi => hx i)
    filter_upwards [(hpartial₂ n).coeFn_toLp, hsum] with x hpartial hsum
    exact hpartial.trans hsum.symm
  have hconv₁ : Tendsto (fun n => (hpartial₁ n).toLp (partialSum n))
      atTop (𝓝 (∑' i, (hs₁ i).toLp (s i))) := by
    convert hSum₁.hasSum.comp hF using 1
    funext n
    exact hEmbed₁ n
  have hconv₂ : Tendsto (fun n => (hpartial₂ n).toLp (partialSum n))
      atTop (𝓝 (∑' i, (hs₂ i).toLp (s i))) := by
    convert hSum₂.hasSum.comp hF using 1
    funext n
    exact hEmbed₂ n
  have hAE := ae_eq_of_l1_l2_limits_of_same_functions hpartial₁ hpartial₂
    hconv₁ hconv₂
  exact hAE

/-- Every countable index type admits a cofinal sequence of finite subsets.
This supplies the finite partial sums used to compare the `L¹` and `L²`
limits of the same bad-output series. -/
theorem exists_cofinal_finset_sequence
    {ι : Type*} [Countable ι] :
    ∃ F : ℕ → Finset ι, Tendsto F atTop atTop := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  refine ⟨fun n => (Finset.range n).preimage e he.injOn, ?_⟩
  exact (tendsto_finset_preimage_atTop_atTop he).comp tendsto_finset_range

/-- If the `L¹` norms of a countable family are summable, its `L¹` sum is
almost everywhere the pointwise sum of the same representatives.  This uses
Mathlib's `Lp.hasSum_coeFn_tsum` to pass from the `L¹` sum to the pointwise
series. -/
theorem ae_eq_l1_tsum_pointwise_tsum
    {α H ι : Type*} [MeasurableSpace α] [NormedAddCommGroup H]
    [CompleteSpace H] [Countable ι] {μ : Measure α} (s : ι → α → H)
    (hs : ∀ i, MemLp (s i) 1 μ)
    (hNorm : (∑' i, ‖(hs i).toLp (s i)‖ₑ) ≠ ⊤) :
    ∀ᵐ x ∂μ,
      (((∑' i, (hs i).toLp (s i)) : Lp H 1 μ) : α → H) x =
        ∑' i, s i x := by
  have hPointwise := Lp.hasSum_coeFn_tsum hNorm
  have hterms : ∀ᵐ x ∂μ, ∀ i, (hs i).toLp (s i) x = s i x := by
    rw [ae_all_iff]
    intro i
    exact (hs i).coeFn_toLp
  filter_upwards [hPointwise, hterms] with x hx hx'
  calc
    (((∑' i, (hs i).toLp (s i)) : Lp H 1 μ) : α → H) x =
        ∑' i, (hs i).toLp (s i) x := hx.tsum_eq.symm
    _ = ∑' i, s i x := tsum_congr (fun i => hx' i)

/-- If a countable family has summable `L¹` representatives, its pointwise
terms are summable almost everywhere. -/
theorem ae_summable_of_l1_lp_series
    {α H ι : Type*} [MeasurableSpace α] [NormedAddCommGroup H]
    [CompleteSpace H] [Countable ι] {μ : Measure α} (s : ι → α → H)
    (hs : ∀ i, MemLp (s i) 1 μ)
    (hNorm : (∑' i, ‖(hs i).toLp (s i)‖ₑ) ≠ ⊤) :
    ∀ᵐ x ∂μ, Summable (fun i => s i x) := by
  have hPointwise := Lp.hasSum_coeFn_tsum hNorm
  have hterms : ∀ᵐ x ∂μ, ∀ i, (hs i).toLp (s i) x = s i x := by
    rw [ae_all_iff]
    intro i
    exact (hs i).coeFn_toLp
  filter_upwards [hPointwise, hterms] with x hx hx'
  exact hx.summable.congr (fun i => hx' i)

/-- A summable family of integrable nonnegative functions has pointwise
summable values almost everywhere. -/
theorem ae_summable_of_integrable_series
    {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    (s : ι → α → ℝ)
    (hsInt : ∀ i, Integrable (s i) μ)
    (hsMass : Summable (fun i => ∫ x, s i x ∂μ))
    (hsNonneg : ∀ i x, 0 ≤ s i x) :
    ∀ᵐ x ∂μ, Summable (fun i => s i x) := by
  have hsMem (i : ι) : MemLp (s i) 1 μ :=
    memLp_one_iff_integrable.mpr (hsInt i)
  have hsNorm : Summable (fun i => ‖(hsMem i).toLp (s i)‖) := by
    apply Summable.congr hsMass
    intro i
    calc
      ∫ x, s i x ∂μ = ∫ x, ‖s i x‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hsNonneg i x)]
      _ = ‖(hsMem i).toLp (s i)‖ :=
        (L1.norm_of_fun_eq_integral_norm
          (memLp_one_iff_integrable.mp (hsMem i))).symm
  have hsNormNeTop :
      (∑' i, ‖(hsMem i).toLp (s i)‖ₑ) ≠ ⊤ := by
    have hne := hsNorm.tsum_ofReal_ne_top
    simpa only [← ofReal_norm] using hne
  have hPointwise := Lp.hasSum_coeFn_tsum hsNormNeTop
  have hterms : ∀ᵐ x ∂μ, ∀ i, (hsMem i).toLp (s i) x = s i x := by
    rw [ae_all_iff]
    intro i
    exact (hsMem i).coeFn_toLp
  filter_upwards [hPointwise, hterms] with x hx hx'
  exact hx.summable.congr (fun i => hx' i)

/-- Combine the two common-partial-sum limits with pointwise convergence of
the `L¹` series.  In particular, this identifies an `L²` bad-output limit
with the pointwise off-support sum whenever the common terms are the
off-support bad outputs. -/
theorem ae_eq_l2_tsum_pointwise_tsum_of_l1_l2_partial_sums
    {α H ι : Type*} [MeasurableSpace α] [NormedAddCommGroup H]
    [CompleteSpace H] [Countable ι] {μ : Measure α} (s : ι → α → H)
    (hs₁ : ∀ i, MemLp (s i) 1 μ) (hs₂ : ∀ i, MemLp (s i) 2 μ)
    (F : ℕ → Finset ι) (hF : Tendsto F atTop atTop)
    (hSum₁ : Summable (fun i => (hs₁ i).toLp (s i)))
    (hSum₂ : Summable (fun i => (hs₂ i).toLp (s i)))
    (hNorm₁ : (∑' i, ‖(hs₁ i).toLp (s i)‖ₑ) ≠ ⊤) :
    ∀ᵐ x ∂μ,
      (((∑' i, (hs₂ i).toLp (s i)) : Lp H 2 μ) : α → H) x =
        ∑' i, s i x := by
  have hsame := ae_eq_of_l1_l2_summable_same_partial_sums
    s hs₁ hs₂ F hF hSum₁ hSum₂
  have hpoint := ae_eq_l1_tsum_pointwise_tsum s hs₁ hNorm₁
  filter_upwards [hsame, hpoint] with x hsame hpoint
  exact hsame.symm.trans hpoint

/-- The interval with the same center as a dyadic cell and nine times its
length.  Since a cell of index `j` has endpoints `jℓ` and `(j+1)ℓ`, the
corresponding endpoints are `(j-4)ℓ` and `(j+5)ℓ`. -/
def dyadicNinefoldInterval (m j : ℤ) : Set ℝ :=
  Set.Ico (((j - 4 : ℤ) : ℝ) * (2 : ℝ) ^ m)
    (((j + 5 : ℤ) : ℝ) * (2 : ℝ) ^ m)

/-- Cut a function off on a measurable or nonmeasurable exceptional set by
setting it to zero there. -/
noncomputable def dyadicWeakCZ_offSupportOutput {H : Type*} [Zero H]
    (E : Set ℝ) (v : ℝ → H) : ℝ → H := by
  classical
  exact Eᶜ.indicator v

/-- Off the exceptional set, the norm of the pointwise bad-output sum is
bounded almost everywhere by the sum of the norms.  The L¹ summability
hypothesis supplies pointwise summability almost everywhere. -/
theorem dyadicWeakCZ_badOutput_tsum_norm_le_ae
    {H ι : Type*} [MeasurableSpace H] [NormedAddCommGroup H]
    [NormedSpace ℝ H] [CompleteSpace H] [Countable ι]
    {μ : Measure ℝ} (E : Set ℝ)
    (v : ι → ℝ → H)
    (hL1 : ∀ i, MemLp (dyadicWeakCZ_offSupportOutput E (v i)) 1 μ)
    (hMass : Summable (fun i => ∫ x,
      ‖dyadicWeakCZ_offSupportOutput E (v i) x‖ ∂μ)) :
    ∀ᵐ x ∂μ, x ∉ E → ‖∑' i, v i x‖ ≤ ∑' i, ‖v i x‖ := by
  let s : ι → ℝ → H := fun i x =>
    dyadicWeakCZ_offSupportOutput E (v i) x
  have hsInt (i : ι) : Integrable (fun x => ‖s i x‖) μ := by
    have hInt : Integrable (s i) μ := memLp_one_iff_integrable.mp (hL1 i)
    exact hInt.norm
  have hsummable := ae_summable_of_integrable_series
    (fun i x => ‖s i x‖) hsInt
    (by simpa [s] using hMass) (fun _ _ => norm_nonneg _)
  filter_upwards [hsummable] with x hx
  intro hxE
  have hnorm : Summable (fun i => ‖v i x‖) := by
    simpa [s, dyadicWeakCZ_offSupportOutput, hxE] using hx
  exact norm_tsum_le_tsum_norm hnorm


/-- The fixed exceptional set used by the off-support estimate: the union of
the ninefold enlargements of all selected maximal bad cells. -/
noncomputable def dyadicWeakCZ_badRegion {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) : Set ℝ :=
  ⋃ q : dyadicVectorMaximalBadCells f t,
    dyadicNinefoldInterval q.1.1 q.1.2

/-- The union of the selected ninefold bad intervals is measurable. -/
theorem measurableSet_dyadicWeakCZ_badRegion
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) :
    MeasurableSet (dyadicWeakCZ_badRegion f t) := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  change MeasurableSet (⋃ q : S, dyadicNinefoldInterval q.1.1 q.1.2)
  exact MeasurableSet.iUnion (fun q => by
    rw [dyadicNinefoldInterval]
    exact measurableSet_Ico)

/-- The bounded `L²` operator sends the summable dyadic bad pieces to a
summable family of outputs; restriction to the complement of the fixed
ninefold bad region preserves this `L²` summability. -/
theorem dyadicWeakCZ_badOutput_L2_summable
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    {f : ℝ → H₁} (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {t : ℝ}
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ] Lp H₂ 2 (volume : Measure ℝ)) :
    Summable (fun q : dyadicVectorMaximalBadCells f t =>
      dyadicWeakCZ_L2_restrict (dyadicWeakCZ_badRegion f t)ᶜ
        (measurableSet_dyadicWeakCZ_badRegion f t).compl
        (T ((memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
          (dyadicVectorBadPiece f q.1.1 q.1.2)))) := by
  let b : dyadicVectorMaximalBadCells f t → Lp H₁ 2 (volume : Measure ℝ) :=
    fun q => (memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
      (dyadicVectorBadPiece f q.1.1 q.1.2)
  have hb : Summable b := by
    simpa [b] using dyadicVectorBadPieces_l2_summable hf hf₂ (t := t)
  have hTb : Summable (fun q => T (b q)) := T.summable hb
  exact dyadicWeakCZ_restrict_L2_summable
    (dyadicWeakCZ_badRegion f t)ᶜ
    (measurableSet_dyadicWeakCZ_badRegion f t).compl
    (fun q => T (b q)) hTb

/-- The per-cell off-support estimate makes the restrictions of the bad
outputs summable in `L¹`. The complement of the union of ninefold cells is
contained in each individual cell complement. -/
theorem dyadicWeakCZ_badOutput_L1_summable
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    {f : ℝ → H₁} (hf : Integrable f volume)
    {t B : ℝ}
    (v : dyadicVectorMaximalBadCells f t → ℝ → H₂)
    (hv₂ : ∀ q, MemLp (v q) 2 volume)
    (hOffInt : ∀ q : dyadicVectorMaximalBadCells f t,
      IntegrableOn (fun x => ‖v q x‖)
        (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ volume)
    (hOff : ∀ q : dyadicVectorMaximalBadCells f t,
      ∫ x in (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ, ‖v q x‖ ∂volume ≤
        B * ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume) :
    ∃ hL1 : ∀ q : dyadicVectorMaximalBadCells f t,
      MemLp (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
        (v q)) 1 volume,
      Summable (fun q => (hL1 q).toLp
        (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
          (v q))) ∧
      Summable (fun q => ∫ x, ‖dyadicWeakCZ_offSupportOutput
        (dyadicWeakCZ_badRegion f t)
        (v q) x‖ ∂volume) := by
  classical
  let E := dyadicWeakCZ_badRegion f t
  have hE : MeasurableSet E := measurableSet_dyadicWeakCZ_badRegion f t
  let restricted : dyadicVectorMaximalBadCells f t → ℝ → H₂ :=
    fun q => dyadicWeakCZ_offSupportOutput E (v q)
  let hL1 : ∀ q, MemLp (restricted q) 1 volume := by
    intro q
    have hsubset : Eᶜ ⊆ (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ := by
      intro x hxE hxQ
      exact hxE (Set.mem_iUnion.mpr ⟨q, hxQ⟩)
    have hNormInt : Integrable
        (Eᶜ.indicator (fun x => ‖v q x‖)) volume := by
      apply (integrable_indicator_iff hE.compl).2
      exact (hOffInt q).mono_set hsubset
    have hNormEq : (fun x => ‖restricted q x‖) =ᵐ[volume]
        Eᶜ.indicator (fun x => ‖v q x‖) := by
      filter_upwards with x
      by_cases hx : x ∈ Eᶜ <;> simp [restricted, dyadicWeakCZ_offSupportOutput, hx]
    have hRestrictedNormInt : Integrable (fun x => ‖restricted q x‖) volume :=
      (integrable_congr hNormEq).2 hNormInt
    have hRestrictedInt : Integrable (restricted q) volume :=
      (integrable_norm_iff
        (by
          simpa [restricted, dyadicWeakCZ_offSupportOutput] using
            (hv₂ q).aestronglyMeasurable.indicator hE.compl)).mp
        hRestrictedNormInt
    exact memLp_one_iff_integrable.mpr hRestrictedInt
  have hcell (q : dyadicVectorMaximalBadCells f t) :
      ∫ x, ‖restricted q x‖ ∂volume ≤
        B * ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume := by
    have hsubset : Eᶜ ⊆ (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ := by
      intro x hxE hxQ
      exact hxE (Set.mem_iUnion.mpr ⟨q, hxQ⟩)
    have hnormEq : (fun x => ‖restricted q x‖) =ᵐ[volume]
        Eᶜ.indicator (fun x => ‖v q x‖) := by
      filter_upwards with x
      by_cases hx : x ∈ Eᶜ <;> simp [restricted, dyadicWeakCZ_offSupportOutput, hx]
    calc
      ∫ x, ‖restricted q x‖ ∂volume =
          ∫ x, Eᶜ.indicator (fun x => ‖v q x‖) x ∂volume := by
        apply integral_congr_ae
        exact hnormEq
      _ = ∫ x in Eᶜ, ‖v q x‖ ∂volume := integral_indicator hE.compl
      _ ≤ ∫ x in (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ,
          ‖v q x‖ ∂volume :=
        setIntegral_mono_set (hOffInt q)
          (ae_of_all _ (fun x => norm_nonneg (v q x))) hsubset.eventuallySubset
      _ ≤ B * ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume := by
        exact hOff q
  have hbad : Summable (fun q : dyadicVectorMaximalBadCells f t =>
      ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume) :=
    dyadicVectorBadPieces_l1_summable hf (t := t)
  have hmajor := hbad.mul_left B
  have hRestrictedMass : Summable (fun q => ∫ x, ‖restricted q x‖ ∂volume) :=
    Summable.of_nonneg_of_le
      (fun q => integral_nonneg (fun x => norm_nonneg (restricted q x)))
      hcell hmajor
  have hLpNorm : Summable (fun q : dyadicVectorMaximalBadCells f t =>
      ‖(hL1 q).toLp (restricted q)‖) := by
    apply Summable.congr hRestrictedMass
    intro q
    exact (L1.norm_of_fun_eq_integral_norm
      (memLp_one_iff_integrable.mp (hL1 q))).symm
  have hSum : Summable (fun q : dyadicVectorMaximalBadCells f t =>
      (hL1 q).toLp (restricted q)) := hLpNorm.of_norm
  refine ⟨?_, ⟨hSum, ?_⟩⟩
  · intro q
    simpa [restricted, E] using hL1 q
  · simpa [restricted, E] using hRestrictedMass

/-- Specialize the common finite-partial-sum argument to outputs of the
selected dyadic bad pieces, restricted to the complement of the fixed
ninefold bad region.  The conclusion identifies the `L²` sum of the
restricted outputs with the pointwise off-support series. -/
theorem dyadicWeakCZ_badOutput_L2_tsum_eq_offSupport_pointwise_tsum
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    {f : ℝ → H₁} {t : ℝ}
    (v : dyadicVectorMaximalBadCells f t → ℝ → H₂)
    (F : ℕ → Finset (dyadicVectorMaximalBadCells f t))
    (hF : Tendsto F atTop atTop)
    (hL1 : ∀ q, MemLp
      (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q)) 1 volume)
    (hL2 : ∀ q, MemLp
      (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q)) 2 volume)
    (hSumL1 : Summable (fun q => (hL1 q).toLp
      (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q))))
    (hSumL2 : Summable (fun q => (hL2 q).toLp
      (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q))))
    (hNormL1 : (∑' q, ‖(hL1 q).toLp
      (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q))‖ₑ) ≠ ⊤) :
    ∀ᵐ x ∂volume,
      (((∑' q, (hL2 q).toLp
        (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q))) :
          Lp H₂ 2 volume) : ℝ → H₂) x =
        dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
          (fun y => ∑' q, v q y) x := by
  classical
  let s : dyadicVectorMaximalBadCells f t → ℝ → H₂ := fun q x =>
    dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q) x
  have h := ae_eq_l2_tsum_pointwise_tsum_of_l1_l2_partial_sums
    s hL1 hL2 F hF hSumL1 hSumL2 hNormL1
  filter_upwards [h] with x hx
  by_cases hxE : x ∈ dyadicWeakCZ_badRegion f t
  · calc
      (((∑' q, (hL2 q).toLp
          (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q))) :
            Lp H₂ 2 volume) : ℝ → H₂) x =
          ∑' q, dyadicWeakCZ_offSupportOutput
            (dyadicWeakCZ_badRegion f t) (v q) x := by
        simpa [s] using hx
      _ = 0 := by simp [dyadicWeakCZ_offSupportOutput, hxE]
      _ = dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
            (fun y => ∑' q, v q y) x := by
        simp [dyadicWeakCZ_offSupportOutput, hxE]
  · have htsum :
        (∑' q, dyadicWeakCZ_offSupportOutput
          (dyadicWeakCZ_badRegion f t) (v q) x) =
          ∑' q, v q x := by
      apply tsum_congr
      intro q
      simp [dyadicWeakCZ_offSupportOutput, hxE]
    calc
      (((∑' q, (hL2 q).toLp
          (dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q))) :
            Lp H₂ 2 volume) : ℝ → H₂) x =
          ∑' q, dyadicWeakCZ_offSupportOutput
            (dyadicWeakCZ_badRegion f t) (v q) x := by
        simpa [s] using hx
      _ = ∑' q, v q x := htsum
      _ = dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
            (fun y => ∑' q, v q y) x := by
        simp [dyadicWeakCZ_offSupportOutput, hxE]

private theorem volume_dyadicNinefoldInterval (m j : ℤ) :
    volume (dyadicNinefoldInterval m j) =
      ENNReal.ofReal (9 * (2 : ℝ) ^ m) := by
  rw [dyadicNinefoldInterval, Real.volume_Ico]
  congr 1
  push_cast
  ring

/-- The union of the ninefold enlargements of the selected maximal bad cells
has measure at most nine times the sharp dyadic bad-region bound. -/
theorem dyadicVectorMaximalBadCells_ninefold_measure_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    volume (⋃ q : dyadicVectorMaximalBadCells f t,
      dyadicNinefoldInterval q.1.1 q.1.2) ≤
        ENNReal.ofReal (9 * ((∫ x, ‖f x‖ ∂volume) / t)) := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  have hlength := dyadicVectorMaximalBadCells_sum_length_le hf ht
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ∂volume :=
    integral_nonneg (fun x => norm_nonneg _)
  have hquot : 0 ≤ (∫ x, ‖f x‖ ∂volume) / t := div_nonneg hnonneg ht.le
  have hNine : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by norm_num
  calc
    volume (⋃ q : S, dyadicNinefoldInterval q.1.1 q.1.2) ≤
        ∑' q : S, volume (dyadicNinefoldInterval q.1.1 q.1.2) :=
      MeasureTheory.measure_iUnion_le (fun q : S =>
        dyadicNinefoldInterval q.1.1 q.1.2)
    _ = ∑' q : S, ENNReal.ofReal (9 * (2 : ℝ) ^ q.1.1) := by
      apply tsum_congr
      intro q
      exact volume_dyadicNinefoldInterval q.1.1 q.1.2
    _ = ∑' q : S, 9 * ENNReal.ofReal ((2 : ℝ) ^ q.1.1) := by
      apply tsum_congr
      intro q
      rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (9 : ℝ)), ENNReal.ofReal_ofNat]
    _ = 9 * ∑' q : S, ENNReal.ofReal ((2 : ℝ) ^ q.1.1) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ 9 * ENNReal.ofReal ((∫ x, ‖f x‖ ∂volume) / t) := by
      exact mul_le_mul_of_nonneg_left hlength (by positivity)
    _ = ENNReal.ofReal (9 * ((∫ x, ‖f x‖ ∂volume) / t)) := by
      rw [hNine, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (9 : ℝ))]

/-- Sum the per-cell off-support L¹ bounds over the selected bad pieces.
Since the complement of the union of all ninefold cells lies outside each
individual ninefold cell, the total off-support mass is at most
`2 B ‖f‖₁`. -/
theorem dyadicWeakCZ_badOutput_integrals_tsum_le
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    {f : ℝ → H₁} (hf : Integrable f volume) {t B : ℝ} (hB : 0 ≤ B)
    (v : dyadicVectorMaximalBadCells f t → ℝ → H₂)
    (hOffInt : ∀ q : dyadicVectorMaximalBadCells f t,
      IntegrableOn (fun x => ‖v q x‖)
        (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ volume)
    (hOff : ∀ q : dyadicVectorMaximalBadCells f t,
      ∫ x in (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ, ‖v q x‖ ∂volume ≤
        B * ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume) :
    (∑' q : dyadicVectorMaximalBadCells f t,
      ∫ x in (⋃ q : dyadicVectorMaximalBadCells f t,
        dyadicNinefoldInterval q.1.1 q.1.2)ᶜ, ‖v q x‖ ∂volume) ≤
      2 * B * ∫ x, ‖f x‖ ∂volume := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  let E : Set ℝ := ⋃ q : S, dyadicNinefoldInterval q.1.1 q.1.2
  have hbadSummable := dyadicVectorBadPieces_l1_summable hf (t := t)
  have hbadBound := dyadicVectorBadPieces_l1_tsum_le_two hf (t := t)
  have hcell (q : S) :
      ∫ x in Eᶜ, ‖v q x‖ ∂volume ≤
        B * ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume := by
    have hQsub : dyadicNinefoldInterval q.1.1 q.1.2 ⊆ E := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨q, hx⟩
    have hcompl : Eᶜ ⊆ (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ := by
      intro x hxE hxQ
      exact hxE (Set.mem_iUnion.mpr ⟨q, hxQ⟩)
    calc
      ∫ x in Eᶜ, ‖v q x‖ ∂volume ≤
          ∫ x in (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ, ‖v q x‖ ∂volume :=
        setIntegral_mono_set (hOffInt q)
          (ae_of_all _ (fun x => norm_nonneg (v q x))) hcompl.eventuallySubset
      _ ≤ B * ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume := hOff q
  have hleftSummable : Summable (fun q : S =>
      ∫ x in Eᶜ, ‖v q x‖ ∂volume) :=
    Summable.of_nonneg_of_le
      (fun q => integral_nonneg (fun x => norm_nonneg (v q x)))
      hcell (hbadSummable.mul_left B)
  calc
    (∑' q : S, ∫ x in Eᶜ, ‖v q x‖ ∂volume) ≤
        ∑' q : S, B *
          ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume :=
      hleftSummable.tsum_le_tsum hcell (hbadSummable.mul_left B)
    _ = B * ∑' q : S,
          ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume :=
      hbadSummable.tsum_mul_left B
    _ ≤ B * (2 * ∫ x, ‖f x‖ ∂volume) :=
      mul_le_mul_of_nonneg_left hbadBound hB
    _ = 2 * B * ∫ x, ‖f x‖ ∂volume := by ring

/-- The exact total off-support mass of the restricted outputs is at most
`2 B ‖f‖₁`. This is the existing per-cell summation estimate, rewritten as
ordinary integrals of the zero-extended restricted outputs. -/
theorem dyadicWeakCZ_badOutput_restricted_integrals_tsum_le
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    {f : ℝ → H₁} (hf : Integrable f volume) {t B : ℝ} (hB : 0 ≤ B)
    (v : dyadicVectorMaximalBadCells f t → ℝ → H₂)
    (hOffInt : ∀ q : dyadicVectorMaximalBadCells f t,
      IntegrableOn (fun x => ‖v q x‖)
        (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ volume)
    (hOff : ∀ q : dyadicVectorMaximalBadCells f t,
      ∫ x in (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ, ‖v q x‖ ∂volume ≤
        B * ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume) :
    (∑' q : dyadicVectorMaximalBadCells f t,
      ∫ x, ‖dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
        (v q) x‖ ∂volume) ≤ 2 * B * ∫ x, ‖f x‖ ∂volume := by
  classical
  let E := dyadicWeakCZ_badRegion f t
  have hE : MeasurableSet E := measurableSet_dyadicWeakCZ_badRegion f t
  have hbase := dyadicWeakCZ_badOutput_integrals_tsum_le hf hB v hOffInt hOff
  have hcell (q : dyadicVectorMaximalBadCells f t) :
      ∫ x, ‖dyadicWeakCZ_offSupportOutput E (v q) x‖ ∂volume =
        ∫ x in Eᶜ, ‖v q x‖ ∂volume := by
    have hnormEq : (fun x => ‖dyadicWeakCZ_offSupportOutput E (v q) x‖) =ᵐ[volume]
        Eᶜ.indicator (fun x => ‖v q x‖) := by
      filter_upwards with x
      by_cases hx : x ∈ Eᶜ <;> simp [dyadicWeakCZ_offSupportOutput, hx]
    calc
      ∫ x, ‖dyadicWeakCZ_offSupportOutput E (v q) x‖ ∂volume =
          ∫ x, Eᶜ.indicator (fun x => ‖v q x‖) x ∂volume := by
        apply integral_congr_ae
        exact hnormEq
      _ = ∫ x in Eᶜ, ‖v q x‖ ∂volume := integral_indicator hE.compl
  have hsumEq :
      (∑' q : dyadicVectorMaximalBadCells f t,
        ∫ x, ‖dyadicWeakCZ_offSupportOutput E (v q) x‖ ∂volume) =
      ∑' q : dyadicVectorMaximalBadCells f t,
        ∫ x in Eᶜ, ‖v q x‖ ∂volume := by
    apply tsum_congr
    exact hcell
  change (∑' q : dyadicVectorMaximalBadCells f t,
      ∫ x, ‖dyadicWeakCZ_offSupportOutput E (v q) x‖ ∂volume) ≤ _
  rw [hsumEq]
  exact hbase

/-- The scalar series of off-support bad-output norms is integrable, and its
integral is at most the exact total off-support mass `2 B ‖f‖₁`. -/
theorem dyadicWeakCZ_badOutput_pointwise_series_integrable
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    {f : ℝ → H₁} (hf : Integrable f volume) {t B : ℝ} (hB : 0 ≤ B)
    (v : dyadicVectorMaximalBadCells f t → ℝ → H₂)
    (hv₂ : ∀ q, MemLp (v q) 2 volume)
    (hOffInt : ∀ q : dyadicVectorMaximalBadCells f t,
      IntegrableOn (fun x => ‖v q x‖)
        (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ volume)
    (hOff : ∀ q : dyadicVectorMaximalBadCells f t,
      ∫ x in (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ, ‖v q x‖ ∂volume ≤
        B * ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume) :
    Integrable (fun x => ∑' q : dyadicVectorMaximalBadCells f t,
      ‖dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
        (v q) x‖) volume ∧
      (∫ x, ∑' q : dyadicVectorMaximalBadCells f t,
        ‖dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
          (v q) x‖ ∂volume) ≤ 2 * B * ∫ x, ‖f x‖ ∂volume := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  let w : S → ℝ → H₂ := fun q x =>
    dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t) (v q) x
  let s : S → ℝ → ℝ := fun q x => ‖w q x‖
  obtain ⟨hL1, _, hMass⟩ :=
    dyadicWeakCZ_badOutput_L1_summable hf v hv₂ hOffInt hOff
  have hsInt (q : S) : Integrable (s q) volume := by
    have hwInt : Integrable (w q) volume :=
      memLp_one_iff_integrable.mp (hL1 q)
    simpa [s] using hwInt.norm
  have hsMem (q : S) : MemLp (s q) 1 volume :=
    memLp_one_iff_integrable.mpr (hsInt q)
  have hsNorm : Summable (fun q : S => ‖(hsMem q).toLp (s q)‖) := by
    apply Summable.congr hMass
    intro q
    calc
      ∫ x, ‖w q x‖ ∂volume = ∫ x, ‖s q x‖ ∂volume := by simp [s]
      _ = ‖(hsMem q).toLp (s q)‖ :=
        (L1.norm_of_fun_eq_integral_norm
          (memLp_one_iff_integrable.mp (hsMem q))).symm
  have hsSum : Summable (fun q : S => (hsMem q).toLp (s q)) := hsNorm.of_norm
  have hsNormNeTop :
      (∑' q : S, ‖(hsMem q).toLp (s q)‖ₑ) ≠ ⊤ := by
    have hne := hsNorm.tsum_ofReal_ne_top
    simpa only [← ofReal_norm] using hne
  let U : Lp ℝ 1 volume := ∑' q : S, (hsMem q).toLp (s q)
  have hUInt : Integrable (U : ℝ → ℝ) volume :=
    memLp_one_iff_integrable.mp (Lp.memLp U)
  have hAE := ae_eq_l1_tsum_pointwise_tsum s hsMem hsNormNeTop
  have hSeriesInt : Integrable (fun x => ∑' q : S, s q x) volume :=
    (integrable_congr hAE).mp hUInt
  have hsIntegralSum : Summable (fun q : S => ∫ x, ‖s q x‖ ∂volume) := by
    apply Summable.congr hMass
    intro q
    simp [s, w]
  have hIntegralTsum :=
    integral_tsum_of_summable_integral_norm hsInt hsIntegralSum
  have hMassEq :
      (∑' q : S, ∫ x, s q x ∂volume) =
        ∑' q : S, ∫ x, ‖w q x‖ ∂volume := by
    apply tsum_congr
    intro q
    simp [s, w]
  have htotal :=
    dyadicWeakCZ_badOutput_restricted_integrals_tsum_le hf hB v hOffInt hOff
  refine ⟨?_, ?_⟩
  · simpa [s, w] using hSeriesInt
  · calc
      ∫ x, ∑' q : S, ‖w q x‖ ∂volume =
          ∑' q : S, ∫ x, s q x ∂volume := by
            simpa [s] using hIntegralTsum.symm
      _ = ∑' q : S, ∫ x, ‖w q x‖ ∂volume := hMassEq
      _ ≤ 2 * B * ∫ x, ‖f x‖ ∂volume := by
        simpa [w] using htotal

/-- Apply the general off-support hypothesis to the mean-zero dyadic bad
pieces.  This packages the concrete `L²` outputs and obtains their exact
off-support integrability and `B‖b_Q‖₁` bounds. -/
theorem dyadicWeakCZ_badOutput_series_integrable_of_offSupport
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    {f : ℝ → H₁} (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {t B : ℝ} (hB : 0 ≤ B)
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume) :
    Integrable (fun x => ∑' q : dyadicVectorMaximalBadCells f t,
      ‖dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
        (fun y => (T ((memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
          (dyadicVectorBadPiece f q.1.1 q.1.2))) y) x‖) volume ∧
      (∫ x, ∑' q : dyadicVectorMaximalBadCells f t,
        ‖dyadicWeakCZ_offSupportOutput (dyadicWeakCZ_badRegion f t)
          (fun y => (T ((memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
            (dyadicVectorBadPiece f q.1.1 q.1.2))) y) x‖ ∂volume) ≤
        2 * B * ∫ x, ‖f x‖ ∂volume := by
  classical
  let out : dyadicVectorMaximalBadCells f t → Lp H₂ 2 volume := fun q =>
    T ((memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
      (dyadicVectorBadPiece f q.1.1 q.1.2))
  let v : dyadicVectorMaximalBadCells f t → ℝ → H₂ := fun q => out q
  have hv₂ (q : dyadicVectorMaximalBadCells f t) : MemLp (v q) 2 volume := by
    exact Lp.memLp (out q)
  have hPieces (q : dyadicVectorMaximalBadCells f t) :=
    hOffSupport (dyadicVectorBadPiece f q.1.1 q.1.2) q.1.1 q.1.2
      (memLp_one_iff_integrable.mpr
        (integrable_dyadicVectorBadPiece hf q.1.1 q.1.2))
      (memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2)
      (integral_dyadicVectorBadPiece_eq_zero hf q.1.1 q.1.2)
      (fun x hx => dyadicVectorBadPiece_eq_zero_of_not_mem f q.1.1 q.1.2 hx)
  have hInt (q : dyadicVectorMaximalBadCells f t) :
      IntegrableOn (fun x => ‖v q x‖)
        (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ volume := by
    simpa [v] using hPieces q |>.1
  have hBound (q : dyadicVectorMaximalBadCells f t) :
      ∫ x in (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ, ‖v q x‖ ∂volume ≤
        B * ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume := by
    simpa [v] using hPieces q |>.2
  have hmain := dyadicWeakCZ_badOutput_pointwise_series_integrable
    hf hB v hv₂ hInt hBound
  simpa [v] using hmain


/-- For `p=2`, the square of the extended `L²` seminorm is the integral of
the pointwise squared norm, expressed in `ENNReal`. -/
theorem eLpNorm_two_sq_eq_ofReal_integral_norm_sq
    {H : Type*} [NormedAddCommGroup H] {f : ℝ → H}
    (hf : MemLp f (ENNReal.ofReal 2) volume) :
    eLpNorm f (ENNReal.ofReal 2) volume ^ 2 =
      ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂volume) := by
  have hp0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
  have hpTop : ENNReal.ofReal (2 : ℝ) ≠ ⊤ := by simp
  have hpReal : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by norm_num
  have hsqInt : Integrable (fun x => ‖f x‖ ^ 2) volume := by
    have hf' : MemLp f 2 volume := by simpa using hf
    exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf'
  have hmoment : ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂volume) =
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume := by
    rw [ofReal_integral_eq_lintegral_ofReal hsqInt
      (ae_of_all volume (fun x => sq_nonneg (‖f x‖)))]
    apply lintegral_congr_ae
    filter_upwards with x
    rw [ENNReal.ofReal_pow (norm_nonneg (f x)) 2, ofReal_norm]
  have htwoCast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have hpowEq (x : ℝ) : ‖f x‖ₑ ^ (2 : ℝ) = ‖f x‖ₑ ^ 2 := by
    rw [htwoCast]
    exact ENNReal.rpow_natCast _ 2
  have hIntPow : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume) =
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume := by
    apply lintegral_congr_ae
    filter_upwards with x
    exact hpowEq x
  calc
    eLpNorm f (ENNReal.ofReal 2) volume ^ 2 =
        ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
        hf.aestronglyMeasurable, hpReal]
    _ = ((∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [hIntPow]
    _ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂volume) := hmoment.symm

/-- The actual dyadic good part belongs to `L²`: its pointwise `2t` bound
and its `L¹` integrability make its squared norm integrable. -/
theorem memLp_two_dyadicVectorGoodPart {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    MemLp (dyadicVectorGoodPart f t) 2 volume := by
  let g : ℝ → H := dyadicVectorGoodPart f t
  have hgood : Integrable g volume := by
    dsimp [g]
    exact dyadicVectorGoodPart_integrable hf ht
  have hnorm : Integrable (fun x => ‖g x‖) volume := hgood.norm
  have hsqAES : AEStronglyMeasurable (fun x => ‖g x‖ ^ 2) volume :=
    hnorm.aestronglyMeasurable.pow 2
  have hdom : Integrable (fun x => (2 * t) * ‖g x‖) volume :=
    hnorm.const_mul (2 * t)
  have hsq : Integrable (fun x => ‖g x‖ ^ 2) volume := by
    apply hdom.mono' hsqAES
    filter_upwards [dyadicVectorGoodPart_norm_le_two_ae hf ht] with x hx
    have hnonneg : 0 ≤ ‖g x‖ := norm_nonneg _
    have hle : ‖g x‖ ^ 2 ≤ (2 * t) * ‖g x‖ := by nlinarith
    calc
      ‖‖g x‖ ^ 2‖ = ‖g x‖ ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ (2 * t) * ‖g x‖ := hle
  exact (memLp_two_iff_integrable_sq_norm hgood.aestronglyMeasurable).mpr hsq

/-- The dyadic good part has the exact square estimate required by the
weak-CZ Chebyshev step, in the `eLpNorm` normalization used by Mathlib. -/
theorem eLpNorm_sq_dyadicVectorGoodPart_le {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    eLpNorm (dyadicVectorGoodPart f t) (ENNReal.ofReal 2) volume ^
        (ENNReal.ofReal 2).toReal ≤
      ENNReal.ofReal (2 * t * ∫ x, ‖f x‖ ∂volume) := by
  have hp : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by norm_num
  calc
    eLpNorm (dyadicVectorGoodPart f t) (ENNReal.ofReal 2) volume ^
        (ENNReal.ofReal 2).toReal =
        eLpNorm (dyadicVectorGoodPart f t) (ENNReal.ofReal 2) volume ^ 2 := by
          rw [hp]
          exact ENNReal.rpow_natCast _ 2
    _ = ENNReal.ofReal
        (∫ x, ‖dyadicVectorGoodPart f t x‖ ^ 2 ∂volume) :=
      eLpNorm_two_sq_eq_ofReal_integral_norm_sq (by
        simpa using memLp_two_dyadicVectorGoodPart hf ht)
    _ ≤ ENNReal.ofReal (2 * t * ∫ x, ‖f x‖ ∂volume) :=
      ENNReal.ofReal_le_ofReal (integral_norm_sq_dyadicVectorGoodPart_le hf ht)

/-- The good-part contribution in the weak-CZ proof.  The hypotheses expose
the two inputs separately: the dyadic good-part square estimate and the
strong `L²` bound of the operator. -/
theorem dyadicWeakCZ_goodPart_contribution
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedAddCommGroup H₂]
    {g : ℝ → H₁} {u : ℝ → H₂} {t A L : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A)
    (hgSquare : eLpNorm g (ENNReal.ofReal 2) volume ^
      (ENNReal.ofReal 2).toReal ≤
      ENNReal.ofReal (2 * t * L))
    (hOperator : eLpNorm u (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal 2) volume) :
    volume {x | t / 2 < ‖u x‖} ≤
      ENNReal.ofReal (8 * A ^ 2 * L / t) := by
  have hε : ENNReal.ofReal (t / 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hset : {x | t / 2 < ‖u x‖} ⊆
      {x | ENNReal.ofReal (t / 2) ≤ ‖u x‖ₑ} := by
    intro x hx
    change t / 2 < ‖u x‖ at hx
    change ENNReal.ofReal (t / 2) ≤ ‖u x‖ₑ
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hx)
  have hcheb := MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm
    (μ := volume) (p := ENNReal.ofReal 2)
    (by norm_num : ENNReal.ofReal 2 ≠ 0)
    (by simp : ENNReal.ofReal 2 ≠ ⊤)
    (f := u) hε (by simp)
  have hpReal : (ENNReal.ofReal 2).toReal = 2 := by norm_num
  have hOpSquare : eLpNorm u (ENNReal.ofReal 2) volume ^
      (ENNReal.ofReal 2).toReal ≤
      ENNReal.ofReal (A ^ (ENNReal.ofReal 2).toReal) *
        ENNReal.ofReal (2 * t * L) := by
    calc
      eLpNorm u (ENNReal.ofReal 2) volume ^ (ENNReal.ofReal 2).toReal ≤
          (ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal 2) volume) ^
            (ENNReal.ofReal 2).toReal :=
        ENNReal.rpow_le_rpow hOperator (by norm_num [hpReal])
      _ = (ENNReal.ofReal A) ^ (ENNReal.ofReal 2).toReal *
          eLpNorm g (ENNReal.ofReal 2) volume ^ (ENNReal.ofReal 2).toReal :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num [hpReal])
      _ = ENNReal.ofReal (A ^ (ENNReal.ofReal 2).toReal) *
          eLpNorm g (ENNReal.ofReal 2) volume ^ (ENNReal.ofReal 2).toReal := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hA (by norm_num [hpReal])]
      _ ≤ ENNReal.ofReal (A ^ (ENNReal.ofReal 2).toReal) *
          ENNReal.ofReal (2 * t * L) := by gcongr
  calc
    volume {x | t / 2 < ‖u x‖} ≤
        volume {x | ENNReal.ofReal (t / 2) ≤ ‖u x‖ₑ} := measure_mono hset
    _ ≤ (ENNReal.ofReal (t / 2))⁻¹ ^ (ENNReal.ofReal 2).toReal *
        eLpNorm u (ENNReal.ofReal 2) volume ^ (ENNReal.ofReal 2).toReal := hcheb
    _ ≤ (ENNReal.ofReal (t / 2))⁻¹ ^ (ENNReal.ofReal 2).toReal *
        (ENNReal.ofReal (A ^ (ENNReal.ofReal 2).toReal) *
          ENNReal.ofReal (2 * t * L)) := by
      gcongr
    _ = ENNReal.ofReal (8 * A ^ 2 * L / t) := by
      rw [hpReal]
      change (ENNReal.ofReal (t / 2))⁻¹ ^ ((2 : ℕ) : ℝ) *
          (ENNReal.ofReal (A ^ ((2 : ℕ) : ℝ)) *
            ENNReal.ofReal (2 * t * L)) = _
      rw [ENNReal.rpow_natCast]
      rw [Real.rpow_natCast]
      have hinv : (ENNReal.ofReal (t / 2))⁻¹ =
          ENNReal.ofReal ((t / 2)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos (by positivity : 0 < t / 2)).symm
      have hpow : ENNReal.ofReal (((t / 2)⁻¹) ^ 2) =
          ENNReal.ofReal ((t / 2)⁻¹) ^ 2 :=
        ENNReal.ofReal_pow (by positivity : 0 ≤ (t / 2)⁻¹) 2
      have hmulA : ENNReal.ofReal (A ^ 2 * (2 * t * L)) =
          ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (2 * t * L) :=
        ENNReal.ofReal_mul (by positivity : 0 ≤ A ^ 2)
      have hmulAll : ENNReal.ofReal (((t / 2)⁻¹) ^ 2 *
          (A ^ 2 * (2 * t * L))) =
          ENNReal.ofReal (((t / 2)⁻¹) ^ 2) *
            ENNReal.ofReal (A ^ 2 * (2 * t * L)) :=
        ENNReal.ofReal_mul (sq_nonneg ((t / 2)⁻¹))
      calc
        (ENNReal.ofReal (t / 2))⁻¹ ^ 2 *
            (ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (2 * t * L)) =
            ENNReal.ofReal (((t / 2)⁻¹) ^ 2) *
              (ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (2 * t * L)) := by
          rw [hinv, hpow.symm]
        _ = ENNReal.ofReal (((t / 2)⁻¹) ^ 2) *
              ENNReal.ofReal (A ^ 2 * (2 * t * L)) := by rw [hmulA.symm]
        _ = ENNReal.ofReal (((t / 2)⁻¹) ^ 2 *
              (A ^ 2 * (2 * t * L))) := by rw [hmulAll.symm]
        _ = ENNReal.ofReal (8 * A ^ 2 * L / t) := by
          congr 1 <;> field_simp <;> ring

/-- Apply the good-part Chebyshev estimate to the actual dyadic Calderón–
Zygmund good part, using its checked square-integrability and exact square
bound. -/
theorem dyadicWeakCZ_dyadicGoodPart_contribution
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁] [CompleteSpace H₁]
    [MeasurableSpace H₁] [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂]
    {f : ℝ → H₁} {u : ℝ → H₂} {t A : ℝ}
    (hf : Integrable f volume) (ht : 0 < t)
    (hA : 0 ≤ A)
    (hOperator : eLpNorm u (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal A *
        eLpNorm (dyadicVectorGoodPart f t) (ENNReal.ofReal 2) volume) :
    volume {x | t / 2 < ‖u x‖} ≤
      ENNReal.ofReal (8 * A ^ 2 * (∫ x, ‖f x‖ ∂volume) / t) := by
  exact dyadicWeakCZ_goodPart_contribution (g := dyadicVectorGoodPart f t)
    (L := ∫ x, ‖f x‖ ∂volume) ht hA
    (eLpNorm_sq_dyadicVectorGoodPart_le hf ht) hOperator

/-- Chebyshev's estimate for a pointwise sum of bad-piece outputs away from
the enlarged bad region.  The hypotheses isolate the Fatou/series step from
the operator-specific off-support bounds. -/
theorem dyadicWeakCZ_badSeries_measure_le
    {ι H : Type*} [Countable ι] [NormedAddCommGroup H]
    {E : Set ℝ} {u : ℝ → H} {v : ι → ℝ → H} {t L : ℝ}
    (ht : 0 < t)
    (hpoint : ∀ᵐ x ∂volume, x ∉ E → ‖u x‖ ≤ ∑' i, ‖v i x‖)
    (hseries : Integrable (fun x => ∑' i, ‖v i x‖) volume)
    (hIntegral : (∫ x, ∑' i, ‖v i x‖ ∂volume) ≤ L) :
    volume {x | x ∉ E ∧ t < ‖u x‖} ≤ ENNReal.ofReal (L / t) := by
  let F : ℝ → ℝ := fun x => ∑' i, ‖v i x‖
  have hFnonneg : ∀ x, 0 ≤ F x := by
    intro x
    exact tsum_nonneg (fun i => norm_nonneg (v i x))
  have hFlin : ENNReal.ofReal (∫ x, F x ∂volume) =
      ∫⁻ x, ENNReal.ofReal (F x) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hseries
      (ae_of_all volume hFnonneg)
  have hFmeas : AEMeasurable (fun x => ENNReal.ofReal (F x)) volume := by
    exact hseries.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hε : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  have hεtop : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsubset : {x | x ∉ E ∧ t < ‖u x‖} ≤ᵐ[volume]
      {x | ENNReal.ofReal t ≤ ENNReal.ofReal (F x)} := by
    filter_upwards [hpoint] with x hxpoint
    intro hx
    exact ENNReal.ofReal_le_ofReal
      ((le_of_lt hx.2).trans (hxpoint hx.1))
  calc
    volume {x | x ∉ E ∧ t < ‖u x‖} ≤
        volume {x | ENNReal.ofReal t ≤ ENNReal.ofReal (F x)} := measure_mono_ae hsubset
    _ ≤ (∫⁻ x, ENNReal.ofReal (F x) ∂volume) / ENNReal.ofReal t :=
      MeasureTheory.meas_ge_le_lintegral_div hFmeas hε hεtop
    _ = ENNReal.ofReal ((∫ x, F x ∂volume) / t) := by
      rw [← hFlin, ← ENNReal.ofReal_div_of_pos ht]
    _ ≤ ENNReal.ofReal (L / t) := ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hIntegral ht.le)

/-- Assemble the three estimates in the weak-CZ proof.  The enlarged bad
region, the good output, and the bad output off that region contribute the
exact constants `9`, `8 A²`, and `4 B`. -/
theorem dyadicWeakCZ_weak_bound_of_components
    {H : Type*} [NormedAddCommGroup H]
    {E : Set ℝ} {Tf good bad : ℝ → H} {level M A B : ℝ}
    (hlevel : 0 < level) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hpoint : ∀ᵐ x ∂volume, x ∉ E → ‖Tf x‖ ≤ ‖good x‖ + ‖bad x‖)
    (hE : volume E ≤ ENNReal.ofReal (9 * (M / level)))
    (hGood : volume {x | level / 2 < ‖good x‖} ≤
      ENNReal.ofReal (8 * A ^ 2 * M / level))
    (hBad : volume {x | x ∉ E ∧ level / 2 < ‖bad x‖} ≤
      ENNReal.ofReal (4 * B * M / level)) :
    volume {x | level < ‖Tf x‖} ≤
      ENNReal.ofReal ((9 + 8 * A ^ 2 + 4 * B) * (M / level)) := by
  have hsubset : {x | level < ‖Tf x‖} ≤ᵐ[volume]
      (E ∪ {x | level / 2 < ‖good x‖}) ∪
        {x | x ∉ E ∧ level / 2 < ‖bad x‖} := by
    filter_upwards [hpoint] with x hpointx
    intro hx
    by_cases hxE : x ∈ E
    · exact Or.inl (Or.inl hxE)
    ·
      by_cases hgood : level / 2 < ‖good x‖
      · exact Or.inl (Or.inr hgood)
      ·
        have hgood' : ‖good x‖ ≤ level / 2 := le_of_not_gt hgood
        by_cases hbad : level / 2 < ‖bad x‖
        · exact Or.inr (show x ∈ {x | x ∉ E ∧ level / 2 < ‖bad x‖} from
            ⟨hxE, hbad⟩)
        · have hbad' : ‖bad x‖ ≤ level / 2 := le_of_not_gt hbad
          have hupper : ‖Tf x‖ ≤ level := by
            calc
              ‖Tf x‖ ≤ ‖good x‖ + ‖bad x‖ := hpointx hxE
              _ ≤ level / 2 + level / 2 := add_le_add hgood' hbad'
              _ = level := by ring
          exact False.elim ((not_lt_of_ge hupper) hx)
  have hsum :
      ENNReal.ofReal (9 * (M / level)) +
          ENNReal.ofReal (8 * A ^ 2 * M / level) +
          ENNReal.ofReal (4 * B * M / level) =
        ENNReal.ofReal ((9 + 8 * A ^ 2 + 4 * B) * (M / level)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1 <;> field_simp <;> ring
  calc
    volume {x | level < ‖Tf x‖} ≤
        volume ((E ∪ {x | level / 2 < ‖good x‖}) ∪
          {x | x ∉ E ∧ level / 2 < ‖bad x‖}) := measure_mono_ae hsubset
    _ ≤ volume E + volume {x | level / 2 < ‖good x‖} +
        volume {x | x ∉ E ∧ level / 2 < ‖bad x‖} := by
      calc
        volume ((E ∪ {x | level / 2 < ‖good x‖}) ∪
            {x | x ∉ E ∧ level / 2 < ‖bad x‖}) ≤
            volume (E ∪ {x | level / 2 < ‖good x‖}) +
              volume {x | x ∉ E ∧ level / 2 < ‖bad x‖} := measure_union_le _ _
        _ ≤ volume E + volume {x | level / 2 < ‖good x‖} +
              volume {x | x ∉ E ∧ level / 2 < ‖bad x‖} := by
          gcongr
          exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (9 * (M / level)) +
          ENNReal.ofReal (8 * A ^ 2 * M / level) +
          ENNReal.ofReal (4 * B * M / level) := by
      exact add_le_add (add_le_add hE hGood) hBad
    _ = ENNReal.ofReal ((9 + 8 * A ^ 2 + 4 * B) * (M / level)) := hsum

/-- A uniform off-support estimate forces its constant to be nonnegative as
soon as the source fiber is nontrivial.  The test is the difference of the
two half-cell indicators in the unit dyadic interval. -/
theorem dyadicWeakCZ_offSupport_constant_nonneg_of_nontrivial
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {B : ℝ}
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    (hsource : ¬ Subsingleton H₁) : 0 ≤ B := by
  classical
  letI : CompleteSpace H₁ := FiniteDimensional.complete ℝ H₁
  obtain ⟨e, he⟩ : ∃ e : H₁, e ≠ 0 := by
    by_contra h
    push_neg at h
    apply hsource
    exact ⟨fun x y => by rw [h x, h y]⟩
  let leftHalf : Set ℝ := Set.Ico 0 (1 / 2)
  let rightHalf : Set ℝ := Set.Ico (1 / 2) 1
  have hμLeft : volume leftHalf ≠ (⊤ : ENNReal) := by
    dsimp [leftHalf]
    exact (measure_Ico_lt_top (a := (0 : ℝ)) (b := (1 / 2 : ℝ))).ne
  have hμRight : volume rightHalf ≠ (⊤ : ENNReal) := by
    dsimp [rightHalf]
    exact (measure_Ico_lt_top (a := (1 / 2 : ℝ)) (b := (1 : ℝ))).ne
  have hILeftOne : MemLp (leftHalf.indicator (fun _ : ℝ => e)) 1 volume :=
    memLp_indicator_const 1 measurableSet_Ico.nullMeasurableSet e (Or.inr hμLeft)
  have hIRightOne : MemLp (rightHalf.indicator (fun _ : ℝ => -e)) 1 volume :=
    memLp_indicator_const 1 measurableSet_Ico.nullMeasurableSet (-e) (Or.inr hμRight)
  have hILeftTwo : MemLp (leftHalf.indicator (fun _ : ℝ => e)) 2 volume :=
    memLp_indicator_const 2 measurableSet_Ico.nullMeasurableSet e (Or.inr hμLeft)
  have hIRightTwo : MemLp (rightHalf.indicator (fun _ : ℝ => -e)) 2 volume :=
    memLp_indicator_const 2 measurableSet_Ico.nullMeasurableSet (-e) (Or.inr hμRight)
  let u : ℝ → H₁ :=
    leftHalf.indicator (fun _ => e) + rightHalf.indicator (fun _ => -e)
  have hu₁ : MemLp u 1 volume := by
    simpa [u] using hILeftOne.add hIRightOne
  have hu₂ : MemLp u 2 volume := by
    simpa [u] using hILeftTwo.add hIRightTwo
  have hILeftInt : Integrable (leftHalf.indicator (fun _ : ℝ => e)) volume :=
    memLp_one_iff_integrable.mp hILeftOne
  have hIRightInt : Integrable (rightHalf.indicator (fun _ : ℝ => -e)) volume :=
    memLp_one_iff_integrable.mp hIRightOne
  have hLeftMeas : MeasurableSet leftHalf := by
    simpa [leftHalf] using (measurableSet_Ico :
      MeasurableSet (Set.Ico (0 : ℝ) (1 / 2)))
  have hRightMeas : MeasurableSet rightHalf := by
    simpa [rightHalf] using (measurableSet_Ico :
      MeasurableSet (Set.Ico (1 / 2 : ℝ) 1))
  have hmean : ∫ x, u x ∂volume = 0 := by
    calc
      ∫ x, u x ∂volume =
          (∫ x, leftHalf.indicator (fun _ : ℝ => e) x ∂volume) +
            ∫ x, rightHalf.indicator (fun _ : ℝ => -e) x ∂volume := by
        dsimp [u]
        rw [integral_add hILeftInt hIRightInt]
      _ = volume.real leftHalf • e + volume.real rightHalf • (-e) := by
        rw [integral_indicator_const e hLeftMeas,
          integral_indicator_const (-e) hRightMeas]
      _ = 0 := by norm_num [leftHalf, rightHalf]
  have hsupport : ∀ x, x ∉ dyadicInterval 0 0 → u x = 0 := by
    intro x hx
    have hxQ : ¬ (0 ≤ x ∧ x < 1) := by
      simpa [dyadicInterval] using hx
    have hxOutside : x < 0 ∨ 1 ≤ x := by
      rcases not_and_or.mp hxQ with hleft | hright
      · exact Or.inl (lt_of_not_ge hleft)
      · exact Or.inr (le_of_not_gt hright)
    have hxLeft : x ∉ leftHalf := by
      intro hx'
      simp only [leftHalf, Set.mem_Ico] at hx'
      rcases hxOutside with hleft | hright <;> linarith
    have hxRight : x ∉ rightHalf := by
      intro hx'
      simp only [rightHalf, Set.mem_Ico] at hx'
      rcases hxOutside with hleft | hright <;> linarith
    simp [u, hxLeft, hxRight]
  let p : ℝ → ℝ := leftHalf.indicator (fun _ => ‖e‖)
  have hpMem : MemLp p 1 volume := by
    simpa [p, leftHalf] using
      (memLp_indicator_const 1 measurableSet_Ico.nullMeasurableSet ‖e‖ (Or.inr hμLeft))
  have hpInt : Integrable p volume := memLp_one_iff_integrable.mp hpMem
  have huInt : Integrable u volume := memLp_one_iff_integrable.mp hu₁
  have hnormInt : Integrable (fun x => ‖u x‖) volume := huInt.norm
  have hpoint : ∀ x, p x ≤ ‖u x‖ := by
    intro x
    by_cases hxLeft : x ∈ leftHalf
    · have hxRight : x ∉ rightHalf := by
        intro hxR
        simp only [leftHalf, rightHalf, Set.mem_Ico] at hxLeft hxR
        linarith
      simp [p, u, hxLeft, hxRight]
    · simp [p, hxLeft, norm_nonneg]
  have hpIntegral : ∫ x, p x ∂volume = (1 / 2) * ‖e‖ := by
    dsimp [p]
    rw [integral_indicator_const ‖e‖ hLeftMeas]
    norm_num [leftHalf, smul_eq_mul]
  have heNorm : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hmass : 0 < ∫ x, ‖u x‖ ∂volume := by
    have hpPos : 0 < ∫ x, p x ∂volume := by
      rw [hpIntegral]
      positivity
    exact lt_of_lt_of_le hpPos
      (integral_mono hpInt hnormInt hpoint)
  have hOff := hOffSupport u 0 0 hu₁ hu₂ hmean hsupport
  have hleft : 0 ≤ ∫ x in (dyadicNinefoldInterval 0 0)ᶜ,
      ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume :=
    integral_nonneg (fun x => norm_nonneg _)
  have hmul : 0 ≤ B * ∫ x, ‖u x‖ ∂volume := le_trans hleft hOff.2
  nlinarith

/-- Weak `(1,1)` estimate from the exact dyadic Calderón–Zygmund
decomposition and a uniform off-support bound.  The off-support hypothesis
is stated with `IntegrableOn`, as required for its Bochner integral. -/
theorem weakTypeFromOffSupport_of_nonneg
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {f : ℝ → H₁} (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {level : ℝ} (hlevel : 0 < level) :
    volume {x | level < ‖(T (hf₂.toLp f) : Lp H₂ 2 volume) x‖} ≤
      ENNReal.ofReal ((9 + 8 * A ^ 2 + 4 * B) *
        ((∫ x, ‖f x‖ ∂volume) / level)) := by
  classical
  letI : CompleteSpace H₁ := FiniteDimensional.complete ℝ H₁
  let E : Set ℝ := dyadicWeakCZ_badRegion f level
  have hEmeas : MeasurableSet E := measurableSet_dyadicWeakCZ_badRegion f level
  have hScount : (dyadicVectorMaximalBadCells f level).Countable :=
    Set.countable_univ.mono (Set.subset_univ _)
  letI : Countable (dyadicVectorMaximalBadCells f level) := hScount.to_subtype
  let b : dyadicVectorMaximalBadCells f level → ℝ → H₁ := fun q =>
    dyadicVectorBadPiece f q.1.1 q.1.2
  have hb₁ (q : dyadicVectorMaximalBadCells f level) : MemLp (b q) 1 volume :=
    memLp_one_iff_integrable.mpr (integrable_dyadicVectorBadPiece hf q.1.1 q.1.2)
  have hb₂ (q : dyadicVectorMaximalBadCells f level) : MemLp (b q) 2 volume :=
    memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2
  have hbZero (q : dyadicVectorMaximalBadCells f level) :
      ∫ x, b q x ∂volume = 0 := by
    exact integral_dyadicVectorBadPiece_eq_zero hf q.1.1 q.1.2
  have hbSupport (q : dyadicVectorMaximalBadCells f level) :
      ∀ x, x ∉ dyadicInterval q.1.1 q.1.2 → b q x = 0 := by
    intro x hx
    exact dyadicVectorBadPiece_eq_zero_of_not_mem f q.1.1 q.1.2 hx
  have hbLp₁ : Summable (fun q : dyadicVectorMaximalBadCells f level =>
      (hb₁ q).toLp (b q)) := by
    simpa [b, hb₁, Integrable.toL1] using
      (dyadicVectorBadPieces_l1_summableLp hf (t := level))
  have hbLp₂ : Summable (fun q : dyadicVectorMaximalBadCells f level =>
      (hb₂ q).toLp (b q)) := by
    simpa [b, hb₂] using
      (dyadicVectorBadPieces_l2_summable hf hf₂ (t := level))
  have hbMass : Summable (fun q : dyadicVectorMaximalBadCells f level =>
      ∫ x, ‖b q x‖ ∂volume) := by
    simpa [b] using (dyadicVectorBadPieces_l1_summable hf (t := level))
  have hbNorm : Summable (fun q : dyadicVectorMaximalBadCells f level =>
      ‖(hb₁ q).toLp (b q)‖) := by
    apply Summable.congr hbMass
    intro q
    exact (L1.norm_of_fun_eq_integral_norm
      (memLp_one_iff_integrable.mp (hb₁ q))).symm
  have hbNormNeTop :
      (∑' q : dyadicVectorMaximalBadCells f level,
        ‖(hb₁ q).toLp (b q)‖ₑ) ≠ ⊤ := by
    have hne := hbNorm.tsum_ofReal_ne_top
    simpa only [← ofReal_norm] using hne
  obtain ⟨F, hF⟩ :=
    exists_cofinal_finset_sequence (ι := dyadicVectorMaximalBadCells f level)
  let badInput : Lp H₁ 2 volume := ∑' q, (hb₂ q).toLp (b q)
  let goodInput : Lp H₁ 2 volume :=
    (memLp_two_dyadicVectorGoodPart hf hlevel).toLp
      (dyadicVectorGoodPart f level)
  have hInputSeries := ae_eq_l2_tsum_pointwise_tsum_of_l1_l2_partial_sums
    b hb₁ hb₂ F hF hbLp₁ hbLp₂ hbNormNeTop
  have hInputDecomp : hf₂.toLp f = goodInput + badInput := by
    apply Lp.ext
    filter_upwards [hf₂.coeFn_toLp,
      (memLp_two_dyadicVectorGoodPart hf hlevel).coeFn_toLp,
      hInputSeries, Lp.coeFn_add goodInput badInput] with x hfx hgx hbx hadd
    calc
      hf₂.toLp f x = f x := hfx
      _ = dyadicVectorGoodPart f level x + ∑' q, b q x :=
        dyadicVectorGoodPart_add_badPieces_eq x
      _ = goodInput x + badInput x := by rw [← hgx, ← hbx]
      _ = (goodInput + badInput) x := hadd.symm
  have hTDecomp : T (hf₂.toLp f) = T goodInput + T badInput := by
    rw [hInputDecomp]
    exact map_add T goodInput badInput
  have hAEnorm : ‖T‖ₑ ≤ ENNReal.ofReal A := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hT
  have hGoodOperator :
      eLpNorm (T goodInput : ℝ → H₂) 2 volume ≤
        ENNReal.ofReal A *
          eLpNorm (dyadicVectorGoodPart f level) 2 volume := by
    calc
      eLpNorm (T goodInput : ℝ → H₂) 2 volume = ‖T goodInput‖ₑ := by
        exact (Lp.enorm_def (T goodInput)).symm
      _ ≤ ‖T‖ₑ * ‖goodInput‖ₑ := T.le_opENorm goodInput
      _ ≤ ENNReal.ofReal A * ‖goodInput‖ₑ :=
        mul_le_mul_of_nonneg_right hAEnorm (by positivity)
      _ = ENNReal.ofReal A *
          eLpNorm (dyadicVectorGoodPart f level) 2 volume := by
        rw [Lp.enorm_toLp (memLp_two_dyadicVectorGoodPart hf hlevel)]
  have hGoodOperator' :
      eLpNorm (fun x => (T goodInput : ℝ → H₂) x) (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal A *
          eLpNorm (dyadicVectorGoodPart f level) (ENNReal.ofReal 2) volume := by
    simpa using hGoodOperator
  have hGood : volume {x | level / 2 < ‖(T goodInput : ℝ → H₂) x‖} ≤
      ENNReal.ofReal (8 * A ^ 2 * (∫ x, ‖f x‖ ∂volume) / level) :=
    dyadicWeakCZ_dyadicGoodPart_contribution
      (f := f) (u := fun x => (T goodInput : ℝ → H₂) x)
      (t := level) (A := A) hf hlevel hA hGoodOperator'
  let out : dyadicVectorMaximalBadCells f level → Lp H₂ 2 volume := fun q =>
    T ((hb₂ q).toLp (b q))
  let v : dyadicVectorMaximalBadCells f level → ℝ → H₂ := fun q => out q
  have hv₂ (q : dyadicVectorMaximalBadCells f level) : MemLp (v q) 2 volume :=
    Lp.memLp (out q)
  have hPieces (q : dyadicVectorMaximalBadCells f level) :=
    hOffSupport (b q) q.1.1 q.1.2 (hb₁ q) (hb₂ q)
      (hbZero q) (hbSupport q)
  have hOffInt (q : dyadicVectorMaximalBadCells f level) :
      IntegrableOn (fun x => ‖v q x‖)
        (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ volume := by
    simpa [v, out] using (hPieces q).1
  have hOff (q : dyadicVectorMaximalBadCells f level) :
      ∫ x in (dyadicNinefoldInterval q.1.1 q.1.2)ᶜ, ‖v q x‖ ∂volume ≤
        B * ∫ x, ‖b q x‖ ∂volume := by
    simpa [v, out] using (hPieces q).2
  obtain ⟨hOutL1, hOutSumL1, hOutMass⟩ :=
    dyadicWeakCZ_badOutput_L1_summable hf v hv₂ hOffInt hOff
  have hOutNorm : Summable (fun q : dyadicVectorMaximalBadCells f level =>
      ‖(hOutL1 q).toLp
        (dyadicWeakCZ_offSupportOutput E (v q))‖) := by
    apply Summable.congr hOutMass
    intro q
    exact (L1.norm_of_fun_eq_integral_norm
      (memLp_one_iff_integrable.mp (hOutL1 q))).symm
  have hOutNormNeTop :
      (∑' q : dyadicVectorMaximalBadCells f level,
        ‖(hOutL1 q).toLp
          (dyadicWeakCZ_offSupportOutput E (v q))‖ₑ) ≠ ⊤ := by
    have hne := hOutNorm.tsum_ofReal_ne_top
    simpa only [← ofReal_norm] using hne
  have hEcompl : MeasurableSet Eᶜ := hEmeas.compl
  let R : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ) :=
    dyadicWeakCZ_L2_restrict Eᶜ hEcompl
  have hOutSumL2 : Summable (fun q : dyadicVectorMaximalBadCells f level =>
      R (out q)) := by
    simpa [R, out, b] using
      (dyadicWeakCZ_badOutput_L2_summable hf hf₂ T)
  have hOutL2 (q : dyadicVectorMaximalBadCells f level) :
      MemLp (dyadicWeakCZ_offSupportOutput E (v q)) 2 volume :=
    (Lp.memLp (out q)).indicator hEcompl.nullMeasurableSet
  have hOutTerm (q : dyadicVectorMaximalBadCells f level) :
      R (out q) = (hOutL2 q).toLp
        (dyadicWeakCZ_offSupportOutput E (v q)) := by
    change ((Lp.memLp (out q)).indicator hEcompl.nullMeasurableSet).toLp
        (Eᶜ.indicator (out q)) = _
    rfl
  have hOutSumL2' : Summable (fun q : dyadicVectorMaximalBadCells f level =>
      (hOutL2 q).toLp (dyadicWeakCZ_offSupportOutput E (v q))) := by
    apply Summable.congr hOutSumL2
    intro q
    exact hOutTerm q
  have hOutPointwise :=
    dyadicWeakCZ_badOutput_L2_tsum_eq_offSupport_pointwise_tsum
      (H₁ := H₁) (H₂ := H₂) (f := f) (t := level) (v := v)
      F hF hOutL1 hOutL2 hOutSumL1 hOutSumL2' hOutNormNeTop
  have hOutMap : Summable (fun q : dyadicVectorMaximalBadCells f level => out q) :=
    T.summable hbLp₂
  have hTbadSum : T badInput = ∑' q, out q := by
    simpa [badInput, out, b] using T.map_tsum hbLp₂
  have hRbadSum : R (T badInput) =
      ∑' q : dyadicVectorMaximalBadCells f level, R (out q) := by
    rw [hTbadSum]
    exact R.map_tsum hOutMap
  have hRbadSum' : R (T badInput) =
      ∑' q : dyadicVectorMaximalBadCells f level,
        (hOutL2 q).toLp (dyadicWeakCZ_offSupportOutput E (v q)) := by
    calc
      R (T badInput) = ∑' q, R (out q) := hRbadSum
      _ = ∑' q, (hOutL2 q).toLp
          (dyadicWeakCZ_offSupportOutput E (v q)) := by
        apply tsum_congr
        exact hOutTerm
  have hRbadPointwise : (R (T badInput) : ℝ → H₂) =ᵐ[volume]
      dyadicWeakCZ_offSupportOutput E (fun y => ∑' q, v q y) := by
    filter_upwards [Lp.ext_iff.mp hRbadSum', hOutPointwise] with x hsum hpoint
    exact hsum.trans hpoint
  have hRrep : (R (T badInput) : ℝ → H₂) =ᵐ[volume]
      Eᶜ.indicator (T badInput : ℝ → H₂) := by
    change (((Lp.memLp (T badInput)).indicator hEcompl.nullMeasurableSet).toLp
      (Eᶜ.indicator (T badInput)) : ℝ → H₂) =ᵐ[volume]
        Eᶜ.indicator (T badInput)
    exact ((Lp.memLp (T badInput)).indicator hEcompl.nullMeasurableSet).coeFn_toLp
  have hBadOutside : ∀ᵐ x ∂volume, x ∉ E →
      (T badInput : ℝ → H₂) x = ∑' q, v q x := by
    filter_upwards [hRrep, hRbadPointwise] with x hrep hpoint
    intro hxE
    have h := hrep.symm.trans hpoint
    simpa [dyadicWeakCZ_offSupportOutput, hxE] using h
  have hTdecompPointwise : (T (hf₂.toLp f) : ℝ → H₂) =ᵐ[volume]
      (fun x => (T goodInput : ℝ → H₂) x + (T badInput : ℝ → H₂) x) := by
    filter_upwards [Lp.ext_iff.mp hTDecomp,
      Lp.coeFn_add (T goodInput) (T badInput)] with x hEq hAdd
    exact hEq.trans hAdd
  have hpoint : ∀ᵐ x ∂volume, x ∉ E →
      ‖(T (hf₂.toLp f) : ℝ → H₂) x‖ ≤
        ‖(T goodInput : ℝ → H₂) x‖ + ‖(fun x => ∑' q, v q x) x‖ := by
    filter_upwards [hTdecompPointwise, hBadOutside] with x hdecomp hbad
    intro hxE
    rw [hdecomp, hbad hxE]
    exact norm_add_le _ _
  have hSeries := dyadicWeakCZ_badOutput_pointwise_series_integrable
    hf hB v hv₂ hOffInt hOff
  let vRestricted : dyadicVectorMaximalBadCells f level → ℝ → H₂ := fun q =>
    dyadicWeakCZ_offSupportOutput E (v q)
  have hBadNorm := dyadicWeakCZ_badOutput_tsum_norm_le_ae E v hOutL1 hOutMass
  have hBadSeriesPoint : ∀ᵐ x ∂volume, x ∉ E →
      ‖(fun x => ∑' q, v q x) x‖ ≤ ∑' q, ‖vRestricted q x‖ := by
    filter_upwards [hBadNorm] with x hx
    intro hxE
    simpa [vRestricted, dyadicWeakCZ_offSupportOutput, hxE] using hx hxE
  have hBadSet0 := dyadicWeakCZ_badSeries_measure_le
    (u := fun x => ∑' q, v q x) (v := vRestricted) (t := level / 2)
    (L := 2 * B * ∫ x, ‖f x‖ ∂volume)
    (by positivity) hBadSeriesPoint hSeries.1 hSeries.2
  have hBad : volume {x | x ∉ E ∧ level / 2 <
      ‖(fun x => ∑' q, v q x) x‖} ≤
      ENNReal.ofReal (4 * B * (∫ x, ‖f x‖ ∂volume) / level) := by
    calc
      volume {x | x ∉ E ∧ level / 2 < ‖(fun x => ∑' q, v q x) x‖} ≤
          ENNReal.ofReal ((2 * B * ∫ x, ‖f x‖ ∂volume) / (level / 2)) := hBadSet0
      _ = ENNReal.ofReal (4 * B * (∫ x, ‖f x‖ ∂volume) / level) := by
        congr 1 <;> field_simp [hlevel.ne'] <;> ring
  have hM : 0 ≤ ∫ x, ‖f x‖ ∂volume :=
    integral_nonneg (fun x => norm_nonneg _)
  have hBadRegion : volume E ≤
      ENNReal.ofReal (9 * ((∫ x, ‖f x‖ ∂volume) / level)) := by
    simpa [E, dyadicWeakCZ_badRegion] using
      dyadicVectorMaximalBadCells_ninefold_measure_le hf hlevel
  exact dyadicWeakCZ_weak_bound_of_components hlevel hB hM hpoint
    hBadRegion hGood hBad

/-- Weak `(1,1)` from the off-support hypothesis, with no sign assumptions
on its constants.  The sign of `A` follows from the operator norm bound; for
nontrivial source fibers the universal off-support hypothesis forces `B≥0`.
-/
theorem weakTypeFromOffSupport_weakPart
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {f : ℝ → H₁} (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {level : ℝ} (hlevel : 0 < level) :
    volume {x | level < ‖(T (hf₂.toLp f) : Lp H₂ 2 volume) x‖} ≤
      ENNReal.ofReal ((9 + 8 * A ^ 2 + 4 * B) *
        ((∫ x, ‖f x‖ ∂volume) / level)) := by
  classical
  by_cases hsub : Subsingleton H₁
  · letI : Subsingleton H₁ := hsub
    have hInput : hf₂.toLp f = 0 := by
      apply Lp.ext
      filter_upwards with x
      exact Subsingleton.elim _ _
    have hOutput : T (hf₂.toLp f) = 0 := by rw [hInput, map_zero]
    have hEmpty : {x | level < ‖(T (hf₂.toLp f) : Lp H₂ 2 volume) x‖} = ∅ := by
      ext x
      simp [hOutput, hlevel.le]
    simp [hEmpty]
  · have hA : 0 ≤ A := le_trans (norm_nonneg T) hT
    have hB : 0 ≤ B :=
      dyadicWeakCZ_offSupport_constant_nonneg_of_nontrivial T hOffSupport hsub
    exact weakTypeFromOffSupport_of_nonneg T hA hB hT hOffSupport hf hf₂ hlevel

/-- The zero `L²` operator bound forces the original map to vanish.  This
is the `A = 0` branch used when defining the strong `Lᵖ` constants in
`lj:weak-cz`. -/
theorem weakTypeFromOffSupport_zero_operator
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (hT : ‖T‖ ≤ 0) :
    T = 0 := by
  have hnorm : ‖T‖ = 0 := le_antisymm hT (norm_nonneg T)
  ext f
  have hTf : ‖T f‖ ≤ 0 := by
    calc
      ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
      _ = 0 := by rw [hnorm]; simp
  exact Lp.ext_iff.mp (norm_eq_zero.mp (le_antisymm hTf (norm_nonneg _)))

/-- A measurable, bounded function with finite-measure support belongs to
every finite or infinite `Lᵖ` space. -/
private theorem memLp_of_bounded_finite_support
    {H : Type*} [NormedAddCommGroup H]
    {f : ℝ → H} (hf : AEStronglyMeasurable f volume)
    (hS : MeasurableSet {x | f x ≠ 0})
    (hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hμS : volume {x | f x ≠ 0} < ∞) (p : ℝ≥0∞) :
    MemLp f p volume := by
  rcases hbound with ⟨C, hC⟩
  let major : ℝ → ℝ := {x | f x ≠ 0}.indicator (fun _ => C)
  have hmajor : MemLp major p volume := by
    simpa [major] using
      (memLp_indicator_const p hS.nullMeasurableSet C (Or.inr (ne_of_lt hμS)))
  have hdom : ∀ x, ‖f x‖ ≤ major x := by
    intro x
    by_cases hx : f x ≠ 0
    · simpa [major, hx] using hC x
    · have hfx : f x = 0 := not_ne_iff.mp hx
      simp [major, hx, hfx]
  exact hmajor.mono' hf (Filter.Eventually.of_forall hdom)

/-- Bounded measurable functions with finite-measure support form a real
subspace. This is the dense domain used to extend an `L²`-defined operator
after the interpolated estimate has been proved there. -/
private def weakCZBoundedFiniteSupportSubmodule
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H] :
    Submodule ℝ (ℝ → H) := by
  letI : MeasurableAdd₂ H := ⟨continuous_add.measurable⟩
  letI : MeasurableSMul₂ ℝ H := ⟨continuous_smul.measurable⟩
  refine {
    carrier := fun f => Measurable f ∧
      (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧ volume {x | f x ≠ 0} < ∞
    zero_mem' := by
      refine ⟨measurable_const, ⟨0, ?_⟩, ?_⟩
      · intro x
        simp
      · simp
    add_mem' := by
      intro f g hf hg
      rcases hf.2.1 with ⟨Cf, hCf⟩
      rcases hg.2.1 with ⟨Cg, hCg⟩
      refine ⟨hf.1.add hg.1, ⟨max Cf 0 + max Cg 0, ?_⟩, ?_⟩
      · intro x
        calc
          ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
          _ ≤ max Cf 0 + max Cg 0 :=
            add_le_add (hCf x |>.trans (le_max_left Cf 0))
              (hCg x |>.trans (le_max_left Cg 0))
      · have hsubset : {x | f x + g x ≠ 0} ⊆
          {x | f x ≠ 0} ∪ {x | g x ≠ 0} := by
            intro x hx
            by_contra h
            have hfx : f x = 0 := by
              by_contra hfx
              exact h (Or.inl hfx)
            have hgx : g x = 0 := by
              by_contra hgx
              exact h (Or.inr hgx)
            exact hx (by simp [hfx, hgx])
        exact (measure_mono hsubset).trans_lt
          (measure_union_lt_top hf.2.2 hg.2.2)
    smul_mem' := by
      intro c f hf
      rcases hf.2.1 with ⟨Cf, hCf⟩
      refine ⟨hf.1.const_smul c,
        ⟨‖c‖ * max Cf 0, ?_⟩, ?_⟩
      · intro x
        calc
          ‖c • f x‖ = ‖c‖ * ‖f x‖ := norm_smul _ _
          _ ≤ ‖c‖ * max Cf 0 :=
            mul_le_mul_of_nonneg_left (hCf x |>.trans (le_max_left Cf 0))
              (norm_nonneg _)
      · have hsubset : {x | c • f x ≠ 0} ⊆ {x | f x ≠ 0} := by
          intro x hx
          by_contra h
          have hfx : f x = 0 := not_ne_iff.mp h
          exact hx (by simp [hfx])
        exact (measure_mono hsubset).trans_lt hf.2.2
  }

/-- The canonical embedding of this dense domain into a finite-exponent
`Lp` space. -/
private noncomputable def weakCZBoundedFiniteSupport_toLp
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    (p : ℝ≥0∞) :
    weakCZBoundedFiniteSupportSubmodule (H := H) →ₗ[ℝ]
      Lp H p (volume : Measure ℝ) := by
  classical
  let D := weakCZBoundedFiniteSupportSubmodule (H := H)
  let toLp' : D → Lp H p volume := fun f =>
    (memLp_of_bounded_finite_support f.2.1.aestronglyMeasurable
      (by
        have hz : MeasurableSet {x | f.1 x = 0} :=
          measurableSet_eq_fun f.2.1 measurable_const
        have hs : {x | f.1 x ≠ 0} = {x | f.1 x = 0}ᶜ := by
          ext x
          simp
        rw [hs]
        exact hz.compl)
      f.2.2.1 f.2.2.2 p).toLp f.1
  refine {
    toFun := toLp'
    map_add' := by
      intro f g
      apply Lp.ext
      let hf := memLp_of_bounded_finite_support f.2.1.aestronglyMeasurable
        (by
          have hz : MeasurableSet {x | f.1 x = 0} :=
            measurableSet_eq_fun f.2.1 measurable_const
          have hs : {x | f.1 x ≠ 0} = {x | f.1 x = 0}ᶜ := by
            ext x
            simp
          rw [hs]
          exact hz.compl)
        f.2.2.1 f.2.2.2 p
      let hg := memLp_of_bounded_finite_support g.2.1.aestronglyMeasurable
        (by
          have hz : MeasurableSet {x | g.1 x = 0} :=
            measurableSet_eq_fun g.2.1 measurable_const
          have hs : {x | g.1 x ≠ 0} = {x | g.1 x = 0}ᶜ := by
            ext x
            simp
          rw [hs]
          exact hz.compl)
        g.2.2.1 g.2.2.2 p
      let hsumMem := memLp_of_bounded_finite_support (f + g).2.1.aestronglyMeasurable
        (by
          have hz : MeasurableSet {x | (f + g).1 x = 0} :=
            measurableSet_eq_fun (f + g).2.1 measurable_const
          have hs : {x | (f + g).1 x ≠ 0} = {x | (f + g).1 x = 0}ᶜ := by
            ext x
            simp
          rw [hs]
          exact hz.compl)
        (f + g).2.2.1 (f + g).2.2.2 p
      filter_upwards [hsumMem.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
        Lp.coeFn_add (hf.toLp f.1) (hg.toLp g.1)] with x hsumAE hfAE hgAE hadd
      calc
        hsumMem.toLp (f.1 + g.1) x = f.1 x + g.1 x := hsumAE
        _ = hf.toLp f.1 x + hg.toLp g.1 x := by rw [hfAE, hgAE]
        _ = ((hf.toLp f.1) + (hg.toLp g.1)) x := hadd.symm
    map_smul' := by
      intro c f
      apply Lp.ext
      let hf := memLp_of_bounded_finite_support f.2.1.aestronglyMeasurable
        (by
          have hz : MeasurableSet {x | f.1 x = 0} :=
            measurableSet_eq_fun f.2.1 measurable_const
          have hs : {x | f.1 x ≠ 0} = {x | f.1 x = 0}ᶜ := by
            ext x
            simp
          rw [hs]
          exact hz.compl)
        f.2.2.1 f.2.2.2 p
      let hc := memLp_of_bounded_finite_support (c • f).2.1.aestronglyMeasurable
        (by
          have hz : MeasurableSet {x | (c • f).1 x = 0} :=
            measurableSet_eq_fun (c • f).2.1 measurable_const
          have hs : {x | (c • f).1 x ≠ 0} = {x | (c • f).1 x = 0}ᶜ := by
            ext x
            simp
          rw [hs]
          exact hz.compl)
        (c • f).2.2.1 (c • f).2.2.2 p
      filter_upwards [hc.coeFn_toLp, hf.coeFn_toLp,
        Lp.coeFn_smul c (hf.toLp f.1)] with x hcAE hfAE hsmul
      calc
        hc.toLp (c • f.1) x = c • f.1 x := hcAE
        _ = c • hf.toLp f.1 x := by rw [hfAE]
        _ = (c • hf.toLp f.1) x := hsmul.symm
  }

/-- Bounded measurable functions with finite-measure support are dense in
every finite `Lp` exponent.  Compactly supported continuous approximants
give elements of the dense domain above. -/
private theorem weakCZBoundedFiniteSupport_denseRange
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    DenseRange (weakCZBoundedFiniteSupport_toLp (H := H) p) := by
  classical
  rw [Metric.denseRange_iff]
  intro f r hr
  let ε : ℝ := r / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεne : ENNReal.ofReal ε ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨g, hgcompact, happrox, hgcont, hgmem⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp hεne
  have hsupport : {x | g x ≠ 0} ⊆ tsupport g := by
    intro x hx
    exact subset_tsupport g hx
  have hμ : volume {x | g x ≠ 0} < ∞ :=
    (measure_mono hsupport).trans_lt hgcompact.measure_lt_top
  obtain ⟨C, hC⟩ := hgcont.bounded_above_of_compact_support hgcompact
  let d : weakCZBoundedFiniteSupportSubmodule (H := H) :=
    ⟨g, hgcont.measurable, ⟨C, hC⟩, hμ⟩
  let dMem : MemLp g p volume :=
    memLp_of_bounded_finite_support d.2.1.aestronglyMeasurable
      (by
        have hz : MeasurableSet {x | g x = 0} :=
          measurableSet_eq_fun d.2.1 measurable_const
        have hs : {x | g x ≠ 0} = {x | g x = 0}ᶜ := by
          ext x
          simp
        rw [hs]
        exact hz.compl)
      d.2.2.1 d.2.2.2 p
  let dLp : Lp H p volume := weakCZBoundedFiniteSupport_toLp p d
  have hcoe : (dLp : ℝ → H) =ᵐ[volume] g := by
    dsimp [dLp, weakCZBoundedFiniteSupport_toLp]
    exact dMem.coeFn_toLp
  have hdiff : (fun x => (f : ℝ → H) x - (dLp : ℝ → H) x) =ᵐ[volume]
      (fun x => (f : ℝ → H) x - g x) := by
    filter_upwards [hcoe] with x hx
    simp [hx]
  have hdist : dist f dLp < r := by
    calc
      dist f dLp = (eLpNorm ((f : ℝ → H) - (dLp : ℝ → H)) p volume).toReal :=
        Lp.dist_def f dLp
      _ = (eLpNorm ((f : ℝ → H) - g) p volume).toReal :=
        congrArg ENNReal.toReal (eLpNorm_congr_ae hdiff)
      _ ≤ (ENNReal.ofReal ε).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top happrox
      _ = ε := ENNReal.toReal_ofReal hε.le
      _ < r := by dsimp [ε]; linarith
  exact ⟨d, hdist⟩

/-- The measurable representatives form a real vector subspace of the raw
function space.  This is used only to choose a linear representative of an
`L²` output; the weak estimate above remains valid for the more general
measurable-space assumptions in the blueprint. -/
private def weakCZMeasurableFunctionSubmodule
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H] :
    Submodule ℝ (ℝ → H) := by
  letI : MeasurableAdd₂ H := ⟨continuous_add.measurable⟩
  letI : MeasurableSMul₂ ℝ H := ⟨continuous_smul.measurable⟩
  exact {
    carrier := {f | Measurable f}
    zero_mem' := measurable_const
    add_mem' := fun hf hg => hf.add hg
    smul_mem' := by
      intro c f hf
      exact measurable_const.smul hf
  }

/-- The quotient map from measurable functions onto `L⁰` has a real-linear
right inverse.  Existence follows from projectivity of vector spaces over
`ℝ`; the selected representative is measurable and makes output additivity
pointwise, rather than merely almost everywhere. -/
private theorem weakCZMeasurableFunctionSection_exists
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H] :
    ∃ S : (ℝ →ₘ[volume] H) →ₗ[ℝ]
        weakCZMeasurableFunctionSubmodule (H := H),
      ∀ f, AEEqFun.mk (S f).1 ((S f).2.aestronglyMeasurable) = f := by
  let toLpZero : weakCZMeasurableFunctionSubmodule (H := H) →ₗ[ℝ]
      ℝ →ₘ[volume] H := {
    toFun := fun f => AEEqFun.mk f.1 f.2.aestronglyMeasurable
    map_add' := by
      intro f g
      change AEEqFun.mk (f.1 + g.1) _ =
        AEEqFun.mk f.1 _ + AEEqFun.mk g.1 _
      exact (AEEqFun.mk_add_mk f.1 g.1 f.2.aestronglyMeasurable
        g.2.aestronglyMeasurable).symm
    map_smul' := by
      intro c f
      change AEEqFun.mk (c • f.1) _ = c • AEEqFun.mk f.1 _
      exact (AEEqFun.smul_mk c f.1 f.2.aestronglyMeasurable).symm
  }
  have hsurj : Function.Surjective toLpZero := by
    intro f
    refine ⟨⟨f, f.measurable⟩, ?_⟩
    change AEEqFun.mk (f : ℝ → H) _ = f
    exact AEEqFun.mk_coeFn f
  letI : Module.Free ℝ (ℝ →ₘ[volume] H) :=
    Module.Free.of_divisionRing ℝ (ℝ →ₘ[volume] H)
  obtain ⟨S, hS⟩ := LinearMap.exists_rightInverse_of_surjective toLpZero
    (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨S, ?_⟩
  intro f
  change toLpZero (S f) = f
  exact LinearMap.congr_fun hS f

private noncomputable def weakCZMeasurableFunctionSection
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H] :
    (ℝ →ₘ[volume] H) →ₗ[ℝ]
      weakCZMeasurableFunctionSubmodule (H := H) :=
  Classical.choose weakCZMeasurableFunctionSection_exists

private theorem weakCZMeasurableFunctionSection_spec
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    (f : ℝ →ₘ[volume] H) :
    AEEqFun.mk ((weakCZMeasurableFunctionSection (H := H) f).1)
      ((weakCZMeasurableFunctionSection (H := H) f).2.aestronglyMeasurable) = f :=
  Classical.choose_spec weakCZMeasurableFunctionSection_exists f

/-- A continuous `L²` operator has a pointwise-linear measurable output
representative, chosen by the right inverse above. -/
private noncomputable def weakCZLinearOutputRepresentative
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ)) :
    Lp H₁ 2 (volume : Measure ℝ) →ₗ[ℝ]
      weakCZMeasurableFunctionSubmodule (H := H₂) := by
  let lpToAEEqFun : Lp H₂ 2 (volume : Measure ℝ) →ₗ[ℝ]
      ℝ →ₘ[volume] H₂ := {
    toFun := fun f => f.1
    map_add' := by intro f g; rfl
    map_smul' := by intro c f; rfl
  }
  exact (weakCZMeasurableFunctionSection (H := H₂)).comp
    (lpToAEEqFun.comp T.toLinearMap)

private theorem weakCZLinearOutputRepresentative_mk
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (f : Lp H₁ 2 (volume : Measure ℝ)) :
    AEEqFun.mk ((weakCZLinearOutputRepresentative T f).1)
      ((weakCZLinearOutputRepresentative T f).2.aestronglyMeasurable) =
        (T f).1 := by
  exact weakCZMeasurableFunctionSection_spec ((T f).1)

private theorem weakCZLinearOutputRepresentative_add
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (f g : Lp H₁ 2 (volume : Measure ℝ)) :
    (weakCZLinearOutputRepresentative T (f + g)).1 =
      (weakCZLinearOutputRepresentative T f).1 +
        (weakCZLinearOutputRepresentative T g).1 := by
  exact congrArg Subtype.val
    ((weakCZLinearOutputRepresentative T).map_add f g)

private theorem weakCZLinearOutputRepresentative_smul
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ)) (c : ℝ)
    (f : Lp H₁ 2 (volume : Measure ℝ)) :
    (weakCZLinearOutputRepresentative T (c • f)).1 =
      c • (weakCZLinearOutputRepresentative T f).1 := by
  exact congrArg Subtype.val
    ((weakCZLinearOutputRepresentative T).map_smul c f)

private def weakCZDirectionalInput {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (θ : ℝ → H) (g : ℝ → ℂ) : ℝ → H :=
  fun x => Complex.re (g x) • θ x

/-- Real directional scalarization preserves the finite-support `L¹` and
`L²` input classes needed by the weak-CZ hypothesis. -/
private theorem weakCZDirectionalInput_memLp_one_two
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    (θ : ℝ → H) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (g : Variation.LayerCakeInput volume) :
    MemLp (weakCZDirectionalInput θ g.1) 1 volume ∧
      MemLp (weakCZDirectionalInput θ g.1) 2 volume := by
  classical
  have hBounded := g.2.2.1
  have hμ := g.2.2.2
  rcases hBounded with ⟨C, hC⟩
  have hgSupportMeas : MeasurableSet {x | g.1 x ≠ 0} := by
    have hzero : MeasurableSet {x | g.1 x = 0} :=
      measurableSet_eq_fun g.2.1 measurable_const
    have hcompl : {x | g.1 x ≠ 0} = {x | g.1 x = 0}ᶜ := by
      ext x
      simp
    rw [hcompl]
    exact hzero.compl
  have hθScalar : Measurable (fun x => Complex.re (g.1 x)) :=
    Complex.measurable_re.comp g.2.1
  have hdirMeas : Measurable (weakCZDirectionalInput θ g.1) :=
    hθScalar.smul hθ
  have hdirNorm : ∀ x, ‖weakCZDirectionalInput θ g.1 x‖ ≤ ‖g.1 x‖ := by
    intro x
    calc
      ‖weakCZDirectionalInput θ g.1 x‖ = |Complex.re (g.1 x)| * ‖θ x‖ := by
        simp [weakCZDirectionalInput, norm_smul, Real.norm_eq_abs]
      _ ≤ |Complex.re (g.1 x)| * 1 :=
        mul_le_mul_of_nonneg_left (hθnorm x) (abs_nonneg _)
      _ ≤ ‖g.1 x‖ := by simpa using Complex.abs_re_le_norm (g.1 x)
  have hdirBound : ∃ D : ℝ, ∀ x,
      ‖weakCZDirectionalInput θ g.1 x‖ ≤ D := by
    exact ⟨C, fun x => (hdirNorm x).trans (hC x)⟩
  have hdirSupportMeas :
      MeasurableSet {x | weakCZDirectionalInput θ g.1 x ≠ 0} := by
    have hzero : MeasurableSet
        {x | weakCZDirectionalInput θ g.1 x = 0} :=
      measurableSet_eq_fun hdirMeas measurable_const
    have hcompl : {x | weakCZDirectionalInput θ g.1 x ≠ 0} =
        {x | weakCZDirectionalInput θ g.1 x = 0}ᶜ := by
      ext x
      simp
    rw [hcompl]
    exact hzero.compl
  have hdirSupportSubset :
      {x | weakCZDirectionalInput θ g.1 x ≠ 0} ⊆ {x | g.1 x ≠ 0} := by
    intro x hx
    by_contra hgx
    have hgzero : g.1 x = 0 := not_ne_iff.mp hgx
    simp [weakCZDirectionalInput, hgzero] at hx
  have hdirμ : volume {x | weakCZDirectionalInput θ g.1 x ≠ 0} < ∞ :=
    (measure_mono hdirSupportSubset).trans_lt hμ
  have hdir1 : MemLp (weakCZDirectionalInput θ g.1) 1 volume :=
    memLp_of_bounded_finite_support hdirMeas.aestronglyMeasurable
      hdirSupportMeas hdirBound hdirμ 1
  have hdir2 : MemLp (weakCZDirectionalInput θ g.1) 2 volume :=
    memLp_of_bounded_finite_support hdirMeas.aestronglyMeasurable
      hdirSupportMeas hdirBound hdirμ 2
  exact ⟨hdir1, hdir2⟩

private noncomputable def weakCZDirectionalL2Input
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    (θ : ℝ → H) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) : Lp H 2 (volume : Measure ℝ) :=
  let hmem := weakCZDirectionalInput_memLp_one_two θ hθ hθnorm g
  hmem.2.toLp (weakCZDirectionalInput θ g.1)

private theorem weakCZDirectionalL2Input_eq_toLp
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    (θ : ℝ → H) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (g : Variation.LayerCakeInput (volume : Measure ℝ))
    (hu₂ : MemLp (weakCZDirectionalInput θ g.1) 2 volume) :
    weakCZDirectionalL2Input θ hθ hθnorm g =
      hu₂.toLp (weakCZDirectionalInput θ g.1) := by
  apply Lp.ext
  filter_upwards [
    (weakCZDirectionalInput_memLp_one_two θ hθ hθnorm g).2.coeFn_toLp,
    hu₂.coeFn_toLp] with x hx₁ hx₂
  exact hx₁.trans hx₂.symm

private noncomputable def weakCZDirectionalOutput
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ] Lp H₂ 2 (volume : Measure ℝ))
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) : ℝ → H₂ :=
  (weakCZLinearOutputRepresentative T
    (weakCZDirectionalL2Input θ hθ hθnorm g)).1

private theorem weakCZDirectionalOutput_measurable
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ] Lp H₂ 2 (volume : Measure ℝ))
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) :
    Measurable (weakCZDirectionalOutput T θ hθ hθnorm g) :=
  (weakCZLinearOutputRepresentative T
    (weakCZDirectionalL2Input θ hθ hθnorm g)).2

private theorem weakCZDirectionalOutput_add
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ] Lp H₂ 2 (volume : Measure ℝ))
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (f g : Variation.LayerCakeInput (volume : Measure ℝ))
    (hfg : Variation.LayerCakeAdmissible (volume : Measure ℝ) (f.1 + g.1)) :
    weakCZDirectionalOutput T θ hθ hθnorm ⟨f.1 + g.1, hfg⟩ =
      weakCZDirectionalOutput T θ hθ hθnorm f +
        weakCZDirectionalOutput T θ hθ hθnorm g := by
  let fg : Variation.LayerCakeInput (volume : Measure ℝ) := ⟨f.1 + g.1, hfg⟩
  have hdirection :
      weakCZDirectionalInput θ (f.1 + g.1) =
        weakCZDirectionalInput θ f.1 + weakCZDirectionalInput θ g.1 := by
    funext x
    simp [weakCZDirectionalInput, Complex.add_re, add_smul]
  have hinput : weakCZDirectionalL2Input θ hθ hθnorm fg =
      weakCZDirectionalL2Input θ hθ hθnorm f +
        weakCZDirectionalL2Input θ hθ hθnorm g := by
    dsimp [weakCZDirectionalL2Input]
    rw [MemLp.toLp_congr
      (weakCZDirectionalInput_memLp_one_two θ hθ hθnorm fg).2
      ((weakCZDirectionalInput_memLp_one_two θ hθ hθnorm f).2.add
        (weakCZDirectionalInput_memLp_one_two θ hθ hθnorm g).2)
      (Filter.Eventually.of_forall (fun x => congrFun hdirection x))]
    exact MemLp.toLp_add
      (weakCZDirectionalInput_memLp_one_two θ hθ hθnorm f).2
      (weakCZDirectionalInput_memLp_one_two θ hθ hθnorm g).2
  dsimp [weakCZDirectionalOutput]
  rw [hinput]
  exact weakCZLinearOutputRepresentative_add T _ _

private theorem weakCZDirectionalOutput_real_smul
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ] Lp H₂ 2 (volume : Measure ℝ))
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (c : ℝ) (hc : 0 ≤ c) (f : Variation.LayerCakeInput (volume : Measure ℝ))
    (hcf : Variation.LayerCakeAdmissible (volume : Measure ℝ) (c • f.1)) :
    weakCZDirectionalOutput T θ hθ hθnorm ⟨c • f.1, hcf⟩ =
      c • weakCZDirectionalOutput T θ hθ hθnorm f := by
  let cf : Variation.LayerCakeInput (volume : Measure ℝ) := ⟨c • f.1, hcf⟩
  have hdirection :
      weakCZDirectionalInput θ (c • f.1) =
        c • weakCZDirectionalInput θ f.1 := by
    funext x
    simp [weakCZDirectionalInput, Complex.real_smul, Complex.mul_re,
      smul_smul, mul_comm]
  have hinput : weakCZDirectionalL2Input θ hθ hθnorm cf =
      c • weakCZDirectionalL2Input θ hθ hθnorm f := by
    dsimp [weakCZDirectionalL2Input]
    rw [MemLp.toLp_congr
      (weakCZDirectionalInput_memLp_one_two θ hθ hθnorm cf).2
      ((weakCZDirectionalInput_memLp_one_two θ hθ hθnorm f).2.const_smul c)
      (Filter.Eventually.of_forall (fun x => congrFun hdirection x))]
    exact MemLp.toLp_const_smul c
      (weakCZDirectionalInput_memLp_one_two θ hθ hθnorm f).2
  dsimp [weakCZDirectionalOutput]
  rw [hinput]
  exact weakCZLinearOutputRepresentative_smul T c _

private theorem weakCZDirectionalOutput_ae_eq_L2Output
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ] Lp H₂ 2 (volume : Measure ℝ))
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) :
    weakCZDirectionalOutput T θ hθ hθnorm g =ᵐ[volume]
      (T (weakCZDirectionalL2Input θ hθ hθnorm g) : ℝ → H₂) := by
  dsimp [weakCZDirectionalOutput]
  apply AEEqFun.mk_eq_mk.mp
  calc
    AEEqFun.mk ((weakCZLinearOutputRepresentative T
        (weakCZDirectionalL2Input θ hθ hθnorm g)).1)
        ((weakCZLinearOutputRepresentative T
          (weakCZDirectionalL2Input θ hθ hθnorm g)).2.aestronglyMeasurable) =
      (T (weakCZDirectionalL2Input θ hθ hθnorm g)).1 :=
        weakCZLinearOutputRepresentative_mk T _
    _ = AEEqFun.mk
        (T (weakCZDirectionalL2Input θ hθ hθnorm g) : ℝ → H₂)
        ((T (weakCZDirectionalL2Input θ hθ hθnorm g)).1.aestronglyMeasurable) :=
          (AEEqFun.mk_coeFn _).symm

private theorem weakCZDirectionalOutput_eLpNorm_two_le
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ] Lp H₂ 2 (volume : Measure ℝ))
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    {A : ℝ} (hA : 0 ≤ A) (hT : ‖T‖ ≤ A)
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) :
    eLpNorm (weakCZDirectionalOutput T θ hθ hθnorm g) (ENNReal.ofReal 2)
        volume ≤
      ENNReal.ofReal A * eLpNorm g.1 (ENNReal.ofReal 2) volume := by
  let u := weakCZDirectionalInput θ g.1
  let hu := weakCZDirectionalInput_memLp_one_two θ hθ hθnorm g
  let input : Lp H₁ 2 volume := hu.2.toLp u
  let output : Lp H₂ 2 volume := T input
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hOutputNorm : eLpNorm (output : ℝ → H₂) (ENNReal.ofReal 2)
      volume = ENNReal.ofReal ‖output‖ := by
    rw [htwo]
    calc
      eLpNorm (output : ℝ → H₂) 2 volume = ‖output‖ₑ :=
        (Lp.enorm_def output).symm
      _ = ENNReal.ofReal ‖output‖ := (ofReal_norm output).symm
  have hInputNorm : eLpNorm (input : ℝ → H₁) (ENNReal.ofReal 2)
      volume = ENNReal.ofReal ‖input‖ := by
    rw [htwo]
    calc
      eLpNorm (input : ℝ → H₁) 2 volume = ‖input‖ₑ :=
        (Lp.enorm_def input).symm
      _ = ENNReal.ofReal ‖input‖ := (ofReal_norm input).symm
  have hOp : ‖output‖ ≤ A * ‖input‖ := by
    dsimp [output]
    calc
      ‖T input‖ ≤ ‖T‖ * ‖input‖ := T.le_opNorm input
      _ ≤ A * ‖input‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
  have hInputDom : ∀ x, ‖u x‖ ≤ ‖g.1 x‖ := by
    intro x
    change ‖Complex.re (g.1 x) • θ x‖ ≤ ‖g.1 x‖
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |Complex.re (g.1 x)| * ‖θ x‖ ≤ |Complex.re (g.1 x)| * 1 :=
        mul_le_mul_of_nonneg_left (hθnorm x) (abs_nonneg _)
      _ ≤ ‖g.1 x‖ := by
        simpa only [mul_one] using Complex.abs_re_le_norm (g.1 x)
  have hInputLp : eLpNorm (input : ℝ → H₁) (ENNReal.ofReal 2)
      volume ≤ eLpNorm g.1 (ENNReal.ofReal 2) volume := by
    rw [eLpNorm_congr_ae (by simpa [input] using hu.2.coeFn_toLp)]
    exact eLpNorm_mono_real hu.2.aestronglyMeasurable hInputDom |>.trans_eq
      (eLpNorm_norm g.1 g.2.1.aestronglyMeasurable)
  calc
    eLpNorm (weakCZDirectionalOutput T θ hθ hθnorm g)
        (ENNReal.ofReal 2) volume =
        eLpNorm (output : ℝ → H₂) (ENNReal.ofReal 2) volume :=
      eLpNorm_congr_ae
        (weakCZDirectionalOutput_ae_eq_L2Output T θ hθ hθnorm g)
    _ = ENNReal.ofReal ‖output‖ := hOutputNorm
    _ ≤ ENNReal.ofReal (A * ‖input‖) := ENNReal.ofReal_le_ofReal hOp
    _ = ENNReal.ofReal A * eLpNorm (input : ℝ → H₁)
        (ENNReal.ofReal 2) volume := by
        rw [ENNReal.ofReal_mul hA, hInputNorm]
    _ ≤ ENNReal.ofReal A * eLpNorm g.1 (ENNReal.ofReal 2) volume := by
        exact mul_le_mul_of_nonneg_left hInputLp (by positivity)

private theorem weakCZ_layerCake_memLp_one
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) :
    MemLp g.1 1 volume := by
  have hzero : MeasurableSet {x | g.1 x = (0 : ℂ)} :=
    measurableSet_eq_fun g.2.1 measurable_const
  have hsupport : {x | g.1 x ≠ 0} = {x | g.1 x = (0 : ℂ)}ᶜ := by
    ext x
    simp
  have hS : MeasurableSet {x | g.1 x ≠ 0} := hsupport ▸ hzero.compl
  have hμS : volume {x | g.1 x ≠ 0} < ∞ := by
    rw [hsupport]
    exact g.2.2.2
  exact memLp_of_bounded_finite_support g.2.1.aestronglyMeasurable
    hS g.2.2.1 hμS 1

private theorem weakCZ_layerCake_moment_one
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) :
    Variation.complexLpMoment 1 volume g.1 =
      ENNReal.ofReal (∫ x, ‖g.1 x‖ ∂volume) := by
  unfold Variation.complexLpMoment
  calc
    ∫⁻ x, (ENNReal.ofReal ‖g.1 x‖).rpow 1 ∂volume =
        ∫⁻ x, ENNReal.ofReal ‖g.1 x‖ ∂volume := by
          apply lintegral_congr_ae
          filter_upwards with x
          simp
    _ = ∫⁻ x, ‖g.1 x‖ₑ ∂volume := by
      apply lintegral_congr_ae
      filter_upwards with x
      exact ofReal_norm (g.1 x)
    _ = ENNReal.ofReal (∫ x, ‖g.1 x‖ ∂volume) :=
      (ofReal_integral_norm_eq_lintegral_enorm
        (memLp_one_iff_integrable.mp (weakCZ_layerCake_memLp_one g))).symm

private theorem weakCZ_layerCake_moment_two
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) :
    Variation.complexLpMoment 2 volume g.1 =
      eLpNorm g.1 (ENNReal.ofReal 2) volume ^ (2 : ℝ) := by
  have hp0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
  have hpTop : ENNReal.ofReal (2 : ℝ) ≠ ⊤ := by simp
  have htoReal : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by norm_num
  calc
    Variation.complexLpMoment 2 volume g.1 =
        ∫⁻ x, ‖g.1 x‖ₑ ^ (2 : ℝ) ∂volume := by
      unfold Variation.complexLpMoment
      apply lintegral_congr_ae
      filter_upwards with x
      simp [ENNReal.rpow_eq_pow]
    _ = eLpNorm g.1 (ENNReal.ofReal 2) volume ^ (2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
        g.2.1.aestronglyMeasurable, htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0),
        ENNReal.rpow_one]

private theorem weakCZDirectionalInput_integral_norm_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    (θ : ℝ → H) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) :
    ∫ x, ‖weakCZDirectionalInput θ g.1 x‖ ∂volume ≤
      ∫ x, ‖g.1 x‖ ∂volume := by
  have hu := weakCZDirectionalInput_memLp_one_two θ hθ hθnorm g
  have hg := weakCZ_layerCake_memLp_one g
  have huInt := memLp_one_iff_integrable.mp hu.1
  have hgInt := memLp_one_iff_integrable.mp hg
  apply integral_mono huInt.norm hgInt.norm
  intro x
  change ‖Complex.re (g.1 x) • θ x‖ ≤ ‖g.1 x‖
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |Complex.re (g.1 x)| * ‖θ x‖ ≤ |Complex.re (g.1 x)| * 1 :=
      mul_le_mul_of_nonneg_left (hθnorm x) (abs_nonneg _)
    _ ≤ ‖g.1 x‖ := by
      simpa only [mul_one] using Complex.abs_re_le_norm (g.1 x)

private theorem weakCZ_offSupport_nonneg_bound_from_memLp_one_two
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    (u : ℝ → H₁) (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume)
    {t : ℝ} (ht : 0 < t) :
    volume {x | t < ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖} ≤
      ENNReal.ofReal ((9 + 8 * A ^ 2 + 4 * B) *
        ((∫ x, ‖u x‖ ∂volume) / t)) := by
  letI : CompleteSpace H₁ := FiniteDimensional.complete ℝ H₁
  exact weakTypeFromOffSupport_of_nonneg T hA hB hT hOffSupport
    (memLp_one_iff_integrable.mp hu₁) hu₂ ht

private theorem weakCZ_measure_weak_bound_of_ae_eq_L2Output
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    (u : ℝ → H₁) (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume)
    {t : ℝ} (ht : 0 < t) (v : ℝ → H₂)
    (hrep : v =ᵐ[volume] (T (hu₂.toLp u) : ℝ → H₂)) :
    volume {x | t < ‖v x‖} ≤
      ENNReal.ofReal ((9 + 8 * A ^ 2 + 4 * B) *
        ((∫ x, ‖u x‖ ∂volume) / t)) := by
  have hweak := weakCZ_offSupport_nonneg_bound_from_memLp_one_two
    T hA hB hT hOffSupport u hu₁ hu₂ ht
  have hset : {x | t < ‖v x‖} =ᵐ[volume]
      {x | t < ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖} := by
    filter_upwards [hrep] with x hx
    simp [hx]
  exact (measure_mono_ae hset.le).trans hweak

private theorem weakCZDirectionalOutput_weak_one
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) {t : ℝ}
    (ht : 0 < t) :
    volume {x | t < ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖} ≤
      (ENNReal.ofReal (9 + 8 * A ^ 2 + 4 * B)).rpow 1 *
        (ENNReal.ofReal t).rpow (-1) *
        Variation.complexLpMoment 1 volume g.1 := by
  let u : ℝ → H₁ := weakCZDirectionalInput θ g.1
  let hu := weakCZDirectionalInput_memLp_one_two θ hθ hθnorm g
  have hinput := weakCZDirectionalL2Input_eq_toLp θ hθ hθnorm g hu.2
  have hTinput :
      (T (weakCZDirectionalL2Input θ hθ hθnorm g) : ℝ → H₂) =ᵐ[volume]
        (T (hu.2.toLp u) : ℝ → H₂) := by
    exact Lp.ext_iff.mp (congrArg T hinput)
  have hrepresentative : weakCZDirectionalOutput T θ hθ hθnorm g =ᵐ[volume]
      (T (hu.2.toLp u) : ℝ → H₂) := by
    exact (weakCZDirectionalOutput_ae_eq_L2Output T θ hθ hθnorm g).trans
      (by simpa [u] using hTinput)
  have hweak := weakCZ_measure_weak_bound_of_ae_eq_L2Output
    T hA hB hT hOffSupport u hu.1 hu.2 ht
    (weakCZDirectionalOutput T θ hθ hθnorm g) hrepresentative
  have hW : 0 ≤ 9 + 8 * A ^ 2 + 4 * B := by positivity
  have hInt : 0 ≤ ∫ x, ‖g.1 x‖ ∂volume :=
    integral_nonneg (fun x => norm_nonneg _)
  have hDirInt := weakCZDirectionalInput_integral_norm_le θ hθ hθnorm g
  have hReal :
      (9 + 8 * A ^ 2 + 4 * B) * ((∫ x, ‖u x‖ ∂volume) / t) ≤
        (9 + 8 * A ^ 2 + 4 * B) * ((∫ x, ‖g.1 x‖ ∂volume) / t) := by
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hDirInt ht.le) hW
  have hMoment := weakCZ_layerCake_moment_one g
  have hTarget :
      (ENNReal.ofReal (9 + 8 * A ^ 2 + 4 * B)).rpow 1 *
        (ENNReal.ofReal t).rpow (-1) *
        Variation.complexLpMoment 1 volume g.1 =
      ENNReal.ofReal
        ((9 + 8 * A ^ 2 + 4 * B) * ((∫ x, ‖g.1 x‖ ∂volume) / t)) := by
    change ENNReal.ofReal (9 + 8 * A ^ 2 + 4 * B) ^ (1 : ℝ) *
        ENNReal.ofReal t ^ (-1 : ℝ) *
        Variation.complexLpMoment 1 volume g.1 = _
    rw [ENNReal.ofReal_rpow_of_nonneg hW (by norm_num : 0 ≤ (1 : ℝ)),
      Real.rpow_one, hMoment]
    have htInv : ENNReal.ofReal t ^ (-1 : ℝ) = ENNReal.ofReal (t⁻¹) := by
      rw [ENNReal.rpow_neg,
        ENNReal.ofReal_rpow_of_nonneg ht.le (by norm_num : 0 ≤ (1 : ℝ)),
        Real.rpow_one, ENNReal.ofReal_inv_of_pos ht]
    rw [htInv]
    calc
      (ENNReal.ofReal (9 + 8 * A ^ 2 + 4 * B) * ENNReal.ofReal (t⁻¹)) *
          ENNReal.ofReal (∫ x, ‖g.1 x‖ ∂volume) =
        ENNReal.ofReal ((9 + 8 * A ^ 2 + 4 * B) * t⁻¹) *
          ENNReal.ofReal (∫ x, ‖g.1 x‖ ∂volume) := by
          rw [ENNReal.ofReal_mul hW]
      _ = ENNReal.ofReal
          ((9 + 8 * A ^ 2 + 4 * B) * t⁻¹ *
            (∫ x, ‖g.1 x‖ ∂volume)) := by
          rw [← ENNReal.ofReal_mul' hInt]
      _ = ENNReal.ofReal
          ((9 + 8 * A ^ 2 + 4 * B) *
            ((∫ x, ‖g.1 x‖ ∂volume) / t)) := by
          congr 1 <;> field_simp [ht.ne'] <;> ring
  calc
    volume {x | t < ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖} ≤
        ENNReal.ofReal
          ((9 + 8 * A ^ 2 + 4 * B) * ((∫ x, ‖u x‖ ∂volume) / t)) := hweak
    _ ≤ ENNReal.ofReal
          ((9 + 8 * A ^ 2 + 4 * B) * ((∫ x, ‖g.1 x‖ ∂volume) / t)) :=
        ENNReal.ofReal_le_ofReal hReal
    _ = (ENNReal.ofReal (9 + 8 * A ^ 2 + 4 * B)).rpow 1 *
          (ENNReal.ofReal t).rpow (-1) *
          Variation.complexLpMoment 1 volume g.1 := hTarget.symm

private theorem weakCZDirectionalOutput_weak_two
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A : ℝ} (hA : 0 ≤ A) (hT : ‖T‖ ≤ A)
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) {t : ℝ}
    (ht : 0 < t) :
    volume {x | t < ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖} ≤
      (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
        Variation.complexLpMoment 2 volume g.1 := by
  let out : ℝ → H₂ := weakCZDirectionalOutput T θ hθ hθnorm g
  have houtMeas : Measurable out :=
    weakCZDirectionalOutput_measurable T θ hθ hθnorm g
  have houtAE := weakCZDirectionalOutput_ae_eq_L2Output T θ hθ hθnorm g
  have houtL2 : MemLp out (ENNReal.ofReal 2) volume := by
    have hnormAE : ∀ᵐ x ∂volume,
        ‖(T (weakCZDirectionalL2Input θ hθ hθnorm g) : ℝ → H₂) x‖ =
          ‖out x‖ :=
      houtAE.symm.mono (fun _ hx => congrArg (fun y : H₂ => ‖y‖) hx)
    have hTmem : MemLp
        (T (weakCZDirectionalL2Input θ hθ hθnorm g) : ℝ → H₂)
        (ENNReal.ofReal 2) volume := by
      simpa using Lp.memLp (T (weakCZDirectionalL2Input θ hθ hθnorm g))
    exact hTmem.congr_norm houtMeas.aestronglyMeasurable hnormAE
  have hSqInt : Integrable (fun x => ‖out x‖ ^ 2) volume := by
    apply (memLp_two_iff_integrable_sq_norm houtMeas.aestronglyMeasurable).mp
    simpa using houtL2
  have hGmeas : Measurable (fun x => ENNReal.ofReal (‖out x‖ ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((houtMeas.norm).pow_const 2)
  have hGint :
      (∫⁻ x, ENNReal.ofReal (‖out x‖ ^ 2) ∂volume) =
        eLpNorm out (ENNReal.ofReal 2) volume ^ (2 : ℝ) := by
    have hOfRealInt :
        ENNReal.ofReal (∫ x, ‖out x‖ ^ 2 ∂volume) =
          ∫⁻ x, ENNReal.ofReal (‖out x‖ ^ 2) ∂volume :=
      ofReal_integral_eq_lintegral_ofReal hSqInt
        (ae_of_all volume (fun x => sq_nonneg (‖out x‖)))
    have hNormSq := eLpNorm_two_sq_eq_ofReal_integral_norm_sq houtL2
    calc
      (∫⁻ x, ENNReal.ofReal (‖out x‖ ^ 2) ∂volume) =
          ENNReal.ofReal (∫ x, ‖out x‖ ^ 2 ∂volume) := hOfRealInt.symm
      _ = eLpNorm out (ENNReal.ofReal 2) volume ^ 2 := hNormSq.symm
      _ = eLpNorm out (ENNReal.ofReal 2) volume ^ (2 : ℝ) := by
        rw [← ENNReal.rpow_natCast]
        norm_num
  have hOutL2 := weakCZDirectionalOutput_eLpNorm_two_le
    T θ hθ hθnorm hA hT g
  have hMoment := weakCZ_layerCake_moment_two g
  have hOutMoment :
      eLpNorm out (ENNReal.ofReal 2) volume ^ (2 : ℝ) ≤
        (ENNReal.ofReal A).rpow 2 * Variation.complexLpMoment 2 volume g.1 := by
    calc
      eLpNorm out (ENNReal.ofReal 2) volume ^ (2 : ℝ) ≤
          (ENNReal.ofReal A * eLpNorm g.1 (ENNReal.ofReal 2) volume) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hOutL2 (by norm_num)
      _ = (ENNReal.ofReal A).rpow 2 *
          (eLpNorm g.1 (ENNReal.ofReal 2) volume).rpow 2 :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = (ENNReal.ofReal A).rpow 2 *
          Variation.complexLpMoment 2 volume g.1 := by
        change (ENNReal.ofReal A).rpow 2 *
          (eLpNorm g.1 (ENNReal.ofReal 2) volume) ^ (2 : ℝ) = _
        rw [← hMoment]
  have hdenom : ENNReal.ofReal (t ^ 2) = (ENNReal.ofReal t).rpow 2 := by
    rw [← Real.rpow_natCast t 2]
    exact (ENNReal.ofReal_rpow_of_nonneg ht.le
      (by norm_num : 0 ≤ (2 : ℝ))).symm
  have hthreshold : {x | t < ‖out x‖} ⊆
      {x | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal (‖out x‖ ^ 2)} := by
    intro x hx
    change ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal (‖out x‖ ^ 2)
    apply ENNReal.ofReal_le_ofReal
    have hsum : 0 < ‖out x‖ + t :=
      add_pos (lt_trans ht hx) ht
    have hprod : 0 < (‖out x‖ - t) * (‖out x‖ + t) :=
      mul_pos (sub_pos.mpr hx) hsum
    nlinarith
  have htarget : ENNReal.ofReal (t ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ht)).ne'
  have htargetTop : ENNReal.ofReal (t ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hmarkov := MeasureTheory.meas_ge_le_lintegral_div
    (μ := volume) (f := fun x => ENNReal.ofReal (‖out x‖ ^ 2))
    hGmeas.aemeasurable htarget htargetTop
  have hlevel : volume {x | t < ‖out x‖} ≤
      ((ENNReal.ofReal A).rpow 2 * Variation.complexLpMoment 2 volume g.1) /
        ENNReal.ofReal (t ^ 2) := by
    calc
      volume {x | t < ‖out x‖} ≤
          volume {x | ENNReal.ofReal (t ^ 2) ≤
            ENNReal.ofReal (‖out x‖ ^ 2)} := measure_mono hthreshold
      _ ≤ (∫⁻ x, ENNReal.ofReal (‖out x‖ ^ 2) ∂volume) /
            ENNReal.ofReal (t ^ 2) := hmarkov
      _ ≤ ((ENNReal.ofReal A).rpow 2 *
            Variation.complexLpMoment 2 volume g.1) /
            ENNReal.ofReal (t ^ 2) := by
          rw [hGint]
          exact ENNReal.div_le_div_right hOutMoment (ENNReal.ofReal (t ^ 2))
  have hneg : (ENNReal.ofReal t).rpow (-2) =
      ((ENNReal.ofReal t).rpow 2)⁻¹ :=
    ENNReal.rpow_neg (ENNReal.ofReal t) 2
  rw [hdenom] at hlevel
  calc
    volume {x | t < ‖out x‖} ≤
        ((ENNReal.ofReal A).rpow 2 *
          Variation.complexLpMoment 2 volume g.1) /
            (ENNReal.ofReal t).rpow 2 := hlevel
    _ = (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
          Variation.complexLpMoment 2 volume g.1 := by
        rw [div_eq_mul_inv, hneg]
        ac_rfl

private def weakCZDirectionalWeakTypeOperator
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ] Lp H₂ 2 (volume : Measure ℝ))
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    (W A : ℝ)
    (hweak₁ : ∀ (g : Variation.LayerCakeInput (volume : Measure ℝ)) (t : ℝ),
      0 < t →
      volume {x | t < ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖} ≤
        (ENNReal.ofReal W).rpow 1 * (ENNReal.ofReal t).rpow (-1) *
          Variation.complexLpMoment 1 volume g.1)
    (hweak₂ : ∀ (g : Variation.LayerCakeInput (volume : Measure ℝ)) (t : ℝ),
      0 < t →
      volume {x | t < ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖} ≤
        (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
          Variation.complexLpMoment 2 volume g.1) :
    WeakTypeInterpolationOperator (volume : Measure ℝ) 1 2 W A where
  apply g x := ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖
  measurable_apply g :=
    (weakCZDirectionalOutput_measurable T θ hθ hθnorm g).norm
  nonneg_apply _ _ := norm_nonneg _
  subadditive := by
    intro f g hfg x
    rw [weakCZDirectionalOutput_add T θ hθ hθnorm f g hfg]
    exact norm_add_le _ _
  positive_homogeneous := by
    intro f c hc hcf x
    rw [weakCZDirectionalOutput_real_smul T θ hθ hθnorm c hc f hcf]
    change ‖c • weakCZDirectionalOutput T θ hθ hθnorm f x‖ =
      c * ‖weakCZDirectionalOutput T θ hθ hθnorm f x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  weak_s₀ := hweak₁
  weak_s₁ := hweak₂

private theorem weakCZDirectionalOutput_eLpNorm_interpolation
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ] Lp H₂ 2 (volume : Measure ℝ))
    (θ : ℝ → H₁) (hθ : Measurable θ) (hθnorm : ∀ x, ‖θ x‖ ≤ 1)
    {W A : ℝ} (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hweak₁ : ∀ (g : Variation.LayerCakeInput (volume : Measure ℝ)) (t : ℝ),
      0 < t →
      volume {x | t < ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖} ≤
        (ENNReal.ofReal W).rpow 1 * (ENNReal.ofReal t).rpow (-1) *
          Variation.complexLpMoment 1 volume g.1)
    (hweak₂ : ∀ (g : Variation.LayerCakeInput (volume : Measure ℝ)) (t : ℝ),
      0 < t →
      volume {x | t < ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖} ≤
        (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
          Variation.complexLpMoment 2 volume g.1)
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) :
    eLpNorm (fun x => ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖)
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal
        (weakTypeInterpolationConstant 1 p 2 *
          W ^ weakTypeInterpolationTheta0 1 p 2 *
          A ^ weakTypeInterpolationTheta1 1 p 2) *
        eLpNorm g.1 (ENNReal.ofReal p) volume := by
  exact weakTypeInterpolation
    (weakCZDirectionalWeakTypeOperator T θ hθ hθnorm W A hweak₁ hweak₂)
    (by norm_num) hp₁ hp₂ hW hA g

/-- A bounded finite-support vector input is a real directional scalarization
of a bounded finite-support complex input.  This is the source-faithful
reduction needed to apply scalar weak-type interpolation to Euclidean fibers. -/
private theorem weakCZVectorInput_scalarize
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    (f : ℝ → H) (hf : Measurable f)
    (hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hμ : volume {x | f x ≠ 0} < ∞) :
    ∃ g : Variation.LayerCakeInput (volume : Measure ℝ),
      ∃ θ : ℝ → H, Measurable θ ∧ (∀ x, ‖θ x‖ ≤ 1) ∧
        (∀ x, weakCZDirectionalInput θ g.1 x = f x) ∧
        (∀ x, ‖g.1 x‖ = ‖f x‖) := by
  classical
  let gFn : ℝ → ℂ := fun x => (‖f x‖ : ℝ)
  let θ : ℝ → H := fun x =>
    if ‖f x‖ = 0 then 0 else (‖f x‖)⁻¹ • f x
  have hgMeas : Measurable gFn := Complex.measurable_ofReal.comp hf.norm
  have hgSupport : {x | gFn x ≠ 0} = {x | f x ≠ 0} := by
    ext x
    simp [gFn]
  have hgBound : ∃ C : ℝ, ∀ x, ‖gFn x‖ ≤ C := by
    rcases hbound with ⟨C, hC⟩
    refine ⟨max C 0, ?_⟩
    intro x
    calc
      ‖gFn x‖ = ‖f x‖ := by simp [gFn]
      _ ≤ max C 0 := (hC x).trans (le_max_left C 0)
  have hgSupportFinite : volume {x | gFn x ≠ 0} < ∞ := by
    rw [hgSupport]
    exact hμ
  let g : Variation.LayerCakeInput (volume : Measure ℝ) :=
    ⟨gFn, hgMeas, hgBound, hgSupportFinite⟩
  have hzero : MeasurableSet {x | ‖f x‖ = (0 : ℝ)} :=
    measurableSet_eq_fun hf.norm measurable_const
  have hinv : Measurable (fun x => (‖f x‖)⁻¹) := hf.norm.inv
  have hθraw : Measurable (fun x => (‖f x‖)⁻¹ • f x) := hinv.smul hf
  have hθMeas : Measurable θ := by
    dsimp [θ]
    exact Measurable.ite hzero measurable_const hθraw
  have hθNorm : ∀ x, ‖θ x‖ ≤ 1 := by
    intro x
    by_cases hx : ‖f x‖ = 0
    · simp [θ, hx]
    · have hpos : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      have hθx : θ x = (‖f x‖)⁻¹ • f x := by
        dsimp [θ]
        rw [if_neg hx]
      calc
        ‖θ x‖ = ‖(‖f x‖)⁻¹ • f x‖ := congrArg norm hθx
        _ = 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
          exact inv_mul_cancel₀ (ne_of_gt hpos)
        _ ≤ 1 := le_rfl
  have hinput : ∀ x, weakCZDirectionalInput θ g.1 x = f x := by
    intro x
    by_cases hx : ‖f x‖ = 0
    · have hfx : f x = 0 := norm_eq_zero.mp hx
      simp [weakCZDirectionalInput, θ, g, gFn, hx, hfx]
    · have hpos : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      change Complex.re (Complex.ofReal (‖f x‖)) • θ x = f x
      rw [Complex.ofReal_re]
      have hθx : θ x = (‖f x‖)⁻¹ • f x := by
        dsimp [θ]
        rw [if_neg hx]
      rw [hθx]
      calc
        ‖f x‖ • ((‖f x‖)⁻¹ • f x) =
            (‖f x‖ * (‖f x‖)⁻¹) • f x := smul_smul _ _ _
        _ = f x := by rw [mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  have hnorm : ∀ x, ‖g.1 x‖ = ‖f x‖ := by
    intro x
    simp [g, gFn]
  exact ⟨g, θ, hθMeas, hθNorm, hinput, hnorm⟩

/-- The two weak endpoints give the exact interpolated estimate for every
bounded finite-support vector input.  The later extension step only needs to
extend this dense-class estimate to all of `L^p`. -/
private theorem weakCZ_finiteVectorInput_strong_lt_two
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (f : ℝ → H₁) (hf : Measurable f)
    (hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hμ : volume {x | f x ≠ 0} < ∞) :
    eLpNorm (fun x => ‖(T ((memLp_of_bounded_finite_support
        hf.aestronglyMeasurable
        (by
          have hzero : MeasurableSet {x | f x = 0} :=
            measurableSet_eq_fun hf measurable_const
          have hsupport : {x | f x ≠ 0} = {x | f x = 0}ᶜ := by
            ext x
            simp
          rw [hsupport]
          exact hzero.compl)
        hbound hμ 2).toLp f) : Lp H₂ 2 volume) x‖)
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal
        (weakTypeInterpolationConstant 1 p 2 *
          (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
          A ^ weakTypeInterpolationTheta1 1 p 2) *
        eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal p) volume := by
  classical
  have hzero : MeasurableSet {x | f x = 0} :=
    measurableSet_eq_fun hf measurable_const
  have hsupport : MeasurableSet {x | f x ≠ 0} := by
    have hset : {x | f x ≠ 0} = {x | f x = 0}ᶜ := by
      ext x
      simp
    rw [hset]
    exact hzero.compl
  let hmem₂ : MemLp f 2 volume :=
    memLp_of_bounded_finite_support hf.aestronglyMeasurable hsupport hbound hμ 2
  let f₂ : Lp H₁ 2 volume := hmem₂.toLp f
  obtain ⟨g, θ, hθ, hθnorm, hrepr, hgnorm⟩ :=
    weakCZVectorInput_scalarize f hf hbound hμ
  have hdir₂ : weakCZDirectionalL2Input θ hθ hθnorm g = f₂ := by
    apply Lp.ext
    filter_upwards [
      (weakCZDirectionalInput_memLp_one_two θ hθ hθnorm g).2.coeFn_toLp,
      hmem₂.coeFn_toLp] with x hdir hf₂
    exact hdir.trans ((hrepr x).trans hf₂.symm)
  have hTfun :
      (T (weakCZDirectionalL2Input θ hθ hθnorm g) : ℝ → H₂) =
        (T f₂ : ℝ → H₂) :=
    congrArg (fun u : Lp H₂ 2 volume => (u : ℝ → H₂)) (congrArg T hdir₂)
  have hrepresentative : weakCZDirectionalOutput T θ hθ hθnorm g =ᵐ[volume]
      (T f₂ : ℝ → H₂) := by
    filter_upwards [
      weakCZDirectionalOutput_ae_eq_L2Output T θ hθ hθnorm g] with x hx
    exact hx.trans (congrFun hTfun x)
  have hweak₁ : ∀ (g : Variation.LayerCakeInput (volume : Measure ℝ)) (t : ℝ),
      0 < t →
      volume {x | t < ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖} ≤
        (ENNReal.ofReal (9 + 8 * A ^ 2 + 4 * B)).rpow 1 *
          (ENNReal.ofReal t).rpow (-1) *
          Variation.complexLpMoment 1 volume g.1 := by
    intro g t ht
    exact weakCZDirectionalOutput_weak_one T hA hB hT hOffSupport
      θ hθ hθnorm g ht
  have hweak₂ : ∀ (g : Variation.LayerCakeInput (volume : Measure ℝ)) (t : ℝ),
      0 < t →
      volume {x | t < ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖} ≤
        (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
          Variation.complexLpMoment 2 volume g.1 := by
    intro g t ht
    exact weakCZDirectionalOutput_weak_two T hA hT θ hθ hθnorm g ht
  have hW : 0 ≤ 9 + 8 * A ^ 2 + 4 * B := by positivity
  have hinterp := weakCZDirectionalOutput_eLpNorm_interpolation
    T θ hθ hθnorm hW hA hweak₁ hweak₂ hp₁ hp₂ g
  have hinputNorm :
      eLpNorm g.1 (ENNReal.ofReal p) volume =
        eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal p) volume := by
    calc
      eLpNorm g.1 (ENNReal.ofReal p) volume =
          eLpNorm (fun x => ‖g.1 x‖) (ENNReal.ofReal p) volume :=
            (eLpNorm_norm g.1 g.2.1.aestronglyMeasurable).symm
      _ = eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal p) volume :=
        eLpNorm_congr_ae (ae_of_all volume hgnorm)
  have hrepresentativeNorm :
      (fun x => ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖) =ᵐ[volume]
        (fun x => ‖(T f₂ : ℝ → H₂) x‖) := by
    exact hrepresentative.mono (fun _ hx => congrArg norm hx)
  have houtputNorm :
      eLpNorm (fun x => ‖(T f₂ : ℝ → H₂) x‖) (ENNReal.ofReal p) volume =
        eLpNorm (fun x => ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖)
          (ENNReal.ofReal p) volume := by
    exact eLpNorm_congr_ae hrepresentativeNorm |>.symm
  calc
    eLpNorm (fun x => ‖(T f₂ : ℝ → H₂) x‖) (ENNReal.ofReal p) volume =
        eLpNorm (fun x => ‖weakCZDirectionalOutput T θ hθ hθnorm g x‖)
          (ENNReal.ofReal p) volume := houtputNorm
    _ ≤ ENNReal.ofReal
          (weakTypeInterpolationConstant 1 p 2 *
            (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
            A ^ weakTypeInterpolationTheta1 1 p 2) *
          eLpNorm g.1 (ENNReal.ofReal p) volume := hinterp
    _ = ENNReal.ofReal
          (weakTypeInterpolationConstant 1 p 2 *
            (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
            A ^ weakTypeInterpolationTheta1 1 p 2) *
          eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal p) volume := by
        rw [hinputNorm]

/-- The finite-input interpolated bound gives target `L^p` membership for
the original `L²` output.  This is the membership step needed to define the
operator on the bounded finite-support domain before completing it. -/
private theorem weakCZ_finiteSupport_output_memLp
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (d : weakCZBoundedFiniteSupportSubmodule (H := H₁)) :
    MemLp
      ((T ((memLp_of_bounded_finite_support d.2.1.aestronglyMeasurable
        (by
          have hz : MeasurableSet {x | d.1 x = 0} :=
            measurableSet_eq_fun d.2.1 measurable_const
          have hs : {x | d.1 x ≠ 0} = {x | d.1 x = 0}ᶜ := by
            ext x
            simp
          rw [hs]
          exact hz.compl)
        d.2.2.1 d.2.2.2 2).toLp d.1) : ℝ → H₂))
      (ENNReal.ofReal p) volume := by
  classical
  have hzero : MeasurableSet {x | d.1 x = 0} :=
    measurableSet_eq_fun d.2.1 measurable_const
  have hsupport : MeasurableSet {x | d.1 x ≠ 0} := by
    have hset : {x | d.1 x ≠ 0} = {x | d.1 x = 0}ᶜ := by
      ext x
      simp
    rw [hset]
    exact hzero.compl
  let hmem₂ : MemLp d.1 2 volume :=
    memLp_of_bounded_finite_support d.2.1.aestronglyMeasurable hsupport
      d.2.2.1 d.2.2.2 2
  let input₂ : Lp H₁ 2 volume := hmem₂.toLp d.1
  let output₂ : Lp H₂ 2 volume := T input₂
  have hstrong := weakCZ_finiteVectorInput_strong_lt_two T hA hB hT
    hOffSupport hp₁ hp₂ d.1 d.2.1 d.2.2.1 d.2.2.2
  have hstrong' :
      eLpNorm (fun x => ‖(output₂ : ℝ → H₂) x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal
          (weakTypeInterpolationConstant 1 p 2 *
            (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
            A ^ weakTypeInterpolationTheta1 1 p 2) *
          eLpNorm (fun x => ‖d.1 x‖) (ENNReal.ofReal p) volume := by
    exact hstrong
  have hsourceMem : MemLp d.1 (ENNReal.ofReal p) volume :=
    memLp_of_bounded_finite_support d.2.1.aestronglyMeasurable hsupport
      d.2.2.1 d.2.2.2 (ENNReal.ofReal p)
  have hsourceNorm : MemLp (fun x => ‖d.1 x‖) (ENNReal.ofReal p) volume :=
    hsourceMem.norm
  have hfinite :
      ENNReal.ofReal
          (weakTypeInterpolationConstant 1 p 2 *
            (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
            A ^ weakTypeInterpolationTheta1 1 p 2) *
        eLpNorm (fun x => ‖d.1 x‖) (ENNReal.ofReal p) volume < ∞ := by
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hsourceNorm.eLpNorm_ne_top)
  have hnormMem : MemLp (fun x => ‖(output₂ : ℝ → H₂) x‖)
      (ENNReal.ofReal p) volume := by
    rw [memLp_iff]
    exact hstrong'.trans_lt hfinite
  exact (memLp_norm_iff (Lp.memLp output₂).aestronglyMeasurable).mp hnormMem

/-- The original `L²` operator, viewed on bounded finite-support inputs as
a linear map into target `L^p`. -/
private noncomputable def weakCZ_finiteSupportLpMap
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) :
    weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let source₂ : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ 2 volume := weakCZBoundedFiniteSupport_toLp 2
  let outMem : ∀ d : weakCZBoundedFiniteSupportSubmodule (H := H₁),
      MemLp (T (source₂ d) : ℝ → H₂) (ENNReal.ofReal p) volume := by
    intro d
    simpa [source₂, weakCZBoundedFiniteSupport_toLp] using
      (weakCZ_finiteSupport_output_memLp T hA hB hT hOffSupport hp₁ hp₂ d)
  let out : weakCZBoundedFiniteSupportSubmodule (H := H₁) →
      Lp H₂ (ENNReal.ofReal p) volume := fun d =>
        (outMem d).toLp (T (source₂ d) : ℝ → H₂)
  refine {
    toFun := out
    map_add' := by
      intro d e
      have hTadd : T (source₂ (d + e)) = T (source₂ d) + T (source₂ e) := by
        rw [map_add source₂, map_add T]
      apply Lp.ext
      filter_upwards [(outMem (d + e)).coeFn_toLp,
        (outMem d).coeFn_toLp, (outMem e).coeFn_toLp,
        Lp.ext_iff.mp hTadd,
        Lp.coeFn_add (T (source₂ d)) (T (source₂ e)),
        Lp.coeFn_add (out d) (out e)] with
        x hsum hd he hT hadd houtAdd
      calc
        out (d + e) x = T (source₂ (d + e)) x := hsum
        _ = (T (source₂ d) + T (source₂ e)) x := hT
        _ = T (source₂ d) x + T (source₂ e) x := hadd
        _ = out d x + out e x := by rw [← hd, ← he]
        _ = (out d + out e) x := houtAdd.symm
    map_smul' := by
      intro c d
      have hTsmul : T (source₂ (c • d)) = c • T (source₂ d) := by
        rw [map_smul source₂, map_smul T]
      apply Lp.ext
      filter_upwards [(outMem (c • d)).coeFn_toLp,
        (outMem d).coeFn_toLp, Lp.ext_iff.mp hTsmul,
        Lp.coeFn_smul c (T (source₂ d)),
        Lp.coeFn_smul c (out d)] with x hscaled hd hT hsmul houtSmul
      calc
        out (c • d) x = T (source₂ (c • d)) x := hscaled
        _ = (c • T (source₂ d)) x := hT
        _ = c • T (source₂ d) x := hsmul
        _ = c • out d x := by rw [hd]
        _ = (c • out d) x := houtSmul.symm
  }

/-- The operator on the bounded finite-support domain obeys the exact
interpolated `L^p` operator bound. -/
private theorem weakCZ_finiteSupportLpMap_norm_le
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (d : weakCZBoundedFiniteSupportSubmodule (H := H₁)) :
    ‖weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂ d‖ ≤
      (weakTypeInterpolationConstant 1 p 2 *
        (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
        A ^ weakTypeInterpolationTheta1 1 p 2) *
      ‖weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p) d‖ := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal p
  letI : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let source₂ : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ 2 volume := weakCZBoundedFiniteSupport_toLp 2
  let sourceP : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ P volume := weakCZBoundedFiniteSupport_toLp P
  let outMem : ∀ d : weakCZBoundedFiniteSupportSubmodule (H := H₁),
      MemLp (T (source₂ d) : ℝ → H₂) P volume := by
    intro d
    simpa [P, source₂, weakCZBoundedFiniteSupport_toLp] using
      (weakCZ_finiteSupport_output_memLp T hA hB hT hOffSupport hp₁ hp₂ d)
  have houtCoe :
      (weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂ d : ℝ → H₂) =ᵐ[volume]
        (T (source₂ d) : ℝ → H₂) := by
    change ((outMem d).toLp (T (source₂ d) : ℝ → H₂) : ℝ → H₂) =ᵐ[volume]
      (T (source₂ d) : ℝ → H₂)
    exact (outMem d).coeFn_toLp
  have hsourceCoe : (sourceP d : ℝ → H₁) =ᵐ[volume] d.1 := by
    let hmemP : MemLp d.1 P volume :=
      memLp_of_bounded_finite_support d.2.1.aestronglyMeasurable
        (by
          have hz : MeasurableSet {x | d.1 x = 0} :=
            measurableSet_eq_fun d.2.1 measurable_const
          have hs : {x | d.1 x ≠ 0} = {x | d.1 x = 0}ᶜ := by
            ext x
            simp
          rw [hs]
          exact hz.compl)
        d.2.2.1 d.2.2.2 P
    change (hmemP.toLp d.1 : ℝ → H₁) =ᵐ[volume] d.1
    exact hmemP.coeFn_toLp
  let C : ℝ := weakTypeInterpolationConstant 1 p 2 *
      (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
      A ^ weakTypeInterpolationTheta1 1 p 2
  have hC : 0 ≤ C := by
    dsimp [C, weakTypeInterpolationConstant, weakTypeInterpolationTheta0,
      weakTypeInterpolationTheta1]
    positivity
  have hstrong := weakCZ_finiteVectorInput_strong_lt_two
    T hA hB hT hOffSupport hp₁ hp₂ d.1 d.2.1 d.2.2.1 d.2.2.2
  have hstrong' :
      eLpNorm (fun x => ‖(T (source₂ d) : ℝ → H₂) x‖) P volume ≤
        ENNReal.ofReal C * eLpNorm (fun x => ‖d.1 x‖) P volume := by
    simpa [P, C, source₂, weakCZBoundedFiniteSupport_toLp] using hstrong
  have hsourcePNorm : MemLp (fun x => ‖(sourceP d : ℝ → H₁) x‖) P volume :=
    (Lp.memLp (sourceP d)).norm
  have hfiniteP :
      ENNReal.ofReal C * eLpNorm (fun x => ‖(sourceP d : ℝ → H₁) x‖) P volume < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hsourcePNorm.eLpNorm_ne_top)
  have hfinitePVector :
      ENNReal.ofReal C * eLpNorm (sourceP d : ℝ → H₁) P volume < ∞ := by
    rw [← eLpNorm_norm (sourceP d : ℝ → H₁)
      (Lp.memLp (sourceP d)).aestronglyMeasurable]
    exact hfiniteP
  have hnormineq :
      eLpNorm (weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂ d :
        ℝ → H₂) P volume ≤ ENNReal.ofReal C * eLpNorm (sourceP d : ℝ → H₁) P volume := by
    calc
      eLpNorm (weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂ d :
          ℝ → H₂) P volume = eLpNorm (T (source₂ d) : ℝ → H₂) P volume :=
        eLpNorm_congr_ae houtCoe
      _ = eLpNorm (fun x => ‖(T (source₂ d) : ℝ → H₂) x‖) P volume := by
        exact (eLpNorm_norm (T (source₂ d) : ℝ → H₂)
          (Lp.memLp (T (source₂ d))).aestronglyMeasurable).symm
      _ ≤ ENNReal.ofReal C * eLpNorm (fun x => ‖d.1 x‖) P volume := hstrong'
      _ = ENNReal.ofReal C * eLpNorm (sourceP d : ℝ → H₁) P volume := by
        congr 1
        calc
          eLpNorm (fun x => ‖d.1 x‖) P volume =
              eLpNorm (fun x => ‖(sourceP d : ℝ → H₁) x‖) P volume :=
            eLpNorm_congr_ae
              (hsourceCoe.symm.mono (fun x hx => congrArg norm hx))
          _ = eLpNorm (sourceP d : ℝ → H₁) P volume :=
            eLpNorm_norm (sourceP d : ℝ → H₁)
              (Lp.memLp (sourceP d)).aestronglyMeasurable
  calc
    ‖weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂ d‖ =
        (eLpNorm (weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂ d :
          ℝ → H₂) P volume).toReal := by rw [Lp.norm_def]
    _ ≤ (ENNReal.ofReal C * eLpNorm (sourceP d : ℝ → H₁) P volume).toReal :=
      ENNReal.toReal_mono hfinitePVector.ne hnormineq
    _ = C * ‖sourceP d‖ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ← Lp.norm_def]
    _ = C * ‖weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p) d‖ := rfl

/-- The p<2 estimate extends uniquely from bounded finite-support inputs
to the full `L^p` space. -/
private noncomputable def weakCZ_LpExtension_lt_two
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  exact (weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂).extendOfNorm
    (weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p))

/-- The extension agrees with the original `L²` operator on the dense
bounded finite-support domain, and has the exact p<2 norm bound. -/
private theorem weakCZ_LpExtension_lt_two_agrees_and_bounded
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    ∃ extension : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ),
      (∀ d : weakCZBoundedFiniteSupportSubmodule (H := H₁),
        extension (weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p) d) =
          weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂ d) ∧
      (∀ f, ‖extension f‖ ≤
        (weakTypeInterpolationConstant 1 p 2 *
          (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
          A ^ weakTypeInterpolationTheta1 1 p 2) * ‖f‖) := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let e : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ (ENNReal.ofReal p) volume :=
    weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p)
  let S := weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂
  let C : ℝ := weakTypeInterpolationConstant 1 p 2 *
      (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
      A ^ weakTypeInterpolationTheta1 1 p 2
  have hdense : DenseRange e := by
    simpa [e] using
      (weakCZBoundedFiniteSupport_denseRange (H := H₁)
        (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top)
  have hbound : ∀ d, ‖S d‖ ≤ C * ‖e d‖ := by
    intro d
    exact weakCZ_finiteSupportLpMap_norm_le T hA hB hT hOffSupport hp₁ hp₂ d
  let extension := S.extendOfNorm e
  refine ⟨extension, ?_, ?_⟩
  · intro d
    exact LinearMap.extendOfNorm_eq hdense ⟨C, hbound⟩ d
  · intro f
    exact LinearMap.norm_extendOfNorm_apply_le hdense C hbound f

private theorem weakCZ_finiteSupportLpMap_coeFn_lt_two
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : ‖T‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (d : weakCZBoundedFiniteSupportSubmodule (H := H₁)) :
    (weakCZ_finiteSupportLpMap T hA hB hT hOffSupport hp₁ hp₂ d :
      ℝ → H₂) =ᵐ[volume]
      (T (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂) := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal p
  letI : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let source₂ : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ 2 volume := weakCZBoundedFiniteSupport_toLp 2
  let outMem : ∀ d : weakCZBoundedFiniteSupportSubmodule (H := H₁),
      MemLp (T (source₂ d) : ℝ → H₂) P volume := by
    intro d
    simpa [P, source₂, weakCZBoundedFiniteSupport_toLp] using
      (weakCZ_finiteSupport_output_memLp T hA hB hT hOffSupport hp₁ hp₂ d)
  change ((outMem d).toLp (T (source₂ d) : ℝ → H₂) : ℝ → H₂) =ᵐ[volume]
    (T (source₂ d) : ℝ → H₂)
  exact (outMem d).coeFn_toLp

/-- The `p=2` branch of `lj:weak-cz` is exactly the original operator norm
bound, expressed in the `eLpNorm` convention used by interpolation. -/
private theorem weakCZ_L2_operator_eLpNorm_le
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A : ℝ} (hA : 0 ≤ A) (hT : ‖T‖ ≤ A)
    (f : Lp H₁ 2 (volume : Measure ℝ)) :
    eLpNorm (T f : ℝ → H₂) (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal A * eLpNorm (f : ℝ → H₁) (ENNReal.ofReal 2) volume := by
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hnormT : eLpNorm (T f : ℝ → H₂) (ENNReal.ofReal 2) volume =
      ENNReal.ofReal ‖T f‖ := by
    rw [htwo]
    calc
      eLpNorm (T f : ℝ → H₂) 2 volume = ‖T f‖ₑ :=
        (Lp.enorm_def (T f)).symm
      _ = ENNReal.ofReal ‖T f‖ := (ofReal_norm (T f)).symm
  have hnormF : eLpNorm (f : ℝ → H₁) (ENNReal.ofReal 2) volume =
      ENNReal.ofReal ‖f‖ := by
    rw [htwo]
    calc
      eLpNorm (f : ℝ → H₁) 2 volume = ‖f‖ₑ := (Lp.enorm_def f).symm
      _ = ENNReal.ofReal ‖f‖ := (ofReal_norm f).symm
  have hbound : ‖T f‖ ≤ A * ‖f‖ := by
    calc
      ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
      _ ≤ A * ‖f‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
  calc
    eLpNorm (T f : ℝ → H₂) (ENNReal.ofReal 2) volume =
        ENNReal.ofReal ‖T f‖ := hnormT
    _ ≤ ENNReal.ofReal (A * ‖f‖) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal A * eLpNorm (f : ℝ → H₁)
        (ENNReal.ofReal 2) volume := by rw [ENNReal.ofReal_mul hA, hnormF]

/-- Hölder's estimate for the real inner-product pairing on finite-vector
`Lᵖ` spaces. This is the real-fiber counterpart needed to dualize the
real-linear Calderón–Zygmund operator. -/
private theorem weakCZ_norm_integral_real_inner_le_lpNorm_mul_lpNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : ℝ → H} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    ‖∫ x, inner ℝ (f x) (g x) ∂volume‖ ≤
      lpNorm f (ENNReal.ofReal p) volume *
        lpNorm g (ENNReal.ofReal q) volume := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 :=
    hpq.ennrealOfReal
  have hprod : Integrable (fun x => ‖f x‖ * ‖g x‖) volume := by
    change Integrable ((fun x => ‖f x‖) * (fun x => ‖g x‖)) volume
    exact hf.norm.integrable_mul hg.norm
  have hinner : Integrable (fun x => inner ℝ (f x) (g x)) volume :=
    hprod.mono'
      (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => norm_inner_le_norm (f x) (g x))
  calc
    ‖∫ x, inner ℝ (f x) (g x) ∂volume‖ ≤
        ∫ x, ‖inner ℝ (f x) (g x)‖ ∂volume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂volume :=
      integral_mono_ae hinner.norm hprod
        (Filter.Eventually.of_forall fun x => norm_inner_le_norm (f x) (g x))
    _ ≤ (∫ x, ‖f x‖ ^ p ∂volume) ^ (1 / p) *
          (∫ x, ‖g x‖ ^ q ∂volume) ^ (1 / q) :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq hf hg
    _ = lpNorm f (ENNReal.ofReal p) volume *
          lpNorm g (ENNReal.ofReal q) volume := by
      rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
            (ENNReal.ofReal_ne_zero_iff.mpr hpq.pos) (by simp)
            hf.aestronglyMeasurable,
          MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
            (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos) (by simp)
            hg.aestronglyMeasurable]
      simp [ENNReal.toReal_ofReal hpq.pos.le,
        ENNReal.toReal_ofReal hpq.symm.pos.le]

/-- The real-inner-product version of the pointwise norming identity. -/
private theorem weakCZ_inner_real_lpNormingVector_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {p : ℝ} (hp : 1 < p) (v : H) :
    inner ℝ v (lpNormingVector p v) = ‖v‖ ^ p := by
  by_cases hv : ‖v‖ = 0
  · have hv0 : v = 0 := norm_eq_zero.mp hv
    simp [hv0, lpNormingVector, Real.zero_rpow (lt_trans zero_lt_one hp).ne']
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    rw [lpNormingVector, inner_smul_right, inner_self_eq_norm_sq_to_K]
    have hreal :
        (‖v‖ ^ (p - 1)) / ‖v‖ * ‖v‖ ^ 2 = ‖v‖ ^ p := by
      calc
        (‖v‖ ^ (p - 1)) / ‖v‖ * ‖v‖ ^ 2 =
            ‖v‖ ^ (p - 1) * ‖v‖ := by field_simp
        _ = ‖v‖ ^ (p - 1) * ‖v‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = ‖v‖ ^ ((p - 1) + 1) :=
          (Real.rpow_add hvpos (p - 1) 1).symm
        _ = ‖v‖ ^ p := by ring_nf
    norm_cast

/-- The normalized `Lᵖ` norming function attains the norm in the real
inner-product pairing. -/
private theorem weakCZ_integral_inner_real_normalizedLpNormingFunction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : ℝ → H} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hpos : 0 < lpNorm f (ENNReal.ofReal p) volume) :
    (∫ x, inner ℝ (f x)
      (normalizedLpNormingFunction (μ := volume) p f x) ∂volume) =
      lpNorm f (ENNReal.ofReal p) volume := by
  let L : ℝ := lpNorm f (ENNReal.ofReal p) volume
  have hpoint (x : ℝ) :
      inner ℝ (f x) (normalizedLpNormingFunction (μ := volume) p f x) =
        L ^ (1 - p) * ‖f x‖ ^ p := by
    simp only [normalizedLpNormingFunction, Pi.smul_apply]
    rw [inner_smul_right, weakCZ_inner_real_lpNormingVector_self hpq.lt]
  calc
    (∫ x, inner ℝ (f x)
        (normalizedLpNormingFunction (μ := volume) p f x) ∂volume) =
        ∫ x, L ^ (1 - p) * ‖f x‖ ^ p ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = L ^ (1 - p) * (∫ x, ‖f x‖ ^ p ∂volume) := by
      rw [integral_const_mul]
    _ = L := by
      rw [integral_norm_rpow_eq_lpNorm_rpow hpq.pos hf]
      dsimp [L]
      rw [← Real.rpow_add hpos]
      rw [show (1 - p) + p = 1 by ring, Real.rpow_one]

/-- Pairing values in the real finite-vector `Lᵖ` duality formula. -/
private def weakCZRealLpDualPairingValues
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (q : ℝ) (f : ℝ → H) : Set ℝ :=
  {a | ∃ g : ℝ → H,
    MemLp g (ENNReal.ofReal q) volume ∧
    lpNorm g (ENNReal.ofReal q) volume ≤ 1 ∧
    a = ‖∫ x, inner ℝ (f x) (g x) ∂volume‖}

/-- Real finite-vector `Lᵖ` duality as the supremum of integral pairings. -/
private theorem weakCZ_lpNorm_eq_sSup_realLpDualPairingValues
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : ℝ → H} (hf : MemLp f (ENNReal.ofReal p) volume) :
    lpNorm f (ENNReal.ofReal p) volume =
      sSup (weakCZRealLpDualPairingValues q f) := by
  have hupper : ∀ a ∈ weakCZRealLpDualPairingValues q f,
      a ≤ lpNorm f (ENNReal.ofReal p) volume := by
    rintro a ⟨g, hg, hgOne, rfl⟩
    calc
      ‖∫ x, inner ℝ (f x) (g x) ∂volume‖ ≤
          lpNorm f (ENNReal.ofReal p) volume *
            lpNorm g (ENNReal.ofReal q) volume :=
        weakCZ_norm_integral_real_inner_le_lpNorm_mul_lpNorm hpq hf hg
      _ ≤ lpNorm f (ENNReal.ofReal p) volume * 1 :=
        mul_le_mul_of_nonneg_left hgOne lpNorm_nonneg
      _ = lpNorm f (ENNReal.ofReal p) volume := by ring
  have hzeroMem : 0 ∈ weakCZRealLpDualPairingValues q f := by
    refine ⟨fun _ => 0, MemLp.zero', by simp, ?_⟩
    simp
  have hnonempty : (weakCZRealLpDualPairingValues q f).Nonempty :=
    ⟨0, hzeroMem⟩
  have hbdd : BddAbove (weakCZRealLpDualPairingValues q f) :=
    ⟨lpNorm f (ENNReal.ofReal p) volume, hupper⟩
  apply le_antisymm
  · by_cases hzero : lpNorm f (ENNReal.ofReal p) volume = 0
    · rw [hzero]
      exact le_csSup hbdd hzeroMem
    · have hpos : 0 < lpNorm f (ENNReal.ofReal p) volume :=
        lt_of_le_of_ne lpNorm_nonneg (Ne.symm hzero)
      have hpair : lpNorm f (ENNReal.ofReal p) volume ∈
          weakCZRealLpDualPairingValues q f := by
        refine ⟨normalizedLpNormingFunction (μ := volume) p f,
          memLp_normalizedLpNormingFunction hpq hf, ?_, ?_⟩
        · rw [lpNorm_normalizedLpNormingFunction hpq hf hpos]
        · rw [weakCZ_integral_inner_real_normalizedLpNormingFunction
            hpq hf hpos]
          exact (abs_of_nonneg
            (lpNorm_nonneg : 0 ≤ lpNorm f (ENNReal.ofReal p) volume)).symm.trans
              (Real.norm_eq_abs _).symm
      exact le_csSup hbdd hpair
  · exact csSup_le hnonempty hupper

/-- The real L² adjoint identity written for function representatives, rather
than the quotient-space inner products. -/
private theorem weakCZ_adjoint_real_integral_pairing
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [CompleteSpace H₁] [CompleteSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {f : ℝ → H₁} {g : ℝ → H₂}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ x, inner ℝ ((T (hf.toLp f) : Lp H₂ 2 volume) x) (g x) ∂volume) =
      ∫ x, inner ℝ (f x)
        ((T.adjoint (hg.toLp g) : Lp H₁ 2 volume) x) ∂volume := by
  letI : InnerProductSpace ℝ (Lp H₁ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  letI : InnerProductSpace ℝ (Lp H₂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  let f₂ : Lp H₁ 2 volume := hf.toLp f
  let g₂ : Lp H₂ 2 volume := hg.toLp g
  have hadjLp :
      (∫ x, inner ℝ (f₂ x)
        ((T.adjoint g₂ : Lp H₁ 2 volume) x) ∂volume) =
      ∫ x, inner ℝ ((T f₂ : Lp H₂ 2 volume) x) (g₂ x) ∂volume := by
    calc
      _ = inner ℝ f₂ (T.adjoint g₂) :=
        (MeasureTheory.L2.inner_def _ _).symm
      _ = inner ℝ (T f₂) g₂ :=
        ContinuousLinearMap.adjoint_inner_right T f₂ g₂
      _ = _ := MeasureTheory.L2.inner_def _ _
  calc
    (∫ x, inner ℝ ((T f₂ : Lp H₂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ ((T f₂ : Lp H₂ 2 volume) x) (g₂ x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [← hx]
    _ = ∫ x, inner ℝ (f₂ x)
        ((T.adjoint g₂ : Lp H₁ 2 volume) x) ∂volume := hadjLp.symm
    _ = ∫ x, inner ℝ (f x)
        ((T.adjoint g₂ : Lp H₁ 2 volume) x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]

/-- The adjoint identity for arbitrary quotient-space `L²` inputs. -/
private theorem weakCZ_adjoint_Lp_integral_pairing
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [CompleteSpace H₁] [CompleteSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (f : Lp H₁ 2 (volume : Measure ℝ))
    (g : Lp H₂ 2 (volume : Measure ℝ)) :
    (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
      ∫ x, inner ℝ (f x) ((T.adjoint g : Lp H₁ 2 volume) x) ∂volume := by
  letI : InnerProductSpace ℝ (Lp H₁ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  letI : InnerProductSpace ℝ (Lp H₂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  calc
    (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
        inner ℝ (T f) g := (MeasureTheory.L2.inner_def _ _).symm
    _ = inner ℝ f (T.adjoint g) :=
      (ContinuousLinearMap.adjoint_inner_right T f g).symm
    _ = ∫ x, inner ℝ (f x) ((T.adjoint g : Lp H₁ 2 volume) x) ∂volume :=
      MeasureTheory.L2.inner_def _ _

/-- If a bounded finite-support function is normed by the standard real
`Lᵖ` test function, that test remains bounded with finite-measure support
when `p>2`. -/
private noncomputable def weakCZ_normalizedLpNormingFunction_mem_boundedFiniteSupport
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    {p : ℝ} (hp : 2 < p)
    (d : weakCZBoundedFiniteSupportSubmodule (H := H)) :
    weakCZBoundedFiniteSupportSubmodule (H := H) := by
  classical
  letI : MeasurableSMul₂ ℝ H := ⟨continuous_smul.measurable⟩
  let f : ℝ → H := d
  let g : ℝ → H := normalizedLpNormingFunction (μ := volume) p f
  have hfMeas : Measurable f := d.2.1
  have hnorm : Measurable (fun x => ‖f x‖) := hfMeas.norm
  have hcoeff : Measurable (fun x => (‖f x‖ ^ (p - 1)) / ‖f x‖) :=
    (hnorm.pow_const (p - 1)).div hnorm
  have hvector : Measurable (fun x => lpNormingVector p (f x)) := by
    change Measurable
      (fun x => ((‖f x‖ ^ (p - 1)) / ‖f x‖) • f x)
    exact hcoeff.smul hfMeas
  have hgMeas : Measurable g := by
    dsimp [g, normalizedLpNormingFunction]
    exact measurable_const.smul hvector
  let C : ℝ := Classical.choose d.2.2.1
  have hC : ∀ x, ‖f x‖ ≤ C := Classical.choose_spec d.2.2.1
  let C' : ℝ := max C 0
  have hC'nonneg : 0 ≤ C' := le_max_right C 0
  have hC' (x : ℝ) : ‖f x‖ ≤ C' :=
    (hC x).trans (le_max_left C 0)
  let L : ℝ := lpNorm f (ENNReal.ofReal p) volume
  have hp1 : 1 < p := by linarith
  have hgBound : ∀ x, ‖g x‖ ≤ ‖L ^ (1 - p)‖ * C' ^ (p - 1) := by
    intro x
    calc
      ‖g x‖ = ‖L ^ (1 - p)‖ * ‖lpNormingVector p (f x)‖ := by
        change ‖L ^ (1 - p) • lpNormingVector p (f x)‖ = _
        rw [norm_smul]
      _ = ‖L ^ (1 - p)‖ * ‖f x‖ ^ (p - 1) := by
        rw [norm_lpNormingVector hp1]
      _ ≤ ‖L ^ (1 - p)‖ * C' ^ (p - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hC' x)
            (by linarith : 0 ≤ p - 1)) (norm_nonneg _)
  have hzeroVector : lpNormingVector p (0 : H) = 0 := by
    simp [lpNormingVector, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  have hsupport : {x | g x ≠ 0} ⊆ {x | f x ≠ 0} := by
    intro x hx
    by_contra hfx
    have hfx0 : f x = 0 := not_ne_iff.mp hfx
    apply hx
    simp [g, normalizedLpNormingFunction, hfx0, hzeroVector]
  have hμ : volume {x | g x ≠ 0} < ∞ :=
    (measure_mono hsupport).trans_lt d.2.2.2
  exact ⟨g, hgMeas, ⟨‖L ^ (1 - p)‖ * C' ^ (p - 1), hgBound⟩, hμ⟩

/-- The output truncated to a bounded interval and bounded amplitude is a
bounded measurable function with finite-measure support. -/
private noncomputable def weakCZ_boundedSupportTruncation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    (u : ℝ → H) (hu : Measurable u) (n : ℕ) :
    weakCZBoundedFiniteSupportSubmodule (H := H) := by
  classical
  let N : ℝ := n
  let E : Set ℝ := Set.Icc (-N) N ∩ {x | ‖u x‖ ≤ N}
  let v : ℝ → H := fun x => if x ∈ E then u x else 0
  have hE : MeasurableSet E :=
    measurableSet_Icc.inter (measurableSet_le hu.norm measurable_const)
  have hvMeas : Measurable v := by
    dsimp [v]
    exact Measurable.ite hE hu measurable_const
  have hvBound : ∀ x, ‖v x‖ ≤ N := by
    intro x
    by_cases hx : x ∈ E
    · simpa [v, hx] using hx.2
    · simp [v, hx, N]
  have hsupport : {x | v x ≠ 0} ⊆ Set.Icc (-N) N := by
    intro x hx
    by_cases hxe : x ∈ E
    · exact hxe.1
    · simp [v, hxe] at hx
  have hμIcc : volume (Set.Icc (-N) N) < ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hμ : volume {x | v x ≠ 0} < ∞ :=
    (measure_mono hsupport).trans_lt hμIcc
  exact ⟨v, hvMeas, ⟨N, hvBound⟩, hμ⟩

private theorem weakCZ_boundedSupportTruncation_eq_of_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    (u : ℝ → H) (hu : Measurable u) (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ∩ {x | ‖u x‖ ≤ n}) :
    (weakCZ_boundedSupportTruncation u hu n : ℝ → H) x = u x := by
  classical
  change (if x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ∩
      {x | ‖u x‖ ≤ n} then u x else 0) = u x
  simp [hx]

private theorem weakCZ_boundedSupportTruncation_eq_zero_of_not_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    (u : ℝ → H) (hu : Measurable u) (n : ℕ) (x : ℝ)
    (hx : x ∉ Set.Icc (-(n : ℝ)) (n : ℝ) ∩ {x | ‖u x‖ ≤ n}) :
    (weakCZ_boundedSupportTruncation u hu n : ℝ → H) x = 0 := by
  classical
  change (if x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ∩
      {x | ‖u x‖ ≤ n} then u x else 0) = 0
  simp [hx]

private theorem weakCZ_boundedSupportTruncation_eventually_eq
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    (u : ℝ → H) (hu : Measurable u) (x : ℝ) :
    (fun n : ℕ => (weakCZ_boundedSupportTruncation u hu n : ℝ → H) x) =ᶠ[atTop]
      fun _ => u x := by
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt |x|
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt ‖u x‖
  let n₀ : ℕ := max n₁ n₂
  have hn₀x : |x| ≤ (n₀ : ℝ) := by
    dsimp [n₀]
    exact le_trans hn₁.le (by exact_mod_cast Nat.le_max_left n₁ n₂)
  have hn₀u : ‖u x‖ ≤ (n₀ : ℝ) := by
    dsimp [n₀]
    exact le_trans hn₂.le (by exact_mod_cast Nat.le_max_right n₁ n₂)
  have htail : ∀ n, n₀ ≤ n →
      (weakCZ_boundedSupportTruncation u hu n : ℝ → H) x = u x := by
    intro n hn
    apply weakCZ_boundedSupportTruncation_eq_of_mem u hu n x
    constructor
    · constructor
      · have hcast : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hleft : -|x| ≤ x := neg_abs_le x
        linarith
      · have hcast : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hright : x ≤ |x| := le_abs_self x
        linarith
    · have hcast : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact hn₀u.trans hcast
  exact Filter.eventually_atTop.2 ⟨n₀, htail⟩

/-- The dense-domain embedding preserves the `lpNorm` of its represented
bounded finite-support function. -/
private theorem weakCZBoundedFiniteSupport_toLp_norm
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    (p : ℝ≥0∞) (d : weakCZBoundedFiniteSupportSubmodule (H := H)) :
    ‖weakCZBoundedFiniteSupport_toLp (H := H) p d‖ = lpNorm d.1 p volume := by
  classical
  have hmem : MemLp d.1 p volume :=
    memLp_of_bounded_finite_support d.2.1.aestronglyMeasurable
      (by
        have hz : MeasurableSet {x | d.1 x = 0} :=
          measurableSet_eq_fun d.2.1 measurable_const
        have hs : {x | d.1 x ≠ 0} = {x | d.1 x = 0}ᶜ := by
          ext x
          simp
        rw [hs]
        exact hz.compl)
      d.2.2.1 d.2.2.2 p
  change ‖hmem.toLp d.1‖ = lpNorm d.1 p volume
  rw [Lp.norm_def]
  change (eLpNorm (hmem.toLp d.1 : ℝ → H) p volume).toReal =
    (eLpNorm d.1 p volume).toReal
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae hmem.coeFn_toLp)

/-- The dense-domain embedding represents its defining function almost
everywhere. -/
private theorem weakCZBoundedFiniteSupport_toLp_coeFn
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    (p : ℝ≥0∞) (d : weakCZBoundedFiniteSupportSubmodule (H := H)) :
    (weakCZBoundedFiniteSupport_toLp (H := H) p d : ℝ → H) =ᵐ[volume] d.1 := by
  classical
  let hmem : MemLp d.1 p volume :=
    memLp_of_bounded_finite_support d.2.1.aestronglyMeasurable
      (by
        have hz : MeasurableSet {x | d.1 x = 0} :=
          measurableSet_eq_fun d.2.1 measurable_const
        have hs : {x | d.1 x ≠ 0} = {x | d.1 x = 0}ᶜ := by
          ext x
          simp
        rw [hs]
        exact hz.compl)
      d.2.2.1 d.2.2.2 p
  change (hmem.toLp d.1 : ℝ → H) =ᵐ[volume] d.1
  exact hmem.coeFn_toLp

/-- The `L^q` mass of an `L^q` function outside expanding bounded intervals
tends to zero. Compactly supported continuous approximation supplies the
tail control used in the simultaneous `L^p` and `L²` core approximation. -/
private theorem weakCZ_eLpNorm_Icc_complement_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hqTop : q ≠ ∞)
    {u : ℝ → H} (hu : MemLp u q volume) :
    Tendsto
      (fun n : ℕ => eLpNorm
        ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator u) q volume)
      atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hεhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨g, hgcompact, happrox, _hgcont, _hgmem⟩ :=
    hu.exists_hasCompactSupport_eLpNorm_sub_le hqTop hεhalf.ne'
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hgcompact.isBounded
  let R' : ℝ := max R 0
  obtain ⟨N, hN⟩ := exists_nat_gt R'
  have hNreal : R' < (N : ℝ) := by exact_mod_cast hN
  have hsupport : tsupport g ⊆ Set.Icc (-(N : ℝ)) (N : ℝ) := by
    intro x hx
    have hxball : x ∈ Metric.closedBall (0 : ℝ) R' :=
      Metric.closedBall_subset_closedBall (le_max_left R 0) (hR hx)
    have hxabs : |x| ≤ R' := by
      simpa [Real.dist_eq] using Metric.mem_closedBall.mp hxball
    exact abs_le.mp (le_trans hxabs hNreal.le)
  have hgzero (n : ℕ) (hn : N ≤ n) (x : ℝ)
      (hx : x ∉ Set.Icc (-(n : ℝ)) (n : ℝ)) : g x = 0 := by
    by_contra hne
    have hxsupport : x ∈ tsupport g := subset_tsupport g hne
    have hxN : x ∈ Set.Icc (-(N : ℝ)) (N : ℝ) := hsupport hxsupport
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hxn : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) := by
      rcases Set.mem_Icc.mp hxN with ⟨hleft, hright⟩
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    exact hx hxn
  filter_upwards [eventually_ge_atTop N] with n hn
  have hrepr :
      ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator u) =ᵐ[volume]
        ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator (u - g)) := by
    filter_upwards [] with x
    by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · simp [hx]
    · simp [hx, hgzero n hn x hx]
  calc
    eLpNorm ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator u) q volume =
        eLpNorm ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator (u - g)) q volume :=
      eLpNorm_congr_ae hrepr
    _ ≤ eLpNorm (u - g) q volume :=
      eLpNorm_indicator_le (u - g) measurableSet_Icc.compl.nullMeasurableSet
    _ ≤ ε / 2 := happrox
    _ ≤ ε := ENNReal.half_le_self

/-- One bounded finite-support sequence approximates an input simultaneously
in a finite `L^q` space and in `L²`. This is the joint-density fact needed to
identify the `L^q` extension with the original `L²` operator on their common
domain. -/
private theorem weakCZBoundedFiniteSupport_jointLpL2Approximation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.PseudoMetrizableSpace H] [SecondCountableTopology H]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hqTop : q ≠ ∞)
    (u : ℝ → H) (hu : Measurable u)
    (huq : MemLp u q volume) (hu2 : MemLp u 2 volume) :
    ∃ d : ℕ → weakCZBoundedFiniteSupportSubmodule (H := H),
      Tendsto
        (fun n => weakCZBoundedFiniteSupport_toLp q (d n))
        atTop (𝓝 (huq.toLp u)) ∧
      Tendsto
        (fun n => weakCZBoundedFiniteSupport_toLp 2 (d n))
        atTop (𝓝 (hu2.toLp u)) := by
  classical
  let s : Set H := Set.range u ∪ {0}
  have hzero : (0 : H) ∈ s := by simp [s]
  let approx : ℕ → SimpleFunc ℝ H := fun n =>
    SimpleFunc.approxOn u hu s 0 hzero n
  let approxFn : ℕ → ℝ → H := fun n => approx n
  have happroxQ : Tendsto
      (fun n => eLpNorm (approxFn n - u) q volume) atTop (𝓝 0) := by
    have h := SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
      (p := q) hqTop hu huq.eLpNorm_lt_top
    simpa only [approxFn, approx, s] using h
  have happrox2 : Tendsto
      (fun n => eLpNorm (approxFn n - u) (2 : ℝ≥0∞) volume) atTop (𝓝 0) := by
    have htwoTop : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
    have h := SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
      (p := (2 : ℝ≥0∞)) htwoTop hu hu2.eLpNorm_lt_top
    simpa only [approxFn, approx, s] using h
  have htailQ := weakCZ_eLpNorm_Icc_complement_tendsto_zero hqTop huq
  have htail2 := weakCZ_eLpNorm_Icc_complement_tendsto_zero
    (q := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top hu2
  let cutApprox : ℕ → ℝ → H := fun n x =>
    if x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) then approxFn n x else 0
  let d : ℕ → weakCZBoundedFiniteSupportSubmodule (H := H) := fun n => by
    let I : Set ℝ := Set.Icc (-(n : ℝ)) (n : ℝ)
    have hmeas : Measurable (cutApprox n) := by
      change Measurable (fun x => if x ∈ I then approxFn n x else 0)
      exact Measurable.ite measurableSet_Icc (approx n).measurable measurable_const
    let hbounded : ∃ C : ℝ, ∀ x, ‖approx n x‖ ≤ C :=
      (approx n).exists_forall_norm_le
    let C : ℝ := Classical.choose hbounded
    have hC : ∀ x, ‖approx n x‖ ≤ C := Classical.choose_spec hbounded
    have hbound : ∀ x, ‖cutApprox n x‖ ≤ max C 0 := by
      intro x
      by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · have hx' : -(n : ℝ) ≤ x ∧ x ≤ n := Set.mem_Icc.mp hx
        calc
          ‖cutApprox n x‖ = ‖approx n x‖ := by simp [cutApprox, hx', approxFn]
          _ ≤ C := hC x
          _ ≤ max C 0 := le_max_left C 0
      · have hx' : ¬ (-(n : ℝ) ≤ x ∧ x ≤ n) := by
          simpa only [Set.mem_Icc] using hx
        calc
          ‖cutApprox n x‖ = 0 := by simp [cutApprox, hx', Set.mem_Icc]
          _ ≤ max C 0 := le_max_right C 0
    have hsupport : {x | cutApprox n x ≠ 0} ⊆ I := by
      intro x hx
      change x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      by_contra hnot
      have hnot' : ¬ (-(n : ℝ) ≤ x ∧ x ≤ n) := by
        simpa only [Set.mem_Icc] using hnot
      apply hx
      simp [cutApprox, hnot', Set.mem_Icc]
    have hμI : volume I < ∞ := by
      dsimp [I]
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    exact ⟨cutApprox n, hmeas, ⟨max C 0, hbound⟩,
      (measure_mono hsupport).trans_lt hμI⟩
  let raw : ℕ → ℝ → H := fun n => d n
  have hrawEq (n : ℕ) : raw n = cutApprox n := rfl
  have hmemQ (n : ℕ) : MemLp (raw n) q volume := by
    have hz : MeasurableSet {x | (d n : ℝ → H) x = 0} :=
      measurableSet_eq_fun (d n).2.1 measurable_const
    have hs : {x | (d n : ℝ → H) x ≠ 0} = {x | (d n : ℝ → H) x = 0}ᶜ := by
      ext x
      simp
    have hmem := memLp_of_bounded_finite_support
      (d n).2.1.aestronglyMeasurable (by rw [hs]; exact hz.compl)
      (d n).2.2.1 (d n).2.2.2 q
    simpa [raw] using hmem
  have hmem2 (n : ℕ) : MemLp (raw n) (2 : ℝ≥0∞) volume := by
    have hz : MeasurableSet {x | (d n : ℝ → H) x = 0} :=
      measurableSet_eq_fun (d n).2.1 measurable_const
    have hs : {x | (d n : ℝ → H) x ≠ 0} = {x | (d n : ℝ → H) x = 0}ᶜ := by
      ext x
      simp
    have hmem := memLp_of_bounded_finite_support
      (d n).2.1.aestronglyMeasurable (by rw [hs]; exact hz.compl)
      (d n).2.2.1 (d n).2.2.2 (2 : ℝ≥0∞)
    simpa [raw] using hmem
  have herror (r : ℝ≥0∞) [Fact (1 ≤ r)] (n : ℕ) :
      eLpNorm (raw n - u) r volume ≤
        eLpNorm (approxFn n - u) r volume +
          eLpNorm ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator u) r volume := by
    have hsplit : raw n - u =ᵐ[volume]
        (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (approxFn n - u) +
          (Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator (-u) := by
      filter_upwards [] with x
      by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · rw [hrawEq n]
        change cutApprox n x - u x = _
        have hx' : -(n : ℝ) ≤ x ∧ x ≤ n := Set.mem_Icc.mp hx
        have hcut : cutApprox n x = approxFn n x := by
          simp [cutApprox, Set.mem_Icc, hx']
        rw [hcut, Pi.add_apply, Set.indicator_of_mem hx,
          Set.indicator_of_notMem (by simpa using hx)]
        simp
      · rw [hrawEq n]
        change cutApprox n x - u x = _
        have hx' : ¬ (-(n : ℝ) ≤ x ∧ x ≤ n) := by
          simpa only [Set.mem_Icc] using hx
        have hcut : cutApprox n x = 0 := by
          simp [cutApprox, Set.mem_Icc, hx']
        rw [hcut, Pi.add_apply, Set.indicator_of_notMem hx,
          Set.indicator_of_mem (by simpa using hx)]
        simp
    rw [eLpNorm_congr_ae hsplit]
    calc
      eLpNorm
          ((Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (approxFn n - u) +
            (Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator (-u)) r volume ≤
          eLpNorm ((Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (approxFn n - u)) r volume +
            eLpNorm ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator (-u)) r volume :=
        eLpNorm_add_le (Fact.out : 1 ≤ r)
      _ ≤ eLpNorm (approxFn n - u) r volume +
            eLpNorm ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator (-u)) r volume :=
        add_le_add (eLpNorm_indicator_le _ measurableSet_Icc.nullMeasurableSet) le_rfl
      _ = eLpNorm (approxFn n - u) r volume +
            eLpNorm ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator u) r volume := by
        congr 1
        rw [Set.indicator_neg', eLpNorm_neg]
  have hnormQ : Tendsto (fun n => eLpNorm (raw n - u) q volume)
      atTop (𝓝 0) := by
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
    filter_upwards [ENNReal.tendsto_nhds_zero.1 happroxQ
        (ε / 2) (ENNReal.half_pos hε.ne'),
      ENNReal.tendsto_nhds_zero.1 htailQ
        (ε / 2) (ENNReal.half_pos hε.ne')] with n hnA hnB
    calc
      eLpNorm (raw n - u) q volume ≤
          eLpNorm (approxFn n - u) q volume +
            eLpNorm ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator u) q volume := herror q n
      _ ≤ ε / 2 + ε / 2 := add_le_add hnA hnB
      _ = ε := ENNReal.add_halves ε
  have hnorm2 : Tendsto (fun n => eLpNorm (raw n - u) (2 : ℝ≥0∞) volume)
      atTop (𝓝 0) := by
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
    filter_upwards [ENNReal.tendsto_nhds_zero.1 happrox2
        (ε / 2) (ENNReal.half_pos hε.ne'),
      ENNReal.tendsto_nhds_zero.1 htail2
        (ε / 2) (ENNReal.half_pos hε.ne')] with n hnA hnB
    calc
      eLpNorm (raw n - u) (2 : ℝ≥0∞) volume ≤
          eLpNorm (approxFn n - u) (2 : ℝ≥0∞) volume +
            eLpNorm ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator u) (2 : ℝ≥0∞) volume :=
        herror (2 : ℝ≥0∞) n
      _ ≤ ε / 2 + ε / 2 := add_le_add hnA hnB
      _ = ε := ENNReal.add_halves ε
  let seqQ : ℕ → Lp H q volume := fun n =>
    (hmemQ n).toLp (raw n)
  let seq2 : ℕ → Lp H (2 : ℝ≥0∞) volume := fun n =>
    (hmem2 n).toLp (raw n)
  have hseqQ : Tendsto seqQ atTop (𝓝 (huq.toLp u)) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      raw hmemQ u huq).mpr hnormQ
  have hseq2 : Tendsto seq2 atTop (𝓝 (hu2.toLp u)) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      raw hmem2 u hu2).mpr hnorm2
  have hseqQeq (n : ℕ) :
      weakCZBoundedFiniteSupport_toLp q (d n) = seqQ n := by
    apply Lp.ext
    filter_upwards [weakCZBoundedFiniteSupport_toLp_coeFn q (d n),
      (hmemQ n).coeFn_toLp] with x h₁ h₂
    exact h₁.trans h₂.symm
  have hseq2eq (n : ℕ) :
      weakCZBoundedFiniteSupport_toLp (2 : ℝ≥0∞) (d n) = seq2 n := by
    apply Lp.ext
    filter_upwards [weakCZBoundedFiniteSupport_toLp_coeFn (2 : ℝ≥0∞) (d n),
      (hmem2 n).coeFn_toLp] with x h₁ h₂
    exact h₁.trans h₂.symm
  refine ⟨d, ?_, ?_⟩
  · exact hseqQ.congr' (Filter.Eventually.of_forall fun n => (hseqQeq n).symm)
  · exact hseq2.congr' (Filter.Eventually.of_forall fun n => (hseq2eq n).symm)

/-- Interpolation on bounded inputs gives the exact finite-support
`Lᵖ` norm bound for the original `L²` output. -/
private theorem weakCZ_finiteSupport_output_lpNorm_le
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (S : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : ‖S‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(S (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(S (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (d : weakCZBoundedFiniteSupportSubmodule (H := H₁)) :
    lpNorm (S (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂)
        (ENNReal.ofReal p) volume ≤
      (weakTypeInterpolationConstant 1 p 2 *
        (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
        A ^ weakTypeInterpolationTheta1 1 p 2) *
        lpNorm d.1 (ENNReal.ofReal p) volume := by
  let hOut : MemLp (S (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂)
      (ENNReal.ofReal p) volume :=
    weakCZ_finiteSupport_output_memLp S hA hB hS hOffSupport hp₁ hp₂ d
  let out : Lp H₂ (ENNReal.ofReal p) volume := hOut.toLp
    (S (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂)
  let map : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₂ (ENNReal.ofReal p) volume :=
    weakCZ_finiteSupportLpMap S hA hB hS hOffSupport hp₁ hp₂
  have hmapEq : map d = out := by
    change (weakCZ_finiteSupport_output_memLp S hA hB hS hOffSupport
      hp₁ hp₂ d).toLp (S (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂) = out
    rfl
  have hmapBound :=
    weakCZ_finiteSupportLpMap_norm_le S hA hB hS hOffSupport hp₁ hp₂ d
  have houtNorm : lpNorm (S (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂)
      (ENNReal.ofReal p) volume = ‖map d‖ := by
    change (eLpNorm (S (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂)
        (ENNReal.ofReal p) volume).toReal = ‖out‖
    rw [Lp.norm_def]
    change (eLpNorm (S (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂)
        (ENNReal.ofReal p) volume).toReal =
      (eLpNorm (out : ℝ → H₂) (ENNReal.ofReal p) volume).toReal
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hOut.coeFn_toLp.symm)
  rw [houtNorm]
  calc
    ‖map d‖ ≤
        (weakTypeInterpolationConstant 1 p 2 *
          (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
          A ^ weakTypeInterpolationTheta1 1 p 2) *
          ‖weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p) d‖ := hmapBound
    _ =
        (weakTypeInterpolationConstant 1 p 2 *
          (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
          A ^ weakTypeInterpolationTheta1 1 p 2) *
          lpNorm d.1 (ENNReal.ofReal p) volume := by
      rw [weakCZBoundedFiniteSupport_toLp_norm]

/-- A bounded finite-support piece of the `L²` output obeys the p>2 bound by
testing against its normalized `Lᵖ` norming function and applying the p′<2
estimate to the adjoint. -/
private theorem weakCZ_finiteSupport_output_truncation_lpNorm_le
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    [CompleteSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (S : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₁ 2 (volume : Measure ℝ))
    (hPair : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
      (g : Lp H₂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S g : Lp H₁ 2 volume) x) ∂volume)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : ‖S‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₂) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp : 2 < p)
    (dIn : weakCZBoundedFiniteSupportSubmodule (H := H₁))
    (dOut : weakCZBoundedFiniteSupportSubmodule (H := H₂))
    (hOn : ∀ᵐ x ∂volume, dOut.1 x ≠ 0 →
      (T (weakCZBoundedFiniteSupport_toLp 2 dIn) : Lp H₂ 2 volume) x =
        dOut.1 x) :
    lpNorm dOut.1 (ENNReal.ofReal p) volume ≤
      (weakTypeInterpolationConstant 1 p.conjExponent 2 *
        (9 + 8 * A ^ 2 + 4 * B) ^
          weakTypeInterpolationTheta0 1 p.conjExponent 2 *
        A ^ weakTypeInterpolationTheta1 1 p.conjExponent 2) *
        lpNorm dIn.1 (ENNReal.ofReal p) volume := by
  classical
  have hp1 : 1 < p := by linarith
  let q : ℝ := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq1 : 1 < q := hpq.symm.lt
  have hq2 : q < 2 := by
    have hqpos : 0 < q := hpq.symm.pos
    have hprod : p = q * (p - 1) := by
      have hdiv := hpq.div_conj_eq_sub_one
      field_simp [ne_of_gt hqpos] at hdiv
      nlinarith
    by_contra hnot
    have htwoq : 2 ≤ q := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right htwoq (sub_nonneg.mpr hp.le)
    nlinarith
  have hW : 0 ≤ 9 + 8 * A ^ 2 + 4 * B := by positivity
  have hI : 0 ≤ weakTypeInterpolationConstant 1 q 2 := by
    dsimp [weakTypeInterpolationConstant]
    positivity
  have hθ₀ : 0 ≤ weakTypeInterpolationTheta0 1 q 2 := by
    dsimp [weakTypeInterpolationTheta0]
    positivity
  have hθ₁ : 0 ≤ weakTypeInterpolationTheta1 1 q 2 := by
    dsimp [weakTypeInterpolationTheta1]
    positivity
  have hC : 0 ≤ weakTypeInterpolationConstant 1 q 2 *
      (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 q 2 *
      A ^ weakTypeInterpolationTheta1 1 q 2 := by
    exact mul_nonneg (mul_nonneg hI (Real.rpow_nonneg hW _))
      (Real.rpow_nonneg hA _)
  have hInP : MemLp dIn.1 (ENNReal.ofReal p) volume :=
    memLp_of_bounded_finite_support dIn.2.1.aestronglyMeasurable
      (by
        have hz : MeasurableSet {x | dIn.1 x = 0} :=
          measurableSet_eq_fun dIn.2.1 measurable_const
        have hs : {x | dIn.1 x ≠ 0} = {x | dIn.1 x = 0}ᶜ := by
          ext x
          simp
        rw [hs]
        exact hz.compl)
      dIn.2.2.1 dIn.2.2.2 (ENNReal.ofReal p)
  have hOutP : MemLp dOut.1 (ENNReal.ofReal p) volume :=
    memLp_of_bounded_finite_support dOut.2.1.aestronglyMeasurable
      (by
        have hz : MeasurableSet {x | dOut.1 x = 0} :=
          measurableSet_eq_fun dOut.2.1 measurable_const
        have hs : {x | dOut.1 x ≠ 0} = {x | dOut.1 x = 0}ᶜ := by
          ext x
          simp
        rw [hs]
        exact hz.compl)
      dOut.2.2.1 dOut.2.2.2 (ENNReal.ofReal p)
  by_cases hzero : lpNorm dOut.1 (ENNReal.ofReal p) volume = 0
  · rw [hzero]
    exact mul_nonneg hC (lpNorm_nonneg)
  · have hpos : 0 < lpNorm dOut.1 (ENNReal.ofReal p) volume :=
      lt_of_le_of_ne lpNorm_nonneg (Ne.symm hzero)
    let dTest := weakCZ_normalizedLpNormingFunction_mem_boundedFiniteSupport hp dOut
    have hTestVal : (dTest : ℝ → H₂) =
        normalizedLpNormingFunction (μ := volume) p dOut.1 := rfl
    have hTestMem : MemLp dTest.1 (ENNReal.ofReal q) volume := by
      rw [hTestVal]
      exact memLp_normalizedLpNormingFunction hpq hOutP
    have hTestNorm : lpNorm dTest.1 (ENNReal.ofReal q) volume = 1 := by
      rw [hTestVal]
      exact lpNorm_normalizedLpNormingFunction hpq hOutP hpos
    let f₂ : Lp H₁ 2 (volume : Measure ℝ) :=
      weakCZBoundedFiniteSupport_toLp 2 dIn
    let g₂ : Lp H₂ 2 (volume : Measure ℝ) :=
      weakCZBoundedFiniteSupport_toLp 2 dTest
    have hf₂AE : (f₂ : ℝ → H₁) =ᵐ[volume] dIn.1 := by
      simpa [f₂] using weakCZBoundedFiniteSupport_toLp_coeFn 2 dIn
    have hg₂AE : (g₂ : ℝ → H₂) =ᵐ[volume] dTest.1 := by
      simpa [g₂] using weakCZBoundedFiniteSupport_toLp_coeFn 2 dTest
    have hzeroVector : lpNormingVector p (0 : H₂) = 0 := by
      simp [lpNormingVector, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
    have hpairReplace :
        (∫ x, inner ℝ ((T f₂ : Lp H₂ 2 volume) x) (g₂ x) ∂volume) =
          ∫ x, inner ℝ (dOut.1 x) (dTest.1 x) ∂volume := by
      calc
        (∫ x, inner ℝ ((T f₂ : Lp H₂ 2 volume) x) (g₂ x) ∂volume) =
            ∫ x, inner ℝ ((T f₂ : Lp H₂ 2 volume) x) (dTest.1 x) ∂volume := by
          apply integral_congr_ae
          filter_upwards [hg₂AE] with x hx
          rw [hx]
        _ = ∫ x, inner ℝ (dOut.1 x) (dTest.1 x) ∂volume := by
          apply integral_congr_ae
          filter_upwards [hOn] with x hOnx
          by_cases htest : dTest.1 x = 0
          · simp [htest]
          · have hOutNe : dOut.1 x ≠ 0 := by
              intro hOutZero
              have htestZero : dTest.1 x = 0 := by
                rw [hTestVal]
                simp [normalizedLpNormingFunction, hOutZero, hzeroVector]
              exact htest htestZero
            rw [hOnx hOutNe]
    have hnormingIntegral :
        (∫ x, inner ℝ (dOut.1 x) (dTest.1 x) ∂volume) =
          lpNorm dOut.1 (ENNReal.ofReal p) volume := by
      rw [hTestVal]
      exact weakCZ_integral_inner_real_normalizedLpNormingFunction hpq hOutP hpos
    have hpair :
        (∫ x, inner ℝ (dOut.1 x) (dTest.1 x) ∂volume) =
          ∫ x, inner ℝ (dIn.1 x) ((S g₂ : Lp H₁ 2 volume) x) ∂volume := by
      calc
        (∫ x, inner ℝ (dOut.1 x) (dTest.1 x) ∂volume) =
            ∫ x, inner ℝ ((T f₂ : Lp H₂ 2 volume) x) (g₂ x) ∂volume :=
          hpairReplace.symm
        _ = ∫ x, inner ℝ (f₂ x) ((S g₂ : Lp H₁ 2 volume) x) ∂volume :=
          hPair f₂ g₂
        _ = ∫ x, inner ℝ (dIn.1 x) ((S g₂ : Lp H₁ 2 volume) x) ∂volume := by
          apply integral_congr_ae
          filter_upwards [hf₂AE] with x hx
          rw [hx]
    have hSout : MemLp (S g₂ : ℝ → H₁) (ENNReal.ofReal q) volume :=
      weakCZ_finiteSupport_output_memLp S hA hB hS hOffSupport hq1 hq2 dTest
    have hSbound : lpNorm (S g₂ : ℝ → H₁) (ENNReal.ofReal q) volume ≤
        (weakTypeInterpolationConstant 1 q 2 *
          (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 q 2 *
          A ^ weakTypeInterpolationTheta1 1 q 2) *
          lpNorm dTest.1 (ENNReal.ofReal q) volume :=
      weakCZ_finiteSupport_output_lpNorm_le S hA hB hS hOffSupport hq1 hq2 dTest
    have hholder :=
      weakCZ_norm_integral_real_inner_le_lpNorm_mul_lpNorm hpq hInP hSout
    calc
      lpNorm dOut.1 (ENNReal.ofReal p) volume =
          ‖∫ x, inner ℝ (dIn.1 x) ((S g₂ : Lp H₁ 2 volume) x) ∂volume‖ := by
        rw [← hpair, hnormingIntegral, Real.norm_eq_abs,
          abs_of_nonneg lpNorm_nonneg]
      _ ≤ lpNorm dIn.1 (ENNReal.ofReal p) volume *
          lpNorm (S g₂ : ℝ → H₁) (ENNReal.ofReal q) volume := hholder
      _ ≤ lpNorm dIn.1 (ENNReal.ofReal p) volume *
          ((weakTypeInterpolationConstant 1 q 2 *
            (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 q 2 *
            A ^ weakTypeInterpolationTheta1 1 q 2) *
            lpNorm dTest.1 (ENNReal.ofReal q) volume) :=
        mul_le_mul_of_nonneg_left hSbound lpNorm_nonneg
      _ =
          (weakTypeInterpolationConstant 1 q 2 *
            (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 q 2 *
            A ^ weakTypeInterpolationTheta1 1 q 2) *
            lpNorm dIn.1 (ENNReal.ofReal p) volume := by
        rw [hTestNorm]
        ring

private theorem weakCZ_finiteSupport_output_memLp_gt_two
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    [CompleteSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (S : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₁ 2 (volume : Measure ℝ))
    (hPair : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
      (g : Lp H₂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S g : Lp H₁ 2 volume) x) ∂volume)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : ‖S‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₂) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp : 2 < p)
    (dIn : weakCZBoundedFiniteSupportSubmodule (H := H₁)) :
    MemLp
      ((T (weakCZBoundedFiniteSupport_toLp 2 dIn) : Lp H₂ 2 volume) : ℝ → H₂)
      (ENNReal.ofReal p) volume ∧
    eLpNorm
      ((T (weakCZBoundedFiniteSupport_toLp 2 dIn) : Lp H₂ 2 volume) : ℝ → H₂)
      (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal
          ((weakTypeInterpolationConstant 1 p.conjExponent 2 *
            (9 + 8 * A ^ 2 + 4 * B) ^
              weakTypeInterpolationTheta0 1 p.conjExponent 2 *
            A ^ weakTypeInterpolationTheta1 1 p.conjExponent 2) *
            lpNorm dIn.1 (ENNReal.ofReal p) volume) := by
  classical
  let input₂ : Lp H₁ 2 volume := weakCZBoundedFiniteSupport_toLp 2 dIn
  let output₂ : Lp H₂ 2 volume := T input₂
  let hmeas : AEStronglyMeasurable (output₂ : ℝ → H₂) volume :=
    Lp.aestronglyMeasurable output₂
  let u : ℝ → H₂ := hmeas.mk (output₂ : ℝ → H₂)
  have huMeas : Measurable u := hmeas.measurable_mk
  have huAE : (output₂ : ℝ → H₂) =ᵐ[volume] u := hmeas.ae_eq_mk
  let dOut : ℕ → weakCZBoundedFiniteSupportSubmodule (H := H₂) :=
    fun n => weakCZ_boundedSupportTruncation u huMeas n
  let C : ℝ :=
    weakTypeInterpolationConstant 1 p.conjExponent 2 *
      (9 + 8 * A ^ 2 + 4 * B) ^
        weakTypeInterpolationTheta0 1 p.conjExponent 2 *
      A ^ weakTypeInterpolationTheta1 1 p.conjExponent 2
  have htruncMem (n : ℕ) : MemLp (dOut n).1 (ENNReal.ofReal p) volume := by
    exact memLp_of_bounded_finite_support (dOut n).2.1.aestronglyMeasurable
      (by
        have hz : MeasurableSet {x | (dOut n).1 x = 0} :=
          measurableSet_eq_fun (dOut n).2.1 measurable_const
        have hs : {x | (dOut n).1 x ≠ 0} = {x | (dOut n).1 x = 0}ᶜ := by
          ext x
          simp
        rw [hs]
        exact hz.compl)
      (dOut n).2.2.1 (dOut n).2.2.2 (ENNReal.ofReal p)
  have htruncLpNorm (n : ℕ) :
      lpNorm (dOut n).1 (ENNReal.ofReal p) volume ≤
        C * lpNorm dIn.1 (ENNReal.ofReal p) volume := by
    have hOn : ∀ᵐ x ∂volume, (dOut n).1 x ≠ 0 →
        (T (weakCZBoundedFiniteSupport_toLp 2 dIn) : Lp H₂ 2 volume) x =
          (dOut n).1 x := by
      filter_upwards [huAE] with x hx hnonzero
      have hmem :
          x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ∩ {x | ‖u x‖ ≤ n} := by
        by_contra hnot
        have hzero := weakCZ_boundedSupportTruncation_eq_zero_of_not_mem
          u huMeas n x hnot
        exact hnonzero hzero
      have hvalue := weakCZ_boundedSupportTruncation_eq_of_mem
        u huMeas n x hmem
      exact hx.trans hvalue.symm
    simpa [C] using
      (weakCZ_finiteSupport_output_truncation_lpNorm_le
        T S hPair hA hB hS hOffSupport hp dIn (dOut n) hOn)
  have htruncENorm (n : ℕ) :
      eLpNorm (dOut n).1 (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * lpNorm dIn.1 (ENNReal.ofReal p) volume) := by
    calc
      eLpNorm (dOut n).1 (ENNReal.ofReal p) volume =
          ENNReal.ofReal (lpNorm (dOut n).1 (ENNReal.ofReal p) volume) :=
        (ofReal_lpNorm (htruncMem n)).symm
      _ ≤ ENNReal.ofReal (C * lpNorm dIn.1 (ENNReal.ofReal p) volume) :=
        ENNReal.ofReal_le_ofReal (htruncLpNorm n)
  have hbound : ∀ᶠ n : ℕ in atTop,
      eLpNorm (dOut n).1 (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * lpNorm dIn.1 (ENNReal.ofReal p) volume) :=
    Filter.Eventually.of_forall htruncENorm
  have huNorm :
      eLpNorm u (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * lpNorm dIn.1 (ENNReal.ofReal p) volume) := by
    apply Lp.eLpNorm_le_of_ae_tendsto hbound
    · intro n
      exact (dOut n).2.1.aestronglyMeasurable
    · exact huMeas.aestronglyMeasurable
    · filter_upwards [] with x
      simpa [dOut] using tendsto_const_nhds.congr'
        (weakCZ_boundedSupportTruncation_eventually_eq u huMeas x).symm
  have huMem : MemLp u (ENNReal.ofReal p) volume := by
    rw [memLp_iff]
    exact huNorm.trans_lt ENNReal.ofReal_lt_top
  have houtMem : MemLp (output₂ : ℝ → H₂) (ENNReal.ofReal p) volume :=
    (memLp_congr_ae huAE).2 huMem
  have houtNorm :
      eLpNorm (output₂ : ℝ → H₂) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * lpNorm dIn.1 (ENNReal.ofReal p) volume) := by
    calc
      eLpNorm (output₂ : ℝ → H₂) (ENNReal.ofReal p) volume =
          eLpNorm u (ENNReal.ofReal p) volume := eLpNorm_congr_ae huAE
      _ ≤ ENNReal.ofReal (C * lpNorm dIn.1 (ENNReal.ofReal p) volume) := huNorm
  simpa [input₂, output₂, C] using ⟨houtMem, houtNorm⟩

private noncomputable def weakCZ_finiteSupportLpMap_gt_two
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    [CompleteSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (S : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₁ 2 (volume : Measure ℝ))
    (hPair : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
      (g : Lp H₂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S g : Lp H₁ 2 volume) x) ∂volume)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : ‖S‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₂) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp : 2 < p) :
    weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let source₂ : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ 2 volume := weakCZBoundedFiniteSupport_toLp 2
  let outMem : ∀ d : weakCZBoundedFiniteSupportSubmodule (H := H₁),
      MemLp (T (source₂ d) : ℝ → H₂) (ENNReal.ofReal p) volume := by
    intro d
    simpa [source₂, weakCZBoundedFiniteSupport_toLp] using
      (weakCZ_finiteSupport_output_memLp_gt_two
        T S hPair hA hB hS hOffSupport hp d).1
  let out : weakCZBoundedFiniteSupportSubmodule (H := H₁) →
      Lp H₂ (ENNReal.ofReal p) volume := fun d =>
        (outMem d).toLp (T (source₂ d) : ℝ → H₂)
  refine {
    toFun := out
    map_add' := by
      intro d e
      have hTadd : T (source₂ (d + e)) = T (source₂ d) + T (source₂ e) := by
        rw [map_add source₂, map_add T]
      apply Lp.ext
      filter_upwards [(outMem (d + e)).coeFn_toLp,
        (outMem d).coeFn_toLp, (outMem e).coeFn_toLp,
        Lp.ext_iff.mp hTadd,
        Lp.coeFn_add (T (source₂ d)) (T (source₂ e)),
        Lp.coeFn_add (out d) (out e)] with
        x hsum hd he hT hadd houtAdd
      calc
        out (d + e) x = T (source₂ (d + e)) x := hsum
        _ = (T (source₂ d) + T (source₂ e)) x := hT
        _ = T (source₂ d) x + T (source₂ e) x := hadd
        _ = out d x + out e x := by rw [← hd, ← he]
        _ = (out d + out e) x := houtAdd.symm
    map_smul' := by
      intro c d
      have hTsmul : T (source₂ (c • d)) = c • T (source₂ d) := by
        rw [map_smul source₂, map_smul T]
      apply Lp.ext
      filter_upwards [(outMem (c • d)).coeFn_toLp,
        (outMem d).coeFn_toLp, Lp.ext_iff.mp hTsmul,
        Lp.coeFn_smul c (T (source₂ d)),
        Lp.coeFn_smul c (out d)] with x hscaled hd hT hsmul houtSmul
      calc
        out (c • d) x = T (source₂ (c • d)) x := hscaled
        _ = (c • T (source₂ d)) x := hT
        _ = c • T (source₂ d) x := hsmul
        _ = c • out d x := by rw [hd]
        _ = (c • out d) x := houtSmul.symm
  }

private theorem weakCZ_finiteSupportLpMap_gt_two_norm_le
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    [CompleteSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (S : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₁ 2 (volume : Measure ℝ))
    (hPair : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
      (g : Lp H₂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S g : Lp H₁ 2 volume) x) ∂volume)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : ‖S‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₂) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp : 2 < p)
    (d : weakCZBoundedFiniteSupportSubmodule (H := H₁)) :
    ‖weakCZ_finiteSupportLpMap_gt_two
        T S hPair hA hB hS hOffSupport hp d‖ ≤
      (weakTypeInterpolationConstant 1 p.conjExponent 2 *
        (9 + 8 * A ^ 2 + 4 * B) ^
          weakTypeInterpolationTheta0 1 p.conjExponent 2 *
        A ^ weakTypeInterpolationTheta1 1 p.conjExponent 2) *
        ‖weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p) d‖ := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal p
  letI : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let source₂ : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ 2 volume := weakCZBoundedFiniteSupport_toLp 2
  let sourceP : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ P volume := weakCZBoundedFiniteSupport_toLp P
  let outMem : ∀ d : weakCZBoundedFiniteSupportSubmodule (H := H₁),
      MemLp (T (source₂ d) : ℝ → H₂) P volume := by
    intro d
    simpa [P, source₂, weakCZBoundedFiniteSupport_toLp] using
      (weakCZ_finiteSupport_output_memLp_gt_two
        T S hPair hA hB hS hOffSupport hp d).1
  have houtCoe :
      (weakCZ_finiteSupportLpMap_gt_two
        T S hPair hA hB hS hOffSupport hp d : ℝ → H₂) =ᵐ[volume]
        (T (source₂ d) : ℝ → H₂) := by
    change ((outMem d).toLp (T (source₂ d) : ℝ → H₂) : ℝ → H₂) =ᵐ[volume]
      (T (source₂ d) : ℝ → H₂)
    exact (outMem d).coeFn_toLp
  let C : ℝ := weakTypeInterpolationConstant 1 p.conjExponent 2 *
      (9 + 8 * A ^ 2 + 4 * B) ^
        weakTypeInterpolationTheta0 1 p.conjExponent 2 *
      A ^ weakTypeInterpolationTheta1 1 p.conjExponent 2
  have hC : 0 ≤ C := by
    have hp₁ : 1 < p := by linarith
    have hpq : p.HolderConjugate p.conjExponent :=
      Real.HolderConjugate.conjExponent hp₁
    have hq1 : 1 < p.conjExponent := hpq.symm.lt
    have hq2 : p.conjExponent < 2 := by
      have hqpos : 0 < p.conjExponent := hpq.symm.pos
      have hprod : p = p.conjExponent * (p - 1) := by
        have hdiv := hpq.div_conj_eq_sub_one
        field_simp [ne_of_gt hqpos] at hdiv
        nlinarith
      by_contra hnot
      have htwoq : 2 ≤ p.conjExponent := le_of_not_gt hnot
      have hmul := mul_le_mul_of_nonneg_right htwoq (sub_nonneg.mpr hp.le)
      nlinarith
    have hW : 0 ≤ 9 + 8 * A ^ 2 + 4 * B := by positivity
    have hI : 0 ≤ weakTypeInterpolationConstant 1 p.conjExponent 2 := by
      dsimp [weakTypeInterpolationConstant]
      positivity
    have hθ₀ : 0 ≤ weakTypeInterpolationTheta0 1 p.conjExponent 2 := by
      dsimp [weakTypeInterpolationTheta0]
      positivity
    have hθ₁ : 0 ≤ weakTypeInterpolationTheta1 1 p.conjExponent 2 := by
      dsimp [weakTypeInterpolationTheta1]
      positivity
    dsimp [C]
    exact mul_nonneg (mul_nonneg hI (Real.rpow_nonneg hW _))
      (Real.rpow_nonneg hA _)
  have hstrong :
      eLpNorm (T (source₂ d) : ℝ → H₂) P volume ≤
        ENNReal.ofReal (C * lpNorm d.1 P volume) := by
    simpa [P, C, source₂, weakCZBoundedFiniteSupport_toLp] using
      (weakCZ_finiteSupport_output_memLp_gt_two
        T S hPair hA hB hS hOffSupport hp d).2
  have hfinite : ENNReal.ofReal (C * lpNorm d.1 P volume) < ∞ :=
    ENNReal.ofReal_lt_top
  calc
    ‖weakCZ_finiteSupportLpMap_gt_two
        T S hPair hA hB hS hOffSupport hp d‖ =
        (eLpNorm
          (weakCZ_finiteSupportLpMap_gt_two
            T S hPair hA hB hS hOffSupport hp d : ℝ → H₂)
          P volume).toReal := by
            rw [Lp.norm_def]
    _ = (eLpNorm (T (source₂ d) : ℝ → H₂) P volume).toReal := by
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae houtCoe)
    _ ≤ (ENNReal.ofReal (C * lpNorm d.1 P volume)).toReal :=
      ENNReal.toReal_mono hfinite.ne hstrong
    _ = C * lpNorm d.1 P volume :=
      ENNReal.toReal_ofReal (mul_nonneg hC lpNorm_nonneg)
    _ = C * ‖weakCZBoundedFiniteSupport_toLp P d‖ := by
      rw [← weakCZBoundedFiniteSupport_toLp_norm P d]
    _ = _ := by rfl

private noncomputable def weakCZ_LpExtension_gt_two
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    [CompleteSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (S : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₁ 2 (volume : Measure ℝ))
    (hPair : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
      (g : Lp H₂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S g : Lp H₁ 2 volume) x) ∂volume)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : ‖S‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₂) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp : 2 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  exact (weakCZ_finiteSupportLpMap_gt_two
    T S hPair hA hB hS hOffSupport hp).extendOfNorm
      (weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p))

private theorem weakCZ_LpExtension_gt_two_agrees_and_bounded
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    [CompleteSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (S : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₁ 2 (volume : Measure ℝ))
    (hPair : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
      (g : Lp H₂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S g : Lp H₁ 2 volume) x) ∂volume)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : ‖S‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₂) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp : 2 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∃ extension : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ),
      (∀ d : weakCZBoundedFiniteSupportSubmodule (H := H₁),
        extension (weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p) d) =
          weakCZ_finiteSupportLpMap_gt_two
            T S hPair hA hB hS hOffSupport hp d) ∧
      (∀ f, ‖extension f‖ ≤
        (weakTypeInterpolationConstant 1 p.conjExponent 2 *
          (9 + 8 * A ^ 2 + 4 * B) ^
            weakTypeInterpolationTheta0 1 p.conjExponent 2 *
          A ^ weakTypeInterpolationTheta1 1 p.conjExponent 2) * ‖f‖) := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let e : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ (ENNReal.ofReal p) volume :=
    weakCZBoundedFiniteSupport_toLp (ENNReal.ofReal p)
  let Sₚ := weakCZ_finiteSupportLpMap_gt_two
    T S hPair hA hB hS hOffSupport hp
  let C : ℝ := weakTypeInterpolationConstant 1 p.conjExponent 2 *
      (9 + 8 * A ^ 2 + 4 * B) ^
        weakTypeInterpolationTheta0 1 p.conjExponent 2 *
      A ^ weakTypeInterpolationTheta1 1 p.conjExponent 2
  have hdense : DenseRange e := by
    simpa [e] using
      (weakCZBoundedFiniteSupport_denseRange (H := H₁)
        (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top)
  have hbound : ∀ d, ‖Sₚ d‖ ≤ C * ‖e d‖ := by
    intro d
    simpa [Sₚ, C] using
      weakCZ_finiteSupportLpMap_gt_two_norm_le
        T S hPair hA hB hS hOffSupport hp d
  let extension := Sₚ.extendOfNorm e
  exact ⟨extension,
    (fun d => LinearMap.extendOfNorm_eq hdense ⟨C, hbound⟩ d),
    (fun f => by
      simpa [extension, Sₚ, C] using
        (LinearMap.norm_extendOfNorm_apply_le hdense C hbound f))⟩

private theorem weakCZ_finiteSupportLpMap_coeFn_gt_two
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    [CompleteSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (S : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₁ 2 (volume : Measure ℝ))
    (hPair : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
      (g : Lp H₂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S g : Lp H₁ 2 volume) x) ∂volume)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : ‖S‖ ≤ A)
    (hOffSupport : ∀ (u : ℝ → H₂) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume)
    {p : ℝ} (hp : 2 < p)
    (d : weakCZBoundedFiniteSupportSubmodule (H := H₁)) :
    (weakCZ_finiteSupportLpMap_gt_two
      T S hPair hA hB hS hOffSupport hp d : ℝ → H₂) =ᵐ[volume]
      (T (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂) := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal p
  letI : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let source₂ : weakCZBoundedFiniteSupportSubmodule (H := H₁) →ₗ[ℝ]
      Lp H₁ 2 volume := weakCZBoundedFiniteSupport_toLp 2
  let outMem : ∀ d : weakCZBoundedFiniteSupportSubmodule (H := H₁),
      MemLp (T (source₂ d) : ℝ → H₂) P volume := by
    intro d
    simpa [P, source₂, weakCZBoundedFiniteSupport_toLp] using
      (weakCZ_finiteSupport_output_memLp_gt_two
        T S hPair hA hB hS hOffSupport hp d).1
  change ((outMem d).toLp (T (source₂ d) : ℝ → H₂) : ℝ → H₂) =ᵐ[volume]
    (T (source₂ d) : ℝ → H₂)
  exact (outMem d).coeFn_toLp

/-- A bounded extension and the original `L²` operator agree on their full
common domain once they agree on bounded finite-support inputs. The same
finite-support sequence is used in both norms, and uniqueness of limits in
measure identifies the two outputs. -/
private theorem weakCZLpExtension_agrees_on_common_domain
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [MeasurableSpace H₁] [BorelSpace H₁] [OpensMeasurableSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁] [SecondCountableTopology H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
    [MeasurableSpace H₂] [BorelSpace H₂] [OpensMeasurableSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂] [SecondCountableTopology H₂]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hqTop : q ≠ ∞)
    (U : Lp H₁ q (volume : Measure ℝ) →L[ℝ]
      Lp H₂ q (volume : Measure ℝ))
    (core : weakCZBoundedFiniteSupportSubmodule (H := H₁) →
      Lp H₂ q (volume : Measure ℝ))
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    (hcoreU : ∀ d, U (weakCZBoundedFiniteSupport_toLp q d) = core d)
    (hcoreT : ∀ d,
      (core d : ℝ → H₂) =ᵐ[volume]
        (T (weakCZBoundedFiniteSupport_toLp 2 d) : ℝ → H₂))
    (u : ℝ → H₁) (hu : Measurable u)
    (huq : MemLp u q volume) (hu2 : MemLp u 2 volume) :
    (U (huq.toLp u) : ℝ → H₂) =ᵐ[volume]
      (T (hu2.toLp u) : ℝ → H₂) := by
  obtain ⟨d, hq, h2⟩ :=
    weakCZBoundedFiniteSupport_jointLpL2Approximation hqTop u hu huq hu2
  let seqQ : ℕ → Lp H₁ q volume := fun n =>
    weakCZBoundedFiniteSupport_toLp q (d n)
  let seq2 : ℕ → Lp H₁ 2 volume := fun n =>
    weakCZBoundedFiniteSupport_toLp 2 (d n)
  have hU : Tendsto (fun n => U (seqQ n)) atTop (𝓝 (U (huq.toLp u))) :=
    (U.continuous.tendsto _).comp hq
  have hT : Tendsto (fun n => T (seq2 n)) atTop (𝓝 (T (hu2.toLp u))) :=
    (T.continuous.tendsto _).comp h2
  have hseq (n : ℕ) :
      (U (seqQ n) : ℝ → H₂) =ᵐ[volume] (T (seq2 n) : ℝ → H₂) := by
    rw [hcoreU (d n)]
    exact hcoreT (d n)
  have hUmeasure : TendstoInMeasure volume (fun n => U (seqQ n)) atTop
      (U (huq.toLp u)) := tendstoInMeasure_of_tendsto_Lp hU
  have hTmeasure : TendstoInMeasure volume (fun n => T (seq2 n)) atTop
      (T (hu2.toLp u)) := tendstoInMeasure_of_tendsto_Lp hT
  have hTmeasure' : TendstoInMeasure volume (fun n => U (seqQ n)) atTop
      (T (hu2.toLp u)) := by
    apply TendstoInMeasure.congr_left (f := fun n => T (seq2 n))
      (f' := fun n => U (seqQ n)) ?_ hTmeasure
    intro n
    exact (hseq n).symm
  exact ae_eq_of_tendstoInMeasure hUmeasure hTmeasure'

/-- The exact dyadic off-support hypothesis in `lj:weak-cz`, with its finite
nonnegative integral represented by an `IntegrableOn` witness and its Bochner
integral inequality. -/
def weakCZOffSupportBound
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ)) (B : ℝ) : Prop :=
  ∀ (u : ℝ → H₁) (m j : ℤ)
    (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
    (∫ x, u x ∂volume = 0) →
    (∀ x, x ∉ dyadicInterval m j → u x = 0) →
    IntegrableOn
      (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
      (dyadicNinefoldInterval m j)ᶜ volume ∧
    ∫ x in (dyadicNinefoldInterval m j)ᶜ,
        ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
      B * ∫ x, ‖u x‖ ∂volume

/-- The all-`p` strong constant in `lj:weak-cz`. The three branches are the
interpolated `1<p<2` bound, the `L²` operator bound, and the reflected
`p'=p.conjExponent` bound for `p>2`. -/
def weakTypeFromOffSupportStrongConstant (p A B : ℝ) : ℝ :=
  if p < 2 then
    weakTypeInterpolationConstant 1 p 2 *
      (9 + 8 * A ^ 2 + 4 * B) ^ weakTypeInterpolationTheta0 1 p 2 *
      A ^ weakTypeInterpolationTheta1 1 p 2
  else if p = 2 then A
  else
    weakTypeInterpolationConstant 1 p.conjExponent 2 *
      (9 + 8 * A ^ 2 + 4 * B) ^
        weakTypeInterpolationTheta0 1 p.conjExponent 2 *
      A ^ weakTypeInterpolationTheta1 1 p.conjExponent 2

/-- Weak type `(1,1)` from the exact dyadic off-support estimate, together
with the conditional all-`p` extension when the same estimate holds for an
adjoint-pair operator. The weak endpoint needs only the hypothesis on `T`;
the strong conclusion takes the adjoint-pair data as its explicit premise. -/
theorem weakTypeFromOffSupport
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hT : ‖T‖ ≤ A)
    (hOffSupportT : weakCZOffSupportBound T B) :
    (∀ {f : ℝ → H₁} (hf : Integrable f volume)
      (hf₂ : MemLp f 2 volume) {level : ℝ} (hlevel : 0 < level),
      volume {x | level < ‖(T (hf₂.toLp f) : Lp H₂ 2 volume) x‖} ≤
        ENNReal.ofReal ((9 + 8 * A ^ 2 + 4 * B) *
          ((∫ x, ‖f x‖ ∂volume) / level))) ∧
    (∀ (S : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
        Lp H₁ 2 (volume : Measure ℝ))
      (hPair : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
        (g : Lp H₂ 2 (volume : Measure ℝ)),
        (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
          ∫ x, inner ℝ (f x) ((S g : Lp H₁ 2 volume) x) ∂volume)
      (hS : ‖S‖ ≤ A) (hOffSupportS : weakCZOffSupportBound S B)
      (p : ℝ) (hp₁ : 1 < p),
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
      ∃ U : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
          Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ),
        ∀ f, ‖U f‖ ≤
          weakTypeFromOffSupportStrongConstant p A B * ‖f‖) := by
  classical
  letI : CompleteSpace H₁ := FiniteDimensional.complete ℝ H₁
  letI : CompleteSpace H₂ := FiniteDimensional.complete ℝ H₂
  have hOffT : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume := by
    simpa [weakCZOffSupportBound] using hOffSupportT
  constructor
  · intro f hf hf₂ level hlevel
    exact weakTypeFromOffSupport_weakPart T hT hOffT hf hf₂ hlevel
  · intro S hPair hS hOffSupportS p hp₁
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    have hA : 0 ≤ A := le_trans (norm_nonneg T) hT
    have hOffS : ∀ (u : ℝ → H₂) (m j : ℤ)
        (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
        (∫ x, u x ∂volume = 0) →
        (∀ x, x ∉ dyadicInterval m j → u x = 0) →
        IntegrableOn
          (fun x => ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖)
          (dyadicNinefoldInterval m j)ᶜ volume ∧
        ∫ x in (dyadicNinefoldInterval m j)ᶜ,
            ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖ ∂volume ≤
          B * ∫ x, ‖u x‖ ∂volume := by
      simpa [weakCZOffSupportBound] using hOffSupportS
    by_cases hsub : Subsingleton H₁
    · letI : Subsingleton H₁ := hsub
      have hbounded : ∀ f : Lp (α := ℝ) H₁ (ENNReal.ofReal p)
          (μ := (volume : Measure ℝ)),
          ‖(0 : Lp (α := ℝ) H₁ (ENNReal.ofReal p) (μ := volume) →L[ℝ]
            Lp (α := ℝ) H₂ (ENNReal.ofReal p) (μ := volume)) f‖ ≤
              weakTypeFromOffSupportStrongConstant p A B * ‖f‖ := by
        intro f
        have hfzero : f = 0 := by
          apply Lp.ext
          filter_upwards [] with x
          exact Subsingleton.elim _ _
        simp [hfzero]
      exact ⟨0, hbounded⟩
    · have hB : 0 ≤ B :=
        dyadicWeakCZ_offSupport_constant_nonneg_of_nontrivial T hOffT hsub
      by_cases hp₂ : p < 2
      · obtain ⟨U, _, hbound⟩ :=
          weakCZ_LpExtension_lt_two_agrees_and_bounded
            T hA hB hT hOffT hp₁ hp₂
        have hbound' : ∀ f, ‖U f‖ ≤
            weakTypeFromOffSupportStrongConstant p A B * ‖f‖ := by
          intro f
          simpa [weakTypeFromOffSupportStrongConstant, hp₂] using hbound f
        exact ⟨U, hbound'⟩
      · by_cases hpEq : p = 2
        · subst p
          have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
          letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
          have hbound : ∀ f : Lp H₁ 2 (volume : Measure ℝ),
              ‖T f‖ ≤ A * ‖f‖ := by
            intro f
            have hnorm : ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
            have hscale : ‖T‖ * ‖f‖ ≤ A * ‖f‖ :=
              mul_le_mul_of_nonneg_right hT (norm_nonneg f)
            exact hnorm.trans hscale
          have hresult :
              ∃ U : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
                  Lp H₂ 2 (volume : Measure ℝ),
                ∀ f, ‖U f‖ ≤ A * ‖f‖ := ⟨T, hbound⟩
          have castBoundedResult
              {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)] (hrs : r = s) :
              (∃ U : Lp H₁ r (volume : Measure ℝ) →L[ℝ]
                  Lp H₂ r (volume : Measure ℝ), ∀ f, ‖U f‖ ≤ A * ‖f‖) →
              (∃ U : Lp H₁ s (volume : Measure ℝ) →L[ℝ]
                  Lp H₂ s (volume : Measure ℝ), ∀ f, ‖U f‖ ≤ A * ‖f‖) := by
            cases hrs
            intro h
            exact h
          have hresult' :
              ∃ U : Lp H₁ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ) →L[ℝ]
                  Lp H₂ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ),
                ∀ f, ‖U f‖ ≤ A * ‖f‖ :=
            castBoundedResult htwo.symm hresult
          simpa [weakTypeFromOffSupportStrongConstant] using hresult'
        · have hle : (2 : ℝ) ≤ p := le_of_not_gt hp₂
          have hpgt : 2 < p := lt_of_le_of_ne hle (Ne.symm hpEq)
          obtain ⟨U, _, hbound⟩ :=
            weakCZ_LpExtension_gt_two_agrees_and_bounded
              T S hPair hA hB hS hOffS hpgt
          have hnotlt : ¬ p < 2 := hp₂
          have hbound' : ∀ f, ‖U f‖ ≤
              weakTypeFromOffSupportStrongConstant p A B * ‖f‖ := by
            intro f
            simpa [weakTypeFromOffSupportStrongConstant, hnotlt, hpEq]
              using hbound f
          exact ⟨U, hbound'⟩

/-- The strong extension in `weakTypeFromOffSupport` agrees with the original
`L²` operator on every input in `Lᵖ ∩ L²`. The existing theorem states the
norm bound; this companion theorem records the full common-domain agreement. -/
theorem weakTypeFromOffSupport_extension_agrees_on_Lp_inter_L2
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁]
    [SecondCountableTopology H₁] [OpensMeasurableSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [TopologicalSpace.PseudoMetrizableSpace H₂]
    [SecondCountableTopology H₂] [OpensMeasurableSpace H₂]
    (T : Lp H₁ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₂ 2 (volume : Measure ℝ))
    {A B : ℝ} (hT : ‖T‖ ≤ A)
    (hOffSupportT : weakCZOffSupportBound T B)
    (S : Lp H₂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp H₁ 2 (volume : Measure ℝ))
    (hPair : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
      (g : Lp H₂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T f : Lp H₂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S g : Lp H₁ 2 volume) x) ∂volume)
    (hS : ‖S‖ ≤ A) (hOffSupportS : weakCZOffSupportBound S B)
    (p : ℝ) (hp₁ : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    ∃ U : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ),
      (∀ f, ‖U f‖ ≤ weakTypeFromOffSupportStrongConstant p A B * ‖f‖) ∧
      (∀ (f : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ))
        (hf₂ : MemLp (f : ℝ → H₁) 2 volume),
        (U f : ℝ → H₂) =ᵐ[volume]
          (T (hf₂.toLp (f : ℝ → H₁)) : ℝ → H₂)) := by
  classical
  letI : CompleteSpace H₁ := FiniteDimensional.complete ℝ H₁
  letI : CompleteSpace H₂ := FiniteDimensional.complete ℝ H₂
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  have hOffT : ∀ (u : ℝ → H₁) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(T (hu₂.toLp u) : Lp H₂ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume := by
    simpa [weakCZOffSupportBound] using hOffSupportT
  have hA : 0 ≤ A := le_trans (norm_nonneg T) hT
  have hOffS : ∀ (u : ℝ → H₂) (m j : ℤ)
      (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume),
      (∫ x, u x ∂volume = 0) →
      (∀ x, x ∉ dyadicInterval m j → u x = 0) →
      IntegrableOn
        (fun x => ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖)
        (dyadicNinefoldInterval m j)ᶜ volume ∧
      ∫ x in (dyadicNinefoldInterval m j)ᶜ,
          ‖(S (hu₂.toLp u) : Lp H₁ 2 volume) x‖ ∂volume ≤
        B * ∫ x, ‖u x‖ ∂volume := by
    simpa [weakCZOffSupportBound] using hOffSupportS
  by_cases hsub : Subsingleton H₁
  · letI : Subsingleton H₁ := hsub
    let U : Lp H₁ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp H₂ (ENNReal.ofReal p) (volume : Measure ℝ) := 0
    refine ⟨U, ?_, ?_⟩
    · intro f
      have hfzero : f = 0 := by
        apply Lp.ext
        filter_upwards [] with x
        exact Subsingleton.elim _ _
      simp [U, hfzero]
    · intro f hf₂
      have hfzero : f = 0 := by
        apply Lp.ext
        filter_upwards [] with x
        exact Subsingleton.elim _ _
      have hsourcezero : hf₂.toLp (f : ℝ → H₁) = 0 := by
        apply Lp.ext
        filter_upwards [] with x
        exact Subsingleton.elim _ _
      have hUzero : U f = 0 := by simp [U]
      have hTzero : T (hf₂.toLp (f : ℝ → H₁)) = 0 := by
        rw [hsourcezero]
        simp
      rw [hUzero, hTzero]
      rfl
  · have hB : 0 ≤ B :=
      dyadicWeakCZ_offSupport_constant_nonneg_of_nontrivial T hOffT hsub
    by_cases hp₂ : p < 2
    · obtain ⟨U, hcoreU, hbound⟩ :=
        weakCZ_LpExtension_lt_two_agrees_and_bounded
          T hA hB hT hOffT hp₁ hp₂
      let P : ℝ≥0∞ := ENNReal.ofReal p
      let core : weakCZBoundedFiniteSupportSubmodule (H := H₁) →
          Lp H₂ P volume :=
        weakCZ_finiteSupportLpMap T hA hB hT hOffT hp₁ hp₂
      have hstrong : ∀ f, ‖U f‖ ≤
          weakTypeFromOffSupportStrongConstant p A B * ‖f‖ := by
        intro f
        simpa [weakTypeFromOffSupportStrongConstant, hp₂] using hbound f
      have hagreement : ∀ (f : Lp H₁ P volume)
          (hf₂ : MemLp (f : ℝ → H₁) 2 volume),
          (U f : ℝ → H₂) =ᵐ[volume]
            (T (hf₂.toLp (f : ℝ → H₁)) : ℝ → H₂) := by
        intro f hf₂
        have hfq : MemLp (f : ℝ → H₁) P volume := Lp.memLp f
        have hfqToLp : hfq.toLp (f : ℝ → H₁) = f := by
          apply Lp.ext
          filter_upwards [hfq.coeFn_toLp] with x hx
          exact hx
        have hUeq : U f = U (hfq.toLp (f : ℝ → H₁)) :=
          congrArg U hfqToLp.symm
        have hUae : (U f : ℝ → H₂) =ᵐ[volume]
            (U (hfq.toLp (f : ℝ → H₁)) : ℝ → H₂) := Lp.ext_iff.mp hUeq
        exact hUae.trans (weakCZLpExtension_agrees_on_common_domain
          (q := P) ENNReal.ofReal_ne_top U core T
          (by intro d; simpa [core, P] using hcoreU d)
          (by
            intro d
            exact weakCZ_finiteSupportLpMap_coeFn_lt_two
              T hA hB hT hOffT hp₁ hp₂ d)
          (f : ℝ → H₁) (Lp.stronglyMeasurable f).measurable hfq hf₂)
      exact ⟨U, by simpa [P] using hstrong, by simpa [P] using hagreement⟩
    · by_cases hpEq : p = 2
      · subst p
        have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
        letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
        have hTbound : ∀ f : Lp H₁ 2 (volume : Measure ℝ),
            ‖T f‖ ≤ A * ‖f‖ := by
          intro f
          exact (T.le_opNorm f).trans
            (mul_le_mul_of_nonneg_right hT (norm_nonneg f))
        have hTagree : ∀ (f : Lp H₁ 2 (volume : Measure ℝ))
            (hf₂ : MemLp (f : ℝ → H₁) 2 volume),
            (T f : ℝ → H₂) =ᵐ[volume]
              (T (hf₂.toLp (f : ℝ → H₁)) : ℝ → H₂) := by
          intro f hf₂
          have hrep : hf₂.toLp (f : ℝ → H₁) = f := by
            apply Lp.ext
            filter_upwards [hf₂.coeFn_toLp] with x hx
            exact hx
          rw [hrep]
        have castResult
            {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)] (hrs : r = s) :
            (∃ U : Lp H₁ r volume →L[ℝ] Lp H₂ r volume,
              (∀ f, ‖U f‖ ≤ A * ‖f‖) ∧
              (∀ (f : Lp H₁ r volume) (hf₂ : MemLp (f : ℝ → H₁) 2 volume),
                (U f : ℝ → H₂) =ᵐ[volume]
                  (T (hf₂.toLp (f : ℝ → H₁)) : ℝ → H₂))) →
            (∃ U : Lp H₁ s volume →L[ℝ] Lp H₂ s volume,
              (∀ f, ‖U f‖ ≤ A * ‖f‖) ∧
              (∀ (f : Lp H₁ s volume) (hf₂ : MemLp (f : ℝ → H₁) 2 volume),
                (U f : ℝ → H₂) =ᵐ[volume]
                  (T (hf₂.toLp (f : ℝ → H₁)) : ℝ → H₂))) := by
          cases hrs
          intro h
          exact h
        have hresult : ∃ U : Lp H₁ (ENNReal.ofReal (2 : ℝ)) volume →L[ℝ]
            Lp H₂ (ENNReal.ofReal (2 : ℝ)) volume,
            (∀ f, ‖U f‖ ≤ A * ‖f‖) ∧
            (∀ (f : Lp H₁ (ENNReal.ofReal (2 : ℝ)) volume)
              (hf₂ : MemLp (f : ℝ → H₁) 2 volume),
              (U f : ℝ → H₂) =ᵐ[volume]
                (T (hf₂.toLp (f : ℝ → H₁)) : ℝ → H₂)) :=
          castResult htwo.symm ⟨T, hTbound, hTagree⟩
        simpa [weakTypeFromOffSupportStrongConstant] using hresult
      · have hle : (2 : ℝ) ≤ p := le_of_not_gt hp₂
        have hpgt : 2 < p := lt_of_le_of_ne hle (Ne.symm hpEq)
        obtain ⟨U, hcoreU, hbound⟩ :=
          weakCZ_LpExtension_gt_two_agrees_and_bounded
            T S hPair hA hB hS hOffS hpgt
        let P : ℝ≥0∞ := ENNReal.ofReal p
        let core : weakCZBoundedFiniteSupportSubmodule (H := H₁) →
            Lp H₂ P volume :=
          weakCZ_finiteSupportLpMap_gt_two T S hPair hA hB hS hOffS hpgt
        have hstrong : ∀ f, ‖U f‖ ≤
            weakTypeFromOffSupportStrongConstant p A B * ‖f‖ := by
          intro f
          simpa [weakTypeFromOffSupportStrongConstant, hp₂, hpEq] using hbound f
        have hagreement : ∀ (f : Lp H₁ P volume)
            (hf₂ : MemLp (f : ℝ → H₁) 2 volume),
            (U f : ℝ → H₂) =ᵐ[volume]
              (T (hf₂.toLp (f : ℝ → H₁)) : ℝ → H₂) := by
          intro f hf₂
          have hfq : MemLp (f : ℝ → H₁) P volume := Lp.memLp f
          have hfqToLp : hfq.toLp (f : ℝ → H₁) = f := by
            apply Lp.ext
            filter_upwards [hfq.coeFn_toLp] with x hx
            exact hx
          have hUeq : U f = U (hfq.toLp (f : ℝ → H₁)) :=
            congrArg U hfqToLp.symm
          have hUae : (U f : ℝ → H₂) =ᵐ[volume]
              (U (hfq.toLp (f : ℝ → H₁)) : ℝ → H₂) := Lp.ext_iff.mp hUeq
          exact hUae.trans (weakCZLpExtension_agrees_on_common_domain
            (q := P) ENNReal.ofReal_ne_top U core T
            (by intro d; simpa [core, P] using hcoreU d)
            (by
              intro d
              exact weakCZ_finiteSupportLpMap_coeFn_gt_two
                T S hPair hA hB hS hOffS hpgt d)
            (f : ℝ → H₁) (Lp.stronglyMeasurable f).measurable hfq hf₂)
        exact ⟨U, by simpa [P] using hstrong,
          by simpa [P] using hagreement⟩


/-- Continuous finite-exponent Lp operators are determined by their common L2
inputs. This exposes the existing bounded finite-support density argument. -/
theorem lpContinuousLinearMap_eq_of_agree_inter_L2
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [MeasurableSpace H₁] [BorelSpace H₁] [OpensMeasurableSpace H₁]
    [TopologicalSpace.PseudoMetrizableSpace H₁] [SecondCountableTopology H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T U : Lp H₁ p (volume : Measure ℝ) →L[ℝ] Lp H₂ p (volume : Measure ℝ))
    (hagree : ∀ (f : Lp H₁ p (volume : Measure ℝ)),
      MemLp (f : ℝ → H₁) 2 volume → T f = U f) : T = U := by
  have hdense := weakCZBoundedFiniteSupport_denseRange (H := H₁) hp
  have heq : (T : Lp H₁ p volume → Lp H₂ p volume) = U :=
    hdense.equalizer T.continuous U.continuous (by
      funext d
      apply hagree
      have hS : MeasurableSet {x | d.1 x ≠ 0} := by
        have hz : MeasurableSet {x | d.1 x = 0} :=
          measurableSet_eq_fun d.2.1 measurable_const
        have hs : {x | d.1 x ≠ 0} = {x | d.1 x = 0}ᶜ := by
          ext x
          rfl
        rw [hs]
        exact hz.compl
      have hmem := memLp_of_bounded_finite_support d.2.1.aestronglyMeasurable
        hS d.2.2.1 d.2.2.2 2
      exact hmem.ae_eq (weakCZBoundedFiniteSupport_toLp_coeFn p d).symm)
  exact DFunLike.ext T U (fun f => congrFun heq f)

#print axioms lpContinuousLinearMap_eq_of_agree_inter_L2

#print axioms weakCZDirectionalOutput_ae_eq_L2Output
#print axioms weakCZDirectionalOutput_eLpNorm_two_le
#print axioms weakCZDirectionalL2Input_eq_toLp
#print axioms weakCZ_layerCake_memLp_one
#print axioms weakCZ_layerCake_moment_one
#print axioms weakCZ_layerCake_moment_two
#print axioms weakCZDirectionalInput_integral_norm_le
#print axioms weakCZ_offSupport_nonneg_bound_from_memLp_one_two
#print axioms weakCZ_measure_weak_bound_of_ae_eq_L2Output
#print axioms weakCZDirectionalOutput_weak_one
#print axioms weakCZDirectionalOutput_weak_two
#print axioms weakCZDirectionalWeakTypeOperator
#print axioms weakCZDirectionalOutput_eLpNorm_interpolation
#print axioms weakCZVectorInput_scalarize
#print axioms weakCZ_finiteVectorInput_strong_lt_two
#print axioms weakCZ_finiteSupport_output_memLp
#print axioms weakCZ_finiteSupportLpMap
#print axioms weakCZ_finiteSupportLpMap_norm_le
#print axioms weakCZ_LpExtension_lt_two
#print axioms weakCZ_LpExtension_lt_two_agrees_and_bounded
#print axioms weakCZ_L2_operator_eLpNorm_le
#print axioms weakCZBoundedFiniteSupport_denseRange
#print axioms weakCZ_norm_integral_real_inner_le_lpNorm_mul_lpNorm
#print axioms weakCZ_inner_real_lpNormingVector_self
#print axioms weakCZ_integral_inner_real_normalizedLpNormingFunction
#print axioms weakCZ_lpNorm_eq_sSup_realLpDualPairingValues
#print axioms weakCZ_adjoint_real_integral_pairing
#print axioms weakCZ_adjoint_Lp_integral_pairing
#print axioms weakCZ_normalizedLpNormingFunction_mem_boundedFiniteSupport
#print axioms weakCZ_boundedSupportTruncation
#print axioms weakCZ_boundedSupportTruncation_eq_of_mem
#print axioms weakCZ_boundedSupportTruncation_eq_zero_of_not_mem
#print axioms weakCZBoundedFiniteSupport_toLp_norm
#print axioms weakCZBoundedFiniteSupport_toLp_coeFn
#print axioms weakCZ_finiteSupport_output_lpNorm_le
#print axioms weakCZ_finiteSupport_output_truncation_lpNorm_le

end

end FractionalPrimes.Literature.JSW

#print axioms FractionalPrimes.Literature.JSW.dyadicVectorMaximalBadCells_ninefold_measure_le
#print axioms FractionalPrimes.Literature.JSW.ae_eq_of_tendstoInMeasure
#print axioms FractionalPrimes.Literature.JSW.ae_eq_of_l1_l2_limits_of_same_functions
#print axioms FractionalPrimes.Literature.JSW.ae_eq_of_l1_l2_summable_same_partial_sums
#print axioms FractionalPrimes.Literature.JSW.ae_eq_l1_tsum_pointwise_tsum
#print axioms FractionalPrimes.Literature.JSW.ae_eq_l2_tsum_pointwise_tsum_of_l1_l2_partial_sums
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_offSupportOutput
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_badRegion
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_badOutput_L2_tsum_eq_offSupport_pointwise_tsum
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_badOutput_integrals_tsum_le
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_badOutput_L1_summable
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_badOutput_restricted_integrals_tsum_le
#print axioms FractionalPrimes.Literature.JSW.eLpNorm_two_sq_eq_ofReal_integral_norm_sq
#print axioms FractionalPrimes.Literature.JSW.memLp_two_dyadicVectorGoodPart
#print axioms FractionalPrimes.Literature.JSW.eLpNorm_sq_dyadicVectorGoodPart_le
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_goodPart_contribution
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_dyadicGoodPart_contribution
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_badSeries_measure_le
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_weak_bound_of_components
#print axioms FractionalPrimes.Literature.JSW.weakTypeFromOffSupport_of_nonneg
#print axioms FractionalPrimes.Literature.JSW.dyadicWeakCZ_offSupport_constant_nonneg_of_nontrivial
#print axioms FractionalPrimes.Literature.JSW.weakTypeFromOffSupport_weakPart
#print axioms FractionalPrimes.Literature.JSW.weakTypeFromOffSupport_zero_operator
#print axioms FractionalPrimes.Literature.JSW.weakTypeFromOffSupport
#print axioms FractionalPrimes.Literature.JSW.weakTypeFromOffSupport_extension_agrees_on_Lp_inter_L2

end
