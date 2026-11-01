module

public import FractionalPrimes.Literature.MobiusToLong.RealMobiusProduct
public import FractionalPrimes.Literature.MobiusToLong.RealZetaComparison
public import FractionalPrimes.Literature.MobiusToLong.RealMobiusIntegralIdentity
public import FractionalPrimes.Literature.MobiusToLong.MobiusMellinDerivative
public import FractionalPrimes.Literature.MobiusToLong.MobiusReciprocalInitialAbel
public import Mathlib.Topology.Order.Basic

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace FractionalPrimes.Literature.MobiusToLong

noncomputable section

/-- The real zeta comparison and the absolutely convergent Dirichlet product
trap the Mellin transform between the exact endpoint bounds from the
blueprint. -/
theorem mobiusMellinTransform_squeeze {σ : ℝ} (hσ : 1 < σ) :
    (σ - 1) / (1 + (σ - 1)) ≤ mobiusMellinTransform σ ∧
      mobiusMellinTransform σ ≤ σ - 1 := by
  have hgap : 0 < σ - 1 := by linarith
  have hz := realRiemannZeta_bounds hσ
  have hzpos : 0 < realRiemannZeta σ := by
    exact lt_of_lt_of_le (by positivity) hz.1
  have hprod : mobiusMellinTransform σ * realRiemannZeta σ = 1 := by
    rw [← realMobiusDirichletSeries_eq_mobiusMellinTransform hσ]
    exact realMobiusDirichletSeries_mul_realRiemannZeta_eq_one hσ
  have hrecip : mobiusMellinTransform σ = (realRiemannZeta σ)⁻¹ := by
    field_simp [ne_of_gt hzpos] at hprod ⊢
    exact hprod
  constructor
  · rw [hrecip]
    calc
      (σ - 1) / (1 + (σ - 1)) = (1 + (σ - 1)⁻¹)⁻¹ := by
        field_simp [ne_of_gt hgap]
        <;> ring
      _ ≤ (realRiemannZeta σ)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hzpos hz.2
  · rw [hrecip]
    calc
      (realRiemannZeta σ)⁻¹ ≤ ((σ - 1)⁻¹)⁻¹ := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (by positivity) hz.1
      _ = σ - 1 := by field_simp [ne_of_gt hgap]

/-- Continuity at the left endpoint and the zeta-product squeeze give the
exact endpoint value of the real Mellin transform. -/
theorem mobiusMellinTransform_at_one_eq_zero {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    mobiusMellinTransform 1 = 0 := by
  let l : Filter ℝ := 𝓝[Set.Ici (1 : ℝ) \ {1}] 1
  have hset : Set.Ici (1 : ℝ) \ {1} = Set.Ioi 1 := by
    ext σ
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨hle, hne⟩
      exact lt_of_le_of_ne hle (Ne.symm hne)
    · intro h
      exact ⟨le_of_lt h, ne_of_gt h⟩
  have hl : l = 𝓝[Set.Ioi (1 : ℝ)] 1 := by
    dsimp [l]
    rw [hset]
  haveI : l.NeBot := by
    rw [hl]
    exact nhdsWithin_Ioi_neBot le_rfl
  have hId : Tendsto (fun σ : ℝ => σ) l (𝓝 1) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hgap : Tendsto (fun σ : ℝ => σ - 1) l (𝓝 0) := by
    simpa [l] using hId.sub_const (1 : ℝ)
  have hbound : ∀ᶠ σ : ℝ in l,
      |mobiusMellinTransform σ| ≤ σ - 1 := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    have hσne : σ ≠ 1 := by simpa using hσ.2
    have hσgt : 1 < σ := lt_of_le_of_ne hσ.1 (Ne.symm hσne)
    rcases mobiusMellinTransform_squeeze hσgt with ⟨hlower, hupper⟩
    have hnonneg : 0 ≤ mobiusMellinTransform σ := by
      have hpos : 0 < (σ - 1) / (1 + (σ - 1)) :=
        div_pos (by linarith) (by linarith)
      linarith
    rw [abs_of_nonneg hnonneg]
    exact hupper
  have hFzero : Tendsto mobiusMellinTransform l (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hgap
      (Filter.Eventually.of_forall fun σ => abs_nonneg (mobiusMellinTransform σ))
      hbound
  have hcont : Tendsto mobiusMellinTransform l
      (𝓝 (mobiusMellinTransform 1)) := by
    apply tendsto_nhdsWithin_mono_left
      (s := Set.Ici (1 : ℝ) \ {1}) (t := Set.Ici 1)
      (by intro σ hσ; exact hσ.1)
    exact (mobiusMellinTransform_hasDerivWithinAt_one hR hC hM).continuousWithinAt
  exact tendsto_nhds_unique hcont hFzero

/-- The right derivative coefficient at one has the exact value one, as
obtained by squeezing the right difference quotients between `1/σ` and `1`.
-/
theorem mobiusMellinTransform_deriv_value_eq_one {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    (∫ t in Set.Ioi 1,
      mobiusSummatory t * Real.rpow t (-2) * (1 - Real.log t)) = 1 := by
  let l : Filter ℝ := 𝓝[Set.Ici (1 : ℝ) \ {1}] 1
  have hset : Set.Ici (1 : ℝ) \ {1} = Set.Ioi 1 := by
    ext σ
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨hle, hne⟩
      exact lt_of_le_of_ne hle (Ne.symm hne)
    · intro h
      exact ⟨le_of_lt h, ne_of_gt h⟩
  have hl : l = 𝓝[Set.Ioi (1 : ℝ)] 1 := by
    dsimp [l]
    rw [hset]
  haveI : l.NeBot := by
    rw [hl]
    exact nhdsWithin_Ioi_neBot le_rfl
  have hF1 := mobiusMellinTransform_at_one_eq_zero hR hC hM
  have hId : Tendsto (fun σ : ℝ => σ) l (𝓝 1) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hInv : Tendsto (fun σ : ℝ => 1 / σ) l (𝓝 1) := by
    have h := hId.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  have hSlopeBounds : ∀ᶠ σ : ℝ in l,
      1 / σ ≤ slope mobiusMellinTransform 1 σ ∧
        slope mobiusMellinTransform 1 σ ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    have hσne : σ ≠ 1 := by simpa using hσ.2
    have hσgt : 1 < σ := lt_of_le_of_ne hσ.1 (Ne.symm hσne)
    have hgap : 0 < σ - 1 := by linarith
    rcases mobiusMellinTransform_squeeze hσgt with ⟨hlower, hupper⟩
    have hslope : slope mobiusMellinTransform 1 σ =
        mobiusMellinTransform σ / (σ - 1) := by
      rw [slope_def_field, hF1]
      simp
    have hlowdiv := div_le_div_of_nonneg_right hlower (le_of_lt hgap)
    have hleft : ((σ - 1) / (1 + (σ - 1))) / (σ - 1) = 1 / σ := by
      field_simp [ne_of_gt hgap, ne_of_gt (by linarith : 0 < σ)]
      <;> ring
    have huptdiv := div_le_div_of_nonneg_right hupper (le_of_lt hgap)
    have hright : (σ - 1) / (σ - 1) = 1 := by
      field_simp [ne_of_gt hgap]
    constructor
    · rw [hslope]
      exact hleft ▸ hlowdiv
    · rw [hslope]
      simpa [hright] using huptdiv
  have hSlopeLower : ∀ᶠ σ : ℝ in l,
      1 / σ ≤ slope mobiusMellinTransform 1 σ :=
    hSlopeBounds.mono fun σ hσ => hσ.1
  have hSlopeUpper : ∀ᶠ σ : ℝ in l,
      slope mobiusMellinTransform 1 σ ≤ 1 :=
    hSlopeBounds.mono fun σ hσ => hσ.2
  have hSlopeOne : Tendsto (slope mobiusMellinTransform 1) l (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hInv tendsto_const_nhds hSlopeLower hSlopeUpper
  have hSlopeD : Tendsto (slope mobiusMellinTransform 1) l
      (𝓝 (∫ t in Set.Ioi 1,
        mobiusSummatory t * Real.rpow t (-2) * (1 - Real.log t))) :=
    (hasDerivWithinAt_iff_tendsto_slope).1
      (mobiusMellinTransform_hasDerivWithinAt_one hR hC hM)
  exact (tendsto_nhds_unique hSlopeOne hSlopeD).symm

end
end FractionalPrimes.Literature.MobiusToLong

