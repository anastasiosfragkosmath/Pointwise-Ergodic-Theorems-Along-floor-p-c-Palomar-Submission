module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseCenterPigeonhole
public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseNumerics

/-!
# Setup for the second recurrence in the bilinear polynomial inverse theorem

This file continues blueprint item `lbi:inverse-theorem` after the
cross-centre denominator pigeonhole.  It verifies the exact second recurrence
length and density, and packages the integral common-centre offset.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The source length `N₁ = ceil (2M)` used in the descending recurrence. -/
def bilinearSecondRecurrenceLength (M : ℝ) : ℕ := Nat.ceil (2 * M)

/-- For `M ≥ 1`, the second recurrence length lies between `M` and `3M`. -/
theorem bilinearSecondRecurrenceLength_bounds
    (M : ℝ) (hM : 1 ≤ M) :
    M ≤ (bilinearSecondRecurrenceLength M : ℝ) ∧
      (bilinearSecondRecurrenceLength M : ℝ) ≤ 3 * M := by
  have hceilLower : 2 * M ≤ (bilinearSecondRecurrenceLength M : ℝ) := by
    dsimp [bilinearSecondRecurrenceLength]
    exact Nat.le_ceil _
  have hceilUpper : (bilinearSecondRecurrenceLength M : ℝ) < 2 * M + 1 := by
    dsimp [bilinearSecondRecurrenceLength]
    exact Nat.ceil_lt_add_one (by positivity)
  constructor <;> linarith

/-- Every source centre in `[M/2,2M]` belongs to `{1,...,N₁}`. -/
theorem bilinearWindowCenters_subset_secondRecurrenceRange
    (M : ℝ) (hM : 0 ≤ M) :
    bilinearWindowCenters M ⊆
      Finset.Icc 1 (bilinearSecondRecurrenceLength M) := by
  intro u hu
  have huData := (mem_bilinearWindowCenters M u).mp hu
  apply Finset.mem_Icc.mpr
  refine ⟨huData.1, ?_⟩
  have hceil : 2 * M ≤ (bilinearSecondRecurrenceLength M : ℝ) := by
    dsimp [bilinearSecondRecurrenceLength]
    exact Nat.le_ceil _
  exact_mod_cast huData.2.2.trans hceil

/-- The explicit identity for `Z₂` converts the cross-centre count into the
exact density `2 δ₂ N₁` required by polynomial recurrence. -/
theorem bilinearSecondRecurrence_density
    (d : ℕ) (hd : 1 ≤ d) (M ρ : ℝ)
    (hM : 1 ≤ M) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    2 * (bilinearInverseZTwo d ρ⁻¹)⁻¹ *
        (bilinearSecondRecurrenceLength M : ℝ) ≤
      ρ ^ 4 * M / (4000 * bilinearInverseA d ρ⁻¹) := by
  have hρinv : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hvalues := bilinearInverseBudget_values d hd ρ⁻¹ hρinv
  have hApos : 0 < bilinearInverseA d ρ⁻¹ := by
    linarith [hvalues.2.2.2.1]
  have hZTwoPos : 0 < bilinearInverseZTwo d ρ⁻¹ := by
    linarith [hvalues.2.2.2.2.1]
  have hNupper := (bilinearSecondRecurrenceLength_bounds M hM).2
  calc
    2 * (bilinearInverseZTwo d ρ⁻¹)⁻¹ *
        (bilinearSecondRecurrenceLength M : ℝ) ≤
        2 * (bilinearInverseZTwo d ρ⁻¹)⁻¹ * (3 * M) := by
      exact mul_le_mul_of_nonneg_left hNupper (by positivity)
    _ = 6 * M / bilinearInverseZTwo d ρ⁻¹ := by
      field_simp [ne_of_gt hZTwoPos]
      ring
    _ = ρ ^ 4 * M / (4000 * bilinearInverseA d ρ⁻¹) := by
      rw [bilinearInverseZTwo_eval]
      field_simp [ne_of_gt hρ, ne_of_gt hApos]
      ring

/-- The common left origin has the source bound `|ell₀ u-X| ≤ 44H` for
every window centre; no choice of a good pair is needed for this geometric
estimate. -/
theorem bilinearCommonLeftBase_offset_bound
    (X H M : ℝ) (hM : 0 < M) (hs : 1 ≤ H / M)
    (u : ℕ) (hu : u ∈ bilinearWindowCenters M) :
    |(bilinearCommonLeftBase X (H / M) u : ℝ) * (u : ℝ) - X| ≤ 44 * H := by
  let ell0 := bilinearCommonLeftBase X (H / M) u
  have huData := (mem_bilinearWindowCenters M u).mp hu
  have huPosNat : 0 < u := by omega
  have huPos : 0 < (u : ℝ) := by exact_mod_cast huPosNat
  have hHpos : 0 < H := by
    have hMleH : M ≤ H := by
      have := (le_div_iff₀ hM).mp hs
      simpa using this
    linarith
  have hMleH : M ≤ H := by
    have := (le_div_iff₀ hM).mp hs
    simpa using this
  have hspos : 0 < H / M := by positivity
  have hell0Le : (ell0 : ℝ) ≤ X / (u : ℝ) - 21 * (H / M) := by
    dsimp [ell0, bilinearCommonLeftBase]
    exact Int.floor_le _
  have hell0Lower : X / (u : ℝ) - 21 * (H / M) < (ell0 : ℝ) + 1 := by
    dsimp [ell0, bilinearCommonLeftBase]
    exact Int.lt_floor_add_one _
  have hoffsetNonpos : (ell0 : ℝ) * (u : ℝ) - X ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_right hell0Le huPos.le
    have hsnonneg : 0 ≤ 21 * (H / M) * (u : ℝ) := by positivity
    calc
      (ell0 : ℝ) * (u : ℝ) - X ≤
          (X / (u : ℝ) - 21 * (H / M)) * (u : ℝ) - X := by linarith
      _ = -(21 * (H / M) * (u : ℝ)) := by
        field_simp [huPos.ne']
        ring
      _ ≤ 0 := neg_nonpos.mpr hsnonneg
  have hoffsetUpper : X - (ell0 : ℝ) * (u : ℝ) ≤ 44 * H := by
    have hraw : X - (ell0 : ℝ) * (u : ℝ) <
        (21 * (H / M) + 1) * (u : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hell0Lower huPos
      field_simp [huPos.ne'] at hmul ⊢
      linarith
    have huUpper := huData.2.2
    have hcoef0 : 0 ≤ 21 * (H / M) + 1 := by positivity
    have hbound : (21 * (H / M) + 1) * (u : ℝ) ≤
        (21 * (H / M) + 1) * (2 * M) :=
      mul_le_mul_of_nonneg_left huUpper hcoef0
    have hidentity : (21 * (H / M) + 1) * (2 * M) = 42 * H + 2 * M := by
      field_simp [hM.ne']
      ring
    rw [hidentity] at hbound
    linarith
  rw [show bilinearCommonLeftBase X (H / M) u = ell0 by rfl,
    abs_of_nonpos hoffsetNonpos]
  linarith

/-- The selected centres satisfy all input conditions for the second
recurrence, and the common-centre error is represented by an integer whenever
the source centre `X` is integral. -/
theorem bilinearSelectedCenters_secondRecurrenceSetup
    (d : ℕ) (hd : 1 ≤ d) (X H M ρ : ℝ)
    (hM : 1 ≤ M) (hs : 1 ≤ H / M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (U : Finset ℕ)
    (hUcenters : U ⊆ bilinearWindowCenters M)
    (hUcount : ρ ^ 4 * M / (4000 * bilinearInverseA d ρ⁻¹) ≤
      (U.card : ℝ))
    (X0 : ℤ) (hXint : X = (X0 : ℝ)) :
    U ⊆ Finset.Icc 1 (bilinearSecondRecurrenceLength M) ∧
    2 * (bilinearInverseZTwo d ρ⁻¹)⁻¹ *
        (bilinearSecondRecurrenceLength M : ℝ) ≤ (U.card : ℝ) ∧
    ∀ u ∈ U, ∃ h0 : ℤ,
      (bilinearCommonLeftBase X (H / M) u : ℝ) * (u : ℝ) - X = (h0 : ℝ) ∧
        |(h0 : ℝ)| ≤ 44 * H := by
  have hMpos : 0 < M := by linarith
  constructor
  · exact hUcenters.trans
      (bilinearWindowCenters_subset_secondRecurrenceRange M hMpos.le)
  constructor
  · exact (bilinearSecondRecurrence_density d hd M ρ hM hρ hρhalf).trans hUcount
  · intro u hu
    let h0 : ℤ := bilinearCommonLeftBase X (H / M) u * (u : ℤ) - X0
    refine ⟨h0, ?_, ?_⟩
    · dsimp [h0]
      rw [hXint]
      exact bilinearCommonCentre_offset_intCast X0
        (bilinearCommonLeftBase (X0 : ℝ) (H / M) u) u
    · have hoffset := bilinearCommonLeftBase_offset_bound X H M hMpos hs u
        (hUcenters hu)
      have heq :
          (bilinearCommonLeftBase X (H / M) u : ℝ) * (u : ℝ) - X =
            (h0 : ℝ) := by
        dsimp [h0]
        rw [hXint]
        exact bilinearCommonCentre_offset_intCast X0
          (bilinearCommonLeftBase (X0 : ℝ) (H / M) u) u
      rw [heq] at hoffset
      exact hoffset

#print axioms bilinearSecondRecurrenceLength_bounds
#print axioms bilinearSecondRecurrence_density
#print axioms bilinearCommonLeftBase_offset_bound
#print axioms bilinearSelectedCenters_secondRecurrenceSetup

end

end FractionalPrimes.Literature.Polynomial
