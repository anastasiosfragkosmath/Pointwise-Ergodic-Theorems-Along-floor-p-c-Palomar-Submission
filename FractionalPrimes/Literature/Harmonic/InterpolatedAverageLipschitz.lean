module

public import FractionalPrimes.Literature.Harmonic.InterpolatedUnweightedAverage
public import FractionalPrimes.WeightedLpAverages

/-!
# Lipschitz dependence of the interpolated averages on time

The finite averages have increments of size at most `2/(N+1)`. The
piecewise-linear interpolation therefore has the time modulus required by
the short-variation argument.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Successive finite averages differ by the new endpoint minus the old
average, divided by the new normalization. -/
theorem unweightedAverageLpCLM_succ_sub_endpoint {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : InvertibleSystem X) (c : ℝ) (N : ℕ)
    (hN : 1 ≤ N) :
    unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
        unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩ =
      (N + 1 : ℂ)⁻¹ •
        (floorPowerShiftLpCLM (p := p) S c (N + 1) -
          unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  simp only [sub_apply, smul_apply]
  have hnew := unweightedAverageLpCLM_apply_ae (p := p) S c
    ⟨N + 1, by omega⟩ f
  have hold := unweightedAverageLpCLM_apply_ae (p := p) S c ⟨N, hN⟩ f
  have hshift :
      (floorPowerShiftLpCLM (p := p) S c (N + 1) f : X → ℂ) =ᵐ[S.μ]
        S.shift (floorPower c (N + 1)) (f : X → ℂ) := by
    change (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
      (μ := S.μ) (μb := S.μ) ℂ
      (S.iterate (floorPower c (N + 1)))
      (InvertibleSystem.measurePreserving_integerIterate S
        (floorPower c (N + 1))) f : X → ℂ) =ᵐ[S.μ]
        S.shift (floorPower c (N + 1)) (f : X → ℂ)
    filter_upwards [Lp.coeFn_compMeasurePreserving f
      (InvertibleSystem.measurePreserving_integerIterate S
        (floorPower c (N + 1)))] with x hx
    simpa [InvertibleSystem.shift] using hx
  have hpoint := weightedAverage_succ_sub_endpoint S c
    (fun _ => (1 : ℂ)) (f : X → ℂ) N hN
  have hleftSub := Lp.coeFn_sub
    (unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ f)
    (unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩ f)
  have hrightSub := Lp.coeFn_sub
    (floorPowerShiftLpCLM (p := p) S c (N + 1) f)
    (unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩ f)
  have hrightSmul := Lp.coeFn_smul (N + 1 : ℂ)⁻¹
    (floorPowerShiftLpCLM (p := p) S c (N + 1) f -
      unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩ f)
  filter_upwards [hnew, hold, hshift, hleftSub, hrightSub, hrightSmul]
    with x hnew hold hshift hleftSub hrightSub hrightSmul
  rw [hleftSub]
  simp only [Pi.sub_apply]
  rw [hnew, hold]
  rw [hrightSmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hrightSub]
  simp only [Pi.sub_apply]
  rw [hshift, hold]
  simpa [unweightedAverage] using congrFun hpoint x

/-- The increment of `B_N` has the source's `2/(N+1)` operator norm bound. -/
theorem unweightedAverageLpCLM_succ_sub_norm_le {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : InvertibleSystem X) (c : ℝ) (N : ℕ)
    (hN : 1 ≤ N) :
    ‖unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
        unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩‖ ≤
      2 / (N + 1 : ℝ) := by
  rw [unweightedAverageLpCLM_succ_sub_endpoint (p := p) S c N hN,
    norm_smul]
  have hendpoint :
      ‖floorPowerShiftLpCLM (p := p) S c (N + 1)‖ ≤ 1 := by
    let iso := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
      (μ := S.μ) (μb := S.μ) ℂ
      (S.iterate (floorPower c (N + 1)))
      (InvertibleSystem.measurePreserving_integerIterate S
        (floorPower c (N + 1)))
    change ‖iso.toContinuousLinearMap‖ ≤ 1
    exact LinearIsometry.norm_toContinuousLinearMap_le iso
  have haverage := unweightedAverageLpCLM_norm_le_one (p := p) S c ⟨N, hN⟩
  have htriangle :
      ‖floorPowerShiftLpCLM (p := p) S c (N + 1) -
          unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩‖ ≤ 2 := by
    calc
      _ ≤ ‖floorPowerShiftLpCLM (p := p) S c (N + 1)‖ +
          ‖unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  have hscalar : ‖(N + 1 : ℂ)⁻¹‖ = (N + 1 : ℝ)⁻¹ := by
    rw [norm_inv]
    have hcast : (N + 1 : ℂ) = ((N + 1 : ℕ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_natCast]
    norm_cast
  rw [hscalar]
  have hden : 0 < (N + 1 : ℝ) := by positivity
  calc
    (N + 1 : ℝ)⁻¹ *
        ‖floorPowerShiftLpCLM (p := p) S c (N + 1) -
          unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩‖ ≤
      (N + 1 : ℝ)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left htriangle (by positivity)
    _ = 2 / (N + 1 : ℝ) := by field_simp

/-- On each unit interval beginning at an integer `N ≥ 1`, the interpolation
is affine with slope `B_(N+1) - B_N`. -/
theorem interpolatedUnweightedAverage_eq_affine_on_unit_interval
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : InvertibleSystem X) (c : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (s : ℝ)
    (hsN : (N : ℝ) ≤ s) (hsN1 : s ≤ N + 1) :
    interpolatedUnweightedAverage (p := p) S c s (by
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have hNposNat : 0 < N := by omega
        exact_mod_cast hNposNat
      exact lt_of_lt_of_le hNpos hsN) =
      unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩ +
        (s - N) •
          (unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
            unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩) := by
  by_cases hleft : s = N
  · subst s
    rw [interpolatedUnweightedAverage_at_integer (p := p) S c N hN]
    simp only [sub_self]
    module
  by_cases hright : s = N + 1
  · subst s
    have hcast : (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) := by norm_cast
    have hAt := interpolatedUnweightedAverage_at_integer (p := p) S c
      (N + 1) (by omega)
    have hvalue :
        interpolatedUnweightedAverage (p := p) S c ((N : ℝ) + 1) (by positivity) =
          unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ := by
      simpa only [← hcast] using hAt
    rw [hvalue]
    have hcoeff : (N : ℝ) + 1 - N = 1 := by ring
    rw [hcoeff, one_smul]
    module
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsone : 1 < s := by
    have hsNlt : (N : ℝ) < s := lt_of_le_of_ne hsN (Ne.symm hleft)
    linarith
  have hfloor : ⌊s⌋₊ = N := by
    apply Nat.le_antisymm
    · have hsupper : s < (N + 1 : ℝ) := by
        by_contra hnot
        apply hright
        apply le_antisymm hsN1
        exact le_of_not_gt hnot
      have hsupperNat : s < ((N + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hsupper
      have hlt : ⌊s⌋₊ < N + 1 :=
        (Nat.floor_lt (by linarith)).2 hsupperNat
      omega
    · exact Nat.le_floor (by exact_mod_cast hsN)
  unfold interpolatedUnweightedAverage
  rw [dite_eq_right (not_le_of_gt hsone)]
  simp only [hfloor]
  module

/-- The interpolation is constant on `(0,1]`. -/
theorem interpolatedUnweightedAverage_eq_one_of_le_one {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : InvertibleSystem X) (c t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    interpolatedUnweightedAverage (p := p) S c t ht =
      unweightedAverageLpCLM (p := p) S c ⟨1, by norm_num⟩ := by
  simp [interpolatedUnweightedAverage, ht1]

/-- At the right endpoint of a unit interval the interpolation equals the
next integer average. -/
theorem interpolatedUnweightedAverage_at_cast_succ {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : InvertibleSystem X) (c : ℝ) (N : ℕ) :
    interpolatedUnweightedAverage (p := p) S c ((N : ℝ) + 1) (by positivity) =
      unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ := by
  have hcast : (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) := by norm_cast
  simpa only [← hcast] using
    (interpolatedUnweightedAverage_at_integer (p := p) S c (N + 1) (by omega))

/-- The successor increment is bounded by `2/t` whenever its right endpoint
is no earlier than `t`. -/
private theorem unweightedAverageLpCLM_succ_sub_norm_le_of_le_time
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : InvertibleSystem X) (c t : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (ht : 0 < t) (htN : t ≤ N + 1) :
    ‖unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
        unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩‖ ≤ 2 / t := by
  have hrecip : 1 / (N + 1 : ℝ) ≤ 1 / t :=
    one_div_le_one_div_of_le ht htN
  calc
    ‖unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
        unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩‖ ≤ 2 / (N + 1 : ℝ) :=
      unweightedAverageLpCLM_succ_sub_norm_le (p := p) S c N hN
    _ = 2 * (1 / (N + 1 : ℝ)) := by ring
    _ ≤ 2 * (1 / t) := mul_le_mul_of_nonneg_left hrecip (by norm_num)
    _ = 2 / t := by ring

/-- For an increment of length at most one, at most one integer breakpoint is
crossed; the affine pieces and the finite-average increment bound give the
stronger modulus `2h/t`. -/
theorem interpolatedAverageLipschitz_local {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : InvertibleSystem X) (c t h : ℝ)
    (ht : 0 < t) (hh : 0 < h) (hh1 : h ≤ 1) :
    ‖interpolatedUnweightedAverage (p := p) S c (t + h) (by linarith) -
      interpolatedUnweightedAverage (p := p) S c t ht‖ ≤ 2 * h / t := by
  classical
  let u : ℝ := t + h
  let A := interpolatedUnweightedAverage (p := p) S c t ht
  let A' := interpolatedUnweightedAverage (p := p) S c u (by dsimp [u]; linarith)
  by_cases ht1 : t ≤ 1
  · by_cases hu1 : u ≤ 1
    · have hA : A = unweightedAverageLpCLM (p := p) S c ⟨1, by norm_num⟩ := by
        simpa [A] using interpolatedUnweightedAverage_eq_one_of_le_one S c t ht ht1
      have hA' : A' = unweightedAverageLpCLM (p := p) S c ⟨1, by norm_num⟩ := by
        simpa [A', u] using
          interpolatedUnweightedAverage_eq_one_of_le_one S c u (by dsimp [u]; linarith) hu1
      change ‖A' - A‖ ≤ 2 * h / t
      rw [hA', hA]
      simp
      positivity
    · have hu1lt : 1 < u := lt_of_not_ge hu1
      have hu2 : u ≤ 2 := by dsimp [u]; linarith
      have hu2' : u ≤ (1 : ℝ) + 1 := by
        have hnum : (1 : ℝ) + 1 = 2 := by norm_num
        rw [hnum]
        exact hu2
      have huLower : ((1 : ℕ) : ℝ) ≤ u := by exact_mod_cast hu1lt.le
      have huUpper : u ≤ ((1 : ℕ) : ℝ) + 1 := by
        have hcast : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1 := by norm_cast
        rw [hcast]
        exact hu2'
      have hAffine := interpolatedUnweightedAverage_eq_affine_on_unit_interval
        (p := p) S c 1 (by norm_num) u huLower huUpper
      have hA : A = unweightedAverageLpCLM (p := p) S c ⟨1, by norm_num⟩ := by
        simpa [A] using interpolatedUnweightedAverage_eq_one_of_le_one S c t ht ht1
      have hdecomp : A' - A = (u - 1) •
          (unweightedAverageLpCLM (p := p) S c ⟨2, by norm_num⟩ -
            unweightedAverageLpCLM (p := p) S c ⟨1, by norm_num⟩) := by
        change interpolatedUnweightedAverage (p := p) S c u (by dsimp [u]; linarith) -
          interpolatedUnweightedAverage (p := p) S c t ht = _
        rw [hAffine]
        have hAfun := interpolatedUnweightedAverage_eq_one_of_le_one
          (p := p) S c t ht ht1
        rw [hAfun]
        module
      have hstep : ‖unweightedAverageLpCLM (p := p) S c ⟨2, by norm_num⟩ -
          unweightedAverageLpCLM (p := p) S c ⟨1, by norm_num⟩‖ ≤ 1 := by
        have h := unweightedAverageLpCLM_succ_sub_norm_le (p := p) S c 1 (by norm_num)
        norm_num at h ⊢
        exact h
      have hcoef0 : 0 ≤ u - 1 := by dsimp [u]; linarith
      have hcoefh : u - 1 ≤ h := by dsimp [u]; linarith
      have hfactor : 1 ≤ 2 / t := by
        have hrecip := one_div_le_one_div_of_le ht ht1
        have hrecip' : 1 ≤ 1 / t := by simpa using hrecip
        calc
          (1 : ℝ) ≤ 2 * (1 / t) := by nlinarith
          _ = 2 / t := by ring
      calc
        ‖A' - A‖ = ‖(u - 1) •
            (unweightedAverageLpCLM (p := p) S c ⟨2, by norm_num⟩ -
              unweightedAverageLpCLM (p := p) S c ⟨1, by norm_num⟩)‖ := by rw [hdecomp]
        _ ≤ (u - 1) * 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef0]
          exact mul_le_mul_of_nonneg_left hstep hcoef0
        _ ≤ h * 1 := by nlinarith
        _ ≤ 2 * h / t := by
          have hmul := mul_le_mul_of_nonneg_left hfactor hh.le
          calc
            h * 1 ≤ h * (2 / t) := by simpa using hmul
            _ = 2 * h / t := by ring
  · have ht1lt : 1 < t := lt_of_not_ge ht1
    let N : ℕ := ⌊t⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      exact Nat.le_floor (by exact_mod_cast ht1lt.le)
    have htN : (N : ℝ) ≤ t := by
      dsimp [N]
      exact Nat.floor_le (by linarith)
    have htN1lt : t < (N : ℝ) + 1 := by
      dsimp [N]
      exact_mod_cast Nat.lt_floor_add_one t
    have htN1 : t ≤ (N : ℝ) + 1 := htN1lt.le
    have huN2 : u ≤ (N : ℝ) + 2 := by dsimp [u]; linarith
    by_cases huN1 : u ≤ (N : ℝ) + 1
    · have htAff := interpolatedUnweightedAverage_eq_affine_on_unit_interval
        (p := p) S c N hN t htN htN1
      have huAff := interpolatedUnweightedAverage_eq_affine_on_unit_interval
        (p := p) S c N hN u (by dsimp [u]; linarith) huN1
      have hdecomp : A' - A = h •
          (unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
            unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩) := by
        dsimp [A, A', u]
        rw [huAff, htAff]
        module
      have hstep := unweightedAverageLpCLM_succ_sub_norm_le_of_le_time
        (p := p) S c t N hN ht htN1
      calc
        ‖A' - A‖ = ‖h •
            (unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
              unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩)‖ := by rw [hdecomp]
        _ ≤ h * (2 / t) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh.le]
          exact mul_le_mul_of_nonneg_left hstep hh.le
        _ = 2 * h / t := by ring
    · have huN1gt : (N : ℝ) + 1 < u := lt_of_not_ge huN1
      let α : ℝ := (N : ℝ) + 1 - t
      let β : ℝ := u - ((N : ℝ) + 1)
      have hα : 0 ≤ α := by dsimp [α]; linarith
      have hβ : 0 ≤ β := by dsimp [β]; linarith
      have hsum : α + β = h := by dsimp [α, β, u]; ring
      have huLower : ((N + 1 : ℕ) : ℝ) ≤ u := by
        simpa only [Nat.cast_add, Nat.cast_one] using huN1gt.le
      have huUpper : u ≤ ((N + 1 : ℕ) : ℝ) + 1 := by
        have hcast : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 2 := by norm_cast
        rw [hcast]
        exact huN2
      have huAff := interpolatedUnweightedAverage_eq_affine_on_unit_interval
        (p := p) S c (N + 1) (by omega) u huLower huUpper
      have htAff := interpolatedUnweightedAverage_eq_affine_on_unit_interval
        (p := p) S c N hN t htN htN1
      have hdecomp : A' - A = α •
          (unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
            unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩) +
          β • (unweightedAverageLpCLM (p := p) S c ⟨N + 2, by omega⟩ -
            unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩) := by
        dsimp [A, A', u, α, β]
        rw [huAff, htAff]
        module
      have hstep₀ := unweightedAverageLpCLM_succ_sub_norm_le_of_le_time
        (p := p) S c t N hN ht htN1
      have hstep₁ := unweightedAverageLpCLM_succ_sub_norm_le_of_le_time
        (p := p) S c t (N + 1) (by omega) ht (by
          have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_cast
          rw [hcast]
          linarith)
      calc
        ‖A' - A‖ ≤
            α * ‖unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
              unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩‖ +
            β * ‖unweightedAverageLpCLM (p := p) S c ⟨N + 2, by omega⟩ -
              unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩‖ := by
          rw [hdecomp]
          calc
            _ ≤ ‖α • (unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
                unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩)‖ +
              ‖β • (unweightedAverageLpCLM (p := p) S c ⟨N + 2, by omega⟩ -
                unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩)‖ := norm_add_le _ _
            _ = α * ‖unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩ -
                unweightedAverageLpCLM (p := p) S c ⟨N, hN⟩‖ +
              β * ‖unweightedAverageLpCLM (p := p) S c ⟨N + 2, by omega⟩ -
                unweightedAverageLpCLM (p := p) S c ⟨N + 1, by omega⟩‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα,
                Real.norm_eq_abs, abs_of_nonneg hβ]
        _ ≤ α * (2 / t) + β * (2 / t) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hstep₀ hα)
            (mul_le_mul_of_nonneg_left hstep₁ hβ)
        _ = 2 * h / t := by rw [← add_mul, hsum]; ring

private theorem sum_range_successor_sub {E : Type*} [AddCommGroup E]
    [Module ℝ E] (F : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range n, (F (i + 1) - F i)) = F n - F 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      abel

/-- Finite subdivision into intervals of length at most one gives the global
`2h/t` modulus without an operator-valued differentiation argument. -/
private theorem interpolatedAverageLipschitz_global_two {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : InvertibleSystem X) (c t h : ℝ)
    (ht : 0 < t) (hh : 0 < h) :
    ‖interpolatedUnweightedAverage (p := p) S c (t + h) (by linarith) -
      interpolatedUnweightedAverage (p := p) S c t ht‖ ≤ 2 * h / t := by
  classical
  let n : ℕ := ⌊h⌋₊ + 1
  have hnpos : 0 < n := by dsimp [n]; omega
  have hhn : h ≤ (n : ℝ) := by
    dsimp [n]
    have hlt := Nat.lt_floor_add_one h
    exact_mod_cast hlt.le
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let δ : ℝ := h / (n : ℝ)
  have hδpos : 0 < δ := div_pos hh hnreal
  have hδle : δ ≤ 1 := (div_le_one hnreal).2 hhn
  have hendpoint : (n : ℝ) * δ = h := by
    dsimp [δ]
    field_simp [ne_of_gt hnreal]
  let τ : ℕ → ℝ := fun i => t + (i : ℝ) * δ
  have hτpos (i : ℕ) : 0 < τ i := by
    dsimp [τ]
    positivity
  let F : ℕ → (Lp ℂ p S.μ →L[ℂ] Lp ℂ p S.μ) := fun i =>
    interpolatedUnweightedAverage (p := p) S c (τ i) (hτpos i)
  have htime (i : ℕ) : τ (i + 1) = τ i + δ := by
    dsimp [τ]
    push_cast
    ring
  have hstep (i : ℕ) :
      ‖F (i + 1) - F i‖ ≤ 2 * δ / τ i := by
    have hlocal := interpolatedAverageLipschitz_local (p := p) S c (τ i) δ
      (hτpos i) hδpos hδle
    simpa [F, htime i] using hlocal
  have hstep' (i : ℕ) : ‖F (i + 1) - F i‖ ≤ 2 * δ / t := by
    have htτ : t ≤ τ i := by
      dsimp [τ]
      have hi : 0 ≤ (i : ℝ) := by positivity
      nlinarith [mul_nonneg hi hδpos.le]
    have hrecip : 1 / (τ i) ≤ 1 / t :=
      one_div_le_one_div_of_le ht htτ
    calc
      ‖F (i + 1) - F i‖ ≤ 2 * δ / τ i := hstep i
      _ = (2 * δ) * (1 / τ i) := by ring
      _ ≤ (2 * δ) * (1 / t) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 2 * δ / t := by ring
  have hsumle :
      (∑ i ∈ Finset.range n, ‖F (i + 1) - F i‖) ≤
        ∑ _i ∈ Finset.range n, (2 * δ / t) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hstep' i
  have hsumconst :
      (∑ _i ∈ Finset.range n, (2 * δ / t)) = (n : ℝ) * (2 * δ / t) := by
    simp
  have htel := sum_range_successor_sub F n
  have hleft : F 0 = interpolatedUnweightedAverage (p := p) S c t ht := by
    simp [F, τ]
  have hright :
      F n = interpolatedUnweightedAverage (p := p) S c (t + h) (by linarith) := by
    change interpolatedUnweightedAverage (p := p) S c (t + (n : ℝ) * δ)
      (hτpos n) = _
    have htimes : t + (n : ℝ) * δ = t + h := congrArg (fun z : ℝ => t + z) hendpoint
    simpa only [htimes]
  calc
    ‖interpolatedUnweightedAverage (p := p) S c (t + h) (by linarith) -
        interpolatedUnweightedAverage (p := p) S c t ht‖ = ‖F n - F 0‖ := by
      rw [hright, hleft]
    _ = ‖∑ i ∈ Finset.range n, (F (i + 1) - F i)‖ := by rw [htel]
    _ ≤ ∑ i ∈ Finset.range n, ‖F (i + 1) - F i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range n, (2 * δ / t) := hsumle
    _ = (n : ℝ) * (2 * δ / t) := hsumconst
    _ = 2 * h / t := by rw [← hendpoint]; ring

/-- Smoothness in time for the exact interpolated averages in `ha:time`.
This is the source's all-`p`, all-positive-`t,h` estimate. -/
theorem interpolatedAverageLipschitz {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : InvertibleSystem X) (c t h : ℝ)
    (ht : 0 < t) (hh : 0 < h) :
    ‖interpolatedUnweightedAverage (p := p) S c (t + h) (by linarith) -
      interpolatedUnweightedAverage (p := p) S c t ht‖ ≤ 4 * h / t := by
  calc
    _ ≤ 2 * h / t := interpolatedAverageLipschitz_global_two S c t h ht hh
    _ ≤ 4 * h / t := by
      have hq : 0 ≤ h / t := div_nonneg hh.le ht.le
      calc
        2 * h / t = 2 * (h / t) := by ring
        _ ≤ 4 * (h / t) := by nlinarith
        _ = 4 * h / t := by ring

end

end FractionalPrimes

end
