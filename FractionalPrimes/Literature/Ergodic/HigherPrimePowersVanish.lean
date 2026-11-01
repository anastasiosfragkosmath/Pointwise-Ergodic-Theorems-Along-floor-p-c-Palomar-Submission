module

public import FractionalPrimes.Literature.Ergodic.PrimePartsDecomposition
public import FractionalPrimes.LpAverages
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Vanishing of the higher-prime-power remainder

This file proves the `Lᵖ` and almost-everywhere vanishing parts of blueprint
`er:primepowers`, using the exact finite operator and coefficient sum from
`PrimePartsDecomposition.lean`.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology
open scoped Nat.Prime

namespace FractionalPrimes

noncomputable section

private def paperHigherPowerExponentSet (N : Scale) : Finset ℕ :=
  (Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊).filter (fun k => 2 ≤ k)

private def paperHigherPowerPrimeSet (N : Scale) (k : ℕ) : Finset ℕ :=
  (Finset.Icc 0 ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter
    (fun p => Nat.Prime p ∧ p ^ k ≤ N.1)

private def paperHigherPowerRawAbsPart {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) : X → ℝ :=
  fun x =>
    ∑ k ∈ paperHigherPowerExponentSet N,
      ∑ p ∈ paperHigherPowerPrimeSet N k,
        Real.log (p : ℝ) * ‖f (S.iterate (floorPower c (p ^ k)) x)‖

private def paperHigherPowerCoefficientSum (N : Scale) : ℝ :=
  ∑ k ∈ paperHigherPowerExponentSet N,
    ∑ p ∈ paperHigherPowerPrimeSet N k, Real.log (p : ℝ)

/-- Positive majorant for the pointwise absolute value of the higher-power
operator, with precisely the same finite prime-power indices. -/
private def paperHigherPowerAbsPart {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) : X → ℝ :=
  fun x => (N.1 : ℝ)⁻¹ * paperHigherPowerRawAbsPart S c f N x

private def paperHigherPowerFourthScale (k : ℕ) : Scale :=
  ⟨4 ^ (k + 1), by positivity⟩

private theorem paperHigherPowerFourthScale_mass_le (k : ℕ) :
    paperHigherPrimePowerMass (paperHigherPowerFourthScale k) ≤
      (4 * Real.log 2) *
        (((k + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k + 1)) := by
  have hscale4 : 4 ≤ (paperHigherPowerFourthScale k).1 := by
    dsimp [paperHigherPowerFourthScale]
    have hone : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
    simpa [Nat.pow_succ] using Nat.mul_le_mul_right 4 hone
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowCast :
      ((paperHigherPowerFourthScale k).1 : ℝ) = (4 : ℝ) ^ (k + 1) := by
    simp [paperHigherPowerFourthScale, Nat.cast_pow]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogScale :
      Real.log ((paperHigherPowerFourthScale k).1 : ℝ) =
        2 * ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [hpowCast, Real.log_pow, hlog4]
    ring
  have hsquare : (4 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
    ring
  have hsqrtScale :
      Real.sqrt ((paperHigherPowerFourthScale k).1 : ℝ) = (2 : ℝ) ^ (k + 1) := by
    rw [hpowCast, hsquare, Real.sqrt_sq (by positivity)]
  calc
    paperHigherPrimePowerMass (paperHigherPowerFourthScale k) ≤
        Real.log ((paperHigherPowerFourthScale k).1 : ℝ) ^ 2 /
          (Real.log 2 * Real.sqrt ((paperHigherPowerFourthScale k).1 : ℝ)) :=
      paperHigherPrimePowerMass_le (by omega)
    _ = (4 * Real.log 2) *
          (((k + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k + 1)) := by
      rw [hlogScale, hsqrtScale]
      rw [one_div_pow]
      field_simp [ne_of_gt hlog2]
      ring

private theorem paperHigherPowerFourthScale_mass_summable :
    Summable (fun k : ℕ =>
      paperHigherPrimePowerMass (paperHigherPowerFourthScale k)) := by
  have hbase : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
  have hshift : Summable (fun k : ℕ =>
      ((k + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k + 1)) := by
    have h := (summable_nat_add_iff
      (f := fun k : ℕ => (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hmajor : Summable (fun k : ℕ =>
      (4 * Real.log 2) * (((k + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k + 1))) :=
    hshift.mul_left (4 * Real.log 2)
  apply Summable.of_nonneg_of_le
  · intro k
    exact paperHigherPrimePowerMass_nonneg (paperHigherPowerFourthScale k)
  · intro k
    exact paperHigherPowerFourthScale_mass_le k
  · exact hmajor

private theorem paperHigherPrimePowerMass_tendsto_zero :
    Tendsto (fun N : Scale => paperHigherPrimePowerMass N) atTop (𝓝 0) := by
  have hscaleNat : Tendsto (fun N : Scale => N.1) atTop atTop := by
    have hmap : Filter.map (fun N : Scale => N.1) atTop = atTop :=
      map_val_atTop_of_Ici_subset (a := (1 : ℕ))
        (s := {n : ℕ | 0 < n}) (by
          intro n hn
          change 1 ≤ n at hn
          exact lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn)
    change Filter.map (fun N : Scale => N.1) atTop ≤ atTop
    rw [hmap]
  have hscaleAtTop : Tendsto (fun N : Scale => (N.1 : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp hscaleNat
  have hsmallReal : Tendsto
      (fun x : ℝ => (Real.log x) ^ (2 : ℝ) / Real.sqrt x)
      atTop (𝓝 0) := by
    have h := (paper_log_rpow_isLittleO_rpow (a := 2) (b := 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simpa [Real.sqrt_eq_rpow] using h
  have hsmallScale : Tendsto
      (fun N : Scale => (Real.log (N.1 : ℝ)) ^ 2 / Real.sqrt (N.1 : ℝ))
      atTop (𝓝 0) := by
    have h := hsmallReal.comp hscaleAtTop
    convert h using 1
    ext N
    simp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmajor : Tendsto
      (fun N : Scale =>
        ((Real.log (N.1 : ℝ)) ^ 2 / Real.sqrt (N.1 : ℝ)) / Real.log 2)
      atTop (𝓝 0) := by
    simpa [hlog2.ne'] using hsmallScale.div_const (Real.log 2)
  have hnonneg : ∀ N : Scale, 0 ≤ paperHigherPrimePowerMass N :=
    paperHigherPrimePowerMass_nonneg
  have hNlarge : ∀ᶠ N : Scale in atTop, 2 ≤ N.1 :=
    hscaleNat.eventually_ge_atTop 2
  have hbound : ∀ᶠ N : Scale in atTop,
      paperHigherPrimePowerMass N ≤
        ((Real.log (N.1 : ℝ)) ^ 2 / Real.sqrt (N.1 : ℝ)) / Real.log 2 := by
    filter_upwards [hNlarge] with N hN
    have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
    have hsqrtpos : 0 < Real.sqrt (N.1 : ℝ) := Real.sqrt_pos.2 hNpos
    have hmass := paperHigherPrimePowerMass_le hN
    calc
      paperHigherPrimePowerMass N ≤
          (Real.log (N.1 : ℝ)) ^ 2 /
            (Real.log 2 * Real.sqrt (N.1 : ℝ)) := hmass
      _ = ((Real.log (N.1 : ℝ)) ^ 2 / Real.sqrt (N.1 : ℝ)) /
            Real.log 2 := by
        field_simp [ne_of_gt hsqrtpos, ne_of_gt hlog2]
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hbound hmajor

private theorem tendsto_paperHigherPowerLog_four_atTop :
    Tendsto (fun N : Scale => Nat.log 4 N.1) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro k
  refine Filter.eventually_atTop.2 ⟨paperHigherPowerFourthScale k, ?_⟩
  intro N hN
  have hscale : 4 ^ (k + 1) ≤ N.1 := by exact_mod_cast hN
  have hpow : 4 ^ k ≤ 4 ^ (k + 1) := by
    gcongr
    omega
  exact Nat.le_log_of_pow_le (by norm_num) (hpow.trans hscale)

private theorem paperHigherPowerCoefficientSum_eq_pairSum (N : Scale) :
    paperHigherPowerCoefficientSum N = paperHigherPrimePowerPairSum N.1 := by
  unfold paperHigherPowerCoefficientSum paperHigherPrimePowerPairSum
    paperHigherPowerExponentSet paperHigherPowerPrimeSet
  have hset :
      (Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊).filter
          (fun k => 2 ≤ k) =
        Finset.Icc 2 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hset]

private theorem paperHigherPowerAbsPart_nonneg
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) (N : Scale) (x : X) :
    0 ≤ paperHigherPowerAbsPart S c f N x := by
  unfold paperHigherPowerAbsPart paperHigherPowerRawAbsPart
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg
  · have hp' := (Finset.mem_filter.mp hp).2.1
    exact Real.log_nonneg (by exact_mod_cast hp'.one_le)
  · exact norm_nonneg _

private theorem paperHigherPowerRawAbsPart_nonneg
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) (N : Scale) (x : X) :
    0 ≤ paperHigherPowerRawAbsPart S c f N x := by
  unfold paperHigherPowerRawAbsPart
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg
  · have hp' := (Finset.mem_filter.mp hp).2.1
    exact Real.log_nonneg (by exact_mod_cast hp'.one_le)
  · exact norm_nonneg _

private theorem paperHigherPowerExponentSet_mono {N M : Scale}
    (hNM : N.1 ≤ M.1) :
    paperHigherPowerExponentSet N ⊆ paperHigherPowerExponentSet M := by
  have hNMreal : (N.1 : ℝ) ≤ (M.1 : ℝ) := by exact_mod_cast hNM
  have hlogN : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogmono := Real.log_le_log hlogN hNMreal
  have hquotient := div_le_div_of_nonneg_right hlogmono hlog2.le
  have hfloor := Nat.floor_mono hquotient
  intro k hk
  simp only [paperHigherPowerExponentSet, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
  exact ⟨⟨hk.1.1, hk.1.2.trans hfloor⟩, hk.2⟩

private theorem paperHigherPowerPrimeSet_mono {N M : Scale}
    (hNM : N.1 ≤ M.1) {k : ℕ}
    (hk : k ∈ paperHigherPowerExponentSet N) :
    paperHigherPowerPrimeSet N k ⊆ paperHigherPowerPrimeSet M k := by
  have hkpos : 0 < k := by
    have hk' := (Finset.mem_filter.mp hk).2
    omega
  have hNMreal : (N.1 : ℝ) ≤ (M.1 : ℝ) := by exact_mod_cast hNM
  have hroot : (N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) ≤
      (M.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) :=
    Real.rpow_le_rpow (by positivity) hNMreal (by positivity)
  have hfloor := Nat.floor_mono hroot
  intro p hp
  simp only [paperHigherPowerPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hfloor⟩, hp.2.1, hp.2.2.trans hNM⟩

private theorem paperHigherPowerRawAbsPart_mono {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) {N M : Scale}
    (hNM : N.1 ≤ M.1) (x : X) :
    paperHigherPowerRawAbsPart S c f N x ≤ paperHigherPowerRawAbsPart S c f M x := by
  classical
  unfold paperHigherPowerRawAbsPart
  calc
    (∑ k ∈ paperHigherPowerExponentSet N,
      ∑ p ∈ paperHigherPowerPrimeSet N k,
        Real.log (p : ℝ) * ‖f (S.iterate (floorPower c (p ^ k)) x)‖) ≤
      ∑ k ∈ paperHigherPowerExponentSet N,
        ∑ p ∈ paperHigherPowerPrimeSet M k,
          Real.log (p : ℝ) * ‖f (S.iterate (floorPower c (p ^ k)) x)‖ := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (paperHigherPowerPrimeSet_mono hNM hk)
      intro p hp hpn
      apply mul_nonneg
      · have hp' := (Finset.mem_filter.mp hp).2.1
        exact Real.log_nonneg (by exact_mod_cast hp'.one_le)
      · exact norm_nonneg _
    _ ≤ ∑ k ∈ paperHigherPowerExponentSet M,
        ∑ p ∈ paperHigherPowerPrimeSet M k,
          Real.log (p : ℝ) * ‖f (S.iterate (floorPower c (p ^ k)) x)‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (paperHigherPowerExponentSet_mono hNM)
      intro k hk hkn
      apply Finset.sum_nonneg
      intro p hp
      apply mul_nonneg
      · have hp' := (Finset.mem_filter.mp hp).2.1
        exact Real.log_nonneg (by exact_mod_cast hp'.one_le)
      · exact norm_nonneg _

private theorem paperHigherPowerAbsPart_le_four_of_scale
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) {N M : Scale}
    (hNM : N.1 ≤ M.1) (hM4N : M.1 ≤ 4 * N.1) (x : X) :
    paperHigherPowerAbsPart S c f N x ≤
      4 * paperHigherPowerAbsPart S c f M x := by
  have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hMpos : 0 < (M.1 : ℝ) := by exact_mod_cast M.2
  have hM4Nreal : (M.1 : ℝ) ≤ 4 * (N.1 : ℝ) := by exact_mod_cast hM4N
  have hinv : (N.1 : ℝ)⁻¹ ≤ 4 * (M.1 : ℝ)⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv]
    rw [div_le_div_iff₀ hNpos hMpos]
    nlinarith
  change (N.1 : ℝ)⁻¹ * paperHigherPowerRawAbsPart S c f N x ≤
    4 * ((M.1 : ℝ)⁻¹ * paperHigherPowerRawAbsPart S c f M x)
  calc
    (N.1 : ℝ)⁻¹ * paperHigherPowerRawAbsPart S c f N x ≤
        (N.1 : ℝ)⁻¹ * paperHigherPowerRawAbsPart S c f M x :=
      mul_le_mul_of_nonneg_left
        (paperHigherPowerRawAbsPart_mono S c f hNM x)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (4 * (M.1 : ℝ)⁻¹) * paperHigherPowerRawAbsPart S c f M x :=
      mul_le_mul_of_nonneg_right hinv
        (paperHigherPowerRawAbsPart_nonneg S c f M x)
    _ = 4 * ((M.1 : ℝ)⁻¹ * paperHigherPowerRawAbsPart S c f M x) := by ring

private theorem aestronglyMeasurable_paperHigherPrimePowerPart
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) (N : Scale)
    (hf : AEStronglyMeasurable f S.μ) :
    AEStronglyMeasurable (paperHigherPrimePowerPart S c f N) S.μ := by
  classical
  unfold paperHigherPrimePowerPart
  have hsum : AEStronglyMeasurable
      (fun x => ∑ k ∈ (Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊).filter
          (fun k => 2 ≤ k),
        ∑ p ∈ (Finset.Ioc 0
            ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime,
          (Real.log (p : ℝ) : ℂ) * f (S.iterate (floorPower c (p ^ k)) x)) S.μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro k hk
    have hinner := Finset.aestronglyMeasurable_fun_sum
      ((Finset.Ioc 0 ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime)
      (fun p _ => by
        have hshift := aestronglyMeasurable_shift_floorPower S c (p ^ k) hf
        simpa only [smul_eq_mul, S.shift_floorPower_apply] using
          hshift.const_smul (Real.log (p : ℝ) : ℂ))
    convert hinner using 1
    ext x
    rfl
  exact hsum.const_mul ((N.1 : ℂ)⁻¹)

private theorem norm_paperHigherPrimePowerPart_le_absPart
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) (N : Scale) (x : X) :
    ‖paperHigherPrimePowerPart S c f N x‖ ≤ paperHigherPowerAbsPart S c f N x := by
  classical
  have hscale : ‖(N.1 : ℂ)⁻¹‖ = (N.1 : ℝ)⁻¹ := by
    simp [norm_inv]
  have hlog (p : ℕ) (hp : Nat.Prime p) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hlogNorm (p : ℕ) (hp : Nat.Prime p) :
      ‖(Real.log (p : ℝ) : ℂ)‖ = Real.log (p : ℝ) := by
    calc
      ‖(Real.log (p : ℝ) : ℂ)‖ = |Real.log (p : ℝ)| := RCLike.norm_ofReal _
      _ = Real.log (p : ℝ) := abs_of_nonneg (hlog p hp)
  have hterm (k p : ℕ) (hp : Nat.Prime p) :
      ‖(Real.log (p : ℝ) : ℂ) * f (S.iterate (floorPower c (p ^ k)) x)‖ ≤
        Real.log (p : ℝ) * ‖f (S.iterate (floorPower c (p ^ k)) x)‖ := by
    rw [norm_mul, hlogNorm p hp]
  let K : Finset ℕ := paperHigherPowerExponentSet N
  let P : ℕ → Finset ℕ := fun k =>
    (Finset.Ioc 0 ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime
  have hindexSet (k : ℕ) (hk : k ∈ K) :
      P k = paperHigherPowerPrimeSet N k := by
    exact paperPrimeRootFilter_eq_primePowerFilter (N := N.1) (k := k) (by
      have hk' := (Finset.mem_filter.mp hk).2
      omega)
  have hsumBound :
      ‖∑ k ∈ K, ∑ p ∈ P k,
          (Real.log (p : ℝ) : ℂ) * f (S.iterate (floorPower c (p ^ k)) x)‖ ≤
        ∑ k ∈ K, ∑ p ∈ P k,
          Real.log (p : ℝ) * ‖f (S.iterate (floorPower c (p ^ k)) x)‖ := by
    calc
      ‖∑ k ∈ K, ∑ p ∈ P k,
          (Real.log (p : ℝ) : ℂ) * f (S.iterate (floorPower c (p ^ k)) x)‖ ≤
        ∑ k ∈ K, ‖∑ p ∈ P k,
          (Real.log (p : ℝ) : ℂ) * f (S.iterate (floorPower c (p ^ k)) x)‖ :=
        norm_sum_le K _
      _ ≤ ∑ k ∈ K, ∑ p ∈ P k,
          Real.log (p : ℝ) * ‖f (S.iterate (floorPower c (p ^ k)) x)‖ := by
        apply Finset.sum_le_sum
        intro k hk
        calc
          ‖∑ p ∈ P k, (Real.log (p : ℝ) : ℂ) *
              f (S.iterate (floorPower c (p ^ k)) x)‖ ≤
            ∑ p ∈ P k, ‖(Real.log (p : ℝ) : ℂ) *
              f (S.iterate (floorPower c (p ^ k)) x)‖ := norm_sum_le (P k) _
          _ ≤ ∑ p ∈ P k, Real.log (p : ℝ) *
              ‖f (S.iterate (floorPower c (p ^ k)) x)‖ := by
            apply Finset.sum_le_sum
            intro p hp
            exact hterm k p (Finset.mem_filter.mp hp).2
  have hrealIndex :
      (∑ k ∈ K, ∑ p ∈ P k,
        Real.log (p : ℝ) * ‖f (S.iterate (floorPower c (p ^ k)) x)‖) =
      (∑ k ∈ K, ∑ p ∈ paperHigherPowerPrimeSet N k,
        Real.log (p : ℝ) * ‖f (S.iterate (floorPower c (p ^ k)) x)‖) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hindexSet k hk]
  have hcomplexIndex :
      paperHigherPrimePowerPart S c f N x =
        (N.1 : ℂ)⁻¹ *
          ∑ k ∈ K, ∑ p ∈ P k,
            (Real.log (p : ℝ) : ℂ) * f (S.iterate (floorPower c (p ^ k)) x) := by
    unfold paperHigherPrimePowerPart
    have hsumIndex :
      (∑ k ∈ Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊ with 2 ≤ k,
        ∑ p ∈ Finset.Ioc 0
            ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
          (Real.log (p : ℝ) : ℂ) * f (S.iterate (floorPower c (p ^ k)) x)) =
        (∑ k ∈ K, ∑ p ∈ P k,
          (Real.log (p : ℝ) : ℂ) * f (S.iterate (floorPower c (p ^ k)) x)) := by
      simp only [Finset.sum_filter, K, P, paperHigherPowerExponentSet]
    rw [hsumIndex]
  rw [hcomplexIndex, norm_mul, hscale]
  unfold paperHigherPowerAbsPart paperHigherPowerRawAbsPart
  rw [← hrealIndex]
  exact mul_le_mul_of_nonneg_left hsumBound
    (inv_nonneg.mpr (Nat.cast_nonneg _))

private theorem paperHigherPowerCoefficientSum_ofReal (N : Scale) :
    ENNReal.ofReal (paperHigherPowerCoefficientSum N) =
      ∑ k ∈ paperHigherPowerExponentSet N,
        ∑ p ∈ paperHigherPowerPrimeSet N k, ENNReal.ofReal (Real.log (p : ℝ)) := by
  unfold paperHigherPowerCoefficientSum
  rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => by
    apply Finset.sum_nonneg
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2.1
    exact Real.log_nonneg (by exact_mod_cast hp'.one_le))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ENNReal.ofReal_sum_of_nonneg (fun p hp => by
    have hp' := (Finset.mem_filter.mp hp).2.1
    exact Real.log_nonneg (by exact_mod_cast hp'.one_le))]

set_option maxHeartbeats 5000000 in
private theorem eLpNorm_paperHigherPowerAbsPart_le
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) (N : Scale) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : MemLp f p S.μ) :
    eLpNorm (paperHigherPowerAbsPart S c f N) p S.μ ≤
      ENNReal.ofReal (paperHigherPrimePowerMass N) * eLpNorm f p S.μ := by
  classical
  let K := paperHigherPowerExponentSet N
  let P := paperHigherPowerPrimeSet N
  let hFun : X → ℝ := fun x =>
    ∑ k ∈ K, ∑ q ∈ P k,
      Real.log (q : ℝ) * ‖f (S.iterate (floorPower c (q ^ k)) x)‖
  have hshiftNorm (n : ℕ) :
      eLpNorm (fun x => ‖f (S.iterate (floorPower c n) x)‖) p S.μ =
        eLpNorm f p S.μ := by
    calc
      eLpNorm (fun x => ‖f (S.iterate (floorPower c n) x)‖) p S.μ =
          eLpNorm (fun x => ‖S.shift (floorPower c n) f x‖) p S.μ := by
        congr 1
      _ = eLpNorm (S.shift (floorPower c n) f) p S.μ :=
        eLpNorm_norm (S.shift (floorPower c n) f)
          (aestronglyMeasurable_shift_floorPower S c n hf.aestronglyMeasurable)
      _ = eLpNorm f p S.μ := eLpNorm_shift_floorPower S c n hf.aestronglyMeasurable
  have htermNorm (k q : ℕ) (hq : q ∈ P k) :
      eLpNorm (fun x => Real.log (q : ℝ) *
        ‖f (S.iterate (floorPower c (q ^ k)) x)‖) p S.μ =
        ENNReal.ofReal (Real.log (q : ℝ)) * eLpNorm f p S.μ := by
    have hlog : 0 ≤ Real.log (q : ℝ) := by
      have hq' := (Finset.mem_filter.mp hq).2.1
      exact Real.log_nonneg (by exact_mod_cast hq'.one_le)
    rw [show (fun x => Real.log (q : ℝ) *
        ‖f (S.iterate (floorPower c (q ^ k)) x)‖) =
        (Real.log (q : ℝ)) •
          (fun x => ‖f (S.iterate (floorPower c (q ^ k)) x)‖) by
          funext x
          simp [smul_eq_mul]]
    rw [eLpNorm_const_smul, hshiftNorm]
    rw [Real.enorm_of_nonneg hlog]
  have hinner (k : ℕ) :
      eLpNorm (fun x => ∑ q ∈ P k,
        Real.log (q : ℝ) * ‖f (S.iterate (floorPower c (q ^ k)) x)‖) p S.μ ≤
        ∑ q ∈ P k, ENNReal.ofReal (Real.log (q : ℝ)) * eLpNorm f p S.μ := by
    calc
      eLpNorm (fun x => ∑ q ∈ P k,
          Real.log (q : ℝ) * ‖f (S.iterate (floorPower c (q ^ k)) x)‖) p S.μ ≤
          ∑ q ∈ P k, eLpNorm (fun x => Real.log (q : ℝ) *
            ‖f (S.iterate (floorPower c (q ^ k)) x)‖) p S.μ := by
        have htriangle := eLpNorm_sum_le (μ := S.μ) (p := p)
          (f := fun (q : ℕ) (x : X) => Real.log (q : ℝ) *
            ‖f (S.iterate (floorPower c (q ^ k)) x)‖) (s := P k) hp
        have hsumFun :
            (fun x => ∑ q ∈ P k, Real.log (q : ℝ) *
              ‖f (S.iterate (floorPower c (q ^ k)) x)‖) =
              ∑ q ∈ P k, (fun x => Real.log (q : ℝ) *
                ‖f (S.iterate (floorPower c (q ^ k)) x)‖) := by
          funext x
          simp only [Finset.sum_apply]
        rw [hsumFun]
        exact htriangle
      _ = ∑ q ∈ P k,
          ENNReal.ofReal (Real.log (q : ℝ)) * eLpNorm f p S.μ := by
        apply Finset.sum_congr rfl
        intro q hq
        exact htermNorm k q hq
  have hcoef :
      (∑ k ∈ K, ∑ q ∈ P k,
          ENNReal.ofReal (Real.log (q : ℝ))) =
        ENNReal.ofReal (paperHigherPowerCoefficientSum N) := by
    rw [paperHigherPowerCoefficientSum_ofReal]
  have hmass : paperHigherPrimePowerMass N =
      (N.1 : ℝ)⁻¹ * paperHigherPowerCoefficientSum N := by
    unfold paperHigherPrimePowerMass
    rw [paperHigherPowerCoefficientSum_eq_pairSum]
  have hInvNorm : ‖(N.1 : ℝ)⁻¹‖ₑ = ENNReal.ofReal ((N.1 : ℝ)⁻¹) := by
    exact Real.enorm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hfactor :
      (∑ k ∈ K, ∑ q ∈ P k,
          ENNReal.ofReal (Real.log (q : ℝ)) * eLpNorm f p S.μ) =
        ENNReal.ofReal (paperHigherPowerCoefficientSum N) * eLpNorm f p S.μ := by
    calc
      (∑ k ∈ K, ∑ q ∈ P k,
          ENNReal.ofReal (Real.log (q : ℝ)) * eLpNorm f p S.μ) =
          ∑ k ∈ K, (∑ q ∈ P k, ENNReal.ofReal (Real.log (q : ℝ))) *
            eLpNorm f p S.μ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.sum_mul]
      _ = (∑ k ∈ K, ∑ q ∈ P k, ENNReal.ofReal (Real.log (q : ℝ))) *
          eLpNorm f p S.μ := by rw [← Finset.sum_mul]
      _ = ENNReal.ofReal (paperHigherPowerCoefficientSum N) *
          eLpNorm f p S.μ := by rw [hcoef]
  have hsumFunOuter :
      hFun = ∑ k ∈ K, (fun x => ∑ q ∈ P k,
        Real.log (q : ℝ) * ‖f (S.iterate (floorPower c (q ^ k)) x)‖) := by
    funext x
    simp only [hFun, Finset.sum_apply]
  change eLpNorm ((N.1 : ℝ)⁻¹ • hFun) p S.μ ≤ _
  rw [eLpNorm_const_smul]
  calc
    ‖(N.1 : ℝ)⁻¹‖ₑ * eLpNorm hFun p S.μ ≤
        ‖(N.1 : ℝ)⁻¹‖ₑ *
          ∑ k ∈ K, eLpNorm (fun x => ∑ q ∈ P k,
            Real.log (q : ℝ) * ‖f (S.iterate (floorPower c (q ^ k)) x)‖) p S.μ :=
      mul_le_mul_of_nonneg_left (by
        rw [hsumFunOuter]
        exact eLpNorm_sum_le hp) bot_le
    _ ≤ ‖(N.1 : ℝ)⁻¹‖ₑ *
          ∑ k ∈ K, ∑ q ∈ P k,
            ENNReal.ofReal (Real.log (q : ℝ)) * eLpNorm f p S.μ := by
      apply mul_le_mul_of_nonneg_left _ bot_le
      exact Finset.sum_le_sum fun k hk => hinner k
    _ = ENNReal.ofReal (paperHigherPrimePowerMass N) * eLpNorm f p S.μ := by
      rw [hInvNorm]
      rw [hfactor, ← mul_assoc, ← ENNReal.ofReal_mul
        (inv_nonneg.mpr (Nat.cast_nonneg _)), hmass]

theorem eLpNorm_paperHigherPrimePowerPart_tendsto_zero
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (_hpTop : p ≠ ∞) (hf : MemLp f p S.μ) :
    Tendsto (fun N : Scale =>
      eLpNorm (paperHigherPrimePowerPart S c f N) p S.μ) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun N : Scale =>
      ENNReal.ofReal (paperHigherPrimePowerMass N) * eLpNorm f p S.μ)
      atTop (𝓝 0) := by
    have hmass := ENNReal.tendsto_ofReal paperHigherPrimePowerMass_tendsto_zero
    have hconst : Tendsto (fun _ : Scale => eLpNorm f p S.μ) atTop
        (𝓝 (eLpNorm f p S.μ)) := tendsto_const_nhds
    simpa using ENNReal.Tendsto.mul hmass
      (Or.inr hf.eLpNorm_ne_top) hconst
      (Or.inr (by simp : ENNReal.ofReal (0 : ℝ) ≠ ∞))
  have hbound : ∀ N : Scale,
      eLpNorm (paperHigherPrimePowerPart S c f N) p S.μ ≤
        ENNReal.ofReal (paperHigherPrimePowerMass N) * eLpNorm f p S.μ := by
    intro N
    calc
      eLpNorm (paperHigherPrimePowerPart S c f N) p S.μ ≤
          eLpNorm (paperHigherPowerAbsPart S c f N) p S.μ :=
        eLpNorm_mono_real
          (aestronglyMeasurable_paperHigherPrimePowerPart S c f N
            hf.aestronglyMeasurable)
          (fun x => norm_paperHigherPrimePowerPart_le_absPart S c f N x)
      _ ≤ ENNReal.ofReal (paperHigherPrimePowerMass N) * eLpNorm f p S.μ :=
        eLpNorm_paperHigherPowerAbsPart_le S c f N hp hf
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards
    [hmajor.eventually (ENNReal.nhds_zero_basis_Iic.mem_of_mem hε),
      Filter.Eventually.of_forall hbound] with N hmaj hN
  exact hN.trans hmaj

private theorem paperHigherPrimePowerPart_tendsto_zero_of_fourth_scale
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) (x : X)
    (hG : Tendsto (fun k : ℕ =>
      paperHigherPowerAbsPart S c f (paperHigherPowerFourthScale k) x)
      atTop (𝓝 0)) :
    Tendsto (fun N : Scale => paperHigherPrimePowerPart S c f N x)
      atTop (𝓝 0) := by
  have hlog := tendsto_paperHigherPowerLog_four_atTop
  have hmajor : Tendsto (fun N : Scale =>
      4 * paperHigherPowerAbsPart S c f
        (paperHigherPowerFourthScale (Nat.log 4 N.1)) x)
      atTop (𝓝 0) := by
    simpa using (hG.comp hlog).const_mul (4 : ℝ)
  have hbound : ∀ N : Scale,
      ‖paperHigherPrimePowerPart S c f N x‖ ≤
        4 * paperHigherPowerAbsPart S c f
          (paperHigherPowerFourthScale (Nat.log 4 N.1)) x := by
    intro N
    let k := Nat.log 4 N.1
    let M := paperHigherPowerFourthScale k
    have hNpos : N.1 ≠ 0 := by omega
    have hpowLower : 4 ^ k ≤ N.1 := Nat.pow_log_le_self 4 hNpos
    have hNM' : N.1 < 4 ^ (k + 1) := by
      exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) N.1
    have hNM : N.1 ≤ M.1 := by
      dsimp [M, paperHigherPowerFourthScale]
      exact hNM'.le
    have hM4N : M.1 ≤ 4 * N.1 := by
      dsimp [M, paperHigherPowerFourthScale]
      calc
        4 ^ (k + 1) = 4 * 4 ^ k := by
          rw [Nat.pow_succ]
          exact Nat.mul_comm _ _
        _ ≤ 4 * N.1 := Nat.mul_le_mul_left 4 hpowLower
    calc
      ‖paperHigherPrimePowerPart S c f N x‖ ≤
          paperHigherPowerAbsPart S c f N x :=
        norm_paperHigherPrimePowerPart_le_absPart S c f N x
      _ ≤ 4 * paperHigherPowerAbsPart S c f M x :=
        paperHigherPowerAbsPart_le_four_of_scale S c f hNM hM4N x
  have hnorm : Tendsto (fun N : Scale =>
      ‖paperHigherPrimePowerPart S c f N x‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      ?_ hmajor
    exact Filter.Eventually.of_forall hbound
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- For every finite exponent `p ≥ 1`, the normalized higher-prime-power
remainder tends to zero in `Lᵖ` along all positive integer scales. -/
theorem paperHigherPrimePowerPart_eLpNorm_tendsto_zero
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hf : MemLp f p S.μ) :
    Tendsto (fun N : Scale =>
      eLpNorm (paperHigherPrimePowerPart S c f N) p S.μ) atTop (𝓝 0) :=
  eLpNorm_paperHigherPrimePowerPart_tendsto_zero S c f hp hpTop hf

/-- The higher-prime-power remainder tends to zero almost everywhere along
the complete scale parameter, not only along a selected subsequence. -/
theorem paperHigherPrimePowerPart_ae_tendsto_zero
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (_hpTop : p ≠ ∞) (hf : MemLp f p S.μ) :
    ∀ᵐ x ∂S.μ,
      Tendsto (fun N : Scale => paperHigherPrimePowerPart S c f N x)
        atTop (𝓝 0) := by
  let G : ℕ → X → ℝ := fun k x =>
    paperHigherPowerAbsPart S c f (paperHigherPowerFourthScale k) x
  have hmassSummable : Summable (fun k : ℕ =>
      paperHigherPrimePowerMass (paperHigherPowerFourthScale k)) :=
    paperHigherPowerFourthScale_mass_summable
  have hmassNeTop : (∑' k : ℕ,
      ENNReal.ofReal (paperHigherPrimePowerMass
        (paperHigherPowerFourthScale k))) ≠ ∞ :=
    hmassSummable.tsum_ofReal_ne_top
  have hmajorNeTop : (∑' k : ℕ,
      ENNReal.ofReal (paperHigherPrimePowerMass
        (paperHigherPowerFourthScale k)) * eLpNorm f p S.μ) ≠ ∞ := by
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hmassNeTop hf.eLpNorm_ne_top
  have htermBound : ∀ k : ℕ,
      eLpNorm (G k) p S.μ ≤
        ENNReal.ofReal (paperHigherPrimePowerMass
          (paperHigherPowerFourthScale k)) * eLpNorm f p S.μ := by
    intro k
    exact eLpNorm_paperHigherPowerAbsPart_le S c f
      (paperHigherPowerFourthScale k) hp hf
  have htsumBound : (∑' k : ℕ, eLpNorm (G k) p S.μ) ≤
      ∑' k : ℕ,
        ENNReal.ofReal (paperHigherPrimePowerMass
          (paperHigherPowerFourthScale k)) * eLpNorm f p S.μ :=
    ENNReal.tsum_le_tsum htermBound
  have htsumNeTop : (∑' k : ℕ, eLpNorm (G k) p S.μ) ≠ ∞ :=
    ne_top_of_le_ne_top hmajorNeTop htsumBound
  have hsumAE : ∀ᵐ x ∂S.μ, Summable (fun k : ℕ => ‖G k x‖) :=
    summable_norm_of_tsum_eLpNorm_ne_top hp htsumNeTop
  filter_upwards [hsumAE] with x hsum
  have hGnonneg (k : ℕ) : 0 ≤ G k x := by
    exact paperHigherPowerAbsPart_nonneg S c f
      (paperHigherPowerFourthScale k) x
  have hGsum : Summable (fun k : ℕ => G k x) :=
    hsum.congr (fun k => by
      dsimp [G]
      rw [abs_of_nonneg (hGnonneg k)])
  have hGzero : Tendsto (fun k : ℕ => G k x) atTop (𝓝 0) :=
    hGsum.tendsto_atTop_zero
  exact paperHigherPrimePowerPart_tendsto_zero_of_fourth_scale
    S c f x hGzero

/-- Conditional prime-only convergence: any `Lᵖ` and almost-everywhere limit
for the von Mangoldt averages transfers to the prime-only averages by the
exact finite decomposition and the higher-prime-power remainder limit. This
packages the consequence of `er:weighted-convergence` without asserting that
weighted convergence unconditionally holds. -/
theorem paperPrimeOnlyPart_converges_of_vonMangoldtAverage_converges
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : FractionalExponent) (p : ℝ) (hp : 1 < p) (f : X → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) S.μ)
    (hWeighted : ∃ Lf : X → ℂ,
      MemLp Lf (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ,
        Tendsto (fun N : Scale => vonMangoldtAverage S c.value f N x)
          atTop (𝓝 (Lf x))) ∧
      Tendsto (fun N : Scale =>
        eLpNorm (vonMangoldtAverage S c.value f N - Lf)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0)) :
    ∃ Lf : X → ℂ,
      MemLp Lf (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ,
        Tendsto (fun N : Scale => paperPrimeOnlyPart S c.value f N x)
          atTop (𝓝 (Lf x))) ∧
      Tendsto (fun N : Scale =>
        eLpNorm (paperPrimeOnlyPart S c.value f N - Lf)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  obtain ⟨Lf, hLf, hAae, hALp⟩ := hWeighted
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hRlp := paperHigherPrimePowerPart_eLpNorm_tendsto_zero
    S c.value f hpENN ENNReal.ofReal_ne_top hf
  have hRae := paperHigherPrimePowerPart_ae_tendsto_zero
    S c.value f hpENN ENNReal.ofReal_ne_top hf
  have hprimeEq (N : Scale) :
      paperPrimeOnlyPart S c.value f N =
        vonMangoldtAverage S c.value f N -
          paperHigherPrimePowerPart S c.value f N := by
    rw [vonMangoldtAverage_eq_primeParts]
    funext x
    simp
  have hprimeDiff (N : Scale) :
      paperPrimeOnlyPart S c.value f N - Lf =
        (vonMangoldtAverage S c.value f N - Lf) -
          paperHigherPrimePowerPart S c.value f N := by
    rw [hprimeEq]
    abel
  have hbound (N : Scale) :
      eLpNorm (paperPrimeOnlyPart S c.value f N - Lf)
          (ENNReal.ofReal p) S.μ ≤
        eLpNorm (vonMangoldtAverage S c.value f N - Lf)
            (ENNReal.ofReal p) S.μ +
          eLpNorm (paperHigherPrimePowerPart S c.value f N)
            (ENNReal.ofReal p) S.μ := by
    rw [hprimeDiff]
    exact eLpNorm_sub_le hpENN
  have hsum : Tendsto (fun N : Scale =>
      eLpNorm (vonMangoldtAverage S c.value f N - Lf)
          (ENNReal.ofReal p) S.μ +
        eLpNorm (paperHigherPrimePowerPart S c.value f N)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
    simpa using hALp.add hRlp
  have hprimeLp : Tendsto (fun N : Scale =>
      eLpNorm (paperPrimeOnlyPart S c.value f N - Lf)
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards
      [hsum.eventually (ENNReal.nhds_zero_basis_Iic.mem_of_mem hε),
        Filter.Eventually.of_forall hbound] with N hsumN hboundN
    exact hboundN.trans hsumN
  have hprimeAe : ∀ᵐ x ∂S.μ,
      Tendsto (fun N : Scale => paperPrimeOnlyPart S c.value f N x)
        atTop (𝓝 (Lf x)) := by
    filter_upwards [hAae, hRae] with x hxA hxR
    have hseq : (fun N : Scale => paperPrimeOnlyPart S c.value f N x) =
        fun N : Scale => vonMangoldtAverage S c.value f N x -
          paperHigherPrimePowerPart S c.value f N x := by
      funext N
      exact congrFun (hprimeEq N) x
    rw [hseq]
    simpa using hxA.sub hxR
  exact ⟨Lf, hLf, hprimeAe, hprimeLp⟩

end

#print axioms paperHigherPrimePowerPart_eLpNorm_tendsto_zero
#print axioms paperHigherPrimePowerPart_ae_tendsto_zero
#print axioms paperPrimeOnlyPart_converges_of_vonMangoldtAverage_converges

end FractionalPrimes

end

