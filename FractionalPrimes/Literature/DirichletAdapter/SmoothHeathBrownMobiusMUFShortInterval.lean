module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownSmallGroupData
public import FractionalPrimes.Literature.DirichletAdapter.SmoothSmallGroupFloorPrefixBridge
public import FractionalPrimes.Literature.Twisted.ConditionalMobiusResidueFromMUF
public import Mathlib.Tactic
@[expose] public section

/-!
# Selected Möbius-factor short intervals from MUF

This file connects the exact real-endpoint prefix bridge to the actual
normalized smooth Heath--Brown Möbius factor. The residue estimate is still
obtained from the explicit scalar `MobiusUniformity` premise.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The auxiliary weight that converts the normalized smooth Möbius factor
into the source summand `μ(n)n^(-1/2-it)` on one residue class. -/
noncomputable def smoothHeathBrownMobiusResiduePhaseWeight
    (q b : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  if _hn : 0 < n then
    if n % q = b then
      (Real.sqrt (n : ℝ) : ℂ) *
        (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))
    else 0
  else 0

/-- The residue-phase weight is bounded by one everywhere, including at the
origin where it is defined to vanish. -/
theorem smoothHeathBrownMobiusResiduePhaseWeight_norm_le_one
    (q b : ℕ) (t : ℝ) (n : ℕ) :
    ‖smoothHeathBrownMobiusResiduePhaseWeight q b t n‖ ≤ 1 := by
  by_cases hn0 : n = 0
  · subst n
    simp [smoothHeathBrownMobiusResiduePhaseWeight]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hres : n % q = b
  · rw [smoothHeathBrownMobiusResiduePhaseWeight, dif_pos hn, if_pos hres,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hscalar :
        ‖(n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))‖ =
          1 / Real.sqrt (n : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      have hre :
          ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)).re = -(1 / 2 : ℝ) := by
        simp
      rw [hre]
      have hsqrt :
          Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : 0 < (n : ℝ))]
        have hexp : (1 / 2 : ℝ) + (-(1 / 2 : ℝ)) = 0 := by ring
        rw [hexp, Real.rpow_zero]
      have hsqrtpos : 0 < Real.sqrt (n : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast hn)
      have hinv :
          (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (n : ℝ) := by
        rw [eq_div_iff hsqrtpos.ne']
        simpa [mul_comm] using hsqrt
      exact hinv
    rw [hscalar]
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hn)
    field_simp <;> norm_num
  · simp [smoothHeathBrownMobiusResiduePhaseWeight, hn, hres]

/-- With this phase weight, the actual normalized smooth Möbius factor is
exactly the source residue summand times the sampled smooth cutoff. -/
theorem smoothHeathBrownMobiusWeightedFactorCoefficient_eq_residueTerm
    {X z : ℝ} (j : SmoothHeathBrownScaleIndex X)
    (q b : ℕ) (t : ℝ) (n : ℕ) :
    smoothHeathBrownWeightedFactorCoefficient (z := z) (.mobius j)
        (smoothHeathBrownMobiusResiduePhaseWeight q b t) n =
      (if (n : ℝ) ≤ z then
        if n % q = b then mobiusMellinResidueTerm t n else 0 else 0) *
        smoothSmallGroupThetaWeight
          (smoothHeathBrownFactorScale (.mobius j)) n := by
  by_cases hn0 : n = 0
  · subst n
    simp [smoothHeathBrownWeightedFactorCoefficient,
      smoothHeathBrownNormalizedFactorCoefficient,
      smoothHeathBrownMobiusFactor,
      smoothHeathBrownMobiusResiduePhaseWeight,
      smoothSmallGroupThetaWeight, mobiusMellinResidueTerm]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  by_cases hcut : (n : ℝ) ≤ z
  · rw [smoothHeathBrownWeightedFactorCoefficient,
      smoothHeathBrownNormalizedFactorCoefficient]
    simp only [smoothHeathBrownMobiusFactor, ArithmeticFunction.coe_mk,
      hn.ne', ↓reduceIte, smoothSmallGroupThetaWeight]
    rw [truncatedMobius_apply_of_le hcut]
    by_cases hres : n % q = b
    · simp [smoothHeathBrownMobiusResiduePhaseWeight, hn, hres,
        mobiusMellinResidueTerm]
      have hsqrtC : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hnR))
      field_simp [hsqrtC]
      push_cast
      simp [hcut, smoothHeathBrownFactorScale]
      ring
    · simp [smoothHeathBrownMobiusResiduePhaseWeight, hn, hres]
  · simp [smoothHeathBrownWeightedFactorCoefficient,
      smoothHeathBrownNormalizedFactorCoefficient,
      smoothHeathBrownMobiusFactor, hn.ne', hcut,
      smoothHeathBrownMobiusResiduePhaseWeight,
      smoothSmallGroupThetaWeight]

/-- Replacing a real left endpoint by its natural floor does not change the
integer points in a real half-open interval. -/
theorem factorExtractionRealInterval_floor_left_eq
    {u v : ℝ} :
    factorExtractionRealInterval (Nat.floor u : ℝ) v =
      factorExtractionRealInterval u v := by
  simp [factorExtractionRealInterval]

/-- A cutoff residue prefix starting at the natural floor of a real point is
bounded by the residue estimate at that real point. This preserves the MUF
lower-endpoint hypothesis even when the floor itself is below `M`. -/
theorem smoothSmallGroupMobiusResidueFloorPrefix_bound
    {u z M C : ℝ} {k q b : ℕ} {t : ℝ}
    (hu : 0 ≤ u) (hz : 0 ≤ z) (hMu : M ≤ u)
    (hkM : (k : ℝ) ≤ 2 * M) (hC : 0 ≤ C)
    (hResidueInterval : ∀ {u' v' : ℝ}, M ≤ u' → u' ≤ v' → v' ≤ 2 * M →
      ‖∑ m ∈ Finset.Ioc (Nat.floor u') (Nat.floor v'),
          if m % q = b then mobiusMellinResidueTerm t m else 0‖ ≤ C) :
    ‖smoothSmallGroupPrefix (Nat.floor u)
      (fun m => if (m : ℝ) ≤ z then
        if m % q = b then mobiusMellinResidueTerm t m else 0 else 0)
      k‖ ≤ C := by
  have hprefix := smoothSmallGroupPrefix_cutoff_eq_realInterval
    (Nat.floor u) k hz
    (fun m => if m % q = b then mobiusMellinResidueTerm t m else 0)
  have hkNonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hvnonneg : 0 ≤ min (k : ℝ) z := le_min hkNonneg hz
  have hvUpper : min (k : ℝ) z ≤ 2 * M := le_trans (min_le_left _ _) hkM
  have hfloorLeft := factorExtractionRealInterval_floor_left_eq
    (u := u) (v := min (k : ℝ) z)
  by_cases huv : u ≤ min (k : ℝ) z
  · have hbound := hResidueInterval (u' := u) (v' := min (k : ℝ) z)
      hMu huv hvUpper
    rw [hprefix, hfloorLeft]
    simpa [factorExtractionRealInterval, mobiusMellinResidueTerm] using hbound
  · have hzero : factorExtractionRealInterval u (min (k : ℝ) z) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      rw [mem_factorExtractionRealInterval hu hvnonneg] at hm
      exact huv (le_trans hm.1.le hm.2)
    rw [hprefix, hfloorLeft, hzero]
    simp
    exact hC

/-- Finite Abel transfer of an exact MUF-type residue-interval estimate to
the actual smooth Heath--Brown Möbius factor on an arbitrary real interval
contained in one source dyadic block. The factor `3` is the checked total
variation cost of the sampled smooth cutoff. -/
theorem smoothHeathBrownMobiusResidueFactor_shortInterval_of_intervalBound
    {X z M C : ℝ} (j : SmoothHeathBrownScaleIndex X)
    (q b : ℕ) (t : ℝ) (hz : 0 ≤ z) (hMpos : 0 < M) (hC : 0 ≤ C)
    (hResidueInterval : ∀ {u' v' : ℝ}, M ≤ u' → u' ≤ v' → v' ≤ 2 * M →
      ‖∑ m ∈ Finset.Ioc (Nat.floor u') (Nat.floor v'),
          if m % q = b then mobiusMellinResidueTerm t m else 0‖ ≤ C)
    {u v : ℝ} (hu : 0 ≤ u)
    (hI : Set.Ioc u v ⊆ Set.Ioc M (2 * M)) :
    ‖∑ n ∈ factorExtractionRealInterval u v,
        smoothHeathBrownWeightedFactorCoefficient (z := z) (.mobius j)
          (smoothHeathBrownMobiusResiduePhaseWeight q b t) n‖ ≤ 3 * C := by
  let u₀ : ℝ := max u M
  let a : ℕ := Nat.floor u₀
  let b₀ : ℕ := Nat.floor v
  let f : ℕ → ℂ := fun n =>
    if (n : ℝ) ≤ z then
      if n % q = b then mobiusMellinResidueTerm t n else 0 else 0
  by_cases huv : u < v
  · have hvnonneg : 0 ≤ v := le_trans hu huv.le
    have hvblock := hI ⟨huv, le_rfl⟩
    have hu₀nonneg : 0 ≤ u₀ := by
      dsimp [u₀]
      exact le_trans hMpos.le (le_max_right u M)
    have hMu₀ : M ≤ u₀ := by dsimp [u₀]; exact le_max_right u M
    have hu₀v : u₀ < v := by
      dsimp [u₀]
      exact max_lt_iff.mpr ⟨huv, hvblock.1⟩
    have hfactor :
        factorExtractionRealInterval u v = Finset.Ioc a b₀ := by
      calc
        factorExtractionRealInterval u v =
            factorExtractionRealInterval u₀ v := by
          ext n
          rw [mem_factorExtractionRealInterval hu hvnonneg,
            mem_factorExtractionRealInterval hu₀nonneg hvnonneg]
          constructor
          · rintro ⟨hun, hnv⟩
            have hnblock := hI ⟨hun, hnv⟩
            refine ⟨?_, hnv⟩
            dsimp [u₀]
            exact max_lt_iff.mpr ⟨hun, hnblock.1⟩
          · rintro ⟨hu₀n, hnv⟩
            exact ⟨lt_of_le_of_lt (le_max_left u M) hu₀n, hnv⟩
        _ = Finset.Ioc a b₀ := by rfl
    have hprefix : ∀ k, a < k → k ≤ b₀ → ‖smoothSmallGroupPrefix a f k‖ ≤ C := by
      intro k hak hkb
      have hak' : Nat.floor u₀ < k := by simpa [a] using hak
      have hkb' : k ≤ Nat.floor v := by simpa [b₀] using hkb
      have hknv : (k : ℝ) ≤ v := by
        calc
          (k : ℝ) ≤ (Nat.floor v : ℝ) := Nat.cast_le.mpr hkb'
          _ ≤ v := Nat.floor_le hvnonneg
      have hkM : (k : ℝ) ≤ 2 * M := le_trans hknv hvblock.2
      dsimp [f]
      exact smoothSmallGroupMobiusResidueFloorPrefix_bound
        (u := u₀) (z := z) (M := M) (C := C) (k := k)
        hu₀nonneg hz hMu₀ hkM hC hResidueInterval
    have hNpos :
        0 < smoothHeathBrownFactorScale (.mobius j) := by
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (smoothHeathBrownFactorScale_ge_one (.mobius j))
    have hsumEq :
        (∑ n ∈ factorExtractionRealInterval u v,
          smoothHeathBrownWeightedFactorCoefficient (z := z) (.mobius j)
            (smoothHeathBrownMobiusResiduePhaseWeight q b t) n) =
          ∑ n ∈ Finset.Ioc a b₀,
            f n * smoothSmallGroupThetaWeight
              (smoothHeathBrownFactorScale (.mobius j)) n := by
      rw [hfactor]
      apply Finset.sum_congr rfl
      intro n hn
      rw [smoothHeathBrownMobiusWeightedFactorCoefficient_eq_residueTerm]
    by_cases hab : a < b₀
    · rw [hsumEq]
      exact smoothSmallGroupThetaFiniteAbelTransfer hab hNpos f hC hprefix
    · have hba : b₀ ≤ a := Nat.le_of_not_gt hab
      rw [hsumEq, Finset.Ioc_eq_empty_of_le hba]
      simp
      positivity
  · have hvu : v ≤ u := le_of_not_gt huv
    have hfloor : Nat.floor v ≤ Nat.floor u := Nat.floor_mono hvu
    have hempty : factorExtractionRealInterval u v = ∅ := by
      simp [factorExtractionRealInterval, Finset.Ioc_eq_empty_of_le hfloor]
    rw [hempty]
    simp
    positivity

/-- The preceding finite transfer specialized to the exact interval bound
provided by `mobiusResidueFromFactorGoal`. Its analytic content remains the
explicit premise `hMUF`; all floor, cutoff, factor, and smooth-weight steps
are proved here. -/
theorem smoothHeathBrownMobiusResidueFactor_shortInterval_of_MUF
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {B κ : ℝ} (hB : 0 < B) (hκ : 0 < κ) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X M z : ℝ}, X₀ ≤ X → X ^ (1 / 400 : ℝ) ≤ M → M ≤ X →
        (j : SmoothHeathBrownScaleIndex X) →
        {q : ℕ} → 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
        {b : ℕ} → b < q → (t : ℝ) → |t| ≤ X → 0 ≤ z →
        ∀ {u v : ℝ}, 0 ≤ u → Set.Ioc u v ⊆ Set.Ioc M (2 * M) →
          ‖∑ n ∈ factorExtractionRealInterval u v,
              smoothHeathBrownWeightedFactorCoefficient (z := z) (.mobius j)
                (smoothHeathBrownMobiusResiduePhaseWeight q b t) n‖ ≤
            3 * Cμ * Real.sqrt M * (Real.log X) ^ (-κ) := by
  obtain ⟨Cμ, X₀, hCμ, hX₀three, hResidueAt⟩ :=
    mobiusResidueFromFactorGoal hMUF
      (show 0 < (1 / 400 : ℝ) by norm_num)
      (show (1 / 400 : ℝ) ≤ 1 by norm_num)
      (show 0 < (1 : ℝ) by norm_num) hB hκ
  refine ⟨Cμ, X₀, hCμ, hX₀three, ?_⟩
  intro X M z hX₀X hMlow hMupper j q hq hqlog b hb t ht hz u v hu hI
  have hXthree : 3 ≤ X := le_trans hX₀three hX₀X
  have hXpos : 0 < X := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le
    (Real.rpow_pos_of_pos hXpos (1 / 400 : ℝ)) hMlow
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  let C : ℝ := Cμ * Real.sqrt M * (Real.log X) ^ (-κ)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hResidueInterval :
      ∀ {u' v' : ℝ}, M ≤ u' → u' ≤ v' → v' ≤ 2 * M →
        ‖∑ m ∈ Finset.Ioc (Nat.floor u') (Nat.floor v'),
            if m % q = b then mobiusMellinResidueTerm t m else 0‖ ≤ C := by
    intro u' v' hu' huv' hv'
    have ht' : |t| ≤ X ^ (1 : ℝ) := by simpa using ht
    have hbound := hResidueAt hX₀X hMlow hMupper hq hqlog hb t ht'
      hu' huv' hv'
    simpa [C] using hbound
  have hfinite := smoothHeathBrownMobiusResidueFactor_shortInterval_of_intervalBound
    (X := X) (z := z) (M := M) (C := C) j q b t hz hMpos hC
    hResidueInterval hu hI
  calc
    ‖∑ n ∈ factorExtractionRealInterval u v,
        smoothHeathBrownWeightedFactorCoefficient (z := z) (.mobius j)
          (smoothHeathBrownMobiusResiduePhaseWeight q b t) n‖ ≤ 3 * C := hfinite
    _ = 3 * Cμ * Real.sqrt M * (Real.log X) ^ (-κ) := by
      dsimp [C]
      ring

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusResiduePhaseWeight_norm_le_one
#print axioms FractionalPrimes.Literature.DirichletAdapter.factorExtractionRealInterval_floor_left_eq
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothSmallGroupMobiusResidueFloorPrefix_bound
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusWeightedFactorCoefficient_eq_residueTerm
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusResidueFactor_shortInterval_of_intervalBound
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusResidueFactor_shortInterval_of_MUF
