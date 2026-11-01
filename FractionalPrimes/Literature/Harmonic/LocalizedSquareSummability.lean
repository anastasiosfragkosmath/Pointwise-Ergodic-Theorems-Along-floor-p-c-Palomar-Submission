module

public import FractionalPrimes.Literature.Harmonic.LocalizedDyadicIncrements
public import FractionalPrimes.Literature.Harmonic.FrequencyResolutionLp
public import FractionalPrimes.FiniteMomentExhaustion

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩

/-- The `L²(ℓ²)` function of localized increments at fixed frequency offset
`j` and subdivision level `l`. -/
noncomputable def localizedUnweightedIncrementSquareFunction
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) : ℝ :=
  Real.sqrt (∑' i : ℤ × Fin (2 ^ l),
    ‖localizedInterpolatedAverageL2 c
        (localizedDyadicLeftTime i.1 l i.2.val + localizedDyadicMesh i.1 l)
        (localizedDyadicRightTime_pos i.1 l i.2.val)
        (localizedSignedFrequencyProjectionL2 c hc (j + i.1) f) x -
      localizedInterpolatedAverageL2 c
        (localizedDyadicLeftTime i.1 l i.2.val)
        (localizedDyadicLeftTime_pos i.1 l i.2.val)
        (localizedSignedFrequencyProjectionL2 c hc (j + i.1) f) x‖ ^ 2)

/-- The coefficient shape required by the square estimate. Its leading
constant is fixed once from the localized increment and square function
bounds, and is independent of `j` and `l`. -/
def localizedSquareCoefficient (c : ℝ) (hc : 1 < c)
    (hcNon : NonIntegral c) (j : ℤ) (l : ℕ) : ℝ :=
  localizedUnweightedIncrementConstant c hc hcNon *
    frequencyProjectionFiniteSquareFunctionBound 2 *
      min 1 (Real.rpow 2 ((l : ℝ) - localizedIncrementSigma c * |(j : ℝ)|))

private theorem lpCast_norm_eq {α E : Type*} [NormedAddCommGroup E]
    {p q : ℝ≥0∞} (e : p = q) (f : lp (fun _ : α => E) p) :
    ‖e ▸ f‖ = ‖f‖ := by
  cases e
  rfl

private theorem frequencyProjectionFiniteSquareFunction_eq_range
    (c : ℝ) (hc : 1 < c) (N : ℕ)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal 2)) (x : ℤ) :
    finiteProjectionSquareFunction (N + 1)
        (frequencyProjectionLpOperatorFamily c hc
          (by norm_num : 1 < (2 : ℝ)) N) f x =
      Real.sqrt (∑ h ∈ Finset.range (N + 1),
        ‖frequencyProjectionLpProjection c hc
          (by norm_num : 1 < (2 : ℝ)) h f x‖ ^ 2) := by
  unfold finiteProjectionSquareFunction finiteCoordinateSquare
  change Real.sqrt (∑ i : Fin (N + 1),
      ‖frequencyProjectionLpOperatorFamily c hc
        (by norm_num : 1 < (2 : ℝ)) N i f x‖ ^ 2) = _
  congr 1
  calc
    ∑ i : Fin (N + 1),
        ‖frequencyProjectionLpOperatorFamily c hc
          (by norm_num : 1 < (2 : ℝ)) N i f x‖ ^ 2 =
      ∑ i : Fin (N + 1),
        ‖frequencyProjectionLpProjection c hc
          (by norm_num : 1 < (2 : ℝ)) i.val f x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      change ‖frequencyProjectionLpOperatorFamily c hc
        (by norm_num : 1 < (2 : ℝ)) N i f x‖ ^ 2 = _
      rw [frequencyProjectionLpOperatorFamily_eq_projection]
    _ = ∑ h ∈ Finset.range (N + 1),
        ‖frequencyProjectionLpProjection c hc
          (by norm_num : 1 < (2 : ℝ)) h f x‖ ^ 2 :=
      Fin.sum_univ_eq_sum_range
        (fun h : ℕ => ‖frequencyProjectionLpProjection c hc
          (by norm_num : 1 < (2 : ℝ)) h f x‖ ^ 2) (N + 1)

private theorem frequencyProjectionPointwiseSquareSummable
    (c : ℝ) (hc : 1 < c) (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal 2))
    (x : ℤ) :
    Summable (fun h : ℕ =>
      ‖frequencyProjectionLpProjection c hc (by norm_num : 1 < (2 : ℝ)) h f x‖ ^ 2) := by
  classical
  let a : ℕ → ℝ := fun h =>
    ‖frequencyProjectionLpProjection c hc (by norm_num : 1 < (2 : ℝ)) h f x‖ ^ 2
  let B := frequencyProjectionFiniteSquareFunctionBound 2 * ‖f‖
  have hconst : 0 ≤ frequencyProjectionFiniteSquareFunctionBound 2 := by
    unfold frequencyProjectionFiniteSquareFunctionBound
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (frequencyProjectionSignedLpBound_nonneg (by norm_num))
  have hB : 0 ≤ B := mul_nonneg hconst (norm_nonneg f)
  have hpartial (N : ℕ) :
      ∑ h ∈ Finset.range (N + 1), a h ≤ B ^ 2 := by
    obtain ⟨g, hg, hgnorm⟩ :=
      frequencyProjectionFiniteSquareFunction_memLp_norm_le
        (p := 2) (by norm_num) c hc N f
    have hgpoint : g x = Real.sqrt
        (∑ h ∈ Finset.range (N + 1), a h) := by
      calc
        g x = finiteProjectionSquareFunction (N + 1)
            (frequencyProjectionLpOperatorFamily c hc
              (by norm_num : 1 < (2 : ℝ)) N) f x := hg x
        _ = Real.sqrt (∑ h ∈ Finset.range (N + 1), a h) := by
          rw [frequencyProjectionFiniteSquareFunction_eq_range]
    have hgNonneg : 0 ≤ g x := by rw [hgpoint]; exact Real.sqrt_nonneg _
    have hgPointBound : g x ≤ B := by
      calc
        g x = ‖g x‖ := (Real.norm_of_nonneg hgNonneg).symm
        _ ≤ ‖g‖ := lp.norm_apply_le_norm
          (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num : 0 < (2 : ℝ))) g x
        _ ≤ B := hgnorm
    have hsumNonneg : 0 ≤ ∑ h ∈ Finset.range (N + 1), a h :=
      Finset.sum_nonneg fun h hh => sq_nonneg _
    have hsquare : (g x) ^ 2 = ∑ h ∈ Finset.range (N + 1), a h := by
      rw [hgpoint]
      exact Real.sq_sqrt hsumNonneg
    rw [← hsquare]
    nlinarith [hgPointBound, hB]
  have hpartial' (N : ℕ) :
      ∑ h ∈ Finset.range N, a h ≤ B ^ 2 := by
    calc
      ∑ h ∈ Finset.range N, a h ≤
          ∑ h ∈ Finset.range (N + 1), a h :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.le_succ N))
          (by intro h hh hnot; exact sq_nonneg _)
      _ ≤ B ^ 2 := hpartial N
  have ha : Summable a :=
    summable_of_sum_range_le (fun h => sq_nonneg _) hpartial'
  simpa only [a] using ha

private theorem lpCast_sub {p q : ℝ≥0∞} (e : p = q)
    (f g : lp (fun _ : ℤ => ℂ) p) :
    e ▸ (f - g) = (e ▸ f) - (e ▸ g) := by
  cases e
  rfl

theorem localizedFrequencyProjectionL2_eq_frequencyProjectionLpProjection
    (c : ℝ) (hc : 1 < c) (h : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    localizedFrequencyProjectionL2 c hc h f =
      frequencyProjectionLpTwoExponent ▸
        frequencyProjectionLpProjection c hc (by norm_num : 1 < (2 : ℝ)) h
          (frequencyProjectionLpTwoToMultiplier f) := by
  cases h with
  | zero =>
      simp [localizedFrequencyProjectionL2, frequencyProjectionLpProjection,
        frequencyProjectionPartialLpOperatorL2,
        frequencyProjectionLpTwoToMultiplier, frequencyProjectionLpTwoExponent,
        frequencyProjectionPartialLpOperator]
  | succ h =>
      simp only [localizedFrequencyProjectionL2, frequencyProjectionLpProjection,
        Nat.succ_ne_zero, if_false, Nat.succ_sub_one,
        frequencyProjectionPartialLpOperatorL2]
      exact (lpCast_sub frequencyProjectionLpTwoExponent _ _).symm

/-- Summable natural-frequency projection energy with the exact `ha:lp` bound. -/
theorem frequencyProjectionNaturalEnergyBound
    (c : ℝ) (hc : 1 < c) (f : lp (fun _ : ℤ => ℂ) 2) :
    Summable (fun h : ℕ =>
      ‖localizedFrequencyProjectionL2 c hc h f‖ ^ 2) ∧
    (∑' h : ℕ, ‖localizedFrequencyProjectionL2 c hc h f‖ ^ 2) ≤
      (frequencyProjectionFiniteSquareFunctionBound 2 * ‖f‖) ^ 2 := by
  classical
  let F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal 2) :=
    frequencyProjectionLpTwoToMultiplier f
  let B := frequencyProjectionFiniteSquareFunctionBound 2 * ‖F‖
  have hFnorm : ‖F‖ = ‖f‖ := by
    exact lpCast_norm_eq frequencyProjectionLpTwoExponent.symm f
  have hB0 : 0 ≤ B := by
    have hfirst : 0 ≤ Real.sqrt 2 * Real.rpow 12 (1 / (2 : ℝ)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)
    have hbound : 0 ≤ frequencyProjectionSignedLpBound (2 : ℝ) :=
      frequencyProjectionSignedLpBound_nonneg (by norm_num : 1 < (2 : ℝ))
    dsimp [B, frequencyProjectionFiniteSquareFunctionBound]
    exact mul_nonneg (mul_nonneg hfirst hbound) (norm_nonneg F)
  obtain ⟨G, hG, hGnorm⟩ :=
    frequencyProjectionSquareFunction_memLp_norm_le
      (p := 2) (by norm_num) c hc F
  have hGpoint (x : ℤ) :
      G x = Real.sqrt (∑' h : ℕ,
        ‖frequencyProjectionLpProjection c hc
          (by norm_num : 1 < (2 : ℝ)) h F x‖ ^ 2) := hG x
  have hGnonneg (x : ℤ) : 0 ≤ G x := by
    rw [hGpoint x]
    exact Real.sqrt_nonneg _
  let term : ℤ → ℕ → ℝ := fun x h =>
    ‖frequencyProjectionLpProjection c hc
      (by norm_num : 1 < (2 : ℝ)) h F x‖ ^ 2
  have hpointSummable (x : ℤ) : Summable (term x) := by
    simpa [term] using frequencyProjectionPointwiseSquareSummable c hc F x
  have hGsquare (x : ℤ) : G x ^ 2 = ∑' h : ℕ, term x h := by
    calc
      G x ^ 2 = (Real.sqrt (∑' h : ℕ, term x h)) ^ 2 := by
        rw [hGpoint x]
      _ = ∑' h : ℕ, term x h :=
        Real.sq_sqrt (tsum_nonneg fun h => sq_nonneg (‖frequencyProjectionLpProjection
          c hc (by norm_num : 1 < (2 : ℝ)) h F x‖))
  have hpToReal : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by norm_num
  have hGabsSummable : Summable (fun x : ℤ => ‖G x‖ ^ 2) := by
    simpa only [hpToReal, Real.rpow_two] using
      (lp.memℓp G).summable
        (by norm_num : 0 < (ENNReal.ofReal (2 : ℝ)).toReal)
  have hGsum : Summable (fun x : ℤ => G x ^ 2) := by
    refine hGabsSummable.congr ?_
    intro x
    rw [Real.norm_of_nonneg (hGnonneg x)]
  have hProduct : Summable (fun z : ℤ × ℕ => term z.1 z.2) := by
    apply (summable_prod_of_nonneg (fun z : ℤ × ℕ => sq_nonneg
      (‖frequencyProjectionLpProjection c hc
        (by norm_num : 1 < (2 : ℝ)) z.2 F z.1‖))).2
    constructor
    · intro x
      exact hpointSummable x
    · have houter : Summable (fun x : ℤ => ∑' h : ℕ, term x h) := by
        refine hGsum.congr ?_
        intro x
        exact hGsquare x
      exact houter
  have hNatOuter : Summable (fun h : ℕ => ∑' x : ℤ, term x h) :=
    hProduct.prod_symm.prod
  have hcoordNorm (h : ℕ) :
      ‖frequencyProjectionLpProjection c hc
          (by norm_num : 1 < (2 : ℝ)) h F‖ ^ 2 =
        ∑' x : ℤ, term x h := by
    let P := frequencyProjectionLpProjection c hc
      (by norm_num : 1 < (2 : ℝ)) h F
    have hnorm : (∑' x : ℤ, ‖P x‖ ^ 2) ^ (1 / 2 : ℝ) = ‖P‖ := by
      simpa only [hpToReal, Real.rpow_two] using
        (lp.norm_eq_tsum_rpow
          (by norm_num : 0 < (ENNReal.ofReal (2 : ℝ)).toReal) P).symm
    have hsumNonneg : 0 ≤ ∑' x : ℤ, ‖P x‖ ^ 2 :=
      tsum_nonneg fun x => sq_nonneg (‖P x‖)
    calc
      ‖P‖ ^ 2 = ((∑' x : ℤ, ‖P x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [← hnorm]
      _ = ∑' x : ℤ, ‖P x‖ ^ 2 := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hsumNonneg]
      _ = ∑' x : ℤ, term x h := by
        apply tsum_congr
        intro x
        rfl
  have henergySummable : Summable (fun h : ℕ =>
      ‖frequencyProjectionLpProjection c hc
        (by norm_num : 1 < (2 : ℝ)) h F‖ ^ 2) := by
    refine hNatOuter.congr ?_
    intro h
    exact (hcoordNorm h).symm
  have henergy :
      (∑' h : ℕ, ‖frequencyProjectionLpProjection c hc
        (by norm_num : 1 < (2 : ℝ)) h F‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ = ∑' x : ℤ, G x ^ 2 := by
        calc
          _ = ∑' h : ℕ, ∑' x : ℤ, term x h := by
            apply tsum_congr
            intro h
            exact hcoordNorm h
          _ = ∑' x : ℤ, ∑' h : ℕ, term x h := hProduct.tsum_comm
          _ = ∑' x : ℤ, G x ^ 2 := by
            apply tsum_congr
            intro x
            exact (hGsquare x).symm
      _ = ‖G‖ ^ 2 := by
        have hnormG : (∑' x : ℤ, ‖G x‖ ^ 2) ^ (1 / 2 : ℝ) = ‖G‖ := by
          simpa only [hpToReal, Real.rpow_two] using
            (lp.norm_eq_tsum_rpow
              (by norm_num : 0 < (ENNReal.ofReal (2 : ℝ)).toReal) G).symm
        have hsumGNonneg : 0 ≤ ∑' x : ℤ, ‖G x‖ ^ 2 :=
          tsum_nonneg fun x => sq_nonneg (‖G x‖)
        calc
          ∑' x : ℤ, G x ^ 2 = ∑' x : ℤ, ‖G x‖ ^ 2 := by
            apply tsum_congr
            intro x
            rw [Real.norm_of_nonneg (hGnonneg x)]
          _ = ((∑' x : ℤ, ‖G x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
            rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hsumGNonneg]
          _ = ‖G‖ ^ 2 := by rw [hnormG]
      _ ≤ B ^ 2 := by nlinarith [hGnorm, hB0, norm_nonneg G]
  refine ⟨?_, ?_⟩
  · have hcast (h : ℕ) :
        localizedFrequencyProjectionL2 c hc h f =
          frequencyProjectionLpTwoExponent ▸
            frequencyProjectionLpProjection c hc
              (by norm_num : 1 < (2 : ℝ)) h F := by
      exact localizedFrequencyProjectionL2_eq_frequencyProjectionLpProjection
        c hc h f
    have hnormcast (h : ℕ) :
        ‖localizedFrequencyProjectionL2 c hc h f‖ ^ 2 =
          ‖frequencyProjectionLpProjection c hc
            (by norm_num : 1 < (2 : ℝ)) h F‖ ^ 2 := by
      rw [hcast h]
      simp only [lpCast_norm_eq frequencyProjectionLpTwoExponent]
    simpa only [hnormcast] using henergySummable
  · have hcast (h : ℕ) :
        localizedFrequencyProjectionL2 c hc h f =
          frequencyProjectionLpTwoExponent ▸
            frequencyProjectionLpProjection c hc
              (by norm_num : 1 < (2 : ℝ)) h F := by
      exact localizedFrequencyProjectionL2_eq_frequencyProjectionLpProjection
        c hc h f
    have hnormcast (h : ℕ) :
        ‖localizedFrequencyProjectionL2 c hc h f‖ ^ 2 =
          ‖frequencyProjectionLpProjection c hc
            (by norm_num : 1 < (2 : ℝ)) h F‖ ^ 2 := by
      rw [hcast h]
      simp only [lpCast_norm_eq frequencyProjectionLpTwoExponent]
    simpa only [hnormcast, F, B, hFnorm] using henergy

/-- The signed, frequency-shifted projection energy used by `ha:square`.
Negative projection indices vanish, and translation of the integer index
preserves the natural-frequency energy. -/
theorem frequencyProjectionSignedShiftEnergyBound
    (c : ℝ) (hc : 1 < c) (j : ℤ)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    Summable (fun k : ℤ =>
      ‖localizedSignedFrequencyProjectionL2 c hc (j + k) f‖ ^ 2) ∧
    (∑' k : ℤ,
      ‖localizedSignedFrequencyProjectionL2 c hc (j + k) f‖ ^ 2) ≤
      (frequencyProjectionFiniteSquareFunctionBound 2 * ‖f‖) ^ 2 := by
  let g : ℤ → ℝ := fun h =>
    ‖localizedSignedFrequencyProjectionL2 c hc h f‖ ^ 2
  have hnat : Summable (fun n : ℕ => g n) := by
    simpa [g, localizedSignedFrequencyProjectionL2] using
      (frequencyProjectionNaturalEnergyBound c hc f).1
  have hnegPoint (n : ℕ) : g (-(n + 1 : ℤ)) = 0 := by
    have hh : -(n + 1 : ℤ) < 0 := by omega
    dsimp [g]
    rw [localizedSignedFrequencyProjectionL2_of_neg c hc _ hh]
    simp
  have hneg : (fun n : ℕ => g (-(n + 1 : ℤ))) = fun _ => 0 := by
    funext n
    exact hnegPoint n
  have hnegSummable : Summable (fun n : ℕ => g (-(n + 1 : ℤ))) := by
    simpa only [hneg] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hg : Summable g := by
    exact Summable.of_nat_of_neg_add_one hnat hnegSummable
  have hgsum : (∑' h : ℤ, g h) =
      ∑' n : ℕ, ‖localizedFrequencyProjectionL2 c hc n f‖ ^ 2 := by
    rw [tsum_of_nat_of_neg_add_one hnat hnegSummable]
    rw [hneg]
    simp [g, localizedSignedFrequencyProjectionL2]
  have hshift : Summable (fun k : ℤ => g (j + k)) :=
    hg.comp_injective (Equiv.addLeft j).injective
  have hshiftSum : (∑' k : ℤ, g (j + k)) = ∑' h : ℤ, g h := by
    exact Equiv.tsum_eq (Equiv.addLeft j) g
  constructor
  · exact hshift
  · change (∑' k : ℤ, g (j + k)) ≤ _
    rw [hshiftSum, hgsum]
    exact (frequencyProjectionNaturalEnergyBound c hc f).2

#print axioms frequencyProjectionSignedShiftEnergyBound

/-- At a fixed dyadic scale, summing the localized increment bound over
the exact `2^l` subintervals gives the finite mesh energy estimate. -/
theorem localizedIncrementFiniteMeshEnergyBound
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j k : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    (∑ m : Fin (2 ^ l),
      ‖localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m.val + localizedDyadicMesh k l)
          (localizedDyadicRightTime_pos k l m.val)
          (localizedSignedFrequencyProjectionL2 c hc (j + k) f) -
        localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m.val)
          (localizedDyadicLeftTime_pos k l m.val)
          (localizedSignedFrequencyProjectionL2 c hc (j + k) f)‖ ^ 2) ≤
      (2 ^ l : ℝ) *
        (localizedUnweightedIncrementConstant c hc hcNon *
          min ((2 : ℝ) ^ (-(l : ℤ)))
            (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|))) ^ 2 *
          ‖localizedSignedFrequencyProjectionL2 c hc (j + k) f‖ ^ 2 := by
  let P := localizedSignedFrequencyProjectionL2 c hc (j + k) f
  let A := localizedUnweightedIncrementConstant c hc hcNon *
    min ((2 : ℝ) ^ (-(l : ℤ)))
      (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|))
  have hpoint (m : Fin (2 ^ l)) :
      ‖localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m.val + localizedDyadicMesh k l)
          (localizedDyadicRightTime_pos k l m.val) P -
        localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m.val)
          (localizedDyadicLeftTime_pos k l m.val) P‖ ≤ A * ‖P‖ := by
    exact localizedUnweightedIncrement c hc hcNon j k l m.val m.isLt f
  have hsq (m : Fin (2 ^ l)) :
      ‖localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m.val + localizedDyadicMesh k l)
          (localizedDyadicRightTime_pos k l m.val) P -
        localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m.val)
          (localizedDyadicLeftTime_pos k l m.val) P‖ ^ 2 ≤
        A ^ 2 * ‖P‖ ^ 2 := by
    have h := hpoint m
    have hn : 0 ≤ ‖localizedInterpolatedAverageL2 c
        (localizedDyadicLeftTime k l m.val + localizedDyadicMesh k l)
        (localizedDyadicRightTime_pos k l m.val) P -
      localizedInterpolatedAverageL2 c
        (localizedDyadicLeftTime k l m.val)
        (localizedDyadicLeftTime_pos k l m.val) P‖ := norm_nonneg _
    nlinarith [sq_nonneg (A * ‖P‖)]
  calc
    _ ≤ ∑ _m : Fin (2 ^ l), A ^ 2 * ‖P‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact hsq m
    _ = (2 ^ l : ℝ) * A ^ 2 * ‖P‖ ^ 2 := by simp [mul_assoc]
    _ = _ := by rfl

#print axioms localizedIncrementFiniteMeshEnergyBound

/-- Countable signed-scale version of the fixed-mesh energy estimate. -/
theorem localizedIncrementCountableMeshEnergyBound
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    let E : ℤ → ℝ := fun k =>
      ∑ m : Fin (2 ^ l),
        ‖localizedInterpolatedAverageL2 c
            (localizedDyadicLeftTime k l m.val + localizedDyadicMesh k l)
            (localizedDyadicRightTime_pos k l m.val)
            (localizedSignedFrequencyProjectionL2 c hc (j + k) f) -
          localizedInterpolatedAverageL2 c
            (localizedDyadicLeftTime k l m.val)
            (localizedDyadicLeftTime_pos k l m.val)
            (localizedSignedFrequencyProjectionL2 c hc (j + k) f)‖ ^ 2
    Summable E ∧
      (∑' k : ℤ, E k) ≤
        (2 ^ l : ℝ) *
          (localizedUnweightedIncrementConstant c hc hcNon *
            min ((2 : ℝ) ^ (-(l : ℤ)))
              (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|))) ^ 2 *
            (frequencyProjectionFiniteSquareFunctionBound 2 * ‖f‖) ^ 2 := by
  let E : ℤ → ℝ := fun k =>
    ∑ m : Fin (2 ^ l),
      ‖localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m.val + localizedDyadicMesh k l)
          (localizedDyadicRightTime_pos k l m.val)
          (localizedSignedFrequencyProjectionL2 c hc (j + k) f) -
        localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m.val)
          (localizedDyadicLeftTime_pos k l m.val)
          (localizedSignedFrequencyProjectionL2 c hc (j + k) f)‖ ^ 2
  let P : ℤ → ℝ := fun k =>
    ‖localizedSignedFrequencyProjectionL2 c hc (j + k) f‖ ^ 2
  let C : ℝ := (2 ^ l : ℝ) *
    (localizedUnweightedIncrementConstant c hc hcNon *
      min ((2 : ℝ) ^ (-(l : ℤ)))
        (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|))) ^ 2
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have hP := frequencyProjectionSignedShiftEnergyBound c hc j f
  have hmajor : Summable (fun k => C * P k) := hP.1.mul_left C
  have hE0 (k : ℤ) : 0 ≤ E k := by
    dsimp [E]
    exact Finset.sum_nonneg fun m hm => sq_nonneg _
  have hcell (k : ℤ) : E k ≤ C * P k := by
    simpa [E, P, C, mul_assoc] using
      localizedIncrementFiniteMeshEnergyBound c hc hcNon j k l f
  have hEsum : Summable E :=
    Summable.of_nonneg_of_le hE0 hcell hmajor
  constructor
  · exact hEsum
  · change (∑' k : ℤ, E k) ≤ _
    calc
      (∑' k : ℤ, E k) ≤ ∑' k : ℤ, C * P k :=
        hEsum.tsum_le_tsum hcell hmajor
      _ = C * ∑' k : ℤ, P k := by rw [tsum_mul_left]
      _ ≤ C * (frequencyProjectionFiniteSquareFunctionBound 2 * ‖f‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hP.2 hC0
      _ = _ := by rfl

#print axioms localizedIncrementCountableMeshEnergyBound

private theorem summableIntGeometricAbs {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (fun j : ℤ => q ^ |(j : ℝ)|) := by
  have hnat : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq0.le hq1
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa [abs_of_nonneg] using hnat
  · simpa [abs_neg, abs_of_nonneg] using hnat

private theorem summableNatIntGeometricProduct {qN qJ : ℝ}
    (hqN0 : 0 ≤ qN) (hqN1 : qN < 1)
    (hqJ0 : 0 < qJ) (hqJ1 : qJ < 1) :
    Summable (fun z : ℕ × ℤ => qN ^ z.1 * qJ ^ |(z.2 : ℝ)|) := by
  have hN : Summable (fun n : ℕ => qN ^ n) :=
    summable_geometric_of_lt_one hqN0 hqN1
  have hJ := summableIntGeometricAbs hqJ0 hqJ1
  apply (summable_prod_of_nonneg (fun z : ℕ × ℤ =>
    mul_nonneg (pow_nonneg hqN0 _) (Real.rpow_nonneg hqJ0.le _))).2
  constructor
  · intro n
    exact hJ.mul_left (qN ^ n)
  · have houter : Summable (fun n : ℕ =>
        ∑' j : ℤ, qN ^ n * qJ ^ |(j : ℝ)|) := by
      have houter' := hN.mul_right (∑' j : ℤ, qJ ^ |(j : ℝ)|)
      simpa only [hJ.tsum_mul_left] using houter'
    exact houter

private theorem rpow_min_le_rpow_product {x : ℝ} (hx : 0 < x)
    {theta rho : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hrho : 0 < rho) :
    (min 1 x) ^ rho ≤ x ^ (theta * rho) := by
  have hmin : min 1 x ≤ x ^ theta := by
    by_cases hx1 : x ≤ 1
    · rw [min_eq_right hx1]
      exact Real.self_le_rpow_of_le_one hx.le hx1 htheta1.le
    · have hx1' : 1 ≤ x := le_of_not_ge hx1
      rw [min_eq_left hx1']
      exact Real.one_le_rpow hx1' htheta0.le
  calc
    (min 1 x) ^ rho ≤ (x ^ theta) ^ rho :=
      Real.rpow_le_rpow (by positivity) hmin hrho.le
    _ = x ^ (theta * rho) := (Real.rpow_mul hx.le theta rho).symm

/-- The coefficient array in `ha:square` is summable with every source
choice `0 < epsilon < rho`. The proof uses a fractional power `theta` of
the minimum, choosing `theta*rho=epsilon/2`; the remaining two factors are
ordinary geometric series. -/
theorem localizedSquareCoefficient_summable
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (epsilon rho : ℝ) (hepsilon : 0 < epsilon) (hepsilonRho : epsilon < rho) :
    Summable (fun z : ℕ × ℤ =>
      Real.rpow 2 (-epsilon * (z.1 : ℝ)) *
        (localizedSquareCoefficient c hc hcNon z.2 z.1) ^ rho) := by
  let C := localizedUnweightedIncrementConstant c hc hcNon *
    frequencyProjectionFiniteSquareFunctionBound 2
  let theta := epsilon / (2 * rho)
  let qN := Real.rpow 2 (-(epsilon / 2))
  let qJ := Real.rpow 2 (-(localizedIncrementSigma c * (epsilon / 2)))
  have hrho : 0 < rho := lt_trans hepsilon hepsilonRho
  have htheta0 : 0 < theta := by
    dsimp [theta]
    positivity
  have htheta1 : theta < 1 := by
    dsimp [theta]
    rw [div_lt_one (by positivity)]
    linarith
  have hA0 : 0 ≤ localizedUnweightedIncrementConstant c hc hcNon := by
    unfold localizedUnweightedIncrementConstant
    exact le_trans (by norm_num : 0 ≤ (4 : ℝ)) (le_max_left _ _)
  have hL0 : 0 ≤ frequencyProjectionFiniteSquareFunctionBound 2 := by
    unfold frequencyProjectionFiniteSquareFunctionBound
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (frequencyProjectionSignedLpBound_nonneg (by norm_num))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hA0 hL0
  have hqN0 : 0 < qN := by
    dsimp [qN]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hqN1 : qN < 1 := by
    dsimp [qN]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have h : 0 < epsilon / 2 := by positivity
    linarith
  have hsigma : 0 < localizedIncrementSigma c := by
    unfold localizedIncrementSigma
    have hdelta : 0 < localizedProgressionDelta c := by
      unfold localizedProgressionDelta
      positivity
    exact lt_min (by norm_num) hdelta
  have hqJ0 : 0 < qJ := by
    dsimp [qJ]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hqJ1 : qJ < 1 := by
    dsimp [qJ]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have h : 0 < localizedIncrementSigma c * (epsilon / 2) := by positivity
    linarith
  have hprod := summableNatIntGeometricProduct hqN0.le hqN1 hqJ0 hqJ1
  have hCoeffNonneg (z : ℕ × ℤ) :
      0 ≤ localizedSquareCoefficient c hc hcNon z.2 z.1 := by
    unfold localizedSquareCoefficient
    exact mul_nonneg (mul_nonneg hA0 hL0)
      (le_min (by norm_num) (Real.rpow_nonneg (by norm_num) _))
  have hbound (z : ℕ × ℤ) :
      Real.rpow 2 (-epsilon * (z.1 : ℝ)) *
          (localizedSquareCoefficient c hc hcNon z.2 z.1) ^ rho ≤
        C ^ rho * (qN ^ z.1 * qJ ^ |(z.2 : ℝ)|) := by
    have hmin : min 1 (Real.rpow 2
        ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|)) ≤
        (Real.rpow 2 ((z.1 : ℝ) - localizedIncrementSigma c *
          |(z.2 : ℝ)|)) ^ theta := by
      let x := Real.rpow 2
        ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|)
      have hxpos : 0 < x := by
        dsimp [x]
        exact Real.rpow_pos_of_pos (by norm_num) _
      by_cases hx : x ≤ 1
      · rw [min_eq_right hx]
        exact Real.self_le_rpow_of_le_one hxpos.le hx htheta1.le
      · rw [min_eq_left (le_of_not_ge hx)]
        exact Real.one_le_rpow (le_of_not_ge hx) htheta0.le
    have hminRho :
        (min 1 (Real.rpow 2
          ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|))) ^ rho ≤
        (Real.rpow 2 ((z.1 : ℝ) - localizedIncrementSigma c *
          |(z.2 : ℝ)|)) ^ (theta * rho) := by
      calc
        _ ≤ (Real.rpow 2 ((z.1 : ℝ) - localizedIncrementSigma c *
            |(z.2 : ℝ)|) ^ theta) ^ rho :=
          Real.rpow_le_rpow (le_min (by norm_num)
            (Real.rpow_nonneg (by norm_num) _)) hmin hrho.le
        _ = _ := (Real.rpow_mul
          (Real.rpow_nonneg (by norm_num) _) theta rho).symm
    have hmin0 : 0 ≤ min 1 (Real.rpow 2
        ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|)) :=
      le_min (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    have hCoeffRpow :
        (localizedSquareCoefficient c hc hcNon z.2 z.1) ^ rho =
          C ^ rho * (min 1 (Real.rpow 2
            ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|))) ^ rho := by
      change ((localizedUnweightedIncrementConstant c hc hcNon *
          frequencyProjectionFiniteSquareFunctionBound 2) *
        min 1 (Real.rpow 2
          ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|))) ^ rho = _
      rw [Real.mul_rpow (mul_nonneg hA0 hL0) hmin0]
    have hExp :
        Real.rpow 2 (-epsilon * (z.1 : ℝ)) *
            (Real.rpow 2 ((z.1 : ℝ) - localizedIncrementSigma c *
              |(z.2 : ℝ)|)) ^ (theta * rho) =
          qN ^ z.1 * qJ ^ |(z.2 : ℝ)| := by
      dsimp [qN, qJ]
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (-(epsilon / 2)) z.1,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
          (-(localizedIncrementSigma c * (epsilon / 2))) |(z.2 : ℝ)|,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
          ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|) (theta * rho)]
      have hthetaRho : theta * rho = epsilon / 2 := by
        dsimp [theta]
        field_simp
      rw [hthetaRho]
      have hexp :
          (-epsilon * (z.1 : ℝ)) +
              ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|) *
                (epsilon / 2) =
            (-(epsilon / 2) * (z.1 : ℝ)) +
              (-(localizedIncrementSigma c * (epsilon / 2)) *
                |(z.2 : ℝ)|) := by ring
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hexp,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc
      _ = Real.rpow 2 (-epsilon * (z.1 : ℝ)) *
          (C ^ rho * (min 1 (Real.rpow 2
            ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|))) ^ rho) := by
          rw [hCoeffRpow]
      _ = C ^ rho *
          (Real.rpow 2 (-epsilon * (z.1 : ℝ)) *
            (min 1 (Real.rpow 2
              ((z.1 : ℝ) - localizedIncrementSigma c * |(z.2 : ℝ)|))) ^ rho) := by ring
      _ ≤ C ^ rho *
          (Real.rpow 2 (-epsilon * (z.1 : ℝ)) *
            (Real.rpow 2 ((z.1 : ℝ) - localizedIncrementSigma c *
              |(z.2 : ℝ)|)) ^ (theta * rho)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hC0 _)
          exact mul_le_mul_of_nonneg_left hminRho
            (Real.rpow_nonneg (by norm_num) _)
      _ = C ^ rho * (qN ^ z.1 * qJ ^ |(z.2 : ℝ)|) := by rw [hExp]
  apply Summable.of_nonneg_of_le
  · intro z
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (hCoeffNonneg z) _)
  · exact hbound
  · exact hprod.mul_left (C ^ rho)

end

end FractionalPrimes.Literature.Harmonic

end
