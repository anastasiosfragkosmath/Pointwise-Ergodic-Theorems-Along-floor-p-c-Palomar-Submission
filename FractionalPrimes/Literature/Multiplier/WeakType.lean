module

public import FractionalPrimes.Literature.Multiplier.KernelHormander
public import FractionalPrimes.Literature.Multiplier.DiscreteCZDecomposition
public import FractionalPrimes.DiscreteLpBridge
public import FractionalPrimes.FourierSequence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Weak `(1,1)` estimate for the periodic multiplier (`lp:weak-type`)

The first helper records the `L∞` consequence of the symbol's zeroth-order
hypothesis. The full weak-type proof is developed below in source order.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The zeroth-order part of `SymbolData` bounds the symbol by `D` almost
everywhere on the unit circle. The representative interval has only the
zero and seam endpoints to remove; those are null for Lebesgue measure. -/
theorem torusSymbol_norm_le_D_ae {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) :
    ∀ᵐ ξ ∂torusHaar, ‖torusSymbol h ξ‖ ≤ D := by
  have hIoc : ∀ᵐ x : ℝ ∂(volume.restrict
      (Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1))), ‖m x‖ ≤ D := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Measure.ae_ne volume (0 : ℝ),
      Measure.ae_ne volume (1 / 2 : ℝ)] with x hx0 hxhalf hxI
    have hxI' : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      simpa only [Set.mem_Ioc,
        show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num] using hxI
    have hxpos : 0 < |x| := abs_pos.mpr hx0
    have hxlt : |x| < 1 / 2 := by
      rw [abs_lt]
      constructor
      · exact hxI'.1
      · by_contra! hge
        have heq : x = 1 / 2 := le_antisymm hxI'.2 hge
        exact hxhalf heq
    have hbound := h.weightedDerivativeBound x hxpos hxlt
    have h1 : 0 ≤ ‖x * deriv m x‖ := norm_nonneg _
    have h2 : 0 ≤ ‖x ^ 2 * iteratedDeriv 2 m x‖ := norm_nonneg _
    linarith
  have hmp : MeasurePreserving ((↑) : ℝ → Torus)
      (volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1))) torusHaar := by
    have h' := AddCircle.measurePreserving_mk (T := (1 : ℝ)) (-(1 / 2 : ℝ))
    simpa [torusHaar, AddCircle.volume_eq_smul_haarAddCircle] using h'
  have hmeas : AEMeasurable ((↑) : ℝ → Torus)
      (volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1))) :=
    hmp.measurable.aemeasurable
  have hset : MeasurableSet {ξ : Torus | ‖torusSymbol h ξ‖ ≤ D} :=
    measurableSet_le (torusSymbol_measurable h).norm measurable_const
  have hcomp : ∀ᵐ x : ℝ ∂(volume.restrict
      (Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1))),
      ‖torusSymbol h (x : Torus)‖ ≤ D := by
    filter_upwards [hIoc] with x hx
    simpa only [torusSymbol_coe] using hx
  have hmap := (ae_map_iff hmeas hset).2 hcomp
  simpa only [hmp.map_eq] using hmap

/-- Consequently, the exact `L²` multiplier bound is at most the source
constant `D`, including the zero-constant case. -/
theorem norm_torusSymbolLp_le_D {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) : ‖torusSymbolLp h‖ ≤ D := by
  letI : IsProbabilityMeasure torusHaar := torusHaar_isProbability
  have hbound : ∀ᵐ ξ ∂torusHaar,
      ‖(torusSymbolLp h : Torus → ℂ) ξ‖ ≤ D := by
    filter_upwards [torusSymbolLp_coeFn h, torusSymbol_norm_le_D_ae h]
      with ξ hcoe hsymbol
    rw [hcoe]
    exact hsymbol
  have hn := Lp.norm_le_of_ae_bound (f := torusSymbolLp h)
    h.D_nonneg hbound
  simpa [torusHaar, AddCircle.volume_eq_smul_haarAddCircle] using hn


/-- Chebyshev's inequality for a sequence in `ℓ²`, stated as the exact
finite cardinality estimate needed for the multiplier level set. -/
private theorem lp_level_ncard_sq_le (u : lp (fun _ : ℤ => ℂ) 2) (r : ℝ)
    (hr : 0 < r) :
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
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ← hcardReal,
    ENNReal.coe_toReal, hnorm] at hreal
  have hrN : (rN : ℝ) = r := rfl
  rw [hrN] at hreal
  have htarget : (E.ncard : ℝ) * r ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith [hreal]
  simpa [E] using htarget

/-- Positive level sets of an `ℓ²` sequence are finite, for use when
counting unions of the three Calderón–Zygmund level sets. -/
private theorem lp_strict_level_set_finite
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

/-- The multiplier's `ℓ²` bound and discrete Chebyshev estimate give the
exact level-set square bound with the symbol constant `D`. -/
theorem TmL2_level_ncard_sq_le {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (u : lp (fun _ : ℤ => ℂ) 2) (r : ℝ)
    (hr : 0 < r) :
    (Set.ncard {x : ℤ | r < ‖TmL2 h u x‖} : ℝ) * r ^ 2 ≤
      D ^ 2 * ‖u‖ ^ 2 := by
  have hcheb := lp_level_ncard_sq_le (TmL2 h u) r hr
  have hbound : ‖TmL2 h u‖ ≤ D * ‖u‖ := by
    calc
      ‖TmL2 h u‖ ≤ ‖torusSymbolLp h‖ * ‖u‖ := norm_TmL2_le h u
      _ ≤ D * ‖u‖ :=
        mul_le_mul_of_nonneg_right (norm_torusSymbolLp_le_D h) (norm_nonneg _)
  have hsq :=
    (sq_le_sq₀ (norm_nonneg (TmL2 h u))
      (mul_nonneg h.D_nonneg (norm_nonneg u))).2 hbound
  calc
    (Set.ncard {x : ℤ | r < ‖TmL2 h u x‖} : ℝ) * r ^ 2 ≤
        ‖TmL2 h u‖ ^ 2 := hcheb
    _ ≤ (D * ‖u‖) ^ 2 := hsq
    _ = D ^ 2 * ‖u‖ ^ 2 := by ring

/-- The `ℓ²` norm of a finite-support sequence is exactly the square root of
the counting-measure square-sum used by the discrete CZ decomposition. -/
theorem finiteIntegerSequenceL2_norm_sq_eq_discreteL2NormSq
    (g : ℤ → ℂ) (hg : g.HasFiniteSupport) :
    ‖finiteIntegerSequenceL2 hg.toFinset g‖ ^ 2 = discreteL2NormSq g := by
  have hrep : (finiteIntegerSequenceL2 hg.toFinset g : ℤ → ℂ) = g := by
    funext x
    rw [finiteIntegerSequenceL2_apply]
    by_cases hx : x ∈ hg.toFinset
    · simp [hx]
    · have hgx : g x = 0 := by
        by_contra hne
        exact hx (hg.mem_toFinset.mpr (Function.mem_support.mpr hne))
      simp [hx, hgx]
  have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
    (by norm_num : 0 < (2 : ENNReal).toReal)
    (finiteIntegerSequenceL2 hg.toFinset g)
  have hcast : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  simp only [hcast, hrep] at hnorm
  have htwo : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [htwo, Real.rpow_natCast] at hnorm
  simpa only [discreteL2NormSq] using hnorm

/-- The good part in the exact dyadic CZ data obeys the weak level-set
bound from the source, with coefficient `8 D / threshold`. -/
theorem kernelWeakType_goodPart_count_le {m : ℝ → ℂ} {D threshold : ℝ}
    (h : SymbolData m D) (hD : 0 < D) (hthreshold : 0 < threshold)
    (f : ℤ → ℂ)
    (d : DiscreteCZDecompositionData f (threshold / D)) :
    (Set.ncard {x : ℤ | threshold / 2 < ‖TmL2 h
      (finiteIntegerSequenceL2 d.good_finite_support.toFinset d.goodPart) x‖} : ℝ)
      ≤ 8 * D / threshold * discreteL1Norm f := by
  let g : lp (fun _ : ℤ => ℂ) 2 :=
    finiteIntegerSequenceL2 d.good_finite_support.toFinset d.goodPart
  have hcheb := TmL2_level_ncard_sq_le h g (threshold / 2) (by positivity)
  have hgood : ‖g‖ ^ 2 ≤ 2 * (threshold / D) * discreteL1Norm f := by
    rw [finiteIntegerSequenceL2_norm_sq_eq_discreteL2NormSq d.goodPart
      d.good_finite_support]
    exact d.good_l2_sq_bound
  have hden : 0 < (threshold / 2) ^ 2 := sq_pos_of_pos (by positivity)
  have hcount :
      (Set.ncard {x : ℤ | threshold / 2 < ‖TmL2 h g x‖} : ℝ) ≤
        D ^ 2 * ‖g‖ ^ 2 / (threshold / 2) ^ 2 := by
    apply (le_div_iff₀ hden).2
    simpa [mul_comm] using hcheb
  change (Set.ncard {x : ℤ | threshold / 2 < ‖TmL2 h g x‖} : ℝ) ≤ _
  calc
    _ ≤ D ^ 2 * ‖g‖ ^ 2 / (threshold / 2) ^ 2 := hcount
    _ ≤ D ^ 2 * (2 * (threshold / D) * discreteL1Norm f) /
        (threshold / 2) ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgood (sq_nonneg D)) hden.le
    _ = 8 * D / threshold * discreteL1Norm f := by
      field_simp [ne_of_gt hD, ne_of_gt hthreshold]
      ring


/-- For each CZ bad piece, the exact finite-input convolution formula and
its zero mean give the source's kernel-difference cancellation identity. -/
theorem TmL2_badPiece_cancellation {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (f : ℤ → ℂ) (alpha : ℝ)
    (d : DiscreteCZDecompositionData f alpha)
    (i : ℕ × ℤ) (hi : i ∈ d.intervals) (x : ℤ) :
    TmL2 h
      (finiteSequenceL2
        (Finsupp.ofSupportFinite (dyadicBadPiece f i)
          (d.bad_finite_support i hi))) x =
      ∑ y ∈ dyadicIntervals i.1 i.2,
        (kernelCoefficient (torusSymbol h) (x - y) -
          kernelCoefficient (torusSymbol h)
            (x - i.2 * (2 : ℤ) ^ i.1)) * dyadicBadPiece f i y := by
  classical
  let b : ℤ →₀ ℂ :=
    Finsupp.ofSupportFinite (dyadicBadPiece f i) (d.bad_finite_support i hi)
  have hbcoe : (b : ℤ → ℂ) = dyadicBadPiece f i :=
    Finsupp.ofSupportFinite_coe
  have hbsupport : b.support = (d.bad_finite_support i hi).toFinset := by
    simpa [b] using Finsupp.ofSupportFinite_support (d.bad_finite_support i hi)
  have hsub : b.support ⊆ dyadicIntervals i.1 i.2 := by
    intro y hy
    rw [hbsupport] at hy
    exact d.bad_support i hi ((d.bad_finite_support i hi).mem_toFinset.mp hy)
  have hsum :
      (∑ y ∈ b.support,
        kernelCoefficient (torusSymbol h) (x - y) * b y) =
      ∑ y ∈ dyadicIntervals i.1 i.2,
        kernelCoefficient (torusSymbol h) (x - y) * dyadicBadPiece f i y := by
    calc
      _ = ∑ y ∈ b.support,
          kernelCoefficient (torusSymbol h) (x - y) * dyadicBadPiece f i y := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [← congrFun hbcoe y]
      _ = ∑ y ∈ dyadicIntervals i.1 i.2,
          kernelCoefficient (torusSymbol h) (x - y) * dyadicBadPiece f i y := by
        apply Finset.sum_subset hsub
        intro y hyI hynot
        have hzero : b y = 0 := Finsupp.notMem_support_iff.mp hynot
        rw [← congrFun hbcoe y, hzero]
        simp
  change TmL2 h (finiteSequenceL2 b) x = _
  rw [TmL2_finite_convolution h b x]
  let a : ℤ := i.2 * (2 : ℤ) ^ i.1
  have hconst :
      (∑ y ∈ dyadicIntervals i.1 i.2,
        kernelCoefficient (torusSymbol h) (x - a) * dyadicBadPiece f i y) = 0 := by
    rw [← Finset.mul_sum, d.bad_mean_zero i hi, mul_zero]
  calc
    (∑ y ∈ b.support,
      kernelCoefficient (torusSymbol h) (x - y) * b y) =
        ∑ y ∈ dyadicIntervals i.1 i.2,
          kernelCoefficient (torusSymbol h) (x - y) * dyadicBadPiece f i y := hsum
    _ = ∑ y ∈ dyadicIntervals i.1 i.2,
          (kernelCoefficient (torusSymbol h) (x - y) -
            kernelCoefficient (torusSymbol h) (x - a)) * dyadicBadPiece f i y := by
      calc
        _ = (∑ y ∈ dyadicIntervals i.1 i.2,
              kernelCoefficient (torusSymbol h) (x - y) * dyadicBadPiece f i y) -
            (∑ y ∈ dyadicIntervals i.1 i.2,
              kernelCoefficient (torusSymbol h) (x - a) * dyadicBadPiece f i y) := by
          rw [hconst]
          ring
        _ = ∑ y ∈ dyadicIntervals i.1 i.2,
              (kernelCoefficient (torusSymbol h) (x - y) * dyadicBadPiece f i y -
                kernelCoefficient (torusSymbol h) (x - a) * dyadicBadPiece f i y) := by
          rw [← Finset.sum_sub_distrib]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro y hy
          ring

/-- The complement of a fivefold enlargement is strictly outside the
Hörmander tail for every point of the original interval. -/
theorem integerIntervalEnlargement_complement_strict_tail
    (a x y : ℤ) (L : ℕ) (hL : 0 < L)
    (hy : y ∈ Finset.Ico a (a + (L : ℤ)))
    (hx : x ∉ integerIntervalEnlargement a L) :
    2 * |y - a| < |x - a| := by
  have hLZ : 0 < (L : ℤ) := by exact_mod_cast hL
  have hy' : a ≤ y ∧ y < a + (L : ℤ) := by
    simpa only [Finset.mem_Ico] using hy
  have hx' : x < a - 2 * (L : ℤ) ∨ a + 3 * (L : ℤ) ≤ x := by
    by_contra hnot
    rcases not_or.mp hnot with ⟨hleft, hright⟩
    apply hx
    simpa [integerIntervalEnlargement, Finset.mem_Ico] using
      And.intro (not_lt.mp hleft) (not_le.mp hright)
  rcases hx' with hleft | hright
  · have hyabs : |y - a| = y - a := abs_of_nonneg (by omega)
    have hxneg : x - a < 0 := by omega
    have hxabs : |x - a| = -(x - a) := abs_of_neg hxneg
    rw [hyabs, hxabs]
    omega
  · have hyabs : |y - a| = y - a := abs_of_nonneg (by omega)
    have hxpos : 0 < x - a := by omega
    have hxabs : |x - a| = x - a := abs_of_pos hxpos
    rw [hyabs, hxabs]
    omega

/-- The dyadic interval `[a 2^k,(a+1)2^k)` has length `2^k`, so the
previous geometric lemma applies with its exact left endpoint. -/
theorem dyadicIntervals_enlargement_complement_strict_tail
    (k : ℕ) (a x y : ℤ) (hy : y ∈ dyadicIntervals k a)
    (hx : x ∉ integerIntervalEnlargement (a * (2 : ℤ) ^ k) (2 ^ k)) :
    2 * |y - a * (2 : ℤ) ^ k| < |x - a * (2 : ℤ) ^ k| := by
  let left : ℤ := a * (2 : ℤ) ^ k
  let length : ℕ := 2 ^ k
  have hlength : (length : ℤ) = (2 : ℤ) ^ k := by
    dsimp [length]
  have hupper : (a + 1) * (2 : ℤ) ^ k = left + (length : ℤ) := by
    rw [hlength]
    dsimp [left]
    ring
  have hy' : left ≤ y ∧ y < (a + 1) * (2 : ℤ) ^ k := by
    simpa only [left, mem_dyadicIntervals] using hy
  have hyI : y ∈ Finset.Ico left (left + (length : ℤ)) := by
    rw [Finset.mem_Ico]
    exact ⟨hy'.1, by simpa [hupper] using hy'.2⟩
  have hlengthpos : 0 < length := by
    dsimp [length]
    positivity
  simpa only [left] using
    integerIntervalEnlargement_complement_strict_tail
      left x y length hlengthpos hyI hx

/-- Translation identifies points outside an enlargement with a subset of
the strict integer Hörmander tail, retaining the tail summability. -/
theorem kernelDifference_summable_tsum_outside_enlargement_le
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D)
    (center shift : ℤ) (S : Finset ℤ)
    (hgeom : ∀ x : ℤ, x ∉ S → 2 * |shift| < |x - center|) :
    Summable (fun x : {x : ℤ // x ∉ S} =>
      ‖kernelCoefficient (torusSymbol h) (x.1 - center - shift) -
        kernelCoefficient (torusSymbol h) (x.1 - center)‖) ∧
    (∑' x : {x : ℤ // x ∉ S},
      ‖kernelCoefficient (torusSymbol h) (x.1 - center - shift) -
        kernelCoefficient (torusSymbol h) (x.1 - center)‖) ≤ H₀ * D := by
  classical
  let Tail := {n : ℤ // 2 * |shift| < |n|}
  let outside := {x : ℤ // x ∉ S}
  let translate : outside → Tail := fun x =>
    ⟨x.1 - center, hgeom x.1 x.2⟩
  have hinj : Function.Injective translate := by
    intro x y heq
    apply Subtype.ext
    have hval := congrArg Subtype.val heq
    dsimp [translate] at hval
    omega
  have htail : Summable (fun n : Tail =>
      ‖kernelCoefficient (torusSymbol h) (n.1 - shift) -
        kernelCoefficient (torusSymbol h) n.1‖) := kernelHormander_summable h shift
  have hsource : Summable (fun x : outside =>
      ‖kernelCoefficient (torusSymbol h) (x.1 - center - shift) -
        kernelCoefficient (torusSymbol h) (x.1 - center)‖) := by
    change Summable ((fun n : Tail =>
      ‖kernelCoefficient (torusSymbol h) (n.1 - shift) -
        kernelCoefficient (torusSymbol h) n.1‖) ∘ translate)
    exact htail.comp_injective hinj
  have hcompare :
      (∑' x : outside,
        ‖kernelCoefficient (torusSymbol h) (x.1 - center - shift) -
          kernelCoefficient (torusSymbol h) (x.1 - center)‖) ≤
      (∑' n : Tail,
        ‖kernelCoefficient (torusSymbol h) (n.1 - shift) -
          kernelCoefficient (torusSymbol h) n.1‖) := by
    exact hsource.tsum_le_tsum_of_inj translate hinj
      (fun n _ => norm_nonneg _) (fun _ => le_rfl) htail
  refine ⟨hsource, ?_⟩
  calc
    _ ≤ ∑' n : Tail,
        ‖kernelCoefficient (torusSymbol h) (n.1 - shift) -
          kernelCoefficient (torusSymbol h) n.1‖ := hcompare
    _ ≤ H₀ * D := kernelHormander h shift

/-- Cancellation and the strict-tail kernel estimate give summability and
the exact `H₀ D` bound for one bad piece outside its fivefold enlargement. -/
theorem TmL2_badPiece_summable_and_l1_outside_enlargement_le
    {m : ℝ → ℂ} {D alpha : ℝ} (h : SymbolData m D)
    (f : ℤ → ℂ) (d : DiscreteCZDecompositionData f alpha)
    (i : ℕ × ℤ) (hi : i ∈ d.intervals) :
    Summable (fun x : {x : ℤ // x ∉ integerIntervalEnlargement
        (i.2 * (2 : ℤ) ^ i.1) (2 ^ i.1)} =>
      ‖TmL2 h
        (finiteSequenceL2
          (Finsupp.ofSupportFinite (dyadicBadPiece f i)
            (d.bad_finite_support i hi))) x.1‖) ∧
    (∑' x : {x : ℤ // x ∉ integerIntervalEnlargement
        (i.2 * (2 : ℤ) ^ i.1) (2 ^ i.1)},
      ‖TmL2 h
        (finiteSequenceL2
          (Finsupp.ofSupportFinite (dyadicBadPiece f i)
            (d.bad_finite_support i hi))) x.1‖) ≤
      H₀ * D * discreteL1Norm (dyadicBadPiece f i) := by
  classical
  let I := dyadicIntervals i.1 i.2
  let center : ℤ := i.2 * (2 : ℤ) ^ i.1
  let length : ℕ := 2 ^ i.1
  let bad : ℤ → ℂ := dyadicBadPiece f i
  let badL2 := finiteSequenceL2
    (Finsupp.ofSupportFinite bad (d.bad_finite_support i hi))
  let outside := {x : ℤ // x ∉ integerIntervalEnlargement center length}
  have hsupport : Function.support bad ⊆ (I : Set ℤ) := d.bad_support i hi
  have hbadL1 : discreteL1Norm bad = ∑ y ∈ I, ‖bad y‖ :=
    discreteL1Norm_eq_sum_of_support_subset bad I hsupport
  have hkernel (y : ℤ) (hy : y ∈ I) :
      Summable (fun x : outside =>
        ‖kernelCoefficient (torusSymbol h) (x.1 - y) -
          kernelCoefficient (torusSymbol h) (x.1 - center)‖) ∧
      (∑' x : outside,
        ‖kernelCoefficient (torusSymbol h) (x.1 - y) -
          kernelCoefficient (torusSymbol h) (x.1 - center)‖) ≤ H₀ * D := by
    have hgeom : ∀ x : ℤ,
        x ∉ integerIntervalEnlargement center length →
          2 * |y - center| < |x - center| := by
      intro x hx
      have htail := dyadicIntervals_enlargement_complement_strict_tail
        i.1 i.2 x y (by simpa [I] using hy) (by simpa [center, length] using hx)
      simpa [center] using htail
    have htail := kernelDifference_summable_tsum_outside_enlargement_le
      h center (y - center) (integerIntervalEnlargement center length) hgeom
    have hindex (x : outside) :
        x.1 - y = x.1 - center - (y - center) := by ring
    refine ⟨?_, ?_⟩
    · simpa only [hindex] using htail.1
    · simpa only [hindex] using htail.2
  let majorant (x : outside) : ℝ :=
    ∑ y ∈ I, ‖bad y‖ *
      ‖kernelCoefficient (torusSymbol h) (x.1 - y) -
        kernelCoefficient (torusSymbol h) (x.1 - center)‖
  have hmajorantSummable : Summable majorant := by
    change Summable (fun x : outside => ∑ y ∈ I, ‖bad y‖ *
      ‖kernelCoefficient (torusSymbol h) (x.1 - y) -
        kernelCoefficient (torusSymbol h) (x.1 - center)‖)
    apply summable_sum
    intro y hy
    exact (hkernel y hy).1.mul_left ‖bad y‖
  have hpoint (x : outside) : ‖TmL2 h badL2 x.1‖ ≤ majorant x := by
    change ‖TmL2 h
      (finiteSequenceL2
        (Finsupp.ofSupportFinite (dyadicBadPiece f i)
          (d.bad_finite_support i hi))) x.1‖ ≤ majorant x
    rw [TmL2_badPiece_cancellation h f alpha d i hi x.1]
    dsimp [majorant, bad, I]
    calc
      ‖∑ y ∈ dyadicIntervals i.1 i.2,
          (kernelCoefficient (torusSymbol h) (x.1 - y) -
            kernelCoefficient (torusSymbol h) (x.1 - center)) *
              dyadicBadPiece f i y‖ ≤
          ∑ y ∈ dyadicIntervals i.1 i.2,
            ‖(kernelCoefficient (torusSymbol h) (x.1 - y) -
              kernelCoefficient (torusSymbol h) (x.1 - center)) *
                dyadicBadPiece f i y‖ := norm_sum_le _ _
      _ = ∑ y ∈ dyadicIntervals i.1 i.2,
            ‖dyadicBadPiece f i y‖ *
              ‖kernelCoefficient (torusSymbol h) (x.1 - y) -
                kernelCoefficient (torusSymbol h) (x.1 - center)‖ := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [norm_mul, mul_comm]
  have hpointNonneg (x : outside) : 0 ≤ ‖TmL2 h badL2 x.1‖ := norm_nonneg _
  have houtputSummable : Summable (fun x : outside => ‖TmL2 h badL2 x.1‖) :=
    Summable.of_nonneg_of_le hpointNonneg hpoint hmajorantSummable
  have hsumMajorant := Summable.tsum_finsetSum (fun y hy =>
    (hkernel y hy).1.mul_left ‖bad y‖)
  have hswap : (∑' x : outside, majorant x) =
      ∑ y ∈ I, ‖bad y‖ *
        (∑' x : outside,
          ‖kernelCoefficient (torusSymbol h) (x.1 - y) -
            kernelCoefficient (torusSymbol h) (x.1 - center)‖) := by
    dsimp [majorant]
    rw [hsumMajorant]
    apply Finset.sum_congr rfl
    intro y hy
    exact (hkernel y hy).1.tsum_mul_left ‖bad y‖
  refine ⟨houtputSummable, ?_⟩
  calc
    _ ≤ ∑' x : outside, majorant x :=
      Summable.tsum_le_tsum hpoint houtputSummable hmajorantSummable
    _ = ∑ y ∈ I, ‖bad y‖ *
          (∑' x : outside,
            ‖kernelCoefficient (torusSymbol h) (x.1 - y) -
              kernelCoefficient (torusSymbol h) (x.1 - center)‖) := hswap
    _ ≤ ∑ y ∈ I, ‖bad y‖ * (H₀ * D) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hkernel y hy).2 (norm_nonneg _)
    _ = (∑ y ∈ I, ‖bad y‖) * (H₀ * D) := by rw [Finset.sum_mul]
    _ = discreteL1Norm bad * (H₀ * D) := by rw [← hbadL1]
    _ = H₀ * D * discreteL1Norm bad := by ring

/-- The scalar bad-piece estimate projected from its summability package. -/
theorem TmL2_badPiece_l1_outside_enlargement_le
    {m : ℝ → ℂ} {D alpha : ℝ} (h : SymbolData m D)
    (f : ℤ → ℂ) (d : DiscreteCZDecompositionData f alpha)
    (i : ℕ × ℤ) (hi : i ∈ d.intervals) :
    (∑' x : {x : ℤ // x ∉ integerIntervalEnlargement
        (i.2 * (2 : ℤ) ^ i.1) (2 ^ i.1)},
      ‖TmL2 h
        (finiteSequenceL2
          (Finsupp.ofSupportFinite (dyadicBadPiece f i)
            (d.bad_finite_support i hi))) x.1‖) ≤
      H₀ * D * discreteL1Norm (dyadicBadPiece f i) :=
  (TmL2_badPiece_summable_and_l1_outside_enlargement_le h f d i hi).2

/-- A single dyadic bad piece, embedded in the sequence `ℓ²` space. -/
noncomputable def finiteBadPieceL2 (f : ℤ → ℂ) (i : ℕ × ℤ) :
    lp (fun _ : ℤ => ℂ) 2 :=
  finiteSequenceL2
    (Finsupp.ofSupportFinite (dyadicBadPiece f i)
      (dyadicBadPiece_hasFiniteSupport f i))

private theorem finiteBadPieceL2_apply (f : ℤ → ℂ) (i : ℕ × ℤ) (x : ℤ) :
    finiteBadPieceL2 f i x = dyadicBadPiece f i x := by
  change finiteSequenceL2
    (Finsupp.ofSupportFinite (dyadicBadPiece f i)
      (dyadicBadPiece_hasFiniteSupport f i)) x = _
  rw [finiteSequenceL2_apply]
  exact congrFun (Finsupp.ofSupportFinite_coe
    (f := dyadicBadPiece f i)
    (hf := dyadicBadPiece_hasFiniteSupport f i)) x

/-- The finite sum of all bad pieces in the Calderón–Zygmund decomposition,
embedded in sequence `ℓ²`. -/
noncomputable def finiteCZBadPartL2 {alpha : ℝ} (f : ℤ → ℂ)
    (d : DiscreteCZDecompositionData f alpha) : lp (fun _ : ℤ => ℂ) 2 :=
  ∑ i ∈ d.intervals, finiteBadPieceL2 f i

/-- The union of the exact fivefold enlargements of a finite dyadic family. -/
def dyadicCZEnlargementUnion (S : Finset (ℕ × ℤ)) : Finset ℤ :=
  S.biUnion (fun i =>
    integerIntervalEnlargement (i.2 * (2 : ℤ) ^ i.1) (2 ^ i.1))

/-- The union of the exact fivefold enlargements has the source cardinality
bound when the CZ decomposition is taken at height `threshold / D`. -/
theorem dyadicCZEnlargementUnion_card_le {f : ℤ → ℂ} {D threshold : ℝ}
    (hD : 0 < D) (hthreshold : 0 < threshold)
    (d : DiscreteCZDecompositionData f (threshold / D)) :
    ((dyadicCZEnlargementUnion d.intervals).card : ℝ) ≤
      5 * D / threshold * discreteL1Norm f := by
  classical
  let enlargement : ℕ × ℤ → Finset ℤ := fun i =>
    integerIntervalEnlargement (i.2 * (2 : ℤ) ^ i.1) (2 ^ i.1)
  have hUnionCard :
      (dyadicCZEnlargementUnion d.intervals).card ≤
        ∑ i ∈ d.intervals, (enlargement i).card := by
    simpa only [dyadicCZEnlargementUnion, enlargement] using
      (Finset.card_biUnion_le (s := d.intervals)
        (t := fun i : ℕ × ℤ =>
          integerIntervalEnlargement (i.2 * (2 : ℤ) ^ i.1) (2 ^ i.1)))
  have hUnionCardReal :
      ((dyadicCZEnlargementUnion d.intervals).card : ℝ) ≤
        ∑ i ∈ d.intervals, ((enlargement i).card : ℝ) := by
    exact_mod_cast hUnionCard
  have hsumCard :
      (∑ i ∈ d.intervals, ((enlargement i).card : ℝ)) =
        5 * (∑ i ∈ d.intervals,
          ((dyadicIntervals i.1 i.2).card : ℝ)) := by
    simp_rw [enlargement, integerIntervalEnlargement_card,
      dyadicIntervals_card, Nat.cast_mul, Nat.cast_ofNat]
    rw [Finset.mul_sum]
  calc
    ((dyadicCZEnlargementUnion d.intervals).card : ℝ)
        ≤ ∑ i ∈ d.intervals, ((enlargement i).card : ℝ) := hUnionCardReal
    _ = 5 * (∑ i ∈ d.intervals,
          ((dyadicIntervals i.1 i.2).card : ℝ)) := hsumCard
    _ ≤ 5 * (discreteL1Norm f / (threshold / D)) :=
      mul_le_mul_of_nonneg_left d.interval_measure_bound (by norm_num)
    _ = 5 * D / threshold * discreteL1Norm f := by
      field_simp [ne_of_gt hD, ne_of_gt hthreshold]

/-- The bad part is summable and has `ℓ¹` mass at most twice that of the
input outside the union of the exact fivefold enlargements. -/
theorem TmL2_badPart_summable_and_l1_outside_enlargementUnion_le
    {m : ℝ → ℂ} {D alpha : ℝ} (h : SymbolData m D)
    (f : ℤ → ℂ) (d : DiscreteCZDecompositionData f alpha) :
    Summable (fun x : {x : ℤ // x ∉ dyadicCZEnlargementUnion d.intervals} =>
      ‖TmL2 h (finiteCZBadPartL2 f d) x.1‖) ∧
    (∑' x : {x : ℤ // x ∉ dyadicCZEnlargementUnion d.intervals},
      ‖TmL2 h (finiteCZBadPartL2 f d) x.1‖) ≤
      2 * H₀ * D * discreteL1Norm f := by
  classical
  let outside := {x : ℤ // x ∉ dyadicCZEnlargementUnion d.intervals}
  let majorant (x : outside) : ℝ :=
    ∑ i ∈ d.intervals, ‖TmL2 h (finiteBadPieceL2 f i) x.1‖
  have hinputEq (i : ℕ × ℤ) (hi : i ∈ d.intervals) :
      finiteBadPieceL2 f i =
        finiteSequenceL2
          (Finsupp.ofSupportFinite (dyadicBadPiece f i)
            (d.bad_finite_support i hi)) := by
    apply lp.ext
    funext n
    simp only [finiteBadPieceL2, finiteSequenceL2_apply]
  have hlinear :
      TmL2 h (finiteCZBadPartL2 f d) =
        ∑ i ∈ d.intervals, TmL2 h (finiteBadPieceL2 f i) := by
    unfold finiteCZBadPartL2
    calc
      TmL2 h (∑ i ∈ d.intervals, finiteBadPieceL2 f i) =
          TmL2CLM h (∑ i ∈ d.intervals, finiteBadPieceL2 f i) :=
        TmL2_eq_TmL2CLM h _
      _ = ∑ i ∈ d.intervals, TmL2CLM h (finiteBadPieceL2 f i) := by
        rw [map_sum]
      _ = ∑ i ∈ d.intervals, TmL2 h (finiteBadPieceL2 f i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (TmL2_eq_TmL2CLM h (finiteBadPieceL2 f i)).symm
  have hpiece (i : ℕ × ℤ) (hi : i ∈ d.intervals) :
      Summable (fun x : outside =>
        ‖TmL2 h (finiteBadPieceL2 f i) x.1‖) ∧
      (∑' x : outside, ‖TmL2 h (finiteBadPieceL2 f i) x.1‖) ≤
        H₀ * D * discreteL1Norm (dyadicBadPiece f i) := by
    let enlargement := integerIntervalEnlargement
      (i.2 * (2 : ℤ) ^ i.1) (2 ^ i.1)
    let outsideI := {x : ℤ // x ∉ enlargement}
    let inclusion : outside → outsideI := fun x =>
      ⟨x.1, by
        intro hxi
        apply x.property
        change x.1 ∈ d.intervals.biUnion (fun j =>
          integerIntervalEnlargement (j.2 * (2 : ℤ) ^ j.1) (2 ^ j.1))
        exact Finset.mem_biUnion.mpr ⟨i, hi, by simpa [enlargement] using hxi⟩⟩
    have hinj : Function.Injective inclusion := by
      intro x y heq
      apply Subtype.ext
      calc
        x.1 = (inclusion x).1 := rfl
        _ = (inclusion y).1 := congrArg (fun z : outsideI => z.1) heq
        _ = y.1 := rfl
    have hlocal :=
      TmL2_badPiece_summable_and_l1_outside_enlargement_le h f d i hi
    have hlocalSummable : Summable (fun x : outsideI =>
        ‖TmL2 h (finiteBadPieceL2 f i) x.1‖) := by
      simpa only [hinputEq i hi] using hlocal.1
    have hsource : Summable (fun x : outside =>
        ‖TmL2 h (finiteBadPieceL2 f i) x.1‖) := by
      change Summable ((fun x : outsideI =>
        ‖TmL2 h (finiteBadPieceL2 f i) x.1‖) ∘ inclusion)
      exact hlocalSummable.comp_injective hinj
    have hcompare :
        (∑' x : outside, ‖TmL2 h (finiteBadPieceL2 f i) x.1‖) ≤
        (∑' x : outsideI, ‖TmL2 h (finiteBadPieceL2 f i) x.1‖) := by
      exact hsource.tsum_le_tsum_of_inj inclusion hinj
        (fun x _ => norm_nonneg _) (fun _ => le_rfl) hlocalSummable
    refine ⟨hsource, ?_⟩
    calc
      _ ≤ ∑' x : outsideI, ‖TmL2 h (finiteBadPieceL2 f i) x.1‖ := hcompare
      _ ≤ H₀ * D * discreteL1Norm (dyadicBadPiece f i) := by
        simpa only [hinputEq i hi] using hlocal.2
  have hmajorantSummable : Summable majorant := by
    change Summable (fun x : outside =>
      ∑ i ∈ d.intervals, ‖TmL2 h (finiteBadPieceL2 f i) x.1‖)
    apply summable_sum
    intro i hi
    exact (hpiece i hi).1
  have hpoint (x : outside) :
      ‖TmL2 h (finiteCZBadPartL2 f d) x.1‖ ≤ majorant x := by
    have hlinAt := congrArg (fun u : lp (fun _ : ℤ => ℂ) 2 => u x.1) hlinear
    rw [hlinAt]
    dsimp [majorant]
    simp only [lp.coeFn_sum, Finset.sum_apply]
    exact norm_sum_le _ _
  have hpointNonneg (x : outside) :
      0 ≤ ‖TmL2 h (finiteCZBadPartL2 f d) x.1‖ := norm_nonneg _
  have houtputSummable : Summable (fun x : outside =>
      ‖TmL2 h (finiteCZBadPartL2 f d) x.1‖) :=
    Summable.of_nonneg_of_le hpointNonneg hpoint hmajorantSummable
  have hsumMajorant := Summable.tsum_finsetSum (fun i hi => (hpiece i hi).1)
  have hswap : (∑' x : outside, majorant x) =
      ∑ i ∈ d.intervals, ∑' x : outside,
        ‖TmL2 h (finiteBadPieceL2 f i) x.1‖ := by
    dsimp [majorant]
    exact hsumMajorant
  have hHD : 0 ≤ H₀ * D := by
    have hA : 0 ≤ A := by
      rw [A_eq]
      exact mul_nonneg (by positivity) (le_of_lt B_pos)
    rw [H₀_eq]
    exact mul_nonneg (mul_nonneg (by norm_num) hA) h.D_nonneg
  refine ⟨houtputSummable, ?_⟩
  calc
    _ ≤ ∑' x : outside, majorant x :=
      Summable.tsum_le_tsum hpoint houtputSummable hmajorantSummable
    _ = ∑ i ∈ d.intervals, ∑' x : outside,
          ‖TmL2 h (finiteBadPieceL2 f i) x.1‖ := hswap
    _ ≤ ∑ i ∈ d.intervals,
          H₀ * D * discreteL1Norm (dyadicBadPiece f i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hpiece i hi).2
    _ = H₀ * D *
          (∑ i ∈ d.intervals, discreteL1Norm (dyadicBadPiece f i)) := by
      rw [Finset.mul_sum]
    _ ≤ H₀ * D * (2 * discreteL1Norm f) :=
      mul_le_mul_of_nonneg_left d.bad_l1_bound hHD
    _ = 2 * H₀ * D * discreteL1Norm f := by ring

/-- The scalar bad-part estimate projected from its summability package. -/
theorem TmL2_badPart_l1_outside_enlargementUnion_le
    {m : ℝ → ℂ} {D alpha : ℝ} (h : SymbolData m D)
    (f : ℤ → ℂ) (d : DiscreteCZDecompositionData f alpha) :
    (∑' x : {x : ℤ // x ∉ dyadicCZEnlargementUnion d.intervals},
      ‖TmL2 h (finiteCZBadPartL2 f d) x.1‖) ≤
      2 * H₀ * D * discreteL1Norm f :=
  (TmL2_badPart_summable_and_l1_outside_enlargementUnion_le h f d).2

/-- Markov's inequality turns the bad-part `ℓ¹` estimate outside the exact
fivefold union into its strict level-set count. -/
theorem TmL2_badPart_ncard_level_outside_enlargementUnion_le
    {m : ℝ → ℂ} {D alpha threshold : ℝ} (h : SymbolData m D)
    (f : ℤ → ℂ) (d : DiscreteCZDecompositionData f alpha)
    (hthreshold : 0 < threshold) :
    (Set.ncard {x : {x : ℤ // x ∉ dyadicCZEnlargementUnion d.intervals} |
      threshold / 2 < ‖TmL2 h (finiteCZBadPartL2 f d) x.1‖} : ℝ) ≤
      4 * H₀ * D / threshold * discreteL1Norm f := by
  classical
  let outside := {x : ℤ // x ∉ dyadicCZEnlargementUnion d.intervals}
  let u : outside → ℝ := fun x => ‖TmL2 h (finiteCZBadPartL2 f d) x.1‖
  let Ege : Set outside := {x | threshold / 2 ≤ u x}
  let Estrict : Set outside := {x | threshold / 2 < u x}
  have huNonneg (x : outside) : 0 ≤ u x := by
    exact norm_nonneg _
  have hpackage :=
    TmL2_badPart_summable_and_l1_outside_enlargementUnion_le h f d
  have huSummable : Summable u := by
    simpa only [u] using hpackage.1
  have huNormSummable : Summable (fun x : outside => ‖u x‖) := huSummable.norm
  have huIntegrable : Integrable u (Measure.count : Measure outside) :=
    integrable_count_iff.mpr huNormSummable
  have hIntegral :
      (∫ x, u x ∂(Measure.count : Measure outside)) = ∑' x : outside, u x := by
    rw [integral_countable huIntegrable]
    simp
  have hsumBound : (∑' x : outside, u x) ≤
      2 * H₀ * D * discreteL1Norm f := by
    simpa only [u] using hpackage.2
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall huNonneg) huIntegrable (threshold / 2)
  have hnorm (x : outside) : ‖u x‖ = u x :=
    Real.norm_of_nonneg (huNonneg x)
  have hEgeMeasure : (Measure.count : Measure outside) Ege < ∞ := by
    have h := huIntegrable.measure_norm_ge_lt_top
      (ε := threshold / 2) (by positivity)
    simpa only [Ege, hnorm] using h
  have hEgeFinite : Ege.Finite := (Measure.count_apply_lt_top).mp hEgeMeasure
  have hEgeNcard : (Ege.ncard : ℝ) =
      (Measure.count : Measure outside).real Ege := by
    simp [Measure.real_def, Measure.count_apply_finite Ege hEgeFinite,
      Set.ncard_eq_toFinset_card Ege hEgeFinite]
  have hmarkBound : (threshold / 2) * (Ege.ncard : ℝ) ≤
      2 * H₀ * D * discreteL1Norm f := by
    calc
      _ = (threshold / 2) * (Measure.count : Measure outside).real Ege := by
        rw [hEgeNcard]
      _ ≤ ∫ x, u x ∂(Measure.count : Measure outside) := hmark
      _ = ∑' x : outside, u x := hIntegral
      _ ≤ 2 * H₀ * D * discreteL1Norm f := hsumBound
  have hEstrictSubset : Estrict ⊆ Ege := by
    intro x hx
    change threshold / 2 < u x at hx
    exact hx.le
  have hEstrictNcard : (Estrict.ncard : ℝ) ≤ Ege.ncard := by
    exact_mod_cast Set.ncard_le_ncard hEstrictSubset hEgeFinite
  have hcountMul : (Estrict.ncard : ℝ) * (threshold / 2) ≤
      2 * H₀ * D * discreteL1Norm f := by
    calc
      _ ≤ (Ege.ncard : ℝ) * (threshold / 2) :=
        mul_le_mul_of_nonneg_right hEstrictNcard (by positivity)
      _ = (threshold / 2) * (Ege.ncard : ℝ) := by ring
      _ ≤ 2 * H₀ * D * discreteL1Norm f := hmarkBound
  have hstrictBound : (Estrict.ncard : ℝ) ≤
      (2 * H₀ * D * discreteL1Norm f) / (threshold / 2) :=
    (le_div_iff₀ (by positivity)).2 hcountMul
  change (Estrict.ncard : ℝ) ≤ _
  calc
    _ ≤ (2 * H₀ * D * discreteL1Norm f) / (threshold / 2) := hstrictBound
    _ = 4 * H₀ * D / threshold * discreteL1Norm f := by
      field_simp [ne_of_gt hthreshold]
      ring

/-- For positive symbol constant, the CZ decomposition assembles the exact
good-part, bad-part, and fivefold-enlargement counts with constant `W`. -/
theorem kernelWeakType_fromCZ_count_le
    {m : ℝ → ℂ} {D threshold : ℝ} (h : SymbolData m D)
    (hD : 0 < D) (hthreshold : 0 < threshold)
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (d : DiscreteCZDecompositionData f (threshold / D)) :
    (Set.ncard {x : ℤ | threshold < ‖TmL2 h
      (finiteIntegerSequenceL2 hf.toFinset f) x‖} : ℝ) ≤
      W * D / threshold * discreteL1Norm f := by
  classical
  let input : lp (fun _ : ℤ => ℂ) 2 := finiteIntegerSequenceL2 hf.toFinset f
  let good : lp (fun _ : ℤ => ℂ) 2 :=
    finiteIntegerSequenceL2 d.good_finite_support.toFinset d.goodPart
  let bad : lp (fun _ : ℤ => ℂ) 2 := finiteCZBadPartL2 f d
  let U : Set ℤ := (dyadicCZEnlargementUnion d.intervals : Set ℤ)
  let G : Set ℤ := {x : ℤ | threshold / 2 < ‖TmL2 h good x‖}
  let outside := {x : ℤ // x ∉ dyadicCZEnlargementUnion d.intervals}
  let badOutsideLevel : Set outside :=
    {x : outside | threshold / 2 < ‖TmL2 h bad x.1‖}
  let B : Set ℤ := Subtype.val '' badOutsideLevel
  let L : Set ℤ := {x : ℤ | threshold < ‖TmL2 h input x‖}
  have hinputRep : (input : ℤ → ℂ) = f := by
    funext x
    dsimp [input]
    rw [finiteIntegerSequenceL2_apply]
    by_cases hx : x ∈ hf.toFinset
    · simp [hx]
    · have hfx : f x = 0 := by
        by_contra hne
        exact hx (hf.mem_toFinset.mpr (Function.mem_support.mpr hne))
      simp [hx, hfx]
  have hgoodRep : (good : ℤ → ℂ) = d.goodPart := by
    funext x
    dsimp [good]
    rw [finiteIntegerSequenceL2_apply]
    by_cases hx : x ∈ d.good_finite_support.toFinset
    · simp [hx]
    · have hgoodx : d.goodPart x = 0 := by
        by_contra hne
        exact hx (d.good_finite_support.mem_toFinset.mpr
          (Function.mem_support.mpr hne))
      simp [hx, hgoodx]
  have hbadRep : (bad : ℤ → ℂ) =
      (fun x : ℤ => ∑ i ∈ d.intervals, dyadicBadPiece f i x) := by
    funext x
    dsimp [bad, finiteCZBadPartL2]
    simp only [lp.coeFn_sum, Finset.sum_apply, finiteBadPieceL2_apply]
  have hdecomp : input = good + bad := by
    apply lp.ext
    funext x
    rw [hinputRep, lp.coeFn_add, hgoodRep, hbadRep]
    exact d.decomposition x
  have hTmDecomp : TmL2 h input = TmL2 h good + TmL2 h bad := by
    calc
      TmL2 h input = TmL2CLM h input := TmL2_eq_TmL2CLM h input
      _ = TmL2CLM h (good + bad) := by rw [hdecomp]
      _ = TmL2CLM h good + TmL2CLM h bad := map_add _ _ _
      _ = TmL2 h good + TmL2 h bad := by
        rw [← TmL2_eq_TmL2CLM h good, ← TmL2_eq_TmL2CLM h bad]
  have hlevels : L ⊆ U ∪ (G ∪ B) := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · by_cases hxG : x ∈ G
      · exact Or.inr (Or.inl hxG)
      · have hgoodle : ‖TmL2 h good x‖ ≤ threshold / 2 := by
          apply le_of_not_gt
          intro hgt
          exact hxG hgt
        apply Or.inr (Or.inr ?_)
        by_contra hnotB
        have hbadle : ‖TmL2 h bad x‖ ≤ threshold / 2 := by
          apply le_of_not_gt
          intro hgt
          apply hnotB
          exact ⟨⟨x, hxU⟩, hgt, rfl⟩
        have hpoint : TmL2 h input x =
            TmL2 h good x + TmL2 h bad x := by
          exact congrArg (fun v : lp (fun _ : ℤ => ℂ) 2 => v x) hTmDecomp
        have hbound : ‖TmL2 h input x‖ ≤ threshold := by
          rw [hpoint]
          calc
            ‖TmL2 h good x + TmL2 h bad x‖ ≤
                ‖TmL2 h good x‖ + ‖TmL2 h bad x‖ := norm_add_le _ _
            _ ≤ threshold / 2 + threshold / 2 := add_le_add hgoodle hbadle
            _ = threshold := by ring
        exact (not_lt_of_ge hbound) hx
  have hUfinite : U.Finite := by
    simpa only [U] using (dyadicCZEnlargementUnion d.intervals).finite_toSet
  have hGfinite : G.Finite := by
    simpa only [G, good] using
      lp_strict_level_set_finite (TmL2 h good) (threshold / 2) (by positivity)
  have hBadAllFinite : {x : ℤ | threshold / 2 < ‖TmL2 h bad x‖}.Finite :=
    lp_strict_level_set_finite (TmL2 h bad) (threshold / 2) (by positivity)
  have hBsubset : B ⊆ {x : ℤ | threshold / 2 < ‖TmL2 h bad x‖} := by
    rintro x ⟨y, hy, rfl⟩
    exact hy
  have hBfinite : B.Finite := hBadAllFinite.subset hBsubset
  have hUnionFinite : (U ∪ (G ∪ B)).Finite := hUfinite.union (hGfinite.union hBfinite)
  have hcountNat : L.ncard ≤ U.ncard + G.ncard + B.ncard := by
    calc
      L.ncard ≤ (U ∪ (G ∪ B)).ncard := Set.ncard_le_ncard hlevels hUnionFinite
      _ ≤ U.ncard + (G ∪ B).ncard := Set.ncard_union_le U (G ∪ B)
      _ ≤ U.ncard + G.ncard + B.ncard := by
        have hGB := Set.ncard_union_le G B
        omega
  have hUcount : (U.ncard : ℝ) ≤
      5 * D / threshold * discreteL1Norm f := by
    simpa [U, Set.ncard_coe_finset] using
      dyadicCZEnlargementUnion_card_le hD hthreshold d
  have hGcount : (G.ncard : ℝ) ≤
      8 * D / threshold * discreteL1Norm f := by
    simpa [G, good] using
      kernelWeakType_goodPart_count_le h hD hthreshold f d
  have hBcount : (B.ncard : ℝ) ≤
      4 * H₀ * D / threshold * discreteL1Norm f := by
    have h := TmL2_badPart_ncard_level_outside_enlargementUnion_le
      h f d hthreshold
    have hBcard : B.ncard = badOutsideLevel.ncard := by
      dsimp only [B]
      exact Set.ncard_image_of_injective badOutsideLevel Subtype.val_injective
    rw [hBcard]
    simpa only [badOutsideLevel, outside] using h
  calc
    (L.ncard : ℝ) ≤ U.ncard + G.ncard + B.ncard := by exact_mod_cast hcountNat
    _ ≤ 5 * D / threshold * discreteL1Norm f +
        8 * D / threshold * discreteL1Norm f +
        4 * H₀ * D / threshold * discreteL1Norm f :=
      add_le_add (add_le_add hUcount hGcount) hBcount
    _ = W * D / threshold * discreteL1Norm f := by
      rw [W_eq]
      ring

/-- The exact weak `(1,1)` estimate, including the zero-symbol-constant case. -/
theorem kernelWeakType {m : ℝ → ℂ} {D threshold : ℝ}
    (h : SymbolData m D) (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (hthreshold : 0 < threshold) :
    (Set.ncard {x : ℤ | threshold < ‖TmL2 h
      (finiteIntegerSequenceL2 hf.toFinset f) x‖} : ℝ) ≤
      W * D / threshold * discreteL1Norm f := by
  classical
  by_cases hDzero : D = 0
  · have hsymbolBound : ‖torusSymbolLp h‖ ≤ 0 := by
      simpa [hDzero] using norm_torusSymbolLp_le_D h
    have hsymbolNorm : ‖torusSymbolLp h‖ = 0 :=
      le_antisymm hsymbolBound (norm_nonneg _)
    have houtputNormLe :
        ‖TmL2 h (finiteIntegerSequenceL2 hf.toFinset f)‖ ≤ 0 := by
      calc
        ‖TmL2 h (finiteIntegerSequenceL2 hf.toFinset f)‖ ≤
            ‖torusSymbolLp h‖ *
              ‖finiteIntegerSequenceL2 hf.toFinset f‖ :=
          norm_TmL2_le h _
        _ = 0 := by rw [hsymbolNorm]; simp
    have houtputNorm :
        ‖TmL2 h (finiteIntegerSequenceL2 hf.toFinset f)‖ = 0 :=
      le_antisymm houtputNormLe (norm_nonneg _)
    have houtputZero :
        TmL2 h (finiteIntegerSequenceL2 hf.toFinset f) = 0 :=
      norm_eq_zero.mp houtputNorm
    have hpoint (x : ℤ) :
        TmL2 h (finiteIntegerSequenceL2 hf.toFinset f) x = 0 :=
      congrArg (fun u : lp (fun _ : ℤ => ℂ) 2 => u x) houtputZero
    have hlevel :
        {x : ℤ | threshold < ‖TmL2 h
          (finiteIntegerSequenceL2 hf.toFinset f) x‖} = ∅ := by
      ext x
      change (threshold < ‖TmL2 h
        (finiteIntegerSequenceL2 hf.toFinset f) x‖) ↔ False
      rw [hpoint x, norm_zero]
      constructor
      · exact not_lt_of_ge hthreshold.le
      · intro hx
        exact False.elim hx
    rw [hlevel, hDzero]
    simp
  · have hDpos : 0 < D := lt_of_le_of_ne h.D_nonneg (Ne.symm hDzero)
    obtain ⟨d⟩ := discreteCZDecomposition f hf (threshold / D) (by positivity)
    exact kernelWeakType_fromCZ_count_le h hDpos hthreshold f hf d

end

end FractionalPrimes.Literature.Multiplier
