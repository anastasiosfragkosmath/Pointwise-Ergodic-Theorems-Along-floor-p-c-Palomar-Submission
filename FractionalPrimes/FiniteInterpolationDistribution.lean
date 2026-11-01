module

public import FractionalPrimes.FiniteInterpolationSplit
public import FractionalPrimes.FiniteInterpolationMoments
public import FractionalPrimes.FiniteSupportLpConstruction
public import FractionalPrimes.FiniteConvolutionLinearity

@[expose] public section

/-!
# The all-output distribution estimate for elementary interpolation

This module follows the approved `lem:interpolation` proof: split a finite
input at `a * lambda`, estimate the low output in `L²` and the high output
in `L¹`, then use the strict-level union bound.  The early interpolation
source index reports no dedicated Astra derivation; the exact constants and
cutoff conventions below come from `expanded-blueprint.tex`, lines 593–625.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem finite_enorm_sum_eq_ofReal_norm_sum
    (s : Finset ℤ) (f : ℤ → ℂ) :
    (∑ k ∈ s, ‖f k‖ₑ) = ENNReal.ofReal (∑ k ∈ s, ‖f k‖) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => norm_nonneg (f k))]
  simp only [ofReal_norm]

private theorem finite_enorm_sq_sum_eq_ofReal_norm_sq_sum
    (s : Finset ℤ) (f : ℤ → ℂ) :
    (∑ k ∈ s, ‖f k‖ₑ ^ 2) =
      ENNReal.ofReal (∑ k ∈ s, ‖f k‖ ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => sq_nonneg (‖f k‖))]
  simp only [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]

private theorem finiteSupportCountLpTwo_eLpNorm_real
    (s : Finset ℤ) (f : ℤ → ℂ) :
    eLpNorm (finiteSupportCountLpTwo s f : ℤ → ℂ) 2 Measure.count =
      ENNReal.ofReal ((∑ k ∈ s, ‖f k‖ ^ 2) ^ (1 / 2 : ℝ)) := by
  rw [finiteSupportCountLpTwo_eLpNorm, finite_enorm_sq_sum_eq_ofReal_norm_sq_sum]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun k hk => sq_nonneg (‖f k‖)) (by norm_num : 0 ≤ (1 / 2 : ℝ))]

private theorem finite_l2_weak_rhs_eq_ofReal
    (s : Finset ℤ) (f : ℤ → ℂ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (ENNReal.ofReal epsilon *
      (∑ k ∈ s, ‖f k‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 =
      ENNReal.ofReal (epsilon ^ 2 * ∑ k ∈ s, ‖f k‖ ^ 2) := by
  have hsum : 0 ≤ ∑ k ∈ s, ‖f k‖ ^ 2 :=
    Finset.sum_nonneg fun k hk => sq_nonneg (‖f k‖)
  rw [finite_enorm_sq_sum_eq_ofReal_norm_sq_sum,
    ENNReal.ofReal_rpow_of_nonneg hsum (by norm_num : 0 ≤ (1 / 2 : ℝ)),
    ← ENNReal.ofReal_mul hepsilon,
    ← ENNReal.ofReal_pow (mul_nonneg hepsilon (Real.rpow_nonneg hsum _)) 2]
  congr 1
  rw [mul_pow]
  have hrpow :
      ((∑ k ∈ s, ‖f k‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) =
        ∑ k ∈ s, ‖f k‖ ^ 2 := by
    calc
      ((∑ k ∈ s, ‖f k‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) =
          ((∑ k ∈ s, ‖f k‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = (∑ k ∈ s, ‖f k‖ ^ 2) ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by
        rw [← Real.rpow_mul hsum]
      _ = ∑ k ∈ s, ‖f k‖ ^ 2 := by norm_num
  rw [hrpow]

private theorem finite_count_card_le_ofReal_mul
    {s : Set ℤ} (hs : s.Finite) {threshold bound : ℝ}
    (hthreshold : 0 < threshold) (hbound : 0 ≤ bound)
    (hweak : ENNReal.ofReal threshold * Measure.count s ≤ ENNReal.ofReal bound) :
    (hs.toFinset.card : ℝ) ≤ bound / threshold := by
  have hcount : Measure.count s = (hs.toFinset.card : ℝ≥0∞) := by
    rw [Measure.count_apply_finite s hs]
  rw [hcount] at hweak
  have hrealENN :
      ENNReal.ofReal (threshold * (hs.toFinset.card : ℝ)) ≤ ENNReal.ofReal bound := by
    calc
      ENNReal.ofReal (threshold * (hs.toFinset.card : ℝ)) =
          ENNReal.ofReal threshold * (hs.toFinset.card : ℝ≥0∞) := by
            rw [ENNReal.ofReal_mul hthreshold.le]
            norm_cast
      _ ≤ ENNReal.ofReal bound := hweak
  have hreal := (ENNReal.ofReal_le_ofReal_iff hbound).mp hrealENN
  exact (le_div_iff₀ hthreshold).2 (by nlinarith [hreal])

private theorem finite_count_card_le_ofReal_sq_mul
    {s : Set ℤ} (hs : s.Finite) {threshold bound : ℝ}
    (hthreshold : 0 < threshold) (hbound : 0 ≤ bound)
    (hweak : ENNReal.ofReal threshold ^ 2 * Measure.count s ≤ ENNReal.ofReal bound) :
    (hs.toFinset.card : ℝ) ≤ bound / threshold ^ 2 := by
  have hcount : Measure.count s = (hs.toFinset.card : ℝ≥0∞) := by
    rw [Measure.count_apply_finite s hs]
  rw [hcount] at hweak
  have hrealENN :
      ENNReal.ofReal (threshold ^ 2 * (hs.toFinset.card : ℝ)) ≤ ENNReal.ofReal bound := by
    calc
      ENNReal.ofReal (threshold ^ 2 * (hs.toFinset.card : ℝ)) =
          ENNReal.ofReal threshold ^ 2 * (hs.toFinset.card : ℝ≥0∞) := by
            rw [ENNReal.ofReal_mul (sq_nonneg threshold),
              ENNReal.ofReal_pow hthreshold.le 2]
            norm_cast
      _ ≤ ENNReal.ofReal bound := hweak
  have hreal := (ENNReal.ofReal_le_ofReal_iff hbound).mp hrealENN
  apply (le_div_iff₀ (sq_pos_of_pos hthreshold)).2
  nlinarith [hreal]

private theorem count_set_finite_of_ofReal_weight
    {s : Set ℤ} {weight : ℝ≥0∞} {bound : ℝ}
    (hweight : weight ≠ 0)
    (hweak : weight * Measure.count s ≤ ENNReal.ofReal bound) : s.Finite := by
  have hprod : weight * Measure.count s < ∞ := hweak.trans_lt (by simp)
  have hcount : Measure.count s < ∞ :=
    ENNReal.lt_top_of_mul_ne_top_right hprod.ne hweight
  exact (Measure.count_apply_lt_top).mp hcount

/-- Exact all-of-`ℤ` strict-superlevel distribution bound for the approved
finite low/high split.  The low part uses `‖f k‖ ≤ a * lambda`; the high
part uses the strict complement `a * lambda < ‖f k‖`. -/
theorem finiteIntegerKernelConvolution_low_high_distribution
    (K : IntegerL1Kernel) (s : Finset ℤ) (f : ℤ → ℂ)
    {B epsilon a lambda : ℝ}
    (hB : ∑' m : ℤ, ‖K.coeff m‖ ≤ B)
    (hBpos : 0 < B) (hepsilon : 0 < epsilon)
    (hlambda : 0 < lambda)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count) :
    ∃ hE : {k : ℤ |
        lambda < ‖integerKernelConvolution K
          (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖}.Finite,
      (hE.toFinset.card : ℝ) ≤
        4 * epsilon ^ 2 / lambda ^ 2 *
            (∑ k ∈ s, ‖finiteLowPart s (a * lambda) f k‖ ^ 2) +
        2 * B / lambda *
            (∑ k ∈ s, ‖finiteHighPart s (a * lambda) f k‖) := by
  classical
  let cutoff : ℝ := a * lambda
  let lo : ℤ → ℂ := finiteLowPart s cutoff f
  let hi : ℤ → ℂ := finiteHighPart s cutoff f
  let half : ℝ := lambda / 2
  let outFull : ℤ → ℂ := integerKernelConvolution K
    (finiteSupportCountLpTwo s f : ℤ → ℂ)
  let outLo : ℤ → ℂ := integerKernelConvolution K
    (finiteSupportCountLpTwo s lo : ℤ → ℂ)
  let outHi : ℤ → ℂ := integerKernelConvolution K
    (finiteSupportCountLpOne s hi : ℤ → ℂ)
  let E : Set ℤ := {k | lambda < ‖outFull k‖}
  let Elo : Set ℤ := {k | ENNReal.ofReal half < ‖outLo k‖ₑ}
  let Ehi : Set ℤ := {k | ENNReal.ofReal half < ‖outHi k‖ₑ}

  have hhalf : 0 < half := by dsimp [half]; linarith
  have hmassENN :
      (∑' m : ℤ, ‖K.coeff m‖ₑ) =
        ENNReal.ofReal (∑' m : ℤ, ‖K.coeff m‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg (K.coeff m))
      K.summable_norm]
    simp [enorm_eq_nnnorm]
  have hmassBound :
      (∑' m : ℤ, ‖K.coeff m‖ₑ) ≤ ENNReal.ofReal B := by
    rw [hmassENN]
    exact (ENNReal.ofReal_le_ofReal_iff hBpos.le).2 hB

  have hloOp : eLpNorm (integerKernelConvolution K
      (finiteSupportCountLpTwo s lo : ℤ → ℂ)) 2 Measure.count ≤
      ENNReal.ofReal epsilon *
        eLpNorm (finiteSupportCountLpTwo s lo : ℤ → ℂ) 2 Measure.count :=
    hL2 (finiteSupportCountLpTwo s lo)
  have hloWeak := finiteSupportCountLpTwo_convolution_weak
    K s lo (ENNReal.ofReal epsilon) hloOp hhalf.le
  have hloWeakReal :
      ENNReal.ofReal half ^ 2 * Measure.count Elo ≤
        ENNReal.ofReal (epsilon ^ 2 * ∑ k ∈ s, ‖lo k‖ ^ 2) := by
    dsimp [Elo, outLo]
    simpa only [finite_l2_weak_rhs_eq_ofReal s lo hepsilon.le] using hloWeak

  have hhiWeak := finiteSupportCountLpOne_convolution_weak K s hi hhalf.le
  have hhiInput :
      (∑ k ∈ s, ‖hi k‖ₑ) = ENNReal.ofReal (∑ k ∈ s, ‖hi k‖) :=
    finite_enorm_sum_eq_ofReal_norm_sum s hi
  have hhiWeakReal :
      ENNReal.ofReal half * Measure.count Ehi ≤
        ENNReal.ofReal (B * ∑ k ∈ s, ‖hi k‖) := by
    dsimp [Ehi, outHi]
    calc
      ENNReal.ofReal half * Measure.count
          {k : ℤ | ENNReal.ofReal half <
            ‖integerKernelConvolution K
              (finiteSupportCountLpOne s hi : ℤ → ℂ) k‖ₑ} ≤
          (∑' m : ℤ, ‖K.coeff m‖ₑ) *
            (∑ k ∈ s, ‖hi k‖ₑ) := hhiWeak
      _ = (∑' m : ℤ, ‖K.coeff m‖ₑ) *
            ENNReal.ofReal (∑ k ∈ s, ‖hi k‖) := by rw [hhiInput]
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (∑ k ∈ s, ‖hi k‖) :=
        mul_le_mul_of_nonneg_right hmassBound (by positivity)
      _ = ENNReal.ofReal (B * ∑ k ∈ s, ‖hi k‖) :=
        (ENNReal.ofReal_mul hBpos.le).symm

  have hEloFinite : Elo.Finite := by
    have hfinite := count_set_finite_of_ofReal_weight
      (by exact pow_ne_zero 2 (ENNReal.ofReal_ne_zero_iff.mpr hhalf))
      (by simpa [Elo] using hloWeakReal)
    exact hfinite
  have hEhiFinite : Ehi.Finite := by
    have hfinite := count_set_finite_of_ofReal_weight
      (ENNReal.ofReal_ne_zero_iff.mpr hhalf)
      (by simpa [Ehi] using hhiWeakReal)
    exact hfinite

  have hfullRep : (finiteSupportCountLpTwo s f : ℤ → ℂ) =
      (finiteIntegerSequenceL2 s f : ℤ → ℂ) := by
    funext k
    rw [finiteSupportCountLpTwo_apply, finiteIntegerSequenceL2_apply]
  have hloRep : (finiteSupportCountLpTwo s lo : ℤ → ℂ) =
      (finiteIntegerSequenceL2 s lo : ℤ → ℂ) := by
    funext k
    rw [finiteSupportCountLpTwo_apply, finiteIntegerSequenceL2_apply]
  have hhiRep : (finiteSupportCountLpOne s hi : ℤ → ℂ) =
      (finiteIntegerSequenceL2 s hi : ℤ → ℂ) := by
    funext k
    rw [finiteSupportCountLpOne_apply, finiteIntegerSequenceL2_apply]
  have hsplit : (finiteIntegerSequenceL2 s f : ℤ → ℂ) =
      (finiteIntegerSequenceL2 s (fun k => lo k + hi k) : ℤ → ℂ) := by
    funext k
    rw [finiteIntegerSequenceL2_apply, finiteIntegerSequenceL2_apply]
    by_cases hk : k ∈ s
    · have hsplitk := finiteIntegerSequenceL2_eq_finiteLowPart_add_finiteHighPart
        s cutoff f k
      simpa [finiteIntegerSequenceL2_apply, hk] using hsplitk
    · simp [hk]
  have hadd (k : ℤ) : outFull k = outLo k + outHi k := by
    dsimp [outFull, outLo, outHi]
    rw [hfullRep, hsplit, integerKernelConvolution_finiteIntegerSequenceL2_add]
    rw [← hloRep, ← hhiRep]

  have hsubset : E ⊆ Elo ∪ Ehi := by
    intro k hk
    by_contra hnot
    have hklo : ¬ ENNReal.ofReal half < ‖outLo k‖ₑ := by
      intro hh
      exact hnot (Or.inl hh)
    have hkhi : ¬ ENNReal.ofReal half < ‖outHi k‖ₑ := by
      intro hh
      exact hnot (Or.inr hh)
    have hlo : ‖outLo k‖ ≤ half := by
      have h := le_of_not_gt hklo
      have h' : ENNReal.ofReal ‖outLo k‖ ≤ ENNReal.ofReal half := by
        simpa using h
      exact (ENNReal.ofReal_le_ofReal_iff hhalf.le).mp h'
    have hhi : ‖outHi k‖ ≤ half := by
      have h := le_of_not_gt hkhi
      have h' : ENNReal.ofReal ‖outHi k‖ ≤ ENNReal.ofReal half := by
        simpa using h
      exact (ENNReal.ofReal_le_ofReal_iff hhalf.le).mp h'
    have htriangle : ‖outFull k‖ ≤ lambda := by
      calc
        ‖outFull k‖ = ‖outLo k + outHi k‖ := by rw [hadd k]
        _ ≤ ‖outLo k‖ + ‖outHi k‖ := norm_add_le _ _
        _ ≤ half + half := add_le_add hlo hhi
        _ = lambda := by dsimp [half]; ring
    exact (not_lt_of_ge htriangle) hk

  have hEfinite : E.Finite := (hEloFinite.union hEhiFinite).subset hsubset
  have hcardNat : hEfinite.toFinset.card ≤
      hEloFinite.toFinset.card + hEhiFinite.toFinset.card := by
    calc
      hEfinite.toFinset.card ≤
          (hEloFinite.toFinset ∪ hEhiFinite.toFinset).card :=
        Finset.card_le_card (by
          intro k hk
          have hkE : k ∈ E := by simpa using hk
          have hkUnion := hsubset hkE
          simpa using hkUnion)
      _ ≤ hEloFinite.toFinset.card + hEhiFinite.toFinset.card :=
        Finset.card_union_le _ _

  have hLoBound : 0 ≤ epsilon ^ 2 * ∑ k ∈ s, ‖lo k‖ ^ 2 :=
    mul_nonneg (sq_nonneg epsilon)
      (Finset.sum_nonneg fun k hk => sq_nonneg (‖lo k‖))
  have hHiBound : 0 ≤ B * ∑ k ∈ s, ‖hi k‖ :=
    mul_nonneg hBpos.le (Finset.sum_nonneg fun k hk => norm_nonneg (hi k))

  have hloCard : (hEloFinite.toFinset.card : ℝ) ≤
      4 * epsilon ^ 2 / lambda ^ 2 * (∑ k ∈ s, ‖lo k‖ ^ 2) := by
    calc
      (hEloFinite.toFinset.card : ℝ) ≤
          (epsilon ^ 2 * ∑ k ∈ s, ‖lo k‖ ^ 2) / half ^ 2 :=
        finite_count_card_le_ofReal_sq_mul hEloFinite hhalf hLoBound hloWeakReal
      _ = 4 * epsilon ^ 2 / lambda ^ 2 *
          (∑ k ∈ s, ‖lo k‖ ^ 2) := by
        dsimp [half]
        field_simp [ne_of_gt hlambda] <;> norm_num

  have hhiCard : (hEhiFinite.toFinset.card : ℝ) ≤
      2 * B / lambda * (∑ k ∈ s, ‖hi k‖) := by
    calc
      (hEhiFinite.toFinset.card : ℝ) ≤
          (B * ∑ k ∈ s, ‖hi k‖) / half :=
        finite_count_card_le_ofReal_mul hEhiFinite hhalf hHiBound hhiWeakReal
      _ = 2 * B / lambda * (∑ k ∈ s, ‖hi k‖) := by
        dsimp [half]
        field_simp [ne_of_gt hlambda]

  refine ⟨hEfinite, ?_⟩
  have hcardReal : (hEfinite.toFinset.card : ℝ) ≤
      (hEloFinite.toFinset.card : ℝ) + (hEhiFinite.toFinset.card : ℝ) := by
    exact_mod_cast hcardNat

  calc
    (hEfinite.toFinset.card : ℝ) ≤
        (hEloFinite.toFinset.card : ℝ) + (hEhiFinite.toFinset.card : ℝ) := hcardReal
    _ ≤ 4 * epsilon ^ 2 / lambda ^ 2 * (∑ k ∈ s, ‖lo k‖ ^ 2) +
          2 * B / lambda * (∑ k ∈ s, ‖hi k‖) := add_le_add hloCard hhiCard
    _ = 4 * epsilon ^ 2 / lambda ^ 2 *
          (∑ k ∈ s, ‖finiteLowPart s (a * lambda) f k‖ ^ 2) +
        2 * B / lambda *
          (∑ k ∈ s, ‖finiteHighPart s (a * lambda) f k‖) := by
      simp [lo, hi, cutoff]

end

end FractionalPrimes
