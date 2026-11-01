module
public import FractionalPrimes.Literature.Reciprocal.GlobalCharacterMobius
public import FractionalPrimes.Literature.Twisted.OriginalLongFactorOfMobiusGoal
public import FractionalPrimes.Literature.Twisted.ShiftedConvolutionSmallFactor
public import FractionalPrimes.Literature.Twisted.DivisorSubpowerExplicit
public import FractionalPrimes.Literature.Twisted.GroupedFactorScaleBounds
public import FractionalPrimes.Literature.Twisted.CharacterEvalNorm
public import FractionalPrimes.Literature.Twisted.SelectedComponentMass
public import FractionalPrimes.Literature.Uniformity.ArithmeticGroupedFactorBounds
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition
@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Finset
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

namespace FractionalPrimes.Literature.Twisted

private theorem groupedDyadicInterval_real_bounds {j n : ℕ}
    (h : inDyadicInterval j n) :
    dyadicScale j < (n : ℝ) ∧ (n : ℝ) ≤ 2 * dyadicScale j := by
  by_cases hj : j = 0
  · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h.1
    have hnle : n ≤ 1 := by
      simpa [inDyadicInterval, dyadicUpperNat, hj] using h.2
    have hn : n = 1 := by omega
    simp [dyadicScale, hj, hn]
    norm_num
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hscale : dyadicScale j = (dyadicLowerNat j : ℝ) := by
      simp [dyadicScale, dyadicLowerNat, hj]
    have hjEq : j.pred + 1 = j := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hjpos
    have hpow : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ j.pred := by
      calc
        (2 : ℝ) ^ j = (2 : ℝ) ^ (j.pred + 1) :=
          congrArg (fun k : ℕ => (2 : ℝ) ^ k) hjEq.symm
        _ = (2 : ℝ) ^ j.pred * 2 := by rw [pow_succ]
        _ = 2 * (2 : ℝ) ^ j.pred := by ring
    have hupper : (dyadicUpperNat j : ℝ) = 2 * dyadicScale j := by
      simp only [dyadicUpperNat, Nat.cast_pow, Nat.cast_ofNat]
      rw [hpow, dyadicScale, if_neg hj]
    constructor
    · rw [hscale]
      exact_mod_cast h.1
    · rw [← hupper]
      exact_mod_cast h.2

private theorem groupedDyadicInterval_of_real_bounds {j n : ℕ}
    (hn : 0 < n) (h : dyadicScale j < (n : ℝ) ∧
      (n : ℝ) ≤ 2 * dyadicScale j) :
    inDyadicInterval j n := by
  by_cases hj : j = 0
  · have hnle : n ≤ 1 := by
      simpa [dyadicScale, hj] using h.2
    simpa [inDyadicInterval, dyadicLowerNat, dyadicUpperNat, hj] using
      ⟨hn, hnle⟩
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hscale : dyadicScale j = (dyadicLowerNat j : ℝ) := by
      simp [dyadicScale, dyadicLowerNat, hj]
    have hjEq : j.pred + 1 = j := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hjpos
    have hpow : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ j.pred := by
      calc
        (2 : ℝ) ^ j = (2 : ℝ) ^ (j.pred + 1) :=
          congrArg (fun k : ℕ => (2 : ℝ) ^ k) hjEq.symm
        _ = (2 : ℝ) ^ j.pred * 2 := by rw [pow_succ]
        _ = 2 * (2 : ℝ) ^ j.pred := by ring
    have hupper : (dyadicUpperNat j : ℝ) = 2 * dyadicScale j := by
      simp only [dyadicUpperNat, Nat.cast_pow, Nat.cast_ofNat]
      rw [hpow, dyadicScale, if_neg hj]
    have hloR : (dyadicLowerNat j : ℝ) < (n : ℝ) := by
      rw [← hscale]
      exact h.1
    have hlo : dyadicLowerNat j < n := by exact_mod_cast hloR
    have hhiR : (n : ℝ) ≤ (dyadicUpperNat j : ℝ) := by
      rw [hupper]
      exact h.2
    have hhi : n ≤ dyadicUpperNat j := by exact_mod_cast hhiR
    simpa [inDyadicInterval] using ⟨hlo, hhi⟩

private theorem groupedDyadicFactor_support_bounds {X z : ℝ}
    (f : DyadicArithmeticFactor X) {n : ℕ}
    (hne : dyadicFactorFunction z f n ≠ 0) :
    dyadicFactorScale f < (n : ℝ) ∧
      (n : ℝ) ≤ 2 * dyadicFactorScale f := by
  cases f with
  | one j =>
      have hI : inDyadicInterval j.val.val n := by
        by_contra hI
        apply hne
        simp [dyadicFactorFunction, dyadicOneFactor_apply, hI]
      exact groupedDyadicInterval_real_bounds hI
  | logarithm j =>
      have hI : inDyadicInterval j.val.val n := by
        by_contra hI
        apply hne
        simp [dyadicFactorFunction, dyadicLogFactor_apply, hI]
      exact groupedDyadicInterval_real_bounds hI
  | mobius j =>
      have hI : inDyadicInterval j.val.val n := by
        by_contra hI
        apply hne
        simp [dyadicFactorFunction, dyadicMobiusFactor_apply, hI]
      exact groupedDyadicInterval_real_bounds hI

private theorem groupedDyadicFactor_coefficient_norm_le {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) (f : DyadicArithmeticFactor X) (n : ℕ) :
    ‖dyadicFactorComplexFunction z f n‖ ≤ Real.log (8 * X) := by
  have hmass := dyadicFactorFunction_abs_le_massWeight hX z f n
  have hmassle : dyadicFactorMassWeight f ≤ Real.log (8 * X) := by
    cases f with
    | one j =>
        simp [dyadicFactorMassWeight]
        linarith [log_eightX_gt_one hX]
    | mobius j =>
        simp [dyadicFactorMassWeight]
        linarith [log_eightX_gt_one hX]
    | logarithm j => simp [dyadicFactorMassWeight]
  simpa [dyadicFactorComplexFunction, Complex.norm_real,
    Real.norm_eq_abs] using hmass.trans hmassle

noncomputable def groupedFactorAllocationTerm {X : ℝ}
    (z : ℝ) (f : DyadicArithmeticFactor X) (r p : ℕ)
    (χ : ℕ → ℂ) (s : ℝ) (m : ℕ) : ℂ :=
  dyadicFactorComplexFunction z f (r * m) *
    (if Nat.Coprime m p then factorExtractionMellinWeight χ s m else 0)

/-- The original-factor bound supplies the short-interval hypothesis for
each labeled dyadic factor, with its own dyadic cutoff retained. -/
theorem groupedDyadicFactorOriginalLocalEstimate
    {X a z s : ℝ} (hX3 : 3 ≤ X) (hz : 0 ≤ z)
    (f : DyadicArithmeticFactor X)
    (hOrig : OriginalLongFactorAt X (dyadicFactorScale f) s a)
    {r p Q : ℕ} (χ : BlueprintCharacter Q)
    (hr : 1 ≤ r) (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (hp : 1 ≤ p) (hplog : (p : ℝ) ≤ (Real.log X) ^ a)
    (hQ : 1 ≤ Q) (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a)
    (hfreqlo : (Real.log X) ^ (45 * a) ≤ |s|)
    (hfreqhi : |s| ≤ X ^ (a + 1))
    {u v : ℝ} (hu : 0 ≤ u)
    (hsub : Set.Ioc u v ⊆ Set.Ioc
      (dyadicFactorScale f / (r : ℝ))
      (2 * (dyadicFactorScale f / (r : ℝ)))) :
    ‖∑ m ∈ factorExtractionRealInterval u v,
      groupedFactorAllocationTerm z f r p
        (fun m => evalInt χ (m : ℤ)) s m‖ ≤
      (Real.log X) ^ (-21 * a) *
        Real.sqrt (dyadicFactorScale f / (r : ℝ)) := by
  classical
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide) hr)
  have hscalePos : 0 < dyadicFactorScale f :=
    lt_of_lt_of_le (by norm_num) (dyadicFactorScale_ge_half f)
  have hlogPos : 0 < Real.log X := Real.log_pos (by linarith [hX3])
  by_cases huv : v ≤ u
  · have hfloor : Nat.floor v ≤ Nat.floor u := Nat.floor_mono huv
    simp [factorExtractionRealInterval, Finset.Ioc_eq_empty_of_le hfloor,
      groupedFactorAllocationTerm]
    positivity
  · have huv' : u < v := lt_of_not_ge huv
    have hendpoints := (Set.Ioc_subset_Ioc_iff huv').1 hsub
    have hleft : dyadicFactorScale f / (r : ℝ) ≤ u := hendpoints.2
    have hright : v ≤ 2 * (dyadicFactorScale f / (r : ℝ)) := hendpoints.1
    have hu' : 0 ≤ dyadicFactorScale f / (r : ℝ) :=
      (div_pos hscalePos hrR).le
    have huPos : 0 < u := lt_of_lt_of_le (div_pos hscalePos hrR) hleft
    have hv : 0 ≤ v := le_trans hu' (le_trans hleft huv'.le)
    have hO := hOrig r p Q χ hr hrlog hp hplog hQ hQlog hfreqlo hfreqhi
    have hscaleLower : dyadicFactorScale f ≤ (r : ℝ) * u := by
      simpa [mul_comm] using (div_le_iff₀ hrR).1 hleft
    have hscaleUpper : (r : ℝ) * v ≤ 2 * dyadicFactorScale f := by
      calc
        (r : ℝ) * v ≤ (r : ℝ) * (2 * (dyadicFactorScale f / (r : ℝ))) :=
          mul_le_mul_of_nonneg_left hright hrR.le
        _ = 2 * dyadicFactorScale f := by field_simp
    let χnat : ℕ → ℂ := fun m => evalInt χ (m : ℤ)
    have hχnorm : ∀ m, 0 < m → ‖χnat m‖ ≤ 1 := by
      intro m hm
      exact evalInt_norm_le_one χ (m : ℤ)
    have hχone : χnat 1 = 1 := by
      simp [χnat, evalInt]
    have hχmul : ∀ m n, χnat (m * n) = χnat m * χnat n := by
      intro m n
      simp [χnat, evalInt, Int.cast_mul]
    have hweight (m : ℕ) (hm : 0 < m) :
        factorExtractionMellinWeight χnat s m =
          χnat m * (m : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ)) := by
      simp [factorExtractionMellinWeight, χnat, hm]
    rcases f with j | j | j
    · let zlarge : ℝ := (r : ℝ) * v
      have hzlarge : zlarge / (r : ℝ) = v := by
        dsimp [zlarge]
        field_simp
      have hOlocal := hO .one u v zlarge hleft huv'.le
        (by simpa [zlarge, hzlarge] using hright)
      have hsum :
          (∑ m ∈ factorExtractionRealInterval u v,
            groupedFactorAllocationTerm z (.one j) r p χnat s m) =
          ∑ m ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
            originalLongFactorCoefficient .one r p χ s m := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmreal := (mem_factorExtractionRealInterval hu hv m).mp hm
        have hlow : dyadicFactorScale (.one j) <
            (r * m : ℕ) := by
          have hmul : dyadicFactorScale (.one j) < (r : ℝ) * m :=
            lt_of_le_of_lt hscaleLower
              (mul_lt_mul_of_pos_left hmreal.1 hrR)
          simpa only [Nat.cast_mul] using hmul
        have hupp : (r * m : ℕ) ≤ 2 * dyadicFactorScale (.one j) := by
          have hmul : (r : ℝ) * m ≤ 2 * dyadicFactorScale (.one j) :=
            le_trans (mul_le_mul_of_nonneg_left hmreal.2 hrR.le) hscaleUpper
          exact_mod_cast hmul
        have hmpos : 0 < m := by
          have hmR : 0 < (m : ℝ) := lt_trans huPos hmreal.1
          exact_mod_cast hmR
        have hnpos : 0 < r * m := Nat.mul_pos (lt_of_lt_of_le (by decide) hr) hmpos
        have hI : inDyadicInterval j.val.val (r * m) := by
          simpa [dyadicFactorScale] using
            groupedDyadicInterval_of_real_bounds hnpos ⟨hlow, hupp⟩
        simp [groupedFactorAllocationTerm, dyadicFactorComplexFunction,
          dyadicFactorFunction, dyadicOneFactor_apply, hI,
          factorExtractionMellinWeight, χnat, hmpos,
          originalLongFactorCoefficient, OriginalLongFactorWeight.coeff,
          hweight m hmpos]
      calc
        _ = ‖∑ m ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
              originalLongFactorCoefficient .one r p χ s m‖ := by
                rw [hsum]
        _ ≤ (Real.log X) ^ (-21 * a) *
              Real.sqrt (dyadicFactorScale (.one j) / (r : ℝ)) := by
                simpa [OriginalLongFactorAt, zlarge, hzlarge] using hOlocal
    · let zlarge : ℝ := (r : ℝ) * v
      have hzlarge : zlarge / (r : ℝ) = v := by
        dsimp [zlarge]
        field_simp
      have hOlocal := hO .logarithm u v zlarge hleft huv'.le
        (by simpa [zlarge, hzlarge] using hright)
      have hsum :
          (∑ m ∈ factorExtractionRealInterval u v,
            groupedFactorAllocationTerm z (.logarithm j) r p χnat s m) =
          ∑ m ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
            originalLongFactorCoefficient .logarithm r p χ s m := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmreal := (mem_factorExtractionRealInterval hu hv m).mp hm
        have hmul : dyadicFactorScale (.logarithm j) <
            (r : ℝ) * m :=
          lt_of_le_of_lt hscaleLower (mul_lt_mul_of_pos_left hmreal.1 hrR)
        have hlow : dyadicFactorScale (.logarithm j) <
            (r * m : ℕ) := by simpa only [Nat.cast_mul] using hmul
        have hmulU : (r : ℝ) * m ≤ 2 * dyadicFactorScale (.logarithm j) :=
          le_trans (mul_le_mul_of_nonneg_left hmreal.2 hrR.le) hscaleUpper
        have hupp : (r * m : ℕ) ≤ 2 * dyadicFactorScale (.logarithm j) := by
          exact_mod_cast hmulU
        have hmpos : 0 < m := by
          have hmR : 0 < (m : ℝ) := lt_trans huPos hmreal.1
          exact_mod_cast hmR
        have hnpos : 0 < r * m := Nat.mul_pos (lt_of_lt_of_le (by decide) hr) hmpos
        have hI : inDyadicInterval j.val.val (r * m) := by
          simpa [dyadicFactorScale] using
            groupedDyadicInterval_of_real_bounds hnpos ⟨hlow, hupp⟩
        by_cases hcop : Nat.Coprime m p
        · simp [groupedFactorAllocationTerm, dyadicFactorComplexFunction,
            dyadicFactorFunction, dyadicLogFactor_apply, hI, hcop,
            factorExtractionMellinWeight, χnat, hmpos, ArithmeticFunction.log_apply,
            originalLongFactorCoefficient, OriginalLongFactorWeight.coeff]
          ring_nf
        · simp [groupedFactorAllocationTerm, dyadicFactorComplexFunction,
            dyadicFactorFunction, dyadicLogFactor_apply, hI, hcop,
            factorExtractionMellinWeight, χnat, hmpos, ArithmeticFunction.log_apply,
            originalLongFactorCoefficient, OriginalLongFactorWeight.coeff]
      calc
        _ = ‖∑ m ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
              originalLongFactorCoefficient .logarithm r p χ s m‖ := by
                rw [hsum]
        _ ≤ (Real.log X) ^ (-21 * a) *
              Real.sqrt (dyadicFactorScale (.logarithm j) / (r : ℝ)) := by
                simpa [OriginalLongFactorAt, zlarge, hzlarge] using hOlocal
    · have hOlocal := hO .mobius u v z hleft huv'.le hright
      let L := factorExtractionRealInterval u v
      let M := Finset.Ioc (Nat.floor u)
        (Nat.floor (min v (z / (r : ℝ))))
      have hsubM : M ⊆ L := by
        intro m hm
        have hmlo := (Finset.mem_Ioc.mp hm).1
        have hmhi := (Finset.mem_Ioc.mp hm).2
        apply Finset.mem_Ioc.mpr
        refine ⟨hmlo, ?_⟩
        exact le_trans hmhi (Nat.floor_mono (min_le_left v _))
      have hzero : ∀ m ∈ L, m ∉ M →
          groupedFactorAllocationTerm z (.mobius j) r p χnat s m = 0 := by
        intro m hmL hmM
        have hmreal := (mem_factorExtractionRealInterval hu hv m).mp hmL
        have hfloor : Nat.floor (min v (z / (r : ℝ))) < m := by
          have hmlo : Nat.floor u < m := (Finset.mem_Ioc.mp hmL).1
          have hnot : ¬ m ≤ Nat.floor (min v (z / (r : ℝ))) := by
            intro hle
            exact hmM (Finset.mem_Ioc.mpr ⟨hmlo, hle⟩)
          omega
        have hmin0 : 0 ≤ min v (z / (r : ℝ)) :=
          le_min hv (div_nonneg hz hrR.le)
        have hminlt : min v (z / (r : ℝ)) < (m : ℝ) :=
          (Nat.floor_lt hmin0).mp hfloor
        have hzlt : z / (r : ℝ) < (m : ℝ) := by
          by_cases hvz : v ≤ z / (r : ℝ)
          · have : v < (m : ℝ) := by simpa [min_eq_left hvz] using hminlt
            linarith [hmreal.2]
          · simpa [min_eq_right (le_of_not_ge hvz)] using hminlt
        have hzscaled : z < (r : ℝ) * m := by
          simpa [mul_comm] using (div_lt_iff₀ hrR).1 hzlt
        have hcut : ¬ ((r * m : ℕ) : ℝ) ≤ z := by
          have hcast : ((r * m : ℕ) : ℝ) = (r : ℝ) * m := by norm_cast
          rw [hcast]
          exact not_le_of_gt hzscaled
        have hfacReal : dyadicFactorFunction z (.mobius j) (r * m) = 0 := by
          unfold dyadicFactorFunction
          rw [dyadicMobiusFactor_apply]
          rw [if_neg (fun h => hcut h.2)]
        have hfac : dyadicFactorComplexFunction z (.mobius j) (r * m) = 0 := by
          change ((dyadicFactorFunction z (.mobius j) (r * m) : ℝ) : ℂ) = 0
          rw [hfacReal]
          simp
        simp [groupedFactorAllocationTerm, hfac]
      have hsum :
          (∑ m ∈ L,
            groupedFactorAllocationTerm z (.mobius j) r p χnat s m) =
          ∑ m ∈ M, originalLongFactorCoefficient .mobius r p χ s m := by
        calc
          (∑ m ∈ L,
              groupedFactorAllocationTerm z (.mobius j) r p χnat s m) =
              ∑ m ∈ M, groupedFactorAllocationTerm z (.mobius j) r p χnat s m :=
                (Finset.sum_subset hsubM hzero).symm
          _ = ∑ m ∈ M, originalLongFactorCoefficient .mobius r p χ s m := by
                apply Finset.sum_congr rfl
                intro m hm
                have hmreal := (mem_factorExtractionRealInterval hu hv m).mp
                  (hsubM hm)
                have hmul : dyadicFactorScale (.mobius j) < (r : ℝ) * m :=
                  lt_of_le_of_lt hscaleLower
                    (mul_lt_mul_of_pos_left hmreal.1 hrR)
                have hlow : dyadicFactorScale (.mobius j) <
                    (r * m : ℕ) := by simpa only [Nat.cast_mul] using hmul
                have hmulU : (r : ℝ) * m ≤
                    2 * dyadicFactorScale (.mobius j) :=
                  le_trans (mul_le_mul_of_nonneg_left hmreal.2 hrR.le)
                    hscaleUpper
                have hupp : (r * m : ℕ) ≤
                    2 * dyadicFactorScale (.mobius j) := by exact_mod_cast hmulU
                have hmpos : 0 < m := by
                  have hmR : 0 < (m : ℝ) := lt_trans huPos hmreal.1
                  exact_mod_cast hmR
                have hnpos : 0 < r * m :=
                  Nat.mul_pos (lt_of_lt_of_le (by decide) hr) hmpos
                have hI : inDyadicInterval j.val.val (r * m) := by
                  simpa [dyadicFactorScale] using
                    groupedDyadicInterval_of_real_bounds hnpos ⟨hlow, hupp⟩
                have hcut : ((r * m : ℕ) : ℝ) ≤ z := by
                  have hmupper : (m : ℝ) ≤ min v (z / (r : ℝ)) :=
                    le_trans (Nat.cast_le.mpr (Finset.mem_Ioc.mp hm).2)
                      (Nat.floor_le (le_min hv (div_nonneg hz hrR.le)))
                  have hmul := mul_le_mul_of_nonneg_left hmupper hrR.le
                  have hmin := min_le_right v (z / (r : ℝ))
                  calc
                    ((r * m : ℕ) : ℝ) = (r : ℝ) * m := by norm_cast
                    _ ≤ (r : ℝ) * min v (z / (r : ℝ)) := hmul
                    _ ≤ (r : ℝ) * (z / (r : ℝ)) :=
                      mul_le_mul_of_nonneg_left hmin hrR.le
                    _ = z := by field_simp
                have hfac : dyadicFactorComplexFunction z (.mobius j) (r * m) =
                    ((ArithmeticFunction.moebius (r * m) : ℝ) : ℂ) := by
                  change ((dyadicFactorFunction z (.mobius j) (r * m) : ℝ) : ℂ) = _
                  unfold dyadicFactorFunction
                  rw [dyadicMobiusFactor_apply]
                  rw [if_pos ⟨hI, hcut⟩]
                unfold groupedFactorAllocationTerm
                rw [hfac, factorExtractionMellinWeight, dif_pos hmpos]
                by_cases hcop : Nat.Coprime m p
                · simp [hcop, χnat, originalLongFactorCoefficient,
                    OriginalLongFactorWeight.coeff] <;> ring_nf
                · simp [hcop, χnat, originalLongFactorCoefficient,
                    OriginalLongFactorWeight.coeff]
      calc
        _ = ‖∑ m ∈ M, originalLongFactorCoefficient .mobius r p χ s m‖ := by
              rw [hsum]
        _ ≤ (Real.log X) ^ (-21 * a) *
              Real.sqrt (dyadicFactorScale (.mobius j) / (r : ℝ)) := by
                simpa [OriginalLongFactorAt, L, M] using hOlocal

private theorem toComplexArithmeticFunction_complexPositiveConvolution
    (f g : ComplexPositiveIntegerFunction) :
    toComplexArithmeticFunction (complexPositiveDirichletConvolution f g) =
      toComplexArithmeticFunction f * toComplexArithmeticFunction g := by
  ext n
  cases n with
  | zero => simp [toComplexArithmeticFunction, complexPositiveDirichletConvolution]
  | succ n => simp [toComplexArithmeticFunction, complexPositiveDirichletConvolution]

private theorem toComplexArithmeticFunction_dyadicProduct {X : ℝ} (z : ℝ)
    (fs : List (DyadicArithmeticFactor X)) :
    toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs) =
      (fs.map (dyadicFactorComplexFunction z)).prod := by
  induction fs with
  | nil =>
      ext n
      cases n with
      | zero => simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
          dyadicConvolutionFactors]
      | succ n =>
          by_cases hn : n = 0
          · subst n
            simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
              dyadicConvolutionFactors, ArithmeticFunction.one_apply]
          · simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
              dyadicConvolutionFactors, hn, ArithmeticFunction.one_apply]
  | cons f fs ih =>
      have hsingle :
          toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z [f]) =
            dyadicFactorComplexFunction z f := by
        ext n
        cases n with
        | zero => simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
            dyadicConvolutionFactors, dyadicFactorComplexFunction]
        | succ n =>
            simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
              dyadicConvolutionFactors, dyadicFactorComplexFunction]
      change toComplexArithmeticFunction
        (dyadicConvolutionPositiveComplex z ([f] ++ fs)) = _
      rw [← dyadicConvolutionPositiveComplex_append z [f] fs,
        toComplexArithmeticFunction_complexPositiveConvolution, hsingle, ih]
      simp [List.map_cons, List.prod_cons]

private theorem mobiusLabelFactor_not_logarithm {X : ℝ}
    (ν : MobiusDyadicLabel X) {f : DyadicArithmeticFactor X}
    (hf : f ∈ mobiusLabelFactors ν) :
    ∀ j, f ≠ .logarithm j := by
  have hf' : f ∈
      List.ofFn (fun i : Fin ν.1.val => .mobius (ν.2.1 i)) ++
        List.ofFn (fun i : Fin (ν.1.val - 1) => .one (ν.2.2 i)) := by
    simpa [mobiusLabelFactors] using hf
  rcases List.mem_append.mp hf' with hmob | hone
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmob
    intro j hlog
    rw [← hi] at hlog
    cases hlog
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hone
    intro j hlog
    rw [← hi] at hlog
    cases hlog

private theorem factorExtractionAllocationCoordinate_le {k r : ℕ}
    (d : divisorFactorTuples k r) (i : Fin k) :
    (d.1 i).1 ≤ r := by
  have hprod : (d.1 i).1 ≤ ∏ j : Fin k, (d.1 j).1 := by
    simpa using
      (Finset.single_le_prod
        (s := Finset.univ) (f := fun j : Fin k => (d.1 j).1)
        (fun j hj => Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (d.1 j).2))
        (Finset.mem_univ i))
  rw [d.2] at hprod
  exact hprod

private theorem factorExtractionAllocationResidual_pos_le {k r : ℕ}
    (hr : 0 < r) (d : divisorFactorTuples k r) (i : Fin k) :
    0 < factorExtractionAllocationResidual d i ∧
      factorExtractionAllocationResidual d i ≤ r := by
  let P := ∏ j ∈ Finset.Iic i, (d.1 j).1
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun j hj => (d.1 j).2
  have hPle : P ≤ r := by
    calc
      P ≤ ∏ j ∈ Finset.univ, (d.1 j).1 := by
        apply Finset.prod_le_prod_of_subset_of_one_le
          (Finset.subset_univ _)
        intro j hj hjnot
        exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (d.1 j).2)
      _ = r := d.2
  constructor
  · exact Nat.div_pos hPle hPpos
  · exact Nat.div_le_self _ _

private theorem dyadicFactorScale_pos_local {X : ℝ}
    (f : DyadicArithmeticFactor X) : 0 < dyadicFactorScale f := by
  cases f <;> simp [dyadicFactorScale, dyadicScale] <;> positivity

private theorem arithmeticFunction_mul_apply_ne_zero_grouped
    {f g : ArithmeticFunction ℝ} {n : ℕ} (hne : (f * g) n ≠ 0) :
    ∃ x ∈ n.divisorsAntidiagonal, f x.1 ≠ 0 ∧ g x.2 ≠ 0 := by
  rw [ArithmeticFunction.mul_apply] at hne
  by_contra hnone
  have hterms : ∀ x ∈ n.divisorsAntidiagonal,
      f x.1 = 0 ∨ g x.2 = 0 := by
    intro x hx
    by_cases hf : f x.1 = 0
    · exact Or.inl hf
    · right
      by_contra hg
      exact hnone ⟨x, hx, hf, hg⟩
  have hsum : (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rcases hterms x hx with hf | hg
    · simp [hf]
    · simp [hg]
  exact hne hsum

private theorem dyadicConvolutionFactors_support_bounds_grouped
    {X z : ℝ} (fs : List (DyadicArithmeticFactor X)) (hfs : fs ≠ [])
    {n : ℕ} (hne : dyadicConvolutionFactors z fs n ≠ 0) :
    dyadicFactorScaleProduct fs < (n : ℝ) ∧
      (n : ℝ) ≤ (2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs := by
  induction fs generalizing n with
  | nil => contradiction
  | cons f fs ih =>
      cases fs with
      | nil =>
          have hfactor : dyadicFactorFunction z f n ≠ 0 := by
            simpa [dyadicConvolutionFactors] using hne
          have hb := groupedDyadicFactor_support_bounds
            (X := X) (z := z) (f := f) hfactor
          simpa [dyadicFactorScaleProduct, dyadicConvolutionFactors] using hb
      | cons g gs =>
          have hmul :
              (dyadicFactorFunction z f * dyadicConvolutionFactors z (g :: gs)) n ≠ 0 := by
            simpa [dyadicConvolutionFactors] using hne
          obtain ⟨x, hx, hfirst, htail⟩ :=
            arithmeticFunction_mul_apply_ne_zero_grouped hmul
          have hfirstBounds := groupedDyadicFactor_support_bounds
            (X := X) (z := z) (f := f) hfirst
          have htailBounds := ih (by simp) htail
          have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
          have hpairReal : (n : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by
            exact_mod_cast hpair.symm
          have hx1pos : 0 < (x.1 : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero
              (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx)
          have hscalePos : 0 < dyadicFactorScaleProduct (g :: gs) :=
            dyadicFactorScaleProduct_pos (g :: gs)
          have hlow : dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs) <
              (x.1 : ℝ) * (x.2 : ℝ) := by
            calc
              dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs) <
                  (x.1 : ℝ) * dyadicFactorScaleProduct (g :: gs) :=
                mul_lt_mul_of_pos_right hfirstBounds.1 hscalePos
              _ < (x.1 : ℝ) * (x.2 : ℝ) :=
                mul_lt_mul_of_pos_left htailBounds.1 hx1pos
          have hupp : (x.1 : ℝ) * (x.2 : ℝ) ≤
              (2 : ℝ) ^ ((g :: gs).length + 1) *
                (dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs)) := by
            calc
              (x.1 : ℝ) * (x.2 : ℝ) ≤
                  (2 * dyadicFactorScale f) *
                    ((2 : ℝ) ^ (g :: gs).length *
                      dyadicFactorScaleProduct (g :: gs)) :=
                mul_le_mul hfirstBounds.2 htailBounds.2
                  (Nat.cast_nonneg x.2)
                  (mul_nonneg (by norm_num) (dyadicFactorScale_pos_local f).le)
              _ = (2 : ℝ) ^ ((g :: gs).length + 1) *
                    (dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs)) := by
                      rw [pow_succ]
                      ring
          have hscaleeq : dyadicFactorScaleProduct (f :: g :: gs) =
              dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs) := by
            simp [dyadicFactorScaleProduct]
          constructor
          · rw [hscaleeq, hpairReal]
            exact hlow
          · rw [List.length_cons, hscaleeq, hpairReal]
            exact hupp

private theorem selectedMobiusDyadicFactor_not_logarithm
    {X : ℝ} (ν : MobiusDyadicLabel X)
    (I : Finset (Fin (mobiusLabelFactors ν).length))
    {f : DyadicArithmeticFactor X}
    (hf : f ∈ selectedDyadicFactors (mobiusLabelFactors ν) I) :
    ∀ j, f ≠ .logarithm j := by
  rcases List.mem_map.mp hf with ⟨i, hi, rfl⟩
  have hi' : i ∈ I := by simpa using hi
  exact mobiusLabelFactor_not_logarithm ν (List.get_mem _ i)

/-- Extract one long original factor from a selected Möbius label group.
The exact shifted-convolution lemma preserves every gcd allocation and the
product-interval truncation; the only coefficient loss is the component
scalar. -/
theorem groupedMobiusFactorListExtraction
    {X a z s N₁ : ℝ} (hX3 : 3 ≤ X) (hz : 0 ≤ z)
    (hN₁ : 0 < N₁) (ν : MobiusDyadicLabel X)
    (I : Finset (Fin (mobiusLabelFactors ν).length))
    (i : Fin (mobiusLabelFactors ν).length) (hiI : i ∈ I)
    {r Q : ℕ} (hr : 1 ≤ r)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (χ : BlueprintCharacter Q) (hQ : 1 ≤ Q)
    (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a)
    (hfreqlo : (Real.log X) ^ (45 * a) ≤ |s|)
    (hfreqhi : |s| ≤ X ^ (a + 1))
    (hOrig : OriginalLongFactorAt X
      (dyadicFactorScale ((mobiusLabelFactors ν).get i)) s a)
    (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10) :
    ‖c * ∑ m ∈ factorExtractionRealInterval
        (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        dyadicFactorComplexProduct z
          (selectedDyadicFactors (mobiusLabelFactors ν) I) (r * m) *
          factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) s m‖ ≤
      (2 : ℝ) ^ 10 *
        (3 : ℝ) ^
          ((selectedDyadicFactors (mobiusLabelFactors ν) I).length - 1) *
        (divisorFunction
          (selectedDyadicFactors (mobiusLabelFactors ν) I).length
          ⟨r, lt_of_lt_of_le (by decide) hr⟩ : ℝ) *
        (Real.log X) ^ (-21 * a) *
        Real.sqrt
          (dyadicFactorScaleProduct
            (selectedDyadicFactors (mobiusLabelFactors ν) I) / (r : ℝ)) := by
  classical
  let factors := selectedDyadicFactors (mobiusLabelFactors ν) I
  obtain ⟨i₀, hi₀⟩ := selectedDyadicFactors_get_of_mem
    (mobiusLabelFactors ν) I hiI
  have hOrigF : OriginalLongFactorAt X
      (dyadicFactorScale (factors.get i₀)) s a := by
    change OriginalLongFactorAt X
      (dyadicFactorScale ((selectedDyadicFactors
        (mobiusLabelFactors ν) I).get i₀)) s a
    rw [hi₀]
    exact hOrig
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hU : 0 < N₁ / (r : ℝ) := div_pos hN₁ hrR
  have hx : 0 ≤ N₁ / (r : ℝ) := hU.le
  have hxy : N₁ / (r : ℝ) ≤ 2 * N₁ / (r : ℝ) := by
    rw [show 2 * N₁ / (r : ℝ) = 2 * (N₁ / (r : ℝ)) by ring]
    nlinarith
  let cfactors : List (ArithmeticFunction ℂ) :=
    factors.map (dyadicFactorComplexFunction z)
  have hlen : cfactors.length = factors.length := by simp [cfactors]
  let e : Fin cfactors.length ≃ Fin factors.length := finCongr hlen
  let k := cfactors.length
  let i₀c : Fin k := e.symm i₀
  have hOrig₀ : OriginalLongFactorAt X
      (dyadicFactorScale (factors.get (e i₀c))) s a := by
    simpa [i₀c] using hOrigF
  let N : Fin k → ℝ := fun j => dyadicFactorScale (factors.get (e j))
  let B : Fin k → ℝ := fun j => dyadicFactorMassWeight (factors.get (e j))
  let χnat : ℕ → ℂ := fun m => evalInt χ (m : ℤ)
  have hcfget (j : Fin k) :
      cfactors.get j = dyadicFactorComplexFunction z (factors.get (e j)) := by
    simp [cfactors, e, k]
  have hN : ∀ j, 0 < N j := by
    intro j
    exact dyadicFactorScale_pos_local (factors.get (e j))
  have hB : ∀ j, 0 ≤ B j := by
    intro j
    exact dyadicFactorMassWeight_nonneg hX3 (factors.get (e j))
  have hε : 0 ≤ (Real.log X) ^ (-21 * a) :=
    Real.rpow_nonneg (Real.log_pos (by linarith [hX3])).le _
  have hcoeff : ∀ j n, ‖cfactors.get j n‖ ≤ B j := by
    intro j n
    rw [hcfget j]
    simpa [B, dyadicFactorComplexFunction,
      Complex.norm_real, Real.norm_eq_abs] using
        dyadicFactorFunction_abs_le_massWeight hX3 z (factors.get (e j)) n
  have hsupport : ∀ j n, cfactors.get j n ≠ 0 →
      N j < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N j := by
    intro j n hne
    rw [hcfget j] at hne
    have hne' :
        ((dyadicFactorFunction z (factors.get (e j)) n : ℝ) : ℂ) ≠ 0 := by
      simpa [dyadicFactorComplexFunction] using hne
    have hreal : dyadicFactorFunction z (factors.get (e j)) n ≠ 0 := by
      intro hz0
      apply hne'
      exact_mod_cast hz0
    simpa [N] using groupedDyadicFactor_support_bounds
      (X := X) (z := z) (f := factors.get (e j)) hreal
  have hχnorm : ∀ m, 0 < m → ‖χnat m‖ ≤ 1 := by
    intro m hm
    exact evalInt_norm_le_one χ (m : ℤ)
  have hχone : χnat 1 = 1 := by simp [χnat, evalInt]
  have hχmul : ∀ m n, χnat (m * n) = χnat m * χnat n := by
    intro m n
    simp [χnat, evalInt, Int.cast_mul]
  have hshort : ∀ d : divisorFactorTuples k r, ∀ u v : ℝ,
      0 ≤ u →
      Set.Ioc u v ⊆ Set.Ioc
        (N i₀c / ((d.1 i₀c).1 : ℝ))
        (2 * (N i₀c / ((d.1 i₀c).1 : ℝ))) →
      ‖∑ m ∈ factorExtractionRealInterval u v,
        factorExtractionAllocatedFactor
          (fun j n => cfactors.get j n)
          (fun j => (d.1 j).1)
          (fun j => factorExtractionAllocationResidual d j)
          (factorExtractionMellinWeight χnat s) i₀c m‖ ≤
        (Real.log X) ^ (-21 * a) *
          Real.sqrt (N i₀c / ((d.1 i₀c).1 : ℝ)) := by
    intro d u v hu hsub
    let rd : ℕ := (d.1 i₀c).1
    let pd : ℕ := factorExtractionAllocationResidual d i₀c
    have hrdpos : 0 < rd := (d.1 i₀c).2
    have hrdone : 1 ≤ rd := Nat.succ_le_of_lt hrdpos
    have hrdle : rd ≤ r := by
      exact factorExtractionAllocationCoordinate_le d i₀c
    have hrdlog : (rd : ℝ) ≤ (Real.log X) ^ a := by
      calc
        (rd : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrdle
        _ ≤ (Real.log X) ^ a := hrlog
    have hpd := factorExtractionAllocationResidual_pos_le hr0 d i₀c
    have hpdlog : (pd : ℝ) ≤ (Real.log X) ^ a := by
      calc
        (pd : ℝ) ≤ (r : ℝ) := by exact_mod_cast hpd.2
        _ ≤ (Real.log X) ^ a := hrlog
    have hlocal := groupedDyadicFactorOriginalLocalEstimate
      hX3 hz (factors.get (e i₀c)) hOrig₀
      (r := rd) (p := pd) (Q := Q) χ
      hrdone hrdlog (Nat.succ_le_of_lt hpd.1) hpdlog hQ hQlog
      hfreqlo hfreqhi hu hsub
    have hsum :
        (∑ m ∈ factorExtractionRealInterval u v,
          factorExtractionAllocatedFactor
            (fun j n => cfactors.get j n)
            (fun j => (d.1 j).1)
            (fun j => factorExtractionAllocationResidual d j)
            (factorExtractionMellinWeight χnat s) i₀c m) =
        ∑ m ∈ factorExtractionRealInterval u v,
          groupedFactorAllocationTerm z (factors.get (e i₀c)) rd pd
            (fun m => evalInt χ (m : ℤ)) s m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [factorExtractionAllocatedFactor, groupedFactorAllocationTerm]
      have hcoeff :
          (cfactors.get i₀c) ((d.1 i₀c).1 * m) =
            dyadicFactorComplexFunction z (factors.get (e i₀c)) (rd * m) := by
        simpa [rd] using
          congrArg (fun f : ArithmeticFunction ℂ => f ((d.1 i₀c).1 * m))
            (hcfget i₀c)
      rw [hcoeff]
    rw [hsum]
    simpa [rd, pd, N] using hlocal
  have hsmall := shiftedConvolutionSmallFactor
    cfactors hr0 i₀c N B χnat s ((Real.log X) ^ (-21 * a))
    hN hB hε hcoeff hsupport hχnorm hχone hχmul hshort hx hxy
  have hBone (j : Fin k) : B j = 1 := by
    have hmem : factors.get (e j) ∈ factors := List.get_mem factors (e j)
    have hnot := selectedMobiusDyadicFactor_not_logarithm ν I hmem
    cases hval : factors.get (e j) with
    | one l =>
        change dyadicFactorMassWeight (factors.get (e j)) = 1
        rw [hval]
        simp [dyadicFactorMassWeight]
    | mobius l =>
        change dyadicFactorMassWeight (factors.get (e j)) = 1
        rw [hval]
        simp [dyadicFactorMassWeight]
    | logarithm l => exact False.elim (hnot l hval)
  have hBprod : ∏ j ∈ Finset.univ.erase i₀c, B j = 1 := by
    calc
      ∏ j ∈ Finset.univ.erase i₀c, B j =
          ∏ j ∈ Finset.univ.erase i₀c, (1 : ℝ) := by
            apply Finset.prod_congr rfl
            intro j hj
            exact hBone j
      _ = 1 := by simp
  have hNprodFactors :
      (∏ j : Fin factors.length, dyadicFactorScale (factors.get j)) =
        dyadicFactorScaleProduct factors := by
    rw [← Fin.prod_ofFn]
    change (List.ofFn (fun j : Fin factors.length =>
      dyadicFactorScale (factors.get j))).prod =
        (factors.map dyadicFactorScale).prod
    simpa only [List.get_eq_getElem] using
      congrArg List.prod (List.ofFn_getElem_eq_map factors dyadicFactorScale)
  have hNprod : (∏ j : Fin k, N j) =
      dyadicFactorScaleProduct factors := by
    calc
      (∏ j : Fin k, N j) =
          ∏ j : Fin cfactors.length,
            dyadicFactorScale (factors.get (e j)) := by simp [N, k]
      _ = ∏ j : Fin factors.length,
            dyadicFactorScale (factors.get j) :=
          Fintype.prod_equiv e _ _ (by intro j; rfl)
      _ = dyadicFactorScaleProduct factors := hNprodFactors
  have hsmall' :
      ‖∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        dyadicFactorComplexProduct z factors (r * m) *
          factorExtractionMellinWeight χnat s m‖ ≤
      (3 : ℝ) ^ (factors.length - 1) *
        (divisorFunction cfactors.length ⟨r, hr0⟩ : ℝ) *
          (Real.log X) ^ (-21 * a) *
          Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) := by
    simpa [cfactors, factors, k, dyadicFactorComplexProduct,
      hNprod, hBprod] using hsmall
  have hbaseNonneg :
      0 ≤ (3 : ℝ) ^ (factors.length - 1) *
        (divisorFunction cfactors.length ⟨r, hr0⟩ : ℝ) *
        (Real.log X) ^ (-21 * a) *
        Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) := by
    positivity
  have hsmall'' :
      ‖∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        dyadicFactorComplexProduct z factors (r * m) *
          factorExtractionMellinWeight χnat s m‖ ≤
      (3 : ℝ) ^ (factors.length - 1) *
        (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) *
          (Real.log X) ^ (-21 * a) *
          Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) := by
    simpa [cfactors] using hsmall'
  calc
    ‖c * ∑ m ∈ factorExtractionRealInterval
        (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        dyadicFactorComplexProduct z factors (r * m) *
          factorExtractionMellinWeight χnat s m‖ =
      ‖c‖ * ‖∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        dyadicFactorComplexProduct z factors (r * m) *
          factorExtractionMellinWeight χnat s m‖ := by rw [norm_mul]
    _ ≤ (2 : ℝ) ^ 10 *
        ((3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r, hr0⟩ : ℝ) *
          (Real.log X) ^ (-21 * a) *
          Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ))) := by
      exact mul_le_mul hc hsmall'' (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ 10 * (3 : ℝ) ^
          ((selectedDyadicFactors (mobiusLabelFactors ν) I).length - 1) *
        (divisorFunction
          (selectedDyadicFactors (mobiusLabelFactors ν) I).length
          ⟨r, lt_of_lt_of_le (by decide) hr⟩ : ℝ) *
        (Real.log X) ^ (-21 * a) *
        Real.sqrt (dyadicFactorScaleProduct
          (selectedDyadicFactors (mobiusLabelFactors ν) I) / (r : ℝ)) := by
      simp [factors, k]
      ring

/-- The absolute prefactor after the explicit `d₂₀` estimate and the
coarse `log(8X) ≤ 4 log X` loss. -/
noncomputable def groupedMobiusFactorListAbsorptionConstant : ℝ :=
  (2 : ℝ) ^ 12 * (3 : ℝ) ^ 19 * Real.sqrt 2 *
    divisorSubpowerConstant 20 (1 / 100 : ℝ)

/-- A sufficient log-log threshold for the final grouped-factor absorption.
Its only variable parameter is the fixed exponent `a`. -/
noncomputable def groupedMobiusFactorListAbsorptionThreshold (a : ℝ) : ℝ :=
  Real.exp ((2 / (a - a / 100 - 1)) * Real.log
    (groupedMobiusFactorListAbsorptionConstant *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM
        (a - a / 100 - 1) 0))

/-- The selected Möbius factor extraction with its divisor coefficient
reduced to `d₂₀`, followed by the explicit subpower and logarithmic
absorption. The product-scale condition is the nonempty-block consequence
used in the source proof. -/
theorem groupedMobiusFactorListExtractionAbsorbed
    {X a z N₁ s : ℝ} (hX3 : 3 ≤ X) (ha : 2 ≤ a)
    (hz : 0 ≤ z)
    (hthreshold : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (hN₁ : 0 < N₁) (ν : MobiusDyadicLabel X)
    (I : Finset (Fin (mobiusLabelFactors ν).length))
    (i : Fin (mobiusLabelFactors ν).length) (hiI : i ∈ I)
    {r Q : ℕ} (hr : 1 ≤ r)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (χ : BlueprintCharacter Q) (hQ : 1 ≤ Q)
    (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a)
    (hfreqlo : (Real.log X) ^ (45 * a) ≤ |s|)
    (hfreqhi : |s| ≤ X ^ (a + 1))
    (hOrig : OriginalLongFactorAt X
      (dyadicFactorScale ((mobiusLabelFactors ν).get i)) s a)
    (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hprod : dyadicFactorScaleProduct
      (selectedDyadicFactors (mobiusLabelFactors ν) I) ≤ 2 * N₁) :
    ‖c * ∑ m ∈ factorExtractionRealInterval
        (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        dyadicFactorComplexProduct z
          (selectedDyadicFactors (mobiusLabelFactors ν) I) (r * m) *
          factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) s m‖ ≤
      (Real.log X) ^ (-20 * a) * Real.sqrt (N₁ / (r : ℝ)) := by
  classical
  let factors := selectedDyadicFactors (mobiusLabelFactors ν) I
  let L := Real.log X
  let δ := a - a / 100 - 1
  let K := groupedMobiusFactorListAbsorptionConstant
  have hδ : 0 < δ := by
    dsimp [δ]
    nlinarith [ha]
  have hD : 1 ≤ divisorSubpowerConstant 20 (1 / 100 : ℝ) := by
    rw [divisorSubpowerConstant]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbase : 1 ≤ 1 + (20 : ℝ) / ((1 / 100 : ℝ) * Real.log 2) := by
      have hden : 0 < (1 / 100 : ℝ) * Real.log 2 := by positivity
      have hquot : 0 ≤ (20 : ℝ) / ((1 / 100 : ℝ) * Real.log 2) :=
        div_nonneg (by norm_num) hden.le
      linarith
    exact one_le_pow₀ hbase
  have hK : 1 ≤ K := by
    dsimp [K, groupedMobiusFactorListAbsorptionConstant]
    have hsqrt : 1 ≤ Real.sqrt 2 := by
      rw [Real.one_le_sqrt]
      norm_num
    have hD' := hD
    have hconst : 1 ≤ (2 : ℝ) ^ 12 * (3 : ℝ) ^ 19 := by norm_num
    have hconstsqrt : 1 ≤ (2 : ℝ) ^ 12 * (3 : ℝ) ^ 19 * Real.sqrt 2 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ ((2 : ℝ) ^ 12 * (3 : ℝ) ^ 19) * Real.sqrt 2 :=
          mul_le_mul hconst hsqrt (by norm_num) (by positivity)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ ((2 : ℝ) ^ 12 * (3 : ℝ) ^ 19 * Real.sqrt 2) *
          divisorSubpowerConstant 20 (1 / 100 : ℝ) :=
        mul_le_mul hconstsqrt hD (by norm_num) (by positivity)
  have hM : 1 ≤ FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0 :=
    FractionalPrimes.Literature.Uniformity.one_le_logAbsorptionM
  have hKM : 1 ≤ K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0 := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ K * FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0 :=
        mul_le_mul hK hM (by norm_num) (by linarith [hK])
  have hlogKM : 0 ≤ Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0) :=
    Real.log_nonneg hKM
  have hExpNonneg : 0 ≤ (2 / δ) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0) := by
    positivity
  have hthresholdExp : Real.exp ((2 / δ) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0)) ≤ L := by
    simpa [L, δ, K, groupedMobiusFactorListAbsorptionThreshold,
      groupedMobiusFactorListAbsorptionConstant] using hthreshold
  have hLone : 1 ≤ L := by
    have hExpOne : 1 ≤ Real.exp ((2 / δ) * Real.log (K *
        FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0)) := by
      have h := Real.add_one_le_exp ((2 / δ) * Real.log (K *
        FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0))
      linarith
    exact hExpOne.trans hthresholdExp
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hlarge : (2 / δ) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0) ≤
        Real.log L := by
    rw [← Real.log_exp ((2 / δ) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0))]
    exact Real.log_le_log (Real.exp_pos _) hthresholdExp
  have hKpow : K ≤ L ^ δ := by
    have hAbsorb := FractionalPrimes.Literature.Uniformity.log_absorption_bound
      (a := δ) (b := 0) (K := K) (X := L)
      hδ (by norm_num) hK hLone hlarge
    simpa using hAbsorb
  have hKnegative : K * L ^ (-δ) ≤ 1 := by
    have hpowpos : 0 < L ^ δ := Real.rpow_pos_of_pos hLpos δ
    calc
      K * L ^ (-δ) = K / L ^ δ := by
        rw [Real.rpow_neg hLpos.le]
        simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one hpowpos).2 hKpow
  have hlenlo : 1 ≤ factors.length := by
    rw [selectedDyadicFactors_length]
    have hIpos : 0 < I.card := Finset.card_pos.mpr ⟨i, hiI⟩
    omega
  have hlenhi : factors.length ≤ 20 := by
    calc
      factors.length = I.card := by simp [factors]
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ I)
      _ = (mobiusLabelFactors ν).length := by simp
      _ ≤ 20 := (mobiusLabelFactorCount ν).2
  have hlenexp : factors.length - 1 ≤ 19 := by omega
  have hthree : (3 : ℝ) ^ (factors.length - 1) ≤ (3 : ℝ) ^ 19 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hlenexp
  have hdivNat : divisorFunction factors.length ⟨r, lt_of_lt_of_le
      (by decide) hr⟩ ≤ divisorFunction 20 ⟨r, lt_of_lt_of_le
        (by decide) hr⟩ := by
    rw [← divisorCoefficient_eq_divisorFunction factors.length r
          (lt_of_lt_of_le (by decide) hr),
        ← divisorCoefficient_eq_divisorFunction 20 r
          (lt_of_lt_of_le (by decide) hr)]
    exact divisorCoefficient_mono
      (lt_of_lt_of_le (by decide) hr) hlenhi
  have hdivNatR : (divisorFunction factors.length ⟨r,
      lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        divisorFunction 20 ⟨r, lt_of_lt_of_le (by decide) hr⟩ := by
    exact_mod_cast hdivNat
  have hdiv20 : (divisorFunction 20 ⟨r,
      lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        (divisorFunction 2 ⟨r,
          lt_of_lt_of_le (by decide) hr⟩ : ℝ) ^ 20 := by
    have hNat := divisorCoefficient_twenty_le_two_pow r
      (lt_of_lt_of_le (by decide) hr)
    rw [divisorCoefficient_eq_divisorFunction 20 r
          (lt_of_lt_of_le (by decide) hr),
        divisorCoefficient_eq_divisorFunction 2 r
          (lt_of_lt_of_le (by decide) hr)] at hNat
    exact_mod_cast hNat
  have hdivSub := divisorSubpowerExplicit
    (C := 20) (by norm_num) (ε := 1 / 100) (by norm_num)
      (⟨r, lt_of_lt_of_le (by decide) hr⟩ : PositiveInteger)
  have hdivBound : (divisorFunction factors.length ⟨r,
      lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        divisorSubpowerConstant 20 (1 / 100 : ℝ) *
          (r : ℝ) ^ (1 / 100 : ℝ) := by
    exact hdivNatR.trans (hdiv20.trans hdivSub)
  have hrpow : (r : ℝ) ^ (1 / 100 : ℝ) ≤ L ^ (a / 100) := by
    calc
      (r : ℝ) ^ (1 / 100 : ℝ) ≤ (L ^ a) ^ (1 / 100 : ℝ) :=
        Real.rpow_le_rpow (by exact_mod_cast (Nat.zero_le r)) hrlog
          (by norm_num)
      _ = L ^ (a / 100) := by
        rw [← Real.rpow_mul hLpos.le a (1 / 100 : ℝ)]
        congr 1
        ring
  have hdivBoundL : (divisorFunction factors.length ⟨r,
      lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100) := by
    exact hdivBound.trans (mul_le_mul_of_nonneg_left hrpow
      (by positivity))
  have hcoeffBase :
      (2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r,
            lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        (2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
          divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100) := by
    have hA : (2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) ≤
        (2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 :=
      mul_le_mul_of_nonneg_left hthree (by positivity)
    calc
      _ ≤ ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1)) *
          (divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100)) :=
        mul_le_mul_of_nonneg_left hdivBoundL (by positivity)
      _ ≤ (2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
          (divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100)) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ = (2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
          divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100) := by ring
  have hpowjoin : L ^ (a / 100) * L ^ (-21 * a) * L =
      L ^ (-20 * a) * L ^ (-δ) := by
    calc
      L ^ (a / 100) * L ^ (-21 * a) * L =
          L ^ ((a / 100) + (-21 * a) + 1) := by
            calc
              _ = L ^ ((a / 100) + (-21 * a)) * L := by
                rw [← Real.rpow_add hLpos]
              _ = L ^ ((a / 100) + (-21 * a)) * L ^ (1 : ℝ) := by
                congr 1
                exact (Real.rpow_one L).symm
              _ = _ := by rw [← Real.rpow_add hLpos]
      _ = L ^ (-20 * a + -δ) := by
            congr 1
            dsimp [δ]
            ring
      _ = L ^ (-20 * a) * L ^ (-δ) := by
            rw [← Real.rpow_add hLpos]
  have hcoeffAbsorb :
      ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r,
            lt_of_lt_of_le (by decide) hr⟩ : ℝ) * L ^ (-21 * a)) *
          Real.sqrt 2 * (4 * L) ≤ L ^ (-20 * a) := by
    calc
      _ ≤ ((2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
          divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100)) *
            L ^ (-21 * a) * Real.sqrt 2 * (4 * L) := by
          calc
            _ = ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
                (divisorFunction factors.length ⟨r,
                  lt_of_lt_of_le (by decide) hr⟩ : ℝ)) *
                (L ^ (-21 * a) * Real.sqrt 2 * (4 * L)) := by ring
            _ ≤ ((2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
                divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100)) *
                (L ^ (-21 * a) * Real.sqrt 2 * (4 * L)) :=
              mul_le_mul_of_nonneg_right hcoeffBase (by positivity)
            _ = _ := by ring
      _ = K * L ^ (-20 * a) * L ^ (-δ) := by
          calc
            _ = ((2 : ℝ) ^ 12 * (3 : ℝ) ^ 19 * Real.sqrt 2 *
                divisorSubpowerConstant 20 (1 / 100 : ℝ)) *
                  (L ^ (a / 100) * L ^ (-21 * a) * L) := by ring
            _ = K * (L ^ (-20 * a) * L ^ (-δ)) := by
              rw [hpowjoin]
              rfl
            _ = _ := by ring
      _ ≤ L ^ (-20 * a) := by
          calc
            K * L ^ (-20 * a) * L ^ (-δ) =
                L ^ (-20 * a) * (K * L ^ (-δ)) := by ring
            _ ≤ L ^ (-20 * a) * 1 :=
              mul_le_mul_of_nonneg_left hKnegative
                (Real.rpow_nonneg hLpos.le _)
            _ = L ^ (-20 * a) := by ring
  have hsmall := groupedMobiusFactorListExtraction
    hX3 hz hN₁ ν I i hiI hr hrlog χ hQ hQlog
    hfreqlo hfreqhi hOrig c hc
  have hroot : Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) ≤
      Real.sqrt 2 * Real.sqrt (N₁ / (r : ℝ)) := by
    have hfrac : dyadicFactorScaleProduct factors / (r : ℝ) ≤
        2 * (N₁ / (r : ℝ)) := by
      calc
        dyadicFactorScaleProduct factors / (r : ℝ) ≤
            (2 * N₁) / (r : ℝ) :=
          div_le_div_of_nonneg_right (by simpa [factors] using hprod)
            (by positivity)
        _ = 2 * (N₁ / (r : ℝ)) := by ring
    calc
      Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) ≤
          Real.sqrt (2 * (N₁ / (r : ℝ))) := Real.sqrt_le_sqrt hfrac
      _ = Real.sqrt 2 * Real.sqrt (N₁ / (r : ℝ)) := by
          rw [Real.sqrt_mul (by norm_num)]
  have hsmallRoot :
      ‖c * ∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        dyadicFactorComplexProduct z factors (r * m) *
          factorExtractionMellinWeight (fun m => evalInt χ (m : ℤ)) s m‖ ≤
        ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r,
            lt_of_lt_of_le (by decide) hr⟩ : ℝ) * L ^ (-21 * a)) *
          (Real.sqrt 2 * Real.sqrt (N₁ / (r : ℝ))) := by
    exact hsmall.trans (mul_le_mul_of_nonneg_left hroot (by positivity))
  have hcoeff :
      ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r,
            lt_of_lt_of_le (by decide) hr⟩ : ℝ) * L ^ (-21 * a)) *
          Real.sqrt 2 ≤ L ^ (-20 * a) := by
    have h4L : 1 ≤ 4 * L := by nlinarith [hLone]
    have hApos : 0 ≤ (2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
        (divisorFunction factors.length ⟨r,
          lt_of_lt_of_le (by decide) hr⟩ : ℝ) * L ^ (-21 * a) *
          Real.sqrt 2 := by positivity
    calc
      _ = ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r,
            lt_of_lt_of_le (by decide) hr⟩ : ℝ) * L ^ (-21 * a) *
            Real.sqrt 2) * 1 := by ring
      _ ≤ ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r,
            lt_of_lt_of_le (by decide) hr⟩ : ℝ) * L ^ (-21 * a) *
            Real.sqrt 2) * (4 * L) :=
          mul_le_mul_of_nonneg_left h4L hApos
      _ ≤ L ^ (-20 * a) := hcoeffAbsorb
  calc
    _ ≤ ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
        (divisorFunction factors.length ⟨r,
          lt_of_lt_of_le (by decide) hr⟩ : ℝ) * L ^ (-21 * a)) *
        (Real.sqrt 2 * Real.sqrt (N₁ / (r : ℝ))) := hsmallRoot
    _ = (((2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
          (divisorFunction factors.length ⟨r,
            lt_of_lt_of_le (by decide) hr⟩ : ℝ) * L ^ (-21 * a)) *
          Real.sqrt 2) * Real.sqrt (N₁ / (r : ℝ)) := by ring
    _ ≤ L ^ (-20 * a) * Real.sqrt (N₁ / (r : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _)

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.groupedMobiusFactorListExtraction
#print axioms FractionalPrimes.Literature.Twisted.groupedMobiusFactorListExtractionAbsorbed
