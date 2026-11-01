module
public import FractionalPrimes.Literature.Twisted.GroupedSmallFactorOfMobiusGoal
public import FractionalPrimes.Literature.Twisted.OriginalLongFactorOfMobiusGoal
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition
@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

namespace FractionalPrimes.Literature.Twisted

/-- The major type-II package contains a labeled original factor in the
middle exponent range. The failed type-I bound and the original scale
comparison put that factor in the range required by
`originalLongFactorOfMobiusGoal`. -/
theorem largeTypeIIDyadicData_hasOriginalLongFactorAt
    {X a z c δ s : ℝ} (hX : 1 ≤ X)
    (fs : List (DyadicArithmeticFactor X))
    (α : Fin fs.length → ℝ)
    (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j : Fin fs.length, α j = 1)
    (hscale : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤ dyadicFactorScale (fs.get j) ∧
        dyadicFactorScale (fs.get j) ≤ normalizedExponentConstant * X ^ α j)
    (hNoI : ∀ j, α j < (3 / 8 : ℝ))
    (hdata : largeTypeIIDyadicComponentData z c δ
      (groupedDyadicFactor z (c : ℂ) fs) fs α)
    (hOriginal : ∀ {N : ℝ},
      (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) ≤ N →
      N ≤ (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) →
      OriginalLongFactorAt X N s a) :
    ∃ I : Finset (Fin fs.length), ∃ i : Fin fs.length,
      ∃ v : ComplexPositiveIntegerFunction,
      i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
        v = groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I) ∧
        OriginalLongFactorAt X (dyadicFactorScale (fs.get i)) s a := by
  rcases hdata with ⟨Aminus, Aplus, v, f₁, f₂, γ, η, η', I, J, J', i,
    htypeII, hfactor, hv, hf₁, hf₂, hAminus1, hAminusAplus,
    hAminusLow, hAplusHigh, hgammasum, hgammaLo, hgammaHi, hmajorGap,
    hvSupport, hf₁Support, hf₂Support, hiI, hiAlpha⟩
  have hlen : 0 < fs.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let w : GroupingPredicates fs.length :=
    ⟨α, hlen, hα, hsum⟩
  have hnotI : ¬ w.I (5 / 8) := by
    intro hwI
    rcases hwI with ⟨j, hj⟩
    have hjlarge : (3 / 8 : ℝ) ≤ α j := by
      dsimp [w, GroupingPredicates.I] at hj
      linarith
    exact (not_lt_of_ge hjlarge) (hNoI j)
  have hrange := groupedFactorOriginalScaleBounds hX w hnotI i hiAlpha (hscale i)
  exact ⟨I, i, v, hiI, hiAlpha, hv,
    hOriginal hrange.1 hrange.2⟩

/-- A nonzero progression term meeting the block forces the product of the
selected dyadic scales below the block's upper endpoint. -/
private theorem groupedShort_toComplexArithmeticFunction_convolution
    (f g : ComplexPositiveIntegerFunction) :
    toComplexArithmeticFunction (complexPositiveDirichletConvolution f g) =
      toComplexArithmeticFunction f * toComplexArithmeticFunction g := by
  ext n
  cases n with
  | zero => simp [toComplexArithmeticFunction, complexPositiveDirichletConvolution]
  | succ n => simp [toComplexArithmeticFunction, complexPositiveDirichletConvolution]

private theorem groupedShort_toComplexArithmeticFunction_dyadicProduct
    {X : ℝ} (z : ℝ) (fs : List (DyadicArithmeticFactor X)) :
    toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs) =
      dyadicFactorComplexProduct z fs := by
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
              dyadicConvolutionFactors, dyadicFactorComplexProduct,
              ArithmeticFunction.one_apply]
          · simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
              dyadicConvolutionFactors, dyadicFactorComplexProduct, hn,
              ArithmeticFunction.one_apply]
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
        groupedShort_toComplexArithmeticFunction_convolution, hsingle, ih]
      simp [List.map_cons, List.prod_cons, dyadicFactorComplexProduct]

private theorem groupedShort_dyadicProduct_apply_eq_ofReal
    {X z : ℝ} (fs : List (DyadicArithmeticFactor X))
    {n : ℕ} (hn : 0 < n) :
    dyadicFactorComplexProduct z fs n =
      ((dyadicConvolutionFactors z fs n : ℝ) : ℂ) := by
  have hproduct := groupedShort_toComplexArithmeticFunction_dyadicProduct z fs
  have happly := congrArg (fun F : ArithmeticFunction ℂ => F n) hproduct
  simpa [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
    dyadicFactorComplexProduct, hn] using happly.symm

private theorem groupedShort_toComplexArithmeticFunction_grouped
    {X z : ℝ} (c : ℂ) (fs : List (DyadicArithmeticFactor X)) :
    toComplexArithmeticFunction (groupedDyadicFactor z c fs) =
      c • dyadicFactorComplexProduct z fs := by
  ext n
  cases n with
  | zero =>
      simp [toComplexArithmeticFunction, groupedDyadicFactor,
        dyadicFactorComplexProduct]
  | succ n =>
      have hcast := groupedShort_dyadicProduct_apply_eq_ofReal (z := z) fs
        (Nat.succ_pos n)
      change c * ((dyadicConvolutionFactors z fs (n + 1) : ℝ) : ℂ) =
        c * dyadicFactorComplexProduct z fs (n + 1)
      rw [hcast]

/-- A nonzero factor-extraction sum has a point in the block where the
selected dyadic convolution is nonzero, forcing its product scale below the
block's upper endpoint. -/
theorem groupedDyadicProductScale_le_of_nonzeroBlockSum
    {X z N₁ s : ℝ} (hN₁ : 0 < N₁)
    (fs : List (DyadicArithmeticFactor X)) (hfs : fs ≠ [])
    {r Q : ℕ} (hr : 1 ≤ r)
    (χ : BlueprintCharacter Q)
    (hsum : ∑ m ∈ factorExtractionRealInterval
        (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        dyadicFactorComplexProduct z fs (r * m) *
          factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) s m ≠ 0) :
    dyadicFactorScaleProduct fs ≤ 2 * N₁ := by
  classical
  let S := factorExtractionRealInterval (N₁ / (r : ℝ))
    (2 * N₁ / (r : ℝ))
  have hterm : ∃ m ∈ S,
      dyadicFactorComplexProduct z fs (r * m) *
        factorExtractionMellinWeight
          (fun m => evalInt χ (m : ℤ)) s m ≠ 0 := by
    by_contra hnone
    apply hsum
    apply Finset.sum_eq_zero
    intro m hm
    by_contra hne
    exact hnone ⟨m, hm, hne⟩
  rcases hterm with ⟨m, hm, hne⟩
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hU : 0 < N₁ / (r : ℝ) := div_pos hN₁ hrR
  have hmBounds : N₁ / (r : ℝ) < (m : ℝ) ∧
      (m : ℝ) ≤ 2 * N₁ / (r : ℝ) := by
    exact (mem_factorExtractionRealInterval hU.le (by positivity) m).mp
      (by simpa [S] using hm)
  have hmpos : 0 < m := by exact_mod_cast (lt_trans hU hmBounds.1)
  have hcf : dyadicFactorComplexProduct z fs (r * m) ≠ 0 :=
    (mul_ne_zero_iff.mp hne).1
  have hconv : dyadicConvolutionFactors z fs (r * m) ≠ 0 := by
    intro hz
    apply hcf
    rw [groupedShort_dyadicProduct_apply_eq_ofReal fs
      (Nat.mul_pos hr0 hmpos), hz]
    simp
  have hsupport := dyadicConvolutionFactors_support_bounds fs hfs hconv
  have hnupper : ((r * m : ℕ) : ℝ) ≤ 2 * N₁ := by
    calc
      ((r * m : ℕ) : ℝ) = (r : ℝ) * (m : ℝ) := by
        exact_mod_cast Nat.cast_mul r m
      _ ≤ (r : ℝ) * (2 * N₁ / (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hmBounds.2 hrR.le
      _ = 2 * N₁ := by field_simp [ne_of_gt hrR]
  exact le_of_lt (hsupport.1.trans_le hnupper)

/-- The threshold selected by `originalLongFactorOfMobiusGoal` for a fixed
Möbius uniformity hypothesis and exponent. -/
noncomputable def mobiusOriginalLongFactorThreshold
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    (a : ℝ) (ha : 2 ≤ a) : ℝ :=
  Classical.choose (originalLongFactorOfMobiusGoal hMUF ha)

/-- The original-factor conclusion at the threshold selected from MUF. -/
theorem originalLongFactorAt_of_MUF_threshold
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X N s : ℝ} (ha : 2 ≤ a)
    (hX : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (hNlow : (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) ≤ N)
    (hNhigh : N ≤ (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ)) :
    OriginalLongFactorAt X N s a := by
  have hspec := Classical.choose_spec (originalLongFactorOfMobiusGoal hMUF ha)
  have hX' := hX
  change Classical.choose (originalLongFactorOfMobiusGoal hMUF ha) ≤ X at hX'
  exact hspec.2 hX' hNlow hNhigh

/-- The actual tagged type-II Möbius component supplies the original factor,
the coefficient, and the nonzero-block scale condition needed by the
absorbed grouped-factor estimate. The sum is written with the zero extension
of the positive-integer group, so its interval endpoints retain the source's
open-left, closed-right convention exactly. -/
theorem largeMobiusTypeIIGroupedSmallFactor
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X N₁ s : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    (hNoI : ¬ typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)))
    (hNoI2 : ¬ typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)))
    (hN₁ : 0 < N₁) {r Q : ℕ} (hr : 1 ≤ r)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (χ : BlueprintCharacter Q) (hQ : 1 ≤ Q)
    (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a)
    (hfreqlo : (Real.log X) ^ (45 * a) ≤ |s|)
    (hfreqhi : |s| ≤ X ^ (a + 1)) :
    ∃ α : Fin (mobiusLabelFactors ν).length → ℝ,
      (∀ j, 0 ≤ α j) ∧
      (∑ j : Fin (mobiusLabelFactors ν).length, α j = 1) ∧
      (∀ j, α j < (3 / 8 : ℝ)) ∧
      ∃ I : Finset (Fin (mobiusLabelFactors ν).length),
        ∃ i : Fin (mobiusLabelFactors ν).length,
        ∃ v : ComplexPositiveIntegerFunction,
          i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
          v = groupedDyadicFactor (dyadicMobiusCutoff X)
            (dyadicBinomialCoefficient ν.1 : ℂ)
            (selectedDyadicFactors (mobiusLabelFactors ν) I) ∧
          ‖∑ m ∈ factorExtractionRealInterval
              (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
            toComplexArithmeticFunction v (r * m) *
              factorExtractionMellinWeight
                (fun m => evalInt χ (m : ℤ)) s m‖ ≤
            (Real.log X) ^ (-20 * a) * Real.sqrt (N₁ / (r : ℝ)) := by
  classical
  have hX3 : 3 ≤ X := by
    have : (3 : ℝ) ≤ 2 ^ 120 := by norm_num
    exact this.trans hXlarge
  have hXone : 1 ≤ X := by linarith
  have hz : 0 ≤ dyadicMobiusCutoff X := by
    unfold dyadicMobiusCutoff
    positivity
  let component : ComplexPositiveIntegerFunction := fun n =>
    ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)
  obtain ⟨α, hα, hsum, hscale, hmob, htagged⟩ :=
    largeMobiusDyadicComponentTypesTagged hXlarge ν hν
  have hNoI' : ¬ typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ)) component := by
    simpa [component] using hNoI
  have hNoI2' : ¬ typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ)) component := by
    simpa [component] using hNoI2
  have hcomponent : component = groupedDyadicFactor
      (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1 : ℂ)
      (mobiusLabelFactors ν) := by
    funext n
    simp [component, groupedDyadicFactor, mobiusDyadicComponent_apply]
  rcases htagged with hI | hI2 | ⟨hdata, hNoIα⟩
  · exact False.elim (hNoI' hI)
  · exact False.elim (hNoI2' hI2)
  · have hdata' : largeTypeIIDyadicComponentData
        (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1)
        (decompositionDelta X)
        (groupedDyadicFactor (dyadicMobiusCutoff X)
          (dyadicBinomialCoefficient ν.1 : ℂ)
          (mobiusLabelFactors ν))
        (mobiusLabelFactors ν) α := by
      change largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        component (mobiusLabelFactors ν) α at hdata
      rw [hcomponent] at hdata
      exact hdata
    have hOriginal : ∀ {N : ℝ},
        (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) ≤ N →
        N ≤ (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) →
        OriginalLongFactorAt X N s a := by
      intro N hNlow hNhigh
      exact originalLongFactorAt_of_MUF_threshold hMUF ha hXorig
        hNlow hNhigh
    obtain ⟨I, i, v, hiI, hiAlpha, hv, hOrig⟩ :=
      largeTypeIIDyadicData_hasOriginalLongFactorAt
        hXone (mobiusLabelFactors ν) α hα hsum hscale hNoIα hdata'
        hOriginal
    let factors := selectedDyadicFactors (mobiusLabelFactors ν) I
    have hfs : factors ≠ [] := by
      intro hempty
      have hlen : factors.length = I.card := by simp [factors]
      have hIpos : 0 < I.card := Finset.card_pos.mpr ⟨i, hiI⟩
      rw [hempty] at hlen
      simp at hlen
      exact False.elim ((Nat.ne_of_gt hIpos) hlen.symm)
    have hscalar : ‖(dyadicBinomialCoefficient ν.1 : ℂ)‖ ≤
        (2 : ℝ) ^ 10 := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using
        dyadicBinomialCoefficient_abs_le ν.1
    let raw := ∑ m ∈ factorExtractionRealInterval
        (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        dyadicFactorComplexProduct (dyadicMobiusCutoff X) factors (r * m) *
          factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) s m
    have hrawBound : ‖(dyadicBinomialCoefficient ν.1 : ℂ) * raw‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt (N₁ / (r : ℝ)) := by
      by_cases hraw : raw = 0
      · rw [hraw]
        have hlog : 0 < Real.log X := Real.log_pos (by linarith)
        have hrhs : 0 ≤ (Real.log X) ^ (-20 * a) *
            Real.sqrt (N₁ / (r : ℝ)) := by positivity
        simpa using hrhs
      · have hprod := groupedDyadicProductScale_le_of_nonzeroBlockSum
          hN₁ factors hfs hr χ (by simpa [raw] using hraw)
        have hAbs := groupedMobiusFactorListExtractionAbsorbed
          hX3 ha hz hXabsorb hN₁ ν I i hiI hr hrlog χ hQ hQlog
          hfreqlo hfreqhi hOrig (dyadicBinomialCoefficient ν.1 : ℂ)
          hscalar hprod
        simpa [raw, factors] using hAbs
    have hsumEq :
        (∑ m ∈ factorExtractionRealInterval
            (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
          toComplexArithmeticFunction v (r * m) *
            factorExtractionMellinWeight
              (fun m => evalInt χ (m : ℤ)) s m) =
        (dyadicBinomialCoefficient ν.1 : ℂ) * raw := by
      have htoV := congrArg toComplexArithmeticFunction hv
      rw [groupedShort_toComplexArithmeticFunction_grouped] at htoV
      calc
        _ = ∑ m ∈ factorExtractionRealInterval
              (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
              ((dyadicBinomialCoefficient ν.1 : ℂ) *
                dyadicFactorComplexProduct (dyadicMobiusCutoff X)
                  factors (r * m)) *
                factorExtractionMellinWeight
                  (fun m => evalInt χ (m : ℤ)) s m := by
            apply Finset.sum_congr rfl
            intro m hm
            have hpoint := congrArg (fun F : ArithmeticFunction ℂ => F (r * m)) htoV
            simpa [factors, Pi.smul_apply, smul_eq_mul] using
              congrArg (fun w : ℂ => w *
                factorExtractionMellinWeight
                  (fun m => evalInt χ (m : ℤ)) s m) hpoint
        _ = (dyadicBinomialCoefficient ν.1 : ℂ) * raw := by
            dsimp [raw]
            calc
              _ = ∑ m ∈ factorExtractionRealInterval
                    (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
                    (dyadicBinomialCoefficient ν.1 : ℂ) *
                      (dyadicFactorComplexProduct (dyadicMobiusCutoff X)
                        factors (r * m) *
                        factorExtractionMellinWeight
                          (fun m => evalInt χ (m : ℤ)) s m) := by
                apply Finset.sum_congr rfl
                intro m hm
                ring
              _ = (dyadicBinomialCoefficient ν.1 : ℂ) *
                    ∑ m ∈ factorExtractionRealInterval
                      (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
                      dyadicFactorComplexProduct (dyadicMobiusCutoff X)
                        factors (r * m) *
                        factorExtractionMellinWeight
                          (fun m => evalInt χ (m : ℤ)) s m := by
                rw [Finset.mul_sum]
    have hbound :
        ‖∑ m ∈ factorExtractionRealInterval
            (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
          toComplexArithmeticFunction v (r * m) *
            factorExtractionMellinWeight
              (fun m => evalInt χ (m : ℤ)) s m‖ ≤
          (Real.log X) ^ (-20 * a) * Real.sqrt (N₁ / (r : ℝ)) := by
      calc
        _ = ‖(dyadicBinomialCoefficient ν.1 : ℂ) * raw‖ :=
          congrArg (fun w : ℂ => ‖w‖) hsumEq
        _ ≤ _ := hrawBound
    exact ⟨α, hα, hsum, hNoIα, I, i, v, hiI, hiAlpha, hv, hbound⟩

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.largeTypeIIDyadicData_hasOriginalLongFactorAt
#print axioms FractionalPrimes.Literature.Twisted.groupedDyadicProductScale_le_of_nonzeroBlockSum
#print axioms FractionalPrimes.Literature.Twisted.largeMobiusTypeIIGroupedSmallFactor
