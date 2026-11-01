module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedDyadicPTWSourceAssembly
public import FractionalPrimes.Literature.Twisted.GroupedSmallFactorSourceSumUniform
public import FractionalPrimes.Literature.Twisted.GroupedSmallFactorTypeIIPackage
@[expose] public section

/-! The selected Möbius group supplies the exact first-factor block in the
nonunit PTW assembly. The residual coprimality cutoff is absorbed into a
character induced to the residual modulus. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

private theorem selectedMobiusPTW_fixed_witness
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    (hNoI : ¬ typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)))
    (hNoI2 : ¬ typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ))) :
    ∃ I : Finset (Fin (mobiusLabelFactors ν).length),
      ∃ i : Fin (mobiusLabelFactors ν).length,
        i ∈ I ∧
        ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
          |s| ≤ X ^ (a + 1) →
          OriginalLongFactorAt X
            (dyadicFactorScale ((mobiusLabelFactors ν).get i)) s a := by
  have hXone : 1 ≤ X := by linarith [hXlarge]
  let component : ComplexPositiveIntegerFunction := fun n =>
    ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)
  obtain ⟨α, hα, hsum, hscale, _hmob, htagged⟩ :=
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
    obtain ⟨I, i, _v, hiI, _hiAlpha, _hv, hNlow, hNhigh⟩ :=
      largeTypeIIDyadicData_hasOriginalLongFactorIndexRange hXone
        (mobiusLabelFactors ν) α hα hsum hscale hNoIα hdata'
    refine ⟨I, i, hiI, ?_⟩
    intro s hslo hshi
    exact originalLongFactorAt_of_MUF_threshold hMUF ha hXorig
      hNlow hNhigh

private theorem selectedPTWAllocation_prefix_dvd
    {d : ℕ} (r : divisorFactorTuples 3 d) (i : Fin 3) :
    orderedAllocationPrefix r.1 i ∣ d := by
  have hp := Finset.prod_dvd_prod_of_subset
    (Finset.Iic i) Finset.univ (fun j : Fin 3 => (r.1 j).1)
    (Finset.subset_univ _)
  simpa [orderedAllocationPrefix, r.2] using hp

private theorem selectedPTWAllocation_coordinate_dvd
    {d : ℕ} (r : divisorFactorTuples 3 d) (i : Fin 3) :
    (r.1 i).1 ∣ d := by
  have hp := Finset.dvd_prod_of_mem
    (s := Finset.univ) (f := fun j : Fin 3 => (r.1 j).1)
    (Finset.mem_univ i)
  simpa [r.2] using hp

set_option maxHeartbeats 2000000
/-- Fixed-witness form of the selected Möbius first-factor estimate. This is
the interface used when the first group must be the same labelled subset as
the one in a previously extracted type-II factorization. -/
theorem selectedMobiusPTWFirstFactorMellinBlock_fixed
    {a X : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : MobiusDyadicLabel X)
    (I : Finset (Fin (mobiusLabelFactors ν).length))
    (i : Fin (mobiusLabelFactors ν).length) (hiI : i ∈ I)
    (hOriginal : ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
      |s| ≤ X ^ (a + 1) →
      OriginalLongFactorAt X
        (dyadicFactorScale ((mobiusLabelFactors ν).get i)) s a) :
        ∀ {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
          (hqfactor : d * Q = q)
          (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
          (r : divisorFactorTuples 3 d) (M : ℝ) (hM : 0 < M)
          (χ : BlueprintCharacter Q) (s : ℝ),
          (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
          ‖∑ n ∈ factorExtractionRealInterval M (2 * M),
            toComplexArithmeticFunction
                (groupedDyadicFactor (dyadicMobiusCutoff X)
                  (dyadicBinomialCoefficient ν.1 : ℂ)
                  (selectedDyadicFactors (mobiusLabelFactors ν) I))
                ((r.1 0).1 * n) *
              factorExtractionMellinWeight
                (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
            (Real.log X) ^ (-20 * a) * Real.sqrt M := by
  classical
  intro d Q q hd hQ hqfactor hqlog r M hM χ s hslo hshi
  let fs := selectedDyadicFactors (mobiusLabelFactors ν) I
  let z := dyadicMobiusCutoff X
  let c : ℂ := (dyadicBinomialCoefficient ν.1 : ℂ)
  let r₀ := (r.1 0).1
  let p := q / orderedAllocationPrefix r.1 0
  let R := Nat.lcm Q p
  have hX3 : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  have hz : 0 ≤ z := by
    dsimp [z, dyadicMobiusCutoff]
    positivity
  have hc : ‖c‖ ≤ (2 : ℝ) ^ 10 := by
    dsimp [c]
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      dyadicBinomialCoefficient_abs_le ν.1
  have hr₀pos : 0 < r₀ := (r.1 0).2
  have hr₀ : 1 ≤ r₀ := Nat.succ_le_iff.mpr hr₀pos
  have hcoordDvd : r₀ ∣ d := by
    exact selectedPTWAllocation_coordinate_dvd r 0
  have hcoordLeD : r₀ ≤ d := Nat.le_of_dvd hd hcoordDvd
  have hQone : 1 ≤ Q := Nat.succ_le_iff.mpr hQ
  have hdLeQ : d ≤ q := by
    calc
      d ≤ d * Q := by simpa using Nat.mul_le_mul_left d hQone
      _ = q := hqfactor
  have hr₀leq : r₀ ≤ q := hcoordLeD.trans hdLeQ
  have hr₀log : (r₀ : ℝ) ≤ (Real.log X) ^ a := by
    exact (show (r₀ : ℝ) ≤ (q : ℝ) by exact_mod_cast hr₀leq).trans hqlog
  have hprefixDvd := selectedPTWAllocation_prefix_dvd r 0
  have hprefixPos : 0 < orderedAllocationPrefix r.1 0 := by
    unfold orderedAllocationPrefix
    exact Finset.prod_pos fun j hj => (r.1 j).2
  have hqFactored : q = orderedAllocationPrefix r.1 0 *
      ((d / orderedAllocationPrefix r.1 0) * Q) := by
    calc
      q = d * Q := hqfactor.symm
      _ = (orderedAllocationPrefix r.1 0 *
            (d / orderedAllocationPrefix r.1 0)) * Q := by
        rw [Nat.mul_div_cancel' hprefixDvd]
      _ = _ := by ring
  have hprefixDvdQ : orderedAllocationPrefix r.1 0 ∣ q :=
    ⟨(d / orderedAllocationPrefix r.1 0) * Q, hqFactored⟩
  have hpformula : p = (d / orderedAllocationPrefix r.1 0) * Q := by
    dsimp [p]
    apply Nat.mul_left_cancel hprefixPos
    calc
      orderedAllocationPrefix r.1 0 *
          (q / orderedAllocationPrefix r.1 0) = q :=
        Nat.mul_div_cancel' hprefixDvdQ
      _ = orderedAllocationPrefix r.1 0 *
          ((d / orderedAllocationPrefix r.1 0) * Q) := hqFactored
  have hQdvd : Q ∣ p := by
    refine ⟨d / orderedAllocationPrefix r.1 0, ?_⟩
    rw [hpformula]
    exact Nat.mul_comm _ _
  have hDpos : 0 < d / orderedAllocationPrefix r.1 0 :=
    Nat.div_pos (Nat.le_of_dvd hd hprefixDvd) hprefixPos
  have hpPos : 0 < p := by
    rw [hpformula]
    exact Nat.mul_pos hDpos hQ
  have hpLeq : p ≤ q := by
    dsimp [p]
    exact Nat.div_le_self _ _
  have hpLog : (p : ℝ) ≤ (Real.log X) ^ a := by
    exact (show (p : ℝ) ≤ (q : ℝ) by exact_mod_cast hpLeq).trans hqlog
  have hR : R = p := by
    dsimp [R]
    exact Nat.lcm_eq_right_iff_dvd.mpr hQdvd
  have hRpos : 0 < R := by rw [hR]; exact hpPos
  have hRlog : (R : ℝ) ≤ (Real.log X) ^ a := by
    rw [hR]
    exact hpLog
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  letI : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  letI : NeZero R := ⟨Nat.ne_of_gt hRpos⟩
  let χR : BlueprintCharacter R :=
    inducedBlueprintCharacter (Nat.dvd_lcm_left Q p) χ
  have hχweight : ∀ n : ℕ,
      selectedPTWAllocationCharacterWeight q r χ 0 n =
        evalInt χR (n : ℤ) := by
    intro n
    change (if Nat.Coprime n p then evalInt χ (n : ℤ) else 0) =
      evalInt (inducedBlueprintCharacter (Nat.dvd_lcm_left Q p) χ) (n : ℤ)
    rw [inducedLcmCharacter_eval_eq_cutoff χ n]
    by_cases hcop : Nat.Coprime n p <;> simp [hcop]
  have hN₁ : 0 < M * (r₀ : ℝ) := by
    exact mul_pos hM (by exact_mod_cast hr₀pos)
  have hN₁div : M * (r₀ : ℝ) / (r₀ : ℝ) = M := by
    field_simp [ne_of_gt (show 0 < (r₀ : ℝ) by exact_mod_cast hr₀pos)]
  have h2N₁div : 2 * (M * (r₀ : ℝ)) / (r₀ : ℝ) = 2 * M := by
    field_simp [ne_of_gt (show 0 < (r₀ : ℝ) by exact_mod_cast hr₀pos)]
  have hSource := groupedMobiusFactorListExtractionAbsorbed_uniform
    hX3 ha hz hXabsorb hN₁ ν I i hiI hr₀ hr₀log χR
    (Nat.succ_le_iff.mpr hRpos) hRlog hOriginal c hc
  have hbound := hSource s hslo hshi
  have hsourceEq := groupedDyadicFactor_factorExtraction_sum_eq
    (z := z) (N₁ := M * (r₀ : ℝ)) (r := r₀) (Q := R)
    (c := c) (fs := fs) χR s
  have hsourceEq' :
      (∑ n ∈ factorExtractionRealInterval M (2 * M),
        toComplexArithmeticFunction (groupedDyadicFactor z c fs)
            (r₀ * n) *
          factorExtractionMellinWeight
            (fun n => evalInt χR (n : ℤ)) s n) =
        c * ∑ n ∈ factorExtractionRealInterval M (2 * M),
          dyadicFactorComplexProduct z fs (r₀ * n) *
            factorExtractionMellinWeight
              (fun n => evalInt χR (n : ℤ)) s n := by
    simpa [hN₁div, h2N₁div, z, c, fs] using hsourceEq
  have hweightfn :
      factorExtractionMellinWeight
          (selectedPTWAllocationCharacterWeight q r χ 0) s =
        factorExtractionMellinWeight
          (fun n => evalInt χR (n : ℤ)) s := by
    funext n
    simp [factorExtractionMellinWeight, hχweight]
  have hsourceEq'' :
      (∑ n ∈ factorExtractionRealInterval M (2 * M),
        toComplexArithmeticFunction (groupedDyadicFactor z c fs)
            (r₀ * n) *
          factorExtractionMellinWeight
            (selectedPTWAllocationCharacterWeight q r χ 0) s n) =
        c * ∑ n ∈ factorExtractionRealInterval M (2 * M),
          dyadicFactorComplexProduct z fs (r₀ * n) *
            factorExtractionMellinWeight
              (fun n => evalInt χR (n : ℤ)) s n := by
    calc
      (∑ n ∈ factorExtractionRealInterval M (2 * M),
        toComplexArithmeticFunction (groupedDyadicFactor z c fs) (r₀ * n) *
          factorExtractionMellinWeight
            (selectedPTWAllocationCharacterWeight q r χ 0) s n) =
        ∑ n ∈ factorExtractionRealInterval M (2 * M),
          toComplexArithmeticFunction (groupedDyadicFactor z c fs) (r₀ * n) *
            factorExtractionMellinWeight
              (fun n => evalInt χR (n : ℤ)) s n := by
        simp_rw [← hweightfn]
      _ = c * ∑ n ∈ factorExtractionRealInterval M (2 * M),
          dyadicFactorComplexProduct z fs (r₀ * n) *
            factorExtractionMellinWeight
              (fun n => evalInt χR (n : ℤ)) s n := hsourceEq'
  calc
    _ = ‖c * ∑ n ∈ factorExtractionRealInterval M (2 * M),
          dyadicFactorComplexProduct z fs (r₀ * n) *
            factorExtractionMellinWeight
              (fun n => evalInt χR (n : ℤ)) s n‖ :=
      congrArg (fun w : ℂ => ‖w‖) hsourceEq''
    _ ≤ (Real.log X) ^ (-20 * a) * Real.sqrt M := by
      simpa [hN₁div, h2N₁div, z, c, fs] using hbound

/-- The source fixed-witness Mellin estimate discharges the selected first
factor block for every gcd allocation and residual character. The residual
cutoff `q / orderedAllocationPrefix` is represented exactly by inducing the
character from `Q` to that residual modulus. The source requires the global
modulus bound `q ≤ log(X)^a`, which gives both its allocation and character
range hypotheses. -/
theorem selectedMobiusPTWFirstFactorMellinBlock_uniform
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X : ℝ} (ha : 2 ≤ a)
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
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ))) :
    ∃ I : Finset (Fin (mobiusLabelFactors ν).length),
      ∃ i : Fin (mobiusLabelFactors ν).length, i ∈ I ∧
        ∀ {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
          (hqfactor : d * Q = q)
          (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
          (r : divisorFactorTuples 3 d) (M : ℝ) (hM : 0 < M)
          (χ : BlueprintCharacter Q) (s : ℝ),
          (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
          ‖∑ n ∈ factorExtractionRealInterval M (2 * M),
            toComplexArithmeticFunction
                (groupedDyadicFactor (dyadicMobiusCutoff X)
                  (dyadicBinomialCoefficient ν.1 : ℂ)
                  (selectedDyadicFactors (mobiusLabelFactors ν) I))
                ((r.1 0).1 * n) *
              factorExtractionMellinWeight
                (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
            (Real.log X) ^ (-20 * a) * Real.sqrt M := by
  obtain ⟨I, i, hiI, hOriginal⟩ := selectedMobiusPTW_fixed_witness
    hMUF ha hXlarge hXorig ν hν hNoI hNoI2
  exact ⟨I, i, hiI,
    selectedMobiusPTWFirstFactorMellinBlock_fixed
      ha hXlarge hXabsorb ν I i hiI hOriginal⟩

#print axioms selectedMobiusPTWFirstFactorMellinBlock_uniform

end FractionalPrimes.Literature.DirichletMean

end
