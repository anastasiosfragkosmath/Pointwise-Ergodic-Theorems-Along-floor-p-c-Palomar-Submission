module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusFirstFactorBlock
public import FractionalPrimes.Literature.Twisted.SelectedVonMangoldtOriginalFactorUniform
@[expose] public section

@[expose] public section
noncomputable section
open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators
namespace FractionalPrimes.Literature.DirichletMean

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


/-- The selected von Mangoldt group supplies the allocated first-factor block.
The exact residual coprimality weight is the character induced to its modulus. -/
theorem selectedVonMangoldtPTWFirstFactorMellinBlock_fixed
    {a X : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    (i : Fin (vonMangoldtLabelFactors ν).length) (hiI : i ∈ I)
    (hOriginal : ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
      |s| ≤ X ^ (a + 1) →
      OriginalLongFactorAt X
        (dyadicFactorScale ((vonMangoldtLabelFactors ν).get i)) s a) :
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
                  (selectedDyadicFactors (vonMangoldtLabelFactors ν) I))
                ((r.1 0).1 * n) *
              factorExtractionMellinWeight
                (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
            (Real.log X) ^ (-20 * a) * Real.sqrt M := by
  classical
  intro d Q q hd hQ hqfactor hqlog r M hM χ s hslo hshi
  let fs := selectedDyadicFactors (vonMangoldtLabelFactors ν) I
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
  have hSource := selectedVonMangoldtGroup_originalFactorExtractionAbsorbed_uniform
    hX3 ha hz hXabsorb hN₁ ν I i hiI hr₀ hr₀log χR
    (Nat.succ_le_iff.mpr hRpos) hRlog hOriginal
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

#print axioms selectedVonMangoldtPTWFirstFactorMellinBlock_fixed
end FractionalPrimes.Literature.DirichletMean
end
