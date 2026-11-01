module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThetaLogSelectedGroupSource
public import FractionalPrimes.Literature.DirichletAdapter.SmoothGroupArithmeticFunctionTupleExpansion
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownSmallGroupData
public import FractionalPrimes.Literature.Twisted.ShiftedConvolutionFactorExtraction
import Mathlib.Tactic

/-! A module-safe source identity for the theta/log selected-group branch.
The residue-restricted arithmetic factor is defined locally so this module
does not depend on the legacy Möbius short-interval bridge. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The theta/log branch's source coefficient restricted to one natural
residue class. Its underlying coefficient is the exact normalized smooth
Heath--Brown factor. -/
noncomputable def smoothHeathBrownThetaLogSourceResidueFactor
    {X z : ℝ} (q b : ℕ) (f : SmoothHeathBrownFactor X) : ArithmeticFunction ℂ :=
  ⟨fun n =>
    if n % q = b then
      (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n : ℂ)
    else 0, by
      simp only [Nat.zero_mod]
      split_ifs with h
      · have hb : b = 0 := h.symm
        subst b
        cases f <;> simp [smoothHeathBrownNormalizedFactorCoefficient,
          smoothHeathBrownThetaFactor, smoothHeathBrownLogFactor,
          smoothHeathBrownMobiusFactor]
      · simp [h]⟩

/-- The residue-restricted source factor vanishes off its exact finite
dyadic support. -/
theorem smoothHeathBrownThetaLogSourceResidueFactor_eq_zero_of_not_mem
    {X z : ℝ} (q b : ℕ) (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hn : n ∉ smoothHeathBrownFactorFiniteSupport f) :
    smoothHeathBrownThetaLogSourceResidueFactor (z := z) q b f n = 0 := by
  change (if n % q = b then
      (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n : ℂ)
    else 0) = 0
  by_cases hres : n % q = b
  · simp only [hres, if_pos]
    by_contra hcoeff
    have hreal : smoothHeathBrownNormalizedFactorCoefficient
        (z := z) f n ≠ 0 := by
      intro hzero
      apply hcoeff
      simp [hzero]
    exact hn (smoothHeathBrownNormalizedFactorCoefficient_support
      (z := z) f hreal)
  · simp [hres]

/-- Every natural in the exact finite source support is positive. -/
theorem smoothHeathBrownThetaLogFactorFiniteSupport_pos
    {X : ℝ} (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hn : n ∈ smoothHeathBrownFactorFiniteSupport f) : 0 < n := by
  have hN : 1 ≤ smoothHeathBrownFactorScale f :=
    smoothHeathBrownFactorScale_ge_one f
  have hNnonneg : 0 ≤ smoothHeathBrownFactorScale f := by linarith
  have hwindow : n ∈ smoothFactorMassWindow (smoothHeathBrownFactorScale f) := by
    rw [← smoothHeathBrownFactorFiniteSupport_eq_massWindow]
    exact hn
  have hinterval :=
    (mem_smoothFactorMassWindow hNnonneg n).mp hwindow
  have hhalf : 0 < smoothHeathBrownFactorScale f / 2 := by linarith
  have hreal : 0 < (n : ℝ) := lt_trans hhalf hinterval.1
  exact_mod_cast hreal

/-- The exact source Mellin phase is the weighted normalized factor
coefficient used by the theta/log finite transfer. -/
theorem smoothHeathBrownThetaLogWeightedFactorCoefficient_eq_sourcePhase
    {X z : ℝ} (f : SmoothHeathBrownFactor X) (q b : ℕ) (t : ℝ)
    {n : ℕ} (hn : 0 < n) :
    smoothHeathBrownWeightedFactorCoefficient (z := z) f
        (smoothHeathBrownThetaLogResiduePhaseWeight q b t) n =
      smoothHeathBrownThetaLogSourceResidueFactor (z := z) q b f n *
        (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) := by
  by_cases hres : n % q = b
  · have hfactor :
        smoothHeathBrownThetaLogSourceResidueFactor (z := z) q b f n =
          (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n : ℂ) := by
      simp [smoothHeathBrownThetaLogSourceResidueFactor, hres]
    rw [smoothHeathBrownWeightedFactorCoefficient,
      smoothHeathBrownThetaLogResiduePhaseWeight, dif_pos hn, if_pos hres,
      hfactor]
    have hroot : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn)))
    field_simp [hroot]
  · simp [smoothHeathBrownWeightedFactorCoefficient,
      smoothHeathBrownThetaLogResiduePhaseWeight, hn, hres,
      smoothHeathBrownThetaLogSourceResidueFactor]

/-- Mellin sum over a real half-open interval equals its finite supported
tuple sum, for a selected subset of arithmetic-function factors. -/
theorem smoothHeathBrownThetaLogArithmeticFunctionSubsetProduct_intervalMellinSum_eq_tupleSum
    {K : ℕ} (I : Finset (Fin K)) (f : Fin K → ArithmeticFunction ℂ)
    (S : Fin K → Finset ℕ)
    (hf : ∀ i ∈ I, ∀ n, n ∉ S i → f i n = 0)
    (hpos : ∀ i ∈ I, ∀ n, n ∈ S i → 0 < n)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (s : ℂ) :
    (∑ n ∈ factorExtractionRealInterval x y,
        (∏ i : I, f i.val) n * (n : ℂ) ^ s) =
      ∑ m ∈ (Fintype.piFinset (fun i : I => S i.val)).filter
          (fun m =>
            x < (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ∧
              (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ≤ y),
        ∏ i : I, (f i.val (m i) * (m i : ℂ) ^ s) := by
  classical
  let SSub : I → Finset ℕ := fun i => S i.val
  let A : Finset ℕ := factorExtractionRealInterval x y
  let P : Finset (I → ℕ) :=
    (Fintype.piFinset SSub).filter
      (fun m =>
        x < (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ∧
          (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ≤ y)
  let T : Finset (Σ n : ℕ, I → ℕ) :=
    A.sigma (fun n =>
      (Fintype.piFinset SSub).filter (fun m => ∏ i : I, m i = n))
  have hexpand :
      (∑ n ∈ A, (∏ i : I, f i.val) n * (n : ℂ) ^ s) =
        ∑ n ∈ A,
          ∑ m ∈ (Fintype.piFinset SSub).filter
              (fun m => ∏ i : I, m i = n),
            ∏ i : I, (f i.val (m i) * (m i : ℂ) ^ s) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact arithmeticFunctionSubsetProduct_apply_supportedTupleSum_mellin
      I f S hf hpos n s
  have hmem (z : Σ n : ℕ, I → ℕ) (hz : z ∈ T) : z.2 ∈ P := by
    rcases Finset.mem_sigma.mp hz with ⟨hn, hm⟩
    rcases Finset.mem_filter.mp hm with ⟨hmS, hmprod⟩
    have hwindow :=
      (mem_factorExtractionRealInterval hx hy z.1).mp (by simpa [A] using hn)
    rw [← hmprod] at hwindow
    apply Finset.mem_filter.mpr
    refine ⟨hmS, ?_⟩
    simpa [P, Nat.cast_prod] using hwindow
  have hinj : ∀ z₁ ∈ T, ∀ z₂ ∈ T, z₁.2 = z₂.2 → z₁ = z₂ := by
    intro z₁ hz₁ z₂ hz₂ heq
    rcases Finset.mem_sigma.mp hz₁ with ⟨_, hm₁⟩
    rcases Finset.mem_sigma.mp hz₂ with ⟨_, hm₂⟩
    have hprod₁ := (Finset.mem_filter.mp hm₁).2
    have hprod₂ := (Finset.mem_filter.mp hm₂).2
    have hn : z₁.1 = z₂.1 := by
      calc
        z₁.1 = ∏ i : I, z₁.2 i := hprod₁.symm
        _ = ∏ i : I, z₂.2 i := by rw [heq]
        _ = z₂.1 := hprod₂
    cases z₁ with
    | mk n₁ m₁ =>
      cases z₂ with
      | mk n₂ m₂ =>
        simp only at hn heq
        subst n₂
        subst m₂
        rfl
  have hsurj : ∀ m ∈ P, ∃ z ∈ T, z.2 = m := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmS, hmwindow⟩
    let n : ℕ := ∏ i : I, m i
    have hnwindow : x < (n : ℝ) ∧ (n : ℝ) ≤ y := by
      simpa [n] using hmwindow
    have hn : n ∈ A := by
      apply (mem_factorExtractionRealInterval hx hy n).2
      exact hnwindow
    have htuple :
        m ∈ (Fintype.piFinset SSub).filter (fun v => ∏ i : I, v i = n) :=
      Finset.mem_filter.mpr ⟨hmS, by simp [n]⟩
    exact ⟨⟨n, m⟩,
      Finset.mem_sigma.mpr ⟨by simpa [A] using hn, htuple⟩, rfl⟩
  calc
    (∑ n ∈ factorExtractionRealInterval x y,
        (∏ i : I, f i.val) n * (n : ℂ) ^ s) =
        ∑ n ∈ A, (∏ i : I, f i.val) n * (n : ℂ) ^ s := by rfl
    _ = ∑ n ∈ A,
          ∑ m ∈ (Fintype.piFinset SSub).filter
              (fun m => ∏ i : I, m i = n),
            ∏ i : I, (f i.val (m i) * (m i : ℂ) ^ s) := hexpand
    _ = ∑ z ∈ T, ∏ i : I, (f i.val (z.2 i) * (z.2 i : ℂ) ^ s) := by
          simp [T, Finset.sum_sigma]
    _ = ∑ m ∈ P, ∏ i : I, (f i.val (m i) * (m i : ℂ) ^ s) := by
          refine Finset.sum_bij (fun z _ => z.2) ?_ ?_ ?_ ?_
          · exact hmem
          · exact hinj
          · intro m hm
            obtain ⟨z, hz, heq⟩ := hsurj m hm
            exact ⟨z, hz, heq⟩
          · intro z hz
            rfl
    _ = ∑ m ∈ (Fintype.piFinset (fun i : I => S i.val)).filter
          (fun m =>
            x < (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ∧
              (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ≤ y),
        ∏ i : I, (f i.val (m i) * (m i : ℂ) ^ s) := by rfl

/-- Exact source-interval identity for theta/log residue factors. The result
is the finite convolution used by the already checked theta/log block bound.
The endpoint convention remains `(x,y]`. -/
theorem smoothHeathBrownThetaLogSelectedGroupSourceInterval_eq_tupleSum
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fs.length)) (q : ℕ)
    (residue : Fin fs.length → ℕ) (t x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∑ n ∈ factorExtractionRealInterval x y,
        (∏ i : I,
          smoothHeathBrownThetaLogSourceResidueFactor (z := z)
            q (residue i.val) (fs.get i.val)) n *
          (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) =
      smoothGroupSubsetConvolutionSum I
        (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
        (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
          (fs.get i)
          (smoothHeathBrownThetaLogResiduePhaseWeight q (residue i) t) n)
        x y := by
  classical
  let S : Fin fs.length → Finset ℕ :=
    fun i => smoothHeathBrownFactorFiniteSupport (fs.get i)
  let f : Fin fs.length → ArithmeticFunction ℂ :=
    fun i => smoothHeathBrownThetaLogSourceResidueFactor
      (z := z) q (residue i) (fs.get i)
  let a : Fin fs.length → ℕ → ℂ :=
    fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
      (fs.get i) (smoothHeathBrownThetaLogResiduePhaseWeight q (residue i) t) n
  have hf : ∀ i ∈ I, ∀ n, n ∉ S i → f i n = 0 := by
    intro i hi n hn
    exact smoothHeathBrownThetaLogSourceResidueFactor_eq_zero_of_not_mem
      (z := z) q (residue i) (fs.get i) hn
  have hpos : ∀ i ∈ I, ∀ n, n ∈ S i → 0 < n := by
    intro i hi n hn
    exact smoothHeathBrownThetaLogFactorFiniteSupport_pos (fs.get i) hn
  have hcore :=
    smoothHeathBrownThetaLogArithmeticFunctionSubsetProduct_intervalMellinSum_eq_tupleSum
      I f S hf hpos x y hx hy
      (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))
  have hphase (m : I → ℕ)
      (hm : m ∈ Fintype.piFinset (fun i : I => S i.val)) :
      ∀ i : I, 0 < m i := by
    intro i
    exact smoothHeathBrownThetaLogFactorFiniteSupport_pos (fs.get i.val)
      (Fintype.mem_piFinset.mp hm i)
  have hcoeff (m : I → ℕ)
      (hm : m ∈ Fintype.piFinset (fun i : I => S i.val)) :
      (∏ i : I,
          (f i.val (m i) * (m i : ℂ) ^
            (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)))) =
        ∏ i : I, a i.val (m i) := by
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [a, f]
    exact (smoothHeathBrownThetaLogWeightedFactorCoefficient_eq_sourcePhase
      (z := z) (fs.get i.val) q (residue i.val) t
      (hphase m hm i)).symm
  rw [show
      (∑ n ∈ factorExtractionRealInterval x y,
          (∏ i : I,
            smoothHeathBrownThetaLogSourceResidueFactor (z := z)
              q (residue i.val) (fs.get i.val)) n *
            (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) =
        ∑ n ∈ factorExtractionRealInterval x y,
          (∏ i : I, f i.val) n *
            (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) by rfl] at hcore
  rw [hcore]
  unfold smoothGroupSubsetConvolutionSum
  apply Finset.sum_congr rfl
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmSupport, _⟩
  exact hcoeff m hmSupport

#print axioms smoothHeathBrownThetaLogSourceResidueFactor_eq_zero_of_not_mem
#print axioms smoothHeathBrownThetaLogWeightedFactorCoefficient_eq_sourcePhase
#print axioms smoothHeathBrownThetaLogArithmeticFunctionSubsetProduct_intervalMellinSum_eq_tupleSum
#print axioms smoothHeathBrownThetaLogSelectedGroupSourceInterval_eq_tupleSum

end FractionalPrimes.Literature.DirichletAdapter

end
