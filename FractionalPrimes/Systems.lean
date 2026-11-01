module

public import FractionalPrimes.Core
public import FractionalPrimes.Operators
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# System and iterate facts

These facts connect the integer-valued fractional-power times used in the
averages with the ordinary natural iterates supplied by Mathlib.
-/

public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The paper's integer model: counting measure on `ℤ` and the shift
`n ↦ n - 1`. Translation invariance of counting measure is supplied by
Mathlib's additive-group measure interface. -/
@[expose] noncomputable def integerShiftSystem : InvertibleSystem ℤ where
  μ := Measure.count
  sigmaFinite := inferInstance
  T := MeasurableEquiv.addLeft (-1)
  preserves := by
    simpa [sub_eq_add_neg, add_comm] using
      (MeasureTheory.measurePreserving_add_left (Measure.count : Measure ℤ) (-1))

@[simp] theorem integerShiftSystem_measure :
    integerShiftSystem.μ = (Measure.count : Measure ℤ) := rfl

@[simp] theorem integerShiftSystem_apply (n : ℤ) :
    integerShiftSystem.T n = n - 1 := by
  change (-1 : ℤ) + n = n - 1
  omega

/-- Integer iterates of the paper's shift act by translation by `-m`. -/
@[simp] theorem integerShiftSystem_iterate_apply (m n : ℤ) :
    integerShiftSystem.iterate m n = n - m := by
  simp [InvertibleSystem.iterate, integerShiftSystem, sub_eq_add_neg]
  abel

/-- The abstract weighted average on the paper's integer system is exactly
convolution by its finite weighted kernel. -/
theorem weightedAverage_integerShift_eq_integerKernelConvolution
    (c : ℝ) (w : ℕ → ℂ) (f : ℤ → ℂ) (N : Scale) (x : ℤ) :
    weightedAverage integerShiftSystem c w f N x =
      integerKernelConvolution (finiteWeightedIntegerKernel c N w) f x := by
  rw [finiteWeightedIntegerKernel_convolution_eq_sum]
  simp [weightedAverage, integerShiftSystem_iterate_apply]

/-- The unweighted average on the integer system is convolution by the
unweighted floor-power kernel. -/
theorem unweightedAverage_integerShift_eq_integerKernelConvolution
    (c : ℝ) (f : ℤ → ℂ) (N : Scale) (x : ℤ) :
    unweightedAverage integerShiftSystem c f N x =
      integerKernelConvolution (floorPowerKernel c N) f x := by
  simpa [unweightedAverage, floorPowerKernel, finiteWeightedIntegerKernel] using
    (weightedAverage_integerShift_eq_integerKernelConvolution c (fun _ => (1 : ℂ)) f N x)

/-- The von Mangoldt average on the integer system is convolution by its
finite weighted kernel. -/
theorem vonMangoldtAverage_integerShift_eq_integerKernelConvolution
    (c : ℝ) (f : ℤ → ℂ) (N : Scale) (x : ℤ) :
    vonMangoldtAverage integerShiftSystem c f N x =
      integerKernelConvolution (vonMangoldtIntegerKernel c N) f x := by
  simpa [vonMangoldtAverage, vonMangoldtIntegerKernel] using
    (weightedAverage_integerShift_eq_integerKernelConvolution c
      (fun n => (vonMangoldtWeight n : ℂ)) f N x)

/-- The Möbius average on the integer system is convolution by its finite
weighted kernel. -/
theorem mobiusAverage_integerShift_eq_integerKernelConvolution
    (c : ℝ) (f : ℤ → ℂ) (N : Scale) (x : ℤ) :
    mobiusAverage integerShiftSystem c f N x =
      integerKernelConvolution (mobiusIntegerKernel c N) f x := by
  simpa [mobiusAverage, mobiusIntegerKernel] using
    (weightedAverage_integerShift_eq_integerKernelConvolution c
      (fun n => (mobiusWeight n : ℂ)) f N x)

/-- The prime average on the integer system is convolution by the prime
kernel with its exact prime-count normalization. -/
theorem primeAverage_integerShift_eq_primeKernelConvolution
    (c : ℝ) (f : ℤ → ℂ) (N : ℕ) (hN : 2 ≤ N) (x : ℤ) :
    primeAverage integerShiftSystem c f N hN x =
      integerKernelConvolution (primeIntegerKernel c N hN) f x := by
  classical
  let NS : Scale := ⟨N, by omega⟩
  let C : ℂ := (N : ℂ) * (Nat.primeCounting N : ℂ)⁻¹
  have hsum :
      (∑ n ∈ Finset.Icc 1 N,
        primeKernelWeight N n * f (x - floorPower c n)) =
      C * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        f (x - floorPower c p) := by
    change (∑ n ∈ Finset.Icc 1 N,
      (if n.Prime then C else 0) * f (x - floorPower c n)) = _
    calc
      _ = ∑ n ∈ Finset.Icc 1 N, C *
            (if n.Prime then f (x - floorPower c n) else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hp : n.Prime <;> simp [hp]
      _ = C * ∑ n ∈ Finset.Icc 1 N,
            (if n.Prime then f (x - floorPower c n) else 0) := by
        rw [← Finset.mul_sum]
      _ = C * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            f (x - floorPower c p) := by
        rw [← Finset.sum_filter]
  rw [primeIntegerKernel, finiteWeightedIntegerKernel_convolution_eq_sum]
  change (Nat.primeCounting N : ℂ)⁻¹ *
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        f (integerShiftSystem.iterate (floorPower c p) x) = _
  simp only [integerShiftSystem_iterate_apply]
  rw [hsum]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hπ0 : (Nat.primeCounting N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (primeCounting_pos_of_two_le hN))
  dsimp [C, NS]
  field_simp [hN0, hπ0]

/-- Counting measure has no nonempty null sets, so almost-everywhere
representative statements on the paper's integer model are pointwise. -/
theorem integerShiftSystem_ae_iff {p : ℤ → Prop} :
    (∀ᵐ n ∂integerShiftSystem.μ, p n) ↔ ∀ n, p n := by
  simp [integerShiftSystem]

namespace InvertibleSystem

/-- The natural iterate of a measure-preserving transformation is measure preserving. -/
theorem measurePreserving_natIterate {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (n : ℕ) :
    MeasurePreserving ((S.T : X → X)^[n]) S.μ S.μ :=
  S.preserves.iterate n

/-- The transformation at every fractional-power time is measure preserving. -/
theorem measurePreserving_floorTime {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (n : ℕ) :
    MeasurePreserving ((S.T : X → X)^[floorTime c n]) S.μ S.μ :=
  measurePreserving_natIterate S (floorTime c n)

/-- Integer iteration agrees with ordinary iteration at natural exponents. -/
theorem iterate_nat_apply {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (n : ℕ) (x : X) :
    S.iterate (n : ℤ) x = ((S.T : X → X)^[n]) x := by
  rw [InvertibleSystem.iterate]
  rw [zpow_natCast]
  rw [← Equiv.Perm.iterate_eq_pow]
  rfl

/-- Every integer iterate of an invertible measure-preserving system preserves
its measure. -/
theorem measurePreserving_integerIterate {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (m : ℤ) :
    MeasurePreserving (S.iterate m) S.μ S.μ := by
  cases m with
  | ofNat n =>
      convert S.preserves.iterate n using 1
      funext x
      exact (S.iterate_nat_apply n x).symm
  | negSucc n =>
      have hinv : MeasurePreserving (S.T.symm : X → X) S.μ S.μ :=
        MeasurePreserving.symm S.T S.preserves
      have heq : S.iterate (Int.negSucc n) = ((S.T.symm : X → X)^[n + 1]) := by
        funext x
        change (S.T.toEquiv ^ Int.negSucc n) x = _
        calc
          _ = ((S.T.toEquiv ^ (n + 1))⁻¹) x := by rw [zpow_negSucc]
          _ = ((S.T.toEquiv)⁻¹ ^ (n + 1)) x := by rw [inv_pow]
          _ = (S.T.symm.toEquiv ^ (n + 1)) x := by rfl
          _ = ((S.T.symm : X → X)^[n + 1]) x := by
            rw [← Equiv.Perm.iterate_eq_pow]
            rfl
      convert hinv.iterate (n + 1) using 1

/-- Composition with an integer iterate preserves every nonnegative extended
integral, including the value `∞`. -/
theorem lintegral_comp_integerIterate {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (m : ℤ) (f : X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f (S.iterate m x) ∂S.μ = ∫⁻ x, f x ∂S.μ :=
  (measurePreserving_integerIterate S m).lintegral_comp hf

/-- Composition with an integer iterate is an isometry on `Lᵖ`, including
the endpoint `p = ∞`. -/
theorem lp_comp_integerIterate_isometry {X : Type*} [MeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : InvertibleSystem X) (m : ℤ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Isometry
      (Lp.compMeasurePreserving (S.iterate m)
        (measurePreserving_integerIterate S m) : Lp E p S.μ → Lp E p S.μ) :=
  Lp.isometry_compMeasurePreserving (measurePreserving_integerIterate S m)

/-- The union of every integer translate (preimage) of a measurable null set. -/
def integerOrbitUnion {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (A : Set X) : Set X :=
  ⋃ m : ℤ, S.iterate m ⁻¹' A

theorem measurableSet_integerOrbitUnion {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (integerOrbitUnion S A) := by
  exact MeasurableSet.iUnion fun m =>
    (measurePreserving_integerIterate S m).measurable hA

theorem measure_integerOrbitUnion_eq_zero {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) {A : Set X} (hA : MeasurableSet A)
    (hAμ : S.μ A = 0) : S.μ (integerOrbitUnion S A) = 0 := by
  rw [integerOrbitUnion, measure_iUnion_null_iff]
  intro m
  rw [(measurePreserving_integerIterate S m).measure_preimage hA.nullMeasurableSet]
  exact hAμ

/-- Composition of an integer iterate with the system map adds one to its
exponent. -/
theorem iterate_add_one_apply {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (m : ℤ) (x : X) :
    S.iterate (m + 1) x = S.iterate m (S.T x) := by
  change (S.T.toEquiv ^ (m + 1)) x = (S.T.toEquiv ^ m) (S.T x)
  rw [zpow_add, zpow_one]
  rfl

/-- Composition with the inverse system map subtracts one from an integer
iterate exponent. -/
theorem iterate_sub_one_apply {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (m : ℤ) (x : X) :
    S.iterate (m - 1) x = S.iterate m (S.T.symm x) := by
  have hm : m - 1 = m + (-1 : ℤ) := by omega
  change (S.T.toEquiv ^ (m - 1)) x = (S.T.toEquiv ^ m) (S.T.symm x)
  rw [hm, zpow_add, zpow_neg_one]
  rfl

/-- The union of all integer preimages of a set is invariant under the
system map. -/
theorem integerOrbitUnion_preimage_T {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (A : Set X) :
    S.T ⁻¹' integerOrbitUnion S A = integerOrbitUnion S A := by
  ext x
  simp only [Set.mem_preimage, integerOrbitUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    rw [iterate_add_one_apply]
    exact hm
  · rintro ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    rw [← iterate_add_one_apply S (m - 1) x]
    simpa only [sub_add_cancel] using hm

/-- The union of all integer preimages of a set is invariant under the
inverse system map as well. -/
theorem integerOrbitUnion_preimage_Tsymm {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (A : Set X) :
    S.T.symm ⁻¹' integerOrbitUnion S A = integerOrbitUnion S A := by
  ext x
  simp only [Set.mem_preimage, integerOrbitUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    rw [iterate_sub_one_apply]
    exact hm
  · rintro ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    rw [← iterate_sub_one_apply S (m + 1) x]
    rw [show m + 1 - 1 = m by omega]
    exact hm

/-- The paper's floor time may be evaluated using a natural iterate. -/
theorem iterate_floorPower_apply {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (n : ℕ) (x : X) :
    S.iterate (floorPower c n) x = ((S.T : X → X)^[floorTime c n]) x := by
  rw [← coe_floorTime c n]
  exact iterate_nat_apply S (floorTime c n) x

/-- A translated function at a fractional-power time has a natural-iterate form. -/
theorem shift_floorPower_apply {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (n : ℕ) (f : X → ℂ) (x : X) :
    S.shift (floorPower c n) f x = f ((S.T : X → X)^[floorTime c n] x) := by
  rw [shift]
  exact congrArg f (iterate_floorPower_apply S c n x)

end InvertibleSystem

end

end FractionalPrimes
