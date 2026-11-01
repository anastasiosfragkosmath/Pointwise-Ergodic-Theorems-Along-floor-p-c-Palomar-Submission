module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownFinite
public import FractionalPrimes.Literature.Uniformity.ArithmeticDyadicComponents
public import FractionalPrimes.Literature.Uniformity.HeathBrownIdentity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-!
# Finite smooth factors in the truncated Heath--Brown identity

This file distributes the exact truncated Heath--Brown identity over the
finite smooth dyadic partition. It proves the unfiltered component expansion
and its source component count; later support retention and major grouping
are separate steps.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open Finset
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

noncomputable section

/-- Scale indices `0 ≤ j ≤ ceil(log₂(4X))`. -/
abbrev SmoothHeathBrownScaleIndex (X : ℝ) :=
  Fin (smoothHeathBrownDepth X + 1)

/-- The pointwise smooth factor `theta(n/2^j)`, represented as an arithmetic
function with value zero at the arithmetic-function origin. -/
noncomputable def smoothHeathBrownThetaFactor {X : ℝ}
    (j : SmoothHeathBrownScaleIndex X) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else
    smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val), by simp⟩

/-- The pointwise factor `mu(n) 1_{n≤z} theta(n/2^j)`. -/
noncomputable def smoothHeathBrownMobiusFactor {X : ℝ} (z : ℝ)
    (j : SmoothHeathBrownScaleIndex X) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else
    truncatedMobius z n * smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val), by simp⟩

/-- The pointwise factor `log(n) theta(n/2^j)`. -/
noncomputable def smoothHeathBrownLogFactor {X : ℝ}
    (j : SmoothHeathBrownScaleIndex X) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else
    (ArithmeticFunction.log : ArithmeticFunction ℝ) n *
      smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val), by simp⟩

/-- One of the three pointwise factor types in `lda:smooth-hb`. -/
inductive SmoothHeathBrownFactor (X : ℝ) where
  | theta (j : SmoothHeathBrownScaleIndex X)
  | logarithm (j : SmoothHeathBrownScaleIndex X)
  | mobius (j : SmoothHeathBrownScaleIndex X)

/-- The arithmetic function represented by a tagged smooth factor. -/
noncomputable def smoothHeathBrownFactorFunction {X : ℝ} (z : ℝ) :
    SmoothHeathBrownFactor X → ArithmeticFunction ℝ
  | .theta j => smoothHeathBrownThetaFactor j
  | .logarithm j => smoothHeathBrownLogFactor j
  | .mobius j => smoothHeathBrownMobiusFactor z j

/-- The ordered Dirichlet convolution of a list of smooth factors. -/
noncomputable def smoothHeathBrownConvolutionFactors {X : ℝ} (z : ℝ)
    (fs : List (SmoothHeathBrownFactor X)) : ArithmeticFunction ℝ :=
  (fs.map (smoothHeathBrownFactorFunction z)).prod

/-- The finite smooth partition of the constant-one arithmetic function. -/
noncomputable def smoothHeathBrownThetaPartition (X : ℝ) : ArithmeticFunction ℝ :=
  ∑ j : SmoothHeathBrownScaleIndex X, smoothHeathBrownThetaFactor j

/-- The finite smooth partition of the cutoff Möbius function. -/
noncomputable def smoothHeathBrownMobiusPartition (X z : ℝ) : ArithmeticFunction ℝ :=
  ∑ j : SmoothHeathBrownScaleIndex X, smoothHeathBrownMobiusFactor z j

/-- The finite smooth partition of the logarithm. -/
noncomputable def smoothHeathBrownLogPartition (X : ℝ) : ArithmeticFunction ℝ :=
  ∑ j : SmoothHeathBrownScaleIndex X, smoothHeathBrownLogFactor j

private theorem arithmeticFunction_sum_apply {α : Type*} (s : Finset α)
    (f : α → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.sum_insert ha, ArithmeticFunction.add_apply, ih]

/-- Local equality of the theta partition and zeta on the target range. -/
theorem smoothHeathBrownThetaPartition_apply {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    smoothHeathBrownThetaPartition X n = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
  classical
  rw [smoothHeathBrownThetaPartition, arithmeticFunction_sum_apply]
  have hsum :
      (∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
        smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) = 1 := by
    calc
      (∑ j : SmoothHeathBrownScaleIndex X,
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) =
        ∑ j ∈ Finset.range (smoothHeathBrownDepth X + 1),
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j) :=
            Fin.sum_univ_eq_sum_range
              (fun j : ℕ => smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j))
              (smoothHeathBrownDepth X + 1)
      _ = 1 := smoothDyadicTheta_partition hX hn hnX
  calc
    (∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
        smoothHeathBrownThetaFactor j n) =
        ∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) := by
            apply Finset.sum_congr rfl
            intro j
            simp [smoothHeathBrownThetaFactor, hn.ne']
    _ = 1 := hsum
    _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by simp [hn.ne']

/-- Local equality of the Möbius-factor partition and the exact truncated
Möbius function on the target range. -/
theorem smoothHeathBrownMobiusPartition_apply {X z : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    smoothHeathBrownMobiusPartition X z n = truncatedMobius z n := by
  classical
  rw [smoothHeathBrownMobiusPartition, arithmeticFunction_sum_apply]
  have hsum :
      (∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
        smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) = 1 := by
    calc
      (∑ j : SmoothHeathBrownScaleIndex X,
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) =
        ∑ j ∈ Finset.range (smoothHeathBrownDepth X + 1),
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j) :=
            Fin.sum_univ_eq_sum_range
              (fun j : ℕ => smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j))
              (smoothHeathBrownDepth X + 1)
      _ = 1 := smoothDyadicTheta_partition hX hn hnX
  calc
    (∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
        smoothHeathBrownMobiusFactor z j n) =
        ∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
          truncatedMobius z n *
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) := by
              apply Finset.sum_congr rfl
              intro j
              simp [smoothHeathBrownMobiusFactor, hn.ne']
    _ = truncatedMobius z n *
          (∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) := by
              exact (Finset.mul_sum (Finset.univ : Finset (SmoothHeathBrownScaleIndex X))
                (fun j => smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val))
                (truncatedMobius z n)).symm
    _ = truncatedMobius z n := by rw [hsum, mul_one]

/-- Local equality of the logarithm-factor partition and the arithmetic
logarithm on the target range. -/
theorem smoothHeathBrownLogPartition_apply {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    smoothHeathBrownLogPartition X n = (ArithmeticFunction.log : ArithmeticFunction ℝ) n := by
  classical
  rw [smoothHeathBrownLogPartition, arithmeticFunction_sum_apply]
  have hsum :
      (∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
        smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) = 1 := by
    calc
      (∑ j : SmoothHeathBrownScaleIndex X,
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) =
        ∑ j ∈ Finset.range (smoothHeathBrownDepth X + 1),
          smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j) :=
            Fin.sum_univ_eq_sum_range
              (fun j : ℕ => smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j))
              (smoothHeathBrownDepth X + 1)
      _ = 1 := smoothDyadicTheta_partition hX hn hnX
  calc
    (∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
        smoothHeathBrownLogFactor j n) =
        ∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
          (ArithmeticFunction.log : ArithmeticFunction ℝ) n *
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) := by
              apply Finset.sum_congr rfl
              intro j
              simp [smoothHeathBrownLogFactor, hn.ne']
    _ = (ArithmeticFunction.log : ArithmeticFunction ℝ) n *
          (∑ j ∈ (Finset.univ : Finset (SmoothHeathBrownScaleIndex X)),
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) := by
              exact (Finset.mul_sum (Finset.univ : Finset (SmoothHeathBrownScaleIndex X))
                (fun j => smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val))
                ((ArithmeticFunction.log : ArithmeticFunction ℝ) n)).symm
    _ = (ArithmeticFunction.log : ArithmeticFunction ℝ) n := by rw [hsum, mul_one]

/-- Labels for every smooth convolution term in the Möbius identity. -/
abbrev SmoothHeathBrownMobiusLabel (X : ℝ) :=
  Σ r : HeathBrownIndex,
    ((Fin r.val → SmoothHeathBrownScaleIndex X) ×
      (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X))

/-- Labels for every smooth convolution term in the von Mangoldt identity. -/
abbrev SmoothHeathBrownVonMangoldtLabel (X : ℝ) :=
  Σ r : HeathBrownIndex,
    (((Fin r.val → SmoothHeathBrownScaleIndex X) ×
      (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X)) ×
        SmoothHeathBrownScaleIndex X)

/-- The factor list of one smooth Möbius label. -/
def smoothHeathBrownMobiusLabelFactors {X : ℝ}
    (ν : SmoothHeathBrownMobiusLabel X) : List (SmoothHeathBrownFactor X) :=
  List.ofFn (fun i : Fin ν.1.val => .mobius (ν.2.1 i)) ++
    List.ofFn (fun i : Fin (ν.1.val - 1) => .theta (ν.2.2 i))

/-- The factor list of one smooth von Mangoldt label, with its sole log factor
last. -/
def smoothHeathBrownVonMangoldtLabelFactors {X : ℝ}
    (ν : SmoothHeathBrownVonMangoldtLabel X) : List (SmoothHeathBrownFactor X) :=
  List.ofFn (fun i : Fin ν.1.val => .mobius (ν.2.1.1 i)) ++
    List.ofFn (fun i : Fin (ν.1.val - 1) => .theta (ν.2.1.2 i)) ++
      [.logarithm ν.2.2]

/-- The arithmetic component assigned to a smooth Möbius label. -/
noncomputable def smoothHeathBrownMobiusComponent {X : ℝ} (z : ℝ)
    (ν : SmoothHeathBrownMobiusLabel X) : ArithmeticFunction ℝ :=
  algebraMap ℝ (ArithmeticFunction ℝ) (dyadicBinomialCoefficient ν.1) *
    smoothHeathBrownConvolutionFactors z (smoothHeathBrownMobiusLabelFactors ν)

/-- The arithmetic component assigned to a smooth von Mangoldt label. -/
noncomputable def smoothHeathBrownVonMangoldtComponent {X : ℝ} (z : ℝ)
    (ν : SmoothHeathBrownVonMangoldtLabel X) : ArithmeticFunction ℝ :=
  algebraMap ℝ (ArithmeticFunction ℝ) (dyadicBinomialCoefficient ν.1) *
    smoothHeathBrownConvolutionFactors z (smoothHeathBrownVonMangoldtLabelFactors ν)

@[simp]
theorem smoothHeathBrownMobiusComponent_apply {X : ℝ} (z : ℝ)
    (ν : SmoothHeathBrownMobiusLabel X) (n : ℕ) :
    smoothHeathBrownMobiusComponent z ν n =
      dyadicBinomialCoefficient ν.1 *
        smoothHeathBrownConvolutionFactors z (smoothHeathBrownMobiusLabelFactors ν) n := by
  rw [smoothHeathBrownMobiusComponent, ← Algebra.smul_def]
  simp [ArithmeticFunction.smul_map]

@[simp]
theorem smoothHeathBrownVonMangoldtComponent_apply {X : ℝ} (z : ℝ)
    (ν : SmoothHeathBrownVonMangoldtLabel X) (n : ℕ) :
    smoothHeathBrownVonMangoldtComponent z ν n =
      dyadicBinomialCoefficient ν.1 *
        smoothHeathBrownConvolutionFactors z (smoothHeathBrownVonMangoldtLabelFactors ν) n := by
  rw [smoothHeathBrownVonMangoldtComponent, ← Algebra.smul_def]
  simp [ArithmeticFunction.smul_map]

@[simp]
theorem smoothHeathBrownMobiusLabelFactors_length {X : ℝ}
    (ν : SmoothHeathBrownMobiusLabel X) :
    (smoothHeathBrownMobiusLabelFactors ν).length = 2 * ν.1.val - 1 := by
  have hr : 1 ≤ ν.1.val := (Finset.mem_Icc.mp ν.1.property).1
  simp [smoothHeathBrownMobiusLabelFactors]
  omega

@[simp]
theorem smoothHeathBrownVonMangoldtLabelFactors_length {X : ℝ}
    (ν : SmoothHeathBrownVonMangoldtLabel X) :
    (smoothHeathBrownVonMangoldtLabelFactors ν).length = 2 * ν.1.val := by
  have hr : 1 ≤ ν.1.val := (Finset.mem_Icc.mp ν.1.property).1
  simp [smoothHeathBrownVonMangoldtLabelFactors]
  omega

/-- Every source component has between one and twenty factors. -/
theorem smoothHeathBrownMobiusFactorCount {X : ℝ}
    (ν : SmoothHeathBrownMobiusLabel X) :
    1 ≤ (smoothHeathBrownMobiusLabelFactors ν).length ∧
      (smoothHeathBrownMobiusLabelFactors ν).length ≤ 20 := by
  rcases Finset.mem_Icc.mp ν.1.property with ⟨hrlo, hrhi⟩
  rw [smoothHeathBrownMobiusLabelFactors_length]
  omega

/-- Every von Mangoldt component has between one and twenty factors. -/
theorem smoothHeathBrownVonMangoldtFactorCount {X : ℝ}
    (ν : SmoothHeathBrownVonMangoldtLabel X) :
    1 ≤ (smoothHeathBrownVonMangoldtLabelFactors ν).length ∧
      (smoothHeathBrownVonMangoldtLabelFactors ν).length ≤ 20 := by
  rcases Finset.mem_Icc.mp ν.1.property with ⟨hrlo, hrhi⟩
  rw [smoothHeathBrownVonMangoldtLabelFactors_length]
  omega

private theorem smoothHeathBrownMobiusPowerExpansion {X z : ℝ} (r : ℕ) :
    smoothHeathBrownMobiusPartition X z ^ r =
      ∑ φ : Fin r → SmoothHeathBrownScaleIndex X,
        smoothHeathBrownConvolutionFactors z
          (List.ofFn fun i : Fin r => SmoothHeathBrownFactor.mobius (φ i)) := by
  rw [smoothHeathBrownMobiusPartition, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro φ
  simp [smoothHeathBrownConvolutionFactors, List.map_ofFn, List.prod_ofFn,
    smoothHeathBrownFactorFunction]

private theorem smoothHeathBrownThetaPowerExpansion {X : ℝ} (r : ℕ) :
    smoothHeathBrownThetaPartition X ^ r =
      ∑ φ : Fin r → SmoothHeathBrownScaleIndex X,
        smoothHeathBrownConvolutionFactors 0
          (List.ofFn fun i : Fin r => SmoothHeathBrownFactor.theta (φ i)) := by
  rw [smoothHeathBrownThetaPartition, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro φ
  simp [smoothHeathBrownConvolutionFactors, List.map_ofFn, List.prod_ofFn,
    smoothHeathBrownFactorFunction]

private theorem smoothHeathBrownMobiusThetaProductExpansion {X z : ℝ}
    (r s : ℕ) :
    smoothHeathBrownMobiusPartition X z ^ r *
        smoothHeathBrownThetaPartition X ^ s =
      ∑ p : (Fin r → SmoothHeathBrownScaleIndex X) ×
          (Fin s → SmoothHeathBrownScaleIndex X),
        smoothHeathBrownConvolutionFactors z
          (List.ofFn (fun i : Fin r => SmoothHeathBrownFactor.mobius (p.1 i)) ++
            List.ofFn (fun i : Fin s => SmoothHeathBrownFactor.theta (p.2 i))) := by
  rw [smoothHeathBrownMobiusPowerExpansion (X := X) (z := z) r,
    smoothHeathBrownThetaPowerExpansion (X := X) s, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_congr
  intro p
  rcases p with ⟨φ, ψ⟩
  simp [smoothHeathBrownConvolutionFactors, List.map_append, List.prod_append,
    List.map_ofFn, List.prod_ofFn, smoothHeathBrownFactorFunction]

private theorem smoothHeathBrownMobiusThetaLogProductExpansion {X z : ℝ}
    (r s : ℕ) :
    (smoothHeathBrownMobiusPartition X z ^ r *
        smoothHeathBrownThetaPartition X ^ s) * smoothHeathBrownLogPartition X =
      ∑ p : ((Fin r → SmoothHeathBrownScaleIndex X) ×
          (Fin s → SmoothHeathBrownScaleIndex X)) ×
            SmoothHeathBrownScaleIndex X,
        smoothHeathBrownConvolutionFactors z
          ((List.ofFn (fun i : Fin r =>
              SmoothHeathBrownFactor.mobius (p.1.1 i)) ++
            List.ofFn (fun i : Fin s =>
              SmoothHeathBrownFactor.theta (p.1.2 i))) ++
            [SmoothHeathBrownFactor.logarithm p.2]) := by
  rw [smoothHeathBrownMobiusThetaProductExpansion (X := X) (z := z) r s,
    smoothHeathBrownLogPartition, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_congr
  intro p
  rcases p with ⟨⟨φ, ψ⟩, j⟩
  simp [smoothHeathBrownConvolutionFactors, List.map_append, List.prod_append,
    List.map_ofFn, List.prod_ofFn, smoothHeathBrownFactorFunction]
  exact mul_assoc _ _ _

private def smoothHeathBrownIndexEquiv :
    HeathBrownIndex ≃ Fin 10 where
  toFun r := ⟨r.val - 1, by
    rcases Finset.mem_Icc.mp r.property with ⟨hrlo, hrhi⟩
    omega⟩
  invFun r := ⟨r.val + 1, by
    have hrlt := r.isLt
    simp only [Finset.mem_Icc]
    constructor <;> omega⟩
  left_inv r := by
    apply Subtype.ext
    exact Nat.sub_add_cancel (Finset.mem_Icc.mp r.property).1
  right_inv r := by
    apply Fin.ext
    change (r.val + 1) - 1 = r.val
    exact Nat.add_sub_cancel_right _ _

private theorem smoothHeathBrownIndex_card : Fintype.card HeathBrownIndex = 10 := by
  calc
    Fintype.card HeathBrownIndex = Fintype.card (Fin 10) :=
      Fintype.card_congr smoothHeathBrownIndexEquiv
    _ = 10 := Fintype.card_fin 10

private theorem smoothHeathBrownScaleIndex_card (X : ℝ) :
    Fintype.card (SmoothHeathBrownScaleIndex X) =
      smoothHeathBrownDepth X + 1 := by
  simp [SmoothHeathBrownScaleIndex]

private theorem smoothHeathBrownMobiusLabel_card_le (X : ℝ) :
    Fintype.card (SmoothHeathBrownMobiusLabel X) ≤
      10 * (smoothHeathBrownDepth X + 1) ^ 20 := by
  classical
  let d := Fintype.card (SmoothHeathBrownScaleIndex X)
  let D := smoothHeathBrownDepth X + 1
  have hd : d = D := smoothHeathBrownScaleIndex_card X
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hcard : Fintype.card (SmoothHeathBrownMobiusLabel X) =
      ∑ r : HeathBrownIndex, d ^ r.val * d ^ (r.val - 1) := by
    simp [SmoothHeathBrownMobiusLabel, d, Fintype.card_sigma,
      Fintype.card_prod, Fintype.card_fun]
  rw [hcard, hd]
  calc
    (∑ r : HeathBrownIndex, D ^ r.val * D ^ (r.val - 1)) ≤
        ∑ _r : HeathBrownIndex, D ^ 20 := by
          apply Finset.sum_le_sum
          intro r hrmem
          rcases Finset.mem_Icc.mp r.property with ⟨hrlo, hrhi⟩
          have hexp : r.val + (r.val - 1) ≤ 20 := by omega
          calc
            D ^ r.val * D ^ (r.val - 1) = D ^ (r.val + (r.val - 1)) := by
              rw [← pow_add]
            _ ≤ D ^ (r.val + (r.val - 1)) := le_rfl
            _ ≤ D ^ 20 := pow_le_pow_right' hD hexp
    _ = 10 * D ^ 20 := by
      rw [Finset.sum_const, Finset.card_univ, smoothHeathBrownIndex_card]
      simp

private theorem smoothHeathBrownVonMangoldtLabel_card_le (X : ℝ) :
    Fintype.card (SmoothHeathBrownVonMangoldtLabel X) ≤
      10 * (smoothHeathBrownDepth X + 1) ^ 20 := by
  classical
  let d := Fintype.card (SmoothHeathBrownScaleIndex X)
  let D := smoothHeathBrownDepth X + 1
  have hd : d = D := smoothHeathBrownScaleIndex_card X
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hcard : Fintype.card (SmoothHeathBrownVonMangoldtLabel X) =
      ∑ r : HeathBrownIndex, d ^ r.val * d ^ (r.val - 1) * d := by
    simp [SmoothHeathBrownVonMangoldtLabel, d, Fintype.card_sigma,
      Fintype.card_prod, Fintype.card_fun]
  rw [hcard, hd]
  calc
    (∑ r : HeathBrownIndex, D ^ r.val * D ^ (r.val - 1) * D) ≤
        ∑ _r : HeathBrownIndex, D ^ 20 := by
          apply Finset.sum_le_sum
          intro r hrmem
          rcases Finset.mem_Icc.mp r.property with ⟨hrlo, hrhi⟩
          have hexp : r.val + (r.val - 1) + 1 ≤ 20 := by omega
          have hfactor : D ^ r.val * D ^ (r.val - 1) * D =
              D ^ (r.val + (r.val - 1) + 1) := by
            calc
              D ^ r.val * D ^ (r.val - 1) * D =
                  D ^ (r.val + (r.val - 1)) * D := by rw [← pow_add]
              _ = D ^ (r.val + (r.val - 1)) * D ^ 1 := by simp
              _ = D ^ (r.val + (r.val - 1) + 1) := by rw [← pow_add]
          calc
            D ^ r.val * D ^ (r.val - 1) * D =
                D ^ (r.val + (r.val - 1) + 1) := hfactor
            _ ≤ D ^ 20 := pow_le_pow_right' hD hexp
    _ = 10 * D ^ 20 := by
      rw [Finset.sum_const, Finset.card_univ, smoothHeathBrownIndex_card]
      simp

/-- The exact source component count, before any support-based filtering. -/
theorem smoothHeathBrownComponentCount (X : ℝ) :
    Fintype.card (SmoothHeathBrownMobiusLabel X) ≤
        10 * (smoothHeathBrownDepth X + 1) ^ 20 ∧
      Fintype.card (SmoothHeathBrownVonMangoldtLabel X) ≤
        10 * (smoothHeathBrownDepth X + 1) ^ 20 := by
  exact ⟨smoothHeathBrownMobiusLabel_card_le X,
    smoothHeathBrownVonMangoldtLabel_card_le X⟩

/-- The binomial coefficients have the exact source bound. -/
theorem smoothHeathBrownComponentCoefficient_abs_le (r : HeathBrownIndex) :
    |dyadicBinomialCoefficient r| ≤ 2 ^ 10 :=
  dyadicBinomialCoefficient_abs_le r

private theorem arithmeticFunction_pow_apply_eq_of_divisors
    {f g : ArithmeticFunction ℝ} (k n : ℕ)
    (hfg : ∀ d, d ∣ n → f d = g d) :
    (f ^ k) n = (g ^ k) n := by
  induction k generalizing n hfg with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ArithmeticFunction.mul_apply,
        pow_succ, ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro x hx
      have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hdvd1 : x.1 ∣ n := ⟨x.2, hpair.symm⟩
      have hdvd2 : x.2 ∣ n := ⟨x.1, by simpa [Nat.mul_comm] using hpair.symm⟩
      have hleft : (f ^ k) x.1 = (g ^ k) x.1 :=
        ih x.1 (fun d hd => hfg d (dvd_trans hd hdvd1))
      rw [hleft, hfg x.2 hdvd2]

private theorem arithmeticFunction_mul_apply_eq_of_divisors
    {f f' g g' : ArithmeticFunction ℝ} {n : ℕ}
    (hff : ∀ d, d ∣ n → f d = f' d)
    (hgg : ∀ d, d ∣ n → g d = g' d) :
    (f * g) n = (f' * g') n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hdvd1 : x.1 ∣ n := ⟨x.2, hpair.symm⟩
  have hdvd2 : x.2 ∣ n := ⟨x.1, by simpa [Nat.mul_comm] using hpair.symm⟩
  rw [hff x.1 hdvd1, hgg x.2 hdvd2]

private theorem smoothHeathBrownLocalMobius {X z : ℝ} (hX : 3 ≤ X)
    {n d : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) (hdn : d ∣ n) :
    truncatedMobius z d = smoothHeathBrownMobiusPartition X z d := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hdle : d ≤ n := Nat.le_of_dvd hn hdn
  have hdreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdle
  exact (smoothHeathBrownMobiusPartition_apply hX hdpos
    (hdreal.trans hnX)).symm

private theorem smoothHeathBrownLocalTheta {X : ℝ} (hX : 3 ≤ X)
    {n d : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) (hdn : d ∣ n) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d =
      smoothHeathBrownThetaPartition X d := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hdle : d ≤ n := Nat.le_of_dvd hn hdn
  have hdreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdle
  exact (smoothHeathBrownThetaPartition_apply hX hdpos
    (hdreal.trans hnX)).symm

private theorem smoothHeathBrownLocalLog {X : ℝ} (hX : 3 ≤ X)
    {n d : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) (hdn : d ∣ n) :
    (ArithmeticFunction.log : ArithmeticFunction ℝ) d =
      smoothHeathBrownLogPartition X d := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hdle : d ≤ n := Nat.le_of_dvd hn hdn
  have hdreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdle
  exact (smoothHeathBrownLogPartition_apply hX hdpos
    (hdreal.trans hnX)).symm

/-- The exact unfiltered smooth convolution expansion of the Möbius function
on `0<n≤3X`. Its cutoff is the source's `z=(4X)^(1/10)`, and its labels have
the exact source bound `10 (J+1)^20`. -/
theorem smoothHeathBrownMobiusExpansion {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    (ArithmeticFunction.moebius n : ℝ) =
      ∑ ν : SmoothHeathBrownMobiusLabel X,
        smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n := by
  classical
  let z : ℝ := dyadicMobiusCutoff X
  have hX0 : 0 ≤ X := by linarith
  have hz1 : 1 ≤ z := by
    dsimp [z]
    exact dyadicMobiusCutoff_ge_one hX
  have hnz : (n : ℝ) ≤ z ^ 10 := by
    dsimp [z]
    rw [dyadicMobiusCutoff_pow hX0]
    linarith
  have hHB := heathBrownMobiusIdentity (L := 10) (by norm_num) (z := z)
    hz1 hn hnz
  have hHBattach :
      (ArithmeticFunction.moebius n : ℝ) =
        ∑ r ∈ (Finset.Icc 1 10).attach,
          ((-1 : ℝ) ^ (r.val - 1) * (Nat.choose 10 r.val : ℝ)) *
            ((truncatedMobius z ^ r.val *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) n) := by
    rw [← Finset.sum_attach]
    exact hHB
  have hHB' :
      (ArithmeticFunction.moebius n : ℝ) =
        ∑ r : HeathBrownIndex,
          dyadicBinomialCoefficient r *
            ((truncatedMobius z ^ r.val *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) n) := by
    simpa [HeathBrownIndex, dyadicBinomialCoefficient,
      Finset.sum_coe_sort_eq_attach] using hHBattach
  have hterm (r : HeathBrownIndex) :
      dyadicBinomialCoefficient r *
          ((truncatedMobius z ^ r.val *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) n) =
        ∑ p : (Fin r.val → SmoothHeathBrownScaleIndex X) ×
            (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X),
          smoothHeathBrownMobiusComponent z ⟨r, p⟩ n := by
    have hpowMu (m : ℕ) (hmn : m ∣ n) :
        (truncatedMobius z ^ r.val) m =
          (smoothHeathBrownMobiusPartition X z ^ r.val) m := by
      apply arithmeticFunction_pow_apply_eq_of_divisors
      intro d hdm
      exact smoothHeathBrownLocalMobius hX hn hnX (dvd_trans hdm hmn)
    have hpowTheta (m : ℕ) (hmn : m ∣ n) :
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) m =
          (smoothHeathBrownThetaPartition X ^ (r.val - 1)) m := by
      apply arithmeticFunction_pow_apply_eq_of_divisors
      intro d hdm
      exact smoothHeathBrownLocalTheta hX hn hnX (dvd_trans hdm hmn)
    have hprod := arithmeticFunction_mul_apply_eq_of_divisors hpowMu hpowTheta
    have hexp := smoothHeathBrownMobiusThetaProductExpansion
      (X := X) (z := z) r.val (r.val - 1)
    have hexpN :
        (smoothHeathBrownMobiusPartition X z ^ r.val *
          smoothHeathBrownThetaPartition X ^ (r.val - 1)) n =
        ∑ p : (Fin r.val → SmoothHeathBrownScaleIndex X) ×
            (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X),
          smoothHeathBrownConvolutionFactors z
            (List.ofFn (fun i : Fin r.val =>
                SmoothHeathBrownFactor.mobius (p.1 i)) ++
              List.ofFn (fun i : Fin (r.val - 1) =>
                SmoothHeathBrownFactor.theta (p.2 i))) n := by
      calc
        _ = (∑ p : (Fin r.val → SmoothHeathBrownScaleIndex X) ×
              (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X),
              smoothHeathBrownConvolutionFactors z
                (List.ofFn (fun i : Fin r.val =>
                    SmoothHeathBrownFactor.mobius (p.1 i)) ++
                  List.ofFn (fun i : Fin (r.val - 1) =>
                    SmoothHeathBrownFactor.theta (p.2 i)))) n :=
              congrArg (fun F : ArithmeticFunction ℝ => F n) hexp
        _ = _ := arithmeticFunction_sum_apply _ _ _
    calc
      _ = dyadicBinomialCoefficient r *
          ((smoothHeathBrownMobiusPartition X z ^ r.val *
            smoothHeathBrownThetaPartition X ^ (r.val - 1)) n) := by
              rw [hprod]
      _ = ∑ p : (Fin r.val → SmoothHeathBrownScaleIndex X) ×
            (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X),
          dyadicBinomialCoefficient r *
            smoothHeathBrownConvolutionFactors z
              (List.ofFn (fun i : Fin r.val =>
                  SmoothHeathBrownFactor.mobius (p.1 i)) ++
                List.ofFn (fun i : Fin (r.val - 1) =>
                  SmoothHeathBrownFactor.theta (p.2 i))) n := by
              rw [hexpN, Finset.mul_sum]
      _ = _ := by
            apply Fintype.sum_congr
            intro p
            simp [smoothHeathBrownMobiusComponent_apply,
              smoothHeathBrownMobiusLabelFactors, dyadicBinomialCoefficient]
  calc
    (ArithmeticFunction.moebius n : ℝ) =
        ∑ r : HeathBrownIndex,
          dyadicBinomialCoefficient r *
            ((truncatedMobius z ^ r.val *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) n) := hHB'
    _ = ∑ r : HeathBrownIndex,
          ∑ p : (Fin r.val → SmoothHeathBrownScaleIndex X) ×
            (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X),
              smoothHeathBrownMobiusComponent z ⟨r, p⟩ n := by
          apply Fintype.sum_congr
          intro r
          exact hterm r
    _ = ∑ ν : SmoothHeathBrownMobiusLabel X,
          smoothHeathBrownMobiusComponent z ν n := by
          simpa only [SmoothHeathBrownMobiusLabel, Fintype.sum_sigma]

/-- The exact unfiltered smooth convolution expansion of the von Mangoldt
function on `0<n≤3X`, with the source cutoff and component count. -/
theorem smoothHeathBrownVonMangoldtExpansion {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    ArithmeticFunction.vonMangoldt n =
      ∑ ν : SmoothHeathBrownVonMangoldtLabel X,
        smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν n := by
  classical
  let z : ℝ := dyadicMobiusCutoff X
  have hX0 : 0 ≤ X := by linarith
  have hz1 : 1 ≤ z := by
    dsimp [z]
    exact dyadicMobiusCutoff_ge_one hX
  have hnz : (n : ℝ) ≤ z ^ 10 := by
    dsimp [z]
    rw [dyadicMobiusCutoff_pow hX0]
    linarith
  have hHB := heathBrownVonMangoldtIdentity (L := 10) (by norm_num) (z := z)
    hz1 hn hnz
  have hHBattach :
      ArithmeticFunction.vonMangoldt n =
        ∑ r ∈ (Finset.Icc 1 10).attach,
          ((-1 : ℝ) ^ (r.val - 1) * (Nat.choose 10 r.val : ℝ)) *
            (((truncatedMobius z ^ r.val *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) *
                (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) := by
    rw [← Finset.sum_attach]
    exact hHB
  have hHB' :
      ArithmeticFunction.vonMangoldt n =
        ∑ r : HeathBrownIndex,
          dyadicBinomialCoefficient r *
            (((truncatedMobius z ^ r.val *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) *
                (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) := by
    simpa [HeathBrownIndex, dyadicBinomialCoefficient,
      Finset.sum_coe_sort_eq_attach] using hHBattach
  have hterm (r : HeathBrownIndex) :
      dyadicBinomialCoefficient r *
          (((truncatedMobius z ^ r.val *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) *
              (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) =
        ∑ p : ((Fin r.val → SmoothHeathBrownScaleIndex X) ×
            (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X)) ×
              SmoothHeathBrownScaleIndex X,
          smoothHeathBrownVonMangoldtComponent z ⟨r, p⟩ n := by
    have hpowMu (m : ℕ) (hmn : m ∣ n) :
        (truncatedMobius z ^ r.val) m =
          (smoothHeathBrownMobiusPartition X z ^ r.val) m := by
      apply arithmeticFunction_pow_apply_eq_of_divisors
      intro d hdm
      exact smoothHeathBrownLocalMobius hX hn hnX (dvd_trans hdm hmn)
    have hpowTheta (m : ℕ) (hmn : m ∣ n) :
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) m =
          (smoothHeathBrownThetaPartition X ^ (r.val - 1)) m := by
      apply arithmeticFunction_pow_apply_eq_of_divisors
      intro d hdm
      exact smoothHeathBrownLocalTheta hX hn hnX (dvd_trans hdm hmn)
    have hpowProduct (m : ℕ) (hmn : m ∣ n) :
        (truncatedMobius z ^ r.val *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) m =
        (smoothHeathBrownMobiusPartition X z ^ r.val *
          smoothHeathBrownThetaPartition X ^ (r.val - 1)) m := by
      exact arithmeticFunction_mul_apply_eq_of_divisors
        (fun d hdm => hpowMu d (dvd_trans hdm hmn))
        (fun d hdm => hpowTheta d (dvd_trans hdm hmn))
    have hprod := arithmeticFunction_mul_apply_eq_of_divisors
      hpowProduct (fun d hdn => smoothHeathBrownLocalLog hX hn hnX hdn)
    have hexp := smoothHeathBrownMobiusThetaLogProductExpansion
      (X := X) (z := z) r.val (r.val - 1)
    have hexpN :
        ((smoothHeathBrownMobiusPartition X z ^ r.val *
          smoothHeathBrownThetaPartition X ^ (r.val - 1)) *
            smoothHeathBrownLogPartition X) n =
        ∑ p : ((Fin r.val → SmoothHeathBrownScaleIndex X) ×
            (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X)) ×
              SmoothHeathBrownScaleIndex X,
          smoothHeathBrownConvolutionFactors z
            ((List.ofFn (fun i : Fin r.val =>
                SmoothHeathBrownFactor.mobius (p.1.1 i)) ++
              List.ofFn (fun i : Fin (r.val - 1) =>
                SmoothHeathBrownFactor.theta (p.1.2 i))) ++
            [SmoothHeathBrownFactor.logarithm p.2]) n := by
      calc
        _ = (∑ p : ((Fin r.val → SmoothHeathBrownScaleIndex X) ×
              (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X)) ×
                SmoothHeathBrownScaleIndex X,
              smoothHeathBrownConvolutionFactors z
                ((List.ofFn (fun i : Fin r.val =>
                    SmoothHeathBrownFactor.mobius (p.1.1 i)) ++
                  List.ofFn (fun i : Fin (r.val - 1) =>
                    SmoothHeathBrownFactor.theta (p.1.2 i))) ++
                [SmoothHeathBrownFactor.logarithm p.2])) n :=
              congrArg (fun F : ArithmeticFunction ℝ => F n) hexp
        _ = _ := arithmeticFunction_sum_apply _ _ _
    calc
      _ = dyadicBinomialCoefficient r *
          (((smoothHeathBrownMobiusPartition X z ^ r.val *
            smoothHeathBrownThetaPartition X ^ (r.val - 1)) *
              smoothHeathBrownLogPartition X) n) := by
                rw [hprod]
      _ = ∑ p : ((Fin r.val → SmoothHeathBrownScaleIndex X) ×
            (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X)) ×
              SmoothHeathBrownScaleIndex X,
          dyadicBinomialCoefficient r *
            smoothHeathBrownConvolutionFactors z
              ((List.ofFn (fun i : Fin r.val =>
                  SmoothHeathBrownFactor.mobius (p.1.1 i)) ++
                List.ofFn (fun i : Fin (r.val - 1) =>
                  SmoothHeathBrownFactor.theta (p.1.2 i))) ++
              [SmoothHeathBrownFactor.logarithm p.2]) n := by
                rw [hexpN, Finset.mul_sum]
      _ = _ := by
            apply Fintype.sum_congr
            intro p
            simp [smoothHeathBrownVonMangoldtComponent_apply,
              smoothHeathBrownVonMangoldtLabelFactors,
              dyadicBinomialCoefficient]
  calc
    ArithmeticFunction.vonMangoldt n =
        ∑ r : HeathBrownIndex,
          dyadicBinomialCoefficient r *
            (((truncatedMobius z ^ r.val *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) *
                (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) := hHB'
    _ = ∑ r : HeathBrownIndex,
          ∑ p : ((Fin r.val → SmoothHeathBrownScaleIndex X) ×
              (Fin (r.val - 1) → SmoothHeathBrownScaleIndex X)) ×
                SmoothHeathBrownScaleIndex X,
            smoothHeathBrownVonMangoldtComponent z ⟨r, p⟩ n := by
          apply Fintype.sum_congr
          intro r
          exact hterm r
    _ = ∑ ν : SmoothHeathBrownVonMangoldtLabel X,
          smoothHeathBrownVonMangoldtComponent z ν n := by
          simpa only [SmoothHeathBrownVonMangoldtLabel, Fintype.sum_sigma]

end

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownComponentCount
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusExpansion
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownVonMangoldtExpansion
