module
public import FractionalPrimes.Literature.Polynomial.PolynomialFullResidueFromScalarTasks
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalScalarInverseAssembly
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalSourceBoundDataAssembly
public import FractionalPrimes.Literature.MobiusToLong.UnitGlobalFromMobiusFactor
public import FractionalPrimes.Literature.Reciprocal.GlobalCharacterMobius
@[expose] public section

/-! The exact separate-maxima source package and its conditional integer/real
uniformity consequences.  This remains a traditional-import assembly root:
the LONG chain passes through the approved reciprocal modules. -/

noncomputable section

open Finset
open scoped BigOperators

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.MobiusToLong
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.Centres

/-- The first separate maximum in the source full-residue proposition,
over exactly `1 ≤ q ≤ (log X)^B` and the representatives `a < q`. -/
def ordinaryFullResidueMobiusMaximum (X H : ℕ) (B : ℝ) : ℝ :=
  (((longModuliRange X B).sup fun q =>
    (Finset.range q).sup fun a =>
      (⟨‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖,
        norm_nonneg _⟩ : NNReal)) : NNReal)

/-- The second separate maximum in the source full-residue proposition. -/
def ordinaryFullResidueLambdaCramerMaximum (X H : ℕ) (B : ℝ) : ℝ :=
  (((longModuliRange X B).sup fun q =>
    (Finset.range q).sup fun a =>
      (⟨‖residuePrefixSum X H q a (fun n =>
          (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖,
        norm_nonneg _⟩ : NNReal)) : NNReal)

/-- The exact sum-of-two-separate-maxima conclusion in
`lup:full-residue-of-analytic`. -/
def ordinaryFullResidueBoundsTask : Prop :=
  ∀ A B η : ℝ, 0 < A → 0 < B → 0 < η → η < 3 / 16 →
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ X H : ℕ, 3 ≤ X →
        (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
        (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
          ordinaryFullResidueMobiusMaximum X H B +
            ordinaryFullResidueLambdaCramerMaximum X H B ≤
              C_F * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ)

private theorem ordinaryFullResidueMobiusMaximum_le_of_pointwise
    (X H : ℕ) (B M : ℝ) (hM : 0 ≤ M)
    (hpoint : ∀ q, q ∈ longModuliRange X B → ∀ a, a < q →
      ‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖ ≤ M) :
    ordinaryFullResidueMobiusMaximum X H B ≤ M := by
  have hsup :
      ((longModuliRange X B).sup fun q =>
        (Finset.range q).sup fun a =>
          (⟨‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖,
            norm_nonneg _⟩ : NNReal)) ≤ (⟨M, hM⟩ : NNReal) := by
    apply Finset.sup_le
    intro q hq
    apply Finset.sup_le
    intro a ha
    exact_mod_cast hpoint q hq a (Finset.mem_range.mp ha)
  unfold ordinaryFullResidueMobiusMaximum
  exact_mod_cast hsup

private theorem ordinaryFullResidueLambdaCramerMaximum_le_of_pointwise
    (X H : ℕ) (B M : ℝ) (hM : 0 ≤ M)
    (hpoint : ∀ q, q ∈ longModuliRange X B → ∀ a, a < q →
      ‖residuePrefixSum X H q a (fun n =>
        (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤ M) :
    ordinaryFullResidueLambdaCramerMaximum X H B ≤ M := by
  have hsup :
      ((longModuliRange X B).sup fun q =>
        (Finset.range q).sup fun a =>
          (⟨‖residuePrefixSum X H q a (fun n =>
              (paperLambda n : ℂ) -
                (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖,
            norm_nonneg _⟩ : NNReal)) ≤ (⟨M, hM⟩ : NNReal) := by
    apply Finset.sup_le
    intro q hq
    apply Finset.sup_le
    intro a ha
    exact_mod_cast hpoint q hq a (Finset.mem_range.mp ha)
  unfold ordinaryFullResidueLambdaCramerMaximum
  exact_mod_cast hsup

private theorem ordinaryFullResidueMobius_le_max
    (X H q a : ℕ) (B : ℝ) (hq : 1 ≤ q)
    (hqB : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B) (ha : a < q) :
    ‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖ ≤
      ordinaryFullResidueMobiusMaximum X H B := by
  have hqmem : q ∈ longModuliRange X B :=
    (mem_longModuliRange_iff).2 ⟨hq, hqB⟩
  have hinner := Finset.le_sup
    (f := fun a =>
      (⟨‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖,
        norm_nonneg _⟩ : NNReal))
    (Finset.mem_range.mpr ha)
  have houter := Finset.le_sup
    (f := fun q =>
      (Finset.range q).sup fun a =>
        (⟨‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖,
          norm_nonneg _⟩ : NNReal)) hqmem
  unfold ordinaryFullResidueMobiusMaximum
  exact_mod_cast le_trans hinner houter

private theorem ordinaryFullResidueLambdaCramer_le_max
    (X H q a : ℕ) (B : ℝ) (hq : 1 ≤ q)
    (hqB : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B) (ha : a < q) :
    ‖residuePrefixSum X H q a (fun n =>
      (paperLambda n : ℂ) -
        (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
      ordinaryFullResidueLambdaCramerMaximum X H B := by
  have hqmem : q ∈ longModuliRange X B :=
    (mem_longModuliRange_iff).2 ⟨hq, hqB⟩
  have hinner := Finset.le_sup
    (f := fun a =>
      (⟨‖residuePrefixSum X H q a (fun n =>
          (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖,
        norm_nonneg _⟩ : NNReal))
    (Finset.mem_range.mpr ha)
  have houter := Finset.le_sup
    (f := fun q =>
      (Finset.range q).sup fun a =>
        (⟨‖residuePrefixSum X H q a (fun n =>
            (paperLambda n : ℂ) -
              (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖,
          norm_nonneg _⟩ : NNReal)) hqmem
  unfold ordinaryFullResidueLambdaCramerMaximum
  exact_mod_cast le_trans hinner houter

/-- The source-facing `fullResidueBoundOfScalarTasks`: LONG and the exact
scalar DP contract give the sum of the two separate residue maxima. The
constant is twice the checked uniform per-class constant, accounting for
the source's separate maxima. -/
theorem fullResidueBoundOfScalarTasks
    (hLONG : LongGlobalProperty)
    (hDP : shortIntervalDirichletTask) :
    ordinaryFullResidueBoundsTask := by
  intro A B η hA hB hη hηmax
  obtain ⟨C, hC, hpoint⟩ :=
    ordinaryFullResidueCancellation_of_LONG_DP hLONG hDP
      A B η hA hB hη hηmax
  let C_F : ℝ := 2 * C
  refine ⟨C_F, by dsimp [C_F]; positivity, ?_⟩
  intro X H hX hHlower hHupper
  let p : ℝ := (Real.log (X : ℝ)) ^ (-A : ℝ)
  let M : ℝ := C * (H : ℝ) * p
  have hp : 0 ≤ p := by
    dsimp [p]
    exact Real.rpow_nonneg (Real.log_nonneg (by
      have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      linarith)) _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMuMax := ordinaryFullResidueMobiusMaximum_le_of_pointwise
    X H B M hM (by
      intro q hqmem a ha
      have hq := (mem_longModuliRange_iff).1 hqmem
      have hpw := hpoint X H hX hHlower hHupper q hq.1 hq.2 a ha
      have hmuPair : ‖residuePrefixSum X H q a
          (fun n => (paperMu n : ℂ))‖ ≤
            ‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖ +
              ‖residuePrefixSum X H q a (fun n =>
                (paperLambda n : ℂ) -
                  (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ :=
        le_add_of_nonneg_right (norm_nonneg _)
      have hmu : ‖residuePrefixSum X H q a
          (fun n => (paperMu n : ℂ))‖ ≤ C * (H : ℝ) * p :=
        le_trans hmuPair hpw
      simpa [M, p] using hmu)
  have hLambdaMax := ordinaryFullResidueLambdaCramerMaximum_le_of_pointwise
    X H B M hM (by
      intro q hqmem a ha
      have hq := (mem_longModuliRange_iff).1 hqmem
      have hpw := hpoint X H hX hHlower hHupper q hq.1 hq.2 a ha
      have hlamPair : ‖residuePrefixSum X H q a (fun n =>
          (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
          ‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖ +
            ‖residuePrefixSum X H q a (fun n =>
              (paperLambda n : ℂ) -
                (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ :=
        le_add_of_nonneg_left (norm_nonneg _)
      have hlam : ‖residuePrefixSum X H q a (fun n =>
          (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤ C * (H : ℝ) * p :=
        le_trans hlamPair hpw
      simpa [M, p] using hlam)
  calc
    ordinaryFullResidueMobiusMaximum X H B +
        ordinaryFullResidueLambdaCramerMaximum X H B ≤ M + M :=
      add_le_add hMuMax hLambdaMax
    _ = C_F * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
      dsimp [C_F, M, p]
      ring

private theorem ordinaryFullResidueCancellation_of_fullResidueBounds
    (hFull : ordinaryFullResidueBoundsTask) :
    ordinaryFullResidueCancellationTask := by
  intro A B η hA hB hη hηmax
  obtain ⟨C_F, hC_F, hFullBound⟩ := hFull A B η hA hB hη hηmax
  refine ⟨C_F, hC_F, ?_⟩
  intro X H hX hHlower hHupper q hq hqB a ha
  have hMuPoint := ordinaryFullResidueMobius_le_max X H q a B hq hqB ha
  have hLambdaPoint := ordinaryFullResidueLambdaCramer_le_max
    X H q a B hq hqB ha
  have hFullX := hFullBound X H hX hHlower hHupper
  calc
    _ ≤ ordinaryFullResidueMobiusMaximum X H B +
        ordinaryFullResidueLambdaCramerMaximum X H B :=
      add_le_add hMuPoint hLambdaPoint
    _ ≤ C_F * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := hFullX

/-- The source `prefixBoundsOfFullResidueBounds` implication: separate
ordinary full-residue maxima yield the prefix major-arc task. -/
theorem prefixBoundsOfFullResidueBounds
    (hFull : ordinaryFullResidueBoundsTask) : polynomialMajorArcTask :=
  polynomialMajorArcTask_of_ordinaryFullResidueCancellation
    (ordinaryFullResidueCancellation_of_fullResidueBounds hFull)

/-- The source-exact LONG+DP-to-PMA theorem, routed through the separate
maxima proposition and its prefix consequence. -/
theorem polynomialMajorArcTask_of_LONG_DP_source
    (hLONG : LongGlobalProperty)
    (hDP : shortIntervalDirichletTask) : polynomialMajorArcTask :=
  prefixBoundsOfFullResidueBounds (fullResidueBoundOfScalarTasks hLONG hDP)

/-- MUF supplies LONG; together with the still-explicit scalar DP task this
gives the exact source PMA contract through the separate-maxima wrappers. -/
theorem polynomialMajorArcTask_of_MUF_and_DP
    (hMUF : MobiusUniformity)
    (hDP : shortIntervalDirichletTask) : polynomialMajorArcTask := by
  have hLONG : LongGlobalProperty :=
    longOfUnitGlobal (unitGlobalProperty_of_MUF hMUF)
  exact polynomialMajorArcTask_of_LONG_DP_source hLONG hDP

/-- Conditional integer uniformity with exactly the remaining source inputs
MUF, scalar DP, and the selected/restricted PTW contract. The global scalar
inverse task is discharged by the checked `scalarInverseClauses` assembly. -/
theorem conditionalIntegerUniformityOf_MUF_DP_PTW
    (hMUF : MobiusUniformity)
    (hDP : shortIntervalDirichletTask)
    (hPTW : restrictedPolynomialTwistedTask)
    (d : ℕ) (A η : ℝ) (hA : 0 < A) (hη : 0 < η)
    (hηmax : η < 3 / 16) :
    ∃ C : ℝ, 0 < C ∧
      ∀ X H : ℕ, 3 ≤ X →
        (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
        (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
        ∀ P : Polynomial ℝ, P.natDegree ≤ d →
          ‖∑ n ∈ Finset.Ioc X (X + H),
              (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
            ‖∑ n ∈ Finset.Ioc X (X + H),
              ((paperLambda (n : ℤ) : ℂ) -
                (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
                unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
            C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  exact conditionalIntegerUniformityOfPMAandPTW d A η hA hη hηmax
    (polynomialMajorArcTask_of_MUF_and_DP hMUF hDP) hPTW

/-- Conditional real-centred uniformity with exactly the remaining source
inputs MUF, scalar DP, and selected/restricted PTW. Quantifiers and the
location-dependent Cramér model are those of `lc:integer-to-real`. -/
theorem conditionalRealUniformityOf_MUF_DP_PTW
    (hMUF : MobiusUniformity)
    (hDP : shortIntervalDirichletTask)
    (hPTW : restrictedPolynomialTwistedTask)
    (k : ℕ) (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε)
    (hεtop : ε < 3 / 16) :
    ∃ Cint : ℝ, 0 < Cint ∧
      ∀ P : Polynomial ℝ, P.natDegree ≤ k →
        ∀ X H : ℝ, 3 ≤ X → X ^ (5 / 8 + ε) ≤ H →
          H ≤ X ^ (1 - ε) →
            ‖∑ n ∈ realIntegerInterval X H,
                (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
              ‖realCenterLambdaModelPhaseSum P X H‖ ≤
              integerToRealUniformityConstant A ε Cint * H *
                (Real.log X) ^ (-A : ℝ) := by
  exact conditionalRealUniformityOfPMAandPTW k A hA
    (polynomialMajorArcTask_of_MUF_and_DP hMUF hDP) hPTW ε hε hεtop

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.fullResidueBoundOfScalarTasks
#print axioms FractionalPrimes.Literature.Polynomial.prefixBoundsOfFullResidueBounds
#print axioms FractionalPrimes.Literature.Polynomial.polynomialMajorArcTask_of_LONG_DP_source
#print axioms FractionalPrimes.Literature.Polynomial.polynomialMajorArcTask_of_MUF_and_DP
#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerUniformityOf_MUF_DP_PTW
#print axioms FractionalPrimes.Literature.Polynomial.conditionalRealUniformityOf_MUF_DP_PTW
