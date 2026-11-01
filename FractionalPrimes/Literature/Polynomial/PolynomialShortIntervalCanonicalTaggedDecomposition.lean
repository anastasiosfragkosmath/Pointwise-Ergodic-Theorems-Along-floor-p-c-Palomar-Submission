module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalP3SourceInstantiation
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTaggedComponentAPI
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWTaggedComponentAPI
public import Mathlib.Tactic

/-! Canonical elementary-type decompositions and original dyadic-label
provenance from the outer source decomposition. The upstream branch package
is Prop-valued, so we choose a tag only after proving that some tag has the
corresponding source evidence. No twisted-prefix estimate is attached here. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.DirichletMean
open scoped BigOperators

namespace FractionalPrimes.Literature.Polynomial

/-- A tagged package propositionally supplies a compatible designation.
This existential is eliminated by classical choice below; we do not
priority-test the potentially overlapping arithmetic predicates. -/
theorem exists_restrictedPTWDesignationEvidence_of_taggedPackage
    {X : ℝ} {z c : ℝ} {f : ComplexPositiveIntegerFunction}
    {fs : List (DyadicArithmeticFactor X)} {α : Fin fs.length → ℝ}
    (hα : ∀ i, 0 ≤ α i)
    (hsum : ∑ i, α i = 1)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (hmob : ∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ))
    (branch : largeDyadicComponentTaggedPackage z c
      (decompositionDelta X) f fs α) :
    ∃ tag : Fin 3, restrictedPTWDesignationEvidence X f tag := by
  rcases branch with hI | hI2 | ⟨hII, hstrict⟩
  · exact ⟨0, by simpa [restrictedPTWDesignationEvidence] using hI⟩
  · exact ⟨1, by simpa [restrictedPTWDesignationEvidence] using hI2⟩
  · refine ⟨2, ?_⟩
    simpa [restrictedPTWDesignationEvidence] using
      (show ∃ (z' c' : ℝ) (fs' : List (DyadicArithmeticFactor X))
          (α' : Fin fs'.length → ℝ),
          (∀ i, 0 ≤ α' i) ∧ (∑ i, α' i = 1) ∧
          (∀ i,
            normalizedExponentConstant⁻¹ * X ^ α' i ≤
                dyadicFactorScale (fs'.get i) ∧
              dyadicFactorScale (fs'.get i) ≤
                normalizedExponentConstant * X ^ α' i) ∧
          (∀ i j, fs'.get i = .mobius j → α' i ≤ (1 / 8 : ℝ)) ∧
          largeTypeIIDyadicComponentData z' c' (decompositionDelta X)
            f fs' α' ∧ (∀ i, α' i < (3 / 8 : ℝ)) from
        ⟨z, c, fs, α, hα, hsum, hscale, hmob, hII, hstrict⟩)

/-- Stronger source-alignment version of the designation existence lemma.
If tag 2 is chosen, the certificate is the very type-II datum and strict
exponent cap carried by this tagged package, with the same `z`, `c`, `fs`,
and `α`. -/
theorem exists_restrictedPTWDesignationEvidence_aligned_of_taggedPackage
    {X : ℝ} {z c : ℝ} {f : ComplexPositiveIntegerFunction}
    {fs : List (DyadicArithmeticFactor X)} {α : Fin fs.length → ℝ}
    (hα : ∀ i, 0 ≤ α i)
    (hsum : ∑ i, α i = 1)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (hmob : ∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ))
    (branch : largeDyadicComponentTaggedPackage z c
      (decompositionDelta X) f fs α) :
    ∃ tag : Fin 3,
      restrictedPTWDesignationEvidence X f tag ∧
      (tag.val = 2 →
        largeTypeIIDyadicComponentData z c (decompositionDelta X) f fs α ∧
          ∀ i, α i < (3 / 8 : ℝ)) := by
  rcases branch with hI | hI2 | ⟨hII, hstrict⟩
  · refine ⟨0, ?_, ?_⟩
    · simpa [restrictedPTWDesignationEvidence] using hI
    · intro htag
      norm_num at htag
  · refine ⟨1, ?_, ?_⟩
    · simpa [restrictedPTWDesignationEvidence] using hI2
    · intro htag
      norm_num at htag
  · refine ⟨2, ?_, ?_⟩
    · simpa [restrictedPTWDesignationEvidence] using
        (show ∃ (z' c' : ℝ) (fs' : List (DyadicArithmeticFactor X))
            (α' : Fin fs'.length → ℝ),
            (∀ i, 0 ≤ α' i) ∧ (∑ i, α' i = 1) ∧
            (∀ i,
              normalizedExponentConstant⁻¹ * X ^ α' i ≤
                  dyadicFactorScale (fs'.get i) ∧
                dyadicFactorScale (fs'.get i) ≤
                  normalizedExponentConstant * X ^ α' i) ∧
            (∀ i j, fs'.get i = .mobius j → α' i ≤ (1 / 8 : ℝ)) ∧
            largeTypeIIDyadicComponentData z' c' (decompositionDelta X)
              f fs' α' ∧ (∀ i, α' i < (3 / 8 : ℝ)) from
          ⟨z, c, fs, α, hα, hsum, hscale, hmob, hII, hstrict⟩)
    · intro _
      exact ⟨hII, hstrict⟩

/-- A canonical source-tagged Möbius decomposition. Its index is the exact
dyadic label; `component_eq_raw` exposes the coefficient source needed by
the short-prefix mass estimate. -/
structure SelectedMobiusPTWCanonicalTaggedDecomposition (X : ℝ) where
  outer : SelectedMobiusPTWTaggedOuterDecomposition X
  elementary : ElementaryArithmeticTypeDecomposition X mobiusComplexPositiveFunction
  label : elementary.Index → MobiusDyadicLabel X
  label_mem : ∀ i, i ∈ elementary.indices →
    label i ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)
  label_injective : Function.Injective label
  label_surjective : ∀ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
    ∃ i, i ∈ elementary.indices ∧ label i = ν
  component_eq_raw : ∀ i (_hi : i ∈ elementary.indices),
    elementary.component i = selectedMobiusPTWRawDyadicComponent (label i)
  designationTag : ∀ i (_hi : i ∈ elementary.indices), Fin 3
  designationEvidence : ∀ i (hi : i ∈ elementary.indices),
    restrictedPTWDesignationEvidence X
      (elementary.component i) (designationTag i hi)
  designationTagIIAlignment : ∀ i (hi : i ∈ elementary.indices),
    (designationTag i hi).val = 2 →
      let data := Classical.choice
        (outer.taggedComponent (label i) (label_mem i hi))
      largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient (label i).1) (decompositionDelta X)
        (selectedMobiusPTWRawDyadicComponent (label i))
        (mobiusLabelFactors (label i)) data.exponents ∧
        ∀ j, data.exponents j < (3 / 8 : ℝ)

/-- A canonical source-tagged von Mangoldt decomposition, parallel to the
Möbius package and retaining its literal dyadic label in each component. -/
structure SelectedVonMangoldtPTWCanonicalTaggedDecomposition (X : ℝ) where
  outer : SelectedVonMangoldtPTWTaggedOuterDecomposition X
  elementary : ElementaryArithmeticTypeDecomposition X vonMangoldtComplexPositiveFunction
  label : elementary.Index → VonMangoldtDyadicLabel X
  label_mem : ∀ i, i ∈ elementary.indices →
    label i ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)
  label_injective : Function.Injective label
  label_surjective : ∀ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
    ∃ i, i ∈ elementary.indices ∧ label i = ν
  component_eq_raw : ∀ i (_hi : i ∈ elementary.indices),
    elementary.component i = selectedVonMangoldtPTWRawDyadicComponent (label i)
  designationTag : ∀ i (_hi : i ∈ elementary.indices), Fin 3
  designationEvidence : ∀ i (hi : i ∈ elementary.indices),
    restrictedPTWDesignationEvidence X
      (elementary.component i) (designationTag i hi)
  designationTagIIAlignment : ∀ i (hi : i ∈ elementary.indices),
    (designationTag i hi).val = 2 →
      let data := Classical.choice
        (outer.taggedComponent (label i) (label_mem i hi))
      largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient (label i).1) (decompositionDelta X)
        (selectedVonMangoldtPTWRawDyadicComponent (label i))
        (vonMangoldtLabelFactors (label i)) data.exponents ∧
        ∀ j, data.exponents j < (3 / 8 : ℝ)

noncomputable def selectedMobiusDataOfOuter
    {X : ℝ} (outer : SelectedMobiusPTWTaggedOuterDecomposition X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)) :
    SelectedMobiusPTWTaggedComponentData ν :=
  Classical.choice (outer.taggedComponent ν hν)

noncomputable def selectedVonMangoldtDataOfOuter
    {X : ℝ} (outer : SelectedVonMangoldtPTWTaggedOuterDecomposition X)
    (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) :
    SelectedVonMangoldtPTWTaggedComponentData ν :=
  Classical.choice (outer.taggedComponent ν hν)

/-- The source-tagged Möbius package supplies a designation for its literal
raw component. The returned witness retains the strict type-II exponent cap
whenever tag 2 is selected. -/
theorem exists_selectedMobiusPTWDesignationOfData
    {X : ℝ} {ν : MobiusDyadicLabel X}
    (data : SelectedMobiusPTWTaggedComponentData ν) :
    ∃ tag : Fin 3, restrictedPTWDesignationEvidence X
      (selectedMobiusPTWRawDyadicComponent ν) tag := by
  let sourceComponent : ComplexPositiveIntegerFunction := fun n =>
    ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)
  have hcomponent : sourceComponent = selectedMobiusPTWRawDyadicComponent ν := by
    funext n
    rfl
  rcases exists_restrictedPTWDesignationEvidence_of_taggedPackage
      (X := X) (z := dyadicMobiusCutoff X)
      (c := dyadicBinomialCoefficient ν.1)
      (f := sourceComponent) (fs := mobiusLabelFactors ν)
      (α := data.exponents)
      data.nonnegative data.sum_one data.scale_bounds
      data.mobius_exponent_bound
      (by simpa [sourceComponent] using data.branch) with ⟨tag, htag⟩
  exact ⟨tag, hcomponent ▸ htag⟩

/-- Strong source-alignment theorem for the selected Möbius datum: whenever
tag 2 is selected, its type-II data and strict cap use this exact datum's
factor list and exponent vector. -/
theorem exists_selectedMobiusPTWDesignationAlignmentOfData
    {X : ℝ} {ν : MobiusDyadicLabel X}
    (data : SelectedMobiusPTWTaggedComponentData ν) :
    ∃ tag : Fin 3,
      restrictedPTWDesignationEvidence X
        (selectedMobiusPTWRawDyadicComponent ν) tag ∧
      (tag.val = 2 →
        largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
          (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
          (selectedMobiusPTWRawDyadicComponent ν)
          (mobiusLabelFactors ν) data.exponents ∧
          ∀ i, data.exponents i < (3 / 8 : ℝ)) := by
  let sourceComponent : ComplexPositiveIntegerFunction := fun n =>
    ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)
  have hcomponent : sourceComponent = selectedMobiusPTWRawDyadicComponent ν := by
    funext n
    rfl
  rcases exists_restrictedPTWDesignationEvidence_aligned_of_taggedPackage
      (X := X) (z := dyadicMobiusCutoff X)
      (c := dyadicBinomialCoefficient ν.1)
      (f := sourceComponent) (fs := mobiusLabelFactors ν)
      (α := data.exponents)
      data.nonnegative data.sum_one data.scale_bounds
      data.mobius_exponent_bound
      (by simpa [sourceComponent] using data.branch) with
      ⟨tag, hevidence, halignment⟩
  refine ⟨tag, hcomponent ▸ hevidence, ?_⟩
  intro htag
  exact hcomponent ▸ halignment htag

/-- Strong source-alignment theorem for the selected von Mangoldt datum. -/
theorem exists_selectedVonMangoldtPTWDesignationAlignmentOfData
    {X : ℝ} {ν : VonMangoldtDyadicLabel X}
    (data : SelectedVonMangoldtPTWTaggedComponentData ν) :
    ∃ tag : Fin 3,
      restrictedPTWDesignationEvidence X
        (selectedVonMangoldtPTWRawDyadicComponent ν) tag ∧
      (tag.val = 2 →
        largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
          (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
          (selectedVonMangoldtPTWRawDyadicComponent ν)
          (vonMangoldtLabelFactors ν) data.exponents ∧
          ∀ i, data.exponents i < (3 / 8 : ℝ)) := by
  let sourceComponent : ComplexPositiveIntegerFunction := fun n =>
    ((vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)
  have hcomponent : sourceComponent = selectedVonMangoldtPTWRawDyadicComponent ν := by
    funext n
    rfl
  rcases exists_restrictedPTWDesignationEvidence_aligned_of_taggedPackage
      (X := X) (z := dyadicMobiusCutoff X)
      (c := dyadicBinomialCoefficient ν.1)
      (f := sourceComponent) (fs := vonMangoldtLabelFactors ν)
      (α := data.exponents)
      data.nonnegative data.sum_one data.scale_bounds
      data.mobius_exponent_bound
      (by simpa [sourceComponent] using data.branch) with
      ⟨tag, hevidence, halignment⟩
  refine ⟨tag, hcomponent ▸ hevidence, ?_⟩
  intro htag
  exact hcomponent ▸ halignment htag

noncomputable def selectedMobiusPTWDesignationTagOfData
    {X : ℝ} {ν : MobiusDyadicLabel X}
    (data : SelectedMobiusPTWTaggedComponentData ν) : Fin 3 :=
  Classical.choose (exists_selectedMobiusPTWDesignationAlignmentOfData data)

theorem selectedMobiusPTWDesignationTagOfData_spec
    {X : ℝ} {ν : MobiusDyadicLabel X}
    (data : SelectedMobiusPTWTaggedComponentData ν) :
    restrictedPTWDesignationEvidence X
      (selectedMobiusPTWRawDyadicComponent ν)
      (selectedMobiusPTWDesignationTagOfData data) :=
  (Classical.choose_spec
    (exists_selectedMobiusPTWDesignationAlignmentOfData data)).1

theorem selectedMobiusPTWDesignationTagOfData_alignment_spec
    {X : ℝ} {ν : MobiusDyadicLabel X}
    (data : SelectedMobiusPTWTaggedComponentData ν) :
    (selectedMobiusPTWDesignationTagOfData data).val = 2 →
      largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (selectedMobiusPTWRawDyadicComponent ν)
        (mobiusLabelFactors ν) data.exponents ∧
        ∀ i, data.exponents i < (3 / 8 : ℝ) :=
  (Classical.choose_spec
    (exists_selectedMobiusPTWDesignationAlignmentOfData data)).2

/-- The corresponding source-valid designation for a Möbius outer label. -/
noncomputable def selectedMobiusPTWDesignationTagOfOuter
    {X : ℝ} (outer : SelectedMobiusPTWTaggedOuterDecomposition X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)) : Fin 3 :=
  selectedMobiusPTWDesignationTagOfData (selectedMobiusDataOfOuter outer ν hν)

theorem selectedMobiusPTWDesignationTagOfOuter_spec
    {X : ℝ} (outer : SelectedMobiusPTWTaggedOuterDecomposition X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)) :
    restrictedPTWDesignationEvidence X (selectedMobiusPTWRawDyadicComponent ν)
      (selectedMobiusPTWDesignationTagOfOuter outer ν hν) :=
  selectedMobiusPTWDesignationTagOfData_spec (selectedMobiusDataOfOuter outer ν hν)

/-- The source-tagged von Mangoldt package supplies a designation for its
literal raw component, retaining the strict type-II exponent cap. -/
theorem exists_selectedVonMangoldtPTWDesignationOfData
    {X : ℝ} {ν : VonMangoldtDyadicLabel X}
    (data : SelectedVonMangoldtPTWTaggedComponentData ν) :
    ∃ tag : Fin 3, restrictedPTWDesignationEvidence X
      (selectedVonMangoldtPTWRawDyadicComponent ν) tag := by
  let sourceComponent : ComplexPositiveIntegerFunction := fun n =>
    ((vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)
  have hcomponent : sourceComponent = selectedVonMangoldtPTWRawDyadicComponent ν := by
    funext n
    rfl
  rcases exists_restrictedPTWDesignationEvidence_of_taggedPackage
      (X := X) (z := dyadicMobiusCutoff X)
      (c := dyadicBinomialCoefficient ν.1)
      (f := sourceComponent) (fs := vonMangoldtLabelFactors ν)
      (α := data.exponents)
      data.nonnegative data.sum_one data.scale_bounds
      data.mobius_exponent_bound
      (by simpa [sourceComponent] using data.branch) with ⟨tag, htag⟩
  exact ⟨tag, hcomponent ▸ htag⟩

noncomputable def selectedVonMangoldtPTWDesignationTagOfData
    {X : ℝ} {ν : VonMangoldtDyadicLabel X}
    (data : SelectedVonMangoldtPTWTaggedComponentData ν) : Fin 3 :=
  Classical.choose
    (exists_selectedVonMangoldtPTWDesignationAlignmentOfData data)

theorem selectedVonMangoldtPTWDesignationTagOfData_spec
    {X : ℝ} {ν : VonMangoldtDyadicLabel X}
    (data : SelectedVonMangoldtPTWTaggedComponentData ν) :
    restrictedPTWDesignationEvidence X
      (selectedVonMangoldtPTWRawDyadicComponent ν)
      (selectedVonMangoldtPTWDesignationTagOfData data) :=
  (Classical.choose_spec
    (exists_selectedVonMangoldtPTWDesignationAlignmentOfData data)).1

theorem selectedVonMangoldtPTWDesignationTagOfData_alignment_spec
    {X : ℝ} {ν : VonMangoldtDyadicLabel X}
    (data : SelectedVonMangoldtPTWTaggedComponentData ν) :
    (selectedVonMangoldtPTWDesignationTagOfData data).val = 2 →
      largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (selectedVonMangoldtPTWRawDyadicComponent ν)
        (vonMangoldtLabelFactors ν) data.exponents ∧
        ∀ i, data.exponents i < (3 / 8 : ℝ) :=
  (Classical.choose_spec
    (exists_selectedVonMangoldtPTWDesignationAlignmentOfData data)).2

/-- The corresponding source-valid designation for a von Mangoldt outer
label. -/
noncomputable def selectedVonMangoldtPTWDesignationTagOfOuter
    {X : ℝ} (outer : SelectedVonMangoldtPTWTaggedOuterDecomposition X)
    (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) : Fin 3 :=
  selectedVonMangoldtPTWDesignationTagOfData
    (selectedVonMangoldtDataOfOuter outer ν hν)

theorem selectedVonMangoldtPTWDesignationTagOfOuter_spec
    {X : ℝ} (outer : SelectedVonMangoldtPTWTaggedOuterDecomposition X)
    (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) :
    restrictedPTWDesignationEvidence X
      (selectedVonMangoldtPTWRawDyadicComponent ν)
      (selectedVonMangoldtPTWDesignationTagOfOuter outer ν hν) :=
  selectedVonMangoldtPTWDesignationTagOfData_spec
    (selectedVonMangoldtDataOfOuter outer ν hν)

/-- Project the tagged Möbius outer decomposition to the exact elementary
type decomposition while retaining labels and source-selected branch data. -/
noncomputable def selectedMobiusPTWCanonicalTaggedDecompositionOfOuter
    {X : ℝ} (outer : SelectedMobiusPTWTaggedOuterDecomposition X) :
    SelectedMobiusPTWCanonicalTaggedDecomposition X := by
  let labels := mobiusDyadicLabels X (dyadicMobiusCutoff X)
  let raw : MobiusDyadicLabel X → ComplexPositiveIntegerFunction :=
    selectedMobiusPTWRawDyadicComponent
  let E : ElementaryArithmeticTypeDecomposition X mobiusComplexPositiveFunction :=
    { Index := MobiusDyadicLabel X
      indices := labels
      component := raw
      decomposition := by
        intro n hnlo hnhi
        simpa [labels, raw] using outer.decomposition n hnlo hnhi
      componentType := by
        intro ν hν
        let data := selectedMobiusDataOfOuter outer ν (by simpa [labels] using hν)
        rcases data.branch with hI | hI2 | ⟨hII, _hstrict⟩
        · exact Or.inl hI
        · exact Or.inr (Or.inl hI2)
        · exact Or.inr (Or.inr ⟨dyadicMobiusCutoff X,
            dyadicBinomialCoefficient ν.1, mobiusLabelFactors ν,
            data.exponents, data.nonnegative, data.sum_one,
            data.scale_bounds, data.mobius_exponent_bound, hII⟩)
      count := by simpa [labels] using outer.count }
  refine
    { outer := outer
      elementary := E
      label := fun ν => ν
      label_mem := ?_
      label_injective := ?_
      label_surjective := ?_
      component_eq_raw := ?_
      designationTag := ?_
      designationEvidence := ?_
      designationTagIIAlignment := ?_ }
  · intro ν hν
    exact hν
  · intro ν μ h
    exact h
  · intro ν hν
    exact ⟨ν, hν, rfl⟩
  · intro ν hν
    rfl
  · intro ν hν
    exact selectedMobiusPTWDesignationTagOfOuter outer ν (by simpa [labels] using hν)
  · intro ν hν
    change restrictedPTWDesignationEvidence X
      (selectedMobiusPTWRawDyadicComponent ν)
      (selectedMobiusPTWDesignationTagOfOuter outer ν
        (by simpa [labels] using hν))
    exact selectedMobiusPTWDesignationTagOfOuter_spec outer ν
      (by simpa [labels] using hν)
  · intro ν hν htag
    let hν' : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X) := by
      simpa [labels] using hν
    let data := selectedMobiusDataOfOuter outer ν hν'
    change largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
      (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
      (selectedMobiusPTWRawDyadicComponent ν) (mobiusLabelFactors ν)
      data.exponents ∧ ∀ j, data.exponents j < (3 / 8 : ℝ)
    have htagData : (selectedMobiusPTWDesignationTagOfData data).val = 2 := by
      change (selectedMobiusPTWDesignationTagOfOuter outer ν hν').val = 2
      exact htag
    exact selectedMobiusPTWDesignationTagOfData_alignment_spec data htagData

/-- Project the tagged von Mangoldt outer decomposition to the exact
elementary type decomposition while retaining labels and source-selected
branch data. -/
noncomputable def selectedVonMangoldtPTWCanonicalTaggedDecompositionOfOuter
    {X : ℝ} (outer : SelectedVonMangoldtPTWTaggedOuterDecomposition X) :
    SelectedVonMangoldtPTWCanonicalTaggedDecomposition X := by
  let labels := vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)
  let raw : VonMangoldtDyadicLabel X → ComplexPositiveIntegerFunction :=
    selectedVonMangoldtPTWRawDyadicComponent
  let E : ElementaryArithmeticTypeDecomposition X vonMangoldtComplexPositiveFunction :=
    { Index := VonMangoldtDyadicLabel X
      indices := labels
      component := raw
      decomposition := by
        intro n hnlo hnhi
        simpa [labels, raw] using outer.decomposition n hnlo hnhi
      componentType := by
        intro ν hν
        let data := selectedVonMangoldtDataOfOuter outer ν
          (by simpa [labels] using hν)
        rcases data.branch with hI | hI2 | ⟨hII, _hstrict⟩
        · exact Or.inl hI
        · exact Or.inr (Or.inl hI2)
        · exact Or.inr (Or.inr ⟨dyadicMobiusCutoff X,
            dyadicBinomialCoefficient ν.1, vonMangoldtLabelFactors ν,
            data.exponents, data.nonnegative, data.sum_one,
            data.scale_bounds, data.mobius_exponent_bound, hII⟩)
      count := by simpa [labels] using outer.count }
  refine
    { outer := outer
      elementary := E
      label := fun ν => ν
      label_mem := ?_
      label_injective := ?_
      label_surjective := ?_
      component_eq_raw := ?_
      designationTag := ?_
      designationEvidence := ?_
      designationTagIIAlignment := ?_ }
  · intro ν hν
    exact hν
  · intro ν μ h
    exact h
  · intro ν hν
    exact ⟨ν, hν, rfl⟩
  · intro ν hν
    rfl
  · intro ν hν
    exact selectedVonMangoldtPTWDesignationTagOfOuter outer ν
      (by simpa [labels] using hν)
  · intro ν hν
    change restrictedPTWDesignationEvidence X
      (selectedVonMangoldtPTWRawDyadicComponent ν)
      (selectedVonMangoldtPTWDesignationTagOfOuter outer ν
        (by simpa [labels] using hν))
    exact selectedVonMangoldtPTWDesignationTagOfOuter_spec outer ν
      (by simpa [labels] using hν)
  · intro ν hν htag
    let hν' : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X) := by
      simpa [labels] using hν
    let data := selectedVonMangoldtDataOfOuter outer ν hν'
    change largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
      (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
      (selectedVonMangoldtPTWRawDyadicComponent ν)
      (vonMangoldtLabelFactors ν) data.exponents ∧
      ∀ j, data.exponents j < (3 / 8 : ℝ)
    have htagData : (selectedVonMangoldtPTWDesignationTagOfData data).val = 2 := by
      change (selectedVonMangoldtPTWDesignationTagOfOuter outer ν hν').val = 2
      exact htag
    exact selectedVonMangoldtPTWDesignationTagOfData_alignment_spec data htagData

/-- Large-scale source selection for the Möbius weight, before attaching the
uniform-in-H,T prefix estimate. -/
theorem exists_selectedMobiusPTWCanonicalTaggedDecomposition
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X) :
    Nonempty (SelectedMobiusPTWCanonicalTaggedDecomposition X) := by
  rcases selectedMobiusPTW_taggedOuterDecomposition hXlarge with ⟨outer⟩
  exact ⟨selectedMobiusPTWCanonicalTaggedDecompositionOfOuter outer⟩

/-- Large-scale source selection for the von Mangoldt weight, before
attaching the uniform-in-H,T prefix estimate. -/
theorem exists_selectedVonMangoldtPTWCanonicalTaggedDecomposition
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X) :
    Nonempty (SelectedVonMangoldtPTWCanonicalTaggedDecomposition X) := by
  rcases selectedVonMangoldtPTW_taggedOuterDecomposition hXlarge with ⟨outer⟩
  exact ⟨selectedVonMangoldtPTWCanonicalTaggedDecompositionOfOuter outer⟩

#print axioms exists_restrictedPTWDesignationEvidence_of_taggedPackage
#print axioms exists_restrictedPTWDesignationEvidence_aligned_of_taggedPackage
#print axioms exists_selectedMobiusPTWDesignationAlignmentOfData
#print axioms exists_selectedVonMangoldtPTWDesignationAlignmentOfData
#print axioms selectedMobiusPTWDesignationTagOfData_spec
#print axioms selectedMobiusPTWDesignationTagOfData_alignment_spec
#print axioms selectedVonMangoldtPTWDesignationTagOfData_spec
#print axioms selectedVonMangoldtPTWDesignationTagOfData_alignment_spec
#print axioms selectedMobiusPTWCanonicalTaggedDecompositionOfOuter
#print axioms selectedVonMangoldtPTWCanonicalTaggedDecompositionOfOuter
#print axioms exists_selectedMobiusPTWCanonicalTaggedDecomposition
#print axioms exists_selectedVonMangoldtPTWCanonicalTaggedDecomposition

end FractionalPrimes.Literature.Polynomial

end
