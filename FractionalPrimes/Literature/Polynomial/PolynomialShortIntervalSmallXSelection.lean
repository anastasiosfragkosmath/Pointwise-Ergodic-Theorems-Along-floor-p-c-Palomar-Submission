module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalCanonicalTaggedDecomposition
public import Mathlib.Tactic

/-! Small-scale (`3 ≤ X < 2^120`) source selections for the restricted
twisted-prefix contract. The dyadic labels and annular decomposition remain
literal; each component is truncated only at the source support endpoint
`4X`, and its selected designation is type I. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.DirichletMean
open scoped BigOperators

namespace FractionalPrimes.Literature.Polynomial

private theorem cast_smallX_le {X : ℕ} (hXsmall : X < 2 ^ 120) :
    (X : ℝ) ≤ (2 : ℝ) ^ 120 := by
  have hnat : X ≤ 2 ^ 120 := Nat.le_of_lt hXsmall
  exact_mod_cast hnat

/-- Every truncated Möbius dyadic component is explicitly type I below the
source cutoff. -/
theorem mobiusSmallXComponent_typeI
    {X : ℕ} (hX : 3 ≤ X) (hXsmall : X < 2 ^ 120)
    (ν : MobiusDyadicLabel (X : ℝ)) :
    typeIFunction (decompositionDelta (X : ℝ))
      (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ))
      (truncatePositiveComponent (4 * (X : ℝ))
        (selectedMobiusPTWRawDyadicComponent ν)) := by
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hsmallReal : (X : ℝ) ≤ (2 : ℝ) ^ 120 := cast_smallX_le hXsmall
  have hgroup := truncatedRawDyadicComponent_typeI_explicit
    hXreal hsmallReal (dyadicMobiusCutoff (X : ℝ))
    (dyadicBinomialCoefficient ν.1) (mobiusLabelFactors ν)
    (mobiusLabelFactorCount ν) (dyadicBinomialCoefficient_abs_le ν.1)
  have hraw : selectedMobiusPTWRawDyadicComponent ν =
      groupedDyadicFactor (dyadicMobiusCutoff (X : ℝ))
        (dyadicBinomialCoefficient ν.1 : ℂ) (mobiusLabelFactors ν) := by
    funext n
    simp [selectedMobiusPTWRawDyadicComponent, groupedDyadicFactor,
      mobiusDyadicComponent_apply]
  rw [← hraw] at hgroup
  exact hgroup

/-- The small-(X) Möbius decomposition uses the exact dyadic label set and
the source's truncated raw component. On the annulus the truncation is
identically the raw component, so the source dyadic identity is unchanged. -/
noncomputable def mobiusSmallXElementaryTypeDecomposition
    (X : ℕ) (hX : 3 ≤ X) (hXsmall : X < 2 ^ 120) :
    ElementaryArithmeticTypeDecomposition (X : ℝ)
      mobiusComplexPositiveFunction := by
  let labels := mobiusDyadicLabels (X : ℝ) (dyadicMobiusCutoff (X : ℝ))
  let raw : MobiusDyadicLabel (X : ℝ) → ComplexPositiveIntegerFunction :=
    selectedMobiusPTWRawDyadicComponent
  let component : MobiusDyadicLabel (X : ℝ) → ComplexPositiveIntegerFunction :=
    fun ν => truncatePositiveComponent (4 * (X : ℝ)) (raw ν)
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  refine ⟨MobiusDyadicLabel (X : ℝ), labels, component, ?_, ?_, ?_⟩
  · intro n hnlo hnhi
    have hdecomp := mobiusDyadicDecomposition hXreal n.2 hnlo hnhi
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) hdecomp
    simpa [labels, raw, component, mobiusComplexPositiveFunction,
      selectedMobiusPTWRawDyadicComponent, truncatePositiveComponent,
      Complex.ofReal_sum, hnhi] using hcast
  · intro ν hν
    exact Or.inl (mobiusSmallXComponent_typeI hX hXsmall ν)
  · exact_mod_cast mobiusDyadicLabels_typeCount hXreal

/-- The small-(X) von Mangoldt dyadic components are explicitly type I. -/
theorem vonMangoldtSmallXComponent_typeI
    {X : ℕ} (hX : 3 ≤ X) (hXsmall : X < 2 ^ 120)
    (ν : VonMangoldtDyadicLabel (X : ℝ)) :
    typeIFunction (decompositionDelta (X : ℝ))
      (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ))
      (truncatePositiveComponent (4 * (X : ℝ))
        (selectedVonMangoldtPTWRawDyadicComponent ν)) := by
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hsmallReal : (X : ℝ) ≤ (2 : ℝ) ^ 120 := cast_smallX_le hXsmall
  have hgroup := truncatedRawDyadicComponent_typeI_explicit
    hXreal hsmallReal (dyadicMobiusCutoff (X : ℝ))
    (dyadicBinomialCoefficient ν.1) (vonMangoldtLabelFactors ν)
    (vonMangoldtLabelFactorCount ν) (dyadicBinomialCoefficient_abs_le ν.1)
  have hraw : selectedVonMangoldtPTWRawDyadicComponent ν =
      groupedDyadicFactor (dyadicMobiusCutoff (X : ℝ))
        (dyadicBinomialCoefficient ν.1 : ℂ) (vonMangoldtLabelFactors ν) := by
    funext n
    simp [selectedVonMangoldtPTWRawDyadicComponent, groupedDyadicFactor,
      vonMangoldtDyadicComponent_apply]
  rw [← hraw] at hgroup
  exact hgroup

/-- The small-(X) von Mangoldt decomposition retains its exact dyadic labels
and source annular decomposition. -/
noncomputable def vonMangoldtSmallXElementaryTypeDecomposition
    (X : ℕ) (hX : 3 ≤ X) (hXsmall : X < 2 ^ 120) :
    ElementaryArithmeticTypeDecomposition (X : ℝ)
      vonMangoldtComplexPositiveFunction := by
  let labels := vonMangoldtDyadicLabels (X : ℝ) (dyadicMobiusCutoff (X : ℝ))
  let raw : VonMangoldtDyadicLabel (X : ℝ) → ComplexPositiveIntegerFunction :=
    selectedVonMangoldtPTWRawDyadicComponent
  let component : VonMangoldtDyadicLabel (X : ℝ) → ComplexPositiveIntegerFunction :=
    fun ν => truncatePositiveComponent (4 * (X : ℝ)) (raw ν)
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  refine ⟨VonMangoldtDyadicLabel (X : ℝ), labels, component, ?_, ?_, ?_⟩
  · intro n hnlo hnhi
    have hdecomp := vonMangoldtDyadicDecomposition hXreal n.2 hnlo hnhi
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) hdecomp
    simpa [labels, raw, component, vonMangoldtComplexPositiveFunction,
      selectedVonMangoldtPTWRawDyadicComponent, truncatePositiveComponent,
      Complex.ofReal_sum, hnhi] using hcast
  · intro ν hν
    exact Or.inl (vonMangoldtSmallXComponent_typeI hX hXsmall ν)
  · exact_mod_cast vonMangoldtDyadicLabels_typeCount hXreal

def smallXTypeITag : Fin 3 := ⟨0, by decide⟩

/-- For `3 ≤ X < 2^120`, the Möbius source satisfies the full restricted
selection contract with the explicit type-I designation. The threshold
comparison `aStar ≤ a` is an input, while the twisted-prefix clause is true
because the designated tag is 0. -/
def mobiusSmallXRestrictedPTWSelection
    (X : ℕ) (hX : 3 ≤ X) (hXsmall : X < 2 ^ 120)
    (aStar a η Ctw : ℝ) (haStar : 1 ≤ aStar) (haStarLe : aStar ≤ a) :
    RestrictedPTWSelection X aStar a η Ctw mobiusComplexPositiveFunction := by
  let D := mobiusSmallXElementaryTypeDecomposition X hX hXsmall
  refine ⟨haStar, haStarLe, D, ?_, ?_, ?_⟩
  · intro i hi
    exact smallXTypeITag
  · intro i hi
    change typeIFunction (decompositionDelta (X : ℝ))
      (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ)) (D.component i)
    exact mobiusSmallXComponent_typeI hX hXsmall i
  · intro H hHlower hHupper i hi
    simp [restrictedPTWDesignatedPrefixConclusion, smallXTypeITag]

/-- The corresponding von Mangoldt small-(X) restricted selection. -/
def vonMangoldtSmallXRestrictedPTWSelection
    (X : ℕ) (hX : 3 ≤ X) (hXsmall : X < 2 ^ 120)
    (aStar a η Ctw : ℝ) (haStar : 1 ≤ aStar) (haStarLe : aStar ≤ a) :
    RestrictedPTWSelection X aStar a η Ctw vonMangoldtComplexPositiveFunction := by
  let D := vonMangoldtSmallXElementaryTypeDecomposition X hX hXsmall
  refine ⟨haStar, haStarLe, D, ?_, ?_, ?_⟩
  · intro i hi
    exact smallXTypeITag
  · intro i hi
    change typeIFunction (decompositionDelta (X : ℝ))
      (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ)) (D.component i)
    exact vonMangoldtSmallXComponent_typeI hX hXsmall i
  · intro H hHlower hHupper i hi
    simp [restrictedPTWDesignatedPrefixConclusion, smallXTypeITag]

#print axioms mobiusSmallXComponent_typeI
#print axioms mobiusSmallXElementaryTypeDecomposition
#print axioms vonMangoldtSmallXComponent_typeI
#print axioms vonMangoldtSmallXElementaryTypeDecomposition
#print axioms mobiusSmallXRestrictedPTWSelection
#print axioms vonMangoldtSmallXRestrictedPTWSelection

end FractionalPrimes.Literature.Polynomial

end
