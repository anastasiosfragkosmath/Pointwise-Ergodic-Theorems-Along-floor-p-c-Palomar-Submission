module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalSmallXSelection
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalLargeXSelectionAssembly
public import FractionalPrimes.Literature.Polynomial.SelectedPTWBoundedScaleEnvelope
public import Mathlib.Tactic

/-! All-scale assembly of the corrected restricted PTW selections. Small X
uses the checked type-I truncation, the bounded range uses the exact raw
component envelope, and the eventual range retains its source-selected
canonical tags. The eventual type-II envelope estimates remain explicit
conditional inputs. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Twisted
open scoped BigOperators

namespace FractionalPrimes.Literature.Polynomial

/-- One fixed selected outer decomposition for each large natural scale.
These choices depend only on `X` and its large-scale proof, never on `H` or
the twist. -/
theorem selectedMobiusPTWOuterForNat
    (X : ℕ) (hXlarge : (2 : ℝ) ^ 120 ≤ (X : ℝ)) :
    SelectedMobiusPTWTaggedOuterDecomposition (X : ℝ) :=
  Classical.choice (selectedMobiusPTW_taggedOuterDecomposition hXlarge)

theorem selectedVonMangoldtPTWOuterForNat
    (X : ℕ) (hXlarge : (2 : ℝ) ^ 120 ≤ (X : ℝ)) :
    SelectedVonMangoldtPTWTaggedOuterDecomposition (X : ℝ) :=
  Classical.choice (selectedVonMangoldtPTW_taggedOuterDecomposition hXlarge)

/-- The fixed canonical Möbius data used at each large natural scale. -/
noncomputable def selectedMobiusPTWCanonicalForNat
    (X : ℕ) (hXlarge : (2 : ℝ) ^ 120 ≤ (X : ℝ)) :
    SelectedMobiusPTWCanonicalTaggedDecomposition (X : ℝ) :=
  selectedMobiusPTWCanonicalTaggedDecompositionOfOuter
    (selectedMobiusPTWOuterForNat X hXlarge)

/-- The fixed canonical von Mangoldt data used at each large natural scale. -/
noncomputable def selectedVonMangoldtPTWCanonicalForNat
    (X : ℕ) (hXlarge : (2 : ℝ) ^ 120 ≤ (X : ℝ)) :
    SelectedVonMangoldtPTWCanonicalTaggedDecomposition (X : ℝ) :=
  selectedVonMangoldtPTWCanonicalTaggedDecompositionOfOuter
    (selectedVonMangoldtPTWOuterForNat X hXlarge)

/-- Eventual Möbius type-II envelope input, for the fixed canonical outer
choices above. The threshold `X₀` is independent of `X`, `H`, and `T`. -/
def selectedMobiusPTWEventualTagIIEnvelopeBound
    (X₀ a η Cinf : ℝ) : Prop :=
  ∀ X : ℕ, ∀ hXlarge : (2 : ℝ) ^ 120 ≤ (X : ℝ),
    X₀ ≤ (X : ℝ) →
      selectedMobiusCanonicalTagIIEnvelopeBound X a η Cinf
        (selectedMobiusPTWCanonicalForNat X hXlarge)

/-- Eventual von Mangoldt type-II envelope input, with the same uniform
threshold and fixed canonical choice convention. -/
def selectedVonMangoldtPTWEventualTagIIEnvelopeBound
    (X₀ a η Cinf : ℝ) : Prop :=
  ∀ X : ℕ, ∀ hXlarge : (2 : ℝ) ^ 120 ≤ (X : ℝ),
    X₀ ≤ (X : ℝ) →
      selectedVonMangoldtCanonicalTagIIEnvelopeBound X a η Cinf
        (selectedVonMangoldtPTWCanonicalForNat X hXlarge)

theorem log_nat_three_ge_one {X : ℕ} (hX : 3 ≤ X) :
    1 ≤ Real.log (X : ℝ) := by
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hmono : Real.log 3 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) hXreal
  linarith [Real.log_three_gt_d9]

theorem shortLength_le_X_of_upper {X H : ℕ} {η : ℝ}
    (hX : 3 ≤ X) (hη : 0 < η)
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η)) : H ≤ X := by
  have hXone : 1 ≤ (X : ℝ) := by
    have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hexp : (1 - η : ℝ) ≤ 1 := by linarith
  have hpow : (X : ℝ) ^ (1 - η : ℝ) ≤ (X : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexp
  have hHreal : (H : ℝ) ≤ (X : ℝ) := by
    simpa only [Real.rpow_one] using hHupper.trans hpow
  exact_mod_cast hHreal

/-- Single-scale Möbius assembly. Below `X₀` the bounded-scale envelope
handles every raw label; above it only the designated type-II labels require
the explicit eventual premise. -/
def mobiusRestrictedPTWSelection_allScales
    (X : ℕ) (hX : 3 ≤ X)
    (aStar a η Ctw Cinf X₀ : ℝ)
    (haStar : 1 ≤ aStar) (haStarLe : aStar ≤ a)
    (hη : 0 < η) (_hX₀large : (2 : ℝ) ^ 120 ≤ X₀)
    (hCsmall :
      selectedComponentBoundedScaleConstant X₀ * (Real.log X₀) ^ a ≤ Ctw)
    (hCinf : Cinf ≤ Ctw)
    (hEventual : selectedMobiusPTWEventualTagIIEnvelopeBound X₀ a η Cinf) :
    RestrictedPTWSelection X aStar a η Ctw mobiusComplexPositiveFunction := by
  by_cases hsmall : X < 2 ^ 120
  · exact mobiusSmallXRestrictedPTWSelection X hX hsmall aStar a η Ctw
      haStar haStarLe
  · have hXlargeNat : 2 ^ 120 ≤ X := le_of_not_gt hsmall
    have hXlarge : (2 : ℝ) ^ 120 ≤ (X : ℝ) := by exact_mod_cast hXlargeNat
    have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    let C := selectedMobiusPTWCanonicalForNat X hXlarge
    have ha : 0 ≤ a := by
      exact le_trans (le_trans (by norm_num : (0 : ℝ) ≤ 1) haStar) haStarLe
    have hlog : 1 ≤ Real.log (X : ℝ) := log_nat_three_ge_one hX
    have hQ : 1 ≤ (Real.log (X : ℝ)) ^ a := Real.one_le_rpow hlog ha
    by_cases hbounded : (X : ℝ) ≤ X₀
    · have hbound :
          selectedMobiusCanonicalTagIIEnvelopeBound X a η Ctw C := by
        intro i hi htag H hHlower hHupper T hTlower hTupper
        have hHX : H ≤ X := shortLength_le_X_of_upper hX hη hHupper
        have hraw := mobiusSelectedPTWEnvelope_boundedScale
          (X := X) (H := H) (X₀ := X₀) (a := a)
          (Q := (Real.log (X : ℝ)) ^ a) (T := T)
          hX hbounded hHX ha hQ (C.label i)
        have hfactor : 0 ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
          exact mul_nonneg (Nat.cast_nonneg H)
            (Real.rpow_nonneg (by linarith : 0 ≤ Real.log (X : ℝ)) _)
        calc
          _ ≤ (selectedComponentBoundedScaleConstant X₀ *
              (Real.log X₀) ^ a) * (H : ℝ) *
                (Real.log (X : ℝ)) ^ (-a) := hraw
          _ = (selectedComponentBoundedScaleConstant X₀ *
              (Real.log X₀) ^ a) *
                ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := by ring
          _ ≤ Ctw * ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) :=
            mul_le_mul_of_nonneg_right hCsmall hfactor
          _ = Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by ring
      exact selectedMobiusLargeXRestrictedPTWSelectionOfCanonical
        X aStar a η Ctw haStar haStarLe C hbound
    · have hX0 : X₀ ≤ (X : ℝ) := le_of_lt (lt_of_not_ge hbounded)
      have hrawBound := hEventual X hXlarge hX0
      have hbound :
          selectedMobiusCanonicalTagIIEnvelopeBound X a η Ctw C := by
        intro i hi htag H hHlower hHupper T hTlower hTupper
        have hraw := hrawBound i hi htag H hHlower hHupper T hTlower hTupper
        have hfactor : 0 ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
          exact mul_nonneg (Nat.cast_nonneg H)
            (Real.rpow_nonneg (by linarith : 0 ≤ Real.log (X : ℝ)) _)
        calc
          _ ≤ Cinf * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := hraw
          _ = Cinf * ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := by ring
          _ ≤ Ctw * ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) :=
            mul_le_mul_of_nonneg_right hCinf hfactor
          _ = Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by ring
      exact selectedMobiusLargeXRestrictedPTWSelectionOfCanonical
        X aStar a η Ctw haStar haStarLe C hbound

/-- Single-scale von Mangoldt assembly, with the same bounded-range constant
and the fixed source-selected canonical tags. -/
def vonMangoldtRestrictedPTWSelection_allScales
    (X : ℕ) (hX : 3 ≤ X)
    (aStar a η Ctw Cinf X₀ : ℝ)
    (haStar : 1 ≤ aStar) (haStarLe : aStar ≤ a)
    (hη : 0 < η) (_hX₀large : (2 : ℝ) ^ 120 ≤ X₀)
    (hCsmall :
      selectedComponentBoundedScaleConstant X₀ * (Real.log X₀) ^ a ≤ Ctw)
    (hCinf : Cinf ≤ Ctw)
    (hEventual : selectedVonMangoldtPTWEventualTagIIEnvelopeBound X₀ a η Cinf) :
    RestrictedPTWSelection X aStar a η Ctw vonMangoldtComplexPositiveFunction := by
  by_cases hsmall : X < 2 ^ 120
  · exact vonMangoldtSmallXRestrictedPTWSelection X hX hsmall aStar a η Ctw
      haStar haStarLe
  · have hXlargeNat : 2 ^ 120 ≤ X := le_of_not_gt hsmall
    have hXlarge : (2 : ℝ) ^ 120 ≤ (X : ℝ) := by exact_mod_cast hXlargeNat
    have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    let C := selectedVonMangoldtPTWCanonicalForNat X hXlarge
    have ha : 0 ≤ a := by
      exact le_trans (le_trans (by norm_num : (0 : ℝ) ≤ 1) haStar) haStarLe
    have hlog : 1 ≤ Real.log (X : ℝ) := log_nat_three_ge_one hX
    have hQ : 1 ≤ (Real.log (X : ℝ)) ^ a := Real.one_le_rpow hlog ha
    by_cases hbounded : (X : ℝ) ≤ X₀
    · have hbound :
          selectedVonMangoldtCanonicalTagIIEnvelopeBound X a η Ctw C := by
        intro i hi htag H hHlower hHupper T hTlower hTupper
        have hHX : H ≤ X := shortLength_le_X_of_upper hX hη hHupper
        have hraw := vonMangoldtSelectedPTWEnvelope_boundedScale
          (X := X) (H := H) (X₀ := X₀) (a := a)
          (Q := (Real.log (X : ℝ)) ^ a) (T := T)
          hX hbounded hHX ha hQ (C.label i)
        have hfactor : 0 ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
          exact mul_nonneg (Nat.cast_nonneg H)
            (Real.rpow_nonneg (by linarith : 0 ≤ Real.log (X : ℝ)) _)
        calc
          _ ≤ (selectedComponentBoundedScaleConstant X₀ *
              (Real.log X₀) ^ a) * (H : ℝ) *
                (Real.log (X : ℝ)) ^ (-a) := hraw
          _ = (selectedComponentBoundedScaleConstant X₀ *
              (Real.log X₀) ^ a) *
                ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := by ring
          _ ≤ Ctw * ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) :=
            mul_le_mul_of_nonneg_right hCsmall hfactor
          _ = Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by ring
      exact selectedVonMangoldtLargeXRestrictedPTWSelectionOfCanonical
        X aStar a η Ctw haStar haStarLe C hbound
    · have hX0 : X₀ ≤ (X : ℝ) := le_of_lt (lt_of_not_ge hbounded)
      have hrawBound := hEventual X hXlarge hX0
      have hbound :
          selectedVonMangoldtCanonicalTagIIEnvelopeBound X a η Ctw C := by
        intro i hi htag H hHlower hHupper T hTlower hTupper
        have hraw := hrawBound i hi htag H hHlower hHupper T hTlower hTupper
        have hfactor : 0 ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
          exact mul_nonneg (Nat.cast_nonneg H)
            (Real.rpow_nonneg (by linarith : 0 ≤ Real.log (X : ℝ)) _)
        calc
          _ ≤ Cinf * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := hraw
          _ = Cinf * ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := by ring
          _ ≤ Ctw * ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) :=
            mul_le_mul_of_nonneg_right hCinf hfactor
          _ = Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by ring
      exact selectedVonMangoldtLargeXRestrictedPTWSelectionOfCanonical
        X aStar a η Ctw haStar haStarLe C hbound

/-- One common positive constant gives both source selections at every
integer scale. The only analytic input is the pair of uniform eventual
tag-II bounds above the fixed threshold `X₀`. -/
theorem exists_commonAllScalesRestrictedPTWSelections
    (aStar a η CmuInf ClambdaInf X₀ : ℝ)
    (haStar : 1 ≤ aStar) (haStarLe : aStar ≤ a)
    (hη : 0 < η) (_hηmax : η < 3 / 16)
    (hX₀large : (2 : ℝ) ^ 120 ≤ X₀)
    (hμEventual : selectedMobiusPTWEventualTagIIEnvelopeBound X₀ a η CmuInf)
    (hLambdaEventual : selectedVonMangoldtPTWEventualTagIIEnvelopeBound X₀ a η ClambdaInf) :
    ∃ Ctw : ℝ, 0 < Ctw ∧
      ∀ X : ℕ, 3 ≤ X →
        Nonempty (RestrictedPTWSelection X aStar a η Ctw
          mobiusComplexPositiveFunction) ∧
        Nonempty (RestrictedPTWSelection X aStar a η Ctw
          vonMangoldtComplexPositiveFunction) := by
  let Csmall :=
    selectedComponentBoundedScaleConstant X₀ * (Real.log X₀) ^ a
  let Ctw := max 1 (max (max CmuInf ClambdaInf) Csmall)
  have hpositive : 0 < Ctw := by
    dsimp [Ctw]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hCsmall : Csmall ≤ Ctw := by
    dsimp [Ctw]
    exact le_trans (le_max_right (max CmuInf ClambdaInf) Csmall)
      (le_max_right 1 (max (max CmuInf ClambdaInf) Csmall))
  have hCmu : CmuInf ≤ Ctw := by
    dsimp [Ctw]
    exact le_trans (le_trans (le_max_left CmuInf ClambdaInf)
      (le_max_left (max CmuInf ClambdaInf) Csmall))
      (le_max_right 1 (max (max CmuInf ClambdaInf) Csmall))
  have hClambda : ClambdaInf ≤ Ctw := by
    dsimp [Ctw]
    exact le_trans (le_trans (le_max_right CmuInf ClambdaInf)
      (le_max_left (max CmuInf ClambdaInf) Csmall))
      (le_max_right 1 (max (max CmuInf ClambdaInf) Csmall))
  refine ⟨Ctw, hpositive, ?_⟩
  intro X hX
  refine ⟨⟨mobiusRestrictedPTWSelection_allScales X hX
      aStar a η Ctw CmuInf X₀ haStar haStarLe hη hX₀large hCsmall hCmu hμEventual⟩,
    ⟨vonMangoldtRestrictedPTWSelection_allScales X hX
      aStar a η Ctw ClambdaInf X₀ haStar haStarLe hη hX₀large hCsmall hClambda hLambdaEventual⟩⟩

#print axioms mobiusRestrictedPTWSelection_allScales
#print axioms vonMangoldtRestrictedPTWSelection_allScales
#print axioms exists_commonAllScalesRestrictedPTWSelections

end FractionalPrimes.Literature.Polynomial

end
