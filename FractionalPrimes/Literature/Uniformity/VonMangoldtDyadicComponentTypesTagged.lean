module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition
public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.Uniformity
noncomputable section

/-- The von Mangoldt companion to the already checked tagged Möbius
component theorem. It preserves the failed type-I exponent inequality
when the grouped source construction chooses type II. -/
theorem largeVonMangoldtDyadicComponentTypesTagged {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) :
    ∃ α : Fin (vonMangoldtLabelFactors ν).length → ℝ,
      (∀ i, 0 ≤ α i) ∧
      (∑ i, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤
            dyadicFactorScale ((vonMangoldtLabelFactors ν)[i]) ∧
          dyadicFactorScale ((vonMangoldtLabelFactors ν)[i]) ≤
            normalizedExponentConstant * X ^ α i) ∧
      (∀ i j, (vonMangoldtLabelFactors ν)[i] = .mobius j →
        α i ≤ (1 / 8 : ℝ)) ∧
      largeDyadicComponentTaggedPackage (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (fun n : PositiveInteger =>
          ((vonMangoldtDyadicComponent
            (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ))
        (vonMangoldtLabelFactors ν) α := by
  obtain ⟨α, hα, hsum, hscale, hmob⟩ :=
    vonMangoldtComponentNormalizedExponents hX hν
  have hlen := vonMangoldtLabelFactorCount ν
  have hc := dyadicBinomialCoefficient_abs_le ν.1
  have hscaleGet :
      ∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤
            dyadicFactorScale ((vonMangoldtLabelFactors ν).get i) ∧
          dyadicFactorScale ((vonMangoldtLabelFactors ν).get i) ≤
            normalizedExponentConstant * X ^ α i := by
    intro i
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hscale i
  have hmobGet :
      ∀ i j, (vonMangoldtLabelFactors ν).get i = .mobius j →
        α i ≤ (1 / 8 : ℝ) := by
    intro i j hij
    apply hmob i j
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hij
  have hcomponent :
      (fun n : PositiveInteger =>
        ((vonMangoldtDyadicComponent
          (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)) =
      groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ)
        (vonMangoldtLabelFactors ν) := by
    funext n
    simp [groupedDyadicFactor, vonMangoldtDyadicComponent_apply]
  have hpackage := largeGroupedDyadicComponentTaggedPackage_public hX
    (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1)
    (vonMangoldtLabelFactors ν) hlen hc α hα hsum hscaleGet hmobGet
  refine ⟨α, hα, hsum, hscale, hmob, ?_⟩
  rw [hcomponent]
  exact hpackage

#print axioms largeVonMangoldtDyadicComponentTypesTagged
end
end FractionalPrimes.Literature.Uniformity.Combinatorics
