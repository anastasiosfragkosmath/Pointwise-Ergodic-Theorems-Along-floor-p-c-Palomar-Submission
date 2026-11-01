/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Hecke/DetectorRowSpecialization.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Hecke.RowClosure
public import OAI.NumberTheory.DirichletL.Hecke.Dyadic
@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowSpecialization
open HeckeFamily HeckeDyadic HeckeRowClosure

theorem inverse_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ true W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        (UniqueFactorizationMonoid.moebius J.val : ℂ)*idealCoeff η J.val*
          CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [ite_true,idealCoeff_eq_row η χ m f z heq]
  ring

theorem plain_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ false W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        idealCoeff η J.val*CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [Bool.false_eq_true,ite_false,idealCoeff_eq_row η χ m f z heq]

end SevenEighths.HeckeDetectorRowSpecialization

end

end OAI
