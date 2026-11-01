/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Detector/TuplePrincipal.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Detector.TuplePrime
@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem indexedCompensatedHigh_principal_continued {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x*globalClosedCorrection η S x w z)*
      ∏i,compensatedReplacement (coordV (Ideal.absNorm (P i).val) z)
        (coordW (Ideal.absNorm (P i).val) 1 w)
        (coordD (Ideal.absNorm (P i).val) (HeckeFamily.idealCoeff η (P i).val) 1 x)
        (idealMarkedClosed η (P i) x w z)
        (star (HeckeFamily.idealCoeff η (P i).val)*(Ideal.absNorm (P i).val:ℂ)^x)
        ((Ideal.absNorm (P i).val:ℂ)^(-w))/idealClosedCorrection η (P i) x w z := by
  have hs (i : Fin K) : Supported (P i).val := outside_prime_supported S hS.bad (P i) (hPS i)
  rw [indexedCompensatedHigh_principal η S P hP hs]
  have ht : ∀Q∈Finset.univ.image P,Q.val∉S := by
    intro Q hQ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hPS i
  rw [spectralCompensatedHigh_continued S hS (Finset.univ.image P) ht η x w z _ _ hx hw hz,
    Finset.prod_image hP.injOn]

end SevenEighths.ProbePhysical
end

end OAI
