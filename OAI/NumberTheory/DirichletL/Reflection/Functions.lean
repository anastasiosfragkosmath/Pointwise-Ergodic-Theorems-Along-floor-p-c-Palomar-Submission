/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Reflection/Functions.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Reflection.Transport
@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma sourceRowPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (R F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by
  subst q
  subst j'
  rfl

lemma sourceSlotPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (S F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by
  subst q
  subst j'
  rfl

theorem sourceRowPhase_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (R F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s hp hg j (R.image f) (F.image f) u m =
      sourceRowPhase s hq hqg j' (R.image g) (F.image g) u m := by
  rw [← sourceRowPhase_transport s hp hg j f hf R F u m,
    ← sourceRowPhase_transport s hq hqg j' g hg' R F u m]
  exact sourceRowPhase_congr_functions s _ _ _ _ _ _ R F u m (funext he) (funext hj)

theorem sourceSlotPhase_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (S F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s hp hg j (S.image f) (F.image f) u m =
      sourceSlotPhase s hq hqg j' (S.image g) (F.image g) u m := by
  rw [← sourceSlotPhase_transport s hp hg j f hf S F u m,
    ← sourceSlotPhase_transport s hq hqg j' g hg' S F u m]
  exact sourceSlotPhase_congr_functions s _ _ _ _ _ _ S F u m (funext he) (funext hj)

end
end SevenEighths.InverseReflectedPhase

end OAI
