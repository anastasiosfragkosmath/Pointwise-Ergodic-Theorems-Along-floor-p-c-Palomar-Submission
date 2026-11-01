module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

/-!
Adapters for the finite-character data and orthogonality statements in
`ltw:character-data` and `ltw:character-orthogonality` of the approved blueprint.

The character family is Mathlib's `DirichletCharacter ℂ q`, so its value on a
nonunit residue is definitionally the extension-by-zero convention. The level
`q = 1` is retained: `ZMod 1` is a singleton and its only character is the
principal character, with value one everywhere.
-/

noncomputable section

namespace FractionalPrimes.Literature.Twisted

/-- Unit-circle characters of an abelian group, represented by Mathlib's circle group. -/
abbrev UnitCircleCharacter (G : Type*) [CommGroup G] := G →* Circle

/-- Complex Dirichlet characters of level `q`, including the level-one case. -/
abbrev BlueprintCharacter (q : ℕ) := DirichletCharacter ℂ q

/-- The finite family of complex Dirichlet characters modulo `q`. -/
abbrev BlueprintCharacters (q : ℕ) := BlueprintCharacter q

/-- Restrict a complex Dirichlet character to the unit group and view its values in `Circle`. -/
def toUnitCircleCharacter {q : ℕ} (χ : BlueprintCharacter q) :
    UnitCircleCharacter (ZMod q)ˣ where
  toFun u := ⟨χ u, by
    simpa [Circle, Submonoid.unitSphere, mem_sphere_zero_iff_norm] using χ.unit_norm_eq_one u⟩
  map_one' := by apply Circle.ext; simp
  map_mul' u v := by
    apply Circle.ext
    simp only [Circle.coe_mul]
    exact (map_mul χ (u : ZMod q) (v : ZMod q))

/-- Extend a unit-circle character of the residue unit group by zero. -/
def ofUnitCircleCharacter {q : ℕ} (ψ : UnitCircleCharacter (ZMod q)ˣ) :
    BlueprintCharacter q :=
  MulChar.ofUnitHom (Circle.toUnits.comp ψ)

/-- Mathlib's extension-by-zero Dirichlet characters modulo `q` are exactly the
homomorphisms from the residue unit group to the complex unit circle. -/
noncomputable def blueprintCharacterEquiv {q : ℕ} :
    BlueprintCharacter q ≃ UnitCircleCharacter (ZMod q)ˣ where
  toFun := toUnitCircleCharacter
  invFun := ofUnitCircleCharacter
  left_inv χ := by
    ext u
    change MulChar.ofUnitHom (Circle.toUnits.comp (toUnitCircleCharacter χ)) u = χ u
    rw [MulChar.ofUnitHom_coe]
    change (Circle.toUnits (toUnitCircleCharacter χ u) : ℂ) = χ u
    calc
      (Circle.toUnits (toUnitCircleCharacter χ u) : ℂ) =
          (toUnitCircleCharacter χ u : ℂ) := by
        change (unitSphereToUnits ℂ (toUnitCircleCharacter χ u) : ℂ) = _
        exact unitSphereToUnits_apply_coe _
      _ = χ u := rfl
  right_inv ψ := by
    ext u
    change (MulChar.ofUnitHom (Circle.toUnits.comp ψ) u : ℂ) = (ψ u : ℂ)
    rw [MulChar.ofUnitHom_coe]
    change (Circle.toUnits (ψ u) : ℂ) = (ψ u : ℂ)
    change (unitSphereToUnits ℂ (ψ u) : ℂ) = (ψ u : ℂ)
    exact unitSphereToUnits_apply_coe _

/-- The character family has exactly Euler's totient number of members, including at `q = 1`.
This is Mathlib's finite-dual cardinality theorem specialized to complex values. -/
theorem blueprintCharacters_card {q : ℕ} [NeZero q] :
    Fintype.card (BlueprintCharacters q) = q.totient := by
  haveI : NeZero ((Monoid.exponent (ZMod q)ˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast (Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ))⟩
  simpa [BlueprintCharacters, BlueprintCharacter, Nat.card_eq_fintype_card] using
    (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) q)

/-- Evaluate a Dirichlet character on an integer by reduction modulo its level. -/
def evalInt {q : ℕ} (χ : BlueprintCharacter q) (n : ℤ) : ℂ := χ (n : ZMod q)

/-- The principal character is Mathlib's trivial multiplicative character. -/
def principalCharacter (q : ℕ) : BlueprintCharacter q := 1

@[simp]
theorem evalInt_eq_zero_iff {q : ℕ} (χ : BlueprintCharacter q) (n : ℤ) :
    evalInt χ n = 0 ↔ ¬ IsCoprime n (q : ℤ) := by
  simpa [evalInt] using (DirichletCharacter.apply_eq_zero_iff (χ := χ) n)

/-- Extension by zero on nonunits, in the integer-evaluation notation. -/
theorem evalInt_eq_zero_of_not_coprime {q : ℕ} (χ : BlueprintCharacter q) (n : ℤ)
    (hn : ¬ IsCoprime n (q : ℤ)) : evalInt χ n = 0 :=
  (evalInt_eq_zero_iff χ n).2 hn

/-- The principal character is one exactly on integers coprime to its modulus. -/
theorem principalCharacter_evalInt {q : ℕ} (n : ℤ) :
    evalInt (principalCharacter q) n = if IsCoprime n (q : ℤ) then 1 else 0 := by
  by_cases h : IsCoprime n (q : ℤ)
  · have hu : IsUnit (n : ZMod q) :=
      (ZMod.coe_int_isUnit_iff_isCoprime n q).2 (isCoprime_comm.mpr h)
    simp only [evalInt, principalCharacter, if_pos h]
    exact MulChar.one_apply hu
  · have hnu : ¬ IsUnit (n : ZMod q) := by
      intro hu
      exact h ((isCoprime_comm.mp (ZMod.coe_int_isUnit_iff_isCoprime n q |>.1 hu)))
    simp only [evalInt, principalCharacter, if_neg h]
    exact MulChar.map_nonunit 1 hnu

/-- A character has unit modulus at every unit residue. -/
theorem unit_value_norm {q : ℕ} (χ : BlueprintCharacter q) {a : ZMod q}
    (ha : IsUnit a) : ‖χ a‖ = 1 :=
  χ.unit_norm_eq_one ha.unit

/-- At level one every character is the principal character; in particular its value is one. -/
theorem modulus_one_character_eq_principal (χ : BlueprintCharacter 1) :
    χ = principalCharacter 1 := by
  ext a
  have ha : a = (1 : (ZMod 1)ˣ) := Subsingleton.elim _ _
  simp [principalCharacter, ha]

@[simp]
theorem modulus_one_evalInt (χ : BlueprintCharacter 1) (n : ℤ) : evalInt χ n = 1 := by
  rw [modulus_one_character_eq_principal χ]
  have hn : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [evalInt, principalCharacter, hn]
  exact MulChar.one_apply isUnit_one

/-- The character sum with conjugation, in the exact residue-class form used by the blueprint. -/
theorem character_orthogonality_sum {q : ℕ} [NeZero q] (a b : ZMod q) (ha : IsUnit a) :
    ∑ χ : BlueprintCharacter q, star (χ a) * χ b =
      if a = b then (q.totient : ℂ) else 0 := by
  calc
    ∑ χ : BlueprintCharacter q, star (χ a) * χ b =
        ∑ χ : BlueprintCharacter q, χ a⁻¹ * χ b := by
      apply Finset.sum_congr rfl
      intro χ hχ
      congr 1
      have hinv : Ring.inverse a = a⁻¹ := by
        rw [← ha.unit_spec, Ring.inverse_unit]
        exact (ZMod.inv_coe_unit ha.unit).symm
      simpa [hinv] using (MulChar.star_apply' χ a).trans (MulChar.inv_apply χ a)
    _ = if a = b then (q.totient : ℂ) else 0 :=
      DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) ha b

/-- The normalized character sum is exactly the indicator of a residue class.
This statement includes `q = 1`, whose totient is one. -/
theorem character_orthogonality_indicator {q : ℕ} (hq : 0 < q) (a b : ZMod q)
    (ha : IsUnit a) :
    (if a = b then (1 : ℂ) else 0) =
      (∑ χ : BlueprintCharacter q, star (χ a) * χ b) / (q.totient : ℂ) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  haveI : NeZero ((Monoid.exponent (ZMod q)ˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast (Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ))⟩
  rw [character_orthogonality_sum a b ha]
  have hφnat : 0 < q.totient := Nat.totient_pos.mpr hq
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hφnat)
  by_cases hab : a = b
  · simp [hab, hφ]
  · simp [hab]

/-- Integer version of the normalized orthogonality identity. The `IsCoprime` hypothesis
ensures that the residue represented by `a` is a unit. -/
theorem integer_character_orthogonality_indicator {q : ℕ} (hq : 0 < q)
    (a n : ℤ) (ha : IsCoprime a (q : ℤ)) :
    (if (a : ZMod q) = (n : ZMod q) then (1 : ℂ) else 0) =
      (∑ χ : BlueprintCharacter q,
        star (evalInt χ a) * evalInt χ n) / (q.totient : ℂ) := by
  have ha' : IsUnit (a : ZMod q) :=
    (ZMod.coe_int_isUnit_iff_isCoprime a q).2 (isCoprime_comm.mpr ha)
  simpa [evalInt] using character_orthogonality_indicator hq (a : ZMod q) (n : ZMod q) ha'

end FractionalPrimes.Literature.Twisted
