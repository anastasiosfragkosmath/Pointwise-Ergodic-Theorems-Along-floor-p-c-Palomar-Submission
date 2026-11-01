module

public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.GroupTheory.FiniteAbelian.Duality

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

noncomputable section

/-- Regard an element of the circle group as a unit of the circle group. -/
def circleValueAsUnit (z : Circle) : Circleˣ where
  val := z
  inv := z⁻¹
  val_inv := mul_inv_cancel z
  inv_val := inv_mul_cancel z

/-- The canonical monoid hom from the circle group to its group of units. -/
def circleToCircleUnits : Circle →* Circleˣ where
  toFun := circleValueAsUnit
  map_one' := by apply Units.ext; rfl
  map_mul' _ _ := by apply Units.ext; rfl

/-- Forget the redundant unit witness on an element of `Circleˣ`. -/
def circleUnitsToCircle : Circleˣ →* Circle where
  toFun := fun z => z
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Every unit-circle character of a subgroup of a finite abelian group extends to the group.
This is the approved `ltw:character-extension` statement. -/
theorem unitCircleCharacter_extends {G : Type*} [CommGroup G] [Finite G]
    (H : Subgroup G) (χ : UnitCircleCharacter H) :
    ∃ ψ : UnitCircleCharacter G, ψ.domRestrict H = χ := by
  obtain ⟨Ψ, hΨ⟩ :=
    (MonoidHom.domRestrict_surjective (M := Circle) H
      (circleToCircleUnits.comp χ))
  have hΨ' : Ψ.domRestrict H = circleToCircleUnits.comp χ := by
    simpa [MonoidHom.domRestrictHom] using hΨ
  refine ⟨circleUnitsToCircle.comp Ψ, ?_⟩
  ext h
  have hh : Ψ h = circleToCircleUnits (χ h) := by
    have hh := congrArg (fun f : H →* Circleˣ => f h) hΨ'
    simpa only [MonoidHom.domRestrict_apply, MonoidHom.comp_apply] using hh
  simp [circleUnitsToCircle, circleToCircleUnits, circleValueAsUnit, hh]

/-- Nonidentity elements of finite abelian groups are separated by a unit-circle character.
This is the separation conclusion of `ltw:character-extension`. -/
theorem unitCircleCharacter_separates {G : Type*} [CommGroup G] [Finite G]
    {g : G} (hg : g ≠ 1) :
    ∃ χ : UnitCircleCharacter G, χ g ≠ 1 := by
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G Circle hg
  refine ⟨circleUnitsToCircle.comp φ, ?_⟩
  intro h
  apply hφ
  apply Units.ext
  change (φ g : Circle) = 1
  simpa [circleUnitsToCircle] using h

end
end FractionalPrimes.Literature.Twisted
