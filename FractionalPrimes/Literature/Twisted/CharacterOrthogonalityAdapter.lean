module

public import FractionalPrimes.Literature.Twisted.CharacterExtensionAdapter

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

noncomputable section

/-- Unit-circle characters are equivalent to homomorphisms into the unit group of `Circle`. -/
def unitCircleCharacterUnitsEquiv {G : Type*} [CommGroup G] :
    UnitCircleCharacter G ≃ (G →* Circleˣ) where
  toFun χ := circleToCircleUnits.comp χ
  invFun ψ := circleUnitsToCircle.comp ψ
  left_inv χ := by
    ext g
    rfl
  right_inv ψ := by
    ext g
    rfl

instance unitCircleCharacterFinite {G : Type*} [CommGroup G] [Finite G] :
    Finite (UnitCircleCharacter G) :=
  Finite.of_equiv (G →* Circleˣ) (unitCircleCharacterUnitsEquiv (G := G).symm)

noncomputable instance unitCircleCharacterFintype {G : Type*} [CommGroup G] [Finite G] :
    Fintype (UnitCircleCharacter G) := Fintype.ofFinite _

/-- There are exactly as many unit-circle characters of a finite abelian group as group elements. -/
theorem unitCircleCharacter_card {G : Type*} [CommGroup G] [Fintype G] :
    Fintype.card (UnitCircleCharacter G) = Fintype.card G := by
  letI : Fintype (G →* Circleˣ) := Fintype.ofFinite _
  calc
    Fintype.card (UnitCircleCharacter G) = Fintype.card (G →* Circleˣ) :=
      Fintype.card_congr (unitCircleCharacterUnitsEquiv (G := G))
    _ = Nat.card (G →* Circleˣ) := (Nat.card_eq_fintype_card).symm
    _ = Nat.card G := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G Circle
    _ = Fintype.card G := Nat.card_eq_fintype_card

open Classical in
/-- The exact finite-group orthogonality sum. Character values are coerced into `ℂ`, where
addition and finite sums are defined; `Circle` itself is only multiplicative. -/
theorem unitCircleCharacter_sum {G : Type*} [CommGroup G] [Fintype G] (g : G) :
    ∑ χ : UnitCircleCharacter G, (χ g : ℂ) =
      if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  by_cases hg : g = 1
  · subst g
    simp [unitCircleCharacter_card]
  · obtain ⟨ψ, hψ⟩ := unitCircleCharacter_separates hg
    have hψC : (ψ g : ℂ) ≠ 1 := by
      intro h
      apply hψ
      exact Circle.coe_injective h
    let S : ℂ := ∑ χ : UnitCircleCharacter G, (χ g : ℂ)
    have hshift : S = (ψ g : ℂ) * S := by
      calc
        S = ∑ χ : UnitCircleCharacter G, ((ψ * χ) g : ℂ) := by
          dsimp [S]
          exact (Fintype.sum_bijective (fun χ : UnitCircleCharacter G => ψ * χ)
            (Group.mulLeft_bijective ψ) (fun χ => ((ψ * χ) g : ℂ))
            (fun χ => (χ g : ℂ)) (by intro χ; rfl)).symm
        _ = ∑ χ : UnitCircleCharacter G, (ψ g : ℂ) * (χ g : ℂ) := by
          apply Finset.sum_congr rfl
          intro χ hχ
          simp
        _ = (ψ g : ℂ) * S := by
          dsimp [S]
          rw [Finset.mul_sum]
    have hzero : ((ψ g : ℂ) - 1) * S = 0 := by
      calc
        ((ψ g : ℂ) - 1) * S = (ψ g : ℂ) * S - S := by ring
        _ = 0 := sub_eq_zero.mpr hshift.symm
    have hfactor : (ψ g : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hψC
    have hS : S = 0 := (mul_eq_zero.mp hzero).resolve_left hfactor
    simpa [S, hg] using hS

/-- Extend a circle-valued character of the residue unit group to integers by zero. -/
def unitCircleCharacterEvalInt {q : ℕ}
    (ψ : UnitCircleCharacter (ZMod q)ˣ) (n : ℤ) : ℂ :=
  evalInt (ofUnitCircleCharacter ψ) n

/-- The normalized residue-class indicator, indexed directly by unit-circle characters.
The extension-by-zero convention is built into `unitCircleCharacterEvalInt`; this includes `q = 1`. -/
theorem unitCircleCharacter_residue_indicator {q : ℕ} (hq : 0 < q) (a n : ℤ)
    (ha : IsCoprime a (q : ℤ)) :
    (if (a : ZMod q) = (n : ZMod q) then (1 : ℂ) else 0) =
      (∑ ψ : UnitCircleCharacter (ZMod q)ˣ,
        star (unitCircleCharacterEvalInt ψ a) * unitCircleCharacterEvalInt ψ n) /
        (q.totient : ℂ) := by
  have hsum :
      (∑ ψ : UnitCircleCharacter (ZMod q)ˣ,
        star (unitCircleCharacterEvalInt ψ a) * unitCircleCharacterEvalInt ψ n) =
      (∑ χ : BlueprintCharacter q, star (evalInt χ a) * evalInt χ n) := by
    exact Fintype.sum_equiv (blueprintCharacterEquiv (q := q)).symm
      (fun ψ => star (unitCircleCharacterEvalInt ψ a) * unitCircleCharacterEvalInt ψ n)
      (fun χ => star (evalInt χ a) * evalInt χ n) (by
        intro ψ
        rfl)
  rw [hsum]
  exact integer_character_orthogonality_indicator hq a n ha

end
end FractionalPrimes.Literature.Twisted
