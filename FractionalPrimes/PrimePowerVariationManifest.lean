module
public import FractionalPrimes.PrimePowerVariationConstantBridge
@[expose] public section

/-! The exact manifest name for the paper's main variation theorem. -/

namespace FractionalPrimes

noncomputable section

universe u

/-- Blueprint `er:prime-variation`: one strictly positive finite constant
works on every invertible sigma-finite system for every input in the
paper's complete parameter range. -/
theorem primePowerVariation (q : VariationParameters) :
    PrimePowerVariationStatement.{u} q := by
  rcases q with ⟨c, p, hp, r, hr⟩
  exact primePowerVariationStatement_of_OAISource hp hr c

#print axioms primePowerVariation

end
end FractionalPrimes
