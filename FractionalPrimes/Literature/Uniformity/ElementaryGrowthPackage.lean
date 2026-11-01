module

public import FractionalPrimes.Literature.Uniformity.ArchimedeanTwistVariation
public import FractionalPrimes.Literature.Uniformity.LogAbsorption

/-!
# Aggregate package for `lu:elementary-growth`

This package collects the approved archimedean-twist variation bounds and the
explicit logarithmic absorption estimate without changing their hypotheses.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

/-- The exact conclusions of blueprint lemma `lu:elementary-growth`. -/
structure TwistVariationAndLogAbsorption where
  /-- Archimedean twist variation on a finite progression in `(X,X+H]`. -/
  twist_variation : ∀ {X H T : ℝ} (_hX : 1 ≤ X) (_hH : 0 < H) (_hHX : H ≤ X)
    (P : Finset ℤ) (_hPAP : isFiniteArithmeticProgression P)
    (_hP : ∀ n ∈ P, X < (n : ℝ) ∧ (n : ℝ) ≤ X + H),
      finiteOrderedTotalVariation P (fun n => archimedeanTwist T n) ≤
        1 + |T| * H / X
  /-- Summed archimedean twist variation over all `q` residue classes. -/
  residue_variation : ∀ {X H T : ℝ} (_hX : 1 ≤ X) (_hH : 0 < H) (_hHX : H ≤ X)
    (P : Finset ℤ) (_hPAP : isFiniteArithmeticProgression P)
    (_hP : ∀ n ∈ P, X < (n : ℝ) ∧ (n : ℝ) ≤ X + H)
    (q : ℕ) (hq : 0 < q),
      residueClassTotalVariation (P : Set ℤ) (fun n => archimedeanTwist T n) q hq ≤
        ENNReal.ofReal ((q : ℝ) * (1 + |T| * H / X))
  /-- The exact logarithmic absorption inequality, with the explicit
  blueprint constant and threshold. -/
  log_absorption : ∀ {a b K X : ℝ} (_ha : 0 < a) (_hb : 0 ≤ b)
    (_hK : 1 ≤ K) (_hX : 1 ≤ X)
    (_hlarge : (2 / a) * Real.log (K * logAbsorptionM a b) ≤ Real.log X),
      K * (Real.log X) ^ b ≤ X ^ a

/-- Manifest-facing package for the approved `lu:elementary-growth` lemma. -/
theorem twistVariationAndLogAbsorption : TwistVariationAndLogAbsorption where
  twist_variation := fun hX hH hHX P hPAP hP =>
    finiteOrderedTotalVariation_archimedeanTwist_le hX hH hHX P hPAP hP
  residue_variation := fun hX hH hHX P hPAP hP q hq =>
    residueClassTotalVariation_archimedeanTwist_le hX hH hHX P hPAP hP q hq
  log_absorption := fun ha hb hK hX hlarge =>
    log_absorption_bound ha hb hK hX hlarge

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.twistVariationAndLogAbsorption
