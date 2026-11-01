module
public import FractionalPrimes.Literature.Reciprocal.GlobalCharacterMobius
public import FractionalPrimes.Literature.Reciprocal.NormalizedDirichletFamilyInnerLog
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Reciprocal

open FractionalPrimes.Literature.Uniformity

/-- Package the exact fixed-half-plane-to-MUF estimate as the approved
`MobiusUniformity` predicate, including its required logarithmic threshold. -/
theorem mobiusUniformity_of_fixedHalfPlaneProperty
    (hZFR : fixedHalfPlaneProperty) : MobiusUniformity := by
  intro α A B D hα hα1 hA hB hD
  obtain ⟨X₀, hX₀ge3, hfactor⟩ :=
    mobiusFactorOfFixedHalfPlane hα hα1 hA hB hD
  let M : ℝ := logAbsorptionM 1 B
  let Xμ : ℝ := max X₀ (Real.exp (2 * Real.log M))
  have hM : 1 ≤ M := by
    dsimp [M]
    exact one_le_logAbsorptionM
  have hXμ3 : 3 ≤ Xμ := by
    dsimp [Xμ]
    exact le_trans hX₀ge3 (le_max_left _ _)
  have hlogPower : ∀ {X : ℝ}, Xμ ≤ X → (Real.log X) ^ B ≤ X := by
    intro X hXμX
    have hXpos : 0 < X := by
      have hXμpos : 0 < Xμ := by linarith
      exact lt_of_lt_of_le hXμpos hXμX
    have hExpLE : Real.exp (2 * Real.log M) ≤ X := by
      dsimp [Xμ] at hXμX
      exact (le_max_right X₀ (Real.exp (2 * Real.log M))).trans hXμX
    have hlarge : (2 / (1 : ℝ)) *
        Real.log (1 * logAbsorptionM 1 B) ≤ Real.log X := by
      simpa [M] using (Real.le_log_iff_exp_le hXpos).2 hExpLE
    simpa [Real.rpow_one] using
      (log_absorption_bound (by norm_num) hB.le (by norm_num)
        (by linarith) hlarge)
  have hAt : MobiusUniformityAt α A B D
      (8 + 1536 * Real.exp 1) Xμ := by
    intro q inst X L hXμX hXL hLX hq hqX r hr hrX χ t ht u v huL huv hv
    have hX₀X : X₀ ≤ X :=
      (le_max_left X₀ (Real.exp (2 * Real.log M))).trans hXμX
    have hrX' : (r : ℝ) ≤ X := (hrX.trans (hlogPower hXμX))
    exact hfactor (q := q) hZFR hX₀X hXL hLX hq hqX r hr hrX' χ t ht
      huL huv hv
  exact ⟨8 + 1536 * Real.exp 1, Xμ, by positivity, hXμ3,
    hlogPower, hAt⟩

/-- The accepted E1 adapter supplies the fixed-half-plane property, so the
exact scalar `MobiusUniformity` input follows with no added hypotheses. -/
theorem mobiusUniformity_of_OAISource : MobiusUniformity :=
  mobiusUniformity_of_fixedHalfPlaneProperty fixedHalfPlaneProperty_of_OAISource

#print axioms mobiusUniformity_of_fixedHalfPlaneProperty
#print axioms mobiusUniformity_of_OAISource

end FractionalPrimes.Literature.Reciprocal

end
