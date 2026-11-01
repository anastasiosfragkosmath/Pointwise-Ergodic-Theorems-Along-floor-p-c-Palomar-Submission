module

public import FractionalPrimes.Literature.Harmonic.UnweightedMSZAdmissibleData
public import FractionalPrimes.Literature.Harmonic.MSZAdapter

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.Harmonic
open FractionalPrimes.Literature.MSZ
noncomputable section

theorem msz_min_conjugate_endpoints {p : ℝ} (hp : 1 < p) :
    let q := min p (p / (p - 1))
    1 < q ∧ q ≤ 2 ∧ (p = q ∨ p = q / (q - 1)) := by
  have hd : 0 < p - 1 := sub_pos.mpr hp
  have hp' : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ hd]
    linarith
  dsimp only
  refine ⟨lt_min hp hp', ?_, ?_⟩
  · by_cases h : p ≤ 2
    · exact (min_le_left _ _).trans h
    · apply (min_le_right _ _).trans
      rw [div_le_iff₀ hd]
      linarith
  · by_cases h : p ≤ 2
    · left
      symm
      apply min_eq_left
      rw [le_div_iff₀ hd]
      nlinarith
    · right
      have hmin : min p (p / (p - 1)) = p / (p - 1) := by
        apply min_eq_right
        rw [div_le_iff₀ hd]
        nlinarith
      rw [hmin]
      field_simp
      <;> ring

/-- The actual interpolated-family source square at every requested exponent p>1. -/
theorem unweightedMSZEndpointBound
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : AdmissibleData,
      (∀ t, A.kernel t = interpolatedFloorPowerMSZKernel c t) ∧
      ∀ f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
        (∀ x, mszSourceShortVariation A (f : ℤ → ℂ) x < ∞) ∧
        eLpNorm (mszSourceShortVariation A (f : ℤ → ℂ))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (sourceShortVariationConstant A) *
            eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨hq, hq2, hpend⟩ := msz_min_conjugate_endpoints hp
  let A := unweightedMSZAdmissibleData c hc hcNon (min p (p / (p - 1))) hq hq2
  refine ⟨A, fun _ => rfl, fun f => ⟨?_, ?_⟩⟩
  · exact fun x => mszSourceShortVariation_lt_top A p hpend f x
  · exact External.positiveConvolutionShortVariation A p hpend f

#print axioms unweightedMSZEndpointBound
end
end FractionalPrimes.Literature.Harmonic
