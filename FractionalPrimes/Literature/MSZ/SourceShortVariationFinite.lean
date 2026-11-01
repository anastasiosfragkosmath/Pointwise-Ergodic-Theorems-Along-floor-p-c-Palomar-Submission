module

public import FractionalPrimes.Literature.MSZ.ShortVariationEndpoints

/-! Finiteness of the actual ENNReal source square, before taking real coordinates. -/
@[expose] public section
namespace FractionalPrimes.Literature.MSZ
open MeasureTheory
open scoped ENNReal
noncomputable section

def sourceShortVariationCoreConstant (A : AdmissibleData) : ℝ :=
  (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A) *
    (max (2 * (1 + A.Mq))
      ((2 * (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A)) ^
        (2 / A.q))) ^ ((2 - A.q) / 2)

def sourceShortVariationConstant (A : AdmissibleData) : ℝ :=
  1 + sourceShortVariationCoreConstant A

theorem mszSourceShortVariation_lt_top
    (A : AdmissibleData) (p : ℝ)
    (hp : p = A.q ∨ p = A.q / (A.q - 1))
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) (x : ℤ) :
    mszSourceShortVariation A (f : ℤ → ℂ) x < ∞ := by
  have hp1 : 1 < p := by
    rcases hp with h | h
    · simpa only [h] using A.q_gt_one
    · rw [h, lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
      linarith
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp1.le⟩
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hp1)
  have hmem := memLp_count_of_memlp_seq_finite hp0 ENNReal.ofReal_ne_top f
  let B := ENNReal.ofReal (sourceShortVariationCoreConstant A) *
    eLpNorm (fun y : ℤ => f y) (ENNReal.ofReal p) Measure.count
  have hB : B < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmem.eLpNorm_lt_top
  have hbound (n : ℕ) :
      ENNReal.ofReal (mszFiniteShortVariation A n n (f : ℤ → ℂ) x) ≤ B := by
    have hcoord := MeasureTheory.enorm_le_eLpNorm_count
      (fun y : ℤ => mszFiniteShortVariation A n n (f : ℤ → ℂ) y) x hp0
    have hcoord' : ‖mszFiniteShortVariation A n n (f : ℤ → ℂ) x‖ₑ ≤
        eLpNorm (fun y : ℤ => mszFiniteShortVariation A n n (f : ℤ → ℂ) y)
          (ENNReal.ofReal p) Measure.count := by
      simpa only [enorm_eq_nnnorm] using hcoord
    have hnonneg : 0 ≤ mszFiniteShortVariation A n n (f : ℤ → ℂ) x :=
      Real.sqrt_nonneg _
    rw [← ofReal_norm, Real.norm_of_nonneg hnonneg] at hcoord'
    exact hcoord'.trans (by
      simpa only [B, sourceShortVariationCoreConstant] using
        (mszFiniteShortVariation_uniform A n n p hp f))
  rw [mszSourceShortVariation_eq_iSup_diagonal]
  exact lt_of_le_of_lt (iSup_le hbound) hB

#print axioms mszSourceShortVariation_lt_top

/-- The endpoint estimate on the source ENNReal square itself. -/
theorem mszSourceShortVariation_eLpNorm_le
    (A : AdmissibleData) (p : ℝ)
    (hp : p = A.q ∨ p = A.q / (A.q - 1))
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    eLpNorm (mszSourceShortVariation A (f : ℤ → ℂ))
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (sourceShortVariationConstant A) *
        eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count := by
  have heq : eLpNorm (mszSourceShortVariation A (f : ℤ → ℂ))
      (ENNReal.ofReal p) Measure.count =
      eLpNorm (fun x : ℤ => (mszSourceShortVariation A (f : ℤ → ℂ) x).toReal)
        (ENNReal.ofReal p) Measure.count := by
    apply eLpNorm_congr_enorm_ae
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [enorm_eq_self, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (mszSourceShortVariation_lt_top A p hp f x).ne])
  rw [heq]
  exact shortVariationEndpoints A p hp f

#print axioms mszSourceShortVariation_eLpNorm_le

end
end FractionalPrimes.Literature.MSZ
