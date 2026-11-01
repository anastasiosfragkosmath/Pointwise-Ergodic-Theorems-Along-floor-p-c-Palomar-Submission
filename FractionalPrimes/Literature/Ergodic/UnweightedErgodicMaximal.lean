module

public import FractionalPrimes.Literature.Ergodic.UnweightedErgodicVariation
public import FractionalPrimes.Literature.Ergodic.MaximalFromVariation

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
noncomputable section
universe u

def unweightedErgodicMaximal {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) : X → ℝ≥0∞ :=
  scaleFamilyMaximal (fun N => unweightedAverage S c f N)

theorem mobiusAverage_norm_le_unweightedNormAverage
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) (N : Scale) (x : X) :
    ‖mobiusAverage S c f N x‖ ≤
      ‖unweightedAverage S c (fun y => (‖f y‖ : ℂ)) N x‖ := by
  change ‖(N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val,
      (mobiusWeight n : ℂ) * f (S.iterate (floorPower c n) x)‖ ≤
    ‖(N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val,
      1 * (‖f (S.iterate (floorPower c n) x)‖ : ℂ)‖
  simp only [one_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hright : ‖∑ n ∈ Finset.Icc 1 N.val,
      (‖f (S.iterate (floorPower c n) x)‖ : ℂ)‖ =
      ∑ n ∈ Finset.Icc 1 N.val, ‖f (S.iterate (floorPower c n) x)‖ := by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  rw [hright]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  have hmu : ‖(mobiusWeight n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hmu (norm_nonneg _)).trans_eq (one_mul _)

/-- `er:unweighted-maximal`, including the source Möbius domination clause. -/
theorem unweightedErgodicMaximalBound
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent) :
    ∃ C : NNReal, ∀ {X : Type u} [MeasurableSpace X] (S : InvertibleSystem X)
      (f : X → ℂ), MemLp f (ENNReal.ofReal p) S.μ →
      eLpNorm (unweightedErgodicMaximal S c.value f) (ENNReal.ofReal p) S.μ ≤
          ENNReal.ofNNReal C * eLpNorm f (ENNReal.ofReal p) S.μ ∧
        ∀ x, scaleFamilyMaximal (fun N => mobiusAverage S c.value f N) x ≤
          unweightedErgodicMaximal S c.value (fun y => (‖f y‖ : ℂ)) x := by
  obtain ⟨C, hvar⟩ := unweightedErgodicVariation hp (by norm_num : (2 : ℝ) < 3) c
  refine ⟨1 + C, fun {X} _ S f hf => ⟨?_, ?_⟩⟩
  · have hpENN := ENNReal.one_le_ofReal.mpr hp.le
    have hmax := eLpNorm_scaleFamilyMaximal_le S.μ hpENN 3 (by norm_num)
      (fun N => unweightedAverage S c.value f N)
      (fun N => aestronglyMeasurable_unweightedAverage S c.value f N hf.aestronglyMeasurable)
      ⟨1, by omega⟩
    have hbase := eLpNorm_unweightedAverage_le_self S c.value f ⟨1, by omega⟩
      hpENN hf.aestronglyMeasurable
    calc
      _ ≤ _ := hmax
      _ ≤ eLpNorm f (ENNReal.ofReal p) S.μ +
          ENNReal.ofNNReal C * eLpNorm f (ENNReal.ofReal p) S.μ :=
        add_le_add hbase (hvar S f hf)
      _ = _ := by rw [ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]
  · intro x
    apply iSup_le
    intro N
    exact (ENNReal.ofReal_le_ofReal (mobiusAverage_norm_le_unweightedNormAverage S c.value f N x)).trans
      (le_iSup (fun N => ENNReal.ofReal
        ‖unweightedAverage S c.value (fun y => (‖f y‖ : ℂ)) N x‖) N)

#print axioms unweightedErgodicMaximalBound
end
end FractionalPrimes
