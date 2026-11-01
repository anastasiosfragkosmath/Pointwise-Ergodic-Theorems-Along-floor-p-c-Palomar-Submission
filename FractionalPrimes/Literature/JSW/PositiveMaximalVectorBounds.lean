module

public import FractionalPrimes.Literature.JSW.FiniteVectorDuality
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Vector bounds from positive maximal estimates

This module develops the finite-family probability-convolution energy
estimate that is the first pointwise step in `lj:positivity`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open scoped ComplexConjugate

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Summing the checked probability-convolution Jensen inequality gives the
pointwise energy bound for any finite family of probability measures. -/
theorem finiteProbabilityConvolution_square_le
    {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (f : ι → ℝ → ℂ) (x : ℝ)
    (hf : ∀ i, Integrable (fun y => f i (x-y)) (μ i))
    (hfSq : ∀ i, Integrable (fun y => ‖f i (x-y)‖ ^ 2) (μ i)) :
    ∑ i, ‖jswConvolution (μ i) (f i) x‖ ^ 2 ≤
      ∑ i, ∫ y, ‖f i (x-y)‖ ^ 2 ∂(μ i) := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  letI : IsProbabilityMeasure (μ i) := hμ i
  exact jswProbabilityConvolution_square_le (μ i) (f i) x (hf i) (hfSq i)

/-- Fubini identifies the adjoint pairing for convolution by an arbitrary
finite positive measure.  The two product-integrability hypotheses are the
precise absolute-integrability conditions on the two translated kernels;
they are supplied in applications by Hölder for the relevant `Lᵖ` and
conjugate `Lᵖ` inputs. -/
theorem integral_jswConvolution_mul_conj_eq_adjoint
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f g : ℝ → ℂ)
    (hLeft : Integrable
      (fun z : ℝ × ℝ => f (z.1 - z.2) * conj (g z.1))
      (volume.prod μ))
    (hRight : Integrable
      (fun z : ℝ × ℝ => f z.1 * conj (g (z.1 + z.2)))
      (volume.prod μ)) :
    ∫ x, jswConvolution μ f x * conj (g x) ∂volume =
      ∫ x, f x * conj (∫ y, g (x + y) ∂μ) ∂volume := by
  calc
    ∫ x, jswConvolution μ f x * conj (g x) ∂volume =
        ∫ x, ∫ y, f (x - y) * conj (g x) ∂μ ∂volume := by
          congr 1
          funext x
          exact (integral_mul_const (conj (g x)) (fun y : ℝ => f (x - y))).symm
    _ = ∫ y, ∫ x, f (x - y) * conj (g x) ∂volume ∂μ :=
      integral_integral_swap hLeft
    _ = ∫ y, ∫ x, f x * conj (g (x + y)) ∂volume ∂μ := by
      congr 1
      funext y
      simpa [sub_add_cancel] using
        (integral_sub_right_eq_self
          (fun x : ℝ => f x * conj (g (x + y))) y)
    _ = ∫ x, ∫ y, f x * conj (g (x + y)) ∂μ ∂volume :=
      (integral_integral_swap hRight).symm
    _ = ∫ x, f x * conj (∫ y, g (x + y) ∂μ) ∂volume := by
      congr 1
      funext x
      rw [integral_const_mul, integral_conj]

/-- The two translated products in the Fubini pairing lemma are integrable
whenever the inputs have conjugate finite `Lᵖ` exponents.  The measure
preserving shears `(x,y) ↦ (x-y,y)` and `(x,y) ↦ (x+y,y)` lift the translated
input to the product space, after which Hölder gives product integrability. -/
theorem integrable_translated_pair_products_of_memLp
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r q : ℝ} (hrq : r.HolderConjugate q)
    (f g : ℝ → ℂ)
    (hf : MemLp f (ENNReal.ofReal r) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Integrable
        (fun z : ℝ × ℝ => f (z.1 - z.2) * conj (g z.1))
        (volume.prod μ) ∧
      Integrable
        (fun z : ℝ × ℝ => f z.1 * conj (g (z.1 + z.2)))
        (volume.prod μ) := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal q) 1 :=
    hrq.ennrealOfReal
  have hFSub : MemLp (fun z : ℝ × ℝ => f (z.1 - z.2))
      (ENNReal.ofReal r) (volume.prod μ) := by
    have hfst := hf.comp_fst μ
    exact hfst.comp_measurePreserving (measurePreserving_sub_prod volume μ)
  have hGfst : MemLp (fun z : ℝ × ℝ => g z.1)
      (ENNReal.ofReal q) (volume.prod μ) := hg.comp_fst μ
  have hLeft : MemLp
      (fun z : ℝ × ℝ => f (z.1 - z.2) * conj (g z.1)) 1
      (volume.prod μ) := by
    have hGconj : MemLp (fun z : ℝ × ℝ => conj (g z.1))
        (ENNReal.ofReal q) (volume.prod μ) := by
      convert hGfst.star using 1
      funext z
      rfl
    exact hFSub.mul hGconj
  have hFfst : MemLp (fun z : ℝ × ℝ => f z.1)
      (ENNReal.ofReal r) (volume.prod μ) := hf.comp_fst μ
  have hGAdd : MemLp (fun z : ℝ × ℝ => g (z.1 + z.2))
      (ENNReal.ofReal q) (volume.prod μ) := by
    have hfst := hg.comp_fst μ
    exact hfst.comp_measurePreserving (measurePreserving_add_prod volume μ)
  have hRight : MemLp
      (fun z : ℝ × ℝ => f z.1 * conj (g (z.1 + z.2))) 1
      (volume.prod μ) := by
    have hGconj : MemLp (fun z : ℝ × ℝ => conj (g (z.1 + z.2)))
        (ENNReal.ofReal q) (volume.prod μ) := by
      convert hGAdd.star using 1
      funext z
      rfl
    exact hFfst.mul hGconj
  exact ⟨memLp_one_iff_integrable.mp hLeft,
    memLp_one_iff_integrable.mp hRight⟩

/-- In the `p>2` regime of `lj:positivity`, the squared input exponent
`p/2` is Hölder conjugate to the maximal-function exponent `p/(p-2)`, so the
Fubini pairing's product-integrability conditions follow directly from the
paper's `Lᵖ` and `Lᑫ` assumptions. -/
theorem integrable_translated_pair_products_of_memLp_sq
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {p : ℝ} (hp : 2 < p)
    (f g : ℝ → ℂ)
    (hf : MemLp f (ENNReal.ofReal (p / 2)) volume)
    (hg : MemLp g (ENNReal.ofReal (p / (p - 2))) volume) :
    Integrable
        (fun z : ℝ × ℝ => f (z.1 - z.2) * conj (g z.1))
        (volume.prod μ) ∧
      Integrable
        (fun z : ℝ × ℝ => f z.1 * conj (g (z.1 + z.2)))
        (volume.prod μ) := by
  have hpPos : 0 < p := by linarith
  have hpdPos : 0 < p - 2 := by linarith
  have hpq : (p / 2).HolderConjugate (p / (p - 2)) := by
    refine ⟨?_, div_pos hpPos (by norm_num), div_pos hpPos hpdPos⟩
    field_simp
    <;> ring
  exact integrable_translated_pair_products_of_memLp μ hpq f g hf hg

/-- Squaring the pointwise norm converts the `Lᵖ` seminorm exactly into the
`Lᵖ⁄²` seminorm of the squared norm. This is the scalar bridge from the energy
estimate to the vector-valued `Lᵖ(ℓ²)` estimate. -/
theorem eLpNorm_norm_sq_eq
    {H : Type*} [NormedAddCommGroup H]
    {p : ℝ} (hp : 0 < p) {f : ℝ → H}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => ‖f x‖ ^ 2) (ENNReal.ofReal (p / 2)) volume =
      eLpNorm f (ENNReal.ofReal p) volume ^ 2 := by
  calc
    eLpNorm (fun x => ‖f x‖ ^ 2) (ENNReal.ofReal (p / 2)) volume =
        eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) volume := by
          congr 1
          funext x
          exact (Real.rpow_natCast _ _).symm
    _ = eLpNorm f (ENNReal.ofReal (p / 2) * ENNReal.ofReal 2) volume ^ (2 : ℝ) :=
      eLpNorm_norm_rpow f hf (by norm_num : 0 < (2 : ℝ))
    _ = eLpNorm f (ENNReal.ofReal p) volume ^ 2 := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ p / 2)]
      rw [show p / 2 * 2 = p by ring]
      exact ENNReal.rpow_natCast _ _


#print axioms finiteProbabilityConvolution_square_le
#print axioms integral_jswConvolution_mul_conj_eq_adjoint
#print axioms integrable_translated_pair_products_of_memLp
#print axioms integrable_translated_pair_products_of_memLp_sq
#print axioms eLpNorm_norm_sq_eq

end

end FractionalPrimes.Literature.JSW

end
