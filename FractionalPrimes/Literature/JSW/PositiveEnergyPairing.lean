module

public import FractionalPrimes.Literature.JSW.RealAdjointNormDuality

/-!
# Finite positive-energy pairing

The real-valued Fubini identity is used for the squared coordinate energies
in the `p>2` part of `lj:positivity`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Real-valued convolution/reflection pairing under its exact two product
integrability conditions. -/
theorem integral_positiveEnergy_pairing
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f g : ℝ → ℝ)
    (hLeft : Integrable (fun z : ℝ × ℝ => f (z.1 - z.2) * g z.1)
      (volume.prod μ))
    (hRight : Integrable (fun z : ℝ × ℝ => f z.1 * g (z.1 + z.2))
      (volume.prod μ)) :
    ∫ x, (∫ y, f (x - y) ∂μ) * g x ∂volume =
      ∫ x, f x * (∫ y, g (x + y) ∂μ) ∂volume := by
  calc
    ∫ x, (∫ y, f (x - y) ∂μ) * g x ∂volume =
        ∫ x, ∫ y, f (x - y) * g x ∂μ ∂volume := by
          congr 1
          funext x
          exact (integral_mul_const (g x) (fun y : ℝ => f (x - y))).symm
    _ = ∫ y, ∫ x, f (x - y) * g x ∂volume ∂μ :=
      integral_integral_swap hLeft
    _ = ∫ y, ∫ x, f x * g (x + y) ∂volume ∂μ := by
      congr 1
      funext y
      simpa [sub_add_cancel] using
        (integral_sub_right_eq_self (fun x : ℝ => f x * g (x + y)) y)
    _ = ∫ x, ∫ y, f x * g (x + y) ∂μ ∂volume :=
      (integral_integral_swap hRight).symm
    _ = ∫ x, f x * (∫ y, g (x + y) ∂μ) ∂volume := by
      congr 1
      funext x
      rw [integral_const_mul]

/-- Conjugate `L^r` and `L^q` membership supplies both product-integrability
conditions for the real pairing identity. -/
theorem integrable_positiveEnergy_pair_products
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r q : ℝ} (hrq : r.HolderConjugate q)
    (f g : ℝ → ℝ)
    (hf : MemLp f (ENNReal.ofReal r) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Integrable (fun z : ℝ × ℝ => f (z.1 - z.2) * g z.1)
      (volume.prod μ) ∧
    Integrable (fun z : ℝ × ℝ => f z.1 * g (z.1 + z.2))
      (volume.prod μ) := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal q) 1 :=
    hrq.ennrealOfReal
  have hFSub : MemLp (fun z : ℝ × ℝ => f (z.1 - z.2))
      (ENNReal.ofReal r) (volume.prod μ) := by
    exact (hf.comp_fst μ).comp_measurePreserving
      (measurePreserving_sub_prod volume μ)
  have hGfst : MemLp (fun z : ℝ × ℝ => g z.1)
      (ENNReal.ofReal q) (volume.prod μ) := hg.comp_fst μ
  have hFfst : MemLp (fun z : ℝ × ℝ => f z.1)
      (ENNReal.ofReal r) (volume.prod μ) := hf.comp_fst μ
  have hGAdd : MemLp (fun z : ℝ × ℝ => g (z.1 + z.2))
      (ENNReal.ofReal q) (volume.prod μ) := by
    exact (hg.comp_fst μ).comp_measurePreserving
      (measurePreserving_add_prod volume μ)
  exact ⟨memLp_one_iff_integrable.mp (hFSub.mul hGfst),
    memLp_one_iff_integrable.mp (hFfst.mul hGAdd)⟩

/-- The finite-family energy pairing is bounded by the positive reflected
majorant and then by scalar Hölder. This is the scalar core of the upper
vector estimate in `lj:positivity`. -/
theorem finitePositiveEnergy_pairing_le
    {ι : Type*} [Fintype ι] {r q : ℝ}
    (hrq : r.HolderConjugate q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (u : ι → ℝ → ℝ) (hu : ∀ i, MemLp (u i) (ENNReal.ofReal r) volume)
    (hu0 : ∀ i x, 0 ≤ u i x)
    (g M : ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) volume)
    (hM : MemLp M (ENNReal.ofReal q) volume)
    (hM0 : ∀ x, 0 ≤ M x)
    (hmajor : ∀ᵐ x ∂volume, ∀ i,
      (∫ y, g (x + y) ∂(μ i)) ≤ M x) :
    (∫ x, (∑ i, ∫ y, u i (x - y) ∂(μ i)) * g x ∂volume) ≤
      (∫ x, (∑ i, u i x) ^ r ∂volume) ^ (1 / r) *
        (∫ x, M x ^ q ∂volume) ^ (1 / q) := by
  classical
  letI : ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal q) 1 :=
    hrq.ennrealOfReal
  have hU : MemLp (fun x => ∑ i, u i x)
      (ENNReal.ofReal r) volume :=
    memLp_finsetSum Finset.univ (fun i _ => hu i)
  have hU0 : ∀ x, 0 ≤ ∑ i, u i x := by
    intro x
    exact Finset.sum_nonneg (fun i _ => hu0 i x)
  have hUM : Integrable (fun x => (∑ i, u i x) * M x) volume :=
    memLp_one_iff_integrable.mp (hU.mul hM)
  have hpair (i : ι) :
      Integrable (fun x => (∫ y, u i (x - y) ∂(μ i)) * g x) volume ∧
      Integrable (fun x => u i x * (∫ y, g (x + y) ∂(μ i))) volume ∧
      (∫ x, (∫ y, u i (x - y) ∂(μ i)) * g x ∂volume) =
        ∫ x, u i x * (∫ y, g (x + y) ∂(μ i)) ∂volume := by
    letI : IsProbabilityMeasure (μ i) := hμ i
    obtain ⟨hLeft, hRight⟩ :=
      integrable_positiveEnergy_pair_products (μ i) hrq (u i) g (hu i) hg
    refine ⟨?_, ?_, integral_positiveEnergy_pairing (μ i) (u i) g hLeft hRight⟩
    · have h := hLeft.integral_prod_left
      convert h using 1
      ext x
      simp only [Prod.fst, Prod.snd]
      exact (integral_mul_const (g x) (fun y : ℝ => u i (x - y))).symm
    · have h := hRight.integral_prod_left
      convert h using 1
      ext x
      simp only [Prod.fst, Prod.snd]
      exact (integral_const_mul (u i x) (fun y : ℝ => g (x + y))).symm
  have hleft : Integrable
      (fun x => (∑ i, ∫ y, u i (x - y) ∂(μ i)) * g x) volume := by
    have hsum : Integrable
        (fun x => ∑ i, (∫ y, u i (x - y) ∂(μ i)) * g x) volume :=
      integrable_finsetSum Finset.univ (fun i _ => (hpair i).1)
    convert hsum using 1
    ext x
    rw [Finset.sum_mul]
  have hright : Integrable
      (fun x => ∑ i, u i x * (∫ y, g (x + y) ∂(μ i))) volume :=
    integrable_finsetSum Finset.univ (fun i _ => (hpair i).2.1)
  have heq : (∫ x, (∑ i, ∫ y, u i (x - y) ∂(μ i)) * g x ∂volume) =
      ∫ x, ∑ i, u i x * (∫ y, g (x + y) ∂(μ i)) ∂volume := by
    rw [show (fun x => (∑ i, ∫ y, u i (x - y) ∂(μ i)) * g x) =
      (fun x => ∑ i, (∫ y, u i (x - y) ∂(μ i)) * g x) by
        funext x; rw [Finset.sum_mul]]
    rw [integral_finsetSum Finset.univ (fun i _ => (hpair i).1),
      integral_finsetSum Finset.univ (fun i _ => (hpair i).2.1)]
    exact Finset.sum_congr rfl (fun i _ => (hpair i).2.2)
  calc
    _ = ∫ x, ∑ i, u i x * (∫ y, g (x + y) ∂(μ i)) ∂volume := heq
    _ ≤ ∫ x, (∑ i, u i x) * M x ∂volume := by
      apply integral_mono_ae hright hUM
      filter_upwards [hmajor] with x hx
      change (∑ i, u i x * (∫ y, g (x + y) ∂(μ i))) ≤
        (∑ i, u i x) * M x
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hx i) (hu0 i x)
    _ ≤ _ := integral_mul_le_Lp_mul_Lq_of_nonneg hrq
      (Filter.Eventually.of_forall hU0) (Filter.Eventually.of_forall hM0) hU hM

#print axioms integral_positiveEnergy_pairing
#print axioms integrable_positiveEnergy_pair_products
#print axioms finitePositiveEnergy_pairing_le

end

end FractionalPrimes.Literature.JSW

end
