module

public import FractionalPrimes.FourierSequence
public import Mathlib.Algebra.Star.Conjneg

/-!
# Adjoint integer kernels

The paper's adjoint kernel is conjugation followed by integer reflection.
This file verifies its coefficient mass and Fourier-symbol norm invariance.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

/-- The adjoint of an absolutely summable integer convolution kernel. -/
noncomputable def integerKernelAdjoint (K : IntegerL1Kernel) : IntegerL1Kernel where
  coeff := conjneg K.coeff
  summable_norm := by
    rw [show (fun m : ℤ => ‖conjneg K.coeff m‖) =
      (fun m : ℤ => ‖K.coeff m‖) ∘ (Equiv.neg ℤ) by
        funext m
        simp]
    exact (Equiv.neg ℤ).summable_iff.mpr K.summable_norm

/-- Coefficients of the adjoint kernel have the paper's stated form. -/
theorem integerKernelAdjoint_coeff (K : IntegerL1Kernel) (m : ℤ) :
    (integerKernelAdjoint K).coeff m = starRingEnd ℂ (K.coeff (-m)) := rfl

/-- Integer reflection and conjugation preserve the exact `ℓ¹` coefficient
mass of a kernel. -/
theorem integerKernelAdjoint_norm_tsum (K : IntegerL1Kernel) :
    ∑' m : ℤ, ‖(integerKernelAdjoint K).coeff m‖ = ∑' m : ℤ, ‖K.coeff m‖ := by
  unfold integerKernelAdjoint
  rw [show (fun m : ℤ => ‖conjneg K.coeff m‖) =
      (fun m : ℤ => ‖K.coeff m‖) ∘ (Equiv.neg ℤ) by
        funext m
        simp]
  exact (Equiv.neg ℤ).tsum_eq (fun m : ℤ => ‖K.coeff m‖)

/-- Integer reflection and conjugation preserve the extended coefficient
mass that occurs in the exact Young bound. -/
theorem integerKernelAdjoint_enorm_tsum (K : IntegerL1Kernel) :
    ∑' m : ℤ, ‖(integerKernelAdjoint K).coeff m‖ₑ =
      ∑' m : ℤ, ‖K.coeff m‖ₑ := by
  rw [show (fun m : ℤ => ‖(integerKernelAdjoint K).coeff m‖ₑ) =
      (fun m : ℤ => ‖K.coeff m‖ₑ) ∘ (Equiv.neg ℤ) by
        funext m
        simp [integerKernelAdjoint]]
  exact (Equiv.neg ℤ).tsum_eq (fun m : ℤ => ‖K.coeff m‖ₑ)

/-- The adjoint kernel obeys the same Young endpoint bound as the original
kernel, with exactly the same coefficient mass. -/
theorem eLpNorm_integerKernelConvolution_adjoint_le
    {p : ℝ≥0∞} (hp : 1 ≤ p) (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    eLpNorm (integerKernelConvolution (integerKernelAdjoint K) (f : ℤ → ℂ))
        p Measure.count ≤
      (∑' m : ℤ, ‖K.coeff m‖ₑ) *
        eLpNorm (f : ℤ → ℂ) p Measure.count := by
  calc
    eLpNorm (integerKernelConvolution (integerKernelAdjoint K) (f : ℤ → ℂ))
        p Measure.count ≤
      (∑' m : ℤ, ‖(integerKernelAdjoint K).coeff m‖ₑ) *
        eLpNorm (f : ℤ → ℂ) p Measure.count :=
      eLpNorm_integerKernelConvolution_le hp (integerKernelAdjoint K) f
    _ = (∑' m : ℤ, ‖K.coeff m‖ₑ) *
        eLpNorm (f : ℤ → ℂ) p Measure.count := by
      rw [integerKernelAdjoint_enorm_tsum]

/-- Subtraction by a fixed integer, bundled as an embedding for finite-sum
reindexing. -/
def subtractEmbedding (m : ℤ) : ℤ ↪ ℤ :=
  ⟨fun x => x - m, sub_left_injective⟩

/-- Reindex a finite sum by subtraction. -/
theorem sum_subtractEmbedding (m : ℤ) (t : Finset ℤ) (F : ℤ → ℂ) :
    ∑ x ∈ t, F (x - m) =
      ∑ y ∈ t.map (subtractEmbedding m), F y := by
  rw [Finset.sum_map]
  rfl

/-- The finite double-sum reindexing that underlies the convolution-adjoint
pairing formula. This is the exact finite algebraic calculation prescribed
by the blueprint before the support/density extension. -/
theorem finite_kernel_pairing_reindex
    (s t : Finset ℤ) (a f g : ℤ → ℂ) :
    ∑ x ∈ t, (∑ m ∈ s, a m * f (x - m)) * starRingEnd ℂ (g x) =
      ∑ m ∈ s, ∑ y ∈ t.map (subtractEmbedding m),
        f y * starRingEnd ℂ (starRingEnd ℂ (a m) * g (y + m)) := by
  classical
  calc
    _ = ∑ x ∈ t, ∑ m ∈ s,
        (a m * f (x - m)) * starRingEnd ℂ (g x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ∑ m ∈ s, ∑ x ∈ t,
        (a m * f (x - m)) * starRingEnd ℂ (g x) := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ s, ∑ y ∈ t.map (subtractEmbedding m),
        f y * starRingEnd ℂ (starRingEnd ℂ (a m) * g (y + m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      let H : ℤ → ℂ := fun y =>
        (a m * f y) * starRingEnd ℂ (g (y + m))
      calc
        ∑ x ∈ t, (a m * f (x - m)) * starRingEnd ℂ (g x) =
          ∑ x ∈ t, H (x - m) := by
            apply Finset.sum_congr rfl
            intro x hx
            dsimp [H]
            rw [sub_add_cancel]
        _ = ∑ y ∈ t.map (subtractEmbedding m), H y :=
          sum_subtractEmbedding m t H
        _ = ∑ y ∈ t.map (subtractEmbedding m),
            f y * starRingEnd ℂ (starRingEnd ℂ (a m) * g (y + m)) := by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [H]
          rw [map_mul]
          rw [starRingEnd_self_apply]
          ring

/-- The finite-support version of the convolution-adjoint pairing identity.
Both input functions are represented by finite support bounds, so this is the
literal finite reindexing step in the blueprint. -/
theorem finite_supported_pairing_adjoint
    (s t u : Finset ℤ) (a f g : ℤ → ℂ)
    (hf : ∀ y : ℤ, y ∉ t → f y = 0)
    (hg : ∀ x : ℤ, x ∉ u → g x = 0) :
    ∑ x ∈ u, (∑ m ∈ s, a m * f (x - m)) * starRingEnd ℂ (g x) =
      ∑ y ∈ t, f y * starRingEnd ℂ
        (∑ m ∈ s, starRingEnd ℂ (a m) * g (y + m)) := by
  classical
  calc
    _ = ∑ m ∈ s, ∑ x ∈ u,
        (a m * f (x - m)) * starRingEnd ℂ (g x) := by
      rw [show (fun x : ℤ => (∑ m ∈ s, a m * f (x - m)) *
          starRingEnd ℂ (g x)) =
        fun x => ∑ m ∈ s, (a m * f (x - m)) * starRingEnd ℂ (g x) by
          funext x
          rw [Finset.sum_mul]]
      rw [Finset.sum_comm]
    _ = ∑ m ∈ s, ∑ y ∈ t,
        (a m * f y) * starRingEnd ℂ (g (y + m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      let H : ℤ → ℂ := fun y =>
        (a m * f y) * starRingEnd ℂ (g (y + m))
      calc
        ∑ x ∈ u, (a m * f (x - m)) * starRingEnd ℂ (g x) =
            ∑ x ∈ u, H (x - m) := by
          apply Finset.sum_congr rfl
          intro x hx
          dsimp [H]
          rw [sub_add_cancel]
        _ = ∑ y ∈ u.map (subtractEmbedding m), H y :=
          sum_subtractEmbedding m u H
        _ = ∑ y ∈ t, H y := by
          let v := t ∪ u.map (subtractEmbedding m)
          have hq : ∑ y ∈ u.map (subtractEmbedding m), H y = ∑ y ∈ v, H y := by
            apply Finset.sum_subset Finset.subset_union_right
            intro y hyv hyq
            dsimp [H]
            have hgy : g (y + m) = 0 := by
              apply hg
              intro hyu
              apply hyq
              rw [Finset.mem_map]
              refine ⟨y + m, hyu, ?_⟩
              dsimp [subtractEmbedding]
              omega
            rw [hgy]
            simp
          have ht : ∑ y ∈ t, H y = ∑ y ∈ v, H y := by
            apply Finset.sum_subset Finset.subset_union_left
            intro y hyv hyt
            dsimp [H]
            rw [hf y hyt]
            simp
          exact hq.trans ht.symm
        _ = ∑ y ∈ t, (a m * f y) * starRingEnd ℂ (g (y + m)) := by
          rfl
    _ = ∑ y ∈ t, ∑ m ∈ s,
        f y * starRingEnd ℂ (starRingEnd ℂ (a m) * g (y + m)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro m hm
      rw [map_mul, starRingEnd_self_apply]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [map_sum, Finset.mul_sum]

/-- Convolution against finite coefficient support. -/
def finiteIntegerConvolution (s : Finset ℤ) (a f : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ m ∈ s, a m * f (x - m)

/-- The finite adjoint-convolution expression after the reindexing
`r = -m`. -/
def finiteIntegerAdjointConvolution
    (s : Finset ℤ) (a g : ℤ → ℂ) (y : ℤ) : ℂ :=
  ∑ m ∈ s, starRingEnd ℂ (a m) * g (y + m)

/-- Exact discrete complex pairing identity for finite-support convolution
and its adjoint. -/
theorem finiteSupportedDiscreteAdjointPairing
    (s t u : Finset ℤ) (a f g : ℤ → ℂ)
    (hf : ∀ y : ℤ, y ∉ t → f y = 0)
    (hg : ∀ x : ℤ, x ∉ u → g x = 0) :
    ∑ x ∈ u, finiteIntegerConvolution s a f x * starRingEnd ℂ (g x) =
      ∑ y ∈ t, f y * starRingEnd ℂ
        (finiteIntegerAdjointConvolution s a g y) := by
  simpa only [finiteIntegerConvolution, finiteIntegerAdjointConvolution]
    using finite_supported_pairing_adjoint s t u a f g hf hg

/-- The Fourier transform of the adjoint kernel is the complex conjugate of
the original Fourier transform. -/
theorem integerKernelFourierTransform_adjoint (K : IntegerL1Kernel) (ξ : ℝ) :
    integerKernelFourierTransform (integerKernelAdjoint K) ξ =
      starRingEnd ℂ (integerKernelFourierTransform K ξ) := by
  unfold integerKernelFourierTransform
  rw [Complex.conj_tsum]
  let F : ℤ → ℂ := fun n =>
    starRingEnd ℂ (K.coeff n * unitFrequencyPhase (-ξ * (n : ℝ)))
  rw [show (fun m : ℤ => (integerKernelAdjoint K).coeff m *
      unitFrequencyPhase (-ξ * (m : ℝ))) = F ∘ (Equiv.neg ℤ) by
        funext m
        dsimp [F, integerKernelAdjoint]
        rw [map_mul]
        rw [← unitFrequencyPhase_neg_eq_conj]
        congr 2
        simp only [Equiv.neg_apply]
        push_cast
        ring]
  exact (Equiv.neg ℤ).tsum_eq F

/-- The circle Fourier symbol of the adjoint kernel is pointwise conjugate to
the original symbol. -/
theorem integerKernelFourierSymbol_adjoint (K : IntegerL1Kernel) :
    integerKernelFourierSymbol (integerKernelAdjoint K) =
      fun x => starRingEnd ℂ (integerKernelFourierSymbol K x) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  funext x
  have hxmem : x ∈ ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ico 0 (0 + (1 : ℝ)) := by
    rw [AddCircle.coe_image_Ico_eq]
    exact Set.mem_univ x
  rcases hxmem with ⟨ξ, hξ, rfl⟩
  have hξ' : ξ ∈ Set.Ico 0 1 := by simpa using hξ
  rw [integerKernelFourierSymbol_coe_Ico (integerKernelAdjoint K) ξ hξ',
    integerKernelFourierSymbol_coe_Ico K ξ hξ']
  exact integerKernelFourierTransform_adjoint K ξ

/-- The adjoint kernel has exactly the same Fourier essential-supremum norm. -/
theorem eLpNormEssSup_integerKernelFourierSymbol_adjoint (K : IntegerL1Kernel) :
    eLpNormEssSup (integerKernelFourierSymbol (integerKernelAdjoint K))
        (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) =
      eLpNormEssSup (integerKernelFourierSymbol K)
        (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) := by
  rw [integerKernelFourierSymbol_adjoint]
  rw [eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
  congr 1
  funext x
  simp [enorm_eq_nnnorm]

end

end FractionalPrimes
