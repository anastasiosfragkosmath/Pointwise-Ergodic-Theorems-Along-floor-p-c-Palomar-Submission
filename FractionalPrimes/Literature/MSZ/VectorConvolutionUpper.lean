module

public import FractionalPrimes.Literature.MSZ.VectorConvolutionLowerAssembly
public import FractionalPrimes.AdjointKernel

@[expose] public section

open scoped ENNReal NNReal

namespace FractionalPrimes.Literature.MSZ

noncomputable section

/-- Reflection on a real-valued counting `lp` sequence. -/
noncomputable def mszReflectRealLp {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (h : lp (fun _ : ℤ => ℝ) p) : lp (fun _ : ℤ => ℝ) p :=
  ⟨fun x => h (-x), by
    change Memℓp (fun x : ℤ => h (-x)) p
    rw [memℓp_gen_iff hp]
    exact (lp.memℓp h).summable hp |>.comp_injective (fun _ _ hx => neg_injective hx)⟩

@[simp]
theorem mszReflectRealLp_apply {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (h : lp (fun _ : ℤ => ℝ) p) (x : ℤ) :
    mszReflectRealLp hp h x = h (-x) := rfl

theorem mszReflectRealLp_norm {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (h : lp (fun _ : ℤ => ℝ) p) :
    ‖mszReflectRealLp hp h‖ = ‖h‖ := by
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  congr 1
  change (∑' x : ℤ, ‖h (-x)‖ ^ p.toReal) = _
  rw [show (fun x : ℤ => ‖h (-x)‖ ^ p.toReal) =
    (fun x : ℤ => ‖h x‖ ^ p.toReal) ∘ Equiv.neg ℤ by funext x; simp]
  simpa [Function.comp_def] using
    (Equiv.neg ℤ).tsum_eq (fun x : ℤ => ‖h x‖ ^ p.toReal)

/-- The positive convolution of an adjoint kernel is the reflected original
positive convolution. -/
theorem integerKernelPositiveConvolution_adjoint_eq_reflection
    {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (K : IntegerL1Kernel) (h : lp (fun _ : ℤ => ℝ) p)
    (x : ℤ) :
    integerKernelPositiveConvolution (integerKernelAdjoint K) h x =
      integerKernelPositiveConvolution K (mszReflectRealLp hp h) (-x) := by
  rw [integerKernelPositiveConvolution, integerKernelPositiveConvolution]
  calc
    (∑' m : ℤ, ‖(integerKernelAdjoint K).coeff m‖ * h (x - m)) =
        ∑' m : ℤ, ‖K.coeff (-m)‖ * h (x - m) := by
          apply tsum_congr
          intro m
          simp [integerKernelAdjoint_coeff]
    _ = ∑' m : ℤ, ‖K.coeff m‖ * h (x + m) :=
          (Equiv.neg ℤ).tsum_eq (fun m : ℤ => ‖K.coeff m‖ * h (x + m))
    _ = ∑' m : ℤ, ‖K.coeff m‖ *
        mszReflectRealLp hp h (-x - m) := by
          apply tsum_congr
          intro m
          simp [sub_eq_add_neg, add_comm]

/-- The finite positive maximal function of the adjoint family is the
reflection of the original maximal function. -/
theorem integerKernelPositiveConvolutionMax_adjoint_eq_reflection
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (K : ι → IntegerL1Kernel) (h : lp (fun _ : ℤ => ℝ) p)
    (hh : ∀ x, 0 ≤ h x) (x : ℤ) :
    integerKernelPositiveConvolutionMax
        (fun i => integerKernelAdjoint (K i)) h hh x =
      integerKernelPositiveConvolutionMax K (mszReflectRealLp hp h)
        (fun y => hh (-y)) (-x) := by
  classical
  simp only [integerKernelPositiveConvolutionMax]
  apply congrArg (fun z : ℝ≥0 => (z : ℝ))
  apply Finset.sup_congr rfl
  intro i hi
  apply Subtype.ext
  exact integerKernelPositiveConvolution_adjoint_eq_reflection hp (K i) h x

/-- Reflection transfers the exact positive maximal hypothesis in
`vectorLower_normBound` to the adjoint kernel family. -/
theorem vectorLowerAdjointMaximalBound
    {ι : Type*} [Fintype ι] {q : ℝ} (hq : 1 < q)
    (K : ι → IntegerL1Kernel) (B : ℝ)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q))
    (hh : ∀ x, 0 ≤ h x) :
    ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
      (∀ x, M x = integerKernelPositiveConvolutionMax
        (fun i => integerKernelAdjoint (K i)) h hh x) ∧
        ‖M‖ ≤ B * ‖h‖ := by
  classical
  let p : ℝ≥0∞ := ENNReal.ofReal q
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hp : 0 < p.toReal := by
    dsimp [p]
    rw [ENNReal.toReal_ofReal hqpos.le]
    exact hqpos
  let hR : lp (fun _ : ℤ => ℝ) p := mszReflectRealLp hp h
  have hhR : ∀ x, 0 ≤ hR x := by
    intro x
    exact hh (-x)
  obtain ⟨M, hM, hMnorm⟩ := hmax hR hhR
  let MR : lp (fun _ : ℤ => ℝ) p := mszReflectRealLp hp M
  refine ⟨MR, ?_, ?_⟩
  · intro x
    calc
      MR x = M (-x) := rfl
      _ = integerKernelPositiveConvolutionMax K hR hhR (-x) := hM (-x)
      _ = integerKernelPositiveConvolutionMax
          (fun i => integerKernelAdjoint (K i)) h hh x :=
            (integerKernelPositiveConvolutionMax_adjoint_eq_reflection hp K h hh x).symm
  · calc
      ‖MR‖ = ‖M‖ := mszReflectRealLp_norm hp M
      _ ≤ B * ‖hR‖ := hMnorm
      _ = B * ‖h‖ := by rw [mszReflectRealLp_norm hp h]

end

end FractionalPrimes.Literature.MSZ

end
