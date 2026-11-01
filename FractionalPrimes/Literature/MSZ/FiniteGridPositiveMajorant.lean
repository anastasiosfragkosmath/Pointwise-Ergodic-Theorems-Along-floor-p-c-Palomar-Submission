module

public import FractionalPrimes.FiniteMomentExhaustion
public import FractionalPrimes.Literature.MSZ.ConvolutionBounds

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped ENNReal

/-- The absolutely summable kernel obtained by subtracting two MSZ kernels. -/
noncomputable def integerKernelDifference
    (K₂ K₁ : IntegerL1Kernel) : IntegerL1Kernel where
  coeff := fun m => K₂.coeff m - K₁.coeff m
  summable_norm := by
    apply (K₂.summable_norm.add K₁.summable_norm).of_nonneg_of_le
      (fun m => norm_nonneg _)
    intro m
    exact norm_sub_le _ _

/-- The counting-measure `ℓ¹` mass of an absolutely summable complex kernel. -/
noncomputable def integerKernelL1Mass (K : IntegerL1Kernel) : ℝ :=
  ∑' m : ℤ, ‖K.coeff m‖

/-- The positive convolution majorant associated to the coefficientwise
absolute values of a complex kernel and a nonnegative real input. -/
noncomputable def integerKernelPositiveConvolution
    {p : ℝ≥0∞} (K : IntegerL1Kernel)
    (h : lp (fun _ : ℤ => ℝ) p) (x : ℤ) : ℝ :=
  ∑' m : ℤ, ‖K.coeff m‖ * h (x - m)

theorem integerKernelPositiveConvolution_summable
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (K : IntegerL1Kernel) (h : lp (fun _ : ℤ => ℝ) p)
    (hh : ∀ x, 0 ≤ h x) (x : ℤ) :
    Summable (fun m : ℤ => ‖K.coeff m‖ * h (x - m)) := by
  have hbound (m : ℤ) : h (x - m) ≤ ‖h‖ := by
    have hcoord := lp.norm_apply_le_norm hp0 h (x - m)
    rw [Real.norm_eq_abs, abs_of_nonneg (hh (x - m))] at hcoord
    exact hcoord
  apply (K.summable_norm.mul_right ‖h‖).of_nonneg_of_le
    (fun m => mul_nonneg (norm_nonneg _) (hh (x - m)))
  intro m
  exact mul_le_mul_of_nonneg_left (hbound m) (norm_nonneg _)

theorem integerKernelPositiveConvolution_nonneg
    {p : ℝ≥0∞} {K : IntegerL1Kernel}
    {h : lp (fun _ : ℤ => ℝ) p} (hh : ∀ x, 0 ≤ h x) (x : ℤ) :
    0 ≤ integerKernelPositiveConvolution K h x := by
  exact tsum_nonneg (fun m => mul_nonneg (norm_nonneg _) (hh (x - m)))

theorem integerKernelDifference_positiveConvolution_le
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (K₂ K₁ : IntegerL1Kernel) (h : lp (fun _ : ℤ => ℝ) p)
    (hh : ∀ x, 0 ≤ h x) (x : ℤ) :
    integerKernelPositiveConvolution (integerKernelDifference K₂ K₁) h x ≤
      integerKernelPositiveConvolution K₂ h x +
        integerKernelPositiveConvolution K₁ h x := by
  have hdiff := integerKernelPositiveConvolution_summable hp0 hpTop
    (integerKernelDifference K₂ K₁) h hh x
  have h₂ := integerKernelPositiveConvolution_summable hp0 hpTop K₂ h hh x
  have h₁ := integerKernelPositiveConvolution_summable hp0 hpTop K₁ h hh x
  have hterm (m : ℤ) :
      ‖K₂.coeff m - K₁.coeff m‖ * h (x - m) ≤
        ‖K₂.coeff m‖ * h (x - m) + ‖K₁.coeff m‖ * h (x - m) := by
    have hnorm : ‖K₂.coeff m - K₁.coeff m‖ ≤
        ‖K₂.coeff m‖ + ‖K₁.coeff m‖ := norm_sub_le _ _
    calc
      ‖K₂.coeff m - K₁.coeff m‖ * h (x - m) ≤
          (‖K₂.coeff m‖ + ‖K₁.coeff m‖) * h (x - m) :=
            mul_le_mul_of_nonneg_right hnorm (hh (x - m))
      _ = ‖K₂.coeff m‖ * h (x - m) +
          ‖K₁.coeff m‖ * h (x - m) := by ring
  calc
    integerKernelPositiveConvolution (integerKernelDifference K₂ K₁) h x ≤
        ∑' m : ℤ, (‖K₂.coeff m‖ * h (x - m) +
          ‖K₁.coeff m‖ * h (x - m)) := by
            exact hdiff.tsum_le_tsum hterm (h₂.add h₁)
    _ = integerKernelPositiveConvolution K₂ h x +
        integerKernelPositiveConvolution K₁ h x := by
          rw [integerKernelPositiveConvolution, integerKernelPositiveConvolution]
          exact Summable.tsum_add h₂ h₁

/-- The maximal positive convolution majorant of a finite family of kernel
increments. -/
noncomputable def finiteIncrementKernelPositiveMajorant
    {ι η : Type*} {p : ℝ≥0∞}
    (E : Finset η) (hE : E.Nonempty)
    (K : ι → IntegerL1Kernel) (left right : η → ι)
    (h : lp (fun _ : ℤ => ℝ) p) : ℤ → ℝ :=
  fun x => E.sup' hE (fun e =>
    integerKernelPositiveConvolution
      (integerKernelDifference (K (right e)) (K (left e))) h x)

theorem finiteIncrementKernelPositiveMajorant_nonneg
    {ι η : Type*} {p : ℝ≥0∞}
    (E : Finset η) (hE : E.Nonempty)
    (K : ι → IntegerL1Kernel) (left right : η → ι)
    (h : lp (fun _ : ℤ => ℝ) p) (hh : ∀ x, 0 ≤ h x) (x : ℤ) :
    0 ≤ finiteIncrementKernelPositiveMajorant E hE K left right h x := by
  obtain ⟨e, he, hsup⟩ := Finset.exists_mem_eq_sup' hE (fun e =>
    integerKernelPositiveConvolution
      (integerKernelDifference (K (right e)) (K (left e))) h x)
  change 0 ≤ E.sup' hE (fun e =>
    integerKernelPositiveConvolution
      (integerKernelDifference (K (right e)) (K (left e))) h x)
  rw [hsup]
  exact integerKernelPositiveConvolution_nonneg hh x

/-- If all endpoint positive convolutions are dominated by a finite-grid
maximal majorant, then the positive majorant for the entire finite increment
family has the exact factor-two bound. The assumptions are the endpoint
membership and maximal-norm clauses needed to instantiate `lm:finiteBounds`;
time-dependent kernel estimates are supplied separately. -/
theorem finiteIncrementKernelPositiveMajorant_norm_le
    {ι η : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (s : Finset ι) (_hs : s.Nonempty)
    (E : Finset η) (hE : E.Nonempty)
    (K : ι → IntegerL1Kernel) (left right : η → ι)
    (hleft : ∀ e ∈ E, left e ∈ s) (hright : ∀ e ∈ E, right e ∈ s)
    (h : lp (fun _ : ℤ => ℝ) p) (hh : ∀ x, 0 ≤ h x)
    (M : lp (fun _ : ℤ => ℝ) p) (hM : ∀ x, 0 ≤ M x)
    (B_KL : ℝ) (_hB_KL : 0 ≤ B_KL)
    (hEndpoint : ∀ i ∈ s, ∀ x,
      integerKernelPositiveConvolution (K i) h x ≤ M x)
    (hMaximalNorm : ‖M‖ ≤ B_KL * ‖h‖) :
    ∃ G : lp (fun _ : ℤ => ℝ) p,
      (∀ x, G x = finiteIncrementKernelPositiveMajorant E hE K left right h x) ∧
      ‖G‖ ≤ 2 * B_KL * ‖h‖ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  let g : ℤ → ℝ := finiteIncrementKernelPositiveMajorant E hE K left right h
  have hnormM : ∀ x, M x ≤ ‖M‖ := by
    intro x
    have hcoord := lp.norm_apply_le_norm hp0 M x
    rw [Real.norm_eq_abs, abs_of_nonneg (hM x)] at hcoord
    exact hcoord
  have hg_nonneg (x : ℤ) : 0 ≤ g x := by
    exact finiteIncrementKernelPositiveMajorant_nonneg E hE K left right h hh x
  have hg_le (x : ℤ) : g x ≤ 2 * M x := by
    change E.sup' hE (fun e =>
      integerKernelPositiveConvolution
        (integerKernelDifference (K (right e)) (K (left e))) h x) ≤ 2 * M x
    apply Finset.sup'_le hE
    intro e he
    have hpair := integerKernelDifference_positiveConvolution_le hp0 hpTop
      (K (right e)) (K (left e)) h hh x
    calc
      integerKernelPositiveConvolution
          (integerKernelDifference (K (right e)) (K (left e))) h x ≤
          integerKernelPositiveConvolution (K (right e)) h x +
            integerKernelPositiveConvolution (K (left e)) h x := hpair
      _ ≤ M x + M x := add_le_add (hEndpoint (right e) (hright e he) x)
        (hEndpoint (left e) (hleft e he) x)
      _ = 2 * M x := by ring
  have hC : 0 ≤ (2 * ‖M‖) ^ p.toReal := by positivity
  have hfinite : ∀ u : Finset ℤ,
      ∑ x ∈ u, ‖g x‖ ^ p.toReal ≤ (2 * ‖M‖) ^ p.toReal := by
    intro u
    calc
      ∑ x ∈ u, ‖g x‖ ^ p.toReal ≤
          ∑ x ∈ u, 2 ^ p.toReal * (M x) ^ p.toReal := by
            apply Finset.sum_le_sum
            intro x hx
            have hgx : ‖g x‖ = g x := Real.norm_of_nonneg (hg_nonneg x)
            have hpow : (2 * M x) ^ p.toReal =
                2 ^ p.toReal * (M x) ^ p.toReal :=
              Real.mul_rpow (by norm_num) (hM x)
            rw [hgx, ← hpow]
            exact Real.rpow_le_rpow (hg_nonneg x) (hg_le x) hp.le
      _ = 2 ^ p.toReal * (∑ x ∈ u, (M x) ^ p.toReal) := by
            rw [Finset.mul_sum]
      _ ≤ 2 ^ p.toReal * ‖M‖ ^ p.toReal := by
            have hsumM :
                ∑ x ∈ u, (M x) ^ p.toReal ≤ ‖M‖ ^ p.toReal := by
              convert lp.sum_rpow_le_norm_rpow hp M u using 1
              apply Finset.sum_congr rfl
              intro x hx
              rw [Real.norm_of_nonneg (hM x)]
            exact mul_le_mul_of_nonneg_left hsumM (by positivity)
      _ = (2 * ‖M‖) ^ p.toReal := by
            symm
            exact Real.mul_rpow (by norm_num) (norm_nonneg M)
  let G : lp (fun _ : ℤ => ℝ) p :=
    lpOfUniformFiniteMomentBound hp0 hpTop g hC hfinite
  have hnormG : ‖G‖ ≤ 2 * ‖M‖ := by
    calc
      ‖G‖ ≤ ((2 * ‖M‖) ^ p.toReal) ^ (1 / p.toReal) := by
        simpa [G] using
          (lpOfUniformFiniteMomentBound_norm_le hp0 hpTop g hC hfinite)
      _ = 2 * ‖M‖ := by
        simpa [one_div] using
          (Real.rpow_rpow_inv (by positivity : 0 ≤ 2 * ‖M‖) (ne_of_gt hp))
  refine ⟨G, ?_, ?_⟩
  · intro x
    change lpOfUniformFiniteMomentBound hp0 hpTop g hC hfinite x =
      finiteIncrementKernelPositiveMajorant E hE K left right h x
    rfl
  · calc
      ‖G‖ ≤ 2 * ‖M‖ := hnormG
      _ ≤ 2 * (B_KL * ‖h‖) :=
        mul_le_mul_of_nonneg_left hMaximalNorm (by norm_num)
      _ = 2 * B_KL * ‖h‖ := by ring

/-- The exact `E₀` scalar adapter in `lm:finiteBounds`: a time-increment
kernel bound `D·2^(−l)` is bounded by `max(1,D)·2^(−l)`. -/
theorem finiteIncrementKernelMass_le_E0
    {ι η : Type*} (E : Finset η) (D : ℝ) (_hD : 0 ≤ D) (l : ℕ)
    (K : ι → IntegerL1Kernel) (left right : η → ι)
    (hmass : ∀ e ∈ E,
      integerKernelL1Mass (integerKernelDifference (K (right e)) (K (left e))) ≤
        D * (2 : ℝ) ^ (-(l : ℤ))) :
    ∀ e ∈ E,
      integerKernelL1Mass (integerKernelDifference (K (right e)) (K (left e))) ≤
        max 1 D * (2 : ℝ) ^ (-(l : ℤ)) := by
  intro e he
  calc
    integerKernelL1Mass (integerKernelDifference (K (right e)) (K (left e))) ≤
        D * (2 : ℝ) ^ (-(l : ℤ)) := hmass e he
    _ ≤ max 1 D * (2 : ℝ) ^ (-(l : ℤ)) := by
      exact mul_le_mul_of_nonneg_right (le_max_right 1 D) (by positivity)

end FractionalPrimes.Literature.MSZ

end
