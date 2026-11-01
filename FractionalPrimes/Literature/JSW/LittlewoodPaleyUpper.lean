module

public import FractionalPrimes.Literature.JSW.ConvolutionCZBound
public import FractionalPrimes.Literature.JSW.BroadScaleLpDecay
public import FractionalPrimes.Literature.JSW.LpConvolutionDenseConsistency
public import FractionalPrimes.Literature.JSW.SignMomentLowerBound
public import FractionalPrimes.Literature.JSW.VectorDuality
public import FractionalPrimes.Literature.Harmonic.SchwartzCutoff

/-!
# Littlewood--Paley upper square estimate and resolution

This file formalizes `lj:littlewood-paley` with the cutoff and constants from
the blueprint.  The multipliers, inverse Fourier kernels, and finite signed
kernel estimates are kept explicit so that the `L^p` and `L^2` realizations
can be compared without changing the target statement.
-/

@[expose] public section

open MeasureTheory FourierTransform SchwartzMap
open Filter Topology
open scoped ContDiff ENNReal FourierTransform

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The Littlewood--Paley cutoff difference `p_b(ξ)=χ(ξ)-χ(bξ)`. -/
def littlewoodPaleyCutoffDifference (b ξ : ℝ) : ℂ :=
  (χ ξ : ℂ) - (χ (b * ξ) : ℂ)

theorem littlewoodPaleyCutoffDifference_smooth (b : ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (littlewoodPaleyCutoffDifference b) := by
  unfold littlewoodPaleyCutoffDifference
  have hchi : ContDiff ℝ (∞ : ℕ∞ω) (fun ξ : ℝ => (χ ξ : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp chi_contDiff
  have hscaled : ContDiff ℝ (∞ : ℕ∞ω) (fun ξ : ℝ => (χ (b * ξ) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (chi_contDiff.comp (contDiff_const.mul contDiff_id))
  exact hchi.sub hscaled

theorem littlewoodPaleyCutoffDifference_hasCompactSupport (b : ℝ) (hb : b ≠ 0) :
    HasCompactSupport (littlewoodPaleyCutoffDifference b) := by
  unfold littlewoodPaleyCutoffDifference
  have hchi : HasCompactSupport (fun ξ : ℝ => (χ ξ : ℂ)) := by
    exact chi_hasCompactSupport.comp_left
      (g := fun y : ℝ => (y : ℂ)) (by simp)
  have hscaled : HasCompactSupport (fun ξ : ℝ => (χ (b * ξ) : ℂ)) := by
    have h := chi_hasCompactSupport.comp_smul (c := b) hb
    have h' : HasCompactSupport (fun ξ : ℝ => (χ (b • ξ) : ℂ)) := by
      exact h.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)
    simpa [smul_eq_mul] using h'
  exact hchi.sub hscaled

/-- The cutoff difference regarded as an element of Schwartz space. -/
def littlewoodPaleyCutoffSchwartz (b : ℝ) (hb : b ≠ 0) : SchwartzMap ℝ ℂ :=
  (littlewoodPaleyCutoffDifference_hasCompactSupport b hb).toSchwartzMap
    (littlewoodPaleyCutoffDifference_smooth b)

/-- The inverse Fourier transform `q_b=𝓕⁻¹p_b` as a Schwartz function. -/
def littlewoodPaleyKernelSchwartz (b : ℝ) (hb : b ≠ 0) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (littlewoodPaleyCutoffSchwartz b hb)

/-- The pointwise inverse Fourier kernel used by the `L^p` convolution model. -/
def littlewoodPaleyKernel (b : ℝ) (hb : b ≠ 0) : ℝ → ℂ :=
  littlewoodPaleyKernelSchwartz b hb

/-- Fourier inversion identifies the forward transform of `q_b` with its
frequency cutoff. -/
theorem fourier_littlewoodPaleyKernelSchwartz (b : ℝ) (hb : b ≠ 0) :
    𝓕 (littlewoodPaleyKernelSchwartz b hb) = littlewoodPaleyCutoffSchwartz b hb := by
  change 𝓕 (𝓕⁻ (littlewoodPaleyCutoffSchwartz b hb)) = _
  exact FourierTransform.fourier_fourierInv_eq _

theorem fourier_littlewoodPaleyKernel (b : ℝ) (hb : b ≠ 0) (ξ : ℝ) :
    𝓕 (littlewoodPaleyKernelSchwartz b hb) ξ = littlewoodPaleyCutoffDifference b ξ := by
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f ξ)
    (fourier_littlewoodPaleyKernelSchwartz b hb)
  simpa [littlewoodPaleyCutoffSchwartz] using h

theorem littlewoodPaleyKernel_fourierIntegral (b : ℝ) (hb : b ≠ 0)
    (ξ : ℝ) :
    ∫ x : ℝ, littlewoodPaleyKernel b hb x *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume =
      littlewoodPaleyCutoffDifference b ξ := by
  have h := fourier_littlewoodPaleyKernel b hb ξ
  change 𝓕 (littlewoodPaleyKernel b hb) ξ = _ at h
  rw [Real.fourier_eq'] at h
  simpa [littlewoodPaleyKernel, littlewoodPaleyKernelSchwartz,
    littlewoodPaleyCutoffSchwartz, Real.fourierChar_apply, Real.inner_apply,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- The exact supremum seminorm `Q_b` appearing in the blueprint. -/
def littlewoodPaleyQ (b : ℝ) (hb : b ≠ 0) : ℝ :=
  sSup (Set.range fun x : ℝ =>
    (1 + |x|) ^ 3 * ‖deriv (littlewoodPaleyKernel b hb) x‖)

private def littlewoodPaleyDerivativeBound0 (b : ℝ) (hb : b ≠ 0) : ℝ :=
  (2 * Real.pi : ℝ) ^ ((1 : ℤ)) *
    ∫ ξ : ℝ, ‖iteratedDeriv 0
      (fun y : ℝ => (y : ℂ) * littlewoodPaleyCutoffSchwartz b hb y) ξ‖

private def littlewoodPaleyDerivativeBound3 (b : ℝ) (hb : b ≠ 0) : ℝ :=
  (2 * Real.pi : ℝ) ^ ((1 : ℤ) - (3 : ℤ)) *
    ∫ ξ : ℝ, ‖iteratedDeriv 3
      (fun y : ℝ => (y : ℂ) * littlewoodPaleyCutoffSchwartz b hb y) ξ‖

/-- The weighted derivative supremum is finite; the low and high spatial
regions are controlled by the zero and third weighted Schwartz estimates. -/
theorem littlewoodPaleyQ_bounded (b : ℝ) (hb : b ≠ 0) :
    BddAbove (Set.range fun x : ℝ =>
      (1 + |x|) ^ 3 * ‖deriv (littlewoodPaleyKernel b hb) x‖) := by
  let cutoff := littlewoodPaleyCutoffSchwartz b hb
  have hM0 : 0 ≤ littlewoodPaleyDerivativeBound0 b hb := by
    dsimp [littlewoodPaleyDerivativeBound0]
    positivity
  have hM3 : 0 ≤ littlewoodPaleyDerivativeBound3 b hb := by
    dsimp [littlewoodPaleyDerivativeBound3]
    positivity
  refine ⟨8 * (littlewoodPaleyDerivativeBound0 b hb +
      littlewoodPaleyDerivativeBound3 b hb), ?_⟩
  intro z hz
  rcases hz with ⟨x, rfl⟩
  have hzero := FractionalPrimes.Literature.Harmonic.inverseFourierCutoffSchwartz_pointwise_bound
    cutoff 1 0 x
  have hthird := FractionalPrimes.Literature.Harmonic.inverseFourierCutoffSchwartz_pointwise_bound
    cutoff 1 3 x
  have hderiv0 : ‖deriv (littlewoodPaleyKernel b hb) x‖ ≤
      littlewoodPaleyDerivativeBound0 b hb := by
    simpa [cutoff, littlewoodPaleyKernel, littlewoodPaleyKernelSchwartz,
      littlewoodPaleyDerivativeBound0, iteratedDeriv_succ] using hzero
  have hderiv3 : |x| ^ 3 * ‖deriv (littlewoodPaleyKernel b hb) x‖ ≤
      littlewoodPaleyDerivativeBound3 b hb := by
    have h := hthird
    simpa [cutoff, littlewoodPaleyKernel, littlewoodPaleyKernelSchwartz,
      littlewoodPaleyDerivativeBound3, iteratedDeriv_succ, norm_mul, norm_pow,
      Complex.norm_real, mul_comm, mul_left_comm, mul_assoc] using h
  have hnonneg : 0 ≤ ‖deriv (littlewoodPaleyKernel b hb) x‖ := norm_nonneg _
  have hweight : (1 + |x|) ^ 3 * ‖deriv (littlewoodPaleyKernel b hb) x‖ ≤
      8 * (littlewoodPaleyDerivativeBound0 b hb +
        littlewoodPaleyDerivativeBound3 b hb) := by
    by_cases hx : |x| ≤ 1
    · have hfactor : (1 + |x|) ^ 3 ≤ 8 := by
        calc
          (1 + |x|) ^ 3 ≤ (2 : ℝ) ^ 3 := by gcongr <;> linarith [abs_nonneg x]
          _ = 8 := by norm_num
      calc
        _ ≤ 8 * ‖deriv (littlewoodPaleyKernel b hb) x‖ := by
          exact mul_le_mul_of_nonneg_right hfactor hnonneg
        _ ≤ 8 * littlewoodPaleyDerivativeBound0 b hb := by
          simpa using mul_le_mul_of_nonneg_left hderiv0 (by norm_num : 0 ≤ (8 : ℝ))
        _ ≤ _ := by nlinarith [hM3]
    · have hx' : 1 ≤ |x| := le_of_not_ge hx
      have hfactor : (1 + |x|) ^ 3 ≤ 8 * |x| ^ 3 := by
        calc
          (1 + |x|) ^ 3 ≤ (2 * |x|) ^ 3 := by gcongr <;> linarith
          _ = 8 * |x| ^ 3 := by ring
      calc
        _ ≤ 8 * (|x| ^ 3 * ‖deriv (littlewoodPaleyKernel b hb) x‖) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfactor hnonneg
        _ ≤ 8 * littlewoodPaleyDerivativeBound3 b hb :=
          mul_le_mul_of_nonneg_left hderiv3 (by norm_num)
        _ ≤ _ := by nlinarith [hM0]
  exact hweight

theorem littlewoodPaleyQ_nonneg (b : ℝ) (hb : b ≠ 0) :
    0 ≤ littlewoodPaleyQ b hb := by
  apply le_trans _ (le_csSup (littlewoodPaleyQ_bounded b hb) ⟨0, rfl⟩)
  positivity

theorem littlewoodPaleyQ_pointwise (b : ℝ) (hb : b ≠ 0) (x : ℝ) :
    (1 + |x|) ^ 3 * ‖deriv (littlewoodPaleyKernel b hb) x‖ ≤
      littlewoodPaleyQ b hb := by
  exact le_csSup (littlewoodPaleyQ_bounded b hb) ⟨x, rfl⟩

theorem littlewoodPaleyKernel_smooth (b : ℝ) (hb : b ≠ 0) :
    ContDiff ℝ (∞ : ℕ∞ω) (littlewoodPaleyKernel b hb) := by
  exact (littlewoodPaleyKernelSchwartz b hb).smooth ⊤

theorem littlewoodPaleyKernel_integrable (b : ℝ) (hb : b ≠ 0) :
    Integrable (littlewoodPaleyKernel b hb) volume := by
  exact (littlewoodPaleyKernelSchwartz b hb).integrable

/-- The kernel at scale `b^n`, in the exact normalization of the blueprint. -/
def littlewoodPaleyScaledKernel (b : ℝ) (hb : b ≠ 0) (n : ℤ) (x : ℝ) : ℂ :=
  ((b ^ n)⁻¹ : ℝ) • littlewoodPaleyKernel b hb (x / b ^ n)

theorem littlewoodPaleyScaledKernel_smooth {b : ℝ} (hb : b ≠ 0)
    (n : ℤ) : ContDiff ℝ (∞ : ℕ∞ω) (littlewoodPaleyScaledKernel b hb n) := by
  change ContDiff ℝ (∞ : ℕ∞ω)
    (fun x : ℝ => ((b ^ n)⁻¹ : ℝ) • littlewoodPaleyKernel b hb (x / b ^ n))
  have ht : b ^ n ≠ 0 := zpow_ne_zero n hb
  have hscale : ContDiff ℝ (∞ : ℕ∞ω) (fun x : ℝ => x / b ^ n) := by
    exact contDiff_id.div_const _
  have hcomp := (littlewoodPaleyKernel_smooth b hb).comp hscale
  exact hcomp.const_smul ((b ^ n)⁻¹ : ℝ)

theorem littlewoodPaleyScaledKernel_integrable {b : ℝ} (hb : b ≠ 0)
    (n : ℤ) : Integrable (littlewoodPaleyScaledKernel b hb n) volume := by
  change Integrable
    (fun x : ℝ => ((b ^ n)⁻¹ : ℝ) • littlewoodPaleyKernel b hb (x / b ^ n)) volume
  have ht : b ^ n ≠ 0 := zpow_ne_zero n hb
  have hcomp := (littlewoodPaleyKernel_integrable b hb).comp_div ht
  exact Integrable.smul ((b ^ n)⁻¹ : ℝ) hcomp

theorem littlewoodPaleyScaledKernel_fourierIntegral {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (n : ℤ) (ξ : ℝ) :
    ∫ x : ℝ, littlewoodPaleyScaledKernel b hb₀ n x *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume =
      littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
  let t : ℝ := b ^ n
  have ht : 0 < t := by
    dsimp [t]
    exact zpow_pos (by linarith) n
  let g : ℝ → ℂ := fun y => littlewoodPaleyKernel b hb₀ y *
    (Real.fourierChar (-(y * (t * ξ))) : ℂ)
  have hcomp := Measure.integral_comp_mul_left g t⁻¹
  have hcomp' :
      ∫ x : ℝ, g (t⁻¹ * x) ∂volume = t • ∫ y : ℝ, g y ∂volume := by
    simpa [abs_of_pos ht] using hcomp
  have hqarg (x : ℝ) : x / t = t⁻¹ * x := by
    field_simp [ne_of_gt ht]
  have hphase (x : ℝ) :
      (Real.fourierChar (-(x * ξ)) : ℂ) =
        (Real.fourierChar (-((t⁻¹ * x) * (t * ξ))) : ℂ) := by
    congr 1
    field_simp [ne_of_gt ht]
    rfl
  have hchange :
      ∫ x : ℝ, littlewoodPaleyKernel b hb₀ (x / t) *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume =
      ∫ x : ℝ, g (t⁻¹ * x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [g]
    rw [hqarg x, hphase x]
  have hpoint (x : ℝ) :
      littlewoodPaleyScaledKernel b hb₀ n x *
        (Real.fourierChar (-(x * ξ)) : ℂ) =
      t⁻¹ • (littlewoodPaleyKernel b hb₀ (x / t) *
        (Real.fourierChar (-(x * ξ)) : ℂ)) := by
    simp [littlewoodPaleyScaledKernel, t, smul_eq_mul]
    ring
  calc
    ∫ x : ℝ, littlewoodPaleyScaledKernel b hb₀ n x *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume =
        t⁻¹ • ∫ x : ℝ, littlewoodPaleyKernel b hb₀ (x / t) *
          (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume := by
          rw [← integral_smul]
          apply integral_congr_ae
          filter_upwards [] with x
          exact hpoint x
    _ = t⁻¹ • ∫ x : ℝ, g (t⁻¹ * x) ∂volume := by rw [hchange]
    _ = t⁻¹ • (t • ∫ y : ℝ, g y ∂volume) := by rw [hcomp']
    _ = ∫ y : ℝ, g y ∂volume := by
      rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    _ = littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
      simpa [g, t, mul_assoc, mul_left_comm, mul_comm] using
        littlewoodPaleyKernel_fourierIntegral b hb₀ (t * ξ)

theorem deriv_littlewoodPaleyScaledKernel {b : ℝ} (hb : b ≠ 0)
    (n : ℤ) (x : ℝ) :
    deriv (littlewoodPaleyScaledKernel b hb n) x =
      ((b ^ n)⁻¹ : ℝ) • (((b ^ n)⁻¹ : ℝ) •
        deriv (littlewoodPaleyKernel b hb) (x / b ^ n)) := by
  have ht : b ^ n ≠ 0 := zpow_ne_zero n hb
  have hinner : HasDerivAt (fun y : ℝ => y / b ^ n) ((b ^ n)⁻¹) x := by
    simpa using (hasDerivAt_id x).div_const (b ^ n)
  have hkernel : HasDerivAt (littlewoodPaleyKernel b hb)
      (deriv (littlewoodPaleyKernel b hb) (x / b ^ n)) (x / b ^ n) := by
    exact ((littlewoodPaleyKernel_smooth b hb).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hcomp := hkernel.scomp x hinner
  have hscaled := hcomp.const_smul ((b ^ n)⁻¹ : ℝ)
  change deriv (fun y : ℝ => ((b ^ n)⁻¹ : ℝ) •
      littlewoodPaleyKernel b hb (y / b ^ n)) x = _
  exact hscaled.deriv

theorem littlewoodPaleyScaledKernel_derivative_bound {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (n : ℤ) {x : ℝ} (hx : x ≠ 0) :
    ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ ≤
      littlewoodPaleyQ b hb₀ / |x| ^ 2 := by
  let t : ℝ := b ^ n
  let u : ℝ := |x| / t
  have ht : 0 < t := by
    dsimp [t]
    exact zpow_pos (by linarith) n
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hu : 0 < u := div_pos hxabs ht
  have hratio : |x / t| = u := by
    rw [abs_div, abs_of_pos ht]
  have hQ := littlewoodPaleyQ_pointwise b hb₀ (x / t)
  have hq : ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖ ≤
      littlewoodPaleyQ b hb₀ / (1 + u) ^ 3 := by
    apply (le_div_iff₀ (by positivity : 0 < (1 + u) ^ 3)).2
    simpa [hratio, mul_comm] using hQ
  have hderiv := deriv_littlewoodPaleyScaledKernel hb₀ n x
  have hnorm : ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ =
      t⁻¹ * (t⁻¹ * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖) := by
    rw [hderiv]
    simp [t, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < b),
      abs_of_pos (inv_pos.mpr ht)]
  rw [hnorm]
  have hqnonneg : 0 ≤ ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖ := norm_nonneg _
  have hQnonneg := littlewoodPaleyQ_nonneg b hb₀
  have hsmall : u ^ 2 ≤ (1 + u) ^ 3 := by nlinarith [sq_nonneg u]
  calc
    t⁻¹ * (t⁻¹ * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖) ≤
        t⁻¹ * (t⁻¹ * (littlewoodPaleyQ b hb₀ / (1 + u) ^ 3)) := by
      gcongr
    _ = littlewoodPaleyQ b hb₀ / (t ^ 2 * (1 + u) ^ 3) := by
      field_simp [ne_of_gt ht]
    _ ≤ littlewoodPaleyQ b hb₀ / (t ^ 2 * u ^ 2) := by
      apply div_le_div_of_nonneg_left hQnonneg
      · positivity
      · nlinarith [hsmall]
    _ = littlewoodPaleyQ b hb₀ / |x| ^ 2 := by
      have hxu : |x| = t * u := by
        dsimp [u]
        field_simp [ne_of_gt ht]
      rw [hxu]
      ring

theorem littlewoodPaleyScaledKernel_derivative_bound_low {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (n : ℤ) {x : ℝ} (hx : x ≠ 0) :
    ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ ≤
      littlewoodPaleyQ b hb₀ * b ^ n / |x| ^ 3 := by
  let t : ℝ := b ^ n
  let u : ℝ := |x| / t
  have ht : 0 < t := by
    dsimp [t]
    exact zpow_pos (by linarith) n
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hu : 0 < u := div_pos hxabs ht
  have hratio : |x / t| = u := by
    rw [abs_div, abs_of_pos ht]
  have hQ := littlewoodPaleyQ_pointwise b hb₀ (x / t)
  have hq : ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖ ≤
      littlewoodPaleyQ b hb₀ / (1 + u) ^ 3 := by
    apply (le_div_iff₀ (by positivity : 0 < (1 + u) ^ 3)).2
    simpa [hratio, mul_comm] using hQ
  have hderiv := deriv_littlewoodPaleyScaledKernel hb₀ n x
  have hnorm : ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ =
      t⁻¹ * (t⁻¹ * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖) := by
    rw [hderiv]
    simp [t, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < b), abs_of_pos (inv_pos.mpr ht)]
  have hsmall : u ^ 3 ≤ (1 + u) ^ 3 := by nlinarith [hu]
  have hqmul : u ^ 3 * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖ ≤
      littlewoodPaleyQ b hb₀ := by
    calc
      u ^ 3 * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖ ≤
          (1 + u) ^ 3 * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖ :=
        mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ ≤ littlewoodPaleyQ b hb₀ := by
        simpa [hratio] using hQ
  have hfactor : t⁻¹ * (t⁻¹ * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖) =
      (t / |x| ^ 3) *
        (u ^ 3 * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖) := by
    dsimp [u]
    field_simp [ne_of_gt ht, ne_of_gt hxabs]
  rw [hnorm]
  calc
    t⁻¹ * (t⁻¹ * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖) =
        (t / |x| ^ 3) *
          (u ^ 3 * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖) := hfactor
    _ ≤ (t / |x| ^ 3) * littlewoodPaleyQ b hb₀ :=
      mul_le_mul_of_nonneg_left hqmul (by positivity)
    _ = littlewoodPaleyQ b hb₀ * b ^ n / |x| ^ 3 := by
      dsimp [t]
      ring

theorem littlewoodPaleyScaledKernel_derivative_bound_high {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (n : ℤ) (x : ℝ) :
    ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ ≤
      littlewoodPaleyQ b hb₀ * b ^ (-2 * n : ℤ) := by
  let t : ℝ := b ^ n
  let u : ℝ := |x| / t
  have ht : 0 < t := by
    dsimp [t]
    exact zpow_pos (by linarith) n
  have hQ := littlewoodPaleyQ_pointwise b hb₀ (x / t)
  have hq : ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖ ≤
      littlewoodPaleyQ b hb₀ := by
    have hbase : 1 ≤ 1 + |x / t| := by linarith [abs_nonneg (x / t)]
    have hfactor : 1 ≤ (1 + |x / t|) ^ 3 := one_le_pow₀ hbase
    have hnonneg : 0 ≤ ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖ := norm_nonneg _
    nlinarith [hQ, mul_le_mul_of_nonneg_right hfactor hnonneg]
  have hderiv := deriv_littlewoodPaleyScaledKernel hb₀ n x
  have hnorm : ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ =
      t⁻¹ * (t⁻¹ * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖) := by
    rw [hderiv]
    simp [t, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < b), abs_of_pos (inv_pos.mpr ht)]
  have hpow : b ^ (-2 * n : ℤ) = t⁻¹ * t⁻¹ := by
    calc
      b ^ (-2 * n : ℤ) = b ^ (n * (-2 : ℤ)) := by congr 1 <;> ring
      _ = (b ^ n) ^ (-2 : ℤ) := zpow_mul b n (-2 : ℤ)
      _ = t⁻¹ * t⁻¹ := by
        rw [zpow_neg]
        norm_num [t]
        ring
  have htinv : 0 ≤ t⁻¹ := le_of_lt (inv_pos.mpr ht)
  calc
    ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ =
        t⁻¹ * (t⁻¹ * ‖deriv (littlewoodPaleyKernel b hb₀) (x / t)‖) := hnorm
    _ ≤ t⁻¹ * (t⁻¹ * littlewoodPaleyQ b hb₀) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq htinv) htinv
    _ = littlewoodPaleyQ b hb₀ * (t⁻¹ * t⁻¹) := by ring
    _ = littlewoodPaleyQ b hb₀ * b ^ (-2 * n : ℤ) := by rw [← hpow]

/-- The overlap count `N_b` from `lj:littlewood-paley`. -/
def littlewoodPaleyNb (b : ℝ) : ℕ := Nat.ceil (Real.logb b (2 * b)) + 2

/-- The kernel-derivative constant `B_b` from `lj:littlewood-paley`. -/
def littlewoodPaleyBb (b : ℝ) (hb : b ≠ 0) : ℝ :=
  littlewoodPaleyQ b hb * (b / (b - 1) + 1 / (1 - b ^ (-2 : ℤ)))

/-- The finite-sign lower-bound constant `c_p` in the source. -/
def littlewoodPaleyCp (p : ℝ) : ℝ :=
  Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p)

/-- The admissible square-function constant in `lj:littlewood-paley`. -/
def littlewoodPaleyUpperConstant (p b : ℝ) (hb : b ≠ 0) : ℝ :=
  (littlewoodPaleyCp p)⁻¹ *
    weakTypeFromOffSupportStrongConstant p (littlewoodPaleyNb b)
      (littlewoodPaleyBb b hb)

theorem littlewoodPaleyBb_nonneg {b : ℝ} (hb₁ : 1 < b) (hb₀ : b ≠ 0) :
    0 ≤ littlewoodPaleyBb b hb₀ := by
  unfold littlewoodPaleyBb
  have hden : 0 < b - 1 := by linarith
  have hpow : 0 < b ^ (-2 : ℤ) := zpow_pos (by linarith) _
  have hpowlt : b ^ (-2 : ℤ) < 1 := by
    simpa [zpow_neg, zpow_natCast] using
      (inv_lt_one₀ (pow_pos (by linarith : 0 < b) 2)).2
        (by nlinarith [hb₁])
  have hsecond : 0 < 1 - b ^ (-2 : ℤ) := by linarith
  have hfactor : 0 ≤ b / (b - 1) + 1 / (1 - b ^ (-2 : ℤ)) := by positivity
  exact mul_nonneg (littlewoodPaleyQ_nonneg b hb₀) hfactor

theorem littlewoodPaleyCutoffDifference_norm_le (b ξ : ℝ) :
    ‖littlewoodPaleyCutoffDifference b ξ‖ ≤ 1 := by
  unfold littlewoodPaleyCutoffDifference
  rw [← Complex.ofReal_sub]
  rw [Complex.norm_real]
  apply (abs_le).2
  constructor
  · have h₁ := chi_nonneg ξ
    have h₂ := chi_le_one (b * ξ)
    linarith
  · have h₁ := chi_le_one ξ
    have h₂ := chi_nonneg (b * ξ)
    linarith

private theorem chi_eq_zero_of_not_tsupport {x : ℝ} (hx : x ∉ tsupport χ) :
    χ x = 0 := by
  have hnot : x ∉ Function.support χ := fun hs => hx (subset_closure hs)
  change ¬χ x ≠ 0 at hnot
  exact not_ne_iff.mp hnot

/-- The annular support of `p_b` is contained in the source annulus. -/
theorem littlewoodPaleyCutoffDifference_eq_zero_of_not_annulus {b ξ : ℝ}
    (hb : 1 < b) (hsmall : |ξ| < 1 / b ∨ 2 < |ξ|) :
    littlewoodPaleyCutoffDifference b ξ = 0 := by
  rcases hsmall with hsmall | hlarge
  · have hbpos : 0 < b := by linarith
    have hbInvLt : 1 / b < 1 := (div_lt_one hbpos).2 hb
    have hξ : |ξ| ≤ 1 := by linarith
    have hbξ : |b * ξ| ≤ 1 := by
      have hprod : |ξ| * b < 1 := (lt_div_iff₀ hbpos).mp hsmall
      rw [abs_mul, abs_of_pos hbpos, mul_comm]
      exact hprod.le
    simp [littlewoodPaleyCutoffDifference,
      chi_eq_one_of_abs_le ξ hξ, chi_eq_one_of_abs_le (b * ξ) hbξ]
  · have hbpos : 0 < b := by linarith
    have hξnot : ξ ∉ tsupport χ := by
      intro hmem
      have hξrange := tsupport_chi_subset hmem
      have hξabs : |ξ| < 2 := abs_lt.mpr ⟨hξrange.1, hξrange.2⟩
      linarith
    have hbξnot : b * ξ ∉ tsupport χ := by
      intro hmem
      have hbξrange := tsupport_chi_subset hmem
      have hbξabs : |b * ξ| < 2 := abs_lt.mpr ⟨hbξrange.1, hbξrange.2⟩
      have hmono : |ξ| ≤ |b * ξ| := by
        rw [abs_mul, abs_of_pos hbpos]
        nlinarith [abs_nonneg ξ, hb]
      linarith
    simp [littlewoodPaleyCutoffDifference,
      chi_eq_zero_of_not_tsupport hξnot,
      chi_eq_zero_of_not_tsupport hbξnot]

/-- A finite signed sum of the source dilates of `q_b`. -/
def littlewoodPaleySignedKernel (b : ℝ) (hb : b ≠ 0)
    (F : Finset ℤ) (ε : ℤ → ℝ) (x : ℝ) : ℂ :=
  ∑ n ∈ F, (ε n : ℂ) * littlewoodPaleyScaledKernel b hb n x

theorem littlewoodPaleySignedKernel_smooth (b : ℝ) (hb : b ≠ 0)
    (F : Finset ℤ) (ε : ℤ → ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (littlewoodPaleySignedKernel b hb F ε) := by
  unfold littlewoodPaleySignedKernel
  apply ContDiff.sum
  intro n hn
  exact contDiff_const.mul (littlewoodPaleyScaledKernel_smooth hb n)

theorem littlewoodPaleySignedKernel_integrable (b : ℝ) (hb : b ≠ 0)
    (F : Finset ℤ) (ε : ℤ → ℝ) :
    Integrable (littlewoodPaleySignedKernel b hb F ε) volume := by
  unfold littlewoodPaleySignedKernel
  apply integrable_finset_sum
  intro n hn
  exact Integrable.const_mul (littlewoodPaleyScaledKernel_integrable hb n) (ε n : ℂ)

theorem littlewoodPaleySignedKernel_fourierIntegral {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (F : Finset ℤ) (ε : ℤ → ℝ)
    (ξ : ℝ) :
    ∫ x : ℝ, littlewoodPaleySignedKernel b hb₀ F ε x *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume =
      ∑ n ∈ F, (ε n : ℂ) * littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
  have hphase : StronglyMeasurable
      (fun x : ℝ => (Real.fourierChar (-(x * ξ)) : ℂ)) := by
    fun_prop
  have hphaseBound : ∀ x : ℝ,
      ‖(Real.fourierChar (-(x * ξ)) : ℂ)‖ ≤ 1 := by
    intro x
    simp
  have hterm : ∀ n ∈ F, Integrable
      (fun x : ℝ => (ε n : ℂ) *
        (littlewoodPaleyScaledKernel b hb₀ n x *
          (Real.fourierChar (-(x * ξ)) : ℂ))) volume := by
    intro n hn
    have hmul := (littlewoodPaleyScaledKernel_integrable hb₀ n).mul_bdd
      hphase.aestronglyMeasurable (ae_of_all volume hphaseBound)
    exact Integrable.const_mul hmul (ε n : ℂ)
  calc
    ∫ x : ℝ, littlewoodPaleySignedKernel b hb₀ F ε x *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume =
        ∫ x : ℝ, ∑ n ∈ F, (ε n : ℂ) *
          (littlewoodPaleyScaledKernel b hb₀ n x *
            (Real.fourierChar (-(x * ξ)) : ℂ)) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [littlewoodPaleySignedKernel, Finset.sum_mul]
          simp_rw [mul_assoc]
    _ = ∑ n ∈ F, ∫ x : ℝ, (ε n : ℂ) *
          (littlewoodPaleyScaledKernel b hb₀ n x *
            (Real.fourierChar (-(x * ξ)) : ℂ)) ∂volume :=
          integral_finsetSum F hterm
    _ = ∑ n ∈ F, (ε n : ℂ) *
          littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [integral_const_mul]
          exact congrArg (fun z : ℂ => (ε n : ℂ) * z)
            (littlewoodPaleyScaledKernel_fourierIntegral hb₁ hb₀ n ξ)

private theorem littlewoodPaleyLowGeometricSum {b X : ℝ}
    (hb : 1 < b) (hX : 0 ≤ X) (F : Finset ℤ)
    (hactive : ∀ n ∈ F, b ^ n ≤ X) :
    ∑ n ∈ F, b ^ n ≤ b / (b - 1) * X := by
  by_cases hF : F.Nonempty
  · let m : ℤ := F.max' hF
    let k (n : ℤ) : ℕ := (m - n).toNat
    let G : Finset ℕ := F.image k
    have hmF : m ∈ F := by simpa [m] using Finset.max'_mem F hF
    have hle (n : ℤ) (hn : n ∈ F) : n ≤ m := by
      simpa [m] using Finset.le_max' F n hn
    have hkcast (n : ℤ) (hn : n ∈ F) : (k n : ℤ) = m - n := by
      exact Int.toNat_of_nonneg (sub_nonneg.mpr (hle n hn))
    have hinj : Set.InjOn k F := by
      intro a ha b hb hab
      have hcast := congrArg (fun j : ℕ => (j : ℤ)) hab
      rw [hkcast a ha, hkcast b hb] at hcast
      omega
    have hterm (n : ℤ) (hn : n ∈ F) :
        b ^ n = b ^ m * (b⁻¹) ^ k n := by
      have hpowInv : (b⁻¹ : ℝ) ^ k n = b ^ (-(m - n)) := by
        rw [← zpow_natCast, hkcast n hn]
        rw [inv_zpow, zpow_neg]
      calc
        b ^ n = b ^ (m - (m - n)) := by congr 1; omega
        _ = b ^ m * b ^ (-(m - n)) := by
          rw [zpow_sub₀ (ne_of_gt (by linarith : 0 < b)), zpow_neg]
          ring
        _ = b ^ m * (b⁻¹) ^ k n := by rw [hpowInv]
    have hsumEq :
        (∑ n ∈ F, b ^ n) = b ^ m * ∑ j ∈ G, (b⁻¹ : ℝ) ^ j := by
      calc
        (∑ n ∈ F, b ^ n) = ∑ n ∈ F, b ^ m * (b⁻¹ : ℝ) ^ k n := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hterm n hn
        _ = b ^ m * ∑ n ∈ F, (b⁻¹ : ℝ) ^ k n := by rw [Finset.mul_sum]
        _ = b ^ m * ∑ j ∈ G, (b⁻¹ : ℝ) ^ j := by
          congr 1
          dsimp [G]
          exact (Finset.sum_image (f := fun j : ℕ => (b⁻¹ : ℝ) ^ j) hinj).symm
    have hrat : 0 ≤ (b⁻¹ : ℝ) := by positivity
    have hratlt : (b⁻¹ : ℝ) < 1 := (inv_lt_one₀ (by linarith : 0 < b)).2 hb
    have hsum : Summable (fun j : ℕ => (b⁻¹ : ℝ) ^ j) :=
      summable_geometric_of_lt_one hrat hratlt
    have hgeo :
        (∑ j ∈ G, (b⁻¹ : ℝ) ^ j) ≤ ∑' j : ℕ, (b⁻¹ : ℝ) ^ j :=
      Summable.sum_le_tsum G (fun j hj => pow_nonneg hrat j) hsum
    have hgeo' :
        (∑ j ∈ G, (b⁻¹ : ℝ) ^ j) ≤ (1 - b⁻¹)⁻¹ := by
      calc
        _ ≤ ∑' j : ℕ, (b⁻¹ : ℝ) ^ j := hgeo
        _ = (1 - b⁻¹)⁻¹ := tsum_geometric_of_lt_one hrat hratlt
    have hmnonneg : 0 ≤ b ^ m := le_of_lt (zpow_pos (by linarith) m)
    have hfactor : 0 ≤ b / (b - 1) := by positivity
    have hmX : b ^ m ≤ X := hactive m hmF
    calc
      (∑ n ∈ F, b ^ n) = b ^ m * ∑ j ∈ G, (b⁻¹ : ℝ) ^ j := hsumEq
      _ ≤ b ^ m * (1 - b⁻¹)⁻¹ := mul_le_mul_of_nonneg_left hgeo' hmnonneg
      _ = b / (b - 1) * b ^ m := by
        field_simp [ne_of_gt (by linarith : 0 < b), ne_of_gt (by linarith : 0 < b - 1)]
      _ ≤ b / (b - 1) * X := mul_le_mul_of_nonneg_left hmX hfactor
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.sum_empty]
    positivity

private theorem littlewoodPaleyHighGeometricSum {b X : ℝ}
    (hb : 1 < b) (hX : 0 < X) (F : Finset ℤ)
    (hactive : ∀ n ∈ F, X < b ^ n) :
    ∑ n ∈ F, b ^ (-2 * n : ℤ) ≤
      (1 - b ^ (-2 : ℤ))⁻¹ * X ^ (-2 : ℤ) := by
  let G : Finset ℤ := F.image (fun n => -n)
  have hinj : Set.InjOn (fun n : ℤ => -n) F := by
    intro a ha c hc hac
    exact neg_inj.mp hac
  have hsum : (∑ n ∈ F, b ^ (-2 * n : ℤ)) =
      ∑ j ∈ G, (b ^ 2 : ℝ) ^ j := by
    calc
      (∑ n ∈ F, b ^ (-2 * n : ℤ)) =
          ∑ n ∈ F, (b ^ 2 : ℝ) ^ (-n) := by
            apply Finset.sum_congr rfl
            intro n hn
            calc
              b ^ ((-2 : ℤ) * n) = b ^ ((2 : ℤ) * (-n)) := by
                congr 1 <;> ring
              _ = (b ^ (2 : ℤ)) ^ (-n) := zpow_mul b (2 : ℤ) (-n)
              _ = (b ^ 2 : ℝ) ^ (-n) := rfl
      _ = ∑ j ∈ G, (b ^ 2 : ℝ) ^ j := by
        dsimp [G]
        exact (Finset.sum_image (f := fun j : ℤ => (b ^ 2 : ℝ) ^ j) hinj).symm
  have hactive' : ∀ j ∈ G, (b ^ 2 : ℝ) ^ j ≤ X ^ (-2 : ℤ) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨n, hn, rfl⟩
    have hbn : 0 < b ^ n := zpow_pos (by linarith : 0 < b) n
    have hsquare : X ^ 2 ≤ (b ^ n) ^ 2 := by
      nlinarith [hactive n hn, sq_nonneg (b ^ n - X)]
    have hinv : 1 / (b ^ n) ^ 2 ≤ 1 / X ^ 2 :=
      one_div_le_one_div_of_le (by positivity : 0 < X ^ 2) hsquare
    have hident : (b ^ 2 : ℝ) ^ (-n) = 1 / (b ^ n) ^ 2 := by
      calc
        (b ^ 2 : ℝ) ^ (-n) = (b ^ (2 : ℤ)) ^ (-n) := by
          rfl
        _ = b ^ ((2 : ℤ) * (-n)) := (zpow_mul b (2 : ℤ) (-n)).symm
        _ = b ^ (n * (-2 : ℤ)) := by congr 1 <;> ring
        _ = (b ^ n) ^ (-2 : ℤ) := zpow_mul b n (-2 : ℤ)
        _ = 1 / (b ^ n) ^ 2 := by
          rw [zpow_neg]
          simp [one_div]
    have hXident : X ^ (-2 : ℤ) = 1 / X ^ 2 := by
      rw [zpow_neg]
      simp [one_div]
    rw [hident, hXident]
    exact hinv
  have hlow := littlewoodPaleyLowGeometricSum (b := b ^ 2) (X := X ^ (-2 : ℤ))
    (by nlinarith [hb] : 1 < b ^ 2) (le_of_lt (zpow_pos (by linarith : 0 < X) (-2 : ℤ)))
    G hactive'
  have hcoef : (b ^ 2) / (b ^ 2 - 1) = (1 - b ^ (-2 : ℤ))⁻¹ := by
    rw [zpow_neg]
    field_simp [ne_of_gt (by linarith : 0 < b), ne_of_gt (by nlinarith [hb] : 0 < b ^ 2 - 1)]
  calc
    (∑ n ∈ F, b ^ (-2 * n : ℤ)) = ∑ j ∈ G, (b ^ 2 : ℝ) ^ j := hsum
    _ ≤ (b ^ 2) / (b ^ 2 - 1) * X ^ (-2 : ℤ) := hlow
    _ = (1 - b ^ (-2 : ℤ))⁻¹ * X ^ (-2 : ℤ) := by rw [hcoef]

theorem littlewoodPaleySignedKernel_derivative_bound {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (F : Finset ℤ) (ε : ℤ → ℝ)
    (hε : ∀ n ∈ F, |ε n| ≤ 1) {x : ℝ} (hx : x ≠ 0) :
    ‖deriv (littlewoodPaleySignedKernel b hb₀ F ε) x‖ ≤
      littlewoodPaleyBb b hb₀ / |x| ^ 2 := by
  let X : ℝ := |x|
  let Flo : Finset ℤ := F.filter (fun n => b ^ n ≤ X)
  let Fhi : Finset ℤ := F.filter (fun n => ¬ b ^ n ≤ X)
  let d : ℤ → ℝ := fun n =>
    ‖(ε n : ℂ) * deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖
  have hX : 0 < X := by dsimp [X]; exact abs_pos.mpr hx
  have hsumdiff : ∀ n ∈ F,
      DifferentiableAt ℝ
        (fun y : ℝ => (ε n : ℂ) * littlewoodPaleyScaledKernel b hb₀ n y) x := by
    intro n hn
    exact DifferentiableAt.const_mul
      (((littlewoodPaleyScaledKernel_smooth hb₀ n).differentiable (by norm_num)).differentiableAt)
      _
  have hderiv : deriv (littlewoodPaleySignedKernel b hb₀ F ε) x =
      ∑ n ∈ F, (ε n : ℂ) * deriv (littlewoodPaleyScaledKernel b hb₀ n) x := by
    unfold littlewoodPaleySignedKernel
    rw [deriv_fun_sum hsumdiff]
    apply Finset.sum_congr rfl
    intro n hn
    rw [deriv_const_mul_field]
  have hlowTerm : ∀ n ∈ Flo, d n ≤ littlewoodPaleyQ b hb₀ * b ^ n / X ^ 3 := by
    intro n hn
    have hnF : n ∈ F := (Finset.mem_filter.mp hn).1
    have heps : ‖(ε n : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hε n hnF
    calc
      d n = ‖(ε n : ℂ)‖ *
          ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ := norm_mul _ _
      _ ≤ 1 * ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ :=
        mul_le_mul_of_nonneg_right heps (norm_nonneg _)
      _ ≤ littlewoodPaleyQ b hb₀ * b ^ n / X ^ 3 := by
        simpa [X] using littlewoodPaleyScaledKernel_derivative_bound_low
          hb₁ hb₀ n hx
  have hhighTerm : ∀ n ∈ Fhi, d n ≤ littlewoodPaleyQ b hb₀ * b ^ (-2 * n : ℤ) := by
    intro n hn
    have hnF : n ∈ F := (Finset.mem_filter.mp hn).1
    have heps : ‖(ε n : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hε n hnF
    calc
      d n = ‖(ε n : ℂ)‖ *
          ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ := norm_mul _ _
      _ ≤ 1 * ‖deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ :=
        mul_le_mul_of_nonneg_right heps (norm_nonneg _)
      _ ≤ littlewoodPaleyQ b hb₀ * b ^ (-2 * n : ℤ) := by
        simpa [one_mul] using littlewoodPaleyScaledKernel_derivative_bound_high
          hb₁ hb₀ n x
  have hlowGeom : ∑ n ∈ Flo, b ^ n ≤ b / (b - 1) * X := by
    apply littlewoodPaleyLowGeometricSum hb₁ (le_of_lt hX) Flo
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hhighGeom : ∑ n ∈ Fhi, b ^ (-2 * n : ℤ) ≤
      (1 - b ^ (-2 : ℤ))⁻¹ * X ^ (-2 : ℤ) := by
    apply littlewoodPaleyHighGeometricSum hb₁ hX Fhi
    intro n hn
    have hnot := (Finset.mem_filter.mp hn).2
    exact lt_of_not_ge hnot
  have hQnonneg := littlewoodPaleyQ_nonneg b hb₀
  have hlowSum : ∑ n ∈ Flo, d n ≤
      (littlewoodPaleyQ b hb₀ * (b / (b - 1))) / X ^ 2 := by
    calc
      ∑ n ∈ Flo, d n ≤ ∑ n ∈ Flo,
          littlewoodPaleyQ b hb₀ * b ^ n / X ^ 3 :=
            Finset.sum_le_sum hlowTerm
      _ = (littlewoodPaleyQ b hb₀ / X ^ 3) * ∑ n ∈ Flo, b ^ n := by
        calc
          ∑ n ∈ Flo, littlewoodPaleyQ b hb₀ * b ^ n / X ^ 3 =
              ∑ n ∈ Flo, (littlewoodPaleyQ b hb₀ / X ^ 3) * b ^ n := by
                apply Finset.sum_congr rfl
                intro n hn
                ring
          _ = (littlewoodPaleyQ b hb₀ / X ^ 3) * ∑ n ∈ Flo, b ^ n :=
            (Finset.mul_sum _ _ _).symm
      _ ≤ (littlewoodPaleyQ b hb₀ / X ^ 3) * (b / (b - 1) * X) := by
        apply mul_le_mul_of_nonneg_left hlowGeom
        exact div_nonneg hQnonneg (by positivity)
      _ = (littlewoodPaleyQ b hb₀ * (b / (b - 1))) / X ^ 2 := by
        field_simp [ne_of_gt hX, ne_of_gt (by linarith : 0 < b - 1)]
  have hhighSum : ∑ n ∈ Fhi, d n ≤
      (littlewoodPaleyQ b hb₀ * (1 - b ^ (-2 : ℤ))⁻¹) / X ^ 2 := by
    calc
      ∑ n ∈ Fhi, d n ≤ ∑ n ∈ Fhi,
          littlewoodPaleyQ b hb₀ * b ^ (-2 * n : ℤ) :=
            Finset.sum_le_sum hhighTerm
      _ = littlewoodPaleyQ b hb₀ * ∑ n ∈ Fhi, b ^ (-2 * n : ℤ) := by
        rw [Finset.mul_sum]
      _ ≤ littlewoodPaleyQ b hb₀ *
          ((1 - b ^ (-2 : ℤ))⁻¹ * X ^ (-2 : ℤ)) :=
        mul_le_mul_of_nonneg_left hhighGeom (littlewoodPaleyQ_nonneg b hb₀)
      _ = (littlewoodPaleyQ b hb₀ * (1 - b ^ (-2 : ℤ))⁻¹) / X ^ 2 := by
        rw [zpow_neg]
        field_simp [ne_of_gt hX]
  have hsplit : ∑ n ∈ F, d n =
      (∑ n ∈ Flo, d n) + ∑ n ∈ Fhi, d n := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := F) (p := fun n => b ^ n ≤ X) (f := d)]
  have hsumNorm : ‖deriv (littlewoodPaleySignedKernel b hb₀ F ε) x‖ ≤
      ∑ n ∈ F, d n := by
    rw [hderiv]
    calc
      ‖∑ n ∈ F, (ε n : ℂ) *
          deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ ≤
          ∑ n ∈ F, ‖(ε n : ℂ) *
            deriv (littlewoodPaleyScaledKernel b hb₀ n) x‖ := norm_sum_le _ _
      _ = ∑ n ∈ F, d n := by rfl
  have hsplitbound : ∑ n ∈ F, d n ≤
      (littlewoodPaleyQ b hb₀ * (b / (b - 1)) +
        littlewoodPaleyQ b hb₀ * (1 - b ^ (-2 : ℤ))⁻¹) / X ^ 2 := by
    rw [hsplit]
    calc
      (∑ n ∈ Flo, d n) + ∑ n ∈ Fhi, d n ≤
          littlewoodPaleyQ b hb₀ * (b / (b - 1)) / X ^ 2 +
            (littlewoodPaleyQ b hb₀ * (1 - b ^ (-2 : ℤ))⁻¹) / X ^ 2 :=
        add_le_add hlowSum hhighSum
      _ = (littlewoodPaleyQ b hb₀ * (b / (b - 1)) +
            littlewoodPaleyQ b hb₀ * (1 - b ^ (-2 : ℤ))⁻¹) / X ^ 2 := by ring
  calc
    ‖deriv (littlewoodPaleySignedKernel b hb₀ F ε) x‖ ≤ ∑ n ∈ F, d n := hsumNorm
    _ ≤ (littlewoodPaleyQ b hb₀ * (b / (b - 1)) +
          littlewoodPaleyQ b hb₀ * (1 - b ^ (-2 : ℤ))⁻¹) / X ^ 2 := hsplitbound
    _ = littlewoodPaleyBb b hb₀ / |x| ^ 2 := by
      rw [littlewoodPaleyBb]
      dsimp [X]
      ring

theorem littlewoodPaleyActiveCard_le {b : ℝ} (hb : 1 < b)
    (F : Finset ℤ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    (F.filter (fun n =>
      littlewoodPaleyCutoffDifference b (b ^ n * ξ) ≠ 0)).card ≤
        littlewoodPaleyNb b := by
  let S : Finset ℤ := F.filter (fun n =>
    littlewoodPaleyCutoffDifference b (b ^ n * ξ) ≠ 0)
  have hbpos : 0 < b := by linarith
  have hb₀ : b ≠ 0 := ne_of_gt hbpos
  have hξabs : 0 < |ξ| := abs_pos.mpr hξ
  by_cases hS : S.Nonempty
  · let m : ℤ := S.min' hS
    let M : ℤ := S.max' hS
    have hmin : m ∈ S := by simpa [m] using Finset.min'_mem S hS
    have hmax : M ∈ S := by simpa [M] using Finset.max'_mem S hS
    have hle : m ≤ M := Finset.min'_le S M hmax
    have hannulus (n : ℤ) (hn : n ∈ S) :
        1 / b ≤ |b ^ n * ξ| ∧ |b ^ n * ξ| ≤ 2 := by
      have hp := (Finset.mem_filter.mp hn).2
      constructor
      · by_contra h
        have hsmall : |b ^ n * ξ| < 1 / b := lt_of_not_ge h
        exact hp (littlewoodPaleyCutoffDifference_eq_zero_of_not_annulus hb
          (Or.inl hsmall))
      · by_contra h
        have hlarge : 2 < |b ^ n * ξ| := lt_of_not_ge h
        exact hp (littlewoodPaleyCutoffDifference_eq_zero_of_not_annulus hb
          (Or.inr hlarge))
    have hscale (n : ℤ) : |b ^ n * ξ| = b ^ n * |ξ| := by
      rw [abs_mul, abs_of_pos (zpow_pos hbpos n)]
    have hlow : 1 / b ≤ b ^ m * |ξ| := by
      simpa [hscale m] using (hannulus m hmin).1
    have hhigh : b ^ M * |ξ| ≤ 2 := by
      simpa [hscale M] using (hannulus M hmax).2
    have hratio : b ^ (M - m) =
        (b ^ M * |ξ|) / (b ^ m * |ξ|) := by
      rw [zpow_sub₀ hb₀]
      field_simp [ne_of_gt (mul_pos (zpow_pos hbpos m) hξabs)]
    have hratioBound : b ^ (M - m) ≤ 2 * b := by
      have hdenpos : 0 < b ^ m * |ξ| := mul_pos (zpow_pos hbpos m) hξabs
      have hquot : (b ^ M * |ξ|) / (b ^ m * |ξ|) ≤
          2 / (b ^ m * |ξ|) :=
        div_le_div_of_nonneg_right hhigh hdenpos.le
      have hinv' : 1 / (b ^ m * |ξ|) ≤ 1 / (1 / b) :=
        one_div_le_one_div_of_le (by positivity : 0 < 1 / b) hlow
      have hinv : (b ^ m * |ξ|)⁻¹ ≤ (1 / b)⁻¹ := by
        simpa only [one_div] using hinv'
      calc
        b ^ (M - m) = (b ^ M * |ξ|) / (b ^ m * |ξ|) := hratio
        _ ≤ 2 / (b ^ m * |ξ|) := hquot
        _ = 2 * (b ^ m * |ξ|)⁻¹ := by ring
        _ ≤ 2 * (1 / b)⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 2 * b := by field_simp [ne_of_gt hbpos]
    have hlog : (M - m : ℝ) ≤ Real.logb b (2 * b) := by
      have hlogmono := (Real.logb_le_logb (b := b) hb (zpow_pos hbpos (M - m))
        (by positivity : 0 < 2 * b)).2 hratioBound
      have hlogpow : Real.logb b (b ^ (M - m)) = (M - m : ℝ) := by
        rw [← Real.rpow_intCast b (M - m), Real.logb_rpow hbpos (ne_of_gt hb)]
        simp [Int.cast_sub]
      rw [hlogpow] at hlogmono
      exact hlogmono
    have hwidth : M - m ≤ (Nat.ceil (Real.logb b (2 * b)) : ℤ) := by
      exact_mod_cast hlog.trans (Nat.le_ceil (Real.logb b (2 * b)))
    have hsubset : S ⊆ Finset.Icc m M := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S n hn, Finset.le_max' S n hn⟩
    have hcard : (S.card : ℤ) ≤ M - m + 1 := by
      calc
        (S.card : ℤ) ≤ (Finset.Icc m M).card := by
          exact_mod_cast (Finset.card_le_card hsubset)
        _ = M + 1 - m := by
          simpa using (Int.card_Icc_of_le (a := m) M (by omega))
        _ = M - m + 1 := by ring
    have hcard' : S.card ≤ Nat.ceil (Real.logb b (2 * b)) + 1 := by
      exact_mod_cast (hcard.trans (by omega : M - m + 1 ≤
        (Nat.ceil (Real.logb b (2 * b)) : ℤ) + 1))
    have hcard'' : S.card ≤ Nat.ceil (Real.logb b (2 * b)) + 2 := by omega
    simpa [littlewoodPaleyNb] using hcard''
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, hSempty, littlewoodPaleyNb]

private theorem littlewoodPaleySignedMultiplier_bound {b : ℝ}
    (hb : 1 < b) (F : Finset ℤ) (ε : ℤ → ℝ)
    (hε : ∀ n ∈ F, |ε n| ≤ 1) (ξ : ℝ) :
    ‖∑ n ∈ F, (ε n : ℂ) *
      littlewoodPaleyCutoffDifference b (b ^ n * ξ)‖ ≤ littlewoodPaleyNb b := by
  let S : Finset ℤ := F.filter (fun n =>
    littlewoodPaleyCutoffDifference b (b ^ n * ξ) ≠ 0)
  let g : ℤ → ℂ := fun n => (ε n : ℂ) *
    littlewoodPaleyCutoffDifference b (b ^ n * ξ)
  have hsum : (∑ n ∈ F, g n) = ∑ n ∈ S, g n := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := F) (p := fun n => littlewoodPaleyCutoffDifference b (b ^ n * ξ) ≠ 0)
      (f := g)]
    have hzero : ∑ n ∈ F.filter
        (fun n => ¬ littlewoodPaleyCutoffDifference b (b ^ n * ξ) ≠ 0), g n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hp := (Finset.mem_filter.mp hn).2
      have hg : littlewoodPaleyCutoffDifference b (b ^ n * ξ) = 0 := by
        exact not_ne_iff.mp hp
      simp [g, hg]
    rw [hzero]
    simp [S]
  have hterm (n : ℤ) (hn : n ∈ S) : ‖g n‖ ≤ 1 := by
    have hnF : n ∈ F := (Finset.mem_filter.mp hn).1
    have heps : ‖(ε n : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hε n hnF
    calc
      ‖g n‖ = ‖(ε n : ℂ)‖ *
          ‖littlewoodPaleyCutoffDifference b (b ^ n * ξ)‖ := by
            simp [g, norm_mul]
      _ ≤ 1 * 1 := mul_le_mul (heps) (littlewoodPaleyCutoffDifference_norm_le _ _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hcard : S.card ≤ littlewoodPaleyNb b := by
    by_cases hξ : ξ = 0
    · subst ξ
      have hSnon : ¬ S.Nonempty := by
        rintro ⟨n, hn⟩
        have hp := (Finset.mem_filter.mp hn).2
        apply hp
        simp [littlewoodPaleyCutoffDifference]
      have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSnon
      simp [hSempty]
    · have h := littlewoodPaleyActiveCard_le hb F hξ
      simpa [S] using h
  calc
    ‖∑ n ∈ F, (ε n : ℂ) *
        littlewoodPaleyCutoffDifference b (b ^ n * ξ)‖ = ‖∑ n ∈ F, g n‖ := by
          rfl
    _ = ‖∑ n ∈ S, g n‖ := by rw [hsum]
    _ ≤ ∑ n ∈ S, ‖g n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun n hn => hterm n hn)
    _ = S.card := by simp
    _ ≤ littlewoodPaleyNb b := by exact_mod_cast hcard

theorem littlewoodPaleyVariationMeasure_isFinite {K : ℝ → ℂ}
    (hK : Integrable K volume) : IsFiniteMeasure (kernelVariationMeasure K) := by
  have hfi : (∫⁻ x, ‖K x‖ₑ ∂volume) ≠ (∞ : ℝ≥0∞) := by
    simpa only [enorm_norm] using (hasFiniteIntegral_iff_enorm).mp hK.norm.2 |>.ne
  have hfi' : (∫⁻ x, (‖K x‖₊ : ℝ≥0∞) ∂volume) ≠ (∞ : ℝ≥0∞) := by
    simpa only [enorm_eq_nnnorm] using hfi
  rw [kernelVariationMeasure]
  exact isFiniteMeasure_withDensity hfi'

private theorem littlewoodPaleyComplexMeasureFourier_eq_integral
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (ξ : ℝ) :
    complexMeasureFourier (volume.withDensityᵥ K) ξ =
      ∫ y, K y * (Real.fourierChar (-(y * ξ)) : ℂ) ∂volume := by
  let phase : ℝ → ℂ := fun y => (Real.fourierChar (-(y * ξ)) : ℂ)
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hfin : IsFiniteMeasure (kernelVariationMeasure K) :=
    littlewoodPaleyVariationMeasure_isFinite hKint
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact littlewoodPaleyVariationMeasure_isFinite hKint
  letI : IsFiniteMeasure (kernelVariationMeasure K) := hfin
  have hphaseSm : StronglyMeasurable phase := by
    dsimp [phase]
    fun_prop
  have hphaseBound : ∀ y, ‖phase y‖ ≤ 1 := by
    intro y
    simp [phase]
  have hphaseMem : MemLp phase 1 (kernelVariationMeasure K) :=
    MemLp.of_bound hphaseSm.aestronglyMeasurable 1
      (ae_of_all _ hphaseBound)
  let u : Lp ℂ 1 (kernelVariationMeasure K) := hphaseMem.toLp phase
  have hbridge := kernelDensity_vectorIntegral_eq_integral K hKcont hKint u
  have htoWeight : (u : ℝ → ℂ) =ᵐ[volume.withDensity
      (fun y => (‖K y‖₊ : ℝ≥0∞))] phase := by
    simpa [u, kernelVariationMeasure] using hphaseMem.coeFn_toLp
  have hweightMeas : Measurable (fun y : ℝ => (‖K y‖₊ : ℝ≥0∞)) := by
    fun_prop
  have hvol : ∀ᵐ y ∂volume, (‖K y‖₊ : ℝ≥0∞) ≠ 0 → u y = phase y :=
    (ae_withDensity_iff hweightMeas).1 htoWeight
  change ∫ᵛ y, phase y ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = _
  calc
    ∫ᵛ y, phase y ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ᵛ y, u y ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
          apply VectorMeasure.integral_congr_ae
          simpa [u, hvar] using hphaseMem.coeFn_toLp.symm
    _ = ∫ y, K y * u y ∂volume := hbridge
    _ = ∫ y, K y * phase y ∂volume := by
          apply integral_congr_ae
          filter_upwards [hvol] with y hy
          by_cases hKzero : K y = 0
          · simp [hKzero]
          · have hnnorm : ‖K y‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr hKzero
            have hweight : (‖K y‖₊ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hnnorm
            rw [hy hweight]

theorem littlewoodPaleySignedKernelL2Bound {b : ℝ}
    (hb : 1 < b) (F : Finset ℤ) (ε : ℤ → ℝ)
    (hε : ∀ n ∈ F, |ε n| ≤ 1) :
    ‖kernelConvolutionL2Operator
      (littlewoodPaleySignedKernel b (ne_of_gt (by linarith : 0 < b)) F ε)
      (littlewoodPaleySignedKernel_integrable b
        (ne_of_gt (by linarith : 0 < b)) F ε)‖ ≤ littlewoodPaleyNb b := by
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  let K : ℝ → ℂ := littlewoodPaleySignedKernel b hb₀ F ε
  have hKint : Integrable K volume := by
    exact littlewoodPaleySignedKernel_integrable b hb₀ F ε
  have hKcont : Continuous K :=
    (littlewoodPaleySignedKernel_smooth b hb₀ F ε).continuous
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact littlewoodPaleyVariationMeasure_isFinite hKint
  let T : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator K hKint
  let M : Lp ℂ ∞ (volume : Measure ℝ) := complexMeasureFourierLpTop μ
  have hcoe : (M : ℝ → ℂ) =ᵐ[volume] complexMeasureFourier μ := by
    exact coeFn_complexMeasureFourierLpTop μ
  have hMmem : MemLp (M : ℝ → ℂ) ∞ volume := Lp.memLp M
  have hMcob : Filter.IsCoboundedUnder (· ≤ ·) (ae (volume : Measure ℝ))
      (fun ξ => ‖(M : ℝ → ℂ) ξ‖) :=
    Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
      (Filter.Frequently.of_forall fun ξ => norm_nonneg _)
  have hM : ‖M‖ ≤ littlewoodPaleyNb b := by
    change lpNorm (M : ℝ → ℂ) ∞ volume ≤ littlewoodPaleyNb b
    rw [lpNorm_exponent_top_eq_essSup hMmem]
    apply essSup_le_of_ae_le (c := (littlewoodPaleyNb b : ℝ)) ?_
      (hfbdd := hMcob)
    filter_upwards [hcoe] with ξ hξ
    rw [hξ, littlewoodPaleyComplexMeasureFourier_eq_integral K hKcont hKint ξ]
    have hFourier := littlewoodPaleySignedKernel_fourierIntegral hb hb₀ F ε ξ
    have hFourier' : ∫ y, K y * (Real.fourierChar (-(y * ξ)) : ℂ) ∂volume =
        ∑ n ∈ F, (ε n : ℂ) * littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
      simpa [K] using hFourier
    calc
      ‖∫ y, K y * (Real.fourierChar (-(y * ξ)) : ℂ) ∂volume‖ =
          ‖∑ n ∈ F, (ε n : ℂ) * littlewoodPaleyCutoffDifference b (b ^ n * ξ)‖ :=
            congrArg norm hFourier'
      _ ≤ littlewoodPaleyNb b := littlewoodPaleySignedMultiplier_bound hb F ε hε ξ
  have hfourier (G : Lp ℂ 2 (volume : Measure ℝ)) :
      realFourierTransformL2 (T G) =
        realLpMultiplier M (realFourierTransformL2 G) := by
    change realFourierTransformL2 (lpComplexMeasureConvolution 2 μ G) = _
    exact fourier_lpComplexMeasureConvolution μ G
  have hmult : ‖realLpMultiplier M‖ ≤ littlewoodPaleyNb b := by
    calc
      ‖realLpMultiplier M‖ ≤ ‖M‖ := norm_realLpMultiplier_le M
      _ ≤ littlewoodPaleyNb b := hM
  apply ContinuousLinearMap.opNorm_le_bound T (by positivity)
  intro G
  calc
    ‖T G‖ = ‖realFourierTransformL2 (T G)‖ := by
      rw [norm_realFourierTransformL2]
    _ = ‖realLpMultiplier M (realFourierTransformL2 G)‖ :=
      congrArg norm (hfourier G)
    _ ≤ ‖realLpMultiplier M‖ * ‖realFourierTransformL2 G‖ :=
      (realLpMultiplier M).le_opNorm _
    _ ≤ littlewoodPaleyNb b * ‖G‖ := by
      calc
        ‖realLpMultiplier M‖ * ‖realFourierTransformL2 G‖ ≤
            littlewoodPaleyNb b * ‖realFourierTransformL2 G‖ :=
          mul_le_mul_of_nonneg_right hmult (norm_nonneg _)
        _ = littlewoodPaleyNb b * ‖G‖ := by rw [norm_realFourierTransformL2]

noncomputable def littlewoodPaleyKernelFourierLpTop
    (K : ℝ → ℂ) (hKint : Integrable K volume) :
    Lp ℂ ∞ (volume : Measure ℝ) := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact littlewoodPaleyVariationMeasure_isFinite hKint
  exact complexMeasureFourierLpTop μ

private theorem littlewoodPaleyKernelFourierLpTop_ae
    (K : ℝ → ℂ) (hKint : Integrable K volume) :
    (littlewoodPaleyKernelFourierLpTop K hKint : ℝ → ℂ) =ᵐ[volume]
      complexMeasureFourier (volume.withDensityᵥ K) := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact littlewoodPaleyVariationMeasure_isFinite hKint
  change complexMeasureFourierLpTop μ =ᵐ[volume] complexMeasureFourier μ
  exact coeFn_complexMeasureFourierLpTop μ

theorem littlewoodPaleyScaledKernelFourierLpTop_ae {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (n : ℤ) :
    (littlewoodPaleyKernelFourierLpTop
      (littlewoodPaleyScaledKernel b hb₀ n)
      (littlewoodPaleyScaledKernel_integrable hb₀ n) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
  filter_upwards [littlewoodPaleyKernelFourierLpTop_ae
    (littlewoodPaleyScaledKernel b hb₀ n)
    (littlewoodPaleyScaledKernel_integrable hb₀ n)] with ξ hξ
  rw [hξ, littlewoodPaleyComplexMeasureFourier_eq_integral
    (littlewoodPaleyScaledKernel b hb₀ n)
    (littlewoodPaleyScaledKernel_smooth hb₀ n).continuous
    (littlewoodPaleyScaledKernel_integrable hb₀ n) ξ]
  exact littlewoodPaleyScaledKernel_fourierIntegral hb₁ hb₀ n ξ

private theorem littlewoodPaleySignedKernelFourierLpTop_ae {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (F : Finset ℤ) (ε : ℤ → ℝ) :
    (littlewoodPaleyKernelFourierLpTop
      (littlewoodPaleySignedKernel b hb₀ F ε)
      (littlewoodPaleySignedKernel_integrable b hb₀ F ε) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => ∑ n ∈ F, (ε n : ℂ) *
        littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
  filter_upwards [littlewoodPaleyKernelFourierLpTop_ae
    (littlewoodPaleySignedKernel b hb₀ F ε)
    (littlewoodPaleySignedKernel_integrable b hb₀ F ε)] with ξ hξ
  rw [hξ, littlewoodPaleyComplexMeasureFourier_eq_integral
    (littlewoodPaleySignedKernel b hb₀ F ε)
    (littlewoodPaleySignedKernel_smooth b hb₀ F ε).continuous
    (littlewoodPaleySignedKernel_integrable b hb₀ F ε) ξ]
  exact littlewoodPaleySignedKernel_fourierIntegral hb₁ hb₀ F ε ξ

private noncomputable def littlewoodPaleyScaledMultiplier
    {b : ℝ} (hb₀ : b ≠ 0) (n : ℤ) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  littlewoodPaleyKernelFourierLpTop
    (littlewoodPaleyScaledKernel b hb₀ n)
    (littlewoodPaleyScaledKernel_integrable hb₀ n)

private noncomputable def littlewoodPaleySignedMultiplier
    {b : ℝ} (hb₀ : b ≠ 0) (F : Finset ℤ) (ε : ℤ → ℝ) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  littlewoodPaleyKernelFourierLpTop
    (littlewoodPaleySignedKernel b hb₀ F ε)
    (littlewoodPaleySignedKernel_integrable b hb₀ F ε)

private theorem littlewoodPaleyScaledMultiplier_ae {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (n : ℤ) :
    (littlewoodPaleyScaledMultiplier hb₀ n : ℝ → ℂ) =ᵐ[volume]
      fun ξ => littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
  exact littlewoodPaleyScaledKernelFourierLpTop_ae hb₁ hb₀ n

private theorem littlewoodPaleySignedMultiplier_ae {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (F : Finset ℤ) (ε : ℤ → ℝ) :
    (littlewoodPaleySignedMultiplier hb₀ F ε : ℝ → ℂ) =ᵐ[volume]
      fun ξ => ∑ n ∈ F, (ε n : ℂ) *
        littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
  exact littlewoodPaleySignedKernelFourierLpTop_ae hb₁ hb₀ F ε

private theorem littlewoodPaleyScaledMultiplier_ae_on_finset {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (F : Finset ℤ) :
    ∀ᵐ ξ ∂volume, ∀ n ∈ F,
      (littlewoodPaleyScaledMultiplier hb₀ n : ℝ → ℂ) ξ =
        littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      filter_upwards [] with ξ
      simp
  | @insert a s ha ih =>
      filter_upwards [littlewoodPaleyScaledMultiplier_ae hb₁ hb₀ a, ih]
        with ξ hhead htail n hn
      rcases Finset.mem_insert.mp hn with hna | hns
      · subst n
        exact hhead
      · exact htail n hns

private theorem littlewoodPaleyScaledMultiplier_smul_ae_on_finset
    {b : ℝ} (hb₀ : b ≠ 0) (F : Finset ℤ) (ε : ℤ → ℝ) :
    ∀ᵐ ξ ∂volume, ∀ n ∈ F,
      (((ε n : ℝ) • littlewoodPaleyScaledMultiplier hb₀ n :
          Lp ℂ ∞ (volume : Measure ℝ)) : ℝ → ℂ) ξ =
        (ε n : ℝ) • (littlewoodPaleyScaledMultiplier hb₀ n : ℝ → ℂ) ξ := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      filter_upwards [] with ξ
      simp
  | @insert a s ha ih =>
      filter_upwards [Lp.coeFn_smul (ε a : ℝ)
          (littlewoodPaleyScaledMultiplier hb₀ a), ih]
        with ξ hhead htail n hn
      rcases Finset.mem_insert.mp hn with hna | hns
      · subst n
        exact hhead
      · exact htail n hns

private theorem littlewoodPaley_sum_apply (F : Finset ℤ)
    (f : ℤ → ℝ → ℂ) (ξ : ℝ) :
    (∑ n ∈ F, f n) ξ = ∑ n ∈ F, f n ξ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      simp [Pi.add_apply, ih]

private theorem littlewoodPaleySignedMultiplier_eq_sum {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (F : Finset ℤ) (ε : ℤ → ℝ) :
    littlewoodPaleySignedMultiplier hb₀ F ε =
      ∑ n ∈ F, (ε n : ℝ) • littlewoodPaleyScaledMultiplier hb₀ n := by
  classical
  apply Lp.ext
  filter_upwards [littlewoodPaleySignedMultiplier_ae hb₁ hb₀ F ε,
      Lp.coeFn_finsetSum F (fun n =>
        (ε n : ℝ) • littlewoodPaleyScaledMultiplier hb₀ n),
      littlewoodPaleyScaledMultiplier_ae_on_finset hb₁ hb₀ F,
      littlewoodPaleyScaledMultiplier_smul_ae_on_finset hb₀ F ε]
    with ξ hs hsum hterms hsmul
  rw [hs]
  rw [hsum]
  rw [littlewoodPaley_sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hsmul n hn]
  rw [hterms n hn]
  simp [smul_eq_mul]

private theorem littlewoodPaleyRealLpMultiplier_sum
    (F : Finset ℤ) (M : ℤ → Lp ℂ ∞ (volume : Measure ℝ))
    (ε : ℤ → ℝ) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    realLpMultiplier (∑ n ∈ F, (ε n : ℝ) • M n) G =
      ∑ n ∈ F, (ε n : ℝ) • realLpMultiplier (M n) G := by
  classical
  change ((ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2
      (∑ n ∈ F, (ε n : ℝ) • M n)) G =
    ∑ n ∈ F, (ε n : ℝ) •
      ((ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 (M n)) G
  rw [map_sum]
  simp only [ContinuousLinearMap.map_smul_of_tower,
    ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]

theorem littlewoodPaleyKernelL2_fourier
    (K : ℝ → ℂ) (hKint : Integrable K volume)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    realFourierTransformL2 (kernelConvolutionL2Operator K hKint G) =
      realLpMultiplier (littlewoodPaleyKernelFourierLpTop K hKint)
        (realFourierTransformL2 G) := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact littlewoodPaleyVariationMeasure_isFinite hKint
  change realFourierTransformL2 (lpComplexMeasureConvolution 2 μ G) = _
  exact fourier_lpComplexMeasureConvolution μ G

private theorem littlewoodPaleySignedKernelL2_eq_sum {b : ℝ}
    (hb₁ : 1 < b) (hb₀ : b ≠ 0) (F : Finset ℤ) (ε : ℤ → ℝ) :
    kernelConvolutionL2Operator
        (littlewoodPaleySignedKernel b hb₀ F ε)
        (littlewoodPaleySignedKernel_integrable b hb₀ F ε) =
      ∑ n ∈ F, (ε n : ℝ) •
        kernelConvolutionL2Operator
          (littlewoodPaleyScaledKernel b hb₀ n)
          (littlewoodPaleyScaledKernel_integrable hb₀ n) := by
  classical
  apply ContinuousLinearMap.ext
  intro G
  apply realFourierTransformL2.injective
  have hsum_apply :
      (∑ n ∈ F, (ε n : ℝ) •
        kernelConvolutionL2Operator
          (littlewoodPaleyScaledKernel b hb₀ n)
          (littlewoodPaleyScaledKernel_integrable hb₀ n)) G =
        ∑ n ∈ F, (ε n : ℝ) •
          (kernelConvolutionL2Operator
            (littlewoodPaleyScaledKernel b hb₀ n)
            (littlewoodPaleyScaledKernel_integrable hb₀ n) G) := by
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  rw [hsum_apply]
  calc
    realFourierTransformL2
        (kernelConvolutionL2Operator
          (littlewoodPaleySignedKernel b hb₀ F ε)
          (littlewoodPaleySignedKernel_integrable b hb₀ F ε) G) = realLpMultiplier
        (littlewoodPaleySignedMultiplier hb₀ F ε)
        (realFourierTransformL2 G) := by
          exact littlewoodPaleyKernelL2_fourier
            (littlewoodPaleySignedKernel b hb₀ F ε)
            (littlewoodPaleySignedKernel_integrable b hb₀ F ε) G
    _ = realLpMultiplier
          (∑ n ∈ F, (ε n : ℝ) • littlewoodPaleyScaledMultiplier hb₀ n)
          (realFourierTransformL2 G) := by
          rw [littlewoodPaleySignedMultiplier_eq_sum hb₁ hb₀ F ε]
    _ = ∑ n ∈ F, (ε n : ℝ) •
          realLpMultiplier (littlewoodPaleyScaledMultiplier hb₀ n)
            (realFourierTransformL2 G) :=
          littlewoodPaleyRealLpMultiplier_sum F
            (fun n => littlewoodPaleyScaledMultiplier hb₀ n) ε _
    _ = ∑ n ∈ F, (ε n : ℝ) • realFourierTransformL2
          (kernelConvolutionL2Operator
            (littlewoodPaleyScaledKernel b hb₀ n)
            (littlewoodPaleyScaledKernel_integrable hb₀ n) G) := by
          apply Finset.sum_congr rfl
          intro n hn
          simpa [littlewoodPaleyScaledMultiplier] using
            congrArg (fun Z => (ε n : ℝ) • Z)
              ((littlewoodPaleyKernelL2_fourier
              (littlewoodPaleyScaledKernel b hb₀ n)
              (littlewoodPaleyScaledKernel_integrable hb₀ n) G).symm)
    _ = realFourierTransformL2
          (∑ n ∈ F, (ε n : ℝ) •
            (kernelConvolutionL2Operator
              (littlewoodPaleyScaledKernel b hb₀ n)
              (littlewoodPaleyScaledKernel_integrable hb₀ n) G)) := by
          symm
          change realFourierTransformL2RealCLM
              (∑ n ∈ F, (ε n : ℝ) •
                (kernelConvolutionL2Operator
                  (littlewoodPaleyScaledKernel b hb₀ n)
                  (littlewoodPaleyScaledKernel_integrable hb₀ n) G)) =
            ∑ n ∈ F, (ε n : ℝ) • realFourierTransformL2RealCLM
              (kernelConvolutionL2Operator
                (littlewoodPaleyScaledKernel b hb₀ n)
                (littlewoodPaleyScaledKernel_integrable hb₀ n) G)
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro n hn
          exact map_smul _ _ _

theorem littlewoodPaleySignedLpExtension_exists {b p : ℝ}
    (hb₁ : 1 < b) (hp₁ : 1 < p) (F : Finset ℤ) (ε : ℤ → ℝ)
    (hε : ∀ n ∈ F, |ε n| ≤ 1) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    ∃ U : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      (∀ f, ‖U f‖ ≤ weakTypeFromOffSupportStrongConstant p
        (littlewoodPaleyNb b) (littlewoodPaleyBb b (ne_of_gt (by linarith : 0 < b))) * ‖f‖) ∧
      (∀ (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
        (hf₂ : MemLp (f : ℝ → ℂ) 2 volume),
        (U f : ℝ → ℂ) =ᵐ[volume]
          (kernelConvolutionL2Operator
            (littlewoodPaleySignedKernel b (ne_of_gt (by linarith : 0 < b)) F ε)
            (littlewoodPaleySignedKernel_integrable b
              (ne_of_gt (by linarith : 0 < b)) F ε)
            (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  exact convolutionCZBound
    (littlewoodPaleySignedKernel b hb₀ F ε)
    (by simpa using littlewoodPaleySignedKernel_smooth b hb₀ F ε)
    (littlewoodPaleySignedKernel_integrable b hb₀ F ε)
    (A := littlewoodPaleyNb b) (B := littlewoodPaleyBb b hb₀)
    (littlewoodPaleySignedKernelL2Bound hb₁ F ε hε)
    (fun x hx => littlewoodPaleySignedKernel_derivative_bound
      hb₁ hb₀ F ε hε hx)
    p hp₁

noncomputable def littlewoodPaleySignedLpExtension {b p : ℝ}
    (hb₁ : 1 < b) (hp₁ : 1 < p) (F : Finset ℤ) (ε : ℤ → ℝ)
    (hε : ∀ n ∈ F, |ε n| ≤ 1) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  exact Classical.choose
    (littlewoodPaleySignedLpExtension_exists hb₁ hp₁ F ε hε)

private theorem littlewoodPaleySignedLpExtension_spec {b p : ℝ}
    (hb₁ : 1 < b) (hp₁ : 1 < p) (F : Finset ℤ) (ε : ℤ → ℝ)
    (hε : ∀ n ∈ F, |ε n| ≤ 1) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    (∀ f, ‖littlewoodPaleySignedLpExtension hb₁ hp₁ F ε hε f‖ ≤
      weakTypeFromOffSupportStrongConstant p (littlewoodPaleyNb b)
        (littlewoodPaleyBb b (ne_of_gt (by linarith : 0 < b))) * ‖f‖) ∧
    (∀ (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
      (hf₂ : MemLp (f : ℝ → ℂ) 2 volume),
      (littlewoodPaleySignedLpExtension hb₁ hp₁ F ε hε f : ℝ → ℂ) =ᵐ[volume]
        (kernelConvolutionL2Operator
          (littlewoodPaleySignedKernel b (ne_of_gt (by linarith : 0 < b)) F ε)
          (littlewoodPaleySignedKernel_integrable b
            (ne_of_gt (by linarith : 0 < b)) F ε)
          (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  exact Classical.choose_spec
    (littlewoodPaleySignedLpExtension_exists hb₁ hp₁ F ε hε)

theorem littlewoodPaleyFiniteSignSquareLpBound {p : ℝ} (hp : 1 < p)
    (m : ℕ) (v : Fin m → Lp ℂ (ENNReal.ofReal p) volume)
    (S : jswSignSpace m → Lp ℂ (ENNReal.ofReal p) volume)
    (hS : ∀ (w : jswSignSpace m), (S w : ℝ → ℂ) =ᵐ[volume]
      fun x => jswSignSum m w (fun i => v i x))
    {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ (w : jswSignSpace m), ‖S w‖ ≤ R) :
    lpNorm (fun x : ℝ => Real.sqrt (∑ i : Fin m, ‖v i x‖ ^ 2))
      (ENNReal.ofReal p) volume ≤ (littlewoodPaleyCp p)⁻¹ * R := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let sq : ℝ → ℝ := fun x => Real.sqrt (∑ i : Fin m, ‖v i x‖ ^ 2)
  let l1 : ℝ → ℝ := fun x => ∑ i : Fin m, ‖v i x‖
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hcp : 0 < littlewoodPaleyCp p := by
    unfold littlewoodPaleyCp
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hcp0 : 0 ≤ littlewoodPaleyCp p := hcp.le
  have hcard : 0 < Fintype.card (jswSignSpace m) :=
    Fintype.card_pos_iff.mpr ⟨instNonemptyJswSignSpace m |>.some⟩
  have hl1mem : MemLp l1 (ENNReal.ofReal p) volume := by
    dsimp [l1]
    exact memLp_finsetSum Finset.univ (fun i hi => (Lp.memLp (v i)).norm)
  have hsqAEM : AEStronglyMeasurable sq volume := by
    dsimp [sq]
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    exact (continuous_pow 2).comp_aestronglyMeasurable
      ((Lp.memLp (v i)).norm).aestronglyMeasurable
  have hsqle (x : ℝ) : |sq x| ≤ l1 x := by
    have hsumNonneg : 0 ≤ ∑ i : Fin m, ‖v i x‖ :=
      Finset.sum_nonneg fun i hi => norm_nonneg _
    have henergy : 0 ≤ ∑ i : Fin m, ‖v i x‖ ^ 2 :=
      Finset.sum_nonneg fun i hi => sq_nonneg _
    have hsqsum : (∑ i : Fin m, ‖v i x‖ ^ 2) ≤
        (∑ i : Fin m, ‖v i x‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i hi => norm_nonneg _)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_iff).2 ⟨hsumNonneg, hsqsum⟩
  have hsqmem : MemLp sq (ENNReal.ofReal p) volume :=
    hl1mem.mono' hsqAEM (ae_of_all volume hsqle)
  have hsqnonneg (x : ℝ) : 0 ≤ sq x := Real.sqrt_nonneg _
  have hsqIntegrable : Integrable (fun x : ℝ => sq x ^ p) volume := by
    simpa [sq, ENNReal.toReal_ofReal hp0.le, abs_of_nonneg (Real.sqrt_nonneg _)] using
      hsqmem.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) (by simp)
  have htermIntegrable (w : jswSignSpace m) :
      Integrable (fun x : ℝ => ‖S w x‖ ^ p) volume := by
    simpa [ENNReal.toReal_ofReal hp0.le] using
      (Lp.memLp (S w)).integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) (by simp)
  have hsumTermIntegrable : Integrable
      (fun x : ℝ => ∑ w : jswSignSpace m, ‖S w x‖ ^ p) volume := by
    apply integrable_finset_sum
    intro w hw
    exact htermIntegrable w
  have hexpectIntegrable : Integrable
      (fun x : ℝ => Finset.expect (Finset.univ : Finset (jswSignSpace m))
        (fun w => ‖S w x‖ ^ p)) volume := by
    have hrewrite :
        (fun x : ℝ => Finset.expect (Finset.univ : Finset (jswSignSpace m))
          (fun w => ‖S w x‖ ^ p)) =
        fun x => (∑ w : jswSignSpace m, ‖S w x‖ ^ p) /
          (Fintype.card (jswSignSpace m) : ℝ) := by
      funext x
      rw [Finset.expect_eq_sum_div_card]
      simp
    rw [hrewrite]
    exact hsumTermIntegrable.div_const _
  have hexpectIntegral_eq :
      (∫ x : ℝ, Finset.expect (Finset.univ : Finset (jswSignSpace m))
        (fun w => ‖S w x‖ ^ p) ∂volume) =
      Finset.expect (Finset.univ : Finset (jswSignSpace m))
        (fun w => ∫ x : ℝ, ‖S w x‖ ^ p ∂volume) := by
    calc
      _ = (∫ x : ℝ, ∑ w : jswSignSpace m, ‖S w x‖ ^ p ∂volume) /
          (Fintype.card (jswSignSpace m) : ℝ) := by
            rw [show (fun x : ℝ => Finset.expect
                (Finset.univ : Finset (jswSignSpace m))
                (fun w => ‖S w x‖ ^ p)) =
                fun x => (∑ w : jswSignSpace m, ‖S w x‖ ^ p) /
                  (Fintype.card (jswSignSpace m) : ℝ) by
                  funext x
                  rw [Finset.expect_eq_sum_div_card]
                  simp]
            rw [integral_div]
      _ = (∑ w : jswSignSpace m, ∫ x : ℝ, ‖S w x‖ ^ p ∂volume) /
          (Fintype.card (jswSignSpace m) : ℝ) := by
            rw [integral_finset_sum Finset.univ (fun w hw => htermIntegrable w)]
      _ = Finset.expect (Finset.univ : Finset (jswSignSpace m))
          (fun w => ∫ x : ℝ, ‖S w x‖ ^ p ∂volume) := by
            rw [Finset.expect_eq_sum_div_card]
            simp
  have htermNormBound (w : jswSignSpace m) :
      (∫ x : ℝ, ‖S w x‖ ^ p ∂volume) ≤ R ^ p := by
    rw [integral_norm_rpow_eq_lpNorm_rpow hp0 (Lp.memLp (S w))]
    exact Real.rpow_le_rpow (lpNorm_nonneg) (hbound w) hp0.le
  have hexpectIntegralBound :
      Finset.expect (Finset.univ : Finset (jswSignSpace m))
        (fun w => ∫ x : ℝ, ‖S w x‖ ^ p ∂volume) ≤ R ^ p := by
    rw [Finset.expect_eq_sum_div_card]
    have hsumBound :
        (∑ w : jswSignSpace m, ∫ x : ℝ, ‖S w x‖ ^ p ∂volume) ≤
          (Fintype.card (jswSignSpace m) : ℝ) * R ^ p := by
      calc
        _ ≤ ∑ _w : jswSignSpace m, R ^ p :=
          Finset.sum_le_sum fun w hw => htermNormBound w
        _ = _ := by simp [mul_comm]
    exact (div_le_iff₀ (by exact_mod_cast hcard :
      0 < (Fintype.card (jswSignSpace m) : ℝ))).2 (by
        simpa [mul_comm] using hsumBound)
  have hSall : ∀ᵐ x : ℝ ∂volume, ∀ w : jswSignSpace m,
      S w x = jswSignSum m w (fun i => v i x) := by
    rw [ae_all_iff]
    exact hS
  have hpoint (x : ℝ) (hx : ∀ w : jswSignSpace m,
      S w x = jswSignSum m w (fun i => v i x)) :
      (littlewoodPaleyCp p) ^ p * sq x ^ p ≤
        Finset.expect (Finset.univ : Finset (jswSignSpace m))
          (fun w => ‖S w x‖ ^ p) := by
    have hmoment := signMomentLowerBound m (fun i => v i x) hp0
    have hmoment' : littlewoodPaleyCp p * sq x ≤
        Real.rpow
          (Finset.expect (Finset.univ : Finset (jswSignSpace m))
            (fun w => Real.rpow ‖jswSignSum m w (fun i => v i x)‖ p)) (1 / p) := by
      simpa [littlewoodPaleyCp, sq, Real.sqrt_eq_rpow] using hmoment
    have hsumEq :
        Finset.expect (Finset.univ : Finset (jswSignSpace m))
          (fun w => Real.rpow ‖jswSignSum m w (fun i => v i x)‖ p) =
        Finset.expect (Finset.univ : Finset (jswSignSpace m))
          (fun w => ‖S w x‖ ^ p) := by
      apply Finset.expect_congr rfl
      intro w hw
      rw [hx w, Real.rpow_eq_pow]
    have hexpectNonneg : 0 ≤ Finset.expect
        (Finset.univ : Finset (jswSignSpace m))
        (fun w => ‖S w x‖ ^ p) := by
      rw [Finset.expect_eq_sum_div_card]
      apply div_nonneg
      · exact Finset.sum_nonneg fun w hw => Real.rpow_nonneg (norm_nonneg _) p
      · exact_mod_cast hcard.le
    have hpower := Real.rpow_le_rpow
      (mul_nonneg hcp0 (hsqnonneg x))
      (hmoment'.trans_eq (congrArg (fun y : ℝ => Real.rpow y (1 / p)) hsumEq)) hp0.le
    calc
      (littlewoodPaleyCp p) ^ p * sq x ^ p =
          Real.rpow (littlewoodPaleyCp p * sq x) p :=
            (Real.mul_rpow hcp0 (hsqnonneg x)).symm
      _ ≤ Real.rpow
          (Real.rpow
            (Finset.expect (Finset.univ : Finset (jswSignSpace m))
              (fun w => ‖S w x‖ ^ p)) (1 / p)) p := hpower
      _ = Finset.expect (Finset.univ : Finset (jswSignSpace m))
          (fun w => ‖S w x‖ ^ p) := by
            have hinv : (1 / p) * p = 1 := by field_simp [ne_of_gt hp0]
            calc
              _ = Real.rpow
                  (Finset.expect (Finset.univ : Finset (jswSignSpace m))
                    (fun w => ‖S w x‖ ^ p)) ((1 / p) * p) :=
                    (Real.rpow_mul hexpectNonneg (1 / p) p).symm
              _ = _ := by
                rw [hinv]
                exact Real.rpow_one _
  have hpointAE : ∀ᵐ x : ℝ ∂volume,
      (littlewoodPaleyCp p) ^ p * sq x ^ p ≤
        Finset.expect (Finset.univ : Finset (jswSignSpace m))
          (fun w => ‖S w x‖ ^ p) := by
    filter_upwards [hSall] with x hx
    exact hpoint x hx
  have hIntIneq := integral_mono_ae
    (hsqIntegrable.const_mul ((littlewoodPaleyCp p) ^ p)) hexpectIntegrable hpointAE
  have hIntUpper :
      (littlewoodPaleyCp p) ^ p * (∫ x : ℝ, sq x ^ p ∂volume) ≤ R ^ p := by
    calc
      _ = ∫ x : ℝ, (littlewoodPaleyCp p) ^ p * sq x ^ p ∂volume := by
        rw [integral_const_mul]
      _ ≤ ∫ x : ℝ,
          Finset.expect (Finset.univ : Finset (jswSignSpace m))
            (fun w => ‖S w x‖ ^ p) ∂volume := hIntIneq
      _ = Finset.expect (Finset.univ : Finset (jswSignSpace m))
          (fun w => ∫ x : ℝ, ‖S w x‖ ^ p ∂volume) := hexpectIntegral_eq
      _ ≤ R ^ p := hexpectIntegralBound
  have hcpPow : 0 < (littlewoodPaleyCp p) ^ p :=
    Real.rpow_pos_of_pos hcp _
  have hIntegralBound :
      (∫ x : ℝ, sq x ^ p ∂volume) ≤
        ((littlewoodPaleyCp p)⁻¹ * R) ^ p := by
    have hpow : ((littlewoodPaleyCp p)⁻¹ * R) ^ p =
        ((littlewoodPaleyCp p) ^ p)⁻¹ * R ^ p := by
      rw [Real.mul_rpow (inv_nonneg.mpr hcp0) hR]
      rw [Real.inv_rpow hcp0]
    calc
      (∫ x : ℝ, sq x ^ p ∂volume) ≤ (R ^ p) / ((littlewoodPaleyCp p) ^ p) := by
        apply (le_div_iff₀ hcpPow).2
        simpa [mul_comm] using hIntUpper
      _ = ((littlewoodPaleyCp p)⁻¹ * R) ^ p := by
        rw [hpow, div_eq_mul_inv]
        ring
  have hsquareLp : lpNorm sq (ENNReal.ofReal p) volume =
      (∫ x : ℝ, sq x ^ p ∂volume) ^ (1 / p) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) (by simp) hsqAEM]
    simp [sq, ENNReal.toReal_ofReal hp0.le,
      abs_of_nonneg (Real.sqrt_nonneg _), one_div]
  rw [hsquareLp]
  calc
    (∫ x : ℝ, sq x ^ p ∂volume) ^ (1 / p) ≤
        (((littlewoodPaleyCp p)⁻¹ * R) ^ p) ^ (1 / p) := by
          exact Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg
            (hsqnonneg x) p) hIntegralBound (by positivity)
    _ = (littlewoodPaleyCp p)⁻¹ * R := by
      rw [← Real.rpow_mul (mul_nonneg (inv_nonneg.mpr hcp0) hR)]
      have hcancel : p * (1 / p) = 1 := by field_simp [ne_of_gt hp0]
      rw [hcancel, Real.rpow_one]

noncomputable def littlewoodPaleyProjectionLp {b p : ℝ}
    (hb₁ : 1 < b) (hp₁ : 1 < p) (n : ℤ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  exact littlewoodPaleySignedLpExtension hb₁ hp₁ {n} (fun _ => 1) (by simp)

private theorem littlewoodPaleySignedKernel_singleton {b : ℝ}
    (hb₀ : b ≠ 0) (n : ℤ) :
    littlewoodPaleySignedKernel b hb₀ {n} (fun _ => 1) =
      littlewoodPaleyScaledKernel b hb₀ n := by
  funext x
  simp [littlewoodPaleySignedKernel]

/-- On an `L²` input, a single Littlewood--Paley projection is almost
everywhere the checked convolution by its scaled Schwartz kernel. -/
theorem littlewoodPaleyProjectionLp_l2Kernel {b p : ℝ}
    (hb₁ : 1 < b) (hp₁ : 1 < p) (n : ℤ)
    (G : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hG₂ : MemLp (G : ℝ → ℂ) 2 volume) :
    (littlewoodPaleyProjectionLp hb₁ hp₁ n G : ℝ → ℂ) =ᵐ[volume]
      (kernelConvolutionL2Operator
        (littlewoodPaleyScaledKernel b (ne_of_gt (by linarith : 0 < b)) n)
        (littlewoodPaleyScaledKernel_integrable
          (ne_of_gt (by linarith : 0 < b)) n)
        (hG₂.toLp (G : ℝ → ℂ)) : ℝ → ℂ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  have hspec := (littlewoodPaleySignedLpExtension_spec hb₁ hp₁
    {n} (fun _ => 1) (by simp)).2 G hG₂
  simpa [littlewoodPaleyProjectionLp, littlewoodPaleySignedKernel_singleton,
    ne_of_gt (by linarith : 0 < b)] using hspec

#print axioms littlewoodPaleyProjectionLp_l2Kernel
#print axioms littlewoodPaleyActiveCard_le
#print axioms littlewoodPaleyScaledKernelFourierLpTop_ae
#print axioms littlewoodPaleyKernelL2_fourier

private theorem littlewoodPaleyLpSmul_ae_on_finset {q : ℝ≥0∞}
    (F : Finset ℤ) (ε : ℤ → ℝ) (U : ℤ → Lp ℂ q (volume : Measure ℝ)) :
    ∀ᵐ x : ℝ ∂volume, ∀ n ∈ F,
      ((ε n : ℝ) • U n : Lp ℂ q (volume : Measure ℝ)) x = ε n * U n x := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      filter_upwards [] with x n hn
      exact False.elim (by simpa using hn)
  | @insert a s ha ih =>
      filter_upwards [Lp.coeFn_smul (ε a : ℝ) (U a), ih]
        with x hhead htail n hn
      rcases Finset.mem_insert.mp hn with hna | hns
      · subst n
        exact hhead
      · exact htail n hns

private theorem littlewoodPaleyLpFiniteSmulSum_ae {q : ℝ≥0∞}
    (F : Finset ℤ) (ε : ℤ → ℝ) (U : ℤ → Lp ℂ q (volume : Measure ℝ)) :
    (((∑ n ∈ F, (ε n : ℝ) • U n) : Lp ℂ q (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ n ∈ F, ε n * (U n : ℝ → ℂ) x := by
  have hcoe := Lp.coeFn_finsetSum F (fun n => (ε n : ℝ) • U n)
  have hsmul := littlewoodPaleyLpSmul_ae_on_finset F ε U
  filter_upwards [hcoe, hsmul] with x hx hmul
  calc
    (((∑ n ∈ F, (ε n : ℝ) • U n) : Lp ℂ q (volume : Measure ℝ)) : ℝ → ℂ) x =
        ∑ n ∈ F, ((ε n : ℝ) • U n : Lp ℂ q (volume : Measure ℝ)) x := by
          simpa only [littlewoodPaley_sum_apply] using hx
    _ = ∑ n ∈ F, ε n * (U n : ℝ → ℂ) x := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hmul n hn

private theorem littlewoodPaleySignedLpExtension_eq_sum {b p : ℝ}
    (hb₁ : 1 < b) (hp₁ : 1 < p) (F : Finset ℤ) (ε : ℤ → ℝ)
    (hε : ∀ n ∈ F, |ε n| ≤ 1) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    littlewoodPaleySignedLpExtension hb₁ hp₁ F ε hε =
      ∑ n ∈ F, (ε n : ℝ) • littlewoodPaleyProjectionLp hb₁ hp₁ n := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  let U := littlewoodPaleySignedLpExtension hb₁ hp₁ F ε hε
  let V := ∑ n ∈ F, (ε n : ℝ) • littlewoodPaleyProjectionLp hb₁ hp₁ n
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p)
      (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (ENNReal.ofReal_ne_top)
  have hcompose : U ∘ SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p)
        (volume : Measure ℝ) =
      V ∘ SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
    funext g
    apply Lp.ext
    let f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
      SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p) (volume : Measure ℝ) g
    have hf₂ : MemLp (f : ℝ → ℂ) 2 volume := by
      have hfae : (f : ℝ → ℂ) =ᵐ[volume] g := by
        simpa [f, SchwartzMap.toLpCLM_apply] using
          (SchwartzMap.coeFn_toLp (p := ENNReal.ofReal p)
            (μ := (volume : Measure ℝ)) (f := g))
      exact (memLp_congr_ae hfae).mpr (g.memLp 2 volume)
    have hU := (littlewoodPaleySignedLpExtension_spec hb₁ hp₁ F ε hε).2 f hf₂
    have hkernelSum := congrArg (fun T => T (hf₂.toLp (f : ℝ → ℂ)))
      (littlewoodPaleySignedKernelL2_eq_sum hb₁ hb₀ F ε)
    have hkernelSumAE :
        (kernelConvolutionL2Operator
          (littlewoodPaleySignedKernel b hb₀ F ε)
          (littlewoodPaleySignedKernel_integrable b hb₀ F ε)
          (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) =ᵐ[volume]
          fun x => ∑ n ∈ F, ε n *
            (kernelConvolutionL2Operator
              (littlewoodPaleyScaledKernel b hb₀ n)
              (littlewoodPaleyScaledKernel_integrable hb₀ n)
              (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) x := by
      have hLP := Lp.ext_iff.mp hkernelSum
      have hcoe := Lp.coeFn_finsetSum F (fun n => (ε n : ℝ) •
        kernelConvolutionL2Operator
          (littlewoodPaleyScaledKernel b hb₀ n)
          (littlewoodPaleyScaledKernel_integrable hb₀ n)
          (hf₂.toLp (f : ℝ → ℂ)))
      have hsmul := littlewoodPaleyLpSmul_ae_on_finset F ε (fun n =>
        kernelConvolutionL2Operator
          (littlewoodPaleyScaledKernel b hb₀ n)
          (littlewoodPaleyScaledKernel_integrable hb₀ n)
          (hf₂.toLp (f : ℝ → ℂ)))
      filter_upwards [hLP, hcoe, hsmul] with x hLPx hcoex hsmulx
      calc
        (kernelConvolutionL2Operator
            (littlewoodPaleySignedKernel b hb₀ F ε)
            (littlewoodPaleySignedKernel_integrable b hb₀ F ε)
            (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) x =
            ((∑ n ∈ F, (ε n : ℝ) •
              kernelConvolutionL2Operator
                (littlewoodPaleyScaledKernel b hb₀ n)
                (littlewoodPaleyScaledKernel_integrable hb₀ n))
              (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) x := hLPx
        _ = ((∑ n ∈ F, (ε n : ℝ) •
              kernelConvolutionL2Operator
                (littlewoodPaleyScaledKernel b hb₀ n)
                (littlewoodPaleyScaledKernel_integrable hb₀ n)
                (hf₂.toLp (f : ℝ → ℂ)) : Lp ℂ 2 volume) : ℝ → ℂ) x := by
              simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
        _ = ∑ n ∈ F, ((ε n : ℝ) •
              kernelConvolutionL2Operator
                (littlewoodPaleyScaledKernel b hb₀ n)
                (littlewoodPaleyScaledKernel_integrable hb₀ n)
                (hf₂.toLp (f : ℝ → ℂ)) : Lp ℂ 2 volume) x := by
              simpa only [littlewoodPaley_sum_apply] using hcoex
        _ = ∑ n ∈ F, ε n *
              (kernelConvolutionL2Operator
                (littlewoodPaleyScaledKernel b hb₀ n)
                (littlewoodPaleyScaledKernel_integrable hb₀ n)
                (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) x := by
              apply Finset.sum_congr rfl
              intro n hn
              exact hsmulx n hn
    have hproj (n : ℤ) (hn : n ∈ F) :
        (littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) =ᵐ[volume]
          (kernelConvolutionL2Operator
            (littlewoodPaleyScaledKernel b hb₀ n)
            (littlewoodPaleyScaledKernel_integrable hb₀ n)
            (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) := by
      have hsingleton : |(1 : ℝ)| ≤ 1 := by norm_num
      have hspec := (littlewoodPaleySignedLpExtension_spec hb₁ hp₁ {n}
        (fun _ => 1) (by simp)).2 f hf₂
      simpa [littlewoodPaleyProjectionLp, littlewoodPaleySignedKernel_singleton,
        hb₀] using hspec
    have hprojAll : ∀ᵐ x : ℝ ∂volume, ∀ n ∈ F,
        (littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x =
          (kernelConvolutionL2Operator
            (littlewoodPaleyScaledKernel b hb₀ n)
            (littlewoodPaleyScaledKernel_integrable hb₀ n)
            (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) x := by
      rw [ae_all_iff]
      intro n
      by_cases hn : n ∈ F
      · filter_upwards [hproj n hn] with x hx
        exact fun _ => hx
      · filter_upwards [] with x hnx
        exact False.elim (hn hnx)
    have hsumL :
        (V f : ℝ → ℂ) =ᵐ[volume]
          fun x => ∑ n ∈ F,
            ((ε n : ℝ) • littlewoodPaleyProjectionLp hb₁ hp₁ n f : Lp ℂ
              (ENNReal.ofReal p) volume) x := by
      have hVapply : V f = ∑ n ∈ F,
          (ε n : ℝ) • littlewoodPaleyProjectionLp hb₁ hp₁ n f := by
        simp [V, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      rw [hVapply]
      filter_upwards [Lp.coeFn_finsetSum F (fun n =>
          (ε n : ℝ) • littlewoodPaleyProjectionLp hb₁ hp₁ n f)] with x hx
      simpa only [littlewoodPaley_sum_apply] using hx
    have hsumSmul : ∀ᵐ x : ℝ ∂volume, ∀ n ∈ F,
        ((ε n : ℝ) • littlewoodPaleyProjectionLp hb₁ hp₁ n f : Lp ℂ
          (ENNReal.ofReal p) volume) x =
          ε n * (littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x :=
      littlewoodPaleyLpSmul_ae_on_finset F ε
        (fun n => littlewoodPaleyProjectionLp hb₁ hp₁ n f)
    filter_upwards [hU, hkernelSumAE, hsumL, hprojAll, hsumSmul]
      with x hUx hKx hVx hprojx hsmulx
    calc
      (U f : ℝ → ℂ) x =
          (kernelConvolutionL2Operator
            (littlewoodPaleySignedKernel b hb₀ F ε)
            (littlewoodPaleySignedKernel_integrable b hb₀ F ε)
            (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) x := hUx
      _ = ∑ n ∈ F, ε n *
            (kernelConvolutionL2Operator
            (littlewoodPaleyScaledKernel b hb₀ n)
              (littlewoodPaleyScaledKernel_integrable hb₀ n)
              (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) x := hKx
      _ = ∑ n ∈ F, ε n *
            (littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [(hprojx n hn).symm]
      _ = (V f : ℝ → ℂ) x := by
          symm
          rw [hVx]
          apply Finset.sum_congr rfl
          intro n hn
          rw [hsmulx n hn]
  have hoperator : (U : _ →L[ℝ] _) = V := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrFun (DenseRange.equalizer hdense U.continuous V.continuous hcompose) f
  simpa [U, V] using hoperator

/-- The Boolean sign carried by one coordinate of the recursive finite sign
space. -/
private def littlewoodPaleySignCoordinate : (m : ℕ) →
    jswSignSpace m → Fin m → Bool
  | 0, _, i => Fin.elim0 i
  | m + 1, (b, w), i => Fin.cases b (littlewoodPaleySignCoordinate m w) i

/-- The recursive signed sum is the ordinary coordinate sum for the signs
read from the recursive sample point. -/
private theorem jswSignSum_eq_sum_signCoordinate (m : ℕ)
    (w : jswSignSpace m) (z : Fin m → ℂ) :
    jswSignSum m w z =
      ∑ i : Fin m, (jswSign (littlewoodPaleySignCoordinate m w i) : ℂ) * z i := by
  induction m with
  | zero => simp [jswSignSum]
  | succ m ih =>
      cases w with
      | mk b w =>
          simp [jswSignSum, littlewoodPaleySignCoordinate, Fin.sum_univ_succ, ih]

/-- Reindex a finite sum over a finite subset of `ℤ` by its canonical
increasing enumeration. -/
private theorem littlewoodPaley_sum_finset_eq_sum_fin {M : Type*}
    [AddCommMonoid M] (F : Finset ℤ) (g : ℤ → M) :
    (∑ i : Fin F.card,
      g ((F.orderIsoOfFin rfl i : {n // n ∈ F}) : ℤ)) = ∑ n ∈ F, g n := by
  classical
  let e : Fin F.card ≃ {n // n ∈ F} := F.orderIsoOfFin rfl
  calc
    (∑ i : Fin F.card,
      g ((e i : {n // n ∈ F}) : ℤ)) =
        ∑ x : {n // n ∈ F}, g (x : ℤ) := e.sum_comp (fun x => g (x : ℤ))
    _ = ∑ x ∈ F.attach, g (x : ℤ) :=
      Finset.sum_coe_sort_eq_attach F (fun x => g (x : ℤ))
    _ = ∑ n ∈ F, g n := Finset.sum_attach F g

private noncomputable def littlewoodPaleyFiniteSignCoeff (F : Finset ℤ)
    (w : jswSignSpace F.card) (n : ℤ) : ℝ :=
  if hn : n ∈ F then
    jswSign (littlewoodPaleySignCoordinate F.card w
      ((F.orderIsoOfFin rfl).symm ⟨n, hn⟩))
  else 0

private theorem littlewoodPaleyFiniteSignCoeff_bound (F : Finset ℤ)
    (w : jswSignSpace F.card) :
    ∀ n ∈ F, |littlewoodPaleyFiniteSignCoeff F w n| ≤ 1 := by
  intro n hn
  by_cases h : littlewoodPaleySignCoordinate F.card w
      ((F.orderIsoOfFin rfl).symm ⟨n, hn⟩) = true <;>
    simp [littlewoodPaleyFiniteSignCoeff, hn, jswSign, h]

private theorem littlewoodPaleyFiniteSignCoeff_orderIso (F : Finset ℤ)
    (w : jswSignSpace F.card) (i : Fin F.card) :
    littlewoodPaleyFiniteSignCoeff F w
        ((F.orderIsoOfFin rfl i : {n // n ∈ F}) : ℤ) =
      jswSign (littlewoodPaleySignCoordinate F.card w i) := by
  classical
  let e : Fin F.card ≃o {n // n ∈ F} := F.orderIsoOfFin rfl
  have hn : ((e i : {n // n ∈ F}) : ℤ) ∈ F := (e i).property
  have hsub : (⟨(e i : ℤ), hn⟩ : {n // n ∈ F}) = e i := by
    apply Subtype.ext
    rfl
  unfold littlewoodPaleyFiniteSignCoeff
  rw [dif_pos hn]
  apply congrArg (fun j => jswSign (littlewoodPaleySignCoordinate F.card w j))
  change e.symm (⟨(e i : ℤ), hn⟩ : {n // n ∈ F}) = i
  exact (congrArg e.symm hsub).trans (e.symm_apply_apply i)

private noncomputable def littlewoodPaleyProjectionVector {b p : ℝ}
    (hb₁ : 1 < b) (hp₁ : 1 < p) (F : Finset ℤ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    Fin F.card → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  exact fun i => littlewoodPaleyProjectionLp hb₁ hp₁
    ((F.orderIsoOfFin rfl i : {n // n ∈ F}) : ℤ)

private noncomputable def littlewoodPaleySignExtension {b p : ℝ}
    (hb₁ : 1 < b) (hp₁ : 1 < p) (F : Finset ℤ)
    (w : jswSignSpace F.card) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  exact littlewoodPaleySignedLpExtension hb₁ hp₁ F
    (littlewoodPaleyFiniteSignCoeff F w)
    (littlewoodPaleyFiniteSignCoeff_bound F w)

private theorem littlewoodPaleySignExtension_ae_eq_signSum {b p : ℝ}
    (hb₁ : 1 < b) (hp₁ : 1 < p) (F : Finset ℤ)
    (w : jswSignSpace F.card)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    (littlewoodPaleySignExtension hb₁ hp₁ F w f : ℝ → ℂ) =ᵐ[volume]
      fun x => jswSignSum F.card w (fun i =>
        (littlewoodPaleyProjectionVector hb₁ hp₁ F i f : ℝ → ℂ) x) := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let ε := littlewoodPaleyFiniteSignCoeff F w
  have hlin := littlewoodPaleySignedLpExtension_eq_sum hb₁ hp₁ F ε
    (littlewoodPaleyFiniteSignCoeff_bound F w)
  have hlinf := congrArg (fun T => T f) hlin
  have hlinAE :
      (littlewoodPaleySignExtension hb₁ hp₁ F w f : ℝ → ℂ) =ᵐ[volume]
        ((∑ n ∈ F, (ε n : ℝ) • littlewoodPaleyProjectionLp hb₁ hp₁ n f :
          Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) := by
    simpa [littlewoodPaleySignExtension, ε] using (Lp.ext_iff.mp hlinf)
  have hsumAE := littlewoodPaleyLpFiniteSmulSum_ae F ε
    (fun n => littlewoodPaleyProjectionLp hb₁ hp₁ n f)
  have hpointwise (x : ℝ) :
      ∑ n ∈ F, ε n *
          (littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x =
        ∑ i : Fin F.card,
          (jswSign (littlewoodPaleySignCoordinate F.card w i) : ℂ) *
            (littlewoodPaleyProjectionVector hb₁ hp₁ F i f : ℝ → ℂ) x := by
    calc
      _ = ∑ i : Fin F.card,
          (ε ((F.orderIsoOfFin rfl i : {n // n ∈ F}) : ℤ) : ℂ) *
            (littlewoodPaleyProjectionLp hb₁ hp₁
              ((F.orderIsoOfFin rfl i : {n // n ∈ F}) : ℤ) f : ℝ → ℂ) x :=
          (littlewoodPaley_sum_finset_eq_sum_fin F (fun n =>
            (ε n : ℂ) *
              (littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x)).symm
      _ = ∑ i : Fin F.card,
          (jswSign (littlewoodPaleySignCoordinate F.card w i) : ℂ) *
            (littlewoodPaleyProjectionVector hb₁ hp₁ F i f : ℝ → ℂ) x := by
          apply Finset.sum_congr rfl
          intro i hi
          have hcoeff : ε
              ((F.orderIsoOfFin rfl i : {n // n ∈ F}) : ℤ) =
                jswSign (littlewoodPaleySignCoordinate F.card w i) := by
            change littlewoodPaleyFiniteSignCoeff F w
                ((F.orderIsoOfFin rfl i : {n // n ∈ F}) : ℤ) = _
            exact littlewoodPaleyFiniteSignCoeff_orderIso F w i
          rw [hcoeff]
          rfl
  filter_upwards [hlinAE, hsumAE] with x hlinx hsumx
  calc
    (littlewoodPaleySignExtension hb₁ hp₁ F w f : ℝ → ℂ) x =
        (((∑ n ∈ F, (ε n : ℝ) •
          littlewoodPaleyProjectionLp hb₁ hp₁ n f) : Lp ℂ
            (ENNReal.ofReal p) volume) : ℝ → ℂ) x := hlinx
    _ = ∑ n ∈ F, ε n *
          (littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x := hsumx
    _ = jswSignSum F.card w (fun i =>
          (littlewoodPaleyProjectionVector hb₁ hp₁ F i f : ℝ → ℂ) x) := by
          rw [hpointwise]
          exact (jswSignSum_eq_sum_signCoordinate F.card w
            (fun i => (littlewoodPaleyProjectionVector hb₁ hp₁ F i f : ℝ → ℂ) x)).symm

/-- The finite-family Littlewood--Paley square estimate with the exact
constant `c_p⁻¹ C_p(N_b,B_b)` from the blueprint. -/
theorem littlewoodPaleyUpper_square {b p : ℝ} (hb₁ : 1 < b) (hp₁ : 1 < p)
    (F : Finset ℤ) (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    lpNorm (fun x : ℝ => Real.sqrt (∑ n ∈ F,
      ‖(littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x‖ ^ 2))
      (ENNReal.ofReal p) volume ≤ littlewoodPaleyUpperConstant p b
        (ne_of_gt (by linarith : 0 < b)) * ‖f‖ := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  let v : Fin F.card → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    fun i => littlewoodPaleyProjectionVector hb₁ hp₁ F i f
  let S : jswSignSpace F.card → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    fun w => littlewoodPaleySignExtension hb₁ hp₁ F w f
  let R := weakTypeFromOffSupportStrongConstant p (littlewoodPaleyNb b)
    (littlewoodPaleyBb b hb₀) * ‖f‖
  have hS : ∀ w : jswSignSpace F.card,
      (S w : ℝ → ℂ) =ᵐ[volume]
        fun x => jswSignSum F.card w (fun i => v i x) := by
    intro w
    simpa [S, v] using
      littlewoodPaleySignExtension_ae_eq_signSum hb₁ hp₁ F w f
  have hbound : ∀ w : jswSignSpace F.card, ‖S w‖ ≤ R := by
    intro w
    simpa [S, R, littlewoodPaleySignExtension] using
      (littlewoodPaleySignedLpExtension_spec hb₁ hp₁ F
        (littlewoodPaleyFiniteSignCoeff F w)
        (littlewoodPaleyFiniteSignCoeff_bound F w)).1 f
  have hR : 0 ≤ R := by
    letI : Nonempty (jswSignSpace F.card) := instNonemptyJswSignSpace F.card
    rcases ‹Nonempty (jswSignSpace F.card)› with ⟨w⟩
    exact (norm_nonneg (S w)).trans (hbound w)
  have hsq := littlewoodPaleyFiniteSignSquareLpBound hp₁ F.card v S hS hR hbound
  have hsquareFun :
      (fun x : ℝ => Real.sqrt (∑ i : Fin F.card,
        ‖(littlewoodPaleyProjectionVector hb₁ hp₁ F i f : ℝ → ℂ) x‖ ^ 2)) =
      (fun x : ℝ => Real.sqrt (∑ n ∈ F,
        ‖(littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x‖ ^ 2)) := by
    funext x
    congr 1
    exact littlewoodPaley_sum_finset_eq_sum_fin F (fun n =>
      ‖(littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x‖ ^ 2)
  simpa [v, littlewoodPaleyUpperConstant, R, hb₀, mul_assoc, hsquareFun] using hsq

private def littlewoodPaleyDilatedLowpassKernel
    (ρ : SchwartzMap ℝ ℂ) (a : ℝ) (y : ℝ) : ℂ :=
  a⁻¹ • ρ (y / a)

private theorem littlewoodPaleyDilatedLowpassKernel_continuous
    (ρ : SchwartzMap ℝ ℂ) (a : ℝ) :
    Continuous (littlewoodPaleyDilatedLowpassKernel ρ a) := by
  change Continuous (fun y : ℝ => (a⁻¹ : ℝ) • ρ (y / a))
  exact (ρ.continuous.comp (continuous_id.div_const a)).const_smul (a⁻¹ : ℝ)

private theorem littlewoodPaleyDilatedLowpassKernel_integrable
    (ρ : SchwartzMap ℝ ℂ) {a : ℝ} (ha : a ≠ 0) :
    Integrable (littlewoodPaleyDilatedLowpassKernel ρ a) volume := by
  change Integrable (fun y : ℝ => (a⁻¹ : ℝ) • ρ (y / a)) volume
  exact Integrable.smul a⁻¹ (ρ.integrable.comp_div ha)

private theorem littlewoodPaleyDilatedLowpassKernel_norm_integral
    (ρ : SchwartzMap ℝ ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ y : ℝ, ‖littlewoodPaleyDilatedLowpassKernel ρ a y‖ ∂volume =
      ∫ y : ℝ, ‖ρ y‖ ∂volume := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hchange := Measure.integral_comp_mul_left
    (fun z : ℝ => ‖ρ z‖) a⁻¹
  have hchange' : (∫ y : ℝ, ‖ρ (a⁻¹ * y)‖ ∂volume) =
      a * ∫ z : ℝ, ‖ρ z‖ ∂volume := by
    simpa [abs_of_pos ha] using hchange
  have hnorm (y : ℝ) :
      ‖littlewoodPaleyDilatedLowpassKernel ρ a y‖ =
        a⁻¹ * ‖ρ (a⁻¹ * y)‖ := by
    dsimp [littlewoodPaleyDilatedLowpassKernel]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    congr 1
    field_simp [ha0]
  calc
    ∫ y : ℝ, ‖littlewoodPaleyDilatedLowpassKernel ρ a y‖ ∂volume =
        ∫ y : ℝ, a⁻¹ * ‖ρ (a⁻¹ * y)‖ ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with y
          exact hnorm y
    _ = a⁻¹ * ∫ y : ℝ, ‖ρ (a⁻¹ * y)‖ ∂volume := by
          rw [integral_const_mul]
    _ = a⁻¹ * (a * ∫ z : ℝ, ‖ρ z‖ ∂volume) := by rw [hchange']
    _ = ∫ z : ℝ, ‖ρ z‖ ∂volume := by field_simp [ha0]

private theorem littlewoodPaleyDilatedLowpassKernel_norm_le_seminorm
    (ρ : SchwartzMap ℝ ℂ) {a : ℝ} (ha : 0 < a) (y : ℝ) :
    ‖littlewoodPaleyDilatedLowpassKernel ρ a y‖ ≤
      a⁻¹ * SchwartzMap.seminorm ℝ 0 0 ρ := by
  have hρ := ρ.le_seminorm ℝ 0 0 (y / a)
  have hρ' : ‖ρ (y / a)‖ ≤ SchwartzMap.seminorm ℝ 0 0 ρ := by
    simpa using hρ
  rw [show ‖littlewoodPaleyDilatedLowpassKernel ρ a y‖ =
      a⁻¹ * ‖ρ (y / a)‖ by
        dsimp [littlewoodPaleyDilatedLowpassKernel]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr ha)] ]
  exact mul_le_mul_of_nonneg_left hρ' (inv_nonneg.mpr ha.le)

private theorem littlewoodPaleyRawConvolution_integrable_at
    (K f : ℝ → ℂ) (hK : Integrable K volume) (hfcont : Continuous f)
    (hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    Integrable (fun y : ℝ => K y * f (x-y)) volume := by
  rcases hfbdd with ⟨C, hC⟩
  have hdom : Integrable (fun y : ℝ => C * ‖K y‖) volume :=
    hK.norm.const_mul C
  apply hdom.mono'
  · exact (hK.aestronglyMeasurable.mul
      (hfcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · filter_upwards [] with y
    calc
      ‖K y * f (x-y)‖ = ‖K y‖ * ‖f (x-y)‖ := norm_mul _ _
      _ ≤ ‖K y‖ * C := mul_le_mul_of_nonneg_left (hC (x-y)) (norm_nonneg _)
      _ = C * ‖K y‖ := by ring

/-- The raw convolution against a bounded integrable input has the expected
`L¹` bound.  The pointwise convolution integrand is compared with the
convolution of the two norms, whose integral factors by Tonelli. -/
private theorem littlewoodPaleyRawConvolution_L1_bound
    (K f : ℝ → ℂ) (hK : Integrable K volume) (hf : Integrable f volume)
    (hfcont : Continuous f) (hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x : ℝ => ‖∫ y, K y * f (x-y) ∂volume‖) volume ∧
      (∫ x : ℝ, ‖∫ y, K y * f (x-y) ∂volume‖ ∂volume) ≤
        (∫ y : ℝ, ‖K y‖ ∂volume) * (∫ y : ℝ, ‖f y‖ ∂volume) := by
  classical
  let raw : ℝ → ℂ := fun x => ∫ y, K y * f (x-y) ∂volume
  let major : ℝ → ℝ := fun x => ∫ y, ‖K y‖ * ‖f (x-y)‖ ∂volume
  have hprod : Integrable (fun z : ℝ × ℝ => K z.2 * f (z.1-z.2))
      (volume.prod volume) := by
    simpa [ContinuousLinearMap.mul_apply] using
      hK.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hf
  have hraw : Integrable raw volume := by
    simpa [raw] using hprod.integral_prod_left
  have hmajor : Integrable major volume := by
    change Integrable
      (MeasureTheory.convolution (fun y : ℝ => ‖K y‖)
        (fun y : ℝ => ‖f y‖) (ContinuousLinearMap.mul ℝ ℝ) volume) volume
    exact hK.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm
  rcases hfbdd with ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact le_trans (norm_nonneg (f 0)) this
  have hfiber (x : ℝ) : Integrable (fun y : ℝ => K y * f (x-y)) volume := by
    exact littlewoodPaleyRawConvolution_integrable_at K f hK hfcont
      ⟨C, hC⟩ x
  have hpoint (x : ℝ) : ‖raw x‖ ≤ major x := by
    calc
      ‖raw x‖ = ‖∫ y : ℝ, K y * f (x-y) ∂volume‖ := rfl
      _ ≤ ∫ y : ℝ, ‖K y * f (x-y)‖ ∂volume :=
        norm_integral_le_integral_norm (fun y : ℝ => K y * f (x-y))
      _ = major x := by
        dsimp [raw, major]
        apply integral_congr_ae
        filter_upwards [] with y
        exact norm_mul _ _
  have hfactor : (∫ x : ℝ, major x ∂volume) =
      (∫ y : ℝ, ‖K y‖ ∂volume) * (∫ y : ℝ, ‖f y‖ ∂volume) := by
    change (∫ x : ℝ,
      MeasureTheory.convolution (fun y : ℝ => ‖K y‖)
        (fun y : ℝ => ‖f y‖) (ContinuousLinearMap.mul ℝ ℝ) volume x ∂volume) = _
    exact integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ)
      hK.norm hf.norm
  refine ⟨hraw.norm, ?_⟩
  calc
    ∫ x : ℝ, ‖raw x‖ ∂volume ≤ ∫ x : ℝ, major x ∂volume :=
      integral_mono_ae hraw.norm hmajor (ae_of_all volume hpoint)
    _ = (∫ y : ℝ, ‖K y‖ ∂volume) * (∫ y : ℝ, ‖f y‖ ∂volume) := hfactor

private noncomputable def littlewoodPaleyDilationEquiv (a : ℝ) (ha : a ≠ 0) :
    ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ) (G := ℝˣ)
    (Units.mk0 (a⁻¹) (inv_ne_zero ha))

private theorem littlewoodPaleyDilationEquiv_apply
    (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    littlewoodPaleyDilationEquiv a ha x = x / a := by
  change (a⁻¹ : ℝ) * x = x / a
  field_simp [ha]

private noncomputable def littlewoodPaleyScaledKernelSchwartz
    {b : ℝ} (hb : b ≠ 0) (n : ℤ) : SchwartzMap ℝ ℂ :=
  ((b ^ n)⁻¹ : ℝ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (littlewoodPaleyDilationEquiv (b ^ n) (zpow_ne_zero n hb))
      (littlewoodPaleyKernelSchwartz b hb)

private theorem littlewoodPaleyScaledKernelSchwartz_apply
    {b : ℝ} (hb : b ≠ 0) (n : ℤ) (x : ℝ) :
    littlewoodPaleyScaledKernelSchwartz hb n x = littlewoodPaleyScaledKernel b hb n x := by
  change ((b ^ n)⁻¹ : ℝ) •
      littlewoodPaleyKernelSchwartz b hb
        (littlewoodPaleyDilationEquiv (b ^ n) (zpow_ne_zero n hb) x) =
    ((b ^ n)⁻¹ : ℝ) • littlewoodPaleyKernel b hb (x / b ^ n)
  rw [littlewoodPaleyDilationEquiv_apply]
  rfl

private def littlewoodPaleyLowpassCutoffComplex (ξ : ℝ) : ℂ := (χ ξ : ℂ)

private theorem littlewoodPaleyLowpassCutoffComplex_smooth :
    ContDiff ℝ (∞ : ℕ∞ω) littlewoodPaleyLowpassCutoffComplex := by
  exact Complex.ofRealCLM.contDiff.comp chi_contDiff

private theorem littlewoodPaleyLowpassCutoffComplex_hasCompactSupport :
    HasCompactSupport littlewoodPaleyLowpassCutoffComplex := by
  exact chi_hasCompactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)

private def littlewoodPaleyLowpassCutoffSchwartz : SchwartzMap ℝ ℂ :=
  littlewoodPaleyLowpassCutoffComplex_hasCompactSupport.toSchwartzMap
    littlewoodPaleyLowpassCutoffComplex_smooth

private def littlewoodPaleyLowpassKernelSchwartz : SchwartzMap ℝ ℂ :=
  𝓕⁻ littlewoodPaleyLowpassCutoffSchwartz

private theorem littlewoodPaleyLowpassKernelSchwartz_integral :
    ∫ x : ℝ, littlewoodPaleyLowpassKernelSchwartz x ∂volume = 1 := by
  have hinv : 𝓕 (𝓕⁻ littlewoodPaleyLowpassCutoffSchwartz) =
      littlewoodPaleyLowpassCutoffSchwartz :=
    FourierTransform.fourier_fourierInv_eq _
  have hf := congrArg (fun f : SchwartzMap ℝ ℂ => f 0) hinv
  change 𝓕 littlewoodPaleyLowpassKernelSchwartz 0 =
    littlewoodPaleyLowpassCutoffSchwartz 0 at hf
  change 𝓕 (fun x : ℝ => littlewoodPaleyLowpassKernelSchwartz x) 0 = _ at hf
  rw [Real.fourier_eq'] at hf
  have hchi0 : χ 0 = 1 := chi_eq_one_of_abs_le 0 (by norm_num)
  have hphase (x : ℝ) :
      Complex.exp ((↑(-2 * Real.pi * inner ℝ x 0) : ℂ) * Complex.I) •
        littlewoodPaleyLowpassKernelSchwartz x =
      littlewoodPaleyLowpassKernelSchwartz x := by
    simp [inner]
  simp_rw [hphase] at hf
  have hzero : littlewoodPaleyLowpassCutoffSchwartz 0 = 1 := by
    simp [littlewoodPaleyLowpassCutoffSchwartz,
      littlewoodPaleyLowpassCutoffComplex, hchi0]
  simpa [hzero] using hf

private theorem littlewoodPaleyLowpassKernel_fourierIntegral (ξ : ℝ) :
    ∫ x : ℝ, littlewoodPaleyLowpassKernelSchwartz x *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume = (χ ξ : ℂ) := by
  have hfourier :
      𝓕 littlewoodPaleyLowpassKernelSchwartz ξ = (χ ξ : ℂ) := by
    have hinv : 𝓕 littlewoodPaleyLowpassKernelSchwartz =
        littlewoodPaleyLowpassCutoffSchwartz := by
      change 𝓕 (𝓕⁻ littlewoodPaleyLowpassCutoffSchwartz) = _
      exact FourierTransform.fourier_fourierInv_eq _
    have h := congrArg (fun f : SchwartzMap ℝ ℂ => f ξ) hinv
    simpa [littlewoodPaleyLowpassCutoffSchwartz,
      littlewoodPaleyLowpassCutoffComplex] using h
  change 𝓕 (fun x : ℝ => littlewoodPaleyLowpassKernelSchwartz x) ξ = _ at hfourier
  rw [Real.fourier_eq'] at hfourier
  simpa [Real.fourierChar_apply, Real.inner_apply, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hfourier

private noncomputable def littlewoodPaleyDilatedLowpassSchwartz
    (a : ℝ) (ha : a ≠ 0) : SchwartzMap ℝ ℂ :=
  (a⁻¹ : ℝ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (littlewoodPaleyDilationEquiv a ha)
      littlewoodPaleyLowpassKernelSchwartz

private theorem littlewoodPaleyDilatedLowpassSchwartz_apply
    (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    littlewoodPaleyDilatedLowpassSchwartz a ha x =
      littlewoodPaleyDilatedLowpassKernel littlewoodPaleyLowpassKernelSchwartz a x := by
  change (a⁻¹ : ℝ) • littlewoodPaleyLowpassKernelSchwartz
      (littlewoodPaleyDilationEquiv a ha x) =
    (a⁻¹ : ℝ) • littlewoodPaleyLowpassKernelSchwartz (x / a)
  rw [littlewoodPaleyDilationEquiv_apply]

private theorem littlewoodPaleyDilatedLowpassKernel_fourierIntegral
    (a : ℝ) (ha : 0 < a) (ξ : ℝ) :
    ∫ x : ℝ, littlewoodPaleyDilatedLowpassKernel
        littlewoodPaleyLowpassKernelSchwartz a x *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume = (χ (a * ξ) : ℂ) := by
  let g : ℝ → ℂ := fun y => littlewoodPaleyLowpassKernelSchwartz y *
    (Real.fourierChar (-(y * (a * ξ))) : ℂ)
  have hcomp := Measure.integral_comp_mul_left g a⁻¹
  have hcomp' :
      ∫ x : ℝ, g (a⁻¹ * x) ∂volume = a • ∫ y : ℝ, g y ∂volume := by
    simpa [abs_of_pos ha] using hcomp
  have hphase (x : ℝ) :
      (Real.fourierChar (-(x * ξ)) : ℂ) =
        (Real.fourierChar (-((a⁻¹ * x) * (a * ξ))) : ℂ) := by
    have harg : -(x * ξ) = -((a⁻¹ * x) * (a * ξ)) := by
      field_simp [ne_of_gt ha]
    rw [harg]
  have hchange :
      ∫ x : ℝ, littlewoodPaleyLowpassKernelSchwartz (x / a) *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume =
      ∫ x : ℝ, g (a⁻¹ * x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [g]
    rw [show x / a = a⁻¹ * x by field_simp [ne_of_gt ha], hphase]
  have hpoint (x : ℝ) :
      littlewoodPaleyDilatedLowpassKernel littlewoodPaleyLowpassKernelSchwartz a x *
          (Real.fourierChar (-(x * ξ)) : ℂ) =
        a⁻¹ • (littlewoodPaleyLowpassKernelSchwartz (x / a) *
          (Real.fourierChar (-(x * ξ)) : ℂ)) := by
    simp [littlewoodPaleyDilatedLowpassKernel, smul_eq_mul]
    ring
  calc
    ∫ x : ℝ, littlewoodPaleyDilatedLowpassKernel
        littlewoodPaleyLowpassKernelSchwartz a x *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume =
      a⁻¹ • ∫ x : ℝ, littlewoodPaleyLowpassKernelSchwartz (x / a) *
        (Real.fourierChar (-(x * ξ)) : ℂ) ∂volume := by
          rw [← integral_smul]
          apply integral_congr_ae
          filter_upwards [] with x
          exact hpoint x
    _ = a⁻¹ • ∫ x : ℝ, g (a⁻¹ * x) ∂volume := by rw [hchange]
    _ = a⁻¹ • (a • ∫ y : ℝ, g y ∂volume) := by rw [hcomp']
    _ = ∫ y : ℝ, g y ∂volume := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
    _ = (χ (a * ξ) : ℂ) := by
      simpa [g] using littlewoodPaleyLowpassKernel_fourierIntegral (a * ξ)

private theorem littlewoodPaleyDilatedLowpassSchwartz_fourier
    (a : ℝ) (ha : 0 < a) (ξ : ℝ) :
    𝓕 (littlewoodPaleyDilatedLowpassSchwartz a (ne_of_gt ha)) ξ =
      (χ (a * ξ) : ℂ) := by
  change 𝓕 (fun x : ℝ => littlewoodPaleyDilatedLowpassSchwartz a
    (ne_of_gt ha) x) ξ = _
  rw [Real.fourier_eq']
  simpa [littlewoodPaleyDilatedLowpassSchwartz_apply,
    Real.fourierChar_apply, Real.inner_apply, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using
      littlewoodPaleyDilatedLowpassKernel_fourierIntegral a ha ξ

private theorem littlewoodPaleyScaledKernelSchwartz_fourier
    {b : ℝ} (hb₁ : 1 < b) (hb₀ : b ≠ 0) (n : ℤ) (ξ : ℝ) :
    𝓕 (littlewoodPaleyScaledKernelSchwartz hb₀ n) ξ =
      littlewoodPaleyCutoffDifference b (b ^ n * ξ) := by
  change 𝓕 (fun x : ℝ => littlewoodPaleyScaledKernelSchwartz hb₀ n x) ξ = _
  rw [Real.fourier_eq']
  simpa [littlewoodPaleyScaledKernelSchwartz_apply,
    littlewoodPaleyScaledKernel, Real.fourierChar_apply,
    Real.inner_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      littlewoodPaleyScaledKernel_fourierIntegral hb₁ hb₀ n ξ

private theorem littlewoodPaleyScaledKernel_eq_dilatedLowpass_difference
    {b : ℝ} (hb₁ : 1 < b) (hb₀ : b ≠ 0) (n : ℤ) (x : ℝ) :
    littlewoodPaleyScaledKernel b hb₀ n x =
      littlewoodPaleyDilatedLowpassKernel littlewoodPaleyLowpassKernelSchwartz
          (b ^ n) x -
        littlewoodPaleyDilatedLowpassKernel littlewoodPaleyLowpassKernelSchwartz
          (b ^ (n + 1)) x := by
  have hbpos : 0 < b := by linarith
  have hq : 𝓕 (littlewoodPaleyScaledKernelSchwartz hb₀ n) =
      𝓕 (littlewoodPaleyDilatedLowpassSchwartz (b ^ n)
          (zpow_ne_zero n hb₀) -
        littlewoodPaleyDilatedLowpassSchwartz (b ^ (n + 1))
          (zpow_ne_zero (n + 1) hb₀)) := by
    ext ξ
    let K₀ := littlewoodPaleyDilatedLowpassSchwartz (b ^ n)
      (zpow_ne_zero n hb₀)
    let K₁ := littlewoodPaleyDilatedLowpassSchwartz (b ^ (n + 1))
      (zpow_ne_zero (n + 1) hb₀)
    have hsub : 𝓕 (K₀ - K₁) = 𝓕 K₀ - 𝓕 K₁ := by
      calc
        𝓕 (K₀ - K₁) = 𝓕 (K₀ + -K₁) := by rw [sub_eq_add_neg]
        _ = 𝓕 K₀ + 𝓕 (-K₁) := FourierAdd.fourier_add _ _
        _ = 𝓕 K₀ - 𝓕 K₁ := by
          rw [FourierTransform.fourier_neg, sub_eq_add_neg]
    have hsubVal := congrArg (fun f : SchwartzMap ℝ ℂ => f ξ) hsub
    rw [littlewoodPaleyScaledKernelSchwartz_fourier hb₁ hb₀ n ξ,
      hsubVal]
    rw [SchwartzMap.sub_apply]
    rw [littlewoodPaleyDilatedLowpassSchwartz_fourier (b ^ n)
        (zpow_pos hbpos n) ξ,
      littlewoodPaleyDilatedLowpassSchwartz_fourier (b ^ (n + 1))
        (zpow_pos hbpos (n + 1)) ξ]
    simp [littlewoodPaleyCutoffDifference, zpow_add₀ hb₀, mul_assoc]
    congr 1
    ring
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => 𝓕⁻ f) hq
  have hleft : 𝓕⁻ (𝓕 (littlewoodPaleyScaledKernelSchwartz hb₀ n)) =
      littlewoodPaleyScaledKernelSchwartz hb₀ n :=
    FourierTransform.fourierInv_fourier_eq
      (E := SchwartzMap ℝ ℂ) (F := SchwartzMap ℝ ℂ)
      (littlewoodPaleyScaledKernelSchwartz hb₀ n)
  have hright := FourierTransform.fourierInv_fourier_eq
    (E := SchwartzMap ℝ ℂ) (F := SchwartzMap ℝ ℂ)
    (littlewoodPaleyDilatedLowpassSchwartz (b ^ n) (zpow_ne_zero n hb₀) -
      littlewoodPaleyDilatedLowpassSchwartz (b ^ (n + 1))
        (zpow_ne_zero (n + 1) hb₀))
  rw [hleft, hright] at h
  have hfunc : littlewoodPaleyScaledKernelSchwartz hb₀ n =
      littlewoodPaleyDilatedLowpassSchwartz (b ^ n) (zpow_ne_zero n hb₀) -
        littlewoodPaleyDilatedLowpassSchwartz (b ^ (n + 1))
          (zpow_ne_zero (n + 1) hb₀) := h
  have hx := congrArg (fun f : SchwartzMap ℝ ℂ => f x) hfunc
  simpa [littlewoodPaleyScaledKernelSchwartz_apply,
    littlewoodPaleyDilatedLowpassSchwartz_apply,
    littlewoodPaleyDilatedLowpassKernel] using hx

private theorem littlewoodPaley_sum_Icc_telescopes
    (N : ℕ) (g : ℤ → ℂ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (g n - g (n + 1)) =
      g (-(N : ℤ)) - g ((N : ℤ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      let left : ℤ := -((N + 1 : ℕ) : ℤ)
      let right : ℤ := ((N + 1 : ℕ) : ℤ)
      let old : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
      have hinterval :
          Finset.Icc left right = insert left (insert right old) := by
        ext z
        simp only [left, right, old, Finset.mem_Icc, Finset.mem_insert]
        omega
      have hrightNot : right ∉ old := by
        simp only [right, old, Finset.mem_Icc]
        omega
      have hleftNot : left ∉ insert right old := by
        simp only [left, right, old, Finset.mem_insert, Finset.mem_Icc]
        omega
      have hleftSucc : left + 1 = -(N : ℤ) := by
        dsimp [left]
        omega
      have hrightSucc : right + 1 = (N : ℤ) + 2 := by
        dsimp [right]
        omega
      rw [hinterval, Finset.sum_insert hleftNot,
        Finset.sum_insert hrightNot, ih]
      rw [hleftSucc, hrightSucc]
      dsimp [left, right]
      ring

private theorem littlewoodPaleySignedKernel_Icc_eq_dilatedLowpass_difference
    {b : ℝ} (hb₁ : 1 < b) (hb₀ : b ≠ 0) (N : ℕ) (x : ℝ) :
    littlewoodPaleySignedKernel b hb₀
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) x =
      littlewoodPaleyDilatedLowpassKernel littlewoodPaleyLowpassKernelSchwartz
          (b ^ (-(N : ℤ))) x -
        littlewoodPaleyDilatedLowpassKernel littlewoodPaleyLowpassKernelSchwartz
          (b ^ ((N : ℤ) + 1)) x := by
  rw [show littlewoodPaleySignedKernel b hb₀
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) x =
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          littlewoodPaleyScaledKernel b hb₀ n x by
      simp [littlewoodPaleySignedKernel]]
  rw [← littlewoodPaley_sum_Icc_telescopes N
    (fun n => littlewoodPaleyDilatedLowpassKernel
      littlewoodPaleyLowpassKernelSchwartz (b ^ n) x)]
  apply Finset.sum_congr rfl
  intro n hn
  exact littlewoodPaleyScaledKernel_eq_dilatedLowpass_difference
    hb₁ hb₀ n x

private theorem littlewoodPaleyLpConvolution_ae_eq_kernelIntegral_of_continuous_bounded
    {p : ℝ} (hp₁ : 1 < p) (K : ℝ → ℂ) (hKcont : Continuous K)
    (hKint : Integrable K volume) (f : ℝ → ℂ) (hf : Continuous f)
    (hfLp : MemLp f (ENNReal.ofReal p) volume)
    (hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    (lpComplexMeasureConvolution (ENNReal.ofReal p)
      (volume.withDensityᵥ K)
      (hfLp.toLp f) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y, K y * f (x-y) ∂volume := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  let F : Lp ℂ (ENNReal.ofReal p) volume :=
    hfLp.toLp f
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact littlewoodPaleyVariationMeasure_isFinite hKint
  obtain ⟨C, hC⟩ := hfbdd
  have hFae : (F : ℝ → ℂ) =ᵐ[volume] f := by
    simpa [F] using
      hfLp.coeFn_toLp
  have hraw := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_bounded
    hp₁ μ F f hf.measurable ⟨C, hC⟩ hFae
  have hpoint (x : ℝ) :
      complexMeasureConvolution μ f
        (hf.stronglyMeasurable.aestronglyMeasurable) x =
        ∫ y, K y * f (x-y) ∂volume := by
    let shifted : ℝ → ℂ := fun y => f (x-y)
    let hfAES : AEStronglyMeasurable f volume :=
      hf.stronglyMeasurable.aestronglyMeasurable
    have hshiftMeas : AEStronglyMeasurable shifted
        (kernelVariationMeasure K) := by
      exact (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have hshiftBound (y : ℝ) : ‖shifted y‖ ≤ C := by
      exact hC (x-y)
    have hshiftMem : MemLp shifted 1 (kernelVariationMeasure K) := by
      letI : IsFiniteMeasure (kernelVariationMeasure K) := by
        rw [← hvar]
        infer_instance
      exact MemLp.of_bound hshiftMeas C (ae_of_all _ hshiftBound)
    let u : Lp ℂ 1 (kernelVariationMeasure K) := hshiftMem.toLp shifted
    have hu : (u : ℝ → ℂ) =ᵐ[kernelVariationMeasure K] shifted := by
      exact hshiftMem.coeFn_toLp
    have hmk : f =ᵐ[volume] hfAES.mk f := hfAES.ae_eq_mk
    have hshiftMkVolume :
        shifted =ᵐ[volume] fun y =>
          hfAES.mk f (x-y) := by
      dsimp [shifted]
      exact (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hmk
    have hshiftMk :
        shifted =ᵐ[kernelVariationMeasure K] fun y =>
          hfAES.mk f (x-y) := by
      have hAC : kernelVariationMeasure K ≪ volume := by
        rw [kernelVariationMeasure]
        exact withDensity_absolutelyContinuous volume _
      exact hAC.ae_eq hshiftMkVolume
    have hμshift : (u : ℝ → ℂ) =ᵐ[μ.variation]
        fun y => hfAES.mk f (x-y) := by
      simpa [hvar] using hu.trans hshiftMk
    have hbridge := kernelDensity_vectorIntegral_eq_integral K hKcont hKint u
    have huWeight : (u : ℝ → ℂ) =ᵐ[volume.withDensity
        (fun y => ENNReal.ofReal ‖K y‖)] shifted := by
      simpa [kernelVariationMeasure, enorm_eq_nnnorm] using hu
    calc
      complexMeasureConvolution μ f
          (hf.stronglyMeasurable.aestronglyMeasurable) x =
          ∫ᵛ y, (hf.stronglyMeasurable.aestronglyMeasurable).mk f (x-y)
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := rfl
      _ = ∫ᵛ y, u y ∂[ContinuousLinearMap.mul ℝ ℂ; μ] :=
        VectorMeasure.integral_congr_ae hμshift.symm
      _ = ∫ y, K y * u y ∂volume := hbridge
      _ = ∫ y, K y * f (x-y) ∂volume := by
        exact integral_mul_congr_of_ae_withDensity_norm K
          (fun y => u y) shifted hKcont.measurable huWeight
  change (lpComplexMeasureConvolution (ENNReal.ofReal p) μ F : ℝ → ℂ) =ᵐ[volume] _
  exact hraw.trans (ae_of_all volume hpoint)

private theorem littlewoodPaleyLp2Convolution_ae_eq_kernelIntegral_of_continuous_bounded
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (f : ℝ → ℂ) (hf : Continuous f) (hf₂ : MemLp f 2 volume)
    (hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    (lpComplexMeasureConvolution 2 (volume.withDensityᵥ K)
      (hf₂.toLp f) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y, K y * f (x-y) ∂volume := by
  let F : Lp ℂ 2 volume := hf₂.toLp f
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact littlewoodPaleyVariationMeasure_isFinite hKint
  have hraw := complexMeasureConvolution_ae_eq_raw_integral μ F
  have hcongr := rawComplexMeasureConvolution_ae_congr μ f
    (fun y : ℝ => F y) hf.stronglyMeasurable (Lp.stronglyMeasurable F)
    (by simpa [F] using hf₂.coeFn_toLp.symm)
  have hpoint :
      (fun x : ℝ => complexMeasureConvolution μ (fun y => F y)
        (Lp.aestronglyMeasurable F) x) =ᵐ[volume]
        fun x => ∫ y, K y * f (x-y) ∂volume := by
    filter_upwards [hraw, hcongr] with x hrawX hcongrX
    calc
      complexMeasureConvolution μ (fun y => F y)
          (Lp.aestronglyMeasurable F) x =
          ∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hrawX
      _ = ∫ᵛ y, f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] :=
        hcongrX.symm
      _ = ∫ y, K y * f (x-y) ∂volume := by
        letI : IsFiniteMeasure (kernelVariationMeasure K) := by
          rw [← hvar]
          infer_instance
        obtain ⟨C, hC⟩ := hfbdd
        let shifted : ℝ → ℂ := fun y => f (x-y)
        have hshiftMeas : AEStronglyMeasurable shifted
            (kernelVariationMeasure K) :=
          (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        have hshiftBound (y : ℝ) : ‖shifted y‖ ≤ C := hC (x-y)
        let u : Lp ℂ 1 (kernelVariationMeasure K) :=
          (MemLp.of_bound hshiftMeas C (ae_of_all _ hshiftBound)).toLp shifted
        have hu : (u : ℝ → ℂ) =ᵐ[kernelVariationMeasure K] shifted :=
          (MemLp.of_bound hshiftMeas C (ae_of_all _ hshiftBound)).coeFn_toLp
        have hμae : (u : ℝ → ℂ) =ᵐ[μ.variation] shifted := by
          simpa [hvar] using hu
        calc
          ∫ᵛ y, shifted y ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
              ∫ᵛ y, u y ∂[ContinuousLinearMap.mul ℝ ℂ; μ] :=
            VectorMeasure.integral_congr_ae hμae.symm
          _ = ∫ y, K y * u y ∂volume :=
            kernelDensity_vectorIntegral_eq_integral K hKcont hKint u
          _ = ∫ y, K y * f (x-y) ∂volume := by
            exact integral_mul_congr_of_ae_withDensity_norm K
              (fun y => u y) shifted hKcont.measurable
              (by simpa [kernelVariationMeasure, enorm_eq_nnnorm] using hu)
  change (lpComplexMeasureConvolution 2 μ F : ℝ → ℂ) =ᵐ[volume] _
  exact (lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution μ F).trans hpoint

/-! For a complex Schwartz approximate identity, the Lp convergence follows
from translation continuity, total variation, a change of scale, and dominated
convergence. -/
private theorem lpComplexMeasureConvolution_tendsto_schwartzApprox
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ (∞ : ℝ≥0∞))
    (ρ : SchwartzMap ℝ ℂ) (hρmass : ∫ x : ℝ, ρ x ∂volume = 1)
    (a : ℕ → ℝ) (haPos : ∀ n, 0 < a n)
    (ha : Tendsto a atTop (𝓝 0))
    (F : Lp ℂ p (volume : Measure ℝ)) :
    Tendsto (fun n => lpComplexMeasureConvolution p
      (volume.withDensityᵥ (littlewoodPaleyDilatedLowpassKernel ρ (a n))) F)
      atTop (𝓝 F) := by
  let E : ℕ → ℝ → ℝ := fun n z => ‖ρ z‖ *
    ‖lpRightTranslate p (a n * z) F - F‖
  have hρnorm : Integrable (fun z : ℝ => ‖ρ z‖) volume := ρ.integrable.norm
  have hboundInt : Integrable (fun z : ℝ => 2 * ‖F‖ * ‖ρ z‖) volume := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hρnorm.const_mul (2 * ‖F‖)
  have hzero : lpRightTranslate p 0 F = F := by
    apply Lp.ext
    filter_upwards [coeFn_lpRightTranslate p 0 F] with x hx
    simpa [lpRightTranslate] using hx
  have hOrbitCont : Continuous (fun y : ℝ =>
      ‖lpRightTranslate p y F - F‖) := by
    exact ((continuous_lpRightTranslate hp F).sub continuous_const).norm
  have hEcont (n : ℕ) : Continuous (E n) := by
    dsimp [E]
    exact ρ.continuous.norm |>.mul
      (hOrbitCont.comp (continuous_const.mul continuous_id))
  have hEmem (n : ℕ) : AEStronglyMeasurable (E n) volume :=
    (hEcont n).aestronglyMeasurable
  have hEbound (n : ℕ) (z : ℝ) : ‖E n z‖ ≤ 2 * ‖F‖ * ‖ρ z‖ := by
    have hdiff : ‖lpRightTranslate p (a n * z) F - F‖ ≤ 2 * ‖F‖ := by
      calc
        _ ≤ ‖lpRightTranslate p (a n * z) F‖ + ‖F‖ := norm_sub_le _ _
        _ = 2 * ‖F‖ := by rw [norm_lpRightTranslate]; ring
    have hρnonneg : 0 ≤ ‖ρ z‖ := norm_nonneg _
    have hEnonneg : 0 ≤ E n z := mul_nonneg hρnonneg (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hEnonneg]
    calc
      E n z = ‖ρ z‖ * ‖lpRightTranslate p (a n * z) F - F‖ := rfl
      _ ≤ ‖ρ z‖ * (2 * ‖F‖) := mul_le_mul_of_nonneg_left hdiff hρnonneg
      _ = 2 * ‖F‖ * ‖ρ z‖ := by ring
  have hEpoint (z : ℝ) : Tendsto (fun n : ℕ => E n z) atTop (𝓝 0) := by
    have harg : Tendsto (fun n : ℕ => a n * z) atTop (𝓝 0) := by
      simpa using ha.mul_const z
    have hnorm : Tendsto (fun y : ℝ => ‖lpRightTranslate p y F - F‖)
        (𝓝 0) (𝓝 0) := by
      simpa [hzero] using (hOrbitCont.continuousAt (x := 0)).tendsto
    have hcomp := hnorm.comp harg
    simpa [E, mul_comm] using hcomp.const_mul ‖ρ z‖
  have hEintegral : Tendsto (fun n : ℕ => ∫ z : ℝ, E n z ∂volume)
      atTop (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun z : ℝ => 2 * ‖F‖ * ‖ρ z‖)
      (F := E) (f := fun _ : ℝ => (0 : ℝ))
      (F_measurable := fun n => hEmem n)
      (bound_integrable := hboundInt)
      (h_bound := fun n => ae_of_all volume (hEbound n))
      (h_lim := ae_of_all volume hEpoint)
    simpa using h
  have hConvBound (n : ℕ) :
      ‖lpComplexMeasureConvolution p
        (volume.withDensityᵥ (littlewoodPaleyDilatedLowpassKernel ρ (a n))) F - F‖ ≤
        ∫ z : ℝ, E n z ∂volume := by
    let K : ℝ → ℂ := littlewoodPaleyDilatedLowpassKernel ρ (a n)
    have ha0 : a n ≠ 0 := ne_of_gt (haPos n)
    have hKint : Integrable K volume := by
      dsimp [K, littlewoodPaleyDilatedLowpassKernel]
      exact Integrable.smul (a n)⁻¹ (ρ.integrable.comp_div ha0)
    have hKcont : Continuous K := by
      change Continuous (fun y : ℝ => ((a n)⁻¹ : ℝ) • ρ (y / a n))
      exact (ρ.continuous.comp (continuous_id.div_const (a n))).const_smul
        ((a n)⁻¹ : ℝ)
    have hKweightMeas : Measurable (fun y : ℝ => ‖K y‖₊) :=
      hKcont.nnnorm.measurable
    let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
    have hvar : μ.variation = kernelVariationMeasure K := by
      dsimp [μ, kernelVariationMeasure]
      rw [Measure.variation_withDensityᵥ hKint]
      congr 1
    letI : IsFiniteMeasure μ.variation := by
      rw [hvar]
      exact littlewoodPaleyVariationMeasure_isFinite hKint
    have hmass : μ Set.univ = 1 := by
      change (volume.withDensityᵥ K) Set.univ = _
      rw [withDensityᵥ_apply hKint MeasurableSet.univ]
      simp
      have hcomp := Measure.integral_comp_mul_left (fun z : ℝ => ρ z) (a n)⁻¹
      have hcomp' : ∫ x : ℝ, ρ ((a n)⁻¹ * x) ∂volume =
          (a n) * ∫ z : ℝ, ρ z ∂volume := by
        simpa [abs_of_pos (haPos n), smul_eq_mul] using hcomp
      calc
        ∫ x : ℝ, K x ∂volume = (a n)⁻¹ *
            ∫ x : ℝ, ρ ((a n)⁻¹ * x) ∂volume := by
              dsimp [K, littlewoodPaleyDilatedLowpassKernel]
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards [] with x
              congr 1
              field_simp [ha0]
        _ = (a n)⁻¹ * ((a n) * ∫ z : ℝ, ρ z ∂volume) := by rw [hcomp']
        _ = 1 := by rw [hρmass]; push_cast; field_simp [ha0]
    let B := lpComplexSmulBilinear p
    have hOrbit : μ.Integrable (fun y : ℝ => lpRightTranslate p y F) :=
      integrable_lpRightTranslate hp μ F
    have hconst : μ.Integrable (fun _ : ℝ => F) := by
      change Integrable (fun _ : ℝ => F) μ.variation
      exact integrable_const F
    have hdiffInt : μ.Integrable (fun y : ℝ => lpRightTranslate p y F - F) :=
      hOrbit.sub hconst
    have hdiffRep : lpComplexMeasureConvolution p μ F - F =
        ∫ᵛ y, lpRightTranslate p y F - F ∂[B; μ] := by
      unfold lpComplexMeasureConvolution
      calc
        (∫ᵛ y, lpRightTranslate p y F ∂[B; μ]) - F =
            (∫ᵛ y, lpRightTranslate p y F ∂[B; μ]) -
              ∫ᵛ y, (fun _ : ℝ => F) y ∂[B; μ] := by
                rw [VectorMeasure.integral_const]
                simp [B, hmass]
        _ = ∫ᵛ y, lpRightTranslate p y F - F ∂[B; μ] :=
              (VectorMeasure.integral_sub hOrbit hconst).symm
    have hnormInt := VectorMeasure.norm_integral_le_integral_norm
      (μ := μ) (B := B) (f := fun y : ℝ => lpRightTranslate p y F - F)
    have hBnorm : ‖B‖ ≤ 1 := norm_lpComplexSmulBilinear_le p
    have hweight : (∫ y : ℝ, ‖lpRightTranslate p y F - F‖
        ∂kernelVariationMeasure K) =
        ∫ y : ℝ, ‖K y‖ * ‖lpRightTranslate p y F - F‖ ∂volume := by
      rw [kernelVariationMeasure,
        integral_withDensity_eq_integral_smul hKweightMeas]
      apply integral_congr_ae
      filter_upwards [] with y
      rfl
    have hscale : (∫ y : ℝ, ‖K y‖ * ‖lpRightTranslate p y F - F‖ ∂volume) =
        ∫ z : ℝ, E n z ∂volume := by
      let g : ℝ → ℝ := fun z => ‖ρ z‖ * ‖lpRightTranslate p (a n * z) F - F‖
      have hgcomp := Measure.integral_comp_mul_left g (a n)⁻¹
      have hgcomp' : ∫ y : ℝ, g ((a n)⁻¹ * y) ∂volume =
          (a n) * ∫ z : ℝ, g z ∂volume := by
        simpa [abs_of_pos (haPos n), smul_eq_mul] using hgcomp
      calc
        ∫ y : ℝ, ‖K y‖ * ‖lpRightTranslate p y F - F‖ ∂volume =
            (a n)⁻¹ * ∫ y : ℝ, g ((a n)⁻¹ * y) ∂volume := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards [] with y
              have hKnorm : ‖K y‖ = (a n)⁻¹ * ‖ρ (y / a n)‖ := by
                dsimp [K, littlewoodPaleyDilatedLowpassKernel]
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_pos (inv_pos.mpr (haPos n))]
              have hdiv : y / a n = (a n)⁻¹ * y := by
                field_simp [ha0]
              have harg : a n * ((a n)⁻¹ * y) = y := by
                field_simp [ha0]
              rw [hKnorm, hdiv]
              dsimp [g]
              rw [harg]
              ring
        _ = (a n)⁻¹ * ((a n) * ∫ z : ℝ, g z ∂volume) := by rw [hgcomp']
        _ = ∫ z : ℝ, E n z ∂volume := by
              simp [g, E, ha0, mul_assoc]
    have hnormInt' : ‖∫ᵛ y, lpRightTranslate p y F - F ∂[B; μ]‖ ≤
        ‖B‖ * ∫ y : ℝ, ‖lpRightTranslate p y F - F‖
          ∂kernelVariationMeasure K := by simpa [hvar] using hnormInt
    calc
      ‖lpComplexMeasureConvolution p μ F - F‖ =
          ‖∫ᵛ y, lpRightTranslate p y F - F ∂[B; μ]‖ := by rw [hdiffRep]
      _ ≤ ‖B‖ * ∫ y : ℝ, ‖lpRightTranslate p y F - F‖
            ∂kernelVariationMeasure K := hnormInt'
      _ ≤ ∫ y : ℝ, ‖lpRightTranslate p y F - F‖
            ∂kernelVariationMeasure K := by
              have hintnonneg : 0 ≤ ∫ y : ℝ, ‖lpRightTranslate p y F - F‖
                  ∂kernelVariationMeasure K := integral_nonneg (fun _ => norm_nonneg _)
              nlinarith [hBnorm, hintnonneg]
      _ = ∫ y : ℝ, ‖K y‖ * ‖lpRightTranslate p y F - F‖ ∂volume := hweight
      _ = ∫ z : ℝ, E n z ∂volume := hscale
  have hnonneg (n : ℕ) : 0 ≤ ‖lpComplexMeasureConvolution p
      (volume.withDensityᵥ (littlewoodPaleyDilatedLowpassKernel ρ (a n))) F - F‖ := norm_nonneg _
  have hnormTendsto : Tendsto (fun n : ℕ => ‖lpComplexMeasureConvolution p
      (volume.withDensityᵥ (littlewoodPaleyDilatedLowpassKernel ρ (a n))) F - F‖)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall hnonneg) ?_ hEintegral
    exact Filter.Eventually.of_forall hConvBound
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using hnormTendsto)

/-- Broad dilates of a Schwartz low-pass kernel vanish on Schwartz inputs in
every finite `Lᵖ`, `p > 1`.  The proof uses the uniform `L¹` convolution
bound and the shrinking pointwise kernel bound, then applies the checked
`L¹`/sup interpolation lemma. -/
private theorem littlewoodPaleyDilatedLowpass_convolution_tendsto_zero
    {p b : ℝ} (hp₁ : 1 < p) (hb₁ : 1 < b)
    (ρ f : SchwartzMap ℝ ℂ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    Tendsto (fun n : ℕ => lpComplexMeasureConvolution (ENNReal.ofReal p)
      (volume.withDensityᵥ (littlewoodPaleyDilatedLowpassKernel ρ
        (b ^ (n + 1)))) ((f.memLp (ENNReal.ofReal p) volume).toLp f))
      atTop (𝓝 0) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let a : ℕ → ℝ := fun n => b ^ (n + 1)
  let K : ℕ → ℝ → ℂ := fun n => littlewoodPaleyDilatedLowpassKernel ρ (a n)
  let F : Lp ℂ (ENNReal.ofReal p) volume :=
    (f.memLp (ENNReal.ofReal p) volume).toLp f
  let u : ℕ → Lp ℂ (ENNReal.ofReal p) volume := fun n =>
    lpComplexMeasureConvolution (ENNReal.ofReal p)
      (volume.withDensityᵥ (K n)) F
  let S : ℝ := SchwartzMap.seminorm ℝ 0 0 ρ
  let Mf : ℝ := ∫ y : ℝ, ‖f y‖ ∂volume
  let B : ℝ := (∫ y : ℝ, ‖ρ y‖ ∂volume) * Mf
  let A : ℕ → ℝ := fun n => (a n)⁻¹ * (S * Mf)
  have hbpos : 0 < b := by linarith
  have haPos (n : ℕ) : 0 < a n := by
    exact pow_pos hbpos _
  have hKcont (n : ℕ) : Continuous (K n) := by
    dsimp [K]
    exact littlewoodPaleyDilatedLowpassKernel_continuous ρ (a n)
  have hKint (n : ℕ) : Integrable (K n) volume := by
    dsimp [K]
    exact littlewoodPaleyDilatedLowpassKernel_integrable ρ (ne_of_gt (haPos n))
  have hfint : Integrable f volume := f.integrable
  have hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 f, ?_⟩
    intro x
    simpa using f.le_seminorm ℝ 0 0 x
  have hrawBound (n : ℕ) := littlewoodPaleyRawConvolution_L1_bound
    (K n) f (hKint n) hfint f.continuous hfbdd
  have hbridge (n : ℕ) : (u n : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y, K n y * f (x-y) ∂volume := by
    dsimp [u, F, K]
    exact littlewoodPaleyLpConvolution_ae_eq_kernelIntegral_of_continuous_bounded
      hp₁ (littlewoodPaleyDilatedLowpassKernel ρ (a n))
      (littlewoodPaleyDilatedLowpassKernel_continuous ρ (a n))
      (littlewoodPaleyDilatedLowpassKernel_integrable ρ (ne_of_gt (haPos n)))
      f f.continuous (f.memLp (ENNReal.ofReal p) volume) hfbdd
  have hL1 (n : ℕ) :
      Integrable (fun x : ℝ => ‖(u n : ℝ → ℂ) x‖) volume ∧
        (∫ x : ℝ, ‖(u n : ℝ → ℂ) x‖ ∂volume) ≤ B := by
    have hnormAE : (fun x : ℝ => ‖(u n : ℝ → ℂ) x‖) =ᵐ[volume]
        (fun x => ‖∫ y, K n y * f (x-y) ∂volume‖) :=
      (hbridge n).mono fun x hx => congrArg norm hx
    have hInt : Integrable (fun x : ℝ => ‖(u n : ℝ → ℂ) x‖) volume :=
      (hrawBound n).1.congr hnormAE.symm
    refine ⟨hInt, ?_⟩
    rw [integral_congr_ae hnormAE]
    calc
      (∫ x : ℝ, ‖∫ y, K n y * f (x-y) ∂volume‖ ∂volume) ≤
          (∫ y : ℝ, ‖K n y‖ ∂volume) * Mf := (hrawBound n).2
      _ = B := by
        rw [littlewoodPaleyDilatedLowpassKernel_norm_integral ρ (haPos n)]
  have hS0 : 0 ≤ S := by
    have hρ := ρ.le_seminorm ℝ 0 0 (0 : ℝ)
    exact (norm_nonneg (ρ 0)).trans (by simpa using hρ)
  have hMf0 : 0 ≤ Mf := by
    dsimp [Mf]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hA0 (n : ℕ) : 0 ≤ A n := by
    dsimp [A]
    exact mul_nonneg (inv_nonneg.mpr (haPos n).le)
      (mul_nonneg hS0 hMf0)
  have haAtTop : Tendsto a atTop atTop := by
    have hpow := tendsto_pow_atTop_atTop_of_one_lt hb₁
    change Tendsto (fun n : ℕ => b ^ (n + 1)) atTop atTop
    exact hpow.comp (tendsto_add_atTop_nat 1)
  have hA : Tendsto A atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (a n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp haAtTop
    simpa [A, mul_assoc] using hinv.mul_const (S * Mf)
  have hSup (n : ℕ) : ∀ᵐ x : ℝ ∂volume,
      ‖(u n : ℝ → ℂ) x‖ ≤ A n := by
    filter_upwards [hbridge n] with x hx
    rw [hx]
    let c : ℝ := (a n)⁻¹ * S
    have hc0 : 0 ≤ c := by
      dsimp [c]
      exact mul_nonneg (inv_nonneg.mpr (haPos n).le) hS0
    have hshiftInt : Integrable (fun y : ℝ => ‖f (x-y)‖) volume := by
      exact (volume.measurePreserving_sub_left x).integrable_comp_of_integrable
        hfint.norm
    have hdomInt : Integrable (fun y : ℝ => c * ‖f (x-y)‖) volume :=
      hshiftInt.const_mul c
    have hpointInt : ‖∫ y : ℝ, K n y * f (x-y) ∂volume‖ ≤
        ∫ y : ℝ, c * ‖f (x-y)‖ ∂volume := by
      apply norm_integral_le_of_norm_le hdomInt
      filter_upwards [] with y
      calc
        ‖K n y * f (x-y)‖ = ‖K n y‖ * ‖f (x-y)‖ := norm_mul _ _
        _ ≤ ((a n)⁻¹ * S) * ‖f (x-y)‖ := by
          exact mul_le_mul_of_nonneg_right
            (littlewoodPaleyDilatedLowpassKernel_norm_le_seminorm
              ρ (haPos n) y) (norm_nonneg _)
        _ = c * ‖f (x-y)‖ := rfl
    have hshiftMass : ∫ y : ℝ, ‖f (x-y)‖ ∂volume = Mf := by
      dsimp [Mf]
      exact (volume.measurePreserving_sub_left x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding (fun y : ℝ => ‖f y‖)
    calc
      ‖∫ y : ℝ, K n y * f (x-y) ∂volume‖ ≤
          ∫ y : ℝ, c * ‖f (x-y)‖ ∂volume := hpointInt
      _ = c * ∫ y : ℝ, ‖f (x-y)‖ ∂volume := by rw [integral_const_mul]
      _ = A n := by simpa [c, A, Mf, mul_assoc] using congrArg (fun t : ℝ => c * t) hshiftMass
  have hdecay := lp_tendsto_zero_of_L1_bound_and_sup_tendsto
    hp₁ u A hA hA0 B hL1 hSup
  simpa [u, F] using hdecay

private theorem littlewoodPaleySignedIccLp_eq_dilatedLowpass_difference
    {p b : ℝ} (hp₁ : 1 < p) (hb₁ : 1 < b) (N : ℕ)
    (f : SchwartzMap ℝ ℂ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    littlewoodPaleySignedLpExtension hb₁ hp₁
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp)
      ((f.memLp (ENNReal.ofReal p) volume).toLp f) =
    lpComplexMeasureConvolution (ENNReal.ofReal p)
      (volume.withDensityᵥ (littlewoodPaleyDilatedLowpassKernel
        littlewoodPaleyLowpassKernelSchwartz (b ^ (-(N : ℤ)))))
        ((f.memLp (ENNReal.ofReal p) volume).toLp f) -
    lpComplexMeasureConvolution (ENNReal.ofReal p)
      (volume.withDensityᵥ (littlewoodPaleyDilatedLowpassKernel
        littlewoodPaleyLowpassKernelSchwartz (b ^ ((N : ℤ) + 1))))
        ((f.memLp (ENNReal.ofReal p) volume).toLp f) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  let Fp : Lp ℂ (ENNReal.ofReal p) volume :=
    (f.memLp (ENNReal.ofReal p) volume).toLp f
  let Ksum : ℝ → ℂ := littlewoodPaleySignedKernel b hb₀
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1)
  let Klo : ℝ → ℂ := littlewoodPaleyDilatedLowpassKernel
    littlewoodPaleyLowpassKernelSchwartz (b ^ (-(N : ℤ)))
  let Khi : ℝ → ℂ := littlewoodPaleyDilatedLowpassKernel
    littlewoodPaleyLowpassKernelSchwartz (b ^ ((N : ℤ) + 1))
  have hbpos : 0 < b := by linarith
  have hKsumInt : Integrable Ksum volume := by
    dsimp [Ksum]
    exact littlewoodPaleySignedKernel_integrable b hb₀
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1)
  have hKsumCont : Continuous Ksum := by
    dsimp [Ksum]
    exact (littlewoodPaleySignedKernel_smooth b hb₀
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1)).continuous
  have hKloPos : 0 < b ^ (-(N : ℤ)) := zpow_pos hbpos _
  have hKhiPos : 0 < b ^ ((N : ℤ) + 1) := zpow_pos hbpos _
  have hKloInt : Integrable Klo volume := by
    dsimp [Klo]
    exact littlewoodPaleyDilatedLowpassKernel_integrable
      littlewoodPaleyLowpassKernelSchwartz (ne_of_gt hKloPos)
  have hKhiInt : Integrable Khi volume := by
    dsimp [Khi]
    exact littlewoodPaleyDilatedLowpassKernel_integrable
      littlewoodPaleyLowpassKernelSchwartz (ne_of_gt hKhiPos)
  have hKloCont : Continuous Klo := by
    dsimp [Klo]
    exact littlewoodPaleyDilatedLowpassKernel_continuous
      littlewoodPaleyLowpassKernelSchwartz _
  have hKhiCont : Continuous Khi := by
    dsimp [Khi]
    exact littlewoodPaleyDilatedLowpassKernel_continuous
      littlewoodPaleyLowpassKernelSchwartz _
  have hKernel (y : ℝ) : Ksum y = Klo y - Khi y := by
    dsimp [Ksum, Klo, Khi]
    exact littlewoodPaleySignedKernel_Icc_eq_dilatedLowpass_difference
      hb₁ hb₀ N y
  have hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 f, ?_⟩
    intro x
    simpa using f.le_seminorm ℝ 0 0 x
  have hFpAE : (Fp : ℝ → ℂ) =ᵐ[volume] f := by
    simpa [Fp] using
      (f.memLp (ENNReal.ofReal p) volume).coeFn_toLp
  have hF2 : MemLp (Fp : ℝ → ℂ) 2 volume :=
    (memLp_congr_ae hFpAE).mpr (f.memLp 2 volume)
  have hF2eq : hF2.toLp (Fp : ℝ → ℂ) = (f.memLp 2 volume).toLp f := by
    apply Lp.ext
    filter_upwards [hF2.coeFn_toLp, (f.memLp 2 volume).coeFn_toLp, hFpAE]
      with x hx₁ hx₂ hx₃
    rw [hx₁, hx₃, hx₂]
  have hspec := (littlewoodPaleySignedLpExtension_spec hb₁ hp₁
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp)).2 Fp hF2
  rw [hF2eq] at hspec
  let F2 : Lp ℂ 2 volume := (f.memLp 2 volume).toLp f
  have hsumL2 :
      (kernelConvolutionL2Operator Ksum hKsumInt F2 : ℝ → ℂ) =ᵐ[volume]
        fun x => ∫ y, Ksum y * f (x-y) ∂volume := by
    change (lpComplexMeasureConvolution 2
      (volume.withDensityᵥ Ksum) F2 : ℝ → ℂ) =ᵐ[volume] _
    simpa [Ksum, F2] using
      littlewoodPaleyLp2Convolution_ae_eq_kernelIntegral_of_continuous_bounded
        Ksum hKsumCont hKsumInt f f.continuous (f.memLp 2 volume) hfbdd
  have hlowP :
      (lpComplexMeasureConvolution (ENNReal.ofReal p)
        (volume.withDensityᵥ Klo) Fp : ℝ → ℂ) =ᵐ[volume]
        fun x => ∫ y, Klo y * f (x-y) ∂volume := by
    dsimp [Fp]
    exact littlewoodPaleyLpConvolution_ae_eq_kernelIntegral_of_continuous_bounded
      hp₁ Klo hKloCont hKloInt f f.continuous
      (f.memLp (ENNReal.ofReal p) volume) hfbdd
  have hhighP :
      (lpComplexMeasureConvolution (ENNReal.ofReal p)
        (volume.withDensityᵥ Khi) Fp : ℝ → ℂ) =ᵐ[volume]
        fun x => ∫ y, Khi y * f (x-y) ∂volume := by
    dsimp [Fp]
    exact littlewoodPaleyLpConvolution_ae_eq_kernelIntegral_of_continuous_bounded
      hp₁ Khi hKhiCont hKhiInt f f.continuous
      (f.memLp (ENNReal.ofReal p) volume) hfbdd
  have hrawSplit (x : ℝ) :
      (∫ y, Ksum y * f (x-y) ∂volume) =
        (∫ y, Klo y * f (x-y) ∂volume) -
          (∫ y, Khi y * f (x-y) ∂volume) := by
    have hIntLo := littlewoodPaleyRawConvolution_integrable_at
      Klo f hKloInt f.continuous hfbdd x
    have hIntHi := littlewoodPaleyRawConvolution_integrable_at
      Khi f hKhiInt f.continuous hfbdd x
    rw [← integral_sub hIntLo hIntHi]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hKernel y]
    ring
  have hsumAE : (littlewoodPaleySignedLpExtension hb₁ hp₁
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp) Fp : ℝ → ℂ) =ᵐ[volume]
      fun x =>
        (lpComplexMeasureConvolution (ENNReal.ofReal p)
          (volume.withDensityᵥ Klo) Fp : ℝ → ℂ) x -
        (lpComplexMeasureConvolution (ENNReal.ofReal p)
          (volume.withDensityᵥ Khi) Fp : ℝ → ℂ) x := by
    filter_upwards [hspec, hsumL2, hlowP, hhighP] with x hs hsum hlo hhi
    calc
      (littlewoodPaleySignedLpExtension hb₁ hp₁
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp) Fp : ℝ → ℂ) x =
          (kernelConvolutionL2Operator Ksum hKsumInt F2 : ℝ → ℂ) x := hs
      _ = ∫ y, Ksum y * f (x-y) ∂volume := hsum
      _ = (∫ y, Klo y * f (x-y) ∂volume) -
          (∫ y, Khi y * f (x-y) ∂volume) := hrawSplit x
      _ = (lpComplexMeasureConvolution (ENNReal.ofReal p)
          (volume.withDensityᵥ Klo) Fp : ℝ → ℂ) x -
        (lpComplexMeasureConvolution (ENNReal.ofReal p)
          (volume.withDensityᵥ Khi) Fp : ℝ → ℂ) x := by
          rw [hlo, hhi]
  have hsubAE :
      (lpComplexMeasureConvolution (ENNReal.ofReal p)
        (volume.withDensityᵥ Klo) Fp -
       lpComplexMeasureConvolution (ENNReal.ofReal p)
        (volume.withDensityᵥ Khi) Fp : Lp ℂ (ENNReal.ofReal p) volume) =ᵐ[volume]
        fun x =>
          (lpComplexMeasureConvolution (ENNReal.ofReal p)
            (volume.withDensityᵥ Klo) Fp : ℝ → ℂ) x -
          (lpComplexMeasureConvolution (ENNReal.ofReal p)
            (volume.withDensityᵥ Khi) Fp : ℝ → ℂ) x := by
    exact Lp.coeFn_sub _ _
  apply Lp.ext
  exact hsumAE.trans hsubAE.symm

private theorem littlewoodPaleySignedIcc_tendsto_of_schwartz
    {p b : ℝ} (hp₁ : 1 < p) (hb₁ : 1 < b)
    (f : SchwartzMap ℝ ℂ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    Tendsto
      (fun N : ℕ => littlewoodPaleySignedLpExtension hb₁ hp₁
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp)
        ((f.memLp (ENNReal.ofReal p) volume).toLp f))
      atTop (𝓝 ((f.memLp (ENNReal.ofReal p) volume).toLp f)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  let ρ := littlewoodPaleyLowpassKernelSchwartz
  let Fp : Lp ℂ (ENNReal.ofReal p) volume :=
    (f.memLp (ENNReal.ofReal p) volume).toLp f
  let aLow : ℕ → ℝ := fun N => b ^ (-(N : ℤ))
  let low : ℕ → Lp ℂ (ENNReal.ofReal p) volume := fun N =>
    lpComplexMeasureConvolution (ENNReal.ofReal p)
      (volume.withDensityᵥ (littlewoodPaleyDilatedLowpassKernel ρ (aLow N))) Fp
  let high : ℕ → Lp ℂ (ENNReal.ofReal p) volume := fun N =>
    lpComplexMeasureConvolution (ENNReal.ofReal p)
      (volume.withDensityᵥ (littlewoodPaleyDilatedLowpassKernel ρ
        (b ^ ((N : ℤ) + 1)))) Fp
  have hbpos : 0 < b := by linarith
  have haLowPos (N : ℕ) : 0 < aLow N := by
    exact zpow_pos hbpos _
  have hscaleLow : (fun N : ℕ => aLow N) =ᶠ[atTop]
      fun N => (b ^ N)⁻¹ := by
    filter_upwards [] with N
    dsimp [aLow]
    rw [zpow_neg, zpow_natCast]
  have haLow : Tendsto aLow atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => b ^ N) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hb₁
    exact Tendsto.congr' hscaleLow.symm
      (tendsto_inv_atTop_zero.comp hpow)
  have hlow := lpComplexMeasureConvolution_tendsto_schwartzApprox
    (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top ρ
    (by simpa [ρ] using littlewoodPaleyLowpassKernelSchwartz_integral)
    aLow haLowPos haLow Fp
  have hscaleHigh (N : ℕ) :
      b ^ ((N : ℤ) + 1) = b ^ (N + 1) := by
    have hindex : (N : ℤ) + 1 = ((N + 1 : ℕ) : ℤ) := by omega
    rw [hindex, zpow_natCast]
  have hhigh₀ := littlewoodPaleyDilatedLowpass_convolution_tendsto_zero
    hp₁ hb₁ ρ f
  have hhigh : Tendsto high atTop (𝓝 0) := by
    apply Tendsto.congr' (Filter.Eventually.of_forall fun N => ?_) hhigh₀
    dsimp [high, Fp, ρ]
    rw [hscaleHigh N]
  have hdiff : Tendsto (fun N => low N - high N) atTop (𝓝 Fp) := by
    have h := hlow.sub hhigh
    simpa [low, high, Fp] using h
  have hidentity (N : ℕ) : littlewoodPaleySignedLpExtension hb₁ hp₁
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp) Fp =
      low N - high N := by
    simpa [low, high, Fp, aLow, ρ] using
      littlewoodPaleySignedIccLp_eq_dilatedLowpass_difference
        hp₁ hb₁ N f
  exact Tendsto.congr' (Filter.Eventually.of_forall fun N => (hidentity N).symm)
    hdiff

/-- The symmetric finite Littlewood--Paley sums converge in `Lᵖ`, with the
same finite signed-sum operator bound used in the square-function estimate. -/
theorem littlewoodPaleyResolutionLp {p b : ℝ} (hp₁ : 1 < p) (hb₁ : 1 < b)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        littlewoodPaleyProjectionLp hb₁ hp₁ n f)
      atTop (𝓝 f) := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  let C := weakTypeFromOffSupportStrongConstant p (littlewoodPaleyNb b)
    (littlewoodPaleyBb b hb₀)
  let M := max C 0
  let S (N : ℕ) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    littlewoodPaleySignedLpExtension hb₁ hp₁
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp)
  have hM : 0 ≤ M := le_max_right C 0
  have hCM : C ≤ M := le_max_left C 0
  have hSbound (N : ℕ) (u : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
      ‖S N u‖ ≤ M * ‖u‖ := by
    have hspec := (littlewoodPaleySignedLpExtension_spec hb₁ hp₁
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp)).1 u
    dsimp [S, C] at hspec ⊢
    calc
      ‖littlewoodPaleySignedLpExtension hb₁ hp₁
          (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp) u‖ ≤
          weakTypeFromOffSupportStrongConstant p (littlewoodPaleyNb b)
            (littlewoodPaleyBb b (ne_of_gt (by linarith : 0 < b))) * ‖u‖ := hspec
      _ ≤ max (weakTypeFromOffSupportStrongConstant p (littlewoodPaleyNb b)
            (littlewoodPaleyBb b (ne_of_gt (by linarith : 0 < b)))) 0 * ‖u‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  let hSchwartz (g : SchwartzMap ℝ ℂ) :
      Tendsto (fun N : ℕ => S N
        (SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p)
          (volume : Measure ℝ) g)) atTop
        (𝓝 (SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p)
          (volume : Measure ℝ) g)) := by
    change Tendsto (fun N : ℕ =>
      littlewoodPaleySignedLpExtension hb₁ hp₁
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp)
        ((g.memLp (ENNReal.ofReal p) volume).toLp g)) atTop
      (𝓝 ((g.memLp (ENNReal.ofReal p) volume).toLp g))
    exact littlewoodPaleySignedIcc_tendsto_of_schwartz hp₁ hb₁ g
  have hSsum (N : ℕ) : S N f =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        littlewoodPaleyProjectionLp hb₁ hp₁ n f := by
    have h := congrArg
      (fun T : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) => T f)
      (littlewoodPaleySignedLpExtension_eq_sum hb₁ hp₁
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (by simp))
    simpa [S] using h
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (2 * (M + 1))
  have hM1 : 0 < M + 1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hscale : (M + 1) * δ = ε / 2 := by
    dsimp [δ]
    field_simp
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p)
      (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (ENNReal.ofReal_ne_top)
  obtain ⟨g, hnear⟩ := hdense.exists_dist_lt f hδ
  let gLp : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p) (volume : Measure ℝ) g
  have happrox : dist f gLp < δ := by
    simpa [gLp] using hnear
  have hconv := hSchwartz g
  have hsmall : ∀ᶠ N : ℕ in atTop, dist (S N gLp) gLp < ε / 2 :=
    (Metric.tendsto_nhds.mp hconv) (ε / 2) (by linarith)
  have hnearSeq (N : ℕ) :
      dist (S N f) (S N gLp) ≤ M * dist f gLp := by
    calc
      dist (S N f) (S N gLp) = ‖S N f - S N gLp‖ := dist_eq_norm _ _
      _ = ‖S N (f - gLp)‖ := by rw [map_sub]
      _ ≤ M * ‖f - gLp‖ := hSbound N (f - gLp)
      _ = M * dist f gLp := by rw [dist_eq_norm]
  filter_upwards [hsmall] with N hN
  have htriangle :
      dist (S N f) f ≤ dist (S N f) (S N gLp) +
        dist (S N gLp) gLp + dist gLp f := by
    have h₁ := dist_triangle (S N f) (S N gLp) f
    have h₂ := dist_triangle (S N gLp) gLp f
    calc
      dist (S N f) f ≤ dist (S N f) (S N gLp) + dist (S N gLp) f :=
        h₁
      _ ≤ dist (S N f) (S N gLp) +
          (dist (S N gLp) gLp + dist gLp f) :=
        by linarith
      _ = dist (S N f) (S N gLp) + dist (S N gLp) gLp + dist gLp f := by ring
  have hnearSymm : dist gLp f = dist f gLp := dist_comm _ _
  have hlt : dist (S N f) f < ε := by
    calc
      dist (S N f) f ≤
          M * dist f gLp + dist (S N gLp) gLp + dist f gLp := by
            calc
              dist (S N f) f ≤
                  dist (S N f) (S N gLp) + dist (S N gLp) gLp + dist gLp f :=
                htriangle
              _ ≤ M * dist f gLp + dist (S N gLp) gLp + dist gLp f := by
                linarith [hnearSeq N]
              _ = M * dist f gLp + dist (S N gLp) gLp + dist f gLp := by
                rw [hnearSymm]
      _ = (M + 1) * dist f gLp + dist (S N gLp) gLp := by ring
      _ < (M + 1) * δ + ε / 2 := by
        apply add_lt_add
        · exact mul_lt_mul_of_pos_left happrox hM1
        · exact hN
      _ = ε := by rw [hscale]; ring
  rw [← hSsum N]
  exact hlt

/-- The exact Littlewood--Paley upper estimate and symmetric resolution from
`lj:littlewood-paley`, packaged under the blueprint manifest name. -/
theorem littlewoodPaleyUpper {b p : ℝ} (hb₁ : 1 < b) (hp₁ : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    (∀ (F : Finset ℤ) (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
      lpNorm (fun x : ℝ => Real.sqrt (∑ n ∈ F,
        ‖(littlewoodPaleyProjectionLp hb₁ hp₁ n f : ℝ → ℂ) x‖ ^ 2))
        (ENNReal.ofReal p) volume ≤ littlewoodPaleyUpperConstant p b
          (ne_of_gt (by linarith : 0 < b)) * ‖f‖) ∧
    (∀ f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        littlewoodPaleyProjectionLp hb₁ hp₁ n f) atTop (𝓝 f)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  constructor
  · intro F f
    exact littlewoodPaleyUpper_square hb₁ hp₁ F f
  · intro f
    exact littlewoodPaleyResolutionLp hp₁ hb₁ f

end

end FractionalPrimes.Literature.JSW

end
