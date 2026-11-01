module

public import FractionalPrimes.Literature.JSW.Conventions
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# JSW finite-vector duality and convolution facts

This module records checked interfaces for the `lj:vector-duality` node.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The pointwise vector used in the explicit reverse `Lᵖ` duality
argument.  At a nonzero vector it has the same direction and norm
`‖v‖^(p-1)`; at zero it is defined to be zero. -/
def lpNormingVector {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (p : ℝ) (v : H) : H :=
  ((‖v‖ ^ (p - 1)) / ‖v‖) • v

theorem norm_lpNormingVector
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {p : ℝ} (hp : 1 < p) (v : H) :
    ‖lpNormingVector p v‖ = ‖v‖ ^ (p - 1) := by
  by_cases hv : ‖v‖ = 0
  · simp [lpNormingVector, hv, Real.zero_rpow (sub_pos.mpr hp).ne']
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    rw [lpNormingVector, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.rpow_pos_of_pos hvpos _) hvpos),
      div_mul_cancel₀ _ hv]

theorem aestronglyMeasurable_lpNormingVector
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : α → H} (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    AEStronglyMeasurable (fun x => lpNormingVector p (f x)) μ := by
  unfold FractionalPrimes.Literature.JSW.lpNormingVector
  have hnorm : AEMeasurable (fun x => ‖f x‖) μ := hf.norm.aemeasurable
  have hcoeff : AEMeasurable (fun x => (‖f x‖ ^ (p - 1)) / ‖f x‖) μ :=
    (hnorm.pow_const (p - 1)).div hnorm
  exact hcoeff.aestronglyMeasurable.smul hf

theorem inner_lpNormingVector_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p : ℝ} (hp : 1 < p) (v : H) :
    inner ℂ (lpNormingVector p v) v = ((‖v‖ ^ p : ℝ) : ℂ) := by
  by_cases hv : ‖v‖ = 0
  · have hv0 : v = 0 := norm_eq_zero.mp hv
    simp [hv0, lpNormingVector, Real.zero_rpow (lt_trans zero_lt_one hp).ne']
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    rw [lpNormingVector]
    simp only [← algebraMap_smul ℂ ((‖v‖ ^ (p - 1)) / ‖v‖) v,
      RCLike.algebraMap_eq_ofReal, inner_smul_real_left,
      inner_self_eq_norm_sq_to_K, Algebra.smul_def]
    have hreal :
      (‖v‖ ^ (p - 1)) / ‖v‖ * ‖v‖ ^ 2 =
          ‖v‖ ^ p := by
      calc
        (‖v‖ ^ (p - 1)) / ‖v‖ * ‖v‖ ^ 2 =
            ‖v‖ ^ (p - 1) * ‖v‖ := by field_simp
        _ = ‖v‖ ^ (p - 1) * ‖v‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = ‖v‖ ^ ((p - 1) + 1) :=
          (Real.rpow_add hvpos (p - 1) 1).symm
        _ = ‖v‖ ^ p := by ring_nf
    norm_cast
    exact congrArg (fun z : ℝ => (z : ℂ)) hreal

theorem MemLp.lpNormingVector
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → H} (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun x =>
      FractionalPrimes.Literature.JSW.lpNormingVector p (f x))
      (ENNReal.ofReal q) μ := by
  have hf_int : Integrable (fun x => ‖f x‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hpq.pos.le] using
      hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hpq.pos) (by simp)
  have hnorm_int : Integrable (fun x =>
      ‖FractionalPrimes.Literature.JSW.lpNormingVector p (f x)‖ ^ q) μ := by
    simpa only [norm_lpNormingVector hpq.lt, ← Real.rpow_mul (norm_nonneg _),
      hpq.sub_one_mul_conj] using hf_int
  apply (integrable_norm_rpow_iff
    (aestronglyMeasurable_lpNormingVector hf.aestronglyMeasurable p)
    (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos) (by simp)).mp
  simpa [ENNReal.toReal_ofReal hpq.symm.pos.le] using hnorm_int

theorem lpNorm_lpNormingVector
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → H} (hf : MemLp f (ENNReal.ofReal p) μ) :
    lpNorm (fun x => lpNormingVector p (f x)) (ENNReal.ofReal q) μ =
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / q) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos) (by simp)
    (aestronglyMeasurable_lpNormingVector hf.aestronglyMeasurable p)]
  simp only [ENNReal.toReal_ofReal hpq.symm.pos.le]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [norm_lpNormingVector hpq.lt, ← Real.rpow_mul (norm_nonneg (f x)),
    hpq.sub_one_mul_conj]
  simp [one_div]

/-- The power integral defining a finite positive `Lᵖ` norm is exactly the
`p`-th real power of that norm. -/
theorem integral_norm_rpow_eq_lpNorm_rpow
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H]
    {p : ℝ} (hp : 0 < p)
    {f : α → H} (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫ x, ‖f x‖ ^ p ∂μ) =
      (lpNorm f (ENNReal.ofReal p) μ) ^ p := by
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp) (by simp) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le]
  rw [← Real.rpow_mul hI]
  simp [hp.ne']

/-- The unnormalized pointwise norming vector has conjugate `Lᵠ` norm
`‖f‖ₚ^(p-1)`. -/
theorem lpNorm_lpNormingVector_eq
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → H} (hf : MemLp f (ENNReal.ofReal p) μ) :
    lpNorm (fun x => lpNormingVector p (f x)) (ENNReal.ofReal q) μ =
      (lpNorm f (ENNReal.ofReal p) μ) ^ (p - 1) := by
  rw [lpNorm_lpNormingVector hpq hf,
    integral_norm_rpow_eq_lpNorm_rpow hpq.pos hf,
    ← Real.rpow_mul lpNorm_nonneg]
  congr 1
  rw [mul_one_div, hpq.div_conj_eq_sub_one]

/-- Reversing the two arguments in the pointwise norming identity does not
change its real value. -/
theorem inner_self_lpNormingVector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p : ℝ} (hp : 1 < p) (v : H) :
    inner ℂ v (lpNormingVector p v) = ((‖v‖ ^ p : ℝ) : ℂ) := by
  rw [← inner_conj_symm, inner_lpNormingVector_self hp]
  exact RCLike.conj_ofReal _

/-- The source's normalized pointwise `Lᵠ` norming function. -/
def normalizedLpNormingFunction
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (p : ℝ) (f : α → H) : α → H :=
  (lpNorm f (ENNReal.ofReal p) μ ^ (1 - p)) •
    (fun x => lpNormingVector p (f x))

theorem memLp_normalizedLpNormingFunction
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → H} (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (normalizedLpNormingFunction (μ := μ) p f)
      (ENNReal.ofReal q) μ := by
  exact (MemLp.lpNormingVector hpq hf).const_smul _

theorem lpNorm_normalizedLpNormingFunction
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → H} (hf : MemLp f (ENNReal.ofReal p) μ)
    (hpos : 0 < lpNorm f (ENNReal.ofReal p) μ) :
    lpNorm (normalizedLpNormingFunction (μ := μ) p f)
      (ENNReal.ofReal q) μ = 1 := by
  rw [normalizedLpNormingFunction, lpNorm_const_smul,
    lpNorm_lpNormingVector_eq hpq hf]
  change ‖lpNorm f (ENNReal.ofReal p) μ ^ (1 - p)‖ *
      lpNorm f (ENNReal.ofReal p) μ ^ (p - 1) = 1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg lpNorm_nonneg _),
    ← Real.rpow_add hpos]
  norm_num

theorem integral_inner_normalizedLpNormingFunction
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → H} (hf : MemLp f (ENNReal.ofReal p) μ)
    (hpos : 0 < lpNorm f (ENNReal.ofReal p) μ) :
    (∫ x, inner ℂ (f x)
      (normalizedLpNormingFunction (μ := μ) p f x) ∂μ) =
      (lpNorm f (ENNReal.ofReal p) μ : ℂ) := by
  let L : ℝ := lpNorm f (ENNReal.ofReal p) μ
  calc
    (∫ x, inner ℂ (f x)
        (normalizedLpNormingFunction (μ := μ) p f x) ∂μ) =
        ((L ^ (1 - p) : ℝ) : ℂ) * (∫ x, ((‖f x‖ ^ p : ℝ) : ℂ) ∂μ) := by
      simp only [normalizedLpNormingFunction, Pi.smul_apply]
      have hpoint (x : α) :
          inner ℂ (f x)
              (lpNorm f (ENNReal.ofReal p) μ ^ (1 - p) •
                lpNormingVector p (f x)) =
            ((L ^ (1 - p) : ℝ) : ℂ) * ((‖f x‖ ^ p : ℝ) : ℂ) := by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
          inner_self_lpNormingVector hpq.lt]
        simp [L]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
        integral_const_mul]
    _ = ((L ^ (1 - p) : ℝ) : ℂ) * ((∫ x, ‖f x‖ ^ p ∂μ : ℝ) : ℂ) := by
      exact congrArg (fun z : ℂ => ((L ^ (1 - p) : ℝ) : ℂ) * z)
        (integral_ofReal (𝕜 := ℂ))
    _ = (L : ℂ) := by
      dsimp [L]
      rw [integral_norm_rpow_eq_lpNorm_rpow hpq.pos hf]
      norm_cast
      rw [← Real.rpow_add hpos]
      norm_num
    _ = (lpNorm f (ENNReal.ofReal p) μ : ℂ) := by simp [L]

/-- Every finite positive `Lᵖ` function has a conjugate-exponent unit-ball
test function which attains its norm in the integral inner-product pairing. -/
theorem exists_unitLp_normingFunction
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → H} (hf : MemLp f (ENNReal.ofReal p) μ) :
    ∃ g : α → H,
      MemLp g (ENNReal.ofReal q) μ ∧
      lpNorm g (ENNReal.ofReal q) μ ≤ 1 ∧
      ‖∫ x, inner ℂ (f x) (g x) ∂μ‖ =
        lpNorm f (ENNReal.ofReal p) μ := by
  by_cases hzero : lpNorm f (ENNReal.ofReal p) μ = 0
  · refine ⟨fun _ => 0, MemLp.zero', ?_, ?_⟩
    · simp
    · simp [hzero]
  · have hpos : 0 < lpNorm f (ENNReal.ofReal p) μ :=
      lt_of_le_of_ne lpNorm_nonneg (Ne.symm hzero)
    refine ⟨normalizedLpNormingFunction (μ := μ) p f,
      memLp_normalizedLpNormingFunction hpq hf, ?_, ?_⟩
    · rw [lpNorm_normalizedLpNormingFunction hpq hf hpos]
    · rw [integral_inner_normalizedLpNormingFunction hpq hf hpos,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg lpNorm_nonneg]

/-- Hölder's inequality for the exact complex inner-product pairing used in
the finite-vector duality formula. -/
theorem norm_integral_inner_le_lpNorm_mul_lpNorm
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → H} (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ‖∫ x, inner ℂ (f x) (g x) ∂μ‖ ≤
      lpNorm f (ENNReal.ofReal p) μ *
        lpNorm g (ENNReal.ofReal q) μ := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 :=
    hpq.ennrealOfReal
  have hprod : Integrable (fun x => ‖f x‖ * ‖g x‖) μ := by
    change Integrable ((fun x => ‖f x‖) * (fun x => ‖g x‖)) μ
    exact hf.norm.integrable_mul hg.norm
  have hinner : Integrable (fun x => inner ℂ (f x) (g x)) μ :=
    hprod.mono'
      (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => norm_inner_le_norm (f x) (g x))
  calc
    ‖∫ x, inner ℂ (f x) (g x) ∂μ‖ ≤
        ∫ x, ‖inner ℂ (f x) (g x)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ :=
      integral_mono_ae hinner.norm hprod
        (Filter.Eventually.of_forall fun x => norm_inner_le_norm (f x) (g x))
    _ ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) *
          (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hf hg
    _ = lpNorm f (ENNReal.ofReal p) μ *
          lpNorm g (ENNReal.ofReal q) μ := by
      rw [lpNorm_eq_integral_norm_rpow_toReal
          (ENNReal.ofReal_ne_zero_iff.mpr hpq.pos) (by simp) hf.aestronglyMeasurable,
        lpNorm_eq_integral_norm_rpow_toReal
          (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos) (by simp) hg.aestronglyMeasurable]
      simp [ENNReal.toReal_ofReal hpq.pos.le,
        ENNReal.toReal_ofReal hpq.symm.pos.le]

/-- Pairing values attained by the conjugate-exponent `Lᵠ` unit ball. -/
def lpDualPairingValues
    {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure α) (q : ℝ) (f : α → H) : Set ℝ :=
  {a | ∃ g : α → H,
    MemLp g (ENNReal.ofReal q) μ ∧
    lpNorm g (ENNReal.ofReal q) μ ≤ 1 ∧
    a = ‖∫ x, inner ℂ (f x) (g x) ∂μ‖}

/-- Exact `Lᵖ` duality as a supremum of integral inner-product pairings over
the conjugate `Lᵠ` unit ball. -/
theorem lpNorm_eq_sSup_dualPairingValues
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → H} (hf : MemLp f (ENNReal.ofReal p) μ) :
    lpNorm f (ENNReal.ofReal p) μ =
      sSup (lpDualPairingValues μ q f) := by
  have hupper : ∀ a ∈ lpDualPairingValues μ q f,
      a ≤ lpNorm f (ENNReal.ofReal p) μ := by
    rintro a ⟨g, hg, hgOne, rfl⟩
    calc
      ‖∫ x, inner ℂ (f x) (g x) ∂μ‖ ≤
          lpNorm f (ENNReal.ofReal p) μ *
            lpNorm g (ENNReal.ofReal q) μ :=
        norm_integral_inner_le_lpNorm_mul_lpNorm hpq hf hg
      _ ≤ lpNorm f (ENNReal.ofReal p) μ * 1 :=
        mul_le_mul_of_nonneg_left hgOne lpNorm_nonneg
      _ = lpNorm f (ENNReal.ofReal p) μ := mul_one _
  have hnonempty : (lpDualPairingValues μ q f).Nonempty := by
    refine ⟨0, fun _ => 0, MemLp.zero', by simp, ?_⟩
    simp
  have hbdd : BddAbove (lpDualPairingValues μ q f) :=
    ⟨lpNorm f (ENNReal.ofReal p) μ, hupper⟩
  obtain ⟨g, hg, hgOne, hpair⟩ := exists_unitLp_normingFunction hpq hf
  have hmem : lpNorm f (ENNReal.ofReal p) μ ∈
      lpDualPairingValues μ q f :=
    ⟨g, hg, hgOne, hpair.symm⟩
  exact le_antisymm (le_csSup hbdd hmem) (csSup_le hnonempty hupper)

/- The `lpPairing` interface is the exact integral pairing from the blueprint.
This bridge records its Hölder upper bound, with no finite-dimensional
assumption on the target spaces. -/
theorem lpPairing_norm_le
    {α 𝕜 E F G : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q : ℝ≥0∞}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [CompleteSpace G]
    (B : E →L[𝕜] F →L[𝕜] G) (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.lpPairing μ p q f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  have hpair : B.lpPairing μ p q f g = L1.integral (B.holder (r := 1) f g) := by
    simp [ContinuousLinearMap.lpPairing, ← L1.integral_eq', L1.integral_eq_integral]
  rw [hpair]
  calc
    ‖L1.integral (B.holder (r := 1) f g)‖ ≤ ‖B.holder (r := 1) f g‖ := L1.norm_integral_le _
    _ ≤ ‖B‖ * ‖f‖ * ‖g‖ := ContinuousLinearMap.norm_holder_apply_apply_le B f g

/-- Compactly supported continuous tests approximate every finite-exponent
real-line `Lp` function in the power-integral metric. Such tests are bounded,
so they lie in the test class in `lj:vector-duality`. -/
theorem exists_boundedCompactSupportLpApproximation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {p : ℝ} (hp : 0 < p) {F : ℝ → H}
    (hF : MemLp F (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ → H, HasCompactSupport G ∧ Continuous G ∧
      (∫ x, ‖F x - G x‖ ^ p ∂volume) ≤ ε ∧
      MemLp G (ENNReal.ofReal p) volume ∧ ∃ C : ℝ, ∀ x, ‖G x‖ ≤ C := by
  obtain ⟨G, hGsupport, hGerror, hGcontinuous, hGmem⟩ :=
    hF.exists_hasCompactSupport_integral_rpow_sub_le hp hε
  obtain ⟨C, hC⟩ := hGcontinuous.bounded_above_of_compact_support hGsupport
  exact ⟨G, hGsupport, hGcontinuous, hGerror, hGmem, C, hC⟩

/-- Direct `lpNorm` version of compact-support density. -/
theorem exists_boundedCompactSupportLpNormApproximation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {p : ℝ} (_hp : 0 < p) {F : ℝ → H}
    (hF : MemLp F (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ → H, HasCompactSupport G ∧ Continuous G ∧
      lpNorm (F - G) (ENNReal.ofReal p) volume ≤ ε ∧
      MemLp G (ENNReal.ofReal p) volume ∧ ∃ C : ℝ, ∀ x, ‖G x‖ ≤ C := by
  have hεne : ENNReal.ofReal ε ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hε
  obtain ⟨G, hGsupport, hGerror, hGcontinuous, hGmem⟩ :=
    hF.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hεne
  have htoReal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hGerror
  rw [toReal_eLpNorm, ENNReal.toReal_ofReal hε.le] at htoReal
  obtain ⟨C, hC⟩ := hGcontinuous.bounded_above_of_compact_support hGsupport
  exact ⟨G, hGsupport, hGcontinuous, htoReal, hGmem, C, hC⟩

/-- Integral inner products are integrable under conjugate `Lᵖ` hypotheses. -/
theorem integrable_inner_of_memLp
    {α H : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → H} (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    Integrable (fun x => inner ℂ (f x) (g x)) μ := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 :=
    hpq.ennrealOfReal
  have hprod : Integrable (fun x => ‖f x‖ * ‖g x‖) μ := by
    change Integrable ((fun x => ‖f x‖) * (fun x => ‖g x‖)) μ
    exact hf.norm.integrable_mul hg.norm
  exact hprod.mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => norm_inner_le_norm (f x) (g x))

/-- Pairing values from bounded compactly supported tests in the conjugate
unit ball. -/
def boundedCompactLpDualPairingValues
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (q : ℝ) (f : ℝ → H) : Set ℝ :=
  {a | ∃ g : ℝ → H,
    HasCompactSupport g ∧
    (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) ∧
    MemLp g (ENNReal.ofReal q) volume ∧
    lpNorm g (ENNReal.ofReal q) volume ≤ 1 ∧
    a = ‖∫ x, inner ℂ (f x) (g x) ∂volume‖}

/-- Bounded compactly supported functions give the same exact dual
supremum as the full conjugate-exponent unit ball. -/
theorem lpNorm_eq_sSup_boundedCompactLpDualPairingValues
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : ℝ → H} (hf : MemLp f (ENNReal.ofReal p) volume) :
    lpNorm f (ENNReal.ofReal p) volume =
      sSup (boundedCompactLpDualPairingValues q f) := by
  let L : ℝ := lpNorm f (ENNReal.ofReal p) volume
  have hupper : ∀ a ∈ boundedCompactLpDualPairingValues q f, a ≤ L := by
    rintro a ⟨g, _hgsupport, _hgbounded, hg, hgOne, rfl⟩
    calc
      ‖∫ x, inner ℂ (f x) (g x) ∂volume‖ ≤
          lpNorm f (ENNReal.ofReal p) volume *
            lpNorm g (ENNReal.ofReal q) volume :=
        norm_integral_inner_le_lpNorm_mul_lpNorm hpq hf hg
      _ ≤ lpNorm f (ENNReal.ofReal p) volume * 1 :=
        mul_le_mul_of_nonneg_left hgOne lpNorm_nonneg
      _ = L := by simp [L]
  have hzeroMem : 0 ∈ boundedCompactLpDualPairingValues q f := by
    refine ⟨fun _ => 0, ?_, ⟨0, by simp⟩, MemLp.zero', by simp, ?_⟩
    · simp [HasCompactSupport]
    · simp
  have hnonempty : (boundedCompactLpDualPairingValues q f).Nonempty :=
    ⟨0, hzeroMem⟩
  have hbdd : BddAbove (boundedCompactLpDualPairingValues q f) :=
    ⟨L, hupper⟩
  change L = sSup (boundedCompactLpDualPairingValues q f)
  apply le_antisymm
  · apply le_of_forall_lt
    intro a haL
    by_cases haNeg : a < 0
    · exact lt_csSup_of_lt hbdd hzeroMem haNeg
    · have ha0 : 0 ≤ a := le_of_not_gt haNeg
      have hLpos : 0 < L := lt_of_le_of_lt ha0 haL
      let e : ℝ := (L - a) / (4 * L)
      have hepos : 0 < e := by
        dsimp [e]
        exact div_pos (sub_pos.mpr haL) (mul_pos (by norm_num) hLpos)
      have heLtOne : e < 1 := by
        dsimp [e]
        rw [div_lt_one (mul_pos (by norm_num) hLpos)]
        nlinarith
      let g₀ : ℝ → H := normalizedLpNormingFunction (μ := volume) p f
      have hg₀mem : MemLp g₀ (ENNReal.ofReal q) volume := by
        simpa [g₀] using memLp_normalizedLpNormingFunction hpq hf
      have hg₀norm : lpNorm g₀ (ENNReal.ofReal q) volume = 1 := by
        simpa [g₀, L] using
          lpNorm_normalizedLpNormingFunction hpq hf hLpos
      have hg₀pair : (∫ x, inner ℂ (f x) (g₀ x) ∂volume) = (L : ℂ) := by
        simpa [g₀, L] using
          integral_inner_normalizedLpNormingFunction hpq hf hLpos
      obtain ⟨G, hGsupport, _hGcontinuous, hGerror, hGmem, C, hC⟩ :=
        exists_boundedCompactSupportLpNormApproximation
          hpq.symm.pos hg₀mem hepos
      have hqOne : 1 ≤ ENNReal.ofReal q :=
        ENNReal.one_le_ofReal.mpr hpq.symm.lt.le
      have hGnorm : lpNorm G (ENNReal.ofReal q) volume ≤ 1 + e := by
        have htri := lpNorm_le_lpNorm_add_lpNorm_sub'
          (f := G) (g := g₀) hg₀mem hqOne
        rw [hg₀norm, lpNorm_sub_comm] at htri
        linarith
      let c : ℝ := (1 + e)⁻¹
      have hcpos : 0 < c := by
        dsimp [c]
        exact inv_pos.mpr (by linarith)
      let g : ℝ → H := c • G
      have hgsupport : HasCompactSupport g := by
        have heq : g = (fun _ : ℝ => c) • G := by
          ext x
          simp [g]
        rw [heq]
        exact hGsupport.smul_left
      have hgbounded : ∃ D : ℝ, ∀ x, ‖g x‖ ≤ D := by
        refine ⟨|c| * C, ?_⟩
        intro x
        simp only [g, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)
      have hgmem : MemLp g (ENNReal.ofReal q) volume := by
        simpa [g] using hGmem.const_smul c
      have hgnorm : lpNorm g (ENNReal.ofReal q) volume ≤ 1 := by
        rw [show lpNorm g (ENNReal.ofReal q) volume =
            ‖c‖ * lpNorm G (ENNReal.ofReal q) volume by
              simpa [g] using
                (lpNorm_const_smul (p := ENNReal.ofReal q) c G volume)]
        rw [Real.norm_eq_abs, abs_of_pos hcpos]
        calc
          c * lpNorm G (ENNReal.ofReal q) volume ≤ c * (1 + e) :=
            mul_le_mul_of_nonneg_left hGnorm hcpos.le
          _ = 1 := by
            dsimp [c]
            field_simp
      have hg₀int := integrable_inner_of_memLp hpq hf hg₀mem
      have hGint := integrable_inner_of_memLp hpq hf hGmem
      have hdiffPair :
          ‖(∫ x, inner ℂ (f x) (g₀ x) ∂volume) -
              (∫ x, inner ℂ (f x) (G x) ∂volume)‖ ≤ L * e := by
        have hbound := norm_integral_inner_le_lpNorm_mul_lpNorm hpq hf
          (hg₀mem.sub hGmem)
        have hid :
            (∫ x, inner ℂ (f x) (g₀ x - G x) ∂volume) =
              (∫ x, inner ℂ (f x) (g₀ x) ∂volume) -
                (∫ x, inner ℂ (f x) (G x) ∂volume) := by
          rw [← integral_sub hg₀int hGint]
          apply integral_congr_ae
          filter_upwards [] with x
          exact inner_sub_right _ _ _
        change ‖∫ x, inner ℂ (f x) (g₀ x - G x) ∂volume‖ ≤ _ at hbound
        rw [hid] at hbound
        simpa [L] using
          hbound.trans (mul_le_mul_of_nonneg_left hGerror lpNorm_nonneg)
      have hGpairLower :
          L - L * e ≤ ‖∫ x, inner ℂ (f x) (G x) ∂volume‖ := by
        have hreverse := norm_sub_norm_le
          (∫ x, inner ℂ (f x) (g₀ x) ∂volume)
          (∫ x, inner ℂ (f x) (G x) ∂volume)
        rw [hg₀pair, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hLpos] at hreverse
        rw [hg₀pair] at hdiffPair
        linarith
      have hgpair :
          (∫ x, inner ℂ (f x) (g x) ∂volume) =
            (c : ℂ) * (∫ x, inner ℂ (f x) (G x) ∂volume) := by
        have hpoint (x : ℝ) :
            inner ℂ (f x) (g x) =
              (c : ℂ) * inner ℂ (f x) (G x) := by
          dsimp [g]
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
          simp
        rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
        rw [integral_const_mul]
      have hfrac : e * (a + L) < L - a := by
        dsimp [e]
        field_simp
        nlinarith
      have haScaled : a < c * (L - L * e) := by
        have hdenpos : 0 < 1 + e := by linarith
        have hdiv : a < (L - L * e) / (1 + e) := by
          rw [lt_div_iff₀ hdenpos]
          nlinarith
        simpa [c, div_eq_mul_inv, mul_comm] using hdiv
      have haPair : a < ‖∫ x, inner ℂ (f x) (g x) ∂volume‖ := by
        rw [hgpair, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hcpos]
        exact haScaled.trans_le
          (mul_le_mul_of_nonneg_left hGpairLower hcpos.le)
      have hgSet : ‖∫ x, inner ℂ (f x) (g x) ∂volume‖ ∈
          boundedCompactLpDualPairingValues q f :=
        ⟨g, hgsupport, hgbounded, hgmem, hgnorm, rfl⟩
      exact lt_csSup_of_lt hbdd hgSet haPair
  · exact csSup_le hnonempty hupper

/-- Unit-ball pairings indexed directly by `Lp` elements. -/
def lpElementDualPairingValues
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {P : ℝ≥0∞} (q : ℝ) (F : Lp H P (volume : Measure ℝ)) : Set ℝ :=
  {a | ∃ G : Lp H (ENNReal.ofReal q) (volume : Measure ℝ),
    lpNorm (G : ℝ → H) (ENNReal.ofReal q) volume ≤ 1 ∧
    a = ‖∫ x, inner ℂ ((F : ℝ → H) x) ((G : ℝ → H) x) ∂volume‖}

/-- The representative-level duality theorem, reindexed by genuine `Lp`
elements. -/
theorem lpNorm_eq_sSup_lpElementDualPairingValues
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (F : Lp H (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpNorm (F : ℝ → H) (ENNReal.ofReal p) volume =
      sSup (lpElementDualPairingValues q F) := by
  rw [lpNorm_eq_sSup_dualPairingValues hpq (Lp.memLp F)]
  congr 1
  ext a
  constructor
  · rintro ⟨g, hg, hgOne, rfl⟩
    let G : Lp H (ENNReal.ofReal q) (volume : Measure ℝ) := hg.toLp g
    have hGae : (G : ℝ → H) =ᵐ[volume] g := by
      simpa [G] using hg.coeFn_toLp
    have hGnorm :
        lpNorm (G : ℝ → H) (ENNReal.ofReal q) volume =
          lpNorm g (ENNReal.ofReal q) volume := by
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae hGae)
    refine ⟨G, hGnorm.trans_le hgOne, ?_⟩
    apply congrArg norm
    apply integral_congr_ae
    filter_upwards [hGae] with x hx
    rw [hx]
  · rintro ⟨G, hGOne, rfl⟩
    exact ⟨(G : ℝ → H), Lp.memLp G, hGOne, rfl⟩

/-- Scalar-to-vector and vector-to-scalar adjoint operators have exactly the
same norm at conjugate exponents. The `Fact` instances in the displayed type
are constructed from `hpq`; they add no hypotheses. -/
theorem lpAdjointOperator_norm_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
    ∀ (T : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℂ]
        Lp H (ENNReal.ofReal p) (volume : Measure ℝ))
      (S : Lp H (ENNReal.ofReal q) (volume : Measure ℝ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)),
      (∀ f g,
        (∫ x, inner ℂ ((T f : Lp H (ENNReal.ofReal p) (volume : Measure ℝ)) x)
            ((g : Lp H (ENNReal.ofReal q) (volume : Measure ℝ)) x) ∂volume) =
          ∫ x, inner ℂ ((f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) x)
            ((S g : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) x) ∂volume) →
      ‖T‖ = ‖S‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
  intro T S hadj
  apply le_antisymm
  · apply T.opNorm_le_bound (norm_nonneg S)
    intro f₀
    have hnonempty :
        (lpElementDualPairingValues q (T f₀)).Nonempty := by
      refine ⟨0, 0, ?_, ?_⟩
      · change (eLpNorm ((0 : Lp H (ENNReal.ofReal q) volume) : ℝ → H)
            (ENNReal.ofReal q) volume).toReal ≤ 1
        rw [← Lp.norm_def]
        simp
      · simp
    have hdual := lpNorm_eq_sSup_lpElementDualPairingValues hpq (T f₀)
    change ‖T f₀‖ ≤ ‖S‖ * ‖f₀‖
    rw [show ‖T f₀‖ =
        lpNorm (T f₀ : ℝ → H) (ENNReal.ofReal p) volume by rfl,
      hdual]
    apply csSup_le hnonempty
    rintro a ⟨g, hgOne, rfl⟩
    have hgOne' : ‖g‖ ≤ 1 := by exact hgOne
    have hholder := norm_integral_inner_le_lpNorm_mul_lpNorm hpq
      (Lp.memLp f₀) (Lp.memLp (S g))
    change ‖∫ x, inner ℂ ((f₀ : ℝ → ℂ) x) ((S g : ℝ → ℂ) x) ∂volume‖ ≤
      ‖f₀‖ * ‖S g‖ at hholder
    calc
      ‖∫ x, inner ℂ ((T f₀ : ℝ → H) x) ((g : ℝ → H) x) ∂volume‖ =
          ‖∫ x, inner ℂ ((f₀ : ℝ → ℂ) x) ((S g : ℝ → ℂ) x) ∂volume‖ :=
        congrArg norm (hadj f₀ g)
      _ ≤ ‖f₀‖ * ‖S g‖ := hholder
      _ ≤ ‖f₀‖ * (‖S‖ * ‖g‖) :=
        mul_le_mul_of_nonneg_left (S.le_opNorm g) (norm_nonneg f₀)
      _ ≤ ‖f₀‖ * (‖S‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgOne' (norm_nonneg S))
          (norm_nonneg f₀)
      _ = ‖S‖ * ‖f₀‖ := by ring
  · apply S.opNorm_le_bound (norm_nonneg T)
    intro g₀
    have hnonempty :
        (lpElementDualPairingValues p (S g₀)).Nonempty := by
      refine ⟨0, 0, ?_, ?_⟩
      · change (eLpNorm ((0 : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ)
            (ENNReal.ofReal p) volume).toReal ≤ 1
        rw [← Lp.norm_def]
        simp
      · simp
    have hdual := lpNorm_eq_sSup_lpElementDualPairingValues hpq.symm (S g₀)
    change ‖S g₀‖ ≤ ‖T‖ * ‖g₀‖
    rw [show ‖S g₀‖ =
        lpNorm (S g₀ : ℝ → ℂ) (ENNReal.ofReal q) volume by rfl,
      hdual]
    apply csSup_le hnonempty
    rintro a ⟨f₀, hfOne, rfl⟩
    have hfOne' : ‖f₀‖ ≤ 1 := by exact hfOne
    have hconj :
        ‖∫ x, inner ℂ ((S g₀ : ℝ → ℂ) x) ((f₀ : ℝ → ℂ) x) ∂volume‖ =
          ‖∫ x, inner ℂ ((f₀ : ℝ → ℂ) x) ((S g₀ : ℝ → ℂ) x) ∂volume‖ := by
      have hint :
          (∫ x, inner ℂ ((S g₀ : ℝ → ℂ) x) ((f₀ : ℝ → ℂ) x) ∂volume) =
            conj (∫ x, inner ℂ ((f₀ : ℝ → ℂ) x)
              ((S g₀ : ℝ → ℂ) x) ∂volume) := by
        rw [← integral_conj]
        apply integral_congr_ae
        filter_upwards [] with x
        exact (inner_conj_symm _ _).symm
      rw [hint]
      exact RCLike.norm_conj _
    have hholder := norm_integral_inner_le_lpNorm_mul_lpNorm hpq
      (Lp.memLp (T f₀)) (Lp.memLp g₀)
    change ‖∫ x, inner ℂ ((T f₀ : ℝ → H) x) ((g₀ : ℝ → H) x) ∂volume‖ ≤
      ‖T f₀‖ * ‖g₀‖ at hholder
    calc
      ‖∫ x, inner ℂ ((S g₀ : ℝ → ℂ) x) ((f₀ : ℝ → ℂ) x) ∂volume‖ =
          ‖∫ x, inner ℂ ((f₀ : ℝ → ℂ) x) ((S g₀ : ℝ → ℂ) x) ∂volume‖ :=
        hconj
      _ = ‖∫ x, inner ℂ ((T f₀ : ℝ → H) x) ((g₀ : ℝ → H) x) ∂volume‖ :=
        congrArg norm (hadj f₀ g₀).symm
      _ ≤ ‖T f₀‖ * ‖g₀‖ := hholder
      _ ≤ (‖T‖ * ‖f₀‖) * ‖g₀‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm f₀) (norm_nonneg g₀)
      _ ≤ (‖T‖ * 1) * ‖g₀‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfOne' (norm_nonneg T))
          (norm_nonneg g₀)
      _ = ‖T‖ * ‖g₀‖ := by ring

/-- The probability-measure Cauchy--Schwarz estimate in the form needed for
the pointwise square estimate in `lj:vector-duality`.  This is Jensen's
inequality for the convex function `z ↦ ‖z‖²`. -/
theorem norm_integral_sq_le_integral_norm_sq_probability
    {α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [IsProbabilityMeasure μ]
    {f : α → E} (hf : Integrable f μ)
    (hf_sq : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hconvex : ConvexOn ℝ Set.univ (fun z : E => ‖z‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  exact hconvex.map_integral_le
    (continuous_norm.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    hf (by simpa [Function.comp_def] using hf_sq)

/-- Pointwise probability-convolution square estimate, with precisely the
integrability conditions that make both Bochner integrals meaningful. -/
theorem jswProbabilityConvolution_square_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℂ) (x : ℝ)
    (hf : Integrable (fun y => f (x - y)) μ)
    (hf_sq : Integrable (fun y => ‖f (x - y)‖ ^ 2) μ) :
    ‖jswConvolution μ f x‖ ^ 2 ≤ ∫ y, ‖f (x - y)‖ ^ 2 ∂μ := by
  exact norm_integral_sq_le_integral_norm_sq_probability hf hf_sq

end

end FractionalPrimes.Literature.JSW

end
