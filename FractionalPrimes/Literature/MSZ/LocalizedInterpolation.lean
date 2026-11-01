module

public import FractionalPrimes.Literature.MSZ.StrongInterpolation
public import FractionalPrimes.FiniteMomentExhaustion
public import FractionalPrimes.Literature.MSZ.VectorConvolutionLowerAssembly
public import FractionalPrimes.Literature.MSZ.VectorConvolutionUpperAssembly
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Pointwise additivity of an integer-kernel convolution whenever the two
input series are summable. This is the linearity fact needed for the scalar
subadditivity step in `lm:localInterpolation`. -/
theorem localInterpolation_integerKernelConvolution_add
    (K : IntegerL1Kernel) (f g : ℤ → ℂ) (x : ℤ)
    (hf : Summable (fun m : ℤ => K.coeff m * f (x - m)))
    (hg : Summable (fun m : ℤ => K.coeff m * g (x - m))) :
    integerKernelConvolution K (f + g) x =
      integerKernelConvolution K f x + integerKernelConvolution K g x := by
  have hsum : Summable (fun m : ℤ => K.coeff m * (f + g) (x - m)) := by
    simpa [Pi.add_apply, mul_add] using hf.add hg
  have hfInt : IntegerKernelConvolutionExistsAt K f x := by
    change Integrable (fun m : ℤ => K.coeff m * f (x - m)) Measure.count
    exact (MeasureTheory.integrable_count_iff).2 hf.norm
  have hgInt : IntegerKernelConvolutionExistsAt K g x := by
    change Integrable (fun m : ℤ => K.coeff m * g (x - m)) Measure.count
    exact (MeasureTheory.integrable_count_iff).2 hg.norm
  have hsumInt : IntegerKernelConvolutionExistsAt K (f + g) x := by
    change Integrable
      (fun m : ℤ => K.coeff m * (f + g) (x - m)) Measure.count
    exact (MeasureTheory.integrable_count_iff).2 hsum.norm
  rw [integerKernelConvolution_eq_tsum K (f + g) x hsumInt,
    integerKernelConvolution_eq_tsum K f x hfInt,
    integerKernelConvolution_eq_tsum K g x hgInt]
  calc
    (∑' m : ℤ, K.coeff m * (f + g) (x - m)) =
        ∑' m : ℤ, (K.coeff m * f (x - m) + K.coeff m * g (x - m)) := by
      apply tsum_congr
      intro m
      simp [Pi.add_apply, mul_add]
    _ = (∑' m : ℤ, K.coeff m * f (x - m)) +
          ∑' m : ℤ, K.coeff m * g (x - m) := hf.tsum_add hg

/-- An `lp` pointwise majorant makes the convolution integral exist at each
integer, by the kernel's absolute summability and the coordinate bound for
sequence `lp`. -/
theorem localInterpolation_convolutionExistsAt_of_lp_majorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (K : IntegerL1Kernel)
    (G : lp (fun _ : ℤ => ℝ) p) (f : ℤ → ℂ)
    (hGnonneg : ∀ y, 0 ≤ G y) (hbound : ∀ y, ‖f y‖ ≤ G y) (x : ℤ) :
    IntegerKernelConvolutionExistsAt K f x := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hGnorm (y : ℤ) : ‖f y‖ ≤ ‖G‖ := by
    calc
      ‖f y‖ ≤ G y := hbound y
      _ = ‖G y‖ := (Real.norm_of_nonneg (hGnonneg y)).symm
      _ ≤ ‖G‖ := lp.norm_apply_le_norm hp0 G y
  have hcoeff : Summable (fun m : ℤ => ‖K.coeff m‖ * ‖G‖) :=
    K.summable_norm.mul_right ‖G‖
  have hterm : Summable (fun m : ℤ => ‖K.coeff m * f (x - m)‖) :=
    hcoeff.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hGnorm (x - m)) (norm_nonneg _))
  change Integrable (fun m : ℤ => K.coeff m * f (x - m)) Measure.count
  rw [MeasureTheory.integrable_count_iff]
  exact hterm

/-- Every coordinate of a square function is bounded by its full pointwise
majorant. -/
theorem localInterpolation_squareCoordinate_le_majorant
    (a : ℤ → ℤ → ℂ) (G : ℤ → ℝ)
    (hsummable : ∀ x, Summable (fun h : ℤ => ‖a x h‖ ^ 2))
    (hfull : ∀ x, Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2) ≤ G x)
    (x h : ℤ) : ‖a x h‖ ≤ G x := by
  have hterm : ‖a x h‖ ^ 2 ≤ ∑' k : ℤ, ‖a x k‖ ^ 2 := by
    have hle := (hsummable x).sum_le_tsum ({h} : Finset ℤ)
      (fun k _ => sq_nonneg (‖a x k‖))
    simpa using hle
  calc
    ‖a x h‖ = Real.sqrt (‖a x h‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (∑' k : ℤ, ‖a x k‖ ^ 2) := Real.sqrt_le_sqrt hterm
    _ ≤ G x := hfull x

/-- The finite-family vector convolution is additive when its scalar input
operators are additive and their full square functions have `lp` majorants.
This proves the subadditivity input required by `lm:interpolation`, while
using the exact pointwise convolution representatives. -/
theorem localInterpolation_vectorConvolution_add
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ)
    (K : ι × Fin N → IntegerL1Kernel) (index : ι → ℤ)
    (S : ℤ → (ℤ → ℂ) → ℤ → ℂ) (f g : ℤ → ℂ)
    (hSadd : ∀ h y, S h (f + g) y = S h f y + S h g y)
    (Gf Gg : lp (fun _ : ℤ => ℝ) p)
    (hsummableF : ∀ x, Summable (fun h : ℤ => ‖S h f x‖ ^ 2))
    (hfullF : ∀ x, Real.sqrt (∑' h : ℤ, ‖S h f x‖ ^ 2) ≤ Gf x)
    (hsummableG : ∀ x, Summable (fun h : ℤ => ‖S h g x‖ ^ 2))
    (hfullG : ∀ x, Real.sqrt (∑' h : ℤ, ‖S h g x‖ ^ 2) ≤ Gg x)
    (x : ℤ) :
    integerKernelVectorConvolution K
        (fun y => WithLp.toLp 2 (fun i : ι × Fin N => S (index i.1) (f + g) y)) x =
      integerKernelVectorConvolution K
        (fun y => WithLp.toLp 2 (fun i : ι × Fin N => S (index i.1) f y)) x +
      integerKernelVectorConvolution K
        (fun y => WithLp.toLp 2 (fun i : ι × Fin N => S (index i.1) g y)) x := by
  have hGfnonneg : ∀ y, 0 ≤ Gf y := fun y =>
    (Real.sqrt_nonneg _).trans (hfullF y)
  have hGgnonneg : ∀ y, 0 ≤ Gg y := fun y =>
    (Real.sqrt_nonneg _).trans (hfullG y)
  have hinput :
      (fun y => WithLp.toLp 2
        (fun i : ι × Fin N => S (index i.1) (f + g) y)) =
        (fun y => WithLp.toLp 2
          (fun i : ι × Fin N => S (index i.1) f y)) +
        (fun y => WithLp.toLp 2
          (fun i : ι × Fin N => S (index i.1) g y)) := by
    funext y
    apply PiLp.ext
    intro i
    simp [hSadd]
  unfold integerKernelVectorConvolution
  rw [hinput]
  apply PiLp.ext
  intro i
  let h := index i.1
  have hExistF (z : ℤ) :
      IntegerKernelConvolutionExistsAt (K i) (S h f) z := by
    apply localInterpolation_convolutionExistsAt_of_lp_majorant (K := K i) Gf
    · exact hGfnonneg
    · intro y
      exact localInterpolation_squareCoordinate_le_majorant
        (fun z t => S t f z) Gf hsummableF hfullF y h
  have hExistG (z : ℤ) :
      IntegerKernelConvolutionExistsAt (K i) (S h g) z := by
    apply localInterpolation_convolutionExistsAt_of_lp_majorant (K := K i) Gg
    · exact hGgnonneg
    · intro y
      exact localInterpolation_squareCoordinate_le_majorant
        (fun z t => S t g z) Gg hsummableG hfullG y h
  have hSeriesF (z : ℤ) :
      Summable (fun m : ℤ => (K i).coeff m * S h f (z - m)) := by
    have hInt := hExistF z
    change Integrable (fun m : ℤ => (K i).coeff m * S h f (z - m)) Measure.count at hInt
    exact Summable.of_norm (MeasureTheory.integrable_count_iff.mp hInt)
  have hSeriesG (z : ℤ) :
      Summable (fun m : ℤ => (K i).coeff m * S h g (z - m)) := by
    have hInt := hExistG z
    change Integrable (fun m : ℤ => (K i).coeff m * S h g (z - m)) Measure.count at hInt
    exact Summable.of_norm (MeasureTheory.integrable_count_iff.mp hInt)
  change integerKernelConvolution (K i) (S h f + S h g) x = _
  exact localInterpolation_integerKernelConvolution_add (K i) (S h f) (S h g) x
    (hSeriesF x) (hSeriesG x)

/-- The `eLpNorm` of the pointwise fiber norm of a sequence `lp` vector is
exactly its real `lp` norm, with the extended counting-measure semantics
retained on the left. -/
theorem localInterpolation_eLpNorm_lp_norm
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {p : ℝ} (hp : 1 < p)
    (f : lp (fun _ : ℤ => E) (ENNReal.ofReal p)) :
    eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal p) Measure.count =
      ENNReal.ofReal ‖f‖ := by
  have hpReal : 0 < p := lt_trans zero_lt_one hp
  have hpENN : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hpReal.le]
    exact hpReal
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨(ENNReal.one_le_ofReal).2 (le_of_lt hp)⟩
  have hsumENN : Summable (fun x : ℤ => ‖f x‖ ^ (ENNReal.ofReal p).toReal) :=
    (lp.memℓp f).summable hpENN
  have hsum : Summable (fun x : ℤ => ‖f x‖ ^ p) := by
    simpa only [ENNReal.toReal_ofReal hpReal.le] using hsumENN
  have hterms :
      (∑' x : ℤ, ‖‖f x‖‖ₑ ^ (ENNReal.ofReal p).toReal) =
        ENNReal.ofReal (∑' x : ℤ, ‖f x‖ ^ p) := by
    calc
      _ = ∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ p) := by
        apply tsum_congr
        intro x
        have hnorm : ‖‖f x‖‖ₑ = ENNReal.ofReal ‖f x‖ := by simp
        rw [ENNReal.toReal_ofReal hpReal.le, hnorm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hpReal.le]
      _ = ENNReal.ofReal (∑' x : ℤ, ‖f x‖ ^ p) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun x => Real.rpow_nonneg (norm_nonneg (f x)) _) hsum).symm
  have hsumNonneg : 0 ≤ ∑' x : ℤ, ‖f x‖ ^ p :=
    tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg (f x)) _
  have hnorm :
      (∑' x : ℤ, ‖f x‖ ^ p) ^ (1 / p) = ‖f‖ := by
    simpa only [ENNReal.toReal_ofReal hpReal.le] using
      (lp.norm_eq_tsum_rpow hpENN f).symm
  calc
    eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal p) Measure.count =
        (∑' x : ℤ, ‖‖f x‖‖ₑ ^ (ENNReal.ofReal p).toReal) ^
          (1 / (ENNReal.ofReal p).toReal) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
        (measurable_of_countable _).aestronglyMeasurable, lintegral_count]
    _ = (ENNReal.ofReal (∑' x : ℤ, ‖f x‖ ^ p)) ^ (1 / p) := by
      rw [hterms, ENNReal.toReal_ofReal hpReal.le]
    _ = ENNReal.ofReal ((∑' x : ℤ, ‖f x‖ ^ p) ^ (1 / p)) :=
      ENNReal.ofReal_rpow_of_nonneg hsumNonneg (one_div_nonneg.mpr hpReal.le)
    _ = ENNReal.ofReal ‖f‖ := by rw [hnorm]

/-- An extended-valued counting-measure `Lᵖ` bound has an exact real sequence
`lp` representative. This is the representative bridge needed to turn the
source square-function estimate, encoded with an extended-valued square sum,
into the real majorant used by the endpoint estimates. -/
theorem localInterpolation_realLpRepresentative_of_extended_eLpNorm_bound
    {p C : ℝ} (hp : 1 < p) (F : ℤ → ℝ≥0∞) (hC : 0 ≤ C)
    (hbound : eLpNorm F (ENNReal.ofReal p) Measure.count ≤ ENNReal.ofReal C) :
    ∃ G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
      (∀ x, G x = (F x).toReal) ∧
        (∀ x, ENNReal.ofReal (G x) = F x) ∧ ‖G‖ ≤ C := by
  have hpReal : 0 < p := lt_trans zero_lt_one hp
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpToReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hpReal.le
  have hpENNPos : 0 < (ENNReal.ofReal p).toReal := by
    rw [hpToReal]
    exact hpReal
  have hLpFinite : eLpNorm F (ENNReal.ofReal p) Measure.count < ∞ :=
    lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hIntegralFinite :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpTop
      (measurable_of_countable F).aestronglyMeasurable).mp hLpFinite
  have hTsumFinite :
      (∑' x : ℤ, ‖F x‖ₑ ^ (ENNReal.ofReal p).toReal) < ∞ := by
    simpa only [lintegral_count] using hIntegralFinite
  have htermFinite (x : ℤ) : ‖F x‖ₑ ^ (ENNReal.ofReal p).toReal < ∞ :=
    lt_of_le_of_lt
      (ENNReal.le_tsum (f := fun x : ℤ =>
        ‖F x‖ₑ ^ (ENNReal.ofReal p).toReal) x) hTsumFinite
  have hFfinite (x : ℤ) : F x ≠ ∞ := by
    intro htop
    have htermNe : ‖F x‖ₑ ^ (ENNReal.ofReal p).toReal ≠ ∞ :=
      (htermFinite x).ne
    apply htermNe
    simp [htop, enorm_eq_self, ENNReal.top_rpow_of_pos hpENNPos]
  let R : ℤ → ℝ := fun x => (F x).toReal
  have hsumToReal := ENNReal.summable_toReal hTsumFinite.ne
  have hsumR : Summable (fun x : ℤ => ‖R x‖ ^ p) := by
    refine hsumToReal.congr ?_
    intro x
    dsimp [R]
    rw [abs_of_nonneg ENNReal.toReal_nonneg, hpToReal]
    exact (ENNReal.toReal_rpow (F x) p).symm
  have hmem : Memℓp R (ENNReal.ofReal p) := by
    rw [memℓp_gen_iff (ENNReal.toReal_pos hp0 hpTop)]
    simpa only [hpToReal] using hsumR
  let G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p) := ⟨R, hmem⟩
  have hGapply (x : ℤ) : G x = (F x).toReal := rfl
  have hGnonneg (x : ℤ) : 0 ≤ G x := by
    rw [hGapply]
    exact ENNReal.toReal_nonneg
  have hGofReal (x : ℤ) : ENNReal.ofReal (G x) = F x := by
    rw [hGapply]
    exact ENNReal.ofReal_toReal (hFfinite x)
  have hmeasF : AEStronglyMeasurable F Measure.count :=
    (measurable_of_countable F).aestronglyMeasurable
  have hmeasG : AEStronglyMeasurable (fun x : ℤ => G x) Measure.count :=
    (measurable_of_countable (fun x : ℤ => G x)).aestronglyMeasurable
  have hLpEq :
      eLpNorm F (ENNReal.ofReal p) Measure.count =
        eLpNorm (fun x : ℤ => G x) (ENNReal.ofReal p) Measure.count := by
    apply eLpNorm_congr_enorm_ae hmeasF hmeasG
    filter_upwards with x
    rw [enorm_eq_self, hGapply]
    exact (Real.enorm_toReal (hFfinite x)).symm
  have hnormG :
      eLpNorm (fun x : ℤ => G x) (ENNReal.ofReal p) Measure.count =
        ENNReal.ofReal ‖G‖ := by
    calc
      eLpNorm (fun x : ℤ => G x) (ENNReal.ofReal p) Measure.count =
          eLpNorm (fun x : ℤ => ‖G x‖) (ENNReal.ofReal p) Measure.count := by
            symm
            exact eLpNorm_norm (fun x : ℤ => G x) hmeasG
      _ = ENNReal.ofReal ‖G‖ := localInterpolation_eLpNorm_lp_norm hp G
  have hnormBound : ENNReal.ofReal ‖G‖ ≤ ENNReal.ofReal C := by
    calc
      ENNReal.ofReal ‖G‖ =
          eLpNorm (fun x : ℤ => G x) (ENNReal.ofReal p) Measure.count := hnormG.symm
      _ = eLpNorm F (ENNReal.ofReal p) Measure.count := hLpEq.symm
      _ ≤ ENNReal.ofReal C := hbound
  refine ⟨G, hGapply, hGofReal, ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hnormBound

/-- The source square function with its value in `ℝ≥0∞`, so a divergent
coordinate sum is represented by `∞` rather than by the real `tsum` default. -/
noncomputable def localInterpolationExtendedSquareFunction
    (a : ℤ → ℤ → ℂ) : ℤ → ℝ≥0∞ :=
  fun x => (∑' h : ℤ, ENNReal.ofReal (‖a x h‖ ^ 2)) ^ (1 / 2 : ℝ)

/-- Finite extended square mass gives summability of the corresponding real
square sequence. -/
private theorem localInterpolation_realSquareSummable_of_extended_mass_ne_top
    (a : ℤ → ℤ → ℂ) (x : ℤ)
    (hfinite : (∑' h : ℤ, ENNReal.ofReal (‖a x h‖ ^ 2)) ≠ ∞) :
    Summable (fun h : ℤ => ‖a x h‖ ^ 2) := by
  have hsum := ENNReal.summable_toReal hfinite
  refine hsum.congr ?_
  intro h
  rw [ENNReal.toReal_ofReal (sq_nonneg (‖a x h‖))]

/-- When the extended square mass is finite, taking its `toReal` value agrees
with the square function formed from the real summable series. -/
private theorem localInterpolation_extendedSquare_toReal_eq_real_sqrt
    (a : ℤ → ℤ → ℂ) (x : ℤ)
    (hsummable : Summable (fun h : ℤ => ‖a x h‖ ^ 2)) :
    (localInterpolationExtendedSquareFunction a x).toReal =
      Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2) := by
  have hsum := ENNReal.ofReal_tsum_of_nonneg
    (fun h : ℤ => sq_nonneg (‖a x h‖)) hsummable
  dsimp [localInterpolationExtendedSquareFunction]
  rw [← ENNReal.toReal_rpow, ← hsum,
    ENNReal.toReal_ofReal (tsum_nonneg fun h => sq_nonneg (‖a x h‖)),
    ← Real.sqrt_eq_rpow]

/-- The exact square-function `eLpNorm` hypothesis supplies the nonnegative
real `lp` majorant and pointwise summability used by the vector endpoints. The
extended-valued definition preserves divergence semantics until finiteness
has been deduced from the `eLpNorm` bound. -/
theorem localInterpolation_squareMajorant_of_extended_eLpNorm_bound
    {p C : ℝ} (hp : 1 < p) (a : ℤ → ℤ → ℂ) (hC : 0 ≤ C)
    (hbound : eLpNorm (localInterpolationExtendedSquareFunction a)
      (ENNReal.ofReal p) Measure.count ≤ ENNReal.ofReal C) :
    ∃ G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
      (∀ x, G x = Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2)) ∧
        (∀ x, Summable (fun h : ℤ => ‖a x h‖ ^ 2)) ∧ ‖G‖ ≤ C := by
  obtain ⟨G, hGtoReal, hGofReal, hGnorm⟩ :=
    localInterpolation_realLpRepresentative_of_extended_eLpNorm_bound hp
      (localInterpolationExtendedSquareFunction a) hC hbound
  have hmassNeTop (x : ℤ) :
      (∑' h : ℤ, ENNReal.ofReal (‖a x h‖ ^ 2)) ≠ ∞ := by
    have hFneTop : localInterpolationExtendedSquareFunction a x ≠ ∞ := by
      intro htop
      have hne : ENNReal.ofReal (G x) ≠ ∞ := ENNReal.ofReal_ne_top
      rw [hGofReal x] at hne
      exact hne htop
    intro htop
    apply hFneTop
    dsimp [localInterpolationExtendedSquareFunction]
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
  have hsummable (x : ℤ) : Summable (fun h : ℤ => ‖a x h‖ ^ 2) :=
    localInterpolation_realSquareSummable_of_extended_mass_ne_top a x (hmassNeTop x)
  refine ⟨G, ?_, hsummable, hGnorm⟩
  intro x
  rw [hGtoReal x]
  exact localInterpolation_extendedSquare_toReal_eq_real_sqrt a x (hsummable x)

/-- A finite-support input has finite counting-measure `eLpNorm` at every
finite exponent greater than one. This is the finite-input step needed when
converting the source square-function bound into an extended-valued bound. -/
private theorem localInterpolation_finiteSupport_eLpNorm_lt_top
    {p : ℝ} (hp : 1 < p) (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm f (ENNReal.ofReal p) Measure.count < ∞ := by
  classical
  have hpReal : 0 < p := lt_trans zero_lt_one hp
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpToRealPos : 0 < (ENNReal.ofReal p).toReal :=
    ENNReal.toReal_pos hp0 hpTop
  let s : Finset ℤ := hf.toFinset
  have hfOn : ∀ x ∉ s, f x = 0 := by
    intro x hx
    by_contra hfx
    exact hx (hf.mem_toFinset.mpr (Function.mem_support.mpr hfx))
  have hrep : f = (fun x => if x ∈ s then f x else 0) := by
    funext x
    by_cases hx : x ∈ s
    · simp [hx]
    · simp [hx, hfOn x hx]
  have hsum : (∑ x ∈ s, ‖f x‖ₑ ^ (ENNReal.ofReal p).toReal) < ∞ := by
    apply ENNReal.sum_lt_top.2
    intro x hx
    exact ENNReal.rpow_lt_top_of_nonneg
      hpToRealPos.le enorm_lt_top.ne
  conv_lhs => rw [hrep]
  rw [eLpNorm_finiteSupport_eq_sum_rpow
    (p := ENNReal.ofReal p) hp0 hpTop s f]
  exact ENNReal.rpow_lt_top_of_nonneg
    (one_div_nonneg.mpr hpToRealPos.le) hsum.ne

/-- Convert one source square-function estimate into the checked real `lp`
majorant, using finite support to recover the input `eLpNorm` from its `toReal`
value. The square function remains extended-valued until its finiteness is
deduced by the majorant theorem. -/
private theorem localInterpolation_squareMajorant_of_sourceBound
    {p P : ℝ} (hp : 1 < p) (hP : 0 ≤ P)
    (a : ℤ → ℤ → ℂ) (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (hSq : eLpNorm (localInterpolationExtendedSquareFunction a)
      (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal P * eLpNorm f (ENNReal.ofReal p) Measure.count) :
    ∃ G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
      (∀ x, G x = Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2)) ∧
        (∀ x, Summable (fun h : ℤ => ‖a x h‖ ^ 2)) ∧
        ‖G‖ ≤ P * (eLpNorm f (ENNReal.ofReal p) Measure.count).toReal := by
  have hfFinite := localInterpolation_finiteSupport_eLpNorm_lt_top hp f hf
  have hInputOfReal :
      ENNReal.ofReal (eLpNorm f (ENNReal.ofReal p) Measure.count).toReal =
        eLpNorm f (ENNReal.ofReal p) Measure.count :=
    ENNReal.ofReal_toReal hfFinite.ne
  have hbound :
      eLpNorm (localInterpolationExtendedSquareFunction a)
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal
          (P * (eLpNorm f (ENNReal.ofReal p) Measure.count).toReal) := by
    let E : ℝ := (eLpNorm f (ENNReal.ofReal p) Measure.count).toReal
    calc
      _ ≤ ENNReal.ofReal P * eLpNorm f (ENNReal.ofReal p) Measure.count := hSq
      _ = ENNReal.ofReal P * ENNReal.ofReal E := by
        rw [← hInputOfReal]
      _ = ENNReal.ofReal (P * E) :=
        (ENNReal.ofReal_mul hP).symm
  exact localInterpolation_squareMajorant_of_extended_eLpNorm_bound hp
    a (mul_nonneg hP ENNReal.toReal_nonneg) hbound

/-- A full-domain real `lp` witness for the square-function estimate gives
the extended-valued source bound on each finite-support input. The finite
input is embedded into sequence `lp` with its exact pointwise representative. -/
private theorem localInterpolation_fullSquareWitness_of_finiteSupport
    {p P : ℝ} (hp : 1 < p)
    (S : ℤ → ((ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ)))
    (hSq : ∀ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ∃ G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
        (∀ x, 0 ≤ G x) ∧
        (∀ x, ENNReal.ofReal (G x) =
          localInterpolationExtendedSquareFunction
            (fun x h => S h (F : ℤ → ℂ) x) x) ∧
        ‖G‖ ≤ P * ‖F‖)
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm (localInterpolationExtendedSquareFunction (fun x h => S h f x))
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal P * eLpNorm f (ENNReal.ofReal p) Measure.count := by
  classical
  have hpReal : 0 < p := lt_trans zero_lt_one hp
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpOne : 1 ≤ ENNReal.ofReal p := (ENNReal.one_le_ofReal).2 (le_of_lt hp)
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨hpOne⟩
  have hP : 0 ≤ P := by
    let δ : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
      lp.single (ENNReal.ofReal p) (0 : ℤ) (1 : ℂ)
    obtain ⟨G, _hGnonneg, _hGpoint, hGnorm⟩ := hSq δ
    have hδnorm : ‖δ‖ = 1 := by
      simpa [δ] using
        (lp.norm_single (p := ENNReal.ofReal p)
          (E := fun _ : ℤ => ℂ) (ENNReal.ofReal_pos.mpr hpReal)
          (0 : ℤ) (1 : ℂ))
    have hGleP : ‖G‖ ≤ P := by
      calc
        ‖G‖ ≤ P * ‖δ‖ := hGnorm
        _ = P := by rw [hδnorm, mul_one]
    exact (norm_nonneg G).trans hGleP
  let F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
    finiteSupportSequenceLpGeneral (p := ENNReal.ofReal p)
      hp0 hpTop hpOne hf.toFinset f
  have hFpoint : ∀ x, F x = f x := by
    intro x
    rw [finiteSupportSequenceLpGeneral_apply
      (p := ENNReal.ofReal p) hp0 hpTop hpOne hf.toFinset f x]
    by_cases hx : x ∈ hf.toFinset
    · simp [hx]
    · have hfx : f x = 0 := by
        by_contra hfx
        exact hx (hf.mem_toFinset.mpr (Function.mem_support.mpr hfx))
      simp [hx, hfx]
  have hFseq : (F : ℤ → ℂ) = f := funext hFpoint
  obtain ⟨G, hGnonneg, hGofReal, hGnorm⟩ := hSq F
  let aF : ℤ → ℤ → ℂ := fun x h => S h (F : ℤ → ℂ) x
  let af : ℤ → ℤ → ℂ := fun x h => S h f x
  have ha : aF = af := by
    funext x h
    dsimp [aF, af]
    rw [hFseq]
  have hGofRealF : ∀ x, ENNReal.ofReal (G x) =
      localInterpolationExtendedSquareFunction af x := by
    intro x
    rw [← ha]
    exact hGofReal x
  have hmeasExt : AEStronglyMeasurable
      (localInterpolationExtendedSquareFunction af) Measure.count :=
    (measurable_of_countable _).aestronglyMeasurable
  have hmeasG : AEStronglyMeasurable (fun x : ℤ => G x) Measure.count :=
    (measurable_of_countable _).aestronglyMeasurable
  have hExtEq :
      eLpNorm (localInterpolationExtendedSquareFunction af)
          (ENNReal.ofReal p) Measure.count =
        eLpNorm (fun x : ℤ => G x) (ENNReal.ofReal p) Measure.count := by
    apply eLpNorm_congr_enorm_ae hmeasExt hmeasG
    filter_upwards with x
    rw [enorm_eq_self, ← hGofRealF x,
      Real.enorm_of_nonneg (hGnonneg x)]
  have hGfun : (fun x : ℤ => G x) = fun x => ‖G x‖ := by
    funext x
    exact (Real.norm_of_nonneg (hGnonneg x)).symm
  have hExtNorm :
      eLpNorm (localInterpolationExtendedSquareFunction af)
          (ENNReal.ofReal p) Measure.count = ENNReal.ofReal ‖G‖ := by
    calc
      _ = eLpNorm (fun x : ℤ => G x) (ENNReal.ofReal p) Measure.count := hExtEq
      _ = eLpNorm (fun x : ℤ => ‖G x‖) (ENNReal.ofReal p) Measure.count := by
        rw [hGfun]
      _ = ENNReal.ofReal ‖G‖ := localInterpolation_eLpNorm_lp_norm hp G
  have hmeasF : AEStronglyMeasurable
      (fun x : ℤ => (F : ℤ → ℂ) x) Measure.count :=
    (measurable_of_countable _).aestronglyMeasurable
  have hInputNorm :
      eLpNorm f (ENNReal.ofReal p) Measure.count = ENNReal.ofReal ‖F‖ := by
    calc
      _ = eLpNorm (fun x : ℤ => (F : ℤ → ℂ) x)
          (ENNReal.ofReal p) Measure.count := by
        exact congrArg
          (fun g : ℤ → ℂ => eLpNorm g (ENNReal.ofReal p) Measure.count)
          hFseq.symm
      _ = eLpNorm (fun x : ℤ => ‖F x‖)
          (ENNReal.ofReal p) Measure.count :=
        (eLpNorm_norm (fun x : ℤ => F x) hmeasF).symm
      _ = ENNReal.ofReal ‖F‖ := localInterpolation_eLpNorm_lp_norm hp F
  calc
    _ = ENNReal.ofReal ‖G‖ := hExtNorm
    _ ≤ ENNReal.ofReal (P * ‖F‖) := ENNReal.ofReal_le_ofReal hGnorm
    _ = ENNReal.ofReal P * eLpNorm f (ENNReal.ofReal p) Measure.count := by
      calc
        _ = ENNReal.ofReal P * ENNReal.ofReal ‖F‖ := ENNReal.ofReal_mul hP
        _ = ENNReal.ofReal P * eLpNorm f (ENNReal.ofReal p) Measure.count := by
          rw [← hInputNorm]

/-- The pointwise norm of the actual vector convolution output is
subadditive on two inputs with finite square-function majorants. -/
private theorem localInterpolation_vectorOutputNorm_subadditive
    {ι : Type*} [Fintype ι] {p P : ℝ} (hp : 1 < p) (hP : 0 ≤ P)
    (N : ℕ) (K : ι × Fin N → IntegerL1Kernel) (index : ι → ℤ)
    (S : ℤ → (ℤ → ℂ) → ℤ → ℂ)
    (f g : ℤ → ℂ) (hf : f.HasFiniteSupport) (hg : g.HasFiniteSupport)
    (hSadd : ∀ h y, S h (f + g) y = S h f y + S h g y)
    (hSqF : eLpNorm (localInterpolationExtendedSquareFunction
        (fun x h => S h f x)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal P * eLpNorm f (ENNReal.ofReal p) Measure.count)
    (hSqG : eLpNorm (localInterpolationExtendedSquareFunction
        (fun x h => S h g x)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal P * eLpNorm g (ENNReal.ofReal p) Measure.count)
    (x : ℤ) :
    ‖integerKernelVectorConvolution K
        (fun y => WithLp.toLp 2
          (fun i : ι × Fin N => S (index i.1) (f + g) y)) x‖ ≤
      ‖integerKernelVectorConvolution K
          (fun y => WithLp.toLp 2
            (fun i : ι × Fin N => S (index i.1) f y)) x‖ +
        ‖integerKernelVectorConvolution K
          (fun y => WithLp.toLp 2
            (fun i : ι × Fin N => S (index i.1) g y)) x‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨(ENNReal.one_le_ofReal).2 (le_of_lt hp)⟩
  obtain ⟨Gf, hGfPoint, hGfSum, _hGfNorm⟩ :=
    localInterpolation_squareMajorant_of_sourceBound (P := P) hp hP
      (fun x h => S h f x) f hf hSqF
  obtain ⟨Gg, hGgPoint, hGgSum, _hGgNorm⟩ :=
    localInterpolation_squareMajorant_of_sourceBound (P := P) hp hP
      (fun x h => S h g x) g hg hSqG
  have hVadd := localInterpolation_vectorConvolution_add N K index S f g hSadd
    Gf Gg hGfSum (fun x => (hGfPoint x).ge)
    hGgSum (fun x => (hGgPoint x).ge) x
  rw [hVadd]
  exact norm_add_le _ _

/-- The pointwise norm of the actual vector convolution output is
nonnegative. -/
private theorem localInterpolation_vectorOutputNorm_nonneg
    {ι : Type*} [Fintype ι] (N : ℕ)
    (K : ι × Fin N → IntegerL1Kernel) (index : ι → ℤ)
    (S : ℤ → (ℤ → ℂ) → ℤ → ℂ) (f : ℤ → ℂ) (x : ℤ) :
    0 ≤ ‖integerKernelVectorConvolution K
      (fun y => WithLp.toLp 2
        (fun i : ι × Fin N => S (index i.1) f y)) x‖ :=
  norm_nonneg _

private theorem localInterpolation_lp_nonneg_rpow_sum_le_norm
    {p : ℝ} (hp : 0 < p)
    (g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p))
    (hg : ∀ x, 0 ≤ g x) (s : Finset ℤ) :
    ∑ x ∈ s, g x ^ p ≤ ‖g‖ ^ p := by
  have hpENN : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hp.le]
    exact hp
  have hsumENN : Summable (fun x : ℤ => ‖g x‖ ^ (ENNReal.ofReal p).toReal) :=
    (lp.memℓp g).summable hpENN
  have hsum : Summable (fun x : ℤ => g x ^ p) := by
    apply hsumENN.congr
    intro x
    rw [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (hg x)]
  have htsum : (∑' x : ℤ, ‖g x‖ ^ p) = ∑' x : ℤ, g x ^ p := by
    apply tsum_congr
    intro x
    rw [Real.norm_of_nonneg (hg x)]
  have hnorm : ‖g‖ ^ p = ∑' x : ℤ, g x ^ p := by
    calc
      ‖g‖ ^ p = ((∑' x : ℤ, ‖g x‖ ^ p) ^ (1 / p)) ^ p := by
        simpa only [ENNReal.toReal_ofReal hp.le] using
          congrArg (fun z : ℝ => z ^ p) (lp.norm_eq_tsum_rpow hpENN g)
      _ = ∑' x : ℤ, ‖g x‖ ^ p := by
        have hsumNonneg : 0 ≤ ∑' x : ℤ, ‖g x‖ ^ p :=
          tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg (g x)) _
        rw [← Real.rpow_mul hsumNonneg (1 / p) p]
        have hexp : (1 / p) * p = 1 := by
          field_simp [ne_of_gt hp]
        rw [hexp, Real.rpow_one]
      _ = ∑' x : ℤ, g x ^ p := htsum
  calc
    ∑ x ∈ s, g x ^ p ≤ ∑' x : ℤ, g x ^ p :=
      hsum.sum_le_tsum s (fun x _ => Real.rpow_nonneg (hg x) _)
    _ = ‖g‖ ^ p := hnorm.symm

/-- The lower endpoint exponent in the localized interpolation lemma. -/
def localInterpolationR (q : ℝ) : ℝ := 2 * q / (q + 1)

/-- The conjugate exponent appearing in the localized interpolation lemma. -/
def localInterpolationQPrime (q : ℝ) : ℝ := q / (q - 1)

/-- The upper endpoint exponent in the localized interpolation lemma. -/
def localInterpolationRPrime (q : ℝ) : ℝ := 2 * q / (q - 1)

/-- The constant from the two strong-interpolation applications in
`lm:localInterpolation`. -/
def localInterpolationC (q : ℝ) : ℝ :=
  max
    (2 * (q / (q - localInterpolationR q) + q / (2 - q)) ^ (1 / q))
    (2 * (localInterpolationQPrime q /
      (localInterpolationQPrime q - 2) +
      localInterpolationQPrime q /
        (localInterpolationRPrime q - localInterpolationQPrime q)) ^
          (1 / localInterpolationQPrime q))

/-- Normalize the common vector-endpoint coefficient to the exact
multiplicity and kernel-mass power appearing in `lm:localInterpolation`.
The identity remains valid when `E₀ * B = 0`. -/
private theorem localInterpolation_endpointCoefficient_rpow
    {q E₀ B Pstar : ℝ} (_hq1 : 1 < q) (_hq2 : q < 2)
    (N : ℕ) (hN : 1 ≤ N) (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hPstar : 1 ≤ Pstar) :
    (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar) ^ (2 - q) =
      Pstar ^ (2 - q) *
        ((N : ℝ) * E₀ * B) ^ ((2 - q) / 2) := by
  have hE₀B : 0 ≤ E₀ * B := mul_nonneg hE₀ hB
  have hNcast : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNnonneg : 0 ≤ (N : ℝ) := le_trans (by norm_num) hNcast
  have hPstarNonneg : 0 ≤ Pstar := le_trans (by norm_num) hPstar
  have hbase : (E₀ * B) * (N : ℝ) = (N : ℝ) * E₀ * B := by ring
  calc
    _ = (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ)) ^ (2 - q) *
        Pstar ^ (2 - q) :=
      Real.mul_rpow
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hPstarNonneg
    _ = Pstar ^ (2 - q) *
        (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ)) ^ (2 - q) := by rw [mul_comm]
    _ = Pstar ^ (2 - q) *
        Real.sqrt ((E₀ * B) * (N : ℝ)) ^ (2 - q) := by
      rw [← Real.sqrt_mul hE₀B (N : ℝ)]
    _ = Pstar ^ (2 - q) *
        ((N : ℝ) * E₀ * B) ^ ((2 - q) / 2) := by
      rw [← Real.rpow_div_two_eq_sqrt (x := (E₀ * B) * (N : ℝ))
        (2 - q) (mul_nonneg hE₀B hNnonneg), hbase]

/-- Repeating every coordinate of a finite `ℓ²` vector exactly `N` times
multiplies its squared norm by `N`. This is the fiberwise multiplicity
identity used when the kernel family is indexed by `K × Fin N`. -/
theorem localInterpolation_repeatedPiLp_norm_sq
    {ι : Type*} [Fintype ι] (N : ℕ)
    (v : PiLp 2 (fun _ : ι => ℂ)) :
    ‖WithLp.toLp 2 (fun i : ι × Fin N => v i.1)‖ ^ 2 =
      (N : ℝ) * ‖v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]

/-- A finite square-function bound transfers to the repeated vector used by
the lower and upper convolution endpoints, with the exact multiplicity
factor `N` after squaring. -/
theorem localInterpolation_repeatedPiLp_norm_sq_le
    {ι : Type*} [Fintype ι] (N : ℕ)
    (v : PiLp 2 (fun _ : ι => ℂ)) (G : ℝ)
    (hG : ∑ i : ι, ‖v i‖ ^ 2 ≤ G ^ 2) :
    ‖WithLp.toLp 2 (fun i : ι × Fin N => v i.1)‖ ^ 2 ≤
      (N : ℝ) * G ^ 2 := by
  have hv : ‖v‖ ^ 2 ≤ G ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact hG
  rw [localInterpolation_repeatedPiLp_norm_sq]
  exact mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg N)

/-- Every finite restriction of an `ℓ²` square function is bounded by the
full square function. This is the finite-index-to-countable-index bridge in
the two square-function endpoint estimates. -/
theorem localInterpolation_finiteSquare_le_full
    (s : Finset ℤ) (a : ℤ → ℂ)
    (ha : Summable (fun h : ℤ => ‖a h‖ ^ 2)) :
    Real.sqrt (∑ h ∈ s, ‖a h‖ ^ 2) ≤
      Real.sqrt (∑' h : ℤ, ‖a h‖ ^ 2) := by
  apply Real.sqrt_le_sqrt
  exact ha.sum_le_tsum s (fun h _ => sq_nonneg (‖a h‖))

/-- The finite square function over a translated finite set of projection
indices is bounded by the unshifted full square function. The translation is
reindexed by `Equiv.addRight`, matching the `(k+j)` index in
`lm:localInterpolation`. -/
theorem localInterpolation_finiteShiftSquare_le_full
    (s : Finset ℤ) (shift : ℤ) (a : ℤ → ℂ)
    (ha : Summable (fun h : ℤ => ‖a h‖ ^ 2)) :
    Real.sqrt (∑ k ∈ s, ‖a (k + shift)‖ ^ 2) ≤
      Real.sqrt (∑' h : ℤ, ‖a h‖ ^ 2) := by
  have hshift : Summable (fun k : ℤ => ‖a (k + shift)‖ ^ 2) := by
    have h := (Equiv.addRight shift).summable_iff.mpr ha
    exact h.congr fun k => by
      change ‖a ((Equiv.addRight shift) k)‖ ^ 2 = ‖a (k + shift)‖ ^ 2
      rfl
  calc
    Real.sqrt (∑ k ∈ s, ‖a (k + shift)‖ ^ 2) ≤
        Real.sqrt (∑' k : ℤ, ‖a (k + shift)‖ ^ 2) :=
      localInterpolation_finiteSquare_le_full s (fun k => a (k + shift)) hshift
    _ = Real.sqrt (∑' h : ℤ, ‖a h‖ ^ 2) := by
      congr 1
      exact (Equiv.addRight shift).tsum_eq (fun h => ‖a h‖ ^ 2)

/-- Restricting a full square function to a finite set of shifted indices
preserves its pointwise majorant. This is the finite-`K` input estimate used
when applying the vector endpoints to `S_{k+j} f`. -/
theorem localInterpolation_subfamilySquarePointwise
    (K : Finset ℤ) (shift : ℤ) (a : ℤ → ℤ → ℂ) (G : ℤ → ℝ)
    (hsummable : ∀ x, Summable (fun h : ℤ => ‖a x h‖ ^ 2))
    (hfull : ∀ x, Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2) ≤ G x) :
    ∀ x, Real.sqrt
        (∑ i : {k : ℤ // k ∈ K}, ‖a x (i.1 + shift)‖ ^ 2) ≤ G x := by
  intro x
  have hfinite :=
    localInterpolation_finiteShiftSquare_le_full K shift (a x) (hsummable x)
  have hsum :
      (∑ i : {k : ℤ // k ∈ K}, ‖a x (i.1 + shift)‖ ^ 2) =
        ∑ k ∈ K, ‖a x (k + shift)‖ ^ 2 :=
    Finset.sum_coe_sort K (fun k : ℤ => ‖a x (k + shift)‖ ^ 2)
  calc
    Real.sqrt (∑ i : {k : ℤ // k ∈ K}, ‖a x (i.1 + shift)‖ ^ 2) =
        Real.sqrt (∑ k ∈ K, ‖a x (k + shift)‖ ^ 2) := by rw [hsum]
    _ ≤ Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2) := hfinite
    _ ≤ G x := hfull x

/-- Fiberwise, restricting the square function to finitely many coordinates
and then repeating each retained coordinate `N` times has `ℓ²` norm at most
`sqrt N` times the full square function. -/
theorem localInterpolation_repeatedPiLp_norm_le
    {ι : Type*} [Fintype ι] (N : ℕ) (a : ι → ℂ) (G : ℝ)
    (hG : 0 ≤ G)
    (hA : Real.sqrt (∑ i : ι, ‖a i‖ ^ 2) ≤ G) :
    ‖WithLp.toLp 2 (fun i : ι × Fin N => a i.1)‖ ≤
      Real.sqrt (N : ℝ) * G := by
  have hsumNonneg : 0 ≤ ∑ i : ι, ‖a i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (‖a i‖)
  have hsum : ∑ i : ι, ‖a i‖ ^ 2 ≤ G ^ 2 := by
    have hs := Real.sq_sqrt hsumNonneg
    have hmul := mul_le_mul hA hA (Real.sqrt_nonneg _) hG
    nlinarith [hmul]
  have hv : ‖WithLp.toLp 2 a‖ ^ 2 ≤ G ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact hsum
  have hrepeat := localInterpolation_repeatedPiLp_norm_sq N
    (WithLp.toLp 2 a)
  have hN : (Real.sqrt (N : ℝ) * G) ^ 2 = (N : ℝ) * G ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hmul : (N : ℝ) * ‖WithLp.toLp 2 a‖ ^ 2 ≤
      (N : ℝ) * G ^ 2 :=
    mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg N)
  have hright : 0 ≤ Real.sqrt (N : ℝ) * G :=
    mul_nonneg (Real.sqrt_nonneg _) hG
  have hleft : 0 ≤ ‖WithLp.toLp 2 (fun i : ι × Fin N => a i.1)‖ :=
    norm_nonneg _
  nlinarith [hrepeat, hmul, hN, hleft, hright]

/-- A full square-function majorant in scalar sequence `ℓᵖ` produces the
exact repeated finite-family input required by the vector endpoint theorem.
The factor `sqrt N` records that each selected coordinate is repeated `N`
times. -/
theorem localInterpolation_repeatedInputLp_bound
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 < p) (N : ℕ)
    (G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p))
    (a : ℤ → ι → ℂ)
    (hpoint : ∀ x, Real.sqrt (∑ i : ι, ‖a x i‖ ^ 2) ≤ G x) :
    ∃ F : lp (fun _ : ℤ => PiLp 2 (fun _ : ι × Fin N => ℂ))
        (ENNReal.ofReal p),
      (∀ x, F x = WithLp.toLp 2 (fun i : ι × Fin N => a x i.1)) ∧
        ‖F‖ ≤ Real.sqrt (N : ℝ) * ‖G‖ := by
  have hpReal : 0 < p := lt_trans zero_lt_one hp
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨(ENNReal.one_le_ofReal).2 (le_of_lt hp)⟩
  have hpENN : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hpReal.le]
    exact hpReal
  have hpToReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hpReal.le
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hGnonneg (x : ℤ) : 0 ≤ G x :=
    (Real.sqrt_nonneg _).trans (hpoint x)
  let input : ℤ → PiLp 2 (fun _ : ι × Fin N => ℂ) := fun x =>
    WithLp.toLp 2 (fun i : ι × Fin N => a x i.1)
  let C : ℝ := Real.sqrt (N : ℝ)
  let R : ℝ := C * ‖G‖
  have hC : 0 ≤ C := by dsimp [C]; exact Real.sqrt_nonneg _
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg hC (norm_nonneg G)
  have hfinite (s : Finset ℤ) :
      ∑ x ∈ s, ‖input x‖ ^ (ENNReal.ofReal p).toReal ≤
        R ^ (ENNReal.ofReal p).toReal := by
    rw [hpToReal]
    calc
      ∑ x ∈ s, ‖input x‖ ^ p ≤
          ∑ x ∈ s, (C * G x) ^ p := by
        apply Finset.sum_le_sum
        intro x hx
        exact Real.rpow_le_rpow (norm_nonneg (input x))
          (localInterpolation_repeatedPiLp_norm_le N (a x) (G x)
            (hGnonneg x) (hpoint x)) hpReal.le
      _ = C ^ p * ∑ x ∈ s, G x ^ p := by
        calc
          _ = ∑ x ∈ s, C ^ p * G x ^ p := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Real.mul_rpow hC (hGnonneg x)]
          _ = C ^ p * ∑ x ∈ s, G x ^ p := by rw [← Finset.mul_sum]
      _ ≤ C ^ p * ‖G‖ ^ p := by
        exact mul_le_mul_of_nonneg_left
          (localInterpolation_lp_nonneg_rpow_sum_le_norm hpReal G hGnonneg s)
          (Real.rpow_nonneg hC _)
      _ = R ^ p := by
        dsimp [R]
        exact (Real.mul_rpow hC (norm_nonneg G)).symm
  let out : lp (fun _ : ℤ => PiLp 2 (fun _ : ι × Fin N => ℂ))
      (ENNReal.ofReal p) :=
    lpOfUniformFiniteMomentBound hp0 hpTop input (Real.rpow_nonneg hR _)
      hfinite
  have houtNorm : ‖out‖ ≤ R := by
    apply lp.norm_le_of_forall_sum_le hpENN hR
    intro s
    simpa only [out, lpOfUniformFiniteMomentBound_apply, hpToReal] using hfinite s
  refine ⟨out, ?_, ?_⟩
  · intro x
    rfl
  · simpa [R, C] using houtNorm

/-- The lower vector endpoint for a repeated finite family, with its input
assembled from a scalar square-function majorant. This is the lower-endpoint
application in `lm:localInterpolation`; the family kernels retain the exact
mass and positive-maximal hypotheses of `lm:vectorLower`. -/
theorem localInterpolation_vectorLowerEndpoint
    {ι : Type*} [Fintype ι] {q : ℝ} (hq : 1 < q) (N : ℕ)
    (K : ι × Fin N → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal (localInterpolationR q)))
    (a : ℤ → ι → ℂ)
    (hpoint : ∀ x,
      Real.sqrt (∑ i : ι, ‖a x i‖ ^ 2) ≤ G x) :
    ∃ out : lp (fun _ : ℤ => PiLp 2 (fun _ : ι × Fin N => ℂ))
        (ENNReal.ofReal (localInterpolationR q)),
      (∀ x, out x = integerKernelVectorConvolution K
        (fun y => WithLp.toLp 2 (fun i : ι × Fin N => a y i.1)) x) ∧
        ‖out‖ ≤ Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖G‖ := by
  have hrOne : 1 < localInterpolationR q := by
    have hqpos : 0 < q := lt_trans zero_lt_one hq
    have hden : 0 < q + 1 := by linarith
    dsimp [localInterpolationR]
    rw [lt_div_iff₀ hden]
    nlinarith
  obtain ⟨F, hF, hFnorm⟩ :=
    localInterpolation_repeatedInputLp_bound hrOne N G a hpoint
  obtain ⟨out, hOut, hOutNorm⟩ :=
    vectorLower_normBound hq rfl K E₀ B hE₀ hB hmass hmax F
  have hFseq : (F : ℤ → PiLp 2 (fun _ : ι × Fin N => ℂ)) =
      fun x => WithLp.toLp 2 (fun i : ι × Fin N => a x i.1) := by
    funext x
    exact hF x
  refine ⟨out, ?_, ?_⟩
  · intro x
    rw [hOut x, hFseq]
  · calc
      ‖out‖ ≤ Real.sqrt (E₀ * B) * ‖F‖ := hOutNorm
      _ ≤ Real.sqrt (E₀ * B) *
          (Real.sqrt (N : ℝ) * ‖G‖) :=
        mul_le_mul_of_nonneg_left hFnorm (Real.sqrt_nonneg _)
      _ = Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖G‖ := by ring

/-- The upper vector endpoint for the same repeated finite family, again
assembled from the scalar square-function majorant. This is the
`lm:vectorUpper` application in `lm:localInterpolation`. -/
theorem localInterpolation_vectorUpperEndpoint
    {ι : Type*} [Fintype ι] {q : ℝ} (hq : 1 < q) (N : ℕ)
    (K : ι × Fin N → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal (localInterpolationRPrime q)))
    (a : ℤ → ι → ℂ)
    (hpoint : ∀ x,
      Real.sqrt (∑ i : ι, ‖a x i‖ ^ 2) ≤ G x) :
    ∃ out : lp (fun _ : ℤ => PiLp 2 (fun _ : ι × Fin N => ℂ))
        (ENNReal.ofReal (localInterpolationRPrime q)),
      (∀ x, out x = integerKernelVectorConvolution K
        (fun y => WithLp.toLp 2 (fun i : ι × Fin N => a y i.1)) x) ∧
        ‖out‖ ≤ Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖G‖ := by
  have hqminus : 0 < q - 1 := sub_pos.mpr hq
  have hr'One : 1 < localInterpolationRPrime q := by
    dsimp [localInterpolationRPrime]
    rw [lt_div_iff₀ hqminus]
    nlinarith
  obtain ⟨F, hF, hFnorm⟩ :=
    localInterpolation_repeatedInputLp_bound hr'One N G a hpoint
  obtain ⟨out, hOut, hOutNorm⟩ :=
    vectorUpper_normBound hq K E₀ B hE₀ hB hmass hmax F
  have hFseq : (F : ℤ → PiLp 2 (fun _ : ι × Fin N => ℂ)) =
      fun x => WithLp.toLp 2 (fun i : ι × Fin N => a x i.1) := by
    funext x
    exact hF x
  refine ⟨out, ?_, ?_⟩
  · intro x
    rw [hOut x, hFseq]
  · calc
      ‖out‖ ≤ Real.sqrt (E₀ * B) * ‖F‖ := hOutNorm
      _ ≤ Real.sqrt (E₀ * B) *
          (Real.sqrt (N : ℝ) * ‖G‖) :=
        mul_le_mul_of_nonneg_left hFnorm (Real.sqrt_nonneg _)
      _ = Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖G‖ := by ring

/-- The lower vector endpoint, expressed as the scalar `eLpNorm` of the
pointwise Euclidean norm used by the interpolation lemma. This is the exact
bridge from the mixed sequence-`lp` endpoint to the scalar function `T`. -/
theorem localInterpolation_vectorLowerEndpoint_eLpNorm
    {ι : Type*} [Fintype ι] {q : ℝ} (hq : 1 < q) (N : ℕ)
    (K : ι × Fin N → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal (localInterpolationR q)))
    (a : ℤ → ι → ℂ)
    (hpoint : ∀ x,
      Real.sqrt (∑ i : ι, ‖a x i‖ ^ 2) ≤ G x) :
    eLpNorm
        (fun x => ‖integerKernelVectorConvolution K
          (fun y => WithLp.toLp 2 (fun i : ι × Fin N => a y i.1)) x‖)
        (ENNReal.ofReal (localInterpolationR q)) Measure.count ≤
      ENNReal.ofReal
        (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖G‖) := by
  have hrOne : 1 < localInterpolationR q := by
    have hqpos : 0 < q := lt_trans zero_lt_one hq
    have hden : 0 < q + 1 := by linarith
    dsimp [localInterpolationR]
    rw [lt_div_iff₀ hden]
    nlinarith
  obtain ⟨out, hout, houtNorm⟩ :=
    localInterpolation_vectorLowerEndpoint hq N K E₀ B hE₀ hB hmass hmax G a hpoint
  have hnorm :
      eLpNorm (fun x => ‖out x‖) (ENNReal.ofReal (localInterpolationR q))
        Measure.count = ENNReal.ofReal ‖out‖ :=
    localInterpolation_eLpNorm_lp_norm hrOne out
  have hpointEq :
      (fun x => ‖integerKernelVectorConvolution K
        (fun y => WithLp.toLp 2 (fun i : ι × Fin N => a y i.1)) x‖) =
      fun x => ‖out x‖ := by
    funext x
    rw [(hout x).symm]
  rw [hpointEq, hnorm]
  exact ENNReal.ofReal_le_ofReal houtNorm

/-- The upper vector endpoint, expressed as the scalar `eLpNorm` of the
pointwise Euclidean norm used by the interpolation lemma. -/
theorem localInterpolation_vectorUpperEndpoint_eLpNorm
    {ι : Type*} [Fintype ι] {q : ℝ} (hq : 1 < q) (N : ℕ)
    (K : ι × Fin N → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal (localInterpolationRPrime q)))
    (a : ℤ → ι → ℂ)
    (hpoint : ∀ x,
      Real.sqrt (∑ i : ι, ‖a x i‖ ^ 2) ≤ G x) :
    eLpNorm
        (fun x => ‖integerKernelVectorConvolution K
          (fun y => WithLp.toLp 2 (fun i : ι × Fin N => a y i.1)) x‖)
        (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count ≤
      ENNReal.ofReal
        (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖G‖) := by
  have hr'One : 1 < localInterpolationRPrime q := by
    have hqminus : 0 < q - 1 := sub_pos.mpr hq
    dsimp [localInterpolationRPrime]
    rw [lt_div_iff₀ hqminus]
    nlinarith
  obtain ⟨out, hout, houtNorm⟩ :=
    localInterpolation_vectorUpperEndpoint hq N K E₀ B hE₀ hB hmass hmax G a hpoint
  have hnorm :
      eLpNorm (fun x => ‖out x‖) (ENNReal.ofReal (localInterpolationRPrime q))
        Measure.count = ENNReal.ofReal ‖out‖ :=
    localInterpolation_eLpNorm_lp_norm hr'One out
  have hpointEq :
      (fun x => ‖integerKernelVectorConvolution K
        (fun y => WithLp.toLp 2 (fun i : ι × Fin N => a y i.1)) x‖) =
      fun x => ‖out x‖ := by
    funext x
    rw [(hout x).symm]
  rw [hpointEq, hnorm]
  exact ENNReal.ofReal_le_ofReal houtNorm

/-- Finite-family lower endpoint obtained directly from a full square-function
majorant, with the exact shifted indices `k+j` from the source. -/
theorem localInterpolation_vectorLowerEndpoint_ofFullSquareMajorant
    {q : ℝ} (hq : 1 < q) (N : ℕ) (K : Finset ℤ) (j : ℤ)
    (kernels : {k : ℤ // k ∈ K} × Fin N → IntegerL1Kernel)
    (E₀ B : ℝ) (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (kernels i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax kernels h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal (localInterpolationR q)))
    (a : ℤ → ℤ → ℂ)
    (hsummable : ∀ x, Summable (fun h : ℤ => ‖a x h‖ ^ 2))
    (hfull : ∀ x, Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2) ≤ G x) :
    eLpNorm
        (fun x => ‖integerKernelVectorConvolution kernels
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ K} × Fin N => a y (i.1.1 + j))) x‖)
        (ENNReal.ofReal (localInterpolationR q)) Measure.count ≤
      ENNReal.ofReal
        (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖G‖) := by
  let squareInput : ℤ → {k : ℤ // k ∈ K} → ℂ :=
    fun x k => a x (k.1 + j)
  have hpoint : ∀ x,
      Real.sqrt (∑ k : {k : ℤ // k ∈ K}, ‖squareInput x k‖ ^ 2) ≤ G x := by
    intro x
    change Real.sqrt
        (∑ k : {k : ℤ // k ∈ K}, ‖a x (k.1 + j)‖ ^ 2) ≤ G x
    exact localInterpolation_subfamilySquarePointwise K j a G hsummable hfull x
  simpa [squareInput] using
    localInterpolation_vectorLowerEndpoint_eLpNorm hq N kernels E₀ B hE₀ hB
      hmass hmax G squareInput hpoint

/-- Finite-family upper endpoint obtained directly from a full square-function
majorant, with the same source shift convention as the lower endpoint. -/
theorem localInterpolation_vectorUpperEndpoint_ofFullSquareMajorant
    {q : ℝ} (hq : 1 < q) (N : ℕ) (K : Finset ℤ) (j : ℤ)
    (kernels : {k : ℤ // k ∈ K} × Fin N → IntegerL1Kernel)
    (E₀ B : ℝ) (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (kernels i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax kernels h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (G : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal (localInterpolationRPrime q)))
    (a : ℤ → ℤ → ℂ)
    (hsummable : ∀ x, Summable (fun h : ℤ => ‖a x h‖ ^ 2))
    (hfull : ∀ x, Real.sqrt (∑' h : ℤ, ‖a x h‖ ^ 2) ≤ G x) :
    eLpNorm
        (fun x => ‖integerKernelVectorConvolution kernels
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ K} × Fin N => a y (i.1.1 + j))) x‖)
        (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count ≤
      ENNReal.ofReal
        (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖G‖) := by
  let squareInput : ℤ → {k : ℤ // k ∈ K} → ℂ :=
    fun x k => a x (k.1 + j)
  have hpoint : ∀ x,
      Real.sqrt (∑ k : {k : ℤ // k ∈ K}, ‖squareInput x k‖ ^ 2) ≤ G x := by
    intro x
    change Real.sqrt
        (∑ k : {k : ℤ // k ∈ K}, ‖a x (k.1 + j)‖ ^ 2) ≤ G x
    exact localInterpolation_subfamilySquarePointwise K j a G hsummable hfull x
  simpa [squareInput] using
    localInterpolation_vectorUpperEndpoint_eLpNorm hq N kernels E₀ B hE₀ hB
      hmass hmax G squareInput hpoint

/-- The two scalar endpoint estimates assembled from the source square-function
bounds. Both use the exact common constant `sqrt(E₀ B) sqrt(N) P_*`; the
strict interpolation step is applied separately afterward. -/
private theorem localInterpolation_scalarEndpointBounds
    {q P_r P_r' E₀ B : ℝ} (hq : 1 < q) (N : ℕ) (K : Finset ℤ) (j : ℤ)
    (kernels : {k : ℤ // k ∈ K} × Fin N → IntegerL1Kernel)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (kernels i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax kernels h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (S : ℤ → (ℤ → ℂ) → ℤ → ℂ) (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (hSqR : eLpNorm
        (localInterpolationExtendedSquareFunction (fun x h => S h f x))
        (ENNReal.ofReal (localInterpolationR q)) Measure.count ≤
      ENNReal.ofReal P_r *
        eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count)
    (hSqR' : eLpNorm
        (localInterpolationExtendedSquareFunction (fun x h => S h f x))
        (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count ≤
      ENNReal.ofReal P_r' *
        eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count) :
    eLpNorm
        (fun x => ‖integerKernelVectorConvolution kernels
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ K} × Fin N => S (i.1.1 + j) f y)) x‖)
        (ENNReal.ofReal (localInterpolationR q)) Measure.count ≤
      ENNReal.ofReal
          (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) *
            max 1 (max P_r P_r')) *
        eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count ∧
    eLpNorm
        (fun x => ‖integerKernelVectorConvolution kernels
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ K} × Fin N => S (i.1.1 + j) f y)) x‖)
        (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count ≤
      ENNReal.ofReal
          (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) *
            max 1 (max P_r P_r')) *
        eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hqminus : 0 < q - 1 := sub_pos.mpr hq
  have hqplus : 0 < q + 1 := by linarith
  have hrOne : 1 < localInterpolationR q := by
    dsimp [localInterpolationR]
    rw [lt_div_iff₀ hqplus]
    nlinarith
  have hr'One : 1 < localInterpolationRPrime q := by
    dsimp [localInterpolationRPrime]
    rw [lt_div_iff₀ hqminus]
    nlinarith
  let Pstar : ℝ := max 1 (max P_r P_r')
  have hPstar : 0 ≤ Pstar := by
    dsimp [Pstar]
    exact le_trans (by norm_num) (le_max_left _ _)
  have hPrLe : P_r ≤ Pstar := by
    dsimp [Pstar]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hPr'Le : P_r' ≤ Pstar := by
    dsimp [Pstar]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  let a : ℤ → ℤ → ℂ := fun x h => S h f x
  have hSqRstar : eLpNorm (localInterpolationExtendedSquareFunction a)
      (ENNReal.ofReal (localInterpolationR q)) Measure.count ≤
        ENNReal.ofReal Pstar *
          eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count := by
    calc
      _ ≤ ENNReal.ofReal P_r *
          eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count := by
            simpa [a] using hSqR
      _ ≤ ENNReal.ofReal Pstar *
          eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hPrLe) _
  have hSqR'star : eLpNorm (localInterpolationExtendedSquareFunction a)
      (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count ≤
        ENNReal.ofReal Pstar *
          eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count := by
    calc
      _ ≤ ENNReal.ofReal P_r' *
          eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count := by
            simpa [a] using hSqR'
      _ ≤ ENNReal.ofReal Pstar *
          eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hPr'Le) _
  have hinputR := localInterpolation_finiteSupport_eLpNorm_lt_top hrOne f hf
  have hinputR' := localInterpolation_finiteSupport_eLpNorm_lt_top hr'One f hf
  obtain ⟨Gr, hGrPoint, hGrSum, hGrNorm⟩ :=
    localInterpolation_squareMajorant_of_sourceBound (P := Pstar) hrOne hPstar a f hf hSqRstar
  obtain ⟨Gr', hGr'Point, hGr'Sum, hGr'Norm⟩ :=
    localInterpolation_squareMajorant_of_sourceBound (P := Pstar) hr'One hPstar a f hf hSqR'star
  have hc : 0 ≤ Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hLower := localInterpolation_vectorLowerEndpoint_ofFullSquareMajorant
    hq N K j kernels E₀ B hE₀ hB hmass hmax Gr a hGrSum
    (fun x => (hGrPoint x).ge)
  have hUpper := localInterpolation_vectorUpperEndpoint_ofFullSquareMajorant
    hq N K j kernels E₀ B hE₀ hB hmass hmax Gr' a hGr'Sum
    (fun x => (hGr'Point x).ge)
  constructor
  · calc
      _ ≤ ENNReal.ofReal
          (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖Gr‖) := hLower
      _ ≤ ENNReal.ofReal
          ((Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar) *
            (eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count).toReal) :=
        ENNReal.ofReal_le_ofReal (by
          calc
            _ ≤ (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ)) *
                (Pstar *
                  (eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count).toReal) :=
              mul_le_mul_of_nonneg_left hGrNorm hc
            _ = _ := by ring)
      _ = ENNReal.ofReal
            (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar) *
          eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count := by
        calc
          _ = ENNReal.ofReal
                (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar) *
              ENNReal.ofReal
                (eLpNorm f (ENNReal.ofReal (localInterpolationR q))
                  Measure.count).toReal :=
            ENNReal.ofReal_mul (mul_nonneg hc hPstar)
          _ = ENNReal.ofReal
                (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar) *
              eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count := by
            rw [ENNReal.ofReal_toReal hinputR.ne]
  · calc
      _ ≤ ENNReal.ofReal
          (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * ‖Gr'‖) := hUpper
      _ ≤ ENNReal.ofReal
          ((Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar) *
            (eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count).toReal) :=
        ENNReal.ofReal_le_ofReal (by
          calc
            _ ≤ (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ)) *
                (Pstar *
                  (eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count).toReal) :=
              mul_le_mul_of_nonneg_left hGr'Norm hc
            _ = _ := by ring)
      _ = ENNReal.ofReal
            (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar) *
          eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count := by
        calc
          _ = ENNReal.ofReal
                (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar) *
              ENNReal.ofReal
                (eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q))
                  Measure.count).toReal :=
            ENNReal.ofReal_mul (mul_nonneg hc hPstar)
          _ = ENNReal.ofReal
                (Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar) *
              eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count := by
            rw [ENNReal.ofReal_toReal hinputR'.ne]

private theorem localInterpolation_lp_cast_apply
    {E : Type*} [NormedAddCommGroup E] {p p' : ℝ≥0∞}
    (hpp' : p = p') (f : lp (fun _ : ℤ => E) p) (x : ℤ) :
    (hpp' ▸ f) x = f x := by
  cases hpp'
  rfl

private theorem localInterpolation_lp_norm_cast
    {E : Type*} [NormedAddCommGroup E] {p p' : ℝ≥0∞}
    (hpp' : p = p') (f : lp (fun _ : ℤ => E) p) :
    ‖hpp' ▸ f‖ = ‖f‖ := by
  cases hpp'
  rfl

/-- At `q=2`, the local square-function interpolation is bypassed: the
assumed direct `ℓ²(ℤ;ℓ²)` operator bound gives the endpoint estimate itself. -/
theorem localInterpolation_qTwo_directEndpoint
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (A : ℝ) (hA : 0 ≤ A)
    (U : lp (fun _ : ℤ => E) (2 : ℝ≥0∞))
    (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞))
    (hL2 : ‖U‖ ≤ A * ‖f‖) :
    eLpNorm (fun x : ℤ => ‖U x‖) (2 : ℝ≥0∞) Measure.count ≤
      ENNReal.ofReal A * eLpNorm (fun x : ℤ => f x)
        (2 : ℝ≥0∞) Measure.count := by
  have hP₂ : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hUcast := localInterpolation_eLpNorm_lp_norm (p := (2 : ℝ))
    (by norm_num) (hP₂.symm ▸ U)
  have hUcastApply :
      (fun x : ℤ => ‖(hP₂.symm ▸ U) x‖) = fun x => ‖U x‖ := by
    funext x
    exact congrArg norm (localInterpolation_lp_cast_apply hP₂.symm U x)
  have hUcastNorm := localInterpolation_lp_norm_cast hP₂.symm U
  have hUatOfReal :
      eLpNorm (fun x : ℤ => ‖U x‖) (ENNReal.ofReal (2 : ℝ)) Measure.count =
        ENNReal.ofReal ‖U‖ := by
    calc
      _ = eLpNorm (fun x : ℤ => ‖(hP₂.symm ▸ U) x‖)
          (ENNReal.ofReal (2 : ℝ)) Measure.count := by
        exact congrArg
          (fun g : ℤ → ℝ => eLpNorm g (ENNReal.ofReal (2 : ℝ)) Measure.count)
          hUcastApply.symm
      _ = ENNReal.ofReal ‖hP₂.symm ▸ U‖ := hUcast
      _ = ENNReal.ofReal ‖U‖ := by rw [hUcastNorm]
  have hU : eLpNorm (fun x : ℤ => ‖U x‖) (2 : ℝ≥0∞) Measure.count =
      ENNReal.ofReal ‖U‖ := by
    calc
      _ = eLpNorm (fun x : ℤ => ‖U x‖)
          (ENNReal.ofReal (2 : ℝ)) Measure.count := by
        exact (congrArg
          (fun p : ℝ≥0∞ => eLpNorm (fun x : ℤ => ‖U x‖) p Measure.count)
          hP₂).symm
      _ = ENNReal.ofReal ‖U‖ := hUatOfReal
  have hmeasF : AEStronglyMeasurable (fun x : ℤ => f x) Measure.count :=
    (measurable_of_countable (fun x : ℤ => f x)).aestronglyMeasurable
  have hFcast := localInterpolation_eLpNorm_lp_norm (p := (2 : ℝ))
    (by norm_num) (hP₂.symm ▸ f)
  have hFcastApply :
      (fun x : ℤ => ‖(hP₂.symm ▸ f) x‖) = fun x => ‖f x‖ := by
    funext x
    exact congrArg norm (localInterpolation_lp_cast_apply hP₂.symm f x)
  have hFcastNorm := localInterpolation_lp_norm_cast hP₂.symm f
  have hFatOfReal :
      eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal (2 : ℝ)) Measure.count =
        ENNReal.ofReal ‖f‖ := by
    calc
      _ = eLpNorm (fun x : ℤ => ‖f x‖)
          (ENNReal.ofReal (2 : ℝ)) Measure.count :=
        (eLpNorm_norm (fun x : ℤ => f x) hmeasF).symm
      _ = eLpNorm (fun x : ℤ => ‖(hP₂.symm ▸ f) x‖)
          (ENNReal.ofReal (2 : ℝ)) Measure.count := by
        exact congrArg
          (fun g : ℤ → ℝ => eLpNorm g (ENNReal.ofReal (2 : ℝ)) Measure.count)
          hFcastApply.symm
      _ = ENNReal.ofReal ‖hP₂.symm ▸ f‖ := hFcast
      _ = ENNReal.ofReal ‖f‖ := by rw [hFcastNorm]
  have hF : eLpNorm (fun x : ℤ => f x) (2 : ℝ≥0∞) Measure.count =
      ENNReal.ofReal ‖f‖ := by
    calc
      _ = eLpNorm (fun x : ℤ => f x)
          (ENNReal.ofReal (2 : ℝ)) Measure.count := by
        exact (congrArg
          (fun p : ℝ≥0∞ => eLpNorm (fun x : ℤ => f x) p Measure.count)
          hP₂).symm
      _ = ENNReal.ofReal ‖f‖ := hFatOfReal
  calc
    _ = ENNReal.ofReal ‖U‖ := hU
    _ ≤ ENNReal.ofReal (A * ‖f‖) := ENNReal.ofReal_le_ofReal hL2
    _ = ENNReal.ofReal A * eLpNorm (fun x : ℤ => f x)
        (2 : ℝ≥0∞) Measure.count := by
      calc
        _ = ENNReal.ofReal A * ENNReal.ofReal ‖f‖ := ENNReal.ofReal_mul hA
        _ = ENNReal.ofReal A * eLpNorm (fun x : ℤ => f x)
            (2 : ℝ≥0∞) Measure.count :=
          congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal A * z) hF.symm

/-- The actual vector-output `lp²` bound gives the scalar `eLpNorm` endpoint
for a finite-support input through pointwise-identical representatives. -/
private theorem localInterpolation_vectorOutput_qTwo_endpoint
    {ι : Type*} [Fintype ι] (A : ℝ) (hA : 0 ≤ A)
    (N : ℕ) (K : ι × Fin N → IntegerL1Kernel) (index : ι → ℤ)
    (S : ℤ → (ℤ → ℂ) → ℤ → ℂ)
    (f : ℤ → ℂ) (_hf : f.HasFiniteSupport)
    (f₂ : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞))
    (hf₂ : ∀ x, f₂ x = f x)
    (U : lp (fun _ : ℤ => PiLp 2 (fun _ : ι × Fin N => ℂ))
      (2 : ℝ≥0∞))
    (hU : ∀ x, U x = integerKernelVectorConvolution K
      (fun y => WithLp.toLp 2
        (fun i : ι × Fin N => S (index i.1) f y)) x)
    (hL2 : ‖U‖ ≤ A * ‖f₂‖) :
    eLpNorm (fun x => ‖integerKernelVectorConvolution K
      (fun y => WithLp.toLp 2
        (fun i : ι × Fin N => S (index i.1) f y)) x‖)
      (2 : ℝ≥0∞) Measure.count ≤
        ENNReal.ofReal A * eLpNorm f (2 : ℝ≥0∞) Measure.count := by
  let V : ℤ → PiLp 2 (fun _ : ι × Fin N => ℂ) := fun x =>
    integerKernelVectorConvolution K
      (fun y => WithLp.toLp 2
        (fun i : ι × Fin N => S (index i.1) f y)) x
  have hUfun : (fun x : ℤ => ‖U x‖) = fun x => ‖V x‖ := by
    funext x
    rw [hU x]
  have hfFun : (fun x : ℤ => f₂ x) = f := by
    funext x
    exact hf₂ x
  have hCore := localInterpolation_qTwo_directEndpoint A hA U f₂ hL2
  calc
    _ = eLpNorm (fun x : ℤ => ‖U x‖) (2 : ℝ≥0∞) Measure.count := by
      exact congrArg
        (fun g : ℤ → ℝ => eLpNorm g (2 : ℝ≥0∞) Measure.count) hUfun.symm
    _ ≤ ENNReal.ofReal A *
        eLpNorm (fun x : ℤ => f₂ x) (2 : ℝ≥0∞) Measure.count := hCore
    _ = ENNReal.ofReal A * eLpNorm f (2 : ℝ≥0∞) Measure.count := by
      exact congrArg
        (fun z : ℝ≥0∞ => ENNReal.ofReal A * z)
        (congrArg
          (fun g : ℤ → ℂ => eLpNorm g (2 : ℝ≥0∞) Measure.count) hfFun)

/-- The exact interpolation weights from the source are `2-q` on the lower
endpoint in the estimate at `q`, and `q-1` on the `ℓ²` endpoint in the
estimate at `q'`. -/
theorem localInterpolation_weight_identities {q : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2) :
    localInterpolationR q * (2 - q) /
        (q * (2 - localInterpolationR q)) = 2 - q ∧
      2 * (localInterpolationRPrime q - localInterpolationQPrime q) /
        (localInterpolationQPrime q *
          (localInterpolationRPrime q - 2)) = q - 1 := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hqsub : 0 < q - 1 := sub_pos.mpr hq1
  have hqplus : 0 < q + 1 := by linarith
  have hqplus_ne : q + 1 ≠ 0 := ne_of_gt hqplus
  have hqsub_ne : q - 1 ≠ 0 := ne_of_gt hqsub
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hrpos : 0 < localInterpolationR q := by
    unfold localInterpolationR
    exact div_pos (by positivity) hqplus
  have hqprimepos : 0 < localInterpolationQPrime q :=
    div_pos hqpos hqsub
  constructor
  · have hden : q * (2 - localInterpolationR q) =
        localInterpolationR q := by
      unfold localInterpolationR
      field_simp
      <;> ring
    rw [hden]
    field_simp [ne_of_gt hrpos]
  · unfold localInterpolationRPrime localInterpolationQPrime
    field_simp [hqsub_ne, hqne]
    <;> ring

/-- The two strong-interpolation applications used in the strict range
`1<q<2`. The hypotheses are the endpoint bounds for the scalar pointwise
output norm; the convolution and square-function hypotheses of
`lm:localInterpolation` are used in the next assembly step to establish
these three bounds. -/
theorem localInterpolation_strongStage
    {q beta A : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (hbeta : 0 ≤ beta) (hA : 0 ≤ A)
    (T : (ℤ → ℂ) → ℤ → ℝ)
    (hTsub : ∀ g h, g.HasFiniteSupport → h.HasFiniteSupport →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (hTnonneg : ∀ g, g.HasFiniteSupport → ∀ x, 0 ≤ T g x)
    (hTr : ∀ f, f.HasFiniteSupport →
      eLpNorm (T f) (ENNReal.ofReal (localInterpolationR q)) Measure.count ≤
        ENNReal.ofReal beta *
          eLpNorm f (ENNReal.ofReal (localInterpolationR q)) Measure.count)
    (hTtwo : ∀ f, f.HasFiniteSupport →
      eLpNorm (T f) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal 2) Measure.count)
    (hTr' : ∀ f, f.HasFiniteSupport →
      eLpNorm (T f) (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count ≤
        ENNReal.ofReal beta *
          eLpNorm f (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count)
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm (T f) (ENNReal.ofReal q) Measure.count ≤
        ENNReal.ofReal
          (localInterpolationC q * beta ^ (2 - q) * A ^ (q - 1)) *
          eLpNorm f (ENNReal.ofReal q) Measure.count ∧
      eLpNorm (T f)
          (ENNReal.ofReal (localInterpolationQPrime q)) Measure.count ≤
        ENNReal.ofReal
          (localInterpolationC q * beta ^ (2 - q) * A ^ (q - 1)) *
          eLpNorm f (ENNReal.ofReal (localInterpolationQPrime q)) Measure.count := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hqminus : 0 < q - 1 := sub_pos.mpr hq1
  have hqplus : 0 < q + 1 := by linarith
  have hrOne : 1 ≤ localInterpolationR q := by
    apply (le_div_iff₀ hqplus).2
    nlinarith
  have hrq : localInterpolationR q < q := by
    apply (div_lt_iff₀ hqplus).2
    have hprod : 0 < q * (q - 1) := mul_pos hqpos hqminus
    nlinarith
  have hqprimepos : 0 < localInterpolationQPrime q :=
    div_pos hqpos hqminus
  have htwoqprime : 2 < localInterpolationQPrime q := by
    apply (lt_div_iff₀ hqminus).2
    nlinarith
  have hqprimer' : localInterpolationQPrime q <
      localInterpolationRPrime q := by
    rw [localInterpolationQPrime, localInterpolationRPrime]
    apply (div_lt_div_iff₀ hqminus hqminus).2
    nlinarith [hqpos]
  have hweights := localInterpolation_weight_identities hq1 hq2
  have hthetaLow : localInterpolationR q * (2 - q) /
      (q * (2 - localInterpolationR q)) = 2 - q := hweights.1
  have hthetaHigh : 2 * (localInterpolationRPrime q -
      localInterpolationQPrime q) /
      (localInterpolationQPrime q * (localInterpolationRPrime q - 2)) = q - 1 :=
    hweights.2
  have hcompLow : 1 - (2 - q) = q - 1 := by
    ring
  have hcompHigh : 1 - (q - 1) = 2 - q := by
    ring
  have hlow := strongInterpolation
    (s₀ := localInterpolationR q) (p := q) (s₁ := 2)
    (A₀ := beta) (A₁ := A)
    hrOne hrq hq2 hbeta hA T hTsub hTnonneg hTr hTtwo f hf
  have hhigh := strongInterpolation
    (s₀ := 2) (p := localInterpolationQPrime q)
    (s₁ := localInterpolationRPrime q) (A₀ := A) (A₁ := beta)
    (by norm_num) htwoqprime hqprimer' hA hbeta T hTsub hTnonneg
    hTtwo hTr' f hf
  rw [hthetaLow, hcompLow] at hlow
  rw [hthetaHigh, hcompHigh] at hhigh
  have hbetaPow : 0 ≤ beta ^ (2 - q) := Real.rpow_nonneg hbeta _
  have hAPow : 0 ≤ A ^ (q - 1) := Real.rpow_nonneg hA _
  have hproductNonneg : 0 ≤ beta ^ (2 - q) * A ^ (q - 1) :=
    mul_nonneg hbetaPow hAPow
  have hlowCoefficient :
      2 * (q / (q - localInterpolationR q) + q / (2 - q)) ^ (1 / q) *
          beta ^ (2 - q) * A ^ (q - 1) ≤
        localInterpolationC q * beta ^ (2 - q) * A ^ (q - 1) := by
    unfold localInterpolationC
    calc
      _ = (2 * (q / (q - localInterpolationR q) + q / (2 - q)) ^
            (1 / q)) * (beta ^ (2 - q) * A ^ (q - 1)) := by ring
      _ ≤ max
            (2 * (q / (q - localInterpolationR q) + q / (2 - q)) ^ (1 / q))
            (2 * (localInterpolationQPrime q /
              (localInterpolationQPrime q - 2) +
              localInterpolationQPrime q /
                (localInterpolationRPrime q - localInterpolationQPrime q)) ^
                  (1 / localInterpolationQPrime q)) *
            (beta ^ (2 - q) * A ^ (q - 1)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hproductNonneg
      _ = _ := by ring
  have hhighCoefficient :
      2 * (localInterpolationQPrime q /
          (localInterpolationQPrime q - 2) +
        localInterpolationQPrime q /
          (localInterpolationRPrime q - localInterpolationQPrime q)) ^
            (1 / localInterpolationQPrime q) *
          A ^ (q - 1) * beta ^ (2 - q) ≤
        localInterpolationC q * beta ^ (2 - q) * A ^ (q - 1) := by
    unfold localInterpolationC
    calc
      _ = (2 * (localInterpolationQPrime q /
            (localInterpolationQPrime q - 2) +
          localInterpolationQPrime q /
            (localInterpolationRPrime q - localInterpolationQPrime q)) ^
              (1 / localInterpolationQPrime q)) *
            (beta ^ (2 - q) * A ^ (q - 1)) := by ring
      _ ≤ max
            (2 * (q / (q - localInterpolationR q) + q / (2 - q)) ^ (1 / q))
            (2 * (localInterpolationQPrime q /
              (localInterpolationQPrime q - 2) +
              localInterpolationQPrime q /
                (localInterpolationRPrime q - localInterpolationQPrime q)) ^
                  (1 / localInterpolationQPrime q)) *
            (beta ^ (2 - q) * A ^ (q - 1)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hproductNonneg
      _ = _ := by ring
  constructor
  · calc
      eLpNorm (T f) (ENNReal.ofReal q) Measure.count ≤
          ENNReal.ofReal
            (2 * (q / (q - localInterpolationR q) + q / (2 - q)) ^ (1 / q) *
              beta ^ (2 - q) * A ^ (q - 1)) *
            eLpNorm f (ENNReal.ofReal q) Measure.count := hlow
      _ ≤ _ := by
        gcongr
  · calc
      eLpNorm (T f) (ENNReal.ofReal (localInterpolationQPrime q)) Measure.count ≤
          ENNReal.ofReal
            (2 * (localInterpolationQPrime q /
                (localInterpolationQPrime q - 2) +
              localInterpolationQPrime q /
                (localInterpolationRPrime q - localInterpolationQPrime q)) ^
                  (1 / localInterpolationQPrime q) *
              A ^ (q - 1) * beta ^ (2 - q)) *
            eLpNorm f (ENNReal.ofReal (localInterpolationQPrime q)) Measure.count :=
        hhigh
      _ ≤ _ := by
        gcongr

/-- The finite-support form of the localized interpolation and multiplicity
lemma. The square-function estimates are supplied on the full source `lp`
domains, and the direct endpoint is supplied by its actual `lp²` output
representatives. The separate continuity extension is stated only when the
selected operators have continuous `lp` realizations. -/
theorem localizedInterpolation
    {q E₀ B P_r P_r' A : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2)
    (N : ℕ) (hN : 1 ≤ N) (K : Finset ℤ) (j : ℤ)
    (kernels : {k : ℤ // k ∈ K} × Fin N → IntegerL1Kernel)
    (S : ℤ → ((ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ)))
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (kernels i) ≤ E₀)
    (hmax : ∀ (H : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ H x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax kernels H hh x) ∧
          ‖M‖ ≤ B * ‖H‖)
    (hSqR : ∀ F : lp (fun _ : ℤ => ℂ)
        (ENNReal.ofReal (localInterpolationR q)),
      ∃ G : lp (fun _ : ℤ => ℝ)
          (ENNReal.ofReal (localInterpolationR q)),
        (∀ x, 0 ≤ G x) ∧
        (∀ x, ENNReal.ofReal (G x) =
          localInterpolationExtendedSquareFunction
            (fun x h => S h (F : ℤ → ℂ) x) x) ∧
        ‖G‖ ≤ P_r * ‖F‖)
    (hSqR' : ∀ F : lp (fun _ : ℤ => ℂ)
        (ENNReal.ofReal (localInterpolationRPrime q)),
      ∃ G : lp (fun _ : ℤ => ℝ)
          (ENNReal.ofReal (localInterpolationRPrime q)),
        (∀ x, 0 ≤ G x) ∧
        (∀ x, ENNReal.ofReal (G x) =
          localInterpolationExtendedSquareFunction
            (fun x h => S h (F : ℤ → ℂ) x) x) ∧
        ‖G‖ ≤ P_r' * ‖F‖)
    (hDirect : ∀ F : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞),
      ∃ U : lp
          (fun _ : ℤ => PiLp 2 (fun _ : {k : ℤ // k ∈ K} × Fin N => ℂ))
          (2 : ℝ≥0∞),
        (∀ x, U x = integerKernelVectorConvolution kernels
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ K} × Fin N =>
              S (i.1.1 + j) (F : ℤ → ℂ) y)) x) ∧
        ‖U‖ ≤ A * ‖F‖)
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm (fun x => ‖integerKernelVectorConvolution kernels
      (fun y => WithLp.toLp 2
        (fun i : {k : ℤ // k ∈ K} × Fin N => S (i.1.1 + j) f y)) x‖)
      (ENNReal.ofReal q) Measure.count ≤
        ENNReal.ofReal
          (localInterpolationC q *
            (max 1 (max P_r P_r')) ^ (2 - q) *
            ((N : ℝ) * E₀ * B) ^ ((2 - q) / 2) *
            A ^ (q - 1)) *
          eLpNorm f (ENNReal.ofReal q) Measure.count ∧
    eLpNorm (fun x => ‖integerKernelVectorConvolution kernels
      (fun y => WithLp.toLp 2
        (fun i : {k : ℤ // k ∈ K} × Fin N => S (i.1.1 + j) f y)) x‖)
      (ENNReal.ofReal (localInterpolationQPrime q)) Measure.count ≤
        ENNReal.ofReal
          (localInterpolationC q *
            (max 1 (max P_r P_r')) ^ (2 - q) *
            ((N : ℝ) * E₀ * B) ^ ((2 - q) / 2) *
            A ^ (q - 1)) *
          eLpNorm f (ENNReal.ofReal (localInterpolationQPrime q)) Measure.count := by
  classical
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hqminus : 0 < q - 1 := sub_pos.mpr hq1
  have hqplus : 0 < q + 1 := by linarith
  have hrOne : 1 < localInterpolationR q := by
    dsimp [localInterpolationR]
    rw [lt_div_iff₀ hqplus]
    nlinarith
  have hr'One : 1 < localInterpolationRPrime q := by
    dsimp [localInterpolationRPrime]
    rw [lt_div_iff₀ hqminus]
    nlinarith
  let Pstar : ℝ := max 1 (max P_r P_r')
  have hPstar : 0 ≤ Pstar := by
    dsimp [Pstar]
    exact le_trans (by norm_num) (le_max_left _ _)
  have hPstarOne : 1 ≤ Pstar := by
    dsimp [Pstar]
    exact le_max_left _ _
  have hPrLe : P_r ≤ Pstar := by
    dsimp [Pstar]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hPr'Le : P_r' ≤ Pstar := by
    dsimp [Pstar]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  let index : {k : ℤ // k ∈ K} → ℤ := fun k => k.1 + j
  let Sraw : ℤ → (ℤ → ℂ) → ℤ → ℂ := fun h g x => S h g x
  let T : (ℤ → ℂ) → ℤ → ℝ := fun g x =>
    ‖integerKernelVectorConvolution kernels
      (fun y => WithLp.toLp 2
        (fun i : {k : ℤ // k ∈ K} × Fin N => Sraw (index i.1) g y)) x‖
  let beta : ℝ := Real.sqrt (E₀ * B) * Real.sqrt (N : ℝ) * Pstar
  have hSadd : ∀ h g₁ g₂ y,
      Sraw h (g₁ + g₂) y = Sraw h g₁ y + Sraw h g₂ y := by
    intro h g₁ g₂ y
    exact congrArg (fun g : ℤ → ℂ => g y) ((S h).map_add g₁ g₂)
  have hSqRraw : ∀ g, g.HasFiniteSupport →
      eLpNorm (localInterpolationExtendedSquareFunction
        (fun x h => Sraw h g x))
          (ENNReal.ofReal (localInterpolationR q)) Measure.count ≤
        ENNReal.ofReal P_r *
          eLpNorm g (ENNReal.ofReal (localInterpolationR q)) Measure.count := by
    intro g hg
    simpa [Sraw] using
      localInterpolation_fullSquareWitness_of_finiteSupport
        (p := localInterpolationR q) (P := P_r) hrOne S hSqR g hg
  have hSqR'raw : ∀ g, g.HasFiniteSupport →
      eLpNorm (localInterpolationExtendedSquareFunction
        (fun x h => Sraw h g x))
          (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count ≤
        ENNReal.ofReal P_r' *
          eLpNorm g (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count := by
    intro g hg
    simpa [Sraw] using
      localInterpolation_fullSquareWitness_of_finiteSupport
        (p := localInterpolationRPrime q) (P := P_r') hr'One S hSqR' g hg
  have hSqRstar : ∀ g, g.HasFiniteSupport →
      eLpNorm (localInterpolationExtendedSquareFunction
        (fun x h => Sraw h g x))
          (ENNReal.ofReal (localInterpolationR q)) Measure.count ≤
        ENNReal.ofReal Pstar *
          eLpNorm g (ENNReal.ofReal (localInterpolationR q)) Measure.count := by
    intro g hg
    calc
      _ ≤ ENNReal.ofReal P_r *
          eLpNorm g (ENNReal.ofReal (localInterpolationR q)) Measure.count :=
        hSqRraw g hg
      _ ≤ ENNReal.ofReal Pstar *
          eLpNorm g (ENNReal.ofReal (localInterpolationR q)) Measure.count :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hPrLe) _
  have hA : 0 ≤ A := by
    let δ : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) :=
      lp.single (2 : ℝ≥0∞) (0 : ℤ) (1 : ℂ)
    obtain ⟨U, _hU, hUbound⟩ := hDirect δ
    have hδnorm : ‖δ‖ = 1 := by
      simpa [δ] using
        (lp.norm_single (p := (2 : ℝ≥0∞))
          (E := fun _ : ℤ => ℂ) (by norm_num) (0 : ℤ) (1 : ℂ))
    have hUleA : ‖U‖ ≤ A := by
      calc
        ‖U‖ ≤ A * ‖δ‖ := hUbound
        _ = A := by rw [hδnorm, mul_one]
    exact (norm_nonneg U).trans hUleA
  have hTr : ∀ g, g.HasFiniteSupport →
      eLpNorm (T g) (ENNReal.ofReal (localInterpolationR q)) Measure.count ≤
        ENNReal.ofReal beta *
          eLpNorm g (ENNReal.ofReal (localInterpolationR q)) Measure.count := by
    intro g hg
    have hbounds := localInterpolation_scalarEndpointBounds
      hq1 N K j kernels hE₀ hB hmass hmax Sraw g hg
      (hSqRraw g hg) (hSqR'raw g hg)
    simpa [T, Sraw, beta, Pstar] using hbounds.1
  have hTr' : ∀ g, g.HasFiniteSupport →
      eLpNorm (T g) (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count ≤
        ENNReal.ofReal beta *
          eLpNorm g (ENNReal.ofReal (localInterpolationRPrime q)) Measure.count := by
    intro g hg
    have hbounds := localInterpolation_scalarEndpointBounds
      hq1 N K j kernels hE₀ hB hmass hmax Sraw g hg
      (hSqRraw g hg) (hSqR'raw g hg)
    simpa [T, Sraw, beta, Pstar] using hbounds.2
  have hTsub : ∀ g h, g.HasFiniteSupport → h.HasFiniteSupport →
      ∀ x, T (g + h) x ≤ T g x + T h x := by
    intro g h hg hh x
    have hadd : ∀ n y,
        Sraw n (g + h) y = Sraw n g y + Sraw n h y := by
      intro n y
      exact congrArg (fun z : ℤ → ℂ => z y) ((S n).map_add g h)
    simpa [T] using
      localInterpolation_vectorOutputNorm_subadditive
        (p := localInterpolationR q) (P := Pstar) hrOne hPstar
        N kernels index Sraw g h hg hh hadd (hSqRstar g hg) (hSqRstar h hh) x
  have hTnonneg : ∀ g, g.HasFiniteSupport → ∀ x, 0 ≤ T g x := by
    intro g _hg x
    exact localInterpolation_vectorOutputNorm_nonneg N kernels index Sraw g x
  have hP₂ : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hTtwo : ∀ g, g.HasFiniteSupport →
      eLpNorm (T g) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal 2) Measure.count := by
    intro g hg
    have hp20 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp2top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have hp2one : 1 ≤ (2 : ℝ≥0∞) := by norm_num
    let F₂ : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) :=
      finiteSupportSequenceLpGeneral (p := (2 : ℝ≥0∞))
        hp20 hp2top hp2one hg.toFinset g
    have hF₂point : ∀ x, F₂ x = g x := by
      intro x
      rw [finiteSupportSequenceLpGeneral_apply
        (p := (2 : ℝ≥0∞)) hp20 hp2top hp2one hg.toFinset g x]
      by_cases hx : x ∈ hg.toFinset
      · simp [hx]
      · have hgx : g x = 0 := by
          by_contra hgx
          exact hx (hg.mem_toFinset.mpr (Function.mem_support.mpr hgx))
        simp [hx, hgx]
    have hF₂seq : (F₂ : ℤ → ℂ) = g := funext hF₂point
    obtain ⟨U, hU, hL2⟩ := hDirect F₂
    have hInputEq :
        (fun y : ℤ => WithLp.toLp 2
          (fun i : {k : ℤ // k ∈ K} × Fin N =>
            S (i.1.1 + j) (F₂ : ℤ → ℂ) y)) =
        (fun y : ℤ => WithLp.toLp 2
          (fun i : {k : ℤ // k ∈ K} × Fin N =>
            Sraw (index i.1) g y)) := by
      funext y
      apply PiLp.ext
      intro i
      dsimp [Sraw, index]
      exact congrArg (fun z : ℤ → ℂ => S (i.1.1 + j) z y) hF₂seq
    have hUraw : ∀ x, U x = integerKernelVectorConvolution kernels
        (fun y => WithLp.toLp 2
          (fun i : {k : ℤ // k ∈ K} × Fin N =>
            Sraw (index i.1) g y)) x := by
      intro x
      calc
        U x = integerKernelVectorConvolution kernels
            (fun y => WithLp.toLp 2
              (fun i : {k : ℤ // k ∈ K} × Fin N =>
                S (i.1.1 + j) (F₂ : ℤ → ℂ) y)) x := hU x
        _ = integerKernelVectorConvolution kernels
            (fun y => WithLp.toLp 2
              (fun i : {k : ℤ // k ∈ K} × Fin N =>
                Sraw (index i.1) g y)) x :=
          congrArg
            (fun v : ℤ → PiLp 2
              (fun _ : {k : ℤ // k ∈ K} × Fin N => ℂ) =>
                integerKernelVectorConvolution kernels v x) hInputEq
    have hcore := localInterpolation_vectorOutput_qTwo_endpoint
      A hA N kernels index Sraw g hg F₂ hF₂point U hUraw hL2
    simpa only [hP₂] using hcore
  have hE₀B : 0 ≤ E₀ * B := mul_nonneg hE₀ hB
  have hBeta : 0 ≤ beta := by
    dsimp [beta]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hPstar
  have hStage := localInterpolation_strongStage
    hq1 hq2 hBeta hA T hTsub hTnonneg hTr hTtwo hTr' f hf
  have hCoefficient :
      localInterpolationC q * beta ^ (2 - q) * A ^ (q - 1) =
        localInterpolationC q * Pstar ^ (2 - q) *
          ((N : ℝ) * E₀ * B) ^ ((2 - q) / 2) * A ^ (q - 1) := by
    dsimp [beta]
    rw [localInterpolation_endpointCoefficient_rpow
      hq1 hq2 N hN hE₀ hB hPstarOne]
    ring
  have hqBound :
      eLpNorm (T f) (ENNReal.ofReal q) Measure.count ≤
        ENNReal.ofReal
          (localInterpolationC q * Pstar ^ (2 - q) *
            ((N : ℝ) * E₀ * B) ^ ((2 - q) / 2) * A ^ (q - 1)) *
          eLpNorm f (ENNReal.ofReal q) Measure.count := by
    calc
      _ ≤ ENNReal.ofReal
          (localInterpolationC q * beta ^ (2 - q) * A ^ (q - 1)) *
          eLpNorm f (ENNReal.ofReal q) Measure.count := hStage.1
      _ = _ := by rw [hCoefficient]
  have hq'Bound :
      eLpNorm (T f) (ENNReal.ofReal (localInterpolationQPrime q)) Measure.count ≤
        ENNReal.ofReal
          (localInterpolationC q * Pstar ^ (2 - q) *
            ((N : ℝ) * E₀ * B) ^ ((2 - q) / 2) * A ^ (q - 1)) *
          eLpNorm f (ENNReal.ofReal (localInterpolationQPrime q)) Measure.count := by
    calc
      _ ≤ ENNReal.ofReal
          (localInterpolationC q * beta ^ (2 - q) * A ^ (q - 1)) *
          eLpNorm f (ENNReal.ofReal (localInterpolationQPrime q)) Measure.count :=
        hStage.2
      _ = _ := by rw [hCoefficient]
  constructor
  · simpa [T, Sraw, index, Pstar] using hqBound
  · simpa [T, Sraw, index, Pstar] using hq'Bound

end

end FractionalPrimes.Literature.MSZ
