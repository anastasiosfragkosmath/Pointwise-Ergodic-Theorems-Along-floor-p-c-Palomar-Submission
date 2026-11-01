module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Fixed data for the periodic multiplier theorem (`lp:data`)

This module records the once-fixed cutoff, its exact constants, and the
periodic-symbol hypotheses from the approved multiplier blueprint. Symbols
are represented by their 1-periodic lifts to `ℝ`; smoothness away from the
integer translates of zero is the punctured-torus smoothness condition, and
seam matching is stated at the representatives `-1/2` and `1/2`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open Set
open MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

/-- The fixed cutoff is Mathlib's smooth bump with inner radius `1/8` and
outer radius `3/16`, so its topological support lies strictly inside
`(-1/4, 1/4)`. -/
def fixedCutoffBump : ContDiffBump (0 : ℝ) :=
  ⟨(1 / 8 : ℝ), (3 / 16 : ℝ), by norm_num, by norm_num⟩

/-- The once-fixed even cutoff `ψ` from `lp:data`. -/
def ψ : ℝ → ℝ := fixedCutoffBump

theorem ψ_even (x : ℝ) : ψ (-x) = ψ x :=
  fixedCutoffBump.neg x

theorem ψ_nonneg (x : ℝ) : 0 ≤ ψ x :=
  fixedCutoffBump.nonneg

theorem ψ_le_one (x : ℝ) : ψ x ≤ 1 :=
  fixedCutoffBump.le_one

theorem ψ_eq_one_of_abs_le (x : ℝ) (hx : |x| ≤ 1 / 8) : ψ x = 1 := by
  apply fixedCutoffBump.one_of_mem_closedBall
  change dist x 0 ≤ (1 / 8 : ℝ)
  simpa [Real.dist_eq] using hx

theorem support_ψ : Function.support ψ = Metric.ball (0 : ℝ) (3 / 16 : ℝ) := by
  simpa [ψ, fixedCutoffBump] using fixedCutoffBump.support_eq

theorem tsupport_ψ : tsupport ψ = Metric.closedBall (0 : ℝ) (3 / 16 : ℝ) :=
  fixedCutoffBump.tsupport_eq

theorem tsupport_ψ_subset : tsupport ψ ⊆ Set.Ioo (-(1 / 4 : ℝ)) (1 / 4) := by
  rw [tsupport_ψ]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq] at hx
  constructor <;> linarith [abs_le.mp hx]

theorem ψ_contDiff : ContDiff ℝ (∞ : ℕ∞ω) ψ :=
  fixedCutoffBump.contDiff

theorem ψ_hasCompactSupport : HasCompactSupport ψ :=
  fixedCutoffBump.hasCompactSupport

/-- The norm of the first derivative of the fixed cutoff, in the usual
supremum-norm sense. -/
def ψDerivSup : ℝ := sSup (Set.range fun x : ℝ => ‖deriv ψ x‖)

/-- The norm of the second derivative of the fixed cutoff. -/
def ψSecondDerivSup : ℝ := sSup (Set.range fun x : ℝ => ‖iteratedDeriv 2 ψ x‖)

private theorem ψ_deriv_bddAbove : BddAbove (Set.range fun x : ℝ => ‖deriv ψ x‖) := by
  obtain ⟨C, hC⟩ :=
    (ψ_contDiff.continuous_deriv (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).bounded_above_of_compact_support
      ψ_hasCompactSupport.deriv
  refine ⟨C, ?_⟩
  rintro y ⟨x, rfl⟩
  exact hC x

private theorem ψ_secondDeriv_bddAbove :
    BddAbove (Set.range fun x : ℝ => ‖iteratedDeriv 2 ψ x‖) := by
  have hcont : Continuous (iteratedDeriv 2 ψ) :=
    ψ_contDiff.continuous_iteratedDeriv 2 (by norm_num)
  have hcompact : HasCompactSupport (iteratedDeriv 2 ψ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact ψ_hasCompactSupport.deriv.deriv
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcompact
  refine ⟨C, ?_⟩
  rintro y ⟨x, rfl⟩
  exact hC x

theorem norm_deriv_ψ_le_sup (x : ℝ) : ‖deriv ψ x‖ ≤ ψDerivSup := by
  apply le_csSup ψ_deriv_bddAbove
  exact ⟨x, rfl⟩

theorem norm_iteratedDeriv_two_ψ_le_sup (x : ℝ) :
    ‖iteratedDeriv 2 ψ x‖ ≤ ψSecondDerivSup := by
  apply le_csSup ψ_secondDeriv_bddAbove
  exact ⟨x, rfl⟩

theorem ψDerivSup_nonneg : 0 ≤ ψDerivSup := by
  exact (norm_nonneg (deriv ψ 0)).trans <| le_csSup ψ_deriv_bddAbove ⟨0, rfl⟩

theorem ψSecondDerivSup_nonneg : 0 ≤ ψSecondDerivSup := by
  exact (norm_nonneg (iteratedDeriv 2 ψ 0)).trans <|
    le_csSup ψ_secondDeriv_bddAbove ⟨0, rfl⟩

/-- The exact cutoff-dependent constant `B` in the approved blueprint. -/
def B : ℝ := 1 + ψDerivSup + ψSecondDerivSup

/-- The exact cutoff-dependent constant `A = 2^16 B`. -/
def A : ℝ := 2 ^ 16 * B

/-- The exact cutoff-dependent constant `H₀ = 64 A`. -/
def H₀ : ℝ := 64 * A

/-- The exact weak-type constant `W = 13 + 4 H₀`. -/
def W : ℝ := 13 + 4 * H₀

theorem B_pos : 0 < B := by
  unfold B
  linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]

theorem A_eq : A = 2 ^ 16 * B := rfl

theorem H₀_eq : H₀ = 64 * A := rfl

theorem W_eq : W = 13 + 4 * H₀ := rfl

/-- The integers are exactly the singular points in the real-line lift of
the punctured torus. -/
def puncturedTorusLift : Set ℝ := {x | x ∉ Set.range (fun n : ℤ => (n : ℝ))}

/-- The data and hypotheses from definition `lp:data`, expressed for a
periodic lift of the torus symbol. The smoothness and derivative bound use
the same two classical derivatives as the blueprint. -/
structure SymbolData (m : ℝ → ℂ) (D : ℝ) : Prop where
  measurable : Measurable m
  bounded : ∃ C : ℝ, ∀ x : ℝ, ‖m x‖ ≤ C
  periodic : Function.Periodic m 1
  smoothOnPuncturedTorus : ContDiffOn ℝ 2 m puncturedTorusLift
  seamValue : m (-(1 / 2 : ℝ)) = m (1 / 2)
  seamFirstDerivative : deriv m (-(1 / 2 : ℝ)) = deriv m (1 / 2)
  seamSecondDerivative : iteratedDeriv 2 m (-(1 / 2 : ℝ)) = iteratedDeriv 2 m (1 / 2)
  weightedDerivativeBound : ∀ ξ : ℝ, 0 < |ξ| → |ξ| < 1 / 2 →
    ‖m ξ‖ + ‖ξ * deriv m ξ‖ + ‖ξ ^ 2 * iteratedDeriv 2 m ξ‖ ≤ D

/-- The blueprint's bound itself forces its real constant `D` to be
nonnegative; this is therefore a consequence, not an extra hypothesis. -/
theorem SymbolData.D_nonneg {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) : 0 ≤ D := by
  have hbound := h.weightedDerivativeBound (1 / 4) (by norm_num) (by norm_num)
  have h₁ : 0 ≤ ‖m (1 / 4 : ℝ)‖ := norm_nonneg _
  have h₂ : 0 ≤ ‖(1 / 4 : ℝ) * deriv m (1 / 4)‖ := norm_nonneg _
  have h₃ : 0 ≤ ‖(1 / 4 : ℝ) ^ 2 * iteratedDeriv 2 m (1 / 4)‖ := norm_nonneg _
  linarith

/-- The normalized additive circle used for the Fourier convention in
`lp:data`; Mathlib's `haarAddCircle` has total mass one. -/
abbrev Torus := AddCircle (1 : ℝ)

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def torusHaar : Measure Torus :=
  @AddCircle.haarAddCircle (1 : ℝ) inferInstance

theorem torusHaar_isProbability : IsProbabilityMeasure torusHaar := by
  change IsProbabilityMeasure (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩)
  infer_instance

local instance : IsProbabilityMeasure torusHaar := torusHaar_isProbability

local instance : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := by
  constructor
  norm_num

/-- Reindex an `ℓ²(ℤ)` sequence by `n ↦ -n`.  This is the index change
needed to make Mathlib's positive-frequency Hilbert basis agree with the
blueprint's negative-exponential Fourier convention. -/
def negIndexL2 (f : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 := by
  refine ⟨fun n => f (-n), ?_⟩
  change Memℓp (fun n : ℤ => f (-n)) (2 : ℝ≥0∞)
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  exact (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    |>.comp_injective (fun _ _ h => neg_injective h)

/-- Index reflection is a complex-linear isometry on `ℓ²(ℤ)`. -/
def negIndexL2Equiv :
    lp (fun _ : ℤ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun := negIndexL2
  invFun := negIndexL2
  left_inv := by
    intro f
    apply lp.ext
    funext n
    simp [negIndexL2]
  right_inv := by
    intro f
    apply lp.ext
    funext n
    simp [negIndexL2]
  map_add' := by
    intro f g
    apply lp.ext
    funext n
    rfl
  map_smul' := by
    intro c f
    apply lp.ext
    funext n
    rfl
  norm_map' := by
    intro f
    change ‖negIndexL2 f‖ = ‖f‖
    rw [lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num) (negIndexL2 f),
      lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num) f]
    congr 1
    change (∑' n : ℤ, ‖f (-n)‖ ^ (2 : ℝ)) = ∑' n : ℤ, ‖f n‖ ^ (2 : ℝ)
    rw [show (fun n : ℤ => ‖f (-n)‖ ^ (2 : ℝ)) =
      (fun n : ℤ => ‖f n‖ ^ (2 : ℝ)) ∘ Equiv.neg ℤ by funext n; simp]
    simpa [Function.comp_def] using
      (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ‖f n‖ ^ (2 : ℝ))

/-- The unitary Fourier transform from sequence `ℓ²` to the normalized
circle `L²`, with `\hat f(ξ)=∑ₙ f(n)e^{-2πinξ}`. -/
def sequenceToCircleL2 :
    lp (fun _ : ℤ => ℂ) 2 ≃ₗᵢ[ℂ] Lp ℂ 2 torusHaar :=
  negIndexL2Equiv.trans ((@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr.symm)

/-- The periodic symbol on the additive circle, obtained from its periodic
real-line lift. -/
def torusSymbol {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) : Torus → ℂ :=
  h.periodic.lift

theorem torusSymbol_coe {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (x : ℝ) :
    torusSymbol h (x : Torus) = m x :=
  h.periodic.lift_coe x

theorem torusSymbol_measurable {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    Measurable (torusSymbol h) := by
  rw [measurable_from_quotient]
  change Measurable (fun x : ℝ => torusSymbol h (x : Torus))
  simpa only [torusSymbol_coe] using h.measurable

theorem torusSymbol_norm_le {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D)
    (C : ℝ) (hC : ∀ x : ℝ, ‖m x‖ ≤ C) (ξ : Torus) :
    ‖torusSymbol h ξ‖ ≤ C := by
  induction ξ using QuotientAddGroup.induction_on with
  | H x =>
      simpa [torusSymbol] using hC x

/-- The bounded torus symbol as an `L∞` element. -/
def torusSymbolLp {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    Lp ℂ ⊤ torusHaar := by
  let C : ℝ := Classical.choose h.bounded
  have hC : ∀ x : ℝ, ‖m x‖ ≤ C := Classical.choose_spec h.bounded
  have hmeas : AEStronglyMeasurable (torusSymbol h) torusHaar :=
    (torusSymbol_measurable h).aestronglyMeasurable
  have hbound : ∀ᵐ ξ ∂torusHaar, ‖torusSymbol h ξ‖ ≤ max 0 C := by
    filter_upwards with ξ
    exact (torusSymbol_norm_le h C hC ξ).trans (le_max_right 0 C)
  exact (MemLp.of_bound hmeas (max 0 C) hbound).toLp (torusSymbol h)

theorem torusSymbolLp_coeFn {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    (torusSymbolLp h : Torus → ℂ) =ᵐ[torusHaar] torusSymbol h := by
  unfold torusSymbolLp
  exact MemLp.coeFn_toLp _

/-- The Fourier multiplier on `ℓ²(ℤ)`, defined by conjugating multiplication
by the symbol with the unitary circle Fourier transform. -/
def TmL2 {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D)
    (f : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  sequenceToCircleL2.symm (torusSymbolLp h • sequenceToCircleL2 f)

/-- Multiplication by an `L∞` symbol on circle `L²`, as a continuous linear
map. -/
def torusSymbolMultiplicationCLM (g : Lp ℂ ⊤ torusHaar) :
    Lp ℂ 2 torusHaar →L[ℂ] Lp ℂ 2 torusHaar := by
  let L : Lp ℂ 2 torusHaar →ₗ[ℂ] Lp ℂ 2 torusHaar :=
    { toFun := fun f => g • f
      map_add' := fun f₁ f₂ => Lp.add_smul g f₁ f₂
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) g (c • f),
          Lp.coeFn_smul c f, Lp.coeFn_smul c (g • f),
          Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) g f] with x h₁ h₂ h₃ h₄
        have h₁' : (g • (c • f)) x = g x * ((c • f) x) := by
          simpa only [Pi.smul_apply', smul_eq_mul] using h₁
        have h₂' : (c • f) x = c * f x := by
          simpa only [Pi.smul_apply, smul_eq_mul] using h₂
        have h₃' : (c • (g • f)) x = c * ((g • f) x) := by
          simpa only [Pi.smul_apply, smul_eq_mul] using h₃
        have h₄' : (g • f) x = g x * f x := by
          simpa only [Pi.smul_apply', smul_eq_mul] using h₄
        calc
          (g • (c • f)) x = g x * ((c • f) x) := h₁'
          _ = g x * (c * f x) := by rw [h₂']
          _ = c * (g x * f x) := by ring
          _ = c * ((g • f) x) := by rw [h₄']
          _ = (c • (g • f)) x := h₃'.symm }
  exact L.mkContinuous ‖g‖ (fun f => Lp.norm_smul_le g f)

/-- The `ℓ²` multiplier as a bounded linear operator, obtained by conjugating
circle multiplication by the unitary Fourier transform. -/
def TmL2CLM {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  (sequenceToCircleL2.symm : Lp ℂ 2 torusHaar →L[ℂ] lp (fun _ : ℤ => ℂ) 2).comp
    ((torusSymbolMultiplicationCLM (torusSymbolLp h)).comp
      (sequenceToCircleL2 : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] Lp ℂ 2 torusHaar))

theorem TmL2_eq_TmL2CLM {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D)
    (f : lp (fun _ : ℤ => ℂ) 2) : TmL2 h f = TmL2CLM h f := by
  simp [TmL2, TmL2CLM, torusSymbolMultiplicationCLM, LinearMap.mkContinuous_apply]

/-- Pointwise operator bound for the `ℓ²` multiplier, with the symbol's
`L∞` norm as the constant. -/
theorem norm_TmL2_le {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖TmL2 h f‖ ≤ ‖torusSymbolLp h‖ * ‖f‖ := by
  calc
    ‖TmL2 h f‖ = ‖torusSymbolLp h • sequenceToCircleL2 f‖ :=
      by change ‖sequenceToCircleL2.symm (torusSymbolLp h • sequenceToCircleL2 f)‖ = _
         exact sequenceToCircleL2.symm.norm_map _
    _ ≤ ‖torusSymbolLp h‖ * ‖sequenceToCircleL2 f‖ :=
      Lp.norm_smul_le _ _
    _ = ‖torusSymbolLp h‖ * ‖f‖ := by rw [sequenceToCircleL2.norm_map]

/-- The exact operator-norm estimate `‖T_m‖₂ ≤ ‖m‖_{L∞}`. -/
theorem norm_TmL2CLM_le {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    ‖TmL2CLM h‖ ≤ ‖torusSymbolLp h‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro f
  rw [← TmL2_eq_TmL2CLM h f]
  exact norm_TmL2_le h f

/-- The finite-sequence Fourier polynomial with the blueprint's negative
exponential convention. -/
def finiteFourierTransform (f : ℤ →₀ ℂ) : Torus → ℂ :=
  fun ξ => ∑ n ∈ f.support, f n * fourier (T := (1 : ℝ)) (-n) ξ

/-- Kernel coefficient convention `K(n) = ∫ m(ξ)e^{2πinξ}dξ`, written as
the corresponding Mathlib Fourier coefficient on the unit additive circle. -/
def kernelCoefficient (m : Torus → ℂ) (n : ℤ) : ℂ :=
  fourierCoeff m (-n)

theorem kernelCoefficient_eq_torusIntegral (m : Torus → ℂ) (n : ℤ) :
    kernelCoefficient m n =
      ∫ ξ : Torus, m ξ * fourier (T := (1 : ℝ)) n ξ ∂torusHaar := by
  change (∫ ξ : Torus, fourier (T := (1 : ℝ)) (-(-n)) ξ • m ξ ∂torusHaar) = _
  simp [smul_eq_mul, mul_comm]

/-- A finitely supported sequence, viewed in `ℓ²(ℤ)`. -/
def finiteSequenceL2 (f : ℤ →₀ ℂ) : lp (fun _ : ℤ => ℂ) 2 := by
  let c : ℤ → ℂ := f
  have hsupp : {n : ℤ | c n ≠ 0} ⊆ (f.support : Set ℤ) := by
    intro n hn
    exact Finsupp.mem_support_iff.mpr (by simpa [c] using hn)
  have hmem0 : Memℓp c 0 :=
    memℓp_zero (f.support.finite_toSet.subset hsupp)
  exact ⟨c, hmem0.of_exponent_ge (by norm_num)⟩

@[simp] theorem finiteSequenceL2_apply (f : ℤ →₀ ℂ) (n : ℤ) :
    finiteSequenceL2 f n = f n := by
  simp [finiteSequenceL2]

theorem finiteFourierTransform_continuous (f : ℤ →₀ ℂ) :
    Continuous (finiteFourierTransform f) := by
  classical
  unfold finiteFourierTransform
  fun_prop

theorem finiteFourierTransform_memLp (f : ℤ →₀ ℂ) :
    MemLp (finiteFourierTransform f) 2 torusHaar := by
  classical
  let C : ℝ := ∑ n ∈ f.support, ‖f n‖
  have hbound (ξ : Torus) : ‖finiteFourierTransform f ξ‖ ≤ C := by
    rw [finiteFourierTransform]
    calc
      ‖∑ n ∈ f.support, f n * fourier (T := (1 : ℝ)) (-n) ξ‖ ≤
          ∑ n ∈ f.support, ‖f n * fourier (T := (1 : ℝ)) (-n) ξ‖ := norm_sum_le _ _
      _ = C := by
        rw [show (∑ n ∈ f.support,
            ‖f n * fourier (T := (1 : ℝ)) (-n) ξ‖) =
            ∑ n ∈ f.support, ‖f n‖ by
              apply Finset.sum_congr rfl
              intro n hn
              simp [fourier_apply, Circle.norm_coe]]
  have hmeas : AEStronglyMeasurable (finiteFourierTransform f) torusHaar :=
    (finiteFourierTransform_continuous f).aestronglyMeasurable
  apply MemLp.of_bound hmeas C
  filter_upwards with ξ
  exact hbound ξ

/-- The finite Fourier polynomial as an `L²` element of the circle. -/
def finiteFourierTransformLp (f : ℤ →₀ ℂ) : Lp ℂ 2 torusHaar :=
  (finiteFourierTransform_memLp f).toLp (finiteFourierTransform f)

theorem finiteFourierTransformLp_coeFn (f : ℤ →₀ ℂ) :
    (finiteFourierTransformLp f : Torus → ℂ) =ᵐ[torusHaar] finiteFourierTransform f := by
  exact MemLp.coeFn_toLp (finiteFourierTransform_memLp f)

theorem fourierCoeff_finiteFourierTransform (f : ℤ →₀ ℂ) (k : ℤ) :
    fourierCoeff (finiteFourierTransform f) k = f (-k) := by
  classical
  have hterm (n : ℤ) : Integrable
      (fun ξ : Torus => f n * fourier (T := (1 : ℝ)) (-n) ξ) torusHaar := by
    apply Integrable.of_bound (by fun_prop) ‖f n‖
    filter_upwards with ξ
    simp [fourier_apply, Circle.norm_coe]
  have hsum : finiteFourierTransform f =
      ∑ n ∈ f.support, (fun ξ : Torus =>
        f n * fourier (T := (1 : ℝ)) (-n) ξ) := by
    funext ξ
    simp [finiteFourierTransform]
  rw [hsum]
  have hcoeff := fourierCoeff.sum f.support
    (fun (n : ℤ) (ξ : Torus) => f n * fourier (T := (1 : ℝ)) (-n) ξ)
    (by intro n hn; exact hterm n)
  rw [hcoeff]
  simp only [Finset.sum_apply]
  rw [show (∑ n ∈ f.support,
      fourierCoeff (fun ξ : Torus => f n * fourier (T := (1 : ℝ)) (-n) ξ) k) =
      ∑ n ∈ f.support, if -n = k then f n else 0 by
        apply Finset.sum_congr rfl
        intro n hn
        rw [fourierCoeff.const_mul, fourierCoeff_fourier]
        simp [Pi.single_apply, eq_comm]]
  have hsumEval :
      (∑ n ∈ f.support, if -n = k then f n else 0) = f (-k) := by
    by_cases hk : -k ∈ f.support
    · rw [Finset.sum_eq_single (-k)]
      · simp
      · intro n hn hne
        have hcond : -n ≠ k := by
          intro h
          apply hne
          omega
        simp [hcond]
      · intro hnot
        exact (hnot hk).elim
    · have hfzero : f (-k) = 0 := by
        by_contra hnz
        exact hk (Finsupp.mem_support_iff.mpr hnz)
      rw [hfzero]
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hcond : -n = k
      · have hnk : n = -k := by omega
        exact (False.elim (hk (hnk ▸ hn)))
      · simp [hcond]
  simpa only [eq_comm] using hsumEval.symm

theorem fourierCoeff_finiteFourierTransformLp (f : ℤ →₀ ℂ) (k : ℤ) :
    fourierCoeff (finiteFourierTransformLp f) k = f (-k) := by
  unfold finiteFourierTransformLp
  rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp (finiteFourierTransform_memLp f))]
  exact fourierCoeff_finiteFourierTransform f k

/-- On finite inputs, the unitary transform is exactly the polynomial in the
approved negative-exponential convention. -/
theorem sequenceToCircleL2_finiteSequence (f : ℤ →₀ ℂ) :
    sequenceToCircleL2 (finiteSequenceL2 f) = finiteFourierTransformLp f := by
  apply (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr.injective
  have hleft : (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr
      (sequenceToCircleL2 (finiteSequenceL2 f)) = negIndexL2 (finiteSequenceL2 f) := by
    change (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr
        ((negIndexL2Equiv.trans
          (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr.symm)
          (finiteSequenceL2 f)) = _
    rw [LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [hleft]
  ext k
  change f (-k) =
    (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr (finiteFourierTransformLp f) k
  have hrepr : (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr
      (finiteFourierTransformLp f) k =
        fourierCoeff (finiteFourierTransformLp f) k := by
    exact fourierBasis_repr (finiteFourierTransformLp f) k
  rw [hrepr, fourierCoeff_finiteFourierTransformLp]

/-- Applying the inverse unitary Fourier transform recovers the reflected
Fourier coefficient at each integer. -/
theorem sequenceToCircleL2_symm_apply (g : Lp ℂ 2 torusHaar) (n : ℤ) :
    sequenceToCircleL2.symm g n =
      (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr g (-n) := by
  change negIndexL2
    ((@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr g) n = _
  rfl

/-- Multiplication by a Fourier monomial shifts the Fourier coefficient. -/
theorem fourierCoeff_mul_fourier_shift (g : Torus → ℂ) (a k : ℤ) :
    fourierCoeff (fun ξ => g ξ * fourier (T := (1 : ℝ)) a ξ) k =
      fourierCoeff g (k - a) := by
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul]
  rw [show -(k - a) = -k + a by omega, fourier_add]
  ring

/-- Fourier coefficients of the symbol times the finite Fourier polynomial,
expanded as the finite sum prescribed by Fourier inversion. -/
theorem fourierCoeff_torusSymbol_mul_finiteFourierTransform
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (f : ℤ →₀ ℂ) (k : ℤ) :
    fourierCoeff (fun ξ => torusSymbol h ξ * finiteFourierTransform f ξ) k =
      ∑ n ∈ f.support, f n * fourierCoeff (torusSymbol h) (k + n) := by
  classical
  let C : ℝ := max 0 (Classical.choose h.bounded)
  have hbound : ∀ ξ : Torus, ‖torusSymbol h ξ‖ ≤ C := by
    intro ξ
    exact torusSymbol_norm_le h (Classical.choose h.bounded)
      (Classical.choose_spec h.bounded) ξ |>.trans (le_max_right _ _)
  have hterm (n : ℤ) : Integrable
      (fun ξ : Torus => f n * (torusSymbol h ξ * fourier (T := (1 : ℝ)) (-n) ξ))
      torusHaar := by
    have hmeas : Measurable (fun ξ : Torus =>
        f n * (torusSymbol h ξ * fourier (T := (1 : ℝ)) (-n) ξ)) :=
      measurable_const.mul (h.measurable.mul (map_continuous (fourier (-n))).measurable)
    apply Integrable.of_bound hmeas.aestronglyMeasurable (‖f n‖ * C)
    filter_upwards with ξ
    have hfourier : ‖fourier (T := (1 : ℝ)) (-n) ξ‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    calc
      ‖f n * (torusSymbol h ξ * fourier (T := (1 : ℝ)) (-n) ξ)‖ =
          ‖f n‖ * (‖torusSymbol h ξ‖ *
            ‖fourier (T := (1 : ℝ)) (-n) ξ‖) := by simp
      _ ≤ ‖f n‖ * (C * 1) := by
        apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        simpa [hfourier] using
          (mul_le_mul_of_nonneg_right (hbound ξ) (by norm_num : 0 ≤ (1 : ℝ)))
      _ = ‖f n‖ * C := by ring
  have hfun : (fun ξ : Torus => torusSymbol h ξ * finiteFourierTransform f ξ) =
      ∑ n ∈ f.support, (fun ξ : Torus =>
        f n * (torusSymbol h ξ * fourier (T := (1 : ℝ)) (-n) ξ)) := by
    funext ξ
    simp only [finiteFourierTransform, Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hfun]
  have hcoeff := fourierCoeff.sum f.support
    (fun (n : ℤ) (ξ : Torus) =>
      f n * (torusSymbol h ξ * fourier (T := (1 : ℝ)) (-n) ξ))
    (by intro n hn; exact hterm n)
  rw [hcoeff]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fourierCoeff.const_mul, fourierCoeff_mul_fourier_shift]
  simp

/-- The `L²` Fourier multiplier agrees with finite convolution on finite
inputs, with the kernel sign fixed by the approved Fourier convention. -/
theorem TmL2_finite_convolution {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (f : ℤ →₀ ℂ) (x : ℤ) :
    TmL2 h (finiteSequenceL2 f) x =
      ∑ n ∈ f.support, kernelCoefficient (torusSymbol h) (x - n) * f n := by
  let g : Lp ℂ 2 torusHaar :=
    torusSymbolLp h • sequenceToCircleL2 (finiteSequenceL2 f)
  have hprod : (g : Torus → ℂ) =ᵐ[torusHaar]
      (fun ξ => torusSymbol h ξ * finiteFourierTransform f ξ) := by
    have hseq : (sequenceToCircleL2 (finiteSequenceL2 f) : Torus → ℂ) =ᵐ[torusHaar]
        finiteFourierTransform f := by
      rw [sequenceToCircleL2_finiteSequence]
      exact finiteFourierTransformLp_coeFn f
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (torusSymbolLp h) (sequenceToCircleL2 (finiteSequenceL2 f)),
      torusSymbolLp_coeFn h, hseq] with ξ hmul hsymbol hsequence
    calc
      g ξ = (torusSymbolLp h : Torus → ℂ) ξ *
          (sequenceToCircleL2 (finiteSequenceL2 f) : Torus → ℂ) ξ := by
            change (torusSymbolLp h • sequenceToCircleL2 (finiteSequenceL2 f)) ξ = _
            simpa only [Pi.smul_apply', smul_eq_mul] using hmul
      _ = torusSymbol h ξ * finiteFourierTransform f ξ := by rw [hsymbol, hsequence]
  have hrepr : TmL2 h (finiteSequenceL2 f) x =
      (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr g (-x) := by
    change sequenceToCircleL2.symm g x = _
    rw [sequenceToCircleL2_symm_apply]
  have hcoeff : (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr g (-x) =
      fourierCoeff (fun ξ => torusSymbol h ξ * finiteFourierTransform f ξ) (-x) := by
    calc
      (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr g (-x) = fourierCoeff g (-x) :=
        fourierBasis_repr g (-x)
      _ = fourierCoeff (fun ξ => torusSymbol h ξ * finiteFourierTransform f ξ) (-x) :=
        congrFun (fourierCoeff_congr_ae hprod) (-x)
  rw [hrepr, hcoeff, fourierCoeff_torusSymbol_mul_finiteFourierTransform]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [kernelCoefficient]
  rw [show -(x - n) = -x + n by omega]
  ring

end

end FractionalPrimes.Literature.Multiplier
