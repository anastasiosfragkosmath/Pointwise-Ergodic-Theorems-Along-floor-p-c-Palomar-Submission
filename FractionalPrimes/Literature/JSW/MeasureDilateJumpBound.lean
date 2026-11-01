module

public import FractionalPrimes.Literature.JSW.FiniteJumpLpAssembly
public import FractionalPrimes.Literature.JSW.DyadicFiniteSetJump
public import FractionalPrimes.Literature.JSW.MeasureJumpDecomposition

/-! Uniform jumps for actual measure dilates, with the approved 6S+6R+3J constant. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def jswDyadicJumpConstant (p : ℝ) : ℝ :=
  2*(littlewoodPaleyCp p)⁻¹*weakTypeFromOffSupportStrongConstant p 1 0

/-- `lj:measure-jump`: the exact source constant recipe, uniformly over all
finite naturally ordered scale sets and positive jump thresholds. -/
theorem measureDilateJumpBound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D p a : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D*|ξ|^(-β))
    (hβ : 0 < β) (hp : 1 < p) (ha : 0 < a) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (K : Finset ℤ) (t : ℝ), 0 < t →
      ∀ F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      let J := finiteJumpControl
        (fun k : {k : ℤ // k ∈ K} => jswConvolution
          (Measure.map (fun z : ℝ => jswTau a ha k.1*z) σ) (F : ℝ → ℂ)) t
      MemLp J (ENNReal.ofReal p) volume ∧
      lpNorm J (ENNReal.ofReal p) volume ≤
        (6*S+6*smoothDyadicSquareLpConstant p a ha+3*jswDyadicJumpConstant p)*‖F‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨S,hS,hNu⟩ := roughSquare_finite_bound_all hSupp hdecay (jswB_gt_one ha) hβ hp
  refine ⟨S,hS,fun K t ht F => ?_⟩
  classical
  let N := fun k : {k : ℤ // k ∈ K} => localizedSquareNuLpConvolution hSupp p (jswB a ha) hp k.1 F
  let R := fun k : {k : ℤ // k ∈ K} => smoothDyadicErrorLpOperator hSupp hp
    (jswTau a ha k.1) (jswM a ha k.1) F
  let E := fun k : {k : ℤ // k ∈ K} => dyadicAverage (jswM a ha k.1) (F : ℝ → ℂ)
  let V₁ : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K} :=
    fun x => WithLp.toLp 2 (fun k => (N k : ℝ → ℂ) x)
  let V₂ : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K} :=
    fun x => WithLp.toLp 2 (fun k => (R k : ℝ → ℂ) x)
  let Z := fun k x => V₁ x k+V₂ x k+E k x
  let SigmaF := fun k : {k : ℤ // k ∈ K} => jswConvolution
    (Measure.map (fun z : ℝ => jswTau a ha k.1*z) σ) (F : ℝ → ℂ)
  have hv₁ : MemLp V₁ (ENNReal.ofReal p) volume := MemLp.of_eval_piLp (fun k => Lp.memLp (N k))
  have hv₂ : MemLp V₂ (ENNReal.ofReal p) volume := MemLp.of_eval_piLp (fun k => Lp.memLp (R k))
  have hEm (k : {k : ℤ // k ∈ K}) : Measurable (E k) := measurable_dyadicAverage _ _
  have hEp (k : {k : ℤ // k ∈ K}) : MemLp (E k) (ENNReal.ofReal p) volume :=
    (Lp.memLp (dyadicAverageLpCLM hp (jswM a ha k.1) F)).ae_eq
      (dyadicAverageLpCLM_coeFn hp (jswM a ha k.1) F)
  have hZm (k : {k : ℤ // k ∈ K}) : Measurable (Z k) :=
    (((Lp.stronglyMeasurable (N k)).measurable).add
      (Lp.stronglyMeasurable (R k)).measurable).add (hEm k)
  have hZp (k : {k : ℤ // k ∈ K}) : MemLp (Z k) (ENNReal.ofReal p) volume :=
    ((Lp.memLp (N k)).add (Lp.memLp (R k))).add (hEp k)
  have hZjump := finiteJumpControl_memLp Z ht hZm hZp
  have hdecomp (k : {k : ℤ // k ∈ K}) : SigmaF k =ᵐ[volume] Z k :=
    sigmaDilateConvolution_ae_three_decomposition hSupp hp ha k.1 F
  have hjump : finiteJumpControl SigmaF t =ᵐ[volume] finiteJumpControl Z t := by
    filter_upwards [ae_all_iff.mpr hdecomp] with x hx
    have heq : (fun k => SigmaF k x) = fun k => Z k x := funext hx
    unfold finiteJumpControl
    rw [heq]
  have hmem : MemLp (finiteJumpControl SigmaF t) (ENNReal.ofReal p) volume :=
    hZjump.ae_eq hjump.symm
  refine ⟨hmem, ?_⟩
  have hn := congrArg ENNReal.toReal (eLpNorm_congr_ae hjump (p := ENNReal.ofReal p))
  change lpNorm (finiteJumpControl SigmaF t) (ENNReal.ofReal p) volume =
    lpNorm (finiteJumpControl Z t) (ENNReal.ofReal p) volume at hn
  change lpNorm (finiteJumpControl SigmaF t) (ENNReal.ofReal p) volume ≤ _
  rw [hn]
  have hthree := finiteJumpControl_three_Lp_bound V₁ V₂ E ht
    (ENNReal.one_le_ofReal.mpr hp.le) hv₁ hv₂ hEm hEp
  have hN : lpNorm V₁ (ENNReal.ofReal p) volume ≤ S*‖F‖ := hNu K F
  have hR : lpNorm V₂ (ENNReal.ofReal p) volume ≤ smoothDyadicSquareLpConstant p a ha*‖F‖ :=
    smoothDyadic_finite_output_vector_norm hSupp hp ha K F
  have hE : lpNorm (finiteJumpControl E (t/3)) (ENNReal.ofReal p) volume ≤
      jswDyadicJumpConstant p*‖F‖ := dyadicJumpBound_finiteSet hp ha K (by linarith) F
  nlinarith only [hthree,hN,hR,hE]

#print axioms measureDilateJumpBound
end
end FractionalPrimes.Literature.JSW
end
