module

public import FractionalPrimes.Literature.JSW.PositiveRepresentativeTransfer

/-!
# Reflection transfer for finite-family positive maximal estimates

This keeps the conditional `q>1` maximal premise of `lj:positivity`
available for both a positive family and its reflected adjoint.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- A finite-family positive maximal majorant transfers to reflected
measures with exactly the same constant. -/
theorem finitePositiveMaximalBound_reflect
    {ι : Type*} [Fintype ι] {q : ℝ} (hq : 1 < q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsFiniteMeasure (μ i))
    (B : ℝ)
    (hMax : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          B * lpNorm g (ENNReal.ofReal q) volume) :
    ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i,
          (∫ y, g (x + y) ∂Measure.map Neg.neg (μ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          B * lpNorm g (ENNReal.ofReal q) volume := by
  intro g hg
  let g' : ℝ → ℝ := hg.aestronglyMeasurable.mk g
  have hgRep : g =ᵐ[volume] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hg'Strong : StronglyMeasurable g' :=
    hg.aestronglyMeasurable.stronglyMeasurable_mk
  have hg'Mem : MemLp g' (ENNReal.ofReal q) volume :=
    hg.congr_norm hg'Strong.aestronglyMeasurable (by
      filter_upwards [hgRep] with x hx
      simp [hx])
  let gr : ℝ → ℝ := fun x => g' (-x)
  have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hgrMem : MemLp gr (ENNReal.ofReal q) volume :=
    hg'Mem.comp_measurePreserving hneg
  obtain ⟨M, hMmem, hMnonneg, hMmajor, hMbound⟩ := hMax gr hgrMem
  let Mr : ℝ → ℝ := fun x => M (-x)
  have hMrMem : MemLp Mr (ENNReal.ofReal q) volume :=
    hMmem.comp_measurePreserving hneg
  have hMmajorNeg : ∀ᵐ x ∂volume, ∀ i,
      (∫ y, gr (-x + y) ∂(μ i)) ≤ M (-x) := by
    have hmap : ∀ᵐ z ∂Measure.map (fun x : ℝ => -x) volume,
        ∀ i, (∫ y, gr (z + y) ∂(μ i)) ≤ M z := by
      rw [hneg.map_eq]
      exact hMmajor
    exact ae_of_ae_map (by fun_prop : AEMeasurable (fun x : ℝ => -x) volume) hmap
  have hMajor (i : ι) : ∀ᵐ x ∂volume,
      (∫ y, g (x + y) ∂Measure.map Neg.neg (μ i)) ≤ Mr x := by
    let μr : Measure ℝ := Measure.map Neg.neg (μ i)
    haveI : IsFiniteMeasure (μ i) := hμ i
    haveI : IsFiniteMeasure μr := by dsimp [μr]; infer_instance
    have hTransfer := integral_add_translation_congr_ae μr g g' hgRep
    filter_upwards [hTransfer, hMmajorNeg] with x hxTransfer hxMajor
    have hMap :
        (∫ y, g' (x + y) ∂μr) =
          ∫ y, g' (x + -y) ∂(μ i) := by
      exact MeasureTheory.integral_map (φ := Neg.neg)
        (f := fun y => g' (x + y)) (by fun_prop)
        ((hg'Strong.comp_measurable (by fun_prop)).aestronglyMeasurable)
    calc
      (∫ y, g (x + y) ∂μr) = ∫ y, g' (x + y) ∂μr := hxTransfer
      _ = ∫ y, gr (-x + y) ∂(μ i) := by
        rw [hMap]
        congr 1
        funext y
        simp [gr, show -(-x + y) = x + -y by ring]
      _ ≤ Mr x := hxMajor i
  refine ⟨Mr, hMrMem, fun x => hMnonneg (-x), ae_all_iff.mpr hMajor, ?_⟩
  have hMrNorm : lpNorm Mr (ENNReal.ofReal q) volume =
      lpNorm M (ENNReal.ofReal q) volume := by
    exact congrArg ENNReal.toReal
      (eLpNorm_comp_measurePreserving hMmem.aestronglyMeasurable hneg)
  have hGrNorm : lpNorm gr (ENNReal.ofReal q) volume =
      lpNorm g (ENNReal.ofReal q) volume := by
    have hnorm1 : eLpNorm gr (ENNReal.ofReal q) volume =
        eLpNorm g' (ENNReal.ofReal q) volume :=
      eLpNorm_comp_measurePreserving hg'Mem.aestronglyMeasurable hneg
    have hnorm2 : eLpNorm g' (ENNReal.ofReal q) volume =
        eLpNorm g (ENNReal.ofReal q) volume :=
      eLpNorm_congr_ae hgRep.symm
    exact congrArg ENNReal.toReal (hnorm1.trans hnorm2)
  rw [hMrNorm]
  simpa [hGrNorm] using hMbound

#print axioms finitePositiveMaximalBound_reflect

end

end FractionalPrimes.Literature.JSW

end
