module

public import FractionalPrimes.Literature.JSW.FiniteJumpAssembly
public import FractionalPrimes.Literature.JSW.DyadicMartingaleJumpAssembly

/-! The checked dyadic jump bound on the source's naturally ordered finite scale sets. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
open FractionalPrimes.Literature.Variation
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem jswM_monotone {a : ℝ} (ha : 0 < a) : Monotone (jswM a ha) := by
  intro i j hij
  apply Int.floor_mono
  exact mul_le_mul_of_nonneg_left (Int.cast_le.mpr hij) ha.le

theorem dyadicJumpBound_finiteSet
    {p : ℝ} (hp : 1 < p) {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    {t : ℝ} (ht : 0 < t) (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => t*Real.sqrt (finiteSeparatedJumpCount
      (fun k : {k : ℤ // k ∈ K} => dyadicAverage (jswM a ha k.1) (F : ℝ → ℂ) x) t : ℝ))
      (ENNReal.ofReal p) volume ≤
      (2*(littlewoodPaleyCp p)⁻¹*weakTypeFromOffSupportStrongConstant p 1 0)*‖F‖ := by
  classical
  let e := K.orderIsoOfFin rfl
  let s : Fin K.card → ℤ := fun i => jswM a ha (e i).1
  have hs : Monotone s := by
    intro i j hij
    exact jswM_monotone ha (e.monotone hij)
  have h := dyadicJumpBound hp s (Or.inl hs) t ht F
  have hc (x : ℝ) : finiteSeparatedJumpCount
      (fun i : Fin K.card => dyadicAverage (s i) (F : ℝ → ℂ) x) t =
      finiteSeparatedJumpCount
        (fun k : {k : ℤ // k ∈ K} => dyadicAverage (jswM a ha k.1) (F : ℝ → ℂ) x) t :=
    finiteSeparatedJumpCount_comp_orderIso e
      (fun k : {k : ℤ // k ∈ K} => dyadicAverage (jswM a ha k.1) (F : ℝ → ℂ) x) t
  simp_rw [hc] at h
  simpa only [mul_assoc] using h

#print axioms dyadicJumpBound_finiteSet
end
end FractionalPrimes.Literature.JSW
end
