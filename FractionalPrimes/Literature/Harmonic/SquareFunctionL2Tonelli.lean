module

public import FractionalPrimes.Literature.Harmonic.LocalizedSquareSummability

/-! A countable square-function identity in discrete `ℓ²`. -/

@[expose] public section

open scoped ENNReal BigOperators

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

set_option maxHeartbeats 1000000 in

/-- Tonelli identifies the discrete `ℓ²` norm of a countable square
function with the sum of the component `ℓ²` energies. -/
theorem lpSquareFunction_norm_sq
    {ι : Type*} (v : ι → lp (fun _ : ℤ => ℂ) 2)
    (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ∃ G : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ, G x = Real.sqrt (∑' i : ι, ‖v i x‖ ^ 2)) ∧
      ‖G‖ ^ 2 = ∑' i : ι, ‖v i‖ ^ 2 := by
  classical
  let term : ι → ℤ → ℝ := fun i x => ‖v i x‖ ^ 2
  have hcoord (i : ι) : Summable (term i) := by
    simpa [term, Real.rpow_two] using
      (lp.memℓp (v i)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hcoordNorm (i : ι) : (∑' x : ℤ, term i x) = ‖v i‖ ^ 2 := by
    have hnorm : (∑' x : ℤ, ‖v i x‖ ^ 2) ^ (1 / 2 : ℝ) = ‖v i‖ := by
      simpa only [show (2 : ℝ≥0∞).toReal = 2 by norm_num, Real.rpow_two] using
        (lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (v i)).symm
    have hsum0 : 0 ≤ ∑' x : ℤ, ‖v i x‖ ^ 2 :=
      tsum_nonneg fun x => sq_nonneg _
    dsimp [term]
    calc
      (∑' x : ℤ, ‖v i x‖ ^ 2) =
          ((∑' x : ℤ, ‖v i x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hsum0]
      _ = ‖v i‖ ^ 2 := by rw [hnorm]
  have houter : Summable (fun i : ι => ∑' x : ℤ, term i x) := by
    simpa only [hcoordNorm] using hv
  have hproduct : Summable (fun z : ι × ℤ => term z.1 z.2) := by
    apply (summable_prod_of_nonneg (fun z : ι × ℤ => sq_nonneg _)).2
    exact ⟨hcoord, houter⟩
  have hswap : Summable (fun z : ℤ × ι => term z.2 z.1) := by
    change Summable (fun z : ℤ × ι =>
      (fun w : ι × ℤ => term w.1 w.2) (Equiv.prodComm ℤ ι z))
    exact (Equiv.prodComm ℤ ι).summable_iff.mpr hproduct
  have hswapData :=
    (summable_prod_of_nonneg (f := fun z : ℤ × ι => term z.2 z.1)
      (fun z => sq_nonneg _)).1 hswap
  have hpoint (x : ℤ) : Summable (fun i : ι => term i x) := hswapData.1 x
  have hpointOuter : Summable (fun x : ℤ => ∑' i : ι, term i x) := hswapData.2
  let g : ℤ → ℝ := fun x => Real.sqrt (∑' i : ι, term i x)
  have hg0 (x : ℤ) : 0 ≤ g x := Real.sqrt_nonneg _
  have hgsq (x : ℤ) : g x ^ 2 = ∑' i : ι, term i x := by
    dsimp [g]
    exact Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg _)
  have hgSummable : Summable (fun x : ℤ => ‖g x‖ ^ 2) := by
    have hsq : Summable (fun x : ℤ => g x ^ 2) := by
      simpa only [hgsq] using hpointOuter
    simpa only [Real.norm_of_nonneg (hg0 _)] using hsq
  have hgMem : Memℓp g 2 := by
    apply memℓp_gen
    simpa only [show (2 : ℝ≥0∞).toReal = 2 by norm_num, Real.rpow_two]
      using hgSummable
  let G : lp (fun _ : ℤ => ℝ) 2 := ⟨g, hgMem⟩
  refine ⟨G, ?_, ?_⟩
  · intro x
    rfl
  · have hnorm : (∑' x : ℤ, ‖G x‖ ^ 2) ^ (1 / 2 : ℝ) = ‖G‖ := by
      simpa only [show (2 : ℝ≥0∞).toReal = 2 by norm_num, Real.rpow_two] using
        (lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) G).symm
    have hsum0 : 0 ≤ ∑' x : ℤ, ‖G x‖ ^ 2 :=
      tsum_nonneg fun x => sq_nonneg _
    calc
      ‖G‖ ^ 2 = ∑' x : ℤ, ‖G x‖ ^ 2 := by
        rw [← hnorm, ← Real.sqrt_eq_rpow, Real.sq_sqrt hsum0]
      _ = ∑' x : ℤ, ∑' i : ι, term i x := by
        apply tsum_congr
        intro x
        rw [show G x = g x by rfl, Real.norm_of_nonneg (hg0 x), hgsq]
      _ = ∑' i : ι, ∑' x : ℤ, term i x := by
        exact hproduct.tsum_comm
      _ = ∑' i : ι, ‖v i‖ ^ 2 := by
        apply tsum_congr
        intro i
        exact hcoordNorm i

#print axioms lpSquareFunction_norm_sq

end

end FractionalPrimes.Literature.Harmonic

end
