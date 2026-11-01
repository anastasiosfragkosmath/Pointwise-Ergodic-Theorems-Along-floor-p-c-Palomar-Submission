module

public import FractionalPrimes.Literature.Ergodic.LogarithmicPerturbation

/-!
# Logarithmic perturbation under bounded-difference hypotheses

The source's linear operators need not themselves be continuous. The
bounded differences are represented by continuous linear maps. Centering
at `Q_1` supplies continuous families without changing homogeneous
variation, so the continuous-family theorem applies with exactly the
approved hypotheses.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The next positive averaging scale. -/
def perturbationSuccessorScale (N : Scale) : Scale := ⟨N.1 + 1, by omega⟩

/-- The continuous family obtained by summing only bounded consecutive
differences. Its first member is zero. -/
def perturbationCenteredContinuousFamily {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)]
    (I : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (N : Scale) : IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p :=
  ∑ k ∈ Finset.range (N.1 - 1), I ⟨k + 1, by omega⟩

/-- Finite telescoping identifies the bounded centered family with the
original linear family minus its possibly unbounded first member. -/
theorem perturbationCenteredContinuousFamily_toLinearMap
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (Q : Scale → IntegerSequenceLp p →ₗ[ℂ] IntegerSequenceLp p)
    (I : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (hI : ∀ N : Scale, (I N).toLinearMap = Q (perturbationSuccessorScale N) - Q N)
    (N : Scale) :
    (perturbationCenteredContinuousFamily I N).toLinearMap =
      Q N - Q ⟨1, by omega⟩ := by
  have htel (k : ℕ) :
      (∑ j ∈ Finset.range k, I ⟨j + 1, by omega⟩).toLinearMap =
        Q ⟨k + 1, by omega⟩ - Q ⟨1, by omega⟩ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      change (∑ j ∈ Finset.range k, I ⟨j + 1, by omega⟩).toLinearMap +
        (I ⟨k + 1, by omega⟩).toLinearMap = _
      rw [ih, hI]
      have hnext : perturbationSuccessorScale ⟨k + 1, by omega⟩ =
          (⟨k + 1 + 1, by omega⟩ : Scale) := rfl
      rw [hnext]
      abel
  have hN : (⟨N.1 - 1 + 1, by omega⟩ : Scale) = N := by
    apply Subtype.ext
    change N.1 - 1 + 1 = N.1
    have := N.2
    omega
  simpa only [perturbationCenteredContinuousFamily, hN] using htel (N.1 - 1)

/-- Homogeneous variation is invariant under subtracting the same vector
at every scale. This needs no boundedness or exponent hypothesis. -/
theorem rVariation_sub_common_constant
    {E : Type*} [NormedAddCommGroup E] (r : ℝ) (u : Scale → E) (c : E) :
    rVariation r (fun N => u N - c) = rVariation r u := by
  rw [rVariation_eq, rVariation_eq]
  congr 1
  funext length
  congr 1
  funext chain
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have heq : (u (chain.index i.succ) - c) -
      (u (chain.index i.castSucc) - c) =
        u (chain.index i.succ) - u (chain.index i.castSucc) := by abel
  rw [heq]

/-- Pointwise family form of common-translation invariance. -/
theorem rVariationFun_sub_common_constant
    {X E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (F : Scale → X → E) (c : X → E) :
    rVariationFun r (fun N x => F N x - c x) = rVariationFun r F := by
  funext x
  exact rVariation_sub_common_constant r (fun N => F N x) (c x)

/-- The exact bounded-difference version of `er:perturbation`.

`E` and `I` are the continuous representatives of the bounded errors and
consecutive increments appearing in the source hypotheses. No continuity
is imposed on the individual linear maps `Q N` or `P N`. -/
theorem variationOfLogarithmicPerturbation {p r : ℝ}
    (hp : 1 < p) (hr2 : 2 ≤ r) [Fact (1 ≤ ENNReal.ofReal p)]
    (Q P : Scale → IntegerSequenceLp p →ₗ[ℂ] IntegerSequenceLp p)
    (E I : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (hE : ∀ N : Scale, (E N).toLinearMap = Q N - P N)
    (hI : ∀ N : Scale, (I N).toLinearMap = Q (perturbationSuccessorScale N) - Q N)
    (CP C0 : ℝ)
    (hP : ∀ f : IntegerSequenceLp p,
      eLpNorm (rVariationFun r (fun N => (P N f : ℤ → ℂ)))
        (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal CP * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count)
    (hdecay : ∀ D : ℝ, 0 < D →
      ∃ C_D : ℝ, ∀ N : Scale, 3 ≤ N.1 →
        ‖E N‖ ≤ C_D * Real.rpow (Real.log (N.1 : ℝ)) (-D))
    (hinc : ∀ N : Scale,
      ‖I N‖ ≤ C0 * (Real.log (2 * (N.1 : ℝ)) / ((N.1 : ℝ) + 1))) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : IntegerSequenceLp p,
        eLpNorm (rVariationFun r (fun N => (Q N f : ℤ → ℂ)))
          (ENNReal.ofReal p) Measure.count ≤
          C * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  let Q' : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p :=
    perturbationCenteredContinuousFamily I
  let P' : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p :=
    fun N => Q' N - E N
  have hQcenter (N : Scale) (f : IntegerSequenceLp p) :
      Q' N f = Q N f - Q ⟨1, by omega⟩ f := by
    have heq := LinearMap.congr_fun
      (perturbationCenteredContinuousFamily_toLinearMap Q I hI N) f
    exact heq
  have hPcenter (N : Scale) (f : IntegerSequenceLp p) :
      P' N f = P N f - Q ⟨1, by omega⟩ f := by
    have hEf : E N f = Q N f - P N f := LinearMap.congr_fun (hE N) f
    change Q' N f - E N f = _
    rw [hQcenter, hEf]
    abel
  have hPvariation (f : IntegerSequenceLp p) :
      rVariationFun r (fun N => (P' N f : ℤ → ℂ)) =
        rVariationFun r (fun N => (P N f : ℤ → ℂ)) := by
    have hfunctions : (fun N => (P' N f : ℤ → ℂ)) =
        (fun N x => (P N f : ℤ → ℂ) x - (Q ⟨1, by omega⟩ f : ℤ → ℂ) x) := by
      funext N x
      rw [hPcenter]
      rfl
    rw [hfunctions]
    exact rVariationFun_sub_common_constant r (fun N => (P N f : ℤ → ℂ))
      (Q ⟨1, by omega⟩ f : ℤ → ℂ)
  have hQvariation (f : IntegerSequenceLp p) :
      rVariationFun r (fun N => (Q' N f : ℤ → ℂ)) =
        rVariationFun r (fun N => (Q N f : ℤ → ℂ)) := by
    have hfunctions : (fun N => (Q' N f : ℤ → ℂ)) =
        (fun N x => (Q N f : ℤ → ℂ) x - (Q ⟨1, by omega⟩ f : ℤ → ℂ) x) := by
      funext N x
      rw [hQcenter]
      rfl
    rw [hfunctions]
    exact rVariationFun_sub_common_constant r (fun N => (Q N f : ℤ → ℂ))
      (Q ⟨1, by omega⟩ f : ℤ → ℂ)
  have herrors (N : Scale) : Q' N - P' N = E N := by
    dsimp [P']
    abel
  have hincrements (N : Scale) : Q' (perturbationSuccessorScale N) - Q' N = I N := by
    apply ContinuousLinearMap.ext
    intro f
    change Q' (perturbationSuccessorScale N) f - Q' N f = I N f
    have hIf : I N f = Q (perturbationSuccessorScale N) f - Q N f :=
      LinearMap.congr_fun (hI N) f
    rw [hQcenter, hQcenter, hIf]
    abel
  have hP' : ∀ f : IntegerSequenceLp p,
      eLpNorm (rVariationFun r (fun N => (P' N f : ℤ → ℂ)))
        (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal CP * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    intro f
    rw [hPvariation]
    exact hP f
  have hdecay' : ∀ D : ℝ, 0 < D →
      ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ N : Scale, 3 ≤ N.1 →
        ‖Q' N - P' N‖ ≤ C_D * Real.rpow (Real.log (N.1 : ℝ)) (-D) := by
    intro D hD
    obtain ⟨CD, hCD⟩ := hdecay D hD
    refine ⟨max CD 0, le_max_right _ _, ?_⟩
    intro N hN
    rw [herrors]
    have hlog : 0 ≤ Real.log (N.1 : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N.1 by omega))
    exact (hCD N hN).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hlog _))
  have hinc' : ∀ (m : ℕ) (hm : 1 ≤ m),
      ‖Q' ⟨m + 1, by omega⟩ - Q' ⟨m, hm⟩‖ ≤
        C0 * (Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)) := by
    intro m hm
    have heq : (⟨m + 1, by omega⟩ : Scale) =
        perturbationSuccessorScale ⟨m, hm⟩ := rfl
    rw [heq, hincrements]
    exact hinc ⟨m, hm⟩
  have hPnormalized : ∀ f : IntegerSequenceLp p,
      eLpNorm (rVariationFun r (fun N => (P' N f : ℤ → ℂ)))
        (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (max CP 0) * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count := by
    intro f
    exact (hP' f).trans (mul_le_mul
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl (by simp) (by simp))
  have hincNormalized : ∀ (m : ℕ) (hm : 1 ≤ m),
      ‖Q' ⟨m + 1, by omega⟩ - Q' ⟨m, hm⟩‖ ≤
        max C0 0 * (Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)) := by
    intro m hm
    have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hweight : 0 ≤ Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1) :=
      div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
    exact (hinc' m hm).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hweight)
  obtain ⟨C, hC, hbound⟩ := variationOfLogarithmicPerturbation_continuous
    hp hr2 Q' P' (max CP 0) (max C0 0) (le_max_right _ _) (le_max_right _ _)
      hPnormalized hdecay' hincNormalized
  refine ⟨C, hC, ?_⟩
  intro f
  simpa only [hQvariation] using hbound f

end

end FractionalPrimes

#print axioms FractionalPrimes.perturbationCenteredContinuousFamily_toLinearMap
#print axioms FractionalPrimes.rVariation_sub_common_constant
#print axioms FractionalPrimes.variationOfLogarithmicPerturbation
