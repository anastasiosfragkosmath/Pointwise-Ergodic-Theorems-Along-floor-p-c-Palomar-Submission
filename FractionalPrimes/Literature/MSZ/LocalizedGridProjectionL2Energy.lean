module

public import FractionalPrimes.Literature.MSZ.AdmissibleData

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem mszEnergy_lp_cast_apply
    {E : Type*} [NormedAddCommGroup E] {p p' : ℝ≥0∞}
    (hpp' : p = p') (f : lp (fun _ : ℤ => E) p) (x : ℤ) :
    (hpp' ▸ f) x = f x := by
  cases hpp'
  rfl

private theorem mszEnergy_lp_norm_cast
    {E : Type*} [NormedAddCommGroup E] {p p' : ℝ≥0∞}
    (hpp' : p = p') (f : lp (fun _ : ℤ => E) p) :
    ‖hpp' ▸ f‖ = ‖f‖ := by
  cases hpp'
  rfl

/-- The first energy clause of `lm:shiftedResolution`: the squared `ℓ²`
norms of all projection outputs are summable, with the exact square-function
constant `P(2)`. This is the tail-decay input for shifted symmetric sums. -/
theorem mszLocalizedProjectionL2Energy
    (A : AdmissibleData) (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) :
    Summable (fun h : ℤ => ‖A.projectionsL2 h f‖ ^ 2) ∧
      (∑' h : ℤ, ‖A.projectionsL2 h f‖ ^ 2) ≤
        (A.P 2) ^ 2 * ‖f‖ ^ 2 := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hP₂ : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  let F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal (2 : ℝ)) := hP₂.symm ▸ f
  have hFseq : (F : ℤ → ℂ) = (f : ℤ → ℂ) := by
    funext x
    exact mszEnergy_lp_cast_apply hP₂.symm f x
  have hFnorm : ‖F‖ = ‖f‖ := by
    exact mszEnergy_lp_norm_cast hP₂.symm f
  obtain ⟨G, hGpoint, hGnorm⟩ :=
    A.square_function_bound 2 (by norm_num) F
  have hGpointRaw (x : ℤ) :
      G x = Real.sqrt (∑' h : ℤ,
        ‖A.projections h (f : ℤ → ℂ) x‖ ^ 2) := by
    calc
      G x = projectionSquareFunction A.projections F x := hGpoint x
      _ = Real.sqrt (∑' h : ℤ,
          ‖A.projections h (f : ℤ → ℂ) x‖ ^ 2) := by
        unfold projectionSquareFunction
        congr 1
        apply tsum_congr
        intro h
        rw [hFseq]
  have hGnonneg (x : ℤ) : 0 ≤ G x := by
    rw [hGpointRaw x]
    exact Real.sqrt_nonneg _
  have hPointSummable (x : ℤ) :
      Summable (fun h : ℤ =>
        ‖A.projectionsL2 h f x‖ ^ 2) := by
    have hsource := A.square_function_summable 2 (by norm_num) F x
    refine hsource.congr ?_
    intro h
    rw [A.projectionsL2_agree h f x, ← hFseq]
  have hGsquare (x : ℤ) :
      G x ^ 2 = ∑' h : ℤ, ‖A.projectionsL2 h f x‖ ^ 2 := by
    have hsumEq :
        (∑' h : ℤ, ‖A.projections h (f : ℤ → ℂ) x‖ ^ 2) =
          ∑' h : ℤ, ‖A.projectionsL2 h f x‖ ^ 2 := by
      apply tsum_congr
      intro h
      rw [← A.projectionsL2_agree h f x]
    calc
      G x ^ 2 =
          (Real.sqrt (∑' h : ℤ,
            ‖A.projections h (f : ℤ → ℂ) x‖ ^ 2)) ^ 2 := by
        rw [hGpointRaw x]
      _ = ∑' h : ℤ, ‖A.projections h (f : ℤ → ℂ) x‖ ^ 2 :=
        Real.sq_sqrt (tsum_nonneg fun h => sq_nonneg
          (‖A.projections h (f : ℤ → ℂ) x‖))
      _ = _ := hsumEq
  have hpToReal : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by norm_num
  have hGabsSummable : Summable (fun x : ℤ => ‖G x‖ ^ 2) := by
    simpa only [hpToReal, Real.rpow_two] using
      (lp.memℓp G).summable
        (by norm_num : 0 < (ENNReal.ofReal (2 : ℝ)).toReal)
  have hGsum : Summable (fun x : ℤ => G x ^ 2) := by
    refine hGabsSummable.congr ?_
    intro x
    rw [Real.norm_of_nonneg (hGnonneg x)]
  have hnormG :
      (∑' x : ℤ, ‖G x‖ ^ 2) ^ (1 / 2 : ℝ) = ‖G‖ := by
    simpa only [hpToReal, Real.rpow_two] using
      (lp.norm_eq_tsum_rpow
        (by norm_num : 0 < (ENNReal.ofReal (2 : ℝ)).toReal) G).symm
  have hsumGNonneg : 0 ≤ ∑' x : ℤ, ‖G x‖ ^ 2 :=
    tsum_nonneg fun x => sq_nonneg (‖G x‖)
  have hnormGSq : ‖G‖ ^ 2 = ∑' x : ℤ, G x ^ 2 := by
    calc
      ‖G‖ ^ 2 =
          ((∑' x : ℤ, ‖G x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [← hnormG]
      _ = ∑' x : ℤ, ‖G x‖ ^ 2 := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hsumGNonneg]
      _ = ∑' x : ℤ, G x ^ 2 := by
        apply tsum_congr
        intro x
        rw [Real.norm_of_nonneg (hGnonneg x)]
  have hnormProjection (h : ℤ) :
      ‖A.projectionsL2 h f‖ ^ 2 =
        ∑' x : ℤ, ‖A.projectionsL2 h f x‖ ^ 2 := by
    have hnorm :
        (∑' x : ℤ, ‖A.projectionsL2 h f x‖ ^ 2) ^ (1 / 2 : ℝ) =
          ‖A.projectionsL2 h f‖ := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.norm_eq_tsum_rpow
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
          (A.projectionsL2 h f)).symm
    have hsumNonneg :
        0 ≤ ∑' x : ℤ, ‖A.projectionsL2 h f x‖ ^ 2 :=
      tsum_nonneg fun x => sq_nonneg (‖A.projectionsL2 h f x‖)
    calc
      ‖A.projectionsL2 h f‖ ^ 2 =
          ((∑' x : ℤ, ‖A.projectionsL2 h f x‖ ^ 2) ^
            (1 / 2 : ℝ)) ^ 2 := by
        rw [← hnorm]
      _ = ∑' x : ℤ, ‖A.projectionsL2 h f x‖ ^ 2 := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hsumNonneg]
  have hfinitePointBound (s : Finset ℤ) (x : ℤ) :
      (∑ h ∈ s, ‖A.projectionsL2 h f x‖ ^ 2) ≤ G x ^ 2 := by
    calc
      _ ≤ ∑' h : ℤ, ‖A.projectionsL2 h f x‖ ^ 2 :=
        (hPointSummable x).sum_le_tsum s (fun h _ => sq_nonneg
          (‖A.projectionsL2 h f x‖))
      _ = G x ^ 2 := (hGsquare x).symm
  have hfiniteInnerSummable (s : Finset ℤ) :
      Summable (fun x : ℤ =>
        ∑ h ∈ s, ‖A.projectionsL2 h f x‖ ^ 2) := by
    exact hGsum.of_nonneg_of_le
      (fun x => Finset.sum_nonneg fun h _ => sq_nonneg
        (‖A.projectionsL2 h f x‖))
      (hfinitePointBound s)
  have hfiniteNormBound (s : Finset ℤ) :
      (∑ h ∈ s, ‖A.projectionsL2 h f‖ ^ 2) ≤ ‖G‖ ^ 2 := by
    calc
      _ = ∑ h ∈ s, ∑' x : ℤ,
            ‖A.projectionsL2 h f x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro h hh
        exact hnormProjection h
      _ = ∑' x : ℤ, ∑ h ∈ s,
            ‖A.projectionsL2 h f x‖ ^ 2 := by
        rw [Summable.tsum_finsetSum (fun h hh => by
          simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
            (lp.memℓp (A.projectionsL2 h f)).summable
            (by norm_num : 0 < (2 : ℝ≥0∞).toReal))]
      _ ≤ ∑' x : ℤ, G x ^ 2 :=
        (hfiniteInnerSummable s).tsum_le_tsum (hfinitePointBound s) hGsum
      _ = ‖G‖ ^ 2 := hnormGSq.symm
  have hProjectionSqSummable :
      Summable (fun h : ℤ => ‖A.projectionsL2 h f‖ ^ 2) :=
    summable_of_sum_le (fun h => sq_nonneg (‖A.projectionsL2 h f‖))
      hfiniteNormBound
  have hProjectionSqBound :
      (∑' h : ℤ, ‖A.projectionsL2 h f‖ ^ 2) ≤
        (A.P 2 * ‖f‖) ^ 2 := by
    calc
      _ ≤ ‖G‖ ^ 2 :=
        hProjectionSqSummable.tsum_le_of_sum_le hfiniteNormBound
      _ ≤ (A.P 2 * ‖f‖) ^ 2 := by
        have hP : 0 ≤ A.P 2 := A.P_nonneg 2 (by norm_num)
        have hGnorm' : ‖G‖ ≤ A.P 2 * ‖f‖ := by
          simpa [hFnorm] using hGnorm
        nlinarith [norm_nonneg G, norm_nonneg f, hP]
  refine ⟨hProjectionSqSummable, ?_⟩
  calc
    (∑' h : ℤ, ‖A.projectionsL2 h f‖ ^ 2) ≤
        (A.P 2 * ‖f‖) ^ 2 := hProjectionSqBound
    _ = (A.P 2) ^ 2 * ‖f‖ ^ 2 := by ring

end

end FractionalPrimes.Literature.MSZ

end
