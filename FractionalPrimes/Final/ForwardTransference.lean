module
public import FractionalPrimes.Final.ForwardMoments
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory
open FractionalPrimes.Literature.Ergodic
open FractionalPrimes.Literature.Variation
open scoped ENNReal NNReal
noncomputable section

theorem forward_intIcc_card (R : ℕ) :
    (Finset.Icc (-(R : ℤ)) 0).card = R + 1 := by
  rw [Int.card_Icc]
  omega

theorem transferForwardFiniteKernelVariation
    {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (S : System X) (p r : ℝ≥0∞) (hp1 : 1 ≤ p) (hpTop : p < ∞)
    (_hr1 : 1 ≤ r) (_hrTop : r < ∞)
    (K : I → ℤ →₀ ℂ) (hpos : ∀ i m, m ∈ (K i).support → 0 ≤ m) (C : NNReal)
    (hdisc : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p r K g ≤
        (C : ℝ≥0∞) * extendedLpNorm (Measure.count : Measure ℤ) p (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (hf : MemLp f p S.μ) :
    extendedLpNorm S.μ p (forwardKernelVariation S r.toReal K f) ≤
      (C : ℝ≥0∞) * eLpNorm f p S.μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hptop : p ≠ ∞ := ne_of_lt hpTop
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  let L := finiteKernelSupportRadius K
  have hL : ∀ i m, m ∈ (K i).support → 0 ≤ m ∧ m ≤ (L : ℤ) := by
    intro i m hm
    refine ⟨hpos i m hm, ?_⟩
    have h := finiteKernel_mem_support_radius K i hm
    have habs : |m| ≤ (L : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact (abs_le.mp habs).2
  let V := forwardKernelVariation S r.toReal K f
  let A := ∫⁻ x, V x ^ p.toReal ∂S.μ
  let J := ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂S.μ
  let B := (C : ℝ≥0∞) ^ p.toReal
  have hJ_eq : J = eLpNorm f p S.μ ^ p.toReal := by
    calc
      J = extendedLpNorm S.μ p (fun x => ‖f x‖ₑ) ^ p.toReal := by
        dsimp [J]
        symm
        exact extendedLpNorm_rpow S.μ p (fun x => ‖f x‖ₑ) hp0 hptop
      _ = eLpNorm f p S.μ ^ p.toReal := by
        rw [extendedLpNorm_eq_eLpNorm S.μ p f hp0 hptop hf.aestronglyMeasurable]
  have hJne : J ≠ ∞ := by
    rw [hJ_eq]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hf.eLpNorm_ne_top
  have hBne : B ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  have hAne : A ≠ ∞ := by
    by_contra hAeq
    have hsmall := forwardKernelVariation_moment_scaled S p r K
      (C : ℝ≥0∞) hp1 hpTop hdisc f hf.aestronglyMeasurable 1 L hL
    have hlefttop :
        ((Finset.Icc (-((1 : ℕ) : ℤ)) 0).card : ℝ≥0∞) * A = ∞ := by
      simp [hAeq]
    have hrhsne : B *
        ((Finset.Icc (-((1 + L : ℕ) : ℤ)) 0).card * J) ≠ ∞ := by
      exact ENNReal.mul_ne_top hBne (ENNReal.mul_ne_top ENNReal.coe_ne_top hJne)
    rw [hlefttop] at hsmall
    exact (not_le_of_gt (lt_top_iff_ne_top.mpr hrhsne)) hsmall
  have hscaledReal (R : ℕ) :
      ((R : ℝ) + 1) * A.toReal ≤
        B.toReal * ((((R + L : ℕ) : ℝ) + 1) * J.toReal) := by
    have hraw := forwardKernelVariation_moment_scaled S p r K
      (C : ℝ≥0∞) hp1 hpTop hdisc f hf.aestronglyMeasurable R L hL
    rw [forward_intIcc_card R,
      forward_intIcc_card (R + L)] at hraw
    have hrhsne : B * (((R + L + 1 : ℕ) : ℝ≥0∞) * J) ≠ ∞ := by
      exact ENNReal.mul_ne_top hBne (ENNReal.mul_ne_top ENNReal.coe_ne_top hJne)
    have hreal := ENNReal.toReal_mono hrhsne hraw
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
    have hcardL :
        ((R + 1 : ℕ) : ℝ) = (R : ℝ) + 1 := by push_cast; ring
    have hcardR :
        ((R + L + 1 : ℕ) : ℝ) =
          ((R + L : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcardL, hcardR] at hreal
    exact hreal
  have htargetMoment : A ≤ B * J := by
    by_contra hnot
    have hBJne : B * J ≠ ∞ := ENNReal.mul_ne_top hBne hJne
    have hlt : B * J < A := lt_of_not_ge hnot
    let Δ : ℝ := A.toReal - (B * J).toReal
    have hgap : 0 < A.toReal - (B * J).toReal := by
      have hltReal := (ENNReal.toReal_lt_toReal hBJne hAne).2 hlt
      linarith
    let D : ℝ := B.toReal * J.toReal
    have hD : D = (B * J).toReal := by
      simp [D, ENNReal.toReal_mul]
    let cutoff : ℝ := (L : ℝ) * D / Δ
    obtain ⟨R, hR⟩ := exists_nat_gt cutoff
    have hR' : (L : ℝ) * D / Δ < (R : ℝ) := by simpa [cutoff] using hR
    have hfinal := hscaledReal R
    have hBD : B.toReal * J.toReal = D := by
      simp [D]
    have hfinal' :
        ((R : ℝ) + 1) * A.toReal ≤
          (((R + L : ℕ) : ℝ) + 1) * D := by
      calc
        _ ≤ B.toReal * ((((R + L : ℕ) : ℝ) + 1) * J.toReal) := hfinal
        _ = (((R + L : ℕ) : ℝ) + 1) * D := by rw [← hBD]; ring
    have hΔ : 0 < Δ := by simpa [Δ] using hgap
    have hfinal'' := hfinal'
    rw [hD] at hfinal''
    push_cast at hfinal''
    have hcontr : ((R : ℝ) + 1) * Δ ≤ (L : ℝ) * D := by
      dsimp [Δ]
      rw [hD]
      nlinarith [hfinal'']
    have hRmul : (L : ℝ) * D < (R : ℝ) * Δ :=
      (div_lt_iff₀ hΔ).mp hR'
    have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    have hcoeff : (R : ℝ) * Δ ≤ ((R : ℝ) + 1) * Δ := by
      nlinarith
    exact (not_lt_of_ge (le_trans hcoeff hcontr)) hRmul
  have hnormPow :
      extendedLpNorm S.μ p (forwardKernelVariation S r.toReal K f) ^ p.toReal ≤
        ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
    have hleft : extendedLpNorm S.μ p (forwardKernelVariation S r.toReal K f) ^ p.toReal = A := by
      simpa [V, A] using
        extendedLpNorm_rpow S.μ p V hp0 hptop
    rw [hleft]
    calc
      A ≤ B * J := htargetMoment
      _ = (B * eLpNorm f p S.μ ^ p.toReal) := by rw [hJ_eq]
      _ = ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
        simp [B, ENNReal.mul_rpow_of_nonneg]
  exact (ENNReal.rpow_le_rpow_iff hq).mp hnormPow


theorem transferForwardCountableKernelVariation
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (S : System X) (p r : ℝ≥0∞) (hp1 : 1 ≤ p) (hpTop : p < ∞)
    (hr1 : 1 ≤ r) (hrTop : r < ∞)
    (K : I → ℤ →₀ ℂ) (hpos : ∀ i m, m ∈ (K i).support → 0 ≤ m) (C : NNReal)
    (Exh : Set.FiniteExhaustion (Set.univ : Set I))
    (hdisc : ∀ N : ℕ, ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p r
          (fun i : Exh N => K i.1) g ≤
        (C : ℝ≥0∞) * extendedLpNorm (Measure.count : Measure ℤ) p
          (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (hf : MemLp f p S.μ) :
    extendedLpNorm S.μ p
        (forwardKernelVariation S r.toReal K f) ≤
      (C : ℝ≥0∞) * eLpNorm f p S.μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hptop : p ≠ ∞ := ne_of_lt hpTop
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  let F : I → X → ℂ := fun i => forwardKernelOperator S (K i) f
  have hF : ∀ i, AEMeasurable (F i) S.μ := by
    intro i
    exact aemeasurable_forwardKernelOperator S (K i) f hf.aestronglyMeasurable
  have hmoment := lintegral_orderedRVariationFun_rpow_eq_iSup_trunc_ae
    Exh S.μ r.toReal p.toReal hq F hF
  have hN (N : ℕ) :
      extendedLpNorm S.μ p (orderedRVariationTruncFun Exh r.toReal F N) ≤
        (C : ℝ≥0∞) * eLpNorm f p S.μ := by
    letI : Fintype (Exh N) := Fintype.ofFinite (Exh N)
    let KN : (Exh N) → ℤ →₀ ℂ := fun i => K i.1
    have hfinite := transferForwardFiniteKernelVariation S p r hp1 hpTop hr1 hrTop
      KN (fun i m hm => hpos i.val m hm) C (by
        intro g hg
        exact hdisc N g hg) f hf
    have hvariation :
        forwardKernelVariation S r.toReal KN f =
          orderedRVariationTruncFun Exh r.toReal F N := by
      funext x
      change orderedRVariation r.toReal (fun i : Exh N => F i x) = _
      rw [← orderedRVariationTrunc_eq_subtype Exh r.toReal (fun i => F i x) N]
      rfl
    change extendedLpNorm S.μ p (forwardKernelVariation S r.toReal KN f) ≤ _ at hfinite
    rw [hvariation] at hfinite
    exact hfinite
  have hmomentBound :
      (⨆ N : ℕ,
        ∫⁻ x, (orderedRVariationTruncFun Exh r.toReal F N x) ^ p.toReal ∂S.μ) ≤
        ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
    apply iSup_le
    intro N
    have hpow := ENNReal.rpow_le_rpow (hN N) hq.le
    have hnormEq := extendedLpNorm_rpow S.μ p
      (orderedRVariationTruncFun Exh r.toReal F N) hp0 hptop
    simpa only [hnormEq] using hpow
  have hfullMoment :
      ∫⁻ x, (forwardKernelVariation S r.toReal K f x) ^ p.toReal ∂S.μ ≤
        ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
    have hfull :
        forwardKernelVariation S r.toReal K f = orderedRVariationFun r.toReal F := by
      funext x
      rfl
    rw [hfull, hmoment]
    exact hmomentBound
  have hnormPow :
      extendedLpNorm S.μ p (forwardKernelVariation S r.toReal K f) ^ p.toReal ≤
        ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
    rw [extendedLpNorm_rpow S.μ p _ hp0 hptop]
    exact hfullMoment
  exact (ENNReal.rpow_le_rpow_iff hq).mp hnormPow

#print axioms transferForwardCountableKernelVariation
#print axioms transferForwardFiniteKernelVariation
end
end FractionalPrimes.Final
