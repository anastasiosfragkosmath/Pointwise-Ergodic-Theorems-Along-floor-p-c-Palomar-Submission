module

public import FractionalPrimes.Literature.JSW.PositiveMaximalVectorAdapters
public import FractionalPrimes.Literature.JSW.PositiveMaximalSupFinite
public import FractionalPrimes.Literature.JSW.PositiveRepresentativeTransfer

/-!
# Source maximal adapters for the JSW positive vector estimate

This module connects the geometric-scale probability averages and the
smooth-density averages to the conditional maximal majorant in the finite
vector theorem.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

#print axioms initialSquare_reflectedScale_integral_eq_rawPositiveScale

private theorem lp_coeFn_finset_sup'_ae_source
    {ι : Type*} [DecidableEq ι] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → Lp ℝ p (volume : Measure ℝ)) :
    ((s.sup' hs f : Lp ℝ p (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume]
      fun x => s.sup' hs (fun i => fun y => f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hsn : s.Nonempty
      · have hcoe := Lp.coeFn_sup (f a) (s.sup' hsn f)
        have htail := ih hsn
        have hstep :
            ((f a ⊔ s.sup' hsn f : Lp ℝ p (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume]
              fun x => f a x ⊔ s.sup' hsn (fun i => fun y => f i y) x := by
          filter_upwards [hcoe, htail] with x hx₁ hx₂
          rw [hx₁]
          calc
            (((f a : Lp ℝ p (volume : Measure ℝ)) : ℝ → ℝ) ⊔
                ((s.sup' hsn f : Lp ℝ p (volume : Measure ℝ)) : ℝ → ℝ)) x =
                max (f a x) ((s.sup' hsn f : Lp ℝ p (volume : Measure ℝ)) x) := rfl
            _ = max (f a x) (s.sup' hsn (fun i => fun y => f i y) x) := by
              rw [hx₂]
        have hsEq : hs = Finset.insert_nonempty a s := Subsingleton.elim _ _
        subst hs
        rw [Finset.sup'_insert]
        rw [Finset.sup'_insert]
        exact hstep
      · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
        subst s
        have hsEq : hs = Finset.insert_nonempty a ∅ := Subsingleton.elim _ _
        subst hs
        simpa using (EventuallyEq.rfl :
          (fun x : ℝ => f a x) =ᵐ[volume] fun x => f a x)

/-- If an `L^q` input is represented by a measurable function, every source
scale average is bounded almost everywhere by the raw positive maximal
function. The proof first shows the extended scale supremum is finite a.e.
from uniform finite-window bounds. -/
theorem initialSquareSigmaRawPositiveScale_le_rawMax_ae_of_memLp
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β) (hq : 2 < q)
    [Fact (1 ≤ ENNReal.ofReal q)]
    (F : Lp ℂ (ENNReal.ofReal q) volume)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfm : MemLp f (ENNReal.ofReal q) volume)
    (hF : (F : ℝ → ℂ) =ᵐ[volume] f) :
    ∀ k : ℤ, initialSquareSigmaRawPositiveScale σ b k f ≤ᵐ[volume]
      fun x => initialSquareSigmaRawPositiveMaximal σ b f x := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal q
  let hp : P ≠ ∞ := ENNReal.ofReal_ne_top
  let s : ℕ → Finset ℤ := fun n => Finset.Icc (-(n : ℤ)) (n : ℤ)
  have hne (n : ℕ) : (s n).Nonempty := by
    refine ⟨0, ?_⟩
    simp [s]
  let S : ℕ → Lp ℝ P volume := fun n =>
    initialSquareSigmaFinitePositiveMaximalLp P hp σ b (s n) (hne n) F
  let fS : ℕ → ℝ → ℝ := fun n x => (S n : ℝ → ℝ) x
  let scale : ℤ → Lp ℝ P volume := fun k =>
    initialSquareSigmaPositiveConvolutionScaleLp q σ b k F
  have hscaleNonneg (k : ℤ) : 0 ≤ scale k := by
    dsimp [scale, initialSquareSigmaPositiveConvolutionScaleLp]
    letI : IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation :=
      initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
    exact initialSquare_lpPositiveConvolutionMap_nonneg
      hSupp hσ hb hq k F
  have hsSubset {n m : ℕ} (hnm : n ≤ m) : s n ⊆ s m := by
    intro k hk
    simp only [s, Finset.mem_Icc] at hk ⊢
    omega
  have hSmono : Monotone S := by
    intro n m hnm
    change (s n).sup' (hne n) (fun k => scale k) ≤
      (s m).sup' (hne m) (fun k => scale k)
    exact Finset.sup'_mono (f := fun k => scale k) (hsSubset hnm) (hne n)
  have hSnonneg (n : ℕ) : 0 ≤ S n := by
    change (0 : Lp ℝ P volume) ≤
      (s n).sup' (hne n) (fun k => scale k)
    rcases hne n with ⟨k₀, hk₀⟩
    exact (hscaleNonneg k₀).trans (Finset.le_sup' scale hk₀)
  have hfSmeas (n : ℕ) : Measurable (fS n) := by
    exact (Lp.stronglyMeasurable (S n)).measurable
  have hfSnonneg (n : ℕ) : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ fS n x := by
    change 0 ≤ᵐ[volume] (S n : ℝ → ℝ)
    exact (Lp.coeFn_nonneg (S n)).2 (hSnonneg n)
  have hfSmono (n : ℕ) : ∀ᵐ x ∂(volume : Measure ℝ), fS n x ≤ fS n.succ x := by
    have hstep : S n ≤ S n.succ := hSmono (Nat.le_succ n)
    change (S n : ℝ → ℝ) ≤ᵐ[volume] (S n.succ : ℝ → ℝ)
    exact (Lp.coeFn_le (S n) (S n.succ)).2 hstep
  let C : ℝ≥0∞ := ENNReal.ofReal
      (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
      eLpNorm (F : ℝ → ℂ) P volume
  have hCtop : C ≠ ∞ := by
    apply ne_of_lt
    dsimp [C]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp F).eLpNorm_lt_top
  have hfSbound (n : ℕ) : eLpNorm (fS n) P volume ≤ C := by
    have h := initialSquareSigmaFinitePositiveMaximalLp_bound
      hSupp hσ hb hβ hq (s n) (hne n) F
    simpa [fS, S, C, P] using h
  have hfiniteS := iSup_ofReal_lt_top_ae_of_uniform_eLpNorm
    (q := q) (by linarith : 0 < q) fS hfSmeas hfSnonneg hfSmono hCtop hfSbound
  have hfiniteRep (n : ℕ) :
      (S n : ℝ → ℝ) =ᵐ[volume]
        fun x => (s n).sup' (hne n) (fun k => scale k x) := by
    simpa [S, s, initialSquareSigmaFinitePositiveMaximalLp,
      lpFinitePositiveConvolutionSup, scale,
      initialSquareSigmaPositiveConvolutionScaleLp] using
      (lp_coeFn_finset_sup'_ae_source (s n) (hne n) scale)
  have hmapSup (n : ℕ) (x : ℝ) :
      ENNReal.ofReal ((s n).sup' (hne n) (fun k => scale k x)) =
        (s n).sup' (hne n) (fun k => ENNReal.ofReal (scale k x)) := by
    exact Finset.apply_sup'_eq_sup'_comp (hne n) ENNReal.ofReal
      (by intro u v; simp [ENNReal.ofReal_max])
  have hfiniteOfReal (n : ℕ) :
      (fun x => ENNReal.ofReal (fS n x)) =ᵐ[volume]
        fun x => (s n).sup' (hne n) (fun k => ENNReal.ofReal (scale k x)) := by
    filter_upwards [hfiniteRep n] with x hx
    change ENNReal.ofReal ((S n : ℝ → ℝ) x) = _
    rw [hx]
    exact hmapSup n x
  have hscaleSup : ∀ᵐ x ∂(volume : Measure ℝ),
      (⨆ n, ENNReal.ofReal (fS n x)) = ⨆ k : ℤ, ENNReal.ofReal (scale k x) := by
    filter_upwards [ae_all_iff.mpr hfiniteOfReal] with x hx
    apply le_antisymm
    · apply iSup_le
      intro n
      rw [hx n]
      apply Finset.sup'_le
      intro k hk
      exact le_iSup_of_le k le_rfl
    · apply iSup_le
      intro k
      have hk : k ∈ s k.natAbs := by
        cases k with
        | ofNat n => simp [s]
        | negSucc n => simp [s] <;> omega
      calc
        ENNReal.ofReal (scale k x) ≤
            (s k.natAbs).sup' (hne k.natAbs)
              (fun j => ENNReal.ofReal (scale j x)) :=
          Finset.le_sup' (fun j => ENNReal.ofReal (scale j x)) hk
        _ = ENNReal.ofReal (fS k.natAbs x) := (hx k.natAbs).symm
        _ ≤ ⨆ n, ENNReal.ofReal (fS n x) :=
          le_iSup_of_le k.natAbs le_rfl
  have hscaleRaw (k : ℤ) :
      (scale k : ℝ → ℝ) =ᵐ[volume]
        initialSquareSigmaRawPositiveScale σ b k f := by
    letI : IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation :=
      initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
    have h := initialSquare_lpPositiveConvolutionMap_ae_eq_rawScale_of_memLp
      (q := q) (σ := σ) (b := b) (by linarith : 1 < q) hb k f hf hfm F hF
    simpa [scale, initialSquareSigmaPositiveConvolutionScaleLp] using h
  have hscaleRawAll : ∀ᵐ x ∂(volume : Measure ℝ), ∀ k : ℤ,
      scale k x = initialSquareSigmaRawPositiveScale σ b k f x :=
    ae_all_iff.mpr hscaleRaw
  have hrawSupFinite : ∀ᵐ x ∂(volume : Measure ℝ),
      (⨆ k : ℤ,
        ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k f x)) < ∞ := by
    filter_upwards [hfiniteS, hscaleSup, hscaleRawAll] with x hfin hsup hraw
    have heq : (⨆ n, ENNReal.ofReal (fS n x)) =
        ⨆ k : ℤ, ENNReal.ofReal
          (initialSquareSigmaRawPositiveScale σ b k f x) := by
      rw [hsup]
      exact iSup_congr fun k => congrArg ENNReal.ofReal (hraw k)
    rw [← heq]
    exact hfin
  intro k
  filter_upwards [hrawSupFinite] with x hfinite
  have hscaleNonnegReal :
      0 ≤ initialSquareSigmaRawPositiveScale σ b k f x :=
    integral_nonneg_of_ae (ae_of_all _ fun y => norm_nonneg _)
  have hle := real_le_toReal_iSup_ofReal_of_lt_top
    (fun j : ℤ => initialSquareSigmaRawPositiveScale σ b j f x) k hfinite
  change initialSquareSigmaRawPositiveScale σ b k f x ≤
    (⨆ j : ℤ,
      ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b j f x)).toReal
  exact hle

#print axioms initialSquareSigmaRawPositiveScale_le_rawMax_ae_of_memLp

end

end FractionalPrimes.Literature.JSW

end
