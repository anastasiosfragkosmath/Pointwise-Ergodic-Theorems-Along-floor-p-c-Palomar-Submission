module

public import FractionalPrimes.Literature.JSW.FiniteJumpAssembly
public import FractionalPrimes.Literature.JSW.FiniteVectorLpAssembly

/-! Measurable finite jump controls and the exact source Lp six-six-three estimate. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
open FractionalPrimes.Literature.Variation
namespace FractionalPrimes.Literature.JSW
noncomputable section

def finiteJumpControl {I : Type*} [LinearOrder I] [Fintype I]
    (F : I → ℝ → ℂ) (t x : ℝ) : ℝ :=
  t*Real.sqrt (finiteSeparatedJumpCount (fun i => F i x) t : ℝ)

theorem finiteJumpControl_measurable
    {I : Type*} [LinearOrder I] [Fintype I]
    (F : I → ℝ → ℂ) (t : ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (finiteJumpControl F t) := by
  have hm := (measurable_separatedJumpCount F t hF).ennreal_toReal
  have hc : Measurable (fun x => (finiteSeparatedJumpCount (fun i => F i x) t : ℝ)) := by
    simpa only [separatedJumpCount_eq_finiteSeparatedJumpCount, ENNReal.toReal_natCast] using hm
  exact measurable_const.mul (Real.continuous_sqrt.measurable.comp hc)

theorem finiteJumpControl_nonneg
    {I : Type*} [LinearOrder I] [Fintype I]
    (F : I → ℝ → ℂ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    0 ≤ finiteJumpControl F t x := mul_nonneg ht (Real.sqrt_nonneg _)

theorem finiteJumpControl_memLp
    {I : Type*} [LinearOrder I] [Fintype I]
    (F : I → ℝ → ℂ) {t : ℝ} (ht : 0 < t) {p : ℝ≥0∞}
    (hF : ∀ i, Measurable (F i)) (hf : ∀ i, MemLp (F i) p volume) :
    MemLp (finiteJumpControl F t) p volume := by
  let V : ℝ → EuclideanSpace ℂ I := fun x => WithLp.toLp 2 (fun i => F i x)
  have hV : MemLp V p volume := MemLp.of_eval_piLp hf
  have hmajor : MemLp (fun x => 2*‖V x‖) p volume := hV.norm.const_mul 2
  apply hmajor.mono' (finiteJumpControl_measurable F t hF).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (finiteJumpControl_nonneg F ht.le x)]
  change t*Real.sqrt (finiteSeparatedJumpCount (fun i => F i x) t : ℝ) ≤ 2*‖V x‖
  rw [PiLp.norm_eq_of_L2]
  exact jumpAlgebra_square_bound _ ht

theorem finiteJumpControl_three_Lp_bound
    {I : Type*} [LinearOrder I] [Fintype I]
    (V₁ V₂ : ℝ → EuclideanSpace ℂ I) (F₃ : I → ℝ → ℂ)
    {t : ℝ} (ht : 0 < t) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf₁ : MemLp V₁ p volume) (hf₂ : MemLp V₂ p volume)
    (hF₃ : ∀ i, Measurable (F₃ i)) (hf₃ : ∀ i, MemLp (F₃ i) p volume) :
    lpNorm (finiteJumpControl (fun i x => V₁ x i+V₂ x i+F₃ i x) t) p volume ≤
      6*lpNorm V₁ p volume+6*lpNorm V₂ p volume+
      3*lpNorm (finiteJumpControl F₃ (t/3)) p volume := by
  have hv₁ : MemLp V₁ p volume := hf₁
  have hv₂ : MemLp V₂ p volume := hf₂
  let J := finiteJumpControl F₃ (t/3)
  have hj : MemLp J p volume := finiteJumpControl_memLp F₃ (by linarith) hF₃ hf₃
  have h₁ : MemLp (fun x => 6*‖V₁ x‖) p volume := hv₁.norm.const_mul 6
  have h₂ : MemLp (fun x => 6*‖V₂ x‖) p volume := hv₂.norm.const_mul 6
  have h₃ : MemLp (fun x => 3*J x) p volume := hj.const_mul 3
  have hM : MemLp (fun x => 6*‖V₁ x‖+6*‖V₂ x‖+3*J x) p volume := (h₁.add h₂).add h₃
  have hpoint (x : ℝ) : ‖finiteJumpControl (fun i x => V₁ x i+V₂ x i+F₃ i x) t x‖ ≤
      6*‖V₁ x‖+6*‖V₂ x‖+3*J x := by
    rw [Real.norm_of_nonneg (finiteJumpControl_nonneg _ ht.le x),
      PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    exact jumpAlgebra_three_square_bound _ _ _ ht
  let A : ℝ → ℝ := fun x => 6*‖V₁ x‖
  let B : ℝ → ℝ := fun x => 6*‖V₂ x‖
  let D : ℝ → ℝ := fun x => 3*J x
  have hdom : lpNorm (finiteJumpControl (fun i x => V₁ x i+V₂ x i+F₃ i x) t) p volume ≤
      lpNorm (A+B+D) p volume :=
    lpNorm_mono_real (f := finiteJumpControl (fun i x => V₁ x i+V₂ x i+F₃ i x) t)
      (g := A+B+D) hM hpoint
  have hadd₁ : lpNorm (A+B+D) p volume ≤ lpNorm (A+B) p volume+lpNorm D p volume :=
    lpNorm_add_le (f := A+B) (g := D) (h₁.add h₂) hp
  have hadd₂ : lpNorm (A+B) p volume ≤ lpNorm A p volume+lpNorm B p volume :=
    lpNorm_add_le (f := A) (g := B) h₁ hp
  have hnA : lpNorm A p volume = 6*lpNorm V₁ p volume := by
    simpa only [A, Nat.cast_ofNat, lpNorm_norm hv₁.aestronglyMeasurable] using
      lpNorm_fun_natCast_mul 6 (fun x => ‖V₁ x‖) p volume
  have hnB : lpNorm B p volume = 6*lpNorm V₂ p volume := by
    simpa only [B, Nat.cast_ofNat, lpNorm_norm hv₂.aestronglyMeasurable] using
      lpNorm_fun_natCast_mul 6 (fun x => ‖V₂ x‖) p volume
  have hnD : lpNorm D p volume = 3*lpNorm J p volume := by
    simpa only [D, Nat.cast_ofNat] using lpNorm_fun_natCast_mul 3 J p volume
  have ht := hdom.trans (hadd₁.trans (add_le_add hadd₂ (le_refl (lpNorm D p volume))))

  rw [hnA,hnB,hnD] at ht
  exact ht

#print axioms finiteJumpControl_three_Lp_bound
#print axioms finiteJumpControl_memLp
end
end FractionalPrimes.Literature.JSW
end
