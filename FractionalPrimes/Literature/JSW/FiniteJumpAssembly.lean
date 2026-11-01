module

public import FractionalPrimes.Literature.JSW.JumpAlgebra

/-! Exact finite jump reindexing and the source six-six-three assembly inequality. -/
@[expose] public section
open FractionalPrimes.Literature.Variation
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem finiteSeparatedJumpCount_comp_orderEmbedding_le
    {I J : Type*} [LinearOrder I] [Fintype I] [LinearOrder J] [Fintype J]
    (e : I ↪o J) (z : J → ℂ) (t : ℝ) :
    finiteSeparatedJumpCount (z ∘ e) t ≤ finiteSeparatedJumpCount z t := by
  obtain ⟨s,r,h⟩ := finiteSeparatedJumpCount_isAttained (z ∘ e) t
  apply le_finiteSeparatedJumpCount_of_family
  refine ⟨e ∘ s, e ∘ r, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro i
    exact e.strictMono (h.1.1 i)
  · intro i j hij
    exact e.monotone (h.1.2 i j hij)
  · exact h.2

theorem finiteSeparatedJumpCount_comp_orderIso
    {I J : Type*} [LinearOrder I] [Fintype I] [LinearOrder J] [Fintype J]
    (e : I ≃o J) (z : J → ℂ) (t : ℝ) :
    finiteSeparatedJumpCount (z ∘ e) t = finiteSeparatedJumpCount z t := by
  apply Nat.le_antisymm (finiteSeparatedJumpCount_comp_orderEmbedding_le e.toOrderEmbedding z t)
  have h := finiteSeparatedJumpCount_comp_orderEmbedding_le e.symm.toOrderEmbedding (z ∘ e) t
  change finiteSeparatedJumpCount (fun x => z (e (e.symm x))) t ≤
    finiteSeparatedJumpCount (fun x => z (e x)) t at h
  change finiteSeparatedJumpCount z t ≤ finiteSeparatedJumpCount (fun x => z (e x)) t
  simpa only [Function.comp_def, OrderIso.apply_symm_apply] using h

theorem jumpAlgebra_three_square_bound
    {I : Type*} [LinearOrder I] [Fintype I]
    (z₁ z₂ z₃ : I → ℂ) {t : ℝ} (ht : 0 < t) :
    t*Real.sqrt (finiteSeparatedJumpCount (fun k => z₁ k+z₂ k+z₃ k) t : ℝ) ≤
      6*Real.sqrt (∑ k, ‖z₁ k‖^2)+6*Real.sqrt (∑ k, ‖z₂ k‖^2)+
        3*((t/3)*Real.sqrt (finiteSeparatedJumpCount z₃ (t/3) : ℝ)) := by
  have hcount : (finiteSeparatedJumpCount (fun k => z₁ k+z₂ k+z₃ k) t : ℝ) ≤
      (finiteSeparatedJumpCount z₁ (t/3) : ℝ)+
      (finiteSeparatedJumpCount z₂ (t/3) : ℝ)+
      (finiteSeparatedJumpCount z₃ (t/3) : ℝ) := by
    exact_mod_cast jumpAlgebra_add_three z₁ z₂ z₃ ht
  have hroot : Real.sqrt (finiteSeparatedJumpCount (fun k => z₁ k+z₂ k+z₃ k) t : ℝ) ≤
      Real.sqrt (finiteSeparatedJumpCount z₁ (t/3) : ℝ)+
      Real.sqrt (finiteSeparatedJumpCount z₂ (t/3) : ℝ)+
      Real.sqrt (finiteSeparatedJumpCount z₃ (t/3) : ℝ) := by
    have h₀ := Real.sq_sqrt (show 0 ≤ (finiteSeparatedJumpCount (fun k => z₁ k+z₂ k+z₃ k) t : ℝ) by positivity)
    have h₁ := Real.sq_sqrt (show 0 ≤ (finiteSeparatedJumpCount z₁ (t/3) : ℝ) by positivity)
    have h₂ := Real.sq_sqrt (show 0 ≤ (finiteSeparatedJumpCount z₂ (t/3) : ℝ) by positivity)
    have h₃ := Real.sq_sqrt (show 0 ≤ (finiteSeparatedJumpCount z₃ (t/3) : ℝ) by positivity)
    have hn₀ := Real.sqrt_nonneg (finiteSeparatedJumpCount (fun k => z₁ k+z₂ k+z₃ k) t : ℝ)
    have hn₁ := Real.sqrt_nonneg (finiteSeparatedJumpCount z₁ (t/3) : ℝ)
    have hn₂ := Real.sqrt_nonneg (finiteSeparatedJumpCount z₂ (t/3) : ℝ)
    have hn₃ := Real.sqrt_nonneg (finiteSeparatedJumpCount z₃ (t/3) : ℝ)
    nlinarith [mul_nonneg hn₁ hn₂, mul_nonneg hn₁ hn₃, mul_nonneg hn₂ hn₃]
  have h₁ := jumpAlgebra_square_bound z₁ (threshold := t/3) (by linarith)
  have h₂ := jumpAlgebra_square_bound z₂ (threshold := t/3) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hroot ht.le]

#print axioms jumpAlgebra_three_square_bound
#print axioms finiteSeparatedJumpCount_comp_orderIso
end
end FractionalPrimes.Literature.JSW
end
