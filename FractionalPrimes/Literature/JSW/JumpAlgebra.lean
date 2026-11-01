module

public import FractionalPrimes.Literature.JSW.Conventions
public import FractionalPrimes.Literature.Variation.FiniteJumpCount
import Mathlib.Data.Finset.Sort

/-!
# Square sequences and addition of jumps

This module formalizes the finite scalar-sequence jump algebra in
`lj:jump-algebra`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.JSW

open FractionalPrimes.Literature.Variation

noncomputable section

private theorem jumpAlgebra_sum_comp_le_of_strictMono
    {I : Type*} [LinearOrder I] [Fintype I]
    (f : I → ℝ) (hf : ∀ x, 0 ≤ f x) {n : ℕ} (s : Fin n → I)
    (hs : StrictMono s) :
    (∑ i : Fin n, f (s i)) ≤ ∑ x : I, f x := by
  classical
  let S : Finset I := Finset.univ.image s
  have hEq : (∑ i : Fin n, f (s i)) = ∑ x ∈ S, f x := by
    dsimp [S]
    exact (Finset.sum_image (f := f) (fun _ _ _ _ h => hs.injective h)).symm
  calc
    (∑ i : Fin n, f (s i)) = ∑ x ∈ S, f x := hEq
    _ ≤ ∑ x ∈ Finset.univ, f x :=
      Finset.sum_le_sum_of_subset_of_nonneg (by
        intro x hx
        exact Finset.mem_univ x) (by
        intro x hx hxS
        exact hf x)
    _ = ∑ x : I, f x := by simp

/-- A finite family of separated jumps is bounded by the square mass of its
sequence, with the endpoint multiplicity counted exactly twice. -/
private theorem jumpAlgebra_family_square_bound
    {I : Type*} [LinearOrder I] [Fintype I]
    (z : I → ℂ) (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    {n : ℕ} (s t : Fin n → I)
    (h : SeparatedJumpFamily z threshold s t) :
    (n : ℝ) * threshold ^ 2 ≤ 4 * ∑ k : I, ‖z k‖ ^ 2 := by
  classical
  have hs : StrictMono s := by
    intro i j hij
    exact lt_of_lt_of_le (h.1.1 i) (h.1.2 i j hij)
  have ht : StrictMono t := by
    intro i j hij
    exact lt_of_le_of_lt (h.1.2 i j hij) (h.1.1 j)
  have hinc : ∀ i : Fin n,
      threshold ^ 2 ≤ ‖z (t i) - z (s i)‖ ^ 2 := by
    intro i
    have hlt := h.2 i
    have hn := norm_nonneg (z (t i) - z (s i))
    nlinarith
  have hsumLower : (n : ℝ) * threshold ^ 2 ≤
      ∑ i : Fin n, ‖z (t i) - z (s i)‖ ^ 2 := by
    calc
      (n : ℝ) * threshold ^ 2 = ∑ i : Fin n, threshold ^ 2 := by simp
      _ ≤ ∑ i : Fin n, ‖z (t i) - z (s i)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hinc i
  have hincPoint : ∀ i : Fin n,
      ‖z (t i) - z (s i)‖ ^ 2 ≤
        2 * (‖z (t i)‖ ^ 2 + ‖z (s i)‖ ^ 2) := by
    intro i
    have htriangle := norm_sub_le (z (t i)) (z (s i))
    have hleft := norm_nonneg (z (t i) - z (s i))
    have hright := norm_nonneg (z (t i))
    have hright' := norm_nonneg (z (s i))
    nlinarith [sq_nonneg (‖z (t i)‖ - ‖z (s i)‖)]
  have hsumInc :
      (∑ i : Fin n, ‖z (t i) - z (s i)‖ ^ 2) ≤
        2 * ((∑ i : Fin n, ‖z (t i)‖ ^ 2) +
          (∑ i : Fin n, ‖z (s i)‖ ^ 2)) := by
    calc
      (∑ i : Fin n, ‖z (t i) - z (s i)‖ ^ 2) ≤
          ∑ i : Fin n, 2 * (‖z (t i)‖ ^ 2 + ‖z (s i)‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hincPoint i
      _ = 2 * ((∑ i : Fin n, ‖z (t i)‖ ^ 2) +
          (∑ i : Fin n, ‖z (s i)‖ ^ 2)) := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hsumT := jumpAlgebra_sum_comp_le_of_strictMono
    (f := fun k => ‖z k‖ ^ 2) (by intro k; positivity) t ht
  have hsumS := jumpAlgebra_sum_comp_le_of_strictMono
    (f := fun k => ‖z k‖ ^ 2) (by intro k; positivity) s hs
  have htotal :
      (∑ i : Fin n, ‖z (t i) - z (s i)‖ ^ 2) ≤
        4 * ∑ k : I, ‖z k‖ ^ 2 := by
    calc
      (∑ i : Fin n, ‖z (t i) - z (s i)‖ ^ 2) ≤
          2 * ((∑ i : Fin n, ‖z (t i)‖ ^ 2) +
            (∑ i : Fin n, ‖z (s i)‖ ^ 2)) := hsumInc
      _ ≤ 2 * ((∑ k : I, ‖z k‖ ^ 2) +
            (∑ k : I, ‖z k‖ ^ 2)) := by gcongr
      _ = 4 * ∑ k : I, ‖z k‖ ^ 2 := by ring
  exact hsumLower.trans htotal

/-- The square-sequence estimate for the finite jump count. -/
theorem jumpAlgebra_square_bound
    {I : Type*} [LinearOrder I] [Fintype I]
    (z : I → ℂ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    threshold * Real.sqrt (finiteSeparatedJumpCount z threshold : ℝ) ≤
      2 * Real.sqrt (∑ k : I, ‖z k‖ ^ 2) := by
  have hcount0 : 0 ≤ (finiteSeparatedJumpCount z threshold : ℝ) := by positivity
  have htotal0 : 0 ≤ ∑ k : I, ‖z k‖ ^ 2 := by positivity
  obtain ⟨s, t, hfamily⟩ := finiteSeparatedJumpCount_isAttained z threshold
  have hbound := jumpAlgebra_family_square_bound z threshold hthreshold.le s t hfamily
  have hcountReal : (finiteSeparatedJumpCount z threshold : ℝ) * threshold ^ 2 ≤
      4 * ∑ k : I, ‖z k‖ ^ 2 := by
    simpa [mul_comm] using hbound
  have hleft0 : 0 ≤ threshold * Real.sqrt
      (finiteSeparatedJumpCount z threshold : ℝ) :=
    mul_nonneg hthreshold.le (Real.sqrt_nonneg _)
  have hright0 : 0 ≤ 2 * Real.sqrt (∑ k : I, ‖z k‖ ^ 2) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hleftSq :
      (threshold * Real.sqrt (finiteSeparatedJumpCount z threshold : ℝ)) ^ 2 =
        threshold ^ 2 * (finiteSeparatedJumpCount z threshold : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hcount0]
  have hrightSq :
      (2 * Real.sqrt (∑ k : I, ‖z k‖ ^ 2)) ^ 2 =
        4 * ∑ k : I, ‖z k‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt htotal0]
    ring
  have hsq :
      (threshold * Real.sqrt (finiteSeparatedJumpCount z threshold : ℝ)) ^ 2 ≤
        (2 * Real.sqrt (∑ k : I, ‖z k‖ ^ 2)) ^ 2 := by
    rw [hleftSq, hrightSq]
    nlinarith [hcountReal]
  nlinarith

/-- Adding three scalar sequences costs the sum of their jump counts at
one-third of the threshold. -/
theorem jumpAlgebra_add_three
    {I : Type*} [LinearOrder I] [Fintype I]
    (z₁ z₂ z₃ : I → ℂ) {threshold : ℝ} (_hthreshold : 0 < threshold) :
    finiteSeparatedJumpCount (fun k => z₁ k + z₂ k + z₃ k) threshold ≤
      finiteSeparatedJumpCount z₁ (threshold / 3) +
        finiteSeparatedJumpCount z₂ (threshold / 3) +
          finiteSeparatedJumpCount z₃ (threshold / 3) := by
  classical
  let component : Fin 3 → I → ℂ := fun j =>
    if j = 0 then z₁ else if j = 1 then z₂ else z₃
  let zsum : I → ℂ := fun k => z₁ k + z₂ k + z₃ k
  obtain ⟨s, t, hfamily⟩ := finiteSeparatedJumpCount_isAttained zsum threshold
  have htriangle (i : Fin (finiteSeparatedJumpCount zsum threshold)) :
      ‖zsum (t i) - zsum (s i)‖ ≤
        ∑ j : Fin 3, ‖component j (t i) - component j (s i)‖ := by
    have hrewrite : zsum (t i) - zsum (s i) =
        (z₁ (t i) - z₁ (s i)) + (z₂ (t i) - z₂ (s i)) +
          (z₃ (t i) - z₃ (s i)) := by
      dsimp [zsum]
      ring
    rw [hrewrite]
    calc
      ‖(z₁ (t i) - z₁ (s i)) + (z₂ (t i) - z₂ (s i)) +
          (z₃ (t i) - z₃ (s i))‖ ≤
          ‖(z₁ (t i) - z₁ (s i)) + (z₂ (t i) - z₂ (s i))‖ +
            ‖z₃ (t i) - z₃ (s i)‖ := norm_add_le _ _
      _ ≤ ‖z₁ (t i) - z₁ (s i)‖ + ‖z₂ (t i) - z₂ (s i)‖ +
            ‖z₃ (t i) - z₃ (s i)‖ := by
        calc
          _ = ‖z₃ (t i) - z₃ (s i)‖ +
              ‖z₁ (t i) - z₁ (s i) + (z₂ (t i) - z₂ (s i))‖ := by ring
          _ ≤ ‖z₃ (t i) - z₃ (s i)‖ +
              (‖z₁ (t i) - z₁ (s i)‖ + ‖z₂ (t i) - z₂ (s i)‖) :=
            add_le_add_right
              (norm_add_le (z₁ (t i) - z₁ (s i)) (z₂ (t i) - z₂ (s i))) _
          _ = _ := by ring
      _ = ∑ j : Fin 3, ‖component j (t i) - component j (s i)‖ := by
        simp [component, Fin.sum_univ_three]
  have hsome (i : Fin (finiteSeparatedJumpCount zsum threshold)) :
      ∃ j : Fin 3, threshold / 3 <
        ‖component j (t i) - component j (s i)‖ := by
    by_contra h
    push Not at h
    have h0 := h (0 : Fin 3)
    have h1 := h (1 : Fin 3)
    have h2 := h (2 : Fin 3)
    have h0' : ‖z₁ (t i) - z₁ (s i)‖ ≤ threshold / 3 := by
      simpa [component] using h0
    have h1' : ‖z₂ (t i) - z₂ (s i)‖ ≤ threshold / 3 := by
      simpa [component] using h1
    have h2' : ‖z₃ (t i) - z₃ (s i)‖ ≤ threshold / 3 := by
      simpa [component] using h2
    have hsum :
        (∑ j : Fin 3, ‖component j (t i) - component j (s i)‖) ≤ threshold := by
      calc
        (∑ j : Fin 3, ‖component j (t i) - component j (s i)‖) =
            ‖z₁ (t i) - z₁ (s i)‖ + ‖z₂ (t i) - z₂ (s i)‖ +
              ‖z₃ (t i) - z₃ (s i)‖ := by
          simp [component, Fin.sum_univ_three]
        _ ≤ threshold := by linarith
    exact (not_lt_of_ge (htriangle i |>.trans hsum)) (hfamily.2 i)
  let color : Fin (finiteSeparatedJumpCount zsum threshold) → Fin 3 :=
    fun i => Classical.choose (hsome i)
  have hcolor (i : Fin (finiteSeparatedJumpCount zsum threshold)) :
      threshold / 3 < ‖component (color i) (t i) - component (color i) (s i)‖ :=
    Classical.choose_spec (hsome i)
  let fiber (j : Fin 3) : Finset (Fin (finiteSeparatedJumpCount zsum threshold)) :=
    Finset.univ.filter fun i => color i = j
  have hfiberCount (j : Fin 3) :
      (fiber j).card ≤ finiteSeparatedJumpCount (component j) (threshold / 3) := by
    let e := (fiber j).orderEmbOfFin rfl
    have he : StrictMono e := e.strictMono
    have hfam : SeparatedJumpFamily (component j) (threshold / 3)
        (fun i => s (e i)) (fun i => t (e i)) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i
        exact hfamily.1.1 (e i)
      · intro i k hik
        exact hfamily.1.2 (e i) (e k) (he hik)
      · intro i
        have hemem : e i ∈ fiber j := by
          exact Finset.orderEmbOfFin_mem _ _ i
        have hcol : color (e i) = j := (Finset.mem_filter.mp hemem).2
        simpa [hcol] using hcolor (e i)
    exact le_finiteSeparatedJumpCount_of_family
      (component j) (threshold / 3) ⟨fun i => s (e i), fun i => t (e i), hfam⟩
  have hpartition :
      (finiteSeparatedJumpCount zsum threshold : ℕ) =
        ∑ j : Fin 3, (fiber j).card := by
    simpa [fiber] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (s := (Finset.univ : Finset (Fin (finiteSeparatedJumpCount zsum threshold))))
        (t := (Finset.univ : Finset (Fin 3))) color).symm
  simpa [zsum] using (calc
    finiteSeparatedJumpCount zsum threshold = ∑ j : Fin 3, (fiber j).card :=
      hpartition
    _ ≤ ∑ j : Fin 3, finiteSeparatedJumpCount (component j) (threshold / 3) :=
      Finset.sum_le_sum fun j _ => hfiberCount j
    _ = finiteSeparatedJumpCount z₁ (threshold / 3) +
        finiteSeparatedJumpCount z₂ (threshold / 3) +
          finiteSeparatedJumpCount z₃ (threshold / 3) := by
      simp [component, Fin.sum_univ_three])

/-- The two finite-sequence estimates asserted by `lj:jump-algebra`. -/
theorem jumpAlgebra :
    (∀ {I : Type*} [LinearOrder I] [Fintype I]
      (z : I → ℂ) {threshold : ℝ} (hthreshold : 0 < threshold),
      threshold * Real.sqrt (finiteSeparatedJumpCount z threshold : ℝ) ≤
        2 * Real.sqrt (∑ k : I, ‖z k‖ ^ 2)) ∧
    (∀ {I : Type*} [LinearOrder I] [Fintype I]
      (z₁ z₂ z₃ : I → ℂ) {threshold : ℝ} (hthreshold : 0 < threshold),
      finiteSeparatedJumpCount (fun k => z₁ k + z₂ k + z₃ k) threshold ≤
        finiteSeparatedJumpCount z₁ (threshold / 3) +
          finiteSeparatedJumpCount z₂ (threshold / 3) +
            finiteSeparatedJumpCount z₃ (threshold / 3)) := by
  constructor
  · intro I instOrder instFintype z threshold hthreshold
    exact jumpAlgebra_square_bound z hthreshold
  · intro I instOrder instFintype z₁ z₂ z₃ threshold hthreshold
    exact jumpAlgebra_add_three z₁ z₂ z₃ hthreshold

end

end FractionalPrimes.Literature.JSW

end

#print axioms FractionalPrimes.Literature.JSW.jumpAlgebra_square_bound
#print axioms FractionalPrimes.Literature.JSW.jumpAlgebra_add_three
#print axioms FractionalPrimes.Literature.JSW.jumpAlgebra
