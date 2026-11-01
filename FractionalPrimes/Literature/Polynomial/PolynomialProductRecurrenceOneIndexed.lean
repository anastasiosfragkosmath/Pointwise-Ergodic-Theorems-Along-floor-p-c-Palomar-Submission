module

public import FractionalPrimes.Literature.Polynomial.PolynomialProductRecurrence

/-!
# One-indexed interface to product recurrence

The hyperbola argument produces directions in `[1,N₁]×[1,N₂]`, while
`productRecurrence` is stated on zero-indexed ranges and inserts `+1` in its
phase.  This file gives the exact finite reindexing bridge.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

/-- One-indexed form of `productRecurrence`.  No density is lost in shifting
`[1,N₁]×[1,N₂]` to `range N₁ × range N₂`. -/
theorem productRecurrence_oneIndexed
    {j N₁ N₂ : ℕ} (hj : 1 ≤ j) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    {sigma epsilon theta : ℝ} (hsigma : 0 < sigma)
    (hsigmaHalf : sigma < 1 / 2) (hepsilon : 0 ≤ epsilon)
    (hepsilonUpper : epsilon ≤
      1 / (256 * sigma⁻¹ * productRecurrenceA j sigma⁻¹ ^ 2))
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ Finset.Icc 1 N₁ ×ˢ Finset.Icc 1 N₂)
    (hcard : sigma * (N₁ : ℝ) * (N₂ : ℝ) ≤ (S.card : ℝ))
    (hgood : ∀ p ∈ S,
      realDistanceToIntegers
        (theta * (((p.1 : ℝ) * (p.2 : ℝ)) ^ j)) ≤ epsilon) :
    ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ productRecurrenceB j sigma⁻¹ ∧
      realDistanceToIntegers ((r : ℝ) * theta) ≤
        productRecurrenceB j sigma⁻¹ * epsilon /
          (((N₁ : ℝ) * (N₂ : ℝ)) ^ j) := by
  classical
  let shift : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 - 1, p.2 - 1)
  let shifted : Finset (ℕ × ℕ) := S.image shift
  have hpositive (p : ℕ × ℕ) (hp : p ∈ S) :
      1 ≤ p.1 ∧ 1 ≤ p.2 := by
    have hpbox := Finset.mem_product.mp (hS hp)
    exact ⟨(Finset.mem_Icc.mp hpbox.1).1, (Finset.mem_Icc.mp hpbox.2).1⟩
  have hinjective : Set.InjOn shift (↑S : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hpPos := hpositive p hp
    have hqPos := hpositive q hq
    apply Prod.ext
    · have hfirst := congrArg Prod.fst hpq
      dsimp [shift] at hfirst
      omega
    · have hsecond := congrArg Prod.snd hpq
      dsimp [shift] at hsecond
      omega
  have hshiftCard : shifted.card = S.card := by
    dsimp [shifted]
    exact Finset.card_image_of_injOn hinjective
  let target : Finset (ℕ × ℕ) :=
    (Finset.range N₁ ×ˢ Finset.range N₂).filter
      (fun p : ℕ × ℕ => realDistanceToIntegers
        (theta * (((p.1 + 1 : ℕ) : ℝ) * ((p.2 + 1 : ℕ) : ℝ)) ^ j) ≤
          epsilon)
  have hshiftSubset : shifted ⊆ target := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
    have hpbox := Finset.mem_product.mp (hS hp)
    have hpOne : 1 ≤ p.1 := (Finset.mem_Icc.mp hpbox.1).1
    have hpN₁ : p.1 ≤ N₁ := (Finset.mem_Icc.mp hpbox.1).2
    have hpTwo : 1 ≤ p.2 := (Finset.mem_Icc.mp hpbox.2).1
    have hpN₂ : p.2 ≤ N₂ := (Finset.mem_Icc.mp hpbox.2).2
    apply Finset.mem_filter.mpr
    constructor
    · rw [Finset.mem_product]
      simp only [Finset.mem_range]
      change p.1 - 1 < N₁ ∧ p.2 - 1 < N₂
      omega
    · simpa [shift, Nat.sub_add_cancel hpOne, Nat.sub_add_cancel hpTwo] using
        hgood p hp
  have htargetCard : (S.card : ℝ) ≤ (target.card : ℝ) := by
    have hnat : shifted.card ≤ target.card :=
      Finset.card_le_card hshiftSubset
    rw [hshiftCard] at hnat
    exact_mod_cast hnat
  have hdense : sigma * (N₁ : ℝ) * (N₂ : ℝ) ≤
      (target.card : ℝ) := hcard.trans htargetCard
  apply productRecurrence hj hN₁ hN₂ hsigma hsigmaHalf hepsilon
    hepsilonUpper
  simpa [target] using hdense

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.productRecurrence_oneIndexed
