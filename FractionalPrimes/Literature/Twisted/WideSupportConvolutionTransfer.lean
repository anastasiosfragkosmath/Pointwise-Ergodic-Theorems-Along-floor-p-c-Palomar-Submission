module

public import FractionalPrimes.Literature.Twisted.ShiftedConvolutionFactorExtraction
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Wide-support selected-factor transfer

This file proves the finite convolution step needed when the distinguished
factor occupies the source's two dyadic scales `(N/2,N]` and `(N,2N]`.
The other factors are controlled only by their absolute masses, so their
supports need not be single dyadic intervals.
-/

@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.Twisted

namespace FractionalPrimes.Literature.Twisted

private def wideSupportSplitAt {k : ℕ} (i₀ : Fin k)
    (m : Fin k → ℕ) : (Fin k → ℕ) × ℕ :=
  (Function.update m i₀ 1, m i₀)

private def wideSupportMergeAt {k : ℕ} (i₀ : Fin k)
    (p : (Fin k → ℕ) × ℕ) : Fin k → ℕ :=
  Function.update p.1 i₀ p.2

private theorem wideSupportMergeSplitAt {k : ℕ} (i₀ : Fin k)
    (m : Fin k → ℕ) :
    wideSupportMergeAt i₀ (wideSupportSplitAt i₀ m) = m := by
  funext j
  by_cases hj : j = i₀
  · subst j
    simp [wideSupportMergeAt, wideSupportSplitAt]
  · simp [wideSupportMergeAt, wideSupportSplitAt, hj]

private theorem wideSupportSplitMergeAt {k : ℕ} (i₀ : Fin k)
    (p : (Fin k → ℕ) × ℕ) (hp : p.1 i₀ = 1) :
    wideSupportSplitAt i₀ (wideSupportMergeAt i₀ p) = p := by
  apply Prod.ext
  · funext j
    by_cases hj : j = i₀
    · subst j
      simp [wideSupportSplitAt, wideSupportMergeAt, hp]
    · simp [wideSupportSplitAt, wideSupportMergeAt, hj]
  · simp [wideSupportSplitAt, wideSupportMergeAt]

private theorem wideSupportProductUpdate {k : ℕ} (i₀ : Fin k)
    (u : Fin k → ℕ) (m : ℕ) :
    (∏ i : Fin k, Function.update u i₀ m i) =
      m * ∏ i ∈ Finset.univ.erase i₀, u i := by
  calc
    (∏ i : Fin k, Function.update u i₀ m i) =
        (∏ i ∈ Finset.univ.erase i₀,
          Function.update u i₀ m i) * Function.update u i₀ m i₀ := by
            exact (Finset.prod_erase_mul (s := Finset.univ)
              (f := fun i => Function.update u i₀ m i)
              (Finset.mem_univ i₀)).symm
    _ = (∏ i ∈ Finset.univ.erase i₀, u i) * m := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        exact Function.update_of_ne (Finset.mem_erase.mp hi).1 m u
      · simp
    _ = m * ∏ i ∈ Finset.univ.erase i₀, u i := by ac_rfl

private theorem wideSupportCoefficientProductUpdate {k : ℕ}
    (i₀ : Fin k) (a : Fin k → ℕ → ℂ) (u : Fin k → ℕ) (m : ℕ) :
    (∏ i : Fin k, a i (Function.update u i₀ m i)) =
      a i₀ m * ∏ i ∈ Finset.univ.erase i₀, a i (u i) := by
  calc
    (∏ i : Fin k, a i (Function.update u i₀ m i)) =
        (∏ i ∈ Finset.univ.erase i₀,
          a i (Function.update u i₀ m i)) *
          a i₀ (Function.update u i₀ m i₀) := by
            exact (Finset.prod_erase_mul (s := Finset.univ)
              (f := fun i => a i (Function.update u i₀ m i))
              (Finset.mem_univ i₀)).symm
    _ = (∏ i ∈ Finset.univ.erase i₀, a i (u i)) * a i₀ m := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        exact congrArg (a i)
          (Function.update_of_ne (Finset.mem_erase.mp hi).1 m u)
      · simp
    _ = a i₀ m * ∏ i ∈ Finset.univ.erase i₀, a i (u i) := by ac_rfl

/-- A finite product convolution with a selected factor supported on the exact
two-scale source interval `(N/2,2N]`.  For each fixed choice of the other
factors, the product interval cuts the selected variable into one interval on
`(N/2,N]` and one on `(N,2N]`; the corresponding local estimates are the only
cancellation inputs.  The other coordinates enter only through their
absolute masses. -/
theorem wideSupportFiniteConvolutionSmallFactor
    {k : ℕ} (i₀ : Fin k) (N ε x y : ℝ)
    (S : Fin k → Finset ℕ) (a : Fin k → ℕ → ℂ)
    (B : Fin k → ℝ)
    (hN : 0 < N) (hε : 0 ≤ ε) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hSelected : S i₀ =
      factorExtractionDyadicInterval (N / 2) ∪
        factorExtractionDyadicInterval N)
    (hPositive : ∀ i n, n ∈ S i → 0 < n)
    (hMass : ∀ j ∈ Finset.univ.erase i₀,
      (∑ n ∈ S j, ‖a j n‖) ≤ B j)
    (hShort : ∀ M : ℝ, (M = N / 2 ∨ M = N) →
      ∀ u v : ℝ, 0 ≤ u →
        Set.Ioc u v ⊆ Set.Ioc M (2 * M) →
        ‖∑ n ∈ factorExtractionRealInterval u v, a i₀ n‖ ≤
          ε * Real.sqrt M) :
    ‖∑ m ∈ (Fintype.piFinset S).filter
        (fun m => x < (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ∧
          (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ≤ y),
        ∏ i : Fin k, a i (m i)‖ ≤
      2 * ε * Real.sqrt N *
        ∏ j ∈ Finset.univ.erase i₀, B j := by
  classical
  let V : Finset (Fin k → ℕ) := Fintype.piFinset S
  let P : (Fin k → ℕ) → Prop := fun m =>
    x < (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ∧
      (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ≤ y
  let R : Finset (Fin k → ℕ) :=
    Fintype.piFinset (fun i => if i = i₀ then {1} else S i)
  let Q : (Fin k → ℕ) × ℕ → Prop := fun p =>
    (((∏ j ∈ Finset.univ.erase i₀, p.1 j : ℕ) : ℝ) * (p.2 : ℝ)) ∈
      Set.Ioc x y
  let G : Fin k → ℕ → ℂ := fun i n => a i n
  let F : (Fin k → ℕ) → ℂ := fun m => ∏ i : Fin k, G i (m i)
  have hReindex :
      (∑ m ∈ V.filter P, F m) =
        ∑ p ∈ (R ×ˢ S i₀).filter Q,
          F (wideSupportMergeAt i₀ p) := by
    refine Finset.sum_bij (fun m _ => wideSupportSplitAt i₀ m) ?_ ?_ ?_ ?_
    · intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hmV, hmP⟩
      have hmCoords := Fintype.mem_piFinset.mp hmV
      have hother : (wideSupportSplitAt i₀ m).1 ∈ R := by
        apply Fintype.mem_piFinset.mpr
        intro i
        by_cases hi : i = i₀
        · subst i
          simp [wideSupportSplitAt]
        · have hmi : m i ∈ S i := hmCoords i
          simpa [R, wideSupportSplitAt, hi] using
            (show Function.update m i₀ 1 i ∈ S i by
              simpa [Function.update_of_ne hi] using hmi)
      have hselected : (wideSupportSplitAt i₀ m).2 ∈ S i₀ := hmCoords i₀
      have hP' : P (wideSupportMergeAt i₀
          (wideSupportSplitAt i₀ m)) := by
        rw [wideSupportMergeSplitAt]
        exact hmP
      have hQ : Q (wideSupportSplitAt i₀ m) := by
        have hn := wideSupportProductUpdate i₀
          (wideSupportSplitAt i₀ m).1 (wideSupportSplitAt i₀ m).2
        have hcast :
            (((∏ i : Fin k,
              wideSupportMergeAt i₀ (wideSupportSplitAt i₀ m) i : ℕ) : ℕ) : ℝ) =
              (((∏ i ∈ Finset.univ.erase i₀,
                (wideSupportSplitAt i₀ m).1 i : ℕ) : ℝ) *
                ((wideSupportSplitAt i₀ m).2 : ℝ)) := by
          change (((∏ i : Fin k,
              Function.update (wideSupportSplitAt i₀ m).1 i₀
                (wideSupportSplitAt i₀ m).2 i : ℕ) : ℕ) : ℝ) = _
          rw [hn]
          push_cast
          ring
        have hmem := hP'
        change x < _ ∧ _ ≤ y at hmem
        rw [hcast] at hmem
        exact hmem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hother, hselected⟩, hQ⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      have hmerge := congrArg (wideSupportMergeAt i₀) heq
      simpa [wideSupportMergeSplitAt] using hmerge
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpProd, hq⟩
      rcases Finset.mem_product.mp hpProd with ⟨hpR, hpS⟩
      have hpCoords := Fintype.mem_piFinset.mp hpR
      have hp0 : p.1 i₀ = 1 := by
        have h := hpCoords i₀
        simpa [R] using h
      refine ⟨wideSupportMergeAt i₀ p, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
        · intro i
          by_cases hi : i = i₀
          · subst i
            simpa [wideSupportMergeAt] using hpS
          · have hpi : p.1 i ∈ S i := by
              simpa [R, hi] using hpCoords i
            simpa [wideSupportMergeAt, Function.update_of_ne hi] using hpi
        · have hn := wideSupportProductUpdate i₀ p.1 p.2
          have hcast :
              (((∏ i : Fin k, wideSupportMergeAt i₀ p i : ℕ) : ℕ) : ℝ) =
                (((∏ i ∈ Finset.univ.erase i₀, p.1 i : ℕ) : ℝ) * (p.2 : ℝ)) := by
            change (((∏ i : Fin k,
              Function.update p.1 i₀ p.2 i : ℕ) : ℕ) : ℝ) = _
            rw [hn]
            push_cast
            ring
          change x < _ ∧ _ ≤ y at hq ⊢
          rw [hcast]
          exact hq
      · exact wideSupportSplitMergeAt i₀ p hp0
    · intro m hm
      rw [wideSupportMergeSplitAt]
  have hTarget :
      (∑ p ∈ (R ×ˢ S i₀).filter Q,
        F (wideSupportMergeAt i₀ p)) =
      ∑ u ∈ R,
        (∑ n ∈ (S i₀).filter (fun n => Q (u, n)), G i₀ n) *
          ∏ j ∈ Finset.univ.erase i₀, G j (u j) := by
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hq : Q (u, n)
    · change (if Q (u, n) then F (wideSupportMergeAt i₀ (u, n)) else 0) = _
      simp [hq]
      simpa [F, G, wideSupportMergeAt] using
        (wideSupportCoefficientProductUpdate i₀ G u n)
    · change (if Q (u, n) then F (wideSupportMergeAt i₀ (u, n)) else 0) = _
      simp [hq]
  have hRestMass :
      (∑ u ∈ R, ∏ j ∈ Finset.univ.erase i₀, ‖G j (u j)‖) =
        ∏ j ∈ Finset.univ.erase i₀, ∑ n ∈ S j, ‖G j n‖ := by
    let T : Fin k → Finset ℕ := fun i => if i = i₀ then {1} else S i
    let H : Fin k → ℕ → ℝ := fun i n => if i = i₀ then 1 else ‖G i n‖
    calc
      (∑ u ∈ R, ∏ j ∈ Finset.univ.erase i₀, ‖G j (u j)‖) =
          ∑ u ∈ R, ∏ i : Fin k, H i (u i) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hu0 : u i₀ = 1 := by
          have huCoords := Fintype.mem_piFinset.mp (by simpa [R] using hu)
          simpa [R] using huCoords i₀
        calc
          (∏ j ∈ Finset.univ.erase i₀, ‖G j (u j)‖) =
              ∏ j ∈ Finset.univ.erase i₀, H j (u j) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
            simp [H, hji]
          _ = (∏ j ∈ Finset.univ.erase i₀, H j (u j)) * H i₀ (u i₀) := by
            simp [H, hu0]
          _ = ∏ i : Fin k, H i (u i) := by
            exact Finset.prod_erase_mul (s := Finset.univ)
              (f := fun i => H i (u i)) (Finset.mem_univ i₀)
      _ = ∏ i : Fin k, ∑ n ∈ T i, H i n := by
        rw [show R = Fintype.piFinset T by rfl]
        rw [← Finset.prod_univ_sum]
      _ = ∏ j ∈ Finset.univ.erase i₀, ∑ n ∈ S j, ‖G j n‖ := by
        rw [← Finset.prod_erase_mul (s := Finset.univ)
          (f := fun i : Fin k => ∑ n ∈ T i, H i n)
          (Finset.mem_univ i₀)]
        have hselectedSum : ∑ n ∈ T i₀, H i₀ n = 1 := by simp [T, H]
        rw [hselectedSum, mul_one]
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
        simp [T, H, hji, G]
  have hRestBound :
      (∑ u ∈ R, ∏ j ∈ Finset.univ.erase i₀, ‖G j (u j)‖) ≤
        ∏ j ∈ Finset.univ.erase i₀, B j := by
    rw [hRestMass]
    apply Finset.prod_le_prod₀
    · intro j hj
      positivity
    · intro j hj
      simpa [G] using hMass j hj
  have hlocal (u : Fin k → ℕ) (hu : u ∈ R) :
      ‖∑ n ∈ (S i₀).filter (fun n => Q (u, n)), G i₀ n‖ ≤
        2 * ε * Real.sqrt N := by
    have huCoords := Fintype.mem_piFinset.mp (by simpa [R] using hu)
    have hu0 : u i₀ = 1 := by simpa [R] using huCoords i₀
    let Mnat : ℕ := ∏ j ∈ Finset.univ.erase i₀, u j
    let M : ℝ := (Mnat : ℝ)
    have hMnat : 0 < Mnat := by
      dsimp [Mnat]
      apply Finset.prod_pos
      intro j hj
      have hjS : u j ∈ S j := by
        have h := huCoords j
        simpa [R, (Finset.mem_erase.mp hj).1] using h
      exact hPositive j (u j) hjS
    have hM : 0 < M := by dsimp [M]; exact_mod_cast hMnat
    have hlowScale : 0 < N / 2 := by positivity
    have hlow2 : 2 * (N / 2) = N := by ring
    have hlow := factorExtractionDyadicProductInterval_iff
      hlowScale hM hx hxy
    have hhigh := factorExtractionDyadicProductInterval_iff
      hN hM hx hxy
    have hSelectedUnion : S i₀ =
        factorExtractionDyadicInterval (N / 2) ∪
          factorExtractionDyadicInterval N := hSelected
    have hlowInterval :
        ‖∑ n ∈ factorExtractionRealInterval
          (max (N / 2) (x / M)) (min N (y / M)), G i₀ n‖ ≤
          ε * Real.sqrt (N / 2) := by
      apply hShort (N / 2) (Or.inl rfl)
      · exact le_max_of_le_left hlowScale.le
      · intro z hz
        exact ⟨lt_of_le_of_lt (le_max_left _ _) hz.1,
          le_trans hz.2 (by
            calc
              min N (y / M) ≤ N := min_le_left _ _
              _ = 2 * (N / 2) := hlow2.symm)⟩
    have hhighInterval :
        ‖∑ n ∈ factorExtractionRealInterval
          (max N (x / M)) (min (2 * N) (y / M)), G i₀ n‖ ≤
          ε * Real.sqrt N := by
      apply hShort N (Or.inr rfl)
      · exact le_max_of_le_left hN.le
      · intro z hz
        exact ⟨lt_of_le_of_lt (le_max_left _ _) hz.1,
          le_trans hz.2 (min_le_left _ _)⟩
    have hLowFilter :
        (factorExtractionDyadicInterval (N / 2)).filter
            (fun n => Q (u, n)) =
          factorExtractionRealInterval
            (max (N / 2) (x / M)) (min N (y / M)) := by
      ext n
      simp only [Finset.mem_filter]
      have hQeq : Q (u, n) ↔ M * (n : ℝ) ∈ Set.Ioc x y := by
        simp [Q, M, Mnat, Nat.cast_prod]
      rw [hQeq]
      simpa [M, Mnat, hlow2] using hlow n
    have hHighFilter :
        (factorExtractionDyadicInterval N).filter
            (fun n => Q (u, n)) =
          factorExtractionRealInterval
            (max N (x / M)) (min (2 * N) (y / M)) := by
      ext n
      simp only [Finset.mem_filter]
      have hQeq : Q (u, n) ↔ M * (n : ℝ) ∈ Set.Ioc x y := by
        simp [Q, M, Mnat, Nat.cast_prod]
      rw [hQeq]
      simpa [M, Mnat] using hhigh n
    have hdisjoint : Disjoint
        (factorExtractionDyadicInterval (N / 2))
        (factorExtractionDyadicInterval N) := by
      rw [factorExtractionDyadicInterval, factorExtractionDyadicInterval,
        Finset.Ioc_disjoint_Ioc]
      have hfloor : Nat.floor N ≤ Nat.floor (2 * N) :=
        Nat.floor_mono (by linarith)
      have hfloorHalf : Nat.floor (N / 2) ≤ Nat.floor N :=
        Nat.floor_mono (by linarith)
      have hlowFloorEq : Nat.floor (2 * (N / 2)) = Nat.floor N :=
        congrArg Nat.floor hlow2
      rw [hlowFloorEq]
      rw [min_eq_left hfloor, max_eq_right hfloorHalf]
    have hselectedSum :
        (∑ n ∈ (S i₀).filter (fun n => Q (u, n)), G i₀ n) =
          (∑ n ∈ factorExtractionRealInterval
              (max (N / 2) (x / M)) (min N (y / M)), G i₀ n) +
          ∑ n ∈ factorExtractionRealInterval
              (max N (x / M)) (min (2 * N) (y / M)), G i₀ n := by
      rw [hSelectedUnion, Finset.filter_union]
      rw [Finset.sum_union
        (hdisjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      rw [hLowFilter, hHighFilter]
    rw [hselectedSum]
    have hsumNorm :
        ‖(∑ n ∈ factorExtractionRealInterval
              (max (N / 2) (x / M)) (min N (y / M)), G i₀ n) +
            ∑ n ∈ factorExtractionRealInterval
              (max N (x / M)) (min (2 * N) (y / M)), G i₀ n‖ ≤
          ε * Real.sqrt (N / 2) + ε * Real.sqrt N := by
      exact (norm_add_le _ _).trans (add_le_add hlowInterval hhighInterval)
    apply hsumNorm.trans
    have hsqrt : Real.sqrt (N / 2) ≤ Real.sqrt N := by
      apply Real.sqrt_le_sqrt
      linarith
    nlinarith [hsqrt, hε, Real.sqrt_nonneg N]
  have hBound :
      ‖∑ p ∈ (R ×ˢ S i₀).filter Q,
          F (wideSupportMergeAt i₀ p)‖ ≤
        2 * ε * Real.sqrt N * ∏ j ∈ Finset.univ.erase i₀, B j := by
    rw [hTarget]
    have hC : 0 ≤ 2 * ε * Real.sqrt N := by positivity
    calc
      ‖∑ u ∈ R,
          (∑ n ∈ (S i₀).filter (fun n => Q (u, n)), G i₀ n) *
            ∏ j ∈ Finset.univ.erase i₀, G j (u j)‖ ≤
          ∑ u ∈ R,
            ‖(∑ n ∈ (S i₀).filter (fun n => Q (u, n)), G i₀ n) *
              ∏ j ∈ Finset.univ.erase i₀, G j (u j)‖ := norm_sum_le _ _
      _ = ∑ u ∈ R,
          ‖∑ n ∈ (S i₀).filter (fun n => Q (u, n)), G i₀ n‖ *
            ‖∏ j ∈ Finset.univ.erase i₀, G j (u j)‖ := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [norm_mul]
      _ ≤ ∑ u ∈ R,
          (2 * ε * Real.sqrt N) *
            ‖∏ j ∈ Finset.univ.erase i₀, G j (u j)‖ := by
              apply Finset.sum_le_sum
              intro u hu
              exact mul_le_mul_of_nonneg_right (hlocal u hu) (norm_nonneg _)
      _ = (2 * ε * Real.sqrt N) *
          ∑ u ∈ R, ‖∏ j ∈ Finset.univ.erase i₀, G j (u j)‖ := by
              rw [Finset.mul_sum]
      _ = (2 * ε * Real.sqrt N) *
          ∑ u ∈ R, ∏ j ∈ Finset.univ.erase i₀, ‖G j (u j)‖ := by
              congr 1
              apply Finset.sum_congr rfl
              intro u hu
              simp
      _ ≤ (2 * ε * Real.sqrt N) *
          ∏ j ∈ Finset.univ.erase i₀, B j :=
            mul_le_mul_of_nonneg_left hRestBound hC
  calc
    ‖∑ m ∈ (Fintype.piFinset S).filter P, F m‖ =
        ‖∑ m ∈ V.filter P, F m‖ := by rfl
    _ = ‖∑ p ∈ (R ×ˢ S i₀).filter Q,
          F (wideSupportMergeAt i₀ p)‖ := by rw [hReindex]
    _ ≤ 2 * ε * Real.sqrt N *
        ∏ j ∈ Finset.univ.erase i₀, B j := hBound

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.wideSupportFiniteConvolutionSmallFactor
