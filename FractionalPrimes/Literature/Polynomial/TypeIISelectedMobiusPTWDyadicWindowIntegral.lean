module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWDyadicWindowIdentity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

/-! Finite integral transfer for the dyadic support blocks used in the
selected-Möbius PTW source decomposition. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- A finite source character/allocation sum commutes exactly with the three
dyadic block sums. The common frequency scalar and the allocation/character
weights are retained in every block term. -/
theorem weightedAllocationSource_eq_tripleDyadicBlockSum
    {R : Type*} [Fintype R] {Q : ℕ}
    (k₁ k₂ k₃ : ℕ) (c : ℝ → ℂ)
    (weight : R → BlueprintCharacter Q → ℂ)
    (G : R → BlueprintCharacter Q → ℝ → ℂ)
    (F : ℕ → ℕ → ℕ → R → BlueprintCharacter Q → ℝ → ℂ)
    (hdecomp : ∀ r χ t,
      G r χ t =
        ∑ i ∈ Finset.range k₁,
          ∑ j ∈ Finset.range k₂,
            ∑ k ∈ Finset.range k₃, F i j k r χ t)
    (t : ℝ) :
    c t * (∑ r : R, ∑ χ : BlueprintCharacter Q,
        weight r χ * G r χ t) =
      ∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃,
            ∑ r : R, ∑ χ : BlueprintCharacter Q,
              c t * (weight r χ * F i j k r χ t) := by
  classical
  let A : Finset (R × BlueprintCharacter Q) :=
    Finset.univ ×ˢ Finset.univ
  let B : Finset (ℕ × (ℕ × ℕ)) :=
    Finset.range k₁ ×ˢ (Finset.range k₂ ×ˢ Finset.range k₃)
  let H : (R × BlueprintCharacter Q) → (ℕ × (ℕ × ℕ)) → ℂ :=
    fun a b => c t * (weight a.1 a.2 * F b.1 b.2.1 b.2.2 a.1 a.2 t)
  have hscale (r : R) (χ : BlueprintCharacter Q) :
      c t * (weight r χ * G r χ t) =
        ∑ i ∈ Finset.range k₁,
          ∑ j ∈ Finset.range k₂,
            ∑ k ∈ Finset.range k₃,
              c t * (weight r χ * F i j k r χ t) := by
    rw [hdecomp r χ t]
    calc
      c t * (weight r χ *
          (∑ i ∈ Finset.range k₁,
            ∑ j ∈ Finset.range k₂,
              ∑ k ∈ Finset.range k₃, F i j k r χ t)) =
          (c t * weight r χ) *
            (∑ i ∈ Finset.range k₁,
              ∑ j ∈ Finset.range k₂,
                ∑ k ∈ Finset.range k₃, F i j k r χ t) := by ring
      _ = ∑ i ∈ Finset.range k₁,
            ∑ j ∈ Finset.range k₂,
              ∑ k ∈ Finset.range k₃,
                (c t * weight r χ) * F i j k r χ t := by
          simp_rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range k₁,
            ∑ j ∈ Finset.range k₂,
              ∑ k ∈ Finset.range k₃,
                c t * (weight r χ * F i j k r χ t) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          ring
  have hblock (r : R) (χ : BlueprintCharacter Q) :
      (∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃,
            c t * (weight r χ * F i j k r χ t)) =
        ∑ b ∈ B, H (r, χ) b := by
    dsimp [B, H]
    calc
      _ = ∑ i ∈ Finset.range k₁,
            ∑ p ∈ Finset.range k₂ ×ˢ Finset.range k₃,
              c t * (weight r χ * F i p.1 p.2 r χ t) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (Finset.sum_product' (Finset.range k₂) (Finset.range k₃)
            (fun j k => c t * (weight r χ * F i j k r χ t))).symm
      _ = ∑ b ∈ Finset.range k₁ ×ˢ
              (Finset.range k₂ ×ˢ Finset.range k₃),
              c t * (weight r χ * F b.1 b.2.1 b.2.2 r χ t) :=
          (Finset.sum_product' (Finset.range k₁)
            (Finset.range k₂ ×ˢ Finset.range k₃)
            (fun i p => c t * (weight r χ * F i p.1 p.2 r χ t))).symm
  calc
    c t * (∑ r : R, ∑ χ : BlueprintCharacter Q,
        weight r χ * G r χ t) =
      ∑ r : R, ∑ χ : BlueprintCharacter Q,
        c t * (weight r χ * G r χ t) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ r : R, ∑ χ : BlueprintCharacter Q,
          ∑ b ∈ B, H (r, χ) b := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro χ hχ
      exact (hscale r χ).trans (hblock r χ)
    _ = ∑ a ∈ A, ∑ b ∈ B, H a b := by
      dsimp [A]
      exact (Finset.sum_product' (Finset.univ : Finset R)
        (Finset.univ : Finset (BlueprintCharacter Q))
        (fun r χ => ∑ b ∈ B, H (r, χ) b)).symm
    _ = ∑ b ∈ B, ∑ a ∈ A, H a b := by
      dsimp [A]
      exact Finset.sum_comm
    _ = ∑ b ∈ B, ∑ r : R, ∑ χ : BlueprintCharacter Q,
          c t * (weight r χ * F b.1 b.2.1 b.2.2 r χ t) := by
      apply Finset.sum_congr rfl
      intro b hb
      dsimp [A, H]
      exact Finset.sum_product' (Finset.univ : Finset R)
        (Finset.univ : Finset (BlueprintCharacter Q))
        (fun r χ => c t * (weight r χ * F b.1 b.2.1 b.2.2 r χ t))
    _ = _ := by
      dsimp [B]
      calc
        _ = ∑ i ∈ Finset.range k₁,
              ∑ p ∈ Finset.range k₂ ×ˢ Finset.range k₃,
                ∑ r : R, ∑ χ : BlueprintCharacter Q,
                  c t * (weight r χ * F i p.1 p.2 r χ t) :=
            Finset.sum_product' (Finset.range k₁)
              (Finset.range k₂ ×ˢ Finset.range k₃)
              (fun i p => ∑ r : R, ∑ χ : BlueprintCharacter Q,
                c t * (weight r χ * F i p.1 p.2 r χ t))
        _ = ∑ i ∈ Finset.range k₁,
              ∑ j ∈ Finset.range k₂,
                ∑ k ∈ Finset.range k₃,
                  ∑ r : R, ∑ χ : BlueprintCharacter Q,
                    c t * (weight r χ * F i j k r χ t) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_product' (Finset.range k₂) (Finset.range k₃)
              (fun j k => ∑ r : R, ∑ χ : BlueprintCharacter Q,
                c t * (weight r χ * F i j k r χ t))

/-- The integral of the norm of a finite sum is bounded by the sum of the
integrals of the norms on the source's compact symmetric frequency window. -/
theorem integral_norm_finsetSum_le_sum_integral_norm
    {ι : Type*} (S : Finset ι) (U : ℝ) (F : ι → ℝ → ℂ)
    (hcont : ∀ i, Continuous (F i)) :
    (∫ t in Set.Icc (-U) U, ‖∑ i ∈ S, F i t‖ ∂volume) ≤
      ∑ i ∈ S, ∫ t in Set.Icc (-U) U, ‖F i t‖ ∂volume := by
  let E : Set ℝ := Set.Icc (-U) U
  let sumF : ℝ → ℂ := fun t => ∑ i ∈ S, F i t
  let majorant : ℝ → ℝ := fun t => ∑ i ∈ S, ‖F i t‖
  have hsumCont : Continuous sumF := by
    dsimp [sumF]
    exact continuous_finsetSum S fun i hi => hcont i
  have hmajorCont : Continuous majorant := by
    dsimp [majorant]
    exact continuous_finsetSum S fun i hi => continuous_norm.comp (hcont i)
  have hsumInt : IntegrableOn (fun t : ℝ => ‖sumF t‖) E volume := by
    exact (continuous_norm.comp hsumCont).continuousOn.integrableOn_compact
      isCompact_Icc
  have hmajorInt : IntegrableOn majorant E volume :=
    hmajorCont.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint (t : ℝ) : ‖sumF t‖ ≤ majorant t := by
    dsimp [sumF, majorant]
    exact norm_sum_le S (fun i => F i t)
  calc
    (∫ t in E, ‖sumF t‖ ∂volume) ≤ ∫ t in E, majorant t ∂volume :=
      integral_mono hsumInt hmajorInt hpoint
    _ = ∑ i ∈ S, ∫ t in E, ‖F i t‖ ∂volume := by
      rw [integral_finsetSum]
      intro i hi
      exact (continuous_norm.comp (hcont i)).continuousOn.integrableOn_compact
        isCompact_Icc

/-- Accumulating a uniform source integral bound over three independent
dyadic block indices costs exactly the product of the three finite block
counts. -/
theorem integral_norm_tripleDyadicBlockSum_le
    (k₁ k₂ k₃ : ℕ) (U K : ℝ)
    (F : ℕ → ℕ → ℕ → ℝ → ℂ)
    (hcont : ∀ i j k, Continuous (F i j k))
    (hblock : ∀ i ∈ Finset.range k₁,
      ∀ j ∈ Finset.range k₂, ∀ k ∈ Finset.range k₃,
        (∫ t in Set.Icc (-U) U, ‖F i j k t‖ ∂volume) ≤ K) :
    (∫ t in Set.Icc (-U) U,
      ‖∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃, F i j k t‖ ∂volume) ≤
      (k₁ : ℝ) * (k₂ : ℝ) * (k₃ : ℝ) * K := by
  let S₂₃ := Finset.range k₂ ×ˢ Finset.range k₃
  let S := Finset.range k₁ ×ˢ S₂₃
  let G : ℕ × (ℕ × ℕ) → ℝ → ℂ := fun p t => F p.1 p.2.1 p.2.2 t
  have hflat (t : ℝ) :
      (∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃, F i j k t) =
        ∑ p ∈ S, G p t := by
    dsimp [S, S₂₃, G]
    have hinner (i : ℕ) :
        (∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃, F i j k t) =
        ∑ p ∈ Finset.range k₂ ×ˢ Finset.range k₃,
          F i p.1 p.2 t := by
      exact (Finset.sum_product' (Finset.range k₂) (Finset.range k₃)
        (fun j k => F i j k t)).symm
    rw [show (∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃, F i j k t) =
        ∑ i ∈ Finset.range k₁,
          ∑ p ∈ Finset.range k₂ ×ˢ Finset.range k₃,
            F i p.1 p.2 t by
          apply Finset.sum_congr rfl
          intro i hi
          exact hinner i]
    exact (Finset.sum_product' (Finset.range k₁) S₂₃
      (fun i p => F i p.1 p.2 t)).symm
  have hGcont : ∀ p, Continuous (G p) := by
    intro p
    exact hcont p.1 p.2.1 p.2.2
  have hGbound : ∀ p ∈ S,
      (∫ t in Set.Icc (-U) U, ‖G p t‖ ∂volume) ≤ K := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hi, hjk⟩
    rcases Finset.mem_product.mp hjk with ⟨hj, hk⟩
    exact hblock p.1 hi p.2.1 hj p.2.2 hk
  have hsum := integral_norm_finsetSum_le_sum_integral_norm S U G hGcont
  have hbound :
      (∑ p ∈ S, ∫ t in Set.Icc (-U) U, ‖G p t‖ ∂volume) ≤
        ∑ p ∈ S, K := by
    apply Finset.sum_le_sum
    intro p hp
    exact hGbound p hp
  have hcard : S.card = k₁ * (k₂ * k₃) := by
    simp [S, S₂₃]
  calc
    (∫ t in Set.Icc (-U) U,
      ‖∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃, F i j k t‖ ∂volume) =
        ∫ t in Set.Icc (-U) U, ‖∑ p ∈ S, G p t‖ ∂volume := by
          apply integral_congr_ae
          filter_upwards with t
          rw [hflat t]
    _ ≤ ∑ p ∈ S, ∫ t in Set.Icc (-U) U, ‖G p t‖ ∂volume := hsum
    _ ≤ ∑ p ∈ S, K := hbound
    _ = (S.card : ℝ) * K := by simp
    _ = (k₁ : ℝ) * (k₂ : ℝ) * (k₃ : ℝ) * K := by
      rw [hcard]
      push_cast
      ring

/-- The same outer transfer with the source's common maximum `J₀` block
count. The exact finite loss is `J₀^3`. -/
theorem integral_norm_tripleDyadicBlockSum_le_of_count_bound
    (k₁ k₂ k₃ J₀ : ℕ) (U K : ℝ)
    (F : ℕ → ℕ → ℕ → ℝ → ℂ)
    (hcont : ∀ i j k, Continuous (F i j k))
    (hblock : ∀ i ∈ Finset.range k₁,
      ∀ j ∈ Finset.range k₂, ∀ k ∈ Finset.range k₃,
        (∫ t in Set.Icc (-U) U, ‖F i j k t‖ ∂volume) ≤ K)
    (hcount₁ : k₁ ≤ J₀) (hcount₂ : k₂ ≤ J₀) (hcount₃ : k₃ ≤ J₀)
    (hK : 0 ≤ K) :
    (∫ t in Set.Icc (-U) U,
      ‖∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃, F i j k t‖ ∂volume) ≤
      (J₀ : ℝ) ^ 3 * K := by
  have hbase := integral_norm_tripleDyadicBlockSum_le
    k₁ k₂ k₃ U K F hcont hblock
  have h₁ : (k₁ : ℝ) ≤ J₀ := by exact_mod_cast hcount₁
  have h₂ : (k₂ : ℝ) ≤ J₀ := by exact_mod_cast hcount₂
  have h₃ : (k₃ : ℝ) ≤ J₀ := by exact_mod_cast hcount₃
  have hprod :
      (k₁ : ℝ) * (k₂ : ℝ) * (k₃ : ℝ) ≤ (J₀ : ℝ) ^ 3 := by
    have h12 : (k₁ : ℝ) * (k₂ : ℝ) ≤ (J₀ : ℝ) * J₀ :=
      mul_le_mul h₁ h₂ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc
      (k₁ : ℝ) * (k₂ : ℝ) * (k₃ : ℝ) ≤
          ((J₀ : ℝ) * J₀) * J₀ :=
        mul_le_mul h12 h₃ (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = (J₀ : ℝ) ^ 3 := by ring
  calc
    _ ≤ (k₁ : ℝ) * (k₂ : ℝ) * (k₃ : ℝ) * K := hbase
    _ ≤ (J₀ : ℝ) ^ 3 * K :=
      mul_le_mul_of_nonneg_right hprod hK

/-- An exact pointwise source decomposition may be supplied separately from
the per-block estimates. This adapter transfers those block estimates to
the integral of the full source integrand, with the exact `J₀^3` loss. -/
theorem integral_norm_of_pointwise_tripleDyadicBlockSum_le_of_count_bound
    (k₁ k₂ k₃ J₀ : ℕ) (U K : ℝ)
    (G : ℝ → ℂ) (F : ℕ → ℕ → ℕ → ℝ → ℂ)
    (hsource : ∀ t : ℝ,
      G t = ∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃, F i j k t)
    (hcont : ∀ i j k, Continuous (F i j k))
    (hblock : ∀ i ∈ Finset.range k₁,
      ∀ j ∈ Finset.range k₂, ∀ k ∈ Finset.range k₃,
        (∫ t in Set.Icc (-U) U, ‖F i j k t‖ ∂volume) ≤ K)
    (hcount₁ : k₁ ≤ J₀) (hcount₂ : k₂ ≤ J₀) (hcount₃ : k₃ ≤ J₀)
    (hK : 0 ≤ K) :
    (∫ t in Set.Icc (-U) U, ‖G t‖ ∂volume) ≤ (J₀ : ℝ) ^ 3 * K := by
  calc
    (∫ t in Set.Icc (-U) U, ‖G t‖ ∂volume) =
        ∫ t in Set.Icc (-U) U,
          ‖∑ i ∈ Finset.range k₁,
            ∑ j ∈ Finset.range k₂,
              ∑ k ∈ Finset.range k₃, F i j k t‖ ∂volume := by
          apply integral_congr_ae
          filter_upwards with t
          rw [hsource t]
    _ ≤ (J₀ : ℝ) ^ 3 * K :=
      integral_norm_tripleDyadicBlockSum_le_of_count_bound
        k₁ k₂ k₃ J₀ U K F hcont hblock hcount₁ hcount₂ hcount₃ hK

/-- Combining the exact finite character/allocation reindexing with the
per-block integral bounds transfers those bounds to the full source
integrand. The only outer loss is the exact `J₀^3` block count. -/
theorem integral_norm_weightedAllocationSource_le_of_count_bound
    {R : Type*} [Fintype R] {Q : ℕ}
    (k₁ k₂ k₃ J₀ : ℕ) (U K : ℝ) (c : ℝ → ℂ)
    (weight : R → BlueprintCharacter Q → ℂ)
    (G : R → BlueprintCharacter Q → ℝ → ℂ)
    (F : ℕ → ℕ → ℕ → R → BlueprintCharacter Q → ℝ → ℂ)
    (hdecomp : ∀ r χ t,
      G r χ t =
        ∑ i ∈ Finset.range k₁,
          ∑ j ∈ Finset.range k₂,
            ∑ k ∈ Finset.range k₃, F i j k r χ t)
    (hcont : ∀ i j k, Continuous (fun t : ℝ =>
      ∑ r : R, ∑ χ : BlueprintCharacter Q,
        c t * (weight r χ * F i j k r χ t)))
    (hblock : ∀ i ∈ Finset.range k₁,
      ∀ j ∈ Finset.range k₂, ∀ k ∈ Finset.range k₃,
        (∫ t in Set.Icc (-U) U,
          ‖∑ r : R, ∑ χ : BlueprintCharacter Q,
            c t * (weight r χ * F i j k r χ t)‖ ∂volume) ≤ K)
    (hcount₁ : k₁ ≤ J₀) (hcount₂ : k₂ ≤ J₀) (hcount₃ : k₃ ≤ J₀)
    (hK : 0 ≤ K) :
    (∫ t in Set.Icc (-U) U,
      ‖c t * (∑ r : R, ∑ χ : BlueprintCharacter Q,
        weight r χ * G r χ t)‖ ∂volume) ≤ (J₀ : ℝ) ^ 3 * K := by
  let Fblock : ℕ → ℕ → ℕ → ℝ → ℂ := fun i j k t =>
    ∑ r : R, ∑ χ : BlueprintCharacter Q,
      c t * (weight r χ * F i j k r χ t)
  have hsource : ∀ t : ℝ,
      c t * (∑ r : R, ∑ χ : BlueprintCharacter Q,
        weight r χ * G r χ t) =
      ∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃, Fblock i j k t := by
    intro t
    simpa [Fblock] using
      weightedAllocationSource_eq_tripleDyadicBlockSum
        k₁ k₂ k₃ c weight G F hdecomp t
  have hFcont : ∀ i j k, Continuous (Fblock i j k) := by
    intro i j k
    exact hcont i j k
  have hFblock : ∀ i ∈ Finset.range k₁,
      ∀ j ∈ Finset.range k₂, ∀ k ∈ Finset.range k₃,
        (∫ t in Set.Icc (-U) U, ‖Fblock i j k t‖ ∂volume) ≤ K := hblock
  exact integral_norm_of_pointwise_tripleDyadicBlockSum_le_of_count_bound
    k₁ k₂ k₃ J₀ U K
    (fun t => c t * (∑ r : R, ∑ χ : BlueprintCharacter Q,
      weight r χ * G r χ t)) Fblock hsource hFcont hFblock
    hcount₁ hcount₂ hcount₃ hK

#print axioms weightedAllocationSource_eq_tripleDyadicBlockSum
#print axioms integral_norm_finsetSum_le_sum_integral_norm
#print axioms integral_norm_tripleDyadicBlockSum_le
#print axioms integral_norm_tripleDyadicBlockSum_le_of_count_bound
#print axioms integral_norm_of_pointwise_tripleDyadicBlockSum_le_of_count_bound
#print axioms integral_norm_weightedAllocationSource_le_of_count_bound

end FractionalPrimes.Literature.DirichletMean

end
