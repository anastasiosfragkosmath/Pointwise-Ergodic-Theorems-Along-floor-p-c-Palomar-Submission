module

public import FractionalPrimes.AdjointKernel

@[expose] public section

/-!
# The finite `ℓ²(ℤ)` convolution-adjoint pairing

This file packages the literal finite-support reindexing step from the
blueprint as an equality in Lean's `lp` Hilbert space.  It deliberately stops
before any density or general-operator extension.
-/

namespace FractionalPrimes

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Pairing against a finitely supported sequence in Lean's complex `ℓ²`
space.  Lean's inner product is conjugate-linear in its first argument and
linear in its second. -/
theorem inner_right_finiteIntegerSequenceL2
    (q : lp (fun _ : ℤ => ℂ) 2) (t : Finset ℤ) (b : ℤ → ℂ) :
    inner ℂ q (finiteIntegerSequenceL2 t b) =
      ∑ k ∈ t, b k * starRingEnd ℂ (q k) := by
  rw [lp.inner_eq_tsum]
  have hzero (k : ℤ) (hk : k ∉ t) :
      inner ℂ (q k) (finiteIntegerSequenceL2 t b k) = 0 := by
    simp [finiteIntegerSequenceL2_apply, hk]
  rw [tsum_eq_sum (s := t) hzero]
  apply Finset.sum_congr rfl
  intro k hk
  simp [finiteIntegerSequenceL2_apply, hk, RCLike.inner_apply]

/-- Pairing a finitely supported sequence against an arbitrary `ℓ²` vector.
The displayed order reflects Lean's conjugate-linear-first inner-product
convention. -/
theorem inner_left_finiteIntegerSequenceL2
    (u : Finset ℤ) (c : ℤ → ℂ) (q : lp (fun _ : ℤ => ℂ) 2) :
    inner ℂ (finiteIntegerSequenceL2 u c) q =
      ∑ k ∈ u, q k * starRingEnd ℂ (c k) := by
  rw [lp.inner_eq_tsum]
  have hzero (k : ℤ) (hk : k ∉ u) :
      inner ℂ (finiteIntegerSequenceL2 u c k) (q k) = 0 := by
    simp [finiteIntegerSequenceL2_apply, hk]
  rw [tsum_eq_sum (s := u) hzero]
  apply Finset.sum_congr rfl
  intro k hk
  simp [finiteIntegerSequenceL2_apply, hk, RCLike.inner_apply]

/-- Membership in a finite support translated by subtraction. -/
theorem mem_subtractEmbedding_map_iff (u : Finset ℤ) (m y : ℤ) :
    y ∈ u.map (subtractEmbedding m) ↔ y + m ∈ u := by
  constructor
  · intro hy
    rcases Finset.mem_map.1 hy with ⟨x, hx, hxy⟩
    change x - m = y at hxy
    have : x = y + m := by omega
    simpa [this] using hx
  · intro hy
    apply Finset.mem_map.2
    refine ⟨y + m, ?_, ?_⟩
    · simpa using hy
    · change y + m - m = y
      omega

private theorem sum_finite_shift_pairing
    (t u : Finset ℤ) (b c : ℤ → ℂ) (m : ℤ) (A : ℂ) :
    (∑ y ∈ u.map (subtractEmbedding m),
      finiteIntegerSequenceL2 t b y *
        starRingEnd ℂ (A * finiteIntegerSequenceL2 u c (y + m))) =
      ∑ y ∈ t,
        finiteIntegerSequenceL2 t b y *
          starRingEnd ℂ (A * finiteIntegerSequenceL2 u c (y + m)) := by
  let v := u.map (subtractEmbedding m)
  let H : ℤ → ℂ := fun y =>
    finiteIntegerSequenceL2 t b y *
      starRingEnd ℂ (A * finiteIntegerSequenceL2 u c (y + m))
  have hleft : (∑ y ∈ v, H y) = ∑ y ∈ v ∩ t, H y := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro y hy hyt
    have hyt' : y ∉ t := by
      intro hyt'
      exact hyt (Finset.mem_inter.mpr ⟨hy, hyt'⟩)
    dsimp [H]
    rw [finiteIntegerSequenceL2_apply]
    simp [hyt']
  have hright : (∑ y ∈ v ∩ t, H y) = ∑ y ∈ t, H y := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro y hyt hyv
    have hyv' : y ∉ v := by
      intro hyv'
      exact hyv (Finset.mem_inter.mpr ⟨hyv', hyt⟩)
    have hyu : y + m ∉ u := by
      intro hyu
      exact hyv' (mem_subtractEmbedding_map_iff u m y |>.mpr hyu)
    dsimp [H]
    have hGzero : finiteIntegerSequenceL2 u c (y + m) = 0 := by
      simp [finiteIntegerSequenceL2_apply, hyu]
    simp [hGzero]
  change (∑ y ∈ v, H y) = ∑ y ∈ t, H y
  exact hleft.trans hright

/-- The finite convolution formed from the reflected, conjugated coefficient
support evaluates as the explicit adjoint sum. -/
theorem finite_adjoint_convolution_apply
    (s u : Finset ℤ) (a c : ℤ → ℂ) (y : ℤ) :
    finiteDiscreteConvolutionSequenceL2
        (s.map (Equiv.neg ℤ).toEmbedding) u
        (fun n => starRingEnd ℂ (a (-n))) c y =
      ∑ m ∈ s, starRingEnd ℂ (a m) *
        finiteIntegerSequenceL2 u c (y + m) := by
  rw [finiteDiscreteConvolutionSequenceL2_apply_eq_sum]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro m hm
  change starRingEnd ℂ (a (-(-m))) *
      finiteIntegerSequenceL2 u c (y - (-m)) =
    starRingEnd ℂ (a m) *
      finiteIntegerSequenceL2 u c (y + m)
  simp

/-- The exact finite-support convolution-adjoint pairing in `ℓ²(ℤ)`.

Lean uses the convention that `inner ℂ x y` is conjugate-linear in `x` and
linear in `y`; therefore this is the formal counterpart of
`⟪g, T_a f⟫ = ⟪T_a^* g, f⟫`.  The reflected coefficient support and the
coefficient function `n ↦ conj (a (-n))` are exactly the finite adjoint
kernel.  This is only the finite-support step of the blueprint, not a density
or general-operator identity. -/
theorem finiteDiscreteConvolutionSequenceL2_pairing_adjoint
    (s t u : Finset ℤ) (a b c : ℤ → ℂ) :
    inner ℂ (finiteIntegerSequenceL2 u c)
        (finiteDiscreteConvolutionSequenceL2 s t a b) =
      inner ℂ
        (finiteDiscreteConvolutionSequenceL2
          (s.map (Equiv.neg ℤ).toEmbedding) u
          (fun n => starRingEnd ℂ (a (-n))) c)
        (finiteIntegerSequenceL2 t b) := by
  let F := finiteIntegerSequenceL2 t b
  let G := finiteIntegerSequenceL2 u c
  let C := finiteDiscreteConvolutionSequenceL2 s t a b
  let Cadj := finiteDiscreteConvolutionSequenceL2
    (s.map (Equiv.neg ℤ).toEmbedding) u
    (fun n => starRingEnd ℂ (a (-n))) c
  change inner ℂ G C = inner ℂ Cadj F
  calc
    inner ℂ G C = ∑ x ∈ u,
        (∑ m ∈ s, a m * F (x - m)) * starRingEnd ℂ (G x) := by
      rw [inner_left_finiteIntegerSequenceL2]
      apply Finset.sum_congr rfl
      intro x hx
      have hC := finiteDiscreteConvolutionSequenceL2_apply_eq_sum s t a b x
      dsimp [C, F, G]
      rw [hC]
      simp [finiteIntegerSequenceL2_apply, hx]
    _ = ∑ m ∈ s, ∑ y ∈ u.map (subtractEmbedding m),
        F y * starRingEnd ℂ (starRingEnd ℂ (a m) * G (y + m)) := by
      exact finite_kernel_pairing_reindex s u a F G
    _ = ∑ m ∈ s, ∑ y ∈ t,
        F y * starRingEnd ℂ (starRingEnd ℂ (a m) * G (y + m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact sum_finite_shift_pairing t u b c m (starRingEnd ℂ (a m))
    _ = ∑ y ∈ t, b y * starRingEnd ℂ
        (∑ m ∈ s, starRingEnd ℂ (a m) * G (y + m)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      have hF : F y = b y := by
        dsimp [F]
        simp [finiteIntegerSequenceL2_apply, hy]
      rw [hF, map_sum, Finset.mul_sum]
    _ = ∑ y ∈ t, b y * starRingEnd ℂ (Cadj y) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [finite_adjoint_convolution_apply]
    _ = inner ℂ Cadj F := by
      rw [inner_right_finiteIntegerSequenceL2]

end

end FractionalPrimes

