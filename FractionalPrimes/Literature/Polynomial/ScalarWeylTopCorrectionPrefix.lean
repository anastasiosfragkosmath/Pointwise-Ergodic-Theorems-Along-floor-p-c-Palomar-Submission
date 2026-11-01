module

public import FractionalPrimes.Literature.Polynomial.ScalarWeyl

/-!
# Rational top-coefficient correction and an initial Abel prefix

This is the finite Abel step in `lbi:weyl-inverse`: a top-coefficient
distance bound gives a nearest rational correction, and a variation budget
for the remaining phase transfers a large weighted sum to an initial prefix.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- Generic finite Abel extraction. The norm of the final multiplier value
plus its discrete variation controls the weighted sum by the largest initial
partial sum. -/
private theorem scalarWeyl_prefixOfWeightedSum
    {L : ℕ} {A W : ℝ} (hA : 0 < A) (hW : 0 < W)
    (u v : ℕ → ℂ)
    (hlarge : A ≤ ‖∑ j ∈ Finset.range L, u j * v j‖)
    (hvariation : ‖v (L - 1)‖ +
      ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖ ≤ W) :
    ∃ k : ℕ, k < L ∧
      A / W ≤ ‖∑ j ∈ Finset.range (k + 1), u j‖ := by
  by_cases hLzero : L = 0
  · subst L
    simp at hlarge
    linarith
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hLzero
    have hLone : 1 ≤ L := hLpos
    have hrange : (Finset.range L).Nonempty :=
      ⟨0, Finset.mem_range.mpr hLpos⟩
    let M : ℝ := (Finset.range L).sup' hrange
      (fun k => ‖∑ j ∈ Finset.range (k + 1), u j‖)
    have hprefix_le (k : ℕ) (hk : k < L) :
        ‖∑ j ∈ Finset.range (k + 1), u j‖ ≤ M := by
      dsimp [M]
      exact Finset.le_sup' (s := Finset.range L)
        (f := fun k => ‖∑ j ∈ Finset.range (k + 1), u j‖)
        (Finset.mem_range.mpr hk)
    obtain ⟨k, hk, hMk⟩ := Finset.exists_mem_eq_sup' hrange
      (fun k => ‖∑ j ∈ Finset.range (k + 1), u j‖)
    have hklt : k < L := Finset.mem_range.mp hk
    have hMnonneg : 0 ≤ M := by
      exact le_trans (norm_nonneg _) (hprefix_le 0 hLpos)
    have hfull : ‖∑ j ∈ Finset.range L, u j‖ ≤ M := by
      have hlen : (L - 1) + 1 = L := Nat.sub_add_cancel hLone
      simpa only [hlen] using hprefix_le (L - 1)
        (Nat.sub_lt hLpos (by norm_num))
    have habel := Finset.sum_range_by_parts' (f := u) (g := v) (n := L)
    have habel' :
        (∑ j ∈ Finset.range L, u j * v j) =
          (∑ j ∈ Finset.range L, u j) * v (L - 1) -
            ∑ i ∈ Finset.range (L - 1),
              (∑ j ∈ Finset.range (i + 1), u j) *
                (v (i + 1) - v i) := by
      simpa only [smul_eq_mul] using habel
    have hterm : ∀ i ∈ Finset.range (L - 1),
        ‖(∑ j ∈ Finset.range (i + 1), u j) *
            (v (i + 1) - v i)‖ ≤ M * ‖v (i + 1) - v i‖ := by
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hprefix_le i (by have := Finset.mem_range.mp hi; omega))
        (norm_nonneg _)
    have hsum :
        ‖∑ i ∈ Finset.range (L - 1),
            (∑ j ∈ Finset.range (i + 1), u j) *
              (v (i + 1) - v i)‖ ≤
          M * ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖ := by
      calc
        _ ≤ ∑ i ∈ Finset.range (L - 1),
            ‖(∑ j ∈ Finset.range (i + 1), u j) *
              (v (i + 1) - v i)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (L - 1),
            M * ‖v (i + 1) - v i‖ :=
          Finset.sum_le_sum fun i hi => hterm i hi
        _ = M * ∑ i ∈ Finset.range (L - 1),
            ‖v (i + 1) - v i‖ := by rw [Finset.mul_sum]
    have hweighted :
        ‖∑ j ∈ Finset.range L, u j * v j‖ ≤
          M * (‖v (L - 1)‖ +
            ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖) := by
      rw [habel']
      calc
        _ ≤ ‖(∑ j ∈ Finset.range L, u j) * v (L - 1)‖ +
            ‖∑ i ∈ Finset.range (L - 1),
              (∑ j ∈ Finset.range (i + 1), u j) *
                (v (i + 1) - v i)‖ := norm_sub_le _ _
        _ ≤ M * ‖v (L - 1)‖ +
            M * ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖ := by
          apply add_le_add
          · rw [norm_mul]
            exact mul_le_mul_of_nonneg_right hfull (norm_nonneg _)
          · exact hsum
        _ = _ := by ring
    have hlarge' : A ≤ M * W := by
      calc
        A ≤ ‖∑ j ∈ Finset.range L, u j * v j‖ := hlarge
        _ ≤ M * (‖v (L - 1)‖ +
            ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖) := hweighted
        _ ≤ M * W :=
          mul_le_mul_of_nonneg_left hvariation hMnonneg
    have hAM : A / W ≤ M := (div_le_iff₀ hW).2 hlarge'
    refine ⟨k, hklt, ?_⟩
    calc
      A / W ≤ M := hAM
      _ = ‖∑ j ∈ Finset.range (k + 1), u j‖ := by
        dsimp [M] at hMk ⊢
        exact hMk

/-- The source top-coefficient bound gives a nearest rational correction.
After removing that rational top phase, any variation bound of `1 + 8R` and
the original large sum yield an initial prefix with the exact loss `1 + 8R`.
The sequence `t` records the integer points of the source interval in their
order; its range is assumed to lie in `[1,N]` by the caller who establishes
the monomial-phase variation bound. -/
theorem scalarWeyl_topCorrection_initialPrefix
    {N d r L : ℕ} {R αd A : ℝ}
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hR : 0 ≤ R) (hA : 0 < A)
    (hdist : realDistanceToIntegers ((r : ℝ) * αd) ≤
      R / ((N : ℝ) ^ d))
    (t : ℕ → ℝ) (f : ℕ → ℂ)
    (hlarge : A ≤ ‖∑ j ∈ Finset.range L,
      f j * unitFrequencyPhase (αd * t j ^ d)‖)
    (hvariation : ∀ θ : ℝ,
      |θ| ≤ R / ((r : ℝ) * (N : ℝ) ^ d) →
        ‖unitFrequencyPhase (θ * t (L - 1) ^ d)‖ +
          ∑ i ∈ Finset.range (L - 1),
            ‖unitFrequencyPhase (θ * t (i + 1) ^ d) -
              unitFrequencyPhase (θ * t i ^ d)‖ ≤ 1 + 8 * R) :
    ∃ a : ℤ, ∃ k : ℕ,
      k < L ∧
      |αd - (a : ℝ) / (r : ℝ)| ≤
        R / ((r : ℝ) * (N : ℝ) ^ d) ∧
      A / (1 + 8 * R) ≤
        ‖∑ j ∈ Finset.range (k + 1),
          f j * unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * t j ^ d)‖ := by
  obtain ⟨a, ha⟩ :=
    exists_int_abs_sub_le_of_realDistanceToIntegers_le hdist
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNpowpos : 0 < (N : ℝ) ^ d := pow_pos hNpos _
  have harg :
      αd - (a : ℝ) / (r : ℝ) =
        ((r : ℝ) * αd - (a : ℝ)) / (r : ℝ) := by
    field_simp [ne_of_gt hrpos]
    <;> ring
  have habs :
      |αd - (a : ℝ) / (r : ℝ)| =
        |(r : ℝ) * αd - (a : ℝ)| / (r : ℝ) := by
    calc
      |αd - (a : ℝ) / (r : ℝ)| =
          |((r : ℝ) * αd - (a : ℝ)) / (r : ℝ)| := by rw [harg]
      _ = |(r : ℝ) * αd - (a : ℝ)| / |(r : ℝ)| := abs_div _ _
      _ = |(r : ℝ) * αd - (a : ℝ)| / (r : ℝ) := by
        rw [abs_of_pos hrpos]
  have hquot :
      (R / ((N : ℝ) ^ d)) / (r : ℝ) =
        R / ((r : ℝ) * (N : ℝ) ^ d) := by
    field_simp [ne_of_gt hrpos, ne_of_gt hNpowpos]
    <;> ring
  have happrox : |αd - (a : ℝ) / (r : ℝ)| ≤
      R / ((r : ℝ) * (N : ℝ) ^ d) := by
    calc
      |αd - (a : ℝ) / (r : ℝ)| =
          |(r : ℝ) * αd - (a : ℝ)| / (r : ℝ) := habs
      _ ≤ (R / ((N : ℝ) ^ d)) / (r : ℝ) :=
        div_le_div_of_nonneg_right ha hrpos.le
      _ = R / ((r : ℝ) * (N : ℝ) ^ d) := hquot
  let θ : ℝ := αd - (a : ℝ) / (r : ℝ)
  have hθ : |θ| ≤ R / ((r : ℝ) * (N : ℝ) ^ d) := by simpa [θ] using happrox
  let u : ℕ → ℂ := fun j =>
    f j * unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * t j ^ d)
  let v : ℕ → ℂ := fun j => unitFrequencyPhase (θ * t j ^ d)
  have hsum :
      (∑ j ∈ Finset.range L, f j * unitFrequencyPhase (αd * t j ^ d)) =
        ∑ j ∈ Finset.range L, u j * v j := by
    apply Finset.sum_congr rfl
    intro j hj
    have harg : αd * t j ^ d =
        ((a : ℝ) / (r : ℝ)) * t j ^ d + θ * t j ^ d := by
      dsimp [θ]
      ring
    simp only [u, v]
    rw [harg, unitFrequencyPhase_add]
    ring
  have hlarge' : A ≤ ‖∑ j ∈ Finset.range L, u j * v j‖ := by
    rw [← hsum]
    exact hlarge
  have hvariation' :
      ‖v (L - 1)‖ +
        ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖ ≤ 1 + 8 * R := by
    simpa [v] using hvariation θ hθ
  have hW : 0 < 1 + 8 * R := by linarith
  obtain ⟨k, hk, hprefix⟩ :=
    scalarWeyl_prefixOfWeightedSum hA hW u v hlarge' hvariation'
  refine ⟨a, k, hk, happrox, ?_⟩
  simpa [u] using hprefix

end FractionalPrimes.Literature.Polynomial

end
