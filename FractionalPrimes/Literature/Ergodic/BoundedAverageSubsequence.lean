module

public import FractionalPrimes.Literature.Ergodic.BoundedAverageGap
public import Mathlib.Data.Nat.Find

@[expose] public section
namespace FractionalPrimes
open Filter
open scoped Topology
noncomputable section

/-- All-scale completion of the bounded-input subsequence argument. Repeated
subsequence scales are allowed, as in floor(2^sqrt(k)). -/
theorem boundedPrefixAverage_tendsto_zero_of_subsequence
    (a : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ B)
    (t : ℕ → ℕ) (htpos : ∀ k, 0 < t k) (htmono : Monotone t)
    (htop : Tendsto t atTop atTop)
    (hgap : Tendsto (fun k : ℕ =>
      ((t (k + 1) : ℝ) - t k) / t k) atTop (𝓝 0))
    (hsub : Tendsto (fun k : ℕ =>
      (t k : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc 0 (t k), a n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc 0 N, a n)
      atTop (𝓝 0) := by
  have hex (N : ℕ) : ∃ k : ℕ, N < t k :=
    (htop.eventually (eventually_gt_atTop N)).exists
  let cross : ℕ → ℕ := fun N => Nat.find (hex N)
  let last : ℕ → ℕ := fun N => cross N - 1
  have hcross (N : ℕ) : N < t (cross N) := Nat.find_spec (hex N)
  have hlastTop : Tendsto last atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (t (b + 1))] with N hN
    have hcrossLarge : b + 1 < cross N := by
      by_contra hc
      have := htmono (Nat.le_of_not_gt hc)
      have := hcross N
      omega
    dsimp [last]
    omega
  have hbracket : ∀ᶠ N : ℕ in atTop,
      t (last N) ≤ N ∧ N ≤ t (last N + 1) := by
    filter_upwards [eventually_ge_atTop (t 0)] with N hN
    have hcpos : 0 < cross N := by
      by_contra hc
      have hc0 : cross N = 0 := by omega
      have := hcross N
      rw [hc0] at this
      omega
    have hprev : ¬ N < t (cross N - 1) :=
      Nat.find_min (hex N) (by change cross N - 1 < cross N; omega)
    have hnext : last N + 1 = cross N := by dsimp [last]; omega
    exact ⟨Nat.le_of_not_gt hprev, by rw [hnext]; exact (hcross N).le⟩
  have hmajor : Tendsto (fun N : ℕ =>
      2 * (((t (last N + 1) : ℝ) - t (last N)) / t (last N)) * B +
        ‖(t (last N) : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc 0 (t (last N)), a n‖)
      atTop (𝓝 0) := by
    simpa using (((hgap.comp hlastTop).const_mul 2).mul_const B).add
      ((hsub.comp hlastTop).norm)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
  filter_upwards [hbracket] with N hN
  have hM : (0 : ℝ) < t (last N) := by exact_mod_cast htpos (last N)
  have hNR : (0 : ℝ) < N := lt_of_lt_of_le hM (by exact_mod_cast hN.1)
  have hMN : (t (last N) : ℝ) ≤ N := by exact_mod_cast hN.1
  have hNU : (N : ℝ) ≤ t (last N + 1) := by exact_mod_cast hN.2
  have hratio : ((N : ℝ) - t (last N)) / N ≤
      ((t (last N + 1) : ℝ) - t (last N)) / t (last N) := by
    apply (div_le_div_iff₀ hNR hM).mpr
    have := mul_nonneg (sub_nonneg.mpr hMN)
      (sub_nonneg.mpr (hMN.trans hNU))
    nlinarith
  have hdiff := boundedPrefixAverage_gap_le a B hB (htpos (last N)) hN.1
    (fun n hn => ha n (by have := (Finset.mem_Ioc.mp hn).1; omega))
  calc
    _ ≤ ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.Ioc 0 N, a n) -
          (t (last N) : ℂ)⁻¹ * (∑ n ∈ Finset.Ioc 0 (t (last N)), a n)‖ +
        ‖(t (last N) : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc 0 (t (last N)), a n‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ 2 * ((N : ℝ) - t (last N)) / N * B +
        ‖(t (last N) : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc 0 (t (last N)), a n‖ :=
      add_le_add hdiff le_rfl
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)) hB
      simpa only [mul_div_assoc] using this

#print axioms boundedPrefixAverage_tendsto_zero_of_subsequence
end
end FractionalPrimes
