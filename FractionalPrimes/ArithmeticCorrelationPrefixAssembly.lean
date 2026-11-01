module
public import FractionalPrimes.ArithmeticDyadicCorrelationAssembly
public import Mathlib.Analysis.SpecialFunctions.Sqrt
@[expose] public section

/-!
# Whole-prefix arithmetic correlation from the dyadic estimate

The source dyadic proposition is assembled over natural intervals `(K,K']`.
This file first records the exact finite doubling partition needed to pass
from those intervals to a prefix, with one final partial block.
-/

namespace FractionalPrimes

open scoped BigOperators

/-- Exact decomposition of a natural interval into consecutive doubling
blocks and a final partial interval. -/
theorem sum_Ioc_doubling_partition {α : Type*} [AddCommMonoid α]
    (K N J : ℕ) (hKN : K * 2 ^ J ≤ N) (f : ℕ → α) :
    (∑ n ∈ Finset.Ioc K N, f n) =
      (∑ v ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (K * 2 ^ v) (K * 2 ^ (v + 1)), f n) +
      (∑ n ∈ Finset.Ioc (K * 2 ^ J) N, f n) := by
  induction J generalizing K N with
  | zero =>
      simp
  | succ J ih =>
      have hpowOne : 1 ≤ 2 ^ J := Nat.one_le_pow J 2 (by omega)
      have hpowTwo : 2 ≤ 2 ^ (J + 1) := by
        rw [pow_succ]
        nlinarith [hpowOne]
      have hstartle : K * 2 ≤ K * 2 ^ (J + 1) :=
        Nat.mul_le_mul_left K hpowTwo
      have hmid : K * 2 ≤ N := hstartle.trans hKN
      have hrestEq : (K * 2) * 2 ^ J = K * 2 ^ (J + 1) := by
        rw [pow_succ]
        ring
      have hrest : (K * 2) * 2 ^ J ≤ N := by
        rw [hrestEq]
        exact hKN
      have hshift :
          (∑ v ∈ Finset.range J,
            ∑ n ∈ Finset.Ioc ((K * 2) * 2 ^ v) ((K * 2) * 2 ^ (v + 1)), f n) =
          ∑ v ∈ Finset.range J,
            ∑ n ∈ Finset.Ioc (K * 2 ^ (v + 1))
              (K * 2 ^ ((v + 1) + 1)), f n := by
        apply Finset.sum_congr rfl
        intro v hv
        have hlo : (K * 2) * 2 ^ v = K * 2 ^ (v + 1) := by
          rw [pow_succ]
          ring
        have hhi : (K * 2) * 2 ^ (v + 1) = K * 2 ^ (v + 2) := by
          rw [show v + 2 = (v + 1) + 1 by omega, pow_succ]
          ring
        rw [hlo, hhi]
      have hrange :
          (∑ n ∈ Finset.Ioc K (K * 2), f n) +
            (∑ v ∈ Finset.range J,
              ∑ n ∈ Finset.Ioc (K * 2 ^ (v + 1))
                (K * 2 ^ ((v + 1) + 1)), f n) =
          ∑ v ∈ Finset.range (J + 1),
            ∑ n ∈ Finset.Ioc (K * 2 ^ v) (K * 2 ^ (v + 1)), f n := by
        have hs := Finset.sum_range_succ'
          (fun v => ∑ n ∈ Finset.Ioc (K * 2 ^ v) (K * 2 ^ (v + 1)), f n) J
        simpa [Nat.zero_add, add_comm] using hs.symm
      calc
        (∑ n ∈ Finset.Ioc K N, f n) =
            (∑ n ∈ Finset.Ioc K (K * 2), f n) +
              (∑ n ∈ Finset.Ioc (K * 2) N, f n) := by
          symm
          exact Finset.sum_Ioc_consecutive f (by omega) hmid
        _ = (∑ n ∈ Finset.Ioc K (K * 2), f n) +
              ((∑ v ∈ Finset.range J,
                ∑ n ∈ Finset.Ioc ((K * 2) * 2 ^ v)
                  ((K * 2) * 2 ^ (v + 1)), f n) +
                (∑ n ∈ Finset.Ioc ((K * 2) * 2 ^ J) N, f n)) := by
          rw [ih (K * 2) N hrest]
        _ = (∑ v ∈ Finset.range (J + 1),
              ∑ n ∈ Finset.Ioc (K * 2 ^ v) (K * 2 ^ (v + 1)), f n) +
              (∑ n ∈ Finset.Ioc (K * 2 ^ (J + 1)) N, f n) := by
          rw [hshift, ← hrange, hrestEq]
          abel

/-- The sum of the starting scales in a finite doubling chain is at most
twice its last starting scale. -/
theorem sum_doubling_scales_le_two_last (K J : ℕ) :
    (∑ v ∈ Finset.range (J + 1), K * 2 ^ v) ≤ 2 * (K * 2 ^ J) := by
  induction J with
  | zero => simp; omega
  | succ J ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ v ∈ Finset.range (J + 1), K * 2 ^ v) + K * 2 ^ (J + 1) ≤
            2 * (K * 2 ^ J) + K * 2 ^ (J + 1) :=
          add_le_add ih le_rfl
        _ = 2 * (K * 2 ^ (J + 1)) := by
          rw [pow_succ]
          ring

/-- Right endpoint of the doubling partition, with its final block truncated
at `N`. -/
private def doublingRight (K N J v : ℕ) : ℕ :=
  if v < J then K * 2 ^ (v + 1) else N

/-- The natural prefix is its initial segment followed by the full doubling
blocks and the final partial block. -/
private theorem sum_Ioc_doubling_blocks {α : Type*} [AddCommMonoid α]
    (K N J : ℕ) (hK : K ≤ N) (hKN : K * 2 ^ J ≤ N) (f : ℕ → α) :
    (∑ n ∈ Finset.Ioc 0 N, f n) =
      (∑ n ∈ Finset.Ioc 0 K, f n) +
        ∑ v ∈ Finset.range (J + 1),
          ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n := by
  have hprefix :
      (∑ n ∈ Finset.Ioc 0 N, f n) =
        (∑ n ∈ Finset.Ioc 0 K, f n) +
          ∑ n ∈ Finset.Ioc K N, f n := by
    rw [← Finset.sum_Ioc_consecutive f (Nat.zero_le K) hK]
  rw [sum_Ioc_doubling_partition K N J hKN f] at hprefix
  have hblocks :
      (∑ v ∈ Finset.range (J + 1),
        ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n) =
        (∑ v ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (K * 2 ^ v) (K * 2 ^ (v + 1)), f n) +
          ∑ n ∈ Finset.Ioc (K * 2 ^ J) N, f n := by
    rw [Finset.sum_range_succ]
    have hfull :
        (∑ v ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n) =
          ∑ v ∈ Finset.range J,
            ∑ n ∈ Finset.Ioc (K * 2 ^ v) (K * 2 ^ (v + 1)), f n := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvJ : v < J := Finset.mem_range.mp hv
      simp [doublingRight, hvJ]
    rw [hfull]
    simp [doublingRight]
  rw [← hblocks] at hprefix
  exact hprefix

/-- Triangle inequality for the two coefficient sums over a dyadic prefix. -/
private theorem norm_prefix_le_initial_add_blocks
    (K N J : ℕ) (hK : K ≤ N) (hKN : K * 2 ^ J ≤ N)
    (f g : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Ioc 0 N, f n‖ + ‖∑ n ∈ Finset.Ioc 0 N, g n‖ ≤
      ‖∑ n ∈ Finset.Ioc 0 K, f n‖ + ‖∑ n ∈ Finset.Ioc 0 K, g n‖ +
        ∑ v ∈ Finset.range (J + 1),
          (‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n‖ +
            ‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n‖) := by
  rw [sum_Ioc_doubling_blocks K N J hK hKN f,
      sum_Ioc_doubling_blocks K N J hK hKN g]
  calc
    _ ≤ (‖∑ n ∈ Finset.Ioc 0 K, f n‖ +
          ‖∑ v ∈ Finset.range (J + 1),
            ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n‖) +
        (‖∑ n ∈ Finset.Ioc 0 K, g n‖ +
          ‖∑ v ∈ Finset.range (J + 1),
            ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n‖) :=
      add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ _ := by
      have hf := norm_sum_le (Finset.range (J + 1))
        (fun v => ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n)
      have hg := norm_sum_le (Finset.range (J + 1))
        (fun v => ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n)
      calc
        _ = (‖∑ n ∈ Finset.Ioc 0 K, f n‖ + ‖∑ n ∈ Finset.Ioc 0 K, g n‖) +
              (‖∑ v ∈ Finset.range (J + 1),
                ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n‖ +
               ‖∑ v ∈ Finset.range (J + 1),
                ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n‖) := by
          ac_rfl
        _ ≤ (‖∑ n ∈ Finset.Ioc 0 K, f n‖ + ‖∑ n ∈ Finset.Ioc 0 K, g n‖) +
              ((∑ v ∈ Finset.range (J + 1),
                ‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n‖) +
               (∑ v ∈ Finset.range (J + 1),
                ‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n‖)) := by
          have hfg := add_le_add hf hg
          calc
            _ = (‖∑ v ∈ Finset.range (J + 1),
                  ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n‖ +
                 ‖∑ v ∈ Finset.range (J + 1),
                  ∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n‖) +
                (‖∑ n ∈ Finset.Ioc 0 K, f n‖ + ‖∑ n ∈ Finset.Ioc 0 K, g n‖) := by
              ac_rfl
            _ ≤ _ := add_le_add_left hfg _
            _ = _ := by ac_rfl
        _ = _ := by rw [← Finset.sum_add_distrib]

/-- A natural cutoff just above half the square root, followed by its exact
maximal doubling chain, leaves a final interval of length at most the last
starting scale. -/
private theorem exists_natural_doubling_cutoff {N : ℕ} (hN : 36 ≤ N) :
    ∃ K J : ℕ, 3 ≤ K ∧ Real.sqrt (N : ℝ) / 2 < (K : ℝ) ∧
      (K : ℝ) ≤ Real.sqrt (N : ℝ) ∧ K * 2 ^ J ≤ N ∧
      N ≤ 2 * (K * 2 ^ J) := by
  have hNreal : (36 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hsqrt6 : (6 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have h := Real.sqrt_le_sqrt hNreal
    norm_num at h ⊢
    exact h
  let K : ℕ := Nat.floor (Real.sqrt (N : ℝ) / 2) + 1
  have hKlower : Real.sqrt (N : ℝ) / 2 < (K : ℝ) := by
    simpa [K, Nat.cast_add] using Nat.lt_floor_add_one
      (Real.sqrt (N : ℝ) / 2)
  have hfloor :
      ((Nat.floor (Real.sqrt (N : ℝ) / 2) : ℕ) : ℝ) ≤
        Real.sqrt (N : ℝ) / 2 := Nat.floor_le (by positivity)
  have hhalfOne : (1 : ℝ) ≤ Real.sqrt (N : ℝ) / 2 := by nlinarith [hsqrt6]
  have hKupper : (K : ℝ) ≤ Real.sqrt (N : ℝ) := by
    calc
      (K : ℝ) = (Nat.floor (Real.sqrt (N : ℝ) / 2) : ℝ) + 1 := by simp [K]
      _ ≤ Real.sqrt (N : ℝ) / 2 + 1 := by
        simpa [add_comm] using add_le_add_left hfloor 1
      _ ≤ 2 * (Real.sqrt (N : ℝ) / 2) := by linarith [hhalfOne]
      _ = Real.sqrt (N : ℝ) := by ring
  have hKthreeReal : (3 : ℝ) ≤ (K : ℝ) := by
    have hthree : (3 : ℝ) ≤ Real.sqrt (N : ℝ) / 2 := by nlinarith [hsqrt6]
    exact hthree.trans (le_of_lt hKlower)
  have hKthree : 3 ≤ K := by exact_mod_cast hKthreeReal
  have hsqrtle : Real.sqrt (N : ℝ) ≤ (N : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hNge1)
  have hKNreal : (K : ℝ) ≤ (N : ℝ) := hKupper.trans hsqrtle
  have hKN : K ≤ N := by exact_mod_cast hKNreal
  have hKpos : 0 < K := by omega
  have hqpos : N / K ≠ 0 := (Nat.div_pos hKN hKpos).ne'
  let J : ℕ := Nat.log 2 (N / K)
  have hqLower : 2 ^ J ≤ N / K := by
    dsimp [J]
    exact Nat.pow_log_le_self 2 hqpos
  have hdivMul : (N / K) * K ≤ N := Nat.div_mul_le_self N K
  have hstart : K * 2 ^ J ≤ N := by
    calc
      K * 2 ^ J ≤ K * (N / K) := Nat.mul_le_mul_left K hqLower
      _ = (N / K) * K := Nat.mul_comm _ _
      _ ≤ N := hdivMul
  have hqUpper : N / K < 2 ^ (J + 1) := by
    dsimp [J]
    exact Nat.lt_pow_succ_log_self (by norm_num) (N / K)
  have hNlt : N < K * 2 ^ (J + 1) := by
    have h := (Nat.div_lt_iff_lt_mul hKpos).mp hqUpper
    simpa [Nat.mul_comm] using h
  have hdouble : K * 2 ^ (J + 1) = 2 * (K * 2 ^ J) := by
    rw [pow_succ]
    ring
  refine ⟨K, J, hKthree, hKlower, hKupper, hstart, ?_⟩
  rw [← hdouble]
  exact hNlt.le

/-- Beyond one threshold, a logarithmic power is bounded by a small power of
the scale. -/
private theorem exists_log_rpow_le_half {B : ℝ} (_hB : 0 < B) :
    ∃ T : ℝ, 36 ≤ T ∧ ∀ x : ℝ, T ≤ x →
      (Real.log x) ^ B ≤ x ^ (1 / 2 : ℝ) := by
  have hlittle := (paper_log_rpow_isLittleO_rpow (a := B)
    (b := (1 / 2 : ℝ)) (by linarith)).bound
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hlittle
  let T : ℝ := max 36 T₀
  refine ⟨T, le_max_left _ _, ?_⟩
  intro x hx
  have hx36 : 36 ≤ x := le_trans (le_max_left _ _) hx
  have hT₀x : T₀ ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hleftnonneg : 0 ≤ (Real.log x) ^ B := Real.rpow_nonneg hlognonneg B
  have hrightnonneg : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hbound := hT₀ x hT₀x
  have hnorm : ‖(Real.log x) ^ B‖ ≤ ‖x ^ (1 / 2 : ℝ)‖ := by
    simpa only [Real.rpow_one, one_mul] using hbound
  rw [Real.norm_of_nonneg hleftnonneg, Real.norm_of_nonneg hrightnonneg] at hnorm
  exact hnorm

/-- Rescale a negative logarithmic power when the local logarithm is at least
one quarter of the global logarithm. -/
private theorem logPowerScale_bound {A L Q : ℝ}
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hQ : L / 4 ≤ Q) :
    Q ^ (-(A + 1)) ≤ 4 ^ (A + 1) * L ^ (-A) := by
  have hLpos : 0 < L := by linarith
  have hQpos : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hBpos : 0 < A + 1 := by linarith
  have hBnonpos : -(A + 1) ≤ 0 := by linarith
  have hmono : Q ^ (-(A + 1)) ≤ (L / 4) ^ (-(A + 1)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hQ hBnonpos
  have hdiv : (L / 4) ^ (-(A + 1)) =
      4 ^ (A + 1) * L ^ (-(A + 1)) := by
    rw [Real.div_rpow (le_of_lt hLpos) (by norm_num : (0 : ℝ) ≤ 4)]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    have h4 : (4 : ℝ) ^ (A + 1) ≠ 0 :=
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (A + 1)).ne'
    field_simp [h4]
  have hLexp : L ^ (-(A + 1)) ≤ L ^ (-A) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    linarith
  calc
    Q ^ (-(A + 1)) ≤ (L / 4) ^ (-(A + 1)) := hmono
    _ = 4 ^ (A + 1) * L ^ (-(A + 1)) := hdiv
    _ ≤ 4 ^ (A + 1) * L ^ (-A) :=
      mul_le_mul_of_nonneg_left hLexp (Real.rpow_nonneg (by norm_num) _)

private noncomputable def primePrefixTerm (c ξ : ℝ) (n : ℕ) : ℂ :=
  ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
    unitFrequencyPhase (centeredFrequency ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))

private noncomputable def mobiusPrefixTerm (c ξ : ℝ) (n : ℕ) : ℂ :=
  (paperMu (n : ℤ) : ℂ) *
    unitFrequencyPhase (centeredFrequency ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))

private theorem primePrefixTerm_norm_le {c ξ : ℝ} {N n : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖primePrefixTerm c ξ n‖ ≤ 1 + Real.log (N : ℝ) := by
  have hnInt : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  have hLambda := paperLambda_bounds hnInt
  have hnRealPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNReal : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hnRealPos hNReal
  have habs : |paperLambda (n : ℤ) - 1| ≤ 1 + Real.log (N : ℝ) := by
    calc
      |paperLambda (n : ℤ) - 1| ≤ |paperLambda (n : ℤ)| + |(1 : ℝ)| := abs_sub _ _
      _ = paperLambda (n : ℤ) + 1 := by rw [abs_of_nonneg hLambda.1, abs_one]
      _ ≤ Real.log (n : ℝ) + 1 := by
        calc
          _ = 1 + paperLambda (n : ℤ) := by ring
          _ ≤ 1 + Real.log (n : ℝ) := by
            simpa [add_comm] using add_le_add_left hLambda.2 1
          _ = _ := by ring
      _ ≤ 1 + Real.log (N : ℝ) := by
        simpa [add_comm] using add_le_add_left hlog 1
  dsimp [primePrefixTerm]
  rw [norm_mul, norm_unitFrequencyPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact habs

private theorem mobiusPrefixTerm_norm_le {c ξ : ℝ} {n : ℕ}
    (hn : 1 ≤ n) : ‖mobiusPrefixTerm c ξ n‖ ≤ 1 := by
  have hnInt : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  have hμ := paperMu_abs_le_one hnInt
  dsimp [mobiusPrefixTerm]
  rw [norm_mul, norm_unitFrequencyPhase, mul_one, Complex.norm_intCast]
  exact_mod_cast hμ

/-- Elementary control for a prefix by its coefficient sizes. -/
private theorem norm_arithmetic_prefix_trivial_bound {c ξ : ℝ} {N K : ℕ}
    (hK : K ≤ N) :
    ‖∑ n ∈ Finset.Ioc 0 K, primePrefixTerm c ξ n‖ +
      ‖∑ n ∈ Finset.Ioc 0 K, mobiusPrefixTerm c ξ n‖ ≤
        (K : ℝ) * (2 + Real.log (N : ℝ)) := by
  have hpoint : ∀ n ∈ Finset.Ioc 0 K,
      ‖primePrefixTerm c ξ n‖ + ‖mobiusPrefixTerm c ξ n‖ ≤
        2 + Real.log (N : ℝ) := by
    intro n hn
    have hnmem := Finset.mem_Ioc.mp hn
    have hnpos : 1 ≤ n := by omega
    have hnN : n ≤ N := hnmem.2.trans hK
    have hLambda := primePrefixTerm_norm_le (c := c) (ξ := ξ) hnpos hnN
    have hμ := mobiusPrefixTerm_norm_le (c := c) (ξ := ξ) hnpos
    linarith
  calc
    _ ≤ (∑ n ∈ Finset.Ioc 0 K, ‖primePrefixTerm c ξ n‖) +
        (∑ n ∈ Finset.Ioc 0 K, ‖mobiusPrefixTerm c ξ n‖) :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ = ∑ n ∈ Finset.Ioc 0 K,
        (‖primePrefixTerm c ξ n‖ + ‖mobiusPrefixTerm c ξ n‖) := by
      rw [← Finset.sum_add_distrib]
    _ ≤ ∑ _n ∈ Finset.Ioc 0 K, (2 + Real.log (N : ℝ)) :=
      Finset.sum_le_sum (by intro n hn; exact hpoint n hn)
    _ = (K : ℝ) * (2 + Real.log (N : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul] <;> ring

private theorem log_nat_one_and_four_log_two {N : ℕ} (hN : 36 ≤ N) :
    1 ≤ Real.log (N : ℝ) ∧ 4 * Real.log 2 ≤ Real.log (N : ℝ) := by
  have hN16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 16 ≤ N)
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog16le : Real.log 16 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) hN16
  have hlog16one : 1 ≤ Real.log 16 := by
    apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 16)).2
    exact (Real.exp_one_lt_three.le.trans (by norm_num))
  constructor
  · exact hlog16one.trans hlog16le
  · simpa only [hlog16] using hlog16le

private theorem log_doubling_scale_lower {N K S : ℕ}
    (hN : 36 ≤ N) (hK : Real.sqrt (N : ℝ) / 2 < (K : ℝ))
    (hKS : K ≤ S) :
    Real.log (N : ℝ) / 4 ≤ Real.log (S : ℝ) := by
  have hlogN := log_nat_one_and_four_log_two hN
  have hNpos : 0 < (N : ℝ) := by positivity
  have hbasepos : 0 < Real.sqrt (N : ℝ) / 2 := by positivity
  have hKpos : 0 < (K : ℝ) := by linarith
  have hSreal : (K : ℝ) ≤ (S : ℝ) := by exact_mod_cast hKS
  have hSpos : 0 < (S : ℝ) := lt_of_lt_of_le hKpos hSreal
  have hbase : Real.log (Real.sqrt (N : ℝ) / 2) =
      Real.log (N : ℝ) / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_sqrt (by positivity)]
  calc
    Real.log (N : ℝ) / 4 ≤ Real.log (Real.sqrt (N : ℝ) / 2) := by
      rw [hbase]
      linarith [hlogN.2]
    _ ≤ Real.log (K : ℝ) :=
      Real.log_le_log hbasepos (le_of_lt hK)
    _ ≤ Real.log (S : ℝ) := Real.log_le_log hKpos hSreal

/-- Whole-prefix uniform Fourier bound, conditional only on the source
Dirichlet and restricted polynomial twisted tasks already used by the dyadic
estimate. The real frequency is interpreted by the source's half-open centered
representative. -/
theorem arithmeticCorrelationPrefixBoundOf_OAISource_DP_PTW {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → ∀ ξ : ℝ,
      ‖∑ n ∈ Finset.Ioc 0 N,
          ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
            unitFrequencyPhase (centeredFrequency ξ *
              (Int.floor ((n : ℝ) ^ c) : ℝ))‖ +
        ‖∑ n ∈ Finset.Ioc 0 N,
          (paperMu (n : ℤ) : ℂ) *
            unitFrequencyPhase (centeredFrequency ξ *
              (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
          C * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
  classical
  let B : ℝ := A + 1
  obtain ⟨Cdyad, hCdyad, hdyad⟩ :=
    dyadicArithmeticCorrelationOf_OAISource_DP_PTW hc hcNon hDP hPTW B
      (by dsimp [B]; linarith)
  obtain ⟨T, hT36, hlogGrowth⟩ := exists_log_rpow_le_half (B := B)
    (by dsimp [B]; linarith)
  let M : ℕ := Nat.ceil T
  have hTM : T ≤ (M : ℝ) := by
    dsimp [M]
    exact_mod_cast (Nat.le_ceil T)
  have hM36 : 36 ≤ M := by
    have h : (36 : ℝ) ≤ (M : ℝ) := hT36.trans hTM
    exact_mod_cast h
  have hlogM := log_nat_one_and_four_log_two hM36
  let Csmall : ℝ := (2 + Real.log (M : ℝ)) * (Real.log (M : ℝ)) ^ A
  let Clarge : ℝ := 3 + 2 * Cdyad * (4 : ℝ) ^ B
  let C : ℝ := Csmall + Clarge
  have hCsmall : 0 < Csmall := by
    dsimp [Csmall]
    have hlogMpos : 0 < Real.log (M : ℝ) := lt_of_lt_of_le (by norm_num) hlogM.1
    positivity
  have hClarge : 0 < Clarge := by
    dsimp [Clarge]
    positivity
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    linarith
  · intro N hN ξ
    have hNrealpos : 0 < (N : ℝ) := by positivity
    have hN3real : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlog3 : 1 ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hLone : 1 ≤ Real.log (N : ℝ) :=
      hlog3.trans (Real.log_le_log (by norm_num) hN3real)
    by_cases hlarge : M ≤ N
    · have hN36 : 36 ≤ N := le_trans hM36 hlarge
      have hNreal : T ≤ (N : ℝ) := by
        have hMN : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hlarge
        exact hTM.trans hMN
      obtain ⟨K, J, hKthree, hKlower, hKupper, hKN, hNend⟩ :=
        exists_natural_doubling_cutoff hN36
      have hKleN : K ≤ N := by
        have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
        have hsqrtle : Real.sqrt (N : ℝ) ≤ (N : ℝ) :=
          Real.sqrt_le_self_iff.mpr (Or.inr hNge1)
        exact_mod_cast hKupper.trans hsqrtle
      have hKpos : 0 < K := by omega
      let f : ℕ → ℂ := primePrefixTerm c ξ
      let g : ℕ → ℂ := mobiusPrefixTerm c ξ
      have hfreq := centeredFrequency_mem ξ
      have hlocal : ∀ v ∈ Finset.range (J + 1),
          ‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n‖ +
          ‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n‖ ≤
            Cdyad * ((K * 2 ^ v : ℕ) : ℝ) *
              (4 : ℝ) ^ B * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
        intro v hv
        have hvlt : v < J + 1 := Finset.mem_range.mp hv
        have hvle : v ≤ J := by omega
        have hpowone : 1 ≤ 2 ^ v := Nat.one_le_pow v 2 (by omega)
        have hKtoS : K ≤ K * 2 ^ v := by
          calc
            K = K * 1 := by simp
            _ ≤ K * 2 ^ v := Nat.mul_le_mul_left K hpowone
        have hRle : doublingRight K N J v ≤ 2 * (K * 2 ^ v) := by
          by_cases hvJ : v < J
          · simp [doublingRight, hvJ, pow_succ]
            exact le_of_eq (by ring)
          · have hvEq : v = J := by omega
            subst v
            simp [doublingRight]
            exact hNend
        have hK'S : K * 2 ^ v ≤ doublingRight K N J v := by
          by_cases hvJ : v < J
          · simp [doublingRight, hvJ]
            rw [pow_succ]
            calc
              K * 2 ^ v = (K * 2 ^ v) * 1 := by simp
              _ ≤ (K * 2 ^ v) * 2 := Nat.mul_le_mul_left _ (by omega)
              _ = K * (2 ^ v * 2) := by ring
          · have hvEq : v = J := by omega
            subst v
            simp [doublingRight]
            exact hKN
        have hSthree : 3 ≤ K * 2 ^ v := le_trans hKthree hKtoS
        have hQlower := log_doubling_scale_lower hN36 hKlower hKtoS
        have hlocalLog := logPowerScale_bound (A := A)
          (L := Real.log (N : ℝ))
          (Q := Real.log ((K * 2 ^ v : ℕ) : ℝ)) hA.le hLone hQlower
        have hdyadLocal := hdyad (K * 2 ^ v) (doublingRight K N J v)
          hSthree hK'S hRle (centeredFrequency ξ) hfreq.1 hfreq.2
        simpa [f, g, primePrefixTerm, mobiusPrefixTerm] using
          (calc
            _ ≤ Cdyad * ((K * 2 ^ v : ℕ) : ℝ) *
                  (Real.log ((K * 2 ^ v : ℕ) : ℝ)) ^ (-B : ℝ) := hdyadLocal
            _ ≤ Cdyad * ((K * 2 ^ v : ℕ) : ℝ) *
                  (4 : ℝ) ^ B * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
              calc
                _ ≤ Cdyad * ((K * 2 ^ v : ℕ) : ℝ) *
                    ((4 : ℝ) ^ B * (Real.log (N : ℝ)) ^ (-A : ℝ)) :=
                  mul_le_mul_of_nonneg_left hlocalLog
                    (mul_nonneg (le_of_lt hCdyad) (by positivity))
                _ = _ := by ring)
      have hblocksScale :
          (∑ v ∈ Finset.range (J + 1),
            (‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n‖ +
             ‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n‖)) ≤
            (Cdyad * (4 : ℝ) ^ B * (Real.log (N : ℝ)) ^ (-A : ℝ)) *
              ∑ v ∈ Finset.range (J + 1), ((K * 2 ^ v : ℕ) : ℝ) := by
        calc
          _ ≤ ∑ v ∈ Finset.range (J + 1),
              Cdyad * ((K * 2 ^ v : ℕ) : ℝ) * (4 : ℝ) ^ B *
                (Real.log (N : ℝ)) ^ (-A : ℝ) :=
            Finset.sum_le_sum (by intro v hv; exact hlocal v hv)
          _ = _ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v hv
            ring
      have hscaleNat := sum_doubling_scales_le_two_last K J
      have hscaleReal :
          (∑ v ∈ Finset.range (J + 1), ((K * 2 ^ v : ℕ) : ℝ)) ≤
            2 * ((K * 2 ^ J : ℕ) : ℝ) := by exact_mod_cast hscaleNat
      have hlastReal : ((K * 2 ^ J : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKN
      have hscaleN :
          (∑ v ∈ Finset.range (J + 1), ((K * 2 ^ v : ℕ) : ℝ)) ≤
            2 * (N : ℝ) := hscaleReal.trans (mul_le_mul_of_nonneg_left hlastReal (by norm_num))
      have hfactorNonneg :
          0 ≤ Cdyad * (4 : ℝ) ^ B * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
        positivity
      have hblocks :
          (∑ v ∈ Finset.range (J + 1),
            (‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n‖ +
             ‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n‖)) ≤
            (2 * Cdyad * (4 : ℝ) ^ B) * (N : ℝ) *
              (Real.log (N : ℝ)) ^ (-A : ℝ) := by
        calc
          _ ≤ (Cdyad * (4 : ℝ) ^ B * (Real.log (N : ℝ)) ^ (-A : ℝ)) *
                ∑ v ∈ Finset.range (J + 1), ((K * 2 ^ v : ℕ) : ℝ) := hblocksScale
          _ ≤ (Cdyad * (4 : ℝ) ^ B * (Real.log (N : ℝ)) ^ (-A : ℝ)) *
                (2 * (N : ℝ)) := mul_le_mul_of_nonneg_left hscaleN hfactorNonneg
          _ = _ := by ring
      have hinit := norm_arithmetic_prefix_trivial_bound (c := c)
        (ξ := ξ) hKleN
      have hinitNorm :
          ‖∑ n ∈ Finset.Ioc 0 K, f n‖ + ‖∑ n ∈ Finset.Ioc 0 K, g n‖ ≤
            (K : ℝ) * (2 + Real.log (N : ℝ)) := by
        simpa [f, g, primePrefixTerm, mobiusPrefixTerm] using hinit
      have hKsqrt : (K : ℝ) ≤ Real.sqrt (N : ℝ) := hKupper
      have hloglinear : 2 + Real.log (N : ℝ) ≤ 3 * Real.log (N : ℝ) := by
        linarith
      have hpow : (Real.log (N : ℝ)) ^ B ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
        hlogGrowth (N : ℝ) hNreal
      have hpowId : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A =
          (Real.log (N : ℝ)) ^ B := by
        dsimp [B]
        calc
          _ = (Real.log (N : ℝ)) ^ A * Real.log (N : ℝ) := by ring
          _ = (Real.log (N : ℝ)) ^ (A + 1) := by
            rw [← Real.rpow_add_one (ne_of_gt (by linarith :
              0 < Real.log (N : ℝ))) A]
      have hinitMul :
          (K : ℝ) * (2 + Real.log (N : ℝ)) * (Real.log (N : ℝ)) ^ A ≤
            3 * (N : ℝ) := by
        have hlinear := calc
          (K : ℝ) * (2 + Real.log (N : ℝ)) ≤
              Real.sqrt (N : ℝ) * (2 + Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_right hKsqrt (by positivity)
          _ ≤ Real.sqrt (N : ℝ) * (3 * Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hloglinear (Real.sqrt_nonneg _)
          _ = 3 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by ring
        calc
          _ ≤ (3 * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) *
                (Real.log (N : ℝ)) ^ A :=
            mul_le_mul_of_nonneg_right hlinear (Real.rpow_nonneg (by linarith) A)
          _ = 3 * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ B := by
            rw [← hpowId]
            ring
          _ ≤ 3 * Real.sqrt (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = 3 * (N : ℝ) := by
            rw [← Real.sqrt_eq_rpow (N : ℝ)]
            nlinarith [Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)]
      have hLpowpos : 0 < (Real.log (N : ℝ)) ^ A :=
        Real.rpow_pos_of_pos (by linarith) A
      have hinitSmall :
          (K : ℝ) * (2 + Real.log (N : ℝ)) ≤
            3 * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
        rw [Real.rpow_neg (le_of_lt (by linarith : 0 < Real.log (N : ℝ))) A]
        calc
          _ = ((K : ℝ) * (2 + Real.log (N : ℝ)) *
                (Real.log (N : ℝ)) ^ A) *
                ((Real.log (N : ℝ)) ^ A)⁻¹ := by field_simp [hLpowpos.ne']
          _ ≤ (3 * (N : ℝ)) * ((Real.log (N : ℝ)) ^ A)⁻¹ :=
            mul_le_mul_of_nonneg_right hinitMul (inv_nonneg.mpr hLpowpos.le)
          _ = _ := by ring
      have hinitSmallNorm :
          ‖∑ n ∈ Finset.Ioc 0 K, f n‖ + ‖∑ n ∈ Finset.Ioc 0 K, g n‖ ≤
            3 * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) :=
        hinitNorm.trans hinitSmall
      have hprefix := norm_prefix_le_initial_add_blocks K N J hKleN hKN f g
      have hCbigle : Clarge ≤ C := by dsimp [C]; linarith
      have hlargeBound :
          ‖∑ n ∈ Finset.Ioc 0 N,
              ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
                unitFrequencyPhase (centeredFrequency ξ *
                  (Int.floor ((n : ℝ) ^ c) : ℝ))‖ +
            ‖∑ n ∈ Finset.Ioc 0 N,
              (paperMu (n : ℤ) : ℂ) *
                unitFrequencyPhase (centeredFrequency ξ *
                  (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
              Clarge * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
        simpa [f, g, primePrefixTerm, mobiusPrefixTerm] using
          (calc
            _ ≤ (‖∑ n ∈ Finset.Ioc 0 K, f n‖ +
                  ‖∑ n ∈ Finset.Ioc 0 K, g n‖) +
                ∑ v ∈ Finset.range (J + 1),
                  (‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), f n‖ +
                   ‖∑ n ∈ Finset.Ioc (K * 2 ^ v) (doublingRight K N J v), g n‖) := hprefix
            _ ≤ 3 * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) +
                  (2 * Cdyad * (4 : ℝ) ^ B) * (N : ℝ) *
                    (Real.log (N : ℝ)) ^ (-A : ℝ) := add_le_add hinitSmallNorm hblocks
            _ = Clarge * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
              dsimp [Clarge]
              ring)
      have hlargeFinal := calc
        _ ≤ Clarge * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) := hlargeBound
        _ ≤ C * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCbigle (by positivity)) (by positivity)
      exact hlargeFinal
    · have hNltM : N < M := Nat.lt_of_not_ge hlarge
      have hNleMreal : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNltM.le
      have hlogMge : 0 < Real.log (M : ℝ) := by linarith [hlogM.1]
      have hlogNle : Real.log (N : ℝ) ≤ Real.log (M : ℝ) :=
        Real.log_le_log (by positivity) hNleMreal
      have hpowle : (Real.log (N : ℝ)) ^ A ≤ (Real.log (M : ℝ)) ^ A :=
        Real.rpow_le_rpow (by positivity) hlogNle hA.le
      have hfactor :
          (2 + Real.log (N : ℝ)) * (Real.log (N : ℝ)) ^ A ≤ Csmall := by
        calc
          _ ≤ (2 + Real.log (M : ℝ)) * (Real.log (N : ℝ)) ^ A :=
            mul_le_mul_of_nonneg_right
              (by simpa [add_comm] using add_le_add_left hlogNle 2)
              (Real.rpow_nonneg (by linarith) A)
          _ ≤ (2 + Real.log (M : ℝ)) * (Real.log (M : ℝ)) ^ A :=
            mul_le_mul_of_nonneg_left hpowle (by positivity)
          _ = Csmall := by rfl
      have htrivial := norm_arithmetic_prefix_trivial_bound (c := c)
        (ξ := ξ) (N := N) (K := N) (le_rfl)
      have hfactorN :
          (N : ℝ) * (2 + Real.log (N : ℝ)) *
              (Real.log (N : ℝ)) ^ A ≤ Csmall * (N : ℝ) := by
        calc
          _ = (N : ℝ) * ((2 + Real.log (N : ℝ)) *
                (Real.log (N : ℝ)) ^ A) := by ring
          _ ≤ (N : ℝ) * Csmall := mul_le_mul_of_nonneg_left hfactor (by positivity)
          _ = Csmall * (N : ℝ) := by ring
      have hLpowpos : 0 < (Real.log (N : ℝ)) ^ A :=
        Real.rpow_pos_of_pos (by linarith) A
      have hsmallBound :
          (N : ℝ) * (2 + Real.log (N : ℝ)) ≤
            Csmall * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
        rw [Real.rpow_neg (le_of_lt (by linarith : 0 < Real.log (N : ℝ))) A]
        calc
          _ = ((N : ℝ) * (2 + Real.log (N : ℝ)) *
                (Real.log (N : ℝ)) ^ A) *
                ((Real.log (N : ℝ)) ^ A)⁻¹ := by field_simp [hLpowpos.ne']
          _ ≤ (Csmall * (N : ℝ)) * ((Real.log (N : ℝ)) ^ A)⁻¹ :=
            mul_le_mul_of_nonneg_right hfactorN (inv_nonneg.mpr hLpowpos.le)
          _ = _ := by ring
      have hsmallResult := calc
        _ ≤ (N : ℝ) * (2 + Real.log (N : ℝ)) := htrivial
        _ ≤ Csmall * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) := hsmallBound
        _ ≤ C * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
          have hCsmallle : Csmall ≤ C := by dsimp [C]; linarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCsmallle (by positivity)) (by positivity)
      simpa [primePrefixTerm, mobiusPrefixTerm] using hsmallResult

/-- The prime-comparison half of the whole-prefix estimate, in normalized
Fourier-multiplier form. The two analytic task inputs remain explicit. -/
theorem primeMultiplierComparisonOf_OAISource_DP_PTW {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → ∀ ξ : ℝ,
      ‖∑ n ∈ Finset.Ioc 0 N,
          ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
            unitFrequencyPhase (centeredFrequency ξ *
              (Int.floor ((n : ℝ) ^ c) : ℝ))‖ / (N : ℝ) ≤
        C * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
  obtain ⟨C, hC, hprefix⟩ :=
    arithmeticCorrelationPrefixBoundOf_OAISource_DP_PTW hc hcNon hDP hPTW A hA
  refine ⟨C, hC, ?_⟩
  intro N hN ξ
  have hNpos : 0 < (N : ℝ) := by positivity
  have hcombined := hprefix N hN ξ
  have hprime :
      ‖∑ n ∈ Finset.Ioc 0 N,
          ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
            unitFrequencyPhase (centeredFrequency ξ *
              (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
        C * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) :=
    le_trans (le_add_of_nonneg_right (norm_nonneg _)) hcombined
  calc
    _ ≤ (C * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ)) / (N : ℝ) :=
      div_le_div_of_nonneg_right hprime hNpos.le
    _ = C * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
      field_simp [hNpos.ne']

/-- The Möbius-comparison half of the whole-prefix estimate, in normalized
Fourier-multiplier form. The two analytic task inputs remain explicit. -/
theorem mobiusMultiplierDecayOf_OAISource_DP_PTW {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → ∀ ξ : ℝ,
      ‖∑ n ∈ Finset.Ioc 0 N,
          (paperMu (n : ℤ) : ℂ) *
            unitFrequencyPhase (centeredFrequency ξ *
              (Int.floor ((n : ℝ) ^ c) : ℝ))‖ / (N : ℝ) ≤
        C * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
  obtain ⟨C, hC, hprefix⟩ :=
    arithmeticCorrelationPrefixBoundOf_OAISource_DP_PTW hc hcNon hDP hPTW A hA
  refine ⟨C, hC, ?_⟩
  intro N hN ξ
  have hNpos : 0 < (N : ℝ) := by positivity
  have hcombined := hprefix N hN ξ
  have hmobius :
      ‖∑ n ∈ Finset.Ioc 0 N,
          (paperMu (n : ℤ) : ℂ) *
            unitFrequencyPhase (centeredFrequency ξ *
              (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
        C * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ) :=
    le_trans (le_add_of_nonneg_left (norm_nonneg _)) hcombined
  calc
    _ ≤ (C * (N : ℝ) * (Real.log (N : ℝ)) ^ (-A : ℝ)) / (N : ℝ) :=
      div_le_div_of_nonneg_right hmobius hNpos.le
    _ = C * (Real.log (N : ℝ)) ^ (-A : ℝ) := by
      field_simp [hNpos.ne']

end FractionalPrimes

#print axioms FractionalPrimes.arithmeticCorrelationPrefixBoundOf_OAISource_DP_PTW
#print axioms FractionalPrimes.primeMultiplierComparisonOf_OAISource_DP_PTW
#print axioms FractionalPrimes.mobiusMultiplierDecayOf_OAISource_DP_PTW
