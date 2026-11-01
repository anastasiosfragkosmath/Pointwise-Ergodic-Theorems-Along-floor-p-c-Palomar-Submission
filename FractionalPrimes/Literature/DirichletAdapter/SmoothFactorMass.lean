module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownConvolution
public import Mathlib.Tactic

/-!
# Finite mass of a smooth Heath--Brown factor

The long-factor proof bounds every other factor by its inverse-square-root
absolute mass.  This file isolates the finite counting and weight estimate
behind the source bound `5 * sqrt N`, independently of residue quadrature.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

noncomputable section

/-- The positive integer arguments in the source support window `(N/2, 2N]`.
The smooth cutoff vanishes at the omitted lower endpoint. -/
def smoothFactorMassWindow (N : ℝ) : Finset ℕ :=
  Finset.Ioc (Nat.floor (N / 2)) (Nat.floor (2 * N))

/-- The floor endpoints retain the open-left, closed-right convention of the
source support window. -/
theorem mem_smoothFactorMassWindow {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    n ∈ smoothFactorMassWindow N ↔ N / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
  constructor
  · intro hn
    rcases Finset.mem_Ioc.mp hn with ⟨hnlo, hnhi⟩
    exact ⟨Nat.lt_of_floor_lt hnlo,
      le_trans (Nat.cast_le.mpr hnhi) (Nat.floor_le (by positivity))⟩
  · rintro ⟨hnlo, hnhi⟩
    apply Finset.mem_Ioc.mpr
    exact ⟨(Nat.floor_lt (show 0 ≤ N / 2 by positivity)).2 hnlo, Nat.le_floor hnhi⟩

/-- There are at most `3N` positive integer arguments in the smooth support
window. -/
theorem smoothFactorMassWindow_card_le {N : ℝ} (hN : 1 ≤ N) :
    ((smoothFactorMassWindow N).card : ℝ) ≤ 3 * N := by
  let S := smoothFactorMassWindow N
  have hfloorMono : Nat.floor (N / 2) ≤ Nat.floor (2 * N) :=
    Nat.floor_mono (by nlinarith)
  have hcard : (S.card : ℝ) = (Nat.floor (2 * N) : ℝ) -
      (Nat.floor (N / 2) : ℝ) := by
    dsimp [S, smoothFactorMassWindow]
    rw [Nat.card_Ioc]
    exact_mod_cast Nat.cast_sub hfloorMono
  have hfloorUpper : (Nat.floor (2 * N) : ℝ) ≤ 2 * N :=
    Nat.floor_le (by positivity)
  have hfloorLower : N / 2 - 1 ≤ (Nat.floor (N / 2) : ℝ) :=
    (Nat.sub_one_lt_floor (N / 2)).le
  rw [hcard]
  nlinarith

private theorem invSqrt_le_scaled {N n : ℝ} (hN : 0 < N)
    (hn : N / 2 ≤ n) : 1 / Real.sqrt n ≤ Real.sqrt (2 / N) := by
  have hnpos : 0 < n := by linarith
  have hfrac : 1 / n ≤ 2 / N := by
    apply (div_le_div_iff₀ hnpos hN).2
    nlinarith
  have hsqLeft : (1 / Real.sqrt n) ^ 2 = 1 / n := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hnpos)]
  have hsqRight : (Real.sqrt (2 / N)) ^ 2 = 2 / N :=
    Real.sq_sqrt (by positivity)
  have hleft : 0 ≤ 1 / Real.sqrt n := by positivity
  have hright : 0 ≤ Real.sqrt (2 / N) := by positivity
  nlinarith

/-- If a factor has coefficient modulus at most one on its source support,
its inverse-square-root absolute mass is at most `5 * sqrt N`.  The hypotheses
are the exact finite count and lower-support facts used for each normalized
factor in `lda:type-i`. -/
theorem smoothFactorInverseSqrtMass {N : ℝ} (hN : 1 ≤ N) (f : ℕ → ℂ)
    (hf : ∀ n ∈ smoothFactorMassWindow N, ‖f n‖ ≤ 1) :
    (∑ n ∈ smoothFactorMassWindow N,
      ‖f n‖ / Real.sqrt (n : ℝ)) ≤ 5 * Real.sqrt N := by
  have hNpos : 0 < N := by linarith
  have hNnonneg : 0 ≤ N := by linarith
  have hterm (n : ℕ) (hn : n ∈ smoothFactorMassWindow N) :
      ‖f n‖ / Real.sqrt (n : ℝ) ≤ Real.sqrt (2 / N) := by
    have hwindow := (mem_smoothFactorMassWindow hNnonneg n).mp hn
    calc
      ‖f n‖ / Real.sqrt (n : ℝ) ≤ 1 / Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_right (hf n hn) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (2 / N) := invSqrt_le_scaled hNpos (le_of_lt hwindow.1)
  calc
    (∑ n ∈ smoothFactorMassWindow N,
      ‖f n‖ / Real.sqrt (n : ℝ)) ≤
        ∑ _n ∈ smoothFactorMassWindow N, Real.sqrt (2 / N) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hterm n hn
    _ = ((smoothFactorMassWindow N).card : ℝ) * Real.sqrt (2 / N) := by simp
    _ ≤ (3 * N) * Real.sqrt (2 / N) := by
          exact mul_le_mul_of_nonneg_right (smoothFactorMassWindow_card_le hN)
            (Real.sqrt_nonneg _)
    _ ≤ 5 * Real.sqrt N := by
          have hA : 0 ≤ (3 * N) * Real.sqrt (2 / N) := by positivity
          have hB : 0 ≤ 5 * Real.sqrt N := by positivity
          have hsqA : ((3 * N) * Real.sqrt (2 / N)) ^ 2 = 18 * N := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
            field_simp [ne_of_gt hNpos]
            ring
          have hsqB : (5 * Real.sqrt N) ^ 2 = 25 * N := by
            rw [mul_pow, Real.sq_sqrt (by linarith)]
            ring
          nlinarith

/-- Multiplying the absolute masses of all factors except one costs at most
`5^19 * sqrt(P / N_selected)` when the component has at most twenty factors.
This is the finite product step used after applying the one-factor mass bound. -/
theorem smoothOtherFactorMassProduct {k : ℕ} (hk : k ≤ 20) (selected : Fin k)
    (N mass : Fin k → ℝ) (hN : ∀ i, 0 < N i) (hmass : ∀ i, 0 ≤ mass i)
    (hmassBound : ∀ i, i ≠ selected → mass i ≤ 5 * Real.sqrt (N i)) :
    (∏ i ∈ Finset.univ.erase selected, mass i) ≤
      5 ^ 19 * Real.sqrt ((∏ i : Fin k, N i) / N selected) := by
  let S : Finset (Fin k) := Finset.univ.erase selected
  have hcard : S.card ≤ 19 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (by simp : selected ∈ (Finset.univ : Finset (Fin k)))]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hprod :
      (∏ i ∈ S, mass i) ≤ ∏ i ∈ S, 5 * Real.sqrt (N i) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact hmass i
    · intro i hi
      exact hmassBound i (Finset.ne_of_mem_erase hi)
  have hprodSimplified :
      (∏ i ∈ S, 5 * Real.sqrt (N i)) =
        5 ^ S.card * Real.sqrt (∏ i ∈ S, N i) := by
    calc
      (∏ i ∈ S, 5 * Real.sqrt (N i)) =
          (∏ _i ∈ S, (5 : ℝ)) * (∏ i ∈ S, Real.sqrt (N i)) := by
            rw [Finset.prod_mul_distrib]
      _ = 5 ^ S.card * Real.sqrt (∏ i ∈ S, N i) := by
            rw [Finset.prod_const, Real.sqrt_prod S (by
              intro i hi
              exact le_of_lt (hN i))]
  have hscaleErase : (∏ i ∈ S, N i) =
      (∏ i : Fin k, N i) / N selected := by
    apply (eq_div_iff_mul_eq (ne_of_gt (hN selected))).2
    simpa [S] using
      (Finset.prod_erase_mul (Finset.univ : Finset (Fin k)) N
        (by simp : selected ∈ (Finset.univ : Finset (Fin k))))
  calc
    (∏ i ∈ Finset.univ.erase selected, mass i) = ∏ i ∈ S, mass i := by rfl
    _ ≤ 5 ^ S.card * Real.sqrt (∏ i ∈ S, N i) := by
          rw [← hprodSimplified]
          exact hprod
    _ = 5 ^ S.card *
          Real.sqrt ((∏ i : Fin k, N i) / N selected) := by rw [hscaleErase]
    _ ≤ 5 ^ 19 *
          Real.sqrt ((∏ i : Fin k, N i) / N selected) := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) hcard) (Real.sqrt_nonneg _)

end

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothFactorInverseSqrtMass
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothOtherFactorMassProduct
