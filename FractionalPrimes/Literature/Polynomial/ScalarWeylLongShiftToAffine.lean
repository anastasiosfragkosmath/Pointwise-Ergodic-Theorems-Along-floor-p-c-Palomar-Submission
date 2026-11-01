module

public import FractionalPrimes.Literature.Polynomial.AffineRecurrence
public import FractionalPrimes.Literature.Polynomial.ScalarWeylCommonShiftDenominator
public import FractionalPrimes.Literature.Polynomial.ScalarWeyl

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

set_option maxHeartbeats 600000 in
/-- The long-shift correlations, degree-`d-1` induction callback, and finite
denominator pigeonhole produce the input set for the affine recurrence. This
is the source step from `ηN` good shifts to one common `q₀` on at least
`2σN` shifts, followed by the exact `ε = B/N^(d-1)` affine-recursion call. -/
theorem scalarWeyl_longShiftToAffine
    {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    {δ η B σ R : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hη : η = δ ^ 2 / 8) (hB : 1 ≤ B)
    (hσ : σ = η / (2 * B))
    (hR : R = 32 * (d : ℝ) * B * (σ⁻¹) ^ 2)
    (hNlong : 4 * R ≤ (N : ℝ))
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (J : Finset ℤ)
    (hJinterval : ∃ lo hi : ℤ, J = Finset.Ico lo hi)
    (hJsubset : J ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    (hlarge : δ * (N : ℝ) ≤
      ‖∑ n ∈ J, unitFrequencyPhase (P.eval (n : ℝ))‖)
    (hIH : ∀ {M : ℕ}, 1 ≤ M →
      ∀ (Q : Polynomial ℝ), Q.natDegree ≤ d - 1 →
        ∀ K : Finset ℤ,
          (∃ a b : ℤ, K = Finset.Ico a b) →
          K ⊆ Finset.Icc (1 : ℤ) (M : ℤ) →
          0 < η → η < 1 / 2 →
          η * (M : ℝ) ≤
            ‖∑ n ∈ K, unitFrequencyPhase (Q.eval (n : ℝ))‖ →
          ∃ q : ℕ,
            1 ≤ q ∧ (q : ℝ) ≤ B ∧
            (∀ j, 1 ≤ j → j ≤ d - 1 →
              (M : ℝ) ^ j * realDistanceToIntegers
                ((q : ℝ) * Q.coeff j) ≤ B)) :
    ∃ q₀ q₁ : ℕ,
      1 ≤ q₀ ∧ (q₀ : ℝ) ≤ B ∧
      1 ≤ q₁ ∧ (q₁ : ℝ) ≤ 2 / σ ∧
      realDistanceToIntegers
        ((q₁ : ℝ) * ((q₀ : ℝ) * (d : ℝ) * P.coeff d)) ≤
          16 * B * (σ⁻¹) ^ 2 / (N : ℝ) ^ d := by
  classical
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηhalf : η < 1 / 2 := by
    rw [hη]
    nlinarith [hδhalf]
  have hσformula : σ = δ ^ 2 / (16 * B) := by
    calc
      σ = η / (2 * B) := hσ
      _ = (δ ^ 2 / 8) / (2 * B) := by rw [hη]
      _ = δ ^ 2 / (16 * B) := by ring
  have hσpos : 0 < σ := by rw [hσ]; positivity
  have hσhalf : σ < 1 / 2 := by
    rw [hσformula]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * B)).2
    have hδsq : δ ^ 2 < 1 / 4 := by nlinarith [hδhalf]
    nlinarith [hδsq, hB]

  have hδsq : δ ^ 2 < 1 / 4 := by nlinarith [hδhalf]
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hBcube : 1 ≤ B ^ 3 := by
    calc
      1 = (1 : ℝ) ^ 3 := by norm_num
      _ ≤ B ^ 3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hB 3
  have hdFactor : 1 ≤ 8192 * (d : ℝ) := by nlinarith [hdR]
  have hRfactor : 1 ≤ 8192 * (d : ℝ) * B ^ 3 := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (8192 * (d : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_right hdFactor (by norm_num)
      _ ≤ (8192 * (d : ℝ)) * B ^ 3 :=
        mul_le_mul_of_nonneg_left hBcube (by positivity)
  have hdeltaInvBound : δ⁻¹ ^ 2 ≤ R := by
    have hinvSq : δ⁻¹ ^ 2 = 1 / δ ^ 2 := by
      field_simp [ne_of_gt hδ]
    rw [hinvSq]
    apply (div_le_iff₀ (pow_pos hδ 2)).2
    rw [hR, hσformula]
    field_simp [ne_of_gt hδ, ne_of_gt hBpos]
    nlinarith [hδsq, hRfactor]
  have hNshift : 4 / δ ^ 2 ≤ (N : ℝ) := by
    calc
      4 / δ ^ 2 = 4 * δ⁻¹ ^ 2 := by field_simp [ne_of_gt hδ]
      _ ≤ 4 * R := mul_le_mul_of_nonneg_left hdeltaInvBound (by norm_num)
      _ ≤ (N : ℝ) := hNlong
  have hdge1 : (1 : ℝ) ≤ (d : ℝ) := le_trans (by norm_num) hdR
  have hdb : (1 : ℝ) ≤ (d : ℝ) * B := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_right hdge1 (by norm_num)
      _ ≤ (d : ℝ) * B := mul_le_mul_of_nonneg_left hB (by linarith)
  have hσInvSqNonneg : 0 ≤ (σ⁻¹) ^ 2 := sq_nonneg _
  have hNaffine : 16 * (σ⁻¹) ^ 2 ≤ (N : ℝ) := by
    calc
      16 * (σ⁻¹) ^ 2 ≤ 128 * (d : ℝ) * B * (σ⁻¹) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [hdb]) hσInvSqNonneg
      _ = 4 * R := by rw [hR]; ring
      _ ≤ (N : ℝ) := hNlong
  have hNsource :
      128 * (d : ℝ) * B * (σ⁻¹) ^ 2 ≤ (N : ℝ) := by
    calc
      128 * (d : ℝ) * B * (σ⁻¹) ^ 2 = 4 * R := by rw [hR]; ring
      _ ≤ (N : ℝ) := hNlong

  have hNposNat : 0 < N := by omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  let ε : ℝ := B / (N : ℝ) ^ (d - 1)
  have hNpowpos : 0 < (N : ℝ) ^ (d - 1) := pow_pos hNpos _
  have hNpow : (N : ℝ) ≤ (N : ℝ) ^ (d - 1) := by
    have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hexp : 1 ≤ d - 1 := by omega
    simpa using (pow_le_pow_right₀ hbase hexp)
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact div_pos hBpos hNpowpos
  have hεleBN : ε ≤ B / (N : ℝ) := by
    dsimp [ε]
    apply (div_le_div_iff₀ hNpowpos hNpos).2
    exact mul_le_mul_of_nonneg_left hNpow hBpos.le
  have hσsquareN :
      (σ ^ 2) * (128 * (d : ℝ) * B * (σ⁻¹) ^ 2) ≤
        (σ ^ 2) * (N : ℝ) :=
    mul_le_mul_of_nonneg_left hNsource (sq_nonneg σ)
  have hσcancel :
      (σ ^ 2) * (128 * (d : ℝ) * B * (σ⁻¹) ^ 2) =
        128 * (d : ℝ) * B := by
    field_simp [ne_of_gt hσpos]
  have hBN : B / (N : ℝ) ≤ σ ^ 2 / (128 * (d : ℝ)) := by
    apply (div_le_div_iff₀ hNpos (by positivity :
      (0 : ℝ) < 128 * (d : ℝ))).2
    rw [hσcancel] at hσsquareN
    nlinarith [hσsquareN]
  have hσsqle : σ ^ 2 ≤ σ := by nlinarith [hσpos, hσhalf]
  have hσsqdiv : σ ^ 2 / (128 * (d : ℝ)) ≤
      σ / (128 * (d : ℝ)) :=
    div_le_div_of_nonneg_right hσsqle (by positivity)
  have hdenom : 16 ≤ 128 * (d : ℝ) := by nlinarith [hdR]
  have hσdiv : σ / (128 * (d : ℝ)) ≤ σ / 16 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 128 * (d : ℝ))
      (by norm_num : (0 : ℝ) < 16)).2
    exact mul_le_mul_of_nonneg_left hdenom hσpos.le
  have hεupper : ε ≤ σ / 16 := hεleBN.trans (hBN.trans (hσsqdiv.trans hσdiv))

  let z : ℤ → ℂ := fun n => unitFrequencyPhase (P.eval (n : ℝ))
  have hz : ∀ n ∈ J, ‖z n‖ = 1 := by
    intro n hn
    dsimp [z]
    exact norm_unitFrequencyPhase _
  let H : Finset ℕ := (Finset.Ico 1 N).filter (fun h : ℕ =>
    η * (N : ℝ) ≤
      ‖∑ n ∈ J.filter (fun n => n + (h : ℤ) ∈ J),
        z (n + (h : ℤ)) * star (z n)‖)
  have hcorrelationCount : η * (N : ℝ) ≤ (H.card : ℝ) := by
    have hmany := manyLongShiftCorrelations hN hδ hδhalf hNshift
      J hJinterval hJsubset z hz hlarge
    have hthreshold : η * (N : ℝ) = δ ^ 2 * (N : ℝ) / 8 := by
      rw [hη]
      ring
    simpa [H, z, hthreshold, Int.cast_add, Int.cast_natCast] using hmany

  let topGood : ℕ → ℕ → Prop := fun q h =>
    realDistanceToIntegers
      ((q : ℝ) * (d : ℝ) * P.coeff d * (h : ℝ)) ≤ ε
  have hden : ∀ h ∈ H, ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ B ∧ topGood q h := by
    intro h hh
    rcases Finset.mem_filter.mp hh with ⟨hhIco, hhlarge⟩
    have hhlarge' : η * (N : ℝ) ≤
        ‖∑ n ∈ J.filter (fun n => n + (h : ℤ) ∈ J),
          unitFrequencyPhase (P.eval ((n : ℝ) + (h : ℝ))) *
            star (unitFrequencyPhase (P.eval (n : ℝ)))‖ := by
      simpa [H, z] using hhlarge
    obtain ⟨q, hq, hqB, hqdist⟩ :=
      scalarWeyl_largeShiftCorrelation_induction hd hN P hP
        hJinterval hJsubset hηpos hηhalf hIH h hhIco hhlarge'
    refine ⟨q, hq, hqB, ?_⟩
    simpa [topGood, ε] using hqdist

  obtain ⟨q₀, H₀, hq₀, hq₀B, hH₀count, hH₀subset, hH₀good⟩ :=
    scalarWeyl_commonShiftDenominator H hηpos hB hσ hcorrelationCount
      topGood hden

  let α : ℝ := (q₀ : ℝ) * (d : ℝ) * P.coeff d
  have hgoodSet :
      σ * (N : ℝ) ≤
        (((Finset.Icc 1 N).filter (fun n : ℕ =>
          realDistanceToIntegers (α * (n : ℝ) + 0) ≤ ε)).card : ℝ) := by
    let S : Finset ℕ := (Finset.Icc 1 N).filter (fun n : ℕ =>
      realDistanceToIntegers (α * (n : ℝ) + 0) ≤ ε)
    have hH₀subsetS : H₀ ⊆ S := by
      intro n hn
      have hnH : n ∈ H := hH₀subset hn
      rcases Finset.mem_filter.mp hnH with ⟨hnIco, _⟩
      have hnIcc : n ∈ Finset.Icc 1 N := by
        rw [Finset.mem_Ico] at hnIco
        rw [Finset.mem_Icc]
        exact ⟨hnIco.1, by omega⟩
      have hdist := hH₀good n hn
      have hdist' : realDistanceToIntegers (α * (n : ℝ) + 0) ≤ ε := by
        simpa [α, topGood] using hdist
      exact Finset.mem_filter.mpr ⟨hnIcc, hdist'⟩
    have hH₀toS : (H₀.card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hH₀subsetS
    have hσNnonneg : 0 ≤ σ * (N : ℝ) :=
      mul_nonneg hσpos.le (Nat.cast_nonneg N)
    have hσN : σ * (N : ℝ) ≤ (H₀.card : ℝ) := by
      linarith [hH₀count]
    calc
      σ * (N : ℝ) ≤ (H₀.card : ℝ) := hσN
      _ ≤ (S.card : ℝ) := hH₀toS
      _ = (((Finset.Icc 1 N).filter (fun n : ℕ =>
          realDistanceToIntegers (α * (n : ℝ) + 0) ≤ ε)).card : ℝ) := by
        simp [S]

  obtain ⟨q₁, hq₁, hq₁upper, hq₁dist⟩ :=
    affineRecurrence hN hσpos hσhalf hεpos.le hεupper hNaffine hgoodSet
  refine ⟨q₀, q₁, hq₀, hq₀B, hq₁, hq₁upper, ?_⟩
  have hNpowSucc : (N : ℝ) ^ d =
      (N : ℝ) ^ (d - 1) * (N : ℝ) := by
    have hdexp : d = (d - 1) + 1 := by omega
    calc
      (N : ℝ) ^ d = (N : ℝ) ^ ((d - 1) + 1) := by
        exact congrArg (fun k : ℕ => (N : ℝ) ^ k) hdexp
      _ = (N : ℝ) ^ (d - 1) * (N : ℝ) := by rw [pow_succ]
  have hscale : 16 * ε / (σ ^ 2 * (N : ℝ)) =
      16 * B * (σ⁻¹) ^ 2 / (N : ℝ) ^ d := by
    rw [hNpowSucc]
    dsimp [ε]
    field_simp [ne_of_gt hσpos, ne_of_gt hNpos, ne_of_gt hNpowpos]
  calc
    realDistanceToIntegers ((q₁ : ℝ) * α) ≤
        16 * ε / (σ ^ 2 * (N : ℝ)) := hq₁dist
    _ = 16 * B * (σ⁻¹) ^ 2 / (N : ℝ) ^ d := hscale

end FractionalPrimes.Literature.Polynomial
