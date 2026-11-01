module

public import FractionalPrimes.ArithmeticBasics

@[expose] public section

namespace FractionalPrimes

open scoped BigOperators

/-- A min-truncation loses at most a factor four when its positive argument
is replaced by one that is at least one quarter as large. -/
theorem min_one_le_four_min_one_of_le_four_mul
    {x y : ℝ} (hxy : x ≤ 4 * y) :
    min 1 x ≤ 4 * min 1 y := by
  by_cases hy1 : y ≤ 1
  · rw [min_eq_right hy1]
    exact (min_le_right 1 x).trans hxy
  · have hyge : 1 ≤ y := le_of_not_ge hy1
    calc
      min 1 x ≤ 1 := min_le_left 1 x
      _ ≤ 4 := by norm_num
      _ = 4 * min 1 y := by rw [min_eq_left hyge]; ring

/-- The source boundary kernel is stable under a fourfold change in its
integer cutoff. The smaller cutoff is the one on the left. -/
theorem floorBoundaryKernel_le_four_mul_of_cutoff_le
    {M₁ M₂ : ℕ} (hM₁ : 2 ≤ M₁) (hM₂ : 2 ≤ M₂)
    (hscale : (M₂ : ℝ) ≤ 4 * (M₁ : ℝ)) (t : ℝ) :
    floorBoundaryKernel M₁ hM₁ t ≤ 4 * floorBoundaryKernel M₂ hM₂ t := by
  classical
  by_cases ht : ∃ z : ℤ, t = (z : ℝ)
  · simp [floorBoundaryKernel, ht]
  · simp only [floorBoundaryKernel, ht, if_false]
    let d : ℝ := realDistanceToIntegers t
    let x : ℝ := (M₁ : ℝ) * d
    let y : ℝ := (M₂ : ℝ) * d
    have hd : 0 ≤ d := by
      dsimp [d, realDistanceToIntegers]
      exact Metric.infDist_nonneg
    have hx : 0 ≤ x := by
      dsimp [x]
      exact mul_nonneg (by positivity) hd
    have hy : 0 ≤ y := by
      dsimp [y]
      exact mul_nonneg (by positivity) hd
    have hxy : x⁻¹ ≤ 4 * y⁻¹ := by
      by_cases hd0 : d = 0
      · simp [x, y, d, hd0]
      · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
        have hxpos : 0 < x := by
          dsimp [x]
          exact mul_pos (by positivity) hdpos
        have hypos : 0 < y := by
          dsimp [y]
          exact mul_pos (by positivity) hdpos
        have hscaled : y ≤ 4 * x := by
          dsimp [x, y]
          calc
            (M₂ : ℝ) * d ≤ (4 * (M₁ : ℝ)) * d :=
              mul_le_mul_of_nonneg_right hscale hd
            _ = 4 * ((M₁ : ℝ) * d) := by ring
        have hdiv : (1 : ℝ) / x ≤ 4 / y := by
          apply (div_le_div_iff₀ hxpos hypos).2
          nlinarith
        simpa [one_div, div_eq_mul_inv] using hdiv
    simpa [x, y, d] using
      (min_one_le_four_min_one_of_le_four_mul
        hxy)

/-- Apply the checked progression estimate with an externally fixed cutoff
`M`. Its endpoint cutoff is `floor(N^η)`; the only transfer hypothesis is
that this endpoint cutoff is at most four times the fixed cutoff. -/
theorem boundaryErrorProgression_of_fourfold_fixed_cutoff {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      let M₀ : ℕ := Nat.floor (N ^ η)
      ∃ hM₀ : 2 ≤ M₀, ∀ M : ℕ,
        (M₀ : ℝ) ≤ 4 * (M : ℝ) →
        (hM : 2 ≤ M) →
        ∀ d : ℕ, 1 ≤ d →
          (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
          ((d : ℝ) / N) *
            (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
              floorBoundaryKernel M hM (((d : ℝ) * (n : ℝ)) ^ c)) ≤
            12 * N ^ (-η / 2) := by
  dsimp only
  obtain ⟨N₀, hN₀, hboundary⟩ := boundaryErrorProgression hc hcNon
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let M₀ : ℕ := Nat.floor (N ^ η)
  have hbase := hboundary N hN
  dsimp only at hbase
  rcases hbase with ⟨hM₀, hbase⟩
  refine ⟨hM₀, ?_⟩
  intro M hscale hM d hd hdcut
  have hsum :
      (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
        floorBoundaryKernel M hM (((d : ℝ) * (n : ℝ)) ^ c)) ≤
        4 * (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
          floorBoundaryKernel M₀ hM₀ (((d : ℝ) * (n : ℝ)) ^ c)) := by
    calc
      _ ≤ ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            4 * floorBoundaryKernel M₀ hM₀ (((d : ℝ) * (n : ℝ)) ^ c) :=
          Finset.sum_le_sum fun n hn =>
            floorBoundaryKernel_le_four_mul_of_cutoff_le hM hM₀
              hscale (((d : ℝ) * (n : ℝ)) ^ c)
      _ = 4 * ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            floorBoundaryKernel M₀ hM₀ (((d : ℝ) * (n : ℝ)) ^ c) := by
          rw [Finset.mul_sum]
  have hbase' := hbase d hd hdcut
  have hNpos : 0 < N := by linarith [hN₀, hN]
  have hscaleNonneg : 0 ≤ (d : ℝ) / N := by positivity
  calc
    ((d : ℝ) / N) *
        (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
          floorBoundaryKernel M hM (((d : ℝ) * (n : ℝ)) ^ c))
      ≤ ((d : ℝ) / N) *
          (4 * ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            floorBoundaryKernel M₀ hM₀ (((d : ℝ) * (n : ℝ)) ^ c)) :=
            mul_le_mul_of_nonneg_left hsum hscaleNonneg
    _ = 4 * (((d : ℝ) / N) *
          (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            floorBoundaryKernel M₀ hM₀ (((d : ℝ) * (n : ℝ)) ^ c))) := by ring
    _ ≤ 4 * (3 * N ^ (-η / 2)) := mul_le_mul_of_nonneg_left hbase' (by norm_num)
    _ = 12 * N ^ (-η / 2) := by ring

/-- The exact fixed-cutoff prefix bound used in `ar:short-remainder`.
The kernel retains `floor(K^η)` while the endpoint is `2K`; the proof passes
through the fourfold comparison with `floor((2K)^η)`. -/
theorem fixedCutoffBoundaryPrefix {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ K₀ : ℝ, 3 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      let M : ℕ := Nat.floor (K ^ η)
      ∃ hM : 2 ≤ M,
        (1 / (2 * K)) *
          (∑ n ∈ realIntegerInterval 0 (2 * K),
            floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤
          12 * (2 * K) ^ (-η / 2) := by
  dsimp only
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  obtain ⟨N₀, hN₀, hprogression⟩ :=
    boundaryErrorProgression_of_fourfold_fixed_cutoff hc hcNon
  have hηpos : 0 < η := by dsimp [η, j]; positivity
  obtain ⟨Kthree, hKthree, hKpower⟩ :=
    exists_real_rpow_threshold (C := 3) (s := η) hηpos
  let K₀ : ℝ := max 3 (max (N₀ / 2) Kthree)
  have hK₀ : 3 ≤ K₀ := by
    dsimp [K₀]
    exact le_max_left _ _
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK
  let M : ℕ := Nat.floor (K ^ η)
  have hKge : 3 ≤ K := le_trans hK₀ hK
  have hKpos : 0 < K := by linarith
  have hKthree' : Kthree ≤ K := by
    have hle : Kthree ≤ max (N₀ / 2) Kthree := le_max_right _ _
    dsimp [K₀] at hK
    exact le_trans hle (le_trans (le_max_right _ _) hK)
  have hKpow3 : 3 ≤ K ^ η := hKpower K hKthree'
  have hKpow2 : 2 ≤ K ^ η := by linarith
  have hM : 2 ≤ M := by
    have hfloor := Nat.lt_floor_add_one (K ^ η)
    dsimp [M]
    exact_mod_cast (by nlinarith [hfloor, hKpow3] :
      (2 : ℝ) ≤ (Nat.floor (K ^ η) : ℝ))
  have hN : N₀ ≤ 2 * K := by
    have hhalf : N₀ / 2 ≤ K := by
      have hle : N₀ / 2 ≤ max (N₀ / 2) Kthree := le_max_left _ _
      dsimp [K₀] at hK
      exact le_trans hle (le_trans (le_max_right _ _) hK)
    linarith
  have hfourfold :
      (Nat.floor ((2 * K) ^ η) : ℝ) ≤ 4 * (M : ℝ) := by
    have hfloorTop :
        (Nat.floor ((2 * K) ^ η) : ℝ) ≤ (2 * K) ^ η :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have hmulrpow : (2 * K) ^ η = (2 : ℝ) ^ η * K ^ η := by
      rw [show 2 * K = (2 : ℝ) * K by ring, Real.mul_rpow (by norm_num) hKpos.le]
    have hηle : η ≤ 1 := by
      have hjNat : 1 ≤ j := by dsimp [j]; omega
      have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjNat
      have hpowNat : 1 ≤ 2 ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (j : ℝ) := by exact_mod_cast hpowNat
      have hden : 100 ≤ 100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ) := by
        calc
          100 = 100 * 1 * 1 := by ring
          _ ≤ 100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ) := by gcongr
      dsimp [η]
      rw [div_le_iff₀ (by positivity :
        0 < 100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))]
      nlinarith [hden]
    have htwoη : (2 : ℝ) ^ η ≤ 2 :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hηle |>.trans_eq
        (Real.rpow_one 2)
    have hfloorhalf : K ^ η / 2 ≤ (M : ℝ) :=
      natFloor_cast_ge_half_of_two_le hKpow2
    have htopBound : (2 * K) ^ η ≤ 2 * K ^ η := by
      rw [hmulrpow]
      exact mul_le_mul_of_nonneg_right htwoη
        (Real.rpow_nonneg (by linarith [hKge]) _)
    have hfloorTop' : (Nat.floor ((2 * K) ^ η) : ℝ) ≤ 2 * K ^ η := by
      calc
        (Nat.floor ((2 * K) ^ η) : ℝ) ≤ (2 * K) ^ η := hfloorTop
        _ = (2 : ℝ) ^ η * K ^ η := hmulrpow
        _ ≤ 2 * K ^ η := by rw [← hmulrpow]; exact htopBound
    nlinarith
  have hbase := hprogression (2 * K) hN
  dsimp only at hbase
  rcases hbase with ⟨hM0, hprogression'⟩
  have hbound := hprogression' M hfourfold hM 1 (by norm_num)
    (by
      have hlog : 0 ≤ Real.log (2 * K) := Real.log_nonneg (by nlinarith [hKge])
      exact_mod_cast (Real.one_le_exp_iff.mpr
        (Real.rpow_nonneg hlog (3 / 10 : ℝ))))
  refine ⟨hM, ?_⟩
  simpa [M, j, η] using hbound

#print axioms min_one_le_four_min_one_of_le_four_mul
#print axioms floorBoundaryKernel_le_four_mul_of_cutoff_le
#print axioms boundaryErrorProgression_of_fourfold_fixed_cutoff
#print axioms fixedCutoffBoundaryPrefix

end FractionalPrimes
