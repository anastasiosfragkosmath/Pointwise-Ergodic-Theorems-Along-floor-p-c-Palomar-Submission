module
public import FractionalPrimes.Final.ForwardAverageFacts

public import FractionalPrimes.Chebyshev

/-!
# Prime and higher prime-power parts

This file records the finite operator decomposition in blueprint `er:primeparts`
and the exact scalar mass estimate for its higher-prime-power part.
-/


@[expose] public section

open scoped Nat.Prime

namespace FractionalPrimes.Final

noncomputable section

def paperPrimeOnlyPart {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (f : X → ℂ) (N : Scale) : X → ℂ :=
  fun x => (N.1 : ℂ)⁻¹ *
    ∑ p ∈ (Finset.Icc 1 N.1).filter Nat.Prime,
      (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c p) x)

def paperHigherPrimePowerPart {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (f : X → ℂ) (N : Scale) : X → ℂ :=
  fun x => (N.1 : ℂ)⁻¹ *
    ∑ k ∈ (Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊).filter (fun k => 2 ≤ k),
      ∑ p ∈ (Finset.Ioc 0
          ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime,
        (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c (p ^ k)) x)

def paperHigherPrimePowerMass (N : Scale) : ℝ :=
  (N.1 : ℝ)⁻¹ * paperHigherPrimePowerPairSum N.1

/-- The root cutoff from Mathlib's unique-prime-power reindexing is exactly
the manuscript's finite prime-power condition. -/
theorem paperPrimeRootFilter_eq_primePowerFilter {N k : ℕ} (hk : 0 < k) :
    (Finset.Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime =
      (Finset.Icc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter
        (fun p => Nat.Prime p ∧ p ^ k ≤ N) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hp0, hroot⟩, hp⟩
    have hpow := (prime_le_floor_root_iff_pow_le hp.pos hk).1 hroot
    exact ⟨⟨Nat.zero_le p, hroot⟩, hp, hpow⟩
  · rintro ⟨⟨_, hroot⟩, hp, hpow⟩
    have hroot' := (prime_le_floor_root_iff_pow_le hp.pos hk).2 hpow
    exact ⟨⟨hp.pos, hroot'⟩, hp⟩

private theorem paperMangoldtNumerator_eq_prime_parts
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) (f : X → ℂ) (N : Scale) (x : X) :
    (∑ n ∈ Finset.Icc 1 N.1,
      (vonMangoldtWeight n : ℂ) * f (S.forwardTime (floorPower c n) x)) =
    (∑ p ∈ (Finset.Icc 1 N.1).filter Nat.Prime,
      (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c p) x)) +
    (∑ k ∈ (Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊).filter
        (fun k => 2 ≤ k),
      ∑ p ∈ (Finset.Ioc 0
          ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime,
        (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c (p ^ k)) x)) := by
  classical
  have hN : 0 < N.1 := N.2
  let g : ℕ → ℂ := fun n =>
    (vonMangoldtWeight n : ℂ) * f (S.forwardTime (floorPower c n) x)
  by_cases htwo : 2 ≤ N.1
  · have hinterval : Finset.Icc 1 N.1 = Finset.Ioc 0 N.1 := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hsupport :
        (∑ n ∈ Finset.Ioc 0 N.1, g n) =
          ∑ n ∈ Finset.Ioc 0 N.1 with IsPrimePow n, g n := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hnot
      have hnp : ¬IsPrimePow n := by
        intro hp
        apply hnot
        exact Finset.mem_filter.mpr ⟨hn, hp⟩
      simp [g, vonMangoldtWeight, ArithmeticFunction.vonMangoldt_apply, hnp]
    have hK : 1 ≤ ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊ := by
      apply Nat.le_floor
      apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
      have htwoReal : (2 : ℝ) ≤ (N.1 : ℝ) := by exact_mod_cast htwo
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwoReal
      calc
        (↑(1 : ℕ) : ℝ) * Real.log 2 = Real.log 2 := by norm_num
        _ ≤ Real.log (N.1 : ℝ) := hlog
    have hprimepow := Chebyshev.sum_PrimePow_eq_sum_sum g
      (x := (N.1 : ℝ)) (by positivity)
    have hprimepow' :
        (∑ n ∈ Finset.Ioc 0 N.1 with IsPrimePow n, g n) =
          ∑ k ∈ Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊,
            ∑ p ∈ Finset.Ioc 0
                ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
              g (p ^ k) := by
      simpa only [Nat.floor_natCast] using hprimepow
    have hcoeff :
        (∑ k ∈ Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊,
          ∑ p ∈ Finset.Ioc 0
              ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
            g (p ^ k)) =
        ∑ k ∈ Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊,
          ∑ p ∈ Finset.Ioc 0
              ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
            (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c (p ^ k)) x) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro p hp
      have hprime : p.Prime := (Finset.mem_filter.mp hp).2
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      simp only [g, vonMangoldtWeight]
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hprime]
    have hsplit :
        Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊ =
          insert 1 (Finset.Icc 2 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hfirst :
        (∑ p ∈ Finset.Ioc 0
            ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (1 : ℝ))⌋₊ with Nat.Prime p,
          (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c (p ^ 1)) x)) =
        ∑ p ∈ (Finset.Icc 1 N.1).filter Nat.Prime,
          (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c p) x) := by
      have hpow : (N.1 : ℝ) ^ ((1 : ℝ) / (1 : ℝ)) = (N.1 : ℝ) := by
        norm_num
      simp only [hpow, Nat.floor_natCast, Nat.pow_one]
      have hsets : Finset.Ioc 0 N.1 = Finset.Icc 1 N.1 := by
        ext p
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hsets]
    have hfirst' := hfirst
    simp only [one_div, inv_one, Nat.pow_one] at hfirst'
    have hrest :
        (∑ k ∈ Finset.Icc 2 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊,
          ∑ p ∈ Finset.Ioc 0
              ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
            (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c (p ^ k)) x)) =
        ∑ k ∈ (Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊).filter
            (fun k => 2 ≤ k),
          ∑ p ∈ Finset.Ioc 0
              ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
            (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c (p ^ k)) x) := by
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    calc
      (∑ n ∈ Finset.Icc 1 N.1, g n) = ∑ n ∈ Finset.Ioc 0 N.1, g n := by
        rw [hinterval]
      _ = ∑ n ∈ Finset.Ioc 0 N.1 with IsPrimePow n, g n := hsupport
      _ = ∑ k ∈ Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊,
            ∑ p ∈ Finset.Ioc 0
                ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
              g (p ^ k) := hprimepow'
      _ = ∑ k ∈ Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊,
            ∑ p ∈ Finset.Ioc 0
                ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
              (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c (p ^ k)) x) := hcoeff
      _ = (∑ p ∈ (Finset.Icc 1 N.1).filter Nat.Prime,
              (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c p) x)) +
          (∑ k ∈ (Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊).filter
              (fun k => 2 ≤ k),
            ∑ p ∈ Finset.Ioc 0
                ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
              (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c (p ^ k)) x)) := by
        calc
          (∑ k ∈ Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊,
              ∑ p ∈ Finset.Ioc 0
                  ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
                (Real.log (p : ℝ) : ℂ) *
                  f (S.forwardTime (floorPower c (p ^ k)) x)) =
            (∑ p ∈ Finset.Ioc 0
                ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (1 : ℝ))⌋₊ with Nat.Prime p,
              (Real.log (p : ℝ) : ℂ) *
                f (S.forwardTime (floorPower c (p ^ 1)) x)) +
            (∑ k ∈ Finset.Icc 2 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊,
              ∑ p ∈ Finset.Ioc 0
                  ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
                (Real.log (p : ℝ) : ℂ) *
                  f (S.forwardTime (floorPower c (p ^ k)) x)) := by
            rw [hsplit, Finset.sum_insert (by simp)]
            simp only [Nat.cast_one, one_div, inv_one, Nat.pow_one]
          _ = (∑ p ∈ (Finset.Icc 1 N.1).filter Nat.Prime,
                (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c p) x)) +
              (∑ k ∈ (Finset.Icc 1 ⌊Real.log (N.1 : ℝ) / Real.log 2⌋₊).filter
                  (fun k => 2 ≤ k),
                ∑ p ∈ Finset.Ioc 0
                    ⌊(N.1 : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with Nat.Prime p,
                  (Real.log (p : ℝ) : ℂ) *
                    f (S.forwardTime (floorPower c (p ^ k)) x)) := by
              simp only [one_div, inv_one, Nat.pow_one]
              rw [hfirst']
              apply add_left_cancel_iff.mpr
              simpa only [one_div] using hrest
  · have hNone : N.1 = 1 := by omega
    have hNval : N = ⟨1, by omega⟩ := Subtype.ext hNone
    rw [hNval]
    have hnotprime : ¬Nat.Prime 1 := by norm_num [Nat.Prime]
    have hprimeSum :
        (∑ p ∈ (Finset.Icc 1 (1 : ℕ)).filter Nat.Prime,
          (Real.log (p : ℝ) : ℂ) * f (S.forwardTime (floorPower c p) x)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hp1 : p = 1 := by
        have hp' := (Finset.mem_filter.mp hp).1
        simp only [Finset.mem_Icc] at hp'
        omega
      subst p
      exact (hnotprime (Finset.mem_filter.mp hp).2).elim
    rw [hprimeSum]
    simp [vonMangoldtWeight, ArithmeticFunction.vonMangoldt_apply]

theorem vonMangoldtAverage_eq_primeParts
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) (f : X → ℂ) (N : Scale) :
    vonMangoldtAverage S c f N =
      paperPrimeOnlyPart S c f N + paperHigherPrimePowerPart S c f N := by
  funext x
  unfold vonMangoldtAverage weightedAverage paperPrimeOnlyPart paperHigherPrimePowerPart
  simp only [System.shift_floorPower_apply]
  rw [paperMangoldtNumerator_eq_prime_parts]
  simp only [Pi.add_apply]
  ring

theorem paperHigherPrimePowerMass_nonneg (N : Scale) :
    0 ≤ paperHigherPrimePowerMass N := by
  unfold paperHigherPrimePowerMass paperHigherPrimePowerPairSum
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro p hp
  exact Real.log_nonneg (by
    have hp' := (Finset.mem_filter.mp hp).2.1
    exact_mod_cast hp'.one_le)

theorem paperHigherPrimePowerMass_le {N : Scale} (hN : 2 ≤ N.1) :
    paperHigherPrimePowerMass N ≤
      (Real.log (N.1 : ℝ)) ^ 2 /
        (Real.log 2 * Real.sqrt (N.1 : ℝ)) := by
  exact paperHigherPrimePowerPairSum_normalized_le_of_two_le hN

end

end FractionalPrimes.Final

#print axioms FractionalPrimes.paperPrimeRootFilter_eq_primePowerFilter
#print axioms FractionalPrimes.vonMangoldtAverage_eq_primeParts
#print axioms FractionalPrimes.paperHigherPrimePowerMass_le

