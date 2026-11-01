module

public import FractionalPrimes.PolynomialCorrelationControlsPolynomial

@[expose] public section

namespace FractionalPrimes

open MeasureTheory

/-- Convert the Taylor module used by Mathlib's Taylor theorem into the real
polynomial whose phases occur in the polynomial-correlation seminorm. -/
private noncomputable def fractionalPowerTaylorPolynomial
    (c K X H : ℝ) : Polynomial ℝ :=
  let z : ℝ := X + H / 2
  ∑ i ∈ Finset.range ((arithmeticParameters c).k + 1),
    (Polynomial.X - Polynomial.C z) ^ i *
      Polynomial.C (taylorCoeffWithin (fun x : ℝ => x ^ c) i
        (Set.Icc K (2 * K)) z)

private theorem fractionalPowerTaylorPolynomial_eval
    (c K X H t : ℝ) :
    (fractionalPowerTaylorPolynomial c K X H).eval t =
      taylorWithinEval (fun x : ℝ => x ^ c) (arithmeticParameters c).k
        (Set.Icc K (2 * K)) (X + H / 2) t := by
  simp [fractionalPowerTaylorPolynomial, taylorWithinEval, taylorWithin,
    PolynomialModule.eval_single, PolynomialModule.comp_eval,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X]

private theorem fractionalPowerTaylorPolynomial_natDegree_le
    (c K X H : ℝ) :
    (fractionalPowerTaylorPolynomial c K X H).natDegree ≤
      (arithmeticParameters c).k := by
  let p := arithmeticParameters c
  let z : ℝ := X + H / 2
  have hsum : fractionalPowerTaylorPolynomial c K X H =
      ∑ i ∈ Finset.range (p.k + 1),
        (Polynomial.X - Polynomial.C z) ^ i *
          Polynomial.C (taylorCoeffWithin (fun x : ℝ => x ^ c) i
            (Set.Icc K (2 * K)) z) := by
    simp [fractionalPowerTaylorPolynomial, p, z]
  rw [hsum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i < p.k + 1 := Finset.mem_range.mp hi
  calc
    ((Polynomial.X - Polynomial.C z) ^ i *
        Polynomial.C (taylorCoeffWithin (fun x : ℝ => x ^ c) i
          (Set.Icc K (2 * K)) z)).natDegree ≤
      ((Polynomial.X - Polynomial.C z) ^ i).natDegree +
        (Polynomial.C (taylorCoeffWithin (fun x : ℝ => x ^ c) i
          (Set.Icc K (2 * K)) z)).natDegree :=
        Polynomial.natDegree_mul_le
    _ = i := by simp only [Polynomial.natDegree_pow,
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_C, Nat.mul_one,
      Nat.add_zero]
    _ ≤ p.k := by omega

/-- The local weighted floor-removal reduction from `ar:local-weighted`.
The sole scale-side premise is that the blueprint's exact floor cutoff is at
least two; the eventual-threshold wrapper is provided below. -/
theorem localWeightedPolynomialReduction_of_cutoff_ge_two
    {c K X H ξ : ℝ} (hc : 1 < c) (hK : 1 ≤ K)
    (hX : K ≤ X) (hHpos : 0 < H) (hXH : X + H ≤ 2 * K)
    (hHupper : H ≤ K ^ (arithmeticParameters c).θ)
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (hI : (realIntegerInterval X H).Nonempty)
    (w : ℤ → ℂ)
    (hM : 2 ≤ Nat.floor (K ^ (arithmeticParameters c).η)) :
    let p := arithmeticParameters c
    let I := realIntegerInterval X H
    let M := Nat.floor (K ^ p.η)
    let Cc := 12 * max 1
      (4 * Real.pi * |(descPochhammer ℝ (p.k + 1)).eval c|)
    ‖(∑ n ∈ I, w n *
        unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) /
      (I.card : ℂ)‖ ≤
      Cc * Real.log (2 * K) *
        (polynomialCorrelation (p.k + 1) I w +
          polynomialCorrelationSupNorm I w hI *
            ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) /
                (I.card : ℝ) + K ^ (-2 : ℝ))) := by
  dsimp only
  let p := arithmeticParameters c
  let I : Finset ℤ := realIntegerInterval X H
  let M : ℕ := Nat.floor (K ^ p.η)
  let Poch : ℝ := |(descPochhammer ℝ (p.k + 1)).eval c|
  let D : ℝ := 4 * Real.pi * Poch
  let Cc : ℝ := 12 * max 1 D
  let L : ℝ := (I.card : ℝ)
  let LC : ℂ := (I.card : ℂ)
  let A : ℝ := 12 * Real.log (2 * (M : ℝ))
  let Q : Polynomial ℝ := fractionalPowerTaylorPolynomial c K X H
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hηbounds := arithmeticParameters_eta_pos_lt_one hc
  dsimp only at hηbounds
  have hηpos : 0 < p.η := by simpa [p] using hηbounds.1
  have hηlt : p.η < 1 := by simpa [p] using hηbounds.2
  have hKpow : K ^ p.η ≤ K := by
    calc
      K ^ p.η ≤ K ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hηlt.le
      _ = K := Real.rpow_one K
  have hMle : (M : ℝ) ≤ K := by
    dsimp [M, p]
    exact (Nat.floor_le (Real.rpow_nonneg hKpos.le _)).trans hKpow
  have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) := by
    apply Real.log_nonneg
    have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith
  have hlogK : 0 ≤ Real.log (2 * K) :=
    Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 2 * K)
  have hlogMono : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * K) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hA_le : A ≤ Cc * Real.log (2 * K) := by
    dsimp [A, Cc, D]
    calc
      12 * Real.log (2 * (M : ℝ)) ≤ 12 * Real.log (2 * K) :=
        mul_le_mul_of_nonneg_left hlogMono (by norm_num)
      _ ≤ (12 * max 1 (4 * Real.pi * Poch)) * Real.log (2 * K) :=
        mul_le_mul_of_nonneg_right (by
          have hle : 1 ≤ max 1 (4 * Real.pi * Poch) := le_max_left _ _
          nlinarith) hlogK
  have hD_nonneg : 0 ≤ D := by dsimp [D, Poch]; positivity
  have hAD_le : A * D ≤ Cc * Real.log (2 * K) := by
    dsimp [A, Cc, D]
    have hDle : 4 * Real.pi * Poch ≤ max 1 (4 * Real.pi * Poch) :=
      le_max_right _ _
    calc
      (12 * Real.log (2 * (M : ℝ))) * (4 * Real.pi * Poch) =
          (12 * (4 * Real.pi * Poch)) * Real.log (2 * (M : ℝ)) := by ring
      _ ≤ (12 * max 1 (4 * Real.pi * Poch)) * Real.log (2 * K) := by
        exact mul_le_mul (by nlinarith) hlogMono (by positivity) (by positivity)
  have hCorrNonneg : 0 ≤ polynomialCorrelation (p.k + 1) I w := by
    have hzero := norm_polynomial_phase_sum_le_polynomialCorrelation
      (s := p.k + 1) (I := I) (w := w) (P := 0) hI (by simp)
    exact le_trans (norm_nonneg _) hzero
  have hSupNonneg : 0 ≤ polynomialCorrelationSupNorm I w hI := by
    have hI_nonempty := hI
    obtain ⟨n, hn⟩ := hI_nonempty
    exact le_trans (norm_nonneg (w n))
      (norm_le_polynomialCorrelationSupNorm hI hn)
  have hLpos : 0 < L := by
    dsimp [L, I]
    exact_mod_cast Finset.card_pos.mpr hI
  have hLCnorm : ‖LC‖ = L := by
    dsimp [LC, L]
    simp
  have hxiAbs : |ξ| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hcoef := (floorFourierRemoval (t := 0) M hM hξlo hξhi).1
  have hboundSum :
      ‖(∑ n ∈ I, w n *
        unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
        ∑ n ∈ I, w n * floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M‖ ≤
        A * polynomialCorrelationSupNorm I w hI *
          ∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c) := by
    have hsumEq :
        (∑ n ∈ I, w n *
          unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
          ∑ n ∈ I, w n * floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M =
        ∑ n ∈ I, w n *
          (unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)) -
            floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    have hpoint : ∀ n ∈ I,
        ‖w n *
          (unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)) -
            floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M)‖ ≤
          polynomialCorrelationSupNorm I w hI *
            (A * floorBoundaryKernel M hM ((n : ℝ) ^ c)) := by
      intro n hn
      have hweight := norm_le_polynomialCorrelationSupNorm (I := I) (w := w) hI hn
      have hrem := (floorFourierRemoval (t := (n : ℝ) ^ c) M hM hξlo hξhi).2
      dsimp [A]
      rw [norm_mul]
      exact mul_le_mul hweight hrem (norm_nonneg _) (by positivity)
    calc
      _ = ‖∑ n ∈ I, w n *
          (unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)) -
            floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M)‖ := by rw [hsumEq]
      _ ≤ ∑ n ∈ I, ‖w n *
          (unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)) -
            floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ I, polynomialCorrelationSupNorm I w hI *
          (A * floorBoundaryKernel M hM ((n : ℝ) ^ c)) := Finset.sum_le_sum hpoint
      _ = A * polynomialCorrelationSupNorm I w hI *
          ∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  have hQdegree : Q.natDegree ≤ p.k := by
    dsimp [Q]
    exact fractionalPowerTaylorPolynomial_natDegree_le c K X H
  have hTaylorPoint : ∀ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∀ n ∈ I,
      ‖unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)) -
        unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))‖ ≤ D * K ^ (-2 : ℝ) := by
    intro m hm n hn
    have hmI := Finset.mem_Icc.mp hm
    have hmNat : Int.natAbs m ≤ M := by
      rcases m with m | m
      · simp_all [M]
      · simp_all [M]
        omega
    have hnI := (mem_realIntegerInterval_iff X H n).mp hn
    have hnK : K ≤ (n : ℝ) := le_trans hX (le_of_lt hnI.1)
    have hTaylor := arithmeticParameters_taylor_midpoint_error
      hc hK hHpos.le hHupper hX hXH (le_of_lt hnI.1) hnI.2 hmNat hxiAbs
    have hpolyEval := fractionalPowerTaylorPolynomial_eval c K X H (n : ℝ)
    have hphase := norm_unitFrequencyPhase_mul_sub_le
      ((m : ℝ) + ξ) ((n : ℝ) ^ c) (Q.eval (n : ℝ))
    have hrem : |((m : ℝ) + ξ) *
        ((n : ℝ) ^ c - Q.eval (n : ℝ))| ≤ 2 * Poch * K ^ (-2 : ℝ) := by
      simpa [Q, Poch, hpolyEval] using hTaylor
    dsimp [D]
    calc
      _ ≤ 2 * Real.pi * |(m : ℝ) + ξ| *
          |(n : ℝ) ^ c - Q.eval (n : ℝ)| := hphase
      _ = 2 * Real.pi * |((m : ℝ) + ξ) *
          ((n : ℝ) ^ c - Q.eval (n : ℝ))| := by rw [abs_mul, mul_assoc]
      _ ≤ 2 * Real.pi * (2 * Poch * K ^ (-2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hrem (by positivity)
      _ = (4 * Real.pi * Poch) * K ^ (-2 : ℝ) := by ring
  have hTaylorSum :
      ‖(∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)))) -
        (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))))‖ ≤
        A * polynomialCorrelationSupNorm I w hI * (I.card : ℝ) *
          (D * K ^ (-2 : ℝ)) := by
    have houterEq :
        (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            floorFourierCoefficient m ξ *
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)))) -
          (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            floorFourierCoefficient m ξ *
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))) =
        ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            ((∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c))) -
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      rw [mul_sub]
    have hinner : ∀ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ‖(∑ n ∈ I, w n *
            unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c))) -
          (∑ n ∈ I, w n *
            unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))‖ ≤
        (I.card : ℝ) * polynomialCorrelationSupNorm I w hI *
          (D * K ^ (-2 : ℝ)) := by
      intro m hm
      have hsumEq :
          (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c))) -
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))) =
          ∑ n ∈ I, w n *
            (unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)) -
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      have hpoint : ∀ n ∈ I,
          ‖w n * (unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)) -
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))‖ ≤
            ‖w n‖ * (D * K ^ (-2 : ℝ)) := by
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hTaylorPoint m hm n hn) (norm_nonneg _)
      calc
        _ = ‖∑ n ∈ I, w n *
            (unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)) -
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))‖ := by rw [hsumEq]
        _ ≤ ∑ n ∈ I, ‖w n *
            (unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)) -
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ I, ‖w n‖ * (D * K ^ (-2 : ℝ)) := Finset.sum_le_sum hpoint
        _ ≤ (I.card : ℝ) * polynomialCorrelationSupNorm I w hI *
            (D * K ^ (-2 : ℝ)) := by
              have hnormSum : (∑ n ∈ I, ‖w n‖) ≤
                  (I.card : ℝ) * polynomialCorrelationSupNorm I w hI := by
                have h := Finset.sum_le_card_nsmul I
                  (fun n : ℤ => ‖w n‖)
                  (polynomialCorrelationSupNorm I w hI)
                  (by
                    intro n hn
                    exact norm_le_polynomialCorrelationSupNorm
                      (I := I) (w := w) hI hn)
                simpa [nsmul_eq_mul] using h
              have hCnonneg : 0 ≤ D * K ^ (-2 : ℝ) :=
                mul_nonneg hD_nonneg (Real.rpow_nonneg hKpos.le _)
              calc
                _ = (∑ n ∈ I, ‖w n‖) * (D * K ^ (-2 : ℝ)) := by
                  rw [← Finset.sum_mul]
                _ ≤ ((I.card : ℝ) * polynomialCorrelationSupNorm I w hI) *
                    (D * K ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_right hnormSum hCnonneg
                _ = (I.card : ℝ) * polynomialCorrelationSupNorm I w hI *
                    (D * K ^ (-2 : ℝ)) := by ring
    have houterPoint : ∀ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ‖floorFourierCoefficient m ξ *
          ((∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c))) -
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))))‖ ≤
        ‖floorFourierCoefficient m ξ‖ *
          ((I.card : ℝ) * polynomialCorrelationSupNorm I w hI *
            (D * K ^ (-2 : ℝ))) := by
      intro m hm
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hinner m hm) (norm_nonneg _)
    calc
      _ = ‖∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            ((∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c))) -
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))))‖ := by rw [houterEq]
      _ ≤ ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ‖floorFourierCoefficient m ξ *
            ((∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c))) -
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))))‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ‖floorFourierCoefficient m ξ‖ *
            ((I.card : ℝ) * polynomialCorrelationSupNorm I w hI *
              (D * K ^ (-2 : ℝ))) := Finset.sum_le_sum houterPoint
      _ = (I.card : ℝ) * polynomialCorrelationSupNorm I w hI *
            (D * K ^ (-2 : ℝ)) *
          ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            ‖floorFourierCoefficient m ξ‖ := by
              rw [← Finset.sum_mul]
              ring
      _ ≤ A * polynomialCorrelationSupNorm I w hI * (I.card : ℝ) *
            (D * K ^ (-2 : ℝ)) := by
              dsimp [A]
              have hcoeffNorm : 0 ≤ polynomialCorrelationSupNorm I w hI *
                  (I.card : ℝ) * (D * K ^ (-2 : ℝ)) := by positivity
              nlinarith [mul_le_mul_of_nonneg_left hcoef hcoeffNorm]
  have hPolyBound :
      ‖(∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))) / LC‖ ≤
        A * polynomialCorrelation (p.k + 1) I w := by
    have hdivsum :
        (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))) / LC =
        ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            ((∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))) / LC) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro m hm
      rw [mul_div_assoc]
    have hcontrol : ∀ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ‖(∑ n ∈ I, w n *
          unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))) / LC‖ ≤
          polynomialCorrelation (p.k + 1) I w := by
      intro m hm
      let R : Polynomial ℝ := Polynomial.C (-((m : ℝ) + ξ)) * Q
      have hRdegree : R.natDegree ≤ p.k := by
        dsimp [R]
        calc
          _ ≤ (Polynomial.C (-((m : ℝ) + ξ))).natDegree + Q.natDegree :=
            Polynomial.natDegree_mul_le
          _ = Q.natDegree := by rw [Polynomial.natDegree_C, zero_add]
          _ ≤ p.k := hQdegree
      have hphase : ∀ n : ℤ,
          unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)) =
            unitFrequencyPhase (-(R.eval (n : ℝ))) := by
        intro n
        simp [R, Polynomial.eval_mul, Polynomial.eval_C]
        congr 1
        ring
      simpa [LC, hphase] using
        norm_polynomial_phase_sum_le_polynomialCorrelation
          (s := p.k + 1) (I := I) (w := w) (P := R) hI
          (by simpa using hRdegree)
    have hpoint : ∀ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ‖floorFourierCoefficient m ξ *
          ((∑ n ∈ I, w n *
            unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))) / LC)‖ ≤
        ‖floorFourierCoefficient m ξ‖ *
          polynomialCorrelation (p.k + 1) I w := by
      intro m hm
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hcontrol m hm) (norm_nonneg _)
    rw [hdivsum]
    calc
      _ ≤ ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ‖floorFourierCoefficient m ξ *
            ((∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))) / LC)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ‖floorFourierCoefficient m ξ‖ *
            polynomialCorrelation (p.k + 1) I w := Finset.sum_le_sum hpoint
      _ = polynomialCorrelation (p.k + 1) I w *
          ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            ‖floorFourierCoefficient m ξ‖ := by
              rw [← Finset.sum_mul]
              ring
      _ ≤ A * polynomialCorrelation (p.k + 1) I w := by
        have hcoefNorm : 0 ≤ polynomialCorrelation (p.k + 1) I w := hCorrNonneg
        dsimp [A]
        calc
          _ ≤ polynomialCorrelation (p.k + 1) I w *
              (12 * Real.log (2 * (M : ℝ))) :=
                mul_le_mul_of_nonneg_left hcoef hCorrNonneg
          _ = (12 * Real.log (2 * (M : ℝ))) *
              polynomialCorrelation (p.k + 1) I w := by ring
  have hremNormDiv :
      ‖((∑ n ∈ I, w n *
          unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
        (∑ n ∈ I, w n * floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M)) / LC‖ ≤
        A * polynomialCorrelationSupNorm I w hI *
          ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L) := by
    rw [norm_div, hLCnorm]
    calc
      _ ≤ (A * polynomialCorrelationSupNorm I w hI *
          ∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L :=
        div_le_div_of_nonneg_right hboundSum hLpos.le
      _ = A * polynomialCorrelationSupNorm I w hI *
          ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L) := by
        rw [mul_div_assoc]
  have hTaylorNormDiv :
      ‖((∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)))) -
        (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))))/LC‖ ≤
        A * polynomialCorrelationSupNorm I w hI * (D * K ^ (-2 : ℝ)) := by
    rw [norm_div, hLCnorm]
    have hraw := hTaylorSum
    dsimp only [L]
    dsimp [LC] at *
    rw [div_eq_mul_inv]
    calc
      ‖(∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)))) -
        (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ))))‖ / L ≤
          (A * polynomialCorrelationSupNorm I w hI * L *
            (D * K ^ (-2 : ℝ))) / L := div_le_div_of_nonneg_right hraw hLpos.le
      _ = A * polynomialCorrelationSupNorm I w hI * (D * K ^ (-2 : ℝ)) := by
        field_simp [ne_of_gt hLpos]
        <;> ring
  have hS1eq :
      (∑ n ∈ I, w n * floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M) =
        ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ I, w n *
              unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c))) := by
    simp only [floorFourierShiftedPartialSum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have htarget_decomp :
      (∑ n ∈ I, w n *
          unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) / LC =
        ((∑ n ∈ I, w n *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
          (∑ n ∈ I, w n * floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M)) / LC +
        ((∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            floorFourierCoefficient m ξ *
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)))) -
          (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            floorFourierCoefficient m ξ *
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))))/LC +
        (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            floorFourierCoefficient m ξ *
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))) / LC := by
    rw [hS1eq]
    ring
  have hnormFinal :
      ‖(∑ n ∈ I, w n *
          unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) / LC‖ ≤
        A * polynomialCorrelation (p.k + 1) I w +
          A * polynomialCorrelationSupNorm I w hI *
            ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L +
              D * K ^ (-2 : ℝ)) := by
    rw [htarget_decomp]
    calc
      _ ≤ ‖((∑ n ∈ I, w n *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
          (∑ n ∈ I, w n * floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M)) / LC‖ +
        ‖((∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            floorFourierCoefficient m ξ *
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)))) -
          (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            floorFourierCoefficient m ξ *
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))))/LC‖ +
        ‖(∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            floorFourierCoefficient m ξ *
              (∑ n ∈ I, w n *
                unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))) / LC‖ := by
          let u : ℂ :=
            ((∑ n ∈ I, w n *
                unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
              (∑ n ∈ I, w n * floorFourierShiftedPartialSum ξ ((n : ℝ) ^ c) M)) / LC
          let v : ℂ :=
            ((∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
                floorFourierCoefficient m ξ *
                  (∑ n ∈ I, w n *
                    unitFrequencyPhase (((m : ℝ) + ξ) * ((n : ℝ) ^ c)))) -
              (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
                floorFourierCoefficient m ξ *
                  (∑ n ∈ I, w n *
                    unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))))/LC
          let z : ℂ :=
            (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
              floorFourierCoefficient m ξ *
                (∑ n ∈ I, w n *
                  unitFrequencyPhase (((m : ℝ) + ξ) * Q.eval (n : ℝ)))) / LC
          rw [add_assoc]
          change ‖u + (v + z)‖ ≤ ‖u‖ + ‖v‖ + ‖z‖
          calc
            ‖u + (v + z)‖ ≤ ‖u‖ + ‖v + z‖ := norm_add_le _ _
            _ ≤ ‖u‖ + (‖v‖ + ‖z‖) :=
              add_le_add_right (norm_add_le v z) ‖u‖
            _ = ‖u‖ + ‖v‖ + ‖z‖ := by ring
      _ ≤ A * polynomialCorrelationSupNorm I w hI *
            ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L) +
          A * polynomialCorrelationSupNorm I w hI * (D * K ^ (-2 : ℝ)) +
          A * polynomialCorrelation (p.k + 1) I w := by
            gcongr
      _ = A * polynomialCorrelation (p.k + 1) I w +
          A * polynomialCorrelationSupNorm I w hI *
            ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L +
              D * K ^ (-2 : ℝ)) := by ring
  have htargetFinal :
      A * polynomialCorrelation (p.k + 1) I w +
        A * polynomialCorrelationSupNorm I w hI *
          ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L +
            D * K ^ (-2 : ℝ)) ≤
      Cc * Real.log (2 * K) *
        (polynomialCorrelation (p.k + 1) I w +
          polynomialCorrelationSupNorm I w hI *
            ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L + K ^ (-2 : ℝ))) := by
    dsimp [Cc, D]
    have hFnonneg : 0 ≤
        (∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L := by
      apply div_nonneg
      · exact Finset.sum_nonneg fun n hn => floorBoundaryKernel_nonneg M hM _
      · exact hLpos.le
    have hKpowNonneg : 0 ≤ K ^ (-2 : ℝ) := Real.rpow_nonneg hKpos.le _
    have hKpowPos : 0 ≤ K ^ (-2 : ℝ) := hKpowNonneg
    have hDge1 : 1 ≤ max 1 (4 * Real.pi * Poch) := le_max_left _ _
    have hDle : 4 * Real.pi * Poch ≤ max 1 (4 * Real.pi * Poch) := le_max_right _ _
    have hbase : A ≤ 12 * max 1 (4 * Real.pi * Poch) * Real.log (2 * K) := hA_le
    have hbaseD : A * (4 * Real.pi * Poch) ≤
        12 * max 1 (4 * Real.pi * Poch) * Real.log (2 * K) := hAD_le
    have hCorr := mul_le_mul_of_nonneg_right hA_le hCorrNonneg
    have hBoundary := mul_le_mul_of_nonneg_right hA_le hFnonneg
    have hTaylor := mul_le_mul_of_nonneg_right hAD_le hKpowPos
    have hsum := add_le_add hCorr
      (add_le_add
        (mul_le_mul_of_nonneg_left hBoundary hSupNonneg)
        (mul_le_mul_of_nonneg_left hTaylor hSupNonneg))
    calc
      _ ≤ Cc * Real.log (2 * K) * polynomialCorrelation (p.k + 1) I w +
          (Cc * Real.log (2 * K) * polynomialCorrelationSupNorm I w hI) *
            ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L) +
          (Cc * Real.log (2 * K) * polynomialCorrelationSupNorm I w hI) *
            K ^ (-2 : ℝ) := by
              dsimp [Cc]
              nlinarith [hCorr, hBoundary, hTaylor]
      _ = Cc * Real.log (2 * K) *
          (polynomialCorrelation (p.k + 1) I w +
            polynomialCorrelationSupNorm I w hI *
              ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) / L +
                K ^ (-2 : ℝ))) := by ring
  exact hnormFinal.trans htargetFinal

/-- A real cutoff beyond which the exact floor frequency range has length at
least two. It is chosen from Mathlib's real-power divergence theorem. -/
noncomputable def localWeightedReductionThreshold
    (c : ℝ) (hc : 1 < c) : ℝ :=
  Classical.choose (exists_real_rpow_threshold (C := 4)
    (s := (arithmeticParameters c).η)
    (arithmeticParameters_eta_pos_lt_one hc).1)

private theorem localWeightedReductionThreshold_spec
    (c : ℝ) (hc : 1 < c) :
    1 ≤ localWeightedReductionThreshold c hc ∧
      ∀ K : ℝ, localWeightedReductionThreshold c hc ≤ K →
        4 ≤ K ^ (arithmeticParameters c).η := by
  exact Classical.choose_spec
    (exists_real_rpow_threshold (C := 4)
      (s := (arithmeticParameters c).η)
      (arithmeticParameters_eta_pos_lt_one hc).1)

/-- The chosen scale threshold guarantees the floor cutoff required by the
paper-facing weighted floor reduction. -/
theorem localWeightedReductionCutoff_ge_two
    {c K : ℝ} (hc : 1 < c)
    (hK : localWeightedReductionThreshold c hc ≤ K) :
    2 ≤ Nat.floor (K ^ (arithmeticParameters c).η) := by
  have hKpow := (localWeightedReductionThreshold_spec c hc).2 K hK
  have hfloor := natFloor_cast_ge_half_of_two_le
    (le_trans (by norm_num) hKpow)
  have hfloorCast : 2 ≤
      (Nat.floor (K ^ (arithmeticParameters c).η) : ℝ) := by linarith
  exact_mod_cast hfloorCast

/-- The paper-facing `ar:local-weighted` statement. Its fixed threshold is
chosen from the exact positive blueprint exponent `η`, so the floor cutoff
condition used in the checked core follows for every admissible large scale. -/
theorem localWeightedPolynomialReduction
    {c : ℝ} (hc : 1 < c) :
    let K₀ := localWeightedReductionThreshold c hc
    1 ≤ K₀ ∧ ∀ K X H ξ : ℝ, ∀ w : ℤ → ℂ,
      ∀ (hKlarge : K₀ ≤ K),
        let hM : 2 ≤ Nat.floor (K ^ (arithmeticParameters c).η) :=
          localWeightedReductionCutoff_ge_two hc hKlarge
        K ≤ X → 0 < H → X + H ≤ 2 * K →
        H ≤ K ^ (arithmeticParameters c).θ →
        -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        (hI : (realIntegerInterval X H).Nonempty) →
        let p := arithmeticParameters c
        let I := realIntegerInterval X H
        let M := Nat.floor (K ^ p.η)
        let Cc := 12 * max 1
          (4 * Real.pi * |(descPochhammer ℝ (p.k + 1)).eval c|)
        ‖(∑ n ∈ I, w n *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) /
          (I.card : ℂ)‖ ≤
          Cc * Real.log (2 * K) *
            (polynomialCorrelation (p.k + 1) I w +
              polynomialCorrelationSupNorm I w hI *
                ((∑ n ∈ I, floorBoundaryKernel M hM ((n : ℝ) ^ c)) /
                    (I.card : ℝ) + K ^ (-2 : ℝ))) := by
  dsimp only
  have hthreshold := localWeightedReductionThreshold_spec c hc
  refine ⟨hthreshold.1, ?_⟩
  intro K X H ξ w hKlarge hX hHpos hXH hHupper hξlo hξhi hI
  have hK : 1 ≤ K := hthreshold.1.trans hKlarge
  exact localWeightedPolynomialReduction_of_cutoff_ge_two
    hc hK hX hHpos hXH hHupper hξlo hξhi hI w
      (localWeightedReductionCutoff_ge_two hc hKlarge)

end FractionalPrimes
