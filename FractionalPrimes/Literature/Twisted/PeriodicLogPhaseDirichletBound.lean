module

public import FractionalPrimes.Literature.Derivative.DerivativeTestEleven

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

private theorem nat_two_mul_le_two_pow {j : ℕ} (hj : 4 ≤ j) :
    2 * j ≤ 2 ^ j := by
  have aux : ∀ n : ℕ, 4 ≤ n → 2 * n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
        intro hn
        by_cases hn3 : n = 3
        · subst n
          norm_num
        · have hn4 : 4 ≤ n := by omega
          have hprev := ih hn4
          calc
            2 * (n + 1) ≤ 4 * n := by omega
            _ ≤ 2 * (2 ^ n) := by
              nlinarith [Nat.mul_le_mul_left 2 hprev]
            _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]
  exact aux j hj

/-- The exact derivative-test order selected in blueprint item ltw:plain-factor. -/
noncomputable def periodicLogPhaseOrder (alpha A : ℝ) : ℕ :=
  Nat.ceil (2 * A / alpha) + 2

/-- The exact saving exponent delta = alpha / 2^j. -/
noncomputable def periodicLogPhaseSaving (alpha A : ℝ) : ℝ :=
  alpha / (2 : ℝ) ^ periodicLogPhaseOrder alpha A

/-- The exact higher-derivative scale c_j from the source proof. -/
noncomputable def periodicLogPhaseCj (j : ℕ) : ℝ :=
  (Nat.factorial (j - 1) : ℝ) /
    (2 * Real.pi * (2 : ℝ) ^ j)

/-- The exact constant C_{alpha,A} from blueprint item ltw:plain-factor. -/
noncomputable def periodicLogPhaseConstant (alpha A : ℝ) : ℝ :=
  let j := periodicLogPhaseOrder alpha A
  let D : ℝ := (2 : ℝ) ^ j
  let cj := periodicLogPhaseCj j
  let high := ((2 : ℝ) ^ j) ^ (2 / D)
  let second := (((2 : ℝ) ^ j) ^ 2 * cj) ^ (1 / (D - 2))
  let negative := cj ^ (-2 / D)
  max 64 (max ((j : ℝ) + 2) (11 * max high (max second negative)))

/-- The exact source constant dominates the order contribution. -/
theorem periodicLogPhaseConstant_ge_order (alpha A : ℝ) :
    (periodicLogPhaseOrder alpha A : ℝ) + 2 ≤
      periodicLogPhaseConstant alpha A := by
  unfold periodicLogPhaseConstant
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem periodicLogPhaseConstant_ge_highTerms (alpha A : ℝ) :
    let j := periodicLogPhaseOrder alpha A
    let D : ℝ := (2 : ℝ) ^ j
    let c := periodicLogPhaseCj j
    11 * max (D ^ (2 / D))
      (max ((D ^ 2 * c) ^ (1 / (D - 2))) (c ^ (-2 / D))) ≤
        periodicLogPhaseConstant alpha A := by
  dsimp [periodicLogPhaseConstant, periodicLogPhaseCj]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- Ceiling inequalities give the exact order, saving and high-frequency
exponent relations used in the source proof. -/
theorem periodicLogPhaseOrder_bounds
    {alpha A : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hA : 1 ≤ A) :
    4 ≤ periodicLogPhaseOrder alpha A ∧
      A + alpha ≤
        (periodicLogPhaseOrder alpha A : ℝ) * alpha / 2 ∧
      2 * periodicLogPhaseOrder alpha A ≤
        2 ^ periodicLogPhaseOrder alpha A := by
  let j := periodicLogPhaseOrder alpha A
  have hceil : 2 * A / alpha ≤ (Nat.ceil (2 * A / alpha) : ℝ) :=
    Nat.le_ceil _
  have hceilLo : 2 ≤ (Nat.ceil (2 * A / alpha) : ℕ) := by
    have hlo : 2 ≤ 2 * A / alpha := by
      apply (le_div_iff₀ halpha).2
      nlinarith
    exact_mod_cast le_trans hlo hceil
  have hj : 4 ≤ j := by
    dsimp [j, periodicLogPhaseOrder]
    omega
  have hscaled : 2 * A ≤
      (Nat.ceil (2 * A / alpha) : ℝ) * alpha :=
    (div_le_iff₀ halpha).mp hceil
  have hsum : A + alpha ≤ (j : ℝ) * alpha / 2 := by
    dsimp [j, periodicLogPhaseOrder]
    push_cast
    nlinarith [hscaled]
  have hpow : 2 * j ≤ 2 ^ j := nat_two_mul_le_two_pow hj
  exact ⟨by simpa [j] using hj, by simpa [j] using hsum,
    by simpa [j] using hpow⟩

private theorem periodicLogPhase_div_rpow_scale
    {R y N p : ℝ} (hR : 0 ≤ R) (hy : 0 < y) (hN : 0 < N)
    (hyn : y ≤ N) (hp : 0 ≤ 1 - p) :
    y * (R / y) ^ p ≤ N * (R / N) ^ p := by
  have hform (u : ℝ) (hu : 0 < u) :
      u * (R / u) ^ p = R ^ p * u ^ (1 - p) := by
    rw [Real.div_rpow hR hu.le, Real.rpow_sub hu 1 p, Real.rpow_one]
    ring
  rw [hform y hy, hform N hN]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hy.le hyn hp) (Real.rpow_nonneg hR p)

private theorem periodicLogPhase_mul_rpow_power_scale
    {a y N z : ℝ} {k : ℕ} (ha : 0 < a) (hy : 0 < y) (hN : 0 < N)
    (hyn : y ≤ N) (hexp : 0 ≤ 1 + (k : ℝ) * z) :
    y * (a * y ^ k) ^ z ≤ N * (a * N ^ k) ^ z := by
  have hform (u : ℝ) (hu : 0 < u) :
      u * (a * u ^ k) ^ z = a ^ z * u ^ (1 + (k : ℝ) * z) := by
    rw [Real.mul_rpow ha.le (pow_nonneg hu.le k),
      ← Real.rpow_natCast_mul hu.le k z]
    have hpow : u ^ (1 + (k : ℝ) * z) = u * u ^ ((k : ℝ) * z) := by
      rw [Real.rpow_add hu 1 ((k : ℝ) * z), Real.rpow_one]
    rw [hpow]
    ring
  rw [hform y hy, hform N hN]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hy.le hyn hexp) (Real.rpow_nonneg ha.le z)

/-- Exact high-frequency power comparisons from the source proof. This is
the numerical part of the constant-11 branch, before applying the derivative
test to an interval sum. -/
theorem periodicLogPhaseHighScaleTermBounds
    {alpha A X N s Y : ℝ} {j : ℕ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hj : j = periodicLogPhaseOrder alpha A)
    (hNpow : X ^ (alpha / 2) ≤ N) (hsN : N < s) (hsX : s ≤ X ^ A)
    (hY : 0 < Y) (hYN : Y ≤ N) :
    Y * (((2 : ℝ) ^ j / Y) ^ (2 / (2 : ℝ) ^ j)) ≤
        N * (((2 : ℝ) ^ j) ^ (2 / (2 : ℝ) ^ j) *
          X ^ (-(alpha / (2 : ℝ) ^ j))) ∧
      Y * ((((2 : ℝ) ^ j) ^ 2 *
          (periodicLogPhaseCj j * s / N ^ j)) ^
            (1 / ((2 : ℝ) ^ j - 2))) ≤
        N * ((((2 : ℝ) ^ j) ^ 2 * periodicLogPhaseCj j) ^
          (1 / ((2 : ℝ) ^ j - 2)) * X ^ (-(alpha / (2 : ℝ) ^ j))) ∧
      Y * (((periodicLogPhaseCj j * s / N ^ j) * Y ^ j) ^
          (-2 / (2 : ℝ) ^ j)) ≤
        N * (periodicLogPhaseCj j ^ (-2 / (2 : ℝ) ^ j) *
          X ^ (-(alpha / (2 : ℝ) ^ j))) := by
  rcases periodicLogPhaseOrder_bounds halpha halpha1 hA with
    ⟨horderLo, horderSum, horderPow⟩
  have hj4 : 4 ≤ j := by simpa [hj] using horderLo
  have hsum : A + alpha ≤ (j : ℝ) * alpha / 2 := by
    simpa [hj] using horderSum
  have h2j : 2 * j ≤ 2 ^ j := by simpa [hj] using horderPow
  let D : ℝ := (2 : ℝ) ^ j
  let c : ℝ := periodicLogPhaseCj j
  let lam : ℝ := c * s / N ^ j
  let delta : ℝ := alpha / D
  let p1 : ℝ := 2 / D
  let p2 : ℝ := 1 / (D - 2)
  let p3 : ℝ := -2 / D
  change
    Y * (D / Y) ^ p1 ≤ N * (D ^ p1 * X ^ (-delta)) ∧
      Y * (D ^ 2 * lam) ^ p2 ≤
        N * ((D ^ 2 * c) ^ p2 * X ^ (-delta)) ∧
      Y * (lam * Y ^ j) ^ p3 ≤ N * (c ^ p3 * X ^ (-delta))
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hD16 : 16 ≤ D := by
    dsimp [D]
    have hpow : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj4
    norm_num at hpow ⊢
    exact hpow
  have hDminus : 2 < D := by linarith
  have h2jR : 2 * (j : ℝ) ≤ D := by
    dsimp [D]
    exact_mod_cast h2j
  have hNpos : 0 < N :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hNpow
  have hspos : 0 < s := lt_trans hNpos hsN
  have hMpos : 0 < X ^ (alpha / 2) := Real.rpow_pos_of_pos hXpos _
  have hsLower : X ^ (alpha / 2) ≤ s := hNpow.trans hsN.le
  have hcpos : 0 < c := by
    dsimp [c, periodicLogPhaseCj]
    positivity
  have hlampos : 0 < lam := by
    dsimp [lam]
    positivity
  have hp1 : 0 ≤ p1 := by
    dsimp [p1]
    positivity
  have hp2 : 0 < p2 := by
    dsimp [p2]
    positivity
  have hp3 : p3 ≤ 0 := by
    dsimp [p3]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hDpos.le
  have hpow1 : 0 ≤ 1 - p1 := by
    dsimp [p1]
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hDpos).2 (by linarith [hD16])
  have hpow3 : 0 ≤ 1 + (j : ℝ) * p3 := by
    dsimp [p3]
    have hfrac : (j : ℝ) * (2 / D) ≤ 1 := by
      calc
        (j : ℝ) * (2 / D) = (2 * (j : ℝ)) / D := by ring
        _ ≤ 1 := (div_le_iff₀ hDpos).2 (by nlinarith [h2jR])
    calc
      0 ≤ 1 - (j : ℝ) * (2 / D) := sub_nonneg.mpr (by linarith [hfrac])
      _ = 1 + (j : ℝ) * (-2 / D) := by ring
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    exact div_pos halpha hDpos
  have hMpow1 : (X ^ (alpha / 2)) ^ p1 = X ^ delta := by
    calc
      (X ^ (alpha / 2)) ^ p1 = X ^ ((alpha / 2) * p1) := by
        rw [← Real.rpow_mul hXpos.le (alpha / 2) p1]
      _ = X ^ delta := by
        congr 1
        dsimp [p1, delta, D]
        field_simp [ne_of_gt (show (0 : ℝ) < (2 : ℝ) ^ j by positivity)]
        <;> ring
  have hbase1 : D / N ≤ D / (X ^ (alpha / 2)) := by
    apply (div_le_div_iff₀ hNpos hMpos).2
    nlinarith [mul_nonneg (le_of_lt hDpos) (sub_nonneg.mpr hNpow)]
  have hpowBase1 : (D / N) ^ p1 ≤ (D / (X ^ (alpha / 2))) ^ p1 :=
    Real.rpow_le_rpow (div_nonneg (le_of_lt hDpos) hNpos.le) hbase1 hp1
  have hbasePower1 :
      (D / (X ^ (alpha / 2))) ^ p1 ≤ D ^ p1 * X ^ (-delta) := by
    rw [Real.div_rpow (le_of_lt hDpos) hMpos.le, hMpow1,
      div_eq_mul_inv, Real.rpow_neg hXpos.le delta]
  have hterm1 : Y * (D / Y) ^ p1 ≤ N * (D ^ p1 * X ^ (-delta)) := by
    calc
      Y * (D / Y) ^ p1 ≤ N * (D / N) ^ p1 :=
        periodicLogPhase_div_rpow_scale (le_of_lt hDpos) hY hNpos hYN hpow1
      _ ≤ N * (D ^ p1 * X ^ (-delta)) :=
        mul_le_mul_of_nonneg_left (hpowBase1.trans hbasePower1) hNpos.le
  have hMpow3 : (X ^ (alpha / 2)) ^ p3 = X ^ (-delta) := by
    calc
      (X ^ (alpha / 2)) ^ p3 = X ^ ((alpha / 2) * p3) := by
        rw [← Real.rpow_mul hXpos.le (alpha / 2) p3]
      _ = X ^ (-delta) := by
        congr 1
        dsimp [p3, delta, D]
        field_simp [ne_of_gt (show (0 : ℝ) < (2 : ℝ) ^ j by positivity)]
        <;> ring
  have hspow : s ^ p3 ≤ X ^ (-delta) := by
    calc
      s ^ p3 ≤ (X ^ (alpha / 2)) ^ p3 :=
        Real.rpow_le_rpow_of_nonpos hMpos hsLower hp3
      _ = X ^ (-delta) := hMpow3
  have hlamN : lam * N ^ j = c * s := by
    dsimp [lam]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hNpos.ne')
  have hbasePower3 : (lam * N ^ j) ^ p3 ≤ c ^ p3 * X ^ (-delta) := by
    rw [hlamN, Real.mul_rpow hcpos.le hspos.le]
    exact mul_le_mul_of_nonneg_left hspow (Real.rpow_nonneg hcpos.le p3)
  have hterm3 : Y * (lam * Y ^ j) ^ p3 ≤ N * (c ^ p3 * X ^ (-delta)) := by
    calc
      Y * (lam * Y ^ j) ^ p3 ≤ N * (lam * N ^ j) ^ p3 :=
        periodicLogPhase_mul_rpow_power_scale hlampos hY hNpos hYN hpow3
      _ ≤ N * (c ^ p3 * X ^ (-delta)) :=
        mul_le_mul_of_nonneg_left hbasePower3 hNpos.le
  let M : ℝ := X ^ (alpha / 2)
  have hMj : M ^ j = X ^ ((j : ℝ) * (alpha / 2)) := by
    dsimp [M]
    rw [← Real.rpow_mul_natCast hXpos.le (alpha / 2) j]
    ring_nf
  have hNpowj : M ^ j ≤ N ^ j := pow_le_pow_left₀ hMpos.le hNpow j
  have hratio : s / N ^ j ≤ X ^ (-alpha) := by
    have hquot : s / N ^ j ≤ X ^ A / M ^ j := by
      apply (div_le_div_iff₀ (pow_pos hNpos j) (pow_pos hMpos j)).2
      calc
        s * M ^ j ≤ X ^ A * M ^ j :=
          mul_le_mul_of_nonneg_right hsX (pow_nonneg hMpos.le j)
        _ ≤ X ^ A * N ^ j :=
          mul_le_mul_of_nonneg_left hNpowj (Real.rpow_nonneg hXpos.le A)
    rw [hMj] at hquot
    have hexp : A - (j : ℝ) * (alpha / 2) ≤ -alpha := by
      nlinarith [hsum]
    calc
      s / N ^ j ≤ X ^ A / X ^ ((j : ℝ) * (alpha / 2)) := hquot
      _ = X ^ (A - (j : ℝ) * (alpha / 2)) := by
        rw [← Real.rpow_sub hXpos A ((j : ℝ) * (alpha / 2))]
      _ ≤ X ^ (-alpha) := Real.rpow_le_rpow_of_exponent_le hXone hexp
  have hratioNonneg : 0 ≤ s / N ^ j := div_nonneg hspos.le (pow_nonneg hNpos.le _)
  have hratioPow : (s / N ^ j) ^ p2 ≤ (X ^ (-alpha)) ^ p2 :=
    Real.rpow_le_rpow hratioNonneg hratio hp2.le
  have hratioExp : (X ^ (-alpha)) ^ p2 = X ^ ((-alpha) * p2) := by
    rw [← Real.rpow_mul hXpos.le (-alpha) p2]
  have hrecip : 1 / D ≤ 1 / (D - 2) := by
    apply (div_le_div_iff₀ hDpos (by linarith : 0 < D - 2)).2
    simpa using (show D - 2 ≤ D by linarith)
  have hcmp : alpha / D ≤ alpha / (D - 2) := by
    calc
      alpha / D = alpha * (1 / D) := by ring
      _ ≤ alpha * (1 / (D - 2)) :=
        mul_le_mul_of_nonneg_left hrecip halpha.le
      _ = alpha / (D - 2) := by ring
  have hexp2 : (-alpha) * p2 ≤ -delta := by
    dsimp [p2, delta]
    calc
      (-alpha) * (1 / (D - 2)) = -(alpha / (D - 2)) := by ring
      _ ≤ -(alpha / D) := neg_le_neg hcmp
  have hratioPowBound : (s / N ^ j) ^ p2 ≤ X ^ (-delta) := by
    calc
      (s / N ^ j) ^ p2 ≤ (X ^ (-alpha)) ^ p2 := hratioPow
      _ = X ^ ((-alpha) * p2) := hratioExp
      _ ≤ X ^ (-delta) := Real.rpow_le_rpow_of_exponent_le hXone hexp2
  have hfactor : D ^ 2 * lam = (D ^ 2 * c) * (s / N ^ j) := by
    dsimp [lam]
    ring
  have hfactorNonneg : 0 ≤ D ^ 2 * c := by positivity
  have hfactorPow :
      (D ^ 2 * lam) ^ p2 ≤ (D ^ 2 * c) ^ p2 * X ^ (-delta) := by
    rw [hfactor, Real.mul_rpow hfactorNonneg hratioNonneg]
    exact mul_le_mul_of_nonneg_left hratioPowBound
      (Real.rpow_nonneg hfactorNonneg p2)
  have hterm2 : Y * (D ^ 2 * lam) ^ p2 ≤
      N * ((D ^ 2 * c) ^ p2 * X ^ (-delta)) := by
    calc
      Y * (D ^ 2 * lam) ^ p2 ≤ N * (D ^ 2 * lam) ^ p2 :=
        mul_le_mul_of_nonneg_right hYN (Real.rpow_nonneg (by positivity) p2)
      _ ≤ N * ((D ^ 2 * c) ^ p2 * X ^ (-delta)) :=
        mul_le_mul_of_nonneg_left hfactorPow hNpos.le
  exact ⟨hterm1, hterm2, hterm3⟩

/-- Reindex one residue slice of an exact real-endpoint integer interval.
The scaled interval retains the original half-open endpoints exactly. -/
theorem sum_realIntegerInterval_filter_emod_eq_affine
    (X H : ℝ) (q : ℕ) (hq : 0 < q) (a : ℤ)
    (ha0 : 0 ≤ a) (haq : a < (q : ℤ)) (f : ℤ → ℂ) :
    (∑ n ∈ (FractionalPrimes.realIntegerInterval X H).filter
        (fun n : ℤ => n % (q : ℤ) = a), f n) =
      ∑ m ∈ FractionalPrimes.realIntegerInterval
        ((X - (a : ℝ)) / (q : ℝ)) (H / (q : ℝ)),
        f ((q : ℤ) * m + a) := by
  classical
  symm
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  apply Finset.sum_bij (fun m _ => (q : ℤ) * m + a)
  · intro m hm
    have hbounds := (FractionalPrimes.mem_realIntegerInterval_iff
      ((X - (a : ℝ)) / (q : ℝ)) (H / (q : ℝ)) m).mp hm
    have hlowerQ :
        X - (a : ℝ) < (q : ℝ) * (m : ℝ) := by
      have h := (div_lt_iff₀ hqR).mp hbounds.1
      nlinarith
    have hupperM : (m : ℝ) ≤ (X + H - (a : ℝ)) / (q : ℝ) := by
      have hsplit :
          (X - (a : ℝ)) / (q : ℝ) + H / (q : ℝ) =
            (X + H - (a : ℝ)) / (q : ℝ) := by
        rw [← add_div]
        congr 1
        ring
      rw [hsplit] at hbounds
      exact hbounds.2
    have hupperQ :
        (q : ℝ) * (m : ℝ) ≤ X + H - (a : ℝ) := by
      have h := (le_div_iff₀ hqR).mp hupperM
      nlinarith
    have hlower : X < ((q : ℤ) * m + a : ℤ) := by
      exact_mod_cast (by nlinarith : X < (q : ℝ) * (m : ℝ) + (a : ℝ))
    have hupper : (((q : ℤ) * m + a : ℤ) : ℝ) ≤ X + H := by
      exact_mod_cast (by nlinarith : (q : ℝ) * (m : ℝ) + (a : ℝ) ≤ X + H)
    apply Finset.mem_filter.mpr
    refine ⟨(FractionalPrimes.mem_realIntegerInterval_iff X H
      ((q : ℤ) * m + a)).mpr ⟨hlower, hupper⟩, ?_⟩
    rw [show (q : ℤ) * m + a = a + (q : ℤ) * m by ring,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt ha0 haq]
  · intro m₁ hm₁ m₂ hm₂ heq
    have hmul : (q : ℤ) * m₁ = (q : ℤ) * m₂ :=
      add_right_cancel heq
    exact mul_left_cancel₀ hqZ hmul
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hmod⟩
    have hbounds :=
      (FractionalPrimes.mem_realIntegerInterval_iff X H n).mp hnI
    have hdivision : (n % (q : ℤ)) + (q : ℤ) * (n / (q : ℤ)) = n :=
      Int.emod_add_mul_ediv n (q : ℤ)
    rw [hmod] at hdivision
    refine ⟨n / (q : ℤ), ?_, ?_⟩
    · apply (FractionalPrimes.mem_realIntegerInterval_iff
        ((X - (a : ℝ)) / (q : ℝ)) (H / (q : ℝ)) _).mpr
      have hcast : (n : ℝ) = (a : ℝ) +
          (q : ℝ) * ((n / (q : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast hdivision.symm
      constructor
      · apply (div_lt_iff₀ hqR).mpr
        nlinarith [hbounds.1, hcast]
      · have hdiv :
            ((n / (q : ℤ) : ℤ) : ℝ) ≤
              (X + H - (a : ℝ)) / (q : ℝ) := by
          apply (le_div_iff₀ hqR).mpr
          nlinarith [hbounds.2, hcast]
        have hsplit :
            (X - (a : ℝ)) / (q : ℝ) + H / (q : ℝ) =
              (X + H - (a : ℝ)) / (q : ℝ) := by
          rw [← add_div]
          congr 1
          ring
        rw [hsplit]
        exact hdiv
    · calc
        (q : ℤ) * (n / (q : ℤ)) + a =
            a + (q : ℤ) * (n / (q : ℤ)) := by ring
        _ = n := hdivision
  · intro m hm
    rfl

/-- Exact residue decomposition of a periodic phase sum on a real
half-open interval. The scaled intervals are the original residue slices,
not endpoint enlargements. -/
theorem periodicLogPhaseResiduePartition
    (X H : ℝ) (q : ℕ) (hq : 0 < q) (omega : ℤ → ℂ)
    (hperiod : ∀ n : ℤ, omega n = omega (n % (q : ℤ)))
    (phase : ℤ → ℂ) :
    (∑ n ∈ FractionalPrimes.realIntegerInterval X H,
        omega n * phase n) =
      ∑ a ∈ Finset.Ico (0 : ℤ) (q : ℤ),
        omega a *
          ∑ m ∈ FractionalPrimes.realIntegerInterval
            ((X - (a : ℝ)) / (q : ℝ)) (H / (q : ℝ)),
            phase ((q : ℤ) * m + a) := by
  classical
  let S := FractionalPrimes.realIntegerInterval X H
  let residue : ℤ → ℤ := fun n => n % (q : ℤ)
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  have hmaps : ∀ n ∈ S, residue n ∈ Finset.Ico (0 : ℤ) (q : ℤ) := by
    intro n hn
    have hnonneg : 0 ≤ n % (q : ℤ) := Int.emod_nonneg n hqZ.ne'
    have hlt : n % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos n hqZ
    exact Finset.mem_Ico.mpr ⟨hnonneg, hlt⟩
  calc
    (∑ n ∈ S, omega n * phase n) =
        ∑ a ∈ Finset.Ico (0 : ℤ) (q : ℤ),
          ∑ n ∈ S with residue n = a, omega n * phase n := by
            exact (Finset.sum_fiberwise_of_maps_to hmaps
              (fun n => omega n * phase n)).symm
    _ = ∑ a ∈ Finset.Ico (0 : ℤ) (q : ℤ),
          omega a *
            ∑ m ∈ FractionalPrimes.realIntegerInterval
              ((X - (a : ℝ)) / (q : ℝ)) (H / (q : ℝ)),
              phase ((q : ℤ) * m + a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' : 0 ≤ a ∧ a < (q : ℤ) := Finset.mem_Ico.mp ha
      calc
        (∑ n ∈ S with residue n = a, omega n * phase n) =
            ∑ n ∈ S.filter (fun n : ℤ => n % (q : ℤ) = a),
              omega n * phase n := by
                simp [Finset.sum_filter, residue]
        _ = ∑ n ∈ S.filter (fun n : ℤ => n % (q : ℤ) = a),
              omega a * phase n := by
                apply Finset.sum_congr rfl
                intro n hn
                have hna := (Finset.mem_filter.mp hn).2
                rw [hperiod n, hna]
        _ = omega a *
              ∑ n ∈ S.filter (fun n : ℤ => n % (q : ℤ) = a),
                phase n := by rw [Finset.mul_sum]
        _ = omega a *
              ∑ m ∈ FractionalPrimes.realIntegerInterval
                ((X - (a : ℝ)) / (q : ℝ)) (H / (q : ℝ)),
                phase ((q : ℤ) * m + a) := by
                  rw [sum_realIntegerInterval_filter_emod_eq_affine
                    X H q hq a ha'.1 ha'.2 phase]

/-- The derivative model for the phase `-s log(q x + b)/(2π)`. -/
noncomputable def periodicLogPhaseDerivative (s q b : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => -(s / (2 * Real.pi)) * Real.log (q * x + b)
  | k + 1 => fun x =>
      (-(s / (2 * Real.pi))) * (-1 : ℝ) ^ k * (Nat.factorial k : ℝ) *
        q ^ (k + 1) * ((q * x + b)⁻¹) ^ (k + 1)

theorem periodicLogPhaseDerivative_hasDerivAt
    {s q b x : ℝ} {k : ℕ}
    (hlin : 0 < q * x + b) :
    HasDerivAt (periodicLogPhaseDerivative s q b k)
      (periodicLogPhaseDerivative s q b (k + 1) x) x := by
  have hlinear : HasDerivAt (fun y : ℝ => q * y + b) q x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul q).add_const b
  by_cases hk : k = 0
  · subst k
    have hlog := hlinear.log (ne_of_gt hlin)
    convert hlog.const_mul (-(s / (2 * Real.pi))) using 1 <;>
      simp [periodicLogPhaseDerivative] <;> field_simp [ne_of_gt hlin] <;> ring
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    let c : ℝ := (-(s / (2 * Real.pi))) * (-1 : ℝ) ^ m *
      (Nat.factorial m : ℝ) * q ^ (m + 1)
    have hInv := hlinear.inv (ne_of_gt hlin)
    have hpow := hInv.pow (m + 1)
    have hc := hpow.const_mul c
    have hfun : (fun y : ℝ =>
        c * (((fun z : ℝ => q * z + b)⁻¹ ^ (m + 1)) y)) =
        periodicLogPhaseDerivative s q b (m + 1) := by
      funext y
      simp [c, periodicLogPhaseDerivative]
    have hderiv : c *
        ((m + 1 : ℝ) * ((q * x + b)⁻¹) ^ m *
          (-(q / (q * x + b) ^ 2))) =
        periodicLogPhaseDerivative s q b (m + 2) x := by
      let u : ℝ := q * x + b
      let v : ℝ := u⁻¹
      have hquot : -(q / (q * x + b) ^ 2) =
          -q * (q * x + b)⁻¹ ^ 2 := by
        simp [div_eq_mul_inv, inv_pow]
      have hfac : (Nat.factorial (m + 1) : ℝ) =
          (m + 1 : ℝ) * Nat.factorial m := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hcoeff : c * ((m + 1 : ℝ) * (-q)) =
          (-(s / (2 * Real.pi))) * (-1 : ℝ) ^ (m + 1) *
            (Nat.factorial (m + 1) : ℝ) * q ^ (m + 2) := by
        dsimp [c]
        rw [hfac, show m + 2 = (m + 1) + 1 by omega,
          pow_succ q (m + 1), pow_succ (-1 : ℝ) m]
        ring
      have hvpow : v ^ m * v ^ 2 = v ^ (m + 2) := by
        rw [← pow_add]
      change c * ((m + 1 : ℝ) * v ^ m *
          (-(q / u ^ 2))) =
        (-(s / (2 * Real.pi))) * (-1 : ℝ) ^ (m + 1) *
          (Nat.factorial (m + 1) : ℝ) * q ^ (m + 2) * v ^ (m + 2)
      rw [hquot]
      change c * ((m + 1 : ℝ) * v ^ m * (-q * v ^ 2)) =
        (-(s / (2 * Real.pi))) * (-1 : ℝ) ^ (m + 1) *
          (Nat.factorial (m + 1) : ℝ) * q ^ (m + 2) * v ^ (m + 2)
      calc
        c * ((m + 1 : ℝ) * v ^ m * (-q * v ^ 2)) =
            (c * ((m + 1 : ℝ) * (-q))) * (v ^ m * v ^ 2) := by ring
        _ = (-(s / (2 * Real.pi))) * (-1 : ℝ) ^ (m + 1) *
            (Nat.factorial (m + 1) : ℝ) * q ^ (m + 2) * v ^ (m + 2) := by
          rw [hcoeff, hvpow]
    have hderivRaw : c *
        (((m + 1 : ℕ) : ℝ) * ((fun y : ℝ => q * y + b)⁻¹ x) ^
          ((m + 1) - 1) * (-q / (q * x + b) ^ 2)) =
        periodicLogPhaseDerivative s q b (m + 2) x := by
      simpa only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, Pi.inv_apply, neg_div]
        using hderiv
    rw [hfun] at hc
    change HasDerivAt (periodicLogPhaseDerivative s q b (m + 1))
      (periodicLogPhaseDerivative s q b (m + 2) x) x
    rw [← hderivRaw]
    exact hc

/-- The explicit logarithmic phase derivatives provide the half-open
regularity data required by the constant-11 derivative test. -/
noncomputable def periodicLogPhaseHalfOpenData
    (s q b x Y : ℝ) (order : ℕ) (hY : 0 < Y)
    (hpositive : ∀ t ∈ Set.Ioc x (x + Y), 0 < q * t + b) :
    HalfOpenCkData x Y order where
  length_pos := hY
  derivative := periodicLogPhaseDerivative s q b
  continuous := by
    intro k hk t ht
    have harg : 0 < q * t + b := hpositive t ht
    have hlinear : ContinuousAt (fun y : ℝ => q * y + b) t := by fun_prop
    apply ContinuousAt.continuousWithinAt
    cases k with
    | zero =>
        dsimp [periodicLogPhaseDerivative]
        exact continuousAt_const.mul
          ((Real.continuousAt_log (ne_of_gt harg)).comp_of_eq hlinear rfl)
    | succ m =>
        change ContinuousAt
          (fun y : ℝ =>
            (-(s / (2 * Real.pi)) * (-1 : ℝ) ^ m *
              (Nat.factorial m : ℝ) * q ^ (m + 1)) *
                (q * y + b)⁻¹ ^ (m + 1)) t
        apply continuousAt_const.mul
        exact ((continuousAt_inv₀ (ne_of_gt harg)).comp_of_eq hlinear rfl).pow (m + 1)
  hasDerivAt := by
    intro k hk t ht
    exact periodicLogPhaseDerivative_hasDerivAt
      (hpositive t ⟨ht.1, le_of_lt ht.2⟩)
  right_hasDerivWithinAt := by
    intro k hk
    have ht : x + Y ∈ Set.Ioc x (x + Y) := ⟨by linarith, le_rfl⟩
    exact (periodicLogPhaseDerivative_hasDerivAt (hpositive (x + Y) ht)).hasDerivWithinAt

/-- The exact derivative scale on a residue interval whose linear argument
ranges through `(L,2L]`. -/
theorem periodicLogPhaseDerivative_magnitude_bounds
    {s q b x Y L N : ℝ} {k : ℕ}
    (hs : 0 < s) (hq : 0 < q) (hL : 0 < L)
    (hN : L = q * N)
    (hrange : ∀ u ∈ Set.Ioc x (x + Y),
      L < q * u + b ∧ q * u + b ≤ 2 * L)
    (u : ℝ) (hu : u ∈ Set.Ioc x (x + Y)) :
    s * (Nat.factorial k : ℝ) / (2 * Real.pi * (2 * N) ^ (k + 1)) ≤
        |periodicLogPhaseDerivative s q b (k + 1) u| ∧
      |periodicLogPhaseDerivative s q b (k + 1) u| ≤
        s * (Nat.factorial k : ℝ) / (2 * Real.pi * N ^ (k + 1)) := by
  have harg : 0 < q * u + b := lt_trans hL (hrange u hu).1
  have hNpos : 0 < N := by
    rw [hN] at hL
    nlinarith
  have hformulaPower :
      |periodicLogPhaseDerivative s q b (k + 1) u| =
        (s / (2 * Real.pi)) * (Nat.factorial k : ℝ) *
          q ^ (k + 1) * ((q * u + b)⁻¹) ^ (k + 1) := by
    have hsCoeff : |-(s / (2 * Real.pi))| = s / (2 * Real.pi) := by
      rw [abs_neg, abs_of_nonneg (div_nonneg hs.le (by positivity))]
    have hsign : |(-1 : ℝ) ^ k| = 1 := by simp
    have hfac : |(Nat.factorial k : ℝ)| = (Nat.factorial k : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    have hqpow : |q ^ (k + 1)| = q ^ (k + 1) :=
      abs_of_nonneg (pow_nonneg hq.le _)
    have hinvpow : |((q * u + b)⁻¹) ^ (k + 1)| =
        ((q * u + b)⁻¹) ^ (k + 1) :=
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr harg.le) _)
    calc
      |periodicLogPhaseDerivative s q b (k + 1) u| =
          |-(s / (2 * Real.pi))| * |(-1 : ℝ) ^ k| *
            |(Nat.factorial k : ℝ)| * |q ^ (k + 1)| *
              |((q * u + b)⁻¹) ^ (k + 1)| := by
                simp only [periodicLogPhaseDerivative, abs_mul]
      _ = (s / (2 * Real.pi)) * (Nat.factorial k : ℝ) *
            q ^ (k + 1) * ((q * u + b)⁻¹) ^ (k + 1) := by
          rw [hsCoeff, hsign, hfac, hqpow, hinvpow]
          ring
  have hformula :
      |periodicLogPhaseDerivative s q b (k + 1) u| =
        (s / (2 * Real.pi)) * (Nat.factorial k : ℝ) *
          (q / (q * u + b)) ^ (k + 1) := by
    have hratioPow : (q / (q * u + b)) ^ (k + 1) =
        q ^ (k + 1) * ((q * u + b)⁻¹) ^ (k + 1) := by
      calc
        (q / (q * u + b)) ^ (k + 1) =
            q ^ (k + 1) / (q * u + b) ^ (k + 1) := by rw [div_pow]
        _ = q ^ (k + 1) * ((q * u + b)⁻¹) ^ (k + 1) := by
            rw [div_eq_mul_inv, inv_pow]
    rw [hratioPow]
    simpa [mul_assoc] using hformulaPower
  have hlowRatio : 1 / (2 * N) ≤ q / (q * u + b) := by
    have hlowEq : q / (2 * L) = 1 / (2 * N) := by
      rw [hN]
      field_simp [ne_of_gt hq, ne_of_gt hNpos]
    rw [← hlowEq]
    apply (div_le_div_iff₀ (by positivity) harg).2
    nlinarith [mul_le_mul_of_nonneg_left (hrange u hu).2 hq.le]
  have huplow : q / (q * u + b) ≤ 1 / N := by
    have hupEq : q / L = 1 / N := by
      rw [hN]
      field_simp [ne_of_gt hq, ne_of_gt hNpos]
    calc
      q / (q * u + b) ≤ q / L := by
        apply (div_le_div_iff₀ harg hL).2
        nlinarith [mul_le_mul_of_nonneg_left (hrange u hu).1.le hq.le]
      _ = 1 / N := hupEq
  have hlowPow := pow_le_pow_left₀ (by positivity) hlowRatio (k + 1)
  have hupPow := pow_le_pow_left₀ (by positivity) huplow (k + 1)
  have hcoeff : 0 ≤ (s / (2 * Real.pi)) * (Nat.factorial k : ℝ) := by
    positivity
  constructor
  · rw [hformula]
    have hden : (2 * Real.pi * (2 * N) ^ (k + 1)) ≠ 0 := by positivity
    have hrewrite :
        s * (Nat.factorial k : ℝ) / (2 * Real.pi * (2 * N) ^ (k + 1)) =
          (s / (2 * Real.pi)) * (Nat.factorial k : ℝ) *
            (1 / (2 * N)) ^ (k + 1) := by
      rw [div_pow]
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
      <;> ring
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left hlowPow hcoeff
  · rw [hformula]
    have hrewrite :
        s * (Nat.factorial k : ℝ) / (2 * Real.pi * N ^ (k + 1)) =
          (s / (2 * Real.pi)) * (Nat.factorial k : ℝ) * (1 / N) ^ (k + 1) := by
      rw [div_pow]
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
      <;> ring
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left hupPow hcoeff

/-- Apply the checked constant-11 derivative test to the logarithmic phase
on a residue interval contained in one dyadic block. The derivative scales
are exactly those in the source proof, with `R = 2^j` and
`lambda = c_j s N^{-j}`. -/
theorem periodicLogPhaseHigherDerivativeTest
    {s q b x Y L N : ℝ} {j : ℕ}
    (hs : 0 < s) (hq : 0 < q) (hY : 0 < Y) (hL : 0 < L)
    (hN : L = q * N)
    (hpositive : ∀ u ∈ Set.Ioc x (x + Y), 0 < q * u + b)
    (hrange : ∀ u ∈ Set.Ioc x (x + Y),
      L < q * u + b ∧ q * u + b ≤ 2 * L)
    (hj : 3 ≤ j) (hfloor : (j : ℝ) < (Int.floor Y : ℝ)) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ / Y ≤
      11 * max (((2 : ℝ) ^ j / Y) ^ (2 / (2 : ℝ) ^ j))
        (max ((((2 : ℝ) ^ j) ^ 2 *
            (((Nat.factorial (j - 1) : ℝ) /
              (2 * Real.pi * (2 : ℝ) ^ j)) * s / N ^ j)) ^
              (1 / ((2 : ℝ) ^ j - 2)))
          (((((Nat.factorial (j - 1) : ℝ) /
              (2 * Real.pi * (2 : ℝ) ^ j)) * s / N ^ j) *
              Y ^ j) ^ (-2 / (2 : ℝ) ^ j))) := by
  have hNpos : 0 < N := by
    rw [hN] at hL
    nlinarith
  let cj : ℝ := (Nat.factorial (j - 1) : ℝ) /
    (2 * Real.pi * (2 : ℝ) ^ j)
  let lam : ℝ := cj * s / N ^ j
  let data := periodicLogPhaseHalfOpenData s q b x Y j hY hpositive
  have hLam : 0 < lam := by
    dsimp [lam, cj]
    positivity
  have hR : 1 ≤ (2 : ℝ) ^ j := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hlower : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ |data.derivative j t| := by
    intro t ht
    have hb := periodicLogPhaseDerivative_magnitude_bounds
      (k := j - 1) hs hq hL hN hrange t ht
    have hsub : j - 1 + 1 = j := by omega
    change lam ≤ |periodicLogPhaseDerivative s q b j t|
    dsimp [lam, cj]
    have hEq : s * (Nat.factorial (j - 1) : ℝ) /
        (2 * Real.pi * (2 * N) ^ j) =
        ((Nat.factorial (j - 1) : ℝ) /
          (2 * Real.pi * (2 : ℝ) ^ j)) * s / N ^ j := by
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
      <;> ring
    rw [← hEq]
    simpa [hsub] using hb.1
  have hupper : ∀ t ∈ Set.Ioc x (x + Y),
      |data.derivative j t| ≤ (2 : ℝ) ^ j * lam := by
    intro t ht
    have hb := periodicLogPhaseDerivative_magnitude_bounds
      (k := j - 1) hs hq hL hN hrange t ht
    have hsub : j - 1 + 1 = j := by omega
    change |periodicLogPhaseDerivative s q b j t| ≤ (2 : ℝ) ^ j * lam
    dsimp [lam, cj]
    have hEq : s * (Nat.factorial (j - 1) : ℝ) /
        (2 * Real.pi * N ^ j) =
        (2 : ℝ) ^ j *
          (((Nat.factorial (j - 1) : ℝ) /
            (2 * Real.pi * (2 : ℝ) ^ j)) * s / N ^ j) := by
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
      <;> ring
    rw [← hEq]
    simpa [hsub] using hb.2
  simpa [data, lam, cj, periodicLogPhaseHalfOpenData,
    periodicLogPhaseDerivative] using
      (FractionalPrimes.Literature.Derivative.derivativeTestEleven
        data hj hfloor hR hLam hlower hupper)

/-- The low-frequency branch supplied by the checked second-derivative
estimate, with the exact lower and upper scales on one residue block. -/
theorem periodicLogPhaseSecondDerivativeTest
    {s q b x Y L N : ℝ}
    (hs : 0 < s) (hq : 0 < q) (hY : 1 ≤ Y) (hL : 0 < L)
    (hN : L = q * N)
    (hpositive : ∀ u ∈ Set.Ioc x (x + Y), 0 < q * u + b)
    (hrange : ∀ u ∈ Set.Ioc x (x + Y),
      L < q * u + b ∧ q * u + b ≤ 2 * L) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤
      (14 / 5) / Real.sqrt (s / (8 * Real.pi * N ^ 2)) *
        (s / (2 * Real.pi * N ^ 2) * Y + 2) := by
  have hNpos : 0 < N := by
    rw [hN] at hL
    nlinarith
  let data := periodicLogPhaseHalfOpenData s q b x Y 2
    (by linarith) hpositive
  let c2 := data.toC2Data (by norm_num)
  let lam : ℝ := s / (8 * Real.pi * N ^ 2)
  let Lambda : ℝ := s / (2 * Real.pi * N ^ 2)
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  have hlower : ∀ t ∈ Set.Ioc x (x + Y), lam ≤ c2.secondDerivative t := by
    intro t ht
    have hmag := periodicLogPhaseDerivative_magnitude_bounds
      (k := 1) hs hq hL hN hrange t ht
    have hderiv : 0 ≤ periodicLogPhaseDerivative s q b 2 t := by
      rw [show periodicLogPhaseDerivative s q b 2 t =
          (s / (2 * Real.pi)) * q ^ 2 * ((q * t + b)⁻¹) ^ 2 by
        simp [periodicLogPhaseDerivative, Nat.factorial]
        <;> ring]
      positivity
    change lam ≤ periodicLogPhaseDerivative s q b 2 t
    dsimp [lam]
    have hEq : s * (Nat.factorial 1 : ℝ) /
        (2 * Real.pi * (2 * N) ^ 2) = s / (8 * Real.pi * N ^ 2) := by
      norm_num [Nat.factorial]
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
      <;> ring
    calc
      s / (8 * Real.pi * N ^ 2) ≤
          s * (Nat.factorial 1 : ℝ) /
            (2 * Real.pi * (2 * N) ^ 2) := by rw [hEq]
      _ ≤ |periodicLogPhaseDerivative s q b 2 t| := hmag.1
      _ = periodicLogPhaseDerivative s q b 2 t := abs_of_nonneg hderiv
  have hupper : ∀ t ∈ Set.Ioc x (x + Y),
      c2.secondDerivative t ≤ Lambda := by
    intro t ht
    have hmag := periodicLogPhaseDerivative_magnitude_bounds
      (k := 1) hs hq hL hN hrange t ht
    have hderiv : 0 ≤ periodicLogPhaseDerivative s q b 2 t := by
      rw [show periodicLogPhaseDerivative s q b 2 t =
          (s / (2 * Real.pi)) * q ^ 2 * ((q * t + b)⁻¹) ^ 2 by
        simp [periodicLogPhaseDerivative, Nat.factorial]
        <;> ring]
      positivity
    change periodicLogPhaseDerivative s q b 2 t ≤ Lambda
    dsimp [Lambda]
    have hEq : s * (Nat.factorial 1 : ℝ) /
        (2 * Real.pi * N ^ 2) = s / (2 * Real.pi * N ^ 2) := by
      norm_num [Nat.factorial]
    calc
      periodicLogPhaseDerivative s q b 2 t =
          |periodicLogPhaseDerivative s q b 2 t| :=
            (abs_of_nonneg hderiv).symm
      _ ≤ s * (Nat.factorial 1 : ℝ) /
          (2 * Real.pi * N ^ 2) := hmag.2
      _ = s / (2 * Real.pi * N ^ 2) := hEq
  have htest := c2.secondDerivative_bound_14_over_5 hY hlam hlower hupper
  simpa [data, c2, lam, Lambda, HalfOpenCkData.toC2Data,
    periodicLogPhaseHalfOpenData, periodicLogPhaseDerivative,
    FractionalPrimes.realExponentialPhase, FractionalPrimes.kusminPhase] using htest

/-- Coarse low-frequency form of the second-derivative estimate. This is
the source's 64 (sqrt(s) + N/sqrt(s)) bound for every subinterval of
length at most N. -/
theorem periodicLogPhaseSecondDerivativeTest_coarse
    {s q b x Y L N : ℝ}
    (hs : 0 < s) (hq : 0 < q) (hY : 1 ≤ Y) (hYle : Y ≤ N)
    (hL : 0 < L) (hN : L = q * N)
    (hpositive : ∀ u ∈ Set.Ioc x (x + Y), 0 < q * u + b)
    (hrange : ∀ u ∈ Set.Ioc x (x + Y),
      L < q * u + b ∧ q * u + b ≤ 2 * L) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤
      64 * (Real.sqrt s + N / Real.sqrt s) := by
  have hNpos : 0 < N := by
    rw [hN] at hL
    nlinarith
  have htest := periodicLogPhaseSecondDerivativeTest
    hs hq hY hL hN hpositive hrange
  have hsqrtPos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hrootDen :
      Real.sqrt (s / (8 * Real.pi * N ^ 2)) =
        Real.sqrt s / (Real.sqrt (8 * Real.pi) * N) := by
    rw [Real.sqrt_div (by positivity)]
    have hden :
        Real.sqrt (8 * Real.pi * N ^ 2) =
          Real.sqrt (8 * Real.pi) * N := by
      calc
        Real.sqrt (8 * Real.pi * N ^ 2) =
            Real.sqrt (8 * Real.pi) * Real.sqrt (N ^ 2) := by
              rw [Real.sqrt_mul (by positivity)]
        _ = Real.sqrt (8 * Real.pi) * N := by
              rw [Real.sqrt_sq_eq_abs, abs_of_pos hNpos]
    rw [hden]
  have hcoeff :
      (14 / 5 : ℝ) / Real.sqrt (s / (8 * Real.pi * N ^ 2)) =
        (14 / 5) * Real.sqrt (8 * Real.pi) * N / Real.sqrt s := by
    rw [hrootDen]
    field_simp [ne_of_gt hsqrtPos, ne_of_gt hNpos]
    <;> ring
  have hsqrtPi : Real.sqrt (8 * Real.pi) ≤ 6 := by
    have hpi : 8 * Real.pi ≤ 36 := by
      have := Real.pi_lt_four
      nlinarith [Real.pi_pos]
    calc
      Real.sqrt (8 * Real.pi) ≤ Real.sqrt 36 := Real.sqrt_le_sqrt hpi
      _ = 6 := by norm_num
  have hdenPi : 0 < 2 * Real.pi := by positivity
  have hratio : Real.sqrt (8 * Real.pi) / (2 * Real.pi) ≤ 1 := by
    apply (div_le_one hdenPi).2
    have hpi := Real.pi_gt_three
    nlinarith
  have hcoefA :
      (14 / 5 : ℝ) * Real.sqrt (8 * Real.pi) /
          (2 * Real.pi) ≤ 64 := by
    have h := mul_le_mul_of_nonneg_left hratio
      (by norm_num : (0 : ℝ) ≤ 14 / 5)
    calc
      (14 / 5 : ℝ) * Real.sqrt (8 * Real.pi) / (2 * Real.pi) ≤
          (14 / 5) * 1 := by
            rw [show (14 / 5 : ℝ) * Real.sqrt (8 * Real.pi) /
                (2 * Real.pi) =
                  (14 / 5) *
                    (Real.sqrt (8 * Real.pi) / (2 * Real.pi)) by ring]
            exact h
      _ ≤ 64 := by norm_num
  have hcoefB :
      (28 / 5 : ℝ) * Real.sqrt (8 * Real.pi) ≤ 64 := by
    have h := mul_le_mul_of_nonneg_left hsqrtPi
      (by norm_num : (0 : ℝ) ≤ 28 / 5)
    nlinarith
  have htermY :
      s / (2 * Real.pi * N ^ 2) * Y ≤ s / (2 * Real.pi * N) := by
    have hscale := mul_le_mul_of_nonneg_left hYle
      (div_nonneg hs.le (by positivity : 0 ≤ 2 * Real.pi * N ^ 2))
    have hEq : s / (2 * Real.pi * N ^ 2) * N =
        s / (2 * Real.pi * N) := by
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
      <;> ring
    rw [hEq] at hscale
    exact hscale
  have hterm1 :
      ((14 / 5 : ℝ) / Real.sqrt (s / (8 * Real.pi * N ^ 2))) *
          (s / (2 * Real.pi * N ^ 2) * Y) ≤ 64 * Real.sqrt s := by
    rw [hcoeff]
    calc
      ((14 / 5 : ℝ) * Real.sqrt (8 * Real.pi) * N / Real.sqrt s) *
          (s / (2 * Real.pi * N ^ 2) * Y) ≤
        ((14 / 5 : ℝ) * Real.sqrt (8 * Real.pi) * N / Real.sqrt s) *
          (s / (2 * Real.pi * N)) := by
            apply mul_le_mul_of_nonneg_left htermY
            positivity
      _ = ((14 / 5 : ℝ) * Real.sqrt (8 * Real.pi) /
            (2 * Real.pi)) * Real.sqrt s := by
            field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos, ne_of_gt hsqrtPos]
            nlinarith [Real.sq_sqrt hs.le]
      _ ≤ 64 * Real.sqrt s := by
            exact mul_le_mul_of_nonneg_right hcoefA (Real.sqrt_nonneg s)
  have hterm2 :
      ((14 / 5 : ℝ) / Real.sqrt (s / (8 * Real.pi * N ^ 2))) * 2 ≤
          64 * (N / Real.sqrt s) := by
    rw [hcoeff]
    calc
      ((14 / 5 : ℝ) * Real.sqrt (8 * Real.pi) * N / Real.sqrt s) * 2 =
          ((28 / 5 : ℝ) * Real.sqrt (8 * Real.pi)) *
            (N / Real.sqrt s) := by ring
      _ ≤ 64 * (N / Real.sqrt s) :=
        mul_le_mul_of_nonneg_right hcoefB (div_nonneg hNpos.le hsqrtPos.le)
  calc
    _ ≤ ((14 / 5 : ℝ) / Real.sqrt (s / (8 * Real.pi * N ^ 2))) *
          (s / (2 * Real.pi * N ^ 2) * Y + 2) := htest
    _ = ((14 / 5 : ℝ) / Real.sqrt (s / (8 * Real.pi * N ^ 2))) *
          (s / (2 * Real.pi * N ^ 2) * Y) +
        ((14 / 5 : ℝ) / Real.sqrt (s / (8 * Real.pi * N ^ 2))) * 2 := by ring
    _ ≤ 64 * Real.sqrt s + 64 * (N / Real.sqrt s) :=
      add_le_add hterm1 hterm2
    _ = 64 * (Real.sqrt s + N / Real.sqrt s) := by ring

/-- High-frequency cancellation on a long enough residue interval, with the
exact constant and saving in `ltw:plain-factor`. -/
theorem periodicLogPhaseHighLargeResidueBound
    {alpha A X N s q b x Y L : ℝ} {j : ℕ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hj : j = periodicLogPhaseOrder alpha A)
    (hNpow : X ^ (alpha / 2) ≤ N) (hsN : N < s) (hsX : s ≤ X ^ A)
    (hq : 0 < q) (hL : 0 < L) (hN : L = q * N)
    (hY : 0 < Y) (hYN : Y ≤ N)
    (hpositive : ∀ u ∈ Set.Ioc x (x + Y), 0 < q * u + b)
    (hrange : ∀ u ∈ Set.Ioc x (x + Y),
      L < q * u + b ∧ q * u + b ≤ 2 * L)
    (hfloor : (j : ℝ) < (Int.floor Y : ℝ)) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤
      periodicLogPhaseConstant alpha A * N *
        X ^ (-(periodicLogPhaseSaving alpha A)) := by
  have horder := periodicLogPhaseOrder_bounds halpha halpha1 hA
  have hjLo : 3 ≤ j := by
    have : 4 ≤ periodicLogPhaseOrder alpha A := horder.1
    omega
  have hXpos : 0 < X := by linarith
  have hNpos : 0 < N := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hNpow
  have hspos : 0 < s := lt_trans hNpos hsN
  let D : ℝ := (2 : ℝ) ^ j
  let c : ℝ := periodicLogPhaseCj j
  let lam : ℝ := c * s / N ^ j
  let p1 : ℝ := 2 / D
  let p2 : ℝ := 1 / (D - 2)
  let p3 : ℝ := -2 / D
  let delta : ℝ := alpha / D
  have hlam : 0 < lam := by
    dsimp [lam]
    apply div_pos
    · exact mul_pos (by dsimp [c, periodicLogPhaseCj]; positivity) hspos
    · exact pow_pos hNpos j
  have hR : 1 ≤ (2 : ℝ) ^ j :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have htest := periodicLogPhaseHigherDerivativeTest
    (s := s) (q := q) (b := b) (x := x) (Y := Y) (L := L) (N := N)
    (j := j) (by linarith) hq hY hL hN hpositive hrange hjLo hfloor
  have htest' :
      ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ / Y ≤
        11 * max ((D / Y) ^ p1)
          (max ((D ^ 2 * lam) ^ p2) ((lam * Y ^ j) ^ p3)) := by
    simpa [D, c, lam, p1, p2, p3, periodicLogPhaseCj] using htest
  have hterms := periodicLogPhaseHighScaleTermBounds
    (alpha := alpha) (A := A) (X := X) (N := N) (s := s) (Y := Y)
    (j := j) halpha halpha1 hA hX hj hNpow hsN hsX hY hYN
  have hterm1 : Y * ((D / Y) ^ p1) ≤
      N * (D ^ p1 * X ^ (-delta)) := by
    simpa [D, p1, delta] using hterms.1
  have hterm2 : Y * ((D ^ 2 * lam) ^ p2) ≤
      N * ((D ^ 2 * c) ^ p2 * X ^ (-delta)) := by
    simpa [D, c, lam, p2, delta] using hterms.2.1
  have hterm3 : Y * ((lam * Y ^ j) ^ p3) ≤
      N * (c ^ p3 * X ^ (-delta)) := by
    simpa [c, lam, p3, delta] using hterms.2.2
  have hCmax : 11 * max (D ^ p1) (max ((D ^ 2 * c) ^ p2) (c ^ p3)) ≤
      periodicLogPhaseConstant alpha A := by
    simpa [D, c, p1, p2, p3, hj, periodicLogPhaseCj] using
      periodicLogPhaseConstant_ge_highTerms alpha A
  have hpowX : 0 ≤ X ^ (-delta) := Real.rpow_nonneg (by positivity) _
  have hcoeffDistrib :
      max (D ^ p1) (max ((D ^ 2 * c) ^ p2) (c ^ p3)) * X ^ (-delta) =
        max (D ^ p1 * X ^ (-delta))
          (max ((D ^ 2 * c) ^ p2 * X ^ (-delta))
            (c ^ p3 * X ^ (-delta))) := by
    rw [max_mul_of_nonneg _ _ hpowX, max_mul_of_nonneg _ _ hpowX]
  have hsumMax :
      Y * max ((D / Y) ^ p1)
          (max ((D ^ 2 * lam) ^ p2) ((lam * Y ^ j) ^ p3)) ≤
        N * (max (D ^ p1) (max ((D ^ 2 * c) ^ p2) (c ^ p3)) *
          X ^ (-delta)) := by
    rw [mul_max_of_nonneg _ _ hY.le, mul_max_of_nonneg _ _ hY.le]
    rw [hcoeffDistrib]
    rw [mul_max_of_nonneg _ _ hNpos.le,
      mul_max_of_nonneg _ _ hNpos.le]
    exact max_le
      (le_trans hterm1 (le_max_left _ _))
      (max_le
        (le_trans hterm2 (le_trans (le_max_left _ _) (le_max_right _ _)))
        (le_trans hterm3 (le_trans (le_max_right _ _) (le_max_right _ _))))
  have htestNorm :
      ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤
        11 * (Y * max ((D / Y) ^ p1)
          (max ((D ^ 2 * lam) ^ p2) ((lam * Y ^ j) ^ p3))) := by
    have h := (div_le_iff₀ hY).mp htest'
    calc
      _ ≤ (11 * max ((D / Y) ^ p1)
          (max ((D ^ 2 * lam) ^ p2) ((lam * Y ^ j) ^ p3))) * Y := h
      _ = 11 * (Y * max ((D / Y) ^ p1)
          (max ((D ^ 2 * lam) ^ p2) ((lam * Y ^ j) ^ p3))) := by ring
  have hCscaled :
      11 * (max (D ^ p1) (max ((D ^ 2 * c) ^ p2) (c ^ p3))) *
          X ^ (-delta) ≤ periodicLogPhaseConstant alpha A * X ^ (-delta) :=
    mul_le_mul_of_nonneg_right hCmax hpowX
  have hnorm := htestNorm.trans (by
    calc
      11 * (Y * max ((D / Y) ^ p1)
          (max ((D ^ 2 * lam) ^ p2) ((lam * Y ^ j) ^ p3))) ≤
        11 * (N * (max (D ^ p1)
          (max ((D ^ 2 * c) ^ p2) (c ^ p3)) * X ^ (-delta))) :=
          mul_le_mul_of_nonneg_left hsumMax (by norm_num)
      _ = N * (11 * max (D ^ p1)
          (max ((D ^ 2 * c) ^ p2) (c ^ p3)) * X ^ (-delta)) := by ring
      _ ≤ N * (periodicLogPhaseConstant alpha A * X ^ (-delta)) :=
          mul_le_mul_of_nonneg_left hCscaled hNpos.le
      _ = periodicLogPhaseConstant alpha A * N * X ^ (-delta) := by ring)
  simpa [hj, delta, D, periodicLogPhaseSaving, periodicLogPhaseOrder] using hnorm

private theorem periodicLogPhaseN_saving_lower
    {alpha A X N : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hA : 1 ≤ A) (hX : 3 ≤ X)
    (hNpow : X ^ (alpha / 2) ≤ N) :
    1 ≤ N * X ^ (-(periodicLogPhaseSaving alpha A)) := by
  let j := periodicLogPhaseOrder alpha A
  let D : ℝ := (2 : ℝ) ^ j
  let delta : ℝ := alpha / D
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hj4 : 4 ≤ j := by
    dsimp [j]
    exact (periodicLogPhaseOrder_bounds halpha halpha1 hA).1
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hD16 : 16 ≤ D := by
    dsimp [D]
    have hpow : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj4
    norm_num at hpow ⊢
    exact hpow
  have hdeltaLe : delta ≤ alpha / 4 := by
    dsimp [delta]
    apply (div_le_div_iff₀ hDpos (by norm_num : (0 : ℝ) < 4)).2
    nlinarith [halpha, hD16]
  have hexp : 0 ≤ alpha / 2 - delta := by
    linarith [hdeltaLe]
  have hprod : X ^ (alpha / 2) * X ^ (-delta) =
      X ^ (alpha / 2 - delta) := by
    rw [Real.rpow_neg hXpos.le delta, ← div_eq_mul_inv,
      ← Real.rpow_sub hXpos (alpha / 2) delta]
  have hprodOne : 1 ≤ X ^ (alpha / 2) * X ^ (-delta) := by
    rw [hprod]
    have h := Real.rpow_le_rpow_of_exponent_le hXone hexp
    simpa using h
  have hNfactor : 1 ≤ N * X ^ (-delta) :=
    le_trans hprodOne
      (mul_le_mul_of_nonneg_right hNpow (Real.rpow_nonneg hXpos.le _))
  simpa [delta, D, j, periodicLogPhaseSaving, periodicLogPhaseOrder] using
    hNfactor

/-- High-frequency cancellation on every subinterval of a residue block,
including the short intervals where the derivative test is not applicable. -/
theorem periodicLogPhaseHighFrequencyResidueBound
    {alpha A X N s q b x Y L : ℝ} {j : ℕ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hj : j = periodicLogPhaseOrder alpha A)
    (hNpow : X ^ (alpha / 2) ≤ N) (hsN : N < s) (hsX : s ≤ X ^ A)
    (hq : 0 < q) (hL : 0 < L) (hN : L = q * N)
    (hY : 0 < Y) (hYN : Y ≤ N)
    (hpositive : ∀ u ∈ Set.Ioc x (x + Y), 0 < q * u + b)
    (hrange : ∀ u ∈ Set.Ioc x (x + Y),
      L < q * u + b ∧ q * u + b ≤ 2 * L) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤
      periodicLogPhaseConstant alpha A * N *
        X ^ (-(periodicLogPhaseSaving alpha A)) := by
  by_cases hfloor : (j : ℝ) < (Int.floor Y : ℝ)
  · exact periodicLogPhaseHighLargeResidueBound
      halpha halpha1 hA hX hj hNpow hsN hsX hq hL hN hY hYN
      hpositive hrange hfloor
  · have hfloorLe : (Int.floor Y : ℝ) ≤ j := le_of_not_gt hfloor
    have hYlt : Y < (j : ℝ) + 1 := by
      have hfloorStep : Y < (Int.floor Y : ℝ) + 1 := Int.lt_floor_add_one Y
      exact lt_of_lt_of_le hfloorStep (by linarith)
    have hCsmall : (j : ℝ) + 2 ≤ periodicLogPhaseConstant alpha A := by
      simpa [hj] using periodicLogPhaseConstant_ge_order alpha A
    have hNfactor := periodicLogPhaseN_saving_lower
      halpha halpha1 hA hX hNpow
    have hCnonneg : 0 ≤ periodicLogPhaseConstant alpha A :=
      le_trans (by positivity) hCsmall
    have htrivial :
        ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
          FractionalPrimes.realExponentialPhase
            (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤ Y + 1 :=
      FractionalPrimes.realIntegerInterval_phase_sum_norm_le_length_add_one
        (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) x Y hY.le
    calc
      _ ≤ Y + 1 := htrivial
      _ ≤ (j : ℝ) + 2 := by linarith [hYlt]
      _ ≤ periodicLogPhaseConstant alpha A * N *
          X ^ (-(periodicLogPhaseSaving alpha A)) := by
        calc
          (j : ℝ) + 2 ≤ periodicLogPhaseConstant alpha A := hCsmall
          _ ≤ periodicLogPhaseConstant alpha A *
              (N * X ^ (-(periodicLogPhaseSaving alpha A))) :=
            by simpa using mul_le_mul_of_nonneg_left hNfactor hCnonneg
          _ = periodicLogPhaseConstant alpha A * N *
              X ^ (-(periodicLogPhaseSaving alpha A)) := by ring

/-- Low-frequency cancellation on one residue interval, including its
short-interval case, with the exact source saving and T0 term. -/
theorem periodicLogPhaseLowFrequencyResidueBound
    {alpha A X N T0 s q b x Y L : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hNpow : X ^ (alpha / 2) ≤ N)
    (hT0 : 1 ≤ T0) (hT0s : T0 ≤ s) (hsN : s ≤ N)
    (hq : 0 < q) (hL : 0 < L) (hN : L = q * N)
    (hY : 0 < Y) (hYN : Y ≤ N)
    (hpositive : ∀ u ∈ Set.Ioc x (x + Y), 0 < q * u + b)
    (hrange : ∀ u ∈ Set.Ioc x (x + Y),
      L < q * u + b ∧ q * u + b ≤ 2 * L) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤
      64 * N * (X ^ (-(periodicLogPhaseSaving alpha A)) +
        T0 ^ (-1 / 2 : ℝ)) := by
  let j := periodicLogPhaseOrder alpha A
  let D : ℝ := (2 : ℝ) ^ j
  let delta : ℝ := alpha / D
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hNpos : 0 < N := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hNpow
  have hspos : 0 < s := lt_of_lt_of_le (by linarith : 0 < T0) hT0s
  have hT0pos : 0 < T0 := by linarith
  have hj4 : 4 ≤ j := by
    dsimp [j]
    exact (periodicLogPhaseOrder_bounds halpha halpha1 hA).1
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hD16 : 16 ≤ D := by
    dsimp [D]
    have hpow : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj4
    norm_num at hpow ⊢
    exact hpow
  have hdeltaLe : delta ≤ alpha / 4 := by
    dsimp [delta]
    apply (div_le_div_iff₀ hDpos (by norm_num : (0 : ℝ) < 4)).2
    nlinarith [halpha, hD16]
  have hnegExp : -(alpha / 4) ≤ -delta := by linarith [hdeltaLe]
  have hpowXquarter : X ^ (-(alpha / 4)) ≤ X ^ (-delta) :=
    Real.rpow_le_rpow_of_exponent_le hXone hnegExp
  have hrootEq : Real.sqrt (X ^ (alpha / 2)) = X ^ (alpha / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le (alpha / 2) (1 / 2 : ℝ)]
    congr 1
    ring
  have hrootQuarter : X ^ (alpha / 4) ≤ Real.sqrt N := by
    calc
      X ^ (alpha / 4) = Real.sqrt (X ^ (alpha / 2)) := hrootEq.symm
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt hNpow
  have hrootQuarterPos : 0 < X ^ (alpha / 4) :=
    Real.rpow_pos_of_pos hXpos _
  have hsqrtNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsqrtNbound : Real.sqrt N ≤ N * X ^ (-(alpha / 4)) := by
    have hquot : Real.sqrt N ≤ N / X ^ (alpha / 4) :=
      (le_div_iff₀ hrootQuarterPos).2 (by
        calc
          Real.sqrt N * X ^ (alpha / 4) ≤ Real.sqrt N * Real.sqrt N :=
            mul_le_mul_of_nonneg_left hrootQuarter (Real.sqrt_nonneg N)
          _ = N := by nlinarith [Real.sq_sqrt hNpos.le])
    calc
      Real.sqrt N ≤ N / X ^ (alpha / 4) := hquot
      _ = N * X ^ (-(alpha / 4)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hXpos.le (alpha / 4)]
  have hsqrtS : Real.sqrt s ≤ Real.sqrt N := Real.sqrt_le_sqrt hsN
  have hterm1 : Real.sqrt s ≤ N * X ^ (-delta) :=
    hsqrtS.trans (hsqrtNbound.trans
      (mul_le_mul_of_nonneg_left hpowXquarter hNpos.le))
  have hrootT0 : Real.sqrt T0 ≤ Real.sqrt s := Real.sqrt_le_sqrt hT0s
  have hterm2 : N / Real.sqrt s ≤ N / Real.sqrt T0 := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.2 hspos)
      (Real.sqrt_pos.2 hT0pos)).2
    exact mul_le_mul_of_nonneg_left hrootT0 hNpos.le
  have hT0inv : N / Real.sqrt T0 = N * T0 ^ (-1 / 2 : ℝ) := by
    rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hT0pos.le (1 / 2 : ℝ)]
    rw [show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by norm_num]
  have hNfactor := periodicLogPhaseN_saving_lower
    halpha halpha1 hA hX hNpow
  by_cases hYlong : 1 ≤ Y
  · have htest := periodicLogPhaseSecondDerivativeTest_coarse
      (s := s) (q := q) (b := b) (x := x) (Y := Y) (L := L) (N := N)
      hspos hq hYlong hYN hL hN hpositive hrange
    have hsum : Real.sqrt s + N / Real.sqrt s ≤
        N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ)) := by
      calc
        Real.sqrt s + N / Real.sqrt s ≤
            N * X ^ (-delta) + N / Real.sqrt T0 :=
          add_le_add hterm1 hterm2
        _ = N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ)) := by
          rw [hT0inv]
          ring
    calc
      _ ≤ 64 * (Real.sqrt s + N / Real.sqrt s) := htest
      _ ≤ 64 * (N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 64 * N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ)) := by ring
  · have hYlt : Y < 1 := lt_of_not_ge hYlong
    have htrivial :
        ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
          FractionalPrimes.realExponentialPhase
            (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤ Y + 1 :=
      FractionalPrimes.realIntegerInterval_phase_sum_norm_le_length_add_one
        (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) x Y hY.le
    have hsumLower : 1 ≤ N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ)) := by
      have hT0term : 0 ≤ T0 ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hT0pos.le _
      calc
        1 ≤ N * X ^ (-delta) := by
          simpa [delta, D, j, periodicLogPhaseSaving, periodicLogPhaseOrder]
            using hNfactor
        _ ≤ N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hT0term) hNpos.le
    calc
      _ ≤ Y + 1 := htrivial
      _ ≤ 2 := by linarith
      _ ≤ 64 * (N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ))) := by
        calc
          2 ≤ 64 := by norm_num
          _ ≤ 64 * (N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ))) := by
            calc
              64 = 64 * 1 := by ring
              _ ≤ 64 * (N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ))) :=
                mul_le_mul_of_nonneg_left hsumLower (by norm_num : 0 ≤ (64 : ℝ))
      _ = 64 * N * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ)) := by ring

/-- One residue slice has the uniform source bound in both frequency
regimes. The larger constant in the high-frequency case comes directly from
the stated source constant; the low-frequency case uses its `64` floor. -/
theorem periodicLogPhaseResidueBound
    {alpha A X N T0 s q b x Y L : ℝ} {j : ℕ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hj : j = periodicLogPhaseOrder alpha A)
    (hNpow : X ^ (alpha / 2) ≤ N)
    (hT0 : 1 ≤ T0) (hT0s : T0 ≤ s) (hsX : s ≤ X ^ A)
    (hq : 0 < q) (hL : 0 < L) (hN : L = q * N)
    (hY : 0 < Y) (hYN : Y ≤ N)
    (hpositive : ∀ u ∈ Set.Ioc x (x + Y), 0 < q * u + b)
    (hrange : ∀ u ∈ Set.Ioc x (x + Y),
      L < q * u + b ∧ q * u + b ≤ 2 * L) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤
      periodicLogPhaseConstant alpha A * N *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  have hXpos : 0 < X := by linarith
  have hNpos : 0 < N :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hNpow
  have hT0pos : 0 < T0 := by linarith
  have hT0term : 0 ≤ T0 ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hT0pos.le _
  have hsumNonneg : 0 ≤
      X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ) :=
    add_nonneg (Real.rpow_nonneg hXpos.le _) hT0term
  have hCpos : 0 ≤ periodicLogPhaseConstant alpha A :=
    le_trans (by positivity) (periodicLogPhaseConstant_ge_order alpha A)
  have hC64 : 64 ≤ periodicLogPhaseConstant alpha A := by
    unfold periodicLogPhaseConstant
    exact le_max_left _ _
  by_cases hsN : s ≤ N
  · have hlow := periodicLogPhaseLowFrequencyResidueBound
      halpha halpha1 hA hX hNpow hT0 hT0s hsN hq hL hN hY hYN
      hpositive hrange
    calc
      _ ≤ 64 * N *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := hlow
      _ ≤ periodicLogPhaseConstant alpha A * N *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
        calc
          64 * N * (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) =
              (64 * N) *
                (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by ring
          _ ≤ (periodicLogPhaseConstant alpha A * N) *
                (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hC64 hNpos.le) hsumNonneg
          _ = periodicLogPhaseConstant alpha A * N *
                (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by ring
  · have hsN' : N < s := lt_of_not_ge hsN
    have hhigh := periodicLogPhaseHighFrequencyResidueBound
      halpha halpha1 hA hX hj hNpow hsN' hsX hq hL hN hY hYN
      hpositive hrange
    have hcoef : 0 ≤ periodicLogPhaseConstant alpha A * N :=
      mul_nonneg hCpos hNpos.le
    calc
      _ ≤ periodicLogPhaseConstant alpha A * N *
          X ^ (-(periodicLogPhaseSaving alpha A)) := hhigh
      _ ≤ periodicLogPhaseConstant alpha A * N *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right hT0term) hcoef

/-- The residue estimate is invariant under reversing the phase direction.
The absolute frequency is used in the derivative hypotheses, and the
negative-frequency sum is the conjugate of the positive-frequency sum. -/
theorem periodicLogPhaseResidueBound_signed
    {alpha A X N T0 t q b x Y L : ℝ} {j : ℕ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hj : j = periodicLogPhaseOrder alpha A)
    (hNpow : X ^ (alpha / 2) ≤ N)
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hq : 0 < q) (hL : 0 < L) (hN : L = q * N)
    (hY : 0 < Y) (hYN : Y ≤ N)
    (hpositive : ∀ u ∈ Set.Ioc x (x + Y), 0 < q * u + b)
    (hrange : ∀ u ∈ Set.Ioc x (x + Y),
      L < q * u + b ∧ q * u + b ≤ 2 * L) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
        FractionalPrimes.realExponentialPhase
          (fun u => -(t / (2 * Real.pi)) * Real.log (q * u + b)) n‖ ≤
      periodicLogPhaseConstant alpha A * N *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  have hpos := periodicLogPhaseResidueBound
    (alpha := alpha) (A := A) (X := X) (N := N) (T0 := T0)
    (s := |t|) (q := q) (b := b) (x := x) (Y := Y) (L := L) (j := j)
    halpha halpha1 hA hX hj hNpow hT0 hT0t htX hq hL hN hY hYN
    hpositive hrange
  by_cases ht : 0 ≤ t
  · have habs : |t| = t := abs_of_nonneg ht
    rw [habs] at hpos
    exact hpos
  · have htneg : t < 0 := lt_of_not_ge ht
    have habs : |t| = -t := abs_of_neg htneg
    have hphase (n : ℤ) :
        FractionalPrimes.realExponentialPhase
            (fun u => -(t / (2 * Real.pi)) * Real.log (q * u + b)) n =
          star (FractionalPrimes.realExponentialPhase
            (fun u => -(|t| / (2 * Real.pi)) * Real.log (q * u + b)) n) := by
      unfold FractionalPrimes.realExponentialPhase
      rw [Complex.star_def]
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_neg, map_div, Complex.conj_ofReal, Complex.conj_I]
      rw [habs]
      push_cast
      ring
    have hsum :
        (∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
          FractionalPrimes.realExponentialPhase
            (fun u => -(t / (2 * Real.pi)) * Real.log (q * u + b)) n) =
        star (∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
          FractionalPrimes.realExponentialPhase
            (fun u => -(|t| / (2 * Real.pi)) * Real.log (q * u + b)) n) := by
      calc
        _ = ∑ n ∈ FractionalPrimes.realIntegerInterval x Y,
            star (FractionalPrimes.realExponentialPhase
              (fun u => -(|t| / (2 * Real.pi)) * Real.log (q * u + b)) n) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact hphase n
        _ = _ := by
          simpa only [Complex.star_def] using
            (map_sum (starRingEnd ℂ)
              (fun n => FractionalPrimes.realExponentialPhase
                (fun u => -(|t| / (2 * Real.pi)) * Real.log (q * u + b)) n)
              (FractionalPrimes.realIntegerInterval x Y)).symm
    rw [hsum, norm_star]
    exact hpos

/-- Summing the residue bounds gives cancellation for every subinterval of
`(L,2L]`, uniformly in a bounded periodic weight. The interval endpoints
remain the exact half-open endpoints under residue reindexing. -/
theorem periodicLogPhaseBoundedWeightPhaseInterval
    {alpha A X L T0 s x H : ℝ} {q : ℕ} {omega : ℤ → ℂ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0s : T0 ≤ |s|) (hsX : |s| ≤ X ^ A)
    (hperiod : ∀ n : ℤ, omega n = omega (n % (q : ℤ)))
    (hweight : ∀ n : ℤ, ‖omega n‖ ≤ 1)
    (hxL : L ≤ x) (hupper : x + H ≤ 2 * L) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x H,
        omega n * FractionalPrimes.realExponentialPhase
          (fun u => -(s / (2 * Real.pi)) * Real.log u) n‖ ≤
      periodicLogPhaseConstant alpha A * L *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := lt_of_lt_of_le
    (Real.rpow_pos_of_pos hXpos _) hLlower
  have hqRpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hT0pos : 0 < T0 := by linarith
  by_cases hlen : 0 < H
  · let qR : ℝ := (q : ℝ)
    let N : ℝ := L / qR
    let base : ℝ := X ^ (-(periodicLogPhaseSaving alpha A)) +
      T0 ^ (-1 / 2 : ℝ)
    have hHleL : H ≤ L := by linarith
    have hqR : qR = (q : ℝ) := rfl
    have hNpos : 0 < N := by
      dsimp [N, qR]
      exact div_pos hLpos hqRpos
    have hNval : L = qR * N := by
      dsimp [N]
      calc
        L = (L / qR) * qR := (div_mul_cancel₀ L hqRpos.ne').symm
        _ = qR * (L / qR) := by ring
    have hpowerSquare : X ^ (alpha / 2) * X ^ (alpha / 2) = X ^ alpha := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring
    have hNpow : X ^ (alpha / 2) ≤ N := by
      apply (le_div_iff₀ hqRpos).2
      calc
        X ^ (alpha / 2) * qR ≤ X ^ (alpha / 2) * X ^ (alpha / 2) :=
          mul_le_mul_of_nonneg_left hqBound (Real.rpow_nonneg hXpos.le _)
        _ = X ^ alpha := hpowerSquare
        _ ≤ L := hLlower
    have hcardInt :
        ((Finset.Ico (0 : ℤ) (q : ℤ)).card : ℤ) = (q : ℤ) := by
      rw [Int.card_Ico_of_le 0 (q : ℤ) (by exact_mod_cast (Nat.zero_le q))]
      simp
    have hcardReal :
        ((Finset.Ico (0 : ℤ) (q : ℤ)).card : ℝ) = qR := by
      rw [hqR]
      exact_mod_cast hcardInt
    let phase : ℤ → ℂ := fun n =>
      FractionalPrimes.realExponentialPhase
        (fun u => -(s / (2 * Real.pi)) * Real.log u) n
    have hpartition := periodicLogPhaseResiduePartition
      x H q hq omega hperiod phase
    rw [hpartition]
    have hsliceBound : ∀ a ∈ Finset.Ico (0 : ℤ) (q : ℤ),
        ‖omega a *
          ∑ m ∈ FractionalPrimes.realIntegerInterval
              ((x - (a : ℝ)) / qR) (H / qR),
            phase ((q : ℤ) * m + a)‖ ≤
          periodicLogPhaseConstant alpha A * N * base := by
      intro a ha
      have ha' : 0 ≤ a ∧ a < (q : ℤ) := Finset.mem_Ico.mp ha
      let xa : ℝ := (x - (a : ℝ)) / qR
      let Ya : ℝ := H / qR
      have hYapos : 0 < Ya := by
        dsimp [Ya]
        exact div_pos hlen hqRpos
      have hYale : Ya ≤ N := by
        dsimp [Ya, N]
        apply (div_le_div_iff₀ hqRpos hqRpos).2
        nlinarith [hHleL, hqRpos]
      have hYaleN : Ya ≤ N := hYale
      have hmap : ∀ u ∈ Set.Ioc xa (xa + Ya),
          L < qR * u + (a : ℝ) ∧ qR * u + (a : ℝ) ≤ 2 * L := by
        intro u hu
        rcases hu with ⟨hulo, huhi⟩
        have hulo' : (x - (a : ℝ)) / qR < u := by
          simpa [xa] using hulo
        have huhi' : u ≤ (x - (a : ℝ)) / qR + H / qR := by
          simpa [xa, Ya] using huhi
        have hleft : x < qR * u + (a : ℝ) := by
          have h := (div_lt_iff₀ hqRpos).mp hulo'
          nlinarith
        have hsplit :
            (x - (a : ℝ)) / qR + H / qR = (x + H - (a : ℝ)) / qR := by
          rw [← add_div]
          congr 1
          ring
        rw [hsplit] at huhi'
        have hright : qR * u + (a : ℝ) ≤ x + H := by
          have h := (le_div_iff₀ hqRpos).mp huhi'
          nlinarith
        constructor
        · exact lt_of_le_of_lt hxL hleft
        · exact le_trans hright hupper
      have hpos : ∀ u ∈ Set.Ioc xa (xa + Ya), 0 < qR * u + (a : ℝ) := by
        intro u hu
        exact lt_trans hLpos (hmap u hu).1
      have hres := periodicLogPhaseResidueBound_signed
        (alpha := alpha) (A := A) (X := X) (N := N)
        (T0 := T0) (t := s) (q := qR) (b := (a : ℝ))
        (x := xa) (Y := Ya) (L := L)
        (j := periodicLogPhaseOrder alpha A)
        halpha halpha1 hA hX rfl hNpow hT0 hT0s hsX
        hqRpos hLpos hNval hYapos hYaleN hpos hmap
      have hphaseSum :
          ‖∑ m ∈ FractionalPrimes.realIntegerInterval xa Ya,
              phase ((q : ℤ) * m + a)‖ ≤
            periodicLogPhaseConstant alpha A * N * base := by
        have heq :
            (∑ m ∈ FractionalPrimes.realIntegerInterval xa Ya,
              phase ((q : ℤ) * m + a)) =
            ∑ m ∈ FractionalPrimes.realIntegerInterval xa Ya,
              FractionalPrimes.realExponentialPhase
                (fun u => -(s / (2 * Real.pi)) * Real.log
                  (qR * u + (a : ℝ))) m := by
          apply Finset.sum_congr rfl
          intro m hm
          simp [phase, FractionalPrimes.realExponentialPhase, qR]
        rw [heq]
        simpa [base] using hres
      calc
        ‖omega a *
            ∑ m ∈ FractionalPrimes.realIntegerInterval xa Ya,
              phase ((q : ℤ) * m + a)‖ =
            ‖omega a‖ *
              ‖∑ m ∈ FractionalPrimes.realIntegerInterval xa Ya,
                phase ((q : ℤ) * m + a)‖ := norm_mul _ _
        _ ≤ 1 * (periodicLogPhaseConstant alpha A * N * base) :=
          mul_le_mul (hweight a) hphaseSum (norm_nonneg _) (by norm_num)
        _ = periodicLogPhaseConstant alpha A * N * base := by ring
    have hsumBound :
        ‖∑ a ∈ Finset.Ico (0 : ℤ) (q : ℤ),
          omega a *
            ∑ m ∈ FractionalPrimes.realIntegerInterval
                ((x - (a : ℝ)) / qR) (H / qR),
              phase ((q : ℤ) * m + a)‖ ≤
          periodicLogPhaseConstant alpha A * L * base := by
      calc
        _ ≤ ∑ a ∈ Finset.Ico (0 : ℤ) (q : ℤ),
            ‖omega a *
              ∑ m ∈ FractionalPrimes.realIntegerInterval
                  ((x - (a : ℝ)) / qR) (H / qR),
                phase ((q : ℤ) * m + a)‖ := norm_sum_le _ _
        _ ≤ ∑ _a ∈ Finset.Ico (0 : ℤ) (q : ℤ),
            periodicLogPhaseConstant alpha A * N * base := by
          apply Finset.sum_le_sum
          intro a ha
          exact hsliceBound a ha
        _ = ((Finset.Ico (0 : ℤ) (q : ℤ)).card : ℝ) *
            (periodicLogPhaseConstant alpha A * N * base) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = qR * (periodicLogPhaseConstant alpha A * N * base) := by
          rw [hcardReal]
        _ = periodicLogPhaseConstant alpha A * L * base := by
          rw [hNval]
          ring
    simpa [phase, base] using hsumBound
  · have hEmpty : FractionalPrimes.realIntegerInterval x H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hmem := (FractionalPrimes.mem_realIntegerInterval_iff x H n).mp hn
      linarith
    have hHnonpos : H ≤ 0 := le_of_not_gt hlen
    have hC64 : 64 ≤ periodicLogPhaseConstant alpha A := by
      unfold periodicLogPhaseConstant
      exact le_max_left _ _
    have hCnonneg : 0 ≤ periodicLogPhaseConstant alpha A := by linarith
    have hT0pos : 0 < T0 := by linarith
    have hRHS : 0 ≤ periodicLogPhaseConstant alpha A * L *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg hCnonneg hLpos.le)
        (add_nonneg (Real.rpow_nonneg hXpos.le _)
          (Real.rpow_nonneg hT0pos.le _))
    rw [hEmpty]
    simpa using hRHS

/-- Abel's finite summation identity in the initial-prefix form used below. -/
private theorem periodicLogPhase_sum_range_mul_abel_identity
    (N : ℕ) (u v : ℕ → ℂ) (hN : 0 < N) :
    (∑ j ∈ Finset.range N, u j * v j) =
      (∑ j ∈ Finset.range N, u j) * v (N - 1) +
        ∑ j ∈ Finset.range (N - 1),
          (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1)) := by
  induction N with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ k =>
      have hIH0 := ih (by omega)
      have hIH :
          (∑ j ∈ Finset.range (Nat.succ k), u j * v j) =
            (∑ j ∈ Finset.range (Nat.succ k), u j) * v k +
              ∑ j ∈ Finset.range k,
                (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1)) := by
        simpa using hIH0
      have hNsub : Nat.succ (Nat.succ k) - 1 = Nat.succ k := by omega
      have hsumU :
          (∑ j ∈ Finset.range (Nat.succ (Nat.succ k)), u j) =
            (∑ j ∈ Finset.range (Nat.succ k), u j) + u (Nat.succ k) := by
        simpa using (Finset.sum_range_succ u (Nat.succ k))
      have hsumDiff :
          (∑ j ∈ Finset.range (Nat.succ k),
              (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))) =
            (∑ j ∈ Finset.range k,
              (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))) +
                (∑ i ∈ Finset.range (Nat.succ k), u i) *
                  (v k - v (Nat.succ k)) := by
        simpa using
          (Finset.sum_range_succ
            (fun j => (∑ i ∈ Finset.range (j + 1), u i) *
              (v j - v (j + 1))) k)
      simp only [hNsub]
      rw [Finset.sum_range_succ, hsumU, hsumDiff, hIH]
      ring

/-- Reindex an integer half-open interval with nonnegative lower endpoint as
an initial natural-number range. -/
private theorem periodicLogPhase_sum_range_int_shift
    (lo : ℤ) (hlo : 0 ≤ lo) (k : ℕ) (f : ℤ → ℂ) :
    (∑ i ∈ Finset.range k, f (lo + (i : ℤ))) =
      ∑ n ∈ Finset.Ico lo (lo + (k : ℤ)), f n := by
  classical
  refine Finset.sum_bij (fun i _ => lo + (i : ℤ)) ?_ ?_ ?_ ?_
  · intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    apply Finset.mem_Ico.mpr
    constructor
    · exact le_add_of_nonneg_right (by exact_mod_cast (Nat.zero_le i))
    · have hikZ : (i : ℤ) < (k : ℤ) := by exact_mod_cast hik
      simpa [add_comm] using add_lt_add_left hikZ lo
  · intro i hi j hj hij
    have hcast : (i : ℤ) = (j : ℤ) := add_left_cancel hij
    exact_mod_cast hcast
  · intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hnlo, hnhi⟩
    have hnnonneg : 0 ≤ n := le_trans hlo hnlo
    have hloCast : (lo.toNat : ℤ) = lo := Int.toNat_of_nonneg hlo
    have hnCast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hnnonneg
    have hnatLo : lo.toNat ≤ n.toNat := by
      exact_mod_cast (by simpa [hloCast, hnCast] using hnlo)
    have hnatHi : n.toNat < lo.toNat + k := by
      have hnatHiZ : (n.toNat : ℤ) < (lo.toNat : ℤ) + (k : ℤ) := by
        simpa [hloCast, hnCast] using hnhi
      exact_mod_cast hnatHiZ
    let i : ℕ := n.toNat - lo.toNat
    refine ⟨i, Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [i]
      omega
    · dsimp [i]
      calc
        lo + ((n.toNat - lo.toNat : ℕ) : ℤ) =
            (lo.toNat : ℤ) + ((n.toNat - lo.toNat : ℕ) : ℤ) := by rw [hloCast]
        _ = ((lo.toNat + (n.toNat - lo.toNat) : ℕ) : ℤ) := by push_cast; ring
        _ = (n.toNat : ℤ) := by rw [Nat.add_sub_of_le hnatLo]
        _ = n := hnCast
  · intro i hi
    rfl

/-- On a positive real base, the source complex power factors into the
half-power weight and the real logarithmic phase used above. -/
private theorem periodicLogPhase_cpow_factor
    {t x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) =
      ((Real.rpow x (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp ((-Complex.I * (t : ℂ)) * (Real.log x : ℂ)) := by
  have hcpow :
      (x : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) =
        Complex.exp (((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) *
          (Real.log x : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.ofReal_log hx.le]
    congr 1
    ring
  have hrpow :
      ((Real.rpow x (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        Complex.exp ((-(1 / 2 : ℂ)) * (Real.log x : ℂ)) := by
    have hreal := Real.rpow_def_of_pos hx (-(1 / 2 : ℝ))
    calc
      ((Real.rpow x (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
          ((Real.exp (Real.log x * (-(1 / 2 : ℝ))) : ℝ) : ℂ) :=
        congrArg Complex.ofReal hreal
      _ = Complex.exp ((-(1 / 2 : ℂ)) * (Real.log x : ℂ)) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
  calc
    (x : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) =
        Complex.exp (((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) *
          (Real.log x : ℂ)) := hcpow
    _ = Complex.exp ((-(1 / 2 : ℂ)) * (Real.log x : ℂ)) *
        Complex.exp ((-Complex.I * (t : ℂ)) * (Real.log x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    _ = _ := by rw [hrpow]

/-- The real exponential-phase notation at the logarithmic phase agrees with
the complex exponential factor in `Complex.cpow` on positive integers. -/
private theorem periodicLogPhase_realPhase_eq_exp
    {t : ℝ} (n : ℤ) :
    FractionalPrimes.realExponentialPhase
        (fun u => -(t / (2 * Real.pi)) * Real.log u) n =
      Complex.exp ((-Complex.I * (t : ℂ)) * (Real.log (n : ℝ) : ℂ)) := by
  have hreal :
      2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (n : ℝ)) =
        -t * Real.log (n : ℝ) := by
    field_simp [ne_of_gt Real.pi_pos]
    <;> ring
  unfold FractionalPrimes.realExponentialPhase
  rw [hreal]
  push_cast
  congr 1
  ring

private theorem periodicLogPhase_cpow_factor_int
    {t : ℝ} (n : ℤ) (hn : 0 < (n : ℝ)) :
    (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) =
      ((Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        FractionalPrimes.realExponentialPhase
          (fun u => -(t / (2 * Real.pi)) * Real.log u) n := by
  calc
    (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) =
        ((n : ℝ) : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) := by
          norm_cast
    _ = ((Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp ((-Complex.I * (t : ℂ)) * (Real.log (n : ℝ) : ℂ)) :=
        periodicLogPhase_cpow_factor hn
    _ = _ := by rw [periodicLogPhase_realPhase_eq_exp]

/-- Inserting the exact half-power factor by finite Abel summation gives the
plain periodic logarithmic Dirichlet bound on every subinterval of `(L,2L]`.
The endpoint convention remains `(x,x+H]`. -/
theorem periodicLogPhaseBoundedWeightDirichletInterval
    {alpha A X L T0 t x H : ℝ} {q : ℕ} {omega : ℤ → ℂ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hperiod : ∀ n : ℤ, omega n = omega (n % (q : ℤ)))
    (hweight : ∀ n : ℤ, ‖omega n‖ ≤ 1)
    (hxL : L ≤ x) (hupper : x + H ≤ 2 * L) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x H,
        omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))‖ ≤
      periodicLogPhaseConstant alpha A * Real.sqrt L *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  classical
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := lt_of_lt_of_le
    (Real.rpow_pos_of_pos hXpos _) hLlower
  have hT0pos : 0 < T0 := by linarith
  let base : ℝ :=
    X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)
  have hbase : 0 ≤ base := by
    dsimp [base]
    exact add_nonneg (Real.rpow_nonneg hXpos.le _)
      (Real.rpow_nonneg hT0pos.le _)
  have hCnonneg : 0 ≤ periodicLogPhaseConstant alpha A := by
    unfold periodicLogPhaseConstant
    exact le_trans (by norm_num) (le_max_left _ _)
  have hBnonneg (L : ℝ) (hL : 0 ≤ L) :
      0 ≤ periodicLogPhaseConstant alpha A * L * base :=
    mul_nonneg (mul_nonneg hCnonneg hL) hbase
  by_cases hH : 0 < H
  · let lo : ℤ := Int.floor x + 1
    let hi : ℤ := Int.floor (x + H) + 1
    have hfloorMono : Int.floor x ≤ Int.floor (x + H) :=
      Int.floor_mono (by linarith)
    have hlo0 : 0 ≤ lo := by
      have hfloor0 : 0 ≤ Int.floor x :=
        Int.floor_nonneg.mpr (by linarith)
      dsimp [lo]
      omega
    have hlox : x < (lo : ℝ) := by
      dsimp [lo]
      push_cast
      exact Int.lt_floor_add_one x
    have hhiLo : lo ≤ hi := by
      dsimp [lo, hi]
      omega
    have hNnonneg : 0 ≤ hi - lo := sub_nonneg.mpr hhiLo
    let N : ℕ := (hi - lo).toNat
    have hNcast : (N : ℤ) = hi - lo := by
      dsimp [N]
      exact Int.toNat_of_nonneg hNnonneg
    have hhi : hi = lo + (N : ℤ) := by omega
    have hinterval :
        FractionalPrimes.realIntegerInterval x H = Finset.Ico lo hi := by
      simp [FractionalPrimes.realIntegerInterval, lo, hi]
    have hB : 0 ≤ periodicLogPhaseConstant alpha A * L * base :=
      hBnonneg L hLpos.le
    by_cases hN : 0 < N
    · let f : ℤ → ℂ := fun n => omega n *
        FractionalPrimes.realExponentialPhase
          (fun u => -(t / (2 * Real.pi)) * Real.log u) n
      let u : ℕ → ℂ := fun i => f (lo + (i : ℤ))
      let weight : ℕ → ℝ := fun i =>
        Real.rpow ((lo + (i : ℤ) : ℝ)) (-(1 / 2 : ℝ))
      let v : ℕ → ℂ := fun i => (weight i : ℂ)
      have hphasePrefix : ∀ k : ℕ, k ≤ N →
          ‖∑ i ∈ Finset.range k, u i‖ ≤
            periodicLogPhaseConstant alpha A * L * base := by
        intro k hk
        by_cases hkpos : 0 < k
        · let endpoint : ℤ := lo + (k : ℤ) - 1
          let Yk : ℝ := (endpoint : ℝ) - x
          have hendpoint : endpoint ≤ Int.floor (x + H) := by
            have hkcast : (k : ℤ) ≤ (N : ℤ) := by exact_mod_cast hk
            calc
              endpoint = lo + (k : ℤ) - 1 := rfl
              _ ≤ lo + (N : ℤ) - 1 := by omega
              _ = hi - 1 := by rw [hhi]
              _ = Int.floor (x + H) := by dsimp [hi]; omega
          have hYpos : 0 < Yk := by
            have hendpointLo : lo ≤ endpoint := by
              dsimp [endpoint]
              omega
            have hendpointLoReal : (lo : ℝ) ≤ (endpoint : ℝ) := by
              exact_mod_cast hendpointLo
            dsimp [Yk]
            linarith [hlox, hendpointLoReal]
          have hy : x + Yk = (endpoint : ℝ) := by
            dsimp [Yk]
            ring
          have hfloorEnd : Int.floor (x + Yk) + 1 = lo + (k : ℤ) := by
            rw [hy, Int.floor_intCast]
            dsimp [endpoint]
            omega
          have hintervalPrefix :
              FractionalPrimes.realIntegerInterval x Yk =
                Finset.Ico lo (lo + (k : ℤ)) := by
            change Finset.Ico (Int.floor x + 1)
                (Int.floor (x + Yk) + 1) = _
            rw [show Int.floor x + 1 = lo by rfl, hfloorEnd]
          have hYupper : x + Yk ≤ 2 * L := by
            rw [hy]
            have hfloorReal :
                (Int.floor (x + H) : ℝ) ≤ x + H := Int.floor_le _
            have hendpointReal :
                (endpoint : ℝ) ≤ (Int.floor (x + H) : ℝ) := by
              exact_mod_cast hendpoint
            calc
              (endpoint : ℝ) ≤ x + H := hendpointReal.trans hfloorReal
              _ ≤ 2 * L := hupper
          have hsumPrefix :
              (∑ i ∈ Finset.range k, u i) =
                ∑ n ∈ FractionalPrimes.realIntegerInterval x Yk,
                  omega n * FractionalPrimes.realExponentialPhase
                    (fun u => -(t / (2 * Real.pi)) * Real.log u) n := by
            calc
              _ = ∑ n ∈ Finset.Ico lo (lo + (k : ℤ)), f n :=
                periodicLogPhase_sum_range_int_shift lo hlo0 k f
              _ = ∑ n ∈ FractionalPrimes.realIntegerInterval x Yk, f n := by
                rw [← hintervalPrefix]
              _ = _ := by simp [f]
          have hphaseBound := periodicLogPhaseBoundedWeightPhaseInterval
            (alpha := alpha) (A := A) (X := X) (L := L) (T0 := T0)
            (s := t) (x := x) (H := Yk) (q := q) (omega := omega)
            halpha halpha1 hA hX hLlower hLupper hq hqBound hT0 hT0t htX
            hperiod hweight hxL hYupper
          rw [hsumPrefix]
          simpa [f, base] using hphaseBound
        · have hkzero : k = 0 := by omega
          subst k
          simp [u, hB]
      have hweightStart : weight 0 ≤ L ^ (-(1 / 2 : ℝ)) := by
        have harg : L ≤ (lo : ℝ) := le_of_lt (lt_of_le_of_lt hxL hlox)
        have hmono := Real.rpow_le_rpow_of_nonpos hLpos harg
          (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
        simpa [weight] using hmono
      have hscalePow : L * L ^ (-(1 / 2 : ℝ)) = Real.sqrt L := by
        calc
          L * L ^ (-(1 / 2 : ℝ)) = L ^ (1 : ℝ) * L ^ (-(1 / 2 : ℝ)) := by
            rw [Real.rpow_one]
          _ = L ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by
            rw [← Real.rpow_add hLpos]
          _ = L ^ (1 / 2 : ℝ) := by congr 1 <;> norm_num
          _ = Real.sqrt L := (Real.sqrt_eq_rpow L).symm
      have hscale : L * weight 0 ≤ Real.sqrt L := by
        calc
          L * weight 0 ≤ L * L ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hweightStart hLpos.le
          _ = Real.sqrt L := hscalePow
      have hweightMono : ∀ i : ℕ, weight (i + 1) ≤ weight i := by
        intro i
        have hloPos : 0 < (lo : ℝ) := lt_trans hLpos
          (lt_of_le_of_lt hxL hlox)
        have hiNonneg : 0 ≤ (i : ℝ) := by positivity
        apply Real.rpow_le_rpow_of_nonpos
          (by push_cast; linarith : 0 < (lo + (i : ℤ) : ℝ))
        · push_cast
          nlinarith
        · norm_num
      have hweightNonneg : ∀ i : ℕ, 0 ≤ weight i := by
        intro i
        dsimp [weight]
        exact Real.rpow_nonneg (by positivity) _
      have hvnorm : ∀ i : ℕ, ‖v i‖ = weight i := by
        intro i
        have hpos : 0 ≤ weight i := by
          dsimp [weight]
          exact Real.rpow_nonneg (by positivity) _
        simp [v, abs_of_nonneg hpos]
      have hvdiff (i : ℕ) :
          ‖v i - v (i + 1)‖ = weight i - weight (i + 1) := by
        have hmono := hweightMono i
        have hdiff : 0 ≤ weight i - weight (i + 1) := sub_nonneg.mpr hmono
        rw [show v i - v (i + 1) =
            ((weight i - weight (i + 1) : ℝ) : ℂ) by simp [v]]
        calc
          ‖((weight i - weight (i + 1) : ℝ) : ℂ)‖ =
              |weight i - weight (i + 1)| := Complex.norm_real _
          _ = weight i - weight (i + 1) := abs_of_nonneg hdiff
      have htel : ∀ m : ℕ,
          (∑ i ∈ Finset.range m, (weight i - weight (i + 1))) =
            weight 0 - weight m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            calc
              (∑ i ∈ Finset.range (m + 1),
                  (weight i - weight (i + 1))) =
                  (∑ i ∈ Finset.range m,
                    (weight i - weight (i + 1))) +
                    (weight m - weight (m + 1)) := by
                      rw [Finset.sum_range_succ]
              _ = weight 0 - weight (m + 1) := by rw [ih]; ring
      have hAbel :
          ‖∑ i ∈ Finset.range N, u i * v i‖ ≤
            periodicLogPhaseConstant alpha A * L * base * weight 0 := by
        rw [periodicLogPhase_sum_range_mul_abel_identity N u v hN]
        calc
          _ ≤ ‖(∑ i ∈ Finset.range N, u i) * v (N - 1)‖ +
              ∑ j ∈ Finset.range (N - 1),
                ‖(∑ i ∈ Finset.range (j + 1), u i) *
                  (v j - v (j + 1))‖ := by
                calc
                  _ ≤ ‖(∑ i ∈ Finset.range N, u i) * v (N - 1)‖ +
                      ‖∑ j ∈ Finset.range (N - 1),
                        (∑ i ∈ Finset.range (j + 1), u i) *
                          (v j - v (j + 1))‖ := norm_add_le _ _
                  _ ≤ _ := add_le_add le_rfl (norm_sum_le _ _)
          _ ≤ periodicLogPhaseConstant alpha A * L * base * weight (N - 1) +
              ∑ j ∈ Finset.range (N - 1),
                periodicLogPhaseConstant alpha A * L * base *
                  (weight j - weight (j + 1)) := by
                apply add_le_add
                · rw [norm_mul, hvnorm]
                  exact mul_le_mul (hphasePrefix N le_rfl) le_rfl
                    (hweightNonneg (N - 1)) hB
                · apply Finset.sum_le_sum
                  intro j hj
                  rw [norm_mul, hvdiff]
                  apply mul_le_mul
                    (hphasePrefix (j + 1) (by
                      have hj' := Finset.mem_range.mp hj
                      omega)) le_rfl
                    (sub_nonneg.mpr (hweightMono j)) hB
          _ = periodicLogPhaseConstant alpha A * L * base * weight 0 := by
                rw [← Finset.mul_sum]
                rw [htel (N - 1)]
                ring
      have hscaleB :
          periodicLogPhaseConstant alpha A * L * base * weight 0 ≤
            periodicLogPhaseConstant alpha A * Real.sqrt L * base := by
        have hCB : 0 ≤ periodicLogPhaseConstant alpha A * base :=
          mul_nonneg hCnonneg hbase
        calc
          periodicLogPhaseConstant alpha A * L * base * weight 0 =
              (periodicLogPhaseConstant alpha A * base) * (L * weight 0) := by ring
          _ ≤ (periodicLogPhaseConstant alpha A * base) * Real.sqrt L :=
            mul_le_mul_of_nonneg_left hscale hCB
          _ = periodicLogPhaseConstant alpha A * Real.sqrt L * base := by ring
      have hsumReindex :
          (∑ n ∈ FractionalPrimes.realIntegerInterval x H,
              omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))) =
            ∑ i ∈ Finset.range N, u i * v i := by
        rw [hinterval]
        calc
          _ = ∑ i ∈ Finset.range N,
              (omega (lo + (i : ℤ)) *
                ((lo + (i : ℤ) : ℤ) : ℂ) ^
                  ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))) := by
              rw [hhi]
              exact (periodicLogPhase_sum_range_int_shift lo hlo0 N
                (fun n => omega n * (n : ℂ) ^
                  ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)))).symm
          _ = ∑ i ∈ Finset.range N, u i * v i := by
              apply Finset.sum_congr rfl
              intro i hi
              have hn : 0 < (lo + (i : ℤ) : ℝ) := by
                have hcastlo : x < (lo : ℝ) := hlox
                have hindex : 0 ≤ (i : ℝ) := by positivity
                push_cast
                linarith
              have hncast : 0 < ((lo + (i : ℤ) : ℤ) : ℝ) := by
                simpa only [Int.cast_add, Int.cast_natCast] using hn
              have hcpow := periodicLogPhase_cpow_factor_int
                (t := t) (lo + (i : ℤ)) hncast
              simp only [u, v, f, weight]
              rw [hcpow]
              have hweightCast :
                  ((lo + (i : ℤ) : ℤ) : ℝ) =
                    (lo : ℝ) + ((i : ℤ) : ℝ) := by
                rw [Int.cast_add]
              rw [hweightCast]
              ring
      rw [hsumReindex]
      exact hAbel.trans hscaleB
    · have hNzero : N = 0 := by omega
      have hintervalEmpty :
          FractionalPrimes.realIntegerInterval x H = ∅ := by
        rw [hinterval, hhi, hNzero]
        simp
      rw [hintervalEmpty]
      simp
      positivity
  · have hHnonpos : H ≤ 0 := le_of_not_gt hH
    have hintervalEmpty :
        FractionalPrimes.realIntegerInterval x H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hmem :=
        (FractionalPrimes.mem_realIntegerInterval_iff x H n).mp hn
      linarith
    rw [hintervalEmpty]
    simp
    positivity

/-- A second finite Abel step inserts the source's increasing factor
`log(r*n)`, with its exact uniform `8 * log X` loss. -/
theorem periodicLogPhaseBoundedWeightLogDirichletInterval
    {alpha A X L T0 t x H r : ℝ} {q : ℕ} {omega : ℤ → ℂ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hperiod : ∀ n : ℤ, omega n = omega (n % (q : ℤ)))
    (hweight : ∀ n : ℤ, ‖omega n‖ ≤ 1)
    (hr : 1 ≤ r) (hrX : r ≤ X)
    (hxL : L ≤ x) (hupper : x + H ≤ 2 * L) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x H,
        omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) *
          (Real.log (r * (n : ℝ)) : ℂ)‖ ≤
      8 * Real.log X * periodicLogPhaseConstant alpha A * Real.sqrt L *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  classical
  have hXpos : 0 < X := by linarith
  have hXgt1 : 1 < X := by linarith
  have hLpos : 0 < L := lt_of_lt_of_le
    (Real.rpow_pos_of_pos hXpos _) hLlower
  have hLgt1 : 1 < L :=
    lt_of_lt_of_le (Real.one_lt_rpow hXgt1 halpha) hLlower
  have hT0pos : 0 < T0 := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos hXgt1
  let base : ℝ :=
    X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)
  have hbase : 0 ≤ base := by
    dsimp [base]
    exact add_nonneg (Real.rpow_nonneg hXpos.le _)
      (Real.rpow_nonneg hT0pos.le _)
  have hCnonneg : 0 ≤ periodicLogPhaseConstant alpha A := by
    unfold periodicLogPhaseConstant
    exact le_trans (by norm_num) (le_max_left _ _)
  have hB0 :
      0 ≤ periodicLogPhaseConstant alpha A * Real.sqrt L * base :=
    mul_nonneg (mul_nonneg hCnonneg (Real.sqrt_nonneg L)) hbase
  by_cases hH : 0 < H
  · let lo : ℤ := Int.floor x + 1
    let hi : ℤ := Int.floor (x + H) + 1
    have hfloorMono : Int.floor x ≤ Int.floor (x + H) :=
      Int.floor_mono (by linarith)
    have hlo0 : 0 ≤ lo := by
      have hfloor0 : 0 ≤ Int.floor x := Int.floor_nonneg.mpr (by linarith)
      dsimp [lo]
      omega
    have hlox : x < (lo : ℝ) := by
      dsimp [lo]
      push_cast
      exact Int.lt_floor_add_one x
    have hhiLo : lo ≤ hi := by
      dsimp [lo, hi]
      omega
    have hNnonneg : 0 ≤ hi - lo := sub_nonneg.mpr hhiLo
    let N : ℕ := (hi - lo).toNat
    have hNcast : (N : ℤ) = hi - lo := by
      dsimp [N]
      exact Int.toNat_of_nonneg hNnonneg
    have hhi : hi = lo + (N : ℤ) := by omega
    have hinterval :
        FractionalPrimes.realIntegerInterval x H = Finset.Ico lo hi := by
      simp [FractionalPrimes.realIntegerInterval, lo, hi]
    have hLlo : L < (lo : ℝ) := lt_of_le_of_lt hxL hlox
    have hloPos : 0 < (lo : ℝ) := lt_trans hLpos hLlo
    have hB :
        0 ≤ periodicLogPhaseConstant alpha A * Real.sqrt L * base := hB0
    by_cases hN : 0 < N
    · let f : ℤ → ℂ := fun n =>
        omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))
      let u : ℕ → ℂ := fun i => f (lo + (i : ℤ))
      let logWeight : ℕ → ℝ := fun i =>
        Real.log (r * (lo + (i : ℤ) : ℝ))
      let v : ℕ → ℂ := fun i => (logWeight i : ℂ)
      have hprefix : ∀ k : ℕ, k ≤ N →
          ‖∑ i ∈ Finset.range k, u i‖ ≤
            periodicLogPhaseConstant alpha A * Real.sqrt L * base := by
        intro k hk
        by_cases hkpos : 0 < k
        · let endpoint : ℤ := lo + (k : ℤ) - 1
          let Yk : ℝ := (endpoint : ℝ) - x
          have hendpoint : endpoint ≤ Int.floor (x + H) := by
            have hkcast : (k : ℤ) ≤ (N : ℤ) := by exact_mod_cast hk
            calc
              endpoint = lo + (k : ℤ) - 1 := rfl
              _ ≤ lo + (N : ℤ) - 1 := by omega
              _ = hi - 1 := by rw [hhi]
              _ = Int.floor (x + H) := by dsimp [hi]; omega
          have hendpointLo : lo ≤ endpoint := by
            dsimp [endpoint]
            omega
          have hendpointLoReal : (lo : ℝ) ≤ (endpoint : ℝ) := by
            exact_mod_cast hendpointLo
          have hYpos : 0 < Yk := by
            dsimp [Yk]
            linarith [hlox]
          have hy : x + Yk = (endpoint : ℝ) := by
            dsimp [Yk]
            ring
          have hfloorEnd : Int.floor (x + Yk) + 1 = lo + (k : ℤ) := by
            rw [hy, Int.floor_intCast]
            dsimp [endpoint]
            omega
          have hintervalPrefix :
              FractionalPrimes.realIntegerInterval x Yk =
                Finset.Ico lo (lo + (k : ℤ)) := by
            change Finset.Ico (Int.floor x + 1)
                (Int.floor (x + Yk) + 1) = _
            rw [show Int.floor x + 1 = lo by rfl, hfloorEnd]
          have hYupper : x + Yk ≤ 2 * L := by
            rw [hy]
            have hfloorReal :
                (Int.floor (x + H) : ℝ) ≤ x + H := Int.floor_le _
            have hendpointReal :
                (endpoint : ℝ) ≤ (Int.floor (x + H) : ℝ) := by
              exact_mod_cast hendpoint
            calc
              (endpoint : ℝ) ≤ x + H := hendpointReal.trans hfloorReal
              _ ≤ 2 * L := hupper
          have hsumPrefix :
              (∑ i ∈ Finset.range k, u i) =
                ∑ n ∈ FractionalPrimes.realIntegerInterval x Yk, f n := by
            calc
              _ = ∑ n ∈ Finset.Ico lo (lo + (k : ℤ)), f n :=
                periodicLogPhase_sum_range_int_shift lo hlo0 k f
              _ = ∑ n ∈ FractionalPrimes.realIntegerInterval x Yk, f n := by
                rw [← hintervalPrefix]
          have hprefixBound := periodicLogPhaseBoundedWeightDirichletInterval
            (alpha := alpha) (A := A) (X := X) (L := L) (T0 := T0)
            (t := t) (x := x) (H := Yk) (q := q) (omega := omega)
            halpha halpha1 hA hX hLlower hLupper hq hqBound hT0 hT0t htX
            hperiod hweight hxL hYupper
          rw [hsumPrefix]
          simpa [f, base] using hprefixBound
        · have hkzero : k = 0 := by omega
          subst k
          simpa using hB
      have hlogArgPos : ∀ i : ℕ,
          0 < r * (lo + (i : ℤ) : ℝ) := by
        intro i
        have hiNonneg : 0 ≤ (i : ℝ) := by positivity
        have hbasePos : 0 < (lo + (i : ℤ) : ℝ) := by
          push_cast
          linarith
        exact mul_pos (by linarith : 0 < r) hbasePos
      have hlogArgGt1 : ∀ i : ℕ,
          1 < r * (lo + (i : ℤ) : ℝ) := by
        intro i
        have hiNonneg : 0 ≤ (i : ℝ) := by positivity
        have hbaseGt1 : 1 < (lo + (i : ℤ) : ℝ) := by
          push_cast
          linarith
        have hmul : (lo + (i : ℤ) : ℝ) ≤
            r * (lo + (i : ℤ) : ℝ) := by
          have hbaseNonneg : 0 ≤ (lo + (i : ℤ) : ℝ) := by
            linarith [hbaseGt1]
          have hmul' := mul_le_mul_of_nonneg_right hr hbaseNonneg
          nlinarith [hmul']
        exact lt_of_lt_of_le hbaseGt1 hmul
      have hlogNonneg : ∀ i : ℕ, 0 ≤ logWeight i := by
        intro i
        dsimp [logWeight]
        exact le_of_lt (Real.log_pos (hlogArgGt1 i))
      have hlogMono : ∀ i : ℕ, logWeight i ≤ logWeight (i + 1) := by
        intro i
        apply Real.log_le_log (hlogArgPos i)
        have hbaseMono :
            (lo + (i : ℤ) : ℝ) ≤ (lo + ((i + 1 : ℕ) : ℤ) : ℝ) := by
          push_cast
          norm_num
        exact mul_le_mul_of_nonneg_left hbaseMono (by linarith : 0 ≤ r)
      have hvnorm : ∀ i : ℕ, ‖v i‖ = logWeight i := by
        intro i
        have hnonneg := hlogNonneg i
        simp [v, Complex.norm_real, abs_of_nonneg hnonneg]
      have hvdiff (i : ℕ) :
          ‖v i - v (i + 1)‖ = logWeight (i + 1) - logWeight i := by
        have hmono := hlogMono i
        have hdiff : 0 ≤ logWeight (i + 1) - logWeight i := sub_nonneg.mpr hmono
        calc
          ‖v i - v (i + 1)‖ =
              |logWeight i - logWeight (i + 1)| := by
                rw [show v i - v (i + 1) =
                    ((logWeight i - logWeight (i + 1) : ℝ) : ℂ) by simp [v]]
                exact Complex.norm_real _
          _ = logWeight (i + 1) - logWeight i := by
            rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
            ring
      have htel : ∀ m : ℕ,
          (∑ i ∈ Finset.range m,
              (logWeight (i + 1) - logWeight i)) =
            logWeight m - logWeight 0 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            calc
              (∑ i ∈ Finset.range (m + 1),
                  (logWeight (i + 1) - logWeight i)) =
                  (∑ i ∈ Finset.range m,
                    (logWeight (i + 1) - logWeight i)) +
                      (logWeight (m + 1) - logWeight m) := by
                        rw [Finset.sum_range_succ]
              _ = logWeight (m + 1) - logWeight 0 := by rw [ih]; ring
      have hlastInt : lo + ((N - 1 : ℕ) : ℤ) ≤ Int.floor (x + H) := by
        rw [show Int.floor (x + H) = hi - 1 by dsimp [hi]; omega]
        rw [hhi]
        have hNsub : ((N - 1 : ℕ) : ℤ) + 1 = (N : ℤ) := by
          exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ N))
        omega
      have hlastLe :
          (lo + ((N - 1 : ℕ) : ℤ) : ℝ) ≤ 2 * L := by
        have hfloorReal :
            (Int.floor (x + H) : ℝ) ≤ x + H := Int.floor_le _
        have hlastFloor :
            (lo + ((N - 1 : ℕ) : ℤ) : ℝ) ≤
              (Int.floor (x + H) : ℝ) := by exact_mod_cast hlastInt
        exact le_trans hlastFloor (le_trans hfloorReal hupper)
      have hlastPos : 0 < (lo + ((N - 1 : ℕ) : ℤ) : ℝ) := by
        have hidx : 0 ≤ ((N - 1 : ℕ) : ℤ) := by positivity
        have hidxR : 0 ≤ (((N - 1 : ℕ) : ℤ) : ℝ) := by positivity
        push_cast
        linarith
      have hlastArgLe :
          r * (lo + ((N - 1 : ℕ) : ℤ) : ℝ) ≤ 2 * X ^ 2 := by
        calc
          r * (lo + ((N - 1 : ℕ) : ℤ) : ℝ) ≤ r * (2 * L) :=
            mul_le_mul_of_nonneg_left hlastLe (by linarith : 0 ≤ r)
          _ ≤ X * (2 * L) :=
            mul_le_mul_of_nonneg_right hrX (by positivity)
          _ ≤ 2 * X ^ 2 := by nlinarith [hLupper]
      have hlogLast : logWeight (N - 1) ≤ 3 * Real.log X := by
        have hlogle := Real.log_le_log (hlogArgPos (N - 1)) hlastArgLe
        have hlogproduct : Real.log (2 * X ^ 2) =
            Real.log 2 + 2 * Real.log X := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          norm_num
        have hlog2 : Real.log 2 ≤ Real.log X :=
          Real.log_le_log (by norm_num) (by linarith)
        dsimp [logWeight]
        rw [hlogproduct] at hlogle
        nlinarith
      have hAbel :
          ‖∑ i ∈ Finset.range N, u i * v i‖ ≤
            periodicLogPhaseConstant alpha A * Real.sqrt L * base *
              (6 * Real.log X) := by
        rw [periodicLogPhase_sum_range_mul_abel_identity N u v hN]
        calc
          _ ≤ ‖(∑ i ∈ Finset.range N, u i) * v (N - 1)‖ +
              ∑ j ∈ Finset.range (N - 1),
                ‖(∑ i ∈ Finset.range (j + 1), u i) *
                  (v j - v (j + 1))‖ := by
                calc
                  _ ≤ ‖(∑ i ∈ Finset.range N, u i) * v (N - 1)‖ +
                      ‖∑ j ∈ Finset.range (N - 1),
                        (∑ i ∈ Finset.range (j + 1), u i) *
                          (v j - v (j + 1))‖ := norm_add_le _ _
                  _ ≤ _ := add_le_add le_rfl (norm_sum_le _ _)
          _ ≤ periodicLogPhaseConstant alpha A * Real.sqrt L * base *
                logWeight (N - 1) +
              ∑ j ∈ Finset.range (N - 1),
                periodicLogPhaseConstant alpha A * Real.sqrt L * base *
                  (logWeight (j + 1) - logWeight j) := by
                apply add_le_add
                · rw [norm_mul, hvnorm]
                  exact mul_le_mul (hprefix N le_rfl) le_rfl
                    (hlogNonneg (N - 1)) hB
                · apply Finset.sum_le_sum
                  intro j hj
                  rw [norm_mul, hvdiff]
                  apply mul_le_mul
                    (hprefix (j + 1) (by
                      have hj' := Finset.mem_range.mp hj
                      omega)) le_rfl
                    (sub_nonneg.mpr (hlogMono j)) hB
          _ ≤ periodicLogPhaseConstant alpha A * Real.sqrt L * base *
                (6 * Real.log X) := by
                calc
                  _ = (periodicLogPhaseConstant alpha A * Real.sqrt L * base) *
                      (logWeight (N - 1) +
                        ∑ j ∈ Finset.range (N - 1),
                          (logWeight (j + 1) - logWeight j)) := by
                        rw [← Finset.mul_sum]
                        ring
                  _ = (periodicLogPhaseConstant alpha A * Real.sqrt L * base) *
                      (2 * logWeight (N - 1) - logWeight 0) := by
                        rw [htel (N - 1)]
                        ring
                  _ ≤ (periodicLogPhaseConstant alpha A * Real.sqrt L * base) *
                      (2 * logWeight (N - 1)) := by
                        apply mul_le_mul_of_nonneg_left
                        · linarith [hlogNonneg 0]
                        · exact hB
                  _ ≤ _ := by
                        apply mul_le_mul_of_nonneg_left
                        · nlinarith [hlogLast]
                        · exact hB
      have hsumReindex :
          (∑ n ∈ FractionalPrimes.realIntegerInterval x H,
              omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) *
                (Real.log (r * (n : ℝ)) : ℂ)) =
            ∑ i ∈ Finset.range N, u i * v i := by
        rw [hinterval]
        calc
          _ = ∑ i ∈ Finset.range N,
              (omega (lo + (i : ℤ)) *
                ((lo + (i : ℤ) : ℤ) : ℂ) ^
                  ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))) *
                (Real.log (r * (lo + (i : ℤ) : ℝ)) : ℂ) := by
              rw [hhi]
              simpa only [Int.cast_add] using
                (periodicLogPhase_sum_range_int_shift lo hlo0 N
                (fun n => omega n * (n : ℂ) ^
                  ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) *
                  (Real.log (r * (n : ℝ)) : ℂ))).symm
          _ = ∑ i ∈ Finset.range N, u i * v i := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [u, v, f, logWeight]
      have hAbelEight :
          ‖∑ i ∈ Finset.range N, u i * v i‖ ≤
            periodicLogPhaseConstant alpha A * Real.sqrt L * base *
              (8 * Real.log X) := by
        calc
          _ ≤ periodicLogPhaseConstant alpha A * Real.sqrt L * base *
                (6 * Real.log X) := hAbel
          _ ≤ periodicLogPhaseConstant alpha A * Real.sqrt L * base *
                (8 * Real.log X) := by
                apply mul_le_mul_of_nonneg_left
                · nlinarith [hlogXpos]
                · exact hB
      rw [hsumReindex]
      calc
        _ ≤ periodicLogPhaseConstant alpha A * Real.sqrt L * base *
              (8 * Real.log X) := hAbelEight
        _ = 8 * Real.log X * periodicLogPhaseConstant alpha A *
              Real.sqrt L * base := by ring
    · have hNzero : N = 0 := by omega
      have hintervalEmpty :
          FractionalPrimes.realIntegerInterval x H = ∅ := by
        rw [hinterval, hhi, hNzero]
        simp
      rw [hintervalEmpty]
      simp
      positivity
  · have hHnonpos : H ≤ 0 := le_of_not_gt hH
    have hintervalEmpty :
        FractionalPrimes.realIntegerInterval x H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hmem :=
        (FractionalPrimes.mem_realIntegerInterval_iff x H n).mp hn
      linarith
    rw [hintervalEmpty]
    simp
    positivity

/-- The two exact conclusions of `ltw:plain-factor`, packaged under the
source manifest name. The half-open interval is parametrized as `(x,x+H]`. -/
theorem periodicLogPhaseDirichletBound
    {alpha A X L T0 t : ℝ} {q : ℕ} {omega : ℤ → ℂ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hperiod : ∀ n : ℤ, omega n = omega (n % (q : ℤ)))
    (hweight : ∀ n : ℤ, ‖omega n‖ ≤ 1) :
    (∀ (x H : ℝ), L ≤ x → x + H ≤ 2 * L →
      ‖∑ n ∈ FractionalPrimes.realIntegerInterval x H,
          omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))‖ ≤
        periodicLogPhaseConstant alpha A * Real.sqrt L *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ))) ∧
    (∀ (r x H : ℝ), 1 ≤ r → r ≤ X → L ≤ x → x + H ≤ 2 * L →
      ‖∑ n ∈ FractionalPrimes.realIntegerInterval x H,
          omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) *
            (Real.log (r * (n : ℝ)) : ℂ)‖ ≤
        8 * Real.log X * periodicLogPhaseConstant alpha A * Real.sqrt L *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ))) := by
  constructor
  · intro x H hxL hupper
    exact periodicLogPhaseBoundedWeightDirichletInterval
      halpha halpha1 hA hX hLlower hLupper hq hqBound
      hT0 hT0t htX hperiod hweight hxL hupper
  · intro r x H hr hrX hxL hupper
    exact periodicLogPhaseBoundedWeightLogDirichletInterval
      halpha halpha1 hA hX hLlower hLupper hq hqBound
      hT0 hT0t htX hperiod hweight hr hrX hxL hupper

end FractionalPrimes.Literature.Twisted

#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseDerivative_hasDerivAt
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseOrder_bounds
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseHighScaleTermBounds
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseConstant_ge_order
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseConstant_ge_highTerms
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseHighLargeResidueBound
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseHighFrequencyResidueBound
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseLowFrequencyResidueBound
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseResidueBound
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseBoundedWeightPhaseInterval
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseBoundedWeightDirichletInterval
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseBoundedWeightLogDirichletInterval
#print axioms FractionalPrimes.Literature.Twisted.sum_realIntegerInterval_filter_emod_eq_affine
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseResiduePartition
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseDerivative_magnitude_bounds
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseHigherDerivativeTest
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseSecondDerivativeTest
#print axioms FractionalPrimes.Literature.Twisted.periodicLogPhaseSecondDerivativeTest_coarse
