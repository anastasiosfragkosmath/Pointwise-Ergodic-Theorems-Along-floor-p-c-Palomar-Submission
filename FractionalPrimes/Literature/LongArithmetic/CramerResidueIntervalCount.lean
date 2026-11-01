module

public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace FractionalPrimes.Literature.LongArithmetic

private theorem rat_floor_difference_error (a b : ℚ) :
    |((⌊b⌋ - ⌊a⌋ : ℤ) : ℚ) - (b - a)| ≤ 1 := by
  have ha₁ : (⌊a⌋ : ℚ) ≤ a := Int.floor_le a
  have ha₂ : a < (⌊a⌋ : ℚ) + 1 := Int.lt_floor_add_one a
  have hb₁ : (⌊b⌋ : ℚ) ≤ b := Int.floor_le b
  have hb₂ : b < (⌊b⌋ : ℚ) + 1 := Int.lt_floor_add_one b
  rw [abs_le]
  constructor
  · have hEq :
        ((⌊b⌋ - ⌊a⌋ : ℤ) : ℚ) - (b - a) =
          ((⌊b⌋ : ℚ) - b) + (a - (⌊a⌋ : ℚ)) := by push_cast; ring
    rw [hEq]
    linarith
  · have hEq :
        ((⌊b⌋ - ⌊a⌋ : ℤ) : ℚ) - (b - a) =
          ((⌊b⌋ : ℚ) - b) + (a - (⌊a⌋ : ℚ)) := by push_cast; ring
    rw [hEq]
    linarith

/-- Exact interval-count estimate for one integer residue class. This is the
CRT counting step used in the proof of `lal:cramer-residue`: in an integer
interval of length `L`, one residue class modulo positive `q` has count
within one of `L/q`. The interval is strict at the lower endpoint and closed
at the upper endpoint. -/
theorem intIntervalResidueCount_error
    (X L q r : ℤ) (hL : 0 ≤ L) (hq : 0 < q) :
    |(((Finset.Ioc X (X + L)).filter
        (fun n : ℤ => n ≡ r [ZMOD q])).card : ℝ) -
        (L : ℝ) / (q : ℝ)| ≤ 1 := by
  let S : Finset ℤ := (Finset.Ioc X (X + L)).filter
    (fun n : ℤ => n ≡ r [ZMOD q])
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hquot : ((X - r : ℤ) : ℚ) / (q : ℚ) ≤
      ((X + L - r : ℤ) : ℚ) / (q : ℚ) := by
    apply div_le_div_of_nonneg_right _ hqQ.le
    exact_mod_cast (show X - r ≤ X + L - r by omega)
  have hfloor : ⌊((X - r : ℤ) : ℚ) / (q : ℚ)⌋ ≤
      ⌊((X + L - r : ℤ) : ℚ) / (q : ℚ)⌋ := Int.floor_mono hquot
  have hcard := Int.Ioc_filter_modEq_card X (X + L) (r := q) (hr := hq) r
  have hcount : (S.card : ℤ) =
      ⌊((X + L - r : ℤ) : ℚ) / (q : ℚ)⌋ -
        ⌊((X - r : ℤ) : ℚ) / (q : ℚ)⌋ := by
    have hcard' : S.card = max
        (⌊((X + L - r : ℤ) : ℚ) / (q : ℚ)⌋ -
          ⌊((X - r : ℤ) : ℚ) / (q : ℚ)⌋) 0 := by
      simpa [S] using hcard
    rw [hcard', max_eq_left (sub_nonneg.mpr hfloor)]
  have hlinear :
      (((X + L - r : ℤ) : ℚ) / (q : ℚ)) -
        (((X - r : ℤ) : ℚ) / (q : ℚ)) = (L : ℚ) / (q : ℚ) := by
    push_cast
    ring
  have hrat := rat_floor_difference_error
    (((X - r : ℤ) : ℚ) / (q : ℚ))
    (((X + L - r : ℤ) : ℚ) / (q : ℚ))
  have hrat' :
      |((⌊((X + L - r : ℤ) : ℚ) / (q : ℚ)⌋ -
          ⌊((X - r : ℤ) : ℚ) / (q : ℚ)⌋ : ℤ) : ℚ) -
          (L : ℚ) / (q : ℚ)| ≤ 1 := by
    rw [← hlinear]
    exact hrat
  have hratCard :
      |(S.card : ℚ) - (L : ℚ) / (q : ℚ)| ≤ 1 := by
    have hcountQ : (S.card : ℚ) =
        ((⌊((X + L - r : ℤ) : ℚ) / (q : ℚ)⌋ -
          ⌊((X - r : ℤ) : ℚ) / (q : ℚ)⌋ : ℤ) : ℚ) := by
      exact_mod_cast hcount
    rw [hcountQ]
    exact hrat'
  have hreal :
      |(S.card : ℝ) - (L : ℝ) / (q : ℝ)| ≤ 1 := by
    exact_mod_cast hratCard
  simpa [S] using hreal

#print axioms intIntervalResidueCount_error

private theorem real_floor_difference_error (a b : ℝ) :
    |((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) - (b - a)| ≤ 1 := by
  have ha₁ : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have ha₂ : a < (⌊a⌋ : ℝ) + 1 := Int.lt_floor_add_one a
  have hb₁ : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  have hb₂ : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
  rw [abs_le]
  constructor
  · have hEq :
        ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) - (b - a) =
          ((⌊b⌋ : ℝ) - b) + (a - (⌊a⌋ : ℝ)) := by push_cast; ring
    rw [hEq]
    linarith
  · have hEq :
        ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) - (b - a) =
          ((⌊b⌋ : ℝ) - b) + (a - (⌊a⌋ : ℝ)) := by push_cast; ring
    rw [hEq]
    linarith

private theorem rationalFloor_endpoint_eq_realFloor
    (X : ℝ) (a : ℤ) (m : ℕ) :
    ⌊(((Int.floor X - a : ℤ) : ℚ) / (m : ℚ))⌋ =
      ⌊(X - a) / (m : ℝ)⌋ := by
  rw [Rat.floor_intCast_div_natCast, Int.floor_div_natCast,
    Int.floor_sub_intCast]

private theorem rationalFloor_endpoint_eq_realFloor_intModulus
    (X : ℝ) (a m : ℤ) (hm : 0 < m) :
    ⌊(((Int.floor X - a : ℤ) : ℚ) / (m : ℚ))⌋ =
      ⌊(X - a) / (m : ℝ)⌋ := by
  have hmInt : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm.le
  have hmQ : (m.toNat : ℚ) = (m : ℚ) := by exact_mod_cast hmInt
  have hmR : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hmInt
  rw [← hmQ, ← hmR]
  exact rationalFloor_endpoint_eq_realFloor X a m.toNat

/-- The finite integer interval from the real half-open interval `(X,X+H]`.
This equivalence records both endpoint conventions exactly. -/
private theorem mem_realInterval_floorIoc (X H : ℝ) (n : ℤ) :
    n ∈ Finset.Ioc (Int.floor X) (Int.floor (X + H)) ↔
      X < (n : ℝ) ∧ (n : ℝ) ≤ X + H := by
  simp only [Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

/-- For a real half-open interval, the count in one integer residue class
differs from its length divided by the modulus by at most one. The finite
interval is represented by the exact floor endpoints, so the strict lower
endpoint and inclusive upper endpoint are retained. -/
theorem realIntervalResidueCount_error
    (X H : ℝ) (m r : ℤ) (hH : 0 ≤ H) (hm : 0 < m) :
    |(((Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
        (fun n : ℤ => n ≡ r [ZMOD m])).card : ℝ) - H / (m : ℝ)| ≤ 1 := by
  let S : Finset ℤ := (Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
    (fun n : ℤ => n ≡ r [ZMOD m])
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hquot : (X - (r : ℝ)) / (m : ℝ) ≤
      (X + H - (r : ℝ)) / (m : ℝ) := by
    apply div_le_div_of_nonneg_right _ hmR.le
    linarith
  have hfloor : ⌊(X - (r : ℝ)) / (m : ℝ)⌋ ≤
      ⌊(X + H - (r : ℝ)) / (m : ℝ)⌋ := Int.floor_mono hquot
  have hcard := Int.Ioc_filter_modEq_card
    (Int.floor X) (Int.floor (X + H)) (r := m) (hr := hm) r
  have hcard' : (S.card : ℤ) = max
      (⌊(((Int.floor (X + H) - r : ℤ) : ℚ) / (m : ℚ))⌋ -
        ⌊(((Int.floor X - r : ℤ) : ℚ) / (m : ℚ))⌋) 0 := by
    simpa [S] using hcard
  have hcount : (S.card : ℤ) =
      ⌊(X + H - (r : ℝ)) / (m : ℝ)⌋ -
        ⌊(X - (r : ℝ)) / (m : ℝ)⌋ := by
    rw [hcard',
      rationalFloor_endpoint_eq_realFloor_intModulus (X + H) r m hm,
      rationalFloor_endpoint_eq_realFloor_intModulus X r m hm,
      max_eq_left (sub_nonneg.mpr hfloor)]
  have hcountR : (S.card : ℝ) =
      ((⌊(X + H - (r : ℝ)) / (m : ℝ)⌋ -
        ⌊(X - (r : ℝ)) / (m : ℝ)⌋ : ℤ) : ℝ) := by
    exact_mod_cast hcount
  have hlin :
      ((X + H - (r : ℝ)) / (m : ℝ)) -
        ((X - (r : ℝ)) / (m : ℝ)) = H / (m : ℝ) := by
    field_simp
    ring
  have hfloorBound := real_floor_difference_error
    ((X - (r : ℝ)) / (m : ℝ)) ((X + H - (r : ℝ)) / (m : ℝ))
  have hfinal :
      |(S.card : ℝ) - H / (m : ℝ)| ≤ 1 := by
    rw [hcountR, ← hlin]
    exact hfloorBound
  simpa [S] using hfinal

#print axioms realIntervalResidueCount_error

private theorem exists_coprime_crt_residue
    (q d : ℕ) (a : ℤ) (hq : 0 < q) (hcop : Nat.Coprime q d) :
    ∃ r : ℤ, r ≡ a [ZMOD (q : ℤ)] ∧ r ≡ 0 [ZMOD (d : ℤ)] := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  let a₀ : ℕ := Int.toNat (a % (q : ℤ))
  have ha₀ : (a₀ : ℤ) = a % (q : ℤ) := by
    dsimp [a₀]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hqZ)
  let r₀ : ℕ := (Nat.chineseRemainder hcop a₀ 0).val
  have hr₀q : r₀ ≡ a₀ [MOD q] := (Nat.chineseRemainder hcop a₀ 0).property.1
  have hr₀d : r₀ ≡ 0 [MOD d] := (Nat.chineseRemainder hcop a₀ 0).property.2
  refine ⟨r₀, ?_, ?_⟩
  · have hrq : (r₀ : ℤ) ≡ (a₀ : ℤ) [ZMOD (q : ℤ)] := by
      simpa only [Nat.modEq_iff_dvd, Int.modEq_iff_dvd, Int.natCast_mul,
        Int.natCast_sub] using hr₀q
    calc
      (r₀ : ℤ) ≡ (a₀ : ℤ) [ZMOD (q : ℤ)] := hrq
      _ = a % (q : ℤ) := ha₀
      _ ≡ a [ZMOD (q : ℤ)] := Int.mod_modEq a (q : ℤ)
  · have hrdvd : d ∣ r₀ := Nat.modEq_zero_iff_dvd.mp hr₀d
    have hrdvdZ : (d : ℤ) ∣ (r₀ : ℤ) := Int.natCast_dvd_natCast.mpr hrdvd
    exact Int.modEq_zero_iff_dvd.mpr hrdvdZ

/-- The coprime CRT count used for each supported divisor in
`lal:cramer-residue`. If `d` is coprime to `q`, the simultaneous conditions
`d ∣ n` and `n ≡ a (mod q)` select one class modulo `q*d`; its count on the
real half-open interval differs from `H/(q*d) = H/lcm(d,q)` by at most one. -/
theorem coprimeCRTIntervalCount_error
    (X H : ℝ) (q d : ℕ) (a : ℤ)
    (hH : 0 ≤ H) (hq : 0 < q) (hd : 0 < d)
    (hcop : Nat.Coprime q d) :
    |(((Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
        (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)] ∧ (d : ℤ) ∣ n)).card : ℝ) -
        H / (Nat.lcm d q : ℝ)| ≤ 1 := by
  obtain ⟨r, hrq, hrd⟩ := exists_coprime_crt_residue q d a hq hcop
  have hcopZ : (q : ℤ).natAbs.Coprime (d : ℤ).natAbs := by
    simpa using hcop
  let I : Finset ℤ := Finset.Ioc (Int.floor X) (Int.floor (X + H))
  have hset : I.filter
      (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)] ∧ (d : ℤ) ∣ n) =
      I.filter (fun n : ℤ => n ≡ r [ZMOD ((q : ℤ) * (d : ℤ))]) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hnI, hna, hdn⟩
      have hnq : n ≡ r [ZMOD (q : ℤ)] := hna.trans hrq.symm
      have hnd0 : n ≡ 0 [ZMOD (d : ℤ)] :=
        Int.modEq_zero_iff_dvd.mpr hdn
      have hnd : n ≡ r [ZMOD (d : ℤ)] := hnd0.trans hrd.symm
      exact ⟨hnI, (Int.modEq_and_modEq_iff_modEq_mul hcopZ).mp ⟨hnq, hnd⟩⟩
    · rintro ⟨hnI, hnr⟩
      have hnq : n ≡ r [ZMOD (q : ℤ)] := Int.ModEq.of_mul_right (d : ℤ) hnr
      have hnd : n ≡ r [ZMOD (d : ℤ)] := Int.ModEq.of_mul_left (q : ℤ) hnr
      have hna : n ≡ a [ZMOD (q : ℤ)] := hnq.trans hrq
      have hnd0 : n ≡ 0 [ZMOD (d : ℤ)] := hnd.trans hrd
      exact ⟨hnI, hna, Int.modEq_zero_iff_dvd.mp hnd0⟩
  have hcount := realIntervalResidueCount_error X H
    ((q : ℤ) * (d : ℤ)) r hH (by positivity)
  have hlcm : (Nat.lcm d q : ℝ) = (q : ℝ) * (d : ℝ) := by
    rw [Nat.Coprime.lcm_eq_mul hcop.symm]
    push_cast
    ring
  simpa [I, hset, hlcm, Nat.cast_mul, mul_comm] using hcount

#print axioms coprimeCRTIntervalCount_error

private theorem gcd_dvd_of_crt_conditions
    (d q : ℕ) (a n : ℤ)
    (hdn : (d : ℤ) ∣ n) (hna : n ≡ a [ZMOD (q : ℤ)]) :
    (Nat.gcd d q : ℤ) ∣ a := by
  have hgd : (Nat.gcd d q : ℤ) ∣ (d : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_left d q
  have hgq : (Nat.gcd d q : ℤ) ∣ (q : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_right d q
  have hgn : (Nat.gcd d q : ℤ) ∣ n := hgd.trans hdn
  have hgaSub : (Nat.gcd d q : ℤ) ∣ a - n := hgq.trans (Int.modEq_iff_dvd.mp hna)
  have hga : (Nat.gcd d q : ℤ) ∣ (a - n) + n := dvd_add hgaSub hgn
  convert hga using 1 <;> ring

private theorem exists_crt_residue_general
    (d q : ℕ) (a : ℤ) (hq : 0 < q)
    (hg : (Nat.gcd d q : ℤ) ∣ a) :
    ∃ r : ℤ, (d : ℤ) ∣ r ∧ r ≡ a [ZMOD (q : ℤ)] := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  let a₀ : ℕ := Int.toNat (a % (q : ℤ))
  have ha₀ : (a₀ : ℤ) = a % (q : ℤ) := by
    dsimp [a₀]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hqZ)
  have hgq : (Nat.gcd d q : ℤ) ∣ (q : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_right d q
  have hgaSub : (Nat.gcd d q : ℤ) ∣ a - a % (q : ℤ) :=
    hgq.trans (Int.modEq_iff_dvd.mp (Int.mod_modEq a (q : ℤ)))
  have hga₀Z : (Nat.gcd d q : ℤ) ∣ (a₀ : ℤ) := by
    rw [ha₀]
    have h := dvd_sub hg hgaSub
    convert h using 1 <;> ring
  have hga₀ : Nat.gcd d q ∣ a₀ := by
    exact Int.natCast_dvd_natCast.mp hga₀Z
  have hcompat : (0 : ℕ) ≡ a₀ [MOD Nat.gcd d q] :=
    (Nat.modEq_zero_iff_dvd.mpr hga₀).symm
  let r₀ : ℕ := (Nat.chineseRemainder' hcompat).val
  have hr₀d : r₀ ≡ 0 [MOD d] := (Nat.chineseRemainder' hcompat).property.1
  have hr₀q : r₀ ≡ a₀ [MOD q] := (Nat.chineseRemainder' hcompat).property.2
  refine ⟨r₀, ?_, ?_⟩
  · have hr₀dZ : (r₀ : ℤ) ≡ 0 [ZMOD (d : ℤ)] := by exact_mod_cast hr₀d
    exact Int.modEq_zero_iff_dvd.mp hr₀dZ
  · have hr₀qZ : (r₀ : ℤ) ≡ (a₀ : ℤ) [ZMOD (q : ℤ)] := by
      exact_mod_cast hr₀q
    calc
      (r₀ : ℤ) ≡ (a₀ : ℤ) [ZMOD (q : ℤ)] := hr₀qZ
      _ = a % (q : ℤ) := ha₀
      _ ≡ a [ZMOD (q : ℤ)] := Int.mod_modEq a (q : ℤ)

/-- Exact arbitrary-gcd CRT interval count (`lup:crt-count`). The count is
zero when the gcd compatibility condition fails; otherwise it differs from
the interval length divided by the lcm by at most one. Integer points are
represented by the strict-lower/inclusive-upper real interval `(X, X + H]`.
-/
theorem crtIntervalCount
    (X H : ℝ) (d q : ℕ) (a : ℤ)
    (hH : 0 < H) (hd : 0 < d) (hq : 0 < q) :
    (if (Nat.gcd d q : ℤ) ∣ a then
      |(((Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
          (fun n : ℤ => (d : ℤ) ∣ n ∧ n ≡ a [ZMOD (q : ℤ)])).card : ℝ) -
          H / (Nat.lcm d q : ℝ)| ≤ 1
     else
      ((Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
        (fun n : ℤ => (d : ℤ) ∣ n ∧ n ≡ a [ZMOD (q : ℤ)])).card = 0) := by
  let I : Finset ℤ := Finset.Ioc (Int.floor X) (Int.floor (X + H))
  let S : Finset ℤ := I.filter
    (fun n : ℤ => (d : ℤ) ∣ n ∧ n ≡ a [ZMOD (q : ℤ)])
  by_cases hg : (Nat.gcd d q : ℤ) ∣ a
  · simp only [if_pos hg]
    obtain ⟨r, hrd, hra⟩ := exists_crt_residue_general d q a hq hg
    have hIntLcm : (d : ℤ).lcm (q : ℤ) = (Nat.lcm d q : ℤ) := by
      simp [Int.lcm_def]
    have hLcmPos : 0 < (Nat.lcm d q : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (Nat.lcm_ne_zero (Nat.ne_of_gt hd) (Nat.ne_of_gt hq))
    have hset : S = I.filter
        (fun n : ℤ => n ≡ r [ZMOD ((d : ℤ).lcm (q : ℤ))]) := by
      ext n
      simp only [S, Finset.mem_filter]
      constructor
      · rintro ⟨hnI, hdn, hna⟩
        have hnD : n ≡ 0 [ZMOD (d : ℤ)] := Int.modEq_zero_iff_dvd.mpr hdn
        have hrD : r ≡ 0 [ZMOD (d : ℤ)] := Int.modEq_zero_iff_dvd.mpr hrd
        have hnrd : n ≡ r [ZMOD (d : ℤ)] := hnD.trans hrD.symm
        have hnrq : n ≡ r [ZMOD (q : ℤ)] := hna.trans hra.symm
        exact ⟨hnI, (Int.modEq_and_modEq_iff_modEq_lcm).mp ⟨hnrd, hnrq⟩⟩
      · intro hnr
        rcases hnr with ⟨hnI, hnr⟩
        have hdL : (d : ℤ) ∣ (d : ℤ).lcm (q : ℤ) := Int.dvd_lcm_left _ _
        have hqL : (q : ℤ) ∣ (d : ℤ).lcm (q : ℤ) := Int.dvd_lcm_right _ _
        have hnrD : n ≡ r [ZMOD (d : ℤ)] := Int.ModEq.of_dvd hdL hnr
        have hnrq : n ≡ r [ZMOD (q : ℤ)] := Int.ModEq.of_dvd hqL hnr
        have hrD : r ≡ 0 [ZMOD (d : ℤ)] := Int.modEq_zero_iff_dvd.mpr hrd
        have hnD : n ≡ 0 [ZMOD (d : ℤ)] := hnrD.trans hrD
        have hna : n ≡ a [ZMOD (q : ℤ)] := hnrq.trans hra
        exact ⟨hnI, Int.modEq_zero_iff_dvd.mp hnD, hna⟩
    have hinterval := realIntervalResidueCount_error X H
      ((d : ℤ).lcm (q : ℤ)) r hH.le (by rw [hIntLcm]; exact_mod_cast hLcmPos)
    have hLcmCast : (( (d : ℤ).lcm (q : ℤ) : ℤ) : ℝ) =
        (Nat.lcm d q : ℝ) := by rw [hIntLcm]; norm_cast
    have hbound :
        |((I.filter (fun n : ℤ => n ≡ r [ZMOD ((d : ℤ).lcm (q : ℤ))])).card : ℝ) -
            H / (Nat.lcm d q : ℝ)| ≤ 1 := by
      rw [← hLcmCast]
      exact hinterval
    have hboundS : |(S.card : ℝ) - H / (Nat.lcm d q : ℝ)| ≤ 1 := by
      rw [hset]
      exact hbound
    simpa [S, I] using hboundS
  · simp only [if_neg hg]
    have hSempty : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      change n ∈ I.filter
        (fun n : ℤ => (d : ℤ) ∣ n ∧ n ≡ a [ZMOD (q : ℤ)]) at hn
      rcases Finset.mem_filter.mp hn with ⟨_, ⟨hdn, hna⟩⟩
      exact hg (gcd_dvd_of_crt_conditions d q a n hdn hna)
    simpa [S, I] using congrArg Finset.card hSempty

#print axioms crtIntervalCount

end FractionalPrimes.Literature.LongArithmetic

namespace FractionalPrimes.Literature.Polynomial

/-- Blueprint-named entry point for the exact arbitrary-gcd CRT interval count. -/
theorem crtIntervalCount
    (X H : ℝ) (d q : ℕ) (a : ℤ)
    (hH : 0 < H) (hd : 0 < d) (hq : 0 < q) :
    (if (Nat.gcd d q : ℤ) ∣ a then
      |(((Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
          (fun n : ℤ => (d : ℤ) ∣ n ∧ n ≡ a [ZMOD (q : ℤ)])).card : ℝ) -
          H / (Nat.lcm d q : ℝ)| ≤ 1
     else
      ((Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
        (fun n : ℤ => (d : ℤ) ∣ n ∧ n ≡ a [ZMOD (q : ℤ)])).card = 0) := by
  exact FractionalPrimes.Literature.LongArithmetic.crtIntervalCount
    X H d q a hH hd hq

#print axioms crtIntervalCount

end FractionalPrimes.Literature.Polynomial

end
