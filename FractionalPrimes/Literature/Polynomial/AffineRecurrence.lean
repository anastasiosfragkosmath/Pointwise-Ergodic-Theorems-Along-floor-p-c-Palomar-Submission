module

public import FractionalPrimes.ArithmeticBasicsCore

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- The nearest-integer distance is the absolute value of the project's
half-open centered representative. -/
theorem realDistanceToIntegers_eq_abs_centered (x : ℝ) :
    realDistanceToIntegers x = |centeredFrequency x| := by
  calc
    realDistanceToIntegers x =
        realDistanceToIntegers
          (centeredFrequency x + (Int.floor (x + 1 / 2) : ℝ)) := by
      congr 1
      unfold centeredFrequency
      ring
    _ = realDistanceToIntegers (centeredFrequency x) :=
      realDistanceToIntegers_add_int _ _
    _ = |centeredFrequency x| :=
      realDistanceToIntegers_eq_abs_of_abs_le_half
        (abs_le.mpr ⟨(centeredFrequency_mem x).1,
          le_of_lt (centeredFrequency_mem x).2⟩)

private theorem exists_int_sign_distance_decomposition (x : ℝ) :
    ∃ k : ℤ, ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
      x - (k : ℝ) = σ * realDistanceToIntegers x := by
  let c := centeredFrequency x
  have hcabs : |c| = realDistanceToIntegers x := by
    simpa [c] using (realDistanceToIntegers_eq_abs_centered x).symm
  have hcent : x - (Int.floor (x + 1 / 2) : ℝ) = c := by
    dsimp [c, centeredFrequency]
  by_cases hc : 0 ≤ c
  · have hceq : c = realDistanceToIntegers x := by
      rw [abs_of_nonneg hc] at hcabs
      exact hcabs
    refine ⟨Int.floor (x + 1 / 2), 1, Or.inr rfl, ?_⟩
    rw [hcent, hceq]
    ring
  · have hcneg : c < 0 := lt_of_not_ge hc
    have hceq : c = -realDistanceToIntegers x := by
      rw [abs_of_neg hcneg] at hcabs
      linarith
    refine ⟨Int.floor (x + 1 / 2), -1, Or.inl rfl, ?_⟩
    rw [hcent, hceq]
    ring

private theorem realDistanceToIntegers_add_nat_mul_int
    (x s : ℝ) (k : ℕ) (m : ℤ) :
    realDistanceToIntegers (x + (k : ℝ) * ((m : ℝ) + s)) =
      realDistanceToIntegers (x + (k : ℝ) * s) := by
  have harg :
      x + (k : ℝ) * ((m : ℝ) + s) =
        (x + (k : ℝ) * s) + ((k : ℤ) * m : ℝ) := by
    push_cast
    ring
  rw [harg]
  simpa only [Int.cast_mul, Int.cast_natCast] using
    realDistanceToIntegers_add_int (x + (k : ℝ) * s) (k * m)

private theorem realDistanceToIntegers_affineResidueStep
    (α β : ℝ) (b q k : ℕ) (m : ℤ) (s : ℝ)
    (hstep : (q : ℝ) * α = (m : ℝ) + s) :
    realDistanceToIntegers (α * ((b + k * q : ℕ) : ℝ) + β) =
      realDistanceToIntegers (α * (b : ℝ) + β + (k : ℝ) * s) := by
  have hphase :
      α * ((b + k * q : ℕ) : ℝ) + β =
        (α * (b : ℝ) + β) + (k : ℝ) * ((q : ℝ) * α) := by
    push_cast
    ring
  rw [hphase, hstep]
  exact realDistanceToIntegers_add_nat_mul_int (α * (b : ℝ) + β) s k m

private theorem affineRecurrence_zero_step_bound
    {N : ℕ} {δ ε θ : ℝ} (hε : 0 ≤ ε) (hθ : θ = 0) :
    θ ≤ 16 * ε / (δ ^ 2 * (N : ℝ)) := by
  rw [hθ]
  positivity

/-- A phase within `ε` of the integer lattice has an actual integer
representative within `ε`. -/
theorem exists_int_abs_sub_le_of_realDistanceToIntegers_le
    {x ε : ℝ} (hε : realDistanceToIntegers x ≤ ε) :
    ∃ k : ℤ, |x - (k : ℝ)| ≤ ε := by
  refine ⟨Int.floor (x + 1 / 2), ?_⟩
  rw [realDistanceToIntegers_eq_abs_centered] at hε
  simpa [centeredFrequency] using hε

private theorem realDistanceToIntegers_natGap_le
    {a b : ℕ} {α β ε : ℝ} (hab : a < b)
    (ha : realDistanceToIntegers (α * (a : ℝ) + β) ≤ ε)
    (hb : realDistanceToIntegers (α * (b : ℝ) + β) ≤ ε) :
    realDistanceToIntegers (((b - a : ℕ) : ℝ) * α) ≤ 2 * ε := by
  obtain ⟨ka, hka⟩ := exists_int_abs_sub_le_of_realDistanceToIntegers_le ha
  obtain ⟨kb, hkb⟩ := exists_int_abs_sub_le_of_realDistanceToIntegers_le hb
  have hphase :
      ((b - a : ℕ) : ℝ) * α - ((kb - ka : ℤ) : ℝ) =
        (α * (b : ℝ) + β - (kb : ℝ)) -
          (α * (a : ℝ) + β - (ka : ℝ)) := by
    rw [Nat.cast_sub hab.le]
    push_cast
    ring
  have happrox :
      |((b - a : ℕ) : ℝ) * α - ((kb - ka : ℤ) : ℝ)| ≤ 2 * ε := by
    rw [hphase]
    apply abs_le.mpr
    constructor <;> have ha' := abs_le.mp hka <;>
      have hb' := abs_le.mp hkb <;> linarith
  have hmem : ((kb - ka : ℤ) : ℝ) ∈ Set.range fun z : ℤ => (z : ℝ) :=
    ⟨kb - ka, rfl⟩
  have hdist :
      realDistanceToIntegers (((b - a : ℕ) : ℝ) * α) ≤
        |((b - a : ℕ) : ℝ) * α - ((kb - ka : ℤ) : ℝ)| := by
    unfold realDistanceToIntegers
    calc
      Metric.infDist (((b - a : ℕ) : ℝ) * α)
          (Set.range fun z : ℤ => (z : ℝ)) ≤
        dist (((b - a : ℕ) : ℝ) * α) ((kb - ka : ℤ) : ℝ) :=
          Metric.infDist_le_dist_of_mem
            (x := (((b - a : ℕ) : ℝ) * α)) hmem
      _ = |((b - a : ℕ) : ℝ) * α - ((kb - ka : ℤ) : ℝ)| := by
        rw [Real.dist_eq]
  exact hdist.trans happrox

private theorem nat_sub_gap_lt_of_quotient_eq {a b K : ℕ}
    (hK : 0 < K) (ha : 1 ≤ a)
    (hab : (a - 1) / K = (b - 1) / K) (hlt : a < b) :
    b - a < K := by
  have hb : 1 ≤ b := by omega
  have hdivA : (a - 1) / K * K + (a - 1) % K = a - 1 :=
    by simpa [Nat.mul_comm] using Nat.div_add_mod (a - 1) K
  have hdivB₀ : (b - 1) / K * K + (b - 1) % K = b - 1 :=
    by simpa [Nat.mul_comm] using Nat.div_add_mod (b - 1) K
  have hdivB : (a - 1) / K * K + (b - 1) % K = b - 1 := by
    rw [hab]
    exact hdivB₀
  have hmodA : (a - 1) % K < K := Nat.mod_lt _ hK
  have hmodB : (b - 1) % K < K := Nat.mod_lt _ hK
  omega

/-- The integer selected by the centered floor realizes the nearest-integer
distance used by the progression-counting argument. -/
private theorem abs_sub_centeredFloor_eq_realDistance (x : ℝ) :
    |x - (Int.floor (x + 1 / 2) : ℝ)| = realDistanceToIntegers x := by
  rw [realDistanceToIntegers_eq_abs_centered, centeredFrequency]

/-- Within one fixed integer-centered interval, a real progression with
nonzero step magnitude `θ` has at most `2ε/θ+1` terms. -/
private theorem arithmeticProgressionFiberCard_le
    {x c θ ε : ℝ} (hθ : 0 < θ) (hc : |c| = θ) (hε : 0 ≤ ε)
    (T : Finset ℕ) (hT : T.Nonempty) (j : ℤ)
    (hcenter : ∀ k ∈ T,
      |x + (k : ℝ) * c - (j : ℝ)| ≤ ε) :
    (T.card : ℝ) ≤ 2 * ε / θ + 1 := by
  classical
  let k₀ := T.min' hT
  let k₁ := T.max' hT
  have hk₀ : k₀ ∈ T := by simpa [k₀] using Finset.min'_mem T hT
  have hk₁ : k₁ ∈ T := by simpa [k₁] using Finset.max'_mem T hT
  have hk₀₁ : k₀ ≤ k₁ := by
    exact Finset.min'_le T k₁ hk₁
  have hTsub : T ⊆ Finset.Icc k₀ k₁ := by
    intro k hk
    rw [Finset.mem_Icc]
    exact ⟨Finset.min'_le T k hk, Finset.le_max' T k hk⟩
  have hcardNat : T.card ≤ k₁ - k₀ + 1 := by
    calc
      T.card ≤ (Finset.Icc k₀ k₁).card := Finset.card_le_card hTsub
      _ = k₁ + 1 - k₀ := by simp
      _ = k₁ - k₀ + 1 := by omega
  have hcardReal : (T.card : ℝ) ≤ (k₁ : ℝ) - (k₀ : ℝ) + 1 := by
    calc
      (T.card : ℝ) ≤ ((k₁ - k₀ + 1 : ℕ) : ℝ) := by exact_mod_cast hcardNat
      _ = (k₁ : ℝ) - (k₀ : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hk₀₁]
  have hphase :
      |(x + (k₁ : ℝ) * c) - (x + (k₀ : ℝ) * c)| ≤ 2 * ε := by
    have hu := hcenter k₁ hk₁
    have hv := hcenter k₀ hk₀
    have hdiff :
        (x + (k₁ : ℝ) * c) - (x + (k₀ : ℝ) * c) =
          (x + (k₁ : ℝ) * c - (j : ℝ)) -
            (x + (k₀ : ℝ) * c - (j : ℝ)) := by ring
    rw [hdiff]
    apply abs_le.mpr
    constructor <;> have hu' := abs_le.mp hu <;> have hv' := abs_le.mp hv <;> linarith
  have hphaseEq :
      |(x + (k₁ : ℝ) * c) - (x + (k₀ : ℝ) * c)| =
        ((k₁ - k₀ : ℕ) : ℝ) * θ := by
    have hcast : ((k₁ - k₀ : ℕ) : ℝ) = (k₁ : ℝ) - (k₀ : ℝ) :=
      Nat.cast_sub hk₀₁
    calc
      |(x + (k₁ : ℝ) * c) - (x + (k₀ : ℝ) * c)| =
          |((k₁ : ℝ) - (k₀ : ℝ)) * c| := by congr 1 <;> ring
      _ = |(k₁ : ℝ) - (k₀ : ℝ)| * |c| := abs_mul _ _
      _ = ((k₁ - k₀ : ℕ) : ℝ) * θ := by
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hk₀₁)), hc, ← hcast]
  have hgap : ((k₁ - k₀ : ℕ) : ℝ) * θ ≤ 2 * ε := by
    rw [← hphaseEq]
    exact hphase
  calc
    (T.card : ℝ) ≤ ((k₁ - k₀ : ℕ) : ℝ) + 1 := by
      simpa [Nat.cast_sub hk₀₁] using hcardReal
    _ ≤ 2 * ε / θ + 1 := by
      have hdiv : ((k₁ - k₀ : ℕ) : ℝ) ≤ 2 * ε / θ :=
        (le_div_iff₀ hθ).2 hgap
      linarith

/-- The integer centers whose closed `ε`-neighborhoods can meet `[lo, hi]`
lie in the integer interval from `ceil (lo - ε)` to `floor (hi + ε)`.
When `2ε < 1`, this interval contains at most `hi - lo + 2` centers. -/
private theorem integerCenterInterval_card_le
    {lo hi ε : ℝ} (hlohi : lo ≤ hi) (hε : 0 ≤ ε)
    (h2ε : 2 * ε < 1) :
    ((Finset.Icc (Int.ceil (lo - ε)) (Int.floor (hi + ε))).card : ℝ)
      ≤ hi - lo + 2 := by
  classical
  let a : ℤ := Int.ceil (lo - ε)
  let b : ℤ := Int.floor (hi + ε)
  have hab : a ≤ b + 1 := by
    dsimp [a, b]
    calc
      Int.ceil (lo - ε) ≤ Int.ceil (hi + ε) :=
        Int.ceil_le_ceil (by linarith)
      _ ≤ Int.floor (hi + ε) + 1 := Int.ceil_le_floor_add_one _
  have hcardInt : ((Finset.Icc a b).card : ℤ) = b + 1 - a :=
    Int.card_Icc_of_le (a := a) (b := b) hab
  have hcardReal : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
    exact_mod_cast hcardInt
  have hfloor : (b : ℝ) ≤ hi + ε := by
    dsimp [b]
    exact Int.floor_le _
  have hceil : lo - ε ≤ (a : ℝ) := by
    dsimp [a]
    exact Int.le_ceil _
  change ((Finset.Icc a b).card : ℝ) ≤ hi - lo + 2
  rw [hcardReal]
  nlinarith

/-- In a finite affine progression, only `L * θ + 2` integer centers can be
within `ε` of a term. Each center fiber has at most `2ε/θ + 1` terms, so
the good terms obey the source's center-count times fiber-count bound. -/
private theorem affineProgressionGoodCount_product_bound
    {x c θ ε : ℝ} {L : ℕ} (hL : 0 < L) (hθ : 0 < θ)
    (hc : |c| = θ) (hε : 0 ≤ ε) (h2ε : 2 * ε < 1)
    (G : Finset ℕ) (hG : G ⊆ Finset.range L)
    (hgood : ∀ k ∈ G, realDistanceToIntegers (x + (k : ℝ) * c) ≤ ε) :
    (G.card : ℝ) ≤ ((L : ℝ) * θ + 2) * (2 * ε / θ + 1) := by
  classical
  let t : ℝ := ((L - 1 : ℕ) : ℝ)
  let last : ℝ := x + t * c
  let lo : ℝ := min x last
  let hi : ℝ := max x last
  let f : ℕ → ℤ := fun k => Int.floor (x + (k : ℝ) * c + 1 / 2)
  let J : Finset ℤ := Finset.Icc (Int.ceil (lo - ε)) (Int.floor (hi + ε))
  have ht : 0 ≤ t := by positivity
  have hwidth : hi - lo = t * θ := by
    calc
      hi - lo = |last - x| := by
        dsimp [hi, lo]
        rw [max_sub_min_eq_abs]
      _ = |t * c| := by dsimp [last]; congr 1 <;> ring
      _ = t * θ := by rw [abs_mul, abs_of_nonneg ht, hc]
  have hcenters : (J.card : ℝ) ≤ (L : ℝ) * θ + 2 := by
    have hbase := integerCenterInterval_card_le
      (lo := lo) (hi := hi) (ε := ε) (show lo ≤ hi from min_le_max) hε h2ε
    have htL : t ≤ (L : ℝ) := by
      dsimp [t]
      exact_mod_cast Nat.sub_le L 1
    dsimp [J]
    calc
      ((Finset.Icc (Int.ceil (lo - ε)) (Int.floor (hi + ε))).card : ℝ)
          ≤ hi - lo + 2 := hbase
      _ = t * θ + 2 := by rw [hwidth]
      _ ≤ (L : ℝ) * θ + 2 := by
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right htL hθ.le) 2
  have hphaseRange (k : ℕ) (hk : k ∈ G) :
      lo ≤ x + (k : ℝ) * c ∧ x + (k : ℝ) * c ≤ hi := by
    have hklt : k < L := Finset.mem_range.mp (hG hk)
    have hkn : k ≤ L - 1 := by omega
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hkt : (k : ℝ) ≤ t := by
      dsimp [t]
      exact_mod_cast hkn
    by_cases hc0 : 0 ≤ c
    · have hstart : x ≤ x + (k : ℝ) * c := by
        have := mul_nonneg hk0 hc0
        linarith
      have hend : x + (k : ℝ) * c ≤ last := by
        have := mul_le_mul_of_nonneg_right hkt hc0
        dsimp [last]
        linarith
      exact ⟨(min_le_left _ _).trans hstart,
        hend.trans (le_max_right _ _)⟩
    · have hcneg : c ≤ 0 := le_of_not_ge hc0
      have hstart : x + (k : ℝ) * c ≤ x := by
        have := mul_nonpos_of_nonneg_of_nonpos hk0 hcneg
        linarith
      have hend : last ≤ x + (k : ℝ) * c := by
        have := mul_le_mul_of_nonpos_right hkt hcneg
        dsimp [last]
        linarith
      exact ⟨(min_le_right _ _).trans hend,
        hstart.trans (le_max_left _ _)⟩
  have hmap : ∀ k ∈ G, f k ∈ J := by
    intro k hk
    have hrange := hphaseRange k hk
    have hdist : |x + (k : ℝ) * c - (f k : ℝ)| ≤ ε := by
      calc
        |x + (k : ℝ) * c - (f k : ℝ)| =
            realDistanceToIntegers (x + (k : ℝ) * c) := by
          simpa [f] using abs_sub_centeredFloor_eq_realDistance
            (x + (k : ℝ) * c)
        _ ≤ ε := hgood k hk
    have hlo : lo - ε ≤ (f k : ℝ) := by
      have h := abs_le.mp hdist
      linarith
    have hhi : (f k : ℝ) ≤ hi + ε := by
      have h := abs_le.mp hdist
      linarith
    dsimp [J]
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr hlo, Int.le_floor.mpr hhi⟩
  have hfiber (j : ℤ) (hj : j ∈ J) :
      ((G.filter fun k => f k = j).card : ℝ) ≤ 2 * ε / θ + 1 := by
    let T := G.filter fun k => f k = j
    by_cases hT : T.Nonempty
    · apply arithmeticProgressionFiberCard_le hθ hc hε T hT j
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hdist : |x + (k : ℝ) * c - (f k : ℝ)| ≤ ε := by
        calc
          |x + (k : ℝ) * c - (f k : ℝ)| =
              realDistanceToIntegers (x + (k : ℝ) * c) := by
            simpa [f] using abs_sub_centeredFloor_eq_realDistance
              (x + (k : ℝ) * c)
          _ ≤ ε := hgood k hk'.1
      rw [← hk'.2]
      exact hdist
    · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      simp [T, hTempty]
      positivity
  have hcardEq : G.card = ∑ j ∈ J, (G.filter fun k => f k = j).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  calc
    (G.card : ℝ) = ∑ j ∈ J, ((G.filter fun k => f k = j).card : ℝ) := by
      rw [hcardEq]
      simp
    _ ≤ ∑ j ∈ J, (2 * ε / θ + 1) := by
      exact Finset.sum_le_sum (fun j hj => hfiber j hj)
    _ = (J.card : ℝ) * (2 * ε / θ + 1) := by simp [mul_comm]; ring
    _ ≤ ((L : ℝ) * θ + 2) * (2 * ε / θ + 1) := by
      exact mul_le_mul_of_nonneg_right hcenters (by positivity)

/-- Using `θ ≤ 2ε` in the center-count/fiber-count product gives the
residue-class estimate from the affine recurrence argument. -/
private theorem affineProgressionGoodCount_le
    {x c θ ε : ℝ} {L : ℕ} (hL : 0 < L) (hθ : 0 < θ)
    (hc : |c| = θ) (hε : 0 ≤ ε) (hθε : θ ≤ 2 * ε)
    (h2ε : 2 * ε < 1) (G : Finset ℕ) (hG : G ⊆ Finset.range L)
    (hgood : ∀ k ∈ G, realDistanceToIntegers (x + (k : ℝ) * c) ≤ ε) :
    (G.card : ℝ) ≤ 4 * ε * (L : ℝ) + 4 * ε / θ + 2 := by
  have hproduct := affineProgressionGoodCount_product_bound
    hL hθ hc hε h2ε G hG hgood
  have halg :
      ((L : ℝ) * θ + 2) * (2 * ε / θ + 1) =
        2 * ε * (L : ℝ) + (L : ℝ) * θ + 4 * ε / θ + 2 := by
    field_simp [ne_of_gt hθ]
    ring
  have hterm : (L : ℝ) * θ ≤ 2 * ε * (L : ℝ) := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right hθε (show (0 : ℝ) ≤ (L : ℝ) by positivity))
  calc
    (G.card : ℝ) ≤ ((L : ℝ) * θ + 2) * (2 * ε / θ + 1) := hproduct
    _ = 2 * ε * (L : ℝ) + (L : ℝ) * θ + 4 * ε / θ + 2 := halg
    _ ≤ 4 * ε * (L : ℝ) + 4 * ε / θ + 2 := by nlinarith [hterm]

private def affineResidueClass (N q r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => n % q = r

private def affineResidueBase (q r : ℕ) : ℕ :=
  if r = 0 then q else r

private def affineResidueLength (N q r : ℕ) : ℕ :=
  (N - affineResidueBase q r) / q + 1

private theorem affineResidueBase_le_of_mem {N q r n : ℕ}
    (hn : n ∈ affineResidueClass N q r) : affineResidueBase q r ≤ n := by
  rcases Finset.mem_filter.mp hn with ⟨hnI, hnr⟩
  have hnpos : 0 < n := by
    have hnI' := Finset.mem_Icc.mp hnI
    omega
  by_cases hr0 : r = 0
  · have hnmod : n % q = 0 := by simpa [hr0] using hnr
    have hdiv : q ∣ n := Nat.dvd_of_mod_eq_zero hnmod
    simpa [affineResidueBase, hr0] using (Nat.le_of_dvd hnpos hdiv)
  · have hbase : affineResidueBase q r = r := by
      simp [affineResidueBase, hr0]
    rw [hbase]
    calc
      r = n % q := hnr.symm
      _ ≤ n := Nat.mod_le _ _

private theorem affineResidueBase_le_of_nonempty {N q r : ℕ}
    (hC : (affineResidueClass N q r).Nonempty) : affineResidueBase q r ≤ N := by
  obtain ⟨n, hn⟩ := hC
  have hnI : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn).1
  exact (affineResidueBase_le_of_mem hn).trans (Finset.mem_Icc.mp hnI).2

private theorem affineResidueBase_mod (q r : ℕ) (hr : r < q) :
    affineResidueBase q r % q = r := by
  by_cases hr0 : r = 0
  · simp [affineResidueBase, hr0]
  · simp [affineResidueBase, hr0, Nat.mod_eq_of_lt hr]

private theorem affineResidueClass_eq_range_image
    {N q r : ℕ} (hq : 0 < q) (hr : r < q)
    (hC : (affineResidueClass N q r).Nonempty) :
    affineResidueClass N q r =
      (Finset.range (affineResidueLength N q r)).image
        (fun k => affineResidueBase q r + k * q) := by
  classical
  let b := affineResidueBase q r
  have hbN : b ≤ N := affineResidueBase_le_of_nonempty hC
  have hbpos : 0 < b := by
    by_cases hr0 : r = 0
    · simpa [b, affineResidueBase, hr0] using hq
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      simpa [b, affineResidueBase, hr0] using hrpos
  have hbmod : b % q = r := by
    simpa [b] using affineResidueBase_mod q r hr
  have hb_le_mem : ∀ {n : ℕ}, n ∈ affineResidueClass N q r → b ≤ n := by
    intro n hn
    simpa [b] using affineResidueBase_le_of_mem hn
  ext n
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hnr⟩
    have hbn : b ≤ n := hb_le_mem hn
    have hmod : b ≡ n [MOD q] := by
      change b % q = n % q
      rw [hbmod, hnr]
    obtain ⟨k, hEq⟩ := (Nat.modEq_iff_exists_eq_add hbn).mp hmod
    have hsum : b + k * q ≤ N := by
      calc
        b + k * q = n := by simpa [Nat.mul_comm] using hEq.symm
        _ ≤ N := (Finset.mem_Icc.mp hnI).2
    have hprod : k * q ≤ N - b := by
      apply (Nat.add_le_add_iff_left).mp
      calc
        b + k * q ≤ N := hsum
        _ = b + (N - b) := (Nat.add_sub_cancel' hbN).symm
    have hk : k ≤ (N - b) / q :=
      (Nat.le_div_iff_mul_le hq).2 hprod
    have hkRange : k ∈ Finset.range (affineResidueLength N q r) := by
      apply Finset.mem_range.mpr
      change k < (N - b) / q + 1
      omega
    apply Finset.mem_image.mpr
    refine ⟨k, hkRange, ?_⟩
    simpa [b, Nat.mul_comm] using hEq.symm
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    have hkbound : k ≤ (N - b) / q := by
      have hk' : k < (N - b) / q + 1 := by
        simpa [affineResidueLength, b] using hk
      omega
    have hprod : k * q ≤ N - b :=
      (Nat.le_div_iff_mul_le hq).mp hkbound
    have hupper : b + k * q ≤ N := by
      calc
        b + k * q ≤ b + (N - b) := Nat.add_le_add_left hprod b
        _ = N := Nat.add_sub_cancel' hbN
    have hres : (b + k * q) % q = r := by
      rw [Nat.mul_comm k q, Nat.add_mul_mod_self_left, hbmod]
    apply Finset.mem_filter.mpr
    refine ⟨?_, hres⟩
    rw [Finset.mem_Icc]
    exact ⟨le_trans (Nat.succ_le_iff.mpr hbpos) (Nat.le_add_right b (k * q)), hupper⟩

private theorem affineResidueGoodCount_le
    {N q r : ℕ} {α β c θ ε : ℝ}
    (hq : 0 < q) (hr : r < q)
    (hC : (affineResidueClass N q r).Nonempty)
    (hθ : 0 < θ) (hc : |c| = θ)
    (hε : 0 ≤ ε) (hθε : θ ≤ 2 * ε) (h2ε : 2 * ε < 1)
    (m : ℤ) (hstep : (q : ℝ) * α = (m : ℝ) + c) :
    (((affineResidueClass N q r).filter (fun n : ℕ =>
      realDistanceToIntegers (α * (n : ℝ) + β) ≤ ε)).card : ℝ) ≤
      4 * ε * ((affineResidueClass N q r).card : ℝ) + 4 * ε / θ + 2 := by
  classical
  let b := affineResidueBase q r
  let L := affineResidueLength N q r
  let f : ℕ → ℕ := fun k => b + k * q
  let good : ℕ → Prop := fun n =>
    realDistanceToIntegers (α * (n : ℝ) + β) ≤ ε
  let G : Finset ℕ := (Finset.range L).filter fun k => good (f k)
  have hImage : affineResidueClass N q r = (Finset.range L).image f := by
    simpa [b, L, f] using affineResidueClass_eq_range_image hq hr hC
  have hInjective : Function.Injective f := by
    intro k l hkl
    change b + k * q = b + l * q at hkl
    exact Nat.mul_right_cancel hq (Nat.add_left_cancel hkl)
  have hLpos : 0 < L := by
    dsimp [L, affineResidueLength]
    exact Nat.succ_pos _
  have hFilteredImage :
      (affineResidueClass N q r).filter good = G.image f := by
    rw [hImage]
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, G]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hgood⟩
      exact ⟨k, ⟨hk, hgood⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hgood⟩, rfl⟩
      exact ⟨⟨k, hk, rfl⟩, hgood⟩
  have hInjOn : Set.InjOn f G := by
    intro k hk l hl hkl
    exact hInjective hkl
  have hGoodCard :
      ((affineResidueClass N q r).filter good).card = G.card := by
    rw [hFilteredImage]
    exact Finset.card_image_iff.mpr hInjOn
  have hClassCard : (affineResidueClass N q r).card = L := by
    rw [hImage]
    have hImageCard :
        ((Finset.range L).image f).card = (Finset.range L).card :=
      Finset.card_image_iff.mpr (by
        intro k hk l hl hkl
        exact hInjective hkl)
    simpa [Finset.card_range] using hImageCard
  have hProgressionGood :
      ∀ k ∈ G,
        realDistanceToIntegers (α * (b : ℝ) + β + (k : ℝ) * c) ≤ ε := by
    intro k hk
    have hgoodk : good (f k) := (Finset.mem_filter.mp hk).2
    have hphase := realDistanceToIntegers_affineResidueStep
      α β b q k m c hstep
    change realDistanceToIntegers (α * (f k : ℝ) + β) ≤ ε at hgoodk
    rw [← hphase]
    exact hgoodk
  have hProgressionBound :
      (G.card : ℝ) ≤ 4 * ε * (L : ℝ) + 4 * ε / θ + 2 :=
    affineProgressionGoodCount_le hLpos hθ hc hε hθε h2ε G
      (Finset.filter_subset _ _) hProgressionGood
  calc
    (((affineResidueClass N q r).filter good).card : ℝ) =
        (G.card : ℝ) := by exact_mod_cast hGoodCard
    _ ≤ 4 * ε * (L : ℝ) + 4 * ε / θ + 2 := hProgressionBound
    _ = 4 * ε * ((affineResidueClass N q r).card : ℝ) +
        4 * ε / θ + 2 := by rw [← hClassCard]

private def affineOccupiedResidues (N q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun r => (affineResidueClass N q r).Nonempty

/-- The residue fibers modulo a positive `q` partition `[1,N]`, so their
cardinalities sum exactly to `N`. -/
private theorem affineResidueClass_card_sum_eq {N q : ℕ} (hq : 0 < q) :
    ∑ r ∈ Finset.range q, (affineResidueClass N q r).card = N := by
  classical
  have hmap : ∀ n ∈ Finset.Icc 1 N, n % q ∈ Finset.range q := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.mod_lt n hq)
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  calc
    ∑ r ∈ Finset.range q, (affineResidueClass N q r).card =
        (Finset.Icc 1 N).card := by
      symm
      simpa [affineResidueClass] using hcard
    _ = N := by simp [Nat.card_Icc]

/-- There are at most `q` nonempty residue classes modulo `q`. -/
private theorem affineOccupiedResidues_card_le (N q : ℕ) :
    (affineOccupiedResidues N q).card ≤ q := by
  calc
    (affineOccupiedResidues N q).card ≤ (Finset.range q).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = q := Finset.card_range q

/-- Restricting the exact residue-fiber sum to occupied classes does not
change the total interval length. -/
private theorem affineOccupiedResidueClass_card_sum_eq {N q : ℕ}
    (hq : 0 < q) :
    ∑ r ∈ affineOccupiedResidues N q, (affineResidueClass N q r).card = N := by
  classical
  calc
    ∑ r ∈ affineOccupiedResidues N q, (affineResidueClass N q r).card =
        ∑ r ∈ Finset.range q, (affineResidueClass N q r).card := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r hr hrnot
      have hnot : ¬ (affineResidueClass N q r).Nonempty := by
        intro hne
        exact hrnot (Finset.mem_filter.mpr ⟨hr, hne⟩)
      have hempty : affineResidueClass N q r = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnot
      simp [hempty]
    _ = N := affineResidueClass_card_sum_eq hq

/-- Summing the source's per-class count over the occupied residue classes
gives its exact global error term. -/
private theorem affineResidueBounds_aggregate
    {N q : ℕ} {ε θ : ℝ} (hq : 0 < q)
    (hε : 0 ≤ ε) (hθ : 0 < θ)
    (B : ℕ → ℕ)
    (hB : ∀ r ∈ affineOccupiedResidues N q,
      (B r : ℝ) ≤
        4 * ε * ((affineResidueClass N q r).card : ℝ) + 4 * ε / θ + 2) :
    ∑ r ∈ affineOccupiedResidues N q, (B r : ℝ) ≤
      4 * ε * (N : ℝ) + 4 * (q : ℝ) * ε / θ + 2 * (q : ℝ) := by
  classical
  let R := affineOccupiedResidues N q
  let C : ℝ := 4 * ε / θ + 2
  have hlenNat : ∑ r ∈ R, (affineResidueClass N q r).card = N := by
    simpa [R] using affineOccupiedResidueClass_card_sum_eq hq
  have hlenReal :
      ∑ r ∈ R, ((affineResidueClass N q r).card : ℝ) = (N : ℝ) := by
    calc
      ∑ r ∈ R, ((affineResidueClass N q r).card : ℝ) =
          ((∑ r ∈ R, (affineResidueClass N q r).card : ℕ) : ℝ) := by simp
      _ = (N : ℝ) := by rw [hlenNat]
  have hRcard : (R.card : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast affineOccupiedResidues_card_le N q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    ∑ r ∈ R, (B r : ℝ) ≤
        ∑ r ∈ R,
          (4 * ε * ((affineResidueClass N q r).card : ℝ) + C) := by
      apply Finset.sum_le_sum
      intro r hr
      simpa [C, add_assoc] using hB r hr
    _ = 4 * ε *
          (∑ r ∈ R, ((affineResidueClass N q r).card : ℝ)) +
        (R.card : ℝ) * C := by
      simp [Finset.sum_add_distrib, Finset.mul_sum, C, mul_comm]
      ring
    _ ≤ 4 * ε * (N : ℝ) + (q : ℝ) * C := by
      rw [hlenReal]
      simpa [add_comm] using
        add_le_add_right (mul_le_mul_of_nonneg_right hRcard hC)
          (4 * ε * (N : ℝ))
    _ = 4 * ε * (N : ℝ) + 4 * (q : ℝ) * ε / θ + 2 * (q : ℝ) := by
      dsimp [C]
      ring

/-- The exact final numerical step in the affine recurrence argument.  The
per-residue estimates and the density lower bound force the positive step
distance to satisfy the source's stated bound. -/
private theorem affineThetaBound_of_residueCounts
    {N q : ℕ} {δ ε θ : ℝ}
    (hδ : 0 < δ) (hεupper : ε ≤ δ / 16)
    (hN : 16 * (δ⁻¹)^2 ≤ (N : ℝ))
    (hq : 0 < q) (hqUpper : (q : ℝ) ≤ 2 / δ)
    (hθ : 0 < θ) (hθε : θ ≤ 2 * ε)
    (B : ℕ → ℕ)
    (hB : ∀ r ∈ affineOccupiedResidues N q,
      (B r : ℝ) ≤
        4 * ε * ((affineResidueClass N q r).card : ℝ) +
          4 * ε / θ + 2)
    (hcount : δ * (N : ℝ) ≤
      ∑ r ∈ affineOccupiedResidues N q, (B r : ℝ)) :
    θ ≤ 16 * ε / (δ ^ 2 * (N : ℝ)) := by
  have hε : 0 ≤ ε := by linarith
  have hNpos : 0 < (N : ℝ) := by
    exact lt_of_lt_of_le (by positivity) hN
  have hδNpos : 0 < δ * (N : ℝ) := mul_pos hδ hNpos
  have hδNlarge : 16 / δ ≤ δ * (N : ℝ) := by
    calc
      16 / δ = δ * (16 * (δ⁻¹)^2) := by
        field_simp [ne_of_gt hδ] <;> ring
      _ ≤ δ * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
  have hεCoeff : 4 * ε ≤ δ / 4 := by nlinarith
  have hεN : 4 * ε * (N : ℝ) ≤ δ * (N : ℝ) / 4 := by
    calc
      4 * ε * (N : ℝ) = (4 * ε) * (N : ℝ) := by ring
      _ ≤ (δ / 4) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hεCoeff hNpos.le
      _ = δ * (N : ℝ) / 4 := by ring
  have h2q : 2 * (q : ℝ) ≤ 4 / δ := by
    calc
      2 * (q : ℝ) ≤ 2 * (2 / δ) :=
        mul_le_mul_of_nonneg_left hqUpper (by norm_num)
      _ = 4 / δ := by ring
  have h4over : 4 / δ ≤ δ * (N : ℝ) / 4 := by
    calc
      4 / δ = (16 / δ) / 4 := by ring
      _ ≤ δ * (N : ℝ) / 4 :=
        div_le_div_of_nonneg_right hδNlarge (by norm_num)
  have h2qN : 2 * (q : ℝ) ≤ δ * (N : ℝ) / 4 :=
    le_trans h2q h4over
  have hmiddle : δ * (N : ℝ) / 2 ≤ 4 * (q : ℝ) * ε / θ := by
    have hupper := affineResidueBounds_aggregate hq hε hθ B hB
    linarith
  have hcleared : (δ * (N : ℝ) / 2) * θ ≤ 4 * (q : ℝ) * ε :=
    (le_div_iff₀ hθ).mp hmiddle
  have hthetaQ : θ ≤ 8 * (q : ℝ) * ε / (δ * (N : ℝ)) := by
    apply (le_div_iff₀ hδNpos).2
    nlinarith [hcleared]
  have hqε : 8 * (q : ℝ) * ε ≤ 16 * ε / δ := by
    calc
      8 * (q : ℝ) * ε ≤ 8 * (2 / δ) * ε := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqUpper (by norm_num)) hε
      _ = 16 * ε / δ := by ring
  have hthetaQ' :
      8 * (q : ℝ) * ε / (δ * (N : ℝ)) ≤
        16 * ε / (δ ^ 2 * (N : ℝ)) := by
    calc
      8 * (q : ℝ) * ε / (δ * (N : ℝ)) ≤
          (16 * ε / δ) / (δ * (N : ℝ)) :=
        div_le_div_of_nonneg_right hqε hδNpos.le
      _ = 16 * ε / (δ ^ 2 * (N : ℝ)) := by
        field_simp [ne_of_gt hδ, ne_of_gt hNpos] <;> ring
  exact hthetaQ.trans hthetaQ'

/-- A set of density at least `δ` in `[1,N]` contains two points whose
positive gap is at most `2/δ`. This is the short-gap pigeonhole step of
the affine recurrence proof. -/
private theorem exists_pair_gap_le_of_card
    {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hN : 16 * (δ⁻¹)^2 ≤ (N : ℝ)) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 N)
    (hScard : δ * (N : ℝ) ≤ (S.card : ℝ)) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (b - a : ℝ) ≤ 2 / δ := by
  classical
  have hδN : 2 < δ * (N : ℝ) := by
    have hmul : 16 / δ ≤ δ * (N : ℝ) := by
      calc
        16 / δ = δ * (16 * (δ⁻¹)^2) := by
          field_simp [ne_of_gt hδ]
        _ ≤ δ * (N : ℝ) := mul_le_mul_of_nonneg_left hN hδ.le
    have hlarge : 32 < 16 / δ := by
      rw [lt_div_iff₀ hδ]
      nlinarith
    linarith
  let K : ℕ := ⌊2 / δ⌋₊ + 1
  have hKpos : 0 < K := by
    dsimp [K]
    omega
  have hKfloor : (⌊2 / δ⌋₊ : ℝ) ≤ 2 / δ := Nat.floor_le (by positivity)
  have hKlarge : 2 / δ < (K : ℝ) := by
    dsimp [K]
    rw [Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  by_contra hno
  have hsep {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
      K ≤ b - a := by
    have hnot : ¬ ((b - a : ℝ) ≤ 2 / δ) := by
      intro hle
      exact hno ⟨a, ha, b, hb, hab, hle⟩
    have hgap : (⌊2 / δ⌋₊ : ℝ) < (b - a : ℝ) :=
      lt_of_le_of_lt hKfloor (lt_of_not_ge hnot)
    have hgapCast : (⌊2 / δ⌋₊ : ℝ) < ((b - a : ℕ) : ℝ) := by
      rw [Nat.cast_sub hab.le]
      exact hgap
    have hgapNat : ⌊2 / δ⌋₊ < b - a := by exact_mod_cast hgapCast
    dsimp [K]
    omega
  let f : ℕ → ℕ := fun n => (n - 1) / K
  have hf : ∀ n ∈ S, f n ∈ Finset.range (N / K + 1) := by
    intro n hn
    have hnI := hS hn
    have hnBounds : 1 ≤ n ∧ n ≤ N := Finset.mem_Icc.mp hnI
    have hdiv : (n - 1) / K ≤ N / K :=
      Nat.div_le_div_right (by omega)
    exact Finset.mem_range.mpr (by dsimp [f]; omega)
  have hinj : (S : Set ℕ).InjOn f := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgap := hsep ha hb hlt
      have haBounds : 1 ≤ a ∧ a ≤ N := Finset.mem_Icc.mp (hS ha)
      dsimp [f] at hab
      have hstep := nat_sub_gap_lt_of_quotient_eq hKpos haBounds.1 hab hlt
      omega
    · have hgap := hsep hb ha hgt
      have hbBounds : 1 ≤ b ∧ b ≤ N := Finset.mem_Icc.mp (hS hb)
      dsimp [f] at hab
      have hstep := nat_sub_gap_lt_of_quotient_eq hKpos hbBounds.1 hab.symm hgt
      omega
  have hcard : S.card ≤ N / K + 1 := by
    calc
      S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (N / K + 1)).card := Finset.card_le_card (by
        rw [Finset.image_subset_iff]
        exact hf)
      _ = N / K + 1 := Finset.card_range _
  have hupper : (S.card : ℝ) < δ * (N : ℝ) := by
    calc
      (S.card : ℝ) ≤ ((N / K + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = ((N / K : ℕ) : ℝ) + 1 := by simp
      _ ≤ (N : ℝ) / (K : ℝ) + 1 := by
        simpa [add_comm] using add_le_add_right
          (Nat.cast_div_le (α := ℝ) (m := N) (n := K)) 1
      _ < δ * (N : ℝ) := by
        have hKposR : 0 < (K : ℝ) := by exact_mod_cast hKpos
        have hKinv : 1 / (K : ℝ) < δ / 2 := by
          apply (div_lt_iff₀ hKposR).2
          have hδK : 2 < δ * (K : ℝ) := by
            simpa [mul_comm] using (div_lt_iff₀ hδ).mp hKlarge
          nlinarith
        have hNpos : 0 < (N : ℝ) := by
          by_contra hNpos
          have hNle : (N : ℝ) ≤ 0 := not_lt.mp hNpos
          have hmul : δ * (N : ℝ) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hδ.le hNle
          linarith
        have hNdiv : (N : ℝ) / (K : ℝ) < δ * (N : ℝ) / 2 := by
          calc
            (N : ℝ) / (K : ℝ) = (N : ℝ) * (1 / (K : ℝ)) := by ring
            _ < (N : ℝ) * (δ / 2) := mul_lt_mul_of_pos_left hKinv hNpos
            _ = δ * (N : ℝ) / 2 := by ring
        linarith
  exact (not_le_of_gt hupper) hScard

/-- Blueprint `lpi:linear-recurrence`: a set of density at least `δ` in
`[1,N]`, with `N ≥ 16δ⁻²`, forces a small denominator `q` for the slope. -/
theorem affineRecurrence {N : ℕ} (hN : 1 ≤ N)
    {δ ε α β : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hε : 0 ≤ ε) (hεupper : ε ≤ δ / 16)
    (hNlarge : 16 * (δ⁻¹)^2 ≤ (N : ℝ))
    (hgood : δ * (N : ℝ) ≤
      (((Finset.Icc 1 N).filter (fun n : ℕ =>
        realDistanceToIntegers (α * (n : ℝ) + β) ≤ ε)).card : ℝ)) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ 2 / δ ∧
      realDistanceToIntegers ((q : ℝ) * α) ≤
        16 * ε / (δ ^ 2 * (N : ℝ)) := by
  classical
  let good : ℕ → Prop := fun n =>
    realDistanceToIntegers (α * (n : ℝ) + β) ≤ ε
  let S : Finset ℕ := (Finset.Icc 1 N).filter good
  have hSsubset : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hScard : δ * (N : ℝ) ≤ (S.card : ℝ) := by
    simpa [S, good] using hgood
  obtain ⟨a, ha, b, hb, hab, hgap⟩ :=
    exists_pair_gap_le_of_card hδ hδhalf hNlarge S hSsubset hScard
  have hgoodA : realDistanceToIntegers (α * (a : ℝ) + β) ≤ ε :=
    (Finset.mem_filter.mp ha).2
  have hgoodB : realDistanceToIntegers (α * (b : ℝ) + β) ≤ ε :=
    (Finset.mem_filter.mp hb).2
  let q : ℕ := b - a
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.sub_pos_of_lt hab
  have hq : 1 ≤ q := Nat.succ_le_iff.mpr hqpos
  have hqUpper : (q : ℝ) ≤ 2 / δ := by
    dsimp [q]
    rw [Nat.cast_sub hab.le]
    exact hgap
  have hgapDistance :
      realDistanceToIntegers ((q : ℝ) * α) ≤ 2 * ε := by
    simpa [q] using realDistanceToIntegers_natGap_le hab hgoodA hgoodB
  let θ : ℝ := realDistanceToIntegers ((q : ℝ) * α)
  have hθε : θ ≤ 2 * ε := by simpa [θ] using hgapDistance
  have hθnonneg : 0 ≤ θ := by
    dsimp [θ]
    exact Metric.infDist_nonneg
  by_cases hθzero : θ = 0
  · refine ⟨q, hq, hqUpper, ?_⟩
    simpa [θ] using affineRecurrence_zero_step_bound
      (N := N) (δ := δ) (ε := ε) (θ := θ) hε hθzero
  · have hθpos : 0 < θ := lt_of_le_of_ne hθnonneg (Ne.symm hθzero)
    obtain ⟨m, σ, hσ, hdecomp⟩ :=
      exists_int_sign_distance_decomposition ((q : ℝ) * α)
    let c : ℝ := σ * θ
    have hc : |c| = θ := by
      rcases hσ with hσ | hσ
      · subst σ
        simp [c, abs_of_pos hθpos]
      · subst σ
        simp [c, abs_of_pos hθpos]
    have hstep : (q : ℝ) * α = (m : ℝ) + c := by
      have hdecomp' : (q : ℝ) * α - (m : ℝ) = σ * θ := by
        simpa [θ] using hdecomp
      dsimp [c]
      linarith
    have h2ε : 2 * ε < 1 := by
      calc
        2 * ε ≤ 2 * (δ / 16) :=
          mul_le_mul_of_nonneg_left hεupper (by norm_num)
        _ < 1 := by nlinarith [hδhalf]
    let B : ℕ → ℕ := fun r =>
      ((affineResidueClass N q r).filter good).card
    have hB : ∀ r ∈ affineOccupiedResidues N q,
        (B r : ℝ) ≤
          4 * ε * ((affineResidueClass N q r).card : ℝ) +
            4 * ε / θ + 2 := by
      intro r hr
      rcases Finset.mem_filter.mp hr with ⟨hrq, hC⟩
      have hr' : r < q := Finset.mem_range.mp hrq
      dsimp [B]
      exact affineResidueGoodCount_le hqpos hr' hC hθpos hc hε hθε h2ε
        m hstep
    have hmap : ∀ n ∈ S, n % q ∈ Finset.range q := by
      intro n hn
      exact Finset.mem_range.mpr (Nat.mod_lt n hqpos)
    have hcardFibers := Finset.card_eq_sum_card_fiberwise hmap
    have hfiberCard (r : ℕ) :
        B r = (S.filter (fun n => n % q = r)).card := by
      simp only [B, S, affineResidueClass]
      rw [Finset.filter_comm]
    have hsumRange :
        ∑ r ∈ Finset.range q, (B r : ℝ) = (S.card : ℝ) := by
      calc
        ∑ r ∈ Finset.range q, (B r : ℝ) =
            ∑ r ∈ Finset.range q,
              ((S.filter (fun n => n % q = r)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact_mod_cast hfiberCard r
        _ = (S.card : ℝ) := by
          exact_mod_cast hcardFibers.symm
    have hsumOccupiedRange :
        ∑ r ∈ affineOccupiedResidues N q, (B r : ℝ) =
          ∑ r ∈ Finset.range q, (B r : ℝ) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r hr hrnot
      have hnot : ¬ (affineResidueClass N q r).Nonempty := by
        intro hC
        exact hrnot (Finset.mem_filter.mpr ⟨hr, hC⟩)
      have hCempty : affineResidueClass N q r = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnot
      simp [B, hCempty]
    have hsum :
        ∑ r ∈ affineOccupiedResidues N q, (B r : ℝ) = (S.card : ℝ) :=
      hsumOccupiedRange.trans hsumRange
    have hcount : δ * (N : ℝ) ≤
        ∑ r ∈ affineOccupiedResidues N q, (B r : ℝ) := by
      rw [hsum]
      exact hScard
    have hbound := affineThetaBound_of_residueCounts hδ hεupper hNlarge
      hqpos hqUpper hθpos hθε B hB hcount
    exact ⟨q, hq, hqUpper, by simpa [θ] using hbound⟩

end FractionalPrimes.Literature.Polynomial
