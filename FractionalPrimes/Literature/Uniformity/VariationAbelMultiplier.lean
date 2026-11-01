module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalBasicPackage
public import FractionalPrimes.Literature.Uniformity.ProgressionIntersection
public import FractionalPrimes.Literature.Uniformity.VariationRestriction
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.List.Sort

/-!
# Abel multiplier estimate for finite progression maximal sums

This module follows the Abel summation argument in the approved `lu:tv-calculus`
proof. The finite residue-class variation below is the finite-set form of the
blueprint's `TV_{I;q}`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open Int

noncomputable section

/-- Finite residue-class inhomogeneous variation on an integer interval. -/
def finiteResidueClassVariation (I : FiniteIntegerInterval) (g : ℤ → ℂ)
    (q : ℕ) : ℝ :=
  ∑ a ∈ Finset.range q,
    finiteOrderedTotalVariation
      (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g

/-- A residue slice of an integer interval is represented with its exact
modulus as step, rather than merely as an unspecified arithmetic progression. -/
theorem filtered_Ioc_modEq_eq_arithmeticProgressionPoints
    (lo hi c : ℤ) (q : ℕ) (hq : 0 < q) :
    ∃ a : ℤ, ∃ L : ℕ,
      arithmeticProgressionPoints a q hq L =
        {x ∈ Finset.Ioc lo hi | x ≡ c [ZMOD (q : ℤ)]} := by
  classical
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  let lo' : ℤ := ⌊((lo - c : ℤ) : ℚ) / (q : ℚ)⌋
  let hi' : ℤ := ⌊((hi - c : ℤ) : ℚ) / (q : ℚ)⌋
  let L : ℕ := (hi' - lo').toNat
  let a : ℤ := c + (lo' + 1) * (q : ℤ)
  let emul : ℤ ↪ ℤ := ⟨fun z => z * (q : ℤ), mul_left_injective₀ hqZ.ne'⟩
  let eadd : ℤ ↪ ℤ := ⟨fun z => z + c, add_left_injective c⟩
  have hfilter :
      {x ∈ Finset.Ioc lo hi | x ≡ c [ZMOD (q : ℤ)]} =
        (Finset.Ioc lo' hi').map (emul.trans eadd) := by
    rw [Int.Ioc_filter_modEq_eq lo hi c]
    rw [Int.Ioc_filter_dvd_eq (lo - c) (hi - c) hqZ]
    rw [Finset.map_map]
    rfl
  have hIoc :
      Finset.Ioc lo' hi' =
        (Finset.range L).map
          (Nat.castEmbedding.trans (addLeftEmbedding (lo' + 1))) := by
    simpa [L] using (Int.Ioc_eq_finset_map lo' hi')
  refine ⟨a, L, ?_⟩
  rw [hfilter, hIoc, Finset.map_map]
  simp only [arithmeticProgressionPoints, Finset.map_eq_image]
  apply Finset.image_congr
  intro j hj
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  dsimp [a, lo', emul, eadd]
  ring

private theorem filtered_Ioc_modEq_isFiniteArithmeticProgression
    (lo hi c : ℤ) (q : ℕ) (hq : 0 < q) :
    isFiniteArithmeticProgression
      {x ∈ Finset.Ioc lo hi | x ≡ c [ZMOD (q : ℤ)]} := by
  rcases filtered_Ioc_modEq_eq_arithmeticProgressionPoints lo hi c q hq with
    ⟨a, L, hrepr⟩
  exact ⟨a, q, hq, L, hrepr⟩

/-- A residue slice of a finite integer interval is an arithmetic progression
whose step is exactly the modulus.  This retains the spacing information needed
when selecting residue prefixes. -/
theorem finiteInterval_residueFilter_eq_arithmeticProgressionPoints
    (I : FiniteIntegerInterval) (c : ℤ) (q : ℕ) (hq : 0 < q) :
    ∃ a : ℤ, ∃ L : ℕ,
      arithmeticProgressionPoints a q hq L =
        (I.points.filter fun n => n ≡ c [ZMOD (q : ℤ)]) := by
  classical
  by_cases hL : I.length = 0
  · refine ⟨0, 0, ?_⟩
    simp [FiniteIntegerInterval.points, arithmeticProgressionPoints, hL]
  · have hLpos : 0 < I.length := Nat.pos_of_ne_zero hL
    let lo : ℤ := I.start - 1
    let hi : ℤ := I.start + ((I.length - 1 : ℕ) : ℤ)
    have hIchar :
        I.points =
          {x ∈ Finset.Ioc lo hi | x ≡ I.start [ZMOD (1 : ℤ)]} := by
      simpa [FiniteIntegerInterval.points, lo, hi] using
        (arithmeticProgressionPoints_eq_Ioc_filter_modEq
          I.start 1 (by norm_num) I.length hLpos)
    have hIoc : I.points = Finset.Ioc lo hi := by
      ext x
      rw [hIchar]
      simp [Int.ModEq]
    have hfilter :
        I.points.filter (fun n => n ≡ c [ZMOD (q : ℤ)]) =
          {x ∈ Finset.Ioc lo hi | x ≡ c [ZMOD (q : ℤ)]} := by
      ext x
      simp [hIoc]
    rcases filtered_Ioc_modEq_eq_arithmeticProgressionPoints lo hi c q hq with
      ⟨a, L, hrepr⟩
    exact ⟨a, L, hrepr.trans hfilter.symm⟩

private theorem finiteInterval_residueFilter_isFiniteArithmeticProgression
    (I : FiniteIntegerInterval) (c : ℤ) (q : ℕ) (hq : 0 < q) :
    isFiniteArithmeticProgression
      (I.points.filter fun n => n ≡ c [ZMOD (q : ℤ)]) := by
  classical
  by_cases hL : I.length = 0
  · have hempty :
        I.points.filter (fun n => n ≡ c [ZMOD (q : ℤ)]) = ∅ := by
      simp [FiniteIntegerInterval.points, arithmeticProgressionPoints, hL]
    rw [hempty]
    exact ⟨0, 1, by norm_num, 0, by simp [arithmeticProgressionPoints]⟩
  · have hLpos : 0 < I.length := Nat.pos_of_ne_zero hL
    let lo : ℤ := I.start - 1
    let hi : ℤ := I.start + ((I.length - 1 : ℕ) : ℤ)
    have hIchar :
        I.points =
          {x ∈ Finset.Ioc lo hi | x ≡ I.start [ZMOD (1 : ℤ)]} := by
      simpa [FiniteIntegerInterval.points, lo, hi] using
        (arithmeticProgressionPoints_eq_Ioc_filter_modEq
          I.start 1 (by norm_num) I.length hLpos)
    have hIoc : I.points = Finset.Ioc lo hi := by
      ext x
      rw [hIchar]
      simp [Int.ModEq]
    have hfilter :
        I.points.filter (fun n => n ≡ c [ZMOD (q : ℤ)]) =
          {x ∈ Finset.Ioc lo hi | x ≡ c [ZMOD (q : ℤ)]} := by
      ext x
      simp [hIoc]
    rw [hfilter]
    exact filtered_Ioc_modEq_isFiniteArithmeticProgression lo hi c q hq

private theorem exists_int_modEq_nat_residue (q : ℕ) (hq : 0 < q) (x : ℤ) :
    ∃ a ∈ Finset.range q, x ≡ (a : ℤ) [ZMOD (q : ℤ)] := by
  classical
  let a : ℕ := (x % (q : ℤ)).toNat
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  have hrem0 : 0 ≤ x % (q : ℤ) := Int.emod_nonneg _ hqZ.ne'
  have hremLt : x % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hqZ
  have hcast : (a : ℤ) = x % (q : ℤ) := by
    exact Int.toNat_of_nonneg hrem0
  have haLtZ : (a : ℤ) < (q : ℤ) := by simpa [hcast] using hremLt
  have haLt : a < q := by exact_mod_cast haLtZ
  have hmod : x ≡ (a : ℤ) [ZMOD (q : ℤ)] := by
    change x % (q : ℤ) = (a : ℤ) % (q : ℤ)
    rw [hcast]
    simp
  exact ⟨a, Finset.mem_range.mpr haLt, hmod⟩

private def progressionIndexOrderEmbedding (a : ℤ) (d : ℕ) (hd : 0 < d) :
    ℕ ↪o ℤ :=
  OrderEmbedding.ofStrictMono
    (fun j : ℕ => a + (j : ℤ) * (d : ℤ)) (by
      apply strictMono_nat_of_lt_succ
      intro j
      have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
      simp only [Nat.cast_succ]
      nlinarith)

private theorem arithmeticProgressionPoints_sort_eq_range_map
    (a : ℤ) (d : ℕ) (hd : 0 < d) (L : ℕ) :
    (arithmeticProgressionPoints a d hd L).sort (· ≤ ·) =
      (List.range L).map (progressionIndexOrderEmbedding a d hd) := by
  let e := progressionIndexOrderEmbedding a d hd
  have hpoints :
      arithmeticProgressionPoints a d hd L = (Finset.range L).map e.toEmbedding := by
    ext x
    simp [arithmeticProgressionPoints, e, progressionIndexOrderEmbedding,
      Finset.mem_map]
  rw [hpoints]
  rw [← Finset.map_sort e.toEmbedding (Finset.range L) (· ≤ ·) (· ≤ ·)]
  · rw [Finset.sort_range]
    rfl
  · intro x hx y hy
    exact e.le_iff_le.symm

private theorem list_consecutivePairs_map {α β : Type*} (φ : α → β)
    (l : List α) :
    (l.map φ).consecutivePairs =
      l.consecutivePairs.map (fun p => (φ p.1, φ p.2)) := by
  induction l with
  | nil => simp [List.consecutivePairs]
  | cons a l ih =>
      cases l with
      | nil => simp [List.consecutivePairs]
      | cons b bs =>
          change (φ a, φ b) :: (List.map φ (b :: bs)).consecutivePairs =
            (φ a, φ b) :: ((b :: bs).consecutivePairs).map
              (fun p => (φ p.1, φ p.2))
          exact congrArg (List.cons (φ a, φ b)) ih

private theorem list_consecutivePairs_range_succ (k : ℕ) :
    (List.range (k + 2)).consecutivePairs =
      (0, 1) :: (List.map (fun p => (p.1 + 1, p.2 + 1))
        ((List.range (k + 1)).consecutivePairs)) := by
  have hmap : List.map Nat.succ (List.range (k + 1)) =
      Nat.succ 0 :: List.map Nat.succ (List.map Nat.succ (List.range k)) := by
    rw [List.range_succ_eq_map]
    simp
  rw [show k + 2 = (k + 1) + 1 by omega, List.range_succ_eq_map]
  change (0 :: List.map Nat.succ (List.range (k + 1))).zip
      (List.map Nat.succ (List.range (k + 1))) = _
  rw [hmap, List.zip_cons_cons]
  have hzip :
      (List.map Nat.succ (List.range (k + 1))).zip
          (List.map Nat.succ (List.map Nat.succ (List.range k))) =
        (List.map Nat.succ (List.range (k + 1))).consecutivePairs := by
    simp [List.consecutivePairs, List.range_succ_eq_map]
  rw [← hmap, hzip]
  norm_num
  rw [list_consecutivePairs_map Nat.succ (List.range (k + 1))]

private theorem list_consecutivePairs_range (N : ℕ) :
    (List.range N).consecutivePairs =
      (List.range (N - 1)).map (fun j => (j, j + 1)) := by
  induction N with
  | zero => simp [List.consecutivePairs]
  | succ N ih =>
      cases N with
      | zero => simp [List.consecutivePairs]
      | succ k =>
          rw [list_consecutivePairs_range_succ k, ih]
          simp [List.range_succ_eq_map, Function.comp_def]

private theorem listAdjacentVariation_range_map
    (g : ℤ → ℂ) (φ : ℕ → ℤ) (N : ℕ) :
    listAdjacentVariation g ((List.range N).map φ) =
      (List.map (fun j => ‖g (φ (j + 1)) - g (φ j)‖)
        (List.range (N - 1))).sum := by
  unfold listAdjacentVariation
  rw [list_consecutivePairs_map, list_consecutivePairs_range]
  simp [List.map_map, Function.comp_def]

private theorem list_sum_map_range_eq_finset {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (N : ℕ) :
    ((List.range N).map f).sum = ∑ j ∈ Finset.range N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.range_succ, List.map_append]
      simp [List.sum_append, ih, Finset.sum_range_succ]

private theorem listAdjacentVariation_range_map_finset
    (g : ℤ → ℂ) (φ : ℕ → ℤ) (N : ℕ) :
    listAdjacentVariation g ((List.range N).map φ) =
      ∑ j ∈ Finset.range (N - 1), ‖g (φ (j + 1)) - g (φ j)‖ := by
  rw [listAdjacentVariation_range_map, list_sum_map_range_eq_finset]

private theorem list_foldl_max_ge (l : List ℝ) (b : ℝ) :
    b ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldl_cons]
      exact (le_max_left b a).trans (ih (max b a))

private theorem list_foldl_max_mono (l : List ℝ) {b c : ℝ} (hbc : b ≤ c) :
    l.foldl max b ≤ l.foldl max c := by
  induction l generalizing b c with
  | nil => exact hbc
  | cons a l ih =>
      simp only [List.foldl_cons]
      apply ih
      exact max_le_max_right a hbc

private theorem list_foldl_max_ge_of_mem {l : List ℝ} {x : ℝ} (hx : x ∈ l) :
    x ≤ l.foldl max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
      simp only [List.mem_cons] at hx
      change x ≤ l.foldl max (max 0 a)
      rcases hx with hxa | hx
      · subst x
        exact (le_max_right 0 a).trans (list_foldl_max_ge l (max 0 a))
      · exact (ih hx).trans (list_foldl_max_mono l (le_max_left 0 a))

private theorem norm_le_listSupNorm_of_mem (g : ℤ → ℂ) {l : List ℤ}
    {x : ℤ} (hx : x ∈ l) : ‖g x‖ ≤ listSupNorm g l := by
  unfold listSupNorm
  apply list_foldl_max_ge_of_mem
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

private theorem sum_extendByZero_arithmeticProgressionPoints
    (a : ℤ) (d : ℕ) (hd : 0 < d) (L : ℕ) (F : ℤ → ℂ) :
    (∑ n ∈ arithmeticProgressionPoints a d hd L, F n) =
      ∑ j ∈ Finset.range L, F (progressionIndexOrderEmbedding a d hd j) := by
  classical
  let e := progressionIndexOrderEmbedding a d hd
  have hinj : Set.InjOn (fun j : ℕ => e j) (↑(Finset.range L)) := e.injective.injOn
  simpa [arithmeticProgressionPoints, e, progressionIndexOrderEmbedding] using
    (Finset.sum_image (f := F) hinj)

private theorem progressionMaximalSum_bound_of_ap
    (I : FiniteIntegerInterval) (P : Finset ℤ)
    (hP : isFiniteArithmeticProgression P) (hPI : P ⊆ I.points)
    (f : {n : ℤ // n ∈ I.points} → ℂ) :
    ‖∑ n ∈ P, extendByZero I.points f n‖ ≤ progressionMaximalSum I f := by
  classical
  unfold progressionMaximalSum
  refine Finset.le_sup'
    (fun Q => ‖∑ n ∈ Q, extendByZero I.points f n‖) ?_
  rw [arithmeticProgressionsWithin, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hPI, hP⟩

private theorem sum_range_mul_abel_identity (N : ℕ) (u v : ℕ → ℂ) (hN : 0 < N) :
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

private theorem progressionSum_mul_le_totalVariation_of_ap
    (I : FiniteIntegerInterval) (a : ℤ) (d : ℕ) (hd : 0 < d) (L : ℕ)
    (hsubset : arithmeticProgressionPoints a d hd L ⊆ I.points)
    (f : {n : ℤ // n ∈ I.points} → ℂ) (g : ℤ → ℂ) :
    ‖∑ n ∈ arithmeticProgressionPoints a d hd L,
      extendByZero I.points f n * g n‖ ≤
        progressionMaximalSum I f *
          finiteOrderedTotalVariation (arithmeticProgressionPoints a d hd L) g := by
  classical
  by_cases hL0 : L = 0
  · subst L
    simp [arithmeticProgressionPoints, finiteOrderedTotalVariation,
      listSupNorm, listAdjacentVariation]
  have hL : 0 < L := Nat.pos_of_ne_zero hL0
  let e := progressionIndexOrderEmbedding a d hd
  let u : ℕ → ℂ := fun j => extendByZero I.points f (e j)
  let v : ℕ → ℂ := fun j => g (e j)
  let P := arithmeticProgressionPoints a d hd L
  have hsort : P.sort (· ≤ ·) = (List.range L).map e := by
    simpa [P, e] using arithmeticProgressionPoints_sort_eq_range_map a d hd L
  have hPAP : isFiniteArithmeticProgression P := ⟨a, d, hd, L, rfl⟩
  have hmaxFull := progressionMaximalSum_bound_of_ap I P hPAP hsubset f
  have hsumFull :
      (∑ n ∈ P, extendByZero I.points f n) = ∑ j ∈ Finset.range L, u j := by
    simpa [P, u, e, progressionIndexOrderEmbedding] using
      (sum_extendByZero_arithmeticProgressionPoints a d hd L
        (fun n => extendByZero I.points f n))
  have hfinal : ‖∑ j ∈ Finset.range L, u j‖ ≤ progressionMaximalSum I f := by
    rw [← hsumFull]
    exact hmaxFull
  have hprefix : ∀ j ∈ Finset.range (L - 1),
      ‖∑ i ∈ Finset.range (j + 1), u i‖ ≤ progressionMaximalSum I f := by
    intro j hj
    have hjlt : j < L - 1 := Finset.mem_range.mp hj
    have hlen : j + 1 ≤ L := by omega
    let Q := arithmeticProgressionPoints a d hd (j + 1)
    have hQP : Q ⊆ P := by
      intro x hx
      simp only [Q, P, arithmeticProgressionPoints, Finset.mem_image,
        Finset.mem_range] at hx ⊢
      rcases hx with ⟨i, hi, hix⟩
      exact ⟨i, lt_of_lt_of_le hi hlen, hix⟩
    have hQI : Q ⊆ I.points := hQP.trans hsubset
    have hQAP : isFiniteArithmeticProgression Q := ⟨a, d, hd, j + 1, rfl⟩
    have hmaxQ := progressionMaximalSum_bound_of_ap I Q hQAP hQI f
    have hsumQ :
        (∑ n ∈ Q, extendByZero I.points f n) =
          ∑ i ∈ Finset.range (j + 1), u i := by
      simpa [Q, u, e, progressionIndexOrderEmbedding] using
        (sum_extendByZero_arithmeticProgressionPoints a d hd (j + 1)
          (fun n => extendByZero I.points f n))
    rw [← hsumQ]
    exact hmaxQ
  have hlastMem : e (L - 1) ∈ (List.range L).map e := by
    apply List.mem_map.mpr
    exact ⟨L - 1, List.mem_range.mpr (Nat.sub_lt hL (by norm_num)), rfl⟩
  have hlast : ‖v (L - 1)‖ ≤ listSupNorm g (P.sort (· ≤ ·)) := by
    rw [hsort]
    simpa [v, e] using norm_le_listSupNorm_of_mem g hlastMem
  have hadj :
      listAdjacentVariation g (P.sort (· ≤ ·)) =
        ∑ j ∈ Finset.range (L - 1), ‖v j - v (j + 1)‖ := by
    rw [hsort, listAdjacentVariation_range_map_finset]
    simp [v, norm_sub_rev]
  have hsumProduct :
      (∑ n ∈ P, extendByZero I.points f n * g n) =
        ∑ j ∈ Finset.range L, u j * v j := by
    simpa [P, u, v, e, progressionIndexOrderEmbedding] using
      (sum_extendByZero_arithmeticProgressionPoints a d hd L
        (fun n => extendByZero I.points f n * g n))
  have habel := sum_range_mul_abel_identity L u v hL
  rw [hsumProduct, habel]
  have hterm : ∀ j ∈ Finset.range (L - 1),
      ‖(∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ ≤
        progressionMaximalSum I f * ‖v j - v (j + 1)‖ := by
    intro j hj
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hprefix j hj) (norm_nonneg _)
  have hsumTerms :
      ‖∑ j ∈ Finset.range (L - 1),
          (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ ≤
        ∑ j ∈ Finset.range (L - 1),
          progressionMaximalSum I f * ‖v j - v (j + 1)‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.range (L - 1),
          ‖(∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun j hj => hterm j hj
  have hfirst :
      ‖(∑ j ∈ Finset.range L, u j) * v (L - 1)‖ ≤
        progressionMaximalSum I f * listSupNorm g (P.sort (· ≤ ·)) := by
    rw [norm_mul]
    calc
      ‖∑ j ∈ Finset.range L, u j‖ * ‖v (L - 1)‖ ≤
          progressionMaximalSum I f * ‖v (L - 1)‖ :=
        mul_le_mul_of_nonneg_right hfinal (norm_nonneg _)
      _ ≤ progressionMaximalSum I f * listSupNorm g (P.sort (· ≤ ·)) :=
        mul_le_mul_of_nonneg_left hlast (progressionMaximalSum_nonneg I f)
  calc
    ‖(∑ j ∈ Finset.range L, u j) * v (L - 1) +
        ∑ j ∈ Finset.range (L - 1),
          (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ ≤
        ‖(∑ j ∈ Finset.range L, u j) * v (L - 1)‖ +
          ‖∑ j ∈ Finset.range (L - 1),
            (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ := norm_add_le _ _
    _ ≤ progressionMaximalSum I f * listSupNorm g (P.sort (· ≤ ·)) +
          progressionMaximalSum I f *
            (∑ j ∈ Finset.range (L - 1), ‖v j - v (j + 1)‖) := by
      rw [Finset.mul_sum]
      exact add_le_add hfirst hsumTerms
    _ = progressionMaximalSum I f *
          (listSupNorm g (P.sort (· ≤ ·)) +
            listAdjacentVariation g (P.sort (· ≤ ·))) := by rw [hadj]; ring
    _ = progressionMaximalSum I f * finiteOrderedTotalVariation P g := by
      rw [finiteOrderedTotalVariation]

/-- Finite Abel summation on one arithmetic progression selects an attained
initial prefix.  The full weighted sum is controlled by the inhomogeneous
variation of the weight times the unweighted sum on that prefix. -/
theorem exists_arithmeticProgressionPrefix_sum_mul_bound
    (a : ℤ) (d : ℕ) (hd : 0 < d) (L : ℕ) (F b : ℤ → ℂ) :
    ∃ K : ℕ, K ≤ L ∧
      ‖∑ n ∈ arithmeticProgressionPoints a d hd L, b n * F n‖ ≤
        finiteOrderedTotalVariation (arithmeticProgressionPoints a d hd L) b *
          ‖∑ n ∈ arithmeticProgressionPoints a d hd K, F n‖ := by
  classical
  by_cases hL0 : L = 0
  · subst L
    refine ⟨0, le_rfl, ?_⟩
    simp [arithmeticProgressionPoints, finiteOrderedTotalVariation,
      listSupNorm, listAdjacentVariation]
  have hL : 0 < L := Nat.pos_of_ne_zero hL0
  let e := progressionIndexOrderEmbedding a d hd
  let u : ℕ → ℂ := fun j => F (e j)
  let v : ℕ → ℂ := fun j => b (e j)
  let P := arithmeticProgressionPoints a d hd L
  have hprefixNonempty : (Finset.range (L + 1)).Nonempty := ⟨0, by simp⟩
  let M : ℝ := (Finset.range (L + 1)).sup' hprefixNonempty
    (fun K => ‖∑ j ∈ Finset.range K, u j‖)
  obtain ⟨K, hKmem, hMattains⟩ :=
    Finset.exists_mem_eq_sup' hprefixNonempty
      (fun K => ‖∑ j ∈ Finset.range K, u j‖)
  have hMattainsM : M = ‖∑ j ∈ Finset.range K, u j‖ := by
    simpa [M] using hMattains
  have hKle : K ≤ L := by
    have hKlt : K < L + 1 := Finset.mem_range.mp hKmem
    omega
  have hprefix : ∀ k, k ≤ L →
      ‖∑ j ∈ Finset.range k, u j‖ ≤ M := by
    intro k hk
    exact Finset.le_sup'
      (fun t => ‖∑ j ∈ Finset.range t, u j‖)
      (Finset.mem_range.mpr (by omega))
  have hMnonneg : 0 ≤ M := by
    rw [hMattainsM]
    exact norm_nonneg _
  have hsort : P.sort (· ≤ ·) = (List.range L).map e := by
    simpa [P, e] using arithmeticProgressionPoints_sort_eq_range_map a d hd L
  have hlastMem : e (L - 1) ∈ (List.range L).map e := by
    apply List.mem_map.mpr
    exact ⟨L - 1, List.mem_range.mpr (Nat.sub_lt hL (by norm_num)), rfl⟩
  have hlast : ‖v (L - 1)‖ ≤ listSupNorm b (P.sort (· ≤ ·)) := by
    rw [hsort]
    simpa [v, e] using norm_le_listSupNorm_of_mem b hlastMem
  have hadj :
      listAdjacentVariation b (P.sort (· ≤ ·)) =
        ∑ j ∈ Finset.range (L - 1), ‖v j - v (j + 1)‖ := by
    rw [hsort, listAdjacentVariation_range_map_finset]
    simp [v, norm_sub_rev]
  have hsumProduct :
      (∑ n ∈ P, b n * F n) = ∑ j ∈ Finset.range L, u j * v j := by
    calc
      (∑ n ∈ P, b n * F n) = ∑ n ∈ P, F n * b n := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = ∑ j ∈ Finset.range L, u j * v j := by
        simpa [P, u, v, e, progressionIndexOrderEmbedding] using
          (sum_extendByZero_arithmeticProgressionPoints a d hd L
            (fun n => F n * b n))
  have hsumPrefix :
      (∑ n ∈ arithmeticProgressionPoints a d hd K, F n) =
        ∑ j ∈ Finset.range K, u j := by
    simpa [u, e, progressionIndexOrderEmbedding] using
      (sum_extendByZero_arithmeticProgressionPoints a d hd K F)
  have habel := sum_range_mul_abel_identity L u v hL
  have hterm : ∀ j ∈ Finset.range (L - 1),
      ‖(∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ ≤
        M * ‖v j - v (j + 1)‖ := by
    intro j hj
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right
    · apply hprefix
      have hjlt : j < L - 1 := Finset.mem_range.mp hj
      omega
    · exact norm_nonneg _
  have hsumTerms :
      ‖∑ j ∈ Finset.range (L - 1),
          (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ ≤
        ∑ j ∈ Finset.range (L - 1), M * ‖v j - v (j + 1)‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.range (L - 1),
          ‖(∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ :=
        norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun j hj => hterm j hj
  have hfirst :
      ‖(∑ j ∈ Finset.range L, u j) * v (L - 1)‖ ≤
        M * listSupNorm b (P.sort (· ≤ ·)) := by
    rw [norm_mul]
    calc
      ‖∑ j ∈ Finset.range L, u j‖ * ‖v (L - 1)‖ ≤
          M * ‖v (L - 1)‖ :=
        mul_le_mul_of_nonneg_right (hprefix L le_rfl) (norm_nonneg _)
      _ ≤ M * listSupNorm b (P.sort (· ≤ ·)) :=
        mul_le_mul_of_nonneg_left hlast hMnonneg
  have hweighted :
      ‖∑ j ∈ Finset.range L, u j * v j‖ ≤
        M * finiteOrderedTotalVariation P b := by
    rw [habel]
    calc
      ‖(∑ j ∈ Finset.range L, u j) * v (L - 1) +
          ∑ j ∈ Finset.range (L - 1),
            (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ ≤
          ‖(∑ j ∈ Finset.range L, u j) * v (L - 1)‖ +
            ‖∑ j ∈ Finset.range (L - 1),
              (∑ i ∈ Finset.range (j + 1), u i) * (v j - v (j + 1))‖ :=
        norm_add_le _ _
      _ ≤ M * listSupNorm b (P.sort (· ≤ ·)) +
          M * (∑ j ∈ Finset.range (L - 1), ‖v j - v (j + 1)‖) := by
        rw [Finset.mul_sum]
        exact add_le_add hfirst hsumTerms
      _ = M * (listSupNorm b (P.sort (· ≤ ·)) +
          listAdjacentVariation b (P.sort (· ≤ ·))) := by rw [hadj]; ring
      _ = M * finiteOrderedTotalVariation P b := by
        rw [finiteOrderedTotalVariation]
  refine ⟨K, hKle, ?_⟩
  rw [hsumProduct]
  calc
    ‖∑ j ∈ Finset.range L, u j * v j‖ ≤
        M * finiteOrderedTotalVariation P b := hweighted
    _ = finiteOrderedTotalVariation P b *
        ‖∑ n ∈ arithmeticProgressionPoints a d hd K, F n‖ := by
      rw [hsumPrefix, hMattainsM]
      ring

private theorem nat_residue_unique (q a b : ℕ) (ha : a < q) (hb : b < q)
    (hab : (a : ℤ) ≡ (b : ℤ) [ZMOD (q : ℤ)]) : a = b := by
  have haLt : (a : ℤ) < (q : ℤ) := by exact_mod_cast ha
  have hbLt : (b : ℤ) < (q : ℤ) := by exact_mod_cast hb
  have hrem : (a : ℤ) % (q : ℤ) = (b : ℤ) % (q : ℤ) := by
    change (a : ℤ) % (q : ℤ) = (b : ℤ) % (q : ℤ) at hab
    exact hab
  have harem : (a : ℤ) % (q : ℤ) = a := Int.emod_eq_of_lt (Nat.cast_nonneg _) haLt
  have hbrem : (b : ℤ) % (q : ℤ) = b := Int.emod_eq_of_lt (Nat.cast_nonneg _) hbLt
  rw [harem, hbrem] at hrem
  exact_mod_cast hrem

/-- Split a finite integer sum into the `q` canonical residue classes. -/
theorem sum_eq_sum_residue_filters (P : Finset ℤ) (q : ℕ)
    (hq : 0 < q) (F : ℤ → ℂ) :
    (∑ n ∈ P, F n) =
      ∑ a ∈ Finset.range q,
        ∑ n ∈ P.filter (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), F n := by
  classical
  let fibers := fun a : ℕ => P.filter (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)])
  have hcover : (Finset.range q).biUnion fibers = P := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_biUnion.mp hn with ⟨a, ha, hna⟩
      exact (Finset.mem_filter.mp hna).1
    · intro hn
      obtain ⟨a, ha, hmod⟩ := exists_int_modEq_nat_residue q hq n
      exact Finset.mem_biUnion.mpr ⟨a, ha,
        Finset.mem_filter.mpr ⟨hn, hmod⟩⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range q)) fibers := by
    intro a ha b hb hab
    have ha' : a ∈ Finset.range q := by simpa using ha
    have hb' : b ∈ Finset.range q := by simpa using hb
    apply Finset.disjoint_left.mpr
    intro n hna hnb
    have hnaMod := (Finset.mem_filter.mp hna).2
    have hnbMod := (Finset.mem_filter.mp hnb).2
    apply hab
    exact nat_residue_unique q a b (Finset.mem_range.mp ha')
      (Finset.mem_range.mp hb') (hnaMod.symm.trans hnbMod)
  calc
    (∑ n ∈ P, F n) =
        ∑ n ∈ (Finset.range q).biUnion fibers, F n := by rw [hcover]
    _ = ∑ a ∈ Finset.range q, ∑ n ∈ fibers a, F n :=
      Finset.sum_biUnion hdisj

/-- The exact finite Abel multiplier estimate in blueprint item
`lu:tv-calculus`, with residue-class variation on the interval. -/
theorem progressionMaximalSum_mul_le_finiteResidueClassVariation
    (I : FiniteIntegerInterval)
    (f : {n : ℤ // n ∈ I.points} → ℂ) (g : ℤ → ℂ)
    (q : ℕ) (hq : 0 < q) :
    progressionMaximalSum I (fun n => f n * g n.1) ≤
      finiteResidueClassVariation I g q * progressionMaximalSum I f := by
  classical
  unfold progressionMaximalSum
  apply Finset.sup'_le
  intro P hP
  have hPsubset : P ⊆ I.points :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  have hPAP : isFiniteArithmeticProgression P := (Finset.mem_filter.mp hP).2
  let F : ℤ → ℂ := fun n => extendByZero I.points f n * g n
  have hsumProduct :
      (∑ n ∈ P, extendByZero I.points (fun m => f m * g m.1) n) =
        ∑ n ∈ P, F n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [F, extendByZero, hPsubset hn]
  have hsplit := sum_eq_sum_residue_filters P q hq F
  have hbound : ∀ a ∈ Finset.range q,
      ‖∑ n ∈ P.filter (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), F n‖ ≤
        progressionMaximalSum I f *
          finiteOrderedTotalVariation
            (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g := by
    intro a ha
    let R : Finset ℤ := I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]
    let Q : Finset ℤ := P.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]
    have hRAP : isFiniteArithmeticProgression R := by
      simpa [R] using finiteInterval_residueFilter_isFiniteArithmeticProgression
        I (a : ℤ) q hq
    have hQeq : Q = P ∩ R := by
      ext n
      simp only [Q, R, Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨hnP, hmod⟩
        exact ⟨hnP, hPsubset hnP, hmod⟩
      · rintro ⟨hnP, _, hmod⟩
        exact ⟨hnP, hmod⟩
    rcases hPAP with ⟨pa, pd, hpd, pL, hPeq⟩
    rcases hRAP with ⟨ra, rd, hrd, rL, hReq⟩
    have hQclass : Q = ∅ ∨ isFiniteArithmeticProgression Q := by
      have hclass :=
        arithmeticProgressionPoints_inter_eq_empty_or_isFiniteArithmeticProgression
          pa ra pd rd hpd hrd pL rL
      simpa [Q, R, hQeq, hPeq, hReq] using hclass
    have hQR : Q ⊆ R := by
      rw [hQeq]
      exact Finset.inter_subset_right
    have hRI : R ⊆ I.points := by
      simp [R]
    rcases hQclass with hQempty | hQAP
    · simp [Q, hQempty]
      exact mul_nonneg (progressionMaximalSum_nonneg I f)
        (finiteOrderedTotalVariation_nonneg R g)
    · rcases hQAP with ⟨qa, qd, hqd, qL, hQrepr⟩
      have hQsubsetI : arithmeticProgressionPoints qa qd hqd qL ⊆ I.points := by
        simpa [hQrepr] using hQR.trans hRI
      have hAbel := progressionSum_mul_le_totalVariation_of_ap
        I qa qd hqd qL hQsubsetI f g
      have hAbelQ :
          ‖∑ n ∈ Q, F n‖ ≤
            progressionMaximalSum I f * finiteOrderedTotalVariation Q g := by
        simpa [F, hQrepr] using hAbel
      calc
        ‖∑ n ∈ Q, F n‖ ≤
            progressionMaximalSum I f * finiteOrderedTotalVariation Q g := hAbelQ
        _ ≤ progressionMaximalSum I f * finiteOrderedTotalVariation R g :=
          mul_le_mul_of_nonneg_left
            (finiteOrderedTotalVariation_mono_of_subset hQR g)
            (progressionMaximalSum_nonneg I f)
  calc
    ‖∑ n ∈ P, extendByZero I.points (fun n => f n * g n.1) n‖ =
        ‖∑ n ∈ P, F n‖ := by rw [hsumProduct]
    _ = ‖∑ a ∈ Finset.range q,
          ∑ n ∈ P.filter (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), F n‖ :=
        congrArg norm hsplit
    _ ≤ ∑ a ∈ Finset.range q,
          ‖∑ n ∈ P.filter (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), F n‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.range q,
          progressionMaximalSum I f *
            finiteOrderedTotalVariation
              (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g :=
        Finset.sum_le_sum fun a ha => hbound a ha
    _ = progressionMaximalSum I f * finiteResidueClassVariation I g q := by
        rw [finiteResidueClassVariation, ← Finset.mul_sum]
    _ = finiteResidueClassVariation I g q * progressionMaximalSum I f := by ring

end

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.progressionMaximalSum_mul_le_finiteResidueClassVariation
#print axioms FractionalPrimes.Literature.Uniformity.filtered_Ioc_modEq_eq_arithmeticProgressionPoints
#print axioms FractionalPrimes.Literature.Uniformity.finiteInterval_residueFilter_eq_arithmeticProgressionPoints
#print axioms FractionalPrimes.Literature.Uniformity.exists_arithmeticProgressionPrefix_sum_mul_bound
