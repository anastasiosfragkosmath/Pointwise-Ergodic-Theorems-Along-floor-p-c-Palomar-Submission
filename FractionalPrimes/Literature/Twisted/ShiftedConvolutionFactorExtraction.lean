module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi

/-!
# Finite interval estimates for shifted-convolution factor extraction

This module starts with the exact half-open interval and inverse-square-root
counting estimate used in `ltw:factor-extraction`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

/-- Natural integers in the source interval `(U,2U]`, represented by its
exact floor endpoints. -/
noncomputable def factorExtractionDyadicInterval (U : ℝ) : Finset ℕ :=
  Finset.Ioc (Nat.floor U) (Nat.floor (2 * U))

/-- The floor representation preserves the open-left, closed-right endpoints
of `(U,2U]`. -/
theorem mem_factorExtractionDyadicInterval
    {U : ℝ} (hU : 0 ≤ U) (m : ℕ) :
    m ∈ factorExtractionDyadicInterval U ↔
      U < (m : ℝ) ∧ (m : ℝ) ≤ 2 * U := by
  constructor
  · intro hm
    rcases Finset.mem_Ioc.mp hm with ⟨hmlo, hmhi⟩
    exact ⟨Nat.lt_of_floor_lt hmlo,
      le_trans (Nat.cast_le.mpr hmhi) (Nat.floor_le (by positivity))⟩
  · rintro ⟨hmlo, hmhi⟩
    apply Finset.mem_Ioc.mpr
    refine ⟨(Nat.floor_lt hU).2 hmlo, ?_⟩
    exact Nat.le_floor hmhi

/-- The source's exact factor `3 sqrt(U)` for the inverse-square-root mass
on `(U,2U]`; for `U<1/2` the interval is empty. -/
theorem factorExtractionDyadicInverseSqrtMass
    {U : ℝ} (hU : 0 < U) :
    (∑ m ∈ factorExtractionDyadicInterval U,
      (1 : ℝ) / Real.sqrt (m : ℝ)) ≤ 3 * Real.sqrt U := by
  classical
  by_cases hlarge : 1 / 2 ≤ U
  · let S := factorExtractionDyadicInterval U
    have hfloorMono : Nat.floor U ≤ Nat.floor (2 * U) :=
      Nat.floor_mono (by nlinarith)
    have hcard : (S.card : ℝ) =
        (Nat.floor (2 * U) : ℝ) - (Nat.floor U : ℝ) := by
      dsimp [S, factorExtractionDyadicInterval]
      rw [Nat.card_Ioc]
      exact_mod_cast Nat.cast_sub hfloorMono
    have hfloorUpper : (Nat.floor (2 * U) : ℝ) ≤ 2 * U :=
      Nat.floor_le (by positivity)
    have hfloorLower : U - 1 ≤ (Nat.floor U : ℝ) :=
      (Nat.sub_one_lt_floor U).le
    have hcardSmall : (S.card : ℝ) ≤ U + 1 := by
      rw [hcard]
      calc
        (Nat.floor (2 * U) : ℝ) - (Nat.floor U : ℝ) ≤
            2 * U - (U - 1) := sub_le_sub hfloorUpper hfloorLower
        _ = U + 1 := by ring
    have hcardBound : (S.card : ℝ) ≤ 3 * U := by
      nlinarith
    have hsqrtU : 0 < Real.sqrt U := Real.sqrt_pos.2 hU
    have hterm (m : ℕ) (hm : m ∈ S) :
        (1 : ℝ) / Real.sqrt (m : ℝ) ≤ 1 / Real.sqrt U := by
      have hinterval := (mem_factorExtractionDyadicInterval hU.le m).mp
        (by simpa [S] using hm)
      exact one_div_le_one_div_of_le hsqrtU
        (Real.sqrt_le_sqrt (le_of_lt hinterval.1))
    calc
      (∑ m ∈ S, (1 : ℝ) / Real.sqrt (m : ℝ)) ≤
          ∑ _m ∈ S, (1 : ℝ) / Real.sqrt U := by
        apply Finset.sum_le_sum
        intro m hm
        exact hterm m hm
      _ = (S.card : ℝ) * (1 / Real.sqrt U) := by simp
      _ ≤ (3 * U) * (1 / Real.sqrt U) := by
        exact mul_le_mul_of_nonneg_right hcardBound (by positivity)
      _ = 3 * Real.sqrt U := by
        field_simp [ne_of_gt hsqrtU]
        nlinarith [Real.sq_sqrt hU.le]
  · have hsmall : U < 1 / 2 := lt_of_not_ge hlarge
    have hfloorU : Nat.floor U = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have hfloor2U : Nat.floor (2 * U) = 0 :=
      Nat.floor_eq_zero.mpr (by nlinarith)
    simp [factorExtractionDyadicInterval, hfloorU, hfloor2U]

/-- A coefficient bounded by `B` contributes at most `3 B sqrt(U)` to the
absolute inverse-square-root mass on the source interval `(U,2U]`. -/
theorem factorExtractionDyadicCoefficientMass
    {U B : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (f : ℕ → ℂ)
    (hf : ∀ m ∈ factorExtractionDyadicInterval U, ‖f m‖ ≤ B) :
    (∑ m ∈ factorExtractionDyadicInterval U,
      ‖f m‖ / Real.sqrt (m : ℝ)) ≤ 3 * B * Real.sqrt U := by
  classical
  let S := factorExtractionDyadicInterval U
  have hsum := factorExtractionDyadicInverseSqrtMass hU
  calc
    (∑ m ∈ S, ‖f m‖ / Real.sqrt (m : ℝ)) ≤
        ∑ m ∈ S, B / Real.sqrt (m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact div_le_div_of_nonneg_right (hf m (by simpa [S] using hm))
        (Real.sqrt_nonneg _)
    _ = B * ∑ m ∈ S, (1 : ℝ) / Real.sqrt (m : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [mul_one_div]
    _ ≤ B * (3 * Real.sqrt U) := by
      exact mul_le_mul_of_nonneg_left (by simpa [S] using hsum) hB
    _ = 3 * B * Real.sqrt U := by ring

/-- A bounded coefficient times any weight of size at most `m⁻¹ᐟ²`, with
an optional coprimality cutoff, has the same `3 B sqrt(U)` absolute mass. -/
theorem factorExtractionDyadicTwistedCoefficientMass
    {U B : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (f w : ℕ → ℂ) (s : ℕ)
    (hf : ∀ m ∈ factorExtractionDyadicInterval U, ‖f m‖ ≤ B)
    (hw : ∀ m, 0 < m → ‖w m‖ ≤ 1 / Real.sqrt (m : ℝ)) :
    (∑ m ∈ factorExtractionDyadicInterval U,
      ‖f m * (if Nat.Coprime m s then w m else 0)‖) ≤
        3 * B * Real.sqrt U := by
  classical
  let S := factorExtractionDyadicInterval U
  apply le_trans ?_ (factorExtractionDyadicCoefficientMass hU hB
    (f := f) (by simpa [S] using hf))
  apply Finset.sum_le_sum
  intro m hm
  by_cases hcop : Nat.Coprime m s
  · simp only [if_pos hcop, norm_mul]
    have hmReal : 0 < (m : ℝ) := by
      have hmem := (mem_factorExtractionDyadicInterval hU.le m).mp
        (by simpa [S] using hm)
      exact lt_trans hU hmem.1
    have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmReal
    calc
      ‖f m‖ * ‖w m‖ ≤ ‖f m‖ * (1 / Real.sqrt (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (hw m (by exact_mod_cast hmReal)) (norm_nonneg _)
      _ = ‖f m‖ / Real.sqrt (m : ℝ) := by ring
  · simp [hcop]
    positivity

/-- A real half-open interval encoded as a finite natural interval. -/
noncomputable def factorExtractionRealInterval (x y : ℝ) : Finset ℕ :=
  Finset.Ioc (Nat.floor x) (Nat.floor y)

/-- The floor encoding of a real interval retains the open-left,
closed-right convention. -/
theorem mem_factorExtractionRealInterval
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (m : ℕ) :
    m ∈ factorExtractionRealInterval x y ↔ x < (m : ℝ) ∧ (m : ℝ) ≤ y := by
  constructor
  · intro hm
    rcases Finset.mem_Ioc.mp hm with ⟨hmx, hmy⟩
    exact ⟨Nat.lt_of_floor_lt hmx,
      le_trans (Nat.cast_le.mpr hmy) (Nat.floor_le hy)⟩
  · rintro ⟨hmx, hmy⟩
    apply Finset.mem_Ioc.mpr
    exact ⟨(Nat.floor_lt hx).2 hmx, Nat.le_floor hmy⟩

/-- Scaling an interval by a fixed positive product retains the same endpoint
convention, which is the set inclusion used when the other factors are fixed. -/
theorem factorExtraction_mul_interval_iff
    {x y c m : ℝ} (hc : 0 < c) :
    c * m ∈ Set.Ioc x y ↔ m ∈ Set.Ioc (x / c) (y / c) := by
  constructor
  · rintro ⟨hxm, hmy⟩
    constructor
    · exact (div_lt_iff₀ hc).2 (by simpa [mul_comm] using hxm)
    · exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmy)
  · rintro ⟨hxm, hmy⟩
    constructor
    · simpa [mul_comm] using (div_lt_iff₀ hc).1 hxm
    · simpa [mul_comm] using (le_div_iff₀ hc).1 hmy

/-- After fixing all other factors, the selected factor is restricted to the
intersection of its dyadic support interval and the product interval divided
by the fixed positive product. -/
theorem factorExtractionDyadicProductInterval_iff
    {U M x y : ℝ} (hU : 0 < U) (hM : 0 < M)
    (hx : 0 ≤ x) (hxy : x ≤ y) (m : ℕ) :
    (m ∈ factorExtractionDyadicInterval U ∧
        M * (m : ℝ) ∈ Set.Ioc x y) ↔
      m ∈ factorExtractionRealInterval
        (max U (x / M)) (min (2 * U) (y / M)) := by
  have hupperNonneg : 0 ≤ y / M := div_nonneg (le_trans hx hxy) hM.le
  have hlowerNonneg : 0 ≤ max U (x / M) := le_max_of_le_left hU.le
  have hboundNonneg : 0 ≤ min (2 * U) (y / M) :=
    le_min (by positivity) hupperNonneg
  rw [mem_factorExtractionRealInterval hlowerNonneg hboundNonneg]
  rw [mem_factorExtractionDyadicInterval hU.le]
  rw [factorExtraction_mul_interval_iff hM]
  constructor
  · rintro ⟨⟨hmlo, hmhi⟩, ⟨hmx, hmy⟩⟩
    constructor
    · exact max_lt_iff.mpr ⟨hmlo, hmx⟩
    · exact le_min hmhi hmy
  · rintro ⟨hmlo, hmhi⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact lt_of_le_of_lt (le_max_left _ _) hmlo
    · exact le_trans hmhi (min_le_left _ _)
    · exact lt_of_le_of_lt (le_max_right _ _) hmlo
    · exact le_trans hmhi (min_le_right _ _)

/-- The factor-extraction conclusion for one convolution factor.  The local
short-interval hypothesis is applied to the intersection with the original
dyadic support, retaining both half-open endpoints. -/
theorem shiftedConvolutionSmallFactor_one
    {r : ℕ} {N ε : ℝ} (hr : 0 < r) (hN : 0 < N) (_hε : 0 ≤ ε)
    (a W : ℕ → ℂ)
    (hsupport : ∀ n, a n ≠ 0 → N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N)
    (hshort : ∀ u v : ℝ, 0 ≤ u →
      Set.Ioc u v ⊆ Set.Ioc (N / (r : ℝ)) (2 * N / (r : ℝ)) →
      ‖∑ m ∈ factorExtractionRealInterval u v, a (r * m) * W m‖ ≤
        ε * Real.sqrt (N / (r : ℝ)))
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖∑ n ∈ factorExtractionRealInterval x y, a (r * n) * W n‖ ≤
      ε * Real.sqrt (N / (r : ℝ)) := by
  let U : ℝ := N / (r : ℝ)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hU : 0 < U := by dsimp [U]; exact div_pos hN hrR
  have hxU : 0 ≤ x := hx
  let lo := max U (x / (1 : ℝ))
  let hi := min (2 * U) (y / (1 : ℝ))
  have hlo : 0 ≤ lo := le_max_of_le_left hU.le
  have hhi : 0 ≤ hi := le_min (by positivity)
    (div_nonneg (le_trans hxU hxy) (by norm_num : (0 : ℝ) ≤ 1))
  have hinterval (n : ℕ) :
      (n ∈ factorExtractionRealInterval x y ∧
        n ∈ factorExtractionDyadicInterval U) ↔
        n ∈ factorExtractionRealInterval lo hi := by
    have hprod := factorExtractionDyadicProductInterval_iff
      hU (by norm_num : 0 < (1 : ℝ)) hxU hxy n
    constructor
    · rintro ⟨hnJ, hnD⟩
      apply hprod.mp
      refine ⟨hnD, ?_⟩
      have hy : 0 ≤ y := le_trans hxU hxy
      have hnJ' := (mem_factorExtractionRealInterval hxU hy n).mp hnJ
      simpa using hnJ'
    · intro hnI
      rcases hprod.mpr hnI with ⟨hnD, hnJ⟩
      have hy : 0 ≤ y := le_trans hxU hxy
      exact ⟨(mem_factorExtractionRealInterval hxU hy n).mpr (by simpa using hnJ), hnD⟩
  have hsubset : Set.Ioc lo hi ⊆ Set.Ioc U (2 * U) := by
    intro z hz
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hz.1,
      le_trans hz.2 (min_le_left _ _)⟩
  have hupperEq : 2 * U = 2 * N / (r : ℝ) := by
    dsimp [U]
    field_simp [ne_of_gt hrR]
  have hsubsetSource : Set.Ioc lo hi ⊆
      Set.Ioc (N / (r : ℝ)) (2 * N / (r : ℝ)) := by
    simpa [U, hupperEq, lo, hi] using hsubset
  have hlocal := hshort lo hi hlo hsubsetSource
  have hsum :
      (∑ n ∈ factorExtractionRealInterval x y, a (r * n) * W n) =
        ∑ n ∈ factorExtractionRealInterval lo hi, a (r * n) * W n := by
    have hsub : factorExtractionRealInterval lo hi ⊆
        factorExtractionRealInterval x y := by
      intro n hn
      exact (hinterval n).2 hn |>.1
    have hzero : ∀ n ∈ factorExtractionRealInterval x y,
        n ∉ factorExtractionRealInterval lo hi → a (r * n) * W n = 0 := by
      intro n hnJ hnNot
      by_contra hterm
      have hcoef : a (r * n) ≠ 0 := by
        intro hzero
        apply hterm
        simp [hzero]
      have hsupportn := hsupport (r * n) hcoef
      have hsuppSet : (r : ℝ) * (n : ℝ) ∈ Set.Ioc N (2 * N) := by
        simpa only [Set.mem_Ioc, Nat.cast_mul] using hsupportn
      have hscale := (factorExtraction_mul_interval_iff hrR).1 hsuppSet
      have hscale' : (n : ℝ) ∈ Set.Ioc U (2 * U) := by
        simpa [U, hupperEq] using hscale
      have hmemDyadic : n ∈ factorExtractionDyadicInterval U :=
        (mem_factorExtractionDyadicInterval hU.le n).2 hscale'
      have hmem : n ∈ factorExtractionRealInterval lo hi :=
        (hinterval n).mp ⟨hnJ, hmemDyadic⟩
      exact hnNot hmem
    exact (Finset.sum_subset hsub hzero).symm
  rw [hsum]
  exact hlocal

/-- One allocation factor, with its label and cutoff retained. -/
noncomputable def factorExtractionAllocatedFactor {k : ℕ}
    (a : Fin k → ℕ → ℂ) (d s : Fin k → ℕ) (w : ℕ → ℂ)
    (i : Fin k) (m : ℕ) : ℂ :=
  a i (d i * m) * (if Nat.Coprime m (s i) then w m else 0)

private def factorExtractionSplitAt {k : ℕ} (i₀ : Fin k)
    (m : Fin k → ℕ) : (Fin k → ℕ) × ℕ :=
  (Function.update m i₀ 1, m i₀)

private def factorExtractionMergeAt {k : ℕ} (i₀ : Fin k)
    (p : (Fin k → ℕ) × ℕ) : Fin k → ℕ :=
  Function.update p.1 i₀ p.2

private theorem factorExtractionMergeSplitAt {k : ℕ} (i₀ : Fin k)
    (m : Fin k → ℕ) :
    factorExtractionMergeAt i₀ (factorExtractionSplitAt i₀ m) = m := by
  funext j
  by_cases hj : j = i₀
  · subst j
    simp [factorExtractionMergeAt, factorExtractionSplitAt]
  · simp [factorExtractionMergeAt, factorExtractionSplitAt, hj]

private theorem factorExtractionSplitMergeAt {k : ℕ} (i₀ : Fin k)
    (p : (Fin k → ℕ) × ℕ) (hp : p.1 i₀ = 1) :
    factorExtractionSplitAt i₀ (factorExtractionMergeAt i₀ p) = p := by
  apply Prod.ext
  · funext j
    by_cases hj : j = i₀
    · subst j
      simp [factorExtractionSplitAt, factorExtractionMergeAt, hp]
    · simp [factorExtractionSplitAt, factorExtractionMergeAt, hj]
  · simp [factorExtractionSplitAt, factorExtractionMergeAt]

private theorem factorExtractionNatProductUpdate {k : ℕ} (i₀ : Fin k)
    (u : Fin k → ℕ) (m : ℕ) :
    (∏ i : Fin k, Function.update u i₀ m i) =
      m * ∏ i ∈ Finset.univ.erase i₀, u i := by
  calc
    (∏ i : Fin k, Function.update u i₀ m i) =
        (∏ i ∈ Finset.univ.erase i₀, Function.update u i₀ m i) *
          Function.update u i₀ m i₀ := by
            exact (Finset.prod_erase_mul (s := Finset.univ)
              (f := fun i => Function.update u i₀ m i) (Finset.mem_univ _)).symm
    _ = (∏ i ∈ Finset.univ.erase i₀, u i) * m := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        exact Function.update_of_ne (Finset.mem_erase.mp hi).1 m u
      · simp
    _ = m * ∏ i ∈ Finset.univ.erase i₀, u i := by ac_rfl

private theorem factorExtractionComplexProductUpdate {k : ℕ}
    (i₀ : Fin k) (G : Fin k → ℕ → ℂ) (u : Fin k → ℕ) (m : ℕ) :
    (∏ i : Fin k, G i (Function.update u i₀ m i)) =
      G i₀ m * ∏ i ∈ Finset.univ.erase i₀, G i (u i) := by
  calc
    (∏ i : Fin k, G i (Function.update u i₀ m i)) =
        (∏ i ∈ Finset.univ.erase i₀, G i (Function.update u i₀ m i)) *
          G i₀ (Function.update u i₀ m i₀) := by
            exact (Finset.prod_erase_mul (s := Finset.univ)
              (f := fun i => G i (Function.update u i₀ m i))
              (Finset.mem_univ _)).symm
    _ = (∏ i ∈ Finset.univ.erase i₀, G i (u i)) * G i₀ m := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        exact congrArg (G i)
          (Function.update_of_ne (Finset.mem_erase.mp hi).1 m u)
      · simp
    _ = G i₀ m * ∏ i ∈ Finset.univ.erase i₀, G i (u i) := by ac_rfl

/-- The analytic estimate for one fixed labeled allocation.  It sums the
selected factor last over the exact intersection interval and bounds every
other labeled factor by its absolute inverse-square-root mass. -/
theorem factorExtractionFixedAllocationEstimate
    {k : ℕ} (i₀ : Fin k) (N B : Fin k → ℝ) (d s : Fin k → ℕ)
    (a : Fin k → ℕ → ℂ) (w : ℕ → ℂ) {ε x y : ℝ}
    (hN : ∀ i, 0 < N i) (hd : ∀ i, 0 < d i)
    (hB : ∀ i, 0 ≤ B i) (hε : 0 ≤ ε)
    (hcoeff : ∀ i m,
      m ∈ factorExtractionDyadicInterval (N i / (d i : ℝ)) →
      ‖a i (d i * m)‖ ≤ B i)
    (hw : ∀ m, 0 < m → ‖w m‖ ≤ 1 / Real.sqrt (m : ℝ))
    (hshort : ∀ u v : ℝ, 0 ≤ u →
      Set.Ioc u v ⊆ Set.Ioc (N i₀ / (d i₀ : ℝ))
        (2 * (N i₀ / (d i₀ : ℝ))) →
      ‖∑ m ∈ factorExtractionRealInterval u v,
        factorExtractionAllocatedFactor a d s w i₀ m‖ ≤
          ε * Real.sqrt (N i₀ / (d i₀ : ℝ)))
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖∑ m ∈ (Fintype.piFinset
        (fun i : Fin k => factorExtractionDyadicInterval
          (N i / (d i : ℝ)))).filter
          (fun m => x < (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ∧
            (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ≤ y),
        ∏ i : Fin k, factorExtractionAllocatedFactor a d s w i (m i)‖ ≤
      ε * Real.sqrt (N i₀ / (d i₀ : ℝ)) *
        ∏ i ∈ Finset.univ.erase i₀,
          (3 * B i * Real.sqrt (N i / (d i : ℝ))) := by
  classical
  let U : Fin k → ℝ := fun i => N i / (d i : ℝ)
  let S : Fin k → Finset ℕ := fun i => factorExtractionDyadicInterval (U i)
  let V : Finset (Fin k → ℕ) := Fintype.piFinset S
  let R : Finset (Fin k → ℕ) :=
    Fintype.piFinset (fun i => if i = i₀ then {1} else S i)
  let G : Fin k → ℕ → ℂ := fun i m =>
    factorExtractionAllocatedFactor a d s w i m
  let F : (Fin k → ℕ) → ℂ := fun m => ∏ i : Fin k, G i (m i)
  let P : (Fin k → ℕ) → Prop := fun m =>
    x < (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ∧
      (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ≤ y
  let Q : (Fin k → ℕ) × ℕ → Prop := fun p =>
    (((∏ i ∈ Finset.univ.erase i₀, p.1 i : ℕ) : ℝ) * (p.2 : ℝ)) ∈
      Set.Ioc x y
  have hUpos (i : Fin k) : 0 < U i := by
    dsimp [U]
    exact div_pos (hN i) (by exact_mod_cast (hd i))
  have hreindex :
      (∑ m ∈ V.filter P, F m) =
        ∑ p ∈ (R ×ˢ S i₀).filter Q, F (factorExtractionMergeAt i₀ p) := by
    refine Finset.sum_bij (fun m _ => factorExtractionSplitAt i₀ m) ?_ ?_ ?_ ?_
    · intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hmV, hmP⟩
      have hmCoords := Fintype.mem_piFinset.mp hmV
      have hother : (factorExtractionSplitAt i₀ m).1 ∈ R := by
        apply Fintype.mem_piFinset.mpr
        intro i
        by_cases hi : i = i₀
        · subst i
          simp [factorExtractionSplitAt]
        · have hmi : m i ∈ S i := hmCoords i
          simpa [R, factorExtractionSplitAt, hi] using
            (show Function.update m i₀ 1 i ∈ S i by
              simpa [Function.update_of_ne hi] using hmi)
      have hselected : m i₀ ∈ S i₀ := hmCoords i₀
      have hP' : P (factorExtractionMergeAt i₀
          (factorExtractionSplitAt i₀ m)) := by
        rw [factorExtractionMergeSplitAt]
        exact hmP
      have hQ : Q (factorExtractionSplitAt i₀ m) := by
        have hn := factorExtractionNatProductUpdate i₀
          (factorExtractionSplitAt i₀ m).1 (factorExtractionSplitAt i₀ m).2
        have hcast :
            (((∏ i : Fin k,
              factorExtractionMergeAt i₀ (factorExtractionSplitAt i₀ m) i : ℕ) : ℕ) : ℝ) =
              (((∏ i ∈ Finset.univ.erase i₀,
                (factorExtractionSplitAt i₀ m).1 i : ℕ) : ℝ) *
                ((factorExtractionSplitAt i₀ m).2 : ℝ)) := by
          change (((∏ i : Fin k,
              Function.update (factorExtractionSplitAt i₀ m).1 i₀
                (factorExtractionSplitAt i₀ m).2 i : ℕ) : ℕ) : ℝ) = _
          rw [hn]
          push_cast
          ring
        have hmem : P (factorExtractionMergeAt i₀
            (factorExtractionSplitAt i₀ m)) := hP'
        change x < _ ∧ _ ≤ y at hmem
        rw [hcast] at hmem
        exact hmem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hother, hselected⟩, hQ⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      have hmerge := congrArg (factorExtractionMergeAt i₀) heq
      simpa [factorExtractionMergeSplitAt] using hmerge
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpProd, hq⟩
      rcases Finset.mem_product.mp hpProd with ⟨hpR, hpS⟩
      have hpCoords := Fintype.mem_piFinset.mp hpR
      have hp0 : p.1 i₀ = 1 := by
        have h := hpCoords i₀
        simpa [R] using h
      refine ⟨factorExtractionMergeAt i₀ p, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
        · intro i
          by_cases hi : i = i₀
          · subst i
            simpa [factorExtractionMergeAt] using hpS
          · have hpi : p.1 i ∈ S i := by
              simpa [R, hi] using hpCoords i
            simpa [factorExtractionMergeAt, Function.update_of_ne hi] using hpi
        · have hn := factorExtractionNatProductUpdate i₀ p.1 p.2
          have hcast :
              (((∏ i : Fin k, factorExtractionMergeAt i₀ p i : ℕ) : ℕ) : ℝ) =
                (((∏ i ∈ Finset.univ.erase i₀, p.1 i : ℕ) : ℝ) * (p.2 : ℝ)) := by
            change (((∏ i : Fin k, Function.update p.1 i₀ p.2 i : ℕ) : ℕ) : ℝ) = _
            rw [hn]
            push_cast
            ring
          change x < _ ∧ _ ≤ y at hq ⊢
          rw [hcast]
          exact hq
      · exact factorExtractionSplitMergeAt i₀ p hp0
    · intro m hm
      rw [factorExtractionMergeSplitAt]
  have htarget :
      (∑ p ∈ (R ×ˢ S i₀).filter Q,
        F (factorExtractionMergeAt i₀ p)) =
        ∑ u ∈ R,
          (∑ m ∈ (S i₀).filter (fun m => Q (u, m)), G i₀ m) *
            ∏ j ∈ Finset.univ.erase i₀, G j (u j) := by
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hq : Q (u, m)
    · change (if Q (u, m) then F (factorExtractionMergeAt i₀ (u, m)) else 0) = _
      simp [hq]
      simpa [F, factorExtractionMergeAt] using
        (factorExtractionComplexProductUpdate i₀ G u m)
    · change (if Q (u, m) then F (factorExtractionMergeAt i₀ (u, m)) else 0) = _
      simp only [if_neg hq]
      simp [hq]
  have hmass (i : Fin k) :
      (∑ m ∈ S i, ‖G i m‖) ≤ 3 * B i * Real.sqrt (U i) := by
    apply factorExtractionDyadicTwistedCoefficientMass (hUpos i) (hB i)
    · intro m hm
      exact hcoeff i m (by simpa [S, U] using hm)
    · exact hw
  have hrestMass :
      (∑ u ∈ R, ∏ j ∈ Finset.univ.erase i₀, ‖G j (u j)‖) =
        ∏ j ∈ Finset.univ.erase i₀, ∑ m ∈ S j, ‖G j m‖ := by
    let T : Fin k → Finset ℕ := fun i => if i = i₀ then {1} else S i
    let H : Fin k → ℕ → ℝ := fun i m => if i = i₀ then 1 else ‖G i m‖
    calc
      (∑ u ∈ R, ∏ j ∈ Finset.univ.erase i₀, ‖G j (u j)‖) =
          ∑ u ∈ R, ∏ i : Fin k, H i (u i) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hu0 : u i₀ = 1 := by
          have huCoords := Fintype.mem_piFinset.mp (by simpa [R] using hu)
          have hc := huCoords i₀
          simpa [R] using hc
        calc
          (∏ j ∈ Finset.univ.erase i₀, ‖G j (u j)‖) =
              ∏ j ∈ Finset.univ.erase i₀, H j (u j) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
            simp [H, hji]
          _ = (∏ j ∈ Finset.univ.erase i₀, H j (u j)) * H i₀ (u i₀) := by
            simp [H, hu0]
          _ = ∏ i : Fin k, H i (u i) := by
            exact Finset.prod_erase_mul (s := Finset.univ)
              (f := fun i => H i (u i)) (Finset.mem_univ i₀)
      _ = ∏ i : Fin k, ∑ m ∈ T i, H i m := by
        rw [show R = Fintype.piFinset T by rfl]
        rw [← Finset.prod_univ_sum]
      _ = ∏ j ∈ Finset.univ.erase i₀, ∑ m ∈ S j, ‖G j m‖ := by
        rw [← Finset.prod_erase_mul (s := Finset.univ)
          (f := fun i : Fin k => ∑ m ∈ T i, H i m)
          (Finset.mem_univ i₀)]
        have hselectedSum : ∑ m ∈ T i₀, H i₀ m = 1 := by
          simp [T, H]
        rw [hselectedSum]
        rw [mul_one]
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
        simp [T, H, hji]
  have hprodBound :
      (∏ j ∈ Finset.univ.erase i₀, ∑ m ∈ S j, ‖G j m‖) ≤
        ∏ j ∈ Finset.univ.erase i₀,
          (3 * B j * Real.sqrt (U j)) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      positivity
    · intro j hj
      exact hmass j
  have hK : 0 ≤ ε * Real.sqrt (U i₀) :=
    mul_nonneg hε (Real.sqrt_nonneg _)
  have hbound :
      ‖∑ p ∈ (R ×ˢ S i₀).filter Q,
        F (factorExtractionMergeAt i₀ p)‖ ≤
        ε * Real.sqrt (U i₀) *
          ∏ j ∈ Finset.univ.erase i₀,
            (3 * B j * Real.sqrt (U j)) := by
    rw [htarget]
    calc
      ‖∑ u ∈ R,
          (∑ m ∈ (S i₀).filter (fun m => Q (u, m)), G i₀ m) *
            ∏ j ∈ Finset.univ.erase i₀, G j (u j)‖ ≤
          ∑ u ∈ R,
            ‖(∑ m ∈ (S i₀).filter (fun m => Q (u, m)), G i₀ m) *
              ∏ j ∈ Finset.univ.erase i₀, G j (u j)‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ R,
          (ε * Real.sqrt (U i₀)) *
            ‖∏ j ∈ Finset.univ.erase i₀, G j (u j)‖ := by
        apply Finset.sum_le_sum
        intro u hu
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have hUi : 0 < U i₀ := hUpos i₀
        let M : ℝ := ((∏ j ∈ Finset.univ.erase i₀, u j : ℕ) : ℝ)
        have huCoords := Fintype.mem_piFinset.mp (by simpa [R] using hu)
        have hMjpos : 0 < (∏ j ∈ Finset.univ.erase i₀, u j : ℕ) := by
          apply Finset.prod_pos
          intro j hj
          have hjS : u j ∈ S j := by
            have h := huCoords j
            simpa [R, Finset.mem_erase.mp hj] using h
          have hjmem := (mem_factorExtractionDyadicInterval (hUpos j).le (u j)).mp
            (by simpa [S] using hjS)
          exact_mod_cast (lt_trans (hUpos j) hjmem.1)
        have hMpos : 0 < M := by
          dsimp [M]
          exact_mod_cast hMjpos
        let lo := max (U i₀) (x / M)
        let hi := min (2 * U i₀) (y / M)
        have hy : 0 ≤ y := le_trans hx hxy
        have hlo : 0 ≤ lo := le_max_of_le_left (hUpos i₀).le
        have hhi : 0 ≤ hi := le_min (by positivity) (div_nonneg hy hMpos.le)
        have hfilter :
            (S i₀).filter (fun m => Q (u, m)) =
              factorExtractionRealInterval lo hi := by
          ext m
          simp only [Finset.mem_filter]
          have hQeq : Q (u, m) ↔ M * (m : ℝ) ∈ Set.Ioc x y := by
            simp [Q, M, Nat.cast_prod]
          rw [hQeq]
          simpa [S, U, lo, hi] using
            (factorExtractionDyadicProductInterval_iff
              (hUpos i₀) hMpos hx hxy m)
        have hsubset : Set.Ioc lo hi ⊆
            Set.Ioc (U i₀) (2 * U i₀) := by
          intro z hz
          exact ⟨lt_of_le_of_lt (le_max_left _ _) hz.1,
            le_trans hz.2 (min_le_left _ _)⟩
        have hselected := hshort lo hi hlo hsubset
        have hlocal :
            ‖∑ m ∈ (S i₀).filter (fun m => Q (u, m)), G i₀ m‖ ≤
              ε * Real.sqrt (U i₀) := by
          have hsumFilter := congrArg
            (fun t : Finset ℕ => ∑ m ∈ t, G i₀ m) hfilter
          rw [hsumFilter]
          simpa [G, U, factorExtractionAllocatedFactor] using hselected
        exact hlocal
      _ = (ε * Real.sqrt (U i₀)) *
          ∑ u ∈ R, ‖∏ j ∈ Finset.univ.erase i₀, G j (u j)‖ := by
        rw [Finset.mul_sum]
      _ = (ε * Real.sqrt (U i₀)) *
          ∏ j ∈ Finset.univ.erase i₀, ∑ m ∈ S j, ‖G j m‖ := by
        rw [← hrestMass]
        apply congrArg
        apply Finset.sum_congr rfl
        intro u hu
        simp
      _ ≤ (ε * Real.sqrt (U i₀)) *
          ∏ j ∈ Finset.univ.erase i₀,
            (3 * B j * Real.sqrt (U j)) :=
        mul_le_mul_of_nonneg_left hprodBound hK
  calc
    ‖∑ m ∈ (Fintype.piFinset
        (fun i : Fin k => factorExtractionDyadicInterval
          (N i / (d i : ℝ)))).filter
          (fun m => x < (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ∧
            (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ≤ y),
        ∏ i : Fin k, factorExtractionAllocatedFactor a d s w i (m i)‖ =
        ‖∑ m ∈ V.filter P, F m‖ := by rfl
    _ = ‖∑ p ∈ (R ×ˢ S i₀).filter Q,
          F (factorExtractionMergeAt i₀ p)‖ := by rw [hreindex]
    _ ≤ ε * Real.sqrt (U i₀) *
        ∏ j ∈ Finset.univ.erase i₀,
          (3 * B j * Real.sqrt (U j)) := hbound
    _ = ε * Real.sqrt (N i₀ / (d i₀ : ℝ)) *
        ∏ j ∈ Finset.univ.erase i₀,
          (3 * B j * Real.sqrt (N j / (d j : ℝ))) := by rfl

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.factorExtractionDyadicInverseSqrtMass
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionDyadicCoefficientMass
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionDyadicTwistedCoefficientMass
#print axioms FractionalPrimes.Literature.Twisted.mem_factorExtractionRealInterval
#print axioms FractionalPrimes.Literature.Twisted.factorExtraction_mul_interval_iff
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionDyadicProductInterval_iff
#print axioms FractionalPrimes.Literature.Twisted.shiftedConvolutionSmallFactor_one
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionFixedAllocationEstimate
