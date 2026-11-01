module

public import FractionalPrimes.Literature.Twisted.FlatGcdAllocation
public import FractionalPrimes.Literature.Twisted.ShiftedConvolutionFactorExtraction
public import FractionalPrimes.Literature.Twisted.NonunitTripleCharacterFactorization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Small factor extraction from a shifted convolution

This module checks the multiplicative Mellin weight, the finite interval
reindexing, the support-vanishing restriction, and the coordinatewise bounded
tuple constructor for blueprint item `ltw:factor-extraction`.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity

/-- The inverse-square-root twist on positive naturals, extended by zero at
zero. -/
def factorExtractionMellinWeight (χ : ℕ → ℂ) (t : ℝ) (m : ℕ) : ℂ :=
  if hm : 0 < m then χ m *
    (m : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) else 0

theorem factorExtractionMellinWeight_norm_le
    (χ : ℕ → ℂ) (t : ℝ)
    (hχ : ∀ m, 0 < m → ‖χ m‖ ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    ‖factorExtractionMellinWeight χ t m‖ ≤ 1 / Real.sqrt (m : ℝ) := by
  rw [factorExtractionMellinWeight, dif_pos hm, norm_mul]
  have hpow :
      ‖(m : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))‖ =
        1 / Real.sqrt (m : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos hm]
    have hre : ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)).re = (-1 / 2 : ℝ) := by
      simp [div_eq_mul_inv]
    rw [hre]
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hmR.le, ← Real.sqrt_eq_rpow]
    rw [one_div]
  rw [hpow]
  calc
    ‖χ m‖ * (1 / Real.sqrt (m : ℝ)) ≤
        1 * (1 / Real.sqrt (m : ℝ)) :=
          mul_le_mul_of_nonneg_right (hχ m hm) (by positivity)
    _ = 1 / Real.sqrt (m : ℝ) := by ring

theorem factorExtractionMellinWeight_mul
    (χ : ℕ → ℂ) (t : ℝ)
    (hχmul : ∀ m n, χ (m * n) = χ m * χ n)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    factorExtractionMellinWeight χ t (m * n) =
      factorExtractionMellinWeight χ t m * factorExtractionMellinWeight χ t n := by
  rw [factorExtractionMellinWeight, dif_pos (Nat.mul_pos hm hn),
    factorExtractionMellinWeight, dif_pos hm,
    factorExtractionMellinWeight, dif_pos hn,
    hχmul, positiveNatCpow_mul hm hn]
  ring

theorem factorExtractionMellinWeight_prod
    (χ : ℕ → ℂ) (t : ℝ)
    (hχone : χ 1 = 1)
    (hχmul : ∀ m n, χ (m * n) = χ m * χ n)
    {k : ℕ} (m : Fin k → ℕ) (hm : ∀ i, 0 < m i) :
    factorExtractionMellinWeight χ t (∏ i : Fin k, m i) =
      ∏ i : Fin k, factorExtractionMellinWeight χ t (m i) := by
  induction k with
  | zero =>
      simp [factorExtractionMellinWeight, hχone]
  | succ k ih =>
      rw [Fin.prod_univ_succ]
      have htail : 0 < ∏ i : Fin k, m i.succ :=
        Finset.prod_pos (fun i hi => hm i.succ)
      rw [factorExtractionMellinWeight_mul χ t hχmul (hm 0) htail]
      rw [ih (fun i => m i.succ) (fun i => hm i.succ)]
      rw [Fin.prod_univ_succ]

/-- Positive labeled tuples whose total product is at most `P`. -/
def factorExtractionBoundedPositiveTuple (k P : ℕ) :=
  {m : Fin k → PositiveInteger // ∏ i : Fin k, (m i).1 ≤ P}

def factorExtractionTupleProduct {k : ℕ}
    (m : Fin k → PositiveInteger) : ℕ :=
  ∏ i : Fin k, (m i).1

theorem factorExtractionBoundedPositiveTuple_finite (k P : ℕ) :
    Finite (factorExtractionBoundedPositiveTuple k P) := by
  apply Finite.of_injective
    (fun m i =>
      (⟨(m.1 i).1, Nat.lt_succ_of_le
        ((Finset.single_le_prod (s := Finset.univ)
          (f := fun j : Fin k => (m.1 j).1)
          (fun j hj => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (m.1 j).2)) (Finset.mem_univ i)).trans m.2)⟩ : Fin (P + 1)))
  intro m n h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrArg Fin.val (congrFun h i)

noncomputable instance factorExtractionBoundedPositiveTuple_fintype
    (k P : ℕ) : Fintype (factorExtractionBoundedPositiveTuple k P) := by
  haveI : Finite (factorExtractionBoundedPositiveTuple k P) :=
    factorExtractionBoundedPositiveTuple_finite k P
  exact Fintype.ofFinite _

noncomputable def factorExtractionTupleIntervalEquiv
    (k : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (Σ n : {n : ℕ // n ∈ factorExtractionRealInterval x y},
      divisorFactorTuples k n.1) ≃
    {m : factorExtractionBoundedPositiveTuple k (Nat.floor y) //
      x < (factorExtractionTupleProduct m.1 : ℝ)} := by
  classical
  let I := factorExtractionRealInterval x y
  refine
    { toFun := fun q => ?_
      invFun := fun m => ?_
      left_inv := ?_
      right_inv := ?_ }
  · rcases q with ⟨⟨n, hnI⟩, m⟩
    have hprod : ∏ i : Fin k, (m.1 i).1 = n := m.2
    have hnle : n ≤ Nat.floor y := by
      apply Nat.le_floor
      have hnmem := (mem_factorExtractionRealInterval
        hx (le_trans hx hxy) n).mp hnI
      exact hnmem.2
    refine ⟨⟨m.1, ?_⟩, ?_⟩
    · simpa [factorExtractionTupleProduct, hprod] using hnle
    · change x < (factorExtractionTupleProduct m.1 : ℝ)
      unfold factorExtractionTupleProduct
      rw [hprod]
      exact (mem_factorExtractionRealInterval hx
        (le_trans hx hxy) n).mp hnI |>.1
  · rcases m with ⟨m, hmI⟩
    let n := ∏ i : Fin k, (m.1 i).1
    have hnpos : 0 < n := Finset.prod_pos (fun i hi => (m.1 i).2)
    have hnI : n ∈ I := by
      apply (mem_factorExtractionRealInterval hx (le_trans hx hxy) n).mpr
      refine ⟨?_, ?_⟩
      · simpa [n, factorExtractionTupleProduct] using hmI
      · exact le_trans (Nat.cast_le.mpr m.2)
          (Nat.floor_le (le_trans hx hxy))
    exact ⟨⟨n, hnI⟩, ⟨m.1, rfl⟩⟩
  · rintro ⟨⟨n, hnI⟩, m⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact m.2
    · rfl
  · intro m
    apply Subtype.ext
    apply Subtype.ext
    funext i
    rfl

theorem factorExtractionTupleIntervalEquiv_symm_coordinate
    (k : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (b : {m : factorExtractionBoundedPositiveTuple k (Nat.floor y) //
      x < (factorExtractionTupleProduct m.1 : ℝ)}) (i : Fin k) :
    (((factorExtractionTupleIntervalEquiv k x y hx hxy).symm b).2.1 i).1 =
      (b.1.1 i).1 := by
  have h := congrArg Subtype.val
    ((factorExtractionTupleIntervalEquiv k x y hx hxy).apply_symm_apply b)
  have hvec := congrArg
    (fun q : factorExtractionBoundedPositiveTuple k (Nat.floor y) => q.1) h
  exact congrArg (fun q : Fin k → PositiveInteger => (q i).1) hvec

theorem factorExtractionTupleIntervalReindex
    (k : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (F : ∀ n : ℕ, divisorFactorTuples k n → ℂ) :
    (∑ n ∈ factorExtractionRealInterval x y,
      ∑ m : divisorFactorTuples k n, F n m) =
      ∑ m : {m : factorExtractionBoundedPositiveTuple k (Nat.floor y) //
        x < (factorExtractionTupleProduct m.1 : ℝ)},
        let q := (factorExtractionTupleIntervalEquiv k x y hx hxy).symm m
        F q.1.1 q.2 := by
  classical
  let I := factorExtractionRealInterval x y
  let S := Σ n : {n : ℕ // n ∈ I}, divisorFactorTuples k n.1
  let T := {m : factorExtractionBoundedPositiveTuple k (Nat.floor y) //
    x < (factorExtractionTupleProduct m.1 : ℝ)}
  let e := factorExtractionTupleIntervalEquiv k x y hx hxy
  have hsubtype :
      (∑ n : {n : ℕ // n ∈ I},
        ∑ m : divisorFactorTuples k n.1, F n.1 m) =
      ∑ n ∈ I, ∑ m : divisorFactorTuples k n, F n m := by
    let f : ℕ → ℂ := fun n => ∑ m : divisorFactorTuples k n, F n m
    calc
      (∑ n : {n : ℕ // n ∈ I}, f n.1) =
          ∑ n ∈ I.attach, f n.1 := by rw [← Finset.attach_eq_univ]
      _ = ∑ n ∈ I, f n := Finset.sum_attach I f
      _ = _ := rfl
  rw [← hsubtype]
  let G : S → ℂ := fun q => F q.1.1 q.2
  have hsigma :
      (∑ n : {n : ℕ // n ∈ I},
        ∑ m : divisorFactorTuples k n.1, F n.1 m) =
        ∑ q : S, G q := by
    simpa [G, S] using (Fintype.sum_sigma G).symm
  rw [hsigma]
  let H : T → ℂ := fun m =>
    let q := e.symm m
    F q.1.1 q.2
  apply Fintype.sum_equiv e G H
  intro q
  change F q.1.1 q.2 = F (e.symm (e q)).1.1 (e.symm (e q)).2
  rw [e.symm_apply_apply]

/-- Restrict a bounded positive-tuple sum to tuples whose coordinates meet
their prescribed support sets. Terms outside that support vanish
coordinatewise. -/
theorem factorExtractionSupportedBoundedTupleSum
    (k P : ℕ) (S : Fin k → Finset ℕ) (x : ℝ)
    (F : factorExtractionBoundedPositiveTuple k P → ℂ)
    (hzero : ∀ b : factorExtractionBoundedPositiveTuple k P,
      x < (factorExtractionTupleProduct b.1 : ℝ) →
      (∃ i, (b.1 i).1 ∉ S i) → F b = 0) :
    (∑ b ∈ (Finset.univ : Finset (factorExtractionBoundedPositiveTuple k P)).filter
        (fun b => x < (factorExtractionTupleProduct b.1 : ℝ)), F b) =
      ∑ b ∈ (Finset.univ : Finset (factorExtractionBoundedPositiveTuple k P)).filter
        (fun b => x < (factorExtractionTupleProduct b.1 : ℝ) ∧
          ∀ i, (b.1 i).1 ∈ S i), F b := by
  classical
  let A : Finset (factorExtractionBoundedPositiveTuple k P) :=
    (Finset.univ).filter
      (fun b => x < (factorExtractionTupleProduct b.1 : ℝ))
  let W : Finset (factorExtractionBoundedPositiveTuple k P) :=
    (Finset.univ).filter (fun b =>
      x < (factorExtractionTupleProduct b.1 : ℝ) ∧
        ∀ i, (b.1 i).1 ∈ S i)
  have hWsubset : W ⊆ A := by
    intro b hb
    rcases Finset.mem_filter.mp hb with ⟨_, ⟨hlower, _⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlower⟩
  have hzeroW : ∀ b ∈ A, b ∉ W → F b = 0 := by
    intro b hb hnot
    have hlower : x < (factorExtractionTupleProduct b.1 : ℝ) :=
      (Finset.mem_filter.mp hb).2
    have hcoords : ¬ ∀ i, (b.1 i).1 ∈ S i := by
      intro hS
      apply hnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hlower, hS⟩⟩
    obtain ⟨i, hi⟩ := not_forall.mp hcoords
    exact hzero b hlower ⟨i, hi⟩
  exact (Finset.sum_subset hWsubset hzeroW).symm

/-- Convert a natural tuple with coordinatewise support evidence to a
positive-integer tuple. -/
def factorExtractionSupportedPositiveTuple
    (k : ℕ) (S : Fin k → Finset ℕ)
    (hSpos : ∀ i m, m ∈ S i → 0 < m)
    (m : Fin k → ℕ) (hm : ∀ i, m i ∈ S i) : Fin k → PositiveInteger :=
  fun i => ⟨m i, hSpos i (m i) (hm i)⟩

theorem factorExtractionSupportedPositiveTuple_coordinate
    (k : ℕ) (S : Fin k → Finset ℕ)
    (hSpos : ∀ i m, m ∈ S i → 0 < m)
    (m : Fin k → ℕ) (hm : ∀ i, m i ∈ S i) (i : Fin k) :
    (factorExtractionSupportedPositiveTuple k S hSpos m hm i).1 = m i := by
  rfl

theorem factorExtractionSupportedPositiveTuple_product
    (k : ℕ) (S : Fin k → Finset ℕ)
    (hSpos : ∀ i m, m ∈ S i → 0 < m)
    (m : Fin k → ℕ) (hm : ∀ i, m i ∈ S i) :
    factorExtractionTupleProduct
        (factorExtractionSupportedPositiveTuple k S hSpos m hm) =
      ∏ i : Fin k, m i := by
  unfold factorExtractionTupleProduct
  apply Finset.prod_congr rfl
  intro i hi
  exact factorExtractionSupportedPositiveTuple_coordinate
    k S hSpos m hm i

/-- The selected product box has a label-preserving lift to bounded positive
tuples. The product bound is proved separately from the coordinate support
construction. -/
noncomputable def factorExtractionDyadicTupleLift
    (k P : ℕ) (S : Fin k → Finset ℕ) (x y : ℝ)
    (hPy : P = Nat.floor y) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hSpos : ∀ i m, m ∈ S i → 0 < m)
    (m : {m : Fin k → ℕ // m ∈ (Fintype.piFinset S).filter
      (fun m => x < ((∏ i : Fin k, m i : ℕ) : ℝ) ∧
        ((∏ i : Fin k, m i : ℕ) : ℕ) ≤ y)}) :
    factorExtractionBoundedPositiveTuple k P := by
  classical
  let hm : ∀ i, m.1 i ∈ S i :=
    fun i => Fintype.mem_piFinset.mp (Finset.mem_filter.mp m.2).1 i
  let q : Fin k → PositiveInteger :=
    factorExtractionSupportedPositiveTuple k S hSpos m.1 hm
  have hreal : (factorExtractionTupleProduct q : ℝ) ≤ y := by
    rw [show factorExtractionTupleProduct q = ∏ i : Fin k, m.1 i by
      exact factorExtractionSupportedPositiveTuple_product k S hSpos m.1 hm]
    exact (Finset.mem_filter.mp m.2).2.2
  have hbound : factorExtractionTupleProduct q ≤ P := by
    rw [hPy]
    exact Nat.le_floor hreal
  exact ⟨q, hbound⟩

/-- A selected natural tuple has a bounded positive realization whose
coordinate values agree with it. This existential API keeps the coordinate
fact separate from the proof of the product bound. -/
theorem factorExtractionDyadicTuple_exists
    (k P : ℕ) (S : Fin k → Finset ℕ) (x y : ℝ)
    (hPy : P = Nat.floor y) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hSpos : ∀ i m, m ∈ S i → 0 < m)
    (m : {m : Fin k → ℕ // m ∈ (Fintype.piFinset S).filter
      (fun m => x < ((∏ i : Fin k, m i : ℕ) : ℝ) ∧
        ((∏ i : Fin k, m i : ℕ) : ℕ) ≤ y)}) :
    ∃ q : factorExtractionBoundedPositiveTuple k P,
      ∀ i, (q.1 i).1 = m.1 i := by
  classical
  let hm : ∀ i, m.1 i ∈ S i :=
    fun i => Fintype.mem_piFinset.mp (Finset.mem_filter.mp m.2).1 i
  let q : Fin k → PositiveInteger :=
    factorExtractionSupportedPositiveTuple k S hSpos m.1 hm
  have hreal : (factorExtractionTupleProduct q : ℝ) ≤ y := by
    rw [show factorExtractionTupleProduct q = ∏ i : Fin k, m.1 i by
      exact factorExtractionSupportedPositiveTuple_product k S hSpos m.1 hm]
    exact (Finset.mem_filter.mp m.2).2.2
  have hbound : factorExtractionTupleProduct q ≤ P := by
    rw [hPy]
    exact Nat.le_floor hreal
  refine ⟨⟨q, hbound⟩, ?_⟩
  intro i
  exact factorExtractionSupportedPositiveTuple_coordinate k S hSpos m.1 hm i

/-- Reindex the support-restricted bounded tuple sum by the selected
coordinatewise product box. -/
theorem factorExtractionSupportedBoundedTupleSum_eq_dyadicBox
    (k P : ℕ) (S : Fin k → Finset ℕ) (x y : ℝ)
    (hPy : P = Nat.floor y) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hSpos : ∀ i m, m ∈ S i → 0 < m)
    (F : factorExtractionBoundedPositiveTuple k P → ℂ)
    (hzero : ∀ b : factorExtractionBoundedPositiveTuple k P,
      x < (factorExtractionTupleProduct b.1 : ℝ) →
      (∃ i, (b.1 i).1 ∉ S i) → F b = 0) :
    (∑ b ∈ (Finset.univ : Finset (factorExtractionBoundedPositiveTuple k P)).filter
        (fun b => x < (factorExtractionTupleProduct b.1 : ℝ)), F b) =
      ∑ m : {m : Fin k → ℕ // m ∈ (Fintype.piFinset S).filter
        (fun m => x < ((∏ i : Fin k, m i : ℕ) : ℝ) ∧
          ((∏ i : Fin k, m i : ℕ) : ℕ) ≤ y)},
        F (Classical.choose
          (factorExtractionDyadicTuple_exists k P S x y hPy hx hxy hSpos m)) := by
  classical
  let V : Finset (Fin k → ℕ) :=
    (Fintype.piFinset S).filter
      (fun m => x < ((∏ i : Fin k, m i : ℕ) : ℝ) ∧
        ((∏ i : Fin k, m i : ℕ) : ℕ) ≤ y)
  let A : Finset (factorExtractionBoundedPositiveTuple k P) :=
    (Finset.univ).filter
      (fun b => x < (factorExtractionTupleProduct b.1 : ℝ))
  let W : Finset (factorExtractionBoundedPositiveTuple k P) :=
    (Finset.univ).filter (fun b =>
      x < (factorExtractionTupleProduct b.1 : ℝ) ∧
        ∀ i, (b.1 i).1 ∈ S i)
  have hrestrict : (∑ b ∈ A, F b) = ∑ b ∈ W, F b := by
    simpa [A, W] using
      factorExtractionSupportedBoundedTupleSum k P S x F hzero
  let lift : {m : Fin k → ℕ // m ∈ V} →
      factorExtractionBoundedPositiveTuple k P := fun m =>
    Classical.choose
      (factorExtractionDyadicTuple_exists k P S x y hPy hx hxy hSpos m)
  have hliftCoord : ∀ m : {m : Fin k → ℕ // m ∈ V}, ∀ i,
      ((lift m).1 i).1 = m.1 i := by
    intro m i
    dsimp [lift]
    exact (Classical.choose_spec
      (factorExtractionDyadicTuple_exists k P S x y hPy hx hxy hSpos m)) i
  have hWimage : W = V.attach.image lift := by
    apply Finset.ext
    intro b
    constructor
    · intro hb
      rcases Finset.mem_filter.mp hb with ⟨_, ⟨hlower, hS⟩⟩
      let v : Fin k → ℕ := fun i => (b.1 i).1
      have hvV : v ∈ V := by
        apply Finset.mem_filter.mpr
        refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
        · exact hS
        · constructor
          · simpa [v, factorExtractionTupleProduct] using hlower
          · have hbound : factorExtractionTupleProduct b.1 ≤ P := b.2
            calc
              (factorExtractionTupleProduct b.1 : ℝ) ≤ (P : ℝ) :=
                Nat.cast_le.mpr hbound
              _ = (Nat.floor y : ℝ) := by rw [hPy]
              _ ≤ y := Nat.floor_le (le_trans hx hxy)
      refine Finset.mem_image.mpr ⟨⟨v, hvV⟩, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      funext i
      apply Subtype.ext
      rw [hliftCoord]
    · intro hb
      rcases Finset.mem_image.mp hb with ⟨m, hm, hmb⟩
      rcases Finset.mem_filter.mp m.2 with ⟨hvbox, hvprod⟩
      have hvcoords := Fintype.mem_piFinset.mp hvbox
      have hprod : factorExtractionTupleProduct (lift m).1 =
          ∏ i : Fin k, m.1 i := by
        unfold factorExtractionTupleProduct
        apply Finset.prod_congr rfl
        intro i hi
        exact hliftCoord m i
      have hcoords : ∀ i, ((lift m).1 i).1 ∈ S i := by
        intro i
        rw [hliftCoord]
        exact hvcoords i
      have hlower : x < (factorExtractionTupleProduct (lift m).1 : ℝ) := by
        rw [hprod]
        exact hvprod.1
      have hWlift : lift m ∈ W :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hlower, hcoords⟩⟩
      rw [← hmb]
      exact hWlift
  have hsumImage :
      (∑ b ∈ W, F b) = ∑ m : {m : Fin k → ℕ // m ∈ V}, F (lift m) := by
    rw [hWimage, Finset.sum_image]
    · rw [← Finset.attach_eq_univ]
    · intro m hm n hn hmn
      apply Subtype.ext
      funext i
      have hcoord := congrArg
        (fun q : factorExtractionBoundedPositiveTuple k P => (q.1 i).1) hmn
      rw [hliftCoord m i, hliftCoord n i] at hcoord
      exact hcoord
  calc
    (∑ b ∈ A, F b) = ∑ b ∈ W, F b := hrestrict
    _ = ∑ m : {m : Fin k → ℕ // m ∈ V}, F (lift m) := hsumImage

/-- Sum a uniform bound over the labeled ordered factorizations of `r`.
The factor count is exactly the divisor function `d_k(r)`. -/
theorem factorExtractionAllocationSum_norm_le
    {k r : ℕ} (hr : 0 < r)
    (F : divisorFactorTuples k r → ℂ) (C : ℝ)
    (hF : ∀ d, ‖F d‖ ≤ C) :
    ‖∑ d : divisorFactorTuples k r, F d‖ ≤
      (divisorFunction k ⟨r, hr⟩ : ℝ) * C := by
  classical
  calc
    ‖∑ d : divisorFactorTuples k r, F d‖ ≤
        ∑ d : divisorFactorTuples k r, ‖F d‖ := norm_sum_le _ _
    _ ≤ ∑ _d : divisorFactorTuples k r, C := by
      apply Finset.sum_le_sum
      intro d hd
      exact hF d
    _ = (Fintype.card (divisorFactorTuples k r) : ℝ) * C := by
      simp
    _ = (divisorFunction k ⟨r, hr⟩ : ℝ) * C := by
      rw [← divisorFunction_eq_card_factorTuples k ⟨r, hr⟩]

/-- The exact residual modulus attached to a labeled allocation at index `i`.
It is the quotient by the prefix product through that index. -/
def factorExtractionAllocationResidual {k r : ℕ}
    (d : divisorFactorTuples k r) (i : Fin k) : ℕ :=
  r / ∏ j ∈ Finset.Iic i, (d.1 j).1

/-- Expand a convolution product on a finite positive interval as a sum over
the exact labeled gcd allocations and the positive factor tuples. -/
theorem factorExtractionFlatConvolutionSum
    (fs : List (ArithmeticFunction ℂ)) {r : ℕ} (hr : 0 < r)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (W : ℕ → ℂ) :
    (∑ n ∈ factorExtractionRealInterval x y,
      (fs.prod) (r * n) * W n) =
      ∑ d : divisorFactorTuples fs.length r,
        ∑ n ∈ factorExtractionRealInterval x y,
          ∑ m : divisorFactorTuples fs.length n,
            (if ∀ i : Fin fs.length,
                Nat.Coprime (m.1 i).1 (factorExtractionAllocationResidual d i)
              then ∏ i : Fin fs.length,
                (fs.get i) ((d.1 i).1 * (m.1 i).1)
              else 0) * W n := by
  classical
  let A : Finset ℕ := factorExtractionRealInterval x y
  let G : ℕ → divisorFactorTuples fs.length r → ℂ := fun n d =>
    ∑ m : divisorFactorTuples fs.length n,
      (if ∀ i : Fin fs.length,
          Nat.Coprime (m.1 i).1 (factorExtractionAllocationResidual d i)
        then ∏ i : Fin fs.length,
          (fs.get i) ((d.1 i).1 * (m.1 i).1)
        else 0) * W n
  have hpoint (n : ℕ) (hnA : n ∈ A) :
      (fs.prod) (r * n) = ∑ d : divisorFactorTuples fs.length r,
        ∑ m : divisorFactorTuples fs.length n,
          (if ∀ i : Fin fs.length,
              Nat.Coprime (m.1 i).1 (factorExtractionAllocationResidual d i)
            then ∏ i : Fin fs.length,
              (fs.get i) ((d.1 i).1 * (m.1 i).1)
            else 0) := by
    have hnpos : 0 < n := by
      have hnreal := (mem_factorExtractionRealInterval hx
        (le_trans hx hxy) n).mp (by simpa [A] using hnA)
      have hcast : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt hx hnreal.1
      exact_mod_cast hcast
    rw [flatGcdAllocation fs hr hnpos]
    rfl
  calc
    (∑ n ∈ factorExtractionRealInterval x y,
        (fs.prod) (r * n) * W n) =
        ∑ n ∈ A, ∑ d : divisorFactorTuples fs.length r, G n d := by
          apply Finset.sum_congr rfl
          intro n hnA
          rw [hpoint n hnA]
          simp only [G, Finset.sum_mul]
    _ = ∑ d : divisorFactorTuples fs.length r, ∑ n ∈ A, G n d := by
          rw [Finset.sum_comm]
    _ = ∑ d : divisorFactorTuples fs.length r,
        ∑ n ∈ factorExtractionRealInterval x y,
          ∑ m : divisorFactorTuples fs.length n,
            (if ∀ i : Fin fs.length,
                Nat.Coprime (m.1 i).1 (factorExtractionAllocationResidual d i)
              then ∏ i : Fin fs.length,
                (fs.get i) ((d.1 i).1 * (m.1 i).1)
              else 0) * W n := by
          simp [A, G]

/-- After multiplying the flat gcd-allocation term by the multiplicative
Mellin weight, it is the product of the individually allocated factors. -/
theorem factorExtractionFlatTerm_mul_weight
    {r n : ℕ} (fs : List (ArithmeticFunction ℂ))
    (d : divisorFactorTuples fs.length r)
    (m : divisorFactorTuples fs.length n)
    (χ : ℕ → ℂ) (t : ℝ)
    (hχone : χ 1 = 1)
    (hχmul : ∀ a b, χ (a * b) = χ a * χ b) :
    (if hcut : ∀ i : Fin fs.length,
        Nat.Coprime (m.1 i).1 (factorExtractionAllocationResidual d i)
      then ∏ i : Fin fs.length, (fs.get i) ((d.1 i).1 * (m.1 i).1)
      else 0) *
        factorExtractionMellinWeight χ t n =
      ∏ i : Fin fs.length,
        factorExtractionAllocatedFactor
          (fun i n => fs.get i n)
          (fun i => (d.1 i).1)
          (fun i => factorExtractionAllocationResidual d i)
          (factorExtractionMellinWeight χ t) i (m.1 i).1 := by
  classical
  have hprod : (∏ i : Fin fs.length, (m.1 i).1) = n := m.2
  have hweight : factorExtractionMellinWeight χ t n =
      ∏ i : Fin fs.length, factorExtractionMellinWeight χ t (m.1 i).1 := by
    exact (congrArg (factorExtractionMellinWeight χ t) hprod).symm.trans
      (factorExtractionMellinWeight_prod χ t hχone hχmul
        (fun i => (m.1 i).1)
        (fun i => (m.1 i).2))
  rw [hweight]
  by_cases hcut : ∀ i : Fin fs.length,
      Nat.Coprime (m.1 i).1 (factorExtractionAllocationResidual d i)
  · simp only [dif_pos hcut]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simp [factorExtractionAllocatedFactor, hcut i]
  · simp only [dif_neg hcut]
    obtain ⟨i, hi⟩ := not_forall.mp hcut
    let G : Fin fs.length → ℂ := fun j => factorExtractionAllocatedFactor
        (fun i n => fs.get i n)
        (fun i => (d.1 i).1)
        (fun i => factorExtractionAllocationResidual d i)
        (factorExtractionMellinWeight χ t) j (m.1 j).1
    have hzero : G i = 0 := by
      dsimp [G, factorExtractionAllocatedFactor]
      rw [if_neg hi]
      simp
    have hprodzero : (∏ j : Fin fs.length, G j) = 0 := by
      simpa using Finset.prod_eq_zero (Finset.mem_univ i) hzero
    rw [hprodzero]
    simp

/-- For one gcd allocation, the finite interval sum is exactly a sum over
bounded positive labeled tuples, with the Mellin weight split among factors. -/
theorem factorExtractionAllocationTupleReindex
    (fs : List (ArithmeticFunction ℂ)) {r : ℕ}
    (d : divisorFactorTuples fs.length r)
    (χ : ℕ → ℂ) (t : ℝ) (hχone : χ 1 = 1)
    (hχmul : ∀ a b, χ (a * b) = χ a * χ b)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (∑ n ∈ factorExtractionRealInterval x y,
      ∑ m : divisorFactorTuples fs.length n,
        (if ∀ i : Fin fs.length,
            Nat.Coprime (m.1 i).1 (factorExtractionAllocationResidual d i)
          then ∏ i : Fin fs.length,
            (fs.get i) ((d.1 i).1 * (m.1 i).1)
          else 0) * factorExtractionMellinWeight χ t n) =
      ∑ b : {b : factorExtractionBoundedPositiveTuple fs.length (Nat.floor y) //
          x < (factorExtractionTupleProduct b.1 : ℝ)},
        ∏ i : Fin fs.length,
          factorExtractionAllocatedFactor
            (fun i n => fs.get i n)
            (fun i => (d.1 i).1)
            (fun i => factorExtractionAllocationResidual d i)
            (factorExtractionMellinWeight χ t) i (b.1.1 i).1 := by
  classical
  let F : ∀ n : ℕ, divisorFactorTuples fs.length n → ℂ := fun n m =>
    (if ∀ i : Fin fs.length,
        Nat.Coprime (m.1 i).1 (factorExtractionAllocationResidual d i)
      then ∏ i : Fin fs.length,
        (fs.get i) ((d.1 i).1 * (m.1 i).1)
      else 0) * factorExtractionMellinWeight χ t n
  rw [factorExtractionTupleIntervalReindex fs.length x y hx hxy F]
  apply Finset.sum_congr rfl
  intro b hb
  dsimp [F]
  let q := (factorExtractionTupleIntervalEquiv fs.length x y hx hxy).symm b
  calc
    (if hcut : ∀ i : Fin fs.length,
          Nat.Coprime (q.2.1 i).1 (factorExtractionAllocationResidual d i)
        then ∏ i : Fin fs.length,
          (fs.get i) ((d.1 i).1 * (q.2.1 i).1)
        else 0) * factorExtractionMellinWeight χ t q.1.1 =
        ∏ i : Fin fs.length,
          factorExtractionAllocatedFactor
            (fun i n => fs.get i n)
            (fun i => (d.1 i).1)
            (fun i => factorExtractionAllocationResidual d i)
            (factorExtractionMellinWeight χ t) i (q.2.1 i).1 := by
              exact factorExtractionFlatTerm_mul_weight fs d q.2 χ t hχone hχmul
    _ = ∏ i : Fin fs.length,
          factorExtractionAllocatedFactor
            (fun i n => fs.get i n)
            (fun i => (d.1 i).1)
            (fun i => factorExtractionAllocationResidual d i)
            (factorExtractionMellinWeight χ t) i (b.1.1 i).1 := by
              apply Finset.prod_congr rfl
              intro i hi
              exact congrArg
                (factorExtractionAllocatedFactor
                  (fun i n => fs.get i n)
                  (fun i => (d.1 i).1)
                  (fun i => factorExtractionAllocationResidual d i)
                  (factorExtractionMellinWeight χ t) i)
                (factorExtractionTupleIntervalEquiv_symm_coordinate
                  fs.length x y hx hxy b i)

/-- A single exact gcd allocation obeys the small-factor estimate once the
original factors are supported on their prescribed dyadic intervals. -/
theorem factorExtractionAllocationEstimate
    {k : ℕ} (i₀ : Fin k) (N B : Fin k → ℝ) (d s : Fin k → ℕ)
    (a : Fin k → ℕ → ℂ) (w : ℕ → ℂ) {ε x y : ℝ}
    (hN : ∀ i, 0 < N i) (hd : ∀ i, 0 < d i)
    (hB : ∀ i, 0 ≤ B i) (hε : 0 ≤ ε)
    (hcoeff : ∀ i m,
      m ∈ factorExtractionDyadicInterval (N i / (d i : ℝ)) →
      ‖a i (d i * m)‖ ≤ B i)
    (hsupport : ∀ i n, a i n ≠ 0 →
      N i < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N i)
    (hw : ∀ m, 0 < m → ‖w m‖ ≤ 1 / Real.sqrt (m : ℝ))
    (hshort : ∀ u v : ℝ, 0 ≤ u →
      Set.Ioc u v ⊆ Set.Ioc (N i₀ / (d i₀ : ℝ))
        (2 * (N i₀ / (d i₀ : ℝ))) →
      ‖∑ m ∈ factorExtractionRealInterval u v,
        factorExtractionAllocatedFactor a d s w i₀ m‖ ≤
          ε * Real.sqrt (N i₀ / (d i₀ : ℝ)))
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖∑ b ∈ (Finset.univ : Finset (factorExtractionBoundedPositiveTuple k (Nat.floor y))).filter
        (fun b => x < (factorExtractionTupleProduct b.1 : ℝ)),
        ∏ i : Fin k,
          factorExtractionAllocatedFactor a d s w i (b.1 i).1‖ ≤
      ε * Real.sqrt (N i₀ / (d i₀ : ℝ)) *
        ∏ j ∈ Finset.univ.erase i₀,
          (3 * B j * Real.sqrt (N j / (d j : ℝ))) := by
  classical
  let U : Fin k → ℝ := fun i => N i / (d i : ℝ)
  let S : Fin k → Finset ℕ := fun i => factorExtractionDyadicInterval (U i)
  let F : factorExtractionBoundedPositiveTuple k (Nat.floor y) → ℂ :=
    fun b => ∏ i : Fin k, factorExtractionAllocatedFactor a d s w i (b.1 i).1
  have hUpos (i : Fin k) : 0 < U i := by
    dsimp [U]
    exact div_pos (hN i) (by exact_mod_cast hd i)
  have hSpos : ∀ i m, m ∈ S i → 0 < m := by
    intro i m hm
    have hmem := (mem_factorExtractionDyadicInterval (hUpos i).le m).mp
      (by simpa [S, U] using hm)
    have hreal : (0 : ℝ) < (m : ℝ) := lt_trans (hUpos i) hmem.1
    exact_mod_cast hreal
  have hzero : ∀ b : factorExtractionBoundedPositiveTuple k (Nat.floor y),
      x < (factorExtractionTupleProduct b.1 : ℝ) →
      (∃ i, (b.1 i).1 ∉ S i) → F b = 0 := by
    intro b _hlower hbad
    obtain ⟨i, hi⟩ := hbad
    let m : ℕ := (b.1 i).1
    have hcoeffZero : a i (d i * m) = 0 := by
      by_contra hne
      have hsupp := hsupport i (d i * m) hne
      have hscaled : ((d i : ℝ) * (m : ℝ)) ∈ Set.Ioc (N i) (2 * N i) := by
        simpa only [Set.mem_Ioc, Nat.cast_mul] using hsupp
      have hrR : 0 < (d i : ℝ) := by exact_mod_cast hd i
      have hscale := (factorExtraction_mul_interval_iff hrR).1 hscaled
      have hscale' : U i < (m : ℝ) ∧ (m : ℝ) ≤ 2 * U i := by
        constructor
        · simpa [U] using hscale.1
        · calc
            (m : ℝ) ≤ (2 * N i) / (d i : ℝ) := hscale.2
            _ = 2 * U i := by dsimp [U]; ring
      have hmem : m ∈ factorExtractionDyadicInterval (U i) :=
        (mem_factorExtractionDyadicInterval (hUpos i).le m).2 hscale'
      exact hi (by simpa [S] using hmem)
    have hfactor : factorExtractionAllocatedFactor a d s w i m = 0 := by
      simp [factorExtractionAllocatedFactor, hcoeffZero]
    have hprodzero :
        (∏ j : Fin k,
          factorExtractionAllocatedFactor a d s w j (b.1 j).1) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simpa [m] using hfactor
    simpa [F] using hprodzero
  have hbox := factorExtractionSupportedBoundedTupleSum_eq_dyadicBox
    k (Nat.floor y) S x y rfl hx hxy hSpos F hzero
  let T : Finset (factorExtractionBoundedPositiveTuple k (Nat.floor y)) :=
    (Finset.univ).filter
      (fun b => x < (factorExtractionTupleProduct b.1 : ℝ))
  let V : Finset (Fin k → ℕ) :=
    (Fintype.piFinset S).filter (fun m =>
      x < (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ∧
        (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ≤ y)
  let g : (Fin k → ℕ) → ℂ := fun m =>
    if hm : m ∈ V then
      F (Classical.choose
        (factorExtractionDyadicTuple_exists k (Nat.floor y) S x y rfl
          hx hxy hSpos ⟨m, hm⟩))
    else 0
  have hboxTerms :
      (∑ m ∈ V.attach, F (Classical.choose
        (factorExtractionDyadicTuple_exists k (Nat.floor y) S x y rfl
          hx hxy hSpos ⟨m.1, m.2⟩))) =
        ∑ m ∈ V, ∏ i : Fin k,
          factorExtractionAllocatedFactor a d s w i (m i) := by
    calc
      (∑ m ∈ V.attach, F (Classical.choose
          (factorExtractionDyadicTuple_exists k (Nat.floor y) S x y rfl
            hx hxy hSpos ⟨m.1, m.2⟩))) =
          ∑ m ∈ V.attach, g m.1 := by
            apply Finset.sum_congr rfl
            intro m hm
            simp [g, m.2]
      _ = ∑ m ∈ V, g m := Finset.sum_attach V g
      _ = ∑ m ∈ V, ∏ i : Fin k,
          factorExtractionAllocatedFactor a d s w i (m i) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hcoords := Classical.choose_spec
              (factorExtractionDyadicTuple_exists k (Nat.floor y) S x y rfl
                hx hxy hSpos ⟨m, hm⟩)
            dsimp [g]
            rw [dif_pos hm]
            dsimp [F]
            apply Finset.prod_congr rfl
            intro i hi
            exact congrArg (factorExtractionAllocatedFactor a d s w i)
              (hcoords i)
  have hsum :
      (∑ b ∈ T, F b) =
        ∑ m ∈ V, ∏ i : Fin k,
          factorExtractionAllocatedFactor a d s w i (m i) := by
    calc
      _ = ∑ m : {m : Fin k → ℕ // m ∈ V}, F (Classical.choose
          (factorExtractionDyadicTuple_exists k (Nat.floor y) S x y rfl
            hx hxy hSpos m)) := by
                simpa only [T, V, S, U] using hbox
      _ = ∑ m ∈ V.attach, F (Classical.choose
          (factorExtractionDyadicTuple_exists k (Nat.floor y) S x y rfl
            hx hxy hSpos ⟨m.1, m.2⟩)) := by
              rw [← Finset.attach_eq_univ]
      _ = _ := hboxTerms
  rw [hsum]
  have hfixed := factorExtractionFixedAllocationEstimate i₀ N B d s a w
    hN hd hB hε hcoeff hw hshort hx hxy
  simpa [V, S, U] using hfixed

/-- Simplify the fixed-allocation mass using the exact product of the
allocated divisors. The factor `3` occurs once for each unselected label. -/
theorem factorExtractionAllocationConstant_simplify
    {k r : ℕ} (i₀ : Fin k) (N B : Fin k → ℝ) (d : Fin k → ℕ)
    (ε : ℝ) (hN : ∀ i, 0 < N i) (hd : ∀ i, 0 < d i)
    (hprod : (∏ i : Fin k, d i) = r) :
    ε * Real.sqrt (N i₀ / (d i₀ : ℝ)) *
      ∏ j ∈ Finset.univ.erase i₀,
        (3 * B j * Real.sqrt (N j / (d j : ℝ))) =
      (3 : ℝ) ^ (k - 1) * ε *
        Real.sqrt ((∏ i : Fin k, N i) / (r : ℝ)) *
          ∏ j ∈ Finset.univ.erase i₀, B j := by
  classical
  let U : Fin k → ℝ := fun i => N i / (d i : ℝ)
  let E : Finset (Fin k) := Finset.univ.erase i₀
  have hU_nonneg : ∀ i : Fin k, 0 ≤ U i := by
    intro i
    dsimp [U]
    exact div_nonneg (le_of_lt (hN i)) (by positivity)
  have hdenom : (∏ i : Fin k, (d i : ℝ)) = (r : ℝ) := by
    exact_mod_cast hprod
  have hUprod :
      (∏ i : Fin k, U i) = (∏ i : Fin k, N i) / (r : ℝ) := by
    calc
      (∏ i : Fin k, U i) =
          (∏ i : Fin k, N i) / ∏ i : Fin k, (d i : ℝ) := by
            dsimp [U]
            rw [Finset.prod_div_distrib]
      _ = (∏ i : Fin k, N i) / (r : ℝ) := by rw [hdenom]
  have hsqrt :
      Real.sqrt (U i₀) *
        ∏ j ∈ E, Real.sqrt (U j) =
      Real.sqrt ((∏ i : Fin k, N i) / (r : ℝ)) := by
    calc
      Real.sqrt (U i₀) * ∏ j ∈ E, Real.sqrt (U j) =
          (∏ j ∈ E, Real.sqrt (U j)) * Real.sqrt (U i₀) := by ring
      _ = ∏ i : Fin k, Real.sqrt (U i) := by
        exact Finset.prod_erase_mul (s := Finset.univ)
          (f := fun i : Fin k => Real.sqrt (U i)) (Finset.mem_univ i₀)
      _ = Real.sqrt (∏ i : Fin k, U i) := by
        symm
        exact Real.sqrt_prod Finset.univ (by
          intro i hi
          exact hU_nonneg i)
      _ = Real.sqrt ((∏ i : Fin k, N i) / (r : ℝ)) := by rw [hUprod]
  have hconst :
      (∏ j ∈ E, (3 * B j * Real.sqrt (U j))) =
        (3 : ℝ) ^ (k - 1) *
          (∏ j ∈ E, B j) * (∏ j ∈ E, Real.sqrt (U j)) := by
    calc
      (∏ j ∈ E, (3 * B j * Real.sqrt (U j))) =
          (∏ j ∈ E, (3 * B j)) * (∏ j ∈ E, Real.sqrt (U j)) := by
            rw [Finset.prod_mul_distrib]
      _ = ((∏ j ∈ E, (3 : ℝ)) * (∏ j ∈ E, B j)) *
            (∏ j ∈ E, Real.sqrt (U j)) := by
              rw [Finset.prod_mul_distrib]
      _ = (3 : ℝ) ^ (k - 1) *
            (∏ j ∈ E, B j) * (∏ j ∈ E, Real.sqrt (U j)) := by
              have hcard : E.card = k - 1 := by simp [E]
              simp [E, hcard, Finset.prod_const]
  calc
    ε * Real.sqrt (N i₀ / (d i₀ : ℝ)) *
        ∏ j ∈ Finset.univ.erase i₀,
          (3 * B j * Real.sqrt (N j / (d j : ℝ))) =
        ε * Real.sqrt (U i₀) *
          ((3 : ℝ) ^ (k - 1) * (∏ j ∈ E, B j) *
            (∏ j ∈ E, Real.sqrt (U j))) := by
              simp only [U, E]
              rw [hconst]
    _ = (3 : ℝ) ^ (k - 1) * ε *
          Real.sqrt ((∏ i : Fin k, N i) / (r : ℝ)) *
            ∏ j ∈ Finset.univ.erase i₀, B j := by
              rw [← hsqrt]
              ring

/-- Small-factor extraction for an arbitrary finite Dirichlet convolution.
This is blueprint item `ltw:factor-extraction`, with the local interval
estimate required for every exact labeled gcd allocation. -/
theorem shiftedConvolutionSmallFactor
    (fs : List (ArithmeticFunction ℂ)) {r : ℕ} (hr : 0 < r)
    (i₀ : Fin fs.length) (N B : Fin fs.length → ℝ)
    (χ : ℕ → ℂ) (t ε : ℝ) {x y : ℝ}
    (hN : ∀ i, 0 < N i) (hB : ∀ i, 0 ≤ B i) (hε : 0 ≤ ε)
    (hcoeff : ∀ i n, ‖fs.get i n‖ ≤ B i)
    (hsupport : ∀ i n, fs.get i n ≠ 0 →
      N i < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N i)
    (hχnorm : ∀ m, 0 < m → ‖χ m‖ ≤ 1)
    (hχone : χ 1 = 1)
    (hχmul : ∀ m n, χ (m * n) = χ m * χ n)
    (hshort : ∀ d : divisorFactorTuples fs.length r, ∀ u v : ℝ,
      0 ≤ u →
      Set.Ioc u v ⊆ Set.Ioc
        (N i₀ / ((d.1 i₀).1 : ℝ))
        (2 * (N i₀ / ((d.1 i₀).1 : ℝ))) →
      ‖∑ m ∈ factorExtractionRealInterval u v,
        factorExtractionAllocatedFactor
          (fun i n => fs.get i n)
          (fun i => (d.1 i).1)
          (fun i => factorExtractionAllocationResidual d i)
          (factorExtractionMellinWeight χ t) i₀ m‖ ≤
        ε * Real.sqrt (N i₀ / ((d.1 i₀).1 : ℝ)))
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖∑ n ∈ factorExtractionRealInterval x y,
      (fs.prod) (r * n) * factorExtractionMellinWeight χ t n‖ ≤
      (3 : ℝ) ^ (fs.length - 1) *
        (divisorFunction fs.length ⟨r, hr⟩ : ℝ) * ε *
          Real.sqrt ((∏ i : Fin fs.length, N i) / (r : ℝ)) *
            ∏ j ∈ Finset.univ.erase i₀, B j := by
  classical
  let a : Fin fs.length → ℕ → ℂ := fun i n => fs.get i n
  let w : ℕ → ℂ := factorExtractionMellinWeight χ t
  let F : divisorFactorTuples fs.length r → ℂ := fun d =>
    ∑ b : {b : factorExtractionBoundedPositiveTuple fs.length (Nat.floor y) //
        x < (factorExtractionTupleProduct b.1 : ℝ)},
      ∏ i : Fin fs.length,
        factorExtractionAllocatedFactor a
          (fun i => (d.1 i).1)
          (fun i => factorExtractionAllocationResidual d i)
          w i (b.1.1 i).1
  let C : ℝ :=
    (3 : ℝ) ^ (fs.length - 1) * ε *
      Real.sqrt ((∏ i : Fin fs.length, N i) / (r : ℝ)) *
        ∏ j ∈ Finset.univ.erase i₀, B j
  have hidentity :
      (∑ n ∈ factorExtractionRealInterval x y,
        (fs.prod) (r * n) * w n) =
      ∑ d : divisorFactorTuples fs.length r, F d := by
    calc
      (∑ n ∈ factorExtractionRealInterval x y,
          (fs.prod) (r * n) * w n) =
          ∑ d : divisorFactorTuples fs.length r,
            ∑ n ∈ factorExtractionRealInterval x y,
              ∑ m : divisorFactorTuples fs.length n,
                (if ∀ i : Fin fs.length,
                    Nat.Coprime (m.1 i).1
                      (factorExtractionAllocationResidual d i)
                  then ∏ i : Fin fs.length,
                    (fs.get i) ((d.1 i).1 * (m.1 i).1)
                  else 0) * w n := by
                    exact factorExtractionFlatConvolutionSum fs hr hx hxy w
      _ = ∑ d : divisorFactorTuples fs.length r, F d := by
            apply Finset.sum_congr rfl
            intro d hd
            simpa [F, a, w] using
              (factorExtractionAllocationTupleReindex fs d χ t hχone hχmul
                hx hxy)
  have hF : ∀ d : divisorFactorTuples fs.length r, ‖F d‖ ≤ C := by
    intro d
    let dNat : Fin fs.length → ℕ := fun i => (d.1 i).1
    let s : Fin fs.length → ℕ := fun i =>
      factorExtractionAllocationResidual d i
    have hdNat : ∀ i, 0 < dNat i := fun i => (d.1 i).2
    have hcoeff' : ∀ i m,
        m ∈ factorExtractionDyadicInterval (N i / (dNat i : ℝ)) →
        ‖a i (dNat i * m)‖ ≤ B i := by
      intro i m hm
      exact hcoeff i (dNat i * m)
    have hw : ∀ m, 0 < m → ‖w m‖ ≤ 1 / Real.sqrt (m : ℝ) := by
      intro m hm
      exact factorExtractionMellinWeight_norm_le χ t hχnorm m hm
    have hlocal := factorExtractionAllocationEstimate i₀ N B dNat s a w
      hN hdNat hB hε hcoeff' hsupport hw (hshort d) hx hxy
    have hsum : F d =
        ∑ b ∈ (Finset.univ : Finset
          (factorExtractionBoundedPositiveTuple fs.length (Nat.floor y))).filter
            (fun b => x < (factorExtractionTupleProduct b.1 : ℝ)),
          ∏ i : Fin fs.length,
            factorExtractionAllocatedFactor a dNat s w i (b.1 i).1 := by
      dsimp [F]
      simpa [a, w, dNat, s, Finset.sum_filter] using
        (Finset.sum_subtype_eq_sum_filter
          (s := Finset.univ)
          (p := fun b : factorExtractionBoundedPositiveTuple fs.length
              (Nat.floor y) =>
            x < (factorExtractionTupleProduct b.1 : ℝ))
          (fun b =>
            ∏ i : Fin fs.length,
              factorExtractionAllocatedFactor a dNat s w i (b.1 i).1))
    calc
      ‖F d‖ = ‖∑ b ∈ (Finset.univ : Finset
            (factorExtractionBoundedPositiveTuple fs.length (Nat.floor y))).filter
              (fun b => x < (factorExtractionTupleProduct b.1 : ℝ)),
            ∏ i : Fin fs.length,
              factorExtractionAllocatedFactor a dNat s w i (b.1 i).1‖ := by
                rw [hsum]
      _ ≤ ε * Real.sqrt (N i₀ / (dNat i₀ : ℝ)) *
            ∏ j ∈ Finset.univ.erase i₀,
              (3 * B j * Real.sqrt (N j / (dNat j : ℝ))) := hlocal
      _ = C := by
            simpa [C, dNat, s] using
              factorExtractionAllocationConstant_simplify
                i₀ N B dNat ε hN hdNat d.2
  rw [hidentity]
  have hsumBound := factorExtractionAllocationSum_norm_le hr F C hF
  calc
    ‖∑ d : divisorFactorTuples fs.length r, F d‖ ≤
        (divisorFunction fs.length ⟨r, hr⟩ : ℝ) * C := hsumBound
    _ = (3 : ℝ) ^ (fs.length - 1) *
          (divisorFunction fs.length ⟨r, hr⟩ : ℝ) * ε *
            Real.sqrt ((∏ i : Fin fs.length, N i) / (r : ℝ)) *
              ∏ j ∈ Finset.univ.erase i₀, B j := by
                dsimp [C]
                ring


end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.factorExtractionMellinWeight_norm_le
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionMellinWeight_mul
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionMellinWeight_prod
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionTupleIntervalReindex
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionTupleIntervalEquiv_symm_coordinate

#print axioms FractionalPrimes.Literature.Twisted.factorExtractionSupportedBoundedTupleSum
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionSupportedPositiveTuple_coordinate
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionSupportedPositiveTuple_product
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionDyadicTupleLift
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionDyadicTuple_exists
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionSupportedBoundedTupleSum_eq_dyadicBox
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionAllocationSum_norm_le
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionFlatTerm_mul_weight
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionFlatConvolutionSum
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionAllocationTupleReindex
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionAllocationEstimate
#print axioms FractionalPrimes.Literature.Twisted.factorExtractionAllocationConstant_simplify
#print axioms FractionalPrimes.Literature.Twisted.shiftedConvolutionSmallFactor
