module

public import FractionalPrimes.Literature.Twisted.NonunitTripleCharacterFactorization

/-!
# Finite Mellin identity for a nonunit residue

This module completes the finite truncation and labeled-index assembly for
the nonunit triple character factorization.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity

/-- Positive labeled triples with product at most `P`. -/
def boundedPositiveMellinTriple (P : ℕ) :=
  {m : Fin 3 → PositiveInteger // ∏ i : Fin 3, (m i).1 ≤ P}

theorem boundedPositiveMellinTriple_finite (P : ℕ) :
    Finite (boundedPositiveMellinTriple P) := by
  apply Finite.of_injective
    (fun m : boundedPositiveMellinTriple P => fun i : Fin 3 =>
      (⟨(m.1 i).1, by
        have hle : (m.1 i).1 ≤ ∏ j : Fin 3, (m.1 j).1 := by
          simpa using
            (Finset.single_le_prod (s := Finset.univ)
              (f := fun j : Fin 3 => (m.1 j).1)
              (fun j hj => Nat.one_le_iff_ne_zero.mpr
                (Nat.ne_of_gt (m.1 j).2)) (Finset.mem_univ i))
        exact Nat.lt_succ_of_le (le_trans hle m.2)⟩ : Fin (P + 1)))
  intro m n h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrArg Fin.val (congrFun h i)

noncomputable instance boundedPositiveMellinTriple_fintype (P : ℕ) :
    Fintype (boundedPositiveMellinTriple P) := by
  haveI : Finite (boundedPositiveMellinTriple P) :=
    boundedPositiveMellinTriple_finite P
  exact Fintype.ofFinite _

/-- The exact sigma-index conversion behind the finite Mellin assembly.
The product bound and the labeled factor tuple are equivalent to one positive
labeled triple whose product is bounded. -/
noncomputable def finiteMellinTripleIndexEquiv (P : ℕ) :
    (Σ t : {t : ℕ // t ∈ Finset.Icc 1 P}, divisorFactorTuples 3 t.1) ≃
      boundedPositiveMellinTriple P := by
  classical
  refine
    { toFun := fun x => ⟨x.2.1, ?_⟩
      invFun := fun m => ?_
      left_inv := ?_
      right_inv := ?_ }
  · calc
      ∏ i : Fin 3, (x.2.1 i).1 = x.1.1 := x.2.2
      _ ≤ P := (Finset.mem_Icc.mp x.1.2).2
  · let t : ℕ := ∏ i : Fin 3, (m.1 i).1
    have htpos : 0 < t := by
      dsimp [t]
      exact Finset.prod_pos fun i hi => (m.1 i).2
    refine ⟨⟨t, Finset.mem_Icc.mpr ⟨htpos, m.2⟩⟩,
      ⟨m.1, ?_⟩⟩
    rfl
  · rintro ⟨⟨t, ht⟩, m⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact m.2
    · rfl
  · intro m
    apply Subtype.ext
    rfl

theorem finiteMellinTripleIndexEquiv_symm_tuple (P : ℕ)
    (m : boundedPositiveMellinTriple P) :
    ((finiteMellinTripleIndexEquiv P).symm m).2.1 = m.1 := by
  have h := congrArg Subtype.val
    (Equiv.apply_symm_apply (finiteMellinTripleIndexEquiv P) m)
  change ((finiteMellinTripleIndexEquiv P).symm m).2.1 = m.1 at h
  exact h

theorem finiteMellinTripleIndexEquiv_symm_product (P : ℕ)
    (m : boundedPositiveMellinTriple P) :
    ((finiteMellinTripleIndexEquiv P).symm m).1.1 =
      ∏ i : Fin 3, (m.1 i).1 := by
  have htup := finiteMellinTripleIndexEquiv_symm_tuple P m
  have hp := ((finiteMellinTripleIndexEquiv P).symm m).2.2
  rw [htup] at hp
  exact hp.symm

/-- Reindex the product-bound factor-tuple sum as a sum over bounded positive
labeled triples. -/
theorem finiteMellinTripleSigmaReindex (P : ℕ)
    (F : ∀ t : ℕ, divisorFactorTuples 3 t → ℂ) :
    (∑ t ∈ Finset.Icc 1 P,
      ∑ m : divisorFactorTuples 3 t, F t m) =
      ∑ m : boundedPositiveMellinTriple P,
        F (((finiteMellinTripleIndexEquiv P).symm m).1.1)
          ((finiteMellinTripleIndexEquiv P).symm m).2 := by
  classical
  let T : Finset ℕ := Finset.Icc 1 P
  have hsubtype :
      (∑ t : {t : ℕ // t ∈ T},
        ∑ m : divisorFactorTuples 3 t.1, F t.1 m) =
      ∑ t ∈ T, ∑ m : divisorFactorTuples 3 t, F t m := by
    let f : ℕ → ℂ := fun t => ∑ m : divisorFactorTuples 3 t, F t m
    calc
      (∑ t : {t : ℕ // t ∈ T}, f t.1) =
          ∑ t ∈ T.attach, f t.1 := by
            have hset :
                (Finset.univ : Finset {t : ℕ // t ∈ T}) = T.attach := by
              ext t
              simp
            exact congrArg
              (fun s : Finset {t : ℕ // t ∈ T} => s.sum (fun t => f t.1)) hset
      _ = ∑ t ∈ T, f t := Finset.sum_attach T f
      _ = _ := rfl
  rw [← hsubtype]
  let G : (Σ t : {t : ℕ // t ∈ T}, divisorFactorTuples 3 t.1) → ℂ :=
    fun x => F x.1.1 x.2
  have hsigma :
      (∑ t : {t : ℕ // t ∈ T},
        ∑ m : divisorFactorTuples 3 t.1, F t.1 m) =
        ∑ x : Σ t : {t : ℕ // t ∈ T}, divisorFactorTuples 3 t.1, G x := by
    simpa [G] using (Fintype.sum_sigma G).symm
  rw [hsigma]
  exact Fintype.sum_equiv (finiteMellinTripleIndexEquiv P)
    G
    (fun m => F ((finiteMellinTripleIndexEquiv P).symm m).1.1
      ((finiteMellinTripleIndexEquiv P).symm m).2)
    (by
      intro x
      simpa [G] using
        (congrArg (fun y => F y.1.1 y.2)
          (Equiv.symm_apply_apply (finiteMellinTripleIndexEquiv P) x).symm))

abbrev positiveMellinIntervalIndex (P : ℕ) :=
  {m : ℕ // m ∈ Finset.Icc 1 P}

def positiveMellinIntervalToPositive (P : ℕ)
    (m : positiveMellinIntervalIndex P) : PositiveInteger :=
  ⟨m.1, by have hm := (Finset.mem_Icc.mp m.2).1; omega⟩

def positiveMellinIntervalBox (P : ℕ)
    (m : Fin 3 → positiveMellinIntervalIndex P) : Fin 3 → PositiveInteger :=
  fun i => positiveMellinIntervalToPositive P (m i)

private theorem positiveMellinIntervalIndex_sum_eq_Icc (P : ℕ)
    (f : positiveMellinIntervalIndex P → ℂ) :
    (∑ m : positiveMellinIntervalIndex P, f m) =
      ∑ m ∈ Finset.Icc 1 P,
        (if h : m ∈ Finset.Icc 1 P then f ⟨m, h⟩ else 0) := by
  classical
  let g : ℕ → ℂ := fun m =>
    if h : m ∈ Finset.Icc 1 P then f ⟨m, h⟩ else 0
  calc
    (∑ m : positiveMellinIntervalIndex P, f m) =
        ∑ m ∈ (Finset.Icc 1 P).attach, f m := by
          have hset :
              (Finset.univ : Finset (positiveMellinIntervalIndex P)) =
                (Finset.Icc 1 P).attach := by
            ext m
            simp
          exact congrArg (fun s : Finset (positiveMellinIntervalIndex P) => s.sum f) hset
    _ = ∑ m ∈ (Finset.Icc 1 P).attach, g m.1 := by
          apply Finset.sum_congr rfl
          intro m hm
          simp only [g, dif_pos m.2]
    _ = ∑ m ∈ Finset.Icc 1 P, g m := Finset.sum_attach _ _
    _ = _ := by rfl

private noncomputable def fin3MellinBoxEquiv (α : Type*) :
    (Fin 3 → α) ≃ α × α × α where
  toFun m := (m 0, m 1, m 2)
  invFun p := Fin.cons p.1 (Fin.cons p.2.1 (Fin.cons p.2.2 Fin.elim0))
  left_inv m := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    rfl

/-- Convert the subtype box sum to the three natural interval sums used by
the source finite Dirichlet polynomials. -/
theorem finiteMellinIntervalBox_sum_eq_nested (P : ℕ)
    (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ m : Fin 3 → positiveMellinIntervalIndex P,
      F (m 0).1 (m 1).1 (m 2).1) =
      ∑ m₁ ∈ Finset.Icc 1 P, ∑ m₂ ∈ Finset.Icc 1 P,
        ∑ m₃ ∈ Finset.Icc 1 P, F m₁ m₂ m₃ := by
  classical
  let I := positiveMellinIntervalIndex P
  calc
    (∑ m : Fin 3 → I, F (m 0).1 (m 1).1 (m 2).1) =
        ∑ p : I × I × I, F p.1.1 p.2.1.1 p.2.2.1 := by
          exact Fintype.sum_equiv (fin3MellinBoxEquiv I)
            (fun m => F (m 0).1 (m 1).1 (m 2).1)
            (fun p => F p.1.1 p.2.1.1 p.2.2.1)
            (by intro m; rfl)
    _ = ∑ m₁ : I, ∑ m₂ : I, ∑ m₃ : I,
          F m₁.1 m₂.1 m₃.1 := by
          calc
            (∑ p : I × I × I, F p.1.1 p.2.1.1 p.2.2.1) =
                ∑ m₁ : I, ∑ p : I × I,
                  F m₁.1 p.1.1 p.2.1 := by
                    rw [Fintype.sum_prod_type]
            _ = ∑ m₁ : I, ∑ m₂ : I, ∑ m₃ : I,
                  F m₁.1 m₂.1 m₃.1 := by
                    apply Fintype.sum_congr
                    intro m₁
                    rw [Fintype.sum_prod_type]
    _ = ∑ m₁ ∈ Finset.Icc 1 P, ∑ m₂ : I, ∑ m₃ : I,
          F m₁ m₂.1 m₃.1 := by
          rw [positiveMellinIntervalIndex_sum_eq_Icc]
          apply Finset.sum_congr rfl
          intro m₁ hm₁
          simp only [dif_pos hm₁]
    _ = ∑ m₁ ∈ Finset.Icc 1 P, ∑ m₂ ∈ Finset.Icc 1 P,
          ∑ m₃ : I, F m₁ m₂ m₃.1 := by
          apply Finset.sum_congr rfl
          intro m₁ hm₁
          rw [positiveMellinIntervalIndex_sum_eq_Icc]
          apply Finset.sum_congr rfl
          intro m₂ hm₂
          simp only [dif_pos hm₂]
    _ = ∑ m₁ ∈ Finset.Icc 1 P, ∑ m₂ ∈ Finset.Icc 1 P,
          ∑ m₃ ∈ Finset.Icc 1 P, F m₁ m₂ m₃ := by
          apply Finset.sum_congr rfl
          intro m₁ hm₁
          apply Finset.sum_congr rfl
          intro m₂ hm₂
          rw [positiveMellinIntervalIndex_sum_eq_Icc]
          apply Finset.sum_congr rfl
          intro m₃ hm₃
          simp only [dif_pos hm₃]

/-- Extend a sum over triples with product at most `P` to the full interval
box when the summand vanishes outside the product cutoff. -/
theorem boundedPositiveMellinTriple_sum_eq_intervalBox
    (P : ℕ) (G : (Fin 3 → PositiveInteger) → ℂ)
    (hzero : ∀ m, P < ∏ i : Fin 3, (m i).1 → G m = 0) :
    (∑ m : boundedPositiveMellinTriple P, G m.1) =
      ∑ m : Fin 3 → positiveMellinIntervalIndex P,
        G (positiveMellinIntervalBox P m) := by
  classical
  let boundedIntervalTriple :=
    {m : Fin 3 → positiveMellinIntervalIndex P //
      ∏ i : Fin 3, (m i).1 ≤ P}
  let e : boundedPositiveMellinTriple P ≃ boundedIntervalTriple :=
    { toFun := fun m => by
        refine ⟨fun i => ⟨(m.1 i).1, Finset.mem_Icc.mpr ?_⟩, ?_⟩
        · have hcoord : (m.1 i).1 ≤ ∏ j : Fin 3, (m.1 j).1 :=
            Finset.single_le_prod (s := Finset.univ)
              (f := fun j : Fin 3 => (m.1 j).1)
              (fun j hj => Nat.one_le_iff_ne_zero.mpr
                (Nat.ne_of_gt (m.1 j).2)) (Finset.mem_univ i)
          exact ⟨(m.1 i).2, hcoord.trans m.2⟩
        · simpa using m.2
      invFun := fun m => by
        refine ⟨fun i => ⟨(m.1 i).1, ?_⟩, m.2⟩
        have hlow := (Finset.mem_Icc.mp (m.1 i).2).1
        omega
      left_inv := by
        intro m
        apply Subtype.ext
        funext i
        apply Subtype.ext
        rfl
      right_inv := by
        intro m
        apply Subtype.ext
        funext i
        apply Subtype.ext
        rfl }
  have hreindex :
      (∑ m : boundedPositiveMellinTriple P, G m.1) =
        ∑ m : boundedIntervalTriple, G (positiveMellinIntervalBox P m.1) := by
    exact Fintype.sum_equiv e
      (fun m => G m.1)
      (fun m => G (positiveMellinIntervalBox P m.1))
      (by
        intro m
        apply congrArg G
        funext i
        apply Subtype.ext
        rfl)
  have hfiltered :
      (∑ m : boundedIntervalTriple,
        G (positiveMellinIntervalBox P m.1)) =
      ∑ m : Fin 3 → positiveMellinIntervalIndex P,
        if ∏ i : Fin 3, (m i).1 ≤ P then
          G (positiveMellinIntervalBox P m) else 0 := by
    simpa [boundedIntervalTriple, Finset.sum_filter] using
      (Finset.sum_subtype_eq_sum_filter
        (s := Finset.univ)
        (p := fun m : Fin 3 → positiveMellinIntervalIndex P =>
          ∏ i : Fin 3, (m i).1 ≤ P)
        (fun m => G (positiveMellinIntervalBox P m)))
  calc
    (∑ m : boundedPositiveMellinTriple P, G m.1) =
        ∑ m : boundedIntervalTriple,
          G (positiveMellinIntervalBox P m.1) := hreindex
    _ = ∑ m : Fin 3 → positiveMellinIntervalIndex P,
          if ∏ i : Fin 3, (m i).1 ≤ P then
            G (positiveMellinIntervalBox P m) else 0 := hfiltered
    _ = ∑ m : Fin 3 → positiveMellinIntervalIndex P,
          G (positiveMellinIntervalBox P m) := by
            apply Fintype.sum_congr
            intro m
            by_cases hm : ∏ i : Fin 3, (m i).1 ≤ P
            · simp [hm]
            · have hlt : P < ∏ i : Fin 3, (m i).1 := Nat.lt_of_not_ge hm
              simp [hm, hzero (positiveMellinIntervalBox P m) hlt]

private theorem allocatedCoeffProduct_bound
    (a₁ a₂ a₃ : ArithmeticFunction ℂ) {N₁ N₂ N₃ : ℕ}
    (h₁ : ∀ n, a₁ n ≠ 0 → n ≤ N₁)
    (h₂ : ∀ n, a₂ n ≠ 0 → n ≤ N₂)
    (h₃ : ∀ n, a₃ n ≠ 0 → n ≤ N₃)
    (r m : Fin 3 → PositiveInteger)
    (hcoeff : ∏ i : Fin 3,
      (threeArithmeticFactors a₁ a₂ a₃ i) ((r i).1 * (m i).1) ≠ 0) :
    ∏ i : Fin 3, (m i).1 ≤ N₁ * N₂ * N₃ := by
  have h₁' : a₁ ((r 0).1 * (m 0).1) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hcoeff) 0 (Finset.mem_univ 0)
  have h₂' : a₂ ((r 1).1 * (m 1).1) ≠ 0 := by
    simpa using (Finset.prod_ne_zero_iff.mp hcoeff) 1 (Finset.mem_univ 1)
  have h₃' : a₃ ((r 2).1 * (m 2).1) ≠ 0 := by
    simpa using (Finset.prod_ne_zero_iff.mp hcoeff) 2 (Finset.mem_univ 2)
  have hm₁ : (m 0).1 ≤ N₁ := by
    calc
      (m 0).1 ≤ (r 0).1 * (m 0).1 := by
        simpa using Nat.mul_le_mul_right (m 0).1
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (r 0).2))
      _ ≤ N₁ := h₁ _ h₁'
  have hm₂ : (m 1).1 ≤ N₂ := by
    calc
      (m 1).1 ≤ (r 1).1 * (m 1).1 := by
        simpa using Nat.mul_le_mul_right (m 1).1
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (r 1).2))
      _ ≤ N₂ := h₂ _ h₂'
  have hm₃ : (m 2).1 ≤ N₃ := by
    calc
      (m 2).1 ≤ (r 2).1 * (m 2).1 := by
        simpa using Nat.mul_le_mul_right (m 2).1
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (r 2).2))
      _ ≤ N₃ := h₃ _ h₃'
  calc
    ∏ i : Fin 3, (m i).1 = (m 0).1 * ((m 1).1 * (m 2).1) := by
      rw [Fin.prod_univ_three]
      ring
    _ ≤ N₁ * (N₂ * N₃) := Nat.mul_le_mul hm₁ (Nat.mul_le_mul hm₂ hm₃)
    _ = N₁ * N₂ * N₃ := by ring

private theorem positiveNatCpow_product_four
    {d m₁ m₂ m₃ : ℕ} (hd : 0 < d) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (s : ℂ) :
    ((d * (m₁ * (m₂ * m₃)) : ℕ) : ℂ) ^ (-s) =
      (d : ℂ) ^ (-s) * (m₁ : ℂ) ^ (-s) *
        (m₂ : ℂ) ^ (-s) * (m₃ : ℂ) ^ (-s) := by
  calc
    ((d * (m₁ * (m₂ * m₃)) : ℕ) : ℂ) ^ (-s) =
        (d : ℂ) ^ (-s) * ((m₁ * (m₂ * m₃) : ℕ) : ℂ) ^ (-s) :=
          positiveNatCpow_mul hd (Nat.mul_pos hm₁ (Nat.mul_pos hm₂ hm₃)) (-s)
    _ = (d : ℂ) ^ (-s) *
        ((m₁ : ℂ) ^ (-s) * ((m₂ * m₃ : ℕ) : ℂ) ^ (-s)) := by
          rw [positiveNatCpow_mul hm₁ (Nat.mul_pos hm₂ hm₃) (-s)]
    _ = (d : ℂ) ^ (-s) *
        ((m₁ : ℂ) ^ (-s) *
          ((m₂ : ℂ) ^ (-s) * (m₃ : ℂ) ^ (-s)) ) := by
          rw [positiveNatCpow_mul hm₂ hm₃ (-s)]
    _ = _ := by ring

private def allocatedMellinCoefficientProduct
    (a₁ a₂ a₃ : ArithmeticFunction ℂ)
    (r : Fin 3 → PositiveInteger) (m : Fin 3 → ℕ) : ℂ :=
  ∏ i : Fin 3,
    (threeArithmeticFactors a₁ a₂ a₃ i) ((r i).1 * m i)

private def allocatedMellinCutoff
    (q : ℕ) (r : Fin 3 → PositiveInteger) (m : Fin 3 → ℕ) : Prop :=
  ∀ i : Fin 3, Nat.Coprime (m i) (q / orderedAllocationPrefix r i)

private noncomputable instance allocatedMellinCutoff_decidable
    (q : ℕ) (r : Fin 3 → PositiveInteger) (m : Fin 3 → ℕ) :
    Decidable (allocatedMellinCutoff q r m) := Classical.propDecidable _

private def natMellinTriple (m₁ m₂ m₃ : ℕ) : Fin 3 → ℕ :=
  Fin.cases m₁ (Fin.cases m₂ (Fin.cases m₃ Fin.elim0))

@[simp] private theorem natMellinTriple_zero (m₁ m₂ m₃ : ℕ) :
    natMellinTriple m₁ m₂ m₃ 0 = m₁ := rfl

@[simp] private theorem natMellinTriple_one (m₁ m₂ m₃ : ℕ) :
    natMellinTriple m₁ m₂ m₃ 1 = m₂ := rfl

@[simp] private theorem natMellinTriple_two (m₁ m₂ m₃ : ℕ) :
    natMellinTriple m₁ m₂ m₃ 2 = m₃ := rfl

private theorem allocatedMellinCutoff_components
    (q : ℕ) (r : Fin 3 → PositiveInteger) (m₁ m₂ m₃ : ℕ) :
    allocatedMellinCutoff q r (natMellinTriple m₁ m₂ m₃) ↔
      Nat.Coprime m₁ (q / orderedAllocationPrefix r 0) ∧
      Nat.Coprime m₂ (q / orderedAllocationPrefix r 1) ∧
      Nat.Coprime m₃ (q / orderedAllocationPrefix r 2) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [allocatedMellinCutoff] using h 0
    · simpa [allocatedMellinCutoff] using h 1
    · simpa [allocatedMellinCutoff] using h 2
  · rintro ⟨h₁, h₂, h₃⟩ i
    fin_cases i
    · simpa [allocatedMellinCutoff] using h₁
    · simpa [allocatedMellinCutoff] using h₂
    · simpa [allocatedMellinCutoff] using h₃

private theorem allocatedMellinCoefficientProduct_eq
    (a₁ a₂ a₃ : ArithmeticFunction ℂ)
    (r : Fin 3 → PositiveInteger) (m₁ m₂ m₃ : ℕ) :
    allocatedMellinCoefficientProduct a₁ a₂ a₃ r
      (natMellinTriple m₁ m₂ m₃) =
      a₁ ((r 0).1 * m₁) * a₂ ((r 1).1 * m₂) * a₃ ((r 2).1 * m₃) := by
  simp [allocatedMellinCoefficientProduct, Fin.prod_univ_three,
    Nat.mul_assoc]

private def allocatedMellinTripleTerm
    (a₁ a₂ a₃ : ArithmeticFunction ℂ) (a' : ℤ)
    (Q q d : ℕ) (r : divisorFactorTuples 3 d) (s : ℂ)
    (m : Fin 3 → ℕ) : ℂ := by
  classical
  exact
    (if (a' : ZMod Q) = ((∏ i : Fin 3, m i) : ZMod Q) then 1 else 0) *
      (if allocatedMellinCutoff q r.1 m then
        allocatedMellinCoefficientProduct a₁ a₂ a₃ r.1 m else 0) *
      (((d * (∏ i : Fin 3, m i)) : ℕ) : ℂ) ^ (-s)

private theorem tripleCoprimeCoefficientIdentity
    (c₁ c₂ c₃ : Prop) [Decidable c₁] [Decidable c₂] [Decidable c₃]
    (a₁ a₂ a₃ : ℂ) :
    (if c₁ ∧ c₂ ∧ c₃ then a₁ * a₂ * a₃ else 0) =
      (a₁ * (if c₁ then 1 else 0)) *
        (a₂ * (if c₂ then 1 else 0)) *
        (a₃ * (if c₃ then 1 else 0)) := by
  classical
  by_cases hc₁ : c₁ <;> by_cases hc₂ : c₂ <;> by_cases hc₃ : c₃
  <;> simp [hc₁, hc₂, hc₃] <;> ring

private theorem fixedAllocatedMellinFactorization
    {q Q d N₁ N₂ N₃ : ℕ} (hQ : 0 < Q) (hd : 0 < d)
    (a' : ℤ) (ha' : IsCoprime a' (Q : ℤ))
    (r : divisorFactorTuples 3 d)
    (a₁ a₂ a₃ : ArithmeticFunction ℂ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN₃ : 0 < N₃)
    (hsupp₁ : ∀ n, a₁ n ≠ 0 → n ≤ N₁)
    (hsupp₂ : ∀ n, a₂ n ≠ 0 → n ≤ N₂)
    (hsupp₃ : ∀ n, a₃ n ≠ 0 → n ≤ N₃)
    (s : ℂ) :
    (∑ t ∈ Finset.Icc 1 (N₁ * N₂ * N₃),
      ∑ m : divisorFactorTuples 3 t,
        if (a' : ZMod Q) = (t : ZMod Q) then
          (if allocatedMellinCutoff q r.1 (fun i => (m.1 i).1) then
            allocatedMellinCoefficientProduct a₁ a₂ a₃ r.1
              (fun i => (m.1 i).1) else 0) *
            ((d * t : ℕ) : ℂ) ^ (-s)
        else 0) =
    ((d : ℂ) ^ (-s) / (Q.totient : ℂ)) *
      ∑ χ : BlueprintCharacter Q,
        star (evalInt χ a') *
          finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
            (q / orderedAllocationPrefix r.1 0)
            (Finset.Icc 1 (N₁ * N₂ * N₃)) χ s *
          finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
            (q / orderedAllocationPrefix r.1 1)
            (Finset.Icc 1 (N₁ * N₂ * N₃)) χ s *
          finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
            (q / orderedAllocationPrefix r.1 2)
            (Finset.Icc 1 (N₁ * N₂ * N₃)) χ s := by
  classical
  let P := N₁ * N₂ * N₃
  let S := Finset.Icc 1 P
  let F : ∀ t : ℕ, divisorFactorTuples 3 t → ℂ := fun t m =>
    if (a' : ZMod Q) = (t : ZMod Q) then
      (if allocatedMellinCutoff q r.1 (fun i => (m.1 i).1) then
        allocatedMellinCoefficientProduct a₁ a₂ a₃ r.1
          (fun i => (m.1 i).1) else 0) *
        ((d * t : ℕ) : ℂ) ^ (-s)
    else 0
  let G : (Fin 3 → PositiveInteger) → ℂ := fun m =>
    allocatedMellinTripleTerm a₁ a₂ a₃ a' Q q d r s
      (fun i => (m i).1)
  have hindex :
      (∑ t ∈ S, ∑ m : divisorFactorTuples 3 t, F t m) =
        ∑ m : boundedPositiveMellinTriple P, G m.1 := by
    rw [finiteMellinTripleSigmaReindex P F]
    apply Fintype.sum_congr
    intro m
    have ht := finiteMellinTripleIndexEquiv_symm_product P m
    have hm := finiteMellinTripleIndexEquiv_symm_tuple P m
    simp only [F, G, allocatedMellinTripleTerm, allocatedMellinCutoff,
      allocatedMellinCoefficientProduct, ht, hm]
    have hcastprod :
        ((∏ i : Fin 3, (m.1 i).1 : ℕ) : ZMod Q) =
          ∏ i : Fin 3, ((m.1 i).1 : ZMod Q) := by
      norm_cast
    by_cases hres : (a' : ZMod Q) =
        ((∏ i : Fin 3, (m.1 i).1 : ℕ) : ZMod Q)
    · have hres' : (a' : ZMod Q) =
          ∏ i : Fin 3, ((m.1 i).1 : ZMod Q) := by
        rw [← hcastprod]
        exact hres
      by_cases hcut : allocatedMellinCutoff q r.1
          (fun i => (m.1 i).1)
      · simp [hres, hres', hcut]
      · simp [hres, hres', hcut]
    · have hres' : (a' : ZMod Q) ≠
          ∏ i : Fin 3, ((m.1 i).1 : ZMod Q) := by
        intro h
        apply hres
        rw [hcastprod]
        exact h
      by_cases hcut : allocatedMellinCutoff q r.1
          (fun i => (m.1 i).1)
      · simp [hres, hres', hcut]
      · simp [hres, hres', hcut]
  have hzero : ∀ m : Fin 3 → PositiveInteger,
      P < ∏ i : Fin 3, (m i).1 → G m = 0 := by
    intro m hgt
    have hcastprod :
        ((∏ i : Fin 3, (m i).1 : ℕ) : ZMod Q) =
          ∏ i : Fin 3, ((m i).1 : ZMod Q) := by
      norm_cast
    by_cases hres : (a' : ZMod Q) =
        ((∏ i : Fin 3, (m i).1 : ℕ) : ZMod Q)
    · have hres' : (a' : ZMod Q) =
          ∏ i : Fin 3, ((m i).1 : ZMod Q) := by
        rw [← hcastprod]
        exact hres
      by_cases hcut : allocatedMellinCutoff q r.1 (fun i => (m i).1)
      · have hcoeff : allocatedMellinCoefficientProduct a₁ a₂ a₃ r.1
            (fun i => (m i).1) = 0 := by
          by_contra hne
          have hcoef' : ∏ i : Fin 3,
              (threeArithmeticFactors a₁ a₂ a₃ i)
                ((r.1 i).1 * (m i).1) ≠ 0 := by
            simpa [allocatedMellinCoefficientProduct] using hne
          have hbound := allocatedCoeffProduct_bound a₁ a₂ a₃
            hsupp₁ hsupp₂ hsupp₃ r.1 m hcoef'
          exact (Nat.not_lt_of_ge (by simpa [P] using hbound)) hgt
        change allocatedMellinTripleTerm a₁ a₂ a₃ a' Q q d r s
          (fun i => (m i).1) = 0
        simp [allocatedMellinTripleTerm, hres, hres', hcut, hcoeff]
      · change allocatedMellinTripleTerm a₁ a₂ a₃ a' Q q d r s
          (fun i => (m i).1) = 0
        simp [allocatedMellinTripleTerm, hres, hres', hcut]
    · change allocatedMellinTripleTerm a₁ a₂ a₃ a' Q q d r s
        (fun i => (m i).1) = 0
      have hres' : (a' : ZMod Q) ≠
          ∏ i : Fin 3, ((m i).1 : ZMod Q) := by
        intro h
        apply hres
        rw [hcastprod]
        exact h
      simp [allocatedMellinTripleTerm, hres, hres']
  have hbox := boundedPositiveMellinTriple_sum_eq_intervalBox P G hzero
  let H : ℕ → ℕ → ℕ → ℂ := fun m₁ m₂ m₃ =>
    allocatedMellinTripleTerm a₁ a₂ a₃ a' Q q d r s
      (natMellinTriple m₁ m₂ m₃)
  have hboxNat :
      (∑ m : Fin 3 → positiveMellinIntervalIndex P,
        G (positiveMellinIntervalBox P m)) =
      ∑ m : Fin 3 → positiveMellinIntervalIndex P,
        H (m 0).1 (m 1).1 (m 2).1 := by
    apply Fintype.sum_congr
    intro m
    have hcoords :
        (fun i => (positiveMellinIntervalBox P m i).1) =
          natMellinTriple (m 0).1 (m 1).1 (m 2).1 := by
      funext i
      fin_cases i
      · simp [positiveMellinIntervalBox, positiveMellinIntervalToPositive]
      · simp [positiveMellinIntervalBox, positiveMellinIntervalToPositive]
      · simp [positiveMellinIntervalBox, positiveMellinIntervalToPositive]
    change allocatedMellinTripleTerm a₁ a₂ a₃ a' Q q d r s
      (fun i => (positiveMellinIntervalBox P m i).1) = _
    rw [hcoords]
  have hboxNested := finiteMellinIntervalBox_sum_eq_nested P H
  have hchar := finiteAllocatedTripleCharacterFactorization hQ a' ha'
    S S S a₁ a₂ a₃
    (r.1 0).1 (q / orderedAllocationPrefix r.1 0)
    (r.1 1).1 (q / orderedAllocationPrefix r.1 1)
    (r.1 2).1 (q / orderedAllocationPrefix r.1 2) d s
  have hterm (m₁ m₂ m₃ : ℕ)
      (hm₁ : m₁ ∈ S) (hm₂ : m₂ ∈ S) (hm₃ : m₃ ∈ S) :
      H m₁ m₂ m₃ =
        (if (a' : ZMod Q) = ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
          then 1 else 0) *
        ((d : ℂ) ^ (-s) *
          (a₁ ((r.1 0).1 * m₁) *
            (if Nat.Coprime m₁ (q / orderedAllocationPrefix r.1 0)
              then 1 else 0) * (m₁ : ℂ) ^ (-s)) *
          (a₂ ((r.1 1).1 * m₂) *
            (if Nat.Coprime m₂ (q / orderedAllocationPrefix r.1 1)
              then 1 else 0) * (m₂ : ℂ) ^ (-s)) *
          (a₃ ((r.1 2).1 * m₃) *
            (if Nat.Coprime m₃ (q / orderedAllocationPrefix r.1 2)
              then 1 else 0) * (m₃ : ℂ) ^ (-s))) := by
    have hm₁pos : 0 < m₁ := (Finset.mem_Icc.mp hm₁).1
    have hm₂pos : 0 < m₂ := (Finset.mem_Icc.mp hm₂).1
    have hm₃pos : 0 < m₃ := (Finset.mem_Icc.mp hm₃).1
    have hcut := allocatedMellinCutoff_components q r.1 m₁ m₂ m₃
    have hcoeff := allocatedMellinCoefficientProduct_eq a₁ a₂ a₃ r.1
      m₁ m₂ m₃
    have hpow :
        ((d * (m₁ * (m₂ * m₃)) : ℕ) : ℂ) ^ (-s) =
          (d : ℂ) ^ (-s) * (m₁ : ℂ) ^ (-s) *
            (m₂ : ℂ) ^ (-s) * (m₃ : ℂ) ^ (-s) := by
      exact positiveNatCpow_product_four hd hm₁pos hm₂pos hm₃pos s
    simp only [H, allocatedMellinTripleTerm, natMellinTriple_zero,
      natMellinTriple_one, natMellinTriple_two]
    simp only [Fin.prod_univ_three, natMellinTriple_zero,
      natMellinTriple_one, natMellinTriple_two]
    have hresCast :
        ((m₁ * m₂ * m₃ : ℕ) : ZMod Q) =
          (m₁ : ZMod Q) * (m₂ : ZMod Q) * (m₃ : ZMod Q) := by
      norm_cast
    rw [if_congr hcut rfl rfl]
    rw [hcoeff]
    have hpow' :
        ((d * ((m₁ * m₂) * m₃) : ℕ) : ℂ) ^ (-s) =
          (d : ℂ) ^ (-s) * (m₁ : ℂ) ^ (-s) *
            (m₂ : ℂ) ^ (-s) * (m₃ : ℂ) ^ (-s) := by
      simpa [Nat.mul_assoc] using hpow
    rw [hpow']
    rw [tripleCoprimeCoefficientIdentity]
    rw [← hresCast]
    ring
  let K : ℕ → ℕ → ℕ → ℂ := fun m₁ m₂ m₃ =>
    (if (a' : ZMod Q) = ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
      then 1 else 0) *
    ((d : ℂ) ^ (-s) *
      (a₁ ((r.1 0).1 * m₁) *
        (if Nat.Coprime m₁ (q / orderedAllocationPrefix r.1 0)
          then 1 else 0) * (m₁ : ℂ) ^ (-s)) *
      (a₂ ((r.1 1).1 * m₂) *
        (if Nat.Coprime m₂ (q / orderedAllocationPrefix r.1 1)
          then 1 else 0) * (m₂ : ℂ) ^ (-s)) *
      (a₃ ((r.1 2).1 * m₃) *
        (if Nat.Coprime m₃ (q / orderedAllocationPrefix r.1 2)
          then 1 else 0) * (m₃ : ℂ) ^ (-s)))
  calc
    _ = ∑ m : boundedPositiveMellinTriple P, G m.1 := by
      simpa [P, S, F] using hindex
    _ = ∑ m : Fin 3 → positiveMellinIntervalIndex P,
          G (positiveMellinIntervalBox P m) := hbox
    _ = ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S, H m₁ m₂ m₃ := by
      rw [hboxNat, hboxNested]
    _ = ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S, K m₁ m₂ m₃ := by
      apply Finset.sum_congr rfl
      intro m₁ hm₁
      apply Finset.sum_congr rfl
      intro m₂ hm₂
      apply Finset.sum_congr rfl
      intro m₃ hm₃
      exact hterm m₁ m₂ m₃ hm₁ hm₂ hm₃
    _ = _ := by simpa [K] using hchar

/-- The finite source identity for three coefficient factors on a nonunit
residue class. The left cutoff contains the full support of the convolution;
the character polynomials use the exact factor range `1 ≤ m ≤ N₁N₂N₃`. -/
theorem nonunitTripleCharacterFactorizationFinite
    (a₁ a₂ a₃ : ArithmeticFunction ℂ)
    {N₁ N₂ N₃ q : ℕ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN₃ : 0 < N₃)
    (hsupp₁ : ∀ n, a₁ n ≠ 0 → n ≤ N₁)
    (hsupp₂ : ∀ n, a₂ n ≠ 0 → n ≤ N₂)
    (hsupp₃ : ∀ n, a₃ n ≠ 0 → n ≤ N₃)
    (hq : 0 < q) (a : ℤ) (s : ℂ) :
    (∑ n ∈ Finset.Icc 1 (N₁ * N₂ * N₃),
      if (n : ZMod q) = (a : ZMod q) then
        (a₁ * a₂ * a₃) n * (n : ℂ) ^ (-s) else 0) =
      ((Nat.gcd a.natAbs q : ℂ) ^ (-s) /
        ((q / Nat.gcd a.natAbs q).totient : ℂ)) *
      ∑ r : divisorFactorTuples 3 (Nat.gcd a.natAbs q),
        ∑ χ : BlueprintCharacter (q / Nat.gcd a.natAbs q),
          star (evalInt χ (a / (Nat.gcd a.natAbs q : ℤ))) *
            finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
              (q / orderedAllocationPrefix r.1 0)
              (Finset.Icc 1 (N₁ * N₂ * N₃)) χ s *
            finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
              (q / orderedAllocationPrefix r.1 1)
              (Finset.Icc 1 (N₁ * N₂ * N₃)) χ s *
            finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
              (q / orderedAllocationPrefix r.1 2)
              (Finset.Icc 1 (N₁ * N₂ * N₃)) χ s := by
  classical
  let d : ℕ := Nat.gcd a.natAbs q
  let Q : ℕ := q / d
  let a' : ℤ := a / (d : ℤ)
  let P : ℕ := N₁ * N₂ * N₃
  let S : Finset ℕ := Finset.Icc 1 P
  let f : ArithmeticFunction ℂ := a₁ * a₂ * a₃
  let fs : List (ArithmeticFunction ℂ) := [a₁, a₂, a₃]
  let c : ℂ := (d : ℂ) ^ (-s) / (Q.totient : ℂ)
  let A : divisorFactorTuples 3 d → ℂ := fun r =>
    ∑ χ : BlueprintCharacter Q,
      star (evalInt χ a') *
        finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
          (q / orderedAllocationPrefix r.1 0) S χ s *
        finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
          (q / orderedAllocationPrefix r.1 1) S χ s *
        finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
          (q / orderedAllocationPrefix r.1 2) S χ s
  let C : ∀ t : ℕ, divisorFactorTuples 3 d →
      divisorFactorTuples 3 t → ℂ := fun t r m =>
    if allocatedMellinCutoff q r.1 (fun i => (m.1 i).1) then
      allocatedMellinCoefficientProduct a₁ a₂ a₃ r.1
        (fun i => (m.1 i).1) else 0
  let g : ℕ → ℂ := fun n =>
    if (n : ZMod q) = (a : ZMod q) then
      f n * (n : ℂ) ^ (-s) else 0
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_right _ hq
  have hQpos : 0 < Q := by
    dsimp [Q, d]
    exact Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right _ _)) hdpos
  have ha' : IsCoprime a' (Q : ℤ) := by
    simpa [a', Q, d] using
      (residueGcdQuotientsCoprime (a := a) (q := q) hq)
  have hfsprod : fs.prod = a₁ * a₂ * a₃ := by
    simp [fs]
    exact (mul_assoc a₁ a₂ a₃).symm
  have hsupport (n : ℕ) (hn : 0 < n) (hfn : f n ≠ 0) : n ≤ P := by
    exact tripleConvolution_support_bound a₁ a₂ a₃
      hsupp₁ hsupp₂ hsupp₃ hn (by simpa [f] using hfn)
  have hsmallSubset : Finset.Icc 1 P ⊆ Finset.Icc 1 (d * P) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
    apply Finset.mem_Icc.mpr
    refine ⟨hnlo, ?_⟩
    exact hnhi.trans (Nat.le_mul_of_pos_left P hdpos)
  have hsmallEqLarge :
      (∑ n ∈ Finset.Icc 1 P, g n) =
        ∑ n ∈ Finset.Icc 1 (d * P), g n := by
    apply Finset.sum_subset hsmallSubset
    intro n hn hnnot
    have hnlo := (Finset.mem_Icc.mp hn).1
    have hnP : P < n := by
      have hnnot' : ¬(1 ≤ n ∧ n ≤ P) := by
        simpa [Finset.mem_Icc] using hnnot
      omega
    by_cases hcongr : (n : ZMod q) = (a : ZMod q)
    · have hfn : f n = 0 := by
        by_contra hne
        have hbound := hsupport n (by omega) hne
        omega
      simp [g, hcongr, hfn]
    · simp [g, hcongr]
  have hReindex :
      (∑ n ∈ Finset.Icc 1 (d * P), g n) =
        ∑ t ∈ S,
          if (a' : ZMod Q) = (t : ZMod Q) then
            f (d * t) * ((d * t : ℕ) : ℂ) ^ (-s) else 0 := by
    simpa [g, d, Q, a', P, S, eq_comm] using
      (finiteResidueMellin_gcd_reindex (fun n => f n)
        (a := a) (q := q) (P := P) hq s)
  have hpoint (t : ℕ) (ht : t ∈ S) :
      (if (a' : ZMod Q) = (t : ZMod Q) then
        f (d * t) * ((d * t : ℕ) : ℂ) ^ (-s) else 0) =
      ∑ r : divisorFactorTuples 3 d,
        ∑ m : divisorFactorTuples 3 t,
          if (a' : ZMod Q) = (t : ZMod Q) then
            C t r m * ((d * t : ℕ) : ℂ) ^ (-s) else 0 := by
    by_cases hres : (a' : ZMod Q) = (t : ZMod Q)
    · have hndvd : Nat.gcd a.natAbs q ∣ d * t := by
        refine ⟨t, ?_⟩
        simp [d]
      have hquot : (d * t) / Nat.gcd a.natAbs q = t := by
        dsimp [d]
        exact Nat.mul_div_right t hdpos
      have hquotres :
          (((d * t / Nat.gcd a.natAbs q : ℕ) : ℤ) : ZMod Q) =
            (a' : ZMod Q) := by
        simpa [Q, a', d, hquot, Int.cast_natCast] using hres.symm
      have hcongr₀ : ((d * t : ℕ) : ZMod q) = (a : ZMod q) :=
        (residueGcd_congruence_quotient_iff hq hndvd).2 hquotres
      have hcongr : ((d * t : ℕ) : ZMod q) = (a : ZMod q) := hcongr₀
      have hntpos : 0 < d * t :=
        Nat.mul_pos hdpos ((Finset.mem_Icc.mp ht).1)
      have halloc := residueClassFlatGcdAllocation fs
        (a := a) (q := q) (n := d * t) hq hntpos hcongr
      rw [hfsprod] at halloc
      rw [hquot] at halloc
      have halloc' : f (d * t) =
          ∑ r : divisorFactorTuples 3 d,
            ∑ m : divisorFactorTuples 3 t, C t r m := by
        simpa [f, C, d, fs, residueClassGcdAllocatedConvolution,
          allocatedMellinCutoff, allocatedMellinCoefficientProduct,
          threeArithmeticFactors_zero, threeArithmeticFactors_one,
          threeArithmeticFactors_two,
          Fin.prod_univ_three] using halloc
      simp only [if_pos hres]
      rw [halloc']
      calc
        (∑ r : divisorFactorTuples 3 d,
          ∑ m : divisorFactorTuples 3 t, C t r m) *
            ((d * t : ℕ) : ℂ) ^ (-s) =
          ∑ r : divisorFactorTuples 3 d,
            (∑ m : divisorFactorTuples 3 t, C t r m) *
              ((d * t : ℕ) : ℂ) ^ (-s) := by rw [Finset.sum_mul]
        _ = ∑ r : divisorFactorTuples 3 d,
              ∑ m : divisorFactorTuples 3 t,
                C t r m * ((d * t : ℕ) : ℂ) ^ (-s) := by
          apply Fintype.sum_congr
          intro r
          rw [Finset.sum_mul]
    · simp [hres]
  have hallocated :
      (∑ t ∈ S,
        if (a' : ZMod Q) = (t : ZMod Q) then
          f (d * t) * ((d * t : ℕ) : ℂ) ^ (-s) else 0) =
      ∑ r : divisorFactorTuples 3 d,
        ∑ t ∈ S,
          ∑ m : divisorFactorTuples 3 t,
            if (a' : ZMod Q) = (t : ZMod Q) then
              C t r m * ((d * t : ℕ) : ℂ) ^ (-s) else 0 := by
    calc
      _ = ∑ t ∈ S,
            ∑ r : divisorFactorTuples 3 d,
              ∑ m : divisorFactorTuples 3 t,
                if (a' : ZMod Q) = (t : ZMod Q) then
                  C t r m * ((d * t : ℕ) : ℂ) ^ (-s) else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hpoint t ht
      _ = _ := by rw [Finset.sum_comm]
  have hfixedSum :
      (∑ r : divisorFactorTuples 3 d,
        ∑ t ∈ S,
          ∑ m : divisorFactorTuples 3 t,
            if (a' : ZMod Q) = (t : ZMod Q) then
              C t r m * ((d * t : ℕ) : ℂ) ^ (-s) else 0) =
      ∑ r : divisorFactorTuples 3 d, c * A r := by
    apply Fintype.sum_congr
    intro r
    have hfix := fixedAllocatedMellinFactorization (q := q) hQpos hdpos a' ha' r
      a₁ a₂ a₃ hN₁ hN₂ hN₃ hsupp₁ hsupp₂ hsupp₃ s
    simpa [S, P, C, A, c, allocatedMellinCutoff,
      allocatedMellinCoefficientProduct] using hfix
  have hlarge :
      (∑ n ∈ Finset.Icc 1 (d * P), g n) =
        c * ∑ r : divisorFactorTuples 3 d, A r := by
    calc
      _ = ∑ t ∈ S,
            if (a' : ZMod Q) = (t : ZMod Q) then
              f (d * t) * ((d * t : ℕ) : ℂ) ^ (-s) else 0 := hReindex
      _ = ∑ r : divisorFactorTuples 3 d,
            ∑ t ∈ S,
              ∑ m : divisorFactorTuples 3 t,
                if (a' : ZMod Q) = (t : ZMod Q) then
                  C t r m * ((d * t : ℕ) : ℂ) ^ (-s) else 0 := hallocated
      _ = ∑ r : divisorFactorTuples 3 d, c * A r := hfixedSum
      _ = c * ∑ r : divisorFactorTuples 3 d, A r := by
        rw [Finset.mul_sum]
  change (∑ n ∈ Finset.Icc 1 P, g n) =
      c * ∑ r : divisorFactorTuples 3 d, A r
  calc
    _ = ∑ n ∈ Finset.Icc 1 (d * P), g n := hsmallEqLarge
    _ = _ := hlarge

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.nonunitTripleCharacterFactorizationFinite

namespace FractionalPrimes.Literature.Twisted

/-- Blueprint-name alias for the finite nonunit triple character identity. -/
abbrev nonunitTripleCharacterFactorization :=
  nonunitTripleCharacterFactorizationFinite

end FractionalPrimes.Literature.Twisted

#print axioms FractionalPrimes.Literature.Twisted.nonunitTripleCharacterFactorization
