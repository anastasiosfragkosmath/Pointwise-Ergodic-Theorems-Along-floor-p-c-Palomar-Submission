module

public import FractionalPrimes.Literature.Twisted.SequentialGcdAllocation
public import FractionalPrimes.Literature.Uniformity.DivisorTupleCount

/-!
# Flattening ordered gcd allocation by factor label

The recursive gcd allocation is converted to ordered tuples so a
specified factor can be selected without changing its label.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity

/-- Split an ordered positive factor tuple into its first factor and
the residual tuple. This is the combinatorial reindex used to
flatten sequential gcd allocation. -/
def splitFirstFactorTuple (k : ℕ) (n : PositiveInteger) :
    divisorFactorTuples (k + 1) n.1 ≃
      Σ d : PositiveDivisor n, divisorFactorTuples k (n.1 / d.1) := by
  classical
  refine {
    toFun := fun v => ?_
    invFun := fun q => ?_
    left_inv := ?_
    right_inv := ?_ }
  · let d : ℕ := (v.1 0).1
    have hprod : d * ∏ i : Fin k, (v.1 i.succ).1 = n.1 := by
      simpa [d, Fin.prod_univ_succ] using v.2
    have hdmem : d ∈ n.1.divisors := by
      apply Nat.mem_divisors.mpr
      exact ⟨⟨_, hprod.symm⟩, Nat.ne_of_gt n.2⟩
    refine ⟨⟨d, hdmem⟩, ⟨fun i => v.1 i.succ, ?_⟩⟩
    have hdpos : 0 < d := (v.1 0).2
    symm
    apply (Nat.div_eq_iff_eq_mul_left hdpos (Nat.dvd_of_mem_divisors hdmem)).2
    simpa [Nat.mul_comm] using hprod.symm
  · let d : PositiveInteger := ⟨q.1.1, Nat.pos_of_mem_divisors q.1.2⟩
    refine ⟨Fin.cons d q.2.1, ?_⟩
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, q.2.2]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors q.1.2)
  · intro v
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  · rintro ⟨d, tail⟩
    apply Sigma.subtype_ext
    · rfl
    · rfl

theorem splitFirstFactorTuple_symm_val (k : ℕ) (n : PositiveInteger)
    (d : PositiveDivisor n) (tail : divisorFactorTuples k (n.1 / d.1)) :
    ((splitFirstFactorTuple k n).symm ⟨d, tail⟩).1 =
      Fin.cons (⟨d.1, Nat.pos_of_mem_divisors d.2⟩ : PositiveInteger) tail.1 := by
  rfl

private theorem prefixProduct_succ (k : ℕ) (d : Fin (k + 1) → ℕ)
    (i : Fin k) :
    (∏ j ∈ Finset.Iic i.succ, d j) =
      d 0 * ∏ j ∈ Finset.Iic i, d j.succ := by
  classical
  have hset : (Finset.Iic i.succ : Finset (Fin (k + 1))) =
      insert 0 ((Finset.Iic i).image Fin.succ) := by
    ext j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simp [Fin.succ_le_succ_iff]
  rw [hset, Finset.prod_insert]
  · rw [Finset.prod_image]
    intro a ha b hb hab
    exact (Fin.succ_injective k) hab
  · simp

/-- The labeled ordered-tuple form of the gcd allocation. The cutoff at
factor `i` is exactly the quotient by the product of the allocated
factors through `i`. -/
noncomputable def flatGcdAllocatedConvolution
    (fs : List (ArithmeticFunction ℂ)) (r n : ℕ) : ℂ :=
  ∑ d : divisorFactorTuples fs.length r,
    ∑ m : divisorFactorTuples fs.length n,
      if ∀ i : Fin fs.length,
          Nat.Coprime (m.1 i).1
            (r / ∏ j ∈ Finset.Iic i, (d.1 j).1) then
        ∏ i : Fin fs.length,
          (fs.get i) ((d.1 i).1 * (m.1 i).1)
      else 0

theorem flatGcdCoprime_cons (k r : ℕ)
    (d₀ m₀ : PositiveInteger)
    (d m : Fin k → PositiveInteger) :
    (∀ i : Fin (k + 1),
      Nat.Coprime (((Fin.cons m₀ m : Fin (k + 1) → PositiveInteger) i).1)
        (r / ∏ j ∈ Finset.Iic i,
          (((Fin.cons d₀ d : Fin (k + 1) → PositiveInteger) j).1))) ↔
      Nat.Coprime m₀.1 (r / d₀.1) ∧
        ∀ i : Fin k,
          Nat.Coprime (m i).1
            ((r / d₀.1) / ∏ j ∈ Finset.Iic i, (d j).1) := by
  have hzero : (Finset.Iic (0 : Fin (k + 1))) = {0} := by
    ext j
    simp
  constructor
  · intro h
    constructor
    · simpa [hzero] using h 0
    · intro i
      have hi := h i.succ
      rw [prefixProduct_succ] at hi
      simpa [Nat.div_div_eq_div_mul, Nat.mul_comm, Fin.cons_zero,
        Fin.cons_succ] using hi
  · rintro ⟨h₀, ht⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hzero] using h₀
    · have hj := ht j
      rw [prefixProduct_succ]
      simpa [Nat.div_div_eq_div_mul, Nat.mul_comm, Fin.cons_zero,
        Fin.cons_succ] using hj

theorem sum_divisorFactorTuples_splitFirst (k : ℕ)
    {r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (F : divisorFactorTuples (k + 1) r →
      divisorFactorTuples (k + 1) n → ℂ) :
    (∑ d : divisorFactorTuples (k + 1) r,
      ∑ m : divisorFactorTuples (k + 1) n, F d m) =
      ∑ d : Σ d₀ : PositiveDivisor ⟨r, hr⟩,
          divisorFactorTuples k (r / d₀.1),
        ∑ m : Σ m₀ : PositiveDivisor ⟨n, hn⟩,
            divisorFactorTuples k (n / m₀.1),
          F ((splitFirstFactorTuple k ⟨r, hr⟩).symm d)
            ((splitFirstFactorTuple k ⟨n, hn⟩).symm m) := by
  classical
  let er := splitFirstFactorTuple k ⟨r, hr⟩
  let en := splitFirstFactorTuple k ⟨n, hn⟩
  calc
    (∑ d : divisorFactorTuples (k + 1) r,
      ∑ m : divisorFactorTuples (k + 1) n, F d m) =
        ∑ d : Σ d₀ : PositiveDivisor ⟨r, hr⟩,
          divisorFactorTuples k (r / d₀.1),
          ∑ m : divisorFactorTuples (k + 1) n, F (er.symm d) m := by
            apply Fintype.sum_equiv er
            intro d
            simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Fintype.sum_equiv en
      intro m
      simp [er, en]

theorem flatGcdTerm_cons (fs : List (ArithmeticFunction ℂ))
    (f : ArithmeticFunction ℂ) (r : ℕ)
    (d₀ m₀ : PositiveInteger)
    (d m : Fin fs.length → PositiveInteger) :
    (if ∀ i : Fin (fs.length + 1),
        Nat.Coprime (((Fin.cons m₀ m : Fin (fs.length + 1) → PositiveInteger) i).1)
          (r / ∏ j ∈ Finset.Iic i,
            (((Fin.cons d₀ d : Fin (fs.length + 1) → PositiveInteger) j).1))
      then ∏ i : Fin (fs.length + 1),
        ((f :: fs).get i)
          (((Fin.cons d₀ d : Fin (fs.length + 1) → PositiveInteger) i).1 *
            ((Fin.cons m₀ m : Fin (fs.length + 1) → PositiveInteger) i).1)
      else 0) =
      if Nat.Coprime m₀.1 (r / d₀.1) then
        f (d₀.1 * m₀.1) *
          (if ∀ i : Fin fs.length,
              Nat.Coprime (m i).1
                ((r / d₀.1) / ∏ j ∈ Finset.Iic i, (d j).1) then
            ∏ i : Fin fs.length, (fs.get i) ((d i).1 * (m i).1)
          else 0)
      else 0 := by
  classical
  simp only [flatGcdCoprime_cons]
  by_cases h₀ : Nat.Coprime m₀.1 (r / d₀.1)
  · by_cases ht : ∀ i : Fin fs.length,
        Nat.Coprime (m i).1
          ((r / d₀.1) / ∏ j ∈ Finset.Iic i, (d j).1)
    · rw [if_pos ⟨h₀, ht⟩, if_pos h₀, if_pos ht]
      simp [Fin.prod_univ_succ]
    · rw [if_neg (fun h => ht h.2), if_pos h₀, if_neg ht]
      simp
  · rw [if_neg (fun h => h₀ h.1), if_neg h₀]

private theorem flatGcdAllocatedConvolution_cons
    (f : ArithmeticFunction ℂ) (fs : List (ArithmeticFunction ℂ))
    (r n : PositiveInteger) :
    flatGcdAllocatedConvolution (f :: fs) r.1 n.1 =
      ∑ d : PositiveDivisor r,
        ∑ m : PositiveDivisor n,
          if Nat.Coprime m.1 (r.1 / d.1) then
            f (d.1 * m.1) *
              flatGcdAllocatedConvolution fs (r.1 / d.1) (n.1 / m.1)
          else 0 := by
  classical
  unfold flatGcdAllocatedConvolution
  simp only [List.length_cons]
  rw [sum_divisorFactorTuples_splitFirst fs.length r.2 n.2]
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d₀ hd₀
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m₀ hm₀
  simp_rw [splitFirstFactorTuple_symm_val]
  simp_rw [flatGcdTerm_cons]
  by_cases hcop : Nat.Coprime m₀.1 (r.1 / d₀.1)
  · simp [hcop, Finset.mul_sum]
  · simp [hcop]

private theorem flatGcdAllocatedConvolution_nil (r n : ℕ) :
    flatGcdAllocatedConvolution [] r n =
      if r * n = 1 then 1 else 0 := by
  classical
  have hcard (t : ℕ) :
      Fintype.card (divisorFactorTuples 0 t) = if t = 1 then 1 else 0 := by
    by_cases ht : t = 1
    · have hc : Fintype.card (divisorFactorTuples 0 t) = 1 := by
        apply Fintype.card_eq_one_iff.mpr
        refine ⟨⟨Fin.elim0, by simp [ht]⟩, ?_⟩
        intro v
        apply Subtype.ext
        funext i
        exact Fin.elim0 i
      simpa [ht] using hc
    · have hc : Fintype.card (divisorFactorTuples 0 t) = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        exact ⟨fun v => ht (by simpa [divisorFactorTuples] using v.2.symm)⟩
      simp [ht, hc]
  have hmul : r * n = 1 ↔ r = 1 ∧ n = 1 := by
    constructor
    · intro h
      constructor
      · exact Nat.dvd_one.mp ⟨n, h.symm⟩
      · exact Nat.dvd_one.mp ⟨r, by simpa [Nat.mul_comm] using h.symm⟩
    · rintro ⟨rfl, rfl⟩
      norm_num
  by_cases hr : r = 1 <;> by_cases hn : n = 1 <;>
    simp [flatGcdAllocatedConvolution, hcard, hmul, hr, hn]

private theorem sum_positiveDivisors (n : PositiveInteger) (F : ℕ → ℂ) :
    (∑ d : PositiveDivisor n, F d.1) =
      ∑ d ∈ n.1.divisors, F d := by
  classical
  exact (Finset.sum_subtype n.1.divisors (by intro x; rfl) F).symm

private theorem sum_positiveDivisors₂ (r n : PositiveInteger)
    (F : ℕ → ℕ → ℂ) :
    (∑ d : PositiveDivisor r, ∑ m : PositiveDivisor n, F d.1 m.1) =
      ∑ d ∈ r.1.divisors, ∑ m ∈ n.1.divisors, F d m := by
  classical
  have hfirst := sum_positiveDivisors r
    (fun d => ∑ m : PositiveDivisor n, F d m.1)
  rw [hfirst]
  apply Finset.sum_congr rfl
  intro d hd
  exact sum_positiveDivisors n (F d)

private theorem sequentialGcdAllocatedConvolution_cons_sigma
    (f : ArithmeticFunction ℂ) (fs : List (ArithmeticFunction ℂ))
    (r n : PositiveInteger) :
    sequentialGcdAllocatedConvolution (f :: fs) r.1 n.1 =
      ∑ d : PositiveDivisor r,
        ∑ m : PositiveDivisor n,
          if Nat.Coprime m.1 (r.1 / d.1) then
            f (d.1 * m.1) *
              sequentialGcdAllocatedConvolution fs (r.1 / d.1) (n.1 / m.1)
          else 0 := by
  classical
  let F : ℕ → ℕ → ℂ := fun d m =>
    if Nat.Coprime m (r.1 / d) then
      f (d * m) * sequentialGcdAllocatedConvolution fs (r.1 / d) (n.1 / m)
    else 0
  calc
    sequentialGcdAllocatedConvolution (f :: fs) r.1 n.1 =
        ∑ d ∈ r.1.divisors, ∑ m ∈ n.1.divisors, F d m := by
          simp [sequentialGcdAllocatedConvolution,
            complexNaturalDirichletConvolution,
            sequentialGcdAllocatedFactor, F, ite_mul]
    _ = _ := by
      simpa only [F] using (sum_positiveDivisors₂ r n F).symm

theorem flatGcdAllocatedConvolution_eq_sequential
    (fs : List (ArithmeticFunction ℂ)) (r n : PositiveInteger) :
    flatGcdAllocatedConvolution fs r.1 n.1 =
      sequentialGcdAllocatedConvolution fs r.1 n.1 := by
  induction fs generalizing r n with
  | nil =>
      simpa [sequentialGcdAllocatedConvolution] using
        flatGcdAllocatedConvolution_nil r.1 n.1
  | cons f fs ih =>
      rw [flatGcdAllocatedConvolution_cons f fs r n,
        sequentialGcdAllocatedConvolution_cons_sigma f fs r n]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hcop : Nat.Coprime m.1 (r.1 / d.1)
      · have hrdiv : 0 < r.1 / d.1 :=
          Nat.div_pos (Nat.le_of_dvd r.2 (Nat.dvd_of_mem_divisors d.2))
            (Nat.pos_of_mem_divisors d.2)
        have hndiv : 0 < n.1 / m.1 :=
          Nat.div_pos (Nat.le_of_dvd n.2 (Nat.dvd_of_mem_divisors m.2))
            (Nat.pos_of_mem_divisors m.2)
        simp [hcop, ih ⟨r.1 / d.1, hrdiv⟩ ⟨n.1 / m.1, hndiv⟩]
      · simp [hcop]

/-- The flat labeled tuple expansion of sequential gcd allocation. -/
theorem flatGcdAllocation
    (fs : List (ArithmeticFunction ℂ)) {r n : ℕ}
    (hr : 0 < r) (hn : 0 < n) :
    (fs.prod) (r * n) = flatGcdAllocatedConvolution fs r n := by
  rw [sequentialGcdAllocation fs hr hn]
  exact (flatGcdAllocatedConvolution_eq_sequential fs ⟨r, hr⟩ ⟨n, hn⟩).symm

end FractionalPrimes.Literature.Twisted

end
