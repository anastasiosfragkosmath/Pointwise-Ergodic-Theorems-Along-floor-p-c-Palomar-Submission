module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothGroupMellinPhaseBookkeeping
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.Algebra.Order.Antidiag.Nat
public import Mathlib.Data.Finset.Pi
public import Mathlib.Tactic

/-!
# Supported finite tuple expansion for ordered Dirichlet convolution

This file proves the source bridge from an ordered finite factor convolution
to the supported tuple sum used by the selected-group estimate.  The general
product is first expanded over the multiplicative antidiagonal, then restricted
to the factors' finite supports; the Mellin twist is factored by the checked
finite phase product identity.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open Finset

private theorem finMulAntidiag_succ_sum {k n : ℕ} {R : Type*}
    [AddCommMonoid R] (F : (Fin (k + 1) → ℕ) → R) :
    (∑ m ∈ Nat.finMulAntidiag (k + 1) n, F m) =
      ∑ p ∈ Nat.divisorsAntidiagonal n,
        ∑ v ∈ Nat.finMulAntidiag k p.2, F (Fin.cons p.1 v) := by
  classical
  let A := Nat.divisorsAntidiagonal n
  let B := A.sigma (fun p => Nat.finMulAntidiag k p.2)
  let e : (Σ p : ℕ × ℕ, Fin k → ℕ) → (Fin (k + 1) → ℕ) :=
    fun z => Fin.cons z.1.1 z.2
  have hmem (z : Σ p : ℕ × ℕ, Fin k → ℕ) (hz : z ∈ B) :
      e z ∈ Nat.finMulAntidiag (k + 1) n := by
    rcases Finset.mem_sigma.mp hz with ⟨hp, hv⟩
    have hp' := Nat.mem_divisorsAntidiagonal.mp hp
    have hv' := Nat.mem_finMulAntidiag.mp hv
    rw [Nat.mem_finMulAntidiag]
    constructor
    · simpa [e, Fin.prod_univ_succ, hv'.1] using hp'.1
    · exact hp'.2
  have hinj : ∀ z₁ ∈ B, ∀ z₂ ∈ B, e z₁ = e z₂ → z₁ = z₂ := by
    intro z₁ hz₁ z₂ hz₂ h
    rcases Finset.mem_sigma.mp hz₁ with ⟨hp₁, hv₁⟩
    rcases Finset.mem_sigma.mp hz₂ with ⟨hp₂, hv₂⟩
    have hp₁' := Nat.mem_divisorsAntidiagonal.mp hp₁
    have hp₂' := Nat.mem_divisorsAntidiagonal.mp hp₂
    have hv₁' := Nat.mem_finMulAntidiag.mp hv₁
    have hv₂' := Nat.mem_finMulAntidiag.mp hv₂
    have hhead : z₁.1.1 = z₂.1.1 := by
      have h0 := congrFun h 0
      simpa [e] using h0
    have htail : z₁.2 = z₂.2 := by
      funext i
      have hs := congrFun h i.succ
      simpa [e] using hs
    have hprod : z₁.1.2 = z₂.1.2 := by
      calc
        z₁.1.2 = ∏ i : Fin k, z₁.2 i := hv₁'.1.symm
        _ = ∏ i : Fin k, z₂.2 i := by rw [htail]
        _ = z₂.1.2 := hv₂'.1
    cases z₁ with
    | mk p₁ v₁ =>
      cases z₂ with
      | mk p₂ v₂ =>
        dsimp at hhead hprod htail
        have hp : p₁ = p₂ := Prod.ext hhead hprod
        subst p₂
        have hv : v₁ = v₂ := htail
        subst v₂
        rfl
  have hsurj : ∀ m ∈ Nat.finMulAntidiag (k + 1) n,
      ∃ z ∈ B, e z = m := by
    intro m hm
    have hm' := Nat.mem_finMulAntidiag.mp hm
    let b := ∏ i : Fin k, m i.succ
    let v : Fin k → ℕ := fun i => m i.succ
    let p : ℕ × ℕ := (m 0, b)
    have hprod : m 0 * b = n := by
      dsimp [b]
      simpa [Fin.prod_univ_succ] using hm'.1
    have hp : p ∈ Nat.divisorsAntidiagonal n := by
      rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨hprod, hm'.2⟩
    have hb : b ≠ 0 := by
      intro hb0
      apply hm'.2
      rw [← hprod, hb0]
      simp
    have hv : v ∈ Nat.finMulAntidiag k p.2 := by
      rw [Nat.mem_finMulAntidiag]
      exact ⟨by simp [v, p, b], hb⟩
    refine ⟨⟨p, v⟩, Finset.mem_sigma.mpr ⟨hp, hv⟩, ?_⟩
    apply funext
    intro i
    cases i using Fin.cases with
    | zero => simp [e, p]
    | succ j => simp [e, v]
  calc
    (∑ m ∈ Nat.finMulAntidiag (k + 1) n, F m) =
        ∑ z ∈ B, F (e z) := by
          symm
          refine Finset.sum_bij (fun z _ => e z) ?_ ?_ ?_ ?_
          · exact hmem
          · exact hinj
          · intro m hm
            obtain ⟨z, hz, heq⟩ := hsurj m hm
            exact ⟨z, hz, heq⟩
          · intro z hz
            rfl
    _ = ∑ p ∈ Nat.divisorsAntidiagonal n,
        ∑ v ∈ Nat.finMulAntidiag k p.2, F (Fin.cons p.1 v) := by
          simp [B, A, Finset.sum_sigma, e]

/-- The ordered finite product of arithmetic functions has its exact
coefficient expansion over the finite multiplicative antidiagonal in any
commutative semiring. -/
theorem arithmeticFunctionFinProduct_apply_finMulAntidiag_general
    {R : Type*} [CommSemiring R]
    (k : ℕ) (f : Fin k → ArithmeticFunction R) (n : ℕ) :
    (∏ i : Fin k, f i) n =
      ∑ m ∈ Nat.finMulAntidiag k n, ∏ i : Fin k, f i (m i) := by
  classical
  induction k generalizing n with
  | zero =>
      by_cases hn : n = 1
      · subst n
        simp [Nat.finMulAntidiag_one]
      · simp [Nat.finMulAntidiag_zero_left hn, hn]
  | succ k ih =>
      rw [Fin.prod_univ_succ, ArithmeticFunction.mul_apply]
      simp_rw [ih (fun i => f i.succ)]
      calc
        (∑ p ∈ Nat.divisorsAntidiagonal n,
            f 0 p.1 *
              ∑ m ∈ Nat.finMulAntidiag k p.2,
                ∏ i : Fin k, f i.succ (m i)) =
          ∑ p ∈ Nat.divisorsAntidiagonal n,
            ∑ m ∈ Nat.finMulAntidiag k p.2,
              f 0 p.1 * ∏ i : Fin k, f i.succ (m i) := by
                apply Finset.sum_congr rfl
                intro p hp
                rw [Finset.mul_sum]
        _ = ∑ m ∈ Nat.finMulAntidiag (k + 1) n,
              ∏ i : Fin (k + 1), f i (m i) := by
                rw [finMulAntidiag_succ_sum]
                apply Finset.sum_congr rfl
                intro p hp
                apply Finset.sum_congr rfl
                intro m hm
                simp [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Complex-valued specialization of the ordered finite product expansion. -/
theorem arithmeticFunctionFinProduct_apply_finMulAntidiag
    (k : ℕ) (f : Fin k → ArithmeticFunction ℂ) (n : ℕ) :
    (∏ i : Fin k, f i) n =
      ∑ m ∈ Nat.finMulAntidiag k n, ∏ i : Fin k, f i (m i) :=
  arithmeticFunctionFinProduct_apply_finMulAntidiag_general k f n

/-- Real-valued specialization for smooth Heath--Brown factors. -/
theorem arithmeticFunctionRealFinProduct_apply_finMulAntidiag
    (k : ℕ) (f : Fin k → ArithmeticFunction ℝ) (n : ℕ) :
    (∏ i : Fin k, f i) n =
      ∑ m ∈ Nat.finMulAntidiag k n, ∏ i : Fin k, f i (m i) :=
  arithmeticFunctionFinProduct_apply_finMulAntidiag_general k f n

/-- Supported tuple expansion for an ordered finite product. -/
theorem arithmeticFunctionFinProduct_apply_supportedTupleSum
    (k : ℕ) (f : Fin k → ArithmeticFunction ℂ)
    (S : Fin k → Finset ℕ)
    (hf : ∀ i n, n ∉ S i → f i n = 0)
    (hpos : ∀ i n, n ∈ S i → 0 < n) (n : ℕ) :
    (∏ i : Fin k, f i) n =
      ∑ m ∈ (Fintype.piFinset S).filter (fun m => ∏ i : Fin k, m i = n),
        ∏ i : Fin k, f i (m i) := by
  classical
  let R := (Fintype.piFinset S).filter (fun m => ∏ i : Fin k, m i = n)
  have hRsub : R ⊆ Nat.finMulAntidiag k n := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmS, hmprod⟩
    rw [Nat.mem_finMulAntidiag]
    constructor
    · exact hmprod
    · have hmpos : 0 < ∏ i : Fin k, m i :=
        Finset.prod_pos fun i hi => hpos i (m i) (Fintype.mem_piFinset.mp hmS i)
      rw [hmprod] at hmpos
      exact hmpos.ne'
  have hzero : ∀ m ∈ Nat.finMulAntidiag k n, m ∉ R →
      ∏ i : Fin k, f i (m i) = 0 := by
    intro m hm hmR
    have hsome : ∃ i : Fin k, m i ∉ S i := by
      by_contra h
      push Not at h
      apply hmR
      apply Finset.mem_filter.mpr
      exact ⟨Fintype.mem_piFinset.mpr h,
        (Nat.mem_finMulAntidiag.mp hm).1⟩
    rcases hsome with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hf i (m i) hi)
  rw [arithmeticFunctionFinProduct_apply_finMulAntidiag]
  change (∑ m ∈ Nat.finMulAntidiag k n, ∏ i : Fin k, f i (m i)) =
    ∑ m ∈ R, ∏ i : Fin k, f i (m i)
  symm
  exact Finset.sum_subset hRsub hzero

/-- Mellin twisting of the supported tuple expansion. -/
theorem arithmeticFunctionFinProduct_apply_supportedTupleSum_mellin
    (k : ℕ) (f : Fin k → ArithmeticFunction ℂ)
    (S : Fin k → Finset ℕ)
    (hf : ∀ i n, n ∉ S i → f i n = 0)
    (hpos : ∀ i n, n ∈ S i → 0 < n) (n : ℕ) (s : ℂ) :
    (∏ i : Fin k, f i) n * (n : ℂ) ^ s =
      ∑ m ∈ (Fintype.piFinset S).filter (fun m => ∏ i : Fin k, m i = n),
        ∏ i : Fin k, (f i (m i) * (m i : ℂ) ^ s) := by
  rw [arithmeticFunctionFinProduct_apply_supportedTupleSum k f S hf hpos n,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨_, hmprod⟩
  have hphase :
      ((∏ i : Fin k, m i : ℕ) : ℂ) ^ s =
        ∏ i : Fin k, (m i : ℂ) ^ s := by
    simpa using smoothGroupCpow_natProduct (Finset.univ : Finset (Fin k)) m s
  calc
    (∏ i : Fin k, f i (m i)) * (n : ℂ) ^ s =
        (∏ i : Fin k, f i (m i)) *
          ((∏ i : Fin k, m i : ℕ) : ℂ) ^ s := by rw [hmprod]
    _ = (∏ i : Fin k, f i (m i)) *
          (∏ i : Fin k, (m i : ℂ) ^ s) := by rw [hphase]
    _ = ∏ i : Fin k, (f i (m i) * (m i : ℂ) ^ s) := by
          rw [← Finset.prod_mul_distrib]

/-- Source-exponent specialization of the ordered finite product expansion. -/
theorem arithmeticFunctionFinProduct_apply_supportedTupleSum_sourcePhase
    (k : ℕ) (f : Fin k → ArithmeticFunction ℂ)
    (S : Fin k → Finset ℕ)
    (hf : ∀ i n, n ∉ S i → f i n = 0)
    (hpos : ∀ i n, n ∈ S i → 0 < n) (n : ℕ) (t : ℝ) :
    (∏ i : Fin k, f i) n *
        (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
      ∑ m ∈ (Fintype.piFinset S).filter (fun m => ∏ i : Fin k, m i = n),
        ∏ i : Fin k,
          (f i (m i) *
            (m i : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) :=
  arithmeticFunctionFinProduct_apply_supportedTupleSum_mellin
    k f S hf hpos n (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))

/-- Coefficient expansion for a selected group indexed by a finite subset of
the ambient ordered factor indices. -/
theorem arithmeticFunctionSubsetProduct_apply_supportedTupleSum
    {K : ℕ} (I : Finset (Fin K)) (f : Fin K → ArithmeticFunction ℂ)
    (S : Fin K → Finset ℕ)
    (hf : ∀ i ∈ I, ∀ n, n ∉ S i → f i n = 0)
    (hpos : ∀ i ∈ I, ∀ n, n ∈ S i → 0 < n) (n : ℕ) :
    (∏ i : I, f i.val) n =
      ∑ m ∈ (Fintype.piFinset (fun i : I => S i.val)).filter
          (fun m => ∏ i : I, m i = n),
        ∏ i : I, f i.val (m i) := by
  classical
  let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
  let E : (Fin I.card → ℕ) ≃ (I → ℕ) := {
    toFun := fun m i => m (e.symm i)
    invFun := fun m j => m (e j)
    left_inv := by
      intro m
      funext j
      simp
    right_inv := by
      intro m
      funext i
      simp }
  let SFin : Fin I.card → Finset ℕ := fun j => S (e j).val
  let SSub : I → Finset ℕ := fun i => S i.val
  let fFin : Fin I.card → ArithmeticFunction ℂ := fun j => f (e j).val
  let PF : (Fin I.card → ℕ) → Prop := fun m => ∏ j : Fin I.card, m j = n
  let PS : (I → ℕ) → Prop := fun m => ∏ i : I, m i = n
  let CF : (Fin I.card → ℕ) → ℂ := fun m =>
    ∏ j : Fin I.card, fFin j (m j)
  let CS : (I → ℕ) → ℂ := fun m =>
    ∏ i : I, f i.val (m i)
  have htupleProduct (m : Fin I.card → ℕ) :
      (∏ i : I, E m i) = ∏ j : Fin I.card, m j := by
    simpa [E, e] using (Equiv.prod_comp e.symm m)
  have hcoefficientProduct (m : Fin I.card → ℕ) :
      CS (E m) = CF m := by
    let g : Fin I.card → ℂ := fun j => f (e j).val (m j)
    calc
      CS (E m) = ∏ i : I, f i.val (m (e.symm i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [E]
      _ = ∏ i : I, g (e.symm i) := by
        apply Finset.prod_congr rfl
        intro i hi
        dsimp [g]
        exact (congrArg (fun j : I => f j.val (m (e.symm i)) )
          (e.apply_symm_apply i)).symm
      _ = ∏ j : Fin I.card, g j := Equiv.prod_comp e.symm g
      _ = CF m := by simp [CF, g, fFin]
  have hconv :
      (∏ i : I, f i.val) = ∏ j : Fin I.card, fFin j := by
    simpa [fFin, e] using
      (Equiv.prod_comp e.symm (fun j : Fin I.card => f (e j).val))
  rw [hconv, arithmeticFunctionFinProduct_apply_supportedTupleSum
    I.card fFin SFin (by
      intro j a ha
      exact hf (e j).val (e j).property a (by simpa [SFin] using ha))
    (by
      intro j a ha
      exact hpos (e j).val (e j).property a (by simpa [SFin] using ha)) n]
  change (∑ m ∈ (Fintype.piFinset SFin).filter PF, CF m) =
    ∑ m ∈ (Fintype.piFinset SSub).filter PS, CS m
  refine Finset.sum_bij (fun m _ => E m) ?_ ?_ ?_ ?_
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmSupport, hmProduct⟩
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro i
      have hcoord := (Fintype.mem_piFinset.mp hmSupport) (e.symm i)
      have he : e (e.symm i) = i := e.apply_symm_apply i
      simpa [E, SFin, SSub, he] using hcoord
    · change ∏ i : I, E m i = n
      rw [htupleProduct]
      exact hmProduct
  · intro m₁ hm₁ m₂ hm₂ heq
    exact E.injective heq
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmSupport, hmProduct⟩
    refine ⟨E.symm m, ?_, E.apply_symm_apply m⟩
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro j
      have hcoord := (Fintype.mem_piFinset.mp hmSupport) (e j)
      simpa [SFin, SSub, E, e] using hcoord
    · have hproductBack : (∏ i : I, m i) =
          ∏ j : Fin I.card, E.symm m j := by
        calc
          (∏ i : I, m i) = ∏ i : I, E (E.symm m) i := by
            apply Finset.prod_congr rfl
            intro i hi
            exact (congrFun (E.apply_symm_apply m) i).symm
          _ = ∏ j : Fin I.card, E.symm m j := htupleProduct (E.symm m)
      change ∏ j : Fin I.card, E.symm m j = n
      rw [← hproductBack]
      exact hmProduct
  · intro m hm
    exact (hcoefficientProduct m).symm

/-- Mellin-twisted selected-group coefficient expansion. -/
theorem arithmeticFunctionSubsetProduct_apply_supportedTupleSum_mellin
    {K : ℕ} (I : Finset (Fin K)) (f : Fin K → ArithmeticFunction ℂ)
    (S : Fin K → Finset ℕ)
    (hf : ∀ i ∈ I, ∀ n, n ∉ S i → f i n = 0)
    (hpos : ∀ i ∈ I, ∀ n, n ∈ S i → 0 < n) (n : ℕ) (s : ℂ) :
    (∏ i : I, f i.val) n * (n : ℂ) ^ s =
      ∑ m ∈ (Fintype.piFinset (fun i : I => S i.val)).filter
          (fun m => ∏ i : I, m i = n),
        ∏ i : I, (f i.val (m i) * (m i : ℂ) ^ s) := by
  rw [arithmeticFunctionSubsetProduct_apply_supportedTupleSum I f S hf hpos n,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨_, hmprod⟩
  have hphase : ((∏ i : I, m i : ℕ) : ℂ) ^ s =
      ∏ i : I, (m i : ℂ) ^ s := by
    simpa using smoothGroupCpow_natProduct (Finset.univ : Finset I) m s
  calc
    (∏ i : I, f i.val (m i)) * (n : ℂ) ^ s =
        (∏ i : I, f i.val (m i)) *
          ((∏ i : I, m i : ℕ) : ℂ) ^ s := by rw [hmprod]
    _ = (∏ i : I, f i.val (m i)) *
          (∏ i : I, (m i : ℂ) ^ s) := by rw [hphase]
    _ = ∏ i : I, (f i.val (m i) * (m i : ℂ) ^ s) := by
          rw [← Finset.prod_mul_distrib]

/-- Exact source Mellin phase for the selected finite subset group. -/
theorem arithmeticFunctionSubsetProduct_apply_supportedTupleSum_sourcePhase
    {K : ℕ} (I : Finset (Fin K)) (f : Fin K → ArithmeticFunction ℂ)
    (S : Fin K → Finset ℕ)
    (hf : ∀ i ∈ I, ∀ n, n ∉ S i → f i n = 0)
    (hpos : ∀ i ∈ I, ∀ n, n ∈ S i → 0 < n) (n : ℕ) (t : ℝ) :
    (∏ i : I, f i.val) n *
        (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
      ∑ m ∈ (Fintype.piFinset (fun i : I => S i.val)).filter
          (fun m => ∏ i : I, m i = n),
        ∏ i : I,
          (f i.val (m i) *
            (m i : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) :=
  arithmeticFunctionSubsetProduct_apply_supportedTupleSum_mellin
    I f S hf hpos n (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))

/-- The coefficient of a two-factor Dirichlet convolution is the supported
finite tuple sum, provided each factor vanishes outside its declared finite
support and those supports contain only positive integers. -/
theorem arithmeticFunctionMul_apply_supportedTupleSum
    (f g : ArithmeticFunction ℂ) (S T : Finset ℕ)
    (hf : ∀ n, n ∉ S → f n = 0)
    (hg : ∀ n, n ∉ T → g n = 0)
    (hSpos : ∀ n ∈ S, 0 < n)
    (hTpos : ∀ n ∈ T, 0 < n) (n : ℕ) :
    (f * g) n =
      ∑ p ∈ (S ×ˢ T).filter (fun p => p.1 * p.2 = n),
        f p.1 * g p.2 := by
  classical
  rw [ArithmeticFunction.mul_apply]
  let R := (S ×ˢ T).filter (fun p => p.1 * p.2 = n)
  have hRsub : R ⊆ Nat.divisorsAntidiagonal n := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpST, hpProd⟩
    rcases Finset.mem_product.mp hpST with ⟨hpS, hpT⟩
    rw [Nat.mem_divisorsAntidiagonal]
    have hprodpos : 0 < p.1 * p.2 := Nat.mul_pos (hSpos p.1 hpS) (hTpos p.2 hpT)
    exact ⟨hpProd, by rw [← hpProd]; exact hprodpos.ne'⟩
  have hzero : ∀ p ∈ Nat.divisorsAntidiagonal n, p ∉ R →
      f p.1 * g p.2 = 0 := by
    intro p hp hpR
    have hpanti := Nat.mem_divisorsAntidiagonal.mp hp
    by_cases hpS : p.1 ∈ S
    · have hpT : p.2 ∉ T := by
        intro hpT
        apply hpR
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨hpS, hpT⟩, hpanti.1⟩
      simp [hg p.2 hpT]
    · simp [hf p.1 hpS]
  change (∑ p ∈ Nat.divisorsAntidiagonal n, f p.1 * g p.2) =
    ∑ p ∈ R, f p.1 * g p.2
  symm
  exact Finset.sum_subset hRsub hzero

/-- The exact two-factor source identity after inserting the Mellin power.
The phase of the product is factored over the two tuple coordinates. -/
theorem arithmeticFunctionMul_apply_supportedTupleSum_mellin
    (f g : ArithmeticFunction ℂ) (S T : Finset ℕ)
    (hf : ∀ n, n ∉ S → f n = 0)
    (hg : ∀ n, n ∉ T → g n = 0)
    (hSpos : ∀ n ∈ S, 0 < n)
    (hTpos : ∀ n ∈ T, 0 < n) (n : ℕ) (s : ℂ) :
    (f * g) n * (n : ℂ) ^ s =
      ∑ p ∈ (S ×ˢ T).filter (fun p => p.1 * p.2 = n),
        (f p.1 * (p.1 : ℂ) ^ s) * (g p.2 * (p.2 : ℂ) ^ s) := by
  rw [arithmeticFunctionMul_apply_supportedTupleSum f g S T hf hg hSpos hTpos]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpProd⟩
  rw [← hpProd, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

/-- Specialization to the precise source exponent `-1/2-it`. -/
theorem arithmeticFunctionMul_apply_supportedTupleSum_sourcePhase
    (f g : ArithmeticFunction ℂ) (S T : Finset ℕ)
    (hf : ∀ n, n ∉ S → f n = 0)
    (hg : ∀ n, n ∉ T → g n = 0)
    (hSpos : ∀ n ∈ S, 0 < n)
    (hTpos : ∀ n ∈ T, 0 < n) (n : ℕ) (t : ℝ) :
    (f * g) n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
      ∑ p ∈ (S ×ˢ T).filter (fun p => p.1 * p.2 = n),
        (f p.1 * (p.1 : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) *
          (g p.2 * (p.2 : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) :=
  arithmeticFunctionMul_apply_supportedTupleSum_mellin f g S T hf hg
    hSpos hTpos n (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))

end FractionalPrimes.Literature.DirichletAdapter

#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionMul_apply_supportedTupleSum
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionMul_apply_supportedTupleSum_mellin
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionMul_apply_supportedTupleSum_sourcePhase
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionFinProduct_apply_finMulAntidiag_general
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionFinProduct_apply_finMulAntidiag
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionRealFinProduct_apply_finMulAntidiag
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionFinProduct_apply_supportedTupleSum
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionFinProduct_apply_supportedTupleSum_sourcePhase
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionSubsetProduct_apply_supportedTupleSum
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionSubsetProduct_apply_supportedTupleSum_mellin
#print axioms FractionalPrimes.Literature.DirichletAdapter.arithmeticFunctionSubsetProduct_apply_supportedTupleSum_sourcePhase
