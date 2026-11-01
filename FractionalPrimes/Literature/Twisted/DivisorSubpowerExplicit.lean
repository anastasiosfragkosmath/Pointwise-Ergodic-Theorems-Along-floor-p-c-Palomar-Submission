module

public import FractionalPrimes.Literature.Uniformity.DivisorFunctions
public import FractionalPrimes.Literature.Uniformity.DivisorMultiplicativeLift
public import FractionalPrimes.Literature.Uniformity.DivisorMomentBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit subpower bounds for divisor factors

This module formalizes the quantitative divisor estimate used by the
restricted twisted deduction.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity

/-- The explicit large-prime cutoff in the divisor subpower estimate. -/
noncomputable def divisorSubpowerCutoff (C : ℕ) (ε : ℝ) : ℝ :=
  (2 : ℝ) ^ ((C : ℝ) / ε)

/-- The exact constant `D_{C,ε}` from `ltw:divisor-subpower`. -/
noncomputable def divisorSubpowerConstant (C : ℕ) (ε : ℝ) : ℝ :=
  (1 + (C : ℝ) / (ε * Real.log 2)) ^
    (C * Nat.floor (divisorSubpowerCutoff C ε))

private theorem divisorFunction_two_prime_power (p e : ℕ) (hp : p.Prime) :
    divisorFunction 2 ⟨p ^ e, Nat.pow_pos hp.pos⟩ = e + 1 := by
  simpa using positiveDivisorFunction_prime_pow p 1 e hp

private theorem divisorFunction_two_factorization (n : PositiveInteger) :
    divisorFunction 2 n =
      n.1.factorization.prod (fun _ e => e + 1) := by
  rw [divisorFunction_factorization]
  unfold Finsupp.prod
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using hp)
  have hlocal := divisorFunction_two_prime_power p (n.1.factorization p) hprime
  simpa only [divisorFunction, Nat.cast_ofNat] using hlocal

private theorem divisorFunction_two_factorization_real (n : PositiveInteger) :
    (divisorFunction 2 n : ℝ) =
      n.1.factorization.prod (fun _ e => (e + 1 : ℝ)) := by
  rw [divisorFunction_two_factorization]
  norm_cast

private theorem real_finset_prod_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (ε : ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ ε = ∏ i ∈ s, f i ^ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Real.mul_rpow (hf i (Finset.mem_insert_self i s))
          (Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

private theorem natural_factorization_rpow (n : PositiveInteger) (ε : ℝ) :
    (n.1 : ℝ) ^ ε =
      n.1.factorization.prod (fun p e => ((p ^ e : ℕ) : ℝ) ^ ε) := by
  have hfactor : n.1 = n.1.factorization.prod (fun p e => p ^ e) :=
    (Nat.prod_factorization_pow_eq_self n.2.ne').symm
  have hfactorReal : (n.1 : ℝ) =
      n.1.factorization.prod (fun p e => ((p ^ e : ℕ) : ℝ)) := by
    exact_mod_cast hfactor
  rw [hfactorReal]
  unfold Finsupp.prod
  apply real_finset_prod_rpow
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using hp)
  exact (Nat.cast_nonneg _)

private theorem cast_nat_pow_rpow (p e : ℕ) (hp : 0 < p) (ε : ℝ) :
    ((p ^ e : ℕ) : ℝ) ^ ε = (p : ℝ) ^ (ε * (e : ℝ)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  calc
    ((p ^ e : ℕ) : ℝ) ^ ε = ((p : ℝ) ^ ε) ^ e := by
      rw [Nat.cast_pow]
      exact (Real.rpow_pow_comm (by positivity) ε e).symm
    _ = (p : ℝ) ^ (ε * (e : ℝ)) := by
      calc
        ((p : ℝ) ^ ε) ^ e = ((p : ℝ) ^ ε) ^ (e : ℝ) :=
          (Real.rpow_natCast _ _).symm
        _ = (p : ℝ) ^ (ε * (e : ℝ)) := (Real.rpow_mul hpR.le ε _).symm

private theorem divisorPrimePower_small_bound
    (C e p : ℕ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε)
    (hp : p.Prime) :
    (e + 1 : ℝ) ^ C ≤
      (1 + (C : ℝ) / (ε * Real.log 2)) ^ C *
        ((p ^ e : ℕ) : ℝ) ^ ε := by
  let c : ℝ := ε * Real.log (p : ℝ) / (C : ℝ)
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast hC
  have hp2 : 2 ≤ p := hp.two_le
  have hpLog : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos (mul_pos hε
      (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp2)))) hCpos
  have hcLower : ε * Real.log 2 / (C : ℝ) ≤ c := by
    dsimp [c]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpLog hε.le) hCpos.le
  have hcInv : c⁻¹ ≤ (C : ℝ) / (ε * Real.log 2) := by
    have hlowpos : 0 < ε * Real.log 2 / (C : ℝ) := by positivity
    have hinv := (inv_le_inv₀ hcpos hlowpos).2 hcLower
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hinv
  have hExp : c * (e : ℝ) + 1 ≤ Real.exp (c * (e : ℝ)) :=
    Real.add_one_le_exp _
  have hce : 0 ≤ c * (e : ℝ) := mul_nonneg hcpos.le (Nat.cast_nonneg e)
  have heDiv : (e : ℝ) ≤ Real.exp (c * (e : ℝ)) / c := by
    apply (le_div_iff₀ hcpos).2
    calc
      (e : ℝ) * c = c * (e : ℝ) := by ring
      _ ≤ Real.exp (c * (e : ℝ)) := by linarith
  have hOne : 1 ≤ Real.exp (c * (e : ℝ)) := by linarith
  have hBase : (e + 1 : ℝ) ≤ (1 + c⁻¹) * Real.exp (c * (e : ℝ)) := by
    calc
      (e + 1 : ℝ) ≤ Real.exp (c * (e : ℝ)) / c + Real.exp (c * (e : ℝ)) :=
        add_le_add heDiv hOne
      _ = (1 + c⁻¹) * Real.exp (c * (e : ℝ)) := by
        ring
  have hCoeff : 1 + c⁻¹ ≤ 1 + (C : ℝ) / (ε * Real.log 2) := by linarith
  have hCpow : (e + 1 : ℝ) ^ C ≤
      ((1 + c⁻¹) * Real.exp (c * (e : ℝ))) ^ C := by
    exact pow_le_pow_left₀ (by positivity) hBase C
  have hRpow : ((p ^ e : ℕ) : ℝ) ^ ε =
      Real.exp (Real.log (p : ℝ) * (ε * (e : ℝ))) := by
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    rw [cast_nat_pow_rpow p e hp.pos, Real.rpow_def_of_pos hpR]
  calc
    (e + 1 : ℝ) ^ C ≤
        ((1 + c⁻¹) * Real.exp (c * (e : ℝ))) ^ C := hCpow
    _ = (1 + c⁻¹) ^ C * Real.exp ((C : ℝ) * (c * (e : ℝ))) := by
      rw [mul_pow, ← Real.exp_nat_mul]
    _ ≤ (1 + (C : ℝ) / (ε * Real.log 2)) ^ C *
          Real.exp ((C : ℝ) * (c * (e : ℝ))) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hCoeff C)
        (Real.exp_nonneg _)
    _ = (1 + (C : ℝ) / (ε * Real.log 2)) ^ C *
          Real.exp (Real.log (p : ℝ) * (ε * (e : ℝ))) := by
      congr 1
      dsimp [c]
      field_simp [ne_of_gt hCpos]
    _ = (1 + (C : ℝ) / (ε * Real.log 2)) ^ C *
          ((p ^ e : ℕ) : ℝ) ^ ε := by rw [hRpow]

private theorem divisorPrimePower_large_bound
    (C e p : ℕ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε)
    (hp : p.Prime) (hpB : divisorSubpowerCutoff C ε ≤ (p : ℝ)) :
    (e + 1 : ℝ) ^ C ≤ ((p ^ e : ℕ) : ℝ) ^ ε := by
  have hsmall : e + 1 ≤ 2 ^ e := by
    cases e with
    | zero => norm_num
    | succ e =>
        have hlt : e + 1 < 2 ^ (e + 1) := Nat.lt_two_pow_self
        omega
  have hpow : (e + 1 : ℝ) ^ C ≤ (2 : ℝ) ^ (e * C) := by
    calc
      (e + 1 : ℝ) ^ C ≤ ((2 ^ e : ℕ) : ℝ) ^ C := by
        exact_mod_cast Nat.pow_le_pow_left hsmall C
      _ = (2 : ℝ) ^ (e * C) := by
        norm_num only [Nat.cast_pow]
        rw [← pow_mul]
  have hlogCut : ((C : ℝ) / ε) * Real.log 2 ≤ Real.log (p : ℝ) := by
    have hcutpos : 0 < divisorSubpowerCutoff C ε :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hlog := Real.log_le_log hcutpos hpB
    simpa [divisorSubpowerCutoff, Real.log_rpow (by norm_num : (0 : ℝ) < 2)] using hlog
  have hexpOrder : Real.log 2 * ((e * C : ℕ) : ℝ) ≤
      Real.log (p : ℝ) * (ε * (e : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hlogCut
      (mul_nonneg hε.le (Nat.cast_nonneg e))
    calc
      Real.log 2 * ((e * C : ℕ) : ℝ) =
          (((C : ℝ) / ε) * Real.log 2) * (ε * (e : ℝ)) := by
            push_cast
            field_simp [ne_of_gt hε]
      _ ≤ Real.log (p : ℝ) * (ε * (e : ℝ)) := hmul
  have hLeftExp : (2 : ℝ) ^ (e * C) =
      Real.exp (Real.log 2 * ((e * C : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  have hRightExp : ((p ^ e : ℕ) : ℝ) ^ ε =
      Real.exp (Real.log (p : ℝ) * (ε * (e : ℝ))) := by
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    rw [cast_nat_pow_rpow p e hp.pos, Real.rpow_def_of_pos hpR]
  calc
    (e + 1 : ℝ) ^ C ≤ (2 : ℝ) ^ (e * C) := hpow
    _ ≤ ((p ^ e : ℕ) : ℝ) ^ ε := by
      rw [hLeftExp, hRightExp]
      exact Real.exp_le_exp.mpr hexpOrder

/-- The exact explicit divisor-subpower assertion `ltw:divisor-subpower`.
Here `divisorFunction 2` is the blueprint's ordinary divisor function `τ`. -/
theorem divisorSubpowerExplicit
    {C : ℕ} (hC : 0 < C) {ε : ℝ} (hε : 0 < ε) (n : PositiveInteger) :
    (divisorFunction 2 n : ℝ) ^ C ≤
      divisorSubpowerConstant C ε * (n.1 : ℝ) ^ ε := by
  let B : ℝ := divisorSubpowerCutoff C ε
  let A : ℝ := 1 + (C : ℝ) / (ε * Real.log 2)
  let support := n.1.factorization.support
  let small : Finset ℕ := support.filter (fun p : ℕ => (p : ℝ) < B)
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast hC
  have hAone : 1 ≤ A := by
    dsimp [A]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdenom : 0 < ε * Real.log 2 := mul_pos hε hlog2
    have hquotient : 0 ≤ (C : ℝ) / (ε * Real.log 2) :=
      div_nonneg (by positivity) hdenom.le
    linarith
  have hloc (p : ℕ) (hp : p ∈ support) :
      ((n.1.factorization p + 1 : ℕ) : ℝ) ^ C ≤
        (if (p : ℝ) < B then A ^ C else 1) *
          ((p ^ n.1.factorization p : ℕ) : ℝ) ^ ε := by
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by
      change p ∈ n.1.factorization.support at hp
      simpa only [Nat.support_factorization] using hp)
    by_cases hpB : (p : ℝ) < B
    · have h := divisorPrimePower_small_bound C (n.1.factorization p) p hC ε hε
        hpprime
      simpa [A, B, hpB] using h
    · have hlarge : B ≤ (p : ℝ) := le_of_not_gt hpB
      have h := divisorPrimePower_large_bound C (n.1.factorization p) p hC ε hε
        hpprime (by simpa [B] using hlarge)
      simpa [A, B, hpB] using h
  have hprod :
      (∏ p ∈ support, ((n.1.factorization p + 1 : ℕ) : ℝ) ^ C) ≤
        (∏ p ∈ support, (if (p : ℝ) < B then A ^ C else 1)) *
          (∏ p ∈ support, ((p ^ n.1.factorization p : ℕ) : ℝ) ^ ε) := by
    calc
      _ ≤ ∏ p ∈ support,
          (if (p : ℝ) < B then A ^ C else 1) *
            ((p ^ n.1.factorization p : ℕ) : ℝ) ^ ε := by
        apply Finset.prod_le_prod₀
        · intro p hp
          positivity
        · intro p hp
          exact hloc p hp
      _ = _ := Finset.prod_mul_distrib
  have hsmall_subset : small ⊆ Finset.Icc 2 (Nat.floor B) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpsupp, hpB⟩
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by
      change p ∈ n.1.factorization.support at hpsupp
      simpa only [Nat.support_factorization] using hpsupp)
    refine Finset.mem_Icc.mpr ⟨hpprime.two_le, ?_⟩
    exact Nat.le_floor (le_of_lt hpB)
  have hsmallCard : small.card ≤ Nat.floor B := by
    calc
      small.card ≤ (Finset.Icc 2 (Nat.floor B)).card := Finset.card_le_card hsmall_subset
      _ = Nat.floor B + 1 - 2 := by rw [Nat.card_Icc]
      _ ≤ Nat.floor B := by omega
  have hconstProd :
      (∏ p ∈ support, (if (p : ℝ) < B then A ^ C else 1)) =
        (A ^ C) ^ small.card := by
    rw [Finset.prod_ite]
    simp [small]
  have hconstBound :
      (A ^ C) ^ small.card ≤ divisorSubpowerConstant C ε := by
    rw [show divisorSubpowerConstant C ε = A ^ (C * Nat.floor B) by
      simp [divisorSubpowerConstant, A, B, divisorSubpowerCutoff]]
    rw [← pow_mul]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hAone
    exact_mod_cast Nat.mul_le_mul_left C hsmallCard
  have hproductBound :
      (∏ p ∈ support, ((n.1.factorization p + 1 : ℕ) : ℝ) ^ C) ≤
        divisorSubpowerConstant C ε *
          (∏ p ∈ support, ((p ^ n.1.factorization p : ℕ) : ℝ) ^ ε) := by
    calc
      _ ≤ (A ^ C) ^ small.card *
          (∏ p ∈ support, ((p ^ n.1.factorization p : ℕ) : ℝ) ^ ε) := by
        simpa [hconstProd] using hprod
      _ ≤ _ := mul_le_mul_of_nonneg_right hconstBound (by positivity)
  calc
    (divisorFunction 2 n : ℝ) ^ C =
        ∏ p ∈ support, ((n.1.factorization p + 1 : ℕ) : ℝ) ^ C := by
          rw [divisorFunction_two_factorization_real]
          unfold Finsupp.prod
          simp [support, Finset.prod_pow]
    _ ≤ divisorSubpowerConstant C ε *
          (∏ p ∈ support, ((p ^ n.1.factorization p : ℕ) : ℝ) ^ ε) := hproductBound
    _ = divisorSubpowerConstant C ε * (n.1 : ℝ) ^ ε := by
      rw [natural_factorization_rpow]
      simp [support, Finsupp.prod]

/-- The local weak-composition estimate used for the `d_k` consequence. -/
private theorem divisorFunction_le_tau_pow {k : ℕ} (hk : 1 ≤ k)
    (n : PositiveInteger) : divisorFunction k n ≤ divisorFunction 2 n ^ k := by
  rw [divisorFunction_factorization k n, divisorFunction_pow_factorization 2 k n]
  unfold Finsupp.prod
  apply Finset.prod_le_prod
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using hp)
  have hleft := positiveDivisorFunction_prime_pow p (k - 1)
    (n.1.factorization p) hpprime
  have hright := positiveDivisorFunction_prime_pow p 1
    (n.1.factorization p) hpprime
  change divisorFunction k ⟨p ^ n.1.factorization p,
      Nat.pow_pos hpprime.pos⟩ ≤
    divisorFunction 2 ⟨p ^ n.1.factorization p,
      Nat.pow_pos hpprime.pos⟩ ^ k
  rw [Nat.sub_add_cancel hk] at hleft
  rw [hleft, hright]
  rw [Nat.choose_one_right]
  calc
    ((n.1.factorization p + (k - 1)).choose (k - 1)) ≤
        (n.1.factorization p + 1) ^ (k - 1) :=
      Nat.choose_add_le_add_one_pow _ _
    _ ≤ (n.1.factorization p + 1) ^ k :=
      pow_le_pow_right' (a := n.1.factorization p + 1) (by omega) (by omega)

/-- In particular the `k`-fold divisor function has the same explicit
subpower bound with the source's constant `D_{k,ε}`. -/
theorem divisorFunctionSubpower
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (n : PositiveInteger) :
    (divisorFunction k n : ℝ) ≤
      divisorSubpowerConstant k ε * (n.1 : ℝ) ^ ε := by
  have hcompare := divisorFunction_le_tau_pow hk n
  have hcompareReal : (divisorFunction k n : ℝ) ≤
      (divisorFunction 2 n : ℝ) ^ k := by
    exact_mod_cast hcompare
  exact hcompareReal.trans (divisorSubpowerExplicit hk hε n)


end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.divisorSubpowerExplicit
#print axioms FractionalPrimes.Literature.Twisted.divisorFunctionSubpower
