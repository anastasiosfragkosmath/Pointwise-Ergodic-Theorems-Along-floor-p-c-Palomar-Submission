module
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic
@[expose] public section
namespace FractionalPrimes.Literature.DirichletMean

/-- Every permitted residue has the exact gcd/quotient/reduced-residue
representation used by the nonunit character identity, including residue zero. -/
theorem selectedPTWResidueReduction
    (q b : ℕ) (hq : 0 < q) :
    ∃ d Q r : ℕ, 0 < d ∧ 0 < Q ∧ d * Q = q ∧ d * r = b ∧
      d ≤ q ∧ Nat.Coprime r Q ∧ IsCoprime (r : ℤ) (Q : ℤ) := by
  let d := Nat.gcd b q
  have hd : 0 < d := Nat.gcd_pos_of_pos_right b hq
  have hdq : d ∣ q := Nat.gcd_dvd_right b q
  have hdb : d ∣ b := Nat.gcd_dvd_left b q
  have hQ : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd
  have hcop : Nat.Coprime (b / d) (q / d) := Nat.coprime_div_gcd_div_gcd hd
  exact ⟨d, q / d, b / d, hd, hQ, Nat.mul_div_cancel' hdq,
    Nat.mul_div_cancel' hdb, Nat.le_of_dvd hq hdq, hcop, hcop.isCoprime⟩

#print axioms selectedPTWResidueReduction
end FractionalPrimes.Literature.DirichletMean
end
