module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownFreeFactorLocalAbel
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorProfileResidueAssembly
public import FractionalPrimes.Literature.DirichletAdapter.LongFactorResidueReduction
import Mathlib.Tactic

/-! The checked periodic theta/log interval estimates, applied to the actual
smooth free-factor Mellin sample produced by the Heath--Brown profile. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Polynomial

/-- The finite loss in the theta and normalized logarithmic free-factor
branches.  The Möbius branch is excluded by the hypothesis of the theorem
below and remains handled by its separate scalar estimate. -/
def smoothHeathBrownFreeFactorIntervalCost
    {X : ℝ} : SmoothHeathBrownFactor X → ℝ
  | .theta _ => 5
  | .logarithm _ => 6
  | .mobius _ => 0

/-- The periodic theta/log Abel estimates for the literal smooth
Heath--Brown free-factor sample.  The interval is arbitrary inside `[L,2L]`;
the residue is selected by the actual periodic indicator and the Mellin
power is the exact source exponent. -/
theorem smoothHeathBrownFreeFactor_periodicInterval_bound
    {alpha A X L T0 t x y : ℝ} {q : ℕ} {r : ℤ}
    (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X) (m : ℕ)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hxL : L ≤ x) (hxy : x ≤ y) (hy2 : y ≤ 2 * L) :
    ‖∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
      smoothHeathBrownResidueIndicator q r (n : ℤ) *
        smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ ≤
      smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A * Real.sqrt L *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  have htwist : smoothDyadicTwistExponent t =
      (-(1 / 2 : ℂ)) - Complex.I * (t : ℂ) := by
    dsimp [smoothDyadicTwistExponent]
    ring
  have hsumTheta {j : SmoothHeathBrownScaleIndex X} :
      ‖∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
        smoothHeathBrownResidueIndicator q r (n : ℤ) *
          smoothHeathBrownFreeFactorDiscreteTerm (.theta j) m t n‖ =
      ‖∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
        smoothHeathBrownResidueMellinTerm q r t n *
          (((smoothDyadicTheta ((n : ℝ) /
              smoothHeathBrownFactorScale (.theta j)) *
            polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) : ℝ) : ℂ))‖ := by
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    have hxnonneg : 0 ≤ x := le_trans (le_of_lt
      (lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith [hX]) _) hLlower)) hxL
    have hnpos : 0 < n := by
      have hfloor : 0 ≤ Nat.floor x := Nat.zero_le _
      exact Nat.lt_of_le_of_lt hfloor (Finset.mem_Ioc.mp hn).1
    simp [smoothHeathBrownFreeFactorDiscreteTerm,
      smoothHeathBrownFreeFactorCoefficient, smoothHeathBrownThetaFactor,
      smoothHeathBrownResidueMellinTerm, smoothHeathBrownFactorScale,
      htwist, hnpos.ne']
    ring
  have hsumLog {j : SmoothHeathBrownScaleIndex X} :
      ‖∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
        smoothHeathBrownResidueIndicator q r (n : ℤ) *
          smoothHeathBrownFreeFactorDiscreteTerm (.logarithm j) m t n‖ =
      ‖∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
        smoothHeathBrownResidueMellinTerm q r t n *
          smoothHeathBrownThetaLogOuterWeight
            (smoothHeathBrownFactorScale (.logarithm j)) X m n‖ := by
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    have hxnonneg : 0 ≤ x := le_trans (le_of_lt
      (lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith [hX]) _) hLlower)) hxL
    have hnpos : 0 < n := by
      have hfloor : 0 ≤ Nat.floor x := Nat.zero_le _
      exact Nat.lt_of_le_of_lt hfloor (Finset.mem_Ioc.mp hn).1
    simp [smoothHeathBrownFreeFactorDiscreteTerm,
      smoothHeathBrownFreeFactorCoefficient, smoothHeathBrownLogFactor,
      smoothHeathBrownResidueMellinTerm, smoothHeathBrownFactorScale,
      smoothHeathBrownThetaLogOuterWeight, ArithmeticFunction.log_apply,
      htwist, hnpos.ne']
    ring
  cases f with
  | theta j =>
      have hbound := smoothHeathBrownThetaFactor_periodic_interval
          (alpha := alpha) (A := A) (X := X) (L := L) (T0 := T0)
          (t := t) (S := smoothHeathBrownFactorScale (.theta j))
          (x := x) (y := y) (q := q) (r := r) m
          halpha halpha1 hA hX hLlower hLupper hq hqBound hT0 hT0t
          htX hxL hxy hy2 (by
            have hscale : 1 ≤ smoothHeathBrownFactorScale (.theta j) :=
              smoothHeathBrownFactorScale_ge_one _
            linarith)
      rw [hsumTheta]
      simpa [smoothHeathBrownFreeFactorIntervalCost] using hbound
  | logarithm j =>
      have hbound := smoothHeathBrownLogFactor_periodic_interval
          (alpha := alpha) (A := A) (X := X) (L := L) (T0 := T0)
          (t := t) (S := smoothHeathBrownFactorScale (.logarithm j))
          (x := x) (y := y) (q := q) (r := r) m
          halpha halpha1 hA hX hLlower hLupper hq hqBound hT0 hT0t
          htX hxL hxy hy2 (by
            have hscale : 1 ≤ smoothHeathBrownFactorScale (.logarithm j) :=
              smoothHeathBrownFactorScale_ge_one _
            linarith)
      rw [hsumLog]
      simpa [smoothHeathBrownFreeFactorIntervalCost] using hbound
  | mobius j => exact (hfree j rfl).elim

/-- The free-factor interval bound after fixing the product of the other
factors.  A solvable congruence `m*n ≡ a (mod q)` is reduced to its exact
single residue class modulo `q/gcd(m,q)` before applying the periodic
theta/log estimate. -/
theorem smoothHeathBrownFreeFactor_productResidueInterval_bound
    {alpha A X L T0 t x y : ℝ} {q : ℕ} {a m n₀ : ℕ}
    (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hxL : L ≤ x) (hxy : x ≤ y) (hy2 : y ≤ 2 * L)
    (hsolution : m * n₀ ≡ a [MOD q]) :
    ‖∑ n ∈ (Finset.Ioc (Nat.floor x) (Nat.floor y)).filter
        (fun n => m * n ≡ a [MOD q]),
      smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ ≤
      smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A * Real.sqrt L *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  classical
  let q' : ℕ := q / Nat.gcd m q
  have hq'pos : 0 < q' := by
    dsimp [q']
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq (Nat.gcd_dvd_right m q)
    · exact Nat.gcd_pos_of_pos_right m hq
  have hq'le : q' ≤ q := by
    dsimp [q']
    exact mul_congruence_reduced_modulus_le m q
  have hq'bound : (q' : ℝ) ≤ X ^ (alpha / 2) := by
    calc
      (q' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'le
      _ ≤ X ^ (alpha / 2) := hqBound
  have hsum :
      (∑ n ∈ (Finset.Ioc (Nat.floor x) (Nat.floor y)).filter
          (fun n => m * n ≡ a [MOD q]),
        smoothHeathBrownFreeFactorDiscreteTerm f m t n) =
      ∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
        smoothHeathBrownResidueIndicator q' (n₀ : ℤ) (n : ℤ) *
          smoothHeathBrownFreeFactorDiscreteTerm f m t n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hres : m * n ≡ a [MOD q]
    · have hred := (mul_congruence_iff_reduced_residue m q a n₀ hq
        hsolution n).mp hres
      have hmod : (n : ℤ) ≡ (n₀ : ℤ) [ZMOD (q' : ℤ)] := by
        simpa [q'] using (Int.natCast_modEq_iff).2 hred
      change (n : ℤ) % (q' : ℤ) = (n₀ : ℤ) % (q' : ℤ) at hmod
      simp [smoothHeathBrownResidueIndicator, hmod, hres]
    · have hred : ¬ n ≡ n₀ [MOD q'] := by
        intro hh
        exact hres ((mul_congruence_iff_reduced_residue m q a n₀ hq
          hsolution n).mpr hh)
      have hmod : ¬ (n : ℤ) ≡ (n₀ : ℤ) [ZMOD (q' : ℤ)] := by
        intro hh
        exact hred ((Int.natCast_modEq_iff).mp (by simpa [q'] using hh))
      change (n : ℤ) % (q' : ℤ) ≠ (n₀ : ℤ) % (q' : ℤ) at hmod
      simp [smoothHeathBrownResidueIndicator, hmod, hres]
  have hbound := smoothHeathBrownFreeFactor_periodicInterval_bound
    (alpha := alpha) (A := A) (X := X) (L := L) (T0 := T0)
    (t := t) (x := x) (y := y) (q := q') (r := (n₀ : ℤ))
    hX f m hfree halpha halpha1 hA hLlower hLupper hq'pos hq'bound
    hT0 hT0t htX hxL hxy hy2
  rw [hsum]
  exact hbound

#print axioms smoothHeathBrownFreeFactor_periodicInterval_bound
#print axioms smoothHeathBrownFreeFactor_productResidueInterval_bound

end FractionalPrimes.Literature.DirichletAdapter

end
