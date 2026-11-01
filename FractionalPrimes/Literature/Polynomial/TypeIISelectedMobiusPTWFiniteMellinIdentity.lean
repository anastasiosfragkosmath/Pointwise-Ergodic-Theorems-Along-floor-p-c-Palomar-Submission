module

public import FractionalPrimes.Literature.Twisted.FullFrequencyMellinData
public import FractionalPrimes.Literature.Twisted.NonunitTripleFiniteMellin
public import Mathlib.Tactic

/-! Finite Mellin source identity for a residue-filtered product of three
coefficient sequences. The remaining source-specific task is to instantiate
these coefficient and support hypotheses by the selected Möbius groups. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The real-log convention used by the full-frequency polynomial agrees with
the complex natural power at the exact exponent `-1/2-it`. -/
theorem mellinDirichletMonomial_eq_natCast_cpow
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    mellinDirichletMonomial n t =
      (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
    rw [hcast]
    exact (Complex.ofReal_log hnR.le).symm
  unfold mellinDirichletMonomial
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  congr 1
  push_cast
  ring

/-- The coefficient twist `n^(iT)` shifts the real frequency exactly from
`t` to `t-T` in the full-frequency Mellin convention. -/
theorem mellinDirichletMonomial_twist_eq_natCast_cpow
    {n : ℕ} (hn : 0 < n) (t T : ℝ) :
    (n : ℂ) ^ (Complex.I * (T : ℂ)) * mellinDirichletMonomial n t =
      (n : ℂ) ^
        (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [mellinDirichletMonomial_eq_natCast_cpow hn t]
  calc
    _ = (n : ℂ) ^
        (Complex.I * (T : ℂ) +
          ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))) :=
      (Complex.cpow_add _ _ hnC).symm
    _ = _ := by
      congr 1
      push_cast
      ring

set_option maxHeartbeats 1500000 in
/-- The full-frequency polynomial of a residue-filtered, vertically twisted
three-factor convolution is exactly its finite nonunit character/allocation
expansion. The support and cutoff premises are explicit finite bookkeeping
inputs; no analytic estimate is assumed. -/
theorem fullFrequencyMellinPolynomial_eq_nonunitTripleCharacterAllocation
    (d : FullFrequencyMellinData)
    (a₁ a₂ a₃ : ArithmeticFunction ℂ)
    {N₁ N₂ N₃ q : ℕ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN₃ : 0 < N₃)
    (hsupp₁ : ∀ n, a₁ n ≠ 0 → n ≤ N₁)
    (hsupp₂ : ∀ n, a₂ n ≠ 0 → n ≤ N₂)
    (hsupp₃ : ∀ n, a₃ n ≠ 0 → n ≤ N₃)
    (hq : 0 < q) (residue : ℤ) (T t : ℝ)
    (hcoeff : ∀ n ∈ fullFrequencySupportIndices d.X,
      d.a n =
        if (n : ZMod q) = (residue : ZMod q) then
          (a₁ * a₂ * a₃) n *
            (n : ℂ) ^ (Complex.I * (T : ℂ))
        else 0)
    (hsourceSupport : ∀ n, (a₁ * a₂ * a₃) n ≠ 0 →
      n ∈ fullFrequencySupportIndices d.X)
    (hcutoff : ∀ n ∈ fullFrequencySupportIndices d.X,
      n ≤ N₁ * N₂ * N₃) :
    fullFrequencyMellinPolynomial d t =
      ((Nat.gcd residue.natAbs q : ℂ) ^
          (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) /
        ((q / Nat.gcd residue.natAbs q).totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 (Nat.gcd residue.natAbs q),
          ∑ χ : BlueprintCharacter (q / Nat.gcd residue.natAbs q),
            star (evalInt χ
                (residue / (Nat.gcd residue.natAbs q : ℤ))) *
              finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
                (q / orderedAllocationPrefix r.1 0)
                (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
                (q / orderedAllocationPrefix r.1 1)
                (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
                (q / orderedAllocationPrefix r.1 2)
                (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  classical
  let S := fullFrequencySupportIndices d.X
  let P := N₁ * N₂ * N₃
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)
  let sourceTerm : ℕ → ℂ := fun n =>
    if (n : ZMod q) = (residue : ZMod q) then
      (a₁ * a₂ * a₃) n * (n : ℂ) ^ (-s) else 0
  have hsubset : S ⊆ Finset.Icc 1 P := by
    intro n hn
    refine Finset.mem_Icc.mpr ⟨?_, hcutoff n hn⟩
    have hnmem : n ∈ fullFrequencySupportIndices d.X := hn
    unfold fullFrequencySupportIndices mellinIntervalIndices at hnmem
    have hnmem := Finset.mem_filter.mp hnmem
    exact (Finset.mem_Icc.mp hnmem.1).1
  have hpoint : ∀ n ∈ S,
      d.a n * mellinDirichletMonomial n t = sourceTerm n := by
    intro n hn
    have hnpos : 0 < n := by
      have hnmem : n ∈ fullFrequencySupportIndices d.X := hn
      unfold fullFrequencySupportIndices mellinIntervalIndices at hnmem
      have hnmem := Finset.mem_filter.mp hnmem
      exact (Finset.mem_Icc.mp hnmem.1).1
    rw [hcoeff n hn]
    by_cases hres : (n : ZMod q) = (residue : ZMod q)
    · simp only [sourceTerm, if_pos hres]
      rw [mul_assoc,
        mellinDirichletMonomial_twist_eq_natCast_cpow hnpos t T]
    · simp only [sourceTerm, if_neg hres, zero_mul]
  have hzero : ∀ n ∈ Finset.Icc 1 P, n ∉ S → sourceTerm n = 0 := by
    intro n hn hnS
    by_cases hres : (n : ZMod q) = (residue : ZMod q)
    · have hcoeffzero : (a₁ * a₂ * a₃) n = 0 := by
        by_contra hne
        exact hnS (hsourceSupport n hne)
      simp only [sourceTerm, if_pos hres, hcoeffzero, zero_mul]
    · simp only [sourceTerm, if_neg hres]
  have hsumSupport :
      (∑ n ∈ S, d.a n * mellinDirichletMonomial n t) =
        ∑ n ∈ Finset.Icc 1 P, sourceTerm n := by
    calc
      (∑ n ∈ S, d.a n * mellinDirichletMonomial n t) =
          ∑ n ∈ S, sourceTerm n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hpoint n hn
      _ = ∑ n ∈ Finset.Icc 1 P, sourceTerm n :=
        Finset.sum_subset hsubset hzero
  have hsource := nonunitTripleCharacterFactorizationFinite
    a₁ a₂ a₃ hN₁ hN₂ hN₃ hsupp₁ hsupp₂ hsupp₃ hq residue s
  rw [show fullFrequencyMellinPolynomial d t =
      ∑ n ∈ S, d.a n * mellinDirichletMonomial n t by rfl,
    hsumSupport]
  simpa [P, s, sourceTerm] using hsource

#print axioms mellinDirichletMonomial_eq_natCast_cpow
#print axioms mellinDirichletMonomial_twist_eq_natCast_cpow
#print axioms fullFrequencyMellinPolynomial_eq_nonunitTripleCharacterAllocation

end FractionalPrimes.Literature.DirichletMean

end
