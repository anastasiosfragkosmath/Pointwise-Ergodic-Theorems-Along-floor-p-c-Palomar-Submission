module
public import FractionalPrimes.Literature.Twisted.SmoothSmallGroupAbelTransfer
public import FractionalPrimes.Literature.Twisted.ShiftedConvolutionFactorExtraction
public import FractionalPrimes.Literature.Twisted.ConditionalMobiusResidueFromMUF
public import Mathlib.Tactic
@[expose] public section

/-!
# Real-endpoint bridge for finite small-group prefixes

This module identifies the finite Abel prefix with the exact real half-open
interval used by the periodic-factor and Möbius residue estimates. A Möbius
cutoff is represented by clipping the right endpoint at its real cutoff.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

/-- The finite Abel prefix is exactly the natural half-open interval (a,n]. -/
theorem smoothSmallGroupPrefix_eq_sum_Ioc
    (a n : ℕ) (f : ℕ → ℂ) :
    smoothSmallGroupPrefix a f n =
      ∑ m ∈ Finset.Ioc a n, f m := by
  classical
  unfold smoothSmallGroupPrefix
  rw [← Finset.sum_filter]
  have hset :
      (Finset.range (n + 1)).filter (fun m => a < m) =
        Finset.Ioc a n := by
    ext m
    simp [Finset.mem_Ioc]
    omega
  rw [hset]

/-- Intersecting a natural interval (a,n] with the real Möbius cutoff
m ≤ z is exactly the real half-open interval (a,min(n,z)], with the
source floor endpoints retained. -/
theorem smoothSmallGroupPrefix_cutoff_eq_realInterval
    (a n : ℕ) {z : ℝ} (hz : 0 ≤ z) (f : ℕ → ℂ) :
    smoothSmallGroupPrefix a
        (fun m => if (m : ℝ) ≤ z then f m else 0) n =
      ∑ m ∈ factorExtractionRealInterval (a : ℝ) (min (n : ℝ) z), f m := by
  classical
  have hset :
      Finset.filter (fun m : ℕ => (m : ℝ) ≤ z) (Finset.Ioc a n) =
        factorExtractionRealInterval (a : ℝ) (min (n : ℝ) z) := by
    apply Finset.ext
    intro m
    change (m ∈ Finset.filter (fun k : ℕ => (k : ℝ) ≤ z)
        (Finset.Ioc a n)) ↔
      m ∈ factorExtractionRealInterval (a : ℝ) (min (n : ℝ) z)
    rw [Finset.mem_filter, Finset.mem_Ioc,
      mem_factorExtractionRealInterval (by positivity)
        (le_min (by positivity) hz)]
    constructor
    · rintro ⟨⟨ham, hmn⟩, hmz⟩
      refine ⟨?_, le_min ?_ hmz⟩
      · exact_mod_cast ham
      · exact_mod_cast hmn
    · rintro ⟨ham, hmmin⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact_mod_cast ham
      · exact_mod_cast (le_trans hmmin (min_le_left _ _))
      · exact le_trans hmmin (min_le_right _ _)
  calc
    smoothSmallGroupPrefix a
        (fun m => if (m : ℝ) ≤ z then f m else 0) n =
      ∑ m ∈ Finset.Ioc a n, if (m : ℝ) ≤ z then f m else 0 := by
        rw [smoothSmallGroupPrefix_eq_sum_Ioc]
    _ = ∑ m ∈ Finset.filter (fun m : ℕ => (m : ℝ) ≤ z)
        (Finset.Ioc a n), f m := by
      rw [← Finset.sum_filter]
    _ = ∑ m ∈ factorExtractionRealInterval (a : ℝ) (min (n : ℝ) z), f m := by
      rw [hset]

/-- Specialization of the exact Möbius residue interval estimate to every
finite Abel prefix. The interval estimate has the same form as the
mobiusResidueFromFactorGoal conclusion: the cutoff is handled by clipping
the real right endpoint before applying it. -/
theorem smoothSmallGroupMobiusResiduePrefix_bound
    {a n : ℕ} {z M Cμ : ℝ} {q b : ℕ} {t : ℝ}
    (hz : 0 ≤ z) (hCμ : 0 ≤ Cμ)
    (haM : M ≤ (a : ℝ)) (hnM : (n : ℝ) ≤ 2 * M)
    (hResidueInterval : ∀ {u v : ℝ}, M ≤ u → u ≤ v → v ≤ 2 * M →
      ‖∑ m ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
          if m % q = b then mobiusMellinResidueTerm t m else 0‖ ≤ Cμ) :
    ‖smoothSmallGroupPrefix a
      (fun m => if (m : ℝ) ≤ z then
        if m % q = b then mobiusMellinResidueTerm t m else 0 else 0) n‖ ≤ Cμ := by
  have hprefix := smoothSmallGroupPrefix_cutoff_eq_realInterval a n hz
    (fun m => if m % q = b then mobiusMellinResidueTerm t m else 0)
  let v : ℝ := min (n : ℝ) z
  have hvnonneg : 0 ≤ v := by
    dsimp [v]
    exact le_min (Nat.cast_nonneg _) hz
  have hvUpper : v ≤ 2 * M := by
    dsimp [v]
    exact le_trans (min_le_left _ _) hnM
  by_cases hav : (a : ℝ) ≤ v
  · have hbound := hResidueInterval (u := (a : ℝ)) (v := v) haM hav hvUpper
    rw [hprefix]
    simpa [factorExtractionRealInterval, v, mobiusMellinResidueTerm] using hbound
  · have hzero :
        factorExtractionRealInterval (a : ℝ) v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      rw [mem_factorExtractionRealInterval (by positivity) hvnonneg] at hm
      have haCast : (a : ℝ) ≤ (m : ℝ) := le_of_lt hm.1
      exact hav (haCast.trans hm.2)
    rw [hprefix, hzero]
    simp
    exact hCμ

end FractionalPrimes.Literature.Twisted

#print axioms FractionalPrimes.Literature.Twisted.smoothSmallGroupPrefix_eq_sum_Ioc
#print axioms FractionalPrimes.Literature.Twisted.smoothSmallGroupPrefix_cutoff_eq_realInterval
#print axioms FractionalPrimes.Literature.Twisted.smoothSmallGroupMobiusResiduePrefix_bound

