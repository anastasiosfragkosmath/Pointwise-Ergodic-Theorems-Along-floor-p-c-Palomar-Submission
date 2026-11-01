module

public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace FractionalPrimes.Literature.Reciprocal

/-- The positive-integer prefix sum, written with a zero coefficient at zero
so it matches Mathlib's Abel summation convention. -/
def twistedMufPrefix (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 (Nat.floor x), (if n = 0 then 0 else a n)

def inverseSqrtWeight (x : ℝ) : ℂ :=
  ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ)

/-- Exact half-open interval summation by parts with the weight `n⁻¹ᐟ²`, in
the real-endpoint convention used in the proof of `lrc:muf`. -/
theorem twistedMufAbelSummation (a : ℕ → ℂ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
        a n * inverseSqrtWeight (n : ℝ)) =
      inverseSqrtWeight v * twistedMufPrefix a v -
        inverseSqrtWeight u * twistedMufPrefix a u -
        ∫ z in Set.Ioc u v,
          deriv inverseSqrtWeight z * twistedMufPrefix a z := by
  let c : ℕ → ℂ := fun n => if n = 0 then 0 else a n
  let f : ℝ → ℂ := inverseSqrtWeight
  have hderiv (t : ℝ) (ht : t ≠ 0) :
      HasDerivAt f (((-1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) : ℝ) : ℂ) t := by
    dsimp [f, inverseSqrtWeight]
    convert (Real.hasDerivAt_rpow_const (p := (-1 / 2 : ℝ)) (Or.inl ht)).ofReal_comp
      using 1
    congr 1
    rw [show (-1 / 2 : ℝ) - 1 = -3 / 2 by ring]
  have hf_diff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ f t := by
    intro t ht
    exact (hderiv t (ne_of_gt (lt_of_lt_of_le hu ht.1))).differentiableAt
  have hpow_cont : ContinuousOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Set.Icc u v) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro t ht
    exact Or.inl (ne_of_gt (lt_of_lt_of_le hu ht.1))
  have hderiv_cont :
      ContinuousOn (fun t : ℝ => (((-1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) : ℝ) : ℂ))
        (Set.Icc u v) := by
    fun_prop (disch := linarith)
  have hf_int : IntegrableOn (deriv f) (Set.Icc u v) := by
    have hcont : ContinuousOn (deriv f) (Set.Icc u v) := by
      apply hderiv_cont.congr
      intro t ht
      exact (hderiv t (ne_of_gt (lt_of_lt_of_le hu ht.1))).deriv
    exact hcont.integrableOn_compact isCompact_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c hu.le huv hf_diff hf_int
  have hprefix (x : ℝ) : (∑ n ∈ Finset.Icc 0 (Nat.floor x), c n) =
      twistedMufPrefix a x := by
    rfl
  have hsum :
      (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
          a n * inverseSqrtWeight (n : ℝ)) =
        ∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v), f (n : ℝ) * c n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have hmem := Finset.mem_Ioc.mp hn
      omega
    simp [f, inverseSqrtWeight, c, hn0, mul_comm]
  rw [hsum, habel]
  simp only [hprefix, f]

end FractionalPrimes.Literature.Reciprocal

