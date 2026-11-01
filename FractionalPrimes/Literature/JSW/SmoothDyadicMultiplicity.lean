module

public import FractionalPrimes.Literature.JSW.Conventions
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Semiring

/-! The exact finite scale multiplicity in the source smooth square estimate. -/
@[expose] public section
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem jswM_finite_fiber_card_le
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) (m : ℤ) :
    (K.filter (fun k => jswM a ha k = m)).card ≤ jswMultiplicity a ha := by
  classical
  let S := K.filter (fun k => jswM a ha k = m)
  by_cases hs : S.Nonempty
  · let k₀ := S.min' hs
    have hk₀ : k₀ ∈ S := Finset.min'_mem S hs
    have hbase : Int.floor (a*(k₀ : ℝ)) = m := (Finset.mem_filter.mp hk₀).2
    let N := Nat.ceil (1/a)
    have hN : 1/a ≤ (N : ℝ) := Nat.le_ceil _
    have hsub : S ⊆ Finset.Icc k₀ (k₀+(N : ℤ)) := by
      intro k hk
      have hmin : k₀ ≤ k := Finset.min'_le S k hk
      have hkfloor : Int.floor (a*(k : ℝ)) = m := (Finset.mem_filter.mp hk).2
      have hlo := Int.floor_le (a*(k₀ : ℝ))
      have hhi := Int.lt_floor_add_one (a*(k : ℝ))
      rw [hbase] at hlo
      rw [hkfloor] at hhi
      have hdiff : (k : ℝ)-(k₀ : ℝ) < 1/a := by
        apply (lt_div_iff₀ ha).2
        nlinarith
      have hreal : (k : ℝ) ≤ (k₀ : ℝ)+(N : ℝ) := by linarith
      have hle : k ≤ k₀+(N : ℤ) := by exact_mod_cast hreal
      exact Finset.mem_Icc.mpr ⟨hmin, hle⟩
    have hcard : (Finset.Icc k₀ (k₀+(N : ℤ))).card = N+1 := by
      rw [Int.card_Icc]
      omega
    calc
      _ = S.card := rfl
      _ ≤ (Finset.Icc k₀ (k₀+(N : ℤ))).card := Finset.card_le_card hsub
      _ = _ := hcard
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ _
    simp [hzero]

#print axioms jswM_finite_fiber_card_le
end
end FractionalPrimes.Literature.JSW
end
