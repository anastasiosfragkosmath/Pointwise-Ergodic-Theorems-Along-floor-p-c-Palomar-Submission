module

public import FractionalPrimes.ArithmeticBasicsCore
public import FractionalPrimes.Chebyshev
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.ModEq

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open scoped BigOperators

/-- The finite parameter set for the residue-prefix maximum.  Its entries
are `(q,a,m)` encoded as `((q,a),m)`, with `1 ≤ q ≤ Q`, `0 ≤ a < q`, and
`0 ≤ m ≤ H`.  The real cutoff `Q` is represented exactly by `Nat.floor Q`. -/
noncomputable def residuePrefixParameters (H : ℕ) (Q : ℝ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (((Finset.Icc 1 (Nat.floor Q)).product (Finset.range (Nat.floor Q))).product
      (Finset.Icc 0 H)).filter (fun t => t.1.2 < t.1.1)

/-- The finite residue-class prefix sum on the exact interval
`(X, X + m]`. -/
noncomputable def residuePrefixSum (X m q a : ℕ) (w : ℤ → ℂ) : ℂ :=
  ∑ n ∈ (realIntegerInterval (X : ℝ) (m : ℝ)).filter
      (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]),
    w n

/-- The finite maximum of all residue-class prefix sums with integer
`1 ≤ q ≤ Q`, `0 ≤ a < q`, and `0 ≤ m ≤ H`.  The inserted zero is the
`m = 0` value; for `Q ≥ 1` it is also attained among the displayed indices. -/
noncomputable def residuePrefixEnvelope
    (X H : ℕ) (w : ℤ → ℂ) (Q : ℝ) : ℝ :=
  let values := (residuePrefixParameters H Q).image fun t =>
    ‖residuePrefixSum X t.2 t.1.1 t.1.2 w‖
  (insert 0 values).max' (by simp)

theorem residuePrefixSum_zero (X q a : ℕ) (w : ℤ → ℂ) :
    residuePrefixSum X 0 q a w = 0 := by
  simp [residuePrefixSum, realIntegerInterval]

theorem residuePrefixParameters_one_zero
    (H : ℕ) (Q : ℝ) (hQ : 1 ≤ Q) :
    ((1, 0), 0) ∈ residuePrefixParameters H Q := by
  have hQreal : (1 : ℝ) ≤ Q := hQ
  have hfloor : 1 ≤ Nat.floor Q := by
    have hf := Nat.lt_floor_add_one Q
    by_contra hn
    have hzero : Nat.floor Q = 0 := by omega
    have hf' : Q < 1 := by simpa [hzero] using hf
    exact (not_lt_of_ge hQreal) hf'
  have hfloorpos : 0 < Nat.floor Q := by omega
  simp [residuePrefixParameters, hfloor, hfloorpos]

theorem residuePrefixParameters_mem_iff
    (H : ℕ) (Q : ℝ) (q a m : ℕ) :
    ((q, a), m) ∈ residuePrefixParameters H Q ↔
      1 ≤ q ∧ q ≤ Nat.floor Q ∧ a < q ∧ m ≤ H := by
  simp [residuePrefixParameters, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_range]
  omega

theorem nat_le_real_iff_le_natFloor
    (Q : ℝ) (q : ℕ) (hQ : 0 ≤ Q) :
    (q : ℝ) ≤ Q ↔ q ≤ Nat.floor Q := by
  constructor
  · exact Nat.le_floor
  · intro hq
    exact (Nat.cast_le.mpr hq).trans (Nat.floor_le hQ)

/-- For `Q ≥ 1`, the maximum is taken over a nonempty finite set of actual
residue-prefix values; its value is attained by some allowed `(q,a,m)`. -/
theorem residuePrefixEnvelope_attained
    (X H : ℕ) (w : ℤ → ℂ) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ q a m : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ a < q ∧ m ≤ H ∧
      residuePrefixEnvelope X H w Q =
        ‖residuePrefixSum X m q a w‖ := by
  classical
  let P := residuePrefixParameters H Q
  let values := P.image fun t =>
    ‖residuePrefixSum X t.2 t.1.1 t.1.2 w‖
  have hP : P.Nonempty := ⟨((1, 0), 0), by
    exact residuePrefixParameters_one_zero H Q hQ⟩
  have hvalues : values.Nonempty := by
    obtain ⟨t, ht⟩ := hP
    exact ⟨‖residuePrefixSum X t.2 t.1.1 t.1.2 w‖,
      Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
  have hzero : 0 ∈ values := by
    apply Finset.mem_image.mpr
    refine ⟨((1, 0), 0), residuePrefixParameters_one_zero H Q hQ, ?_⟩
    simp [residuePrefixSum_zero]
  have hmax : (values.max' hvalues) ∈ values := Finset.max'_mem _ _
  have heq : residuePrefixEnvelope X H w Q = values.max' hvalues := by
    change (insert 0 values).max' _ = values.max' hvalues
    rw [Finset.max'_insert]
    exact max_eq_right (Finset.le_max' values 0 hzero)
  have hmaxImage : ∃ t ∈ P,
      ‖residuePrefixSum X t.2 t.1.1 t.1.2 w‖ = values.max' hvalues := by
    simpa only [values, Finset.mem_image] using hmax
  obtain ⟨t, hmem, hval⟩ := hmaxImage
  have hparams : 1 ≤ t.1.1 ∧ t.1.1 ≤ Nat.floor Q ∧
      t.1.2 < t.1.1 ∧ t.2 ≤ H := by
    exact (residuePrefixParameters_mem_iff H Q t.1.1 t.1.2 t.2).mp hmem
  refine ⟨t.1.1, t.1.2, t.2, hparams.1, ?_, hparams.2.2.1,
    hparams.2.2.2, ?_⟩
  · exact (nat_le_real_iff_le_natFloor Q t.1.1 (by linarith)).2 hparams.2.1
  · calc
      residuePrefixEnvelope X H w Q = values.max' hvalues := heq
      _ = ‖residuePrefixSum X t.2 t.1.1 t.1.2 w‖ := hval.symm

/-- Scalar arithmetic contract for the residue-prefix major-arc input.
The Cramér model uses the location cutoff `paperShortBlockCramerWeight X`;
the Möbius function is cast from its integer-valued definition. -/
def polynomialMajorArcTask : Prop :=
  ∀ A B η : ℝ, 0 < A → 0 < B → 0 < η → η < 3 / 16 →
    ∃ C : ℝ, 0 < C ∧ ∀ X H : ℕ, 3 ≤ X →
      (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
      (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
      residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
          ((Real.log (X : ℝ)) ^ B) +
        residuePrefixEnvelope X H
          (fun n => (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
          ((Real.log (X : ℝ)) ^ B) ≤
        C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A)

#print axioms residuePrefixEnvelope
#print axioms polynomialMajorArcTask
#print axioms residuePrefixEnvelope_attained

end FractionalPrimes.Literature.Polynomial

end
