module

public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import FractionalPrimes.Literature.MSZ.AdmissibleData

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped BigOperators

noncomputable section

/-! The summability assumption in `lm:data` implies the exact source
coefficient `sigma_q`; this adapter also bounds every finite level/shift
rectangle by that coefficient. -/

/-- The nonnegative `(l,j)` summand defining `sigma_q` in `lm:data`. -/
def mszSigmaQTerm (A : AdmissibleData) (z : ℕ × ℤ) : ℝ :=
  (2 : ℝ) ^ (-(((A.q - 1) / 2) * (z.1 : ℝ))) *
    (A.a z.2 z.1) ^ (A.q - 1)

/-- The source coefficient `sigma_q = ∑_l ∑_j 2^(-(q-1)l/2) a_{j,l}^{q-1}`. -/
def mszSigmaQ (A : AdmissibleData) : ℝ :=
  ∑' z : ℕ × ℤ, mszSigmaQTerm A z

theorem mszSigmaQTerm_nonneg (A : AdmissibleData) (z : ℕ × ℤ) :
    0 ≤ mszSigmaQTerm A z := by
  dsimp [mszSigmaQTerm]
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    (Real.rpow_nonneg (A.a_nonneg z.2 z.1) _)

/-- The data summability clause with the source choices
`epsilon=(q-1)/2` and `rho=q-1`. -/
theorem mszSigmaQTerm_summable (A : AdmissibleData) :
    Summable (mszSigmaQTerm A) := by
  have hepsPos : 0 < (A.q - 1) / 2 := by
    linarith [A.q_gt_one]
  have hepsLt : (A.q - 1) / 2 < A.q - 1 := by
    linarith [A.q_gt_one]
  change Summable (fun z : ℕ × ℤ =>
    (2 : ℝ) ^ (-(((A.q - 1) / 2) * (z.1 : ℝ))) *
      (A.a z.2 z.1) ^ (A.q - 1))
  exact A.a_summability ((A.q - 1) / 2) (A.q - 1) hepsPos hepsLt

/-- Summability of the shift coefficients at one fixed level. -/
theorem mszSigmaQLevel_summable (A : AdmissibleData) (l : ℕ) :
    Summable (fun j : ℤ => mszSigmaQTerm A (l, j)) := by
  exact (mszSigmaQTerm_summable A).comp_injective fun j₁ j₂ h =>
    congrArg Prod.snd h

/-- The full shift sum at level `l`. -/
def mszSigmaQLevel (A : AdmissibleData) (l : ℕ) : ℝ :=
  ∑' j : ℤ, mszSigmaQTerm A (l, j)

theorem mszSigmaQLevel_nonneg (A : AdmissibleData) (l : ℕ) :
    0 ≤ mszSigmaQLevel A l :=
  tsum_nonneg fun j => mszSigmaQTerm_nonneg A (l, j)

/-- Any finite shift sum at level `l` is bounded by its full shift sum. -/
theorem mszSigmaQLevel_sum_le (A : AdmissibleData) (l : ℕ) (s : Finset ℤ) :
    (∑ j ∈ s, mszSigmaQTerm A (l, j)) ≤ mszSigmaQLevel A l := by
  exact (mszSigmaQLevel_summable A l).sum_le_tsum s
    (fun j hj => mszSigmaQTerm_nonneg A (l, j))

/-- The sum of level coefficients for finitely many levels is bounded by
`sigma_q`, with no loss depending on the level cutoff. -/
theorem mszSigmaQ_finiteLevels_le (A : AdmissibleData) (L : ℕ) :
    (∑ l ∈ Finset.range (L + 1), mszSigmaQLevel A l) ≤ mszSigmaQ A := by
  have htotal := mszSigmaQTerm_summable A
  have hfiber : ∀ l : ℕ, Summable (fun j : ℤ => mszSigmaQTerm A (l, j)) :=
    fun l => mszSigmaQLevel_summable A l
  have houter : Summable (fun l : ℕ => mszSigmaQLevel A l) := htotal.prod
  calc
    (∑ l ∈ Finset.range (L + 1), mszSigmaQLevel A l) ≤
        ∑' l : ℕ, mszSigmaQLevel A l :=
      houter.sum_le_tsum _ (fun l hl => mszSigmaQLevel_nonneg A l)
    _ = ∑' z : ℕ × ℤ, mszSigmaQTerm A z := by
      symm
      exact htotal.tsum_prod' hfiber
    _ = mszSigmaQ A := rfl

/-- Every finite rectangle of level and symmetric-shift coefficients is
bounded by the source `sigma_q`. -/
theorem mszSigmaQ_finiteRectangle_le
    (A : AdmissibleData) (L J : ℕ) :
    (∑ l ∈ Finset.range (L + 1),
      ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), mszSigmaQTerm A (l, j)) ≤
      mszSigmaQ A := by
  calc
    (∑ l ∈ Finset.range (L + 1),
        ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), mszSigmaQTerm A (l, j)) ≤
      ∑ l ∈ Finset.range (L + 1), mszSigmaQLevel A l := by
        apply Finset.sum_le_sum
        intro l hl
        exact mszSigmaQLevel_sum_le A l (Finset.Icc (-(J : ℤ)) (J : ℤ))
    _ ≤ mszSigmaQ A := mszSigmaQ_finiteLevels_le A L

end

end FractionalPrimes.Literature.MSZ

end
