module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWAllocatedScale
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition
public import Mathlib.Tactic

/-! Exact source support, quotient cutoff, retained-block scales, and the
`J₀` cover used by the selected Möbius PTW dyadic decomposition. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Twisted

namespace FractionalPrimes.Literature.DirichletMean

/-- The source block count `J₀=2⌈log₂(2C)⌉+3`, written with natural
ceiling and the real logarithm. -/
noncomputable def selectedMobiusPTWDyadicBlockCount (C : ℝ) : ℕ :=
  2 * Nat.ceil (Real.log (2 * C) / Real.log 2) + 3

/-- The source `J₀` block count covers the full support ratio `C²`. -/
theorem selectedMobiusPTWDyadicBlockCount_covers
    {C : ℝ} (hC : 1 ≤ C) :
    4 * C ^ 2 ≤ (2 : ℝ) ^ selectedMobiusPTWDyadicBlockCount C := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let m : ℕ := Nat.ceil (Real.log (2 * C) / Real.log 2)
  have hceil : Real.log (2 * C) / Real.log 2 ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil _
  have hlogmul : Real.log (2 * C) ≤ (m : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp hceil
  have hexp := Real.exp_le_exp.mpr hlogmul
  have hleft : Real.exp (Real.log (2 * C)) = 2 * C :=
    Real.exp_log (by positivity)
  have hright : Real.exp ((m : ℝ) * Real.log 2) = (2 : ℝ) ^ m := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hleft, hright] at hexp
  have hsquare : (2 * C) * (2 * C) ≤
      ((2 : ℝ) ^ m) * ((2 : ℝ) ^ m) :=
    mul_le_mul hexp hexp (by positivity) (by positivity)
  have hpow : ((2 : ℝ) ^ m) * ((2 : ℝ) ^ m) =
      (2 : ℝ) ^ (m + m) := by rw [← pow_add]
  have hmle : m + m ≤ selectedMobiusPTWDyadicBlockCount C := by
    dsimp [selectedMobiusPTWDyadicBlockCount, m]
    omega
  have hpowle : (2 : ℝ) ^ (m + m) ≤
      (2 : ℝ) ^ selectedMobiusPTWDyadicBlockCount C :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hmle
  calc
    4 * C ^ 2 = (2 * C) * (2 * C) := by ring
    _ ≤ ((2 : ℝ) ^ m) * ((2 : ℝ) ^ m) := hsquare
    _ = (2 : ℝ) ^ (m + m) := hpow
    _ ≤ (2 : ℝ) ^ selectedMobiusPTWDyadicBlockCount C := hpowle

/-- The support interval in `largeTypeIIDyadicComponentData` transfers to
the allocated coefficient `a(r*n)` without changing the coefficient. -/
theorem selectedMobiusPTW_allocated_support_of_group_support
    {M C : ℝ} {r n : ℕ} {f : ComplexPositiveIntegerFunction}
    (hC : 1 ≤ C) (hsupport : complexPositiveSupportedOnInterval f
      (C⁻¹ * M) (C * M))
    (hcoeff : toComplexArithmeticFunction f (r * n) ≠ 0) :
    M / C ≤ ((r * n : ℕ) : ℝ) ∧ ((r * n : ℕ) : ℝ) ≤ C * M := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hcoeffNonzero : r * n ≠ 0 := by
    intro hzero
    apply hcoeff
    rw [hzero]
    simp [toComplexArithmeticFunction]
  have hprodpos : 0 < r * n := Nat.pos_of_ne_zero hcoeffNonzero
  have hcoeff' : f ⟨r * n, hprodpos⟩ ≠ 0 := by
    have happly := toComplexArithmeticFunction_apply f ⟨r * n, hprodpos⟩
    rw [happly] at hcoeff
    exact hcoeff
  have hbounds := hsupport ⟨r * n, hprodpos⟩ hcoeff'
  have hlow : C⁻¹ * M = M / C := by
    field_simp [ne_of_gt hCpos]
  rw [← hlow]
  exact hbounds

/-- A support bound gives an exact finite quotient cutoff, with the natural
ceiling kept at the source scale. -/
theorem selectedMobiusPTW_allocated_cutoff_of_group_support
    {M C : ℝ} {r n : ℕ} {f : ComplexPositiveIntegerFunction}
    (hC : 1 ≤ C) (hr : 1 ≤ r)
    (hsupport : complexPositiveSupportedOnInterval f
      (C⁻¹ * M) (C * M))
    (hcoeff : toComplexArithmeticFunction f (r * n) ≠ 0) :
    n ≤ Nat.ceil (C * M) := by
  have hsupp := selectedMobiusPTW_allocated_support_of_group_support
    hC hsupport hcoeff
  have hnle : n ≤ r * n := by
    calc
      n = 1 * n := by simp
      _ ≤ r * n := Nat.mul_le_mul_right n hr
  have hnreal : (n : ℝ) ≤ ((r * n : ℕ) : ℝ) := by exact_mod_cast hnle
  have hceil : C * M ≤ (Nat.ceil (C * M) : ℝ) := Nat.le_ceil _
  have hnceil : (n : ℝ) ≤ (Nat.ceil (C * M) : ℝ) :=
    hnreal.trans (hsupp.2.trans hceil)
  exact_mod_cast hnceil

/-- Every nonempty allocated dyadic block has original length in the
retained source range `[M/(2C),2CM]`. Here `N=2^j M/(4C)` and the block
is the exact quotient interval `(N/r,2N/r]`. -/
theorem selectedMobiusPTW_retained_block_scale
    {M C : ℝ} {r j n : ℕ}
    (hM : 0 < M) (hC : 1 ≤ C) (hr : 0 < r)
    (hsupport : M / C ≤ ((r * n : ℕ) : ℝ) ∧
      ((r * n : ℕ) : ℝ) ≤ C * M)
    (hblock : n ∈ factorExtractionRealInterval
      ((2 : ℝ) ^ j * (M / (4 * C * (r : ℝ))))
      (2 * ((2 : ℝ) ^ j * (M / (4 * C * (r : ℝ)))))) :
    M / (2 * C) ≤ (2 : ℝ) ^ j * M / (4 * C) ∧
      (2 : ℝ) ^ j * M / (4 * C) ≤ (2 * C) * M := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  let L : ℝ := (2 : ℝ) ^ j * (M / (4 * C * (r : ℝ)))
  let N : ℝ := (2 : ℝ) ^ j * M / (4 * C)
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hLupper : 0 < 2 * L := by positivity
  have hblock' :=
    (mem_factorExtractionRealInterval hLpos.le hLupper.le n).1 hblock
  have hN_eq : N = (r : ℝ) * L := by
    dsimp [N, L]
    field_simp [ne_of_gt hCpos, ne_of_gt hrR]
  have hNlt : N < ((r * n : ℕ) : ℝ) := by
    calc
      N = (r : ℝ) * L := hN_eq
      _ < (r : ℝ) * (n : ℝ) := mul_lt_mul_of_pos_left hblock'.1 hrR
      _ = ((r * n : ℕ) : ℝ) := by rw [Nat.cast_mul]
  have hupper : ((r * n : ℕ) : ℝ) ≤ 2 * N := by
    calc
      ((r * n : ℕ) : ℝ) = (r : ℝ) * (n : ℝ) := by rw [Nat.cast_mul]
      _ ≤ (r : ℝ) * (2 * L) := mul_le_mul_of_nonneg_left hblock'.2 hrR.le
      _ = 2 * N := by rw [hN_eq]; ring
  have hC0 : 0 < 2 * C := by positivity
  have hscaleLow : M / (2 * C) ≤ N := by
    apply (div_le_iff₀ hC0).2
    have hmul : C * (M / C) ≤ C * (2 * N) :=
      mul_le_mul_of_nonneg_left (hsupport.1.trans hupper) hCpos.le
    have hcancel : C * (M / C) = M := by
      field_simp [ne_of_gt hCpos]
    rw [hcancel] at hmul
    nlinarith
  have hscaleHigh : N ≤ (2 * C) * M := by
    calc
      N ≤ C * M := le_of_lt (hNlt.trans_le hsupport.2)
      _ ≤ (2 * C) * M := by
        have hmul := mul_le_mul_of_nonneg_right hC (le_of_lt hM)
        nlinarith
  simpa [N] using And.intro hscaleLow hscaleHigh

#print axioms selectedMobiusPTWDyadicBlockCount_covers
#print axioms selectedMobiusPTW_allocated_support_of_group_support
#print axioms selectedMobiusPTW_allocated_cutoff_of_group_support
#print axioms selectedMobiusPTW_retained_block_scale

end FractionalPrimes.Literature.DirichletMean

end
