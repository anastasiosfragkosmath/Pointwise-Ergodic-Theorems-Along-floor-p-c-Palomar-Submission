module

public import FractionalPrimes.Literature.Polynomial.PolynomialTypeIInverse

/-!
# Scalar bilinear inverse data

This file formalizes blueprint item `lbi:data`.  It records the exact finite
index sets, normalized coefficient moments, bilinear correlation, and
unweighted phase correlations used by the bilinear inverse argument.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open _root_.Polynomial

noncomputable section

/-- Positive natural numbers in the exact half-open real interval
`(L / 2, 2 * L]`. -/
def bilinearLeftSet (L : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor (2 * L))).filter
    (fun l => L / 2 < (l : ℝ))

/-- Positive natural numbers in the exact half-open real interval
`(M, 2 * M]`. -/
def bilinearRightSet (M : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor (2 * M))).filter
    (fun m => M < (m : ℝ))

/-- Positive natural numbers `l` for which `l*m` lies in `(X,X+H]`. -/
def bilinearProductIntervalSet (X H : ℝ) (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor (X + H))).filter
    (fun l => X < (l * m : ℕ) ∧ ((l * m : ℕ) : ℝ) ≤ X + H)

@[simp]
theorem mem_bilinearLeftSet (L : ℝ) (l : ℕ) :
    l ∈ bilinearLeftSet L ↔
      1 ≤ l ∧ L / 2 < (l : ℝ) ∧ (l : ℝ) ≤ 2 * L := by
  simp only [bilinearLeftSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hl, hlfloor⟩, hlower⟩
    exact ⟨hl, hlower,
      (Nat.le_floor_iff' (Nat.ne_of_gt hl)).mp hlfloor⟩
  · rintro ⟨hl, hlower, hupper⟩
    exact ⟨⟨hl, Nat.le_floor hupper⟩, hlower⟩

@[simp]
theorem mem_bilinearRightSet (M : ℝ) (m : ℕ) :
    m ∈ bilinearRightSet M ↔
      1 ≤ m ∧ M < (m : ℝ) ∧ (m : ℝ) ≤ 2 * M := by
  simp only [bilinearRightSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hm, hmfloor⟩, hlower⟩
    exact ⟨hm, hlower,
      (Nat.le_floor_iff' (Nat.ne_of_gt hm)).mp hmfloor⟩
  · rintro ⟨hm, hlower, hupper⟩
    exact ⟨⟨hm, Nat.le_floor hupper⟩, hlower⟩

@[simp]
theorem mem_bilinearProductIntervalSet (X H : ℝ) (m l : ℕ)
    (hm : 0 < m) :
    l ∈ bilinearProductIntervalSet X H m ↔
      1 ≤ l ∧ X < ((l * m : ℕ) : ℝ) ∧
        ((l * m : ℕ) : ℝ) ≤ X + H := by
  simp only [bilinearProductIntervalSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hl, hlfloor⟩, hlower, hupper⟩
    exact ⟨hl, hlower, hupper⟩
  · rintro ⟨hl, hlower, hupper⟩
    have hlupper : (l : ℝ) ≤ X + H := by
      have hmone : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hm
      calc
        (l : ℝ) ≤ (l : ℝ) * (m : ℝ) := by
          nlinarith [show (0 : ℝ) ≤ (l : ℝ) by positivity]
        _ = ((l * m : ℕ) : ℝ) := by norm_num
        _ ≤ X + H := hupper
    exact ⟨⟨hl, Nat.le_floor hlupper⟩, hlower, hupper⟩

/-- The normalized second moment under the square root defining `U`. -/
def bilinearU2 (L : ℝ) (α : ℕ → ℂ) : ℝ :=
  L⁻¹ * ∑ l ∈ bilinearLeftSet L, ‖α l‖ ^ 2

/-- The normalized fourth moment under the fourth root defining `V`. -/
def bilinearV4 (M : ℝ) (β : ℕ → ℂ) : ℝ :=
  M⁻¹ * ∑ m ∈ bilinearRightSet M, ‖β m‖ ^ 4

/-- The exact nonnegative root `U` from the bilinear notation. -/
def bilinearU (L : ℝ) (α : ℕ → ℂ) : ℝ :=
  Real.sqrt (bilinearU2 L α)

/-- The exact nonnegative fourth root `V` from the bilinear notation. -/
def bilinearV (M : ℝ) (β : ℕ → ℂ) : ℝ :=
  Real.sqrt (Real.sqrt (bilinearV4 M β))

/-- The finite bilinear phase correlation `S`. -/
def bilinearS (X H M : ℝ) (α β : ℕ → ℂ)
    (P : Polynomial ℝ) : ℂ :=
  ∑ m ∈ bilinearRightSet M,
    ∑ l ∈ bilinearProductIntervalSet X H m,
      α l * β m * unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ))

/-- The left indices lying simultaneously in the two product windows. -/
def bilinearCommonLeftSet (X H L : ℝ) (m m' : ℕ) : Finset ℕ :=
  (bilinearLeftSet L).filter (fun l =>
    X < ((l * m : ℕ) : ℝ) ∧ ((l * m : ℕ) : ℝ) ≤ X + H ∧
    X < ((l * m' : ℕ) : ℝ) ∧ ((l * m' : ℕ) : ℝ) ≤ X + H)

/-- The unweighted phase correlation `C_{m,m'}`. -/
def bilinearC (X H L : ℝ) (P : Polynomial ℝ) (m m' : ℕ) : ℂ :=
  ∑ l ∈ bilinearCommonLeftSet X H L m m',
    unitFrequencyPhase
      (P.eval ((l * m : ℕ) : ℝ) - P.eval ((l * m' : ℕ) : ℝ))

/-- The exact bundle of quantities introduced in blueprint Definition
`lbi:data`. -/
structure BilinearData where
  r : ℝ
  s : ℝ
  leftSet : Finset ℕ
  rightSet : Finset ℕ
  U : ℝ
  V : ℝ
  S : ℂ
  C : ℕ → ℕ → ℂ

/-- Bilinear notation from blueprint item `lbi:data`. -/
def bilinearData (X H L M : ℝ) (α β : ℕ → ℂ)
    (P : Polynomial ℝ) : BilinearData where
  r := H / L
  s := H / M
  leftSet := bilinearLeftSet L
  rightSet := bilinearRightSet M
  U := bilinearU L α
  V := bilinearV M β
  S := bilinearS X H M α β P
  C := bilinearC X H L P

theorem bilinearU2_nonneg (L : ℝ) (hL : 0 < L) (α : ℕ → ℂ) :
    0 ≤ bilinearU2 L α := by
  unfold bilinearU2
  positivity

theorem bilinearV4_nonneg (M : ℝ) (hM : 0 < M) (β : ℕ → ℂ) :
    0 ≤ bilinearV4 M β := by
  unfold bilinearV4
  positivity

@[simp]
theorem bilinearU_sq (L : ℝ) (hL : 0 < L) (α : ℕ → ℂ) :
    bilinearU L α ^ 2 = bilinearU2 L α := by
  exact Real.sq_sqrt (bilinearU2_nonneg L hL α)

@[simp]
theorem bilinearV_pow_four (M : ℝ) (hM : 0 < M) (β : ℕ → ℂ) :
    bilinearV M β ^ 4 = bilinearV4 M β := by
  unfold bilinearV
  have hV4 := bilinearV4_nonneg M hM β
  have hsqrt : 0 ≤ Real.sqrt (bilinearV4 M β) := Real.sqrt_nonneg _
  calc
    Real.sqrt (Real.sqrt (bilinearV4 M β)) ^ 4 =
        (Real.sqrt (Real.sqrt (bilinearV4 M β)) ^ 2) ^ 2 := by ring
    _ = Real.sqrt (bilinearV4 M β) ^ 2 := by rw [Real.sq_sqrt hsqrt]
    _ = bilinearV4 M β := Real.sq_sqrt hV4

theorem bilinearU_nonneg (L : ℝ) (α : ℕ → ℂ) :
    0 ≤ bilinearU L α := Real.sqrt_nonneg _

theorem bilinearV_nonneg (M : ℝ) (β : ℕ → ℂ) :
    0 ≤ bilinearV M β := Real.sqrt_nonneg _

/-- Under the source scale assumptions, every left index that contributes to
`S` already belongs to the prescribed set `(L/2,2L]`. -/
theorem bilinearProductIntervalSet_subset_left
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (m l : ℕ) (hm : m ∈ bilinearRightSet M)
    (hl : l ∈ bilinearProductIntervalSet X H m) :
    l ∈ bilinearLeftSet L := by
  rw [mem_bilinearLeftSet]
  rw [mem_bilinearRightSet] at hm
  rcases hm with ⟨hmone, hmlo, hmhi⟩
  have hmNatPos : 0 < m := by omega
  rw [mem_bilinearProductIntervalSet X H m l hmNatPos] at hl
  rcases hl with ⟨hlone, hprodlo, hprodhi⟩
  have hcast : (((l * m : ℕ) : ℝ)) = (l : ℝ) * (m : ℝ) := by norm_num
  rw [hcast] at hprodlo hprodhi
  have hLlower : L / 2 < (l : ℝ) := by
    by_contra hnot
    have hlle : (l : ℝ) ≤ L / 2 := le_of_not_gt hnot
    have hmpos : 0 < (m : ℝ) := lt_trans hM hmlo
    have hprodle : (l : ℝ) * (m : ℝ) ≤ X := by
      calc
        (l : ℝ) * (m : ℝ) ≤ (L / 2) * (m : ℝ) :=
          mul_le_mul_of_nonneg_right hlle hmpos.le
        _ ≤ (L / 2) * (2 * M) :=
          mul_le_mul_of_nonneg_left hmhi (by positivity)
        _ = X := by rw [hX]; ring
    exact (not_lt_of_ge hprodle hprodlo)
  have hLupper : (l : ℝ) ≤ 2 * L := by
    have hXpos : 0 < X := by rw [hX]; positivity
    have hsum : X + H ≤ 2 * X := by linarith
    have hprod2 : (l : ℝ) * (m : ℝ) ≤ 2 * X := hprodhi.trans hsum
    have hl0 : 0 ≤ (l : ℝ) := by positivity
    by_contra hnot
    have hlt : 2 * L < (l : ℝ) := lt_of_not_ge hnot
    have hstrict : 2 * X < (l : ℝ) * (m : ℝ) := by
      rw [hX]
      calc
        2 * (L * M) = (2 * L) * M := by ring
        _ < (l : ℝ) * M := mul_lt_mul_of_pos_right hlt hM
        _ < (l : ℝ) * (m : ℝ) :=
          mul_lt_mul_of_pos_left hmlo (by exact_mod_cast hlone)
    exact (not_lt_of_ge hprod2 hstrict)
  exact ⟨hlone, hLlower, hLupper⟩

end

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.bilinearU_sq
#print axioms FractionalPrimes.Literature.Polynomial.bilinearV_pow_four
#print axioms FractionalPrimes.Literature.Polynomial.bilinearProductIntervalSet_subset_left
#print axioms FractionalPrimes.Literature.Polynomial.bilinearData
