module

public import FractionalPrimes.ArithmeticBasics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Elementary sieve data and scalar estimates

Definitions and elementary bounds from the blueprint's `ls:data` and
`ls:scalar` entries. Prime products are finite by construction.
-/

@[expose] public section

namespace FractionalPrimes

noncomputable section

def sievePrimesBelow (z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter fun p => Nat.Prime p ∧ (p : ℝ) < z

def sievePrimeProduct (z : ℝ) : ℕ :=
  ∏ p ∈ sievePrimesBelow z, p

def sieveDensityProduct (z : ℝ) : ℝ :=
  ∏ p ∈ sievePrimesBelow z, (1 - 1 / (p : ℝ))

def sieveConstantC : ℝ := Real.exp 13
def sieveK : ℝ := 8
def sieveBeta : ℝ := 513
def sieveQ : ℝ := (sieveBeta - 1) / (sieveBeta + 1)
def sieveB : ℝ := sieveK * Real.log (sieveQ⁻¹)
def sieveA : ℝ := 13 + sieveK * Real.log (2 * (sieveBeta + 1))
def sieveD₀ : ℝ :=
  sieveConstantC * (2 * (sieveBeta + 1)) ^ (sieveK) *
    Real.exp (sieveA / sieveB + sieveBeta) / (1 - Real.exp (-1))
def sieveD : ℝ := max sieveD₀ (Real.exp 2)
def sieveConstant : ℝ := 2 * (sieveD + 1)

theorem sieveQ_eq : sieveQ = (256 : ℝ) / 257 := by
  norm_num [sieveQ, sieveBeta]

theorem sieveQ_bounds : 0 < sieveQ ∧ sieveQ < 1 := by
  rw [sieveQ_eq]
  norm_num

theorem sieveB_bounds : 0 < sieveB ∧ sieveB ≤ 1 / 32 := by
  have hq := sieveQ_bounds
  have hlogpos : 0 < Real.log (sieveQ⁻¹) := by
    apply Real.log_pos
    exact (one_lt_inv₀ hq.1).2 hq.2
  have hlogle : Real.log (sieveQ⁻¹) ≤ sieveQ⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr hq.1)
  constructor
  · dsimp [sieveB, sieveK]
    positivity
  · dsimp [sieveB, sieveK]
    calc
      8 * Real.log (sieveQ⁻¹) ≤ 8 * (sieveQ⁻¹ - 1) :=
        mul_le_mul_of_nonneg_left hlogle (by norm_num)
      _ = 1 / 32 := by norm_num [sieveQ, sieveBeta]

theorem sieveExponentialScalarBound :
    Real.exp 1 * sieveB * Real.exp (sieveB / 2) ≤ Real.exp (-1) := by
  have hb := sieveB_bounds
  have hE : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hEpos : 0 < Real.exp 1 := Real.exp_pos 1
  have harg : sieveB / 2 ≤ 1 := by nlinarith
  have hexp : Real.exp (sieveB / 2) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr harg
  have hinv : 1 / 3 < 1 / Real.exp 1 :=
    one_div_lt_one_div_of_lt hEpos hE
  apply le_of_lt
  calc
    Real.exp 1 * sieveB * Real.exp (sieveB / 2) ≤
        Real.exp 1 * (1 / 32) * 3 := by
          gcongr
          · exact hb.2
          · exact le_trans hexp hE.le
    _ < 3 * (1 / 32) * 3 := by
          gcongr
    _ = 9 / 32 := by norm_num
    _ < 1 / 3 := by norm_num
    _ < Real.exp (-1) := by
          rw [Real.exp_neg]
          simpa [one_div] using hinv

theorem sieveA_pos : 0 < sieveA := by
  unfold sieveA sieveK sieveBeta
  have hlog : 0 < Real.log (2 * (513 + 1 : ℝ)) := by
    apply Real.log_pos
    norm_num
  positivity

theorem sieveLogExponentialScaleBound (r : ℕ) :
    Real.log sieveConstantC + sieveK *
        Real.log (2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r) ≤
      sieveA + sieveB * r := by
  have hbase : 0 < 2 * (sieveBeta + 1) := by norm_num [sieveBeta]
  have hqinv : 0 < sieveQ⁻¹ := inv_pos.mpr sieveQ_bounds.1
  have hlog : Real.log (2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r) =
      Real.log (2 * (sieveBeta + 1)) + (r : ℝ) * Real.log sieveQ⁻¹ := by
    rw [Real.log_mul (ne_of_gt hbase) (ne_of_gt (pow_pos hqinv r)), Real.log_pow]
  rw [sieveConstantC, Real.log_exp, hlog]
  dsimp [sieveA, sieveB, sieveK]
  apply le_of_eq
  ring

theorem sieveScalePower_factor (r : ℕ) :
    (2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r) ^ sieveK =
      (2 * (sieveBeta + 1)) ^ sieveK * Real.exp (sieveB * r) := by
  have hq : 0 < sieveQ⁻¹ := inv_pos.mpr sieveQ_bounds.1
  have hbase : 0 < 2 * (sieveBeta + 1) := by norm_num [sieveBeta]
  have hpow : (sieveQ⁻¹ ^ r) ^ sieveK = Real.exp (sieveB * r) := by
    rw [Real.rpow_def_of_pos (pow_pos hq r), Real.log_pow]
    rw [sieveB, sieveK]
    congr 1
    push_cast
    ring
  calc
    (2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r) ^ sieveK =
        (2 * (sieveBeta + 1)) ^ sieveK * (sieveQ⁻¹ ^ r) ^ sieveK :=
      Real.mul_rpow hbase.le (pow_pos hq r).le
    _ = (2 * (sieveBeta + 1)) ^ sieveK * Real.exp (sieveB * r) := by rw [hpow]

theorem sieveLogTwo_bounds :
    (2 : ℝ) / 3 ≤ Real.log 2 ∧ Real.log 2 ≤ 3 / 4 := by
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

theorem sieveFactorialBound {m : ℕ} (hm : 1 ≤ m) :
    ((m.factorial : ℕ) : ℝ) ≥ ((m : ℝ) / Real.exp 1) ^ m := by
  have hstirling := Stirling.le_factorial_stirling m
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (m : ℝ)) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three, hmR]
  have hnonneg : 0 ≤ ((m : ℝ) / Real.exp 1) ^ m := by positivity
  calc
    ((m : ℝ) / Real.exp 1) ^ m =
        1 * ((m : ℝ) / Real.exp 1) ^ m := by ring
    _ ≤ Real.sqrt (2 * Real.pi * (m : ℝ)) *
          ((m : ℝ) / Real.exp 1) ^ m :=
      mul_le_mul_of_nonneg_right hsqrt hnonneg
    _ ≤ (m.factorial : ℕ) := hstirling

theorem sievePow_one_add_div_le_exp {A B : ℝ} {m : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hm : 1 ≤ m) :
    (1 + A / (B * m)) ^ m ≤ Real.exp (A / B) := by
  let u : ℝ := A / (B * m)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huExp : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  calc
    (1 + u) ^ m ≤ (Real.exp u) ^ m := by
      exact pow_le_pow_left₀ (by positivity) huExp m
    _ = Real.exp (A / B) := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [u]
      field_simp [ne_of_gt hB, ne_of_gt hmR]
      <;> ring

theorem sieveFactorialExponentialBound {m r : ℕ}
    (hm : 1 ≤ m) (hrm : r ≤ m) :
    (sieveA + sieveB * r) ^ m / (m.factorial : ℕ) ≤
      Real.exp (sieveA / sieveB) * (Real.exp 1 * sieveB) ^ m := by
  have hA : 0 < sieveA := sieveA_pos
  have hB : 0 < sieveB := sieveB_bounds.1
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hfac : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have hstirling := sieveFactorialBound hm
  have hbase : 0 ≤ sieveA + sieveB * r := by positivity
  have hrmR : (r : ℝ) ≤ m := by exact_mod_cast hrm
  have hlin : sieveA + sieveB * r ≤ sieveA + sieveB * m := by
    exact add_le_add_right (mul_le_mul_of_nonneg_left hrmR hB.le) sieveA
  have hfactorialInv :
      (sieveA + sieveB * r) ^ m / (m.factorial : ℕ) ≤
        (sieveA + sieveB * r) ^ m / ((m : ℝ) / Real.exp 1) ^ m := by
    apply div_le_div_of_nonneg_left (by positivity)
      (by positivity) ?_
    exact_mod_cast hstirling
  have hpowlin :
      (Real.exp 1 * (sieveA + sieveB * r) / m) ^ m ≤
        (Real.exp 1 * (sieveA + sieveB * m) / m) ^ m := by
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ hmR.le
    exact mul_le_mul_of_nonneg_left hlin (Real.exp_pos 1).le
  have hrewrite :
      (sieveA + sieveB * r) ^ m / ((m : ℝ) / Real.exp 1) ^ m =
        (Real.exp 1 * (sieveA + sieveB * r) / m) ^ m := by
    calc
      _ = ((sieveA + sieveB * r) / ((m : ℝ) / Real.exp 1)) ^ m := by
        conv_rhs => rw [div_pow]
      _ = (Real.exp 1 * (sieveA + sieveB * r) / m) ^ m := by
        congr 1
        field_simp [ne_of_gt (Real.exp_pos 1), ne_of_gt hmR]
        <;> ring
  have hbaseEq : Real.exp 1 * (sieveA + sieveB * m) / m =
      (Real.exp 1 * sieveB) * (1 + sieveA / (sieveB * m)) := by
    field_simp [ne_of_gt hB, ne_of_gt hmR]
    <;> ring
  calc
    (sieveA + sieveB * r) ^ m / (m.factorial : ℕ) ≤
        (sieveA + sieveB * r) ^ m / ((m : ℝ) / Real.exp 1) ^ m := hfactorialInv
    _ = (Real.exp 1 * (sieveA + sieveB * r) / m) ^ m := hrewrite
    _ ≤ (Real.exp 1 * (sieveA + sieveB * m) / m) ^ m := hpowlin
    _ = (Real.exp 1 * sieveB) ^ m *
        (1 + sieveA / (sieveB * m)) ^ m := by rw [hbaseEq, mul_pow]
    _ ≤ (Real.exp 1 * sieveB) ^ m * Real.exp (sieveA / sieveB) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sievePow_one_add_div_le_exp hA hB hm
    _ = Real.exp (sieveA / sieveB) * (Real.exp 1 * sieveB) ^ m := by ring

theorem sieveExp_neg_nat (m : ℕ) :
    Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
  have h := Real.exp_nat_mul (-1) m
  convert h using 1 <;> congr 1 <;> push_cast <;> ring

theorem sieveExponentialLengthDecay {m r : ℕ} (hmr : 2 * r ≤ m) :
    Real.exp (sieveB * r) * (Real.exp 1 * sieveB) ^ m ≤
      Real.exp (-(m : ℝ)) := by
  have hB : 0 < sieveB := sieveB_bounds.1
  have hrm : (r : ℝ) ≤ (m : ℝ) / 2 := by
    have hcast : (2 : ℝ) * r ≤ (m : ℝ) := by exact_mod_cast hmr
    nlinarith
  have hshift : Real.exp (sieveB * r) ≤ Real.exp (sieveB / 2) ^ m := by
    calc
      Real.exp (sieveB * r) ≤ Real.exp ((m : ℝ) * (sieveB / 2)) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hrm hB.le])
      _ = Real.exp (sieveB / 2) ^ m := Real.exp_nat_mul (sieveB / 2) m
  have hsmall : Real.exp (sieveB / 2) * (Real.exp 1 * sieveB) ≤ Real.exp (-1) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using sieveExponentialScalarBound
  have hpow :
      (Real.exp (sieveB / 2) * (Real.exp 1 * sieveB)) ^ m ≤ Real.exp (-1) ^ m :=
    pow_le_pow_left₀ (by positivity) hsmall m
  calc
    Real.exp (sieveB * r) * (Real.exp 1 * sieveB) ^ m ≤
        Real.exp (sieveB / 2) ^ m * (Real.exp 1 * sieveB) ^ m :=
      mul_le_mul_of_nonneg_right hshift (by positivity)
    _ = (Real.exp (sieveB / 2) * (Real.exp 1 * sieveB)) ^ m := by
      rw [← mul_pow]
    _ ≤ Real.exp (-1) ^ m := hpow
    _ = Real.exp (-(m : ℝ)) := (sieveExp_neg_nat m).symm

theorem sieveScalarTailCutoff (s : ℝ) (m : ℕ) :
    (1 ≤ m ∧ s - sieveBeta < (m : ℝ)) ↔
      ⌊s - sieveBeta⌋₊ + 1 ≤ m := by
  let t : ℝ := s - sieveBeta
  change (1 ≤ m ∧ t < (m : ℝ)) ↔ ⌊t⌋₊ + 1 ≤ m
  by_cases ht : t ≤ 0
  · rw [Nat.floor_of_nonpos ht]
    constructor
    · rintro ⟨hm, _⟩
      omega
    · intro hm
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
      exact ⟨by omega, by linarith⟩
  · have htpos : 0 ≤ t := le_of_not_ge ht
    constructor
    · rintro ⟨hm, htm⟩
      have hfloor : ⌊t⌋₊ < m := (Nat.floor_lt htpos).2 htm
      omega
    · intro hm
      constructor
      · omega
      · apply (Nat.floor_lt htpos).1
        omega

private def natAddLEEquiv (k : ℕ) : ℕ ≃ {m : ℕ // k ≤ m} where
  toFun n := ⟨n + k, by omega⟩
  invFun m := m.1 - k
  left_inv n := by simp
  right_inv m := by
    apply Subtype.ext
    exact Nat.sub_add_cancel m.2

theorem sieveGeometricTail (k : ℕ) :
    (∑' m : {m : ℕ // k ≤ m}, Real.exp (-(m.1 : ℝ))) =
      Real.exp (-(k : ℝ)) / (1 - Real.exp (-1)) := by
  let e := natAddLEEquiv k
  have hsum := Equiv.tsum_eq e (fun m : {m : ℕ // k ≤ m} =>
    Real.exp (-(m.1 : ℝ)))
  rw [← hsum]
  have hshift : ∀ n : ℕ,
      Real.exp (-((e n).1 : ℝ)) =
        Real.exp (-(k : ℝ)) * Real.exp (-(n : ℝ)) := by
    intro n
    simp [e, natAddLEEquiv, Nat.cast_add, neg_add, Real.exp_add, mul_comm]
  simp_rw [hshift]
  rw [tsum_mul_left]
  have hrpos : 0 < Real.exp (-1) := Real.exp_pos _
  have hrlt : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hgeom : (∑' n : ℕ, Real.exp (-(n : ℝ))) =
      (1 - Real.exp (-1))⁻¹ := by
    simp_rw [sieveExp_neg_nat]
    exact tsum_geometric_of_lt_one hrpos.le hrlt
  rw [hgeom]
  field_simp [ne_of_gt (sub_pos.mpr hrlt)]

theorem sieveScalarGeometricTail (s : ℝ) :
    (∑' m : {m : ℕ // 1 ≤ m ∧ s - sieveBeta < (m : ℝ)},
      Real.exp (-(m.1 : ℝ))) ≤
      Real.exp (sieveBeta - s) / (1 - Real.exp (-1)) := by
  let t : ℝ := s - sieveBeta
  let k : ℕ := ⌊t⌋₊ + 1
  let source := {m : ℕ // 1 ≤ m ∧ t < (m : ℝ)}
  let target := {m : ℕ // k ≤ m}
  let e : source ≃ target := {
    toFun := fun m => ⟨m.1, (sieveScalarTailCutoff s m.1).1 (by simpa [t] using m.2)⟩
    invFun := fun m => ⟨m.1, (sieveScalarTailCutoff s m.1).2 (by simpa [k, t] using m.2)⟩
    left_inv := by intro m; apply Subtype.ext; rfl
    right_inv := by intro m; apply Subtype.ext; rfl
  }
  have hsum :
      (∑' m : source, Real.exp (-(m.1 : ℝ))) =
        (∑' m : target, Real.exp (-(m.1 : ℝ))) := by
    exact Equiv.tsum_eq e (fun m : target => Real.exp (-(m.1 : ℝ)))
  have hk : t < (k : ℝ) := by
    simpa [k, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hnum : Real.exp (-(k : ℝ)) ≤ Real.exp (sieveBeta - s) := by
    apply Real.exp_monotone
    dsimp [k, t]
    linarith
  have hrlt : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hden : 0 < 1 - Real.exp (-1) := sub_pos.mpr hrlt
  calc
    (∑' m : source, Real.exp (-(m.1 : ℝ))) =
        Real.exp (-(k : ℝ)) / (1 - Real.exp (-1)) := by
          rw [hsum]
          exact sieveGeometricTail k
    _ ≤ Real.exp (sieveBeta - s) / (1 - Real.exp (-1)) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)

theorem sieveScalarBounds :
    0 < sieveQ ∧ sieveQ < 1 ∧
    0 < sieveB ∧ sieveB ≤ 1 / 32 ∧
    Real.exp 1 * sieveB * Real.exp (sieveB / 2) ≤ Real.exp (-1) ∧
    0 < sieveA ∧
    (2 : ℝ) / 3 ≤ Real.log 2 ∧ Real.log 2 ≤ 3 / 4 ∧
    Real.exp 1 < 3 ∧
    (∀ m : ℕ, 1 ≤ m →
      ((m.factorial : ℕ) : ℝ) ≥ ((m : ℝ) / Real.exp 1) ^ m) ∧
    (∀ s : ℝ,
      (∑' m : {m : ℕ // 1 ≤ m ∧ s - sieveBeta < (m : ℝ)},
        Real.exp (-(m.1 : ℝ))) ≤
        Real.exp (sieveBeta - s) / (1 - Real.exp (-1))) := by
  exact ⟨sieveQ_bounds.1, sieveQ_bounds.2,
    sieveB_bounds.1, sieveB_bounds.2,
    sieveExponentialScalarBound, sieveA_pos,
    sieveLogTwo_bounds.1, sieveLogTwo_bounds.2,
    Real.exp_one_lt_three,
    (fun m hm => sieveFactorialBound hm),
    sieveScalarGeometricTail⟩

theorem sieveDensityProduct_antitone {a z : ℝ} (haz : a ≤ z) :
    sieveDensityProduct z ≤ sieveDensityProduct a := by
  have hsubset : sievePrimesBelow a ⊆ sievePrimesBelow z := by
    intro p hp
    unfold sievePrimesBelow at hp ⊢
    have hpcond := (Finset.mem_filter.mp hp).2
    have hpz : (p : ℝ) < z := lt_of_lt_of_le hpcond.2 haz
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      exact Nat.le_floor (by exact_mod_cast hpz.le)
    · exact ⟨hpcond.1, hpz⟩
  unfold sieveDensityProduct
  apply Finset.prod_le_prod_of_subset_of_le_one₀ hsubset
  · intro p hp
    have hprime : p.Prime := by
      unfold sievePrimesBelow at hp
      exact (Finset.mem_filter.mp hp).2.1
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
    have hpone : 1 ≤ (p : ℝ) := by exact_mod_cast hprime.one_le
    have hinv : 1 / (p : ℝ) ≤ 1 := by
      simpa using (one_div_le_one_div hpR (by norm_num : (0 : ℝ) < 1)).2 hpone
    linarith
  · intro p hp hnot
    have hprime : p.Prime := by
      unfold sievePrimesBelow at hp
      exact (Finset.mem_filter.mp hp).2.1
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
    have hinv : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith

end

end FractionalPrimes

end
