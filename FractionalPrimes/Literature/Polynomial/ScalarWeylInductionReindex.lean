module

public import FractionalPrimes.ArithmeticBasicsCore
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Algebra.Order.Floor.Div

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- The natural ceiling quotient `⌈N/r⌉` lies between the real quotient
`N/r` and twice that quotient when `4r ≤ N`. -/
theorem scalarWeyl_ceilDiv_bounds
    {N r : ℕ} (hr : 0 < r) (h4r : 4 * r ≤ N) :
    (N : ℝ) / (r : ℝ) ≤ ((N ⌈/⌉ r : ℕ) : ℝ) ∧
      ((N ⌈/⌉ r : ℕ) : ℝ) ≤ 2 * (N : ℝ) / (r : ℝ) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hceilLowerNat : N ≤ r * (N ⌈/⌉ r) := by
    simpa [nsmul_eq_mul] using
      (le_smul_ceilDiv (a := r) (b := N) hr)
  have hceilLowerReal :
      (N : ℝ) / (r : ℝ) ≤ ((N ⌈/⌉ r : ℕ) : ℝ) := by
    apply (div_le_iff₀ hrR).2
    have hcast : (N : ℝ) ≤ (r : ℝ) * ((N ⌈/⌉ r : ℕ) : ℝ) := by
      exact_mod_cast hceilLowerNat
    simpa only [mul_comm] using hcast
  have hquot : 4 ≤ N / r := (Nat.le_div_iff_mul_le hr).2 h4r
  have hrem : N % r < r := Nat.mod_lt N hr
  have hrle : r ≤ r * (N / r) := by
    calc
      r = r * 1 := by simp
      _ ≤ r * (N / r) := Nat.mul_le_mul_left r (by omega)
  have hremle : N % r ≤ r * (N / r) := le_trans hrem.le hrle
  have hNle : N ≤ r * (2 * (N / r)) := by
    calc
      N = N % r + r * (N / r) := (Nat.mod_add_div N r).symm
      _ ≤ r * (N / r) + r * (N / r) := Nat.add_le_add_right hremle _
      _ = r * (2 * (N / r)) := by ring
  have hceilUpperNat : N ⌈/⌉ r ≤ 2 * (N / r) :=
    (ceilDiv_le_iff_le_mul hr).2 hNle
  have hceilUpperReal :
      ((N ⌈/⌉ r : ℕ) : ℝ) ≤ 2 * (N : ℝ) / (r : ℝ) := by
    calc
      ((N ⌈/⌉ r : ℕ) : ℝ) ≤ 2 * ((N / r : ℕ) : ℝ) := by
        exact_mod_cast hceilUpperNat
      _ ≤ 2 * (N : ℝ) / (r : ℝ) := by
        have hdiv : ((N / r : ℕ) : ℝ) ≤ (N : ℝ) / (r : ℝ) :=
          Nat.cast_div_le
        calc
          2 * ((N / r : ℕ) : ℝ) ≤ 2 * ((N : ℝ) / (r : ℝ)) :=
            mul_le_mul_of_nonneg_left hdiv (by norm_num)
          _ = 2 * (N : ℝ) / (r : ℝ) := by ring
  exact ⟨hceilLowerReal, hceilUpperReal⟩

/-- Reindex one residue fiber of an integer interval by `n = c + r*k`,
where `c = b-r`. The quotient interval is expressed using rational ceilings,
as in Mathlib's exact interval-filter identities. -/
theorem scalarWeyl_residueFiber_reindex
    {N r N' : ℕ} {lo hi b : ℤ}
    (hr : 0 < r) (hN' : N' = N ⌈/⌉ r)
    (hb : b ∈ Finset.Icc (1 : ℤ) (r : ℤ))
    (hJsubset : Finset.Ico lo hi ⊆ Finset.Icc (1 : ℤ) (N : ℤ)) :
    let c : ℤ := b - (r : ℤ)
    let K : Finset ℤ := Finset.Ico
      (Int.ceil (((lo - c : ℤ) : ℚ) / (r : ℚ)))
      (Int.ceil (((hi - c : ℤ) : ℚ) / (r : ℚ)))
    K ⊆ Finset.Icc (1 : ℤ) (N' : ℤ) ∧
      ∀ f : ℤ → ℂ,
        (∑ n ∈ (Finset.Ico lo hi).filter
          (fun n => n ≡ b [ZMOD (r : ℤ)]), f n) =
        ∑ k ∈ K, f (c + (r : ℤ) * k) := by
  classical
  have hrZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
  let c : ℤ := b - (r : ℤ)
  let K : Finset ℤ := Finset.Ico
    (Int.ceil (((lo - c : ℤ) : ℚ) / (r : ℚ)))
    (Int.ceil (((hi - c : ℤ) : ℚ) / (r : ℚ)))
  let eMul : ℤ ↪ ℤ :=
    ⟨fun k => k * (r : ℤ), mul_left_injective₀ hrZ.ne'⟩
  let eAdd : ℤ ↪ ℤ := ⟨fun k => k + c, add_left_injective c⟩
  let e : ℤ ↪ ℤ := eMul.trans eAdd
  have hbBounds := Finset.mem_Icc.mp hb
  have hcBounds : (1 : ℤ) - (r : ℤ) ≤ c ∧ c ≤ 0 := by
    dsimp [c]
    omega
  have hbc : b ≡ c [ZMOD (r : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-1, ?_⟩
    dsimp [c]
    ring
  have hfilterClass :
      (Finset.Ico lo hi).filter (fun n => n ≡ b [ZMOD (r : ℤ)]) =
        (Finset.Ico lo hi).filter (fun n => n ≡ c [ZMOD (r : ℤ)]) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hmod⟩
      exact ⟨hn, hmod.trans hbc⟩
    · rintro ⟨hn, hmod⟩
      exact ⟨hn, hmod.trans hbc.symm⟩
  have hmodEq :
      (Finset.Ico lo hi).filter (fun n => n ≡ c [ZMOD (r : ℤ)]) =
        ((Finset.Ico (lo - c) (hi - c)).filter (fun x => (r : ℤ) ∣ x)).map eAdd := by
    simpa [eAdd] using (Int.Ico_filter_modEq_eq lo hi c)
  have hdvdEq :
      (Finset.Ico (lo - c) (hi - c)).filter (fun x => (r : ℤ) ∣ x) =
        K.map eMul := by
    simpa [K, eMul] using
      (Int.Ico_filter_dvd_eq (lo - c) (hi - c) hrZ)
  have hfiber :
      (Finset.Ico lo hi).filter (fun n => n ≡ b [ZMOD (r : ℤ)]) = K.map e := by
    calc
      (Finset.Ico lo hi).filter (fun n => n ≡ b [ZMOD (r : ℤ)]) =
          (Finset.Ico lo hi).filter (fun n => n ≡ c [ZMOD (r : ℤ)]) := hfilterClass
      _ = ((Finset.Ico (lo - c) (hi - c)).filter
          (fun x => (r : ℤ) ∣ x)).map eAdd := hmodEq
      _ = (K.map eMul).map eAdd := by rw [hdvdEq]
      _ = K.map e := by
        rw [Finset.map_map]
  have he_formula (k : ℤ) : e k = c + (r : ℤ) * k := by
    dsimp [e, eMul, eAdd]
    ring
  have hKsubset : K ⊆ Finset.Icc (1 : ℤ) (N' : ℤ) := by
    intro k hk
    have hke : e k ∈ K.map e := Finset.mem_map.mpr ⟨k, hk, rfl⟩
    have hkfiber : e k ∈
        (Finset.Ico lo hi).filter (fun n => n ≡ b [ZMOD (r : ℤ)]) := by
      rwa [← hfiber] at hke
    have hkn := Finset.mem_Icc.mp
      (hJsubset (Finset.mem_filter.mp hkfiber).1)
    have hformula := he_formula k
    have hkpos : 0 < k := by
      by_contra hknot
      have hk0 : k ≤ 0 := le_of_not_gt hknot
      have hmul : (r : ℤ) * k ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hrZ) hk0
      have hnle : c + (r : ℤ) * k ≤ 0 := by
        omega
      rw [hformula] at hkn
      omega
    have hkcast : ((k.toNat : ℕ) : ℤ) = k :=
      Int.toNat_of_nonneg hkpos.le
    have hmulUpper : (r : ℤ) * k ≤ (N : ℤ) + (r : ℤ) - 1 := by
      rw [hformula] at hkn
      omega
    have hcastMul : ((r * k.toNat : ℕ) : ℤ) = (r : ℤ) * k := by
      rw [Nat.cast_mul, hkcast]
    have hcastUpper :
        ((N + r - 1 : ℕ) : ℤ) = (N : ℤ) + (r : ℤ) - 1 := by
      have hpos : 1 ≤ N + r := by omega
      simp only [Nat.cast_sub hpos, Nat.cast_add, Nat.cast_one]
    have hmulUpperNat : r * k.toNat ≤ N + r - 1 := by
      have hmulUpperCast :
          ((r * k.toNat : ℕ) : ℤ) ≤ ((N + r - 1 : ℕ) : ℤ) := by
        rw [hcastMul, hcastUpper]
        exact hmulUpper
      exact_mod_cast hmulUpperCast
    have hkdiv : k.toNat ≤ (N + r - 1) / r :=
      (Nat.le_div_iff_mul_le hr).2 (by simpa [Nat.mul_comm] using hmulUpperNat)
    have hkNat : k.toNat ≤ N' := by
      rw [hN', Nat.ceilDiv_eq_add_pred_div]
      exact hkdiv
    exact Finset.mem_Icc.mpr ⟨by omega, by rw [← hkcast]; exact_mod_cast hkNat⟩
  refine ⟨hKsubset, ?_⟩
  intro f
  calc
    (∑ n ∈ (Finset.Ico lo hi).filter
        (fun n => n ≡ b [ZMOD (r : ℤ)]), f n) =
        ∑ k ∈ K.map e, f k := by rw [hfiber]
    _ = ∑ k ∈ K, f (c + (r : ℤ) * k) := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro k hk
      rw [he_formula]

end FractionalPrimes.Literature.Polynomial
