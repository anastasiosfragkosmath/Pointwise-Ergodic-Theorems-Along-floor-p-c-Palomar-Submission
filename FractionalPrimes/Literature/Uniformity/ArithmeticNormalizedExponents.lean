module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import FractionalPrimes.Literature.Uniformity.ArithmeticDyadicComponents

/-!
# Normalized exponents for exact dyadic arithmetic components

This file formalizes blueprint item `lucomb:exponents`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity.Combinatorics

noncomputable section

private theorem dyadicFactorScaleProduct_eq_fin {X : ℝ}
    (fs : List (DyadicArithmeticFactor X)) :
    dyadicFactorScaleProduct fs =
      ∏ i : Fin fs.length, dyadicFactorScale (fs[i]) := by
  change (fs.map dyadicFactorScale).prod = _
  simpa only [Fin.getElem_fin] using
    (Fin.prod_univ_fun_getElem fs dyadicFactorScale).symm

/-- The explicit comparison constant `C_* = 2^23` from `lucomb:exponents`. -/
def normalizedExponentConstant : ℝ := (2 : ℝ) ^ 23

private theorem dyadicScale_lt_natCast_of_mem_interval {j n : ℕ}
    (h : inDyadicInterval j n) : dyadicScale j < (n : ℝ) := by
  by_cases hj : j = 0
  · have hn : 0 < n := by
      simpa [inDyadicInterval, dyadicLowerNat, hj] using h.1
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
    rw [dyadicScale, if_pos hj]
    norm_num
    linarith
  · have hnat : 2 ^ j.pred < n := by
      simpa [inDyadicInterval, dyadicLowerNat, hj] using h.1
    have hreal : (2 : ℝ) ^ j.pred < (n : ℝ) := by exact_mod_cast hnat
    simpa [dyadicScale, hj] using hreal

private theorem normalizedExponents_of_retained {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X)
    (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20)
    (hret : dyadicFactorsRetained (X := X) (z := dyadicMobiusCutoff X) fs) :
    ∃ α : Fin fs.length → ℝ,
      (∀ i, 0 ≤ α i) ∧
      (∑ i : Fin fs.length, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ (α i) ≤ dyadicFactorScale (fs[i]) ∧
          dyadicFactorScale (fs[i]) ≤
            normalizedExponentConstant * X ^ (α i)) ∧
      (∀ i j, fs[i] = .mobius j → α i ≤ (1 / 8 : ℝ)) := by
  let N : Fin fs.length → ℝ := fun i => dyadicFactorScale (fs[i])
  let M : Fin fs.length → ℝ := fun i => max 1 (N i)
  let Q : ℝ := ∏ i : Fin fs.length, M i
  let S : ℝ := Real.log Q
  let α : Fin fs.length → ℝ := fun i => Real.log (M i) / S
  have hXpos : 0 < X := by
    have : (0 : ℝ) < (2 : ℝ) ^ 120 := by positivity
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogXlarge : (120 : ℝ) * Real.log 2 ≤ Real.log X := by
    calc
      (120 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 120) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log X := Real.log_le_log (by positivity) hX
  have hPpos : 0 < dyadicFactorScaleProduct fs := by
    rcases hret.2.2 with hlow
    by_contra hnonpos
    have hnonpos' : dyadicFactorScaleProduct fs ≤ 0 := le_of_not_gt hnonpos
    have hpowpos : 0 < (2 : ℝ) ^ fs.length := by positivity
    nlinarith
  have hPlo : X / (2 : ℝ) ^ 21 ≤ dyadicFactorScaleProduct fs := by
    have hpow : (2 : ℝ) ^ fs.length ≤ (2 : ℝ) ^ 20 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen.2
    have hXle : X ≤ (2 : ℝ) ^ 21 * dyadicFactorScaleProduct fs := by
      calc
        X ≤ 2 * ((2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs) := by
          have hlow := hret.2.2
          nlinarith
        _ ≤ 2 * ((2 : ℝ) ^ 20 * dyadicFactorScaleProduct fs) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hpow hPpos.le
          · norm_num
        _ = (2 : ℝ) ^ 21 * dyadicFactorScaleProduct fs := by
          rw [pow_succ]
          ring
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 21)).2
    nlinarith [hXle]
  have hPupper : dyadicFactorScaleProduct fs ≤ 4 * X := hret.2.1.le
  have hNpos : ∀ i, 0 < N i := by
    intro i
    have hlow : (1 / 2 : ℝ) ≤ N i := by
      simpa [N] using dyadicFactorScale_ge_half (fs[i])
    linarith
  have hMpos : ∀ i, 0 < M i := by
    intro i
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hNleM : ∀ i, N i ≤ M i := by
    intro i
    dsimp [M]
    exact le_max_right _ _
  have hMleTwoN : ∀ i, M i ≤ 2 * N i := by
    intro i
    dsimp [M]
    apply max_le
    · have hlow : (1 / 2 : ℝ) ≤ N i := by
        simpa [N] using dyadicFactorScale_ge_half (fs[i])
      nlinarith
    · nlinarith [hNpos i]
  have hPfin : dyadicFactorScaleProduct fs = ∏ i : Fin fs.length, N i := by
    dsimp [N]
    exact dyadicFactorScaleProduct_eq_fin fs
  have hQlo : dyadicFactorScaleProduct fs ≤ Q := by
    dsimp [Q]
    rw [hPfin]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (hNpos i).le
    · intro i hi
      exact hNleM i
  have hQfactor : Q ≤ ∏ i : Fin fs.length, (2 * N i) := by
    dsimp [Q]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (hMpos i).le
    · intro i hi
      exact hMleTwoN i
  have hQproduct :
      (∏ i : Fin fs.length, (2 * N i)) =
        (2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs := by
    rw [Finset.prod_mul_distrib, hPfin]
    simp
  have hpowlen : (2 : ℝ) ^ fs.length ≤ (2 : ℝ) ^ 20 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen.2
  have hQlower : X / (2 : ℝ) ^ 21 ≤ Q := hPlo.trans hQlo
  have hQupper : Q ≤ (2 : ℝ) ^ 22 * X := by
    calc
      Q ≤ (2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs := by
        rw [← hQproduct]
        exact hQfactor
      _ ≤ (2 : ℝ) ^ 20 * dyadicFactorScaleProduct fs :=
        mul_le_mul_of_nonneg_right hpowlen hPpos.le
      _ ≤ (2 : ℝ) ^ 20 * (4 * X) :=
        mul_le_mul_of_nonneg_left hPupper (by positivity)
      _ = (2 : ℝ) ^ 22 * X := by norm_num [pow_succ]; ring
  have hQpos : 0 < Q := by
    have hlo : 0 < X / (2 : ℝ) ^ 21 := div_pos hXpos (by positivity)
    linarith
  have hlogQ : Real.log Q = ∑ i : Fin fs.length, Real.log (M i) := by
    simpa [Q] using
      (Real.log_prod (s := Finset.univ) (f := M)
        (by intro i hi; exact (hMpos i).ne'))
  have hlogQlower : Real.log (X / (2 : ℝ) ^ 21) ≤ S := by
    dsimp [S]
    exact Real.log_le_log (div_pos hXpos (by positivity)) hQlower
  have hlogQupper : S ≤ Real.log ((2 : ℝ) ^ 22 * X) := by
    dsimp [S]
    exact Real.log_le_log hQpos hQupper
  have hlogDiv :
      Real.log (X / (2 : ℝ) ^ 21) = Real.log X - 21 * Real.log 2 := by
    rw [Real.log_div hXpos.ne' (pow_ne_zero _ (by norm_num)), Real.log_pow]
    norm_num
  have hlogMul :
      Real.log ((2 : ℝ) ^ 22 * X) = Real.log X + 22 * Real.log 2 := by
    rw [Real.log_mul (pow_ne_zero _ (by norm_num)) hXpos.ne', Real.log_pow]
    norm_num [add_comm]
  have hSbounds :
      Real.log X - 22 * Real.log 2 ≤ S ∧ S ≤ Real.log X + 22 * Real.log 2 := by
    constructor
    · rw [hlogDiv] at hlogQlower
      linarith [hlog2pos.le]
    · rw [hlogMul] at hlogQupper
      exact hlogQupper
  have hSpos : 0 < S := by
    have hlog2pos' : 0 < Real.log 2 := hlog2pos
    linarith [hSbounds.1, hlogXlarge]
  have hSdiff : |S - Real.log X| ≤ 22 * Real.log 2 := by
    rw [abs_le]
    constructor <;> linarith [hSbounds.1, hSbounds.2]
  have hαnonneg : ∀ i, 0 ≤ α i := by
    intro i
    dsimp [α]
    apply div_nonneg
    · exact Real.log_nonneg (le_max_left 1 (N i))
    · exact hSpos.le
  have hsumAlpha : ∑ i : Fin fs.length, α i = 1 := by
    calc
      ∑ i : Fin fs.length, α i =
          (∑ i : Fin fs.length, Real.log (M i)) / S := by
            simp [α, Finset.sum_div]
      _ = S / S := by rw [← hlogQ]
      _ = 1 := div_self hSpos.ne'
  have hlogMnonneg : ∀ i, 0 ≤ Real.log (M i) := by
    intro i
    exact Real.log_nonneg (le_max_left 1 (N i))
  have hlogMleS : ∀ i, Real.log (M i) ≤ S := by
    intro i
    calc
      Real.log (M i) ≤ ∑ j : Fin fs.length, Real.log (M j) :=
        Finset.single_le_sum (fun j hj => hlogMnonneg j) (Finset.mem_univ i)
      _ = S := by rw [← hlogQ]
  have hαleone : ∀ i, α i ≤ 1 := by
    intro i
    dsimp [α]
    exact (div_le_one hSpos).2 (hlogMleS i)
  have hlogScaleM : ∀ i, |Real.log (N i) - Real.log (M i)| ≤ Real.log 2 := by
    intro i
    have hlow : (1 / 2 : ℝ) ≤ N i := by
      dsimp [N]
      exact dyadicFactorScale_ge_half (fs[i])
    have hNiMi : N i ≤ M i := hNleM i
    have hMiTwoNi : M i ≤ 2 * N i := hMleTwoN i
    have hNiPos : 0 < N i := hNpos i
    have hMiPos : 0 < M i := hMpos i
    have hlogNiMi : Real.log (N i) ≤ Real.log (M i) :=
      (Real.log_le_log_iff hNiPos hMiPos).2 hNiMi
    have hlogMiTwoNi : Real.log (M i) ≤ Real.log (2 * N i) :=
      (Real.log_le_log_iff hMiPos (mul_pos (by norm_num) hNiPos)).2 hMiTwoNi
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNiPos.ne'] at hlogMiTwoNi
    rw [abs_le]
    constructor <;> nlinarith [hlog2pos.le, hlogNiMi, hlogMiTwoNi]
  have hlogAlphaError :
      ∀ i, |Real.log (M i) - α i * Real.log X| ≤ 22 * Real.log 2 := by
    intro i
    have hidentity :
        Real.log (M i) - α i * Real.log X = α i * (S - Real.log X) := by
      dsimp [α]
      field_simp [ne_of_gt hSpos]
    rw [hidentity, abs_mul, abs_of_nonneg (hαnonneg i)]
    calc
      α i * |S - Real.log X| ≤ α i * (22 * Real.log 2) :=
        mul_le_mul_of_nonneg_left hSdiff (hαnonneg i)
      _ ≤ 1 * (22 * Real.log 2) :=
        mul_le_mul_of_nonneg_right (hαleone i) (by positivity)
      _ = 22 * Real.log 2 := by ring
  have hlogScaleAlphaError :
      ∀ i, |Real.log (N i) - α i * Real.log X| ≤ 23 * Real.log 2 := by
    intro i
    calc
      |Real.log (N i) - α i * Real.log X| =
          |(Real.log (N i) - Real.log (M i)) +
            (Real.log (M i) - α i * Real.log X)| := by congr 1 <;> ring
      _ ≤ |Real.log (N i) - Real.log (M i)| +
            |Real.log (M i) - α i * Real.log X| := abs_add_le _ _
      _ ≤ Real.log 2 + 22 * Real.log 2 :=
            add_le_add (hlogScaleM i) (hlogAlphaError i)
      _ = 23 * Real.log 2 := by ring
  have hCLog : Real.log normalizedExponentConstant = 23 * Real.log 2 := by
    simp [normalizedExponentConstant, Real.log_pow]
  have hCpos : 0 < normalizedExponentConstant := by
    change (0 : ℝ) < (2 : ℝ) ^ 23
    positivity
  have hCInvLog : Real.log normalizedExponentConstant⁻¹ = -(23 * Real.log 2) := by
    rw [Real.log_inv, hCLog]
  have hcompare : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ (α i) ≤ N i ∧
        N i ≤ normalizedExponentConstant * X ^ (α i) := by
    intro i
    have hpowpos : 0 < X ^ (α i) := Real.rpow_pos_of_pos hXpos _
    have hlowlog :
        Real.log (normalizedExponentConstant⁻¹ * X ^ (α i)) ≤ Real.log (N i) := by
      rw [Real.log_mul (inv_ne_zero hCpos.ne') hpowpos.ne']
      rw [hCInvLog, Real.log_rpow hXpos]
      have herr := abs_le.mp (hlogScaleAlphaError i)
      linarith
    have huplog :
        Real.log (N i) ≤ Real.log (normalizedExponentConstant * X ^ (α i)) := by
      rw [Real.log_mul hCpos.ne' hpowpos.ne']
      rw [hCLog, Real.log_rpow hXpos]
      have herr := abs_le.mp (hlogScaleAlphaError i)
      linarith
    exact ⟨(Real.log_le_log_iff
      (mul_pos (inv_pos.mpr hCpos) hpowpos) (hNpos i)).1 hlowlog,
      (Real.log_le_log_iff (hNpos i)
        (mul_pos hCpos hpowpos)).1 huplog⟩
  have hz : 1 < dyadicMobiusCutoff X := by
    dsimp [dyadicMobiusCutoff]
    apply Real.one_lt_rpow
    · nlinarith [hX]
    · norm_num
  refine ⟨α, ?_, hsumAlpha, ?_, ?_⟩
  · exact hαnonneg
  · intro i
    simpa [N] using hcompare i
  · intro i j hij
    have hmem : fs[i] ∈ fs := List.getElem_mem _
    have hfn : dyadicFactorFunction (dyadicMobiusCutoff X) (fs[i]) ≠ 0 :=
      hret.1 _ hmem
    rw [hij] at hfn
    change dyadicMobiusFactor (dyadicMobiusCutoff X) j.val.val ≠ 0 at hfn
    have hexists : ∃ n, dyadicMobiusFactor (dyadicMobiusCutoff X) j.val.val n ≠ 0 := by
      by_contra hnone
      apply hfn
      ext n
      by_contra hn
      exact hnone ⟨n, hn⟩
    obtain ⟨n, hn⟩ := hexists
    have hinterval : inDyadicInterval j.val.val n := by
      by_cases hc : inDyadicInterval j.val.val n ∧
          (n : ℝ) ≤ dyadicMobiusCutoff X
      · exact hc.1
      · simp [dyadicMobiusFactor_apply, hc] at hn
    have hcutoff : (n : ℝ) ≤ dyadicMobiusCutoff X := by
      by_contra hcut
      have hc : ¬ (inDyadicInterval j.val.val n ∧
          (n : ℝ) ≤ dyadicMobiusCutoff X) := by
        simp [hinterval, hcut]
      simp [dyadicMobiusFactor_apply, hc] at hn
    have hNltz : N i < dyadicMobiusCutoff X := by
      change dyadicFactorScale (fs[i]) < dyadicMobiusCutoff X
      rw [hij]
      change dyadicScale j.val.val < dyadicMobiusCutoff X
      exact (dyadicScale_lt_natCast_of_mem_interval hinterval).trans_le hcutoff
    have hMleZ : M i ≤ dyadicMobiusCutoff X := by
      dsimp [M]
      exact max_le (le_of_lt hz) hNltz.le
    have hlogMcutoff : Real.log (M i) ≤ Real.log (dyadicMobiusCutoff X) :=
      Real.log_le_log (hMpos i) hMleZ
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hlogZ :
        Real.log (dyadicMobiusCutoff X) =
          (1 / 10 : ℝ) * Real.log X + (1 / 5 : ℝ) * Real.log 2 := by
      rw [dyadicMobiusCutoff, Real.log_rpow (by positivity : (0 : ℝ) < 4 * X),
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hXpos.ne', hlog4]
      ring
    have hnum : 8 * Real.log (M i) ≤ S := by
      calc
        8 * Real.log (M i) ≤ 8 *
            ((1 / 10 : ℝ) * Real.log X + (1 / 5 : ℝ) * Real.log 2) := by
              exact mul_le_mul_of_nonneg_left (by rw [← hlogZ]; exact hlogMcutoff)
                (by norm_num)
        _ ≤ Real.log X - 22 * Real.log 2 := by
              nlinarith [hlogXlarge, hlog2pos.le]
        _ ≤ S := hSbounds.1
    dsimp [α]
    apply (div_le_iff₀ hSpos).2
    nlinarith only [hnum]

theorem normalizedExponents {X : ℝ} (hX : (2 : ℝ) ^ 120 ≤ X)
    {fs : List (DyadicArithmeticFactor X)}
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20)
    (hret : dyadicFactorsRetained (X := X) (z := dyadicMobiusCutoff X) fs) :
    ∃ α : Fin fs.length → ℝ,
      (∀ i, 0 ≤ α i) ∧
      (∑ i : Fin fs.length, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ (α i) ≤ dyadicFactorScale (fs[i]) ∧
          dyadicFactorScale (fs[i]) ≤
            normalizedExponentConstant * X ^ (α i)) ∧
      (∀ i j, fs[i] = .mobius j → α i ≤ (1 / 8 : ℝ)) :=
  normalizedExponents_of_retained hX fs hlen hret

theorem mobiusComponentNormalizedExponents {X : ℝ}
    {ν : MobiusDyadicLabel X}
    (hX : (2 : ℝ) ^ 120 ≤ X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)) :
    ∃ α : Fin (mobiusLabelFactors ν).length → ℝ,
      (∀ i, 0 ≤ α i) ∧
      (∑ i : Fin (mobiusLabelFactors ν).length, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ (α i) ≤
            dyadicFactorScale ((mobiusLabelFactors ν)[i]) ∧
          dyadicFactorScale ((mobiusLabelFactors ν)[i]) ≤
            normalizedExponentConstant * X ^ (α i)) ∧
      (∀ i j, (mobiusLabelFactors ν)[i] = .mobius j →
        α i ≤ (1 / 8 : ℝ)) := by
  have hlen := mobiusLabelFactorCount ν
  have hret := mobiusDyadicLabels_mem hν
  exact normalizedExponents (X := X) (fs := mobiusLabelFactors ν) hX hlen hret

theorem vonMangoldtComponentNormalizedExponents {X : ℝ}
    {ν : VonMangoldtDyadicLabel X}
    (hX : (2 : ℝ) ^ 120 ≤ X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) :
    ∃ α : Fin (vonMangoldtLabelFactors ν).length → ℝ,
      (∀ i, 0 ≤ α i) ∧
      (∑ i : Fin (vonMangoldtLabelFactors ν).length, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ (α i) ≤
            dyadicFactorScale ((vonMangoldtLabelFactors ν)[i]) ∧
          dyadicFactorScale ((vonMangoldtLabelFactors ν)[i]) ≤
            normalizedExponentConstant * X ^ (α i)) ∧
      (∀ i j, (vonMangoldtLabelFactors ν)[i] = .mobius j →
        α i ≤ (1 / 8 : ℝ)) := by
  have hlen := vonMangoldtLabelFactorCount ν
  have hret := vonMangoldtDyadicLabels_mem hν
  exact normalizedExponents (X := X) (fs := vonMangoldtLabelFactors ν) hX hlen hret

#print axioms normalizedExponents
#print axioms mobiusComponentNormalizedExponents
#print axioms vonMangoldtComponentNormalizedExponents

end

end FractionalPrimes.Literature.Uniformity.Combinatorics

end
