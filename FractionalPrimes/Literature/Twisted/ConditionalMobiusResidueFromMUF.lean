module
public import FractionalPrimes.Literature.Twisted.NonunitResidueIntervalGcdReindex
public import FractionalPrimes.Literature.Twisted.MobiusHighHeightFactorGoal
public import FractionalPrimes.Literature.MobiusToLong.ResidueCharacterExpansion
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
@[expose] public section

/-!
# Nonunit short-interval Möbius residue sums from MUF

This is a conditional adapter: the scalar high-height Möbius estimate remains
an explicit premise.  The proof divides a residue and its modulus by their
gcd, expands the reduced unit residue by finite character orthogonality, and
applies the scalar estimate with its gcd parameter retained.
-/

@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

namespace FractionalPrimes.Literature.Twisted

/-- The source summand `μ(n)n^(-1/2-it)` on positive integers. -/
def mobiusMellinResidueTerm (t : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) *
    (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))

private theorem sqrt_mul_inverse_sqrt {y : ℝ} (hy : 0 < y) :
    Real.sqrt y * y ^ (-1 / 2 : ℝ) = 1 := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_add hy]
  have hpow : (1 / 2 : ℝ) + (-1 / 2 : ℝ) = 0 := by ring
  rw [hpow, Real.rpow_zero]

private theorem mobiusResidueGcdScalar_bound
    {d : ℕ} {M : ℝ} (hd : 0 < d) (hM : 0 ≤ M) (hdM : 1 ≤ (d : ℝ))
    (t : ℝ) :
    ‖(d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ *
        Real.sqrt (M / (d : ℝ)) ≤ Real.sqrt M := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrtD : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hscalar :
      ‖(d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ =
        1 / Real.sqrt (d : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos hd]
    have hre : (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)).re = -(1 / 2 : ℝ) := by
      simp
    rw [hre]
    have hpow : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hinv : (d : ℝ) ^ (-(1 / 2 : ℝ)) =
        1 / Real.sqrt (d : ℝ) := by
      have hmul := sqrt_mul_inverse_sqrt hdR
      have hmul' : Real.sqrt (d : ℝ) *
          (d : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
        simpa only [hpow] using hmul
      rw [eq_div_iff hsqrtD.ne']
      nlinarith [hmul']
    exact hinv
  rw [hscalar, Real.sqrt_div hM (d : ℝ)]
  calc
    (1 / Real.sqrt (d : ℝ)) *
        (Real.sqrt M / Real.sqrt (d : ℝ)) =
          Real.sqrt M / (Real.sqrt (d : ℝ) ^ 2) := by ring
    _ = Real.sqrt M / (d : ℝ) := by rw [Real.sq_sqrt hdR.le]
    _ ≤ Real.sqrt M := div_le_self (Real.sqrt_nonneg M) hdM

/-- The exact `lda:mobius-residue` estimate, with the `MUF` premise kept
explicit.  The threshold is the scalar-goal threshold at exponent `α/2`,
enlarged only to ensure `(log X)^B ≤ X^(α/2)`.  The residue `b` is represented
by its standard natural representative `0 ≤ b < q`. -/
theorem mobiusResidueFromFactorGoal
    (hMUF : MobiusUniformity)
    {α A B K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hA : 0 < A) (hB : 0 < B) (hK : 0 < K) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X M : ℝ}, X₀ ≤ X → X ^ α ≤ M → M ≤ X →
        {q : ℕ} → 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
        {b : ℕ} → b < q → (t : ℝ) → |t| ≤ X ^ A →
        {u v : ℝ} → M ≤ u → u ≤ v → v ≤ 2 * M →
        ‖∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
            if n % q = b then mobiusMellinResidueTerm t n else 0‖ ≤
          Cμ * Real.sqrt M * (Real.log X) ^ (-K) := by
  have hαhalf : 0 < α / 2 := by positivity
  have hαhalf1 : α / 2 ≤ 1 := by nlinarith
  obtain ⟨Cμ, Xμ, hCμ, hXμ3, _, hMufAt⟩ :=
    hMUF hαhalf hαhalf1 hA hB hK
  let a₀ : ℝ := α / 2
  let c₀ : ℝ := (2 / a₀) * Real.log (logAbsorptionM a₀ B)
  let Xlog : ℝ := Real.exp c₀
  let X₀ : ℝ := max Xμ (max 3 Xlog)
  have hMabs : 1 ≤ logAbsorptionM a₀ B := one_le_logAbsorptionM
  have hc₀ : 0 ≤ c₀ := by
    dsimp [c₀, a₀]
    exact mul_nonneg (by positivity)
      (Real.log_nonneg (by nlinarith [hMabs]))
  have hX₀three : 3 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans (le_max_left 3 Xlog) (le_max_right Xμ (max 3 Xlog))
  refine ⟨Cμ, X₀, hCμ, hX₀three, ?_⟩
  intro X M hX₀X hMlow hMhigh q hq hqlog b hb t ht u v hu huv hv
  have hXμX : Xμ ≤ X := le_trans (le_max_left Xμ (max 3 Xlog)) hX₀X
  have hXlogX : Xlog ≤ X :=
    le_trans (le_trans (le_max_right 3 Xlog)
      (le_max_right Xμ (max 3 Xlog))) hX₀X
  have hXthree : 3 ≤ X := le_trans hX₀three hX₀X
  have hXone : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hc₀le : c₀ ≤ Real.log X := by
    calc
      c₀ = Real.log Xlog := by simp [Xlog, c₀]
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos c₀) hXlogX
  have hlarge :
      (2 / a₀) * Real.log (1 * logAbsorptionM a₀ B) ≤ Real.log X := by
    simpa using hc₀le
  have hlogHalf : (Real.log X) ^ B ≤ X ^ a₀ := by
    simpa using log_absorption_bound (by dsimp [a₀]; positivity) hB.le
      (by norm_num) hXone hlarge
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  let d : ℕ := Nat.gcd b q
  let Q : ℕ := q / d
  let b' : ℕ := b / d
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_right b hqpos
  have hdOne : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdpos)
  have hdq : d ∣ q := by dsimp [d]; exact Nat.gcd_dvd_right b q
  have hdb : d ∣ b := by dsimp [d]; exact Nat.gcd_dvd_left b q
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos
  have hQone : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hQpos)
  let dR : ℝ := d
  have hdRpos : 0 < dR := by dsimp [dR]; exact_mod_cast hdpos
  have hdRone : 1 ≤ dR := by dsimp [dR]; exact_mod_cast hdOne
  have hdleq : dR ≤ (q : ℝ) := by
    dsimp [dR]
    exact_mod_cast (Nat.le_of_dvd hqpos hdq)
  have hQleq : (Q : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.div_le_self q d)
  have hscaleLog : dR ≤ X ^ a₀ := le_trans hdleq (le_trans hqlog hlogHalf)
  have hLlow : X ^ a₀ ≤ M / dR := by
    apply (le_div_iff₀ hdRpos).2
    calc
      X ^ a₀ * dR ≤ X ^ a₀ * (X ^ a₀) :=
        mul_le_mul_of_nonneg_left hscaleLog (by positivity)
      _ = X ^ α := by
        rw [← Real.rpow_add hXpos]
        congr 1
        dsimp [a₀]
        ring
      _ ≤ M := hMlow
  have hLhigh : M / dR ≤ X := by
    apply (div_le_iff₀ hdRpos).2
    calc
      M ≤ X := hMhigh
      _ ≤ X * dR := by nlinarith [hXone, hdRone]
  have hqlogD : dR ≤ (Real.log X) ^ B := le_trans hdleq hqlog
  have hQlog : (Q : ℝ) ≤ (Real.log X) ^ B := le_trans hQleq hqlog
  have hQfactor : d * Q = q := by
    dsimp [Q]
    exact Nat.mul_div_cancel' hdq
  have hbFactor : d * b' = b := by
    dsimp [b']
    exact Nat.mul_div_cancel' hdb
  have hb'lt : b' < Q := by
    apply (Nat.mul_lt_mul_right hdpos).mp
    rw [Nat.div_mul_cancel hdb, Nat.div_mul_cancel hdq]
    exact hb
  have hcop : IsCoprime (b' : ℤ) (Q : ℤ) := by
    have hraw := residueGcdQuotientsCoprime (a := (b : ℤ)) (q := q) hqpos
    simpa [d, Q, b', Int.natAbs_natCast, Int.natCast_div] using hraw
  have hMpos : 0 < M := by
    have hpow : 0 < X ^ α := Real.rpow_pos_of_pos hXpos α
    linarith
  have hu0 : 0 ≤ u := le_trans hMpos.le hu
  let S : Finset ℕ := Finset.Ioc (Nat.floor (u / dR)) (Nat.floor (v / dR))
  let f : ℕ → ℂ := fun m => mobiusMellinResidueTerm t (d * m)
  have hscaleD :
      ‖(d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ *
          Real.sqrt (M / dR) ≤ Real.sqrt M :=
    mobiusResidueGcdScalar_bound hdpos hMpos.le hdRone t
  have hsumReindex :
      (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
        if n % q = b then mobiusMellinResidueTerm t n else 0) =
      ∑ m ∈ S, if m % Q = b' then f m else 0 := by
    simpa [S, f, d, Q, b', mobiusMellinResidueTerm] using
      (finiteResidueInterval_gcd_reindex
        (fun n => mobiusMellinResidueTerm t n) hqpos hb hu0 huv)
  letI : NeZero Q := ⟨Nat.ne_of_gt hQpos⟩
  have hresIndicator :
      (∑ m ∈ S, if m % Q = b' then f m else 0) =
        ∑ m ∈ S,
          if ((b' : ℤ) : ZMod Q) = ((m : ℤ) : ZMod Q) then f m else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    have hiff : m % Q = b' ↔
        ((b' : ℤ) : ZMod Q) = ((m : ℤ) : ZMod Q) := by
      constructor
      · intro hmres
        have hmod : m % Q = b' % Q := by
          rw [Nat.mod_eq_of_lt hb'lt]
          exact hmres
        have hcast : (m : ZMod Q) = (b' : ZMod Q) :=
          (ZMod.natCast_eq_natCast_iff' m b' Q).2 hmod
        simpa [Int.cast_natCast] using hcast.symm
      · intro hcast
        have hmod : b' % Q = m % Q :=
          (ZMod.natCast_eq_natCast_iff' b' m Q).1 (by
            simpa [Int.cast_natCast] using hcast)
        rw [Nat.mod_eq_of_lt hb'lt] at hmod
        omega
    by_cases hmres : m % Q = b'
    · rw [if_pos hmres, if_pos (hiff.mp hmres)]
    · have hcast : ((b' : ℤ) : ZMod Q) ≠ ((m : ℤ) : ZMod Q) := by
        intro h
        exact hmres (hiff.mpr h)
      rw [if_neg hmres, if_neg hcast]
  have haUnit : IsUnit (((b' : ℤ) : ZMod Q)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime (b' : ℤ) Q).2 (isCoprime_comm.mpr hcop)
  have hCharacterAverage :=
    FractionalPrimes.Literature.MobiusToLong.finiteResidueSum_eq_character_average
      hQpos (b' : ℤ) hcop S f
  have haverage :
      (∑ m ∈ S, if m % Q = b' then f m else 0) =
        (∑ χ : BlueprintCharacter Q,
          star (evalInt χ (b' : ℤ)) *
            ∑ m ∈ S, f m * evalInt χ (m : ℤ)) / (Q.totient : ℂ) := by
    rw [hresIndicator]
    exact hCharacterAverage
  have hlogPos : 0 < Real.log X := Real.log_pos (by linarith [hXthree])
  have hpowPos : 0 < (Real.log X) ^ (-K : ℝ) :=
    Real.rpow_pos_of_pos hlogPos _
  have hsumBound (χ : BlueprintCharacter Q) :
      ‖∑ m ∈ S, f m * evalInt χ (m : ℤ)‖ ≤
        Cμ * Real.sqrt M * (Real.log X) ^ (-K) := by
    have hd1 : 1 ≤ d := hdOne
    have hAt := hMufAt (q := Q) (X := X) (L := M / dR)
      hXμX hLlow hLhigh hQone hQlog d hd1 hqlogD χ t ht
      (u := u / dR) (v := v / dR)
      (div_le_div_of_nonneg_right hu hdRpos.le)
      (div_le_div_of_nonneg_right huv hdRpos.le)
      (by
        have h := div_le_div_of_nonneg_right hv hdRpos.le
        calc
          v / dR ≤ (2 * M) / dR := h
          _ = 2 * (M / dR) := by ring)
    have hS : S = Finset.Ioc
        (Nat.floor (u / dR)) (Nat.floor (v / dR)) := rfl
    have hterm {m : ℕ} (hmpos : 0 < m) :
        f m * evalInt χ (m : ℤ) =
          (d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
            (twistedMobiusRectangleCoefficient d χ t m *
              inverseSqrtWeight (m : ℝ)) := by
      simp only [f, mobiusMellinResidueTerm, evalInt, Int.cast_natCast]
      rw [positiveNatCpow_mul hdpos hmpos
        (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))]
      have hcoeff := mobiusHighHeightFactorCoefficient_eq
        (q := Q) d χ t hmpos
      calc
        (ArithmeticFunction.moebius (d * m) : ℂ) *
            ((d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
              (m : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) *
            χ (m : ZMod Q) =
          (d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
            ((ArithmeticFunction.moebius (d * m) : ℂ) * χ (m : ZMod Q) *
              (m : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) := by ring
        _ = (d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
            (twistedMobiusRectangleCoefficient d χ t m *
              inverseSqrtWeight (m : ℝ)) := by rw [← hcoeff]
    have hsumEq :
        (∑ m ∈ S, f m * evalInt χ (m : ℤ)) =
          (d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
            ∑ m ∈ S,
              twistedMobiusRectangleCoefficient d χ t m *
                inverseSqrtWeight (m : ℝ) := by
      calc
        (∑ m ∈ S, f m * evalInt χ (m : ℤ)) =
            ∑ m ∈ S,
              (d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
                (twistedMobiusRectangleCoefficient d χ t m *
                  inverseSqrtWeight (m : ℝ)) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hmI := Finset.mem_Ioc.mp (by simpa [S] using hm)
          have hMdivPos : 0 < M / dR := div_pos hMpos hdRpos
          have huDiv : 0 ≤ u / dR := div_nonneg hu0 hdRpos.le
          have huDivPos : 0 < u / dR := lt_of_lt_of_le hMdivPos
            (div_le_div_of_nonneg_right hu hdRpos.le)
          have hmR : u / dR < (m : ℝ) := (Nat.floor_lt huDiv).1 hmI.1
          have hmpos : 0 < m := by
            exact_mod_cast (lt_trans huDivPos hmR)
          exact hterm hmpos
        _ = (d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
            ∑ m ∈ S,
              twistedMobiusRectangleCoefficient d χ t m *
                inverseSqrtWeight (m : ℝ) := by rw [Finset.mul_sum]
    rw [hsumEq]
    calc
      ‖(d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
          ∑ m ∈ S,
            twistedMobiusRectangleCoefficient d χ t m *
              inverseSqrtWeight (m : ℝ)‖ =
        ‖(d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ *
          ‖∑ m ∈ S,
            twistedMobiusRectangleCoefficient d χ t m *
              inverseSqrtWeight (m : ℝ)‖ := norm_mul _ _
      _ ≤ ‖(d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ *
          (Cμ * Real.sqrt (M / dR) * (Real.log X) ^ (-K)) :=
        mul_le_mul_of_nonneg_left hAt (norm_nonneg _)
      _ ≤ Cμ * Real.sqrt M * (Real.log X) ^ (-K) := by
        calc
          _ = (‖(d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ *
                Real.sqrt (M / dR)) * (Cμ * (Real.log X) ^ (-K)) := by ring
          _ ≤ Real.sqrt M * (Cμ * (Real.log X) ^ (-K)) :=
            mul_le_mul_of_nonneg_right hscaleD (by positivity)
          _ = Cμ * Real.sqrt M * (Real.log X) ^ (-K) := by ring
  have hnormClass (χ : BlueprintCharacter Q) :
      ‖evalInt χ (b' : ℤ)‖ = 1 := by
    simpa [evalInt] using unit_value_norm χ haUnit
  rw [hsumReindex, haverage, norm_div, Complex.norm_natCast]
  have hφposNat : 0 < Q.totient := Nat.totient_pos.mpr hQpos
  have hφpos : 0 < (Q.totient : ℝ) := by exact_mod_cast hφposNat
  apply (div_le_iff₀ hφpos).2
  calc
    ‖∑ χ : BlueprintCharacter Q,
        star (evalInt χ (b' : ℤ)) *
          ∑ m ∈ S, f m * evalInt χ (m : ℤ)‖ ≤
      ∑ χ : BlueprintCharacter Q,
        ‖star (evalInt χ (b' : ℤ)) *
          ∑ m ∈ S, f m * evalInt χ (m : ℤ)‖ := norm_sum_le _ _
    _ ≤ ∑ _χ : BlueprintCharacter Q,
        Cμ * Real.sqrt M * (Real.log X) ^ (-K) := by
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul, norm_star, hnormClass χ, one_mul]
      exact hsumBound χ
    _ = (Q.totient : ℝ) * (Cμ * Real.sqrt M * (Real.log X) ^ (-K)) := by
      simp [BlueprintCharacter, blueprintCharacters_card]
    _ = Cμ * Real.sqrt M * (Real.log X) ^ (-K) * (Q.totient : ℝ) := by ring

end FractionalPrimes.Literature.Twisted

#print axioms FractionalPrimes.Literature.Twisted.mobiusResidueFromFactorGoal
