module
public import FractionalPrimes.Literature.Reciprocal.GlobalCharacterMobius
public import FractionalPrimes.Literature.Twisted.PeriodicLogPhaseDirichletBound
public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter
public import FractionalPrimes.Literature.Twisted.CharacterEvalNorm
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import FractionalPrimes.Literature.Uniformity.ElementaryGrowthPackage
@[expose] public section

set_option maxHeartbeats 1000000

@[expose] public section

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius
open FractionalPrimes.Literature.Reciprocal

namespace FractionalPrimes.Literature.Twisted

/-- The three original factors in the original-factor blueprint lemma. -/
inductive OriginalLongFactorWeight
  | one
  | logarithm
  | mobius
  deriving DecidableEq

/-- Coefficients for the exact 1, log, and μ alternatives. -/
noncomputable def OriginalLongFactorWeight.coeff
    (u : OriginalLongFactorWeight) (n : ℕ) : ℂ :=
  match u with
  | .one => 1
  | .logarithm => (Real.log (n : ℝ) : ℂ)
  | .mobius => (ArithmeticFunction.moebius n : ℂ)

/-- Induce a Dirichlet character from modulus q to a multiple R, by
pulling its unit-circle character back along the reduction map on units. -/
noncomputable def inducedBlueprintCharacter
    {q R : ℕ} [NeZero q] [NeZero R] (hqr : q ∣ R)
    (χ : BlueprintCharacter q) : BlueprintCharacter R :=
  ofUnitCircleCharacter
    ((toUnitCircleCharacter χ).comp (ZMod.unitsMap hqr))

theorem inducedBlueprintCharacter_eval_eq_of_coprime
    {q R : ℕ} [NeZero q] [NeZero R] (hqr : q ∣ R)
    (χ : BlueprintCharacter q) {n : ℕ} (hn : Nat.Coprime n R) :
    evalInt (inducedBlueprintCharacter hqr χ) (n : ℤ) =
      evalInt χ (n : ℤ) := by
  let uR : (ZMod R)ˣ := ZMod.unitOfCoprime n hn
  have huR : (uR : ZMod R) = (n : ZMod R) := by
    simp [uR]
  have huQ :
      (ZMod.unitsMap hqr uR : ZMod q) = (n : ZMod q) := by
    change ZMod.castHom hqr (ZMod q) (uR : ZMod R) = _
    rw [huR]
    simp
  simp only [evalInt, Int.cast_natCast]
  change (inducedBlueprintCharacter hqr χ) (n : ZMod R) =
    χ (n : ZMod q)
  rw [← huR]
  change (MulChar.ofUnitHom
      (Circle.toUnits.comp
        ((toUnitCircleCharacter χ).comp (ZMod.unitsMap hqr))) uR : ℂ) =
    χ (n : ZMod q)
  rw [MulChar.ofUnitHom_coe]
  calc
    (Circle.toUnits
        (toUnitCircleCharacter χ (ZMod.unitsMap hqr uR)) : ℂ) =
      (toUnitCircleCharacter χ (ZMod.unitsMap hqr uR) : ℂ) :=
        unitSphereToUnits_apply_coe _
    _ = χ (n : ZMod q) := by
      change χ (ZMod.unitsMap hqr uR : ZMod q) = _
      rw [huQ]

theorem inducedBlueprintCharacter_eval_eq_zero_of_not_coprime
    {q R : ℕ} [NeZero q] [NeZero R] (hqr : q ∣ R)
    (χ : BlueprintCharacter q) {n : ℕ} (hn : ¬ Nat.Coprime n R) :
    evalInt (inducedBlueprintCharacter hqr χ) (n : ℤ) = 0 := by
  apply evalInt_eq_zero_of_not_coprime
  intro hcop
  exact hn (Nat.isCoprime_iff_coprime.mp hcop)

/-- The character induced to `lcm(q,p)` incorporates exactly the coprimality
cutoff at `p`. -/
theorem inducedLcmCharacter_eval_eq_cutoff
    {q p : ℕ} [NeZero q] [NeZero p] [NeZero (Nat.lcm q p)]
    (χ : BlueprintCharacter q) (n : ℕ) :
    evalInt (inducedBlueprintCharacter (Nat.dvd_lcm_left q p) χ) (n : ℤ) =
      evalInt χ (n : ℤ) * (if Nat.Coprime n p then 1 else 0) := by
  by_cases hp : Nat.Coprime n p
  · by_cases hq : Nat.Coprime n q
    · have hR : Nat.Coprime n (Nat.lcm q p) := by
        apply (Nat.Coprime.mul_right hq hp).of_dvd_right
        exact Nat.lcm_dvd (dvd_mul_right q p) (dvd_mul_left p q)
      rw [if_pos hp, mul_one]
      exact inducedBlueprintCharacter_eval_eq_of_coprime
        (Nat.dvd_lcm_left q p) χ hR
    · have hR : ¬ Nat.Coprime n (Nat.lcm q p) := by
        intro h
        exact hq ((Nat.Coprime.of_dvd_right (Nat.dvd_lcm_left q p)) h)
      rw [if_pos hp, inducedBlueprintCharacter_eval_eq_zero_of_not_coprime
        (Nat.dvd_lcm_left q p) χ hR]
      have hχ : evalInt χ (n : ℤ) = 0 := by
        apply evalInt_eq_zero_of_not_coprime
        exact fun h => hq (Nat.isCoprime_iff_coprime.mp h)
      rw [hχ]
      simp
  · have hR : ¬ Nat.Coprime n (Nat.lcm q p) := by
      intro h
      exact hp ((Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right q p)) h)
    rw [if_neg hp, mul_zero,
      inducedBlueprintCharacter_eval_eq_zero_of_not_coprime
        (Nat.dvd_lcm_left q p) χ hR]

/-- The natural interval `(x,y]` is the cast of the exact integer interval
used by the periodic Dirichlet estimate. -/
theorem realIntegerInterval_eq_nat_Ioc_map
    {x y : ℝ} (hx : 0 ≤ x) :
    FractionalPrimes.realIntegerInterval x (y - x) =
      (Finset.Ioc (Nat.floor x) (Nat.floor y)).map Nat.castEmbedding := by
  classical
  ext n
  rw [FractionalPrimes.mem_realIntegerInterval_iff]
  simp only [Finset.mem_map, Finset.mem_Ioc]
  constructor
  · rintro ⟨hxn, hny⟩
    have hnpos : 0 < n := by
      have hnposreal : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt hx hxn
      exact_mod_cast hnposreal
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hnpos)
    refine ⟨n.toNat, ?_, ?_⟩
    · have hnatcastreal : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hncast
      constructor
      · exact (Nat.floor_lt hx).mpr (by rw [hnatcastreal]; exact hxn)
      · have hupper : (n.toNat : ℝ) ≤ y := by
          have hny' : (n : ℝ) ≤ y := by linarith
          rw [hnatcastreal]
          exact hny'
        exact Nat.le_floor hupper
    · simpa using hncast
  · rintro ⟨m, hm, hmn⟩
    have hcast : (m : ℝ) = (n : ℝ) := by exact_mod_cast hmn
    constructor
    · have hxlt : x < (m : ℝ) :=
        (Nat.floor_lt hx).mp hm.1
      simpa [hcast] using hxlt
    · have hmpos : 0 < m := by
        have hfloorx : 0 ≤ Nat.floor x := Nat.zero_le _
        omega
      have hfloorYpos : 1 ≤ Nat.floor y := by omega
      have hyone : (1 : ℝ) ≤ y := (Nat.one_le_floor_iff y).mp hfloorYpos
      have hmy : (m : ℝ) ≤ y := by
        calc
          (m : ℝ) ≤ (Nat.floor y : ℝ) := by exact_mod_cast hm.2
          _ ≤ y := Nat.floor_le (le_trans (by norm_num : (0 : ℝ) ≤ 1) hyone)
      have hny : (n : ℝ) ≤ y := by simpa [hcast] using hmy
      linarith

/-- The exact coefficient `u(rm) χ(m) 1_{(m,p)=1} m^(-1/2-is)` in the
original-factor statement. -/
noncomputable def originalLongFactorCoefficient
    (u : OriginalLongFactorWeight) (r p : ℕ)
    {Q : ℕ} (χ : BlueprintCharacter Q) (s : ℝ) (m : ℕ) : ℂ :=
  u.coeff (r * m) * evalInt χ (m : ℤ) *
    (if Nat.Coprime m p then 1 else 0) *
      (m : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ))

private noncomputable def originalLongFactorIntCoefficient
    (u : OriginalLongFactorWeight) (r p : ℕ)
    {Q : ℕ} (χ : BlueprintCharacter Q) (s : ℝ) (n : ℤ) : ℂ :=
  u.coeff (r * n.toNat) * evalInt χ n *
    (if Nat.Coprime n.toNat p then 1 else 0) *
      (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ))

/-- Reindex the natural sum on `(x,y]` to the integer interval used by the
periodic estimate. -/
private theorem originalLongFactorSum_reindex
    {x y : ℝ} (hx : 0 ≤ x) (u : OriginalLongFactorWeight)
    (r p : ℕ) {Q : ℕ} (χ : BlueprintCharacter Q) (s : ℝ) :
    (∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
      originalLongFactorCoefficient u r p χ s m) =
      ∑ n ∈ FractionalPrimes.realIntegerInterval x (y - x),
        originalLongFactorIntCoefficient u r p χ s n := by
  classical
  calc
    _ = ∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
        originalLongFactorIntCoefficient u r p χ s (m : ℤ) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp [originalLongFactorCoefficient, originalLongFactorIntCoefficient]
    _ = ∑ n ∈ FractionalPrimes.realIntegerInterval x (y - x),
        originalLongFactorIntCoefficient u r p χ s n := by
      rw [realIntegerInterval_eq_nat_Ioc_map hx, Finset.sum_map]
      simp only [Nat.castEmbedding_apply]

/-- Thresholds supplied by the explicit logarithmic absorption lemma. -/
noncomputable def originalLongFactorAbsorptionThreshold
    (d b K : ℝ) : ℝ :=
  Real.exp ((2 / d) * Real.log (K *
    FractionalPrimes.Literature.Uniformity.logAbsorptionM d b))

private theorem originalLongFactor_absorption_of_threshold
    {d b K X X₀ : ℝ} (hd : 0 < d) (hb : 0 ≤ b) (hK : 1 ≤ K)
    (hX₀3 : 3 ≤ X₀)
    (hX₀ : originalLongFactorAbsorptionThreshold d b K ≤ X₀)
    (hX₀X : X₀ ≤ X) :
    K * (Real.log X) ^ b ≤ X ^ d := by
  have hExpX :
      Real.exp ((2 / d) * Real.log (K *
        FractionalPrimes.Literature.Uniformity.logAbsorptionM d b)) ≤ X :=
    hX₀.trans hX₀X
  have hXone : 1 ≤ X := le_trans (by norm_num) (hX₀3.trans hX₀X)
  have hlarge : (2 / d) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM d b) ≤ Real.log X := by
    rw [← Real.log_exp ((2 / d) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM d b))]
    exact Real.log_le_log (Real.exp_pos _) hExpX
  exact FractionalPrimes.Literature.Uniformity.log_absorption_bound
    hd hb hK hXone hlarge

/-- The complex power splits into the exact inverse-square-root and twist
factors appearing in `MobiusUniformityAt`. -/
private theorem originalLongFactor_cpow_split
    {m : ℕ} (hm : 0 < m) (s : ℝ) :
    (m : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ)) =
      inverseSqrtWeight (m : ℝ) * (m : ℂ) ^ (-((s : ℂ) * Complex.I)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hhalf : (m : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((Real.rpow (m : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    have hleft : (m : ℂ) ^ (-(1 / 2 : ℂ)) =
        Complex.exp ((-(1 / 2 : ℂ)) * (Real.log (m : ℝ) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero hmC, Complex.ofReal_log hmR.le]
      congr 1
      push_cast
      ring
    have hright : ((Real.rpow (m : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        Complex.exp ((-(1 / 2 : ℂ)) * (Real.log (m : ℝ) : ℂ)) := by
      have hrpow := Real.rpow_def_of_pos hmR (-(1 / 2 : ℝ))
      calc
        _ = ((Real.exp (Real.log (m : ℝ) * (-(1 / 2 : ℝ))) : ℝ) : ℂ) :=
          congrArg Complex.ofReal hrpow
        _ = Complex.exp ((-(1 / 2 : ℂ)) * (Real.log (m : ℝ) : ℂ)) := by
          rw [Complex.ofReal_exp]
          congr 1
          push_cast
          ring
    exact hleft.trans hright.symm
  have htwist : (m : ℂ) ^ (-((s : ℂ) * Complex.I)) =
      Complex.exp ((-Complex.I * (s : ℂ)) * (Real.log (m : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hmC, Complex.ofReal_log hmR.le]
    congr 1
    push_cast
    ring
  rw [show (-(1 / 2 : ℂ)) - Complex.I * (s : ℂ) =
      (-(1 / 2 : ℂ)) + (-((s : ℂ) * Complex.I)) by ring,
    Complex.cpow_add _ _ hmC, hhalf, inverseSqrtWeight, htwist]
  norm_num

/-- A complex character is periodic modulo its level under integer
reduction. -/
private theorem evalInt_mod_period
    {q : ℕ} [NeZero q] (χ : BlueprintCharacter q) (n : ℤ) :
    evalInt χ (n % (q : ℤ)) = evalInt χ n := by
  change χ (n % (q : ℤ) : ZMod q) = χ (n : ZMod q)
  congr 1
  exact (ZMod.intCast_eq_intCast_iff _ _ q).2 (Int.mod_modEq n (q : ℤ))

private theorem inducedLcmCharacter_eval_eq_cutoff_int
    {q p : ℕ} [NeZero q] [NeZero p] [NeZero (Nat.lcm q p)]
    (χ : BlueprintCharacter q) {n : ℤ} (hn : 0 ≤ n) :
    evalInt (inducedBlueprintCharacter (Nat.dvd_lcm_left q p) χ) n =
      evalInt χ n * (if Nat.Coprime n.toNat p then 1 else 0) := by
  have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  simpa [hcast] using inducedLcmCharacter_eval_eq_cutoff χ n.toNat

private theorem originalLongFactorMobiusCoefficient_eq
    {q p r m : ℕ} [NeZero q] [NeZero p] [NeZero (Nat.lcm q p)]
    (χ : BlueprintCharacter q) (s : ℝ) (hm : 0 < m) :
    originalLongFactorCoefficient .mobius r p χ s m =
      FractionalPrimes.Literature.Reciprocal.twistedMobiusRectangleCoefficient
          r (inducedBlueprintCharacter (Nat.dvd_lcm_left q p) χ) s m *
        inverseSqrtWeight (m : ℝ) := by
  have hchar := inducedLcmCharacter_eval_eq_cutoff (q := q) (p := p) χ m
  have hpow := originalLongFactor_cpow_split hm s
  simp only [originalLongFactorCoefficient, OriginalLongFactorWeight.coeff]
  calc
    _ = (ArithmeticFunction.moebius (r * m) : ℂ) *
          (evalInt χ (m : ℤ) * (if Nat.Coprime m p then 1 else 0)) *
          ((m : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ))) := by ring
    _ = (ArithmeticFunction.moebius (r * m) : ℂ) *
          evalInt (inducedBlueprintCharacter (Nat.dvd_lcm_left q p) χ) (m : ℤ) *
          ((m : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ))) := by rw [← hchar]
    _ = FractionalPrimes.Literature.Reciprocal.twistedMobiusRectangleCoefficient
          r (inducedBlueprintCharacter (Nat.dvd_lcm_left q p) χ) s m *
        inverseSqrtWeight (m : ℝ) := by
      rw [FractionalPrimes.Literature.Reciprocal.twistedMobiusRectangleCoefficient,
        FractionalPrimes.Literature.LongArithmetic.shiftedCharacterMobiusCoefficient,
        FractionalPrimes.Literature.LongArithmetic.mobiusMultiplierCoefficient,
        FractionalPrimes.Literature.LongArithmetic.dirichletCharacterNatHom_apply_of_ne_zero
          _ hm.ne']
      calc
        _ = (ArithmeticFunction.moebius (r * m) : ℂ) *
              evalInt (inducedBlueprintCharacter (Nat.dvd_lcm_left q p) χ)
                (m : ℤ) *
              (inverseSqrtWeight (m : ℝ) *
                (m : ℂ) ^ (-((s : ℂ) * Complex.I))) := by rw [hpow]
        _ = _ := by
          simp only [evalInt, Int.cast_natCast]
          ring

/-- The exact finite-interval form of the original-factor conclusion. Each
`z` imposes the optional upper cutoff `rm ≤ z`; taking `z` beyond `r*y`
recovers every interval without that extra cutoff. -/
def OriginalLongFactorAt (X N s a : ℝ) : Prop :=
  let ell := Real.log X
  ∀ (r p Q : ℕ) (χ : BlueprintCharacter Q),
    1 ≤ r → (r : ℝ) ≤ ell ^ a →
    1 ≤ p → (p : ℝ) ≤ ell ^ a →
    1 ≤ Q → (Q : ℝ) ≤ ell ^ a →
    ell ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
    ∀ (u : OriginalLongFactorWeight) (x y z : ℝ),
      N / (r : ℝ) ≤ x → x ≤ y → y ≤ 2 * (N / (r : ℝ)) →
      ‖∑ m ∈ Finset.Ioc (Nat.floor x)
          (Nat.floor (min y (z / (r : ℝ)))),
        originalLongFactorCoefficient u r p χ s m‖ ≤
        ell ^ (-21 * a) * Real.sqrt (N / (r : ℝ))

/-- The exact `ltw:original-factor` implication. It preserves the three
original weights, every displayed parameter range, and the independent
upper truncation `r*m ≤ z`. -/
theorem originalLongFactorOfMobiusGoal
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a : ℝ} (ha : 2 ≤ a) :
    ∃ Xfac : ℝ, 3 ≤ Xfac ∧
      ∀ {X N s : ℝ}, Xfac ≤ X →
        (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) ≤ N →
        N ≤ (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) →
        OriginalLongFactorAt X N s a := by
  let alpha : ℝ := 1 / 160
  let A : ℝ := a + 1
  let B : ℝ := 2 * a
  let D : ℝ := 22 * a
  have hα : 0 < alpha := by norm_num [alpha]
  have hα1 : alpha ≤ 1 := by norm_num [alpha]
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨Cμ, Xμ, hCμ, hXμ, _hMufLog, hMufAt⟩ :=
    hMUF hα hα1 hA hB hD
  let delta : ℝ := periodicLogPhaseSaving alpha A
  let Cphase : ℝ := periodicLogPhaseConstant alpha A
  have hdelta : 0 < delta := by
    dsimp [delta, periodicLogPhaseSaving, alpha, A]
    positivity
  have hCphase : 0 < Cphase := by
    have hbound := periodicLogPhaseConstant_ge_order alpha A
    have horder : 0 ≤ (periodicLogPhaseOrder alpha A : ℝ) := Nat.cast_nonneg _
    dsimp [Cphase]
    linarith
  let tScale := originalLongFactorAbsorptionThreshold
    (1 / 160 : ℝ) a (2 ^ 23 : ℝ)
  let tMod := originalLongFactorAbsorptionThreshold
    (1 / 320 : ℝ) (2 * a) 1
  let tError := originalLongFactorAbsorptionThreshold delta (22 * a) 1
  let tUpper := originalLongFactorAbsorptionThreshold
    (5 / 8 : ℝ) 0 (2 ^ 23 : ℝ)
  let tLog := Real.exp 1
  let tMobius := Real.exp Cμ
  let tPhase := Real.exp (16 * Cphase)
  let Xfac := 3 + Xμ + tScale + tMod + tError + tUpper + tLog + tMobius + tPhase
  have htScale : 0 < tScale := by dsimp [tScale, originalLongFactorAbsorptionThreshold]; exact Real.exp_pos _
  have htMod : 0 < tMod := by dsimp [tMod, originalLongFactorAbsorptionThreshold]; exact Real.exp_pos _
  have htError : 0 < tError := by dsimp [tError, originalLongFactorAbsorptionThreshold]; exact Real.exp_pos _
  have htUpper : 0 < tUpper := by dsimp [tUpper, originalLongFactorAbsorptionThreshold]; exact Real.exp_pos _
  have htLog : 0 < tLog := by dsimp [tLog]; exact Real.exp_pos _
  have htMobius : 0 < tMobius := by dsimp [tMobius]; exact Real.exp_pos _
  have htPhase : 0 < tPhase := by dsimp [tPhase]; exact Real.exp_pos _
  have hXfac3 : 3 ≤ Xfac := by dsimp [Xfac]; linarith [hXμ, htScale, htMod, htError, htUpper, htLog, htMobius, htPhase]
  have hXμfac : Xμ ≤ Xfac := by dsimp [Xfac]; linarith [htScale, htMod, htError, htUpper, htLog, htMobius, htPhase]
  have htScaleFac : tScale ≤ Xfac := by dsimp [Xfac]; linarith [hXμ, htMod, htError, htUpper, htLog, htMobius, htPhase]
  have htModFac : tMod ≤ Xfac := by dsimp [Xfac]; linarith [hXμ, htScale, htError, htUpper, htLog, htMobius, htPhase]
  have htErrorFac : tError ≤ Xfac := by dsimp [Xfac]; linarith [hXμ, htScale, htMod, htUpper, htLog, htMobius, htPhase]
  have htUpperFac : tUpper ≤ Xfac := by dsimp [Xfac]; linarith [hXμ, htScale, htMod, htError, htLog, htMobius, htPhase]
  have htLogFac : tLog ≤ Xfac := by dsimp [Xfac]; linarith [hXμ, htScale, htMod, htError, htUpper, htMobius, htPhase]
  have htMobiusFac : tMobius ≤ Xfac := by dsimp [Xfac]; linarith [hXμ, htScale, htMod, htError, htUpper, htLog, htPhase]
  have htPhaseFac : tPhase ≤ Xfac := by dsimp [Xfac]; linarith [hXμ, htScale, htMod, htError, htUpper, htLog, htMobius]
  refine ⟨Xfac, hXfac3, ?_⟩
  intro X N s hXfacX hNlow hNhigh
  have hX3 : 3 ≤ X := hXfac3.trans hXfacX
  have hXone : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  let ell : ℝ := Real.log X
  have hExp1 : Real.exp 1 ≤ X := by
    exact (show tLog ≤ Xfac from htLogFac).trans hXfacX
  have hellone : 1 ≤ ell := by
    dsimp [ell]
    exact (Real.le_log_iff_exp_le hXpos).2 hExp1
  have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hellone
  have hExpCμ : Real.exp Cμ ≤ X := by
    exact (show tMobius ≤ Xfac from htMobiusFac).trans hXfacX
  have hCμell : Cμ ≤ ell := by
    dsimp [ell]
    exact (Real.le_log_iff_exp_le hXpos).2 hExpCμ
  have hCμpow : Cμ ≤ ell ^ a := by
    have hpow : 1 ≤ ell ^ (a - 1) := Real.one_le_rpow hellone (by linarith)
    have hfactor : ell ^ a = ell * ell ^ (a - 1) := by
      rw [show a = (a - 1) + 1 by ring, Real.rpow_add hellpos, Real.rpow_one]
      ring
    calc
      Cμ ≤ ell := hCμell
      _ ≤ ell * ell ^ (a - 1) := by
        nlinarith [mul_nonneg (le_of_lt hellpos) (sub_nonneg.mpr hpow)]
      _ = ell ^ a := hfactor.symm
  have hExpPhase : Real.exp (16 * Cphase) ≤ X := by
    exact (show tPhase ≤ Xfac from htPhaseFac).trans hXfacX
  have hCphaseell : 16 * Cphase ≤ ell := by
    dsimp [ell]
    exact (Real.le_log_iff_exp_le hXpos).2 hExpPhase
  have hScale : (2 ^ 23 : ℝ) * ell ^ a ≤ X ^ alpha := by
    exact originalLongFactor_absorption_of_threshold
      (d := 1 / 160) (b := a) (K := 2 ^ 23) (X₀ := Xfac)
      (by norm_num) (by linarith [ha]) (by norm_num) hXfac3 htScaleFac hXfacX
  have hMod : ell ^ (2 * a) ≤ X ^ (1 / 320 : ℝ) := by
    simpa [ell] using originalLongFactor_absorption_of_threshold
      (d := 1 / 320) (b := 2 * a) (K := 1) (X₀ := Xfac)
      (by norm_num) (by positivity) (by norm_num) hXfac3 htModFac hXfacX
  have hError : ell ^ (22 * a) ≤ X ^ delta := by
    simpa [ell] using originalLongFactor_absorption_of_threshold
      (d := delta) (b := 22 * a) (K := 1) (X₀ := Xfac)
      hdelta (by positivity) (by norm_num) hXfac3 htErrorFac hXfacX
  have hUpper : (2 ^ 23 : ℝ) ≤ X ^ (5 / 8 : ℝ) := by
    simpa using originalLongFactor_absorption_of_threshold
      (d := 5 / 8) (b := 0) (K := 2 ^ 23) (X₀ := Xfac)
      (by norm_num) (by norm_num) (by norm_num) hXfac3 htUpperFac hXfacX
  have hLupperCoeff : (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) ≤ X := by
    have hpow : X ^ (5 / 8 : ℝ) * X ^ (3 / 8 : ℝ) = X := by
      rw [← Real.rpow_add hXpos]
      congr 1
      norm_num
    calc
      (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) ≤
          X ^ (5 / 8 : ℝ) * X ^ (3 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hUpper (Real.rpow_nonneg hXpos.le _)
      _ = X := hpow
  have hNpos : 0 < N := by
    have hpow : 0 < X ^ (1 / 80 : ℝ) := Real.rpow_pos_of_pos hXpos _
    have hprod : 0 < (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) :=
      mul_pos (by positivity) hpow
    exact lt_of_lt_of_le hprod hNlow
  have hrweight_bound (r : ℕ) (hr : 1 ≤ r) (hrX : (r : ℝ) ≤ ell ^ a) :
      (r : ℝ) ≤ ell ^ (2 * a) := by
    calc
      (r : ℝ) ≤ ell ^ a := hrX
      _ ≤ ell ^ (2 * a) :=
        Real.rpow_le_rpow_of_exponent_le hellone (by linarith [ha])
  have hCstarR {r : ℕ} (hrX : (r : ℝ) ≤ ell ^ a) :
      (2 ^ 23 : ℝ) * r ≤ X ^ alpha := by
    calc
      (2 ^ 23 : ℝ) * r ≤ (2 ^ 23 : ℝ) * ell ^ a :=
        mul_le_mul_of_nonneg_left hrX (by positivity)
      _ ≤ X ^ alpha := hScale
  have hLowerLength {r : ℕ} (hr : 1 ≤ r) (hrX : (r : ℝ) ≤ ell ^ a) :
      X ^ alpha ≤ N / r := by
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hr)
    have hpowtwice : X ^ alpha * X ^ alpha = X ^ (1 / 80 : ℝ) := by
      rw [← Real.rpow_add hXpos]
      congr 1
      dsimp [alpha]
      norm_num
    have hprod : (2 ^ 23 : ℝ) * r * X ^ alpha ≤ X ^ (1 / 80 : ℝ) := by
      calc
        (2 ^ 23 : ℝ) * r * X ^ alpha ≤ X ^ alpha * X ^ alpha :=
          mul_le_mul_of_nonneg_right (hCstarR hrX) (Real.rpow_nonneg hXpos.le _)
        _ = X ^ (1 / 80 : ℝ) := hpowtwice
    have hNscaled' : X ^ (1 / 80 : ℝ) ≤ N * (2 ^ 23 : ℝ) := by
      have hdiv : X ^ (1 / 80 : ℝ) / (2 ^ 23 : ℝ) ≤ N := by
        simpa [div_eq_mul_inv, mul_comm] using hNlow
      exact (div_le_iff₀ (by positivity : 0 < (2 ^ 23 : ℝ))).mp hdiv
    have hNscaled : X ^ (1 / 80 : ℝ) ≤ (2 ^ 23 : ℝ) * N := by
      simpa [mul_comm] using hNscaled'
    have hcancel : (2 ^ 23 : ℝ) * (r * X ^ alpha) ≤
        (2 ^ 23 : ℝ) * N := by
      calc
        (2 ^ 23 : ℝ) * (r * X ^ alpha) = (2 ^ 23 : ℝ) * r * X ^ alpha := by ring
        _ ≤ X ^ (1 / 80 : ℝ) := hprod
        _ ≤ (2 ^ 23 : ℝ) * N := hNscaled
    have hrN : r * X ^ alpha ≤ N :=
      (mul_le_mul_iff_of_pos_left (by positivity : 0 < (2 ^ 23 : ℝ))).mp hcancel
    apply (le_div_iff₀ hrpos).2
    simpa [mul_comm] using hrN
  have hLengthUpper {r : ℕ} (hr : 1 ≤ r) (hrN : 0 ≤ N) :
      N / r ≤ X := by
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hr)
    have hdiv : N / r ≤ N := by
      have hrReal : 1 ≤ (r : ℝ) := by exact_mod_cast hr
      have hprod : N ≤ N * r := by
        calc
          N = N * 1 := by ring
          _ ≤ N * r := mul_le_mul_of_nonneg_left hrReal hrN
      exact (div_le_iff₀ hrpos).2 (by simpa [mul_comm] using hprod)
    exact hdiv.trans (hNhigh.trans hLupperCoeff)
  have hXμX : Xμ ≤ X := hXμfac.trans hXfacX
  dsimp [OriginalLongFactorAt]
  intro r p Q χ hr hrX hp hpX hQ hQX hsmin hsmax u x y z hx hxy hy
  let R : ℕ := Nat.lcm Q p
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hppos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  letI : NeZero Q := ⟨Nat.ne_of_gt hQpos⟩
  letI : NeZero p := ⟨Nat.ne_of_gt hppos⟩
  have hRpos : 0 < R := lt_of_lt_of_le hQpos (Nat.le_lcm_left Q hppos)
  letI : NeZero R := ⟨Nat.ne_of_gt hRpos⟩
  have hRdiv : R ≤ Q * p := by
    exact Nat.le_of_dvd (Nat.mul_pos hQpos hppos)
      (Nat.lcm_dvd (dvd_mul_right Q p) (dvd_mul_left p Q))
  have hRbound : (R : ℝ) ≤ ell ^ (2 * a) := by
    calc
      (R : ℝ) ≤ (Q * p : ℕ) := by exact_mod_cast hRdiv
      _ = (Q : ℝ) * (p : ℝ) := by norm_num
      _ ≤ ell ^ a * ell ^ a :=
        mul_le_mul hQX hpX (by positivity) (by positivity)
      _ = ell ^ (2 * a) := by
        rw [← Real.rpow_add hellpos]
        congr 1
        ring
  have hRperiod : (R : ℝ) ≤ X ^ (alpha / 2) := by
    have hmod' : ell ^ (2 * a) ≤ X ^ (alpha / 2) := by
      rw [show alpha / 2 = (1 / 320 : ℝ) by norm_num [alpha]]
      exact hMod
    exact hRbound.trans hmod'
  have hrbound := hrweight_bound r hr hrX
  have hLlower := hLowerLength hr hrX
  have hLupper := hLengthUpper hr (le_of_lt hNpos)
  let L : ℝ := N / (r : ℝ)
  have hLpos : 0 < L := by
    dsimp [L]
    exact div_pos hNpos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hr))
  have hxL : L ≤ x := by simpa [L] using hx
  have hxNonneg : 0 ≤ x := le_trans (le_of_lt hLpos) hxL
  let chiR : BlueprintCharacter R :=
    inducedBlueprintCharacter (Nat.dvd_lcm_left Q p) χ
  let omega : ℤ → ℂ := fun n => evalInt chiR n
  have hperiod : ∀ n : ℤ, omega n = omega (n % (R : ℤ)) := by
    intro n
    exact (evalInt_mod_period chiR n).symm
  have hweight : ∀ n : ℤ, ‖omega n‖ ≤ 1 := by
    intro n
    exact evalInt_norm_le_one chiR n
  let T0 : ℝ := ell ^ (45 * a)
  have hT0one : 1 ≤ T0 := by
    dsimp [T0]
    exact Real.one_le_rpow hellone (by positivity)
  have hperiodic := periodicLogPhaseDirichletBound
    (alpha := alpha) (A := A) (X := X) (L := L) (T0 := T0) (t := s)
    (q := R) (omega := omega)
    hα hα1 (by dsimp [A]; linarith [ha]) (hXfac3.trans hXfacX) hLlower hLupper
    hRpos hRperiod hT0one hsmin hsmax hperiod hweight
  obtain ⟨hplain, hlog⟩ := hperiodic
  have hXterm : X ^ (-delta) ≤ ell ^ (-(22 * a)) := by
    rw [Real.rpow_neg hXpos.le delta, Real.rpow_neg hellpos.le (22 * a)]
    simpa [one_div] using one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hellpos (22 * a)) hError
  have hT0pow : T0 ^ (-1 / 2 : ℝ) = ell ^ (-(45 * a) / 2) := by
    dsimp [T0]
    rw [← Real.rpow_mul hellpos.le (45 * a) (-1 / 2 : ℝ)]
    congr 1
    ring
  have hTterm : T0 ^ (-1 / 2 : ℝ) ≤ ell ^ (-(22 * a)) := by
    rw [hT0pow]
    exact Real.rpow_le_rpow_of_exponent_le hellone (by linarith [ha])
  let error : ℝ := X ^ (-delta) + T0 ^ (-1 / 2 : ℝ)
  have herr : error ≤
      2 * ell ^ (-(22 * a)) := by
    dsimp [error]
    linarith
  have hAminus : 1 ≤ ell ^ (a - 2) :=
    Real.one_le_rpow hellone (by linarith [ha])
  have hAminusFactor : ell ^ (a - 1) = ell * ell ^ (a - 2) := by
    rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add hellpos, Real.rpow_one]
    ring
  have hPhasePow : 16 * Cphase ≤ ell ^ (a - 1) := by
    rw [hAminusFactor]
    nlinarith [mul_nonneg (le_of_lt hellpos) (sub_nonneg.mpr hAminus)]
  have hlogconstant : 16 * Cphase * ell ^ (1 - a) ≤ 1 := by
    rw [show (1 - a : ℝ) = -(a - 1) by ring,
      Real.rpow_neg hellpos.le]
    have hCphase0 : 16 * Cphase ≠ 0 :=
      ne_of_gt (mul_pos (by norm_num) hCphase)
    have hinv : (ell ^ (a - 1))⁻¹ ≤ (16 * Cphase)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 hPhasePow
    calc
      16 * Cphase * (ell ^ (a - 1))⁻¹ ≤
          16 * Cphase * (16 * Cphase)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 1 := by field_simp [hCphase0]
  have hpowSplit : ell ^ (1 - a) * ell ^ (-(21 * a)) =
      ell ^ (1 - 22 * a) := by
    rw [← Real.rpow_add hellpos]
    congr 1
    ring
  have hlogMain : 8 * ell * Cphase * (2 * ell ^ (-(22 * a))) ≤
      ell ^ (-(21 * a)) := by
    have hpowFirst' : ell ^ (1 : ℝ) * ell ^ (-(22 * a)) =
        ell ^ (1 - 22 * a) := by
      rw [← Real.rpow_add hellpos]
      congr 1
    have hpowFirst : ell * ell ^ (-(22 * a)) = ell ^ (1 - 22 * a) := by
      simpa only [Real.rpow_one] using hpowFirst'
    calc
      8 * ell * Cphase * (2 * ell ^ (-(22 * a))) =
          16 * Cphase * (ell * ell ^ (-(22 * a))) := by ring
      _ = 16 * Cphase * ell ^ (1 - 22 * a) := by rw [hpowFirst]
      _ = (16 * Cphase * ell ^ (1 - a)) * ell ^ (-(21 * a)) := by
        rw [← hpowSplit]
        ring
      _ ≤ 1 * ell ^ (-(21 * a)) :=
        mul_le_mul_of_nonneg_right hlogconstant (Real.rpow_nonneg hellpos.le _)
      _ = ell ^ (-(21 * a)) := by ring
  have hplainMain : Cphase * error ≤ ell ^ (-(21 * a)) := by
    have hcoef : Cphase ≤ 8 * ell * Cphase := by
      have hfactor : 1 ≤ 8 * ell := by nlinarith [hellone]
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hfactor (le_of_lt hCphase))
    have htail : 0 ≤ error := by
      dsimp [error]
      positivity
    calc
      Cphase * error ≤ (8 * ell * Cphase) * error :=
        mul_le_mul_of_nonneg_right hcoef htail
      _ ≤ 8 * ell * Cphase * (2 * ell ^ (-(22 * a))) :=
        mul_le_mul_of_nonneg_left herr (by positivity)
      _ ≤ ell ^ (-(21 * a)) := hlogMain
  have hlogMainErr : 8 * ell * Cphase * error ≤ ell ^ (-(21 * a)) := by
    calc
      8 * ell * Cphase * error ≤
          8 * ell * Cphase * (2 * ell ^ (-(22 * a))) :=
        mul_le_mul_of_nonneg_left herr (by positivity)
      _ ≤ ell ^ (-(21 * a)) := hlogMain
  have hEllApowX : ell ^ a ≤ X := by
    have hEllAnonneg : 0 ≤ ell ^ a := Real.rpow_nonneg hellpos.le _
    have hCstarOne : 1 ≤ (2 ^ 23 : ℝ) := by norm_num
    have hEllA : ell ^ a ≤ (2 ^ 23 : ℝ) * ell ^ a := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hCstarOne hEllAnonneg)
    have hXalphaX : X ^ alpha ≤ X := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hXone hα1)
    exact hEllA.trans (hScale.trans hXalphaX)
  have hrleX : (r : ℝ) ≤ X := hrX.trans hEllApowX
  let ycut : ℝ := min y (z / (r : ℝ))
  have hyL : y ≤ 2 * L := by simpa [L] using hy
  have hcutUpper : x + (ycut - x) ≤ 2 * L := by
    calc
      x + (ycut - x) = ycut := by ring
      _ ≤ y := min_le_left _ _
      _ ≤ 2 * L := hyL
  have hplainAt := hplain x (ycut - x) hxL hcutUpper
  have hlogAt := hlog (r : ℝ) x (ycut - x)
    (by exact_mod_cast hr) hrleX hxL hcutUpper
  have hcharAt {n : ℤ} (hn : 0 ≤ n) :
      evalInt chiR n = evalInt χ n * (if Nat.Coprime n.toNat p then 1 else 0) := by
    exact inducedLcmCharacter_eval_eq_cutoff_int
      (q := Q) (p := p) χ hn
  have hsumOne :
      (∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor ycut),
        originalLongFactorCoefficient .one r p χ s m) =
      ∑ n ∈ FractionalPrimes.realIntegerInterval x (ycut - x),
        omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ)) := by
    rw [originalLongFactorSum_reindex (x := x) (y := ycut)
      hxNonneg .one r p χ s]
    apply Finset.sum_congr rfl
    intro n hn
    have hbounds := (FractionalPrimes.mem_realIntegerInterval_iff x
      (ycut - x) n).mp hn
    have hnnonneg : 0 ≤ n := by
      exact_mod_cast (le_of_lt (lt_of_le_of_lt hxNonneg hbounds.1))
    have hchar := hcharAt hnnonneg
    simp only [originalLongFactorIntCoefficient, OriginalLongFactorWeight.coeff,
      one_mul, omega]
    rw [← hchar]
  have hsumLog :
      (∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor ycut),
        originalLongFactorCoefficient .logarithm r p χ s m) =
      ∑ n ∈ FractionalPrimes.realIntegerInterval x (ycut - x),
        omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ)) *
          (Real.log ((r : ℝ) * (n : ℝ)) : ℂ) := by
    rw [originalLongFactorSum_reindex (x := x) (y := ycut)
      hxNonneg .logarithm r p χ s]
    apply Finset.sum_congr rfl
    intro n hn
    have hbounds := (FractionalPrimes.mem_realIntegerInterval_iff x
      (ycut - x) n).mp hn
    have hnnonneg : 0 ≤ n := by
      exact_mod_cast (le_of_lt (lt_of_le_of_lt hxNonneg hbounds.1))
    have hchar := hcharAt hnnonneg
    have hnatcast : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hnnonneg)
    have hlogarg : ((r * n.toNat : ℕ) : ℝ) =
        (r : ℝ) * (n : ℝ) := by
      calc
        ((r * n.toNat : ℕ) : ℝ) = (r : ℝ) * (n.toNat : ℝ) := by norm_num
        _ = (r : ℝ) * (n : ℝ) := by rw [hnatcast]
    have hlog :
        (Real.log ((r * n.toNat : ℕ) : ℝ) : ℂ) =
          (Real.log ((r : ℝ) * (n : ℝ)) : ℂ) := by
      exact congrArg (fun t : ℝ => (Real.log t : ℂ)) hlogarg
    simp only [originalLongFactorIntCoefficient,
      OriginalLongFactorWeight.coeff, omega]
    calc
      (Real.log ((r * n.toNat : ℕ) : ℝ) : ℂ) * evalInt χ (n : ℤ) *
          (if Nat.Coprime n.toNat p then 1 else 0) *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ)) =
        (Real.log ((r * n.toNat : ℕ) : ℝ) : ℂ) *
          (evalInt χ (n : ℤ) * (if Nat.Coprime n.toNat p then 1 else 0)) *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ)) := by ring
      _ = (Real.log ((r * n.toNat : ℕ) : ℝ) : ℂ) *
          evalInt chiR (n : ℤ) *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ)) := by rw [← hchar]
      _ = evalInt chiR (n : ℤ) *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ)) *
          (Real.log ((r : ℝ) * (n : ℝ)) : ℂ) := by rw [← hlog]; ring
  cases u with
  | one =>
    have hbound : ‖∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor ycut),
        originalLongFactorCoefficient .one r p χ s m‖ ≤
        ell ^ (-(21 * a)) * Real.sqrt L := by
      calc
        _ = ‖∑ n ∈ FractionalPrimes.realIntegerInterval x (ycut - x),
            omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ))‖ := by
          rw [hsumOne]
        _ ≤ Cphase * Real.sqrt L * error := by
          simpa [delta, Cphase, error, T0] using hplainAt
        _ = Real.sqrt L * (Cphase * error) := by ring
        _ ≤ Real.sqrt L * ell ^ (-(21 * a)) :=
          mul_le_mul_of_nonneg_left hplainMain (Real.sqrt_nonneg _)
        _ = ell ^ (-(21 * a)) * Real.sqrt L := by ring
    simpa [ell, L, ycut] using hbound
  | logarithm =>
    have hbound : ‖∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor ycut),
        originalLongFactorCoefficient .logarithm r p χ s m‖ ≤
        ell ^ (-(21 * a)) * Real.sqrt L := by
      calc
        _ = ‖∑ n ∈ FractionalPrimes.realIntegerInterval x (ycut - x),
            omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (s : ℂ)) *
              (Real.log ((r : ℝ) * (n : ℝ)) : ℂ)‖ := by
          rw [hsumLog]
        _ ≤ 8 * ell * Cphase * Real.sqrt L * error := by
          simpa [delta, Cphase, error, T0] using hlogAt
        _ = Real.sqrt L * (8 * ell * Cphase * error) := by ring
        _ ≤ Real.sqrt L * ell ^ (-(21 * a)) :=
          mul_le_mul_of_nonneg_left hlogMainErr (Real.sqrt_nonneg _)
        _ = ell ^ (-(21 * a)) * Real.sqrt L := by ring
    simpa [ell, L, ycut] using hbound
  | mobius =>
    by_cases hxcut : x ≤ ycut
    · have hMufBound := hMufAt
        (X := X) (L := L) (hXμX) hLlower hLupper
        (q := R) (by exact_mod_cast hRpos) hRbound
        r hr hrbound chiR s hsmax
        (u := x) (v := ycut) hxL hxcut (by
          exact (min_le_left y (z / (r : ℝ))).trans hyL)
      have hsumMuf :
          (∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor ycut),
            originalLongFactorCoefficient .mobius r p χ s m) =
          ∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor ycut),
            FractionalPrimes.Literature.Reciprocal.twistedMobiusRectangleCoefficient
              r chiR s m * inverseSqrtWeight (m : ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmpos : 0 < m := by
          have hxm : x < (m : ℝ) := (Nat.floor_lt hxNonneg).mp
            (Finset.mem_Ioc.mp hm).1
          have hxpos : 0 < x := lt_of_lt_of_le hLpos hxL
          exact_mod_cast (lt_trans hxpos hxm)
        exact originalLongFactorMobiusCoefficient_eq
          (q := Q) (p := p) (r := r) (m := m) χ s hmpos
      have hbound : ‖∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor ycut),
          originalLongFactorCoefficient .mobius r p χ s m‖ ≤
          ell ^ (-(21 * a)) * Real.sqrt L := by
        calc
          _ = ‖∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor ycut),
              FractionalPrimes.Literature.Reciprocal.twistedMobiusRectangleCoefficient
                r chiR s m * inverseSqrtWeight (m : ℝ)‖ := by rw [hsumMuf]
          _ ≤ Cμ * Real.sqrt L * ell ^ (-(22 * a)) := hMufBound
          _ = Real.sqrt L * (Cμ * ell ^ (-(22 * a))) := by ring
          _ ≤ Real.sqrt L * ell ^ (-(21 * a)) :=
            mul_le_mul_of_nonneg_left (by
              calc
                Cμ * ell ^ (-(22 * a)) ≤ ell ^ a * ell ^ (-(22 * a)) :=
                  mul_le_mul_of_nonneg_right hCμpow (Real.rpow_nonneg hellpos.le _)
                _ = ell ^ (-(21 * a)) := by
                  rw [← Real.rpow_add hellpos]
                  congr 1
                  ring) (Real.sqrt_nonneg _)
          _ = ell ^ (-(21 * a)) * Real.sqrt L := by ring
      simpa [ell, L, ycut] using hbound
    · have hEmpty : FractionalPrimes.realIntegerInterval x (ycut - x) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        have hbounds := (FractionalPrimes.mem_realIntegerInterval_iff x
          (ycut - x) n).mp hn
        have hnupper : (n : ℝ) ≤ ycut := by linarith
        exact (not_le.mpr hbounds.1)
          (le_trans hnupper (le_of_lt (lt_of_not_ge hxcut)))
      have hsumEmpty := originalLongFactorSum_reindex (x := x) (y := ycut)
        hxNonneg .mobius r p χ s
      have hbound : ‖∑ m ∈ Finset.Ioc (Nat.floor x) (Nat.floor ycut),
          originalLongFactorCoefficient .mobius r p χ s m‖ ≤
          ell ^ (-(21 * a)) * Real.sqrt L := by
        rw [hsumEmpty, hEmpty]
        simp
        positivity
      simpa [ell, L, ycut] using hbound

end FractionalPrimes.Literature.Twisted

end
