module
public import FractionalPrimes.Literature.LongArithmetic.ShiftedCharacterMobiusSeries
public import FractionalPrimes.Literature.LongArithmetic.RemovedEulerFactorsBound
public import FractionalPrimes.Literature.LongArithmetic.FiniteEulerCorrectionProduct
public import FractionalPrimes.Literature.Reciprocal.ReciprocalStrip
public import FractionalPrimes.Literature.Reciprocal.PrincipalReciprocalHalfPlaneAnalyticity
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletEulerLog
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletMathlibIdentification
@[expose] public section

@[expose] public section

noncomputable section

open Complex Set
open scoped ArithmeticFunction.Moebius LSeries.notation Topology

namespace FractionalPrimes.Literature.Reciprocal

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Twisted

/-- The left-edge distance in `lrc:twisted-rectangle`, expressed directly in
terms of `X`. -/
def twistedMobiusRectangleDelta (X : ℝ) : ℝ :=
  1 / (8 * Real.log (Real.log X))

/-- The exact closed rectangle from `lrc:twisted-rectangle`. -/
def twistedMobiusRectangleRegion (X A : ℝ) : Set ℂ :=
  {s | 1 - twistedMobiusRectangleDelta X ≤ s.re ∧
    s.re ≤ 3 / 2 ∧ |s.im| ≤ X ^ (A + 2)}

/-- The exact uniform exponent in `lrc:twisted-rectangle`. -/
def twistedMobiusRectangleErrorExponent (A B X : ℝ) : ℝ :=
  12 + 12 * Real.log (Real.log X) +
    600 * (A + B + 6) ^ FractionalPrimes.Literature.Analytic.explicitLogarithmTheta *
      (Real.log X) ^ FractionalPrimes.Literature.Analytic.explicitLogarithmTheta

/-- The explicit analytic extension specified in the proof of
`lrc:twisted-rectangle`. The two finite products remain separate because the
principal character has its own modulus factors. -/
noncomputable def twistedMobiusRectangleExtension {q : ℕ} [NeZero q]
    (r : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (s : ℂ) : ℂ :=
  if _hχ : χ = principalCharacter q then
    (ArithmeticFunction.moebius r : ℂ) *
      continuedDirichletPrincipalReciprocal (s + (t : ℂ) * Complex.I) *
      qPrimeEulerCorrectionProduct q (s + (t : ℂ) * Complex.I) *
      rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q))
        (s + (t : ℂ) * Complex.I)
  else
    (ArithmeticFunction.moebius r : ℂ) *
      (nonprincipalContinuedDirichletLCore χ (s + (t : ℂ) * Complex.I))⁻¹ *
      rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q))
        (s + (t : ℂ) * Complex.I)

/-- The coefficient convention in `lrc:twisted-rectangle`, as an `LSeries`
coefficient. -/
noncomputable def twistedMobiusRectangleCoefficient {q : ℕ} [NeZero q]
    (r : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  shiftedCharacterMobiusCoefficient r χ t n

private theorem twistedMobiusRectangleCoefficient_norm_le_one
    {q : ℕ} [NeZero q] (r : ℕ) (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) :
    ‖twistedMobiusRectangleCoefficient r χ t n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [twistedMobiusRectangleCoefficient, shiftedCharacterMobiusCoefficient,
      mobiusMultiplierCoefficient, hn]
  · have hmu :
        ‖mobiusMultiplierCoefficient r (dirichletCharacterNatHom χ) n‖ ≤ 1 := by
      rw [mobiusMultiplierCoefficient, norm_mul]
      have hmoebius :
          ‖(ArithmeticFunction.moebius (r * n) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r * n)
      have hcharacter := dirichletCharacterNatHom_norm_le_one χ hn
      calc
        ‖(ArithmeticFunction.moebius (r * n) : ℂ)‖ *
            ‖dirichletCharacterNatHom χ n‖ ≤ 1 * 1 :=
          mul_le_mul hmoebius hcharacter (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hphase :
        ‖(n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re]
    rw [twistedMobiusRectangleCoefficient, shiftedCharacterMobiusCoefficient,
      norm_mul, hphase]
    simpa using hmu

private theorem twistedMobiusRectangle_geometry {X : ℝ}
    (hw : Real.exp 8 ≤ Real.log X) :
    0 < Real.log X ∧ 8 ≤ Real.log (Real.log X) ∧
      0 < twistedMobiusRectangleDelta X ∧
      twistedMobiusRectangleDelta X ≤ 1 / 64 ∧
      twistedMobiusRectangleDelta X ≤
        min (1 / 4) (1 / (4 * Real.log (Real.log X))) := by
  have hwpos : 0 < Real.log X := (Real.exp_pos 8).trans_le hw
  have hlogw : 8 ≤ Real.log (Real.log X) := by
    calc
      8 = Real.log (Real.exp 8) := by rw [Real.log_exp]
      _ ≤ Real.log (Real.log X) := Real.log_le_log (Real.exp_pos 8) hw
  have hden : (64 : ℝ) ≤ 8 * Real.log (Real.log X) := by nlinarith
  have hdelta : twistedMobiusRectangleDelta X ≤ 1 / 64 :=
    one_div_le_one_div_of_le (by norm_num) hden
  have hdelta0 : 0 < twistedMobiusRectangleDelta X := by
    dsimp [twistedMobiusRectangleDelta]
    positivity
  have hdeltaquarter : twistedMobiusRectangleDelta X ≤ 1 / 4 :=
    hdelta.trans (by norm_num)
  have hdeltaLog : twistedMobiusRectangleDelta X ≤
      1 / (4 * Real.log (Real.log X)) := by
    have hdenpos : 0 < 4 * Real.log (Real.log X) := by positivity
    have hdenle : 4 * Real.log (Real.log X) ≤
        8 * Real.log (Real.log X) := by nlinarith
    dsimp [twistedMobiusRectangleDelta]
    exact one_div_le_one_div_of_le hdenpos hdenle
  exact ⟨hwpos, hlogw, hdelta0, hdelta,
    le_min hdeltaquarter hdeltaLog⟩

private theorem twistedMobiusRectangle_logArgument_bound
    {A B X : ℝ} {q : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hw : Real.exp 8 ≤ Real.log X) (hwX : (Real.log X) ^ B ≤ X)
    (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ (Real.log X) ^ B) (t : ℝ)
    (ht : |t| ≤ X ^ A) {s : ℂ}
    (hs : s ∈ twistedMobiusRectangleRegion X A) :
    1 + Real.log (4 * (q : ℝ) * (|s.im + t| + 4)) ≤
      (A + B + 6) * Real.log X := by
  let w : ℝ := Real.log X
  have hwpos : 0 < w := by dsimp [w]; exact (Real.exp_pos 8).trans_le hw
  have hwlog : 8 ≤ Real.log w := by
    dsimp [w]
    calc
      8 = Real.log (Real.exp 8) := by rw [Real.log_exp]
      _ ≤ Real.log (Real.log X) := Real.log_le_log (Real.exp_pos 8) hw
  have hXpos : 0 < X := by
    have hpow : 0 < (Real.log X) ^ B := Real.rpow_pos_of_pos
      ((Real.exp_pos 8).trans_le hw) B
    exact lt_of_lt_of_le hpow hwX
  have hXlarge : 9 ≤ X := by
    have hlogX : 9 ≤ Real.log X := by
      calc
        9 ≤ Real.exp 8 := by linarith [Real.add_one_le_exp 8]
        _ ≤ Real.log X := hw
    exact hlogX.trans (Real.log_le_self hXpos.le)
  have hXone : 1 ≤ X := le_trans (by norm_num) hXlarge
  have hpowone : 1 ≤ X ^ (A + 2) :=
    Real.one_le_rpow hXone (by linarith)
  have hpowA : X ^ A ≤ X ^ (A + 2) :=
    Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
  rcases hs with ⟨_, _, hsim⟩
  have hτ : |s.im + t| ≤ 2 * X ^ (A + 2) := by
    calc
      |s.im + t| ≤ |s.im| + |t| := abs_add_le _ _
      _ ≤ X ^ (A + 2) + X ^ (A + 2) :=
        add_le_add hsim (ht.trans hpowA)
      _ = 2 * X ^ (A + 2) := by ring
  have hτ4 : |s.im + t| + 4 ≤ 3 * X ^ (A + 2) := by
    have hxpow : X ≤ X ^ (A + 2) := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hXone
        (show (1 : ℝ) ≤ A + 2 by linarith))
    have h4 : 4 ≤ X ^ (A + 2) := by linarith
    nlinarith [hτ]
  have harg :
      4 * (q : ℝ) * (|s.im + t| + 4) ≤
        12 * w ^ B * X ^ (A + 2) := by
    calc
      4 * (q : ℝ) * (|s.im + t| + 4) ≤
          4 * w ^ B * (3 * X ^ (A + 2)) := by
            have hq4 : 4 * (q : ℝ) ≤ 4 * w ^ B :=
              mul_le_mul_of_nonneg_left hq (by norm_num)
            exact mul_le_mul hq4 hτ4 (by positivity) (by positivity)
      _ = 12 * w ^ B * X ^ (A + 2) := by ring
  have hargpos : 0 < 4 * (q : ℝ) * (|s.im + t| + 4) := by
    have hqpos : 0 < (q : ℝ) := by
      have hqnat : 0 < q := by omega
      exact_mod_cast hqnat
    positivity
  have hmajorpos : 0 < 12 * w ^ B * X ^ (A + 2) := by positivity
  have hlogarg : Real.log (4 * (q : ℝ) * (|s.im + t| + 4)) ≤
      Real.log (12 * w ^ B * X ^ (A + 2)) :=
    Real.log_le_log hargpos harg
  have hlogmajor : Real.log (12 * w ^ B * X ^ (A + 2)) =
      Real.log 12 + B * Real.log w + (A + 2) * Real.log X := by
    rw [Real.log_mul (by positivity : 12 * w ^ B ≠ 0)
      (ne_of_gt (Real.rpow_pos_of_pos hXpos (A + 2)))]
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hwpos B))]
    rw [Real.log_rpow hwpos B, Real.log_rpow hXpos (A + 2)]
  have hlog12 : Real.log 12 ≤ 11 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12)
    nlinarith
  have hwlarge : 9 ≤ w := by
    dsimp [w]
    calc
      9 ≤ Real.exp 8 := by linarith [Real.add_one_le_exp 8]
      _ ≤ Real.log X := hw
  have hlogw : Real.log w ≤ w := Real.log_le_self hwpos.le
  calc
    1 + Real.log (4 * (q : ℝ) * (|s.im + t| + 4)) ≤
        1 + Real.log (12 * w ^ B * X ^ (A + 2)) := by linarith [hlogarg]
    _ = 1 + Real.log 12 + B * Real.log w + (A + 2) * w := by
      rw [hlogmajor, show Real.log X = w by rfl]
      ring
    _ ≤ 4 * w + B * w + (A + 2) * w := by
      have hconst : 1 + Real.log 12 ≤ 4 * w := by nlinarith
      have hBterm : B * Real.log w ≤ B * w :=
        mul_le_mul_of_nonneg_left hlogw hB.le
      nlinarith
    _ = (A + B + 6) * Real.log X := by
      rw [show w = Real.log X by rfl]
      ring

private theorem mobiusWeightedDirichletSeries_eq_inverse_LSeries
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ) s =
      (LSeries (χ ·) s)⁻¹ := by
  have hcoeff : ∀ {n : ℕ}, n ≠ 0 →
      ((ArithmeticFunction.moebius n : ℂ) * dirichletCharacterNatHom χ n) =
        (χ n : ℂ) * (ArithmeticFunction.moebius n : ℂ) := by
    intro n hn
    rw [dirichletCharacterNatHom_apply_of_ne_zero χ hn]
    ring
  have hseries : mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ) s =
      LSeries (↗χ * ↗ArithmeticFunction.moebius) s := by
    apply LSeries_congr
    intro n hn
    simp [hcoeff hn, mul_comm]
  calc
    mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ) s =
        LSeries (↗χ * ↗ArithmeticFunction.moebius) s := hseries
    _ = Complex.exp (-continuedDirichletEulerLog χ s) :=
      LSeries_twistedMoebius_eq_exp_neg_continuedDirichletEulerLog χ hs
    _ = (Complex.exp (continuedDirichletEulerLog χ s))⁻¹ := by
      rw [Complex.exp_neg]
    _ = (LSeries (χ ·) s)⁻¹ := by
      rw [exp_continuedDirichletEulerLog_eq_LSeries χ hs]

private theorem mobiusWeightedDirichletSeries_ne_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ) s ≠ 0 := by
  rw [mobiusWeightedDirichletSeries_eq_inverse_LSeries χ hs]
  apply inv_ne_zero
  rw [← exp_continuedDirichletEulerLog_eq_LSeries χ hs]
  exact Complex.exp_ne_zero _

#print axioms mobiusWeightedDirichletSeries_eq_inverse_LSeries

private theorem finitePrimeDivisors_eq_mobiusPrimeDivisors (r : ℕ) :
    finitePrimeDivisors r = mobiusPrimeDivisors r := by
  ext p
  rw [mem_finitePrimeDivisors, mem_mobiusPrimeDivisors]

private theorem qPrimeEulerCorrectionProduct_eq_primeFactors
    {q : ℕ} [NeZero q] (s : ℂ) :
    qPrimeEulerCorrectionProduct q s =
      ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  classical
  unfold qPrimeEulerCorrectionProduct finiteEulerCorrectionProduct finitePrimeDivisors
  rw [Finset.prod_map]
  simp only [one_mul]
  exact Finset.prod_attach q.primeFactors
    (fun p : ℕ => (1 - (p : ℂ) ^ (-s))⁻¹)

private theorem rPrimeEulerCorrectionProduct_eq_mobiusPrimeDivisors
    {q : ℕ} [NeZero q] (r : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q)) s =
      ∏ p ∈ mobiusPrimeDivisors r,
        (mobiusEulerFactor (dirichletCharacterNatHom χ) s p)⁻¹ := by
  classical
  unfold rPrimeEulerCorrectionProduct finiteEulerCorrectionProduct
  rw [finitePrimeDivisors_eq_mobiusPrimeDivisors]
  apply Finset.prod_congr rfl
  intro p hp
  have hpne : (p : ℕ) ≠ 0 := p.property.ne_zero
  simp only [mobiusEulerFactor]
  rw [dirichletCharacterNatHom_apply_of_ne_zero χ hpne]

private theorem rPrimeEulerCorrectionProduct_eq_primeFactors
    {q : ℕ} [NeZero q] (r : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q)) s =
      ∏ p ∈ r.primeFactors,
        (1 - χ (p : ZMod q) * (p : ℂ) ^ (-s))⁻¹ := by
  classical
  unfold rPrimeEulerCorrectionProduct finiteEulerCorrectionProduct finitePrimeDivisors
  rw [Finset.prod_map]
  exact Finset.prod_attach r.primeFactors
    (fun p : ℕ => (1 - χ (p : ZMod q) * (p : ℂ) ^ (-s))⁻¹)

private theorem qPrimeEulerCorrectionProduct_norm_le_removed
    {q : ℕ} [NeZero q] {X delta : ℝ} {s : ℂ}
    (hX : Real.exp 4 ≤ X) (hq1 : 1 ≤ q) (hqX : (q : ℝ) ≤ X)
    (hδ0 : 0 ≤ delta)
    (hδ : delta ≤ min (1 / 4) (1 / (4 * Real.log (Real.log X))))
    (hs : 1 - delta ≤ s.re) :
    ‖qPrimeEulerCorrectionProduct q s‖ ≤ Real.exp 6 * (Real.log X) ^ 6 := by
  have hremoved := @removedEulerFactorsBound X delta q s
    (fun _ : ℕ => (1 : ℂ)) hX hq1 hqX hδ0 hδ hs
    (by intro p hp; norm_num)
  rw [qPrimeEulerCorrectionProduct_eq_primeFactors]
  simpa only [norm_prod, norm_mul, norm_inv, norm_one, one_mul] using hremoved.2

private theorem rPrimeEulerCorrectionProduct_norm_le_removed
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {X delta : ℝ} {r : ℕ} {s : ℂ}
    (hX : Real.exp 4 ≤ X) (hr1 : 1 ≤ r) (hrX : (r : ℝ) ≤ X)
    (hδ0 : 0 ≤ delta)
    (hδ : delta ≤ min (1 / 4) (1 / (4 * Real.log (Real.log X))))
    (hs : 1 - delta ≤ s.re) :
    ‖rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q)) s‖ ≤
      Real.exp 6 * (Real.log X) ^ 6 := by
  have hremoved := @removedEulerFactorsBound X delta r s
    (fun p : ℕ => χ (p : ZMod q)) hX hr1 hrX hδ0 hδ hs (by
      intro p hp
      exact χ.norm_le_one _)
  rw [rPrimeEulerCorrectionProduct_eq_primeFactors]
  simpa only [norm_prod, norm_mul, norm_inv] using hremoved.2

private theorem principalWeightedSeries_eq_R0_mul_qCorrection
    {q : ℕ} [NeZero q]
    (s : ℂ) (hs : 1 < s.re) :
    mobiusWeightedDirichletSeries
        (dirichletCharacterNatHom (principalCharacter q)) s =
      continuedDirichletPrincipalReciprocal s * qPrimeEulerCorrectionProduct q s := by
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hprincipalL : LSeries ((principalCharacter q) ·) s =
      principalContinuedDirichletL (q := q) s hspos hs1 := by
    symm
    exact principalContinuedDirichletL_eq_LSeries_of_one_lt_re hs
  have hR0 : continuedDirichletPrincipalReciprocal s =
      (continuedDirichletZ s hspos hs1)⁻¹ :=
    continuedDirichletPrincipalReciprocal_eq_inv_continuedDirichletZ hspos hs1
  have hqProd : qPrimeEulerCorrectionProduct q s =
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)))⁻¹ := by
    rw [qPrimeEulerCorrectionProduct_eq_primeFactors, Finset.prod_inv_distrib]
  calc
    mobiusWeightedDirichletSeries
        (dirichletCharacterNatHom (principalCharacter q)) s =
        (LSeries ((principalCharacter q) ·) s)⁻¹ :=
      mobiusWeightedDirichletSeries_eq_inverse_LSeries (principalCharacter q) hs
    _ = (principalContinuedDirichletL (q := q) s hspos hs1)⁻¹ := by
      rw [hprincipalL]
    _ = continuedDirichletPrincipalReciprocal s *
        qPrimeEulerCorrectionProduct q s := by
      rw [principalContinuedDirichletL, hR0, hqProd]
      ring

private theorem nonprincipalWeightedSeries_eq_inverse_core
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ principalCharacter q) {s : ℂ} (hs : 1 < s.re) :
    mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ) s =
      (nonprincipalContinuedDirichletLCore χ s)⁻¹ := by
  have hspos : 0 < s.re := by linarith
  have hnotpole :
      ¬ (χ = principalCharacter q ∧ s = 1) := by
    rintro ⟨h, _⟩
    exact hχ h
  have hcontinued := continuedDirichletL_eq_LSeries_of_one_lt_re χ hs
  have hcore : nonprincipalContinuedDirichletLCore χ s = LSeries (χ ·) s := by
    have hbranch : continuedDirichletL χ s (by linarith) hnotpole =
        nonprincipalContinuedDirichletLCore χ s := by
      simp [continuedDirichletL, hχ, nonprincipalContinuedDirichletL_eq_core]
    rw [← hbranch]
    exact hcontinued
  calc
    mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ) s =
        (LSeries (χ ·) s)⁻¹ := mobiusWeightedDirichletSeries_eq_inverse_LSeries χ hs
    _ = (nonprincipalContinuedDirichletLCore χ s)⁻¹ := by rw [← hcore]

private theorem twistedMobiusRectangleExtension_eq_series
    {q : ℕ} [NeZero q]
    (r : ℕ) (hr : r ≠ 0) (χ : DirichletCharacter ℂ q) (t : ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    twistedMobiusRectangleExtension r χ t s =
      LSeries (twistedMobiusRectangleCoefficient r χ t) s := by
  change twistedMobiusRectangleExtension r χ t s =
    LSeries (shiftedCharacterMobiusCoefficient r χ t) s
  have hshift := shiftedCharacterMobiusDirichletSeries_eq r hr χ t hs
  by_cases hχ : χ = principalCharacter q
  · rw [twistedMobiusRectangleExtension, dite_eq_left hχ]
    have hweighted :
        mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ)
            (s + (t : ℂ) * Complex.I) =
          continuedDirichletPrincipalReciprocal (s + (t : ℂ) * Complex.I) *
            qPrimeEulerCorrectionProduct q (s + (t : ℂ) * Complex.I) := by
      simpa [hχ] using
        principalWeightedSeries_eq_R0_mul_qCorrection _ (by simpa using hs)
    calc
      (ArithmeticFunction.moebius r : ℂ) *
          continuedDirichletPrincipalReciprocal (s + (t : ℂ) * Complex.I) *
          qPrimeEulerCorrectionProduct q (s + (t : ℂ) * Complex.I) *
          rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q))
            (s + (t : ℂ) * Complex.I) =
        (ArithmeticFunction.moebius r : ℂ) *
          mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ)
            (s + (t : ℂ) * Complex.I) *
          rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q))
            (s + (t : ℂ) * Complex.I) := by
              calc
                _ = (ArithmeticFunction.moebius r : ℂ) *
                    (continuedDirichletPrincipalReciprocal
                      (s + (t : ℂ) * Complex.I) *
                     qPrimeEulerCorrectionProduct q (s + (t : ℂ) * Complex.I)) *
                    rPrimeEulerCorrectionProduct r
                      (fun p : Nat.Primes => χ (p : ZMod q))
                      (s + (t : ℂ) * Complex.I) := by ring
                _ = _ := by rw [← hweighted]
      _ = (ArithmeticFunction.moebius r : ℂ) *
          mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ)
            (s + (t : ℂ) * Complex.I) *
          ∏ p ∈ mobiusPrimeDivisors r,
            (mobiusEulerFactor (dirichletCharacterNatHom χ)
              (s + (t : ℂ) * Complex.I) p)⁻¹ := by
              rw [rPrimeEulerCorrectionProduct_eq_mobiusPrimeDivisors]
      _ = LSeries (twistedMobiusRectangleCoefficient r χ t) s := by
        exact hshift.symm
  · rw [twistedMobiusRectangleExtension, dite_eq_right hχ]
    calc
      (ArithmeticFunction.moebius r : ℂ) *
          (nonprincipalContinuedDirichletLCore χ
            (s + (t : ℂ) * Complex.I))⁻¹ *
          rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q))
            (s + (t : ℂ) * Complex.I) =
        (ArithmeticFunction.moebius r : ℂ) *
          mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ)
            (s + (t : ℂ) * Complex.I) *
          rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q))
            (s + (t : ℂ) * Complex.I) := by
              calc
                _ = (ArithmeticFunction.moebius r : ℂ) *
                    (nonprincipalContinuedDirichletLCore χ
                      (s + (t : ℂ) * Complex.I))⁻¹ *
                    rPrimeEulerCorrectionProduct r
                      (fun p : Nat.Primes => χ (p : ZMod q))
                      (s + (t : ℂ) * Complex.I) := by rfl
                _ = (ArithmeticFunction.moebius r : ℂ) *
                    mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ)
                      (s + (t : ℂ) * Complex.I) *
                    rPrimeEulerCorrectionProduct r
                      (fun p : Nat.Primes => χ (p : ZMod q))
                      (s + (t : ℂ) * Complex.I) := by
                        rw [← nonprincipalWeightedSeries_eq_inverse_core χ hχ (by
                          simpa using hs)]
      _ = (ArithmeticFunction.moebius r : ℂ) *
          mobiusWeightedDirichletSeries (dirichletCharacterNatHom χ)
            (s + (t : ℂ) * Complex.I) *
          ∏ p ∈ mobiusPrimeDivisors r,
            (mobiusEulerFactor (dirichletCharacterNatHom χ)
              (s + (t : ℂ) * Complex.I) p)⁻¹ := by
              rw [rPrimeEulerCorrectionProduct_eq_mobiusPrimeDivisors]
      _ = LSeries (twistedMobiusRectangleCoefficient r χ t) s := by
        exact hshift.symm

private theorem twistedMobiusRectangleExtension_analyticOnNhd
    {q : ℕ} [NeZero q] (hZFR : fixedHalfPlaneProperty)
    (r : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    AnalyticOnNhd ℂ (twistedMobiusRectangleExtension r χ t)
      {s : ℂ | (7 / 8 : ℝ) < s.re} := by
  let U : Set ℂ := {s : ℂ | (7 / 8 : ℝ) < s.re}
  let Upos : Set ℂ := {s : ℂ | 0 < s.re}
  let shift : ℂ → ℂ := fun s => s + (t : ℂ) * Complex.I
  have hshift : AnalyticOnNhd ℂ shift U := by
    exact analyticOnNhd_id.add analyticOnNhd_const
  have hshift_maps : Set.MapsTo shift U Upos := by
    intro s hs
    dsimp [U, Upos] at hs ⊢
    have hspos : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 7 / 8) hs
    simpa [shift] using hspos
  have hshift_maps78 : Set.MapsTo shift U U := by
    intro s hs
    dsimp [U] at hs ⊢
    simpa [shift] using hs
  have hR0 : AnalyticOnNhd ℂ
      (fun s : ℂ => continuedDirichletPrincipalReciprocal (shift s)) U := by
    change AnalyticOnNhd ℂ
      (continuedDirichletPrincipalReciprocal ∘ shift) U
    exact AnalyticOnNhd.comp
      (analyticOnNhd_continuedDirichletPrincipalReciprocal_of_fixedHalfPlane hZFR)
      hshift hshift_maps78
  have hqbase : AnalyticOnNhd ℂ (qPrimeEulerCorrectionProduct q) Upos := by
    simpa only [Upos] using analyticOnNhd_qPrimeEulerCorrectionProduct q
  have hq : AnalyticOnNhd ℂ
      (fun s : ℂ => qPrimeEulerCorrectionProduct q (shift s)) U := by
    change AnalyticOnNhd ℂ (qPrimeEulerCorrectionProduct q ∘ shift) U
    exact hqbase.comp hshift hshift_maps
  have hχp : ∀ p ∈ finitePrimeDivisors r,
      ‖χ (p : ZMod q)‖ ≤ 1 := by
    intro p hp
    exact χ.norm_le_one _
  have hrbase : AnalyticOnNhd ℂ
      (rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q))) Upos := by
    simpa only [Upos] using (analyticOnNhd_rPrimeEulerCorrectionProduct r
      (fun p : Nat.Primes => χ (p : ZMod q)) hχp)
  have hr : AnalyticOnNhd ℂ
      (fun s : ℂ => rPrimeEulerCorrectionProduct r
        (fun p : Nat.Primes => χ (p : ZMod q)) (shift s)) U := by
    change AnalyticOnNhd ℂ
      (rPrimeEulerCorrectionProduct r (fun p : Nat.Primes => χ (p : ZMod q)) ∘ shift) U
    exact hrbase.comp hshift hshift_maps
  by_cases hχ : χ = principalCharacter q
  · have hbranch : twistedMobiusRectangleExtension r χ t = fun s : ℂ =>
        ((ArithmeticFunction.moebius r : ℂ) *
          continuedDirichletPrincipalReciprocal (shift s)) *
          qPrimeEulerCorrectionProduct q (shift s) *
          rPrimeEulerCorrectionProduct r
            (fun p : Nat.Primes => χ (p : ZMod q)) (shift s) := by
      funext s
      simp [twistedMobiusRectangleExtension, shift, hχ]
    rw [hbranch]
    have hconst : AnalyticOnNhd ℂ
        (fun _ : ℂ => (ArithmeticFunction.moebius r : ℂ)) U :=
      analyticOnNhd_const
    exact ((hconst.mul hR0).mul hq).mul hr
  · have hUopen : IsOpen U := by
      dsimp [U]
      exact isOpen_lt continuous_const Complex.continuous_re
    have hcoreDiff : DifferentiableOn ℂ
        (nonprincipalContinuedDirichletLCore χ) U := by
      intro s hs
      change (7 / 8 : ℝ) < s.re at hs
      exact (nonprincipalContinuedDirichletL_differentiableAt χ hχ
        (lt_trans (by norm_num : (0 : ℝ) < 7 / 8) hs)).differentiableWithinAt
    have hcoreAnalytic : AnalyticOnNhd ℂ
        (nonprincipalContinuedDirichletLCore χ) U :=
      hcoreDiff.analyticOnNhd hUopen
    have hcoreNe : ∀ s ∈ U, nonprincipalContinuedDirichletLCore χ s ≠ 0 := by
      intro s hs
      have hspos : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 7 / 8) hs
      have hnotpole :
          ¬ (χ = principalCharacter q ∧ s = 1) := by
        rintro ⟨h, _⟩
        exact hχ h
      have hLne := hZFR χ hs hnotpole
      simpa [continuedDirichletL, hχ, nonprincipalContinuedDirichletL_eq_core] using hLne
    have hcoreInv : AnalyticOnNhd ℂ
        (fun s : ℂ => (nonprincipalContinuedDirichletLCore χ s)⁻¹) U :=
      hcoreAnalytic.inv hcoreNe
    have hcoreShift : AnalyticOnNhd ℂ
        (fun s : ℂ => (nonprincipalContinuedDirichletLCore χ (shift s))⁻¹) U := by
      change AnalyticOnNhd ℂ
        ((fun s : ℂ => (nonprincipalContinuedDirichletLCore χ s)⁻¹) ∘ shift) U
      exact hcoreInv.comp hshift hshift_maps78
    have hbranch : twistedMobiusRectangleExtension r χ t = fun s : ℂ =>
        ((ArithmeticFunction.moebius r : ℂ) *
          (nonprincipalContinuedDirichletLCore χ (shift s))⁻¹) *
          rPrimeEulerCorrectionProduct r
            (fun p : Nat.Primes => χ (p : ZMod q)) (shift s) := by
      funext s
      simp [twistedMobiusRectangleExtension, shift, hχ]
    rw [hbranch]
    have hconst : AnalyticOnNhd ℂ
        (fun _ : ℂ => (ArithmeticFunction.moebius r : ℂ)) U :=
      analyticOnNhd_const
    exact (hconst.mul hcoreShift).mul hr

private theorem twistedMobiusRectangle_extension_norm_le
    {q : ℕ} [NeZero q] (hZFR : fixedHalfPlaneProperty)
    {A B X : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hw : Real.exp 8 ≤ Real.log X) (hwX : (Real.log X) ^ B ≤ X)
    (r : ℕ) (hr1 : 1 ≤ r) (hrX : (r : ℝ) ≤ X)
    (hq1 : 1 ≤ q) (hqX : (q : ℝ) ≤ (Real.log X) ^ B)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : |t| ≤ X ^ A)
    {s : ℂ} (hs : s ∈ twistedMobiusRectangleRegion X A) :
    ‖twistedMobiusRectangleExtension r χ t s‖ ≤
      Real.exp (twistedMobiusRectangleErrorExponent A B X) := by
  let w : ℝ := Real.log X
  let z : ℂ := s + (t : ℂ) * Complex.I
  let τ : ℝ := s.im + t
  rcases twistedMobiusRectangle_geometry hw with
    ⟨hwpos, hlogwge8, hdelta0, hdelta64, hdeltaBound⟩
  have hXpos : 0 < X := by
    have hwBpos : 0 < w ^ B := Real.rpow_pos_of_pos hwpos B
    exact lt_of_lt_of_le hwBpos (by simpa [w] using hwX)
  have hXexp4 : Real.exp 4 ≤ X := by
    have hlogXle : Real.log X ≤ X := Real.log_le_self hXpos.le
    calc
      Real.exp 4 ≤ Real.exp 8 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ Real.log X := hw
      _ ≤ X := hlogXle
  have hqleX : (q : ℝ) ≤ X := hqX.trans (by simpa [w] using hwX)
  rcases hs with ⟨hslo, hshi, hsim⟩
  have hslo63 : (63 / 64 : ℝ) ≤ s.re := by
    have hleft : 1 - (1 / 64 : ℝ) ≤ s.re := by
      exact (sub_le_sub_left hdelta64 1).trans hslo
    linarith
  have hlogBound :
      1 + Real.log (4 * (q : ℝ) * (|τ| + 4)) ≤ (A + B + 6) * w := by
    simpa [τ, w] using
      twistedMobiusRectangle_logArgument_bound hA hB hw hwX hq1 hqX t ht
        ⟨hslo, hshi, hsim⟩
  have hargLarge : 1 ≤ 4 * (q : ℝ) * (|τ| + 4) := by
    have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have hτnonneg : 0 ≤ |τ| := abs_nonneg _
    nlinarith
  have hlogArgNonneg :
      0 ≤ 1 + Real.log (4 * (q : ℝ) * (|τ| + 4)) := by
    exact add_nonneg (by norm_num)
      (Real.log_nonneg hargLarge)
  have htheta : 0 <
      FractionalPrimes.Literature.Analytic.explicitLogarithmTheta := by
    exact (reciprocalStripBound hZFR).1
  have hpowerArg :
      (1 + Real.log (4 * (q : ℝ) * (|τ| + 4))) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta ≤
        ((A + B + 6) * w) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta :=
    Real.rpow_le_rpow hlogArgNonneg hlogBound htheta.le
  have hpowerFactor :
      ((A + B + 6) * w) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta =
        (A + B + 6) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta *
        w ^ FractionalPrimes.Literature.Analytic.explicitLogarithmTheta :=
    Real.mul_rpow (by positivity) (by positivity)
  have hbaseExponent : reciprocalStripMajorant q τ ≤
      600 * (A + B + 6) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta *
        w ^ FractionalPrimes.Literature.Analytic.explicitLogarithmTheta := by
    unfold reciprocalStripMajorant
    calc
      600 * (1 + Real.log (4 * (q : ℝ) * (|τ| + 4))) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta ≤
        600 * ((A + B + 6) * w) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta :=
        mul_le_mul_of_nonneg_left hpowerArg (by norm_num)
      _ = 600 * (A + B + 6) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta *
          w ^ FractionalPrimes.Literature.Analytic.explicitLogarithmTheta := by
        rw [hpowerFactor]
        ring
  have hsigmaHi : s.re ≤ 3 / 2 := hshi
  have ⟨_, _, hstrip, _, _, hprincipal⟩ := reciprocalStripBound hZFR
  have hbasePoint : z = (s.re : ℂ) + (τ : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [z, τ, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
  have hrecipPoint := hstrip hq1 χ s.re τ hslo63 hsigmaHi
  have hprincipalPoint := hprincipal hq1 s.re τ hslo63 hsigmaHi
  have hbase :
      ‖(if χ = principalCharacter q then
          continuedDirichletPrincipalReciprocal z
        else (nonprincipalContinuedDirichletLCore χ z)⁻¹)‖ ≤
        Real.exp (600 * (A + B + 6) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta *
          w ^ FractionalPrimes.Literature.Analytic.explicitLogarithmTheta) := by
    by_cases hχ : χ = principalCharacter q
    · simp only [ite_eq_left hχ]
      rw [hbasePoint]
      calc
        ‖continuedDirichletPrincipalReciprocal
            ((s.re : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
            Real.exp (reciprocalStripMajorant q τ) := hprincipalPoint
        _ ≤ _ := Real.exp_le_exp.mpr hbaseExponent
    · simp only [ite_eq_right hχ]
      rw [hbasePoint]
      have hrecipNorm :
          ‖(nonprincipalContinuedDirichletLCore χ
              ((s.re : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ≤
            Real.exp (reciprocalStripMajorant q τ) := by
        simpa [normalizedDirichletFamily, hχ] using hrecipPoint.1
      exact hrecipNorm.trans (Real.exp_le_exp.mpr hbaseExponent)
  have hdelta0' : 0 ≤ twistedMobiusRectangleDelta X := hdelta0.le
  have hleft : 1 - twistedMobiusRectangleDelta X ≤ z.re := by
    simpa [z, Complex.add_re] using hslo
  have hqRemoved := qPrimeEulerCorrectionProduct_norm_le_removed
    hXexp4 hq1 hqleX hdelta0' hdeltaBound hleft
  have hrRemoved := rPrimeEulerCorrectionProduct_norm_le_removed χ
    hXexp4 hr1 hrX hdelta0' hdeltaBound hleft
  let K : ℝ := Real.exp 6 * w ^ 6
  have hKone : 1 ≤ K := by
    dsimp [K]
    have hlogwle : Real.log w ≤ w := Real.log_le_self hwpos.le
    have hwone : 1 ≤ w := by linarith [hlogwge8, hlogwle]
    have hexp : 1 ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
    have hwpow : 1 ≤ w ^ 6 := one_le_pow₀ hwone
    calc
      1 ≤ Real.exp 6 := hexp
      _ = Real.exp 6 * 1 := by ring
      _ ≤ Real.exp 6 * w ^ 6 :=
        mul_le_mul_of_nonneg_left hwpow (by positivity)
  let qFactor : ℂ := if χ = principalCharacter q then
      qPrimeEulerCorrectionProduct q z else 1
  have hqFactor : ‖qFactor‖ ≤ K := by
    by_cases hχ : χ = principalCharacter q
    · simpa [qFactor, hχ, K, w] using hqRemoved
    · simp [qFactor, hχ, K]
      simpa [K] using hKone
  have hrFactor :
      ‖rPrimeEulerCorrectionProduct r
        (fun p : Nat.Primes => χ (p : ZMod q)) z‖ ≤ K := by
    simpa [K, w] using hrRemoved
  have hmu : ‖(ArithmeticFunction.moebius r : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
  have hrepr : twistedMobiusRectangleExtension r χ t s =
      ((ArithmeticFunction.moebius r : ℂ) *
        (if χ = principalCharacter q then
          continuedDirichletPrincipalReciprocal z
        else (nonprincipalContinuedDirichletLCore χ z)⁻¹)) *
        qFactor * rPrimeEulerCorrectionProduct r
          (fun p : Nat.Primes => χ (p : ZMod q)) z := by
    by_cases hχ : χ = principalCharacter q
    · simp [twistedMobiusRectangleExtension, qFactor, z, hχ]
    · simp [twistedMobiusRectangleExtension, qFactor, z, hχ]
  have hcorrectionExp : Real.exp 6 * w ^ 6 =
      Real.exp (6 + 6 * Real.log w) := by
    calc
      Real.exp 6 * w ^ 6 = Real.exp 6 * (Real.exp (Real.log w)) ^ 6 := by
        rw [Real.exp_log (by linarith [hlogwge8])]
      _ = Real.exp 6 * Real.exp (6 * Real.log w) := by
        exact congrArg (fun y : ℝ => Real.exp 6 * y)
          (Real.exp_nat_mul (Real.log w) 6).symm
      _ = Real.exp (6 + 6 * Real.log w) := by rw [← Real.exp_add]
  have hcombine :
      Real.exp (600 * (A + B + 6) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta *
          w ^ FractionalPrimes.Literature.Analytic.explicitLogarithmTheta) * K * K =
        Real.exp (twistedMobiusRectangleErrorExponent A B X) := by
    dsimp [K]
    rw [hcorrectionExp, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [twistedMobiusRectangleErrorExponent]
    rw [show Real.log X = w by rfl]
    ring
  rw [hrepr]
  calc
    ‖((ArithmeticFunction.moebius r : ℂ) *
        (if χ = principalCharacter q then
          continuedDirichletPrincipalReciprocal z
        else (nonprincipalContinuedDirichletLCore χ z)⁻¹)) *
        qFactor * rPrimeEulerCorrectionProduct r
          (fun p : Nat.Primes => χ (p : ZMod q)) z‖ =
      ‖(ArithmeticFunction.moebius r : ℂ)‖ *
        ‖(if χ = principalCharacter q then
          continuedDirichletPrincipalReciprocal z
        else (nonprincipalContinuedDirichletLCore χ z)⁻¹)‖ *
        ‖qFactor‖ *
        ‖rPrimeEulerCorrectionProduct r
          (fun p : Nat.Primes => χ (p : ZMod q)) z‖ := by
            simp only [norm_mul]
    _ ≤ 1 * Real.exp (600 * (A + B + 6) ^
          FractionalPrimes.Literature.Analytic.explicitLogarithmTheta *
          w ^ FractionalPrimes.Literature.Analytic.explicitLogarithmTheta) * K * K := by
      gcongr
    _ = Real.exp (twistedMobiusRectangleErrorExponent A B X) := by
      simpa only [one_mul] using hcombine

/-- The complete approved `lrc:twisted-rectangle` assertion. The displayed
extension retains the principal regularization and the distinct modulus and
multiplier Euler corrections; its restriction to `Re(s)>1` is the original
shifted, filtered Möbius Dirichlet series. -/
theorem twistedMobiusRectangle
    {q : ℕ} [NeZero q] (hZFR : fixedHalfPlaneProperty)
    {A B X : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hw : Real.exp 8 ≤ Real.log X)
    (hwX : (Real.log X) ^ B ≤ X)
    (r : ℕ) (hr1 : 1 ≤ r) (hrX : (r : ℝ) ≤ X)
    (hq1 : 1 ≤ q) (hqX : (q : ℝ) ≤ (Real.log X) ^ B)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : |t| ≤ X ^ A) :
    (∀ s : ℂ, 1 < s.re →
      twistedMobiusRectangleExtension r χ t s =
        LSeries (twistedMobiusRectangleCoefficient r χ t) s) ∧
    AnalyticOnNhd ℂ (twistedMobiusRectangleExtension r χ t)
      (twistedMobiusRectangleRegion X A) ∧
    (∀ s ∈ twistedMobiusRectangleRegion X A,
      ‖twistedMobiusRectangleExtension r χ t s‖ ≤
        Real.exp (twistedMobiusRectangleErrorExponent A B X)) ∧
    (∀ n : ℕ, ‖twistedMobiusRectangleCoefficient r χ t n‖ ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact twistedMobiusRectangleExtension_eq_series r
      (by omega) χ t hs
  · have ⟨_, _, hdelta0, hdelta64, _⟩ :=
      twistedMobiusRectangle_geometry hw
    apply (twistedMobiusRectangleExtension_analyticOnNhd hZFR r χ t).mono
    intro s hs
    rcases hs with ⟨hslo, hshi, hsim⟩
    have hsleft : (63 / 64 : ℝ) ≤ s.re := by
      calc
        (63 / 64 : ℝ) = 1 - 1 / 64 := by norm_num
        _ ≤ 1 - twistedMobiusRectangleDelta X :=
          sub_le_sub_left hdelta64 1
        _ ≤ s.re := hslo
    exact lt_of_lt_of_le (by norm_num : (7 / 8 : ℝ) < 63 / 64) hsleft
  · intro s hs
    exact twistedMobiusRectangle_extension_norm_le hZFR hA hB hw hwX
      r hr1 hrX hq1 hqX χ t ht hs
  · exact twistedMobiusRectangleCoefficient_norm_le_one r χ t

#print axioms twistedMobiusRectangle

#print axioms twistedMobiusRectangleExtension_analyticOnNhd

#print axioms twistedMobiusRectangleExtension_eq_series

end FractionalPrimes.Literature.Reciprocal

end
