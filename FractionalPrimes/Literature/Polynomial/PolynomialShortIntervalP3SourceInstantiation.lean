module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalConditionalComponentAdapter
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalTypeIInverseAssembly
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalTypeIIInverseAssembly
public import FractionalPrimes.Literature.Uniformity.CramerShortDivisor

/-!
# Source instantiation of the conditional-integer component selection

This module connects the finite P3 selector to the exact arithmetic
decomposition and short-divisor approximation data used by the blueprint.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

/-- The fixed model supplied by `cramerShortDivisorApproximation`, viewed
as a complex-valued function on positive integers. -/
noncomputable def cramerShortDivisorModel (X : ℕ) (b : ℕ → ℝ) :
    ComplexPositiveIntegerFunction :=
  fun n => (shortDivisorSum ((X : ℝ) ^ (1 / 16 : ℝ)) b n : ℂ)

theorem cramerShortDivisorModel_zeroExtension_eq
    (X : ℕ) (b : ℕ → ℝ) (n : ℤ) (hn : 0 < n) :
    complexPositiveIntegerZeroExtension (cramerShortDivisorModel X b) n =
      (shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs : ℂ) := by
  have hnatAbsZ : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn.le
  have htoNatZ : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
  have hnatAbs : n.natAbs = n.toNat := by
    exact_mod_cast hnatAbsZ.trans htoNatZ.symm
  simp [complexPositiveIntegerZeroExtension, cramerShortDivisorModel,
    shortDivisorSumNat, hn, hnatAbs]

/-- The exact arithmetic decomposition extends to the integer interval of a
short block contained in `(X,2X]`. -/
theorem elementaryDecomposition_zeroExtension_on_interval
    (X H : ℕ) (g : ComplexPositiveIntegerFunction)
    (D : ElementaryArithmeticTypeDecomposition (X : ℝ) g)
    [DecidableEq D.Index]
    (hX : 3 ≤ X) (hHleX : H ≤ X) :
    ∀ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      complexPositiveIntegerZeroExtension g n =
        ∑ i ∈ D.indices,
          complexPositiveIntegerZeroExtension (D.component i) n := by
  intro n hn
  have hb := (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) n).mp hn
  have hnpos : 0 < n := by
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast (show 0 < X by omega)
    have hnposReal : (0 : ℝ) < (n : ℝ) := lt_trans hXpos hb.1
    exact_mod_cast hnposReal
  let m : PositiveInteger := ⟨n.toNat, by omega⟩
  have hmcast : (m.1 : ℤ) = n := by
    exact Int.toNat_of_nonneg (le_of_lt hnpos)
  have hmreal : (m.1 : ℝ) = (n : ℝ) := by exact_mod_cast hmcast
  have hXreal : 0 < (X : ℝ) := by positivity
  have hHreal : (H : ℝ) ≤ (X : ℝ) := by exact_mod_cast hHleX
  have hmlo : (X : ℝ) / 2 ≤ (m.1 : ℝ) := by
    rw [hmreal]
    linarith [hb.1]
  have hmhi : (m.1 : ℝ) ≤ 4 * (X : ℝ) := by
    rw [hmreal]
    linarith [hb.2, hHreal]
  have hdecomp := D.decomposition m hmlo hmhi
  have hcasted :
      complexPositiveIntegerZeroExtension g (m.1 : ℤ) =
        ∑ i ∈ D.indices,
          complexPositiveIntegerZeroExtension (D.component i) (m.1 : ℤ) := by
    simpa only [complexPositiveIntegerZeroExtension_natCast] using hdecomp
  rw [hmcast] at hcasted
  exact hcasted

/-- The zero function is a legal type-I component at the exact conditional
cutoff whenever `0 < δ < 1`. -/
theorem zero_conditionalTypeI
    (X : ℕ) (δ : ℝ) (hX : 3 ≤ X)
    (hδpos : 0 < δ) (hδlt : δ < 1) :
    typeIFunction δ (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ))
      (fun _ : PositiveInteger => (0 : ℂ)) := by
  have hbudget : (1 : ℝ) ^ 2 ≤ δ⁻¹ := by
    have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδpos).2 (le_of_lt hδlt)
    simpa using hinv
  have hcut : 1 ≤ decompositionC * (X : ℝ) ^ (5 / 8 : ℝ) := by
    have hXone : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
    have hpow : (1 : ℝ) ≤ (X : ℝ) ^ (5 / 8 : ℝ) :=
      Real.one_le_rpow hXone (by norm_num)
    have hC : (1 : ℝ) ≤ decompositionC := by
      unfold decompositionC
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
      have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 :=
        one_le_pow₀ (by norm_num)
      calc
        1 = 1 * 1 := by ring
        _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
          mul_le_mul h2 h81 (by norm_num) (by positivity)
    calc
      1 = 1 * 1 := by ring
      _ ≤ decompositionC * (X : ℝ) ^ (5 / 8 : ℝ) :=
        mul_le_mul hC hpow (by norm_num) (by positivity)
  have hbase := arithmeticShortDivisorSum_typeI
    δ (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ)) 1
    (fun _ : PositiveInteger => (0 : ℂ)) hδpos hδlt hcut (by norm_num)
    hbudget (by simp)
  have hzero : arithmeticShortDivisorSum
      (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ))
      (fun _ : PositiveInteger => (0 : ℂ)) =
        (fun _ : PositiveInteger => (0 : ℂ)) := by
    funext n
    simp [arithmeticShortDivisorSum]
  simpa [hzero] using hbase

/-- P3 applied to the arithmetic decomposition selected by PTW for Möbius,
with a harmless zero type-I summand. The selected index is retained so the
later Type-II branch can use the designation in this very decomposition. -/
theorem exists_mobius_conditionalInteger_selectedComponent
    (X H Dexp : ℕ)
    (D : ElementaryArithmeticTypeDecomposition (X : ℝ)
      mobiusComplexPositiveFunction)
    [DecidableEq D.Index] (A δ : ℝ) (P : Polynomial ℝ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHleX : H ≤ X)
    (hL : 2 ≤ Real.log (X : ℝ))
    (hδpos : 0 < δ) (hδlt : δ < 1)
    (hDelta : δ = (Real.log (X : ℝ)) ^ (-(Dexp : ℝ)))
    (hThreshold : 4 * decompositionC <
      (Real.log (X : ℝ)) ^ ((Dexp : ℝ) - A - (decompositionB : ℝ)))
    (hDeltaType : δ ≤ decompositionDelta (X : ℝ))
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖) :
    ∃ f : ComplexPositiveIntegerFunction,
      conditionalIntegerComponentType (X : ℝ) δ f ∧
      δ * (H : ℝ) < typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ) ∧
      (f = (fun _ : PositiveInteger => (0 : ℂ)) ∨
        ∃ i, i ∈ D.indices ∧ f = D.component i) := by
  classical
  let extra : ComplexPositiveIntegerFunction := fun _ => 0
  let w : ℤ → ℂ := fun n => (paperMu n : ℂ)
  let r : ℤ → ℂ := fun _ => 0
  have hDsum := elementaryDecomposition_zeroExtension_on_interval
    X H mobiusComplexPositiveFunction D hX hHleX
  have hdecomp : ∀ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      w n =
        ((∑ i ∈ D.indices,
          complexPositiveIntegerZeroExtension (D.component i) n) +
          complexPositiveIntegerZeroExtension extra n) + r n := by
    intro n hn
    have hnpos : 0 < n := by
      have hb := (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) n).mp hn
      have hXpos : (0 : ℝ) < (X : ℝ) := by
        exact_mod_cast (show 0 < X by omega)
      exact_mod_cast lt_trans hXpos hb.1
    have hw : w n =
        complexPositiveIntegerZeroExtension mobiusComplexPositiveFunction n := by
      simp [w, paperMu, mobiusWeight, mobiusComplexPositiveFunction,
        complexPositiveIntegerZeroExtension, hnpos]
    rw [hw, hDsum n hn]
    simp [extra, r, complexPositiveIntegerZeroExtension, hnpos]
  have hresidual :
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        r n * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
          (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) / 4 := by
    simp [r]
    positivity
  have hExtraType := zero_conditionalTypeI X δ hX hδpos hδlt
  obtain ⟨j, hj, htype, hcorrelation⟩ :=
    exists_conditionalIntegerSelectedComponent X H A δ Dexp
      mobiusComplexPositiveFunction D extra w r P hX hH hHleX hL hDelta
      hThreshold hDeltaType hExtraType hdecomp hresidual (by simpa [w] using hLarge)
  cases j with
  | none =>
      exact ⟨extra, by simpa [extra] using htype,
        by simpa [extra] using hcorrelation, Or.inl rfl⟩
  | some i =>
      have hiImage : some i ∈ D.indices.image (some : D.Index → Option D.Index) := by
        simpa using hj
      have hi : i ∈ D.indices := by
        rcases Finset.mem_image.mp hiImage with ⟨i', hi', heq⟩
        exact Option.some.inj heq ▸ hi'
      exact ⟨D.component i, htype, hcorrelation, Or.inr ⟨i, hi, rfl⟩⟩

/-- The logarithmic definition `δ=(log X)^(-D)` gives exactly the inverse
parameter used in the Cramér-model type-I budget. -/
theorem conditionalDelta_inv
    (X Dexp : ℕ) (δ : ℝ)
    (hL : 0 < Real.log (X : ℝ))
    (hDelta : δ = (Real.log (X : ℝ)) ^ (-(Dexp : ℝ))) :
    δ⁻¹ = (Real.log (X : ℝ)) ^ (Dexp : ℝ) := by
  rw [hDelta, Real.rpow_neg hL.le]
  exact inv_inv _

/-- The approved short-divisor approximation remains a quarter-sized error
after multiplication by the polynomial phase, provided the source threshold
`(log X)^2 ≥ 4 C_app` holds. -/
theorem cramerApproximation_phaseError_le_quarter
    (A : ℝ) (X H : ℕ) (P : Polynomial ℝ)
    (hL : 2 ≤ Real.log (X : ℝ))
    (hApp : 4 * cramerApproximationConstant (A + 2) (1 / 16 : ℝ) ≤
      (Real.log (X : ℝ)) ^ 2)
    (b : ℕ → ℝ)
    (hApprox :
      (∑ n ∈ Finset.Ioc X (X + H),
        |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
          shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n|) ≤
        cramerApproximationConstant (A + 2) (1 / 16 : ℝ) *
          (H : ℝ) * (Real.log X) ^ (-(A + 2))) :
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      (((shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs -
        paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
        unitFrequencyPhase (P.eval (n : ℝ)))‖ ≤
      (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) / 4 := by
  classical
  let L : ℝ := Real.log (X : ℝ)
  let Capp : ℝ := cramerApproximationConstant (A + 2) (1 / 16 : ℝ)
  let Iint : Finset ℤ := Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hCappNonneg : 0 ≤ Capp := by
    dsimp [Capp, cramerApproximationConstant]
    positivity
  have hfloorX : Int.floor (X : ℝ) = (X : ℤ) := by norm_num
  have hfloorEnd : Int.floor ((X : ℝ) + (H : ℝ)) = ((X + H : ℕ) : ℤ) := by
    rw [← Nat.cast_add]
    norm_num
  have hinterval : realIntegerInterval (X : ℝ) (H : ℝ) = Iint := by
    ext n
    simp only [realIntegerInterval, Iint, Finset.mem_Ico, Finset.mem_Ioc,
      hfloorX, hfloorEnd]
    omega
  have hApproxInt :
      (∑ n ∈ Iint,
        |paperShortBlockCramerWeight (X : ℝ) n -
          shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs|) ≤
        Capp * (H : ℝ) * L ^ (-(A + 2)) := by
    have hsum := cramerShortInterval_sum_nat_eq_int X H (fun n : ℤ =>
      |paperShortBlockCramerWeight (X : ℝ) n -
        shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs|)
    calc
      (∑ n ∈ Iint,
          |paperShortBlockCramerWeight (X : ℝ) n -
            shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs|) =
          ∑ n ∈ Finset.Ioc X (X + H),
            |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
              shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n| := by
        simpa [Iint, Nat.cast_add] using hsum.symm
      _ ≤ cramerApproximationConstant (A + 2) (1 / 16 : ℝ) *
          (H : ℝ) * (Real.log X) ^ (-(A + 2)) := hApprox
      _ = Capp * (H : ℝ) * L ^ (-(A + 2)) := by rfl
  have hRealScale : Capp * L ^ (-(A + 2)) ≤
      (1 / 4 : ℝ) * L ^ (-A) := by
    have hpow : L ^ (-(A + 2 : ℝ)) = L ^ (-2 : ℝ) * L ^ (-A) := by
      rw [show -(A + 2 : ℝ) = (-2 : ℝ) + (-A) by ring,
        Real.rpow_add hLpos]
    have hInv : Capp * L ^ (-2 : ℝ) ≤ 1 / 4 := by
      rw [Real.rpow_neg hLpos.le]
      have hdiv : Capp / (L ^ 2) ≤ 1 / 4 := by
        apply (div_le_iff₀ (by positivity : 0 < L ^ 2)).2
        nlinarith [hApp]
      simpa [div_eq_mul_inv] using hdiv
    calc
      Capp * L ^ (-(A + 2 : ℝ)) =
          (Capp * L ^ (-2 : ℝ)) * L ^ (-A) := by rw [hpow]; ring
      _ ≤ (1 / 4 : ℝ) * L ^ (-A) :=
        mul_le_mul_of_nonneg_right hInv (Real.rpow_nonneg hLpos.le _)
  have hApproxQuarter : Capp * (H : ℝ) * L ^ (-(A + 2 : ℝ)) ≤
      (H : ℝ) * L ^ (-A) / 4 := by
    calc
      Capp * (H : ℝ) * L ^ (-(A + 2 : ℝ)) =
          (H : ℝ) * (Capp * L ^ (-(A + 2 : ℝ))) := by ring
      _ ≤ (H : ℝ) * ((1 / 4 : ℝ) * L ^ (-A)) :=
        mul_le_mul_of_nonneg_left hRealScale (by positivity)
      _ = (H : ℝ) * L ^ (-A) / 4 := by ring
  calc
    _ ≤ ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        ‖(((shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs -
            paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
            unitFrequencyPhase (P.eval (n : ℝ)))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Iint,
        |paperShortBlockCramerWeight (X : ℝ) n -
          shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs| := by
      rw [hinterval]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [norm_mul, norm_unitFrequencyPhase, mul_one, Complex.norm_real]
      rw [Real.norm_eq_abs]
      rw [show shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs -
          paperShortBlockCramerWeight (X : ℝ) n =
            -(paperShortBlockCramerWeight (X : ℝ) n -
              shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs) by ring,
        abs_neg]
    _ ≤ Capp * (H : ℝ) * L ^ (-(A + 2 : ℝ)) := hApproxInt
    _ ≤ (H : ℝ) * L ^ (-A) / 4 := hApproxQuarter

/-- The fixed `T_X` supplied by the approved approximation theorem, including
its coefficient support/size clauses and the phase-weighted quarter-error.
The support exponent is the source's fixed `1/16`, independent of `H`. -/
theorem exists_cramerApproximation_phaseError
    (A : ℝ) (X H : ℕ) (P : Polynomial ℝ)
    (hA : 0 < A) (hX : 3 ≤ X)
    (hHlower : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ))
    (hL : 2 ≤ Real.log (X : ℝ))
    (hApp : 4 * cramerApproximationConstant (A + 2) (1 / 16 : ℝ) ≤
      (Real.log (X : ℝ)) ^ 2) :
    ∃ b : ℕ → ℝ,
      (∀ d, b d ≠ 0 → 0 < d ∧ (d : ℝ) ≤ (X : ℝ) ^ (1 / 16 : ℝ)) ∧
      (∀ d, |b d| ≤ Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ)) ∧
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        (((shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs -
          paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
          unitFrequencyPhase (P.eval (n : ℝ)))‖ ≤
        (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) / 4 := by
  obtain ⟨b, hbSupport, hbCoeff, hApprox⟩ :=
    cramerShortDivisorApproximation (A + 2) (1 / 16 : ℝ) X H
      (by linarith) hX (by norm_num) (by norm_num) hHlower
  exact ⟨b, hbSupport, hbCoeff,
    cramerApproximation_phaseError_le_quarter A X H P hL hApp
      b hApprox⟩

/-- The exact negative Cramér model is a type-I function at the source
parameter `δ`, after enlarging its short-divisor support to the conditional
integer cutoff `C X^(5/8)`. The level hypothesis is the source threshold
`(log X)^(D-4/5) ≥ exp(26)`. -/
theorem cramerNegativeModel_typeI
    (X Dexp : ℕ) (δ : ℝ) (b : ℕ → ℝ)
    (hX : 3 ≤ X) (hL : 2 ≤ Real.log (X : ℝ))
    (hδpos : 0 < δ) (hδlt : δ < 1)
    (hδinv : δ⁻¹ = (Real.log (X : ℝ)) ^ (Dexp : ℝ))
    (hLevel : Real.exp 26 ≤
      (Real.log (X : ℝ)) ^ ((Dexp : ℝ) - 4 / 5))
    (hb : ∀ d, |b d| ≤ Real.exp 13 *
      (Real.log X) ^ (2 / 5 : ℝ)) :
    typeIFunction δ (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ))
      (-cramerShortDivisorModel X b) := by
  classical
  let L : ℝ := Real.log (X : ℝ)
  let Y : ℝ := (X : ℝ) ^ (1 / 16 : ℝ)
  let W : ℝ := Real.exp 13 * L ^ (2 / 5 : ℝ)
  let bComplex : ComplexPositiveIntegerFunction := fun n => (b n.1 : ℂ)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  have hXone : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hWone : 1 ≤ W := by
    dsimp [W]
    have hexp : 1 ≤ Real.exp 13 := Real.one_le_exp (by norm_num)
    have hpow : 1 ≤ L ^ (2 / 5 : ℝ) :=
      Real.one_le_rpow hLone (by norm_num)
    calc
      1 = 1 * 1 := by ring
      _ ≤ Real.exp 13 * L ^ (2 / 5 : ℝ) :=
        mul_le_mul hexp hpow (by norm_num) (by positivity)
  have hbComplex : ∀ n, ‖bComplex n‖ ≤ W := by
    intro n
    dsimp [bComplex, W, L]
    rw [Complex.norm_real]
    exact hb n.1
  have hWsq : W ^ 2 ≤ δ⁻¹ := by
    have hpowSquare : (L ^ (2 / 5 : ℝ)) ^ 2 = L ^ (4 / 5 : ℝ) := by
      rw [← Real.rpow_natCast (L ^ (2 / 5 : ℝ)) 2,
        ← Real.rpow_mul hLpos.le]
      congr 1
      norm_num
    have hexpSquare : (Real.exp 13) ^ 2 = Real.exp 26 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    have hWidentity : W ^ 2 = Real.exp 26 * L ^ (4 / 5 : ℝ) := by
      dsimp [W]
      rw [mul_pow, hexpSquare, hpowSquare]
    have hlevelProduct : Real.exp 26 * L ^ (4 / 5 : ℝ) ≤
        L ^ ((Dexp : ℝ) - 4 / 5) * L ^ (4 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hLevel (Real.rpow_nonneg hLpos.le _)
    have hpower : L ^ ((Dexp : ℝ) - 4 / 5) * L ^ (4 / 5 : ℝ) =
        L ^ (Dexp : ℝ) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    calc
      W ^ 2 = Real.exp 26 * L ^ (4 / 5 : ℝ) := hWidentity
      _ ≤ L ^ ((Dexp : ℝ) - 4 / 5) * L ^ (4 / 5 : ℝ) := hlevelProduct
      _ = L ^ (Dexp : ℝ) := hpower
      _ = δ⁻¹ := by simpa [L] using hδinv.symm
  have hYge : 1 ≤ Y := by
    dsimp [Y]
    exact Real.one_le_rpow hXone (by norm_num)
  have hYle : Y ≤ decompositionC * (X : ℝ) ^ (5 / 8 : ℝ) := by
    dsimp [Y]
    have hXrpow : (X : ℝ) ^ (1 / 16 : ℝ) ≤
        (X : ℝ) ^ (5 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
    have hCge : 1 ≤ decompositionC := by
      unfold decompositionC
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
      have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 :=
        one_le_pow₀ (by norm_num)
      calc
        1 = 1 * 1 := by ring
        _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
          mul_le_mul h2 h81 (by norm_num) (by positivity)
    calc
      (X : ℝ) ^ (1 / 16 : ℝ) ≤ (X : ℝ) ^ (5 / 8 : ℝ) := hXrpow
      _ = 1 * (X : ℝ) ^ (5 / 8 : ℝ) := by ring
      _ ≤ decompositionC * (X : ℝ) ^ (5 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hCge
          (Real.rpow_nonneg (by positivity) _)
  have hmodel : cramerShortDivisorModel X b =
      arithmeticShortDivisorSum Y bComplex := by
    funext n
    exact shortDivisorSum_complex Y b n
  have hnegativeModel : -cramerShortDivisorModel X b =
      -arithmeticShortDivisorSum Y bComplex := by
    funext n
    exact congrArg Neg.neg (congrFun hmodel n)
  have hbase :=
    (arithmeticShortDivisorSum_typeI_both_signs δ Y W bComplex
      hδpos hδlt hYge hWone hWsq hbComplex).2
  rw [← hnegativeModel] at hbase
  exact typeIFunction_mono hbase hδpos le_rfl hYle

/-- Instantiate P3 with the von Mangoldt decomposition selected by PTW, the fixed
`1/16` Cramér approximation, and the negative type-I model term. -/
theorem exists_lambda_conditionalInteger_selectedComponent
    (X H Dexp : ℕ)
    (D : ElementaryArithmeticTypeDecomposition (X : ℝ)
      vonMangoldtComplexPositiveFunction)
    [DecidableEq D.Index] (A δ : ℝ) (P : Polynomial ℝ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHleX : H ≤ X)
    (hA : 0 < A)
    (hHlower : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ))
    (hL : 2 ≤ Real.log (X : ℝ))
    (hδpos : 0 < δ) (hδlt : δ < 1)
    (hDelta : δ = (Real.log (X : ℝ)) ^ (-(Dexp : ℝ)))
    (hThreshold : 4 * decompositionC <
      (Real.log (X : ℝ)) ^ ((Dexp : ℝ) - A - (decompositionB : ℝ)))
    (hDeltaType : δ ≤ decompositionDelta (X : ℝ))
    (hApp : 4 * cramerApproximationConstant (A + 2) (1 / 16 : ℝ) ≤
      (Real.log (X : ℝ)) ^ 2)
    (hLevel : Real.exp 26 ≤
      (Real.log (X : ℝ)) ^ ((Dexp : ℝ) - 4 / 5))
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        ((paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) *
            unitFrequencyPhase (P.eval (n : ℝ))‖) :
    ∃ b : ℕ → ℝ,
      (∀ d, b d ≠ 0 → 0 < d ∧
        (d : ℝ) ≤ (X : ℝ) ^ (1 / 16 : ℝ)) ∧
      (∀ d, |b d| ≤ Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ)) ∧
      ∃ f : ComplexPositiveIntegerFunction,
        conditionalIntegerComponentType (X : ℝ) δ f ∧
        δ * (H : ℝ) < typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ) ∧
        (f = -cramerShortDivisorModel X b ∨
          ∃ i, i ∈ D.indices ∧ f = D.component i) := by
  classical
  have hDeltaInv := conditionalDelta_inv X Dexp δ (by linarith) hDelta
  obtain ⟨b, hbSupport, hbCoeff, hError⟩ :=
    exists_cramerApproximation_phaseError A X H P hA hX hHlower hL hApp
  let extra : ComplexPositiveIntegerFunction := -cramerShortDivisorModel X b
  let w : ℤ → ℂ := fun n =>
    (paperLambda n : ℂ) - (paperShortBlockCramerWeight (X : ℝ) n : ℂ)
  let r : ℤ → ℂ := fun n =>
    ((shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs -
      paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)
  have hDsum := elementaryDecomposition_zeroExtension_on_interval
    X H vonMangoldtComplexPositiveFunction D hX hHleX
  have hdecomp : ∀ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      w n =
        ((∑ i ∈ D.indices,
          complexPositiveIntegerZeroExtension (D.component i) n) +
          complexPositiveIntegerZeroExtension extra n) + r n := by
    intro n hn
    have hnpos : 0 < n := by
      have hb := (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) n).mp hn
      have hXpos : (0 : ℝ) < (X : ℝ) := by
        exact_mod_cast (show 0 < X by omega)
      exact_mod_cast lt_trans hXpos hb.1
    have htarget : (paperLambda n : ℂ) =
        complexPositiveIntegerZeroExtension vonMangoldtComplexPositiveFunction n := by
      simp [paperLambda, vonMangoldtWeight_def,
        vonMangoldtComplexPositiveFunction,
        complexPositiveIntegerZeroExtension, hnpos]
    have hmodelExt := cramerShortDivisorModel_zeroExtension_eq X b n hnpos
    have hextra : complexPositiveIntegerZeroExtension extra n =
        -((shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ)) b n.natAbs : ℝ) : ℂ) := by
      have hnegExt : complexPositiveIntegerZeroExtension extra n =
          -complexPositiveIntegerZeroExtension
            (cramerShortDivisorModel X b) n := by
        simp [extra, complexPositiveIntegerZeroExtension, hnpos]
      rw [hnegExt, hmodelExt]
    dsimp [w, r]
    rw [htarget, hDsum n hn, hextra]
    push_cast
    ring
  have hExtraType := cramerNegativeModel_typeI X Dexp δ b hX hL
    hδpos hδlt hDeltaInv hLevel hbCoeff
  have hresidual :
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        r n * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
          (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) / 4 := by
    simpa [r] using hError
  obtain ⟨j, hj, htype, hcorrelation⟩ :=
    exists_conditionalIntegerSelectedComponent X H A δ Dexp
      vonMangoldtComplexPositiveFunction D extra w r P hX hH hHleX hL hDelta
      hThreshold hDeltaType hExtraType hdecomp hresidual (by simpa [w] using hLarge)
  refine ⟨b, hbSupport, hbCoeff, ?_⟩
  cases j with
  | none =>
      exact ⟨extra, by simpa [extra] using htype,
        by simpa [extra] using hcorrelation, Or.inl rfl⟩
  | some i =>
      have hiImage : some i ∈ D.indices.image (some : D.Index → Option D.Index) := by
        simpa using hj
      have hi : i ∈ D.indices := by
        rcases Finset.mem_image.mp hiImage with ⟨i', hi', heq⟩
        exact Option.some.inj heq ▸ hi'
      exact ⟨D.component i, htype, hcorrelation, Or.inr ⟨i, hi, rfl⟩⟩

/-! A designation is a source-construction output.  The third value is
reserved for the selected type-II branch and retains the original-factor
exponent cap; it is not inferred from the untagged component disjunction. -/
def restrictedPTWDesignationEvidence (X : ℝ)
    (f : ComplexPositiveIntegerFunction) (tag : Fin 3) : Prop :=
  if tag.val = 0 then
    typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ)) f
  else if tag.val = 1 then
    typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ)) f
  else
    ∃ (z c : ℝ) (fs : List (DyadicArithmeticFactor X))
      (α : Fin fs.length → ℝ),
      (∀ i, 0 ≤ α i) ∧
      (∑ i, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
          dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i) ∧
      (∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ)) ∧
      largeTypeIIDyadicComponentData z c (decompositionDelta X) f fs α ∧
      (∀ i, α i < (3 / 8 : ℝ))

/-- The exact twisted-prefix conclusion associated with a retained source
designation. Only the designated type-II tag carries a bound. -/
def restrictedPTWDesignatedPrefixConclusion
    (X H : ℕ) (a _η Ctw : ℝ)
    (f : ComplexPositiveIntegerFunction) (tag : Fin 3) : Prop :=
  if tag.val = 2 then
    ∀ T : ℝ,
      (X : ℝ) / (H : ℝ) * (Real.log (X : ℝ)) ^ (50 * a) ≤ |T| →
      |T| ≤ (X : ℝ) ^ a →
      residuePrefixEnvelope X H
        (fun n => complexPositiveIntegerZeroExtension f n *
          archimedeanTwist T (n : ℝ))
        ((Real.log (X : ℝ)) ^ a) ≤
        Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a)
  else True

/-- The exact PTW contract at the source threshold value `aStar = a_*^P(η)`.
The chosen decomposition and its per-component designation are independent
of the short length and twist. The prefix estimate is attached only to the
designated type-II tag, which retains the source's strict exponent cap. -/
structure RestrictedPTWSelection (X : ℕ) (aStar a η Ctw : ℝ)
    (g : ComplexPositiveIntegerFunction) where
  threshold_ge_one : 1 ≤ aStar
  threshold_le_a : aStar ≤ a
  decomposition : ElementaryArithmeticTypeDecomposition (X : ℝ) g
  designationTag : ∀ i, i ∈ decomposition.indices → Fin 3
  designationEvidence : ∀ i (hi : i ∈ decomposition.indices),
    restrictedPTWDesignationEvidence (X : ℝ) (decomposition.component i)
      (designationTag i hi)
  twistedPrefix : ∀ (H : ℕ),
    (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
    (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
    ∀ i (hi : i ∈ decomposition.indices),
      restrictedPTWDesignatedPrefixConclusion X H a η Ctw
        (decomposition.component i) (designationTag i hi)

/-- The exact common hypotheses used by the checked Type-I/Type-I₂ and
Type-II contradiction assemblies in `lupo:conditional-integer`. This record
only packages source premises; it does not replace any inverse implication. -/
structure ConditionalIntegerInverseContext
    (d X H K c D E a b : ℕ) (A a₀ η δ Cpm Ctw Astar : ℝ)
    (P : Polynomial ℝ) (w : ℤ → ℂ) where
  hInv : arithmeticInverseTasksWithConstants d K c
  hd : 1 ≤ d
  hX : 3 ≤ X
  hA : 0 < A
  hη : 0 < η
  hηmax : η < 3 / 16
  hDsource : A + (b : ℝ) + 5 < (D : ℝ)
  hE : E = 2 * c * D + 3
  hEa : E < a
  hAgtDE : (D : ℝ) + (E : ℝ) + 3 < (a : ℝ)
  hAgtD : d + 3 < a
  ha₀ : a₀ = A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3
  hL : 2 ≤ Real.log (X : ℝ)
  hδpos : 0 < δ
  hδsmall : δ < min (1 / 2) ((Real.log (X : ℝ))⁻¹)
  hδinv : δ⁻¹ = (Real.log (X : ℝ)) ^ (D : ℝ)
  hDelta : δ = (Real.log (X : ℝ)) ^ (-(D : ℝ))
  hDeltaType : δ ≤ decompositionDelta (X : ℝ)
  hThreshold : 4 * decompositionC <
    (Real.log (X : ℝ)) ^ ((D : ℝ) - A - (decompositionB : ℝ))
  hHlower : (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ)
  hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η)
  hApp : 4 * cramerApproximationConstant (A + 2) (1 / 16 : ℝ) ≤
    (Real.log (X : ℝ)) ^ 2
  hLevel : Real.exp 26 ≤ (Real.log (X : ℝ)) ^ ((D : ℝ) - 4 / 5)
  hCtype : 1 ≤ decompositionC
  hScaleBudget :
    2 * (K : ℝ) * decompositionC * (Real.log (X : ℝ)) ^ (c * D) <
      (X : ℝ) ^ η
  hP : P.natDegree ≤ d
  hL3modulus : (d.factorial : ℝ) * (K : ℝ) ≤
    (Real.log (X : ℝ)) ^ 3
  hL3variation : (d.factorial : ℝ) *
    (1 + 2 * Real.pi * binomialVariationConstant d) * (K : ℝ) ≤
      (Real.log (X : ℝ)) ^ 3
  hL3q : (d.factorial : ℝ) * (K : ℝ) ≤ (Real.log (X : ℝ)) ^ 3
  hL3T : 2 * Real.pi * (d : ℝ) * (K : ℝ) ≤ (Real.log (X : ℝ)) ^ 3
  hL3tv : (d.factorial : ℝ) *
    (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) * (K : ℝ) ^ 2 ≤
      (Real.log (X : ℝ)) ^ 3
  hLE : (Real.log (X : ℝ)) ^ E ≤ X
  hCpmPos : 0 < Cpm
  hCpmSmall : 2 * Cpm < (Real.log (X : ℝ)) ^ 2
  hMuPrefix :
    residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
        ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
      Cpm * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀)
  hCramerPrefix :
    residuePrefixEnvelope X H
        (fun n => (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
        ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
      Cpm * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀)
  hw : w = (fun n => (paperMu n : ℂ)) ∨
    w = (fun n => (paperLambda n : ℂ) -
      (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
  muPTWSelection : RestrictedPTWSelection X Astar (a : ℝ) η Ctw
    mobiusComplexPositiveFunction
  lambdaPTWSelection : RestrictedPTWSelection X Astar (a : ℝ) η Ctw
    vonMangoldtComplexPositiveFunction
  hCtwPos : 0 < Ctw
  hCtwSmall : Ctw < (Real.log (X : ℝ)) ^ 2
  hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      w n * unitFrequencyPhase (P.eval (n : ℝ))‖

/-- Apply the inverse contradiction to a selected Type-I or Type-I₂ branch.
This helper needs no twist estimate. -/
theorem selectedTypeIOrTypeI2Component_refutes
    {d X H K c D E a b : ℕ} {A a₀ η δ Cpm Ctw Astar : ℝ}
    {P : Polynomial ℝ} {w : ℤ → ℂ}
    (ctx : ConditionalIntegerInverseContext d X H K c D E a b
      A a₀ η δ Cpm Ctw Astar P w)
    (f : ComplexPositiveIntegerFunction)
    (hType : typeIFunction δ (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ)) f ∨
      typeI2Function δ (decompositionC * (X : ℝ) ^ (7 / 16 : ℝ)) f)
    (hCorrelation : δ * (H : ℝ) ≤
      typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ)) : False := by
  exact selectedTypeIOrTypeI2_refutes_largeCorrelation
    d X H K c D E a b A a₀ η δ P f w Cpm decompositionC
    ctx.hInv ctx.hd ctx.hX ctx.hA ctx.hη ctx.hηmax ctx.hDsource ctx.hE
    ctx.hEa ctx.ha₀ ctx.hL ctx.hδpos ctx.hδsmall
    (by simpa only [Real.rpow_natCast] using ctx.hδinv) ctx.hHlower
    ctx.hHupper ctx.hCtype ctx.hScaleBudget ctx.hP hType hCorrelation
    ctx.hL3modulus ctx.hL3variation ctx.hCpmPos ctx.hCpmSmall
    ctx.hMuPrefix ctx.hCramerPrefix ctx.hw ctx.hLarge

/-- The scale clause packaged in an exact Type-II decomposition implies the
coarser conditional scale cutoff used by the inverse theorem. -/
private theorem selectedTypeII_conditionalScaleBound (X Aminus Aplus : ℝ)
    (hX : 0 < X)
    (hAminusLow : decompositionC⁻¹ * X ^ (3 / 8 : ℝ) ≤ Aminus)
    (hAplusHigh : Aplus ≤ decompositionC * X ^ (5 / 8 : ℝ)) :
    max Aplus (X / Aminus) ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
  have hCpos : 0 < decompositionC := by
    unfold decompositionC
    positivity
  have hlowpos : 0 < decompositionC⁻¹ * X ^ (3 / 8 : ℝ) :=
    mul_pos (inv_pos.mpr hCpos) (Real.rpow_pos_of_pos hX _)
  have hAminuspos : 0 < Aminus := lt_of_lt_of_le hlowpos hAminusLow
  have hratio : X / Aminus ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
    apply (div_le_iff₀ hAminuspos).2
    calc
      X = decompositionC * X ^ (5 / 8 : ℝ) *
          (decompositionC⁻¹ * X ^ (3 / 8 : ℝ) : ℝ) := by
        have hpow : X ^ (5 / 8 : ℝ) * X ^ (3 / 8 : ℝ) = X := by
          calc
            X ^ (5 / 8 : ℝ) * X ^ (3 / 8 : ℝ) =
                X ^ ((5 / 8 : ℝ) + (3 / 8 : ℝ)) := by
                  rw [← Real.rpow_add hX]
            _ = X := by
              rw [show (5 / 8 : ℝ) + (3 / 8 : ℝ) = 1 by norm_num,
                Real.rpow_one]
        calc
          X = 1 * X := by ring
          _ = (decompositionC * decompositionC⁻¹) *
              (X ^ (5 / 8 : ℝ) * X ^ (3 / 8 : ℝ)) := by
                rw [hpow]
                field_simp [ne_of_gt hCpos]
          _ = decompositionC * X ^ (5 / 8 : ℝ) *
              (decompositionC⁻¹ * X ^ (3 / 8 : ℝ) : ℝ) := by ring
      _ ≤ decompositionC * X ^ (5 / 8 : ℝ) * Aminus :=
        mul_le_mul_of_nonneg_left hAminusLow
          (mul_nonneg hCpos.le (Real.rpow_nonneg hX.le _))
  exact max_le_iff.mpr ⟨hAplusHigh, hratio⟩

/-- Apply the Type-II inverse contradiction only to a component designated
Type II by the same decomposition selected in the PTW contract. -/
theorem selectedDesignatedTypeIIComponent_refutes
    {d X H K c D E a b : ℕ} {A a₀ η δ Cpm Ctw Astar : ℝ}
    {P : Polynomial ℝ} {w : ℤ → ℂ}
    (ctx : ConditionalIntegerInverseContext d X H K c D E a b
      A a₀ η δ Cpm Ctw Astar P w)
    {g : ComplexPositiveIntegerFunction}
    (selection : RestrictedPTWSelection X Astar (a : ℝ) η Ctw g)
    (i : selection.decomposition.Index)
    (hi : i ∈ selection.decomposition.indices)
    (hTagTwo : (selection.designationTag i hi).val = 2)
    (hDesignation : restrictedPTWDesignationEvidence (X : ℝ)
      (selection.decomposition.component i) (selection.designationTag i hi))
    (hCorrelation : δ * (H : ℝ) ≤
      typeIScalarPhaseCorrelation (selection.decomposition.component i)
        P (X : ℝ) (H : ℝ)) : False := by
  have hTagNotZero : (selection.designationTag i hi).val ≠ 0 := by omega
  have hTagNotOne : (selection.designationTag i hi).val ≠ 1 := by omega
  have hTypeIIData :
      ∃ (z coefficient : ℝ)
        (fs : List (DyadicArithmeticFactor (X : ℝ)))
        (α : Fin fs.length → ℝ),
        (∀ j, 0 ≤ α j) ∧
        (∑ j, α j = 1) ∧
        (∀ j,
          normalizedExponentConstant⁻¹ * (X : ℝ) ^ α j ≤
              dyadicFactorScale (fs.get j) ∧
            dyadicFactorScale (fs.get j) ≤
              normalizedExponentConstant * (X : ℝ) ^ α j) ∧
        (∀ j k, fs.get j = .mobius k → α j ≤ (1 / 8 : ℝ)) ∧
        largeTypeIIDyadicComponentData z coefficient
          (decompositionDelta (X : ℝ))
          (selection.decomposition.component i) fs α ∧
        (∀ j, α j < (3 / 8 : ℝ)) := by
    simpa [restrictedPTWDesignationEvidence, hTagNotZero, hTagNotOne]
      using hDesignation
  rcases hTypeIIData with
    ⟨z, coefficient, fs, α, _hα, _hsum, _hscale, _hmob, hData, _hstrict⟩
  have hTwistPrefix := selection.twistedPrefix H ctx.hHlower ctx.hHupper
    i hi
  have hTwistPrefix' : ∀ T : ℝ,
      (X : ℝ) / (H : ℝ) * (Real.log (X : ℝ)) ^ ((50 : ℕ) * a) ≤ |T| →
      |T| ≤ (X : ℝ) ^ a →
      residuePrefixEnvelope X H
        (fun n => complexPositiveIntegerZeroExtension
          (selection.decomposition.component i) n * archimedeanTwist T (n : ℝ))
        ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
        Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-(a : ℝ)) := by
    have hTagTwo' : (selection.designationTag i hi).val = 2 := hTagTwo
    have hTwistPrefix0 :
        ∀ T : ℝ,
          (X : ℝ) / (H : ℝ) * (Real.log (X : ℝ)) ^ ((50 : ℝ) * (a : ℝ)) ≤ |T| →
          |T| ≤ (X : ℝ) ^ (a : ℝ) →
          residuePrefixEnvelope X H
            (fun n => complexPositiveIntegerZeroExtension
              (selection.decomposition.component i) n *
                archimedeanTwist T (n : ℝ))
            ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
            Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-(a : ℝ)) := by
      simpa [restrictedPTWDesignatedPrefixConclusion, hTagTwo']
        using hTwistPrefix
    intro T hLower hUpper
    have hexp : (50 : ℝ) * (a : ℝ) = (((50 : ℕ) * a : ℕ) : ℝ) := by
      norm_cast
    have hLower' : (X : ℝ) / (H : ℝ) *
        (Real.log (X : ℝ)) ^ ((50 : ℝ) * (a : ℝ)) ≤ |T| := by
      rw [hexp, Real.rpow_natCast]
      exact hLower
    have hUpper' : |T| ≤ (X : ℝ) ^ (a : ℝ) := by
      simpa only [Real.rpow_natCast] using hUpper
    exact hTwistPrefix0 T hLower' hUpper'
  rcases hData with ⟨Aminus, Aplus, v, aa, b1, γ, ηv, η', I, J, J', i0,
    hTypeII, _hfactor, _hv, _haa, _hb1, hAminusOne, _hAminusAplus,
    hAminusLow, hAplusHigh, _hsumExp, _hgammaLow, _hgammaHigh, _hetaGap,
    _hsupportV, _hsupportA, _hsupportB, _hi0, _halpha⟩
  have hXthree : 3 ≤ X := ctx.hX
  have hXnat : 0 < X := by omega
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXnat
  have hTypeII' : typeIIFunction δ Aminus Aplus
      (selection.decomposition.component i) :=
    typeIIFunction_mono hTypeII ctx.hδpos ctx.hDeltaType hAminusOne le_rfl le_rfl
  have hScale := selectedTypeII_conditionalScaleBound (X : ℝ) Aminus Aplus hXpos
    hAminusLow hAplusHigh
  exact selectedTypeII_refutes_largeCorrelation
    d X H K c D E a b A a₀ η δ Aminus Aplus Cpm decompositionC Ctw P
    (selection.decomposition.component i) w ctx.hInv ctx.hd ctx.hX ctx.hA
    ctx.hη ctx.hηmax ctx.hDsource ctx.hE ctx.hEa ctx.hAgtDE ctx.hAgtD
    ctx.ha₀ ctx.hL ctx.hδpos ctx.hδsmall
    (by simpa only [Real.rpow_natCast] using ctx.hδinv)
    ctx.hHlower ctx.hHupper hScale ctx.hCtype ctx.hScaleBudget
    ctx.hL3q ctx.hL3T ctx.hL3tv ctx.hLE ctx.hP hTypeII' hCorrelation
    ctx.hCpmPos ctx.hCpmSmall ctx.hMuPrefix ctx.hCramerPrefix ctx.hw
    hTwistPrefix' ctx.hCtwPos ctx.hCtwSmall ctx.hLarge

/-- The two source-defined arithmetic objectives cannot have a large
correlation once the exact conditional-integer premises and the checked
inverse clauses are supplied. The proof instantiates the source decomposition
and approximation before invoking the checked branch contradictions. -/
theorem conditionalIntegerSourceLargeCorrelation_refutes
    {d X H K c Dexp E a b : ℕ} {A a₀ η δ Cpm Ctw Astar : ℝ}
    {P : Polynomial ℝ} {w : ℤ → ℂ}
    (ctx : ConditionalIntegerInverseContext d X H K c Dexp E a b
      A a₀ η δ Cpm Ctw Astar P w) : False := by
  classical
  have hXone : (1 : ℝ) ≤ (X : ℝ) := by
    have hXnat : 3 ≤ X := ctx.hX
    exact_mod_cast (show 1 ≤ X by omega)
  have hShortExponent : (5 / 8 : ℝ) ≤ (5 / 8 : ℝ) + η := by
    linarith [ctx.hη]
  have hShortLength : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hXone hShortExponent).trans ctx.hHlower
  have hHone : (1 : ℝ) ≤ (H : ℝ) := by
    have hexpNonneg : 0 ≤ (5 / 8 : ℝ) + η := by positivity
    exact (Real.one_le_rpow hXone hexpNonneg).trans ctx.hHlower
  have hHpos : 0 < H := by
    have hNat : 1 ≤ H := by exact_mod_cast hHone
    omega
  have hXexp : 1 - η ≤ 1 := by linarith [ctx.hη]
  have hUpperPower : (X : ℝ) ^ (1 - η) ≤ (X : ℝ) := by
    calc
      (X : ℝ) ^ (1 - η) ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone hXexp
      _ = (X : ℝ) := Real.rpow_one _
  have hHleX : H ≤ X := by
    exact_mod_cast (le_trans ctx.hHupper hUpperPower)
  rcases ctx.hw with hMu | hLambda
  · have hLargeMu : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
        ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ := by
      simpa [hMu] using ctx.hLarge
    have hδlt : δ < 1 := by
      have hmin : min (1 / 2 : ℝ) ((Real.log (X : ℝ))⁻¹) ≤ 1 / 2 :=
        min_le_left _ _
      linarith [ctx.hδsmall]
    let D := ctx.muPTWSelection.decomposition
    obtain ⟨f, hType, hCorrelation, hOrigin⟩ :=
      exists_mobius_conditionalInteger_selectedComponent X H Dexp D A δ P
        ctx.hX hHpos hHleX ctx.hL ctx.hδpos
        hδlt
        ctx.hDelta ctx.hThreshold ctx.hDeltaType hLargeMu
    rcases hOrigin with hExtra | ⟨i, hi, hEq⟩
    · subst f
      have hExtraType := zero_conditionalTypeI X δ ctx.hX
        ctx.hδpos hδlt
      exact selectedTypeIOrTypeI2Component_refutes ctx
        (fun _ : PositiveInteger => 0) (Or.inl hExtraType) hCorrelation.le
    · subst f
      have hTagEvidence := ctx.muPTWSelection.designationEvidence i hi
      by_cases hTagZero :
          (ctx.muPTWSelection.designationTag i hi).val = 0
      · have hI : typeIFunction (decompositionDelta (X : ℝ))
            (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ)) (D.component i) := by
          simpa [restrictedPTWDesignationEvidence, hTagZero]
            using hTagEvidence
        have hI' : typeIFunction δ
            (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ)) (D.component i) :=
          typeIFunction_mono hI ctx.hδpos ctx.hDeltaType le_rfl
        exact selectedTypeIOrTypeI2Component_refutes ctx (D.component i)
          (Or.inl hI') hCorrelation.le
      · by_cases hTagOne :
            (ctx.muPTWSelection.designationTag i hi).val = 1
        · have hI2 : typeI2Function (decompositionDelta (X : ℝ))
              (decompositionC * (X : ℝ) ^ (7 / 16 : ℝ)) (D.component i) := by
            simpa [restrictedPTWDesignationEvidence, hTagZero, hTagOne]
              using hTagEvidence
          have hI2' : typeI2Function δ
              (decompositionC * (X : ℝ) ^ (7 / 16 : ℝ)) (D.component i) :=
            typeI2Function_mono hI2 ctx.hδpos ctx.hDeltaType le_rfl
          exact selectedTypeIOrTypeI2Component_refutes ctx (D.component i)
            (Or.inr hI2') hCorrelation.le
        · have hTagTwo :
              (ctx.muPTWSelection.designationTag i hi).val = 2 := by
            have hlt := (ctx.muPTWSelection.designationTag i hi).isLt
            omega
          exact selectedDesignatedTypeIIComponent_refutes ctx
            ctx.muPTWSelection i hi hTagTwo hTagEvidence hCorrelation.le
  · have hLargeLambda : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
        ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          ((paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) *
            unitFrequencyPhase (P.eval (n : ℝ))‖ := by
      simpa [hLambda] using ctx.hLarge
    have hδlt : δ < 1 := by
      have hmin : min (1 / 2 : ℝ) ((Real.log (X : ℝ))⁻¹) ≤ 1 / 2 :=
        min_le_left _ _
      linarith [ctx.hδsmall]
    let D := ctx.lambdaPTWSelection.decomposition
    obtain ⟨bModel, hbSupport, hbCoeff, f, hType, hCorrelation, hOrigin⟩ :=
      exists_lambda_conditionalInteger_selectedComponent X H Dexp D A δ P
        ctx.hX hHpos hHleX ctx.hA hShortLength ctx.hL ctx.hδpos
        hδlt
        ctx.hDelta ctx.hThreshold ctx.hDeltaType ctx.hApp ctx.hLevel
        hLargeLambda
    rcases hOrigin with hExtra | ⟨i, hi, hEq⟩
    · subst f
      have hDeltaInv := conditionalDelta_inv X Dexp δ (by linarith [ctx.hL]) ctx.hDelta
      have hExtraType := cramerNegativeModel_typeI X Dexp δ bModel
        ctx.hX ctx.hL ctx.hδpos hδlt hDeltaInv ctx.hLevel hbCoeff
      exact selectedTypeIOrTypeI2Component_refutes ctx
        (-cramerShortDivisorModel X bModel) (Or.inl hExtraType)
        hCorrelation.le
    · subst f
      have hTagEvidence := ctx.lambdaPTWSelection.designationEvidence i hi
      by_cases hTagZero :
          (ctx.lambdaPTWSelection.designationTag i hi).val = 0
      · have hI : typeIFunction (decompositionDelta (X : ℝ))
            (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ)) (D.component i) := by
          simpa [restrictedPTWDesignationEvidence, hTagZero]
            using hTagEvidence
        have hI' : typeIFunction δ
            (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ)) (D.component i) :=
          typeIFunction_mono hI ctx.hδpos ctx.hDeltaType le_rfl
        exact selectedTypeIOrTypeI2Component_refutes ctx (D.component i)
          (Or.inl hI') hCorrelation.le
      · by_cases hTagOne :
            (ctx.lambdaPTWSelection.designationTag i hi).val = 1
        · have hI2 : typeI2Function (decompositionDelta (X : ℝ))
              (decompositionC * (X : ℝ) ^ (7 / 16 : ℝ)) (D.component i) := by
            simpa [restrictedPTWDesignationEvidence, hTagZero, hTagOne]
              using hTagEvidence
          have hI2' : typeI2Function δ
              (decompositionC * (X : ℝ) ^ (7 / 16 : ℝ)) (D.component i) :=
            typeI2Function_mono hI2 ctx.hδpos ctx.hDeltaType le_rfl
          exact selectedTypeIOrTypeI2Component_refutes ctx (D.component i)
            (Or.inr hI2') hCorrelation.le
        · have hTagTwo :
              (ctx.lambdaPTWSelection.designationTag i hi).val = 2 := by
            have hlt := (ctx.lambdaPTWSelection.designationTag i hi).isLt
            omega
          exact selectedDesignatedTypeIIComponent_refutes ctx
            ctx.lambdaPTWSelection i hi hTagTwo hTagEvidence hCorrelation.le

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.cramerApproximation_phaseError_le_quarter
#print axioms FractionalPrimes.Literature.Polynomial.exists_cramerApproximation_phaseError
#print axioms FractionalPrimes.Literature.Polynomial.cramerNegativeModel_typeI
#print axioms FractionalPrimes.Literature.Polynomial.exists_mobius_conditionalInteger_selectedComponent
#print axioms FractionalPrimes.Literature.Polynomial.exists_lambda_conditionalInteger_selectedComponent
#print axioms FractionalPrimes.Literature.Polynomial.selectedTypeIOrTypeI2Component_refutes
#print axioms FractionalPrimes.Literature.Polynomial.selectedDesignatedTypeIIComponent_refutes
#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerSourceLargeCorrelation_refutes
