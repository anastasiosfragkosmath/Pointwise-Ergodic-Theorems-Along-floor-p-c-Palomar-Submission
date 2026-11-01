module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalTrilinearSmallFactor
public import FractionalPrimes.Literature.Polynomial.ShortIntervalTrilinearLargeCell
public import FractionalPrimes.Literature.Polynomial.ShortIntervalFactorSquareCoeff
public import FractionalPrimes.Literature.Polynomial.DirichletMeanConstants
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-! Exact finite assembly of the checked small-factor and dyadic-cell
contributions to `ldm:trilinear`, using the checked `ldm:power-levels` package.
No analytic estimate is added beyond that package. -/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.DirichletMean

noncomputable section

private theorem trilinearExponentGeometry
    (eps a b c : ℝ)
    (heps1 : eps ≤ 3 / 16)
    (hsum : a + b + c = 1)
    (haLower : 1 / 4 - eps / 100 ≤ a)
    (haUpper : a ≤ 1 / 2 + eps / 100)
    (hbalance : |b - c| ≤ 1 / 4 + eps / 100) :
    (1 / 8 - 3 / 1600 ≤ a) ∧ (1 / 8 - 3 / 1600 ≤ b) ∧
    (1 / 8 - 3 / 1600 ≤ c) ∧
    (a ≤ 1 / 2 + 3 / 1600) ∧ (b ≤ 1 / 2 + 3 / 1600) ∧
    (c ≤ 1 / 2 + 3 / 1600) ∧
    (a + b ≤ 7 / 8 + 3 / 1600) ∧
    (a + c ≤ 7 / 8 + 3 / 1600) ∧
    (b + c ≤ 7 / 8 + 3 / 1600) := by
  have heps : eps / 100 ≤ (3 : ℝ) / 1600 := by nlinarith
  have habs := abs_le.mp hbalance
  have hbc : b + c = 1 - a := by linarith
  have hlowA : (1 / 8 : ℝ) - 3 / 1600 ≤ a := by linarith
  have hhighA : a ≤ 1 / 2 + 3 / 1600 := by linarith
  have hlowB : (1 / 8 : ℝ) - 3 / 1600 ≤ b := by
    linarith [hbc, habs.1]
  have hlowC : (1 / 8 : ℝ) - 3 / 1600 ≤ c := by
    linarith [hbc, habs.2]
  have hhighB : b ≤ 1 / 2 + 3 / 1600 := by
    linarith [hbc, habs.2]
  have hhighC : c ≤ 1 / 2 + 3 / 1600 := by
    linarith [hbc, habs.1]
  have hsumAB : a + b ≤ 7 / 8 + 3 / 1600 := by linarith [hlowC, hsum]
  have hsumAC : a + c ≤ 7 / 8 + 3 / 1600 := by linarith [hlowB, hsum]
  have hsumBC : b + c ≤ 7 / 8 + 3 / 1600 := by linarith [hlowA, hsum]
  exact ⟨hlowA, hlowB, hlowC, hhighA, hhighB, hhighC,
    hsumAB, hsumAC, hsumBC⟩

private theorem factorMeanSquareIcc_from_powerLevels
    (C : ℕ) (X T N : ℝ) (coeff : ℕ → ℂ)
    (hX : 2 ^ 16 ≤ X) (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hNX : N ≤ X) (hTX : T ≤ X)
    (hcoeff : factorCoefficientBound C N coeff) :
    (∫ t in Set.Icc (-T) T,
      ‖factorPolynomial N coeff t‖ ^ 2 ∂volume) ≤
        K C * Real.log (4 * X) ^ b C * (T + N) := by
  have hinterval := (factorAndSquareLevelBounds C N T X 1 coeff
    hX hN hT hNX hTX (by norm_num) hcoeff).2
  have hconvert : (∫ t in (-T)..T,
      Complex.normSq (factorPolynomial N coeff t)) =
      ∫ t in Set.Icc (-T) T,
        ‖factorPolynomial N coeff t‖ ^ 2 ∂volume := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc]
    simp [Complex.normSq_eq_norm_sq]
  calc
    _ = ∫ t in (-T)..T,
        Complex.normSq (factorPolynomial N coeff t) := hconvert.symm
    _ ≤ K C * Real.log (4 * X) ^ b C * (T + N) := hinterval

private theorem trilinearLengthBounds
    (X v : ℝ) (hX : 2 ^ 16 ≤ X)
    (hvLower : 1 / 8 - 3 / 1600 ≤ v)
    (hvUpper : v ≤ 1 / 2 + 3 / 1600) :
    2 ≤ X ^ v ∧ X ^ v ≤ X := by
  have hXone : 1 ≤ X := by norm_num at hX ⊢; linarith
  have hv0 : 0 ≤ v := by linarith
  have hbase : 0 ≤ (2 : ℝ) := by norm_num
  have hbaseMono : (2 ^ 16 : ℝ) ^ v ≤ X ^ v :=
    Real.rpow_le_rpow (by positivity) hX hv0
  have hbaseEq : (2 ^ 16 : ℝ) ^ v = (2 : ℝ) ^ (16 * v) := by
    rw [show (2 ^ 16 : ℝ) = (2 : ℝ) ^ (16 : ℝ) by norm_num,
      Real.rpow_mul hbase]
  have hexpLower : (1 : ℝ) ≤ 16 * v := by nlinarith
  have hpowLower : (2 : ℝ) ≤ (2 : ℝ) ^ (16 * v) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      hexpLower
    simpa using h
  have hNlower : 2 ≤ X ^ v := by linarith [hbaseMono, hbaseEq, hpowLower]
  have hvUpperOne : v ≤ 1 := by nlinarith
  have hNupper : X ^ v ≤ X := by
    calc
      X ^ v ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hXone hvUpperOne
      _ = X := by rw [Real.rpow_one]
  exact ⟨hNlower, hNupper⟩

private theorem trilinearLengthSqrtProduct
    (X a b c : ℝ) (hX : 0 < X)
    (N1 N2 N3 : ℝ) (ha : N1 = X ^ a) (hb : N2 = X ^ b)
    (hc : N3 = X ^ c) (hsum : a + b + c = 1) :
    Real.sqrt N1 * Real.sqrt N2 * Real.sqrt N3 = Real.sqrt X := by
  have hN1 : 0 < N1 := by rw [ha]; positivity
  have hN2 : 0 < N2 := by rw [hb]; positivity
  have hN3 : 0 < N3 := by rw [hc]; positivity
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.sqrt_eq_rpow, ha, hb, hc]
  rw [← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le,
    ← Real.rpow_mul hX.le]
  rw [← Real.rpow_add hX, ← Real.rpow_add hX]
  congr 1
  ring_nf
  linarith

private theorem trilinearCellLevelMeasureBounds
    (C : ℕ) (X T N V kL : ℝ) (coeff : ℕ → ℂ) (cell : Set ℝ)
    (hX : 2 ^ 16 ≤ X) (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hNX : N ≤ X) (hTX : T ≤ X) (hV : 0 < V)
    (hcoeff : factorCoefficientBound C N coeff)
    (hkL : kL = K C * Real.log (4 * X) ^ b C)
    (hcellInterval : cell ⊆ Set.Icc (-T) T)
    (hcellLevel : ∀ t ∈ cell,
      V ≤ ‖factorPolynomial N coeff t‖) :
    (volume.real cell ≤ kL *
      (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6))) ∧
    (volume.real cell ≤ kL *
      (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12))) := by
  have hpackage := factorAndSquareLevelBounds C N T X V coeff
    hX hN hT hNX hTX hV hcoeff
  have hlevelSubset : cell ⊆
      FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) := by
    intro t ht
    refine ⟨hcellInterval ht, ?_⟩
    simpa [factorPolynomial] using hcellLevel t ht
  have hlevelInterval :
      FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) ⊆
          Set.Icc (-T) T := by
    intro t ht
    exact ht.1
  have hfinite : MeasureTheory.volume
      (FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) ≠ ⊤ := by
    apply ne_of_lt
    have hmono := MeasureTheory.measure_mono (μ := volume) hlevelInterval
    exact lt_of_le_of_lt hmono (by simp [Real.volume_Icc])
  have hcellMeasure : volume.real cell ≤
      volume.real (FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) :=
    MeasureTheory.measureReal_mono hlevelSubset hfinite
  have hlevelOne : volume.real
      (FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) ≤
      K C * Real.log (4 * X) ^ b C *
        (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) := by
    simpa using hpackage.1 1 (Or.inl rfl)
  have hlevelTwo : volume.real
      (FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) ≤
      K C * Real.log (4 * X) ^ b C *
        (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by
    simpa using hpackage.1 2 (Or.inr rfl)
  constructor
  · calc
      volume.real cell ≤
          volume.real (FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
            (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) :=
        hcellMeasure
      _ ≤ K C * Real.log (4 * X) ^ b C *
          (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) :=
        hlevelOne
      _ = kL * (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) := by rw [← hkL]
  · calc
      volume.real cell ≤
          volume.real (FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
            (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) :=
        hcellMeasure
      _ ≤ K C * Real.log (4 * X) ^ b C *
          (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) :=
        hlevelTwo
      _ = kL * (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by rw [← hkL]

set_option maxHeartbeats 2000000 in
private theorem trilinearLargeFactorCellCost
    (C : ℕ) (X T eps a b c delta : ℝ)
    (coeff1 coeff2 coeff3 : ℕ → ℂ) (E : Set ℝ)
    (idx : ℕ × ℕ × ℕ)
    (hX : 2 ^ 16 ≤ X) (hT : 2 ≤ T)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 3 / 16)
    (hTupper : T ≤ X ^ (3 / 8 - eps))
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hsum : a + b + c = 1)
    (haLower : 1 / 4 - eps / 100 ≤ a)
    (haUpper : a ≤ 1 / 2 + eps / 100)
    (hbalance : |b - c| ≤ 1 / 4 + eps / 100)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hEmeas : MeasurableSet E)
    (hEsubset : E ⊆ Set.Icc (-T) T)
    (hcap2 : ∀ t ∈ E,
      ‖factorPolynomial (X ^ b) coeff2 t‖ ≤ Real.sqrt (X ^ b))
    (hcap3 : ∀ t ∈ E,
      ‖factorPolynomial (X ^ c) coeff3 t‖ ≤ Real.sqrt (X ^ c))
    (hsmall : ∀ t ∈ E,
      ‖factorPolynomial (X ^ a) coeff1 t‖ ≤ delta * Real.sqrt (X ^ a))
    (hcoeff1 : factorCoefficientBound C (X ^ a) coeff1)
    (hcoeff2 : factorCoefficientBound C (X ^ b) coeff2)
    (hcoeff3 : factorCoefficientBound C (X ^ c) coeff3) :
    ∫ t in trilinearDyadicLargeFactorCell E
        (factorPolynomial (X ^ a) coeff1)
        (factorPolynomial (X ^ b) coeff2)
        (factorPolynomial (X ^ c) coeff3) idx,
      ‖factorPolynomial (X ^ a) coeff1 t *
        factorPolynomial (X ^ b) coeff2 t *
        factorPolynomial (X ^ c) coeff3 t‖ ∂volume ≤
      16 * (K C * Real.log (4 * X) ^ FractionalPrimes.Literature.DirichletMean.b C) * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) := by
  classical
  let N1 := X ^ a
  let N2 := X ^ b
  let N3 := X ^ c
  let F1 := factorPolynomial N1 coeff1
  let F2 := factorPolynomial N2 coeff2
  let F3 := factorPolynomial N3 coeff3
  let L := Real.log (4 * X)
  let kL := K C * L ^ FractionalPrimes.Literature.DirichletMean.b C
  let V1 := (2 : ℝ) ^ idx.1
  let V2 := (2 : ℝ) ^ idx.2.1
  let V3 := (2 : ℝ) ^ idx.2.2
  let cell := trilinearDyadicLargeFactorCell E F1 F2 F3 idx
  have hXone : 1 ≤ X := by norm_num at hX ⊢; linarith
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXone
  have hXgt : 1 < X := by norm_num at hX ⊢; linarith
  have hTpos : 0 < T := by linarith
  have hgeometry := trilinearExponentGeometry eps a b c heps1
    hsum haLower haUpper hbalance
  have hN1bounds := trilinearLengthBounds X a hX hgeometry.1 hgeometry.2.2.2.1
  have hN2bounds := trilinearLengthBounds X b hX hgeometry.2.1 hgeometry.2.2.2.2.1
  have hN3bounds := trilinearLengthBounds X c hX hgeometry.2.2.1 hgeometry.2.2.2.2.2.1
  have hTleX : T ≤ X := by
    calc
      T ≤ X ^ (3 / 8 - eps) := hTupper
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
      _ = X := by rw [Real.rpow_one]
  have hL : 1 ≤ L := by
    have hlog4 : 1 ≤ Real.log (4 : ℝ) := by
      have h := Real.le_log_one_add_of_nonneg (x := (3 : ℝ)) (by norm_num)
      norm_num at h
      linarith
    have h4X : 4 ≤ 4 * X := by nlinarith
    dsimp [L]
    exact hlog4.trans (Real.log_le_log (by norm_num) h4X)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hkLpos : 0 < kL := by
    dsimp [kL, L]
    exact mul_pos (constants_positive C).2.2.1 (pow_pos hLpos _)
  have hF1 : Continuous F1 := by
    dsimp [F1, N1]
    exact factorPolynomial_continuous _ _
  have hF2 : Continuous F2 := by
    dsimp [F2, N2]
    exact factorPolynomial_continuous _ _
  have hF3 : Continuous F3 := by
    dsimp [F3, N3]
    exact factorPolynomial_continuous _ _
  have hcellMeas : MeasurableSet cell := by
    dsimp [cell]
    exact trilinearDyadicLargeFactorCell_measurable E F1 F2 F3 idx
      hEmeas hF1 hF2 hF3
  have hcellBounds : ∀ t ∈ cell,
      (V1 ≤ ‖F1 t‖ ∧ ‖F1 t‖ ≤ 2 * V1) ∧
      (V2 ≤ ‖F2 t‖ ∧ ‖F2 t‖ ≤ 2 * V2) ∧
      (V3 ≤ ‖F3 t‖ ∧ ‖F3 t‖ ≤ 2 * V3) := by
    intro t ht
    have ht' := ht
    simp only [cell, trilinearDyadicLargeFactorCell, Set.mem_inter_iff] at ht'
    have hdom := ht'.1
    have htriple := ht'.2
    change t ∈ E ∧ 1 < ‖F1 t‖ ∧ 1 < ‖F2 t‖ ∧ 1 < ‖F3 t‖ at hdom
    change t ∈ trilinearDyadicScalarCell F1 idx.1 ∧
      (t ∈ trilinearDyadicScalarCell F2 idx.2.1 ∧
        t ∈ trilinearDyadicScalarCell F3 idx.2.2) at htriple
    rcases htriple with ⟨hcell1, ⟨hcell2, hcell3⟩⟩
    change (2 : ℝ) ^ idx.1 ≤ ‖F1 t‖ ∧
      ‖F1 t‖ < (2 : ℝ) ^ (idx.1 + 1) at hcell1
    change (2 : ℝ) ^ idx.2.1 ≤ ‖F2 t‖ ∧
      ‖F2 t‖ < (2 : ℝ) ^ (idx.2.1 + 1) at hcell2
    change (2 : ℝ) ^ idx.2.2 ≤ ‖F3 t‖ ∧
      ‖F3 t‖ < (2 : ℝ) ^ (idx.2.2 + 1) at hcell3
    refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · exact hcell1.1
    · simpa [V1, pow_succ, mul_comm] using hcell1.2.le
    · exact hcell2.1
    · simpa [V2, pow_succ, mul_comm] using hcell2.2.le
    · exact hcell3.1
    · simpa [V3, pow_succ, mul_comm] using hcell3.2.le
  have hcellInterval : cell ⊆ Set.Icc (-T) T := by
    intro t ht
    have ht' := ht
    simp only [cell, trilinearDyadicLargeFactorCell, Set.mem_inter_iff] at ht'
    rcases ht' with ⟨hdom, _⟩
    change t ∈ E ∧ _ at hdom
    exact hEsubset hdom.1
  have hmeanLevel1 := trilinearCellLevelMeasureBounds C X T N1 V1 kL coeff1 cell
    hX hN1bounds.1 hT hN1bounds.2 hTleX (by dsimp [V1]; positivity)
    (by simpa [N1] using hcoeff1) (by dsimp [kL, L]) hcellInterval
    (by intro t ht; exact (hcellBounds t ht).1.1)
  have hmeanLevel2 := trilinearCellLevelMeasureBounds C X T N2 V2 kL coeff2 cell
    hX hN2bounds.1 hT hN2bounds.2 hTleX (by dsimp [V2]; positivity)
    (by simpa [N2] using hcoeff2) (by dsimp [kL, L]) hcellInterval
    (by intro t ht; exact (hcellBounds t ht).2.1.1)
  have hmeanLevel3 := trilinearCellLevelMeasureBounds C X T N3 V3 kL coeff3 cell
    hX hN3bounds.1 hT hN3bounds.2 hTleX (by dsimp [V3]; positivity)
    (by simpa [N3] using hcoeff3) (by dsimp [kL, L]) hcellInterval
    (by intro t ht; exact (hcellBounds t ht).2.2.1)
  have hpoint : ∀ t ∈ cell, ‖F1 t * F2 t * F3 t‖ ≤ 8 * V1 * V2 * V3 := by
    intro t ht
    have hb := hcellBounds t ht
    calc
      ‖F1 t * F2 t * F3 t‖ = ‖F1 t‖ * ‖F2 t‖ * ‖F3 t‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ (2 * V1) * (2 * V2) * (2 * V3) := by
        apply mul_le_mul
        · exact mul_le_mul hb.1.2 hb.2.1.2 (norm_nonneg _) (by positivity)
        · exact hb.2.2.2
        · positivity
        · positivity
      _ = 8 * V1 * V2 * V3 := by ring
  have hsqrtProduct : Real.sqrt N1 * Real.sqrt N2 * Real.sqrt N3 = Real.sqrt X :=
    trilinearLengthSqrtProduct X a b c hXpos N1 N2 N3 rfl rfl rfl hsum
  have hlargeExponent : 2 * kL < volume.real cell →
      (volume.real cell / (2 * kL)) * V1 * V2 * V3 ≤
        Real.sqrt X * X ^ (-(min eps (-Real.log delta / Real.log X)) / 16) := by
    intro hlarge
    let m := volume.real cell
    let R := m / (2 * kL)
    let h := min eps (-Real.log delta / Real.log X)
    let r := Real.logb X R
    let x := Real.logb X V1
    let y := Real.logb X V2
    let z := Real.logb X V3
    have hcellNonempty : cell.Nonempty := by
      by_contra hne
      have hempty : cell = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hzero : volume.real cell = 0 := by simp [hempty]
      linarith
    rcases hcellNonempty with ⟨t, ht⟩
    have ht' := ht
    simp only [cell, trilinearDyadicLargeFactorCell, Set.mem_inter_iff] at ht'
    rcases ht' with ⟨hdom, _⟩
    change t ∈ E ∧ _ at hdom
    have hcapV1 : V1 ≤ delta * Real.sqrt N1 := by
      exact (hcellBounds t ht).1.1.trans
        (by simpa [F1, N1] using hsmall t hdom.1)
    have hcapV2 : V2 ≤ Real.sqrt N2 := by
      exact (hcellBounds t ht).2.1.1.trans
        (by simpa [F2, N2] using hcap2 t hdom.1)
    have hcapV3 : V3 ≤ Real.sqrt N3 := by
      exact (hcellBounds t ht).2.2.1.trans
        (by simpa [F3, N3] using hcap3 t hdom.1)
    have hm : m = volume.real cell := rfl
    have hRgt : 1 < R := by
      dsimp [R, m]
      rw [one_lt_div (by positivity : 0 < 2 * kL)]
      exact hlarge
    have hRpos : 0 < R := lt_trans zero_lt_one hRgt
    have hV1pos : 0 < V1 := by dsimp [V1]; positivity
    have hV2pos : 0 < V2 := by dsimp [V2]; positivity
    have hV3pos : 0 < V3 := by dsimp [V3]; positivity
    have hlogX : 0 < Real.log X := Real.log_pos hXgt
    have hRpow : R = X ^ r := by
      dsimp [r]
      exact (Real.rpow_logb hXpos hXgt.ne' hRpos).symm
    have hV1pow : V1 = X ^ x := by
      dsimp [x]
      exact (Real.rpow_logb hXpos hXgt.ne' hV1pos).symm
    have hV2pow : V2 = X ^ y := by
      dsimp [y]
      exact (Real.rpow_logb hXpos hXgt.ne' hV2pos).symm
    have hV3pow : V3 = X ^ z := by
      dsimp [z]
      exact (Real.rpow_logb hXpos hXgt.ne' hV3pos).symm
    have hV1one : 1 ≤ V1 := by dsimp [V1]; exact one_le_pow₀ (by norm_num)
    have hV2one : 1 ≤ V2 := by dsimp [V2]; exact one_le_pow₀ (by norm_num)
    have hV3one : 1 ≤ V3 := by dsimp [V3]; exact one_le_pow₀ (by norm_num)
    have hr0 : 0 ≤ r := by
      dsimp [r, Real.logb]
      exact div_nonneg (Real.log_nonneg hRgt.le) hlogX.le
    have hx0 : 0 ≤ x := by
      dsimp [x, Real.logb]
      exact div_nonneg (Real.log_nonneg hV1one) hlogX.le
    have hy0 : 0 ≤ y := by
      dsimp [y, Real.logb]
      exact div_nonneg (Real.log_nonneg hV2one) hlogX.le
    have hz0 : 0 ≤ z := by
      dsimp [z, Real.logb]
      exact div_nonneg (Real.log_nonneg hV3one) hlogX.le
    have hlogdelta : Real.log delta ≤ 0 := by
      calc
        Real.log delta ≤ Real.log 1 := Real.log_le_log hdelta0 hdelta1
        _ = 0 := Real.log_one
    have hh0 : 0 ≤ h := by
      dsimp [h]
      exact le_min heps0 (div_nonneg (neg_nonneg.mpr hlogdelta) hlogX.le)
    have hh1 : h ≤ eps := by dsimp [h]; exact min_le_left _ _
    have hdeltaExponent : Real.log delta ≤ -h * Real.log X := by
      have hmin : h ≤ -Real.log delta / Real.log X := by
        dsimp [h]
        exact min_le_right _ _
      have hmul := (le_div_iff₀ hlogX).mp hmin
      nlinarith
    have hroot1 : Real.sqrt N1 = X ^ (a / 2) := by
      rw [Real.sqrt_eq_rpow, show N1 = X ^ a by rfl,
        ← Real.rpow_mul hXpos.le]
      congr 1
      ring
    have hroot2 : Real.sqrt N2 = X ^ (b / 2) := by
      rw [Real.sqrt_eq_rpow, show N2 = X ^ b by rfl,
        ← Real.rpow_mul hXpos.le]
      congr 1
      ring
    have hroot3 : Real.sqrt N3 = X ^ (c / 2) := by
      rw [Real.sqrt_eq_rpow, show N3 = X ^ c by rfl,
        ← Real.rpow_mul hXpos.le]
      congr 1
      ring
    have hx1 : x ≤ a / 2 - h := by
      have hlogcap := Real.log_le_log hV1pos hcapV1
      rw [hV1pow, Real.log_rpow hXpos,
        Real.log_mul hdelta0.ne'
          (Real.sqrt_pos.2 (by positivity : 0 < N1)).ne',
        hroot1, Real.log_rpow hXpos] at hlogcap
      have hcombined : x * Real.log X ≤ (a / 2 - h) * Real.log X := by
        calc
          x * Real.log X ≤ Real.log delta + a / 2 * Real.log X := hlogcap
          _ ≤ -h * Real.log X + a / 2 * Real.log X :=
            by simpa [add_comm] using
              add_le_add_left hdeltaExponent (a / 2 * Real.log X)
          _ = (a / 2 - h) * Real.log X := by ring
      exact (mul_le_mul_iff_of_pos_right hlogX).mp hcombined
    have hy1 : y ≤ b / 2 := by
      have hlogcap := Real.log_le_log hV2pos hcapV2
      rw [hV2pow, Real.log_rpow hXpos, hroot2, Real.log_rpow hXpos] at hlogcap
      exact (mul_le_mul_iff_of_pos_right hlogX).mp hlogcap
    have hz1 : z ≤ c / 2 := by
      have hlogcap := Real.log_le_log hV3pos hcapV3
      rw [hV3pow, Real.log_rpow hXpos, hroot3, Real.log_rpow hXpos] at hlogcap
      exact (mul_le_mul_iff_of_pos_right hlogX).mp hlogcap
    have hexponent := trilinearLargeDyadicCellExponentBound X T kL eps h
      a b c x y z r N1 N2 N3 V1 V2 V3 m R hXgt hTpos hkLpos
      (by positivity) (by positivity) (by positivity)
      hV1pos hV2pos hV3pos (by rfl) (by rfl) (by rfl) (by rfl) hV1pow
      hV2pow hV3pow hRpow hTupper
      (by simpa [m] using hmeanLevel1.1)
      (by simpa [m] using hmeanLevel1.2)
      (by simpa [m] using hmeanLevel2.1)
      (by simpa [m] using hmeanLevel2.2)
      (by simpa [m] using hmeanLevel3.1)
      (by simpa [m] using hmeanLevel3.2)
      heps0 heps1 hh0 hh1 ha0 hb0 hc0 hx0 hy0 hz0 hr0 hsum
      haLower haUpper hbalance hx1 hy1 hz1
    simpa [h, m, R] using hexponent
  by_cases hempty : cell = ∅
  ·
    have hempty' : trilinearDyadicLargeFactorCell E
        (factorPolynomial (X ^ a) coeff1)
        (factorPolynomial (X ^ b) coeff2)
        (factorPolynomial (X ^ c) coeff3) idx = ∅ := by
      simpa [cell, F1, F2, F3, N1, N2, N3] using hempty
    rw [hempty']
    simp
    positivity
  · have hnonempty : cell.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    rcases hnonempty with ⟨t, ht⟩
    have ht' := ht
    simp only [cell, trilinearDyadicLargeFactorCell, Set.mem_inter_iff] at ht'
    rcases ht' with ⟨hdom, _⟩
    change t ∈ E ∧ _ at hdom
    have hsmallCap : volume.real cell ≤ 2 * kL →
        V1 * V2 * V3 ≤ delta * Real.sqrt X := by
      intro _
      have hcap1' : V1 ≤ delta * Real.sqrt N1 :=
        (hcellBounds t ht).1.1.trans (by simpa [F1, N1] using hsmall t hdom.1)
      have hcap2' : V2 ≤ Real.sqrt N2 :=
        (hcellBounds t ht).2.1.1.trans (by simpa [F2, N2] using hcap2 t hdom.1)
      have hcap3' : V3 ≤ Real.sqrt N3 :=
        (hcellBounds t ht).2.2.1.trans (by simpa [F3, N3] using hcap3 t hdom.1)
      have hprod12 : V1 * V2 ≤ (delta * Real.sqrt N1) * Real.sqrt N2 :=
        mul_le_mul hcap1' hcap2' (by positivity) (by positivity)
      have hprod123 : (V1 * V2) * V3 ≤
          ((delta * Real.sqrt N1) * Real.sqrt N2) * Real.sqrt N3 :=
        mul_le_mul hprod12 hcap3' (by positivity) (by positivity)
      calc
        V1 * V2 * V3 = (V1 * V2) * V3 := by ring
        _ ≤ ((delta * Real.sqrt N1) * Real.sqrt N2) * Real.sqrt N3 := hprod123
        _ = delta * Real.sqrt X := by rw [← hsqrtProduct]; ring
    have hlargeCap : 2 * kL < volume.real cell →
        (volume.real cell / (2 * kL)) * V1 * V2 * V3 ≤
          Real.sqrt X * X ^ (-(min eps (-Real.log delta / Real.log X)) / 16) :=
      hlargeExponent
    have hcellBound := trilinearDyadicCellIntegralBound_by_mass
      T V1 V2 V3 (volume.real cell) kL X eps delta F1 F2 F3 cell
      hXgt heps0 hdelta0 hdelta1 hkLpos (by positivity) (by positivity)
      (by positivity) rfl hcellMeas hcellInterval hpoint hF1 hF2 hF3
      hsmallCap hlargeCap
    simpa [cell, kL, L, F1, F2, F3, N1, N2, N3] using hcellBound

set_option maxHeartbeats 2000000 in
/-- The exact scalar trilinear mean estimate `ldm:trilinear`. The arbitrary
measurable restriction is retained, and all three level packages are obtained
from `factorAndSquareLevelBounds`. -/
theorem trilinearFiveEighths
    (C : ℕ) (X T eps a b c delta : ℝ)
    (coeff1 coeff2 coeff3 : ℕ → ℂ) (E : Set ℝ)
    (hX : 2 ^ 16 ≤ X) (hT : 2 ≤ T)
    (heps0 : 0 < eps) (heps1 : eps ≤ 3 / 16)
    (hTupper : T ≤ X ^ (3 / 8 - eps))
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hsum : a + b + c = 1)
    (haLower : 1 / 4 - eps / 100 ≤ a)
    (haUpper : a ≤ 1 / 2 + eps / 100)
    (hbalance : |b - c| ≤ 1 / 4 + eps / 100)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hEmeas : MeasurableSet E)
    (hEsubset : E ⊆ Set.Icc (-T) T)
    (hcoeff1 : factorCoefficientBound C (X ^ a) coeff1)
    (hcoeff2 : factorCoefficientBound C (X ^ b) coeff2)
    (hcoeff3 : factorCoefficientBound C (X ^ c) coeff3)
    (hcap1 : ∀ t ∈ E,
      ‖factorPolynomial (X ^ a) coeff1 t‖ ≤ Real.sqrt (X ^ a))
    (hcap2 : ∀ t ∈ E,
      ‖factorPolynomial (X ^ b) coeff2 t‖ ≤ Real.sqrt (X ^ b))
    (hcap3 : ∀ t ∈ E,
      ‖factorPolynomial (X ^ c) coeff3 t‖ ≤ Real.sqrt (X ^ c))
    (hsmall : ∀ t ∈ E,
      ‖factorPolynomial (X ^ a) coeff1 t‖ ≤ delta * Real.sqrt (X ^ a)) :
    ∫ t in E,
      ‖factorPolynomial (X ^ a) coeff1 t *
        factorPolynomial (X ^ b) coeff2 t *
        factorPolynomial (X ^ c) coeff3 t‖ ∂volume ≤
      J C * Real.log (4 * X) ^
        (FractionalPrimes.Literature.DirichletMean.b C + 3) * Real.sqrt X *
        (delta ^ (1 / 16 : ℝ) + X ^ (-eps / 16)) := by
  classical
  have heps0 : 0 ≤ eps := heps0.le
  let N1 := X ^ a
  let N2 := X ^ b
  let N3 := X ^ c
  let F1 := factorPolynomial N1 coeff1
  let F2 := factorPolynomial N2 coeff2
  let F3 := factorPolynomial N3 coeff3
  let L := Real.log (4 * X)
  let kL := K C * L ^ FractionalPrimes.Literature.DirichletMean.b C
  let f : ℝ → ℝ := fun t => ‖F1 t * F2 t * F3 t‖
  let region1 : Set ℝ := E ∩ {t | ‖F1 t‖ ≤ 1}
  let region2 : Set ℝ := E ∩ ({t | 1 < ‖F1 t‖} ∩ {t | ‖F2 t‖ ≤ 1})
  let region3 : Set ℝ := E ∩ ({t | 1 < ‖F1 t‖} ∩
    ({t | 1 < ‖F2 t‖} ∩ {t | ‖F3 t‖ ≤ 1}))
  let A := trilinearDyadicLargeFactorDomain E F1 F2 F3
  let parts : Fin 4 → Set ℝ := fun i =>
    if i.val = 0 then region1 else
    if i.val = 1 then region2 else
    if i.val = 2 then region3 else A
  let S : Finset (Fin 4) := Finset.univ
  let cells : (ℕ × ℕ × ℕ) → Set ℝ :=
    fun i => trilinearDyadicLargeFactorCell E F1 F2 F3 i
  let Sidx := trilinearDyadicTripleIndices (Nat.log2 (Nat.floor X) + 1)
  let cellCost : (ℕ × ℕ × ℕ) → ℝ := fun i =>
    ∫ t in cells i, f t ∂volume
  let s1 : ℝ := ∫ t in region1, f t ∂volume
  let s2 : ℝ := ∫ t in region2, f t ∂volume
  let s3 : ℝ := ∫ t in region3, f t ∂volume
  let largeIntegral : ℝ := ∫ t in A, f t ∂volume
  have hXone : 1 ≤ X := by norm_num at hX ⊢; linarith
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXone
  have hXgt : 1 < X := by norm_num at hX ⊢; linarith
  have hTpos : 0 < T := by linarith
  have hgeometry := trilinearExponentGeometry eps a b c heps1
    hsum haLower haUpper hbalance
  have hN1bounds := trilinearLengthBounds X a hX hgeometry.1 hgeometry.2.2.2.1
  have hN2bounds := trilinearLengthBounds X b hX hgeometry.2.1 hgeometry.2.2.2.2.1
  have hN3bounds := trilinearLengthBounds X c hX hgeometry.2.2.1 hgeometry.2.2.2.2.2.1
  have hTleX : T ≤ X := by
    calc
      T ≤ X ^ (3 / 8 - eps) := hTupper
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
      _ = X := by rw [Real.rpow_one]
  have hL : 1 ≤ L := by
    have hlog4 : 1 ≤ Real.log (4 : ℝ) := by
      have h := Real.le_log_one_add_of_nonneg (x := (3 : ℝ)) (by norm_num)
      norm_num at h
      linarith
    have h4X : 4 ≤ 4 * X := by nlinarith
    dsimp [L]
    exact hlog4.trans (Real.log_le_log (by norm_num) h4X)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hkLpos : 0 < kL := by
    dsimp [kL]
    exact mul_pos (constants_positive C).2.2.1 (pow_pos hLpos _)
  have hF1 : Continuous F1 := by
    dsimp [F1, N1]
    exact factorPolynomial_continuous _ _
  have hF2 : Continuous F2 := by
    dsimp [F2, N2]
    exact factorPolynomial_continuous _ _
  have hF3 : Continuous F3 := by
    dsimp [F3, N3]
    exact factorPolynomial_continuous _ _
  have hmean1 := factorMeanSquareIcc_from_powerLevels C X T N1 coeff1
    hX hN1bounds.1 hT hN1bounds.2 hTleX (by simpa [N1] using hcoeff1)
  have hmean2 := factorMeanSquareIcc_from_powerLevels C X T N2 coeff2
    hX hN2bounds.1 hT hN2bounds.2 hTleX (by simpa [N2] using hcoeff2)
  have hmean3 := factorMeanSquareIcc_from_powerLevels C X T N3 coeff3
    hX hN3bounds.1 hT hN3bounds.2 hTleX (by simpa [N3] using hcoeff3)
  have hmean1' : (∫ t in Set.Icc (-T) T, ‖F1 t‖ ^ 2 ∂volume) ≤
      K C * Real.log (4 * X) ^ FractionalPrimes.Literature.DirichletMean.b C * (T + N1) := by
    simpa [F1] using hmean1
  have hmean2' : (∫ t in Set.Icc (-T) T, ‖F2 t‖ ^ 2 ∂volume) ≤
      K C * Real.log (4 * X) ^ FractionalPrimes.Literature.DirichletMean.b C * (T + N2) := by
    simpa [F2] using hmean2
  have hmean3' : (∫ t in Set.Icc (-T) T, ‖F3 t‖ ^ 2 ∂volume) ≤
      K C * Real.log (4 * X) ^ FractionalPrimes.Literature.DirichletMean.b C * (T + N3) := by
    simpa [F3] using hmean3
  have hless1 : MeasurableSet {t : ℝ | ‖F1 t‖ ≤ 1} :=
    measurableSet_le hF1.norm.measurable measurable_const
  have hless2 : MeasurableSet {t : ℝ | ‖F2 t‖ ≤ 1} :=
    measurableSet_le hF2.norm.measurable measurable_const
  have hless3 : MeasurableSet {t : ℝ | ‖F3 t‖ ≤ 1} :=
    measurableSet_le hF3.norm.measurable measurable_const
  have hgreater1 : MeasurableSet {t : ℝ | 1 < ‖F1 t‖} :=
    measurableSet_Ioi.preimage hF1.norm.measurable
  have hgreater2 : MeasurableSet {t : ℝ | 1 < ‖F2 t‖} :=
    measurableSet_Ioi.preimage hF2.norm.measurable
  have hregion1Meas : MeasurableSet region1 := by
    dsimp [region1]
    exact hEmeas.inter hless1
  have hregion2Meas : MeasurableSet region2 := by
    dsimp [region2]
    exact hEmeas.inter (hgreater1.inter hless2)
  have hregion3Meas : MeasurableSet region3 := by
    dsimp [region3]
    exact hEmeas.inter (hgreater1.inter (hgreater2.inter hless3))
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact trilinearDyadicLargeFactorDomain_measurable E F1 F2 F3
      hEmeas hF1 hF2 hF3
  have hregion1Subset : region1 ⊆ Set.Icc (-T) T := by
    intro t ht
    exact hEsubset ht.1
  have hregion2Subset : region2 ⊆ Set.Icc (-T) T := by
    intro t ht
    exact hEsubset ht.1
  have hregion3Subset : region3 ⊆ Set.Icc (-T) T := by
    intro t ht
    exact hEsubset ht.1
  have hsmall1 : ∀ t ∈ region1, ‖F1 t‖ ≤ 1 := by
    intro t ht
    exact ht.2
  have hsmall2 : ∀ t ∈ region2, ‖F2 t‖ ≤ 1 := by
    intro t ht
    exact ht.2.2
  have hsmall3 : ∀ t ∈ region3, ‖F3 t‖ ≤ 1 := by
    intro t ht
    exact ht.2.2.2
  have hpair := trilinearPairExponentBounds eps a b c heps0 heps1
    ha0 hb0 hc0 hsum haLower haUpper hbalance
  have hs1 : s1 ≤ 2 * K C * Real.log (4 * X) ^
      FractionalPrimes.Literature.DirichletMean.b C * X ^ ((15 : ℝ) / 32) := by
    dsimp [s1, f, F1, F2, F3, N1, N2, N3]
    exact trilinearSmallFactorIntegralBound C X T eps (X ^ b) (X ^ c) b c
      (factorPolynomial (X ^ a) coeff1)
      (factorPolynomial (X ^ b) coeff2)
      (factorPolynomial (X ^ c) coeff3) region1
      hX hT heps0 heps1 hTupper rfl rfl hgeometry.2.2.2.2.1
      hgeometry.2.2.2.2.2.1 hgeometry.2.2.2.2.2.2.2.2
      hregion1Meas hregion1Subset hsmall1
      (factorPolynomial_continuous _ _) (factorPolynomial_continuous _ _)
      (factorPolynomial_continuous _ _) hmean2' hmean3'
  have hs2 : s2 ≤ 2 * K C * Real.log (4 * X) ^
      FractionalPrimes.Literature.DirichletMean.b C * X ^ ((15 : ℝ) / 32) := by
    dsimp [s2, f, F1, F2, F3, N1, N2, N3]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      trilinearSmallFactorIntegralBound C X T eps (X ^ a) (X ^ c) a c
      (factorPolynomial (X ^ b) coeff2)
      (factorPolynomial (X ^ a) coeff1)
      (factorPolynomial (X ^ c) coeff3) region2
      hX hT heps0 heps1 hTupper rfl rfl
      hgeometry.2.2.2.1 hgeometry.2.2.2.2.2.1 hgeometry.2.2.2.2.2.2.2.1
      hregion2Meas hregion2Subset hsmall2
      (factorPolynomial_continuous _ _) (factorPolynomial_continuous _ _)
      (factorPolynomial_continuous _ _) hmean1' hmean3'
  have hs3 : s3 ≤ 2 * K C * Real.log (4 * X) ^
      FractionalPrimes.Literature.DirichletMean.b C * X ^ ((15 : ℝ) / 32) := by
    dsimp [s3, f, F1, F2, F3, N1, N2, N3]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      trilinearSmallFactorIntegralBound C X T eps (X ^ a) (X ^ b) a b
      (factorPolynomial (X ^ c) coeff3)
      (factorPolynomial (X ^ a) coeff1)
      (factorPolynomial (X ^ b) coeff2) region3
      hX hT heps0 heps1 hTupper rfl rfl
      hgeometry.2.2.2.1 hgeometry.2.2.2.2.1 hgeometry.2.2.2.2.2.2.1
      hregion3Meas hregion3Subset hsmall3
      (factorPolynomial_continuous _ _) (factorPolynomial_continuous _ _)
      (factorPolynomial_continuous _ _) hmean1' hmean2'
  have hpartsMeas : ∀ i ∈ S, MeasurableSet (parts i) := by
    intro i hi
    fin_cases i
    · simpa [parts] using hregion1Meas
    · simpa [parts] using hregion2Meas
    · simpa [parts] using hregion3Meas
    · simpa [parts] using hAmeas
  have hpartsDisjoint : Set.Pairwise (↑S : Set (Fin 4))
      (fun i j => Disjoint (parts i) (parts j)) := by
    intro i hi j hj hne
    fin_cases i <;> fin_cases j <;>
      simp_all [parts, region1, region2, region3, A,
        trilinearDyadicLargeFactorDomain, Set.disjoint_left,
        Set.mem_inter_iff]
  have hpartsCover : E = ⋃ i ∈ S, parts i := by
    ext t
    constructor
    · intro ht
      by_cases h1 : ‖F1 t‖ ≤ 1
      · refine Set.mem_iUnion.mpr ⟨⟨0, by decide⟩,
          Set.mem_iUnion.mpr ⟨by simp [S], ?_⟩⟩
        simp [parts, region1, h1, ht]
      · have h1gt : 1 < ‖F1 t‖ := lt_of_not_ge h1
        by_cases h2 : ‖F2 t‖ ≤ 1
        · refine Set.mem_iUnion.mpr ⟨⟨1, by decide⟩,
            Set.mem_iUnion.mpr ⟨by simp [S], ?_⟩⟩
          simp [parts, region2, h1gt, h2, ht]
        · have h2gt : 1 < ‖F2 t‖ := lt_of_not_ge h2
          by_cases h3 : ‖F3 t‖ ≤ 1
          · refine Set.mem_iUnion.mpr ⟨⟨2, by decide⟩,
              Set.mem_iUnion.mpr ⟨by simp [S], ?_⟩⟩
            simp [parts, region3, h1gt, h2gt, h3, ht]
          · have h3gt : 1 < ‖F3 t‖ := lt_of_not_ge h3
            refine Set.mem_iUnion.mpr ⟨⟨3, by decide⟩,
              Set.mem_iUnion.mpr ⟨by simp [S], ?_⟩⟩
            simp [parts, A, trilinearDyadicLargeFactorDomain,
              h1gt, h2gt, h3gt, ht]
    · intro ht
      rcases Set.mem_iUnion.mp ht with ⟨i, ht⟩
      rcases Set.mem_iUnion.mp ht with ⟨hi, hpart⟩
      fin_cases i <;>
        simp_all [parts, region1, region2, region3, A,
          trilinearDyadicLargeFactorDomain, Set.mem_inter_iff]
  have hcontf : Continuous f := by
    dsimp [f]
    exact (((hF1.mul hF2).mul hF3).norm)
  have hIntI : IntegrableOn f (Set.Icc (-T) T) :=
    hcontf.continuousOn.integrableOn_compact isCompact_Icc
  have hIntE : IntegrableOn f E := hIntI.mono_set hEsubset
  have hAsubE : A ⊆ E := by
    intro t ht
    exact ht.1
  have hIntA : IntegrableOn f A := hIntE.mono_set hAsubE
  have hpartsIntegral := trilinearDyadicLargeFactorDomain_integral_eq_sum
    S E parts f hpartsCover hpartsMeas hpartsDisjoint hIntE
  have hpartsSum : (∑ i ∈ S, ∫ t in parts i, f t ∂volume) =
      s1 + s2 + s3 + largeIntegral := by
    simp [S, parts, s1, s2, s3, largeIntegral, Fin.sum_univ_four]
  have hIntegralSplit : (∫ t in E, f t ∂volume) =
      s1 + s2 + s3 + largeIntegral := by
    calc
      (∫ t in E, f t ∂volume) = ∑ i ∈ S, ∫ t in parts i, f t ∂volume :=
        hpartsIntegral
      _ = s1 + s2 + s3 + largeIntegral := hpartsSum
  have hbound1 : ∀ t ∈ E, ‖F1 t‖ ≤ Real.sqrt X := by
    intro t ht
    exact (hcap1 t ht).trans (Real.sqrt_le_sqrt hN1bounds.2)
  have hbound2 : ∀ t ∈ E, ‖F2 t‖ ≤ Real.sqrt X := by
    intro t ht
    exact (hcap2 t ht).trans (Real.sqrt_le_sqrt hN2bounds.2)
  have hbound3 : ∀ t ∈ E, ‖F3 t‖ ≤ Real.sqrt X := by
    intro t ht
    exact (hcap3 t ht).trans (Real.sqrt_le_sqrt hN3bounds.2)
  have hdyadicCover := trilinearDyadicLargeFactorDomain_eq_finiteCells
    X hX E F1 F2 F3 hbound1 hbound2 hbound3
  have hcellMeas : ∀ i ∈ Sidx, MeasurableSet (cells i) := by
    intro i hi
    dsimp [cells]
    exact trilinearDyadicLargeFactorCell_measurable E F1 F2 F3 i
      hEmeas hF1 hF2 hF3
  have hcellDisjoint : Set.Pairwise (↑Sidx : Set (ℕ × ℕ × ℕ))
      (fun i j => Disjoint (cells i) (cells j)) := by
    intro i hi j hj hne
    dsimp [cells]
    exact trilinearDyadicLargeFactorCell_disjoint E F1 F2 F3 hne
  have hlargeEq : largeIntegral = ∑ i ∈ Sidx, cellCost i := by
    dsimp [largeIntegral, cells, cellCost, A, f, F1, F2, F3, N1, N2, N3] at *
    exact trilinearDyadicLargeFactorDomain_integral_eq_sum
      Sidx (trilinearDyadicLargeFactorDomain E
        (factorPolynomial (X ^ a) coeff1)
        (factorPolynomial (X ^ b) coeff2)
        (factorPolynomial (X ^ c) coeff3))
      (fun i => trilinearDyadicLargeFactorCell E
        (factorPolynomial (X ^ a) coeff1)
        (factorPolynomial (X ^ b) coeff2)
        (factorPolynomial (X ^ c) coeff3) i)
      (fun t => ‖factorPolynomial (X ^ a) coeff1 t *
        factorPolynomial (X ^ b) coeff2 t *
        factorPolynomial (X ^ c) coeff3 t‖)
      hdyadicCover hcellMeas hcellDisjoint hIntA
  have hcellCostBound : ∀ i ∈ Sidx,
      cellCost i ≤ 16 * kL * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) := by
    intro i hi
    dsimp [cellCost, cells, f, F1, F2, F3, N1, N2, N3, kL, L]
    exact trilinearLargeFactorCellCost C X T eps a b c delta
      coeff1 coeff2 coeff3 E i hX hT heps0 heps1 hTupper
      ha0 hb0 hc0 hsum haLower haUpper hbalance hdelta0 hdelta1
      hEmeas hEsubset
      (by simpa [N2] using hcap2)
      (by simpa [N3] using hcap3)
      (by simpa [N1] using hsmall) hcoeff1 hcoeff2 hcoeff3
  have hcount : (Sidx.card : ℝ) ≤ 8 * L ^ 3 := by
    dsimp [Sidx, L]
    exact trilinearDyadicLevelTripleCardBound X hX
  have hassembly := trilinearDyadicAndSmallFactorAssembly
    Sidx L kL X eps delta s1 s2 s3 cellCost
    hXgt hL (le_of_lt hkLpos) heps0 heps1 hdelta0 hdelta1
    hcount hcellCostBound
    (by
      calc
        s1 ≤ 2 * K C * Real.log (4 * X) ^
            FractionalPrimes.Literature.DirichletMean.b C * X ^ ((15 : ℝ) / 32) := hs1
        _ = 2 * kL * X ^ ((15 : ℝ) / 32) := by dsimp [kL, L]; ring)
    (by
      calc
        s2 ≤ 2 * K C * Real.log (4 * X) ^
            FractionalPrimes.Literature.DirichletMean.b C * X ^ ((15 : ℝ) / 32) := hs2
        _ = 2 * kL * X ^ ((15 : ℝ) / 32) := by dsimp [kL, L]; ring)
    (by
      calc
        s3 ≤ 2 * K C * Real.log (4 * X) ^
            FractionalPrimes.Literature.DirichletMean.b C * X ^ ((15 : ℝ) / 32) := hs3
        _ = 2 * kL * X ^ ((15 : ℝ) / 32) := by dsimp [kL, L]; ring)
  have hmaxsum : max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) ≤
      X ^ (-eps / 16) + delta ^ (1 / 16 : ℝ) := by
    apply max_le_iff.mpr
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · exact le_add_of_nonneg_left (by positivity)
  have hfinalScale : 256 * kL * L ^ 3 * Real.sqrt X *
      (X ^ (-eps / 16) + delta ^ (1 / 16 : ℝ)) =
      J C * Real.log (4 * X) ^
        (FractionalPrimes.Literature.DirichletMean.b C + 3) * Real.sqrt X *
        (delta ^ (1 / 16 : ℝ) + X ^ (-eps / 16)) := by
    dsimp [kL, L, J]
    rw [pow_add]
    ring
  calc
    (∫ t in E,
        ‖factorPolynomial (X ^ a) coeff1 t *
          factorPolynomial (X ^ b) coeff2 t *
          factorPolynomial (X ^ c) coeff3 t‖ ∂volume) =
        s1 + s2 + s3 + (∑ i ∈ Sidx, cellCost i) := by
      calc
        _ = s1 + s2 + s3 + largeIntegral := by simpa [f] using hIntegralSplit
        _ = s1 + s2 + s3 + (∑ i ∈ Sidx, cellCost i) := by rw [hlargeEq]
    _ ≤ 256 * kL * L ^ 3 * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) := hassembly
    _ ≤ 256 * kL * L ^ 3 * Real.sqrt X *
        (X ^ (-eps / 16) + delta ^ (1 / 16 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hmaxsum
      positivity
    _ = J C * Real.log (4 * X) ^
        (FractionalPrimes.Literature.DirichletMean.b C + 3) * Real.sqrt X *
        (delta ^ (1 / 16 : ℝ) + X ^ (-eps / 16)) := hfinalScale

#print axioms FractionalPrimes.Literature.DirichletMean.trilinearFiveEighths

end

end FractionalPrimes.Literature.DirichletMean

end
