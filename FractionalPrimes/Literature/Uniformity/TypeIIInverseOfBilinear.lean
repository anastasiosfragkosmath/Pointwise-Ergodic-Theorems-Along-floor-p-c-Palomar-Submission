module

public import FractionalPrimes.Literature.Uniformity.ArithmeticInverseTasks
public import FractionalPrimes.Literature.Uniformity.BilinearCoefficientTask
public import FractionalPrimes.Literature.Polynomial.PolynomialTypeI2Inverse

/-!
# Reduction of the ordinary Type-II inverse clause to the bilinear task

This file formalizes blueprint item `lu:bilinear-to-ii`.  The preliminary
lemmas below isolate the exact dyadic index set that can meet `(4,2X]` and
the canonical centered presentation of the polynomial phase.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The dyadic blocks `(2^(k-1),2^k]` whose lower endpoint is at least four. -/
def typeIIActiveDyadicIndices (N : ℕ) : Finset ℕ :=
  Finset.Icc 3 (Nat.log2 N + 1)

theorem typeIIActiveDyadicIndices_subset (N : ℕ) :
    typeIIActiveDyadicIndices N ⊆ typeIDyadicIndices N := by
  intro k hk
  rw [typeIIActiveDyadicIndices, Finset.mem_Icc] at hk
  exact Finset.mem_Icc.mpr ⟨by omega, hk.2⟩

/-- A block outside the active range contains only integers at most four. -/
theorem typeIDyadicBlock_le_four_of_not_active
    (N k m : ℕ) (hk : k ∈ typeIDyadicIndices N)
    (hknot : k ∉ typeIIActiveDyadicIndices N)
    (hm : m ∈ typeIDyadicBlock N k) : m ≤ 4 := by
  rw [typeIDyadicIndices, Finset.mem_Icc] at hk
  rw [typeIIActiveDyadicIndices, Finset.mem_Icc] at hknot
  rw [typeIDyadicBlock, Finset.mem_filter] at hm
  have hklt : k < 3 := by omega
  have hscale : 2 * typeIDyadicScale k ≤ 4 := by
    interval_cases k <;> norm_num [typeIDyadicScale]
  have hmreal : (m : ℝ) ≤ 4 := hm.2.2.trans hscale
  exact_mod_cast hmreal

/-- The number of active dyadic blocks is strictly less than `4/δ` under the
exact source logarithmic smallness hypothesis. -/
theorem typeIIActiveDyadicIndices_card_bound
    (X H δ : ℝ) (hX : 3 ≤ X) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hδ : 0 < δ) (hδlog : δ < (Real.log X)⁻¹) :
    ((typeIIActiveDyadicIndices (Nat.floor (X + H))).card : ℝ) <
      4 * δ⁻¹ := by
  let N := Nat.floor (X + H)
  have hXpos : 0 < X := by linarith
  have hNne : N ≠ 0 := by
    have hsum3 : 3 ≤ X + H := by linarith
    have hthree : 3 ≤ N := by
      dsimp [N]
      exact Nat.le_floor hsum3
    omega
  have hpowNat : 2 ^ Nat.log2 N ≤ N := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hNne
  have hfloorLe : (N : ℝ) ≤ X + H := by
    dsimp [N]
    exact Nat.floor_le (by linarith)
  have hpowReal : (2 : ℝ) ^ Nat.log2 N ≤ 2 * X := by
    calc
      (2 : ℝ) ^ Nat.log2 N = ((2 ^ Nat.log2 N : ℕ) : ℝ) := by norm_cast
      _ ≤ (N : ℝ) := by exact_mod_cast hpowNat
      _ ≤ X + H := hfloorLe
      _ ≤ 2 * X := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogTwo : (2 / 3 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogTwoLe : Real.log 2 ≤ Real.log X :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith)
  have hlogPow :
      (Nat.log2 N : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log X := by
    calc
      (Nat.log2 N : ℝ) * Real.log 2 =
          Real.log ((2 : ℝ) ^ Nat.log2 N) := by rw [Real.log_pow]
      _ ≤ Real.log (2 * X) := Real.log_le_log (by positivity) hpowReal
      _ = Real.log 2 + Real.log X := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
  have hlogNat : (Nat.log2 N : ℝ) ≤ 3 * Real.log X := by
    have hnonneg : 0 ≤ (Nat.log2 N : ℝ) := by positivity
    nlinarith [hlogPow, hlogTwo, hlogTwoLe]
  have hcardLeNat : (typeIIActiveDyadicIndices N).card ≤ Nat.log2 N := by
    simp only [typeIIActiveDyadicIndices, Nat.card_Icc]
    omega
  have hcardLe : ((typeIIActiveDyadicIndices N).card : ℝ) ≤
      (Nat.log2 N : ℝ) := by exact_mod_cast hcardLeNat
  have hδprod : δ * Real.log X < 1 := by
    apply (lt_div_iff₀ hlogXpos).mp
    simpa [one_div] using hδlog
  have hloglt : Real.log X < δ⁻¹ := by
    have : Real.log X < 1 / δ := (lt_div_iff₀ hδ).2 (by nlinarith)
    simpa [one_div] using this
  change ((typeIIActiveDyadicIndices N).card : ℝ) < 4 * δ⁻¹
  calc
    _ ≤ (Nat.log2 N : ℝ) := hcardLe
    _ ≤ 3 * Real.log X := hlogNat
    _ < 3 * δ⁻¹ := by nlinarith
    _ < 4 * δ⁻¹ := by have := inv_pos.mpr hδ; nlinarith

/-- The canonical centered coefficients reconstruct the original phase. -/
theorem bilinearCenteredPhase_centeredCoefficients
    (d : ℕ) (X : ℤ) (P : Polynomial ℝ) (hP : P.natDegree ≤ d) :
    bilinearCenteredPhase (X : ℝ) d
        (fun i => (phaseCenteredAt P X).coeff i) = P := by
  let ν : ℕ → ℝ := fun i => (phaseCenteredAt P X).coeff i
  have hexp := phaseCenteredAt_monomial_expansion P hP X
  have hexp' : phaseCenteredAt P X =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C ((phaseCenteredAt P X).coeff j) * Polynomial.X ^ j := by
    simpa [phaseCenteredAt, add_comm] using hexp
  have hcomp :
      (phaseCenteredAt P X).comp
          (Polynomial.X - Polynomial.C (X : ℝ)) = P := by
    rw [phaseCenteredAt, Polynomial.comp_assoc]
    simp
  calc
    bilinearCenteredPhase (X : ℝ) d ν =
        (phaseCenteredAt P X).comp
          (Polynomial.X - Polynomial.C (X : ℝ)) := by
      rw [hexp']
      unfold bilinearCenteredPhase
      simp only [Polynomial.sum_comp, Polynomial.mul_comp,
        Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
      rfl
    _ = P := hcomp

/-- The contribution of one dyadic block in the second Type-II factor. -/
def typeIIBlockCorrelation (N k : ℕ)
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) : ℂ :=
  ∑ m ∈ typeIDyadicBlock N k, ∑ l ∈ Finset.Icc 1 N,
    if l * m ∈ typeIIntervalSet X H then
      complexPositiveIntegerNatExtension α l *
        complexPositiveIntegerNatExtension β m *
        unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ))
    else 0

/-- The exact factor-pair sum is the sum of all dyadic second-factor
blocks. -/
theorem typeIScalarPhaseSum_eq_typeIIBlockCorrelation_sum
    (N : ℕ) (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (hinterval : typeIIntervalSet X H ⊆ Finset.Icc 1 N) :
    typeIScalarPhaseSum (complexPositiveDirichletConvolution α β) P X H =
      ∑ k ∈ typeIDyadicIndices N,
        typeIIBlockCorrelation N k α β P X H := by
  rw [typeIScalarPhaseSum_eq_factor_pair_sum α β P X H N hinterval]
  rw [Finset.sum_comm]
  rw [sum_typeIDyadicBlocks N]
  rfl

/-- A finite sum with large norm and fewer than `4/δ` summands has a
summand of norm at least `δ²H/4`. -/
theorem exists_norm_ge_delta_sq_quarter_of_norm_sum_ge
    (s : Finset ℕ) (z : ℕ → ℂ) (δ H : ℝ)
    (hδ : 0 < δ) (hH : 0 < H)
    (hcard : (s.card : ℝ) < 4 * δ⁻¹)
    (hsum : δ * H ≤ ‖∑ k ∈ s, z k‖) :
    ∃ k ∈ s, δ ^ 2 * H / 4 ≤ ‖z k‖ := by
  have hs : s.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
    simp at hsum
    nlinarith
  by_contra hlarge
  push_neg at hlarge
  have hnormsum : ‖∑ k ∈ s, z k‖ ≤ ∑ k ∈ s, ‖z k‖ :=
    norm_sum_le _ _
  have hpointwise : ∑ k ∈ s, ‖z k‖ <
      ∑ _k ∈ s, δ ^ 2 * H / 4 := by
    exact Finset.sum_lt_sum_of_nonempty hs hlarge
  have hthreshold : 0 < δ ^ 2 * H / 4 := by positivity
  have hcardmul : (s.card : ℝ) * (δ ^ 2 * H / 4) < δ * H := by
    have hmul := mul_lt_mul_of_pos_right hcard hthreshold
    have hinv : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ.ne'
    rw [Finset.sum_const, nsmul_eq_mul] at hpointwise
    nlinarith
  rw [Finset.sum_const, nsmul_eq_mul] at hpointwise
  linarith

/-- If the supported first factor is shorter than `X/4`, every block below
the active dyadic range vanishes. -/
theorem typeIIBlockCorrelation_eq_zero_of_not_active
    (N k : ℕ) (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H Aminus Aplus : ℝ)
    (hk : k ∈ typeIDyadicIndices N)
    (hknot : k ∉ typeIIActiveDyadicIndices N)
    (hAplus : 0 ≤ Aplus) (hXA : 4 * Aplus < X)
    (hsupp : complexPositiveSupportedOnInterval α Aminus Aplus) :
    typeIIBlockCorrelation N k α β P X H = 0 := by
  unfold typeIIBlockCorrelation
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hprod : l * m ∈ typeIIntervalSet X H
  · rw [if_pos hprod]
    have hmle : m ≤ 4 :=
      typeIDyadicBlock_le_four_of_not_active N k m hk hknot hm
    have hlpos : 0 < l := by
      have := (Finset.mem_Icc.mp hl).1
      omega
    have hαzero : complexPositiveIntegerNatExtension α l = 0 := by
      by_contra hne
      have hαne : α ⟨l, hlpos⟩ ≠ 0 := by
        simpa [complexPositiveIntegerNatExtension, hlpos] using hne
      have hlupper : (l : ℝ) ≤ Aplus := (hsupp ⟨l, hlpos⟩ hαne).2
      have hmcast : (m : ℝ) ≤ 4 := by exact_mod_cast hmle
      have hprodle : (l : ℝ) * (m : ℝ) ≤ Aplus * 4 :=
        mul_le_mul hlupper hmcast (by positivity) hAplus
      have hprodlower := (mem_typeIIntervalSet X H (l * m)).mp hprod |>.2.1
      have hcast : (((l * m : ℕ) : ℝ)) = (l : ℝ) * (m : ℝ) := by
        norm_num
      rw [hcast] at hprodlower
      linarith
    simp [hαzero]
  · simp [hprod]

/-- After the short first factor forces all second factors above four, the
scalar correlation is exactly the sum over the active dyadic blocks. -/
theorem typeIScalarPhaseSum_eq_active_typeIIBlockCorrelation_sum
    (N : ℕ) (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H Aminus Aplus : ℝ)
    (hinterval : typeIIntervalSet X H ⊆ Finset.Icc 1 N)
    (hAplus : 0 ≤ Aplus) (hXA : 4 * Aplus < X)
    (hsupp : complexPositiveSupportedOnInterval α Aminus Aplus) :
    typeIScalarPhaseSum (complexPositiveDirichletConvolution α β) P X H =
      ∑ k ∈ typeIIActiveDyadicIndices N,
        typeIIBlockCorrelation N k α β P X H := by
  rw [typeIScalarPhaseSum_eq_typeIIBlockCorrelation_sum N α β P X H hinterval]
  exact (Finset.sum_subset (typeIIActiveDyadicIndices_subset N)
    (fun k hk hknot =>
      typeIIBlockCorrelation_eq_zero_of_not_active N k α β P X H
        Aminus Aplus hk hknot hAplus hXA hsupp)).symm

/-- The finite conditional inner sum used in the dyadic decomposition is
exactly the product-window inner sum in the bilinear task. -/
theorem typeIIConditionalInnerSum_eq_bilinearInner
    (N m : ℕ) (X H : ℝ) (hm : 0 < m)
    (hN : N = Nat.floor (X + H))
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ) :
    (∑ l ∈ Finset.Icc 1 N,
      if l * m ∈ typeIIntervalSet X H then
        complexPositiveIntegerNatExtension α l *
          complexPositiveIntegerNatExtension β m *
          unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ))
      else 0) =
    ∑ l ∈ bilinearProductIntervalSet X H m,
      complexPositiveIntegerNatExtension α l *
        complexPositiveIntegerNatExtension β m *
        unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ)) := by
  rw [← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc,
    mem_typeIIntervalSet, mem_bilinearProductIntervalSet X H m l hm]
  constructor
  · rintro ⟨⟨hlone, hlN⟩, hprodOne, hprodLower, hprodUpper⟩
    exact ⟨hlone, hprodLower, hprodUpper⟩
  · rintro ⟨hlone, hprodLower, hprodUpper⟩
    have hmone : 1 ≤ m := hm
    have hlprod : l ≤ l * m := by
      simpa using Nat.mul_le_mul_left l hmone
    have hlupper : (l : ℝ) ≤ X + H := by
      calc
        (l : ℝ) ≤ ((l * m : ℕ) : ℝ) := by exact_mod_cast hlprod
        _ ≤ X + H := hprodUpper
    have hlN : l ≤ N := by rw [hN]; exact Nat.le_floor hlupper
    have hprodOne : 1 ≤ l * m := Nat.mul_pos (by omega) hm
    exact ⟨⟨hlone, hlN⟩, hprodOne, hprodLower, hprodUpper⟩

theorem typeIDyadicBlock_subset_bilinearRightSet (N k : ℕ) :
    typeIDyadicBlock N k ⊆ bilinearRightSet (typeIDyadicScale k) := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmN, hmrange⟩
  rw [mem_bilinearRightSet]
  exact ⟨(Finset.mem_Icc.mp hmN).1, hmrange.1, hmrange.2⟩

/-- Padding a finite dyadic block past `floor (X+H)` adds no terms, so the
selected block is exactly the bilinear correlation `S`. -/
theorem typeIIBlockCorrelation_eq_bilinearS
    (N k : ℕ) (X H : ℝ) (hN : N = Nat.floor (X + H))
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ) :
    typeIIBlockCorrelation N k α β P X H =
      bilinearS X H (typeIDyadicScale k)
        (complexPositiveIntegerNatExtension α)
        (complexPositiveIntegerNatExtension β) P := by
  let inner : ℕ → ℂ := fun m =>
    ∑ l ∈ bilinearProductIntervalSet X H m,
      complexPositiveIntegerNatExtension α l *
        complexPositiveIntegerNatExtension β m *
        unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ))
  calc
    typeIIBlockCorrelation N k α β P X H =
        ∑ m ∈ typeIDyadicBlock N k, inner m := by
      unfold typeIIBlockCorrelation
      apply Finset.sum_congr rfl
      intro m hm
      have hmpos : 0 < m := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
        omega
      exact typeIIConditionalInnerSum_eq_bilinearInner
        N m X H hmpos hN α β P
    _ = ∑ m ∈ bilinearRightSet (typeIDyadicScale k), inner m := by
      apply Finset.sum_subset (typeIDyadicBlock_subset_bilinearRightSet N k)
      intro m hmright hmnot
      have hmdata := (mem_bilinearRightSet (typeIDyadicScale k) m).mp hmright
      have hmNlt : N < m := by
        by_contra hnotlt
        have hmN : m ≤ N := le_of_not_gt hnotlt
        apply hmnot
        rw [typeIDyadicBlock, Finset.mem_filter]
        exact ⟨Finset.mem_Icc.mpr ⟨hmdata.1, hmN⟩, hmdata.2.1, hmdata.2.2⟩
      dsimp [inner]
      apply Finset.sum_eq_zero
      intro l hl
      have hmpos : 0 < m := by omega
      have hldata :=
        (mem_bilinearProductIntervalSet X H m l hmpos).mp hl
      have hmleprod : m ≤ l * m := by
        calc
          m = 1 * m := by simp
          _ ≤ l * m := Nat.mul_le_mul_right m hldata.1
      have hprodN : l * m ≤ N := by
        rw [hN]
        exact Nat.le_floor hldata.2.2
      omega
    _ = bilinearS X H (typeIDyadicScale k)
          (complexPositiveIntegerNatExtension α)
          (complexPositiveIntegerNatExtension β) P := by
      rfl

/-- A nonzero dyadic block contains an actual nonzero factor pair. -/
theorem typeIIBlockCorrelation_nonzero_pair
    (N k : ℕ) (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (hblock : typeIIBlockCorrelation N k α β P X H ≠ 0) :
    ∃ m ∈ typeIDyadicBlock N k, ∃ l ∈ Finset.Icc 1 N,
      l * m ∈ typeIIntervalSet X H ∧
      complexPositiveIntegerNatExtension α l ≠ 0 ∧
      complexPositiveIntegerNatExtension β m ≠ 0 := by
  unfold typeIIBlockCorrelation at hblock
  obtain ⟨m, hm, hmSum⟩ := Finset.exists_ne_zero_of_sum_ne_zero hblock
  obtain ⟨l, hl, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmSum
  have hprod : l * m ∈ typeIIntervalSet X H := by
    by_contra hnot
    simp [hnot] at hterm
  rw [if_pos hprod] at hterm
  have hcoeff :
      complexPositiveIntegerNatExtension α l *
        complexPositiveIntegerNatExtension β m ≠ 0 :=
    (mul_ne_zero_iff.mp hterm).1
  exact ⟨m, hm, l, hl, hprod,
    (mul_ne_zero_iff.mp hcoeff).1, (mul_ne_zero_iff.mp hcoeff).2⟩

/-- The active blocks all have bilinear scale at least two. -/
theorem typeIIActiveDyadicScale_ge_two
    (N k : ℕ) (hk : k ∈ typeIIActiveDyadicIndices N) :
    2 ≤ typeIDyadicScale k := by
  have hkthree : 3 ≤ k :=
    (Finset.mem_Icc.mp (show k ∈ Finset.Icc 3 (Nat.log2 N + 1) from hk)).1
  have hkzero : k ≠ 0 := by omega
  simp only [typeIDyadicScale, if_neg hkzero]
  norm_cast
  have : 1 ≤ k - 1 := by omega
  simpa using pow_le_pow_right' (a := (2 : ℕ)) (by omega) this

/-- The second-moment assumption gives the normalized bound `U²≤2δ⁻¹`. -/
theorem bilinearU_sq_le_two_inv
    (δ L : ℝ) (hL : 0 < L) (h2L : 1 ≤ 2 * L)
    (α : ComplexPositiveIntegerFunction)
    (hMoment : complexPositiveSecondMomentBound δ α) :
    bilinearU L (complexPositiveIntegerNatExtension α) ^ 2 ≤ 2 * δ⁻¹ := by
  have hsubset : bilinearLeftSet L ⊆ Finset.Icc 1 (Nat.floor (2 * L)) :=
    Finset.filter_subset _ _
  have hsum :
      (∑ l ∈ bilinearLeftSet L,
          ‖complexPositiveIntegerNatExtension α l‖ ^ 2) ≤
        complexPositiveSecondMoment α (2 * L) := by
    calc
      (∑ l ∈ bilinearLeftSet L,
          ‖complexPositiveIntegerNatExtension α l‖ ^ 2) =
          ∑ l ∈ bilinearLeftSet L,
            complexPositiveSecondMomentSummand α l := by
        apply Finset.sum_congr rfl
        intro l hl
        have hlpos : 0 < l := by
          have := (mem_bilinearLeftSet L l).mp hl |>.1
          omega
        simp [complexPositiveIntegerNatExtension,
          complexPositiveSecondMomentSummand, hlpos]
      _ ≤ complexPositiveSecondMoment α (2 * L) := by
        unfold complexPositiveSecondMoment
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro l hl hnot
        simp only [complexPositiveSecondMomentSummand]
        split <;> positivity
  rw [bilinearU_sq L hL]
  unfold bilinearU2
  calc
    L⁻¹ * ∑ l ∈ bilinearLeftSet L,
        ‖complexPositiveIntegerNatExtension α l‖ ^ 2 ≤
        L⁻¹ * complexPositiveSecondMoment α (2 * L) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hL.le)
    _ ≤ L⁻¹ * (δ⁻¹ * (2 * L)) :=
      mul_le_mul_of_nonneg_left (hMoment (2 * L) h2L)
        (inv_nonneg.mpr hL.le)
    _ = 2 * δ⁻¹ := by field_simp

/-- The fourth-moment assumption gives the normalized bound `V⁴≤2δ⁻²`. -/
theorem bilinearV_pow_four_le_two_inv_sq
    (δ M : ℝ) (hM : 0 < M) (h2M : 1 ≤ 2 * M)
    (β : ComplexPositiveIntegerFunction)
    (hMoment : complexPositiveFourthMomentBound δ β) :
    bilinearV M (complexPositiveIntegerNatExtension β) ^ 4 ≤
      2 * δ⁻¹ ^ 2 := by
  have hsubset : bilinearRightSet M ⊆ Finset.Icc 1 (Nat.floor (2 * M)) :=
    Finset.filter_subset _ _
  have hsum :
      (∑ m ∈ bilinearRightSet M,
          ‖complexPositiveIntegerNatExtension β m‖ ^ 4) ≤
        complexPositiveFourthMoment β (2 * M) := by
    calc
      (∑ m ∈ bilinearRightSet M,
          ‖complexPositiveIntegerNatExtension β m‖ ^ 4) =
          ∑ m ∈ bilinearRightSet M,
            complexPositiveFourthMomentSummand β m := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmpos : 0 < m := by
          have := (mem_bilinearRightSet M m).mp hm |>.1
          omega
        simp [complexPositiveIntegerNatExtension,
          complexPositiveFourthMomentSummand, hmpos]
      _ ≤ complexPositiveFourthMoment β (2 * M) := by
        unfold complexPositiveFourthMoment
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro m hm hnot
        simp only [complexPositiveFourthMomentSummand]
        split <;> positivity
  rw [bilinearV_pow_four M hM]
  unfold bilinearV4
  calc
    M⁻¹ * ∑ m ∈ bilinearRightSet M,
        ‖complexPositiveIntegerNatExtension β m‖ ^ 4 ≤
        M⁻¹ * complexPositiveFourthMoment β (2 * M) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hM.le)
    _ ≤ M⁻¹ * (δ⁻¹ ^ 2 * (2 * M)) :=
      mul_le_mul_of_nonneg_left (hMoment (2 * M) h2M)
        (inv_nonneg.mpr hM.le)
    _ = 2 * δ⁻¹ ^ 2 := by field_simp

/-- The two normalized moment bounds imply the source product estimate
`UV≤2δ⁻¹`. -/
theorem bilinearUV_le_two_inv
    (δ L M : ℝ) (hδ : 0 < δ)
    (α β : ComplexPositiveIntegerFunction)
    (hU : bilinearU L (complexPositiveIntegerNatExtension α) ^ 2 ≤
      2 * δ⁻¹)
    (hV : bilinearV M (complexPositiveIntegerNatExtension β) ^ 4 ≤
      2 * δ⁻¹ ^ 2) :
    bilinearU L (complexPositiveIntegerNatExtension α) *
        bilinearV M (complexPositiveIntegerNatExtension β) ≤ 2 * δ⁻¹ := by
  let U := bilinearU L (complexPositiveIntegerNatExtension α)
  let V := bilinearV M (complexPositiveIntegerNatExtension β)
  have hU0 : 0 ≤ U := bilinearU_nonneg _ _
  have hV0 : 0 ≤ V := bilinearV_nonneg _ _
  have hinv0 : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hVsq : V ^ 2 ≤ 2 * δ⁻¹ := by
    apply (sq_le_sq₀ (sq_nonneg V) (mul_nonneg (by norm_num) hinv0)).mp
    calc
      (V ^ 2) ^ 2 = V ^ 4 := by ring
      _ ≤ 2 * δ⁻¹ ^ 2 := hV
      _ ≤ (2 * δ⁻¹) ^ 2 := by nlinarith [sq_nonneg δ⁻¹]
  apply (sq_le_sq₀ (mul_nonneg hU0 hV0)
    (mul_nonneg (by norm_num) hinv0)).mp
  calc
    (U * V) ^ 2 = U ^ 2 * V ^ 2 := by ring
    _ ≤ (2 * δ⁻¹) * (2 * δ⁻¹) :=
      mul_le_mul hU hVsq (sq_nonneg V)
        (mul_nonneg (by norm_num) hinv0)
    _ = (2 * δ⁻¹) ^ 2 := by ring

theorem bilinearU_pos_of_mem_ne_zero
    (L : ℝ) (hL : 0 < L) (α : ℕ → ℂ) (l : ℕ)
    (hl : l ∈ bilinearLeftSet L) (hα : α l ≠ 0) :
    0 < bilinearU L α := by
  have hterm : 0 < ‖α l‖ ^ 2 := by positivity
  have hsum : 0 < ∑ n ∈ bilinearLeftSet L, ‖α n‖ ^ 2 := by
    exact hterm.trans_le (Finset.single_le_sum
      (f := fun n => ‖α n‖ ^ 2) (fun n hn => by positivity) hl)
  unfold bilinearU bilinearU2
  exact Real.sqrt_pos.2 (mul_pos (inv_pos.mpr hL) hsum)

theorem bilinearV_pos_of_mem_ne_zero
    (M : ℝ) (hM : 0 < M) (β : ℕ → ℂ) (m : ℕ)
    (hm : m ∈ bilinearRightSet M) (hβ : β m ≠ 0) :
    0 < bilinearV M β := by
  have hterm : 0 < ‖β m‖ ^ 4 := by positivity
  have hsum : 0 < ∑ n ∈ bilinearRightSet M, ‖β n‖ ^ 4 := by
    exact hterm.trans_le (Finset.single_le_sum
      (f := fun n => ‖β n‖ ^ 4) (fun n hn => by positivity) hm)
  unfold bilinearV bilinearV4
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (mul_pos (inv_pos.mpr hM) hsum))

/-- Exact dyadic pigeonhole step in the ordinary Type-II reduction. -/
theorem exists_large_typeIIBlockCorrelation
    (N : ℕ) (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H δ Aminus Aplus : ℝ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X)
    (hδ : 0 < δ) (hδlog : δ < (Real.log X)⁻¹)
    (hN : N = Nat.floor (X + H))
    (hinterval : typeIIntervalSet X H ⊆ Finset.Icc 1 N)
    (hAplus : 0 ≤ Aplus) (hXA : 4 * Aplus < X)
    (hsupp : complexPositiveSupportedOnInterval α Aminus Aplus)
    (hcorr : δ * H ≤
      ‖typeIScalarPhaseSum (complexPositiveDirichletConvolution α β) P X H‖) :
    ∃ k ∈ typeIIActiveDyadicIndices N,
      δ ^ 2 * H / 4 ≤ ‖typeIIBlockCorrelation N k α β P X H‖ := by
  rw [typeIScalarPhaseSum_eq_active_typeIIBlockCorrelation_sum
    N α β P X H Aminus Aplus hinterval hAplus hXA hsupp] at hcorr
  exact exists_norm_ge_delta_sq_quarter_of_norm_sum_ge
    (typeIIActiveDyadicIndices N)
    (fun k => typeIIBlockCorrelation N k α β P X H)
    δ H hδ hH
    (by simpa [hN] using
      typeIIActiveDyadicIndices_card_bound X H δ hX hH.le hHX hδ hδlog)
    hcorr

/-- The ordinary Type-II inverse clause follows from the nondegenerate
bilinear coefficient task with the exact constants in the blueprint. -/
theorem typeIIInverseOfBilinear
    (d K₀ c₀ : ℕ)
    (hBIL : bilinearCoefficientTaskWithConstants d K₀ c₀) :
    typeIIInverseTaskClause d (2 * 8 ^ c₀ * K₀) (3 * c₀) := by
  rcases hBIL with ⟨hK₀, hc₀, hbilinear⟩
  intro X H P δ Aminus Aplus f hX hH hHX hP hδ hδsmall htype hcorr
  rcases htype with
    ⟨_hδtype, hδone, hAminus, hAplus, α, β, hf, hsupp, _hzero,
      hαmoment, _hβsecond, hβfourth⟩
  let S : ℝ := max Aplus ((X : ℝ) / Aminus)
  by_cases hexceptional :
      (H : ℝ) ≤
        arithmeticInverseBudget (2 * 8 ^ c₀ * K₀) (3 * c₀) δ * S
  · left
    simpa [S] using hexceptional
  right
  have hXr : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hHr : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHXr : (H : ℝ) ≤ (X : ℝ) := by exact_mod_cast hHX
  have hδhalf : δ < 1 / 2 := hδsmall.trans_le (min_le_left _ _)
  have hδlog : δ < (Real.log (X : ℝ))⁻¹ :=
    hδsmall.trans_le (min_le_right _ _)
  have hδle : δ ≤ 1 := by linarith
  have hδinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδle
  have hSnonneg : 0 ≤ S := by
    exact le_trans (by linarith : 0 ≤ Aplus) (le_max_left _ _)
  have hSgeAplus : Aplus ≤ S := le_max_left _ _
  have hconstantNat : 4 ≤ 2 * 8 ^ c₀ * K₀ := by
    have hpow : 1 ≤ 8 ^ c₀ := one_le_pow₀ (by norm_num)
    have hfirst : 4 ≤ 2 * 8 ^ c₀ * 2 := by nlinarith
    exact hfirst.trans (Nat.mul_le_mul_left (2 * 8 ^ c₀) hK₀)
  have hbudgetFour :
      4 ≤ arithmeticInverseBudget (2 * 8 ^ c₀ * K₀) (3 * c₀) δ := by
    unfold arithmeticInverseBudget
    have hconstantReal : (4 : ℝ) ≤ (2 * 8 ^ c₀ * K₀ : ℕ) := by
      exact_mod_cast hconstantNat
    calc
      (4 : ℝ) = 4 * 1 := by ring
      _ ≤ (2 * 8 ^ c₀ * K₀ : ℕ) * (δ⁻¹) ^ (3 * c₀) :=
        mul_le_mul hconstantReal (one_le_pow₀ hδinv)
          (by norm_num) (by positivity)
  have hnonexceptional :
      arithmeticInverseBudget (2 * 8 ^ c₀ * K₀) (3 * c₀) δ * S <
        (H : ℝ) := lt_of_not_ge hexceptional
  have hHfourS : 4 * S < (H : ℝ) := by
    have := mul_le_mul_of_nonneg_right hbudgetFour hSnonneg
    linarith
  have hXAplus : 4 * Aplus < (X : ℝ) := by
    have hfour : 4 * Aplus ≤ 4 * S := by linarith
    linarith
  let N : ℕ := Nat.floor ((X : ℝ) + (H : ℝ))
  have hN : N = Nat.floor ((X : ℝ) + (H : ℝ)) := rfl
  have hinterval :
      typeIIntervalSet (X : ℝ) (H : ℝ) ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [mem_typeIIntervalSet] at hn
    exact Finset.mem_Icc.mpr ⟨hn.1, by rw [hN]; exact Nat.le_floor hn.2.2⟩
  have hcorr' :
      δ * (H : ℝ) ≤
        ‖typeIScalarPhaseSum (complexPositiveDirichletConvolution α β) P
          (X : ℝ) (H : ℝ)‖ := by
    simpa [typeIScalarPhaseCorrelation, hf] using hcorr
  obtain ⟨k, hk, hblockLower⟩ :=
    exists_large_typeIIBlockCorrelation N α β P (X : ℝ) (H : ℝ)
      δ Aminus Aplus hXr (by linarith) hHXr hδ hδlog hN hinterval
      (by linarith) hXAplus hsupp hcorr'
  have hblockNormPos :
      0 < ‖typeIIBlockCorrelation N k α β P (X : ℝ) (H : ℝ)‖ := by
    exact lt_of_lt_of_le (by positivity) hblockLower
  have hblockNe :
      typeIIBlockCorrelation N k α β P (X : ℝ) (H : ℝ) ≠ 0 :=
    norm_pos_iff.mp hblockNormPos
  obtain ⟨m, hmBlock, l, hlN, hprod, hαne, hβne⟩ :=
    typeIIBlockCorrelation_nonzero_pair N k α β P (X : ℝ) (H : ℝ) hblockNe
  let M : ℝ := typeIDyadicScale k
  let L : ℝ := (X : ℝ) / M
  have hMtwo : 2 ≤ M := by
    simpa [M] using typeIIActiveDyadicScale_ge_two N k hk
  have hMpos : 0 < M := by linarith
  have hLpos : 0 < L := div_pos (by linarith) hMpos
  have hmRight : m ∈ bilinearRightSet M := by
    simpa [M] using typeIDyadicBlock_subset_bilinearRightSet N k hmBlock
  have hmpos : 0 < m := by
    have := (mem_bilinearRightSet M m).mp hmRight |>.1
    omega
  have hlProduct : l ∈ bilinearProductIntervalSet (X : ℝ) (H : ℝ) m := by
    rw [mem_bilinearProductIntervalSet (X : ℝ) (H : ℝ) m l hmpos]
    have hp := (mem_typeIIntervalSet (X : ℝ) (H : ℝ) (l * m)).mp hprod
    exact ⟨(Finset.mem_Icc.mp hlN).1, hp.2.1, hp.2.2⟩
  have hLM : (X : ℝ) = L * M := by
    dsimp [L]
    field_simp
  have hlLeft : l ∈ bilinearLeftSet L :=
    bilinearProductIntervalSet_subset_left (X : ℝ) (H : ℝ) L M
      hLpos hMpos hLM hHXr m l hmRight hlProduct
  have h2L : 1 ≤ 2 * L := by
    have hlone : (1 : ℝ) ≤ (l : ℝ) := by
      exact_mod_cast (mem_bilinearLeftSet L l).mp hlLeft |>.1
    have hlupper := (mem_bilinearLeftSet L l).mp hlLeft |>.2.2
    linarith
  have h2M : 1 ≤ 2 * M := by linarith
  have hUsq := bilinearU_sq_le_two_inv δ L hLpos h2L α hαmoment
  have hVfour :=
    bilinearV_pow_four_le_two_inv_sq δ M hMpos h2M β hβfourth
  have hUVbound := bilinearUV_le_two_inv δ L M hδ α β hUsq hVfour
  have hUpos : 0 < bilinearU L (complexPositiveIntegerNatExtension α) :=
    bilinearU_pos_of_mem_ne_zero L hLpos _ l hlLeft hαne
  have hVpos : 0 < bilinearV M (complexPositiveIntegerNatExtension β) :=
    bilinearV_pos_of_mem_ne_zero M hMpos _ m hmRight hβne
  have hUVpos : 0 <
      bilinearU L (complexPositiveIntegerNatExtension α) *
        bilinearV M (complexPositiveIntegerNatExtension β) :=
    mul_pos hUpos hVpos
  let ρ : ℝ := δ ^ 3 / 8
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hδcube : δ ^ 3 < (1 / 2 : ℝ) ^ 3 :=
    (pow_lt_pow_iff_left₀ hδ.le (by norm_num) (by norm_num)).2 hδhalf
  have hρhalf : ρ < 1 / 2 := by
    dsimp [ρ]
    nlinarith
  have hlarge :
      ρ * (H : ℝ) *
          (bilinearU L (complexPositiveIntegerNatExtension α) *
            bilinearV M (complexPositiveIntegerNatExtension β)) ≤
        ‖bilinearS (X : ℝ) (H : ℝ) M
          (complexPositiveIntegerNatExtension α)
          (complexPositiveIntegerNatExtension β) P‖ := by
    have hmul := mul_le_mul_of_nonneg_left hUVbound
      (mul_nonneg hρpos.le (by linarith : 0 ≤ (H : ℝ)))
    calc
      ρ * (H : ℝ) *
          (bilinearU L (complexPositiveIntegerNatExtension α) *
            bilinearV M (complexPositiveIntegerNatExtension β)) ≤
          ρ * (H : ℝ) * (2 * δ⁻¹) := hmul
      _ = δ ^ 2 * (H : ℝ) / 4 := by
        dsimp [ρ]
        field_simp
        ring
      _ ≤ ‖typeIIBlockCorrelation N k α β P (X : ℝ) (H : ℝ)‖ :=
        hblockLower
      _ = ‖bilinearS (X : ℝ) (H : ℝ) M
          (complexPositiveIntegerNatExtension α)
          (complexPositiveIntegerNatExtension β) P‖ := by
        rw [typeIIBlockCorrelation_eq_bilinearS N k (X : ℝ) (H : ℝ)
          hN α β P]
  have hlpos : 0 < l := by
    have := (Finset.mem_Icc.mp hlN).1
    omega
  have hαsub : α ⟨l, hlpos⟩ ≠ 0 := by
    simpa [complexPositiveIntegerNatExtension, hlpos] using hαne
  have hlsupp := hsupp ⟨l, hlpos⟩ hαsub
  have hmrange := (Finset.mem_filter.mp hmBlock).2
  have hproddata :=
    (mem_typeIIntervalSet (X : ℝ) (H : ℝ) (l * m)).mp hprod
  have hprodcast : (((l * m : ℕ) : ℝ)) = (l : ℝ) * (m : ℝ) := by
    norm_num
  have hLupper : L < 2 * Aplus := by
    apply (div_lt_iff₀ hMpos).2
    have hprodBound : (l : ℝ) * (m : ℝ) ≤ Aplus * (2 * M) :=
      mul_le_mul hlsupp.2 hmrange.2 (by positivity) (by linarith)
    rw [hprodcast] at hproddata
    nlinarith
  have hMupper : M < 2 * ((X : ℝ) / Aminus) := by
    have hAminusPos : 0 < Aminus := by linarith
    rw [show 2 * ((X : ℝ) / Aminus) = (2 * (X : ℝ)) / Aminus by ring]
    apply (lt_div_iff₀ hAminusPos).2
    have hlowerProd : Aminus * (m : ℝ) ≤ (l : ℝ) * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hlsupp.1 (by positivity)
    rw [hprodcast] at hproddata
    have hprodUpper : (l : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ) := by
      linarith
    have hMltm : M < (m : ℝ) := hmrange.1
    calc
      M * Aminus < (m : ℝ) * Aminus :=
        mul_lt_mul_of_pos_right hMltm hAminusPos
      _ = Aminus * (m : ℝ) := by ring
      _ ≤ (l : ℝ) * (m : ℝ) := hlowerProd
      _ ≤ 2 * (X : ℝ) := hprodUpper
  have hmaxLM : max L M ≤ 2 * S := by
    apply max_le
    · calc
        L ≤ 2 * Aplus := hLupper.le
        _ ≤ 2 * S := by gcongr
    · calc
        M ≤ 2 * ((X : ℝ) / Aminus) := hMupper.le
        _ ≤ 2 * S := by
          dsimp [S]
          gcongr
          exact le_max_right _ _
  have hρinv : ρ⁻¹ = 8 * δ⁻¹ ^ 3 := by
    dsimp [ρ]
    field_simp
  have hρpow : ρ⁻¹ ^ c₀ = (8 : ℝ) ^ c₀ * δ⁻¹ ^ (3 * c₀) := by
    rw [hρinv, mul_pow, pow_mul]
  have hlength :
      (K₀ : ℝ) * (ρ⁻¹) ^ c₀ * max ((X : ℝ) / M) M ≤ (H : ℝ) := by
    have hLe : max ((X : ℝ) / M) M ≤ 2 * S := by
      simpa [L] using hmaxLM
    calc
      (K₀ : ℝ) * (ρ⁻¹) ^ c₀ * max ((X : ℝ) / M) M ≤
          (K₀ : ℝ) * (ρ⁻¹) ^ c₀ * (2 * S) := by
        gcongr
      _ = arithmeticInverseBudget (2 * 8 ^ c₀ * K₀) (3 * c₀) δ * S := by
        rw [hρpow]
        unfold arithmeticInverseBudget
        push_cast
        ring
      _ ≤ (H : ℝ) := hnonexceptional.le
  let ν : ℕ → ℝ := fun i => (phaseCenteredAt P X).coeff i
  have hνtop : ν (d + 1) = 0 := by
    dsimp [ν]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (phaseCenteredAt_natDegree_le P hP X)
      (Nat.lt_succ_self d)
  have hphase : bilinearCenteredPhase (X : ℝ) d ν = P := by
    simpa [ν] using bilinearCenteredPhase_centeredCoefficients d X P hP
  have hlargeν :
      ρ * (H : ℝ) *
          (bilinearU ((X : ℝ) / M) (complexPositiveIntegerNatExtension α) *
            bilinearV M (complexPositiveIntegerNatExtension β)) ≤
        ‖bilinearS (X : ℝ) (H : ℝ) M
          (complexPositiveIntegerNatExtension α)
          (complexPositiveIntegerNatExtension β)
          (bilinearCenteredPhase (X : ℝ) d ν)‖ := by
    simpa [L, hphase] using hlarge
  obtain ⟨Q, hQone, hQbound, hQcoeff⟩ :=
    hbilinear X (H : ℝ) M ρ hXr hHr hHXr hMtwo hρpos hρhalf
      hlength (complexPositiveIntegerNatExtension α)
      (complexPositiveIntegerNatExtension β) ν hνtop
      (by simpa [L] using hUVpos) hlargeν
  have hsmallBudget :
      (K₀ : ℝ) * (ρ⁻¹) ^ c₀ ≤
        arithmeticInverseBudget (2 * 8 ^ c₀ * K₀) (3 * c₀) δ := by
    rw [hρpow]
    unfold arithmeticInverseBudget
    push_cast
    let B : ℝ := (K₀ : ℝ) * 8 ^ c₀ * δ⁻¹ ^ (3 * c₀)
    have hnonneg : 0 ≤ B := by dsimp [B]; positivity
    calc
      (K₀ : ℝ) * (8 ^ c₀ * δ⁻¹ ^ (3 * c₀)) = B := by
        dsimp [B]
        ring
      _ ≤ 2 * B := by linarith
      _ = 2 * 8 ^ c₀ * (K₀ : ℝ) * δ⁻¹ ^ (3 * c₀) := by
        dsimp [B]
        ring
  refine ⟨Q, hQone, hQbound.trans hsmallBudget, ?_⟩
  intro j hjone hjd
  have hcoeff := hQcoeff j hjone hjd
  dsimp [ν] at hcoeff ⊢
  exact hcoeff.trans (by
    have hHpow : 0 < (H : ℝ) ^ (j + 1) := by positivity
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsmallBudget (by linarith : 0 ≤ (X : ℝ)))
      hHpow.le)

#print axioms typeIIInverseOfBilinear

end


end FractionalPrimes.Literature.Uniformity

