module

public import FractionalPrimes.Literature.Polynomial.PolynomialPreliminaryTypeI2LargeMConclusion
public import FractionalPrimes.Literature.Polynomial.PolynomialDilationConcatenation
public import FractionalPrimes.Literature.Polynomial.PolynomialTypeI2SmallScale
public import FractionalPrimes.Literature.Polynomial.PolynomialWeightCutoff

/-!
# Scalar Type-I₂ inverse estimate

This file formalizes blueprint item `lpi:type-I2`.  The first checkpoint is
the exact finite expansion of the three Dirichlet factors; later declarations
will add the source's dyadic selection and many-dilate assembly.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open _root_.Polynomial
open scoped ENNReal

noncomputable section

/-- At a positive natural index, zero extension turns the convolution into
the exact finite divisor sum of the two zero-extended factors. -/
theorem complexPositiveIntegerNatExtension_convolution
    (α β : ComplexPositiveIntegerFunction) (n : ℕ) (hn : 0 < n) :
    complexPositiveIntegerNatExtension
        (complexPositiveDirichletConvolution α β) n =
      ∑ d ∈ n.divisors,
        complexPositiveIntegerNatExtension α d *
          complexPositiveIntegerNatExtension β (n / d) := by
  rw [complexPositiveIntegerNatExtension, dif_pos hn,
    complexPositiveDirichletConvolution_eq_divisor_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hquot : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)) hdpos
  simp [complexDivisorConvolutionSummand_of_mem _ _ _ _ hd,
    complexPositiveIntegerNatExtension, hdpos, hquot]

/-- Exact finite three-factor expansion, with the first coefficient factored
out.  The condition `a*m ∈ [1,N]` is the harmless intermediate support
condition produced by the two successive divisor reindexings. -/
theorem typeI2ScalarPhaseSum_eq_triple_factorized
    (α β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) :
    typeIScalarPhaseSum
        (complexPositiveDirichletConvolution
          (complexPositiveDirichletConvolution α β₁) β₂) P X H =
      ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ∑ m ∈ Finset.Icc 1 (Nat.floor (X + H)),
          if a * m ∈ Finset.Icc 1 (Nat.floor (X + H)) then
            complexPositiveIntegerNatExtension α a *
              complexPositiveIntegerNatExtension β₁ m *
                (∑ n ∈ Finset.Icc 1 (Nat.floor (X + H)),
                  if (a * m) * n ∈ typeIIntervalSet X H then
                    complexPositiveIntegerNatExtension β₂ n *
                      unitFrequencyPhase
                        (P.eval ((((a * m) * n : ℕ) : ℝ)))
                  else 0)
          else 0 := by
  classical
  let R : Finset ℕ := Finset.Icc 1 (Nat.floor (X + H))
  let W : ℕ → ℂ := fun c =>
    ∑ n ∈ R,
      if c * n ∈ typeIIntervalSet X H then
        complexPositiveIntegerNatExtension β₂ n *
          unitFrequencyPhase (P.eval (((c * n : ℕ) : ℝ)))
      else 0
  rw [typeIScalarPhaseSum_factorized]
  change (∑ c ∈ R,
      complexPositiveIntegerNatExtension
          (complexPositiveDirichletConvolution α β₁) c * W c) = _
  have hexpand :
      (∑ c ∈ R,
          complexPositiveIntegerNatExtension
              (complexPositiveDirichletConvolution α β₁) c * W c) =
        ∑ c ∈ R, ∑ d ∈ c.divisors,
          complexPositiveIntegerNatExtension α d *
            complexPositiveIntegerNatExtension β₁ (c / d) * W c := by
    apply Finset.sum_congr rfl
    intro c hc
    have hcpos : 0 < c := by
      have := (Finset.mem_Icc.mp (show c ∈ R from hc)).1
      omega
    rw [complexPositiveIntegerNatExtension_convolution α β₁ c hcpos,
      Finset.sum_mul]
  rw [hexpand]
  rw [finite_divisor_sum_reindex R (Nat.floor (X + H)) (by
    intro c hc
    exact hc)
    (complexPositiveIntegerNatExtension α)
    (complexPositiveIntegerNatExtension β₁) W]

/-- The individual fully expanded Type-I₂ summand.  Keeping this as a named
term lets the exact dyadic partition act independently in all three
coordinates. -/
def typeI2FactorizedTerm
    (α β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (a m n : ℕ) : ℂ :=
  if a * m ∈ Finset.Icc 1 (Nat.floor (X + H)) then
    complexPositiveIntegerNatExtension α a *
      complexPositiveIntegerNatExtension β₁ m *
        (if (a * m) * n ∈ typeIIntervalSet X H then
          complexPositiveIntegerNatExtension β₂ n *
            unitFrequencyPhase (P.eval ((((a * m) * n : ℕ) : ℝ)))
        else 0)
  else 0

/-- Fully distribute the exact three-factor expansion into a rectangular
finite triple sum. -/
theorem typeI2ScalarPhaseSum_eq_triple_sum
    (α β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) :
    typeIScalarPhaseSum
        (complexPositiveDirichletConvolution
          (complexPositiveDirichletConvolution α β₁) β₂) P X H =
      ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ∑ m ∈ Finset.Icc 1 (Nat.floor (X + H)),
          ∑ n ∈ Finset.Icc 1 (Nat.floor (X + H)),
            typeI2FactorizedTerm α β₁ β₂ P X H a m n := by
  rw [typeI2ScalarPhaseSum_eq_triple_factorized]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ham : a * m ∈ Finset.Icc 1 (Nat.floor (X + H))
  · simp only [ham, if_true, typeI2FactorizedTerm]
    rw [Finset.mul_sum]
  · simp [typeI2FactorizedTerm, ham]

/-- If the outer Type-I₂ coefficient is supported below `A_I2<X`, every
fully expanded outer summand beyond `⌊X⌋` vanishes exactly. -/
theorem typeI2_triple_sum_eq_floorX
    (α β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H A_I2 : ℝ) (hH : 0 ≤ H) (hAI : A_I2 < X)
    (hsupp : complexPositiveSupportedOnInterval α 1 A_I2) :
    (∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ∑ m ∈ Finset.Icc 1 (Nat.floor (X + H)),
          ∑ n ∈ Finset.Icc 1 (Nat.floor (X + H)),
            typeI2FactorizedTerm α β₁ β₂ P X H a m n) =
      ∑ a ∈ Finset.Icc 1 (Nat.floor X),
        ∑ m ∈ Finset.Icc 1 (Nat.floor (X + H)),
          ∑ n ∈ Finset.Icc 1 (Nat.floor (X + H)),
            typeI2FactorizedTerm α β₁ β₂ P X H a m n := by
  have hcut : Nat.floor X ≤ Nat.floor (X + H) :=
    Nat.floor_mono (by linarith)
  have hsub : Finset.Icc 1 (Nat.floor X) ⊆
      Finset.Icc 1 (Nat.floor (X + H)) := by
    intro a ha
    rcases Finset.mem_Icc.mp ha with ⟨haone, haX⟩
    exact Finset.mem_Icc.mpr ⟨haone, haX.trans hcut⟩
  symm
  apply Finset.sum_subset hsub
  intro a haBig haNotSmall
  have haOne : 1 ≤ a := (Finset.mem_Icc.mp haBig).1
  have haAbove : Nat.floor X < a := by
    by_contra h
    exact haNotSmall (Finset.mem_Icc.mpr ⟨haOne, le_of_not_gt h⟩)
  have hfloor : X < (Nat.floor X : ℝ) + 1 := Nat.lt_floor_add_one X
  have haCast : (Nat.floor X : ℝ) + 1 ≤ (a : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr haAbove)
  have hXltA : X < (a : ℝ) := lt_of_lt_of_le hfloor haCast
  have haPos : 0 < a := by omega
  have hαzero : complexPositiveIntegerNatExtension α a = 0 := by
    by_contra hne
    have hαval : α ⟨a, haPos⟩ ≠ 0 := by
      simpa [complexPositiveIntegerNatExtension, haPos] using hne
    have hαupper := (hsupp ⟨a, haPos⟩ hαval).2
    linarith
  simp [typeI2FactorizedTerm, hαzero]

/-- The inner double sum on selected finite `m`- and `n`-blocks, with the
intermediate support condition retained exactly as it arises from the two
successive divisor reindexings. -/
def typeI2SelectedInner
    (β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (SM SN : Finset ℕ) (a : ℕ) : ℂ :=
  ∑ m ∈ SM,
    if a * m ∈ Finset.Icc 1 (Nat.floor (X + H)) then
      complexPositiveIntegerNatExtension β₁ m *
        (∑ n ∈ SN,
          if (a * m) * n ∈ typeIIntervalSet X H then
            complexPositiveIntegerNatExtension β₂ n *
              unitFrequencyPhase (P.eval ((((a * m) * n : ℕ) : ℝ)))
          else 0)
    else 0

/-- On any three selected finite blocks, the exact expanded Type-I₂ sum is
the outer coefficient paired with the selected inner double sum. -/
theorem typeI2_selected_block_eq_weighted_inner
    (α β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (SA SM SN : Finset ℕ) :
    (∑ a ∈ SA, ∑ m ∈ SM, ∑ n ∈ SN,
        typeI2FactorizedTerm α β₁ β₂ P X H a m n) =
      ∑ a ∈ SA, complexPositiveIntegerNatExtension α a *
        typeI2SelectedInner β₁ β₂ P X H SM SN a := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  rw [typeI2SelectedInner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ham : a * m ∈ Finset.Icc 1 (Nat.floor (X + H))
  · simp only [typeI2FactorizedTerm, ham, if_true]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · simp [typeI2FactorizedTerm, ham]

/-- Every source dyadic scale is strictly positive, including the exceptional
initial half-scale. -/
theorem typeIDyadicScale_pos (k : ℕ) : 0 < typeIDyadicScale k := by
  unfold typeIDyadicScale
  split <;> positivity

/-- A selected Type-I₂ dyadic block with nonzero contribution has scale
product strictly below `2X`. This is the exact support-geometric assertion
used before orienting the two inner coordinates. -/
theorem typeI2_nonzero_selected_block_scales_mul_lt
    (α β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (N₁ N₂ N₃ k₁ k₂ k₃ : ℕ) (hHX : H ≤ X)
    (hblock :
      (∑ a ∈ typeIDyadicBlock N₁ k₁,
        ∑ m ∈ typeIDyadicBlock N₂ k₂,
          ∑ n ∈ typeIDyadicBlock N₃ k₃,
            typeI2FactorizedTerm α β₁ β₂ P X H a m n) ≠ 0) :
    typeIDyadicScale k₁ * typeIDyadicScale k₂ * typeIDyadicScale k₃ <
      2 * X := by
  classical
  obtain ⟨a, ha, haSum⟩ := Finset.exists_ne_zero_of_sum_ne_zero hblock
  obtain ⟨m, hm, hmSum⟩ := Finset.exists_ne_zero_of_sum_ne_zero haSum
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmSum
  have ham : a * m ∈ Finset.Icc 1 (Nat.floor (X + H)) := by
    by_contra ham
    simp [typeI2FactorizedTerm, ham] at hterm
  have hamn : (a * m) * n ∈ typeIIntervalSet X H := by
    by_contra hamn
    simp [typeI2FactorizedTerm, ham, hamn] at hterm
  have haLower : typeIDyadicScale k₁ < (a : ℝ) :=
    (Finset.mem_filter.mp ha).2.1
  have hmLower : typeIDyadicScale k₂ < (m : ℝ) :=
    (Finset.mem_filter.mp hm).2.1
  have hnLower : typeIDyadicScale k₃ < (n : ℝ) :=
    (Finset.mem_filter.mp hn).2.1
  have haPos : 0 < (a : ℝ) :=
    lt_trans (typeIDyadicScale_pos k₁) haLower
  have hmPos : 0 < (m : ℝ) :=
    lt_trans (typeIDyadicScale_pos k₂) hmLower
  have hAM : typeIDyadicScale k₁ * typeIDyadicScale k₂ <
      (a : ℝ) * (m : ℝ) := by
    calc
      typeIDyadicScale k₁ * typeIDyadicScale k₂ <
          (a : ℝ) * typeIDyadicScale k₂ :=
        mul_lt_mul_of_pos_right haLower (typeIDyadicScale_pos k₂)
      _ < (a : ℝ) * (m : ℝ) := mul_lt_mul_of_pos_left hmLower haPos
  have hAMN : typeIDyadicScale k₁ * typeIDyadicScale k₂ *
      typeIDyadicScale k₃ < (a : ℝ) * (m : ℝ) * (n : ℝ) := by
    calc
      typeIDyadicScale k₁ * typeIDyadicScale k₂ * typeIDyadicScale k₃ <
          ((a : ℝ) * (m : ℝ)) * typeIDyadicScale k₃ :=
        mul_lt_mul_of_pos_right hAM (typeIDyadicScale_pos k₃)
      _ < ((a : ℝ) * (m : ℝ)) * (n : ℝ) :=
        mul_lt_mul_of_pos_left hnLower (mul_pos haPos hmPos)
  have hupper : (((a * m) * n : ℕ) : ℝ) ≤ X + H :=
    ((mem_typeIIntervalSet X H ((a * m) * n)).1 hamn).2.2
  calc
    typeIDyadicScale k₁ * typeIDyadicScale k₂ * typeIDyadicScale k₃ <
        (a : ℝ) * (m : ℝ) * (n : ℝ) := hAMN
    _ = (((a * m) * n : ℕ) : ℝ) := by norm_num
    _ ≤ X + H := hupper
    _ ≤ 2 * X := by linarith

/-- After orienting the two inner dyadic scales so that `M ≤ N`, the source
product bound implies the precise pointwise restriction
`M ≤ 2 * sqrt (X / a)` on every outer block point `a ≤ 2A`. -/
theorem typeI2_oriented_inner_scale_le
    (A M N X a : ℝ) (hAhalf : 1 / 2 ≤ A) (hMpos : 0 < M)
    (hMN : M ≤ N) (hprod : A * M * N < 2 * X)
    (hapos : 0 < a) (haUpper : a ≤ 2 * A) :
    M ≤ 2 * √(X / a) := by
  have hApos : 0 < A := by linarith
  have hNpos : 0 < N := lt_of_lt_of_le hMpos hMN
  have hXpos : 0 < X := by
    have hleft : 0 < A * M * N := mul_pos (mul_pos hApos hMpos) hNpos
    linarith
  have hAMM : A * M * M ≤ A * M * N :=
    mul_le_mul_of_nonneg_left hMN (mul_nonneg hApos.le hMpos.le)
  have hMdiv : M ^ 2 ≤ 2 * X / A := by
    apply le_of_lt
    apply (lt_div_iff₀ hApos).2
    nlinarith
  have hfirst : M ≤ √(2 * X / A) :=
    (Real.le_sqrt hMpos.le (by positivity)).2 hMdiv
  have hcross : (2 * X) * a ≤ (4 * X) * A := by
    have hmul := mul_le_mul_of_nonneg_left haUpper
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hXpos.le)
    nlinarith
  have hratio : 2 * X / A ≤ 4 * (X / a) := by
    rw [show 4 * (X / a) = (4 * X) / a by ring]
    exact (div_le_div_iff₀ hApos hapos).2 hcross
  have hXa : 0 ≤ X / a := (div_pos hXpos hapos).le
  have hsquare : 4 * (X / a) = (2 * √(X / a)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hXa]
    ring
  have hsecond : √(2 * X / A) ≤ 2 * √(X / a) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · rw [← hsquare]
      exact hratio
  exact hfirst.trans hsecond

/-- If a positive product lies in the Type-I interval, then its left factor
lies in the finite ambient range used by the successive divisor expansion. -/
theorem typeI2_left_factor_mem_ambient_of_product_mem
    (X H : ℝ) (a m n : ℕ)
    (hamn : (a * m) * n ∈ typeIIntervalSet X H) :
    a * m ∈ Finset.Icc 1 (Nat.floor (X + H)) := by
  have hprops := (mem_typeIIntervalSet X H ((a * m) * n)).1 hamn
  have hprodPos : 0 < (a * m) * n := by omega
  have hamPos : 0 < a * m := by
    exact pos_of_mul_pos_left hprodPos (Nat.zero_le n)
  have hnPos : 0 < n :=
    pos_of_mul_pos_right hprodPos (Nat.zero_le (a * m))
  have hfactorNat : a * m ≤ (a * m) * n :=
    Nat.le_mul_of_pos_right (a * m) hnPos
  have hfactorReal : ((a * m : ℕ) : ℝ) ≤ X + H := by
    calc
      ((a * m : ℕ) : ℝ) ≤ (((a * m) * n : ℕ) : ℝ) := by
        exact_mod_cast hfactorNat
      _ ≤ X + H := hprops.2.2
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr hamPos.ne', Nat.le_floor hfactorReal⟩

/-- The selected inner sum in its symmetric, fully distributed form. The
intermediate divisor-expansion guard is absent because interval membership of
the full product forces it automatically. -/
def typeI2SymmetricInner
    (β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (SM SN : Finset ℕ) (a : ℕ) : ℂ :=
  ∑ m ∈ SM, ∑ n ∈ SN,
    if (a * m) * n ∈ typeIIntervalSet X H then
      complexPositiveIntegerNatExtension β₁ m *
        complexPositiveIntegerNatExtension β₂ n *
          unitFrequencyPhase (P.eval ((((a * m) * n : ℕ) : ℝ)))
    else 0

/-- The guarded inner sum from the exact divisor expansion equals its
symmetric full-product form on arbitrary finite blocks. -/
theorem typeI2SelectedInner_eq_symmetric
    (β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (SM SN : Finset ℕ) (a : ℕ) :
    typeI2SelectedInner β₁ β₂ P X H SM SN a =
      typeI2SymmetricInner β₁ β₂ P X H SM SN a := by
  classical
  unfold typeI2SelectedInner typeI2SymmetricInner
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ham : a * m ∈ Finset.Icc 1 (Nat.floor (X + H))
  · simp only [ham, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hamn : (a * m) * n ∈ typeIIntervalSet X H
    · simp [hamn, mul_assoc]
    · simp [hamn]
  · simp only [ham, if_false]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hamn : (a * m) * n ∉ typeIIntervalSet X H := by
      intro hmem
      exact ham (typeI2_left_factor_mem_ambient_of_product_mem X H a m n hmem)
    simp [hamn]

/-- The symmetric inner sum is invariant under swapping the two inner blocks
and their two weights. -/
theorem typeI2SymmetricInner_swap
    (β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (SM SN : Finset ℕ) (a : ℕ) :
    typeI2SymmetricInner β₁ β₂ P X H SM SN a =
      typeI2SymmetricInner β₂ β₁ P X H SN SM a := by
  classical
  unfold typeI2SymmetricInner
  calc
    (∑ m ∈ SM, ∑ n ∈ SN,
        if (a * m) * n ∈ typeIIntervalSet X H then
          complexPositiveIntegerNatExtension β₁ m *
            complexPositiveIntegerNatExtension β₂ n *
              unitFrequencyPhase (P.eval ((((a * m) * n : ℕ) : ℝ)))
        else 0) =
      ∑ n ∈ SN, ∑ m ∈ SM,
        if (a * m) * n ∈ typeIIntervalSet X H then
          complexPositiveIntegerNatExtension β₁ m *
            complexPositiveIntegerNatExtension β₂ n *
              unitFrequencyPhase (P.eval ((((a * m) * n : ℕ) : ℝ)))
        else 0 := by rw [Finset.sum_comm]
    _ = ∑ n ∈ SN, ∑ m ∈ SM,
        if (a * n) * m ∈ typeIIntervalSet X H then
          complexPositiveIntegerNatExtension β₂ n *
            complexPositiveIntegerNatExtension β₁ m *
              unitFrequencyPhase (P.eval ((((a * n) * m : ℕ) : ℝ)))
        else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      have hprod : (a * n) * m = (a * m) * n := by ac_rfl
      rw [hprod]
      by_cases hmem : (a * m) * n ∈ typeIIntervalSet X H
      · simp only [hmem, if_true]
        ring
      · simp [hmem]

/-- On an index lying in the interval, natural zero extension commutes with
restricting a positive-integer weight. -/
theorem complexPositiveIntegerNatExtension_intervalWeightRestriction_of_mem
    (J : Set ℝ) (β : ComplexPositiveIntegerFunction) (n : ℕ)
    (hnJ : (n : ℝ) ∈ J) :
    complexPositiveIntegerNatExtension (intervalWeightRestriction J β) n =
      complexPositiveIntegerNatExtension β n := by
  classical
  by_cases hn : 0 < n
  · simp [complexPositiveIntegerNatExtension, intervalWeightRestriction,
      hn, hnJ]
  · have hnzero : n = 0 := by omega
    subst n
    simp [complexPositiveIntegerNatExtension]

/-- Off the restricting interval, the naturally extended restricted weight
vanishes. -/
theorem complexPositiveIntegerNatExtension_intervalWeightRestriction_of_not_mem
    (J : Set ℝ) (β : ComplexPositiveIntegerFunction) (n : ℕ)
    (hnJ : (n : ℝ) ∉ J) :
    complexPositiveIntegerNatExtension (intervalWeightRestriction J β) n = 0 := by
  classical
  by_cases hn : 0 < n
  · simp [complexPositiveIntegerNatExtension, intervalWeightRestriction,
      hn, hnJ]
  · have hnzero : n = 0 := by omega
    subst n
    simp [complexPositiveIntegerNatExtension]

/-- Dividing the interval by a positive integer dilation is exactly
equivalent to multiplying the natural product by that dilation. -/
theorem typeI2_mem_scaled_interval_iff
    (X H : ℝ) (a m n : ℕ) (ha : 0 < a) :
    m * n ∈ typeIIntervalSet (X / (a : ℝ)) (H / (a : ℝ)) ↔
      (a * m) * n ∈ typeIIntervalSet X H := by
  have haReal : 0 < (a : ℝ) := by exact_mod_cast ha
  have hcast : (((a * m) * n : ℕ) : ℝ) =
      (a : ℝ) * ((m * n : ℕ) : ℝ) := by
    push_cast
    ring
  constructor
  · intro hscaled
    rcases (mem_typeIIntervalSet _ _ (m * n)).1 hscaled with
      ⟨hmnOne, hlow, hupp⟩
    apply (mem_typeIIntervalSet X H ((a * m) * n)).2
    refine ⟨?_, ?_, ?_⟩
    · have hmnPos : 0 < m * n := by omega
      have hprodPos : 0 < a * (m * n) := Nat.mul_pos ha hmnPos
      simpa [mul_assoc] using Nat.succ_le_iff.mpr hprodPos
    · rw [hcast]
      have h := (div_lt_iff₀ haReal).1 hlow
      simpa [mul_comm] using h
    · rw [hcast]
      have hsum : ((m * n : ℕ) : ℝ) ≤ (X + H) / (a : ℝ) := by
        simpa [add_div] using hupp
      have h := (le_div_iff₀ haReal).1 hsum
      simpa [mul_comm] using h
  · intro horiginal
    rcases (mem_typeIIntervalSet X H ((a * m) * n)).1 horiginal with
      ⟨hprodOne, hlow, hupp⟩
    apply (mem_typeIIntervalSet _ _ (m * n)).2
    have hprodPos : 0 < a * (m * n) := by
      have : 0 < (a * m) * n := by omega
      simpa [mul_assoc] using this
    have hmnPos : 0 < m * n :=
      pos_of_mul_pos_right hprodPos (Nat.zero_le a)
    refine ⟨Nat.succ_le_iff.mpr hmnPos, ?_, ?_⟩
    · apply (div_lt_iff₀ haReal).2
      have h : X < (a : ℝ) * ((m * n : ℕ) : ℝ) := by
        simpa [hcast] using hlow
      simpa [mul_comm] using h
    · rw [show X / (a : ℝ) + H / (a : ℝ) =
          (X + H) / (a : ℝ) by ring]
      apply (le_div_iff₀ haReal).2
      have h : (a : ℝ) * ((m * n : ℕ) : ℝ) ≤ X + H := by
        simpa [hcast] using hupp
      simpa [mul_comm] using h

/-- The interval after positive dilation is contained in the original finite
ambient cutoff when `X,H` are nonnegative. -/
theorem typeI2_scaled_interval_subset_ambient
    (X H : ℝ) (a : ℕ) (ha : 0 < a) (hX : 0 ≤ X) (hH : 0 ≤ H) :
    typeIIntervalSet (X / (a : ℝ)) (H / (a : ℝ)) ⊆
      Finset.Icc 1 (Nat.floor (X + H)) := by
  intro n hn
  have hprops := (mem_typeIIntervalSet _ _ n).1 hn
  have haOne : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hdiv : (X + H) / (a : ℝ) ≤ X + H :=
    div_le_self (add_nonneg hX hH) haOne
  have hnUpper : (n : ℝ) ≤ X + H := by
    calc
      (n : ℝ) ≤ X / (a : ℝ) + H / (a : ℝ) := hprops.2.2
      _ = (X + H) / (a : ℝ) := by ring
      _ ≤ X + H := hdiv
  exact Finset.mem_Icc.mpr ⟨hprops.1, Nat.le_floor hnUpper⟩

/-- The polynomial phase after fixing the positive outer Type-I₂ factor. -/
noncomputable def typeI2DilatedPolynomial
    (P : Polynomial ℝ) (a : ℕ) : Polynomial ℝ :=
  P.comp (Polynomial.C (a : ℝ) * Polynomial.X)

@[simp]
theorem typeI2DilatedPolynomial_eval
    (P : Polynomial ℝ) (a : ℕ) (x : ℝ) :
    (typeI2DilatedPolynomial P a).eval x = P.eval ((a : ℝ) * x) := by
  rw [typeI2DilatedPolynomial, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- Dilation by a scalar linear polynomial does not increase the degree of
the Type-I₂ phase. -/
theorem typeI2DilatedPolynomial_degree
    (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (a : ℕ) :
    (typeI2DilatedPolynomial P a).natDegree ≤ d := by
  have hlinear :
      (Polynomial.C (a : ℝ) * Polynomial.X).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  calc
    (typeI2DilatedPolynomial P a).natDegree ≤
        P.natDegree *
          (Polynomial.C (a : ℝ) * Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ d * 1 := Nat.mul_le_mul hP hlinear
    _ = d := by simp

/-- Centering the dilated Type-I₂ phase at `q` gives exactly the phase
coordinate used by the many-dilate concatenation theorem. -/
theorem typeI2DilatedPolynomial_centered
    (P : Polynomial ℝ) (a : ℕ) (q : ℤ) :
    (typeI2DilatedPolynomial P a).comp
        (Polynomial.X + Polynomial.C (q : ℝ)) =
      phaseDilatedAt P a q := by
  have hlinear :
      (Polynomial.C (a : ℝ) * Polynomial.X).comp
          (Polynomial.X + Polynomial.C (q : ℝ)) =
        Polynomial.C ((a : ℝ) * (q : ℝ)) +
          Polynomial.C (a : ℝ) * Polynomial.X := by
    simp only [Polynomial.comp, Polynomial.eval₂_mul,
      Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_X]
    calc
      Polynomial.C (a : ℝ) * (Polynomial.X + Polynomial.C (q : ℝ)) =
          Polynomial.C (a : ℝ) * Polynomial.X +
            Polynomial.C (a : ℝ) * Polynomial.C (q : ℝ) := by rw [mul_add]
      _ = Polynomial.C ((a : ℝ) * (q : ℝ)) +
          Polynomial.C (a : ℝ) * Polynomial.X := by
        rw [Polynomial.C_mul]
        ac_rfl
  rw [typeI2DilatedPolynomial, Polynomial.comp_assoc, hlinear]
  rfl

/-- The same centering identity in the canonical `phaseCenteredAt` normal
form used by the preliminary Type-I₂ inverse theorem. -/
theorem typeI2DilatedPolynomial_phaseCenteredAt
    (P : Polynomial ℝ) (a : ℕ) (q : ℤ) :
    phaseCenteredAt (typeI2DilatedPolynomial P a) q =
      phaseDilatedAt P a q := by
  simpa [phaseCenteredAt, add_comm] using
    typeI2DilatedPolynomial_centered P a q

/-- The symmetric selected inner block is exactly the scalar Type-I phase sum
of the two interval-restricted weights after dividing the interval and
dilating the polynomial by the fixed outer factor. -/
theorem typeI2SymmetricInner_eq_dilated_phase_sum
    (β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (a kM kN : ℕ) (ha : 0 < a) (hX : 0 ≤ X) (hH : 0 ≤ H) :
    typeI2SymmetricInner β₁ β₂ P X H
        (typeIDyadicBlock (Nat.floor (X + H)) kM)
        (typeIDyadicBlock (Nat.floor (X + H)) kN) a =
      typeIScalarPhaseSum
        (complexPositiveDirichletConvolution
          (intervalWeightRestriction
            (Set.Ioc (typeIDyadicScale kM) (2 * typeIDyadicScale kM)) β₁)
          (intervalWeightRestriction
            (Set.Ioc (typeIDyadicScale kN) (2 * typeIDyadicScale kN)) β₂))
        (typeI2DilatedPolynomial P a) (X / (a : ℝ)) (H / (a : ℝ)) := by
  classical
  let R := Finset.Icc 1 (Nat.floor (X + H))
  let SM := typeIDyadicBlock (Nat.floor (X + H)) kM
  let SN := typeIDyadicBlock (Nat.floor (X + H)) kN
  let JM : Set ℝ := Set.Ioc (typeIDyadicScale kM) (2 * typeIDyadicScale kM)
  let JN : Set ℝ := Set.Ioc (typeIDyadicScale kN) (2 * typeIDyadicScale kN)
  have hinterval : typeIIntervalSet (X / (a : ℝ)) (H / (a : ℝ)) ⊆ R := by
    simpa [R] using typeI2_scaled_interval_subset_ambient X H a ha hX hH
  have hSMsub : SM ⊆ R := by
    intro m hm
    exact (Finset.mem_filter.mp (show m ∈
      typeIDyadicBlock (Nat.floor (X + H)) kM from hm)).1
  have hSNsub : SN ⊆ R := by
    intro n hn
    exact (Finset.mem_filter.mp (show n ∈
      typeIDyadicBlock (Nat.floor (X + H)) kN from hn)).1
  rw [typeIScalarPhaseSum_eq_factor_pair_sum _ _ _ _ _ _ hinterval]
  change typeI2SymmetricInner β₁ β₂ P X H SM SN a = _
  symm
  calc
    (∑ m ∈ R, ∑ n ∈ R,
        if m * n ∈ typeIIntervalSet (X / (a : ℝ)) (H / (a : ℝ)) then
          complexPositiveIntegerNatExtension
              (intervalWeightRestriction JM β₁) m *
            complexPositiveIntegerNatExtension
              (intervalWeightRestriction JN β₂) n *
            unitFrequencyPhase
              ((typeI2DilatedPolynomial P a).eval ((m * n : ℕ) : ℝ))
        else 0) =
      ∑ m ∈ SM, ∑ n ∈ R,
        if m * n ∈ typeIIntervalSet (X / (a : ℝ)) (H / (a : ℝ)) then
          complexPositiveIntegerNatExtension
              (intervalWeightRestriction JM β₁) m *
            complexPositiveIntegerNatExtension
              (intervalWeightRestriction JN β₂) n *
            unitFrequencyPhase
              ((typeI2DilatedPolynomial P a).eval ((m * n : ℕ) : ℝ))
        else 0 := by
      symm
      apply Finset.sum_subset hSMsub
      intro m hmR hmSM
      have hmJM : (m : ℝ) ∉ JM := by
        intro hmJM
        apply hmSM
        apply Finset.mem_filter.mpr
        exact ⟨hmR, by simpa [JM] using hmJM⟩
      rw [complexPositiveIntegerNatExtension_intervalWeightRestriction_of_not_mem
        JM β₁ m hmJM]
      simp
    _ = ∑ m ∈ SM, ∑ n ∈ SN,
        if m * n ∈ typeIIntervalSet (X / (a : ℝ)) (H / (a : ℝ)) then
          complexPositiveIntegerNatExtension
              (intervalWeightRestriction JM β₁) m *
            complexPositiveIntegerNatExtension
              (intervalWeightRestriction JN β₂) n *
            unitFrequencyPhase
              ((typeI2DilatedPolynomial P a).eval ((m * n : ℕ) : ℝ))
        else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      symm
      apply Finset.sum_subset hSNsub
      intro n hnR hnSN
      have hnJN : (n : ℝ) ∉ JN := by
        intro hnJN
        apply hnSN
        apply Finset.mem_filter.mpr
        exact ⟨hnR, by simpa [JN] using hnJN⟩
      rw [complexPositiveIntegerNatExtension_intervalWeightRestriction_of_not_mem
        JN β₂ n hnJN]
      simp
    _ = typeI2SymmetricInner β₁ β₂ P X H SM SN a := by
      unfold typeI2SymmetricInner
      apply Finset.sum_congr rfl
      intro m hm
      have hmJM : (m : ℝ) ∈ JM := by
        have hmBlock := (Finset.mem_filter.mp (show m ∈
          typeIDyadicBlock (Nat.floor (X + H)) kM from hm)).2
        simpa [JM] using hmBlock
      apply Finset.sum_congr rfl
      intro n hn
      have hnJN : (n : ℝ) ∈ JN := by
        have hnBlock := (Finset.mem_filter.mp (show n ∈
          typeIDyadicBlock (Nat.floor (X + H)) kN from hn)).2
        simpa [JN] using hnBlock
      rw [complexPositiveIntegerNatExtension_intervalWeightRestriction_of_mem
        JM β₁ m hmJM,
        complexPositiveIntegerNatExtension_intervalWeightRestriction_of_mem
          JN β₂ n hnJN]
      by_cases hscaled :
          m * n ∈ typeIIntervalSet (X / (a : ℝ)) (H / (a : ℝ))
      · have horiginal :=
          (typeI2_mem_scaled_interval_iff X H a m n ha).1 hscaled
        simp only [hscaled, horiginal, if_true, typeI2DilatedPolynomial_eval]
        congr 3
        push_cast
        ring
      · have horiginal : (a * m) * n ∉ typeIIntervalSet X H := by
          intro horiginal
          exact hscaled ((typeI2_mem_scaled_interval_iff X H a m n ha).2 horiginal)
        simp [hscaled, horiginal]

/-- Every source dyadic scale is at least the exceptional initial scale
`1/2`. -/
theorem one_half_le_typeIDyadicScale (k : ℕ) :
    (1 / 2 : ℝ) ≤ typeIDyadicScale k := by
  unfold typeIDyadicScale
  split
  · rfl
  · have hpow : (1 : ℕ) ≤ 2 ^ (k - 1) := one_le_pow₀ (by omega)
    have hpowReal : (1 : ℝ) ≤ ((2 ^ (k - 1) : ℕ) : ℝ) := by
      exact_mod_cast hpow
    linarith

/-- A hyperbola strip whose first coordinate lies in `(M,2M]`, with
`M ≥ 1/2`, has only finitely many integer lattice points under the positive
short-interval hypotheses used in the Type-I₂ reduction. -/
theorem hyperbolaLatticeSet_finite_of_interval
    (X H M : ℝ) (J : Set ℝ) (hX : 0 < X) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hMhalf : (1 / 2 : ℝ) ≤ M) (hJ : J ⊆ Set.Ioc M (2 * M)) :
    (Hyperbola.hyperbolaLatticeSet X H J).Finite := by
  let B : Set (ℤ × ℤ) :=
    Set.Icc (1 : ℤ) ⌊2 * M⌋ ×ˢ Set.Icc (1 : ℤ) ⌊X + H⌋
  have hsubset : Hyperbola.hyperbolaLatticeSet X H J ⊆ B := by
    intro p hp
    rcases hp with ⟨hpJ, hprodLow, hprodHigh⟩
    have hpJ' := hJ hpJ
    have hhalfPos : (0 : ℝ) < 1 / 2 := by norm_num
    have hMpos : 0 < M := lt_of_lt_of_le hhalfPos hMhalf
    have hp1Real : 0 < (p.1 : ℝ) := lt_trans hMpos hpJ'.1
    have hprodPos : 0 < (p.1 : ℝ) * (p.2 : ℝ) :=
      lt_trans hX hprodLow
    have hp2Real : 0 < (p.2 : ℝ) :=
      (mul_pos_iff_of_pos_left hp1Real).1 hprodPos
    have hp1 : (1 : ℤ) ≤ p.1 := by
      have : (0 : ℤ) < p.1 := by exact_mod_cast hp1Real
      omega
    have hp2 : (1 : ℤ) ≤ p.2 := by
      have : (0 : ℤ) < p.2 := by exact_mod_cast hp2Real
      omega
    have hp1Upper : p.1 ≤ ⌊2 * M⌋ :=
      Int.le_floor.mpr (by exact_mod_cast hpJ'.2)
    have hp1OneReal : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hp1
    have hp2Prod : (p.2 : ℝ) ≤ (p.1 : ℝ) * (p.2 : ℝ) :=
      le_mul_of_one_le_left hp2Real.le hp1OneReal
    have hp2UpperReal : (p.2 : ℝ) ≤ X + H :=
      hp2Prod.trans hprodHigh
    have hp2Upper : p.2 ≤ ⌊X + H⌋ :=
      Int.le_floor.mpr (by exact_mod_cast hp2UpperReal)
    change p ∈ Set.Icc (1 : ℤ) ⌊2 * M⌋ ×ˢ
      Set.Icc (1 : ℤ) ⌊X + H⌋
    exact ⟨⟨hp1, hp1Upper⟩, ⟨hp2, hp2Upper⟩⟩
  have hBfinite : B.Finite := by
    dsimp [B]
    exact (Set.finite_Icc (1 : ℤ) ⌊2 * M⌋).prod
      (Set.finite_Icc (1 : ℤ) ⌊X + H⌋)
  exact hBfinite.subset hsubset

/-- Under the same interval hypotheses, the integer hyperbola lattice has an
exact finite representative. -/
theorem exists_hyperbolaLatticeFinset_of_interval
    (X H M : ℝ) (J : Set ℝ) (hX : 0 < X) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hMhalf : (1 / 2 : ℝ) ≤ M) (hJ : J ⊆ Set.Ioc M (2 * M)) :
    ∃ Λ : Finset (ℤ × ℤ),
      (Λ : Set (ℤ × ℤ)) = Hyperbola.hyperbolaLatticeSet X H J := by
  classical
  let hfinite := hyperbolaLatticeSet_finite_of_interval
    X H M J hX hH hHX hMhalf hJ
  exact ⟨hfinite.toFinset, hfinite.coe_toFinset⟩

/-- After fixing a positive outer factor, every symmetric selected Type-I₂
block has an exact finite hyperbola-lattice representation.  The first
coordinate carries the selected `kM` interval, while the restriction to the
selected `kN` interval is absorbed into the second weight. -/
theorem exists_typeI2_selected_lattice_representation
    (β₁ β₂ : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (a kM kN : ℕ) (ha : 0 < a)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H ≤ X) :
    ∃ Λ : Finset (ℤ × ℤ),
      (Λ : Set (ℤ × ℤ)) =
          Hyperbola.hyperbolaLatticeSet (X / (a : ℝ)) (H / (a : ℝ))
            (Set.Ioc (typeIDyadicScale kM) (2 * typeIDyadicScale kM)) ∧
        typeI2SymmetricInner β₁ β₂ P X H
            (typeIDyadicBlock (Nat.floor (X + H)) kM)
            (typeIDyadicBlock (Nat.floor (X + H)) kN) a =
          ∑ p ∈ Λ,
            complexPositiveIntegerZeroExtension β₁ p.1 *
              complexPositiveIntegerZeroExtension
                (intervalWeightRestriction
                  (Set.Ioc (typeIDyadicScale kN)
                    (2 * typeIDyadicScale kN)) β₂) p.2 *
                unitFrequencyPhase
                  ((typeI2DilatedPolynomial P a).eval
                    ((p.1 : ℝ) * (p.2 : ℝ))) := by
  have haReal : 0 < (a : ℝ) := by exact_mod_cast ha
  have hXa : 0 < X / (a : ℝ) := div_pos hX haReal
  have hHa : 0 ≤ H / (a : ℝ) := div_nonneg hH haReal.le
  have hHXa : H / (a : ℝ) ≤ X / (a : ℝ) :=
    (div_le_div_iff_of_pos_right haReal).2 hHX
  obtain ⟨Λ, hΛ⟩ := exists_hyperbolaLatticeFinset_of_interval
    (X / (a : ℝ)) (H / (a : ℝ)) (typeIDyadicScale kM)
    (Set.Ioc (typeIDyadicScale kM) (2 * typeIDyadicScale kM))
    hXa hHa hHXa (one_half_le_typeIDyadicScale kM) (by intro x hx; exact hx)
  refine ⟨Λ, hΛ, ?_⟩
  rw [typeI2SymmetricInner_eq_dilated_phase_sum β₁ β₂ P X H a kM kN
    ha hX.le hH]
  exact preliminaryTypeI2_intervalWeight_latticeSum
    (X / (a : ℝ)) (H / (a : ℝ)) (typeIDyadicScale kM)
    (Set.Ioc (typeIDyadicScale kM) (2 * typeIDyadicScale kM))
    hXa (one_half_le_typeIDyadicScale kM) (by intro x hx; exact hx)
    Λ hΛ β₁
    (intervalWeightRestriction
      (Set.Ioc (typeIDyadicScale kN) (2 * typeIDyadicScale kN)) β₂)
    (typeI2DilatedPolynomial P a)
    (fun p => unitFrequencyPhase
      ((typeI2DilatedPolynomial P a).eval ((p.1 : ℝ) * (p.2 : ℝ))))
    (by intro p hp; rfl)

/-- The variation budget for the interval-restricted second Type-I₂ weight.
This is the exact bridge from the global `δ⁻¹` hypothesis and the factor
three in `lpi:weight-cutoff` to a preliminary-inverse parameter `κ`. -/
theorem typeI2_intervalWeightVariation_le_parameter
    (β : ComplexPositiveIntegerFunction) (q : ℕ) (hq : 0 < q)
    (δ κ : ℝ) (k : ℕ)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹))
    (hbudget : 3 * δ⁻¹ ≤ κ⁻¹) :
    complexPositiveIntegerResidueVariation
        (intervalWeightRestriction
          (Set.Ioc (typeIDyadicScale k) (2 * typeIDyadicScale k)) β) q hq ≤
      ENNReal.ofReal (κ⁻¹) := by
  calc
    complexPositiveIntegerResidueVariation
        (intervalWeightRestriction
          (Set.Ioc (typeIDyadicScale k) (2 * typeIDyadicScale k)) β) q hq ≤
        3 * complexPositiveIntegerResidueVariation β q hq := by
      apply intervalWeightVariation
      intro x y z hx hy hxz hzy
      exact ⟨lt_of_lt_of_le hx.1 hxz, le_trans hzy hy.2⟩
    _ ≤ 3 * ENNReal.ofReal (δ⁻¹) :=
      mul_le_mul le_rfl hTV (by simp) (by simp)
    _ = ENNReal.ofReal (3 * δ⁻¹) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    _ ≤ ENNReal.ofReal (κ⁻¹) := ENNReal.ofReal_le_ofReal hbudget

/-- The inhomogeneous residue-variation hypothesis controls the zero
extension at every integer, including the zero values outside the positive
integers. -/
theorem typeI2_zeroExtension_norm_le
    (β : ComplexPositiveIntegerFunction) (q : ℕ) (hq : 0 < q)
    (δ : ℝ) (hδ : 0 < δ)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹)) (z : ℤ) :
    ‖complexPositiveIntegerZeroExtension β z‖ ≤ δ⁻¹ := by
  by_cases hz : 0 < z
  · let n : PositiveInteger := ⟨z.toNat, by omega⟩
    have hnCast : (n.1 : ℤ) = z := by
      dsimp [n]
      exact Int.toNat_of_nonneg hz.le
    rw [← hnCast, complexPositiveIntegerZeroExtension_natCast]
    exact preliminary_residueVariation_controls_value β q hq δ hδ hTV n
  · simp [complexPositiveIntegerZeroExtension, hz, inv_nonneg.mpr hδ.le]

/-- Cutting a weight down to an arbitrary real set cannot increase the
pointwise bound supplied by its original residue variation. -/
theorem typeI2_intervalWeight_zeroExtension_norm_le
    (J : Set ℝ) (β : ComplexPositiveIntegerFunction)
    (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹)) (z : ℤ) :
    ‖complexPositiveIntegerZeroExtension (intervalWeightRestriction J β) z‖ ≤
      δ⁻¹ := by
  by_cases hz : 0 < z
  · let n : PositiveInteger := ⟨z.toNat, by omega⟩
    have hnCast : (n.1 : ℤ) = z := by
      dsimp [n]
      exact Int.toNat_of_nonneg hz.le
    rw [← hnCast, complexPositiveIntegerZeroExtension_natCast]
    by_cases hnJ : (n.1 : ℝ) ∈ J
    · simp only [intervalWeightRestriction, hnJ, if_true]
      exact preliminary_residueVariation_controls_value β q hq δ hδ hTV n
    · simp [intervalWeightRestriction, hnJ, inv_nonneg.mpr hδ.le]
  · simp [complexPositiveIntegerZeroExtension, hz, inv_nonneg.mpr hδ.le]

/-- The all-scales hyperbola count and the two original variation hypotheses
give the exact uniform pointwise correlation bound used in the full Type-I₂
argument. -/
theorem typeI2_lattice_correlation_norm_le
    (X H M : ℝ) (J : Set ℝ)
    (hX : 1 ≤ X)
    (hHlower : 16 * Real.rpow X (1 / 3 : ℝ) ≤ H)
    (hHupper : H ≤ X)
    (hMlower : (1 / 2 : ℝ) ≤ M)
    (hMupper : M ≤ 2 * Real.sqrt X)
    (hJconvex : Set.OrdConnected J)
    (hJsubset : J ⊆ Set.Ioc M (2 * M))
    (Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) =
      Hyperbola.hyperbolaLatticeSet X H J)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q hq ≤
      ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q hq ≤
      ENNReal.ofReal (δ⁻¹))
    (J₂ : Set ℝ) (P : Polynomial ℝ) :
    ‖∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension
            (intervalWeightRestriction J₂ β₂) p.2 *
          unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖ ≤
      (typeI2CCountValue : ℝ) * δ⁻¹ ^ 2 * H := by
  have hδinvNonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have hterm : ∀ p ∈ Λ,
      ‖complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension
            (intervalWeightRestriction J₂ β₂) p.2 *
          unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖ ≤
        δ⁻¹ ^ 2 := by
    intro p hp
    have hp₁ := typeI2_zeroExtension_norm_le β₁ q hq δ hδ hTV₁ p.1
    have hp₂ := typeI2_intervalWeight_zeroExtension_norm_le
      J₂ β₂ q hq δ hδ hTV₂ p.2
    simp only [norm_mul, norm_unitFrequencyPhase, mul_one]
    calc
      ‖complexPositiveIntegerZeroExtension β₁ p.1‖ *
          ‖complexPositiveIntegerZeroExtension
            (intervalWeightRestriction J₂ β₂) p.2‖ ≤
          δ⁻¹ * δ⁻¹ :=
        mul_le_mul hp₁ hp₂ (norm_nonneg _) hδinvNonneg
      _ = δ⁻¹ ^ 2 := by ring
  have hcard : Λ.card =
      (Hyperbola.hyperbolaLatticeSet X H J).ncard := by
    calc
      Λ.card = ((Λ : Set (ℤ × ℤ))).ncard :=
        (Set.ncard_coe_finset Λ).symm
      _ = (Hyperbola.hyperbolaLatticeSet X H J).ncard :=
        congrArg Set.ncard hΛ
  have hcount := hyperbolaCountAllScales X H M J hX hHlower hHupper
    hMlower hMupper hJconvex hJsubset
  calc
    ‖∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension
            (intervalWeightRestriction J₂ β₂) p.2 *
          unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖ ≤
        ∑ p ∈ Λ,
          ‖complexPositiveIntegerZeroExtension β₁ p.1 *
            complexPositiveIntegerZeroExtension
              (intervalWeightRestriction J₂ β₂) p.2 *
            unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ Λ, δ⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact hterm p hp
    _ = (Λ.card : ℝ) * δ⁻¹ ^ 2 := by simp [Finset.sum_const]
    _ = ((Hyperbola.hyperbolaLatticeSet X H J).ncard : ℝ) * δ⁻¹ ^ 2 := by
      rw [hcard]
    _ ≤ ((typeI2CCountValue : ℝ) * H) * δ⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ = (typeI2CCountValue : ℝ) * δ⁻¹ ^ 2 * H := by ring

/-- One retained outer dilation enters the already checked preliminary
Type-I₂ inverse theorem through the exact selected-lattice representation.
The returned monomial bounds are rewritten into the coordinates required by
many-dilate concatenation. -/
theorem typeI2_selected_inner_preliminary_inverse
    {d : ℕ} (hd : 1 ≤ d)
    (X H κ : ℝ) (a kM kN : ℕ) (ha : 0 < a)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hXa : 3 ≤ X / (a : ℝ))
    (hHa : 1 ≤ H / (a : ℝ))
    (hroot : Real.rpow (X / (a : ℝ)) (1 / 3 : ℝ) ≤ H / (a : ℝ))
    (hMupper : typeIDyadicScale kM ≤
      2 * Real.sqrt (X / (a : ℝ)))
    (hκ : 0 < κ)
    (hκsmall : κ < min (1 / 2)
      ((Real.log (X / (a : ℝ)))⁻¹))
    (q : ℕ) (hq : 1 ≤ q) (hqbound : (q : ℝ) ≤ κ⁻¹)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q (by omega) ≤
      ENNReal.ofReal (κ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation
      (intervalWeightRestriction
        (Set.Ioc (typeIDyadicScale kN) (2 * typeIDyadicScale kN)) β₂)
      q (by omega) ≤ ENNReal.ofReal (κ⁻¹))
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hlarge : κ * (H / (a : ℝ)) ≤
      ‖typeI2SymmetricInner β₁ β₂ P X H
        (typeIDyadicBlock (Nat.floor (X + H)) kM)
        (typeIDyadicBlock (Nat.floor (X + H)) kN) a‖) :
    H / (a : ℝ) ≤ typeI2J d κ⁻¹ *
        Real.rpow (X / (a : ℝ)) (1 / 3 : ℝ) ∨
      ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ typeI2J d κ⁻¹ ∧
        ∀ j, 1 ≤ j → j ≤ d →
          (H / (a : ℝ)) ^ j * realDistanceToIntegers
            ((r : ℝ) * (phaseDilatedAt P a
              (Int.floor (X / (a : ℝ)))).coeff j) ≤
            typeI2J d κ⁻¹ := by
  have hHdiv : H / (a : ℝ) ≤ X / (a : ℝ) := by
    have haReal : 0 < (a : ℝ) := by exact_mod_cast ha
    exact (div_le_div_iff_of_pos_right haReal).2 hHX
  obtain ⟨Λ, hΛ, hrepresentation⟩ :=
    exists_typeI2_selected_lattice_representation
      β₁ β₂ P X H a kM kN ha hX hH hHX
  have hlargeLattice : κ * (H / (a : ℝ)) ≤
      ‖∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension
            (intervalWeightRestriction
              (Set.Ioc (typeIDyadicScale kN)
                (2 * typeIDyadicScale kN)) β₂) p.2 *
          unitFrequencyPhase
            ((typeI2DilatedPolynomial P a).eval
              ((p.1 : ℝ) * (p.2 : ℝ)))‖ := by
    rw [← hrepresentation]
    exact hlarge
  rcases preliminaryTypeI2Inverse d hd
      (X / (a : ℝ)) (H / (a : ℝ)) (typeIDyadicScale kM) κ
      (Set.Ioc (typeIDyadicScale kM) (2 * typeIDyadicScale kM))
      hXa hHa hroot hHdiv (one_half_le_typeIDyadicScale kM) hMupper
      Set.ordConnected_Ioc (by intro x hx; exact hx) hκ hκsmall
      q hq hqbound β₁
      (intervalWeightRestriction
        (Set.Ioc (typeIDyadicScale kN) (2 * typeIDyadicScale kN)) β₂)
      hTV₁ hTV₂ Λ hΛ (typeI2DilatedPolynomial P a)
      (typeI2DilatedPolynomial_degree d P hP a) hlargeLattice with
    hshort | ⟨r, hr, hrbound, hbin, hmono⟩
  · exact Or.inl hshort
  · right
    refine ⟨r, hr, hrbound, ?_⟩
    intro j hj hjd
    have hjbound := hmono j hj hjd
    rw [typeI2DilatedPolynomial_phaseCenteredAt] at hjbound
    exact hjbound

/-- Successive source dyadic scales are separated: if `k<l`, the upper
endpoint of block `k` is no larger than the lower endpoint of block `l`. -/
theorem two_mul_typeIDyadicScale_le_of_lt {k l : ℕ} (hkl : k < l) :
    2 * typeIDyadicScale k ≤ typeIDyadicScale l := by
  have hl0 : l ≠ 0 := by omega
  by_cases hk0 : k = 0
  · subst k
    have hpow : (1 : ℕ) ≤ 2 ^ (l - 1) := one_le_pow₀ (by omega)
    have hpowR : (1 : ℝ) ≤ ((2 ^ (l - 1) : ℕ) : ℝ) := by
      exact_mod_cast hpow
    simpa [typeIDyadicScale, hl0] using hpowR
  · simp only [typeIDyadicScale, if_neg hk0, if_neg hl0]
    norm_cast
    have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hkle : k ≤ l - 1 := by omega
    have hkEq : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
    calc
      2 * 2 ^ (k - 1) = 2 ^ (k - 1) * 2 := by ring
      _ = 2 ^ (k - 1 + 1) := (pow_succ 2 (k - 1)).symm
      _ = 2 ^ k := by rw [hkEq]
      _ ≤ 2 ^ (l - 1) := pow_le_pow_right' (by omega) hkle

/-- The standard half-open dyadic blocks used in the Type-I and Type-I₂
proofs are pairwise disjoint. -/
theorem typeIDyadicBlock_pairwiseDisjoint (N : ℕ) :
    Set.PairwiseDisjoint (↑(typeIDyadicIndices N)) (typeIDyadicBlock N) := by
  intro k hk l hl hne
  change Disjoint (typeIDyadicBlock N k) (typeIDyadicBlock N l)
  rw [Finset.disjoint_left]
  intro a hak hal
  have hkBounds := (Finset.mem_filter.mp hak).2
  have hlBounds := (Finset.mem_filter.mp hal).2
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · have hsep := two_mul_typeIDyadicScale_le_of_lt hkl
    linarith
  · have hsep := two_mul_typeIDyadicScale_le_of_lt hlk
    linarith

/-- The finite source dyadic blocks form an exact partition of `[1,N]`. -/
theorem typeIDyadicBlocks_biUnion (N : ℕ) :
    (typeIDyadicIndices N).biUnion (typeIDyadicBlock N) =
      Finset.Icc 1 N := by
  classical
  ext a
  constructor
  · intro ha
    rcases Finset.mem_biUnion.mp ha with ⟨k, hk, hak⟩
    exact (Finset.mem_filter.mp hak).1
  · intro ha
    obtain ⟨k, hk, hak⟩ := typeIDyadicBlock_cover N a ha
    exact Finset.mem_biUnion.mpr ⟨k, hk, hak⟩

/-- Sum decomposition over the exact finite dyadic partition. -/
theorem sum_typeIDyadicBlocks {M : Type*} [AddCommMonoid M]
    (N : ℕ) (f : ℕ → M) :
    (∑ a ∈ Finset.Icc 1 N, f a) =
      ∑ k ∈ typeIDyadicIndices N, ∑ a ∈ typeIDyadicBlock N k, f a := by
  classical
  rw [← typeIDyadicBlocks_biUnion N]
  exact Finset.sum_biUnion (typeIDyadicBlock_pairwiseDisjoint N)

/-- The two unrestricted Type-I₂ coordinates, which are at most `X+H≤2X`,
use strictly fewer than `8/δ` dyadic blocks under the source logarithmic
smallness hypothesis. -/
theorem typeI2InnerDyadicIndices_card_bound
    (X H δ : ℝ) (hX : 3 ≤ X) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hδ : 0 < δ) (hδlog : δ < (Real.log X)⁻¹) :
    (typeIDyadicIndices (Nat.floor (X + H))).card < 8 * δ⁻¹ := by
  have hXpos : 0 < X := by linarith
  have hXHthree : 3 ≤ X + H := by linarith
  have hN : 3 ≤ Nat.floor (X + H) := Nat.le_floor hXHthree
  have hNne : Nat.floor (X + H) ≠ 0 := by omega
  have hpowNat : 2 ^ Nat.log2 (Nat.floor (X + H)) ≤ Nat.floor (X + H) := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hNne
  have hfloorLe : ((Nat.floor (X + H) : ℕ) : ℝ) ≤ X + H :=
    Nat.floor_le (by linarith)
  have hpowReal : (2 : ℝ) ^ Nat.log2 (Nat.floor (X + H)) ≤ 2 * X := by
    calc
      (2 : ℝ) ^ Nat.log2 (Nat.floor (X + H)) =
          ((2 ^ Nat.log2 (Nat.floor (X + H)) : ℕ) : ℝ) := by norm_cast
      _ ≤ (Nat.floor (X + H) : ℝ) := by exact_mod_cast hpowNat
      _ ≤ X + H := hfloorLe
      _ ≤ 2 * X := by linarith
  have hlogXpos : 0 < Real.log X := by
    have hlog3 : 1 ≤ Real.log 3 := by
      exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
        Real.exp_one_lt_three |>.le
    have hlogmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX
    linarith
  have hlogTwo : (2 / 3 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogTwoLe : Real.log 2 ≤ Real.log X :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith)
  have hlogPow :
      (Nat.log2 (Nat.floor (X + H)) : ℝ) * Real.log 2 ≤
        Real.log 2 + Real.log X := by
    calc
      (Nat.log2 (Nat.floor (X + H)) : ℝ) * Real.log 2 =
          Real.log ((2 : ℝ) ^ Nat.log2 (Nat.floor (X + H))) := by
            rw [Real.log_pow]
      _ ≤ Real.log (2 * X) := Real.log_le_log (by positivity) hpowReal
      _ = Real.log 2 + Real.log X := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
  have hlogNat : (Nat.log2 (Nat.floor (X + H)) : ℝ) ≤
      3 * Real.log X := by
    have hnonneg : 0 ≤ (Nat.log2 (Nat.floor (X + H)) : ℝ) := by positivity
    nlinarith [hlogPow, hlogTwo, hlogTwoLe]
  have hcardEq : (typeIDyadicIndices (Nat.floor (X + H))).card =
      Nat.log2 (Nat.floor (X + H)) + 2 := by
    simp [typeIDyadicIndices, Nat.card_Icc]
  have hlogLarge : 1 ≤ Real.log X := by
    have hlog3 : 1 ≤ Real.log 3 := by
      exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
        Real.exp_one_lt_three |>.le
    have hlogmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX
    linarith
  have hcount :
      ((typeIDyadicIndices (Nat.floor (X + H))).card : ℝ) ≤
        5 * Real.log X := by
    rw [hcardEq]
    push_cast
    nlinarith [hlogNat, hlogLarge]
  have hδprod : δ * Real.log X < 1 := by
    apply (lt_div_iff₀ hlogXpos).mp
    simpa [one_div] using hδlog
  have hloglt : Real.log X < δ⁻¹ := by
    have hloglt' : Real.log X < 1 / δ :=
      (lt_div_iff₀ hδ).2 (by nlinarith [hδprod])
    simpa [one_div] using hloglt'
  calc
    ((typeIDyadicIndices (Nat.floor (X + H))).card : ℝ) ≤
        5 * Real.log X := hcount
    _ < 5 * δ⁻¹ := by nlinarith
    _ < 8 * δ⁻¹ := by have := inv_pos.mpr hδ; nlinarith

/-- Exact three-coordinate dyadic decomposition, with the block indices
ordered outside the three arithmetic variables. -/
theorem sum_typeIDyadicBlock_triples
    (N₁ N₂ N₃ : ℕ) (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 N₁,
        ∑ m ∈ Finset.Icc 1 N₂,
          ∑ n ∈ Finset.Icc 1 N₃, F a m n) =
      ∑ k₁ ∈ typeIDyadicIndices N₁,
        ∑ k₂ ∈ typeIDyadicIndices N₂,
          ∑ k₃ ∈ typeIDyadicIndices N₃,
            ∑ a ∈ typeIDyadicBlock N₁ k₁,
              ∑ m ∈ typeIDyadicBlock N₂ k₂,
                ∑ n ∈ typeIDyadicBlock N₃ k₃, F a m n := by
  classical
  rw [sum_typeIDyadicBlocks N₁]
  apply Finset.sum_congr rfl
  intro k₁ hk₁
  calc
    (∑ a ∈ typeIDyadicBlock N₁ k₁,
        ∑ m ∈ Finset.Icc 1 N₂,
          ∑ n ∈ Finset.Icc 1 N₃, F a m n) =
        ∑ a ∈ typeIDyadicBlock N₁ k₁,
          ∑ k₂ ∈ typeIDyadicIndices N₂,
            ∑ m ∈ typeIDyadicBlock N₂ k₂,
              ∑ n ∈ Finset.Icc 1 N₃, F a m n := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [sum_typeIDyadicBlocks N₂]
    _ = ∑ k₂ ∈ typeIDyadicIndices N₂,
          ∑ a ∈ typeIDyadicBlock N₁ k₁,
            ∑ m ∈ typeIDyadicBlock N₂ k₂,
              ∑ n ∈ Finset.Icc 1 N₃, F a m n := by
          rw [Finset.sum_comm]
    _ = ∑ k₂ ∈ typeIDyadicIndices N₂,
          ∑ k₃ ∈ typeIDyadicIndices N₃,
            ∑ a ∈ typeIDyadicBlock N₁ k₁,
              ∑ m ∈ typeIDyadicBlock N₂ k₂,
                ∑ n ∈ typeIDyadicBlock N₃ k₃, F a m n := by
          apply Finset.sum_congr rfl
          intro k₂ hk₂
          calc
            (∑ a ∈ typeIDyadicBlock N₁ k₁,
                ∑ m ∈ typeIDyadicBlock N₂ k₂,
                  ∑ n ∈ Finset.Icc 1 N₃, F a m n) =
                ∑ a ∈ typeIDyadicBlock N₁ k₁,
                  ∑ m ∈ typeIDyadicBlock N₂ k₂,
                    ∑ k₃ ∈ typeIDyadicIndices N₃,
                      ∑ n ∈ typeIDyadicBlock N₃ k₃, F a m n := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  apply Finset.sum_congr rfl
                  intro m hm
                  rw [sum_typeIDyadicBlocks N₃]
            _ = ∑ a ∈ typeIDyadicBlock N₁ k₁,
                  ∑ k₃ ∈ typeIDyadicIndices N₃,
                    ∑ m ∈ typeIDyadicBlock N₂ k₂,
                      ∑ n ∈ typeIDyadicBlock N₃ k₃, F a m n := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  rw [Finset.sum_comm]
            _ = ∑ k₃ ∈ typeIDyadicIndices N₃,
                  ∑ a ∈ typeIDyadicBlock N₁ k₁,
                    ∑ m ∈ typeIDyadicBlock N₂ k₂,
                      ∑ n ∈ typeIDyadicBlock N₃ k₃, F a m n := by
                  rw [Finset.sum_comm]

/-- A finite triple sum whose norm is larger than the number of terms times
`τ` has a summand of norm at least `τ`. -/
theorem exists_triple_norm_ge_of_norm_sum_ge
    (K₁ K₂ K₃ : Finset ℕ) (Z : ℕ → ℕ → ℕ → ℂ) (τ L : ℝ)
    (hproduct :
      (K₁.card : ℝ) * (K₂.card : ℝ) * (K₃.card : ℝ) * τ < L)
    (hlarge : L ≤ ‖∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, Z k₁ k₂ k₃‖) :
    ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, ∃ k₃ ∈ K₃, τ ≤ ‖Z k₁ k₂ k₃‖ := by
  classical
  by_contra hnone
  simp only [not_exists, not_and, not_le] at hnone
  have htriangle :
      ‖∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, Z k₁ k₂ k₃‖ ≤
        ∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, ‖Z k₁ k₂ k₃‖ := by
    calc
      ‖∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, Z k₁ k₂ k₃‖ ≤
          ∑ k₁ ∈ K₁, ‖∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, Z k₁ k₂ k₃‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ‖∑ k₃ ∈ K₃, Z k₁ k₂ k₃‖ := by
        apply Finset.sum_le_sum
        intro k₁ hk₁
        exact norm_sum_le _ _
      _ ≤ ∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, ‖Z k₁ k₂ k₃‖ := by
        apply Finset.sum_le_sum
        intro k₁ hk₁
        apply Finset.sum_le_sum
        intro k₂ hk₂
        exact norm_sum_le _ _
  have hterm :
      (∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, ‖Z k₁ k₂ k₃‖) ≤
        ∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, τ := by
    apply Finset.sum_le_sum
    intro k₁ hk₁
    apply Finset.sum_le_sum
    intro k₂ hk₂
    apply Finset.sum_le_sum
    intro k₃ hk₃
    exact (hnone k₁ hk₁ k₂ hk₂ k₃ hk₃).le
  have hconst :
      (∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, τ) =
        (K₁.card : ℝ) * (K₂.card : ℝ) * (K₃.card : ℝ) * τ := by
    simp [Finset.sum_const]
    ring
  have hcontra : L < L := calc
    L ≤ ‖∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, Z k₁ k₂ k₃‖ := hlarge
    _ ≤ ∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, ‖Z k₁ k₂ k₃‖ := htriangle
    _ ≤ ∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, τ := hterm
    _ = (K₁.card : ℝ) * (K₂.card : ℝ) * (K₃.card : ℝ) * τ := hconst
    _ < L := hproduct
  exact lt_irrefl L hcontra

/-- The exact Type-I₂ dyadic pigeonhole step.  The source block-count bounds
`4/δ`, `8/δ`, `8/δ` yield the literal retained mass
`ρ H = (δ^4/256) H`. -/
theorem exists_typeI2_dyadic_triple
    (N₁ N₂ N₃ : ℕ) (δ H : ℝ) (hδ : 0 < δ) (hH : 0 < H)
    (hcard₁ : (typeIDyadicIndices N₁).card < 4 * δ⁻¹)
    (hcard₂ : (typeIDyadicIndices N₂).card < 8 * δ⁻¹)
    (hcard₃ : (typeIDyadicIndices N₃).card < 8 * δ⁻¹)
    (F : ℕ → ℕ → ℕ → ℂ)
    (hlarge : δ * H ≤
      ‖∑ a ∈ Finset.Icc 1 N₁,
        ∑ m ∈ Finset.Icc 1 N₂,
          ∑ n ∈ Finset.Icc 1 N₃, F a m n‖) :
    ∃ k₁ ∈ typeIDyadicIndices N₁,
      ∃ k₂ ∈ typeIDyadicIndices N₂,
        ∃ k₃ ∈ typeIDyadicIndices N₃,
          (δ ^ 4 / 256) * H ≤
            ‖∑ a ∈ typeIDyadicBlock N₁ k₁,
              ∑ m ∈ typeIDyadicBlock N₂ k₂,
                ∑ n ∈ typeIDyadicBlock N₃ k₃, F a m n‖ := by
  classical
  let K₁ := typeIDyadicIndices N₁
  let K₂ := typeIDyadicIndices N₂
  let K₃ := typeIDyadicIndices N₃
  let Z : ℕ → ℕ → ℕ → ℂ := fun k₁ k₂ k₃ =>
    ∑ a ∈ typeIDyadicBlock N₁ k₁,
      ∑ m ∈ typeIDyadicBlock N₂ k₂,
        ∑ n ∈ typeIDyadicBlock N₃ k₃, F a m n
  have hK₁ne : K₁.Nonempty := by
    refine ⟨0, ?_⟩
    simp [K₁, typeIDyadicIndices]
  have hK₂ne : K₂.Nonempty := by
    refine ⟨0, ?_⟩
    simp [K₂, typeIDyadicIndices]
  have hK₃ne : K₃.Nonempty := by
    refine ⟨0, ?_⟩
    simp [K₃, typeIDyadicIndices]
  have hc₁pos : 0 < (K₁.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hK₁ne
  have hc₂pos : 0 < (K₂.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hK₂ne
  have hc₃pos : 0 < (K₃.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hK₃ne
  have hc₁δ : (K₁.card : ℝ) * δ < 4 := by
    apply (lt_div_iff₀ hδ).mp
    simpa [K₁, div_eq_mul_inv] using hcard₁
  have hc₂δ : (K₂.card : ℝ) * δ < 8 := by
    apply (lt_div_iff₀ hδ).mp
    simpa [K₂, div_eq_mul_inv] using hcard₂
  have hc₃δ : (K₃.card : ℝ) * δ < 8 := by
    apply (lt_div_iff₀ hδ).mp
    simpa [K₃, div_eq_mul_inv] using hcard₃
  have hpair :
      ((K₁.card : ℝ) * δ) * ((K₂.card : ℝ) * δ) < 4 * 8 := by
    calc
      ((K₁.card : ℝ) * δ) * ((K₂.card : ℝ) * δ) <
          4 * ((K₂.card : ℝ) * δ) :=
        mul_lt_mul_of_pos_right hc₁δ (mul_pos hc₂pos hδ)
      _ < 4 * 8 := mul_lt_mul_of_pos_left hc₂δ (by norm_num)
  have htriple :
      ((K₁.card : ℝ) * δ) * ((K₂.card : ℝ) * δ) *
          ((K₃.card : ℝ) * δ) < 256 := by
    calc
      ((K₁.card : ℝ) * δ) * ((K₂.card : ℝ) * δ) *
          ((K₃.card : ℝ) * δ) <
          (4 * 8) * ((K₃.card : ℝ) * δ) :=
        mul_lt_mul_of_pos_right hpair (mul_pos hc₃pos hδ)
      _ < (4 * 8) * 8 := mul_lt_mul_of_pos_left hc₃δ (by norm_num)
      _ = 256 := by norm_num
  have hratio :
      (((K₁.card : ℝ) * δ) * ((K₂.card : ℝ) * δ) *
          ((K₃.card : ℝ) * δ)) / 256 < 1 := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 256)).2
    simpa using htriple
  have hproduct :
      (K₁.card : ℝ) * (K₂.card : ℝ) * (K₃.card : ℝ) *
          ((δ ^ 4 / 256) * H) < δ * H := by
    calc
      (K₁.card : ℝ) * (K₂.card : ℝ) * (K₃.card : ℝ) *
          ((δ ^ 4 / 256) * H) =
          (δ * H) *
            ((((K₁.card : ℝ) * δ) * ((K₂.card : ℝ) * δ) *
              ((K₃.card : ℝ) * δ)) / 256) := by ring
      _ < (δ * H) * 1 := mul_lt_mul_of_pos_left hratio (mul_pos hδ hH)
      _ = δ * H := by ring
  have hlarge' : δ * H ≤
      ‖∑ k₁ ∈ K₁, ∑ k₂ ∈ K₂, ∑ k₃ ∈ K₃, Z k₁ k₂ k₃‖ := by
    rw [← sum_typeIDyadicBlock_triples N₁ N₂ N₃ F]
    exact hlarge
  obtain ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, hZ⟩ :=
    exists_triple_norm_ge_of_norm_sum_ge K₁ K₂ K₃ Z
      ((δ ^ 4 / 256) * H) (δ * H) hproduct hlarge'
  exact ⟨k₁, by simpa [K₁] using hk₁,
    k₂, by simpa [K₂] using hk₂,
    k₃, by simpa [K₃] using hk₃, by simpa [Z] using hZ⟩

/-- The Type-I₂ second moment of the outer coefficient and
Cauchy--Schwarz turn one large selected block into the exact source lower
bound for the squared inner correlations. -/
theorem typeI2_block_inner_square_sum_lower
    (α : ComplexPositiveIntegerFunction) (S : Finset ℕ) (inner : ℕ → ℂ)
    (δ ρ H A : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hH : 0 < H)
    (hAhalf : 1 / 2 ≤ A)
    (hMoment : complexPositiveSecondMomentBound δ α)
    (hSbounds : ∀ a ∈ S, A < (a : ℝ) ∧ (a : ℝ) ≤ 2 * A)
    (hRaw : ρ * H ≤
      ‖∑ a ∈ S, complexPositiveIntegerNatExtension α a * inner a‖) :
    δ * ρ ^ 2 * H ^ 2 / (2 * A) ≤
      ∑ a ∈ S, ‖inner a‖ ^ 2 := by
  have hApos : 0 < A := by linarith
  have h2A : 1 ≤ 2 * A := by linarith
  have hSpos : ∀ a ∈ S, 0 < a := by
    intro a ha
    have haPositive : 0 < (a : ℝ) :=
      lt_trans hApos (hSbounds a ha).1
    exact_mod_cast haPositive
  have hSsubset : S ⊆ Finset.Icc 1 (Nat.floor (2 * A)) := by
    intro a ha
    have haOne : 1 ≤ a := Nat.succ_le_iff.mpr (hSpos a ha)
    have haUpper : a ≤ Nat.floor (2 * A) :=
      Nat.le_floor (hSbounds a ha).2
    exact Finset.mem_Icc.mpr ⟨haOne, haUpper⟩
  have hMomentSum :
      (∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ ^ 2) ≤
        complexPositiveSecondMoment α (2 * A) := by
    calc
      (∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ ^ 2) =
          ∑ a ∈ S, complexPositiveSecondMomentSummand α a := by
            apply Finset.sum_congr rfl
            intro a ha
            have haPos := hSpos a ha
            simp [complexPositiveIntegerNatExtension,
              complexPositiveSecondMomentSummand, haPos]
      _ ≤ complexPositiveSecondMoment α (2 * A) := by
        unfold complexPositiveSecondMoment
        apply Finset.sum_le_sum_of_subset_of_nonneg hSsubset
        intro a ha hnot
        simp [complexPositiveSecondMomentSummand]
        by_cases haPos : 0 < a <;> simp [haPos]
  have hAlphaSquare :
      (∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ ^ 2) ≤
        (2 * A) / δ := by
    calc
      _ ≤ complexPositiveSecondMoment α (2 * A) := hMomentSum
      _ ≤ δ⁻¹ * (2 * A) := hMoment (2 * A) h2A
      _ = (2 * A) / δ := by ring
  have hweighted : ρ * H ≤
      ∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ * ‖inner a‖ := by
    calc
      ρ * H ≤ ‖∑ a ∈ S,
          complexPositiveIntegerNatExtension α a * inner a‖ := hRaw
      _ ≤ ∑ a ∈ S,
          ‖complexPositiveIntegerNatExtension α a * inner a‖ :=
        norm_sum_le _ _
      _ = ∑ a ∈ S,
          ‖complexPositiveIntegerNatExtension α a‖ * ‖inner a‖ := by
        apply Finset.sum_congr rfl
        intro a ha
        exact norm_mul _ _
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun a => ‖complexPositiveIntegerNatExtension α a‖)
    (fun a => ‖inner a‖)
  have hInnerNonneg : 0 ≤ ∑ a ∈ S, ‖inner a‖ ^ 2 := by positivity
  have hWeightedNonneg : 0 ≤
      ∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ * ‖inner a‖ := by
    positivity
  have htargetNumerator :
      (ρ * H) ^ 2 ≤ ((2 * A) / δ) * ∑ a ∈ S, ‖inner a‖ ^ 2 := by
    calc
      (ρ * H) ^ 2 ≤
          (∑ a ∈ S,
            ‖complexPositiveIntegerNatExtension α a‖ * ‖inner a‖) ^ 2 := by
        exact (sq_le_sq₀ (by positivity) hWeightedNonneg).2 hweighted
      _ ≤ (∑ a ∈ S,
          ‖complexPositiveIntegerNatExtension α a‖ ^ 2) *
            ∑ a ∈ S, ‖inner a‖ ^ 2 := hCauchy
      _ ≤ ((2 * A) / δ) * ∑ a ∈ S, ‖inner a‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hAlphaSquare hInnerNonneg
  have hdenom : 0 < (2 * A) / δ := div_pos (by positivity) hδ
  have htargetNumerator' :
      (ρ * H) ^ 2 ≤
        (∑ a ∈ S, ‖inner a‖ ^ 2) * ((2 * A) / δ) := by
    calc
      _ ≤ ((2 * A) / δ) * ∑ a ∈ S, ‖inner a‖ ^ 2 := htargetNumerator
      _ = _ := by ring
  have hdiv := (div_le_iff₀ hdenom).2 htargetNumerator'
  have hidentity :
      ((ρ * H) ^ 2) / ((2 * A) / δ) =
        δ * ρ ^ 2 * H ^ 2 / (2 * A) := by
    field_simp
  rw [hidentity] at hdiv
  exact hdiv

/-- Removing all outer indices below the source threshold
`κ H/A = (δρ/4) H/A` leaves at least the exact source density
`η A = δ⁵ρ² A/(8 C²)`, provided every inner correlation obeys the uniform
hyperbola-count upper bound `C δ⁻² H/A`. -/
theorem typeI2_many_large_inner_correlations
    (δ H A ρ C : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hH : 0 < H) (hA : 0 < A) (hρ : 0 < ρ) (hC : 0 < C)
    (S : Finset ℕ) (hScard : (S.card : ℝ) ≤ 2 * A)
    (inner : ℕ → ℂ)
    (hupper : ∀ a ∈ S, ‖inner a‖ ≤ C * δ⁻¹ ^ 2 * H / A)
    (hsquare : δ * ρ ^ 2 * H ^ 2 / (2 * A) ≤
      ∑ a ∈ S, ‖inner a‖ ^ 2) :
    (δ ^ 5 * ρ ^ 2 / (8 * C ^ 2)) * A ≤
      ((S.filter fun a =>
        (δ * ρ / 4) * (H / A) ≤ ‖inner a‖).card : ℝ) := by
  classical
  let threshold : ℝ := (δ * ρ / 4) * (H / A)
  let large := S.filter fun a => threshold ≤ ‖inner a‖
  let small := S.filter fun a => ‖inner a‖ < threshold
  let upper : ℝ := C * δ⁻¹ ^ 2 * H / A
  have hthresholdPos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hupperPos : 0 < upper := by
    dsimp [upper]
    positivity
  have hAne : A ≠ 0 := ne_of_gt hA
  have hCne : C ≠ 0 := ne_of_gt hC
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hδle2 : δ ≤ 2 := by linarith
  have hδmul : δ * δ ≤ δ * 2 :=
    mul_le_mul_of_nonneg_left hδle2 hδ.le
  have hlowCoeff : δ ^ 2 / 8 ≤ δ / 4 := by
    nlinarith [hδmul]
  have hcommonNonneg : 0 ≤ ρ ^ 2 * H ^ 2 / A := by positivity
  have hlowCompare :
      δ ^ 2 * ρ ^ 2 * H ^ 2 / (8 * A) ≤
        δ * ρ ^ 2 * H ^ 2 / (4 * A) := by
    calc
      δ ^ 2 * ρ ^ 2 * H ^ 2 / (8 * A) =
          (δ ^ 2 / 8) * (ρ ^ 2 * H ^ 2 / A) := by
            field_simp
      _ ≤ (δ / 4) * (ρ ^ 2 * H ^ 2 / A) :=
        mul_le_mul_of_nonneg_right hlowCoeff hcommonNonneg
      _ = δ * ρ ^ 2 * H ^ 2 / (4 * A) := by field_simp
  have hsmallSum :
      (∑ a ∈ small, ‖inner a‖ ^ 2) ≤
        δ * ρ ^ 2 * H ^ 2 / (4 * A) := by
    have hterm : ∀ a ∈ small, ‖inner a‖ ^ 2 ≤ threshold ^ 2 := by
      intro a ha
      have hlt := (Finset.mem_filter.mp ha).2
      exact (sq_le_sq₀ (norm_nonneg _) hthresholdPos.le).2 hlt.le
    have hcardSmall : (small.card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hsumBound :
        (∑ a ∈ small, ‖inner a‖ ^ 2) ≤ (2 * A) * threshold ^ 2 := by
      calc
        _ ≤ ∑ a ∈ small, threshold ^ 2 := Finset.sum_le_sum hterm
        _ = (small.card : ℝ) * threshold ^ 2 := by
          simp [Finset.sum_const]
        _ ≤ (S.card : ℝ) * threshold ^ 2 :=
          mul_le_mul_of_nonneg_right hcardSmall (sq_nonneg threshold)
        _ ≤ (2 * A) * threshold ^ 2 :=
          mul_le_mul_of_nonneg_right hScard (sq_nonneg threshold)
    have hscale : (2 * A) * threshold ^ 2 =
        δ ^ 2 * ρ ^ 2 * H ^ 2 / (8 * A) := by
      dsimp [threshold]
      field_simp
      ring
    calc
      _ ≤ (2 * A) * threshold ^ 2 := hsumBound
      _ = δ ^ 2 * ρ ^ 2 * H ^ 2 / (8 * A) := hscale
      _ ≤ _ := hlowCompare
  have hsplit :
      (∑ a ∈ S, ‖inner a‖ ^ 2) =
        (∑ a ∈ large, ‖inner a‖ ^ 2) +
          (∑ a ∈ small, ‖inner a‖ ^ 2) := by
    simpa only [large, small, not_le] using
      (Finset.sum_filter_add_sum_filter_not S
        (fun a => threshold ≤ ‖inner a‖) (fun a => ‖inner a‖ ^ 2)).symm
  let retained : ℝ := δ * ρ ^ 2 * H ^ 2 / (4 * A)
  have hratio : δ * ρ ^ 2 * H ^ 2 / (2 * A) = 2 * retained := by
    dsimp [retained]
    field_simp [hAne]
    <;> ring
  have hlargeLower : retained ≤ ∑ a ∈ large, ‖inner a‖ ^ 2 := by
    rw [hsplit, hratio] at hsquare
    have hsmallRetained : (∑ a ∈ small, ‖inner a‖ ^ 2) ≤ retained := by
      simpa [retained] using hsmallSum
    linarith
  have hlargeUpper :
      (∑ a ∈ large, ‖inner a‖ ^ 2) ≤
        (large.card : ℝ) * upper ^ 2 := by
    calc
      _ ≤ ∑ a ∈ large, upper ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have haS := (Finset.mem_filter.mp ha).1
        exact (sq_le_sq₀ (norm_nonneg _) hupperPos.le).2
          (by simpa [upper] using hupper a haS)
      _ = (large.card : ℝ) * upper ^ 2 := by
        simp [Finset.sum_const]
  have htargetFactor :
      ((δ ^ 5 * ρ ^ 2 / (8 * C ^ 2)) * A) * upper ^ 2 =
        δ * ρ ^ 2 * H ^ 2 / (8 * A) := by
    dsimp [upper]
    field_simp [hAne, hCne, hδne]
    <;> ring
  have hhalfRetained :
      δ * ρ ^ 2 * H ^ 2 / (8 * A) ≤ retained := by
    dsimp [retained]
    apply div_le_div_of_nonneg_left (by positivity)
    · positivity
    · nlinarith [hA]
  have hproduct :
      ((δ ^ 5 * ρ ^ 2 / (8 * C ^ 2)) * A) * upper ^ 2 ≤
        (large.card : ℝ) * upper ^ 2 := by
    calc
      _ = δ * ρ ^ 2 * H ^ 2 / (8 * A) := htargetFactor
      _ ≤ retained := hhalfRetained
      _ ≤ ∑ a ∈ large, ‖inner a‖ ^ 2 := hlargeLower
      _ ≤ _ := hlargeUpper
  have hcount : (δ ^ 5 * ρ ^ 2 / (8 * C ^ 2)) * A ≤
      (large.card : ℝ) :=
    le_of_mul_le_mul_right hproduct (sq_pos_of_pos hupperPos)
  simpa [large, threshold] using hcount

/-- The approved final Type-I₂ budget has a uniform lower bound strong
enough to supply every local scale inequality in the final assembly. -/
theorem typeI2Bound_ge_sixteen
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : 2 ≤ x) :
    16 ≤ typeI2Bound d x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  let B : ℝ := typeI2J d (1024 * x ^ 5)
  let y : ℝ := 524288 * (typeI2CCountValue : ℝ) ^ 2 * x ^ 13
  have hB : 16 ≤ B := by
    dsimp [B]
    exact typeI2J_ge_sixteen d (1024 * x ^ 5) (by positivity)
  have hB1 : 1 ≤ B := by linarith
  have hC1 : 1 ≤ (typeI2CCountValue : ℝ) := by
    norm_num [typeI2CCountValue, typeI2CPointValue, typeI2BZeroValue,
      typeI2EValue, typeI2DValue, typeI2KZeroValue]
  have hC2 : 1 ≤ (typeI2CCountValue : ℝ) ^ 2 := one_le_pow₀ hC1
  have hx13 : 1 ≤ x ^ 13 := one_le_pow₀ hx1
  have hy : 2 ≤ y := by
    dsimp [y]
    have hmulC : (524288 : ℝ) ≤
        524288 * (typeI2CCountValue : ℝ) ^ 2 := by
      nlinarith [mul_nonneg
        (show (0 : ℝ) ≤ 524288 by norm_num) (sub_nonneg.mpr hC2)]
    have hmulX :
        524288 * (typeI2CCountValue : ℝ) ^ 2 ≤
          524288 * (typeI2CCountValue : ℝ) ^ 2 * x ^ 13 := by
      calc
        524288 * (typeI2CCountValue : ℝ) ^ 2 =
            524288 * (typeI2CCountValue : ℝ) ^ 2 * 1 := by ring
        _ ≤ 524288 * (typeI2CCountValue : ℝ) ^ 2 * x ^ 13 :=
          mul_le_mul_of_nonneg_left hx13 (by positivity)
    exact (show (2 : ℝ) ≤ 524288 by norm_num) |>.trans
      (hmulC.trans hmulX)
  have hV : 4 ≤ inverseBoundV d B y :=
    inverseBoundV_ge_four d hd B y hB1 hy
  have hE : 1 ≤ (inverseBoundEValue d : ℝ) := by
    exact_mod_cast inverseBoundE_ge_one d
  have hinner : 0 ≤ 16 + B + inverseBoundV d B y := by linarith
  rw [typeI2Bound_eval]
  change 16 ≤ (inverseBoundEValue d : ℝ) *
    (16 + B + inverseBoundV d B y)
  calc
    16 ≤ 16 + B + inverseBoundV d B y := by linarith
    _ = 1 * (16 + B + inverseBoundV d B y) := by ring
    _ ≤ (inverseBoundEValue d : ℝ) *
        (16 + B + inverseBoundV d B y) :=
      mul_le_mul_of_nonneg_right hE hinner

/-- The final approved Type-I₂ budget simultaneously dominates the local
preliminary-inverse budget and the many-dilate concatenation budget. -/
theorem typeI2_finalBudget_dominates
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : 2 ≤ x) :
    typeI2J d (1024 * x ^ 5) ≤ typeI2Bound d x ∧
      inverseBoundV d (typeI2J d (1024 * x ^ 5))
        (typeI2Density x) ≤ typeI2Bound d x := by
  let B : ℝ := typeI2J d (1024 * x ^ 5)
  let y : ℝ := typeI2Density x
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hB : 16 ≤ B := by
    dsimp [B]
    exact typeI2J_ge_sixteen d (1024 * x ^ 5) (by positivity)
  have hB1 : 1 ≤ B := by linarith
  have hC1 : 1 ≤ (typeI2CCountValue : ℝ) := by
    norm_num [typeI2CCountValue, typeI2CPointValue, typeI2BZeroValue,
      typeI2EValue, typeI2DValue, typeI2KZeroValue]
  have hC2 : 1 ≤ (typeI2CCountValue : ℝ) ^ 2 := one_le_pow₀ hC1
  have hx13 : 1 ≤ x ^ 13 := one_le_pow₀ hx1
  have hy2 : 2 ≤ y := by
    dsimp [y]
    rw [typeI2Density_eval]
    have hmulC : (524288 : ℝ) ≤
        524288 * (typeI2CCountValue : ℝ) ^ 2 := by
      nlinarith [mul_nonneg
        (show (0 : ℝ) ≤ 524288 by norm_num) (sub_nonneg.mpr hC2)]
    have hmulX :
        524288 * (typeI2CCountValue : ℝ) ^ 2 ≤
          524288 * (typeI2CCountValue : ℝ) ^ 2 * x ^ 13 := by
      calc
        524288 * (typeI2CCountValue : ℝ) ^ 2 =
            524288 * (typeI2CCountValue : ℝ) ^ 2 * 1 := by ring
        _ ≤ 524288 * (typeI2CCountValue : ℝ) ^ 2 * x ^ 13 :=
          mul_le_mul_of_nonneg_left hx13 (by positivity)
    exact (show (2 : ℝ) ≤ 524288 by norm_num) |>.trans
      (hmulC.trans hmulX)
  have hV : 4 ≤ inverseBoundV d B y :=
    inverseBoundV_ge_four d hd B y hB1 hy2
  have hE : 1 ≤ (inverseBoundEValue d : ℝ) := by
    exact_mod_cast inverseBoundE_ge_one d
  have hinner : 0 ≤ 16 + B + inverseBoundV d B y := by linarith
  have hBfinal : B ≤ typeI2Bound d x := by
    rw [typeI2Bound_eval, ← typeI2Density_eval]
    change B ≤ (inverseBoundEValue d : ℝ) *
      (16 + B + inverseBoundV d B y)
    calc
      B ≤ 16 + B + inverseBoundV d B y := by linarith
      _ = 1 * (16 + B + inverseBoundV d B y) := by ring
      _ ≤ (inverseBoundEValue d : ℝ) *
          (16 + B + inverseBoundV d B y) :=
        mul_le_mul_of_nonneg_right hE hinner
  have hVfinal : inverseBoundV d B y ≤ typeI2Bound d x := by
    rw [typeI2Bound_eval, ← typeI2Density_eval]
    change inverseBoundV d B y ≤ (inverseBoundEValue d : ℝ) *
      (16 + B + inverseBoundV d B y)
    calc
      inverseBoundV d B y ≤ 16 + B + inverseBoundV d B y := by linarith
      _ = 1 * (16 + B + inverseBoundV d B y) := by ring
      _ ≤ (inverseBoundEValue d : ℝ) *
          (16 + B + inverseBoundV d B y) :=
        mul_le_mul_of_nonneg_right hE hinner
  exact ⟨by simpa [B] using hBfinal, by simpa [B, y] using hVfinal⟩

/-- Exact reciprocal of the source threshold
`κ=δ⁵/1024`. -/
theorem typeI2Kappa_inv (δ : ℝ) (hδ : 0 < δ) :
    (δ ^ 5 / 1024)⁻¹ = 1024 * δ⁻¹ ^ 5 := by
  field_simp [ne_of_gt hδ]
  <;> ring

/-- Exact reciprocal of the retained-density parameter, identified with the
second input of the approved concatenation budget. -/
theorem typeI2Eta_inv (δ : ℝ) (hδ : 0 < δ) :
    (δ ^ 13 /
      (524288 * (typeI2CCountValue : ℝ) ^ 2))⁻¹ =
      typeI2Density δ⁻¹ := by
  have hC : (typeI2CCountValue : ℝ) ≠ 0 := by
    norm_num [typeI2CCountValue, typeI2CPointValue, typeI2BZeroValue,
      typeI2EValue, typeI2DValue, typeI2KZeroValue]
  rw [typeI2Density_eval]
  field_simp [ne_of_gt hδ, hC]
  <;> ring

/-- Terms outside the approved outer support may be removed from a selected
Type-I₂ block without changing its weighted inner sum. -/
theorem typeI2_outer_sum_restrict_support
    (α : ComplexPositiveIntegerFunction) (A₀ : ℝ)
    (hsupp : complexPositiveSupportedOnInterval α 1 A₀)
    (S : Finset ℕ) (inner : ℕ → ℂ) :
    (∑ a ∈ S, complexPositiveIntegerNatExtension α a * inner a) =
      ∑ a ∈ S.filter (fun a : ℕ => (a : ℝ) ≤ A₀),
        complexPositiveIntegerNatExtension α a * inner a := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases haA : (a : ℝ) ≤ A₀
  · simp [haA]
  · have hzero : complexPositiveIntegerNatExtension α a = 0 := by
      by_cases hapos : 0 < a
      · by_contra hne
        have hval : α ⟨a, hapos⟩ ≠ 0 := by
          simpa [complexPositiveIntegerNatExtension, hapos] using hne
        have hupper := (hsupp ⟨a, hapos⟩ hval).2
        exact haA hupper
      · simp [complexPositiveIntegerNatExtension, hapos]
    simp [haA, hzero]

/-- A global Type-I₂ length inequality descends to every retained outer
dilation, with any local budget dominated by the final budget. -/
theorem typeI2_local_budget_length
    (X H A₀ a B F : ℝ)
    (hX : 0 < X) (hA₀ : 0 < A₀) (ha : 0 < a)
    (haA₀ : a ≤ A₀) (hB : 0 ≤ B) (hBF : B ≤ F)
    (hlong : F * Real.rpow X (1 / 3 : ℝ) *
      Real.rpow A₀ (2 / 3 : ℝ) < H) :
    B * Real.rpow (X / a) (1 / 3 : ℝ) < H / a := by
  have hanonneg : 0 ≤ a := ha.le
  have hXnonneg : 0 ≤ X := hX.le
  have haPow :
      a = Real.rpow a (1 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) := by
    calc
      a = Real.rpow a (1 : ℝ) := (Real.rpow_one a).symm
      _ = Real.rpow a ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by norm_num
      _ = Real.rpow a (1 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) :=
        Real.rpow_add ha _ _
  have hrootA : Real.rpow a (1 / 3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ha _)
  have haDiv :
      a / Real.rpow a (1 / 3 : ℝ) = Real.rpow a (2 / 3 : ℝ) := by
    apply (div_eq_iff hrootA).2
    exact haPow.trans (mul_comm _ _)
  have hlocalIdentity :
      Real.rpow (X / a) (1 / 3 : ℝ) * a =
        Real.rpow X (1 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) := by
    change (X / a) ^ (1 / 3 : ℝ) * a =
      X ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)
    rw [Real.div_rpow hXnonneg hanonneg]
    calc
      (X ^ (1 / 3 : ℝ) / a ^ (1 / 3 : ℝ)) * a =
          X ^ (1 / 3 : ℝ) * (a / a ^ (1 / 3 : ℝ)) := by
        field_simp [hrootA]
      _ = X ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ) := by
        exact congrArg (fun z : ℝ => X ^ (1 / 3 : ℝ) * z) haDiv
  have haRpow : Real.rpow a (2 / 3 : ℝ) ≤
      Real.rpow A₀ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hanonneg haA₀ (by norm_num)
  have hF : 0 ≤ F := hB.trans hBF
  apply (lt_div_iff₀ ha).2
  calc
    B * Real.rpow (X / a) (1 / 3 : ℝ) * a =
        B * (Real.rpow (X / a) (1 / 3 : ℝ) * a) := by ring
    _ = B * Real.rpow X (1 / 3 : ℝ) *
        Real.rpow a (2 / 3 : ℝ) := by rw [hlocalIdentity]; ring
    _ ≤ F * Real.rpow X (1 / 3 : ℝ) *
        Real.rpow a (2 / 3 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hBF (Real.rpow_nonneg hXnonneg _))
        (Real.rpow_nonneg hanonneg _)
    _ ≤ F * Real.rpow X (1 / 3 : ℝ) *
        Real.rpow A₀ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left haRpow
        (mul_nonneg hF (Real.rpow_nonneg hXnonneg _))
    _ < H := hlong

/-- The failed global Type-I₂ length alternative supplies the exact local
scale conditions required at every retained outer dilation. -/
theorem typeI2_local_scale_bounds
    (X H A₀ a : ℝ)
    (hX : 0 < X) (hHX : H ≤ X) (hA₀ : 0 < A₀)
    (ha : 0 < a) (haA₀ : a ≤ A₀)
    (hlong : 16 * Real.rpow X (1 / 3 : ℝ) *
      Real.rpow A₀ (2 / 3 : ℝ) < H) :
    3 ≤ X / a ∧ 1 ≤ H / a ∧
      16 * Real.rpow (X / a) (1 / 3 : ℝ) ≤ H / a := by
  have hA₀nonneg : 0 ≤ A₀ := hA₀.le
  have hanonneg : 0 ≤ a := ha.le
  have hXnonneg : 0 ≤ X := hX.le
  have haPow :
      a = Real.rpow a (1 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) := by
    calc
      a = Real.rpow a (1 : ℝ) := (Real.rpow_one a).symm
      _ = Real.rpow a ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by norm_num
      _ = Real.rpow a (1 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) :=
        Real.rpow_add ha _ _
  have hlocalIdentity :
      Real.rpow (X / a) (1 / 3 : ℝ) * a =
        Real.rpow X (1 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) := by
    change (X / a) ^ (1 / 3 : ℝ) * a =
      X ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)
    have hrootA : Real.rpow a (1 / 3 : ℝ) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos ha _)
    have haDiv :
        a / Real.rpow a (1 / 3 : ℝ) = Real.rpow a (2 / 3 : ℝ) := by
      apply (div_eq_iff hrootA).2
      exact haPow.trans (mul_comm _ _)
    rw [Real.div_rpow hXnonneg hanonneg]
    calc
      (X ^ (1 / 3 : ℝ) / a ^ (1 / 3 : ℝ)) * a =
          X ^ (1 / 3 : ℝ) * (a / a ^ (1 / 3 : ℝ)) := by
        field_simp [hrootA]
      _ = X ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ) := by
        exact congrArg (fun z : ℝ => X ^ (1 / 3 : ℝ) * z) haDiv
  have haRpow : Real.rpow a (2 / 3 : ℝ) ≤
      Real.rpow A₀ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hanonneg haA₀ (by norm_num)
  have hlocalRoot :
      16 * Real.rpow (X / a) (1 / 3 : ℝ) ≤ H / a := by
    apply (le_div_iff₀ ha).2
    calc
      16 * Real.rpow (X / a) (1 / 3 : ℝ) * a =
          16 * (Real.rpow (X / a) (1 / 3 : ℝ) * a) := by ring
      _ = 16 * Real.rpow X (1 / 3 : ℝ) *
          Real.rpow a (2 / 3 : ℝ) := by rw [hlocalIdentity]; ring
      _ ≤ 16 * Real.rpow X (1 / 3 : ℝ) *
          Real.rpow A₀ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left haRpow
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hXnonneg _))
      _ ≤ H := hlong.le
  have hratioPos : 0 < X / a := div_pos hX ha
  let u : ℝ := Real.rpow (X / a) (1 / 3 : ℝ)
  have hu : 0 < u := by
    dsimp [u]
    exact Real.rpow_pos_of_pos hratioPos _
  have huCube : u ^ 3 = X / a := by
    dsimp [u]
    convert Real.rpow_inv_natCast_pow hratioPos.le
      (by norm_num : (3 : ℕ) ≠ 0) using 1 <;> norm_num
  have hlocalUpper : H / a ≤ X / a :=
    (div_le_div_iff_of_pos_right ha).2 hHX
  have h16u : 16 * u ≤ X / a := by
    exact le_trans hlocalRoot hlocalUpper
  have hu4 : 4 ≤ u := by
    rw [← huCube] at h16u
    nlinarith [sq_nonneg u]
  have huPow : (4 : ℝ) ^ 3 ≤ u ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hu4 3
  have hratio64 : 64 ≤ X / a := by
    rw [← huCube]
    norm_num at huPow ⊢
    exact huPow
  have hHdiv : 1 ≤ H / a := by
    have h64 : (64 : ℝ) ≤ H / a := by
      calc
        64 = 16 * 4 := by norm_num
        _ ≤ 16 * u := mul_le_mul_of_nonneg_left hu4 (by norm_num)
        _ ≤ H / a := by simpa [u] using hlocalRoot
    linarith
  exact ⟨by linarith, hHdiv, hlocalRoot⟩

/-- Once a selected Type-I₂ triple is oriented so that its first inner
scale is the smaller one, the exact moment, hyperbola-count, preliminary
inverse, and dilation-concatenation inputs give the approved global
binomial conclusion. -/
theorem typeI2_oriented_block_inverse
    {d : ℕ} (hd : 1 ≤ d)
    (X H δ A₀ : ℝ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hδ : 0 < δ)
    (hδsmall : δ < min (1 / 2) ((Real.log X)⁻¹))
    (α β₁ β₂ : ComplexPositiveIntegerFunction)
    (hsupp : complexPositiveSupportedOnInterval α 1 A₀)
    (hMoment : complexPositiveSecondMomentBound δ α)
    (q : ℕ) (hq : 0 < q) (hqbound : (q : ℝ) ≤ δ⁻¹)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q hq ≤
      ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q hq ≤
      ENNReal.ofReal (δ⁻¹))
    (kA kM kN : ℕ)
    (hMN : typeIDyadicScale kM ≤ typeIDyadicScale kN)
    (hprod : typeIDyadicScale kA * typeIDyadicScale kM *
      typeIDyadicScale kN < 2 * X)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hrawP : (δ ^ 4 / 256) * H ≤
      ‖∑ a ∈ typeIDyadicBlock (Nat.floor X) kA,
        complexPositiveIntegerNatExtension α a *
          typeI2SymmetricInner β₁ β₂ P X H
            (typeIDyadicBlock (Nat.floor (X + H)) kM)
            (typeIDyadicBlock (Nat.floor (X + H)) kN) a‖)
    (hA₀ : 1 ≤ A₀) (hA₀X : A₀ < X)
    (hlength : typeI2Bound d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) *
      Real.rpow A₀ (2 / 3 : ℝ) < H) :
    ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ typeI2Bound d δ⁻¹ ∧
      polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
        (Int.floor X) H ≤ typeI2Bound d δ⁻¹ := by
  classical
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < H := by linarith
  have hA₀pos : 0 < A₀ := by linarith
  have hδhalf : δ < 1 / 2 :=
    lt_of_lt_of_le hδsmall (min_le_left _ _)
  have hδlog : δ < (Real.log X)⁻¹ :=
    lt_of_lt_of_le hδsmall (min_le_right _ _)
  have hδone : δ ≤ 1 := by linarith
  have hδinv : 2 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hδ).2
    nlinarith
  have hfinal16 : 16 ≤ typeI2Bound d δ⁻¹ :=
    typeI2Bound_ge_sixteen d hd δ⁻¹ hδinv
  have hscaleNonneg : 0 ≤
      Real.rpow X (1 / 3 : ℝ) * Real.rpow A₀ (2 / 3 : ℝ) := by
    exact mul_nonneg (Real.rpow_nonneg hXpos.le _)
      (Real.rpow_nonneg hA₀pos.le _)
  have hglobal16 :
      16 * Real.rpow X (1 / 3 : ℝ) *
        Real.rpow A₀ (2 / 3 : ℝ) < H := by
    have hmul := mul_le_mul_of_nonneg_right hfinal16 hscaleNonneg
    exact lt_of_le_of_lt (by simpa [mul_assoc] using hmul) hlength
  let ρ : ℝ := δ ^ 4 / 256
  let A : ℝ := typeIDyadicScale kA
  let M : ℝ := typeIDyadicScale kM
  let N : ℝ := typeIDyadicScale kN
  let S₀ : Finset ℕ := typeIDyadicBlock (Nat.floor X) kA
  let S : Finset ℕ := S₀.filter (fun a : ℕ => (a : ℝ) ≤ A₀)
  let inner : ℕ → ℂ := fun a =>
    typeI2SymmetricInner β₁ β₂ P X H
      (typeIDyadicBlock (Nat.floor (X + H)) kM)
      (typeIDyadicBlock (Nat.floor (X + H)) kN) a
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hAhalf : 1 / 2 ≤ A := by
    simpa [A] using one_half_le_typeIDyadicScale kA
  have hApos : 0 < A := by linarith
  have hMhalf : 1 / 2 ≤ M := by
    simpa [M] using one_half_le_typeIDyadicScale kM
  have hMpos : 0 < M := by linarith
  have hSbounds : ∀ a ∈ S,
      A < (a : ℝ) ∧ (a : ℝ) ≤ 2 * A := by
    intro a haS
    have haS₀ := (Finset.mem_filter.mp haS).1
    simpa [S₀, A, typeIDyadicBlock] using
      (Finset.mem_filter.mp haS₀).2
  have hSA₀ : ∀ a ∈ S, (a : ℝ) ≤ A₀ := by
    intro a haS
    exact (Finset.mem_filter.mp haS).2
  have hrawS : ρ * H ≤
      ‖∑ a ∈ S, complexPositiveIntegerNatExtension α a * inner a‖ := by
    have hraw₀ : ρ * H ≤
        ‖∑ a ∈ S₀, complexPositiveIntegerNatExtension α a * inner a‖ := by
      simpa [ρ, S₀, inner] using hrawP
    have hrestrict :=
      typeI2_outer_sum_restrict_support α A₀ hsupp S₀ inner
    rw [hrestrict] at hraw₀
    simpa [S] using hraw₀
  have hScard : (S.card : ℝ) ≤ 2 * A := by
    have hsub : S ⊆ S₀ := Finset.filter_subset _ _
    have hcardNat := Finset.card_le_card hsub
    have hcardReal : (S.card : ℝ) ≤ (S₀.card : ℝ) := by
      exact_mod_cast hcardNat
    exact hcardReal.trans (by
      simpa [S₀, A] using typeIDyadicBlock_card_le (Nat.floor X) kA)
  have hsquare : δ * ρ ^ 2 * H ^ 2 / (2 * A) ≤
      ∑ a ∈ S, ‖inner a‖ ^ 2 :=
    typeI2_block_inner_square_sum_lower α S inner δ ρ H A
      hδ hρpos hHpos hAhalf hMoment hSbounds hrawS
  have hupper : ∀ a ∈ S,
      ‖inner a‖ ≤
        (typeI2CCountValue : ℝ) * δ⁻¹ ^ 2 * H / A := by
    intro a haS
    have habounds := hSbounds a haS
    have haA₀ := hSA₀ a haS
    have haReal : 0 < (a : ℝ) := lt_trans hApos habounds.1
    have ha : 0 < a := by exact_mod_cast haReal
    have hlocal := typeI2_local_scale_bounds X H A₀ (a : ℝ)
      hXpos hHX hA₀pos haReal haA₀ hglobal16
    have hMupper : M ≤ 2 * Real.sqrt (X / (a : ℝ)) := by
      exact typeI2_oriented_inner_scale_le A M N X (a : ℝ)
        hAhalf hMpos (by simpa [M, N] using hMN)
        (by simpa [A, M, N] using hprod) haReal habounds.2
    obtain ⟨Λ, hΛ, hrepresentation⟩ :=
      exists_typeI2_selected_lattice_representation
        β₁ β₂ P X H a kM kN ha hXpos hHpos.le hHX
    have hHXa : H / (a : ℝ) ≤ X / (a : ℝ) :=
      (div_le_div_iff_of_pos_right haReal).2 hHX
    have hcount := typeI2_lattice_correlation_norm_le
      (X / (a : ℝ)) (H / (a : ℝ)) M
      (Set.Ioc M (2 * M)) (by linarith [hlocal.1]) hlocal.2.2 hHXa hMhalf hMupper
      Set.ordConnected_Ioc (by intro x hx; exact hx) Λ
      (by simpa [M] using hΛ) β₁ β₂ q hq δ hδ hTV₁ hTV₂
      (Set.Ioc N (2 * N)) (typeI2DilatedPolynomial P a)
    have hlocalNorm : ‖inner a‖ ≤
        (typeI2CCountValue : ℝ) * δ⁻¹ ^ 2 * (H / (a : ℝ)) := by
      dsimp [inner]
      rw [hrepresentation]
      simpa [M, N] using hcount
    have hdiv : H / (a : ℝ) ≤ H / A := by
      apply (div_le_div_iff₀ haReal hApos).2
      exact mul_le_mul_of_nonneg_left habounds.1.le hHpos.le
    calc
      ‖inner a‖ ≤
          (typeI2CCountValue : ℝ) * δ⁻¹ ^ 2 * (H / (a : ℝ)) :=
        hlocalNorm
      _ ≤ (typeI2CCountValue : ℝ) * δ⁻¹ ^ 2 * (H / A) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (typeI2CCountValue : ℝ) * δ⁻¹ ^ 2 * H / A := by ring
  have hCpos : 0 < (typeI2CCountValue : ℝ) := by
    norm_num [typeI2CCountValue, typeI2CPointValue, typeI2BZeroValue,
      typeI2EValue, typeI2DValue, typeI2KZeroValue]
  have hmany := typeI2_many_large_inner_correlations
    δ H A ρ (typeI2CCountValue : ℝ) hδ hδone hHpos hApos hρpos
    hCpos S hScard inner hupper hsquare
  let κ : ℝ := δ ^ 5 / 1024
  let η : ℝ := δ ^ 13 /
    (524288 * (typeI2CCountValue : ℝ) ^ 2)
  let Sgood : Finset ℕ := S.filter fun a =>
    κ * (H / A) ≤ ‖inner a‖
  have hκeq : δ * ρ / 4 = κ := by dsimp [ρ, κ]; ring
  have hηeq : δ ^ 5 * ρ ^ 2 /
      (8 * (typeI2CCountValue : ℝ) ^ 2) = η := by
    dsimp [ρ, η]
    ring
  have hSgoodCard : η * A ≤ (Sgood.card : ℝ) := by
    rw [hκeq, hηeq] at hmany
    simpa [Sgood] using hmany
  have hκpos : 0 < κ := by dsimp [κ]; positivity
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hδpow5 : δ ^ 5 ≤ δ := by
    have hpow4 : δ ^ 4 ≤ (1 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hδ.le hδone 4
    calc
      δ ^ 5 = δ * δ ^ 4 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (by simpa using hpow4) hδ.le
      _ = δ := by ring
  have hκleδ : κ ≤ δ := by
    dsimp [κ]
    have hnonneg : 0 ≤ δ ^ 5 := pow_nonneg hδ.le _
    calc
      δ ^ 5 / 1024 ≤ δ ^ 5 := by nlinarith
      _ ≤ δ := hδpow5
  have hκhalf : κ < 1 / 2 := lt_of_le_of_lt hκleδ hδhalf
  have hδpow13 : δ ^ 13 ≤ δ := by
    have hpow12 : δ ^ 12 ≤ (1 : ℝ) ^ 12 :=
      pow_le_pow_left₀ hδ.le hδone 12
    calc
      δ ^ 13 = δ * δ ^ 12 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (by simpa using hpow12) hδ.le
      _ = δ := by ring
  have hdenOne : 1 ≤ 524288 * (typeI2CCountValue : ℝ) ^ 2 := by
    have hCgeOne : (1 : ℝ) ≤ typeI2CCountValue := by
      norm_num [typeI2CCountValue, typeI2CPointValue, typeI2BZeroValue,
        typeI2EValue, typeI2DValue, typeI2KZeroValue]
    have hCsq : 1 ≤ (typeI2CCountValue : ℝ) ^ 2 :=
      one_le_pow₀ hCgeOne
    nlinarith [mul_nonneg
      (show (0 : ℝ) ≤ 524288 by norm_num) (sub_nonneg.mpr hCsq)]
  have hηleδ : η ≤ δ := by
    dsimp [η]
    have hdenpos : 0 < 524288 * (typeI2CCountValue : ℝ) ^ 2 := by
      positivity
    have hdiv : δ ^ 13 /
        (524288 * (typeI2CCountValue : ℝ) ^ 2) ≤ δ ^ 13 := by
      apply (div_le_iff₀ hdenpos).2
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hdenOne (pow_nonneg hδ.le 13)
    exact hdiv.trans hδpow13
  have hηhalf : η < 1 / 2 := lt_of_le_of_lt hηleδ hδhalf
  have hκinv : κ⁻¹ = 1024 * δ⁻¹ ^ 5 := by
    simpa [κ] using typeI2Kappa_inv δ hδ
  have hηinv : η⁻¹ = typeI2Density δ⁻¹ := by
    simpa [η] using typeI2Eta_inv δ hδ
  have hδinvK : δ⁻¹ ≤ κ⁻¹ := by
    exact (inv_le_inv₀ hδ hκpos).2 hκleδ
  have hthreeδinvK : 3 * δ⁻¹ ≤ κ⁻¹ := by
    rw [hκinv]
    have hx1 : 1 ≤ δ⁻¹ := by linarith
    have hxpow : δ⁻¹ ≤ δ⁻¹ ^ 5 := by
      calc
        δ⁻¹ = δ⁻¹ * 1 := by ring
        _ ≤ δ⁻¹ * δ⁻¹ ^ 4 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hx1) (inv_nonneg.mpr hδ.le)
        _ = δ⁻¹ ^ 5 := by ring
    calc
      3 * δ⁻¹ ≤ 1024 * δ⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hδ.le)
      _ ≤ 1024 * δ⁻¹ ^ 5 :=
        mul_le_mul_of_nonneg_left hxpow (by norm_num)
  let B : ℝ := typeI2J d (1024 * δ⁻¹ ^ 5)
  have hdom := typeI2_finalBudget_dominates d hd δ⁻¹ hδinv
  have hBfinal : B ≤ typeI2Bound d δ⁻¹ := by
    simpa [B] using hdom.1
  have hB16 : 16 ≤ B := by
    dsimp [B]
    exact typeI2J_ge_sixteen d (1024 * δ⁻¹ ^ 5) (by positivity)
  have hB1 : 1 ≤ B := by linarith
  have hSgoodbounds : ∀ a ∈ Sgood,
      A < (a : ℝ) ∧ (a : ℝ) ≤ 2 * A := by
    intro a ha
    exact hSbounds a (Finset.mem_filter.mp ha).1
  have hdata : ∀ a ∈ Sgood, ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ B ∧
      ∀ j, 1 ≤ j → j ≤ d →
        (H / (a : ℝ)) ^ j * realDistanceToIntegers
          ((r : ℝ) * (phaseDilatedAt P a
            (Int.floor (X / (a : ℝ)))).coeff j) ≤ B := by
    intro a haGood
    have haS := (Finset.mem_filter.mp haGood).1
    have hgood := (Finset.mem_filter.mp haGood).2
    have habounds := hSbounds a haS
    have haA₀ := hSA₀ a haS
    have haReal : 0 < (a : ℝ) := lt_trans hApos habounds.1
    have ha : 0 < a := by exact_mod_cast haReal
    have hlocal := typeI2_local_scale_bounds X H A₀ (a : ℝ)
      hXpos hHX hA₀pos haReal haA₀ hglobal16
    have haOne : 1 ≤ a := by omega
    have haOneReal : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast haOne
    have hXaUpper : X / (a : ℝ) ≤ X := by
      apply (div_le_iff₀ haReal).2
      calc
        X = X * 1 := by ring
        _ ≤ X * (a : ℝ) := mul_le_mul_of_nonneg_left haOneReal hXpos.le
    have hlogXaPos : 0 < Real.log (X / (a : ℝ)) :=
      Real.log_pos (by linarith [hlocal.1])
    have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
    have hlogMono : Real.log (X / (a : ℝ)) ≤ Real.log X :=
      Real.log_le_log (div_pos hXpos haReal) hXaUpper
    have hinvLog : (Real.log X)⁻¹ ≤
        (Real.log (X / (a : ℝ)))⁻¹ :=
      (inv_le_inv₀ hlogXpos hlogXaPos).2 hlogMono
    have hκlog : κ < (Real.log (X / (a : ℝ)))⁻¹ :=
      lt_of_lt_of_le (lt_of_le_of_lt hκleδ hδlog) hinvLog
    have hκsmall : κ < min (1 / 2)
        ((Real.log (X / (a : ℝ)))⁻¹) := lt_min hκhalf hκlog
    have hMupper : typeIDyadicScale kM ≤
        2 * Real.sqrt (X / (a : ℝ)) := by
      simpa [A, M, N] using
        typeI2_oriented_inner_scale_le A M N X (a : ℝ)
          hAhalf hMpos (by simpa [M, N] using hMN)
          (by simpa [A, M, N] using hprod) haReal habounds.2
    have hHdivA : H / (a : ℝ) ≤ H / A := by
      apply (div_le_div_iff₀ haReal hApos).2
      exact mul_le_mul_of_nonneg_left habounds.1.le hHpos.le
    have hlargeLocal : κ * (H / (a : ℝ)) ≤ ‖inner a‖ :=
      (mul_le_mul_of_nonneg_left hHdivA hκpos.le).trans hgood
    have hqK : (q : ℝ) ≤ κ⁻¹ := hqbound.trans hδinvK
    have hTV₁K : complexPositiveIntegerResidueVariation β₁ q hq ≤
        ENNReal.ofReal (κ⁻¹) :=
      hTV₁.trans (ENNReal.ofReal_le_ofReal hδinvK)
    have hTV₂K : complexPositiveIntegerResidueVariation
        (intervalWeightRestriction
          (Set.Ioc (typeIDyadicScale kN) (2 * typeIDyadicScale kN)) β₂)
        q hq ≤ ENNReal.ofReal (κ⁻¹) :=
      typeI2_intervalWeightVariation_le_parameter β₂ q hq δ κ kN
        hTV₂ hthreeδinvK
    have hpre := typeI2_selected_inner_preliminary_inverse hd
      X H κ a kM kN ha hXpos hHpos.le hHX hlocal.1 hlocal.2.1
      (by linarith [hlocal.2.2]) hMupper hκpos hκsmall q (by omega)
      hqK β₁ β₂ hTV₁K hTV₂K P hP (by
        simpa [inner] using hlargeLocal)
    rcases hpre with hshort | ⟨r, hr, hrB, hmono⟩
    · have hBnonneg : 0 ≤ typeI2J d κ⁻¹ := by
        linarith [typeI2J_ge_sixteen d κ⁻¹ (inv_nonneg.mpr hκpos.le)]
      have hlocalLong := typeI2_local_budget_length X H A₀ (a : ℝ)
        (typeI2J d κ⁻¹) (typeI2Bound d δ⁻¹) hXpos hA₀pos
        haReal haA₀ hBnonneg (by simpa [hκinv, B] using hBfinal) hlength
      exact False.elim (not_lt_of_ge hshort hlocalLong)
    · refine ⟨r, hr, ?_, ?_⟩
      · simpa [B, hκinv] using hrB
      · intro j hj hjd
        simpa [B, hκinv] using hmono j hj hjd
  have hSgoodNonempty : Sgood.Nonempty := by
    have hcardPos : 0 < (Sgood.card : ℝ) :=
      lt_of_lt_of_le (mul_pos hηpos hApos) hSgoodCard
    have hcardPosNat : 0 < Sgood.card := by exact_mod_cast hcardPos
    exact Finset.card_pos.mp hcardPosNat
  have hAleA₀ : A ≤ A₀ := by
    obtain ⟨a, haGood⟩ := hSgoodNonempty
    have haS : a ∈ S := (Finset.mem_filter.mp haGood).1
    have habounds := hSgoodbounds a haGood
    have haA₀ := hSA₀ a haS
    linarith
  have hconcat := concatenateDilatedPhases hd hAhalf hH hB1 hηpos hηhalf
    P hP Sgood hSgoodbounds hSgoodCard hdata
  rcases hconcat with hshort | ⟨r, hr, hrV, hmono⟩
  · have hcanonicalShort :
        H ≤ inverseBoundV d
          (typeI2J d (1024 * δ⁻¹ ^ 5)) (typeI2Density δ⁻¹) * A := by
      simpa [B, hηinv] using hshort
    have hcanonicalLong := typeI2_dilationShortBranch_excluded
      d δ X H A₀ A hδ hA₀pos hApos hAleA₀
      hA₀X hlength
    exact False.elim (not_lt_of_ge hcanonicalShort hcanonicalLong)
  · have hVle : inverseBoundV d B η⁻¹ ≤ typeI2Bound d δ⁻¹ := by
      simpa [B, hηinv] using hdom.2
    have hrReal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hVnonneg : 0 ≤ inverseBoundV d B η⁻¹ := by
      linarith [hrV]
    have hEVle : (inverseBoundEValue d : ℝ) *
        inverseBoundV d B η⁻¹ ≤ typeI2Bound d δ⁻¹ := by
      have hE0 : 0 ≤ (inverseBoundEValue d : ℝ) := by positivity
      rw [typeI2Bound_eval, ← typeI2Density_eval]
      rw [← hηinv]
      change (inverseBoundEValue d : ℝ) * inverseBoundV d B η⁻¹ ≤
        (inverseBoundEValue d : ℝ) *
          (16 + B + inverseBoundV d B η⁻¹)
      apply mul_le_mul_of_nonneg_left _ hE0
      linarith [hB16]
    let coeff : ℕ → ℝ := fun j =>
      (phaseCenteredAt P (Int.floor X)).coeff j
    have hexp := phaseCenteredAt_monomial_expansion P hP (Int.floor X)
    have hmonoFin : ∀ j ∈ Finset.Icc 1 d,
        H ^ j * realDistanceToIntegers ((r : ℝ) * coeff j) ≤
          inverseBoundV d B η⁻¹ := by
      intro j hj
      exact hmono j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
    have hbin := monomialToBinomialControl d hd (Int.floor X) H hH
      P coeff (by simpa [coeff] using hexp) r hr
      (inverseBoundV d B η⁻¹) hmonoFin
    exact ⟨r, hr, hrV.trans hVle, hbin.trans hEVle⟩

/-- Scalar Type-I₂ inverse estimate with the exact approved final budget
and the paper's binomial coefficient seminorm. -/
theorem typeI2Inverse
    (d : ℕ) (hd : 1 ≤ d) (X H δ A_I2 : ℝ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hδ : 0 < δ)
    (hδsmall : δ < min (1 / 2) ((Real.log X)⁻¹))
    (f : ComplexPositiveIntegerFunction)
    (hf : typeI2Function δ A_I2 f)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hlarge : δ * H ≤ typeIScalarPhaseCorrelation f P X H) :
    H ≤ typeI2Bound d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) *
        Real.rpow A_I2 (2 / 3 : ℝ) ∨
      ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ typeI2Bound d δ⁻¹ ∧
        polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
          (Int.floor X) H ≤ typeI2Bound d δ⁻¹ := by
  classical
  rcases hf with ⟨_, _, hAI, α, β₁, β₂, q, hq, hconv, hsupp,
    hMoment, hqone, hqbound, hTV₁, hTV₂⟩
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < H := by linarith
  have hHnonneg : 0 ≤ H := hHpos.le
  have hAIpos : 0 < A_I2 := by linarith
  have hδhalf : δ < 1 / 2 :=
    lt_of_lt_of_le hδsmall (min_le_left _ _)
  have hδlog : δ < (Real.log X)⁻¹ :=
    lt_of_lt_of_le hδsmall (min_le_right _ _)
  have hδinv : 2 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hδ).2
    nlinarith
  by_cases hshort : H ≤
      typeI2Bound d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) *
        Real.rpow A_I2 (2 / 3 : ℝ)
  · exact Or.inl hshort
  · have hlength :
        typeI2Bound d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) *
          Real.rpow A_I2 (2 / 3 : ℝ) < H := lt_of_not_ge hshort
    have hAIltX : A_I2 < X := by
      by_contra hnot
      have hXleAI : X ≤ A_I2 := le_of_not_gt hnot
      have hrootMono : Real.rpow X (2 / 3 : ℝ) ≤
          Real.rpow A_I2 (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hXpos.le hXleAI (by norm_num)
      have hXsplit : X = Real.rpow X (1 / 3 : ℝ) *
          Real.rpow X (2 / 3 : ℝ) := by
        calc
          X = Real.rpow X (1 : ℝ) := (Real.rpow_one X).symm
          _ = Real.rpow X ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by norm_num
          _ = _ := Real.rpow_add hXpos _ _
      have hscale : X ≤ Real.rpow X (1 / 3 : ℝ) *
          Real.rpow A_I2 (2 / 3 : ℝ) := by
        calc
          X = Real.rpow X (1 / 3 : ℝ) *
              Real.rpow X (2 / 3 : ℝ) := hXsplit
          _ ≤ Real.rpow X (1 / 3 : ℝ) *
              Real.rpow A_I2 (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hrootMono
              (Real.rpow_nonneg hXpos.le _)
      have hfinalOne : 1 ≤ typeI2Bound d δ⁻¹ := by
        linarith [typeI2Bound_ge_sixteen d hd δ⁻¹ hδinv]
      have hscaleNonneg : 0 ≤ Real.rpow X (1 / 3 : ℝ) *
          Real.rpow A_I2 (2 / 3 : ℝ) := by
        exact mul_nonneg (Real.rpow_nonneg hXpos.le _)
          (Real.rpow_nonneg hAIpos.le _)
      have hcontr : H ≤
          typeI2Bound d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) *
            Real.rpow A_I2 (2 / 3 : ℝ) := by
        calc
          H ≤ X := hHX
          _ ≤ Real.rpow X (1 / 3 : ℝ) *
              Real.rpow A_I2 (2 / 3 : ℝ) := hscale
          _ = 1 * (Real.rpow X (1 / 3 : ℝ) *
              Real.rpow A_I2 (2 / 3 : ℝ)) := by ring
          _ ≤ typeI2Bound d δ⁻¹ *
              (Real.rpow X (1 / 3 : ℝ) *
                Real.rpow A_I2 (2 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hfinalOne hscaleNonneg
          _ = typeI2Bound d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) *
              Real.rpow A_I2 (2 / 3 : ℝ) := by ring
      exact (not_lt_of_ge hcontr hlength).elim
    have hlargeSum : δ * H ≤
        ‖typeIScalarPhaseSum
          (complexPositiveDirichletConvolution
            (complexPositiveDirichletConvolution α β₁) β₂) P X H‖ := by
      simpa [typeIScalarPhaseCorrelation, hconv] using hlarge
    have hlargeTriple : δ * H ≤
        ‖∑ a ∈ Finset.Icc 1 (Nat.floor X),
          ∑ m ∈ Finset.Icc 1 (Nat.floor (X + H)),
            ∑ n ∈ Finset.Icc 1 (Nat.floor (X + H)),
              typeI2FactorizedTerm α β₁ β₂ P X H a m n‖ := by
      rw [← typeI2_triple_sum_eq_floorX α β₁ β₂ P X H A_I2
        hHnonneg hAIltX hsupp]
      rw [← typeI2ScalarPhaseSum_eq_triple_sum]
      exact hlargeSum
    have hcardA := typeIDyadicIndices_card_bound X δ hX hδ hδlog
    have hcardInner := typeI2InnerDyadicIndices_card_bound
      X H δ hX hHnonneg hHX hδ hδlog
    obtain ⟨kA, hkA, kM, hkM, kN, hkN, hblock⟩ :=
      exists_typeI2_dyadic_triple (Nat.floor X)
        (Nat.floor (X + H)) (Nat.floor (X + H)) δ H hδ hHpos
        hcardA hcardInner hcardInner
        (typeI2FactorizedTerm α β₁ β₂ P X H) hlargeTriple
    have hblockNe :
        (∑ a ∈ typeIDyadicBlock (Nat.floor X) kA,
          ∑ m ∈ typeIDyadicBlock (Nat.floor (X + H)) kM,
            ∑ n ∈ typeIDyadicBlock (Nat.floor (X + H)) kN,
              typeI2FactorizedTerm α β₁ β₂ P X H a m n) ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hblock
      have hpositive : 0 < (δ ^ 4 / 256) * H := by positivity
      linarith
    have hprod := typeI2_nonzero_selected_block_scales_mul_lt
      α β₁ β₂ P X H (Nat.floor X) (Nat.floor (X + H))
      (Nat.floor (X + H)) kA kM kN hHX hblockNe
    have hweighted := hblock
    rw [typeI2_selected_block_eq_weighted_inner] at hweighted
    have hsymmetric : (δ ^ 4 / 256) * H ≤
        ‖∑ a ∈ typeIDyadicBlock (Nat.floor X) kA,
          complexPositiveIntegerNatExtension α a *
            typeI2SymmetricInner β₁ β₂ P X H
              (typeIDyadicBlock (Nat.floor (X + H)) kM)
              (typeIDyadicBlock (Nat.floor (X + H)) kN) a‖ := by
      calc
        (δ ^ 4 / 256) * H ≤
            ‖∑ a ∈ typeIDyadicBlock (Nat.floor X) kA,
              complexPositiveIntegerNatExtension α a *
                typeI2SelectedInner β₁ β₂ P X H
                  (typeIDyadicBlock (Nat.floor (X + H)) kM)
                  (typeIDyadicBlock (Nat.floor (X + H)) kN) a‖ := hweighted
        _ = ‖∑ a ∈ typeIDyadicBlock (Nat.floor X) kA,
              complexPositiveIntegerNatExtension α a *
                typeI2SymmetricInner β₁ β₂ P X H
                  (typeIDyadicBlock (Nat.floor (X + H)) kM)
                  (typeIDyadicBlock (Nat.floor (X + H)) kN) a‖ := by
          congr 1
          apply Finset.sum_congr rfl
          intro a ha
          rw [typeI2SelectedInner_eq_symmetric]
    by_cases hMN : typeIDyadicScale kM ≤ typeIDyadicScale kN
    · exact Or.inr (typeI2_oriented_block_inverse hd X H δ A_I2 hX hH hHX
        hδ hδsmall α β₁ β₂ hsupp hMoment q hq hqbound hTV₁ hTV₂
        kA kM kN hMN hprod P hP hsymmetric hAI hAIltX hlength)
    · have hNM : typeIDyadicScale kN ≤ typeIDyadicScale kM :=
        le_of_not_ge hMN
      have hprodSwap : typeIDyadicScale kA * typeIDyadicScale kN *
          typeIDyadicScale kM < 2 * X := by
        nlinarith [hprod]
      have hsymmetricSwap : (δ ^ 4 / 256) * H ≤
          ‖∑ a ∈ typeIDyadicBlock (Nat.floor X) kA,
            complexPositiveIntegerNatExtension α a *
              typeI2SymmetricInner β₂ β₁ P X H
                (typeIDyadicBlock (Nat.floor (X + H)) kN)
                (typeIDyadicBlock (Nat.floor (X + H)) kM) a‖ := by
        calc
          (δ ^ 4 / 256) * H ≤
              ‖∑ a ∈ typeIDyadicBlock (Nat.floor X) kA,
                complexPositiveIntegerNatExtension α a *
                  typeI2SymmetricInner β₁ β₂ P X H
                    (typeIDyadicBlock (Nat.floor (X + H)) kM)
                    (typeIDyadicBlock (Nat.floor (X + H)) kN) a‖ := hsymmetric
          _ = ‖∑ a ∈ typeIDyadicBlock (Nat.floor X) kA,
                complexPositiveIntegerNatExtension α a *
                  typeI2SymmetricInner β₂ β₁ P X H
                    (typeIDyadicBlock (Nat.floor (X + H)) kN)
                    (typeIDyadicBlock (Nat.floor (X + H)) kM) a‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro a ha
            rw [typeI2SymmetricInner_swap]
      exact Or.inr (typeI2_oriented_block_inverse hd X H δ A_I2 hX hH hHX
        hδ hδsmall α β₂ β₁ hsupp hMoment q hq hqbound hTV₂ hTV₁
        kA kN kM hNM hprodSwap P hP hsymmetricSwap hAI hAIltX hlength)

end

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.complexPositiveIntegerNatExtension_convolution
#print axioms FractionalPrimes.Literature.Polynomial.typeI2ScalarPhaseSum_eq_triple_factorized
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_selected_block_eq_weighted_inner
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_nonzero_selected_block_scales_mul_lt
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_oriented_inner_scale_le
#print axioms FractionalPrimes.Literature.Polynomial.typeI2SelectedInner_eq_symmetric
#print axioms FractionalPrimes.Literature.Polynomial.typeI2SymmetricInner_swap
#print axioms FractionalPrimes.Literature.Polynomial.typeI2SymmetricInner_eq_dilated_phase_sum
#print axioms FractionalPrimes.Literature.Polynomial.exists_typeI2_selected_lattice_representation
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_intervalWeightVariation_le_parameter
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_lattice_correlation_norm_le
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_many_large_inner_correlations
#print axioms FractionalPrimes.Literature.Polynomial.typeI2Bound_ge_sixteen
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_finalBudget_dominates
#print axioms FractionalPrimes.Literature.Polynomial.typeI2Kappa_inv
#print axioms FractionalPrimes.Literature.Polynomial.typeI2Eta_inv
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_outer_sum_restrict_support
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_local_budget_length
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_local_scale_bounds
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_oriented_block_inverse
#print axioms FractionalPrimes.Literature.Polynomial.typeI2Inverse
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_selected_inner_preliminary_inverse
#print axioms FractionalPrimes.Literature.Polynomial.sum_typeIDyadicBlocks
#print axioms FractionalPrimes.Literature.Polynomial.exists_typeI2_dyadic_triple
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_block_inner_square_sum_lower
