module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothFactorMass
public import FractionalPrimes.Literature.Twisted.SelectedSmoothGroupScale
public import FractionalPrimes.Literature.Twisted.WideSupportConvolutionTransfer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Finite scale and mass assembly for a selected smooth group

This file isolates the finite product substitution in `lda:small-group`.
The selected factor's scale cancels the denominator in the product of the
other-factor mass bounds, and the source dyadic range converts the component
scale to the block scale.  Local cancellation remains an explicit input to
`WideSupportConvolutionTransfer`.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The inverse-square-root scale of the selected factor times the absolute
mass product of the remaining at most twenty factors is bounded by the source
dyadic block scale.  The exponent range is the exact source range
`-k ≤ h < k`; `k ≤ 20` gives the loss `2^10` after taking square roots. -/
theorem smoothGroupSelectedMassScale
    {k : ℕ} (hk : k ≤ 20) (selected : Fin k) (h : ℤ)
    (N mass : Fin k → ℝ) (L : ℝ)
    (hN : ∀ i, 0 < N i)
    (hmass : ∀ i, 0 ≤ mass i)
    (hmassBound : ∀ i, i ≠ selected → mass i ≤ 5 * Real.sqrt (N i))
    (hL : L = (2 : ℝ) ^ h * (∏ i : Fin k, N i))
    (hh : -(k : ℤ) ≤ h ∧ h < (k : ℤ)) :
    Real.sqrt (N selected) *
        (∏ i ∈ Finset.univ.erase selected, mass i) ≤
      (2 : ℝ) ^ 10 * 5 ^ 19 * Real.sqrt L := by
  have hlow : -(20 : ℤ) ≤ h := by omega
  have hpowLower : (2 : ℝ) ^ (-(20 : ℤ)) ≤ (2 : ℝ) ^ h :=
    zpow_le_zpow_right₀ (by norm_num) hlow
  let P : ℝ := ∏ i : Fin k, N i
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun i hi => hN i
  have hNselected : 0 < N selected := hN selected
  have hMassProduct := smoothOtherFactorMassProduct hk selected N mass hN
    hmass hmassBound
  have hcancel :
      Real.sqrt (N selected) * Real.sqrt (P / N selected) = Real.sqrt P := by
    calc
      Real.sqrt (N selected) * Real.sqrt (P / N selected) =
          Real.sqrt (N selected * (P / N selected)) :=
        (Real.sqrt_mul hNselected.le (P / N selected)).symm
      _ = Real.sqrt P := by
        congr 1
        dsimp [P]
        field_simp [ne_of_gt hNselected]
  have hblockLower : (2 : ℝ) ^ (-(20 : ℤ)) * P ≤ L := by
    have hmul := mul_le_mul_of_nonneg_right hpowLower hPpos.le
    simpa [hL, P] using hmul
  have hPLe : P ≤ (2 : ℝ) ^ 20 * L := by
    have hpow : (2 : ℝ) ^ 20 * (2 : ℝ) ^ (-(20 : ℤ)) = 1 := by
      norm_num
    calc
      P = (2 : ℝ) ^ 20 * ((2 : ℝ) ^ (-(20 : ℤ)) * P) := by
        calc
          P = ((2 : ℝ) ^ 20 * (2 : ℝ) ^ (-(20 : ℤ))) * P := by
            rw [hpow]
            ring
          _ = (2 : ℝ) ^ 20 * ((2 : ℝ) ^ (-(20 : ℤ)) * P) := by ring
      _ ≤ (2 : ℝ) ^ 20 * L :=
        mul_le_mul_of_nonneg_left hblockLower (by positivity)
  have hroot : Real.sqrt P ≤ (2 : ℝ) ^ 10 * Real.sqrt L := by
    have hsqrt := Real.sqrt_le_sqrt hPLe
    calc
      Real.sqrt P ≤ Real.sqrt ((2 : ℝ) ^ 20 * L) := hsqrt
      _ = Real.sqrt (((2 : ℝ) ^ 10) ^ 2 * L) := by
        congr 1
        norm_num [pow_mul]
      _ = Real.sqrt (((2 : ℝ) ^ 10) ^ 2) * Real.sqrt L :=
        Real.sqrt_mul (sq_nonneg ((2 : ℝ) ^ 10)) L
      _ = (2 : ℝ) ^ 10 * Real.sqrt L := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hproduct :=
    mul_le_mul_of_nonneg_left hMassProduct (Real.sqrt_nonneg (N selected))
  calc
    Real.sqrt (N selected) *
        (∏ i ∈ Finset.univ.erase selected, mass i) ≤
      Real.sqrt (N selected) *
        (5 ^ 19 * Real.sqrt (P / N selected)) := hproduct
    _ = 5 ^ 19 * Real.sqrt P := by
      calc
        _ = 5 ^ 19 *
            (Real.sqrt (N selected) *
              Real.sqrt ((∏ i : Fin k, N i) / N selected)) := by ring
        _ = 5 ^ 19 * Real.sqrt P := by
          rw [show Real.sqrt (N selected) *
              Real.sqrt ((∏ i : Fin k, N i) / N selected) = Real.sqrt P by
                simpa [P] using hcancel]
    _ ≤ 5 ^ 19 * ((2 : ℝ) ^ 10 * Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (2 : ℝ) ^ 10 * 5 ^ 19 * Real.sqrt L := by ring

/-- Finite convolution assembly for one selected smooth factor.  The only
factor cancellation input is the explicit dyadic short-interval estimate
`hShort`; the other factors enter through their source absolute-mass bounds.
Combining the two dyadic pieces with the selected-mass product costs the exact
source factor `2^11 * 5^19` on the block scale. -/
theorem smoothGroupWideSupportFiniteTransfer
    {k : ℕ} (hk : k ≤ 20) (selected : Fin k) (h : ℤ)
    (N : Fin k → ℝ) (L ε x y : ℝ)
    (S : Fin k → Finset ℕ) (a : Fin k → ℕ → ℂ)
    (hN : ∀ i, 0 < N i)
    (hL : L = (2 : ℝ) ^ h * (∏ i : Fin k, N i))
    (hh : -(k : ℤ) ≤ h ∧ h < (k : ℤ))
    (hε : 0 ≤ ε) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hSelected : S selected =
      FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
          (N selected / 2) ∪
        FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
          (N selected))
    (hPositive : ∀ i n, n ∈ S i → 0 < n)
    (hOtherMass : ∀ j ∈ Finset.univ.erase selected,
      (∑ n ∈ S j, ‖a j n‖) ≤ 5 * Real.sqrt (N j))
    (hShort : ∀ M : ℝ, (M = N selected / 2 ∨ M = N selected) →
      ∀ u v : ℝ, 0 ≤ u →
        Set.Ioc u v ⊆ Set.Ioc M (2 * M) →
        ‖∑ n ∈
            FractionalPrimes.Literature.Twisted.factorExtractionRealInterval
              u v, a selected n‖ ≤ ε * Real.sqrt M) :
    ‖∑ m ∈ (Fintype.piFinset S).filter
        (fun m => x < (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ∧
          (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ≤ y),
        ∏ i : Fin k, a i (m i)‖ ≤
      (2 : ℝ) ^ 11 * 5 ^ 19 * ε * Real.sqrt L := by
  let mass : Fin k → ℝ := fun i => ∑ n ∈ S i, ‖a i n‖
  have hmassNonneg : ∀ i, 0 ≤ mass i := by
    intro i
    dsimp [mass]
    apply Finset.sum_nonneg
    intro n hn
    exact norm_nonneg _
  have hmassBound : ∀ i, i ≠ selected →
      mass i ≤ 5 * Real.sqrt (N i) := by
    intro i hi
    exact hOtherMass i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  have hscale := smoothGroupSelectedMassScale hk selected h N mass L hN
    hmassNonneg hmassBound hL hh
  have hfinite :=
    FractionalPrimes.Literature.Twisted.wideSupportFiniteConvolutionSmallFactor
      selected (N selected) ε x y S a mass (hN selected) hε hx hxy
      hSelected hPositive (by
        intro j hj
        rfl) hShort
  have hscaleMul :=
    mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * ε by positivity)
  calc
    ‖∑ m ∈ (Fintype.piFinset S).filter
        (fun m => x < (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ∧
          (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ≤ y),
        ∏ i : Fin k, a i (m i)‖ ≤
      2 * ε * Real.sqrt (N selected) *
        (∏ j ∈ Finset.univ.erase selected, mass j) := hfinite
    _ = 2 * ε *
        (Real.sqrt (N selected) *
          (∏ j ∈ Finset.univ.erase selected, mass j)) := by ring
    _ ≤ 2 * ε *
        ((2 : ℝ) ^ 10 * 5 ^ 19 * Real.sqrt L) := hscaleMul
    _ = (2 : ℝ) ^ 11 * 5 ^ 19 * ε * Real.sqrt L := by ring

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothGroupSelectedMassScale
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothGroupWideSupportFiniteTransfer
