module

public import FractionalPrimes.Literature.Multiplier.DyadicKernelPointwise
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.GroupWithZero.Indicator

/-!
# High-frequency decay for dyadic multiplier kernels

This module continues the checked compact-support and product-rule estimates in
`DyadicKernelPointwise`, using Mathlib's Fourier-transform derivative identity
for the two integrations by parts in the approved dyadic-kernel lemma.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open MeasureTheory
open scoped FourierTransform

noncomputable section

theorem dyadicKernelPiece_x_sq_bound {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) (hx : x ≠ 0) :
    ‖dyadicKernelPiece h j x‖ ≤ 45 * B * D /
      (dyadicScale j * |x| ^ 2) := by
  let f : ℝ → ℂ := dyadicSymbolPiece h j
  have hfcont : ContDiff ℝ 2 f := dyadicSymbolPiece_contDiff h j
  have hfint : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) →
      Integrable (iteratedDeriv n f) := by
    intro n hn
    have hn' : n ≤ 2 := by exact_mod_cast hn
    simpa [f] using dyadicSymbolPiece_iteratedDeriv_integrable h j n hn'
  have hFourierDeriv :=
    Real.fourier_iteratedDeriv (N := 2) hfcont hfint (n := 2) (by norm_num)
  have hFourierIdentity := congrFun hFourierDeriv (-x)
  have hFourierL1 :
      ‖𝓕 (iteratedDeriv 2 f) (-x)‖ ≤
        ∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖ := by
    change ‖VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ ℝ) (iteratedDeriv 2 f) (-x)‖ ≤ _
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv 2 f) (-x)
  have hL1 := dyadicSymbolPiece_iteratedDeriv_two_l1_le h j
  have hKernelFourier : dyadicKernelPiece h j x = 𝓕 f (-x) := by
    simpa [f] using dyadicKernelPiece_eq_fourier_neg h j x
  let c : ℂ := (2 * (Real.pi : ℂ) * Complex.I * (-x : ℂ)) ^ 2
  have hc_norm : ‖c‖ = (2 * Real.pi * |x|) ^ 2 := by
    dsimp [c]
    simp [norm_pow, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_neg]
  have hc_pos : 0 < ‖c‖ := by
    rw [hc_norm]
    positivity
  have hnorm_relation :
      ‖𝓕 (iteratedDeriv 2 f) (-x)‖ = ‖c‖ * ‖𝓕 f (-x)‖ := by
    simpa [f, c] using congrArg (fun z : ℂ => ‖z‖) hFourierIdentity
  have hFourierBound : ‖𝓕 f (-x)‖ ≤
      (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / ‖c‖ := by
    apply (le_div_iff₀ hc_pos).2
    rw [mul_comm, ← hnorm_relation]
    exact hFourierL1
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hc_lower : 4 * |x| ^ 2 ≤ ‖c‖ := by
    rw [hc_norm]
    have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hbase : 2 * |x| ≤ 2 * Real.pi * |x| := by nlinarith
    have hbase_sum : 0 ≤ 2 * |x| + (2 * Real.pi * |x|) := by positivity
    have hsquare := mul_nonneg (sub_nonneg.mpr hbase) hbase_sum
    nlinarith [hsquare]
  have hden_pos : 0 < 4 * |x| ^ 2 := by positivity
  have hL1_nonneg : 0 ≤ ∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hFourierBound' : ‖𝓕 f (-x)‖ ≤
      (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / (4 * |x| ^ 2) := by
    calc
      ‖𝓕 f (-x)‖ ≤
          (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / ‖c‖ := hFourierBound
      _ ≤ (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / (4 * |x| ^ 2) :=
        (div_le_div_iff₀ hc_pos hden_pos).2 (by
          exact mul_le_mul_of_nonneg_left hc_lower hL1_nonneg)
  have hL1compare :
      (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / (4 * |x| ^ 2) ≤
        (357 * B * D / (2 * dyadicScale j)) / (4 * |x| ^ 2) :=
    div_le_div_of_nonneg_right hL1 (by positivity)
  have hxidentity :
      (357 * B * D / (2 * dyadicScale j)) / (4 * |x| ^ 2) =
        (357 * B * D) / (8 * dyadicScale j * |x| ^ 2) := by
    field_simp
    ring
  have hB : 0 ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
  have hBD : 0 ≤ B * D := mul_nonneg hB h.D_nonneg
  have hconstant : 357 * B * D / (8 * dyadicScale j * |x| ^ 2) ≤
      45 * B * D / (dyadicScale j * |x| ^ 2) := by
    have hden : 0 < dyadicScale j * |x| ^ 2 :=
      mul_pos (dyadicScale_pos j) (sq_pos_of_pos hxabs)
    have hden8 : 0 < 8 * dyadicScale j * |x| ^ 2 :=
      mul_pos (mul_pos (by norm_num) (dyadicScale_pos j))
        (sq_pos_of_pos hxabs)
    apply (div_le_div_iff₀ hden8 hden).2
    nlinarith [mul_nonneg hBD hden.le]
  calc
    ‖dyadicKernelPiece h j x‖ = ‖𝓕 f (-x)‖ := by rw [hKernelFourier]
    _ ≤ (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / (4 * |x| ^ 2) := hFourierBound'
    _ ≤ (357 * B * D / (2 * dyadicScale j)) / (4 * |x| ^ 2) := hL1compare
    _ = 357 * B * D / (8 * dyadicScale j * |x| ^ 2) := hxidentity
    _ ≤ 45 * B * D / (dyadicScale j * |x| ^ 2) := hconstant

/-- The symbol obtained by differentiating the real inverse-transform kernel.
This is exactly `2πi ξ m_j(ξ)` from the approved proof. -/
def dyadicKernelDerivativeSymbol {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) *
    ((ξ : ℂ) * dyadicSymbolPiece h j ξ)

theorem dyadicKernelDerivativeSymbol_contDiff {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    ContDiff ℝ 2 (dyadicKernelDerivativeSymbol h j) := by
  have hf := dyadicSymbolPiece_contDiff h j
  have hid : ContDiff ℝ 2 (fun ξ : ℝ => (ξ : ℂ)) := by
    change ContDiff ℝ 2 (fun ξ : ℝ => Complex.ofRealCLM ξ)
    exact Complex.ofRealCLM.contDiff.comp contDiff_id
  unfold dyadicKernelDerivativeSymbol
  exact contDiff_const.mul (hid.mul hf)

theorem dyadicKernelDerivativeSymbol_hasCompactSupport {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    HasCompactSupport (dyadicKernelDerivativeSymbol h j) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  have hinner : Function.support
      (fun ξ : ℝ => (ξ : ℂ) * dyadicSymbolPiece h j ξ) ⊆
      Function.support (dyadicSymbolPiece h j) := Function.support_mul_subset_right _ _
  have houter : Function.support (dyadicKernelDerivativeSymbol h j) ⊆
      Function.support (fun ξ : ℝ => (ξ : ℂ) * dyadicSymbolPiece h j ξ) := by
    exact Function.support_mul_subset_right _ _
  exact houter.trans (hinner.trans (dyadicSymbolPiece_support_Icc h j))

theorem dyadicKernelDerivativeSymbol_integrable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    Integrable (dyadicKernelDerivativeSymbol h j) :=
  (dyadicKernelDerivativeSymbol_contDiff h j).continuous.integrable_of_hasCompactSupport
    (dyadicKernelDerivativeSymbol_hasCompactSupport h j)

theorem dyadicKernelDerivativeSymbol_iteratedDeriv_two_formula
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (j : ℕ) (ξ : ℝ) :
    iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (2 * deriv (dyadicSymbolPiece h j) ξ +
          (ξ : ℂ) * iteratedDeriv 2 (dyadicSymbolPiece h j) ξ) := by
  have hf := dyadicSymbolPiece_contDiff h j
  have hid : ContDiff ℝ 2 (fun y : ℝ => (y : ℂ)) := by
    change ContDiff ℝ 2 (fun y : ℝ => Complex.ofRealCLM y)
    exact Complex.ofRealCLM.contDiff.comp contDiff_id
  have hprod := iteratedDeriv_mul (n := 2) (x := ξ)
    hid.contDiffAt
    hf.contDiffAt
  have hcastDeriv : deriv (fun y : ℝ => (y : ℂ)) = fun _ => 1 := by
    funext y
    exact (Complex.ofRealCLM.hasFDerivAt (x := y)).hasDerivAt.deriv
  have hcastSecond : iteratedDeriv 2 (fun y : ℝ => (y : ℂ)) ξ = 0 := by
    simp [iteratedDeriv_succ, iteratedDeriv_one, hcastDeriv]
  have hlinear : iteratedDeriv 2
      (fun y : ℝ => (y : ℂ) * dyadicSymbolPiece h j y) ξ =
      2 * deriv (dyadicSymbolPiece h j) ξ +
        (ξ : ℂ) * iteratedDeriv 2 (dyadicSymbolPiece h j) ξ := by
    change iteratedDeriv 2
      ((fun y : ℝ => (y : ℂ)) * dyadicSymbolPiece h j) ξ = _
    rw [hprod]
    simp [Finset.sum_range_succ, hcastDeriv, hcastSecond]
    ring
  rw [show dyadicKernelDerivativeSymbol h j = fun y : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I) *
        ((y : ℂ) * dyadicSymbolPiece h j y) by rfl]
  calc
    iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ =
        iteratedDeriv 2 (fun y : ℝ =>
          (2 * (Real.pi : ℂ) * Complex.I) *
            ((y : ℂ) * dyadicSymbolPiece h j y)) ξ := rfl
    _ = (2 * (Real.pi : ℂ) * Complex.I) *
        iteratedDeriv 2
          (fun y : ℝ => (y : ℂ) * dyadicSymbolPiece h j y) ξ :=
      iteratedDeriv_const_mul _
        (((Complex.ofRealCLM.contDiff.comp contDiff_id).mul hf).contDiffAt)
    _ = _ := congrArg ((2 * (Real.pi : ℂ) * Complex.I) * ·) hlinear

theorem dyadicKernelDerivativeSymbol_iteratedDeriv_two_norm_le
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (j : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ‖ ≤
      1018 * B * D / dyadicScale j := by
  have ht := dyadicScale_pos j
  have hB : 0 ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
  by_cases hξ : ξ ∈ dyadicClosedAnnulus j
  · obtain ⟨_, houter⟩ := hξ
    have hfirst := dyadicSymbolPiece_deriv_norm_le h j ξ
    have hsecond := dyadicSymbolPiece_iteratedDeriv_two_norm_le h j ξ
    have hxi : ‖(ξ : ℂ)‖ ≤ dyadicScale j / 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact houter
    have hc : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ ≤ 8 := by
      simp [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_lt_four]
    have hterm₁ : ‖(2 : ℂ) * deriv (dyadicSymbolPiece h j) ξ‖ ≤
        2 * (19 * B * D / dyadicScale j) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hfirst (by norm_num)
    have hterm₂ : ‖(ξ : ℂ) * iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖ ≤
        (dyadicScale j / 4) *
          (357 * B * D / dyadicScale j ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul hxi hsecond (by positivity) (by positivity)
    have hinside : ‖2 * deriv (dyadicSymbolPiece h j) ξ +
        (ξ : ℂ) * iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖ ≤
        2 * (19 * B * D / dyadicScale j) +
          (dyadicScale j / 4) * (357 * B * D / dyadicScale j ^ 2) := by
      calc
        _ ≤ ‖(2 : ℂ) * deriv (dyadicSymbolPiece h j) ξ‖ +
            ‖(ξ : ℂ) * iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hterm₁ hterm₂
    have hD : 0 ≤ D := h.D_nonneg
    calc
      ‖iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ‖ =
          ‖(2 * (Real.pi : ℂ) * Complex.I) *
            (2 * deriv (dyadicSymbolPiece h j) ξ +
              (ξ : ℂ) * iteratedDeriv 2 (dyadicSymbolPiece h j) ξ)‖ := by
                rw [dyadicKernelDerivativeSymbol_iteratedDeriv_two_formula]
      _ = ‖2 * (Real.pi : ℂ) * Complex.I‖ *
          ‖2 * deriv (dyadicSymbolPiece h j) ξ +
            (ξ : ℂ) * iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖ := norm_mul _ _
      _ ≤ 8 * (2 * (19 * B * D / dyadicScale j) +
            (dyadicScale j / 4) * (357 * B * D / dyadicScale j ^ 2)) := by
              calc
                _ ≤ 8 * ‖2 * deriv (dyadicSymbolPiece h j) ξ +
                    (ξ : ℂ) * iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖ :=
                      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
                _ ≤ _ := mul_le_mul_of_nonneg_left hinside (by norm_num)
      _ = 1018 * B * D / dyadicScale j := by
        field_simp [ne_of_gt ht]
        ring
  · have hts : ξ ∉ tsupport (dyadicKernelDerivativeSymbol h j) := by
      intro hts
      have hsub₁ : tsupport (fun y : ℝ =>
          (y : ℂ) * dyadicSymbolPiece h j y) ⊆
          tsupport (dyadicSymbolPiece h j) :=
        tsupport_mul_subset_right (f := fun y : ℝ => (y : ℂ))
          (g := dyadicSymbolPiece h j)
      have hsub₂ : tsupport (dyadicKernelDerivativeSymbol h j) ⊆
          tsupport (fun y : ℝ => (y : ℂ) * dyadicSymbolPiece h j y) := by
        change tsupport (fun y : ℝ =>
          (2 * (Real.pi : ℂ) * Complex.I) *
            ((y : ℂ) * dyadicSymbolPiece h j y)) ⊆ _
        exact tsupport_mul_subset_right
          (f := fun _ : ℝ => (2 * (Real.pi : ℂ) * Complex.I))
          (g := fun y : ℝ => (y : ℂ) * dyadicSymbolPiece h j y)
      exact hξ (dyadicSymbolPiece_tsupport_annulus h j (hsub₂.trans hsub₁ hts))
    have hderivts : ξ ∉ tsupport (deriv (dyadicKernelDerivativeSymbol h j)) := by
      intro hx
      exact hts (tsupport_deriv_subset hx)
    rw [show iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ =
        deriv (deriv (dyadicKernelDerivativeSymbol h j)) ξ by
          simp [iteratedDeriv_succ, iteratedDeriv_one],
      deriv_of_notMem_tsupport hderivts]
    have hnonneg : 0 ≤ 1018 * B * D / dyadicScale j := by
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) h.D_nonneg) ht.le
    simpa using hnonneg

theorem dyadicKernelDerivativeSymbol_support_Icc {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    Function.support (dyadicKernelDerivativeSymbol h j) ⊆
      Set.Icc (-(dyadicScale j / 4)) (dyadicScale j / 4) := by
  have hinner : Function.support
      (fun ξ : ℝ => (ξ : ℂ) * dyadicSymbolPiece h j ξ) ⊆
      Function.support (dyadicSymbolPiece h j) := Function.support_mul_subset_right _ _
  have houter : Function.support (dyadicKernelDerivativeSymbol h j) ⊆
      Function.support (fun ξ : ℝ => (ξ : ℂ) * dyadicSymbolPiece h j ξ) := by
    exact Function.support_mul_subset_right _ _
  exact houter.trans (hinner.trans (dyadicSymbolPiece_support_Icc h j))

theorem dyadicKernelDerivativeSymbol_iteratedDeriv_integrable
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (j n : ℕ) (hn : n ≤ 2) :
    Integrable (fun ξ : ℝ =>
      iteratedDeriv n (dyadicKernelDerivativeSymbol h j) ξ) := by
  have hcont := dyadicKernelDerivativeSymbol_contDiff h j
  have hcompact := dyadicKernelDerivativeSymbol_hasCompactSupport h j
  interval_cases n
  · simpa only [iteratedDeriv_zero] using hcont.continuous.integrable_of_hasCompactSupport hcompact
  · simpa only [iteratedDeriv_one] using
      (hcont.continuous_iteratedDeriv 1 (by norm_num)).integrable_of_hasCompactSupport
        (by simpa only [iteratedDeriv_one] using hcompact.deriv)
  · have hcont₂ : Continuous
        (fun ξ : ℝ => iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ) :=
      hcont.continuous_iteratedDeriv 2 (by norm_num)
    have hcompact₂ : HasCompactSupport
        (fun ξ : ℝ => iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ) := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        hcompact.deriv.deriv
    exact hcont₂.integrable_of_hasCompactSupport hcompact₂

def dyadicKernelWeightedInput {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ) : ℂ :=
  (ξ : ℂ) * dyadicSymbolPiece h j ξ

theorem dyadicKernelWeightedInput_contDiff {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    ContDiff ℝ 2 (dyadicKernelWeightedInput h j) := by
  change ContDiff ℝ 2
    (fun ξ : ℝ => (ξ : ℂ) * dyadicSymbolPiece h j ξ)
  have hcast : ContDiff ℝ 2 (fun ξ : ℝ => (ξ : ℂ)) := by
    change ContDiff ℝ 2 (fun ξ : ℝ => Complex.ofRealCLM ξ)
    exact Complex.ofRealCLM.contDiff.comp contDiff_id
  exact hcast.mul (dyadicSymbolPiece_contDiff h j)

theorem dyadicKernelWeightedInput_hasCompactSupport {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    HasCompactSupport (dyadicKernelWeightedInput h j) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  have hs : Function.support (dyadicKernelWeightedInput h j) ⊆
      Function.support (dyadicSymbolPiece h j) := by
    change Function.support
      (fun ξ : ℝ => (ξ : ℂ) * dyadicSymbolPiece h j ξ) ⊆ _
    exact Function.support_mul_subset_right _ _
  exact hs.trans (dyadicSymbolPiece_support_Icc h j)

theorem dyadicKernelWeightedInput_integrable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) : Integrable (dyadicKernelWeightedInput h j) :=
  (dyadicKernelWeightedInput_contDiff h j).continuous.integrable_of_hasCompactSupport
    (dyadicKernelWeightedInput_hasCompactSupport h j)

theorem dyadicKernelPiece_deriv_eq_fourier_derivativeSymbol
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (j : ℕ) (x : ℝ) :
    deriv (dyadicKernelPiece h j) x =
      𝓕 (dyadicKernelDerivativeSymbol h j) (-x) := by
  let f : ℝ → ℂ := dyadicSymbolPiece h j
  let g : ℝ → ℂ := dyadicKernelDerivativeSymbol h j
  have hf : Integrable f := by
    simpa [f] using dyadicSymbolPiece_iteratedDeriv_integrable h j 0 (by norm_num)
  have hfweighted : Integrable (fun ξ : ℝ => ξ • f ξ) := by
    have hweight : (fun ξ : ℝ => ξ • f ξ) = dyadicKernelWeightedInput h j := by
      funext ξ
      change ξ • dyadicSymbolPiece h j ξ =
        (ξ : ℂ) * dyadicSymbolPiece h j ξ
      rw [Complex.real_smul]
    rw [hweight]
    exact dyadicKernelWeightedInput_integrable h j
  have hFourierDeriv := Real.deriv_fourier hf hfweighted
  have hkernel : dyadicKernelPiece h j = fun y : ℝ => 𝓕 f (-y) := by
    funext y
    simpa [f] using dyadicKernelPiece_eq_fourier_neg h j y
  have hweighted :
      (fun ξ : ℝ => (-2 * Real.pi * Complex.I * ξ) • f ξ) =
        fun ξ : ℝ => -g ξ := by
    funext ξ
    simp [f, g, dyadicKernelDerivativeSymbol, smul_eq_mul]
    ring
  have hnegFourier : 𝓕 (fun ξ : ℝ => -g ξ) (-x) = -𝓕 g (-x) := by
    rw [Real.fourier_eq, Real.fourier_eq]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with ξ
    simp [Pi.neg_apply, neg_smul]
  calc
    deriv (dyadicKernelPiece h j) x = deriv (fun y : ℝ => 𝓕 f (-y)) x :=
      congrArg (fun F : ℝ → ℂ => deriv F x) hkernel
    _ = -𝓕 (fun ξ : ℝ => (-2 * Real.pi * Complex.I * ξ) • f ξ) (-x) := by
      rw [deriv_comp_neg, hFourierDeriv]
    _ = -𝓕 (fun ξ : ℝ => -g ξ) (-x) := by rw [hweighted]
    _ = 𝓕 g (-x) := by rw [hnegFourier]; simp

theorem dyadicKernelDerivativeSymbol_l1_le {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    ∫ ξ : ℝ, ‖dyadicKernelDerivativeSymbol h j ξ‖ ≤
      D * dyadicScale j ^ 2 := by
  let t := dyadicScale j
  let q : ℝ → ℝ := fun ξ => ‖dyadicKernelDerivativeSymbol h j ξ‖
  let s : Set ℝ := Set.Icc (-(t / 4)) (t / 4)
  have ht : 0 < t := dyadicScale_pos j
  have hqcont : Continuous q := by
    dsimp [q]
    exact (dyadicKernelDerivativeSymbol_contDiff h j).continuous.norm
  have hqsupport : Function.support q ⊆ s := by
    intro ξ hξ
    have hne : dyadicKernelDerivativeSymbol h j ξ ≠ 0 := by
      simpa [q] using hξ
    have hsupp : ξ ∈ Function.support (dyadicKernelDerivativeSymbol h j) := by
      change dyadicKernelDerivativeSymbol h j ξ ≠ 0
      exact hne
    simpa [s, t] using dyadicKernelDerivativeSymbol_support_Icc h j hsupp
  have hqcompact : HasCompactSupport q :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hqsupport
  have hqint : Integrable q := hqcont.integrable_of_hasCompactSupport hqcompact
  have hqintSet : IntegrableOn q s volume := hqint.integrableOn
  have hfinite : volume s ≠ ⊤ := by
    dsimp [s]
    exact isCompact_Icc.measure_lt_top.ne
  have hq_indicator : q = s.indicator q := by
    funext ξ
    by_cases hξ : ξ ∈ s
    · simp [hξ]
    · have hzero : q ξ = 0 := by
        by_contra hqξ
        have hqmem : ξ ∈ Function.support q := by
          change q ξ ≠ 0
          exact hqξ
        exact hξ (hqsupport hqmem)
      simp [hξ, hzero]
  have hc : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ ≤ 8 := by
    simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_lt_four]
  have hD : 0 ≤ D := h.D_nonneg
  calc
    ∫ ξ : ℝ, q ξ = ∫ ξ : ℝ, s.indicator q ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact congrFun hq_indicator ξ
    _ = ∫ ξ in s, q ξ ∂volume := integral_indicator (by
      dsimp [s]
      exact measurableSet_Icc)
    _ ≤ ∫ ξ in s, 2 * t * D ∂volume := by
      apply setIntegral_mono_on hqintSet (integrableOn_const hfinite) (by
        dsimp [s]
        exact measurableSet_Icc)
      intro ξ hξ
      have hxi : ‖(ξ : ℂ)‖ ≤ t / 4 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨hξ.1, hξ.2⟩
      have hnorm : ‖dyadicSymbolPiece h j ξ‖ ≤ D := dyadicSymbolPiece_norm_le h j ξ
      have hproduct : ‖dyadicKernelDerivativeSymbol h j ξ‖ =
          ‖(2 * (Real.pi : ℂ) * Complex.I)‖ *
            (‖(ξ : ℂ)‖ * ‖dyadicSymbolPiece h j ξ‖) := by
        change ‖(2 * (Real.pi : ℂ) * Complex.I) *
          ((ξ : ℂ) * dyadicSymbolPiece h j ξ)‖ = _
        simp only [norm_mul]
      calc
        q ξ = ‖(2 * (Real.pi : ℂ) * Complex.I)‖ *
            (‖(ξ : ℂ)‖ * ‖dyadicSymbolPiece h j ξ‖) := by
              exact hproduct
        _ ≤ 8 * ((t / 4) * D) := by
          apply mul_le_mul hc
          · exact mul_le_mul hxi hnorm (by positivity) (by positivity)
          · positivity
          · positivity
        _ = 2 * t * D := by ring
    _ = (2 * t * D) * (t / 2) := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc]
      have hwidth : t / 4 - -(t / 4) = t / 2 := by ring
      rw [hwidth, ENNReal.toReal_ofReal (by positivity)]
      ring
    _ = D * dyadicScale j ^ 2 := by
      dsimp [t]
      ring

theorem dyadicKernelDerivativeSymbol_iteratedDeriv_two_l1_le
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (j : ℕ) :
    ∫ ξ : ℝ, ‖iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ‖ ≤
      509 * B * D := by
  let t := dyadicScale j
  let q : ℝ → ℝ := fun ξ =>
    ‖iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ‖
  let s : Set ℝ := Set.Icc (-(t / 4)) (t / 4)
  have ht : 0 < t := dyadicScale_pos j
  have hqcont : Continuous q := by
    dsimp [q]
    exact ((dyadicKernelDerivativeSymbol_contDiff h j).continuous_iteratedDeriv
      2 (by norm_num)).norm
  have hqsupport : Function.support q ⊆ s := by
    intro ξ hξ
    have hne : iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ ≠ 0 := by
      simpa [q] using hξ
    have hsupp : ξ ∈ Function.support
        (iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j)) := by
      change iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j) ξ ≠ 0
      exact hne
    have hAnn : ξ ∈ dyadicClosedAnnulus j := by
      have hts : ξ ∈ tsupport (iteratedDeriv 2 (dyadicKernelDerivativeSymbol h j)) :=
        subset_closure hsupp
      have hts0 : ξ ∈ tsupport
          (deriv (deriv (dyadicKernelDerivativeSymbol h j))) := by
        simpa [iteratedDeriv_succ, iteratedDeriv_one] using hts
      have hts' : ξ ∈ tsupport (dyadicKernelDerivativeSymbol h j) :=
        tsupport_deriv_subset (tsupport_deriv_subset hts0)
      have hsub₂ := tsupport_mul_subset_right
        (f := fun _ : ℝ => (2 * (Real.pi : ℂ) * Complex.I))
        (g := fun y : ℝ => (y : ℂ) * dyadicSymbolPiece h j y)
      have hsub₁ := tsupport_mul_subset_right (f := fun y : ℝ => (y : ℂ))
        (g := dyadicSymbolPiece h j)
      have htsf : ξ ∈ tsupport (dyadicSymbolPiece h j) := hsub₁ (hsub₂ hts')
      exact dyadicSymbolPiece_tsupport_annulus h j htsf
    have hupper : |ξ| ≤ t / 4 := by
      simpa [t] using hAnn.2
    simpa [s, t] using abs_le.mp hupper
  have hqcompact : HasCompactSupport q :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hqsupport
  have hqint : Integrable q := hqcont.integrable_of_hasCompactSupport hqcompact
  have hqintSet : IntegrableOn q s volume := hqint.integrableOn
  have hfinite : volume s ≠ ⊤ := by
    dsimp [s]
    exact isCompact_Icc.measure_lt_top.ne
  have hq_indicator : q = s.indicator q := by
    funext ξ
    by_cases hξ : ξ ∈ s
    · simp [hξ]
    · have hzero : q ξ = 0 := by
        by_contra hqξ
        have hqmem : ξ ∈ Function.support q := by
          change q ξ ≠ 0
          exact hqξ
        exact hξ (hqsupport hqmem)
      simp [hξ, hzero]
  calc
    ∫ ξ : ℝ, q ξ = ∫ ξ : ℝ, s.indicator q ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact congrFun hq_indicator ξ
    _ = ∫ ξ in s, q ξ ∂volume := integral_indicator (by
      dsimp [s]
      exact measurableSet_Icc)
    _ ≤ ∫ ξ in s, 1018 * B * D / t ∂volume := by
      apply setIntegral_mono_on hqintSet (integrableOn_const hfinite) (by
        dsimp [s]
        exact measurableSet_Icc)
      intro ξ hξ
      exact dyadicKernelDerivativeSymbol_iteratedDeriv_two_norm_le h j ξ
    _ = (1018 * B * D / t) * (t / 2) := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc]
      have hwidth : t / 4 - -(t / 4) = t / 2 := by ring
      rw [hwidth, ENNReal.toReal_ofReal (by positivity)]
      field_simp
    _ = 509 * B * D := by
      field_simp [ne_of_gt ht]
      ring

theorem dyadicKernelPiece_deriv_x_sq_bound {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) (hx : x ≠ 0) :
    ‖deriv (dyadicKernelPiece h j) x‖ ≤
      128 * B * D / |x| ^ 2 := by
  let f : ℝ → ℂ := dyadicKernelDerivativeSymbol h j
  have hfcont : ContDiff ℝ 2 f := dyadicKernelDerivativeSymbol_contDiff h j
  have hfint : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) → Integrable (iteratedDeriv n f) := by
    intro n hn
    have hn' : n ≤ 2 := by exact_mod_cast hn
    simpa [f] using dyadicKernelDerivativeSymbol_iteratedDeriv_integrable h j n hn'
  have hFourierDeriv := Real.fourier_iteratedDeriv
    (N := 2) hfcont hfint (n := 2) (by norm_num)
  have hFourierIdentity := congrFun hFourierDeriv (-x)
  have hFourierL1 :
      ‖𝓕 (iteratedDeriv 2 f) (-x)‖ ≤
        ∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖ := by
    change ‖VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ ℝ) (iteratedDeriv 2 f) (-x)‖ ≤ _
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv 2 f) (-x)
  have hL1 := dyadicKernelDerivativeSymbol_iteratedDeriv_two_l1_le h j
  have hKernelFourier :
      deriv (dyadicKernelPiece h j) x = 𝓕 f (-x) := by
    simpa [f] using dyadicKernelPiece_deriv_eq_fourier_derivativeSymbol h j x
  let c : ℂ := (2 * (Real.pi : ℂ) * Complex.I * (-x : ℂ)) ^ 2
  have hc_norm : ‖c‖ = (2 * Real.pi * |x|) ^ 2 := by
    dsimp [c]
    simp [norm_pow, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_neg]
  have hc_pos : 0 < ‖c‖ := by
    rw [hc_norm]
    positivity
  have hnorm_relation :
      ‖𝓕 (iteratedDeriv 2 f) (-x)‖ = ‖c‖ * ‖𝓕 f (-x)‖ := by
    simpa [f, c] using congrArg (fun z : ℂ => ‖z‖) hFourierIdentity
  have hFourierBound : ‖𝓕 f (-x)‖ ≤
      (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / ‖c‖ := by
    apply (le_div_iff₀ hc_pos).2
    rw [mul_comm, ← hnorm_relation]
    exact hFourierL1
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hc_lower : 4 * |x| ^ 2 ≤ ‖c‖ := by
    rw [hc_norm]
    have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hbase : 2 * |x| ≤ 2 * Real.pi * |x| := by nlinarith
    have hbase_sum : 0 ≤ 2 * |x| + (2 * Real.pi * |x|) := by positivity
    have hsquare := mul_nonneg (sub_nonneg.mpr hbase) hbase_sum
    nlinarith [hsquare]
  have hden_pos : 0 < 4 * |x| ^ 2 := by positivity
  have hL1_nonneg : 0 ≤ ∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hFourierBound' : ‖𝓕 f (-x)‖ ≤
      (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / (4 * |x| ^ 2) := by
    calc
      ‖𝓕 f (-x)‖ ≤
          (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / ‖c‖ := hFourierBound
      _ ≤ (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / (4 * |x| ^ 2) :=
        (div_le_div_iff₀ hc_pos hden_pos).2
          (mul_le_mul_of_nonneg_left hc_lower hL1_nonneg)
  have hL1compare :
      (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / (4 * |x| ^ 2) ≤
        (509 * B * D) / (4 * |x| ^ 2) :=
    div_le_div_of_nonneg_right hL1 (by positivity)
  have hB : 0 ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
  have hBD : 0 ≤ B * D := mul_nonneg hB h.D_nonneg
  have hconstant : 509 * B * D / (4 * |x| ^ 2) ≤
      128 * B * D / |x| ^ 2 := by
    have hden : 0 < |x| ^ 2 := sq_pos_of_pos hxabs
    have hden4 : 0 < 4 * |x| ^ 2 := by positivity
    apply (div_le_div_iff₀ hden4 hden).2
    nlinarith [mul_nonneg hBD hden.le]
  calc
    ‖deriv (dyadicKernelPiece h j) x‖ = ‖𝓕 f (-x)‖ := by
      rw [hKernelFourier]
    _ ≤ (∫ ξ : ℝ, ‖iteratedDeriv 2 f ξ‖) / (4 * |x| ^ 2) := hFourierBound'
    _ ≤ (509 * B * D) / (4 * |x| ^ 2) := hL1compare
    _ ≤ 128 * B * D / |x| ^ 2 := hconstant

theorem dyadicKernelPiece_deriv_pointwise_bound {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) :
    ‖deriv (dyadicKernelPiece h j) x‖ ≤
      A * D * dyadicScale j ^ 2 /
        (1 + dyadicScale j * |x|) ^ 2 := by
  let t := dyadicScale j
  let u := t * |x|
  have ht : 0 < t := dyadicScale_pos j
  have hB : 0 ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
  have hB1 : 1 ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
  have hA : 512 * B ≤ A := by
    unfold A
    nlinarith [hB]
  have hA4 : 4 ≤ A := by nlinarith [hA, hB1]
  have hAnonneg : 0 ≤ A := by unfold A; positivity
  have hu_nonneg : 0 ≤ u := mul_nonneg ht.le (abs_nonneg x)
  by_cases hu : u ≤ 1
  · have hFourierL1 :
        ‖𝓕 (dyadicKernelDerivativeSymbol h j) (-x)‖ ≤
          ∫ ξ : ℝ, ‖dyadicKernelDerivativeSymbol h j ξ‖ := by
      change ‖VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ ℝ) (dyadicKernelDerivativeSymbol h j) (-x)‖ ≤ _
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ) (dyadicKernelDerivativeSymbol h j) (-x)
    have hL1 := dyadicKernelDerivativeSymbol_l1_le h j
    have hdt : 0 ≤ D * t ^ 2 := mul_nonneg h.D_nonneg (sq_nonneg t)
    have hden : (1 + u) ^ 2 ≤ 4 := by nlinarith [hu]
    have hdenA : (1 + u) ^ 2 ≤ A := hden.trans hA4
    have hdenpos : 0 < (1 + u) ^ 2 := by positivity
    have hcompare : D * t ^ 2 ≤ A * D * t ^ 2 / (1 + u) ^ 2 := by
      apply (le_div_iff₀ hdenpos).2
      have hmul := mul_le_mul_of_nonneg_left hdenA hdt
      nlinarith [hmul]
    calc
      ‖deriv (dyadicKernelPiece h j) x‖ =
          ‖𝓕 (dyadicKernelDerivativeSymbol h j) (-x)‖ := by
            rw [dyadicKernelPiece_deriv_eq_fourier_derivativeSymbol]
      _ ≤ ∫ ξ : ℝ, ‖dyadicKernelDerivativeSymbol h j ξ‖ := hFourierL1
      _ ≤ D * t ^ 2 := hL1
      _ ≤ A * D * t ^ 2 / (1 + u) ^ 2 := hcompare
      _ = A * D * dyadicScale j ^ 2 /
            (1 + dyadicScale j * |x|) ^ 2 := by simp [u, t]
  · have huge : 1 ≤ u := le_of_not_ge hu
    have hx : x ≠ 0 := by
      intro hx
      subst x
      simp [u] at huge
      norm_num at huge
    have hxabs : 0 < |x| := abs_pos.mpr hx
    have hkernel := dyadicKernelPiece_deriv_x_sq_bound h j x hx
    have hkernelRewrite : 128 * B * D / |x| ^ 2 =
        128 * B * D * t ^ 2 / u ^ 2 := by
      dsimp [u]
      field_simp [ne_of_gt ht, ne_of_gt hxabs]
    have hden : (1 + u) ^ 2 ≤ 4 * u ^ 2 := by nlinarith [huge]
    have hDt : 0 ≤ D * t ^ 2 := mul_nonneg h.D_nonneg (sq_nonneg t)
    have hnum : 512 * B * D * t ^ 2 ≤ A * D * t ^ 2 := by
      calc
        512 * B * D * t ^ 2 = (512 * B) * (D * t ^ 2) := by ring
        _ ≤ A * (D * t ^ 2) := mul_le_mul_of_nonneg_right hA hDt
        _ = A * D * t ^ 2 := by ring
    have hnum' := mul_le_mul_of_nonneg_right hnum (sq_nonneg u)
    have hfraction : 128 * B * D * t ^ 2 / u ^ 2 ≤
        A * D * t ^ 2 / (4 * u ^ 2) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < u))
        (mul_pos (by norm_num) (sq_pos_of_pos (by linarith : 0 < u)))).2
      nlinarith [hnum']
    have htargetNonneg : 0 ≤ A * D * t ^ 2 :=
      mul_nonneg (mul_nonneg hAnonneg h.D_nonneg) (sq_nonneg t)
    have htargetDenPos : 0 < (1 + u) ^ 2 := by positivity
    have hfraction' : A * D * t ^ 2 / (4 * u ^ 2) ≤
        A * D * t ^ 2 / (1 + u) ^ 2 :=
      div_le_div_of_nonneg_left htargetNonneg htargetDenPos hden
    calc
      ‖deriv (dyadicKernelPiece h j) x‖ ≤ 128 * B * D / |x| ^ 2 := hkernel
      _ = 128 * B * D * t ^ 2 / u ^ 2 := hkernelRewrite
      _ ≤ A * D * t ^ 2 / (4 * u ^ 2) := hfraction
      _ ≤ A * D * t ^ 2 / (1 + u) ^ 2 := hfraction'
      _ = A * D * dyadicScale j ^ 2 /
            (1 + dyadicScale j * |x|) ^ 2 := by simp [u, t]

theorem dyadicKernelPiece_pointwise_bound {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) :
    ‖dyadicKernelPiece h j x‖ ≤
      A * D * dyadicScale j / (1 + dyadicScale j * |x|) ^ 2 := by
  let t := dyadicScale j
  let u := t * |x|
  have ht : 0 < t := dyadicScale_pos j
  have hB : 0 ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
  have hA : 180 * B ≤ A := by
    unfold A
    norm_num
    nlinarith [hB]
  have hAnonneg : 0 ≤ A := by
    unfold A
    positivity
  by_cases hu : u ≤ 1
  · exact dyadicKernelPiece_bound_of_small_frequency h j x (by
      simpa [u, t] using hu)
  · have huge : 1 ≤ u := le_of_not_ge hu
    have hx : x ≠ 0 := by
      intro hx
      subst x
      simp [u] at huge
      norm_num at huge
    have hxabs : 0 < |x| := abs_pos.mpr hx
    have hkernel := dyadicKernelPiece_x_sq_bound h j x hx
    have hkernelRewrite :
        45 * B * D / (t * |x| ^ 2) = 45 * B * D * t / u ^ 2 := by
      dsimp [u]
      field_simp [ne_of_gt ht, ne_of_gt hxabs]
    have hden : (1 + u) ^ 2 ≤ 4 * u ^ 2 := by nlinarith [huge]
    have hDt : 0 ≤ D * t := mul_nonneg h.D_nonneg ht.le
    have hnum : 180 * B * D * t ≤ A * D * t := by
      calc
        180 * B * D * t = (180 * B) * (D * t) := by ring
        _ ≤ A * (D * t) := mul_le_mul_of_nonneg_right hA hDt
        _ = A * D * t := by ring
    have hnum' := mul_le_mul_of_nonneg_right hnum (sq_nonneg u)
    have hfraction : 45 * B * D * t / u ^ 2 ≤ A * D * t / (4 * u ^ 2) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < u))
        (mul_pos (by norm_num) (sq_pos_of_pos (by linarith : 0 < u)))).2
      nlinarith [hnum']
    have htargetNonneg : 0 ≤ A * D * t :=
      mul_nonneg (mul_nonneg hAnonneg h.D_nonneg) ht.le
    have htargetDenPos : 0 < (1 + u) ^ 2 := by positivity
    have hfraction' : A * D * t / (4 * u ^ 2) ≤
        A * D * t / (1 + u) ^ 2 :=
      div_le_div_of_nonneg_left htargetNonneg htargetDenPos hden
    calc
      ‖dyadicKernelPiece h j x‖ ≤ 45 * B * D / (t * |x| ^ 2) := hkernel
      _ = 45 * B * D * t / u ^ 2 := hkernelRewrite
      _ ≤ A * D * t / (4 * u ^ 2) := hfraction
      _ ≤ A * D * t / (1 + u) ^ 2 := hfraction'
      _ = A * D * dyadicScale j / (1 + dyadicScale j * |x|) ^ 2 := by
        simp [u, t]

end

end FractionalPrimes.Literature.Multiplier
