module

public import FractionalPrimes.Variation

/-!
# Basic finite-chain variation consequences

This module develops direct consequences of the homogeneous variation already
defined in `FractionalPrimes.Core`.  In particular, it records that variation
controls every increment along two positive scales.
-/

public section

namespace FractionalPrimes

open scoped ENNReal NNReal

noncomputable section

/-- The two-point strictly increasing chain determined by two ordered scales. -/
def twoScaleChain (N M : Scale) (hNM : N < M) : StrictScaleChain 1 where
  index i := if i = 0 then N else M
  strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- The two-point chain has the prescribed endpoints. -/
theorem twoScaleChain_zero (N M : Scale) (hNM : N < M) :
    (twoScaleChain N M hNM).index 0 = N := by
  simp [twoScaleChain]

/-- The two-point chain has the prescribed endpoints. -/
theorem twoScaleChain_one (N M : Scale) (hNM : N < M) :
    (twoScaleChain N M hNM).index 1 = M := by
  simp [twoScaleChain]

/-- The contribution of a two-point chain is exactly its endpoint increment. -/
theorem chainVariation_twoScaleChain {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (hr : 0 < r) (u : Scale → E) {N M : Scale} (hNM : N < M) :
    chainVariation r u (twoScaleChain N M hNM) = ENNReal.ofReal ‖u M - u N‖ := by
  rw [chainVariation_eq]
  have hvalue :
      ((∑ i : Fin 1,
        (ENNReal.ofReal ‖u ((twoScaleChain N M hNM).index i.succ) -
          u ((twoScaleChain N M hNM).index i.castSucc)‖).rpow r).rpow r⁻¹) =
        ((ENNReal.ofReal ‖u M - u N‖).rpow r).rpow r⁻¹ := by
    simp [twoScaleChain]
  rw [hvalue]
  simp [ne_of_gt hr]

/-- A positive-exponent variation dominates each individual scale increment. -/
theorem enorm_sub_le_rVariation {E : Type*} [NormedAddCommGroup E] (r : ℝ)
    (hr : 0 < r) (u : Scale → E) {N M : Scale} (hNM : N < M) :
    ENNReal.ofReal ‖u M - u N‖ ≤ rVariation r u := by
  have hchain :
      ((∑ i : Fin 1,
        (ENNReal.ofReal ‖u ((twoScaleChain N M hNM).index i.succ) -
          u ((twoScaleChain N M hNM).index i.castSucc)‖).rpow r).rpow r⁻¹)
        ≤ rVariation r u := by
    rw [rVariation_eq]
    exact le_iSup_of_le 1 (le_iSup_of_le (twoScaleChain N M hNM) le_rfl)
  have hvalue :
      ((∑ i : Fin 1,
        (ENNReal.ofReal ‖u ((twoScaleChain N M hNM).index i.succ) -
          u ((twoScaleChain N M hNM).index i.castSucc)‖).rpow r).rpow r⁻¹) =
        ((ENNReal.ofReal ‖u M - u N‖).rpow r).rpow r⁻¹ := by
    simp [twoScaleChain]
  rw [hvalue] at hchain
  simpa [ENNReal.rpow_mul, ne_of_gt hr, inv_mul_cancel₀ (ne_of_gt hr)] using hchain

/-- For a positive exponent, zero homogeneous variation is equivalent to constancy. -/
theorem rVariation_eq_zero_iff {E : Type*} [NormedAddCommGroup E] (r : ℝ)
    (hr : 0 < r) (u : Scale → E) :
    rVariation r u = 0 ↔ ∀ N M : Scale, u N = u M := by
  constructor
  · intro hzero N M
    have zero_increment : ∀ {A B : Scale}, A < B → u B = u A := by
      intro A B hAB
      have hle := enorm_sub_le_rVariation r hr u hAB
      rw [hzero] at hle
      have henorm : ENNReal.ofReal ‖u B - u A‖ = 0 := bot_unique hle
      have hnorm : ‖u B - u A‖ = 0 :=
        le_antisymm (ENNReal.ofReal_eq_zero.mp henorm) (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    rcases lt_trichotomy N M with hNM | hNM | hMN
    · exact (zero_increment hNM).symm
    · exact hNM ▸ rfl
    · exact zero_increment hMN
  · intro hconstant
    let base : Scale := ⟨1, Nat.succ_pos 0⟩
    have hu : u = fun _ : Scale => u base := by
      funext N
      exact hconstant N base
    rw [hu]
    exact rVariation_const r hr (u base)

end

end FractionalPrimes

end
