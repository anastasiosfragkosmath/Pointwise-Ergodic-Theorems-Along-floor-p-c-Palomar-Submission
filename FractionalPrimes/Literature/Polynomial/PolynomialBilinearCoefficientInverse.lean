module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseDescent

/-!
# Nondegenerate bilinear polynomial inverse theorem

This file closes blueprint node `lbi:inverse-theorem` by assembling the
checked energy, pigeonhole, recurrence, and finite-descent components.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The exact nondegenerate bilinear polynomial inverse theorem from the
approved blueprint. -/
theorem bilinearCoefficientInverse
    (d : ℕ) (hd : 1 ≤ d)
    (X₀ : ℤ) (H M ρ : ℝ)
    (hX : 3 ≤ (X₀ : ℝ))
    (hH : 2 ≤ H) (hHX : H ≤ (X₀ : ℝ)) (hM : 2 ≤ M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (hlength :
      (bilinearInverseConstant d : ℝ) *
          (ρ⁻¹) ^ bilinearInverseExponent d *
            max ((X₀ : ℝ) / M) M ≤ H)
    (α β : ℕ → ℂ) (ν : ℕ → ℝ)
    (hνtop : ν (d + 1) = 0)
    (hUV : 0 < bilinearU ((X₀ : ℝ) / M) α * bilinearV M β)
    (hlarge :
      ρ * H * (bilinearU ((X₀ : ℝ) / M) α * bilinearV M β) ≤
        ‖bilinearS (X₀ : ℝ) H M α β
          (bilinearCenteredPhase (X₀ : ℝ) d ν)‖) :
    ∃ Q : ℕ, 1 ≤ Q ∧
      (Q : ℝ) ≤ (bilinearInverseConstant d : ℝ) *
        (ρ⁻¹) ^ bilinearInverseExponent d ∧
      ∀ j, 1 ≤ j → j ≤ d →
        realDistanceToIntegers
            ((Q : ℝ) * bilinearDerivativeCoefficient (X₀ : ℝ) ν j) ≤
          (bilinearInverseConstant d : ℝ) *
            (ρ⁻¹) ^ bilinearInverseExponent d *
              (X₀ : ℝ) / H ^ (j + 1) := by
  let X : ℝ := X₀
  let L : ℝ := X / M
  have hMpos : 0 < M := by linarith
  have hXreal : 3 ≤ X := by simpa [X] using hX
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hXL : X = L * M := by
    dsimp [L]
    field_simp [hMpos.ne']
  have hscale := bilinearInverse_scale_bounds d hd X H L M ρ
    hXreal hH (by simpa [X] using hHX) hM (by rfl) hρ hρhalf
    (by simpa [X, L] using hlength)
  rcases hscale with ⟨hZ8, hZr, hZs, hrM, hsL⟩
  have hr : 1 ≤ H / L := by linarith
  have hs : 1 ≤ H / M := by linarith
  have hrEight : 8 ≤ H / L := hZ8.trans hZr
  obtain ⟨q₀, U, hq₀, hq₀A, hUcenters, hUcount, hfirst⟩ :=
    bilinearLargeCorrelation_commonDenominator d hd X H L M ρ hLpos hM
      hXL (by simpa [X] using hHX) hr hs hrEight hrM hZr hZs hρ hρhalf
      α β ν
      (by simpa [X, L] using hUV)
      (by simpa [X, L] using hlarge)
  rcases bilinearSelectedCenters_secondRecurrenceSetup d hd X H M ρ
      (by linarith) hs hρ hρhalf U hUcenters hUcount X₀ (by rfl) with
    ⟨hUrange, hUcard, hoffset⟩
  have hUupper : ∀ u ∈ U, (u : ℝ) ≤ 2 * M := by
    intro u hu
    exact ((mem_bilinearWindowCenters M u).mp (hUcenters hu)).2.2
  obtain ⟨state⟩ := bilinearInverseDescent_exists_finalState
    d q₀ hd X H L M ρ hLpos (by linarith) (by linarith) hXL
    hρ hρhalf hZr hZs hrM ν hνtop
    (fun u => bilinearCommonLeftBase X (H / M) u)
    U hUrange hUcard hUupper hoffset
    (fun j hj u hu => by
      have hjData := Finset.mem_Icc.mp hj
      exact hfirst u hu j hjData.1 hjData.2)
  have hUlowerPos :
      0 < 2 * (bilinearInverseZTwo d ρ⁻¹)⁻¹ *
        (bilinearSecondRecurrenceLength M : ℝ) := by
    have hδ := (bilinearInverse_auxiliary_densities d hd ρ hρ hρhalf).2.2.1
    have hN := bilinearSecondRecurrenceLength_bounds M (by linarith)
    have hNpos : 0 < (bilinearSecondRecurrenceLength M : ℝ) := by
      linarith [hN.1]
    exact mul_pos (mul_pos (by norm_num) hδ) hNpos
  have hUcardPosReal : 0 < (U.card : ℝ) := hUlowerPos.trans_le hUcard
  have hUcardPos : 0 < U.card := by exact_mod_cast hUcardPosReal
  have hUnonempty : U.Nonempty := Finset.card_pos.mp hUcardPos
  rcases state.final_coefficients hd (by linarith) (by linarith) hXpos.le
      hρ hρhalf ν hνtop
      (fun u => bilinearCommonLeftBase X (H / M) u)
      U hUnonempty hUupper hoffset
      (fun u hu => by
        simpa using hfirst u hu 1 (by omega) hd) with
    ⟨htE, hall⟩
  have hx : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  rcases bilinearInverseBudget_values d hd ρ⁻¹ hx with
    ⟨hB, hZOne, hVOne, hA, hZTwo, hVTwo, hC, hE, hZ⟩
  have hZdom := bilinearInverseZ_dominates d hd ρ⁻¹ hx
  have hρinvOne : 1 ≤ ρ⁻¹ := by linarith
  have hZbudget := bilinearInverseZ_le_budget d ρ⁻¹ hρinvOne
  let Q : ℕ := state.t * q₀
  have hQpos : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.mul_pos state.t_pos hq₀
  have hQAE : (Q : ℝ) ≤
      bilinearInverseA d ρ⁻¹ * bilinearInverseE d ρ⁻¹ := by
    calc
      (Q : ℝ) = (q₀ : ℝ) * (state.t : ℝ) := by simp [Q]; ring
      _ ≤ bilinearInverseA d ρ⁻¹ * bilinearInverseE d ρ⁻¹ :=
        mul_le_mul hq₀A htE (Nat.cast_nonneg _) (by linarith)
  have hQZ : (Q : ℝ) ≤ bilinearInverseZ d ρ⁻¹ := by
    calc
      (Q : ℝ) ≤ bilinearInverseA d ρ⁻¹ *
          bilinearInverseE d ρ⁻¹ := hQAE
      _ ≤ (bilinearInverseCValue d : ℝ) *
          bilinearInverseA d ρ⁻¹ * bilinearInverseE d ρ⁻¹ := by
        have hAE0 : 0 ≤ bilinearInverseA d ρ⁻¹ *
            bilinearInverseE d ρ⁻¹ := by positivity
        calc
          bilinearInverseA d ρ⁻¹ * bilinearInverseE d ρ⁻¹ =
              1 * (bilinearInverseA d ρ⁻¹ *
                bilinearInverseE d ρ⁻¹) := by ring
          _ ≤ (bilinearInverseCValue d : ℝ) *
              (bilinearInverseA d ρ⁻¹ *
                bilinearInverseE d ρ⁻¹) :=
            mul_le_mul_of_nonneg_right hC hAE0
          _ = (bilinearInverseCValue d : ℝ) *
              bilinearInverseA d ρ⁻¹ * bilinearInverseE d ρ⁻¹ := by ring
      _ ≤ bilinearInverseZ d ρ⁻¹ := hZdom.2.2.2.2
  refine ⟨Q, hQpos, hQZ.trans hZbudget, ?_⟩
  intro j hj hjd
  have hjmem : j ∈ Finset.Icc 1 d := Finset.mem_Icc.mpr ⟨hj, hjd⟩
  have hcoefficient := hall j hjmem
  have hscale0 : 0 ≤ X / H ^ (j + 1) := by positivity
  calc
    realDistanceToIntegers
        ((Q : ℝ) * bilinearDerivativeCoefficient (X₀ : ℝ) ν j) =
      realDistanceToIntegers
        (((state.t * q₀ : ℕ) : ℝ) *
          bilinearDerivativeCoefficient X ν j) := by rfl
    _ ≤ (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ *
          bilinearInverseE d ρ⁻¹ * X / H ^ (j + 1) := hcoefficient
    _ ≤ bilinearInverseZ d ρ⁻¹ * (X / H ^ (j + 1)) := by
      have hCAE := hZdom.2.2.2.2
      convert mul_le_mul_of_nonneg_right hCAE hscale0 using 1 <;> ring
    _ ≤ ((bilinearInverseConstant d : ℝ) *
          (ρ⁻¹) ^ bilinearInverseExponent d) *
        (X / H ^ (j + 1)) :=
      mul_le_mul_of_nonneg_right hZbudget hscale0
    _ = (bilinearInverseConstant d : ℝ) *
          (ρ⁻¹) ^ bilinearInverseExponent d *
            (X₀ : ℝ) / H ^ (j + 1) := by
      dsimp [X]
      ring

#print axioms bilinearCoefficientInverse

end

end FractionalPrimes.Literature.Polynomial
