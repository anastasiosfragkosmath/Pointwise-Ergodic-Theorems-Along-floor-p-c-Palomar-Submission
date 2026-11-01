module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownMobiusSubsetAssembly
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownSmallFactorMUFRange
public import Mathlib.Tactic
@[expose] public section

/-!
# MUF subset assembly with the selected scale supplied by three-group geometry

This adapter replaces the explicit MUF range premise for `N/2` and `N` by the
source scale bounds for the selected Möbius factor.  It enlarges the existing
threshold by the fixed elementary scale threshold `2^160`; the analytic
MUF constants, the finite factor `2^11 * 5^19`, and both logarithmic bounds
are inherited unchanged from the base assembly.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- Insert the actual three-group scale bounds into the MUF-selected Möbius
subset assembly.  The new threshold guarantees that both selected dyadic
parameters lie in the exact MUF window `[X^(1/400), X]`. -/
theorem smoothHeathBrownMobiusSubsetAssembly_from_MUF_of_scaleBounds
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {B K : ℝ} (hB : 0 < B) (hK : 0 < K) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fs : List (SmoothHeathBrownFactor X)) →
        (I : Finset (Fin fs.length)) →
        (selected : Fin fs.length) →
        (j : SmoothHeathBrownScaleIndex X) →
        fs.get selected = .mobius j →
        selected ∈ I → I.card ≤ 20 →
        (h : ℤ) → (L x y : ℝ) →
        {q : ℕ} → 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
        {b : ℕ} → b < q → (t : ℝ) → |t| ≤ X →
        (ω : Fin fs.length → ℕ → ℂ) →
        (hω : ∀ i n, ‖ω i n‖ ≤ 1) →
        (hωselected : ∀ n,
          ω selected n = smoothHeathBrownMobiusResiduePhaseWeight q b t n) →
        X ^ (1 / 100 : ℝ) ≤
          smoothHeathBrownFactorScale (.mobius j) →
        smoothHeathBrownFactorScale (.mobius j) ≤
          (2 : ℝ) ^ 11 * Real.sqrt X →
        L = (2 : ℝ) ^ h *
          (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)) →
        -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ) →
        0 ≤ x → x ≤ y →
          ‖smoothGroupSubsetConvolutionSum I
              (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
              (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
                (fs.get i) (ω i) n)
              x y‖ ≤
            (2 : ℝ) ^ 11 * 5 ^ 19 *
                (3 * Cμ * (Real.log X) ^ (-(K + 4))) * Real.sqrt L ∧
          ‖smoothGroupSubsetConvolutionSum I
              (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
              (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
                (fs.get i) (ω i) n)
              x y‖ ≤ (Real.log X) ^ (-K) * Real.sqrt L := by
  obtain ⟨Cμ, Xbase, hCμ, hXbase3, hbase⟩ :=
    smoothHeathBrownMobiusSubsetAssembly_from_MUF hMUF hB hK
  let X₀ : ℝ := max Xbase ((2 : ℝ) ^ 160)
  have hX₀3 : 3 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans hXbase3 (le_max_left Xbase ((2 : ℝ) ^ 160))
  refine ⟨Cμ, X₀, hCμ, hX₀3, ?_⟩
  intro X z hX₀X hz fs I selected j htag hselected hcount h L x y
    q hq hqlog b hb t ht ω hω hωselected hscaleLo hscaleHi hL hh hx hxy
  have hXbaseX : Xbase ≤ X := by
    exact le_trans (le_max_left Xbase ((2 : ℝ) ^ 160)) hX₀X
  have hX160 : (2 : ℝ) ^ 160 ≤ X := by
    exact le_trans (le_max_right Xbase ((2 : ℝ) ^ 160)) hX₀X
  have hMrange : ∀ M : ℝ,
      (M = smoothHeathBrownFactorScale (.mobius j) / 2 ∨
        M = smoothHeathBrownFactorScale (.mobius j)) →
      X ^ (1 / 400 : ℝ) ≤ M ∧ M ≤ X := by
    exact smoothHeathBrownSmallFactor_mufRange_of_scaleBounds
      hX160 hscaleLo hscaleHi
  exact hbase hXbaseX hz fs I selected j htag hselected hcount h L x y
    hq hqlog hb t ht ω hω hωselected hMrange hL hh hx hxy

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusSubsetAssembly_from_MUF_of_scaleBounds
