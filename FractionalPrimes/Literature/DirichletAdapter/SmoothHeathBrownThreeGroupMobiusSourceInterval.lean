module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownMobiusSelectedGroupSourceAssembly
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownSmallFactorMUFRange
public import Mathlib.Tactic
@[expose] public section

/-!
# Three-group Möbius source interval assembly

This adapter combines the retained three-group scale selection with the
OAISource selected-group source interval estimate. The scale selection's
exact `2^160` threshold and source scale bounds are kept explicit.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- Under the approved retained three-group branch, the selected Möbius
factor's scale bounds feed the checked scale assembly and control the exact
residue-restricted source interval sum. The theorem leaves the selected tag
as a hypothesis, since the small-group argument treats non-Möbius tags by
their separate periodic-factor route. -/
theorem smoothHeathBrownThreeGroupMobiusSourceInterval_of_OAISource
    {B K : ℝ} (hB : 0 < B) (hK : 0 < K) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fs : List (SmoothHeathBrownFactor X)) →
        fs.length ≤ 20 → fs ≠ [] →
        smoothHeathBrownSupportRetained
          (X := X) (z := dyadicMobiusCutoff X) fs →
        (hE : 0 < smoothHeathBrownExponentSum fs) →
        (smoothHeathBrownExponentGrouping fs hE).IImaj (5 / 8) →
        ∃ I : Finset (Fin fs.length), ∃ selected : Fin fs.length,
          selected ∈ I ∧ I.card ≤ 20 ∧
          X ^ (1 / 100 : ℝ) ≤
            smoothHeathBrownFactorScale (fs.get selected) ∧
          smoothHeathBrownFactorScale (fs.get selected) ≤
            (2 : ℝ) ^ 11 * Real.sqrt X ∧
          (∀ j : SmoothHeathBrownScaleIndex X,
            fs.get selected = .mobius j →
            ∀ M : ℝ,
              (M = smoothHeathBrownFactorScale (.mobius j) / 2 ∨
                M = smoothHeathBrownFactorScale (.mobius j)) →
              X ^ (1 / 400 : ℝ) ≤ M ∧ M ≤ X) ∧
          ∀ j : SmoothHeathBrownScaleIndex X,
            fs.get selected = .mobius j →
            ∀ (h : ℤ) (L x y : ℝ),
              {q : ℕ} → 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
              (residue : Fin fs.length → ℕ) → residue selected < q →
              (t : ℝ) → |t| ≤ X →
              L = (2 : ℝ) ^ h *
                (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)) →
              -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ) →
              0 ≤ x → x ≤ y →
              ‖∑ n ∈ factorExtractionRealInterval x y,
                  (∏ i : I,
                    smoothHeathBrownResidueFactorArithmeticFunction (z := z)
                      q (residue i.val) (fs.get i.val)) n *
                    (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
                (2 : ℝ) ^ 11 * 5 ^ 19 *
                  (3 * Cμ * (Real.log X) ^ (-(K + 4))) * Real.sqrt L ∧
              ‖∑ n ∈ factorExtractionRealInterval x y,
                  (∏ i : I,
                    smoothHeathBrownResidueFactorArithmeticFunction (z := z)
                      q (residue i.val) (fs.get i.val)) n *
                    (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
                (Real.log X) ^ (-K) * Real.sqrt L := by
  obtain ⟨Cμ, Xbase, hCμ, hXbase3, hsource⟩ :=
    smoothHeathBrownMobiusSelectedGroupSourceInterval_of_scaleBounds_OAISource
      hB hK
  let X₀ : ℝ := max Xbase ((2 : ℝ) ^ 160)
  have hX₀3 : 3 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans hXbase3 (le_max_left Xbase ((2 : ℝ) ^ 160))
  refine ⟨Cμ, X₀, hCμ, hX₀3, ?_⟩
  intro X z hX₀X hz fs hlen hfsne hret hE hgroup
  have hXbaseX : Xbase ≤ X :=
    le_trans (le_max_left Xbase ((2 : ℝ) ^ 160)) hX₀X
  have hX160 : (2 : ℝ) ^ 160 ≤ X :=
    le_trans (le_max_right Xbase ((2 : ℝ) ^ 160)) hX₀X
  obtain ⟨I, selected, hselected, hNlo, hNhi, hMrange⟩ :=
    smoothHeathBrownThreeGroupMobiusMUFRangeForAssembly
      hX160 fs hlen hfsne hret hE hgroup
  have hIcard : I.card ≤ 20 := by
    calc
      I.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ I)
      _ = fs.length := by simp
      _ ≤ 20 := hlen
  refine ⟨I, selected, hselected, hIcard, hNlo, hNhi, hMrange, ?_⟩
  intro j htag h L x y q hq hqlog residue hresidue t ht hL hh hx hxy
  have hNlo' : X ^ (1 / 100 : ℝ) ≤
      smoothHeathBrownFactorScale (.mobius j) := by
    rw [← htag]
    exact hNlo
  have hNhi' : smoothHeathBrownFactorScale (.mobius j) ≤
      (2 : ℝ) ^ 11 * Real.sqrt X := by
    rw [← htag]
    exact hNhi
  exact hsource hXbaseX hz fs I selected j htag hselected hIcard h L x y
    hq hqlog residue hresidue t ht hNlo' hNhi' hL hh hx hxy

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownThreeGroupMobiusSourceInterval_of_OAISource
