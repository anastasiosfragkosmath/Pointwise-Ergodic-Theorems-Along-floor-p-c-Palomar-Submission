module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWSourceWindow
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWCellLogThreshold
public import Mathlib.Tactic
@[expose] public section

/-! A single source threshold for the already checked selected-Möbius
full-frequency assembly.  This packages only the threshold facts used by the
live conditional integral theorem; its grouped-factor estimate remains an
explicit input to that theorem. -/

noncomputable section

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Twisted

/-- The maximum threshold needed to apply the live selected-Möbius source
integral estimate on every frequency interval in the absolute-transfer
envelope.  The three entries are the source-window threshold, cell-log
threshold, and uncapped-saving threshold, with the latter two evaluated at
the source choice `eps = eta/4`. -/
noncomputable def selectedMobiusPTWFinalSourceThreshold
    (a eta : ℝ) : ℝ :=
  max (selectedMobiusPTWSourceWindowThreshold a eta)
    (max (Real.exp (selectedMobiusPTWCellLogThreshold a (eta / 4)))
      (selectedMobiusPTWUncappedSavingThreshold a (eta / 4)))

/-- Above the combined source threshold, every premise of the live
selected-Möbius aggregate that depends only on `X` and the outer frequency
endpoint is available.  The bound on the integral itself is still supplied
by the aggregate theorem, with its exact grouped-factor `hMUFblock`
continuation. -/
theorem selectedMobiusPTWFinalSourceThreshold_facts
    {a eta X H T U : ℝ}
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta0 : 0 < eta) (heta : eta < 3 / 16)
    (hX : selectedMobiusPTWFinalSourceThreshold a eta ≤ X)
    (hHpos : 0 < H)
    (hHlower : X ^ (5 / 8 + eta) ≤ H)
    (hHupper : H ≤ X ^ (1 - eta))
    (hTlower : (X / H) * (Real.log X) ^ (50 * a) ≤ |T|)
    (hTupper : |T| ≤ X ^ a)
    (hU : U ∈ Set.Icc (X / H)
      ((X / H) * selectedMobiusPTWTransferW X a ^ 4)) :
    (2 : ℝ) ^ 120 ≤ X ∧
      Real.exp (selectedMobiusPTWCellLogThreshold a (eta / 4)) ≤ X ∧
      selectedMobiusPTWUncappedSavingThreshold a (eta / 4) ≤ X ∧
      0 < eta / 4 ∧ eta / 4 ≤ 3 / 16 ∧
      2 ≤ U ∧ U ≤ X ^ (3 / 8 - 2 * (eta / 4)) ∧
      ∀ t ∈ Set.Icc (-U) U,
        (Real.log X) ^ (45 * a) ≤ |T - t| ∧
          |T - t| ≤ X ^ (a + 1) := by
  have hSource : selectedMobiusPTWSourceWindowThreshold a eta ≤ X :=
    (le_max_left _ _).trans hX
  have hTail :
      max (Real.exp (selectedMobiusPTWCellLogThreshold a (eta / 4)))
          (selectedMobiusPTWUncappedSavingThreshold a (eta / 4)) ≤ X :=
    (le_max_right _ _).trans hX
  have hCell : Real.exp (selectedMobiusPTWCellLogThreshold a (eta / 4)) ≤ X :=
    (le_max_left _ _).trans hTail
  have hSave : selectedMobiusPTWUncappedSavingThreshold a (eta / 4) ≤ X :=
    (le_max_right _ _).trans hTail
  have hWindow := selectedMobiusPTWSourceWindow_compatible
    ha heta0 heta hSource hHpos hHlower hHupper hTlower hTupper hU
  have hGrowth := selectedMobiusPTWTransferGrowth_of_threshold
    ha heta0 ((le_max_left _ _).trans hSource)
  have hEta4pos : 0 < eta / 4 := by positivity
  have hEta4le : eta / 4 ≤ 3 / 16 := by
    nlinarith
  refine ⟨hGrowth.2.1, hCell, hSave, hEta4pos, hEta4le,
    hWindow.1, ?_, hWindow.2.2⟩
  have hexp : 3 / 8 - eta / 2 = 3 / 8 - 2 * (eta / 4) := by ring
  rw [← hexp]
  exact hWindow.2.1

#print axioms selectedMobiusPTWFinalSourceThreshold_facts

end FractionalPrimes.Literature.DirichletMean

end
