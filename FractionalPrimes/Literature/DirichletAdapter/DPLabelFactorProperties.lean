module

public import FractionalPrimes.Literature.DirichletAdapter.DPRetainedPositiveExponent
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorOuterMass
public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
noncomputable section

/-- Möbius source labels have no logarithmic factor. -/
theorem smoothHeathBrownMobiusLabel_logFactorCount_zero
    {X : ℝ} (ν : SmoothHeathBrownMobiusLabel X) :
    (smoothHeathBrownMobiusLabelFactors ν).countP
      smoothHeathBrownTypeILogFactor = 0 := by
  simp [smoothHeathBrownMobiusLabelFactors,
    smoothHeathBrownTypeILogFactor]

/-- Von Mangoldt source labels carry exactly their final logarithmic factor. -/
theorem smoothHeathBrownVonMangoldtLabel_logFactorCount_one
    {X : ℝ} (ν : SmoothHeathBrownVonMangoldtLabel X) :
    (smoothHeathBrownVonMangoldtLabelFactors ν).countP
      smoothHeathBrownTypeILogFactor = 1 := by
  have hM : (List.ofFn (fun i : Fin ν.1.val =>
      SmoothHeathBrownFactor.mobius (ν.2.1.1 i))).countP
      smoothHeathBrownTypeILogFactor = 0 := by
    apply List.countP_eq_zero.mpr
    intro f hf
    simp only [List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    simp [smoothHeathBrownTypeILogFactor]
  have hT : (List.ofFn (fun i : Fin (ν.1.val - 1) =>
      SmoothHeathBrownFactor.theta (ν.2.1.2 i))).countP
      smoothHeathBrownTypeILogFactor = 0 := by
    apply List.countP_eq_zero.mpr
    intro f hf
    simp only [List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    simp [smoothHeathBrownTypeILogFactor]
  simp [smoothHeathBrownVonMangoldtLabelFactors,
    smoothHeathBrownTypeILogFactor, hM, hT]

#print axioms smoothHeathBrownMobiusLabel_logFactorCount_zero
#print axioms smoothHeathBrownVonMangoldtLabel_logFactorCount_one
end
end FractionalPrimes.Literature.DirichletAdapter
