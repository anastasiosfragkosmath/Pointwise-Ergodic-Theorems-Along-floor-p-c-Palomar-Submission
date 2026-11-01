module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownDPBranchEnvelope
public import FractionalPrimes.Literature.DirichletAdapter.DPBranchLogarithmicAbsorption
@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter
noncomputable section

/-- The exact coefficient multiplying the source Type-I branch. -/
noncomputable def dpSourceTypeIConstant (j : ℕ) : ℝ :=
  (2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j

/-- The exact coefficient multiplying the source IImaj branch after
reordering its scalar, residue, and square-root factors. -/
noncomputable def dpSourceIImajConstant : ℝ :=
  (2 * Real.pi : ℝ)⁻¹ * ((40 : ℝ) * (40 * 40)) *
    (3 * smoothHeathBrownDPBlockFourierConstant)

theorem dpSourceTypeIConstant_nonneg (j : ℕ) :
    0 ≤ dpSourceTypeIConstant j := by
  have hmax : 0 ≤ max (1 : ℝ)
      (max (Twisted.smoothDyadicA j) (Twisted.smoothDyadicB j)) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hC : 0 ≤ Twisted.smoothDyadicC j := by
    unfold Twisted.smoothDyadicC
    positivity
  unfold dpSourceTypeIConstant
  positivity

theorem dpSourceIImajConstant_nonneg :
    0 ≤ dpSourceIImajConstant := by
  have hmass := smoothHeathBrownDPFourierKernelMass_nonneg
  have hmoment := smoothHeathBrownDPFourierKernelFirstMoment_nonneg
  have hJ : 0 ≤ FractionalPrimes.Literature.DirichletMean.J 20 := by
    simp [FractionalPrimes.Literature.DirichletMean.J,
      FractionalPrimes.Literature.DirichletMean.K]
  have hkernel : 0 ≤ 2 * smoothHeathBrownDPFourierKernelMass +
      4 * smoothHeathBrownDPFourierKernelFirstMoment := by positivity
  have hC : 0 ≤ smoothHeathBrownDPBlockFourierConstant := by
    unfold smoothHeathBrownDPBlockFourierConstant
    positivity
  unfold dpSourceIImajConstant
  positivity

#print axioms dpSourceTypeIConstant_nonneg
#print axioms dpSourceIImajConstant_nonneg
end
end FractionalPrimes.Literature.DirichletAdapter
