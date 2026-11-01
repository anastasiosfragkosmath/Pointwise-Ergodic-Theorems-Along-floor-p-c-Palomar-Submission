module

public import FractionalPrimes.FiniteAdjointPairing

@[expose] public section

/-!
# The `ℓ²` adjoint identity for an absolutely summable integer kernel

This extends the checked finite-support pairing by the two truncation limits
used in the Fourier-sequence construction.
-/

namespace FractionalPrimes

open Filter
open scoped BigOperators ComplexConjugate Topology

noncomputable section

/-- Symmetric integer intervals are invariant under negation. -/
theorem symmetricIcc_map_neg (N : ℕ) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).map (Equiv.neg ℤ).toEmbedding =
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  ext z
  simp only [Finset.mem_map, Finset.mem_Icc]
  constructor
  · rintro ⟨x, hx, hxz⟩
    change -x = z at hxz
    rw [← hxz]
    omega
  · intro hz
    refine ⟨-z, ?_, ?_⟩
    · omega
    · change -(-z) = z
      simp

/-- The adjoint pairing after completing only the kernel truncation, while
both input vectors still have finite support. -/
theorem integerKernelFiniteConvolutionLimitL2_pairing_adjoint
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (t u : Finset ℤ) (b c : ℤ → ℂ) :
    inner ℂ (finiteIntegerSequenceL2 u c)
        (integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b) =
      inner ℂ
        (integerKernelFiniteConvolutionLimitL2 (hT := hT)
          (integerKernelAdjoint K) u c)
        (finiteIntegerSequenceL2 t b) := by
  let s : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) (N : ℤ)
  let F := finiteIntegerSequenceL2 t b
  let G := finiteIntegerSequenceL2 u c
  let A : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    finiteDiscreteConvolutionSequenceL2 (s N) t K.coeff b
  let B : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    finiteDiscreteConvolutionSequenceL2 (s N) u
      (integerKernelAdjoint K).coeff c
  have hA : Tendsto A atTop
      (𝓝 (integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b)) := by
    simpa [A, s] using
      integerKernelFiniteConvolutionTruncations_tendsto_limitL2
        (hT := hT) K t b
  have hB : Tendsto B atTop
      (𝓝 (integerKernelFiniteConvolutionLimitL2 (hT := hT)
        (integerKernelAdjoint K) u c)) := by
    simpa [B, s] using
      integerKernelFiniteConvolutionTruncations_tendsto_limitL2
        (hT := hT) (integerKernelAdjoint K) u c
  have hfinite (N : ℕ) : inner ℂ G (A N) = inner ℂ (B N) F := by
    dsimp [A, B, F, G]
    have hs : (s N).map (Equiv.neg ℤ).toEmbedding = s N := by
      dsimp [s]
      exact symmetricIcc_map_neg N
    have hcoeff : (fun n : ℤ => starRingEnd ℂ (K.coeff (-n))) =
        (integerKernelAdjoint K).coeff := by
      funext n
      exact (integerKernelAdjoint_coeff K n).symm
    have hpair :=
      finiteDiscreteConvolutionSequenceL2_pairing_adjoint (s N) t u K.coeff b c
    rw [hs, hcoeff] at hpair
    exact hpair
  have hleft : Tendsto (fun N => inner ℂ G (A N)) atTop
      (𝓝 (inner ℂ G
        (integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b))) :=
    tendsto_const_nhds.inner hA
  have hright : Tendsto (fun N => inner ℂ (B N) F) atTop
      (𝓝 (inner ℂ
        (integerKernelFiniteConvolutionLimitL2 (hT := hT)
          (integerKernelAdjoint K) u c) F)) :=
    hB.inner tendsto_const_nhds
  exact tendsto_nhds_unique hleft
    ((Filter.tendsto_congr' (Filter.Eventually.of_forall hfinite)).2 hright)

/-- The completed `ℓ²(ℤ)` convolution operator has the reflected-conjugate
kernel as its Hilbert-space adjoint.  Lean's inner product is conjugate-linear
in the first input, so the orientation is `⟪g, K*f⟫ = ⟪K* * g, f⟫`. -/
theorem integerKernelConvolutionL2_pairing_adjoint
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (f g : lp (fun _ : ℤ => ℂ) 2) :
    inner ℂ g (integerKernelConvolutionL2 (hT := hT) K f) =
      inner ℂ (integerKernelConvolutionL2 (hT := hT)
        (integerKernelAdjoint K) g) f := by
  let s : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) (N : ℤ)
  let F : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N => finiteIntegerSequenceL2 (s N) f
  let G : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N => finiteIntegerSequenceL2 (s N) g
  let A : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    integerKernelFiniteConvolutionLimitL2 (hT := hT) K (s N) f
  let B : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    integerKernelFiniteConvolutionLimitL2 (hT := hT) (integerKernelAdjoint K) (s N) g
  have hF : Tendsto F atTop (𝓝 f) := by
    simpa [F, s] using finiteIntegerSequenceL2_Icc_tendsto f
  have hG : Tendsto G atTop (𝓝 g) := by
    simpa [G, s] using finiteIntegerSequenceL2_Icc_tendsto g
  have hA : Tendsto A atTop (𝓝 (integerKernelConvolutionL2 (hT := hT) K f)) := by
    simpa [A, s] using integerKernelInputTruncationOutputs_tendsto (hT := hT) K f
  have hB : Tendsto B atTop
      (𝓝 (integerKernelConvolutionL2 (hT := hT) (integerKernelAdjoint K) g)) := by
    simpa [B, s] using integerKernelInputTruncationOutputs_tendsto
      (hT := hT) (integerKernelAdjoint K) g
  have hfinite (N : ℕ) : inner ℂ (G N) (A N) = inner ℂ (B N) (F N) := by
    dsimp [A, B, F, G]
    exact integerKernelFiniteConvolutionLimitL2_pairing_adjoint K (s N) (s N) f g
  have hleft : Tendsto (fun N => inner ℂ (G N) (A N)) atTop
      (𝓝 (inner ℂ g (integerKernelConvolutionL2 (hT := hT) K f))) :=
    hG.inner hA
  have hright : Tendsto (fun N => inner ℂ (B N) (F N)) atTop
      (𝓝 (inner ℂ (integerKernelConvolutionL2 (hT := hT)
        (integerKernelAdjoint K) g) f)) :=
    hB.inner hF
  exact tendsto_nhds_unique hleft
    ((Filter.tendsto_congr' (Filter.Eventually.of_forall hfinite)).2 hright)

end

end FractionalPrimes
