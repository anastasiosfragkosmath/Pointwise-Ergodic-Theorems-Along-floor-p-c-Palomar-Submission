module
public import FractionalPrimes.Final.ForwardSystems
public import FractionalPrimes.Literature.Ergodic.FiniteKernelTransference
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory
open FractionalPrimes.Literature.Ergodic
open FractionalPrimes.Literature.Variation
open scoped ENNReal
noncomputable section

/-- A one-sided finite orbit. Negative sequence coordinates encode forward
iterates, agreeing with the existing convolution sign convention. -/
def forwardOrbitCutoff {X : Type*} [MeasurableSpace X]
    (S : System X) (f : X → ℂ) (N : ℕ) (x : X) : ℤ → ℂ :=
  fun j => if j ∈ Finset.Icc (-(N : ℤ)) 0 then f (S.T^[(-j).toNat] x) else 0

def forwardKernelOperator {X : Type*} [MeasurableSpace X]
    (S : System X) (K : ℤ →₀ ℂ) (f : X → ℂ) : X → ℂ :=
  fun x => ∑ m ∈ K.support, K m * f (S.T^[m.toNat] x)

theorem forwardOrbitCutoff_support_finite {X : Type*} [MeasurableSpace X]
    (S : System X) (f : X → ℂ) (N : ℕ) (x : X) :
    (Function.support (forwardOrbitCutoff S f N x)).Finite := by
  classical
  apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) 0)).subset
  intro j hj
  by_contra h
  change j ∉ Finset.Icc (-(N : ℤ)) 0 at h
  have hz : forwardOrbitCutoff S f N x j = 0 := by simp [forwardOrbitCutoff, h]
  exact hj hz

/-- Only nonnegative kernel times occur in the revised paper. No inverse
transformation is used, including at either cutoff endpoint. -/
theorem convolution_forwardOrbitCutoff {X : Type*} [MeasurableSpace X]
    (S : System X) (K : ℤ →₀ ℂ) (f : X → ℂ) (R L : ℕ)
    (hK : ∀ m ∈ K.support, 0 ≤ m ∧ m ≤ (L : ℤ))
    (j : ℤ) (hj : j ∈ Finset.Icc (-(R : ℤ)) 0) (x : X) :
    finiteKernelConvolution K (forwardOrbitCutoff S f (R + L) x) j =
      forwardKernelOperator S K f (S.T^[(-j).toNat] x) := by
  classical
  unfold finiteKernelConvolution forwardKernelOperator
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hm0, hmL⟩ := hK m hm
  obtain ⟨hjR, hj0⟩ := Finset.mem_Icc.mp hj
  have hseg : j - m ∈ Finset.Icc (-((R + L : ℕ) : ℤ)) 0 := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  simp only [forwardOrbitCutoff, hseg, ↓reduceIte]
  have hadd : (-(j - m)).toNat = m.toNat + (-j).toNat := by omega
  rw [hadd, Function.iterate_add_apply]

def forwardKernelVariation {I X : Type*} [LinearOrder I] [MeasurableSpace X]
    (S : System X) (r : ℝ) (K : I → ℤ →₀ ℂ) (f : X → ℂ) : X → ℝ≥0∞ :=
  orderedRVariationFun r (fun i => forwardKernelOperator S (K i) f)

theorem variation_forwardOrbitCutoff {I X : Type*} [LinearOrder I]
    [MeasurableSpace X] (S : System X) (r : ℝ) (K : I → ℤ →₀ ℂ)
    (f : X → ℂ) (R L : ℕ)
    (hK : ∀ i m, m ∈ (K i).support → 0 ≤ m ∧ m ≤ (L : ℤ))
    (j : ℤ) (hj : j ∈ Finset.Icc (-(R : ℤ)) 0) (x : X) :
    finiteKernelDiscreteVariation r K (forwardOrbitCutoff S f (R + L) x) j =
      forwardKernelVariation S r K f (S.T^[(-j).toNat] x) := by
  unfold finiteKernelDiscreteVariation forwardKernelVariation orderedRVariationFun
  congr 1
  funext i
  exact convolution_forwardOrbitCutoff S (K i) f R L (hK i) j hj x

theorem lintegral_comp_forwardIterate {X : Type*} [MeasurableSpace X]
    (S : System X) (n : ℕ) (F : X → ℝ≥0∞) (hF : AEMeasurable F S.μ) :
    ∫⁻ x, F (S.T^[n] x) ∂S.μ = ∫⁻ x, F x ∂S.μ := by
  have hp := S.measurePreserving_iterate n
  have hm : AEMeasurable F (S.μ.map S.T^[n]) := by rw [hp.map_eq]; exact hF
  change lintegral S.μ (F ∘ S.T^[n]) = _
  rw [lintegral_comp' hm hp.measurable.aemeasurable, hp.map_eq]

/-- Integrating a forward-orbit sum costs exactly its cardinality. -/
theorem lintegral_forwardOrbit_sum {X : Type*} [MeasurableSpace X]
    (S : System X) (N : ℕ) (F : X → ℝ≥0∞) (hF : AEMeasurable F S.μ) :
    ∫⁻ x, ∑ j ∈ Finset.Icc (-(N : ℤ)) 0, F (S.T^[(-j).toNat] x) ∂S.μ =
      (N + 1 : ℕ) * ∫⁻ x, F x ∂S.μ := by
  have hcomp (j : ℤ) : AEMeasurable (fun x => F (S.T^[(-j).toNat] x)) S.μ := by
    have hp := S.measurePreserving_iterate (-j).toNat
    have hm : AEMeasurable F (S.μ.map S.T^[(-j).toNat]) := by
      rw [hp.map_eq]; exact hF
    exact hm.comp_measurable hp.measurable
  rw [lintegral_finsetSum' _ (fun j _ => hcomp j)]
  simp_rw [lintegral_comp_forwardIterate S _ F hF]
  have hcard : (Finset.Icc (-(N : ℤ)) 0).card = N + 1 := by
    rw [Int.card_Icc]
    omega
  simp [Finset.sum_const, nsmul_eq_mul, hcard]

#print axioms convolution_forwardOrbitCutoff
#print axioms variation_forwardOrbitCutoff
#print axioms lintegral_forwardOrbit_sum
end
end FractionalPrimes.Final
