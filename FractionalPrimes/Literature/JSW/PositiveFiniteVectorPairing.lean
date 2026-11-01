module

public import FractionalPrimes.Literature.JSW.PositiveFiniteAdjointPairing
public import FractionalPrimes.Literature.JSW.PositiveVectorDualityTransfer
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Coordinate form of finite-vector `Lᵖ` pairings
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The integral pairing of finite complex Euclidean vectors is the sum
of their scalar coordinate pairings at conjugate exponents. -/
theorem integral_finiteEuclidean_inner_eq_sum
    {ι : Type*} [Fintype ι]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (F : ℝ → EuclideanSpace ℂ ι)
    (G : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume)
    (hG : MemLp G (ENNReal.ofReal q) volume) :
    (∫ x, inner ℂ (F x) (G x) ∂volume) =
      ∑ i, ∫ x, inner ℂ (F x i) (G x i) ∂volume := by
  classical
  have hInt (i : ι) :
      Integrable (fun x => inner ℂ (F x i) (G x i)) volume :=
    integrable_inner_of_memLp hpq (hF.eval_piLp i) (hG.eval_piLp i)
  calc
    (∫ x, inner ℂ (F x) (G x) ∂volume) =
        ∫ x, ∑ i, inner ℂ (F x i) (G x i) ∂volume := by
          simp only [PiLp.inner_apply]
    _ = ∑ i, ∫ x, inner ℂ (F x i) (G x i) ∂volume := by
      rw [integral_finset_sum Finset.univ (fun i _ => hInt i)]

/-- A coordinatewise raw probability-convolution identity yields the
exact finite-vector adjoint pairing required for lower-exponent duality. -/
theorem finiteProbabilityConvolution_vector_adjoint_pairing
    {ι : Type*} [Fintype ι]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsFiniteMeasure (μ i))
    (F U : ℝ → EuclideanSpace ℂ ι)
    (G V : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume)
    (hU : MemLp U (ENNReal.ofReal p) volume)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hV : MemLp V (ENNReal.ofReal q) volume)
    (hUraw : ∀ i, (fun x => U x i) =ᵐ[volume]
      (fun x => jswConvolution (μ i) (fun y => F y i) x))
    (hVraw : ∀ i, (fun x => V x i) =ᵐ[volume]
      (fun x => ∫ y, G (x + y) i ∂(μ i))) :
    (∫ x, inner ℂ (U x) (G x) ∂volume) =
      ∫ x, inner ℂ (F x) (V x) ∂volume := by
  classical
  have hraw := finiteProbabilityConvolution_adjoint_inner_pairing
    hpq μ hμ (fun i x => F x i) (fun i x => G x i)
    (fun i => hF.eval_piLp i) (fun i => hG.eval_piLp i)
  rw [integral_finiteEuclidean_inner_eq_sum hpq U G hU hG,
    integral_finiteEuclidean_inner_eq_sum hpq F V hF hV]
  calc
    (∑ i, ∫ x, inner ℂ (U x i) (G x i) ∂volume) =
        ∑ i, ∫ x, inner ℂ
          (jswConvolution (μ i) (fun y => F y i) x) (G x i) ∂volume := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [hUraw i] with x hx
      rw [hx]
    _ = ∑ i, ∫ x, inner ℂ (F x i)
          (∫ y, G (x + y) i ∂(μ i)) ∂volume := hraw
    _ = ∑ i, ∫ x, inner ℂ (F x i) (V x i) ∂volume := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [hVraw i] with x hx
      rw [hx]

/-- Subtracting two positive finite-family pairings gives the adjoint
pairing for their signed difference, with no new measure-theoretic
side conditions. -/
theorem finiteProbabilityDifference_vector_adjoint_pairing
    {ι : Type*} [Fintype ι]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (μσ μψ : ι → Measure ℝ)
    (hμσ : ∀ i, IsFiniteMeasure (μσ i))
    (hμψ : ∀ i, IsFiniteMeasure (μψ i))
    (F : ℝ → EuclideanSpace ℂ ι)
    (Uσ Uψ : ℝ → EuclideanSpace ℂ ι)
    (G : ℝ → EuclideanSpace ℂ ι)
    (Vσ Vψ : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume)
    (hUσ : MemLp Uσ (ENNReal.ofReal p) volume)
    (hUψ : MemLp Uψ (ENNReal.ofReal p) volume)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hVσ : MemLp Vσ (ENNReal.ofReal q) volume)
    (hVψ : MemLp Vψ (ENNReal.ofReal q) volume)
    (hUσraw : ∀ i, (fun x => Uσ x i) =ᵐ[volume]
      (fun x => jswConvolution (μσ i) (fun y => F y i) x))
    (hUψraw : ∀ i, (fun x => Uψ x i) =ᵐ[volume]
      (fun x => jswConvolution (μψ i) (fun y => F y i) x))
    (hVσraw : ∀ i, (fun x => Vσ x i) =ᵐ[volume]
      (fun x => ∫ y, G (x + y) i ∂(μσ i)))
    (hVψraw : ∀ i, (fun x => Vψ x i) =ᵐ[volume]
      (fun x => ∫ y, G (x + y) i ∂(μψ i))) :
    (∫ x, inner ℂ (Uσ x - Uψ x) (G x) ∂volume) =
      ∫ x, inner ℂ (F x) (Vσ x - Vψ x) ∂volume := by
  have hσ := finiteProbabilityConvolution_vector_adjoint_pairing
    hpq μσ hμσ F Uσ G Vσ hF hUσ hG hVσ hUσraw hVσraw
  have hψ := finiteProbabilityConvolution_vector_adjoint_pairing
    hpq μψ hμψ F Uψ G Vψ hF hUψ hG hVψ hUψraw hVψraw
  have hIntUσ := integrable_inner_of_memLp hpq hUσ hG
  have hIntUψ := integrable_inner_of_memLp hpq hUψ hG
  have hIntVσ := integrable_inner_of_memLp hpq hF hVσ
  have hIntVψ := integrable_inner_of_memLp hpq hF hVψ
  calc
    (∫ x, inner ℂ (Uσ x - Uψ x) (G x) ∂volume) =
        ∫ x, (inner ℂ (Uσ x) (G x) - inner ℂ (Uψ x) (G x)) ∂volume := by
          simp only [inner_sub_left]
    _ = (∫ x, inner ℂ (Uσ x) (G x) ∂volume) -
          ∫ x, inner ℂ (Uψ x) (G x) ∂volume :=
      integral_sub hIntUσ hIntUψ
    _ = (∫ x, inner ℂ (F x) (Vσ x) ∂volume) -
          ∫ x, inner ℂ (F x) (Vψ x) ∂volume := by rw [hσ, hψ]
    _ = ∫ x, (inner ℂ (F x) (Vσ x) - inner ℂ (F x) (Vψ x)) ∂volume :=
      (integral_sub hIntVσ hIntVψ).symm
    _ = ∫ x, inner ℂ (F x) (Vσ x - Vψ x) ∂volume := by
      simp only [inner_sub_right]

#print axioms integral_finiteEuclidean_inner_eq_sum
#print axioms finiteProbabilityConvolution_vector_adjoint_pairing
#print axioms finiteProbabilityDifference_vector_adjoint_pairing

end

end FractionalPrimes.Literature.JSW

end
