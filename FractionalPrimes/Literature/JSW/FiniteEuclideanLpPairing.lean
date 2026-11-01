module

public import FractionalPrimes.Literature.JSW.FiniteVectorLpAssembly
public import Mathlib.MeasureTheory.Function.L2Space

/-! Finite scalar adjoint pairings assemble into the actual Euclidean L2 pairing. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem finiteEuclideanLp_integral_pairing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T S : ι → Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ))
    (hpair : ∀ i (f g : Lp ℂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T i f : ℝ → ℂ) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S i g : ℝ → ℂ) x) ∂volume)
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (G : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure ℝ)) :
    (∫ x, inner ℝ ((finiteVectorLpAssembly 2 (fun i => T i F) : ℝ → EuclideanSpace ℂ ι) x)
      (G x) ∂volume) =
    ∫ x, inner ℝ (F x) ((∑ i, S i
      ((PiLp.proj 2 (fun _ : ι => ℂ) i : EuclideanSpace ℂ ι →L[ℝ] ℂ).compLpL 2 volume G) :
        Lp ℂ 2 volume) x) ∂volume := by
  let L := fun i : ι => (PiLp.proj 2 (fun _ : ι => ℂ) i : EuclideanSpace ℂ ι →L[ℝ] ℂ)
  let g := fun i => (L i).compLpL 2 volume G
  have hg (i : ι) : (g i : ℝ → ℂ) =ᵐ[volume] (fun x => G x i) := (L i).coeFn_compLpL G
  have hv := finiteVectorLpAssembly_ae_eq 2 (fun i => T i F)
  have hleft : (fun x => inner ℝ ((finiteVectorLpAssembly 2 (fun i => T i F) :
      ℝ → EuclideanSpace ℂ ι) x) (G x)) =ᵐ[volume]
      (fun x => ∑ i, inner ℝ ((T i F : ℝ → ℂ) x) ((g i : ℝ → ℂ) x)) := by
    filter_upwards [hv, ae_all_iff.mpr hg] with x hx hgi
    rw [hx]
    simp only [real_inner_eq_re_inner ℂ, PiLp.inner_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hgi i]
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun i => S i (g i))
  have hright : (fun x => inner ℝ (F x) ((∑ i, S i (g i) : Lp ℂ 2 volume) x)) =ᵐ[volume]
      (fun x => ∑ i, inner ℝ (F x) ((S i (g i) : ℝ → ℂ) x)) := by
    filter_upwards [hsum] with x hx
    rw [hx]
    simp only [Finset.sum_apply, inner_sum]
  rw [integral_congr_ae hleft]
  change (∫ x, ∑ i, inner ℝ ((T i F : ℝ → ℂ) x) ((g i : ℝ → ℂ) x) ∂volume) =
    ∫ x, inner ℝ (F x) ((∑ i, S i (g i) : Lp ℂ 2 volume) x) ∂volume
  rw [integral_congr_ae hright,
    integral_finsetSum Finset.univ (fun i _ => MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (T i F) (g i)),
    integral_finsetSum Finset.univ (fun i _ => MeasureTheory.L2.integrable_inner (𝕜 := ℝ) F (S i (g i)))]
  exact Finset.sum_congr rfl fun i _ => hpair i F (g i)

#print axioms finiteEuclideanLp_integral_pairing
end
end FractionalPrimes.Literature.JSW
end
