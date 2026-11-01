module

public import FractionalPrimes.Literature.JSW.RoughSquareNormalizedDecay
public import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt

/-! Identify a shifted summable reconstruction by its centered resolution. -/

@[expose] public section
open Filter
open scoped Topology
namespace FractionalPrimes.Literature.JSW

theorem roughSquareSeries_coordinate_identification
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (P : E →L[ℝ] G) (a : ℤ → E) (g : ℤ → G) (v : G) (k : ℤ)
    (ha : Summable a) (hcoord : ∀ j, P (a j) = g (k+j))
    (hresolution : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g n)
      atTop (𝓝 v)) :
    P (∑' j : ℤ, a j) = v := by
  have hshift : HasSum (fun j : ℤ => g (k+j)) (P (∑' j : ℤ, a j)) :=
    (P.hasSum ha.hasSum).congr_fun (fun j => (hcoord j).symm)
  have hg : HasSum g (P (∑' j : ℤ, a j)) :=
    (Equiv.addLeft k).hasSum_iff.mp hshift
  have hsym : HasSum g (P (∑' j : ℤ, a j)) (SummationFilter.symmetricIcc ℤ) :=
    hg.mono_left (SummationFilter.symmetricIcc ℤ).le_atTop
  exact tendsto_nhds_unique (SummationFilter.hasSum_symmetricIcc_iff.mp hsym) hresolution

#print axioms roughSquareSeries_coordinate_identification
end FractionalPrimes.Literature.JSW
end
