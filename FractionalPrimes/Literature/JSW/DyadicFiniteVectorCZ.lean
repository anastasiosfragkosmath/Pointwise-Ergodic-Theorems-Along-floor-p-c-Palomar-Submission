module

public import FractionalPrimes.Literature.JSW.DyadicFiniteVectorL2BadSeries
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The finite-vector dyadic Calderón–Zygmund decomposition

This packages the checked vector-valued good-part estimates, mean-zero and
support properties of the bad pieces, and their convergence in both `L¹` and
`L²` into the exact decomposition used in the JSW proof.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Finite-vector dyadic Calderón–Zygmund decomposition at height `cutoff`.

The selected cells are the maximal dyadic cells on which the average of
`‖f‖` exceeds `λ`.  The good part and the bad pieces are defined by the
standard cell-average construction.  The first estimate is expressed in
`ENNReal`, where it is the measure estimate for the countable disjoint union
of the selected cells.  The series summability clauses assert convergence in
the corresponding Bochner `L¹` and `L²` spaces. -/
theorem dyadicCZDecomposition {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    {f : ℝ → H} (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {cutoff : ℝ} (hcutoff : 0 < cutoff) :
    Set.PairwiseDisjoint (dyadicVectorMaximalBadCells f cutoff)
      (fun q => dyadicInterval q.1 q.2) ∧
    (∑' q : dyadicVectorMaximalBadCells f cutoff,
      ENNReal.ofReal ((2 : ℝ) ^ q.1.1)) ≤
        ENNReal.ofReal ((∫ x, ‖f x‖ ∂volume) / cutoff) ∧
    (∀ᵐ x ∂volume, ‖dyadicVectorGoodPart f cutoff x‖ ≤ 2 * cutoff) ∧
    (∫ x, ‖dyadicVectorGoodPart f cutoff x‖ ∂volume) ≤
      ∫ x, ‖f x‖ ∂volume ∧
    (∫ x, ‖dyadicVectorGoodPart f cutoff x‖ ^ 2 ∂volume) ≤
      2 * cutoff * ∫ x, ‖f x‖ ∂volume ∧
    (∀ q : dyadicVectorMaximalBadCells f cutoff, ∀ x : ℝ,
      x ∉ dyadicInterval q.1.1 q.1.2 →
        dyadicVectorBadPiece f q.1.1 q.1.2 x = 0) ∧
    (∀ q : dyadicVectorMaximalBadCells f cutoff,
      ∫ x, dyadicVectorBadPiece f q.1.1 q.1.2 x ∂volume = 0) ∧
    (∑' q : dyadicVectorMaximalBadCells f cutoff,
      ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume) ≤
        2 * ∫ x, ‖f x‖ ∂volume ∧
    Summable (fun q : dyadicVectorMaximalBadCells f cutoff =>
      (integrable_dyadicVectorBadPiece hf q.1.1 q.1.2).toL1
        (dyadicVectorBadPiece f q.1.1 q.1.2)) ∧
    Summable (fun q : dyadicVectorMaximalBadCells f cutoff =>
      (memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
        (dyadicVectorBadPiece f q.1.1 q.1.2)) ∧
    (∀ x : ℝ, f x = dyadicVectorGoodPart f cutoff x +
      ∑' q : dyadicVectorMaximalBadCells f cutoff,
        dyadicVectorBadPiece f q.1.1 q.1.2 x) := by
  classical
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  refine ⟨dyadicVectorMaximalBadCells_pairwiseDisjoint f cutoff, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact dyadicVectorMaximalBadCells_sum_length_le hf hcutoff
  · exact dyadicVectorGoodPart_norm_le_two_ae hf hcutoff
  · exact integral_norm_dyadicVectorGoodPart_le hf hcutoff
  · exact integral_norm_sq_dyadicVectorGoodPart_le hf hcutoff
  · intro q x hx
    exact dyadicVectorBadPiece_eq_zero_of_not_mem f q.1.1 q.1.2 hx
  · intro q
    exact integral_dyadicVectorBadPiece_eq_zero hf q.1.1 q.1.2
  · exact dyadicVectorBadPieces_l1_tsum_le_two hf (t := cutoff)
  · exact dyadicVectorBadPieces_l1_summableLp hf (t := cutoff)
  · exact dyadicVectorBadPieces_l2_summable hf hf₂ (t := cutoff)
  · intro x
    exact dyadicVectorGoodPart_add_badPieces_eq x

end

end FractionalPrimes.Literature.JSW

#print axioms FractionalPrimes.Literature.JSW.dyadicCZDecomposition

end
