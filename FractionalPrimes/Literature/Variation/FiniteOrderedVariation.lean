module

public import FractionalPrimes.Literature.Variation.FiniteChainVariation

/-!
# Finite ordered variation bounds

For a finite index set, each increment is bounded by twice the maximum of
the sequence.  The number of increments is at most the cardinality of the
index set, giving a finite ENNReal bound for the all-chain variation.  This
is the finite-output interface needed by layer-cake interpolation.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open scoped ENNReal

/-- The maximum norm of a complex sequence on a finite index set.  The
empty-set value is zero. -/
noncomputable def finiteOrderedSequenceMaxNorm
    {I : Type*} [Fintype I] (u : I → ℂ) : ℝ := by
  classical
  exact if hI : Nonempty I then
    (Finset.univ : Finset I).sup' (Finset.univ_nonempty_iff.mpr hI)
      (fun i => ‖u i‖)
  else 0

/-- A single finite-chain variation is bounded by the cardinality factor
times twice the maximum pointwise norm. -/
theorem finiteChainVariation_le_two_card_rpow_maxNorm
    {I : Type*} [LinearOrder I] [Fintype I] (r : ℝ) (u : I → ℂ)
    (hr : 0 < r) {length : ℕ} (chain : StrictOrderedChain I length) :
    finiteChainVariation r u chain ≤
      (2 : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞).rpow r⁻¹ *
        ENNReal.ofReal (finiteOrderedSequenceMaxNorm u) := by
  classical
  let M : ℝ := finiteOrderedSequenceMaxNorm u
  have hM : 0 ≤ M := by
    dsimp [M, finiteOrderedSequenceMaxNorm]
    split_ifs with hI
    · have hUniv : (Finset.univ : Finset I).Nonempty :=
        Finset.univ_nonempty_iff.mpr hI
      obtain ⟨i⟩ := hI
      have hi : ‖u i‖ ≤ (Finset.univ : Finset I).sup'
          hUniv (fun j => ‖u j‖) :=
        Finset.le_sup' (s := (Finset.univ : Finset I))
          (f := fun j : I => ‖u j‖) (Finset.mem_univ i)
      exact le_trans (norm_nonneg _) hi
    · exact le_rfl
  have hMbound (i : I) : ‖u i‖ ≤ M := by
    dsimp [M, finiteOrderedSequenceMaxNorm]
    split_ifs with hI
    · exact Finset.le_sup' (s := Finset.univ) (f := fun j : I => ‖u j‖)
        (Finset.mem_univ i)
    · exact False.elim (hI ⟨i⟩)
  have hlen : length + 1 ≤ Fintype.card I := by
    have hcard := Fintype.card_le_of_injective chain.point chain.strictMono.injective
    simpa using hcard
  have hlen' : length ≤ Fintype.card I := by omega
  have htwononneg : 0 ≤ (2 : ℝ) * M := by positivity
  let cap : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) * M)
  have hstep (i : Fin length) :
      ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ≤ 2 * M := by
    calc
      ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ≤
          ‖u (chain.point i.succ)‖ + ‖u (chain.point i.castSucc)‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hMbound _) (hMbound _)
      _ = 2 * M := by ring
  have hterm (i : Fin length) :
      (ENNReal.ofReal ‖u (chain.point i.succ) -
        u (chain.point i.castSucc)‖).rpow r ≤ cap.rpow r := by
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hstep i)) hr.le
  have hsum :
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (chain.point i.succ) -
          u (chain.point i.castSucc)‖).rpow r) ≤
        (Fintype.card I : ℝ≥0∞) * cap.rpow r := by
    calc
      _ ≤ ∑ i : Fin length, cap.rpow r :=
        Finset.sum_le_sum fun i hi => hterm i
      _ = (length : ℝ≥0∞) * cap.rpow r := by simp
      _ ≤ (Fintype.card I : ℝ≥0∞) * cap.rpow r :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlen') zero_le
  have hroot :
      ((Fintype.card I : ℝ≥0∞) * cap.rpow r).rpow r⁻¹ =
        (2 : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞).rpow r⁻¹ *
          ENNReal.ofReal M := by
    calc
      _ = (Fintype.card I : ℝ≥0∞).rpow r⁻¹ *
          (cap.rpow r).rpow r⁻¹ :=
        ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le)
      _ = (Fintype.card I : ℝ≥0∞).rpow r⁻¹ * cap.rpow (r * r⁻¹) := by
        congr 1
        exact (ENNReal.rpow_mul cap r r⁻¹).symm
      _ = (Fintype.card I : ℝ≥0∞).rpow r⁻¹ * cap := by
        rw [mul_inv_cancel₀ hr.ne']
        congr 1
        exact ENNReal.rpow_one cap
      _ = (2 : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞).rpow r⁻¹ *
            ENNReal.ofReal M := by
        dsimp [cap]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
        ac_rfl
  calc
    finiteChainVariation r u chain ≤
        ((Fintype.card I : ℝ≥0∞) * cap.rpow r).rpow r⁻¹ := by
          unfold finiteChainVariation
          exact ENNReal.rpow_le_rpow hsum (inv_nonneg.mpr hr.le)
    _ = (2 : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞).rpow r⁻¹ *
          ENNReal.ofReal (finiteOrderedSequenceMaxNorm u) := by
          rw [hroot]

/-- The ordered variation over finite `I` has the exact finite bound
`2 * card(I)^(1/r) * max_i ‖u i‖`. -/
theorem orderedRVariation_le_two_card_rpow_maxNorm
    {I : Type*} [LinearOrder I] [Fintype I] (r : ℝ) (u : I → ℂ)
    (hr : 0 < r) :
    orderedRVariation r u ≤
      (2 : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞).rpow r⁻¹ *
        ENNReal.ofReal (finiteOrderedSequenceMaxNorm u) := by
  unfold orderedRVariation
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  exact finiteChainVariation_le_two_card_rpow_maxNorm r u hr chain

/-- Ordered variation on a finite index set is finite for every positive
exponent. -/
theorem orderedRVariation_lt_top_of_pos
    {I : Type*} [LinearOrder I] [Fintype I] (r : ℝ) (u : I → ℂ)
    (hr : 0 < r) : orderedRVariation r u < ∞ := by
  have hcard : (Fintype.card I : ℝ≥0∞).rpow r⁻¹ < ∞ := by
    exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hr.le) (by simp)
  have hmax : ENNReal.ofReal (finiteOrderedSequenceMaxNorm u) < ∞ := ENNReal.ofReal_lt_top
  have hbound :
      (2 : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞).rpow r⁻¹ *
        ENNReal.ofReal (finiteOrderedSequenceMaxNorm u) < ∞ := by
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hcard) hmax
  exact (orderedRVariation_le_two_card_rpow_maxNorm r u hr).trans_lt hbound

/-- If a finite index set has fewer than two points, its increment
variation is zero. -/
theorem orderedRVariation_eq_zero_of_card_le_one
    {I : Type*} [LinearOrder I] [Fintype I] (r : ℝ) (u : I → ℂ)
    (hr : 0 < r) (hcard : Fintype.card I ≤ 1) : orderedRVariation r u = 0 := by
  classical
  unfold orderedRVariation
  apply le_antisymm
  · apply iSup_le
    intro length
    apply iSup_le
    intro chain
    have hlen : length + 1 ≤ Fintype.card I := by
      have h := Fintype.card_le_of_injective chain.point chain.strictMono.injective
      simpa using h
    have hzero : length = 0 := by omega
    subst length
    have hzero : finiteChainVariation r u chain = 0 := by
      unfold finiteChainVariation
      rw [Fin.sum_univ_zero]
      exact ENNReal.zero_rpow_of_pos (inv_pos.mpr hr)
    simpa [hzero]
  · exact zero_le

/-- Empty finite index sets have zero ordered variation. -/
theorem orderedRVariation_eq_zero_of_isEmpty
    {I : Type*} [LinearOrder I] [Fintype I] [IsEmpty I]
    (r : ℝ) (u : I → ℂ) (hr : 0 < r) : orderedRVariation r u = 0 := by
  apply orderedRVariation_eq_zero_of_card_le_one r u hr
  simp

end FractionalPrimes.Literature.Variation
