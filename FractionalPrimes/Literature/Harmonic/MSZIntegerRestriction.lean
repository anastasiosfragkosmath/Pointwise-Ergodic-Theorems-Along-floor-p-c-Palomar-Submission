module

public import FractionalPrimes.Literature.Harmonic.UnweightedMSZEndpointBound
public import FractionalPrimes.VariationBlocks

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.Harmonic
open FractionalPrimes.Literature.MSZ FractionalPrimes.Literature.Variation
noncomputable section

def integerMSZTime (N : Scale) : MSZTime :=
  ⟨(N.val : ℚ), N.val, N.property, 0, by simp⟩

theorem unweightedIntegerBlockVariation_le_msz
    (c : ℝ) (A : AdmissibleData)
    (hA : ∀ t, A.kernel t = interpolatedFloorPowerMSZKernel c t)
    (k : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    rVariationOn 2 (fun N => unweightedAverage integerShiftSystem c f N x)
        (Set.Icc (unweightedDyadicScale k) (unweightedDyadicScale (k + 1))) ≤
      mszSourceShortBlockVariation A (k : ℤ) f x := by
  classical
  unfold rVariationOn
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  split_ifs with hchain
  · let e : Fin (length + 1) → MSZShortBlockTime (k : ℤ) := fun i =>
      ⟨integerMSZTime (chain.index i), by
        have hlo : 2 ^ k ≤ (chain.index i).val := (hchain i).1
        have hhi : (chain.index i).val ≤ 2 ^ (k + 1) := (hchain i).2
        constructor
        · change (2 : ℚ) ^ (k : ℤ) ≤ ((chain.index i).val : ℚ)
          rw [zpow_natCast]
          exact_mod_cast hlo
        · change ((chain.index i).val : ℚ) ≤ (2 : ℚ) ^ ((k : ℤ) + 1)
          rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega, zpow_natCast]
          exact_mod_cast hhi⟩
    have he : StrictMono e := by
      intro i j hij
      change ((chain.index i).val : ℚ) < ((chain.index j).val : ℚ)
      exact_mod_cast chain.strictMono hij
    let d : StrictOrderedChain (MSZShortBlockTime (k : ℤ)) length := ⟨e, he⟩
    have hval (i : Fin (length + 1)) :
        mszShortBlockValue A (k : ℤ) f x (d.point i) =
          unweightedAverage integerShiftSystem c f (chain.index i) x := by
      change mszKernelAverage (A.kernel (integerMSZTime (chain.index i))) f x = _
      rw [hA]
      exact interpolatedMSZKernel_integer_average c _ _ (by simp [integerMSZTime]) f x
    have hbound := finiteChainVariation_le_orderedRVariation 2
      (mszShortBlockValue A (k : ℤ) f x) d
    simpa only [finiteChainVariation, chainVariation, hval,
      mszSourceShortBlockVariation, ENNReal.rpow_eq_pow] using hbound
  · exact bot_le

def unweightedShortVariationSquare (c : ℝ) (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  (∑' k : ℕ, (rVariationOn 2
    (fun N => unweightedAverage integerShiftSystem c f N x)
    (Set.Icc (unweightedDyadicScale k) (unweightedDyadicScale (k + 1)))).rpow 2).rpow
      (1 / 2 : ℝ)

theorem unweightedShortVariationSquare_le_msz
    (c : ℝ) (A : AdmissibleData)
    (hA : ∀ t, A.kernel t = interpolatedFloorPowerMSZKernel c t)
    (f : ℤ → ℂ) (x : ℤ) :
    unweightedShortVariationSquare c f x ≤ mszSourceShortVariation A f x := by
  classical
  let U := fun k : ℕ => rVariationOn 2
    (fun N => unweightedAverage integerShiftSystem c f N x)
    (Set.Icc (unweightedDyadicScale k) (unweightedDyadicScale (k + 1)))
  let V := fun k : ℤ => mszSourceShortBlockVariation A k f x
  change (ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num))
    (∑' k : ℕ, (U k).rpow 2) ≤ _
  rw [ENNReal.tsum_eq_iSup_nat, OrderIso.map_iSup]
  apply iSup_le
  intro n
  have hsum : (∑ k ∈ Finset.range n, (U k).rpow 2) ≤
      ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), (V j).rpow 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, (V (k : ℤ)).rpow 2 := by
        apply Finset.sum_le_sum
        intro k _
        exact ENNReal.rpow_le_rpow (unweightedIntegerBlockVariation_le_msz c A hA k f x)
          (by norm_num)
      _ = ∑ j ∈ (Finset.range n).image (fun k : ℕ => (k : ℤ)), (V j).rpow 2 := by
        symm
        apply Finset.sum_image
        intro i _ j _ hij
        exact Nat.cast_injective hij
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
          have hk' := Finset.mem_range.mp hk
          simp only [Finset.mem_Icc]
          constructor <;> omega
        · intro _ _ _
          exact bot_le
  have hroot := ENNReal.rpow_le_rpow hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hsource : (∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      (V j).rpow 2).rpow (1 / 2 : ℝ) ≤ mszSourceShortVariation A f x :=
    le_iSup (fun K : ℕ =>
      (∑ j ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (mszSourceShortBlockVariation A j f x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) n
  exact hroot.trans hsource

#print axioms unweightedShortVariationSquare_le_msz

end
end FractionalPrimes.Literature.Harmonic
