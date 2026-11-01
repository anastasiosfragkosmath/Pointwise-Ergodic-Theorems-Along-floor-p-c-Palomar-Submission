module

public import FractionalPrimes.ArithmeticBasicsCore
public import FractionalPrimes.Literature.MSZ.LocalizedGridProjectionL2Energy
public import FractionalPrimes.Literature.MSZ.LocalizedGridProjectionTail

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open Filter
open scoped ENNReal Topology

noncomputable section

private theorem msz_sum_shifted_symmetricIcc_eq_Icc
    {E : Type*} [AddCommMonoid E] (u : ℤ → E) (k : ℤ) (J : ℕ) :
    (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u (k + j)) =
      ∑ h ∈ Finset.Icc (k - (J : ℤ)) (k + (J : ℤ)), u h := by
  classical
  apply Finset.sum_bij (fun j _ => k + j)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj j' hj' h
    exact add_left_cancel h
  · intro h hh
    simp only [Finset.mem_Icc] at hh
    refine ⟨h - k, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    rfl

/-- For a nonnegative shift by `m`, the shifted interval differs from the
centered interval by the explicitly indexed positive and negative boundary
blocks. The identity is stated once the windows overlap, `m ≤ J`. -/
private theorem msz_shifted_symmetricIcc_sum_formula
    {E : Type*} [AddCommGroup E] (u : ℤ → E) (m J : ℕ) (hmJ : m ≤ J) :
    (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u ((m : ℤ) + j)) =
      (∑ h ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u h) +
        (∑ r ∈ Finset.range m, u ((J + 1 + r : ℕ) : ℤ)) -
        ∑ r ∈ Finset.range m, u (-((J - m + 1 + r : ℕ) : ℤ)) := by
  classical
  let F : Finset ℤ := Finset.Icc (-(J : ℤ)) (J : ℤ)
  let Eshift : Finset ℤ :=
    Finset.Icc ((m : ℤ) - (J : ℤ)) ((m : ℤ) + (J : ℤ))
  let L : Finset ℤ := Finset.Ico (-(J : ℤ)) ((m : ℤ) - (J : ℤ))
  let R : Finset ℤ :=
    Finset.Ico ((J : ℤ) + 1) (((J + m : ℕ) : ℤ) + 1)
  have hEshift : Eshift = (F \ L) ∪ R := by
    ext h
    simp only [Eshift, F, L, R, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_Icc, Finset.mem_Ico]
    push_cast
    omega
  have hLsub : L ⊆ F := by
    intro h hh
    simp only [L, F, Finset.mem_Ico, Finset.mem_Icc] at hh ⊢
    push_cast at hh ⊢
    constructor <;> omega
  have hDisjoint : Disjoint (F \ L) R := by
    apply Finset.disjoint_left.mpr
    intro h hhF hhR
    simp only [F, L, R, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ico] at hhF hhR
    push_cast at hhF hhR
    omega
  have hSumEshift :
      (∑ h ∈ Eshift, u h) =
        (∑ h ∈ F \ L, u h) + ∑ h ∈ R, u h := by
    rw [hEshift, Finset.sum_union hDisjoint]
  have hSumF :
      (∑ h ∈ F, u h) =
        (∑ h ∈ F \ L, u h) + ∑ h ∈ L, u h :=
    (Finset.sum_sdiff (f := u) hLsub).symm
  have hSumFminusL :
      (∑ h ∈ F \ L, u h) = (∑ h ∈ F, u h) - ∑ h ∈ L, u h := by
    calc
      (∑ h ∈ F \ L, u h) =
          ((∑ h ∈ F \ L, u h) + ∑ h ∈ L, u h) -
            ∑ h ∈ L, u h := by abel
      _ = (∑ h ∈ F, u h) - ∑ h ∈ L, u h := by rw [← hSumF]
  have hRsum :
      (∑ h ∈ R, u h) =
        ∑ r ∈ Finset.range m, u ((J + 1 + r : ℕ) : ℤ) := by
    simpa [R] using
      (sum_positive_Ico_eq_sum_range u J (J + m) (Nat.le_add_right J m))
  have hLsum :
      (∑ h ∈ L, u h) =
        ∑ r ∈ Finset.range m, u (-((J - m + 1 + r : ℕ) : ℤ)) := by
    have hLinterval :
        L = Finset.Ico (-(J : ℤ)) (-((J - m : ℕ) : ℤ)) := by
      ext h
      simp only [L, Finset.mem_Ico]
      push_cast
      omega
    rw [hLinterval]
    simpa [Nat.sub_sub_self hmJ] using
      (sum_negative_Ico_eq_sum_range u (J - m) J (Nat.sub_le J m))
  calc
    (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u ((m : ℤ) + j)) =
        ∑ h ∈ Eshift, u h := by
      exact msz_sum_shifted_symmetricIcc_eq_Icc u (m : ℤ) J
    _ = (∑ h ∈ F \ L, u h) + ∑ h ∈ R, u h := hSumEshift
    _ = (∑ h ∈ F, u h) - ∑ h ∈ L, u h + ∑ h ∈ R, u h := by
      rw [hSumFminusL]
    _ = (∑ h ∈ F, u h) +
          (∑ r ∈ Finset.range m, u ((J + 1 + r : ℕ) : ℤ)) -
          ∑ r ∈ Finset.range m, u (-((J - m + 1 + r : ℕ) : ℤ)) := by
      rw [hRsum, hLsum]
      abel

private theorem msz_sum_leftShift_eq_reflectedRightShift
    {E : Type*} [AddCommMonoid E] (u : ℤ → E) (m J : ℕ) :
    (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u (-(m : ℤ) + j)) =
      ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u (-((m : ℤ) + j)) := by
  classical
  apply Finset.sum_bij (fun j _ => -j)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj j' hj' h
    exact Int.neg_inj.mp h
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨-j, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · simp
  · intro j hj
    congr 1
    ring

private theorem msz_nat_sub_add_tendsto_atTop (m c : ℕ) :
    Tendsto (fun J : ℕ => J - m + c) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro N
  filter_upwards [Filter.eventually_ge_atTop (N + m)] with J hJ
  omega

/-- The finite boundary blocks of a right-shifted symmetric window tend to
zero in any normed additive group when both projection tails do. -/
private theorem msz_shiftedWindowDifference_nonneg_tendsto
    {E : Type*} [NormedAddCommGroup E] (u : ℤ → E) (m : ℕ)
    (hpos : Tendsto (fun n : ℕ => u (n : ℤ)) atTop (𝓝 0))
    (hneg : Tendsto (fun n : ℕ => u (-(n : ℤ))) atTop (𝓝 0)) :
    Tendsto
      (fun J : ℕ =>
        ‖(∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u ((m : ℤ) + j)) -
          ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u j‖)
      atTop (𝓝 0) := by
  let pos : ℕ → E := fun J =>
    ∑ r ∈ Finset.range m, u ((J + 1 + r : ℕ) : ℤ)
  let neg : ℕ → E := fun J =>
    ∑ r ∈ Finset.range m, u (-((J - m + 1 + r : ℕ) : ℤ))
  have hposBoundary : Tendsto pos atTop (𝓝 0) := by
    have hsum : Tendsto pos atTop
        (𝓝 (∑ r ∈ Finset.range m, (0 : E))) := by
      apply tendsto_finsetSum
      intro r hr
      have hIndex : Tendsto (fun J : ℕ => J + 1 + r) atTop atTop := by
        apply Filter.tendsto_atTop.2
        intro N
        filter_upwards [Filter.eventually_ge_atTop N] with J hJ
        omega
      exact hpos.comp hIndex
    simpa using hsum
  have hnegBoundary : Tendsto neg atTop (𝓝 0) := by
    have hsum : Tendsto neg atTop
        (𝓝 (∑ r ∈ Finset.range m, (0 : E))) := by
      apply tendsto_finsetSum
      intro r hr
      have hIndex : Tendsto (fun J : ℕ => J - m + 1 + r) atTop atTop :=
        by simpa only [Nat.add_assoc] using msz_nat_sub_add_tendsto_atTop m (1 + r)
      exact hneg.comp hIndex
    simpa using hsum
  have hboundary : Tendsto (fun J => pos J - neg J) atTop (𝓝 0) := by
    simpa using hposBoundary.sub hnegBoundary
  let difference : ℕ → E := fun J =>
    (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u ((m : ℤ) + j)) -
      ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u j
  have hEq : difference =ᶠ[atTop] fun J => pos J - neg J := by
    filter_upwards [Filter.eventually_ge_atTop m] with J hJ
    dsimp [difference, pos, neg]
    rw [msz_shifted_symmetricIcc_sum_formula u m J hJ]
    abel
  have hDifference : Tendsto difference atTop (𝓝 0) :=
    Tendsto.congr' hEq.symm hboundary
  exact (tendsto_zero_iff_norm_tendsto_zero).1 hDifference

/-- For each fixed integer shift, the shifted and centered symmetric windows
have the same limit. Their difference consists only of `2 * |k|` boundary
terms, whose indices escape to the two tails. -/
theorem mszLocalizedShiftedSymmetricWindowComparison
    (A : AdmissibleData) (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) (k : ℤ) :
    Tendsto
      (fun J : ℕ =>
        ‖(∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
              A.projectionsL2 (k + j) f) -
          ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f‖)
      atTop (𝓝 0) := by
  obtain ⟨hposNorm, hnegNorm⟩ :=
    mszLocalizedProjectionL2Norm_tendsto_zero A f
  have hpos : Tendsto (fun n : ℕ => A.projectionsL2 (n : ℤ) f)
      atTop (𝓝 0) := (tendsto_zero_iff_norm_tendsto_zero).2 hposNorm
  have hneg : Tendsto (fun n : ℕ => A.projectionsL2 (-(n : ℤ)) f)
      atTop (𝓝 0) := (tendsto_zero_iff_norm_tendsto_zero).2 hnegNorm
  by_cases hk : 0 ≤ k
  · let m : ℕ := k.toNat
    have hmcast : (m : ℤ) = k := Int.toNat_of_nonneg hk
    have h := msz_shiftedWindowDifference_nonneg_tendsto
      (fun h : ℤ => A.projectionsL2 h f) m hpos hneg
    simpa [hmcast] using h
  · have hk' : k < 0 := lt_of_not_ge hk
    let m : ℕ := (-k).toNat
    have hmcast : (m : ℤ) = -k :=
      Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hk'))
    have hkcast : k = -(m : ℤ) := by omega
    let u : ℤ → lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) :=
      fun h => A.projectionsL2 (-h) f
    have huPos : Tendsto (fun n : ℕ => u (n : ℤ)) atTop (𝓝 0) := by
      change Tendsto
        (fun n : ℕ => A.projectionsL2 (-(n : ℤ)) f) atTop (𝓝 0)
      exact hneg
    have huNeg : Tendsto (fun n : ℕ => u (-(n : ℤ))) atTop (𝓝 0) := by
      change Tendsto
        (fun n : ℕ => A.projectionsL2 (-(-(n : ℤ))) f) atTop (𝓝 0)
      simpa using hpos
    have hright := msz_shiftedWindowDifference_nonneg_tendsto u m huPos huNeg
    have hshift (J : ℕ) :
        (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 (k + j) f) =
          ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u ((m : ℤ) + j) := by
      rw [hkcast]
      dsimp [u]
      exact msz_sum_leftShift_eq_reflectedRightShift
        (fun h : ℤ => A.projectionsL2 h f) m J
    have hcenter (J : ℕ) :
        (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f) =
          ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u j := by
      simpa [u] using
        (msz_sum_leftShift_eq_reflectedRightShift
          (fun h : ℤ => A.projectionsL2 h f) 0 J)
    have hseq :
        (fun J : ℕ =>
          ‖(∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
                A.projectionsL2 (k + j) f) -
            ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f‖) =
        (fun J : ℕ =>
          ‖(∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u ((m : ℤ) + j)) -
            ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), u j‖) := by
      funext J
      rw [hshift J, hcenter J]
    rw [hseq]
    exact hright

end

end FractionalPrimes.Literature.MSZ

end
