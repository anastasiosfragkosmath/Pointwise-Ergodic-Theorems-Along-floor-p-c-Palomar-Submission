module

public import FractionalPrimes.Literature.Uniformity.ArchimedeanTwist
public import FractionalPrimes.Literature.Uniformity.VariationCalculusC1

/-!
# Variation of the archimedean twist on short intervals

This file proves the twist-variation clause of `lu:elementary-growth` and
its residue-class consequence, using the exact inhomogeneous variation from
`lu:ap-tv`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem orderedTotalVariation_mono_of_subset {A B : Set ℤ}
    (hAB : A ⊆ B) (g : ℤ → ℂ) :
    orderedTotalVariation A g ≤ orderedTotalVariation B g := by
  unfold orderedTotalVariation
  refine iSup_le fun F => ?_
  let G : {G : Finset ℤ // ∀ n ∈ G, n ∈ B} :=
    ⟨F.1, fun n hn => hAB (F.2 n hn)⟩
  exact le_iSup_of_le G le_rfl

private theorem archimedeanTwist_intervalNormSup_eq_one {X H T : ℝ}
    (hH : 0 < H) :
    intervalNormSup X (X + H) (archimedeanTwist T) = 1 := by
  have hrange :
      Set.range (fun t : Set.Icc X (X + H) => ‖archimedeanTwist T t‖) = {1} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact norm_archimedeanTwist_eq_one T t
    · intro hy
      have hy' : y = 1 := by simpa using hy
      subst y
      refine ⟨⟨X, ⟨le_rfl, ?_⟩⟩, ?_⟩
      · linarith
      · exact norm_archimedeanTwist_eq_one T X
  rw [intervalNormSup, hrange]
  simp

private theorem archimedeanTwist_intervalVariation_bound {X H T : ℝ}
    (hX : 1 ≤ X) (hH : 0 < H) :
    orderedTotalVariation {n : ℤ | (n : ℝ) ∈ Set.Icc X (X + H)}
      (fun n => archimedeanTwist T n) ≤
      ENNReal.ofReal (1 + |T| * H / X) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hXY : X ≤ X + H := le_add_of_nonneg_right hH.le
  have hXYlt : X < X + H := by linarith
  have hsmooth : ContDiffOn ℝ 1 (archimedeanTwist T) (Set.Icc X (X + H)) :=
    contDiffOn_archimedeanTwist (T := T) hXpos
  let D : ℝ → ℝ := fun t =>
    ‖derivWithin (archimedeanTwist T) (Set.Icc X (X + H)) t‖
  have hDcont : ContinuousOn D (Set.Icc X (X + H)) := by
    exact (hsmooth.continuousOn_derivWithin (uniqueDiffOn_Icc hXYlt) (by norm_num)).norm
  have hDint : IntervalIntegrable D volume X (X + H) :=
    hDcont.intervalIntegrable_of_Icc hXY
  let C : ℝ := |T| / X
  have hCint : IntervalIntegrable (fun _ : ℝ => C) volume X (X + H) :=
    intervalIntegrable_const
  have hDle : ∀ t ∈ Set.Ioo X (X + H), D t ≤ C := by
    intro t ht
    change ‖derivWithin (archimedeanTwist T) (Set.Icc X (X + H)) t‖ ≤ C
    rw [show derivWithin (archimedeanTwist T) (Set.Icc X (X + H)) t =
      deriv (archimedeanTwist T) t from
        derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    change ‖deriv (archimedeanTwist T) t‖ ≤ |T| / X
    calc
      ‖deriv (archimedeanTwist T) t‖ ≤ |T| / t :=
        norm_deriv_archimedeanTwist_le (T := T) (lt_trans hXpos ht.1)
      _ ≤ |T| / X := div_le_div_of_nonneg_left (abs_nonneg T) hXpos ht.1.le
  have hIntegral : ∫ t in X..X + H, D t ≤ |T| * H / X := by
    calc
      ∫ t in X..X + H, D t ≤ ∫ t in X..X + H, C :=
        intervalIntegral.integral_mono_on_of_le_Ioo hXY hDint hCint hDle
      _ = (X + H - X) * C := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      _ = |T| * H / X := by
        dsimp [C]
        field_simp [ne_of_gt hXpos]
        ring
  have hRealBound :
      intervalNormSup X (X + H) (archimedeanTwist T) +
          ∫ t in X..X + H, D t ≤ 1 + |T| * H / X := by
    rw [archimedeanTwist_intervalNormSup_eq_one hH]
    nlinarith [hIntegral]
  have hC1 := orderedTotalVariation_le_sup_add_integral hXY
    (archimedeanTwist T) hsmooth
    {n : ℤ | (n : ℝ) ∈ Set.Icc X (X + H)} (fun _ hn => hn)
  exact hC1.trans (ENNReal.ofReal_le_ofReal hRealBound)

/-- The exact twist-variation bound in `lu:elementary-growth` for a finite
arithmetic progression in `(X,X+H]`. -/
theorem finiteOrderedTotalVariation_archimedeanTwist_le
    {X H T : ℝ} (hX : 1 ≤ X) (hH : 0 < H) (_hHX : H ≤ X)
    (P : Finset ℤ) (_hPAP : isFiniteArithmeticProgression P)
    (hP : ∀ n ∈ P, X < (n : ℝ) ∧ (n : ℝ) ≤ X + H) :
    finiteOrderedTotalVariation P (fun n => archimedeanTwist T n) ≤
      1 + |T| * H / X := by
  let Pset : Set ℤ := P
  have hPsub : Pset ⊆ {n : ℤ | (n : ℝ) ∈ Set.Icc X (X + H)} := by
    intro n hn
    have hn' := hP n hn
    exact ⟨hn'.1.le, hn'.2⟩
  have hfinite :
      ENNReal.ofReal (finiteOrderedTotalVariation P (fun n => archimedeanTwist T n)) ≤
        orderedTotalVariation Pset (fun n => archimedeanTwist T n) := by
    unfold orderedTotalVariation
    exact le_iSup_of_le ⟨P, fun _ hn => hn⟩ le_rfl
  have hvariation := orderedTotalVariation_mono_of_subset hPsub
    (fun n => archimedeanTwist T n)
  have hinterval := archimedeanTwist_intervalVariation_bound (T := T) hX hH
  have hENN :
      ENNReal.ofReal (finiteOrderedTotalVariation P (fun n => archimedeanTwist T n)) ≤
        ENNReal.ofReal (1 + |T| * H / X) := hfinite.trans (hvariation.trans hinterval)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN

/-- Summing the twist variation over the `q` residue classes costs at most
the factor `q` in the `lu:elementary-growth` estimate. -/
theorem residueClassTotalVariation_archimedeanTwist_le
    {X H T : ℝ} (hX : 1 ≤ X) (hH : 0 < H) (_hHX : H ≤ X)
    (P : Finset ℤ) (_hPAP : isFiniteArithmeticProgression P)
    (hP : ∀ n ∈ P, X < (n : ℝ) ∧ (n : ℝ) ≤ X + H)
    (q : ℕ) (hq : 0 < q) :
    residueClassTotalVariation (P : Set ℤ) (fun n => archimedeanTwist T n) q hq ≤
      ENNReal.ofReal ((q : ℝ) * (1 + |T| * H / X)) := by
  let Pset : Set ℤ := P
  have hPsub : Pset ⊆ {n : ℤ | (n : ℝ) ∈ Set.Icc X (X + H)} := by
    intro n hn
    have hn' := hP n hn
    exact ⟨hn'.1.le, hn'.2⟩
  have hinterval := archimedeanTwist_intervalVariation_bound (T := T) hX hH
  unfold residueClassTotalVariation
  calc
    (∑ a ∈ Finset.range q,
        orderedTotalVariation (Pset ∩ integerResidueClass q a)
          (fun n => archimedeanTwist T n)) ≤
      ∑ _a ∈ Finset.range q, ENNReal.ofReal (1 + |T| * H / X) := by
        apply Finset.sum_le_sum
        intro a ha
        exact (orderedTotalVariation_mono_of_subset
          (fun _ hn => hPsub hn.1) (fun n => archimedeanTwist T n)).trans hinterval
    _ = ENNReal.ofReal ((q : ℝ) * (1 + |T| * H / X)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity)]
      simp

end

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.finiteOrderedTotalVariation_archimedeanTwist_le
#print axioms FractionalPrimes.Literature.Uniformity.residueClassTotalVariation_archimedeanTwist_le
