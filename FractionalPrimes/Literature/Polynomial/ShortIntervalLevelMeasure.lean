module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalDirichletMeanValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Compactness.Compact

/-! The first level-set prerequisites for `lgv:level-measure`.

Blueprint: `expanded-blueprint.tex:5598-5621`.
Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-large-values.tex`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.LargeValues

noncomputable section

/-- The closed-interval level set of the finite Dirichlet polynomial. -/
def dirichletLevelSet (N T V : ℝ) (a : ℕ → ℂ) : Set ℝ :=
  {t | t ∈ Set.Icc (-T) T ∧ V ≤ ‖dirichletPolynomial N a t‖}

private lemma dirichletPolynomial_continuous (N : ℝ) (a : ℕ → ℂ) :
    Continuous (dirichletPolynomial N a) := by
  unfold dirichletPolynomial
  fun_prop

/-- Continuity of the finite polynomial makes its closed level set measurable. -/
theorem dirichletLevelSet_measurable (N T V : ℝ) (a : ℕ → ℂ) :
    MeasurableSet (dirichletLevelSet N T V a) := by
  have hnorm : Continuous (fun t : ℝ => ‖dirichletPolynomial N a t‖) :=
    (dirichletPolynomial_continuous N a).norm
  change MeasurableSet (Set.Icc (-T) T ∩ {t | V ≤ ‖dirichletPolynomial N a t‖})
  exact measurableSet_Icc.inter (measurableSet_le measurable_const hnorm.measurable)

/-- Chebyshev's inequality and the integrated mean-square estimate give the
second, mean-square bound in `lgv:level-measure`. -/
theorem dirichletLevelSetMeasureBound_meanSquare
    (N T V : ℝ) (a : ℕ → ℂ) (hN : 2 ≤ N) (hT : 2 ≤ T) (hV : 0 < V) :
    volume.real (dirichletLevelSet N T V a) ≤
      (2 * T + 8 * N * (1 + Real.log (2 * N))) *
        dirichletEnergy N a / V ^ 2 := by
  classical
  let f : ℝ → ℝ := fun t => Complex.normSq (dirichletPolynomial N a t)
  let μ : Measure ℝ := volume.restrict (Set.Icc (-T) T)
  have hcont : Continuous f := by
    dsimp [f]
    exact Complex.continuous_normSq.comp (dirichletPolynomial_continuous N a)
  have hfIntIcc : IntegrableOn f (Set.Icc (-T) T) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hA : MeasurableSet {t : ℝ | V ^ 2 ≤ f t} :=
    measurableSet_le measurable_const hcont.measurable
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := f) (ae_of_all _ fun _ => Complex.normSq_nonneg _)
    hfIntIcc.integrable (V ^ 2)
  have hEsubset : dirichletLevelSet N T V a ⊆ {t : ℝ | V ^ 2 ≤ f t} := by
    intro t ht
    rcases ht with ⟨_, hlarge⟩
    change V ^ 2 ≤ Complex.normSq (dirichletPolynomial N a t)
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (le_of_lt hV) hlarge 2
  have hmeasureA : V ^ 2 * μ.real {t : ℝ | V ^ 2 ≤ f t} ≤
      ∫ t, f t ∂μ := by
    exact hmarkov
  have hmeasureE : volume.real (dirichletLevelSet N T V a) ≤
      μ.real {t : ℝ | V ^ 2 ≤ f t} := by
    have hEmeas := dirichletLevelSet_measurable N T V a
    have hrestrictE : μ.real (dirichletLevelSet N T V a) =
        volume.real (dirichletLevelSet N T V a) := by
      rw [show μ = volume.restrict (Set.Icc (-T) T) by rfl,
        MeasureTheory.measureReal_restrict_apply hEmeas]
      congr 1
      exact Set.inter_eq_left.mpr (by
        intro t ht
        exact ht.1)
    have hmono : μ.real (dirichletLevelSet N T V a) ≤
        μ.real {t : ℝ | V ^ 2 ≤ f t} := by
      have hfinite : μ {t : ℝ | V ^ 2 ≤ f t} ≠ ⊤ := by
        have hle : μ {t : ℝ | V ^ 2 ≤ f t} ≤ volume (Set.Icc (-T) T) := by
          rw [show μ = volume.restrict (Set.Icc (-T) T) by rfl,
            Measure.restrict_apply hA]
          exact measure_mono Set.inter_subset_right
        have hvol : volume (Set.Icc (-T) T) < ⊤ := by simp [Real.volume_Icc]
        exact ne_of_lt (lt_of_le_of_lt hle hvol)
      exact MeasureTheory.measureReal_mono hEsubset hfinite
    rw [← hrestrictE]
    exact hmono
  have hmeanSquare : (∫ t, f t ∂μ) ≤
      (2 * T + 8 * N * (1 + Real.log (2 * N))) * dirichletEnergy N a := by
    have hms := meanSquareBound_Ioc N (-T) (2 * T) a hN (by linarith)
    have hinterval : -T + 2 * T = T := by ring
    have hms' : (∫ t in Set.Ioc (-T) T,
        Complex.normSq (dirichletPolynomial N a t) ∂volume) ≤
        (2 * T + 8 * N * (1 + Real.log (2 * N))) * dirichletEnergy N a := by
      simpa [hinterval] using hms
    have hIcc : (∫ t in Set.Icc (-T) T, f t ∂volume) =
        ∫ t in Set.Ioc (-T) T, f t ∂volume := by
      simpa [f] using (MeasureTheory.integral_Icc_eq_integral_Ioc
        (μ := volume) (x := -T) (y := T)
        (f := fun t : ℝ => Complex.normSq (dirichletPolynomial N a t)))
    calc
      (∫ t, f t ∂μ) = ∫ t in Set.Icc (-T) T, f t ∂volume := rfl
      _ = ∫ t in Set.Ioc (-T) T, f t ∂volume := hIcc
      _ ≤ (2 * T + 8 * N * (1 + Real.log (2 * N))) * dirichletEnergy N a := by
        exact hms'
  have hproduct : V ^ 2 * volume.real (dirichletLevelSet N T V a) ≤
      (2 * T + 8 * N * (1 + Real.log (2 * N))) * dirichletEnergy N a := by
    calc
      V ^ 2 * volume.real (dirichletLevelSet N T V a) ≤
          V ^ 2 * μ.real {t : ℝ | V ^ 2 ≤ f t} :=
        mul_le_mul_of_nonneg_left hmeasureE (sq_nonneg V)
      _ ≤ ∫ t, f t ∂μ := hmeasureA
      _ ≤ (2 * T + 8 * N * (1 + Real.log (2 * N))) * dirichletEnergy N a := hmeanSquare
  apply (le_div_iff₀ (sq_pos_of_pos hV)).2
  simpa [mul_comm] using hproduct

private def separatedLevelFinset (E : Set ℝ) (S : Finset ℝ) : Prop :=
  (∀ x ∈ S, x ∈ E) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|

/-- A compact level set is covered by unit-radius intervals centered at a
maximum-cardinality separated subset. The hypothesis packages the finite
large-value estimate `lgv:separated`; the resulting factor two comes from the
length of each covering interval. -/
theorem dirichletLevelSetMeasureBound_of_separated
    (N T V B : ℝ) (a : ℕ → ℂ)
    (hseparatedBound : ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ j, t j ∈ dirichletLevelSet N T V a) →
      (∀ i j, i ≠ j → 1 ≤ |t i - t j|) → (R : ℝ) ≤ B) :
    volume.real (dirichletLevelSet N T V a) ≤ 2 * B := by
  classical
  let E := dirichletLevelSet N T V a
  change volume.real E ≤ 2 * B
  have hB : 0 ≤ B := by
    have h := hseparatedBound 0 Fin.elim0 (by intro j; exact Fin.elim0 j)
      (by intro i j; exact Fin.elim0 i)
    simpa using h
  by_cases hEempty : E = ∅
  · simp [hEempty]
    nlinarith [hB]
  have hnorm : Continuous (fun t : ℝ => ‖dirichletPolynomial N a t‖) :=
    (dirichletPolynomial_continuous N a).norm
  have hclosed : IsClosed {t : ℝ | V ≤ ‖dirichletPolynomial N a t‖} :=
    isClosed_Ici.preimage hnorm
  have hcompact : IsCompact E := by
    change IsCompact (Set.Icc (-T) T ∩
      {t : ℝ | V ≤ ‖dirichletPolynomial N a t‖})
    exact isCompact_Icc.inter_right hclosed
  have hseparatedCardBound (S : Finset ℝ)
      (hS : separatedLevelFinset E S) : (S.card : ℝ) ≤ B := by
    let t : Fin S.card → ℝ := fun j => S.orderEmbOfFin rfl j
    have htE : ∀ j, t j ∈ E := by
      intro j
      exact hS.1 _ (Finset.orderEmbOfFin_mem S rfl j)
    have htSep : ∀ i j, i ≠ j → 1 ≤ |t i - t j| := by
      intro i j hij
      have hne : t i ≠ t j := by
        intro heq
        exact hij ((S.orderEmbOfFin rfl).injective heq)
      exact hS.2 _ (Finset.orderEmbOfFin_mem S rfl i)
        _ (Finset.orderEmbOfFin_mem S rfl j) hne
    exact hseparatedBound S.card t htE htSep
  let cards := (Finset.range (Nat.floor B + 1)).filter fun r =>
    ∃ S : Finset ℝ, separatedLevelFinset E S ∧ S.card = r
  have hcards : cards.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩⟩
    exact ⟨∅, by simp [separatedLevelFinset], rfl⟩
  let Rmax := cards.max' hcards
  obtain ⟨S, hS, hScard⟩ := (Finset.mem_filter.mp (Finset.max'_mem cards hcards)).2
  have hSmax (S' : Finset ℝ) (hS' : separatedLevelFinset E S') : S'.card ≤ S.card := by
    have hcard : S'.card ≤ Nat.floor B := Nat.le_floor (hseparatedCardBound S' hS')
    have hm : S'.card ∈ cards := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hcard)
      · exact ⟨S', hS', rfl⟩
    have hmmax := Finset.le_max' cards S'.card hm
    rw [hScard]
    exact hmmax
  have hcover : E ⊆ ⋃ x ∈ S, Metric.closedBall x 1 := by
    intro t htE
    by_contra hnot
    have hdist (x : ℝ) (hx : x ∈ S) : 1 < |t - x| := by
      have hnotBall : t ∉ Metric.closedBall x 1 := by
        intro hball
        exact hnot (Set.mem_iUnion₂.mpr ⟨x, hx, hball⟩)
      have hdist' : 1 < dist t x := by
        apply lt_of_not_ge
        intro hle
        exact hnotBall (by simpa [Metric.mem_closedBall] using hle)
      simpa [Real.dist_eq] using hdist'
    have htNotMem : t ∉ S := by
      intro htm
      have := hdist t htm
      rw [sub_self, abs_zero] at this
      norm_num at this
    have hinsertSub : separatedLevelFinset E (insert t S) := by
      constructor
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · exact htE
        · exact hS.1 x hxS
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · rcases Finset.mem_insert.mp hy with rfl | hyS
          · exact (hxy rfl).elim
          · exact (hdist y hyS).le
        · rcases Finset.mem_insert.mp hy with rfl | hyS
          · simpa [abs_sub_comm] using (hdist x hxS).le
          · exact hS.2 x hxS y hyS hxy
    have hcardInsert : (insert t S).card = S.card + 1 :=
      Finset.card_insert_of_notMem htNotMem
    have hmax := hSmax (insert t S) hinsertSub
    omega
  have hfiniteCover : volume (⋃ x ∈ S, Metric.closedBall x 1) ≠ ⊤ := by
    have hcoverBound : (⋃ x ∈ S, Metric.closedBall x 1) ⊆
        Set.Icc (-T - 1) (T + 1) := by
      intro y hy
      rcases Set.mem_iUnion₂.mp hy with ⟨x, hxS, hyball⟩
      have hxE := hS.1 x hxS
      change x ∈ Set.Icc (-T) T ∧ _ at hxE
      have hxlo : -T ≤ x := hxE.1.1
      have hxhi : x ≤ T := hxE.1.2
      have hdist : dist y x ≤ 1 := by
        simpa [Metric.mem_closedBall] using hyball
      have hdistAbs : |y - x| ≤ 1 := by simpa [Real.dist_eq] using hdist
      rcases abs_le.mp hdistAbs with ⟨hlo, hhi⟩
      exact ⟨by linarith, by linarith⟩
    have hle : volume (⋃ x ∈ S, Metric.closedBall x 1) ≤
        volume (Set.Icc (-T - 1) (T + 1)) := measure_mono hcoverBound
    apply ne_of_lt
    exact lt_of_le_of_lt hle (by simp [Real.volume_Icc])
  calc
    volume.real E ≤ volume.real (⋃ x ∈ S, Metric.closedBall x 1) :=
      MeasureTheory.measureReal_mono hcover hfiniteCover
    _ ≤ ∑ x ∈ S, volume.real (Metric.closedBall x 1) :=
      MeasureTheory.measureReal_biUnion_finset_le S (fun x => Metric.closedBall x 1)
    _ ≤ 2 * B := by
      calc
        (∑ x ∈ S, volume.real (Metric.closedBall x 1)) =
            ∑ x ∈ S, (2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp
        _ = (S.card : ℝ) * 2 := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ B * 2 := mul_le_mul_of_nonneg_right
          (hseparatedCardBound S hS) (by norm_num)
        _ = 2 * B := by ring

end

end FractionalPrimes.Literature.LargeValues

end

#print axioms FractionalPrimes.Literature.LargeValues.dirichletLevelSet_measurable
#print axioms FractionalPrimes.Literature.LargeValues.dirichletLevelSetMeasureBound_meanSquare
#print axioms FractionalPrimes.Literature.LargeValues.dirichletLevelSetMeasureBound_of_separated
