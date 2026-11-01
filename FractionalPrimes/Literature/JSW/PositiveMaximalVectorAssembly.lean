module

public import FractionalPrimes.Literature.JSW.PositiveEnergyPairing
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Assembly of vector bounds from positive maximal bounds

This downstream module assembles the scalar energy and duality lemmas for
`lj:positivity`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open scoped ComplexConjugate

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- For a finite Euclidean-valued input, its squared `Lᵖ(ℓ²)` norm equals the
`Lᵖ⁄²` norm of its coordinate energy. -/
theorem lpNorm_finiteEuclidean_energy_sq
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p)
    (F : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume) :
    lpNorm (fun x => (∑ i, ‖F x i‖ ^ 2 : ℝ))
        (ENNReal.ofReal (p / 2)) volume =
      lpNorm F (ENNReal.ofReal p) volume ^ 2 := by
  have henergy : MemLp (fun x => (∑ i, ‖F x i‖ ^ 2 : ℝ))
      (ENNReal.ofReal (p / 2)) volume := by
    apply finitePositiveEnergy_memLp
    intro i
    exact hF.eval_piLp i
  have hnormEnergy : (fun x => (∑ i, ‖F x i‖ ^ 2 : ℝ)) =
      (fun x => ‖F x‖ ^ 2) := by
    funext x
    exact (EuclideanSpace.norm_sq_eq (F x)).symm
  have hELp : eLpNorm
      (fun x => (∑ i, ‖F x i‖ ^ 2 : ℝ))
      (ENNReal.ofReal (p / 2)) volume =
        eLpNorm F (ENNReal.ofReal p) volume ^ 2 := by
    rw [hnormEnergy]
    exact eLpNorm_norm_sq_eq hp hF.aestronglyMeasurable
  calc
    lpNorm (fun x => (∑ i, ‖F x i‖ ^ 2 : ℝ))
        (ENNReal.ofReal (p / 2)) volume =
        (eLpNorm (fun x => (∑ i, ‖F x i‖ ^ 2 : ℝ))
          (ENNReal.ofReal (p / 2)) volume).toReal := rfl
    _ = (eLpNorm F (ENNReal.ofReal p) volume ^ 2).toReal :=
      congrArg ENNReal.toReal hELp
    _ = (eLpNorm F (ENNReal.ofReal p) volume).toReal ^ 2 := by
      rw [ENNReal.toReal_pow]
    _ = lpNorm F (ENNReal.ofReal p) volume ^ 2 := rfl

/-- The energy bound for a finite family of probability convolutions, in a
form that isolates the sole maximal-function input. For every nonnegative
dual test, the reflected averages are dominated pointwise by an `Lᑫ`
majorant whose norm has bound `B`. -/
theorem finiteProbabilityVector_energy_bound
    {ι : Type*} [Fintype ι] {p q : ℝ} (hp : 2 < p)
    (hrq : (p / 2).HolderConjugate q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (F U : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume)
    (hU : MemLp U (ENNReal.ofReal p) volume)
    (hJensen : ∀ᵐ x ∂volume,
      (∑ i, ‖U x i‖ ^ 2) ≤
        ∑ i, ∫ y, ‖F (x - y) i‖ ^ 2 ∂(μ i))
    (B : ℝ) (hB : 0 ≤ B)
    (hMax : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          B * lpNorm g (ENNReal.ofReal q) volume) :
    lpNorm (fun x => (∑ i, ‖U x i‖ ^ 2 : ℝ))
        (ENNReal.ofReal (p / 2)) volume ≤
      B * lpNorm (fun x => (∑ i, ‖F x i‖ ^ 2 : ℝ))
        (ENNReal.ofReal (p / 2)) volume := by
  classical
  let r : ℝ := p / 2
  let P : ℝ≥0∞ := ENNReal.ofReal r
  let Q : ℝ≥0∞ := ENNReal.ofReal q
  have hrpos : 0 < r := by dsimp [r]; linarith
  have hqpos : 0 < q := hrq.symm.pos
  letI : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr hrq.lt.le⟩
  letI : Fact (1 ≤ Q) := ⟨ENNReal.one_le_ofReal.mpr hrq.symm.lt.le⟩
  letI : ENNReal.HolderTriple P Q 1 := hrq.ennrealOfReal
  let eIn : ℝ → ℝ := fun x => ∑ i, ‖F x i‖ ^ 2
  let eOut : ℝ → ℝ := fun x => ∑ i, ‖U x i‖ ^ 2
  have hCoordF : ∀ i, MemLp (fun x => F x i) (ENNReal.ofReal p) volume := by
    intro i
    exact hF.eval_piLp i
  have hCoordU : ∀ i, MemLp (fun x => U x i) (ENNReal.ofReal p) volume := by
    intro i
    exact hU.eval_piLp i
  have hEnergyIn : MemLp eIn P volume := by
    exact finitePositiveEnergy_memLp (fun i x => F x i) hCoordF
  have hEnergyOut : MemLp eOut P volume := by
    exact finitePositiveEnergy_memLp (fun i x => U x i) hCoordU
  have hEnergyInNonneg : ∀ x, 0 ≤ eIn x := by
    intro x
    exact Finset.sum_nonneg fun i _ => sq_nonneg ‖F x i‖
  have hEnergyOutNonneg : ∀ x, 0 ≤ eOut x := by
    intro x
    exact Finset.sum_nonneg fun i _ => sq_nonneg ‖U x i‖
  have hEnergyOutComplex : MemLp (fun x => (eOut x : ℂ)) P volume := by
    exact (@RCLike.ofRealCLM ℂ _).comp_memLp' hEnergyOut
  have hEnergyOutNorm : lpNorm (fun x => (eOut x : ℂ)) P volume =
      lpNorm eOut P volume := by
    have hnorm : (fun x => ‖(eOut x : ℂ)‖) =ᵐ[volume] eOut := by
      filter_upwards [] with x
      simp [abs_of_nonneg (hEnergyOutNonneg x)]
    apply congrArg ENNReal.toReal
    calc
      eLpNorm (fun x => (eOut x : ℂ)) P volume =
          eLpNorm (fun x => ‖(eOut x : ℂ)‖) P volume :=
        (eLpNorm_norm (fun x => (eOut x : ℂ))
          hEnergyOutComplex.aestronglyMeasurable).symm
      _ = eLpNorm eOut P volume := eLpNorm_congr_ae hnorm

  have hDual := lpNorm_eq_sSup_dualPairingValues hrq hEnergyOutComplex
  have hPairingNonempty :
      (lpDualPairingValues volume q (fun x => (eOut x : ℂ))).Nonempty := by
    refine ⟨0, 0, MemLp.zero', by simp, ?_⟩
    simp
  rw [← hEnergyOutNorm, hDual]
  apply csSup_le hPairingNonempty
  rintro a ⟨g, hg, hgOne, rfl⟩
  let gAbs : ℝ → ℝ := fun x => ‖g x‖
  have hgAbs : MemLp gAbs Q volume := by
    exact hg.norm
  obtain ⟨M, hM, hMnonneg, hMajor, hMbound⟩ := hMax gAbs hgAbs
  have hInputSquaredCoord : ∀ i,
      MemLp (fun x => ‖F x i‖ ^ 2) P volume := by
    intro i
    have h := (hCoordF i).norm_rpow_div (2 : ℝ≥0∞)
    convert h using 1
    · ext x
      simp
    · dsimp [P, r]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
      norm_num
  have hInputSquaredNonneg : ∀ i x, 0 ≤ ‖F x i‖ ^ 2 := by
    intro i x
    positivity
  have hPair := finitePositiveEnergy_pairing_le hrq μ hμ
    (fun i x => ‖F x i‖ ^ 2) hInputSquaredCoord hInputSquaredNonneg
    gAbs M hgAbs hM hMnonneg hMajor
  have hInputRoot :
      (∫ x, eIn x ^ r ∂volume) ^ (1 / r) = lpNorm eIn P volume := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hrpos) (by simp)
      hEnergyIn.aestronglyMeasurable]
    simp only [P, ENNReal.toReal_ofReal hrpos.le, one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnergyInNonneg x)]
  have hMaxRoot :
      (∫ x, M x ^ q ∂volume) ^ (1 / q) = lpNorm M Q volume := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hqpos) (by simp)
      hM.aestronglyMeasurable]
    simp only [Q, ENNReal.toReal_ofReal hqpos.le, one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hMnonneg x)]
  have htestNorm : lpNorm gAbs Q volume = lpNorm g Q volume := by
    unfold lpNorm
    exact congrArg ENNReal.toReal (eLpNorm_norm g hg.aestronglyMeasurable)
  have hEnergyPairIntegrable :
      Integrable (fun x => eOut x * gAbs x) volume := by
    exact memLp_one_iff_integrable.mp (hEnergyOut.mul hgAbs)
  have hInputPairIntegrable :
      Integrable
        (fun x => (∑ i, ∫ y, ‖F (x - y) i‖ ^ 2 ∂(μ i)) * gAbs x)
        volume := by
    have hterm (i : ι) :
        Integrable (fun x => (∫ y, ‖F (x - y) i‖ ^ 2 ∂(μ i)) * gAbs x)
          volume := by
      obtain ⟨hLeft, _⟩ := integrable_positiveEnergy_pair_products
        (μ i) hrq (fun x => ‖F x i‖ ^ 2) gAbs
        (hInputSquaredCoord i) hgAbs
      have h := hLeft.integral_prod_left
      convert h using 1
      ext x
      simp only [Prod.fst, Prod.snd]
      exact (integral_mul_const (gAbs x)
        (fun y : ℝ => ‖F (x - y) i‖ ^ 2)).symm
    have hsum := integrable_finsetSum Finset.univ (fun i _ => hterm i)
    convert hsum using 1
    ext x
    rw [Finset.sum_mul]
  have hPointwiseMonotone :
      (fun x => eOut x * gAbs x) ≤ᵐ[volume]
      (fun x => (∑ i, ∫ y, ‖F (x - y) i‖ ^ 2 ∂(μ i)) * gAbs x) := by
    filter_upwards [hJensen] with x hx
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg (g x))
  have hEnergyIntegralLe := integral_mono_ae hEnergyPairIntegrable
    hInputPairIntegrable hPointwiseMonotone
  have hDualPairBound :
      ‖∫ x, inner ℂ ((eOut x : ℂ)) (g x) ∂volume‖ ≤
        B * lpNorm eIn P volume := by
    have hInnerIntegrable : Integrable
        (fun x => inner ℂ ((eOut x : ℂ)) (g x)) volume := by
      apply hEnergyPairIntegrable.mono'
        (hEnergyOutComplex.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      filter_upwards [] with x
      calc
        ‖inner ℂ ((eOut x : ℂ)) (g x)‖ ≤
            ‖(eOut x : ℂ)‖ * ‖g x‖ := norm_inner_le_norm _ _
        _ = eOut x * gAbs x := by
          simp [gAbs, abs_of_nonneg (hEnergyOutNonneg x)]
    calc
      ‖∫ x, inner ℂ ((eOut x : ℂ)) (g x) ∂volume‖ ≤
          ∫ x, ‖inner ℂ ((eOut x : ℂ)) (g x)‖ ∂volume :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, eOut x * gAbs x ∂volume := by
        apply integral_mono_ae hInnerIntegrable.norm hEnergyPairIntegrable
        filter_upwards [] with x
        calc
          ‖inner ℂ ((eOut x : ℂ)) (g x)‖ ≤
              ‖(eOut x : ℂ)‖ * ‖g x‖ := norm_inner_le_norm _ _
          _ = eOut x * gAbs x := by
            simp [gAbs, abs_of_nonneg (hEnergyOutNonneg x)]
      _ ≤ (∫ x, (∑ i, ∫ y, ‖F (x - y) i‖ ^ 2 ∂(μ i)) * gAbs x ∂volume) :=
        hEnergyIntegralLe
      _ ≤ (∫ x, eIn x ^ r ∂volume) ^ (1 / r) *
            (∫ x, M x ^ q ∂volume) ^ (1 / q) := hPair
      _ = lpNorm eIn P volume * lpNorm M Q volume := by
        rw [hInputRoot, hMaxRoot]
      _ ≤ lpNorm eIn P volume * (B * lpNorm gAbs Q volume) :=
        mul_le_mul_of_nonneg_left hMbound (lpNorm_nonneg)
      _ ≤ lpNorm eIn P volume * (B * 1) := by
        apply mul_le_mul_of_nonneg_left ?_ lpNorm_nonneg
        apply mul_le_mul_of_nonneg_left ?_ hB
        simpa [htestNorm] using hgOne
      _ = B * lpNorm eIn P volume := by ring
  exact hDualPairBound

/- The square-root version is the exact finite-family `Lᵖ(ℓ²)` bound used
by the source lemma. -/
theorem finiteProbabilityVector_lp_bound
    {ι : Type*} [Fintype ι] {p q : ℝ} (hp : 2 < p)
    (hrq : (p / 2).HolderConjugate q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (F U : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume)
    (hU : MemLp U (ENNReal.ofReal p) volume)
    (hJensen : ∀ᵐ x ∂volume,
      (∑ i, ‖U x i‖ ^ 2) ≤
        ∑ i, ∫ y, ‖F (x - y) i‖ ^ 2 ∂(μ i))
    (B : ℝ) (hB : 0 ≤ B)
    (hMax : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          B * lpNorm g (ENNReal.ofReal q) volume) :
    lpNorm U (ENNReal.ofReal p) volume ≤
      Real.sqrt B * lpNorm F (ENNReal.ofReal p) volume := by
  have henergy := finiteProbabilityVector_energy_bound hp hrq μ hμ F U hF hU
    hJensen B hB hMax
  rw [lpNorm_finiteEuclidean_energy_sq (by linarith) U hU,
    lpNorm_finiteEuclidean_energy_sq (by linarith) F hF] at henergy
  have hu : 0 ≤ lpNorm U (ENNReal.ofReal p) volume := lpNorm_nonneg
  have hv : 0 ≤ Real.sqrt B * lpNorm F (ENNReal.ofReal p) volume :=
    mul_nonneg (Real.sqrt_nonneg B) lpNorm_nonneg
  have hvsq :
      (Real.sqrt B * lpNorm F (ENNReal.ofReal p) volume) ^ 2 =
        B * (lpNorm F (ENNReal.ofReal p) volume) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hB]
  nlinarith


#print axioms lpNorm_finiteEuclidean_energy_sq
#print axioms finiteProbabilityVector_energy_bound
#print axioms finiteProbabilityVector_lp_bound

end

end FractionalPrimes.Literature.JSW

end
