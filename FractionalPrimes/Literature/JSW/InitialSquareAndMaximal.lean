module

public import FractionalPrimes.Literature.JSW.MeasureSplitting
public import FractionalPrimes.Literature.JSW.RealPlancherelCompletion
public import FractionalPrimes.Literature.JSW.ComplexMeasureL2Representative
public import FractionalPrimes.Literature.JSW.MaximalBounds
public import FractionalPrimes.Literature.JSW.WeakTypeInterpolation

/-!
# Initial square and maximal bounds

This file develops the first square-function and maximal consequences of
`lj:measure-splitting`, with the exact scale constants in `lj:initial-square`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The frequency weight in the finite geometric-series estimate for the
dyadic scale square function. -/
def initialSquareFrequencyWeight (b β s : ℝ) (k : ℤ) : ℝ :=
  min (b ^ k * s) (Real.rpow (b ^ k * s) (-β))

/-- The last low-frequency integer scale for a positive frequency size. -/
def initialSquareFrequencyCutoff (b s : ℝ) : ℤ :=
  Int.floor (Real.logb b s⁻¹)

private theorem initialSquareFrequencyCutoff_bounds {b s : ℝ}
    (hb : 1 < b) (hs : 0 < s) :
    b ^ initialSquareFrequencyCutoff b s * s ≤ 1 ∧
      1 < b ^ (initialSquareFrequencyCutoff b s + 1) * s := by
  let n : ℤ := initialSquareFrequencyCutoff b s
  have hbpos : 0 < b := by linarith
  have hbne : b ≠ 1 := ne_of_gt hb
  have hlowExp : (n : ℝ) ≤ Real.logb b s⁻¹ := by
    exact Int.floor_le _
  have hhighExp : Real.logb b s⁻¹ < (n : ℝ) + 1 := by
    exact Int.lt_floor_add_one _
  have hlowPow : Real.rpow b (n : ℝ) ≤ s⁻¹ := by
    calc
      Real.rpow b (n : ℝ) ≤ Real.rpow b (Real.logb b s⁻¹) :=
        Real.rpow_le_rpow_of_exponent_le hb.le hlowExp
      _ = s⁻¹ := Real.rpow_logb hbpos hbne (inv_pos.mpr hs)
  have hhighPow : s⁻¹ < Real.rpow b ((n : ℝ) + 1) := by
    calc
      s⁻¹ = Real.rpow b (Real.logb b s⁻¹) :=
        (Real.rpow_logb hbpos hbne (inv_pos.mpr hs)).symm
      _ < Real.rpow b ((n : ℝ) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt hb hhighExp
  constructor
  · have hpow : b ^ n ≤ s⁻¹ := by simpa [n, Real.rpow_intCast] using hlowPow
    calc
      b ^ n * s ≤ s⁻¹ * s := mul_le_mul_of_nonneg_right hpow hs.le
      _ = 1 := inv_mul_cancel₀ hs.ne'
  · have hpow : s⁻¹ < b ^ (n + 1) := by
      rw [← Real.rpow_intCast b (n + 1)]
      convert hhighPow using 1 <;> simp [n]
    calc
      1 = s⁻¹ * s := (inv_mul_cancel₀ hs.ne').symm
      _ < b ^ (n + 1) * s := mul_lt_mul_of_pos_right hpow hs

private theorem initialSquare_lowScale_power {b : ℝ} (hb : 0 < b)
    {k n : ℤ} (hkn : k ≤ n) :
    b ^ k = b ^ n * (b⁻¹) ^ (n - k).toNat := by
  have hnat : ((n - k).toNat : ℤ) = n - k :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hkn)
  have hnatR : ((n - k).toNat : ℝ) = (n : ℝ) - k := by
    exact_mod_cast hnat
  have hkR : (k : ℝ) = (n : ℝ) - (n - k).toNat := by
    rw [hnatR]
    ring
  have hnatPow : Real.rpow b ((n - k).toNat : ℝ) = b ^ (n - k).toNat :=
    Real.rpow_natCast b ((n - k).toNat)
  have hpow : Real.rpow b (k : ℝ) =
      Real.rpow b (n : ℝ) * (b⁻¹) ^ (n - k).toNat := by
    calc
      Real.rpow b (k : ℝ) = Real.rpow b ((n : ℝ) - (n - k).toNat) := by rw [hkR]
      _ = Real.rpow b (n : ℝ) / Real.rpow b ((n - k).toNat : ℝ) :=
        Real.rpow_sub hb _ _
      _ = Real.rpow b (n : ℝ) / b ^ (n - k).toNat := by rw [hnatPow]
      _ = Real.rpow b (n : ℝ) * (b⁻¹) ^ (n - k).toNat := by
        rw [div_eq_mul_inv, inv_pow]
  rw [← Real.rpow_intCast b k, ← Real.rpow_intCast b n]
  exact hpow

private theorem initialSquare_highScale_power {b : ℝ} (hb : 0 < b)
    {n k : ℤ} (hnk : n ≤ k) :
    b ^ k = b ^ n * b ^ (k - n).toNat := by
  have hlow := initialSquare_lowScale_power hb hnk
  have h := congrArg (fun x : ℝ => x * b ^ (k - n).toNat) hlow
  rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hb.ne'), mul_one] at h
  exact h.symm

private theorem initialSquare_low_frequency_finite_sum {b s : ℝ}
    (hb : 1 < b) (hs : 0 < s) (F : Finset ℤ) (n : ℤ)
    (hF : ∀ k ∈ F, k ≤ n) (hscale : b ^ n * s ≤ 1) :
    (∑ k ∈ F, (b ^ k * s) ^ 2) ≤
      1 / (1 - (b⁻¹) ^ 2) := by
  have hbpos : 0 < b := by linarith
  have hinvpos : 0 < b⁻¹ := inv_pos.mpr hbpos
  have hinvlt : b⁻¹ < 1 := by
    exact (inv_lt_one₀ hbpos).2 hb
  have hqpos : 0 < (b⁻¹) ^ 2 := by positivity
  have hqLt : (b⁻¹) ^ 2 < 1 := by nlinarith
  let q : ℝ := (b⁻¹) ^ 2
  let idx : ℤ → ℕ := fun k => (n - k).toNat
  have hinj : Set.InjOn idx F := by
    intro k hk l hl hkl
    have hkbound := hF k hk
    have hlbound := hF l hl
    have hknat : ((n - k).toNat : ℤ) = n - k :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hkbound)
    have hlnat : ((n - l).toNat : ℤ) = n - l :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hlbound)
    have hnat : (n - k).toNat = (n - l).toNat := hkl
    have hnat' := congrArg (fun j : ℕ => (j : ℤ)) hnat
    rw [hknat, hlnat] at hnat'
    omega
  have hterm : ∀ k ∈ F,
      (b ^ k * s) ^ 2 = (b ^ n * s) ^ 2 * q ^ idx k := by
    intro k hk
    have hkpow := initialSquare_lowScale_power hbpos (hF k hk)
    dsimp [idx, q]
    rw [hkpow]
    rw [mul_pow, mul_pow]
    rw [← pow_mul]
    norm_num
    ring
  have hqsum : Summable (fun j : ℕ => (b ^ n * s) ^ 2 * q ^ j) := by
    dsimp [q]
    exact (summable_geometric_of_lt_one (by positivity) hqLt).mul_left _
  calc
    (∑ k ∈ F, (b ^ k * s) ^ 2) =
        ∑ k ∈ F, (b ^ n * s) ^ 2 * q ^ idx k := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hterm k hk
    _ = ∑ j ∈ F.image idx, (b ^ n * s) ^ 2 * q ^ j := by
          symm
          exact Finset.sum_image hinj
    _ ≤ ∑' j : ℕ, (b ^ n * s) ^ 2 * q ^ j :=
          Summable.sum_le_tsum _ (fun j hj => by positivity) hqsum
    _ = (b ^ n * s) ^ 2 * (1 / (1 - q)) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hqLt]
          have hqdef : q = (b⁻¹) ^ 2 := rfl
          rw [hqdef, one_div]
    _ ≤ 1 / (1 - q) := by
          have hbase : 0 ≤ b ^ n * s := by positivity
          have hbaseSq : (b ^ n * s) ^ 2 ≤ 1 := by
            nlinarith [sq_nonneg (b ^ n * s - 1)]
          have hden : 0 < 1 - q := by dsimp [q]; linarith
          calc
            (b ^ n * s) ^ 2 * (1 / (1 - q)) =
                (b ^ n * s) ^ 2 / (1 - q) := by
                  simp only [one_div, one_mul, div_eq_mul_inv]
            _ ≤ 1 / (1 - q) := div_le_div_of_nonneg_right hbaseSq hden.le
    _ = 1 / (1 - (b⁻¹) ^ 2) := by rfl

private theorem initialSquare_high_frequency_finite_sum {b s β : ℝ}
    (hb : 1 < b) (hs : 0 < s) (hβ : 0 < β)
    (F : Finset ℤ) (n : ℤ) (hF : ∀ k ∈ F, n < k)
    (hscale : 1 < b ^ (n + 1) * s) :
    (∑ k ∈ F,
      (min (b ^ k * s) (Real.rpow (b ^ k * s) (-β))) ^ 2) ≤
      1 / (1 - Real.rpow b (-2 * β)) := by
  have hbpos : 0 < b := by linarith
  let m : ℤ := n + 1
  let idx : ℤ → ℕ := fun k => (k - m).toNat
  let q : ℝ := Real.rpow b (-2 * β)
  let C : ℝ := Real.rpow (b ^ m * s) (-2 * β)
  have hF' : ∀ k ∈ F, m ≤ k := by
    intro k hk
    dsimp [m]
    have := hF k hk
    omega
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos hbpos _
  have hqLt : q < 1 := by
    dsimp [q]
    apply Real.rpow_lt_one_of_one_lt_of_neg hb
    nlinarith
  have hinj : Set.InjOn idx F := by
    intro k hk l hl hkl
    have hkbound := hF' k hk
    have hlbound := hF' l hl
    have hknat : ((k - m).toNat : ℤ) = k - m :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hkbound)
    have hlnat : ((l - m).toNat : ℤ) = l - m :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hlbound)
    have hnat := congrArg (fun j : ℕ => (j : ℤ)) hkl
    rw [hknat, hlnat] at hnat
    omega
  have hbasepos : 0 < b ^ m * s := by positivity
  have hfactor : ∀ k ∈ F,
      Real.rpow (b ^ k * s) (-2 * β) = C * q ^ idx k := by
    intro k hk
    have hkpow := initialSquare_highScale_power hbpos (hF' k hk)
    have hu : b ^ k * s = (b ^ m * s) * b ^ (k - m).toNat := by
      rw [hkpow]
      ring
    have hfactorNat : Real.rpow (b ^ (k - m).toNat) (-2 * β) =
        q ^ (k - m).toNat := by
      dsimp [q]
      exact (Real.rpow_pow_comm hbpos.le (-2 * β) (k - m).toNat).symm
    calc
      Real.rpow (b ^ k * s) (-2 * β) =
          Real.rpow ((b ^ m * s) * b ^ (k - m).toNat) (-2 * β) := by rw [hu]
      _ = Real.rpow (b ^ m * s) (-2 * β) *
          Real.rpow (b ^ (k - m).toNat) (-2 * β) := by
            exact Real.mul_rpow hbasepos.le (pow_nonneg hbpos.le _)
      _ = C * q ^ idx k := by
            rw [hfactorNat]
  have hterm : ∀ k ∈ F,
      (min (b ^ k * s) (Real.rpow (b ^ k * s) (-β))) ^ 2 ≤
        C * q ^ idx k := by
    intro k hk
    have hu : 0 < b ^ k * s := by positivity
    have hpow : 0 ≤ Real.rpow (b ^ k * s) (-β) :=
      Real.rpow_nonneg hu.le _
    have hmin : 0 ≤ min (b ^ k * s) (Real.rpow (b ^ k * s) (-β)) :=
      le_min (by positivity) hpow
    have hsq := (sq_le_sq₀ hmin hpow).2 (min_le_right _ _)
    have hsqpow : (Real.rpow (b ^ k * s) (-β)) ^ 2 =
        Real.rpow (b ^ k * s) (-2 * β) := by
      calc
        (Real.rpow (b ^ k * s) (-β)) ^ 2 =
            Real.rpow (b ^ k * s) ((-β) * (2 : ℝ)) :=
              (Real.rpow_mul_natCast hu.le (-β) 2).symm
        _ = Real.rpow (b ^ k * s) (-2 * β) := by congr 1 <;> ring
    calc
      (min (b ^ k * s) (Real.rpow (b ^ k * s) (-β))) ^ 2 ≤
          (Real.rpow (b ^ k * s) (-β)) ^ 2 := hsq
      _ = C * q ^ idx k := by rw [hsqpow, hfactor k hk]
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg (by positivity) _
  have hCle : C ≤ 1 := by
    dsimp [C]
    apply Real.rpow_le_one_of_one_le_of_nonpos hscale.le
    nlinarith
  have hqsum : Summable (fun j : ℕ => C * q ^ j) := by
    exact (summable_geometric_of_lt_one hqpos.le hqLt).mul_left _
  calc
    (∑ k ∈ F,
        (min (b ^ k * s) (Real.rpow (b ^ k * s) (-β))) ^ 2) ≤
        ∑ k ∈ F, C * q ^ idx k := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k hk
    _ = ∑ j ∈ F.image idx, C * q ^ j := by
          symm
          exact Finset.sum_image hinj
    _ ≤ ∑' j : ℕ, C * q ^ j :=
          Summable.sum_le_tsum _ (fun j hj => by positivity) hqsum
    _ = C * (1 - q)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hqpos.le hqLt]
    _ ≤ 1 / (1 - q) := by
          have hden : 0 ≤ (1 - q)⁻¹ := by positivity
          calc
            C * (1 - q)⁻¹ ≤ 1 * (1 - q)⁻¹ :=
              mul_le_mul_of_nonneg_right hCle hden
            _ = 1 / (1 - q) := by simp [one_div]
    _ = 1 / (1 - Real.rpow b (-2 * β)) := by rfl

/-- The finite scale sum of the measure-splitting Fourier majorant has the
exact two geometric denominators in `lj:initial-square`. -/
theorem initialSquareFrequencyWeight_squareSum_le {b β s : ℝ}
    (hb : 1 < b) (hβ : 0 < β) (hs : 0 < s) (F : Finset ℤ) :
    (∑ k ∈ F, (initialSquareFrequencyWeight b β s k) ^ 2) ≤
      1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β)) := by
  let n := initialSquareFrequencyCutoff b s
  let Flo := F.filter (fun k => k ≤ n)
  let Fhi := F.filter (fun k => ¬ k ≤ n)
  have hcut := initialSquareFrequencyCutoff_bounds hb hs
  have hlow : (∑ k ∈ Flo, (initialSquareFrequencyWeight b β s k) ^ 2) ≤
      1 / (1 - b⁻¹ ^ 2) := by
    calc
      (∑ k ∈ Flo, (initialSquareFrequencyWeight b β s k) ^ 2) ≤
          ∑ k ∈ Flo, (b ^ k * s) ^ 2 := by
            apply Finset.sum_le_sum
            intro k hk
            have hk' := Finset.mem_filter.mp hk
            have hu : 0 < b ^ k * s := by positivity
            have hp : 0 ≤ Real.rpow (b ^ k * s) (-β) :=
              Real.rpow_nonneg hu.le _
            have hm : 0 ≤ min (b ^ k * s) (Real.rpow (b ^ k * s) (-β)) :=
              le_min (by positivity) hp
            exact (sq_le_sq₀ hm (by positivity)).2 (min_le_left _ _)
      _ ≤ 1 / (1 - b⁻¹ ^ 2) := by
            apply initialSquare_low_frequency_finite_sum hb hs Flo n
            · intro k hk
              exact (Finset.mem_filter.mp hk).2
            · exact hcut.1
  have hhigh : (∑ k ∈ Fhi, (initialSquareFrequencyWeight b β s k) ^ 2) ≤
      1 / (1 - Real.rpow b (-2 * β)) := by
    apply initialSquare_high_frequency_finite_sum hb hs hβ Fhi n
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨_, hknot⟩
      omega
    · exact hcut.2
  calc
    (∑ k ∈ F, (initialSquareFrequencyWeight b β s k) ^ 2) =
        (∑ k ∈ Flo, (initialSquareFrequencyWeight b β s k) ^ 2) +
          ∑ k ∈ Fhi, (initialSquareFrequencyWeight b β s k) ^ 2 := by
            dsimp [Flo, Fhi]
            rw [← Finset.sum_filter_add_sum_filter_not
              (s := F) (p := fun k => k ≤ n)]
    _ ≤ 1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β)) :=
          add_le_add hlow hhigh

private theorem initialSquareDensityVariationMass {σ : Measure ℝ}
    [IsProbabilityMeasure σ] {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) :
    (volume.withDensityᵥ (measureSplittingPsi σ)).variation Set.univ = 1 := by
  have hψint : Integrable (measureSplittingPsi σ) volume :=
    measureSplittingPsi_integrable σ hSupp
  have hden : (fun x => ‖measureSplittingPsi σ x‖ₑ) =
      fun x => ENNReal.ofReal (measureSplittingPsi σ x) := by
    funext x
    exact Real.enorm_eq_ofReal (hσ.psi_nonneg x)
  rw [Measure.variation_withDensityᵥ hψint, hden,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hψint (ae_of_all volume hσ.psi_nonneg),
    hσ.psi_integral]
  norm_num

private theorem initialSquareNu_variation_isFinite {σ : Measure ℝ}
    [IsProbabilityMeasure σ] {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) :
    IsFiniteMeasure (measureSplittingNu σ).variation := by
  have hdensity : IsFiniteMeasure
      (volume.withDensityᵥ (measureSplittingPsi σ)).variation := by
    rw [isFiniteMeasure_iff]
    rw [initialSquareDensityVariationMass hSupp hσ]
    norm_num
  have hvariation : (measureSplittingNu σ).variation ≤
      σ + (volume.withDensityᵥ (measureSplittingPsi σ)).variation := by
    simpa [measureSplittingNu, Measure.variation_toSignedMeasure] using
      (VectorMeasure.variation_sub_le (μ := σ.toSignedMeasure)
        (ν := volume.withDensityᵥ (measureSplittingPsi σ)))
  exact isFiniteMeasure_of_le
    (σ + (volume.withDensityᵥ (measureSplittingPsi σ)).variation) hvariation

private theorem initialSquareNuFourier_zero {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {β D : ℝ} (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) :
    measureSplittingNuFourier σ 0 = 0 := by
  letI : IsFiniteMeasure (measureSplittingNu σ).variation :=
    initialSquareNu_variation_isFinite hSupp hσ
  unfold measureSplittingNuFourier
  have hphase :
      (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * 0) * Complex.I)) =
        fun _ => (1 : ℂ) := by
    funext x
    simp
  rw [hphase, VectorMeasure.integral_const]
  simp [hσ.nu_mass]

/-- The real signed cancellation measure viewed as a complex vector measure. -/
def initialSquareNuComplexMeasure (σ : Measure ℝ) [IsFiniteMeasure σ] :
    ComplexMeasure ℝ :=
  (measureSplittingNu σ).toComplexMeasure 0

def initialSquareSigmaComplexMeasure (σ : Measure ℝ)
    [IsFiniteMeasure σ] : ComplexMeasure ℝ :=
  σ.toSignedMeasure.toComplexMeasure 0

def initialSquarePsiComplexMeasure (σ : Measure ℝ) :
    ComplexMeasure ℝ :=
  SignedMeasure.toComplexMeasure
    (volume.withDensityᵥ (measureSplittingPsi σ)) 0

/-- The smooth splitting density as the signed measure of its positive
`withDensity` probability measure. -/
theorem initialSquarePsiMeasure_eq_toSignedMeasure_withDensity
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    volume.withDensityᵥ (measureSplittingPsi σ) =
      @Measure.toSignedMeasure ℝ _
        (volume.withDensity (fun x =>
          ENNReal.ofReal (measureSplittingPsi σ x)))
        (isFiniteMeasure_withDensity_ofReal
          (measureSplittingPsi_integrable σ hSupp).2) := by
  let f : ℝ → ℝ := measureSplittingPsi σ
  have hfi : Integrable f volume := by
    dsimp [f]
    exact measureSplittingPsi_integrable σ hSupp
  have hnonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact measureSplittingPsi_nonneg σ x
  have hneg : (fun x : ℝ => ENNReal.ofReal (-f x)) = 0 := by
    funext x
    simp [hnonneg x]
  have hnegMeasure :
      @Measure.toSignedMeasure ℝ _
        (volume.withDensity (fun x => ENNReal.ofReal (-f x)))
        (isFiniteMeasure_withDensity_ofReal hfi.neg.2) = 0 := by
    ext s hs
    simp [Measure.toSignedMeasure_apply_measurable hs, hneg]
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hfi,
    hnegMeasure, sub_zero]

theorem initialSquareNuComplexMeasure_sub_split (σ : Measure ℝ)
    [IsFiniteMeasure σ] :
    initialSquareNuComplexMeasure σ =
      initialSquareSigmaComplexMeasure σ - initialSquarePsiComplexMeasure σ := by
  ext E hE
  apply Complex.ext
  · simp [initialSquareNuComplexMeasure, measureSplittingNu,
      initialSquareSigmaComplexMeasure, initialSquarePsiComplexMeasure,
      SignedMeasure.toComplexMeasure_apply]
  · simp [initialSquareNuComplexMeasure, measureSplittingNu,
      initialSquareSigmaComplexMeasure, initialSquarePsiComplexMeasure,
      SignedMeasure.toComplexMeasure_apply]

private theorem initialSquareNuComplexMeasure_variation_le
    (μ : SignedMeasure ℝ) :
    (μ.toComplexMeasure 0).variation ≤ μ.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E hE
  rw [SignedMeasure.toComplexMeasure_apply]
  have him : (0 : SignedMeasure ℝ) E = (0 : ℝ) := by simp
  rw [him]
  have hzero : ({ re := μ E, im := (0 : ℝ) } : ℂ) = (μ E : ℂ) := rfl
  rw [hzero]
  change ENNReal.ofNNReal ‖(μ E : ℂ)‖₊ ≤ μ.variation E
  rw [Complex.nnnorm_real]
  exact VectorMeasure.enorm_measure_le_variation μ E

private theorem initialSquareNuComplexMeasure_variation_ge
    (μ : SignedMeasure ℝ) :
    μ.variation ≤ (μ.toComplexMeasure 0).variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E hE
  have heq : (μ.toComplexMeasure 0) E = (μ E : ℂ) := by
    rw [SignedMeasure.toComplexMeasure_apply]
    have hz : (0 : SignedMeasure ℝ) E = (0 : ℝ) := by simp
    rw [hz]
    rfl
  have hbound := VectorMeasure.enorm_measure_le_variation
    (μ.toComplexMeasure 0) E
  rw [heq] at hbound
  have hnorm : ‖(μ E : ℂ)‖ₑ = ‖μ E‖ₑ := by
    change ENNReal.ofNNReal ‖(μ E : ℂ)‖₊ = ENNReal.ofNNReal ‖μ E‖₊
    rw [Complex.nnnorm_real]
  rw [hnorm] at hbound
  exact hbound

private theorem initialSquareNuComplexMeasure_variation_eq
    (μ : SignedMeasure ℝ) :
    (μ.toComplexMeasure 0).variation = μ.variation := by
  exact le_antisymm
    (initialSquareNuComplexMeasure_variation_le μ)
    (initialSquareNuComplexMeasure_variation_ge μ)

private theorem initialSquareNuComplexMeasure_transpose_eq
    (μ : SignedMeasure ℝ) :
    (μ.toComplexMeasure 0).transpose (ContinuousLinearMap.mul ℝ ℂ) =
      μ.transpose (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
  ext E hE z
  have heq : (μ.toComplexMeasure 0) E = (μ E : ℂ) := by
    rw [SignedMeasure.toComplexMeasure_apply]
    have hz : (0 : SignedMeasure ℝ) E = (0 : ℝ) := by simp
    rw [hz]
    rfl
  change ((ContinuousLinearMap.mul ℝ ℂ).flip ((μ.toComplexMeasure 0) E)) z =
    (ContinuousLinearMap.lsmul ℝ ℝ (μ E)) z
  rw [heq]
  simp [ContinuousLinearMap.mul_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_comm]

theorem initialSquareNuComplexMeasure_integral_eq
    (μ : SignedMeasure ℝ) (f : ℝ → ℂ) :
    (∫ᵛ y, f y ∂[ContinuousLinearMap.mul ℝ ℂ; μ.toComplexMeasure 0]) =
      ∫ᵛ y, f y ∂<•μ := by
  rw [VectorMeasure.integral_eq_setToFun, VectorMeasure.integral_eq_setToFun]
  let μc := μ.toComplexMeasure 0
  let Bc : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  let Bs : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip
  have hvar : μc.variation = μ.variation :=
    initialSquareNuComplexMeasure_variation_eq μ
  have htrans : μc.transpose Bc = μ.transpose Bs :=
    initialSquareNuComplexMeasure_transpose_eq μ
  have htransFun : (μc.transpose Bc : Set ℝ → ℂ →L[ℝ] ℂ) =
      (μ.transpose Bs : Set ℝ → ℂ →L[ℝ] ℂ) := by
    exact congrArg
      (fun v : VectorMeasure ℝ (ℂ →L[ℝ] ℂ) =>
        (v : Set ℝ → ℂ →L[ℝ] ℂ)) htrans
  have hT1 : DominatedFinMeasAdditive μc.variation (μc.transpose Bc) ‖Bc‖ :=
    dominatedFinMeasAdditive_cbmApplyMeasure μc Bc
  have hT1' : DominatedFinMeasAdditive μc.variation (μ.transpose Bs) ‖Bc‖ := by
    simpa [htrans] using hT1
  have hT2 : DominatedFinMeasAdditive μ.variation (μ.transpose Bs) ‖Bs‖ :=
    dominatedFinMeasAdditive_cbmApplyMeasure μ Bs
  have hμle : μc.variation ≤ (1 : ℝ≥0∞) • μ.variation := by
    simpa using le_of_eq hvar
  have hμ'le : μ.variation ≤ (1 : ℝ≥0∞) • μc.variation := by
    simpa using le_of_eq hvar.symm
  calc
    setToFun μc.variation (μc.transpose Bc) hT1 f =
        setToFun μc.variation (μ.transpose Bs) hT1' f :=
          setToFun_congr_left hT1 hT1' htransFun f
    _ = setToFun μ.variation (μ.transpose Bs) hT2 f :=
          setToFun_congr_measure 1 1 (by simp) (by simp)
            hμle hμ'le hT1' hT2 f

private theorem initialSquarePsiComplexMeasure_integral_eq_density
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (g : ℝ → ℂ) :
    (∫ᵛ y, g y ∂[ContinuousLinearMap.mul ℝ ℂ;
        initialSquarePsiComplexMeasure σ]) =
      ∫ y, (measureSplittingPsi σ y : ℂ) * g y ∂volume := by
  let f : ℝ → ℝ := measureSplittingPsi σ
  let ρ : Measure ℝ := volume.withDensity (fun y => ENNReal.ofReal (f y))
  have hfi : Integrable f volume := by
    dsimp [f]
    exact measureSplittingPsi_integrable σ hSupp
  have hnonneg : ∀ y, 0 ≤ f y := by
    intro y
    exact measureSplittingPsi_nonneg σ y
  have hmeas : Measurable (fun y : ℝ => ENNReal.ofReal (f y)) := by
    exact ENNReal.measurable_ofReal.comp
      (measureSplittingPsi_contDiff σ).continuous.measurable
  have htop : ∀ᵐ y ∂(volume : Measure ℝ), ENNReal.ofReal (f y) < ∞ :=
    ae_of_all _ fun y => ENNReal.ofReal_lt_top
  have hρ : IsFiniteMeasure ρ := by
    dsimp [ρ]
    exact isFiniteMeasure_withDensity_ofReal hfi.2
  letI : IsFiniteMeasure ρ := hρ
  calc
    _ = ∫ᵛ y, g y ∂<•(volume.withDensityᵥ f) := by
      unfold initialSquarePsiComplexMeasure
      exact initialSquareNuComplexMeasure_integral_eq (volume.withDensityᵥ f) g
    _ = ∫ᵛ y, g y ∂<•ρ.toSignedMeasure := by
      congr 1
      exact initialSquarePsiMeasure_eq_toSignedMeasure_withDensity hSupp
    _ = ∫ y, g y ∂ρ := by
      rw [VectorMeasure.integral_toSignedMeasure]
    _ = ∫ y, (ENNReal.ofReal (f y)).toReal • g y ∂volume := by
      exact integral_withDensity_eq_integral_toReal_smul hmeas htop g
    _ = ∫ y, (f y : ℂ) * g y ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [ENNReal.toReal_ofReal (hnonneg y), smul_eq_mul]

private theorem initialSquareNuComplexMeasure_variation_isFinite
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) :
    IsFiniteMeasure (initialSquareNuComplexMeasure σ).variation := by
  letI : IsFiniteMeasure (measureSplittingNu σ).variation :=
    initialSquareNu_variation_isFinite hSupp hσ
  exact isFiniteMeasure_of_le (measureSplittingNu σ).variation
    (initialSquareNuComplexMeasure_variation_le (measureSplittingNu σ))

/-- The finite multiplier sum bound which supplies the Fourier side of the
`L²` square-function estimate in `lj:initial-square`. -/
theorem initialSquareNuFourier_finite_scale_sum_bound {σ : Measure ℝ}
    [IsProbabilityMeasure σ] {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    {b ξ : ℝ} (hb : 1 < b) (hβ : 0 < β) (F : Finset ℤ) :
    (∑ k ∈ F, ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ ^ 2) ≤
      (2 * Real.pi + 2 * |D|) ^ 2 *
        (1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β))) := by
  by_cases hξ : ξ = 0
  · subst ξ
    have hzero := initialSquareNuFourier_zero hSupp hσ
    have hbpos : 0 < b := by linarith
    have hinvpos : 0 < b⁻¹ := inv_pos.mpr hbpos
    have hinvlt : b⁻¹ < 1 := (inv_lt_one₀ hbpos).2 hb
    have hden1 : 0 < 1 - b⁻¹ ^ 2 := by nlinarith
    have hden2 : 0 < 1 - Real.rpow b (-2 * β) := by
      have hq : Real.rpow b (-2 * β) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
      linarith
    have hsum : 0 ≤
        1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β)) :=
      add_nonneg (div_nonneg (by norm_num) hden1.le)
        (div_nonneg (by norm_num) hden2.le)
    have hresult : 0 ≤ (2 * Real.pi + 2 * |D|) ^ 2 *
        (1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β))) :=
      mul_nonneg (sq_nonneg _) hsum
    simpa [hzero] using hresult
  · have hs : 0 < |ξ| := abs_pos.mpr hξ
    let H : ℝ := 2 * Real.pi + 2 * |D|
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hdecay : ∀ k ∈ F,
        ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ ≤
          H * initialSquareFrequencyWeight b β |ξ| k := by
      intro k hk
      have hbpow : 0 < b ^ k := zpow_pos (by linarith : 0 < b) k
      have harg : b ^ k * ξ ≠ 0 := mul_ne_zero (ne_of_gt hbpow) hξ
      have hbound := hσ.nu_fourier_decay harg
      have habs : |b ^ k * ξ| = b ^ k * |ξ| := by
        rw [abs_mul, abs_of_pos hbpow]
      calc
        ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ ≤
            H * min |b ^ k * ξ| (|b ^ k * ξ| ^ (-β)) := by
              simpa [H] using hbound
        _ = H * initialSquareFrequencyWeight b β |ξ| k := by
              rw [habs]
              rfl
    have hsum := initialSquareFrequencyWeight_squareSum_le hb hβ hs F
    have hnonneg : 0 ≤ H ^ 2 := sq_nonneg H
    calc
      (∑ k ∈ F, ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ ^ 2) ≤
          ∑ k ∈ F, (H * initialSquareFrequencyWeight b β |ξ| k) ^ 2 := by
            apply Finset.sum_le_sum
            intro k hk
            have hnonnegLeft : 0 ≤
                ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ := norm_nonneg _
            have hnonnegRight : 0 ≤
                H * initialSquareFrequencyWeight b β |ξ| k := by
              apply mul_nonneg hH
              unfold initialSquareFrequencyWeight
              exact le_min (by positivity) (Real.rpow_nonneg (by positivity) _)
            exact (sq_le_sq₀ hnonnegLeft hnonnegRight).2 (hdecay k hk)
      _ = H ^ 2 *
          ∑ k ∈ F, (initialSquareFrequencyWeight b β |ξ| k) ^ 2 := by
            simp_rw [mul_pow]
            rw [← Finset.mul_sum]
      _ ≤ H ^ 2 *
          (1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β))) :=
            mul_le_mul_of_nonneg_left hsum hnonneg
      _ = _ := by rfl

/-- Push the complexified cancellation measure forward to the scale `t`. -/
def initialSquareDilateComplexMeasure (μ : ComplexMeasure ℝ) (t : ℝ) :
    ComplexMeasure ℝ :=
  μ.map (fun x : ℝ => t * x)

/-- The complex convolution by a dilated smooth splitting measure, expressed
as its scalar density integral for any strongly measurable input. -/
theorem initialSquarePsiDilatedComplexMeasureConvolution_eq_integral
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (t : ℝ) (ht : t ≠ 0)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) (x : ℝ) :
    complexMeasureConvolution
        (initialSquareDilateComplexMeasure (initialSquarePsiComplexMeasure σ) t)
        f hf x =
      ∫ z, (measureSplittingPsi σ z : ℂ) * hf.mk f (x - t * z) ∂volume := by
  change (∫ᵛ y, hf.mk f (x - y) ∂[
      ContinuousLinearMap.mul ℝ ℂ;
      (initialSquarePsiComplexMeasure σ).map (fun y : ℝ => t * y)]) = _
  rw [(measurableEmbedding_mulLeft₀ ht).integral_map_vectorMeasure]
  exact initialSquarePsiComplexMeasure_integral_eq_density hSupp
    (fun z => hf.mk f (x - t * z))

#print axioms initialSquarePsiDilatedComplexMeasureConvolution_eq_integral

private theorem initialSquare_intervalIntegrable_comp_affine
    {g : ℝ → ℂ} (hg : LocallyIntegrable g volume)
    (x t : ℝ) (ht : 0 < t) :
    IntervalIntegrable (fun z => g (x - t * z)) volume (-2) 2 := by
  have htarget : IntervalIntegrable g volume (x - 2 * t) (x + 2 * t) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by nlinarith)]
    exact (hg.locallyIntegrableOn _).integrableOn_isCompact isCompact_Icc
  have hshift : IntervalIntegrable (fun z => g (x + z)) volume (-2 * t) (2 * t) := by
    simpa using
      (IntervalIntegrable.comp_add_left_iff (f := g)
        (a := x - 2 * t) (b := x + 2 * t) (c := x)).mpr htarget
  have hscaled : IntervalIntegrable (fun z => g (x + (-t) * z)) volume
      ((2 * t) / (-t)) ((-2 * t) / (-t)) := by
    exact hshift.symm.comp_mul_left (a := 2 * t) (b := -2 * t) (c := -t)
  convert hscaled using 1 <;> field_simp [ht.ne'] <;> ring_nf

/-- A smooth splitting density integral is bounded by the centered
Hardy--Littlewood average at twice the scale. -/
theorem initialSquare_psi_kernel_integral_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {g : ℝ → ℂ} (hg : LocallyIntegrable g volume)
    (x t : ℝ) (ht : 0 < t) :
    ‖∫ z, (measureSplittingPsi σ z : ℂ) * g (x - t * z) ∂volume‖ ≤
      4 * lpNorm φ ∞ volume * lineCenteredAverage g x (2 * t) := by
  let c : ℝ := lpNorm φ ∞ volume
  let P : ℝ → ℂ := fun z => (measureSplittingPsi σ z : ℂ) * g (x - t * z)
  let G : ℝ → ℂ := fun z => g (x - t * z)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact lpNorm_nonneg
  have hcomp : IntervalIntegrable G volume (-2) 2 := by
    simpa [G] using initialSquare_intervalIntegrable_comp_affine hg x t ht
  have hpsiCont : Continuous (fun z : ℝ => (measureSplittingPsi σ z : ℂ)) := by
    exact Complex.continuous_ofReal.comp (measureSplittingPsi_contDiff σ).continuous
  have hPint : IntervalIntegrable P volume (-2) 2 := by
    dsimp [P, G] at *
    exact hcomp.continuousOn_mul hpsiCont.continuousOn
  have hPzero : ∀ z, z ∉ Set.Icc (-(2 : ℝ)) 2 → P z = 0 := by
    intro z hz
    simp [P, measureSplittingPsi_eq_zero_of_not_mem_Icc σ hSupp hz]
  have hPsupport : Function.support P ⊆ Set.Icc (-(2 : ℝ)) 2 := by
    intro z hz
    by_contra hnot
    exact hz (hPzero z hnot)
  have hPIcc : IntegrableOn P (Set.Icc (-(2 : ℝ)) 2) volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le
      (μ := volume) (by norm_num : (-(2 : ℝ)) ≤ 2)).mp hPint
  have hPint' : Integrable P volume :=
    (integrableOn_iff_integrable_of_support_subset hPsupport).mp hPIcc
  have hGIcc : IntegrableOn (fun z => ‖G z‖) (Set.Icc (-(2 : ℝ)) 2) volume := by
    have hGIntIcc : IntegrableOn G (Set.Icc (-(2 : ℝ)) 2) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        (μ := volume) (by norm_num : (-(2 : ℝ)) ≤ 2)).mp hcomp
    exact hGIntIcc.norm
  have hmajorant : Integrable
      (fun z => c * Set.indicator (Set.Icc (-(2 : ℝ)) 2) (fun w => ‖G w‖) z)
      volume := by
    have h := hGIcc.integrable_indicator measurableSet_Icc
    simpa [mul_comm] using h.const_mul c
  have hpsiNonneg (z : ℝ) : 0 ≤ measureSplittingPsi σ z :=
    measureSplittingPsi_nonneg σ z
  have hpsiBound (z : ℝ) : measureSplittingPsi σ z ≤ c := by
    have h := measureSplittingPsi_iteratedDeriv_pointwise_bound σ 0 z
    simpa [c, iteratedDeriv_zero, Real.norm_eq_abs,
      abs_of_nonneg (hpsiNonneg z)] using h
  have hpoint : ∀ z,
      ‖P z‖ ≤ c * Set.indicator (Set.Icc (-(2 : ℝ)) 2)
        (fun w => ‖G w‖) z := by
    intro z
    by_cases hz : z ∈ Set.Icc (-(2 : ℝ)) 2
    · have hnorm : ‖(measureSplittingPsi σ z : ℂ)‖ = measureSplittingPsi σ z := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpsiNonneg z)]
      have hnormMul : ‖(measureSplittingPsi σ z : ℂ) * G z‖ =
          measureSplittingPsi σ z * ‖G z‖ := by
        rw [norm_mul, hnorm]
      change ‖(measureSplittingPsi σ z : ℂ) * G z‖ ≤
        c * Set.indicator (Set.Icc (-(2 : ℝ)) 2)
          (fun w => ‖G w‖) z
      rw [Set.indicator_of_mem hz, hnormMul]
      exact mul_le_mul_of_nonneg_right (hpsiBound z) (norm_nonneg _)
    · simp [P, G, hz,
        measureSplittingPsi_eq_zero_of_not_mem_Icc σ hSupp hz]
  have hmass :
      (∫ z, ‖G z‖ ∂(volume.restrict (Set.Icc (-(2 : ℝ)) 2))) =
        ∫ z in (-(2 : ℝ))..2, ‖G z‖ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hchange :
      (∫ z in (-(2 : ℝ))..2, ‖G z‖) =
        t⁻¹ * (∫ y in x - 2 * t..x + 2 * t, ‖g y‖) := by
    have h := intervalIntegral.integral_comp_sub_mul
      (f := fun y : ℝ => ‖g y‖) (a := -(2 : ℝ)) (b := 2)
      (c := t) ht.ne' x
    have hleft : (∫ z in (-(2 : ℝ))..2, ‖G z‖) =
        ∫ z in (-(2 : ℝ))..2, ‖g (x - t * z)‖ := by rfl
    have hend₁ : x - t * 2 = x - 2 * t := by ring
    have hend₂ : x - t * (-(2 : ℝ)) = x + 2 * t := by ring
    rw [← hleft, hend₁, hend₂] at h
    simpa only [smul_eq_mul] using h
  have haverage :
      lineCenteredAverage g x (2 * t) =
        (∫ y in x - 2 * t..x + 2 * t, ‖g y‖) / (4 * t) := by
    simp [lineCenteredAverage]
    field_simp [ht.ne']
    ring
  calc
    ‖∫ z, P z ∂volume‖ ≤ ∫ z, ‖P z‖ ∂volume := by
      exact norm_integral_le_integral_norm P
    _ ≤ ∫ z, c * Set.indicator (Set.Icc (-(2 : ℝ)) 2)
          (fun w => ‖G w‖) z ∂volume :=
        integral_mono_ae hPint'.norm hmajorant
          (ae_of_all volume fun z => hpoint z)
    _ = c * ∫ z, ‖G z‖ ∂(volume.restrict (Set.Icc (-(2 : ℝ)) 2)) := by
        rw [integral_const_mul, integral_indicator measurableSet_Icc]
    _ = c * (∫ z in (-(2 : ℝ))..2, ‖G z‖) := by rw [hmass]
    _ = 4 * c * lineCenteredAverage g x (2 * t) := by
        rw [hchange, haverage]
        field_simp [ht.ne']

private theorem initialSquare_lineCenteredAverage_congr_ae
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) (x r : ℝ) :
    lineCenteredAverage f x r = lineCenteredAverage g x r := by
  unfold lineCenteredAverage
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hfg] with y hy
  simp [hy]

/-- The pointwise smooth-measure convolution is dominated by the centered
maximal function, with the exact factor `4 * ‖φ‖∞` from `lj:initial-square`.
The right side is the extended-valued maximal function, so the estimate also
holds at exceptional points where that maximal function is infinite. -/
theorem initialSquarePsiConvolution_maximal_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume)
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ENNReal.ofReal ‖complexMeasureConvolution
        (initialSquareDilateComplexMeasure (initialSquarePsiComplexMeasure σ) t)
        f hf.aestronglyMeasurable x‖ ≤
      ENNReal.ofReal (4 * lpNorm φ ∞ volume) * lineMaximal f x := by
  let hsm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  let g : ℝ → ℂ := hsm.mk f
  have hfg : f =ᵐ[volume] g := hsm.ae_eq_mk
  have hlocf : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hlocg : LocallyIntegrable g volume := hlocf.congr hfg
  have hconv := initialSquarePsiDilatedComplexMeasureConvolution_eq_integral
    hSupp t ht.ne' f hsm x
  have hkernel := initialSquare_psi_kernel_integral_bound hSupp hlocg x t ht
  have haverageEq := initialSquare_lineCenteredAverage_congr_ae hfg x (2 * t)
  have havgNonneg : 0 ≤ lineCenteredAverage f x (2 * t) := by
    unfold lineCenteredAverage
    apply div_nonneg
    · exact intervalIntegral.integral_nonneg (by nlinarith [ht])
        (fun y _ => norm_nonneg (f y))
    · positivity
  have hmax : ENNReal.ofReal (lineCenteredAverage f x (2 * t)) ≤
      lineMaximal f x := by
    unfold lineMaximal
    exact le_iSup_of_le ⟨2 * t, by linarith⟩ le_rfl
  have hcoef : 0 ≤ 4 * lpNorm φ ∞ volume := by
    exact mul_nonneg (by norm_num) lpNorm_nonneg
  calc
    _ = ENNReal.ofReal ‖(∫ z, (measureSplittingPsi σ z : ℂ) *
          g (x - t * z) ∂volume)‖ := by
      rw [hconv]
    _ ≤ ENNReal.ofReal (4 * lpNorm φ ∞ volume *
          lineCenteredAverage g x (2 * t)) :=
      ENNReal.ofReal_le_ofReal hkernel
    _ = ENNReal.ofReal (4 * lpNorm φ ∞ volume) *
          ENNReal.ofReal (lineCenteredAverage f x (2 * t)) := by
      rw [← haverageEq, ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (4 * lpNorm φ ∞ volume) * lineMaximal f x :=
      mul_le_mul_of_nonneg_left hmax bot_le

/-- The smooth-part maximal comparison at every finite exponent `q>1`.
The density calculation needs only local integrability, which follows
from `MemLp f q`; global `L²` membership is unnecessary. -/
theorem initialSquarePsiConvolution_maximal_bound_of_memLp
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {q : ℝ} (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f (ENNReal.ofReal q) volume)
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ENNReal.ofReal ‖complexMeasureConvolution
        (initialSquareDilateComplexMeasure (initialSquarePsiComplexMeasure σ) t)
        f hf.aestronglyMeasurable x‖ ≤
      ENNReal.ofReal (4 * lpNorm φ ∞ volume) * lineMaximal f x := by
  let hsm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  let g : ℝ → ℂ := hsm.mk f
  have hfg : f =ᵐ[volume] g := hsm.ae_eq_mk
  have hlocf : LocallyIntegrable f volume :=
    hf.locallyIntegrable (ENNReal.one_le_ofReal.mpr hq.le)
  have hlocg : LocallyIntegrable g volume := hlocf.congr hfg
  have hconv := initialSquarePsiDilatedComplexMeasureConvolution_eq_integral
    hSupp t ht.ne' f hsm x
  have hkernel := initialSquare_psi_kernel_integral_bound hSupp hlocg x t ht
  have haverageEq := initialSquare_lineCenteredAverage_congr_ae hfg x (2 * t)
  have havgNonneg : 0 ≤ lineCenteredAverage f x (2 * t) := by
    unfold lineCenteredAverage
    apply div_nonneg
    · exact intervalIntegral.integral_nonneg (by nlinarith [ht])
        (fun y _ => norm_nonneg (f y))
    · positivity
  have hmax : ENNReal.ofReal (lineCenteredAverage f x (2 * t)) ≤
      lineMaximal f x := by
    unfold lineMaximal
    exact le_iSup_of_le ⟨2 * t, by linarith⟩ le_rfl
  have hcoef : 0 ≤ 4 * lpNorm φ ∞ volume := by
    exact mul_nonneg (by norm_num) lpNorm_nonneg
  calc
    _ = ENNReal.ofReal ‖(∫ z, (measureSplittingPsi σ z : ℂ) *
          g (x - t * z) ∂volume)‖ := by
      rw [hconv]
    _ ≤ ENNReal.ofReal (4 * lpNorm φ ∞ volume *
          lineCenteredAverage g x (2 * t)) :=
      ENNReal.ofReal_le_ofReal hkernel
    _ = ENNReal.ofReal (4 * lpNorm φ ∞ volume) *
          ENNReal.ofReal (lineCenteredAverage f x (2 * t)) := by
      rw [← haverageEq, ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (4 * lpNorm φ ∞ volume) * lineMaximal f x :=
      mul_le_mul_of_nonneg_left hmax bot_le

#print axioms initialSquarePsiConvolution_maximal_bound_of_memLp

theorem initialSquareDilateComplexMeasure_sub (μ ν : ComplexMeasure ℝ)
    (t : ℝ) :
    initialSquareDilateComplexMeasure (μ - ν) t =
      initialSquareDilateComplexMeasure μ t - initialSquareDilateComplexMeasure ν t := by
  ext E hE
  change ((μ - ν).map (fun x : ℝ => t * x)) E =
    ((μ.map (fun x : ℝ => t * x)) - (ν.map (fun x : ℝ => t * x))) E
  rw [MeasureTheory.VectorMeasure.map_apply (v := μ - ν) (by fun_prop) hE]
  simp only [_root_.sub_apply]
  rw [MeasureTheory.VectorMeasure.map_apply (v := μ) (by fun_prop) hE,
    MeasureTheory.VectorMeasure.map_apply (v := ν) (by fun_prop) hE]

private theorem initialSquare_lpComplexMeasureConvolution_sub
    (μ ν : ComplexMeasure ℝ)
    [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation]
    [IsFiniteMeasure (μ - ν).variation]
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    lpComplexMeasureConvolution 2 (μ - ν) F =
      lpComplexMeasureConvolution 2 μ F - lpComplexMeasureConvolution 2 ν F := by
  have hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  unfold lpComplexMeasureConvolution
  exact VectorMeasure.integral_sub_vectorMeasure
    (integrable_lpRightTranslate hp μ F)
    (integrable_lpRightTranslate hp ν F)

theorem initialSquare_complexMeasureConvolution_sub
    (μ ν : ComplexMeasure ℝ)
    [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation]
    [IsFiniteMeasure (μ - ν).variation]
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) (x : ℝ)
    (hμ : μ.Integrable (fun y : ℝ => hf.mk f (x - y)))
    (hν : ν.Integrable (fun y : ℝ => hf.mk f (x - y))) :
    complexMeasureConvolution (μ - ν) f hf x =
      complexMeasureConvolution μ f hf x -
        complexMeasureConvolution ν f hf x := by
  unfold complexMeasureConvolution
  exact VectorMeasure.integral_sub_vectorMeasure hμ hν

theorem initialSquare_complexMeasureFourier_dilate
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (t ξ : ℝ) :
    complexMeasureFourier (initialSquareDilateComplexMeasure μ t) ξ =
      complexMeasureFourier μ (t * ξ) := by
  let φ : ℝ → ℝ := fun x => t * x
  have hfm : AEStronglyMeasurable
      (fun y : ℝ => (Real.fourierChar (-(y * ξ)) : ℂ))
      (μ.variation.map φ) := by
    have harg : Continuous (fun y : ℝ => -(y * ξ)) := by fun_prop
    exact (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp harg)).aestronglyMeasurable
  have hfi : μ.Integrable
      (fun x : ℝ => (Real.fourierChar (-(φ x * ξ)) : ℂ)) := by
    change Integrable (fun x : ℝ => (Real.fourierChar (-(φ x * ξ)) : ℂ)) μ.variation
    apply (integrable_const (1 : ℝ)).mono'
    · have harg : Continuous (fun x : ℝ => -(φ x * ξ)) := by fun_prop
      exact (continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp harg)).aestronglyMeasurable
    · filter_upwards [] with x
      simp
  unfold complexMeasureFourier initialSquareDilateComplexMeasure
  rw [VectorMeasure.integral_map (by fun_prop) hfm hfi]
  congr 1
  funext x
  congr 1
  congr 1
  ring

theorem initialSquareNuComplexMeasure_fourier_eq
    {σ : Measure ℝ} [IsFiniteMeasure σ] (ξ : ℝ) :
    complexMeasureFourier (initialSquareNuComplexMeasure σ) ξ =
      measureSplittingNuFourier σ ξ := by
  unfold complexMeasureFourier measureSplittingNuFourier
  change (∫ᵛ y, (Real.fourierChar (-(y * ξ)) : ℂ)
      ∂[ContinuousLinearMap.mul ℝ ℂ;
        (measureSplittingNu σ).toComplexMeasure 0]) = _
  rw [initialSquareNuComplexMeasure_integral_eq]
  apply VectorMeasure.integral_congr_ae
  filter_upwards [] with x
  rw [Real.fourierChar_apply]
  congr 1
  congr 1
  push_cast
  ring

/-- The Fourier transform of a dilated cancellation complex measure is
the source cancellation Fourier coefficient at the scaled frequency. -/
theorem initialSquareNuDilateComplexMeasure_fourier_eq
    {σ : Measure ℝ} [IsFiniteMeasure σ]
    [IsFiniteMeasure (initialSquareNuComplexMeasure σ).variation]
    (t ξ : ℝ) :
    complexMeasureFourier
        (initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ) t) ξ =
      measureSplittingNuFourier σ (t * ξ) := by
  rw [initialSquare_complexMeasureFourier_dilate,
    initialSquareNuComplexMeasure_fourier_eq]

#print axioms initialSquareNuDilateComplexMeasure_fourier_eq

/-- At every frequency, the finite family of scaled complex-measure
multipliers has the same geometric bound as the cancellation Fourier
coefficients in `lj:measure-splitting`. -/
theorem initialSquare_scaledNuMultiplier_frequency_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β) (F : Finset ℤ) :
    ∀ ξ : ℝ,
      (∑ k : {k : ℤ // k ∈ F},
        ‖complexMeasureFourier
          (initialSquareDilateComplexMeasure
            (initialSquareNuComplexMeasure σ)
            (b ^ k.1)) ξ‖ ^ 2) ≤
        (2 * Real.pi + 2 * |D|) ^ 2 *
          (1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β))) := by
  classical
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  have hμfinite : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite hSupp hσ
  letI : IsFiniteMeasure μ.variation := hμfinite
  intro ξ
  have hFourier (k : {k : ℤ // k ∈ F}) :
      complexMeasureFourier
          (initialSquareDilateComplexMeasure
            (initialSquareNuComplexMeasure σ) (b ^ k.1)) ξ =
        measureSplittingNuFourier σ (b ^ k.1 * ξ) := by
    letI : IsFiniteMeasure
        (initialSquareDilateComplexMeasure
          (initialSquareNuComplexMeasure σ) (b ^ k.1)).variation := by
      change IsFiniteMeasure
        ((initialSquareNuComplexMeasure σ).map
          (fun x : ℝ => b ^ k.1 * x)).variation
      infer_instance
    calc
      complexMeasureFourier
          (initialSquareDilateComplexMeasure
            (initialSquareNuComplexMeasure σ) (b ^ k.1)) ξ =
          complexMeasureFourier (initialSquareNuComplexMeasure σ)
            (b ^ k.1 * ξ) :=
        initialSquare_complexMeasureFourier_dilate
          (initialSquareNuComplexMeasure σ) (b ^ k.1) ξ
      _ = measureSplittingNuFourier σ (b ^ k.1 * ξ) :=
        initialSquareNuComplexMeasure_fourier_eq
          (σ := σ) (b ^ k.1 * ξ)
  calc
    (∑ k : {k : ℤ // k ∈ F},
        ‖complexMeasureFourier
          (initialSquareDilateComplexMeasure
            (initialSquareNuComplexMeasure σ) (b ^ k.1)) ξ‖ ^ 2) =
        ∑ k : {k : ℤ // k ∈ F},
          ‖measureSplittingNuFourier σ (b ^ k.1 * ξ)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hFourier k]
    _ ≤ (2 * Real.pi + 2 * |D|) ^ 2 *
          (1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β))) := by
          rw [Finset.univ_eq_attach,
            Finset.sum_attach F (fun n : ℤ =>
              ‖measureSplittingNuFourier σ (b ^ n * ξ)‖ ^ 2)]
          exact initialSquareNuFourier_finite_scale_sum_bound
            hSupp hσ hb hβ F (ξ := ξ)

private theorem initialSquare_lp_two_norm_sq_eq_integral_norm_sq
    (U : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖U‖ ^ 2 = ∫ x, ‖U x‖ ^ 2 ∂(volume : Measure ℝ) := by
  calc
    ‖U‖ ^ 2 = RCLike.re (inner ℂ U U) :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) U).symm
    _ = RCLike.re (∫ x, inner ℂ (U x) (U x) ∂(volume : Measure ℝ)) := by
      rw [L2.inner_def]
    _ = ∫ x, RCLike.re (inner ℂ (U x) (U x)) ∂(volume : Measure ℝ) :=
      (integral_re (L2.integrable_inner U U)).symm
    _ = ∫ x, ‖U x‖ ^ 2 ∂(volume : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (U x)

/-- A finite multiplier square function is bounded by the square root of a
uniform pointwise sum of squared multiplier coefficients. -/
theorem finiteFourierMultiplierSquareFunction_norm_le_of_frequency_bound
    {ι : Type*} [Fintype ι]
    (M : ι → Lp ℂ ∞ (volume : Measure ℝ))
    (G : Lp ℂ 2 (volume : Measure ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ᵐ ξ ∂(volume : Measure ℝ),
      (∑ i : ι, ‖(M i : ℝ → ℂ) ξ‖ ^ 2) ≤ C) :
    ‖finiteFourierMultiplierSquareFunctionLp M G‖ ≤
      Real.sqrt C * ‖G‖ := by
  classical
  let ghat := realFourierTransformL2 G
  have hghatMem : MemLp (ghat : ℝ → ℂ) 2 volume := Lp.memLp ghat
  have hghatInt : Integrable (fun ξ : ℝ => ‖(ghat : ℝ → ℂ) ξ‖ ^ 2) volume :=
    hghatMem.integrable_norm_pow (by norm_num)
  have hprod : ∀ᵐ ξ ∂(volume : Measure ℝ),
      (∑ i : ι, ‖(M i : ℝ → ℂ) ξ‖ ^ 2 *
        ‖(ghat : ℝ → ℂ) ξ‖ ^ 2) ≤
        C * ‖(ghat : ℝ → ℂ) ξ‖ ^ 2 := by
    filter_upwards [hcoeff] with ξ hξ
    calc
      (∑ i : ι, ‖(M i : ℝ → ℂ) ξ‖ ^ 2 *
          ‖(ghat : ℝ → ℂ) ξ‖ ^ 2) =
          (∑ i : ι, ‖(M i : ℝ → ℂ) ξ‖ ^ 2) *
            ‖(ghat : ℝ → ℂ) ξ‖ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ C * ‖(ghat : ℝ → ℂ) ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hξ (sq_nonneg _)
  have hRHSInt : Integrable
      (fun ξ : ℝ => C * ‖(ghat : ℝ → ℂ) ξ‖ ^ 2) volume := by
    simpa only [mul_comm] using hghatInt.const_mul C
  have hLHSMeas : AEStronglyMeasurable
      (fun ξ : ℝ => ∑ i : ι, ‖(M i : ℝ → ℂ) ξ‖ ^ 2 *
        ‖(ghat : ℝ → ℂ) ξ‖ ^ 2) volume := by
    convert Finset.aestronglyMeasurable_sum
      (Finset.univ : Finset ι) (by
        intro i hi
        exact ((Lp.memLp (M i)).aestronglyMeasurable.norm.pow 2).mul
          (hghatMem.aestronglyMeasurable.norm.pow 2)) using 1
    ext ξ
    simp
  have hLHSInt : Integrable
      (fun ξ : ℝ => ∑ i : ι, ‖(M i : ℝ → ℂ) ξ‖ ^ 2 *
        ‖(ghat : ℝ → ℂ) ξ‖ ^ 2) volume := by
    apply hRHSInt.mono' hLHSMeas
    filter_upwards [hprod] with ξ hξ
    have hnonneg : 0 ≤
        ∑ i : ι, ‖(M i : ℝ → ℂ) ξ‖ ^ 2 *
          ‖(ghat : ℝ → ℂ) ξ‖ ^ 2 :=
      Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hξ
  have hSq :
      ‖finiteFourierMultiplierSquareFunctionLp M G‖ ^ 2 ≤
        C * ‖realFourierTransformL2 G‖ ^ 2 := by
    rw [finiteFourierMultiplierSquareNormFormula]
    calc
      (∫ ξ, ∑ i : ι, ‖(M i : ℝ → ℂ) ξ‖ ^ 2 *
          ‖(ghat : ℝ → ℂ) ξ‖ ^ 2 ∂(volume : Measure ℝ)) ≤
          ∫ ξ, C * ‖(ghat : ℝ → ℂ) ξ‖ ^ 2 ∂(volume : Measure ℝ) :=
        integral_mono_ae hLHSInt hRHSInt hprod
      _ = C * ‖realFourierTransformL2 G‖ ^ 2 := by
        rw [integral_const_mul,
          ← initialSquare_lp_two_norm_sq_eq_integral_norm_sq]
  have hroot : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
  have hsqRoot :
      ‖finiteFourierMultiplierSquareFunctionLp M G‖ ^ 2 ≤
        (Real.sqrt C * ‖G‖) ^ 2 := by
    calc
      ‖finiteFourierMultiplierSquareFunctionLp M G‖ ^ 2 ≤
          C * ‖realFourierTransformL2 G‖ ^ 2 := hSq
      _ = (Real.sqrt C * ‖G‖) ^ 2 := by
          rw [norm_realFourierTransformL2, mul_pow, Real.sq_sqrt hC]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hroot (norm_nonneg _))).1 hsqRoot

/-- The finite family of Fourier multipliers of the dilated cancellation
measure, with finite variation supplied by `lj:measure-splitting`. -/
def initialSquareNuFiniteScaleMultipliers
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (b : ℝ) (F : Finset ℤ) :
    {k : ℤ // k ∈ F} → Lp ℂ ∞ (volume : Measure ℝ) := by
  classical
  intro k
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  letI : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite hSupp hσ
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μ (b ^ k.1)).variation := by
    change IsFiniteMeasure (μ.map (fun x : ℝ => b ^ k.1 * x)).variation
    infer_instance
  exact complexMeasureFourierLpTop
    (initialSquareDilateComplexMeasure μ (b ^ k.1))

/-- Finite-scale `L²` square-function estimate with the exact constant
`A_ν` from `lj:initial-square`. -/
theorem initialSquare_finite_scale_square_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β) (F : Finset ℤ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖finiteFourierMultiplierSquareFunctionLp
      (initialSquareNuFiniteScaleMultipliers hSupp hσ b F) G‖ ≤
        (2 * Real.pi + 2 * |D|) *
          Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
            1 / (1 - Real.rpow b (-2 * β))) * ‖G‖ := by
  classical
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  have hμfinite : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite hSupp hσ
  letI : IsFiniteMeasure μ.variation := hμfinite
  let M : {k : ℤ // k ∈ F} → Lp ℂ ∞ (volume : Measure ℝ) :=
    initialSquareNuFiniteScaleMultipliers hSupp hσ b F
  have hcoea (k : {k : ℤ // k ∈ F}) : (M k : ℝ → ℂ) =ᵐ[volume]
      complexMeasureFourier
        (initialSquareDilateComplexMeasure μ (b ^ k.1)) := by
    letI : IsFiniteMeasure
        (initialSquareDilateComplexMeasure μ (b ^ k.1)).variation := by
      change IsFiniteMeasure (μ.map (fun x : ℝ => b ^ k.1 * x)).variation
      infer_instance
    exact coeFn_complexMeasureFourierLpTop _
  have hcommon : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ∀ k : {k : ℤ // k ∈ F},
      (M k : ℝ → ℂ) ξ =
        complexMeasureFourier
          (initialSquareDilateComplexMeasure μ (b ^ k.1)) ξ := by
    rw [ae_all_iff]
    exact hcoea
  have hcoeff : ∀ᵐ ξ ∂(volume : Measure ℝ),
      (∑ k : {k : ℤ // k ∈ F}, ‖(M k : ℝ → ℂ) ξ‖ ^ 2) ≤
        (2 * Real.pi + 2 * |D|) ^ 2 *
          (1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β))) := by
    filter_upwards [hcommon] with ξ hξ
    calc
      (∑ k : {k : ℤ // k ∈ F}, ‖(M k : ℝ → ℂ) ξ‖ ^ 2) =
          ∑ k : {k : ℤ // k ∈ F}, ‖complexMeasureFourier
            (initialSquareDilateComplexMeasure μ (b ^ k.1)) ξ‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hξ k]
      _ ≤ (2 * Real.pi + 2 * |D|) ^ 2 *
            (1 / (1 - b⁻¹ ^ 2) + 1 / (1 - Real.rpow b (-2 * β))) := by
              simpa only [μ] using
                initialSquare_scaledNuMultiplier_frequency_bound
                  hSupp hσ hb hβ F ξ
  have hbpos : 0 < b := by linarith
  have hinvlt : b⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < b)).2 hb
  have hinvnonneg : 0 ≤ b⁻¹ := inv_nonneg.mpr hbpos.le
  have hden1 : 0 < 1 - b⁻¹ ^ 2 := by nlinarith
  have hpowlt : Real.rpow b (-2 * β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  have hden2 : 0 < 1 - Real.rpow b (-2 * β) := by linarith
  let S : ℝ := 1 / (1 - b⁻¹ ^ 2) +
    1 / (1 - Real.rpow b (-2 * β))
  have hS : 0 < S := by
    dsimp [S]
    exact add_pos (div_pos (by norm_num) hden1)
      (div_pos (by norm_num) hden2)
  let H : ℝ := 2 * Real.pi + 2 * |D|
  let A : ℝ := H * Real.sqrt S
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAsq : A ^ 2 = H ^ 2 * S := by
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt hS.le]
  have hcoeff' : ∀ᵐ ξ ∂(volume : Measure ℝ),
      (∑ k : {k : ℤ // k ∈ F}, ‖(M k : ℝ → ℂ) ξ‖ ^ 2) ≤ A ^ 2 := by
    simpa only [hAsq] using hcoeff
  have hfinite :=
    finiteFourierMultiplierSquareFunction_norm_le_of_frequency_bound
      M G (C := A ^ 2) (sq_nonneg A) hcoeff'
  have hroot : Real.sqrt (A ^ 2) = A := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hA]
  have hfinite' :
      ‖finiteFourierMultiplierSquareFunctionLp M G‖ ≤ A * ‖G‖ := by
    simpa only [hroot] using hfinite
  simpa [M, A, H, S] using hfinite'

/-- Convolution by the dilated cancellation measure, as an `L²` element. -/
def initialSquareNuConvolution
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (b : ℝ) (k : ℤ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) := by
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  letI : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite hSupp hσ
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μ (b ^ k)).variation := by
    change IsFiniteMeasure (μ.map (fun x : ℝ => b ^ k * x)).variation
    infer_instance
  exact lpComplexMeasureConvolution 2
    (initialSquareDilateComplexMeasure μ (b ^ k)) G

/-- The pointwise convolution representative at a scale agrees almost
everywhere with the `L²` vector-measure convolution. -/
theorem initialSquareNuConvolution_ae_eq_complexMeasureConvolution
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (b : ℝ) (k : ℤ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    (initialSquareNuConvolution hSupp hσ b k G : ℝ → ℂ) =ᵐ[volume]
      complexMeasureConvolution
        (initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ) (b ^ k))
        (fun x : ℝ => G x) (Lp.aestronglyMeasurable G) := by
  let ν : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  have hν : IsFiniteMeasure ν.variation := by
    dsimp [ν]
    exact initialSquareNuComplexMeasure_variation_isFinite hSupp hσ
  letI : IsFiniteMeasure ν.variation := hν
  let μ : ComplexMeasure ℝ := initialSquareDilateComplexMeasure ν (b ^ k)
  have hμ : IsFiniteMeasure μ.variation := by
    change IsFiniteMeasure (ν.map (fun x : ℝ => b ^ k * x)).variation
    infer_instance
  letI : IsFiniteMeasure μ.variation := hμ
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure ν (b ^ k)).variation := by
    change IsFiniteMeasure (ν.map (fun x : ℝ => b ^ k * x)).variation
    infer_instance
  simpa [initialSquareNuConvolution, μ, ν] using
    (lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution μ G)

private theorem initialSquareNuConvolution_sub_split
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (k : ℤ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    initialSquareNuConvolution hSupp hσ b k G =
      lpComplexMeasureConvolution 2
          (initialSquareDilateComplexMeasure (initialSquareSigmaComplexMeasure σ)
            (b ^ k)) G -
        lpComplexMeasureConvolution 2
          (initialSquareDilateComplexMeasure (initialSquarePsiComplexMeasure σ)
            (b ^ k)) G := by
  let μσ := initialSquareSigmaComplexMeasure σ
  let μψ := initialSquarePsiComplexMeasure σ
  have hsplit : initialSquareNuComplexMeasure σ = μσ - μψ := by
    exact initialSquareNuComplexMeasure_sub_split σ
  have hσvar : IsFiniteMeasure μσ.variation := by
    change IsFiniteMeasure ((σ.toSignedMeasure.toComplexMeasure 0).variation)
    rw [initialSquareNuComplexMeasure_variation_eq (σ.toSignedMeasure),
      Measure.variation_toSignedMeasure]
    infer_instance
  have hψrealvar : IsFiniteMeasure
      (volume.withDensityᵥ (measureSplittingPsi σ)).variation := by
    rw [isFiniteMeasure_iff, initialSquareDensityVariationMass hSupp hσ]
    norm_num
  have hψvar : IsFiniteMeasure μψ.variation := by
    dsimp [μψ, initialSquarePsiComplexMeasure]
    rw [initialSquareNuComplexMeasure_variation_eq]
    exact hψrealvar
  let t := b ^ k
  let μ := initialSquareNuComplexMeasure σ
  have hμvar : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite hSupp hσ
  letI : IsFiniteMeasure μ.variation := hμvar
  have hσdvar : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μσ t).variation := by
    change IsFiniteMeasure (μσ.map (fun x : ℝ => t * x)).variation
    infer_instance
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μσ t).variation := hσdvar
  have hψdvar : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μψ t).variation := by
    change IsFiniteMeasure (μψ.map (fun x : ℝ => t * x)).variation
    infer_instance
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μψ t).variation := hψdvar
  have hdilate : initialSquareDilateComplexMeasure μ t =
      initialSquareDilateComplexMeasure μσ t -
        initialSquareDilateComplexMeasure μψ t := by
    dsimp [μ]
    rw [hsplit]
    exact initialSquareDilateComplexMeasure_sub μσ μψ t
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μσ t -
        initialSquareDilateComplexMeasure μψ t).variation := by
    rw [← hdilate]
    change IsFiniteMeasure (μ.map (fun x : ℝ => t * x)).variation
    exact inferInstance
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μ t).variation := by
    rw [hdilate]
    infer_instance
  change lpComplexMeasureConvolution 2
      (initialSquareDilateComplexMeasure μ t) G = _
  rw [hdilate]
  exact initialSquare_lpComplexMeasureConvolution_sub
    (initialSquareDilateComplexMeasure μσ t)
    (initialSquareDilateComplexMeasure μψ t) G

private theorem initialSquareSigmaConvolution_ae_eq_nu_add_psi
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (k : ℤ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    complexMeasureConvolution
        (initialSquareDilateComplexMeasure (initialSquareSigmaComplexMeasure σ)
          (b ^ k))
        (fun x : ℝ => G x) (Lp.aestronglyMeasurable G) =ᵐ[volume]
      (initialSquareNuConvolution hSupp hσ b k G : ℝ → ℂ) +
        complexMeasureConvolution
          (initialSquareDilateComplexMeasure (initialSquarePsiComplexMeasure σ)
            (b ^ k))
          (fun x : ℝ => G x) (Lp.aestronglyMeasurable G) := by
  let μσ := initialSquareSigmaComplexMeasure σ
  let μψ := initialSquarePsiComplexMeasure σ
  have hσvar : IsFiniteMeasure μσ.variation := by
    change IsFiniteMeasure ((σ.toSignedMeasure.toComplexMeasure 0).variation)
    rw [initialSquareNuComplexMeasure_variation_eq (σ.toSignedMeasure),
      Measure.variation_toSignedMeasure]
    infer_instance
  have hψrealvar : IsFiniteMeasure
      (volume.withDensityᵥ (measureSplittingPsi σ)).variation := by
    rw [isFiniteMeasure_iff, initialSquareDensityVariationMass hSupp hσ]
    norm_num
  have hψvar : IsFiniteMeasure μψ.variation := by
    dsimp [μψ, initialSquarePsiComplexMeasure]
    rw [initialSquareNuComplexMeasure_variation_eq]
    exact hψrealvar
  let t : ℝ := b ^ k
  let μσt := initialSquareDilateComplexMeasure μσ t
  let μψt := initialSquareDilateComplexMeasure μψ t
  have hσtvar : IsFiniteMeasure μσt.variation := by
    change IsFiniteMeasure (μσ.map (fun x : ℝ => t * x)).variation
    infer_instance
  have hψtvar : IsFiniteMeasure μψt.variation := by
    change IsFiniteMeasure (μψ.map (fun x : ℝ => t * x)).variation
    infer_instance
  letI : IsFiniteMeasure μσt.variation := hσtvar
  letI : IsFiniteMeasure μψt.variation := hψtvar
  let σLp := lpComplexMeasureConvolution 2 μσt G
  let ψLp := lpComplexMeasureConvolution 2 μψt G
  let νLp := initialSquareNuConvolution hSupp hσ b k G
  have hνsplit : νLp = σLp - ψLp := by
    simpa [νLp, σLp, ψLp, μσ, μψ, μσt, μψt, t] using
      initialSquareNuConvolution_sub_split hSupp hσ k G
  have hLp : σLp = νLp + ψLp := by
    calc
      σLp = (σLp - ψLp) + ψLp := by abel
      _ = νLp + ψLp := by rw [← hνsplit]
  have hLpAE : (σLp : ℝ → ℂ) =ᵐ[volume] (νLp + ψLp : Lp ℂ 2 volume) := by
    rw [hLp]
  have hσrep := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution μσt G
  have hψrep := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution μψt G
  have hνrep := initialSquareNuConvolution_ae_eq_complexMeasureConvolution
    hSupp hσ b k G
  have hadd := Lp.coeFn_add νLp ψLp
  filter_upwards [hσrep, hψrep, hνrep, hLpAE, hadd] with x hσrep hψrep hνrep hLpAE hadd
  calc
    complexMeasureConvolution μσt (fun x : ℝ => G x)
        (Lp.aestronglyMeasurable G) x = σLp x := hσrep.symm
    _ = (νLp + ψLp) x := hLpAE
    _ = νLp x + ψLp x := hadd
    _ = (initialSquareNuConvolution hSupp hσ b k G : ℝ → ℂ) x +
        complexMeasureConvolution μψt (fun x : ℝ => G x)
          (Lp.aestronglyMeasurable G) x := by rw [hνrep, hψrep]

/-- The single-scale Fourier multiplier for the cancellation measure. -/
def initialSquareNuFourierMultiplier
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (b : ℝ) (k : ℤ) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  initialSquareNuFiniteScaleMultipliers hSupp hσ b ({k} : Finset ℤ)
    ⟨k, by simp⟩

/-- Fourier inversion identifies the finite-measure convolution with its
multiplier operator at every geometric scale. -/
theorem initialSquareNuConvolution_eq_fourierMultiplier
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (k : ℤ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    initialSquareNuConvolution hSupp hσ b k G =
      realFourierMultiplier (initialSquareNuFourierMultiplier hSupp hσ b k) G := by
  classical
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  have hμfinite : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite hSupp hσ
  letI : IsFiniteMeasure μ.variation := hμfinite
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μ (b ^ k)).variation := by
    change IsFiniteMeasure (μ.map (fun x : ℝ => b ^ k * x)).variation
    infer_instance
  apply realFourierTransformL2.injective
  change realFourierTransformL2
      (lpComplexMeasureConvolution 2
        (initialSquareDilateComplexMeasure μ (b ^ k)) G) = _
  rw [fourier_lpComplexMeasureConvolution]
  simp [realFourierMultiplier]
  have hM : complexMeasureFourierLpTop
      (initialSquareDilateComplexMeasure μ (b ^ k)) =
      initialSquareNuFourierMultiplier hSupp hσ b k := by
    simp [initialSquareNuFourierMultiplier,
      initialSquareNuFiniteScaleMultipliers, μ]
  rw [← hM]

private theorem initialSquare_sum_subtype_eq_nested {F : Finset ℤ}
    (f : {k : ℤ // k ∈ F} → ℝ) (g : ℤ → ℝ)
    (hfg : ∀ k, f k = g k.1) :
    (∑ k : {k : ℤ // k ∈ F}, f k) = ∑ k ∈ F, g k := by
  calc
    (∑ k : {k : ℤ // k ∈ F}, f k) =
        ∑ k : {k : ℤ // k ∈ F}, g k.1 := by
      apply Finset.sum_congr rfl
      intro k _
      exact hfg k
    _ = ∑ k ∈ F, g k := by
      rw [Finset.univ_eq_attach F, Finset.sum_attach]

/-- The finite sum of squared actual convolution outputs has the same
`L²` integral as the finite multiplier square function. -/
theorem initialSquare_finite_convolution_energy_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β) (F : Finset ℤ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x, ∑ k ∈ F,
      ‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2
        ∂(volume : Measure ℝ)) ≤
      ((2 * Real.pi + 2 * |D|) *
        Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
          1 / (1 - Real.rpow b (-2 * β))) * ‖G‖) ^ 2 := by
  classical
  let M : {k : ℤ // k ∈ F} → Lp ℂ ∞ (volume : Measure ℝ) :=
    initialSquareNuFiniteScaleMultipliers hSupp hσ b F
  have hbound := initialSquare_finite_scale_square_bound
    hSupp hσ hb hβ F G
  have hA : 0 ≤ (2 * Real.pi + 2 * |D|) *
      Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
        1 / (1 - Real.rpow b (-2 * β))) := by positivity
  have hsquareBound :
      ‖finiteFourierMultiplierSquareFunctionLp M G‖ ^ 2 ≤
        ((2 * Real.pi + 2 * |D|) *
          Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
            1 / (1 - Real.rpow b (-2 * β))) * ‖G‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hA (norm_nonneg _))).2 hbound
  have hconvAE (k : {k : ℤ // k ∈ F}) :
      (initialSquareNuConvolution hSupp hσ b k.1 G : ℝ → ℂ) =ᵐ[volume]
        (realFourierMultiplier (M k) G : ℝ → ℂ) := by
    have heq := initialSquareNuConvolution_eq_fourierMultiplier
      (b := b) hSupp hσ k.1 G
    change (initialSquareNuConvolution hSupp hσ b k.1 G :
      Lp ℂ 2 (volume : Measure ℝ)) =
      realFourierMultiplier (M k) G at heq
    exact Lp.ext_iff.mp heq
  have hconvAll : ∀ᵐ x ∂(volume : Measure ℝ),
      ∀ k : {k : ℤ // k ∈ F},
        initialSquareNuConvolution hSupp hσ b k.1 G x =
          realFourierMultiplier (M k) G x := by
    rw [ae_all_iff]
    exact hconvAE
  have hcoea := coeFn_finiteFourierMultiplierSquareFunctionLp M G
  have hsumAE : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖finiteFourierMultiplierSquareFunctionLp M G x‖ ^ 2 =
        ∑ k ∈ F,
          ‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2 := by
    filter_upwards [hcoea, hconvAll] with x hx hconv
    rw [hx]
    simp only [finiteFourierMultiplierSquareFunction]
    have hnonneg : 0 ≤ ∑ k : {k : ℤ // k ∈ F},
        ‖(realFourierMultiplier (M k) G : ℝ → ℂ) x‖ ^ 2 :=
      Finset.sum_nonneg fun k hk => sq_nonneg _
    have hpoint :
        (Real.sqrt (∑ k : {k : ℤ // k ∈ F},
          ‖(realFourierMultiplier (M k) G : ℝ → ℂ) x‖ ^ 2)) ^ 2 =
          ∑ k : {k : ℤ // k ∈ F},
            ‖(realFourierMultiplier (M k) G : ℝ → ℂ) x‖ ^ 2 :=
      Real.sq_sqrt hnonneg
    simp only [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [hpoint]
    exact initialSquare_sum_subtype_eq_nested
      (fun k => ‖(realFourierMultiplier (M k) G : ℝ → ℂ) x‖ ^ 2)
      (fun k => ‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2)
      (fun k => by rw [hconv k])
  calc
    (∫ x, ∑ k ∈ F,
        ‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2
          ∂(volume : Measure ℝ)) =
        ∫ x, ‖finiteFourierMultiplierSquareFunctionLp M G x‖ ^ 2
          ∂(volume : Measure ℝ) := by
            apply integral_congr_ae
            filter_upwards [hsumAE] with x hx
            exact hx.symm
    _ = ‖finiteFourierMultiplierSquareFunctionLp M G‖ ^ 2 :=
          (initialSquare_lp_two_norm_sq_eq_integral_norm_sq _).symm
    _ ≤ ((2 * Real.pi + 2 * |D|) *
          Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
            1 / (1 - Real.rpow b (-2 * β))) * ‖G‖) ^ 2 := hsquareBound

/-- The full geometric-scale square energy, expressed as an `ENNReal`
countable sum so that monotone convergence applies without a pointwise
summability assumption. -/
def initialSquareInfiniteConvolutionEnergy
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (b : ℝ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℤ, ENNReal.ofReal
    (‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2)

/-- The pointwise square function of all geometric-scale cancellation
convolutions. The `toReal` convention only affects the null set where the
energy is infinite. -/
def initialSquareConvolutionSquareFunction
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {β D : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (b : ℝ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ :=
  Real.sqrt (initialSquareInfiniteConvolutionEnergy hSupp hσ b G x).toReal

/-- Monotone convergence from the finite frequency-energy estimates gives
the exact full-scale `L²` energy bound. -/
theorem initialSquare_infinite_convolution_energy_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ x, initialSquareInfiniteConvolutionEnergy hSupp hσ b G x
      ∂(volume : Measure ℝ)) ≤
      ENNReal.ofReal (((2 * Real.pi + 2 * |D|) *
        Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
          1 / (1 - Real.rpow b (-2 * β))) * ‖G‖) ^ 2) := by
  classical
  let f : ℤ → ℝ → ℝ := fun k x =>
    ‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2
  let Fenn : ℤ → ℝ → ℝ≥0∞ := fun k x => ENNReal.ofReal (f k x)
  have hmeas : ∀ k, AEMeasurable (Fenn k) (volume : Measure ℝ) := by
    intro k
    have hnorm : AEStronglyMeasurable
        (fun x : ℝ => ‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2)
        (volume : Measure ℝ) :=
      (Lp.memLp (initialSquareNuConvolution hSupp hσ b k G)).aestronglyMeasurable.norm.pow 2
    exact hnorm.aemeasurable.ennreal_ofReal
  have hfiniteConvert (F : Finset ℤ) :
      ENNReal.ofReal (∫ x, ∑ k ∈ F, f k x ∂(volume : Measure ℝ)) =
        ∫⁻ x, ∑ k ∈ F, Fenn k x ∂(volume : Measure ℝ) := by
    have hInt : ∀ k ∈ F, Integrable (f k) (volume : Measure ℝ) := by
      intro k hk
      exact (Lp.memLp (initialSquareNuConvolution hSupp hσ b k G)).integrable_norm_pow
        (by norm_num)
    have hsumInt : Integrable (fun x => ∑ k ∈ F, f k x)
        (volume : Measure ℝ) := integrable_finset_sum F hInt
    have hsumNonneg : 0 ≤ᵐ[(volume : Measure ℝ)] fun x => ∑ k ∈ F, f k x := by
      filter_upwards [] with x
      exact Finset.sum_nonneg fun k hk => sq_nonneg _
    calc
      _ = ∫⁻ x, ENNReal.ofReal (∑ k ∈ F, f k x) ∂(volume : Measure ℝ) :=
        ofReal_integral_eq_lintegral_ofReal hsumInt hsumNonneg
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [] with x
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro k hk
        exact sq_nonneg _
  have hfiniteBound (F : Finset ℤ) :
      (∑ k ∈ F, ∫⁻ x, Fenn k x ∂(volume : Measure ℝ)) ≤
        ENNReal.ofReal (((2 * Real.pi + 2 * |D|) *
          Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
            1 / (1 - Real.rpow b (-2 * β))) * ‖G‖) ^ 2) := by
    rw [← lintegral_finsetSum' F (fun k hk => hmeas k)]
    rw [← hfiniteConvert F]
    apply ENNReal.ofReal_le_ofReal
    exact initialSquare_finite_convolution_energy_bound
      hSupp hσ hb hβ F G
  change (∫⁻ x, ∑' k : ℤ, Fenn k x ∂(volume : Measure ℝ)) ≤ _
  rw [lintegral_tsum hmeas]
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  exact hfiniteBound F

/-- The exact full-scale `L²` square-function estimate in
`lj:initial-square`. -/
theorem initialSquare_square_function_L2_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (initialSquareConvolutionSquareFunction hSupp hσ b G)
      (ENNReal.ofReal 2) (volume : Measure ℝ) ≤
        ENNReal.ofReal ((2 * Real.pi + 2 * |D|) *
          Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
            1 / (1 - Real.rpow b (-2 * β))) * ‖G‖) := by
  let E := initialSquareInfiniteConvolutionEnergy hSupp hσ b G
  let S := initialSquareConvolutionSquareFunction hSupp hσ b G
  have htermMeas (k : ℤ) : Measurable (fun x : ℝ =>
      ENNReal.ofReal (‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2)) := by
    have hconv : Measurable
        (fun x : ℝ => initialSquareNuConvolution hSupp hσ b k G x) :=
      (Lp.stronglyMeasurable
        (initialSquareNuConvolution hSupp hσ b k G)).measurable
    exact ENNReal.continuous_ofReal.measurable.comp (hconv.norm.pow_const 2)
  have hEmeas : Measurable E := by
    dsimp [E, initialSquareInfiniteConvolutionEnergy]
    exact Measurable.ennreal_tsum htermMeas
  have hSmeas : Measurable S := by
    dsimp [S, initialSquareConvolutionSquareFunction]
    exact Real.continuous_sqrt.measurable.comp
      (ENNReal.measurable_toReal.comp hEmeas)
  have hSnonneg (x : ℝ) : 0 ≤ S x := by
    dsimp [S, initialSquareConvolutionSquareFunction]
    exact Real.sqrt_nonneg _
  have hSsq (x : ℝ) : S x ^ 2 = (E x).toReal := by
    dsimp [S, initialSquareConvolutionSquareFunction]
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hpoint (x : ℝ) : ENNReal.ofReal (S x ^ 2) ≤ E x := by
    rw [hSsq]
    exact ENNReal.ofReal_toReal_le
  have hmomentBound :
      (∫⁻ x, ENNReal.ofReal (S x ^ 2) ∂(volume : Measure ℝ)) ≤
        ENNReal.ofReal (((2 * Real.pi + 2 * |D|) *
          Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
            1 / (1 - Real.rpow b (-2 * β))) * ‖G‖) ^ 2) := by
    calc
      _ ≤ ∫⁻ x, E x ∂(volume : Measure ℝ) := lintegral_mono hpoint
      _ ≤ _ := initialSquare_infinite_convolution_energy_bound
        hSupp hσ hb hβ G
  have hmoment :
      (∫⁻ x, ENNReal.ofReal (S x ^ 2) ∂(volume : Measure ℝ)) =
        eLpNorm S (ENNReal.ofReal 2) (volume : Measure ℝ) ^ 2 := by
    have htwo : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by norm_num
    have htwoNe : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
    have htwoTop : ENNReal.ofReal (2 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
    calc
      _ = ∫⁻ x, ‖S x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
        apply lintegral_congr_ae
        filter_upwards with x
        rw [ENNReal.ofReal_pow (hSnonneg x) 2]
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hSnonneg x)]
        exact (ENNReal.rpow_natCast (ENNReal.ofReal (S x)) 2).symm
      _ = _ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal htwoNe htwoTop
          hSmeas.aestronglyMeasurable, htwo]
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  have hmoment' := hmoment.symm ▸ hmomentBound
  have hA : 0 ≤ (2 * Real.pi + 2 * |D|) *
      Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
        1 / (1 - Real.rpow b (-2 * β))) * ‖G‖ := by positivity
  have hroot := ENNReal.rpow_le_rpow hmoment' (by norm_num : 0 ≤ (1 / 2 : ℝ))
  have hleft :
      (eLpNorm S (ENNReal.ofReal 2) (volume : Measure ℝ) ^ 2) ^ (1 / 2 : ℝ) =
        eLpNorm S (ENNReal.ofReal 2) (volume : Measure ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hright :
      ENNReal.ofReal (((2 * Real.pi + 2 * |D|) *
        Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
          1 / (1 - Real.rpow b (-2 * β))) * ‖G‖) ^ 2) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal ((2 * Real.pi + 2 * |D|) *
          Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
            1 / (1 - Real.rpow b (-2 * β))) * ‖G‖) := by
    rw [ENNReal.ofReal_pow hA 2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hleft, hright] at hroot
  exact hroot

private theorem initialSquareNuConvolution_le_squareFunction_ae
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β)
    (G : Lp ℂ 2 (volume : Measure ℝ)) (k : ℤ) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ‖initialSquareNuConvolution hSupp hσ b k G x‖ ≤
        initialSquareConvolutionSquareFunction hSupp hσ b G x := by
  let E := initialSquareInfiniteConvolutionEnergy hSupp hσ b G
  have htermMeas (j : ℤ) : Measurable (fun x : ℝ =>
      ENNReal.ofReal (‖initialSquareNuConvolution hSupp hσ b j G x‖ ^ 2)) := by
    have hconv : Measurable
        (fun x : ℝ => initialSquareNuConvolution hSupp hσ b j G x) :=
      (Lp.stronglyMeasurable
        (initialSquareNuConvolution hSupp hσ b j G)).measurable
    exact ENNReal.continuous_ofReal.measurable.comp (hconv.norm.pow_const 2)
  have hEmeas : Measurable E := by
    dsimp [E, initialSquareInfiniteConvolutionEnergy]
    exact Measurable.ennreal_tsum htermMeas
  have hEfinite : ∫⁻ x, E x ∂(volume : Measure ℝ) < ∞ := by
    exact (initialSquare_infinite_convolution_energy_bound
      hSupp hσ hb hβ G).trans_lt ENNReal.ofReal_lt_top
  have hEfiniteAE : ∀ᵐ x ∂(volume : Measure ℝ), E x < ∞ :=
    ae_lt_top hEmeas hEfinite.ne
  filter_upwards [hEfiniteAE] with x hx
  have hterm :
      ENNReal.ofReal (‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2) ≤ E x := by
    dsimp [E, initialSquareInfiniteConvolutionEnergy]
    exact ENNReal.le_tsum (f := fun j : ℤ =>
      ENNReal.ofReal (‖initialSquareNuConvolution hSupp hσ b j G x‖ ^ 2)) k
  have hreal : ‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2 ≤ (E x).toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hx.ne).mpr hterm
    simpa using h
  have hsq :
      ‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2 ≤
        (Real.sqrt (E x).toReal) ^ 2 := by
    simpa [Real.sq_sqrt (ENNReal.toReal_nonneg)] using hreal
  have hnorm := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 hsq
  simpa [initialSquareConvolutionSquareFunction, E,
    initialSquareInfiniteConvolutionEnergy] using hnorm

private theorem initialSquare_lineMaximal_lt_top_ae_of_memLp_two
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal 2) volume) :
    ∀ᵐ x ∂(volume : Measure ℝ), lineMaximal f x < ∞ := by
  let I : ℝ := ∫ x, ‖f x‖ ^ 2 ∂(volume : Measure ℝ)
  have hfTwo : MemLp f (2 : ℝ≥0∞) volume := by simpa using hf
  have hIint : Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume :=
    hfTwo.integrable_norm_pow (by norm_num)
  have hInonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun x => sq_nonneg _
  have hlevel {t : ℝ} (ht : 0 < t) :
      volume {x : ℝ | ENNReal.ofReal t < lineMaximal f x} ≤
        ENNReal.ofReal (12 * I / t ^ 2) := by
    let high : ℝ → ℂ := lineMaximalHighCutoff (t / 2) f
    have hhigh : Integrable high volume :=
      lineMaximalHighCutoff_integrable (f := f) (p := 2) (a := t / 2)
        (by norm_num) (by linarith) hf
    have hmajor : Integrable (fun x : ℝ => (2 / t) * ‖f x‖ ^ 2) volume :=
      hIint.const_mul (2 / t)
    have hpoint (x : ℝ) : ‖high x‖ ≤ (2 / t) * ‖f x‖ ^ 2 := by
      by_cases hx : t / 2 < ‖f x‖
      · have hfactor : 0 ≤ (2 / t) * ‖f x‖ ^ 2 - ‖f x‖ := by
          have hnonneg : 0 ≤ ‖f x‖ := norm_nonneg _
          have hprod : 0 ≤ ‖f x‖ * (2 * ‖f x‖ - t) :=
            mul_nonneg hnonneg (by linarith)
          have hmul : t * ‖f x‖ ≤ 2 * ‖f x‖ ^ 2 := by nlinarith
          have hmul' : ‖f x‖ * t ≤ 2 * ‖f x‖ ^ 2 := by
            simpa [mul_comm] using hmul
          have hdiv : ‖f x‖ ≤ (2 * ‖f x‖ ^ 2) / t :=
            (le_div_iff₀ ht).2 hmul'
          simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
        simpa [high, lineMaximalHighCutoff, hx] using hfactor
      · simpa [high, lineMaximalHighCutoff, hx] using
          (mul_nonneg (by positivity : 0 ≤ (2 / t : ℝ)) (sq_nonneg ‖f x‖))
    have hhighIntegral :
        (∫ x, ‖high x‖ ∂(volume : Measure ℝ)) ≤ (2 / t) * I := by
      calc
        _ ≤ ∫ x, (2 / t) * ‖f x‖ ^ 2 ∂(volume : Measure ℝ) :=
          integral_mono_ae hhigh.norm hmajor (ae_of_all volume hpoint)
        _ = (2 / t) * I := by
          rw [integral_const_mul]
    have hweak := lineMaximal_weakLp_distribution_bound
      (f := f) (p := 2) (t := t) (by norm_num) ht hf
    calc
      _ ≤ ENNReal.ofReal
          (3 * (∫ x, ‖high x‖ ∂(volume : Measure ℝ)) / (t / 2)) := by
        simpa [high] using hweak
      _ ≤ ENNReal.ofReal (12 * I / t ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hreal :
            3 * (∫ x, ‖high x‖ ∂(volume : Measure ℝ)) / (t / 2) ≤
              12 * I / t ^ 2 := by
          calc
            _ ≤ 3 * ((2 / t) * I) / (t / 2) := by
              apply (div_le_div_iff₀ (by positivity) (by positivity)).2
              have hnum :
                  3 * (∫ x, ‖high x‖ ∂(volume : Measure ℝ)) ≤
                    3 * ((2 / t) * I) :=
                mul_le_mul_of_nonneg_left hhighIntegral (by norm_num)
              exact mul_le_mul_of_nonneg_right hnum (by positivity)
            _ = 12 * I / t ^ 2 := by
              field_simp [ht.ne']
              ring
        exact hreal
  let bad : Set ℝ := {x | lineMaximal f x = ∞}
  have hmeasureBound (n : ℕ) :
      volume bad ≤ ENNReal.ofReal
        (12 * I * (((n : ℝ) + 1)⁻¹) ^ 2) := by
    have ht : 0 < (n : ℝ) + 1 := by positivity
    have hsubset : bad ⊆ {x : ℝ | ENNReal.ofReal ((n : ℝ) + 1) < lineMaximal f x} := by
      intro x hx
      change lineMaximal f x = ∞ at hx
      change ENNReal.ofReal ((n : ℝ) + 1) < lineMaximal f x
      rw [hx]
      exact ENNReal.ofReal_lt_top
    calc
      _ ≤ volume {x : ℝ | ENNReal.ofReal ((n : ℝ) + 1) < lineMaximal f x} :=
        measure_mono hsubset
      _ ≤ ENNReal.ofReal (12 * I / ((n : ℝ) + 1) ^ 2) := hlevel ht
      _ = _ := by congr 1 <;> field_simp [ht.ne'] <;> ring
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have hdecay : Tendsto
      (fun n : ℕ => ENNReal.ofReal (12 * I * (((n : ℝ) + 1)⁻¹) ^ 2))
      atTop (𝓝 0) := by
    have hreal : Tendsto
        (fun n : ℕ => 12 * I * (((n : ℝ) + 1)⁻¹) ^ 2)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul (hinv.pow 2))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hbad : volume bad = 0 := by
    have hle := le_of_tendsto_of_tendsto' tendsto_const_nhds hdecay hmeasureBound
    exact le_antisymm (by simpa [bad] using hle) bot_le
  rw [ae_iff]
  simpa [bad, ENNReal.not_lt_top] using hbad

/-- The geometric-scale maximal convolution by the positive probability
measure, represented through its complex vector-measure convolution. When
`G` is the complexification of a nonnegative input, this is the maximal
average `sup_k σ_{b^k} * G` from `lj:initial-square`. -/
def initialSquareSigmaConvolutionMaximal
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ≥0∞ :=
  ⨆ k : ℤ, ENNReal.ofReal ‖complexMeasureConvolution
    (initialSquareDilateComplexMeasure
      (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
    (fun y : ℝ => G y) (Lp.aestronglyMeasurable G) x‖

/-- The `L²` representative of the pointwise modulus, complexified so it can
be used by `initialSquareSigmaConvolutionMaximal`. -/
def initialSquareAbsL2Representative (F : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (((Lp.memLp F).norm).ofReal).toLp (fun x : ℝ => (‖F x‖ : ℂ))

private theorem initialSquareAbsL2Representative_ae
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun x : ℝ => initialSquareAbsL2Representative F x) =ᵐ[volume]
      (fun x => (‖F x‖ : ℂ)) := by
  simpa [initialSquareAbsL2Representative] using
    (MemLp.coeFn_toLp (((Lp.memLp F).norm).ofReal))

/-- Public interface to the checked almost-everywhere modulus representative. -/
theorem initialSquareAbsL2Representative_ae_bridge
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun x : ℝ => initialSquareAbsL2Representative F x) =ᵐ[volume]
      (fun x => (‖F x‖ : ℂ)) :=
  initialSquareAbsL2Representative_ae F

#print axioms initialSquareAbsL2Representative_ae_bridge

/-- The source positive convolution maximal function, written at the base
measure after the change of variables defining `σ_{b^k}`. -/
def initialSquareSigmaPositiveConvolutionMaximal
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (F : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ≥0∞ :=
  ⨆ k : ℤ, ENNReal.ofReal
    (∫ y, ‖F (x - y)‖ ∂(Measure.map (fun y : ℝ => b ^ k * y) σ))

private theorem initialSquare_sigma_positive_dilation_change_variables
    (σ : Measure ℝ) (t : ℝ) (F : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) :
    ∫ y, ‖F (x - y)‖ ∂(Measure.map (fun y : ℝ => t * y) σ) =
      ∫ y, ‖F (x - t * y)‖ ∂σ := by
  exact integral_map_of_stronglyMeasurable (by fun_prop)
    (((Lp.stronglyMeasurable F).comp_measurable (by fun_prop)).norm)

private theorem initialSquare_sigma_positive_convolution_scale_ae
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (hb : 1 < b) (F : Lp ℂ 2 (volume : Measure ℝ)) (k : ℤ) :
    (fun x : ℝ => complexMeasureConvolution
      (initialSquareDilateComplexMeasure
        (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
      (fun y : ℝ => initialSquareAbsL2Representative F y)
      (Lp.aestronglyMeasurable (initialSquareAbsL2Representative F)) x) =ᵐ[volume]
    (fun x : ℝ =>
      ((∫ y, ‖F (x - b ^ k * y)‖ ∂σ : ℝ) : ℂ)) := by
  let μ₀ : ComplexMeasure ℝ := σ.toSignedMeasure.toComplexMeasure 0
  let t : ℝ := b ^ k
  have ht : t ≠ 0 := by
    dsimp [t]
    positivity
  have hbaseVar : IsFiniteMeasure μ₀.variation := by
    dsimp [μ₀]
    rw [initialSquareNuComplexMeasure_variation_eq (σ.toSignedMeasure),
      Measure.variation_toSignedMeasure]
    infer_instance
  letI : IsFiniteMeasure μ₀.variation := hbaseVar
  let μ : ComplexMeasure ℝ := initialSquareDilateComplexMeasure μ₀ t
  have hμvar : IsFiniteMeasure μ.variation := by
    change IsFiniteMeasure (μ₀.map (fun x : ℝ => t * x)).variation
    infer_instance
  letI : IsFiniteMeasure μ.variation := hμvar
  have hrep := initialSquareAbsL2Representative_ae F
  have hraw := complexMeasureConvolution_ae_eq_raw_integral μ
    (initialSquareAbsL2Representative F)
  have hcongr := rawComplexMeasureConvolution_ae_congr μ
    (fun y : ℝ => initialSquareAbsL2Representative F y)
    (fun y : ℝ => (‖F y‖ : ℂ))
    (Lp.stronglyMeasurable (initialSquareAbsL2Representative F))
    (Complex.continuous_ofReal.comp_stronglyMeasurable
      ((Lp.stronglyMeasurable F).norm)) hrep
  have hmap (x : ℝ) :
      ∫ᵛ y, (‖F (x - y)‖ : ℂ) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ᵛ y, (‖F (x - t * y)‖ : ℂ) ∂[ContinuousLinearMap.mul ℝ ℂ; μ₀] := by
    change ∫ᵛ y, (‖F (x - y)‖ : ℂ)
        ∂[ContinuousLinearMap.mul ℝ ℂ; μ₀.map (fun y : ℝ => t * y)] = _
    rw [(measurableEmbedding_mulLeft₀ ht).integral_map_vectorMeasure]
  have hreal (x : ℝ) :
      ∫ᵛ y, (‖F (x - t * y)‖ : ℂ)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ₀] =
        ((∫ y, ‖F (x - t * y)‖ ∂σ : ℝ) : ℂ) := by
    calc
      _ = ∫ᵛ y, (‖F (x - t * y)‖ : ℂ)
          ∂<•(σ.toSignedMeasure) :=
        initialSquareNuComplexMeasure_integral_eq (σ.toSignedMeasure) _
      _ = ∫ y, (‖F (x - t * y)‖ : ℂ) ∂σ := by
        rw [VectorMeasure.integral_toSignedMeasure]
      _ = ((∫ y, ‖F (x - t * y)‖ ∂σ : ℝ) : ℂ) := by
        rw [integral_complex_ofReal]
  filter_upwards [hraw, hcongr] with x hxraw hxcongr
  calc
    complexMeasureConvolution μ
        (fun y : ℝ => initialSquareAbsL2Representative F y)
        (Lp.aestronglyMeasurable (initialSquareAbsL2Representative F)) x
      = ∫ᵛ y, initialSquareAbsL2Representative F (x-y)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hxraw
    _ = ∫ᵛ y, (‖F (x-y)‖ : ℂ) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
      exact hxcongr
    _ = ∫ᵛ y, (‖F (x-t*y)‖ : ℂ)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ₀] := hmap x
    _ = ((∫ y, ‖F (x-t*y)‖ ∂σ : ℝ) : ℂ) := hreal x

/-- Public interface to the checked scale-level representative bridge used by
finite-exponent density extensions. -/
theorem initialSquare_sigma_positive_convolution_scale_ae_bridge
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (hb : 1 < b) (F : Lp ℂ 2 (volume : Measure ℝ)) (k : ℤ) :
    (fun x : ℝ => complexMeasureConvolution
      (initialSquareDilateComplexMeasure
        (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
      (fun y : ℝ => initialSquareAbsL2Representative F y)
      (Lp.aestronglyMeasurable (initialSquareAbsL2Representative F)) x) =ᵐ[volume]
    (fun x : ℝ => ((∫ y, ‖F (x - b ^ k * y)‖ ∂σ : ℝ) : ℂ)) :=
  initialSquare_sigma_positive_convolution_scale_ae hb F k

#print axioms initialSquare_sigma_positive_convolution_scale_ae_bridge

/-- For arbitrary `L²` input, the positive maximal average of its modulus is
almost everywhere the checked represented complex-measure maximal operator.
The formula is the source convolution `σ_{b^k} * |F|`, with the pushed
forward dilation expanded by change of variables. -/
theorem initialSquare_sigma_positive_convolution_maximal_ae
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (hb : 1 < b) (F : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun x : ℝ => initialSquareSigmaPositiveConvolutionMaximal σ b F x) =ᵐ[volume]
      (fun x : ℝ => initialSquareSigmaConvolutionMaximal σ b
        (initialSquareAbsL2Representative F) x) := by
  have hterms : ∀ᵐ x ∂volume, ∀ k : ℤ,
      ENNReal.ofReal
          (∫ y, ‖F (x - y)‖
            ∂(Measure.map (fun y : ℝ => b ^ k * y) σ)) =
        ENNReal.ofReal ‖complexMeasureConvolution
          (initialSquareDilateComplexMeasure
            (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
          (fun y : ℝ => initialSquareAbsL2Representative F y)
          (Lp.aestronglyMeasurable (initialSquareAbsL2Representative F)) x‖ := by
    rw [ae_all_iff]
    intro k
    have hscale := initialSquare_sigma_positive_convolution_scale_ae
      (σ := σ) (b := b) hb F k
    filter_upwards [hscale] with x hx
    have hsource := initialSquare_sigma_positive_dilation_change_variables
      σ (b ^ k) F x
    rw [hsource]
    have hnonneg : 0 ≤ ∫ y, ‖F (x - b ^ k * y)‖ ∂σ :=
      integral_nonneg_of_ae (ae_of_all _ fun y => norm_nonneg _)
    rw [hx]
    simp [Complex.norm_real, abs_of_nonneg hnonneg]
  change ∀ᵐ x ∂volume,
      (⨆ k : ℤ, ENNReal.ofReal
        (∫ y, ‖F (x - y)‖
          ∂(Measure.map (fun y : ℝ => b ^ k * y) σ))) =
        (⨆ k : ℤ, ENNReal.ofReal ‖complexMeasureConvolution
          (initialSquareDilateComplexMeasure
            (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
          (fun y : ℝ => initialSquareAbsL2Representative F y)
          (Lp.aestronglyMeasurable (initialSquareAbsL2Representative F)) x‖)
  filter_upwards [hterms] with x hx
  exact iSup_congr hx

/-- The real-valued representative of the source positive maximal function. -/
def initialSquareSigmaPositiveConvolutionMaximalReal
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (F : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ :=
  (initialSquareSigmaPositiveConvolutionMaximal σ b F x).toReal

/-- The `σ` maximal convolution is pointwise dominated almost everywhere by
the cancellation square function plus the centered maximal function for the
smooth part, with the exact `4 * ‖φ‖∞` factor. -/
theorem initialSquare_sigma_convolution_maximal_pointwise
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      initialSquareSigmaConvolutionMaximal σ b G x ≤
        ENNReal.ofReal (initialSquareConvolutionSquareFunction hSupp hσ b G x) +
          ENNReal.ofReal (4 * lpNorm φ ∞ volume) *
            lineMaximal (fun y : ℝ => G y) x := by
  have hsplitAll : ∀ᵐ x ∂(volume : Measure ℝ), ∀ k : ℤ,
      complexMeasureConvolution
          (initialSquareDilateComplexMeasure
            (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
          (fun y : ℝ => G y) (Lp.aestronglyMeasurable G) x =
        (initialSquareNuConvolution hSupp hσ b k G : ℝ → ℂ) x +
          complexMeasureConvolution
            (initialSquareDilateComplexMeasure
              (initialSquarePsiComplexMeasure σ) (b ^ k))
            (fun y : ℝ => G y) (Lp.aestronglyMeasurable G) x := by
    apply ae_all_iff.mpr
    intro k
    have hk := initialSquareSigmaConvolution_ae_eq_nu_add_psi
      (b := b) hSupp hσ k G
    filter_upwards [hk] with x hx
    simpa [initialSquareSigmaComplexMeasure] using hx
  have hnuAll : ∀ᵐ x ∂(volume : Measure ℝ), ∀ k : ℤ,
      ‖initialSquareNuConvolution hSupp hσ b k G x‖ ≤
        initialSquareConvolutionSquareFunction hSupp hσ b G x := by
    rw [ae_all_iff]
    intro k
    exact initialSquareNuConvolution_le_squareFunction_ae
      hSupp hσ hb hβ G k
  filter_upwards [hsplitAll, hnuAll] with x hsplit hnu
  apply iSup_le
  intro k
  change ENNReal.ofReal ‖complexMeasureConvolution
      (initialSquareDilateComplexMeasure
        (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
      (fun y : ℝ => G y) (Lp.aestronglyMeasurable G) x‖ ≤ _
  have htk : 0 < b ^ k := by positivity
  have hpsi := initialSquarePsiConvolution_maximal_bound hSupp
    (fun y : ℝ => G y) (Lp.memLp G) (b ^ k) htk x
  have hnorm :
      ‖complexMeasureConvolution
          (initialSquareDilateComplexMeasure
            (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
          (fun y : ℝ => G y) (Lp.aestronglyMeasurable G) x‖ ≤
        ‖initialSquareNuConvolution hSupp hσ b k G x‖ +
          ‖complexMeasureConvolution
            (initialSquareDilateComplexMeasure
              (initialSquarePsiComplexMeasure σ) (b ^ k))
            (fun y : ℝ => G y) (Lp.aestronglyMeasurable G) x‖ := by
    rw [hsplit k]
    exact norm_add_le _ _
  calc
    _ ≤ ENNReal.ofReal
        (‖initialSquareNuConvolution hSupp hσ b k G x‖ +
          ‖complexMeasureConvolution
            (initialSquareDilateComplexMeasure
              (initialSquarePsiComplexMeasure σ) (b ^ k))
            (fun y : ℝ => G y) (Lp.aestronglyMeasurable G) x‖) :=
      ENNReal.ofReal_le_ofReal hnorm
    _ = ENNReal.ofReal ‖initialSquareNuConvolution hSupp hσ b k G x‖ +
        ENNReal.ofReal ‖complexMeasureConvolution
            (initialSquareDilateComplexMeasure
              (initialSquarePsiComplexMeasure σ) (b ^ k))
            (fun y : ℝ => G y) (Lp.aestronglyMeasurable G) x‖ :=
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ ENNReal.ofReal
          (initialSquareConvolutionSquareFunction hSupp hσ b G x) +
        ENNReal.ofReal (4 * lpNorm φ ∞ volume) *
          lineMaximal (fun y : ℝ => G y) x := by
      exact add_le_add (ENNReal.ofReal_le_ofReal (hnu k)) hpsi

/-- The real-valued representative of the extended σ maximal convolution. -/
def initialSquareSigmaConvolutionMaximalReal
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ :=
  (initialSquareSigmaConvolutionMaximal σ b G x).toReal

private theorem initialSquareSigmaConvolutionMaximal_measurable
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    Measurable (initialSquareSigmaConvolutionMaximal σ b G) := by
  apply Measurable.iSup
  intro k
  let μ : ComplexMeasure ℝ :=
    initialSquareDilateComplexMeasure
      (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k)
  have hbaseVar : IsFiniteMeasure
      (σ.toSignedMeasure.toComplexMeasure 0).variation := by
    rw [initialSquareNuComplexMeasure_variation_eq (σ.toSignedMeasure),
      Measure.variation_toSignedMeasure]
    infer_instance
  letI : IsFiniteMeasure (σ.toSignedMeasure.toComplexMeasure 0).variation := hbaseVar
  have hμvar : IsFiniteMeasure μ.variation := by
    change IsFiniteMeasure
      ((σ.toSignedMeasure.toComplexMeasure 0).map
        (fun x : ℝ => b ^ k * x)).variation
    infer_instance
  letI : IsFiniteMeasure μ.variation := hμvar
  have hconv := stronglyMeasurable_complexMeasureConvolution μ
    (fun y : ℝ => G y) (Lp.aestronglyMeasurable G)
  change Measurable (fun x : ℝ => ENNReal.ofReal ‖
    complexMeasureConvolution μ (fun y : ℝ => G y)
      (Lp.aestronglyMeasurable G) x‖)
  exact ENNReal.continuous_ofReal.measurable.comp hconv.measurable.norm

private theorem initialSquare_sigma_convolution_maximalReal_le_ae
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      initialSquareSigmaConvolutionMaximalReal σ b G x ≤
        initialSquareConvolutionSquareFunction hSupp hσ b G x +
          (4 * lpNorm φ ∞ volume) * lineMaximalReal (fun y : ℝ => G y) x := by
  have hpoint := initialSquare_sigma_convolution_maximal_pointwise
    hSupp hσ hb hβ G
  have hlineFinite : ∀ᵐ x ∂(volume : Measure ℝ),
      lineMaximal (fun y : ℝ => G y) x < ∞ := by
    have hG : MemLp (fun y : ℝ => G y) (ENNReal.ofReal 2) volume := by
      simpa using Lp.memLp G
    exact initialSquare_lineMaximal_lt_top_ae_of_memLp_two hG
  have hc : 0 ≤ 4 * lpNorm φ ∞ volume := by
    exact mul_nonneg (by norm_num) lpNorm_nonneg
  filter_upwards [hpoint, hlineFinite] with x hpoint hlineFinite
  let S := initialSquareConvolutionSquareFunction hSupp hσ b G x
  let L := lineMaximal (fun y : ℝ => G y) x
  let c := 4 * lpNorm φ ∞ volume
  have hSnonneg : 0 ≤ S := by
    dsimp [S, initialSquareConvolutionSquareFunction]
    exact Real.sqrt_nonneg _
  have hSfin : ENNReal.ofReal S < ∞ := ENNReal.ofReal_lt_top
  have hprodFin : ENNReal.ofReal c * L < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlineFinite
  have hRhsFin : ENNReal.ofReal S + ENNReal.ofReal c * L < ∞ :=
    ENNReal.add_lt_top.mpr ⟨hSfin, hprodFin⟩
  have hMfin : initialSquareSigmaConvolutionMaximal σ b G x < ∞ :=
    lt_of_le_of_lt hpoint hRhsFin
  have hreal :=
    (ENNReal.toReal_le_toReal hMfin.ne hRhsFin.ne).mpr hpoint
  have hRhsEq :
      (ENNReal.ofReal S + ENNReal.ofReal c * L).toReal =
        S + c * lineMaximalReal (fun y : ℝ => G y) x := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hprodFin.ne,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hSnonneg,
      ENNReal.toReal_ofReal hc]
    dsimp [L, lineMaximalReal]
  rw [hRhsEq] at hreal
  simpa [initialSquareSigmaConvolutionMaximalReal, S, c] using hreal

/-- The exact `B₂ = Aν + 4 ‖φ‖∞ H₂` bound for the real-valued
maximal convolution representative. -/
theorem initialSquare_sigma_convolution_maximal_L2_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (initialSquareSigmaConvolutionMaximalReal σ b G)
        (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal
          ((2 * Real.pi + 2 * |D|) *
              Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
                1 / (1 - Real.rpow b (-2 * β))) +
            (4 * lpNorm φ ∞ volume) *
              (6 * (2 : ℝ) * (2 : ℝ) ^ ((2 : ℝ) - 1) /
                ((2 : ℝ) - 1)) ^ (1 / (2 : ℝ))) *
        eLpNorm (fun y : ℝ => G y) (ENNReal.ofReal 2) volume := by
  let S := initialSquareConvolutionSquareFunction hSupp hσ b G
  let L := lineMaximalReal (fun y : ℝ => G y)
  let M := initialSquareSigmaConvolutionMaximalReal σ b G
  let p : ℝ≥0∞ := ENNReal.ofReal 2
  let A : ℝ := (2 * Real.pi + 2 * |D|) *
    Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
      1 / (1 - Real.rpow b (-2 * β)))
  let c : ℝ := 4 * lpNorm φ ∞ volume
  let H2 : ℝ :=
    (6 * (2 : ℝ) * (2 : ℝ) ^ ((2 : ℝ) - 1) /
      ((2 : ℝ) - 1)) ^ (1 / (2 : ℝ))
  have hG : MemLp (fun y : ℝ => G y) p volume := by
    simpa [p] using Lp.memLp G
  have hGnorm : eLpNorm (fun y : ℝ => G y) p volume =
      ENNReal.ofReal ‖G‖ := by
    change eLpNorm G (ENNReal.ofReal 2) volume = ENNReal.ofReal ‖G‖
    have hE : eLpNorm G 2 volume = ENNReal.ofReal ‖G‖ := by
      calc
        eLpNorm G 2 volume =
            ENNReal.ofReal (ENNReal.toReal (eLpNorm G 2 volume)) :=
          (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top G)).symm
        _ = ENNReal.ofReal ‖G‖ := by rw [Lp.norm_def]
    simpa using hE
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (by norm_num) lpNorm_nonneg
  have hH2 : 0 ≤ H2 := by
    dsimp [H2]
    positivity
  have hpoint := initialSquare_sigma_convolution_maximalReal_le_ae
    hSupp hσ hb hβ G
  have hMmeas : Measurable M := by
    dsimp [M, initialSquareSigmaConvolutionMaximalReal]
    exact ENNReal.measurable_toReal.comp
      (initialSquareSigmaConvolutionMaximal_measurable σ b G)
  let E := initialSquareInfiniteConvolutionEnergy hSupp hσ b G
  have htermMeas (k : ℤ) : Measurable (fun x : ℝ =>
      ENNReal.ofReal (‖initialSquareNuConvolution hSupp hσ b k G x‖ ^ 2)) := by
    have hconv : Measurable
        (fun x : ℝ => initialSquareNuConvolution hSupp hσ b k G x) :=
      (Lp.stronglyMeasurable
        (initialSquareNuConvolution hSupp hσ b k G)).measurable
    exact ENNReal.continuous_ofReal.measurable.comp (hconv.norm.pow_const 2)
  have hEmeas : Measurable E := by
    dsimp [E, initialSquareInfiniteConvolutionEnergy]
    exact Measurable.ennreal_tsum htermMeas
  have hSmeas : Measurable S := by
    dsimp [S, initialSquareConvolutionSquareFunction]
    exact Real.continuous_sqrt.measurable.comp
      (ENNReal.measurable_toReal.comp hEmeas)
  have hGloc : LocallyIntegrable (fun y : ℝ => G y) volume := by
    have hp1 : (1 : ℝ≥0∞) ≤ p := by
      dsimp [p]
      norm_num
    exact hG.locallyIntegrable hp1
  have hLmeas : Measurable L := by
    exact lineMaximalReal_measurable_of_locallyIntegrable hGloc
  have hRmeas : Measurable (fun x : ℝ => S x + c * L x) := by
    exact hSmeas.add (measurable_const.mul hLmeas)
  have hMnonneg (x : ℝ) : 0 ≤ M x := by
    dsimp [M, initialSquareSigmaConvolutionMaximalReal]
    exact ENNReal.toReal_nonneg
  have hSnonneg (x : ℝ) : 0 ≤ S x := by
    dsimp [S, initialSquareConvolutionSquareFunction]
    exact Real.sqrt_nonneg _
  have hLnonneg (x : ℝ) : 0 ≤ L x := by
    dsimp [L, lineMaximalReal]
    exact ENNReal.toReal_nonneg
  have hpointNorm : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖M x‖ ≤ S x + c * L x := by
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hMnonneg x)]
    simpa [M, S, L, c] using hx
  have hmono := eLpNorm_mono_ae_real (p := p)
    hMmeas.aestronglyMeasurable hpointNorm
  have hp1 : (1 : ℝ≥0∞) ≤ p := by
    dsimp [p]
    norm_num
  have hsum := eLpNorm_add_le (p := p) (μ := volume)
    (f := S) (g := fun x : ℝ => c * L x) hp1
  have hsq := initialSquare_square_function_L2_bound hSupp hσ hb hβ G
  have hsq' : eLpNorm S p volume ≤ ENNReal.ofReal A *
      eLpNorm (fun y : ℝ => G y) p volume := by
    calc
      eLpNorm S p volume = eLpNorm S (ENNReal.ofReal 2) volume := rfl
      _ ≤ ENNReal.ofReal (A * ‖G‖) := by simpa [S, A] using hsq
      _ = ENNReal.ofReal A * eLpNorm (fun y : ℝ => G y) p volume := by
        rw [ENNReal.ofReal_mul hA, ← hGnorm]
  have hline := lineMaximal_strongLp (f := fun y : ℝ => G y)
    (p := (2 : ℝ)) (by norm_num) hG
  have hline' : eLpNorm L p volume ≤ ENNReal.ofReal H2 *
      eLpNorm (fun y : ℝ => G y) p volume := by
    simpa [p, L, H2] using hline
  have hscaled : eLpNorm (fun x : ℝ => c * L x) p volume =
      ENNReal.ofReal c * eLpNorm L p volume := by
    calc
      eLpNorm (fun x : ℝ => c * L x) p volume = eLpNorm (c • L) p volume := rfl
      _ = ‖c‖ₑ * eLpNorm L p volume := eLpNorm_const_smul c L p volume
      _ = ENNReal.ofReal c * eLpNorm L p volume := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]
  have hupper : eLpNorm (fun x : ℝ => S x + c * L x) p volume ≤
      ENNReal.ofReal A * eLpNorm (fun y : ℝ => G y) p volume +
        ENNReal.ofReal c *
          (ENNReal.ofReal H2 * eLpNorm (fun y : ℝ => G y) p volume) := by
    calc
      _ ≤ eLpNorm S p volume +
          eLpNorm (fun x : ℝ => c * L x) p volume := hsum
      _ ≤ ENNReal.ofReal A * eLpNorm (fun y : ℝ => G y) p volume +
          ENNReal.ofReal c *
            (ENNReal.ofReal H2 * eLpNorm (fun y : ℝ => G y) p volume) := by
          rw [hscaled]
          exact add_le_add hsq' <| mul_le_mul_of_nonneg_left hline'
            (by positivity : 0 ≤ ENNReal.ofReal c)
  have hcoeff :
      ENNReal.ofReal A + ENNReal.ofReal c * ENNReal.ofReal H2 =
        ENNReal.ofReal (A + c * H2) := by
    calc
      _ = ENNReal.ofReal A + ENNReal.ofReal (c * H2) := by
        rw [← ENNReal.ofReal_mul hc]
      _ = ENNReal.ofReal (A + c * H2) :=
        (ENNReal.ofReal_add hA (mul_nonneg hc hH2)).symm
  have hfinish := hmono.trans hupper
  have hfinal : eLpNorm M p volume ≤
      ENNReal.ofReal (A + c * H2) *
        eLpNorm (fun y : ℝ => G y) p volume := by
    calc
      _ ≤ ENNReal.ofReal A * eLpNorm (fun y : ℝ => G y) p volume +
          ENNReal.ofReal c *
            (ENNReal.ofReal H2 * eLpNorm (fun y : ℝ => G y) p volume) := hfinish
      _ = (ENNReal.ofReal A + ENNReal.ofReal c * ENNReal.ofReal H2) *
          eLpNorm (fun y : ℝ => G y) p volume := by
        calc
          _ = ENNReal.ofReal A * eLpNorm (fun y : ℝ => G y) p volume +
              (ENNReal.ofReal c * ENNReal.ofReal H2) *
                eLpNorm (fun y : ℝ => G y) p volume := by rw [mul_assoc]
          _ = _ := by rw [← add_mul]
      _ = _ := by rw [hcoeff]
  simpa [p, A, c, H2] using hfinal

/-- Transfer the exact `B₂` estimate from represented complex-measure
convolution to the source positive maximal function for arbitrary `L²`
inputs. -/
theorem initialSquare_sigma_positive_convolution_maximal_L2_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D)
    (hb : 1 < b) (hβ : 0 < β)
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (initialSquareSigmaPositiveConvolutionMaximalReal σ b F)
        (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal
          ((2 * Real.pi + 2 * |D|) *
              Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
                1 / (1 - Real.rpow b (-2 * β))) +
            (4 * lpNorm φ ∞ volume) *
              (6 * (2 : ℝ) * (2 : ℝ) ^ ((2 : ℝ) - 1) /
                ((2 : ℝ) - 1)) ^ (1 / (2 : ℝ))) *
        eLpNorm (fun y : ℝ => F y) (ENNReal.ofReal 2) volume := by
  let G := initialSquareAbsL2Representative F
  have hbridge := initialSquare_sigma_positive_convolution_maximal_ae
    (σ := σ) (b := b) hb F
  have hreal :
      initialSquareSigmaPositiveConvolutionMaximalReal σ b F =ᵐ[volume]
        initialSquareSigmaConvolutionMaximalReal σ b G := by
    filter_upwards [hbridge] with x hx
    simpa [initialSquareSigmaPositiveConvolutionMaximalReal,
      initialSquareSigmaConvolutionMaximalReal, G] using
        congrArg ENNReal.toReal hx
  have hinput : eLpNorm (fun y : ℝ => G y) (ENNReal.ofReal 2) volume =
      eLpNorm (fun y : ℝ => F y) (ENNReal.ofReal 2) volume := by
    apply eLpNorm_congr_norm_ae
      (Lp.aestronglyMeasurable G) (Lp.aestronglyMeasurable F)
    filter_upwards [initialSquareAbsL2Representative_ae F] with y hy
    simp [G, hy]
  have hbound := initialSquare_sigma_convolution_maximal_L2_bound
    hSupp hσ hb hβ G
  calc
    eLpNorm (initialSquareSigmaPositiveConvolutionMaximalReal σ b F)
        (ENNReal.ofReal 2) volume =
      eLpNorm (initialSquareSigmaConvolutionMaximalReal σ b G)
        (ENNReal.ofReal 2) volume := eLpNorm_congr_ae hreal
    _ ≤ _ := hbound
    _ = _ := by rw [hinput]

private theorem initialSquare_support_map_neg
    {σ : Measure ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    (Measure.map Neg.neg σ).support ⊆ Set.Icc (-(1 : ℝ)) 1 := by
  intro x hx
  have hxopen : ∀ U, x ∈ U → IsOpen U →
      0 < (Measure.map Neg.neg σ) U := by
    rw [Measure.support_eq_forall_isOpen] at hx
    exact hx
  have hxpre : -x ∈ σ.support := by
    rw [Measure.support_eq_forall_isOpen]
    intro U hU hUopen
    have hpreopen : IsOpen (Neg.neg ⁻¹' U) := hUopen.preimage continuous_neg
    have hxpre : x ∈ Neg.neg ⁻¹' U := by simpa using hU
    have hpos := hxopen (Neg.neg ⁻¹' U) hxpre hpreopen
    rw [Measure.map_apply (by fun_prop) hpreopen.measurableSet] at hpos
    simpa using hpos
  have hbound := hSupp hxpre
  rcases Set.mem_Icc.mp hbound with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- The reflected positive maximal operator has the same exact `B₂` bound
as the original positive maximal operator. This is the missing reflected
endpoint in `lj:initial-square`. -/
theorem initialSquare_sigma_reflected_positive_convolution_maximal_L2_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β)
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm
        (initialSquareSigmaPositiveConvolutionMaximalReal
          (Measure.map Neg.neg σ) b F)
        (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal
          ((2 * Real.pi + 2 * |D|) *
              Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
                1 / (1 - Real.rpow b (-2 * β))) +
            (4 * lpNorm φ ∞ volume) *
              (6 * (2 : ℝ) * (2 : ℝ) ^ ((2 : ℝ) - 1) /
                ((2 : ℝ) - 1)) ^ (1 / (2 : ℝ))) *
        eLpNorm (fun y : ℝ => F y) (ENNReal.ofReal 2) volume := by
  let σref : Measure ℝ := Measure.map Neg.neg σ
  have hsplit := measureSplitting σ hSupp β hβ D hdecay
  have hσref : MeasureSplittingBounds σref β D := by
    simpa [σref] using hsplit.2
  have hSuppRef : σref.support ⊆ Set.Icc (-(1 : ℝ)) 1 := by
    exact initialSquare_support_map_neg hSupp
  haveI : IsProbabilityMeasure σref := inferInstance
  have hbound := initialSquare_sigma_positive_convolution_maximal_L2_bound
    hSuppRef hσref hb hβ F
  simpa [σref] using hbound

#print axioms initialSquare_sigma_convolution_maximal_L2_bound
#print axioms initialSquare_sigma_positive_convolution_maximal_ae
#print axioms initialSquare_sigma_positive_convolution_maximal_L2_bound
#print axioms initialSquare_sigma_reflected_positive_convolution_maximal_L2_bound

end

end FractionalPrimes.Literature.JSW

end
