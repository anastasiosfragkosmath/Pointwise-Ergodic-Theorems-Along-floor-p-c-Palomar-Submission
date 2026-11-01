module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownFreeFactorOuterSummation
import Mathlib.Tactic

/-! The source-coefficient short-interval input for the theta/log branch of
`lda:small-group`.  This module uses the bare periodic Mellin estimate and
inserts only the selected factor's literal theta and normalized-log weights;
the separate outer polynomial cutoff is not part of this factorwise source
coefficient. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

private theorem natResidue_iff_intResidue
    {n q b : ℕ} (hbq : b < q) :
    n % q = b ↔ (n : ℤ) % (q : ℤ) = (b : ℤ) % (q : ℤ) := by
  constructor
  · intro h
    rw [← Int.natCast_mod, ← Int.natCast_mod,
      Nat.mod_eq_of_lt hbq]
    exact_mod_cast h
  · intro h
    rw [← Int.natCast_mod, ← Int.natCast_mod] at h
    have h' : n % q = b % q := by exact_mod_cast h
    simpa [Nat.mod_eq_of_lt hbq] using h'

/- The finite factor coefficient phase weight. This is the same exact
residue/Mellin normalization used by the source bridge, defined locally so
this module stays importable from the current `module` graph. -/
noncomputable def smoothHeathBrownThetaLogResiduePhaseWeight
    (q b : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  if _hn : 0 < n then
    if n % q = b then
      (Real.sqrt (n : ℝ) : ℂ) *
        (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))
    else 0
  else 0

theorem smoothHeathBrownThetaLogResiduePhaseWeight_norm_le_one
    (q b : ℕ) (t : ℝ) (n : ℕ) :
    ‖smoothHeathBrownThetaLogResiduePhaseWeight q b t n‖ ≤ 1 := by
  by_cases hn0 : n = 0
  · subst n
    simp [smoothHeathBrownThetaLogResiduePhaseWeight]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hres : n % q = b
  · rw [smoothHeathBrownThetaLogResiduePhaseWeight, dif_pos hn, if_pos hres,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hscalar :
        ‖(n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))‖ =
          1 / Real.sqrt (n : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      have hre :
          ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)).re = -(1 / 2 : ℝ) := by
        simp
      rw [hre]
      have hsqrt :
          Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : 0 < (n : ℝ))]
        norm_num
      have hsqrtpos : 0 < Real.sqrt (n : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast hn)
      exact (eq_div_iff hsqrtpos.ne').2 (by nlinarith [hsqrt])
    rw [hscalar]
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hn)
    field_simp <;> norm_num
  · simp [smoothHeathBrownThetaLogResiduePhaseWeight, hn, hres]

/-- The source weight left after converting a factor coefficient to a bare
periodic Mellin sequence.  The logarithm is normalized by the exact
`4 * log X` scalar from `lda:small-group`. -/
noncomputable def smoothHeathBrownThetaLogSourceWeight
    {X : ℝ} (f : SmoothHeathBrownFactor X) (n : ℕ) : ℂ :=
  match f with
  | .theta _ => smoothSmallGroupThetaWeight
      (smoothHeathBrownFactorScale f) n
  | .logarithm _ => smoothSmallGroupThetaWeight
      (smoothHeathBrownFactorScale f) n *
        ((Real.log (n : ℝ) / (4 * Real.log X) : ℝ) : ℂ)
  | .mobius _ => 0

private theorem smoothHeathBrownWeightedFactorCoefficient_eq_residueMellin_mul_sourceWeight
    {X z : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (q b : ℕ) (hbq : b < q) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    smoothHeathBrownWeightedFactorCoefficient (z := z) f
    (smoothHeathBrownThetaLogResiduePhaseWeight q b t) n =
      smoothHeathBrownResidueMellinTerm q (b : ℤ) t n *
        smoothHeathBrownThetaLogSourceWeight f n := by
  unfold smoothHeathBrownWeightedFactorCoefficient
  rw [smoothHeathBrownThetaLogResiduePhaseWeight, dif_pos hn]
  cases f with
  | theta j =>
      by_cases hres : n % q = b
      · have hint := (natResidue_iff_intResidue hbq).mp hres
        simp only [if_pos hres]
        have hsqrt : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn)))
        simp [smoothHeathBrownResidueMellinTerm,
          smoothHeathBrownResidueIndicator,
          smoothHeathBrownThetaLogSourceWeight,
          smoothHeathBrownFactorScale,
          smoothHeathBrownNormalizedFactorCoefficient,
          smoothHeathBrownThetaFactor,
          smoothSmallGroupThetaWeight, hn.ne', hint]
        field_simp [hsqrt]
      · have hint : (n : ℤ) % (q : ℤ) ≠ (b : ℤ) % (q : ℤ) := by
          intro hh
          exact hres ((natResidue_iff_intResidue hbq).mpr hh)
        simp [smoothHeathBrownResidueMellinTerm,
          smoothHeathBrownResidueIndicator,
          smoothHeathBrownThetaLogSourceWeight,
          smoothHeathBrownFactorScale,
          smoothHeathBrownNormalizedFactorCoefficient,
          smoothHeathBrownThetaFactor,
          smoothSmallGroupThetaWeight, hn.ne', hres, hint]
  | logarithm j =>
      by_cases hres : n % q = b
      · have hint := (natResidue_iff_intResidue hbq).mp hres
        simp only [if_pos hres]
        have hsqrt : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn)))
        simp [smoothHeathBrownResidueMellinTerm,
          smoothHeathBrownResidueIndicator,
          smoothHeathBrownThetaLogSourceWeight,
          smoothHeathBrownFactorScale,
          smoothHeathBrownNormalizedFactorCoefficient,
          smoothHeathBrownLogFactor,
          smoothSmallGroupThetaWeight, ArithmeticFunction.log_apply,
          hn.ne', hint]
        have hlogX : Real.log X ≠ 0 :=
          ne_of_gt (Real.log_pos (by linarith [hX]))
        field_simp [hsqrt, hlogX]
      · have hint : (n : ℤ) % (q : ℤ) ≠ (b : ℤ) % (q : ℤ) := by
          intro hh
          exact hres ((natResidue_iff_intResidue hbq).mpr hh)
        simp [smoothHeathBrownResidueMellinTerm,
          smoothHeathBrownResidueIndicator,
          smoothHeathBrownThetaLogSourceWeight,
          smoothHeathBrownFactorScale,
          smoothHeathBrownNormalizedFactorCoefficient,
          smoothHeathBrownLogFactor,
          smoothSmallGroupThetaWeight, ArithmeticFunction.log_apply,
          hn.ne', hres, hint]
  | mobius j => exact (hfree j rfl).elim

private theorem sum_Ico_succ_diff_source (f : ℕ → ℝ) {a b : ℕ}
    (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico a b, (f (n + 1) - f n)) = f b - f a := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · calc
          (∑ n ∈ Finset.Ico a (b + 1), (f (n + 1) - f n)) =
              (∑ n ∈ Finset.Ico a b, (f (n + 1) - f n)) +
                (f (b + 1) - f b) := by
                  rw [Finset.sum_Ico_succ_top hab']
          _ = (f b - f a) + (f (b + 1) - f b) := by rw [ih hab']
          _ = f (b + 1) - f a := by ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

private theorem smoothSmallGroupPrefix_eq_Ioc_source
    (a k : ℕ) (f : ℕ → ℂ) :
    smoothSmallGroupPrefix a f k = ∑ n ∈ Finset.Ioc a k, f n := by
  classical
  unfold smoothSmallGroupPrefix
  have hset :
      (Finset.range (k + 1)).filter (fun n => a < n) = Finset.Ioc a k := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [← Finset.sum_filter]
  rw [hset]

private theorem smoothSmallGroupPrefix_eq_realIntegerInterval_source
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (f : ℕ → ℂ) (g : ℤ → ℂ)
    (hfg : ∀ n : ℕ, f n = g (n : ℤ)) :
    smoothSmallGroupPrefix (Nat.floor x) f k =
      ∑ n ∈ FractionalPrimes.realIntegerInterval x ((k : ℝ) - x), g n := by
  have hset :
      FractionalPrimes.realIntegerInterval x ((k : ℝ) - x) =
        (Finset.Ioc (Nat.floor x) k).map Nat.castEmbedding := by
    classical
    ext n
    rw [FractionalPrimes.mem_realIntegerInterval_iff]
    simp only [Finset.mem_map, Finset.mem_Ioc]
    constructor
    · rintro ⟨hnx, hnk⟩
      have hnpos : 0 < n := by
        have hnposreal : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt hx hnx
        exact_mod_cast hnposreal
      have hncast : (n.toNat : ℤ) = n :=
        Int.toNat_of_nonneg (le_of_lt hnpos)
      refine ⟨n.toNat, ?_, ?_⟩
      · constructor
        · have hnatcastreal : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hncast
          exact (Nat.floor_lt hx).mpr (by rw [hnatcastreal]; exact hnx)
        · have hnatle : (n.toNat : ℝ) ≤ (k : ℝ) := by
            have hnk' : (n : ℝ) ≤ (k : ℝ) := by simpa using hnk
            have hnatcastreal : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hncast
            rw [hnatcastreal]
            exact hnk'
          exact_mod_cast hnatle
      · simpa using hncast
    · rintro ⟨m, hm, hmn⟩
      have hcast : (m : ℝ) = (n : ℝ) := by exact_mod_cast hmn
      constructor
      · have hxlt : x < (m : ℝ) := (Nat.floor_lt hx).mp hm.1
        simpa [hcast] using hxlt
      · have hmk : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hm.2
        simpa [hcast] using hmk
  rw [smoothSmallGroupPrefix_eq_Ioc_source, hset, Finset.sum_map]
  simp only [Nat.castEmbedding_apply]
  rw [Finset.sum_congr rfl]
  intro n hn
  exact hfg n

private theorem logSample_bounds
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 200 ≤ X) {n b : ℕ}
    (hn : 1 ≤ n) (hnb : n ≤ b) (hb : (b : ℝ) ≤ 2 * X) :
    0 ≤ Real.log (n : ℝ) / (4 * Real.log X) ∧
      Real.log (n : ℝ) / (4 * Real.log X) ≤ 1 := by
  have hX : 3 ≤ X := by
    have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 200 := by norm_num
    linarith
  have hXpos : 0 < X := by linarith
  have hXgt1 : 1 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hXgt1
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hnX : (n : ℝ) ≤ X ^ 2 := by
    calc
      (n : ℝ) ≤ b := by exact_mod_cast hnb
      _ ≤ 2 * X := hb
      _ ≤ X ^ 2 := by nlinarith [hX]
  have hlogUpper : Real.log (n : ℝ) ≤ 2 * Real.log X := by
    calc
      Real.log (n : ℝ) ≤ Real.log (X ^ 2) := Real.log_le_log hnreal hnX
      _ = 2 * Real.log X := Real.log_pow X 2
  constructor
  · exact div_nonneg hlogn (by positivity)
  · apply (div_le_one (by positivity)).2
    linarith

private theorem normalizedLog_sample_variation_le_one
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 200 ≤ X)
    {a b : ℕ} (hab : a < b) (hb : (b : ℝ) ≤ 2 * X) :
    (∑ n ∈ Finset.Ioc a (b - 1),
      |(Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X)) -
        (Real.log (n : ℝ) / (4 * Real.log X))|) ≤ 1 := by
  have hset : Finset.Ioc a (b - 1) = Finset.Ico (a + 1) b := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset]
  have hmono (n : ℕ) (hn : n ∈ Finset.Ico (a + 1) b) :
      Real.log (n : ℝ) / (4 * Real.log X) ≤
        Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) := by
    have hnpos : 0 < (n : ℝ) := by
      have hnNat : 1 ≤ n := by
        have := (Finset.mem_Ico.mp hn).1
        omega
      exact_mod_cast (by omega : 0 < n)
    have h3 : (3 : ℝ) ≤ X := by
      have h3' : (3 : ℝ) ≤ (2 : ℝ) ^ 200 := by norm_num
      linarith
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hstep : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ n)
    have hlog := Real.log_le_log hnpos hstep
    exact div_le_div_of_nonneg_right hlog (by positivity)
  have hsumEq :
      (∑ n ∈ Finset.Ico (a + 1) b,
        |(Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X)) -
          (Real.log (n : ℝ) / (4 * Real.log X))|) =
        Real.log (b : ℝ) / (4 * Real.log X) -
          Real.log ((a + 1 : ℕ) : ℝ) / (4 * Real.log X) := by
    calc
      _ = ∑ n ∈ Finset.Ico (a + 1) b,
          ((Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X)) -
            (Real.log (n : ℝ) / (4 * Real.log X))) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [abs_of_nonneg (sub_nonneg.mpr (hmono n hn))]
      _ = _ := sum_Ico_succ_diff_source
        (fun n => Real.log (n : ℝ) / (4 * Real.log X)) (by omega)
  rw [hsumEq]
  have hlogX : 0 < Real.log X := by
    have h3 : (3 : ℝ) ≤ X := by
      have : (3 : ℝ) ≤ (2 : ℝ) ^ 200 := by norm_num
      linarith
    exact Real.log_pos (by linarith)
  have hbpos : 1 ≤ b := by omega
  have hbBound := logSample_bounds hXlarge hbpos le_rfl hb
  have haBound := logSample_bounds hXlarge (by omega : 1 ≤ a + 1)
    (by omega : a + 1 ≤ b) hb
  linarith [hbBound.2, haBound.1]

private theorem realProductStepVariation_le
    {a₁ a₀ b₁ b₀ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : a₀ ≤ 1)
    (hb₀ : 0 ≤ b₀) (hb₁ : b₀ ≤ 1)
    (hb₀' : 0 ≤ b₁) (hb₁' : b₁ ≤ 1) :
    |a₁ * b₁ - a₀ * b₀| ≤ |a₁ - a₀| + |b₁ - b₀| := by
  have hdecomp : a₁ * b₁ - a₀ * b₀ = (a₁ - a₀) * b₁ + a₀ * (b₁ - b₀) := by ring
  rw [hdecomp]
  calc
    |(a₁ - a₀) * b₁ + a₀ * (b₁ - b₀)| ≤
        |(a₁ - a₀) * b₁| + |a₀ * (b₁ - b₀)| := abs_add_le _ _
    _ = |a₁ - a₀| * |b₁| + |a₀| * |b₁ - b₀| := by rw [abs_mul, abs_mul]
    _ ≤ |a₁ - a₀| * 1 + 1 * |b₁ - b₀| := by
      gcongr
      · rw [abs_of_nonneg hb₀']; exact hb₁'
      · rw [abs_of_nonneg ha₀]; exact ha₁
    _ = |a₁ - a₀| + |b₁ - b₀| := by ring

private theorem smoothHeathBrownLogSourceWeight_variation_le_three
    {X N : ℝ} (hXlarge : (2 : ℝ) ^ 200 ≤ X) (hN : 0 < N)
    {a b : ℕ} (hab : a < b) (hb : (b : ℝ) ≤ 2 * X) :
    (∑ n ∈ Finset.Ioc a (b - 1),
      ‖(smoothSmallGroupThetaWeight N (n + 1) *
          ((Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) : ℝ) : ℂ)) -
        (smoothSmallGroupThetaWeight N n *
          ((Real.log (n : ℝ) / (4 * Real.log X) : ℝ) : ℂ))‖) ≤ 3 := by
  have hthetaVar := smoothSmallGroupThetaWeightVariation hN hab
  have hlogVar := normalizedLog_sample_variation_le_one hXlarge hab hb
  let ℓ : ℕ → ℝ := fun n => Real.log (n : ℝ) / (4 * Real.log X)
  have hlogVar' :
      (∑ n ∈ Finset.Ioc a (b - 1), |ℓ (n + 1) - ℓ n|) ≤ 1 := by
    simpa [ℓ] using hlogVar
  have hstep (n : ℕ) (hn : n ∈ Finset.Ioc a (b - 1)) :
      ‖(smoothSmallGroupThetaWeight N (n + 1) *
          ((Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) : ℝ) : ℂ)) -
        (smoothSmallGroupThetaWeight N n *
          ((Real.log (n : ℝ) / (4 * Real.log X) : ℝ) : ℂ))‖ ≤
        ‖smoothSmallGroupThetaWeight N (n + 1) -
            smoothSmallGroupThetaWeight N n‖ +
          |(Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X)) -
            (Real.log (n : ℝ) / (4 * Real.log X))| := by
    let θ₁ := smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / N)
    let θ₀ := smoothDyadicTheta ((n : ℝ) / N)
    let ℓ₁ := Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X)
    let ℓ₀ := Real.log (n : ℝ) / (4 * Real.log X)
    have hθ₀ : 0 ≤ θ₀ ∧ θ₀ ≤ 1 := by
      simp [θ₀, smoothDyadicTheta_nonneg, smoothDyadicTheta_le_one]
    have hθ₁ : 0 ≤ θ₁ ∧ θ₁ ≤ 1 := by
      simp [θ₁, smoothDyadicTheta_nonneg, smoothDyadicTheta_le_one]
    have hnBounds : 1 ≤ n ∧ n ≤ b := by
      have hnI := Finset.mem_Ioc.mp hn
      constructor <;> omega
    have hn1 : 1 ≤ n + 1 := by omega
    have hnI' := Finset.mem_Ioc.mp hn
    have hn1b : n + 1 ≤ b := by omega
    have hℓ₀ := logSample_bounds hXlarge hnBounds.1 hnBounds.2 hb
    have hℓ₁ := logSample_bounds hXlarge hn1 hn1b hb
    have hweightEq :
        smoothSmallGroupThetaWeight N (n + 1) * (ℓ₁ : ℂ) -
          smoothSmallGroupThetaWeight N n * (ℓ₀ : ℂ) =
        ((θ₁ * ℓ₁ - θ₀ * ℓ₀ : ℝ) : ℂ) := by
      simp [θ₁, θ₀, ℓ₁, ℓ₀, smoothSmallGroupThetaWeight]
    have hthetaDiff :
        ‖smoothSmallGroupThetaWeight N (n + 1) -
          smoothSmallGroupThetaWeight N n‖ = |θ₁ - θ₀| := by
      simp only [smoothSmallGroupThetaWeight, θ₁, θ₀]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hweightEq, Complex.norm_real, Real.norm_eq_abs]
    calc
      |θ₁ * ℓ₁ - θ₀ * ℓ₀| ≤ |θ₁ - θ₀| + |ℓ₁ - ℓ₀| :=
        realProductStepVariation_le hθ₀.1 hθ₀.2 hℓ₀.1 hℓ₀.2
          hℓ₁.1 hℓ₁.2
      _ = ‖smoothSmallGroupThetaWeight N (n + 1) -
            smoothSmallGroupThetaWeight N n‖ + |ℓ₁ - ℓ₀| := by
        rw [← hthetaDiff]
      _ = _ := by rfl
  calc
    _ ≤ ∑ n ∈ Finset.Ioc a (b - 1),
        (‖smoothSmallGroupThetaWeight N (n + 1) -
            smoothSmallGroupThetaWeight N n‖ +
          |ℓ (n + 1) - ℓ n|) := by
              apply Finset.sum_le_sum
              intro n hn
              exact hstep n hn
    _ = (∑ n ∈ Finset.Ioc a (b - 1),
          ‖smoothSmallGroupThetaWeight N (n + 1) -
              smoothSmallGroupThetaWeight N n‖) +
        ∑ n ∈ Finset.Ioc a (b - 1),
          |ℓ (n + 1) - ℓ n| := by
              rw [Finset.sum_add_distrib]
    _ ≤ 2 + 1 := add_le_add hthetaVar hlogVar'
    _ = 3 := by norm_num

private theorem selectedIntervalEndpoints_of_support
    {M u v : ℝ}
    (hI : Set.Ioc u v ⊆ Set.Ioc M (2 * M)) (huv : u < v) :
    M ≤ u ∧ v ≤ 2 * M := by
  have hv := hI ⟨huv, le_rfl⟩
  refine ⟨?_, hv.2⟩
  by_contra hMu
  have huM : u < M := lt_of_not_ge hMu
  let w := min v M
  have huw : u < w := lt_min huv huM
  have hwv : w ≤ v := min_le_left _ _
  have hwM : w ≤ M := min_le_right _ _
  have hw := hI ⟨huw, hwv⟩
  exact (not_lt_of_ge hwM) hw.1

/-- The exact `hShort` source input for the theta/log branch of
`lda:small-group`.  It bounds the factorwise residue coefficient on every
real half-open subinterval contained in either required source block.
The periodic estimate is applied to the bare Mellin phase, after which
finite Abel inserts precisely the theta cutoff and (for the logarithmic
tag) the normalized factor `log n / (4 log X)`. -/
theorem smoothHeathBrownThetaLogResidueFactor_shortInterval
    {X z M T0 t u v : ℝ} {q b : ℕ}
    (hXlarge : (2 : ℝ) ^ 200 ≤ X)
    (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (hNlower : X ^ (1 / 100 : ℝ) ≤ smoothHeathBrownFactorScale f)
    (hNupper : smoothHeathBrownFactorScale f ≤
      (2 : ℝ) ^ 11 * Real.sqrt X)
    (hM : M = smoothHeathBrownFactorScale f / 2 ∨
      M = smoothHeathBrownFactorScale f)
    (hq : 0 < q) (hbq : b < q)
    (hqX : (q : ℝ) ≤ X ^ (1 / 400 : ℝ))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X)
    (hu : 0 ≤ u)
    (hI : Set.Ioc u v ⊆ Set.Ioc M (2 * M)) :
    ‖∑ n ∈ factorExtractionRealInterval u v,
        smoothHeathBrownWeightedFactorCoefficient (z := z) f
          (smoothHeathBrownThetaLogResiduePhaseWeight q b t) n‖ ≤
      smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant (1 / 200 : ℝ) 1 * Real.sqrt M *
          (X ^ (-(periodicLogPhaseSaving (1 / 200 : ℝ) 1)) +
            T0 ^ (-1 / 2 : ℝ)) := by
  have hX : 3 ≤ X := by
    have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 200 := by norm_num
    linarith
  have hXpos : 0 < X := by linarith
  have hT0nonneg : 0 ≤ T0 := by linarith
  have hNpos : 0 < smoothHeathBrownFactorScale f :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (smoothHeathBrownFactorScale_ge_one f)
  have hsourceWindow := smoothHeathBrownFreeFactor_sourceScale_meetsPeriodicWindow
    hXlarge hNlower hNupper
  have hMwindow : X ^ (1 / 200 : ℝ) ≤ M ∧ M ≤ X := by
    rcases hM with hhalf | hfull
    · rw [hhalf]
      exact ⟨hsourceWindow.1, by nlinarith [hsourceWindow.2, hNpos.le]⟩
    · rw [hfull]
      exact ⟨by nlinarith [hsourceWindow.1, hNpos.le], hsourceWindow.2⟩
  have hMpos : 0 < M := lt_of_lt_of_le
    (Real.rpow_pos_of_pos hXpos _) hMwindow.1
  have hqperiod : (q : ℝ) ≤ X ^ ((1 / 200 : ℝ) / 2) := by
    have heq : (1 / 200 : ℝ) / 2 = 1 / 400 := by norm_num
    rw [heq]
    exact hqX
  have htXperiod : |t| ≤ X ^ (1 : ℝ) := by simpa using htX
  let C : ℝ := periodicLogPhaseConstant (1 / 200 : ℝ) 1 *
    Real.sqrt M *
      (X ^ (-(periodicLogPhaseSaving (1 / 200 : ℝ) 1)) +
        T0 ^ (-1 / 2 : ℝ))
  have hC : 0 ≤ C := by
    dsimp [C]
    have hconstant : 0 ≤ periodicLogPhaseConstant (1 / 200 : ℝ) 1 := by
      unfold periodicLogPhaseConstant
      exact le_trans (by norm_num) (le_max_left _ _)
    exact mul_nonneg
      (mul_nonneg hconstant (Real.sqrt_nonneg _))
      (add_nonneg (Real.rpow_nonneg hXpos.le _)
        (Real.rpow_nonneg hT0nonneg _))
  let a : ℕ := Nat.floor u
  let bNat : ℕ := Nat.floor v
  by_cases huv : u < v
  · have hend := selectedIntervalEndpoints_of_support hI huv
    have hvnonneg : 0 ≤ v := le_trans hu huv.le
    let base : ℕ → ℂ := fun n =>
      smoothHeathBrownResidueMellinTerm q (b : ℤ) t n
    let omega : ℤ → ℂ := fun n =>
      smoothHeathBrownResidueIndicator q (b : ℤ) n
    have hperiod : ∀ n : ℤ, omega n = omega (n % (q : ℤ)) := by
      intro n
      dsimp [omega]
      exact (smoothHeathBrownResidueIndicator_periodic q (b : ℤ) n).symm
    have hweight : ∀ n : ℤ, ‖omega n‖ ≤ 1 := by
      intro n
      exact smoothHeathBrownResidueIndicator_norm_le_one q (b : ℤ) n
    have hprefix : ∀ k, a < k → k ≤ bNat →
        ‖smoothSmallGroupPrefix a base k‖ ≤ C := by
      intro k hak hkb
      have hxk : u < (k : ℝ) := by
        dsimp [a] at hak
        exact (Nat.floor_lt hu).mp hak
      have hkv : (k : ℝ) ≤ v := by
        have hkfloor : (k : ℝ) ≤ (Nat.floor v : ℝ) := by
          exact_mod_cast hkb
        exact le_trans hkfloor (Nat.floor_le hvnonneg)
      have hphase := periodicLogPhaseBoundedWeightDirichletInterval
        (alpha := (1 / 200 : ℝ)) (A := 1) (X := X) (L := M)
        (T0 := T0) (t := t) (x := u) (H := (k : ℝ) - u)
        (q := q) (omega := omega)
        (by norm_num) (by norm_num) (by norm_num) hX
        hMwindow.1 hMwindow.2 hq hqperiod hT0 hT0t htXperiod
        hperiod hweight hend.1 (by
          calc
            u + ((k : ℝ) - u) = (k : ℝ) := by ring
            _ ≤ v := hkv
            _ ≤ 2 * M := hend.2)
      let g : ℤ → ℂ := fun n =>
        omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))
      have hfg : ∀ n : ℕ, base n = g (n : ℤ) := by
        intro n
        simp [base, g, omega, smoothHeathBrownResidueMellinTerm]
      have hprefEq := smoothSmallGroupPrefix_eq_realIntegerInterval_source
        hu k base g hfg
      rw [hprefEq]
      simpa [C, base, g, omega, smoothHeathBrownResidueMellinTerm] using hphase
    have hsumEq :
        (∑ n ∈ factorExtractionRealInterval u v,
          smoothHeathBrownWeightedFactorCoefficient (z := z) f
            (smoothHeathBrownThetaLogResiduePhaseWeight q b t) n) =
          ∑ n ∈ Finset.Ioc a bNat,
            base n * smoothHeathBrownThetaLogSourceWeight f n := by
      change (∑ n ∈ Finset.Ioc a bNat,
          smoothHeathBrownWeightedFactorCoefficient (z := z) f
            (smoothHeathBrownThetaLogResiduePhaseWeight q b t) n) = _
      apply Finset.sum_congr rfl
      intro n hn
      have hnreal := (mem_factorExtractionRealInterval hu hvnonneg n).mp
        (by simpa [factorExtractionRealInterval, a, bNat] using hn)
      have hnpos : 0 < n := by
        have hnrealpos : 0 < (n : ℝ) := lt_of_le_of_lt hu hnreal.1
        exact_mod_cast hnrealpos
      exact (smoothHeathBrownWeightedFactorCoefficient_eq_residueMellin_mul_sourceWeight
        hX f hfree q b hbq t hnpos)
    by_cases hab : a < bNat
    · cases f with
    | theta j =>
        have hlocal := smoothSmallGroupThetaFiniteAbelTransfer hab
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
            (smoothHeathBrownFactorScale_ge_one (.theta j)))
          base hC hprefix
        have hsum :
            (∑ n ∈ factorExtractionRealInterval u v,
              smoothHeathBrownWeightedFactorCoefficient (z := z)
                (.theta j) (smoothHeathBrownThetaLogResiduePhaseWeight q b t) n) =
              ∑ n ∈ Finset.Ioc a bNat,
                base n * smoothSmallGroupThetaWeight
                  (smoothHeathBrownFactorScale (.theta j)) n := by
          simpa [smoothHeathBrownThetaLogSourceWeight,
            smoothHeathBrownFactorScale] using hsumEq
        rw [hsum]
        have hlocal' :
            ‖∑ n ∈ Finset.Ioc a bNat,
              base n * smoothSmallGroupThetaWeight
                (smoothHeathBrownFactorScale (.theta j)) n‖ ≤ 3 * C := by
          simpa [a, bNat] using hlocal
        calc
          _ ≤ 3 * C := hlocal'
          _ ≤ 5 * C := by nlinarith [hC]
          _ = smoothHeathBrownFreeFactorIntervalCost (.theta j) * C := by
            norm_num [smoothHeathBrownFreeFactorIntervalCost]
          _ = smoothHeathBrownFreeFactorIntervalCost (.theta j) *
              periodicLogPhaseConstant (1 / 200 : ℝ) 1 * Real.sqrt M *
                (X ^ (-(periodicLogPhaseSaving (1 / 200 : ℝ) 1)) +
                  T0 ^ (-1 / 2 : ℝ)) := by
            simp only [C]
            ring
    | logarithm j =>
        let w : ℕ → ℂ := fun n => smoothSmallGroupThetaWeight
            (smoothHeathBrownFactorScale (.logarithm j)) n *
          ((Real.log (n : ℝ) / (4 * Real.log X) : ℝ) : ℂ)
        have hbcast : (bNat : ℝ) ≤ 2 * X := by
          have hbv : (bNat : ℝ) ≤ v := Nat.floor_le hvnonneg
          calc
            (bNat : ℝ) ≤ v := hbv
            _ ≤ 2 * M := hend.2
            _ ≤ 2 * X := by nlinarith [hMwindow.2]
        have hbpos : 1 ≤ bNat := by omega
        have hlogb := logSample_bounds hXlarge hbpos le_rfl hbcast
        have hthetaB : ‖smoothSmallGroupThetaWeight
            (smoothHeathBrownFactorScale (.logarithm j)) bNat‖ ≤ 1 :=
          smoothSmallGroupThetaWeight_norm_le_one _ _
        have hlogB : ‖((Real.log (bNat : ℝ) /
            (4 * Real.log X) : ℝ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hlogb.1]
          exact hlogb.2
        have hterminal : ‖w bNat‖ ≤ 1 := by
          dsimp [w]
          rw [norm_mul]
          exact mul_le_one₀ hthetaB (norm_nonneg _) hlogB
        have hvariation := smoothHeathBrownLogSourceWeight_variation_le_three
          hXlarge (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
            (smoothHeathBrownFactorScale_ge_one (.logarithm j)))
          hab hbcast
        have hweightvariation :
            ‖w bNat‖ +
              ∑ n ∈ Finset.Ioc a (bNat - 1), ‖w (n + 1) - w n‖ ≤ 4 := by
          have hvariation' :
              (∑ n ∈ Finset.Ioc a (bNat - 1), ‖w (n + 1) - w n‖) ≤ 3 := by
            simpa only [w] using hvariation
          calc
            _ ≤ 1 + 3 := add_le_add hterminal hvariation'
            _ = 4 := by norm_num
        have hlocal := smoothSmallGroupFiniteAbelTransfer hab base w hC
          hprefix hweightvariation
        have hsum :
            (∑ n ∈ factorExtractionRealInterval u v,
              smoothHeathBrownWeightedFactorCoefficient (z := z)
                (.logarithm j)
                (smoothHeathBrownThetaLogResiduePhaseWeight q b t) n) =
              ∑ n ∈ Finset.Ioc a bNat, base n * w n := by
          simpa [w, smoothHeathBrownThetaLogSourceWeight,
            smoothHeathBrownFactorScale] using hsumEq
        rw [hsum]
        have hlocal' :
            ‖∑ n ∈ Finset.Ioc a bNat, base n * w n‖ ≤ 4 * C := by
          simpa [a, bNat, mul_comm] using hlocal
        calc
          _ ≤ 4 * C := hlocal'
          _ ≤ 6 * C := by nlinarith [hC]
          _ = smoothHeathBrownFreeFactorIntervalCost (.logarithm j) * C := by
            norm_num [smoothHeathBrownFreeFactorIntervalCost]
          _ = smoothHeathBrownFreeFactorIntervalCost (.logarithm j) *
              periodicLogPhaseConstant (1 / 200 : ℝ) 1 * Real.sqrt M *
                (X ^ (-(periodicLogPhaseSaving (1 / 200 : ℝ) 1)) +
                  T0 ^ (-1 / 2 : ℝ)) := by
            simp only [C]
            ring
    | mobius j => exact (hfree j rfl).elim
    · have hba : bNat ≤ a := Nat.le_of_not_gt hab
      have hEmpty : Finset.Ioc a bNat = ∅ := Finset.Ioc_eq_empty_of_le hba
      rw [hsumEq, hEmpty]
      simp
      have hcost : 0 ≤ smoothHeathBrownFreeFactorIntervalCost f := by
        cases f <;> simp [smoothHeathBrownFreeFactorIntervalCost]
      simpa [C, mul_assoc] using mul_nonneg hcost hC
  · have hvu : v ≤ u := le_of_not_gt huv
    have hfloor : Nat.floor v ≤ Nat.floor u := Nat.floor_mono hvu
    have hEmpty : factorExtractionRealInterval u v = ∅ := by
      simp [factorExtractionRealInterval, hfloor]
    rw [hEmpty]
    simp
    have hcost : 0 ≤ smoothHeathBrownFreeFactorIntervalCost f := by
      cases f <;> simp [smoothHeathBrownFreeFactorIntervalCost]
    simpa [C, mul_assoc] using mul_nonneg hcost hC

#print axioms smoothHeathBrownThetaLogResidueFactor_shortInterval

/-- The theta/log selected-group estimate for the exact residue-phase
weights.  The local factor cancellation is supplied by
`smoothHeathBrownThetaLogResidueFactor_shortInterval`; the finite transfer
then gives the block bound, and the two periodic error terms are absorbed
with the source margin `D ≥ 2K+10`.  The interval `(x,y]` may be any
subinterval of the source block `(L,2L]`. -/
theorem smoothHeathBrownThetaLogSelectedGroupResidue_logDecay
    {X z L T0 t x y : ℝ} {fs : List (SmoothHeathBrownFactor X)}
    {q : ℕ} {B K D : ℝ}
    (I : Finset (Fin fs.length)) (selected : Fin fs.length)
    (hselected : selected ∈ I) (hcount : I.card ≤ 20)
    (residue : Fin fs.length → ℕ) (hresidue : residue selected < q)
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius j)
    (hB : 0 < B) (hK : 0 < K) (hD : 2 * K + 10 ≤ D)
    (hlog : 2 ≤ Real.log X)
    (hq : 0 < q) (hqLog : (q : ℝ) ≤ (Real.log X) ^ B)
    (hqLarge : (2 / (1 / 400 : ℝ)) *
      Real.log (logAbsorptionM (1 / 400) B) ≤ Real.log X)
    (hT0Eq : T0 = (Real.log X) ^ D / 2)
    (hT0t : T0 ≤ |t|) (htX : |t| ≤ X)
    (hNlower : X ^ (1 / 100 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected))
    (hNupper : smoothHeathBrownFactorScale (fs.get selected) ≤
      (2 : ℝ) ^ 11 * Real.sqrt X)
    (h : ℤ)
    (hL : L = (2 : ℝ) ^ h *
      (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)))
    (hh : -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ))
    (hLx : L ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 * L)
    (hpolyLarge : (2 / periodicLogPhaseSaving (1 / 200) 1) *
      Real.log (2 * smoothHeathBrownFreeFactorBlockConstant
          (fs.get selected) *
        logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) ≤
          Real.log X)
    (htailLarge : (2 * Real.sqrt 2 *
      smoothHeathBrownFreeFactorBlockConstant (fs.get selected)) ^
        (1 / 5 : ℝ) ≤ Real.log X) :
    ‖smoothGroupSubsetConvolutionSum I
        (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
        (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
          (fs.get i)
          (smoothHeathBrownThetaLogResiduePhaseWeight q (residue i) t) n)
        x y‖ ≤ Real.sqrt L * (Real.log X) ^ (-K) := by
  have hXpos : 0 < X := by
    have htwo : 0 < (2 : ℝ) ^ 200 := by positivity
    linarith
  have hXthree : 3 ≤ X := by
    have hthree : (3 : ℝ) ≤ (2 : ℝ) ^ 200 := by norm_num
    linarith
  have hXone : 1 ≤ X := by linarith
  have hlogone : 1 ≤ Real.log X := by linarith
  have hD10 : 10 ≤ D := by linarith
  have hT0 : 1 ≤ T0 :=
    smoothHeathBrownFreeFactor_sourceT0_ge_one hlog hD10 hT0Eq
  have hqBound : (q : ℝ) ≤ X ^ (1 / 400 : ℝ) :=
    smoothHeathBrownFreeFactor_modulus_log_bound hXone hB.le hqLog hqLarge
  have hqBound' : (q : ℝ) ≤ X ^ ((1 / 200 : ℝ) / 2) := by
    have heq : (1 / 200 : ℝ) / 2 = 1 / 400 := by norm_num
    rw [heq]
    exact hqBound
  have hscalePos : ∀ i ∈ I,
      0 < smoothHeathBrownFactorScale (fs.get i) := by
    intro i hi
    have hscale := smoothHeathBrownFactorScale_ge_one (fs.get i)
    linarith
  have hscaleProductPos : 0 <
      ∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i) :=
    Finset.prod_pos fun i hi => hscalePos i hi
  have hLpos : 0 < L := by
    rw [hL]
    exact mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) h) hscaleProductPos
  have hx : 0 ≤ x := le_trans (le_of_lt hLpos) hLx
  let omega : Fin fs.length → ℕ → ℂ := fun i n =>
    smoothHeathBrownThetaLogResiduePhaseWeight q (residue i) t n
  have homega : ∀ i n, ‖omega i n‖ ≤ 1 := by
    intro i n
    exact smoothHeathBrownThetaLogResiduePhaseWeight_norm_le_one
      q (residue i) t n
  let err : ℝ :=
    X ^ (-(periodicLogPhaseSaving (1 / 200) 1)) +
      T0 ^ (-1 / 2 : ℝ)
  let eps : ℝ := smoothHeathBrownFreeFactorIntervalCost
      (fs.get selected) * periodicLogPhaseConstant (1 / 200) 1 * err
  have hcost : 0 ≤ smoothHeathBrownFreeFactorIntervalCost
      (fs.get selected) := by
    cases fs.get selected <;> simp [smoothHeathBrownFreeFactorIntervalCost]
  have hphase : 0 ≤ periodicLogPhaseConstant (1 / 200 : ℝ) 1 := by
    unfold periodicLogPhaseConstant
    exact le_trans (by norm_num) (le_max_left _ _)
  have herr : 0 ≤ err := by
    dsimp [err]
    exact add_nonneg (Real.rpow_nonneg hXpos.le _)
      (Real.rpow_nonneg (by linarith : 0 ≤ T0) _)
  have heps : 0 ≤ eps := by
    dsimp [eps]
    exact mul_nonneg (mul_nonneg hcost hphase) herr
  have hShort : ∀ M : ℝ,
      (M = smoothHeathBrownFactorScale (fs.get selected) / 2 ∨
        M = smoothHeathBrownFactorScale (fs.get selected)) →
      ∀ u v : ℝ, 0 ≤ u →
        Set.Ioc u v ⊆ Set.Ioc M (2 * M) →
        ‖∑ n ∈ factorExtractionRealInterval u v,
          smoothHeathBrownWeightedFactorCoefficient (z := z)
            (fs.get selected) (omega selected) n‖ ≤ eps * Real.sqrt M := by
    intro M hM u v hu hI
    have hlocal := smoothHeathBrownThetaLogResidueFactor_shortInterval
      (X := X) (z := z) (M := M) (T0 := T0) (t := t) (u := u) (v := v)
      (q := q) (b := residue selected) hXscale (fs.get selected) hfree
      hNlower hNupper hM hq hresidue hqBound hT0 hT0t htX hu hI
    calc
      _ ≤ smoothHeathBrownFreeFactorIntervalCost (fs.get selected) *
          periodicLogPhaseConstant (1 / 200) 1 * Real.sqrt M * err := by
            simpa [err] using hlocal
      _ = eps * Real.sqrt M := by
            dsimp [eps]
            ring
  have htransfer := smoothHeathBrownSubsetWideSupportFiniteTransfer
    hXthree fs I selected hselected hcount h L eps x y omega hL hh heps hx
    hxy homega hShort
  have hC : 1 ≤ smoothHeathBrownFreeFactorBlockConstant
      (fs.get selected) :=
    smoothHeathBrownFreeFactorBlockConstant_ge_one
      (fs.get selected) hfree
  have hdelta : 0 < periodicLogPhaseSaving (1 / 200) 1 := by
    unfold periodicLogPhaseSaving
    positivity
  have hAbsorb := smoothHeathBrownFreeFactor_sourceLogError_absorption
    hXone hlogone (le_of_lt hK) hD hC hdelta hT0Eq hpolyLarge htailLarge
  calc
    _ ≤ (2 : ℝ) ^ 11 * 5 ^ 19 * eps * Real.sqrt L := htransfer
    _ = smoothHeathBrownFreeFactorBlockConstant (fs.get selected) *
          Real.sqrt L * err := by
            dsimp [eps, err, smoothHeathBrownFreeFactorBlockConstant]
            ring
    _ = Real.sqrt L *
          (smoothHeathBrownFreeFactorBlockConstant (fs.get selected) * err) := by
            ring
    _ ≤ Real.sqrt L * (Real.log X) ^ (-K) :=
      mul_le_mul_of_nonneg_left hAbsorb (Real.sqrt_nonneg L)

#print axioms smoothHeathBrownThetaLogSelectedGroupResidue_logDecay

end FractionalPrimes.Literature.DirichletAdapter

end
