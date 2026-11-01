module

public import FractionalPrimes.Literature.Uniformity.NewtonExpansionPeriodicity
public import FractionalPrimes.Literature.Uniformity.CoefficientRecurrenceToLogPhase
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Variation of a phase with controlled binomial coefficients

Blueprint `lu:binomial-tv`. The constant is exactly
`B_d = sum_{j=1}^d j^j/j!`. The derivative estimate is obtained by
differentiating the finite falling-factor product, as in the source.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

noncomputable section

/-- The exact degree-dependent constant in the approved variation bound. -/
def binomialVariationConstant (d : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 d, (j : ℝ) ^ j / (j.factorial : ℝ)

@[simp]
theorem binomialVariationConstant_zero : binomialVariationConstant 0 = 0 := by
  simp [binomialVariationConstant]

theorem binomialVariationConstant_nonneg (d : ℕ) :
    0 ≤ binomialVariationConstant d := by
  unfold binomialVariationConstant
  exact Finset.sum_nonneg (by intro j hj; positivity)

theorem newton_descPochhammer_eq_prod (j : ℕ) :
    descPochhammer ℝ j =
      ∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ)) := by
  apply Polynomial.funext
  intro t
  simp [Polynomial.eval_prod, descPochhammer_eval_eq_prod_range]

/-- The exact derivative of the falling-factor binomial polynomial. -/
theorem newtonBinomialPolynomial_derivative_eval (j : ℕ) (t : ℝ) :
    (newtonBinomialPolynomial j).derivative.eval t =
      (j.factorial : ℝ)⁻¹ *
        ∑ i ∈ Finset.range j,
          ∏ a ∈ (Finset.range j).erase i, (t - (a : ℝ)) := by
  rw [newtonBinomialPolynomial, Polynomial.derivative_mul]
  simp only [Polynomial.derivative_C, zero_mul, zero_add]
  rw [newton_descPochhammer_eq_prod, Polynomial.derivative_prod_finset]
  simp [Polynomial.eval_finsetSum, Polynomial.eval_prod]

/-- Each factor `t-i` is bounded by `j*H` on `[0,H]` when `H≥1`. -/
theorem abs_newtonFactor_le (j i : ℕ) (hj : 1 ≤ j) (hi : i < j)
    (H t : ℝ) (hH : 1 ≤ H) (ht : t ∈ Set.Icc 0 H) :
    |t - (i : ℝ)| ≤ (j : ℝ) * H := by
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hir : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hi.le
  have hi0 : (0 : ℝ) ≤ i := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith [ht.1, ht.2]

/-- The source derivative envelope, valid including `H=1`. -/
theorem abs_newtonBinomialPolynomial_derivative_le
    (j : ℕ) (hj : 1 ≤ j) (H t : ℝ) (hH : 1 ≤ H)
    (ht : t ∈ Set.Icc 0 H) :
    |(newtonBinomialPolynomial j).derivative.eval t| ≤
      (j : ℝ) * ((j : ℝ) * H) ^ (j - 1) / (j.factorial : ℝ) := by
  rw [newtonBinomialPolynomial_derivative_eval, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (j.factorial : ℝ)⁻¹)]
  have hsum :
      |∑ i ∈ Finset.range j,
          ∏ a ∈ (Finset.range j).erase i, (t - (a : ℝ))| ≤
        (j : ℝ) * ((j : ℝ) * H) ^ (j - 1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range j,
          |∏ a ∈ (Finset.range j).erase i, (t - (a : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range j, ((j : ℝ) * H) ^ (j - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.abs_prod]
        have hprod := Finset.prod_le_prod₀
          (s := (Finset.range j).erase i)
          (f := fun a : ℕ => |t - (a : ℝ)|) (g := fun _ : ℕ => (j : ℝ) * H)
          (by intro a ha; positivity)
          (by
            intro a ha
            exact abs_newtonFactor_le j a hj
              (Finset.mem_range.mp (Finset.mem_of_mem_erase ha)) H t hH ht)
        simpa only [Finset.prod_const, Finset.card_erase_of_mem hi,
          Finset.card_range] using hprod
      _ = (j : ℝ) * ((j : ℝ) * H) ^ (j - 1) := by simp
  calc
    _ ≤ (j.factorial : ℝ)⁻¹ *
        ((j : ℝ) * ((j : ℝ) * H) ^ (j - 1)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The exact shifted real derivative of a Newton-coordinate polynomial. -/
theorem hasDerivAt_newtonRealPhase
    (d : ℕ) (M : ℤ) (s : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (newtonRealPhase d M s)
      (∑ j ∈ Finset.range (d + 1), s j *
        (newtonBinomialPolynomial j).derivative.eval (t - (M : ℝ))) t := by
  unfold newtonRealPhase
  apply HasDerivAt.fun_sum
  intro j hj
  have hshift : HasDerivAt (fun t : ℝ => t - (M : ℝ)) 1 t :=
    (hasDerivAt_id t).sub_const _
  simpa only [mul_one, Function.comp_def] using
    (((newtonBinomialPolynomial j).hasDerivAt (t - (M : ℝ))).comp t hshift).const_mul
      (s j)

/-- Each weighted derivative term has the uniform normalized budget
`(B/H)*(j^j/j!)`. -/
theorem abs_weighted_newtonBinomialPolynomial_derivative_le
    (j : ℕ) (hj : 1 ≤ j) (H B t a : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B) (ht : t ∈ Set.Icc 0 H)
    (ha : |a| ≤ B / H ^ j) :
    |a * (newtonBinomialPolynomial j).derivative.eval t| ≤
      (B / H) * ((j : ℝ) ^ j / (j.factorial : ℝ)) := by
  have hHpos : 0 < H := by linarith
  have hjfact : (j.factorial : ℝ) ≠ 0 := by positivity
  have hjexp : j - 1 + 1 = j := by omega
  have hpower : (j : ℝ) * ((j : ℝ) * H) ^ (j - 1) * H =
      (j : ℝ) ^ j * H ^ j := by
    rw [mul_pow]
    calc
      _ = ((j : ℝ) * (j : ℝ) ^ (j - 1)) * (H ^ (j - 1) * H) := by ring
      _ = _ := by rw [← pow_succ', ← pow_succ, hjexp]
  rw [abs_mul]
  calc
    |a| * |(newtonBinomialPolynomial j).derivative.eval t| ≤
        (B / H ^ j) *
          ((j : ℝ) * ((j : ℝ) * H) ^ (j - 1) / (j.factorial : ℝ)) :=
      mul_le_mul ha (abs_newtonBinomialPolynomial_derivative_le j hj H t hH ht)
        (abs_nonneg _) (by positivity)
    _ = (B / H) * ((j : ℝ) ^ j / (j.factorial : ℝ)) := by
      apply mul_right_cancel₀ (by positivity : H ^ j * (j.factorial : ℝ) * H ≠ 0)
      field_simp [hHpos.ne', hjfact]
      nlinarith [hpower]

/-- Pointwise real-derivative bound after summing all controlled Newton
coefficients; the constant coefficient contributes zero. -/
theorem abs_deriv_newtonRealPhase_le
    (d : ℕ) (M : ℤ) (s : ℕ → ℝ) (H B t : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hs : ∀ j, 1 ≤ j → j ≤ d → |s j| ≤ B / H ^ j)
    (ht : t ∈ Set.Icc (M : ℝ) ((M : ℝ) + H)) :
    |deriv (newtonRealPhase d M s) t| ≤
      (B / H) * binomialVariationConstant d := by
  rw [(hasDerivAt_newtonRealPhase d M s t).deriv]
  have hsum : (∑ j ∈ Finset.range (d + 1), s j *
      (newtonBinomialPolynomial j).derivative.eval (t - (M : ℝ))) =
      ∑ j ∈ Finset.Icc 1 d, s j *
        (newtonBinomialPolynomial j).derivative.eval (t - (M : ℝ)) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hj).2; omega)
    · intro j hj hnot
      have hj0 : j = 0 := by
        simp only [Finset.mem_range, Finset.mem_Icc, not_and_or, not_le] at hj hnot
        omega
      subst j
      simp [newtonBinomialPolynomial, descPochhammer_zero]
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 d,
        |s j * (newtonBinomialPolynomial j).derivative.eval (t - (M : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 d,
        (B / H) * ((j : ℝ) ^ j / (j.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjb := Finset.mem_Icc.mp hj
      exact abs_weighted_newtonBinomialPolynomial_derivative_le j hjb.1 H B
        (t - (M : ℝ)) (s j) hH hB
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ (hs j hjb.1 hjb.2)
    _ = _ := by rw [binomialVariationConstant, Finset.mul_sum]

/-- The smooth unit-frequency phase with the prescribed Newton
coefficients. -/
def binomialComplexPhase (d : ℕ) (M : ℤ) (s : ℕ → ℝ) (t : ℝ) : ℂ :=
  unitFrequencyPhase (newtonRealPhase d M s t)

@[simp]
theorem norm_binomialComplexPhase (d : ℕ) (M : ℤ) (s : ℕ → ℝ) (t : ℝ) :
    ‖binomialComplexPhase d M s t‖ = 1 := norm_unitFrequencyPhase _

theorem contDiff_binomialComplexPhase (d : ℕ) (M : ℤ) (s : ℕ → ℝ) :
    ContDiff ℝ 1 (binomialComplexPhase d M s) := by
  have hreal : ContDiff ℝ 1 (newtonRealPhase d M s) := by
    unfold newtonRealPhase
    apply ContDiff.sum
    intro j hj
    have hpoly : ContDiff ℝ 1 (fun t : ℝ => (newtonBinomialPolynomial j).eval t) := by
      simpa using (newtonBinomialPolynomial j).contDiff_aeval (𝕜 := ℝ) 1
    have hshift : ContDiff ℝ 1 (fun t : ℝ => t - (M : ℝ)) := by fun_prop
    simpa only [Function.comp_def, smul_eq_mul] using
      (hpoly.comp hshift).const_smul (s j)
  have hscaled : ContDiff ℝ 1 (fun t => (2 * Real.pi) * newtonRealPhase d M s t) := by
    simpa [smul_eq_mul] using hreal.const_smul (2 * Real.pi)
  have hcomplex : ContDiff ℝ 1
      (fun t => (((2 * Real.pi) * newtonRealPhase d M s t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hscaled
  have harg : ContDiff ℝ 1
      (fun t => (((2 * Real.pi) * newtonRealPhase d M s t : ℝ) : ℂ) * Complex.I) := by
    simpa [smul_eq_mul, mul_comm] using hcomplex.const_smul Complex.I
  unfold binomialComplexPhase unitFrequencyPhase
  convert harg.cexp using 1

theorem norm_deriv_binomialComplexPhase
    (d : ℕ) (M : ℤ) (s : ℕ → ℝ) (t : ℝ) :
    ‖deriv (binomialComplexPhase d M s) t‖ =
      2 * Real.pi * |deriv (newtonRealPhase d M s) t| := by
  rw [(hasDerivAt_newtonRealPhase d M s t).deriv]
  change ‖deriv (fun x => unitFrequencyPhase (newtonRealPhase d M s x)) t‖ = _
  rw [(HasDerivAt.unitFrequencyPhase_comp (hasDerivAt_newtonRealPhase d M s t)).deriv,
    norm_mul, norm_unitFrequencyPhase, one_mul, norm_mul,
    Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (mul_pos two_pos Real.pi_pos)]

/-- Integrating the phase derivative preserves the precise source budget
`2*pi*B*B_d`. -/
theorem integral_norm_derivWithin_binomialComplexPhase_le
    (d : ℕ) (M : ℤ) (s : ℕ → ℝ) (H B : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hs : ∀ j, 1 ≤ j → j ≤ d → |s j| ≤ B / H ^ j) :
    (∫ t in (M : ℝ)..(M : ℝ) + H,
        ‖derivWithin (binomialComplexPhase d M s)
          (Set.Icc (M : ℝ) ((M : ℝ) + H)) t‖) ≤
      2 * Real.pi * B * binomialVariationConstant d := by
  have hHpos : 0 < H := by linarith
  have hXY : (M : ℝ) ≤ (M : ℝ) + H := by linarith
  have hXYlt : (M : ℝ) < (M : ℝ) + H := by linarith
  let G : ℝ → ℝ := fun t =>
    ‖derivWithin (binomialComplexPhase d M s)
      (Set.Icc (M : ℝ) ((M : ℝ) + H)) t‖
  let C : ℝ := 2 * Real.pi * (B / H) * binomialVariationConstant d
  have hGcont : ContinuousOn G (Set.Icc (M : ℝ) ((M : ℝ) + H)) := by
    dsimp [G]
    exact ((contDiff_binomialComplexPhase d M s).contDiffOn.continuousOn_derivWithin
      (uniqueDiffOn_Icc hXYlt) (by norm_num)).norm
  have hGint : IntervalIntegrable G MeasureTheory.volume (M : ℝ) ((M : ℝ) + H) :=
    hGcont.intervalIntegrable_of_Icc hXY
  have hpoint : ∀ t ∈ Set.Ioo (M : ℝ) ((M : ℝ) + H), G t ≤ C := by
    intro t ht
    dsimp [G, C]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
      norm_deriv_binomialComplexPhase]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (abs_deriv_newtonRealPhase_le d M s H B t hH hB hs ⟨ht.1.le, ht.2.le⟩)
      (by positivity : 0 ≤ 2 * Real.pi)
  calc
    (∫ t in (M : ℝ)..(M : ℝ) + H, G t) ≤
        ∫ _t in (M : ℝ)..(M : ℝ) + H, C :=
      intervalIntegral.integral_mono_on_of_le_Ioo hXY hGint
        intervalIntegrable_const hpoint
    _ = 2 * Real.pi * B * binomialVariationConstant d := by
      simp only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul]
      dsimp [C]
      field_simp [hHpos.ne']

/-- The polynomial phase has the source variation bound on every ordered
subset of the short integer interval, hence on each finite progression. -/
theorem orderedTotalVariation_binomialComplexPhase_le
    (d : ℕ) (M : ℤ) (s : ℕ → ℝ) (H B : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hs : ∀ j, 1 ≤ j → j ≤ d → |s j| ≤ B / H ^ j)
    (P : Set ℤ) (hP : ∀ n ∈ P, (n : ℝ) ∈ Set.Icc (M : ℝ) ((M : ℝ) + H)) :
    orderedTotalVariation P (fun n : ℤ => binomialComplexPhase d M s n) ≤
      ENNReal.ofReal (1 + 2 * Real.pi * B * binomialVariationConstant d) := by
  have hXY : (M : ℝ) ≤ (M : ℝ) + H := by linarith
  have hsup : intervalNormSup (M : ℝ) ((M : ℝ) + H)
      (binomialComplexPhase d M s) = 1 := by
    have hrange : Set.range
        (fun t : Set.Icc (M : ℝ) ((M : ℝ) + H) =>
          ‖binomialComplexPhase d M s (t : ℝ)‖) = {1} := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        simp
      · intro hy
        have hy' : y = 1 := by simpa using hy
        subst y
        exact ⟨⟨(M : ℝ), ⟨le_rfl, hXY⟩⟩, by simp⟩
    rw [intervalNormSup, hrange]
    simp
  have hbound := orderedTotalVariation_le_sup_add_integral hXY
    (binomialComplexPhase d M s) (contDiff_binomialComplexPhase d M s).contDiffOn P hP
  apply hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hsup]
  exact add_le_add le_rfl
    (integral_norm_derivWithin_binomialComplexPhase_le d M s H B hH hB hs)

/-- The rational Newton factor is constant on each residue class of its
exact period, so it costs no further variation within that class. -/
theorem residueClassTotalVariation_rational_add_binomial_le
    (d q : ℕ) (M : ℤ) (r s : ℕ → ℝ) (H B : ℝ)
    (hq : 1 ≤ q) (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hr : ∀ j, 1 ≤ j → j ≤ d → ∃ k : ℤ, (q : ℝ) * r j = (k : ℝ))
    (hs : ∀ j, 1 ≤ j → j ≤ d → |s j| ≤ B / H ^ j) :
    ∃ hperiod : 0 < q * d.factorial,
      residueClassTotalVariation (logPhaseIntegerInterval (M : ℝ) H)
          (fun n : ℤ => unitFrequencyPhase
            (newtonRealPhase d M r n + newtonRealPhase d M s n))
          (q * d.factorial) hperiod ≤
        ENNReal.ofReal ((q * d.factorial : ℕ) *
          (1 + 2 * Real.pi * B * binomialVariationConstant d)) := by
  have hperiod : 0 < q * d.factorial :=
    Nat.mul_pos (by omega) (Nat.factorial_pos d)
  refine ⟨hperiod, ?_⟩
  let C : ℝ := 1 + 2 * Real.pi * B * binomialVariationConstant d
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [binomialVariationConstant_nonneg d]
  let g : ℤ → ℂ := fun n => unitFrequencyPhase (newtonRealPhase d M r n)
  let k : ℤ → ℂ := fun n => binomialComplexPhase d M s n
  have hper := newtonRationalPhase_periodic d q M r hq hr
  have hclass (a : ℕ) :
      orderedTotalVariation
          (logPhaseIntegerInterval (M : ℝ) H ∩ integerResidueClass (q * d.factorial) a)
          (fun n : ℤ => unitFrequencyPhase
            (newtonRealPhase d M r n + newtonRealPhase d M s n)) ≤
        ENNReal.ofReal C := by
    let P := logPhaseIntegerInterval (M : ℝ) H ∩ integerResidueClass (q * d.factorial) a
    have hP : ∀ n ∈ P, (n : ℝ) ∈ Set.Icc (M : ℝ) ((M : ℝ) + H) := by
      intro n hn
      exact ⟨hn.1.1.le, hn.1.2⟩
    have hconst : ∀ n ∈ P, g n = g (a : ℤ) := by
      intro n hn
      obtain ⟨b, hb⟩ := hn.2
      have heq := hper.int_mul b (a : ℤ)
      dsimp [g]
      rw [hb]
      simpa only [Int.cast_id, mul_comm] using heq
    have hg : orderedTotalVariation P g ≤ 1 :=
      orderedTotalVariation_le_one_of_eq_unit_constant
        (by linarith : (M : ℝ) ≤ (M : ℝ) + H) P g (g (a : ℤ))
        (norm_unitFrequencyPhase _) hP hconst
    have hk : orderedTotalVariation P k ≤ ENNReal.ofReal C :=
      orderedTotalVariation_binomialComplexPhase_le d M s H B hH hB hs P hP
    have hfactor : ∀ n ∈ P,
        unitFrequencyPhase (newtonRealPhase d M r n + newtonRealPhase d M s n) =
          g n * k n := by
      intro n hn
      exact unitFrequencyPhase_add _ _
    change orderedTotalVariation P _ ≤ _
    rw [orderedTotalVariation_congr_on_logPhase P _ (fun n => g n * k n) hfactor]
    calc
      _ ≤ orderedTotalVariation P g * orderedTotalVariation P k :=
        orderedTotalVariation_mul_le P g k
      _ ≤ 1 * ENNReal.ofReal C := mul_le_mul hg hk (by simp) (by simp)
      _ = ENNReal.ofReal C := one_mul _
  unfold residueClassTotalVariation
  calc
    _ ≤ ∑ _a ∈ Finset.range (q * d.factorial), ENNReal.ofReal C :=
      Finset.sum_le_sum (by intro a ha; exact hclass a)
    _ = ((q * d.factorial : ℕ) : ENNReal) * ENNReal.ofReal C := by simp
    _ = ENNReal.ofReal (((q * d.factorial : ℕ) : ℝ) * C) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((q * d.factorial : ℕ) : ℝ))]
      simp

/-- Original-polynomial version of the smooth-binomial variation bound. -/
theorem finiteOrderedTotalVariation_polynomial_binomial_le
    (d : ℕ) (M : ℤ) (S : Polynomial ℝ) (s : ℕ → ℝ) (H B : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hS : ∀ t : ℝ, S.eval ((M : ℝ) + t) =
      ∑ j ∈ Finset.range (d + 1), s j * (newtonBinomialPolynomial j).eval t)
    (hs : ∀ j, 1 ≤ j → j ≤ d → |s j| ≤ B / H ^ j)
    (P : Finset ℤ) (hP : ∀ n ∈ P, (M : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (M : ℝ) + H) :
    finiteOrderedTotalVariation P (fun n : ℤ => unitFrequencyPhase (S.eval n)) ≤
      1 + 2 * Real.pi * B * binomialVariationConstant d := by
  have hphase : (fun n : ℤ => unitFrequencyPhase (S.eval n)) =
      (fun n : ℤ => binomialComplexPhase d M s n) := by
    funext n
    have hSn : S.eval (n : ℝ) = newtonRealPhase d M s n := by
      simpa [newtonRealPhase] using hS ((n : ℝ) - (M : ℝ))
    exact congrArg unitFrequencyPhase hSn
  rw [hphase]
  have hfinite : ENNReal.ofReal
      (finiteOrderedTotalVariation P (fun n : ℤ => binomialComplexPhase d M s n)) ≤
      orderedTotalVariation (P : Set ℤ) (fun n : ℤ => binomialComplexPhase d M s n) := by
    exact le_iSup_of_le ⟨P, fun _ hn => hn⟩ le_rfl
  have hbound := orderedTotalVariation_binomialComplexPhase_le d M s H B hH hB hs
    (P : Set ℤ) (by intro n hn; exact ⟨(hP n hn).1.le, (hP n hn).2⟩)
  exact (ENNReal.ofReal_le_ofReal_iff
    (by positivity [binomialVariationConstant_nonneg d])).mp (hfinite.trans hbound)

/-- Original-polynomial version of the rational-factor residue bound. -/
theorem residueClassTotalVariation_polynomial_rational_add_binomial_le
    (d q : ℕ) (M : ℤ) (R S : Polynomial ℝ) (r s : ℕ → ℝ) (H B : ℝ)
    (hq : 1 ≤ q) (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hR : ∀ t : ℝ, R.eval ((M : ℝ) + t) =
      ∑ j ∈ Finset.range (d + 1), r j * (newtonBinomialPolynomial j).eval t)
    (hS : ∀ t : ℝ, S.eval ((M : ℝ) + t) =
      ∑ j ∈ Finset.range (d + 1), s j * (newtonBinomialPolynomial j).eval t)
    (hr : ∀ j, 1 ≤ j → j ≤ d → ∃ k : ℤ, (q : ℝ) * r j = (k : ℝ))
    (hs : ∀ j, 1 ≤ j → j ≤ d → |s j| ≤ B / H ^ j) :
    ∃ hperiod : 0 < q * d.factorial,
      residueClassTotalVariation (logPhaseIntegerInterval (M : ℝ) H)
          (fun n : ℤ => unitFrequencyPhase ((R + S).eval n))
          (q * d.factorial) hperiod ≤
        ENNReal.ofReal ((q * d.factorial : ℕ) *
          (1 + 2 * Real.pi * B * binomialVariationConstant d)) := by
  have hphase : (fun n : ℤ => unitFrequencyPhase ((R + S).eval n)) =
      (fun n : ℤ => unitFrequencyPhase
        (newtonRealPhase d M r n + newtonRealPhase d M s n)) := by
    funext n
    have hRn : R.eval (n : ℝ) = newtonRealPhase d M r n := by
      simpa [newtonRealPhase] using hR ((n : ℝ) - (M : ℝ))
    have hSn : S.eval (n : ℝ) = newtonRealPhase d M s n := by
      simpa [newtonRealPhase] using hS ((n : ℝ) - (M : ℝ))
    rw [Polynomial.eval_add, hRn, hSn]
  rw [hphase]
  exact residueClassTotalVariation_rational_add_binomial_le d q M r s H B hq hH hB hr hs

/-- Manifest-facing `lu:binomial-tv`: the finite ordered variation of
the original smooth polynomial phase, together with the exact residue
bound after adding any rational Newton-coordinate polynomial. -/
theorem binomialPhaseVariation
    (d : ℕ) (M : ℤ) (S : Polynomial ℝ) (s : ℕ → ℝ) (H B : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hS : ∀ t : ℝ, S.eval ((M : ℝ) + t) =
      ∑ j ∈ Finset.range (d + 1), s j * (newtonBinomialPolynomial j).eval t)
    (hs : ∀ j, 1 ≤ j → j ≤ d → |s j| ≤ B / H ^ j) :
    (∀ (P : Finset ℤ),
      (∀ n ∈ P, (M : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (M : ℝ) + H) →
        finiteOrderedTotalVariation P (fun n : ℤ => unitFrequencyPhase (S.eval n)) ≤
          1 + 2 * Real.pi * B * binomialVariationConstant d) ∧
    (∀ (q : ℕ) (R : Polynomial ℝ) (r : ℕ → ℝ), 1 ≤ q →
      (∀ t : ℝ, R.eval ((M : ℝ) + t) =
        ∑ j ∈ Finset.range (d + 1), r j * (newtonBinomialPolynomial j).eval t) →
      (∀ j, 1 ≤ j → j ≤ d → ∃ k : ℤ, (q : ℝ) * r j = (k : ℝ)) →
      ∃ hperiod : 0 < q * d.factorial,
        residueClassTotalVariation (logPhaseIntegerInterval (M : ℝ) H)
            (fun n : ℤ => unitFrequencyPhase ((R + S).eval n))
            (q * d.factorial) hperiod ≤
          ENNReal.ofReal ((q * d.factorial : ℕ) *
            (1 + 2 * Real.pi * B * binomialVariationConstant d))) := by
  constructor
  · exact finiteOrderedTotalVariation_polynomial_binomial_le d M S s H B hH hB hS hs
  · intro q R r hq hR hr
    exact residueClassTotalVariation_polynomial_rational_add_binomial_le
      d q M R S r s H B hq hH hB hR hS hr hs

end

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.abs_newtonBinomialPolynomial_derivative_le
#print axioms FractionalPrimes.Literature.Uniformity.abs_deriv_newtonRealPhase_le
#print axioms FractionalPrimes.Literature.Uniformity.orderedTotalVariation_binomialComplexPhase_le
#print axioms FractionalPrimes.Literature.Uniformity.residueClassTotalVariation_polynomial_rational_add_binomial_le
#print axioms FractionalPrimes.Literature.Uniformity.binomialPhaseVariation
