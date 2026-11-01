module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import FractionalPrimes.Literature.Analytic.ReciprocalStripConstant
public import FractionalPrimes.Literature.Reciprocal.NormalizedDirichletFamilyInnerLog
public import FractionalPrimes.Literature.Reciprocal.PrincipalReciprocalExtension
@[expose] public section

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- The elementary principal-factor estimate used to pass from the regularized
principal function to its reciprocal bound. -/
theorem reciprocalStrip_fraction_norm_le_one {s : ℂ} (hs : 0 < s.re) :
    ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  have hden0 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hplus : ‖s + 1‖ ^ 2 = (s.re + 1) ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      add_zero]
    ring
  have hminus : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      sub_zero]
    ring
  have hsq : ‖s + 1‖ ^ 2 - ‖s - 1‖ ^ 2 = 4 * s.re := by
    rw [hplus, hminus]
    ring
  have hden : ‖s - 1‖ ≤ ‖s + 1‖ := by
    nlinarith [norm_nonneg (s + 1), norm_nonneg (s - 1), hs]
  calc
    ‖(s - 1) / (s + 1)‖ = ‖s - 1‖ / ‖s + 1‖ := norm_div (s - 1) (s + 1)
    _ ≤ 1 := (div_le_one (norm_pos_iff.mpr hden0)).2 hden

noncomputable def reciprocalStripMajorant (q : ℕ) (t : ℝ) : ℝ :=
  600 * (1 + Real.log (4 * (q : ℝ) * (|t| + 4))) ^
    FractionalPrimes.Literature.Analytic.explicitLogarithmTheta

private theorem reciprocalStrip_bounds_at
    (hZFR : fixedHalfPlaneProperty)
    {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (χ : _root_.DirichletCharacter ℂ q) (σ t : ℝ)
    (hσlo : (63 / 64 : ℝ) ≤ σ) (hσhi : σ ≤ 3 / 2) :
    ‖(normalizedDirichletFamily χ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
      Real.exp (reciprocalStripMajorant q t) ∧
    ‖deriv (normalizedDirichletFamily χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        normalizedDirichletFamily χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      32 * reciprocalStripMajorant q t := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  let c : ℂ := 2 + (t : ℂ) * Complex.I
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have htR : (4 : ℝ) ≤ |t| + 4 := by nlinarith [abs_nonneg t]
  have harg : (1 : ℝ) ≤ 4 * (q : ℝ) * (|t| + 4) := by
    calc
      (1 : ℝ) ≤ 16 := by norm_num
      _ = 4 * (1 : ℝ) * 4 := by norm_num
      _ ≤ 4 * (q : ℝ) * (|t| + 4) := by gcongr
  have hM : 0 ≤ Real.log (4 * (q : ℝ) * (|t| + 4)) := Real.log_nonneg harg
  have hgeometry := FractionalPrimes.Literature.Analytic.reciprocalStrip_point_mem_closedBall
    (σ := σ) (t := t) hσlo hσhi
  have hsreal : s.re = σ := by simp [s]
  have hspos : 0 < s.re := by rw [hsreal]; linarith
  obtain ⟨hHanalytic, hHne, hHbound, hinner⟩ :=
    normalizedDirichletFamily_spec hZFR hq χ t
  have hHboundExp : ∀ z ∈ Metric.ball c (35 / 32 : ℝ),
      ‖normalizedDirichletFamily χ z‖ ≤
        Real.exp (Real.log (4 * (q : ℝ) * (|t| + 4))) := by
    intro z hz
    have hexp : Real.exp (Real.log (4 * (q : ℝ) * (|t| + 4))) =
        4 * (q : ℝ) * (|t| + 4) :=
      Real.exp_log (by linarith [harg])
    rw [hexp]
    exact hHbound z hz
  obtain ⟨g₀, hg₀, hg₀exp, hg₀bound⟩ := hinner
  have hclosedU : Metric.closedBall c (1 / 2 : ℝ) ⊆
      Metric.ball c (17 / 32 : ℝ) := by
    exact Metric.closedBall_subset_ball (by norm_num)
  have hg₀bound7 : ∀ z ∈ Metric.closedBall c (1 / 2 : ℝ), ‖g₀ z‖ ≤ 7 := by
    intro z hz
    exact (hg₀bound z hz).trans (by norm_num)
  have hradii := FractionalPrimes.Literature.Analytic.explicitLogarithmRadii
    hM hHanalytic hHne hHboundExp Metric.isOpen_ball hclosedU hg₀ hg₀exp hg₀bound7
  obtain ⟨_, _, _, _, _, _, _hGbound, hRecip, hDeriv⟩ := hradii
  have hsclosed65 : s ∈ Metric.closedBall c (65 / 64 : ℝ) := by
    simpa [s, c] using hgeometry
  have hsball : s ∈ Metric.ball c (35 / 32 : ℝ) :=
    (Metric.closedBall_subset_ball (by norm_num :
      (65 / 64 : ℝ) < 35 / 32)) hsclosed65
  have hsclosed67 : s ∈ Metric.closedBall c (67 / 64 : ℝ) := by
    exact (Metric.closedBall_subset_closedBall (by norm_num :
      (65 / 64 : ℝ) ≤ 67 / 64)) (by simpa [s, c] using hgeometry)
  have hC_le : FractionalPrimes.Literature.Analytic.explicitLogarithmConstant
      (Real.log (4 * (q : ℝ) * (|t| + 4))) ≤ reciprocalStripMajorant q t := by
    simpa [reciprocalStripMajorant] using
      FractionalPrimes.Literature.Analytic.explicitLogarithmConstant_le_reciprocalStripMajorant hM
  have hrecip : ‖(normalizedDirichletFamily χ s)⁻¹‖ ≤
      Real.exp (reciprocalStripMajorant q t) := by
    have hbase := hRecip s hsclosed67
    calc
      ‖(normalizedDirichletFamily χ s)⁻¹‖ = ‖normalizedDirichletFamily χ s‖⁻¹ := by
        simp [norm_inv]
      _ ≤ Real.exp (FractionalPrimes.Literature.Analytic.explicitLogarithmConstant
          (Real.log (4 * (q : ℝ) * (|t| + 4)))) := by
        simpa [s, c] using hbase
      _ ≤ Real.exp (reciprocalStripMajorant q t) := Real.exp_le_exp.mpr hC_le
  have hderiv : ‖deriv (normalizedDirichletFamily χ) s /
      normalizedDirichletFamily χ s‖ ≤ 32 * reciprocalStripMajorant q t := by
    have hbase := hDeriv s hsclosed65
    calc
      ‖deriv (normalizedDirichletFamily χ) s / normalizedDirichletFamily χ s‖ ≤
          32 * FractionalPrimes.Literature.Analytic.explicitLogarithmConstant
            (Real.log (4 * (q : ℝ) * (|t| + 4))) := by
        simpa [s, c] using hbase
      _ ≤ 32 * reciprocalStripMajorant q t :=
        mul_le_mul_of_nonneg_left hC_le (by norm_num)
  exact ⟨by simpa [s] using hrecip, by simpa [s] using hderiv⟩

/-- The complete conditional reciprocal-strip package `lrc:reciprocal-strip`.
It retains the approved `ZFR_{7/8}` premise, exact strip endpoints and majorant,
and the principal removable reciprocal at `s=1`. -/
theorem reciprocalStripBound (hZFR : fixedHalfPlaneProperty) :
    0 < FractionalPrimes.Literature.Analytic.explicitLogarithmTheta ∧
    FractionalPrimes.Literature.Analytic.explicitLogarithmTheta < 1 ∧
    (∀ {q : ℕ} [NeZero q] (_hq : 1 ≤ q)
      (χ : _root_.DirichletCharacter ℂ q) (σ t : ℝ)
      (_hσlo : (63 / 64 : ℝ) ≤ σ) (_hσhi : σ ≤ 3 / 2),
      ‖(normalizedDirichletFamily χ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
        Real.exp (reciprocalStripMajorant q t) ∧
      ‖deriv (normalizedDirichletFamily χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          normalizedDirichletFamily χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        32 * reciprocalStripMajorant q t) ∧
    AnalyticAt ℂ continuedDirichletPrincipalReciprocal 1 ∧
    (∀ {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1),
      continuedDirichletPrincipalReciprocal s =
        (continuedDirichletZ s hs hs1)⁻¹) ∧
    (∀ {q : ℕ} [NeZero q] (_hq : 1 ≤ q) (σ t : ℝ)
      (_hσlo : (63 / 64 : ℝ) ≤ σ) (_hσhi : σ ≤ 3 / 2),
      ‖continuedDirichletPrincipalReciprocal
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        Real.exp (reciprocalStripMajorant q t)) := by
  have hthetaPos :
      0 < FractionalPrimes.Literature.Analytic.explicitLogarithmTheta := by
    unfold FractionalPrimes.Literature.Analytic.explicitLogarithmTheta
    apply div_pos
    · exact Real.log_pos (by norm_num)
    · exact Real.log_pos (by norm_num)
  have hthetaLt :
      FractionalPrimes.Literature.Analytic.explicitLogarithmTheta < 1 := by
    have hden : 0 < Real.log (17 / 8 : ℝ) := Real.log_pos (by norm_num)
    have hnumlt : Real.log (67 / 32 : ℝ) < Real.log (17 / 8 : ℝ) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    unfold FractionalPrimes.Literature.Analytic.explicitLogarithmTheta
    exact (div_lt_one hden).2 hnumlt
  have hfamily :
      ∀ {q : ℕ} [NeZero q] (hq : 1 ≤ q)
        (χ : _root_.DirichletCharacter ℂ q) (σ t : ℝ)
        (hσlo : (63 / 64 : ℝ) ≤ σ) (hσhi : σ ≤ 3 / 2),
        ‖(normalizedDirichletFamily χ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
          Real.exp (reciprocalStripMajorant q t) ∧
        ‖deriv (normalizedDirichletFamily χ)
            ((σ : ℂ) + (t : ℂ) * Complex.I) /
          normalizedDirichletFamily χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          32 * reciprocalStripMajorant q t := by
    intro q inst hq χ σ t hσlo hσhi
    exact reciprocalStrip_bounds_at hZFR hq χ σ t hσlo hσhi
  have hprincipal : ∀ {q : ℕ} [NeZero q] (hq : 1 ≤ q) (σ t : ℝ)
      (hσlo : (63 / 64 : ℝ) ≤ σ) (hσhi : σ ≤ 3 / 2),
      ‖continuedDirichletPrincipalReciprocal
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        Real.exp (reciprocalStripMajorant q t) := by
    intro q inst hq σ t hσlo hσhi
    let χ₀ : _root_.DirichletCharacter ℂ q :=
      FractionalPrimes.Literature.Twisted.principalCharacter q
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    have hpt := reciprocalStrip_bounds_at hZFR hq χ₀ σ t hσlo hσhi
    have hRecipNormH0 : ‖continuedDirichletH0Total s‖⁻¹ ≤
        Real.exp (reciprocalStripMajorant q t) := by
      simpa [s, χ₀, normalizedDirichletFamily] using hpt.1
    have hRecipH0 : ‖(continuedDirichletH0Total s)⁻¹‖ ≤
        Real.exp (reciprocalStripMajorant q t) := by
      simpa using hRecipNormH0
    have hsreal : s.re = σ := by simp [s]
    have hspos : 0 < s.re := by rw [hsreal]; linarith
    have hsplus : s + 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    obtain ⟨_, hfamilyNe, _, _⟩ := normalizedDirichletFamily_spec
      hZFR hq χ₀ t
    have hsball : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (35 / 32 : ℝ) := by
      have hclosed : s ∈ Metric.closedBall
          (2 + (t : ℂ) * Complex.I) (65 / 64 : ℝ) := by
        simpa [s] using
          (FractionalPrimes.Literature.Analytic.reciprocalStrip_point_mem_closedBall
            (σ := σ) (t := t) hσlo hσhi)
      exact (Metric.closedBall_subset_ball (by norm_num :
        (65 / 64 : ℝ) < 35 / 32)) hclosed
    have hH0ne : continuedDirichletH0Total s ≠ 0 := by
      have h := hfamilyNe s (by simpa [s, χ₀, normalizedDirichletFamily] using hsball)
      simpa [χ₀, normalizedDirichletFamily] using h
    have hrepr : continuedDirichletPrincipalReciprocal s =
        ((s - 1) / (s + 1)) * (continuedDirichletH0Total s)⁻¹ := by
      unfold continuedDirichletPrincipalReciprocal
      field_simp [hsplus, hH0ne]
    calc
      ‖continuedDirichletPrincipalReciprocal s‖ =
          ‖((s - 1) / (s + 1)) * (continuedDirichletH0Total s)⁻¹‖ :=
        congrArg norm hrepr
      _ = ‖(s - 1) / (s + 1)‖ *
            ‖(continuedDirichletH0Total s)⁻¹‖ := norm_mul _ _
      _ ≤ 1 * Real.exp (reciprocalStripMajorant q t) := by
        exact mul_le_mul
          (reciprocalStrip_fraction_norm_le_one hspos) hRecipH0
          (norm_nonneg _) (by positivity)
      _ = Real.exp (reciprocalStripMajorant q t) := by ring
  exact ⟨hthetaPos, hthetaLt, hfamily,
    analyticAt_continuedDirichletPrincipalReciprocal_one,
    (fun hs hs1 => continuedDirichletPrincipalReciprocal_eq_inv_continuedDirichletZ hs hs1),
    hprincipal⟩

#print axioms reciprocalStripBound

end FractionalPrimes.Literature.Reciprocal

end
