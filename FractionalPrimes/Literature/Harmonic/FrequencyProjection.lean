module

public import FractionalPrimes.Literature.Multiplier.Data

/-!
# The inhomogeneous frequency projections from `ha:lp-def`

This file fixes the cutoff and defines the real torus symbols `s_h` in the
approved blueprint. The cutoff is obtained by rescaling the already checked
even bump `ψ`; its plateau and support are exactly the required ones. The
symbols are kept as torus functions, with their smooth real representatives
and seam behavior recorded explicitly.
-/

@[expose] public section

open Set
open scoped ContDiff FourierTransform

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.Multiplier

noncomputable section

/-- The fixed cutoff in `ha:lp-def`. Rescaling `ψ` gives plateau radius
`1/4` and support radius `3/8`, strictly inside the required `1/2`. -/
def frequencyProjectionCutoff (ξ : ℝ) : ℝ := ψ (ξ / 2)

theorem frequencyProjectionCutoff_even (ξ : ℝ) :
    frequencyProjectionCutoff (-ξ) = frequencyProjectionCutoff ξ := by
  change ψ (-ξ / 2) = ψ (ξ / 2)
  rw [show -ξ / 2 = -(ξ / 2) by ring, ψ_even]

theorem frequencyProjectionCutoff_nonneg (ξ : ℝ) :
    0 ≤ frequencyProjectionCutoff ξ := ψ_nonneg _

theorem frequencyProjectionCutoff_le_one (ξ : ℝ) :
    frequencyProjectionCutoff ξ ≤ 1 := ψ_le_one _

theorem frequencyProjectionCutoff_eq_one_of_abs_le (ξ : ℝ)
    (hξ : |ξ| ≤ 1 / 4) : frequencyProjectionCutoff ξ = 1 := by
  unfold frequencyProjectionCutoff
  apply ψ_eq_one_of_abs_le
  have hdiv : |ξ / 2| = |ξ| / 2 := by
    rw [abs_div]
    norm_num
  rw [hdiv]
  linarith

theorem frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs
    (ξ : ℝ) (hξ : 3 / 8 < |ξ|) : frequencyProjectionCutoff ξ = 0 := by
  unfold frequencyProjectionCutoff
  have hdiv : 3 / 16 < |ξ / 2| := by
    rw [abs_div]
    norm_num
    linarith
  by_contra hne
  have hmem : ξ / 2 ∈ Function.support ψ := by
    simpa [Function.mem_support] using hne
  rw [support_ψ] at hmem
  have hball := Metric.mem_ball.mp hmem
  rw [Real.dist_eq] at hball
  have habs : |ξ / 2| < 3 / 16 := by simpa using hball
  linarith

theorem frequencyProjectionCutoff_support_subset :
    Function.support frequencyProjectionCutoff ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  intro ξ hξ
  have hne : frequencyProjectionCutoff ξ ≠ 0 := by
    simpa [Function.mem_support] using hξ
  have habs : |ξ| < 1 / 2 := by
    by_contra hnot
    have hlarge : 1 / 2 ≤ |ξ| := le_of_not_gt hnot
    exact hne (frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs ξ
      (by linarith : 3 / 8 < |ξ|))
  exact abs_lt.mp habs

theorem frequencyProjectionCutoff_tsupport_subset :
    tsupport frequencyProjectionCutoff ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  have hnonzero_support :
      Function.support frequencyProjectionCutoff ⊆ Set.Icc (-(3 / 8 : ℝ)) (3 / 8) := by
    intro ξ hξ
    have hne : frequencyProjectionCutoff ξ ≠ 0 := by
      simpa [Function.mem_support] using hξ
    have habs : |ξ| ≤ 3 / 8 := by
      by_contra hnot
      exact hne (frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs ξ
        (lt_of_not_ge hnot))
    exact abs_le.mp habs
  have hclosure :
      tsupport frequencyProjectionCutoff ⊆ Set.Icc (-(3 / 8 : ℝ)) (3 / 8) := by
    rw [tsupport]
    exact closure_minimal hnonzero_support isClosed_Icc
  intro ξ hξ
  have hbound := hclosure hξ
  constructor <;> linarith [hbound.1, hbound.2]

theorem frequencyProjectionCutoff_hasCompactSupport :
    HasCompactSupport frequencyProjectionCutoff := by
  change IsCompact (tsupport frequencyProjectionCutoff)
  have hsub :
      tsupport frequencyProjectionCutoff ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro ξ hξ
    have hbound := frequencyProjectionCutoff_tsupport_subset hξ
    exact ⟨le_of_lt hbound.1, hbound.2.le⟩
  exact IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)))
    (isClosed_tsupport frequencyProjectionCutoff) hsub

theorem frequencyProjectionCutoff_contDiff :
    ContDiff ℝ (∞ : ℕ∞ω) frequencyProjectionCutoff := by
  have hscale : ContDiff ℝ (∞ : ℕ∞ω) (fun ξ : ℝ => ξ / 2) := by
    fun_prop
  change ContDiff ℝ (∞ : ℕ∞ω) (ψ ∘ fun ξ : ℝ => ξ / 2)
  exact ψ_contDiff.comp hscale

/-- The real representative of the source symbol `s_h`. -/
def frequencyProjectionSymbolRepresentative (c : ℝ) (h : ℤ) (ξ : ℝ) : ℝ :=
  if h < 0 then 0
  else if h = 0 then 1 - frequencyProjectionCutoff ξ
  else
    frequencyProjectionCutoff
        (Real.rpow 2 (((h : ℝ) - 1) * c) * ξ) -
      frequencyProjectionCutoff (Real.rpow 2 ((h : ℝ) * c) * ξ)

/-- The exact torus multiplier `s_h` from the approved definition.
`AddCircle.liftIoc` uses the equivalent endpoint representative
`(-1/2,1/2]`; the endpoint values agree by the seam theorem below. -/
def frequencyProjectionSymbol (c : ℝ) (h : ℤ) : Torus → ℝ :=
  AddCircle.liftIoc (1 : ℝ) (-(1 / 2 : ℝ))
    (frequencyProjectionSymbolRepresentative c h)

theorem frequencyProjectionSymbol_coe {c : ℝ} {h : ℤ} {ξ : ℝ}
    (hξ : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :
    frequencyProjectionSymbol c h ξ =
      frequencyProjectionSymbolRepresentative c h ξ := by
  simpa [frequencyProjectionSymbol] using
    (AddCircle.liftIoc_coe_apply
      (a := -(1 / 2 : ℝ)) (p := (1 : ℝ))
      (f := frequencyProjectionSymbolRepresentative c h) (x := ξ)
      (by exact ⟨hξ.1, by linarith [hξ.2]⟩))

theorem frequencyProjectionSymbolRepresentative_contDiff (c : ℝ) (h : ℤ) :
    ContDiff ℝ (∞ : ℕ∞ω) (frequencyProjectionSymbolRepresentative c h) := by
  have hcut : ContDiff ℝ (∞ : ℕ∞ω) frequencyProjectionCutoff :=
    frequencyProjectionCutoff_contDiff
  unfold frequencyProjectionSymbolRepresentative
  split_ifs with hneg hzero
  · exact contDiff_const
  · exact contDiff_const.sub hcut
  · exact (hcut.comp (by fun_prop)).sub (hcut.comp (by fun_prop))

/-- Away from the support of the cutoff, every representative is constant
near the seam: it is `1` for `h=0` and `0` for all other indices. -/
theorem frequencyProjectionSymbolRepresentative_eq_seamValue
    {c : ℝ} (hc : 1 < c) (h : ℤ) {ξ : ℝ} (hξ : 3 / 8 < |ξ|) :
    frequencyProjectionSymbolRepresentative c h ξ = if h = 0 then 1 else 0 := by
  by_cases hneg : h < 0
  · have hne : h ≠ 0 := by omega
    simp [frequencyProjectionSymbolRepresentative, hneg, hne]
  · by_cases hzero : h = 0
    · subst h
      simp only [frequencyProjectionSymbolRepresentative]
      rw [frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs ξ hξ]
      norm_num
    · have hpos : 1 ≤ h := by omega
      have hcast : 1 ≤ (h : ℝ) := by exact_mod_cast hpos
      have hcast0 : 0 ≤ (h : ℝ) := by linarith
      have hc0 : 0 < c := by linarith
      have hexp1 : 0 ≤ ((h : ℝ) - 1) * c :=
        mul_nonneg (sub_nonneg.mpr hcast) hc0.le
      have hexp2 : 0 ≤ (h : ℝ) * c := mul_nonneg hcast0 hc0.le
      have hscale1 : 1 ≤ Real.rpow 2 (((h : ℝ) - 1) * c) :=
        Real.one_le_rpow (by norm_num) hexp1
      have hscale2 : 1 ≤ Real.rpow 2 ((h : ℝ) * c) :=
        Real.one_le_rpow (by norm_num) hexp2
      have hscale1abs :
          1 ≤ |Real.rpow 2 (((h : ℝ) - 1) * c)| := by
        have hnonneg : 0 ≤ Real.rpow 2 (((h : ℝ) - 1) * c) :=
          Real.rpow_nonneg (by norm_num) _
        calc
          1 ≤ Real.rpow 2 (((h : ℝ) - 1) * c) := hscale1
          _ = |Real.rpow 2 (((h : ℝ) - 1) * c)| := (abs_of_nonneg hnonneg).symm
      have hscale2abs : 1 ≤ |Real.rpow 2 ((h : ℝ) * c)| := by
        have hnonneg : 0 ≤ Real.rpow 2 ((h : ℝ) * c) :=
          Real.rpow_nonneg (by norm_num) _
        calc
          1 ≤ Real.rpow 2 ((h : ℝ) * c) := hscale2
          _ = |Real.rpow 2 ((h : ℝ) * c)| := (abs_of_nonneg hnonneg).symm
      have harg1 :
          3 / 8 < |Real.rpow 2 (((h : ℝ) - 1) * c) * ξ| := by
        rw [abs_mul]
        calc
          3 / 8 < 1 * |ξ| := by simpa using hξ
          _ ≤ |Real.rpow 2 (((h : ℝ) - 1) * c)| * |ξ| :=
            mul_le_mul_of_nonneg_right hscale1abs (abs_nonneg ξ)
      have harg2 : 3 / 8 < |Real.rpow 2 ((h : ℝ) * c) * ξ| := by
        rw [abs_mul]
        calc
          3 / 8 < 1 * |ξ| := by simpa using hξ
          _ ≤ |Real.rpow 2 ((h : ℝ) * c)| * |ξ| :=
            mul_le_mul_of_nonneg_right hscale2abs (abs_nonneg ξ)
      simp only [frequencyProjectionSymbolRepresentative,
        if_neg hneg, if_neg hzero]
      rw [frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs _ harg1,
        frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs _ harg2]
      ring

/-- The endpoint representatives match; locally constant behavior there
records the smooth seam matching in this quotient presentation. -/
theorem frequencyProjectionSymbolRepresentative_seam
    {c : ℝ} (hc : 1 < c) (h : ℤ) :
    frequencyProjectionSymbolRepresentative c h (-(1 / 2 : ℝ)) =
      frequencyProjectionSymbolRepresentative c h (1 / 2) := by
  rw [frequencyProjectionSymbolRepresentative_eq_seamValue hc h (by norm_num),
    frequencyProjectionSymbolRepresentative_eq_seamValue hc h (by norm_num)]

theorem frequencyProjectionSymbol_continuous
    {c : ℝ} (hc : 1 < c) (h : ℤ) :
    Continuous (frequencyProjectionSymbol c h) := by
  apply AddCircle.liftIoc_continuous
  · have hadd : -(1 / 2 : ℝ) + 1 = (1 / 2 : ℝ) := by norm_num
    rw [hadd]
    exact frequencyProjectionSymbolRepresentative_seam hc h
  · exact (frequencyProjectionSymbolRepresentative_contDiff c h).continuous.continuousOn

/-- The Fourier-side action prescribed by `\widehat{S_h f}=s_h\widehat f`.
The sequence-space extension is handled with the square-function lemma
`ha:lp`; here the definition records the exact multiplier side. -/
def frequencyProjectionFourierSideAction (c : ℝ) (h : ℤ)
    (F : Torus → ℂ) : Torus → ℂ :=
  fun ξ => (frequencyProjectionSymbol c h ξ : ℂ) * F ξ

theorem frequencyProjectionFourierSideAction_apply
    (c : ℝ) (h : ℤ) (F : Torus → ℂ) (ξ : Torus) :
    frequencyProjectionFourierSideAction c h F ξ =
      (frequencyProjectionSymbol c h ξ : ℂ) * F ξ := rfl

end

end FractionalPrimes.Literature.Harmonic

namespace FractionalPrimes

open FractionalPrimes.Literature.Multiplier

/-- The source-index name for the torus multiplier `s_h` defined in
`ha:lp-def`. -/
noncomputable def frequencyProjection (c : ℝ) (h : ℤ) : Torus → ℝ :=
  Literature.Harmonic.frequencyProjectionSymbol c h

end FractionalPrimes

end
