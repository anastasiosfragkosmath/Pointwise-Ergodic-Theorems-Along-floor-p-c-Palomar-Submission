module

public import FractionalPrimes.Literature.Multiplier.PeriodicMultiplier
public import FractionalPrimes.Literature.Multiplier.ConjugateSymbol
public import FractionalPrimes.Literature.Multiplier.ConjugateExponent
public import FractionalPrimes.FiniteLpNorming
public import FractionalPrimes.FiniteLpDuality
public import FractionalPrimes.FiniteAdjointPairing

/-!
# Finite-output upper-exponent multiplier estimate

For `p > 2`, finite-set duality transfers the checked low-exponent estimate
for the conjugate symbol to a finite-output `p`-norm estimate for the original
multiplier. The output and test truncations remain finite throughout.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open scoped BigOperators ComplexConjugate ENNReal NNReal

noncomputable section

private noncomputable def multiplierFiniteSupportSeqLp
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (s : Finset ℤ) (f : ℤ → ℂ) :
    lp (fun _ : ℤ => ℂ) r :=
  ∑ k ∈ s, lp.single r k (f k)

private theorem multiplierFiniteSupportSeqLp_apply
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (s : Finset ℤ) (f : ℤ → ℂ) (k : ℤ) :
    multiplierFiniteSupportSeqLp r s f k = if k ∈ s then f k else 0 := by
  simp only [multiplierFiniteSupportSeqLp, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_single, Finset.sum_pi_single]

private theorem multiplierFiniteSupportSeqLp_norm_rpow
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : 0 < r.toReal)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    ‖multiplierFiniteSupportSeqLp r s f‖ ^ r.toReal =
      ∑ k ∈ s, ‖f k‖ ^ r.toReal := by
  simpa only [multiplierFiniteSupportSeqLp] using
    lp.norm_sum_single (E := fun _ : ℤ => ℂ) hr f s

private theorem multiplierFiniteSupportSeqLp_norm
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : 0 < r.toReal)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    ‖multiplierFiniteSupportSeqLp r s f‖ =
      (∑ k ∈ s, ‖f k‖ ^ r.toReal) ^ (1 / r.toReal) := by
  have hpow := multiplierFiniteSupportSeqLp_norm_rpow r hr s f
  have hnorm : 0 ≤ ‖multiplierFiniteSupportSeqLp r s f‖ := norm_nonneg _
  calc
    ‖multiplierFiniteSupportSeqLp r s f‖ =
        (‖multiplierFiniteSupportSeqLp r s f‖ ^ r.toReal) ^
          (1 / r.toReal) := by
            simpa [one_div] using
              (Real.rpow_rpow_inv hnorm (ne_of_gt hr)).symm
    _ = (∑ k ∈ s, ‖f k‖ ^ r.toReal) ^ (1 / r.toReal) := by rw [hpow]

/-- For a finite input and any finite output set, the `p`-norm of the
periodic multiplier output is bounded by the conjugate low-exponent constant
times `D` and the finite-input `p`-norm. -/
theorem TmL2_finiteOutput_pNorm_le
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hD : 0 < D)
    (hp : 2 < p) (f : ℤ →₀ ℂ) (out : Finset ℤ) :
    (((∑ k ∈ out,
        ‖TmL2 h (finiteSequenceL2 f) k‖₊ ^ p : ℝ≥0) ^ (1 / p) : ℝ≥0) : ℝ) ≤
      (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D *
        (((∑ k ∈ f.support, ‖f k‖₊ ^ p : ℝ≥0) ^ (1 / p) : ℝ≥0) : ℝ) := by
  classical
  let q : ℝ := p / (p - 1)
  let P : ℝ≥0∞ := ENNReal.ofReal p
  let Q : ℝ≥0∞ := ENNReal.ofReal q
  have hpReal : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  have hpden : 0 < p - 1 := by linarith
  have hq1 : 1 < q := by
    simpa [q] using multiplierConjugateExponent_gt_one hp
  have hq2 : q < 2 := by
    simpa [q] using multiplierConjugateExponent_lt_two hp
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hconj : p.HolderConjugate q := by
    simpa [q] using multiplierConjugateExponent_holderConjugate hp
  have hp0 : P ≠ 0 := by
    dsimp [P]
    exact ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  have hq0 : Q ≠ 0 := by
    dsimp [Q]
    exact ENNReal.ofReal_ne_zero_iff.mpr hqpos
  have hqTop : Q ≠ ∞ := by
    dsimp [Q]
    exact ENNReal.ofReal_ne_top
  have hPpos : 0 < P.toReal := by
    dsimp [P]
    rw [ENNReal.toReal_ofReal hpReal.le]
    exact hpReal
  have hQpos : 0 < Q.toReal := by
    dsimp [Q]
    rw [ENNReal.toReal_ofReal hqpos.le]
    exact hqpos
  have hPto : P.toReal = p := by
    dsimp [P]
    exact ENNReal.toReal_ofReal hpReal.le
  have hQto : Q.toReal = q := by
    dsimp [Q]
    exact ENNReal.toReal_ofReal hqpos.le
  have hPfact : 1 ≤ P := by
    change 1 ≤ ENNReal.ofReal p
    exact ENNReal.one_le_ofReal.mpr (by linarith)
  have hQfact : 1 ≤ Q := by
    change 1 ≤ ENNReal.ofReal q
    exact ENNReal.one_le_ofReal.mpr hq1.le
  letI : Fact (1 ≤ P) := ⟨hPfact⟩
  letI : Fact (1 ≤ Q) := ⟨hQfact⟩
  have hconjSeq : P.toReal.HolderConjugate Q.toReal := by
    rw [hPto, hQto]
    exact hconj
  rcases exists_finite_complex_norming_dual out
      (fun k : ℤ => TmL2 h (finiteSequenceL2 f) k) hconj with
    ⟨g, hgZeroOutside, hgMoment, hNormingPair⟩
  have hgSupport : Function.support g ⊆ (out : Set ℤ) := by
    intro k hk
    by_contra hkout
    exact (Function.mem_support.mp hk) (hgZeroOutside k hkout)
  have hgFinite : (Function.support g).Finite := out.finite_toSet.subset hgSupport
  let gFin : ℤ →₀ ℂ := Finsupp.ofSupportFinite g hgFinite
  have hgFinCoe : (gFin : ℤ → ℂ) = g := Finsupp.ofSupportFinite_coe
  have hgFinApply (k : ℤ) : gFin k = g k := congrFun hgFinCoe k
  have hgFinSupport : gFin.support ⊆ out := by
    intro k hk
    have hgnz : g k ≠ 0 := by
      have hgnzFin : gFin k ≠ 0 := Finsupp.mem_support_iff.mp hk
      rw [hgFinApply k] at hgnzFin
      exact hgnzFin
    by_contra hkout
    exact hgnz (hgZeroOutside k hkout)
  have hMomentRealOut : (∑ k ∈ out, ‖g k‖ ^ q) ≤ 1 := by
    have hMomentCast :
        ((∑ k ∈ out, ‖g k‖₊ ^ q : ℝ≥0) : ℝ) ≤ 1 := by
      exact_mod_cast hgMoment
    have hMomentEq :
        (∑ k ∈ out, ‖g k‖ ^ q) =
          ((∑ k ∈ out, ‖g k‖₊ ^ q : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [NNReal.coe_rpow, coe_nnnorm]
    rw [hMomentEq]
    exact hMomentCast
  have hMomentSupport :
      (∑ k ∈ gFin.support, ‖gFin k‖ ^ q) = (∑ k ∈ out, ‖g k‖ ^ q) := by
    calc
      (∑ k ∈ gFin.support, ‖gFin k‖ ^ q) =
          ∑ k ∈ gFin.support, ‖g k‖ ^ q := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hgFinApply k]
      _ = ∑ k ∈ out, ‖g k‖ ^ q := by
        apply Finset.sum_subset hgFinSupport
        intro k hk hknot
        have hzero : g k = 0 := by
          by_contra hne
          apply hknot
          apply Finsupp.mem_support_iff.mpr
          rw [hgFinApply k]
          exact hne
        simp [hzero, hqpos.ne']
  have hMomentReal : (∑ k ∈ gFin.support, ‖gFin k‖ ^ q) ≤ 1 :=
    hMomentSupport ▸ hMomentRealOut
  have hInputMomentNonneg : 0 ≤ ∑ k ∈ gFin.support, ‖gFin k‖ ^ q := by
    apply Finset.sum_nonneg
    intro k hk
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hInputRoot :
      (∑ k ∈ gFin.support, ‖gFin k‖ ^ q) ^ (1 / q) ≤ 1 := by
    calc
      _ ≤ 1 ^ (1 / q) :=
        Real.rpow_le_rpow hInputMomentNonneg hMomentReal (by positivity)
      _ = 1 := by simp
  have hWpos : 0 < W := by
    rw [W_eq, H₀_eq, A_eq]
    nlinarith [B_pos]
  let lowCoefficient : ℝ := 2 * W * q / (q - 1) + 4 * q / (2 - q)
  let lowConstant : ℝ := lowCoefficient ^ (1 / q)
  have hLowCoefficientNonneg : 0 ≤ lowCoefficient := by
    dsimp [lowCoefficient]
    positivity
  have hLowConstantNonneg : 0 ≤ lowConstant :=
    Real.rpow_nonneg hLowCoefficientNonneg _
  have hconstant : lowConstant =
      (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) := by
    dsimp [lowConstant, lowCoefficient, q]
    exact weakStrongInterpolation_conjugateConstant_eq hp
  rcases exists_TmL2_lp_of_finsupp
      (h := h.conjugate) (p := q) hD hq1 hq2 gFin with
    ⟨G, hG, hGnorm⟩
  have hGnormFinal :
      ‖G‖ ≤ (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D := by
    calc
      ‖G‖ ≤ lowConstant * D := by
        calc
          ‖G‖ ≤ lowConstant * D *
              (∑ k ∈ gFin.support, ‖gFin k‖ ^ q) ^ (1 / q) := by
                simpa [lowConstant, lowCoefficient] using hGnorm
          _ ≤ lowConstant * D * 1 :=
                mul_le_mul_of_nonneg_left hInputRoot
                  (mul_nonneg hLowConstantNonneg hD.le)
          _ = lowConstant * D := by simp
      _ = (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D := by
        rw [hconstant]
  have hFsequence :
      finiteIntegerSequenceL2 f.support (f : ℤ → ℂ) = finiteSequenceL2 f := by
    apply lp.ext
    funext k
    rw [finiteIntegerSequenceL2_apply, finiteSequenceL2_apply]
    by_cases hk : k ∈ f.support
    · simp [hk]
    · have hzero : f k = 0 := by
        by_contra hne
        exact hk (Finsupp.mem_support_iff.mpr hne)
      simp [hk, hzero]
  have hGsequence :
      finiteIntegerSequenceL2 out g = finiteSequenceL2 gFin := by
    apply lp.ext
    funext k
    rw [finiteIntegerSequenceL2_apply, finiteSequenceL2_apply]
    by_cases hk : k ∈ out
    · simp [hk, hgFinApply k]
    · have hzero : g k = 0 := hgZeroOutside k hk
      simp [hk, hzero, hgFinApply k]
  let Fseq : lp (fun _ : ℤ => ℂ) P :=
    multiplierFiniteSupportSeqLp P f.support (f : ℤ → ℂ)
  have hFseqNorm :
      ‖Fseq‖ =
        (((∑ k ∈ f.support, ‖f k‖₊ ^ p : ℝ≥0) ^ (1 / p) : ℝ≥0) : ℝ) := by
    rw [multiplierFiniteSupportSeqLp_norm P hPpos f.support (f : ℤ → ℂ), hPto]
    congr 1
    rw [NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [NNReal.coe_rpow, coe_nnnorm]
  have hadjoint := inner_TmL2_conjugate_adjoint h
    (finiteIntegerSequenceL2 f.support (f : ℤ → ℂ))
    (finiteIntegerSequenceL2 out g)
  rw [inner_left_finiteIntegerSequenceL2,
    inner_right_finiteIntegerSequenceL2] at hadjoint
  have hpair :
      (∑ k ∈ out, TmL2 h (finiteSequenceL2 f) k * starRingEnd ℂ (g k)) =
        ∑ k ∈ f.support, f k * starRingEnd ℂ (G k) := by
    calc
      _ = ∑ k ∈ out,
          TmL2 h (finiteIntegerSequenceL2 f.support (f : ℤ → ℂ)) k *
            starRingEnd ℂ (g k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← hFsequence]
      _ = ∑ k ∈ f.support,
          f k * starRingEnd ℂ
            (TmL2 (h.conjugate) (finiteIntegerSequenceL2 out g) k) := hadjoint
      _ = ∑ k ∈ f.support, f k * starRingEnd ℂ (G k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hGsequence, ← congrFun hG k]
  have hpairSeq :
      (∑ k ∈ out, TmL2 h (finiteSequenceL2 f) k * starRingEnd ℂ (g k)) =
        ∑ k ∈ f.support, Fseq k * starRingEnd ℂ (G k) := by
    calc
      _ = ∑ k ∈ f.support, f k * starRingEnd ℂ (G k) := hpair
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [Fseq, multiplierFiniteSupportSeqLp_apply, hk]
  have hHolder :
      ‖∑ k ∈ out,
          TmL2 h (finiteSequenceL2 f) k * starRingEnd ℂ (g k)‖ ≤
        ‖Fseq‖ * ‖G‖ := by
    rw [hpairSeq]
    exact finiteLp_pairing_le_norm hconjSeq f.support Fseq G
  have hNormingNorm :
      ‖∑ k ∈ out,
          TmL2 h (finiteSequenceL2 f) k * starRingEnd ℂ (g k)‖ =
        (((∑ k ∈ out,
          ‖TmL2 h (finiteSequenceL2 f) k‖₊ ^ p : ℝ≥0) ^ (1 / p) : ℝ≥0) : ℝ) := by
    rw [hNormingPair]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    exact NNReal.coe_nonneg _
  have hrealBound :
      (((∑ k ∈ out,
        ‖TmL2 h (finiteSequenceL2 f) k‖₊ ^ p : ℝ≥0) ^
          (1 / p) : ℝ≥0) : ℝ) ≤
        (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D *
          (((∑ k ∈ f.support,
            ‖f k‖₊ ^ p : ℝ≥0) ^ (1 / p) : ℝ≥0) : ℝ) := by
    calc
      _ = ‖∑ k ∈ out,
          TmL2 h (finiteSequenceL2 f) k * starRingEnd ℂ (g k)‖ :=
            hNormingNorm.symm
      _ ≤ ‖Fseq‖ * ‖G‖ := hHolder
      _ ≤ ‖Fseq‖ *
          ((2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D) :=
            mul_le_mul_of_nonneg_left hGnormFinal (norm_nonneg _)
      _ = _ := by rw [hFseqNorm]; ring
  exact hrealBound

/-- For `p > 2`, the periodic multiplier applied to a finite input has a full
`ℓᵖ` representative with the exact conjugate low-exponent constant. -/
theorem exists_TmL2_lp_of_finsupp_high
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hD : 0 < D)
    (hp : 2 < p) (f : ℤ →₀ ℂ) :
    ∃ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ((F : ℤ → ℂ) = fun k => TmL2 h (finiteSequenceL2 f) k) ∧
      ‖F‖ ≤
        (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D *
          (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p) := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal p
  let output : ℤ → ℂ := fun k => TmL2 h (finiteSequenceL2 f) k
  let inputRoot : ℝ :=
    (((∑ k ∈ f.support, ‖f k‖₊ ^ p : ℝ≥0) ^ (1 / p) : ℝ≥0) : ℝ)
  let rootBound : ℝ :=
    (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D * inputRoot
  have hpReal : 0 < p := by linarith
  have hp0 : P ≠ 0 := by
    dsimp [P]
    exact ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  have hPto : P.toReal = p := by
    dsimp [P]
    exact ENNReal.toReal_ofReal hpReal.le
  have hWpos : 0 < W := by
    rw [W_eq, H₀_eq, A_eq]
    nlinarith [B_pos]
  have hconstantBaseNonneg : 0 ≤ 2 * W * p + 4 * p / (p - 2) := by
    positivity
  have hinputRootNonneg : 0 ≤ inputRoot := by
    dsimp [inputRoot]
    positivity
  have hrootBoundNonneg : 0 ≤ rootBound := by
    dsimp [rootBound]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hconstantBaseNonneg _) hD.le)
      hinputRootNonneg
  have hfiniteMoment : ∀ s : Finset ℤ,
      ∑ k ∈ s, ‖output k‖ ^ p ≤ rootBound ^ p := by
    intro s
    have hsumNonneg : 0 ≤ ∑ k ∈ s, ‖output k‖ ^ p := by
      apply Finset.sum_nonneg
      intro k hk
      exact Real.rpow_nonneg (norm_nonneg _) _
    have hrootNonneg :
        0 ≤ (∑ k ∈ s, ‖output k‖ ^ p) ^ (1 / p) :=
      Real.rpow_nonneg hsumNonneg _
    have hrootCast :
        (∑ k ∈ s, ‖output k‖ ^ p) ^ (1 / p) =
          (((∑ k ∈ s, ‖output k‖₊ ^ p : ℝ≥0) ^ (1 / p) : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_rpow, NNReal.coe_sum, coe_nnnorm]
    have hroot :
        (∑ k ∈ s, ‖output k‖ ^ p) ^ (1 / p) ≤ rootBound := by
      rw [hrootCast]
      simpa [output, rootBound, inputRoot] using
        TmL2_finiteOutput_pNorm_le h hD hp f s
    have hrootPow :
        ((∑ k ∈ s, ‖output k‖ ^ p) ^ (1 / p)) ^ p ≤ rootBound ^ p :=
      Real.rpow_le_rpow hrootNonneg hroot hpReal.le
    have hrootIdentity :
        ((∑ k ∈ s, ‖output k‖ ^ p) ^ (1 / p)) ^ p =
          ∑ k ∈ s, ‖output k‖ ^ p := by
      rw [← Real.rpow_mul hsumNonneg]
      have hexp : (1 / p) * p = 1 := by field_simp [ne_of_gt hpReal]
      rw [hexp, Real.rpow_one]
    rw [hrootIdentity] at hrootPow
    exact hrootPow
  have hfinite : ∀ s : Finset ℤ,
      ∑ k ∈ s, ‖output k‖ ^ P.toReal ≤ rootBound ^ p := by
    intro s
    rw [hPto]
    exact hfiniteMoment s
  let F : lp (fun _ : ℤ => ℂ) P :=
    lpOfUniformFiniteMomentBound hp0 hpTop output
      (Real.rpow_nonneg hrootBoundNonneg _) hfinite
  have hnorm := lpOfUniformFiniteMomentBound_norm_le
    hp0 hpTop output (Real.rpow_nonneg hrootBoundNonneg _) hfinite
  have hrootIdentity : (rootBound ^ p) ^ (1 / p) = rootBound := by
    rw [← Real.rpow_mul hrootBoundNonneg]
    have hexp : p * (1 / p) = 1 := by field_simp [ne_of_gt hpReal]
    rw [hexp, Real.rpow_one]
  have hinputRoot : inputRoot =
      (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p) := by
    dsimp [inputRoot]
    simp only [NNReal.coe_rpow, NNReal.coe_sum, coe_nnnorm]
  refine ⟨F, ?_, ?_⟩
  · funext k
    exact lpOfUniformFiniteMomentBound_apply hp0 hpTop output
      (Real.rpow_nonneg hrootBoundNonneg _) hfinite k
  · rw [hPto] at hnorm
    calc
      ‖F‖ ≤ (rootBound ^ p) ^ (1 / p) := by simpa [F] using hnorm
      _ = rootBound := hrootIdentity
      _ = _ := by rw [show rootBound =
          (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D *
            inputRoot by rfl, hinputRoot]

end

end FractionalPrimes.Literature.Multiplier
