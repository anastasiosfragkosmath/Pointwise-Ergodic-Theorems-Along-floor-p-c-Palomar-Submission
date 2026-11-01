module

public import FractionalPrimes.FiniteLpNorming
public import FractionalPrimes.FiniteLpDuality
public import FractionalPrimes.GeneralDiscreteLpBridge
public import FractionalPrimes.GeneralAdjointPairing
public import FractionalPrimes.FiniteAdjointPairing
public import FractionalPrimes.FiniteSupportLpNorm

@[expose] public section

/-!
# Finite-support duality for the upper-exponent interpolation branch

This file implements only the finite-set p>2 duality step in blueprint
`lem:interpolation`.  It makes no density or full-operator extension claim.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal NNReal

noncomputable section

private noncomputable def finiteSupportSeqLp (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (s : Finset ℤ) (f : ℤ → ℂ) : lp (fun _ : ℤ => ℂ) r :=
  ∑ k ∈ s, lp.single r k (f k)

private theorem finiteSupportSeqLp_apply (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (s : Finset ℤ) (f : ℤ → ℂ) (k : ℤ) :
    finiteSupportSeqLp r s f k = if k ∈ s then f k else 0 := by
  simp only [finiteSupportSeqLp, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_single, Finset.sum_pi_single]

private theorem finiteSupportSeqLp_norm_rpow (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : 0 < r.toReal) (s : Finset ℤ) (f : ℤ → ℂ) :
    ‖finiteSupportSeqLp r s f‖ ^ r.toReal =
      ∑ k ∈ s, ‖f k‖ ^ r.toReal := by
  simpa only [finiteSupportSeqLp] using
    lp.norm_sum_single (E := fun _ : ℤ => ℂ) hr f s

private theorem finiteSupportSeqLp_norm (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : 0 < r.toReal) (s : Finset ℤ) (f : ℤ → ℂ) :
    ‖finiteSupportSeqLp r s f‖ =
      (∑ k ∈ s, ‖f k‖ ^ r.toReal) ^ (1 / r.toReal) := by
  have hpow := finiteSupportSeqLp_norm_rpow r hr s f
  have hnorm : 0 ≤ ‖finiteSupportSeqLp r s f‖ := norm_nonneg _
  calc
    ‖finiteSupportSeqLp r s f‖ =
        (‖finiteSupportSeqLp r s f‖ ^ r.toReal) ^ (1 / r.toReal) := by
          simpa [one_div] using
            (Real.rpow_rpow_inv hnorm (ne_of_gt hr)).symm
    _ = (∑ k ∈ s, ‖f k‖ ^ r.toReal) ^ (1 / r.toReal) := by rw [hpow]

/-- The exact finite-output p-moment bound follows from the p/(p-1) bound
for the adjoint.  Both the input and output are truncated to the displayed
finite sets; no density or arbitrary-input extension is asserted here. -/
theorem finiteSupportConvolutionLpBound_of_adjoint
    (K : IntegerL1Kernel) (p : ℝ) (hp : 2 < p) (C : ℝ≥0)
    (hAdj : ∀ g : Lp ℂ (ENNReal.ofReal (p / (p - 1)))
        (Measure.count : Measure ℤ),
      eLpNorm
          (integerKernelConvolution (integerKernelAdjoint K) (g : ℤ → ℂ))
          (ENNReal.ofReal (p / (p - 1))) Measure.count ≤
        (C : ℝ≥0∞) *
          eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal (p / (p - 1))) Measure.count)
    (t u : Finset ℤ) (f : ℤ → ℂ) :
    (∑ k ∈ u,
      ‖integerKernelConvolution K (fun k => if k ∈ t then f k else 0) k‖₊ ^ p) ^
        (1 / p) ≤
      C * (∑ k ∈ t, ‖f k‖₊ ^ p) ^ (1 / p) := by
  let q : ℝ := p / (p - 1)
  let P : ℝ≥0∞ := ENNReal.ofReal p
  let Q : ℝ≥0∞ := ENNReal.ofReal q
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  have hpden : 0 < p - 1 := by linarith
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos hp0 hpden
  have hq1 : 1 < q := by
    have hqeq : q = 1 + 1 / (p - 1) := by
      dsimp [q]
      field_simp
      <;> ring
    rw [hqeq]
    have : 0 < 1 / (p - 1) := one_div_pos.mpr hpden
    linarith
  have hconj : p.HolderConjugate q := by
    simpa [q, Real.conjExponent] using
      (Real.HolderConjugate.conjExponent hp1)
  have hPpos : 0 < P.toReal := by
    dsimp [P]
    rw [ENNReal.toReal_ofReal hp0.le]
    exact hp0
  have hQpos : 0 < Q.toReal := by
    dsimp [Q]
    rw [ENNReal.toReal_ofReal hqpos.le]
    exact hqpos
  have hPto : P.toReal = p := by
    dsimp [P]
    exact ENNReal.toReal_ofReal hp0.le
  have hQto : Q.toReal = q := by
    dsimp [Q]
    exact ENNReal.toReal_ofReal hqpos.le
  have hPfact : 1 ≤ P := by
    change 1 ≤ ENNReal.ofReal p
    exact ENNReal.one_le_ofReal.mpr (by linarith)
  have hQfact : 1 ≤ Q := by
    change 1 ≤ ENNReal.ofReal q
    exact ENNReal.one_le_ofReal.mpr (by linarith)
  letI : Fact (1 ≤ P) := ⟨hPfact⟩
  letI : Fact (1 ≤ Q) := ⟨hQfact⟩
  have hconjSeq : P.toReal.HolderConjugate Q.toReal := by
    rw [hPto, hQto]
    exact hconj
  rcases exists_finite_complex_norming_dual u
      (fun k => integerKernelConvolution K (fun j => if j ∈ t then f j else 0) k)
      hconj with ⟨g, hgSupport, hgMoment, hNormingPair⟩
  let Fseq := finiteSupportSeqLp P t f
  let Gseq := finiteSupportSeqLp Q u g
  let Ftrunc : ℤ → ℂ := fun k => if k ∈ t then f k else 0
  let Gtrunc : ℤ → ℂ := fun k => if k ∈ u then g k else 0
  let Gcount : Lp ℂ Q (Measure.count : Measure ℤ) :=
    generalLpToCountLp (ENNReal.ofReal_ne_zero_iff.mpr hqpos)
      ENNReal.ofReal_ne_top Gseq
  have hGseqNorm : ‖Gseq‖ ≤ 1 := by
    rw [finiteSupportSeqLp_norm Q hQpos u g, hQto]
    have hMomentReal :
        (∑ k ∈ u, ‖g k‖ ^ q) ≤ 1 := by
      have hMomentCast :
          ((∑ k ∈ u, ‖g k‖₊ ^ q : ℝ≥0) : ℝ) ≤ 1 := by
        exact_mod_cast hgMoment
      have hMomentEq :
          (∑ k ∈ u, ‖g k‖ ^ q) =
            ((∑ k ∈ u, ‖g k‖₊ ^ q : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [NNReal.coe_rpow, coe_nnnorm]
      rw [hMomentEq]
      exact hMomentCast
    calc
      (∑ k ∈ u, ‖g k‖ ^ q) ^ (1 / q) ≤ 1 ^ (1 / q) :=
        Real.rpow_le_rpow (by positivity) hMomentReal (by positivity)
      _ = 1 := by simp
  have hGcountRep (k : ℤ) : (Gcount : ℤ → ℂ) k = Gtrunc k := by
    rw [generalLpToCountLp_apply]
    simp [Gseq, Gtrunc, finiteSupportSeqLp_apply]
  have hGcountNorm :
      eLpNorm (Gcount : ℤ → ℂ) Q Measure.count ≤ 1 := by
    calc
      eLpNorm (Gcount : ℤ → ℂ) Q Measure.count = ‖Gcount‖ₑ := by
        rw [← Lp.enorm_def]
      _ = ENNReal.ofReal ‖Gcount‖ := by simp
      _ = ENNReal.ofReal ‖Gseq‖ := by
        rw [generalLpToCountLp_norm]
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hGseqNorm
      _ = 1 := by norm_num
  have hAdjBound := hAdj Gcount
  let adjOut : ℤ → ℂ :=
    integerKernelConvolution (integerKernelAdjoint K) (Gcount : ℤ → ℂ)
  have hAdjOutTop : eLpNorm adjOut Q Measure.count < ∞ := by
    have hprod :
        (C : ℝ≥0∞) * eLpNorm (Gcount : ℤ → ℂ) Q Measure.count < ∞ :=
      ENNReal.mul_lt_top ENNReal.coe_lt_top
        (lt_top_iff_ne_top.mpr (Lp.memLp Gcount).eLpNorm_ne_top)
    exact lt_of_le_of_lt hAdjBound hprod
  have hAdjOutMem : MemLp adjOut Q Measure.count := hAdjOutTop
  let AdjLp : Lp ℂ Q (Measure.count : Measure ℤ) := hAdjOutMem.toLp adjOut
  let AdjSeq := countLpToGeneralLp
    (ENNReal.ofReal_ne_zero_iff.mpr hqpos)
    ENNReal.ofReal_ne_top AdjLp
  have hAdjOutBound : eLpNorm adjOut Q Measure.count ≤ C := by
    calc
      eLpNorm adjOut Q Measure.count ≤
          (C : ℝ≥0∞) * eLpNorm (Gcount : ℤ → ℂ) Q Measure.count := hAdjBound
      _ ≤ (C : ℝ≥0∞) * 1 := by gcongr
      _ = C := by simp
  have hAdjSeqNorm : ‖AdjSeq‖ ≤ C := by
    calc
      ‖AdjSeq‖ = ‖AdjLp‖ := countLpToGeneralLp_norm _ _ AdjLp
      _ = ENNReal.toReal (eLpNorm adjOut Q Measure.count) :=
        Lp.norm_toLp adjOut hAdjOutMem
      _ ≤ ENNReal.toReal (C : ℝ≥0∞) :=
        ENNReal.toReal_mono ENNReal.coe_ne_top hAdjOutBound
      _ = C := by simp
  have hAdjSeqApply (k : ℤ) : AdjSeq k = adjOut k := by
    rw [countLpToGeneralLp_apply]
    exact (ae_count_int_iff_forall.mp (MemLp.coeFn_toLp hAdjOutMem)) k
  have hFseqNorm :
      ‖Fseq‖ =
        (((∑ k ∈ t, ‖f k‖₊ ^ p : ℝ≥0) ^ (1 / p) : ℝ≥0) : ℝ) := by
    rw [finiteSupportSeqLp_norm P hPpos t f, hPto]
    congr 1
    rw [NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [NNReal.coe_rpow, coe_nnnorm]
  let hT : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let F2 := finiteIntegerSequenceL2 t f
  let G2 := finiteIntegerSequenceL2 u g
  let T2 := integerKernelConvolutionL2 (hT := hT) K F2
  let A2 := integerKernelConvolutionL2 (hT := hT) (integerKernelAdjoint K) G2
  have hF2Rep : (F2 : ℤ → ℂ) = Ftrunc := by
    funext k
    simp [F2, Ftrunc, finiteIntegerSequenceL2_apply]
  have hG2Rep : (G2 : ℤ → ℂ) = Gtrunc := by
    funext k
    simp [G2, Gtrunc, finiteIntegerSequenceL2_apply]
  have hT2Apply (k : ℤ) : T2 k = integerKernelConvolution K Ftrunc k := by
    simpa [T2, hF2Rep] using integerKernelConvolutionL2_apply (hT := hT) K F2 k
  have hA2Apply (k : ℤ) : A2 k = integerKernelConvolution
      (integerKernelAdjoint K) Gtrunc k := by
    simpa [A2, hG2Rep] using integerKernelConvolutionL2_apply (hT := hT)
      (integerKernelAdjoint K) G2 k
  have hGtruncEq : Gtrunc = (Gcount : ℤ → ℂ) := by
    funext k
    rw [hGcountRep]
  have hA2AdjOut (k : ℤ) : A2 k = adjOut k := by
    rw [hA2Apply]
    change integerKernelConvolution (integerKernelAdjoint K) Gtrunc k =
      integerKernelConvolution (integerKernelAdjoint K) (Gcount : ℤ → ℂ) k
    rw [hGtruncEq]
  have hleft : inner ℂ G2 T2 =
      ∑ k ∈ u, T2 k * starRingEnd ℂ (g k) := by
    simpa [G2] using inner_left_finiteIntegerSequenceL2 u g T2
  have hright : inner ℂ A2 F2 =
      ∑ k ∈ t, f k * starRingEnd ℂ (A2 k) := by
    simpa [F2] using inner_right_finiteIntegerSequenceL2 A2 t f
  have hadjoint := integerKernelConvolutionL2_pairing_adjoint (hT := hT) K F2 G2
  have hpairL2 :
      (∑ k ∈ u, T2 k * starRingEnd ℂ (g k)) =
        ∑ k ∈ t, f k * starRingEnd ℂ (A2 k) := by
    calc
      _ = inner ℂ G2 T2 := hleft.symm
      _ = inner ℂ A2 F2 := hadjoint
      _ = _ := hright
  have hpairing :
      (∑ k ∈ u,
        integerKernelConvolution K Ftrunc k * starRingEnd ℂ (g k)) =
      ∑ k ∈ t, f k * starRingEnd ℂ (adjOut k) := by
    calc
      _ = ∑ k ∈ u, T2 k * starRingEnd ℂ (g k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hT2Apply k]
      _ = _ := hpairL2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hA2AdjOut k]
  have hpairSeq :
      (∑ k ∈ u,
        integerKernelConvolution K Ftrunc k * starRingEnd ℂ (g k)) =
      ∑ k ∈ t, Fseq k * starRingEnd ℂ (AdjSeq k) := by
    rw [hpairing]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← hAdjSeqApply k]
    simp [Fseq, finiteSupportSeqLp_apply, hk]
  have hHolder :
      ‖∑ k ∈ u,
        integerKernelConvolution K Ftrunc k * starRingEnd ℂ (g k)‖ ≤
          ‖Fseq‖ * ‖AdjSeq‖ := by
    rw [hpairSeq]
    exact finiteLp_pairing_le_norm hconjSeq t Fseq AdjSeq
  have hNormingNorm :
      ‖∑ k ∈ u,
        integerKernelConvolution K Ftrunc k * starRingEnd ℂ (g k)‖ =
          (((∑ k ∈ u,
            ‖integerKernelConvolution K Ftrunc k‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℝ) := by
    rw [hNormingPair]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    exact NNReal.coe_nonneg _
  have hrealBound :
      (((∑ k ∈ u,
        ‖integerKernelConvolution K Ftrunc k‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℝ) ≤
        C * (((∑ k ∈ t, ‖f k‖₊ ^ p : ℝ≥0) ^ (1 / p) : ℝ≥0) : ℝ) := by
    calc
      _ = ‖∑ k ∈ u,
          integerKernelConvolution K Ftrunc k * starRingEnd ℂ (g k)‖ :=
            hNormingNorm.symm
      _ ≤ ‖Fseq‖ * ‖AdjSeq‖ := hHolder
      _ ≤ ‖Fseq‖ * C := mul_le_mul_of_nonneg_left hAdjSeqNorm (norm_nonneg _)
      _ = _ := by rw [hFseqNorm]; ring
  exact NNReal.coe_le_coe.mp (by
    simpa [Ftrunc, NNReal.coe_mul] using hrealBound)

end

end FractionalPrimes
