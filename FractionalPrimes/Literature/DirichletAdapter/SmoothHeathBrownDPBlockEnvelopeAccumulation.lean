module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownDPSourceComponentTransfer
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupMellinBlockEnvelope
public import FractionalPrimes.Literature.DirichletAdapter.DPLogarithmicAbsorption
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWDyadicWindowIdentity
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownMobiusSelectedGroupSourceBridge
public import Mathlib.Tactic
@[expose] public section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! Exact finite residue and block accumulation for the source DP envelope.
The actual three-group polynomial identity is an explicit input here; this
module handles the Mellin/kernel and finite-sum bookkeeping without changing
the source residue set or shift variable. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open MeasureTheory
open scoped BigOperators

/-- Exact dyadic decomposition of one source group convolution Mellin sum.
The source coefficient, residue restriction, real half-open windows, and
frequency shift are unchanged. The block polynomial on the right is the
actual residue-restricted Heath--Brown group block used by the trilinear
adapter. -/
theorem smoothHeathBrownResidueGroupBroadWindow_sum_eq_dyadicBlockPolynomials
    {X z : ℝ} {K : ℕ}
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (M u t : ℝ) (k : ℕ) (hM : 0 < M) :
    (∑ n ∈ factorExtractionRealInterval M ((2 : ℝ) ^ k * M),
      (∏ i : I,
        smoothHeathBrownResidueFactorArithmeticFunction (z := z)
          q (residue i.val) (fs i.val)) n *
        (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
          Complex.I * ((t - u : ℝ) : ℂ))) =
      ∑ j ∈ Finset.range k,
        factorPolynomial ((2 : ℝ) ^ j * M)
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) fs I q residue ((2 : ℝ) ^ j * M) u) t := by
  classical
  rw [factorExtractionRealInterval_sum_eq_sum_dyadicWindows hM.le k
    (fun n =>
      (∏ i : I,
        smoothHeathBrownResidueFactorArithmeticFunction (z := z)
          q (residue i.val) (fs i.val)) n *
        (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
          Complex.I * ((t - u : ℝ) : ℂ)))]
  apply Finset.sum_congr rfl
  intro j hj
  have hL : 0 < (2 : ℝ) ^ j * M := mul_pos (by positivity) hM
  exact (smoothHeathBrownResidueGroupBlock_factorPolynomial_eq_sourceInterval
    (z := z) fs I q residue ((2 : ℝ) ^ j * M) u t hL).symm

/-- If the support of every factor tuple lies in a fixed broad real window,
the exact residue-restricted group convolution Mellin sum factors into the
product of the individual residue-restricted factor Mellin sums. The window
hypothesis is explicit, so the source open-left, closed-right convention is
preserved. -/
theorem smoothHeathBrownResidueGroupBroadWindow_sum_eq_factorMellinProduct
    {X z : ℝ} {K : ℕ}
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (M U : ℝ) (s : ℂ) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hwindow : ∀ m ∈ Fintype.piFinset
        (fun i : I => smoothHeathBrownFactorFiniteSupport (fs i.val)),
      M < (∏ i : I, (m i : ℝ)) ∧ (∏ i : I, (m i : ℝ)) ≤ U) :
    (∑ n ∈ factorExtractionRealInterval M U,
      (∏ i : I,
        smoothHeathBrownResidueFactorArithmeticFunction (z := z)
          q (residue i.val) (fs i.val)) n * (n : ℂ) ^ s) =
      ∏ i : I,
        ∑ n ∈ smoothHeathBrownFactorFiniteSupport (fs i.val),
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (fs i.val) n * (n : ℂ) ^ s := by
  classical
  let S : Fin K → Finset ℕ := fun i => smoothHeathBrownFactorFiniteSupport (fs i)
  let f : Fin K → ArithmeticFunction ℂ := fun i =>
    smoothHeathBrownResidueFactorArithmeticFunction (z := z) q (residue i) (fs i)
  have hf : ∀ i ∈ I, ∀ n, n ∉ S i → f i n = 0 := by
    intro i hi n hn
    exact smoothHeathBrownResidueFactorArithmeticFunction_eq_zero_of_not_mem
      (z := z) q (residue i) (fs i) hn
  have hpos : ∀ i ∈ I, ∀ n, n ∈ S i → 0 < n := by
    intro i hi n hn
    exact smoothHeathBrownFactorFiniteSupport_pos (fs i) hn
  have htuple := arithmeticFunctionSubsetProduct_intervalMellinSum_eq_tupleSum
    I f S hf hpos M U hM hU s
  have htuple' :
      (∑ n ∈ factorExtractionRealInterval M U,
        (∏ i : I, f i.val) n * (n : ℂ) ^ s) =
        ∑ m ∈ (Fintype.piFinset (fun i : I => S i.val)).filter
            (fun m => M < (∏ i : I, (m i : ℝ)) ∧
              (∏ i : I, (m i : ℝ)) ≤ U),
          ∏ i : I, f i.val (m i) * (m i : ℂ) ^ s := by
    simpa only [Nat.cast_prod] using htuple
  have hfilter :
      (Fintype.piFinset (fun i : I => S i.val)).filter
          (fun m => M < (∏ i : I, (m i : ℝ)) ∧
            (∏ i : I, (m i : ℝ)) ≤ U) =
        Fintype.piFinset (fun i : I => S i.val) := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    exact hwindow m (by simpa [S] using hm)
  rw [htuple', hfilter]
  simpa [S, f] using
    (Finset.prod_univ_sum
      (fun i : I => smoothHeathBrownFactorFiniteSupport (fs i.val))
      (fun i n =>
        smoothHeathBrownResidueFactorArithmeticFunction (z := z)
          q (residue i.val) (fs i.val) n * (n : ℂ) ^ s)).symm

private theorem smoothHeathBrownNatResidue_iff_intModEq
    {n q : ℕ} (b : Fin q) :
    n % q = b.val ↔ Int.ModEq (q : ℤ) (n : ℤ) (b.val : ℤ) := by
  constructor
  · intro h
    apply (Int.natCast_modEq_iff).2
    change n % q = b.val % q
    simpa [Nat.mod_eq_of_lt b.isLt] using h
  · intro h
    have h' := (Int.natCast_modEq_iff).1 h
    change n % q = b.val % q at h'
    simpa [Nat.mod_eq_of_lt b.isLt] using h'

private theorem smoothHeathBrownNormalizedMellinTerm_eq
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    mellinDirichletMonomial n t =
      mellinSeparationMonomial ⟨n, hn⟩
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
  unfold mellinDirichletMonomial mellinSeparationMonomial
  congr 1
  push_cast
  ring

/-- One original source factor's normalized residue Mellin polynomial is
exactly the corresponding finite Mellin-separation factor polynomial. The
normalization, natural residue selector, and source phase agree without
changing the factor's support window. -/
theorem smoothHeathBrownResidueFactorFiniteSupport_mellinPolynomial_eq
    {X z : ℝ} {q : ℕ} (hq : 0 < q)
    (f : SmoothHeathBrownFactor X) (b : Fin q) (t : ℝ) :
    (∑ n ∈ smoothHeathBrownFactorFiniteSupport f,
      smoothHeathBrownResidueFactorArithmeticFunction (z := z) q b.val f n *
        mellinDirichletMonomial n t) =
      mellinSeparationFactorPolynomial
        (fun _ : Fin 1 => smoothHeathBrownNormalizedMellinFactor (z := z) f)
        q 0 b (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
  classical
  let α := smoothHeathBrownNormalizedMellinFactor (z := z) f
  let S := smoothHeathBrownFactorFiniteSupport f
  let src : ℕ → ℂ := fun n =>
    smoothHeathBrownResidueFactorArithmeticFunction (z := z) q b.val f n *
      mellinDirichletMonomial n t
  let P : Finset PositiveInteger := α.support.filter
    (fun p => Int.ModEq (q : ℤ) (p.1 : ℤ) (b.val : ℤ))
  let Q : Finset ℕ := S.filter (fun n => src n ≠ 0)
  let dst : PositiveInteger → ℂ := fun p =>
    α p * mellinSeparationMonomial p
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))
  have hleft : (∑ n ∈ S, src n) = ∑ n ∈ Q, src n := by
    rw [Finset.sum_filter_ne_zero]
  have hbij : (∑ p ∈ P, dst p) = ∑ n ∈ Q, src n := by
    apply Finset.sum_bij (fun p _ => p.1)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpα, hpres⟩
      have hcoeff :
          smoothHeathBrownNormalizedFactorCoefficient (z := z) f p.1 ≠ 0 := by
        intro hz
        apply Finsupp.mem_support_iff.mp hpα
        simp [α, smoothHeathBrownNormalizedMellinFactor_apply, hz]
      have hmemS := smoothHeathBrownNormalizedFactorCoefficient_support f hcoeff
      have hresNat := (smoothHeathBrownNatResidue_iff_intModEq b).2 hpres
      have hsrcne : src p.1 ≠ 0 := by
        have hfactor :
            smoothHeathBrownResidueFactorArithmeticFunction (z := z) q b.val f p.1 =
              (smoothHeathBrownNormalizedFactorCoefficient (z := z) f p.1 : ℂ) := by
          change (if p.1 % q = b.val then _ else 0) = _
          rw [if_pos hresNat]
        have hcoeffC :
            (smoothHeathBrownNormalizedFactorCoefficient (z := z) f p.1 : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr hcoeff
        have hphase : mellinDirichletMonomial p.1 t ≠ 0 := by
          unfold mellinDirichletMonomial
          exact Complex.exp_ne_zero _
        change (smoothHeathBrownResidueFactorArithmeticFunction (z := z)
          q b.val f p.1 * mellinDirichletMonomial p.1 t) ≠ 0
        rw [hfactor]
        exact mul_ne_zero hcoeffC hphase
      exact Finset.mem_filter.mpr ⟨hmemS, hsrcne⟩
    · intro p hp p' hp' hval
      exact Subtype.ext hval
    · intro n hnQ
      rw [Finset.mem_filter] at hnQ
      rcases hnQ with ⟨hnS, hsrcne⟩
      have hnpos := smoothHeathBrownFactorFiniteSupport_pos f hnS
      have hresNat : n % q = b.val := by
        by_contra hnot
        apply hsrcne
        simp [src, smoothHeathBrownResidueFactorArithmeticFunction, hnot]
      have hcoeff :
          smoothHeathBrownNormalizedFactorCoefficient (z := z) f n ≠ 0 := by
        intro hz
        apply hsrcne
        simp [src, smoothHeathBrownResidueFactorArithmeticFunction,
          hresNat, hz]
      let p : PositiveInteger := ⟨n, hnpos⟩
      have hpα : p ∈ α.support := by
        rw [Finsupp.mem_support_iff]
        change α p ≠ 0
        simp [α, smoothHeathBrownNormalizedMellinFactor_apply, p, hcoeff]
      have hpres : Int.ModEq (q : ℤ) (p.1 : ℤ) (b.val : ℤ) :=
        (smoothHeathBrownNatResidue_iff_intModEq b).1 hresNat
      refine ⟨p, Finset.mem_filter.mpr ⟨hpα, hpres⟩, rfl⟩
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpα, hpres⟩
      have hresNat := (smoothHeathBrownNatResidue_iff_intModEq b).2 hpres
      have hcoeff :
          smoothHeathBrownResidueFactorArithmeticFunction (z := z) q b.val f p.1 =
            (smoothHeathBrownNormalizedFactorCoefficient (z := z) f p.1 : ℂ) := by
        change (if p.1 % q = b.val then _ else 0) = _
        rw [if_pos hresNat]
      have hphase := smoothHeathBrownNormalizedMellinTerm_eq p.1 p.2 t
      simp [src, dst, α, hcoeff, hphase]
  change (∑ n ∈ S, src n) = _
  calc
    (∑ n ∈ S, src n) = ∑ n ∈ Q, src n := hleft
    _ = ∑ p ∈ P, dst p := hbij.symm
    _ = _ := by
      simp [P, dst, α, mellinSeparationFactorPolynomial,
        smoothHeathBrownNormalizedMellinFactor_apply]

private theorem smoothHeathBrownMellinSeparationMonomial_eq_cpow
    (p : PositiveInteger) (s : ℂ) :
    mellinSeparationMonomial p s = (p.1 : ℂ) ^ (-s) := by
  have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.2
  calc
    Complex.exp (-s * (Real.log (p.1 : ℝ) : ℂ)) =
        Complex.exp ((-s) * (Real.log (p.1 : ℝ) : ℂ)) := by ring_nf
    _ = (p.1 : ℂ) ^ (-s) := by
      symm
      rw [show (p.1 : ℂ) = ((p.1 : ℝ) : ℂ) by norm_cast]
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
        Complex.ofReal_log hp.le]
      congr 1
      ring

/-- The source cpow Mellin phase of one normalized residue factor is the
same finite Mellin-separation polynomial as its real-log definition. -/
theorem smoothHeathBrownResidueFactorFiniteSupport_cpowSum_eq_mellinPolynomial
    {X z : ℝ} {q : ℕ} (hq : 0 < q)
    (f : SmoothHeathBrownFactor X) (b : Fin q) (t : ℝ) :
    (∑ n ∈ smoothHeathBrownFactorFiniteSupport f,
      smoothHeathBrownResidueFactorArithmeticFunction (z := z) q b.val f n *
        (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))) =
      mellinSeparationFactorPolynomial
        (fun _ : Fin 1 => smoothHeathBrownNormalizedMellinFactor (z := z) f)
        q 0 b (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
  classical
  calc
    (∑ n ∈ smoothHeathBrownFactorFiniteSupport f,
        smoothHeathBrownResidueFactorArithmeticFunction (z := z) q b.val f n *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))) =
      ∑ n ∈ smoothHeathBrownFactorFiniteSupport f,
        smoothHeathBrownResidueFactorArithmeticFunction (z := z) q b.val f n *
          mellinDirichletMonomial n t := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnpos := smoothHeathBrownFactorFiniteSupport_pos f hn
            have hphase := smoothHeathBrownNormalizedMellinTerm_eq n hnpos t
            have hcpow : (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) =
                mellinDirichletMonomial n t := by
              let p : PositiveInteger := ⟨n, hnpos⟩
              have hs : -((((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))) =
                  (-(1 / 2 : ℂ)) - Complex.I * (t : ℂ) := by
                have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
                rw [hhalf]
                ring
              calc
                (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) =
                    (n : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)))) := by
                      rw [hs]
                _ = mellinSeparationMonomial p
                    (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
                      symm
                      exact smoothHeathBrownMellinSeparationMonomial_eq_cpow p _
                _ = mellinDirichletMonomial n t := by
                      simpa [p] using hphase.symm
            rw [hcpow]
    _ = _ := smoothHeathBrownResidueFactorFiniteSupport_mellinPolynomial_eq
      hq f b t

/-- With the source tuple-product window fixed, the original residue-group
Mellin sum is exactly the finite product of its normalized Mellin-separation
factor polynomials. The residue selector remains the source natural
remainder, represented in `Fin q` only at the polynomial interface. -/
theorem smoothHeathBrownResidueGroupBroadWindow_sum_eq_factorPolynomials
    {X z : ℝ} {K : ℕ}
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (hq : 0 < q)
    (residue : Fin K → ℕ) (hresidue : ∀ i ∈ I, residue i < q)
    (M U t u : ℝ) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hwindow : ∀ m ∈ Fintype.piFinset
        (fun i : I => smoothHeathBrownFactorFiniteSupport (fs i.val)),
      M < (∏ i : I, (m i : ℝ)) ∧ (∏ i : I, (m i : ℝ)) ≤ U) :
    (∑ n ∈ factorExtractionRealInterval M U,
      (∏ i : I,
        smoothHeathBrownResidueFactorArithmeticFunction (z := z)
          q (residue i.val) (fs i.val)) n *
        (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
          Complex.I * ((t - u : ℝ) : ℂ))) =
      ∏ i : I,
        mellinSeparationFactorPolynomial
          (fun _ : Fin 1 =>
            smoothHeathBrownNormalizedMellinFactor (z := z) (fs i.val))
          q 0 ⟨residue i.val, hresidue i.val i.property⟩
          (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) := by
  classical
  have hgroup := smoothHeathBrownResidueGroupBroadWindow_sum_eq_factorMellinProduct
    (z := z) fs I q residue M U
    ((-(1 / 2 : ℂ)) - Complex.I * ((t - u : ℝ) : ℂ)) hM hU hwindow
  calc
    (∑ n ∈ factorExtractionRealInterval M U,
        (∏ i : I,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (fs i.val)) n *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
            Complex.I * ((t - u : ℝ) : ℂ))) =
        ∏ i : I,
          ∑ n ∈ smoothHeathBrownFactorFiniteSupport (fs i.val),
            smoothHeathBrownResidueFactorArithmeticFunction (z := z)
              q (residue i.val) (fs i.val) n *
              (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
                Complex.I * ((t - u : ℝ) : ℂ)) := hgroup
    _ = ∏ i : I,
          mellinSeparationFactorPolynomial
            (fun _ : Fin 1 =>
              smoothHeathBrownNormalizedMellinFactor (z := z) (fs i.val))
            q 0 ⟨residue i.val, hresidue i.val i.property⟩
            (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact smoothHeathBrownResidueFactorFiniteSupport_cpowSum_eq_mellinPolynomial
        hq (fs i.val) ⟨residue i.val, hresidue i.val i.property⟩ (t - u)

/-- Every tuple of source-supported factors in a nonempty group has its
product in the exact broad interval `(S/2^|I|, 2^|I| S]`. This supplies the
support window used before the group sum is split into its source dyadic
blocks. -/
theorem smoothHeathBrownDPGroupTupleSupportWindow
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fs.length)) (hI : I.Nonempty) :
    ∀ m ∈ Fintype.piFinset
        (fun i : I => smoothHeathBrownFactorFiniteSupport (fs.get i.val)),
      smoothHeathBrownSubgroupScaleProduct fs I / (2 : ℝ) ^ I.card <
          ∏ i : I, (m i : ℝ) ∧
        (∏ i : I, (m i : ℝ)) ≤
          (2 : ℝ) ^ I.card * smoothHeathBrownSubgroupScaleProduct fs I := by
  classical
  let N : I → ℝ := fun i => smoothHeathBrownFactorScale (fs.get i.val)
  let P : ℝ := ∏ i : I, N i
  have hP : P = smoothHeathBrownSubgroupScaleProduct fs I := by
    change (∏ i : I, smoothHeathBrownFactorScale (fs.get i.val)) =
      ∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)
    exact Finset.prod_coe_sort I (fun i => smoothHeathBrownFactorScale (fs.get i))
  have hNge (i : I) : 1 ≤ N i := by
    exact smoothHeathBrownFactorScale_ge_one (fs.get i.val)
  have hNpos (i : I) : 0 < N i := lt_of_lt_of_le (by norm_num) (hNge i)
  have hNnonneg (i : I) : 0 ≤ N i := le_trans (by norm_num) (hNge i)
  have hsubtypeNonempty : (Finset.univ : Finset I).Nonempty := by
    rcases hI with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩, Finset.mem_univ _⟩
  intro m hm
  have hmass (i : I) :
      m i ∈ smoothFactorMassWindow (N i) := by
    rw [← smoothHeathBrownFactorFiniteSupport_eq_massWindow]
    exact Fintype.mem_piFinset.mp hm i
  have hwindow (i : I) :
      N i / 2 < (m i : ℝ) ∧ (m i : ℝ) ≤ 2 * N i := by
    exact (mem_smoothFactorMassWindow (hNnonneg i) (m i)).mp (hmass i)
  have hprodLower :
      (∏ i : I, N i / 2) < ∏ i : I, (m i : ℝ) := by
    apply Finset.prod_lt_prod_of_nonempty₀
    · intro i hi
      exact div_pos (hNpos i) (by norm_num)
    · intro i hi
      exact (hwindow i).1
    · exact hsubtypeNonempty
  have hprodLowerEq :
      (∏ i : I, N i / 2) = P / (2 : ℝ) ^ I.card := by
    rw [Finset.prod_div_distrib]
    simp [P]
  have hprodUpper :
      ∏ i : I, (m i : ℝ) ≤ ∏ i : I, (2 * N i) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact Nat.cast_nonneg _
    · intro i hi
      exact (hwindow i).2
  have hprodUpperEq :
      (∏ i : I, (2 * N i)) = (2 : ℝ) ^ I.card * P := by
    rw [Finset.prod_mul_distrib]
    simp [P]
  constructor
  · rw [← hP, ← hprodLowerEq]
    exact hprodLower
  · calc
      ∏ i : I, (m i : ℝ) ≤ ∏ i : I, (2 * N i) := hprodUpper
      _ = (2 : ℝ) ^ I.card * P := hprodUpperEq
      _ = (2 : ℝ) ^ I.card *
          smoothHeathBrownSubgroupScaleProduct fs I := by rw [hP]

/-- The product of the original residue-restricted factor polynomials in one
nonempty selected group is the exact sum of its source dyadic group blocks.
The broad support interval and block scales are derived from the factor
scales; the arbitrary frequency shift and half-open block convention are
retained. -/
theorem smoothHeathBrownResidueGroupFactorProduct_eq_dyadicBlocks
    {X z : ℝ} {q : ℕ}
    (fsList : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fsList.length)) (hI : I.Nonempty)
    (hq : 0 < q) (residue : Fin fsList.length → ℕ)
    (hresidue : ∀ i ∈ I, residue i < q) (t u : ℝ) :
    (∏ i : I,
      mellinSeparationFactorPolynomial
        (fun _ : Fin 1 =>
          smoothHeathBrownNormalizedMellinFactor (z := z) (fsList.get i.val))
        q 0 ⟨residue i.val, hresidue i.val i.property⟩
        (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ))) =
      ∑ j ∈ Finset.range (2 * I.card),
        factorPolynomial
          ((2 : ℝ) ^ j *
            (smoothHeathBrownSubgroupScaleProduct fsList I /
              (2 : ℝ) ^ I.card))
          (smoothHeathBrownResidueGroupBlockTwistedCoefficient
            (z := z) (fun i => fsList.get i) I q residue
            ((2 : ℝ) ^ j *
              (smoothHeathBrownSubgroupScaleProduct fsList I /
                (2 : ℝ) ^ I.card)) u) t := by
  classical
  let fs : Fin fsList.length → SmoothHeathBrownFactor X := fun i => fsList.get i
  let S : ℝ := smoothHeathBrownSubgroupScaleProduct fsList I
  let M : ℝ := S / (2 : ℝ) ^ I.card
  let U : ℝ := (2 : ℝ) ^ I.card * S
  let k : ℕ := 2 * I.card
  have hSpos : 0 < S := by
    dsimp [S, smoothHeathBrownSubgroupScaleProduct]
    exact Finset.prod_pos fun i hi => smoothHeathBrownFactorScale_pos (fs i)
  have hdenpos : 0 < (2 : ℝ) ^ I.card := by positivity
  have hMpos : 0 < M := by dsimp [M]; exact div_pos hSpos hdenpos
  have hM : 0 < M := hMpos
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have hwindow : ∀ m ∈ Fintype.piFinset
      (fun i : I => smoothHeathBrownFactorFiniteSupport (fs i.val)),
      M < (∏ i : I, (m i : ℝ)) ∧
        (∏ i : I, (m i : ℝ)) ≤ U := by
    intro m hm
    have htuple := smoothHeathBrownDPGroupTupleSupportWindow fsList I hI m hm
    simpa [M, U, S] using htuple
  have hscale : (2 : ℝ) ^ k * M = U := by
    dsimp [k, M, U]
    rw [show 2 * I.card = I.card + I.card by omega, pow_add]
    field_simp
  have hbroad := smoothHeathBrownResidueGroupBroadWindow_sum_eq_factorPolynomials
    (z := z) fs I q hq residue hresidue M U t u (le_of_lt hM) hU hwindow
  have hdyadic := smoothHeathBrownResidueGroupBroadWindow_sum_eq_dyadicBlockPolynomials
    (z := z) fs I q residue M u t k hM
  calc
    (∏ i : I,
        mellinSeparationFactorPolynomial
          (fun _ : Fin 1 =>
            smoothHeathBrownNormalizedMellinFactor (z := z) (fsList.get i.val))
          q 0 ⟨residue i.val, hresidue i.val i.property⟩
          (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ))) =
        ∑ n ∈ factorExtractionRealInterval M U,
          (∏ i : I,
            smoothHeathBrownResidueFactorArithmeticFunction (z := z)
              q (residue i.val) (fsList.get i.val)) n *
            (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
              Complex.I * ((t - u : ℝ) : ℂ)) := hbroad.symm
    _ = ∑ n ∈ factorExtractionRealInterval M ((2 : ℝ) ^ k * M),
          (∏ i : I,
            smoothHeathBrownResidueFactorArithmeticFunction (z := z)
              q (residue i.val) (fsList.get i.val)) n *
            (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
              Complex.I * ((t - u : ℝ) : ℂ)) := by rw [hscale]
    _ = ∑ j ∈ Finset.range k,
          factorPolynomial ((2 : ℝ) ^ j * M)
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I q residue
              ((2 : ℝ) ^ j * M) u) t := hdyadic
    _ = _ := by simpa [M, k, S]

private theorem smoothHeathBrownDP_prod_eq_three_disjoint_cover
    {n : ℕ} {α : Type*} [CommMonoid α]
    (I J K : Finset (Fin n)) (hIJ : Disjoint I J)
    (hIK : Disjoint I K) (hJK : Disjoint J K)
    (hcover : I ∪ J ∪ K = Finset.univ) (f : Fin n → α) :
    (∏ i : Fin n, f i) =
      (∏ i : I, f i.val) *
        ((∏ i : J, f i.val) * (∏ i : K, f i.val)) := by
  classical
  have hdisj : Disjoint (I ∪ J) K := by
    rw [Finset.disjoint_left]
    intro i hi hk
    rcases Finset.mem_union.mp hi with hiI | hiJ
    · exact (Finset.disjoint_left.mp hIK) hiI hk
    · exact (Finset.disjoint_left.mp hJK) hiJ hk
  have hI : (∏ i : I, f i.val) = ∏ i ∈ I, f i :=
    Finset.prod_coe_sort I f
  have hJ : (∏ i : J, f i.val) = ∏ i ∈ J, f i :=
    Finset.prod_coe_sort J f
  have hK : (∏ i : K, f i.val) = ∏ i ∈ K, f i :=
    Finset.prod_coe_sort K f
  calc
    (∏ i : Fin n, f i) = ∏ i ∈ Finset.univ, f i := rfl
    _ = ∏ i ∈ I ∪ J ∪ K, f i := by rw [← hcover]
    _ = (∏ i ∈ I ∪ J, f i) * (∏ i ∈ K, f i) :=
      Finset.prod_union hdisj
    _ = ((∏ i ∈ I, f i) * (∏ i ∈ J, f i)) *
        (∏ i ∈ K, f i) := by rw [Finset.prod_union hIJ]
    _ = (∏ i : I, f i.val) *
        ((∏ i : J, f i.val) * (∏ i : K, f i.val)) := by
          rw [← hI, ← hJ, ← hK]
          ac_rfl

/-- Exact pointwise expansion of the full residue product into all dyadic
block triples of a fixed three-way source partition. This is the finite
`hExpansion` input for the envelope accumulation theorem below. -/
theorem smoothHeathBrownThreeGroupResidueProduct_eq_blockTripleSum
    {X z : ℝ} {q : ℕ}
    (fsList : List (SmoothHeathBrownFactor X))
    (I₁ I₂ I₃ : Finset (Fin fsList.length))
    (hI₁ : I₁.Nonempty) (hI₂ : I₂.Nonempty) (hI₃ : I₃.Nonempty)
    (hI₁I₂ : Disjoint I₁ I₂) (hI₁I₃ : Disjoint I₁ I₃)
    (hI₂I₃ : Disjoint I₂ I₃)
    (hcover : I₁ ∪ I₂ ∪ I₃ = Finset.univ)
    (hq : 0 < q) (b : Fin fsList.length → Fin q) (t u : ℝ) :
    productDirichletPolynomialsAt
        (fun i : Fin fsList.length =>
          smoothHeathBrownNormalizedMellinFactor (z := z) (fsList.get i))
        b t u =
      ∑ p ∈
          Finset.range (2 * I₁.card) ×ˢ
            (Finset.range (2 * I₂.card) ×ˢ Finset.range (2 * I₃.card)),
        productDirichletPolynomialsAt
          (smoothHeathBrownThreeGroupBlockMellinFactors
            (z := z) (fun i : Fin fsList.length => fsList.get i)
            I₁ I₂ I₃ q (fun i => (b i).val)
            ((2 : ℝ) ^ p.1 *
              (smoothHeathBrownSubgroupScaleProduct fsList I₁ /
                (2 : ℝ) ^ I₁.card))
            ((2 : ℝ) ^ p.2.1 *
              (smoothHeathBrownSubgroupScaleProduct fsList I₂ /
                (2 : ℝ) ^ I₂.card))
            ((2 : ℝ) ^ p.2.2 *
              (smoothHeathBrownSubgroupScaleProduct fsList I₃ /
                (2 : ℝ) ^ I₃.card))
          )
          (fun _ : Fin 3 => (0 : Fin 1)) t u := by
  classical
  let α : Fin fsList.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := z) (fsList.get i)
  let residue : Fin fsList.length → ℕ := fun i => (b i).val
  let φ : Fin fsList.length → ℂ := fun i =>
    mellinSeparationFactorPolynomial (fun _ : Fin 1 => α i) q 0 (b i)
      (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ))
  let A₁ := Finset.range (2 * I₁.card)
  let A₂ := Finset.range (2 * I₂.card)
  let A₃ := Finset.range (2 * I₃.card)
  let M₁ := smoothHeathBrownSubgroupScaleProduct fsList I₁ /
      (2 : ℝ) ^ I₁.card
  let M₂ := smoothHeathBrownSubgroupScaleProduct fsList I₂ /
      (2 : ℝ) ^ I₂.card
  let M₃ := smoothHeathBrownSubgroupScaleProduct fsList I₃ /
      (2 : ℝ) ^ I₃.card
  let F₁ : ℕ → ℂ := fun j => factorPolynomial ((2 : ℝ) ^ j * M₁)
    (smoothHeathBrownResidueGroupBlockTwistedCoefficient
      (z := z) (fun i => fsList.get i) I₁ q residue ((2 : ℝ) ^ j * M₁) u) t
  let F₂ : ℕ → ℂ := fun j => factorPolynomial ((2 : ℝ) ^ j * M₂)
    (smoothHeathBrownResidueGroupBlockTwistedCoefficient
      (z := z) (fun i => fsList.get i) I₂ q residue ((2 : ℝ) ^ j * M₂) u) t
  let F₃ : ℕ → ℂ := fun j => factorPolynomial ((2 : ℝ) ^ j * M₃)
    (smoothHeathBrownResidueGroupBlockTwistedCoefficient
      (z := z) (fun i => fsList.get i) I₃ q residue ((2 : ℝ) ^ j * M₃) u) t
  let Jblock := A₁ ×ˢ (A₂ ×ˢ A₃)
  let β : (ℕ × (ℕ × ℕ)) → Fin 3 → MellinSeparationFactor := fun p =>
    smoothHeathBrownThreeGroupBlockMellinFactors
      (z := z) (fun i : Fin fsList.length => fsList.get i)
      I₁ I₂ I₃ q residue ((2 : ℝ) ^ p.1 * M₁)
      ((2 : ℝ) ^ p.2.1 * M₂) ((2 : ℝ) ^ p.2.2 * M₃)
  let ρ : (ℕ × (ℕ × ℕ)) → Fin 3 → Fin 1 := fun _ _ => 0
  have hresidue : ∀ i ∈ I₁, residue i < q := by
    intro i hi
    exact (b i).isLt
  have hresidue₂ : ∀ i ∈ I₂, residue i < q := by
    intro i hi
    exact (b i).isLt
  have hresidue₃ : ∀ i ∈ I₃, residue i < q := by
    intro i hi
    exact (b i).isLt
  have h₁ := smoothHeathBrownResidueGroupFactorProduct_eq_dyadicBlocks
    (z := z)
    fsList I₁ hI₁ hq residue hresidue t u
  have h₂ := smoothHeathBrownResidueGroupFactorProduct_eq_dyadicBlocks
    (z := z)
    fsList I₂ hI₂ hq residue hresidue₂ t u
  have h₃ := smoothHeathBrownResidueGroupFactorProduct_eq_dyadicBlocks
    (z := z)
    fsList I₃ hI₃ hq residue hresidue₃ t u
  have h₁' : (∏ i : I₁, φ i.val) = ∑ j ∈ A₁, F₁ j := by
    simpa [φ, F₁, A₁, M₁, α] using h₁
  have h₂' : (∏ i : I₂, φ i.val) = ∑ j ∈ A₂, F₂ j := by
    simpa [φ, F₂, A₂, M₂, α] using h₂
  have h₃' : (∏ i : I₃, φ i.val) = ∑ j ∈ A₃, F₃ j := by
    simpa [φ, F₃, A₃, M₃, α] using h₃
  have hsplit := smoothHeathBrownDP_prod_eq_three_disjoint_cover
    I₁ I₂ I₃ hI₁I₂ hI₁I₃ hI₂I₃ hcover φ
  have hsum :
      (∑ j ∈ A₁, F₁ j) *
        ((∑ j ∈ A₂, F₂ j) * (∑ j ∈ A₃, F₃ j)) =
      ∑ p ∈ Jblock, F₁ p.1 * (F₂ p.2.1 * F₃ p.2.2) := by
    have h₂₃ :
        (∑ p ∈ A₂ ×ˢ A₃, F₂ p.1 * F₃ p.2) =
          (∑ j ∈ A₂, F₂ j) * (∑ j ∈ A₃, F₃ j) := by
      rw [Finset.sum_product]
      exact (Finset.sum_mul_sum A₂ A₃ F₂ F₃).symm
    have hindex :
        (∑ p ∈ Jblock, F₁ p.1 * (F₂ p.2.1 * F₃ p.2.2)) =
          ∑ i ∈ A₁, ∑ p ∈ A₂ ×ˢ A₃, F₁ i * (F₂ p.1 * F₃ p.2) := by
      dsimp [Jblock, A₁, A₂, A₃]
      rw [Finset.sum_product]
    calc
      _ = (∑ i ∈ A₁, F₁ i) *
          (∑ p ∈ A₂ ×ˢ A₃, F₂ p.1 * F₃ p.2) := by rw [← h₂₃]
      _ = ∑ i ∈ A₁, ∑ p ∈ A₂ ×ˢ A₃,
          F₁ i * (F₂ p.1 * F₃ p.2) := Finset.sum_mul_sum _ _ _ _
      _ = _ := hindex.symm
  have hM₁pos : 0 < M₁ := by
    dsimp [M₁]
    apply div_pos
    · exact Finset.prod_pos fun i hi => smoothHeathBrownFactorScale_pos (fsList.get i)
    · positivity
  have hM₂pos : 0 < M₂ := by
    dsimp [M₂]
    apply div_pos
    · exact Finset.prod_pos fun i hi => smoothHeathBrownFactorScale_pos (fsList.get i)
    · positivity
  have hM₃pos : 0 < M₃ := by
    dsimp [M₃]
    apply div_pos
    · exact Finset.prod_pos fun i hi => smoothHeathBrownFactorScale_pos (fsList.get i)
    · positivity
  change (∏ i : Fin fsList.length, φ i) = _
  calc
    (∏ i : Fin fsList.length, φ i) =
        (∏ i : I₁, φ i.val) *
          ((∏ i : I₂, φ i.val) * (∏ i : I₃, φ i.val)) := hsplit
    _ = (∑ j ∈ A₁, F₁ j) *
          ((∑ j ∈ A₂, F₂ j) * (∑ j ∈ A₃, F₃ j)) := by rw [h₁', h₂', h₃']
    _ = ∑ p ∈ Jblock, F₁ p.1 * (F₂ p.2.1 * F₃ p.2.2) := hsum
    _ = ∑ p ∈ Jblock,
          productDirichletPolynomialsAt (β p) (ρ p) t u := by
      apply Finset.sum_congr rfl
      intro p hp
      have hL₁ : 0 < (2 : ℝ) ^ p.1 * M₁ := mul_pos (by positivity) hM₁pos
      have hL₂ : 0 < (2 : ℝ) ^ p.2.1 * M₂ := mul_pos (by positivity) hM₂pos
      have hL₃ : 0 < (2 : ℝ) ^ p.2.2 * M₃ := mul_pos (by positivity) hM₃pos
      have hpoly := smoothHeathBrownThreeGroupBlockMellinFactors_polynomial_eq
        (z := z) (fun i : Fin fsList.length => fsList.get i)
        I₁ I₂ I₃ q residue
        ((2 : ℝ) ^ p.1 * M₁) ((2 : ℝ) ^ p.2.1 * M₂)
        ((2 : ℝ) ^ p.2.2 * M₃) u t hL₁ hL₂ hL₃
      calc
        F₁ p.1 * (F₂ p.2.1 * F₃ p.2.2) =
            (F₁ p.1 * F₂ p.2.1) * F₃ p.2.2 := by ring
        _ = productDirichletPolynomialsAt (β p) (ρ p) t u := by
          simpa [β, ρ, F₁, F₂, F₃, M₁, M₂, M₃] using hpoly.symm

/-- The finite index set of source dyadic block triples for a fixed partition. -/
def smoothHeathBrownDPThreeGroupBlockIndexSet {K : ℕ}
    (I₁ I₂ I₃ : Finset (Fin K)) : Finset (ℕ × (ℕ × ℕ)) :=
  Finset.range (2 * I₁.card) ×ˢ
    (Finset.range (2 * I₂.card) ×ˢ Finset.range (2 * I₃.card))

/-- There are at most `40^3` natural-indexed dyadic triples when each source
group has at most 20 factors. -/
theorem smoothHeathBrownDPThreeGroupBlockIndexSet_card_le
    {K : ℕ} (I₁ I₂ I₃ : Finset (Fin K))
    (hI₁ : I₁.card ≤ 20) (hI₂ : I₂.card ≤ 20) (hI₃ : I₃.card ≤ 20) :
    (smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃).card ≤
      40 * (40 * 40) := by
  have h₁ : 2 * I₁.card ≤ 40 := by omega
  have h₂ : 2 * I₂.card ≤ 40 := by omega
  have h₃ : 2 * I₃.card ≤ 40 := by omega
  simp only [smoothHeathBrownDPThreeGroupBlockIndexSet,
    Finset.card_product, Finset.card_range]
  exact Nat.mul_le_mul h₁ (Nat.mul_le_mul h₂ h₃)

/-- Under the source `q ≤ (log X)^B` and `r ≤ R` hypotheses, the product of
the allowed residue count and the three-group dyadic block count has the
exact polylogarithmic upper bound `40^3 (log X)^(BR)`. -/
theorem smoothHeathBrownDPThreeGroupResidueBlockCount_le_logPower
    {r q K : ℕ} (a : ℤ) (B R X : ℝ)
    (hB : 0 < B) (hR : 0 < R) (hX : 3 ≤ X)
    (hq : (q : ℝ) ≤ Real.rpow (Real.log X) B)
    (hr : (r : ℝ) ≤ R)
    (I₁ I₂ I₃ : Finset (Fin K))
    (hI₁ : I₁.card ≤ 20) (hI₂ : I₂.card ≤ 20) (hI₃ : I₃.card ≤ 20) :
    ((mellinSeparationAllowedResidues (r := r) (q := q) a).card : ℝ) *
        ((smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃).card : ℝ) ≤
      (40 : ℝ) * (40 * 40) * Real.rpow (Real.log X) (B * R) := by
  have hres := mellinSeparationAllowedResidues_card_le_log_power
    (r := r) (q := q) a B R X hB hR hX hq hr
  have hblocksNat := smoothHeathBrownDPThreeGroupBlockIndexSet_card_le
    I₁ I₂ I₃ hI₁ hI₂ hI₃
  have hblocks :
      ((smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃).card : ℝ) ≤
        (40 : ℝ) * (40 * 40) := by exact_mod_cast hblocksNat
  have hcountNonneg :
      0 ≤ ((smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃).card : ℝ) :=
    Nat.cast_nonneg _
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith [hX])
  have hpolyNonneg : 0 ≤ Real.rpow (Real.log X) (B * R) :=
    (Real.rpow_pos_of_pos hlogXpos _).le
  calc
    ((mellinSeparationAllowedResidues (r := r) (q := q) a).card : ℝ) *
        ((smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃).card : ℝ) ≤
      Real.rpow (Real.log X) (B * R) * ((40 : ℝ) * (40 * 40)) :=
        mul_le_mul hres hblocks hcountNonneg hpolyNonneg
    _ = (40 : ℝ) * (40 * 40) * Real.rpow (Real.log X) (B * R) := by ring

/-- Every natural dyadic block index in the source range corresponds to the
exact integer shift range used by the three-group source theorem. -/
theorem smoothHeathBrownDPBlockIndex_shift_mem
    {c j : ℕ} (hj : j < 2 * c) :
    -(c : ℤ) ≤ (j : ℤ) - (c : ℤ) ∧ (j : ℤ) - (c : ℤ) < (c : ℤ) := by
  omega

/-- The natural-indexed block scale in the finite Mellin expansion is exactly
the integer-shift block scale in `lda:dp-from-muf`, with no rounding. -/
theorem smoothHeathBrownDPBlockScale_eq_integerShift
    (S : ℝ) (c j : ℕ) :
    (2 : ℝ) ^ j * (S / (2 : ℝ) ^ c) =
      smoothHeathBrownDyadicBlockScale S ((j : ℤ) - (c : ℤ)) := by
  rw [smoothHeathBrownDyadicBlockScale]
  have hp : (2 : ℝ) ^ ((j : ℤ) - (c : ℤ)) =
      (2 : ℝ) ^ j / (2 : ℝ) ^ c := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0) (j : ℤ) (c : ℤ)]
    simp
  rw [hp]
  ring

/-- Membership in the exact finite source triple index set gives all three
integer shift bounds required by the selected-group DP integral theorem. -/
theorem smoothHeathBrownDPThreeGroupBlock_shiftBounds
    {K : ℕ} (I₁ I₂ I₃ : Finset (Fin K))
    (p : ℕ × (ℕ × ℕ))
    (hp : p ∈ smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃) :
    (-(I₁.card : ℤ) ≤ (p.1 : ℤ) - (I₁.card : ℤ) ∧
        (p.1 : ℤ) - (I₁.card : ℤ) < I₁.card) ∧
    ((-(I₂.card : ℤ) ≤ (p.2.1 : ℤ) - (I₂.card : ℤ) ∧
        (p.2.1 : ℤ) - (I₂.card : ℤ) < I₂.card) ∧
      (-(I₃.card : ℤ) ≤ (p.2.2 : ℤ) - (I₃.card : ℤ) ∧
        (p.2.2 : ℤ) - (I₃.card : ℤ) < I₃.card)) := by
  change p ∈ Finset.range (2 * I₁.card) ×ˢ
    (Finset.range (2 * I₂.card) ×ˢ Finset.range (2 * I₃.card)) at hp
  rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂₃⟩
  rcases Finset.mem_product.mp hp₂₃ with ⟨hp₂, hp₃⟩
  exact ⟨smoothHeathBrownDPBlockIndex_shift_mem (Finset.mem_range.mp hp₁),
    ⟨smoothHeathBrownDPBlockIndex_shift_mem (Finset.mem_range.mp hp₂),
      smoothHeathBrownDPBlockIndex_shift_mem (Finset.mem_range.mp hp₃)⟩⟩

/-- The three natural-indexed factor scales of the source block factors equal
the corresponding exact integer-shift scales for the source partition. -/
theorem smoothHeathBrownDPThreeGroupBlockScales_eq_integerShifts
    {X : ℝ} (fsList : List (SmoothHeathBrownFactor X))
    (I₁ I₂ I₃ : Finset (Fin fsList.length))
    (p : ℕ × (ℕ × ℕ)) :
    ((2 : ℝ) ^ p.1 *
        (smoothHeathBrownSubgroupScaleProduct fsList I₁ / (2 : ℝ) ^ I₁.card) =
      smoothHeathBrownDyadicBlockScale
        (smoothHeathBrownSubgroupScaleProduct fsList I₁)
        ((p.1 : ℤ) - (I₁.card : ℤ))) ∧
    ((2 : ℝ) ^ p.2.1 *
        (smoothHeathBrownSubgroupScaleProduct fsList I₂ / (2 : ℝ) ^ I₂.card) =
      smoothHeathBrownDyadicBlockScale
        (smoothHeathBrownSubgroupScaleProduct fsList I₂)
        ((p.2.1 : ℤ) - (I₂.card : ℤ))) ∧
    ((2 : ℝ) ^ p.2.2 *
        (smoothHeathBrownSubgroupScaleProduct fsList I₃ / (2 : ℝ) ^ I₃.card) =
      smoothHeathBrownDyadicBlockScale
        (smoothHeathBrownSubgroupScaleProduct fsList I₃)
        ((p.2.2 : ℤ) - (I₃.card : ℤ))) := by
  exact ⟨smoothHeathBrownDPBlockScale_eq_integerShift _ _ _,
    smoothHeathBrownDPBlockScale_eq_integerShift _ _ _,
    smoothHeathBrownDPBlockScale_eq_integerShift _ _ _⟩

/-- The source product scale of an integer-shift triple is exactly the
product scale of the corresponding natural-indexed finite block. -/
theorem smoothHeathBrownDPThreeGroupBlockProductScale_eq_integerShifts
    {X : ℝ} (fsList : List (SmoothHeathBrownFactor X))
    (I₁ I₂ I₃ : Finset (Fin fsList.length))
    (p : ℕ × (ℕ × ℕ)) :
    smoothHeathBrownThreeDyadicBlockProductScale
        (smoothHeathBrownSubgroupScaleProduct fsList I₁)
        (smoothHeathBrownSubgroupScaleProduct fsList I₂)
        (smoothHeathBrownSubgroupScaleProduct fsList I₃)
        ((p.1 : ℤ) - (I₁.card : ℤ))
        ((p.2.1 : ℤ) - (I₂.card : ℤ))
        ((p.2.2 : ℤ) - (I₃.card : ℤ)) =
      ((2 : ℝ) ^ p.1 *
          (smoothHeathBrownSubgroupScaleProduct fsList I₁ / (2 : ℝ) ^ I₁.card)) *
        ((2 : ℝ) ^ p.2.1 *
          (smoothHeathBrownSubgroupScaleProduct fsList I₂ / (2 : ℝ) ^ I₂.card)) *
        ((2 : ℝ) ^ p.2.2 *
          (smoothHeathBrownSubgroupScaleProduct fsList I₃ / (2 : ℝ) ^ I₃.card)) := by
  rw [smoothHeathBrownThreeDyadicBlockProductScale]
  rw [← smoothHeathBrownDPBlockScale_eq_integerShift
    (smoothHeathBrownSubgroupScaleProduct fsList I₁) I₁.card p.1]
  rw [← smoothHeathBrownDPBlockScale_eq_integerShift
    (smoothHeathBrownSubgroupScaleProduct fsList I₂) I₂.card p.2.1]
  rw [← smoothHeathBrownDPBlockScale_eq_integerShift
    (smoothHeathBrownSubgroupScaleProduct fsList I₃) I₃.card p.2.2]

/-- Convert the source trilinear interval's `Y^(log L/log Y)` scales back to
the exact natural block scales used by the Mellin product envelope. This is
the only normalization step needed to use the source interval as `hLow`. -/
theorem smoothHeathBrownThreeGroupSourceInterval_to_blockScales
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I₁ I₂ I₃ : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L₁ L₂ L₃ Y W V u M : ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃)
    (hY : (2 : ℝ) ^ 16 ≤ Y) (hYprod : Y = L₁ * L₂ * L₃)
    (hSource :
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₁ q residue L₁ u) t *
          factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₂ q residue L₂ u) t *
          factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₃ q residue L₃ u) t‖ ≤ M) :
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial L₁
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₁ q residue L₁ u) t *
          factorPolynomial L₂
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₂ q residue L₂ u) t *
          factorPolynomial L₃
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₃ q residue L₃ u) t‖ ≤ M := by
  have hYpos : 0 < Y := by rw [hYprod]; positivity
  have hYgt : 1 < Y := by
    have hpow : 1 < (2 : ℝ) ^ 16 := by norm_num
    linarith
  have hlogYpos : 0 < Real.log Y := Real.log_pos hYgt
  have hpow₁ : Y ^ (Real.log L₁ / Real.log Y) = L₁ := by
    rw [Real.rpow_def_of_pos hYpos]
    rw [show Real.log Y * (Real.log L₁ / Real.log Y) = Real.log L₁ by
      field_simp [ne_of_gt hlogYpos]]
    exact Real.exp_log hL₁
  have hpow₂ : Y ^ (Real.log L₂ / Real.log Y) = L₂ := by
    rw [Real.rpow_def_of_pos hYpos]
    rw [show Real.log Y * (Real.log L₂ / Real.log Y) = Real.log L₂ by
      field_simp [ne_of_gt hlogYpos]]
    exact Real.exp_log hL₂
  have hpow₃ : Y ^ (Real.log L₃ / Real.log Y) = L₃ := by
    rw [Real.rpow_def_of_pos hYpos]
    rw [show Real.log Y * (Real.log L₃ / Real.log Y) = Real.log L₃ by
      field_simp [ne_of_gt hlogYpos]]
    exact Real.exp_log hL₃
  simpa only [hpow₁, hpow₂, hpow₃] using hSource

/-- Feed the exact source DP interval integral into the actual-residue
Fourier-weighted block-envelope estimate. The source integral remains an
explicit premise; this adapter only changes its `Y^(log L/log Y)` display to
the equal block scales and then applies the checked low/high envelope split. -/
theorem smoothHeathBrownThreeGroupBlock_fourierIntegral_le_of_sourceIntervals
    {X z : ℝ} {K : ℕ} (hX : 3 ≤ X)
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I₁ I₂ I₃ : Finset (Fin K))
    (hI₁ : I₁.card ≤ 20) (hI₂ : I₂.card ≤ 20) (hI₃ : I₃.card ≤ 20)
    (q : ℕ) (residue : Fin K → ℕ)
    (L₁ L₂ L₃ Y eps T0 W T Mlow Ktail : ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃)
    (hL₁two : 2 ≤ L₁) (hL₂two : 2 ≤ L₂) (hL₃two : 2 ≤ L₃)
    (hY : (2 : ℝ) ^ 16 ≤ Y) (hYprod : Y = L₁ * L₂ * L₃)
    (hEps0 : 0 < eps) (hEps : eps ≤ 3 / 16)
    (hTtwo : 2 ≤ T) (hTupper : T ≤ Y ^ ((3 / 8 : ℝ) - eps))
    (hαlower : 1 / 4 - eps / 100 ≤ Real.log L₁ / Real.log Y)
    (hαupper : Real.log L₁ / Real.log Y ≤ 1 / 2 + eps / 100)
    (hβγ : |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
      1 / 4 + eps / 100)
    (hW : 2 ≤ W) (hWT : W ≤ T0) (hVtop : T0 * W ^ 4 ≤ T)
    (hMlow : 0 ≤ Mlow)
    (hSourceInterval : ∀ (u V : ℝ), |u| ≤ W / 2 →
      V ∈ Set.Icc T0 (T0 * W ^ 4) →
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₁ q residue L₁ u) t *
          factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₂ q residue L₂ u) t *
          factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₃ q residue L₃ u) t‖ ≤ Mlow)
    (hKernelTail :
      ∫ u in {u : ℝ | W / 2 < |u|},
        ‖mellinSeparationLogKernelFourier u‖ ≤ Ktail) :
    (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
      productDirichletMeanEnvelope
        (smoothHeathBrownThreeGroupBlockMellinFactors
          (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃)
        (fun _ : Fin 3 => (0 : Fin 1)) T0 W u) ≤
      Mlow * (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖) +
        Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y * (1 + Y ^ (-eps / 16 : ℝ)) * Ktail := by
  have hLow : ∀ (u V : ℝ), |u| ≤ W / 2 →
      V ∈ Set.Icc T0 (T0 * W ^ 4) →
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial L₁
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₁ q residue L₁ u) t *
          factorPolynomial L₂
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₂ q residue L₂ u) t *
          factorPolynomial L₃
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₃ q residue L₃ u) t‖ ≤ Mlow := by
    intro u V hu hV
    exact smoothHeathBrownThreeGroupSourceInterval_to_blockScales
      fs I₁ I₂ I₃ q residue L₁ L₂ L₃ Y W V u Mlow
      hL₁ hL₂ hL₃ hY hYprod (hSourceInterval u V hu hV)
  exact smoothHeathBrownThreeGroupBlock_fourierIntegral_le
    hX fs I₁ I₂ I₃ hI₁ hI₂ hI₃ q residue L₁ L₂ L₃ Y eps T0 W T Mlow Ktail
    hL₁ hL₂ hL₃ hL₁two hL₂two hL₃two hY hYprod hEps0 hEps hTtwo hTupper
    hαlower hαupper hβγ hW hWT hVtop hMlow hLow hKernelTail

/-- The actual three-group Mellin factors at a source dyadic block triple. -/
noncomputable def smoothHeathBrownDPThreeGroupBlockFactors
    {X z : ℝ} {q : ℕ} (fsList : List (SmoothHeathBrownFactor X))
    (I₁ I₂ I₃ : Finset (Fin fsList.length))
    (b : Fin fsList.length → Fin q) (p : ℕ × (ℕ × ℕ)) :
    Fin 3 → MellinSeparationFactor :=
  smoothHeathBrownThreeGroupBlockMellinFactors
    (z := z) (fun i : Fin fsList.length => fsList.get i)
    I₁ I₂ I₃ q (fun i => (b i).val)
    ((2 : ℝ) ^ p.1 *
      (smoothHeathBrownSubgroupScaleProduct fsList I₁ /
        (2 : ℝ) ^ I₁.card))
    ((2 : ℝ) ^ p.2.1 *
      (smoothHeathBrownSubgroupScaleProduct fsList I₂ /
        (2 : ℝ) ^ I₂.card))
    ((2 : ℝ) ^ p.2.2 *
      (smoothHeathBrownSubgroupScaleProduct fsList I₃ /
        (2 : ℝ) ^ I₃.card))

/-- The actual finite-block Mellin factor tuple is precisely the source
three-group factor tuple at the associated integer shifts. -/
theorem smoothHeathBrownDPThreeGroupBlockFactors_eq_integerShiftFactors
    {X z : ℝ} {q : ℕ} (fsList : List (SmoothHeathBrownFactor X))
    (I₁ I₂ I₃ : Finset (Fin fsList.length))
    (b : Fin fsList.length → Fin q) (p : ℕ × (ℕ × ℕ)) :
    smoothHeathBrownDPThreeGroupBlockFactors (z := z) (q := q)
        fsList I₁ I₂ I₃ b p =
      smoothHeathBrownThreeGroupBlockMellinFactors
        (z := z) (fun i : Fin fsList.length => fsList.get i)
        I₁ I₂ I₃ q (fun i => (b i).val)
        (smoothHeathBrownDyadicBlockScale
          (smoothHeathBrownSubgroupScaleProduct fsList I₁)
          ((p.1 : ℤ) - (I₁.card : ℤ)))
        (smoothHeathBrownDyadicBlockScale
          (smoothHeathBrownSubgroupScaleProduct fsList I₂)
          ((p.2.1 : ℤ) - (I₂.card : ℤ)))
        (smoothHeathBrownDyadicBlockScale
          (smoothHeathBrownSubgroupScaleProduct fsList I₃)
          ((p.2.2 : ℤ) - (I₃.card : ℤ))) := by
  unfold smoothHeathBrownDPThreeGroupBlockFactors
  rw [← smoothHeathBrownDPBlockScale_eq_integerShift
    (smoothHeathBrownSubgroupScaleProduct fsList I₁) I₁.card p.1]
  rw [← smoothHeathBrownDPBlockScale_eq_integerShift
    (smoothHeathBrownSubgroupScaleProduct fsList I₂) I₂.card p.2.1]
  rw [← smoothHeathBrownDPBlockScale_eq_integerShift
    (smoothHeathBrownSubgroupScaleProduct fsList I₃) I₃.card p.2.2]

/-- Specialize the uniform source DP interval output at `U = V` for every
possible mean-envelope endpoint `V`, and transport the natural finite block
index to its exact legal integer-shift triple. The source low-frequency
interval and its all-shift bound remain explicit in `hSourceDP`. -/
theorem smoothHeathBrownDPThreeGroupBlockSourceInterval_fromShiftOutput
    {X z B κ D η W T0 : ℝ}
    (fsList : List (SmoothHeathBrownFactor X))
    (I₁ I₂ I₃ : Finset (Fin fsList.length))
    (selected : Fin fsList.length)
    (q : ℕ) (residue : Fin fsList.length → ℕ)
    (hresidue : residue selected < q)
    (p : ℕ × (ℕ × ℕ))
    (hp : p ∈ smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃)
    (hWtwo : 2 ≤ W) (hWT0 : W ≤ T0)
    (hT0upper : T0 ≤ X ^ ((3 / 8 : ℝ) - η))
    (hq : 1 ≤ q) (hqlog : (q : ℝ) ≤ (Real.log X) ^ B)
    (hSourceDP : ∀ (U : ℝ), W ≤ U →
      U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ) →
      ∀ (u : ℝ), |u| ≤ W / 2 →
      ∀ (q' : ℕ), 1 ≤ q' → (q' : ℝ) ≤ (Real.log X) ^ B →
      ∀ (residue' : Fin fsList.length → ℕ),
      residue' selected < q' →
      ∀ (h₁ h₂ h₃ : ℤ),
      (-(I₁.card : ℤ) ≤ h₁ ∧ h₁ < I₁.card) →
      (-(I₂.card : ℤ) ≤ h₂ ∧ h₂ < I₂.card) →
      (-(I₃.card : ℤ) ≤ h₃ ∧ h₃ < I₃.card) →
      let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I₁
      let S₂ := smoothHeathBrownSubgroupScaleProduct fsList I₂
      let S₃ := smoothHeathBrownSubgroupScaleProduct fsList I₃
      let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
      let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
      let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
      let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
      let eps := η / 2
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
        ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I₁ q' residue' L₁ u) t *
          factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I₂ q' residue' L₂ u) t *
          factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I₃ q' residue' L₃ u) t‖ ≤
        FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
          (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
            (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
              Y ^ (-eps / 16 : ℝ))) :
    let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I₁
    let S₂ := smoothHeathBrownSubgroupScaleProduct fsList I₂
    let S₃ := smoothHeathBrownSubgroupScaleProduct fsList I₃
    let h₁ : ℤ := (p.1 : ℤ) - (I₁.card : ℤ)
    let h₂ : ℤ := (p.2.1 : ℤ) - (I₂.card : ℤ)
    let h₃ : ℤ := (p.2.2 : ℤ) - (I₃.card : ℤ)
    let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
    let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
    let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
    let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
    let eps := η / 2
    ∀ (u V : ℝ), |u| ≤ W / 2 →
      V ∈ Set.Icc T0 (T0 * W ^ (4 : ℕ)) →
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I₁ q residue L₁ u) t *
          factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I₂ q residue L₂ u) t *
          factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I₃ q residue L₃ u) t‖ ≤
        FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
          (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
            (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
              Y ^ (-eps / 16 : ℝ)) := by
  classical
  dsimp only
  let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I₁
  let S₂ := smoothHeathBrownSubgroupScaleProduct fsList I₂
  let S₃ := smoothHeathBrownSubgroupScaleProduct fsList I₃
  let h₁ : ℤ := (p.1 : ℤ) - (I₁.card : ℤ)
  let h₂ : ℤ := (p.2.1 : ℤ) - (I₂.card : ℤ)
  let h₃ : ℤ := (p.2.2 : ℤ) - (I₃.card : ℤ)
  let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
  let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
  let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
  let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
  let eps : ℝ := η / 2
  have hshift := smoothHeathBrownDPThreeGroupBlock_shiftBounds I₁ I₂ I₃ p hp
  have hWnonneg : 0 ≤ W := by linarith [hWtwo]
  have hpow : 0 ≤ W ^ (4 : ℕ) := by positivity
  intro u V hu hV
  rcases hV with ⟨hVlo, hVhi⟩
  have hWV : W ≤ V := le_trans hWT0 hVlo
  have hVupper : V ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ) := by
    calc
      V ≤ T0 * W ^ (4 : ℕ) := hVhi
      _ ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_right hT0upper hpow
  have hresult := hSourceDP V hWV hVupper u hu q hq hqlog
    residue hresidue h₁ h₂ h₃
    hshift.1 hshift.2.1 hshift.2.2
  simpa [S₁, S₂, S₃, h₁, h₂, h₃, L₁, L₂, L₃, Y, eps] using hresult

/-- Compose the actual fixed-witness `IImaj` source interval output with the
per-block `U = V` specialization. The selected three groups are chosen once,
before the interval endpoint, residue, shift, and block index are supplied.
For `T₀ = X/H`, the source lower bound on `H` gives the exact upper endpoint
needed by the block adapter. -/
theorem smoothHeathBrownDPThreeGroupBlockSourceInterval_of_IImaj
    {B κ D η : ℝ} (hB : 0 < B) (hκ : 0 < κ)
    (hD : 2 * κ + 10 ≤ D) (hη : 0 < η) (hηsmall : η < 3 / 16) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fsList : List (SmoothHeathBrownFactor X)) →
        fsList.length ≤ 20 → fsList ≠ [] →
        smoothHeathBrownSupportRetained
          (X := X) (z := dyadicMobiusCutoff X) fsList →
        (hE : 0 < smoothHeathBrownExponentSum fsList) →
        (smoothHeathBrownExponentGrouping fsList hE).IImaj (5 / 8) →
        ∃ I J J' : Finset (Fin fsList.length), ∃ selected : Fin fsList.length,
          Disjoint I J ∧ Disjoint I J' ∧ Disjoint J J' ∧
          I ∪ J ∪ J' = Finset.univ ∧
          (1 / 4 : ℝ) ≤
            subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ∧
          subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ≤
            1 / 2 ∧
          |subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J -
            subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J'| ≤
              1 / 4 ∧
          selected ∈ I ∧ I.card ≤ 20 ∧ J.card ≤ 20 ∧ J'.card ≤ 20 ∧
          X ^ (1 / 100 : ℝ) ≤
            smoothHeathBrownFactorScale (fsList.get selected) ∧
          smoothHeathBrownFactorScale (fsList.get selected) ≤
            (2 : ℝ) ^ 11 * Real.sqrt X ∧
          ∀ {H W : ℝ},
          X ^ ((5 / 8 : ℝ) + η) ≤ H →
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ X / H →
          ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          (residue : Fin fsList.length → ℕ) → residue selected < q →
          ∀ p : ℕ × (ℕ × ℕ),
          p ∈ smoothHeathBrownDPThreeGroupBlockIndexSet I J J' →
          ∀ (u V : ℝ), |u| ≤ W / 2 →
          V ∈ Set.Icc (X / H) ((X / H) * W ^ (4 : ℕ)) →
          let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
          let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
          let S₃ := smoothHeathBrownSubgroupScaleProduct fsList J'
          let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
          let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
          let h₃ : ℤ := (p.2.2 : ℤ) - (J'.card : ℤ)
          let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
          let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
          let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
          let Y := smoothHeathBrownThreeDyadicBlockProductScale
            S₁ S₂ S₃ h₁ h₂ h₃
          let eps := η / 2
          ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
            ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
                (smoothHeathBrownResidueGroupBlockTwistedCoefficient
                  (z := z) (fun i => fsList.get i) I q residue L₁ u) t *
              factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
                (smoothHeathBrownResidueGroupBlockTwistedCoefficient
                  (z := z) (fun i => fsList.get i) J q residue L₂ u) t *
              factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
                (smoothHeathBrownResidueGroupBlockTwistedCoefficient
                  (z := z) (fun i => fsList.get i) J' q residue L₃ u) t‖ ≤
            FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
              (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
                (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
                  Y ^ (-eps / 16 : ℝ)) := by
  obtain ⟨Cμ, Xsource, hCμ, hXsourceThree, hsourceOutput⟩ :=
    smoothHeathBrownThreeGroupActualResidueDPIntegral_of_IImaj
      (B := B) (κ := κ) (D := D) (η := η) hB hκ hD hη hηsmall
  refine ⟨Cμ, Xsource, hCμ, hXsourceThree, ?_⟩
  intro X z hXsource hz fsList hlen hfsne hret hE hIImaj
  obtain ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover,
      hIlo, hIhi, hgap, hselected, hIcard, hJcard, hJ'card,
      hNlo, hNhi, hsource⟩ :=
    hsourceOutput hXsource hz fsList hlen hfsne hret hE hIImaj
  refine ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover,
    hIlo, hIhi, hgap, hselected, hIcard, hJcard, hJ'card, hNlo, hNhi, ?_⟩
  intro H W hHlower hW hWtwo hWT0 q hq hqlog residue hresidue p hp u V hu hV
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < H := by
    have hpow : 0 < X ^ ((5 / 8 : ℝ) + η) :=
      Real.rpow_pos_of_pos hXpos _
    linarith
  have hT0upper : X / H ≤ X ^ ((3 / 8 : ℝ) - η) := by
    apply (div_le_iff₀ hHpos).2
    have hsum : ((3 / 8 : ℝ) - η) + ((5 / 8 : ℝ) + η) = 1 := by ring
    have hpow : X ^ ((3 / 8 : ℝ) - η) *
        X ^ ((5 / 8 : ℝ) + η) = X := by
      calc
        X ^ ((3 / 8 : ℝ) - η) * X ^ ((5 / 8 : ℝ) + η) =
            X ^ (((3 / 8 : ℝ) - η) + ((5 / 8 : ℝ) + η)) :=
          (Real.rpow_add hXpos ((3 / 8 : ℝ) - η)
            ((5 / 8 : ℝ) + η)).symm
        _ = X := by rw [hsum]; simp
    calc
      X = X ^ ((3 / 8 : ℝ) - η) * X ^ ((5 / 8 : ℝ) + η) := hpow.symm
      _ ≤ X ^ ((3 / 8 : ℝ) - η) * H :=
        mul_le_mul_of_nonneg_left hHlower
          (Real.rpow_nonneg hXpos.le _)
  have hSourceDP : ∀ (U : ℝ), W ≤ U →
      U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ) →
      ∀ (u : ℝ), |u| ≤ W / 2 →
      ∀ (q' : ℕ), 1 ≤ q' → (q' : ℝ) ≤ (Real.log X) ^ B →
      ∀ (residue' : Fin fsList.length → ℕ), residue' selected < q' →
      ∀ (h₁ h₂ h₃ : ℤ),
      (-(I.card : ℤ) ≤ h₁ ∧ h₁ < I.card) →
      (-(J.card : ℤ) ≤ h₂ ∧ h₂ < J.card) →
      (-(J'.card : ℤ) ≤ h₃ ∧ h₃ < J'.card) →
      let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
      let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
      let S₃ := smoothHeathBrownSubgroupScaleProduct fsList J'
      let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
      let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
      let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
      let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
      let eps := η / 2
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
        ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I q' residue' L₁ u) t *
          factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) J q' residue' L₂ u) t *
          factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) J' q' residue' L₃ u) t‖ ≤
        FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
          (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
            (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
              Y ^ (-eps / 16 : ℝ)) := by
    intro U hWU hU u hu q' hq' hq'log residue' hresidue' h₁ h₂ h₃ hh₁ hh₂ hh₃
    exact hsource hW hWtwo hWU hU u hu q' hq' hq'log residue' hresidue'
      h₁ h₂ h₃ hh₁ hh₂ hh₃
  have hblock := smoothHeathBrownDPThreeGroupBlockSourceInterval_fromShiftOutput
    (X := X) (z := z) (B := B) (κ := κ) (D := D) (η := η)
    (W := W) (T0 := X / H) fsList I J J' selected q residue hresidue p hp
    hWtwo hWT0 hT0upper hq hqlog hSourceDP
  exact hblock u V hu hV

/-- Derive the exact geometry needed by the actual-residue high-frequency
block estimate from retained factor scales, the approved three-group
partition, and the source logarithmic thresholds. The output keeps the
individual scales, product scale, exponent display, and envelope top endpoint
at their source values. -/
theorem smoothHeathBrownDPThreeGroupBlockGeometry_ofRetained
    {X η D W T0 : ℝ}
    (fsList : List (SmoothHeathBrownFactor X))
    (hlen : fsList.length ≤ 20) (hfsne : fsList ≠ [])
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fsList)
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hη : 0 < η) (hηsmall : η < 3 / 16) (hDnonneg : 0 ≤ D)
    (hlogThreshold : 10 ^ 6 / η ≤ Real.log X)
    (I J K : Finset (Fin fsList.length))
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K)
    (hcover : I ∪ J ∪ K = Finset.univ)
    (hE : 0 < smoothHeathBrownExponentSum fsList)
    (hIlo : (1 / 4 : ℝ) ≤
      subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I)
    (hIhi : subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ≤
      1 / 2)
    (hgap : |subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J -
      subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) K| ≤ 1 / 4)
    (p : ℕ × (ℕ × ℕ))
    (hp : p ∈ smoothHeathBrownDPThreeGroupBlockIndexSet I J K)
    (hW : W = (Real.log X) ^ D) (hWtwo : 2 ≤ W) (hWT0 : W ≤ T0)
    (hT0upper : T0 ≤ X ^ ((3 / 8 : ℝ) - η))
    (hlarge : (2 / (η / 2)) * Real.log
      ((2 : ℝ) ^ (42 * ((3 / 8 : ℝ) - η / 2)) *
        logAbsorptionM (η / 2) (4 * D)) ≤ Real.log X) :
    let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
    let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
    let S₃ := smoothHeathBrownSubgroupScaleProduct fsList K
    let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
    let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
    let h₃ : ℤ := (p.2.2 : ℤ) - (K.card : ℤ)
    let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
    let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
    let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
    let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
    let eps := η / 2
    (2 ≤ L₁ ∧ 2 ≤ L₂ ∧ 2 ≤ L₃) ∧
    (X / (2 : ℝ) ^ 42 ≤ Y ∧ Y ≤ (2 : ℝ) ^ 42 * X) ∧
    (2 : ℝ) ^ 16 ≤ Y ∧
    Y = L₁ * L₂ * L₃ ∧
    (0 < eps ∧ eps ≤ 3 / 16) ∧
    ((1 / 4 : ℝ) - eps / 100 ≤ Real.log L₁ / Real.log Y ∧
      Real.log L₁ / Real.log Y ≤ 1 / 2 + eps / 100 ∧
      |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
        1 / 4 + eps / 100) ∧
    T0 * W ^ (4 : ℕ) ≤ Y ^ ((3 / 8 : ℝ) - eps) ∧
    2 ≤ Y ^ ((3 / 8 : ℝ) - eps) := by
  classical
  dsimp only
  let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
  let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
  let S₃ := smoothHeathBrownSubgroupScaleProduct fsList K
  let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
  let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
  let h₃ : ℤ := (p.2.2 : ℤ) - (K.card : ℤ)
  let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
  let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
  let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
  let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
  let eps : ℝ := η / 2
  have hXnonneg : 0 ≤ X := by linarith
  have hPbounds := smoothHeathBrownSupportRetained_scale_bounds
    hlen hfsne hXnonneg hret
  have hPwindow : X / (2 : ℝ) ^ 22 ≤ smoothHeathBrownScaleProduct fsList ∧
      smoothHeathBrownScaleProduct fsList ≤ (2 : ℝ) ^ 22 * X := by
    constructor
    · simpa [div_eq_mul_inv, mul_comm] using hPbounds.1
    · exact hPbounds.2
  have hIratio :
      (1 / 4 : ℝ) ≤ Real.log S₁ /
          Real.log (smoothHeathBrownScaleProduct fsList) ∧
      Real.log S₁ / Real.log (smoothHeathBrownScaleProduct fsList) ≤ 1 / 2 := by
    constructor
    · rw [← smoothHeathBrownSubgroupWeightSum_eq_log_ratio fsList hE I]
      exact hIlo
    · rw [← smoothHeathBrownSubgroupWeightSum_eq_log_ratio fsList hE I]
      exact hIhi
  have hJKbalance :
      |Real.log S₂ / Real.log (smoothHeathBrownScaleProduct fsList) -
        Real.log S₃ / Real.log (smoothHeathBrownScaleProduct fsList)| ≤
          1 / 4 := by
    rw [← smoothHeathBrownSubgroupWeightSum_eq_log_ratio fsList hE J,
      ← smoothHeathBrownSubgroupWeightSum_eq_log_ratio fsList hE K]
    exact hgap
  have hshift := smoothHeathBrownDPThreeGroupBlock_shiftBounds I J K p hp
  have hLtwoRaw := smoothHeathBrownThreeDyadicBlockScales_ge_two
    fsList hlen hXscale hη hηsmall hlogThreshold I J K hIJ hIK hJK hcover
    hPwindow hIratio hJKbalance h₁ h₂ h₃ hshift.1 hshift.2.1 hshift.2.2
  have hLtwo : 2 ≤ L₁ ∧ 2 ≤ L₂ ∧ 2 ≤ L₃ := by
    simpa [L₁, L₂, L₃, S₁, S₂, S₃] using hLtwoRaw
  have hYwindowRaw := smoothHeathBrownThreeDyadicBlockProductScale_componentWindow
    fsList hlen I J K hIJ hIK hJK hcover hPwindow h₁ h₂ h₃
    hshift.1 hshift.2.1 hshift.2.2
  have hYwindow : X / (2 : ℝ) ^ 42 ≤ Y ∧ Y ≤ (2 : ℝ) ^ 42 * X := by
    simpa [Y, L₁, L₂, L₃, S₁, S₂, S₃] using hYwindowRaw
  have hYprod : Y = L₁ * L₂ * L₃ := by
    simp [Y, L₁, L₂, L₃, S₁, S₂, S₃,
      smoothHeathBrownThreeDyadicBlockProductScale,
      smoothHeathBrownDyadicBlockScale]
  have hexpRaw := smoothHeathBrownThreeGroupBlockExponentBounds
    fsList hlen hXscale hη hηsmall hlogThreshold I J K hIJ hIK hJK hcover
    hPwindow hIratio hJKbalance h₁ h₂ h₃ hshift.1 hshift.2.1 hshift.2.2
  have hexp :
      (1 / 4 : ℝ) - η / 200 ≤ Real.log L₁ / Real.log Y ∧
      Real.log L₁ / Real.log Y ≤ 1 / 2 + η / 200 ∧
      |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
        1 / 4 + η / 200 := by
    simpa [L₁, L₂, L₃, Y, S₁, S₂, S₃] using hexpRaw
  have hexpEps :
      (1 / 4 : ℝ) - eps / 100 ≤ Real.log L₁ / Real.log Y ∧
      Real.log L₁ / Real.log Y ≤ 1 / 2 + eps / 100 ∧
      |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
        1 / 4 + eps / 100 := by
    constructor
    · dsimp [eps]
      nlinarith [hexp.1]
    constructor
    · dsimp [eps]
      nlinarith [hexp.2.1]
    calc
      |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
          1 / 4 + η / 200 := hexp.2.2
      _ = 1 / 4 + eps / 100 := by dsimp [eps]; ring
  have hWnonneg : 0 ≤ W := by linarith [hWtwo]
  have hT0nonneg : 0 ≤ T0 := le_trans (by linarith [hWtwo]) hWT0
  have hWpow : 1 ≤ W ^ (4 : ℕ) := one_le_pow₀ (by linarith [hWtwo])
  let U := T0 * W ^ (4 : ℕ)
  have hWU : W ≤ U := by
    dsimp [U]
    calc
      W ≤ T0 := hWT0
      _ = T0 * 1 := by ring
      _ ≤ T0 * W ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_left hWpow hT0nonneg
  have hUupper : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ) := by
    dsimp [U]
    exact mul_le_mul_of_nonneg_right hT0upper (by positivity)
  have hYlower : X / (2 : ℝ) ^ 42 ≤ Y := hYwindow.1
  have htime := smoothHeathBrownThreeGroupBlockTimeWindow
    (X := X) (η := η) (D := D) (W := W) (U := U) (Y := Y)
    (T₀ := (Real.log X) ^ D / 2) (t := U) (u := 0)
    hXscale hη hηsmall hDnonneg hW hWtwo hWU hUupper hYlower hlarge rfl
    (by
      have hUpos : 0 ≤ U := mul_nonneg hT0nonneg (by positivity)
      constructor
      · rw [abs_of_nonneg hUpos]
        exact hWU
      · rw [abs_of_nonneg hUpos])
    (by nlinarith [hWtwo])
  rcases htime with ⟨hYlarge, _, hUtoY, _, _, _⟩
  have hT0top : T0 * W ^ (4 : ℕ) ≤ Y ^ ((3 / 8 : ℝ) - eps) := by
    simpa [U, eps] using hUtoY
  have hEps : 0 < eps ∧ eps ≤ 3 / 16 := by
    constructor
    · dsimp [eps]
      positivity
    · dsimp [eps]
      linarith [hηsmall]
  have hTtwo : 2 ≤ Y ^ ((3 / 8 : ℝ) - eps) := by
    have hYone : 1 ≤ Y := le_trans (by norm_num : (1 : ℝ) ≤ (2 : ℝ) ^ 16) hYlarge
    have hExponent : (1 / 8 : ℝ) ≤ (3 / 8 : ℝ) - eps := by
      dsimp [eps]
      linarith [hηsmall]
    have hExpMon := Real.rpow_le_rpow_of_exponent_le hYone hExponent
    have hBaseMon : ((2 : ℝ) ^ 16) ^ (1 / 8 : ℝ) ≤ Y ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hYlarge (by norm_num)
    have hBaseEq : ((2 : ℝ) ^ 16) ^ (1 / 8 : ℝ) = 4 := by norm_num
    have hFour : 4 ≤ Y ^ ((3 / 8 : ℝ) - eps) := by
      calc
        4 = ((2 : ℝ) ^ 16) ^ (1 / 8 : ℝ) := hBaseEq.symm
        _ ≤ Y ^ (1 / 8 : ℝ) := hBaseMon
        _ ≤ Y ^ ((3 / 8 : ℝ) - eps) := hExpMon
    linarith
  exact ⟨hLtwo, hYwindow, hYlarge, hYprod, hEps, hexpEps, hT0top, hTtwo⟩

/-- Close the actual-residue block mean envelope from its source low-frequency
interval bound. The high-frequency part is discharged by the checked
uncapped trilinear estimate in `smoothHeathBrownThreeGroupBlock_fourierIntegral_le`;
the remaining Fourier tail is bounded with the exact first-moment factor `2/W`.
The source kernel and arbitrary Mellin shift are unchanged. -/
theorem smoothHeathBrownThreeGroupBlock_fourierIntegral_le_of_sourceIntervals_firstMoment
    {X z κ : ℝ} {K : ℕ} (hX : 3 ≤ X)
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I₁ I₂ I₃ : Finset (Fin K))
    (hI₁ : I₁.card ≤ 20) (hI₂ : I₂.card ≤ 20) (hI₃ : I₃.card ≤ 20)
    (q : ℕ) (residue : Fin K → ℕ)
    (L₁ L₂ L₃ Y eps T0 W T : ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃)
    (hL₁two : 2 ≤ L₁) (hL₂two : 2 ≤ L₂) (hL₃two : 2 ≤ L₃)
    (hY : (2 : ℝ) ^ 16 ≤ Y) (hYprod : Y = L₁ * L₂ * L₃)
    (hEps0 : 0 < eps) (hEps : eps ≤ 3 / 16)
    (hTtwo : 2 ≤ T) (hTupper : T ≤ Y ^ ((3 / 8 : ℝ) - eps))
    (hαlower : 1 / 4 - eps / 100 ≤ Real.log L₁ / Real.log Y)
    (hαupper : Real.log L₁ / Real.log Y ≤ 1 / 2 + eps / 100)
    (hβγ : |Real.log L₂ / Real.log Y - Real.log L₃ / Real.log Y| ≤
      1 / 4 + eps / 100)
    (hW : 2 ≤ W) (hWT : W ≤ T0) (hVtop : T0 * W ^ 4 ≤ T)
    (hSourceInterval : ∀ (u V : ℝ), |u| ≤ W / 2 →
      V ∈ Set.Icc T0 (T0 * W ^ 4) →
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₁ q residue L₁ u) t *
          factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₂ q residue L₂ u) t *
          factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₃ q residue L₃ u) t‖ ≤
        FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
          (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
            (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
              Y ^ (-eps / 16 : ℝ))) :
    (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
      productDirichletMeanEnvelope
        (smoothHeathBrownThreeGroupBlockMellinFactors
          (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃)
        (fun _ : Fin 3 => (0 : Fin 1)) T0 W u) ≤
      (FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
        (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
          (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
            Y ^ (-eps / 16 : ℝ))) *
          (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖) +
        (Z 20 Y ^ 3 * FractionalPrimes.Literature.DirichletMean.J 20 *
          (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
            (1 + Y ^ (-eps / 16 : ℝ))) *
          ((2 / W) * (∫ u : ℝ, |u| *
            ‖mellinSeparationLogKernelFourier u‖)) := by
  have hXpos : 0 < X := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hYpos : 0 < Y := by positivity
  have hYgt : 1 < Y := by
    have hpow : 1 < (2 : ℝ) ^ 16 := by norm_num
    linarith
  have hlog4Ypos : 0 < Real.log (4 * Y) :=
    Real.log_pos (by nlinarith)
  have hZpos : 0 < Z 20 Y := by
    unfold Z
    positivity
  have hJpos : 0 < FractionalPrimes.Literature.DirichletMean.J 20 :=
    (FractionalPrimes.Literature.DirichletMean.constants_positive 20).2.2.2
  have hMlow : 0 ≤
      FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
        (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
          (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
            Y ^ (-eps / 16 : ℝ)) := by
    have hlog4Y : 0 ≤ Real.log (4 * Y) := le_of_lt hlog4Ypos
    have hlogX : 0 ≤ Real.log X := le_of_lt hlogXpos
    have hYnonneg : 0 ≤ Y := le_of_lt hYpos
    positivity
  have hWpos : 0 < W := by linarith
  let Ktail : ℝ := (2 / W) * (∫ u : ℝ,
    |u| * ‖mellinSeparationLogKernelFourier u‖)
  have hKernelTail :
      ∫ u in {u : ℝ | W / 2 < |u|},
        ‖mellinSeparationLogKernelFourier u‖ ≤ Ktail := by
    simpa [Ktail] using mellinSeparationLogKernelFourier_tail_le_firstMoment hWpos
  have hresult := smoothHeathBrownThreeGroupBlock_fourierIntegral_le_of_sourceIntervals
    (z := z) hX fs I₁ I₂ I₃ hI₁ hI₂ hI₃ q residue
    L₁ L₂ L₃ Y eps T0 W T
    (FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
      (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
        (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
          Y ^ (-eps / 16 : ℝ))) Ktail
    hL₁ hL₂ hL₃ hL₁two hL₂two hL₃two hY hYprod hEps0 hEps
    hTtwo hTupper hαlower hαupper hβγ hW hWT hVtop hMlow
    hSourceInterval hKernelTail
  simpa [Ktail, mul_assoc, mul_left_comm, mul_comm] using hresult

/-- Apply the retained-scale geometry and source interval to one actual
three-group block. This is the full per-block low/high-frequency envelope
bound: the source interval controls `|u| ≤ W/2`, the uncapped trilinear
estimate controls `|u| > W/2`, and the Fourier tail contributes `2/W`. -/
theorem smoothHeathBrownDPThreeGroupBlockEnvelope_ofSourceIntervalAndRetained
    {X z κ η D W T0 : ℝ}
    (fsList : List (SmoothHeathBrownFactor X))
    (hlen : fsList.length ≤ 20) (hfsne : fsList ≠ [])
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fsList)
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hη : 0 < η) (hηsmall : η < 3 / 16) (hDnonneg : 0 ≤ D)
    (hlogThreshold : 10 ^ 6 / η ≤ Real.log X)
    (I J K : Finset (Fin fsList.length))
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K)
    (hcover : I ∪ J ∪ K = Finset.univ)
    (hE : 0 < smoothHeathBrownExponentSum fsList)
    (hIlo : (1 / 4 : ℝ) ≤
      subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I)
    (hIhi : subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ≤
      1 / 2)
    (hgap : |subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J -
      subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) K| ≤ 1 / 4)
    (p : ℕ × (ℕ × ℕ))
    (hp : p ∈ smoothHeathBrownDPThreeGroupBlockIndexSet I J K)
    (hW : W = (Real.log X) ^ D) (hWtwo : 2 ≤ W) (hWT0 : W ≤ T0)
    (hT0upper : T0 ≤ X ^ ((3 / 8 : ℝ) - η))
    (hlarge : (2 / (η / 2)) * Real.log
      ((2 : ℝ) ^ (42 * ((3 / 8 : ℝ) - η / 2)) *
        logAbsorptionM (η / 2) (4 * D)) ≤ Real.log X)
    (q : ℕ) (residue : Fin fsList.length → ℕ)
    (hSourceInterval :
      let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
      let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
      let S₃ := smoothHeathBrownSubgroupScaleProduct fsList K
      let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
      let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
      let h₃ : ℤ := (p.2.2 : ℤ) - (K.card : ℤ)
      let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
      let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
      let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
      let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
      let eps := η / 2
      ∀ (u V : ℝ), |u| ≤ W / 2 →
      V ∈ Set.Icc T0 (T0 * W ^ (4 : ℕ)) →
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I q residue L₁ u) t *
          factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) J q residue L₂ u) t *
          factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) K q residue L₃ u) t‖ ≤
        FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
          (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
            (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
              Y ^ (-eps / 16 : ℝ))) :
    let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
    let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
    let S₃ := smoothHeathBrownSubgroupScaleProduct fsList K
    let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
    let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
    let h₃ : ℤ := (p.2.2 : ℤ) - (K.card : ℤ)
    let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
    let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
    let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
    let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
    let eps := η / 2
    (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
      productDirichletMeanEnvelope
        (smoothHeathBrownThreeGroupBlockMellinFactors
          (z := z) (fun i => fsList.get i) I J K q residue L₁ L₂ L₃)
        (fun _ : Fin 3 => (0 : Fin 1)) T0 W u) ≤
      (FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
        (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
          (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
            Y ^ (-eps / 16 : ℝ))) *
          (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖) +
        (Z 20 Y ^ 3 * FractionalPrimes.Literature.DirichletMean.J 20 *
          (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
            (1 + Y ^ (-eps / 16 : ℝ))) *
          ((2 / W) * (∫ u : ℝ, |u| *
            ‖mellinSeparationLogKernelFourier u‖)) := by
  classical
  dsimp only at hSourceInterval ⊢
  let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
  let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
  let S₃ := smoothHeathBrownSubgroupScaleProduct fsList K
  let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
  let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
  let h₃ : ℤ := (p.2.2 : ℤ) - (K.card : ℤ)
  let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
  let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
  let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
  let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
  let eps : ℝ := η / 2
  obtain ⟨hLtwo, hYwindow, hYlarge, hYprod, hEps, hexp, hVtop, hTtwo⟩ :=
    smoothHeathBrownDPThreeGroupBlockGeometry_ofRetained
      fsList hlen hfsne hret hXscale hη hηsmall hDnonneg hlogThreshold
      I J K hIJ hIK hJK hcover hE hIlo hIhi hgap p hp hW hWtwo hWT0
      hT0upper hlarge
  have hX : 3 ≤ X := by linarith [hXscale]
  have hIcard : I.card ≤ 20 := by
    exact le_trans (Finset.card_le_card (Finset.subset_univ I)) (by simpa using hlen)
  have hJcard : J.card ≤ 20 := by
    exact le_trans (Finset.card_le_card (Finset.subset_univ J)) (by simpa using hlen)
  have hKcard : K.card ≤ 20 := by
    exact le_trans (Finset.card_le_card (Finset.subset_univ K)) (by simpa using hlen)
  have hSourceInterval' : ∀ (u V : ℝ), |u| ≤ W / 2 →
      V ∈ Set.Icc T0 (T0 * W ^ (4 : ℕ)) →
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I q residue L₁ u) t *
          factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) J q residue L₂ u) t *
          factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) K q residue L₃ u) t‖ ≤
        FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
          (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
            (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
              Y ^ (-eps / 16 : ℝ)) := by
    simpa [S₁, S₂, S₃, h₁, h₂, h₃, L₁, L₂, L₃, Y, eps] using hSourceInterval
  have hEnvelope :=
    smoothHeathBrownThreeGroupBlock_fourierIntegral_le_of_sourceIntervals_firstMoment
      (z := z) (κ := κ) hX (fun i => fsList.get i) I J K
      hIcard hJcard hKcard q residue L₁ L₂ L₃ Y eps T0 W
      (Y ^ ((3 / 8 : ℝ) - eps))
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hLtwo.1)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hLtwo.2.1)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hLtwo.2.2)
      hLtwo.1 hLtwo.2.1 hLtwo.2.2 hYlarge hYprod
      hEps.1 hEps.2 hTtwo (by rfl)
      hexp.1 hexp.2.1 hexp.2.2 hWtwo hWT0 hVtop hSourceInterval'
  simpa [S₁, S₂, S₃, h₁, h₂, h₃, L₁, L₂, L₃, Y, eps] using hEnvelope

/-- The total mass of the exact angular Fourier kernel used by Mellin
separation. -/
noncomputable def smoothHeathBrownDPFourierKernelMass : ℝ :=
  ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖

/-- The first absolute moment of the exact angular Fourier kernel used by
Mellin separation. -/
noncomputable def smoothHeathBrownDPFourierKernelFirstMoment : ℝ :=
  ∫ u : ℝ, |u| * ‖mellinSeparationLogKernelFourier u‖

/-- The logarithmic exponent obtained after expanding the three divisor-moment
factors in `Z 20 Y`. -/
def smoothHeathBrownDPBlockLogExponent : ℕ := b 20 + 3 * 2 ^ 20

/-- A fixed numerical constant for the source low/high Fourier split. It
contains only the exact trilinear constant, numerical scale factors, and the
two fixed kernel integrals. -/
noncomputable def smoothHeathBrownDPBlockFourierConstant : ℝ :=
  J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
      (2 : ℝ) ^ smoothHeathBrownDPBlockLogExponent * (2 : ℝ) ^ 21 *
      (2 * smoothHeathBrownDPFourierKernelMass +
        4 * smoothHeathBrownDPFourierKernelFirstMoment)

theorem smoothHeathBrownDPFourierKernelMass_nonneg :
    0 ≤ smoothHeathBrownDPFourierKernelMass := by
  unfold smoothHeathBrownDPFourierKernelMass
  exact integral_nonneg (fun u => norm_nonneg _)

theorem smoothHeathBrownDPFourierKernelFirstMoment_nonneg :
    0 ≤ smoothHeathBrownDPFourierKernelFirstMoment := by
  unfold smoothHeathBrownDPFourierKernelFirstMoment
  exact integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (norm_nonneg _))

/-- Numerical conversion of the exact three-group low/high-frequency
envelope. The group and residue arithmetic is deliberately not hidden here:
`hEnvelope` is the checked actual-residue block envelope, whose low-frequency
input is supplied by the fixed selected-group source branch. The output has
the source logarithmic exponent `m=b₂₀+3·2²⁰` and keeps the three distinct
savings from the source proof. -/
theorem smoothHeathBrownDPThreeGroupBlockUniformNumerical_ofEnvelope
    {X Y η κ D W E : ℝ}
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hYlower : X / (2 : ℝ) ^ 42 ≤ Y)
    (hYupper : Y ≤ (2 : ℝ) ^ 42 * X)
    (hYlarge : (2 : ℝ) ^ 16 ≤ Y)
    (hη : 0 < η) (hηsmall : η < 3 / 16)
    (hW : W = (Real.log X) ^ D)
    (hEnvelope : E ≤
      (J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y *
            (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
              Y ^ (-((η / 2) / 16 : ℝ)))) *
          smoothHeathBrownDPFourierKernelMass +
        (Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y * (1 + Y ^ (-((η / 2) / 16 : ℝ)))) *
          ((2 / W) * smoothHeathBrownDPFourierKernelFirstMoment)) :
    E ≤ smoothHeathBrownDPBlockFourierConstant * Real.sqrt X *
      (Real.log X) ^ smoothHeathBrownDPBlockLogExponent *
        ((Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
          (Real.log X) ^ (-D)) := by
  have hXpos : 0 < X := by
    have hpow : 0 < (2 : ℝ) ^ 200 := by positivity
    exact lt_of_lt_of_le hpow hXscale
  have hXone : 1 ≤ X := by
    have hpow : 1 ≤ (2 : ℝ) ^ 200 := by norm_num
    exact hpow.trans hXscale
  have hXstrict : 1 < X := by
    have hpow : 1 < (2 : ℝ) ^ 200 := by norm_num
    exact lt_of_lt_of_le hpow hXscale
  have hlogXpos : 0 < Real.log X := Real.log_pos hXstrict
  have hlogXnonneg : 0 ≤ Real.log X := hlogXpos.le
  have hYpos : 0 < Y := by
    have hbase : 0 < (2 : ℝ) ^ 16 := by positivity
    exact lt_of_lt_of_le hbase hYlarge
  have hYone : 1 ≤ Y := by
    have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ 16 := by norm_num
    exact hbase.trans hYlarge
  have h4Yone : 1 < 4 * Y := by nlinarith [hYlarge]
  have h4Ypos : 0 < 4 * Y := mul_pos (by norm_num) hYpos
  have hlog4Ypos : 0 < Real.log (4 * Y) := Real.log_pos h4Yone
  have h2pow44le : (2 : ℝ) ^ 44 ≤ X := by
    have hpow : (2 : ℝ) ^ 44 ≤ (2 : ℝ) ^ 200 := by norm_num
    exact hpow.trans hXscale
  have hlog44 : 44 * Real.log 2 ≤ Real.log X := by
    have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ 44)
      h2pow44le
    rw [Real.log_pow] at hlog
    exact hlog
  have h4Yle : 4 * Y ≤ (2 : ℝ) ^ 44 * X := by
    have hpow : (2 : ℝ) ^ 44 = 4 * (2 : ℝ) ^ 42 := by
      rw [show (44 : ℕ) = 2 + 42 by omega, pow_add]
      norm_num
    calc
      4 * Y ≤ 4 * ((2 : ℝ) ^ 42 * X) :=
        mul_le_mul_of_nonneg_left hYupper (by norm_num)
      _ = (2 : ℝ) ^ 44 * X := by
        calc
          4 * ((2 : ℝ) ^ 42 * X) = (4 * (2 : ℝ) ^ 42) * X := by ring
          _ = (2 : ℝ) ^ 44 * X := by rw [← hpow]
  have hlog4Y : Real.log (4 * Y) ≤ 2 * Real.log X := by
    calc
      Real.log (4 * Y) ≤ Real.log ((2 : ℝ) ^ 44 * X) :=
        Real.log_le_log h4Ypos h4Yle
      _ = 44 * Real.log 2 + Real.log X := by
        rw [Real.log_mul (by positivity) hXpos.ne', Real.log_pow]
        norm_num
      _ ≤ 2 * Real.log X := by linarith
  have hlogXpowNonneg : 0 ≤ (Real.log X) ^
      (smoothHeathBrownDPBlockLogExponent : ℕ) := by positivity
  have hlog4powZ :
      (Real.log (4 * Y)) ^ (2 ^ 20 - 1) ≤
        (2 * Real.log X) ^ (2 ^ 20 - 1) :=
    pow_le_pow_left₀ hlog4Ypos.le hlog4Y (2 ^ 20 - 1)
  have hZ : Z 20 Y ≤
      (2 : ℝ) ^ (2 ^ 20 + 1) *
        (2 * Real.log X) ^ (2 ^ 20 - 1) := by
    rw [Z]
    exact mul_le_mul_of_nonneg_left hlog4powZ (by positivity)
  have hZnonneg : 0 ≤ Z 20 Y := by
    rw [Z]
    positivity
  have hZcube := pow_le_pow_left₀ hZnonneg hZ 3
  have hZcube' : Z 20 Y ^ 3 ≤
      (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
        (2 * Real.log X) ^ (3 * (2 ^ 20 - 1)) := by
    calc
      Z 20 Y ^ 3 ≤
          ((2 : ℝ) ^ (2 ^ 20 + 1) *
            (2 * Real.log X) ^ (2 ^ 20 - 1)) ^ 3 := hZcube
      _ = (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ (3 * (2 ^ 20 - 1)) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 1 <;> congr 1 <;> omega
  have hlogpow :
      (Real.log (4 * Y)) ^ (b 20 + 3) ≤
        (2 * Real.log X) ^ (b 20 + 3) :=
    pow_le_pow_left₀ hlog4Ypos.le hlog4Y (b 20 + 3)
  have hmexp : 3 * (2 ^ 20 - 1) + (b 20 + 3) =
      smoothHeathBrownDPBlockLogExponent := by
    change 3 * (2 ^ 20 - 1) + (b 20 + 3) = b 20 + 3 * 2 ^ 20
    omega
  have hlogProduct :
      Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) ≤
        (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
          (2 * Real.log X) ^ smoothHeathBrownDPBlockLogExponent := by
    calc
      Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) ≤
          ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ (3 * (2 ^ 20 - 1))) *
              (Real.log (4 * Y)) ^ (b 20 + 3) :=
        mul_le_mul_of_nonneg_right hZcube' (by positivity)
      _ ≤ ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ (3 * (2 ^ 20 - 1))) *
              (2 * Real.log X) ^ (b 20 + 3) :=
        mul_le_mul_of_nonneg_left hlogpow (by positivity)
      _ = (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ smoothHeathBrownDPBlockLogExponent := by
        rw [mul_assoc, ← pow_add, hmexp]
  have hlogProduct' :
      Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) ≤
        (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) * (2 : ℝ) ^
          smoothHeathBrownDPBlockLogExponent *
          (Real.log X) ^ smoothHeathBrownDPBlockLogExponent := by
    calc
      _ ≤ (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
          (2 * Real.log X) ^ smoothHeathBrownDPBlockLogExponent := hlogProduct
      _ = _ := by rw [mul_pow]; ring
  have hsqrtY : Real.sqrt Y ≤ (2 : ℝ) ^ 21 * Real.sqrt X := by
    calc
      Real.sqrt Y ≤ Real.sqrt ((2 : ℝ) ^ 42 * X) := Real.sqrt_le_sqrt hYupper
      _ = Real.sqrt ((2 : ℝ) ^ 42) * Real.sqrt X :=
        Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ 42) X
      _ = (2 : ℝ) ^ 21 * Real.sqrt X := by
        rw [show (2 : ℝ) ^ 42 = ((2 : ℝ) ^ 21) ^ 2 by norm_num [pow_mul],
          Real.sqrt_sq_eq_abs]
        norm_num
  let m : ℕ := smoothHeathBrownDPBlockLogExponent
  let C : ℝ := J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
    (2 : ℝ) ^ m * (2 : ℝ) ^ 21
  have hJnonneg : 0 ≤ J 20 := by
    simp [J, K]
  have hCoeff :
      J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y ≤ C * Real.sqrt X * (Real.log X) ^ m := by
    calc
      J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y =
        J 20 * (Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3)) *
          Real.sqrt Y := by ring
      _ ≤ J 20 * ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) * (2 : ℝ) ^ m *
            (Real.log X) ^ m) * Real.sqrt Y := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogProduct' hJnonneg)
          (Real.sqrt_nonneg Y)
      _ ≤ J 20 * ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) * (2 : ℝ) ^ m *
            (Real.log X) ^ m) * ((2 : ℝ) ^ 21 * Real.sqrt X) :=
        mul_le_mul_of_nonneg_left hsqrtY (by positivity)
      _ = C * Real.sqrt X * (Real.log X) ^ m := by
        dsimp [C, m]
        ring
  have hCoeffHigh :
      Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y ≤ C * Real.sqrt X * (Real.log X) ^ m := by
    calc
      Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y =
        J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y := by ring
      _ ≤ C * Real.sqrt X * (Real.log X) ^ m := hCoeff
  let Pbase : ℝ := C * Real.sqrt X * (Real.log X) ^ m
  let a : ℝ := η / 32
  have ha : 0 < a := by dsimp [a]; positivity
  have hYdecay : Y ^ (-a) ≤ 2 * X ^ (-a) := by
    have hbasepos : 0 < X / (2 : ℝ) ^ 42 := div_pos hXpos (by positivity)
    have hmon := Real.rpow_le_rpow_of_nonpos hbasepos hYlower
      (neg_nonpos.mpr ha.le)
    have hdivpow :
        (X / (2 : ℝ) ^ 42) ^ (-a) =
          (2 : ℝ) ^ (42 * a) * X ^ (-a) := by
      have hbasepow : ((2 : ℝ) ^ 42) ^ a = (2 : ℝ) ^ (42 * a) := by
        exact (Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) 42 a).symm
      have hden : ((2 : ℝ) ^ 42) ^ (-a) =
          (((2 : ℝ) ^ 42) ^ a)⁻¹ := by
        rw [Real.rpow_neg (by positivity)]
      calc
        (X / (2 : ℝ) ^ 42) ^ (-a) =
            X ^ (-a) / ((2 : ℝ) ^ 42) ^ (-a) :=
          Real.div_rpow hXpos.le (by positivity) (-a)
        _ = X ^ (-a) * ((2 : ℝ) ^ 42) ^ a := by
          rw [div_eq_mul_inv, hden, inv_inv]
        _ = X ^ (-a) * (2 : ℝ) ^ (42 * a) := by rw [hbasepow]
        _ = (2 : ℝ) ^ (42 * a) * X ^ (-a) := by ring
    have hconst : (2 : ℝ) ^ (42 * a) ≤ 2 := by
      calc
        (2 : ℝ) ^ (42 * a) ≤ (2 : ℝ) ^ 1 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            dsimp [a]
            nlinarith [hηsmall])
        _ = 2 := by norm_num
    calc
      Y ^ (-a) ≤ (X / (2 : ℝ) ^ 42) ^ (-a) := hmon
      _ = (2 : ℝ) ^ (42 * a) * X ^ (-a) := hdivpow
      _ ≤ 2 * X ^ (-a) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hXpos.le _)
  have hYdecay' :
      Y ^ (-((η / 2) / 16 : ℝ)) ≤ 2 * X ^ (-η / 32 : ℝ) := by
    convert hYdecay using 1 <;> congr 1 <;> dsimp [a] <;> ring
  have hYsmall : Y ^ (-((η / 2) / 16 : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hYone
    have : 0 < (η / 2) / 16 := by positivity
    linarith
  have hlowid :
      ((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) =
        (Real.log X) ^ (-κ / 16 : ℝ) := by
    rw [← Real.rpow_mul hlogXnonneg (-κ) (1 / 16 : ℝ)]
    congr 1
    ring
  have hWpos : 0 < W := by
    rw [hW]
    exact Real.rpow_pos_of_pos hlogXpos _
  have htail : 2 / W = 2 * (Real.log X) ^ (-D : ℝ) := by
    calc
      2 / W = 2 / ((Real.log X) ^ D) := by rw [hW]
      _ = 2 * (Real.log X) ^ (-D : ℝ) := by
        rw [Real.rpow_neg hlogXpos.le]
        ring
  have hK0 : 0 ≤ smoothHeathBrownDPFourierKernelMass :=
    smoothHeathBrownDPFourierKernelMass_nonneg
  have hK1 : 0 ≤ smoothHeathBrownDPFourierKernelFirstMoment :=
    smoothHeathBrownDPFourierKernelFirstMoment_nonneg
  have hlogPowerNonneg : 0 ≤ (Real.log X) ^ m := by
    positivity
  have hPnonneg : 0 ≤ C * Real.sqrt X * (Real.log X) ^ m := by
    dsimp [C]
    positivity
  have hsumNonneg :
      0 ≤ (Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
        (Real.log X) ^ (-D : ℝ) := by
    positivity
  have hlowfactor :
      ((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
          Y ^ (-((η / 2) / 16 : ℝ)) ≤
        (Real.log X) ^ (-κ / 16 : ℝ) + 2 * X ^ (-η / 32 : ℝ) := by
    rw [hlowid]
    exact add_le_add le_rfl hYdecay'
  have hhighfactor :
      1 + Y ^ (-((η / 2) / 16 : ℝ)) ≤ 2 := by linarith [hYsmall]
  have hbracket :
      smoothHeathBrownDPFourierKernelMass *
          ((Real.log X) ^ (-κ / 16 : ℝ) + 2 * X ^ (-η / 32 : ℝ)) +
        4 * smoothHeathBrownDPFourierKernelFirstMoment *
          (Real.log X) ^ (-D : ℝ) ≤
        (2 * smoothHeathBrownDPFourierKernelMass +
          4 * smoothHeathBrownDPFourierKernelFirstMoment) *
          ((Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
            (Real.log X) ^ (-D : ℝ)) := by
    have hA : 0 ≤ (Real.log X) ^ (-κ / 16 : ℝ) := by positivity
    have hB : 0 ≤ X ^ (-η / 32 : ℝ) := by positivity
    have hC : 0 ≤ (Real.log X) ^ (-D : ℝ) := by positivity
    have hA' : 0 ≤
        (smoothHeathBrownDPFourierKernelMass +
          4 * smoothHeathBrownDPFourierKernelFirstMoment) *
          (Real.log X) ^ (-κ / 16 : ℝ) :=
      mul_nonneg (by positivity) hA
    have hB' : 0 ≤
        (4 * smoothHeathBrownDPFourierKernelFirstMoment) *
          X ^ (-η / 32 : ℝ) :=
      mul_nonneg (by positivity) hB
    have hC' : 0 ≤
        (2 * smoothHeathBrownDPFourierKernelMass) *
          (Real.log X) ^ (-D : ℝ) :=
      mul_nonneg (by positivity) hC
    nlinarith [hA', hB', hC']
  have hraw' : E ≤
      Pbase *
        (smoothHeathBrownDPFourierKernelMass *
            ((Real.log X) ^ (-κ / 16 : ℝ) + 2 * X ^ (-η / 32 : ℝ)) +
          4 * smoothHeathBrownDPFourierKernelFirstMoment *
            (Real.log X) ^ (-D : ℝ)) := by
    calc
      E ≤
          (J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
              Real.sqrt Y *
              (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
                Y ^ (-((η / 2) / 16 : ℝ)))) *
              smoothHeathBrownDPFourierKernelMass +
            (Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
              Real.sqrt Y * (1 + Y ^ (-((η / 2) / 16 : ℝ)))) *
              ((2 / W) * smoothHeathBrownDPFourierKernelFirstMoment) := hEnvelope
      _ ≤ Pbase *
            (smoothHeathBrownDPFourierKernelMass *
                ((Real.log X) ^ (-κ / 16 : ℝ) + 2 * X ^ (-η / 32 : ℝ)) +
              4 * smoothHeathBrownDPFourierKernelFirstMoment *
                (Real.log X) ^ (-D : ℝ)) := by
        have hlowFactorNonneg :
            0 ≤ ((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
              Y ^ (-((η / 2) / 16 : ℝ)) := by positivity
        have hlowTerm' :
            (J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
              Real.sqrt Y *
              (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
                Y ^ (-((η / 2) / 16 : ℝ)))) *
              smoothHeathBrownDPFourierKernelMass ≤
              Pbase * (smoothHeathBrownDPFourierKernelMass *
                ((Real.log X) ^ (-κ / 16 : ℝ) +
                  2 * X ^ (-η / 32 : ℝ))) := by
          calc
            _ ≤ (Pbase *
                (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
                  Y ^ (-((η / 2) / 16 : ℝ)))) *
                  smoothHeathBrownDPFourierKernelMass := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hCoeff
                  hlowFactorNonneg)
                hK0
            _ ≤ (Pbase *
                ((Real.log X) ^ (-κ / 16 : ℝ) +
                  2 * X ^ (-η / 32 : ℝ))) *
                  smoothHeathBrownDPFourierKernelMass := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlowfactor hPnonneg)
                hK0
            _ = _ := by ring
        have hhighFactorNonneg :
            0 ≤ 1 + Y ^ (-((η / 2) / 16 : ℝ)) := by positivity
        have hhighTerm' :
            (Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
              Real.sqrt Y * (1 + Y ^ (-((η / 2) / 16 : ℝ)))) *
              ((2 / W) * smoothHeathBrownDPFourierKernelFirstMoment) ≤
              Pbase * (4 * smoothHeathBrownDPFourierKernelFirstMoment *
                (Real.log X) ^ (-D : ℝ)) := by
          have hcoeff' :
              (Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
                Real.sqrt Y) *
                (1 + Y ^ (-((η / 2) / 16 : ℝ)) ) ≤ Pbase * 2 := by
            calc
              _ ≤ Pbase * (1 + Y ^ (-((η / 2) / 16 : ℝ))) :=
                mul_le_mul_of_nonneg_right hCoeffHigh hhighFactorNonneg
              _ ≤ Pbase * 2 :=
                mul_le_mul_of_nonneg_left hhighfactor hPnonneg
          calc
            _ ≤ (Pbase * 2) *
                ((2 / W) * smoothHeathBrownDPFourierKernelFirstMoment) :=
              mul_le_mul_of_nonneg_right hcoeff'
                (mul_nonneg (div_nonneg (by norm_num) hWpos.le) hK1)
            _ = Pbase * (4 * smoothHeathBrownDPFourierKernelFirstMoment *
                (Real.log X) ^ (-D : ℝ)) := by rw [htail]; ring
        calc
          _ ≤ Pbase * (smoothHeathBrownDPFourierKernelMass *
                ((Real.log X) ^ (-κ / 16 : ℝ) +
                  2 * X ^ (-η / 32 : ℝ))) +
              Pbase * (4 * smoothHeathBrownDPFourierKernelFirstMoment *
                (Real.log X) ^ (-D : ℝ)) :=
            add_le_add hlowTerm' hhighTerm'
          _ = _ := by ring
  calc
    E ≤ Pbase *
        (smoothHeathBrownDPFourierKernelMass *
            ((Real.log X) ^ (-κ / 16 : ℝ) + 2 * X ^ (-η / 32 : ℝ)) +
          4 * smoothHeathBrownDPFourierKernelFirstMoment *
            (Real.log X) ^ (-D : ℝ)) := hraw'
    _ ≤ C * Real.sqrt X * (Real.log X) ^ m *
        ((2 * smoothHeathBrownDPFourierKernelMass +
          4 * smoothHeathBrownDPFourierKernelFirstMoment) *
          ((Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
            (Real.log X) ^ (-D : ℝ))) :=
      mul_le_mul_of_nonneg_left hbracket hPnonneg
    _ = smoothHeathBrownDPBlockFourierConstant * Real.sqrt X *
        (Real.log X) ^ smoothHeathBrownDPBlockLogExponent *
          ((Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
            (Real.log X) ^ (-D : ℝ)) := by
      change (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
          (2 : ℝ) ^ m * (2 : ℝ) ^ 21) * Real.sqrt X *
          (Real.log X) ^ m *
          ((2 * smoothHeathBrownDPFourierKernelMass +
            4 * smoothHeathBrownDPFourierKernelFirstMoment) *
            ((Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
              (Real.log X) ^ (-D : ℝ))) =
        (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
          (2 : ℝ) ^ m * (2 : ℝ) ^ 21 *
          (2 * smoothHeathBrownDPFourierKernelMass +
            4 * smoothHeathBrownDPFourierKernelFirstMoment)) *
          Real.sqrt X * (Real.log X) ^ m *
          ((Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
            (Real.log X) ^ (-D : ℝ))
      ring

/-- The source block Mellin factors are evaluated at their zero residue tuple. -/
def smoothHeathBrownDPThreeGroupBlockResidues
    {X : ℝ} {q : ℕ} (fsList : List (SmoothHeathBrownFactor X))
    (b : Fin fsList.length → Fin q) (p : ℕ × (ℕ × ℕ)) :
    Fin 3 → Fin 1 := fun _ => 0

/-- Source-facing numerical estimate for the actual retained three-group
block. The fixed `IImaj` witness supplies the exact residue-restricted source
interval input; the larger threshold below also exposes the logarithmic and
product-scale threshold facts needed by the block geometry and absorption.
The remaining group, residue, shift, and Mellin variables retain their source
quantifiers. -/
theorem smoothHeathBrownDPThreeGroupBlockUniformNumerical_of_IImaj
    {B κ D η : ℝ} (hB : 0 < B) (hκ : 0 < κ)
    (hD : 2 * κ + 10 ≤ D) (hη : 0 < η) (hηsmall : η < 3 / 16) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fsList : List (SmoothHeathBrownFactor X)) →
        fsList.length ≤ 20 → fsList ≠ [] →
        smoothHeathBrownSupportRetained
          (X := X) (z := dyadicMobiusCutoff X) fsList →
        (hE : 0 < smoothHeathBrownExponentSum fsList) →
        (smoothHeathBrownExponentGrouping fsList hE).IImaj (5 / 8) →
        ∃ I J J' : Finset (Fin fsList.length), ∃ selected : Fin fsList.length,
          Disjoint I J ∧ Disjoint I J' ∧ Disjoint J J' ∧
          I ∪ J ∪ J' = Finset.univ ∧
          (1 / 4 : ℝ) ≤
            subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ∧
          subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ≤
            1 / 2 ∧
          |subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J -
            subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J'| ≤
              1 / 4 ∧
          selected ∈ I ∧ I.card ≤ 20 ∧ J.card ≤ 20 ∧ J'.card ≤ 20 ∧
          X ^ (1 / 100 : ℝ) ≤
            smoothHeathBrownFactorScale (fsList.get selected) ∧
          smoothHeathBrownFactorScale (fsList.get selected) ≤
            (2 : ℝ) ^ 11 * Real.sqrt X ∧
          (2 : ℝ) ^ 200 ≤ X ∧
          ∀ {H W : ℝ},
          X ^ ((5 / 8 : ℝ) + η) ≤ H →
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ X / H →
          ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          (residue : Fin fsList.length → ℕ) → residue selected < q →
          ∀ p : ℕ × (ℕ × ℕ),
          p ∈ smoothHeathBrownDPThreeGroupBlockIndexSet I J J' →
          ∀ u : ℝ, |u| ≤ W / 2 →
          let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
          let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
          let S₃ := smoothHeathBrownSubgroupScaleProduct fsList J'
          let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
          let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
          let h₃ : ℤ := (p.2.2 : ℤ) - (J'.card : ℤ)
          let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
          let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
          let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
          let Y := smoothHeathBrownThreeDyadicBlockProductScale
            S₁ S₂ S₃ h₁ h₂ h₃
          (∫ u' : ℝ, ‖mellinSeparationLogKernelFourier u'‖ *
            productDirichletMeanEnvelope
              (smoothHeathBrownThreeGroupBlockMellinFactors
                (z := z) (fun i => fsList.get i) I J J' q residue
                L₁ L₂ L₃)
              (fun _ : Fin 3 => (0 : Fin 1))
              (X / H) W u') ≤
            smoothHeathBrownDPBlockFourierConstant * Real.sqrt X *
              (Real.log X) ^ smoothHeathBrownDPBlockLogExponent *
                ((Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
                  (Real.log X) ^ (-D)) := by
  obtain ⟨Cμ, Xsource, hCμ, hXsourceThree, hsourceOutput⟩ :=
    smoothHeathBrownDPThreeGroupBlockSourceInterval_of_IImaj
      (B := B) (κ := κ) (D := D) (η := η) hB hκ hD hη hηsmall
  let Rlog : ℝ := 10 ^ 6 / η
  let Rlarge : ℝ := (2 / (η / 2)) * Real.log
    ((2 : ℝ) ^ (42 * ((3 / 8 : ℝ) - η / 2)) *
      logAbsorptionM (η / 2) (4 * D))
  let R : ℝ := max Rlog Rlarge
  let X₀ : ℝ := max Xsource
    (max ((2 : ℝ) ^ 200) (Real.exp R))
  have hX₀three : 3 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans hXsourceThree (le_max_left _ _)
  refine ⟨X₀, hX₀three, ?_⟩
  intro X z hX₀X hz fsList hlen hfsne hret hE hIImaj
  have hXsource : Xsource ≤ X :=
    le_trans (le_max_left _ _) hX₀X
  have hXscale : (2 : ℝ) ^ 200 ≤ X := by
    have hpowX₀ : (2 : ℝ) ^ 200 ≤ X₀ := by
      dsimp [X₀]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact hpowX₀.trans hX₀X
  have hexpRX : Real.exp R ≤ X := by
    have hX₀exp : Real.exp R ≤ X₀ := by
      dsimp [X₀]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact hX₀exp.trans hX₀X
  have hRlelog : R ≤ Real.log X := by
    have hlog := Real.log_le_log (Real.exp_pos R) hexpRX
    simpa using hlog
  have hRlelog' : max Rlog Rlarge ≤ Real.log X := by
    simpa [R] using hRlelog
  have hlogThreshold : 10 ^ 6 / η ≤ Real.log X := by
    simpa [Rlog] using le_trans (le_max_left Rlog Rlarge) hRlelog'
  have hlarge : (2 / (η / 2)) * Real.log
      ((2 : ℝ) ^ (42 * ((3 / 8 : ℝ) - η / 2)) *
        logAbsorptionM (η / 2) (4 * D)) ≤ Real.log X := by
    simpa [Rlarge] using le_trans (le_max_right Rlog Rlarge) hRlelog'
  obtain ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover,
      hIlo, hIhi, hgap, hselected, hIcard, hJcard, hJ'card,
      hNlo, hNhi, hsource⟩ :=
    hsourceOutput hXsource hz fsList hlen hfsne hret hE hIImaj
  refine ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover,
    hIlo, hIhi, hgap, hselected, hIcard, hJcard, hJ'card,
    hNlo, hNhi, hXscale, ?_⟩
  intro H W hHlower hW hWtwo hWT0 q hq hqlog residue hresidue p hp u hu
  have hXpos : 0 < X := by linarith [hXscale]
  have hHpos : 0 < H := by
    have hpow : 0 < X ^ ((5 / 8 : ℝ) + η) :=
      Real.rpow_pos_of_pos hXpos _
    linarith
  have hT0upper : X / H ≤ X ^ ((3 / 8 : ℝ) - η) := by
    apply (div_le_iff₀ hHpos).2
    have hsum : ((3 / 8 : ℝ) - η) + ((5 / 8 : ℝ) + η) = 1 := by ring
    have hpow : X ^ ((3 / 8 : ℝ) - η) *
        X ^ ((5 / 8 : ℝ) + η) = X := by
      calc
        X ^ ((3 / 8 : ℝ) - η) * X ^ ((5 / 8 : ℝ) + η) =
            X ^ (((3 / 8 : ℝ) - η) + ((5 / 8 : ℝ) + η)) :=
          (Real.rpow_add hXpos ((3 / 8 : ℝ) - η)
            ((5 / 8 : ℝ) + η)).symm
        _ = X := by rw [hsum]; simp
    calc
      X = X ^ ((3 / 8 : ℝ) - η) * X ^ ((5 / 8 : ℝ) + η) := hpow.symm
      _ ≤ X ^ ((3 / 8 : ℝ) - η) * H :=
        mul_le_mul_of_nonneg_left hHlower
          (Real.rpow_nonneg hXpos.le _)
  let T0 : ℝ := X / H
  have hSourceInterval :
      let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
      let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
      let S₃ := smoothHeathBrownSubgroupScaleProduct fsList J'
      let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
      let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
      let h₃ : ℤ := (p.2.2 : ℤ) - (J'.card : ℤ)
      let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
      let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
      let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
      let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
      let eps := η / 2
      ∀ (u' V : ℝ), |u'| ≤ W / 2 →
      V ∈ Set.Icc T0 (T0 * W ^ (4 : ℕ)) →
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial (Y ^ (Real.log L₁ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) I q residue L₁ u') t *
          factorPolynomial (Y ^ (Real.log L₂ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) J q residue L₂ u') t *
          factorPolynomial (Y ^ (Real.log L₃ / Real.log Y))
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) (fun i => fsList.get i) J' q residue L₃ u') t‖ ≤
        FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
          (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
            (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
              Y ^ (-(η / 2) / 16 : ℝ)) := by
    simpa [T0] using
      (hsource hHlower hW hWtwo hWT0 q hq hqlog residue hresidue p hp)
  have hraw :=
    smoothHeathBrownDPThreeGroupBlockEnvelope_ofSourceIntervalAndRetained
      (X := X) (z := z) (κ := κ) (η := η) (D := D) (W := W)
      (T0 := T0) fsList hlen hfsne hret hXscale hη hηsmall
      (by linarith [hD]) hlogThreshold I J J' hIJ hIJ' hJJ' hcover hE
      hIlo hIhi hgap p hp hW hWtwo hWT0 hT0upper hlarge q residue
      hSourceInterval
  let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
  let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
  let S₃ := smoothHeathBrownSubgroupScaleProduct fsList J'
  let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
  let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
  let h₃ : ℤ := (p.2.2 : ℤ) - (J'.card : ℤ)
  let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
  let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
  let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
  let Y := smoothHeathBrownThreeDyadicBlockProductScale S₁ S₂ S₃ h₁ h₂ h₃
  let E := ∫ u' : ℝ, ‖mellinSeparationLogKernelFourier u'‖ *
    productDirichletMeanEnvelope
      (smoothHeathBrownThreeGroupBlockMellinFactors
        (z := z) (fun i => fsList.get i) I J J' q residue L₁ L₂ L₃)
      (fun _ : Fin 3 => (0 : Fin 1)) T0 W u'
  have hEnvelope : E ≤
      (FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
        (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
          (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
            Y ^ (-(η / 2) / 16 : ℝ))) *
        smoothHeathBrownDPFourierKernelMass +
      (Z 20 Y ^ 3 * FractionalPrimes.Literature.DirichletMean.J 20 *
        (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
          (1 + Y ^ (-(η / 2) / 16 : ℝ))) *
        ((2 / W) * smoothHeathBrownDPFourierKernelFirstMoment) := by
    simpa [E, S₁, S₂, S₃, h₁, h₂, h₃, L₁, L₂, L₃, Y, T0,
      smoothHeathBrownDPFourierKernelMass,
      smoothHeathBrownDPFourierKernelFirstMoment] using hraw
  have hgeom := smoothHeathBrownDPThreeGroupBlockGeometry_ofRetained
      fsList hlen hfsne hret hXscale hη hηsmall (by linarith [hD])
      hlogThreshold I J J' hIJ hIJ' hJJ' hcover hE hIlo hIhi hgap p hp
      hW hWtwo hWT0 hT0upper hlarge
  dsimp only at hgeom
  rcases hgeom with
    ⟨_hLtwo, hYwindow, hYlarge, _hYprod, _hEps, _hexp, _hVtop, _hTtwo⟩
  have hEnvelopeForNumerical : E ≤
      (FractionalPrimes.Literature.DirichletMean.J 20 * Z 20 Y ^ 3 *
        (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
          (((Real.log X) ^ (-κ)) ^ (1 / 16 : ℝ) +
            Y ^ (-((η / 2) / 16 : ℝ)))) *
        smoothHeathBrownDPFourierKernelMass +
      (Z 20 Y ^ 3 * FractionalPrimes.Literature.DirichletMean.J 20 *
        (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
          (1 + Y ^ (-((η / 2) / 16 : ℝ)))) *
        ((2 / W) * smoothHeathBrownDPFourierKernelFirstMoment) := by
    have hexp : (-(η / 2) / 16 : ℝ) = -((η / 2) / 16 : ℝ) := by ring
    simpa [hexp] using hEnvelope
  have hnum := smoothHeathBrownDPThreeGroupBlockUniformNumerical_ofEnvelope
    (X := X) (Y := Y) (η := η) (κ := κ) (D := D) (W := W) (E := E)
    hXscale hYwindow.1 hYwindow.2 hYlarge hη hηsmall hW hEnvelopeForNumerical
  simpa [E, S₁, S₂, S₃, h₁, h₂, h₃, L₁, L₂, L₃, Y, T0] using hnum

/-- The three sets in an `IImaj (5/8)` source witness are all nonempty.
This is the exact weight-mass consequence needed to expand all three group
convolutions into source dyadic blocks. -/
theorem smoothHeathBrownDPThreeGroupGroups_nonempty_of_weightBounds
    {k : ℕ} (w : GroupingPredicates k)
    (I J J' : Finset (Fin k))
    (hIJ : Disjoint I J) (hIJ' : Disjoint I J')
    (hJJ' : Disjoint J J')
    (hcover : I ∪ J ∪ J' = Finset.univ)
    (hIlo : (1 / 4 : ℝ) ≤ subsetWeightSum w I)
    (hIhi : subsetWeightSum w I ≤ 1 / 2)
    (hgap : |subsetWeightSum w J - subsetWeightSum w J'| ≤ 1 / 4) :
    I.Nonempty ∧ J.Nonempty ∧ J'.Nonempty := by
  have hdis : Disjoint I (J ∪ J') := Finset.disjoint_union_right.mpr ⟨hIJ, hIJ'⟩
  have htotal : subsetWeightSum w I + subsetWeightSum w J +
      subsetWeightSum w J' = 1 := by
    have h := w.weight_sum_eq_one
    rw [← hcover] at h
    calc
      subsetWeightSum w I + subsetWeightSum w J + subsetWeightSum w J' =
          subsetWeightSum w I +
            (subsetWeightSum w J + subsetWeightSum w J') := by ring
      _ = 1 := by
        simpa [subsetWeightSum, Finset.sum_union hdis, Finset.sum_union hJJ'] using h
  have hInonneg : 0 ≤ subsetWeightSum w I := by
    exact Finset.sum_nonneg fun i hi => w.weight_nonneg i
  have hJnonneg : 0 ≤ subsetWeightSum w J := by
    exact Finset.sum_nonneg fun i hi => w.weight_nonneg i
  have hJ'nonneg : 0 ≤ subsetWeightSum w J' := by
    exact Finset.sum_nonneg fun i hi => w.weight_nonneg i
  have hJsum : (1 / 2 : ℝ) ≤
      subsetWeightSum w J + subsetWeightSum w J' := by
    rw [← htotal]
    linarith
  have hgap' := abs_le.mp hgap
  have hIpos : 0 < subsetWeightSum w I := by linarith
  have hJpos : 0 < subsetWeightSum w J := by linarith
  have hJ'pos : 0 < subsetWeightSum w J' := by linarith
  have hIcard : 0 < I.card := by
    by_contra h
    have he : I = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos h)
    simp [he, subsetWeightSum] at hIpos
  have hJcard : 0 < J.card := by
    by_contra h
    have he : J = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos h)
    simp [he, subsetWeightSum] at hJpos
  have hJ'card : 0 < J'.card := by
    by_contra h
    have he : J' = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos h)
    simp [he, subsetWeightSum] at hJ'pos
  exact ⟨Finset.card_pos.mp hIcard, Finset.card_pos.mp hJcard,
    Finset.card_pos.mp hJ'card⟩

/-- Absorb the three exact block savings at any requested logarithmic decay
rate.  This adds the absorption threshold to the source block threshold but
keeps the same selected groups, factor, and all residue/shift quantifiers. -/
theorem smoothHeathBrownDPThreeGroupBlockUniformAbsorbed_of_IImaj
    {A B κ D η : ℝ} (hB : 0 < B) (hκsrc : 0 < κ)
    (hDsrc : 2 * κ + 10 ≤ D) (hη : 0 < η)
    (hηsmall : η < 3 / 16) (hA : 0 < A)
    (hκabs : 16 * (A + (smoothHeathBrownDPBlockLogExponent : ℝ)) ≤ κ)
    (hDabs : A + (smoothHeathBrownDPBlockLogExponent : ℝ) ≤ D) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fsList : List (SmoothHeathBrownFactor X)) →
        fsList.length ≤ 20 → fsList ≠ [] →
        smoothHeathBrownSupportRetained
          (X := X) (z := dyadicMobiusCutoff X) fsList →
        (hE : 0 < smoothHeathBrownExponentSum fsList) →
        (smoothHeathBrownExponentGrouping fsList hE).IImaj (5 / 8) →
        ∃ I J J' : Finset (Fin fsList.length), ∃ selected : Fin fsList.length,
          Disjoint I J ∧ Disjoint I J' ∧ Disjoint J J' ∧
          I ∪ J ∪ J' = Finset.univ ∧
          (1 / 4 : ℝ) ≤
            subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ∧
          subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) I ≤
            1 / 2 ∧
          |subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J -
            subsetWeightSum (smoothHeathBrownExponentGrouping fsList hE) J'| ≤
              1 / 4 ∧
          selected ∈ I ∧ I.card ≤ 20 ∧ J.card ≤ 20 ∧ J'.card ≤ 20 ∧
          X ^ (1 / 100 : ℝ) ≤
            smoothHeathBrownFactorScale (fsList.get selected) ∧
          smoothHeathBrownFactorScale (fsList.get selected) ≤
            (2 : ℝ) ^ 11 * Real.sqrt X ∧
          (2 : ℝ) ^ 200 ≤ X ∧
          ∀ {H W : ℝ},
          X ^ ((5 / 8 : ℝ) + η) ≤ H →
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ X / H →
          ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          (residue : Fin fsList.length → ℕ) → residue selected < q →
          ∀ p : ℕ × (ℕ × ℕ),
          p ∈ smoothHeathBrownDPThreeGroupBlockIndexSet I J J' →
          ∀ u : ℝ, |u| ≤ W / 2 →
          let S₁ := smoothHeathBrownSubgroupScaleProduct fsList I
          let S₂ := smoothHeathBrownSubgroupScaleProduct fsList J
          let S₃ := smoothHeathBrownSubgroupScaleProduct fsList J'
          let h₁ : ℤ := (p.1 : ℤ) - (I.card : ℤ)
          let h₂ : ℤ := (p.2.1 : ℤ) - (J.card : ℤ)
          let h₃ : ℤ := (p.2.2 : ℤ) - (J'.card : ℤ)
          let L₁ := smoothHeathBrownDyadicBlockScale S₁ h₁
          let L₂ := smoothHeathBrownDyadicBlockScale S₂ h₂
          let L₃ := smoothHeathBrownDyadicBlockScale S₃ h₃
          let Y := smoothHeathBrownThreeDyadicBlockProductScale
            S₁ S₂ S₃ h₁ h₂ h₃
          (∫ u' : ℝ, ‖mellinSeparationLogKernelFourier u'‖ *
            productDirichletMeanEnvelope
              (smoothHeathBrownThreeGroupBlockMellinFactors
                (z := z) (fun i => fsList.get i) I J J' q residue
                L₁ L₂ L₃)
              (fun _ : Fin 3 => (0 : Fin 1))
              (X / H) W u') ≤
            3 * smoothHeathBrownDPBlockFourierConstant * Real.sqrt X *
              (Real.log X) ^ (-A) := by
  obtain ⟨Xnum, hXnum3, hnum⟩ :=
    smoothHeathBrownDPThreeGroupBlockUniformNumerical_of_IImaj
      hB hκsrc hDsrc hη hηsmall
  let Rabs : ℝ := (2 / (η / 32)) * Real.log
    (logAbsorptionM (η / 32)
      (A + (smoothHeathBrownDPBlockLogExponent : ℝ)))
  let X₀ : ℝ := max Xnum (max (Real.exp 1) (Real.exp Rabs))
  have hX₀three : 3 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans hXnum3 (le_max_left _ _)
  refine ⟨X₀, hX₀three, ?_⟩
  intro X z hX₀X hz fsList hlen hfsne hret hE hIImaj
  have hXnumX : Xnum ≤ X := le_trans (le_max_left _ _) hX₀X
  have hexpOne : Real.exp 1 ≤ X :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) hX₀X)
  have hexpRabs : Real.exp Rabs ≤ X :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hX₀X)
  have hlogXone : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hexpOne
    simpa using h
  have hlogXabs : Rabs ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos Rabs) hexpRabs
    simpa [Rabs] using h
  rcases hnum hXnumX hz fsList hlen hfsne hret hE hIImaj with
    ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover, hIlo, hIhi,
      hgap, hselected, hIcard, hJcard, hJ'card, hNlo, hNhi, hXscale,
      hblock⟩
  refine ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover, hIlo, hIhi,
    hgap, hselected, hIcard, hJcard, hJ'card, hNlo, hNhi, hXscale, ?_⟩
  intro H W hHlower hW hWtwo hWT0 q hq hqlog residue hresidue p hp u hu
  have hXone : 1 ≤ X := by
    have hpow : 1 ≤ (2 : ℝ) ^ 200 := by norm_num
    exact hpow.trans hXscale
  have hm : 0 ≤ (smoothHeathBrownDPBlockLogExponent : ℝ) := by positivity
  have hsave := dpLogarithmicSavings_absorption
    hXone hm hA hη hlogXone hκabs hDabs (by simpa [Rabs] using hlogXabs)
  rw [Real.rpow_natCast] at hsave
  have hraw := hblock hHlower hW hWtwo hWT0 q hq hqlog residue hresidue p hp u hu
  have hconstant : 0 ≤ smoothHeathBrownDPBlockFourierConstant := by
    have hmass := smoothHeathBrownDPFourierKernelMass_nonneg
    have hmoment := smoothHeathBrownDPFourierKernelFirstMoment_nonneg
    have hJ : 0 ≤ FractionalPrimes.Literature.DirichletMean.J 20 := by
      simp [FractionalPrimes.Literature.DirichletMean.J,
        FractionalPrimes.Literature.DirichletMean.K]
    have hkernel : 0 ≤ 2 * smoothHeathBrownDPFourierKernelMass +
        4 * smoothHeathBrownDPFourierKernelFirstMoment := by positivity
    unfold smoothHeathBrownDPBlockFourierConstant
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hJ (by positivity))
          (by positivity))
        (by positivity))
      hkernel
  have hfactor : 0 ≤ smoothHeathBrownDPBlockFourierConstant * Real.sqrt X :=
    mul_nonneg hconstant (Real.sqrt_nonneg X)
  calc
    _ ≤ smoothHeathBrownDPBlockFourierConstant * Real.sqrt X *
        (Real.log X) ^ (smoothHeathBrownDPBlockLogExponent : ℕ) *
          ((Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
            (Real.log X) ^ (-D)) := by
              simpa only [Nat.cast_ofNat] using hraw
    _ = (smoothHeathBrownDPBlockFourierConstant * Real.sqrt X) *
        ((Real.log X) ^ (smoothHeathBrownDPBlockLogExponent : ℕ) *
          ((Real.log X) ^ (-κ / 16 : ℝ) + X ^ (-η / 32 : ℝ) +
            (Real.log X) ^ (-D))) := by ring
    _ ≤ (smoothHeathBrownDPBlockFourierConstant * Real.sqrt X) *
        (3 * (Real.log X) ^ (-A)) :=
          mul_le_mul_of_nonneg_left hsave hfactor
    _ = 3 * smoothHeathBrownDPBlockFourierConstant * Real.sqrt X *
        (Real.log X) ^ (-A) := by ring

/-- Exact full-product expansion in the reusable source block API. -/
theorem smoothHeathBrownThreeGroupResidueProduct_sourceBlockExpansion
    {X z : ℝ} {q : ℕ}
    (fsList : List (SmoothHeathBrownFactor X))
    (I₁ I₂ I₃ : Finset (Fin fsList.length))
    (hI₁ : I₁.Nonempty) (hI₂ : I₂.Nonempty) (hI₃ : I₃.Nonempty)
    (hI₁I₂ : Disjoint I₁ I₂) (hI₁I₃ : Disjoint I₁ I₃)
    (hI₂I₃ : Disjoint I₂ I₃)
    (hcover : I₁ ∪ I₂ ∪ I₃ = Finset.univ)
    (hq : 0 < q) (b : Fin fsList.length → Fin q) (t u : ℝ) :
    productDirichletPolynomialsAt
        (fun i : Fin fsList.length =>
          smoothHeathBrownNormalizedMellinFactor (z := z) (fsList.get i))
        b t u =
      ∑ p ∈ smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃,
        productDirichletPolynomialsAt
          (smoothHeathBrownDPThreeGroupBlockFactors (z := z) (q := q)
            fsList I₁ I₂ I₃ b p)
          (smoothHeathBrownDPThreeGroupBlockResidues (q := q) fsList b p) t u := by
  change productDirichletPolynomialsAt
      (fun i : Fin fsList.length =>
        smoothHeathBrownNormalizedMellinFactor (z := z) (fsList.get i))
      b t u =
    ∑ p ∈ Finset.range (2 * I₁.card) ×ˢ
        (Finset.range (2 * I₂.card) ×ˢ Finset.range (2 * I₃.card)),
      productDirichletPolynomialsAt
        (smoothHeathBrownThreeGroupBlockMellinFactors
          (z := z) (fun i : Fin fsList.length => fsList.get i)
          I₁ I₂ I₃ q (fun i => (b i).val)
          ((2 : ℝ) ^ p.1 *
            (smoothHeathBrownSubgroupScaleProduct fsList I₁ /
              (2 : ℝ) ^ I₁.card))
          ((2 : ℝ) ^ p.2.1 *
            (smoothHeathBrownSubgroupScaleProduct fsList I₂ /
              (2 : ℝ) ^ I₂.card))
          ((2 : ℝ) ^ p.2.2 *
            (smoothHeathBrownSubgroupScaleProduct fsList I₃ /
              (2 : ℝ) ^ I₃.card)))
        (fun _ : Fin 3 => (0 : Fin 1)) t u
  exact smoothHeathBrownThreeGroupResidueProduct_eq_blockTripleSum
    (z := z) fsList I₁ I₂ I₃ hI₁ hI₂ hI₃ hI₁I₂ hI₁I₃ hI₂I₃
    hcover hq b t u

/-- Pointwise source mean-envelope accumulation for an exact finite expansion
whose block polynomials may have a different number of factors and a
different residue modulus from the full source polynomial. -/
theorem productDirichletMeanEnvelope_le_sum_of_polynomialExpansion_differentTypes
    {r q r' q' : ℕ} {ι : Type*} (J : Finset ι)
    (α : Fin r → MellinSeparationFactor) (bResidue : Fin r → Fin q)
    (blockFactors : ι → Fin r' → MellinSeparationFactor)
    (blockResidues : ι → Fin r' → Fin q')
    {T0 W u : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hExpansion : ∀ t : ℝ,
      productDirichletPolynomialsAt α bResidue t u =
        ∑ i ∈ J,
          productDirichletPolynomialsAt (blockFactors i) (blockResidues i) t u) :
    productDirichletMeanEnvelope α bResidue T0 W u ≤
      ∑ i ∈ J,
        productDirichletMeanEnvelope (blockFactors i) (blockResidues i) T0 W u := by
  classical
  obtain ⟨V, hV, hmax, _⟩ :=
    productDirichletMeanEnvelope_hasMaximum α bResidue hW hWT
  have hT0pos : 0 < T0 := by linarith [hW, hWT]
  have hVpos : 0 < V := lt_of_lt_of_le hT0pos hV.1
  let E : Set ℝ := {t : ℝ | W ≤ |t| ∧ |t| ≤ V}
  have hEmeas : MeasurableSet E := by
    change MeasurableSet ((fun t : ℝ => |t|) ⁻¹' Set.Icc W V)
    exact (isClosed_Icc.preimage continuous_abs).measurableSet
  have hEclosed : IsClosed E := by
    change IsClosed ((fun t : ℝ => |t|) ⁻¹' Set.Icc W V)
    exact isClosed_Icc.preimage continuous_abs
  have hEsubset : E ⊆ Set.Icc (-V) V := by
    intro t ht
    exact abs_le.mp ht.2
  have hEcompact : IsCompact E :=
    isCompact_Icc.of_isClosed_subset hEclosed hEsubset
  have hLeftCont : Continuous (fun t : ℝ =>
      productDirichletTailIntegrand α bResidue t u) := by
    unfold productDirichletTailIntegrand
    exact continuous_norm.comp
      (productDirichletPolynomialsAt_continuous_in_t α bResidue u)
  have hLeftInt : IntegrableOn
      (fun t : ℝ => productDirichletTailIntegrand α bResidue t u) E :=
    hLeftCont.continuousOn.integrableOn_compact hEcompact
  have hBlockCont (i : ι) : Continuous (fun t : ℝ =>
      productDirichletTailIntegrand (blockFactors i) (blockResidues i) t u) := by
    unfold productDirichletTailIntegrand
    exact continuous_norm.comp
      (productDirichletPolynomialsAt_continuous_in_t
        (blockFactors i) (blockResidues i) u)
  have hRightInt : IntegrableOn
      (fun t : ℝ => ∑ i ∈ J,
        productDirichletTailIntegrand (blockFactors i) (blockResidues i) t u) E := by
    apply integrable_finsetSum J
    intro i hi
    exact (hBlockCont i).continuousOn.integrableOn_compact hEcompact
  have hnorm (t : ℝ) :
      productDirichletTailIntegrand α bResidue t u ≤
        ∑ i ∈ J,
          productDirichletTailIntegrand (blockFactors i) (blockResidues i) t u := by
    unfold productDirichletTailIntegrand
    rw [hExpansion t]
    exact norm_sum_le _ _
  have htailE :
      (∫ t in E, productDirichletTailIntegrand α bResidue t u) ≤
        ∑ i ∈ J, ∫ t in E,
          productDirichletTailIntegrand (blockFactors i) (blockResidues i) t u := by
    calc
      (∫ t in E, productDirichletTailIntegrand α bResidue t u) ≤
          ∫ t in E, ∑ i ∈ J,
            productDirichletTailIntegrand (blockFactors i) (blockResidues i) t u :=
        setIntegral_mono_on hLeftInt hRightInt hEmeas (by
          intro t ht
          exact hnorm t)
      _ = ∑ i ∈ J, ∫ t in E,
          productDirichletTailIntegrand (blockFactors i) (blockResidues i) t u := by
        rw [integral_finsetSum]
        intro i hi
        exact (hBlockCont i).continuousOn.integrableOn_compact hEcompact
  have htail : productDirichletTailIntegral α bResidue W u V ≤
      ∑ i ∈ J, productDirichletTailIntegral
        (blockFactors i) (blockResidues i) W u V := by
    simpa [productDirichletTailIntegral, E] using htailE
  have htailBound : productDirichletMeanObjective α bResidue T0 W u V ≤
      ∑ i ∈ J,
        productDirichletMeanEnvelope (blockFactors i) (blockResidues i) T0 W u := by
    have hfactor : 0 ≤ T0 / V := div_nonneg hT0pos.le hVpos.le
    calc
      productDirichletMeanObjective α bResidue T0 W u V =
          (T0 / V) * productDirichletTailIntegral α bResidue W u V := rfl
      _ ≤ (T0 / V) *
          (∑ i ∈ J, productDirichletTailIntegral
            (blockFactors i) (blockResidues i) W u V) :=
        mul_le_mul_of_nonneg_left htail hfactor
      _ = ∑ i ∈ J, (T0 / V) *
          productDirichletTailIntegral
            (blockFactors i) (blockResidues i) W u V := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ J,
          productDirichletMeanEnvelope (blockFactors i) (blockResidues i) T0 W u := by
        apply Finset.sum_le_sum
        intro i hi
        rcases productDirichletMeanEnvelope_hasMaximum
            (blockFactors i) (blockResidues i) (u := u) hW hWT with
          ⟨_, _, _, hblockle⟩
        simpa [productDirichletMeanObjective] using hblockle V hV
  calc
    productDirichletMeanEnvelope α bResidue T0 W u =
        productDirichletMeanObjective α bResidue T0 W u V := hmax.symm
    _ ≤ ∑ i ∈ J,
        productDirichletMeanEnvelope (blockFactors i) (blockResidues i) T0 W u :=
      htailBound

/-- Integrating an exact finite block expansion transfers to the sum of block
envelopes even when the block factor dimensions and residue moduli differ. -/
theorem productDirichletMeanEnvelope_fourierIntegral_le_sum_of_polynomialExpansion_differentTypes
    {r q r' q' : ℕ} {ι : Type*} (J : Finset ι)
    (α : Fin r → MellinSeparationFactor) (bResidue : Fin r → Fin q)
    (blockFactors : ι → Fin r' → MellinSeparationFactor)
    (blockResidues : ι → Fin r' → Fin q') {T0 W : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hExpansion : ∀ (t u : ℝ),
      productDirichletPolynomialsAt α bResidue t u =
        ∑ i ∈ J,
          productDirichletPolynomialsAt (blockFactors i) (blockResidues i) t u) :
    (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
      productDirichletMeanEnvelope α bResidue T0 W u) ≤
      ∑ i ∈ J, ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanEnvelope
          (blockFactors i) (blockResidues i) T0 W u := by
  classical
  let Kfun : ℝ → ℝ := fun u => ‖mellinSeparationLogKernelFourier u‖
  have hLeft : Integrable (fun u : ℝ => Kfun u *
      productDirichletMeanEnvelope α bResidue T0 W u) := by
    simpa [Kfun] using
      productDirichletMeanEnvelope_weighted_integrable α bResidue hW hWT
  have hEach (i : ι) : Integrable (fun u : ℝ => Kfun u *
      productDirichletMeanEnvelope
        (blockFactors i) (blockResidues i) T0 W u) := by
    simpa [Kfun] using productDirichletMeanEnvelope_weighted_integrable
      (blockFactors i) (blockResidues i) hW hWT
  have hRight : Integrable (fun u : ℝ => ∑ i ∈ J, Kfun u *
      productDirichletMeanEnvelope
        (blockFactors i) (blockResidues i) T0 W u) := by
    apply integrable_finsetSum J
    intro i hi
    exact hEach i
  have hPoint (u : ℝ) :
      Kfun u * productDirichletMeanEnvelope α bResidue T0 W u ≤
        ∑ i ∈ J, Kfun u * productDirichletMeanEnvelope
          (blockFactors i) (blockResidues i) T0 W u := by
    have henv := productDirichletMeanEnvelope_le_sum_of_polynomialExpansion_differentTypes
      J α bResidue blockFactors blockResidues hW hWT
      (fun t => hExpansion t u)
    have hk : 0 ≤ Kfun u := by simp [Kfun]
    calc
      Kfun u * productDirichletMeanEnvelope α bResidue T0 W u ≤
          Kfun u * ∑ i ∈ J,
            productDirichletMeanEnvelope
              (blockFactors i) (blockResidues i) T0 W u :=
        mul_le_mul_of_nonneg_left henv hk
      _ = ∑ i ∈ J, Kfun u *
            productDirichletMeanEnvelope
              (blockFactors i) (blockResidues i) T0 W u := by
        rw [Finset.mul_sum]
  calc
    (∫ u : ℝ, Kfun u * productDirichletMeanEnvelope α bResidue T0 W u) ≤
        ∫ u : ℝ, ∑ i ∈ J, Kfun u *
          productDirichletMeanEnvelope
            (blockFactors i) (blockResidues i) T0 W u :=
      integral_mono hLeft hRight hPoint
    _ = ∑ i ∈ J, ∫ u : ℝ, Kfun u *
          productDirichletMeanEnvelope
            (blockFactors i) (blockResidues i) T0 W u := by
      rw [integral_finsetSum]
      intro i hi
      exact hEach i

/-- A source component whose exact Mellin polynomial is a scalar multiple of
the separated full-factor product has its mean envelope bounded by the sum
over every allowed residue tuple and every term in an exact finite block
expansion of that product. The block factors may depend on the residue tuple,
as they do for actual residue-restricted Heath--Brown groups. -/
theorem dirichletMeanEnvelopeOfA_X_le_scaledBlockProductMeans
    {r q r' q' : ℕ} {ι : Type*} (J : Finset ι)
    (hr : 0 < r) (α : Fin r → MellinSeparationFactor)
    (hq : 0 < q) (a : ℤ) (X : ℝ) (hX : 3 ≤ X)
    (κ : ℂ) (A : ℝ → ℂ)
    (hscale : ∀ t, A t = κ *
      (mellinSeparationProductWindowData α q a X hX).A_X t)
    (blockFactors : (Fin r → Fin q) → ι → Fin r' → MellinSeparationFactor)
    (blockResidues : (Fin r → Fin q) → ι → Fin r' → Fin q')
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hExpansion : ∀ (b : Fin r → Fin q) (t u : ℝ),
      productDirichletPolynomialsAt α b t u =
        ∑ i ∈ J,
          productDirichletPolynomialsAt (blockFactors b i)
            (blockResidues b i) t u) :
    dirichletMeanEnvelopeOfA_X A T0 W ≤
      ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∑ i ∈ J,
            ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
              productDirichletMeanEnvelope
                (blockFactors b i) (blockResidues b i) T0 W u) := by
  classical
  let R := mellinSeparationAllowedResidues (r := r) (q := q) a
  let Kfun : ℝ → ℝ := fun u => ‖mellinSeparationLogKernelFourier u‖
  have hsource := dirichletMeanEnvelopeOfA_X_le_scaledProductMeans
    hr α hq a X hX κ A hscale hW hWT
  have hblocks :
      ∑ b ∈ R,
        ∫ u : ℝ, Kfun u * productDirichletMeanEnvelope α b T0 W u ≤
      ∑ b ∈ R, ∑ i ∈ J,
        ∫ u : ℝ, Kfun u * productDirichletMeanEnvelope
          (blockFactors b i) (blockResidues b i) T0 W u := by
    apply Finset.sum_le_sum
    intro b hb
    simpa [Kfun] using
      productDirichletMeanEnvelope_fourierIntegral_le_sum_of_polynomialExpansion_differentTypes
        J α b (blockFactors b) (blockResidues b) hW hWT
        (fun t u => hExpansion b t u)
  have hkernel : 0 ≤ (2 * Real.pi : ℝ)⁻¹ := by positivity
  have hκ : 0 ≤ ‖κ‖ := norm_nonneg _
  calc
    dirichletMeanEnvelopeOfA_X A T0 W ≤
        ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
          ∑ b ∈ R,
            ∫ u : ℝ, Kfun u * productDirichletMeanEnvelope α b T0 W u) := by
              simpa [R, Kfun] using hsource
    _ ≤ ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
          ∑ b ∈ R, ∑ i ∈ J,
            ∫ u : ℝ, Kfun u * productDirichletMeanEnvelope
              (blockFactors b i) (blockResidues b i) T0 W u) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hblocks hkernel
      · exact hκ

/-- For a source component with the exact normalized Mellin factorization,
its full mean envelope is bounded by the finite sum over the actual source
three-group dyadic blocks. All residue tuples and Mellin shifts are retained. -/
theorem dirichletMeanEnvelopeOfA_X_le_sourceThreeGroupBlockMeans
    {X z : ℝ} {q : ℕ} (fsList : List (SmoothHeathBrownFactor X))
    (hlen : 0 < fsList.length)
    (I₁ I₂ I₃ : Finset (Fin fsList.length))
    (hI₁ : I₁.Nonempty) (hI₂ : I₂.Nonempty) (hI₃ : I₃.Nonempty)
    (hI₁I₂ : Disjoint I₁ I₂) (hI₁I₃ : Disjoint I₁ I₃)
    (hI₂I₃ : Disjoint I₂ I₃)
    (hcover : I₁ ∪ I₂ ∪ I₃ = Finset.univ)
    (hq : 0 < q) (a : ℤ) (hX : 3 ≤ X)
    (κ : ℂ) (A : ℝ → ℂ)
    (hscale : ∀ t, A t = κ *
      (mellinSeparationProductWindowData
        (fun i : Fin fsList.length =>
          smoothHeathBrownNormalizedMellinFactor (z := z) (fsList.get i))
        q a X hX).A_X t)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelopeOfA_X A T0 W ≤
      ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues
            (r := fsList.length) (q := q) a,
          ∑ p ∈ smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃,
            ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
              productDirichletMeanEnvelope
                (smoothHeathBrownDPThreeGroupBlockFactors
                  (z := z) (q := q) fsList I₁ I₂ I₃ b p)
                (smoothHeathBrownDPThreeGroupBlockResidues
                  (q := q) fsList b p)
                T0 W u) := by
  classical
  let α : Fin fsList.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := z) (fsList.get i)
  let J := smoothHeathBrownDPThreeGroupBlockIndexSet I₁ I₂ I₃
  let blockFactors :
      (Fin fsList.length → Fin q) →
        (ℕ × (ℕ × ℕ)) → Fin 3 → MellinSeparationFactor := fun b p =>
    smoothHeathBrownDPThreeGroupBlockFactors (z := z) (q := q)
      fsList I₁ I₂ I₃ b p
  let blockResidues :
      (Fin fsList.length → Fin q) →
        (ℕ × (ℕ × ℕ)) → Fin 3 → Fin 1 := fun b p =>
    smoothHeathBrownDPThreeGroupBlockResidues (q := q) fsList b p
  have hExpansion : ∀ (b : Fin fsList.length → Fin q) (t u : ℝ),
      productDirichletPolynomialsAt α b t u =
        ∑ p ∈ J,
          productDirichletPolynomialsAt (blockFactors b p)
            (blockResidues b p) t u := by
    intro b t u
    simpa [α, J, blockFactors, blockResidues] using
      smoothHeathBrownThreeGroupResidueProduct_sourceBlockExpansion
        (z := z) fsList I₁ I₂ I₃ hI₁ hI₂ hI₃ hI₁I₂ hI₁I₃ hI₂I₃
        hcover hq b t u
  have hresult := dirichletMeanEnvelopeOfA_X_le_scaledBlockProductMeans
    (J := J) hlen α hq a X hX κ A
    (by intro t; exact hscale t) blockFactors blockResidues hW hWT hExpansion
  simpa [α, J, blockFactors, blockResidues] using hresult

/-- If every residue/block term has an explicit Fourier-weighted mean bound,
the exact source-component transfer accumulates those bounds over the full
allowed residue set and the finite block index set. This keeps the source
scalar and `(2π)⁻¹` normalization visible. -/
theorem dirichletMeanEnvelopeOfA_X_le_scaledBlockFourierBounds
    {r q r' q' : ℕ} {ι : Type*} (J : Finset ι)
    (hr : 0 < r) (α : Fin r → MellinSeparationFactor)
    (hq : 0 < q) (a : ℤ) (X : ℝ) (hX : 3 ≤ X)
    (κ : ℂ) (A : ℝ → ℂ)
    (hscale : ∀ t, A t = κ *
      (mellinSeparationProductWindowData α q a X hX).A_X t)
    (blockFactors : (Fin r → Fin q) → ι → Fin r' → MellinSeparationFactor)
    (blockResidues : (Fin r → Fin q) → ι → Fin r' → Fin q')
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hExpansion : ∀ (b : Fin r → Fin q) (t u : ℝ),
      productDirichletPolynomialsAt α b t u =
        ∑ i ∈ J,
          productDirichletPolynomialsAt (blockFactors b i)
            (blockResidues b i) t u)
    (M : (Fin r → Fin q) → ι → ℝ)
    (hBlock : ∀ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
      ∀ i ∈ J,
        (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          productDirichletMeanEnvelope
            (blockFactors b i) (blockResidues b i) T0 W u) ≤ M b i) :
    dirichletMeanEnvelopeOfA_X A T0 W ≤
      ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∑ i ∈ J, M b i) := by
  classical
  let R := mellinSeparationAllowedResidues (r := r) (q := q) a
  have hmeans := dirichletMeanEnvelopeOfA_X_le_scaledBlockProductMeans
    (J := J) hr α hq a X hX κ A hscale blockFactors blockResidues
    hW hWT hExpansion
  have hsum :
      ∑ b ∈ R, ∑ i ∈ J,
        ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          productDirichletMeanEnvelope
            (blockFactors b i) (blockResidues b i) T0 W u ≤
      ∑ b ∈ R, ∑ i ∈ J, M b i := by
    apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum
    intro i hi
    exact hBlock b (by simpa [R] using hb) i hi
  have hfactor : 0 ≤ ‖κ‖ * (2 * Real.pi : ℝ)⁻¹ :=
    mul_nonneg (norm_nonneg κ) (by positivity)
  calc
    dirichletMeanEnvelopeOfA_X A T0 W ≤
        ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
          ∑ b ∈ R, ∑ i ∈ J,
            ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
              productDirichletMeanEnvelope
                (blockFactors b i) (blockResidues b i) T0 W u) := by
      simpa [R] using hmeans
    _ = (‖κ‖ * (2 * Real.pi : ℝ)⁻¹) *
        (∑ b ∈ R, ∑ i ∈ J,
          ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
            productDirichletMeanEnvelope
              (blockFactors b i) (blockResidues b i) T0 W u) := by ring
    _ ≤ (‖κ‖ * (2 * Real.pi : ℝ)⁻¹) *
        (∑ b ∈ R, ∑ i ∈ J, M b i) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ R, ∑ i ∈ J, M b i) := by ring

/-- Specialization of the finite block accumulator to one uniform bound for
all allowed residue and block pairs, with their exact finite count visible. -/
theorem dirichletMeanEnvelopeOfA_X_le_scaledBlockUniformFourierBound
    {r q r' q' : ℕ} {ι : Type*} (J : Finset ι)
    (hr : 0 < r) (α : Fin r → MellinSeparationFactor)
    (hq : 0 < q) (a : ℤ) (X : ℝ) (hX : 3 ≤ X)
    (κ : ℂ) (A : ℝ → ℂ)
    (hscale : ∀ t, A t = κ *
      (mellinSeparationProductWindowData α q a X hX).A_X t)
    (blockFactors : (Fin r → Fin q) → ι → Fin r' → MellinSeparationFactor)
    (blockResidues : (Fin r → Fin q) → ι → Fin r' → Fin q')
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hExpansion : ∀ (b : Fin r → Fin q) (t u : ℝ),
      productDirichletPolynomialsAt α b t u =
        ∑ i ∈ J,
          productDirichletPolynomialsAt (blockFactors b i)
            (blockResidues b i) t u)
    (M : ℝ)
    (hBlock : ∀ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
      ∀ i ∈ J,
        (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          productDirichletMeanEnvelope
            (blockFactors b i) (blockResidues b i) T0 W u) ≤ M) :
    dirichletMeanEnvelopeOfA_X A T0 W ≤
      ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ((mellinSeparationAllowedResidues (r := r) (q := q) a).card : ℝ) *
          (J.card : ℝ) * M) := by
  classical
  let R := mellinSeparationAllowedResidues (r := r) (q := q) a
  have hsumConst :
      ∑ b ∈ R, ∑ i ∈ J, (M : ℝ) =
        (R.card : ℝ) * (J.card : ℝ) * M := by
    calc
      ∑ b ∈ R, ∑ i ∈ J, (M : ℝ) =
          ∑ b ∈ R, (J.card : ℝ) * M := by simp
      _ = (R.card : ℝ) * ((J.card : ℝ) * M) := by simp
      _ = (R.card : ℝ) * (J.card : ℝ) * M := by ring
  have hresult := dirichletMeanEnvelopeOfA_X_le_scaledBlockFourierBounds
    (J := J) hr α hq a X hX κ A hscale blockFactors blockResidues hW hWT
    hExpansion (fun _ _ => M) (by
      intro b hb i hi
      exact hBlock b (by simpa [R] using hb) i hi)
  calc
    dirichletMeanEnvelopeOfA_X A T0 W ≤
        ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
          ∑ b ∈ R, ∑ i ∈ J, M) := by
      simpa [R] using hresult
    _ = ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
          ((R.card : ℝ) * (J.card : ℝ) * M)) := by rw [hsumConst]
    _ = ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
          ((mellinSeparationAllowedResidues (r := r) (q := q) a).card : ℝ) *
            (J.card : ℝ) * M) := by simp [R, mul_assoc]

/-- Source-facing finite accumulation of the absorbed IImaj block bound over
all allowed residue tuples and all three-group dyadic block triples.  The
extra `20 B` of block decay pays exactly for the source residue count; the
retained factor list, source scalar, modulus, and outer-cutoff product window
remain explicit. -/
theorem smoothHeathBrownDPProductWindowEnvelope_of_IImaj
    {A B κ D η : ℝ} (hB : 0 < B) (hκsrc : 0 < κ)
    (hDsrc : 2 * κ + 10 ≤ D) (hη : 0 < η)
    (hηsmall : η < 3 / 16) (hA : 0 < A)
    (hκabs : 16 * ((A + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ)) ≤ κ)
    (hDabs : (A + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ) ≤ D) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fsList : List (SmoothHeathBrownFactor X)) →
        fsList.length ≤ 20 → fsList ≠ [] →
        smoothHeathBrownSupportRetained
          (X := X) (z := dyadicMobiusCutoff X) fsList →
        (hE : 0 < smoothHeathBrownExponentSum fsList) →
        (smoothHeathBrownExponentGrouping fsList hE).IImaj (5 / 8) →
        ∀ {H W : ℝ},
          X ^ ((5 / 8 : ℝ) + η) ≤ H →
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ X / H →
          ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ (a : ℤ) (c : ℂ) (F : ℝ → ℂ) (hX : 3 ≤ X),
          (∀ t, F t = c *
            (mellinSeparationProductWindowData
              (fun i : Fin fsList.length =>
                smoothHeathBrownNormalizedMellinFactor
                  (z := z) (fsList.get i)) q a X hX).A_X t) →
          dirichletMeanEnvelopeOfA_X F (X / H) W ≤
            ‖c‖ * ((2 * Real.pi : ℝ)⁻¹ *
              ((40 : ℝ) * (40 * 40) *
                Real.rpow (Real.log X) (B * 20) *
                (3 * smoothHeathBrownDPBlockFourierConstant *
                  Real.sqrt X * (Real.log X) ^ (-(A + 20 * B))))) := by
  have hAcount : 0 < A + 20 * B := by positivity
  obtain ⟨X₀, hX₀three, hblockUniform⟩ :=
    smoothHeathBrownDPThreeGroupBlockUniformAbsorbed_of_IImaj
      (A := A + 20 * B) hB hκsrc hDsrc hη hηsmall hAcount
      hκabs hDabs
  refine ⟨X₀, hX₀three, ?_⟩
  intro X z hX₀X hz fsList hlen hfsne hret hE hIImaj H W
    hHlower hW hWtwo hWT0 q hq hqlog a c F hX hscale
  rcases hblockUniform hX₀X hz fsList hlen hfsne hret hE hIImaj with
    ⟨I, J, J', selected, hIJ, hIJ', hJJ', hcover, hIlo, hIhi,
      hgap, hselected, hIcard, hJcard, hJ'card, hNlo, hNhi, hXscale,
      hblock⟩
  have hX : 3 ≤ X := by
    have hthree : 3 ≤ (2 : ℝ) ^ 200 := by norm_num
    exact hthree.trans hXscale
  have hqpos : 0 < q := by omega
  have hlenpos : 0 < fsList.length := by
    cases fsList with
    | nil => contradiction
    | cons f fs => simp
  have hnonempty := smoothHeathBrownDPThreeGroupGroups_nonempty_of_weightBounds
    (smoothHeathBrownExponentGrouping fsList hE) I J J'
    hIJ hIJ' hJJ' hcover hIlo hIhi hgap
  rcases hnonempty with ⟨hInonempty, hJnonempty, hJ'nonempty⟩
  let α : Fin fsList.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := z) (fsList.get i)
  let Jset := smoothHeathBrownDPThreeGroupBlockIndexSet I J J'
  let Rset := mellinSeparationAllowedResidues
    (r := fsList.length) (q := q) a
  let blockFactors : (Fin fsList.length → Fin q) →
      (ℕ × (ℕ × ℕ)) → Fin 3 → MellinSeparationFactor := fun b p =>
    smoothHeathBrownDPThreeGroupBlockFactors
      (z := z) (q := q) fsList I J J' b p
  let blockResidues : (Fin fsList.length → Fin q) →
      (ℕ × (ℕ × ℕ)) → Fin 3 → Fin 1 := fun b p =>
    smoothHeathBrownDPThreeGroupBlockResidues (q := q) fsList b p
  have hExpansion : ∀ (b : Fin fsList.length → Fin q) (t u : ℝ),
      productDirichletPolynomialsAt α b t u =
        ∑ p ∈ Jset,
          productDirichletPolynomialsAt (blockFactors b p)
            (blockResidues b p) t u := by
    intro b t u
    simpa [α, Jset, blockFactors, blockResidues] using
      smoothHeathBrownThreeGroupResidueProduct_sourceBlockExpansion
        (z := z) fsList I J J' hInonempty hJnonempty hJ'nonempty
        hIJ hIJ' hJJ' hcover hqpos b t u
  let M : ℝ := 3 * smoothHeathBrownDPBlockFourierConstant *
    Real.sqrt X * (Real.log X) ^ (-(A + 20 * B))
  have hconst : 0 ≤ smoothHeathBrownDPBlockFourierConstant := by
    have hmass := smoothHeathBrownDPFourierKernelMass_nonneg
    have hmoment := smoothHeathBrownDPFourierKernelFirstMoment_nonneg
    have hJ : 0 ≤ FractionalPrimes.Literature.DirichletMean.J 20 := by
      simp [FractionalPrimes.Literature.DirichletMean.J,
        FractionalPrimes.Literature.DirichletMean.K]
    have hkernel : 0 ≤ 2 * smoothHeathBrownDPFourierKernelMass +
        4 * smoothHeathBrownDPFourierKernelFirstMoment := by positivity
    unfold smoothHeathBrownDPBlockFourierConstant
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hJ (by positivity))
          (by positivity))
        (by positivity))
      hkernel
  have hlogXnonneg : 0 ≤ Real.log X := Real.log_nonneg (by linarith [hXscale])
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hBlock : ∀ b ∈ Rset, ∀ p ∈ Jset,
      (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanEnvelope (blockFactors b p) (blockResidues b p)
          (X / H) W u) ≤ M := by
    intro b hb p hp
    let residue : Fin fsList.length → ℕ := fun i => (b i).val
    have hres : residue selected < q := by
      dsimp [residue]
      exact (b selected).isLt
    have houter : |(0 : ℝ)| ≤ W / 2 := by
      rw [abs_zero]
      linarith
    have hsource := hblock hHlower hW hWtwo hWT0 q hq hqlog
      residue hres p hp 0 houter
    have hfactor := smoothHeathBrownDPThreeGroupBlockFactors_eq_integerShiftFactors
      (z := z) (q := q) fsList I J J' b p
    change (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanEnvelope
          (smoothHeathBrownDPThreeGroupBlockFactors
            (z := z) (q := q) fsList I J J' b p)
          (fun _ : Fin 3 => (0 : Fin 1)) (X / H) W u) ≤ M
    dsimp [M]
    simpa [hfactor] using hsource
  have hUniform := dirichletMeanEnvelopeOfA_X_le_scaledBlockUniformFourierBound
    (J := Jset) hlenpos α hqpos a X hX c F hscale
    blockFactors blockResidues hWtwo hWT0 hExpansion M (by
      intro b hb p hp
      exact hBlock b (by simpa [Rset] using hb) p (by simpa [Jset] using hp))
  have hrle : (fsList.length : ℝ) ≤ 20 := by exact_mod_cast hlen
  have hCount := smoothHeathBrownDPThreeGroupResidueBlockCount_le_logPower
    (a := a) (B := B) (R := 20) (X := X) hB (by norm_num) hX
    (by simpa using hqlog) hrle I J J' hIcard hJcard hJ'card
  have hUniform' : dirichletMeanEnvelopeOfA_X F (X / H) W ≤
      ‖c‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ((Rset.card : ℝ) * (Jset.card : ℝ) * M)) := by
    simpa [Rset, Jset, mul_assoc] using hUniform
  let N : ℝ := (40 : ℝ) * (40 * 40) * Real.rpow (Real.log X) (B * 20)
  have hCountM := mul_le_mul_of_nonneg_right hCount hMnonneg
  have hfactor : 0 ≤ ‖c‖ * (2 * Real.pi : ℝ)⁻¹ :=
    mul_nonneg (norm_nonneg c) (by positivity)
  calc
    dirichletMeanEnvelopeOfA_X F (X / H) W ≤
        ‖c‖ * ((2 * Real.pi : ℝ)⁻¹ *
          ((Rset.card : ℝ) * (Jset.card : ℝ) * M)) := hUniform'
    _ = (‖c‖ * (2 * Real.pi : ℝ)⁻¹) *
        ((Rset.card : ℝ) * (Jset.card : ℝ) * M) := by ring
    _ ≤ (‖c‖ * (2 * Real.pi : ℝ)⁻¹) * (N * M) :=
      mul_le_mul_of_nonneg_left hCountM hfactor
    _ = ‖c‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ((40 : ℝ) * (40 * 40) * Real.rpow (Real.log X) (B * 20) * M)) := by
      dsimp [N]
      ring
    _ = _ := by dsimp [M]

/-- Absorb a uniform block bound into any proved residue/block count. This
leaves the exact source scalar and Fourier normalization unchanged. -/
theorem dirichletMeanEnvelopeOfA_X_le_countAbsorbedUniformBound
    {r q : ℕ} {ι : Type*} (R : Finset (Fin r → Fin q)) (J : Finset ι)
    (κ : ℂ) (A : ℝ → ℂ) {T0 W : ℝ} (M N : ℝ)
    (hM : 0 ≤ M)
    (hCount : (R.card : ℝ) * (J.card : ℝ) ≤ N)
    (hUniform : dirichletMeanEnvelopeOfA_X A T0 W ≤
      ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ((R.card : ℝ) * (J.card : ℝ) * M))) :
    dirichletMeanEnvelopeOfA_X A T0 W ≤
      ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ * (N * M)) := by
  have hcountM := mul_le_mul_of_nonneg_right hCount hM
  have hscalar : 0 ≤ ‖κ‖ * (2 * Real.pi : ℝ)⁻¹ :=
    mul_nonneg (norm_nonneg κ) (by positivity)
  calc
    dirichletMeanEnvelopeOfA_X A T0 W ≤
        ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
          ((R.card : ℝ) * (J.card : ℝ) * M)) := hUniform
    _ = (‖κ‖ * (2 * Real.pi : ℝ)⁻¹) *
        ((R.card : ℝ) * (J.card : ℝ) * M) := by ring
    _ ≤ (‖κ‖ * (2 * Real.pi : ℝ)⁻¹) * (N * M) :=
      mul_le_mul_of_nonneg_left hcountM hscalar
    _ = ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ * (N * M)) := by ring
  

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.dirichletMeanEnvelopeOfA_X_le_scaledBlockProductMeans
#print axioms FractionalPrimes.Literature.DirichletAdapter.dirichletMeanEnvelopeOfA_X_le_sourceThreeGroupBlockMeans
#print axioms FractionalPrimes.Literature.DirichletAdapter.dirichletMeanEnvelopeOfA_X_le_scaledBlockFourierBounds
#print axioms FractionalPrimes.Literature.DirichletAdapter.dirichletMeanEnvelopeOfA_X_le_scaledBlockUniformFourierBound
#print axioms FractionalPrimes.Literature.DirichletAdapter.dirichletMeanEnvelopeOfA_X_le_countAbsorbedUniformBound
#print axioms FractionalPrimes.Literature.DirichletAdapter.productDirichletMeanEnvelope_le_sum_of_polynomialExpansion_differentTypes
#print axioms FractionalPrimes.Literature.DirichletAdapter.productDirichletMeanEnvelope_fourierIntegral_le_sum_of_polynomialExpansion_differentTypes
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownThreeGroupResidueProduct_sourceBlockExpansion
#print axioms FractionalPrimes.Literature.DirichletAdapter.dirichletMeanEnvelopeOfA_X_le_scaledProductMeans
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPBlockIndex_shift_mem
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPBlockScale_eq_integerShift
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupBlock_shiftBounds
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupBlockScales_eq_integerShifts
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupBlockProductScale_eq_integerShifts
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupBlockFactors_eq_integerShiftFactors
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupBlockSourceInterval_fromShiftOutput
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupBlockSourceInterval_of_IImaj
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupBlockUniformNumerical_of_IImaj
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupGroups_nonempty_of_weightBounds
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupBlockUniformAbsorbed_of_IImaj
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPProductWindowEnvelope_of_IImaj
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownThreeGroupBlock_fourierIntegral_le_of_sourceIntervals_firstMoment
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupBlockIndexSet_card_le
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPThreeGroupResidueBlockCount_le_logPower
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownThreeGroupSourceInterval_to_blockScales
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownThreeGroupBlock_fourierIntegral_le_of_sourceIntervals
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownResidueGroupBroadWindow_sum_eq_dyadicBlockPolynomials
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownResidueGroupBroadWindow_sum_eq_factorMellinProduct
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownResidueFactorFiniteSupport_mellinPolynomial_eq
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownResidueFactorFiniteSupport_cpowSum_eq_mellinPolynomial
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownDPGroupTupleSupportWindow
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownResidueGroupBroadWindow_sum_eq_factorPolynomials
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownResidueGroupFactorProduct_eq_dyadicBlocks
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownThreeGroupResidueProduct_eq_blockTripleSum
