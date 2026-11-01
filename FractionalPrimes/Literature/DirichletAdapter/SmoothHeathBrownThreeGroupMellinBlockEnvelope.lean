module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupTrilinearInstantiation
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupSourceDPIntegral
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThreeGroupHighFrequency
public import FractionalPrimes.Literature.Polynomial.PolynomialProductMeanEnvelope
public import Mathlib.Tactic
@[expose] public section

/-! A source-faithful finite bridge from an actual residue-restricted
Heath--Brown block polynomial to the finitely-supported Mellin factors used
by the product mean envelope. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.LargeValues
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open MeasureTheory
open scoped FourierTransform

/-- A coefficient sequence supported on the source Dirichlet block, viewed
as a finitely supported positive-integer Mellin factor. -/
noncomputable def smoothHeathBrownBlockMellinFactor
    (L : ℝ) (coeff : ℕ → ℂ)
    (hsupport : ∀ n, coeff n ≠ 0 → n ∈ dirichletIndices L) :
    MellinSeparationFactor := by
  classical
  let f : PositiveInteger → ℂ := fun n => coeff n.1
  have hf : (Function.support f).Finite := by
    have hindices : ((dirichletIndices L : Finset ℕ) : Set ℕ).Finite :=
      (dirichletIndices L).finite_toSet
    have hpre : {n : PositiveInteger | n.1 ∈ dirichletIndices L}.Finite := by
      apply hindices.preimage
      intro n hn m hm hnm
      exact Subtype.ext hnm
    apply hpre.subset
    intro n hn
    change f n ≠ 0 at hn
    have hcoeff : coeff n.1 ≠ 0 := hn
    exact hsupport n.1 hcoeff
  exact Finsupp.ofSupportFinite f hf

@[simp] theorem smoothHeathBrownBlockMellinFactor_apply
    (L : ℝ) (coeff : ℕ → ℂ)
    (hsupport : ∀ n, coeff n ≠ 0 → n ∈ dirichletIndices L)
    (n : PositiveInteger) :
    smoothHeathBrownBlockMellinFactor L coeff hsupport n = coeff n.1 := by
  classical
  simp [smoothHeathBrownBlockMellinFactor]

theorem smoothHeathBrownResidueGroupBlockCoefficient_support
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L : ℝ) (n : ℕ)
    (hn : smoothHeathBrownResidueGroupBlockCoefficient (z := z)
      fs I q residue L n ≠ 0) :
    n ∈ dirichletIndices L := by
  by_contra hnot
  exact hn (by simp [smoothHeathBrownResidueGroupBlockCoefficient, hnot])

/-- The Mellin factor for an actual residue-restricted smooth group block. -/
noncomputable def smoothHeathBrownResidueGroupBlockMellinFactor
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L : ℝ) : MellinSeparationFactor :=
  smoothHeathBrownBlockMellinFactor L
    (smoothHeathBrownResidueGroupBlockCoefficient (z := z) fs I q residue L)
    (smoothHeathBrownResidueGroupBlockCoefficient_support fs I q residue L)

@[simp] theorem smoothHeathBrownResidueGroupBlockMellinFactor_apply
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L : ℝ) (n : PositiveInteger) :
    smoothHeathBrownResidueGroupBlockMellinFactor (z := z) fs I q residue L n =
      smoothHeathBrownResidueGroupBlockCoefficient (z := z) fs I q residue L n.1 := by
  simp [smoothHeathBrownResidueGroupBlockMellinFactor]

private theorem mellinSeparationMonomial_eq_cpow
    (n : PositiveInteger) (s : ℂ) :
    mellinSeparationMonomial n s = (n.1 : ℂ) ^ (-s) := by
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  calc
    Complex.exp (-s * (Real.log (n.1 : ℝ) : ℂ)) =
        Complex.exp ((-s) * (Real.log (n.1 : ℝ) : ℂ)) := by ring_nf
    _ = (n.1 : ℂ) ^ (-s) := by
      symm
      rw [show (n.1 : ℂ) = ((n.1 : ℝ) : ℂ) by norm_cast]
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'),
        Complex.ofReal_log hn.le]
      congr 1
      ring

private theorem smoothHeathBrownBlockMellinFactor_polynomial
    {L : ℝ} (hL : 0 < L) (coeff : ℕ → ℂ)
    (hsupport : ∀ n, coeff n ≠ 0 → n ∈ dirichletIndices L)
    (s : ℂ) :
    mellinSeparationFactorPolynomial
        (fun _ : Fin 1 => smoothHeathBrownBlockMellinFactor L coeff hsupport)
        1 0 ⟨0, by omega⟩ s =
      ∑ n ∈ dirichletIndices L,
        coeff n * Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
  classical
  let α : MellinSeparationFactor :=
    smoothHeathBrownBlockMellinFactor L coeff hsupport
  let term : ℕ → ℂ := fun n =>
    coeff n * Complex.exp (-s * (Real.log (n : ℝ) : ℂ))
  have hterm (n : ℕ) : term n ≠ 0 ↔ coeff n ≠ 0 := by
    simp [term, Complex.exp_ne_zero]
  have hres (n : PositiveInteger) :
      Int.ModEq (1 : ℤ) (n.1 : ℤ) 0 := by
    simp [Int.ModEq]
  have hfilter :
      α.support.filter (fun n => Int.ModEq (1 : ℤ) (n.1 : ℤ) 0) = α.support := by
    apply Finset.filter_eq_self.mpr
    intro n hn
    exact hres n
  change (∑ n ∈ α.support.filter
      (fun n => Int.ModEq (1 : ℤ) (n.1 : ℤ) (0 : ℤ)),
        α n * mellinSeparationMonomial n s) = _
  rw [hfilter]
  have hbij :
      (∑ n ∈ α.support, α n * mellinSeparationMonomial n s) =
        ∑ n ∈ (dirichletIndices L).filter (fun n => term n ≠ 0), term n := by
    apply Finset.sum_bij (fun n _ => n.1)
    · intro n hn
      rw [Finset.mem_filter]
      constructor
      · have hcoeff : coeff n.1 ≠ 0 := by
          simpa [α, smoothHeathBrownBlockMellinFactor] using
            (Finsupp.mem_support_iff.mp hn)
        exact hsupport n.1 hcoeff
      · exact (hterm n.1).2 (by
          simpa [α, smoothHeathBrownBlockMellinFactor] using
            (Finsupp.mem_support_iff.mp hn))
    · intro n hn m hm hnm
      exact Subtype.ext hnm
    · intro n hn
      rw [Finset.mem_filter] at hn
      rcases hn with ⟨hnidx, hnterm⟩
      have hnpos : 0 < n := by
        have hleft : L < (n : ℝ) := by
          rw [dirichletIndices, Finset.mem_filter, Finset.mem_range] at hnidx
          exact hnidx.2
        have hnreal : 0 < (n : ℝ) := lt_trans hL hleft
        exact_mod_cast hnreal
      have hncoeff : coeff n ≠ 0 := (hterm n).1 hnterm
      let p : PositiveInteger := ⟨n, hnpos⟩
      refine ⟨p, ?_, ?_⟩
      · rw [Finsupp.mem_support_iff]
        change smoothHeathBrownBlockMellinFactor L coeff hsupport p ≠ 0
        rw [smoothHeathBrownBlockMellinFactor_apply]
        simpa [p] using hncoeff
      · rfl
    · intro n hn
      simp [term, α, smoothHeathBrownBlockMellinFactor,
        mellinSeparationMonomial]
  calc
    (∑ n ∈ α.support, α n * mellinSeparationMonomial n s) =
        ∑ n ∈ (dirichletIndices L).filter (fun n => term n ≠ 0), term n := hbij
    _ = ∑ n ∈ dirichletIndices L, term n := by
      rw [Finset.sum_filter_ne_zero]
    _ = _ := by simp [term]

/-- The finite Mellin polynomial of an actual residue-restricted group block
is exactly its source factor polynomial, with the arbitrary shift retained.
This identity connects the source block estimates to the product mean
envelope. -/
theorem smoothHeathBrownResidueGroupBlockMellinFactor_polynomial_eq
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L u t : ℝ) (hL : 0 < L) :
    mellinSeparationFactorPolynomial
        (fun _ : Fin 1 =>
          smoothHeathBrownResidueGroupBlockMellinFactor (z := z)
            fs I q residue L)
        1 0 ⟨0, by omega⟩
        (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) =
      factorPolynomial L
        (smoothHeathBrownResidueGroupBlockTwistedCoefficient
          (z := z) fs I q residue L u) t := by
  classical
  let coeff : ℕ → ℂ := smoothHeathBrownResidueGroupBlockCoefficient
    (z := z) fs I q residue L
  let α : MellinSeparationFactor :=
    smoothHeathBrownResidueGroupBlockMellinFactor (z := z) fs I q residue L
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)
  have hpoly := smoothHeathBrownBlockMellinFactor_polynomial hL coeff
    (smoothHeathBrownResidueGroupBlockCoefficient_support fs I q residue L) s
  have hpoly' :
      mellinSeparationFactorPolynomial (fun _ : Fin 1 => α) 1 0
        ⟨0, by omega⟩ s =
        ∑ n ∈ dirichletIndices L,
          coeff n * Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
    simpa [α, coeff, smoothHeathBrownResidueGroupBlockMellinFactor] using hpoly
  have hidx : dirichletIndices L = factorExtractionRealInterval L (2 * L) :=
    dirichletIndices_eq_factorExtractionRealInterval hL.le
  have hsum :
      (∑ n ∈ dirichletIndices L,
        coeff n * Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) =
      ∑ n ∈ factorExtractionRealInterval L (2 * L),
        (∏ i : I,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (fs i.val)) n *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
            Complex.I * ((t - u : ℝ) : ℂ)) := by
    rw [hidx]
    apply Finset.sum_congr rfl
    intro n hn
    have hnwindow :=
      (mem_factorExtractionRealInterval (by linarith : 0 ≤ L)
        (by positivity : 0 ≤ 2 * L) n).mp hn
    have hnreal : 0 < (n : ℝ) := lt_trans hL hnwindow.1
    have hnpos : 0 < n := by exact_mod_cast hnreal
    have hnidx : n ∈ dirichletIndices L := by rw [hidx]; exact hn
    have hcoeff : coeff n =
        (∏ i : I,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (fs i.val)) n := by
      simp [coeff, smoothHeathBrownResidueGroupBlockCoefficient, hnidx]
    rw [hcoeff]
    have hmon : Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) =
        (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * ((t - u : ℝ) : ℂ)) := by
      have hmono := mellinSeparationMonomial_eq_cpow
        (⟨n, hnpos⟩ : PositiveInteger) s
      have hsexp : -s = (-(1 / 2 : ℂ)) -
          Complex.I * ((t - u : ℝ) : ℂ) := by
        dsimp [s]
        push_cast
        ring
      calc
        Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) =
            mellinSeparationMonomial ⟨n, hnpos⟩ s := rfl
        _ = (n : ℂ) ^ (-s) := by simpa using hmono
        _ = _ := by rw [hsexp]
    rw [hmon]
  have hsource := smoothHeathBrownResidueGroupBlock_factorPolynomial_eq_sourceInterval
    (z := z) fs I q residue L u t hL
  change mellinSeparationFactorPolynomial (fun _ : Fin 1 => α) 1 0
    ⟨0, by omega⟩ s = _
  calc
    mellinSeparationFactorPolynomial (fun _ : Fin 1 => α) 1 0
        ⟨0, by omega⟩ s =
      ∑ n ∈ dirichletIndices L,
        coeff n * Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := hpoly'
    _ = ∑ n ∈ factorExtractionRealInterval L (2 * L),
        (∏ i : I,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (fs i.val)) n *
          (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
            Complex.I * ((t - u : ℝ) : ℂ)) := hsum
    _ = factorPolynomial L
        (smoothHeathBrownResidueGroupBlockTwistedCoefficient
          (z := z) fs I q residue L u) t := hsource.symm

/-- A uniform bound for every tail in the compact source window bounds the
corresponding product mean envelope. The normalization `T₀/V` is retained
exactly, and is at most one throughout its source parameter interval. -/
theorem productDirichletMeanEnvelope_le_of_tailBound
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {T0 W : ℝ} (u C : ℝ)
    (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hTail : ∀ V ∈ Set.Icc T0 (T0 * W ^ 4),
      productDirichletTailIntegral α b W u V ≤ C) :
    productDirichletMeanEnvelope α b T0 W u ≤ C := by
  obtain ⟨V, hV, hEq, hmax⟩ :=
    productDirichletMeanEnvelope_hasMaximum α b (u := u) hW hWT
  rw [← hEq]
  have hVpos : 0 < V := by
    have hT0 : 0 < T0 := lt_of_lt_of_le (by linarith) hWT
    exact lt_of_lt_of_le hT0 hV.1
  have hWpos : 0 < W := by linarith
  have hTailMeas : MeasurableSet {t : ℝ | W ≤ |t| ∧ |t| ≤ V} := by
    change MeasurableSet ((fun t : ℝ => |t|) ⁻¹' Set.Icc W V)
    exact (isClosed_Icc.preimage continuous_abs).measurableSet
  have hTailNonneg : 0 ≤ productDirichletTailIntegral α b W u V :=
    setIntegral_nonneg hTailMeas (by intro t ht; exact norm_nonneg _)
  have hratio : T0 / V ≤ 1 := by
    apply (div_le_iff₀ hVpos).2
    linarith [hV.1]
  calc
    productDirichletMeanObjective α b T0 W u V =
        (T0 / V) * productDirichletTailIntegral α b W u V := rfl
    _ ≤ 1 * productDirichletTailIntegral α b W u V :=
      mul_le_mul_of_nonneg_right hratio hTailNonneg
    _ = productDirichletTailIntegral α b W u V := by ring
    _ ≤ C := hTail V hV

/-- The three Mellin factors associated with the actual selected-group block
triple. The index order is precisely `(I₁,I₂,I₃)`. -/
noncomputable def smoothHeathBrownThreeGroupBlockMellinFactors
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I₁ I₂ I₃ : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L₁ L₂ L₃ : ℝ) : Fin 3 → MellinSeparationFactor := by
  exact fun j => Fin.cases
    (smoothHeathBrownResidueGroupBlockMellinFactor (z := z)
      fs I₁ q residue L₁)
    (fun j => Fin.cases
      (smoothHeathBrownResidueGroupBlockMellinFactor (z := z)
        fs I₂ q residue L₂)
      (fun _ => smoothHeathBrownResidueGroupBlockMellinFactor (z := z)
        fs I₃ q residue L₃) j) j

/-- The product polynomial of the three Mellin factors is the exact product
of the three actual shifted group block polynomials. -/
theorem smoothHeathBrownThreeGroupBlockMellinFactors_polynomial_eq
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I₁ I₂ I₃ : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L₁ L₂ L₃ u t : ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃) :
    productDirichletPolynomialsAt
      (smoothHeathBrownThreeGroupBlockMellinFactors
        (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃)
      (fun _ : Fin 3 => (0 : Fin 1)) t u =
      factorPolynomial L₁
        (smoothHeathBrownResidueGroupBlockTwistedCoefficient
          (z := z) fs I₁ q residue L₁ u) t *
      factorPolynomial L₂
        (smoothHeathBrownResidueGroupBlockTwistedCoefficient
          (z := z) fs I₂ q residue L₂ u) t *
      factorPolynomial L₃
        (smoothHeathBrownResidueGroupBlockTwistedCoefficient
          (z := z) fs I₃ q residue L₃ u) t := by
  classical
  let α := smoothHeathBrownThreeGroupBlockMellinFactors
    (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃
  have hα0 : α 0 = smoothHeathBrownResidueGroupBlockMellinFactor
      (z := z) fs I₁ q residue L₁ := by
    rfl
  have hα1 : α 1 = smoothHeathBrownResidueGroupBlockMellinFactor
      (z := z) fs I₂ q residue L₂ := by
    rfl
  have hα2 : α 2 = smoothHeathBrownResidueGroupBlockMellinFactor
      (z := z) fs I₃ q residue L₃ := by
    rfl
  have h0 := smoothHeathBrownResidueGroupBlockMellinFactor_polynomial_eq
    (z := z) fs I₁ q residue L₁ u t hL₁
  have h1 := smoothHeathBrownResidueGroupBlockMellinFactor_polynomial_eq
    (z := z) fs I₂ q residue L₂ u t hL₂
  have h2 := smoothHeathBrownResidueGroupBlockMellinFactor_polynomial_eq
    (z := z) fs I₃ q residue L₃ u t hL₃
  have hpoly0 : mellinSeparationFactorPolynomial α 1 0 0
      (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) =
      factorPolynomial L₁
        (smoothHeathBrownResidueGroupBlockTwistedCoefficient
          (z := z) fs I₁ q residue L₁ u) t := by
    rw [mellinSeparationFactorPolynomial, hα0]
    simpa [mellinSeparationFactorPolynomial, Int.ModEq] using h0
  have hpoly1 : mellinSeparationFactorPolynomial α 1 1 0
      (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) =
      factorPolynomial L₂
        (smoothHeathBrownResidueGroupBlockTwistedCoefficient
          (z := z) fs I₂ q residue L₂ u) t := by
    rw [mellinSeparationFactorPolynomial, hα1]
    simpa [mellinSeparationFactorPolynomial, Int.ModEq] using h1
  have hpoly2 : mellinSeparationFactorPolynomial α 1 2 0
      (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) =
      factorPolynomial L₃
        (smoothHeathBrownResidueGroupBlockTwistedCoefficient
          (z := z) fs I₃ q residue L₃ u) t := by
    rw [mellinSeparationFactorPolynomial, hα2]
    simpa [mellinSeparationFactorPolynomial, Int.ModEq] using h2
  change productDirichletPolynomialsAt α (fun _ : Fin 3 => (0 : Fin 1)) t u = _
  unfold productDirichletPolynomialsAt
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  change mellinSeparationFactorPolynomial α 1 0 0
      (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) *
    (mellinSeparationFactorPolynomial α 1 1 0
        (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) *
      (mellinSeparationFactorPolynomial α 1 2 0
          (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) * 1)) = _
  rw [hpoly0, hpoly1, hpoly2]
  ring

/-- The product mean tail integral for the three Mellin factors is the same
Lebesgue integral as the source actual-residue three-block product, with the
original real half-open window convention preserved. -/
theorem smoothHeathBrownThreeGroupBlock_productTail_eq
    {X z : ℝ} {K : ℕ} (fs : Fin K → SmoothHeathBrownFactor X)
    (I₁ I₂ I₃ : Finset (Fin K)) (q : ℕ) (residue : Fin K → ℕ)
    (L₁ L₂ L₃ W u V : ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃) :
    productDirichletTailIntegral
      (smoothHeathBrownThreeGroupBlockMellinFactors
        (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃)
      (fun _ : Fin 3 => (0 : Fin 1)) W u V =
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
        ‖factorPolynomial L₁
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₁ q residue L₁ u) t *
          factorPolynomial L₂
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₂ q residue L₂ u) t *
          factorPolynomial L₃
            (smoothHeathBrownResidueGroupBlockTwistedCoefficient
              (z := z) fs I₃ q residue L₃ u) t‖ := by
  unfold productDirichletTailIntegral productDirichletTailIntegrand
  apply integral_congr_ae
  filter_upwards with t
  rw [smoothHeathBrownThreeGroupBlockMellinFactors_polynomial_eq
    (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃ u t hL₁ hL₂ hL₃]

/-- The actual-residue low/high shift estimates imply the matching
piecewise product mean-envelope bound. The low-frequency estimate is kept as
an explicit source premise; the high-frequency estimate is discharged by
`ldm:trilinear` after exact Mellin-factor conversion. -/
theorem smoothHeathBrownThreeGroupBlock_productMeanEnvelope_le
    {X z : ℝ} {K : ℕ} (hX : 3 ≤ X)
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I₁ I₂ I₃ : Finset (Fin K))
    (hI₁ : I₁.card ≤ 20) (hI₂ : I₂.card ≤ 20) (hI₃ : I₃.card ≤ 20)
    (q : ℕ) (residue : Fin K → ℕ)
    (L₁ L₂ L₃ Y eps T0 W T Mlow : ℝ)
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
    (hLow : ∀ (u V : ℝ), |u| ≤ W / 2 →
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
              (z := z) fs I₃ q residue L₃ u) t‖ ≤ Mlow) :
    ∀ u : ℝ,
      (|u| ≤ W / 2 →
        productDirichletMeanEnvelope
          (smoothHeathBrownThreeGroupBlockMellinFactors
            (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃)
          (fun _ : Fin 3 => (0 : Fin 1)) T0 W u ≤ Mlow) ∧
      (W / 2 < |u| →
        productDirichletMeanEnvelope
          (smoothHeathBrownThreeGroupBlockMellinFactors
            (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃)
          (fun _ : Fin 3 => (0 : Fin 1)) T0 W u ≤
          Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
            Real.sqrt Y * (1 + Y ^ (-eps / 16 : ℝ))) := by
  classical
  let α := smoothHeathBrownThreeGroupBlockMellinFactors
    (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃
  let bres : Fin 3 → Fin 1 := fun _ => 0
  intro u
  constructor
  · intro hu
    apply productDirichletMeanEnvelope_le_of_tailBound α bres u Mlow hW hWT
    intro V hV
    rw [smoothHeathBrownThreeGroupBlock_productTail_eq
      (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃ W u V hL₁ hL₂ hL₃]
    exact hLow u V hu hV
  · intro hu
    apply productDirichletMeanEnvelope_le_of_tailBound α bres u
      (Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
        Real.sqrt Y * (1 + Y ^ (-eps / 16 : ℝ))) hW hWT
    intro V hV
    have hVT : V ≤ T := hV.2.trans hVtop
    have hYpos : 0 < Y := by positivity
    have hYgt : 1 < Y := by
      have hpow : 1 < (2 : ℝ) ^ 16 := by norm_num
      linarith
    have hlogYpos : 0 < Real.log Y := Real.log_pos hYgt
    have hlogProd : Real.log Y = Real.log L₁ + Real.log L₂ + Real.log L₃ := by
      rw [hYprod]
      rw [Real.log_mul (ne_of_gt (mul_pos hL₁ hL₂)) (ne_of_gt hL₃)]
      rw [Real.log_mul (ne_of_gt hL₁) (ne_of_gt hL₂)]
    have hpow₁ : Y ^ (Real.log L₁ / Real.log Y) = L₁ := by
      rw [Real.rpow_def_of_pos hYpos]
      rw [show Real.log Y * (Real.log L₁ / Real.log Y) = Real.log L₁ by
        field_simp]
      exact Real.exp_log hL₁
    have hpow₂ : Y ^ (Real.log L₂ / Real.log Y) = L₂ := by
      rw [Real.rpow_def_of_pos hYpos]
      rw [show Real.log Y * (Real.log L₂ / Real.log Y) = Real.log L₂ by
        field_simp]
      exact Real.exp_log hL₂
    have hpow₃ : Y ^ (Real.log L₃ / Real.log Y) = L₃ := by
      rw [Real.rpow_def_of_pos hYpos]
      rw [show Real.log Y * (Real.log L₃ / Real.log Y) = Real.log L₃ by
        field_simp]
      exact Real.exp_log hL₃
    let E : Set ℝ := {t : ℝ | W ≤ |t| ∧ |t| ≤ V}
    have hEmeas : MeasurableSet E := by
      change MeasurableSet ((fun t : ℝ => |t|) ⁻¹' Set.Icc W V)
      exact (isClosed_Icc.preimage continuous_abs).measurableSet
    have hEsubset : E ⊆ Set.Icc (-T) T := by
      intro t ht
      have ht' : W ≤ |t| ∧ |t| ≤ V := ht
      exact abs_le.mp (le_trans ht'.2 hVT)
    have hhigh := smoothHeathBrownThreeGroupHighFrequency_actualResidue
      (z := z) hX fs I₁ I₂ I₃ hI₁ hI₂ hI₃ q residue u
      L₁ L₂ L₃ Y eps T E hL₁ hL₂ hL₃ hL₁two hL₂two hL₃two
      hY hYprod hEps0 hEps hTtwo hTupper hαlower hαupper hβγ
      hEmeas hEsubset
    rw [smoothHeathBrownThreeGroupBlock_productTail_eq
      (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃ W u V hL₁ hL₂ hL₃]
    simpa [E, hpow₁, hpow₂, hpow₃] using hhigh

/-- Integrating the piecewise envelope bound against the fixed smooth Mellin
Fourier kernel separates the full kernel mass from its large-shift tail. -/
theorem productDirichletMeanEnvelope_fourierIntegral_le_of_piecewise
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (bResidue : Fin r → Fin q) {T0 W : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0) (Mlow Mhigh Ktail : ℝ)
    (hMlow : 0 ≤ Mlow) (hMhigh : 0 ≤ Mhigh)
    (hPiece : ∀ u : ℝ,
      (|u| ≤ W / 2 →
        productDirichletMeanEnvelope α bResidue T0 W u ≤ Mlow) ∧
      (W / 2 < |u| →
        productDirichletMeanEnvelope α bResidue T0 W u ≤ Mhigh))
    (hKernelTail :
      ∫ u in {u : ℝ | W / 2 < |u|},
        ‖mellinSeparationLogKernelFourier u‖ ≤ Ktail) :
    (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
      productDirichletMeanEnvelope α bResidue T0 W u) ≤
      Mlow * (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖) +
        Mhigh * Ktail := by
  classical
  let Kfun : ℝ → ℝ := fun u => ‖mellinSeparationLogKernelFourier u‖
  let high : Set ℝ := {u : ℝ | W / 2 < |u|}
  have hK : Integrable Kfun := by
    simpa [Kfun] using mellinSeparationLogKernelFourier_integrable.norm
  have hHighMeas : MeasurableSet high := by
    change MeasurableSet ((fun u : ℝ => |u|) ⁻¹' Set.Ioi (W / 2))
    exact (isOpen_Ioi.preimage continuous_abs).measurableSet
  have hHighK : Integrable (Set.indicator high Kfun) :=
    (hK.integrableOn (s := high)).integrable_indicator hHighMeas
  have hLeft : Integrable (fun u : ℝ => Kfun u *
      productDirichletMeanEnvelope α bResidue T0 W u) := by
    simpa [Kfun] using
      productDirichletMeanEnvelope_weighted_integrable α bResidue hW hWT
  have hRight : Integrable (fun u : ℝ =>
      Mlow * Kfun u + Mhigh * Set.indicator high Kfun u) :=
    (hK.const_mul Mlow).add (hHighK.const_mul Mhigh)
  have hPoint (u : ℝ) :
      Kfun u * productDirichletMeanEnvelope α bResidue T0 W u ≤
        Mlow * Kfun u + Mhigh * Set.indicator high Kfun u := by
    by_cases hu : u ∈ high
    · have hu' : W / 2 < |u| := hu
      have henv := (hPiece u).2 hu'
      have hknonneg : 0 ≤ Kfun u := norm_nonneg _
      have hmul := mul_le_mul_of_nonneg_left henv hknonneg
      simpa [Kfun, Set.indicator, high, hu, mul_comm] using
        (calc
          Kfun u * productDirichletMeanEnvelope α bResidue T0 W u ≤
              Kfun u * Mhigh := hmul
          _ ≤ Mlow * Kfun u + Kfun u * Mhigh := by
              nlinarith [mul_nonneg hMlow hknonneg]
          _ = Mlow * Kfun u + Mhigh * Kfun u := by ring)
    · have hu' : |u| ≤ W / 2 := by
        by_contra h
        exact hu (by change W / 2 < |u|; exact lt_of_not_ge h)
      have henv := (hPiece u).1 hu'
      have hknonneg : 0 ≤ Kfun u := norm_nonneg _
      have hmul := mul_le_mul_of_nonneg_left henv hknonneg
      simpa [Kfun, Set.indicator, high, hu, mul_comm] using hmul
  have hmono := integral_mono hLeft hRight hPoint
  calc
    (∫ u : ℝ, Kfun u * productDirichletMeanEnvelope α bResidue T0 W u) ≤
        ∫ u : ℝ, Mlow * Kfun u + Mhigh * Set.indicator high Kfun u := hmono
    _ = Mlow * (∫ u : ℝ, Kfun u) +
          Mhigh * (∫ u : ℝ, Set.indicator high Kfun u) := by
      rw [integral_add (hK.const_mul Mlow) (hHighK.const_mul Mhigh),
        integral_const_mul, integral_const_mul]
    _ = Mlow * (∫ u : ℝ, Kfun u) +
          Mhigh * (∫ u in high, Kfun u) := by
      rw [integral_indicator hHighMeas]
    _ ≤ Mlow * (∫ u : ℝ, Kfun u) + Mhigh * Ktail := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hKernelTail hMhigh) _

/-- The source-facing Fourier-weighted envelope bound for one actual
three-group residue block.  It combines the low-shift interval input with
the checked high-shift trilinear estimate, without dropping the arbitrary
Mellin shift or changing the product-scale window. -/
theorem smoothHeathBrownThreeGroupBlock_fourierIntegral_le
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
    (hLow : ∀ (u V : ℝ), |u| ≤ W / 2 →
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
  classical
  let α : Fin 3 → MellinSeparationFactor :=
    smoothHeathBrownThreeGroupBlockMellinFactors
      (z := z) fs I₁ I₂ I₃ q residue L₁ L₂ L₃
  let bres : Fin 3 → Fin 1 := fun _ => 0
  let Mhigh : ℝ := Z 20 Y ^ 3 * J 20 * (Real.log (4 * Y)) ^ (b 20 + 3) *
    Real.sqrt Y * (1 + Y ^ (-eps / 16 : ℝ))
  have hMhigh : 0 ≤ Mhigh := by
    dsimp [Mhigh, Z]
    have hYpos : 0 < Y := by linarith
    have hYgt : 1 < Y := by
      have hpow : 1 < (2 : ℝ) ^ 16 := by norm_num
      linarith
    have hlog : 0 < Real.log (4 * Y) := by
      apply Real.log_pos
      nlinarith
    have hlogY : 0 < Real.log Y := Real.log_pos hYgt
    have hJ : 0 < J 20 := (constants_positive 20).2.2.2
    have hZ : 0 <
        (2 : ℝ) ^ (2 ^ 20 + 1) * (Real.log (4 * Y)) ^ (2 ^ 20 - 1) := by
      positivity
    have hfactor : 0 < 1 + Y ^ (-eps / 16 : ℝ) := by
      have hrpow : 0 < Y ^ (-eps / 16 : ℝ) := Real.rpow_pos_of_pos hYpos _
      linarith
    positivity
  have hPiece := smoothHeathBrownThreeGroupBlock_productMeanEnvelope_le
    (z := z) hX fs I₁ I₂ I₃ hI₁ hI₂ hI₃ q residue
    L₁ L₂ L₃ Y eps T0 W T Mlow hL₁ hL₂ hL₃ hL₁two hL₂two hL₃two
    hY hYprod hEps0 hEps hTtwo hTupper hαlower hαupper hβγ
    hW hWT hVtop hLow
  have hPiece' : ∀ u : ℝ,
      (|u| ≤ W / 2 → productDirichletMeanEnvelope α bres T0 W u ≤ Mlow) ∧
      (W / 2 < |u| → productDirichletMeanEnvelope α bres T0 W u ≤ Mhigh) := by
    intro u
    simpa [α, bres, Mhigh] using hPiece u
  have hresult := productDirichletMeanEnvelope_fourierIntegral_le_of_piecewise
    α bres hW hWT Mlow Mhigh Ktail hMlow hMhigh hPiece' hKernelTail
  simpa [α, bres, Mhigh] using hresult

/-- The angular Fourier kernel has an integrable first absolute moment.  This
is obtained directly from the Schwartz Fourier transform and the exact
`u/(2π)` normalization used by Mellin separation. -/
theorem mellinSeparationLogKernelFourier_absMoment_integrable :
    Integrable (fun u : ℝ => |u| *
      ‖mellinSeparationLogKernelFourier u‖) := by
  have hF : Integrable (fun v : ℝ => |v| *
      ‖(𝓕 mellinSeparationLogKernelSchwartz) v‖) := by
    convert (𝓕 mellinSeparationLogKernelSchwartz).integrable_pow_mul volume 1 using 1
    ext v
    simp [Real.norm_eq_abs]
  have hc : 0 < (2 * Real.pi : ℝ) := by positivity
  have hcn : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hc
  have hscaled := hF.comp_div hcn
  have hscaled' := hscaled.const_mul (2 * Real.pi : ℝ)
  apply hscaled'.congr
  filter_upwards with u
  change (2 * Real.pi : ℝ) *
      (|u / (2 * Real.pi)| *
        ‖(𝓕 mellinSeparationLogKernelSchwartz) (u / (2 * Real.pi))‖) =
    |u| * ‖mellinSeparationLogKernelFourier u‖
  rw [mellinSeparationLogKernelFourier_eq_fourier]
  have hu : (2 * Real.pi : ℝ) * |u / (2 * Real.pi)| = |u| := by
    rw [abs_div, abs_of_pos hc]
    field_simp
  calc
    (2 * Real.pi : ℝ) *
        (|u / (2 * Real.pi)| *
          ‖(𝓕 mellinSeparationLogKernelSchwartz) (u / (2 * Real.pi))‖) =
        ((2 * Real.pi : ℝ) * |u / (2 * Real.pi)|) *
          ‖(𝓕 mellinSeparationLogKernelSchwartz) (u / (2 * Real.pi))‖ := by ring
    _ = |u| * ‖(𝓕 mellinSeparationLogKernelSchwartz) (u / (2 * Real.pi))‖ := by
      rw [hu]

/-- The large-shift Fourier-kernel mass is bounded by its first moment with
the exact reciprocal cutoff factor. -/
theorem mellinSeparationLogKernelFourier_tail_le_firstMoment
    {W : ℝ} (hW : 0 < W) :
    ∫ u in {u : ℝ | W / 2 < |u|},
      ‖mellinSeparationLogKernelFourier u‖ ≤
      (2 / W) * (∫ u : ℝ, |u| *
        ‖mellinSeparationLogKernelFourier u‖) := by
  classical
  let Kfun : ℝ → ℝ := fun u => ‖mellinSeparationLogKernelFourier u‖
  let high : Set ℝ := {u : ℝ | W / 2 < |u|}
  have hK : Integrable Kfun := by
    simpa [Kfun] using mellinSeparationLogKernelFourier_integrable.norm
  have hMoment : Integrable (fun u : ℝ => |u| * Kfun u) := by
    simpa [Kfun] using mellinSeparationLogKernelFourier_absMoment_integrable
  have hHighMeas : MeasurableSet high := by
    change MeasurableSet ((fun u : ℝ => |u|) ⁻¹' Set.Ioi (W / 2))
    exact (isOpen_Ioi.preimage continuous_abs).measurableSet
  have hHighK : Integrable (Set.indicator high Kfun) :=
    (hK.integrableOn (s := high)).integrable_indicator hHighMeas
  have hRight : Integrable (fun u : ℝ => (2 / W) * (|u| * Kfun u)) :=
    hMoment.const_mul (2 / W)
  have hPoint (u : ℝ) :
      Set.indicator high Kfun u ≤ (2 / W) * (|u| * Kfun u) := by
    by_cases hu : u ∈ high
    · have hu' : W / 2 < |u| := hu
      have hscale : 1 ≤ (2 / W) * |u| := by
        calc
          1 ≤ (2 * |u|) / W := (le_div_iff₀ hW).2 (by nlinarith)
          _ = (2 / W) * |u| := by ring
      have hmul := mul_le_mul_of_nonneg_right hscale
        (norm_nonneg (mellinSeparationLogKernelFourier u))
      rw [Set.indicator_of_mem hu]
      calc
        Kfun u = 1 * Kfun u := by ring
        _ ≤ ((2 / W) * |u|) * Kfun u := hmul
        _ = (2 / W) * (|u| * Kfun u) := by ring
    · simp only [Set.indicator, hu, if_false]
      positivity
  have hmono := integral_mono hHighK hRight hPoint
  rw [integral_indicator hHighMeas, integral_const_mul] at hmono
  simpa [Kfun] using hmono

/-- A finite exact expansion of a product Dirichlet polynomial transfers to
the corresponding sum of product mean envelopes.  This is the general
outer-block accumulation step; the polynomial identity is kept as an
explicit source-facing input. -/
theorem productDirichletMeanEnvelope_le_sum_of_polynomialExpansion
    {r q : ℕ} {ι : Type*} (J : Finset ι)
    (α : Fin r → MellinSeparationFactor) (bResidue : Fin r → Fin q)
    (blockFactors : ι → Fin r → MellinSeparationFactor)
    (blockResidues : ι → Fin r → Fin q)
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
  have hEcompact : IsCompact E := by
    exact isCompact_Icc.of_isClosed_subset hEclosed hEsubset
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

/-- Integrating a finite exact block expansion preserves the same finite sum
of block envelope integrals. -/
theorem productDirichletMeanEnvelope_fourierIntegral_le_sum_of_polynomialExpansion
    {r q : ℕ} {ι : Type*} (J : Finset ι)
    (α : Fin r → MellinSeparationFactor) (bResidue : Fin r → Fin q)
    (blockFactors : ι → Fin r → MellinSeparationFactor)
    (blockResidues : ι → Fin r → Fin q) {T0 W : ℝ}
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
  have hRight : Integrable (fun u : ℝ => ∑ i ∈ J, Kfun u *
      productDirichletMeanEnvelope
        (blockFactors i) (blockResidues i) T0 W u) := by
    apply integrable_finsetSum J
    intro i hi
    simpa [Kfun] using
      productDirichletMeanEnvelope_weighted_integrable
        (blockFactors i) (blockResidues i) hW hWT
  have hPoint (u : ℝ) :
      Kfun u * productDirichletMeanEnvelope α bResidue T0 W u ≤
        ∑ i ∈ J, Kfun u *
          productDirichletMeanEnvelope
            (blockFactors i) (blockResidues i) T0 W u := by
    have henv := productDirichletMeanEnvelope_le_sum_of_polynomialExpansion
      J α bResidue blockFactors blockResidues hW hWT (fun t => hExpansion t u)
    have hKnonneg : 0 ≤ Kfun u := norm_nonneg _
    calc
      Kfun u * productDirichletMeanEnvelope α bResidue T0 W u ≤
          Kfun u *
            (∑ i ∈ J, productDirichletMeanEnvelope
              (blockFactors i) (blockResidues i) T0 W u) :=
        mul_le_mul_of_nonneg_left henv hKnonneg
      _ = ∑ i ∈ J, Kfun u *
          productDirichletMeanEnvelope
            (blockFactors i) (blockResidues i) T0 W u := by
        rw [Finset.mul_sum]
  have hmono := integral_mono hLeft hRight hPoint
  calc
    (∫ u : ℝ, Kfun u * productDirichletMeanEnvelope α bResidue T0 W u) ≤
        ∫ u : ℝ, ∑ i ∈ J, Kfun u *
          productDirichletMeanEnvelope
            (blockFactors i) (blockResidues i) T0 W u := hmono
    _ = ∑ i ∈ J, ∫ u : ℝ, Kfun u *
          productDirichletMeanEnvelope
            (blockFactors i) (blockResidues i) T0 W u := by
      rw [integral_finsetSum]
      intro i hi
      exact (productDirichletMeanEnvelope_weighted_integrable
        (blockFactors i) (blockResidues i) hW hWT)
    _ = ∑ i ∈ J, ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          productDirichletMeanEnvelope
            (blockFactors i) (blockResidues i) T0 W u := by
      rfl

#print axioms smoothHeathBrownBlockMellinFactor
#print axioms smoothHeathBrownResidueGroupBlockMellinFactor_polynomial_eq
#print axioms productDirichletMeanEnvelope_le_of_tailBound
#print axioms smoothHeathBrownThreeGroupBlockMellinFactors_polynomial_eq
#print axioms smoothHeathBrownThreeGroupBlock_productTail_eq
#print axioms smoothHeathBrownThreeGroupBlock_productMeanEnvelope_le
#print axioms productDirichletMeanEnvelope_fourierIntegral_le_of_piecewise
#print axioms smoothHeathBrownThreeGroupBlock_fourierIntegral_le
#print axioms mellinSeparationLogKernelFourier_absMoment_integrable
#print axioms mellinSeparationLogKernelFourier_tail_le_firstMoment
#print axioms productDirichletMeanEnvelope_le_sum_of_polynomialExpansion
#print axioms productDirichletMeanEnvelope_fourierIntegral_le_sum_of_polynomialExpansion

end FractionalPrimes.Literature.DirichletAdapter

end
