module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalComponentSelection
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition
public import FractionalPrimes.Literature.Uniformity.TypeMonotonicity

/-!
# Connecting conditional component selection to inverse-clause inputs

This module starts the source-faithful assembly of the finite `P3` selection
with the checked arithmetic type decomposition and the inverse-correlation
API.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

/-- The real-interval correlation used by the inverse clauses is the same
finite sum as the integer-extension correlation in the `P3` selector. -/
theorem typeIScalarPhaseSum_eq_integerInterval
    (X H : ℕ) (hX : 3 ≤ X) (P : Polynomial ℝ)
    (f : ComplexPositiveIntegerFunction) :
    typeIScalarPhaseSum f P (X : ℝ) (H : ℝ) =
      ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        complexPositiveIntegerZeroExtension f n *
          unitFrequencyPhase (P.eval (n : ℝ)) := by
  classical
  unfold typeIScalarPhaseSum
  apply Finset.sum_bij
    (s := typeIIntervalSet (X : ℝ) (H : ℝ))
    (t := realIntegerInterval (X : ℝ) (H : ℝ))
    (f := fun n : ℕ => complexPositivePhaseTerm f P n)
    (g := fun n : ℤ =>
      complexPositiveIntegerZeroExtension f n *
        unitFrequencyPhase (P.eval (n : ℝ)))
    (fun n _ => (n : ℤ))
  · intro n hn
    have hmem := (mem_typeIIntervalSet (X : ℝ) (H : ℝ) n).mp hn
    exact (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) (n : ℤ)).2
      ⟨by exact_mod_cast hmem.2.1, by exact_mod_cast hmem.2.2⟩
  · intro n hn m hm hnm
    exact_mod_cast hnm
  · intro z hz
    have hbounds :=
      (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) z).mp hz
    have hzpos : 0 < z := by
      have hXpos : (0 : ℤ) < (X : ℤ) := by
        exact_mod_cast (show 0 < X by omega)
      have hXltz : (X : ℤ) < z := by exact_mod_cast hbounds.1
      exact lt_trans hXpos hXltz
    have hcast : ((z.toNat : ℕ) : ℤ) = z :=
      Int.toNat_of_nonneg (le_of_lt hzpos)
    have hcastR : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hcast
    have hnpos : 0 < z.toNat := by
      have : (0 : ℤ) < (z.toNat : ℤ) := by simpa [hcast] using hzpos
      omega
    refine ⟨z.toNat, ?_, hcast⟩
    apply (mem_typeIIntervalSet (X : ℝ) (H : ℝ) z.toNat).2
    exact ⟨Nat.succ_le_iff.mpr hnpos,
      ⟨by simpa [hcastR] using hbounds.1, by simpa [hcastR] using hbounds.2⟩⟩
  · intro n hn
    have hnpos : 0 < n :=
      Nat.lt_of_lt_of_le (by decide : 0 < 1)
        ((mem_typeIIntervalSet (X : ℝ) (H : ℝ) n).mp hn).1
    rw [complexPositivePhaseTerm_eq_natExtension]
    have hext : complexPositiveIntegerNatExtension f n =
        complexPositiveIntegerZeroExtension f (n : ℤ) := by
      simp [complexPositiveIntegerNatExtension,
        complexPositiveIntegerZeroExtension, hnpos]
    rw [hext]
    congr 1

/-- Type classification at the source cutoff, converted to the stricter
logarithmic parameter used by the scalar inverse clauses. The type-II scale
bound is the exact `max(Aplus, X/Aminus)` bound of `lupo:conditional-integer`.
-/
def conditionalIntegerComponentType (X δ : ℝ)
    (f : ComplexPositiveIntegerFunction) : Prop :=
  typeIFunction δ (decompositionC * X ^ (5 / 8 : ℝ)) f ∨
    typeI2Function δ (decompositionC * X ^ (7 / 16 : ℝ)) f ∨
      ∃ Aminus Aplus : ℝ,
        typeIIFunction δ Aminus Aplus f ∧
          max Aplus (X / Aminus) ≤ decompositionC * X ^ (5 / 8 : ℝ)

private theorem conditionalTypeIIScaleBound
    (X Aminus Aplus : ℝ) (hX : 0 < X)
    (hAminus : decompositionC⁻¹ * X ^ (3 / 8 : ℝ) ≤ Aminus)
    (hAplus : Aplus ≤ decompositionC * X ^ (5 / 8 : ℝ)) :
    max Aplus (X / Aminus) ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
  have hCpos : 0 < decompositionC := by
    unfold decompositionC
    exact mul_pos
      (pow_pos (by norm_num : (0 : ℝ) < 2) _)
      (pow_pos (by norm_num : (0 : ℝ) < 81) _)
  have hlowpos : 0 < decompositionC⁻¹ * X ^ (3 / 8 : ℝ) :=
    mul_pos (inv_pos.mpr hCpos) (Real.rpow_pos_of_pos hX _)
  have hAminuspos : 0 < Aminus := lt_of_lt_of_le hlowpos hAminus
  have hratio : X / Aminus ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
    apply (div_le_iff₀ hAminuspos).2
    calc
      X = decompositionC * X ^ (5 / 8 : ℝ) *
          (decompositionC⁻¹ * X ^ (3 / 8 : ℝ)) := by
        have hpow : X ^ (5 / 8 : ℝ) * X ^ (3 / 8 : ℝ) = X := by
          calc
            X ^ (5 / 8 : ℝ) * X ^ (3 / 8 : ℝ) =
                X ^ ((5 / 8 : ℝ) + (3 / 8 : ℝ)) := by
                  rw [← Real.rpow_add hX]
            _ = X := by rw [show (5 / 8 : ℝ) + (3 / 8 : ℝ) = 1 by norm_num,
              Real.rpow_one]
        calc
          X = 1 * X := by ring
          _ = (decompositionC * decompositionC⁻¹) *
              (X ^ (5 / 8 : ℝ) * X ^ (3 / 8 : ℝ)) := by
                rw [hpow]
                field_simp [ne_of_gt hCpos]
          _ = decompositionC * X ^ (5 / 8 : ℝ) *
              (decompositionC⁻¹ * X ^ (3 / 8 : ℝ)) := by ring
      _ ≤ decompositionC * X ^ (5 / 8 : ℝ) * Aminus :=
        mul_le_mul_of_nonneg_left hAminus
          (mul_nonneg hCpos.le (Real.rpow_nonneg hX.le _))
  exact max_le_iff.mpr ⟨hAplus, hratio⟩

theorem elementaryTypeComponent_mono
    (X δ : ℝ) (f : ComplexPositiveIntegerFunction)
    (hX : 3 ≤ X) (hδ : 0 < δ)
    (hδle : δ ≤ decompositionDelta X)
    (hf : elementaryTypeComponent X f) :
    conditionalIntegerComponentType X δ f := by
  rcases hf with hI | hI2 | hII
  · exact Or.inl (typeIFunction_mono hI hδ hδle le_rfl)
  · exact Or.inr (Or.inl (typeI2Function_mono hI2 hδ hδle le_rfl))
  · rcases hII with ⟨z, c, fs, α, hscaleα, hsumα, hscale, hmob, hdata⟩
    rcases hdata with
      ⟨Aminus, Aplus, v, a, b1, γ, η, η', I, J, J', i,
        htype, hfactor, hv, ha, hb, hAminus1, hAminusAplus,
        hAminusLow, hAplusHigh, hsumExp, hgammaLow, hgammaHigh,
        hetaGap, hsupportV, hsupportA, hsupportB, hi, halpha⟩
    have hXpos : 0 < X := by linarith
    have htype' : typeIIFunction δ Aminus Aplus f :=
      typeIIFunction_mono htype hδ hδle hAminus1 le_rfl le_rfl
    exact Or.inr (Or.inr ⟨Aminus, Aplus, htype',
      conditionalTypeIIScaleBound X Aminus Aplus hXpos hAminusLow hAplusHigh⟩)

/-- Select a type-I, type-I₂, or type-II component from the exact finite
arithmetic decomposition after appending one source type-I term. The
decomposition and residual hypotheses have precisely the form used in the
conditional integer proof: for `Λ-Cr_X`, the extra term is `-T_X` and the
residual is `T_X-Cr_X`; for `μ`, both may be zero. -/
theorem exists_conditionalIntegerSelectedComponent
    (X H : ℕ) (A δ : ℝ) (Dexp : ℕ)
    (g : ComplexPositiveIntegerFunction)
    (D : ElementaryArithmeticTypeDecomposition (X : ℝ) g)
    [DecidableEq D.Index]
    (extra : ComplexPositiveIntegerFunction) (w r : ℤ → ℂ)
    (P : Polynomial ℝ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHleX : H ≤ X)
    (hL : 2 ≤ Real.log (X : ℝ))
    (hDelta : δ = (Real.log (X : ℝ)) ^ (-(Dexp : ℝ)))
    (hThreshold : 4 * decompositionC <
      (Real.log (X : ℝ)) ^ ((Dexp : ℝ) - A - (decompositionB : ℝ)))
    (hDeltaType : δ ≤ decompositionDelta (X : ℝ))
    (hExtraType : typeIFunction δ
      (decompositionC * (X : ℝ) ^ (5 / 8 : ℝ)) extra)
    (hDecomposition : ∀ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      w n =
        ((∑ i ∈ D.indices,
          complexPositiveIntegerZeroExtension (D.component i) n) +
          complexPositiveIntegerZeroExtension extra n) + r n)
    (hResidual :
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        r n * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
          (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) / 4)
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖) :
    ∃ j ∈ insert none (D.indices.image (some : D.Index → Option D.Index)),
      conditionalIntegerComponentType (X : ℝ) δ
          (match j with
          | none => extra
          | some i => D.component i) ∧
        δ * (H : ℝ) <
          typeIScalarPhaseCorrelation
            (match j with
            | none => extra
            | some i => D.component i) P (X : ℝ) (H : ℝ) := by
  classical
  let S := insert none (D.indices.image (some : D.Index → Option D.Index))
  let component : Option D.Index → ComplexPositiveIntegerFunction := fun j =>
    match j with
    | none => extra
    | some i => D.component i
  have hnone : none ∉ D.indices.image (some : D.Index → Option D.Index) := by simp
  have hinj : Set.InjOn (some : D.Index → Option D.Index)
      (D.indices : Set D.Index) := by
    intro i hi j hj hij
    exact Option.some.inj hij
  have hsum (n : ℤ) :
      (∑ j ∈ S,
        complexPositiveIntegerZeroExtension (component j) n) =
        (∑ i ∈ D.indices,
          complexPositiveIntegerZeroExtension (D.component i) n) +
          complexPositiveIntegerZeroExtension extra n := by
    dsimp [S]
    rw [Finset.sum_insert hnone, Finset.sum_image hinj]
    simp [component]
    ring
  have hCgeone : 1 ≤ decompositionC := by
    unfold decompositionC
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
    have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
    calc
      1 = 1 * 1 := by ring
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul h2 h81 (by norm_num) (by positivity)
  have hcountbase : (D.indices.card : ℝ) ≤
      decompositionC * (Real.log (X : ℝ)) ^ (decompositionB : ℝ) := by
    simpa [decompositionDType] using D.count
  have hcount : (S.card : ℝ) ≤
      decompositionC * (Real.log (X : ℝ)) ^ (decompositionB : ℝ) + 1 := by
    have hcardImage :
        (D.indices.image (some : D.Index → Option D.Index)).card =
          D.indices.card := by
      exact Finset.card_image_iff.mpr hinj
    have hcardS : S.card = D.indices.card + 1 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem hnone, hcardImage]
    rw [hcardS]
    push_cast
    linarith
  have hDecomposition' : ∀ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      w n = (∑ j ∈ S,
        complexPositiveIntegerZeroExtension (component j) n) + r n := by
    intro n hn
    calc
      w n =
          ((∑ i ∈ D.indices,
            complexPositiveIntegerZeroExtension (D.component i) n) +
            complexPositiveIntegerZeroExtension extra n) + r n :=
        hDecomposition n hn
      _ = (∑ j ∈ S,
          complexPositiveIntegerZeroExtension (component j) n) + r n := by
        rw [← hsum n]
  obtain ⟨j, hj, hselected⟩ := exists_component_gt_deltaH_of_source_budget
    X H A decompositionC decompositionB Dexp (Option D.Index) S w r
    (fun j n => complexPositiveIntegerZeroExtension (component j) n)
    P δ hH (by linarith [hCgeone]) hCgeone hL hDelta hThreshold hcount
    hDecomposition' hResidual hLarge
  have hselectedType : conditionalIntegerComponentType (X : ℝ) δ
      (component j) := by
    rcases j with i | i
    · exact Or.inl hExtraType
    · have hiImage : some i ∈ D.indices.image (some : D.Index → Option D.Index) := by
        simpa [S] using hj
      have hi : i ∈ D.indices := by
        rcases Finset.mem_image.mp hiImage with ⟨i', hi', heq⟩
        have heq' : i' = i := Option.some.inj heq
        simpa [heq'] using hi'
      exact elementaryTypeComponent_mono (X : ℝ) δ (D.component i)
        (by exact_mod_cast hX) (by rw [hDelta]; positivity) hDeltaType
        (D.componentType i hi)
  have hcorrelation : δ * (H : ℝ) <
      typeIScalarPhaseCorrelation (component j) P (X : ℝ) (H : ℝ) := by
    rw [typeIScalarPhaseCorrelation, typeIScalarPhaseSum_eq_integerInterval
      X H hX P (component j)]
    exact hselected
  exact ⟨j, by simpa [S] using hj, hselectedType, hcorrelation⟩

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.typeIScalarPhaseSum_eq_integerInterval
#print axioms FractionalPrimes.Literature.Polynomial.elementaryTypeComponent_mono
#print axioms FractionalPrimes.Literature.Polynomial.exists_conditionalIntegerSelectedComponent
