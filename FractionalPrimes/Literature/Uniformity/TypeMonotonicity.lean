module

public import FractionalPrimes.Literature.Uniformity.CoefficientRecurrenceToLogPhase

/-!
# Monotonicity of arithmetic types and short divisor sums

Blueprint `lu:type-monotonicity`. The predicates and their moment and
residue-variation bounds are those of the approved arithmetic-type data.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

noncomputable section

theorem complexPositiveSupportedOnInterval_mono
    {f : ComplexPositiveIntegerFunction} {A B A' B' : ℝ}
    (hf : complexPositiveSupportedOnInterval f A B)
    (hA : A' ≤ A) (hB : B ≤ B') :
    complexPositiveSupportedOnInterval f A' B' := by
  intro n hn
  exact ⟨hA.trans (hf n hn).1, (hf n hn).2.trans hB⟩

theorem complexPositiveSecondMomentBound_mono
    {δ δ' : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    {f : ComplexPositiveIntegerFunction}
    (hf : complexPositiveSecondMomentBound δ f) :
    complexPositiveSecondMomentBound δ' f := by
  intro B hB
  have hinv : δ⁻¹ ≤ δ'⁻¹ := inv_anti₀ hδ' hδ
  exact (hf B hB).trans
    (mul_le_mul_of_nonneg_right hinv (by linarith))

theorem complexPositiveFourthMomentBound_mono
    {δ δ' : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    {f : ComplexPositiveIntegerFunction}
    (hf : complexPositiveFourthMomentBound δ f) :
    complexPositiveFourthMomentBound δ' f := by
  intro B hB
  have hinv : δ⁻¹ ≤ δ'⁻¹ := inv_anti₀ hδ' hδ
  have hpow : δ⁻¹ ^ 2 ≤ δ'⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (hδ'.le.trans hδ)) hinv 2
  exact (hf B hB).trans
    (mul_le_mul_of_nonneg_right hpow (by linarith))

/-- Decreasing the type parameter and enlarging its upper support keeps
the same Type-I witnesses. -/
theorem typeIFunction_mono
    {δ δ' A A' : ℝ} {f : ComplexPositiveIntegerFunction}
    (hf : typeIFunction δ A f) (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (hA : A ≤ A') : typeIFunction δ' A' f := by
  obtain ⟨hδ0, hδ1, hA1, α, β, q, hq, hconv, hsupp, hmom,
    hq1, hqδ, hTV⟩ := hf
  have hinv : δ⁻¹ ≤ δ'⁻¹ := inv_anti₀ hδ' hδ
  exact ⟨hδ', hδ.trans_lt hδ1, hA1.trans hA,
    α, β, q, hq, hconv,
    complexPositiveSupportedOnInterval_mono hsupp le_rfl hA,
    complexPositiveSecondMomentBound_mono hδ' hδ hmom,
    hq1, hqδ.trans hinv,
    hTV.trans (ENNReal.ofReal_le_ofReal hinv)⟩

/-- Type-I₂ monotonicity keeps the common modulus and both variation
witnesses unchanged. -/
theorem typeI2Function_mono
    {δ δ' A A' : ℝ} {f : ComplexPositiveIntegerFunction}
    (hf : typeI2Function δ A f) (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (hA : A ≤ A') : typeI2Function δ' A' f := by
  obtain ⟨hδ0, hδ1, hA1, α, β₁, β₂, q, hq, hconv, hsupp, hmom,
    hq1, hqδ, hTV₁, hTV₂⟩ := hf
  have hinv : δ⁻¹ ≤ δ'⁻¹ := inv_anti₀ hδ' hδ
  exact ⟨hδ', hδ.trans_lt hδ1, hA1.trans hA,
    α, β₁, β₂, q, hq, hconv,
    complexPositiveSupportedOnInterval_mono hsupp le_rfl hA,
    complexPositiveSecondMomentBound_mono hδ' hδ hmom,
    hq1, hqδ.trans hinv,
    hTV₁.trans (ENNReal.ofReal_le_ofReal hinv),
    hTV₂.trans (ENNReal.ofReal_le_ofReal hinv)⟩

/-- Type-II monotonicity allows both support endpoints to be enlarged
outward, retaining the lower-endpoint-at-least-one convention. -/
theorem typeIIFunction_mono
    {δ δ' Aminus Aplus Aminus' Aplus' : ℝ}
    {f : ComplexPositiveIntegerFunction}
    (hf : typeIIFunction δ Aminus Aplus f)
    (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (hAminus1 : 1 ≤ Aminus') (hAminus : Aminus' ≤ Aminus)
    (hAplus : Aplus ≤ Aplus') :
    typeIIFunction δ' Aminus' Aplus' f := by
  obtain ⟨hδ0, hδ1, hAminusOld, hAplusOld, α, β,
    hconv, hsupp, hempty, hα, hβ, hβ4⟩ := hf
  refine ⟨hδ', hδ.trans_lt hδ1, hAminus1, hAplusOld.trans hAplus,
    α, β, hconv,
    complexPositiveSupportedOnInterval_mono hsupp hAminus hAplus,
    ?_, complexPositiveSecondMomentBound_mono hδ' hδ hα,
    complexPositiveSecondMomentBound_mono hδ' hδ hβ,
    complexPositiveFourthMomentBound_mono hδ' hδ hβ4⟩
  intro hempty'
  exact hempty (lt_of_le_of_lt hAplus (lt_of_lt_of_le hempty' hAminus))

/-- A constant function has no adjacent increments, and its finite
inhomogeneous variation is bounded by its constant norm. -/
theorem finiteOrderedTotalVariation_const_le (F : Finset ℤ) (c : ℂ) :
    finiteOrderedTotalVariation F (fun _ => c) ≤ ‖c‖ := by
  have hfold : ∀ (ns : List ℤ) (b : ℝ), b ≤ ‖c‖ →
      ((ns.map fun _ => ‖c‖).foldl max b) ≤ ‖c‖ := by
    intro ns
    induction ns with
    | nil => intro b hb; simpa using hb
    | cons n ns ih =>
      intro b hb
      simpa only [List.map_cons, List.foldl_cons] using
        ih (max b ‖c‖) (max_le hb le_rfl)
  unfold finiteOrderedTotalVariation listSupNorm listAdjacentVariation
  simp only [sub_self, norm_zero, List.map_const', List.sum_replicate,
    nsmul_zero, add_zero]
  simpa only [List.map_const'] using
    hfold (F.sort (· ≤ ·)) 0 (norm_nonneg _)

/-- The same constant bound holds on an arbitrary ordered set, including
the unbounded positive integers used by the arithmetic types. -/
theorem orderedTotalVariation_const_le (S : Set ℤ) (c : ℂ) :
    orderedTotalVariation S (fun _ => c) ≤ ENNReal.ofReal ‖c‖ := by
  apply iSup_le
  intro F
  exact ENNReal.ofReal_le_ofReal (finiteOrderedTotalVariation_const_le F.1 c)

/-- The constant-one positive-integer factor has variation at most one
with modulus one. Its zero extension outside the positive integers does
not affect this restricted variation. -/
theorem complexPositiveIntegerResidueVariation_one :
    complexPositiveIntegerResidueVariation (fun _ => 1) 1 (by decide) ≤ 1 := by
  unfold complexPositiveIntegerResidueVariation positiveIntegerResidueTotalVariation
    residueClassTotalVariation
  simp only [Finset.range_one, Finset.sum_singleton]
  have heq : orderedTotalVariation
      ({n : ℤ | 0 < n} ∩ integerResidueClass 1 0)
      (complexPositiveIntegerZeroExtension (fun _ : PositiveInteger => (1 : ℂ))) =
    orderedTotalVariation ({n : ℤ | 0 < n} ∩ integerResidueClass 1 0)
      (fun _ => (1 : ℂ)) := by
    apply orderedTotalVariation_congr_on_logPhase
    intro n hn
    have hnpos : 0 < n := hn.1
    simp [complexPositiveIntegerZeroExtension, hnpos]
  rw [heq]
  simpa using orderedTotalVariation_const_le
    ({n : ℤ | 0 < n} ∩ integerResidueClass 1 0) (1 : ℂ)

/-- Coefficients of the short divisor sum, cut off at the real endpoint
`D`, as in the blueprint. -/
def shortDivisorTypeCoefficient (D : ℝ) (b : ComplexPositiveIntegerFunction) :
    ComplexPositiveIntegerFunction := fun n =>
  if (n.1 : ℝ) ≤ D then b n else 0

/-- The exact sum over positive divisors `a` of `n` with `a≤D`. -/
def arithmeticShortDivisorSum (D : ℝ) (b : ComplexPositiveIntegerFunction)
    (n : PositiveInteger) : ℂ :=
  ∑ a ∈ n.1.divisors, if ha : 0 < a then
    if (a : ℝ) ≤ D then b ⟨a, ha⟩ else 0 else 0

theorem arithmeticShortDivisorSum_eq_convolution
    (D : ℝ) (b : ComplexPositiveIntegerFunction) :
    arithmeticShortDivisorSum D b =
      complexPositiveDirichletConvolution (shortDivisorTypeCoefficient D b)
        (fun _ => 1) := by
  funext n
  rw [complexPositiveDirichletConvolution_eq_divisor_sum]
  unfold arithmeticShortDivisorSum
  apply Finset.sum_congr rfl
  intro a ha
  simp [complexDivisorConvolutionSummand, ha, Nat.pos_of_mem_divisors ha,
    shortDivisorTypeCoefficient]

theorem shortDivisorTypeCoefficient_supported
    (D : ℝ) (b : ComplexPositiveIntegerFunction) :
    complexPositiveSupportedOnInterval (shortDivisorTypeCoefficient D b) 1 D := by
  intro n hn
  have hcut : (n.1 : ℝ) ≤ D := by
    by_contra hcut
    exact hn (by simp [shortDivisorTypeCoefficient, hcut])
  exact ⟨by exact_mod_cast n.2, hcut⟩

theorem shortDivisorTypeCoefficient_norm_le
    (D W : ℝ) (hW : 0 ≤ W) (b : ComplexPositiveIntegerFunction)
    (hb : ∀ n, ‖b n‖ ≤ W) (n : PositiveInteger) :
    ‖shortDivisorTypeCoefficient D b n‖ ≤ W := by
  by_cases hcut : (n.1 : ℝ) ≤ D
  · simpa [shortDivisorTypeCoefficient, hcut] using hb n
  · simpa [shortDivisorTypeCoefficient, hcut] using hW

/-- The finite second-moment bound uses exactly `floor B` positive
indices and therefore loses no extra constant. -/
theorem shortDivisorTypeCoefficient_secondMoment_le
    (D W : ℝ) (hW : 0 ≤ W) (b : ComplexPositiveIntegerFunction)
    (hb : ∀ n, ‖b n‖ ≤ W) (B : ℝ) (hB : 1 ≤ B) :
    complexPositiveSecondMoment (shortDivisorTypeCoefficient D b) B ≤
      W ^ 2 * B := by
  have hterm : ∀ n ∈ Finset.Icc 1 (Nat.floor B),
      complexPositiveSecondMomentSummand (shortDivisorTypeCoefficient D b) n ≤
        W ^ 2 := by
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    simpa only [complexPositiveSecondMomentSummand, dite_eq_left hnpos] using
      pow_le_pow_left₀ (norm_nonneg _)
        (shortDivisorTypeCoefficient_norm_le D W hW b hb ⟨n, hnpos⟩) 2
  calc
    complexPositiveSecondMoment (shortDivisorTypeCoefficient D b) B ≤
        ∑ _n ∈ Finset.Icc 1 (Nat.floor B), W ^ 2 :=
      Finset.sum_le_sum hterm
    _ = (Nat.floor B : ℝ) * W ^ 2 := by simp [Nat.card_Icc]
    _ ≤ B * W ^ 2 :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (sq_nonneg W)
    _ = W ^ 2 * B := mul_comm _ _

/-- Admissibility of a short divisor sum with precisely the source budget
`δ⁻¹≥W²`; the cutoff and coefficient bounds are uniform in `n`. -/
theorem arithmeticShortDivisorSum_typeI
    (δ D W : ℝ) (b : ComplexPositiveIntegerFunction)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hD : 1 ≤ D) (hW : 1 ≤ W)
    (hbudget : W ^ 2 ≤ δ⁻¹) (hb : ∀ n, ‖b n‖ ≤ W) :
    typeIFunction δ D (arithmeticShortDivisorSum D b) := by
  have hδinv : 1 ≤ δ⁻¹ := by simpa using inv_anti₀ hδ hδ1.le
  refine ⟨hδ, hδ1, hD, shortDivisorTypeCoefficient D b,
    (fun _ => 1), 1, by decide,
    arithmeticShortDivisorSum_eq_convolution D b,
    shortDivisorTypeCoefficient_supported D b, ?_, by decide,
    by simpa using hδinv, ?_⟩
  · intro B hB
    exact (shortDivisorTypeCoefficient_secondMoment_le D W
      (by linarith) b hb B hB).trans
        (mul_le_mul_of_nonneg_right hbudget (by linarith))
  · exact complexPositiveIntegerResidueVariation_one.trans
      (by simpa using ENNReal.ofReal_le_ofReal hδinv)

/-- Negating the coefficient family gives exactly the negative divisor
sum. -/
theorem arithmeticShortDivisorSum_neg
    (D : ℝ) (b : ComplexPositiveIntegerFunction) :
    arithmeticShortDivisorSum D (fun n => -b n) =
      -arithmeticShortDivisorSum D b := by
  funext n
  simp only [arithmeticShortDivisorSum, Pi.neg_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hapos := Nat.pos_of_mem_divisors ha
  simp only [dite_eq_left hapos]
  split_ifs <;> simp

/-- Both signs of the short divisor sum are Type I under the identical
source hypotheses. -/
theorem arithmeticShortDivisorSum_typeI_both_signs
    (δ D W : ℝ) (b : ComplexPositiveIntegerFunction)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hD : 1 ≤ D) (hW : 1 ≤ W)
    (hbudget : W ^ 2 ≤ δ⁻¹) (hb : ∀ n, ‖b n‖ ≤ W) :
    typeIFunction δ D (arithmeticShortDivisorSum D b) ∧
      typeIFunction δ D (-arithmeticShortDivisorSum D b) := by
  refine ⟨arithmeticShortDivisorSum_typeI δ D W b hδ hδ1 hD hW hbudget hb, ?_⟩
  rw [← arithmeticShortDivisorSum_neg]
  exact arithmeticShortDivisorSum_typeI δ D W (fun n => -b n)
    hδ hδ1 hD hW hbudget (by intro n; simpa using hb n)

/-- The complete manifest-facing `lu:type-monotonicity` package:
parameter/support monotonicity of all three types, and Type-I
admissibility of both signs of the exact short divisor sum. -/
theorem typeMonotonicity :
    (∀ (δ δ' A A' : ℝ) (f : ComplexPositiveIntegerFunction),
      typeIFunction δ A f → 0 < δ' → δ' ≤ δ → A ≤ A' →
        typeIFunction δ' A' f) ∧
    (∀ (δ δ' A A' : ℝ) (f : ComplexPositiveIntegerFunction),
      typeI2Function δ A f → 0 < δ' → δ' ≤ δ → A ≤ A' →
        typeI2Function δ' A' f) ∧
    (∀ (δ δ' Aminus Aplus Aminus' Aplus' : ℝ)
        (f : ComplexPositiveIntegerFunction),
      typeIIFunction δ Aminus Aplus f → 0 < δ' → δ' ≤ δ →
        1 ≤ Aminus' → Aminus' ≤ Aminus → Aplus ≤ Aplus' →
          typeIIFunction δ' Aminus' Aplus' f) ∧
    (∀ (δ D W : ℝ) (b : ComplexPositiveIntegerFunction),
      0 < δ → δ < 1 → 1 ≤ D → 1 ≤ W → W ^ 2 ≤ δ⁻¹ →
        (∀ n, ‖b n‖ ≤ W) →
          typeIFunction δ D (arithmeticShortDivisorSum D b) ∧
            typeIFunction δ D (-arithmeticShortDivisorSum D b)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro δ δ' A A' f hf hδ' hδ hA
    exact typeIFunction_mono hf hδ' hδ hA
  · intro δ δ' A A' f hf hδ' hδ hA
    exact typeI2Function_mono hf hδ' hδ hA
  · intro δ δ' Aminus Aplus Aminus' Aplus' f hf hδ' hδ hAminus1 hAminus hAplus
    exact typeIIFunction_mono hf hδ' hδ hAminus1 hAminus hAplus
  · exact arithmeticShortDivisorSum_typeI_both_signs

end

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.typeIFunction_mono
#print axioms FractionalPrimes.Literature.Uniformity.typeI2Function_mono
#print axioms FractionalPrimes.Literature.Uniformity.typeIIFunction_mono
#print axioms FractionalPrimes.Literature.Uniformity.complexPositiveIntegerResidueVariation_one
#print axioms FractionalPrimes.Literature.Uniformity.arithmeticShortDivisorSum_typeI_both_signs
#print axioms FractionalPrimes.Literature.Uniformity.typeMonotonicity
