module

public import FractionalPrimes.Literature.Polynomial.TypeIICharacterAllocationPTWAssembly
public import FractionalPrimes.Literature.Twisted.NonunitTripleFiniteMellin
public import FractionalPrimes.Literature.Twisted.CharacterEvalNorm

/-! Source-specific assembly of the three selected dyadic factors over the
exact nonunit gcd allocations and residual characters. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.LargeValues
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- The exact source normalization of one allocated dyadic factor. -/
def selectedPTWFactorScale (X : ℝ) (r : ℕ) : ℝ :=
  (2 : ℝ) ^ 10 * Real.log (8 * X) *
    (divisorCoefficient 2 r : ℝ) ^ 20

/-- The residual character coefficient for one source gcd allocation. -/
def selectedPTWAllocationCharacterWeight
    {d Q : ℕ} (q : ℕ) (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (i : Fin 3) (n : ℕ) : ℂ :=
  if Nat.Coprime n (q / orderedAllocationPrefix r.1 i) then
    evalInt χ (n : ℤ) else 0

/-- The actual source-scaled product of the three normalized selected-group
Dirichlet polynomials for one allocation and one residual character. -/
def selectedDyadicPTWAllocationTerm
    {d Q : ℕ} (q : ℕ) (X z Y : ℝ) (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    (alpha beta gamma T : ℝ)
    (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q) (t : ℝ) : ℂ :=
  let r₁ := (r.1 0).1
  let r₂ := (r.1 1).1
  let r₃ := (r.1 2).1
  let B₁ := selectedPTWFactorScale X r₁
  let B₂ := selectedPTWFactorScale X r₂
  let B₃ := selectedPTWFactorScale X r₃
  let g₁ : ℕ → ℂ := fun n =>
    toComplexArithmeticFunction (groupedDyadicFactor z c fs₁) n
  let g₂ : ℕ → ℂ := fun n =>
    toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₂) n
  let g₃ : ℕ → ℂ := fun n =>
    toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₃) n
  let χ₁ : ℕ → ℂ := selectedPTWAllocationCharacterWeight q r χ 0
  let χ₂ : ℕ → ℂ := selectedPTWAllocationCharacterWeight q r χ 1
  let χ₃ : ℕ → ℂ := selectedPTWAllocationCharacterWeight q r χ 2
  ((B₁ * B₂ * B₃ : ℝ) : ℂ) *
    (factorPolynomial (Y ^ alpha)
        (selectedGroupTrilinearCoeff B₁ r₁ g₁ χ₁ T) t *
      factorPolynomial (Y ^ beta)
        (selectedGroupTrilinearCoeff B₂ r₂ g₂ χ₂ T) t *
      factorPolynomial (Y ^ gamma)
        (selectedGroupTrilinearCoeff B₃ r₃ g₃ χ₃ T) t)

/-- The allocation-specific numerical hypotheses checked before applying
`ldm:uncapped` to one dyadic block. -/
structure SelectedPTWAllocationGeometry
    (eps Y U : ℝ) where
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  M : ℝ
  hM : 0 < M
  hMpow : M = Y ^ alpha
  heps0 : 0 < eps
  heps : eps ≤ 3 / 16
  hU0 : 2 ≤ U
  hU : U ≤ Y ^ (3 / 8 - eps)
  ha0 : 0 ≤ alpha
  hb0 : 0 ≤ beta
  hc0 : 0 ≤ gamma
  hsum : alpha + beta + gamma = 1
  haLow : 1 / 4 - eps / 100 ≤ alpha
  haHigh : alpha ≤ 1 / 2 + eps / 100
  hbc : |beta - gamma| ≤ 1 / 4 + eps / 100

private theorem selectedPTW_divisorCoefficient_two_eq_divisors_card
    (n : ℕ) : divisorCoefficient 2 n = n.divisors.card := by
  change (ArithmeticFunction.zeta ^ 2) n = n.divisors.card
  rw [show (2 : ℕ) = 1 + 1 by omega, pow_succ, pow_one,
    ArithmeticFunction.mul_zeta_apply]
  calc
    (∑ d ∈ n.divisors, ArithmeticFunction.zeta d) =
        ∑ d ∈ n.divisors, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact ArithmeticFunction.zeta_apply_ne
        (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
    _ = n.divisors.card := by simp

private theorem selectedPTW_divisorCoefficient_two_mono_of_dvd
    {u n : ℕ} (hun : u ∣ n) (hn : n ≠ 0) :
    divisorCoefficient 2 u ≤ divisorCoefficient 2 n := by
  rw [selectedPTW_divisorCoefficient_two_eq_divisors_card,
    selectedPTW_divisorCoefficient_two_eq_divisors_card]
  apply Finset.card_le_card
  intro d hd
  rcases Nat.mem_divisors.mp hd with ⟨hdu, _⟩
  exact Nat.mem_divisors.mpr ⟨dvd_trans hdu hun, hn⟩

private theorem selectedPTW_divisorCoefficient_two_ge_one
    {n : ℕ} (hn : 0 < n) : 1 ≤ divisorCoefficient 2 n := by
  rw [selectedPTW_divisorCoefficient_two_eq_divisors_card]
  have hmem : 1 ∈ n.divisors := by
    exact Nat.mem_divisors.mpr ⟨one_dvd n, (Nat.ne_of_gt hn)⟩
  exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨1, hmem⟩)

private theorem selectedPTWFactorScale_ge_one
    {X : ℝ} (hX : 3 ≤ X) {r : ℕ} (hr : 0 < r) :
    1 ≤ selectedPTWFactorScale X r := by
  have hlog := log_eightX_gt_one hX
  have hdivNat := selectedPTW_divisorCoefficient_two_ge_one hr
  have hdiv : 1 ≤ (divisorCoefficient 2 r : ℝ) := by exact_mod_cast hdivNat
  have hdivPow : 1 ≤ (divisorCoefficient 2 r : ℝ) ^ 20 := one_le_pow₀ hdiv
  have hbase : 1 ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) := by
    calc
      1 ≤ (2 : ℝ) ^ 10 := by norm_num
      _ = (2 : ℝ) ^ 10 * 1 := by ring
      _ ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) :=
        mul_le_mul_of_nonneg_left hlog.le (by positivity)
  have hbase_nonneg : 0 ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) :=
    mul_nonneg (by positivity) (le_trans (by norm_num) hlog.le)
  unfold selectedPTWFactorScale
  calc
    1 ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) := hbase
    _ = ((2 : ℝ) ^ 10 * Real.log (8 * X)) * 1 := by ring
    _ ≤ ((2 : ℝ) ^ 10 * Real.log (8 * X)) *
        (divisorCoefficient 2 r : ℝ) ^ 20 :=
      mul_le_mul_of_nonneg_left hdivPow hbase_nonneg

private theorem selectedPTWAllocation_coordinate_dvd
    {d : ℕ} (r : divisorFactorTuples 3 d) (i : Fin 3) :
    (r.1 i).1 ∣ d := by
  calc
    (r.1 i).1 ∣ ∏ j : Fin 3, (r.1 j).1 :=
      Finset.dvd_prod_of_mem (fun j : Fin 3 => (r.1 j).1)
        (Finset.mem_univ i)
    _ = d := r.2

private theorem selectedPTWFactorScale_mono_of_dvd
    {X : ℝ} (hX : 3 ≤ X) {u n : ℕ}
    (hun : u ∣ n) (hn : n ≠ 0) :
    selectedPTWFactorScale X u ≤ selectedPTWFactorScale X n := by
  have hdivNat := selectedPTW_divisorCoefficient_two_mono_of_dvd hun hn
  have hdiv : (divisorCoefficient 2 u : ℝ) ≤
      (divisorCoefficient 2 n : ℝ) := by exact_mod_cast hdivNat
  have hdivNonneg : 0 ≤ (divisorCoefficient 2 u : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ hdivNonneg hdiv 20
  have hlog := log_eightX_gt_one hX
  unfold selectedPTWFactorScale
  exact mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (by positivity) (le_trans (by norm_num) hlog.le))

private theorem selectedPTWAllocationCharacterWeight_norm_le_one
    {Q d q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (i : Fin 3) (n : ℕ) :
    ‖selectedPTWAllocationCharacterWeight q r χ i n‖ ≤ 1 := by
  unfold selectedPTWAllocationCharacterWeight
  split_ifs
  · exact evalInt_norm_le_one χ _
  · simp

/-- The exact normalized uncapped kernel for the three selected factor
polynomials, retaining the source `J₍₂₀₎`, `Z₍₂₀₎`, logarithmic, and
short-factor saving constants. -/
def selectedDyadicPTWUncappedKernel
    (X Y a eps : ℝ) : ℝ :=
  J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
    Real.sqrt Y *
      (((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
        Y ^ (-eps / 16 : ℝ))

set_option maxHeartbeats 2000000 in
/-- Source-specific PTW character/allocation assembly for the actual product
of the three normalized selected-group factor polynomials. For each gcd
allocation the source scales are exactly
`Bᵢ = 2^10 log(8X) d₂(rᵢ)^20`; the allocation count is exactly `d₃(d)`,
and the character-average normalization contributes exactly `d^(-1/2)`.
The selected first-factor block estimate remains the explicit source input.
-/
theorem selectedDyadicPTWCharacterAllocationIntegral_bound
    {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (a' : ℤ) (ha' : IsCoprime a' (Q : ℤ))
    (X z Y U a eps Tfreq : ℝ) (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    (hXsrc : 3 ≤ X) (hY : (2 : ℝ) ^ 16 ≤ Y)
    (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : fs₁.length ≤ 20) (hlen₂ : fs₂.length ≤ 20)
    (hlen₃ : fs₃.length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight fs₁ ≤ Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight fs₂ ≤ Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight fs₃ ≤ Real.log (8 * X))
    (hδ0 : 0 < (Real.log X) ^ (-20 * a))
    (hδ : (Real.log X) ^ (-20 * a) ≤ 1)
    (geometry : ∀ _r : divisorFactorTuples 3 d,
      SelectedPTWAllocationGeometry eps Y U)
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hblock : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (s : ℝ),
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖∑ n ∈ factorExtractionRealInterval
          (geometry r).M (2 * (geometry r).M),
        toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
            ((r.1 0).1 * n) *
          factorExtractionMellinWeight
            (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt (geometry r).M) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ a') *
              selectedDyadicPTWAllocationTerm q X z Y c
                fs₁ fs₂ fs₃ (geometry r).alpha (geometry r).beta
                (geometry r).gamma Tfreq r χ t‖ ∂volume) ≤
      (d : ℝ) ^ (-(1 / 2 : ℝ)) *
        (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
          ((selectedPTWFactorScale X d *
              selectedPTWFactorScale X d * selectedPTWFactorScale X d) *
            selectedDyadicPTWUncappedKernel X Y a eps) := by
  classical
  let F : divisorFactorTuples 3 d → BlueprintCharacter Q → ℝ → ℂ :=
    fun r χ t => selectedDyadicPTWAllocationTerm q X z Y c
      fs₁ fs₂ fs₃ (geometry r).alpha (geometry r).beta
        (geometry r).gamma Tfreq r χ t
  let A : divisorFactorTuples 3 d → ℝ := fun r =>
    selectedPTWFactorScale X (r.1 0).1 *
      selectedPTWFactorScale X (r.1 1).1 *
        selectedPTWFactorScale X (r.1 2).1
  let Amax : ℝ := selectedPTWFactorScale X d *
    selectedPTWFactorScale X d * selectedPTWFactorScale X d
  let Kbase : ℝ := selectedDyadicPTWUncappedKernel X Y a eps
  have hXone : 1 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hXone
  have hYpos : 0 < Y := by
    have hpow : 0 < (2 : ℝ) ^ 16 := by positivity
    linarith
  have hlog4Y : 0 < Real.log (4 * Y) := by
    apply Real.log_pos
    nlinarith
  have hKbase : 0 ≤ Kbase := by
    dsimp [Kbase, selectedDyadicPTWUncappedKernel]
    have hδpos : 0 < (Real.log X) ^ (-20 * a) := hδ0
    have hδpow : 0 ≤
        ((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) :=
      Real.rpow_nonneg hδpos.le _
    have hYpow : 0 ≤ Y ^ (-eps / 16 : ℝ) :=
      Real.rpow_nonneg hYpos.le _
    have hZ : 0 ≤ Z 20 Y := by
      unfold Z
      positivity
    have hJ : 0 ≤ J 20 := by
      unfold J K
      positivity
    have hlogpow : 0 ≤ (Real.log (4 * Y)) ^ (b 20 + 3) :=
      pow_nonneg hlog4Y.le _
    have hsqrt : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg _
    have hsum : 0 ≤
        ((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
          Y ^ (-eps / 16 : ℝ) := add_nonneg hδpow hYpow
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hJ (pow_nonneg hZ 3)) hlogpow) hsqrt) hsum
  have hAmax : ∀ r : divisorFactorTuples 3 d, A r ≤ Amax := by
    intro r
    have hdne : d ≠ 0 := Nat.ne_of_gt hd
    have h1 := selectedPTWFactorScale_mono_of_dvd hXsrc
      (selectedPTWAllocation_coordinate_dvd r 0) hdne
    have h2 := selectedPTWFactorScale_mono_of_dvd hXsrc
      (selectedPTWAllocation_coordinate_dvd r 1) hdne
    have h3 := selectedPTWFactorScale_mono_of_dvd hXsrc
      (selectedPTWAllocation_coordinate_dvd r 2) hdne
    have hr1 : 0 < (r.1 0).1 := (r.1 0).2
    have hr2 : 0 < (r.1 1).1 := (r.1 1).2
    have hr3 : 0 < (r.1 2).1 := (r.1 2).2
    have hdscale : 0 ≤ selectedPTWFactorScale X d :=
      le_trans (by norm_num) (selectedPTWFactorScale_ge_one hXsrc hd)
    have hscale1 : 0 ≤ selectedPTWFactorScale X (r.1 2).1 :=
      le_trans (by norm_num)
        (selectedPTWFactorScale_ge_one hXsrc hr3)
    have hscale12 :
        selectedPTWFactorScale X (r.1 0).1 *
            selectedPTWFactorScale X (r.1 1).1 ≤
          selectedPTWFactorScale X d * selectedPTWFactorScale X d :=
      mul_le_mul h1 h2
        (le_trans (by norm_num)
          (selectedPTWFactorScale_ge_one hXsrc (r.1 1).2)) hdscale
    dsimp [A, Amax]
    calc
      _ ≤ (selectedPTWFactorScale X d * selectedPTWFactorScale X d) *
          selectedPTWFactorScale X (r.1 2).1 :=
        mul_le_mul_of_nonneg_right hscale12 hscale1
      _ ≤ (selectedPTWFactorScale X d * selectedPTWFactorScale X d) *
          selectedPTWFactorScale X d :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
  have hFcont : ∀ r χ, Continuous (F r χ) := by
    intro r χ
    dsimp [F, selectedDyadicPTWAllocationTerm]
    exact continuous_const.mul
      (((factorPolynomial_continuous _ _).mul
        (factorPolynomial_continuous _ _)).mul
          (factorPolynomial_continuous _ _))
  have hterm : ∀ r χ,
      (∫ t in Set.Icc (-U) U, ‖F r χ t‖ ∂volume) ≤ A r * Kbase := by
    intro r χ
    let G := geometry r
    let r₁ := (r.1 0).1
    let r₂ := (r.1 1).1
    let r₃ := (r.1 2).1
    let B₁ := selectedPTWFactorScale X r₁
    let B₂ := selectedPTWFactorScale X r₂
    let B₃ := selectedPTWFactorScale X r₃
    let χ₁ := selectedPTWAllocationCharacterWeight q r χ 0
    let χ₂ := selectedPTWAllocationCharacterWeight q r χ 1
    let χ₃ := selectedPTWAllocationCharacterWeight q r χ 2
    have hr₁ : 1 ≤ r₁ := Nat.succ_le_iff.mpr (r.1 0).2
    have hr₂ : 1 ≤ r₂ := Nat.succ_le_iff.mpr (r.1 1).2
    have hr₃ : 1 ≤ r₃ := Nat.succ_le_iff.mpr (r.1 2).2
    have hB₁ : 1 ≤ B₁ := by
      exact selectedPTWFactorScale_ge_one hXsrc (r.1 0).2
    have hB₂ : 0 < B₂ := by
      exact lt_of_lt_of_le (by norm_num)
        (selectedPTWFactorScale_ge_one hXsrc (r.1 1).2)
    have hB₃ : 0 < B₃ := by
      exact lt_of_lt_of_le (by norm_num)
        (selectedPTWFactorScale_ge_one hXsrc (r.1 2).2)
    have hB₁pos : 0 < B₁ := lt_of_lt_of_le (by norm_num) hB₁
    have hBscale₁ :
        (2 : ℝ) ^ 10 * Real.log (8 * X) *
          (divisorCoefficient 2 r₁ : ℝ) ^ 20 ≤ B₁ := by
      rfl
    have hBscale₂ :
        (2 : ℝ) ^ 10 * Real.log (8 * X) *
          (divisorCoefficient 2 r₂ : ℝ) ^ 20 ≤ B₂ := by
      rfl
    have hBscale₃ :
        (2 : ℝ) ^ 10 * Real.log (8 * X) *
          (divisorCoefficient 2 r₃ : ℝ) ^ 20 ≤ B₃ := by
      rfl
    have hχ₁ : ∀ n, ‖χ₁ n‖ ≤ 1 :=
      selectedPTWAllocationCharacterWeight_norm_le_one
        (Q := Q) (d := d) (q := q) r χ 0
    have hχ₂ : ∀ n, ‖χ₂ n‖ ≤ 1 :=
      selectedPTWAllocationCharacterWeight_norm_le_one
        (Q := Q) (d := d) (q := q) r χ 1
    have hχ₃ : ∀ n, ‖χ₃ n‖ ≤ 1 :=
      selectedPTWAllocationCharacterWeight_norm_le_one
        (Q := Q) (d := d) (q := q) r χ 2
    have hE : MeasurableSet (Set.Icc (-U) U) := measurableSet_Icc
    have hEsub : Set.Icc (-U) U ⊆ Set.Icc (-U) U := by
      intro t ht
      exact ht
    have hfreqlocal : ∀ t ∈ Set.Icc (-U) U,
        (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
          |Tfreq - t| ≤ X ^ (a + 1) := hfreq
    have hK := selectedDyadicGroupAllocationTrilinearIntegral_bound
      Y eps U G.alpha G.beta G.gamma X a G.M B₁ B₂ B₃ Tfreq z
      (Set.Icc (-U) U) c fs₁ fs₂ fs₃ r₁ r₂ r₃ χ₁ χ₂ χ₃
      hXsrc hc hlen₁ hlen₂ hlen₃ hweight₁ hweight₂ hweight₃
      hr₁ hr₂ hr₃ hBscale₁ hBscale₂ hBscale₃
      G.hM G.hMpow hB₁ hB₁pos hB₂ hB₃ hY G.heps0 G.heps
      G.hU0 G.hU G.ha0 G.hb0 G.hc0 G.hsum G.haLow G.haHigh G.hbc
      hδ0 hδ hE hEsub hχ₁ hχ₂ hχ₃ hfreqlocal (hblock r χ)
    change (∫ t in Set.Icc (-U) U,
      ‖((B₁ * B₂ * B₃ : ℝ) : ℂ) *
        (factorPolynomial (Y ^ G.alpha)
            (selectedGroupTrilinearCoeff B₁ r₁
              (fun n => toComplexArithmeticFunction
                (groupedDyadicFactor z c fs₁) n) χ₁ Tfreq) t *
          factorPolynomial (Y ^ G.beta)
            (selectedGroupTrilinearCoeff B₂ r₂
              (fun n => toComplexArithmeticFunction
                (dyadicConvolutionPositiveComplex z fs₂) n) χ₂ Tfreq) t *
          factorPolynomial (Y ^ G.gamma)
            (selectedGroupTrilinearCoeff B₃ r₃
              (fun n => toComplexArithmeticFunction
                (dyadicConvolutionPositiveComplex z fs₃) n) χ₃ Tfreq) t)‖ ∂volume) ≤
      B₁ * B₂ * B₃ *
        selectedDyadicPTWUncappedKernel X Y a eps
    exact hK
  exact nonunitTripleCharacterAverageIntegral_bound_of_allocationK
    hd hQ a' ha' U Tfreq Amax Kbase F hFcont A hAmax hKbase hterm

#print axioms selectedDyadicPTWCharacterAllocationIntegral_bound

end FractionalPrimes.Literature.DirichletMean

end

