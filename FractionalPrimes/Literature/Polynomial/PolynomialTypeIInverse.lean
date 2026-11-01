module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import FractionalPrimes.Literature.Uniformity.TotalVariationCalculusPackage
public import FractionalPrimes.Literature.Polynomial.ProgressionPhaseInverse
public import FractionalPrimes.Literature.Polynomial.PolynomialDilationConcatenation
public import FractionalPrimes.Literature.Polynomial.PolynomialMonomialToBinomial
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scalar Type I inverse estimate

This file formalizes the scalar Type I inverse theorem in blueprint
item `lpi:type-I`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open _root_.Polynomial
open scoped ENNReal

noncomputable section

/-- A finite ordered variation is bounded by the extended variation on the
same underlying set. -/
theorem finiteOrderedTotalVariation_le_orderedTotalVariation
    (S : Finset ℤ) (g : ℤ → ℂ) :
    ENNReal.ofReal (finiteOrderedTotalVariation S g) ≤
      orderedTotalVariation (S : Set ℤ) g := by
  unfold orderedTotalVariation
  let S' : {F : Finset ℤ // ∀ n ∈ F, n ∈ (S : Set ℤ)} :=
    ⟨S, fun _ hn => hn⟩
  exact le_iSup_of_le S' le_rfl

/-- The finite residue variation on a positive integer interval is bounded by
the exact infinite positive-integer residue variation. -/
private theorem finiteResidueClassVariation_le_positiveInteger
    (I : FiniteIntegerInterval) (g : ℤ → ℂ) (q : ℕ) (hq : 0 < q)
    (hI : ∀ n ∈ I.points, 0 < n) :
    ENNReal.ofReal (finiteResidueClassVariation I g q) ≤
      positiveIntegerResidueTotalVariation g q hq := by
  classical
  rw [finiteResidueClassVariation, ENNReal.ofReal_sum_of_nonneg]
  · unfold positiveIntegerResidueTotalVariation residueClassTotalVariation
    apply Finset.sum_le_sum
    intro a ha
    calc
      ENNReal.ofReal
          (finiteOrderedTotalVariation
            (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g) ≤
        orderedTotalVariation
          ((I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)] : Finset ℤ) : Set ℤ) g :=
        finiteOrderedTotalVariation_le_orderedTotalVariation _ _
      _ ≤ orderedTotalVariation
          ({n : ℤ | 0 < n} ∩ integerResidueClass q a) g :=
        orderedTotalVariation_mono_of_subset (by
          intro n hn
          have hn' : n ∈ I.points.filter
              (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) := hn
          rcases Finset.mem_filter.mp hn' with ⟨hnI, hmod⟩
          refine ⟨hI n hnI, ?_⟩
          exact Int.modEq_iff_add_fac.mp hmod.symm) g
  · intro a ha
    exact finiteOrderedTotalVariation_nonneg _ _

/-- A Type I variation hypothesis controls the finite residue variation on
every positive integer interval by the same real constant. -/
private theorem finiteResidueClassVariation_le_of_typeI
    (I : FiniteIntegerInterval) (β : ComplexPositiveIntegerFunction)
    (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ)
    (hI : ∀ n ∈ I.points, 0 < n)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹)) :
    finiteResidueClassVariation I (complexPositiveIntegerZeroExtension β) q ≤
      δ⁻¹ := by
  have hfinite := finiteResidueClassVariation_le_positiveInteger
    I (complexPositiveIntegerZeroExtension β) q hq hI
  have hbound : ENNReal.ofReal
      (finiteResidueClassVariation I (complexPositiveIntegerZeroExtension β) q) ≤
      ENNReal.ofReal (δ⁻¹) := hfinite.trans hTV
  exact (ENNReal.ofReal_le_ofReal_iff (inv_nonneg.mpr hδ.le)).mp hbound

/-- The finite set of positive integers in the exact real interval
`(X,X+H]`. -/
def typeIIntervalSet (X H : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor (X + H))).filter
    (fun n => X < (n : ℝ) ∧ (n : ℝ) ≤ X + H)

@[simp]
theorem mem_typeIIntervalSet (X H : ℝ) (n : ℕ) :
    n ∈ typeIIntervalSet X H ↔
      1 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ X + H := by
  simp only [typeIIntervalSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hnlo, _⟩, hX, hnhi⟩
    exact ⟨hnlo, hX, hnhi⟩
  · rintro ⟨hnlo, hX, hnhi⟩
    exact ⟨⟨hnlo, Nat.le_floor hnhi⟩, ⟨hX, hnhi⟩⟩

/-- The summand `f(n)e(P(n))`, totalized at zero for natural-indexed sums. -/
def complexPositivePhaseTerm (f : ComplexPositiveIntegerFunction)
    (P : Polynomial ℝ) (n : ℕ) : ℂ :=
  if hn : 0 < n then
    f ⟨n, hn⟩ * unitFrequencyPhase (P.eval (n : ℝ))
  else 0

/-- Extend a complex-valued positive-integer function to `ℕ` by zero at zero. -/
def complexPositiveIntegerNatExtension
    (f : ComplexPositiveIntegerFunction) (n : ℕ) : ℂ :=
  if hn : 0 < n then f ⟨n, hn⟩ else 0

/-- The exact complex sum in the scalar Type I correlation. -/
def typeIScalarPhaseSum (f : ComplexPositiveIntegerFunction)
    (P : Polynomial ℝ) (X H : ℝ) : ℂ :=
  ∑ n ∈ typeIIntervalSet X H, complexPositivePhaseTerm f P n

/-- The scalar Type I correlation on the exact real interval `(X,X+H]`. -/
def typeIScalarPhaseCorrelation (f : ComplexPositiveIntegerFunction)
    (P : Polynomial ℝ) (X H : ℝ) : ℝ :=
  ‖typeIScalarPhaseSum f P X H‖

@[simp]
theorem complexPositivePhaseTerm_eq_natExtension
    (f : ComplexPositiveIntegerFunction) (P : Polynomial ℝ) (n : ℕ) :
    complexPositivePhaseTerm f P n =
      complexPositiveIntegerNatExtension f n *
        unitFrequencyPhase (P.eval (n : ℝ)) := by
  by_cases hn : 0 < n <;> simp [complexPositivePhaseTerm,
    complexPositiveIntegerNatExtension, hn]

/-- Reindex a finite Dirichlet divisor sum as the corresponding finite sum
over factor pairs. -/
theorem finite_divisor_sum_reindex
    (M : Finset ℕ) (N : ℕ) (hM : M ⊆ Finset.Icc 1 N)
    (α β w : ℕ → ℂ) :
    (∑ n ∈ M, ∑ d ∈ n.divisors,
      α d * β (n / d) * w n) =
    ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      if a * b ∈ M then α a * β b * w (a * b) else 0 := by
  classical
  let t₀ : ℕ → Finset ℕ := fun n => n.divisors
  let s : Finset (Σ n : ℕ, ℕ) := M.sigma t₀
  let R : Finset ℕ := Finset.Icc 1 N
  let t : Finset (ℕ × ℕ) := (R ×ˢ R).filter fun p => p.1 * p.2 ∈ M
  have hleft :
      (∑ n ∈ M, ∑ d ∈ n.divisors, α d * β (n / d) * w n) =
        ∑ x ∈ s, α x.2 * β (x.1 / x.2) * w x.1 := by
    simpa [s, t₀] using
      (Finset.sum_sigma' M t₀ (fun n d => α d * β (n / d) * w n))
  have hright :
      (∑ a ∈ R, ∑ b ∈ R,
        if a * b ∈ M then α a * β b * w (a * b) else 0) =
        ∑ p ∈ t, α p.1 * β p.2 * w (p.1 * p.2) := by
    calc
      (∑ a ∈ R, ∑ b ∈ R,
          if a * b ∈ M then α a * β b * w (a * b) else 0) =
        ∑ p ∈ R ×ˢ R,
          (fun a b => if a * b ∈ M then α a * β b * w (a * b) else 0) p.1 p.2 := by
            exact (Finset.sum_product' R R
              (fun a b => if a * b ∈ M then α a * β b * w (a * b) else 0)).symm
      _ = ∑ p ∈ t, α p.1 * β p.2 * w (p.1 * p.2) := by
            rw [show t = (R ×ˢ R).filter (fun p => p.1 * p.2 ∈ M) by rfl,
              Finset.sum_filter]
  rw [hleft, hright]
  apply Finset.sum_bij'
    (fun x _ => (x.2, x.1 / x.2))
    (fun p hp => ⟨p.1 * p.2, p.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_sigma.mp (show x ∈ s from hx) with ⟨hnM, hd⟩
    have hnN := hM hnM
    have hnpos : 0 < x.1 := by
      have := (Finset.mem_Icc.mp hnN).1
      omega
    have hdpos : 0 < x.2 := Nat.pos_of_mem_divisors hd
    have hdiv : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hd
    have hdle : x.2 ≤ x.1 := Nat.le_of_dvd hnpos hdiv
    have hquotpos : 0 < x.1 / x.2 :=
      Nat.div_pos (Nat.le_of_dvd hnpos hdiv) hdpos
    have hquotle : x.1 / x.2 ≤ x.1 := Nat.div_le_self _ _
    have hprod : x.2 * (x.1 / x.2) = x.1 := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_Icc.mpr ⟨by omega, hdle.trans (Finset.mem_Icc.mp hnN).2⟩,
        Finset.mem_Icc.mpr ⟨by omega, hquotle.trans (Finset.mem_Icc.mp hnN).2⟩⟩
    · simpa [hprod] using hnM
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpR, hpM⟩
    rcases Finset.mem_product.mp hpR with ⟨haR, hbR⟩
    have haPos : 0 < p.1 := by
      have := (Finset.mem_Icc.mp haR).1
      omega
    have hbPos : 0 < p.2 := by
      have := (Finset.mem_Icc.mp hbR).1
      omega
    exact Finset.mem_sigma.mpr ⟨hpM,
      Nat.mem_divisors.mpr ⟨dvd_mul_right p.1 p.2,
        (Nat.mul_pos haPos hbPos).ne'⟩⟩
  · intro x hx
    rcases Finset.mem_sigma.mp (show x ∈ s from hx) with ⟨hnM, hd⟩
    have hdiv : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hd
    have hprod : x.2 * (x.1 / x.2) = x.1 := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
    apply Sigma.ext
    · exact hprod
    · rfl
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpR, hpM⟩
    rcases Finset.mem_product.mp hpR with ⟨haR, hbR⟩
    have haPos : 0 < p.1 := by
      have hprodPos := (Finset.mem_Icc.mp (hM hpM)).1
      rcases Nat.eq_zero_or_pos p.1 with hz | hpos
      · simp [hz] at hprodPos
      · exact hpos
    apply Prod.ext
    · rfl
    · calc
        p.1 * p.2 / p.1 = p.2 * p.1 / p.1 := by rw [Nat.mul_comm]
        _ = p.2 := Nat.mul_div_left _ haPos
  · intro x hx
    have hd : x.2 ∈ x.1.divisors := (Finset.mem_sigma.mp hx).2
    have hdiv : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hd
    have hprod : x.2 * (x.1 / x.2) = x.1 := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
    simp [hprod]

/-- At a positive index, the Type I convolution phase term expands to its
finite divisor sum with both factors totalized at zero. -/
theorem complexPositivePhaseTerm_convolution
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ) (n : ℕ)
    (hn : 0 < n) :
    complexPositivePhaseTerm (complexPositiveDirichletConvolution α β) P n =
      ∑ d ∈ n.divisors,
        complexPositiveIntegerNatExtension α d *
          complexPositiveIntegerNatExtension β (n / d) *
          unitFrequencyPhase (P.eval (n : ℝ)) := by
  rw [complexPositivePhaseTerm, dif_pos hn,
    complexPositiveDirichletConvolution_eq_divisor_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [complexDivisorConvolutionSummand_of_mem _ _ _ _ hd]
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hquot : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)) hdpos
  simp [complexPositiveIntegerNatExtension, hdpos, hquot]

/-- Exact finite factor-pair expansion of the scalar phase sum of a Type I
Dirichlet convolution on `(X,X+H]`. -/
theorem typeIScalarPhaseSum_eq_factor_pair_sum
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (N : ℕ)
    (hM : typeIIntervalSet X H ⊆ Finset.Icc 1 N) :
    typeIScalarPhaseSum (complexPositiveDirichletConvolution α β) P X H =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a * b ∈ typeIIntervalSet X H then
          complexPositiveIntegerNatExtension α a *
            complexPositiveIntegerNatExtension β b *
            unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
        else 0 := by
  classical
  unfold typeIScalarPhaseSum
  calc
    (∑ n ∈ typeIIntervalSet X H,
        complexPositivePhaseTerm (complexPositiveDirichletConvolution α β) P n) =
      ∑ n ∈ typeIIntervalSet X H,
        ∑ d ∈ n.divisors,
          complexPositiveIntegerNatExtension α d *
            complexPositiveIntegerNatExtension β (n / d) *
            unitFrequencyPhase (P.eval (n : ℝ)) := by
              apply Finset.sum_congr rfl
              intro n hn
              have hnpos : 0 < n := by
                have hnmem := Finset.mem_Icc.mp (hM hn)
                omega
              exact complexPositivePhaseTerm_convolution α β P n hnpos
    _ = _ := finite_divisor_sum_reindex
      (typeIIntervalSet X H) N hM
      (complexPositiveIntegerNatExtension α)
      (complexPositiveIntegerNatExtension β)
      (fun n => unitFrequencyPhase (P.eval (n : ℝ)))

/-- Factor the coefficient attached to the first variable out of a finite
Dirichlet factor-pair sum. -/
theorem finite_factor_pair_sum_factor
    (M R : Finset ℕ) (α β w : ℕ → ℂ) :
    (∑ a ∈ R, ∑ b ∈ R,
      if a * b ∈ M then α a * β b * w (a * b) else 0) =
      ∑ a ∈ R, α a *
        (∑ b ∈ R,
          if a * b ∈ M then β b * w (a * b) else 0) := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : a * b ∈ M <;> simp [hab, mul_assoc]

/-- A Type I second factor may multiply any phase sequence on a positive
integer interval at a cost of exactly `δ⁻¹` in the progression maximum. -/
private theorem interval_sum_mul_typeI_le
    (I : FiniteIntegerInterval) (β : ComplexPositiveIntegerFunction)
    (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ)
    (hI : ∀ n ∈ I.points, 0 < n)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹))
    (phase : {n : ℤ // n ∈ I.points} → ℂ) :
    ‖∑ n ∈ I.points.attach,
      phase n * complexPositiveIntegerZeroExtension β n.1‖ ≤
      δ⁻¹ * progressionMaximalSum I phase := by
  have hfinite := finiteResidueClassVariation_le_of_typeI
    I β q hq δ hδ hI hTV
  have hmax := progressionMaximalSum_mul_le_finiteResidueClassVariation
    I phase (complexPositiveIntegerZeroExtension β) q hq
  have hwhole := progressionMaximalSum_interval_lower I
    (fun n => phase n * complexPositiveIntegerZeroExtension β n.1)
  calc
    ‖∑ n ∈ I.points.attach,
        phase n * complexPositiveIntegerZeroExtension β n.1‖ ≤
      progressionMaximalSum I
        (fun n => phase n * complexPositiveIntegerZeroExtension β n.1) := hwhole
    _ ≤ finiteResidueClassVariation I
          (complexPositiveIntegerZeroExtension β) q * progressionMaximalSum I phase := hmax
    _ ≤ δ⁻¹ * progressionMaximalSum I phase :=
      mul_le_mul_of_nonneg_right hfinite
        (progressionMaximalSum_nonneg I phase)

/-- The integer interval of possible second factors after fixing the first
factor `a`. -/
private def typeIInnerInterval (a : ℕ) (X H : ℝ) : FiniteIntegerInterval :=
  ⟨Int.floor (X / (a : ℝ)) + 1,
    (Int.floor ((X + H) / (a : ℝ)) - Int.floor (X / (a : ℝ))).toNat⟩

/-- The inner interval consists exactly of integers strictly above the lower
floor and at most the upper floor. -/
private theorem typeIInnerInterval_points
    (u v : ℝ) (huv : u ≤ v) :
    (⟨Int.floor u + 1,
      (Int.floor v - Int.floor u).toNat⟩ : FiniteIntegerInterval).points =
      Finset.Ioc (Int.floor u) (Int.floor v) := by
  classical
  let lo : ℤ := Int.floor u
  let hi : ℤ := Int.floor v
  let I : FiniteIntegerInterval := ⟨lo + 1, (hi - lo).toNat⟩
  have hlohi : lo ≤ hi := Int.floor_mono huv
  have hcast : ((hi - lo).toNat : ℤ) = hi - lo :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hlohi)
  by_cases hEq : lo = hi
  · have hfloorEq : Int.floor u = Int.floor v := by simpa [lo, hi] using hEq
    simp [FiniteIntegerInterval.points, arithmeticProgressionPoints, hfloorEq]
  · have hlt : lo < hi := lt_of_le_of_ne hlohi hEq
    have hcastI : (I.length : ℤ) = hi - lo := by
      simpa [I] using hcast
    have hLne : I.length ≠ 0 := by
      intro hzero
      rw [hzero] at hcastI
      omega
    have hLpos : 0 < I.length := Nat.pos_of_ne_zero hLne
    have hLge : 1 ≤ I.length := hLpos
    have hlenSub : ((I.length - 1 : ℕ) : ℤ) = hi - lo - 1 := by
      rw [Nat.cast_sub hLge, hcastI]
      norm_num
    have hchar := arithmeticProgressionPoints_eq_Ioc_filter_modEq
      I.start 1 (by norm_num) I.length hLpos
    have hstart : I.start - 1 = lo := by simp [I]
    have hend : I.start + ((I.length - 1 : ℕ) : ℤ) = hi := by
      calc
        I.start + ((I.length - 1 : ℕ) : ℤ) =
            (lo + 1) + ((I.length - 1 : ℕ) : ℤ) := by simp [I]
        _ = hi := by rw [hlenSub]; omega
    have hI : I.points = Finset.Ioc lo hi := by
      rw [FiniteIntegerInterval.points, hchar]
      ext x
      simp [hstart, hend, Int.ModEq]
    simpa [I, lo, hi, typeIInnerInterval] using hI

/-- The exact second-factor interval has at most its real length plus one
integer points. -/
private theorem typeIInnerInterval_card_le
    (a : ℕ) (ha : 0 < a) (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H) :
    ((typeIInnerInterval a X H).points.card : ℝ) ≤ H / (a : ℝ) + 1 := by
  let u : ℝ := X / (a : ℝ)
  let v : ℝ := (X + H) / (a : ℝ)
  let I := typeIInnerInterval a X H
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have huv : u ≤ v := by
    dsimp [u, v]
    exact div_le_div_of_nonneg_right (by linarith) haR.le
  have hpoints : I.points = Finset.Ioc (Int.floor u) (Int.floor v) := by
    simpa [I, typeIInnerInterval, u, v] using
      typeIInnerInterval_points u v huv
  have hcardZ : ((I.points.card : ℕ) : ℤ) = Int.floor v - Int.floor u := by
    rw [hpoints]
    exact Int.card_Ioc_of_le _ _ (Int.floor_mono huv)
  have hcardR : (I.points.card : ℝ) =
      (Int.floor v : ℝ) - (Int.floor u : ℝ) := by
    exact_mod_cast hcardZ
  have hfloorV : (Int.floor v : ℝ) ≤ v := Int.floor_le v
  have hfloorU : u < (Int.floor u : ℝ) + 1 := Int.lt_floor_add_one u
  have hlength : v - u = H / (a : ℝ) := by
    dsimp [u, v]
    field_simp [ne_of_gt haR]
    <;> ring
  calc
    (I.points.card : ℝ) =
        (Int.floor v : ℝ) - (Int.floor u : ℝ) := hcardR
    _ ≤ v - u + 1 := by nlinarith [hfloorV, hfloorU]
    _ = H / (a : ℝ) + 1 := by rw [hlength]

/-- Membership in the factor interval is equivalent to the two real bounds
obtained after dividing the original interval by `a`. -/
private theorem typeIInnerInterval_mem_iff
    (a : ℕ) (ha : 0 < a) (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (b : ℤ) :
    b ∈ (typeIInnerInterval a X H).points ↔
      X / (a : ℝ) < (b : ℝ) ∧
        (b : ℝ) ≤ (X + H) / (a : ℝ) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have huv : X / (a : ℝ) ≤ (X + H) / (a : ℝ) := by
    exact div_le_div_of_nonneg_right (by linarith) haR.le
  have hpoints := typeIInnerInterval_points
    (X / (a : ℝ)) ((X + H) / (a : ℝ)) huv
  rw [typeIInnerInterval, hpoints]
  simp only [Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

/-- Every integer in the inner interval is positive when the original left
endpoint is nonnegative. -/
private theorem typeIInnerInterval_positive
    (a : ℕ) (ha : 0 < a) (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (n : ℤ) (hn : n ∈ (typeIInnerInterval a X H).points) :
    0 < n := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hfloor : 0 ≤ Int.floor (X / (a : ℝ)) :=
    Int.floor_nonneg.mpr (div_nonneg hX haR.le)
  have hmem := (typeIInnerInterval_mem_iff a ha X H hX hH n).mp hn
  exact lt_of_le_of_lt hfloor (Int.floor_lt.mpr hmem.1)

/-- The factor-pair condition is exactly membership of the second factor in
the divided real interval. -/
private theorem typeIInnerInterval_nat_mem_iff
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (X H : ℝ)
    (hX : 0 ≤ X) (hH : 0 ≤ H) :
    (b : ℤ) ∈ FiniteIntegerInterval.points (typeIInnerInterval a X H) ↔
      a * b ∈ typeIIntervalSet X H := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  constructor
  · intro hbI
    have hbBounds :=
      (typeIInnerInterval_mem_iff a ha X H hX hH (b : ℤ)).mp hbI
    have hlow : X < ((a * b : ℕ) : ℝ) := by
      have h := (div_lt_iff₀ haR).mp hbBounds.1
      simpa [Nat.cast_mul, mul_comm] using h
    have hupp : ((a * b : ℕ) : ℝ) ≤ X + H := by
      have h := (le_div_iff₀ haR).mp hbBounds.2
      simpa [Nat.cast_mul, mul_comm] using h
    apply (mem_typeIIntervalSet X H (a * b)).2
    refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos ha hb)), hlow, hupp⟩
  · intro hab
    rcases (mem_typeIIntervalSet X H (a * b)).1 hab with ⟨_, hlow, hupp⟩
    apply (typeIInnerInterval_mem_iff a ha X H hX hH (b : ℤ)).mpr
    constructor
    · apply (div_lt_iff₀ haR).2
      simpa [Nat.cast_mul, mul_comm] using hlow
    · apply (le_div_iff₀ haR).2
      simpa [Nat.cast_mul, mul_comm] using hupp

/-- The natural number represented by a point of the inner interval lies in
the original finite cutoff. -/
private theorem typeIInnerInterval_nat_bounds
    (a : ℕ) (ha : 0 < a) (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (z : ℤ) (hz : z ∈ (typeIInnerInterval a X H).points) :
    1 ≤ z.toNat ∧ z.toNat ≤ Nat.floor (X + H) := by
  have hzpos := typeIInnerInterval_positive a ha X H hX hH z hz
  have hzcast : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hzpos.le
  have haOne : 1 ≤ (a : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr ha)
  have hrealTop : 0 ≤ X + H := by linarith
  have hdiv : (X + H) / (a : ℝ) ≤ X + H := div_le_self hrealTop haOne
  have hzupper :=
    (typeIInnerInterval_mem_iff a ha X H hX hH z).mp hz |>.2
  have hNatupper : (z.toNat : ℝ) ≤ X + H := by
    have hzcastR : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast hzcast
    exact hzcastR ▸ hzupper.trans hdiv
  constructor
  · have hzNatpos : 0 < z.toNat := by omega
    exact Nat.succ_le_iff.mpr hzNatpos
  · exact Nat.le_floor hNatupper

/-- Reindex the finite natural sum over valid second factors as the exact
integer interval sum used by the Abel variation estimate. -/
private theorem typeIInnerFactorSum_eq_interval
    (a : ℕ) (ha : 0 < a) (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ) :
    (∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
      if a * b ∈ typeIIntervalSet X H then
        complexPositiveIntegerNatExtension β b *
          unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
      else 0) =
      ∑ z ∈ (typeIInnerInterval a X H).points.attach,
        complexPositiveIntegerZeroExtension β z.1 *
          unitFrequencyPhase (P.eval (((a : ℤ) * z.1 : ℤ) : ℝ)) := by
  classical
  let I := typeIInnerInterval a X H
  let R := Finset.Icc 1 (Nat.floor (X + H))
  let B := R.filter fun b => a * b ∈ typeIIntervalSet X H
  let sourceTerm : ℕ → ℂ := fun b =>
    complexPositiveIntegerNatExtension β b *
      unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
  let targetTerm : {z : ℤ // z ∈ I.points} → ℂ := fun z =>
    complexPositiveIntegerZeroExtension β z.1 *
      unitFrequencyPhase (P.eval (((a : ℤ) * z.1 : ℤ) : ℝ))
  have hfilter :
      (∑ b ∈ R,
        if a * b ∈ typeIIntervalSet X H then sourceTerm b else 0) =
        ∑ b ∈ B, sourceTerm b := by
    rw [show B = R.filter (fun b => a * b ∈ typeIIntervalSet X H) by rfl,
      Finset.sum_filter]
  rw [show (∑ b ∈ R,
      if a * b ∈ typeIIntervalSet X H then sourceTerm b else 0) =
      ∑ b ∈ B, sourceTerm b by exact hfilter]
  exact Finset.sum_bij'
    (fun b hb => ⟨(b : ℤ), by
      rcases Finset.mem_filter.mp hb with ⟨hbR, hab⟩
      have hbpos : 0 < b := by
        have hbOne := (Finset.mem_Icc.mp hbR).1
        omega
      exact (typeIInnerInterval_nat_mem_iff
        a b ha hbpos X H hX hH).2 hab⟩)
    (fun z _ => z.1.toNat)
    (by
      intro b hb
      exact Finset.mem_attach _ _)
    (by
      intro z hz
      obtain ⟨hbOne, hbUpper⟩ :=
        typeIInnerInterval_nat_bounds a ha X H hX hH z.1 z.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hbOne, hbUpper⟩, ?_⟩
      have hbpos : 0 < z.1.toNat := Nat.succ_le_iff.mp hbOne
      have hcast : ((z.1.toNat : ℕ) : ℤ) = z.1 :=
        Int.toNat_of_nonneg
          (typeIInnerInterval_positive a ha X H hX hH z.1 z.2).le
      have hmem : (z.1.toNat : ℤ) ∈ I.points := by
        rw [hcast]
        exact z.2
      exact (typeIInnerInterval_nat_mem_iff a z.1.toNat ha hbpos
        X H hX hH).1 hmem)
    (by
      intro b hb
      simp)
    (by
      intro z hz
      apply Subtype.ext
      change ((z.1.toNat : ℕ) : ℤ) = z.1
      exact Int.toNat_of_nonneg
        (typeIInnerInterval_positive a ha X H hX hH z.1 z.2).le)
    (by
      intro b hb
      rcases Finset.mem_filter.mp hb with ⟨hbR, hab⟩
      have hbpos : 0 < b := by
        have hbOne := (Finset.mem_Icc.mp hbR).1
        omega
      have hβ : complexPositiveIntegerZeroExtension β (b : ℤ) =
          complexPositiveIntegerNatExtension β b := by
        simp [complexPositiveIntegerZeroExtension,
          complexPositiveIntegerNatExtension, hbpos]
      have hphase : (((a : ℤ) * (b : ℤ) : ℤ) : ℝ) =
          ((a * b : ℕ) : ℝ) := by
        norm_cast
      simp [sourceTerm, targetTerm, hβ, hphase])

/-- The phase sequence on the inner interval after dilation by `a`. -/
private def typeIInnerPhaseFunction
    (a : ℕ) (P : Polynomial ℝ) (I : FiniteIntegerInterval) :
    {n : ℤ // n ∈ I.points} → ℂ := fun n =>
      unitFrequencyPhase (P.eval (((a : ℤ) * n.1 : ℤ) : ℝ))

/-- Apply the exact Type I variation estimate to the inner sum for one fixed
positive dilation. -/
private theorem typeIInnerFactorSum_norm_le
    (a : ℕ) (ha : 0 < a) (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹)) :
    ‖∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
      if a * b ∈ typeIIntervalSet X H then
        complexPositiveIntegerNatExtension β b *
          unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
      else 0‖ ≤
      δ⁻¹ * progressionMaximalSum (typeIInnerInterval a X H)
        (typeIInnerPhaseFunction a P (typeIInnerInterval a X H)) := by
  let I := typeIInnerInterval a X H
  have hIpositive : ∀ n ∈ I.points, 0 < n := by
    intro n hn
    exact typeIInnerInterval_positive a ha X H hX hH n hn
  have hsum := typeIInnerFactorSum_eq_interval a ha X H hX hH β P
  have hcomm :
      (∑ z ∈ I.points.attach,
        complexPositiveIntegerZeroExtension β z.1 *
          unitFrequencyPhase (P.eval (((a : ℤ) * z.1 : ℤ) : ℝ))) =
      ∑ z ∈ I.points.attach,
        typeIInnerPhaseFunction a P I z *
          complexPositiveIntegerZeroExtension β z.1 := by
    apply Finset.sum_congr rfl
    intro z hz
    simp [typeIInnerPhaseFunction, mul_comm]
  have hAbel := interval_sum_mul_typeI_le I β q hq δ hδ
    hIpositive hTV (typeIInnerPhaseFunction a P I)
  rw [hsum, hcomm]
  simpa [I] using hAbel

/-- A maximal progression sum on a finite interval is attained by one of its
finite arithmetic progressions. -/
private theorem exists_progression_sum_ge_of_le_maximal
    (I : FiniteIntegerInterval) (phase : ℤ → ℂ) (t : ℝ)
    (ht : t ≤ progressionMaximalSum I (fun n => phase n.1)) :
    ∃ J : Finset ℤ,
      J ⊆ I.points ∧ isFiniteArithmeticProgression J ∧
        t ≤ ‖∑ n ∈ J, phase n‖ := by
  classical
  let F := arithmeticProgressionsWithin I.points
  let f : Finset ℤ → ℝ := fun J =>
    ‖∑ n ∈ J, extendByZero I.points (fun z => phase z.1) n‖
  have hmax : t ≤ F.sup' (arithmeticProgressionsWithin_nonempty I.points) f := by
    simpa [F, f, progressionMaximalSum] using ht
  obtain ⟨J, hJmem, hJlarge⟩ :=
    (Finset.le_sup'_iff (arithmeticProgressionsWithin_nonempty I.points)).mp hmax
  rcases Finset.mem_filter.mp hJmem with ⟨hJsub, hJAP⟩
  have hJsubset : J ⊆ I.points := Finset.mem_powerset.mp hJsub
  have hsum :
      (∑ n ∈ J, extendByZero I.points (fun z => phase z.1) n) =
        ∑ n ∈ J, phase n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [extendByZero, hJsubset hn]
  exact ⟨J, hJsubset, hJAP, hsum ▸ hJlarge⟩

/-- Every member of the original real interval is below its exact natural
floor cutoff. -/
theorem typeIIntervalSet_subset_floor (X H : ℝ) :
    typeIIntervalSet X H ⊆ Finset.Icc 1 (Nat.floor (X + H)) := by
  intro n hn
  rcases (mem_typeIIntervalSet X H n).1 hn with ⟨hnlo, _, hnhi⟩
  exact Finset.mem_Icc.mpr ⟨hnlo, Nat.le_floor hnhi⟩

/-- The exact factor-pair expansion with the first coefficient factored out. -/
theorem typeIScalarPhaseSum_factorized
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) :
    typeIScalarPhaseSum (complexPositiveDirichletConvolution α β) P X H =
      ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        complexPositiveIntegerNatExtension α a *
          (∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
            if a * b ∈ typeIIntervalSet X H then
              complexPositiveIntegerNatExtension β b *
                unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
            else 0) := by
  rw [typeIScalarPhaseSum_eq_factor_pair_sum α β P X H
    (Nat.floor (X + H)) (typeIIntervalSet_subset_floor X H)]
  exact finite_factor_pair_sum_factor
    (typeIIntervalSet X H) (Finset.Icc 1 (Nat.floor (X + H)))
    (complexPositiveIntegerNatExtension α)
    (complexPositiveIntegerNatExtension β)
    (fun n => unitFrequencyPhase (P.eval (n : ℝ)))

/-- The maximal phase sum after dilation by `a`. -/
private def typeIInnerMaximalSum (a : ℕ) (P : Polynomial ℝ)
    (X H : ℝ) : ℝ :=
  progressionMaximalSum (typeIInnerInterval a X H)
    (typeIInnerPhaseFunction a P (typeIInnerInterval a X H))

/-- The polynomial phase after dilation by a positive integer. -/
private def typeIDilatedPolynomial (P : Polynomial ℝ) (a : ℕ) : Polynomial ℝ :=
  P.comp (Polynomial.C (a : ℝ) * Polynomial.X)

private theorem typeIDilatedPolynomial_degree
    (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (a : ℕ) :
    (typeIDilatedPolynomial P a).natDegree ≤ d := by
  have hlinear :
      (Polynomial.C (a : ℝ) * Polynomial.X).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  calc
    (typeIDilatedPolynomial P a).natDegree ≤
        P.natDegree * (Polynomial.C (a : ℝ) * Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ d * 1 := Nat.mul_le_mul hP hlinear
    _ = d := by simp

private theorem typeIDilatedPolynomial_eval
    (P : Polynomial ℝ) (a : ℕ) (x : ℝ) :
    (typeIDilatedPolynomial P a).eval x = P.eval ((a : ℝ) * x) := by
  rw [typeIDilatedPolynomial, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

private theorem typeIDilatedPolynomial_centered
    (P : Polynomial ℝ) (a : ℕ) (q : ℤ) :
    (typeIDilatedPolynomial P a).comp
        (Polynomial.X + Polynomial.C (q : ℝ)) =
      phaseDilatedAt P a q := by
  have hlinear :
      (Polynomial.C (a : ℝ) * Polynomial.X).comp
          (Polynomial.X + Polynomial.C (q : ℝ)) =
        Polynomial.C ((a : ℝ) * (q : ℝ)) +
          Polynomial.C (a : ℝ) * Polynomial.X := by
    simp only [Polynomial.comp, Polynomial.eval₂_mul,
      Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_X]
    calc
      Polynomial.C (a : ℝ) * (Polynomial.X + Polynomial.C (q : ℝ)) =
          Polynomial.C (a : ℝ) * Polynomial.X +
            Polynomial.C (a : ℝ) * Polynomial.C (q : ℝ) := by rw [mul_add]
      _ = Polynomial.C ((a : ℝ) * (q : ℝ)) +
          Polynomial.C (a : ℝ) * Polynomial.X := by
        rw [Polynomial.C_mul]
        ac_rfl
  rw [typeIDilatedPolynomial, Polynomial.comp_assoc, hlinear]
  rfl

/-- A high maximal sum on one dilation supplies the exact local data required
by the progression inverse theorem, with `κ=δ⁴/16`. -/
private theorem typeI_local_progression_inverse
    {d : ℕ} (hd : 1 ≤ d) (δ H A X : ℝ)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hH : 0 < H) (hA : 0 < A)
    (a : ℕ) (ha : 0 < a) (hAa : A < (a : ℝ))
    (hHdiv : 1 ≤ H / (a : ℝ))
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (J : Finset ℤ) (hJAP : isFiniteArithmeticProgression J)
    (hJsubset : ∀ n ∈ J,
      X / (a : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ X / (a : ℝ) + H / (a : ℝ))
    (hJlarge : (δ ^ 4 / 16) * (H / A) ≤
      ‖∑ n ∈ J,
        unitFrequencyPhase
          (P.eval (((a : ℤ) * n : ℤ) : ℝ))‖) :
    ∃ r : ℤ, 1 ≤ r ∧
      (r : ℝ) ≤ inverseBoundG d (16 * δ⁻¹ ^ 4) ∧
      ∀ j, 1 ≤ j → j ≤ d →
        (H / (a : ℝ)) ^ j *
          realDistanceToIntegers
            ((r : ℝ) * (phaseDilatedAt P a
              (Int.floor (X / (a : ℝ)))).coeff j) ≤
          inverseBoundG d (16 * δ⁻¹ ^ 4) := by
  let κ : ℝ := δ ^ 4 / 16
  have hκpos : 0 < κ := by dsimp [κ]; positivity
  have hδle : δ ≤ 1 / 2 := hδhalf.le
  have hδpow : δ ^ 4 ≤ (1 / 2 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hδle 4
  have hκhalf : κ < 1 / 2 := by
    dsimp [κ]
    norm_num at hδpow ⊢
    nlinarith
  have hκinv : κ⁻¹ = 16 * δ⁻¹ ^ 4 := by
    dsimp [κ]
    field_simp [ne_of_gt hδ]
    <;> ring
  have hratio : H / (a : ℝ) ≤ H / A :=
    div_le_div_of_nonneg_left hH.le hA (by exact_mod_cast hAa.le)
  have hthreshold : κ * (H / (a : ℝ)) ≤
      ‖∑ n ∈ J, unitFrequencyPhase
          (P.eval (((a : ℤ) * n : ℤ) : ℝ))‖ := by
    calc
      κ * (H / (a : ℝ)) ≤ κ * (H / A) :=
        mul_le_mul_of_nonneg_left hratio hκpos.le
      _ = (δ ^ 4 / 16) * (H / A) := by rfl
      _ ≤ _ := hJlarge
  have hphaseSum :
      (∑ n ∈ J, unitFrequencyPhase
        (P.eval (((a : ℤ) * n : ℤ) : ℝ))) =
      ∑ n ∈ J, unitFrequencyPhase
        ((typeIDilatedPolynomial P a).eval (n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [typeIDilatedPolynomial_eval]
    congr 2
    norm_cast
  have hthreshold' : κ * (H / (a : ℝ)) ≤
      ‖∑ n ∈ J, unitFrequencyPhase
        ((typeIDilatedPolynomial P a).eval (n : ℝ))‖ := by
    rw [← hphaseSum]
    exact hthreshold
  obtain ⟨r, hrpos, hrbound, hcoeff⟩ :=
    progressionPhaseInverse d hd (H / (a : ℝ)) hHdiv (X / (a : ℝ))
      hκpos hκhalf (typeIDilatedPolynomial P a)
      (typeIDilatedPolynomial_degree d P hP a) J hJAP hJsubset hthreshold'
  refine ⟨(r : ℤ), ?_, ?_, ?_⟩
  · exact_mod_cast hrpos
  · have hrbound' : (r : ℝ) ≤ inverseBoundG d (16 * δ⁻¹ ^ 4) := by
      simpa [hκinv] using hrbound
    simpa only [Int.cast_natCast] using hrbound'
  · intro j hj hjd
    have hlocal := hcoeff j hj hjd
    rw [typeIDilatedPolynomial_centered] at hlocal
    simpa [hκinv, Int.cast_natCast] using hlocal

private theorem phaseCenteredAt_degree_le
    {d : ℕ} (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (Y : ℤ) :
    (phaseCenteredAt P Y).natDegree ≤ d := by
  have hlinear :
      (Polynomial.C (Y : ℝ) + Polynomial.X).natDegree ≤ 1 := by
    rw [add_comm, Polynomial.natDegree_X_add_C]
  calc
    (phaseCenteredAt P Y).natDegree ≤
        P.natDegree * (Polynomial.C (Y : ℝ) + Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ d * 1 := Nat.mul_le_mul hP hlinear
    _ = d := by simp

/-- The centered phase has its exact degree-`d` monomial expansion. -/
private theorem phaseCenteredAt_monomial_expansion
    {d : ℕ} (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (Y : ℤ) :
    P.comp (Polynomial.X + Polynomial.C (Y : ℝ)) =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C ((phaseCenteredAt P Y).coeff j) * Polynomial.X ^ j := by
  have hcenter :
      P.comp (Polynomial.X + Polynomial.C (Y : ℝ)) = phaseCenteredAt P Y := by
    rw [phaseCenteredAt]
    congr 1
    exact add_comm _ _
  have hsum : phaseCenteredAt P Y =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C ((phaseCenteredAt P Y).coeff j) * Polynomial.X ^ j := by
    calc
      phaseCenteredAt P Y =
          ∑ j ∈ Finset.range ((phaseCenteredAt P Y).natDegree + 1),
            Polynomial.C ((phaseCenteredAt P Y).coeff j) * Polynomial.X ^ j :=
        (phaseCenteredAt P Y).as_sum_range_C_mul_X_pow
      _ = ∑ j ∈ Finset.range (d + 1),
            Polynomial.C ((phaseCenteredAt P Y).coeff j) * Polynomial.X ^ j := by
        apply Finset.sum_subset
        · intro j hj
          exact Finset.mem_range.mpr
            (Nat.lt_of_lt_of_le (Finset.mem_range.mp hj)
              (Nat.add_le_add_right (phaseCenteredAt_degree_le P hP Y) 1))
        · intro j hj hnot
          have hjlarge : (phaseCenteredAt P Y).natDegree < j := by
            simp only [Finset.mem_range] at hj hnot
            omega
          simp [Polynomial.coeff_eq_zero_of_natDegree_lt hjlarge]
  exact hcenter.trans hsum

/-- Unit-modulus phases give the exact interval-length upper bound for the
dilated maximal sum. -/
private theorem typeIInnerMaximalSum_le_two_H_over_A
    (a : ℕ) (ha : 0 < a) (P : Polynomial ℝ) (X H A : ℝ)
    (hX : 0 ≤ X) (hH : 0 < H) (hA : 0 < A)
    (hAa : A < (a : ℝ)) (hHdiv : 1 ≤ H / (a : ℝ)) :
    typeIInnerMaximalSum a P X H ≤ 2 * H / A := by
  let I := typeIInnerInterval a X H
  have hmax := progressionMaximalSum_le_interval_norm_sum I
    (typeIInnerPhaseFunction a P I)
  have hnormSum :
      (∑ x ∈ I.points.attach,
        ‖typeIInnerPhaseFunction a P I x‖) = (I.points.card : ℝ) := by
    simp [typeIInnerPhaseFunction, norm_unitFrequencyPhase]
  have hcard := typeIInnerInterval_card_le a ha X H hX hH.le
  have hmaxBound : typeIInnerMaximalSum a P X H ≤ H / (a : ℝ) + 1 := by
    simpa [typeIInnerMaximalSum, I] using hmax.trans (hnormSum ▸ hcard)
  have hdiv : H / (a : ℝ) ≤ H / A :=
    div_le_div_of_nonneg_left hH.le hA (by exact_mod_cast hAa.le)
  calc
    typeIInnerMaximalSum a P X H ≤ H / (a : ℝ) + 1 := hmaxBound
    _ ≤ 2 * (H / (a : ℝ)) := by nlinarith [hHdiv]
    _ ≤ 2 * (H / A) := by nlinarith [hdiv]
    _ = 2 * H / A := by ring

/-- The Type I convolution correlation is bounded by the weighted sum of
the dilated maximal phase sums, with the exact variation loss `δ⁻¹`. -/
private theorem typeIScalarPhaseSum_norm_le_weightedMaxima
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H δ : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H) (hδ : 0 < δ)
    (q : ℕ) (hq : 0 < q)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹)) :
    ‖typeIScalarPhaseSum (complexPositiveDirichletConvolution α β) P X H‖ ≤
      δ⁻¹ * ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ‖complexPositiveIntegerNatExtension α a‖ *
          typeIInnerMaximalSum a P X H := by
  rw [typeIScalarPhaseSum_factorized]
  calc
    ‖∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        complexPositiveIntegerNatExtension α a *
          (∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
            if a * b ∈ typeIIntervalSet X H then
              complexPositiveIntegerNatExtension β b *
                unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
            else 0)‖ ≤
      ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ‖complexPositiveIntegerNatExtension α a *
          (∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
            if a * b ∈ typeIIntervalSet X H then
              complexPositiveIntegerNatExtension β b *
                unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
            else 0)‖ := norm_sum_le _ _
    _ = ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ‖complexPositiveIntegerNatExtension α a‖ *
          ‖∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
            if a * b ∈ typeIIntervalSet X H then
              complexPositiveIntegerNatExtension β b *
                unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
            else 0‖ := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [norm_mul]
    _ ≤ ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ‖complexPositiveIntegerNatExtension α a‖ *
          (δ⁻¹ * typeIInnerMaximalSum a P X H) := by
          apply Finset.sum_le_sum
          intro a ha
          have haPos : 0 < a := by
            have := (Finset.mem_Icc.mp ha).1
            omega
          exact mul_le_mul_of_nonneg_left
            (typeIInnerFactorSum_norm_le a haPos X H hX hH β P
              q hq δ hδ hTV)
            (norm_nonneg _)
    _ = δ⁻¹ * ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ‖complexPositiveIntegerNatExtension α a‖ *
          typeIInnerMaximalSum a P X H := by
          calc
            _ = ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
                δ⁻¹ * (‖complexPositiveIntegerNatExtension α a‖ *
                  typeIInnerMaximalSum a P X H) := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    ring
            _ = _ := by rw [← Finset.mul_sum]

/-- The factor-pair expansion bounds the correlation by the weighted absolute
values of its inner Dirichlet sums, before applying variation. -/
private theorem typeIScalarPhaseSum_norm_le_weightedInnerSums
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) :
    ‖typeIScalarPhaseSum (complexPositiveDirichletConvolution α β) P X H‖ ≤
      ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ‖complexPositiveIntegerNatExtension α a‖ *
          ‖∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
            if a * b ∈ typeIIntervalSet X H then
              complexPositiveIntegerNatExtension β b *
                unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
            else 0‖ := by
  rw [typeIScalarPhaseSum_factorized]
  calc
    ‖∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        complexPositiveIntegerNatExtension α a *
          (∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
            if a * b ∈ typeIIntervalSet X H then
              complexPositiveIntegerNatExtension β b *
                unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
            else 0)‖ ≤
      ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
        ‖complexPositiveIntegerNatExtension α a *
          (∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
            if a * b ∈ typeIIntervalSet X H then
              complexPositiveIntegerNatExtension β b *
                unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
            else 0)‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [norm_mul]

/-- The weighted inner-sum summand before taking its finite dyadic blocks. -/
private def typeIInnerWeightedTerm
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H : ℝ) (a : ℕ) : ℝ :=
  ‖complexPositiveIntegerNatExtension α a‖ *
    ‖∑ b ∈ Finset.Icc 1 (Nat.floor (X + H)),
      if a * b ∈ typeIIntervalSet X H then
        complexPositiveIntegerNatExtension β b *
          unitFrequencyPhase (P.eval ((a * b : ℕ) : ℝ))
      else 0‖

/-- Type I support above `A_I<X` makes every weighted summand past
`floor X` vanish exactly. -/
private theorem typeIInnerWeightedSum_eq_floorX
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H A_I : ℝ) (hH : 0 ≤ H) (hAI : A_I < X)
    (hsupp : complexPositiveSupportedOnInterval α 1 A_I) :
    (∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
      typeIInnerWeightedTerm α β P X H a) =
    ∑ a ∈ Finset.Icc 1 (Nat.floor X),
      typeIInnerWeightedTerm α β P X H a := by
  have hcut : Nat.floor X ≤ Nat.floor (X + H) :=
    Nat.floor_mono (by linarith)
  have hsub : Finset.Icc 1 (Nat.floor X) ⊆
      Finset.Icc 1 (Nat.floor (X + H)) := by
    intro a ha
    rcases Finset.mem_Icc.mp ha with ⟨haone, haX⟩
    exact Finset.mem_Icc.mpr ⟨haone, haX.trans hcut⟩
  symm
  apply Finset.sum_subset hsub
  intro a haBig haNotSmall
  have haOne : 1 ≤ a := (Finset.mem_Icc.mp haBig).1
  have haAbove : Nat.floor X < a := by
    by_contra h
    exact haNotSmall (Finset.mem_Icc.mpr ⟨haOne, le_of_not_gt h⟩)
  have hfloor : X < (Nat.floor X : ℝ) + 1 := Nat.lt_floor_add_one X
  have haCast : (Nat.floor X : ℝ) + 1 ≤ (a : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr haAbove)
  have hXltA : X < (a : ℝ) := lt_of_lt_of_le hfloor haCast
  have haPos : 0 < a := by omega
  have hαzero : complexPositiveIntegerNatExtension α a = 0 := by
    by_contra hne
    have hαval : α ⟨a, haPos⟩ ≠ 0 := by
      simpa [complexPositiveIntegerNatExtension, haPos] using hne
    have hαupper := (hsupp ⟨a, haPos⟩ hαval).2
    linarith
  simp [typeIInnerWeightedTerm, hαzero]

/-- On any finite set of positive dilations, the exact Type I variation
estimate converts inner sums into the progression maxima with loss `δ⁻¹`. -/
private theorem typeI_block_raw_weight_le_maxima
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H δ : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (q : ℕ) (hq : 0 < q) (hδ : 0 < δ)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹))
    (S : Finset ℕ) (hSpos : ∀ a ∈ S, 0 < a) :
    (∑ a ∈ S, typeIInnerWeightedTerm α β P X H a) ≤
      δ⁻¹ * ∑ a ∈ S,
        ‖complexPositiveIntegerNatExtension α a‖ *
          typeIInnerMaximalSum a P X H := by
  calc
    (∑ a ∈ S, typeIInnerWeightedTerm α β P X H a) ≤
        ∑ a ∈ S,
          ‖complexPositiveIntegerNatExtension α a‖ *
            (δ⁻¹ * typeIInnerMaximalSum a P X H) := by
      apply Finset.sum_le_sum
      intro a ha
      dsimp [typeIInnerWeightedTerm]
      exact mul_le_mul_of_nonneg_left
        (typeIInnerFactorSum_norm_le a (hSpos a ha) X H hX hH β P
          q hq δ hδ hTV)
        (norm_nonneg _)
    _ = δ⁻¹ * ∑ a ∈ S,
          ‖complexPositiveIntegerNatExtension α a‖ *
            typeIInnerMaximalSum a P X H := by
      calc
        _ = ∑ a ∈ S, δ⁻¹ *
              (‖complexPositiveIntegerNatExtension α a‖ *
                typeIInnerMaximalSum a P X H) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = _ := by rw [← Finset.mul_sum]

/-- The Type I second moment and Cauchy--Schwarz give the exact lower bound
for the sum of squares of the dilated maximal phase sums. -/
private theorem typeI_block_maxima_square_sum_lower
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ)
    (X H δ A ρ : ℝ) (hX : 0 ≤ X) (hH : 0 < H)
    (hδ : 0 < δ) (hAhalf : 1 / 2 ≤ A)
    (hρ : 0 < ρ)
    (hMoment : complexPositiveSecondMomentBound δ α)
    (q : ℕ) (hq : 0 < q)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹))
    (S : Finset ℕ)
    (hSbounds : ∀ a ∈ S, A < (a : ℝ) ∧
      (a : ℝ) ≤ 2 * A)
    (hRaw : ρ * H ≤ ∑ a ∈ S, typeIInnerWeightedTerm α β P X H a) :
    (δ ^ 3 * ρ ^ 2 * H ^ 2) / (2 * A) ≤
      ∑ a ∈ S, (typeIInnerMaximalSum a P X H) ^ 2 := by
  have hApos : 0 < A := by linarith
  have h2A : 1 ≤ 2 * A := by linarith
  have hSpos : ∀ a ∈ S, 0 < a := by
    intro a ha
    have haLow := hSbounds a ha |>.1
    have haPositive : 0 < (a : ℝ) := lt_trans hApos haLow
    exact_mod_cast haPositive
  have hmaxLower := typeI_block_raw_weight_le_maxima α β P X H δ hX hH.le
    q hq hδ hTV S hSpos
  have hweightedLower : δ * (ρ * H) ≤
      ∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ *
        typeIInnerMaximalSum a P X H := by
    have hmul := mul_le_mul_of_nonneg_left
      (hRaw.trans hmaxLower) hδ.le
    calc
      δ * (ρ * H) ≤
          δ * (δ⁻¹ *
            ∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ *
              typeIInnerMaximalSum a P X H) := hmul
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
  have hSsubset : S ⊆ Finset.Icc 1 (Nat.floor (2 * A)) := by
    intro a ha
    rcases hSbounds a ha with ⟨haLow, haHigh⟩
    have haOne : 1 ≤ a := Nat.succ_le_iff.mpr (hSpos a ha)
    have haUpper : a ≤ Nat.floor (2 * A) := Nat.le_floor haHigh
    exact Finset.mem_Icc.mpr ⟨haOne, haUpper⟩
  have hMomentSum :
      (∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ ^ 2) ≤
        complexPositiveSecondMoment α (2 * A) := by
    calc
      (∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ ^ 2) =
          ∑ a ∈ S, complexPositiveSecondMomentSummand α a := by
            apply Finset.sum_congr rfl
            intro a ha
            have haPos := hSpos a ha
            simp [complexPositiveIntegerNatExtension,
              complexPositiveSecondMomentSummand, haPos]
      _ ≤ complexPositiveSecondMoment α (2 * A) := by
        unfold complexPositiveSecondMoment
        apply Finset.sum_le_sum_of_subset_of_nonneg hSsubset
        intro a ha hnot
        simp [complexPositiveSecondMomentSummand]
        by_cases haPos : 0 < a <;> simp [haPos]
  have hMomentBound :
      complexPositiveSecondMoment α (2 * A) ≤ δ⁻¹ * (2 * A) :=
    hMoment (2 * A) h2A
  have hMsumNonneg : 0 ≤
      ∑ a ∈ S, (typeIInnerMaximalSum a P X H) ^ 2 := by
    apply Finset.sum_nonneg
    intro a ha
    exact sq_nonneg _
  have hAlphaSquare :
      (∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ ^ 2) ≤
        (2 * A) / δ := by
    calc
      _ ≤ complexPositiveSecondMoment α (2 * A) := hMomentSum
      _ ≤ δ⁻¹ * (2 * A) := hMomentBound
      _ = (2 * A) / δ := by ring
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun a => ‖complexPositiveIntegerNatExtension α a‖)
    (fun a => typeIInnerMaximalSum a P X H)
  have hCauchy' :
      (∑ a ∈ S,
        ‖complexPositiveIntegerNatExtension α a‖ *
          typeIInnerMaximalSum a P X H) ^ 2 ≤
        (∑ a ∈ S, ‖complexPositiveIntegerNatExtension α a‖ ^ 2) *
          ∑ a ∈ S, (typeIInnerMaximalSum a P X H) ^ 2 := hCauchy
  have hdenom : 0 < (2 * A) / δ := div_pos (by positivity) hδ
  have hsumNonneg : 0 ≤
      ∑ a ∈ S,
        ‖complexPositiveIntegerNatExtension α a‖ *
          typeIInnerMaximalSum a P X H := by
    apply Finset.sum_nonneg
    intro a ha
    have hM : 0 ≤ typeIInnerMaximalSum a P X H := by
      dsimp [typeIInnerMaximalSum]
      exact progressionMaximalSum_nonneg _ _
    exact mul_nonneg (norm_nonneg _) hM
  have htargetNumerator :
      (δ * (ρ * H)) ^ 2 ≤
        ((2 * A) / δ) *
          ∑ a ∈ S, (typeIInnerMaximalSum a P X H) ^ 2 := by
    calc
      _ ≤
          (∑ a ∈ S,
            ‖complexPositiveIntegerNatExtension α a‖ *
              typeIInnerMaximalSum a P X H) ^ 2 := by
        have hleftNonneg : 0 ≤ δ * (ρ * H) := by positivity
        exact (sq_le_sq₀ hleftNonneg hsumNonneg).2 hweightedLower
      _ ≤
          (∑ a ∈ S,
            ‖complexPositiveIntegerNatExtension α a‖ ^ 2) *
            ∑ a ∈ S, (typeIInnerMaximalSum a P X H) ^ 2 := hCauchy'
      _ ≤ _ := mul_le_mul_of_nonneg_right hAlphaSquare hMsumNonneg
  have htargetNumerator' :
      (δ * (ρ * H)) ^ 2 ≤
        (∑ a ∈ S, (typeIInnerMaximalSum a P X H) ^ 2) * ((2 * A) / δ) := by
    calc
      _ ≤ ((2 * A) / δ) *
            ∑ a ∈ S, (typeIInnerMaximalSum a P X H) ^ 2 := htargetNumerator
      _ = _ := by ring
  have hdiv := (div_le_iff₀ hdenom).2 htargetNumerator'
  have hidentity :
      ((δ * (ρ * H)) ^ 2) / ((2 * A) / δ) =
        (δ ^ 3 * ρ ^ 2 * H ^ 2) / (2 * A) := by
    field_simp
  rw [hidentity] at hdiv
  exact hdiv

/-- The low maximal sums cannot account for more than a quarter of the
Cauchy--Schwarz lower bound; therefore at least `δ³ρ² A/16` indices satisfy
the source threshold `Mₐ ≥ (δ²ρ/4) H/A`. -/
private theorem typeI_block_many_large_maxima
    (δ H A ρ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hH : 0 < H) (hA : 0 < A) (hρ : 0 < ρ)
    (S : Finset ℕ) (hScard : (S.card : ℝ) ≤ 2 * A)
    (M : ℕ → ℝ) (hMnonneg : ∀ a ∈ S, 0 ≤ M a)
    (hMupper : ∀ a ∈ S, M a ≤ 2 * H / A)
    (hMsquare : (δ ^ 3 * ρ ^ 2 * H ^ 2) / (2 * A) ≤
      ∑ a ∈ S, (M a) ^ 2) :
    (δ ^ 3 * ρ ^ 2 / 16) * A ≤
      ((S.filter fun a => (δ ^ 2 * ρ / 4) * (H / A) ≤ M a).card : ℝ) := by
  classical
  let threshold := (δ ^ 2 * ρ / 4) * (H / A)
  let large := S.filter fun a => threshold ≤ M a
  let small := S.filter fun a => M a < threshold
  have hthresholdPos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hAne : A ≠ 0 := ne_of_gt hA
  have hδcube : 0 ≤ δ ^ 3 := by positivity
  have hδle2 : δ ≤ 2 := by linarith
  have hδcubeMul : δ ^ 3 * δ ≤ δ ^ 3 * 2 :=
    mul_le_mul_of_nonneg_left hδle2 hδcube
  have hlowCoeff : δ ^ 4 / 8 ≤ δ ^ 3 / 4 := by
    nlinarith [hδcubeMul]
  have hcommonNonneg : 0 ≤ ρ ^ 2 * H ^ 2 / A := by positivity
  have hlowCompare :
      (δ ^ 4 * ρ ^ 2 * H ^ 2) / (8 * A) ≤
        (δ ^ 3 * ρ ^ 2 * H ^ 2) / (4 * A) := by
    calc
      (δ ^ 4 * ρ ^ 2 * H ^ 2) / (8 * A) =
          (δ ^ 4 / 8) * (ρ ^ 2 * H ^ 2 / A) := by
            field_simp
      _ ≤ (δ ^ 3 / 4) * (ρ ^ 2 * H ^ 2 / A) :=
        mul_le_mul_of_nonneg_right hlowCoeff hcommonNonneg
      _ = (δ ^ 3 * ρ ^ 2 * H ^ 2) / (4 * A) := by
            field_simp
  have hlowSum :
      (∑ a ∈ small, (M a) ^ 2) ≤
        (δ ^ 3 * ρ ^ 2 * H ^ 2) / (4 * A) := by
    have hterm : ∀ a ∈ small, (M a) ^ 2 ≤ threshold ^ 2 := by
      intro a ha
      have hlt := (Finset.mem_filter.mp ha).2
      exact sq_le_sq₀ (hMnonneg a ((Finset.mem_filter.mp ha).1))
        hthresholdPos.le |>.2 hlt.le
    have hconstant :
        (∑ a ∈ small, threshold ^ 2) = (small.card : ℝ) * threshold ^ 2 := by
      simp [Finset.sum_const]
    have hcardSmall : (small.card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hsumBound :
        (∑ a ∈ small, (M a) ^ 2) ≤ (2 * A) * threshold ^ 2 := by
      calc
        _ ≤ ∑ a ∈ small, threshold ^ 2 := Finset.sum_le_sum hterm
        _ = (small.card : ℝ) * threshold ^ 2 := hconstant
        _ ≤ (S.card : ℝ) * threshold ^ 2 :=
          mul_le_mul_of_nonneg_right hcardSmall (sq_nonneg threshold)
        _ ≤ (2 * A) * threshold ^ 2 :=
          mul_le_mul_of_nonneg_right hScard (sq_nonneg threshold)
    have hscale : (2 * A) * threshold ^ 2 =
        (δ ^ 4 * ρ ^ 2 * H ^ 2) / (8 * A) := by
      dsimp [threshold]
      field_simp
      ring
    calc
      _ ≤ (2 * A) * threshold ^ 2 := hsumBound
      _ = (δ ^ 4 * ρ ^ 2 * H ^ 2) / (8 * A) := hscale
      _ ≤ _ := hlowCompare
  have hsplit :
      (∑ a ∈ S, (M a) ^ 2) =
        (∑ a ∈ large, (M a) ^ 2) +
          (∑ a ∈ small, (M a) ^ 2) := by
    simpa only [large, small, not_le] using
      (Finset.sum_filter_add_sum_filter_not S
        (fun a => threshold ≤ M a) (fun a => (M a) ^ 2)).symm
  let C := (δ ^ 3 * ρ ^ 2 * H ^ 2) / (4 * A)
  have hratio : (δ ^ 3 * ρ ^ 2 * H ^ 2) / (2 * A) = 2 * C := by
    dsimp [C]
    field_simp [hAne]
    <;> ring
  have hlowSumC : (∑ a ∈ small, (M a) ^ 2) ≤ C := by
    simpa [C] using hlowSum
  have hlargeLowerC : C ≤ ∑ a ∈ large, (M a) ^ 2 := by
    rw [hsplit] at hMsquare
    rw [hratio] at hMsquare
    linarith [hMsquare, hlowSumC]
  have hlargeLower :
      (δ ^ 3 * ρ ^ 2 * H ^ 2) / (4 * A) ≤
        ∑ a ∈ large, (M a) ^ 2 := by
    simpa [C] using hlargeLowerC
  have hlargeUpper :
      (∑ a ∈ large, (M a) ^ 2) ≤
        (large.card : ℝ) * (2 * H / A) ^ 2 := by
    calc
      _ ≤ ∑ a ∈ large, (2 * H / A) ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hMpos : 0 ≤ M a := hMnonneg a ((Finset.mem_filter.mp ha).1)
        exact (sq_le_sq₀ hMpos (by positivity)).2
          (hMupper a ((Finset.mem_filter.mp ha).1))
      _ = (large.card : ℝ) * (2 * H / A) ^ 2 := by simp [Finset.sum_const]
  have hfactorPos : 0 < (2 * H / A) ^ 2 := by positivity
  have hfactorId :
      ((δ ^ 3 * ρ ^ 2 / 16) * A) * (2 * H / A) ^ 2 =
        (δ ^ 3 * ρ ^ 2 * H ^ 2) / (4 * A) := by
    field_simp
    ring
  have hproduct :
      ((δ ^ 3 * ρ ^ 2 / 16) * A) * (2 * H / A) ^ 2 ≤
        (large.card : ℝ) * (2 * H / A) ^ 2 := by
    calc
      _ = (δ ^ 3 * ρ ^ 2 * H ^ 2) / (4 * A) := hfactorId
      _ ≤ ∑ a ∈ large, (M a) ^ 2 := hlargeLower
      _ ≤ _ := hlargeUpper
  have hcount : (δ ^ 3 * ρ ^ 2 / 16) * A ≤ (large.card : ℝ) :=
    le_of_mul_le_mul_right hproduct hfactorPos
  simpa [large, threshold] using hcount

/-- The scale attached to the exceptional first dyadic block and to the
subsequent powers-of-two blocks. -/
def typeIDyadicScale (k : ℕ) : ℝ :=
  if k = 0 then 1 / 2 else ((2 ^ (k - 1) : ℕ) : ℝ)

/-- A finite dyadic block, intersected with the range of possible first
Dirichlet factors. -/
def typeIDyadicBlock (N k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun a =>
    typeIDyadicScale k < (a : ℝ) ∧ (a : ℝ) ≤ 2 * typeIDyadicScale k

/-- A dyadic block has at most `2A` natural indices when its upper endpoint
is `2A`. -/
theorem typeIDyadicBlock_card_le (N k : ℕ) :
    ((typeIDyadicBlock N k).card : ℝ) ≤ 2 * typeIDyadicScale k := by
  classical
  let A := typeIDyadicScale k
  let S := typeIDyadicBlock N k
  let T := Finset.Icc 1 (Nat.floor (2 * A))
  have hsub : S ⊆ T := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨haN, haBlock⟩
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp haN).1,
      Nat.le_floor (by simpa [A] using haBlock.2)⟩
  have hTcard : (T.card : ℝ) = (Nat.floor (2 * A) : ℝ) := by
    simp [T, Nat.card_Icc]
  have hAnonneg : 0 ≤ A := by
    dsimp [A, typeIDyadicScale]
    split <;> positivity
  calc
    (S.card : ℝ) ≤ (T.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = (Nat.floor (2 * A) : ℝ) := hTcard
    _ ≤ 2 * A := Nat.floor_le (by positivity)
    _ = 2 * typeIDyadicScale k := by rfl

/-- The index range contains the initial half-scale block and one block for
each power of two through `N`. -/
def typeIDyadicIndices (N : ℕ) : Finset ℕ :=
  Finset.Icc 0 (Nat.log2 N + 1)

/-- Every positive integer through `N` lies in one of the first `log₂ N + 2`
blocks, including the half-scale block containing `a = 1`. -/
theorem typeIDyadicBlock_cover (N a : ℕ) (ha : a ∈ Finset.Icc 1 N) :
    ∃ k ∈ typeIDyadicIndices N, a ∈ typeIDyadicBlock N k := by
  have haBounds := Finset.mem_Icc.mp ha
  by_cases haone : a = 1
  · refine ⟨0, Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, ?_⟩
    · omega
    · rw [typeIDyadicBlock, Finset.mem_filter]
      refine ⟨ha, ?_⟩
      norm_num [typeIDyadicScale, haone]
  · have haTwo : 2 ≤ a := by omega
    have hprev : a - 1 ≤ N := (Nat.sub_le _ _).trans haBounds.2
    let m := Nat.log 2 (a - 1)
    let k := m + 1
    have hmLower : 2 ^ m ≤ a - 1 := by
      dsimp [m]
      exact Nat.pow_log_le_self 2 (by omega)
    have hmUpper : a - 1 < 2 ^ (m + 1) := by
      simpa [m] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) (a - 1)
    have hak : k ≤ Nat.log2 N + 1 := by
      dsimp [k, m]
      rw [Nat.log2_eq_log_two]
      exact Nat.add_le_add_right (Nat.log_mono_right hprev) 1
    refine ⟨k, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hak⟩, ?_⟩
    rw [typeIDyadicBlock, Finset.mem_filter]
    refine ⟨ha, ?_⟩
    have hkpos : k ≠ 0 := by dsimp [k]; omega
    have hscale : typeIDyadicScale k = ((2 ^ m : ℕ) : ℝ) := by
      simp [typeIDyadicScale, hkpos, k, m]
    have hdouble : 2 * ((2 ^ m : ℕ) : ℝ) =
        ((2 ^ (m + 1) : ℕ) : ℝ) := by
      push_cast
      rw [pow_succ]
      ring
    constructor
    · have hcast : ((2 ^ m : ℕ) : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by
        exact_mod_cast hmLower
      have hsub : ((a - 1 : ℕ) : ℝ) + 1 = (a : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ a)
      rw [hscale]
      linarith
    · have hsub : ((a - 1 : ℕ) : ℝ) + 1 = (a : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ a)
      have hpowReal : (a : ℝ) ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show a ≤ 2 ^ (m + 1) by omega)
      rw [hscale, hdouble]
      exact hpowReal

/-- The number of dyadic blocks is at most `4 log X`, and the Type I
smallness hypothesis makes this strictly less than `4 δ⁻¹`. -/
theorem typeIDyadicIndices_card_bound
    (X δ : ℝ) (hX : 3 ≤ X) (hδ : 0 < δ)
    (hδlog : δ < (Real.log X)⁻¹) :
    (typeIDyadicIndices (Nat.floor X)).card < 4 * δ⁻¹ := by
  have hN : 3 ≤ Nat.floor X := by
    exact Nat.le_floor hX
  have hNne : Nat.floor X ≠ 0 := by omega
  have hpowNat : 2 ^ Nat.log2 (Nat.floor X) ≤ Nat.floor X := by
    simpa only [Nat.log2_eq_log_two] using
      Nat.pow_log_le_self 2 hNne
  have hNle : ((Nat.floor X : ℕ) : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hpowReal : (2 : ℝ) ^ Nat.log2 (Nat.floor X) ≤ X := by
    calc
      (2 : ℝ) ^ Nat.log2 (Nat.floor X) =
          ((2 ^ Nat.log2 (Nat.floor X) : ℕ) : ℝ) := by norm_cast
      _ ≤ (Nat.floor X : ℝ) := by exact_mod_cast hpowNat
      _ ≤ X := hNle
  have hlogXpos : 0 < Real.log X := by
    have hlog3 : 1 ≤ Real.log 3 := by
      exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
        Real.exp_one_lt_three |>.le
    have hlogmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX
    linarith
  have hlogTwo : (2 / 3 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogPow : (Nat.log2 (Nat.floor X) : ℝ) * Real.log 2 ≤
      Real.log X := by
    calc
      (Nat.log2 (Nat.floor X) : ℝ) * Real.log 2 =
          Real.log ((2 : ℝ) ^ Nat.log2 (Nat.floor X)) := by
            rw [Real.log_pow]
      _ ≤ Real.log X := Real.log_le_log (by positivity) hpowReal
  have hlogNat : (Nat.log2 (Nat.floor X) : ℝ) ≤
      (3 / 2) * Real.log X := by
    have hnonneg : 0 ≤ (Nat.log2 (Nat.floor X) : ℝ) := by positivity
    nlinarith [hlogPow, hlogTwo, hnonneg]
  have hcardEq : (typeIDyadicIndices (Nat.floor X)).card =
      Nat.log2 (Nat.floor X) + 2 := by
    simp [typeIDyadicIndices, Nat.card_Icc]
  have hlogLarge : 1 ≤ Real.log X := by
    have hlog3 : 1 ≤ Real.log 3 := by
      exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
        Real.exp_one_lt_three |>.le
    have hlogmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX
    linarith
  have hcount :
      ((typeIDyadicIndices (Nat.floor X)).card : ℝ) ≤ 4 * Real.log X := by
    rw [hcardEq]
    push_cast
    nlinarith [hlogNat, hlogLarge]
  have hδprod : δ * Real.log X < 1 := by
    apply (lt_div_iff₀ hlogXpos).mp
    simpa [one_div] using hδlog
  have hloglt : Real.log X < δ⁻¹ := by
    have hloglt' : Real.log X < 1 / δ :=
      (lt_div_iff₀ hδ).2 (by nlinarith [hδprod])
    simpa [one_div] using hloglt'
  change ((typeIDyadicIndices (Nat.floor X)).card : ℝ) < 4 * δ⁻¹
  calc
    _ ≤ 4 * Real.log X := hcount
    _ < 4 * δ⁻¹ := by nlinarith

/-- Nonnegative mass on `[1,N]` is bounded by the sum of its masses over the
covering dyadic blocks.  Overlap at the endpoints is harmless. -/
theorem typeI_sum_le_dyadic_block_sums
    (N : ℕ) (g : ℕ → ℝ)
    (hg : ∀ a ∈ Finset.Icc 1 N, 0 ≤ g a) :
    (∑ a ∈ Finset.Icc 1 N, g a) ≤
      ∑ k ∈ typeIDyadicIndices N,
        ∑ a ∈ typeIDyadicBlock N k, g a := by
  calc
    (∑ a ∈ Finset.Icc 1 N, g a) ≤
        ∑ a ∈ Finset.Icc 1 N,
          ∑ k ∈ typeIDyadicIndices N,
            if a ∈ typeIDyadicBlock N k then g a else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨k, hk, hak⟩ := typeIDyadicBlock_cover N a ha
      calc
        g a = (if a ∈ typeIDyadicBlock N k then g a else 0) := by simp [hak]
        _ ≤ ∑ j ∈ typeIDyadicIndices N,
            if a ∈ typeIDyadicBlock N j then g a else 0 :=
          Finset.single_le_sum
            (f := fun j => if a ∈ typeIDyadicBlock N j then g a else 0)
            (fun j hj => by
              by_cases hmem : a ∈ typeIDyadicBlock N j
              · simp [hmem, hg a ha]
              · simp [hmem]) hk
    _ = ∑ k ∈ typeIDyadicIndices N,
        ∑ a ∈ Finset.Icc 1 N,
          if a ∈ typeIDyadicBlock N k then g a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ typeIDyadicIndices N,
        ∑ a ∈ typeIDyadicBlock N k, g a := by
      apply Finset.sum_congr rfl
      intro k hk
      change
        (∑ a ∈ Finset.Icc 1 N,
          if a ∈ (Finset.Icc 1 N).filter
              (fun (a : ℕ) => typeIDyadicScale k < (a : ℝ) ∧
                (a : ℝ) ≤ 2 * typeIDyadicScale k) then g a else 0) =
          ∑ a ∈ (Finset.Icc 1 N).filter
              (fun (a : ℕ) => typeIDyadicScale k < (a : ℝ) ∧
                (a : ℝ) ≤ 2 * typeIDyadicScale k), g a
      rw [← Finset.sum_filter]
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      simp [ha]

/-- The total mass on `[1,N]` forces one dyadic block to carry at least its
average over the exact finite block count. -/
private theorem exists_typeI_dyadic_block_average
    (N : ℕ) (δ H : ℝ) (hδ : 0 < δ) (hH : 0 < H)
    (hcardBound : (typeIDyadicIndices N).card < 4 * δ⁻¹)
    (g : ℕ → ℝ)
    (hg : ∀ a ∈ Finset.Icc 1 N, 0 ≤ g a)
    (hTotal : δ * H ≤ ∑ a ∈ Finset.Icc 1 N, g a) :
    ∃ k ∈ typeIDyadicIndices N,
      (δ ^ 2 / 4) * H ≤ ∑ a ∈ typeIDyadicBlock N k, g a := by
  classical
  let K := typeIDyadicIndices N
  let blockMass := fun k => ∑ a ∈ typeIDyadicBlock N k, g a
  have hKne : K.Nonempty := by
    refine ⟨0, ?_⟩
    simp [K, typeIDyadicIndices]
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image K blockMass hKne
  have hcover := typeI_sum_le_dyadic_block_sums N g hg
  have hblocks :
      (∑ j ∈ K, blockMass j) ≤ (K.card : ℝ) * blockMass k := by
    calc
      (∑ j ∈ K, blockMass j) ≤ ∑ j ∈ K, blockMass k := by
        apply Finset.sum_le_sum
        intro j hj
        exact hmax j hj
      _ = (K.card : ℝ) * blockMass k := by simp [Finset.sum_const]
  have hcardPosNat : 0 < K.card := Finset.card_pos.mpr hKne
  have hcardPos : 0 < (K.card : ℝ) := by exact_mod_cast hcardPosNat
  have hsmall : (δ ^ 2 / 4 * H) * (K.card : ℝ) < δ * H := by
    have hcardLe : (K.card : ℝ) * δ < 4 := by
      have hbound : (K.card : ℝ) < 4 / δ := by
        simpa [K, div_eq_mul_inv] using hcardBound
      nlinarith [((lt_div_iff₀ hδ).mp hbound)]
    have hfactor : ((K.card : ℝ) * δ) / 4 < 1 := by
      apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      nlinarith [hcardLe]
    have hδH : 0 < δ * H := mul_pos hδ hH
    have heq : (δ ^ 2 / 4 * H) * (K.card : ℝ) =
        (δ * H) * (((K.card : ℝ) * δ) / 4) := by ring
    rw [heq]
    nlinarith
  have hscaled : (δ ^ 2 / 4 * H) * (K.card : ℝ) ≤
      (K.card : ℝ) * blockMass k := by
    calc
      _ ≤ δ * H := hsmall.le
      _ ≤ ∑ a ∈ Finset.Icc 1 N, g a := hTotal
      _ ≤ ∑ j ∈ K, blockMass j := by simpa [K, blockMass] using hcover
      _ ≤ _ := hblocks
  have hresult : (δ ^ 2 / 4) * H ≤ blockMass k := by
    apply le_of_mul_le_mul_left ?_ hcardPos
    nlinarith [hscaled]
  exact ⟨k, hk, by simpa [blockMass] using hresult⟩

/-- Scalar type I inverse estimate with the exact approved inverse budget.
The second branch records both the binomial seminorm and all centered
monomial coefficient bounds. -/
theorem typeIInverse
    (d : ℕ) (hd : 1 ≤ d) (X H δ A_I : ℝ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hδ : 0 < δ)
    (hδsmall : δ < min (1 / 2) ((Real.log X)⁻¹))
    (f : ComplexPositiveIntegerFunction)
    (hf : typeIFunction δ A_I f)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hlarge : δ * H ≤ typeIScalarPhaseCorrelation f P X H) :
    H ≤ inverseBoundI d δ⁻¹ * A_I ∨
      ∃ r : ℤ, 1 ≤ r ∧
        (r : ℝ) ≤ inverseBoundI d δ⁻¹ ∧
        polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
          (Int.floor X) H ≤ inverseBoundI d δ⁻¹ ∧
        ∀ j, 1 ≤ j → j ≤ d →
          H ^ j * realDistanceToIntegers
            ((r : ℝ) * (phaseCenteredAt P (Int.floor X)).coeff j) ≤
              inverseBoundI d δ⁻¹ := by
  classical
  rcases hf with ⟨_, _, hAI, α, β, q, hq, hconv, hsupp,
    hMoment, hqone, hqbound, hTV⟩
  have hδhalf : δ < 1 / 2 := lt_of_lt_of_le hδsmall (min_le_left _ _)
  have hδlog : δ < (Real.log X)⁻¹ := lt_of_lt_of_le hδsmall (min_le_right _ _)
  have hXnonneg : 0 ≤ X := by linarith
  have hHpos : 0 < H := by linarith
  have hAIpos : 0 < A_I := by linarith
  have hδinv : 2 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hδ).2
    nlinarith [hδhalf]
  have hIgefour : 4 ≤ inverseBoundI d δ⁻¹ :=
    inverseBoundI_ge_four d hd δ⁻¹ hδinv
  by_cases hshort : H ≤ inverseBoundI d δ⁻¹ * A_I
  · exact Or.inl hshort
  · have hlong : inverseBoundI d δ⁻¹ * A_I < H := lt_of_not_ge hshort
    have hfourAI : 4 * A_I < H := by
      have hscale : 4 * A_I ≤ inverseBoundI d δ⁻¹ * A_I :=
        mul_le_mul_of_nonneg_right hIgefour hAIpos.le
      linarith
    have hAIltX : A_I < X := by
      calc
        A_I < 4 * A_I := by nlinarith [hAIpos]
        _ < H := hfourAI
        _ ≤ X := hHX
    have hlarge' :
        δ * H ≤ ‖typeIScalarPhaseSum
          (complexPositiveDirichletConvolution α β) P X H‖ := by
      simpa [typeIScalarPhaseCorrelation, hconv] using hlarge
    have hRawFloor :
        δ * H ≤ ∑ a ∈ Finset.Icc 1 (Nat.floor X),
          typeIInnerWeightedTerm α β P X H a := by
      calc
        δ * H ≤ ‖typeIScalarPhaseSum
            (complexPositiveDirichletConvolution α β) P X H‖ := hlarge'
        _ ≤ ∑ a ∈ Finset.Icc 1 (Nat.floor (X + H)),
            typeIInnerWeightedTerm α β P X H a := by
              simpa [typeIInnerWeightedTerm] using
                typeIScalarPhaseSum_norm_le_weightedInnerSums α β P X H
        _ = ∑ a ∈ Finset.Icc 1 (Nat.floor X),
            typeIInnerWeightedTerm α β P X H a :=
              typeIInnerWeightedSum_eq_floorX α β P X H A_I
                (by linarith [hH]) hAIltX hsupp
    have hblockCount := typeIDyadicIndices_card_bound X δ hX hδ hδlog
    let g : ℕ → ℝ := fun a => typeIInnerWeightedTerm α β P X H a
    have hg : ∀ a ∈ Finset.Icc 1 (Nat.floor X), 0 ≤ g a := by
      intro a ha
      dsimp [g, typeIInnerWeightedTerm]
      positivity
    obtain ⟨k, hk, hblockRaw⟩ :=
      exists_typeI_dyadic_block_average (Nat.floor X) δ H hδ hHpos
        hblockCount g hg hRawFloor
    let ρ : ℝ := δ ^ 2 / 4
    let A : ℝ := typeIDyadicScale k
    let S : Finset ℕ := typeIDyadicBlock (Nat.floor X) k
    have hAhalf : 1 / 2 ≤ A := by
      dsimp [A, typeIDyadicScale]
      split
      · norm_num
      · have hpow :
            (1 : ℝ) ≤ ((2 ^ (k - 1) : ℕ) : ℝ) := by
          exact_mod_cast (Nat.one_le_pow (k - 1) 2 (by norm_num))
        nlinarith [hpow]
    have hApos : 0 < A := by linarith
    have hρpos : 0 < ρ := by dsimp [ρ]; positivity
    have hSbounds : ∀ a ∈ S,
        A < (a : ℝ) ∧ (a : ℝ) ≤ 2 * A := by
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨_, hbounds⟩
      simpa [S, A, typeIDyadicBlock] using hbounds
    have hRaw : ρ * H ≤
        ∑ a ∈ S, typeIInnerWeightedTerm α β P X H a := by
      simpa [ρ, S, g] using hblockRaw
    have hMsquare := typeI_block_maxima_square_sum_lower α β P X H δ A ρ
      hXnonneg hHpos hδ hAhalf hρpos hMoment q hq hTV S hSbounds hRaw
    have hScard : (S.card : ℝ) ≤ 2 * A := by
      simpa [S, A] using typeIDyadicBlock_card_le (Nat.floor X) k
    have hA_lt_AI : A < A_I := by
      by_contra hnot
      have hAIleA : A_I ≤ A := le_of_not_gt hnot
      have htermzero : ∀ a ∈ S,
          typeIInnerWeightedTerm α β P X H a = 0 := by
        intro a ha
        have haPosR : 0 < (a : ℝ) :=
          lt_trans hApos (hSbounds a ha).1
        have haPos : 0 < a := by exact_mod_cast haPosR
        have hαzero : complexPositiveIntegerNatExtension α a = 0 := by
          by_contra hαne
          have hαne' : α ⟨a, haPos⟩ ≠ 0 := by
            simpa [complexPositiveIntegerNatExtension, haPos] using hαne
          have hαsupport := hsupp ⟨a, haPos⟩ hαne'
          have haAI : A_I < (a : ℝ) :=
            lt_of_le_of_lt hAIleA (hSbounds a ha).1
          linarith
        simp [typeIInnerWeightedTerm, hαzero]
      have hsumzero :
          (∑ a ∈ S, typeIInnerWeightedTerm α β P X H a) = 0 :=
        Finset.sum_eq_zero htermzero
      rw [hsumzero] at hRaw
      have hpositive := mul_pos hρpos hHpos
      linarith
    let M : ℕ → ℝ := fun a => typeIInnerMaximalSum a P X H
    have hMnonneg : ∀ a ∈ S, 0 ≤ M a := by
      intro a ha
      dsimp [M, typeIInnerMaximalSum]
      exact progressionMaximalSum_nonneg _ _
    have hMupper : ∀ a ∈ S, M a ≤ 2 * H / A := by
      intro a ha
      have haPosR : 0 < (a : ℝ) :=
        lt_trans hApos (hSbounds a ha).1
      have haPos : 0 < a := by exact_mod_cast haPosR
      have hHgeA : (a : ℝ) ≤ H := by
        have haUpper := (hSbounds a ha).2
        linarith [hA_lt_AI, hfourAI, haUpper]
      have hHdiv : 1 ≤ H / (a : ℝ) := by
        apply (le_div_iff₀ haPosR).2
        simpa using hHgeA
      simpa [M] using
        typeIInnerMaximalSum_le_two_H_over_A a haPos P X H A
          hXnonneg hHpos hApos (hSbounds a ha).1 hHdiv
    have hδone : δ ≤ 1 := by linarith [hδhalf]
    have hmany := typeI_block_many_large_maxima δ H A ρ hδ hδone
      hHpos hApos hρpos S hScard M hMnonneg hMupper hMsquare
    let κ : ℝ := δ ^ 4 / 16
    let η : ℝ := δ ^ 7 / 256
    let Sgood : Finset ℕ := S.filter fun a =>
      (δ ^ 2 * ρ / 4) * (H / A) ≤ M a
    have hκeq : δ ^ 2 * ρ / 4 = κ := by dsimp [ρ, κ]; ring
    have hηeq : δ ^ 3 * ρ ^ 2 / 16 = η := by dsimp [ρ, η]; ring
    have hSgoodCard : η * A ≤ (Sgood.card : ℝ) := by
      have hmany' : (δ ^ 3 * ρ ^ 2 / 16) * A ≤ (Sgood.card : ℝ) := by
        simpa [Sgood] using hmany
      rw [← hηeq]
      exact hmany'
    have hηpos : 0 < η := by dsimp [η]; positivity
    have hηhalf : η < 1 / 2 := by
      have hδpow : δ ^ 7 ≤ (1 / 2 : ℝ) ^ 7 :=
        pow_le_pow_left₀ (by positivity) hδhalf.le 7
      dsimp [η]
      norm_num at hδpow ⊢
      nlinarith
    have hηinv : η⁻¹ = 256 * δ⁻¹ ^ 7 := by
      dsimp [η]
      field_simp [ne_of_gt hδ]
      <;> ring
    have hηinv2 : 2 ≤ η⁻¹ := by
      rw [hηinv]
      have hpow : 1 ≤ δ⁻¹ ^ 7 := one_le_pow₀ (by linarith [hδinv])
      calc
        2 ≤ 256 := by norm_num
        _ ≤ 256 * δ⁻¹ ^ 7 := by
          simpa using mul_le_mul_of_nonneg_left hpow
            (show (0 : ℝ) ≤ 256 by norm_num)
    let B : ℝ := inverseBoundG d (16 * δ⁻¹ ^ 4)
    have hB : 1 ≤ B := by
      have hpow : 1 ≤ δ⁻¹ ^ 4 := one_le_pow₀ (by linarith [hδinv])
      have hx : 2 ≤ 16 * δ⁻¹ ^ 4 := by
        calc
          2 ≤ 16 := by norm_num
          _ ≤ 16 * δ⁻¹ ^ 4 := by
            simpa using mul_le_mul_of_nonneg_left hpow
              (show (0 : ℝ) ≤ 16 by norm_num)
      simpa [B] using inverseBoundG_ge_one d (16 * δ⁻¹ ^ 4) hx
    have hSgoodbounds : ∀ a ∈ Sgood,
        A < (a : ℝ) ∧ (a : ℝ) ≤ 2 * A := by
      intro a ha
      exact hSbounds a (Finset.mem_filter.mp ha).1
    have hdata : ∀ a ∈ Sgood, ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ B ∧
        ∀ j, 1 ≤ j → j ≤ d →
          (H / (a : ℝ)) ^ j * realDistanceToIntegers
            ((r : ℝ) * (phaseDilatedAt P a
              (Int.floor (X / (a : ℝ)))).coeff j) ≤ B := by
      intro a haGood
      have hhigh := (Finset.mem_filter.mp haGood).2
      have haPosR : 0 < (a : ℝ) :=
        lt_trans hApos (hSbounds a (Finset.mem_filter.mp haGood).1).1
      have haPos : 0 < a := by exact_mod_cast haPosR
      have hHgeA : (a : ℝ) ≤ H := by
        have haUpper := (hSbounds a (Finset.mem_filter.mp haGood).1).2
        linarith [hA_lt_AI, hfourAI, haUpper]
      have hHdiv : 1 ≤ H / (a : ℝ) := by
        apply (le_div_iff₀ haPosR).2
        simpa using hHgeA
      have hthresholdEq : δ ^ 4 / 16 = δ ^ 2 * ρ / 4 := by
        dsimp [ρ]
        ring
      have hlocalThreshold : (δ ^ 4 / 16) * (H / A) ≤ M a := by
        calc
          (δ ^ 4 / 16) * (H / A) =
              (δ ^ 2 * ρ / 4) * (H / A) := by rw [hthresholdEq]
          _ ≤ M a := hhigh
      let I := typeIInnerInterval a X H
      let phase : ℤ → ℂ := fun n =>
        unitFrequencyPhase (P.eval (((a : ℤ) * n : ℤ) : ℝ))
      have hphaseEq :
          (fun n : {n : ℤ // n ∈ I.points} => phase n.1) =
            typeIInnerPhaseFunction a P I := by
        funext n
        rfl
      have hmaxle : (δ ^ 4 / 16) * (H / A) ≤
          progressionMaximalSum I (fun n => phase n.1) := by
        change (δ ^ 4 / 16) * (H / A) ≤
          progressionMaximalSum I (fun n => phase n.1)
        rw [hphaseEq]
        simpa [I, M, typeIInnerMaximalSum] using hlocalThreshold
      obtain ⟨J, hJsubset, hJAP, hJlarge⟩ :=
        exists_progression_sum_ge_of_le_maximal I phase
          ((δ ^ 4 / 16) * (H / A)) hmaxle
      have hJsubsetReal : ∀ n ∈ J,
          X / (a : ℝ) < (n : ℝ) ∧
            (n : ℝ) ≤ X / (a : ℝ) + H / (a : ℝ) := by
        intro n hn
        have hbounds :=
          (typeIInnerInterval_mem_iff a haPos X H hXnonneg
            (by linarith [hH]) n).mp (hJsubset hn)
        have hdivAdd : (X + H) / (a : ℝ) =
            X / (a : ℝ) + H / (a : ℝ) := by
          field_simp [ne_of_gt haPosR]
          <;> ring
        exact ⟨hbounds.1, by rw [hdivAdd] at hbounds; exact hbounds.2⟩
      have hlocal := typeI_local_progression_inverse hd δ H A X
        hδ hδhalf hHpos hApos a haPos (hSgoodbounds a haGood).1
        hHdiv P hP J hJAP hJsubsetReal hJlarge
      rcases hlocal with ⟨r, hrpos, hrbound, hcoeff⟩
      refine ⟨r, hrpos, ?_, ?_⟩
      · simpa [B] using hrbound
      · intro j hj hjd
        simpa [B] using hcoeff j hj hjd
    have hconcat := concatenateDilatedPhases hd hAhalf hH hB
      hηpos hηhalf P hP Sgood hSgoodbounds hSgoodCard hdata
    have hIeval : inverseBoundI d δ⁻¹ =
        (inverseBoundEValue d : ℝ) * inverseBoundV d B η⁻¹ := by
      rw [inverseBoundI_eval, hηinv]
    have hE : 1 ≤ (inverseBoundEValue d : ℝ) := by
      exact_mod_cast inverseBoundE_ge_one d
    have hVnonneg : 0 ≤ inverseBoundV d B η⁻¹ := by
      have hVfour := inverseBoundV_ge_four d hd B η⁻¹ hB hηinv2
      linarith
    have hVleI : inverseBoundV d B η⁻¹ ≤ inverseBoundI d δ⁻¹ := by
      rw [hIeval]
      calc
        inverseBoundV d B η⁻¹ = 1 * inverseBoundV d B η⁻¹ := by ring
        _ ≤ (inverseBoundEValue d : ℝ) * inverseBoundV d B η⁻¹ :=
          mul_le_mul_of_nonneg_right hE hVnonneg
    rcases hconcat with hVshort | ⟨r, hrpos, hrV, hmono⟩
    · have hVAI : inverseBoundV d B η⁻¹ * A ≤
          inverseBoundI d δ⁻¹ * A_I := by
        calc
          inverseBoundV d B η⁻¹ * A ≤ inverseBoundI d δ⁻¹ * A :=
            mul_le_mul_of_nonneg_right hVleI hApos.le
          _ ≤ inverseBoundI d δ⁻¹ * A_I :=
            mul_le_mul_of_nonneg_left hA_lt_AI.le (by linarith [hIgefour])
      exact False.elim (hshort (hVshort.trans hVAI))
    · let αcoef : ℕ → ℝ := fun j =>
        (phaseCenteredAt P (Int.floor X)).coeff j
      have hexp := phaseCenteredAt_monomial_expansion P hP (Int.floor X)
      have hmonoFin : ∀ j ∈ Finset.Icc 1 d,
          H ^ j * realDistanceToIntegers ((r : ℝ) * αcoef j) ≤
            inverseBoundV d B η⁻¹ := by
        intro j hj
        exact hmono j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
      have hbin := monomialToBinomialControl d hd (Int.floor X) H hH
        P αcoef (by simpa [αcoef] using hexp) r hrpos
        (inverseBoundV d B η⁻¹) hmonoFin
      have hbinI :
          polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
            (Int.floor X) H ≤ inverseBoundI d δ⁻¹ := by
        calc
          _ ≤ (inverseBoundEValue d : ℝ) * inverseBoundV d B η⁻¹ := hbin
          _ = inverseBoundI d δ⁻¹ := hIeval.symm
      refine Or.inr ⟨r, hrpos, ?_, hbinI, ?_⟩
      · exact le_trans hrV hVleI
      · intro j hj hjd
        exact le_trans (hmono j hj hjd) hVleI

/-- The explicit polynomial value at one giving the arithmetic Type I
constant `K_d^I = I_d(1)`. -/
def typeIArithmeticConstant (d : ℕ) : ℝ :=
  (((inverseBoundIPolynomial d).eval 1 : ℕ) : ℝ)

/-- The explicit arithmetic Type I exponent `c_d^I = deg I_d`. -/
def typeIArithmeticExponent (d : ℕ) : ℕ :=
  (inverseBoundIPolynomial d).natDegree

private theorem natPolynomial_eval_le_value_at_one_mul_power
    (p : Polynomial ℕ) (x : ℝ) (hx : 1 ≤ x) :
    p.eval₂ (Nat.castRingHom ℝ) x ≤
      ((p.eval 1 : ℕ) : ℝ) * x ^ p.natDegree := by
  let s := Finset.range (p.natDegree + 1)
  have hsum : (∑ i ∈ s, (p.coeff i : ℝ)) = ((p.eval 1 : ℕ) : ℝ) := by
    calc
      (∑ i ∈ s, (p.coeff i : ℝ)) = p.eval₂ (Nat.castRingHom ℝ) 1 := by
        symm
        dsimp [s]
        rw [Polynomial.eval₂_eq_sum_range]
        simp
      _ = ((p.eval 1 : ℕ) : ℝ) := by
        rw [Polynomial.eval₂_at_one]
        simp
  have hEvalX : p.eval₂ (Nat.castRingHom ℝ) x =
      ∑ i ∈ s, (p.coeff i : ℝ) * x ^ i := by
    dsimp [s]
    rw [Polynomial.eval₂_eq_sum_range]
    simp
  have hterms :
      (∑ i ∈ s, (p.coeff i : ℝ) * x ^ i) ≤
        ∑ i ∈ s, (p.coeff i : ℝ) * x ^ p.natDegree := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hiDeg : i ≤ p.natDegree := by
      dsimp [s] at hi
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact pow_le_pow_right₀ hx hiDeg
  calc
    p.eval₂ (Nat.castRingHom ℝ) x =
        ∑ i ∈ s, (p.coeff i : ℝ) * x ^ i := hEvalX
    _ ≤ ∑ i ∈ s, (p.coeff i : ℝ) * x ^ p.natDegree := hterms
    _ = (∑ i ∈ s, (p.coeff i : ℝ)) * x ^ p.natDegree := by
      rw [Finset.sum_mul]
    _ = ((p.eval 1 : ℕ) : ℝ) * x ^ p.natDegree := by rw [hsum]

/-- The explicit constant is the value of the approved inverse polynomial at
one. -/
theorem typeIArithmeticConstant_eq_inverseBoundI_one (d : ℕ) :
    typeIArithmeticConstant d = inverseBoundI d 1 := by
  simp [typeIArithmeticConstant, inverseBoundI, Polynomial.eval₂_at_one]

/-- The exact inverse budget is bounded by the source's explicit
`K_d^I (δ⁻¹)^{c_d^I}` arithmetic budget for every argument at least one. -/
theorem inverseBoundI_le_arithmeticBudget (d : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    inverseBoundI d x ≤
      typeIArithmeticConstant d * x ^ typeIArithmeticExponent d := by
  simpa [inverseBoundI, typeIArithmeticConstant,
    typeIArithmeticExponent] using
      natPolynomial_eval_le_value_at_one_mul_power
        (inverseBoundIPolynomial d) x hx

/-- The original arithmetic form of the Type I inverse clause, with the
explicit constants `K_d^I = I_d(1)` and `c_d^I = deg I_d`. -/
theorem typeIInverse_arithmetic
    (d : ℕ) (hd : 1 ≤ d) (X H δ A_I : ℝ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hδ : 0 < δ)
    (hδsmall : δ < min (1 / 2) ((Real.log X)⁻¹))
    (f : ComplexPositiveIntegerFunction)
    (hf : typeIFunction δ A_I f)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hlarge : δ * H ≤ typeIScalarPhaseCorrelation f P X H) :
    H ≤ typeIArithmeticConstant d * (δ⁻¹) ^ typeIArithmeticExponent d * A_I ∨
      ∃ r : ℤ, 1 ≤ r ∧
        (r : ℝ) ≤
          typeIArithmeticConstant d * (δ⁻¹) ^ typeIArithmeticExponent d ∧
        polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
          (Int.floor X) H ≤
            typeIArithmeticConstant d * (δ⁻¹) ^ typeIArithmeticExponent d ∧
        ∀ j, 1 ≤ j → j ≤ d →
          H ^ j * realDistanceToIntegers
            ((r : ℝ) * (phaseCenteredAt P (Int.floor X)).coeff j) ≤
              typeIArithmeticConstant d *
                (δ⁻¹) ^ typeIArithmeticExponent d := by
  have hδhalf : δ < 1 / 2 := lt_of_lt_of_le hδsmall (min_le_left _ _)
  have hδle : δ ≤ 1 := by linarith
  have hδinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδle
  have hAInonneg : 0 ≤ A_I := le_trans (by norm_num) hf.2.2.1
  have hbudget := inverseBoundI_le_arithmeticBudget d hδinv
  rcases typeIInverse d hd X H δ A_I hX hH hHX hδ hδsmall f hf P hP hlarge with
    hshort | ⟨r, hr, hrbound, hbin, hmono⟩
  · left
    calc
      H ≤ inverseBoundI d δ⁻¹ * A_I := hshort
      _ ≤
        (typeIArithmeticConstant d * (δ⁻¹) ^
          typeIArithmeticExponent d) * A_I :=
        mul_le_mul_of_nonneg_right hbudget hAInonneg
  · right
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · exact le_trans hrbound hbudget
    · exact le_trans hbin hbudget
    · intro j hj hjd
      exact le_trans (hmono j hj hjd) hbudget

end

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.finiteOrderedTotalVariation_le_orderedTotalVariation
#print axioms FractionalPrimes.Literature.Polynomial.typeIInverse
#print axioms FractionalPrimes.Literature.Polynomial.typeIInverse_arithmetic
