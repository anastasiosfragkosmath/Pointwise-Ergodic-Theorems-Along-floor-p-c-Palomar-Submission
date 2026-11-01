module

public import FractionalPrimes.Chebyshev
public import FractionalPrimes.Literature.Uniformity.VariationAbelMultiplier
public import FractionalPrimes.Literature.LongArithmetic.CramerResidueIntervalCount
public import FractionalPrimes.Literature.LongArithmetic.CramerResidueModelReduction
public import FractionalPrimes.Literature.LongArithmetic.NonunitVonMangoldtBound

/-!
# The unrestricted-modulus major-arc comparison task

This file records the exact optional comparison proposition
`lu:major-arcs-task` from `expanded-blueprint.tex:12778–12798`, matching
`blueprint-sources 2/literature-expansion/sections/uniformity.tex:25–45`.
The declaration `majorArcTask` is a proposition-valued task contract only;
it does not prove the major-arc estimate.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Uniformity

/-- The finite integer interval `(X, X + H]` with integer parameters. -/
def majorArcInterval (X H : ℕ) : FiniteIntegerInterval :=
  ⟨(X : ℤ) + 1, H⟩

/-- The source maximal progression sum on `(X, X + H]`, represented by the
existing finite-interval maximal seminorm. -/
def majorArcMaximalSum (X H : ℕ) (f : ℤ → ℂ) : ℝ :=
  progressionMaximalSum (majorArcInterval X H) (fun n => f n.1)

/-- The maximal progression sum restricted to one residue slice of the
major-arc interval. -/
def majorArcResidueMaximalSum (X H q a : ℕ) (f : ℤ → ℂ) : ℝ :=
  progressionMaximalSumOnFiniteSet
    ((majorArcInterval X H).points.filter
      (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]))
    (fun n => f n.1)

/-- The short-interval `Λ - Cr_X` coefficient on a positive natural index. -/
def majorArcLambdaMinusCramerNat (X : ℝ) (n : ℕ) : ℝ :=
  paperLambda (n : ℤ) - paperShortBlockCramerWeight X (n : ℤ)

/-- The integer interval used by the source is exactly the interval represented
by `majorArcInterval`, including both endpoint conventions. -/
theorem majorArcInterval_points_eq_Ioc (X H : ℕ) :
    (majorArcInterval X H).points =
      Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) := by
  classical
  ext n
  simp only [majorArcInterval, FiniteIntegerInterval.points,
    arithmeticProgressionPoints, Finset.mem_image, Finset.mem_range,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨j, hj, rfl⟩
    constructor <;> omega
  · intro hn
    refine ⟨n.toNat - X - 1, ?_, ?_⟩
    · omega
    · have hncast : ((n.toNat : ℕ) : ℤ) = n := by omega
      omega

/-- Exact residue geometry for the major-arc interval: every fixed residue
slice is an arithmetic progression with step exactly `q`. This reuses the
finite interval/residue representation from `lu:tv-calculus`. -/
theorem majorArcInterval_residueSlice_eq_progressionPoints
    (X H : ℕ) (c : ℤ) (q : ℕ) (hq : 0 < q) :
    ∃ a : ℤ, ∃ L : ℕ,
      arithmeticProgressionPoints a q hq L =
        ((majorArcInterval X H).points.filter
          (fun n => n ≡ c [ZMOD (q : ℤ)])) := by
  exact finiteInterval_residueFilter_eq_arithmeticProgressionPoints
    (majorArcInterval X H) c q hq

/-- Coefficient bookkeeping on the major-arc interval: a finite sum splits
exactly over the canonical residues modulo `q`. -/
theorem majorArcInterval_sum_eq_sum_residue_filters
    (X H q : ℕ) (hq : 0 < q) (F : ℤ → ℂ) :
    (∑ n ∈ (majorArcInterval X H).points, F n) =
      ∑ a ∈ Finset.range q,
        ∑ n ∈ (majorArcInterval X H).points.filter
          (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), F n := by
  exact sum_eq_sum_residue_filters (majorArcInterval X H).points q hq F

/-- The interval maximal sum is bounded by the sum of the maximal sums on
its residue slices modulo `q`. Each test progression is split into its
residue intersections; the intersections are progressions by the checked
finite intersection theorem. -/
theorem majorArcMaximalSum_le_sum_residueMaxima
    (X H q : ℕ) (hq : 0 < q) (F : ℤ → ℂ) :
    majorArcMaximalSum X H F ≤
      ∑ a ∈ Finset.range q, majorArcResidueMaximalSum X H q a F := by
  classical
  let I := majorArcInterval X H
  let fI : {n : ℤ // n ∈ I.points} → ℂ := fun n => F n.1
  change progressionMaximalSum I fI ≤ _
  unfold progressionMaximalSum
  apply Finset.sup'_le
  intro P hP
  have hPmem := Finset.mem_filter.mp hP
  have hPI : P ⊆ I.points := Finset.mem_powerset.mp hPmem.1
  have hPAP : isFiniteArithmeticProgression P := hPmem.2
  let Fext : ℤ → ℂ := fun n => extendByZero I.points fI n
  have hsplit := sum_eq_sum_residue_filters P q hq Fext
  have htriangle :
      ‖∑ n ∈ P, Fext n‖ ≤
        ∑ a ∈ Finset.range q,
          ‖∑ n ∈ P.filter
              (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), Fext n‖ := by
    rw [hsplit]
    exact norm_sum_le _ _
  have hterm : ∀ a ∈ Finset.range q,
      ‖∑ n ∈ P.filter (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), Fext n‖ ≤
        majorArcResidueMaximalSum X H q a F := by
    intro a ha
    let R : Finset ℤ := I.points.filter
      (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)])
    let Q : Finset ℤ := P.filter
      (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)])
    have hQR : Q ⊆ R := by
      intro n hn
      exact Finset.mem_filter.mpr
        ⟨hPI (Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2⟩
    have hQeq : Q = P ∩ R := by
      ext n
      simp only [Q, R, Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨hnP, hmod⟩
        exact ⟨hnP, hPI hnP, hmod⟩
      · rintro ⟨hnP, _, hmod⟩
        exact ⟨hnP, hmod⟩
    have hRrep : ∃ b : ℤ, ∃ L : ℕ,
        arithmeticProgressionPoints b q hq L = R := by
      simpa [R, I] using
        (finiteInterval_residueFilter_eq_arithmeticProgressionPoints
          I (a : ℤ) q hq)
    rcases hPAP with ⟨bP, dP, hdP, LP, hPrep⟩
    rcases hRrep with ⟨bR, LR, hRrep⟩
    have hQclass : Q = ∅ ∨ isFiniteArithmeticProgression Q := by
      have hclass := arithmeticProgressionPoints_inter_eq_empty_or_isFiniteArithmeticProgression
        bP bR dP q hdP hq LP LR
      simpa [Q, R, hQeq, hPrep, hRrep] using hclass
    have hQmem : Q ∈ arithmeticProgressionsWithin R := by
      rcases hQclass with hempty | hQAP
      · rw [hempty]
        exact empty_mem_arithmeticProgressionsWithin R
      · rw [arithmeticProgressionsWithin, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hQR, hQAP⟩
    have hsum :
        (∑ n ∈ Q, Fext n) =
          ∑ n ∈ Q, extendByZero R (fun n => F n.1) n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnR : n ∈ R := hQR hn
      have hnI : n ∈ I.points := (Finset.mem_filter.mp hnR).1
      simp [Fext, fI, extendByZero, hnI, hnR]
    have hmax :
        ‖∑ n ∈ Q, extendByZero R (fun n => F n.1) n‖ ≤
          majorArcResidueMaximalSum X H q a F := by
      change ‖∑ n ∈ Q, extendByZero R (fun n => F n.1) n‖ ≤
        progressionMaximalSumOnFiniteSet R (fun n => F n.1)
      unfold progressionMaximalSumOnFiniteSet
      exact Finset.le_sup'
        (fun S => ‖∑ n ∈ S, extendByZero R (fun n => F n.1) n‖) hQmem
    rw [← hsum] at hmax
    simpa [Q] using hmax
  calc
    ‖∑ n ∈ P, extendByZero I.points fI n‖ = ‖∑ n ∈ P, Fext n‖ := by
      rfl
    _ ≤ ∑ a ∈ Finset.range q,
          ‖∑ n ∈ P.filter
            (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), Fext n‖ := htriangle
    _ ≤ ∑ a ∈ Finset.range q, majorArcResidueMaximalSum X H q a F :=
      Finset.sum_le_sum hterm

/-- The exact residue-count error on the major-arc interval: every class
modulo `q` occurs within one of `H/q` times. This is finite interval
bookkeeping, not an estimate for the arithmetic coefficients. -/
theorem majorArcInterval_residueSlice_card_error
    (X H q : ℕ) (r : ℤ) (hq : 0 < q) :
    |(((majorArcInterval X H).points.filter
        (fun n => n ≡ r [ZMOD (q : ℤ)] )).card : ℝ) -
        (H : ℝ) / (q : ℝ)| ≤ 1 := by
  rw [majorArcInterval_points_eq_Ioc]
  have h := FractionalPrimes.Literature.LongArithmetic.intIntervalResidueCount_error
    (X : ℤ) (H : ℤ) (q : ℤ) r (by omega) (by exact_mod_cast hq)
  simpa [Nat.cast_add] using h

/-- Integer-centred specialization of the already checked strict-cutoff
Cramér residue-mean theorem. It supplies the model coefficient on each
major-arc residue, under exactly the source's sieve-level and small-prime
conditions; it is not cancellation for `μ` or `Λ`. -/
theorem majorArcCramerResidueMean
    (X H : ℕ) (y : ℝ) (q : ℕ) (a : ℤ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hq : 0 < q)
    (hzy : paperShortBlockCutoff (X : ℝ) ≤ y)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q →
      (p : ℝ) < paperShortBlockCutoff (X : ℝ)) :
    (1 < Int.gcd a (q : ℤ) →
      ∀ n : ℤ, n ≡ a [ZMOD (q : ℤ)] →
        paperShortBlockCramerWeight (X : ℝ) n = 0) ∧
    (Int.gcd a (q : ℤ) = 1 →
      |(∑ n ∈ ((majorArcInterval X H).points.filter
            (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)])),
          paperShortBlockCramerWeight (X : ℝ) n) -
        (H : ℝ) / (Nat.totient q : ℝ)| ≤
        sieveD * ((H : ℝ) / (Nat.totient q : ℝ)) *
            Real.exp (-(Real.log y /
              Real.log (paperShortBlockCutoff (X : ℝ)))) +
          paperCramerDensity (paperShortBlockCutoff (X : ℝ)) * y) := by
  have hXr : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hHr : 0 < (H : ℝ) := by positivity
  have h := FractionalPrimes.Literature.LongArithmetic.cramerResidueMean
    (X : ℝ) (H : ℝ) y q a hXr hHr hq hzy hsmall
  simpa [majorArcInterval_points_eq_Ioc, Nat.cast_add] using h

/-- The exact finite sieve-density coefficient on the unit residue classes.
This is the specialization of the checked strict-cutoff cancellation
`R(z) V_S = q/φ(q)` to the Cramér cutoff used by the major-arc task. The
selected primes remain precisely those `p < z` that do not divide `q`. -/
theorem majorArcCramerSelectedDensity_eq_totientRatio
    (X : ℝ) (q : ℕ) (hq : 0 < q)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q →
      (p : ℝ) < paperShortBlockCutoff X) :
    paperCramerDensity (paperShortBlockCutoff X) *
        FractionalPrimes.Literature.LongArithmetic.deletedPrimeSieveDensityProduct
          (FractionalPrimes.Literature.LongArithmetic.cramerResidueSelectedPrimes
            (paperShortBlockCutoff X) q)
          (paperShortBlockCutoff X) =
      (q : ℝ) / (Nat.totient q : ℝ) := by
  exact FractionalPrimes.Literature.LongArithmetic.cramerResidueDensity_selected_eq_totientRatio
    (paperShortBlockCutoff X) q hq hsmall

/-- Summing the exact unit-class main terms `H/φ(q)` over canonical
residues gives exactly `H`. This is the finite coefficient normalization
used when the residue-class Cramér means are reassembled. -/
theorem majorArcUnitResidueMainTerms_sum (H : ℝ) (q : ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q,
      if Nat.Coprime a q then H / (Nat.totient q : ℝ) else 0) = H := by
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hcount :
      ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨haq, ha⟩
      exact ⟨haq, ha.symm⟩
    · rintro ⟨haq, hqa⟩
      exact ⟨haq, hqa.symm⟩
  calc
    (∑ a ∈ Finset.range q,
      if Nat.Coprime a q then H / (Nat.totient q : ℝ) else 0) =
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          H / (Nat.totient q : ℝ) := by
            rw [← Finset.sum_filter]
    _ = ((Finset.range q).filter (fun a => Nat.Coprime a q)).card •
          (H / (Nat.totient q : ℝ)) := by
            rw [Finset.sum_const]
    _ = H := by
      rw [hcount]
      simp only [nsmul_eq_mul]
      field_simp [ne_of_gt hφ]

/-- Reassembling the checked Cramér means over the canonical residue classes
gives the total short-interval mass, with the unit-class mean errors summed
exactly over `φ(q)` classes. Nonunit classes contribute zero under the same
strict-cutoff condition. This is finite coefficient bookkeeping, not a
major-arc cancellation estimate. -/
theorem majorArcCramerTotalMass_error
    (X H : ℕ) (y : ℝ) (q : ℕ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hq : 0 < q)
    (hzy : paperShortBlockCutoff (X : ℝ) ≤ y)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q →
      (p : ℝ) < paperShortBlockCutoff (X : ℝ)) :
    |(∑ n ∈ (majorArcInterval X H).points,
        paperShortBlockCramerWeight (X : ℝ) n) - (H : ℝ)| ≤
      sieveD * (H : ℝ) *
          Real.exp (-(Real.log y /
            Real.log (paperShortBlockCutoff (X : ℝ)))) +
        (Nat.totient q : ℝ) *
          paperCramerDensity (paperShortBlockCutoff (X : ℝ)) * y := by
  classical
  let mass : ℕ → ℝ := fun a =>
    ∑ n ∈ (majorArcInterval X H).points.filter
      (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]),
      paperShortBlockCramerWeight (X : ℝ) n
  let err : ℝ :=
    sieveD * ((H : ℝ) / (Nat.totient q : ℝ)) *
        Real.exp (-(Real.log y /
          Real.log (paperShortBlockCutoff (X : ℝ)))) +
      paperCramerDensity (paperShortBlockCutoff (X : ℝ)) * y
  let G : ℕ → ℝ := fun a =>
    mass a - if Nat.Coprime a q then
      (H : ℝ) / (Nat.totient q : ℝ) else 0
  have hphi : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hphiR : 0 < (Nat.totient q : ℝ) := by exact_mod_cast hphi
  have hcount :
      ((Finset.range q).filter (fun a => Nat.Coprime a q)).card =
        Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨haq, hcop⟩
      exact ⟨haq, hcop.symm⟩
    · rintro ⟨haq, hcop⟩
      exact ⟨haq, hcop.symm⟩
  have hsplitC := majorArcInterval_sum_eq_sum_residue_filters X H q hq
    (fun n => (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
  have hsplit :
      (∑ n ∈ (majorArcInterval X H).points,
        paperShortBlockCramerWeight (X : ℝ) n) =
      ∑ a ∈ Finset.range q, mass a := by
    have hre := congrArg Complex.re hsplitC
    simpa only [Complex.re_sum, Complex.ofReal_re, mass] using hre
  have hGsum :
      (∑ a ∈ Finset.range q, G a) =
        (∑ n ∈ (majorArcInterval X H).points,
          paperShortBlockCramerWeight (X : ℝ) n) - (H : ℝ) := by
    rw [hsplit]
    calc
      (∑ a ∈ Finset.range q, G a) =
          (∑ a ∈ Finset.range q, mass a) -
            (∑ a ∈ Finset.range q,
              if Nat.Coprime a q then
                (H : ℝ) / (Nat.totient q : ℝ) else 0) := by
        simp only [G]
        rw [Finset.sum_sub_distrib]
      _ = (∑ a ∈ Finset.range q, mass a) - (H : ℝ) := by
        rw [majorArcUnitResidueMainTerms_sum (H : ℝ) q hq]
  have hterm : ∀ a ∈ Finset.range q,
      |G a| ≤ if Nat.Coprime a q then err else 0 := by
    intro a ha
    by_cases hcop : Nat.Coprime a q
    · have hgcd : Int.gcd (a : ℤ) (q : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact_mod_cast Nat.coprime_iff_gcd_eq_one.mp hcop
      have hmean := majorArcCramerResidueMean X H y q (a : ℤ)
        hX hH hq hzy hsmall
      have hmass :
          |mass a - (H : ℝ) / (Nat.totient q : ℝ)| ≤ err := by
        simpa [mass, err] using hmean.2 hgcd
      change |mass a - (if Nat.Coprime a q then
        (H : ℝ) / (Nat.totient q : ℝ) else 0)| ≤
          if Nat.Coprime a q then err else 0
      rw [if_pos hcop, if_pos hcop]
      exact hmass
    · have hgcdNat : Nat.gcd a q ≠ 1 := by
        intro hgcd
        exact hcop (Nat.coprime_iff_gcd_eq_one.mpr hgcd)
      have hgcdPos : 0 < Nat.gcd a q := Nat.gcd_pos_of_pos_right a hq
      have hgcdGt : 1 < Nat.gcd a q := by omega
      have hgcdInt : 1 < Int.gcd (a : ℤ) (q : ℤ) := by
        rw [Int.gcd_natCast_natCast]
        exact_mod_cast hgcdGt
      have hmean := majorArcCramerResidueMean X H y q (a : ℤ)
        hX hH hq hzy hsmall
      have hmass : mass a = 0 := by
        dsimp [mass]
        apply Finset.sum_eq_zero
        intro n hn
        exact hmean.1 hgcdInt n (Finset.mem_filter.mp hn).2
      simp [G, hcop, hmass]
  have hGbound :
      (∑ a ∈ Finset.range q, |G a|) ≤ (Nat.totient q : ℝ) * err := by
    calc
      (∑ a ∈ Finset.range q, |G a|) ≤
          ∑ a ∈ Finset.range q,
            if Nat.Coprime a q then err else 0 :=
        Finset.sum_le_sum (fun a ha => hterm a ha)
      _ = (Nat.totient q : ℝ) * err := by
        rw [← Finset.sum_filter, Finset.sum_const, hcount]
        simp [nsmul_eq_mul]
  calc
    |(∑ n ∈ (majorArcInterval X H).points,
        paperShortBlockCramerWeight (X : ℝ) n) - (H : ℝ)| =
      |∑ a ∈ Finset.range q, G a| := by rw [hGsum]
    _ ≤ ∑ a ∈ Finset.range q, |G a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Nat.totient q : ℝ) * err := hGbound
    _ = sieveD * (H : ℝ) *
          Real.exp (-(Real.log y /
            Real.log (paperShortBlockCutoff (X : ℝ)))) +
        (Nat.totient q : ℝ) *
          paperCramerDensity (paperShortBlockCutoff (X : ℝ)) * y := by
      dsimp [err]
      field_simp [ne_of_gt hphiR]
      <;> ring

/-- On one unit residue slice, the short-interval `Λ - Cr_X` coefficient
sum differs from the von Mangoldt slice sum normalized by `H/φ(q)` by at
most the checked Cramér residue-mean error. This is a finite coefficient
decomposition; it supplies no cancellation estimate for the von Mangoldt
slice itself. -/
theorem majorArcUnitLambdaMinusCramerResidue_error
    (X H : ℕ) (y : ℝ) (q : ℕ) (a : ℤ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hq : 0 < q)
    (hzy : paperShortBlockCutoff (X : ℝ) ≤ y)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q →
      (p : ℝ) < paperShortBlockCutoff (X : ℝ))
    (ha : Int.gcd a (q : ℤ) = 1) :
    |(∑ n ∈ ((majorArcInterval X H).points.filter
        (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)])),
        (paperLambda n - paperShortBlockCramerWeight (X : ℝ) n)) -
      ((∑ n ∈ ((majorArcInterval X H).points.filter
          (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)])), paperLambda n) -
        (H : ℝ) / (Nat.totient q : ℝ))| ≤
      sieveD * ((H : ℝ) / (Nat.totient q : ℝ)) *
          Real.exp (-(Real.log y /
            Real.log (paperShortBlockCutoff (X : ℝ)))) +
        paperCramerDensity (paperShortBlockCutoff (X : ℝ)) * y := by
  let R : Finset ℤ := (majorArcInterval X H).points.filter
    (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)])
  have hmodel := majorArcCramerResidueMean X H y q a hX hH hq hzy hsmall
  have hmean := hmodel.2 ha
  have hdecomp :
      (∑ n ∈ R,
        (paperLambda n - paperShortBlockCramerWeight (X : ℝ) n)) =
      (∑ n ∈ R, paperLambda n) -
        (∑ n ∈ R, paperShortBlockCramerWeight (X : ℝ) n) := by
    rw [Finset.sum_sub_distrib]
  calc
    |(∑ n ∈ R,
        (paperLambda n - paperShortBlockCramerWeight (X : ℝ) n)) -
      ((∑ n ∈ R, paperLambda n) - (H : ℝ) / (Nat.totient q : ℝ))| =
      |(-((∑ n ∈ R, paperShortBlockCramerWeight (X : ℝ) n) -
          (H : ℝ) / (Nat.totient q : ℝ)))| := by
        rw [hdecomp]
        congr 1
        ring
    _ = |(∑ n ∈ R, paperShortBlockCramerWeight (X : ℝ) n) -
          (H : ℝ) / (Nat.totient q : ℝ)| := by rw [abs_neg]
    _ ≤ sieveD * ((H : ℝ) / (Nat.totient q : ℝ)) *
          Real.exp (-(Real.log y /
            Real.log (paperShortBlockCutoff (X : ℝ)))) +
        paperCramerDensity (paperShortBlockCutoff (X : ℝ)) * y := by
      simpa [R] using hmean

/-- On a unit residue class, the short-interval Cramér weight is exactly
the density multiplier times the sieve indicator formed from primes below
the strict cutoff that do not divide the modulus. -/
theorem majorArcCramerWeight_eq_selectedIndicator
    (X : ℝ) (q : ℕ) (a n : ℤ)
    (ha : Nat.Coprime a.natAbs q)
    (hmod : n ≡ a [ZMOD (q : ℤ)]) :
    paperShortBlockCramerWeight X n =
      paperCramerDensity (paperShortBlockCutoff X) *
        (if Int.gcd n
            (((FractionalPrimes.Literature.LongArithmetic.cramerResidueSelectedPrimes
              (paperShortBlockCutoff X) q).prod id : ℕ) : ℤ) = 1
          then 1 else 0) := by
  have hind :=
    FractionalPrimes.Literature.LongArithmetic.cramerSieveIndicator_eq_selected_of_coprimeResidue
      (paperShortBlockCutoff X) q a n ha hmod
  have hind' :
      (if Int.gcd n (paperPrimeProduct (paperShortBlockCutoff X) : ℤ) = 1
        then (1 : ℝ) else 0) =
      (if Int.gcd n
          (((FractionalPrimes.Literature.LongArithmetic.cramerResidueSelectedPrimes
            (paperShortBlockCutoff X) q).prod id : ℕ) : ℤ) = 1
        then 1 else 0) := by
    convert hind using 1 <;> rfl
  unfold paperShortBlockCramerWeight paperCramerWeight
  exact congrArg (fun u : ℝ =>
    paperCramerDensity (paperShortBlockCutoff X) * u) hind'

/-- On a nonunit residue class, the strict-cutoff Cramér coefficient
vanishes. Thus every finite short-interval subsum of `Λ - Cr_X` in that
class is bounded by the exact nonunit von Mangoldt bound. This is coefficient
bookkeeping for `lu:major-arcs-task`, conditional only on the source's strict
prime-divisor cutoff condition. -/
theorem majorArcNonunitLambdaMinusCramerSubsumBound
    (X H q : ℕ) (a : ℤ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hq : 1 ≤ q)
    (ha : 1 < Int.gcd a (q : ℤ))
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q →
      (p : ℝ) < paperShortBlockCutoff (X : ℝ))
    (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc (X + 1) (X + H))
    (hres : ∀ n ∈ S, (n : ℤ) ≡ a [ZMOD (q : ℤ)]) :
    0 ≤ ∑ n ∈ S, majorArcLambdaMinusCramerNat (X : ℝ) n ∧
      (∑ n ∈ S, majorArcLambdaMinusCramerNat (X : ℝ) n) ≤
        (Real.log (q : ℝ) / Real.log 2) *
          Real.log ((X + H : ℕ) : ℝ) := by
  have hY : 2 ≤ ((X + H : ℕ) : ℝ) := by
    have hNat : 2 ≤ X + H := by omega
    exact_mod_cast hNat
  have hS' : S ⊆ Finset.Icc 1 (Nat.floor ((X + H : ℕ) : ℝ)) := by
    intro n hn
    have hnRange := hS hn
    simp only [Finset.mem_Icc] at hnRange
    simp only [Finset.mem_Icc]
    constructor
    · omega
    · have hfloor : Nat.floor ((X + H : ℕ) : ℝ) = X + H := by
        exact Nat.floor_natCast _
      rw [hfloor]
      exact hnRange.2
  have hLambdaBound :=
    FractionalPrimes.Literature.LongArithmetic.nonunitVonMangoldtSubsumBound
      hY hq ha S hS' hres
  have hcoeff : ∀ n ∈ S,
      majorArcLambdaMinusCramerNat (X : ℝ) n = vonMangoldtWeight n := by
    intro n hn
    have hnpos : 0 < (n : ℤ) := by
      have hnRange := hS hn
      simp only [Finset.mem_Icc] at hnRange
      omega
    have hmodel : paperShortBlockCramerWeight (X : ℝ) (n : ℤ) = 0 := by
      simpa [paperShortBlockCramerWeight] using
        (FractionalPrimes.Literature.LongArithmetic.paperCramerWeight_eq_zero_of_nonunitResidue
          (paperShortBlockCutoff (X : ℝ)) q a (n : ℤ) ha hsmall (hres n hn))
    have hLam : paperLambda (n : ℤ) = vonMangoldtWeight n := by
      rw [paperLambda, if_pos hnpos]
      simp
    rw [majorArcLambdaMinusCramerNat, hLam, hmodel]
    ring
  have hsum :
      (∑ n ∈ S, majorArcLambdaMinusCramerNat (X : ℝ) n) =
        ∑ n ∈ S, vonMangoldtWeight n := by
    refine Finset.sum_congr rfl (by
      intro n hn
      exact hcoeff n hn)
  rw [hsum]
  exact hLambdaBound

/-- The optional major-arc task `lu:major-arcs-task` exactly as stated in
the approved blueprint. Here positive integer parameters are represented by
`ℕ`, while all scale comparisons and the interval maximal sums use their
canonical integer/real embeddings. The Cramér term uses the strict-cutoff
model `paperShortBlockCramerWeight` from `lc:models`. This is only a
proposition-valued task contract, not a proof of the estimate. -/
def majorArcTask : Prop :=
  ∀ a η : ℝ, 0 < a → 0 < η → η < 3 / 16 →
    ∃ C : ℝ, 0 < C ∧
      ∀ X H : ℕ, 3 ≤ X → 1 ≤ H →
        (X : ℝ) ^ (7 / 12 + η) ≤ (H : ℝ) →
        (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
        majorArcMaximalSum X H (fun n => (paperMu n : ℂ)) +
          majorArcMaximalSum X H
            (fun n => (paperLambda n : ℂ) -
              (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) ≤
          C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a)

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.majorArcInterval_points_eq_Ioc
#print axioms FractionalPrimes.Literature.Uniformity.majorArcMaximalSum_le_sum_residueMaxima
#print axioms FractionalPrimes.Literature.Uniformity.majorArcInterval_residueSlice_eq_progressionPoints
#print axioms FractionalPrimes.Literature.Uniformity.majorArcInterval_sum_eq_sum_residue_filters
#print axioms FractionalPrimes.Literature.Uniformity.majorArcInterval_residueSlice_card_error
#print axioms FractionalPrimes.Literature.Uniformity.majorArcCramerResidueMean
#print axioms FractionalPrimes.Literature.Uniformity.majorArcCramerSelectedDensity_eq_totientRatio
#print axioms FractionalPrimes.Literature.Uniformity.majorArcUnitResidueMainTerms_sum
#print axioms FractionalPrimes.Literature.Uniformity.majorArcCramerTotalMass_error
#print axioms FractionalPrimes.Literature.Uniformity.majorArcUnitLambdaMinusCramerResidue_error
#print axioms FractionalPrimes.Literature.Uniformity.majorArcCramerWeight_eq_selectedIndicator
#print axioms FractionalPrimes.Literature.Uniformity.majorArcNonunitLambdaMinusCramerSubsumBound
#print axioms FractionalPrimes.Literature.Uniformity.majorArcTask
