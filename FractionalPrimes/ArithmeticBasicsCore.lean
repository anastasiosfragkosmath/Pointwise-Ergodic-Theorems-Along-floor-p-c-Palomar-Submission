module

public import FractionalPrimes.Core
public import FractionalPrimes.RpowContinuity
public import FractionalPrimes.CenteredFloor
public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.Interval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

namespace FractionalPrimes


/-- The exact finite set of integers in the paper's interval `(x,x+Y]`. -/
noncomputable def realIntegerInterval (x Y : ℝ) : Finset ℤ :=
  Finset.Ico (⌊x⌋ + 1) (⌊x + Y⌋ + 1)

noncomputable def realIntegerGoodBandSamples (x Y θ : ℝ) (k : ℤ) (D : ℝ → ℝ) : Finset ℤ :=
  (realIntegerInterval x Y).filter fun n : ℤ =>
    D (n : ℝ) ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ)

/-- The blueprint's local `C²` data on the half-open interval `(x,x+Y]`.
Continuity on `Ioc` records left-continuous extension to the right endpoint;
the derivative fields on `Ioo` are ordinary interior derivatives, and the
endpoint fields record derivatives relative to the left-sided domain. No
regularity at the excluded point `x` is required. -/
structure HalfOpenC2Data (x Y : ℝ) where
  length_pos : 0 < Y
  f : ℝ → ℝ
  firstDerivative : ℝ → ℝ
  secondDerivative : ℝ → ℝ
  f_continuous : ContinuousOn f (Set.Ioc x (x + Y))
  first_continuous : ContinuousOn firstDerivative (Set.Ioc x (x + Y))
  second_continuous : ContinuousOn secondDerivative (Set.Ioc x (x + Y))
  f_hasDerivAt : ∀ t ∈ Set.Ioo x (x + Y),
    HasDerivAt f (firstDerivative t) t
  first_hasDerivAt : ∀ t ∈ Set.Ioo x (x + Y),
    HasDerivAt firstDerivative (secondDerivative t) t
  f_right_hasDerivWithinAt :
    HasDerivWithinAt f (firstDerivative (x + Y)) (Set.Iic (x + Y)) (x + Y)
  first_right_hasDerivWithinAt :
    HasDerivWithinAt firstDerivative (secondDerivative (x + Y))
      (Set.Iic (x + Y)) (x + Y)

/-- Finite-order differentiability data on the paper's half-open interval.
`derivative k` represents the `k`th derivative, with continuous extensions
through the included right endpoint and relative derivatives there. -/
structure HalfOpenCkData (x Y : ℝ) (order : ℕ) where
  length_pos : 0 < Y
  derivative : ℕ → ℝ → ℝ
  continuous : ∀ k ≤ order, ContinuousOn (derivative k) (Set.Ioc x (x + Y))
  hasDerivAt : ∀ k, k < order → ∀ t ∈ Set.Ioo x (x + Y),
    HasDerivAt (derivative k) (derivative (k + 1) t) t
  right_hasDerivWithinAt : ∀ k, k < order →
    HasDerivWithinAt (derivative k) (derivative (k + 1) (x + Y))
      (Set.Iic (x + Y)) (x + Y)

/-- The explicit `k`th derivative model for a scaled real monomial. -/
noncomputable def scaledRealMonomialDerivative (a c : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  a * (descPochhammer ℝ k).eval c * t ^ (c - (k : ℝ))

/-- The explicit monomial derivative model has the next derivative at every
nonzero point. -/
theorem scaledRealMonomialDerivative_hasDerivAt {a c t : ℝ} (k : ℕ) (ht : t ≠ 0) :
    HasDerivAt (scaledRealMonomialDerivative a c k)
      (scaledRealMonomialDerivative a c (k + 1) t) t := by
  have hpow := (Real.hasDerivAt_rpow_const
    (x := t) (p := c - (k : ℝ)) (Or.inl ht)).const_mul
      (a * (descPochhammer ℝ k).eval c)
  convert hpow using 1
  · funext z
    simp [scaledRealMonomialDerivative]
  · rw [scaledRealMonomialDerivative, descPochhammer_succ_eval, Nat.cast_succ]
    have hexp : c - ((k : ℝ) + 1) = c - (k : ℝ) - 1 := by ring
    rw [hexp]
    ring

/-- A scaled real monomial supplies the half-open differentiability data
required by the derivative test on every interval with positive left endpoint. -/
noncomputable def scaledRealMonomialHalfOpenData (a c x Y : ℝ) (order : ℕ)
    (hx : 0 < x) (hY : 0 < Y) :
    HalfOpenCkData x Y order where
  length_pos := hY
  derivative := scaledRealMonomialDerivative a c
  continuous := by
    intro k hk t ht
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_const.mul
    apply Real.continuousAt_rpow_const
    exact Or.inl (ne_of_gt (hx.trans (Set.mem_Ioc.mp ht).1))
  hasDerivAt := by
    intro k hk t ht
    exact scaledRealMonomialDerivative_hasDerivAt k
      (ne_of_gt (hx.trans ht.1))
  right_hasDerivWithinAt := by
    intro k hk
    have hright : 0 < x + Y := by linarith
    exact (scaledRealMonomialDerivative_hasDerivAt k (ne_of_gt hright)).hasDerivWithinAt

/-- Negating the represented function negates every derivative level while
preserving the paper's half-open regularity convention. -/
def HalfOpenCkData.neg {x Y : ℝ} {order : ℕ}
    (data : HalfOpenCkData x Y order) : HalfOpenCkData x Y order where
  length_pos := data.length_pos
  derivative k t := -data.derivative k t
  continuous k hk := (data.continuous k hk).neg
  hasDerivAt k hk t ht := (data.hasDerivAt k hk t ht).neg
  right_hasDerivWithinAt k hk := (data.right_hasDerivWithinAt k hk).neg

def HalfOpenCkData.toC2Data {x Y : ℝ} {order : ℕ}
    (data : HalfOpenCkData x Y order) (horder : 2 ≤ order) : HalfOpenC2Data x Y where
  length_pos := data.length_pos
  f := data.derivative 0
  firstDerivative := data.derivative 1
  secondDerivative := data.derivative 2
  f_continuous := data.continuous 0 (by omega)
  first_continuous := data.continuous 1 (by omega)
  second_continuous := data.continuous 2 horder
  f_hasDerivAt := by
    intro t ht
    simpa using data.hasDerivAt 0 (by omega) t ht
  first_hasDerivAt := by
    intro t ht
    simpa using data.hasDerivAt 1 (by omega) t ht
  f_right_hasDerivWithinAt := by
    simpa using data.right_hasDerivWithinAt 0 (by omega)
  first_right_hasDerivWithinAt := by
    simpa using data.right_hasDerivWithinAt 1 (by omega)

/-- The derivative family is unchanged when half-open data is transported
across equal interval-length and order indices. -/
theorem HalfOpenCkData.cast_derivative
    {x Y₁ Y₂ : ℝ} {order₁ order₂ k : ℕ}
    (hY : Y₁ = Y₂) (horder : order₁ = order₂)
    (data : HalfOpenCkData x Y₁ order₁) :
    (cast (by cases hY; cases horder; rfl :
      HalfOpenCkData x Y₁ order₁ = HalfOpenCkData x Y₂ order₂) data).derivative k =
      data.derivative k := by
  cases hY
  cases horder
  rfl

/-- The derivative family beginning at a fixed order, with the same domain
and endpoint conventions. -/
def HalfOpenCkData.derivativeTail
    {x Y : ℝ} {order offset : ℕ} (data : HalfOpenCkData x Y order)
    (hoffset : offset ≤ order) : HalfOpenCkData x Y (order - offset) where
  length_pos := data.length_pos
  derivative k := data.derivative (k + offset)
  continuous k hk := data.continuous (k + offset) (by omega)
  hasDerivAt k hk t ht := by
    have h := data.hasDerivAt (k + offset) (by omega) t ht
    simpa [Nat.add_assoc, Nat.add_comm offset 1] using h
  right_hasDerivWithinAt k hk := by
    have h := data.right_hasDerivWithinAt (k + offset) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm offset 1] using h

theorem HalfOpenC2Data.restrict_compact {x Y a b : ℝ}
    (data : HalfOpenC2Data x Y) (hxa : x < a) (hba : b ≤ x + Y) :
    ContinuousOn data.f (Set.Icc a b) ∧
    ContinuousOn data.firstDerivative (Set.Icc a b) ∧
    ContinuousOn data.secondDerivative (Set.Icc a b) ∧
    (∀ t ∈ Set.Ioo a b, HasDerivAt data.f (data.firstDerivative t) t) ∧
    (∀ t ∈ Set.Ioo a b,
      HasDerivAt data.firstDerivative (data.secondDerivative t) t) := by
  have hsub : Set.Icc a b ⊆ Set.Ioc x (x + Y) := by
    intro t ht
    exact ⟨lt_of_lt_of_le hxa ht.1, ht.2.trans hba⟩
  have hsubo : Set.Ioo a b ⊆ Set.Ioo x (x + Y) := by
    intro t ht
    exact ⟨lt_trans hxa ht.1, lt_of_lt_of_le ht.2 hba⟩
  refine ⟨data.f_continuous.mono hsub,
    data.first_continuous.mono hsub,
    data.second_continuous.mono hsub, ?_, ?_⟩
  · intro t ht
    exact data.f_hasDerivAt t (hsubo ht)
  · intro t ht
    exact data.first_hasDerivAt t (hsubo ht)

/-- The first fundamental-theorem step on a compact subinterval of the
paper's half-open domain. The compact interval may end at the included right
endpoint, but its left endpoint stays strictly above the excluded endpoint. -/
theorem HalfOpenC2Data.integral_secondDerivative_eq_sub
    {x Y a b : ℝ} (data : HalfOpenC2Data x Y)
    (hxa : x < a) (hab : a ≤ b) (hby : b ≤ x + Y) :
    ∫ t in a..b, data.secondDerivative t =
      data.firstDerivative b - data.firstDerivative a := by
  have hdata := data.restrict_compact hxa hby
  rcases hdata with ⟨_hf, hfirst, hsecond, _hfderiv, hfirstderiv⟩
  have hint : IntervalIntegrable data.secondDerivative MeasureTheory.volume a b := by
    have hcont : ContinuousOn data.secondDerivative (Set.uIcc a b) := by
      simpa [Set.uIcc_of_le hab] using hsecond
    exact hcont.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hfirst
    hfirstderiv hint

theorem mem_realIntegerInterval_iff (x Y : ℝ) (n : ℤ) :
    n ∈ realIntegerInterval x Y ↔ (x < n ∧ (n : ℝ) ≤ x + Y) := by
  simp only [realIntegerInterval, Finset.mem_Ico]
  constructor
  · intro hn
    constructor
    · apply (Int.floor_lt).mp
      omega
    · apply (Int.le_floor).mp
      omega
  · rintro ⟨hlo, hhi⟩
    constructor
    · have hh := (Int.floor_lt).mpr hlo
      omega
    · have hh := (Int.le_floor).mpr hhi
      omega

/-- Consecutive half-open real intervals partition exactly as the corresponding
integer interval, with the shared endpoint assigned to the left interval. -/
theorem realIntegerInterval_eq_union_adjacent
    {x Y Z : ℝ} (hY : 0 ≤ Y) (hZ : 0 ≤ Z) :
    realIntegerInterval x (Y + Z) =
      realIntegerInterval x Y ∪ realIntegerInterval (x + Y) Z := by
  ext n
  simp only [Finset.mem_union, mem_realIntegerInterval_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    by_cases hmid : (n : ℝ) ≤ x + Y
    · left
      exact ⟨hlo, hmid⟩
    · right
      constructor
      · exact lt_of_not_ge hmid
      · have hfinal : (n : ℝ) ≤ (x + Y) + Z := by nlinarith
        exact hfinal
  · rintro (⟨hlo, hmid⟩ | ⟨hmid, hhi⟩)
    · exact ⟨hlo, by nlinarith⟩
    · exact ⟨by linarith, by nlinarith⟩

/-- Additive sums over adjacent real intervals split without endpoint loss or
overlap. -/
theorem sum_realIntegerInterval_split
    {α : Type*} [AddCommMonoid α] {x Y Z : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (f : ℤ → α) :
    (∑ n ∈ realIntegerInterval x (Y + Z), f n) =
      (∑ n ∈ realIntegerInterval x Y, f n) +
        (∑ n ∈ realIntegerInterval (x + Y) Z, f n) := by
  rw [realIntegerInterval_eq_union_adjacent hY hZ]
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro n hnLeft hnRight
  have hLeft := (mem_realIntegerInterval_iff x Y n).mp hnLeft
  have hRight := (mem_realIntegerInterval_iff (x + Y) Z n).mp hnRight
  exact (not_lt_of_ge hLeft.2) hRight.1

/-- The quotient at the next dyadic scale is the half scale divided by the
current dyadic denominator. -/
theorem realDyadicQuotient_succ (X : ℝ) (v : ℕ) :
    X / (2 : ℝ) ^ (v + 1) = (X / 2) / (2 : ℝ) ^ v := by
  rw [pow_succ]
  field_simp
  <;> ring

/-- Adjacent dyadic denominators differ by exactly a factor of two. -/
theorem realDyadicQuotient_double (X : ℝ) (v : ℕ) :
    X / (2 : ℝ) ^ v = 2 * (X / (2 : ℝ) ^ (v + 1)) := by
  calc
    X / (2 : ℝ) ^ v = 2 * ((X / 2) / (2 : ℝ) ^ v) := by
      field_simp
      <;> ring
    _ = 2 * (X / (2 : ℝ) ^ (v + 1)) := by
      rw [realDyadicQuotient_succ]

/-- The integer points in one dyadic block `(X/2^(v+1), X/2^v]`. -/
noncomputable def realDyadicIntegerBlock (X : ℝ) (v : ℕ) : Finset ℤ :=
  realIntegerInterval (X / (2 : ℝ) ^ (v + 1))
    (X / (2 : ℝ) ^ (v + 1))

/-- Exact finite partition of `(0,X]` into its first `J` dyadic blocks and the
remaining initial interval. -/
theorem sum_realIntegerInterval_dyadic_partition
    {α : Type*} [AddCommMonoid α] (X : ℝ) (hX : 0 ≤ X)
    (J : ℕ) (f : ℤ → α) :
    (∑ n ∈ realIntegerInterval 0 X, f n) =
      (∑ v ∈ Finset.range J,
        ∑ n ∈ realDyadicIntegerBlock X v, f n) +
        (∑ n ∈ realIntegerInterval 0 (X / (2 : ℝ) ^ J), f n) := by
  induction J generalizing X with
  | zero =>
      simp [realDyadicIntegerBlock]
  | succ J ih =>
      have hsplit :
          (∑ n ∈ realIntegerInterval 0 X, f n) =
            (∑ n ∈ realIntegerInterval 0 (X / 2), f n) +
              (∑ n ∈ realIntegerInterval (X / 2) (X / 2), f n) := by
        have hhalf : 0 ≤ X / 2 := by positivity
        have hsplit' := sum_realIntegerInterval_split
          (x := (0 : ℝ)) (Y := X / 2) (Z := X / 2) hhalf hhalf f
        calc
          _ = ∑ n ∈ realIntegerInterval 0 (X / 2 + X / 2), f n := by
            congr 2
            ring
          _ = _ := by
            simpa only [zero_add] using hsplit'
      rw [hsplit]
      rw [ih (X / 2) (by positivity)]
      have hblocks :
          (∑ v ∈ Finset.range J,
            ∑ n ∈ realDyadicIntegerBlock (X / 2) v, f n) =
          (∑ v ∈ Finset.range J,
            ∑ n ∈ realDyadicIntegerBlock X (v + 1), f n) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp only [realDyadicIntegerBlock]
        have hscale := realDyadicQuotient_succ X (v + 1)
        simpa [Nat.add_assoc] using
          (show
            (∑ n ∈ realIntegerInterval ((X / 2) / (2 : ℝ) ^ (v + 1))
              ((X / 2) / (2 : ℝ) ^ (v + 1)), f n) =
            (∑ n ∈ realIntegerInterval (X / (2 : ℝ) ^ (v + 2))
              (X / (2 : ℝ) ^ (v + 2)), f n) by rw [hscale])
      have hfirst : realDyadicIntegerBlock X 0 =
          realIntegerInterval (X / 2) (X / 2) := by
        simp [realDyadicIntegerBlock]
      have hrem : X / (2 : ℝ) ^ (J + 1) =
          (X / 2) / (2 : ℝ) ^ J := realDyadicQuotient_succ X J
      rw [Finset.sum_range_succ']
      rw [hblocks, hfirst, hrem]
      ac_rfl

/-- The lengths of the first `J` dyadic blocks telescope to the length of
`(X/2^J,X]`. -/
theorem sum_realDyadicBlockLengths (X : ℝ) (J : ℕ) :
    (∑ v ∈ Finset.range J, X / (2 : ℝ) ^ (v + 1)) =
      X - X / (2 : ℝ) ^ J := by
  induction J generalizing X with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      have hscale : X / (2 : ℝ) ^ J =
          2 * (X / (2 : ℝ) ^ (J + 1)) := by
        have hq := realDyadicQuotient_succ X J
        calc
          X / (2 : ℝ) ^ J = 2 * ((X / 2) / (2 : ℝ) ^ J) := by
            field_simp
            <;> ring
          _ = 2 * (X / (2 : ℝ) ^ (J + 1)) := by rw [hq]
      nlinarith

/-- Aggregate retained dyadic block norms by their total length, with the
initial remainder kept as a separate term. -/
theorem norm_sum_realIntegerInterval_dyadic_aggregate
    {X C R : ℝ} {J : ℕ} (hX : 0 ≤ X) (hC : 0 ≤ C)
    (f : ℤ → ℂ)
    (hblocks : ∀ v ∈ Finset.range J,
      ‖∑ n ∈ realDyadicIntegerBlock X v, f n‖ ≤
        C * (X / (2 : ℝ) ^ (v + 1)))
    (hremainder :
      ‖∑ n ∈ realIntegerInterval 0 (X / (2 : ℝ) ^ J), f n‖ ≤ R) :
    ‖∑ n ∈ realIntegerInterval 0 X, f n‖ ≤ C * X + R := by
  let blockSum : ℕ → ℂ := fun v => ∑ n ∈ realDyadicIntegerBlock X v, f n
  have hblockNormSum :
      (∑ v ∈ Finset.range J, ‖blockSum v‖) ≤ C * X := by
    calc
      (∑ v ∈ Finset.range J, ‖blockSum v‖) ≤
          ∑ v ∈ Finset.range J, C * (X / (2 : ℝ) ^ (v + 1)) := by
        apply Finset.sum_le_sum
        intro v hv
        exact hblocks v hv
      _ = C * (∑ v ∈ Finset.range J, X / (2 : ℝ) ^ (v + 1)) := by
        rw [← Finset.mul_sum]
      _ = C * (X - X / (2 : ℝ) ^ J) := by
        rw [sum_realDyadicBlockLengths]
      _ ≤ C * X := by
        have hrem : 0 ≤ X / (2 : ℝ) ^ J := by positivity
        nlinarith
  have hpartition := sum_realIntegerInterval_dyadic_partition X hX J f
  calc
    ‖∑ n ∈ realIntegerInterval 0 X, f n‖ =
        ‖(∑ v ∈ Finset.range J, blockSum v) +
          (∑ n ∈ realIntegerInterval 0 (X / (2 : ℝ) ^ J), f n)‖ := by
            rw [hpartition]
    _ ≤ ‖∑ v ∈ Finset.range J, blockSum v‖ +
        ‖∑ n ∈ realIntegerInterval 0 (X / (2 : ℝ) ^ J), f n‖ := norm_add_le _ _
    _ ≤ (∑ v ∈ Finset.range J, ‖blockSum v‖) + R := by
      exact add_le_add (norm_sum_le _ _) hremainder
    _ ≤ C * X + R := add_le_add hblockNormSum le_rfl

/-- Aggregate nonnegative-style real block sums from a uniform bound on each
retained dyadic block, keeping the terminal initial interval separate. -/
theorem sum_realIntegerInterval_dyadic_uniform
    {X B R : ℝ} {J : ℕ} (hX : 0 ≤ X)
    (f : ℤ → ℝ)
    (hblocks : ∀ v ∈ Finset.range J,
      (∑ n ∈ realDyadicIntegerBlock X v, f n) ≤ B)
    (hremainder :
      (∑ n ∈ realIntegerInterval 0 (X / (2 : ℝ) ^ J), f n) ≤ R) :
    (∑ n ∈ realIntegerInterval 0 X, f n) ≤ (J : ℝ) * B + R := by
  have hblockSum :
      (∑ v ∈ Finset.range J,
        ∑ n ∈ realDyadicIntegerBlock X v, f n) ≤ (J : ℝ) * B := by
    calc
      _ ≤ ∑ _v ∈ Finset.range J, B := by
        apply Finset.sum_le_sum
        intro v hv
        exact hblocks v hv
      _ = (J : ℝ) * B := by simp
  rw [sum_realIntegerInterval_dyadic_partition X hX J f]
  exact add_le_add hblockSum hremainder

theorem realIntegerInterval_card_le (x Y : ℝ) (hY : 1 ≤ Y) :
    ((realIntegerInterval x Y).card : ℝ) ≤ Y + 1 := by
  have hmono : ⌊x⌋ ≤ ⌊x + Y⌋ := Int.floor_mono (by linarith)
  have hIco : ⌊x⌋ + 1 ≤ ⌊x + Y⌋ + 1 := by omega
  have hcard : ((realIntegerInterval x Y).card : ℝ) =
      ((⌊x + Y⌋ + 1 : ℤ) : ℝ) - ((⌊x⌋ + 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.card_Ico_of_le (⌊x⌋ + 1) (⌊x + Y⌋ + 1) hIco
  have hfloorLo : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hfloorHi : (⌊x + Y⌋ : ℝ) ≤ x + Y := Int.floor_le (x + Y)
  push_cast at hcard
  linarith

/-- Exact cardinality of the paper's half-open real interval of integers.
For positive length this is `floor (x + Y) - floor x`, equivalently
`floor b - floor a` for `(a,b]`. -/
theorem realIntegerInterval_card (x Y : ℝ) (hY : 0 < Y) :
    ((realIntegerInterval x Y).card : ℤ) = ⌊x + Y⌋ - ⌊x⌋ := by
  have hmono : ⌊x⌋ ≤ ⌊x + Y⌋ := Int.floor_mono (by linarith)
  have hIco : ⌊x⌋ + 1 ≤ ⌊x + Y⌋ + 1 := by omega
  have hcard := Int.card_Ico_of_le (⌊x⌋ + 1) (⌊x + Y⌋ + 1) hIco
  simpa [realIntegerInterval] using hcard

theorem realIntegerInterval_card_le_of_nonneg (x Y : ℝ) (hY : 0 ≤ Y) :
    ((realIntegerInterval x Y).card : ℝ) ≤ Y + 1 := by
  have hmono : ⌊x⌋ ≤ ⌊x + Y⌋ := Int.floor_mono (by linarith)
  have hIco : ⌊x⌋ + 1 ≤ ⌊x + Y⌋ + 1 := by omega
  have hcard : ((realIntegerInterval x Y).card : ℝ) =
      ((⌊x + Y⌋ + 1 : ℤ) : ℝ) - ((⌊x⌋ + 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.card_Ico_of_le (⌊x⌋ + 1) (⌊x + Y⌋ + 1) hIco
  have hfloorLo : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hfloorHi : (⌊x + Y⌋ : ℝ) ≤ x + Y := Int.floor_le (x + Y)
  push_cast at hcard
  linarith

/-- The number of positive integers in `(0,Y]` is at most its real length,
including when `Y<1`. -/
theorem realIntegerInterval_zero_card_le (Y : ℝ) (hY : 0 ≤ Y) :
    ((realIntegerInterval 0 Y).card : ℝ) ≤ Y := by
  have hfloor : 0 ≤ ⌊Y⌋ := Int.floor_nonneg.mpr hY
  have hIco : (1 : ℤ) ≤ ⌊Y⌋ + 1 := by omega
  have hcardInt : ((realIntegerInterval 0 Y).card : ℤ) = ⌊Y⌋ := by
    simpa [realIntegerInterval] using
      (Int.card_Ico_of_le (1 : ℤ) (⌊Y⌋ + 1) hIco)
  have hcard : ((realIntegerInterval 0 Y).card : ℝ) = (⌊Y⌋ : ℝ) := by
    exact_mod_cast hcardInt
  rw [hcard]
  exact Int.floor_le Y

/-- A finite dyadic cutoff makes the remaining interval no longer than the
prescribed `N^(1-κ)/d` initial segment. -/
theorem exists_real_dyadic_cutoff
    {N d κ : ℝ} (hN : 1 < N) (hd : 0 < d) (hκ : 0 < κ) :
    ∃ J : ℕ, (N / d) / (2 : ℝ) ^ J ≤ N ^ (1 - κ) / d := by
  have hpowTendsto :
      Filter.Tendsto (fun J : ℕ => (2 : ℝ) ^ J) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨J, hJ⟩ :=
    Filter.tendsto_atTop_atTop.mp hpowTendsto (N ^ κ)
  have hJpow : N ^ κ ≤ (2 : ℝ) ^ J := hJ J le_rfl
  have hNpos : 0 < N := by linarith
  have hprod : N ^ (1 - κ) * N ^ κ = N := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring_nf
    rw [Real.rpow_one]
  have hnum : N ≤ N ^ (1 - κ) * (2 : ℝ) ^ J := by
    calc
      N = N ^ (1 - κ) * N ^ κ := hprod.symm
      _ ≤ N ^ (1 - κ) * (2 : ℝ) ^ J :=
        mul_le_mul_of_nonneg_left hJpow (Real.rpow_nonneg hNpos.le _)
  have hdiv : N / (2 : ℝ) ^ J ≤ N ^ (1 - κ) :=
    (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ J)).2 hnum
  refine ⟨J, ?_⟩
  calc
    (N / d) / (2 : ℝ) ^ J = (N / (2 : ℝ) ^ J) / d := by ring
    _ ≤ N ^ (1 - κ) / d := div_le_div_of_nonneg_right hdiv hd.le

/-- The least dyadic cutoff leaves every preceding block above the retained
scale `N^(1-κ)/(2d)`. -/
theorem exists_minimal_real_dyadic_cutoff
    {N d κ : ℝ} (hN : 1 < N) (hd : 0 < d) (hκ : 0 < κ) :
    ∃ J : ℕ,
      (N / d) / (2 : ℝ) ^ J ≤ N ^ (1 - κ) / d ∧
      ∀ v : ℕ, v < J →
        N ^ (1 - κ) / (2 * d) ≤ (N / d) / (2 : ℝ) ^ (v + 1) := by
  let cutoff : ℕ → Prop := fun J =>
    (N / d) / (2 : ℝ) ^ J ≤ N ^ (1 - κ) / d
  have hexists : ∃ J, cutoff J := exists_real_dyadic_cutoff hN hd hκ
  let J : ℕ := Nat.find hexists
  have hcut : cutoff J := Nat.find_spec hexists
  have hNpos : 0 < N := by linarith
  have hpowlt : N ^ (1 - κ) < N := by
    calc
      N ^ (1 - κ) < N ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hN (by linarith)
      _ = N := by rw [Real.rpow_one]
  have hzero : ¬ cutoff 0 := by
    intro hzero
    have hdiv : N / d ≤ N ^ (1 - κ) / d := by simpa [cutoff] using hzero
    have hcross := (div_le_div_iff₀ hd hd).mp hdiv
    have hNle : N ≤ N ^ (1 - κ) :=
      (mul_le_mul_iff_right₀ hd).mp (by simpa [mul_comm] using hcross)
    exact (not_le_of_gt hpowlt) hNle
  have hJpos : 0 < J := by
    apply Nat.pos_of_ne_zero
    intro hJzero
    apply hzero
    simpa [J, hJzero] using hcut
  have hprev :
      N ^ (1 - κ) / d < (N / d) / (2 : ℝ) ^ (J - 1) := by
    apply lt_of_not_ge
    exact Nat.find_min hexists (Nat.pred_lt (Nat.ne_of_gt hJpos))
  refine ⟨J, hcut, ?_⟩
  intro v hv
  have hidx : v + 1 ≤ J := Nat.succ_le_of_lt hv
  have hden : (2 : ℝ) ^ (v + 1) ≤ (2 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) hidx
  have hXnonneg : 0 ≤ N / d := by positivity
  have hPmono : (N / d) / (2 : ℝ) ^ J ≤ (N / d) / (2 : ℝ) ^ (v + 1) := by
    apply (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) J)
      (pow_pos (by norm_num : (0 : ℝ) < 2) (v + 1))).2
    nlinarith [mul_le_mul_of_nonneg_left hden hXnonneg]
  have hprevScale := realDyadicQuotient_double (N / d) (J - 1)
  have hprevScale' : (N / d) / (2 : ℝ) ^ (J - 1) =
      2 * ((N / d) / (2 : ℝ) ^ J) := by
    simpa [Nat.sub_add_cancel hJpos] using hprevScale
  have hcutHalf : N ^ (1 - κ) / (2 * d) <
      (N / d) / (2 : ℝ) ^ J := by
    calc
      N ^ (1 - κ) / (2 * d) = (N ^ (1 - κ) / d) / 2 := by ring
      _ < ((N / d) / (2 : ℝ) ^ (J - 1)) / 2 :=
        (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)
          (by norm_num : (0 : ℝ) < 2)).2 (by simpa using hprev)
      _ = (N / d) / (2 : ℝ) ^ J := by rw [hprevScale']; ring
  exact hcutHalf.le.trans hPmono

/-- The finite dyadic remainder contributes at most `N^-κ` after the
normalization `d/N`. -/
theorem monomial_remainder_normalized_bound
    {N d κ : ℝ} (hN : 1 < N) (hd : 0 < d) (hκ : 0 < κ)
    (J : ℕ)
    (hcut : (N / d) / (2 : ℝ) ^ J ≤ N ^ (1 - κ) / d) :
    (d / N) *
      ((realIntegerInterval 0 ((N / d) / (2 : ℝ) ^ J)).card : ℝ) ≤
      N ^ (-κ) := by
  have hNpos : 0 < N := by linarith
  have hY : 0 ≤ (N / d) / (2 : ℝ) ^ J := by positivity
  have hcard := realIntegerInterval_zero_card_le ((N / d) / (2 : ℝ) ^ J) hY
  have hcard' :
      ((realIntegerInterval 0 ((N / d) / (2 : ℝ) ^ J)).card : ℝ) ≤
        N ^ (1 - κ) / d := hcard.trans hcut
  have hscale := mul_le_mul_of_nonneg_left hcard'
    (le_of_lt (div_pos hd hNpos))
  have hfactor : N ^ (1 - κ) = N * N ^ (-κ) := by
    calc
      N ^ (1 - κ) = N ^ (1 + (-κ)) := by congr 1 <;> ring
      _ = N ^ (1 : ℝ) * N ^ (-κ) := Real.rpow_add hNpos 1 (-κ)
      _ = N * N ^ (-κ) := by rw [Real.rpow_one]
  have hid : (d / N) * (N ^ (1 - κ) / d) = N ^ (-κ) := by
    field_simp
    exact hfactor
  calc
    (d / N) *
        ((realIntegerInterval 0 ((N / d) / (2 : ℝ) ^ J)).card : ℝ) ≤
        (d / N) * (N ^ (1 - κ) / d) := hscale
    _ = N ^ (-κ) := hid

/-- The real forward difference `Δₐ f(t)=f(t+a)-f(t)` from the blueprint. -/
def realForwardDifference (a : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f (t + a) - f t

/-- The real-step forward difference used in the calculus lemmas of the
derivative-test blueprint. -/
def realForwardDifferenceR (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f (t + a) - f t

/-- Iterated real-step differences, applied in the tuple order used by the
derivative-test blueprint. -/
def iteratedRealForwardDifferenceR (f : ℝ → ℝ) : List ℝ → ℝ → ℝ
  | [] => f
  | a :: rest => iteratedRealForwardDifferenceR (realForwardDifferenceR a f) rest

/-- Nested shift-box integration in the order of the blueprint: the first
shift is integrated innermost and the last shift outermost. -/
noncomputable def nestedRealShiftBoxIntegral (f : ℝ → ℝ) : List ℝ → ℝ → ℝ
  | [], t => f t
  | a :: rest, t =>
      nestedRealShiftBoxIntegral (fun s => ∫ u in 0..a, f (s + u)) rest t

/-- Integrating a continuous function over a fixed translated interval
produces a continuous function of the translation parameter. -/
theorem continuousOn_shiftIntervalIntegral {f : ℝ → ℝ} {t upper a : ℝ}
    (ha : 0 ≤ a) (htu : t ≤ upper)
    (hf : ContinuousOn f (Set.Icc t (upper + a))) :
    ContinuousOn (fun s => ∫ u in 0..a, f (s + u)) (Set.Icc t upper) := by
  have hfull : t ≤ upper + a := by linarith
  have hfullInt : MeasureTheory.IntegrableOn f (Set.Icc t (upper + a)) :=
    hf.integrableOn_compact isCompact_Icc
  let P : ℝ → ℝ := fun z => ∫ u in t..z, f u
  have hP : ContinuousOn P (Set.Icc t (upper + a)) := by
    have hfullInt' : MeasureTheory.IntegrableOn f
        (Set.uIcc t (upper + a)) MeasureTheory.volume := by
      simpa [Set.uIcc_of_le hfull] using hfullInt
    have h := intervalIntegral.continuousOn_primitive_interval
      hfullInt'
    simpa [P, Set.uIcc_of_le hfull] using h
  have hshift : ContinuousOn (fun s : ℝ => s + a) (Set.Icc t upper) :=
    (continuous_id.add continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => s + a)
      (Set.Icc t upper) (Set.Icc t (upper + a)) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hshiftP := hP.comp hshift hmaps
  have hbaseP : ContinuousOn P (Set.Icc t upper) := hP.mono (by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 (by linarith [ha])⟩)
  have hQ : ContinuousOn (fun s => P (s + a) - P s) (Set.Icc t upper) :=
    hshiftP.sub hbaseP
  have hIntSeg : ∀ l r, t ≤ l → l ≤ r → r ≤ upper + a →
      IntervalIntegrable f MeasureTheory.volume l r := by
    intro l r htl hlr hru
    have hcc : ContinuousOn f (Set.Icc l r) := hf.mono (by
      intro z hz
      exact ⟨le_trans htl hz.1, hz.2.trans hru⟩)
    have hucc : ContinuousOn f (Set.uIcc l r) := by
      simpa [Set.uIcc_of_le hlr] using hcc
    exact hucc.intervalIntegrable
  have hEq : Set.EqOn (fun s => ∫ u in 0..a, f (s + u))
      (fun s => P (s + a) - P s) (Set.Icc t upper) := by
    intro s hs
    have hts : t ≤ s := hs.1
    have hsu : s ≤ upper := hs.2
    have hsa : s ≤ s + a := le_add_of_nonneg_right ha
    have hsau : s + a ≤ upper + a := by nlinarith [hsu]
    have htrans := intervalIntegral.integral_comp_add_right
      (a := 0) (b := a) (f := f) s
    have htrans' :
        ∫ u in 0..a, f (s + u) = ∫ u in s..s + a, f u := by
      simp [add_comm]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hIntSeg t s le_rfl hts (le_trans hsu (by linarith [ha])))
      (hIntSeg s (s + a) hts hsa hsau)
    dsimp [P]
    linarith
  exact hQ.congr hEq

/-- A single real-step difference of derivative level `k` differentiates to
the same difference at level `k+1` on the exact interior of its domain. -/
theorem HalfOpenCkData.realForwardDifferenceR_hasDerivAt
    {x Y a t : ℝ} {order k : ℕ} (data : HalfOpenCkData x Y order)
    (hk : k < order) (ha : 0 ≤ a) (htx : x < t) (htY : t + a < x + Y) :
    HasDerivAt (realForwardDifferenceR a (data.derivative k))
      (data.derivative (k + 1) (t + a) - data.derivative (k + 1) t) t := by
  have hta : x < t + a := lt_of_lt_of_le htx (le_add_of_nonneg_right ha)
  have htmem : t ∈ Set.Ioo x (x + Y) :=
    ⟨htx, lt_of_le_of_lt (le_add_of_nonneg_right ha) htY⟩
  have htamem : t + a ∈ Set.Ioo x (x + Y) := ⟨hta, htY⟩
  have hshift : HasDerivAt (fun s : ℝ => data.derivative k (s + a))
      (data.derivative (k + 1) (t + a)) t := by
    have hid : HasDerivAt (fun s : ℝ => s + a) 1 t :=
      (hasDerivAt_id t).add_const a
    have hcomp := (data.hasDerivAt k hk (t + a) htamem).comp t hid
    simpa [Function.comp_def] using hcomp
  have hbase := data.hasDerivAt k hk t htmem
  change HasDerivAt (fun s : ℝ => data.derivative k (s + a) -
    data.derivative k s) _ _
  exact hshift.sub hbase

/-- A positive real difference lowers the available derivative order by one
and preserves the half-open endpoint convention on the shrunken interval. -/
def HalfOpenCkData.realForwardDifferenceR_data
    {x Y a : ℝ} {order : ℕ} (data : HalfOpenCkData x Y order)
    (horder : 0 < order) (ha : 0 < a) (haY : a < Y) :
    HalfOpenCkData x (Y - a) (order - 1) where
  length_pos := sub_pos.mpr haY
  derivative k := realForwardDifferenceR a (data.derivative k)
  continuous k hk := by
    have hkorder : k + 1 ≤ order := by omega
    have hshift : ContinuousOn (fun t : ℝ => t + a)
        (Set.Ioc x (x + (Y - a))) :=
      (continuous_id.add continuous_const).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => t + a)
        (Set.Ioc x (x + (Y - a))) (Set.Ioc x (x + Y)) := by
      intro t ht
      change x < t ∧ t ≤ x + (Y - a) at ht
      change x < t + a ∧ t + a ≤ x + Y
      constructor <;> linarith
    have hshifted := (data.continuous k (by omega)).comp hshift hmaps
    have hbase : ContinuousOn (data.derivative k)
        (Set.Ioc x (x + (Y - a))) :=
      (data.continuous k (by omega)).mono (by
        intro t ht
        exact ⟨ht.1, le_trans ht.2 (by linarith)⟩)
    change ContinuousOn (fun t : ℝ => data.derivative k (t + a) -
      data.derivative k t) (Set.Ioc x (x + (Y - a)))
    exact hshifted.sub hbase
  hasDerivAt k hk t ht := by
    have hkorder : k < order := by omega
    have hta : x < t + a := lt_of_lt_of_le ht.1 (le_add_of_nonneg_right (le_of_lt ha))
    have htY : t + a < x + Y := by
      have := ht.2
      change t < x + (Y - a) at this
      linarith
    exact data.realForwardDifferenceR_hasDerivAt hkorder (le_of_lt ha) ht.1 htY
  right_hasDerivWithinAt k hk := by
    have hkorder : k < order := by omega
    let b : ℝ := x + (Y - a)
    have hbx : x < b := by dsimp [b]; linarith
    have hbY : b < x + Y := by dsimp [b]; linarith
    have hshiftMap : Set.MapsTo (fun t : ℝ => t + a)
        (Set.Iic b) (Set.Iic (x + Y)) := by
      intro t ht
      change t ≤ b at ht
      change t + a ≤ x + Y
      linarith
    have hid : HasDerivWithinAt (fun t : ℝ => t + a) 1 (Set.Iic b) b :=
      (hasDerivWithinAt_id b (Set.Iic b)).add_const a
    have hbadd : b + a = x + Y := by dsimp [b]; ring
    have hright : HasDerivWithinAt (data.derivative k)
        (data.derivative (k + 1) (b + a)) (Set.Iic (b + a)) (b + a) := by
      simpa [hbadd] using data.right_hasDerivWithinAt k hkorder
    have hshift : HasDerivWithinAt (fun t : ℝ => data.derivative k (t + a))
        (data.derivative (k + 1) (b + a)) (Set.Iic b) b := by
      have h := hright.comp b hid (by
      intro t ht
      change t ≤ b at ht
      change t + a ≤ b + a
      linarith)
      simpa [Function.comp_def, mul_one] using h
    have hbase := (data.hasDerivAt k hkorder b ⟨hbx, hbY⟩).hasDerivWithinAt
        (s := Set.Iic b)
    change HasDerivWithinAt (fun t : ℝ => data.derivative k (t + a) -
      data.derivative k t) _ (Set.Iic b) b
    exact hshift.sub hbase

theorem list_sum_nonneg_of_forall_pos (shifts : List ℝ)
    (hpos : ∀ a ∈ shifts, 0 < a) : 0 ≤ shifts.sum := by
  induction shifts with
  | nil => simp
  | cons a rest ih =>
    have ha := hpos a (by simp)
    have hrest : ∀ z ∈ rest, 0 < z := by
      intro z hz
      exact hpos z (by simp [hz])
    simp only [List.sum_cons]
    linarith [ih hrest]

theorem list_sum_nonneg_of_forall_nonneg (shifts : List ℝ)
    (hnonneg : ∀ a ∈ shifts, 0 ≤ a) : 0 ≤ shifts.sum := by
  induction shifts with
  | nil => simp
  | cons a rest ih =>
    have ha := hnonneg a (by simp)
    have hrest : ∀ z ∈ rest, 0 ≤ z := by
      intro z hz
      exact hnonneg z (by simp [hz])
    simp only [List.sum_cons]
    linarith [ih hrest]

/-- If two integrands agree on the full interval reached by a nonnegative
shift list, then their nested box integrals agree. -/
theorem nestedRealShiftBoxIntegral_congr {f g : ℝ → ℝ}
    (shifts : List ℝ) (t : ℝ)
    (hnonneg : ∀ a ∈ shifts, 0 ≤ a)
    (hfg : ∀ s ∈ Set.Icc t (t + shifts.sum), f s = g s) :
    nestedRealShiftBoxIntegral f shifts t =
      nestedRealShiftBoxIntegral g shifts t := by
  induction shifts generalizing t f g with
  | nil =>
    change f t = g t
    exact hfg t (by simp)
  | cons a rest ih =>
    have ha : 0 ≤ a := hnonneg a (by simp)
    have hrestnonneg : ∀ z ∈ rest, 0 ≤ z := by
      intro z hz
      exact hnonneg z (by simp [hz])
    have hrestsum := list_sum_nonneg_of_forall_nonneg rest hrestnonneg
    have hEq : ∀ s ∈ Set.Icc t (t + rest.sum),
        (∫ u in 0..a, f (s + u)) = ∫ u in 0..a, g (s + u) := by
      intro s hs
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : 0 ≤ u ∧ u ≤ a := by
        simpa [Set.uIcc_of_le ha] using hu
      apply hfg (s + u)
      constructor
      · linarith [hs.1]
      · have hsum : (a :: rest).sum = a + rest.sum := List.sum_cons
        rw [hsum]
        linarith [hs.2]
    change nestedRealShiftBoxIntegral
      (fun s => ∫ u in 0..a, f (s + u)) rest t =
      nestedRealShiftBoxIntegral
      (fun s => ∫ u in 0..a, g (s + u)) rest t
    exact ih t hrestnonneg hEq

/-- The nested box integral is continuous in its base point when the
integrand is continuous on the full compact interval reached by the shifts. -/
theorem nestedRealShiftBoxIntegral_continuousOn {f : ℝ → ℝ}
    (shifts : List ℝ) {t upper : ℝ}
    (hnonneg : ∀ a ∈ shifts, 0 ≤ a) (htu : t ≤ upper)
    (hf : ContinuousOn f (Set.Icc t (upper + shifts.sum))) :
    ContinuousOn (fun s => nestedRealShiftBoxIntegral f shifts s)
      (Set.Icc t upper) := by
  induction shifts generalizing t upper f with
  | nil =>
    change ContinuousOn f (Set.Icc t upper)
    simpa using hf
  | cons a rest ih =>
    have ha : 0 ≤ a := hnonneg a (by simp)
    have hrestnonneg : ∀ z ∈ rest, 0 ≤ z := by
      intro z hz
      exact hnonneg z (by simp [hz])
    have htu' : t ≤ upper + rest.sum := by
      have hsum := list_sum_nonneg_of_forall_nonneg rest hrestnonneg
      linarith
    have hf' : ContinuousOn f
        (Set.Icc t ((upper + rest.sum) + a)) := by
      apply hf.mono
      intro s hs
      constructor
      · exact hs.1
      · have hsum : (a :: rest).sum = a + rest.sum := List.sum_cons
        rw [hsum]
        calc
          s ≤ upper + rest.sum + a := hs.2
          _ = upper + (a + rest.sum) := by ring
    have hG := continuousOn_shiftIntervalIntegral ha htu' hf'
    change ContinuousOn
      (fun s => nestedRealShiftBoxIntegral
        (fun z => ∫ u in 0..a, f (z + u)) rest s) (Set.Icc t upper)
    exact ih hrestnonneg htu hG

/-- Pointwise bounds on a continuous integrand pass through the nested box
integral with the exact product of shift lengths. -/
theorem nestedRealShiftBoxIntegral_bounds {f : ℝ → ℝ}
    (shifts : List ℝ) (t lower upper : ℝ)
    (hnonneg : ∀ a ∈ shifts, 0 ≤ a)
    (hf : ContinuousOn f (Set.Icc t (t + shifts.sum)))
    (hlo : ∀ s ∈ Set.Icc t (t + shifts.sum), lower ≤ f s)
    (hhi : ∀ s ∈ Set.Icc t (t + shifts.sum), f s ≤ upper) :
    lower * shifts.prod ≤ nestedRealShiftBoxIntegral f shifts t ∧
      nestedRealShiftBoxIntegral f shifts t ≤ upper * shifts.prod := by
  induction shifts generalizing t lower upper f with
  | nil =>
    change lower * 1 ≤ f t ∧ f t ≤ upper * 1
    constructor
    · simpa using hlo t (by simp)
    · simpa using hhi t (by simp)
  | cons a rest ih =>
    have ha : 0 ≤ a := hnonneg a (by simp)
    have hrestnonneg : ∀ z ∈ rest, 0 ≤ z := by
      intro z hz
      exact hnonneg z (by simp [hz])
    have hrestsum := list_sum_nonneg_of_forall_nonneg rest hrestnonneg
    let G : ℝ → ℝ := fun s => ∫ u in 0..a, f (s + u)
    have hfull : ∀ s ∈ Set.Icc t (t + rest.sum),
        ∀ u ∈ Set.Icc 0 a, s + u ∈ Set.Icc t (t + (a :: rest).sum) := by
      intro s hs u hu
      constructor
      · linarith [hs.1, hu.1]
      · have hsum : (a :: rest).sum = a + rest.sum := List.sum_cons
        rw [hsum]
        linarith [hs.2, hu.2]
    have hGcont : ContinuousOn G (Set.Icc t (t + rest.sum)) := by
      have hfc : ContinuousOn f (Set.Icc t ((t + rest.sum) + a)) := by
        apply hf.mono
        intro s hs
        constructor
        · exact hs.1
        · have hsum : (a :: rest).sum = a + rest.sum := List.sum_cons
          rw [hsum]
          linarith [hs.2]
      have h := continuousOn_shiftIntervalIntegral ha (by linarith) hfc
      simpa [G] using h
    have hGlo : ∀ s ∈ Set.Icc t (t + rest.sum), lower * a ≤ G s := by
      intro s hs
      have hfuCont : ContinuousOn (fun u : ℝ => f (s + u)) (Set.Icc 0 a) := by
        have hcont : ContinuousOn (fun u : ℝ => s + u) (Set.Icc 0 a) :=
          (continuous_const.add continuous_id).continuousOn
        have hmaps : Set.MapsTo (fun u : ℝ => s + u) (Set.Icc 0 a)
            (Set.Icc t (t + (a :: rest).sum)) := by
          intro u hu
          have hr := hfull s hs u hu
          constructor <;> linarith [hr.1, hr.2]
        exact hf.comp hcont hmaps
      have hfu : IntervalIntegrable (fun u : ℝ => f (s + u))
          MeasureTheory.volume 0 a := by
        have huc : ContinuousOn (fun u : ℝ => f (s + u)) (Set.uIcc 0 a) := by
          simpa [Set.uIcc_of_le ha] using hfuCont
        exact huc.intervalIntegrable
      have hconst : IntervalIntegrable (fun _ : ℝ => lower)
          MeasureTheory.volume 0 a := continuousOn_const.intervalIntegrable
      have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
        ha hconst hfu (by
          intro u hu
          exact hlo (s + u) (hfull s hs u (by
            simpa [Set.uIcc_of_le ha] using hu)))
      have hconstval : (∫ u in 0..a, lower) = lower * a := by
        simp [intervalIntegral.integral_const, mul_comm]
      change lower * a ≤ ∫ u in 0..a, f (s + u)
      rw [← hconstval]
      exact hmono
    have hGhi : ∀ s ∈ Set.Icc t (t + rest.sum), G s ≤ upper * a := by
      intro s hs
      have hfuCont : ContinuousOn (fun u : ℝ => f (s + u)) (Set.Icc 0 a) := by
        have hcont : ContinuousOn (fun u : ℝ => s + u) (Set.Icc 0 a) :=
          (continuous_const.add continuous_id).continuousOn
        have hmaps : Set.MapsTo (fun u : ℝ => s + u) (Set.Icc 0 a)
            (Set.Icc t (t + (a :: rest).sum)) := by
          intro u hu
          have hr := hfull s hs u hu
          constructor <;> linarith [hr.1, hr.2]
        exact hf.comp hcont hmaps
      have hfu : IntervalIntegrable (fun u : ℝ => f (s + u))
          MeasureTheory.volume 0 a := by
        have huc : ContinuousOn (fun u : ℝ => f (s + u)) (Set.uIcc 0 a) := by
          simpa [Set.uIcc_of_le ha] using hfuCont
        exact huc.intervalIntegrable
      have hconst : IntervalIntegrable (fun _ : ℝ => upper)
          MeasureTheory.volume 0 a := continuousOn_const.intervalIntegrable
      have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
        ha hfu hconst (by
          intro u hu
          exact hhi (s + u) (hfull s hs u (by
            simpa [Set.uIcc_of_le ha] using hu)))
      have hconstval : (∫ u in 0..a, upper) = upper * a := by
        simp [intervalIntegral.integral_const, mul_comm]
      change (∫ u in 0..a, f (s + u)) ≤ upper * a
      rw [← hconstval]
      exact hmono
    have hih := ih t (lower * a) (upper * a) hrestnonneg hGcont hGlo hGhi
    constructor
    · change lower * (a * rest.prod) ≤ nestedRealShiftBoxIntegral G rest t
      have hprod : lower * (a * rest.prod) = (lower * a) * rest.prod := by ring
      rw [hprod]
      exact hih.1
    · change nestedRealShiftBoxIntegral G rest t ≤ upper * (a * rest.prod)
      have hprod : upper * (a * rest.prod) = (upper * a) * rest.prod := by ring
      rw [hprod]
      exact hih.2

/-- One-step integral formula for consecutive derivatives, including an
interval whose right endpoint is the included endpoint `x+Y`. -/
theorem HalfOpenCkData.intervalIntegral_derivative_eq_sub
    {x Y a t : ℝ} {order k : ℕ} (data : HalfOpenCkData x Y order)
    (hk : k < order) (ha : 0 ≤ a) (htx : x < t)
    (htend : t + a ≤ x + Y) :
    ∫ u in t..t + a, data.derivative (k + 1) u =
      data.derivative k (t + a) - data.derivative k t := by
  have hright : t ≤ t + a := le_add_of_nonneg_right ha
  have hcont : ContinuousOn (data.derivative k) (Set.Icc t (t + a)) :=
    (data.continuous k (by omega)).mono (by
      intro u hu
      exact ⟨lt_of_lt_of_le htx hu.1, hu.2.trans htend⟩)
  have hderiv : ∀ u ∈ Set.Ioo t (t + a),
      HasDerivAt (data.derivative k) (data.derivative (k + 1) u) u := by
    intro u hu
    apply data.hasDerivAt k hk u
    exact ⟨lt_trans htx hu.1, lt_of_lt_of_le hu.2 htend⟩
  have hint : IntervalIntegrable (data.derivative (k + 1))
      MeasureTheory.volume t (t + a) := by
    have hcont' : ContinuousOn (data.derivative (k + 1))
        (Set.Icc t (t + a)) :=
      (data.continuous (k + 1) (by omega)).mono (by
        intro u hu
        exact ⟨lt_of_lt_of_le htx hu.1, hu.2.trans htend⟩)
    have huIcc : Set.uIcc t (t + a) = Set.Icc t (t + a) :=
      Set.uIcc_of_le hright
    have hcont'' : ContinuousOn (data.derivative (k + 1))
        (Set.uIcc t (t + a)) := by simpa [huIcc] using hcont'
    exact hcont''.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hright hcont
    hderiv hint

/-- The general finite-shift box integral identity. The first shift is
integrated innermost, matching `Δ_{a_h}⋯Δ_{a_1}` exactly. -/
theorem HalfOpenCkData.iteratedDifference_boxIntegral
    {x Y t : ℝ} {order : ℕ} (data : HalfOpenCkData x Y order)
    (shifts : List ℝ) (hlen : shifts.length ≤ order)
    (hpos : ∀ a ∈ shifts, 0 < a) (htx : x < t)
    (htend : t + shifts.sum ≤ x + Y) :
    nestedRealShiftBoxIntegral (data.derivative shifts.length) shifts t =
      iteratedRealForwardDifferenceR (data.derivative 0) shifts t := by
  induction shifts generalizing Y t order data with
  | nil =>
    change data.derivative 0 t = data.derivative 0 t
    rfl
  | cons a rest ih =>
    have ha : 0 < a := hpos a (by simp)
    have hrestpos : ∀ z ∈ rest, 0 < z := by
      intro z hz
      exact hpos z (by simp [hz])
    have hrestnonneg := list_sum_nonneg_of_forall_pos rest hrestpos
    have hlen' : rest.length + 1 ≤ order := by simpa using hlen
    have horder : 0 < order := by omega
    have hlenrest : rest.length ≤ order - 1 := by omega
    have hsumend : t + (a + rest.sum) ≤ x + Y := by
      simpa [List.sum_cons] using htend
    have haY : a < Y := by linarith
    have htail : t + rest.sum ≤ x + (Y - a) := by linarith
    let hdata := data.realForwardDifferenceR_data horder ha haY
    have hEq : ∀ s ∈ Set.Icc t (t + rest.sum),
        (∫ u in 0..a, data.derivative (rest.length + 1) (s + u)) =
          hdata.derivative rest.length s := by
      intro s hs
      have hsx : x < s := lt_of_lt_of_le htx hs.1
      have hsend : s + a ≤ x + Y := by linarith [hs.2, hsumend]
      have hftc := data.intervalIntegral_derivative_eq_sub
        (k := rest.length) (by omega) (le_of_lt ha) hsx hsend
      have htrans := (intervalIntegral.integral_comp_add_right
        (a := 0) (b := a) (f := data.derivative (rest.length + 1)) s).symm
      have htrans' :
          ∫ u in s..s + a, data.derivative (rest.length + 1) u =
            ∫ u in 0..a, data.derivative (rest.length + 1) (u + s) := by
        simpa only [zero_add, add_comm a s] using htrans
      rw [htrans'] at hftc
      change (∫ u in 0..a,
          data.derivative (rest.length + 1) (s + u)) =
        data.derivative rest.length (s + a) - data.derivative rest.length s
      simpa [add_comm] using hftc
    have hbox := nestedRealShiftBoxIntegral_congr rest t
      (fun z hz => le_of_lt (hrestpos z hz)) hEq
    have hih := ih hdata hlenrest hrestpos htx htail
    change nestedRealShiftBoxIntegral
        (fun s => ∫ u in 0..a,
          data.derivative (rest.length + 1) (s + u)) rest t =
      iteratedRealForwardDifferenceR
        (realForwardDifferenceR a (data.derivative 0)) rest t
    calc
      nestedRealShiftBoxIntegral
          (fun s => ∫ u in 0..a,
            data.derivative (rest.length + 1) (s + u)) rest t =
          nestedRealShiftBoxIntegral (hdata.derivative rest.length) rest t := hbox
      _ = iteratedRealForwardDifferenceR (hdata.derivative 0) rest t := hih
      _ = iteratedRealForwardDifferenceR
          (realForwardDifferenceR a (data.derivative 0)) rest t := by
          simp [hdata, HalfOpenCkData.realForwardDifferenceR_data]

/-- Apply the finite-shift box identity to the second derivative family.
This is the calculus identity needed for `f_a''` in `ld:difference-integral`.-/
theorem HalfOpenCkData.secondDerivative_iteratedDifference_boxIntegral
    {x Y t : ℝ} {order : ℕ} (data : HalfOpenCkData x Y order)
    (shifts : List ℝ) (hlen : shifts.length + 2 ≤ order)
    (hpos : ∀ a ∈ shifts, 0 < a) (htx : x < t)
    (htend : t + shifts.sum ≤ x + Y) :
    nestedRealShiftBoxIntegral (data.derivative (shifts.length + 2)) shifts t =
      iteratedRealForwardDifferenceR (data.derivative 2) shifts t := by
  let tail := data.derivativeTail (offset := 2) (by omega)
  have hbox := tail.iteratedDifference_boxIntegral shifts (by omega)
    hpos htx htend
  change nestedRealShiftBoxIntegral (tail.derivative shifts.length) shifts t =
    iteratedRealForwardDifferenceR (tail.derivative 0) shifts t at hbox
  simpa [tail, HalfOpenCkData.derivativeTail] using hbox

/-- Iterated real-step differences retain the exact shrunken half-open
domain and lose one derivative at each positive shift. -/
def HalfOpenCkData.iteratedDifferenceData
    {x Y : ℝ} {order : ℕ} (data : HalfOpenCkData x Y order)
    (shifts : List ℝ) (hpos : ∀ a ∈ shifts, 0 < a)
    (hsum : shifts.sum < Y) (hlen : shifts.length ≤ order) :
    HalfOpenCkData x (Y - shifts.sum) (order - shifts.length) := by
  induction shifts generalizing Y order with
  | nil =>
    refine {
      length_pos := ?_
      derivative := data.derivative
      continuous := ?_
      hasDerivAt := ?_
      right_hasDerivWithinAt := ?_ }
    · simpa using data.length_pos
    · intro k hk
      simpa using data.continuous k (by simpa using hk)
    · intro k hk t ht
      simpa using data.hasDerivAt k (by simpa using hk) t (by simpa using ht)
    · intro k hk
      simpa using data.right_hasDerivWithinAt k (by simpa using hk)
  | cons a rest ih =>
    have ha : 0 < a := hpos a (by simp)
    have hrestpos : ∀ z ∈ rest, 0 < z := by
      intro z hz
      exact hpos z (by simp [hz])
    have hrestnonneg := list_sum_nonneg_of_forall_pos rest hrestpos
    have hsumrest : rest.sum < Y - a := by
      simp only [List.sum_cons] at hsum
      linarith
    have horder : 0 < order := by
      have hlen' : rest.length + 1 ≤ order := by simpa using hlen
      omega
    have hdata := data.realForwardDifferenceR_data horder ha (by linarith)
    have hlenrest : rest.length ≤ order - 1 := by
      have hlen' : rest.length + 1 ≤ order := by simpa using hlen
      omega
    let tail := ih hdata hrestpos hsumrest hlenrest
    have hY : (Y - a) - rest.sum = Y - (a + rest.sum) := by ring
    have horderEq : (order - 1) - rest.length = order - (rest.length + 1) := by omega
    refine {
      length_pos := ?_
      derivative := tail.derivative
      continuous := ?_
      hasDerivAt := ?_
      right_hasDerivWithinAt := ?_ }
    · simpa [List.sum_cons, hY] using tail.length_pos
    · intro k hk
      have hkTail : k ≤ (order - 1) - rest.length := by
        simpa [List.length_cons, ← horderEq] using hk
      simpa [hY] using tail.continuous k hkTail
    · intro k hk t ht
      have hkTail : k < (order - 1) - rest.length := by
        simpa [List.length_cons, ← horderEq] using hk
      have htTail : t ∈ Set.Ioo x (x + ((Y - a) - rest.sum)) := by
        simpa [hY] using ht
      simpa [hY, horderEq] using tail.hasDerivAt k hkTail t htTail
    · intro k hk
      have hkTail : k < (order - 1) - rest.length := by
        simpa [List.length_cons, ← horderEq] using hk
      simpa [hY, horderEq] using tail.right_hasDerivWithinAt k hkTail

/-- Each derivative level of the iterated difference data is the same
iterated real difference applied to the corresponding original derivative. -/
theorem HalfOpenCkData.iteratedDifferenceData_derivative
    {x Y : ℝ} {order k : ℕ} (data : HalfOpenCkData x Y order)
    (shifts : List ℝ) (hpos : ∀ a ∈ shifts, 0 < a)
    (hsum : shifts.sum < Y) (hlen : shifts.length ≤ order)
    (hk : k ≤ order - shifts.length) :
    (data.iteratedDifferenceData shifts hpos hsum hlen).derivative k =
      iteratedRealForwardDifferenceR (data.derivative k) shifts := by
  induction shifts generalizing Y order data with
  | nil =>
    simp [HalfOpenCkData.iteratedDifferenceData, iteratedRealForwardDifferenceR]
  | cons a rest ih =>
    have ha : 0 < a := hpos a (by simp)
    have hrestpos : ∀ z ∈ rest, 0 < z := by
      intro z hz
      exact hpos z (by simp [hz])
    have hrestnonneg := list_sum_nonneg_of_forall_pos rest hrestpos
    have hsumrest : rest.sum < Y - a := by
      simp only [List.sum_cons] at hsum
      linarith
    have hlen' : rest.length + 1 ≤ order := by simpa using hlen
    have horder : 0 < order := by omega
    have hlenrest : rest.length ≤ order - 1 := by omega
    have hhk : k ≤ (order - 1) - rest.length := by
      have hsub : order - (rest.length + 1) = (order - 1) - rest.length := by omega
      simpa [List.length_cons, ← hsub] using hk
    let hdata := data.realForwardDifferenceR_data horder ha (by linarith)
    have hrec := ih hdata hrestpos hsumrest hlenrest hhk
    simpa [HalfOpenCkData.iteratedDifferenceData, hdata,
      HalfOpenCkData.realForwardDifferenceR_data, iteratedRealForwardDifferenceR,
      realForwardDifferenceR] using hrec

/-- The second derivative of an iterated real difference lies between the
highest-derivative bounds times the exact shift product. -/
theorem HalfOpenCkData.iteratedSecondDerivative_product_bounds
    {x Y t lower upper : ℝ} {order : ℕ}
    (data : HalfOpenCkData x Y order) (shifts : List ℝ)
    (hlen : shifts.length + 2 = order)
    (hpos : ∀ a ∈ shifts, 0 < a) (htx : x < t)
    (htend : t + shifts.sum ≤ x + Y)
    (hderiv : ∀ s ∈ Set.Ioc x (x + Y),
      lower ≤ data.derivative order s ∧ data.derivative order s ≤ upper) :
    lower * shifts.prod ≤
        (data.iteratedDifferenceData shifts hpos (by linarith) (by omega)).derivative 2 t ∧
      (data.iteratedDifferenceData shifts hpos (by linarith) (by omega)).derivative 2 t ≤
        upper * shifts.prod := by
  have hnonneg : ∀ a ∈ shifts, 0 ≤ a := fun a ha => le_of_lt (hpos a ha)
  have hreach : Set.Icc t (t + shifts.sum) ⊆ Set.Ioc x (x + Y) := by
    intro s hs
    exact ⟨lt_of_lt_of_le htx hs.1, le_trans hs.2 htend⟩
  have hcont : ContinuousOn (data.derivative (shifts.length + 2))
      (Set.Icc t (t + shifts.sum)) :=
    (data.continuous (shifts.length + 2) (by omega)).mono hreach
  have hlo : ∀ s ∈ Set.Icc t (t + shifts.sum),
      lower ≤ data.derivative (shifts.length + 2) s := by
    intro s hs
    simpa [← hlen] using (hderiv s (hreach hs)).1
  have hhi : ∀ s ∈ Set.Icc t (t + shifts.sum),
      data.derivative (shifts.length + 2) s ≤ upper := by
    intro s hs
    simpa [← hlen] using (hderiv s (hreach hs)).2
  have hbox := nestedRealShiftBoxIntegral_bounds shifts t lower upper
    hnonneg hcont hlo hhi
  let differenceData := data.iteratedDifferenceData shifts hpos (by linarith) (by omega)
  have hderivEq := data.iteratedDifferenceData_derivative shifts hpos
    (by linarith) (by omega) (k := 2) (by omega)
  have hboxEq := data.secondDerivative_iteratedDifference_boxIntegral
    shifts (hlen.le) hpos htx htend
  have heq : differenceData.derivative 2 t =
      nestedRealShiftBoxIntegral (data.derivative (shifts.length + 2)) shifts t := by
    exact (congrFun hderivEq t).trans hboxEq.symm
  rw [heq]
  exact hbox

/-- Exact finite geometric sum used in the capped-power shift allocation. -/
theorem sum_two_pow_succ_range (h : ℕ) :
    (∑ i ∈ Finset.range h, (2 : ℝ) ^ (i + 1)) = (2 : ℝ) ^ (h + 1) - 2 := by
  calc
    (∑ i ∈ Finset.range h, (2 : ℝ) ^ (i + 1)) =
        (∑ i ∈ Finset.range h, (2 : ℝ) ^ i) * 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
    _ = ((2 : ℝ) ^ h - 1) * 2 := by
      have hg := geom_sum_mul (2 : ℝ) h
      have hsum : (∑ i ∈ Finset.range h, (2 : ℝ) ^ i) = (2 : ℝ) ^ h - 1 := by
        nlinarith [hg]
      rw [hsum]
    _ = (2 : ℝ) ^ (h + 1) - 2 := by rw [pow_succ]; ring

/-- The capped profile whose endpoint range supplies the logarithmic shift
allocation. -/
def derivativeCappedShiftProfile (h : ℕ) (v t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range h, min ((2 : ℝ) ^ (i + 1) * t) v

theorem derivativeCappedShiftProfile_continuousOn (h : ℕ) (v : ℝ) :
    ContinuousOn (derivativeCappedShiftProfile h v) (Set.Icc 0 (v / 2)) := by
  unfold derivativeCappedShiftProfile
  apply continuousOn_finsetSum
  intro i hi
  exact ((continuous_const.mul continuous_id).min continuous_const).continuousOn

theorem derivativeCappedShiftProfile_zero (h : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    derivativeCappedShiftProfile h v 0 = 0 := by
  unfold derivativeCappedShiftProfile
  apply Finset.sum_eq_zero
  intro i hi
  simp [hv]

theorem derivativeCappedShiftProfile_right (h : ℕ) (hh : 1 ≤ h)
    {v : ℝ} (hv : 0 ≤ v) :
    derivativeCappedShiftProfile h v (v / 2) = (h : ℝ) * v := by
  unfold derivativeCappedShiftProfile
  have hterm (i : ℕ) : min ((2 : ℝ) ^ (i + 1) * (v / 2)) v = v := by
    apply min_eq_right
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ i :=
      one_le_pow₀ (by norm_num)
    rw [pow_succ]
    nlinarith [hpow, hv]
  simp_rw [hterm]
  simp [Finset.sum_const, Finset.card_range]

theorem exists_derivativeCappedShiftProfile_eq (h : ℕ) (hh : 1 ≤ h)
    {v y : ℝ} (hv : 0 < v) (hy : 0 ≤ y) (hyh : y ≤ (h : ℝ) * v) :
    ∃ t ∈ Set.Icc 0 (v / 2), derivativeCappedShiftProfile h v t = y := by
  have hcont := derivativeCappedShiftProfile_continuousOn h v
  have hzero := derivativeCappedShiftProfile_zero h (le_of_lt hv)
  have hright := derivativeCappedShiftProfile_right h hh (le_of_lt hv)
  have hinterval : 0 ≤ v / 2 := by linarith
  have himage := intermediate_value_Icc hinterval hcont ⟨by simpa [hzero] using hy,
    by simpa [hright] using hyh⟩
  rcases himage with ⟨t, ht, hty⟩
  exact ⟨t, ht, hty⟩

theorem prod_exp_capped_profile (h : ℕ) (v t y : ℝ)
    (hty : derivativeCappedShiftProfile h v t = y) :
    (∏ i ∈ Finset.range h,
      Real.exp (min ((2 : ℝ) ^ (i + 1) * t) v)) = Real.exp y := by
  rw [← Real.exp_sum]
  simpa [derivativeCappedShiftProfile] using congrArg Real.exp hty

theorem prod_exp_capped_profile_eq (h : ℕ) (v t ξ : ℝ)
    (hprofile : derivativeCappedShiftProfile h v t = Real.log ξ) (hξ : 0 < ξ) :
    (∏ i ∈ Finset.range h,
      Real.exp (min ((2 : ℝ) ^ (i + 1) * t) v)) = ξ := by
  calc
    (∏ i ∈ Finset.range h,
        Real.exp (min ((2 : ℝ) ^ (i + 1) * t) v)) =
      Real.exp (derivativeCappedShiftProfile h v t) :=
        prod_exp_capped_profile h v t _ rfl
    _ = Real.exp (Real.log ξ) := congrArg Real.exp hprofile
    _ = ξ := Real.exp_log hξ

theorem exp_cappedCoordinate_mem (i : ℕ) {v t : ℝ}
    (hv : 0 < v) (ht : t ∈ Set.Icc 0 (v / 2)) :
    Real.exp (min ((2 : ℝ) ^ (i + 1) * t) v) ∈ Set.Icc 1 (Real.exp v) := by
  have hpow : 0 ≤ (2 : ℝ) ^ (i + 1) := pow_nonneg (by norm_num) _
  have harg : 0 ≤ min ((2 : ℝ) ^ (i + 1) * t) v :=
    le_min (mul_nonneg hpow ht.1) (le_of_lt hv)
  have hargV : min ((2 : ℝ) ^ (i + 1) * t) v ≤ v := min_le_right _ _
  constructor
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr harg
  · exact Real.exp_le_exp.mpr hargV

theorem exp_log_eq_of_one_lt {V : ℝ} (hV : 1 < V) :
    Real.exp (Real.log V) = V := Real.exp_log (by linarith)

theorem exp_mul_log_eq_rpow {V a : ℝ} (hV : 0 < V) :
    Real.exp (a * Real.log V) = V ^ a := by
  rw [Real.rpow_def_of_pos hV]
  congr 1
  ring

theorem exp_rpow_exp (s e : ℝ) : (Real.exp s) ^ e = Real.exp (e * s) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos s), Real.log_exp]
  congr 1
  ring

theorem exp_mul_rpow_exp (m s e : ℝ) :
    Real.exp m * (Real.exp s) ^ e = Real.exp (m + e * s) := by
  rw [exp_rpow_exp]
  rw [← Real.exp_add]

theorem derivativeCappedShiftProfile_uncapped (h : ℕ) (hh : 1 ≤ h)
    {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) (hcap : t ≤ v / (2 : ℝ) ^ h) :
    derivativeCappedShiftProfile h v t = ((2 : ℝ) ^ (h + 1) - 2) * t := by
  unfold derivativeCappedShiftProfile
  have hterm (i : ℕ) (hi : i ∈ Finset.range h) :
      min ((2 : ℝ) ^ (i + 1) * t) v = (2 : ℝ) ^ (i + 1) * t := by
    apply min_eq_left
    have hi' : i + 1 ≤ h := by simpa using hi
    have hpow : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ h :=
      pow_le_pow_right₀ (by norm_num) hi'
    calc
      (2 : ℝ) ^ (i + 1) * t ≤ (2 : ℝ) ^ h * t := mul_le_mul_of_nonneg_right hpow ht
      _ ≤ v := by
        have hcap' := (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ h)).mp hcap
        nlinarith [hcap']
  calc
    (∑ i ∈ Finset.range h, min ((2 : ℝ) ^ (i + 1) * t) v) =
        ∑ i ∈ Finset.range h, (2 : ℝ) ^ (i + 1) * t := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i hi
    _ = ((2 : ℝ) ^ (h + 1) - 2) * t := by
      rw [← Finset.sum_mul, sum_two_pow_succ_range]

theorem exp_uncappedCoordinate_eq_rpow (h i : ℕ) (hh : 1 ≤ h)
    {v t ξ : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t)
    (hcap : t ≤ v / (2 : ℝ) ^ h) (hprofile : derivativeCappedShiftProfile h v t = Real.log ξ)
    (hξ : 0 < ξ) :
    Real.exp ((2 : ℝ) ^ (i + 1) * t) =
      ξ ^ ((2 : ℝ) ^ (i + 1) / ((2 : ℝ) ^ (h + 1) - 2)) := by
  have hsum := derivativeCappedShiftProfile_uncapped h hh hv ht hcap
  have hden : 0 < (2 : ℝ) ^ (h + 1) - 2 := by
    have hp : (4 : ℝ) ≤ (2 : ℝ) ^ (h + 1) := by
      calc
        (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ (h + 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    linarith
  have harg : (2 : ℝ) ^ (i + 1) * t =
      ((2 : ℝ) ^ (i + 1) / ((2 : ℝ) ^ (h + 1) - 2)) * Real.log ξ := by
    rw [← hprofile, hsum]
    field_simp
  rw [harg, exp_mul_log_eq_rpow hξ]

theorem uncappedCoordinate_ge_min_rpow (h i : ℕ) (hh : 1 ≤ h) (hi : i < h)
    {v t ξ : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t)
    (hcap : t ≤ v / (2 : ℝ) ^ h) (hprofile : derivativeCappedShiftProfile h v t = Real.log ξ)
    (hξ : 0 < ξ) :
    min (ξ ^ ((2 : ℝ) ^ (i + 1) / ((2 : ℝ) ^ (h + 1) - 2)))
        (Real.exp v ^ ((2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ h)) ≤
      Real.exp (min ((2 : ℝ) ^ (i + 1) * t) v) := by
  have heq := exp_uncappedCoordinate_eq_rpow h i hh hv ht hcap hprofile hξ
  have hcoeff : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ h :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hterm : (2 : ℝ) ^ (i + 1) * t ≤ v := by
    calc
      (2 : ℝ) ^ (i + 1) * t ≤ (2 : ℝ) ^ h * t :=
        mul_le_mul_of_nonneg_right hcoeff ht
      _ ≤ v := by
        have hcap' := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) h)).mp hcap
        nlinarith [hcap']
  rw [← heq]
  rw [min_eq_left hterm]
  exact min_le_left (Real.exp ((2 : ℝ) ^ (i + 1) * t))
    (Real.exp v ^ ((2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ h))

theorem cappedCoordinate_exponent_lower (h i : ℕ) (hi : i < h)
    {v t : ℝ} (hv : 0 ≤ v) (hcap : v / (2 : ℝ) ^ h ≤ t) :
    (2 : ℝ) ^ (i + 1) * v / (2 : ℝ) ^ h ≤
      min ((2 : ℝ) ^ (i + 1) * t) v := by
  have hpow : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ h :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hden : 0 < (2 : ℝ) ^ h := pow_pos (by norm_num) _
  apply le_min
  · calc
      (2 : ℝ) ^ (i + 1) * v / (2 : ℝ) ^ h =
          (2 : ℝ) ^ (i + 1) * (v / (2 : ℝ) ^ h) := by ring
      _ ≤ (2 : ℝ) ^ (i + 1) * t :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
  · apply (div_le_iff₀ hden).2
    calc
      (2 : ℝ) ^ (i + 1) * v ≤ (2 : ℝ) ^ h * v :=
        mul_le_mul_of_nonneg_right hpow hv
      _ = v * (2 : ℝ) ^ h := by ring

theorem exp_cappedCoordinate_ge_rpow (h i : ℕ) (hi : i < h)
    {V t : ℝ} (hV : 1 < V) (ht : Real.log V / (2 : ℝ) ^ h ≤ t) :
    V ^ ((2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ h) ≤
      Real.exp (min ((2 : ℝ) ^ (i + 1) * t) (Real.log V)) := by
  have hv : 0 ≤ Real.log V := le_of_lt (Real.log_pos hV)
  have harg := cappedCoordinate_exponent_lower h i hi hv ht
  have hpow : Real.exp (((2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ h) * Real.log V) =
      V ^ ((2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ h) := exp_mul_log_eq_rpow (by linarith)
  rw [← hpow]
  apply Real.exp_le_exp.mpr
  calc
    ((2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ h) * Real.log V =
        (2 : ℝ) ^ (i + 1) * Real.log V / (2 : ℝ) ^ h := by ring
    _ ≤ min ((2 : ℝ) ^ (i + 1) * t) (Real.log V) := harg

theorem natFloor_half_le_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌊x⌋₊ by simpa using Nat.floor_mono hx)
  have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  nlinarith

theorem natFloor_rpow_neg_le_of_one_le {x a : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a) :
    (⌊x⌋₊ : ℝ) ^ (-a) ≤ (2 : ℝ) ^ a * x ^ (-a) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hscale := Real.rpow_le_rpow_of_nonpos
    (by positivity : 0 < x / 2) (natFloor_half_le_of_one_le hx)
    (neg_nonpos.mpr ha)
  have hdiv : x / 2 = x * (2 : ℝ)⁻¹ := by ring
  have hmul : (x * (2 : ℝ)⁻¹) ^ (-a) =
      x ^ (-a) * ((2 : ℝ)⁻¹) ^ (-a) := by
    rw [Real.mul_rpow (le_of_lt hxpos) (by positivity)]
  have hinv : ((2 : ℝ)⁻¹) ^ (-a) = (2 : ℝ) ^ a := by
    rw [Real.rpow_neg_eq_inv_rpow]
    norm_num
  calc
    (⌊x⌋₊ : ℝ) ^ (-a) ≤ (x / 2) ^ (-a) := hscale
    _ = x ^ (-a) * (2 : ℝ) ^ a := by rw [hdiv, hmul, hinv]
    _ = (2 : ℝ) ^ a * x ^ (-a) := by ring

theorem natFloor_rpow_neg_le_sqrt_two_of_one_le
    {x a : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a) (haHalf : a ≤ 1 / 2) :
    (⌊x⌋₊ : ℝ) ^ (-a) ≤ Real.sqrt 2 * x ^ (-a) := by
  have hcoeff : (2 : ℝ) ^ a ≤ Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) haHalf
  have hxpow : 0 ≤ x ^ (-a) := Real.rpow_nonneg (by linarith : 0 ≤ x) _
  calc
    (⌊x⌋₊ : ℝ) ^ (-a) ≤ (2 : ℝ) ^ a * x ^ (-a) :=
      natFloor_rpow_neg_le_of_one_le hx ha
    _ ≤ Real.sqrt 2 * x ^ (-a) := mul_le_mul_of_nonneg_right hcoeff hxpow

theorem rpow_neg_le_max_of_min_le {x u v a : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hx : 0 < x) (ha : 0 ≤ a)
    (hmin : min u v ≤ x) :
    x ^ (-a) ≤ max (u ^ (-a)) (v ^ (-a)) := by
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv] at hmin
    exact (Real.rpow_le_rpow_of_nonpos hu hmin (neg_nonpos.mpr ha)).trans
      (le_max_left _ _)
  · rw [min_eq_right hvu] at hmin
    exact (Real.rpow_le_rpow_of_nonpos hv hmin (neg_nonpos.mpr ha)).trans
      (le_max_right _ _)

theorem derivativeShiftAllocation (h : ℕ) (hh : 1 ≤ h) {V ξ : ℝ}
    (hV : 1 ≤ V) (hξ : 1 ≤ ξ) (hξV : ξ ≤ V ^ h) :
    ∃ x : ℕ → ℝ,
      (∀ i ∈ Finset.range h, x i ∈ Set.Icc 1 V) ∧
      (∏ i ∈ Finset.range h, x i) = ξ ∧
      (∀ i ∈ Finset.range h,
        min (ξ ^ ((2 : ℝ) ^ (i + 1) / ((2 : ℝ) ^ (h + 1) - 2)))
            (V ^ ((2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ h)) ≤ x i) := by
  by_cases hVone : V = 1
  · have hξone : ξ = 1 := by
      have : ξ ≤ 1 := by simpa [hVone] using hξV
      linarith
    refine ⟨fun _ => 1, ?_, ?_, ?_⟩
    · intro i hi
      simp [hVone]
    · simpa [hξone]
    · intro i hi
      simp [hξone, hVone]
  · have hVgt : 1 < V := lt_of_le_of_ne hV (Ne.symm hVone)
    have hv : 0 < Real.log V := Real.log_pos hVgt
    have hξpos : 0 < ξ := by linarith
    have hlogξlo : 0 ≤ Real.log ξ := Real.log_nonneg hξ
    have hlogξhi : Real.log ξ ≤ (h : ℝ) * Real.log V := by
      have hlog := Real.log_le_log hξpos hξV
      rw [Real.log_pow] at hlog
      exact hlog
    obtain ⟨t, ht, hprofile⟩ :=
      exists_derivativeCappedShiftProfile_eq h hh hv hlogξlo hlogξhi
    let x : ℕ → ℝ := fun i => Real.exp (min ((2 : ℝ) ^ (i + 1) * t) (Real.log V))
    refine ⟨x, ?_, ?_, ?_⟩
    · intro i hi
      have hx := exp_cappedCoordinate_mem i hv ht
      simpa [x, exp_log_eq_of_one_lt hVgt] using hx
    · simpa [x] using prod_exp_capped_profile_eq h (Real.log V) t ξ hprofile hξpos
    · intro i hi
      have hi' : i < h := Finset.mem_range.mp hi
      by_cases hunc : t ≤ Real.log V / (2 : ℝ) ^ h
      · have hu := uncappedCoordinate_ge_min_rpow h i hh hi' hv.le ht.1 hunc hprofile hξpos
        simpa [x, exp_log_eq_of_one_lt hVgt] using hu
      · have hc : Real.log V / (2 : ℝ) ^ h ≤ t := le_of_not_ge hunc
        have hc' := exp_cappedCoordinate_ge_rpow h i hi' hVgt hc
        exact (min_le_right _ _).trans (by simpa [x] using hc')

theorem balanceLogLeftThreshold (α β n z : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hz : z ≤ -n / (α + β)) : n + β * z ≤ -α * z := by
  have hsum : 0 < α + β := by linarith
  have hmul := mul_le_mul_of_nonneg_left hz (le_of_lt hsum)
  have hquot : (α + β) * (-n / (α + β)) = -n := by
    field_simp [ne_of_gt hsum]
  nlinarith [hmul, hquot]

theorem balanceLogRightThreshold (β m n z : ℝ) (hβ : 0 < β)
    (hz : z ≤ (m - n) / (2 * β)) : n + β * z ≤ m - β * z := by
  have hmul := mul_le_mul_of_nonneg_left hz
    (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hβ))
  have hquot : (2 * β) * ((m - n) / (2 * β)) = m - n := by
    field_simp [ne_of_gt hβ]
  nlinarith [hmul, hquot]

theorem balanceAtULogPoint (α β n : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    n + β * (-n / (α + β)) = -α * (-n / (α + β)) ∧
    -α * (-n / (α + β)) = α * n / (α + β) := by
  have hsum : 0 < α + β := by linarith
  constructor <;> field_simp [ne_of_gt hsum] <;> ring

theorem balanceAtWLogPoint (β m n : ℝ) (hβ : 0 < β) :
    m - β * ((m - n) / (2 * β)) = (m + n) / 2 ∧
    n + β * ((m - n) / (2 * β)) = (m + n) / 2 := by
  constructor <;> field_simp [ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hβ)] <;> ring

theorem balanceLogUResidual (α β m n : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwu : (m - n) / (2 * β) ≤ -n / (α + β)) :
    m - β * (-n / (α + β)) ≤ n + β * (-n / (α + β)) := by
  have htwo : 0 < 2 * β := by positivity
  have hmul := mul_le_mul_of_nonneg_left hwu (le_of_lt htwo)
  have hquot : (2 * β) * ((m - n) / (2 * β)) = m - n := by
    field_simp [ne_of_gt hβ]
  nlinarith [hmul, hquot]

theorem balanceLogWResidual (α β m n : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (huw : -n / (α + β) ≤ (m - n) / (2 * β)) :
    -α * ((m - n) / (2 * β)) ≤ (m + n) / 2 := by
  have hsum : 0 < α + β := by linarith
  have htwo : 0 < 2 * β := by positivity
  have hmul := mul_le_mul_of_nonneg_left huw
    (le_of_lt (mul_pos hsum htwo))
  have hleft : ((α + β) * (2 * β)) * (-n / (α + β)) = -2 * β * n := by
    field_simp [ne_of_gt hsum]
  have hright : ((α + β) * (2 * β)) * ((m - n) / (2 * β)) =
      (α + β) * (m - n) := by
    field_simp [ne_of_gt htwo]
  have hcross : -2 * β * n ≤ (α + β) * (m - n) := by
    rw [hleft, hright] at hmul
    exact hmul
  have hnum : -α * (m - n) ≤ β * (m + n) := by nlinarith [hcross]
  have hquot : (-α * (m - n)) / (2 * β) ≤ (m + n) / 2 := by
    apply (div_le_iff₀ htwo).2
    nlinarith [hnum]
  have hleft' : -α * ((m - n) / (2 * β)) =
      (-α * (m - n)) / (2 * β) := by ring
  rw [hleft']
  exact hquot

theorem max3_le_max4_of_components (a b c d e f g : ℝ)
    (ha : a ≤ d) (hb : b ≤ e) (hc : c ≤ max f g) :
    max a (max b c) ≤ max d (max e (max f g)) := by
  apply max_le_iff.mpr
  constructor
  · exact le_trans ha (le_max_left _ _)
  · apply max_le_iff.mpr
    constructor
    · exact le_trans hb (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans hc (le_trans (le_max_right _ _) (le_max_right _ _))

theorem max3_le_of_components (a b c R : ℝ)
    (ha : a ≤ R) (hb : b ≤ R) (hc : c ≤ R) : max a (max b c) ≤ R := by
  exact max_le_iff.mpr ⟨ha, max_le_iff.mpr ⟨hb, hc⟩⟩

theorem balanceThreeLogPowers (α β m n z : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    let u := -n / (α + β)
    let w := (m - n) / (2 * β)
    let s := min z (max u w)
    s ≤ z ∧
      max (-α * s) (max (m - β * s) (n + β * s)) ≤
        max (-α * z) (max (m - β * z) (max ((m + n) / 2) (α * n / (α + β)))) := by
  let u := -n / (α + β)
  let w := (m - n) / (2 * β)
  let s := min z (max u w)
  have hsum : 0 < α + β := by linarith
  have hbound :
      max (-α * s) (max (m - β * s) (n + β * s)) ≤
        max (-α * z) (max (m - β * z) (max ((m + n) / 2) (α * n / (α + β)))) := by
    change max (-α * s) (max (m - β * s) (n + β * s)) ≤
      max (-α * z) (max (m - β * z) (max ((m + n) / 2) (α * n / (α + β))))
    by_cases hz : z ≤ max u w
    · have hs : s = z := min_eq_left hz
      rw [hs]
      have hthird : n + β * z ≤ max (-α * z) (m - β * z) := by
        rcases le_max_iff.mp hz with hzu | hzw
        · have hzu' : z ≤ -n / (α + β) := by simpa [u] using hzu
          exact (balanceLogLeftThreshold α β n z hα hβ hzu').trans (le_max_left _ _)
        · have hzw' : z ≤ (m - n) / (2 * β) := by simpa [w] using hzw
          exact (balanceLogRightThreshold β m n z hβ hzw').trans (le_max_right _ _)
      apply max3_le_of_components
      · exact le_max_left _ _
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact hthird.trans (max_le_iff.mpr
          ⟨le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _)⟩)
    · have hmaxz : max u w < z := lt_of_not_ge hz
      have hs : s = max u w := min_eq_right hmaxz.le
      rw [hs]
      rcases le_total w u with hwu | huw
      · rw [max_eq_left hwu]
        have huEq := balanceAtULogPoint α β n hα hβ
        have huResidual := balanceLogUResidual α β m n hα hβ (by simpa [u, w] using hwu)
        have hG : α * n / (α + β) ≤
            max (-α * z) (max (m - β * z) (max ((m + n) / 2) (α * n / (α + β)))) := by
          exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
        apply max3_le_of_components
        · exact le_trans (le_of_eq (by simpa [u] using huEq.2)) hG
        · exact le_trans (by simpa [u] using huResidual)
            (le_trans (le_of_eq (by simpa [u] using huEq.1))
              (le_trans (le_of_eq huEq.2) hG))
        · exact le_trans (le_of_eq (by simpa [u] using huEq.1))
            (le_trans (le_of_eq huEq.2) hG)
      · rw [max_eq_right huw]
        have hwEq := balanceAtWLogPoint β m n hβ
        have hwResidual := balanceLogWResidual α β m n hα hβ (by simpa [u, w] using huw)
        have hF : (m + n) / 2 ≤
            max (-α * z) (max (m - β * z) (max ((m + n) / 2) (α * n / (α + β)))) := by
          exact le_trans (le_max_left _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))
        apply max3_le_of_components
        · exact le_trans (by simpa [w] using hwResidual) hF
        · exact le_trans (le_of_eq (by simpa [w] using hwEq.1)) hF
        · exact le_trans (le_of_eq (by simpa [w] using hwEq.2)) hF
  change s ≤ z ∧
    max (-α * s) (max (m - β * s) (n + β * s)) ≤
      max (-α * z) (max (m - β * z) (max ((m + n) / 2) (α * n / (α + β))) )
  exact ⟨min_le_left _ _, hbound⟩

theorem exp_max_pair (a b : ℝ) : Real.exp (max a b) = max (Real.exp a) (Real.exp b) := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, max_eq_right (Real.exp_le_exp.mpr hab)]
  · have hba : b ≤ a := le_of_not_ge hab
    rw [max_eq_left hba, max_eq_left (Real.exp_le_exp.mpr hba)]

theorem derivativeBalanceThreePowers (M N Z α β : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hZ : 0 < Z) (hα : 0 < α) (hβ : 0 < β) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ Z ∧
      max (ξ ^ (-α)) (max (M * ξ ^ (-β)) (N * ξ ^ β)) ≤
        max (Z ^ (-α)) (max (M * Z ^ (-β))
          (max (Real.sqrt (M * N)) (N ^ (α / (α + β))))) := by
  let m := Real.log M
  let n := Real.log N
  let z := Real.log Z
  let u := -n / (α + β)
  let w := (m - n) / (2 * β)
  let s := min z (max u w)
  let ξ := Real.exp s
  have hm : Real.exp m = M := Real.exp_log hM
  have hn : Real.exp n = N := Real.exp_log hN
  have hz : Real.exp z = Z := Real.exp_log hZ
  have hlog := balanceThreeLogPowers α β m n z hα hβ
  have hsbound : s ≤ z := by simpa [m, n, z, u, w, s] using hlog.1
  have hmaxbound :
      max (-α * s) (max (m - β * s) (n + β * s)) ≤
        max (-α * z) (max (m - β * z) (max ((m + n) / 2) (α * n / (α + β)))) := by
    simpa [m, n, z, u, w, s] using hlog.2
  have hξpos : 0 < ξ := Real.exp_pos s
  have hξZ : ξ ≤ Z := by
    dsimp [ξ]
    rw [← hz]
    exact Real.exp_le_exp.mpr hsbound
  have hterm1 : ξ ^ (-α) = Real.exp (-α * s) := by
    dsimp [ξ]
    rw [exp_rpow_exp]
  have hterm2 : M * ξ ^ (-β) = Real.exp (m - β * s) := by
    dsimp [ξ]
    rw [← hm, exp_mul_rpow_exp]
    congr 1
    ring
  have hterm3 : N * ξ ^ β = Real.exp (n + β * s) := by
    dsimp [ξ]
    rw [← hn, exp_mul_rpow_exp]
  have hright1 : Z ^ (-α) = Real.exp (-α * z) := by
    rw [← hz, exp_rpow_exp]
  have hright2 : M * Z ^ (-β) = Real.exp (m - β * z) := by
    rw [← hm, ← hz, exp_mul_rpow_exp]
    congr 1
    ring
  have hMN : M * N = Real.exp (m + n) := by
    rw [← hm, ← hn, ← Real.exp_add]
  have hright3 : Real.sqrt (M * N) = Real.exp ((m + n) / 2) := by
    rw [hMN, Real.sqrt_eq_rpow, exp_rpow_exp]
    congr 1
    ring
  have hright4 : N ^ (α / (α + β)) = Real.exp (α * n / (α + β)) := by
    rw [← hn, exp_rpow_exp]
    congr 1
    ring
  have hleft : max (ξ ^ (-α)) (max (M * ξ ^ (-β)) (N * ξ ^ β)) =
      Real.exp (max (-α * s) (max (m - β * s) (n + β * s))) := by
    rw [hterm1, hterm2, hterm3, ← exp_max_pair, ← exp_max_pair]
  have hright : max (Z ^ (-α)) (max (M * Z ^ (-β))
      (max (Real.sqrt (M * N)) (N ^ (α / (α + β))))) =
      Real.exp (max (-α * z) (max (m - β * z)
        (max ((m + n) / 2) (α * n / (α + β))))) := by
    rw [hright1, hright2, hright3, hright4, ← exp_max_pair, ← exp_max_pair, ← exp_max_pair]
  refine ⟨ξ, hξpos, hξZ, ?_⟩
  rw [hleft, hright]
  exact Real.exp_le_exp.mpr hmaxbound
  
  
/-- Two successive applications of the fundamental theorem of calculus,
written as nested integrals over the translated intervals. -/
theorem HalfOpenCkData.twoStep_intervalIntegral_difference
    {x Y a b t : ℝ} {order : ℕ} (data : HalfOpenCkData x Y order)
    (horder : 2 ≤ order) (ha : 0 < a) (hb : 0 ≤ b)
    (htx : x < t) (htab : t + a + b ≤ x + Y) :
    ∫ s in t..t + b, ∫ u in s..s + a,
        data.derivative 2 u =
      realForwardDifferenceR b (realForwardDifferenceR a (data.derivative 0)) t := by
  have haY : a < Y := by linarith
  let hdata := data.realForwardDifferenceR_data (by omega) ha haY
  have htb : t + b ≤ x + (Y - a) := by linarith
  have houter := hdata.intervalIntegral_derivative_eq_sub
    (k := 0) (by omega) hb htx htb
  have houter' :
      ∫ s in t..t + b, realForwardDifferenceR a (data.derivative 1) s =
        realForwardDifferenceR b (realForwardDifferenceR a (data.derivative 0)) t := by
    simpa [hdata, HalfOpenCkData.realForwardDifferenceR_data,
      realForwardDifferenceR] using houter
  have hinner : Set.EqOn
      (fun s : ℝ => realForwardDifferenceR a (data.derivative 1) s)
      (fun s => ∫ u in s..s + a, data.derivative 2 u)
      (Set.uIcc t (t + b)) := by
    intro s hs
    have hs' : t ≤ s ∧ s ≤ t + b := by
      simpa [Set.uIcc_of_le (le_add_of_nonneg_right hb)] using hs
    have hsx : x < s := lt_of_lt_of_le htx hs'.1
    have hsend : s + a ≤ x + Y := by linarith [hs'.2]
    have hpoint := data.intervalIntegral_derivative_eq_sub
      (k := 1) (by omega) (le_of_lt ha) hsx hsend
    simpa [realForwardDifferenceR] using hpoint.symm
  calc
    ∫ s in t..t + b, ∫ u in s..s + a, data.derivative 2 u =
        ∫ s in t..t + b, realForwardDifferenceR a (data.derivative 1) s :=
      intervalIntegral.integral_congr hinner.symm
    _ = realForwardDifferenceR b (realForwardDifferenceR a (data.derivative 0)) t :=
      houter'

/-- Translate a nested two-shift integral to the zero-based rectangle used
in the derivative-test blueprint. -/
theorem intervalIntegral_twoStep_translate (f : ℝ → ℝ) (t a b : ℝ) :
    ∫ s in t..t + b, ∫ u in s..s + a, f u =
      ∫ v in 0..b, ∫ u in 0..a, f (t + u + v) := by
  let G : ℝ → ℝ := fun s => ∫ u in s..s + a, f u
  have houter :
      ∫ s in t..t + b, G s = ∫ v in 0..b, G (v + t) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := 0) (b := b) (f := G) t
    simpa only [zero_add, add_comm b t] using h.symm
  have hinner (v : ℝ) :
      G (v + t) = ∫ u in 0..a, f (t + u + v) := by
    change (∫ u in v + t..v + t + a, f u) = _
    have htrans := (intervalIntegral.integral_comp_add_right
      (a := 0) (b := a) (f := f) (v + t)).symm
    simpa [add_assoc, add_comm, add_left_comm] using htrans
  calc
    ∫ s in t..t + b, ∫ u in s..s + a, f u =
        ∫ v in 0..b, G (v + t) := by simpa [G] using houter
    _ = ∫ v in 0..b, ∫ u in 0..a, f (t + u + v) :=
      intervalIntegral.integral_congr (by
        intro v hv
        exact hinner v)

/-- The exact zero-based two-dimensional box formula for two successive
real forward differences. -/
theorem HalfOpenCkData.twoStep_boxIntegral_difference
    {x Y a b t : ℝ} {order : ℕ} (data : HalfOpenCkData x Y order)
    (horder : 2 ≤ order) (ha : 0 < a) (hb : 0 ≤ b)
    (htx : x < t) (htab : t + a + b ≤ x + Y) :
    ∫ v in 0..b, ∫ u in 0..a, data.derivative 2 (t + u + v) =
      realForwardDifferenceR b (realForwardDifferenceR a (data.derivative 0)) t := by
  calc
    ∫ v in 0..b, ∫ u in 0..a, data.derivative 2 (t + u + v) =
        ∫ s in t..t + b, ∫ u in s..s + a, data.derivative 2 u :=
      (intervalIntegral_twoStep_translate (data.derivative 2) t a b).symm
    _ = realForwardDifferenceR b (realForwardDifferenceR a (data.derivative 0)) t :=
      data.twoStep_intervalIntegral_difference horder ha hb htx htab

/-- The three-shift box identity, obtained by applying the two-shift result
to the once-differenced data and expanding its second derivative by FTC. -/
theorem HalfOpenCkData.threeStep_boxIntegral_difference
    {x Y a b c t : ℝ} {order : ℕ} (data : HalfOpenCkData x Y order)
    (horder : 3 ≤ order) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (htx : x < t) (htabc : t + a + b + c ≤ x + Y) :
    ∫ v in 0..c, ∫ u in 0..b, ∫ w in 0..a,
        data.derivative 3 (t + w + u + v) =
      realForwardDifferenceR c
        (realForwardDifferenceR b
          (realForwardDifferenceR a (data.derivative 0))) t := by
  have haY : a < Y := by linarith
  let hdata := data.realForwardDifferenceR_data (by omega) ha haY
  have htwo := hdata.twoStep_boxIntegral_difference
    (by omega) hb hc htx (by linarith)
  have hinner (u v : ℝ) (hu : 0 ≤ u) (hu' : u ≤ b)
      (hv : 0 ≤ v) (hv' : v ≤ c) :
      hdata.derivative 2 (t + u + v) =
        ∫ w in 0..a, data.derivative 3 (t + w + u + v) := by
    have hsx : x < t + u + v := by linarith
    have hsend : t + u + v + a ≤ x + Y := by linarith
    have hftc := data.intervalIntegral_derivative_eq_sub
      (k := 2) (by omega) (le_of_lt ha) hsx hsend
    have htrans := (intervalIntegral.integral_comp_add_right
      (a := 0) (b := a) (f := data.derivative 3) (t + u + v)).symm
    have htrans' :
        ∫ w in t + u + v..(t + u + v) + a, data.derivative 3 w =
          ∫ w in 0..a, data.derivative 3 (w + (t + u + v)) := by
      simpa only [zero_add, add_comm a (t + u + v)] using htrans
    rw [htrans'] at hftc
    change data.derivative 2 (t + u + v + a) -
      data.derivative 2 (t + u + v) = _
    simpa [add_assoc, add_comm, add_left_comm] using hftc.symm
  have hbox :
      ∫ v in 0..c, ∫ u in 0..b, hdata.derivative 2 (t + u + v) =
        ∫ v in 0..c, ∫ u in 0..b, ∫ w in 0..a,
          data.derivative 3 (t + w + u + v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : 0 ≤ u ∧ u ≤ b := by
      simpa [Set.uIcc_of_le (le_of_lt hb)] using hu
    have hv' : 0 ≤ v ∧ v ≤ c := by
      simpa [Set.uIcc_of_le hc] using hv
    change hdata.derivative 2 (t + u + v) = _
    exact hinner u v hu'.1 hu'.2 hv'.1 hv'.2
  calc
    ∫ v in 0..c, ∫ u in 0..b, ∫ w in 0..a,
        data.derivative 3 (t + w + u + v) =
      ∫ v in 0..c, ∫ u in 0..b, hdata.derivative 2 (t + u + v) :=
        hbox.symm
    _ = realForwardDifferenceR c
        (realForwardDifferenceR b (realForwardDifferenceR a (data.derivative 0))) t := by
      simpa [hdata, HalfOpenCkData.realForwardDifferenceR_data,
        realForwardDifferenceR] using htwo

/-- Differentiating a real-step difference of the first derivative is valid
on the exact interior of its shrinking interval. -/
theorem HalfOpenC2Data.realForwardDifferenceR_firstDerivative_hasDerivAt
    {x Y a t : ℝ} (data : HalfOpenC2Data x Y)
    (ha : 0 ≤ a) (htx : x < t) (htY : t + a < x + Y) :
    HasDerivAt (realForwardDifferenceR a data.firstDerivative)
      (data.secondDerivative (t + a) - data.secondDerivative t) t := by
  have hta : x < t + a := lt_of_lt_of_le htx (le_add_of_nonneg_right ha)
  have htmem : t ∈ Set.Ioo x (x + Y) := ⟨htx, lt_of_le_of_lt (le_add_of_nonneg_right ha) htY⟩
  have htamem : t + a ∈ Set.Ioo x (x + Y) := ⟨hta, htY⟩
  have hshift : HasDerivAt (fun s : ℝ => data.firstDerivative (s + a))
      (data.secondDerivative (t + a)) t := by
    have hid : HasDerivAt (fun s : ℝ => s + a) 1 t :=
      (hasDerivAt_id t).add_const a
    have hcomp := (data.first_hasDerivAt (t + a) htamem).comp t hid
    simpa [Function.comp_def] using hcomp
  have hbase := data.first_hasDerivAt t htmem
  change HasDerivAt (fun s : ℝ => data.firstDerivative (s + a) -
    data.firstDerivative s) _ _
  exact hshift.sub hbase

/-- The iterated forward difference in the tuple order of `ld:data`. -/
def iteratedRealForwardDifference (f : ℝ → ℝ) : List ℕ → ℝ → ℝ
  | [] => f
  | a :: rest => iteratedRealForwardDifference (realForwardDifference a f) rest

theorem iteratedRealForwardDifference_cast (f : ℝ → ℝ) (shifts : List ℕ) :
    iteratedRealForwardDifference f shifts =
      iteratedRealForwardDifferenceR f (shifts.map fun a => (a : ℝ)) := by
  induction shifts generalizing f with
  | nil => rfl
  | cons a rest ih =>
      simp only [iteratedRealForwardDifference, iteratedRealForwardDifferenceR,
        List.map_cons]
      rw [ih]
      rfl

/-- The unit complex phase `exp(2π i f(n))` used in the derivative-test sums. -/
noncomputable def realExponentialPhase (f : ℝ → ℝ) (n : ℤ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * f (n : ℝ)) : ℂ) * Complex.I)

/-- Fourier characters at monomial sample points are the derivative-test
phases used throughout the paper. -/
theorem fourier_monomial_phase (c : ℝ) (h n : ℤ) :
    let x : ℝ := (n : ℝ) ^ c
    fourier h (x : AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) =
      realExponentialPhase (fun t => (h : ℝ) * t ^ c) n := by
  dsimp only
  rw [fourier_coe_apply]
  unfold realExponentialPhase
  rw [show (1 / 2 : ℝ) - (-1 / 2 : ℝ) = 1 by ring]
  simp only [Complex.ofReal_one, div_one]
  congr 1
  push_cast
  ring

theorem norm_realExponentialPhase (f : ℝ → ℝ) (n : ℤ) :
    ‖realExponentialPhase f n‖ = 1 := by
  unfold realExponentialPhase
  convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi * f (n : ℝ)) using 1

theorem realIntegerInterval_phase_sum_norm_le_length_add_one
    (f : ℝ → ℝ) (x Y : ℝ) (hY : 0 ≤ Y) :
    ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ ≤ Y + 1 := by
  have hnorm : ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ ≤
      (realIntegerInterval x Y).card := by
    calc
      ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ ≤
          ∑ n ∈ realIntegerInterval x Y, ‖realExponentialPhase f n‖ := norm_sum_le _ _
      _ = (realIntegerInterval x Y).card := by simp [norm_realExponentialPhase]
  have hcard := realIntegerInterval_card_le_of_nonneg x Y hY
  exact hnorm.trans hcard

theorem realIntegerInterval_phase_sum_short_scale_bound
    (f : ℝ → ℝ) (x K L ν : ℝ)
    (hK : 1 ≤ K) (hν : 0 ≤ ν) (hν' : ν ≤ 1)
    (hL : 0 ≤ L) (hLsmall : L < K ^ (1 - ν)) :
    ‖∑ n ∈ realIntegerInterval x L, realExponentialPhase f n‖ ≤
      2 * K ^ (1 - ν) := by
  have hscale : 1 ≤ K ^ (1 - ν) :=
    Real.one_le_rpow hK (by linarith)
  calc
    ‖∑ n ∈ realIntegerInterval x L, realExponentialPhase f n‖ ≤ L + 1 :=
      realIntegerInterval_phase_sum_norm_le_length_add_one f x L hL
    _ ≤ K ^ (1 - ν) + 1 := add_le_add (le_of_lt hLsmall) le_rfl
    _ ≤ 2 * K ^ (1 - ν) := by nlinarith

/-- Distance from a real number to the embedded integers, as used in the
blueprint's boundary kernel. -/
noncomputable def realDistanceToIntegers (t : ℝ) : ℝ :=
  Metric.infDist t (Set.range fun z : ℤ => (z : ℝ))

/-- Distance to the integers is unchanged by an integer translation. -/
theorem realDistanceToIntegers_add_int (t : ℝ) (z : ℤ) :
    realDistanceToIntegers (t + (z : ℝ)) = realDistanceToIntegers t := by
  let Φ : ℝ → ℝ := fun x => x + (z : ℝ)
  have hΦ : Isometry Φ := Isometry.of_dist_eq fun x y => by
    dsimp [Φ]
    rw [Real.dist_eq, Real.dist_eq]
    congr 1
    ring
  have himage : Φ '' Set.range (fun k : ℤ => (k : ℝ)) =
      Set.range (fun k : ℤ => (k : ℝ)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨k, rfl⟩, rfl⟩
      exact ⟨k + z, by push_cast; ring⟩
    · rintro ⟨k, rfl⟩
      refine ⟨((k - z : ℤ) : ℝ), ⟨k - z, rfl⟩, ?_⟩
      push_cast
      ring
  change Metric.infDist (t + (z : ℝ))
    (Set.range fun k : ℤ => (k : ℝ)) = _
  rw [← himage]
  exact Metric.infDist_image hΦ

theorem realDistanceToIntegers_eq_abs_of_abs_le_half {t : ℝ}
    (ht : |t| ≤ 1 / 2) : realDistanceToIntegers t = |t| := by
  apply le_antisymm
  · exact (Metric.infDist_le_dist_of_mem (Set.mem_range_self (0 : ℤ))).trans_eq
      (by simp [realDistanceToIntegers, Real.dist_eq])
  · change |t| ≤ Metric.infDist t
      (Set.range fun z : ℤ => (z : ℝ))
    have hs : (Set.range fun z : ℤ => (z : ℝ)).Nonempty :=
      ⟨0, ⟨0, by simp⟩⟩
    apply (Metric.le_infDist hs).2
    intro y hy
    rcases hy with ⟨z, rfl⟩
    simp only [Real.dist_eq]
    have htl : -(1 / 2 : ℝ) ≤ t := (abs_le.mp ht).1
    have htr : t ≤ (1 / 2 : ℝ) := (abs_le.mp ht).2
    rcases lt_trichotomy z 0 with hzneg | hzero | hzpos
    · have hzne : (z : ℝ) ≤ -1 := by exact_mod_cast (Int.le_sub_one_of_lt hzneg)
      have hgap : 1 / 2 ≤ t - z := by exact_mod_cast (by linarith)
      rw [abs_of_nonneg (by linarith : 0 ≤ t - z)]
      exact le_trans ht hgap
    · subst z
      simp
    · have hzge : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (Int.add_one_le_of_lt hzpos)
      have hgap : 1 / 2 ≤ (z : ℝ) - t := by linarith
      rw [abs_of_nonpos (by linarith : t - (z : ℝ) ≤ 0)]
      convert le_trans ht hgap using 1 <;> ring

/-- The periodic boundary kernel from `ar:floor-data`. The proof argument
records the blueprint's domain `M ≥ 2`. -/
noncomputable def floorBoundaryKernel (M : ℕ) (_hM : 2 ≤ M) (t : ℝ) : ℝ :=
  by
    classical
    exact if ∃ z : ℤ, t = (z : ℝ) then 1 else
      min 1 (((M : ℝ) * realDistanceToIntegers t)⁻¹)

/-- The boundary kernel is periodic with period one, as specified in the
paper's definition through distance to the integers. -/
theorem floorBoundaryKernel_add_int (M : ℕ) (hM : 2 ≤ M) (t : ℝ) (k : ℤ) :
    floorBoundaryKernel M hM (t + (k : ℝ)) = floorBoundaryKernel M hM t := by
  classical
  by_cases ht : ∃ z : ℤ, t = (z : ℝ)
  · have htk : ∃ z : ℤ, t + (k : ℝ) = (z : ℝ) := by
      rcases ht with ⟨z, rfl⟩
      exact ⟨z + k, by push_cast; ring⟩
    simp [floorBoundaryKernel, ht, htk]
  · have htk : ¬ ∃ z : ℤ, t + (k : ℝ) = (z : ℝ) := by
      intro h
      rcases h with ⟨z, hz⟩
      apply ht
      refine ⟨z - k, ?_⟩
      push_cast at hz ⊢
      linarith
    simp only [floorBoundaryKernel, ht, htk, if_false]
    rw [realDistanceToIntegers_add_int]

theorem floorBoundaryKernel_nonneg (M : ℕ) (hM : 2 ≤ M) (t : ℝ) :
    0 ≤ floorBoundaryKernel M hM t := by
  classical
  by_cases ht : ∃ z : ℤ, t = (z : ℝ)
  · simp [floorBoundaryKernel, ht]
  · simp only [floorBoundaryKernel, ht, if_false]
    apply le_min
    · norm_num
    · apply inv_nonneg.mpr
      exact mul_nonneg (by positivity) (Metric.infDist_nonneg)

theorem floorBoundaryKernel_le_one (M : ℕ) (hM : 2 ≤ M) (t : ℝ) :
    floorBoundaryKernel M hM t ≤ 1 := by
  classical
  by_cases ht : ∃ z : ℤ, t = (z : ℝ)
  · simp [floorBoundaryKernel, ht]
  · simp [floorBoundaryKernel, ht]

/-- A finite sum of boundary-kernel values is bounded by the number of
sampled integers. -/
theorem sum_floorBoundaryKernel_monomial_le_card (M : ℕ) (hM : 2 ≤ M)
    (c : ℝ) (s : Finset ℤ) :
    (∑ n ∈ s, floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤ (s.card : ℝ) := by
  calc
    (∑ n ∈ s, floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤
        ∑ _n ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact floorBoundaryKernel_le_one M hM ((n : ℝ) ^ c)
    _ = (s.card : ℝ) := by simp

/-- The terminal dyadic interval of length less than two contributes at most
two to the boundary-kernel sum. -/
theorem sum_floorBoundaryKernel_monomial_terminal_lt_two
    (M : ℕ) (hM : 2 ≤ M) (c Y : ℝ)
    (hY : 0 ≤ Y) (hYlt : Y < 2) :
    (∑ n ∈ realIntegerInterval 0 Y,
      floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤ 2 := by
  calc
    (∑ n ∈ realIntegerInterval 0 Y,
        floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤
        ((realIntegerInterval 0 Y).card : ℝ) :=
          sum_floorBoundaryKernel_monomial_le_card M hM c _
    _ ≤ Y := realIntegerInterval_zero_card_le Y hY
    _ ≤ 2 := hYlt.le

/-- The integer interval `(0,N]` is exactly the image of the natural interval
`[1,N]` under the natural-to-integer cast. -/
theorem realIntegerInterval_zero_eq_nat_Icc (N : ℕ) :
    realIntegerInterval 0 (N : ℝ) =
      (Finset.Icc 1 N).map Nat.castEmbedding := by
  ext z
  rw [mem_realIntegerInterval_iff]
  simp only [Finset.mem_map, Finset.mem_Icc, Nat.castEmbedding_apply]
  constructor
  · rintro ⟨hzpos, hzN⟩
    have hz1 : (1 : ℤ) ≤ z := by exact_mod_cast hzpos
    have hzN' : z ≤ (N : ℤ) := by
      have htmp : z ≤ (0 : ℤ) + (N : ℤ) := by exact_mod_cast hzN
      simpa using htmp
    have hz0 : 0 ≤ z := le_trans (by norm_num : (0 : ℤ) ≤ 1) hz1
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    refine ⟨z.toNat, ⟨?_, ?_⟩, hzcast⟩
    · have hz1' : (1 : ℤ) ≤ (z.toNat : ℤ) := by simpa [hzcast] using hz1
      exact_mod_cast hz1'
    · have hzN'' : (z.toNat : ℤ) ≤ (N : ℤ) := by simpa [hzcast] using hzN'
      exact_mod_cast hzN''
  · rintro ⟨n, hn, hcast⟩
    rcases hn with ⟨hn1, hnN⟩
    rw [← hcast]
    constructor
    · have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast (by omega : 0 < n)
      exact_mod_cast hnpos
    · simpa using (show n ≤ N from hnN)

/-- Sum over the paper's positive-natural range as the corresponding
positive-integer interval sum. -/
theorem sum_realIntegerInterval_zero_eq_nat_Icc
    {α : Type*} [AddCommMonoid α] (N : ℕ) (f : ℤ → α) :
    (∑ z ∈ realIntegerInterval 0 (N : ℝ), f z) =
      ∑ n ∈ Finset.Icc 1 N, f (n : ℤ) := by
  rw [realIntegerInterval_zero_eq_nat_Icc]
  rw [Finset.sum_map]
  rfl

/-- For nonnegative boundary-kernel values, the norm of their complex-coerced
finite sum is exactly the original real sum. -/
theorem norm_sum_floorBoundaryKernel_monomial_eq_sum
    (M : ℕ) (hM : 2 ≤ M) (c : ℝ) (s : Finset ℤ) :
    ‖∑ n ∈ s, (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ =
      ∑ n ∈ s, floorBoundaryKernel M hM ((n : ℝ) ^ c) := by
  have hnonneg : 0 ≤ ∑ n ∈ s, floorBoundaryKernel M hM ((n : ℝ) ^ c) :=
    Finset.sum_nonneg fun n hn => floorBoundaryKernel_nonneg M hM ((n : ℝ) ^ c)
  calc
    ‖∑ n ∈ s, (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ =
        ‖((∑ n ∈ s, floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℝ) : ℂ)‖ := by
          rw [← Complex.ofReal_sum]
    _ = ∑ n ∈ s, floorBoundaryKernel M hM ((n : ℝ) ^ c) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

theorem floorBoundaryKernel_eq_min_of_abs_le_half (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : |t| ≤ 1 / 2) :
    floorBoundaryKernel M hM t =
      if t = 0 then 1 else min 1 (((M : ℝ) * |t|)⁻¹) := by
  classical
  by_cases ht0 : t = 0
  · subst t
    have hz : ∃ z : ℤ, (0 : ℝ) = (z : ℝ) := ⟨0, by simp⟩
    rw [floorBoundaryKernel, if_pos hz]
    simp
  · have hnotInt : ¬ ∃ z : ℤ, t = (z : ℝ) := by
      rintro ⟨z, hzt⟩
      have habs : |(z : ℝ)| ≤ 1 / 2 := by simpa [hzt] using ht
      rcases lt_trichotomy z 0 with hzneg | hzero | hzpos
      · have hzle : (z : ℝ) ≤ -1 := by exact_mod_cast (Int.le_sub_one_of_lt hzneg)
        have : 1 ≤ |(z : ℝ)| := by rw [abs_of_nonpos (by linarith)]; linarith
        linarith
      · exact ht0 (by simpa [hzero] using hzt)
      · have hzge : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (Int.add_one_le_of_lt hzpos)
        have : 1 ≤ |(z : ℝ)| := by rw [abs_of_nonneg (by linarith)]; linarith
        linarith
    rw [floorBoundaryKernel, if_neg hnotInt,
      realDistanceToIntegers_eq_abs_of_abs_le_half ht]
    simp [ht0]

theorem intervalIntegral_inv_eq_log_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, x⁻¹) = Real.log b - Real.log a := by
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc a b) :=
    continuousOn_inv₀.mono (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hx0
      have hx' : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
      have hxa : a ≤ x := hx'.1
      exact (ne_of_gt (lt_of_lt_of_le ha hxa)) hx0)
  rw [Set.uIcc_of_le hab] at hcont
  have hint : IntervalIntegrable (fun x : ℝ => x⁻¹) MeasureTheory.volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt Real.log (x⁻¹) x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    have hxa : a ≤ x := hx'.1
    exact Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le ha hxa))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem floorBoundaryKernel_eq_piecewise_pos (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    floorBoundaryKernel M hM t =
      if t ≤ 1 / (M : ℝ) then 1 else ((M : ℝ) * t)⁻¹ := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have habs : |t| ≤ 1 / 2 := by simpa [abs_of_nonneg ht0] using htHalf
  rw [floorBoundaryKernel_eq_min_of_abs_le_half M hM habs]
  by_cases hcentral : t ≤ 1 / (M : ℝ)
  · by_cases ht : t = 0
    · subst t
      simp
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
      have hprodpos : 0 < (M : ℝ) * t := mul_pos hMpos htpos
      have hprodle : (M : ℝ) * t ≤ 1 := by
        have := (le_div_iff₀ hMpos).mp hcentral
        nlinarith
      rw [if_neg ht, if_pos hcentral, abs_of_nonneg ht0]
      exact min_eq_left ((one_le_inv₀ hprodpos).2 hprodle)
  · have houter : 1 / (M : ℝ) < t := lt_of_not_ge hcentral
    have htpos : 0 < t := lt_trans (by positivity) houter
    have hprodpos : 0 < (M : ℝ) * t := mul_pos hMpos htpos
    have hprodgt : 1 < (M : ℝ) * t := by
      have := (div_lt_iff₀ hMpos).mp houter
      nlinarith [mul_comm t (M : ℝ)]
    have hinv : ((M : ℝ) * t)⁻¹ < 1 := (inv_lt_one₀ hprodpos).2 hprodgt
    have ht : t ≠ 0 := ne_of_gt htpos
    rw [if_neg ht, if_neg hcentral, abs_of_nonneg ht0]
    exact min_eq_right hinv.le

theorem intervalIntegral_floorBoundaryKernel_pos (M : ℕ) (hM : 2 ≤ M) :
    (∫ t in 0..(1 / 2 : ℝ), floorBoundaryKernel M hM t) =
      (1 / (M : ℝ)) * (1 + Real.log ((M : ℝ) / 2)) := by
  let a : ℝ := 1 / (M : ℝ)
  let b : ℝ := 1 / 2
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hapos : 0 < a := by dsimp [a]; positivity
  have hale : a ≤ b := by
    dsimp [a, b]
    exact one_div_le_one_div_of_le zero_lt_two hMge
  have hhalf : a ≤ 1 / 2 := by simpa [b] using hale
  have hbpos : 0 < b := by dsimp [b]; norm_num
  have hleftEq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
      (fun _ => (1 : ℝ)) (Set.uIcc 0 a) := by
    intro t ht
    change floorBoundaryKernel M hM t = 1
    have ht' : t ∈ Set.Icc 0 a := by simpa [Set.uIcc_of_le (le_of_lt hapos)] using ht
    have htcut : t ≤ 1 / (M : ℝ) := by simpa [a] using ht'.2
    have hprodle : (M : ℝ) * t ≤ 1 := by
      simpa [mul_comm] using (le_div_iff₀ hMpos).mp htcut
    by_cases ht0 : t = 0
    · subst t
      have hz : ∃ z : ℤ, (0 : ℝ) = (z : ℝ) := ⟨0, by simp⟩
      rw [floorBoundaryKernel, if_pos hz]
    · rw [floorBoundaryKernel_eq_min_of_abs_le_half M hM
        (by simpa [abs_of_nonneg ht'.1] using le_trans ht'.2 hhalf)]
      rw [if_neg ht0, abs_of_nonneg ht'.1]
      exact min_eq_left ((one_le_inv₀
        (mul_pos hMpos (lt_of_le_of_ne ht'.1 (Ne.symm ht0)))).2 hprodle)
  have hrightEq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
      (fun t => ((M : ℝ) * t)⁻¹) (Set.uIcc a b) := by
    intro t ht
    change floorBoundaryKernel M hM t = ((M : ℝ) * t)⁻¹
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hale] using ht
    have htpos : 0 ≤ t := le_trans hapos.le ht'.1
    have htHalf : t ≤ 1 / 2 := by simpa [b] using ht'.2
    have hlow : 1 / (M : ℝ) ≤ t := by simpa [a] using ht'.1
    rw [floorBoundaryKernel_eq_piecewise_pos M hM htpos htHalf]
    by_cases hcut : t ≤ 1 / (M : ℝ)
    · have heq : t = 1 / (M : ℝ) := le_antisymm hcut hlow
      rw [if_pos hcut, heq]
      simp [hMpos.ne']
    · rw [if_neg hcut]
  have hleftInt : IntervalIntegrable (fun t => floorBoundaryKernel M hM t)
      MeasureTheory.volume 0 a := by
    have hleftEq' : Set.EqOn (fun t => floorBoundaryKernel M hM t)
        (fun _ => (1 : ℝ)) (Set.uIoc 0 a) := hleftEq.mono Set.uIoc_subset_uIcc
    apply (intervalIntegrable_congr hleftEq').mpr
    exact intervalIntegrable_const
  have hmodelCont : ContinuousOn (fun t : ℝ => ((M : ℝ) * t)⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.inv₀ (continuousOn_const.mul continuousOn_id)
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hapos ht.1
    exact ne_of_gt (mul_pos hMpos htpos)
  have hrightInt : IntervalIntegrable (fun t => floorBoundaryKernel M hM t)
      MeasureTheory.volume a b := by
    have hrightEq' : Set.EqOn (fun t => floorBoundaryKernel M hM t)
        (fun t => ((M : ℝ) * t)⁻¹) (Set.uIoc a b) :=
      hrightEq.mono Set.uIoc_subset_uIcc
    apply (intervalIntegrable_congr hrightEq').mpr
    exact hmodelCont.intervalIntegrable_of_Icc hale
  have hleftVal : (∫ t in 0..a, floorBoundaryKernel M hM t) = a := by
    rw [intervalIntegral.integral_congr hleftEq]
    simp
  have hrightVal : (∫ t in a..b, floorBoundaryKernel M hM t) =
      (1 / (M : ℝ)) * (Real.log b - Real.log a) := by
    rw [intervalIntegral.integral_congr hrightEq]
    calc
      (∫ t in a..b, ((M : ℝ) * t)⁻¹) =
          (1 / (M : ℝ)) * (∫ t in a..b, t⁻¹) := by
        rw [show (fun t : ℝ => ((M : ℝ) * t)⁻¹) =
            (fun t => (1 / (M : ℝ)) * t⁻¹) by
              funext t
              field_simp]
        rw [intervalIntegral.integral_const_mul]
      _ = (1 / (M : ℝ)) * (Real.log b - Real.log a) := by
        rw [intervalIntegral_inv_eq_log_sub hapos hale]
  rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt,
    hleftVal, hrightVal]
  rw [← Real.log_div (ne_of_gt hbpos) (ne_of_gt hapos)]
  have harg : b / a = (M : ℝ) / 2 := by
    dsimp [a, b]
    field_simp
  rw [harg]
  dsimp [a, b]
  ring

theorem floorBoundaryKernel_even_of_abs_le_half (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : |t| ≤ 1 / 2) :
    floorBoundaryKernel M hM t = floorBoundaryKernel M hM (-t) := by
  have hneg : |-t| ≤ 1 / 2 := by simpa using ht
  rw [floorBoundaryKernel_eq_min_of_abs_le_half M hM ht,
    floorBoundaryKernel_eq_min_of_abs_le_half M hM hneg]
  simp [abs_neg]

theorem intervalIntegrable_floorBoundaryKernel_pos (M : ℕ) (hM : 2 ≤ M) :
    IntervalIntegrable (fun t => floorBoundaryKernel M hM t)
      MeasureTheory.volume 0 (1 / 2 : ℝ) := by
  let a : ℝ := 1 / (M : ℝ)
  let b : ℝ := 1 / 2
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hapos : 0 < a := by dsimp [a]; positivity
  have hale : a ≤ b := by
    dsimp [a, b]
    exact one_div_le_one_div_of_le zero_lt_two hMge
  have hhalf : a ≤ 1 / 2 := by simpa [b] using hale
  have hleftEq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
      (fun _ => (1 : ℝ)) (Set.uIcc 0 a) := by
    intro t ht
    change floorBoundaryKernel M hM t = 1
    have ht' : t ∈ Set.Icc 0 a := by simpa [Set.uIcc_of_le (le_of_lt hapos)] using ht
    have htcut : t ≤ 1 / (M : ℝ) := by simpa [a] using ht'.2
    have hprodle : (M : ℝ) * t ≤ 1 := by
      simpa [mul_comm] using (le_div_iff₀ hMpos).mp htcut
    by_cases ht0 : t = 0
    · subst t
      have hz : ∃ z : ℤ, (0 : ℝ) = (z : ℝ) := ⟨0, by simp⟩
      rw [floorBoundaryKernel, if_pos hz]
    · rw [floorBoundaryKernel_eq_min_of_abs_le_half M hM
        (by simpa [abs_of_nonneg ht'.1] using le_trans ht'.2 hhalf)]
      rw [if_neg ht0, abs_of_nonneg ht'.1]
      exact min_eq_left ((one_le_inv₀
        (mul_pos hMpos (lt_of_le_of_ne ht'.1 (Ne.symm ht0)))).2 hprodle)
  have hleft : IntervalIntegrable (fun t => floorBoundaryKernel M hM t)
      MeasureTheory.volume 0 a := by
    have heq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
        (fun _ => (1 : ℝ)) (Set.uIoc 0 a) := hleftEq.mono Set.uIoc_subset_uIcc
    exact (intervalIntegrable_congr heq).mpr intervalIntegrable_const
  have hrightEq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
      (fun t => ((M : ℝ) * t)⁻¹) (Set.uIcc a b) := by
    intro t ht
    change floorBoundaryKernel M hM t = ((M : ℝ) * t)⁻¹
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hale] using ht
    have htpos : 0 ≤ t := le_trans hapos.le ht'.1
    have htHalf : t ≤ 1 / 2 := by simpa [b] using ht'.2
    have hlow : 1 / (M : ℝ) ≤ t := by simpa [a] using ht'.1
    rw [floorBoundaryKernel_eq_piecewise_pos M hM htpos htHalf]
    by_cases hcut : t ≤ 1 / (M : ℝ)
    · have heq : t = 1 / (M : ℝ) := le_antisymm hcut hlow
      rw [if_pos hcut, heq]
      simp [hMpos.ne']
    · rw [if_neg hcut]
  have hmodelCont : ContinuousOn (fun t : ℝ => ((M : ℝ) * t)⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.inv₀ (continuousOn_const.mul continuousOn_id)
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hapos ht.1
    exact ne_of_gt (mul_pos hMpos htpos)
  have hright : IntervalIntegrable (fun t => floorBoundaryKernel M hM t)
      MeasureTheory.volume a b := by
    have heq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
        (fun t => ((M : ℝ) * t)⁻¹) (Set.uIoc a b) :=
      hrightEq.mono Set.uIoc_subset_uIcc
    exact (intervalIntegrable_congr heq).mpr
      (hmodelCont.intervalIntegrable_of_Icc hale)
  have htotal := hleft.trans hright
  simpa [b] using htotal

theorem intervalIntegral_floorBoundaryKernel_centered (M : ℕ) (hM : 2 ≤ M) :
    (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), floorBoundaryKernel M hM t) =
      (2 / (M : ℝ)) * (1 + Real.log ((M : ℝ) / 2)) := by
  let b : ℝ := 1 / 2
  have hbpos : 0 < b := by dsimp [b]; norm_num
  have hpos : IntervalIntegrable (fun t => floorBoundaryKernel M hM t)
      MeasureTheory.volume 0 b := by
    simpa [b] using intervalIntegrable_floorBoundaryKernel_pos M hM
  have hnegComp : IntervalIntegrable (fun t => floorBoundaryKernel M hM (-t))
      MeasureTheory.volume 0 (-b) :=
    by
      simpa using (IntervalIntegrable.iff_comp_neg
        (f := fun t => floorBoundaryKernel M hM t) (a := 0) (b := b)).mp hpos
  have hnegEq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
      (fun t => floorBoundaryKernel M hM (-t)) (Set.uIoc 0 (-b)) := by
    intro t ht
    have htIoc : -b < t ∧ t ≤ 0 := by
      simpa [Set.uIoc_of_ge (show -b ≤ 0 by linarith)] using ht
    have ht' : t ∈ Set.Icc (-b) 0 := by
      exact ⟨le_of_lt htIoc.1, htIoc.2⟩
    have htbound : |t| ≤ 1 / 2 := by
      rw [abs_le]
      constructor
      · have hlow : -(1 / 2 : ℝ) < t := by simpa [b] using htIoc.1
        linarith
      · linarith [htIoc.2]
    exact floorBoundaryKernel_even_of_abs_le_half M hM htbound
  have hnegF : IntervalIntegrable (fun t => floorBoundaryKernel M hM t)
      MeasureTheory.volume 0 (-b) :=
    (intervalIntegrable_congr hnegEq).mpr hnegComp
  have hneg : IntervalIntegrable (fun t => floorBoundaryKernel M hM t)
      MeasureTheory.volume (-b) 0 := hnegF.symm
  have hevenEq : Set.EqOn (fun t => floorBoundaryKernel M hM (-t))
      (fun t => floorBoundaryKernel M hM t) (Set.uIcc 0 b) := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 b := by simpa [Set.uIcc_of_le hbpos.le] using ht
    have htbound : |t| ≤ 1 / 2 := by
      rw [abs_of_nonneg ht'.1]
      simpa [b] using ht'.2
    exact (floorBoundaryKernel_even_of_abs_le_half M hM htbound).symm
  have hchange : (∫ t in 0..b, floorBoundaryKernel M hM (-t)) =
      ∫ t in (-b)..0, floorBoundaryKernel M hM t :=
    by
      simpa using (intervalIntegral.integral_comp_neg
        (f := fun t => floorBoundaryKernel M hM t) (a := 0) (b := b))
  have hnegValue : (∫ t in (-b)..0, floorBoundaryKernel M hM t) =
      ∫ t in 0..b, floorBoundaryKernel M hM t := by
    calc
      _ = ∫ t in 0..b, floorBoundaryKernel M hM (-t) := hchange.symm
      _ = ∫ t in 0..b, floorBoundaryKernel M hM t :=
        intervalIntegral.integral_congr hevenEq
  calc
    (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), floorBoundaryKernel M hM t) =
        ∫ t in (-b)..b, floorBoundaryKernel M hM t := by
          norm_num [b]
    _ = (∫ t in (-b)..0, floorBoundaryKernel M hM t) +
        ∫ t in 0..b, floorBoundaryKernel M hM t :=
          (intervalIntegral.integral_add_adjacent_intervals hneg hpos).symm
    _ = 2 * ((1 / (M : ℝ)) * (1 + Real.log ((M : ℝ) / 2))) := by
      rw [hnegValue, intervalIntegral_floorBoundaryKernel_pos]
      ring
    _ = (2 / (M : ℝ)) * (1 + Real.log ((M : ℝ) / 2)) := by ring

/-- The unit frequency `e(t)=exp(2πit)` used in the floor Fourier data. -/
noncomputable def unitFrequencyPhase (t : ℝ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * t) : ℂ) * Complex.I)

/-- The multiplier `b_N(ξ)` from blueprint `def:operators`, written using
the exact floor time and the unit frequency `e(t)=exp(2πit)`. -/
noncomputable def bN (c ξ : ℝ) (N : Scale) : ℂ :=
  (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
    unitFrequencyPhase (-ξ * (floorPower c n : ℝ))

/-- The polynomial-correlation seminorm from blueprint definition
`def:correlation`. For `s≥1` and a finite nonempty integer interval `I`,
this is the supremum over real polynomials of degree at most `s-1` of the
absolute normalized correlation with phase `e(-P(n))`. The definition is
written for an arbitrary finite set, which agrees with the paper on intervals.
-/
noncomputable def polynomialCorrelation (s : ℕ) (I : Finset ℤ)
    (w : ℤ → ℂ) : ℝ :=
  sSup (Set.range fun P : {P : Polynomial ℝ // P.natDegree ≤ s - 1} =>
    ‖(∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))) /
      (I.card : ℂ)‖)

/-- The finite `L∞` quantity from `def:correlation`, with the empty-set value
provided by the finite supremum convention. -/
noncomputable def polynomialCorrelationSupNorm (I : Finset ℤ) (w : ℤ → ℂ)
    (hI : I.Nonempty) : ℝ :=
  I.sup' hI fun n => ‖w n‖

/-- Every pointwise absolute value on the finite interval is bounded by its
finite `L∞` quantity. -/
theorem norm_le_polynomialCorrelationSupNorm {I : Finset ℤ} {w : ℤ → ℂ}
    (hI : I.Nonempty) {n : ℤ} (hn : n ∈ I) :
    ‖w n‖ ≤ polynomialCorrelationSupNorm I w hI := by
  exact Finset.le_sup' (s := I) (f := fun n => ‖w n‖) hn

/-- Negating the real phase parameter conjugates the unit frequency. -/
theorem unitFrequencyPhase_neg_eq_conj (t : ℝ) :
    unitFrequencyPhase (-t) = starRingEnd ℂ (unitFrequencyPhase t) := by
  unfold unitFrequencyPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem norm_unitFrequencyPhase (t : ℝ) : ‖unitFrequencyPhase t‖ = 1 := by
  unfold unitFrequencyPhase
  convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t) using 1

/-- The unique centered representative modulo integers in `[-1/2,1/2)`. -/
noncomputable def centeredFrequency (ξ : ℝ) : ℝ :=
  ξ - (⌊ξ + 1 / 2⌋ : ℝ)

/-- The chosen centered-frequency representative has exactly the half-open
interval convention used by the blueprint. -/
theorem centeredFrequency_mem (ξ : ℝ) :
    -(1 / 2 : ℝ) ≤ centeredFrequency ξ ∧ centeredFrequency ξ < 1 / 2 := by
  have hfloor := Int.floor_le (ξ + 1 / 2)
  have hnext := Int.lt_floor_add_one (ξ + 1 / 2)
  dsimp [centeredFrequency]
  constructor <;> linarith

/-- A frequency already in the chosen half-open interval is fixed by
`centeredFrequency`. -/
theorem centeredFrequency_eq_self_of_mem {ξ : ℝ}
    (hξ : -(1 / 2 : ℝ) ≤ ξ ∧ ξ < 1 / 2) :
    centeredFrequency ξ = ξ := by
  unfold centeredFrequency
  rw [centeredHalfShift_floor_eq_zero hξ]
  simp

/-- Centering is invariant under integer frequency shifts. -/
theorem centeredFrequency_add_int (ξ : ℝ) (z : ℤ) :
    centeredFrequency (ξ + z) = centeredFrequency ξ := by
  unfold centeredFrequency
  rw [show ξ + z + 1 / 2 = (ξ + 1 / 2) + z by push_cast; ring,
    Int.floor_add_intCast]
  push_cast
  ring

/-- The half-open representative is unique in its integer-translation
class: any representative in `[-1/2,1/2)` equals the selected one. -/
theorem centeredFrequency_unique {ξ η : ℝ}
    (hη : -(1 / 2 : ℝ) ≤ η ∧ η < 1 / 2)
    (hcongruent : ∃ z : ℤ, ξ = η + z) :
    centeredFrequency ξ = η := by
  rcases hcongruent with ⟨z, hz⟩
  calc
    centeredFrequency ξ = centeredFrequency (η + z) := by rw [hz]
    _ = centeredFrequency η := centeredFrequency_add_int η z
    _ = η := centeredFrequency_eq_self_of_mem hη

/-- Complex finite mean, with the blueprint's value zero on the empty set. -/
noncomputable def finiteMean {α : Type*} [DecidableEq α]
    (I : Finset α) (f : α → ℂ) : ℂ :=
  if I.Nonempty then I.sum f / (I.card : ℂ) else 0

@[simp] theorem finiteMean_empty {α : Type*} [DecidableEq α] (f : α → ℂ) :
    finiteMean (∅ : Finset α) f = 0 := by
  simp [finiteMean]

/-- The exact objects fixed by blueprint `def:notation`. This packages the
existing half-open interval, phase, torus representatives, distance and
boundary kernel together with the empty-aware finite mean. -/
structure ConventionData (Torus : Type*) [MeasurableSpace Torus] where
  integerInterval : ℝ → ℝ → Finset ℤ
  finiteMean : ∀ {α : Type*} [DecidableEq α], Finset α → (α → ℂ) → ℂ
  unitPhase : ℝ → ℂ
  fractionalPart : ℝ → ℝ
  torusMeasure : MeasureTheory.Measure Torus
  distanceToIntegers : ℝ → ℝ
  centeredFrequency : ℝ → ℝ
  boundaryKernel : (M : ℕ) → 2 ≤ M → ℝ → ℝ

noncomputable def conventions : ConventionData (AddCircle (1 : ℝ)) where
  integerInterval := realIntegerInterval
  finiteMean := @FractionalPrimes.finiteMean
  unitPhase := unitFrequencyPhase
  fractionalPart := Int.fract
  torusMeasure := AddCircle.haarAddCircle
  distanceToIntegers := realDistanceToIntegers
  centeredFrequency := centeredFrequency
  boundaryKernel := floorBoundaryKernel

/-- The packaged mean retains its declared empty-set value. -/
@[simp] theorem conventions_finiteMean_empty {α : Type*} [DecidableEq α]
    (f : α → ℂ) : conventions.finiteMean (∅ : Finset α) f = 0 := by
  simpa [conventions] using finiteMean_empty f

/-- The packaged frequency representative obeys the half-open convention. -/
theorem conventions_centeredFrequency_mem (ξ : ℝ) :
    -(1 / 2 : ℝ) ≤ conventions.centeredFrequency ξ ∧
      conventions.centeredFrequency ξ < 1 / 2 := by
  simpa [conventions] using centeredFrequency_mem ξ

/-- The packaged centered representative is the unique member of the
half-open interval in its integer-translation class. -/
theorem conventions_centeredFrequency_unique {ξ η : ℝ}
    (hη : -(1 / 2 : ℝ) ≤ η ∧ η < 1 / 2)
    (hcongruent : ∃ z : ℤ, ξ = η + z) :
    conventions.centeredFrequency ξ = η := by
  simpa [conventions] using centeredFrequency_unique hη hcongruent

/-- The packaged torus measure is the blueprint's normalized Haar measure. -/
theorem conventions_torusMeasure_univ :
    conventions.torusMeasure Set.univ = 1 := by
  change AddCircle.haarAddCircle Set.univ = 1
  exact MeasureTheory.IsProbabilityMeasure.measure_univ

/-- The packaged half-open integer interval has the exact floor-difference
cardinality from `def:notation`. -/
theorem conventions_integerInterval_card (x Y : ℝ) (hY : 0 < Y) :
    ((conventions.integerInterval x Y).card : ℤ) = ⌊x + Y⌋ - ⌊x⌋ := by
  simpa [conventions] using realIntegerInterval_card x Y hY

/-- The polynomial-correlation seminorm is bounded by the mean absolute value
of the weight on every nonempty finite set. -/
theorem polynomialCorrelation_le_mean_abs {s : ℕ} {I : Finset ℤ}
    {w : ℤ → ℂ} (hI : I.Nonempty) :
    polynomialCorrelation s I w ≤
      (∑ n ∈ I, ‖w n‖) / (I.card : ℝ) := by
  have hcard : 0 < I.card := Finset.card_pos.mpr hI
  have hcardReal : 0 < (I.card : ℝ) := by exact_mod_cast hcard
  have hpolys : Nonempty {P : Polynomial ℝ // P.natDegree ≤ s - 1} := by
    refine ⟨⟨0, ?_⟩⟩
    simp
  unfold polynomialCorrelation
  apply csSup_le
  · rcases hpolys with ⟨P⟩
    exact ⟨_, ⟨P, rfl⟩⟩
  · intro z hz
    rcases hz with ⟨P, rfl⟩
    have hsum :
        ‖∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ ≤
          ∑ n ∈ I, ‖w n‖ := by
      calc
        ‖∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ ≤
            ∑ n ∈ I, ‖w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ :=
          norm_sum_le _ _
        _ = ∑ n ∈ I, ‖w n‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [norm_mul, norm_unitFrequencyPhase, mul_one]
    have hdenom : ‖(I.card : ℂ)‖ = (I.card : ℝ) := by simp
    calc
      ‖(∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))) /
          (I.card : ℂ)‖ =
          ‖∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ /
            ‖(I.card : ℂ)‖ := norm_div _ _
      _ = ‖∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ /
            (I.card : ℝ) := by rw [hdenom]
      _ ≤ (∑ n ∈ I, ‖w n‖) / (I.card : ℝ) :=
        div_le_div_of_nonneg_right hsum (le_of_lt hcardReal)

/-- The correlation class includes the zero polynomial, as specified by the
blueprint's degree cutoff. -/
theorem polynomialCorrelation_zeroPolynomial_mem (s : ℕ) :
    (0 : Polynomial ℝ).natDegree ≤ s - 1 := by
  simp

theorem unitFrequencyPhase_add (s t : ℝ) :
    unitFrequencyPhase (s + t) = unitFrequencyPhase s * unitFrequencyPhase t := by
  unfold unitFrequencyPhase
  rw [show (↑(2 * Real.pi * (s + t)) : ℂ) * Complex.I =
    (↑(2 * Real.pi * s) : ℂ) * Complex.I +
      (↑(2 * Real.pi * t) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add]

theorem norm_one_sub_unitFrequencyPhase_neg_eq (t : ℝ) :
    ‖1 - unitFrequencyPhase (-t)‖ = ‖1 - unitFrequencyPhase t‖ := by
  have hmul : unitFrequencyPhase (-t) * unitFrequencyPhase t = 1 := by
    simpa [unitFrequencyPhase] using (unitFrequencyPhase_add (-t) t).symm
  calc
    ‖1 - unitFrequencyPhase (-t)‖ =
        ‖unitFrequencyPhase (-t) * (unitFrequencyPhase t - 1)‖ := by
          congr 1
          calc
            1 - unitFrequencyPhase (-t) =
                unitFrequencyPhase (-t) * unitFrequencyPhase t -
                  unitFrequencyPhase (-t) := by rw [hmul]
            _ = unitFrequencyPhase (-t) * (unitFrequencyPhase t - 1) := by ring
    _ = ‖unitFrequencyPhase (-t)‖ * ‖unitFrequencyPhase t - 1‖ := norm_mul _ _
    _ = ‖1 - unitFrequencyPhase t‖ := by
          rw [norm_unitFrequencyPhase]
          rw [show unitFrequencyPhase t - 1 = -(1 - unitFrequencyPhase t) by ring,
            norm_neg, one_mul]

theorem unitFrequencyPhase_nat_mul (n : ℕ) (t : ℝ) :
    unitFrequencyPhase ((n : ℝ) * t) = unitFrequencyPhase t ^ n := by
  induction n with
  | zero => simp [unitFrequencyPhase]
  | succ n ih =>
    calc
      unitFrequencyPhase (((n + 1 : ℕ) : ℝ) * t) =
          unitFrequencyPhase ((n : ℝ) * t + t) := by congr 1 <;> push_cast <;> ring
      _ = unitFrequencyPhase ((n : ℝ) * t) * unitFrequencyPhase t :=
          unitFrequencyPhase_add _ _
      _ = unitFrequencyPhase t ^ n * unitFrequencyPhase t := by rw [ih]
      _ = unitFrequencyPhase t ^ (n + 1) := by rw [pow_succ]

/-- Integer frequencies have unit phase one. -/
theorem unitFrequencyPhase_int (n : ℤ) : unitFrequencyPhase (n : ℝ) = 1 := by
  unfold unitFrequencyPhase
  rw [show (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
      (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I]

/-- The integral of a unit-frequency exponential over one period. -/
theorem intervalIntegral_unitFrequencyPhase_mul (a : ℝ) :
    (∫ x in (0 : ℝ)..1, unitFrequencyPhase (a * x)) =
      if a = 0 then 1 else
        (unitFrequencyPhase a - 1) /
          (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
  by_cases ha : a = 0
  · simp [ha, unitFrequencyPhase]
  let c : ℂ := ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by positivity) ha)
    · exact Complex.I_ne_zero
  have hexp (x : ℝ) : unitFrequencyPhase (a * x) = Complex.exp (c * x) := by
    dsimp [unitFrequencyPhase, c]
    congr 1
    push_cast
    ring
  have hphase : unitFrequencyPhase a = Complex.exp c := by
    dsimp [unitFrequencyPhase, c]
  rw [if_neg ha]
  rw [show (fun x : ℝ => unitFrequencyPhase (a * x)) =
      fun x : ℝ => Complex.exp (c * (x : ℂ)) from funext hexp,
    integral_exp_mul_complex hc]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero,
    Complex.exp_zero]
  rw [← hphase]

/-- Chord bound for the unit-frequency exponential, used for the zero
coefficient of the floor Fourier expansion. -/
theorem norm_one_sub_unitFrequencyPhase_neg_le (ξ : ℝ) :
    ‖1 - unitFrequencyPhase (-ξ)‖ ≤ 2 * Real.pi * |ξ| := by
  have hphase : unitFrequencyPhase (-ξ) =
      Complex.exp (Complex.I * ((2 * Real.pi * (-ξ) : ℝ) : ℂ)) := by
    unfold unitFrequencyPhase
    rw [mul_comm ((2 * Real.pi * (-ξ) : ℝ) : ℂ) Complex.I]
  have hnorm := Complex.norm_exp_I_mul_ofReal_sub_one
    (2 * Real.pi * (-ξ))
  have hsin : |Real.sin (-Real.pi * ξ)| ≤ |Real.pi * ξ| := by
    have h := Real.abs_sin_le_abs (x := Real.pi * ξ)
    simpa [abs_neg] using h
  calc
    ‖1 - unitFrequencyPhase (-ξ)‖ =
        ‖Complex.exp (Complex.I * ((2 * Real.pi * (-ξ) : ℝ) : ℂ)) - 1‖ := by
          rw [hphase]
          rw [show (1 : ℂ) - Complex.exp
            (Complex.I * ((2 * Real.pi * (-ξ) : ℝ) : ℂ)) =
              -(Complex.exp (Complex.I * ((2 * Real.pi * (-ξ) : ℝ) : ℂ)) - 1) by ring,
            norm_neg]
    _ = ‖(2 * Real.sin ((2 * Real.pi * (-ξ)) / 2) : ℝ)‖ := hnorm
    _ = 2 * |Real.sin (-Real.pi * ξ)| := by
      rw [Real.norm_eq_abs, abs_mul,
        show |(2 : ℝ)| = 2 by norm_num,
        show (2 * Real.pi * (-ξ)) / 2 = -Real.pi * ξ by ring]
    _ ≤ 2 * |Real.pi * ξ| := mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ = 2 * Real.pi * |ξ| := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

/-- On the centered interval, the chord from one to the unit phase controls
distance to the integer lattice. -/
theorem four_mul_realDistanceToIntegers_le_norm_one_sub_unitFrequencyPhase
    {t : ℝ} (ht : |t| ≤ 1 / 2) :
    4 * realDistanceToIntegers t ≤ ‖1 - unitFrequencyPhase t‖ := by
  have hsinRange : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using ht) Real.pi_pos.le
  have hsin := Real.mul_abs_le_abs_sin hsinRange
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hsin' : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    calc
      2 * |t| = (2 / Real.pi) * (Real.pi * |t|) := by field_simp
      _ ≤ |Real.sin (Real.pi * t)| := hsin
  have hphase : unitFrequencyPhase t =
      Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    unfold unitFrequencyPhase
    rw [mul_comm ((2 * Real.pi * t : ℝ) : ℂ) Complex.I]
  have hnorm := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * t)
  calc
    4 * realDistanceToIntegers t = 4 * |t| := by
      rw [realDistanceToIntegers_eq_abs_of_abs_le_half ht]
    _ ≤ 2 * |Real.sin (Real.pi * t)| := by nlinarith [hsin']
    _ = ‖1 - unitFrequencyPhase t‖ := by
      symm
      calc
        ‖1 - unitFrequencyPhase t‖ =
            ‖unitFrequencyPhase t - 1‖ := by
              rw [show (1 : ℂ) - unitFrequencyPhase t =
                -(unitFrequencyPhase t - 1) by ring, norm_neg]
        _ = ‖Complex.exp
              (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) - 1‖ := by rw [hphase]
        _ = ‖(2 * Real.sin ((2 * Real.pi * t) / 2) : ℝ)‖ := hnorm
        _ = 2 * |Real.sin (Real.pi * t)| := by
          rw [show (2 * Real.pi * t) / 2 = Real.pi * t by ring,
            Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 by norm_num]

theorem norm_one_sub_unitFrequencyPhase_pos_of_centered_ne_zero
    {t : ℝ} (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    0 < ‖1 - unitFrequencyPhase t‖ := by
  have hdist : 0 < realDistanceToIntegers t := by
    rw [realDistanceToIntegers_eq_abs_of_abs_le_half ht]
    exact abs_pos.mpr ht0
  have hchord := four_mul_realDistanceToIntegers_le_norm_one_sub_unitFrequencyPhase ht
  nlinarith

/-- Fourier coefficient of the centered floor function, including its
separate zero-frequency convention. -/
noncomputable def floorFourierCoefficient (m : ℤ) (ξ : ℝ) : ℂ :=
  if ξ = 0 then if m = 0 then 1 else 0 else
    (1 - unitFrequencyPhase (-ξ)) /
      ((2 * Real.pi : ℝ) * Complex.I * ((m : ℂ) + (ξ : ℂ)))

local instance floorFourierCirclePeriodPos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The circle function whose Fourier coefficients are the blueprint's floor
coefficients: on `(0,1]` it is `e(-ξ t)`, extended periodically. -/
noncomputable def floorFourierCircleFunction (ξ : ℝ) : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 (fun t => unitFrequencyPhase (-ξ * t))

/-- The fractional-part circle function is continuous away from its jump at
the zero class. -/
theorem floorFourierCircleFunction_continuousAt_of_ne_zero
    {ξ : ℝ} {x : AddCircle (1 : ℝ)} (hx : x ≠ 0) :
    ContinuousAt (floorFourierCircleFunction ξ) x := by
  let g : ℝ → ℂ := fun t => unitFrequencyPhase (-ξ * t)
  have hg : Continuous g := by
    dsimp [g, unitFrequencyPhase]
    fun_prop
  have hEq : (fun y : AddCircle (1 : ℝ) =>
      AddCircle.liftIco (p := (1 : ℝ)) (a := (0 : ℝ)) g y) =ᶠ[nhds x]
      fun y => AddCircle.liftIoc (p := (1 : ℝ)) (a := (0 : ℝ)) g y := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
    exact (AddCircle.liftIoc_eq_liftIco_of_ne (f := g) hy).symm
  have hIco : ContinuousAt
      (AddCircle.liftIco (p := (1 : ℝ)) (a := (0 : ℝ)) g) x := by
    change ContinuousAt (fun y : AddCircle (1 : ℝ) =>
      g (((AddCircle.equivIco (1 : ℝ) (0 : ℝ) y :
        Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ))) x
    exact hg.continuousAt.comp
      (continuousAt_subtype_val.comp
        (AddCircle.continuousAt_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) hx))
  rw [floorFourierCircleFunction]
  exact hIco.congr hEq

set_option maxHeartbeats 1000000 in
/-- The fractional-part circle function is square-integrable, since its
representative on one period has unit modulus. -/
theorem floorFourierCircleFunction_memLp (ξ : ℝ) :
    MeasureTheory.MemLp (floorFourierCircleFunction ξ) 2 := by
  let g : ℝ → ℂ := fun t => unitFrequencyPhase (-ξ * t)
  have hgcont : Continuous g := by
    dsimp [g, unitFrequencyPhase]
    exact Complex.continuous_exp.comp (by fun_prop)
  have hgmeas :
      MeasureTheory.AEStronglyMeasurable g
        (MeasureTheory.volume.restrict (Set.Ioc 0 (0 + 1))) :=
    hgcont.aestronglyMeasurable
  have hgbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc 0 (0 + 1))),
      ‖g t‖ ≤ 1 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖unitFrequencyPhase (-ξ * t)‖ ≤ 1
    rw [norm_unitFrequencyPhase]
  have hglp : MeasureTheory.MemLp g 2
      (MeasureTheory.volume.restrict (Set.Ioc 0 (0 + 1))) :=
    MeasureTheory.MemLp.of_bound hgmeas 1 hgbound
  change MeasureTheory.MemLp (AddCircle.liftIoc 1 0 g) 2
  exact hglp.memLp_liftIoc

set_option maxHeartbeats 1000000 in
/-- The Fourier coefficients of the fractional-part circle function are the
blueprint's coefficients, with its separate zero-frequency convention. -/
theorem floorFourierCircleFunction_fourierCoeff
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2) (m : ℤ) :
    fourierCoeff (floorFourierCircleFunction ξ) m =
      floorFourierCoefficient m ξ := by
  let a : ℝ := -((m : ℝ) + ξ)
  have hcoeff :
      fourierCoeff (floorFourierCircleFunction ξ) m =
        fourierCoeffOn (by norm_num : (0 : ℝ) < 0 + 1)
          (fun t => unitFrequencyPhase (-ξ * t)) m := by
    rw [floorFourierCircleFunction, fourierCoeff_liftIoc_eq]
  have hfourier (x : ℝ) :
      fourier (-m) (x : AddCircle ((0 : ℝ) + 1 - 0)) =
        unitFrequencyPhase (-(m : ℝ) * x) := by
    rw [fourier_coe_apply]
    unfold unitFrequencyPhase
    congr 1
    push_cast
    ring
  have hintegrand :
      (fun x : ℝ => fourier (-m) (x : AddCircle ((0 : ℝ) + 1 - 0)) •
        unitFrequencyPhase (-ξ * x)) =
      (fun x : ℝ => unitFrequencyPhase (a * x)) := by
    funext x
    rw [hfourier, smul_eq_mul, ← unitFrequencyPhase_add]
    congr 1
    dsimp [a]
    ring
  have hcoeffInt :
      fourierCoeff (floorFourierCircleFunction ξ) m =
        ∫ x in (0 : ℝ)..1, unitFrequencyPhase (a * x) := by
    rw [hcoeff, fourierCoeffOn_eq_integral]
    have hinter :
        (∫ x in (0 : ℝ)..(0 + 1),
            fourier (-m) (x : AddCircle ((0 : ℝ) + 1 - 0)) •
              unitFrequencyPhase (-ξ * x)) =
          ∫ x in (0 : ℝ)..(0 + 1), unitFrequencyPhase (a * x) :=
      intervalIntegral.integral_congr (fun x _ => congrFun hintegrand x)
    calc
      (1 / (0 + 1 - 0) : ℝ) •
          ∫ x in (0 : ℝ)..(0 + 1),
            fourier (-m) (x : AddCircle ((0 : ℝ) + 1 - 0)) •
              unitFrequencyPhase (-ξ * x) =
        (1 / (0 + 1 - 0) : ℝ) •
          ∫ x in (0 : ℝ)..(0 + 1), unitFrequencyPhase (a * x) :=
            congrArg (fun z : ℂ => (1 / (0 + 1 - 0) : ℝ) • z) hinter
      _ = ∫ x in (0 : ℝ)..1, unitFrequencyPhase (a * x) := by norm_num
  by_cases hspecial : m = 0 ∧ ξ = 0
  · rcases hspecial with ⟨rfl, rfl⟩
    have ha : a = 0 := by simp [a]
    rw [hcoeffInt, intervalIntegral_unitFrequencyPhase_mul]
    simp [ha, floorFourierCoefficient, a]
  · have ha : a ≠ 0 := by
      intro ha0
      have hsum : (m : ℝ) + ξ = 0 := by
        dsimp [a] at ha0
        linarith
      by_cases hm : m = 0
      · subst m
        have hξ : ξ = 0 := by simpa using hsum
        exact hspecial ⟨rfl, hξ⟩
      · have hmInt : (1 : ℤ) ≤ |m| := by
          rcases lt_or_gt_of_ne hm with hmneg | hmpos
          · rw [abs_of_neg hmneg]
            omega
          · rw [abs_of_pos hmpos]
            omega
        have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hmInt
        have hmeq : (m : ℝ) = -ξ := by linarith
        have habs : |(m : ℝ)| = |ξ| := by rw [hmeq, abs_neg]
        have hξabs : |ξ| ≤ 1 / 2 :=
          abs_le.mpr ⟨by linarith, le_of_lt hξhi⟩
        nlinarith
    have hmphase : unitFrequencyPhase (-(m : ℝ)) = 1 := by
      have hcast : -(m : ℝ) = ((-m : ℤ) : ℝ) := by norm_cast
      rw [hcast, unitFrequencyPhase_int]
    have hphaseA : unitFrequencyPhase a = unitFrequencyPhase (-ξ) := by
      dsimp [a]
      calc
        unitFrequencyPhase (-((m : ℝ) + ξ)) =
            unitFrequencyPhase (-(m : ℝ) + (-ξ)) := by congr 1 <;> ring
        _ = unitFrequencyPhase (-(m : ℝ)) * unitFrequencyPhase (-ξ) :=
          unitFrequencyPhase_add _ _
        _ = unitFrequencyPhase (-ξ) := by rw [hmphase]; simp
    have hdenCast :
        ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I =
          -(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            ((m : ℂ) + (ξ : ℂ))) := by
      dsimp [a]
      push_cast
      ring
    have hcoefDen :
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          ((m : ℂ) + (ξ : ℂ))) ≠ 0 := by
      have hdenA :
          ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I ≠ 0 := by
        apply mul_ne_zero
        · exact Complex.ofReal_ne_zero.mpr
            (mul_ne_zero (by positivity) ha)
        · exact Complex.I_ne_zero
      intro hzero
      apply hdenA
      rw [hdenCast, hzero]
      simp
    rw [hcoeffInt, intervalIntegral_unitFrequencyPhase_mul, if_neg ha,
      hphaseA, hdenCast]
    by_cases hξ : ξ = 0
    · have hm : m ≠ 0 := by
        intro hm
        exact hspecial ⟨hm, hξ⟩
      simp [floorFourierCoefficient, hξ, hm, unitFrequencyPhase]
    · rw [floorFourierCoefficient, if_neg hξ]
      field_simp [hcoefDen]
      ring

/-- The Fourier series of the fractional-part circle function converges to it
in `L²`, by Mathlib's Fourier Hilbert basis theorem. -/
theorem floorFourierCircleFunction_hasSum_fourier_series_L2 (ξ : ℝ) :
    HasSum
      (fun m : ℤ =>
        fourierCoeff (floorFourierCircleFunction ξ) m • fourierLp 2 m)
      ((floorFourierCircleFunction_memLp ξ).haarAddCircle.toLp
        (floorFourierCircleFunction ξ)) := by
  let hmem := (floorFourierCircleFunction_memLp ξ).haarAddCircle
  have hcoeffFun :
      fourierCoeff (hmem.toLp (floorFourierCircleFunction ξ)) =
        fourierCoeff (floorFourierCircleFunction ξ) :=
    fourierCoeff_congr_ae hmem.coeFn_toLp
  have hcoeff (m : ℤ) := congrFun hcoeffFun m
  simpa only [hcoeff] using
    (hasSum_fourier_series_L2 (hmem.toLp (floorFourierCircleFunction ξ)))

/-- The same L² Fourier expansion converges along the blueprint's symmetric
integer intervals `Icc (-M) M`. -/
theorem floorFourierCircleFunction_symmetric_fourier_series_L2 (ξ : ℝ) :
    HasSum
      (fun m : ℤ =>
        fourierCoeff (floorFourierCircleFunction ξ) m • fourierLp 2 m)
      ((floorFourierCircleFunction_memLp ξ).haarAddCircle.toLp
        (floorFourierCircleFunction ξ))
      (SummationFilter.symmetricIcc ℤ) := by
  apply (floorFourierCircleFunction_hasSum_fourier_series_L2 ξ).mono_left
  exact SummationFilter.le_atTop

set_option maxHeartbeats 1000000 in
/-- The symmetric finite Fourier partial sums converge in `L²` to the
fractional-part circle function represented in Haar `Lp`. -/
theorem floorFourierCircleFunction_symmetric_fourier_partialSums_tendsto
    (ξ : ℝ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          fourierCoeff (floorFourierCircleFunction ξ) m • fourierLp 2 m)
      Filter.atTop
      (nhds ((floorFourierCircleFunction_memLp ξ).haarAddCircle.toLp
        (floorFourierCircleFunction ξ))) := by
  have hs := floorFourierCircleFunction_symmetric_fourier_series_L2 ξ
  simpa only [HasSum, SummationFilter.symmetricIcc_eq_map_Icc_nat,
    Filter.tendsto_map'_iff, Function.comp_def] using hs

/-- A subsequence of the symmetric Fourier partial sums converges pointwise
almost everywhere to the circle function representative. -/
theorem floorFourierCircleFunction_exists_ae_tendsto_symmetric_fourier_subseq
    (ξ : ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂AddCircle.haarAddCircle,
        Filter.Tendsto
          (fun i =>
            (∑ m ∈ Finset.Icc (-(ns i : ℤ)) (ns i : ℤ),
              fourierCoeff (floorFourierCircleFunction ξ) m • fourierLp 2 m) x)
          Filter.atTop
          (nhds (((floorFourierCircleFunction_memLp ξ).haarAddCircle.toLp
            (floorFourierCircleFunction ξ)) x)) := by
  exact
    (MeasureTheory.tendstoInMeasure_of_tendsto_Lp
      (floorFourierCircleFunction_symmetric_fourier_partialSums_tendsto ξ)).exists_seq_tendsto_ae

/-- The finite `Lp` Fourier partial sum has the expected pointwise finite
Fourier-sum representative almost everywhere. -/
theorem floorFourierCircleFunction_fourier_partialSum_coe_ae
    (ξ : ℝ) (M : ℕ) :
    ⇑(∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      fourierCoeff (floorFourierCircleFunction ξ) m •
        fourierLp (T := (1 : ℝ)) 2 m) =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
      (fun x =>
        ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          fourierCoeff (floorFourierCircleFunction ξ) m * fourier m x) := by
  have hsum := eventuallyEq_sum
    (s := Finset.Icc (-(M : ℤ)) (M : ℤ))
    (f := fun m x =>
      (fourierCoeff (floorFourierCircleFunction ξ) m •
        fourierLp (T := (1 : ℝ)) 2 m) x)
    (g := fun m x =>
      fourierCoeff (floorFourierCircleFunction ξ) m * fourier m x)
    (fun m hm => by
      filter_upwards [MeasureTheory.Lp.coeFn_smul
        (fourierCoeff (floorFourierCircleFunction ξ) m)
          (fourierLp (T := (1 : ℝ)) 2 m),
        coeFn_fourierLp (T := (1 : ℝ)) 2 m] with x hsmul hfourier
      rw [hsmul]
      calc
        (fourierCoeff (floorFourierCircleFunction ξ) m •
            (↑(fourierLp (T := (1 : ℝ)) 2 m) : AddCircle (1 : ℝ) → ℂ)) x =
            fourierCoeff (floorFourierCircleFunction ξ) m *
              (↑(fourierLp (T := (1 : ℝ)) 2 m) : AddCircle (1 : ℝ) → ℂ) x := by
                simp [smul_eq_mul]
        _ = fourierCoeff (floorFourierCircleFunction ξ) m * fourier m x := by
          rw [hfourier])
  have hfun :
      (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        fun x : AddCircle (1 : ℝ) =>
          fourierCoeff (floorFourierCircleFunction ξ) m * fourier m x) =
        (fun x =>
          ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            fourierCoeff (floorFourierCircleFunction ξ) m * fourier m x) := by
    funext x
    simp
  exact (MeasureTheory.Lp.coeFn_finsetSum
      (Finset.Icc (-(M : ℤ)) (M : ℤ))
      (fun m => fourierCoeff (floorFourierCircleFunction ξ) m •
        fourierLp (T := (1 : ℝ)) 2 m)).trans <|
    hsum.trans (Filter.Eventually.of_forall fun x => congrFun hfun x)

theorem floorFourierCircleFunction_exists_ae_tendsto_pointwise_fourier_subseq
    (ξ : ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂AddCircle.haarAddCircle,
        Filter.Tendsto
          (fun i =>
            ∑ m ∈ Finset.Icc (-(ns i : ℤ)) (ns i : ℤ),
              fourierCoeff (floorFourierCircleFunction ξ) m * fourier m x)
          Filter.atTop (nhds (floorFourierCircleFunction ξ x)) := by
  obtain ⟨ns, hns, hlim⟩ :=
    floorFourierCircleFunction_exists_ae_tendsto_symmetric_fourier_subseq ξ
  have hrep : ∀ᵐ x ∂AddCircle.haarAddCircle, ∀ M : ℕ,
      (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        fourierCoeff (floorFourierCircleFunction ξ) m •
          fourierLp (T := (1 : ℝ)) 2 m) x =
      ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        fourierCoeff (floorFourierCircleFunction ξ) m * fourier m x := by
    rw [MeasureTheory.ae_all_iff]
    intro M
    exact floorFourierCircleFunction_fourier_partialSum_coe_ae ξ M
  have htoLp := (floorFourierCircleFunction_memLp ξ).haarAddCircle.coeFn_toLp
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hlim, hrep, htoLp] with x hxlim hxrep hxeq
  have heq :
      (fun i =>
        ∑ m ∈ Finset.Icc (-(ns i : ℤ)) (ns i : ℤ),
          fourierCoeff (floorFourierCircleFunction ξ) m * fourier m x) =ᶠ[Filter.atTop]
      (fun i =>
        (∑ m ∈ Finset.Icc (-(ns i : ℤ)) (ns i : ℤ),
          fourierCoeff (floorFourierCircleFunction ξ) m •
            fourierLp (T := (1 : ℝ)) 2 m) x) := by
    exact Filter.Eventually.of_forall fun i => (hxrep (ns i)).symm
  have hpoint := (Filter.tendsto_congr' heq).2 hxlim
  simpa only [hxeq] using hpoint

/-- Reindex an integer half-open interval by its natural-number offset. -/
theorem sum_Ico_int_eq_sum_range_offset {α : Type*} [AddCommMonoid α]
    (f : ℤ → α) (a b : ℤ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, f n =
      ∑ k ∈ Finset.range (Int.toNat (b - a)), f (a + k) := by
  classical
  apply Finset.sum_bij (fun n _ => Int.toNat (n - a))
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    simp only [Finset.mem_Ico, Finset.mem_range]
    have hna : 0 ≤ n - a := by omega
    have hba : 0 ≤ b - a := by omega
    have hnatA : ((n - a).toNat : ℤ) = n - a := Int.toNat_of_nonneg hna
    have hnatB : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg hba
    have hlt : ((n - a).toNat : ℤ) < (b - a).toNat := by
      rw [hnatA, hnatB]
      omega
    exact_mod_cast hlt
  · intro n hn₁ m hn₂ hEq
    simp only [Finset.mem_Ico] at hn₁ hn₂
    have hna : 0 ≤ n - a := by omega
    have hma : 0 ≤ m - a := by omega
    have hnatN : ((n - a).toNat : ℤ) = n - a := Int.toNat_of_nonneg hna
    have hnatM : ((m - a).toNat : ℤ) = m - a := Int.toNat_of_nonneg hma
    have hcast : ((n - a).toNat : ℤ) = (m - a).toNat := by exact_mod_cast hEq
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    have hba : 0 ≤ b - a := by omega
    have hnatB : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg hba
    have hklt : (k : ℤ) < b - a := by
      have hcast : (k : ℤ) < ((b - a).toNat : ℤ) := by exact_mod_cast hk
      rw [hnatB] at hcast
      exact hcast
    refine ⟨a + k, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      constructor <;> omega
    · simp [Int.toNat_natCast]
  · intro n hn
    have hna : 0 ≤ n - a := by
      have hmem := Finset.mem_Ico.mp hn
      omega
    rw [Int.toNat_of_nonneg hna]
    congr 1
    omega

/-- Split the difference of two symmetric integer intervals into its
positive and negative tails, with the half-open endpoints explicit. -/
theorem symmetricIcc_diff_eq_positive_negative_Ico (M N : ℕ) (hMN : M ≤ N) :
    Finset.Icc (-(N : ℤ)) N \ Finset.Icc (-(M : ℤ)) M =
      Finset.Ico ((M : ℤ) + 1) ((N : ℤ) + 1) ∪
        Finset.Ico (-(N : ℤ)) (-(M : ℤ)) := by
  ext m
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]
  omega

/-- The two tails in the symmetric-interval difference are disjoint. -/
theorem symmetricIcc_positive_negative_Ico_disjoint (M N : ℕ) :
    Disjoint (Finset.Ico ((M : ℤ) + 1) ((N : ℤ) + 1))
      (Finset.Ico (-(N : ℤ)) (-(M : ℤ))) := by
  apply Finset.disjoint_left.mpr
  intro m hmPos hmNeg
  simp only [Finset.mem_Ico] at hmPos hmNeg
  omega

/-- Exact additive decomposition of a larger symmetric sum into the smaller
symmetric sum and the two tails. -/
theorem sum_symmetricIcc_eq_sum_symmetricIcc_add_tails
    {α : Type*} [AddCommMonoid α] (f : ℤ → α) (M N : ℕ) (hMN : M ≤ N) :
    (∑ m ∈ Finset.Icc (-(N : ℤ)) N, f m) =
      (∑ m ∈ Finset.Icc (-(M : ℤ)) M, f m) +
        (∑ m ∈ Finset.Ico ((M : ℤ) + 1) ((N : ℤ) + 1), f m) +
        (∑ m ∈ Finset.Ico (-(N : ℤ)) (-(M : ℤ)), f m) := by
  have hsub : Finset.Icc (-(M : ℤ)) M ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  have hsum := Finset.sum_sdiff (f := f) hsub
  rw [symmetricIcc_diff_eq_positive_negative_Ico M N hMN,
    Finset.sum_union (symmetricIcc_positive_negative_Ico_disjoint M N)] at hsum
  calc
    (∑ m ∈ Finset.Icc (-(N : ℤ)) N, f m) =
        (∑ m ∈ Finset.Ico ((M : ℤ) + 1) ((N : ℤ) + 1), f m) +
          (∑ m ∈ Finset.Ico (-(N : ℤ)) (-(M : ℤ)), f m) +
          (∑ m ∈ Finset.Icc (-(M : ℤ)) M, f m) := hsum.symm
    _ = _ := by abel

/-- Reversing a finite natural range preserves its sum. -/
theorem sum_range_reverse_sub {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (L : ℕ) :
    ∑ k ∈ Finset.range L, f (L - 1 - k) =
      ∑ k ∈ Finset.range L, f k := by
  classical
  apply Finset.sum_bij (fun k _ => L - 1 - k)
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk j hj h
    simp only [Finset.mem_range] at hk hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨L - 1 - j, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    congr 1

/-- Reindex the positive tail interval by frequencies `M+1+k`. -/
theorem sum_positive_Ico_eq_sum_range {α : Type*} [AddCommMonoid α]
    (f : ℤ → α) (M N : ℕ) (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ico ((M : ℤ) + 1) ((N : ℤ) + 1), f m =
      ∑ k ∈ Finset.range (N - M), f ((M + 1 + k : ℕ) : ℤ) := by
  have hdiff : ((N : ℤ) + 1) - ((M : ℤ) + 1) = ((N - M : ℕ) : ℤ) := by
    push_cast
    omega
  have hlen : Int.toNat (((N : ℤ) + 1) - ((M : ℤ) + 1)) = N - M := by
    rw [hdiff, Int.toNat_natCast]
  rw [sum_Ico_int_eq_sum_range_offset f ((M : ℤ) + 1) ((N : ℤ) + 1) (by omega), hlen]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1

/-- Reindex the negative tail interval by the reflected frequencies
`-(M+1+k)`, matching the negative coefficient-tail estimate. -/
theorem sum_negative_Ico_eq_sum_range {α : Type*} [AddCommMonoid α]
    (f : ℤ → α) (M N : ℕ) (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ico (-(N : ℤ)) (-(M : ℤ)), f m =
      ∑ k ∈ Finset.range (N - M), f (-(M + 1 + k : ℕ) : ℤ) := by
  have hdiff : (-(M : ℤ)) - (-(N : ℤ)) = ((N - M : ℕ) : ℤ) := by
    have hsub : ((N - M : ℕ) : ℤ) = (N : ℤ) - M := by
      exact Nat.cast_sub hMN
    rw [hsub]
    ring
  have hlen : Int.toNat ((-(M : ℤ)) - (-(N : ℤ))) = N - M := by
    rw [hdiff, Int.toNat_natCast]
  rw [sum_Ico_int_eq_sum_range_offset f (-(N : ℤ)) (-(M : ℤ)) (by omega), hlen]
  calc
    (∑ k ∈ Finset.range (N - M), f (-(N : ℤ) + k)) =
        ∑ k ∈ Finset.range (N - M),
          f (-(M + 1 + ((N - M) - 1 - k) : ℕ) : ℤ) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk' : k < N - M := Finset.mem_range.mp hk
            congr 1
            push_cast
            omega
    _ = ∑ k ∈ Finset.range (N - M), f (-(M + 1 + k : ℕ) : ℤ) := by
      simpa using
        (sum_range_reverse_sub
          (fun j : ℕ => f (-(M + 1 + j : ℕ) : ℤ)) (N - M))

/-- The larger symmetric sum is exactly the smaller sum plus the positive and
negative tails in the natural indexing used by the analytic estimates. -/
theorem sum_symmetricIcc_eq_sum_symmetricIcc_add_range_tails
    {α : Type*} [AddCommMonoid α] (f : ℤ → α) (M N : ℕ) (hMN : M ≤ N) :
    (∑ m ∈ Finset.Icc (-(N : ℤ)) N, f m) =
      (∑ m ∈ Finset.Icc (-(M : ℤ)) M, f m) +
        (∑ k ∈ Finset.range (N - M), f ((M + 1 + k : ℕ) : ℤ)) +
        (∑ k ∈ Finset.range (N - M), f (-(M + 1 + k : ℕ) : ℤ)) := by
  rw [sum_symmetricIcc_eq_sum_symmetricIcc_add_tails f M N hMN,
    sum_positive_Ico_eq_sum_range f M N hMN,
    sum_negative_Ico_eq_sum_range f M N hMN]

/-- The nonzero frequencies in a symmetric integer cutoff are exactly the
positive and negative natural range blocks used by the Fourier-series cutoff
decomposition. -/
theorem sum_symmetricIcc_sdiff_zero_eq_range_pos_neg
    {α : Type*} [AddCommGroup α] (f : ℤ → α) (H : ℕ) :
    (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0}, f h) =
      (∑ k ∈ Finset.range H, f ((k + 1 : ℕ) : ℤ)) +
        ∑ k ∈ Finset.range H, f (-((k + 1 : ℕ) : ℤ)) := by
  have hsub : ({0} : Finset ℤ) ⊆ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
    intro h hh
    simp only [Finset.mem_singleton] at hh
    subst h
    simp
  have hdiff :
      (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), f h) =
        (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0}, f h) + f 0 := by
    simpa using (Finset.sum_sdiff (f := f) hsub).symm
  have htotal := sum_symmetricIcc_eq_sum_symmetricIcc_add_range_tails
    f 0 H (Nat.zero_le H)
  have htotal' :
      (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), f h) =
        f 0 + (∑ k ∈ Finset.range H, f ((k + 1 : ℕ) : ℤ)) +
          ∑ k ∈ Finset.range H, f (-((k + 1 : ℕ) : ℤ)) := by
    simpa [add_comm] using htotal
  calc
    (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0}, f h) =
        (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), f h) - f 0 := by
          rw [hdiff]
          abel
    _ = ((∑ k ∈ Finset.range H, f ((k + 1 : ℕ) : ℤ)) +
          ∑ k ∈ Finset.range H, f (-((k + 1 : ℕ) : ℤ))) := by
          rw [htotal']
          abel

/-- The zero-frequency floor coefficient is bounded by one on the centered
frequency interval. -/
theorem floorFourierCoefficient_zero_norm_le_one {ξ : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2) :
    ‖floorFourierCoefficient 0 ξ‖ ≤ 1 := by
  by_cases hξ : ξ = 0
  · simp [floorFourierCoefficient, hξ]
  have hnum := norm_one_sub_unitFrequencyPhase_neg_le ξ
  have hden :
      ‖((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((0 : ℂ) + (ξ : ℂ))‖ = 2 * Real.pi * |ξ| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hdenpos : 0 < 2 * Real.pi * |ξ| := by positivity
  rw [floorFourierCoefficient, if_neg hξ, norm_div]
  simp only [Int.cast_zero, zero_add] at hden ⊢
  rw [hden]
  exact (div_le_one hdenpos).2 hnum

/-- Away from the zero frequency, the floor Fourier coefficient has the
harmonic majorant `1/|m|` on the blueprint's centered frequency interval. -/
theorem floorFourierCoefficient_norm_le_inv_abs
    {m : ℤ} (hm : m ≠ 0) {ξ : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2) :
    ‖floorFourierCoefficient m ξ‖ ≤ (|(m : ℝ)|)⁻¹ := by
  by_cases hξ : ξ = 0
  · simp [floorFourierCoefficient, hξ, hm]
  have hξabs : |ξ| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, le_of_lt hξhi⟩
  have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
    have hmInt : (1 : ℤ) ≤ |m| := by
      rcases lt_or_gt_of_ne hm with hneg | hpos
      · rw [abs_of_neg hneg]
        omega
      · rw [abs_of_pos hpos]
        omega
    exact_mod_cast hmInt
  have htriangle : |(m : ℝ)| ≤ |(m : ℝ) + ξ| + |ξ| := by
    calc
      |(m : ℝ)| = |((m : ℝ) + ξ) - ξ| := by congr 1 <;> ring
      _ ≤ |(m : ℝ) + ξ| + |ξ| := abs_sub _ _
  have hshift : |(m : ℝ)| / 2 ≤ |(m : ℝ) + ξ| := by
    nlinarith
  have hden : |(m : ℝ)| ≤ Real.pi * |(m : ℝ) + ξ| := by
    nlinarith [Real.pi_gt_three]
  have hnum : ‖1 - unitFrequencyPhase (-ξ)‖ ≤ 2 := by
    calc
      ‖1 - unitFrequencyPhase (-ξ)‖ ≤ ‖(1 : ℂ)‖ + ‖unitFrequencyPhase (-ξ)‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [norm_unitFrequencyPhase]; norm_num
  have hcomplexAdd : (m : ℂ) + (ξ : ℂ) = (((m : ℝ) + ξ : ℝ) : ℂ) := by
    rw [Complex.ofReal_add]
    rfl
  have hnormDen :
      ‖((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((m : ℂ) + (ξ : ℂ))‖ = 2 * Real.pi * |(m : ℝ) + ξ| := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (by positivity : 0 < 2 * Real.pi), Complex.norm_I, hcomplexAdd,
      Complex.norm_real, Real.norm_eq_abs]
    ring
  have hdenpos : 0 < 2 * Real.pi * |(m : ℝ) + ξ| := by
    have hmplus : 0 < |(m : ℝ) + ξ| := by
      have hpos : 0 < |(m : ℝ)| := lt_of_lt_of_le zero_lt_one hmabs
      nlinarith [hden]
    positivity
  have hmabspos : 0 < |(m : ℝ)| := lt_of_lt_of_le zero_lt_one hmabs
  rw [floorFourierCoefficient, if_neg hξ, norm_div, hnormDen]
  calc
    ‖1 - unitFrequencyPhase (-ξ)‖ /
        (2 * Real.pi * |(m : ℝ) + ξ|) ≤
        2 / (2 * Real.pi * |(m : ℝ) + ξ|) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
    _ ≤ (|(m : ℝ)|)⁻¹ := by
      rw [← one_div (|(m : ℝ)|)]
      apply (div_le_div_iff₀ hdenpos hmabspos).2
      nlinarith [hden]

/-- The symmetric finite coefficient sum has the logarithmic bound required
by the blueprint's floor-removal lemma. -/
theorem floorFourierCoefficient_sum_norm_le_log
    (M : ℕ) (hM : 2 ≤ M) {ξ : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2) :
    (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      ‖floorFourierCoefficient m ξ‖) ≤
      10 * Real.log (2 * (M : ℝ)) := by
  let negSet : Finset ℤ := Finset.Icc (-(M : ℤ)) (-1 : ℤ)
  let posSet : Finset ℤ := Finset.Icc (1 : ℤ) (M : ℤ)
  let coeff : ℤ → ℝ := fun m => ‖floorFourierCoefficient m ξ‖
  have hsplit : Finset.Icc (-(M : ℤ)) (M : ℤ) =
      insert 0 (negSet ∪ posSet) := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_union,
      negSet, posSet]
    omega
  have hzero : (0 : ℤ) ∉ negSet ∪ posSet := by
    simp [negSet, posSet, Finset.mem_union, Finset.mem_Icc]
  have hdisj : Disjoint negSet posSet := by
    apply Finset.disjoint_left.mpr
    intro z hzneg hzpos
    simp only [negSet, posSet, Finset.mem_Icc] at hzneg hzpos
    omega
  have hneg :
      (∑ z ∈ negSet, coeff z) =
        ∑ n ∈ Finset.Icc (1 : ℤ) (M : ℤ), coeff (-n) := by
    dsimp [negSet, coeff]
    refine Finset.sum_bij (fun z _ => -z) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_Icc] at hz ⊢
      omega
    · intro z₁ hz₁ z₂ hz₂ h
      exact neg_injective h
    · intro n hn
      refine ⟨-n, ?_, by simp⟩
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro z hz
      simp
  have hposMap :
      Finset.Icc (1 : ℤ) (M : ℤ) =
        (Finset.Icc 1 M).map Nat.castEmbedding := by
    calc
      Finset.Icc (1 : ℤ) (M : ℤ) = Finset.Ico 1 ((M : ℤ) + 1) := by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      _ = (Finset.Icc 1 M).map Nat.castEmbedding := by
        simpa [realIntegerInterval] using realIntegerInterval_zero_eq_nat_Icc M
  have hposNat :
      (∑ n ∈ Finset.Icc 1 M, coeff (n : ℤ)) ≤ (harmonic M : ℝ) := by
    have hle : ∀ n ∈ Finset.Icc 1 M,
        coeff (n : ℤ) ≤ ((n : ℝ)⁻¹) := by
      intro n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hcoef := floorFourierCoefficient_norm_le_inv_abs
        (m := (n : ℤ)) (by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)) hξlo hξhi
      simpa [coeff, abs_of_pos hnpos] using hcoef
    calc
      (∑ n ∈ Finset.Icc 1 M, coeff (n : ℤ)) ≤
          ∑ n ∈ Finset.Icc 1 M, ((n : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hle n hn
      _ = (harmonic M : ℝ) := by
        simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]
  have hnegNat :
      (∑ n ∈ Finset.Icc 1 M, coeff (-(n : ℤ))) ≤ (harmonic M : ℝ) := by
    have hle : ∀ n ∈ Finset.Icc 1 M,
        coeff (-(n : ℤ)) ≤ ((n : ℝ)⁻¹) := by
      intro n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hcoef := floorFourierCoefficient_norm_le_inv_abs
        (m := -(n : ℤ)) (by
          intro h
          have hnz : (n : ℤ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
          exact hnz (neg_eq_zero.mp h)) hξlo hξhi
      simpa [coeff, abs_neg, abs_of_pos hnpos] using hcoef
    calc
      (∑ n ∈ Finset.Icc 1 M, coeff (-(n : ℤ))) ≤
          ∑ n ∈ Finset.Icc 1 M, ((n : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hle n hn
      _ = (harmonic M : ℝ) := by
        simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]
  have hharm := harmonic_le_one_add_log M
  have hlog4 : (6 / 5 : ℝ) ≤ Real.log 4 := by
    convert Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) using 1 <;>
      norm_num
  have hlog : (6 / 5 : ℝ) ≤ Real.log (2 * (M : ℝ)) := by
    have hMreal : 2 ≤ (M : ℝ) := by exact_mod_cast hM
    exact hlog4.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hlogM : Real.log (M : ℝ) ≤ Real.log (2 * (M : ℝ)) := by
    apply Real.log_le_log (by positivity)
    nlinarith [show 0 ≤ (M : ℝ) by positivity]
  have hsumBound :
      (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), coeff m) ≤
        1 + 2 * (harmonic M : ℝ) := by
    rw [hsplit, Finset.sum_insert hzero, Finset.sum_union hdisj]
    dsimp [coeff] at hneg hposNat hnegNat ⊢
    have hposNat' :
        (∑ n ∈ Finset.Icc 1 M,
          ‖floorFourierCoefficient (n : ℤ) ξ‖) ≤ (harmonic M : ℝ) := hposNat
    have hnegNat' :
        (∑ n ∈ Finset.Icc 1 M,
          ‖floorFourierCoefficient (-(n : ℤ)) ξ‖) ≤ (harmonic M : ℝ) := hnegNat
    have hposInt :
        (∑ z ∈ posSet, ‖floorFourierCoefficient z ξ‖) =
          ∑ n ∈ Finset.Icc 1 M, ‖floorFourierCoefficient (n : ℤ) ξ‖ := by
      change (∑ z ∈ Finset.Icc (1 : ℤ) (M : ℤ),
        ‖floorFourierCoefficient z ξ‖) = _
      rw [hposMap, Finset.sum_map]
      rfl
    have hnegInt :
        (∑ n ∈ Finset.Icc (1 : ℤ) (M : ℤ),
          ‖floorFourierCoefficient (-n) ξ‖) =
          ∑ n ∈ Finset.Icc 1 M,
            ‖floorFourierCoefficient (-(n : ℤ)) ξ‖ := by
      rw [hposMap, Finset.sum_map]
      rfl
    rw [hneg, hnegInt, hposInt]
    have hzeroBound : ‖floorFourierCoefficient 0 ξ‖ ≤ 1 :=
      floorFourierCoefficient_zero_norm_le_one hξlo hξhi
    nlinarith [hposNat', hnegNat']
  calc
    (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ‖floorFourierCoefficient m ξ‖) ≤ 1 + 2 * (harmonic M : ℝ) := by
      simpa [coeff] using hsumBound
    _ ≤ 3 + 2 * Real.log (M : ℝ) := by linarith [hharm]
    _ ≤ 3 + 2 * Real.log (2 * (M : ℝ)) := by linarith
    _ ≤ 10 * Real.log (2 * (M : ℝ)) := by nlinarith [hlog]

/-- Each positive-frequency term factors into the common floor coefficient,
the reciprocal phase weight, and a shifted unit phase. -/
theorem floorFourierCoefficient_nat_mul_phase_eq
    {m : ℕ} (hm : 0 < m) {ξ t : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) :
    floorFourierCoefficient (m : ℤ) ξ *
        unitFrequencyPhase (((m : ℝ) + ξ) * t) =
      ((1 - unitFrequencyPhase (-ξ)) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
          ((((m : ℝ) + ξ : ℝ) : ℂ)⁻¹)) *
        (unitFrequencyPhase (ξ * t) * unitFrequencyPhase t ^ m) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [floorFourierCoefficient, hm.ne', unitFrequencyPhase]
  have hmreal : 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hdpos : 0 < (m : ℝ) + ξ := by nlinarith [hξlo]
  have hdenCast : (m : ℂ) + (ξ : ℂ) = (((m : ℝ) + ξ : ℝ) : ℂ) := by
    rw [Complex.ofReal_add]
    rfl
  have hdenNe : (((m : ℝ) + ξ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hdpos)
  have hscaleNe : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
  have hcoef :
      (1 - unitFrequencyPhase (-ξ)) /
          ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
            ((m : ℂ) + (ξ : ℂ))) =
        ((1 - unitFrequencyPhase (-ξ)) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) *
          ((((m : ℝ) + ξ : ℝ) : ℂ)⁻¹) := by
    rw [hdenCast]
    field_simp [hscaleNe, hdenNe]
  have harg : ((m : ℝ) + ξ) * t = (m : ℝ) * t + ξ * t := by ring
  have hmcast : ((m : ℤ) : ℂ) = (m : ℂ) := by norm_cast
  simp only [floorFourierCoefficient, if_neg hξ]
  rw [harg, unitFrequencyPhase_add, unitFrequencyPhase_nat_mul,
    hmcast, hcoef]
  ring_nf

/-- The negative-frequency coefficient term has the reflected reciprocal
factor and the phase at `-t`. -/
theorem floorFourierCoefficient_neg_nat_mul_phase_eq
    {m : ℕ} (hm : 0 < m) {ξ t : ℝ} (hξhi : ξ < 1 / 2) :
    floorFourierCoefficient (-(m : ℤ)) ξ *
        unitFrequencyPhase ((-(m : ℝ) + ξ) * t) =
      (((-(1 - unitFrequencyPhase (-ξ))) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) *
          ((((m : ℝ) - ξ : ℝ) : ℂ)⁻¹)) *
        (unitFrequencyPhase (ξ * t) * unitFrequencyPhase (-t) ^ m) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [floorFourierCoefficient, hm.ne', unitFrequencyPhase]
  have hmreal : 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hdpos : 0 < (m : ℝ) - ξ := by nlinarith
  have hdenCast : -(m : ℂ) + (ξ : ℂ) =
      -((((m : ℝ) - ξ : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sub]
    push_cast
    ring
  have hdenNe : ((((m : ℝ) - ξ : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hdpos)
  have hscaleNe : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
  have hcoef :
      (1 - unitFrequencyPhase (-ξ)) /
          ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
            (-(m : ℂ) + (ξ : ℂ))) =
        ((-(1 - unitFrequencyPhase (-ξ))) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) *
          ((((m : ℝ) - ξ : ℝ) : ℂ)⁻¹) := by
    rw [hdenCast]
    field_simp [hscaleNe, hdenNe]
  have harg : (-(m : ℝ) + ξ) * t = (m : ℝ) * (-t) + ξ * t := by ring
  simp only [floorFourierCoefficient, if_neg hξ]
  push_cast
  push_cast at hcoef
  rw [harg, unitFrequencyPhase_add, unitFrequencyPhase_nat_mul, hcoef]
  ring_nf

/-- The exact finite negative-frequency coefficient tail factors into the
reflected reciprocal phase sum. -/
theorem sum_floorFourierCoefficient_negative_tail_eq
    (M L : ℕ) {ξ t : ℝ} (hξhi : ξ < 1 / 2) :
    (∑ k ∈ Finset.range L,
      floorFourierCoefficient (-(M + 1 + k : ℕ) : ℤ) ξ *
        unitFrequencyPhase ((-(M + 1 + k : ℕ) + ξ) * t)) =
      ((-(1 - unitFrequencyPhase (-ξ)) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
          unitFrequencyPhase (ξ * t) * unitFrequencyPhase (-t) ^ (M + 1)) *
        ∑ k ∈ Finset.range L,
          ((((M : ℝ) + 1 + (k : ℝ) - ξ)⁻¹ : ℝ) : ℂ) *
            unitFrequencyPhase (-t) ^ k) := by
  let C : ℂ :=
    (-(1 - unitFrequencyPhase (-ξ)) /
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) *
      unitFrequencyPhase (ξ * t) * unitFrequencyPhase (-t) ^ (M + 1)
  calc
    (∑ k ∈ Finset.range L,
        floorFourierCoefficient (-(M + 1 + k : ℕ) : ℤ) ξ *
          unitFrequencyPhase ((-(M + 1 + k : ℕ) + ξ) * t)) =
      ∑ k ∈ Finset.range L,
        C * (((((M : ℝ) + 1 + (k : ℝ) - ξ)⁻¹ : ℝ) : ℂ) *
          unitFrequencyPhase (-t) ^ k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hm : 0 < M + 1 + k := by omega
            have hterm := floorFourierCoefficient_neg_nat_mul_phase_eq
              (m := M + 1 + k) (ξ := ξ) (t := t) hm hξhi
            have hfreq : (-(M + 1 + k : ℕ) : ℤ) =
                -((M : ℤ) + 1 + (k : ℤ)) := by push_cast; omega
            have hden : ((M + 1 + k : ℕ) : ℝ) - ξ =
                (M : ℝ) + 1 + (k : ℝ) - ξ := by push_cast; ring
            dsimp [C]
            rw [← hfreq, hterm, ← Complex.ofReal_inv, hden, pow_add]
            ring
    _ = C * ∑ k ∈ Finset.range L,
          ((((M : ℝ) + 1 + (k : ℝ) - ξ)⁻¹ : ℝ) : ℂ) *
            unitFrequencyPhase (-t) ^ k := by
              rw [Finset.mul_sum]
  all_goals rfl

/-- The exact finite positive-frequency coefficient tail factors into the
common floor coefficient and the reciprocal phase sum. -/
theorem sum_floorFourierCoefficient_positive_tail_eq
    (M L : ℕ) {ξ t : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) :
    (∑ k ∈ Finset.range L,
      floorFourierCoefficient ((M + 1 + k : ℕ) : ℤ) ξ *
        unitFrequencyPhase ((((M + 1 + k : ℕ) : ℝ) + ξ) * t)) =
      ((1 - unitFrequencyPhase (-ξ)) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
          unitFrequencyPhase (ξ * t) * unitFrequencyPhase t ^ (M + 1)) *
        ∑ k ∈ Finset.range L,
          ((((M : ℝ) + 1 + (k : ℝ) + ξ)⁻¹ : ℝ) : ℂ) *
            unitFrequencyPhase t ^ k := by
  let C : ℂ :=
    ((1 - unitFrequencyPhase (-ξ)) /
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) *
      unitFrequencyPhase (ξ * t) * unitFrequencyPhase t ^ (M + 1)
  calc
    (∑ k ∈ Finset.range L,
        floorFourierCoefficient ((M + 1 + k : ℕ) : ℤ) ξ *
          unitFrequencyPhase ((((M + 1 + k : ℕ) : ℝ) + ξ) * t)) =
      ∑ k ∈ Finset.range L,
        C * (((((M : ℝ) + 1 + (k : ℝ) + ξ)⁻¹ : ℝ) : ℂ) *
          unitFrequencyPhase t ^ k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hm : 0 < M + 1 + k := by omega
            have hterm := floorFourierCoefficient_nat_mul_phase_eq
              (m := M + 1 + k) (ξ := ξ) (t := t) hm hξlo
            have hfreq : ((M + 1 + k : ℕ) : ℤ) =
                (M : ℤ) + 1 + (k : ℤ) := by push_cast; omega
            have hindex : (((M + 1 + k : ℕ) : ℝ) + ξ) =
                (M : ℝ) + 1 + (k : ℝ) + ξ := by push_cast; ring
            dsimp [C]
            rw [← hfreq, hterm, hindex, ← Complex.ofReal_inv, pow_add]
            ring
    _ = C * ∑ k ∈ Finset.range L,
          ((((M : ℝ) + 1 + (k : ℝ) + ξ)⁻¹ : ℝ) : ℂ) *
            unitFrequencyPhase t ^ k := by
              rw [Finset.mul_sum]
  all_goals rfl

/-- The common factor in the positive-frequency tail has norm at most one
half on the blueprint's centered frequency interval. -/
theorem floorFourier_positive_common_factor_norm_le_half
    {ξ t : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (M : ℕ) :
    ‖((1 - unitFrequencyPhase (-ξ)) /
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        unitFrequencyPhase (ξ * t) * unitFrequencyPhase t ^ (M + 1))‖ ≤
      1 / 2 := by
  have hξabs : |ξ| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, le_of_lt hξhi⟩
  have hnum := norm_one_sub_unitFrequencyPhase_neg_le ξ
  have hden :
      ‖((2 * Real.pi : ℝ) : ℂ) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    ring
  have hquot :
      ‖(1 - unitFrequencyPhase (-ξ)) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I)‖ ≤ |ξ| := by
    rw [norm_div, hden]
    calc
      ‖1 - unitFrequencyPhase (-ξ)‖ / (2 * Real.pi) ≤
          (2 * Real.pi * |ξ|) / (2 * Real.pi) :=
            div_le_div_of_nonneg_right hnum (by positivity)
      _ = |ξ| := by field_simp
  calc
    ‖((1 - unitFrequencyPhase (-ξ)) /
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        unitFrequencyPhase (ξ * t) * unitFrequencyPhase t ^ (M + 1))‖ =
      ‖(1 - unitFrequencyPhase (-ξ)) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I)‖ := by
            rw [norm_mul, norm_mul]
            simp only [norm_unitFrequencyPhase, norm_pow, one_pow]
            ring
    _ ≤ |ξ| := hquot
    _ ≤ 1 / 2 := hξabs

/-- The reflected common factor for a negative-frequency tail has the same
centered-frequency norm bound. -/
theorem floorFourier_negative_common_factor_norm_le_half
    {ξ t : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (M : ℕ) :
    ‖(-(1 - unitFrequencyPhase (-ξ)) /
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        unitFrequencyPhase (ξ * t) * unitFrequencyPhase (-t) ^ (M + 1))‖ ≤
      1 / 2 := by
  have hξabs : |ξ| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, le_of_lt hξhi⟩
  have hnum := norm_one_sub_unitFrequencyPhase_neg_le ξ
  have hden :
      ‖((2 * Real.pi : ℝ) : ℂ) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    ring
  have hquot :
      ‖(-(1 - unitFrequencyPhase (-ξ)) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I))‖ ≤ |ξ| := by
    rw [norm_div, norm_neg, hden]
    calc
      ‖1 - unitFrequencyPhase (-ξ)‖ / (2 * Real.pi) ≤
          (2 * Real.pi * |ξ|) / (2 * Real.pi) :=
            div_le_div_of_nonneg_right hnum (by positivity)
      _ = |ξ| := by field_simp
  calc
    ‖(-(1 - unitFrequencyPhase (-ξ)) /
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        unitFrequencyPhase (ξ * t) * unitFrequencyPhase (-t) ^ (M + 1))‖ =
      ‖-(1 - unitFrequencyPhase (-ξ)) /
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I)‖ := by
            rw [norm_mul, norm_mul]
            simp only [norm_unitFrequencyPhase, norm_pow, one_pow]
            ring
    _ ≤ |ξ| := hquot
    _ ≤ 1 / 2 := hξabs

/-- A finite geometric sum of unit-modulus complex numbers has the standard
denominator bound. This is the oscillatory-sum input for the floor-removal
Fourier tails. -/
theorem norm_sum_range_unit_phase_pow_le {z : ℂ} (hz : z ≠ 1)
    (hznorm : ‖z‖ = 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, z ^ k‖ ≤ 2 / ‖1 - z‖ := by
  have hznorm' (k : ℕ) : ‖z ^ k‖ = 1 := by rw [norm_pow, hznorm]; simp
  have hnum : ‖z ^ n - 1‖ ≤ 2 := by
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hznorm' n]; norm_num
  have hden : ‖z - 1‖ = ‖1 - z‖ := by
    rw [← norm_neg]
    congr 1
    ring
  rw [geom_sum_eq hz n, norm_div]
  calc
    ‖z ^ n - 1‖ / ‖z - 1‖ = ‖z ^ n - 1‖ / ‖1 - z‖ := by rw [hden]
    _ ≤ 2 / ‖1 - z‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)

/-- Finite Abel summation: an antitone nonnegative scalar weight turns a
uniform bound on all partial sums into a weighted-sum bound. -/
theorem norm_sum_range_smul_antitone_le
    (w : ℕ → ℝ) (z : ℕ → ℂ) (B : ℝ) (n : ℕ)
    (hB : 0 ≤ B) (hw0 : 0 ≤ w 0) (hwpos : ∀ i < n, 0 ≤ w i)
    (hwanti : AntitoneOn w (Set.Iio n))
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, z i‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, w i • z i‖ ≤ B * w 0 := by
  cases n with
  | zero => simpa using mul_nonneg hB hw0
  | succ n =>
    have hwN : 0 ≤ w n := hwpos n (by omega)
    have hpartialN := hpartial (n + 1) (by omega)
    have htel :
        (∑ i ∈ Finset.range n, (w i - w (i + 1))) = w 0 - w n := by
      calc
        (∑ i ∈ Finset.range n, (w i - w (i + 1))) =
            -∑ i ∈ Finset.range n, (w (i + 1) - w i) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = -(w n - w 0) := by rw [Finset.sum_range_sub]
        _ = w 0 - w n := by ring
    rw [Finset.sum_range_by_parts w z (n + 1)]
    simp only [Nat.add_sub_cancel]
    calc
      ‖w n • (∑ i ∈ Finset.range (n + 1), z i) -
          ∑ i ∈ Finset.range n,
            (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), z j)‖
        ≤ ‖w n • (∑ i ∈ Finset.range (n + 1), z i)‖ +
          ‖∑ i ∈ Finset.range n,
            (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), z j)‖ := norm_sub_le _ _
      _ ≤ w n * B +
          ∑ i ∈ Finset.range n, (w i - w (i + 1)) * B := by
        apply add_le_add
        · calc
            ‖w n • (∑ i ∈ Finset.range (n + 1), z i)‖ =
                |w n| * ‖∑ i ∈ Finset.range (n + 1), z i‖ := by
                  simp only [norm_smul, Real.norm_eq_abs]
            _ = w n * ‖∑ i ∈ Finset.range (n + 1), z i‖ := by rw [abs_of_nonneg hwN]
            _ ≤ w n * B := mul_le_mul_of_nonneg_left hpartialN hwN
        · calc
            ‖∑ i ∈ Finset.range n,
                (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), z j)‖ ≤
                ∑ i ∈ Finset.range n,
                  ‖(w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), z j)‖ :=
                    norm_sum_le _ _
            _ ≤ ∑ i ∈ Finset.range n, (w i - w (i + 1)) * B := by
              apply Finset.sum_le_sum
              intro i hi
              have hiN : i < n := Finset.mem_range.mp hi
              have hdecr : w (i + 1) ≤ w i :=
                hwanti (by simp [Set.mem_Iio]; omega)
                  (by simp [Set.mem_Iio]; omega) (by omega)
              have hpartialI := hpartial (i + 1) (by omega)
              calc
                ‖(w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), z j)‖ =
                    (w i - w (i + 1)) *
                      ‖∑ j ∈ Finset.range (i + 1), z j‖ := by
                    rw [norm_smul, Real.norm_eq_abs,
                      abs_of_nonpos (sub_nonpos.mpr hdecr)]
                    ring
                _ ≤ (w i - w (i + 1)) * B :=
                    mul_le_mul_of_nonneg_left hpartialI (sub_nonneg.mpr hdecr)
      _ = B * w 0 := by rw [← Finset.sum_mul, htel]; ring

/-- The positive reciprocal-frequency tail has the expected Abel bound on a
centered nonintegral phase. -/
theorem norm_sum_range_positive_reciprocal_phase_le
    (M L : ℕ) (hM : 2 ≤ M) {ξ t : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ)
    (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    ‖∑ k ∈ Finset.range L,
        ((M : ℝ) + 1 + (k : ℝ) + ξ)⁻¹ • unitFrequencyPhase t ^ k‖ ≤
      (2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ)) := by
  let w : ℕ → ℝ := fun k => ((M : ℝ) + 1 + (k : ℝ) + ξ)⁻¹
  have hMreal : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : 0 < (M : ℝ) := by linarith
  have hden (k : ℕ) : 0 < (M : ℝ) + 1 + (k : ℝ) + ξ := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hξlo]
  have hdist : 0 < realDistanceToIntegers t := by
    rw [realDistanceToIntegers_eq_abs_of_abs_le_half ht]
    exact abs_pos.mpr ht0
  have hchord := four_mul_realDistanceToIntegers_le_norm_one_sub_unitFrequencyPhase ht
  have hchordpos : 0 < ‖1 - unitFrequencyPhase t‖ := by
    exact lt_of_lt_of_le (by positivity : 0 < 4 * realDistanceToIntegers t) hchord
  have hphaseNe : unitFrequencyPhase t ≠ 1 := by
    intro hz
    rw [hz] at hchord
    norm_num at hchord
    nlinarith [hdist]
  have hw0 : 0 ≤ w 0 := by
    dsimp [w]
    exact inv_nonneg.mpr (le_of_lt (hden 0))
  have hwpos : ∀ k < L, 0 ≤ w k := by
    intro k hk
    dsimp [w]
    exact inv_nonneg.mpr (le_of_lt (hden k))
  have hwanti : AntitoneOn w (Set.Iio L) := by
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    dsimp [w]
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    rw [← one_div, ← one_div]
    apply (div_le_div_iff₀ (hden j) (hden i)).2
    nlinarith
  have hpartial : ∀ k ≤ L,
      ‖∑ i ∈ Finset.range k, unitFrequencyPhase t ^ i‖ ≤
        2 / ‖1 - unitFrequencyPhase t‖ := by
    intro k hk
    exact norm_sum_range_unit_phase_pow_le hphaseNe
      (norm_unitFrequencyPhase t) k
  have habel := norm_sum_range_smul_antitone_le w
    (fun k => unitFrequencyPhase t ^ k) (2 / ‖1 - unitFrequencyPhase t‖) L
    (by positivity) hw0 hwpos hwanti hpartial
  have hw0le : w 0 ≤ 1 / (M : ℝ) := by
    dsimp [w]
    rw [← one_div]
    apply (div_le_div_iff₀ (hden 0) hMpos).2
    norm_num
    linarith [hξlo]
  calc
    ‖∑ k ∈ Finset.range L,
        ((M : ℝ) + 1 + (k : ℝ) + ξ)⁻¹ • unitFrequencyPhase t ^ k‖ ≤
        (2 / ‖1 - unitFrequencyPhase t‖) * w 0 := by
          simpa [w] using habel
    _ ≤ (2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hw0le (by positivity)

/-- The finite positive coefficient tail is controlled by the common
coefficient factor and the reciprocal-phase estimate. -/
theorem norm_sum_floorFourierCoefficient_positive_tail_le
    (M L : ℕ) (hM : 2 ≤ M) {ξ t : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    ‖∑ k ∈ Finset.range L,
      floorFourierCoefficient ((M + 1 + k : ℕ) : ℤ) ξ *
        unitFrequencyPhase ((((M + 1 + k : ℕ) : ℝ) + ξ) * t)‖ ≤
      (1 / 2) * ((2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ))) := by
  have hfactor := sum_floorFourierCoefficient_positive_tail_eq
    M L (ξ := ξ) (t := t) hξlo
  have hcommon := floorFourier_positive_common_factor_norm_le_half
    (ξ := ξ) (t := t) hξlo hξhi M
  have hrecip := norm_sum_range_positive_reciprocal_phase_le M L hM
    hξlo ht ht0
  have hrecip' :
      ‖∑ k ∈ Finset.range L,
        ((((M : ℝ) + 1 + (k : ℝ) + ξ)⁻¹ : ℝ) : ℂ) *
          unitFrequencyPhase t ^ k‖ ≤
        (2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ)) := by
    simpa only [Complex.real_smul] using hrecip
  rw [hfactor]
  calc
    ‖((1 - unitFrequencyPhase (-ξ)) /
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        unitFrequencyPhase (ξ * t) * unitFrequencyPhase t ^ (M + 1)) *
        ∑ k ∈ Finset.range L,
          ((((M : ℝ) + 1 + (k : ℝ) + ξ)⁻¹ : ℝ) : ℂ) *
            unitFrequencyPhase t ^ k‖ =
      ‖((1 - unitFrequencyPhase (-ξ)) /
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        unitFrequencyPhase (ξ * t) * unitFrequencyPhase t ^ (M + 1))‖ *
        ‖∑ k ∈ Finset.range L,
          ((((M : ℝ) + 1 + (k : ℝ) + ξ)⁻¹ : ℝ) : ℂ) *
            unitFrequencyPhase t ^ k‖ := norm_mul _ _
    _ ≤ (1 / 2) * ((2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ))) :=
      mul_le_mul hcommon hrecip' (norm_nonneg _) (by norm_num)

/-- Every finite negative-frequency coefficient tail satisfies the reflected
Abel bound with the paper's same one-half coefficient factor. -/
theorem norm_sum_floorFourierCoefficient_negative_tail_le
    (M L : ℕ) (hM : 2 ≤ M) {ξ t : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    ‖∑ k ∈ Finset.range L,
      floorFourierCoefficient (-(M + 1 + k : ℕ) : ℤ) ξ *
        unitFrequencyPhase ((-(M + 1 + k : ℕ) + ξ) * t)‖ ≤
      (1 / 2) * ((2 / ‖1 - unitFrequencyPhase (-t)‖) * (1 / (M : ℝ))) := by
  have hfactor := sum_floorFourierCoefficient_negative_tail_eq
    M L (ξ := ξ) (t := t) hξhi
  have hcommon := floorFourier_negative_common_factor_norm_le_half
    (ξ := ξ) (t := t) hξlo hξhi M
  have hξlo' : -(1 / 2 : ℝ) ≤ -ξ := by linarith
  have ht' : abs (-t) ≤ 1 / 2 := by rw [abs_neg]; exact ht
  have ht0' : -t ≠ 0 := neg_ne_zero.mpr ht0
  have hrecip := norm_sum_range_positive_reciprocal_phase_le M L hM
    (ξ := -ξ) (t := -t) hξlo' ht' ht0'
  have hrecip' :
      ‖∑ k ∈ Finset.range L,
        ((((M : ℝ) + 1 + (k : ℝ) - ξ)⁻¹ : ℝ) : ℂ) *
          unitFrequencyPhase (-t) ^ k‖ ≤
        (2 / ‖1 - unitFrequencyPhase (-t)‖) * (1 / (M : ℝ)) := by
    simpa only [Complex.real_smul, sub_eq_add_neg] using hrecip
  rw [hfactor]
  calc
    ‖(-(1 - unitFrequencyPhase (-ξ)) /
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        unitFrequencyPhase (ξ * t) * unitFrequencyPhase (-t) ^ (M + 1)) *
        ∑ k ∈ Finset.range L,
          ((((M : ℝ) + 1 + (k : ℝ) - ξ)⁻¹ : ℝ) : ℂ) *
            unitFrequencyPhase (-t) ^ k‖ =
      ‖-(1 - unitFrequencyPhase (-ξ)) /
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        unitFrequencyPhase (ξ * t) * unitFrequencyPhase (-t) ^ (M + 1)‖ *
        ‖∑ k ∈ Finset.range L,
          ((((M : ℝ) + 1 + (k : ℝ) - ξ)⁻¹ : ℝ) : ℂ) *
            unitFrequencyPhase (-t) ^ k‖ := norm_mul _ _
    _ ≤ (1 / 2) * ((2 / ‖1 - unitFrequencyPhase (-t)‖) * (1 / (M : ℝ))) :=
      mul_le_mul hcommon hrecip' (norm_nonneg _) (by norm_num)

/-- The symmetric Fourier coefficient tail is Cauchy away from integer
phases. The two exact frequency tails have equal chord denominators. -/
theorem norm_symmetric_floorFourierCoefficient_tail_le
    (M N : ℕ) (hM : 2 ≤ M) (hMN : M ≤ N) {ξ t : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    ‖(∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        floorFourierCoefficient m ξ *
          unitFrequencyPhase (((m : ℝ) + ξ) * t)) -
      (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        floorFourierCoefficient m ξ *
          unitFrequencyPhase (((m : ℝ) + ξ) * t))‖ ≤
      (2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ)) := by
  let f : ℤ → ℂ := fun m =>
    floorFourierCoefficient m ξ * unitFrequencyPhase (((m : ℝ) + ξ) * t)
  have hdecomp := sum_symmetricIcc_eq_sum_symmetricIcc_add_range_tails
    f M N hMN
  have hdiff :
      (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f m) -
        (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f m) =
        (∑ k ∈ Finset.range (N - M), f ((M + 1 + k : ℕ) : ℤ)) +
          (∑ k ∈ Finset.range (N - M), f (-(M + 1 + k : ℕ) : ℤ)) := by
    rw [hdecomp]
    abel
  have hpos := norm_sum_floorFourierCoefficient_positive_tail_le
    M (N - M) hM hξlo hξhi ht ht0
  have hneg := norm_sum_floorFourierCoefficient_negative_tail_le
    M (N - M) hM hξlo hξhi ht ht0
  rw [norm_one_sub_unitFrequencyPhase_neg_eq t] at hneg
  let A : ℝ := (2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ))
  have hpos' :
      ‖∑ k ∈ Finset.range (N - M),
        f ((M + 1 + k : ℕ) : ℤ)‖ ≤ (1 / 2) * A := by
    simpa [A, f, mul_assoc, Int.cast_natCast, Nat.cast_add, Nat.cast_one] using hpos
  have hneg' :
      ‖∑ k ∈ Finset.range (N - M),
        f (-(M + 1 + k : ℕ) : ℤ)‖ ≤ (1 / 2) * A := by
    simpa [A, f, mul_assoc, Int.cast_neg, Int.cast_natCast,
      Nat.cast_add, Nat.cast_one] using hneg
  calc
    _ = ‖(∑ k ∈ Finset.range (N - M), f ((M + 1 + k : ℕ) : ℤ)) +
          (∑ k ∈ Finset.range (N - M), f (-(M + 1 + k : ℕ) : ℤ))‖ :=
      congrArg norm hdiff
    _ ≤
        ‖∑ k ∈ Finset.range (N - M),
          f ((M + 1 + k : ℕ) : ℤ)‖ +
        ‖∑ k ∈ Finset.range (N - M),
          f (-(M + 1 + k : ℕ) : ℤ)‖ := norm_add_le _ _
    _ ≤ (1 / 2) * A + (1 / 2) * A := add_le_add hpos' hneg'
    _ = A := by ring
    _ = (2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ)) := rfl

/-- The symmetric shifted Fourier partial sums for the floor coefficients. -/
noncomputable def floorFourierShiftedPartialSum (ξ t : ℝ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    floorFourierCoefficient m ξ *
      unitFrequencyPhase (((m : ℝ) + ξ) * t)

/-- Translating the input by an integer multiplies every shifted Fourier
partial sum by the common fractional-frequency phase. -/
theorem floorFourierShiftedPartialSum_add_int (ξ t : ℝ) (N : ℕ) (k : ℤ) :
    floorFourierShiftedPartialSum ξ (t + (k : ℝ)) N =
      unitFrequencyPhase (ξ * (k : ℝ)) * floorFourierShiftedPartialSum ξ t N := by
  classical
  unfold floorFourierShiftedPartialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have harg : ((m : ℝ) + ξ) * (t + (k : ℝ)) =
      (((m : ℝ) + ξ) * t) + ((m : ℝ) * (k : ℝ)) + ξ * (k : ℝ) := by ring
  rw [harg, unitFrequencyPhase_add, unitFrequencyPhase_add]
  have hmk : (m : ℝ) * (k : ℝ) = ((m * k : ℤ) : ℝ) := by push_cast; ring
  rw [hmk, unitFrequencyPhase_int]
  ring

noncomputable def floorFourierCirclePointwisePartialSum
    (ξ : ℝ) (x : AddCircle (1 : ℝ)) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    fourierCoeff (floorFourierCircleFunction ξ) m * fourier m x

theorem floorFourierShiftedPartialSum_eq_phase_mul_circle_fourier_sum
    {ξ t : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (N : ℕ) :
    floorFourierShiftedPartialSum ξ t N =
      unitFrequencyPhase (ξ * t) *
        (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          fourierCoeff (floorFourierCircleFunction ξ) m *
            fourier m (t : AddCircle (1 : ℝ))) := by
  rw [floorFourierShiftedPartialSum]
  have hchar (m : ℤ) :
      fourier m (t : AddCircle (1 : ℝ)) =
        unitFrequencyPhase ((m : ℝ) * t) := by
    rw [fourier_coe_apply]
    unfold unitFrequencyPhase
    congr 1
    push_cast
    ring
  calc
    (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        floorFourierCoefficient m ξ *
          unitFrequencyPhase (((m : ℝ) + ξ) * t)) =
      ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        unitFrequencyPhase (ξ * t) *
          (floorFourierCoefficient m ξ * fourier m (t : AddCircle (1 : ℝ))) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [hchar m]
            have hphase :
                unitFrequencyPhase (((m : ℝ) + ξ) * t) =
                  unitFrequencyPhase (ξ * t) * unitFrequencyPhase ((m : ℝ) * t) := by
              calc
                unitFrequencyPhase (((m : ℝ) + ξ) * t) =
                    unitFrequencyPhase ((m : ℝ) * t + ξ * t) := by congr 1 <;> ring
                _ = unitFrequencyPhase ((m : ℝ) * t) * unitFrequencyPhase (ξ * t) :=
                  unitFrequencyPhase_add _ _
                _ = unitFrequencyPhase (ξ * t) * unitFrequencyPhase ((m : ℝ) * t) :=
                  mul_comm _ _
            rw [hphase]
            ring
    _ = unitFrequencyPhase (ξ * t) *
        (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          floorFourierCoefficient m ξ * fourier m (t : AddCircle (1 : ℝ))) := by
            rw [Finset.mul_sum]
    _ = unitFrequencyPhase (ξ * t) *
        (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          fourierCoeff (floorFourierCircleFunction ξ) m *
            fourier m (t : AddCircle (1 : ℝ))) := by
            apply congrArg (fun z : ℂ => unitFrequencyPhase (ξ * t) * z)
            apply Finset.sum_congr rfl
            intro m hm
            rw [floorFourierCircleFunction_fourierCoeff hξlo hξhi]

theorem floorFourierShiftedPartialSum_cauchy {ξ t : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    CauchySeq (floorFourierShiftedPartialSum ξ t) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hden := norm_one_sub_unitFrequencyPhase_pos_of_centered_ne_zero ht ht0
  let C : ℝ := 2 / ‖1 - unitFrequencyPhase t‖
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos (by norm_num) hden
  obtain ⟨K, hK⟩ := exists_nat_gt (C / ε)
  refine ⟨max K 2, ?_⟩
  intro m hm n hn
  have hm2 : 2 ≤ m := le_trans (le_max_right K 2) hm
  have hn2 : 2 ≤ n := le_trans (le_max_right K 2) hn
  have hKm : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans (le_max_left K 2) hm
  have hKn : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left K 2) hn
  have hεmul : C < ε * (K : ℝ) := by
    have hK' : C / ε < (K : ℝ) := by exact_mod_cast hK
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hK'
  have hCm : C < ε * (m : ℝ) := lt_of_lt_of_le hεmul
    (mul_le_mul_of_nonneg_left hKm hε.le)
  have hCn : C < ε * (n : ℝ) := lt_of_lt_of_le hεmul
    (mul_le_mul_of_nonneg_left hKn hε.le)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hm)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hdecay_m : C * (1 / (m : ℝ)) < ε := by
    rw [mul_one_div]
    exact (div_lt_iff₀ hmpos).2 hCm
  have hdecay_n : C * (1 / (n : ℝ)) < ε := by
    rw [mul_one_div]
    exact (div_lt_iff₀ hnpos).2 hCn
  by_cases hmn : m ≤ n
  · have htail := norm_symmetric_floorFourierCoefficient_tail_le
      m n hm2 hmn hξlo hξhi ht ht0
    calc
      dist (floorFourierShiftedPartialSum ξ t m)
          (floorFourierShiftedPartialSum ξ t n) =
          ‖floorFourierShiftedPartialSum ξ t n -
            floorFourierShiftedPartialSum ξ t m‖ := by
              rw [dist_comm, dist_eq_norm]
      _ ≤ C * (1 / (m : ℝ)) := by
            simpa [C, floorFourierShiftedPartialSum] using htail
      _ < ε := hdecay_m
  · have hnm : n ≤ m := le_of_not_ge hmn
    have htail := norm_symmetric_floorFourierCoefficient_tail_le
      n m hn2 hnm hξlo hξhi ht ht0
    calc
      dist (floorFourierShiftedPartialSum ξ t m)
          (floorFourierShiftedPartialSum ξ t n) =
          ‖floorFourierShiftedPartialSum ξ t m -
            floorFourierShiftedPartialSum ξ t n‖ := dist_eq_norm _ _
      _ ≤ C * (1 / (n : ℝ)) := by
            simpa [C, floorFourierShiftedPartialSum] using htail
      _ < ε := hdecay_n

theorem floorFourierCirclePointwisePartialSum_cauchy_of_ne_zero
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    {x : AddCircle (1 : ℝ)} (hx0 : x ≠ 0) :
    CauchySeq (fun N => floorFourierCirclePointwisePartialSum ξ x N) := by
  let t : ℝ := (AddCircle.equivIoc (1 : ℝ) (-1 / 2) x).val
  have htmem := (AddCircle.equivIoc (1 : ℝ) (-1 / 2) x).property
  change t ∈ Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) at htmem
  simp only [Set.mem_Ioc] at htmem
  have ht : |t| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by nlinarith⟩
  have hclass : (t : AddCircle (1 : ℝ)) = x := by
    dsimp [t]
    simp
  have ht0 : t ≠ 0 := by
    intro htzero
    apply hx0
    rw [← hclass, htzero]
    simp
  have hshift := floorFourierShiftedPartialSum_cauchy hξlo hξhi ht ht0
  have hqnorm : ‖unitFrequencyPhase (ξ * t)‖ = 1 := norm_unitFrequencyPhase _
  rw [Metric.cauchySeq_iff] at hshift ⊢
  intro ε hε
  obtain ⟨K, hK⟩ := hshift ε hε
  refine ⟨K, ?_⟩
  intro m hm n hn
  have hbridgeM :=
    floorFourierShiftedPartialSum_eq_phase_mul_circle_fourier_sum
      (t := t) hξlo hξhi m
  have hbridgeN :=
    floorFourierShiftedPartialSum_eq_phase_mul_circle_fourier_sum
      (t := t) hξlo hξhi n
  change floorFourierShiftedPartialSum ξ t m =
      unitFrequencyPhase (ξ * t) * floorFourierCirclePointwisePartialSum ξ
        (t : AddCircle (1 : ℝ)) m at hbridgeM
  change floorFourierShiftedPartialSum ξ t n =
      unitFrequencyPhase (ξ * t) * floorFourierCirclePointwisePartialSum ξ
        (t : AddCircle (1 : ℝ)) n at hbridgeN
  rw [hclass] at hbridgeM hbridgeN
  have hdist :
      dist (floorFourierCirclePointwisePartialSum ξ x m)
          (floorFourierCirclePointwisePartialSum ξ x n) =
        dist (floorFourierShiftedPartialSum ξ t m)
          (floorFourierShiftedPartialSum ξ t n) := by
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖floorFourierCirclePointwisePartialSum ξ x m -
          floorFourierCirclePointwisePartialSum ξ x n‖ =
        ‖unitFrequencyPhase (ξ * t) *
          (floorFourierCirclePointwisePartialSum ξ x m -
            floorFourierCirclePointwisePartialSum ξ x n)‖ := by
              rw [norm_mul, hqnorm]
              simp
      _ = ‖unitFrequencyPhase (ξ * t) *
            floorFourierCirclePointwisePartialSum ξ x m -
            unitFrequencyPhase (ξ * t) *
              floorFourierCirclePointwisePartialSum ξ x n‖ := by
              congr 1
              ring
      _ = ‖floorFourierShiftedPartialSum ξ t m -
            floorFourierShiftedPartialSum ξ t n‖ := by
              rw [hbridgeM, hbridgeN]
  rw [hdist]
  exact hK m hm n hn

theorem haarAddCircle_singleton_eq_zero (x : AddCircle (1 : ℝ)) :
    AddCircle.haarAddCircle ({x} : Set (AddCircle (1 : ℝ))) = 0 := by
  let e := AddCircle.equivIoc (1 : ℝ) (-1 / 2)
  let y := e x
  have hmp := AddCircle.measurePreserving_equivIoc (T := (1 : ℝ)) (a := (-1 / 2 : ℝ))
  have hpre : e ⁻¹' ({y} : Set (Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1))) = {x} := by
    ext z
    simp [y, e]
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) {x} = 0 := by
    calc
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) {x} =
          MeasureTheory.volume (e ⁻¹' ({y} : Set (Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1))) : Set (AddCircle (1 : ℝ))) := by
            rw [hpre]
      _ = (MeasureTheory.volume.map e) {y} :=
            (MeasureTheory.Measure.map_apply hmp.measurable
              (measurableSet_singleton y)).symm
      _ = (MeasureTheory.volume.comap (Subtype.val :
            Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) → ℝ)) {y} := by
              rw [hmp.map_eq]
      _ = MeasureTheory.volume ((Subtype.val :
            Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) → ℝ) '' {y}) :=
            comap_subtype_coe_apply measurableSet_Ioc MeasureTheory.volume {y}
      _ = 0 := by
            rw [Set.image_singleton]
            exact Real.volume_singleton
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hvol
  simpa using hvol

theorem floorFourierCircleFunction_fourier_partialSums_tendsto_ae
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,
      Filter.Tendsto
        (fun N => floorFourierCirclePointwisePartialSum ξ x N)
        Filter.atTop (nhds (floorFourierCircleFunction ξ x)) := by
  obtain ⟨ns, hns, hsub⟩ :=
    floorFourierCircleFunction_exists_ae_tendsto_pointwise_fourier_subseq ξ
  have hne : ∀ᵐ x ∂AddCircle.haarAddCircle, x ≠ (0 : AddCircle (1 : ℝ)) := by
    rw [MeasureTheory.ae_iff]
    simpa using haarAddCircle_singleton_eq_zero (0 : AddCircle (1 : ℝ))
  filter_upwards [hsub, hne] with x hxsub hxne
  exact tendsto_nhds_of_cauchySeq_of_subseq
    (floorFourierCirclePointwisePartialSum_cauchy_of_ne_zero
      hξlo hξhi hxne)
    hns.tendsto_atTop hxsub

/-- On a compact set avoiding the zero class, the first circle character stays
uniformly separated from one. This is the compactness input for upgrading the
Fourier partial sums from almost-everywhere convergence to pointwise
convergence away from the singular class. -/
theorem exists_pos_lower_bound_fourier_chord_on_compact
    (K : Set (AddCircle (1 : ℝ))) (hK : IsCompact K)
    (hne : K.Nonempty) (hK0 : ∀ x ∈ K, x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ ‖(1 : ℂ) - fourier 1 x‖ := by
  let f : AddCircle (1 : ℝ) → ℝ := fun x => ‖(1 : ℂ) - fourier 1 x‖
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  obtain ⟨x, hxK, hxMin⟩ := hK.exists_isMinOn hne hf.continuousOn
  have hxpos : 0 < f x := by
    dsimp [f]
    apply norm_pos_iff.mpr
    intro heq
    have hfour : fourier 1 x = 1 := (sub_eq_zero.mp heq).symm
    rw [fourier_one] at hfour
    have hcircle : AddCircle.toCircle x = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      apply Circle.coe_injective
      simpa using hfour
    have hzero : x = 0 :=
      AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hcircle
    exact hK0 x hxK hzero
  refine ⟨f x, hxpos, ?_⟩
  intro y hy
  exact hxMin hy

/-- Uniform symmetric Fourier tail bound on a compact subset avoiding zero.
The compact chord lower bound removes the point-dependent denominator from
the finite Abel estimate. -/
theorem floorFourierCirclePointwisePartialSum_tail_le_on_compact
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (K : Set (AddCircle (1 : ℝ))) (δ : ℝ) (hδ : 0 < δ)
    (hKδ : ∀ x ∈ K, δ ≤ ‖(1 : ℂ) - fourier 1 x‖)
    (M N : ℕ) (hM : 2 ≤ M) (hMN : M ≤ N) :
    ∀ x ∈ K,
      dist (floorFourierCirclePointwisePartialSum ξ x M)
        (floorFourierCirclePointwisePartialSum ξ x N) ≤
        (2 / δ) * (1 / (M : ℝ)) := by
  intro x hxK
  let t : ℝ := (AddCircle.equivIoc (1 : ℝ) (-1 / 2) x).val
  have htmem := (AddCircle.equivIoc (1 : ℝ) (-1 / 2) x).property
  change t ∈ Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) at htmem
  simp only [Set.mem_Ioc] at htmem
  have ht : |t| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by nlinarith⟩
  have hclass : (t : AddCircle (1 : ℝ)) = x := by
    dsimp [t]
    simp
  have ht0 : t ≠ 0 := by
    intro hzero
    have hxzero : x = 0 := by simpa [hzero] using hclass.symm
    have hbound := hKδ x hxK
    rw [hxzero] at hbound
    have hchar : fourier 1 (0 : AddCircle (1 : ℝ)) = 1 := by simp
    rw [hchar] at hbound
    norm_num at hbound
    linarith
  have hchord : ‖1 - unitFrequencyPhase t‖ =
      ‖(1 : ℂ) - fourier 1 x‖ := by
    rw [← hclass, fourier_coe_apply]
    congr 1
    unfold unitFrequencyPhase
    congr 1
    push_cast
    norm_num
    ring
  have htail := norm_symmetric_floorFourierCoefficient_tail_le
    M N hM hMN hξlo hξhi ht ht0
  have htail' :
      ‖floorFourierShiftedPartialSum ξ t N -
        floorFourierShiftedPartialSum ξ t M‖ ≤
      (2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ)) := by
    simpa [floorFourierShiftedPartialSum] using htail
  have hden : δ ≤ ‖1 - unitFrequencyPhase t‖ := by
    rw [hchord]
    exact hKδ x hxK
  have hdenpos : 0 < ‖1 - unitFrequencyPhase t‖ := lt_of_lt_of_le hδ hden
  have hratio : 2 / ‖1 - unitFrequencyPhase t‖ ≤ 2 / δ :=
    div_le_div₀ (by norm_num) le_rfl hδ hden
  have hMpos : 0 ≤ 1 / (M : ℝ) := by positivity
  have htail'' :
      ‖floorFourierShiftedPartialSum ξ t N -
        floorFourierShiftedPartialSum ξ t M‖ ≤ (2 / δ) * (1 / (M : ℝ)) :=
    le_trans htail' (mul_le_mul_of_nonneg_right hratio hMpos)
  have hbridgeM := floorFourierShiftedPartialSum_eq_phase_mul_circle_fourier_sum
    (t := t) hξlo hξhi M
  have hbridgeN := floorFourierShiftedPartialSum_eq_phase_mul_circle_fourier_sum
    (t := t) hξlo hξhi N
  have hqnorm : ‖unitFrequencyPhase (ξ * t)‖ = 1 := norm_unitFrequencyPhase _
  have hdist :
      dist (floorFourierShiftedPartialSum ξ t M)
        (floorFourierShiftedPartialSum ξ t N) =
      dist (floorFourierCirclePointwisePartialSum ξ x M)
        (floorFourierCirclePointwisePartialSum ξ x N) := by
    rw [dist_eq_norm, dist_eq_norm, hbridgeM, hbridgeN]
    rw [hclass]
    calc
      ‖unitFrequencyPhase (ξ * t) *
          floorFourierCirclePointwisePartialSum ξ x M -
        unitFrequencyPhase (ξ * t) *
          floorFourierCirclePointwisePartialSum ξ x N‖ =
        ‖unitFrequencyPhase (ξ * t) *
          (floorFourierCirclePointwisePartialSum ξ x M -
            floorFourierCirclePointwisePartialSum ξ x N)‖ := by congr 1 <;> ring
      _ = ‖floorFourierCirclePointwisePartialSum ξ x M -
          floorFourierCirclePointwisePartialSum ξ x N‖ := by
        rw [norm_mul, hqnorm, one_mul]
  calc
    dist (floorFourierCirclePointwisePartialSum ξ x M)
        (floorFourierCirclePointwisePartialSum ξ x N) =
        dist (floorFourierShiftedPartialSum ξ t M)
          (floorFourierShiftedPartialSum ξ t N) := hdist.symm
    _ = ‖floorFourierShiftedPartialSum ξ t N -
        floorFourierShiftedPartialSum ξ t M‖ := by
          rw [dist_eq_norm]
          rw [norm_sub_rev]
    _ ≤ (2 / δ) * (1 / (M : ℝ)) := htail''

/-- The circle Fourier partial sums are uniformly Cauchy on any set with a
uniform positive lower bound for the first-character chord. -/
theorem floorFourierCirclePointwisePartialSum_uniform_cauchy_on_compact
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (K : Set (AddCircle (1 : ℝ))) (δ : ℝ) (hδ : 0 < δ)
    (hKδ : ∀ x ∈ K, δ ≤ ‖(1 : ℂ) - fourier 1 x‖) :
    ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ x ∈ K, ∀ M ≥ M₀, ∀ N ≥ M₀,
      dist (floorFourierCirclePointwisePartialSum ξ x M)
        (floorFourierCirclePointwisePartialSum ξ x N) < ε := by
  let C : ℝ := 2 / δ
  have hCpos : 0 < C := by dsimp [C]; positivity
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (C / ε)
  refine ⟨max K₀ 2, ?_⟩
  intro x hx M hM N hN
  have hM2 : 2 ≤ M := le_trans (le_max_right K₀ 2) hM
  have hN2 : 2 ≤ N := le_trans (le_max_right K₀ 2) hN
  have hK₀M : (K₀ : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast le_trans (le_max_left K₀ 2) hM
  have hK₀N : (K₀ : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (le_max_left K₀ 2) hN
  have hCεK : C < ε * (K₀ : ℝ) := by
    have hK₀' : C / ε < (K₀ : ℝ) := by exact_mod_cast hK₀
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hK₀'
  have hCεM : C < ε * (M : ℝ) :=
    lt_of_lt_of_le hCεK (mul_le_mul_of_nonneg_left hK₀M hε.le)
  have hCεN : C < ε * (N : ℝ) :=
    lt_of_lt_of_le hCεK (mul_le_mul_of_nonneg_left hK₀N hε.le)
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hdecayM : C * (1 / (M : ℝ)) < ε := by
    rw [mul_one_div]
    exact (div_lt_iff₀ hMpos).2 hCεM
  have hdecayN : C * (1 / (N : ℝ)) < ε := by
    rw [mul_one_div]
    exact (div_lt_iff₀ hNpos).2 hCεN
  by_cases hMN : M ≤ N
  · have htail := floorFourierCirclePointwisePartialSum_tail_le_on_compact
      hξlo hξhi K δ hδ hKδ M N hM2 hMN x hx
    calc
      dist (floorFourierCirclePointwisePartialSum ξ x M)
          (floorFourierCirclePointwisePartialSum ξ x N) ≤
          C * (1 / (M : ℝ)) := by simpa [C] using htail
      _ < ε := hdecayM
  · have hNM : N ≤ M := le_of_not_ge hMN
    have htail := floorFourierCirclePointwisePartialSum_tail_le_on_compact
      hξlo hξhi K δ hδ hKδ N M hN2 hNM x hx
    calc
      dist (floorFourierCirclePointwisePartialSum ξ x M)
          (floorFourierCirclePointwisePartialSum ξ x N) =
          dist (floorFourierCirclePointwisePartialSum ξ x N)
            (floorFourierCirclePointwisePartialSum ξ x M) := dist_comm _ _
      _ ≤ C * (1 / (N : ℝ)) := by simpa [C] using htail
      _ < ε := hdecayN

/-- The pointwise limit of the circle Fourier partial sums, defined to be zero
at the singular zero class. -/
noncomputable def floorFourierCirclePointwiseLimit (ξ : ℝ)
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (x : AddCircle (1 : ℝ)) : ℂ :=
  if hx : x = 0 then 0 else
    Classical.choose (cauchySeq_tendsto_of_complete
      (floorFourierCirclePointwisePartialSum_cauchy_of_ne_zero
        hξlo hξhi hx))

theorem floorFourierCirclePointwisePartialSum_tendsto_at_ne_zero
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    {x : AddCircle (1 : ℝ)} (hx : x ≠ 0) :
    Filter.Tendsto
      (fun N => floorFourierCirclePointwisePartialSum ξ x N)
      Filter.atTop
      (nhds (floorFourierCirclePointwiseLimit ξ hξlo hξhi x)) := by
  rw [floorFourierCirclePointwiseLimit, dif_neg hx]
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete
    (floorFourierCirclePointwisePartialSum_cauchy_of_ne_zero
      hξlo hξhi hx))

/-- On a set with a uniform positive chord bound, the Fourier partial sums
converge uniformly to their pointwise Cauchy limit. -/
theorem floorFourierCirclePointwisePartialSum_tendsto_uniformly_on
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (K : Set (AddCircle (1 : ℝ))) (δ : ℝ) (hδ : 0 < δ)
    (hKδ : ∀ x ∈ K, δ ≤ ‖(1 : ℂ) - fourier 1 x‖) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K,
      dist (floorFourierCirclePointwisePartialSum ξ x N)
        (floorFourierCirclePointwiseLimit ξ hξlo hξhi x) < ε := by
  intro ε hε
  obtain ⟨N₀, hCauchy⟩ :=
    floorFourierCirclePointwisePartialSum_uniform_cauchy_on_compact
      hξlo hξhi K δ hδ hKδ (ε / 2) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN x hxK
  have hx0 : x ≠ 0 := by
    intro hxzero
    have hbound := hKδ x hxK
    rw [hxzero] at hbound
    have hchar : fourier 1 (0 : AddCircle (1 : ℝ)) = 1 := by simp
    rw [hchar] at hbound
    norm_num at hbound
    linarith
  have hlim := floorFourierCirclePointwisePartialSum_tendsto_at_ne_zero
    hξlo hξhi hx0
  have hcloseEventually : ∀ᶠ m : ℕ in Filter.atTop,
      dist (floorFourierCirclePointwisePartialSum ξ x m)
        (floorFourierCirclePointwiseLimit ξ hξlo hξhi x) < ε / 2 := by
    filter_upwards [hlim.eventually
      (Metric.ball_mem_nhds (floorFourierCirclePointwiseLimit ξ hξlo hξhi x)
        (ε := ε / 2) (by linarith))]
      with m hm
    simpa [Metric.mem_ball, dist_comm] using hm
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.1 hcloseEventually
  let m := max P N₀
  have hmP : P ≤ m := le_max_left _ _
  have hmN₀ : N₀ ≤ m := le_max_right _ _
  have hclose := hP m hmP
  have hpair := hCauchy x hxK N hN m hmN₀
  calc
    dist (floorFourierCirclePointwisePartialSum ξ x N)
        (floorFourierCirclePointwiseLimit ξ hξlo hξhi x) ≤
        dist (floorFourierCirclePointwisePartialSum ξ x N)
            (floorFourierCirclePointwisePartialSum ξ x m) +
          dist (floorFourierCirclePointwisePartialSum ξ x m)
            (floorFourierCirclePointwiseLimit ξ hξlo hξhi x) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hpair hclose
    _ = ε := by ring

/-- The pointwise Fourier limit is continuous on every set with a uniform
positive first-character chord bound. -/
theorem floorFourierCirclePointwiseLimit_continuousOn_of_chord_bound
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (K : Set (AddCircle (1 : ℝ))) (δ : ℝ) (hδ : 0 < δ)
    (hKδ : ∀ x ∈ K, δ ≤ ‖(1 : ℂ) - fourier 1 x‖) :
    ContinuousOn (floorFourierCirclePointwiseLimit ξ hξlo hξhi) K := by
  have huniform : TendstoUniformlyOn
      (fun N x => floorFourierCirclePointwisePartialSum ξ x N)
      (floorFourierCirclePointwiseLimit ξ hξlo hξhi) Filter.atTop K := by
    intro u hu
    obtain ⟨ε, hε, hball⟩ := Metric.mem_uniformity_dist.1 hu
    obtain ⟨N₀, hN₀⟩ := floorFourierCirclePointwisePartialSum_tendsto_uniformly_on
      hξlo hξhi K δ hδ hKδ ε hε
    refine Filter.eventually_atTop.2 ⟨N₀, ?_⟩
    intro N hN x hx
    have hbound := hN₀ N hN x hx
    exact hball (by simpa [dist_comm] using hbound)
  apply huniform.continuousOn
  exact Filter.Frequently.of_forall fun N =>
    (show Continuous (fun x => floorFourierCirclePointwisePartialSum ξ x N) from by
      unfold floorFourierCirclePointwisePartialSum
      fun_prop).continuousOn

theorem floorFourierCirclePointwiseLimit_ae_eq
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2) :
    floorFourierCirclePointwiseLimit ξ hξlo hξhi =ᵐ[AddCircle.haarAddCircle]
      floorFourierCircleFunction ξ := by
  have hconv := floorFourierCircleFunction_fourier_partialSums_tendsto_ae
    hξlo hξhi
  have hne : ∀ᵐ x ∂AddCircle.haarAddCircle, x ≠ (0 : AddCircle (1 : ℝ)) := by
    rw [MeasureTheory.ae_iff]
    simpa using haarAddCircle_singleton_eq_zero (0 : AddCircle (1 : ℝ))
  filter_upwards [hconv, hne] with x hxconv hx0
  exact tendsto_nhds_unique
    (floorFourierCirclePointwisePartialSum_tendsto_at_ne_zero hξlo hξhi hx0)
    hxconv

/-- The Fourier partial-sum limit agrees with the paper's fractional-part
function at every nonzero circle point. -/
theorem floorFourierCirclePointwiseLimit_eq_of_ne_zero
    {ξ : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    {x : AddCircle (1 : ℝ)} (hx : x ≠ 0) :
    floorFourierCirclePointwiseLimit ξ hξlo hξhi x =
      floorFourierCircleFunction ξ x := by
  let chord : AddCircle (1 : ℝ) → ℝ := fun y => ‖(1 : ℂ) - fourier 1 y‖
  have hchordcont : Continuous chord := by
    dsimp [chord]
    fun_prop
  have hchordpos : 0 < chord x := by
    dsimp [chord]
    apply norm_pos_iff.mpr
    intro heq
    have hfour : fourier 1 x = 1 := (sub_eq_zero.mp heq).symm
    rw [fourier_one] at hfour
    have hcircle : AddCircle.toCircle x = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      apply Circle.coe_injective
      simpa using hfour
    exact hx (AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hcircle)
  let δ : ℝ := chord x / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let U : Set (AddCircle (1 : ℝ)) := {y | δ < chord y}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const hchordcont
  have hxU : x ∈ U := by
    dsimp [U, δ]
    linarith
  have hUbound : ∀ y ∈ U, δ ≤ chord y := by
    intro y hy
    exact le_of_lt (by simpa [U] using hy)
  have hUzero : ∀ y ∈ U, y ≠ 0 := by
    intro y hy hyzero
    have hybound := hUbound y hy
    have hzerochord : chord (0 : AddCircle (1 : ℝ)) = 0 := by
      simp [chord]
    rw [hyzero, hzerochord] at hybound
    linarith
  have hlimcont : ContinuousOn (floorFourierCirclePointwiseLimit ξ hξlo hξhi) U := by
    apply floorFourierCirclePointwiseLimit_continuousOn_of_chord_bound
      hξlo hξhi U δ hδ
    intro y hy
    exact hUbound y hy
  have hfuncont : ContinuousOn (floorFourierCircleFunction ξ) U := by
    intro y hy
    exact ContinuousAt.continuousWithinAt
      (floorFourierCircleFunction_continuousAt_of_ne_zero (hUzero y hy))
  have hae := MeasureTheory.ae_restrict_of_ae (s := U)
    (floorFourierCirclePointwiseLimit_ae_eq hξlo hξhi)
  have heqOn := MeasureTheory.Measure.eqOn_open_of_ae_eq hae hUopen hlimcont hfuncont
  exact heqOn hxU

/-- On a noninteger real representative, the circle limit is the exponential
of the negative fractional part. -/
theorem floorFourierCirclePointwiseLimit_coe_eq_fractional_part
    {ξ t : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (ht : t ∉ Set.range fun z : ℤ => (z : ℝ)) :
    floorFourierCirclePointwiseLimit ξ hξlo hξhi (t : AddCircle (1 : ℝ)) =
      unitFrequencyPhase (-ξ * (t - (Int.floor t : ℝ))) := by
  have ht0 : (t : AddCircle (1 : ℝ)) ≠ 0 := by
    intro hzero
    rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hzero with ⟨z, hz⟩
    apply ht
    refine ⟨z, ?_⟩
    simpa using hz
  have hfloorne : t ≠ (Int.floor t : ℝ) := by
    intro heq
    apply ht
    exact ⟨Int.floor t, heq.symm⟩
  let r : ℝ := Int.fract t
  have hr : r ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · dsimp [r]
      exact Int.fract_pos.mpr hfloorne
    · dsimp [r]
      exact (Int.fract_lt_one t).le
  have hkcast : (Int.floor t : ℝ) = (Int.floor t : ℤ) • (1 : ℝ) := by simp
  have hkzero : ((Int.floor t : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [hkcast, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero]
  have hdecomp : t = r + (Int.floor t : ℝ) := by
    dsimp [r]
    exact (Int.fract_add_floor t).symm
  have hcircle : (t : AddCircle (1 : ℝ)) = (r : AddCircle (1 : ℝ)) := by
    rw [hdecomp, AddCircle.coe_add, hkzero, add_zero]
  have hval : floorFourierCircleFunction ξ (t : AddCircle (1 : ℝ)) =
      unitFrequencyPhase (-ξ * r) := by
    rw [floorFourierCircleFunction, hcircle]
    exact AddCircle.liftIoc_coe_apply (by simpa [zero_add] using hr)
  calc
    floorFourierCirclePointwiseLimit ξ hξlo hξhi (t : AddCircle (1 : ℝ)) =
        floorFourierCircleFunction ξ (t : AddCircle (1 : ℝ)) :=
      floorFourierCirclePointwiseLimit_eq_of_ne_zero hξlo hξhi ht0
    _ = unitFrequencyPhase (-ξ * r) := hval

/-- The shifted real Fourier partial sums converge to the exact phase at the
integer floor whenever the argument is not an integer. -/
theorem floorFourierShiftedPartialSum_tendsto_floor_phase
    {ξ t : ℝ} (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (ht : t ∉ Set.range fun z : ℤ => (z : ℝ)) :
    Filter.Tendsto (floorFourierShiftedPartialSum ξ t)
      Filter.atTop (nhds (unitFrequencyPhase (ξ * (Int.floor t : ℝ)))) := by
  have ht0 : (t : AddCircle (1 : ℝ)) ≠ 0 := by
    intro hzero
    rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hzero with ⟨z, hz⟩
    apply ht
    exact ⟨z, by simpa using hz⟩
  have hcircle := floorFourierCirclePointwisePartialSum_tendsto_at_ne_zero
    hξlo hξhi ht0
  let q : ℂ := unitFrequencyPhase (ξ * t)
  have hq : Filter.Tendsto (fun _ : ℕ => q) Filter.atTop (nhds q) := tendsto_const_nhds
  have hproduct := hq.mul hcircle
  have hbridge (N : ℕ) :=
    floorFourierShiftedPartialSum_eq_phase_mul_circle_fourier_sum
      (t := t) hξlo hξhi N
  have hsum : Filter.Tendsto (floorFourierShiftedPartialSum ξ t)
      Filter.atTop (nhds (q * floorFourierCirclePointwiseLimit ξ hξlo hξhi
        (t : AddCircle (1 : ℝ)))) := by
    apply hproduct.congr'
    filter_upwards with N
    simpa [q, floorFourierCirclePointwisePartialSum] using (hbridge N).symm
  have harg : ξ * t = ξ * Int.fract t + ξ * (Int.floor t : ℝ) := by
    calc
      ξ * t = ξ * (Int.fract t + (Int.floor t : ℝ)) :=
        congrArg (fun s : ℝ => ξ * s) (Int.fract_add_floor t).symm
      _ = ξ * Int.fract t + ξ * (Int.floor t : ℝ) := by ring
  have hphase : q * floorFourierCirclePointwiseLimit ξ hξlo hξhi
      (t : AddCircle (1 : ℝ)) = unitFrequencyPhase (ξ * (Int.floor t : ℝ)) := by
    rw [floorFourierCirclePointwiseLimit_coe_eq_fractional_part hξlo hξhi ht]
    dsimp [q]
    calc
      unitFrequencyPhase (ξ * t) * unitFrequencyPhase (-ξ * Int.fract t) =
          (unitFrequencyPhase (ξ * Int.fract t) *
            unitFrequencyPhase (-ξ * Int.fract t)) *
            unitFrequencyPhase (ξ * (Int.floor t : ℝ)) := by
              rw [harg, unitFrequencyPhase_add]
              ring
      _ = unitFrequencyPhase (ξ * (Int.floor t : ℝ)) := by
            have hcancel : unitFrequencyPhase (ξ * Int.fract t) *
                unitFrequencyPhase (-ξ * Int.fract t) = 1 := by
              rw [← unitFrequencyPhase_add]
              simp [unitFrequencyPhase]
            rw [hcancel, one_mul]
  rw [hphase] at hsum
  exact hsum

/-- A uniform eventual bound on distances to a fixed point passes to the
limit of a convergent sequence. -/
theorem norm_sub_limit_le_of_eventually_norm_sub_le
    {α : Type*} [NormedAddCommGroup α] {u : ℕ → α} {L a : α} {C : ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds L)) (N₀ : ℕ)
    (hbound : ∀ N ≥ N₀, ‖u N - a‖ ≤ C) : ‖L - a‖ ≤ C := by
  have hdiff : Filter.Tendsto (fun N => u N - a) Filter.atTop (nhds (L - a)) :=
    hu.sub tendsto_const_nhds
  have hnorm := continuous_norm.continuousAt.tendsto.comp hdiff
  apply isClosed_Iic.mem_of_tendsto hnorm
  exact Filter.eventually_atTop.2 ⟨N₀, hbound⟩

/-- Every real number has a translate by an integer in the centered unit
interval. -/
theorem exists_centered_integer_shift (t : ℝ) :
    ∃ k : ℤ, |t - (k : ℝ)| ≤ 1 / 2 := by
  let k : ℤ := Int.floor (t + 1 / 2)
  refine ⟨k, ?_⟩
  rw [abs_le]
  constructor
  · dsimp [k]
    have hk := Int.floor_le (t + 1 / 2)
    linarith
  · dsimp [k]
    have hk := Int.lt_floor_add_one (t + 1 / 2)
    linarith

/-- Centered remainder estimate for `ar:floor-removal`. The far case uses the
pointwise Fourier tail, while the near case uses the trivial finite-sum bound. -/
theorem floorFourierRemoval_remainder_centered
    (M : ℕ) (hM : 2 ≤ M) {ξ t : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (ht : |t| ≤ 1 / 2) :
    ‖unitFrequencyPhase (ξ * (Int.floor t : ℝ)) -
      floorFourierShiftedPartialSum ξ t M‖ ≤
      12 * Real.log (2 * (M : ℝ)) * floorBoundaryKernel M hM t := by
  let target : ℂ := unitFrequencyPhase (ξ * (Int.floor t : ℝ))
  let S : ℂ := floorFourierShiftedPartialSum ξ t M
  have hcoeff := floorFourierCoefficient_sum_norm_le_log M hM hξlo hξhi
  have hS : ‖S‖ ≤ 10 * Real.log (2 * (M : ℝ)) := by
    dsimp [S, floorFourierShiftedPartialSum]
    calc
      ‖∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            unitFrequencyPhase (((m : ℝ) + ξ) * t)‖ ≤
        ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ‖floorFourierCoefficient m ξ *
            unitFrequencyPhase (((m : ℝ) + ξ) * t)‖ := norm_sum_le _ _
      _ = ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ‖floorFourierCoefficient m ξ‖ := by
            apply Finset.sum_congr rfl
            intro m hm
            simp [norm_mul, norm_unitFrequencyPhase]
      _ ≤ 10 * Real.log (2 * (M : ℝ)) := hcoeff
  have htargetnorm : ‖target‖ = 1 := by
    dsimp [target]
    exact norm_unitFrequencyPhase _
  have htrivial : ‖target - S‖ ≤ 1 + 10 * Real.log (2 * (M : ℝ)) := by
    calc
      ‖target - S‖ ≤ ‖target‖ + ‖S‖ := norm_sub_le _ _
      _ ≤ 1 + 10 * Real.log (2 * (M : ℝ)) := add_le_add (by rw [htargetnorm]) hS
  have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlog : (6 / 5 : ℝ) ≤ Real.log (2 * (M : ℝ)) := by
    have hlog4 : (6 / 5 : ℝ) ≤ Real.log 4 := by
      convert Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) using 1 <;>
        norm_num
    exact hlog4.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hlarge : 1 < (M : ℝ) * |t| ∨ (M : ℝ) * |t| ≤ 1 := lt_or_ge 1 _
  rcases hlarge with hfar | hnear
  · have ht0 : t ≠ 0 := by
      intro hz
      rw [hz, abs_zero, mul_zero] at hfar
      norm_num at hfar
    have hnotInt : t ∉ Set.range fun z : ℤ => (z : ℝ) := by
      rintro ⟨z, hzt⟩
      have hzabs : |(z : ℝ)| ≤ 1 / 2 := by simpa [hzt] using ht
      rcases lt_trichotomy z 0 with hzneg | hzero | hzpos
      · have hzle : (z : ℝ) ≤ -1 := by exact_mod_cast (Int.le_sub_one_of_lt hzneg)
        have hone : 1 ≤ |(z : ℝ)| := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        linarith
      · exact ht0 (by simpa [hzero] using hzt.symm)
      · have hzge : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (Int.add_one_le_of_lt hzpos)
        have hone : 1 ≤ |(z : ℝ)| := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        linarith
    have hlimit := floorFourierShiftedPartialSum_tendsto_floor_phase
      hξlo hξhi hnotInt
    have hdenpos : 0 < ‖1 - unitFrequencyPhase t‖ :=
      norm_one_sub_unitFrequencyPhase_pos_of_centered_ne_zero ht ht0
    have htail : ∀ N ≥ M,
        ‖floorFourierShiftedPartialSum ξ t N - S‖ ≤
          (2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ)) := by
      intro N hMN
      simpa [S, floorFourierShiftedPartialSum] using
        (norm_symmetric_floorFourierCoefficient_tail_le
          M N hM hMN hξlo hξhi ht ht0)
    have herr := norm_sub_limit_le_of_eventually_norm_sub_le
      hlimit M htail
    have hchord := four_mul_realDistanceToIntegers_le_norm_one_sub_unitFrequencyPhase ht
    rw [realDistanceToIntegers_eq_abs_of_abs_le_half ht] at hchord
    have hrecip : 2 / ‖1 - unitFrequencyPhase t‖ ≤ 2 / (4 * |t|) :=
      div_le_div₀ (by norm_num) le_rfl (by positivity) hchord
    have hbound : (2 / ‖1 - unitFrequencyPhase t‖) * (1 / (M : ℝ)) ≤
        ((M : ℝ) * |t|)⁻¹ := by
      calc
        _ ≤ (2 / (4 * |t|)) * (1 / (M : ℝ)) :=
          mul_le_mul_of_nonneg_right hrecip (by positivity)
        _ ≤ ((M : ℝ) * |t|)⁻¹ := by
          have hMpos : 0 < (M : ℝ) := by positivity
          have htpos : 0 < |t| := abs_pos.mpr ht0
          have hprodpos : 0 < (M : ℝ) * |t| := mul_pos hMpos htpos
          have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
          rw [show 2 / (4 * |t|) * (1 / (M : ℝ)) =
            (1 / 2 : ℝ) * ((M : ℝ) * |t|)⁻¹ by
              field_simp <;> norm_num]
          exact mul_le_of_le_one_left (inv_nonneg.mpr (le_of_lt hprodpos)) hhalf
    have hkernel : floorBoundaryKernel M hM t = ((M : ℝ) * |t|)⁻¹ := by
      rw [floorBoundaryKernel_eq_min_of_abs_le_half M hM ht]
      have hprodpos : 0 < (M : ℝ) * |t| := by positivity
      have hinv : ((M : ℝ) * |t|)⁻¹ < 1 := (inv_lt_one₀ hprodpos).2 hfar
      rw [if_neg (show t ≠ 0 from ht0)]
      exact min_eq_right hinv.le
    have herr' : ‖target - S‖ ≤ floorBoundaryKernel M hM t := by
      dsimp [target, S] at herr ⊢
      calc
        _ = ‖unitFrequencyPhase (ξ * (Int.floor t : ℝ)) -
            floorFourierShiftedPartialSum ξ t M‖ := rfl
        _ = ‖floorFourierShiftedPartialSum ξ t M -
            unitFrequencyPhase (ξ * (Int.floor t : ℝ))‖ := norm_sub_rev _ _
        _ ≤ ((M : ℝ) * |t|)⁻¹ := by
          rw [norm_sub_rev]
          exact herr.trans hbound
        _ = floorBoundaryKernel M hM t := hkernel.symm
    have hone : 1 ≤ 12 * Real.log (2 * (M : ℝ)) := by nlinarith
    calc
      ‖target - S‖ ≤ floorBoundaryKernel M hM t := herr'
      _ ≤ 12 * Real.log (2 * (M : ℝ)) * floorBoundaryKernel M hM t :=
        le_mul_of_one_le_left (floorBoundaryKernel_nonneg M hM t) hone
  · have hkernel : floorBoundaryKernel M hM t = 1 := by
      rw [floorBoundaryKernel_eq_min_of_abs_le_half M hM ht]
      by_cases ht0 : t = 0
      · simp [ht0]
      · have hprodpos : 0 < (M : ℝ) * |t| := by positivity
        have hinv : 1 ≤ ((M : ℝ) * |t|)⁻¹ :=
          (one_le_inv₀ hprodpos).2 hnear
        rw [if_neg ht0]
        exact min_eq_left hinv
    have hlargebound : 1 + 10 * Real.log (2 * (M : ℝ)) ≤
        12 * Real.log (2 * (M : ℝ)) := by nlinarith
    calc
      ‖target - S‖ ≤ 1 + 10 * Real.log (2 * (M : ℝ)) := htrivial
      _ ≤ 12 * Real.log (2 * (M : ℝ)) := hlargebound
      _ = 12 * Real.log (2 * (M : ℝ)) * floorBoundaryKernel M hM t := by
        simp [hkernel]

/-- The floor-removal remainder estimate for every real input. This is the
remainder half of blueprint lemma `ar:floor-removal`; the coefficient-sum
half is stated separately by `floorFourierCoefficient_sum_norm_le_log`. -/
theorem floorFourierRemoval_remainder
    (M : ℕ) (hM : 2 ≤ M) {ξ t : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2) :
    ‖unitFrequencyPhase (ξ * (Int.floor t : ℝ)) -
      floorFourierShiftedPartialSum ξ t M‖ ≤
      12 * Real.log (2 * (M : ℝ)) * floorBoundaryKernel M hM t := by
  obtain ⟨k, hk⟩ := exists_centered_integer_shift t
  let s : ℝ := t - (k : ℝ)
  have hts : t = s + (k : ℝ) := by dsimp [s]; ring
  have hs : |s| ≤ 1 / 2 := by simpa [s] using hk
  have hfloor : Int.floor t = Int.floor s + k := by
    rw [hts, Int.floor_add_intCast]
  have hphase : unitFrequencyPhase (ξ * (Int.floor t : ℝ)) =
      unitFrequencyPhase (ξ * (Int.floor s : ℝ)) *
        unitFrequencyPhase (ξ * (k : ℝ)) := by
    rw [hfloor, Int.cast_add, mul_add, unitFrequencyPhase_add]
  have hsum := floorFourierShiftedPartialSum_add_int ξ s M k
  have hsum_t : floorFourierShiftedPartialSum ξ t M =
      unitFrequencyPhase (ξ * (k : ℝ)) * floorFourierShiftedPartialSum ξ s M := by
    calc
      floorFourierShiftedPartialSum ξ t M =
          floorFourierShiftedPartialSum ξ (s + (k : ℝ)) M := by rw [hts]
      _ = unitFrequencyPhase (ξ * (k : ℝ)) *
          floorFourierShiftedPartialSum ξ s M := hsum
  have hkernel := floorBoundaryKernel_add_int M hM s k
  rw [← hts] at hkernel
  rw [hphase, hsum_t]
  have hcenter := floorFourierRemoval_remainder_centered M hM hξlo hξhi hs
  have hnorm : ‖unitFrequencyPhase (ξ * (k : ℝ))‖ = 1 := norm_unitFrequencyPhase _
  calc
    ‖unitFrequencyPhase (ξ * (Int.floor s : ℝ)) *
          unitFrequencyPhase (ξ * (k : ℝ)) -
        unitFrequencyPhase (ξ * (k : ℝ)) *
          floorFourierShiftedPartialSum ξ s M‖
      = ‖unitFrequencyPhase (ξ * (k : ℝ))‖ *
          ‖unitFrequencyPhase (ξ * (Int.floor s : ℝ)) -
            floorFourierShiftedPartialSum ξ s M‖ := by
          have hfactor :
              unitFrequencyPhase (ξ * (Int.floor s : ℝ)) *
                  unitFrequencyPhase (ξ * (k : ℝ)) -
                unitFrequencyPhase (ξ * (k : ℝ)) *
                  floorFourierShiftedPartialSum ξ s M =
              unitFrequencyPhase (ξ * (k : ℝ)) *
                (unitFrequencyPhase (ξ * (Int.floor s : ℝ)) -
                  floorFourierShiftedPartialSum ξ s M) := by ring
          rw [hfactor, norm_mul]
    _ = ‖unitFrequencyPhase (ξ * (Int.floor s : ℝ)) -
          floorFourierShiftedPartialSum ξ s M‖ := by rw [hnorm, one_mul]
    _ ≤ 12 * Real.log (2 * (M : ℝ)) * floorBoundaryKernel M hM s := hcenter
    _ = 12 * Real.log (2 * (M : ℝ)) * floorBoundaryKernel M hM t := by
          rw [← hkernel]

/-- Complete Lean formulation of blueprint lemma `ar:floor-removal`. The
coefficient norm is the complex absolute value used by the paper, and the
remainder uses `unitFrequencyPhase` for its notation `e`. -/
theorem floorFourierRemoval
    (M : ℕ) (hM : 2 ≤ M) {ξ t : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2) :
    (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      ‖floorFourierCoefficient m ξ‖) ≤ 12 * Real.log (2 * (M : ℝ)) ∧
    ‖unitFrequencyPhase (ξ * (Int.floor t : ℝ)) -
      floorFourierShiftedPartialSum ξ t M‖ ≤
        12 * Real.log (2 * (M : ℝ)) * floorBoundaryKernel M hM t := by
  constructor
  · have hcoeff := floorFourierCoefficient_sum_norm_le_log M hM hξlo hξhi
    have hlog : 0 ≤ Real.log (2 * (M : ℝ)) := by
      apply Real.log_nonneg
      have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    exact le_trans hcoeff (by nlinarith)
  · exact floorFourierRemoval_remainder M hM hξlo hξhi

/-- The Fourier coefficient `a_h` of the blueprint's boundary kernel, defined
using Mathlib's Fourier coefficients on an additive circle of period one. -/
noncomputable def boundaryKernelFourierCoefficient (M : ℕ) (hM : 2 ≤ M)
    (h : ℤ) : ℂ :=
  fourierCoeffOn (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num)
    (fun t => (floorBoundaryKernel M hM t : ℂ)) h

theorem intervalIntegrable_boundaryKernelFourierIntegrand_of_continuousOn
    (M : ℕ) (hM : 2 ≤ M) (h : ℤ) (a b : ℝ) (hab : a ≤ b)
    (hF : ContinuousOn (fun t => floorBoundaryKernel M hM t : ℝ → ℂ)
      (Set.Icc a b)) :
    IntervalIntegrable
      (fun t => fourier (-h) (t : AddCircle (1 : ℝ)) •
        (floorBoundaryKernel M hM t : ℂ))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
  letI : MeasureTheory.IsLocallyFiniteMeasure
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := Real.locallyFinite_volume
  have hphase : ContinuousOn
      (fun t : ℝ => fourier (-h) (t : AddCircle (1 : ℝ))) (Set.Icc a b) :=
    ((map_continuous (fourier (-h))).comp (AddCircle.continuous_mk' (1 : ℝ))).continuousOn
  have hprod : ContinuousOn
      (fun t : ℝ => fourier (-h) (t : AddCircle (1 : ℝ)) •
        (floorBoundaryKernel M hM t : ℂ)) (Set.Icc a b) := hphase.smul hF
  exact hprod.intervalIntegrable_of_Icc (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hab

theorem boundaryKernelFourierCoefficient_eq_integral (M : ℕ) (hM : 2 ≤ M)
    (h : ℤ) :
    boundaryKernelFourierCoefficient M hM h =
      (1 : ℂ) • ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ) := by
  rw [boundaryKernelFourierCoefficient, fourierCoeffOn_eq_integral]
  norm_num

theorem boundaryKernelFourierCoefficient_zero_eq_integral (M : ℕ)
    (hM : 2 ≤ M) :
    boundaryKernelFourierCoefficient M hM 0 =
      (↑(∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), floorBoundaryKernel M hM t) : ℂ) := by
  rw [boundaryKernelFourierCoefficient_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul]
  exact intervalIntegral.integral_ofReal

theorem boundaryKernelFourierCoefficient_zero_bound (M : ℕ) (hM : 2 ≤ M) :
    ‖boundaryKernelFourierCoefficient M hM 0‖ ≤
      (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) / (M : ℝ) := by
  have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : 0 < (M : ℝ) := by linarith
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogbig : Real.log 4 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hlogsmall : Real.log ((M : ℝ) / 2) ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hlognon : 0 ≤ Real.log ((M : ℝ) / 2) :=
    Real.log_nonneg (by nlinarith)
  have hone : 1 ≤ Real.log (2 * (M : ℝ)) / Real.log 4 :=
    (le_div_iff₀ hlog4).2 (by nlinarith)
  have hfactor : 1 + Real.log ((M : ℝ) / 2) ≤
      (1 + (Real.log 4)⁻¹) * Real.log (2 * (M : ℝ)) := by
    have hrecip : Real.log (2 * (M : ℝ)) / Real.log 4 =
        (Real.log 4)⁻¹ * Real.log (2 * (M : ℝ)) := by ring
    rw [hrecip] at hone
    nlinarith
  have hvalue : 0 ≤ (2 / (M : ℝ)) *
      (1 + Real.log ((M : ℝ) / 2)) := by positivity
  have hnorm : ‖boundaryKernelFourierCoefficient M hM 0‖ =
      (2 / (M : ℝ)) * (1 + Real.log ((M : ℝ) / 2)) := by
    rw [boundaryKernelFourierCoefficient_zero_eq_integral,
      intervalIntegral_floorBoundaryKernel_centered]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hvalue]
  rw [hnorm]
  have hmul := mul_le_mul_of_nonneg_left hfactor (by norm_num : (0 : ℝ) ≤ 2)
  have hdiv := div_le_div_of_nonneg_right hmul (le_of_lt hMpos)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

theorem boundaryKernelFourierCoefficient_norm_le_integral (M : ℕ)
    (hM : 2 ≤ M) (h : ℤ) :
    ‖boundaryKernelFourierCoefficient M hM h‖ ≤
      ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), floorBoundaryKernel M hM t := by
  rw [boundaryKernelFourierCoefficient_eq_integral]
  calc
    ‖(1 : ℂ) • ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)‖ ≤
      ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        ‖fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)‖ := by
            simpa using (intervalIntegral.norm_integral_le_integral_norm
              (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
              (f := fun t => fourier (-h) (t : AddCircle (1 : ℝ)) •
                (floorBoundaryKernel M hM t : ℂ)) (by norm_num))
    _ = ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), floorBoundaryKernel M hM t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change ‖fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)‖ = floorBoundaryKernel M hM t
      have hchar : ‖fourier (-h) (t : AddCircle (1 : ℝ))‖ = 1 := by
        rw [fourier_apply, Circle.norm_coe]
      rw [norm_smul, hchar, one_mul, Complex.norm_real, Real.norm_of_nonneg
        (floorBoundaryKernel_nonneg M hM t)]

theorem boundaryKernelFourierCoefficient_uniform_bound (M : ℕ)
    (hM : 2 ≤ M) (h : ℤ) :
    ‖boundaryKernelFourierCoefficient M hM h‖ ≤
      (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) / (M : ℝ) := by
  have hvalue : (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), floorBoundaryKernel M hM t) =
      (2 / (M : ℝ)) * (1 + Real.log ((M : ℝ) / 2)) :=
    intervalIntegral_floorBoundaryKernel_centered M hM
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogbig : Real.log 4 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith [show (2 : ℝ) ≤ M by exact_mod_cast hM])
  have hlogsmall : Real.log ((M : ℝ) / 2) ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith [show (2 : ℝ) ≤ M by exact_mod_cast hM])
  have hone : 1 ≤ Real.log (2 * (M : ℝ)) / Real.log 4 :=
    (le_div_iff₀ hlog4).2 (by nlinarith)
  have hfactor : 1 + Real.log ((M : ℝ) / 2) ≤
      (1 + (Real.log 4)⁻¹) * Real.log (2 * (M : ℝ)) := by
    have hrecip : Real.log (2 * (M : ℝ)) / Real.log 4 =
        (Real.log 4)⁻¹ * Real.log (2 * (M : ℝ)) := by ring
    rw [hrecip] at hone
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hfactor (by norm_num : (0 : ℝ) ≤ 2)
  have hscaled : (2 / (M : ℝ)) * (1 + Real.log ((M : ℝ) / 2)) ≤
      (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) / (M : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hmul (le_of_lt hMpos)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  calc
    ‖boundaryKernelFourierCoefficient M hM h‖ ≤
        ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), floorBoundaryKernel M hM t :=
      boundaryKernelFourierCoefficient_norm_le_integral M hM h
    _ = (2 / (M : ℝ)) * (1 + Real.log ((M : ℝ) / 2)) := hvalue
    _ ≤ (2 * (1 + (Real.log 4)⁻¹)) *
        Real.log (2 * (M : ℝ)) / (M : ℝ) := hscaled

theorem floorBoundaryKernel_hasDerivAt_pos_tail (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (htlower : 1 / (M : ℝ) < t) (hthigh : t < 1 / 2) :
    HasDerivAt (fun y => floorBoundaryKernel M hM y)
      (- (M : ℝ) / ((M : ℝ) * t) ^ 2) t := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hmem : ∀ᶠ y : ℝ in nhds t, y ∈ Set.Ioo (1 / (M : ℝ)) (1 / 2) :=
    isOpen_Ioo.mem_nhds ⟨htlower, hthigh⟩
  have heq : (fun y => floorBoundaryKernel M hM y) =ᶠ[nhds t]
      (fun y => ((M : ℝ) * y)⁻¹) := hmem.mono fun y hy => by
    change floorBoundaryKernel M hM y = ((M : ℝ) * y)⁻¹
    have hypos : 0 ≤ y := le_of_lt (lt_trans (by positivity) hy.1)
    rw [floorBoundaryKernel_eq_piecewise_pos M hM hypos hy.2.le,
      if_neg (not_le_of_gt hy.1)]
  have harg : (M : ℝ) * t ≠ 0 :=
    ne_of_gt (mul_pos hMpos (lt_trans (by positivity) htlower))
  exact (hasDerivAt_const_mul (M : ℝ) (x := t)).inv harg |>.congr_of_eventuallyEq heq

theorem floorBoundaryKernel_eq_one_of_abs_le_inv (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : |t| ≤ 1 / 2) (hcut : |t| ≤ 1 / (M : ℝ)) :
    floorBoundaryKernel M hM t = 1 := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hprodle : (M : ℝ) * |t| ≤ 1 := by
    simpa [mul_comm] using (le_div_iff₀ hMpos).mp hcut
  rw [floorBoundaryKernel_eq_min_of_abs_le_half M hM ht]
  by_cases ht0 : t = 0
  · simp [ht0]
  · rw [if_neg ht0]
    apply min_eq_left
    apply (one_le_inv₀ (mul_pos hMpos (abs_pos.mpr ht0))).2
    exact hprodle

theorem floorBoundaryKernel_eq_inv_on_pos_tail (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (htlo : 1 / (M : ℝ) ≤ t) (hthi : t ≤ 1 / 2) :
    floorBoundaryKernel M hM t = ((M : ℝ) * t)⁻¹ := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have htpos : 0 ≤ t := le_trans (le_of_lt (by positivity)) htlo
  rw [floorBoundaryKernel_eq_piecewise_pos M hM htpos hthi]
  by_cases hcut : t ≤ 1 / (M : ℝ)
  · have heq : t = 1 / (M : ℝ) := le_antisymm hcut htlo
    rw [if_pos hcut, heq]
    simp [hMpos.ne']
  · rw [if_neg hcut]

theorem floorBoundaryKernel_eq_neg_inv_on_neg_tail (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (htlo : -(1 / 2 : ℝ) ≤ t)
    (hthi : t ≤ -(1 / (M : ℝ))) :
    floorBoundaryKernel M hM t = -((M : ℝ) * t)⁻¹ := by
  have hInvpos : 0 < 1 / (M : ℝ) := by positivity
  have htAbs : |t| ≤ 1 / 2 := (abs_le).2 ⟨htlo, by linarith [hthi, hInvpos]⟩
  rw [floorBoundaryKernel_even_of_abs_le_half M hM htAbs]
  have hposlo : 1 / (M : ℝ) ≤ -t := by linarith
  have hposhi : -t ≤ 1 / 2 := by linarith [htlo]
  rw [floorBoundaryKernel_eq_inv_on_pos_tail M hM hposlo hposhi]
  simp [mul_neg, inv_neg]

theorem floorBoundaryKernel_continuousOn_pos_tail (M : ℕ) (hM : 2 ≤ M) :
    ContinuousOn (fun t => floorBoundaryKernel M hM t)
      (Set.Icc (1 / (M : ℝ)) (1 / 2)) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have heq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
      (fun t => ((M : ℝ) * t)⁻¹) (Set.Icc (1 / (M : ℝ)) (1 / 2)) := by
    intro t ht
    exact floorBoundaryKernel_eq_inv_on_pos_tail M hM ht.1 ht.2
  apply ContinuousOn.congr ?_ heq
  apply (continuousOn_const.mul continuousOn_id).inv₀
  intro t ht
  exact ne_of_gt (mul_pos hMpos (lt_of_lt_of_le (by positivity) ht.1))

theorem floorBoundaryKernel_continuousOn_center (M : ℕ) (hM : 2 ≤ M) :
    ContinuousOn (fun t => floorBoundaryKernel M hM t)
      (Set.Icc (-(1 / (M : ℝ))) (1 / (M : ℝ))) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have heq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
      (fun _ => (1 : ℝ)) (Set.Icc (-(1 / (M : ℝ))) (1 / (M : ℝ))) := by
    intro t ht
    have hcut : |t| ≤ 1 / (M : ℝ) := (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
    have hhalf : |t| ≤ 1 / 2 := by
      apply le_trans hcut
      exact one_div_le_one_div_of_le zero_lt_two (by exact_mod_cast hM)
    exact floorBoundaryKernel_eq_one_of_abs_le_inv M hM hhalf hcut
  exact ContinuousOn.congr continuousOn_const heq

theorem floorBoundaryKernel_continuousOn_neg_tail (M : ℕ) (hM : 2 ≤ M) :
    ContinuousOn (fun t => floorBoundaryKernel M hM t)
      (Set.Icc (-(1 / 2 : ℝ)) (-(1 / (M : ℝ)))) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have heq : Set.EqOn (fun t => floorBoundaryKernel M hM t)
      (fun t => -((M : ℝ) * t)⁻¹)
      (Set.Icc (-(1 / 2 : ℝ)) (-(1 / (M : ℝ)))) := by
    intro t ht
    exact floorBoundaryKernel_eq_neg_inv_on_neg_tail M hM ht.1 ht.2
  apply ContinuousOn.congr ?_ heq
  exact (continuousOn_const.mul continuousOn_id).inv₀
    (fun t ht => by
      rcases ht with ⟨_, ht⟩
      have hInvpos : 0 < 1 / (M : ℝ) := by positivity
      have htneg : t < 0 := lt_of_le_of_lt ht (neg_lt_zero.mpr hInvpos)
      exact ne_of_lt (mul_neg_of_pos_of_neg hMpos htneg)) |>.neg

theorem floorBoundaryKernel_continuousOn_centered_period (M : ℕ) (hM : 2 ≤ M) :
    ContinuousOn (fun t => floorBoundaryKernel M hM t)
      (Set.Icc (-1 / 2 : ℝ) (1 / 2)) := by
  let b : ℝ := 1 / (M : ℝ)
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hbhalf : b ≤ 1 / 2 := by
    dsimp [b]
    apply one_div_le_one_div_of_le zero_lt_two
    exact_mod_cast hM
  have hneg : ContinuousOn (fun t => floorBoundaryKernel M hM t)
      (Set.Icc (-1 / 2 : ℝ) (-b)) := by
    convert floorBoundaryKernel_continuousOn_neg_tail M hM using 1 <;> norm_num [b]
  have hcenter : ContinuousOn (fun t => floorBoundaryKernel M hM t)
      (Set.Icc (-b) b) := by
    simpa [b] using floorBoundaryKernel_continuousOn_center M hM
  have hpos : ContinuousOn (fun t => floorBoundaryKernel M hM t)
      (Set.Icc b (1 / 2 : ℝ)) := by
    simpa [b] using floorBoundaryKernel_continuousOn_pos_tail M hM
  have hnegCenterSet :
      Set.Icc (-1 / 2 : ℝ) (-b) ∪ Set.Icc (-b) b = Set.Icc (-1 / 2) b := by
    ext t
    simp only [Set.mem_union, Set.mem_Icc]
    constructor
    · rintro (⟨ha, ht⟩ | ⟨ht, hb⟩) <;> constructor <;> linarith
    · rintro ⟨ha, ht⟩
      by_cases h : t ≤ -b
      · exact Or.inl ⟨ha, h⟩
      · exact Or.inr ⟨by linarith, ht⟩
  have hleft : ContinuousOn (fun t => floorBoundaryKernel M hM t)
      (Set.Icc (-1 / 2 : ℝ) b) := by
    rw [← hnegCenterSet]
    exact hneg.union_of_isClosed hcenter isClosed_Icc isClosed_Icc
  have hwholeSet :
      Set.Icc (-1 / 2 : ℝ) b ∪ Set.Icc b (1 / 2) = Set.Icc (-1 / 2) (1 / 2) := by
    ext t
    simp only [Set.mem_union, Set.mem_Icc]
    constructor
    · rintro (⟨ha, ht⟩ | ⟨ht, hb⟩) <;> constructor <;> linarith
    · rintro ⟨ha, ht⟩
      by_cases h : t ≤ b
      · exact Or.inl ⟨ha, h⟩
      · exact Or.inr ⟨by linarith, ht⟩
  rw [← hwholeSet]
  exact hleft.union_of_isClosed hpos isClosed_Icc isClosed_Icc

local instance boundaryKernelPeriodPos :
    Fact (0 < (1 / 2 : ℝ) - (-1 / 2 : ℝ)) := ⟨by norm_num⟩

noncomputable def boundaryKernelCircleFunction (M : ℕ) (hM : 2 ≤ M) :
    ContinuousMap (AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) ℂ := by
  letI : Fact (0 < (1 / 2 : ℝ) - (-1 / 2 : ℝ)) := ⟨by norm_num⟩
  refine ⟨AddCircle.liftIoc ((1 / 2 : ℝ) - (-1 / 2 : ℝ)) (-1 / 2 : ℝ)
      (fun t => (floorBoundaryKernel M hM t : ℂ)), ?_⟩
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hleft : floorBoundaryKernel M hM (-1 / 2 : ℝ) = 2 / (M : ℝ) := by
    rw [floorBoundaryKernel_eq_neg_inv_on_neg_tail M hM (by norm_num)
      (by
        have hMle : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        have hinv : (1 : ℝ) / (M : ℝ) ≤ 1 / 2 :=
          one_div_le_one_div_of_le zero_lt_two hMle
        have hneg : -(1 / 2 : ℝ) ≤ -(1 / (M : ℝ)) := neg_le_neg hinv
        convert hneg using 1 <;> ring)]
    field_simp [hMpos.ne']
    <;> ring
  have hright : floorBoundaryKernel M hM (1 / 2 : ℝ) = 2 / (M : ℝ) := by
    rw [floorBoundaryKernel_eq_inv_on_pos_tail M hM
      (by
        have hMle : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        exact one_div_le_one_div_of_le zero_lt_two hMle)
      (by norm_num)]
    field_simp [hMpos.ne']
    <;> ring
  have hend :
      (fun t => (floorBoundaryKernel M hM t : ℂ)) (-1 / 2) =
        (fun t => (floorBoundaryKernel M hM t : ℂ))
          ((-1 / 2 : ℝ) + ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) := by
    rw [show (-1 / 2 : ℝ) + ((1 / 2 : ℝ) - (-1 / 2 : ℝ)) = 1 / 2 by ring]
    change (floorBoundaryKernel M hM (-1 / 2 : ℝ) : ℂ) =
      (floorBoundaryKernel M hM (1 / 2 : ℝ) : ℂ)
    rw [hleft, hright]
  have hcontReal := floorBoundaryKernel_continuousOn_centered_period M hM
  have hcont : ContinuousOn
      (fun t => (floorBoundaryKernel M hM t : ℂ))
      (Set.Icc (-1 / 2 : ℝ) (1 / 2)) :=
    Complex.continuous_ofReal.comp_continuousOn hcontReal
  have hcont' : ContinuousOn
      (fun t => (floorBoundaryKernel M hM t : ℂ))
      (Set.Icc (-1 / 2 : ℝ)
        ((-1 / 2 : ℝ) + ((1 / 2 : ℝ) - (-1 / 2 : ℝ)))) := by
    have hendpoint :
        (-1 / 2 : ℝ) + ((1 / 2 : ℝ) - (-1 / 2 : ℝ)) = 1 / 2 := by ring
    simpa only [hendpoint] using hcont
  exact AddCircle.liftIoc_continuous hend hcont'

theorem boundaryKernelFourierCoefficient_eq_circle_fourierCoeff (M : ℕ)
    (hM : 2 ≤ M) (h : ℤ) :
    boundaryKernelFourierCoefficient M hM h =
      fourierCoeff (boundaryKernelCircleFunction M hM) h := by
  letI : Fact (0 < (1 / 2 : ℝ) - (-1 / 2 : ℝ)) := ⟨by norm_num⟩
  rw [boundaryKernelFourierCoefficient]
  change fourierCoeff
      (AddCircle.liftIoc ((1 / 2 : ℝ) - (-1 / 2 : ℝ)) (-1 / 2 : ℝ)
        (fun t => (floorBoundaryKernel M hM t : ℂ))) h =
    fourierCoeff (boundaryKernelCircleFunction M hM) h
  rfl

theorem boundaryKernelFourierCoefficient_split (M : ℕ) (hM : 2 ≤ M)
    (h : ℤ) :
    boundaryKernelFourierCoefficient M hM h =
      (∫ t in (-1 / 2 : ℝ)..(-(1 / (M : ℝ))),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) +
      (∫ t in (-(1 / (M : ℝ)))..(1 / (M : ℝ)),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) +
      (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) := by
  have hMle : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : 0 < (M : ℝ) := by positivity
  have hpos : 1 / (M : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le zero_lt_two hMle
  have hneg : -(1 / 2 : ℝ) ≤ -(1 / (M : ℝ)) := by linarith
  have hcenterOrder : -(1 / (M : ℝ)) ≤ 1 / (M : ℝ) := by
    have hInvpos : 0 < 1 / (M : ℝ) := by positivity
    linarith
  have hFneg : ContinuousOn (fun t : ℝ => (floorBoundaryKernel M hM t : ℂ))
      (Set.Icc (-(1 / 2 : ℝ)) (-(1 / (M : ℝ)))) :=
    Complex.continuous_ofReal.comp_continuousOn
      (floorBoundaryKernel_continuousOn_neg_tail M hM)
  have hFcenter : ContinuousOn (fun t : ℝ => (floorBoundaryKernel M hM t : ℂ))
      (Set.Icc (-(1 / (M : ℝ))) (1 / (M : ℝ))) :=
    Complex.continuous_ofReal.comp_continuousOn
      (floorBoundaryKernel_continuousOn_center M hM)
  have hFpos : ContinuousOn (fun t : ℝ => (floorBoundaryKernel M hM t : ℂ))
      (Set.Icc (1 / (M : ℝ)) (1 / 2 : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (floorBoundaryKernel_continuousOn_pos_tail M hM)
  have hleft := intervalIntegrable_boundaryKernelFourierIntegrand_of_continuousOn
    M hM h _ _ hneg hFneg
  have hcenter := intervalIntegrable_boundaryKernelFourierIntegrand_of_continuousOn
    M hM h _ _ hcenterOrder hFcenter
  have hright := intervalIntegrable_boundaryKernelFourierIntegrand_of_continuousOn
    M hM h _ _ hpos hFpos
  have hfirst := intervalIntegral.integral_add_adjacent_intervals hleft hcenter
  have hsecond := intervalIntegral.integral_add_adjacent_intervals
    (hleft.trans hcenter) hright
  have hfirst' :
      (∫ t in (-1 / 2 : ℝ)..(-(1 / (M : ℝ))),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) +
      (∫ t in (-(1 / (M : ℝ)))..(1 / (M : ℝ)),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) =
      ∫ t in (-1 / 2 : ℝ)..(1 / (M : ℝ)),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ) := by
    convert hfirst using 1 <;> norm_num
  have hsecond' :
      (∫ t in (-1 / 2 : ℝ)..(1 / (M : ℝ)),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) +
      (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) =
      ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ) := by
    convert hsecond using 1 <;> norm_num
  rw [boundaryKernelFourierCoefficient_eq_integral]
  simp only [one_smul]
  calc
    (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) =
        (∫ t in (-1 / 2 : ℝ)..(1 / (M : ℝ)),
          fourier (-h) (t : AddCircle (1 : ℝ)) •
            (floorBoundaryKernel M hM t : ℂ)) +
        (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
          fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) := hsecond'.symm
    _ = ((∫ t in (-1 / 2 : ℝ)..(-(1 / (M : ℝ))),
          fourier (-h) (t : AddCircle (1 : ℝ)) •
            (floorBoundaryKernel M hM t : ℂ)) +
        (∫ t in (-(1 / (M : ℝ)))..(1 / (M : ℝ)),
          fourier (-h) (t : AddCircle (1 : ℝ)) •
            (floorBoundaryKernel M hM t : ℂ))) +
        (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
          fourier (-h) (t : AddCircle (1 : ℝ)) •
          (floorBoundaryKernel M hM t : ℂ)) := by rw [hfirst']

theorem intervalIntegrable_floorBoundaryKernel_derivative_center (M : ℕ)
    (hM : 2 ≤ M) :
    IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (-(1 / (M : ℝ))) (1 / (M : ℝ)) := by
  letI : MeasureTheory.IsLocallyFiniteMeasure
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    Real.locallyFinite_volume
  exact continuousOn_const.intervalIntegrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))

theorem intervalIntegrable_floorBoundaryKernel_derivative_pos (M : ℕ)
    (hM : 2 ≤ M) :
    IntervalIntegrable
      (fun t : ℝ => -(M : ℝ) / ((M : ℝ) * t) ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (1 / (M : ℝ)) (1 / 2) := by
  letI : MeasureTheory.IsLocallyFiniteMeasure
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    Real.locallyFinite_volume
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMle : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hle : 1 / (M : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le zero_lt_two hMle
  have hlin : ContinuousOn (fun t : ℝ => (M : ℝ) * t)
      (Set.Icc (1 / (M : ℝ)) (1 / 2)) :=
    continuousOn_const.mul continuousOn_id
  have hden : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 2)
      (Set.Icc (1 / (M : ℝ)) (1 / 2)) := hlin.pow 2
  have hden_ne : ∀ t ∈ Set.Icc (1 / (M : ℝ)) (1 / 2),
      ((M : ℝ) * t) ^ 2 ≠ 0 := by
    intro t ht
    apply pow_ne_zero
    exact ne_of_gt (mul_pos hMpos (lt_of_lt_of_le (by positivity) ht.1))
  have hcont : ContinuousOn
      (fun t : ℝ => -(M : ℝ) / ((M : ℝ) * t) ^ 2)
      (Set.Icc (1 / (M : ℝ)) (1 / 2)) :=
    continuousOn_const.neg.div hden hden_ne
  exact hcont.intervalIntegrable_of_Icc
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hle

theorem intervalIntegrable_floorBoundaryKernel_derivative_neg (M : ℕ)
    (hM : 2 ≤ M) :
    IntervalIntegrable
      (fun t : ℝ => (M : ℝ) / ((M : ℝ) * t) ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (-(1 / 2 : ℝ)) (-(1 / (M : ℝ))) := by
  letI : MeasureTheory.IsLocallyFiniteMeasure
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    Real.locallyFinite_volume
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMle : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hle : -(1 / 2 : ℝ) ≤ -(1 / (M : ℝ)) := by
    have h := one_div_le_one_div_of_le zero_lt_two hMle
    linarith
  have hlin : ContinuousOn (fun t : ℝ => (M : ℝ) * t)
      (Set.Icc (-(1 / 2 : ℝ)) (-(1 / (M : ℝ)))) :=
    continuousOn_const.mul continuousOn_id
  have hden : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 2)
      (Set.Icc (-(1 / 2 : ℝ)) (-(1 / (M : ℝ)))) := hlin.pow 2
  have hden_ne : ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / (M : ℝ))),
      ((M : ℝ) * t) ^ 2 ≠ 0 := by
    intro t ht
    apply pow_ne_zero
    exact ne_of_lt (mul_neg_of_pos_of_neg hMpos
      (lt_of_le_of_lt ht.2 (neg_lt_zero.mpr (by positivity))))
  have hcont : ContinuousOn
      (fun t : ℝ => (M : ℝ) / ((M : ℝ) * t) ^ 2)
      (Set.Icc (-(1 / 2 : ℝ)) (-(1 / (M : ℝ)))) :=
    continuousOn_const.div hden hden_ne
  exact hcont.intervalIntegrable_of_Icc
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hle

theorem floorBoundaryKernel_hasDerivAt_center (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (htlower : -(1 / (M : ℝ)) < t)
    (hthigh : t < 1 / (M : ℝ)) :
    HasDerivAt (fun y => floorBoundaryKernel M hM y) 0 t := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hcutHalf : 1 / (M : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le zero_lt_two hMge
  have hmem : ∀ᶠ y : ℝ in nhds t,
      y ∈ Set.Ioo (-(1 / (M : ℝ))) (1 / (M : ℝ)) :=
    isOpen_Ioo.mem_nhds ⟨htlower, hthigh⟩
  have heq : (fun y => floorBoundaryKernel M hM y) =ᶠ[nhds t]
      (fun _ => (1 : ℝ)) := hmem.mono fun y hy => by
    change floorBoundaryKernel M hM y = 1
    have hyabs : |y| ≤ 1 / (M : ℝ) := (abs_le).2 ⟨hy.1.le, hy.2.le⟩
    have hyhalf : |y| ≤ 1 / 2 := le_trans hyabs hcutHalf
    exact floorBoundaryKernel_eq_one_of_abs_le_inv M hM hyhalf hyabs
  exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq

theorem floorBoundaryKernel_hasDerivAt_neg_tail (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (htlow : -(1 / 2 : ℝ) < t)
    (hthigh : t < -(1 / (M : ℝ))) :
    HasDerivAt (fun y => floorBoundaryKernel M hM y)
      ((M : ℝ) / ((M : ℝ) * t) ^ 2) t := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hmem : ∀ᶠ y : ℝ in nhds t,
      y ∈ Set.Ioo (-(1 / 2 : ℝ)) (-(1 / (M : ℝ))) :=
    isOpen_Ioo.mem_nhds ⟨htlow, hthigh⟩
  have heq : (fun y => floorBoundaryKernel M hM y) =ᶠ[nhds t]
      (fun y => -((M : ℝ) * y)⁻¹) := hmem.mono fun y hy => by
    change floorBoundaryKernel M hM y = -((M : ℝ) * y)⁻¹
    have hinvpos : 0 < 1 / (M : ℝ) := by positivity
    have hyabs : |y| ≤ 1 / 2 := by
      rw [abs_le]
      constructor
      · linarith [hy.1]
      · linarith [hy.2, hinvpos]
    have hypos : 0 ≤ -y := by linarith [hy.2, hinvpos]
    have hyupper : -y ≤ 1 / 2 := by linarith [hy.1]
    rw [floorBoundaryKernel_even_of_abs_le_half M hM hyabs,
      floorBoundaryKernel_eq_piecewise_pos M hM hypos hyupper]
    have hcut : ¬ -y ≤ 1 / (M : ℝ) := by linarith [hy.2]
    rw [if_neg hcut]
    simp [mul_neg, inv_neg]
  have harg : (M : ℝ) * t ≠ 0 := by
    have htneg : t < 0 := by
      have hinvpos : 0 < 1 / (M : ℝ) := by positivity
      linarith [hthigh, hinvpos]
    exact ne_of_lt (mul_neg_of_pos_of_neg hMpos htneg)
  have hmodel : HasDerivAt (fun y : ℝ => -((M : ℝ) * y)⁻¹)
      ((M : ℝ) / ((M : ℝ) * t) ^ 2) t := by
    have h := ((hasDerivAt_const_mul (M : ℝ) (x := t)).inv harg).neg
    convert h using 1 <;> ring
  exact hmodel.congr_of_eventuallyEq heq

theorem boundaryKernelFourierTail_pos_ibp (M : ℕ) (hM : 2 ≤ M)
    {a b : ℝ} (hab : a ≤ b) (ha : 1 / (M : ℝ) ≤ a)
    (hb : b ≤ 1 / 2) {h : ℤ} (hh : h ≠ 0) :
    (∫ t in a..b, (floorBoundaryKernel M hM t : ℂ) *
      fourier (-h) (t : AddCircle (1 : ℝ))) =
      (floorBoundaryKernel M hM b : ℂ) *
          (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
            fourier (-h) (b : AddCircle (1 : ℝ))) -
        (floorBoundaryKernel M hM a : ℂ) *
          (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
            fourier (-h) (a : AddCircle (1 : ℝ))) -
        (∫ t in a..b,
          ((-(M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ) *
            (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
              fourier (-h) (t : AddCircle (1 : ℝ)))) := by
  let f : ℝ → ℂ := fun t => (floorBoundaryKernel M hM t : ℂ)
  let g : ℝ → ℂ := fun t =>
    ((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
      fourier (-h) (t : AddCircle (1 : ℝ))
  let f' : ℝ → ℂ := fun t =>
    ((-(M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ)
  let g' : ℝ → ℂ := fun t => fourier (-h) (t : AddCircle (1 : ℝ))
  letI : MeasureTheory.IsLocallyFiniteMeasure
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := Real.locallyFinite_volume
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hFcont : ContinuousOn f (Set.Icc a b) := by
    apply (Complex.continuous_ofReal.comp_continuousOn
      (floorBoundaryKernel_continuousOn_pos_tail M hM)).mono
    intro t ht
    exact ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  have hFcontU : ContinuousOn f (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hFcont
  have hGcont : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact continuousOn_const.mul
      (((map_continuous (fourier (-h))).comp
        (AddCircle.continuous_mk' (1 : ℝ))).continuousOn)
  have hGcontU : ContinuousOn g (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hGcont
  have hFderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt f (f' x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := by
      simpa [min_eq_left hab, max_eq_right hab] using hx
    dsimp [f, f']
    apply HasDerivAt.ofReal_comp
    exact floorBoundaryKernel_hasDerivAt_pos_tail M hM
      (lt_of_le_of_lt ha hx'.1) (lt_of_lt_of_le hx'.2 hb)
  have hT : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hGderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt g (g' x) x := by
    intro x _
    change HasDerivAt
      (fun t : ℝ => ((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
        fourier (-h) (t : AddCircle (1 : ℝ)))
      (fourier (-h) (x : AddCircle (1 : ℝ))) x
    exact has_antideriv_at_fourier_neg hT hh x
  have hlin : ContinuousOn (fun t : ℝ => (M : ℝ) * t) (Set.Icc a b) :=
    continuousOn_const.mul continuousOn_id
  have hden : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 2) (Set.Icc a b) :=
    hlin.pow 2
  have hden_ne : ∀ t ∈ Set.Icc a b, ((M : ℝ) * t) ^ 2 ≠ 0 := by
    intro t ht
    apply pow_ne_zero
    exact ne_of_gt (mul_pos hMpos
      (lt_of_lt_of_le (by positivity) (le_trans ha ht.1)))
  have hf'cont : ContinuousOn f' (Set.Icc a b) := by
    dsimp [f']
    exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.neg.div hden hden_ne)
  have hf'int : IntervalIntegrable f'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b :=
    hf'cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  have hg'cont : ContinuousOn g' (Set.Icc a b) := by
    dsimp [g']
    exact ((map_continuous (fourier (-h))).comp
      (AddCircle.continuous_mk' (1 : ℝ))).continuousOn
  have hg'int : IntervalIntegrable g'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b :=
    hg'cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hFcontU hGcontU hFderiv hGderiv hf'int hg'int

theorem boundaryKernelFourierCenter_ibp (M : ℕ) (hM : 2 ≤ M)
    {h : ℤ} (hh : h ≠ 0) :
    (∫ t in (-(1 / (M : ℝ)))..(1 / (M : ℝ)),
      (floorBoundaryKernel M hM t : ℂ) *
        fourier (-h) (t : AddCircle (1 : ℝ))) =
      (floorBoundaryKernel M hM (1 / (M : ℝ)) : ℂ) *
          (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
            fourier (-h) (((1 / (M : ℝ) : ℝ) : AddCircle (1 : ℝ)))) -
        (floorBoundaryKernel M hM (-(1 / (M : ℝ))) : ℂ) *
          (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
            fourier (-h) ((-(1 / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ))) := by
  let a : ℝ := -(1 / (M : ℝ))
  let b : ℝ := 1 / (M : ℝ)
  let f : ℝ → ℂ := fun t => (floorBoundaryKernel M hM t : ℂ)
  let g : ℝ → ℂ := fun t =>
    ((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
      fourier (-h) (t : AddCircle (1 : ℝ))
  let f' : ℝ → ℂ := fun _ => 0
  let g' : ℝ → ℂ := fun t => fourier (-h) (t : AddCircle (1 : ℝ))
  letI : MeasureTheory.IsLocallyFiniteMeasure
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := Real.locallyFinite_volume
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hInvpos : 0 < 1 / (M : ℝ) := by positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hFcont : ContinuousOn f (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    dsimp [a, b, f]
    exact Complex.continuous_ofReal.comp_continuousOn
      (floorBoundaryKernel_continuousOn_center M hM)
  have hGcont : ContinuousOn g (Set.uIcc a b) := by
    dsimp [g]
    exact continuousOn_const.mul
      (((map_continuous (fourier (-h))).comp
        (AddCircle.continuous_mk' (1 : ℝ))).continuousOn)
  have hFderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt f (f' x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := by
      simpa [min_eq_left hab, max_eq_right hab] using hx
    dsimp [a, b] at hx'
    dsimp [f, f']
    apply HasDerivAt.ofReal_comp
    exact floorBoundaryKernel_hasDerivAt_center M hM hx'.1 hx'.2
  have hT : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hGderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt g (g' x) x := by
    intro x _
    change HasDerivAt
      (fun t : ℝ => ((1 : ℝ) : ℂ) /
        (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
          fourier (-h) (t : AddCircle (1 : ℝ)))
      (fourier (-h) (x : AddCircle (1 : ℝ))) x
    exact has_antideriv_at_fourier_neg hT hh x
  have hf'int : IntervalIntegrable f'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
    dsimp [f']
    exact continuousOn_const.intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) hab
  have hg'cont : ContinuousOn g' (Set.Icc a b) := by
    dsimp [g']
    exact ((map_continuous (fourier (-h))).comp
      (AddCircle.continuous_mk' (1 : ℝ))).continuousOn
  have hg'int : IntervalIntegrable g'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b :=
    hg'cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hFcont hGcont hFderiv hGderiv hf'int hg'int
  simpa only [a, b, f, f', g, g', zero_mul,
    intervalIntegral.integral_zero, sub_zero] using hparts

theorem boundaryKernelFourierTail_neg_ibp (M : ℕ) (hM : 2 ≤ M)
    {a b : ℝ} (hab : a ≤ b) (ha : -(1 / 2 : ℝ) ≤ a)
    (hb : b ≤ -(1 / (M : ℝ))) {h : ℤ} (hh : h ≠ 0) :
    (∫ t in a..b, (floorBoundaryKernel M hM t : ℂ) *
      fourier (-h) (t : AddCircle (1 : ℝ))) =
      (floorBoundaryKernel M hM b : ℂ) *
          (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
            fourier (-h) (b : AddCircle (1 : ℝ))) -
        (floorBoundaryKernel M hM a : ℂ) *
          (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
            fourier (-h) (a : AddCircle (1 : ℝ))) -
        (∫ t in a..b,
          (((M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ) *
            (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
              fourier (-h) (t : AddCircle (1 : ℝ)))) := by
  let f : ℝ → ℂ := fun t => (floorBoundaryKernel M hM t : ℂ)
  let g : ℝ → ℂ := fun t =>
    ((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
      fourier (-h) (t : AddCircle (1 : ℝ))
  let f' : ℝ → ℂ := fun t => (((M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ)
  let g' : ℝ → ℂ := fun t => fourier (-h) (t : AddCircle (1 : ℝ))
  letI : MeasureTheory.IsLocallyFiniteMeasure
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := Real.locallyFinite_volume
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hInvpos : 0 < 1 / (M : ℝ) := by positivity
  have hFcont : ContinuousOn f (Set.uIcc a b) := by
    have hcont := (Complex.continuous_ofReal.comp_continuousOn
      (floorBoundaryKernel_continuousOn_neg_tail M hM)).mono
        (show Set.Icc a b ⊆ Set.Icc (-(1 / 2 : ℝ)) (-(1 / (M : ℝ))) from
          fun t ht => ⟨le_trans ha ht.1, le_trans ht.2 hb⟩)
    rw [Set.uIcc_of_le hab]
    exact hcont
  have hGcont : ContinuousOn g (Set.uIcc a b) := by
    dsimp [g]
    exact continuousOn_const.mul
      (((map_continuous (fourier (-h))).comp
        (AddCircle.continuous_mk' (1 : ℝ))).continuousOn)
  have hFderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt f (f' x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := by
      simpa [min_eq_left hab, max_eq_right hab] using hx
    dsimp [f, f']
    apply HasDerivAt.ofReal_comp
    exact floorBoundaryKernel_hasDerivAt_neg_tail M hM
      (lt_of_le_of_lt ha hx'.1) (lt_of_lt_of_le hx'.2 hb)
  have hT : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hGderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt g (g' x) x := by
    intro x _
    change HasDerivAt
      (fun t : ℝ => ((1 : ℝ) : ℂ) /
        (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
          fourier (-h) (t : AddCircle (1 : ℝ)))
      (fourier (-h) (x : AddCircle (1 : ℝ))) x
    exact has_antideriv_at_fourier_neg hT hh x
  have hlin : ContinuousOn (fun t : ℝ => (M : ℝ) * t) (Set.Icc a b) :=
    continuousOn_const.mul continuousOn_id
  have hden : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 2) (Set.Icc a b) :=
    hlin.pow 2
  have hden_ne : ∀ t ∈ Set.Icc a b, ((M : ℝ) * t) ^ 2 ≠ 0 := by
    intro t ht
    apply pow_ne_zero
    have htneg : t < 0 := by
      have hInvneg : -(1 / (M : ℝ)) < 0 := neg_lt_zero.mpr hInvpos
      exact lt_of_le_of_lt (le_trans ht.2 hb) hInvneg
    exact ne_of_lt (mul_neg_of_pos_of_neg hMpos htneg)
  have hf'cont : ContinuousOn f' (Set.Icc a b) := by
    dsimp [f']
    exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.div hden hden_ne)
  have hf'int : IntervalIntegrable f'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b :=
    hf'cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  have hg'cont : ContinuousOn g' (Set.Icc a b) := by
    dsimp [g']
    exact ((map_continuous (fourier (-h))).comp
      (AddCircle.continuous_mk' (1 : ℝ))).continuousOn
  have hg'int : IntervalIntegrable g'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b :=
    hg'cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hFcont hGcont hFderiv hGderiv hf'int hg'int

theorem boundaryKernelFourierCoefficient_derivative_formula (M : ℕ)
    (hM : 2 ≤ M) {h : ℤ} (hh : h ≠ 0) :
    boundaryKernelFourierCoefficient M hM h =
      -(∫ t in (-(1 / 2 : ℝ))..(-(1 / (M : ℝ))),
        (((M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ) *
          (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
            fourier (-h) (t : AddCircle (1 : ℝ)))) -
      (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
        ((-(M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ) *
          (((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
            fourier (-h) (t : AddCircle (1 : ℝ)))) := by
  have hsplit := boundaryKernelFourierCoefficient_split M hM h
  have hMle : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hposOrder : 1 / (M : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le zero_lt_two hMle
  have hnegOrder : -(1 / 2 : ℝ) ≤ -(1 / (M : ℝ)) := by linarith
  have hneg := boundaryKernelFourierTail_neg_ibp M hM hnegOrder le_rfl le_rfl hh
  have hcenter := boundaryKernelFourierCenter_ibp M hM hh
  have hpos := boundaryKernelFourierTail_pos_ibp M hM hposOrder le_rfl le_rfl hh
  let g : ℝ → ℂ := fun t =>
    ((1 : ℝ) : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
      fourier (-h) (t : AddCircle (1 : ℝ))
  have hsplit' : boundaryKernelFourierCoefficient M hM h =
      (∫ t in (-(1 / 2 : ℝ))..(-(1 / (M : ℝ))),
        (floorBoundaryKernel M hM t : ℂ) *
          fourier (-h) (t : AddCircle (1 : ℝ))) +
      (∫ t in (-(1 / (M : ℝ)))..(1 / (M : ℝ)),
        (floorBoundaryKernel M hM t : ℂ) *
          fourier (-h) (t : AddCircle (1 : ℝ))) +
      (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
        (floorBoundaryKernel M hM t : ℂ) *
          fourier (-h) (t : AddCircle (1 : ℝ))) := by
    convert (by simpa only [smul_eq_mul, mul_comm] using
      (boundaryKernelFourierCoefficient_split M hM h)) using 1 <;> norm_num
  have hFend : floorBoundaryKernel M hM (-(1 / 2 : ℝ)) =
      floorBoundaryKernel M hM (1 / 2 : ℝ) := by
    have heven := floorBoundaryKernel_even_of_abs_le_half M hM
      (t := -(1 / 2 : ℝ)) (by norm_num)
    convert heven using 1 <;> norm_num
  have hcircle : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) =
      -((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
    convert AddCircle.coe_add_period (1 : ℝ) (-(1 / 2 : ℝ)) using 1 <;> norm_num
  have hphaseEnd : @fourier (1 : ℝ) (-h)
      ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) =
      @fourier (1 : ℝ) (-h)
        (-((1 / 2 : ℝ) : AddCircle (1 : ℝ))) :=
    congrArg (@fourier (1 : ℝ) (-h)) hcircle
  rw [hsplit', hneg, hcenter, hpos]
  rw [← hFend, hphaseEnd]
  simp only [AddCircle.coe_neg]
  ring_nf

theorem boundaryKernelFourier_derivative_periodic_jump (M : ℕ)
    (hM : 2 ≤ M) :
    -(M : ℝ) / ((M : ℝ) * (1 / 2 : ℝ)) ^ 2 -
        (M : ℝ) / ((M : ℝ) * (-(1 / 2 : ℝ))) ^ 2 =
      -(8 / (M : ℝ)) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  field_simp
  <;> ring

theorem boundaryKernelFourier_outer_endpoint_coefficient (M : ℕ)
    (hM : 2 ≤ M) :
    (M : ℝ) / ((M : ℝ) * (-(1 / 2 : ℝ))) ^ 2 -
        (-(M : ℝ) / ((M : ℝ) * (1 / 2 : ℝ)) ^ 2) =
      8 / (M : ℝ) := by
  have h := boundaryKernelFourier_derivative_periodic_jump M hM
  linarith

theorem boundaryKernelFourier_outerCharacters_eq {h : ℤ} :
    fourier (-h) ((-(1 / 2 : ℝ)) : AddCircle (1 : ℝ)) =
      fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  have hc : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) =
      ((-(1 / 2 : ℝ)) : AddCircle (1 : ℝ)) := by
    calc
      ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) =
          (((-(1 / 2 : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ)) := by
            congr 1 <;> norm_num
      _ = ((-(1 / 2 : ℝ)) : AddCircle (1 : ℝ)) :=
        AddCircle.coe_add_period (p := (1 : ℝ)) (x := -(1 / 2 : ℝ))
  exact congrArg (fourier (-h)) hc.symm

theorem boundaryKernelFourier_outer_endpoint_terms_eq (M : ℕ)
    (hM : 2 ≤ M) (h : ℤ) (c : ℂ) :
    (((M : ℝ) / ((M : ℝ) * (-(1 / 2 : ℝ))) ^ 2 : ℝ) : ℂ) *
        (c * (c * fourier (-h) ((-(1 / 2 : ℝ)) : AddCircle (1 : ℝ)))) -
      ((-(M : ℝ) / ((M : ℝ) * (1 / 2 : ℝ)) ^ 2 : ℝ) : ℂ) *
        (c * (c * fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))) =
      ((8 / (M : ℝ) : ℝ) : ℂ) *
        (c * (c * fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))) := by
  rw [boundaryKernelFourier_outerCharacters_eq]
  have hcoeff := boundaryKernelFourier_outer_endpoint_coefficient M hM
  have hcoeffC :
      (((M : ℝ) / ((M : ℝ) * (-(1 / 2 : ℝ))) ^ 2 : ℝ) : ℂ) -
        ((-(M : ℝ) / ((M : ℝ) * (1 / 2 : ℝ)) ^ 2 : ℝ) : ℂ) =
          ((8 / (M : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast hcoeff
  calc
    _ = ((((M : ℝ) / ((M : ℝ) * (-(1 / 2 : ℝ))) ^ 2 : ℝ) : ℂ) -
          ((-(M : ℝ) / ((M : ℝ) * (1 / 2 : ℝ)) ^ 2 : ℝ) : ℂ)) *
          (c * (c * fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))) := by ring
    _ = _ := by rw [hcoeffC]

theorem boundaryKernelFourier_derivative_corner_values (M : ℕ)
    (hM : 2 ≤ M) :
    (M : ℝ) / ((M : ℝ) * (-(1 / (M : ℝ)))) ^ 2 = (M : ℝ) ∧
      -(M : ℝ) / ((M : ℝ) * (1 / (M : ℝ))) ^ 2 = -(M : ℝ) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  constructor <;> field_simp <;> ring

theorem boundaryKernelFourier_endpoint_terms_eq (M : ℕ)
    (hM : 2 ≤ M) (h : ℤ) (c : ℂ) :
    - (((M : ℝ) / ((M : ℝ) * (-(1 / (M : ℝ)))) ^ 2 : ℝ) : ℂ) *
        (c * (c * @fourier (1 : ℝ) (-h)
          ((-((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))) +
      (((M : ℝ) / ((M : ℝ) * (-(1 / 2 : ℝ))) ^ 2 : ℝ) : ℂ) *
        (c * (c * fourier (-h) ((-(1 / 2 : ℝ)) : AddCircle (1 : ℝ)))) -
      ((-(M : ℝ) / ((M : ℝ) * (1 / 2 : ℝ)) ^ 2 : ℝ) : ℂ) *
        (c * (c * fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))) +
      ((-(M : ℝ) / ((M : ℝ) * (1 / (M : ℝ))) ^ 2 : ℝ) : ℂ) *
        (c * (c * @fourier (1 : ℝ) (-h)
          ((((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))) =
      - ((M : ℝ) : ℂ) *
          (c * (c * @fourier (1 : ℝ) (-h)
            ((-((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))) -
        ((M : ℝ) : ℂ) *
          (c * (c * @fourier (1 : ℝ) (-h)
            ((((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))) +
        ((8 / (M : ℝ) : ℝ) : ℂ) *
          (c * (c * fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))) := by
  have hcorner := boundaryKernelFourier_derivative_corner_values M hM
  have hnegC :
      (((M : ℝ) / ((M : ℝ) * (-(1 / (M : ℝ)))) ^ 2 : ℝ) : ℂ) =
        ((M : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hcorner.1
  have hposC :
      ((-(M : ℝ) / ((M : ℝ) * (1 / (M : ℝ))) ^ 2 : ℝ) : ℂ) =
        (-(M : ℝ) : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hcorner.2
  calc
    _ =
        - (((M : ℝ) / ((M : ℝ) * (-(1 / (M : ℝ)))) ^ 2 : ℝ) : ℂ) *
            (c * (c * @fourier (1 : ℝ) (-h)
              ((-((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))) +
          ((((M : ℝ) / ((M : ℝ) * (-(1 / 2 : ℝ))) ^ 2 : ℝ) : ℂ) *
              (c * (c * fourier (-h) ((-(1 / 2 : ℝ)) : AddCircle (1 : ℝ)))) -
            ((-(M : ℝ) / ((M : ℝ) * (1 / 2 : ℝ)) ^ 2 : ℝ) : ℂ) *
              (c * (c * fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))) +
          ((-(M : ℝ) / ((M : ℝ) * (1 / (M : ℝ))) ^ 2 : ℝ) : ℂ) *
            (c * (c * @fourier (1 : ℝ) (-h)
              ((((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ))))) := by ring
    _ = _ := by
      rw [boundaryKernelFourier_outer_endpoint_terms_eq M hM h c,
        hnegC, hposC]
      ring

theorem boundaryKernelFourier_antiderivative_scalar_norm (h : ℤ) :
    ‖((1 : ℝ) : ℂ) /
      (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))‖ =
        1 / (2 * Real.pi * |(h : ℝ)|) := by
  have hden :
      ‖-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)‖ =
        2 * Real.pi * |(h : ℝ)| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      Complex.norm_intCast, abs_of_pos Real.pi_pos]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_one, hden]

theorem boundaryKernelFourier_antiderivative_scalar_sq_bound {h : ℤ}
    (hh : h ≠ 0) :
    4 * ‖((1 : ℝ) : ℂ) /
      (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))‖ ^ 2 ≤
        1 / (h : ℝ) ^ 2 := by
  rw [boundaryKernelFourier_antiderivative_scalar_norm]
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have ha : 0 < |(h : ℝ)| := abs_pos.mpr hhR
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hden : 2 * |(h : ℝ)| ≤ 2 * Real.pi * |(h : ℝ)| := by
    nlinarith
  have hrecip : 1 / (2 * Real.pi * |(h : ℝ)|) ≤
      1 / (2 * |(h : ℝ)|) :=
    one_div_le_one_div_of_le (by positivity) hden
  have hsq :
      (1 / (2 * Real.pi * |(h : ℝ)|)) ^ 2 ≤
        (1 / (2 * |(h : ℝ)|)) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hrecip
  have hfinal : 4 * (1 / (2 * |(h : ℝ)|)) ^ 2 =
      1 / (h : ℝ) ^ 2 := by
    calc
      4 * (1 / (2 * |(h : ℝ)|)) ^ 2 =
          1 / |(h : ℝ)| ^ 2 := by
        field_simp [ha.ne']
        <;> ring
      _ = 1 / (h : ℝ) ^ 2 := by rw [sq_abs]
  nlinarith

theorem boundaryKernelFourier_pointwise_character_norm (n : ℤ)
    (t : AddCircle (1 : ℝ)) : ‖@fourier (1 : ℝ) n t‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

theorem boundaryKernelFourier_double_scalar_character_norm (h : ℤ)
    (c : ℂ) (t : AddCircle (1 : ℝ)) :
    ‖c * (c * fourier (-h) t)‖ = ‖c‖ ^ 2 := by
  have hchar : ‖fourier (-h) t‖ = 1 := by
    rw [fourier_apply, Circle.norm_coe]
  rw [norm_mul, norm_mul, hchar]
  ring

theorem boundaryKernelFourier_realScalar_double_character_norm (r : ℝ)
    (h : ℤ) (c : ℂ) (t : AddCircle (1 : ℝ)) :
    ‖(r : ℂ) * (c * (c * fourier (-h) t))‖ = |r| * ‖c‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    boundaryKernelFourier_double_scalar_character_norm]

theorem boundaryKernelFourier_secondDeriv_pos_tail (M : ℕ)
    (hM : 2 ≤ M) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => -(M : ℝ) / ((M : ℝ) * y) ^ 2)
      (2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) t := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlinear : HasDerivAt (fun y : ℝ => (M : ℝ) * y) (M : ℝ) t :=
    hasDerivAt_const_mul (M : ℝ) (x := t)
  have hsquare := hlinear.pow 2
  have harg : (M : ℝ) * t ≠ 0 := ne_of_gt (mul_pos hMpos ht)
  have hmodel := (hsquare.inv (pow_ne_zero 2 harg)).const_mul (-(M : ℝ))
  apply hmodel.congr_deriv
  norm_num
  field_simp [harg]
  <;> ring_nf

theorem boundaryKernelFourier_secondDeriv_neg_tail (M : ℕ)
    (hM : 2 ≤ M) {t : ℝ} (ht : t < 0) :
    HasDerivAt (fun y : ℝ => (M : ℝ) / ((M : ℝ) * y) ^ 2)
      (-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3)) t := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlinear : HasDerivAt (fun y : ℝ => (M : ℝ) * y) (M : ℝ) t :=
    hasDerivAt_const_mul (M : ℝ) (x := t)
  have hsquare := hlinear.pow 2
  have harg : (M : ℝ) * t ≠ 0 := ne_of_lt (mul_neg_of_pos_of_neg hMpos ht)
  have hmodel := (hsquare.inv (pow_ne_zero 2 harg)).const_mul (M : ℝ)
  apply hmodel.congr_deriv
  norm_num
  field_simp [harg]
  <;> ring_nf

theorem boundaryKernelFourier_smoothVariation_pos (M : ℕ)
    (hM : 2 ≤ M) :
    (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
      2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) =
        (M : ℝ) - 4 / (M : ℝ) := by
  let a : ℝ := 1 / (M : ℝ)
  let b : ℝ := 1 / 2
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact one_div_le_one_div_of_le zero_lt_two (by exact_mod_cast hM)
  have hdencont : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 3)
      (Set.Icc a b) :=
    (continuousOn_const.mul continuousOn_id).pow 3
  have hdenne : ∀ t ∈ Set.Icc a b, ((M : ℝ) * t) ^ 3 ≠ 0 := by
    intro t ht
    apply pow_ne_zero
    exact ne_of_gt (mul_pos hMpos (lt_of_lt_of_le ha ht.1))
  have hcont : ContinuousOn
      (fun t : ℝ => 2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3)
      (Set.Icc a b) :=
    ContinuousOn.div continuousOn_const hdencont hdenne
  have hint : IntervalIntegrable
      (fun t : ℝ => 2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3)
      MeasureTheory.volume a b := hcont.intervalIntegrable_of_Icc hab
  have hFcont : ContinuousOn
      (fun t : ℝ => -(M : ℝ) / ((M : ℝ) * t) ^ 2)
      (Set.Icc a b) := by
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_const.mul continuousOn_id).pow 2
    · intro t ht
      apply pow_ne_zero
      exact ne_of_gt (mul_pos hMpos (lt_of_lt_of_le ha ht.1))
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun y : ℝ => -(M : ℝ) / ((M : ℝ) * y) ^ 2)
        (2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) t := by
    intro t ht
    apply boundaryKernelFourier_secondDeriv_pos_tail M hM
    exact lt_trans ha ht.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab hFcont hderiv hint]
  dsimp [a, b]
  field_simp
  <;> ring

theorem boundaryKernelFourier_smoothVariation_neg (M : ℕ)
    (hM : 2 ≤ M) :
    (∫ t in (-(1 / 2 : ℝ))..(-(1 / (M : ℝ))),
      -(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3)) =
        (M : ℝ) - 4 / (M : ℝ) := by
  let a : ℝ := -(1 / 2 : ℝ)
  let b : ℝ := -(1 / (M : ℝ))
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hhalf : 1 / (M : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le zero_lt_two (by exact_mod_cast hM)
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hinvpos : 0 < 1 / (M : ℝ) := by positivity
  have hbneg : b < 0 := by dsimp [b]; exact neg_lt_zero.mpr hinvpos
  have hdencont : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 3)
      (Set.Icc a b) :=
    (continuousOn_const.mul continuousOn_id).pow 3
  have hdenne : ∀ t ∈ Set.Icc a b, ((M : ℝ) * t) ^ 3 ≠ 0 := by
    intro t ht
    apply pow_ne_zero
    have htneg : t < 0 := lt_of_le_of_lt ht.2 hbneg
    exact ne_of_lt (mul_neg_of_pos_of_neg hMpos htneg)
  have hcont : ContinuousOn
      (fun t : ℝ => -(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3))
      (Set.Icc a b) := by
    have hquot : ContinuousOn
        (fun t : ℝ => (2 * (M : ℝ) ^ 2) / ((M : ℝ) * t) ^ 3)
        (Set.Icc a b) := ContinuousOn.div continuousOn_const hdencont hdenne
    exact hquot.neg
  have hint : IntervalIntegrable
      (fun t : ℝ => -(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3))
      MeasureTheory.volume a b := hcont.intervalIntegrable_of_Icc hab
  have hFcont : ContinuousOn
      (fun t : ℝ => (M : ℝ) / ((M : ℝ) * t) ^ 2)
      (Set.Icc a b) := by
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_const.mul continuousOn_id).pow 2
    · intro t ht
      apply pow_ne_zero
      have htneg : t < 0 := lt_of_le_of_lt ht.2 hbneg
      exact ne_of_lt (mul_neg_of_pos_of_neg hMpos htneg)
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun y : ℝ => (M : ℝ) / ((M : ℝ) * y) ^ 2)
        (-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3)) t := by
    intro t ht
    apply boundaryKernelFourier_secondDeriv_neg_tail M hM
    exact lt_trans ht.2 hbneg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab hFcont hderiv hint]
  dsimp [a, b]
  field_simp
  <;> ring

theorem boundaryKernelFourier_smoothIntegral_pos_norm_le (M : ℕ)
    (hM : 2 ≤ M) (h : ℤ) (c : ℂ) :
    ‖∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
      ((2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3 : ℝ) : ℂ) *
        (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))‖ ≤
      ((M : ℝ) - 4 / (M : ℝ)) * ‖c‖ ^ 2 := by
  let a : ℝ := 1 / (M : ℝ)
  let b : ℝ := 1 / 2
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact one_div_le_one_div_of_le zero_lt_two (by exact_mod_cast hM)
  calc
    ‖∫ t in a..b,
        ((2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3 : ℝ) : ℂ) *
          (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))‖ ≤
        ∫ t in a..b,
          ‖((2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3 : ℝ) : ℂ) *
            (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b,
          (2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) * ‖c‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab] using ht
      have htpos : 0 < t := lt_of_lt_of_le ha ht'.1
      have hk : 0 ≤ 2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3 := by
        positivity
      have hchar : ‖fourier (-h) (t : AddCircle (1 : ℝ))‖ = 1 := by
        rw [fourier_apply, Circle.norm_coe]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hk, hchar, mul_one]
      ring
    _ = (∫ t in a..b,
          2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) * ‖c‖ ^ 2 := by
      rw [intervalIntegral.integral_mul_const]
    _ = ((M : ℝ) - 4 / (M : ℝ)) * ‖c‖ ^ 2 := by
      rw [boundaryKernelFourier_smoothVariation_pos M hM]

theorem boundaryKernelFourier_smoothIntegral_neg_norm_le (M : ℕ)
    (hM : 2 ≤ M) (h : ℤ) (c : ℂ) :
    ‖∫ t in (-(1 / 2 : ℝ))..(-(1 / (M : ℝ))),
      ((-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) : ℝ) : ℂ) *
        (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))‖ ≤
      ((M : ℝ) - 4 / (M : ℝ)) * ‖c‖ ^ 2 := by
  let a : ℝ := -(1 / 2 : ℝ)
  let b : ℝ := -(1 / (M : ℝ))
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hinvpos : 0 < 1 / (M : ℝ) := by positivity
  have hMge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have ha : a ≤ b := by
    dsimp [a, b]
    have hfrac := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hMge
    linarith
  have hbneg : b < 0 := by dsimp [b]; exact neg_lt_zero.mpr hinvpos
  calc
    ‖∫ t in a..b,
        ((-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) : ℝ) : ℂ) *
          (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))‖ ≤
        ∫ t in a..b,
          ‖((-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) : ℝ) : ℂ) *
            (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))‖ := by
      exact intervalIntegral.norm_integral_le_integral_norm ha
    _ = ∫ t in a..b,
          (-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3)) * ‖c‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le ha] using ht
      have htneg : t < 0 := lt_of_le_of_lt ht'.2 hbneg
      have hMt : (M : ℝ) * t < 0 := mul_neg_of_pos_of_neg hMpos htneg
      have hden : ((M : ℝ) * t) ^ 3 < 0 := by
        have hposcube : (-( (M : ℝ) * t)) ^ 3 > 0 :=
          pow_pos (neg_pos.mpr hMt) 3
        have hnegcube : ((M : ℝ) * t) ^ 3 = -(-( (M : ℝ) * t)) ^ 3 := by ring
        rw [hnegcube]
        linarith
      have hnum : 0 < 2 * (M : ℝ) ^ 2 := by positivity
      have hk : 0 ≤ -(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) :=
        neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos (le_of_lt hnum)
          (le_of_lt hden))
      have hchar : ‖fourier (-h) (t : AddCircle (1 : ℝ))‖ = 1 := by
        rw [fourier_apply, Circle.norm_coe]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hk, hchar, mul_one]
      ring
    _ = (∫ t in a..b,
          -(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3)) * ‖c‖ ^ 2 := by
      rw [intervalIntegral.integral_mul_const]
    _ = ((M : ℝ) - 4 / (M : ℝ)) * ‖c‖ ^ 2 := by
      rw [boundaryKernelFourier_smoothVariation_neg M hM]

theorem boundaryKernelFourierTail_pos_second_ibp (M : ℕ) (hM : 2 ≤ M)
    {h : ℤ} (hh : h ≠ 0) :
    let c : ℂ := ((1 : ℝ) : ℂ) /
      (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ));
    (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
      ((-(M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ) *
        (c * fourier (-h) (t : AddCircle (1 : ℝ)))) =
      ((-(M : ℝ) / ((M : ℝ) * (1 / 2 : ℝ)) ^ 2 : ℝ) : ℂ) *
          (c * (c * fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))) -
        ((-(M : ℝ) / ((M : ℝ) * (1 / (M : ℝ))) ^ 2 : ℝ) : ℂ) *
          (c * (c * @fourier (1 : ℝ) (-h)
            ((((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))) -
        (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
          ((2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3 : ℝ) : ℂ) *
            (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))) := by
  let a : ℝ := 1 / (M : ℝ)
  let b : ℝ := 1 / 2
  let c : ℂ := ((1 : ℝ) : ℂ) /
    (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))
  let f : ℝ → ℂ := fun t =>
    ((-(M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ)
  let g : ℝ → ℂ := fun t => c * fourier (-h) (t : AddCircle (1 : ℝ))
  let H : ℝ → ℂ := fun t => c * g t
  let f' : ℝ → ℂ := fun t =>
    ((2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3 : ℝ) : ℂ)
  let g' : ℝ → ℂ := fun t => fourier (-h) (t : AddCircle (1 : ℝ))
  let H' : ℝ → ℂ := g
  letI : MeasureTheory.IsLocallyFiniteMeasure
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := Real.locallyFinite_volume
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact one_div_le_one_div_of_le zero_lt_two hMge
  have hFcont : ContinuousOn f (Set.Icc a b) := by
    dsimp [f]
    have hden : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 2)
        (Set.Icc a b) := (continuousOn_const.mul continuousOn_id).pow 2
    have hden_ne : ∀ t ∈ Set.Icc a b, ((M : ℝ) * t) ^ 2 ≠ 0 := by
      intro t ht
      apply pow_ne_zero
      exact ne_of_gt (mul_pos hMpos (lt_of_lt_of_le ha ht.1))
    exact Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.div continuousOn_const.neg hden hden_ne)
  have hFcontU : ContinuousOn f (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hFcont
  have hGcont : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact continuousOn_const.mul
      (((map_continuous (fourier (-h))).comp
        (AddCircle.continuous_mk' (1 : ℝ))).continuousOn)
  have hGcontU : ContinuousOn g (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hGcont
  have hHcont : ContinuousOn H (Set.Icc a b) := by
    dsimp [H]
    exact continuousOn_const.mul hGcont
  have hHcontU : ContinuousOn H (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hHcont
  have hFderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt f (f' x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := by
      simpa [min_eq_left hab, max_eq_right hab] using hx
    dsimp [f, f']
    apply HasDerivAt.ofReal_comp
    apply boundaryKernelFourier_secondDeriv_pos_tail M hM
    exact lt_trans ha hx'.1
  have hT : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hGderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt g (g' x) x := by
    intro x _
    change HasDerivAt
      (fun t : ℝ => c * fourier (-h) (t : AddCircle (1 : ℝ)))
      (fourier (-h) (x : AddCircle (1 : ℝ))) x
    exact has_antideriv_at_fourier_neg hT hh x
  have hHderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt H (H' x) x := by
    intro x hx
    have hder := hGderiv x hx
    change HasDerivAt (fun t : ℝ => c * g t) (g x) x
    convert hder.const_mul c using 1 <;> simp [H, H', g]
  have hf'cont : ContinuousOn f' (Set.Icc a b) := by
    dsimp [f']
    have hden : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 3)
        (Set.Icc a b) := (continuousOn_const.mul continuousOn_id).pow 3
    have hden_ne : ∀ t ∈ Set.Icc a b, ((M : ℝ) * t) ^ 3 ≠ 0 := by
      intro t ht
      apply pow_ne_zero
      exact ne_of_gt (mul_pos hMpos (lt_of_lt_of_le ha ht.1))
    exact Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.div continuousOn_const hden hden_ne)
  have hf'int : IntervalIntegrable f'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b :=
    hf'cont.intervalIntegrable_of_Icc hab
  have hg'cont : ContinuousOn g' (Set.Icc a b) := by
    dsimp [g']
    exact ((map_continuous (fourier (-h))).comp
      (AddCircle.continuous_mk' (1 : ℝ))).continuousOn
  have hg'int : IntervalIntegrable g'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b :=
    hg'cont.intervalIntegrable_of_Icc hab
  have hH'int : IntervalIntegrable H'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
    simpa [H'] using hGcont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hFcontU hHcontU hFderiv hHderiv hf'int hH'int
  simpa only [a, b, c, f, g, H, f', H', mul_assoc] using hIBP

theorem boundaryKernelFourierTail_neg_second_ibp (M : ℕ) (hM : 2 ≤ M)
    {h : ℤ} (hh : h ≠ 0) :
    let c : ℂ := ((1 : ℝ) : ℂ) /
      (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ));
    (∫ t in (-(1 / 2 : ℝ))..(-(1 / (M : ℝ))),
      (((M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ) *
        (c * fourier (-h) (t : AddCircle (1 : ℝ)))) =
      (((M : ℝ) / ((M : ℝ) * (-(1 / (M : ℝ))) : ℝ) ^ 2 : ℝ) : ℂ) *
          (c * (c * @fourier (1 : ℝ) (-h)
            ((-((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))) -
        (((M : ℝ) / ((M : ℝ) * (-(1 / 2 : ℝ)) : ℝ) ^ 2 : ℝ) : ℂ) *
          (c * (c * fourier (-h) ((-(1 / 2 : ℝ)) : AddCircle (1 : ℝ)))) -
        (∫ t in (-(1 / 2 : ℝ))..(-(1 / (M : ℝ))),
          ((-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) : ℝ) : ℂ) *
            (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))) := by
  let a : ℝ := -(1 / 2 : ℝ)
  let b : ℝ := -(1 / (M : ℝ))
  let c : ℂ := ((1 : ℝ) : ℂ) /
    (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))
  let f : ℝ → ℂ := fun t =>
    (((M : ℝ) / ((M : ℝ) * t) ^ 2 : ℝ) : ℂ)
  let g : ℝ → ℂ := fun t => c * fourier (-h) (t : AddCircle (1 : ℝ))
  let H : ℝ → ℂ := fun t => c * g t
  let f' : ℝ → ℂ := fun t =>
    ((-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) : ℝ) : ℂ)
  let g' : ℝ → ℂ := fun t => fourier (-h) (t : AddCircle (1 : ℝ))
  let H' : ℝ → ℂ := g
  letI : MeasureTheory.IsLocallyFiniteMeasure
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := Real.locallyFinite_volume
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hinvpos : 0 < 1 / (M : ℝ) := by positivity
  have hhalf : 1 / (M : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le zero_lt_two (by exact_mod_cast hM)
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbneg : b < 0 := by dsimp [b]; exact neg_lt_zero.mpr hinvpos
  have hFcont : ContinuousOn f (Set.Icc a b) := by
    dsimp [f]
    have hden : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 2)
        (Set.Icc a b) := (continuousOn_const.mul continuousOn_id).pow 2
    have hden_ne : ∀ t ∈ Set.Icc a b, ((M : ℝ) * t) ^ 2 ≠ 0 := by
      intro t ht
      apply pow_ne_zero
      have htneg : t < 0 := lt_of_le_of_lt ht.2 hbneg
      exact ne_of_lt (mul_neg_of_pos_of_neg hMpos htneg)
    exact Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.div continuousOn_const hden hden_ne)
  have hFcontU : ContinuousOn f (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hFcont
  have hGcont : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact continuousOn_const.mul
      (((map_continuous (fourier (-h))).comp
        (AddCircle.continuous_mk' (1 : ℝ))).continuousOn)
  have hGcontU : ContinuousOn g (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hGcont
  have hHcont : ContinuousOn H (Set.Icc a b) := by
    dsimp [H]
    exact continuousOn_const.mul hGcont
  have hHcontU : ContinuousOn H (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hHcont
  have hFderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt f (f' x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := by
      simpa [min_eq_left hab, max_eq_right hab] using hx
    dsimp [f, f']
    apply HasDerivAt.ofReal_comp
    apply boundaryKernelFourier_secondDeriv_neg_tail M hM
    exact lt_trans hx'.2 hbneg
  have hT : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hGderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt g (g' x) x := by
    intro x _
    change HasDerivAt
      (fun t : ℝ => c * fourier (-h) (t : AddCircle (1 : ℝ)))
      (fourier (-h) (x : AddCircle (1 : ℝ))) x
    exact has_antideriv_at_fourier_neg hT hh x
  have hHderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt H (H' x) x := by
    intro x hx
    have hder := hGderiv x hx
    change HasDerivAt (fun t : ℝ => c * g t) (g x) x
    convert hder.const_mul c using 1 <;> simp [H, H', g]
  have hf'cont : ContinuousOn f' (Set.Icc a b) := by
    dsimp [f']
    have hden : ContinuousOn (fun t : ℝ => ((M : ℝ) * t) ^ 3)
        (Set.Icc a b) := (continuousOn_const.mul continuousOn_id).pow 3
    have hden_ne : ∀ t ∈ Set.Icc a b, ((M : ℝ) * t) ^ 3 ≠ 0 := by
      intro t ht
      apply pow_ne_zero
      have htneg : t < 0 := lt_of_le_of_lt ht.2 hbneg
      exact ne_of_lt (mul_neg_of_pos_of_neg hMpos htneg)
    exact Complex.continuous_ofReal.comp_continuousOn <| by
      have hquot : ContinuousOn
          (fun t : ℝ => (2 * (M : ℝ) ^ 2) / ((M : ℝ) * t) ^ 3)
          (Set.Icc a b) := ContinuousOn.div continuousOn_const hden hden_ne
      exact hquot.neg
  have hf'int : IntervalIntegrable f'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b :=
    hf'cont.intervalIntegrable_of_Icc hab
  have hH'int : IntervalIntegrable H'
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
    simpa [H'] using hGcont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hFcontU hHcontU hFderiv hHderiv hf'int hH'int
  simpa only [a, b, c, f, g, H, f', H', mul_assoc, AddCircle.coe_neg] using hIBP

theorem boundaryKernelFourierCoefficient_second_derivative_formula (M : ℕ)
    (hM : 2 ≤ M) {h : ℤ} (hh : h ≠ 0) :
    let c : ℂ := ((1 : ℝ) : ℂ) /
      (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ));
    boundaryKernelFourierCoefficient M hM h =
      - (((M : ℝ) / ((M : ℝ) * (-(1 / (M : ℝ))) : ℝ) ^ 2 : ℝ) : ℂ) *
          (c * (c * @fourier (1 : ℝ) (-h)
            ((-((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))) +
        (((M : ℝ) / ((M : ℝ) * (-(1 / 2 : ℝ)) : ℝ) ^ 2 : ℝ) : ℂ) *
          (c * (c * fourier (-h) ((-(1 / 2 : ℝ)) : AddCircle (1 : ℝ)))) -
        ((-(M : ℝ) / ((M : ℝ) * (1 / 2 : ℝ)) ^ 2 : ℝ) : ℂ) *
          (c * (c * fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))) +
        ((-(M : ℝ) / ((M : ℝ) * (1 / (M : ℝ))) ^ 2 : ℝ) : ℂ) *
          (c * (c * @fourier (1 : ℝ) (-h)
            ((((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))) +
        (∫ t in (-(1 / 2 : ℝ))..(-(1 / (M : ℝ))),
          ((-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) : ℝ) : ℂ) *
            (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))) +
        (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
          ((2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3 : ℝ) : ℂ) *
            (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))) := by
  let c : ℂ := ((1 : ℝ) : ℂ) /
    (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))
  have hfirst := boundaryKernelFourierCoefficient_derivative_formula M hM hh
  have hneg := boundaryKernelFourierTail_neg_second_ibp M hM hh
  have hpos := boundaryKernelFourierTail_pos_second_ibp M hM hh
  dsimp only
  rw [hfirst]
  rw [hneg, hpos]
  ring

theorem boundaryKernelFourierCoefficient_norm_le_variation (M : ℕ)
    (hM : 2 ≤ M) {h : ℤ} (hh : h ≠ 0) :
    ‖boundaryKernelFourierCoefficient M hM h‖ ≤
      4 * (M : ℝ) *
        ‖((1 : ℝ) : ℂ) /
          (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))‖ ^ 2 := by
  let c : ℂ := ((1 : ℝ) : ℂ) /
    (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))
  let Uneg : ℂ := c * (c * @fourier (1 : ℝ) (-h)
    ((-((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))
  let Upos : ℂ := c * (c * @fourier (1 : ℝ) (-h)
    ((((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))
  let Uouter : ℂ := c * (c * fourier (-h)
    ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))
  let Jneg : ℂ := ∫ t in (-(1 / 2 : ℝ))..(-(1 / (M : ℝ))),
    ((-(2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3) : ℝ) : ℂ) *
      (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))
  let Jpos : ℂ := ∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
    ((2 * (M : ℝ) ^ 2 / ((M : ℝ) * t) ^ 3 : ℝ) : ℂ) *
      (c * (c * fourier (-h) (t : AddCircle (1 : ℝ))))
  have hformula := boundaryKernelFourierCoefficient_second_derivative_formula
    M hM hh
  dsimp only [c] at hformula
  rw [boundaryKernelFourier_endpoint_terms_eq M hM h c] at hformula
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMnonneg : 0 ≤ (M : ℝ) := le_of_lt hMpos
  have hinvpos : 0 < 8 / (M : ℝ) := by positivity
  have hUneg : ‖Uneg‖ = ‖c‖ ^ 2 := by
    dsimp [Uneg]
    calc
      ‖c * (c * @fourier (1 : ℝ) (-h)
          ((-((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))‖ =
          ‖c‖ * (‖c‖ * ‖@fourier (1 : ℝ) (-h)
            ((-((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ))‖) := by
              rw [norm_mul, norm_mul]
      _ = ‖c‖ ^ 2 := by
        rw [boundaryKernelFourier_pointwise_character_norm]
        ring
  have hUpos : ‖Upos‖ = ‖c‖ ^ 2 := by
    dsimp [Upos]
    calc
      ‖c * (c * @fourier (1 : ℝ) (-h)
          ((((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ)))‖ =
          ‖c‖ * (‖c‖ * ‖@fourier (1 : ℝ) (-h)
            ((((1 : ℝ) / (M : ℝ)) : ℝ) : AddCircle (1 : ℝ))‖) := by
              rw [norm_mul, norm_mul]
      _ = ‖c‖ ^ 2 := by
        rw [boundaryKernelFourier_pointwise_character_norm]
        ring
  have hUouter : ‖Uouter‖ = ‖c‖ ^ 2 := by
    dsimp [Uouter]
    calc
      ‖c * (c * fourier (-h) ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))‖ =
          ‖c‖ * (‖c‖ * ‖fourier (-h)
            ((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖) := by
              rw [norm_mul, norm_mul]
      _ = ‖c‖ ^ 2 := by
        rw [boundaryKernelFourier_pointwise_character_norm]
        ring
  have hA : ‖-((M : ℝ) : ℂ) * Uneg‖ = (M : ℝ) * ‖c‖ ^ 2 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hMpos, hUneg]
  have hB : ‖-((M : ℝ) : ℂ) * Upos‖ = (M : ℝ) * ‖c‖ ^ 2 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hMpos, hUpos]
  have hC : ‖((8 / (M : ℝ) : ℝ) : ℂ) * Uouter‖ =
      (8 / (M : ℝ)) * ‖c‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hinvpos, hUouter]
  have hJneg := boundaryKernelFourier_smoothIntegral_neg_norm_le M hM h c
  have hJpos := boundaryKernelFourier_smoothIntegral_pos_norm_le M hM h c
  rw [hformula]
  change ‖-((M : ℝ) : ℂ) * Uneg - ((M : ℝ) : ℂ) * Upos +
      ((8 / (M : ℝ) : ℝ) : ℂ) * Uouter + Jneg + Jpos‖ ≤
    4 * (M : ℝ) * ‖c‖ ^ 2
  calc
    _ ≤ ‖-((M : ℝ) : ℂ) * Uneg‖ +
          ‖-((M : ℝ) : ℂ) * Upos‖ +
          ‖((8 / (M : ℝ) : ℝ) : ℂ) * Uouter‖ + ‖Jneg‖ + ‖Jpos‖ := by
      calc
        ‖(-((M : ℝ) : ℂ) * Uneg - ((M : ℝ) : ℂ) * Upos +
            ((8 / (M : ℝ) : ℝ) : ℂ) * Uouter + Jneg) + Jpos‖ ≤
            ‖-((M : ℝ) : ℂ) * Uneg - ((M : ℝ) : ℂ) * Upos +
              ((8 / (M : ℝ) : ℝ) : ℂ) * Uouter + Jneg‖ + ‖Jpos‖ :=
          norm_add_le _ _
        _ ≤ (‖-((M : ℝ) : ℂ) * Uneg - ((M : ℝ) : ℂ) * Upos +
              ((8 / (M : ℝ) : ℝ) : ℂ) * Uouter‖ + ‖Jneg‖) + ‖Jpos‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ((‖-((M : ℝ) : ℂ) * Uneg - ((M : ℝ) : ℂ) * Upos‖ +
              ‖((8 / (M : ℝ) : ℝ) : ℂ) * Uouter‖) + ‖Jneg‖) + ‖Jpos‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (((‖-((M : ℝ) : ℂ) * Uneg‖ +
              ‖-((M : ℝ) : ℂ) * Upos‖) +
              ‖((8 / (M : ℝ) : ℝ) : ℂ) * Uouter‖) + ‖Jneg‖) + ‖Jpos‖ := by
          gcongr
          simpa [neg_mul] using
            (norm_sub_le (-((M : ℝ) : ℂ) * Uneg)
              (((M : ℝ) : ℂ) * Upos))
    _ ≤ ((M : ℝ) * ‖c‖ ^ 2 + (M : ℝ) * ‖c‖ ^ 2 +
          (8 / (M : ℝ)) * ‖c‖ ^ 2 +
          ((M : ℝ) - 4 / (M : ℝ)) * ‖c‖ ^ 2 +
          ((M : ℝ) - 4 / (M : ℝ)) * ‖c‖ ^ 2) := by
      rw [hA, hB, hC]
      linarith [hJneg, hJpos]
    _ = 4 * (M : ℝ) * ‖c‖ ^ 2 := by ring

theorem boundaryKernelFourierCoefficient_norm_le_M_div_h_sq (M : ℕ)
    (hM : 2 ≤ M) {h : ℤ} (hh : h ≠ 0) :
    ‖boundaryKernelFourierCoefficient M hM h‖ ≤
      (M : ℝ) / (h : ℝ) ^ 2 := by
  calc
    ‖boundaryKernelFourierCoefficient M hM h‖ ≤
        4 * (M : ℝ) *
          ‖((1 : ℝ) : ℂ) /
            (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))‖ ^ 2 :=
      boundaryKernelFourierCoefficient_norm_le_variation M hM hh
    _ ≤ (M : ℝ) / (h : ℝ) ^ 2 := by
      have hMnonneg : 0 ≤ (M : ℝ) := by positivity
      calc
        4 * (M : ℝ) *
            ‖((1 : ℝ) : ℂ) /
              (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))‖ ^ 2 =
            (M : ℝ) * (4 *
              ‖((1 : ℝ) : ℂ) /
                (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ))‖ ^ 2) := by ring
        _ ≤ (M : ℝ) * (1 / (h : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (boundaryKernelFourier_antiderivative_scalar_sq_bound hh)
            hMnonneg
        _ = (M : ℝ) / (h : ℝ) ^ 2 := by ring

theorem boundaryKernelFourierCoefficient_norm_le_min (M : ℕ)
    (hM : 2 ≤ M) {h : ℤ} (hh : h ≠ 0) :
    ‖boundaryKernelFourierCoefficient M hM h‖ ≤
      min ((2 * (1 + (Real.log 4)⁻¹)) *
        Real.log (2 * (M : ℝ)) / (M : ℝ)) ((M : ℝ) / (h : ℝ) ^ 2) := by
  rw [le_min_iff]
  exact ⟨boundaryKernelFourierCoefficient_uniform_bound M hM h,
    boundaryKernelFourierCoefficient_norm_le_M_div_h_sq M hM hh⟩

theorem boundaryKernelFourierCoefficient_norm_summable (M : ℕ)
    (hM : 2 ≤ M) :
    Summable (fun h : ℤ => ‖boundaryKernelFourierCoefficient M hM h‖) := by
  apply summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
  rw [Asymptotics.isBigO_iff]
  refine ⟨(M : ℝ), ?_⟩
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with h hh
  have hdecay := boundaryKernelFourierCoefficient_norm_le_M_div_h_sq M hM hh
  have hcmp : |(h : ℝ)| ^ (-2 : ℝ) = 1 / (h : ℝ) ^ 2 := by
    calc
      |(h : ℝ)| ^ (-2 : ℝ) = (|(h : ℝ)| ^ (2 : ℝ))⁻¹ :=
        Real.rpow_neg (abs_nonneg _) (2 : ℝ)
      _ = (|(h : ℝ)| ^ (2 : ℕ))⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast |(h : ℝ)| 2)
      _ = ((h : ℝ) ^ 2)⁻¹ := congrArg Inv.inv (sq_abs _)
      _ = 1 / (h : ℝ) ^ 2 := by rw [one_div]
  change ‖‖boundaryKernelFourierCoefficient M hM h‖‖ ≤
    (M : ℝ) * ‖|(h : ℝ)| ^ (-2 : ℝ)‖
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (by positivity : 0 ≤ |(h : ℝ)| ^ (-2 : ℝ)), hcmp]
  simpa [div_eq_mul_inv] using hdecay

theorem boundaryKernelCircleFunction_hasSum_fourier_series (M : ℕ)
    (hM : 2 ≤ M) :
    HasSum (fun h : ℤ => boundaryKernelFourierCoefficient M hM h • fourier h)
      (boundaryKernelCircleFunction M hM) := by
  letI : Fact (0 < (1 / 2 : ℝ) - (-1 / 2 : ℝ)) := ⟨by norm_num⟩
  have hcoeff :
      Summable (fun h : ℤ => fourierCoeff (boundaryKernelCircleFunction M hM) h) := by
    apply Summable.of_norm
    simpa only [boundaryKernelFourierCoefficient_eq_circle_fourierCoeff M hM] using
      boundaryKernelFourierCoefficient_norm_summable M hM
  have hseries := hasSum_fourier_series_of_summable hcoeff
  simpa only [boundaryKernelFourierCoefficient_eq_circle_fourierCoeff M hM] using hseries

theorem boundaryKernelCircleFunction_apply_centered (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : t ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    boundaryKernelCircleFunction M hM (t : AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) =
      (floorBoundaryKernel M hM t : ℂ) := by
  change AddCircle.liftIoc ((1 / 2 : ℝ) - (-1 / 2 : ℝ)) (-1 / 2 : ℝ)
      (fun s => (floorBoundaryKernel M hM s : ℂ)) (t : AddCircle _) = _
  have ht' : t ∈ Set.Ioc (-1 / 2 : ℝ)
      ((-1 / 2 : ℝ) + ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) := by
    simpa only [show (-1 / 2 : ℝ) + ((1 / 2 : ℝ) - (-1 / 2 : ℝ)) =
      1 / 2 by ring] using ht
  exact AddCircle.liftIoc_coe_apply ht'

/-- Pointwise Fourier reconstruction of the boundary kernel on its centered
representative interval. -/
theorem floorBoundaryKernel_eq_tsum_fourier_centered (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : t ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    (floorBoundaryKernel M hM t : ℂ) =
      ∑' h : ℤ, boundaryKernelFourierCoefficient M hM h •
        fourier h (t : AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) := by
  rw [← boundaryKernelCircleFunction_apply_centered M hM ht]
  let hs := boundaryKernelCircleFunction_hasSum_fourier_series M hM
  calc
    boundaryKernelCircleFunction M hM
        (t : AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) =
        (∑' h : ℤ, boundaryKernelFourierCoefficient M hM h • fourier h)
          (t : AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) := by rw [hs.tsum_eq]
    _ = ∑' h : ℤ, boundaryKernelFourierCoefficient M hM h •
          fourier h (t : AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) := by
      symm
      exact ContinuousMap.tsum_apply hs.summable
        (t : AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ)))

/-- Fourier reconstruction at every real argument, using a centered
representative and period-one invariance of the kernel. -/
theorem floorBoundaryKernel_eq_tsum_fourier (M : ℕ) (hM : 2 ≤ M) (t : ℝ) :
    (floorBoundaryKernel M hM t : ℂ) =
      ∑' h : ℤ, boundaryKernelFourierCoefficient M hM h •
        fourier h (t : AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) := by
  let k : ℤ := Int.ceil (t - 1 / 2)
  let s : ℝ := t - (k : ℝ)
  have hsleft : -(1 / 2 : ℝ) < s := by
    have hceil := Int.ceil_lt_add_one (t - 1 / 2)
    dsimp [s, k]
    linarith
  have hsrght : s ≤ 1 / 2 := by
    have hceil := Int.le_ceil (t - 1 / 2)
    dsimp [s, k]
    linarith
  have hs : s ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
    constructor
    · convert hsleft using 1 <;> ring
    · exact hsrght
  have hshift : t = s + (k : ℝ) := by dsimp [s]; ring
  let T : ℝ := (1 / 2 : ℝ) - (-1 / 2 : ℝ)
  have hT : T = 1 := by dsimp [T]; ring
  have hkzero : ((k : ℝ) : AddCircle T) = 0 := by
    have hkcast : (k : ℝ) = k • T := by rw [hT]; simp
    rw [hkcast, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero]
  have hcircle : (t : AddCircle T) = (s : AddCircle T) := by
    rw [hshift, AddCircle.coe_add, hkzero, add_zero]
  calc
    (floorBoundaryKernel M hM t : ℂ) = (floorBoundaryKernel M hM s : ℂ) := by
      rw [hshift]
      exact_mod_cast floorBoundaryKernel_add_int M hM s k
    _ = ∑' h : ℤ, boundaryKernelFourierCoefficient M hM h •
          fourier h (s : AddCircle T) := by
      simpa [T] using floorBoundaryKernel_eq_tsum_fourier_centered M hM hs
    _ = ∑' h : ℤ, boundaryKernelFourierCoefficient M hM h •
          fourier h (t : AddCircle T) := by rw [← hcircle]

/-- Exchange a finite sum of boundary-kernel values with its absolutely
convergent Fourier series. -/
theorem sum_floorBoundaryKernel_eq_tsum_fourier (M : ℕ) (hM : 2 ≤ M)
    (s : Finset ℤ) (f : ℤ → ℝ) :
    ∑ n ∈ s, (floorBoundaryKernel M hM (f n) : ℂ) =
      ∑' h : ℤ, boundaryKernelFourierCoefficient M hM h •
        ∑ n ∈ s, fourier h (f n : AddCircle ((1 / 2 : ℝ) - (-1 / 2 : ℝ))) := by
  let T : ℝ := (1 / 2 : ℝ) - (-1 / 2 : ℝ)
  letI : Fact (0 < T) := ⟨by dsimp [T]; norm_num⟩
  let g : (s × ℤ) → ℂ := fun p =>
    boundaryKernelFourierCoefficient M hM p.2 • fourier p.2 (f p.1.1 : AddCircle T)
  have hcoeff := boundaryKernelFourierCoefficient_norm_summable M hM
  have hinner : ∀ n : s, Summable (fun h : ℤ => ‖g (n, h)‖) := by
    intro n
    convert hcoeff using 1
    ext h
    have hchar : ‖fourier h (f n.1 : AddCircle T)‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    change ‖boundaryKernelFourierCoefficient M hM h •
      fourier h (f n.1 : AddCircle T)‖ =
      ‖boundaryKernelFourierCoefficient M hM h‖
    rw [norm_smul, hchar, mul_one]
  have houter : Summable (fun n : s => ∑' h : ℤ, ‖g (n, h)‖) := by
    apply Summable.of_finite
  have hdoubleNorm : Summable (fun p : s × ℤ => ‖g p‖) := by
    apply (summable_prod_of_nonneg (fun p : s × ℤ => norm_nonneg (g p))).2
    exact ⟨hinner, houter⟩
  have hdouble : Summable g := Summable.of_norm hdoubleNorm
  calc
    ∑ n ∈ s, (floorBoundaryKernel M hM (f n) : ℂ) =
        ∑ n : s, (floorBoundaryKernel M hM (f n.1) : ℂ) := by
      symm
      exact Finset.sum_coe_sort s (fun n => (floorBoundaryKernel M hM (f n) : ℂ))
    _ = ∑' n : s, (floorBoundaryKernel M hM (f n.1) : ℂ) := by
      rw [tsum_fintype]
    _ = ∑' n : s, ∑' h : ℤ, g (n, h) := by
      apply tsum_congr
      intro n
      simpa [g, T] using floorBoundaryKernel_eq_tsum_fourier M hM (f n.1)
    _ = ∑' h : ℤ, ∑' n : s, g (n, h) := hdouble.tsum_comm.symm
    _ = ∑' h : ℤ, boundaryKernelFourierCoefficient M hM h •
          ∑ n ∈ s, fourier h (f n : AddCircle T) := by
      apply tsum_congr
      intro h
      rw [tsum_fintype]
      rw [← Finset.sum_coe_sort s (fun n => fourier h (f n : AddCircle T))]
      rw [Finset.smul_sum]

/-- The finite-sum Fourier identity with the paper's monomial phase. -/
theorem sum_floorBoundaryKernel_monomial_eq_tsum (M : ℕ) (hM : 2 ≤ M)
    (s : Finset ℤ) (c : ℝ) :
    ∑ n ∈ s, (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ) =
      ∑' h : ℤ, boundaryKernelFourierCoefficient M hM h •
        ∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * t ^ c) n := by
  rw [sum_floorBoundaryKernel_eq_tsum_fourier M hM s (fun n => (n : ℝ) ^ c)]
  apply tsum_congr
  intro h
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact fourier_monomial_phase c h n

/-- The zero Fourier mode contributes only its mean coefficient after the
progression normalization `d/N`; this isolates the zero-mode term in
blueprint `ar:boundary-error`. -/
theorem boundaryKernel_progression_zero_mode_bound
    (M : ℕ) (hM : 2 ≤ M) {N d c : ℝ} (hN : 0 < N) (hd : 0 < d) :
    (d / N) * ‖boundaryKernelFourierCoefficient M hM 0 *
      ∑ n ∈ realIntegerInterval 0 (N / d),
        realExponentialPhase (fun t => (0 : ℝ) * t ^ c) n‖ ≤
      (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) / (M : ℝ) := by
  let s : Finset ℤ := realIntegerInterval 0 (N / d)
  have hNd : 0 ≤ N / d := by positivity
  have hcard : (s.card : ℝ) ≤ N / d := by
    simpa [s] using realIntegerInterval_zero_card_le (N / d) hNd
  have hsum : ‖∑ n ∈ s,
      realExponentialPhase (fun t => (0 : ℝ) * t ^ c) n‖ ≤ (s.card : ℝ) := by
    calc
      ‖∑ n ∈ s, realExponentialPhase (fun t => (0 : ℝ) * t ^ c) n‖ ≤
          ∑ n ∈ s, ‖realExponentialPhase (fun t => (0 : ℝ) * t ^ c) n‖ :=
        norm_sum_le _ _
      _ = (s.card : ℝ) := by simp [norm_realExponentialPhase]
  have hsum' : ‖∑ n ∈ s,
      realExponentialPhase (fun t => (0 : ℝ) * t ^ c) n‖ ≤ N / d :=
    hsum.trans hcard
  have hcoef := boundaryKernelFourierCoefficient_zero_bound M hM
  have hscale : 0 ≤ d / N := le_of_lt (div_pos hd hN)
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hA : 0 ≤
      (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) / (M : ℝ) := by
    have hlog : 0 ≤ Real.log (2 * (M : ℝ)) :=
      Real.log_nonneg (by nlinarith [hMreal])
    positivity
  have hinner :
      ‖boundaryKernelFourierCoefficient M hM 0‖ *
          ‖∑ n ∈ s, realExponentialPhase (fun t => (0 : ℝ) * t ^ c) n‖ ≤
        ((2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) /
          (M : ℝ)) * (N / d) := by
    exact mul_le_mul hcoef hsum' (norm_nonneg _) (by positivity)
  calc
    (d / N) * ‖boundaryKernelFourierCoefficient M hM 0 *
        ∑ n ∈ realIntegerInterval 0 (N / d),
          realExponentialPhase (fun t => (0 : ℝ) * t ^ c) n‖ =
        (d / N) * ‖boundaryKernelFourierCoefficient M hM 0‖ *
          ‖∑ n ∈ s,
            realExponentialPhase (fun t => (0 : ℝ) * t ^ c) n‖ := by
              rw [norm_mul]
              simp [s, mul_assoc]
    _ ≤ (d / N) *
        ((2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) /
          (M : ℝ)) * (N / d) := by
            calc
              _ = (d / N) *
                  (‖boundaryKernelFourierCoefficient M hM 0‖ *
                    ‖∑ n ∈ s,
                      realExponentialPhase (fun t => (0 : ℝ) * t ^ c) n‖) := by ring
              _ ≤ (d / N) *
                  (((2 * (1 + (Real.log 4)⁻¹)) *
                    Real.log (2 * (M : ℝ)) / (M : ℝ)) * (N / d)) :=
                mul_le_mul_of_nonneg_left hinner hscale
              _ = (d / N) *
                  ((2 * (1 + (Real.log 4)⁻¹)) *
                    Real.log (2 * (M : ℝ)) / (M : ℝ)) * (N / d) := by ring
    _ = (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) /
        (M : ℝ) := by
          field_simp
          <;> ring

theorem boundaryKernel_monomial_fourier_terms_summable (M : ℕ)
    (hM : 2 ≤ M) (s : Finset ℤ) (c : ℝ) :
    Summable (fun h : ℤ => boundaryKernelFourierCoefficient M hM h *
      ∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * t ^ c) n) := by
  have hcoeff := boundaryKernelFourierCoefficient_norm_summable M hM
  have hdom : Summable (fun h : ℤ => (s.card : ℝ) *
      ‖boundaryKernelFourierCoefficient M hM h‖) :=
    hcoeff.mul_left (s.card : ℝ)
  apply hdom.of_norm_bounded
  intro h
  rw [norm_mul]
  have hphase : ‖∑ n ∈ s,
      realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤ s.card := by
    calc
      ‖∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤
          ∑ n ∈ s, ‖realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ :=
        norm_sum_le s _
      _ = s.card := by simp [norm_realExponentialPhase]
  calc
    ‖boundaryKernelFourierCoefficient M hM h‖ *
        ‖∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤
      ‖boundaryKernelFourierCoefficient M hM h‖ * s.card :=
        mul_le_mul_of_nonneg_left hphase (norm_nonneg _)
    _ = (s.card : ℝ) *
        ‖boundaryKernelFourierCoefficient M hM h‖ := by ring

theorem sum_inv_sq_shifted_le (H N : ℕ) (hH : 1 ≤ H) :
    (∑ n ∈ Finset.range N, 1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) ≤
      1 / (H : ℝ) - 1 / ((H + N : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hbaseNat : 0 < H + N := by omega
      have hbase : 0 < ((H + N : ℕ) : ℝ) := by exact_mod_cast hbaseNat
      have hbaseR : 0 < (H : ℝ) + (N : ℝ) := by positivity
      have hterm :
          1 / ((H + N + 1 : ℕ) : ℝ) ^ 2 ≤
            1 / ((H + N : ℕ) : ℝ) -
              1 / ((H + N + 1 : ℕ) : ℝ) := by
        have hcast : ((H + N + 1 : ℕ) : ℝ) = (H + N : ℝ) + 1 := by
          push_cast
          ring
        rw [hcast]
        push_cast
        have hprev : (H : ℝ) + (N : ℝ) ≠ 0 := ne_of_gt hbaseR
        field_simp
        nlinarith
      have hcast : ((H + (N + 1) : ℕ) : ℝ) =
          ((H + N + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast]
      calc
        (∑ n ∈ Finset.range N, 1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) +
            1 / ((H + N + 1 : ℕ) : ℝ) ^ 2 ≤
          (1 / (H : ℝ) - 1 / ((H + N : ℕ) : ℝ)) +
            (1 / ((H + N : ℕ) : ℝ) - 1 / ((H + N + 1 : ℕ) : ℝ)) :=
          add_le_add ih hterm
        _ = 1 / (H : ℝ) - 1 / ((H + N + 1 : ℕ) : ℝ) := by ring

theorem tsum_inv_sq_shifted_le (H : ℕ) (hH : 1 ≤ H) :
    (∑' n : ℕ, 1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (H : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) ?_
  intro N
  calc
    (∑ n ∈ Finset.range N, 1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) ≤
        1 / (H : ℝ) - 1 / ((H + N : ℕ) : ℝ) :=
      sum_inv_sq_shifted_le H N hH
    _ ≤ 1 / (H : ℝ) := by
      have hnonneg : 0 ≤ 1 / ((H + N : ℕ) : ℝ) := by positivity
      linarith

theorem tsum_int_eq_zero_add_pos_and_neg {f : ℤ → ℝ} (hf : Summable f) :
    (∑' h : ℤ, f h) = f 0 + (∑' n : ℕ, f (n + 1)) +
      ∑' n : ℕ, f (-(n + 1)) := by
  have hpos : Summable (fun n : ℕ => f (n + 1)) := by
    exact hf.comp_injective (fun m n h => by
      have hm : m + 1 = n + 1 := by exact_mod_cast h
      omega)
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
    exact hf.comp_injective (fun m n h => by
      have hc : ((m + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := neg_inj.mp h
      have hm : m + 1 = n + 1 := by exact_mod_cast hc
      omega)
  rw [tsum_of_add_one_of_neg_add_one hpos hneg]
  ring

theorem tsum_int_complex_eq_zero_add_pos_and_neg {f : ℤ → ℂ}
    (hf : Summable f) :
    (∑' h : ℤ, f h) = f 0 + (∑' n : ℕ, f (n + 1)) +
      ∑' n : ℕ, f (-(n + 1)) := by
  have hpos : Summable (fun n : ℕ => f (n + 1)) := by
    exact hf.comp_injective (fun m n h => by
      have hm : m + 1 = n + 1 := by exact_mod_cast h
      omega)
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
    exact hf.comp_injective (fun m n h => by
      have hc : ((m + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := neg_inj.mp h
      have hm : m + 1 = n + 1 := by exact_mod_cast hc
      omega)
  rw [tsum_of_add_one_of_neg_add_one hpos hneg]
  ring

theorem tsum_int_complex_cutoff_decomposition {f : ℤ → ℂ}
    (hf : Summable f) (H : ℕ) :
    (∑' h : ℤ, f h) = f 0 +
      ((∑ n ∈ Finset.range H, f (n + 1)) +
        ∑' n : ℕ, f (n + H + 1)) +
      ((∑ n ∈ Finset.range H, f (-(n + 1))) +
        ∑' n : ℕ, f (-(n + H + 1))) := by
  have hpos : Summable (fun n : ℕ => f (n + 1)) := by
    exact hf.comp_injective (fun m n h => by
      have hm : m + 1 = n + 1 := by exact_mod_cast h
      omega)
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
    exact hf.comp_injective (fun m n h => by
      have hc : ((m + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := neg_inj.mp h
      have hm : m + 1 = n + 1 := by exact_mod_cast hc
      omega)
  rw [tsum_int_complex_eq_zero_add_pos_and_neg hf,
    ← hpos.sum_add_tsum_nat_add H, ← hneg.sum_add_tsum_nat_add H]
  simp only [Nat.cast_add]

noncomputable def boundaryKernelMonomialFourierTerm (M : ℕ) (hM : 2 ≤ M)
    (s : Finset ℤ) (c : ℝ) (h : ℤ) : ℂ :=
  boundaryKernelFourierCoefficient M hM h *
    ∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * t ^ c) n

theorem boundaryKernelMonomial_zero_mode_bound (M : ℕ) (hM : 2 ≤ M)
    (s : Finset ℤ) (c : ℝ) :
    ‖boundaryKernelMonomialFourierTerm M hM s c 0‖ ≤
      ((2 * (1 + (Real.log 4)⁻¹)) *
        Real.log (2 * (M : ℝ)) / (M : ℝ)) * (s.card : ℝ) := by
  rw [boundaryKernelMonomialFourierTerm, norm_mul]
  have hphase : (∑ n ∈ s,
      realExponentialPhase (fun t => ((0 : ℤ) : ℝ) * t ^ c) n) =
        ((s.card : ℝ) : ℂ) := by
    simp [realExponentialPhase]
  rw [hphase, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right
    (boundaryKernelFourierCoefficient_uniform_bound M hM 0) (by positivity)

theorem sum_floorBoundaryKernel_monomial_cutoff_decomposition
    (M H : ℕ) (hM : 2 ≤ M) (s : Finset ℤ) (c : ℝ) :
    ∑ n ∈ s, (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ) =
      boundaryKernelMonomialFourierTerm M hM s c 0 +
        ((∑ k ∈ Finset.range H,
            boundaryKernelMonomialFourierTerm M hM s c (k + 1)) +
          ∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM s c
            (k + H + 1)) +
        ((∑ k ∈ Finset.range H,
            boundaryKernelMonomialFourierTerm M hM s c (-(k + 1))) +
          ∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM s c
            (-(k + H + 1))) := by
  let f : ℤ → ℂ := fun h => boundaryKernelFourierCoefficient M hM h *
    ∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * t ^ c) n
  have hf : Summable f := by
    simpa [f, smul_eq_mul] using
      boundaryKernel_monomial_fourier_terms_summable M hM s c
  rw [sum_floorBoundaryKernel_monomial_eq_tsum M hM s c]
  simpa [f, boundaryKernelMonomialFourierTerm, smul_eq_mul,
    Nat.cast_add, Nat.cast_one] using
    tsum_int_complex_cutoff_decomposition hf H

theorem boundaryKernelFourierCoefficient_norm_tsum_le_cutoff (M H : ℕ)
    (hM : 2 ≤ M) (hH : 1 ≤ H) :
    (∑' h : ℤ, ‖boundaryKernelFourierCoefficient M hM h‖) ≤
      (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) / (M : ℝ) +
        2 * ((H : ℝ) *
          ((2 * (1 + (Real.log 4)⁻¹)) *
            Real.log (2 * (M : ℝ)) / (M : ℝ)) + (M : ℝ) / (H : ℝ)) := by
  let f : ℤ → ℝ := fun h => ‖boundaryKernelFourierCoefficient M hM h‖
  let A : ℝ := (2 * (1 + (Real.log 4)⁻¹)) *
    Real.log (2 * (M : ℝ)) / (M : ℝ)
  have hfs : Summable f := by
    simpa [f] using boundaryKernelFourierCoefficient_norm_summable M hM
  have hpos : Summable (fun n : ℕ => f (n + 1)) := by
    exact hfs.comp_injective (fun m n h => by
      have hm : m + 1 = n + 1 := by exact_mod_cast h
      omega)
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
    exact hfs.comp_injective (fun m n h => by
      have hc : ((m + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := neg_inj.mp h
      have hm : m + 1 = n + 1 := by exact_mod_cast hc
      omega)
  have hposTail : Summable (fun n : ℕ => f (n + H + 1)) := by
    exact hpos.comp_injective (fun m n h => by omega)
  have hnegTail : Summable (fun n : ℕ => f (-(n + H + 1))) := by
    exact hneg.comp_injective (fun m n h => by omega)
  have hposSquare : Summable (fun n : ℕ =>
      1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) := by
    have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow).2 (by norm_num : 1 < 2)
    have hshift := (summable_nat_add_iff (H + 1)).2 hbase
    exact hshift.congr fun n => by
      simp only [Nat.cast_add, Nat.cast_one]
      congr 1
      push_cast
      ring
  have hlowPos : (∑ n ∈ Finset.range H, f (n + 1)) ≤ (H : ℝ) * A := by
    calc
      (∑ n ∈ Finset.range H, f (n + 1)) ≤
          ∑ _n ∈ Finset.range H, A := by
        apply Finset.sum_le_sum
        intro n hn
        dsimp [f, A]
        exact boundaryKernelFourierCoefficient_uniform_bound M hM (n + 1)
      _ = (H : ℝ) * A := by simp [Finset.sum_const, nsmul_eq_mul]
  have hlowNeg : (∑ n ∈ Finset.range H, f (-(n + 1))) ≤ (H : ℝ) * A := by
    calc
      (∑ n ∈ Finset.range H, f (-(n + 1))) ≤
          ∑ _n ∈ Finset.range H, A := by
        apply Finset.sum_le_sum
        intro n hn
        dsimp [f, A]
        exact boundaryKernelFourierCoefficient_uniform_bound M hM (-(n + 1))
      _ = (H : ℝ) * A := by simp [Finset.sum_const, nsmul_eq_mul]
  have hposTailBound : (∑' n : ℕ, f (n + H + 1)) ≤ (M : ℝ) / (H : ℝ) := by
    calc
      (∑' n : ℕ, f (n + H + 1)) ≤
          ∑' n : ℕ, (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2 :=
        hposTail.tsum_le_tsum (fun n => by
          have hneq : ((n + H + 1 : ℕ) : ℤ) ≠ 0 := by omega
          have hdecay := boundaryKernelFourierCoefficient_norm_le_M_div_h_sq
            M hM hneq
          simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm,
            add_comm, div_eq_mul_inv] using hdecay) (by
              simpa [div_eq_mul_inv] using hposSquare.mul_left (M : ℝ))
      _ ≤ (M : ℝ) / (H : ℝ) := by
        have hMnonneg : 0 ≤ (M : ℝ) := by positivity
        calc
          (∑' n : ℕ, (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2) =
              (M : ℝ) * (∑' n : ℕ,
                1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) := by
            simpa [div_eq_mul_inv] using
              (Summable.tsum_mul_left (M : ℝ) hposSquare)
          _ ≤ (M : ℝ) * (1 / (H : ℝ)) :=
            mul_le_mul_of_nonneg_left (tsum_inv_sq_shifted_le H hH) hMnonneg
          _ = (M : ℝ) / (H : ℝ) := by ring
  have hnegTailBound : (∑' n : ℕ, f (-(n + H + 1))) ≤ (M : ℝ) / (H : ℝ) := by
    calc
      (∑' n : ℕ, f (-(n + H + 1))) ≤
          ∑' n : ℕ, (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2 :=
        hnegTail.tsum_le_tsum (fun n => by
          have hneq : -((n + H + 1 : ℕ) : ℤ) ≠ 0 := by omega
          have hdecay := boundaryKernelFourierCoefficient_norm_le_M_div_h_sq
            M hM hneq
          simp only [f, Int.cast_neg, Int.cast_natCast, Nat.cast_add,
            Nat.cast_one] at hdecay
          ring_nf at hdecay
          change ‖boundaryKernelFourierCoefficient M hM
            (-((n : ℤ) + (H : ℤ) + 1))‖ ≤
              (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2
          have hfreq : -((n : ℤ) + (H : ℤ) + 1) =
              -1 - (n : ℤ) - (H : ℤ) := by ring
          rw [hfreq]
          calc
            ‖boundaryKernelFourierCoefficient M hM
                (-1 - (n : ℤ) - (H : ℤ))‖ ≤
              (M : ℝ) * ((1 + (n : ℝ) + (H : ℝ))⁻¹) ^ 2 := by
                simpa [inv_pow] using hdecay
            _ = (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2 := by
              have hbases : 1 + (n : ℝ) + (H : ℝ) =
                  ((H + n + 1 : ℕ) : ℝ) := by push_cast; ring
              rw [hbases]
              simp [div_eq_mul_inv, inv_pow]) (by
              simpa [div_eq_mul_inv] using hposSquare.mul_left (M : ℝ))
      _ ≤ (M : ℝ) / (H : ℝ) := by
        have hMnonneg : 0 ≤ (M : ℝ) := by positivity
        calc
          (∑' n : ℕ, (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2) =
              (M : ℝ) * (∑' n : ℕ,
                1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) := by
            simpa [div_eq_mul_inv] using
              (Summable.tsum_mul_left (M : ℝ) hposSquare)
          _ ≤ (M : ℝ) * (1 / (H : ℝ)) :=
            mul_le_mul_of_nonneg_left (tsum_inv_sq_shifted_le H hH) hMnonneg
          _ = (M : ℝ) / (H : ℝ) := by ring
  rw [tsum_int_eq_zero_add_pos_and_neg hfs,
    ← hpos.sum_add_tsum_nat_add H, ← hneg.sum_add_tsum_nat_add H]
  have hzero : f 0 ≤ A := by
    dsimp [f, A]
    exact boundaryKernelFourierCoefficient_uniform_bound M hM 0
  dsimp [f, A] at *
  linarith [hlowPos, hlowNeg, hposTailBound, hnegTailBound, hzero]

/-! The two tails beyond a positive integer frequency cutoff are controlled
directly by the `M / |h|^2` coefficient decay. -/
theorem boundaryKernelFourierCoefficient_two_sided_tail (M H : ℕ)
    (hM : 2 ≤ M) (hH : 1 ≤ H) :
    (∑' n : ℕ, ‖boundaryKernelFourierCoefficient M hM
        ((n + H + 1 : ℕ) : ℤ)‖) +
      (∑' n : ℕ, ‖boundaryKernelFourierCoefficient M hM
        (-((n + H + 1 : ℕ) : ℤ))‖) ≤ 2 * (M : ℝ) / (H : ℝ) := by
  let f : ℤ → ℝ := fun h => ‖boundaryKernelFourierCoefficient M hM h‖
  have hfs : Summable f := by
    simpa [f] using boundaryKernelFourierCoefficient_norm_summable M hM
  have hpos : Summable (fun n : ℕ => f (n + 1)) := by
    exact hfs.comp_injective (fun m n h => by
      have hm : m + 1 = n + 1 := by exact_mod_cast h
      omega)
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
    exact hfs.comp_injective (fun m n h => by
      have hc : ((m + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := neg_inj.mp h
      have hm : m + 1 = n + 1 := by exact_mod_cast hc
      omega)
  have hposTail : Summable (fun n : ℕ => f (n + H + 1)) :=
    hpos.comp_injective (fun m n h => by omega)
  have hnegTail : Summable (fun n : ℕ => f (-(n + H + 1))) :=
    hneg.comp_injective (fun m n h => by omega)
  have hsquare : Summable (fun n : ℕ =>
      1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) := by
    have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow).2 (by norm_num : 1 < 2)
    have hshift := (summable_nat_add_iff (H + 1)).2 hbase
    exact hshift.congr fun n => by
      simp only [Nat.cast_add, Nat.cast_one]
      congr 1
      push_cast
      ring
  have hposBound : (∑' n : ℕ, f (n + H + 1)) ≤ (M : ℝ) / (H : ℝ) := by
    calc
      (∑' n : ℕ, f (n + H + 1)) ≤
          ∑' n : ℕ, (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2 :=
        hposTail.tsum_le_tsum (fun n => by
          have hneq : ((n + H + 1 : ℕ) : ℤ) ≠ 0 := by omega
          have hdecay := boundaryKernelFourierCoefficient_norm_le_M_div_h_sq
            M hM hneq
          simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm,
            add_comm, div_eq_mul_inv] using hdecay)
          (by simpa [div_eq_mul_inv] using hsquare.mul_left (M : ℝ))
      _ ≤ (M : ℝ) / (H : ℝ) := by
        have hMnonneg : 0 ≤ (M : ℝ) := by positivity
        calc
          (∑' n : ℕ, (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2) =
              (M : ℝ) * (∑' n : ℕ,
                1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) := by
            simpa [div_eq_mul_inv] using
              (Summable.tsum_mul_left (M : ℝ) hsquare)
          _ ≤ (M : ℝ) * (1 / (H : ℝ)) :=
            mul_le_mul_of_nonneg_left (tsum_inv_sq_shifted_le H hH) hMnonneg
          _ = (M : ℝ) / (H : ℝ) := by ring
  have hnegBound : (∑' n : ℕ, f (-(n + H + 1))) ≤ (M : ℝ) / (H : ℝ) := by
    calc
      (∑' n : ℕ, f (-(n + H + 1))) ≤
          ∑' n : ℕ, (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2 :=
        hnegTail.tsum_le_tsum (fun n => by
          have hneq : -((n + H + 1 : ℕ) : ℤ) ≠ 0 := by omega
          have hdecay := boundaryKernelFourierCoefficient_norm_le_M_div_h_sq
            M hM hneq
          simp only [f, Int.cast_neg, Int.cast_natCast, Nat.cast_add,
            Nat.cast_one] at hdecay
          ring_nf at hdecay
          change ‖boundaryKernelFourierCoefficient M hM
            (-((n : ℤ) + (H : ℤ) + 1))‖ ≤
              (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2
          have hfreq : -((n : ℤ) + (H : ℤ) + 1) =
              -1 - (n : ℤ) - (H : ℤ) := by ring
          rw [hfreq]
          calc
            ‖boundaryKernelFourierCoefficient M hM
                (-1 - (n : ℤ) - (H : ℤ))‖ ≤
              (M : ℝ) * ((1 + (n : ℝ) + (H : ℝ))⁻¹) ^ 2 := by
                simpa [inv_pow] using hdecay
            _ = (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2 := by
              have hbases : 1 + (n : ℝ) + (H : ℝ) =
                  ((H + n + 1 : ℕ) : ℝ) := by push_cast; ring
              rw [hbases]
              simp [div_eq_mul_inv, inv_pow])
          (by simpa [div_eq_mul_inv] using hsquare.mul_left (M : ℝ))
      _ ≤ (M : ℝ) / (H : ℝ) := by
        have hMnonneg : 0 ≤ (M : ℝ) := by positivity
        calc
          (∑' n : ℕ, (M : ℝ) / ((H + n + 1 : ℕ) : ℝ) ^ 2) =
              (M : ℝ) * (∑' n : ℕ,
                1 / ((H + n + 1 : ℕ) : ℝ) ^ 2) := by
            simpa [div_eq_mul_inv] using
              (Summable.tsum_mul_left (M : ℝ) hsquare)
          _ ≤ (M : ℝ) * (1 / (H : ℝ)) :=
            mul_le_mul_of_nonneg_left (tsum_inv_sq_shifted_le H hH) hMnonneg
          _ = (M : ℝ) / (H : ℝ) := by ring
  have hposEq : (∑' n : ℕ, f (n + H + 1)) =
      ∑' n : ℕ, ‖boundaryKernelFourierCoefficient M hM
        ((n + H + 1 : ℕ) : ℤ)‖ := by rfl
  have hnegEq : (∑' n : ℕ, f (-(n + H + 1))) =
      ∑' n : ℕ, ‖boundaryKernelFourierCoefficient M hM
        (-((n + H + 1 : ℕ) : ℤ))‖ := by rfl
  rw [← hposEq, ← hnegEq]
  calc
    (∑' n : ℕ, f (n + H + 1)) +
        (∑' n : ℕ, f (-(n + H + 1))) ≤
      (M : ℝ) / (H : ℝ) + (M : ℝ) / (H : ℝ) :=
        add_le_add hposBound hnegBound
    _ = 2 * (M : ℝ) / (H : ℝ) := by ring

/-- The two phase-weighted Fourier tails are bounded by the sample-set
cardinality times the two-sided coefficient tail. -/
theorem boundaryKernel_monomial_weighted_two_sided_tail_bound
    (M H : ℕ) (hM : 2 ≤ M) (hH : 1 ≤ H)
    (s : Finset ℤ) (c : ℝ) :
    ‖∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM s c
        ((k + H + 1 : ℕ) : ℤ)‖ +
      ‖∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM s c
        (-((k + H + 1 : ℕ) : ℤ))‖ ≤
      (s.card : ℝ) * (2 * (M : ℝ) / (H : ℝ)) := by
  let coeffNorm : ℤ → ℝ := fun h =>
    ‖boundaryKernelFourierCoefficient M hM h‖
  let posFreq : ℕ → ℤ := fun k => ((k + H + 1 : ℕ) : ℤ)
  let negFreq : ℕ → ℤ := fun k => -((k + H + 1 : ℕ) : ℤ)
  let posTerm : ℕ → ℂ := fun k =>
    boundaryKernelMonomialFourierTerm M hM s c (posFreq k)
  let negTerm : ℕ → ℂ := fun k =>
    boundaryKernelMonomialFourierTerm M hM s c (negFreq k)
  have hcoeff : Summable coeffNorm := by
    simpa [coeffNorm] using boundaryKernelFourierCoefficient_norm_summable M hM
  have hposFreqInj : Function.Injective posFreq := by
    intro m n h
    dsimp [posFreq] at h
    have hn : m + H + 1 = n + H + 1 := by exact_mod_cast h
    omega
  have hnegFreqInj : Function.Injective negFreq := by
    intro m n h
    dsimp [negFreq] at h
    have hc : ((m + H + 1 : ℕ) : ℤ) = ((n + H + 1 : ℕ) : ℤ) := neg_inj.mp h
    have hn : m + H + 1 = n + H + 1 := by exact_mod_cast hc
    omega
  have hterms := boundaryKernel_monomial_fourier_terms_summable M hM s c
  have hposTerms : Summable posTerm := by
    exact hterms.comp_injective hposFreqInj
  have hnegTerms : Summable negTerm := by
    exact hterms.comp_injective hnegFreqInj
  have hposCoeffs : Summable (fun k : ℕ => coeffNorm (posFreq k)) :=
    hcoeff.comp_injective hposFreqInj
  have hnegCoeffs : Summable (fun k : ℕ => coeffNorm (negFreq k)) :=
    hcoeff.comp_injective hnegFreqInj
  have hphaseNorm (h : ℤ) :
      ‖∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤ s.card := by
    calc
      ‖∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤
          ∑ n ∈ s, ‖realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ :=
        norm_sum_le s _
      _ = s.card := by simp [norm_realExponentialPhase]
  have hposPoint (k : ℕ) : ‖posTerm k‖ ≤
      (s.card : ℝ) * coeffNorm (posFreq k) := by
    change ‖boundaryKernelFourierCoefficient M hM (posFreq k) *
      ∑ n ∈ s, realExponentialPhase
        (fun t => (posFreq k : ℝ) * t ^ c) n‖ ≤ _
    rw [norm_mul]
    dsimp [coeffNorm]
    calc
      ‖boundaryKernelFourierCoefficient M hM (posFreq k)‖ *
          ‖∑ n ∈ s, realExponentialPhase
            (fun t => (posFreq k : ℝ) * t ^ c) n‖ ≤
        ‖boundaryKernelFourierCoefficient M hM (posFreq k)‖ * s.card :=
          mul_le_mul_of_nonneg_left (hphaseNorm (posFreq k)) (norm_nonneg _)
      _ = (s.card : ℝ) *
          ‖boundaryKernelFourierCoefficient M hM (posFreq k)‖ := by ring
  have hnegPoint (k : ℕ) : ‖negTerm k‖ ≤
      (s.card : ℝ) * coeffNorm (negFreq k) := by
    change ‖boundaryKernelFourierCoefficient M hM (negFreq k) *
      ∑ n ∈ s, realExponentialPhase
        (fun t => (negFreq k : ℝ) * t ^ c) n‖ ≤ _
    rw [norm_mul]
    dsimp [coeffNorm]
    calc
      ‖boundaryKernelFourierCoefficient M hM (negFreq k)‖ *
          ‖∑ n ∈ s, realExponentialPhase
            (fun t => (negFreq k : ℝ) * t ^ c) n‖ ≤
        ‖boundaryKernelFourierCoefficient M hM (negFreq k)‖ * s.card :=
          mul_le_mul_of_nonneg_left (hphaseNorm (negFreq k)) (norm_nonneg _)
      _ = (s.card : ℝ) *
          ‖boundaryKernelFourierCoefficient M hM (negFreq k)‖ := by ring
  have hposNorm : ‖∑' k : ℕ, posTerm k‖ ≤
      (s.card : ℝ) * ∑' k : ℕ, coeffNorm (posFreq k) := by
    calc
      ‖∑' k : ℕ, posTerm k‖ ≤ ∑' k : ℕ, ‖posTerm k‖ :=
        norm_tsum_le_tsum_norm hposTerms.norm
      _ ≤ ∑' k : ℕ, (s.card : ℝ) * coeffNorm (posFreq k) :=
        hposTerms.norm.tsum_le_tsum hposPoint
          (hposCoeffs.mul_left (s.card : ℝ))
      _ = (s.card : ℝ) * ∑' k : ℕ, coeffNorm (posFreq k) := by
        exact (Summable.tsum_mul_left (s.card : ℝ) hposCoeffs)
  have hnegNorm : ‖∑' k : ℕ, negTerm k‖ ≤
      (s.card : ℝ) * ∑' k : ℕ, coeffNorm (negFreq k) := by
    calc
      ‖∑' k : ℕ, negTerm k‖ ≤ ∑' k : ℕ, ‖negTerm k‖ :=
        norm_tsum_le_tsum_norm hnegTerms.norm
      _ ≤ ∑' k : ℕ, (s.card : ℝ) * coeffNorm (negFreq k) :=
        hnegTerms.norm.tsum_le_tsum hnegPoint
          (hnegCoeffs.mul_left (s.card : ℝ))
      _ = (s.card : ℝ) * ∑' k : ℕ, coeffNorm (negFreq k) := by
        exact (Summable.tsum_mul_left (s.card : ℝ) hnegCoeffs)
  have hcoeffTail := boundaryKernelFourierCoefficient_two_sided_tail M H hM hH
  have hcoeffTail' :
      (∑' k : ℕ, coeffNorm (posFreq k)) +
        (∑' k : ℕ, coeffNorm (negFreq k)) ≤
          2 * (M : ℝ) / (H : ℝ) := by
    simpa [coeffNorm, posFreq, negFreq] using hcoeffTail
  have hcardNonneg : 0 ≤ (s.card : ℝ) := by positivity
  calc
    ‖∑' k : ℕ, posTerm k‖ + ‖∑' k : ℕ, negTerm k‖ ≤
        (s.card : ℝ) * ∑' k : ℕ, coeffNorm (posFreq k) +
          (s.card : ℝ) * ∑' k : ℕ, coeffNorm (negFreq k) :=
      add_le_add hposNorm hnegNorm
    _ = (s.card : ℝ) *
        ((∑' k : ℕ, coeffNorm (posFreq k)) +
          (∑' k : ℕ, coeffNorm (negFreq k))) := by ring
    _ ≤ (s.card : ℝ) * (2 * (M : ℝ) / (H : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoeffTail' hcardNonneg

/-- The same two-sided coefficient tail bound for samples of the dilated
monomial `(d*n)^c`; reindex the sample set by multiplication by `d`. -/
theorem boundaryKernel_dilated_monomial_weighted_two_sided_tail_bound
    (M H d : ℕ) (hM : 2 ≤ M) (hH : 1 ≤ H) (hd : 1 ≤ d)
    (s : Finset ℤ) (c : ℝ) :
    ‖∑' k : ℕ, boundaryKernelFourierCoefficient M hM
        ((k + H + 1 : ℕ) : ℤ) *
          ∑ n ∈ s, realExponentialPhase
            (fun t => ((k + H + 1 : ℕ) : ℝ) * ((d : ℝ) * t) ^ c) n‖ +
      ‖∑' k : ℕ, boundaryKernelFourierCoefficient M hM
        (-((k + H + 1 : ℕ) : ℤ)) *
          ∑ n ∈ s, realExponentialPhase
            (fun t => (-((k + H + 1 : ℕ) : ℤ) : ℝ) * ((d : ℝ) * t) ^ c) n‖ ≤
      (s.card : ℝ) * (2 * (M : ℝ) / (H : ℝ)) := by
  let dilate : ℤ → ℤ := fun n => (d : ℤ) * n
  let s' : Finset ℤ := s.image dilate
  have hdne : (d : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one hd))
  have hinj : Set.InjOn dilate (↑s) := by
    intro x hx y hy hxy
    exact mul_left_cancel₀ hdne (by simpa [dilate] using hxy)
  have hterm (h : ℤ) :
      boundaryKernelMonomialFourierTerm M hM s' c h =
        boundaryKernelFourierCoefficient M hM h *
          ∑ n ∈ s, realExponentialPhase
            (fun t => (h : ℝ) * ((d : ℝ) * t) ^ c) n := by
    rw [boundaryKernelMonomialFourierTerm]
    dsimp [s']
    rw [Finset.sum_image hinj]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simp only [dilate]
    unfold realExponentialPhase
    congr 1
    push_cast
    ring
  have hposEq :
      (∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c
        ((k + H + 1 : ℕ) : ℤ)) =
      ∑' k : ℕ, boundaryKernelFourierCoefficient M hM
        ((k + H + 1 : ℕ) : ℤ) *
          ∑ n ∈ s, realExponentialPhase
            (fun t => ((k + H + 1 : ℕ) : ℝ) * ((d : ℝ) * t) ^ c) n := by
    apply tsum_congr
    intro k
    exact hterm _
  have hnegEq :
      (∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c
        (-((k + H + 1 : ℕ) : ℤ))) =
      ∑' k : ℕ, boundaryKernelFourierCoefficient M hM
        (-((k + H + 1 : ℕ) : ℤ)) *
          ∑ n ∈ s, realExponentialPhase
            (fun t => (-((k + H + 1 : ℕ) : ℤ) : ℝ) * ((d : ℝ) * t) ^ c) n := by
    apply tsum_congr
    intro k
    simpa using hterm (-((k + H + 1 : ℕ) : ℤ))
  have htail := boundaryKernel_monomial_weighted_two_sided_tail_bound
    M H hM hH s' c
  rw [hposEq, hnegEq] at htail
  have hcard : s'.card ≤ s.card := Finset.card_image_le
  have hfactor : 0 ≤ 2 * (M : ℝ) / (H : ℝ) := by positivity
  calc
    _ ≤ (s'.card : ℝ) * (2 * (M : ℝ) / (H : ℝ)) := htail
    _ ≤ (s.card : ℝ) * (2 * (M : ℝ) / (H : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hfactor

/-- After the exact progression normalization, the two dilated high-frequency
tails contribute at most `2M/H`. -/
theorem boundaryKernel_progression_high_modes_normalized_bound
    (M H d : ℕ) (hM : 2 ≤ M) (hH : 1 ≤ H) (hd : 1 ≤ d)
    {N c : ℝ} (hN : 0 < N) :
    ((d : ℝ) / N) *
      (‖∑' k : ℕ, boundaryKernelFourierCoefficient M hM
          ((k + H + 1 : ℕ) : ℤ) *
            ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
              realExponentialPhase
                (fun t => ((k + H + 1 : ℕ) : ℝ) * ((d : ℝ) * t) ^ c) n‖ +
        ‖∑' k : ℕ, boundaryKernelFourierCoefficient M hM
          (-((k + H + 1 : ℕ) : ℤ)) *
            ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
              realExponentialPhase
                (fun t => (-((k + H + 1 : ℕ) : ℤ) : ℝ) * ((d : ℝ) * t) ^ c) n‖) ≤
      2 * (M : ℝ) / (H : ℝ) := by
  let s : Finset ℤ := realIntegerInterval 0 (N / (d : ℝ))
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hNd : 0 ≤ N / (d : ℝ) := by positivity
  have hcard : (s.card : ℝ) ≤ N / (d : ℝ) := by
    simpa [s] using realIntegerInterval_zero_card_le (N / (d : ℝ)) hNd
  have hraw := boundaryKernel_dilated_monomial_weighted_two_sided_tail_bound
    M H d hM hH hd s c
  have hscale : 0 ≤ (d : ℝ) / N := le_of_lt (div_pos hdreal hN)
  calc
    ((d : ℝ) / N) *
        (‖∑' k : ℕ, boundaryKernelFourierCoefficient M hM
            ((k + H + 1 : ℕ) : ℤ) *
              ∑ n ∈ s, realExponentialPhase
                (fun t => ((k + H + 1 : ℕ) : ℝ) * ((d : ℝ) * t) ^ c) n‖ +
          ‖∑' k : ℕ, boundaryKernelFourierCoefficient M hM
            (-((k + H + 1 : ℕ) : ℤ)) *
              ∑ n ∈ s, realExponentialPhase
                (fun t => (-((k + H + 1 : ℕ) : ℤ) : ℝ) * ((d : ℝ) * t) ^ c) n‖) ≤
        ((d : ℝ) / N) * ((s.card : ℝ) * (2 * (M : ℝ) / (H : ℝ))) :=
      mul_le_mul_of_nonneg_left hraw hscale
    _ ≤ ((d : ℝ) / N) * ((N / (d : ℝ)) *
          (2 * (M : ℝ) / (H : ℝ))) := by
          gcongr
    _ = 2 * (M : ℝ) / (H : ℝ) := by
          field_simp
          <;> ring

/-- Exact Fourier cutoff decomposition of the boundary-kernel sum on the
dilated progression, obtained by reindexing the samples before applying the
already checked monomial decomposition. -/
theorem sum_floorBoundaryKernel_dilated_monomial_cutoff_decomposition
    (M H d : ℕ) (hM : 2 ≤ M) (hd : 1 ≤ d)
    (s : Finset ℤ) (c : ℝ) :
    ∑ n ∈ s,
        (floorBoundaryKernel M hM
          (((d : ℝ) * (n : ℝ)) ^ c) : ℂ) =
      boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c 0 +
        ((∑ k ∈ Finset.range H,
            boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c (k + 1)) +
          ∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c
            (k + H + 1)) +
        ((∑ k ∈ Finset.range H,
            boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c (-(k + 1))) +
          ∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c
            (-(k + H + 1))) := by
  let dilate : ℤ → ℤ := fun n => (d : ℤ) * n
  let s' : Finset ℤ := s.image dilate
  have hdne : (d : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one hd))
  have hinj : Set.InjOn dilate (↑s) := by
    intro x hx y hy hxy
    exact mul_left_cancel₀ hdne (by simpa [dilate] using hxy)
  have hsum :
      (∑ n ∈ s,
        (floorBoundaryKernel M hM (((d : ℝ) * (n : ℝ)) ^ c) : ℂ)) =
        ∑ n ∈ s', (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ) := by
    dsimp [s']
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have hcast : ((dilate n : ℤ) : ℝ) = (d : ℝ) * (n : ℝ) := by
      simp [dilate]
    rw [hcast]
  calc
    _ = ∑ n ∈ s', (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ) := hsum
    _ = boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c 0 +
        ((∑ k ∈ Finset.range H,
            boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c (k + 1)) +
          ∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c
            (k + H + 1)) +
        ((∑ k ∈ Finset.range H,
            boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c (-(k + 1))) +
          ∑' k : ℕ, boundaryKernelMonomialFourierTerm M hM (s.image (fun n : ℤ => (d : ℤ) * n)) c
            (-(k + H + 1))) := by
          simpa [s'] using
            (sum_floorBoundaryKernel_monomial_cutoff_decomposition
              M H hM s' c)

/-- Reindex one Fourier term from the dilated sample image back to its
original progression indices. -/
theorem boundaryKernelMonomialFourierTerm_dilated
    (M d : ℕ) (hM : 2 ≤ M) (hd : 1 ≤ d)
    (s : Finset ℤ) (c : ℝ) (h : ℤ) :
    boundaryKernelMonomialFourierTerm M hM
        (s.image (fun n : ℤ => (d : ℤ) * n)) c h =
      boundaryKernelFourierCoefficient M hM h *
        ∑ n ∈ s, realExponentialPhase
          (fun t => (h : ℝ) * ((d : ℝ) * t) ^ c) n := by
  let dilate : ℤ → ℤ := fun n => (d : ℤ) * n
  have hdne : (d : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one hd))
  have hinj : Set.InjOn dilate (↑s) := by
    intro x hx y hy hxy
    exact mul_left_cancel₀ hdne (by simpa [dilate] using hxy)
  rw [boundaryKernelMonomialFourierTerm]
  rw [Finset.sum_image hinj]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [dilate]
  unfold realExponentialPhase
  congr 1
  push_cast
  ring

/-- Pre-absorption progression estimate: once the finite low-frequency block
has its monomial cancellation bound, the zero and high modes give the other
two terms of the boundary-error estimate. -/
theorem boundaryKernel_progression_preabs_bound
    (M H d : ℕ) (hM : 2 ≤ M) (hH : 1 ≤ H) (hd : 1 ≤ d)
    {N c B : ℝ} (hN : 0 < N) (hB : 0 ≤ B)
    (hLow : ((d : ℝ) / N) *
      ‖((∑ k ∈ Finset.range H,
          boundaryKernelFourierCoefficient M hM
            ((k + 1 : ℕ) : ℤ) *
            ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
              realExponentialPhase
                (fun t => ((k + 1 : ℕ) : ℝ) * ((d : ℝ) * t) ^ c) n) +
        (∑ k ∈ Finset.range H,
          boundaryKernelFourierCoefficient M hM
            (-((k + 1 : ℕ) : ℤ)) *
            ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
              realExponentialPhase
                (fun t => (-((k + 1 : ℕ) : ℤ) : ℝ) * ((d : ℝ) * t) ^ c) n))‖ ≤ B) :
    ((d : ℝ) / N) *
      ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
        (floorBoundaryKernel M hM
          (((d : ℝ) * (n : ℝ)) ^ c) : ℂ)‖ ≤
      (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) / (M : ℝ) +
        B + 2 * (M : ℝ) / (H : ℝ) := by
  let s : Finset ℤ := realIntegerInterval 0 (N / (d : ℝ))
  let term : ℤ → ℂ := fun h =>
    boundaryKernelFourierCoefficient M hM h *
      ∑ n ∈ s, realExponentialPhase
        (fun t => (h : ℝ) * ((d : ℝ) * t) ^ c) n
  let z : ℂ := term 0
  let lowPos : ℂ := ∑ k ∈ Finset.range H, term ((k + 1 : ℕ) : ℤ)
  let lowNeg : ℂ := ∑ k ∈ Finset.range H, term (-((k + 1 : ℕ) : ℤ))
  let tailPos : ℂ := ∑' k : ℕ, term ((k + H + 1 : ℕ) : ℤ)
  let tailNeg : ℂ := ∑' k : ℕ, term (-((k + H + 1 : ℕ) : ℤ))
  have hterm (h : ℤ) :
      boundaryKernelMonomialFourierTerm M hM
        (s.image (fun n : ℤ => (d : ℤ) * n)) c h = term h := by
    simpa [term, s] using
      boundaryKernelMonomialFourierTerm_dilated M d hM hd s c h
  have hdec0 := sum_floorBoundaryKernel_dilated_monomial_cutoff_decomposition
    M H d hM hd s c
  have hdec :
      (∑ n ∈ s, (floorBoundaryKernel M hM
        (((d : ℝ) * (n : ℝ)) ^ c) : ℂ)) =
        (z + (lowPos + tailPos)) + (lowNeg + tailNeg) := by
    have hdec' := hdec0
    simp only [hterm] at hdec'
    rw [hdec']
    dsimp [z, lowPos, lowNeg, tailPos, tailNeg]
  have hscale : 0 ≤ (d : ℝ) / N := by positivity
  have hdNat : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdreal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdNat
  have hz := boundaryKernel_progression_zero_mode_bound (c := c) M hM hN
    hdreal
  have hz' : ((d : ℝ) / N) * ‖z‖ ≤
      (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) / (M : ℝ) := by
    simpa [z, term, s, realExponentialPhase] using hz
  have htail := boundaryKernel_progression_high_modes_normalized_bound (c := c)
    M H d hM hH hd hN
  have htail' : ((d : ℝ) / N) *
      (‖tailPos‖ + ‖tailNeg‖) ≤ 2 * (M : ℝ) / (H : ℝ) := by
    simpa [tailPos, tailNeg, term, s] using htail
  have hLow' : ((d : ℝ) / N) * ‖lowPos + lowNeg‖ ≤ B := by
    simpa [lowPos, lowNeg, term, s] using hLow
  have hdecomp :
      (∑ n ∈ s, (floorBoundaryKernel M hM
        (((d : ℝ) * (n : ℝ)) ^ c) : ℂ)) =
        z + (lowPos + lowNeg) + (tailPos + tailNeg) := by
    rw [hdec]
    dsimp [z, lowPos, lowNeg, tailPos, tailNeg]
    abel
  have hnorm :
      ‖∑ n ∈ s, (floorBoundaryKernel M hM
        (((d : ℝ) * (n : ℝ)) ^ c) : ℂ)‖ ≤
      ‖z‖ + ‖lowPos + lowNeg‖ + ‖tailPos + tailNeg‖ := by
    rw [hdecomp]
    calc
      ‖z + (lowPos + lowNeg) + (tailPos + tailNeg)‖ ≤
          ‖z + (lowPos + lowNeg)‖ + ‖tailPos + tailNeg‖ := norm_add_le _ _
      _ ≤ (‖z‖ + ‖lowPos + lowNeg‖) + ‖tailPos + tailNeg‖ := by
        exact add_le_add_left (norm_add_le z (lowPos + lowNeg)) _
  have htailNorm : ((d : ℝ) / N) * ‖tailPos + tailNeg‖ ≤
      2 * (M : ℝ) / (H : ℝ) := by
    calc
      _ ≤ ((d : ℝ) / N) * (‖tailPos‖ + ‖tailNeg‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hscale
      _ ≤ 2 * (M : ℝ) / (H : ℝ) := htail'
  calc
    ((d : ℝ) / N) *
        ‖∑ n ∈ s, (floorBoundaryKernel M hM
          (((d : ℝ) * (n : ℝ)) ^ c) : ℂ)‖ ≤
        ((d : ℝ) / N) *
          (‖z‖ + ‖lowPos + lowNeg‖ + ‖tailPos + tailNeg‖) :=
      mul_le_mul_of_nonneg_left hnorm hscale
    _ = ((d : ℝ) / N) * ‖z‖ +
        ((d : ℝ) / N) * ‖lowPos + lowNeg‖ +
        ((d : ℝ) / N) * ‖tailPos + tailNeg‖ := by ring
    _ ≤ (2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) / (M : ℝ) +
          B + 2 * (M : ℝ) / (H : ℝ) := by
      simpa only [add_assoc] using
        add_le_add (add_le_add hz' hLow') htailNorm

/-- A finite family of Fourier modes whose phase sums are uniformly bounded
contributes at most that bound times the coefficient `ℓ¹` mass. -/
theorem norm_sum_fourier_modes_le_phase_bound_mul_coeff_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff phase : ι → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hphase : ∀ h ∈ s, ‖phase h‖ ≤ B) :
    ‖∑ h ∈ s, coeff h * phase h‖ ≤
      B * ∑ h ∈ s, ‖coeff h‖ := by
  calc
    ‖∑ h ∈ s, coeff h * phase h‖ ≤
        ∑ h ∈ s, ‖coeff h * phase h‖ :=
          norm_sum_le s (fun h => coeff h * phase h)
    _ ≤ ∑ h ∈ s, B * ‖coeff h‖ := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul]
      calc
        ‖coeff h‖ * ‖phase h‖ ≤ ‖coeff h‖ * B :=
          mul_le_mul_of_nonneg_left (hphase h hh) (norm_nonneg (coeff h))
        _ = B * ‖coeff h‖ := by ring
    _ = B * ∑ h ∈ s, ‖coeff h‖ := by
      rw [Finset.mul_sum]

theorem boundaryKernelFourierCoefficient_norm_tsum_le_sqrt_log (M : ℕ)
    (hM : 2 ≤ M) :
    (∑' h : ℤ, ‖boundaryKernelFourierCoefficient M hM h‖) ≤
      (5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
        Real.sqrt (Real.log (2 * (M : ℝ))) := by
  let L : ℝ := Real.log (2 * (M : ℝ))
  let K : ℝ := 2 * (1 + (Real.log 4)⁻¹)
  let A : ℝ := K * L / (M : ℝ)
  let x : ℝ := (M : ℝ) / Real.sqrt L
  let H : ℕ := Nat.ceil x
  have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : 0 < (M : ℝ) := by linarith
  have h2M : 1 < 2 * (M : ℝ) := by nlinarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos h2M
  have hspos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hsnonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hlogbound : L ≤ (M : ℝ) ^ 2 := by
    have hlog := Real.log_le_sub_one_of_pos (show 0 < 2 * (M : ℝ) by positivity)
    have hquad : 2 * (M : ℝ) - 1 ≤ (M : ℝ) ^ 2 := by nlinarith
    dsimp [L]
    linarith
  have hs_le_M : Real.sqrt L ≤ (M : ℝ) := by
    nlinarith [Real.sq_sqrt hLpos.le]
  have hL_div_M_le_sqrt : L / (M : ℝ) ≤ Real.sqrt L := by
    apply (div_le_iff₀ hMpos).2
    have hprod : 0 ≤ ((M : ℝ) - Real.sqrt L) * Real.sqrt L :=
      mul_nonneg (sub_nonneg.mpr hs_le_M) hsnonneg
    nlinarith [Real.sq_sqrt hLpos.le]
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hKnonneg : 0 ≤ K := le_of_lt hKpos
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos hMpos hspos
  have hx_le_H : x ≤ (H : ℝ) := by
    exact Nat.le_ceil x
  have hH_lt : (H : ℝ) < x + 1 := by
    exact Nat.ceil_lt_add_one hxpos.le
  have hHpos : 0 < H := Nat.ceil_pos.2 hxpos
  have hscale : x * A = K * Real.sqrt L := by
    dsimp [x, A]
    have hsquare : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
    field_simp [hMpos.ne', hspos.ne']
    rw [hsquare]
    <;> ring
  have hHmul : (H : ℝ) * A ≤ K * Real.sqrt L + A := by
    calc
      (H : ℝ) * A ≤ (x + 1) * A := mul_le_mul_of_nonneg_right hH_lt.le hApos.le
      _ = K * Real.sqrt L + A := by rw [← hscale]; ring
  have hMleHsqrt : (M : ℝ) ≤ (H : ℝ) * Real.sqrt L := by
    exact (div_le_iff₀ hspos).1 hx_le_H
  have htail : (M : ℝ) / (H : ℝ) ≤ Real.sqrt L := by
    apply (div_le_iff₀ (by exact_mod_cast hHpos : 0 < (H : ℝ))).2
    nlinarith [hMleHsqrt]
  have hA_le : A ≤ K * Real.sqrt L := by
    dsimp [A]
    calc
      K * L / (M : ℝ) = K * (L / (M : ℝ)) := by ring
      _ ≤ K * Real.sqrt L := mul_le_mul_of_nonneg_left hL_div_M_le_sqrt hKnonneg
  have hcut := boundaryKernelFourierCoefficient_norm_tsum_le_cutoff M H hM
    (by omega)
  change (∑' h : ℤ, ‖boundaryKernelFourierCoefficient M hM h‖) ≤
    A + 2 * ((H : ℝ) * A + (M : ℝ) / (H : ℝ)) at hcut
  calc
    (∑' h : ℤ, ‖boundaryKernelFourierCoefficient M hM h‖) ≤
        A + 2 * ((H : ℝ) * A + (M : ℝ) / (H : ℝ)) := hcut
    _ ≤ A + 2 * (K * Real.sqrt L + A + Real.sqrt L) := by
      gcongr
    _ ≤ (5 * K + 2) * Real.sqrt L := by nlinarith [hA_le]
    _ = (5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
        Real.sqrt (Real.log (2 * (M : ℝ))) := by simp [K, L]

/-- Low-frequency Fourier modes are bounded by their uniform phase-sum bound
times the established global coefficient `ℓ¹` estimate. -/
theorem boundaryKernel_low_frequency_sum_bound (M : ℕ) (hM : 2 ≤ M)
    (s : Finset ℤ) (phase : ℤ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hphase : ∀ h ∈ s, ‖phase h‖ ≤ B) :
    ‖∑ h ∈ s, boundaryKernelFourierCoefficient M hM h * phase h‖ ≤
      B * ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
        Real.sqrt (Real.log (2 * (M : ℝ)))) := by
  have hcoeff : Summable (fun h : ℤ =>
      ‖boundaryKernelFourierCoefficient M hM h‖) :=
    boundaryKernelFourierCoefficient_norm_summable M hM
  have hfinite : (∑ h ∈ s,
      ‖boundaryKernelFourierCoefficient M hM h‖) ≤
        ∑' h : ℤ, ‖boundaryKernelFourierCoefficient M hM h‖ := by
    exact hcoeff.sum_le_tsum s (fun h hh => norm_nonneg
      (boundaryKernelFourierCoefficient M hM h))
  calc
    ‖∑ h ∈ s,
        boundaryKernelFourierCoefficient M hM h * phase h‖ ≤
      B * ∑ h ∈ s, ‖boundaryKernelFourierCoefficient M hM h‖ :=
      norm_sum_fourier_modes_le_phase_bound_mul_coeff_sum s
        (fun h => boundaryKernelFourierCoefficient M hM h) phase B hB hphase
    _ ≤ B * ∑' h : ℤ, ‖boundaryKernelFourierCoefficient M hM h‖ :=
      mul_le_mul_of_nonneg_left hfinite hB
    _ ≤ B * ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
        Real.sqrt (Real.log (2 * (M : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (boundaryKernelFourierCoefficient_norm_tsum_le_sqrt_log M hM) hB

/-- A boundary-kernel Fourier block inherits the paper's monomial cancellation
estimate after the exact progression normalization. The frequency-range
obligations are explicit so the lemma can be instantiated with the precise
cutoff in `ar:boundary-error`. -/
theorem boundaryKernel_progression_low_modes_of_monomial_bound
    (M H : ℕ) (hM : 2 ≤ M) {N d c η : ℝ}
    (hN : 0 < N) (hd : 0 < d)
    (hfreq : ∀ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0},
      N ^ ((1 / 100 : ℝ) - c) ≤ |(h : ℝ)| ∧
        |(h : ℝ)| ≤ 2 * N ^ (1 / 10000 : ℝ))
    (hmono : ∀ β : ℝ,
      N ^ ((1 / 100 : ℝ) - c) ≤ |β| →
      |β| ≤ 2 * N ^ (1 / 10000 : ℝ) →
      (d / N) * ‖∑ n ∈ realIntegerInterval 0 (N / d),
        realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ ≤
        12 * N ^ (-16 * η)) :
    ‖∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0},
      boundaryKernelFourierCoefficient M hM h *
        (∑ n ∈ realIntegerInterval 0 (N / d),
          realExponentialPhase (fun t => (h : ℝ) * ((d : ℝ) * t) ^ c) n *
            ((d / N : ℝ) : ℂ))‖ ≤
      (12 * N ^ (-16 * η)) *
        ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
          Real.sqrt (Real.log (2 * (M : ℝ)))) := by
  let freqSet : Finset ℤ := Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0}
  let phase : ℤ → ℂ := fun h =>
    ∑ n ∈ realIntegerInterval 0 (N / d),
      realExponentialPhase (fun t => (h : ℝ) * ((d : ℝ) * t) ^ c) n *
        ((d / N : ℝ) : ℂ)
  let B : ℝ := 12 * N ^ (-16 * η)
  have hdscale : 0 ≤ d / N := le_of_lt (div_pos hd hN)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hphase : ∀ h ∈ freqSet, ‖phase h‖ ≤ B := by
    intro h hh
    have hβ := hfreq h (by simpa [freqSet] using hh)
    have hbound := hmono (h : ℝ) hβ.1 hβ.2
    have hnorm : ‖phase h‖ = (d / N) *
        ‖∑ n ∈ realIntegerInterval 0 (N / d),
          realExponentialPhase (fun t => (h : ℝ) * ((d : ℝ) * t) ^ c) n‖ := by
      dsimp [phase]
      rw [← Finset.sum_mul, norm_mul]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hd hN)]
      ring
    rw [hnorm]
    simpa [B] using hbound
  change ‖∑ h ∈ freqSet,
      boundaryKernelFourierCoefficient M hM h * phase h‖ ≤
    B * ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
      Real.sqrt (Real.log (2 * (M : ℝ))))
  exact boundaryKernel_low_frequency_sum_bound M hM freqSet phase B hB hphase

/-- Every nonzero integer frequency below the paper's cutoff lies in the
frequency range required by `monomial_cancellation`. -/
theorem monomial_cancellation_frequency_range
    {N c : ℝ} (hN : 1 ≤ N) (hc : 1 < c) (H : ℕ)
    (hH : (H : ℝ) ≤ N ^ (1 / 10000 : ℝ)) {h : ℤ}
    (hmem : h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ)) (hne : h ≠ 0) :
    N ^ ((1 / 100 : ℝ) - c) ≤ |(h : ℝ)| ∧
      |(h : ℝ)| ≤ 2 * N ^ (1 / 10000 : ℝ) := by
  have hpower : N ^ ((1 / 100 : ℝ) - c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hIntabs : 1 ≤ |(h : ℝ)| := by
    rcases lt_trichotomy h 0 with hneg | hzero | hpos
    · have hle : (h : ℝ) ≤ -1 := by exact_mod_cast (Int.le_sub_one_of_lt hneg)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · exact False.elim (hne hzero)
    · have hge : (1 : ℝ) ≤ (h : ℝ) := by
        exact_mod_cast (Int.add_one_le_of_lt hpos)
      rw [abs_of_nonneg (by linarith)]
      exact hge
  have hmem' := Finset.mem_Icc.mp hmem
  have habs : |(h : ℝ)| ≤ (H : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast hmem'.1
    · exact_mod_cast hmem'.2
  constructor
  · exact hpower.trans hIntabs
  · calc
      |(h : ℝ)| ≤ (H : ℝ) := habs
      _ ≤ N ^ (1 / 10000 : ℝ) := hH
      _ ≤ 2 * N ^ (1 / 10000 : ℝ) := by nlinarith [Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hN) (1 / 10000 : ℝ)]

/-- A finite frequency sequence indexed by naturals has low-mode contribution
bounded by the global coefficient `ℓ¹` estimate, provided its frequency map
is injective. -/
theorem boundaryKernel_frequency_sequence_sum_bound (M : ℕ)
    (hM : 2 ≤ M) (s : Finset ℕ) (freq : ℕ → ℤ)
    (hinj : Function.Injective freq) (phase : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hphase : ∀ k ∈ s, ‖phase k‖ ≤ B) :
    ‖∑ k ∈ s, boundaryKernelFourierCoefficient M hM (freq k) * phase k‖ ≤
      B * ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
        Real.sqrt (Real.log (2 * (M : ℝ)))) := by
  let coeffNorm : ℤ → ℝ := fun h =>
    ‖boundaryKernelFourierCoefficient M hM h‖
  let pulledNorm : ℕ → ℝ := fun k => coeffNorm (freq k)
  have hcoeff : Summable coeffNorm := by
    simpa [coeffNorm] using boundaryKernelFourierCoefficient_norm_summable M hM
  have hpulled : Summable pulledNorm := hcoeff.comp_injective hinj
  have hfinite : (∑ k ∈ s, pulledNorm k) ≤
      ∑' h : ℤ, coeffNorm h := by
    calc
      (∑ k ∈ s, pulledNorm k) ≤ ∑' k : ℕ, pulledNorm k :=
        hpulled.sum_le_tsum s (fun k hk => by positivity)
      _ ≤ ∑' h : ℤ, coeffNorm h := by
        exact hpulled.tsum_le_tsum_of_inj freq hinj
          (fun h hh => norm_nonneg (boundaryKernelFourierCoefficient M hM h))
          (fun k => le_rfl) hcoeff
  have hfinite' : (∑ k ∈ s,
      ‖boundaryKernelFourierCoefficient M hM (freq k)‖) ≤
        ∑' h : ℤ, ‖boundaryKernelFourierCoefficient M hM h‖ := by
    simpa [pulledNorm, coeffNorm] using hfinite
  calc
    ‖∑ k ∈ s,
        boundaryKernelFourierCoefficient M hM (freq k) * phase k‖ ≤
      B * ∑ k ∈ s,
        ‖boundaryKernelFourierCoefficient M hM (freq k)‖ :=
      norm_sum_fourier_modes_le_phase_bound_mul_coeff_sum s
        (fun k => boundaryKernelFourierCoefficient M hM (freq k))
        phase B hB hphase
    _ ≤ B * ∑' h : ℤ,
        ‖boundaryKernelFourierCoefficient M hM h‖ :=
      mul_le_mul_of_nonneg_left hfinite' hB
    _ ≤ B * ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
        Real.sqrt (Real.log (2 * (M : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (boundaryKernelFourierCoefficient_norm_tsum_le_sqrt_log M hM) hB

@[simp] theorem floorFourierCoefficient_zero_zero :
    floorFourierCoefficient 0 0 = 1 := by
  simp [floorFourierCoefficient]

@[simp] theorem floorFourierCoefficient_zero_ne {m : ℤ} (hm : m ≠ 0) :
    floorFourierCoefficient m 0 = 0 := by
  simp [floorFourierCoefficient, hm]

theorem realExponentialPhase_neg (f : ℝ → ℝ) (n : ℤ) :
    realExponentialPhase (fun t => -f t) n = star (realExponentialPhase f n) := by
  unfold realExponentialPhase
  change Complex.exp
      ((↑(2 * Real.pi * (-(f (n : ℝ)))) : ℂ) * Complex.I) =
    star (Complex.exp
      ((↑(2 * Real.pi * f (n : ℝ)) : ℂ) * Complex.I))
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem realExponentialPhase_sum_neg (f : ℝ → ℝ) (x Y : ℝ) :
    (∑ n ∈ realIntegerInterval x Y,
      realExponentialPhase (fun t => -f t) n) =
      star (∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n) := by
  simp_rw [realExponentialPhase_neg]
  simp only [star_sum]

theorem realExponentialPhase_forwardDifference (a : ℕ) (f : ℝ → ℝ) (n : ℤ) :
    realExponentialPhase (realForwardDifference a f) n =
      realExponentialPhase f (n + (a : ℤ)) * star (realExponentialPhase f n) := by
  let A : ℝ := 2 * Real.pi * f ((n + (a : ℤ) : ℤ) : ℝ)
  let B : ℝ := 2 * Real.pi * f (n : ℝ)
  have hnorm : ‖Complex.exp ((↑B : ℂ) * Complex.I)‖ = 1 := by
    dsimp [B]
    exact Complex.norm_exp_ofReal_mul_I _
  have hmul : Complex.exp ((↑B : ℂ) * Complex.I) *
      star (Complex.exp ((↑B : ℂ) * Complex.I)) = 1 := by
    have hz := Complex.mul_conj (Complex.exp ((↑B : ℂ) * Complex.I))
    simpa [Complex.star_def, Complex.normSq_eq_norm_sq, hnorm] using hz
  have hinv : (Complex.exp ((↑B : ℂ) * Complex.I))⁻¹ =
      star (Complex.exp ((↑B : ℂ) * Complex.I)) :=
    inv_eq_of_mul_eq_one_right hmul
  dsimp [realExponentialPhase, realForwardDifference, A, B]
  have harg :
      (↑(2 * Real.pi * (f ((n : ℝ) + (a : ℝ)) - f (n : ℝ))) : ℂ) * Complex.I =
        (↑(2 * Real.pi * f ((n + (a : ℤ) : ℤ) : ℝ)) : ℂ) * Complex.I -
          (↑(2 * Real.pi * f (n : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_sub, div_eq_mul_inv, hinv]
  simp [B]

theorem mem_realIntegerInterval_shift_iff
    (x L : ℝ) (d : ℕ) (n : ℤ) :
    (n ∈ realIntegerInterval x L ∧
      n + (d : ℤ) ∈ realIntegerInterval x L) ↔
        n ∈ realIntegerInterval x (L - d) := by
  rw [mem_realIntegerInterval_iff, mem_realIntegerInterval_iff,
    mem_realIntegerInterval_iff]
  push_cast
  constructor
  · rintro ⟨⟨hnlo, hnhi⟩, ⟨hndlo, hndhi⟩⟩
    constructor
    · exact hnlo
    · linarith
  · rintro ⟨hnlo, hnhi⟩
    constructor
    · constructor
      · exact hnlo
      · linarith
    · constructor
      · linarith
      · linarith

/-- The phase restricted to the paper's finite interval and extended by zero
outside it, as required by the finite Weyl lemma. -/
noncomputable def realIntervalPhase (f : ℝ → ℝ) (x L : ℝ) (n : ℤ) : ℂ :=
  if n ∈ realIntegerInterval x L then realExponentialPhase f n else 0

theorem realIntervalPhase_correlation_eq_difference_sum
    (f : ℝ → ℝ) (x L : ℝ) (d : ℕ) :
    (∑ n ∈ realIntegerInterval x L,
      realIntervalPhase f x L (n + (d : ℤ)) *
        star (realIntervalPhase f x L n)) =
      ∑ n ∈ realIntegerInterval x (L - d),
        realExponentialPhase (realForwardDifference d f) n := by
  let I := realIntegerInterval x L
  let J := realIntegerInterval x (L - d)
  let g : ℤ → ℂ := fun n =>
    realIntervalPhase f x L (n + (d : ℤ)) * star (realIntervalPhase f x L n)
  have hshift (n : ℤ) :
      (n ∈ I ∧ n + (d : ℤ) ∈ I) ↔ n ∈ J := by
    simpa [I, J] using mem_realIntegerInterval_shift_iff x L d n
  have hsub : J ⊆ I := by
    intro n hn
    exact ((hshift n).mpr hn).1
  have hzero : ∀ n ∈ I, n ∉ J → g n = 0 := by
    intro n hn hnot
    have hnotshift : n + (d : ℤ) ∉ realIntegerInterval x L := by
      intro hshiftmem
      exact hnot ((hshift n).mp ⟨hn, by simpa [I] using hshiftmem⟩)
    simp [g, realIntervalPhase, hnotshift]
  have hsum : (∑ n ∈ J, g n) = ∑ n ∈ I, g n :=
    Finset.sum_subset hsub hzero
  have hpoint : ∀ n ∈ J,
      g n = realExponentialPhase (realForwardDifference d f) n := by
    intro n hn
    have hp := (hshift n).mpr hn
    have hp₁ : n ∈ realIntegerInterval x L := by simpa [I] using hp.1
    have hp₂ : n + (d : ℤ) ∈ realIntegerInterval x L := by simpa [I] using hp.2
    simp [g, realIntervalPhase, hp₁, hp₂,
      realExponentialPhase_forwardDifference]
  have hsumJ : (∑ n ∈ J, g n) =
      ∑ n ∈ J, realExponentialPhase (realForwardDifference d f) n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n hn
  rw [← hsum, ← hsumJ]

/-- The finite rectangular box of tuples with `1 ≤ a_i < H_i`, indexed in
exactly the same order as the bounds list. -/
def positiveShiftBox : List ℕ → Finset (List ℕ)
  | [] => {[]}
  | H :: rest =>
      ((Finset.Ico 1 H).product (positiveShiftBox rest)).image
        (fun p : ℕ × List ℕ => p.1 :: p.2)

theorem positiveShiftBox_card (bounds : List ℕ) :
    (positiveShiftBox bounds).card =
      (bounds.map (fun H => H - 1)).prod := by
  induction bounds with
  | nil => simp [positiveShiftBox]
  | cons H rest ih =>
      have hinj : Function.Injective
          (fun p : ℕ × List ℕ => p.1 :: p.2) := by
        intro p q hpq
        cases p with
        | mk a as =>
          cases q with
          | mk b bs =>
            simp only [List.cons.injEq] at hpq
            cases hpq.1
            cases hpq.2
            rfl
      simp only [positiveShiftBox]
      rw [Finset.card_image_of_injective _ hinj]
      have hprod : ((Finset.Ico 1 H).product (positiveShiftBox rest)).card =
          (Finset.Ico 1 H).card * (positiveShiftBox rest).card := by simp
      rw [hprod, Nat.card_Ico, ih]
      simp [List.map_cons, List.prod_cons]


end FractionalPrimes

end
