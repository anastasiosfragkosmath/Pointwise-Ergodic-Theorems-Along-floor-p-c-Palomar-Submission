module

public import FractionalPrimes.Literature.Twisted.SmoothDyadicProfileParametric
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The profile derivative input for high order residue quadrature

This file proves the special-function derivative estimate in the source
profile half of `lda:quadrature`. The finite Fourier quadrature and arithmetic
residue estimates are handled separately.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

open MeasureTheory
open scoped ContDiff Topology

/-- The complex exponent in the source function `x^(-1/2-it)`. -/
def smoothDyadicTwistExponent (t : ℝ) : ℂ :=
  (-1 / 2 : ℂ) - (t : ℂ) * Complex.I

/-- The falling factorial in derivatives of `u^(-1/2-it)`. -/
def smoothDyadicTwistCoeff (t : ℝ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => smoothDyadicTwistCoeff t n *
      (smoothDyadicTwistExponent t - (n : ℂ))

theorem smoothDyadicTwistExponent_re (t : ℝ) :
    (smoothDyadicTwistExponent t).re = -1 / 2 := by
  simp [smoothDyadicTwistExponent]

private theorem smoothDyadicTwistExponent_sub_nat_ne_zero (t : ℝ) (n : ℕ) :
    smoothDyadicTwistExponent t - (n : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have hvalue : (smoothDyadicTwistExponent t - (n : ℂ)).re =
      (-1 / 2 : ℝ) - n := by
    simp [smoothDyadicTwistExponent]
  rw [hvalue] at hre
  simp only [Complex.zero_re] at hre
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The exact iterated derivative formula for the complex power on the
positive half-line. -/
theorem smoothDyadicTwistWeight_iteratedDeriv
    (t : ℝ) (r : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv r (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) u =
      smoothDyadicTwistCoeff t r *
        (u : ℂ) ^ (smoothDyadicTwistExponent t - (r : ℂ)) := by
  induction r generalizing u with
  | zero =>
      simp [smoothDyadicTwistCoeff, iteratedDeriv_zero]
  | succ r ih =>
      rw [iteratedDeriv_succ]
      have hnear :
          iteratedDeriv r (fun x : ℝ =>
              (x : ℂ) ^ smoothDyadicTwistExponent t) =ᶠ[𝓝 u]
            fun x => smoothDyadicTwistCoeff t r *
              (x : ℂ) ^ (smoothDyadicTwistExponent t - (r : ℂ)) := by
        filter_upwards [Ioi_mem_nhds hu] with x hx
        exact ih hx
      rw [hnear.deriv_eq]
      have hpow := Complex.deriv_ofReal_cpow_const (x := u) hu.ne'
        (smoothDyadicTwistExponent_sub_nat_ne_zero t r)
      simp only [deriv_const_mul_field, hpow]
      rw [smoothDyadicTwistCoeff]
      have hexp : smoothDyadicTwistExponent t - (r : ℂ) - 1 =
          smoothDyadicTwistExponent t - ((r + 1 : ℕ) : ℂ) := by
        push_cast
        ring
      rw [hexp]
      ring

private theorem smoothDyadicTwistCoeff_norm_le
    (t : ℝ) (r j : ℕ) (hr : r ≤ j) :
    ‖smoothDyadicTwistCoeff t r‖ ≤
      (((j + 1 : ℕ) : ℝ) * (1 + |t|)) ^ r := by
  induction r with
  | zero =>
      simp [smoothDyadicTwistCoeff]
  | succ r ih =>
      have hrj : r ≤ j := le_trans (Nat.le_succ r) hr
      have hfac :
          ‖smoothDyadicTwistExponent t - (r : ℂ)‖ ≤
            (((j + 1 : ℕ) : ℝ) * (1 + |t|)) := by
        have hz : ‖smoothDyadicTwistExponent t‖ ≤ 1 / 2 + |t| := by
          rw [smoothDyadicTwistExponent]
          calc
            ‖(-1 / 2 : ℂ) - (t : ℂ) * Complex.I‖ ≤
                ‖(-1 / 2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_sub_le _ _
            _ = 1 / 2 + |t| := by simp
        have hrCast : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hrj
        calc
          ‖smoothDyadicTwistExponent t - (r : ℂ)‖ ≤
              ‖smoothDyadicTwistExponent t‖ + ‖(r : ℂ)‖ := norm_sub_le _ _
          _ = ‖smoothDyadicTwistExponent t‖ + (r : ℝ) := by simp
          _ ≤ 1 / 2 + |t| + (r : ℝ) := by gcongr
          _ ≤ (((j + 1 : ℕ) : ℝ) * (1 + |t|)) := by
            have ht : 0 ≤ |t| := abs_nonneg t
            have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
            push_cast
            nlinarith [mul_nonneg hj ht]
      calc
        ‖smoothDyadicTwistCoeff t (r + 1)‖ =
            ‖smoothDyadicTwistCoeff t r *
              (smoothDyadicTwistExponent t - (r : ℂ))‖ := by
                rw [smoothDyadicTwistCoeff]
        _ ≤ ‖smoothDyadicTwistCoeff t r‖ *
              ‖smoothDyadicTwistExponent t - (r : ℂ)‖ := norm_mul_le _ _
        _ ≤ (((j + 1 : ℕ) : ℝ) * (1 + |t|)) ^ r *
              (((j + 1 : ℕ) : ℝ) * (1 + |t|)) :=
                mul_le_mul (ih hrj) hfac (norm_nonneg _) (by positivity)
        _ = (((j + 1 : ℕ) : ℝ) * (1 + |t|)) ^ (r + 1) := by rw [pow_succ]

private theorem smoothDyadicOneLePow {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    1 ≤ x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc
        1 = 1 * 1 := by ring
        _ ≤ x ^ n * x := mul_le_mul ih hx (by norm_num) (by positivity)

/-- Uniform pointwise bound for every derivative order up to `j` on the
source support interval. -/
theorem smoothDyadicTwistWeight_iteratedDeriv_norm_le
    (t : ℝ) (j r : ℕ) (hr : r ≤ j) {u : ℝ}
    (hu₁ : 1 / 2 ≤ u) (_hu₂ : u ≤ 2) :
    ‖iteratedDeriv r
        (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) u‖ ≤
      2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j := by
  have hu : 0 < u := by linarith
  rw [smoothDyadicTwistWeight_iteratedDeriv t r hu]
  have hpowNorm := Complex.norm_cpow_eq_rpow_re_of_pos hu
    (smoothDyadicTwistExponent t - (r : ℂ))
  have hre : (smoothDyadicTwistExponent t - (r : ℂ)).re =
      (-1 / 2 : ℝ) - r := by
    simp [smoothDyadicTwistExponent]
  rw [norm_mul, hpowNorm, hre]
  have hcoeff := smoothDyadicTwistCoeff_norm_le t r j hr
  have hexp : 0 ≤ (((j + 1 : ℕ) : ℝ) * (1 + |t|)) := by positivity
  have hbaseCoeff : 1 ≤ (((j + 1 : ℕ) : ℝ) * (1 + |t|)) := by
    have ht : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hj : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 j)
    exact le_trans (by norm_num) (mul_le_mul hj ht (by norm_num) (by positivity))
  have hcoeff' : ‖smoothDyadicTwistCoeff t r‖ ≤
      (((j + 1 : ℕ) : ℝ) * (1 + |t|)) ^ j :=
    hcoeff.trans (by
      let B : ℝ := (((j + 1 : ℕ) : ℝ) * (1 + |t|))
      have hmono : B ^ r ≤ B ^ j := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
        rw [hk, pow_add]
        calc
          B ^ r = B ^ r * 1 := by ring
          _ ≤ B ^ r * B ^ k :=
            mul_le_mul_of_nonneg_left (smoothDyadicOneLePow hbaseCoeff k)
              (by positivity)
      simpa [B] using hmono)
  have hbase : 0 < (1 / 2 : ℝ) := by norm_num
  have hexponent : (-1 / 2 : ℝ) - r ≤ 0 := by
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  have hscale := Real.rpow_le_rpow_of_nonpos hbase hu₁ hexponent
  have hscale' : u ^ ((-1 / 2 : ℝ) - r) ≤
      (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) := by
    calc
      u ^ ((-1 / 2 : ℝ) - r) ≤
          (1 / 2 : ℝ) ^ ((-1 / 2 : ℝ) - r) := hscale
      _ = (2 : ℝ) ^ ((1 / 2 : ℝ) + r) := by
        rw [show (-1 / 2 : ℝ) - r = -((1 / 2 : ℝ) + r) by ring,
          Real.rpow_neg_eq_inv_rpow]
        norm_num
      _ ≤ (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hrCast : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hr
        push_cast
        linarith
  have hmul := mul_le_mul hcoeff' hscale' (by positivity)
    (by positivity : 0 ≤ (((j + 1 : ℕ) : ℝ) * (1 + |t|)) ^ j)
  calc
    ‖smoothDyadicTwistCoeff t r‖ *
        u ^ ((-1 / 2 : ℝ) - r) ≤
      (((j + 1 : ℕ) : ℝ) * (1 + |t|)) ^ j *
        (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) := hmul
    _ = 2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j := by
      rw [Real.rpow_natCast, mul_pow]
      ring

/-- The smooth source profile after multiplication by the oscillatory power.
The profile vanishes near the origin, so this product is smooth even though
the complex power itself is only used on the positive support. -/
def smoothDyadicTwistedProfileCore (t : ℝ) (p : ℝ × ℝ × ℝ) (u : ℝ) : ℂ :=
  ((smoothDyadicH p.1 p.2.1 p.2.2) •
    (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t)) u

theorem smoothDyadicTwistWeight_contDiffAt
    (t u : ℝ) (hu : 0 < u) :
    ContDiffAt ℝ ∞ (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) u := by
  let z := smoothDyadicTwistExponent t
  let G : ℝ → ℂ := fun x => Complex.exp (z * (Real.log x : ℂ))
  have hlog : ContDiffAt ℝ ∞ Real.log u :=
    Real.contDiffAt_log.mpr hu.ne'
  have hlogC : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.log x : ℂ)) u := by
    exact (Complex.ofRealCLM.contDiff.contDiffAt).comp u hlog
  have harg : ContDiffAt ℝ ∞ (fun x : ℝ => z * (Real.log x : ℂ)) u := by
    exact contDiffAt_const.mul hlogC
  have hG : ContDiffAt ℝ ∞ G u := by
    dsimp [G]
    exact Complex.contDiff_exp.contDiffAt.comp u harg
  have hEq : (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) =ᶠ[𝓝 u] G := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    dsimp [G, z]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    rw [Complex.ofReal_log hx.le]
    congr 1
    ring
  exact hG.congr_of_eventuallyEq hEq

theorem smoothDyadicTwistedProfileCore_contDiff (t : ℝ)
    (p : ℝ × ℝ × ℝ) :
    ContDiff ℝ ∞ (smoothDyadicTwistedProfileCore t p) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : 0 < u
  · have hw := smoothDyadicTwistWeight_contDiffAt t u hu
    exact (smoothDyadicH_contDiff p.1 p.2.1 p.2.2).contDiffAt.smul hw
  · have huBelow : u < (1 / 2 : ℝ) := by linarith
    have hEq : smoothDyadicTwistedProfileCore t p =ᶠ[𝓝 u]
        fun _ : ℝ => 0 := by
      filter_upwards [Iio_mem_nhds huBelow] with x hx
      simp [smoothDyadicTwistedProfileCore,
        smoothDyadicH_eq_zero_of_le_half (le_of_lt hx)]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hEq

private theorem smoothDyadicIterated_tsupport_subset (i : ℕ) (f : ℝ → ℂ) :
    tsupport (iteratedDeriv i f) ⊆ tsupport f := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

theorem smoothDyadicTwistedProfileCore_support_subset (t : ℝ)
    (p : ℝ × ℝ × ℝ) :
    Function.support (smoothDyadicTwistedProfileCore t p) ⊆
      Set.Icc (1 / 2 : ℝ) 2 := by
  intro u hu
  have hprofile : smoothDyadicH p.1 p.2.1 p.2.2 u ≠ 0 := by
    intro hzero
    apply hu
    simp [smoothDyadicTwistedProfileCore, hzero]
  exact smoothDyadicH_support_subset p.1 p.2.1 p.2.2
    (by simpa [Function.mem_support] using hprofile)

theorem smoothDyadicTwistedProfileCore_iterated_support_subset
    (t : ℝ) (p : ℝ × ℝ × ℝ) (i : ℕ) :
    Function.support (iteratedDeriv i (smoothDyadicTwistedProfileCore t p)) ⊆
      Set.Icc (1 / 2 : ℝ) 2 := by
  calc
    Function.support (iteratedDeriv i (smoothDyadicTwistedProfileCore t p))
        ⊆ tsupport (iteratedDeriv i (smoothDyadicTwistedProfileCore t p)) :=
          subset_closure
    _ ⊆ tsupport (smoothDyadicTwistedProfileCore t p) :=
          smoothDyadicIterated_tsupport_subset i _
    _ ⊆ Set.Icc (1 / 2 : ℝ) 2 :=
          closure_minimal (smoothDyadicTwistedProfileCore_support_subset t p)
            isClosed_Icc

theorem smoothDyadicTwistedProfileCore_iterated_norm_integrable
    (t : ℝ) (p : ℝ × ℝ × ℝ) (i : ℕ) :
    Integrable (fun u : ℝ =>
      ‖iteratedDeriv i (smoothDyadicTwistedProfileCore t p) u‖) := by
  have hcont : Continuous (iteratedDeriv i (smoothDyadicTwistedProfileCore t p)) :=
    (smoothDyadicTwistedProfileCore_contDiff t p).continuous_iteratedDeriv i (by simp)
  exact hcont.norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (smoothDyadicTwistedProfileCore_iterated_support_subset t p i)).norm

private theorem smoothDyadicTwistedProfileCore_iterated_leibniz
    (t : ℝ) (p : ℝ × ℝ × ℝ) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (smoothDyadicTwistedProfileCore t p) u =
      ∑ i ∈ Finset.range (j + 1),
        j.choose i • iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u •
          iteratedDeriv (j - i)
            (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) u := by
  have hH : ContDiffWithinAt ℝ (j : ℕ∞)
      (smoothDyadicH p.1 p.2.1 p.2.2) Set.univ u := by
    exact ((smoothDyadicH_contDiff p.1 p.2.1 p.2.2).contDiffAt.of_le
      (by simp)).contDiffWithinAt
  have hW : ContDiffWithinAt ℝ (j : ℕ∞)
      (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) Set.univ u := by
    exact (smoothDyadicTwistWeight_contDiffAt t u hu).of_le (by simp) |>.contDiffWithinAt
  have h := iteratedDerivWithin_smul (Set.mem_univ u) uniqueDiffOn_univ hH hW
  change iteratedDeriv j
      ((smoothDyadicH p.1 p.2.1 p.2.2) •
        (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t)) u = _
  simpa only [iteratedDerivWithin_univ] using h

/-- The pointwise finite Leibniz bound for the source profile. -/
theorem smoothDyadicTwistedProfileCore_iterated_norm_le
    (t : ℝ) (j : ℕ) (p : ℝ × ℝ × ℝ)
    (u : ℝ) :
    ‖iteratedDeriv j (smoothDyadicTwistedProfileCore t p) u‖ ≤
      (2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j) *
        (∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) *
            ‖iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u‖) := by
  by_cases hu : u ∈ Set.Icc (1 / 2 : ℝ) 2
  · have hu₁ := hu.1
    have hu₂ := hu.2
    have hformula := smoothDyadicTwistedProfileCore_iterated_leibniz t p j
      (by linarith : 0 < u)
    rw [hformula]
    let D : ℝ := 2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j
    calc
      ‖∑ i ∈ Finset.range (j + 1),
          j.choose i • iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u •
            iteratedDeriv (j - i)
              (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) u‖ ≤
        ∑ i ∈ Finset.range (j + 1),
          ‖j.choose i • iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u •
            iteratedDeriv (j - i)
              (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) u‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) *
            ‖iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u‖ * D := by
          apply Finset.sum_le_sum
          intro i hi
          have hweight := smoothDyadicTwistWeight_iteratedDeriv_norm_le
            t j (j - i) (Nat.sub_le _ _) hu₁ hu₂
          calc
            ‖j.choose i • iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u •
                iteratedDeriv (j - i)
                  (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) u‖ =
              (j.choose i : ℝ) *
                ‖iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u‖ *
                ‖iteratedDeriv (j - i)
                  (fun x : ℝ => (x : ℂ) ^ smoothDyadicTwistExponent t) u‖ := by
                    simp
                    ring
            _ ≤ (j.choose i : ℝ) *
                ‖iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u‖ * D := by
                  apply mul_le_mul_of_nonneg_left hweight
                  positivity
      _ = D * (∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) *
            ‖iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u‖) := by
          simp only [D]
          rw [← Finset.sum_mul]
          ring
  · have hzero : iteratedDeriv j (smoothDyadicTwistedProfileCore t p) u = 0 := by
      by_contra hne
      have hmem : u ∈
          Function.support (iteratedDeriv j (smoothDyadicTwistedProfileCore t p)) := by
        simpa [Function.mem_support] using hne
      exact hu (smoothDyadicTwistedProfileCore_iterated_support_subset t p j hmem)
    rw [hzero, norm_zero]
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro i hi
      positivity

/-- The exact `A_j` profile bound for the derivative of the oscillatory
profile at the unscaled variable. -/
theorem smoothDyadicTwistedProfileCore_derivativeL1_le
    (t : ℝ) (j : ℕ) (p : ℝ × ℝ × ℝ)
    (hp : p ∈ smoothDyadicProfileParameterBox) :
    (∫ u : ℝ,
      ‖iteratedDeriv j (smoothDyadicTwistedProfileCore t p) u‖ ∂volume) ≤
      (2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j) *
        smoothDyadicA j := by
  let D : ℝ := 2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j
  let S : ℝ → ℝ := fun u =>
    ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) *
        ‖iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u‖
  let M : ℝ → ℝ := fun u => D * S u
  have htermInt (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
      Integrable (fun u : ℝ => (j.choose i : ℝ) *
        ‖iteratedDeriv i (smoothDyadicH p.1 p.2.1 p.2.2) u‖) := by
    simpa [mul_comm] using
      (smoothDyadicHIterated_norm_integrable p.1 p.2.1 p.2.2 i).const_mul
        (j.choose i : ℝ)
  have hSInt : Integrable S := by
    exact integrable_finsetSum (Finset.range (j + 1)) htermInt
  have hMInt : Integrable M := by
    simpa [M, mul_comm] using hSInt.const_mul D
  have hpoint : ∀ u : ℝ,
      ‖iteratedDeriv j (smoothDyadicTwistedProfileCore t p) u‖ ≤ M u := by
    intro u
    simpa [M, S, D] using
      smoothDyadicTwistedProfileCore_iterated_norm_le t j p u
  have hIntComp :
      (∫ u : ℝ,
        ‖iteratedDeriv j (smoothDyadicTwistedProfileCore t p) u‖ ∂volume) ≤
        ∫ u : ℝ, M u ∂volume :=
    integral_mono_ae (smoothDyadicTwistedProfileCore_iterated_norm_integrable t p j)
      hMInt (Filter.Eventually.of_forall hpoint)
  have hSIntegral : (∫ u : ℝ, S u ∂volume) = smoothDyadicAObjective j p := by
    rw [integral_finsetSum (Finset.range (j + 1)) htermInt]
    simp [smoothDyadicAObjective, smoothDyadicHDerivativeL1,
      integral_const_mul]
  have hMIntegral : (∫ u : ℝ, M u ∂volume) = D * smoothDyadicAObjective j p := by
    calc
      (∫ u : ℝ, M u ∂volume) = ∫ u : ℝ, S u * D ∂volume := by
        congr 1
        funext u
        simp [M]
        ring
      _ = (∫ u : ℝ, S u ∂volume) * D := integral_mul_const D S
      _ = D * smoothDyadicAObjective j p := by rw [hSIntegral]; ring
  calc
    (∫ u : ℝ,
        ‖iteratedDeriv j (smoothDyadicTwistedProfileCore t p) u‖ ∂volume) ≤
      ∫ u : ℝ, M u ∂volume := hIntComp
    _ = D * smoothDyadicAObjective j p := hMIntegral
    _ ≤ D * smoothDyadicA j := by
      apply mul_le_mul_of_nonneg_left
        (smoothDyadicA_isMaximum j p hp)
      positivity

/-- The exact scaled source function, written after the change of variables
`u = x/N`. -/
def smoothDyadicQuadratureFunction (N t : ℝ) (p : ℝ × ℝ × ℝ) (x : ℝ) : ℂ :=
  (N : ℂ) ^ smoothDyadicTwistExponent t *
    smoothDyadicTwistedProfileCore t p (N⁻¹ * x)

/-- The source function `x^(-1/2-it) H(x/N)`, extended by zero. -/
def smoothDyadicQuadratureSource (N t : ℝ) (p : ℝ × ℝ × ℝ) (x : ℝ) : ℂ :=
  if 0 < x then
    (x : ℂ) ^ smoothDyadicTwistExponent t *
      (smoothDyadicH p.1 p.2.1 p.2.2 (x / N) : ℂ)
  else 0

theorem smoothDyadicQuadratureFunction_eq_source
    {N t x : ℝ} (p : ℝ × ℝ × ℝ) (hN : 0 < N) :
    smoothDyadicQuadratureFunction N t p x =
      smoothDyadicQuadratureSource N t p x := by
  by_cases hx : 0 < x
  · have hu : 0 < N⁻¹ * x := mul_pos (inv_pos.mpr hN) hx
    have hscale : N * (N⁻¹ * x) = x := by field_simp [ne_of_gt hN]
    have harg : N⁻¹ * x = x / N := by
      field_simp [ne_of_gt hN]
    have hpow :
        (N : ℂ) ^ smoothDyadicTwistExponent t *
            ((N⁻¹ * x : ℝ) : ℂ) ^ smoothDyadicTwistExponent t =
          (x : ℂ) ^ smoothDyadicTwistExponent t := by
      rw [← Complex.mul_cpow_ofReal_nonneg hN.le hu.le]
      congr 1
      exact_mod_cast hscale
    rw [smoothDyadicQuadratureFunction, smoothDyadicQuadratureSource, ite_eq_left hx]
    change (N : ℂ) ^ smoothDyadicTwistExponent t *
        (smoothDyadicH p.1 p.2.1 p.2.2 (N⁻¹ * x) •
          ((N⁻¹ * x : ℝ) : ℂ) ^ smoothDyadicTwistExponent t) =
      (x : ℂ) ^ smoothDyadicTwistExponent t *
        (smoothDyadicH p.1 p.2.1 p.2.2 (x / N) : ℂ)
    rw [harg, RCLike.real_smul_eq_coe_mul]
    have hpow' : (N : ℂ) ^ smoothDyadicTwistExponent t *
        (x / N : ℝ) ^ smoothDyadicTwistExponent t =
          (x : ℂ) ^ smoothDyadicTwistExponent t := by
      simpa [harg] using hpow
    calc
      (N : ℂ) ^ smoothDyadicTwistExponent t *
          ((smoothDyadicH p.1 p.2.1 p.2.2 (x / N) : ℂ) *
            (x / N : ℝ) ^ smoothDyadicTwistExponent t) =
        ((N : ℂ) ^ smoothDyadicTwistExponent t *
            (x / N : ℝ) ^ smoothDyadicTwistExponent t) *
          (smoothDyadicH p.1 p.2.1 p.2.2 (x / N) : ℂ) := by ring
      _ = (x : ℂ) ^ smoothDyadicTwistExponent t *
          (smoothDyadicH p.1 p.2.1 p.2.2 (x / N) : ℂ) := by rw [hpow']
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hu : N⁻¹ * x ≤ (1 / 2 : ℝ) := by
      have hInv : 0 ≤ N⁻¹ := inv_nonneg.mpr hN.le
      have hmul := mul_nonpos_of_nonneg_of_nonpos hInv hxle
      linarith
    simp [smoothDyadicQuadratureFunction, smoothDyadicQuadratureSource,
      smoothDyadicTwistedProfileCore,
      smoothDyadicH_eq_zero_of_le_half hu, hx]

theorem smoothDyadicQuadratureFunction_contDiff
    {N t : ℝ} (p : ℝ × ℝ × ℝ) :
    ContDiff ℝ ∞ (smoothDyadicQuadratureFunction N t p) := by
  let g : ℝ → ℝ := fun x => N⁻¹ * x
  have hg : ContDiff ℝ ∞ g := by
    dsimp [g]
    fun_prop
  have hcomp : ContDiff ℝ ∞ (smoothDyadicTwistedProfileCore t p ∘ g) :=
    (smoothDyadicTwistedProfileCore_contDiff t p).comp hg
  have hc : ContDiff ℝ ∞ (fun _ : ℝ =>
      (N : ℂ) ^ smoothDyadicTwistExponent t) := contDiff_const
  change ContDiff ℝ ∞
    (fun x : ℝ => (N : ℂ) ^ smoothDyadicTwistExponent t *
      smoothDyadicTwistedProfileCore t p (N⁻¹ * x))
  exact hc.mul (by simpa [g, Function.comp_def] using hcomp)

theorem smoothDyadicQuadratureFunction_iteratedDeriv
    {N t : ℝ} (p : ℝ × ℝ × ℝ) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (smoothDyadicQuadratureFunction N t p) x =
      (N : ℂ) ^ smoothDyadicTwistExponent t *
        ((N⁻¹) ^ j •
          iteratedDeriv j (smoothDyadicTwistedProfileCore t p) (N⁻¹ * x)) := by
  let g : ℝ → ℝ := fun y => N⁻¹ * y
  have hcomp : iteratedDeriv j (smoothDyadicTwistedProfileCore t p ∘ g) =
      fun y => (N⁻¹) ^ j •
        iteratedDeriv j (smoothDyadicTwistedProfileCore t p) (N⁻¹ * y) :=
    iteratedDeriv_comp_const_smul
      ((smoothDyadicTwistedProfileCore_contDiff t p).of_le (by simp)) (N⁻¹)
  change iteratedDeriv j
      (fun y : ℝ => (N : ℂ) ^ smoothDyadicTwistExponent t *
        smoothDyadicTwistedProfileCore t p (N⁻¹ * y)) x = _
  rw [iteratedDeriv_const_mul_field]
  rw [show (fun y : ℝ => smoothDyadicTwistedProfileCore t p (N⁻¹ * y)) =
      smoothDyadicTwistedProfileCore t p ∘ g by rfl, hcomp]

/-- The exact `L¹` derivative estimate used by the source-profile half of
`lda:quadrature`. -/
theorem smoothDyadicQuadratureFunction_derivativeL1_le
    {N t : ℝ} (p : ℝ × ℝ × ℝ) (j : ℕ)
    (hN : 1 ≤ N) (_hj : 2 ≤ j) (_ht : 1 ≤ |t|)
    (hp : p ∈ smoothDyadicProfileParameterBox) :
    (∫ x : ℝ,
      ‖iteratedDeriv j (smoothDyadicQuadratureFunction N t p) x‖ ∂volume) ≤
      N ^ ((1 / 2 : ℝ) - (j : ℝ)) *
        (2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j) *
          smoothDyadicA j := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  let z := smoothDyadicTwistExponent t
  let fcore : ℝ → ℝ := fun u =>
    ‖iteratedDeriv j (smoothDyadicTwistedProfileCore t p) u‖
  let C : ℝ := ‖(N : ℂ) ^ z‖ * (N⁻¹) ^ j
  have hnormPoint : ∀ x : ℝ,
      ‖iteratedDeriv j (smoothDyadicQuadratureFunction N t p) x‖ =
        C * fcore (N⁻¹ * x) := by
    intro x
    rw [smoothDyadicQuadratureFunction_iteratedDeriv]
    simp [C, fcore, z, Real.norm_eq_abs, abs_of_pos hNpos]
    ring
  have hchange :
      (∫ x : ℝ, fcore (N⁻¹ * x) ∂volume) =
        N * (∫ u : ℝ, fcore u ∂volume) := by
    simpa [fcore, smul_eq_mul, abs_of_pos hNpos, inv_inv] using
      (MeasureTheory.Measure.integral_comp_mul_left
        (fun u : ℝ =>
          ‖iteratedDeriv j (smoothDyadicTwistedProfileCore t p) u‖)
        (N⁻¹))
  have hscale :
      (∫ x : ℝ,
        ‖iteratedDeriv j (smoothDyadicQuadratureFunction N t p) x‖ ∂volume) =
        (C * N) * (∫ u : ℝ, fcore u ∂volume) := by
    calc
      (∫ x : ℝ,
        ‖iteratedDeriv j (smoothDyadicQuadratureFunction N t p) x‖ ∂volume) =
          ∫ x : ℝ, C * fcore (N⁻¹ * x) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hnormPoint
      _ = C * (∫ x : ℝ, fcore (N⁻¹ * x) ∂volume) := integral_const_mul C _
      _ = C * (N * (∫ u : ℝ, fcore u ∂volume)) := by rw [hchange]
      _ = (C * N) * (∫ u : ℝ, fcore u ∂volume) := by ring
  have hcore := smoothDyadicTwistedProfileCore_derivativeL1_le t j p hp
  have hfactor : C * N = N ^ ((1 / 2 : ℝ) - (j : ℝ)) := by
    have hnormN : ‖(N : ℂ) ^ z‖ = N ^ (-1 / 2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos z,
        smoothDyadicTwistExponent_re]
    have hInvPow : (N⁻¹) ^ j = N ^ (-(j : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_neg_eq_inv_rpow]
    change ‖(N : ℂ) ^ z‖ * (N⁻¹) ^ j * N =
      N ^ ((1 / 2 : ℝ) - (j : ℝ))
    rw [hnormN, hInvPow]
    have hadd1 := (Real.rpow_add hNpos (-1 / 2 : ℝ) (-(j : ℝ))).symm
    have hadd2 :=
      (Real.rpow_add hNpos ((-1 / 2 : ℝ) + (-(j : ℝ))) 1).symm
    calc
      N ^ (-1 / 2 : ℝ) * N ^ (-(j : ℝ)) * N =
          N ^ (-1 / 2 : ℝ) * N ^ (-(j : ℝ)) * N ^ (1 : ℝ) := by simp
      _ = N ^ ((-1 / 2 : ℝ) + (-(j : ℝ))) * N ^ (1 : ℝ) := by rw [hadd1]
      _ = N ^ (((-1 / 2 : ℝ) + (-(j : ℝ))) + 1) := hadd2
      _ = N ^ ((1 / 2 : ℝ) - (j : ℝ)) := by congr 1; ring
  have hcoef_nonneg : 0 ≤ C * N := by
    positivity
  calc
    (∫ x : ℝ,
      ‖iteratedDeriv j (smoothDyadicQuadratureFunction N t p) x‖ ∂volume) =
        (C * N) * (∫ u : ℝ, fcore u ∂volume) := hscale
    _ ≤ (C * N) *
        ((2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j) *
          smoothDyadicA j) := by
        apply mul_le_mul_of_nonneg_left hcore
        exact hcoef_nonneg
    _ = N ^ ((1 / 2 : ℝ) - (j : ℝ)) *
        (2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j) *
          smoothDyadicA j := by rw [hfactor]; ring

theorem smoothDyadicQuadratureSource_contDiff
    {N t : ℝ} (p : ℝ × ℝ × ℝ) (hN : 0 < N) :
    ContDiff ℝ ∞ (smoothDyadicQuadratureSource N t p) := by
  have heq : smoothDyadicQuadratureSource N t p =
      smoothDyadicQuadratureFunction N t p := by
    funext x
    exact (smoothDyadicQuadratureFunction_eq_source p hN).symm
  rw [heq]
  exact smoothDyadicQuadratureFunction_contDiff p

/-- The exact `L¹` derivative estimate for the literal zero-extended source
function in `lda:quadrature`. -/
theorem smoothDyadicQuadratureSource_derivativeL1_le
    {N t : ℝ} (p : ℝ × ℝ × ℝ) (j : ℕ)
    (hN : 1 ≤ N) (_hj : 2 ≤ j) (_ht : 1 ≤ |t|)
    (hp : p ∈ smoothDyadicProfileParameterBox) :
    (∫ x : ℝ,
      ‖iteratedDeriv j (smoothDyadicQuadratureSource N t p) x‖ ∂volume) ≤
      N ^ ((1 / 2 : ℝ) - (j : ℝ)) *
        (2 ^ (j + 1) * (((j + 1 : ℕ) : ℝ) ^ j) * (1 + |t|) ^ j) *
          smoothDyadicA j := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have heq : smoothDyadicQuadratureSource N t p =
      smoothDyadicQuadratureFunction N t p := by
    funext x
    exact (smoothDyadicQuadratureFunction_eq_source p hNpos).symm
  rw [heq]
  exact smoothDyadicQuadratureFunction_derivativeL1_le p j hN _hj _ht hp

#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicTwistWeight_iteratedDeriv_norm_le
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicTwistedProfileCore_derivativeL1_le
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicQuadratureFunction_eq_source
#print axioms FractionalPrimes.Literature.Twisted.smoothDyadicQuadratureSource_derivativeL1_le

end FractionalPrimes.Literature.Twisted
