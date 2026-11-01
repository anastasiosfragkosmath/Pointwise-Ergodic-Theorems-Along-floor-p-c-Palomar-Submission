module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalDirichletMeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The separated sampling consequence of the short-interval Dirichlet
mean-square estimate, corresponding to `lgv:sample-square`. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace FractionalPrimes.Literature.LargeValues

noncomputable section

private def centeredFrequency (N : ℝ) (n : ℕ) : ℂ :=
  Complex.I * ((Real.log N - Real.log (n : ℝ)) : ℂ)

private def centeredDirichletPolynomial (N : ℝ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ dirichletIndices N,
    Complex.exp (centeredFrequency N n * (t : ℂ)) * a n

private def centeredDerivativeCoeff (N : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  centeredFrequency N n * a n

private def centeredDerivativePolynomial (N : ℝ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  centeredDirichletPolynomial N (centeredDerivativeCoeff N a) t

private lemma centeredDirichletPolynomial_eq_twisted (N : ℝ) (a : ℕ → ℂ)
    (t : ℝ) :
    centeredDirichletPolynomial N a t =
      Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) *
        dirichletPolynomial N a t := by
  classical
  unfold centeredDirichletPolynomial dirichletPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  unfold dirichletTerm
  let c := centeredFrequency N n
  have harg : c * (t : ℂ) =
      Complex.I * (t : ℂ) * (Real.log N : ℂ) +
        (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
    dsimp [c, centeredFrequency]
    ring
  calc
    Complex.exp (c * (t : ℂ)) * a n =
        a n * Complex.exp
          (Complex.I * (t : ℂ) * (Real.log N : ℂ) +
            (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) := by
      rw [harg]
      ring
    _ = Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) *
          (a n * Complex.exp
            (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) := by
      rw [Complex.exp_add]
      ring

private lemma centeredDirichletPolynomial_hasDerivAt (N : ℝ)
    (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (centeredDirichletPolynomial N a)
      (centeredDirichletPolynomial N (centeredDerivativeCoeff N a) t) t := by
  classical
  unfold centeredDirichletPolynomial
  apply HasDerivAt.fun_sum
  intro n hn
  let c := centeredFrequency N n
  have hlinear : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c t := by
    simpa [c, mul_comm] using
      (((hasDerivAt_id (t : ℂ)).const_mul c).comp_ofReal)
  have hexp := hlinear.cexp
  have hterm := hexp.mul_const (a n)
  change HasDerivAt
    (fun x : ℝ => Complex.exp (c * (x : ℂ)) * a n)
    (Complex.exp (c * (t : ℂ)) * centeredDerivativeCoeff N a n) t
  simpa [centeredDerivativeCoeff, centeredFrequency, c, mul_assoc] using hterm

private lemma centeredDerivativeEnergy_le (N : ℝ) (a : ℕ → ℂ)
    (hN : 2 ≤ N) :
    dirichletEnergy N (centeredDerivativeCoeff N a) ≤ dirichletEnergy N a := by
  classical
  have hNpos : 0 < N := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  unfold dirichletEnergy
  apply Finset.sum_le_sum
  intro n hn
  have hnBounds : N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
    classical
    rw [dirichletIndices, Finset.mem_filter, Finset.mem_range] at hn
    rcases hn with ⟨hnrange, hleft⟩
    have hnat : n ≤ Nat.floor (2 * N) := Nat.le_of_lt_succ hnrange
    have hfloor : (n : ℝ) ≤ Nat.floor (2 * N) := by exact_mod_cast hnat
    exact ⟨hleft, le_trans hfloor (Nat.floor_le (by positivity))⟩
  have hnpos : 0 < (n : ℝ) := lt_trans hNpos hnBounds.1
  have hratioLower : 1 < (n : ℝ) / N := (one_lt_div hNpos).2 hnBounds.1
  have hratioUpper : (n : ℝ) / N ≤ 2 :=
    (div_le_iff₀ hNpos).2 (by nlinarith [hnBounds.2])
  have hratioPos : 0 < (n : ℝ) / N := div_pos hnpos hNpos
  have hlogRatio : Real.log ((n : ℝ) / N) =
      Real.log (n : ℝ) - Real.log N := by
    rw [Real.log_div hnpos.ne' hNpos.ne']
  have hdiff0 : 0 ≤ Real.log (n : ℝ) - Real.log N := by
    rw [← hlogRatio]
    exact Real.log_nonneg (by linarith)
  have hdiff1 : Real.log (n : ℝ) - Real.log N ≤ 1 := by
    rw [← hlogRatio]
    exact (Real.log_le_log hratioPos hratioUpper).trans hlog2
  have hdiffAbs : |Real.log (n : ℝ) - Real.log N| ≤ 1 :=
    abs_le.mpr ⟨by linarith, hdiff1⟩
  have hcoeffNorm : ‖centeredDerivativeCoeff N a n‖ ≤ ‖a n‖ := by
    dsimp [centeredDerivativeCoeff]
    have hscalarnorm :
        ‖centeredFrequency N n‖ =
          |Real.log (n : ℝ) - Real.log N| := by
      unfold centeredFrequency
      rw [norm_mul]
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simp only [Complex.norm_I, one_mul, Real.norm_eq_abs, abs_sub_comm]
    calc
      ‖centeredFrequency N n * a n‖ =
          |Real.log (n : ℝ) - Real.log N| * ‖a n‖ := by
        rw [norm_mul, hscalarnorm]
      _ ≤ ‖a n‖ := by
        calc
          |Real.log (n : ℝ) - Real.log N| * ‖a n‖ ≤ 1 * ‖a n‖ :=
            mul_le_mul_of_nonneg_right hdiffAbs (norm_nonneg _)
          _ = ‖a n‖ := by ring
  have hsq : ‖centeredDerivativeCoeff N a n‖ ^ 2 ≤ ‖a n‖ ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hcoeffNorm 2
  exact hsq

private lemma centeredNormSq_hasDerivAt (N : ℝ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.normSq (centeredDirichletPolynomial N a x))
      (2 * ⟪centeredDirichletPolynomial N a t,
        centeredDerivativePolynomial N a t⟫) t := by
  simpa only [Complex.normSq_eq_norm_sq, centeredDerivativePolynomial] using
    (centeredDirichletPolynomial_hasDerivAt N a t).norm_sq

private lemma centeredSample_local_bound (N : ℝ) (a : ℕ → ℂ) (x : ℝ) :
    Complex.normSq (centeredDirichletPolynomial N a x) ≤
      2 * (∫ t in x - 1 / 2..x + 1 / 2,
        Complex.normSq (centeredDirichletPolynomial N a t)) +
        (∫ t in x - 1 / 2..x + 1 / 2,
          Complex.normSq (centeredDerivativePolynomial N a t)) := by
  let f : ℝ → ℝ := fun t => Complex.normSq (centeredDirichletPolynomial N a t)
  let g : ℝ → ℝ := fun t => Complex.normSq (centeredDerivativePolynomial N a t)
  let q : ℝ → ℝ := fun t =>
    2 * ⟪centeredDirichletPolynomial N a t,
      centeredDerivativePolynomial N a t⟫
  let l := x - 1 / 2
  let r := x + 1 / 2
  have hqderiv (t : ℝ) : HasDerivAt f (q t) t := by
    simpa [f, q] using centeredNormSq_hasDerivAt N a t
  have hFcont : Continuous (centeredDirichletPolynomial N a) := by
    unfold centeredDirichletPolynomial
    fun_prop
  have hF'derivcont : Continuous (centeredDerivativePolynomial N a) := by
    unfold centeredDerivativePolynomial centeredDirichletPolynomial centeredDerivativeCoeff
    fun_prop
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hqbound (t : ℝ) : |q t| ≤ f t + g t := by
    have hinner := abs_real_inner_le_norm
      (centeredDirichletPolynomial N a t) (centeredDerivativePolynomial N a t)
    have hprod :
        2 * ‖centeredDirichletPolynomial N a t‖ *
            ‖centeredDerivativePolynomial N a t‖ ≤
          ‖centeredDirichletPolynomial N a t‖ ^ 2 +
            ‖centeredDerivativePolynomial N a t‖ ^ 2 := by
      nlinarith [sq_nonneg
        (‖centeredDirichletPolynomial N a t‖ -
          ‖centeredDerivativePolynomial N a t‖)]
    have hqabs : |q t| ≤
        2 * ‖centeredDirichletPolynomial N a t‖ *
          ‖centeredDerivativePolynomial N a t‖ := by
      dsimp [q]
      calc
        |2 * ⟪centeredDirichletPolynomial N a t,
            centeredDerivativePolynomial N a t⟫| =
            2 * |⟪centeredDirichletPolynomial N a t,
              centeredDerivativePolynomial N a t⟫| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        _ ≤ 2 * (‖centeredDirichletPolynomial N a t‖ *
            ‖centeredDerivativePolynomial N a t‖) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
        _ = 2 * ‖centeredDirichletPolynomial N a t‖ *
            ‖centeredDerivativePolynomial N a t‖ := by ring
    simpa [f, g, Complex.normSq_eq_norm_sq] using hqabs.trans hprod
  have hfi : IntervalIntegrable f volume l r := by
    exact hfcont.intervalIntegrable (μ := volume) l r
  have hgi : IntervalIntegrable g volume l r := by
    exact hgcont.intervalIntegrable (μ := volume) l r
  have hqabsint : IntervalIntegrable (fun t => |q t|) volume l r := by
    exact hqcont.abs.intervalIntegrable (μ := volume) l r
  have hC :
      (∫ t in l..r, |q t|) ≤
        (∫ t in l..r, f t) + (∫ t in l..r, g t) := by
    calc
      (∫ t in l..r, |q t|) ≤ ∫ t in l..r, (f t + g t) := by
        apply intervalIntegral.integral_mono_on (by dsimp [l, r]; linarith)
          hqabsint (hfi.add hgi)
        intro t ht
        exact hqbound t
      _ = (∫ t in l..r, f t) + (∫ t in l..r, g t) := by
        rw [intervalIntegral.integral_add hfi hgi]
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc l r) : f x ≤ f s + ∫ t in l..r, |q t| := by
    have hls : l ≤ s := hs.1
    have hsr : s ≤ r := hs.2
    by_cases hsx : s ≤ x
    · have hxr : x ≤ r := by dsimp [r]; linarith
      have hFTC : (∫ t in s..x, q t) = f x - f s :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => hqderiv t) (hqcont.intervalIntegrable (μ := volume) s x)
      have habs : |∫ t in s..x, q t| ≤ ∫ t in s..x, |q t| :=
        intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := q) hsx
      have hmono : (∫ t in s..x, |q t|) ≤ ∫ t in l..r, |q t| :=
        intervalIntegral.integral_mono_interval hls hsx hxr
          (ae_of_all _ (fun _ => abs_nonneg _)) hqabsint
      have hdiff : f x - f s ≤ ∫ t in l..r, |q t| := by
        rw [← hFTC]
        exact (le_abs_self _).trans (habs.trans hmono)
      linarith
    · have hxs : x ≤ s := le_of_not_ge hsx
      have hlx : l ≤ x := by dsimp [l]; linarith
      have hFTC : (∫ t in x..s, q t) = f s - f x :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => hqderiv t) (hqcont.intervalIntegrable (μ := volume) x s)
      have habs : |∫ t in x..s, q t| ≤ ∫ t in x..s, |q t| :=
        intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := q) hxs
      have hmono : (∫ t in x..s, |q t|) ≤ ∫ t in l..r, |q t| :=
        intervalIntegral.integral_mono_interval hlx hxs hsr
          (ae_of_all _ (fun _ => abs_nonneg _)) hqabsint
      have hdiff : |f x - f s| ≤ ∫ t in l..r, |q t| := by
        rw [show f x - f s = -(f s - f x) by ring, abs_neg, ← hFTC]
        exact habs.trans hmono
      linarith [le_abs_self (f x - f s)]
  have hone : r - l = 1 := by dsimp [l, r]; ring
  have hconsti : IntervalIntegrable (fun _ : ℝ => f x) volume l r :=
    intervalIntegrable_const
  have hCint : IntervalIntegrable (fun _ : ℝ => ∫ t in l..r, |q t|) volume l r :=
    intervalIntegrable_const
  have hsumint : IntervalIntegrable (fun s : ℝ => f s + ∫ t in l..r, |q t|)
      volume l r := hfi.add hCint
  have haverage : f x ≤ (∫ t in l..r, f t) + (∫ t in l..r, |q t|) := by
    have hmono := intervalIntegral.integral_mono_on (by dsimp [l, r]; linarith)
      hconsti hsumint hpoint
    have hlhs : (∫ s in l..r, f x) = f x := by
      rw [intervalIntegral.integral_const, hone]
      simp
    have hrhs :
        (∫ s in l..r, f s + ∫ t in l..r, |q t|) =
          (∫ t in l..r, f t) + (∫ t in l..r, |q t|) := by
      rw [intervalIntegral.integral_add hfi hCint]
      rw [intervalIntegral.integral_const, hone]
      simp
    rw [hlhs, hrhs] at hmono
    exact hmono
  have hfinal : f x ≤ 2 * (∫ t in l..r, f t) + (∫ t in l..r, g t) := by
    calc
      f x ≤ (∫ t in l..r, f t) + (∫ t in l..r, |q t|) := haverage
      _ ≤ (∫ t in l..r, f t) +
          ((∫ t in l..r, f t) + (∫ t in l..r, g t)) :=
            add_le_add_right hC _
      _ = 2 * (∫ t in l..r, f t) + (∫ t in l..r, g t) := by ring
  simpa [f, g, l, r] using hfinal

private def sampleWindow (x : ℝ) : Set ℝ := Set.Ioc (x - 1 / 2) (x + 1 / 2)

private lemma separatedWindowIntegral_le_outer (T : ℝ) (R : ℕ)
    (t : Fin R → ℝ) (f : ℝ → ℝ)
    (ht : ∀ j, |t j| ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (hfcont : Continuous f) (hfnonneg : ∀ x, 0 ≤ f x) :
    (∑ j : Fin R, ∫ x in sampleWindow (t j), f x ∂volume) ≤
      ∫ x in Set.Ioc (-T - 1 / 2) (T + 1 / 2), f x ∂volume := by
  let outer : Set ℝ := Set.Ioc (-T - 1 / 2) (T + 1 / 2)
  have hdisj : Pairwise fun i j : Fin R =>
      Disjoint (sampleWindow (t i)) (sampleWindow (t j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hix hjx
    change t i - 1 / 2 < x ∧ x ≤ t i + 1 / 2 at hix
    change t j - 1 / 2 < x ∧ x ≤ t j + 1 / 2 at hjx
    by_cases horder : t i ≤ t j
    · have hsepij := hsep i j hij
      rw [abs_of_nonpos (sub_nonpos.mpr horder)] at hsepij
      have hgap : t i + 1 / 2 ≤ t j - 1 / 2 := by linarith
      exact (not_lt_of_ge hgap) (lt_of_lt_of_le hjx.1 hix.2)
    · have hji : t j < t i := lt_of_not_ge horder
      have hsepji := hsep j i hij.symm
      rw [abs_of_nonpos (sub_nonpos.mpr hji.le)] at hsepji
      have hgap : t j + 1 / 2 ≤ t i - 1 / 2 := by linarith
      exact (not_lt_of_ge hgap) (lt_of_lt_of_le hix.1 hjx.2)
  have hsubset : (⋃ j : Fin R, sampleWindow (t j)) ⊆ outer := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    change t j - 1 / 2 < x ∧ x ≤ t j + 1 / 2 at hj
    rcases abs_le.mp (ht j) with ⟨hleft, hright⟩
    change -T - 1 / 2 < x ∧ x ≤ T + 1 / 2
    constructor <;> linarith
  have hfOuter : IntegrableOn f outer volume := by
    have hcompact : IsCompact (Set.Icc (-T - 1 / 2) (T + 1 / 2)) := isCompact_Icc
    exact (hfcont.continuousOn.integrableOn_compact hcompact).mono_set (by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩)
  have hfLocal (j : Fin R) : IntegrableOn f (sampleWindow (t j)) volume := by
    have hcompact :
        IsCompact (Set.Icc (t j - 1 / 2) (t j + 1 / 2)) := isCompact_Icc
    exact (hfcont.continuousOn.integrableOn_compact hcompact).mono_set (by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩)
  have hsum :
      (∫ x in ⋃ j : Fin R, sampleWindow (t j), f x ∂volume) =
        ∑ j : Fin R, ∫ x in sampleWindow (t j), f x ∂volume :=
    integral_iUnion_fintype (fun j => measurableSet_Ioc) hdisj hfLocal
  have hnonneg : 0 ≤ᵐ[volume.restrict outer] f :=
    ae_of_all _ (fun x => hfnonneg x)
  have hsubsetAE : (⋃ j : Fin R, sampleWindow (t j)) ≤ᵐ[volume] outer := by
    filter_upwards [] with x hx
    exact hsubset hx
  calc
    (∑ j : Fin R, ∫ x in sampleWindow (t j), f x ∂volume) =
        ∫ x in ⋃ j : Fin R, sampleWindow (t j), f x ∂volume := hsum.symm
    _ ≤ ∫ x in outer, f x ∂volume := setIntegral_mono_set hfOuter hnonneg hsubsetAE

private lemma twistNormSq_eq_one (N t : ℝ) :
    Complex.normSq (Complex.exp
      (Complex.I * (t : ℂ) * (Real.log N : ℂ))) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ) * (Real.log N : ℂ)).re = 0 := by
    rw [Complex.mul_re]
    have hre' : (Complex.I * (t : ℂ)).re = 0 := by simp [Complex.mul_re]
    have him' : (Complex.I * (t : ℂ)).im = t := by simp [Complex.mul_im]
    rw [hre', him', Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre]
  simp

/-- The exact separated-sampling estimate `lgv:sample-square`. A finite family
of real sampling times is required to have pairwise spacing at least one and
to lie in `[-T,T]`; `R = 0` is allowed. -/
theorem separatedMeanSquare (N T : ℝ) (R : ℕ) (a : ℕ → ℂ)
    (t : Fin R → ℝ) (hN : 2 ≤ N) (hT : 2 ≤ T)
    (ht : ∀ j, |t j| ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|) :
    (∑ j : Fin R, Complex.normSq (dirichletPolynomial N a (t j))) ≤
      32 * (T + N) * Real.log (4 * N * T) * dirichletEnergy N a := by
  let energyBound := 2 * T + 1 + 8 * N * (1 + Real.log (2 * N))
  let outer := Set.Ioc (-T - 1 / 2) (T + 1 / 2)
  have hNpos : 0 < N := by linarith
  have hTpos : 0 < T := by linarith
  have hlog2N : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by nlinarith)
  have hGnonneg : 0 ≤ dirichletEnergy N a := by
    unfold dirichletEnergy
    exact Finset.sum_nonneg fun n hn => sq_nonneg ‖a n‖
  have hEnergyDerivative :
      dirichletEnergy N (centeredDerivativeCoeff N a) ≤ dirichletEnergy N a :=
    centeredDerivativeEnergy_le N a hN
  have hEnergyBoundNonneg : 0 ≤ energyBound := by
    dsimp [energyBound]
    positivity
  have houterEndpoint : -T - 1 / 2 + (2 * T + 1) = T + 1 / 2 := by ring
  have houterOrder : -T - 1 / 2 ≤ T + 1 / 2 := by linarith
  have houterBound (b : ℕ → ℂ) :
      (∫ x in outer, Complex.normSq (centeredDirichletPolynomial N b x) ∂volume) ≤
        energyBound * dirichletEnergy N b := by
    have hpoint (x : ℝ) :
        Complex.normSq (centeredDirichletPolynomial N b x) =
          Complex.normSq (Complex.exp (Complex.I * (x : ℂ) * (Real.log N : ℂ)) *
            dirichletPolynomial N b x) := by
      rw [centeredDirichletPolynomial_eq_twisted, Complex.normSq_mul,
        twistNormSq_eq_one, one_mul]
    have heq :
        (∫ x in outer, Complex.normSq (centeredDirichletPolynomial N b x) ∂volume) =
          ∫ x in outer, Complex.normSq
            (Complex.exp (Complex.I * (x : ℂ) * (Real.log N : ℂ)) *
              dirichletPolynomial N b x) ∂volume := by
      apply setIntegral_congr_ae measurableSet_Ioc
      filter_upwards [] with x hx
      exact hpoint x
    rw [heq]
    calc
      (∫ x in outer, Complex.normSq
          (Complex.exp (Complex.I * (x : ℂ) * (Real.log N : ℂ)) *
            dirichletPolynomial N b x) ∂volume) =
          ∫ x in (-T - 1 / 2)..(-T - 1 / 2) + (2 * T + 1),
            Complex.normSq (Complex.exp (Complex.I * (x : ℂ) * (Real.log N : ℂ)) *
              dirichletPolynomial N b x) := by
        rw [← intervalIntegral.integral_of_le houterOrder]
        congr 1
        rw [houterEndpoint]
      _ ≤ (2 * T + 1 + 8 * N * (1 + Real.log (2 * N))) *
          dirichletEnergy N b := by
        simpa [energyBound] using
          meanSquareBound_afterTwist N (-T - 1 / 2) (2 * T + 1) b hN (by linarith)
  have houterF := houterBound a
  have houterDerivative :
      (∫ x in outer, Complex.normSq (centeredDerivativePolynomial N a x) ∂volume) ≤
        energyBound * dirichletEnergy N a := by
    calc
      (∫ x in outer, Complex.normSq (centeredDerivativePolynomial N a x) ∂volume) =
          ∫ x in outer, Complex.normSq
            (centeredDirichletPolynomial N (centeredDerivativeCoeff N a) x) ∂volume := by
        rfl
      _ ≤ energyBound * dirichletEnergy N (centeredDerivativeCoeff N a) :=
        houterBound (centeredDerivativeCoeff N a)
      _ ≤ energyBound * dirichletEnergy N a :=
        mul_le_mul_of_nonneg_left hEnergyDerivative hEnergyBoundNonneg
  have hFcont : Continuous (fun x => Complex.normSq
      (centeredDirichletPolynomial N a x)) := by
    unfold centeredDirichletPolynomial
    fun_prop
  have hGcont : Continuous (fun x => Complex.normSq
      (centeredDerivativePolynomial N a x)) := by
    unfold centeredDerivativePolynomial centeredDirichletPolynomial centeredDerivativeCoeff
    fun_prop
  have hFnonneg (x : ℝ) :
      0 ≤ Complex.normSq (centeredDirichletPolynomial N a x) := Complex.normSq_nonneg _
  have hGpointnonneg (x : ℝ) :
      0 ≤ Complex.normSq (centeredDerivativePolynomial N a x) := Complex.normSq_nonneg _
  have hFsum := separatedWindowIntegral_le_outer T R t
    (fun x => Complex.normSq (centeredDirichletPolynomial N a x)) ht hsep
    hFcont hFnonneg
  have hGsum := separatedWindowIntegral_le_outer T R t
    (fun x => Complex.normSq (centeredDerivativePolynomial N a x)) ht hsep
    hGcont hGpointnonneg
  have hlocal :
      (∑ j : Fin R, Complex.normSq (centeredDirichletPolynomial N a (t j))) ≤
        2 * (∑ j : Fin R, ∫ x in sampleWindow (t j),
          Complex.normSq (centeredDirichletPolynomial N a x) ∂volume) +
          ∑ j : Fin R, ∫ x in sampleWindow (t j),
            Complex.normSq (centeredDerivativePolynomial N a x) ∂volume := by
    calc
      (∑ j : Fin R, Complex.normSq (centeredDirichletPolynomial N a (t j))) ≤
          ∑ j : Fin R,
            (2 * (∫ x in sampleWindow (t j),
                Complex.normSq (centeredDirichletPolynomial N a x) ∂volume) +
              ∫ x in sampleWindow (t j),
                Complex.normSq (centeredDerivativePolynomial N a x) ∂volume) := by
        apply Finset.sum_le_sum
        intro j hj
        have h := centeredSample_local_bound N a (t j)
        rw [intervalIntegral.integral_of_le (by linarith),
          intervalIntegral.integral_of_le (by linarith)] at h
        simpa [sampleWindow] using h
      _ = 2 * (∑ j : Fin R, ∫ x in sampleWindow (t j),
            Complex.normSq (centeredDirichletPolynomial N a x) ∂volume) +
          ∑ j : Fin R, ∫ x in sampleWindow (t j),
            Complex.normSq (centeredDerivativePolynomial N a x) ∂volume := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hFsum' :
      (∑ j : Fin R, ∫ x in sampleWindow (t j),
        Complex.normSq (centeredDirichletPolynomial N a x) ∂volume) ≤
        ∫ x in outer, Complex.normSq (centeredDirichletPolynomial N a x) ∂volume := by
    simpa [outer] using hFsum
  have hGsum' :
      (∑ j : Fin R, ∫ x in sampleWindow (t j),
        Complex.normSq (centeredDerivativePolynomial N a x) ∂volume) ≤
        ∫ x in outer, Complex.normSq (centeredDerivativePolynomial N a x) ∂volume := by
    simpa [outer] using hGsum
  have hsampleOuter :
      (∑ j : Fin R, Complex.normSq (centeredDirichletPolynomial N a (t j))) ≤
        3 * energyBound * dirichletEnergy N a := by
    calc
      (∑ j : Fin R, Complex.normSq (centeredDirichletPolynomial N a (t j))) ≤
          2 * (∫ x in outer,
            Complex.normSq (centeredDirichletPolynomial N a x) ∂volume) +
            ∫ x in outer,
              Complex.normSq (centeredDerivativePolynomial N a x) ∂volume := by
        calc
          _ ≤ 2 * (∑ j : Fin R, ∫ x in sampleWindow (t j),
                Complex.normSq (centeredDirichletPolynomial N a x) ∂volume) +
              ∑ j : Fin R, ∫ x in sampleWindow (t j),
                Complex.normSq (centeredDerivativePolynomial N a x) ∂volume := hlocal
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hFsum' (by norm_num)) hGsum'
      _ ≤ 3 * energyBound * dirichletEnergy N a := by
        nlinarith [houterF, houterDerivative]
  have hlog4 : 1 ≤ Real.log (4 : ℝ) := by
    have h := Real.le_log_one_add_of_nonneg (x := (3 : ℝ)) (by norm_num)
    norm_num at h
    linarith
  have hlog2T : 1 ≤ Real.log (2 * T) := by
    calc
      1 ≤ Real.log 4 := hlog4
      _ ≤ Real.log (2 * T) :=
        Real.log_le_log (by norm_num) (by nlinarith)
  have hLidentity : Real.log (4 * N * T) =
      Real.log (2 * N) + Real.log (2 * T) := by
    calc
      Real.log (4 * N * T) = Real.log ((2 * N) * (2 * T)) := by congr 1; ring
      _ = Real.log (2 * N) + Real.log (2 * T) :=
        Real.log_mul (by positivity) (by positivity)
  have hLgap : 1 + Real.log (2 * N) ≤ Real.log (4 * N * T) := by
    rw [hLidentity]
    linarith
  have hLnonneg : 0 ≤ Real.log (4 * N * T) := by linarith
  have henergyAbsorb :
      3 * energyBound ≤ 32 * (T + N) * Real.log (4 * N * T) := by
    have hA : energyBound ≤ 3 * T + 8 * N * Real.log (4 * N * T) := by
      dsimp [energyBound]
      have hlogpart := mul_le_mul_of_nonneg_left hLgap (by positivity : 0 ≤ 8 * N)
      linarith
    have hTscaled : T ≤ T * Real.log (4 * N * T) := by
      calc
        T = T * 1 := by ring
        _ ≤ T * Real.log (4 * N * T) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    calc
      3 * energyBound ≤ 3 * (3 * T + 8 * N * Real.log (4 * N * T)) :=
        mul_le_mul_of_nonneg_left hA (by norm_num)
      _ = 9 * T + 24 * N * Real.log (4 * N * T) := by ring
      _ ≤ 32 * (T + N) * Real.log (4 * N * T) := by
        nlinarith [hTscaled, hLnonneg, hNpos]
  have hsampleD :
      (∑ j : Fin R, Complex.normSq (dirichletPolynomial N a (t j))) =
        ∑ j : Fin R, Complex.normSq (centeredDirichletPolynomial N a (t j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [centeredDirichletPolynomial_eq_twisted, Complex.normSq_mul,
      twistNormSq_eq_one, one_mul]
  calc
    (∑ j : Fin R, Complex.normSq (dirichletPolynomial N a (t j))) =
        ∑ j : Fin R, Complex.normSq (centeredDirichletPolynomial N a (t j)) := hsampleD
    _ ≤ 3 * energyBound * dirichletEnergy N a := hsampleOuter
    _ ≤ 32 * (T + N) * Real.log (4 * N * T) * dirichletEnergy N a :=
      mul_le_mul_of_nonneg_right henergyAbsorb hGnonneg

end

end FractionalPrimes.Literature.LargeValues

end

#print axioms FractionalPrimes.Literature.LargeValues.separatedMeanSquare
