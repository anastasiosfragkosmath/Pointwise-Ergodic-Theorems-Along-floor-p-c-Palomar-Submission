module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

open Set
open scoped Interval

namespace FractionalPrimes.Literature.LongArithmetic

/-- Rectangle displacement with the analytic hypothesis reduced to
complex differentiability on the closed rectangle. -/
private theorem rectangleDisplacement_of_differentiableOn
    {u v T : ℝ} (_huv : u < v) (_hT : 0 < T) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G ([[u, v]] ×ℂ [[-T, T]])) :
    Complex.I • (∫ t : ℝ in -T..T, G ((v : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I • (∫ t : ℝ in -T..T, G ((u : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ x : ℝ in u..v, G ((x : ℂ) + (T : ℂ) * Complex.I)) -
        (∫ x : ℝ in u..v, G ((x : ℂ) + (-T : ℂ) * Complex.I)) := by
  let z : ℂ := (u : ℂ) + (-T : ℂ) * Complex.I
  let w : ℂ := (v : ℂ) + (T : ℂ) * Complex.I
  have hzre : z.re = u := by simp [z]
  have hwre : w.re = v := by simp [w]
  have hzim : z.im = -T := by simp [z]
  have hwim : w.im = T := by simp [w]
  have hrect : ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) = ([[u, v]] ×ℂ [[-T, T]]) := by
    rw [hzre, hwre, hzim, hwim]
  have hG' : DifferentiableOn ℂ G ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    rw [hrect]
    exact hG
  have hboundary :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn G z w hG'
  have hboundary' :
      (∫ x : ℝ in u..v, G ((x : ℂ) + (-T : ℂ) * Complex.I)) -
          (∫ x : ℝ in u..v, G ((x : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I • (∫ t : ℝ in -T..T,
          G ((v : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I • (∫ t : ℝ in -T..T,
          G ((u : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
    simpa [z, w, hzre, hwre, hzim, hwim] using hboundary
  linear_combination hboundary'

/-- Rectangle displacement by the fundamental theorem of calculus, in the
approved open-neighborhood formulation `lal:rectangle`. -/
theorem rectangleDisplacement
    {u v T : ℝ} (huv : u < v) (hT : 0 < T) {U : Set ℂ}
    (_hUopen : IsOpen U)
    (hrect : ([[u, v]] ×ℂ [[-T, T]]) ⊆ U)
    {G : ℂ → ℂ} (hG : ContDiffOn ℂ 1 G U) :
    Complex.I • (∫ t : ℝ in -T..T, G ((v : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I • (∫ t : ℝ in -T..T, G ((u : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ x : ℝ in u..v, G ((x : ℂ) + (T : ℂ) * Complex.I)) -
        (∫ x : ℝ in u..v, G ((x : ℂ) + (-T : ℂ) * Complex.I)) := by
  exact rectangleDisplacement_of_differentiableOn huv hT
    ((hG.mono hrect).differentiableOn_one)

#print axioms rectangleDisplacement

end FractionalPrimes.Literature.LongArithmetic

end
