module

public import FractionalPrimes.Literature.DirichletAdapter.ReciprocalIntegerModes

/-! Compact support and smoothness under the positive affine residue map. -/

@[expose] public section

open scoped ContDiff

namespace FractionalPrimes.Literature.DirichletAdapter

theorem residueAffine_hasCompactSupport
    (F : ℝ → ℂ) (hF : HasCompactSupport F)
    (q b : ℝ) (hq : 0 < q) :
    HasCompactSupport (fun x : ℝ => F (b + q * x)) := by
  have hscale : HasCompactSupport (fun x : ℝ => F (q * x)) := by
    simpa only [smul_eq_mul] using hF.comp_smul (α := ℝ) hq.ne'
  have hshift : HasCompactSupport (fun y : ℝ => F (b + y)) := by
    simpa [Function.comp_def, Homeomorph.addLeft] using
      hF.comp_homeomorph (Homeomorph.addLeft b)
  simpa only [smul_eq_mul] using hshift.comp_smul (α := ℝ) hq.ne'

#print axioms residueAffine_hasCompactSupport

theorem residueAffine_contDiff
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (q b : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => F (b + q * x)) := by
  exact hF.comp (contDiff_const.add (contDiff_const.mul contDiff_id))

#print axioms residueAffine_contDiff

end FractionalPrimes.Literature.DirichletAdapter

end
