module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletPrincipalAnalyticity

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Reciprocal

/-- The exact principal reciprocal regularization in `lrc:reciprocal-strip`.
The totalized `H₀` agrees with the blueprint definition on `Re(s)>0`. -/
def continuedDirichletPrincipalReciprocal (s : ℂ) : ℂ :=
  (s - 1) / ((s + 1) * continuedDirichletH0Total s)

/-- The principal reciprocal regularization is analytic at the removed pole:
the denominator has value one at `s=1`. -/
theorem analyticAt_continuedDirichletPrincipalReciprocal_one :
    AnalyticAt ℂ continuedDirichletPrincipalReciprocal 1 := by
  have hanum : AnalyticAt ℂ (fun s : ℂ => s - 1) 1 :=
    analyticAt_id.sub analyticAt_const
  have hplus : AnalyticAt ℂ (fun s : ℂ => s + 1) 1 :=
    analyticAt_id.add analyticAt_const
  have hden : AnalyticAt ℂ
      (fun s : ℂ => (s + 1) * continuedDirichletH0Total s) 1 :=
    hplus.mul analyticAt_continuedDirichletH0Total_one
  have hden_ne : (1 + 1) * continuedDirichletH0Total 1 ≠ 0 := by
    rw [continuedDirichletH0Total_one]
    norm_num
  change AnalyticAt ℂ (fun s : ℂ => (s - 1) /
    ((s + 1) * continuedDirichletH0Total s)) 1
  exact hanum.div hden hden_ne

/-- Away from `s=1`, the regularized principal reciprocal equals the exact
reciprocal of the pole-excluded continuation `Z(s)`. -/
theorem continuedDirichletPrincipalReciprocal_eq_inv_continuedDirichletZ
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    continuedDirichletPrincipalReciprocal s =
      (continuedDirichletZ s hs hs1)⁻¹ := by
  have hsminus : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hsplus : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [continuedDirichletPrincipalReciprocal, continuedDirichletH0Total_eq hs,
    continuedDirichletH0_eq_mul_Z hs hs1]
  by_cases hZ : continuedDirichletZ s hs hs1 = 0
  · simp [hZ]
  · field_simp [hsminus, hsplus, hZ]

#print axioms analyticAt_continuedDirichletPrincipalReciprocal_one
#print axioms continuedDirichletPrincipalReciprocal_eq_inv_continuedDirichletZ

end FractionalPrimes.Literature.Reciprocal

end
