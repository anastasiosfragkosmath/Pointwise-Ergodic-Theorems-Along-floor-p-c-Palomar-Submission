module

public import FractionalPrimes.Literature.Reciprocal.ZetaFloorAnalyticContinuation

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- The pole-excluded principal zeta function from `lrc:dirichlet-data`.
Its domain is restricted to `s ≠ 1`, where the blueprint defines `Z(s)`. -/
noncomputable def blueprintZeta (s : {z : ℂ // z ≠ 1}) : ℂ :=
  s.val / (s.val - 1) - s.val * zetaFloorCorrectionIntegral s.val

private theorem zetaFloor_pole_split (s x : ℂ) (hs : s ≠ 1) :
    s / (s - 1) - s * x = (s - 1)⁻¹ + (1 - s * x) := by
  have hd : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hratio : s / (s - 1) = 1 + (s - 1)⁻¹ := by
    calc
      s / (s - 1) = s * (s - 1)⁻¹ := by rw [div_eq_mul_inv]
      _ = ((s - 1) + 1) * (s - 1)⁻¹ := by congr 1 <;> ring
      _ = (s - 1) * (s - 1)⁻¹ + 1 * (s - 1)⁻¹ := by rw [add_mul]
      _ = 1 + (s - 1)⁻¹ := by rw [mul_inv_cancel₀ hd]; simp
  rw [hratio]
  ring

/-- On the blueprint's domain, its floor-correction definition of `Z(s)` is
Mathlib's Riemann zeta function throughout `Re(s) > 0`. -/
theorem blueprintZeta_eq_riemannZeta {s : {z : ℂ // z ≠ 1}}
    (hs : 0 < s.val.re) : blueprintZeta s = riemannZeta s.val := by
  have hregular := zetaFloorRegularPart_eq_riemannZeta₀_of_pos_re hs
  rw [riemannZeta_eq_inv_sub_add s.property]
  calc
    blueprintZeta s = (s.val - 1)⁻¹ + zetaFloorRegularPart s.val := by
      change s.val / (s.val - 1) - s.val * zetaFloorCorrectionIntegral s.val = _
      rw [show zetaFloorRegularPart s.val =
        1 - s.val * zetaFloorCorrectionIntegral s.val by rfl]
      exact zetaFloor_pole_split s.val (zetaFloorCorrectionIntegral s.val) s.property
    _ = (s.val - 1)⁻¹ + riemannZeta₀ s.val := by rw [hregular]

#print axioms blueprintZeta_eq_riemannZeta

end FractionalPrimes.Literature.Reciprocal
