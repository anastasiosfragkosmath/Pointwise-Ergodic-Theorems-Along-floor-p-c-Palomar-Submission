module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorMeanScale
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorMeanPointwise

/-! Exact scale bounds for a selected factor in a retained component. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Uniformity

/-- The finite-indexed product in the Type-I tuple bound is the original
ordered component scale product. -/
theorem smoothHeathBrownScaleProduct_eq_factorFinsetProduct
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X)) :
    smoothHeathBrownScaleProduct fs =
      ∏ i : Fin fs.length, smoothHeathBrownFactorScale (fs.get i) := by
  unfold smoothHeathBrownScaleProduct
  rw [← List.prod_ofFn]
  congr 1
  simpa [List.get_eq_getElem] using
    (List.ofFn_getElem_eq_map fs smoothHeathBrownFactorScale).symm

/-- The retained source component supplies both scale bounds used by the
Type-I mean estimate, with its selected long-factor premise unchanged. -/
theorem smoothHeathBrownSupportRetained_selectedTypeIScaleBounds
    {X z : ℝ} (hX : 0 ≤ X) (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (hcount : fs.length ≤ 20)
    (hret : smoothHeathBrownSupportRetained (X := X) (z := z) fs)
    (hlong : (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected)) :
    (2 : ℝ) ^ (-(22 : ℝ)) * X ^ (3 / 8 : ℝ) ≤
        smoothHeathBrownFactorScale (fs.get selected) ∧
      Real.sqrt (smoothHeathBrownScaleProduct fs) ≤
        (2 : ℝ) ^ 11 * Real.sqrt X := by
  have hfsne : fs ≠ [] := by
    intro heq
    subst fs
    exact Fin.elim0 selected
  have hbounds := smoothHeathBrownSupportRetained_scale_bounds
    hcount hfsne hX hret
  constructor
  · exact smoothLongFactor_selectedScale_lower X
      (smoothHeathBrownScaleProduct fs)
      (smoothHeathBrownFactorScale (fs.get selected))
      hX (smoothHeathBrownScaleProduct_pos fs).le hbounds.1 hlong
  · exact smoothHeathBrownSupportRetained_sqrt_scaleProduct_le
      hcount hfsne hX hret

#print axioms smoothHeathBrownScaleProduct_eq_factorFinsetProduct
#print axioms smoothHeathBrownSupportRetained_selectedTypeIScaleBounds

end FractionalPrimes.Literature.DirichletAdapter

end
