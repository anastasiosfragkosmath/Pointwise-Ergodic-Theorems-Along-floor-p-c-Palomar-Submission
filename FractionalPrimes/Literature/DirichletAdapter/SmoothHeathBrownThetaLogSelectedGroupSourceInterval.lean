module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThetaLogSelectedGroupSource
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownThetaLogSourceIntervalIdentity
import Mathlib.Tactic

/-! The source-facing interval statement for the theta/log selected-group
bound.  The finite group estimate is converted to the exact convolution of
the residue-restricted Heath--Brown arithmetic factors by the checked source
tuple identity. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The theta/log selected-group estimate in the paper's original source
notation: each elementary Heath--Brown coefficient is first restricted to
its prescribed residue class, these factors are convolved in the selected
group, and the resulting coefficient is multiplied by the exact Mellin
phase. The selected tag is explicitly theta or normalized logarithm. -/
theorem smoothHeathBrownThetaLogSelectedSubsetSourceInterval_logDecay
    {X z L T0 t x y : ℝ} {fs : List (SmoothHeathBrownFactor X)}
    {q : ℕ} {B K D : ℝ}
    (I : Finset (Fin fs.length)) (selected : Fin fs.length)
    (hselected : selected ∈ I) (hcount : I.card ≤ 20)
    (hbranch : (∃ j : SmoothHeathBrownScaleIndex X,
        fs.get selected = .theta j) ∨
      (∃ j : SmoothHeathBrownScaleIndex X,
        fs.get selected = .logarithm j))
    (residue : Fin fs.length → ℕ) (hresidue : residue selected < q)
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hB : 0 < B) (hK : 0 < K) (hD : 2 * K + 10 ≤ D)
    (hlog : 2 ≤ Real.log X)
    (hq : 0 < q) (hqLog : (q : ℝ) ≤ (Real.log X) ^ B)
    (hqLarge : (2 / (1 / 400 : ℝ)) *
      Real.log (logAbsorptionM (1 / 400) B) ≤ Real.log X)
    (hT0Eq : T0 = (Real.log X) ^ D / 2)
    (hT0t : T0 ≤ |t|) (htX : |t| ≤ X)
    (hNlower : X ^ (1 / 100 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected))
    (hNupper : smoothHeathBrownFactorScale (fs.get selected) ≤
      (2 : ℝ) ^ 11 * Real.sqrt X)
    (h : ℤ)
    (hL : L = (2 : ℝ) ^ h *
      (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)))
    (hh : -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ))
    (hLx : L ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 * L)
    (hpolyLarge : (2 / periodicLogPhaseSaving (1 / 200) 1) *
      Real.log (2 * smoothHeathBrownFreeFactorBlockConstant
          (fs.get selected) *
        logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) ≤
          Real.log X)
    (htailLarge : (2 * Real.sqrt 2 *
      smoothHeathBrownFreeFactorBlockConstant (fs.get selected)) ^
        (1 / 5 : ℝ) ≤ Real.log X) :
    ‖∑ n ∈ factorExtractionRealInterval x y,
        (∏ i : I,
          smoothHeathBrownThetaLogSourceResidueFactor (z := z)
            q (residue i.val) (fs.get i.val)) n *
          (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
      Real.sqrt L * (Real.log X) ^ (-K) := by
  have hfree : ∀ j : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius j := by
    intro j hmobius
    rcases hbranch with ⟨jθ, hθ⟩ | ⟨jlog, hlogarithm⟩
    · rw [hθ] at hmobius
      cases hmobius
    · rw [hlogarithm] at hmobius
      cases hmobius
  have hsubset := smoothHeathBrownThetaLogSelectedGroupResidue_logDecay
    (z := z) (I := I) (selected := selected) (hselected := hselected)
    (hcount := hcount) (residue := residue) hresidue hXscale hfree
    hB hK hD hlog hq hqLog hqLarge hT0Eq hT0t htX hNlower hNupper h
    hL hh hLx hxy hy hpolyLarge htailLarge
  have hXpos : 0 < X := by
    have htwo : 0 < (2 : ℝ) ^ 200 := by positivity
    linarith
  have hscalePos : ∀ i ∈ I,
      0 < smoothHeathBrownFactorScale (fs.get i) := by
    intro i hi
    have hscale := smoothHeathBrownFactorScale_ge_one (fs.get i)
    linarith
  have hscaleProductPos : 0 <
      ∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i) :=
    Finset.prod_pos fun i hi => hscalePos i hi
  have hLpos : 0 < L := by
    rw [hL]
    exact mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) h)
      hscaleProductPos
  have hx : 0 ≤ x := le_trans (le_of_lt hLpos) hLx
  have hy0 : 0 ≤ y := le_trans hx hxy
  have hsource := smoothHeathBrownThetaLogSelectedGroupSourceInterval_eq_tupleSum
    (z := z) fs I q residue t x y hx hy0
  rw [hsource]
  exact hsubset

#print axioms smoothHeathBrownThetaLogSelectedSubsetSourceInterval_logDecay

end FractionalPrimes.Literature.DirichletAdapter

end
