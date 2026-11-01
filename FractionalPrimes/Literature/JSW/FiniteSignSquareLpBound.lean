module

public import FractionalPrimes.Literature.JSW.LittlewoodPaleyUpper

/-!
# Finite-sign square-function integration

This is the generic finite-sign step shared by the JSW Littlewood–Paley
and dyadic martingale-jump arguments. The proof is the already checked
finite-sign integration theorem in `LittlewoodPaleyUpper`; its source
constant is exactly the `c_p` of `lj:signs`.
-/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- If every finite signed combination has `Lᵖ` norm at most `R`, the
square function of its components has norm at most `c_p⁻¹ R`. -/
theorem finiteSignSquareLpBound {p : ℝ} (hp : 1 < p)
    (m : ℕ) (v : Fin m → Lp ℂ (ENNReal.ofReal p) volume)
    (S : jswSignSpace m → Lp ℂ (ENNReal.ofReal p) volume)
    (hS : ∀ (w : jswSignSpace m), (S w : ℝ → ℂ) =ᵐ[volume]
      fun x => jswSignSum m w (fun i => v i x))
    {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ (w : jswSignSpace m), ‖S w‖ ≤ R) :
    lpNorm (fun x : ℝ => Real.sqrt (∑ i : Fin m, ‖v i x‖ ^ 2))
      (ENNReal.ofReal p) volume ≤ (littlewoodPaleyCp p)⁻¹ * R := by
  exact littlewoodPaleyFiniteSignSquareLpBound hp m v S hS hR hbound

end

end FractionalPrimes.Literature.JSW

end
