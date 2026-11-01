module
public import FractionalPrimes.Final.WeightedConvergence
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Nonnegative-time interpretation; negative integers are clamped to zero.
This is not a group action and is used only at nonnegative floor-power times. -/
def System.forwardTime {X : Type*} [MeasurableSpace X]
    (S : System X) (n : ℤ) : X → X := S.T^[n.toNat]

theorem System.shift_floorPower_apply {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (n : ℕ) (f : X → ℂ) (x : X) :
    S.shift (floorTime c n) f x = f (S.forwardTime (floorPower c n) x) := rfl

theorem aestronglyMeasurable_shift_floorPower {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (n : ℕ) {f : X → ℂ}
    (hf : AEStronglyMeasurable f S.μ) :
    AEStronglyMeasurable (S.shift (floorTime c n) f) S.μ :=
  hf.comp_measurePreserving (S.measurePreserving_iterate (floorTime c n))

theorem memLp_shift_floorPower {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (n : ℕ) {p : ℝ≥0∞} {f : X → ℂ}
    (hf : MemLp f p S.μ) : MemLp (S.shift (floorTime c n) f) p S.μ :=
  S.memLp_shift (floorTime c n) hf

theorem eLpNorm_shift_floorPower {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (n : ℕ) {p : ℝ≥0∞} {f : X → ℂ}
    (hf : AEStronglyMeasurable f S.μ) :
    eLpNorm (S.shift (floorTime c n) f) p S.μ = eLpNorm f p S.μ :=
  S.eLpNorm_shift (floorTime c n) hf

def primeCutoffAverage {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (f : X → ℂ) (N : ℕ) (_hN : 2 ≤ N) : X → ℂ :=
  primeAverage S c f N
end
end FractionalPrimes.Final
