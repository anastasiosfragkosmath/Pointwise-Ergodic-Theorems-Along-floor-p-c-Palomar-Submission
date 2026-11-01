module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorRetainedScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Frequency continuity for the literal finite Type-I component. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open MeasureTheory
open FractionalPrimes.Literature.Twisted

private theorem finiteComplexSum_continuousAt
    {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℂ) (t : ℝ)
    (hF : ∀ i ∈ S, ContinuousAt (F i) t) :
    ContinuousAt (fun s : ℝ => ∑ i ∈ S, F i s) t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) t)
  | @insert i S hi ih =>
      have hhead : ContinuousAt (F i) t := hF i (Finset.mem_insert_self i S)
      have htail : ContinuousAt (fun s : ℝ => ∑ x ∈ S, F x s) t :=
        ih (by
          intro x hx
          exact hF x (Finset.mem_insert_of_mem hx))
      have hadd : ContinuousAt (fun s : ℝ => F i s + ∑ x ∈ S, F x s) t := by
        convert hhead.add htail using 1
      simpa only [Finset.sum_insert hi] using hadd

/-- The complementary factor's Mellin phase is continuous for every
positive natural argument in its source support. -/
theorem smoothHeathBrownTypeIOuterPhase_continuousAt
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ContinuousAt (fun s : ℝ => smoothHeathBrownTypeIOuterPhase s n) t := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : (fun s : ℝ => smoothHeathBrownTypeIOuterPhase s n) =
      fun s : ℝ => Complex.exp (Complex.log (n : ℂ) *
        (-(s : ℂ) * Complex.I)) := by
    funext s
    unfold smoothHeathBrownTypeIOuterPhase
    rw [Complex.cpow_def_of_ne_zero hnC]
  rw [heq]
  fun_prop

/-- The selected factor's full `n^(-1/2-it)` sample is continuous in
frequency for every natural argument. -/
theorem smoothHeathBrownFreeFactorDiscreteTerm_continuousAt
    {X : ℝ} (f : SmoothHeathBrownFactor X) (m n : ℕ) (t : ℝ) :
    ContinuousAt (fun s : ℝ =>
      smoothHeathBrownFreeFactorDiscreteTerm f m s n) t := by
  have hExp : ContinuousAt (fun s : ℝ => smoothDyadicTwistExponent s) t := by
    unfold smoothDyadicTwistExponent
    fun_prop
  have hExpNe : smoothDyadicTwistExponent t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [smoothDyadicTwistExponent] at hre
  have hpow : ContinuousAt (fun s : ℝ =>
      (n : ℂ) ^ smoothDyadicTwistExponent s) t :=
    (continuousAt_const_cpow' hExpNe).comp hExp
  unfold smoothHeathBrownFreeFactorDiscreteTerm
  exact hpow.mul continuousAt_const

/-- The actual finite support of a normalized factor contains only positive
natural arguments. -/
theorem smoothHeathBrownFactorFiniteSupport_pos_for_frequency
    {X : ℝ} (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hn : n ∈ smoothHeathBrownFactorFiniteSupport f) : 0 < n := by
  have hN : 1 ≤ smoothHeathBrownFactorScale f :=
    smoothHeathBrownFactorScale_ge_one f
  have hNnonneg : 0 ≤ smoothHeathBrownFactorScale f := by linarith
  have hnWindow : n ∈ smoothFactorMassWindow (smoothHeathBrownFactorScale f) := by
    rw [← smoothHeathBrownFactorFiniteSupport_eq_massWindow]
    exact hn
  have hnReal :=
    (mem_smoothFactorMassWindow hNnonneg n).mp hnWindow |>.1
  have hhalf : 0 < smoothHeathBrownFactorScale f / 2 := by positivity
  exact_mod_cast (lt_trans hhalf hnReal)

/-- One source-weighted outer factor is frequency-continuous on its
finite support. -/
theorem smoothHeathBrownWeightedOuterFactor_continuousAt
    {X z : ℝ} (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hn : n ∈ smoothHeathBrownFactorFiniteSupport f) (t : ℝ) :
    ContinuousAt (fun s : ℝ =>
      smoothHeathBrownWeightedFactorCoefficient (z := z) f
        (smoothHeathBrownTypeIOuterPhase s) n) t := by
  have hphase := smoothHeathBrownTypeIOuterPhase_continuousAt n
    (smoothHeathBrownFactorFiniteSupport_pos_for_frequency f hn) t
  unfold smoothHeathBrownWeightedFactorCoefficient
  exact (continuousAt_const.mul hphase).div_const _

/-- The exact complementary tuple coefficient is frequency-continuous on
the source's finite Cartesian support. -/
theorem smoothHeathBrownTypeIOuterTupleCoefficient_continuousAt
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (u : smoothHeathBrownTypeIOuterIndex selected → ℕ)
    (hu : u ∈ smoothHeathBrownTypeIOuterTupleSet fs selected)
    (t : ℝ) :
    ContinuousAt (fun s : ℝ =>
      smoothHeathBrownTypeIOuterTupleCoefficient (z := z) selected s u) t := by
  classical
  let I := smoothHeathBrownTypeIOuterIndex selected
  have hmem (i : I) :
      u i ∈ smoothHeathBrownFactorFiniteSupport (fs.get i.1) := by
    exact (Fintype.mem_piFinset.mp hu) i
  have hfactor (i : I) : ContinuousAt (fun s : ℝ =>
      smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get i.1)
        (smoothHeathBrownTypeIOuterPhase s) (u i)) t :=
    smoothHeathBrownWeightedOuterFactor_continuousAt
      (fs.get i.1) (hmem i) t
  have hprod (S : Finset I) : ContinuousAt (fun s : ℝ =>
      ∏ i ∈ S, smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get i.1)
        (smoothHeathBrownTypeIOuterPhase s) (u i)) t := by
    induction S using Finset.induction_on with
    | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℂ)) t)
    | @insert i S hi ih =>
        have hmul : ContinuousAt (fun s : ℝ =>
            smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get i.1)
              (smoothHeathBrownTypeIOuterPhase s) (u i) *
              ∏ x ∈ S, smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get x.1)
                (smoothHeathBrownTypeIOuterPhase s) (u x)) t := by
          convert (hfactor i).mul ih using 1
        simpa only [Finset.prod_insert hi] using hmul
  simpa only [smoothHeathBrownTypeIOuterTupleCoefficient] using
    hprod Finset.univ

/-- The literal finite factorized component is continuous in frequency. -/
theorem smoothHeathBrownTypeIFactorizedComponentSum_continuousAt
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (q a : ℕ) (t : ℝ) :
    ContinuousAt (fun s : ℝ =>
      smoothHeathBrownTypeIFactorizedComponentSum (z := z) fs selected q a s) t := by
  classical
  let T := smoothHeathBrownTypeIOuterTupleSet fs selected
  have hterm (u : smoothHeathBrownTypeIOuterIndex selected → ℕ)
      (hu : u ∈ T) : ContinuousAt (fun s : ℝ =>
        smoothHeathBrownTypeIOuterTupleCoefficient (z := z) selected s u *
        (∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions
            (fs.get selected) (smoothHeathBrownTypeIOuterTupleProduct u) q a,
          smoothHeathBrownFreeFactorDiscreteTerm (fs.get selected)
            (smoothHeathBrownTypeIOuterTupleProduct u) s n.1)) t := by
    have houter := smoothHeathBrownTypeIOuterTupleCoefficient_continuousAt
      (z := z) fs selected u hu t
    have hinner : ContinuousAt (fun s : ℝ =>
        ∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions
            (fs.get selected) (smoothHeathBrownTypeIOuterTupleProduct u) q a,
          smoothHeathBrownFreeFactorDiscreteTerm (fs.get selected)
            (smoothHeathBrownTypeIOuterTupleProduct u) s n.1) t := by
      apply finiteComplexSum_continuousAt
      intro n hn
      exact smoothHeathBrownFreeFactorDiscreteTerm_continuousAt
        (fs.get selected) (smoothHeathBrownTypeIOuterTupleProduct u) n.1 t
    convert houter.mul hinner using 1
  have hsum : ContinuousAt (fun s : ℝ =>
      ∑ u ∈ T,
        smoothHeathBrownTypeIOuterTupleCoefficient (z := z) selected s u *
        (∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions
            (fs.get selected) (smoothHeathBrownTypeIOuterTupleProduct u) q a,
          smoothHeathBrownFreeFactorDiscreteTerm (fs.get selected)
            (smoothHeathBrownTypeIOuterTupleProduct u) s n.1)) t := by
    apply finiteComplexSum_continuousAt
    intro u hu
    exact hterm u hu
  simpa only [smoothHeathBrownTypeIFactorizedComponentSum, T] using hsum

/-- Restoring the real source coefficient and logarithmic scalar preserves
frequency continuity of the actual finite component. -/
theorem smoothHeathBrownTypeISourceFactorizedComponentSum_continuousAt
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (q a : ℕ) (c t : ℝ) :
    ContinuousAt (fun s : ℝ =>
      smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a s c) t := by
  have hinner := smoothHeathBrownTypeIFactorizedComponentSum_continuousAt
    (z := z) fs selected q a t
  unfold smoothHeathBrownTypeISourceFactorizedComponentSum
  exact (continuousAt_const.mul continuousAt_const).mul hinner

/-- The norm of the literal source component is interval-integrable on
any finite frequency interval. -/
theorem smoothHeathBrownTypeISourceFactorizedComponentSum_norm_intervalIntegrable
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (q a : ℕ) (c A B : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖) volume A B := by
  have hcont : Continuous (fun t : ℝ =>
      ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (smoothHeathBrownTypeISourceFactorizedComponentSum_continuousAt
      (z := z) fs selected q a c t).norm
  exact hcont.intervalIntegrable A B

#print axioms smoothHeathBrownTypeIOuterPhase_continuousAt
#print axioms smoothHeathBrownFreeFactorDiscreteTerm_continuousAt
#print axioms smoothHeathBrownFactorFiniteSupport_pos_for_frequency
#print axioms smoothHeathBrownWeightedOuterFactor_continuousAt
#print axioms smoothHeathBrownTypeIOuterTupleCoefficient_continuousAt
#print axioms smoothHeathBrownTypeIFactorizedComponentSum_continuousAt
#print axioms smoothHeathBrownTypeISourceFactorizedComponentSum_norm_intervalIntegrable

end FractionalPrimes.Literature.DirichletAdapter

end
