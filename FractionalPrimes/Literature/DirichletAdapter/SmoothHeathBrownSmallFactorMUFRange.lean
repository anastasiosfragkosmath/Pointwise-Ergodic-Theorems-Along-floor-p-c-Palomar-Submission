module

public import FractionalPrimes.Literature.Twisted.SelectedSmoothGroupScale
public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownRetention
import Mathlib.Tactic

/-!
# Scale range for the selected small-group factor

The three-group scale selection gives a factor scale
`X^(1/100) ≤ N ≤ 2^11 sqrt X`.  This file records the exact elementary
conversion to the two MUF block parameters `N/2` and `N`, and connects that
conversion to the selected Möbius subset assembly.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity.Combinatorics

private theorem smoothHeathBrownFactorScale_eq_natPowExponent
    {X : ℝ} (f : SmoothHeathBrownFactor X) :
    smoothHeathBrownFactorScale f =
      (2 : ℝ) ^ smoothHeathBrownFactorExponent f := by
  cases f <;> rfl

/-- The smooth-Heath--Brown selected-factor range places both MUF block
parameters `N/2` and `N` in the exact interval `[X^(1/400), X]`.  The
threshold `2^160 ≤ X` is a convenient explicit strengthening of the source's
“sufficiently large X”; it is independent of all analytic constants. -/
theorem smoothHeathBrownSmallFactor_mufRange_of_scaleBounds
    {X N : ℝ} (hX : (2 : ℝ) ^ 160 ≤ X)
    (hNlo : X ^ (1 / 100 : ℝ) ≤ N)
    (hNhi : N ≤ (2 : ℝ) ^ 11 * Real.sqrt X) :
    ∀ M : ℝ, (M = N / 2 ∨ M = N) →
      X ^ (1 / 400 : ℝ) ≤ M ∧ M ≤ X := by
  have hXpos : 0 < X := by
    have : 0 < (2 : ℝ) ^ 160 := by positivity
    linarith
  have hXone : 1 ≤ X := by
    have : 1 ≤ (2 : ℝ) ^ 160 := by norm_num
    exact le_trans this hX
  have hroot : 2 ≤ X ^ (3 / 400 : ℝ) := by
    have hmono : ((2 : ℝ) ^ 160) ^ (3 / 400 : ℝ) ≤
        X ^ (3 / 400 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hX (by norm_num)
    have hexp : (2 : ℝ) ^ (6 / 5 : ℝ) =
        ((2 : ℝ) ^ 160) ^ (3 / 400 : ℝ) := by
      calc
        (2 : ℝ) ^ (6 / 5 : ℝ) =
            Real.rpow (2 : ℝ) ((160 : ℝ) * (3 / 400 : ℝ)) := by
              congr 1 <;> norm_num
        _ = ((2 : ℝ) ^ 160) ^ (3 / 400 : ℝ) := by
              rw [← Real.rpow_natCast (2 : ℝ) 160]
              rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
              congr 1 <;> ring
    have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (6 / 5 : ℝ) := by
      have hexp' : (1 : ℝ) ≤ 6 / 5 := by norm_num
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by simp
        _ ≤ (2 : ℝ) ^ (6 / 5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp'
    rw [← hexp] at hmono
    exact htwo.trans hmono
  have hsplit : X ^ (1 / 100 : ℝ) =
      X ^ (1 / 400 : ℝ) * X ^ (3 / 400 : ℝ) := by
    rw [← Real.rpow_add hXpos]
    congr 1 <;> norm_num
  have hfactor : 2 * X ^ (1 / 400 : ℝ) ≤ X ^ (1 / 100 : ℝ) := by
    calc
      2 * X ^ (1 / 400 : ℝ) ≤
          X ^ (3 / 400 : ℝ) * X ^ (1 / 400 : ℝ) :=
        mul_le_mul_of_nonneg_right hroot
          (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (1 / 100 : ℝ) := by rw [mul_comm, hsplit]
  have hX22 : (2 : ℝ) ^ 22 ≤ X := by
    exact (by norm_num : (2 : ℝ) ^ 22 ≤ (2 : ℝ) ^ 160).trans hX
  have hsqrt : (2 : ℝ) ^ 11 ≤ Real.sqrt X := by
    apply (Real.le_sqrt (by positivity) (by linarith)).2
    have hsq : ((2 : ℝ) ^ 11) ^ 2 = (2 : ℝ) ^ 22 := by
      rw [← pow_mul]
    rw [hsq]
    exact hX22
  have hNhiX : N ≤ X := by
    have hsqrtX : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hXpos.le
    have hmul := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg X)
    calc
      N ≤ (2 : ℝ) ^ 11 * Real.sqrt X := hNhi
      _ ≤ Real.sqrt X * Real.sqrt X := by nlinarith
      _ = X := by nlinarith
  intro M hM
  rcases hM with hM | hM
  · rw [hM]
    constructor
    · nlinarith
    · have hNnonneg : 0 ≤ N := le_trans (Real.rpow_nonneg hXpos.le _) hNlo
      nlinarith
  · rw [hM]
    constructor
    · have hbase : X ^ (1 / 400 : ℝ) ≤ X ^ (1 / 100 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
      exact hbase.trans hNlo
    · exact hNhiX

/-- Applying the scale conversion to the exact output of the approved
three-group selector.  The factor index remains in the first selected group;
the scale bounds are precisely the selector's `X^(1/100)` and `2^11 sqrt X`
bounds. -/
theorem selectedSmoothGroupSmallFactor_mufRange
    {k : ℕ} {X P : ℝ} (w : GroupingPredicates k)
    (N : Fin k → ℝ) (hlen : k ≤ 20)
    (hX : ((2 : ℝ) ^ 22) ^ 5 ≤ X)
    (hscaleThreshold : (2 : ℝ) ^ 160 ≤ X)
    (hP : ((2 : ℝ) ^ 22)⁻¹ * X ≤ P ∧ P ≤ (2 : ℝ) ^ 22 * X)
    (hN : ∀ i, N i = P ^ w.weight i)
    (hgroup : w.IImaj (5 / 8)) :
    ∃ I : Finset (Fin k), ∃ i : Fin k, i ∈ I ∧
      X ^ (1 / 100 : ℝ) ≤ N i ∧
      N i ≤ (2 : ℝ) ^ 11 * Real.sqrt X ∧
      ∀ M : ℝ, (M = N i / 2 ∨ M = N i) →
        X ^ (1 / 400 : ℝ) ≤ M ∧ M ≤ X := by
  obtain ⟨I, J, J', hIJ, hIJ', hJJ', hcover,
      hIlo, hIhi, hJlo, hJ'lo, hIcardlo, hIcardhi, hJcardlo, hJ'cardlo,
      ⟨i, hiI, hNlo, hNhi⟩⟩ :=
    FractionalPrimes.Literature.Twisted.selectedSmoothGroupSmallFactorScale
      w N hlen hX hP hN hgroup
  exact ⟨I, i, hiI, hNlo, hNhi,
    smoothHeathBrownSmallFactor_mufRange_of_scaleBounds hscaleThreshold
      hNlo hNhi⟩

/-- A factor scale is exactly the scale product raised to its normalized
Heath--Brown exponent weight. This is the actual scale parametrization used
when the abstract three-group selector is applied to a smooth component. -/
theorem smoothHeathBrownFactorScale_eq_scaleProduct_rpow_groupWeight
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (hE : 0 < smoothHeathBrownExponentSum fs) (i : Fin fs.length) :
    smoothHeathBrownFactorScale (fs.get i) =
      smoothHeathBrownScaleProduct fs ^
        (smoothHeathBrownExponentGrouping fs hE).weight i := by
  let E := smoothHeathBrownExponentSum fs
  let e := smoothHeathBrownFactorExponent (fs.get i)
  have hEreal : (E : ℝ) ≠ 0 := by
    have hEpos : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE
    exact ne_of_gt hEpos
  have hweight :
      (smoothHeathBrownExponentGrouping fs hE).weight i =
        (e : ℝ) / (E : ℝ) := by
    rfl
  have hfactor :
      smoothHeathBrownFactorScale (fs.get i) =
        Real.rpow (2 : ℝ) (e : ℝ) := by
    rw [smoothHeathBrownFactorScale_eq_natPowExponent]
    dsimp [e]
    rw [Real.rpow_natCast]
  have hproduct :
      smoothHeathBrownScaleProduct fs = Real.rpow (2 : ℝ) (E : ℝ) := by
    rw [smoothHeathBrownScaleProduct_eq_two_pow_exponentSum]
    exact (Real.rpow_natCast (2 : ℝ) E).symm
  calc
    smoothHeathBrownFactorScale (fs.get i) = Real.rpow (2 : ℝ) (e : ℝ) :=
      hfactor
    _ = Real.rpow (Real.rpow (2 : ℝ) (E : ℝ))
          ((e : ℝ) / (E : ℝ)) := by
      have hcancel : (E : ℝ) * ((e : ℝ) / (E : ℝ)) = (e : ℝ) := by
        field_simp
      calc
        Real.rpow (2 : ℝ) (e : ℝ) =
            Real.rpow (2 : ℝ)
              ((E : ℝ) * ((e : ℝ) / (E : ℝ))) := by rw [hcancel]
        _ = Real.rpow (Real.rpow (2 : ℝ) (E : ℝ))
              ((e : ℝ) / (E : ℝ)) :=
          Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))
            (E : ℝ) ((e : ℝ) / (E : ℝ))
    _ = smoothHeathBrownScaleProduct fs ^
          (smoothHeathBrownExponentGrouping fs hE).weight i := by
      rw [← hproduct, hweight]
      rfl

/-- For an actual retained smooth Heath--Brown list in the source
three-group branch, the selected factor's two possible MUF block scales lie
in `[X^(1/400),X]`. The `2^160` threshold makes the endpoint conversion
explicit; `hgroup` is exactly the approved `IImaj (5/8)` grouping branch. -/
theorem smoothHeathBrownThreeGroupSmallFactor_mufRange
    {X : ℝ} (hX : (2 : ℝ) ^ 160 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (hlen : fs.length ≤ 20) (hfsne : fs ≠ [])
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fs)
    (hE : 0 < smoothHeathBrownExponentSum fs)
    (hgroup :
      (smoothHeathBrownExponentGrouping fs hE).IImaj (5 / 8)) :
    ∃ I : Finset (Fin fs.length), ∃ i : Fin fs.length, i ∈ I ∧
      X ^ (1 / 100 : ℝ) ≤
        smoothHeathBrownFactorScale (fs.get i) ∧
      smoothHeathBrownFactorScale (fs.get i) ≤
        (2 : ℝ) ^ 11 * Real.sqrt X ∧
      ∀ M : ℝ,
        (M = smoothHeathBrownFactorScale (fs.get i) / 2 ∨
          M = smoothHeathBrownFactorScale (fs.get i)) →
        X ^ (1 / 400 : ℝ) ≤ M ∧ M ≤ X := by
  have hX110 : ((2 : ℝ) ^ 22) ^ 5 ≤ X := by
    have hpow : ((2 : ℝ) ^ 22) ^ 5 = (2 : ℝ) ^ 110 := by
      norm_num [pow_mul]
    rw [hpow]
    exact (by norm_num : (2 : ℝ) ^ 110 ≤ (2 : ℝ) ^ 160).trans hX
  have hXnonneg : 0 ≤ X := by
    exact le_trans (by positivity : 0 ≤ (2 : ℝ) ^ 160) hX
  have hPbounds := smoothHeathBrownSupportRetained_scale_bounds
    hlen hfsne hXnonneg hret
  let P := smoothHeathBrownScaleProduct fs
  let w := smoothHeathBrownExponentGrouping fs hE
  let N : Fin fs.length → ℝ := fun i => P ^ (w.weight i)
  have hN : ∀ i, N i = P ^ w.weight i := by
    intro i
    rfl
  have hgroup' : w.IImaj (5 / 8) := by
    simpa [w] using hgroup
  obtain ⟨I, i, hiI, hNlo, hNhi, hMrange⟩ :=
    selectedSmoothGroupSmallFactor_mufRange w N hlen hX110 hX
      (by simpa [P, div_eq_mul_inv, mul_comm] using hPbounds) hN hgroup'
  have hscaleEq : N i = smoothHeathBrownFactorScale (fs.get i) := by
    dsimp [N, P, w]
    exact (smoothHeathBrownFactorScale_eq_scaleProduct_rpow_groupWeight
      fs hE i).symm
  refine ⟨I, i, hiI, ?_, ?_, ?_⟩
  · simpa [hscaleEq] using hNlo
  · simpa [hscaleEq] using hNhi
  · intro M hM
    have hM' : M = N i / 2 ∨ M = N i := by
      rcases hM with hM | hM
      · exact Or.inl (hM.trans (by rw [hscaleEq]))
      · exact Or.inr (hM.trans (by rw [hscaleEq]))
    exact hMrange M hM'

/-- The selected-factor range in the exact form consumed by
`smoothHeathBrownMobiusSubsetAssembly_from_MUF`.  If the factor chosen by the
three-group scale argument is tagged Möbius, this supplies that assembly's
`hMrange` premise for both dyadic pieces. -/
theorem smoothHeathBrownThreeGroupMobiusMUFRangeForAssembly
    {X : ℝ} (hX : (2 : ℝ) ^ 160 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (hlen : fs.length ≤ 20) (hfsne : fs ≠ [])
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fs)
    (hE : 0 < smoothHeathBrownExponentSum fs)
    (hgroup :
      (smoothHeathBrownExponentGrouping fs hE).IImaj (5 / 8)) :
    ∃ I : Finset (Fin fs.length), ∃ selected : Fin fs.length,
      selected ∈ I ∧
      X ^ (1 / 100 : ℝ) ≤
        smoothHeathBrownFactorScale (fs.get selected) ∧
      smoothHeathBrownFactorScale (fs.get selected) ≤
        (2 : ℝ) ^ 11 * Real.sqrt X ∧
      ∀ j : SmoothHeathBrownScaleIndex X,
        fs.get selected = .mobius j →
        ∀ M : ℝ,
          (M = smoothHeathBrownFactorScale (.mobius j) / 2 ∨
            M = smoothHeathBrownFactorScale (.mobius j)) →
          X ^ (1 / 400 : ℝ) ≤ M ∧ M ≤ X := by
  obtain ⟨I, selected, hselected, hNlo, hNhi, hMrange⟩ :=
    smoothHeathBrownThreeGroupSmallFactor_mufRange hX fs hlen hfsne
      hret hE hgroup
  refine ⟨I, selected, hselected, hNlo, hNhi, ?_⟩
  intro j htag M hM
  have hscaleEq : smoothHeathBrownFactorScale (fs.get selected) =
      smoothHeathBrownFactorScale (.mobius j) := by rw [htag]
  apply hMrange M
  rcases hM with hM | hM
  · exact Or.inl (hM.trans
      (congrArg (fun a : ℝ => a / 2) hscaleEq.symm))
  · exact Or.inr (hM.trans hscaleEq.symm)

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownSmallFactor_mufRange_of_scaleBounds
#print axioms FractionalPrimes.Literature.DirichletAdapter.selectedSmoothGroupSmallFactor_mufRange
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownFactorScale_eq_scaleProduct_rpow_groupWeight
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownThreeGroupSmallFactor_mufRange
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownThreeGroupMobiusMUFRangeForAssembly
