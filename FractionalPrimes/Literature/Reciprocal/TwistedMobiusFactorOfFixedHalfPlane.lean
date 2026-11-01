module
public import FractionalPrimes.Literature.Reciprocal.TwistedMobiusPrefix
public import FractionalPrimes.Literature.Reciprocal.TwistedMufAbelCentered
@[expose] public section

noncomputable section

open Finset MeasureTheory Set
open FractionalPrimes.Literature.LongArithmetic

namespace FractionalPrimes.Literature.Reciprocal

private theorem twistedMufPrefix_eq_cesaroPerronSharpSum
    (a : ℕ → ℂ) (x : ℝ) :
    twistedMufPrefix a x = cesaroPerronSharpSum a x := by
  let m := Nat.floor x
  have hdisj : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 m) := by
    simp
  have hdecomp : Finset.Icc 0 m = {0} ∪ Finset.Icc 1 m := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  change (∑ n ∈ Finset.Icc 0 m, (if n = 0 then 0 else a n)) =
    ∑ n ∈ Finset.Icc 1 m, a n
  rw [hdecomp, Finset.sum_union hdisj]
  simp
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  simp [Nat.ne_of_gt hnpos]

/-- The fixed-half-plane input implies the exact Möbius uniformity leaf
`lrc:muf`. The multiplier range is enlarged to `1 ≤ r ≤ X`, as in the
approved blueprint. -/
theorem mobiusFactorOfFixedHalfPlane {α A B D : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ {q : ℕ} [NeZero q] (hZFR : fixedHalfPlaneProperty)
        {X L : ℝ} (hX₀ : X₀ ≤ X) (hXL : X ^ α ≤ L) (hLX : L ≤ X)
        (hq : 1 ≤ q) (hqX : (q : ℝ) ≤ (Real.log X) ^ B)
        (r : ℕ) (hr : 1 ≤ r) (hrX : (r : ℝ) ≤ X)
        (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : |t| ≤ X ^ A)
        {u v : ℝ} (huL : L ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * L),
        ‖∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
            twistedMobiusRectangleCoefficient r χ t n *
              inverseSqrtWeight (n : ℝ)‖ ≤
          (8 + 1536 * Real.exp 1) * Real.sqrt L * (Real.log X) ^ (-D) := by
  obtain ⟨X₀, hX₀ge3, hprefix⟩ :=
    twistedMobiusPrefix hα hα1 hA hB hD
  refine ⟨X₀, hX₀ge3, ?_⟩
  intro q inst hZFR X L hX₀ hXL hLX hq hqX r hr hrX χ t ht u v huL huv hv
  let a : ℕ → ℂ := twistedMobiusRectangleCoefficient r χ t
  let C : ℝ := 2 + 384 * Real.exp 1
  let w : ℝ := Real.log X
  let K : ℝ := 4 * C * L * w ^ (-(D + 2))
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := by
    have : 0 < X ^ α := Real.rpow_pos_of_pos hXpos α
    linarith
  have hwpos : 0 < w := Real.log_pos (by linarith)
  have hwone : 1 ≤ w := by
    have hexp : Real.exp 1 < 3 := by
      have h := Real.exp_one_lt_d9
      norm_num at h ⊢
      linarith
    apply (Real.le_log_iff_exp_le (by linarith : 0 < X)).2
    linarith
  have hCpos : 0 < C := by positivity
  have hKnonneg : 0 ≤ K := by positivity
  have huPos : 0 < u := lt_of_lt_of_le hLpos huL

  have hprefixBound (z : ℝ) (hz : L ≤ z ∧ z ≤ 2 * L) :
      ‖twistedMufPrefix a z‖ ≤ 2 * C * L * w ^ (-(D + 2)) := by
    have hzXα : X ^ α ≤ z := hXL.trans hz.1
    have hz2X : z ≤ 2 * X := by nlinarith [hz.2, hLX]
    have hsharp := hprefix (q := q) hZFR hX₀ hzXα hz2X r hr hrX hq hqX χ t ht
    calc
      ‖twistedMufPrefix a z‖ =
          ‖cesaroPerronSharpSum a z‖ := by
            rw [twistedMufPrefix_eq_cesaroPerronSharpSum]
      _ ≤ C * z * w ^ (-(D + 2)) := by
            simpa [a, C, w, twistedMobiusRectangleCoefficient] using hsharp
      _ ≤ 2 * C * L * w ^ (-(D + 2)) := by
            have hpow : 0 ≤ w ^ (-(D + 2)) := Real.rpow_nonneg (le_of_lt hwpos) _
            nlinarith [hz.2, hCpos, hpow]

  have huRange : L ≤ u ∧ u ≤ 2 * L := by
    constructor
    · exact huL
    · exact huv.trans hv
  have hvRange : L ≤ v ∧ v ≤ 2 * L := by
    constructor
    · exact huL.trans huv
    · exact hv
  have hprefixDiff (z : ℝ) (hz : L ≤ z ∧ z ≤ 2 * L) :
      ‖twistedMufPrefix a z - twistedMufPrefix a u‖ ≤ K := by
    have hzBound := hprefixBound z hz
    have huBound := hprefixBound u huRange
    calc
      _ ≤ ‖twistedMufPrefix a z‖ + ‖twistedMufPrefix a u‖ := norm_sub_le _ _
      _ ≤ 2 * C * L * w ^ (-(D + 2)) + 2 * C * L * w ^ (-(D + 2)) :=
        add_le_add hzBound huBound
      _ = K := by simp [K]; ring

  have hIntCont : ContinuousOn (fun z : ℝ => z ^ (-3 / 2 : ℝ)) (Set.Icc u v) := by
    apply continuousOn_id.rpow_const
    intro z hz
    left
    exact ne_of_gt (lt_of_lt_of_le huPos hz.1)
  have hIntIntegrable :
      IntervalIntegrable (fun z : ℝ => K * z ^ (-3 / 2 : ℝ)) volume u v := by
    apply (continuousOn_const.mul hIntCont).intervalIntegrable_of_Icc huv
  let F : ℝ → ℂ := fun z =>
    (twistedMufPrefix a z - twistedMufPrefix a u) *
      (((z ^ (-3 / 2 : ℝ) : ℝ) : ℂ))
  have hFbound (z : ℝ) (hz : z ∈ Set.Ioc u v) : ‖F z‖ ≤ K * z ^ (-3 / 2 : ℝ) := by
    have hzIcc : z ∈ Set.Icc u v := ⟨le_of_lt hz.1, hz.2⟩
    have hzRange : L ≤ z ∧ z ≤ 2 * L := by
      constructor
      · exact huL.trans (le_of_lt hz.1)
      · exact hz.2.trans hv
    have hdiff := hprefixDiff z hzRange
    have hzpos : 0 < z := lt_of_lt_of_le huPos (le_of_lt hz.1)
    have hpowpos : 0 ≤ z ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hzpos.le _
    change ‖(twistedMufPrefix a z - twistedMufPrefix a u) *
      (((z ^ (-3 / 2 : ℝ) : ℝ) : ℂ))‖ ≤ K * z ^ (-3 / 2 : ℝ)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpowpos]
    exact mul_le_mul_of_nonneg_right hdiff hpowpos
  have hIntNorm :
      ‖∫ z in u..v, F z‖ ≤ K * (∫ z in u..v, z ^ (-3 / 2 : ℝ)) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le
      (μ := volume) huv
      (Filter.Eventually.of_forall fun z => fun hz => hFbound z hz)
      hIntIntegrable
    simpa [F, intervalIntegral.integral_const_mul] using h
  have hIntEval :
      (∫ z in u..v, z ^ (-3 / 2 : ℝ)) =
        2 * (u ^ (-1 / 2 : ℝ) - v ^ (-1 / 2 : ℝ)) :=
    intervalIntegral_rpow_neg_three_halves huPos huv
  have hAbel := twistedMufAbelSummation_explicit a huPos huv
  have hAbel' := hAbel
  rw [show (∫ z in Set.Ioc u v,
      (twistedMufPrefix a z - twistedMufPrefix a u) *
        (((z ^ (-3 / 2 : ℝ) : ℝ) : ℂ))) = ∫ z in u..v, F z by
          rw [← intervalIntegral.integral_of_le huv]
          ] at hAbel'

  have hvPos : 0 < v := lt_of_lt_of_le huPos huv
  have hweightV : ‖inverseSqrtWeight v‖ = v ^ (-1 / 2 : ℝ) := by
    simp [inverseSqrtWeight, abs_of_pos (Real.rpow_pos_of_pos hvPos _)]
  have hsumNorm :
      ‖∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
          a n * inverseSqrtWeight (n : ℝ)‖ ≤ K * u ^ (-1 / 2 : ℝ) := by
    rw [hAbel']
    calc
      _ ≤ ‖inverseSqrtWeight v * (twistedMufPrefix a v - twistedMufPrefix a u)‖ +
          ‖(1 / 2 : ℂ) * ∫ z in u..v, F z‖ := norm_add_le _ _
      _ ≤ K * v ^ (-1 / 2 : ℝ) +
          (1 / 2 : ℝ) * (K * (∫ z in u..v, z ^ (-3 / 2 : ℝ))) := by
            have hvDiff := hprefixDiff v hvRange
            have hfirst :
                ‖inverseSqrtWeight v * (twistedMufPrefix a v - twistedMufPrefix a u)‖ ≤
                  K * v ^ (-1 / 2 : ℝ) := by
              rw [norm_mul, hweightV]
              exact (mul_le_mul_of_nonneg_left hvDiff
                (Real.rpow_nonneg (le_of_lt hvPos) _)).trans_eq (by ring_nf)
            have hsecond :
                ‖(1 / 2 : ℂ) * ∫ z in u..v, F z‖ ≤
                  (1 / 2 : ℝ) * (K * (∫ z in u..v, z ^ (-3 / 2 : ℝ))) := by
              rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
              exact mul_le_mul_of_nonneg_left hIntNorm (by norm_num)
            exact add_le_add hfirst hsecond
      _ = K * u ^ (-1 / 2 : ℝ) := by rw [hIntEval]; ring

  have huInv : u ^ (-1 / 2 : ℝ) ≤ L ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hLpos huL (by norm_num)
  have hmulpow : L * L ^ (-1 / 2 : ℝ) = Real.sqrt L := by
    calc
      L * L ^ (-1 / 2 : ℝ) = L ^ (1 + (-1 / 2 : ℝ)) := by
        calc
          L * L ^ (-1 / 2 : ℝ) = L ^ (1 : ℝ) * L ^ (-1 / 2 : ℝ) := by rw [Real.rpow_one]
          _ = L ^ (1 + (-1 / 2 : ℝ)) := by rw [← Real.rpow_add hLpos]
      _ = L ^ (1 / 2 : ℝ) := by congr 1 <;> ring
      _ = Real.sqrt L := (Real.sqrt_eq_rpow L).symm
  have hwPow : w ^ (-(D + 2)) ≤ w ^ (-D) := by
    apply Real.rpow_le_rpow_of_exponent_le hwone
    linarith
  calc
    _ ≤ K * u ^ (-1 / 2 : ℝ) := hsumNorm
    _ ≤ K * L ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_left huInv hKnonneg
    _ = 4 * C * Real.sqrt L * w ^ (-(D + 2)) := by
      simp only [K]
      rw [← hmulpow]
      ring
    _ ≤ (8 + 1536 * Real.exp 1) * Real.sqrt L * w ^ (-D) := by
      have hfac : 0 ≤ 4 * C * Real.sqrt L := by positivity
      have hchange : 4 * C = 8 + 1536 * Real.exp 1 := by
        dsimp [C]
        ring
      rw [← hchange]
      exact mul_le_mul_of_nonneg_left hwPow hfac

#print axioms mobiusFactorOfFixedHalfPlane

end FractionalPrimes.Literature.Reciprocal

end
