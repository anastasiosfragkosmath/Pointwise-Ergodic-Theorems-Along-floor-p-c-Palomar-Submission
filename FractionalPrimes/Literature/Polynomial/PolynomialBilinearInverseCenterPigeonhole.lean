module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseFirstRecurrence
public import Mathlib.Combinatorics.Pigeonhole

/-!
# The cross-centre pigeonhole in the bilinear polynomial inverse theorem

This file continues blueprint item `lbi:inverse-theorem` immediately after
formula (B2).  It first isolates the finite pigeonhole principle with a real
denominator budget, and then applies it to the first-recurrence denominator
attached to each good window centre.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

/-- If every element of a finite set is assigned a positive natural number at
most the real budget `A`, one value occurs with at least the expected `1/A`
fraction of any certified lower bound for the set's cardinality. -/
theorem finite_value_pigeonhole
    {α : Type*} [DecidableEq α]
    (S : Finset α) (A η : ℝ)
    (hA : 1 ≤ A) (hη : 0 < η) (hcount : η ≤ (S.card : ℝ))
    (f : α → ℕ)
    (hf : ∀ a ∈ S, 1 ≤ f a ∧ (f a : ℝ) ≤ A) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ A ∧
      η / A ≤ (((S.filter fun a => f a = q).card : ℕ) : ℝ) := by
  classical
  let K : ℕ := Nat.floor A
  let Q : Finset ℕ := Finset.Icc 1 K
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hKpos : 1 ≤ K := by
    dsimp [K]
    exact Nat.le_floor (by simpa using hA)
  have hKleA : (K : ℝ) ≤ A := by
    dsimp [K]
    exact Nat.floor_le (by linarith)
  have hQnonempty : Q.Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨by omega, hKpos⟩⟩
  have hmap : ∀ a ∈ S, f a ∈ Q := by
    intro a ha
    have haSpec := hf a ha
    have hupper : f a ≤ K := by
      dsimp [K]
      exact Nat.le_floor haSpec.2
    exact Finset.mem_Icc.mpr ⟨haSpec.1, hupper⟩
  have hQcard : Q.card = K := by
    simp [Q, Nat.card_Icc]
  have hthreshold : 0 ≤ η / A := by positivity
  have hsum : Q.card • (η / A) ≤ ∑ _a ∈ S, (1 : ℝ) := by
    rw [nsmul_eq_mul]
    calc
      (Q.card : ℝ) * (η / A) = (K : ℝ) * (η / A) := by rw [hQcard]
      _ ≤ A * (η / A) :=
        mul_le_mul_of_nonneg_right hKleA hthreshold
      _ = η := by field_simp [ne_of_gt hApos]
      _ ≤ (S.card : ℝ) := hcount
      _ = ∑ _a ∈ S, (1 : ℝ) := by simp
  obtain ⟨q, hqQ, hqLarge⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := S) (t := Q) (f := f) (w := fun _ => (1 : ℝ))
      hmap hQnonempty hsum
  have hqData := Finset.mem_Icc.mp hqQ
  refine ⟨q, hqData.1, ?_, ?_⟩
  · exact (Nat.cast_le.mpr hqData.2).trans hKleA
  · simpa using hqLarge

/-- The centres at which the exact good-pair count needed for the first
recurrence is available. -/
def bilinearGoodCenterSet
    (X H L M ρ : ℝ) (d : ℕ) (ν : ℕ → ℝ) : Finset ℕ :=
  (bilinearWindowCenters M).filter fun u =>
    ρ ^ 4 * (H / L) ^ 2 / 800 ≤
      ((bilinearGoodPairSet X H L M ρ d ν u).card : ℝ)

@[simp]
theorem mem_bilinearGoodCenterSet
    (X H L M ρ : ℝ) (d : ℕ) (ν : ℕ → ℝ) (u : ℕ) :
    u ∈ bilinearGoodCenterSet X H L M ρ d ν ↔
      u ∈ bilinearWindowCenters M ∧
        ρ ^ 4 * (H / L) ^ 2 / 800 ≤
          ((bilinearGoodPairSet X H L M ρ d ν u).card : ℝ) := by
  simp [bilinearGoodCenterSet]

/-- Cross-centre pigeonhole after formula (B2): one denominator `q₀ ≤ A`
works on at least `ρ⁴ M /(4000 A)` good centres, with the exact local
coefficient estimates retained on every selected centre. -/
theorem bilinearGoodCenters_commonDenominator
    (d : ℕ) (hd : 1 ≤ d)
    (X H L M ρ : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (hrZ : bilinearInverseZ d ρ⁻¹ ≤ H / L)
    (hsZ : bilinearInverseZ d ρ⁻¹ ≤ H / M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (ν : ℕ → ℝ)
    (hcenterCount : ρ ^ 4 * M / 4000 ≤
      ((bilinearGoodCenterSet X H L M ρ d ν).card : ℝ)) :
    ∃ q₀ : ℕ, ∃ U : Finset ℕ,
      1 ≤ q₀ ∧ (q₀ : ℝ) ≤ bilinearInverseA d ρ⁻¹ ∧
      U ⊆ bilinearWindowCenters M ∧
      ρ ^ 4 * M / (4000 * bilinearInverseA d ρ⁻¹) ≤ (U.card : ℝ) ∧
      ∀ u ∈ U, ∀ j, 1 ≤ j → j ≤ d →
        realDistanceToIntegers
            ((q₀ : ℝ) *
              bilinearGammaLinearCoefficient X
                (bilinearCommonLeftBase X (H / M) u)
                  d j ν (u : ℝ)) ≤
          bilinearInverseA d ρ⁻¹ * M ^ (j - 1) * X / H ^ (j + 1) := by
  classical
  let G := bilinearGoodCenterSet X H L M ρ d ν
  let A := bilinearInverseA d ρ⁻¹
  let η := ρ ^ 4 * M / 4000
  have hρinv : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hA : 1 ≤ A := by
    simpa [A] using (bilinearInverseBudget_values d hd ρ⁻¹ hρinv).2.2.2.1
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hrec : ∀ u ∈ G, ∃ q' : ℕ,
      1 ≤ q' ∧ (q' : ℝ) ≤ A ∧
      ∀ j, 1 ≤ j → j ≤ d →
        realDistanceToIntegers
            ((q' : ℝ) *
              bilinearGammaLinearCoefficient X
                (bilinearCommonLeftBase X (H / M) u)
                  d j ν (u : ℝ)) ≤
          A * M ^ (j - 1) * X / H ^ (j + 1) := by
    intro u hu
    have huData := mem_bilinearGoodCenterSet X H L M ρ d ν u |>.mp hu
    simpa [A] using bilinearGoodPairFirstRecurrence d hd X H L M ρ
      hL hM hX hHX hr hs hrZ hsZ hρ hρhalf u huData.1 ν huData.2
  let qOf : ℕ → ℕ := fun u =>
    if hu : u ∈ G then Classical.choose (hrec u hu) else 1
  have hqOf (u : ℕ) (hu : u ∈ G) :
      1 ≤ qOf u ∧ (qOf u : ℝ) ≤ A ∧
      ∀ j, 1 ≤ j → j ≤ d →
        realDistanceToIntegers
            ((qOf u : ℝ) *
              bilinearGammaLinearCoefficient X
                (bilinearCommonLeftBase X (H / M) u)
                  d j ν (u : ℝ)) ≤
          A * M ^ (j - 1) * X / H ^ (j + 1) := by
    dsimp [qOf]
    rw [dif_pos hu]
    exact Classical.choose_spec (hrec u hu)
  have hcount : η ≤ (G.card : ℝ) := by
    simpa [η, G] using hcenterCount
  obtain ⟨q₀, hq₀, hq₀A, hq₀Count⟩ :=
    finite_value_pigeonhole G A η hA hη hcount qOf
      (fun u hu => ⟨(hqOf u hu).1, (hqOf u hu).2.1⟩)
  let U := G.filter fun u => qOf u = q₀
  refine ⟨q₀, U, hq₀, ?_, ?_, ?_, ?_⟩
  · simpa [A] using hq₀A
  · intro u hu
    have huG := (Finset.mem_filter.mp hu).1
    exact (mem_bilinearGoodCenterSet X H L M ρ d ν u |>.mp huG).1
  · have hηA : η / A = ρ ^ 4 * M / (4000 * A) := by
      dsimp [η]
      field_simp [ne_of_gt hApos]
    rw [← hηA]
    simpa [U] using hq₀Count
  · intro u hu j hj hjd
    have huData := Finset.mem_filter.mp hu
    have hspec := (hqOf u huData.1).2.2 j hj hjd
    rw [huData.2] at hspec
    simpa [A] using hspec

/-- The preceding unweighted-energy and window-energy lemmas provide exactly
the good-centre count required by the cross-centre pigeonhole.  Thus a large
source correlation already yields the common denominator `q₀` and the full
family of local (B2) estimates. -/
theorem bilinearLargeCorrelation_commonDenominator
    (d : ℕ) (hd : 1 ≤ d)
    (X H L M ρ : ℝ) (hL : 0 < L) (hMtwo : 2 ≤ M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (hrEight : 8 ≤ H / L) (hrM : H / L ≤ M)
    (hrZ : bilinearInverseZ d ρ⁻¹ ≤ H / L)
    (hsZ : bilinearInverseZ d ρ⁻¹ ≤ H / M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (α β : ℕ → ℂ) (ν : ℕ → ℝ)
    (hUV : 0 < bilinearU L α * bilinearV M β)
    (hlarge : ρ * H * (bilinearU L α * bilinearV M β) ≤
      ‖bilinearS X H M α β (bilinearCenteredPhase X d ν)‖) :
    ∃ q₀ : ℕ, ∃ U : Finset ℕ,
      1 ≤ q₀ ∧ (q₀ : ℝ) ≤ bilinearInverseA d ρ⁻¹ ∧
      U ⊆ bilinearWindowCenters M ∧
      ρ ^ 4 * M / (4000 * bilinearInverseA d ρ⁻¹) ≤ (U.card : ℝ) ∧
      ∀ u ∈ U, ∀ j, 1 ≤ j → j ≤ d →
        realDistanceToIntegers
            ((q₀ : ℝ) *
              bilinearGammaLinearCoefficient X
                (bilinearCommonLeftBase X (H / M) u)
                  d j ν (u : ℝ)) ≤
          bilinearInverseA d ρ⁻¹ * M ^ (j - 1) * X / H ^ (j + 1) := by
  have hM : 0 < M := by linarith
  obtain ⟨hzero, hbound, henergy⟩ :=
    bilinearUnweightedEnergy X H L M ρ hL hM hX hHX hr hs hρ
      α β (bilinearCenteredPhase X d ν) hUV hlarge
  have hcenterCount : ρ ^ 4 * M / 4000 ≤
      ((bilinearGoodCenterSet X H L M ρ d ν).card : ℝ) := by
    have hwindow := bilinearWindowEnergy M (H / L) (H / M) ρ
      hMtwo hrEight hrM hs hρ hρhalf
      (bilinearC X H L (bilinearCenteredPhase X d ν))
      hzero hbound henergy
    unfold bilinearGoodCenterSet bilinearGoodPairSet
    convert hwindow using 1
  exact bilinearGoodCenters_commonDenominator d hd X H L M ρ
    hL hM hX hHX hr hs hrZ hsZ hρ hρhalf ν hcenterCount

#print axioms finite_value_pigeonhole
#print axioms bilinearGoodCenters_commonDenominator
#print axioms bilinearLargeCorrelation_commonDenominator

end

end FractionalPrimes.Literature.Polynomial
