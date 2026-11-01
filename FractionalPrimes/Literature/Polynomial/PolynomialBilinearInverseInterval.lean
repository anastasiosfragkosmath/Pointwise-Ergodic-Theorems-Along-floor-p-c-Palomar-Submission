module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseNumerics
public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearCommonCentre
public import FractionalPrimes.Literature.Polynomial.ScalarWeylInverse

/-!
# The common interval in the bilinear inverse theorem

This file isolates the integer-interval reindexing at the first scalar Weyl
application in blueprint item `lbi:inverse-theorem`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

open _root_.Polynomial

/-- The strict lower endpoint shared by the two product intervals. -/
def bilinearCommonLower (X : ℝ) (m m' : ℕ) : ℕ :=
  max (Nat.floor (X / (m : ℝ))) (Nat.floor (X / (m' : ℝ)))

/-- The weak upper endpoint shared by the two product intervals. -/
def bilinearCommonUpper (X H : ℝ) (m m' : ℕ) : ℕ :=
  min (Nat.floor ((X + H) / (m : ℝ)))
    (Nat.floor ((X + H) / (m' : ℝ)))

/-- The phase difference after translating the common left variable by
`ell0`. -/
def bilinearPairShiftPolynomial (X : ℝ) (ell0 : ℤ)
    (d : ℕ) (ν : ℕ → ℝ) (m m' : ℕ) : Polynomial ℝ :=
  (bilinearCenteredPhase X d ν).comp
      (Polynomial.C ((ell0 : ℝ) * (m : ℝ)) +
        Polynomial.C (m : ℝ) * Polynomial.X) -
    (bilinearCenteredPhase X d ν).comp
      (Polynomial.C ((ell0 : ℝ) * (m' : ℝ)) +
        Polynomial.C (m' : ℝ) * Polynomial.X)

@[simp]
theorem bilinearPairShiftPolynomial_eval
    (X : ℝ) (ell0 : ℤ) (d : ℕ) (ν : ℕ → ℝ)
    (m m' : ℕ) (t : ℝ) :
    (bilinearPairShiftPolynomial X ell0 d ν m m').eval t =
      (bilinearCenteredPhase X d ν).eval
          (((ell0 : ℝ) + t) * (m : ℝ)) -
        (bilinearCenteredPhase X d ν).eval
          (((ell0 : ℝ) + t) * (m' : ℝ)) := by
  simp only [bilinearPairShiftPolynomial, Polynomial.eval_sub,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  congr 2 <;> ring

/-- The explicitly centered phase has degree at most the displayed degree. -/
theorem bilinearCenteredPhase_natDegree_le
    (X : ℝ) (d : ℕ) (ν : ℕ → ℝ) :
    (bilinearCenteredPhase X d ν).natDegree ≤ d := by
  unfold bilinearCenteredPhase
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hid : i ≤ d := by
    have := Finset.mem_range.mp hi
    omega
  calc
    (Polynomial.C (ν i) *
        (Polynomial.X - Polynomial.C X) ^ i).natDegree ≤
        (Polynomial.C (ν i)).natDegree +
          ((Polynomial.X - Polynomial.C X) ^ i).natDegree :=
      Polynomial.natDegree_mul_le
    _ = i := by simp
    _ ≤ d := hid

/-- The shifted pair phase remains of degree at most `d`. -/
theorem bilinearPairShiftPolynomial_natDegree_le
    (X : ℝ) (ell0 : ℤ) (d : ℕ) (ν : ℕ → ℝ)
    (m m' : ℕ) :
    (bilinearPairShiftPolynomial X ell0 d ν m m').natDegree ≤ d := by
  have hlinear (a : ℕ) :
      (Polynomial.C ((ell0 : ℝ) * (a : ℝ)) +
        Polynomial.C (a : ℝ) * Polynomial.X).natDegree ≤ 1 := by
    have hc : (Polynomial.C ((ell0 : ℝ) * (a : ℝ)) :
        Polynomial ℝ).natDegree ≤ 1 := by
      rw [Polynomial.natDegree_C]
      omega
    have hx : (Polynomial.C (a : ℝ) * (Polynomial.X :
        Polynomial ℝ)).natDegree ≤ 1 := by
      exact (Polynomial.natDegree_C_mul_le (a : ℝ) Polynomial.X).trans
        (by simp)
    exact (Polynomial.natDegree_add_le _ _).trans (max_le hc hx)
  have hcomp (a : ℕ) :
      ((bilinearCenteredPhase X d ν).comp
        (Polynomial.C ((ell0 : ℝ) * (a : ℝ)) +
          Polynomial.C (a : ℝ) * Polynomial.X)).natDegree ≤ d := by
    calc
      _ ≤ (bilinearCenteredPhase X d ν).natDegree *
          (Polynomial.C ((ell0 : ℝ) * (a : ℝ)) +
            Polynomial.C (a : ℝ) * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ d * 1 := Nat.mul_le_mul
        (bilinearCenteredPhase_natDegree_le X d ν) (hlinear a)
      _ = d := by simp
  exact (Polynomial.natDegree_sub_le_of_le (hcomp m) (hcomp m')).trans
    (by simp)

/-- Evaluation at the translated integer variable recovers the original
product phase difference exactly. -/
theorem bilinearPairShiftPolynomial_eval_nat_sub
    (X : ℝ) (ell0 : ℤ) (d : ℕ) (ν : ℕ → ℝ)
    (m m' l : ℕ) :
    (bilinearPairShiftPolynomial X ell0 d ν m m').eval
        (((l : ℤ) - ell0 : ℤ) : ℝ) =
      (bilinearCenteredPhase X d ν).eval ((l * m : ℕ) : ℝ) -
        (bilinearCenteredPhase X d ν).eval ((l * m' : ℕ) : ℝ) := by
  rw [bilinearPairShiftPolynomial_eval]
  push_cast
  congr 2 <;> ring

/-- Under the source scale assumptions, the common left support is exactly
one half-open interval of natural numbers. -/
theorem bilinearCommonLeftSet_eq_Ioc
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (m m' : ℕ) (hm : m ∈ bilinearRightSet M)
    (hm' : m' ∈ bilinearRightSet M) :
    bilinearCommonLeftSet X H L m m' =
      Finset.Ioc (bilinearCommonLower X m m')
        (bilinearCommonUpper X H m m') := by
  classical
  have hmPos : 0 < m := by
    have := (mem_bilinearRightSet M m).mp hm
    omega
  have hm'Pos : 0 < m' := by
    have := (mem_bilinearRightSet M m').mp hm'
    omega
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hmPos
  have hm'Real : 0 < (m' : ℝ) := by exact_mod_cast hm'Pos
  ext l
  simp only [bilinearCommonLeftSet, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hlL, hlmLower, hlmUpper, hlm'Lower, hlm'Upper⟩
    have hlPos : 0 < l := (mem_bilinearLeftSet L l).mp hlL |>.1
    have hlNe : l ≠ 0 := Nat.ne_of_gt hlPos
    have hlowerM : Nat.floor (X / (m : ℝ)) < l := by
      rw [Nat.floor_lt' hlNe]
      apply (div_lt_iff₀ hmReal).2
      norm_num at hlmLower ⊢
      exact hlmLower
    have hlowerM' : Nat.floor (X / (m' : ℝ)) < l := by
      rw [Nat.floor_lt' hlNe]
      apply (div_lt_iff₀ hm'Real).2
      norm_num at hlm'Lower ⊢
      exact hlm'Lower
    have hupperM : l ≤ Nat.floor ((X + H) / (m : ℝ)) := by
      rw [Nat.le_floor_iff' hlNe]
      apply (le_div_iff₀ hmReal).2
      norm_num at hlmUpper ⊢
      exact hlmUpper
    have hupperM' : l ≤ Nat.floor ((X + H) / (m' : ℝ)) := by
      rw [Nat.le_floor_iff' hlNe]
      apply (le_div_iff₀ hm'Real).2
      norm_num at hlm'Upper ⊢
      exact hlm'Upper
    exact ⟨(max_lt_iff.mpr ⟨hlowerM, hlowerM'⟩),
      (le_min_iff.mpr ⟨hupperM, hupperM'⟩)⟩
  · rintro ⟨hlower, hupper⟩
    have hlowerM : Nat.floor (X / (m : ℝ)) < l :=
      lt_of_le_of_lt (le_max_left _ _) hlower
    have hlowerM' : Nat.floor (X / (m' : ℝ)) < l :=
      lt_of_le_of_lt (le_max_right _ _) hlower
    have hlPos : 0 < l := lt_of_le_of_lt (Nat.zero_le _) hlowerM
    have hlNe : l ≠ 0 := Nat.ne_of_gt hlPos
    have hupperM : l ≤ Nat.floor ((X + H) / (m : ℝ)) :=
      le_trans hupper (min_le_left _ _)
    have hupperM' : l ≤ Nat.floor ((X + H) / (m' : ℝ)) :=
      le_trans hupper (min_le_right _ _)
    have hlmLower : X < ((l * m : ℕ) : ℝ) := by
      have hquot := (Nat.floor_lt' hlNe).mp hlowerM
      apply (div_lt_iff₀ hmReal).mp at hquot
      simpa using hquot
    have hlmUpper : ((l * m : ℕ) : ℝ) ≤ X + H := by
      have hquot := (Nat.le_floor_iff' hlNe).mp hupperM
      apply (le_div_iff₀ hmReal).mp at hquot
      simpa using hquot
    have hlm'Lower : X < ((l * m' : ℕ) : ℝ) := by
      have hquot := (Nat.floor_lt' hlNe).mp hlowerM'
      apply (div_lt_iff₀ hm'Real).mp at hquot
      simpa using hquot
    have hlm'Upper : ((l * m' : ℕ) : ℝ) ≤ X + H := by
      have hquot := (Nat.le_floor_iff' hlNe).mp hupperM'
      apply (le_div_iff₀ hm'Real).mp at hquot
      simpa using hquot
    have hlm : l ∈ bilinearProductIntervalSet X H m :=
      (mem_bilinearProductIntervalSet X H m l hmPos).mpr
        ⟨hlPos, hlmLower, hlmUpper⟩
    have hlL := bilinearProductIntervalSet_subset_left
      X H L M hL hM hX hHX m l hm hlm
    exact ⟨hlL, hlmLower, hlmUpper, hlm'Lower, hlm'Upper⟩

/-- Translating the common left support by an arbitrary integer origin turns
it into the literal half-open integer interval required by
`scalarWeylInverse`. -/
theorem sum_bilinearCommonLeftSet_shift
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (m m' : ℕ) (hm : m ∈ bilinearRightSet M)
    (hm' : m' ∈ bilinearRightSet M)
    (ell0 : ℤ) (f : ℤ → ℂ) :
    (∑ l ∈ bilinearCommonLeftSet X H L m m',
        f ((l : ℤ) - ell0)) =
      ∑ n ∈ Finset.Ico
        ((bilinearCommonLower X m m' : ℤ) + 1 - ell0)
        ((bilinearCommonUpper X H m m' : ℤ) + 1 - ell0), f n := by
  classical
  rw [bilinearCommonLeftSet_eq_Ioc X H L M hL hM hX hHX m m' hm hm']
  refine Finset.sum_bij'
      (s := Finset.Ioc (bilinearCommonLower X m m')
        (bilinearCommonUpper X H m m'))
      (t := Finset.Ico
        ((bilinearCommonLower X m m' : ℤ) + 1 - ell0)
        ((bilinearCommonUpper X H m m' : ℤ) + 1 - ell0))
      (f := fun l => f ((l : ℤ) - ell0)) (g := f)
      (fun l _ => (l : ℤ) - ell0)
      (fun n _ => (n + ell0).toNat) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_Ioc] at hl
    simp only [Finset.mem_Ico]
    have hlower :
        (bilinearCommonLower X m m' : ℤ) < (l : ℤ) := by
      exact_mod_cast hl.1
    have hupper :
        (l : ℤ) ≤ (bilinearCommonUpper X H m m' : ℤ) := by
      exact_mod_cast hl.2
    omega
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    simp only [Finset.mem_Ioc]
    have hzLower :
        (bilinearCommonLower X m m' : ℤ) < n + ell0 := by omega
    have hzUpper :
        n + ell0 ≤ (bilinearCommonUpper X H m m' : ℤ) := by omega
    have hzNonneg : 0 ≤ n + ell0 := by
      have hnonneg : 0 ≤ (bilinearCommonLower X m m' : ℤ) := by
        exact_mod_cast Nat.zero_le (bilinearCommonLower X m m')
      omega
    have hcast : ((n + ell0).toNat : ℤ) = n + ell0 :=
      Int.toNat_of_nonneg hzNonneg
    constructor
    · exact_mod_cast (show (bilinearCommonLower X m m' : ℤ) <
          ((n + ell0).toNat : ℤ) by simpa [hcast] using hzLower)
    · exact_mod_cast (show ((n + ell0).toNat : ℤ) ≤
          (bilinearCommonUpper X H m m' : ℤ) by simpa [hcast] using hzUpper)
  · intro l hl
    simp
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    have hzNonneg : 0 ≤ n + ell0 := by
      have hnonneg : 0 ≤ (bilinearCommonLower X m m' : ℤ) := by
        exact_mod_cast Nat.zero_le (bilinearCommonLower X m m')
      omega
    rw [Int.toNat_of_nonneg hzNonneg]
    omega
  · intro l hl
    rfl

/-- The correlation for a centered phase is exactly the scalar-Weyl sum on
the translated integer interval. -/
theorem bilinearC_centered_eq_shifted_Ico
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (m m' : ℕ) (hm : m ∈ bilinearRightSet M)
    (hm' : m' ∈ bilinearRightSet M)
    (ell0 : ℤ) (d : ℕ) (ν : ℕ → ℝ) :
    bilinearC X H L (bilinearCenteredPhase X d ν) m m' =
      ∑ n ∈ Finset.Ico
        ((bilinearCommonLower X m m' : ℤ) + 1 - ell0)
        ((bilinearCommonUpper X H m m' : ℤ) + 1 - ell0),
          unitFrequencyPhase
            ((bilinearPairShiftPolynomial X ell0 d ν m m').eval (n : ℝ)) := by
  unfold bilinearC
  calc
    (∑ l ∈ bilinearCommonLeftSet X H L m m',
        unitFrequencyPhase
          ((bilinearCenteredPhase X d ν).eval ((l * m : ℕ) : ℝ) -
            (bilinearCenteredPhase X d ν).eval ((l * m' : ℕ) : ℝ))) =
      ∑ l ∈ bilinearCommonLeftSet X H L m m',
        unitFrequencyPhase
          ((bilinearPairShiftPolynomial X ell0 d ν m m').eval
            (((l : ℤ) - ell0 : ℤ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [bilinearPairShiftPolynomial_eval_nat_sub]
    _ = _ := sum_bilinearCommonLeftSet_shift X H L M hL hM hX hHX
      m m' hm hm' ell0
        (fun n => unitFrequencyPhase
          ((bilinearPairShiftPolynomial X ell0 d ν m m').eval (n : ℝ)))

/-- For two indices in one short window, the translated common interval lies
inside the common-centre box `{1, ..., N₀}`. -/
theorem bilinearCommonShiftInterval_subset
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (u : ℕ) (hu : u ∈ bilinearWindowCenters M)
    (m m' : ℕ) (hm : m ∈ bilinearWindow M (H / L) u)
    (hm' : m' ∈ bilinearWindow M (H / L) u) :
    Finset.Ico
        ((bilinearCommonLower X m m' : ℤ) + 1 -
          bilinearCommonLeftBase X (H / M) u)
        ((bilinearCommonUpper X H m m' : ℤ) + 1 -
          bilinearCommonLeftBase X (H / M) u) ⊆
      Finset.Icc (1 : ℤ) (bilinearCommonLeftLength (H / M) : ℤ) := by
  intro n hn
  have hnData := Finset.mem_Ico.mp hn
  let ell0 := bilinearCommonLeftBase X (H / M) u
  let z : ℤ := n + ell0
  have hzLower : (bilinearCommonLower X m m' : ℤ) < z := by
    dsimp [z, ell0]
    omega
  have hzUpper : z ≤ (bilinearCommonUpper X H m m' : ℤ) := by
    dsimp [z, ell0]
    omega
  have hzNonneg : 0 ≤ z := by
    have hnonneg : 0 ≤ (bilinearCommonLower X m m' : ℤ) := by
      exact_mod_cast Nat.zero_le (bilinearCommonLower X m m')
    omega
  let l : ℕ := z.toNat
  have hlCast : (l : ℤ) = z := by
    dsimp [l]
    exact Int.toNat_of_nonneg hzNonneg
  have hlIoc : l ∈ Finset.Ioc (bilinearCommonLower X m m')
      (bilinearCommonUpper X H m m') := by
    rw [Finset.mem_Ioc]
    constructor
    · exact_mod_cast (show (bilinearCommonLower X m m' : ℤ) <
          (l : ℤ) by simpa [hlCast] using hzLower)
    · exact_mod_cast (show (l : ℤ) ≤
          (bilinearCommonUpper X H m m' : ℤ) by simpa [hlCast] using hzUpper)
  have hmRight : m ∈ bilinearRightSet M :=
    (mem_bilinearWindow M (H / L) u m).mp hm |>.1
  have hm'Right : m' ∈ bilinearRightSet M :=
    (mem_bilinearWindow M (H / L) u m').mp hm' |>.1
  have hlCommon : l ∈ bilinearCommonLeftSet X H L m m' := by
    rw [bilinearCommonLeftSet_eq_Ioc X H L M hL hM hX hHX
      m m' hmRight hm'Right]
    exact hlIoc
  rcases Finset.mem_filter.mp hlCommon with
    ⟨hlL, hlmLower, hlmUpper, hlm'Lower, hlm'Upper⟩
  have hbounds := bilinearCommonCentre_index_bounds X H L M hL hM hX
    hr hs u m hu hm (l : ℤ) (by
      constructor
      · simpa using hlmLower
      · simpa using hlmUpper)
  have hnEq : (l : ℤ) - ell0 = n := by
    rw [hlCast]
    dsimp [z]
    omega
  rw [Finset.mem_Icc]
  constructor
  · simpa [hnEq, ell0] using hbounds.1
  · simpa [hnEq, ell0] using hbounds.2.1

/-- The common-centre length is a positive natural number and has the exact
upper bound used to normalize a good correlation. -/
theorem bilinearCommonLeftLength_bounds
    (s : ℝ) (hs : 1 ≤ s) :
    1 ≤ bilinearCommonLeftLength s ∧
      (bilinearCommonLeftLength s : ℝ) ≤ 25 * s := by
  have hs0 : 0 ≤ 24 * s := by positivity
  have hlower : 24 * s ≤ (bilinearCommonLeftLength s : ℝ) := by
    exact Nat.le_ceil (24 * s)
  have hposReal : (1 : ℝ) ≤ (bilinearCommonLeftLength s : ℝ) := by
    linarith
  have hpos : 1 ≤ bilinearCommonLeftLength s := by exact_mod_cast hposReal
  have hceil : (bilinearCommonLeftLength s : ℝ) < 24 * s + 1 := by
    exact Nat.ceil_lt_add_one hs0
  exact ⟨hpos, by linarith⟩

/-- A good pair in one short window supplies the scalar Weyl denominator
with the exact first-stage budget. -/
theorem bilinearGoodPairWeyl
    (d : ℕ) (hd : 1 ≤ d)
    (X H L M ρ : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (u : ℕ) (hu : u ∈ bilinearWindowCenters M)
    (m m' : ℕ) (hm : m ∈ bilinearWindow M (H / L) u)
    (hm' : m' ∈ bilinearWindow M (H / L) u)
    (ν : ℕ → ℝ)
    (hlarge : ρ ^ 2 * (H / M) / 100 ≤
      ‖bilinearC X H L (bilinearCenteredPhase X d ν) m m'‖) :
    ∃ q : ℕ,
      1 ≤ q ∧
      (q : ℝ) ≤ bilinearInverseB d ρ⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        (bilinearCommonLeftLength (H / M) : ℝ) ^ j *
          realDistanceToIntegers
            ((q : ℝ) *
              ((bilinearGammaPolynomial X
                  (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m : ℝ) -
                (bilinearGammaPolynomial X
                  (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m' : ℝ))) ≤
          bilinearInverseB d ρ⁻¹ := by
  let s : ℝ := H / M
  let ell0 : ℤ := bilinearCommonLeftBase X s u
  let N0 : ℕ := bilinearCommonLeftLength s
  let δ : ℝ := ρ ^ 2 / 2500
  let Q : Polynomial ℝ := bilinearPairShiftPolynomial X ell0 d ν m m'
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ < 1 / 2 := by
    dsimp [δ]
    nlinarith [sq_pos_of_pos hρ]
  have hN0Data := bilinearCommonLeftLength_bounds s (by simpa [s] using hs)
  have hN0 : 1 ≤ N0 := by simpa [N0] using hN0Data.1
  have hQdeg : Q.natDegree ≤ d := by
    simpa [Q] using bilinearPairShiftPolynomial_natDegree_le X ell0 d ν m m'
  have hsubset :
      Finset.Ico
          ((bilinearCommonLower X m m' : ℤ) + 1 - ell0)
          ((bilinearCommonUpper X H m m' : ℤ) + 1 - ell0) ⊆
        Finset.Icc (1 : ℤ) (N0 : ℤ) := by
    simpa [s, ell0, N0] using bilinearCommonShiftInterval_subset
      X H L M hL hM hX hHX hr hs u hu m m' hm hm'
  have hnormalized : δ * (N0 : ℝ) ≤
      ρ ^ 2 * s / 100 := by
    have hρsq : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    have hN0Upper : (N0 : ℝ) ≤ 25 * s := by
      simpa [N0] using hN0Data.2
    dsimp [δ]
    calc
      ρ ^ 2 / 2500 * (N0 : ℝ) ≤ ρ ^ 2 / 2500 * (25 * s) := by
        gcongr
      _ = ρ ^ 2 * s / 100 := by ring
  have hsumLarge : δ * (N0 : ℝ) ≤
      ‖∑ n ∈ Finset.Ico
          ((bilinearCommonLower X m m' : ℤ) + 1 - ell0)
          ((bilinearCommonUpper X H m m' : ℤ) + 1 - ell0),
        unitFrequencyPhase (Q.eval (n : ℝ))‖ := by
    calc
      δ * (N0 : ℝ) ≤ ρ ^ 2 * s / 100 := hnormalized
      _ ≤ ‖bilinearC X H L (bilinearCenteredPhase X d ν) m m'‖ := by
        simpa [s] using hlarge
      _ = ‖∑ n ∈ Finset.Ico
          ((bilinearCommonLower X m m' : ℤ) + 1 - ell0)
          ((bilinearCommonUpper X H m m' : ℤ) + 1 - ell0),
        unitFrequencyPhase (Q.eval (n : ℝ))‖ := by
          rw [bilinearC_centered_eq_shifted_Ico X H L M hL hM hX hHX
            m m' ((mem_bilinearWindow M (H / L) u m).mp hm).1
            ((mem_bilinearWindow M (H / L) u m').mp hm').1 ell0 d ν]
  obtain ⟨q, hq, hqBound, hqCoeff⟩ := scalarWeylInverse
    d N0 hd hN0 hδ hδhalf Q hQdeg
      ((bilinearCommonLower X m m' : ℤ) + 1 - ell0)
      ((bilinearCommonUpper X H m m' : ℤ) + 1 - ell0)
      hsubset hsumLarge
  have hδinv : δ⁻¹ = 2500 * (ρ⁻¹) ^ 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hρ]
  have hB :
      (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ =
        bilinearInverseB d ρ⁻¹ := by
    rw [bilinearInverseB_eval, hδinv]
  refine ⟨q, hq, ?_, ?_⟩
  · simpa [hB] using hqBound
  · intro j hj hjd
    have hmPos : 0 < m := by
      have hmRight := (mem_bilinearWindow M (H / L) u m).mp hm |>.1
      have := (mem_bilinearRightSet M m).mp hmRight
      omega
    have hm'Pos : 0 < m' := by
      have hm'Right := (mem_bilinearWindow M (H / L) u m').mp hm' |>.1
      have := (mem_bilinearRightSet M m').mp hm'Right
      omega
    have hcoeff := hqCoeff j hj hjd
    have hQcoeff := bilinearCommonCentre_phase_coefficient
      X ell0 d j ν m m' hmPos hm'Pos
    rw [show Q.coeff j =
        (bilinearGammaPolynomial X ell0 d j ν).eval (m : ℝ) -
          (bilinearGammaPolynomial X ell0 d j ν).eval (m' : ℝ) by
      simpa [Q, bilinearPairShiftPolynomial] using hQcoeff] at hcoeff
    simpa [s, ell0, N0, hB] using hcoeff

/-- The same good-pair denominator in the normalized form used by the first
pigeonhole and polynomial-recurrence step. -/
theorem bilinearGoodPairWeyl_scaled
    (d : ℕ) (hd : 1 ≤ d)
    (X H L M ρ : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (u : ℕ) (hu : u ∈ bilinearWindowCenters M)
    (m m' : ℕ) (hm : m ∈ bilinearWindow M (H / L) u)
    (hm' : m' ∈ bilinearWindow M (H / L) u)
    (ν : ℕ → ℝ)
    (hlarge : ρ ^ 2 * (H / M) / 100 ≤
      ‖bilinearC X H L (bilinearCenteredPhase X d ν) m m'‖) :
    ∃ q : ℕ,
      1 ≤ q ∧
      (q : ℝ) ≤ bilinearInverseB d ρ⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        realDistanceToIntegers
            ((q : ℝ) *
              ((bilinearGammaPolynomial X
                  (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m : ℝ) -
                (bilinearGammaPolynomial X
                  (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m' : ℝ))) ≤
          bilinearInverseB d ρ⁻¹ / (H / M) ^ j := by
  obtain ⟨q, hq, hqB, hqCoeff⟩ := bilinearGoodPairWeyl
    d hd X H L M ρ hL hM hX hHX hr hs hρ hρhalf
      u hu m m' hm hm' ν hlarge
  refine ⟨q, hq, hqB, ?_⟩
  intro j hj hjd
  let N0 : ℕ := bilinearCommonLeftLength (H / M)
  have hN0lower : H / M ≤ (N0 : ℝ) := by
    have hceil : 24 * (H / M) ≤ (N0 : ℝ) := by
      dsimp [N0, bilinearCommonLeftLength]
      exact Nat.le_ceil _
    linarith
  have hspos : 0 < H / M := by linarith
  have hN0pos : 0 < (N0 : ℝ) := lt_of_lt_of_le hspos hN0lower
  have hpow : (H / M) ^ j ≤ (N0 : ℝ) ^ j :=
    pow_le_pow_left₀ hspos.le hN0lower j
  have hρinv : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hBnonneg : 0 ≤ bilinearInverseB d ρ⁻¹ :=
    (bilinearInverseBudget_values d hd ρ⁻¹ hρinv).1 |>.trans' (by norm_num)
  have hraw := hqCoeff j hj hjd
  have hdist : realDistanceToIntegers
            ((q : ℝ) *
              ((bilinearGammaPolynomial X
                  (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m : ℝ) -
                (bilinearGammaPolynomial X
                  (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m' : ℝ))) ≤
      bilinearInverseB d ρ⁻¹ / (N0 : ℝ) ^ j := by
    apply (le_div_iff₀ (pow_pos hN0pos j)).2
    simpa [mul_comm, N0] using hraw
  calc
    realDistanceToIntegers
          ((q : ℝ) *
            ((bilinearGammaPolynomial X
                (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m : ℝ) -
              (bilinearGammaPolynomial X
                (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m' : ℝ))) ≤
        bilinearInverseB d ρ⁻¹ / (N0 : ℝ) ^ j := hdist
    _ ≤ bilinearInverseB d ρ⁻¹ / (H / M) ^ j := by
      exact (div_le_div_iff₀ (pow_pos hN0pos j) (pow_pos hspos j)).2
        (mul_le_mul_of_nonneg_left hpow hBnonneg)

#print axioms bilinearCommonLeftSet_eq_Ioc
#print axioms sum_bilinearCommonLeftSet_shift
#print axioms bilinearCommonShiftInterval_subset
#print axioms bilinearC_centered_eq_shifted_Ico
#print axioms bilinearPairShiftPolynomial_natDegree_le
#print axioms bilinearGoodPairWeyl
#print axioms bilinearGoodPairWeyl_scaled

end

end FractionalPrimes.Literature.Polynomial
