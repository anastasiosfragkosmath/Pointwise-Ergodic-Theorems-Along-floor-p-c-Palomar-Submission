module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import FractionalPrimes.Literature.Hyperbola.GeometricData
public import FractionalPrimes.Literature.Polynomial.PolynomialTypeI2Budgets

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open Set

private theorem intFloorIntervalCard_le (a b : ℝ) (hab : a ≤ b) :
    ((Finset.Ioc (Int.floor a) (Int.floor b)).card : ℝ) ≤ b - a + 1 := by
  rw [Int.card_Ioc]
  have hfloor : Int.floor a ≤ Int.floor b := Int.floor_mono hab
  have hcast :
      ((Int.floor b - Int.floor a).toNat : ℝ) =
        (Int.floor b - Int.floor a : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hfloor)
  rw [hcast]
  have hfa : a < (Int.floor a : ℝ) + 1 := Int.lt_floor_add_one a
  have hfb : (Int.floor b : ℝ) ≤ b := Int.floor_le b
  linarith

private theorem integerProductFiberCard_le
    (X H M : ℝ) (m : ℤ)
    (hM : (1 / 2 : ℝ) ≤ M) (hm : M < (m : ℝ)) (hH : 0 ≤ H) :
    ((Finset.Ioc (Int.floor (X / (m : ℝ)))
      (Int.floor ((X + H) / (m : ℝ)))).card : ℝ) ≤ H / M + 1 := by
  have hMpos : 0 < M := by linarith
  have hmpos : 0 < (m : ℝ) := by linarith
  have hinterval : X / (m : ℝ) ≤ (X + H) / (m : ℝ) := by
    apply div_le_div_of_nonneg_right _ hmpos.le
    linarith
  have hfloor := intFloorIntervalCard_le _ _ hinterval
  have hquot : (X + H) / (m : ℝ) - X / (m : ℝ) = H / (m : ℝ) := by
    field_simp
    ring
  have hdiv : H / (m : ℝ) ≤ H / M := by
    apply (div_le_div_iff₀ hmpos hMpos).2
    nlinarith [mul_le_mul_of_nonneg_left hm.le hH]
  linarith

private theorem smallM_le_H
    (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (hHX : 16 * X ≤ H ^ 3) :
    2 * Real.sqrt (Real.sqrt (H * X)) ≤ H := by
  let s : ℝ := Real.sqrt (Real.sqrt (H * X))
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = Real.sqrt (H * X) := by
    dsimp [s]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = H * X := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (H * X)) ^ 2 := by rw [hs2]
      _ = H * X := Real.sq_sqrt (mul_nonneg hH hX)
  have hHX4 : 16 * H * X ≤ H ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hHX hH
    nlinarith
  have hfourth : (2 * s) ^ 4 ≤ H ^ 4 := by
    rw [show (2 * s) ^ 4 = 16 * s ^ 4 by ring, hs4]
    nlinarith
  have hfourth' : ((2 * s) ^ 2) ^ 2 ≤ (H ^ 2) ^ 2 := by
    nlinarith [hfourth]
  have hsq : (2 * s) ^ 2 ≤ H ^ 2 :=
    (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mp hfourth'
  have hbase : 2 * s ≤ H :=
    (sq_le_sq₀ (by positivity) hH).mp hsq
  simpa [s] using hbase

/-- The finite rectangular overcount for the short-coordinate branch in the
all-scales hyperbola count. Each fixed first coordinate contributes an
integer interval of length at most `H / M + 1`. -/
noncomputable def smallScaleProductPairFinset (X H M : ℝ) :
    Finset (ℤ × ℤ) := by
  classical
  exact (Finset.Ioc (Int.floor M) (Int.floor (2 * M))).biUnion fun m =>
    (Finset.Ioc (Int.floor (X / (m : ℝ)))
      (Int.floor ((X + H) / (m : ℝ)))).image fun n => (m, n)

/-- In the small-`M` branch of `lpi:hyperbola-count`, the lattice count is at
most `6H`. This is the elementary interval-counting part of the approved
proof, isolated from the geometric large-`M` input `lhg:total-count`. -/
theorem smallM_hyperbolaLatticeCount
    (X H M : ℝ) (J : Set ℝ)
    (hX : 1 ≤ X) (hHcube : 16 * X ≤ H ^ 3)
    (hMlower : (1 / 2 : ℝ) ≤ M)
    (hMsmall : M < 2 * Real.sqrt (Real.sqrt (H * X)))
    (hJ : J ⊆ Set.Ioc M (2 * M)) :
    ((Hyperbola.hyperbolaLatticeSet X H J).ncard : ℝ) ≤ 6 * H := by
  classical
  have hHpos : 0 < H := by
    by_contra h
    have hHle : H ≤ 0 := le_of_not_gt h
    have hHcube' : H ^ 3 ≤ 0 := by
      calc
        H ^ 3 = H * H ^ 2 := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hHle (sq_nonneg H)
    linarith [hHcube, hX]
  have hHnonneg : 0 ≤ H := hHpos.le
  have hMpos : 0 < M := by linarith [hMlower]
  have hMleH : M ≤ H := by
    have hsmallBound := smallM_le_H X H (by linarith) hHnonneg hHcube
    linarith
  let mBlock : Finset ℤ := Finset.Ioc (Int.floor M) (Int.floor (2 * M))
  let pairBlock : Finset (ℤ × ℤ) := smallScaleProductPairFinset X H M
  have hsubset : Hyperbola.hyperbolaLatticeSet X H J ⊆ (pairBlock : Set (ℤ × ℤ)) := by
    intro p hp
    rcases hp with ⟨hpJ, hpLower, hpUpper⟩
    have hpInterval := hJ hpJ
    have hmLower : M < (p.1 : ℝ) := hpInterval.1
    have hmUpper : (p.1 : ℝ) ≤ 2 * M := hpInterval.2
    have hmBlock : p.1 ∈ mBlock := by
      simp only [mBlock, Finset.mem_Ioc]
      exact ⟨Int.floor_lt.mpr hmLower, Int.le_floor.mpr hmUpper⟩
    have hmpos : 0 < (p.1 : ℝ) := by linarith [hMlower, hmLower]
    have hnLowerReal : X / (p.1 : ℝ) < (p.2 : ℝ) := by
      apply (div_lt_iff₀ hmpos).2
      simpa [mul_comm] using hpLower
    have hnUpperReal : (p.2 : ℝ) ≤ (X + H) / (p.1 : ℝ) := by
      apply (le_div_iff₀ hmpos).2
      simpa [mul_comm] using hpUpper
    have hnBlock : p.2 ∈ Finset.Ioc (Int.floor (X / (p.1 : ℝ)))
        (Int.floor ((X + H) / (p.1 : ℝ))) := by
      simp only [Finset.mem_Ioc]
      exact ⟨Int.floor_lt.mpr hnLowerReal, Int.le_floor.mpr hnUpperReal⟩
    change p ∈ pairBlock
    simp only [pairBlock, smallScaleProductPairFinset,
      Finset.mem_biUnion, Finset.mem_image]
    exact ⟨p.1, hmBlock, p.2, hnBlock, rfl⟩
  have hpairCard : (pairBlock.card : ℝ) ≤
      ∑ m ∈ mBlock,
        ((Finset.Ioc (Int.floor (X / (m : ℝ)))
          (Int.floor ((X + H) / (m : ℝ)))).card : ℝ) := by
    have hnat :
        ((mBlock.biUnion fun m =>
          (Finset.Ioc (Int.floor (X / (m : ℝ)))
            (Int.floor ((X + H) / (m : ℝ)))).image fun n => (m, n)).card : ℕ) ≤
          ∑ m ∈ mBlock,
            (Finset.Ioc (Int.floor (X / (m : ℝ)))
              (Int.floor ((X + H) / (m : ℝ)))).card := by
      calc
        _ ≤ ∑ m ∈ mBlock,
            ((Finset.Ioc (Int.floor (X / (m : ℝ)))
              (Int.floor ((X + H) / (m : ℝ)))).image fun n => (m, n)).card :=
          Finset.card_biUnion_le
        _ = ∑ m ∈ mBlock,
            (Finset.Ioc (Int.floor (X / (m : ℝ)))
              (Int.floor ((X + H) / (m : ℝ)))).card := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.card_image_iff.mpr]
          intro n₁ hn₁ n₂ hn₂ hEq
          exact congrArg Prod.snd hEq
    exact_mod_cast hnat
  have hsum : ∑ m ∈ mBlock,
      ((Finset.Ioc (Int.floor (X / (m : ℝ)))
        (Int.floor ((X + H) / (m : ℝ)))).card : ℝ) ≤
      ∑ _m ∈ mBlock, (H / M + 1) := by
    apply Finset.sum_le_sum
    intro m hm
    have hmLower : M < (m : ℝ) := by
      exact Int.floor_lt.mp (Finset.mem_Ioc.mp hm).1
    exact integerProductFiberCard_le X H M m hMlower hmLower hHnonneg
  have hmCard : (mBlock.card : ℝ) ≤ M + 1 := by
    calc
      (mBlock.card : ℝ) ≤ 2 * M - M + 1 := by
        simpa [mBlock] using intFloorIntervalCard_le M (2 * M) (by linarith)
      _ = M + 1 := by ring
  have hfactor : 0 ≤ H / M + 1 := by positivity
  have htotal : (pairBlock.card : ℝ) ≤ 6 * H := by
    calc
      (pairBlock.card : ℝ) ≤
          ∑ m ∈ mBlock,
            ((Finset.Ioc (Int.floor (X / (m : ℝ)))
              (Int.floor ((X + H) / (m : ℝ)))).card : ℝ) := hpairCard
      _ ≤ ∑ _m ∈ mBlock, (H / M + 1) := hsum
      _ = (mBlock.card : ℝ) * (H / M + 1) := by simp; ring
      _ ≤ (M + 1) * (H / M + 1) := mul_le_mul_of_nonneg_right hmCard hfactor
      _ ≤ 6 * H := by
        have hdiv : H / M ≤ 2 * H := by
          apply (div_le_iff₀ (by linarith : 0 < M)).2
          nlinarith [mul_le_mul_of_nonneg_left hMlower (show 0 ≤ 2 * H by positivity)]
        have hone : 1 ≤ 2 * H := by nlinarith [hMleH, hMlower]
        have hprod : (M + 1) * (H / M + 1) = H + H / M + M + 1 := by
          field_simp [ne_of_gt hMpos]
          ring
        rw [hprod]
        nlinarith [hMleH, hdiv, hone]
  calc
    ((Hyperbola.hyperbolaLatticeSet X H J).ncard : ℝ) ≤
        ((pairBlock : Set (ℤ × ℤ)).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsubset (Finset.finite_toSet pairBlock)
    _ = (pairBlock.card : ℝ) := by simp
    _ ≤ 6 * H := htotal

/-- Finite moment extraction used in the final type-I2 dyadic argument. The
constants are the literal threshold `κ=δρ/4` and density
`η=δ⁵ρ²/(8 C²)` from the approved proof. -/
theorem manyLargeTypeI2Correlations
    {α : Type*} [DecidableEq α] (s : Finset α) (F : α → ℂ)
    (δ ρ H A C : ℝ)
    (hδ : 0 < δ) (hδle : δ ≤ 1) (hρ : 0 < ρ)
    (hH : 0 < H) (hA : 0 < A) (hC : 0 < C)
    (hcard : (s.card : ℝ) ≤ 2 * A)
    (hmoment : δ * ρ ^ 2 * H ^ 2 / (2 * A) ≤
      ∑ a ∈ s, ‖F a‖ ^ 2)
    (hupper : ∀ a ∈ s, ‖F a‖ ≤ C * δ⁻¹ ^ 2 * H / A) :
    (s.filter fun a => δ * ρ * H / (4 * A) ≤ ‖F a‖).card ≥
      (δ ^ 5 * ρ ^ 2 / (8 * C ^ 2) * A) := by
  classical
  let κ : ℝ := δ * ρ * H / (4 * A)
  let ηA : ℝ := δ ^ 5 * ρ ^ 2 / (8 * C ^ 2) * A
  let upper : ℝ := C * δ⁻¹ ^ 2 * H / A
  let high : Finset α := s.filter fun a => κ ≤ ‖F a‖
  let low : Finset α := s.filter fun a => ¬ κ ≤ ‖F a‖
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hUpperNonneg : 0 ≤ upper := by dsimp [upper]; positivity
  have hκsq : 0 ≤ κ ^ 2 := sq_nonneg κ
  have hUpperSq : 0 ≤ upper ^ 2 := sq_nonneg upper
  have hhighSum : (∑ a ∈ high, ‖F a‖ ^ 2) ≤
      (high.card : ℝ) * upper ^ 2 := by
    calc
      (∑ a ∈ high, ‖F a‖ ^ 2) ≤ ∑ _a ∈ high, upper ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have haS : a ∈ s := (Finset.mem_filter.mp ha).1
        have hnorm := hupper a haS
        have hsq := (sq_le_sq₀ (norm_nonneg (F a)) hUpperNonneg).2 hnorm
        exact hsq
      _ = (high.card : ℝ) * upper ^ 2 := by simp
  have hlowSum : (∑ a ∈ low, ‖F a‖ ^ 2) ≤ (2 * A) * κ ^ 2 := by
    calc
      (∑ a ∈ low, ‖F a‖ ^ 2) ≤ ∑ _a ∈ low, κ ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hnot : ¬ κ ≤ ‖F a‖ := (Finset.mem_filter.mp ha).2
        have hnorm : ‖F a‖ ≤ κ := le_of_lt (lt_of_not_ge hnot)
        exact (sq_le_sq₀ (norm_nonneg (F a)) hκ).2 hnorm
      _ = (low.card : ℝ) * κ ^ 2 := by simp
      _ ≤ (2 * A) * κ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hκsq
        have hlowCard : (low.card : ℝ) ≤ (s.card : ℝ) := by
          exact_mod_cast Finset.card_filter_le s (fun a => ¬ κ ≤ ‖F a‖)
        linarith [hlowCard, hcard]
  have hsplit :
      (∑ a ∈ high, ‖F a‖ ^ 2) + (∑ a ∈ low, ‖F a‖ ^ 2) =
        ∑ a ∈ s, ‖F a‖ ^ 2 := by
    simpa [high, low, κ] using
      (Finset.sum_filter_add_sum_filter_not s (fun a => κ ≤ ‖F a‖)
        (fun a => ‖F a‖ ^ 2))
  have hsumUpper : (∑ a ∈ s, ‖F a‖ ^ 2) ≤
      (high.card : ℝ) * upper ^ 2 + (2 * A) * κ ^ 2 := by
    rw [← hsplit]
    exact add_le_add hhighSum hlowSum
  have hbad : (high.card : ℝ) < ηA → False := by
    intro hsmall
    have hEtaUpper : ηA * upper ^ 2 = δ * ρ ^ 2 * H ^ 2 / (8 * A) := by
      dsimp [ηA, upper]
      field_simp [ne_of_gt hδ, ne_of_gt hA, ne_of_gt hC]
    have hKappa : 2 * A * κ ^ 2 = δ ^ 2 * ρ ^ 2 * H ^ 2 / (8 * A) := by
      dsimp [κ]
      field_simp [ne_of_gt hA]
      ring
    have hdeltaSquare : δ ^ 2 ≤ δ := by nlinarith [hδle]
    have hcommon : 0 ≤ ρ ^ 2 * H ^ 2 / (8 * A) := by positivity
    have hcombined :
        δ * ρ ^ 2 * H ^ 2 / (8 * A) +
            δ ^ 2 * ρ ^ 2 * H ^ 2 / (8 * A) ≤
          δ * ρ ^ 2 * H ^ 2 / (4 * A) := by
      calc
        _ = (δ + δ ^ 2) * (ρ ^ 2 * H ^ 2 / (8 * A)) := by ring
        _ ≤ (2 * δ) * (ρ ^ 2 * H ^ 2 / (8 * A)) :=
          mul_le_mul_of_nonneg_right (by nlinarith [hdeltaSquare]) hcommon
        _ = δ * ρ ^ 2 * H ^ 2 / (4 * A) := by ring
    have hupperContradiction :
        ∑ a ∈ s, ‖F a‖ ^ 2 ≤ δ * ρ ^ 2 * H ^ 2 / (4 * A) := by
      calc
        (∑ a ∈ s, ‖F a‖ ^ 2) ≤
            (high.card : ℝ) * upper ^ 2 + (2 * A) * κ ^ 2 := hsumUpper
        _ ≤ ηA * upper ^ 2 + (2 * A) * κ ^ 2 := by
          exact add_le_add_left
            (mul_le_mul_of_nonneg_right hsmall.le hUpperSq) ((2 * A) * κ ^ 2)
        _ = δ * ρ ^ 2 * H ^ 2 / (8 * A) +
            δ ^ 2 * ρ ^ 2 * H ^ 2 / (8 * A) := by rw [hEtaUpper, hKappa]
        _ ≤ δ * ρ ^ 2 * H ^ 2 / (4 * A) := hcombined
    have hstrict : δ * ρ ^ 2 * H ^ 2 / (4 * A) <
        δ * ρ ^ 2 * H ^ 2 / (2 * A) := by
      have hnum : 0 < δ * ρ ^ 2 * H ^ 2 := by positivity
      have hden : 0 < 2 * A := by positivity
      rw [show 4 * A = 2 * (2 * A) by ring]
      have hdiv :
          δ * ρ ^ 2 * H ^ 2 / (2 * (2 * A)) <
            δ * ρ ^ 2 * H ^ 2 / (2 * A) := by
        apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [hnum, hden]
      exact hdiv
    linarith [hmoment]
  have hhighBound : (ηA : ℝ) ≤ (high.card : ℝ) := by
    by_contra h
    have hsmall : (high.card : ℝ) < ηA := lt_of_not_ge h
    exact hbad hsmall
  have hret := hhighBound
  exact_mod_cast hret

private theorem natPolynomialEval_nonneg (p : Polynomial ℕ) (x : ℝ)
    (hx : 0 ≤ x) : 0 ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add]
      exact add_nonneg hp hq
  | monomial n a =>
      rw [Polynomial.eval₂_monomial]
      exact mul_nonneg (Nat.cast_nonneg a) (pow_nonneg hx n)

private theorem natBivariateEval_nonneg
    (p : InverseBudgetBivariate) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ inverseBoundBivariateEval p x y := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      rw [inverseBoundBivariateEval, MvPolynomial.eval₂_add]
      exact add_nonneg hp hq
  | monomial m a =>
      rw [inverseBoundBivariateEval, MvPolynomial.eval₂_monomial]
      have hvars : ∀ i : Fin 2,
          0 ≤ (if i = 0 then x else y : ℝ) := by
        intro i
        split_ifs <;> assumption
      have hprod : 0 ≤ m.prod (fun i e =>
          (if i = 0 then x else y : ℝ) ^ e) := by
        rw [Finsupp.prod]
        apply Finset.prod_nonneg
        intro i hi
        exact pow_nonneg (hvars i) _
      exact mul_nonneg (Nat.cast_nonneg a) hprod

private theorem typeI2Budget_dominatesV (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    inverseBoundV d (typeI2J d (1024 * x ^ 5)) (typeI2Density x) ≤
      typeI2Bound d x := by
  have hJ : 0 ≤ typeI2J d (1024 * x ^ 5) := by
    exact natPolynomialEval_nonneg _ _ (by positivity)
  have hy : 0 ≤ typeI2Density x := by
    exact natPolynomialEval_nonneg _ _ hx
  have hV : 0 ≤ inverseBoundV d
      (typeI2J d (1024 * x ^ 5)) (typeI2Density x) := by
    exact natBivariateEval_nonneg (inverseBoundVPolynomial d)
      _ _ hJ hy
  have hE : 1 ≤ (inverseBoundEValue d : ℝ) := by
    exact_mod_cast inverseBoundE_ge_one d
  rw [typeI2Bound_eval, ← typeI2Density_eval]
  have hinner : 0 ≤ 16 + typeI2J d (1024 * x ^ 5) +
      inverseBoundV d (typeI2J d (1024 * x ^ 5)) (typeI2Density x) := by
    positivity
  calc
    inverseBoundV d (typeI2J d (1024 * x ^ 5)) (typeI2Density x) ≤
        16 + typeI2J d (1024 * x ^ 5) +
          inverseBoundV d (typeI2J d (1024 * x ^ 5)) (typeI2Density x) := by
            linarith [hJ]
    _ = 1 * (16 + typeI2J d (1024 * x ^ 5) +
          inverseBoundV d (typeI2J d (1024 * x ^ 5)) (typeI2Density x)) := by ring
    _ ≤ (inverseBoundEValue d : ℝ) *
        (16 + typeI2J d (1024 * x ^ 5) +
          inverseBoundV d (typeI2J d (1024 * x ^ 5)) (typeI2Density x)) :=
      mul_le_mul_of_nonneg_right hE hinner

/-- The failed length alternative in the full type-I2 theorem excludes the
short branch of the many-dilate concatenation step. This records the exact
`X^(1/3) A_{I₂}^(2/3) ≥ A_{I₂} ≥ A` scale comparison from the approved proof. -/
theorem typeI2_dilationShortBranch_excluded
    (d : ℕ) (δ X H A0 A : ℝ)
    (hδ : 0 < δ) (hA0 : 0 < A0) (hA : 0 < A)
    (hAblock : A ≤ A0) (hA0X : A0 < X)
    (hlength : typeI2Bound d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) *
      Real.rpow A0 (2 / 3 : ℝ) < H) :
    inverseBoundV d
      (typeI2J d (1024 * (δ⁻¹) ^ 5))
      (typeI2Density (δ⁻¹)) * A < H := by
  have hx : 0 ≤ δ⁻¹ := by positivity
  have hbudget := typeI2Budget_dominatesV d (δ⁻¹) hx
  have hA0leX : A0 ≤ X := hA0X.le
  have hrootMono : Real.rpow A0 (1 / 3 : ℝ) ≤
      Real.rpow X (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hA0.le hA0leX (by norm_num)
  have hA0powNonneg : 0 ≤ Real.rpow A0 (2 / 3 : ℝ) :=
    Real.rpow_nonneg hA0.le _
  have hscale : A0 ≤
      Real.rpow X (1 / 3 : ℝ) * Real.rpow A0 (2 / 3 : ℝ) := by
    calc
      A0 = Real.rpow A0 (1 : ℝ) := (Real.rpow_one A0).symm
      _ = Real.rpow A0 ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by congr 1; norm_num
      _ = Real.rpow A0 (1 / 3 : ℝ) * Real.rpow A0 (2 / 3 : ℝ) :=
        Real.rpow_add hA0 _ _
      _ ≤ Real.rpow X (1 / 3 : ℝ) * Real.rpow A0 (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hrootMono hA0powNonneg
  have hscaleA : A ≤
      Real.rpow X (1 / 3 : ℝ) * Real.rpow A0 (2 / 3 : ℝ) :=
    hAblock.trans hscale
  have hVnonneg : 0 ≤ inverseBoundV d
      (typeI2J d (1024 * (δ⁻¹) ^ 5)) (typeI2Density (δ⁻¹)) := by
    exact natBivariateEval_nonneg (inverseBoundVPolynomial d) _ _
      (natPolynomialEval_nonneg _ _ (by positivity))
      (natPolynomialEval_nonneg _ _ hx)
  calc
    inverseBoundV d (typeI2J d (1024 * (δ⁻¹) ^ 5))
        (typeI2Density (δ⁻¹)) * A ≤ typeI2Bound d (δ⁻¹) * A :=
      mul_le_mul_of_nonneg_right hbudget hA.le
    _ ≤ typeI2Bound d (δ⁻¹) *
        (Real.rpow X (1 / 3 : ℝ) * Real.rpow A0 (2 / 3 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hscaleA (le_trans hVnonneg hbudget)
    _ < H := by simpa [mul_assoc] using hlength

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.smallM_hyperbolaLatticeCount
#print axioms FractionalPrimes.Literature.Polynomial.manyLargeTypeI2Correlations
#print axioms FractionalPrimes.Literature.Polynomial.typeI2_dilationShortBranch_excluded
