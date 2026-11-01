module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearData

/-!
# Removing the scalar bilinear coefficient weights

This file formalizes blueprint item `lbi:unweighted-energy`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

noncomputable section

private theorem intFloorIntervalCard_le_bilinear
    (a b : ℝ) (hab : a ≤ b) :
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

private theorem intClosedIntervalCard_le_bilinear
    (a b : ℝ) (hab : a ≤ b) :
    ((Finset.Icc (Int.ceil a) (Int.floor b)).card : ℝ) ≤ b - a + 1 := by
  classical
  by_cases hbounds : Int.ceil a ≤ Int.floor b
  · have hcardInt :
        ((Finset.Icc (Int.ceil a) (Int.floor b)).card : ℤ) =
          Int.floor b + 1 - Int.ceil a :=
      Int.card_Icc_of_le (a := Int.ceil a) (b := Int.floor b)
        (by omega)
    have hcardReal :
        ((Finset.Icc (Int.ceil a) (Int.floor b)).card : ℝ) =
          (Int.floor b : ℝ) + 1 - (Int.ceil a : ℝ) := by
      exact_mod_cast hcardInt
    rw [hcardReal]
    have hfloor : (Int.floor b : ℝ) ≤ b := Int.floor_le b
    have hceil : a ≤ (Int.ceil a : ℝ) := Int.le_ceil a
    linarith
  · have hempty : Finset.Icc (Int.ceil a) (Int.floor b) = ∅ := by
      exact Finset.Icc_eq_empty hbounds
    rw [hempty]
    simp
    linarith

private theorem bilinearProductIntervalSet_card_le
    (X H : ℝ) (hH : 0 ≤ H) (m : ℕ) (hm : 0 < m) :
    ((bilinearProductIntervalSet X H m).card : ℝ) ≤
      H / (m : ℝ) + 1 := by
  classical
  let T : Finset ℤ := Finset.Ioc (Int.floor (X / (m : ℝ)))
    (Int.floor ((X + H) / (m : ℝ)))
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hquot : X / (m : ℝ) ≤ (X + H) / (m : ℝ) := by
    exact div_le_div_of_nonneg_right (by linarith) hmReal.le
  have hmap : Set.MapsTo (fun l : ℕ => (l : ℤ))
      (bilinearProductIntervalSet X H m : Set ℕ) (T : Set ℤ) := by
    intro l hl
    change l ∈ bilinearProductIntervalSet X H m at hl
    rw [mem_bilinearProductIntervalSet X H m l hm] at hl
    rcases hl with ⟨_, hlower, hupper⟩
    rw [Finset.mem_coe, Finset.mem_Ioc]
    constructor
    · apply (Int.floor_lt).mpr
      apply (div_lt_iff₀ hmReal).2
      norm_num at hlower ⊢
      exact hlower
    · apply (Int.le_floor).mpr
      apply (le_div_iff₀ hmReal).2
      norm_num at hupper ⊢
      exact hupper
  have hinj : (bilinearProductIntervalSet X H m : Set ℕ).InjOn
      (fun l : ℕ => (l : ℤ)) := by
    intro a ha b hb hab
    exact Int.ofNat_inj.mp hab
  have hcardNat : (bilinearProductIntervalSet X H m).card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun l : ℕ => (l : ℤ)) hmap hinj
  have hcardReal :
      ((bilinearProductIntervalSet X H m).card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((bilinearProductIntervalSet X H m).card : ℝ) ≤ (T.card : ℝ) := hcardReal
    _ ≤ (X + H) / (m : ℝ) - X / (m : ℝ) + 1 := by
      exact intFloorIntervalCard_le_bilinear _ _ hquot
    _ = H / (m : ℝ) + 1 := by field_simp; ring

private theorem bilinear_common_left_index_forces_band
    (X H L M : ℝ) (hL : 0 < L) (hr : 1 ≤ H / L)
    (m m' l : ℕ) (hlL : l ∈ bilinearLeftSet L)
    (hlm : l ∈ bilinearProductIntervalSet X H m)
    (hlm' : l ∈ bilinearProductIntervalSet X H m')
    (hm : 0 < m) (hm' : 0 < m') :
    |(m : ℝ) - (m' : ℝ)| < 2 * (H / L) := by
  rw [mem_bilinearLeftSet] at hlL
  rw [mem_bilinearProductIntervalSet X H m l hm] at hlm
  rw [mem_bilinearProductIntervalSet X H m' l hm'] at hlm'
  have hH : 0 < H := by
    have : L ≤ H := by simpa using (le_div_iff₀ hL).mp hr
    linarith
  have hlpos : 0 < (l : ℝ) := by exact_mod_cast hlL.1
  have hdiff :
      |((l * m : ℕ) : ℝ) - ((l * m' : ℕ) : ℝ)| ≤ H := by
    rw [abs_le]
    constructor <;> linarith [hlm.2, hlm'.2]
  have hcastm : (((l * m : ℕ) : ℝ)) = (l : ℝ) * (m : ℝ) := by norm_num
  have hcastm' : (((l * m' : ℕ) : ℝ)) = (l : ℝ) * (m' : ℝ) := by norm_num
  rw [hcastm, hcastm', ← mul_sub, abs_mul, abs_of_nonneg hlpos.le] at hdiff
  have hcoeff : 0 < 2 * (H / L) := by positivity
  have hid : H = (2 * (H / L)) * (L / 2) := by
    field_simp [hL.ne']
    <;> ring
  have hstrict : H < (2 * (H / L)) * (l : ℝ) := by
    calc
      H = (2 * (H / L)) * (L / 2) := hid
      _ < (2 * (H / L)) * (l : ℝ) :=
        mul_lt_mul_of_pos_left hlL.2.1 hcoeff
  have hmul :
      |(m : ℝ) - (m' : ℝ)| * (l : ℝ) <
        (2 * (H / L)) * (l : ℝ) := by
    calc
      |(m : ℝ) - (m' : ℝ)| * (l : ℝ) =
          (l : ℝ) * |(m : ℝ) - (m' : ℝ)| := by ring
      _ ≤ H := hdiff
      _ < (2 * (H / L)) * (l : ℝ) := hstrict
  exact lt_of_mul_lt_mul_right hmul hlpos.le

/-- The unweighted correlation vanishes outside the exact source band
`|m-m'| ≤ 2r`. -/
theorem bilinearC_eq_zero_of_band_lt
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hr : 1 ≤ H / L) (P : Polynomial ℝ)
    (m m' : ℕ) (hm : m ∈ bilinearRightSet M)
    (hm' : m' ∈ bilinearRightSet M)
    (hband : 2 * (H / L) < |(m : ℝ) - (m' : ℝ)|) :
    bilinearC X H L P m m' = 0 := by
  classical
  unfold bilinearC
  apply Finset.sum_eq_zero
  intro l hl
  rcases Finset.mem_filter.mp hl with
    ⟨hlL, hlmLower, hlmUpper, hlm'Lower, hlm'Upper⟩
  have hmNat : 0 < m := by
    rw [mem_bilinearRightSet] at hm
    omega
  have hmNat' : 0 < m' := by
    rw [mem_bilinearRightSet] at hm'
    omega
  have hlmMem : l ∈ bilinearProductIntervalSet X H m := by
    rw [mem_bilinearProductIntervalSet X H m l hmNat]
    exact ⟨(mem_bilinearLeftSet L l).mp hlL |>.1, hlmLower, hlmUpper⟩
  have hlmMem' : l ∈ bilinearProductIntervalSet X H m' := by
    rw [mem_bilinearProductIntervalSet X H m' l hmNat']
    exact ⟨(mem_bilinearLeftSet L l).mp hlL |>.1, hlm'Lower, hlm'Upper⟩
  have := bilinear_common_left_index_forces_band X H L M hL hr
    m m' l hlL hlmMem hlmMem' hmNat hmNat'
  exact False.elim (not_lt_of_ge hband.le this)

/-- Every unweighted correlation has the literal pointwise source bound
`|C_{m,m'}| ≤ 2s`. -/
theorem norm_bilinearC_le
    (X H L M : ℝ) (hM : 0 < M) (hH : 0 ≤ H)
    (hs : 1 ≤ H / M) (P : Polynomial ℝ)
    (m m' : ℕ) (hm : m ∈ bilinearRightSet M) :
    ‖bilinearC X H L P m m'‖ ≤ 2 * (H / M) := by
  classical
  have hmData := (mem_bilinearRightSet M m).mp hm
  have hmNat : 0 < m := by omega
  let F : Finset ℕ := (bilinearLeftSet L).filter (fun l =>
      X < ((l * m : ℕ) : ℝ) ∧ ((l * m : ℕ) : ℝ) ≤ X + H ∧
      X < ((l * m' : ℕ) : ℝ) ∧ ((l * m' : ℕ) : ℝ) ≤ X + H)
  have hFsub : F ⊆ bilinearProductIntervalSet X H m := by
    intro l hl
    rcases Finset.mem_filter.mp hl with
      ⟨hlL, hlmLower, hlmUpper, _, _⟩
    rw [mem_bilinearProductIntervalSet X H m l hmNat]
    exact ⟨(mem_bilinearLeftSet L l).mp hlL |>.1, hlmLower, hlmUpper⟩
  have hcardNat : F.card ≤ (bilinearProductIntervalSet X H m).card :=
    Finset.card_le_card hFsub
  have hcard : (F.card : ℝ) ≤ 2 * (H / M) := by
    calc
      (F.card : ℝ) ≤ ((bilinearProductIntervalSet X H m).card : ℝ) := by
        exact_mod_cast hcardNat
      _ ≤ H / (m : ℝ) + 1 :=
        bilinearProductIntervalSet_card_le X H hH m hmNat
      _ ≤ H / M + 1 := by
        have hmReal : 0 < (m : ℝ) := by exact_mod_cast hmNat
        have hdiv : H / (m : ℝ) ≤ H / M := by
          exact (div_le_div_iff₀ hmReal hM).2
            (mul_le_mul_of_nonneg_left hmData.2.1.le hH)
        linarith
      _ ≤ 2 * (H / M) := by linarith
  calc
    ‖bilinearC X H L P m m'‖ =
        ‖∑ l ∈ F, unitFrequencyPhase
          (P.eval ((l * m : ℕ) : ℝ) - P.eval ((l * m' : ℕ) : ℝ))‖ := by
      rfl
    _ ≤ ∑ l ∈ F, ‖unitFrequencyPhase
          (P.eval ((l * m : ℕ) : ℝ) - P.eval ((l * m' : ℕ) : ℝ))‖ :=
      norm_sum_le _ _
    _ = (F.card : ℝ) := by simp [norm_unitFrequencyPhase]
    _ ≤ 2 * (H / M) := hcard

/-- The `m`-summand after the weighted bilinear sum is regrouped by its left
index. -/
def bilinearInnerTerm (X H : ℝ) (β : ℕ → ℂ) (P : Polynomial ℝ)
    (l m : ℕ) : ℂ :=
  if l ∈ bilinearProductIntervalSet X H m then
    β m * unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ))
  else 0

/-- The inner weighted phase sum at a fixed left index. -/
def bilinearInnerSum (X H M : ℝ) (β : ℕ → ℂ)
    (P : Polynomial ℝ) (l : ℕ) : ℂ :=
  ∑ m ∈ bilinearRightSet M, bilinearInnerTerm X H β P l m

private theorem bilinearProductIntervalSet_eq_left_filter
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (m : ℕ) (hm : m ∈ bilinearRightSet M) :
    bilinearProductIntervalSet X H m =
      (bilinearLeftSet L).filter
        (fun l => l ∈ bilinearProductIntervalSet X H m) := by
  classical
  ext l
  simp only [Finset.mem_filter]
  constructor
  · intro hl
    exact ⟨bilinearProductIntervalSet_subset_left X H L M hL hM hX hHX
      m l hm hl, hl⟩
  · exact fun hl => hl.2

/-- Regroup the source correlation `S` by the exact left index set. -/
theorem bilinearS_eq_left_inner_sum
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (α β : ℕ → ℂ) (P : Polynomial ℝ) :
    bilinearS X H M α β P =
      ∑ l ∈ bilinearLeftSet L,
        α l * bilinearInnerSum X H M β P l := by
  classical
  unfold bilinearS bilinearInnerSum bilinearInnerTerm
  calc
    (∑ m ∈ bilinearRightSet M,
        ∑ l ∈ bilinearProductIntervalSet X H m,
          α l * β m * unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ))) =
      ∑ m ∈ bilinearRightSet M, ∑ l ∈ bilinearLeftSet L,
        if l ∈ bilinearProductIntervalSet X H m then
          α l * β m * unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ))
        else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      conv_lhs =>
        rw [bilinearProductIntervalSet_eq_left_filter X H L M
          hL hM hX hHX m hm, Finset.sum_filter]
    _ = ∑ l ∈ bilinearLeftSet L, ∑ m ∈ bilinearRightSet M,
        if l ∈ bilinearProductIntervalSet X H m then
          α l * β m * unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ))
        else 0 := by rw [Finset.sum_comm]
    _ = ∑ l ∈ bilinearLeftSet L,
        α l * ∑ m ∈ bilinearRightSet M,
          if l ∈ bilinearProductIntervalSet X H m then
            β m * unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ))
          else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmem : l ∈ bilinearProductIntervalSet X H m
      · simp [hmem, mul_assoc]
      · simp [hmem]

private theorem bilinearCommonLeftSet_eq_product_filter
    (X H L : ℝ) (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') :
    bilinearCommonLeftSet X H L m m' =
      (bilinearLeftSet L).filter (fun l =>
        l ∈ bilinearProductIntervalSet X H m ∧
          l ∈ bilinearProductIntervalSet X H m') := by
  classical
  ext l
  simp only [bilinearCommonLeftSet, Finset.mem_filter]
  constructor
  · rintro ⟨hlL, hlower, hlupper, hlower', hlupper'⟩
    have hlone := (mem_bilinearLeftSet L l).mp hlL |>.1
    exact ⟨hlL,
      (mem_bilinearProductIntervalSet X H m l hm).mpr
        ⟨hlone, hlower, hlupper⟩,
      (mem_bilinearProductIntervalSet X H m' l hm').mpr
        ⟨hlone, hlower', hlupper'⟩⟩
  · rintro ⟨hlL, hlm, hlm'⟩
    have hmData := (mem_bilinearProductIntervalSet X H m l hm).mp hlm
    have hmData' := (mem_bilinearProductIntervalSet X H m' l hm').mp hlm'
    exact ⟨hlL, hmData.2.1, hmData.2.2, hmData'.2.1, hmData'.2.2⟩

private theorem bilinearC_eq_indicator_sum
    (X H L : ℝ) (P : Polynomial ℝ) (m m' : ℕ)
    (hm : 0 < m) (hm' : 0 < m') :
    bilinearC X H L P m m' =
      ∑ l ∈ bilinearLeftSet L,
        if l ∈ bilinearProductIntervalSet X H m ∧
            l ∈ bilinearProductIntervalSet X H m' then
          unitFrequencyPhase
            (P.eval ((l * m : ℕ) : ℝ) - P.eval ((l * m' : ℕ) : ℝ))
        else 0 := by
  unfold bilinearC
  rw [bilinearCommonLeftSet_eq_product_filter X H L m m' hm hm',
    Finset.sum_filter]

private theorem norm_sq_finset_sum_eq_re_pair
    {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖ ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, (f i * star (f j)).re := by
  classical
  calc
    ‖∑ i ∈ S, f i‖ ^ 2 = Complex.normSq (∑ i ∈ S, f i) :=
      (Complex.normSq_eq_norm_sq _).symm
    _ = (star (∑ i ∈ S, f i) * ∑ i ∈ S, f i).re := by
      have h := congrArg Complex.re
        (Complex.normSq_eq_conj_mul_self (z := ∑ i ∈ S, f i))
      simpa using h
    _ = ((∑ i ∈ S, f i) * star (∑ i ∈ S, f i)).re := by
      rw [mul_comm]
    _ = ∑ i ∈ S, ∑ j ∈ S, (f i * star (f j)).re := by
      rw [star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum, Complex.re_sum]

private theorem unitFrequencyPhase_mul_star (a b : ℝ) :
    unitFrequencyPhase a * star (unitFrequencyPhase b) =
      unitFrequencyPhase (a - b) := by
  calc
    unitFrequencyPhase a * star (unitFrequencyPhase b) =
        unitFrequencyPhase a * unitFrequencyPhase (-b) := by
      congr 1
      simpa using (unitFrequencyPhase_neg_eq_conj b).symm
    _ = unitFrequencyPhase (a + (-b)) := by rw [← unitFrequencyPhase_add]
    _ = unitFrequencyPhase (a - b) := by congr 1 <;> ring

private theorem bilinearInnerTerm_pair_sum
    (X H L M : ℝ) (β : ℕ → ℂ) (P : Polynomial ℝ)
    (m m' : ℕ) (hm : m ∈ bilinearRightSet M)
    (hm' : m' ∈ bilinearRightSet M) :
    (∑ l ∈ bilinearLeftSet L,
        (bilinearInnerTerm X H β P l m *
          star (bilinearInnerTerm X H β P l m')).re) =
      (β m * star (β m') * bilinearC X H L P m m').re := by
  classical
  have hmNat : 0 < m := by
    have := (mem_bilinearRightSet M m).mp hm
    omega
  have hmNat' : 0 < m' := by
    have := (mem_bilinearRightSet M m').mp hm'
    omega
  rw [bilinearC_eq_indicator_sum X H L P m m' hmNat hmNat',
    Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlm : l ∈ bilinearProductIntervalSet X H m
  · by_cases hlm' : l ∈ bilinearProductIntervalSet X H m'
    · simp only [bilinearInnerTerm, hlm, hlm', and_self, if_pos]
      congr 1
      rw [star_mul]
      calc
        β m * unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ)) *
              (star (unitFrequencyPhase (P.eval ((l * m' : ℕ) : ℝ))) *
                star (β m')) =
            β m * star (β m') *
              (unitFrequencyPhase (P.eval ((l * m : ℕ) : ℝ)) *
                star (unitFrequencyPhase (P.eval ((l * m' : ℕ) : ℝ)))) := by ring
        _ = β m * star (β m') *
              unitFrequencyPhase
                (P.eval ((l * m : ℕ) : ℝ) - P.eval ((l * m' : ℕ) : ℝ)) := by
          rw [unitFrequencyPhase_mul_star]
    · simp [bilinearInnerTerm, hlm, hlm']
  · simp [bilinearInnerTerm, hlm]

private theorem bilinearInnerEnergy_eq_re_weightedC
    (X H L M : ℝ) (β : ℕ → ℂ) (P : Polynomial ℝ) :
    (∑ l ∈ bilinearLeftSet L,
        ‖bilinearInnerSum X H M β P l‖ ^ 2) =
      (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        β m * star (β m') * bilinearC X H L P m m').re := by
  classical
  calc
    (∑ l ∈ bilinearLeftSet L,
        ‖bilinearInnerSum X H M β P l‖ ^ 2) =
      ∑ l ∈ bilinearLeftSet L,
        ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
          (bilinearInnerTerm X H β P l m *
            star (bilinearInnerTerm X H β P l m')).re := by
      apply Finset.sum_congr rfl
      intro l hl
      exact norm_sq_finset_sum_eq_re_pair (bilinearRightSet M)
        (bilinearInnerTerm X H β P l)
    _ = ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ∑ l ∈ bilinearLeftSet L,
          (bilinearInnerTerm X H β P l m *
            star (bilinearInnerTerm X H β P l m')).re := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        (β m * star (β m') * bilinearC X H L P m m').re := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro m' hm'
      exact bilinearInnerTerm_pair_sum X H L M β P m m' hm hm'
    _ = (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        β m * star (β m') * bilinearC X H L P m m').re := by
      simp_rw [Complex.re_sum]

private theorem bilinearInnerEnergy_le_weightedC
    (X H L M : ℝ) (β : ℕ → ℂ) (P : Polynomial ℝ) :
    (∑ l ∈ bilinearLeftSet L,
        ‖bilinearInnerSum X H M β P l‖ ^ 2) ≤
      ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖ := by
  let Z : ℂ := ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
    β m * star (β m') * bilinearC X H L P m m'
  calc
    (∑ l ∈ bilinearLeftSet L,
        ‖bilinearInnerSum X H M β P l‖ ^ 2) = Z.re := by
      exact bilinearInnerEnergy_eq_re_weightedC X H L M β P
    _ ≤ ‖Z‖ := Complex.re_le_norm Z
    _ ≤ ∑ m ∈ bilinearRightSet M,
        ‖∑ m' ∈ bilinearRightSet M,
          β m * star (β m') * bilinearC X H L P m m'‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ‖β m * star (β m') * bilinearC X H L P m m'‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_sum_le _ _
    _ = ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖ := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro m' hm'
      simp [norm_mul]

private theorem bilinear_neighbor_card_le
    (M r : ℝ) (hr : 1 ≤ r) (m : ℕ) :
    (((bilinearRightSet M).filter (fun m' : ℕ =>
      |(m : ℝ) - (m' : ℝ)| ≤ 2 * r)).card : ℝ) ≤ 5 * r := by
  classical
  let N := (bilinearRightSet M).filter (fun m' : ℕ =>
    |(m : ℝ) - (m' : ℝ)| ≤ 2 * r)
  let T : Finset ℤ := Finset.Icc
    (Int.ceil ((m : ℝ) - 2 * r)) (Int.floor ((m : ℝ) + 2 * r))
  have hr0 : 0 ≤ r := by linarith
  have hmap : Set.MapsTo (fun n : ℕ => (n : ℤ)) (N : Set ℕ) (T : Set ℤ) := by
    intro n hn
    have hband := (Finset.mem_filter.mp hn).2
    have habs := abs_le.mp hband
    rw [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · apply (Int.ceil_le).mpr
      norm_num
      linarith
    · apply (Int.le_floor).mpr
      norm_num
      linarith
  have hinj : (N : Set ℕ).InjOn (fun n : ℕ => (n : ℤ)) := by
    intro a ha b hb hab
    exact Int.ofNat_inj.mp hab
  have hcardNat : N.card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℤ)) hmap hinj
  have hcardReal : (N.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcardNat
  calc
    (N.card : ℝ) ≤ (T.card : ℝ) := hcardReal
    _ ≤ ((m : ℝ) + 2 * r) - ((m : ℝ) - 2 * r) + 1 :=
      intClosedIntervalCard_le_bilinear _ _ (by linarith)
    _ = 4 * r + 1 := by ring
    _ ≤ 5 * r := by linarith

private theorem finite_symmetric_band_weight_bound
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (R : ι → ι → Prop) [DecidableRel R]
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, R i j ↔ R j i)
    (D : ℝ) (hcard : ∀ i ∈ S,
      (((S.filter fun j => R i j).card : ℕ) : ℝ) ≤ D) :
    (∑ i ∈ S, ∑ j ∈ S, if R i j then w i * w j else 0) ≤
      D * ∑ i ∈ S, w i ^ 2 := by
  classical
  have hpair :
      (∑ i ∈ S, ∑ j ∈ S, if R i j then w i * w j else 0) ≤
        (1 / 2 : ℝ) *
          ((∑ i ∈ S, ∑ j ∈ S, if R i j then w i ^ 2 else 0) +
            (∑ i ∈ S, ∑ j ∈ S, if R i j then w j ^ 2 else 0)) := by
    calc
      (∑ i ∈ S, ∑ j ∈ S, if R i j then w i * w j else 0) ≤
          ∑ i ∈ S, ∑ j ∈ S,
            if R i j then (w i ^ 2 + w j ^ 2) / 2 else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : R i j
        · simp only [hij, if_true]
          nlinarith [sq_nonneg (w i - w j)]
        · simp [hij]
      _ = _ := by
        calc
          (∑ i ∈ S, ∑ j ∈ S,
              if R i j then (w i ^ 2 + w j ^ 2) / 2 else 0) =
              ∑ i ∈ S, ∑ j ∈ S,
                ((1 / 2 : ℝ) * (if R i j then w i ^ 2 else 0) +
                  (1 / 2 : ℝ) * (if R i j then w j ^ 2 else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hij : R i j <;> simp [hij] <;> ring
          _ = _ := by
            simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            ring
  have hswap :
      (∑ i ∈ S, ∑ j ∈ S, if R i j then w j ^ 2 else 0) =
        ∑ i ∈ S, ∑ j ∈ S, if R i j then w i ^ 2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : R i j
    · have hji : R j i := (hsymm i hi j hj).mp hij
      simp [hij, hji]
    · have hji : ¬ R j i := by
        intro h
        exact hij ((hsymm i hi j hj).mpr h)
      simp [hij, hji]
  have hfirst :
      (∑ i ∈ S, ∑ j ∈ S, if R i j then w i ^ 2 else 0) ≤
        D * ∑ i ∈ S, w i ^ 2 := by
    calc
      (∑ i ∈ S, ∑ j ∈ S, if R i j then w i ^ 2 else 0) =
          ∑ i ∈ S, (((S.filter fun j => R i j).card : ℕ) : ℝ) * w i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_filter]
        simp [mul_comm]
      _ ≤ ∑ i ∈ S, D * w i ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hcard i hi) (sq_nonneg _)
      _ = D * ∑ i ∈ S, w i ^ 2 := by rw [Finset.mul_sum]
  calc
    (∑ i ∈ S, ∑ j ∈ S, if R i j then w i * w j else 0) ≤
        (1 / 2 : ℝ) *
          ((∑ i ∈ S, ∑ j ∈ S, if R i j then w i ^ 2 else 0) +
            (∑ i ∈ S, ∑ j ∈ S, if R i j then w j ^ 2 else 0)) := hpair
    _ = ∑ i ∈ S, ∑ j ∈ S, if R i j then w i ^ 2 else 0 := by
      rw [hswap]
      ring
    _ ≤ D * ∑ i ∈ S, w i ^ 2 := hfirst

private theorem bilinear_alpha_square_sum
    (L : ℝ) (hL : 0 < L) (α : ℕ → ℂ) :
    (∑ l ∈ bilinearLeftSet L, ‖α l‖ ^ 2) =
      L * bilinearU L α ^ 2 := by
  rw [bilinearU_sq L hL α]
  unfold bilinearU2
  field_simp [hL.ne']

private theorem bilinear_beta_fourth_sum
    (M : ℝ) (hM : 0 < M) (β : ℕ → ℂ) :
    (∑ m ∈ bilinearRightSet M, ‖β m‖ ^ 4) =
      M * bilinearV M β ^ 4 := by
  rw [bilinearV_pow_four M hM β]
  unfold bilinearV4
  field_simp [hM.ne']

private theorem bilinear_weightedC_eq_band
    (X H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hr : 1 ≤ H / L) (β : ℕ → ℂ) (P : Polynomial ℝ) :
    (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖) =
      ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
          ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖
        else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro m' hm'
  by_cases hband : |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L)
  · simp [hband]
  · have hstrict : 2 * (H / L) < |(m : ℝ) - (m' : ℝ)| :=
      lt_of_not_ge hband
    have hzero := bilinearC_eq_zero_of_band_lt X H L M hL hM hr P
      m m' hm hm' hstrict
    simp [hband, hzero]

private theorem bilinear_band_beta_square_le
    (H L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hr : 1 ≤ H / L) (β : ℕ → ℂ) :
    (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
          ‖β m‖ ^ 2 * ‖β m'‖ ^ 2
        else 0) ≤
      5 * (H / L) * (M * bilinearV M β ^ 4) := by
  classical
  let R : ℕ → ℕ → Prop := fun m m' =>
    |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L)
  have hbound := finite_symmetric_band_weight_bound
    (bilinearRightSet M) (fun m => ‖β m‖ ^ 2) R
    (by intro m hm; positivity)
    (by
      intro m hm m' hm'
      change |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) ↔
        |(m' : ℝ) - (m : ℝ)| ≤ 2 * (H / L)
      rw [abs_sub_comm])
    (5 * (H / L))
    (by
      intro m hm
      exact bilinear_neighbor_card_le M (H / L) hr m)
  change (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
      if R m m' then ‖β m‖ ^ 2 * ‖β m'‖ ^ 2 else 0) ≤ _
  calc
    (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        if R m m' then ‖β m‖ ^ 2 * ‖β m'‖ ^ 2 else 0) ≤
        5 * (H / L) *
          ∑ m ∈ bilinearRightSet M, (‖β m‖ ^ 2) ^ 2 := hbound
    _ = 5 * (H / L) * (M * bilinearV M β ^ 4) := by
      rw [show (∑ m ∈ bilinearRightSet M, (‖β m‖ ^ 2) ^ 2) =
          ∑ m ∈ bilinearRightSet M, ‖β m‖ ^ 4 by
        apply Finset.sum_congr rfl
        intro m hm
        ring,
        bilinear_beta_fourth_sum M hM β]

private theorem bilinear_band_weightedC_sq_le
    (X H L M : ℝ) (β : ℕ → ℂ) (P : Polynomial ℝ) :
    (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
          ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖
        else 0) ^ 2 ≤
      (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
          ‖β m‖ ^ 2 * ‖β m'‖ ^ 2
        else 0) *
      (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ‖bilinearC X H L P m m'‖ ^ 2) := by
  classical
  let S := bilinearRightSet M
  let f : ℕ × ℕ → ℝ := fun p =>
    if |(p.1 : ℝ) - (p.2 : ℝ)| ≤ 2 * (H / L) then
      ‖β p.1‖ * ‖β p.2‖
    else 0
  let g : ℕ × ℕ → ℝ := fun p => ‖bilinearC X H L P p.1 p.2‖
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (S.product S) f g
  have hf : (∑ p ∈ S.product S, f p ^ 2) =
      ∑ m ∈ S, ∑ m' ∈ S,
        if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
          ‖β m‖ ^ 2 * ‖β m'‖ ^ 2
        else 0 := by
    calc
      (∑ p ∈ S.product S, f p ^ 2) =
          ∑ m ∈ S, ∑ m' ∈ S, f (m, m') ^ 2 :=
        Finset.sum_product' S S (fun m m' => f (m, m') ^ 2)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro m' hm'
        by_cases hband : |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) <;>
          simp [f, hband, mul_pow]
  have hg : (∑ p ∈ S.product S, g p ^ 2) =
      ∑ m ∈ S, ∑ m' ∈ S,
        ‖bilinearC X H L P m m'‖ ^ 2 := by
    calc
      (∑ p ∈ S.product S, g p ^ 2) =
          ∑ m ∈ S, ∑ m' ∈ S, g (m, m') ^ 2 :=
        Finset.sum_product' S S (fun m m' => g (m, m') ^ 2)
      _ = _ := by simp [g]
  change (∑ m ∈ S, ∑ m' ∈ S,
      if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
        ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖
      else 0) ^ 2 ≤ _
  calc
    (∑ m ∈ S, ∑ m' ∈ S,
        if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
          ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖
        else 0) ^ 2 =
        (∑ p ∈ S.product S, f p * g p) ^ 2 := by
      congr 1
      calc
        (∑ m ∈ S, ∑ m' ∈ S,
            if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
              ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖
            else 0) =
            ∑ m ∈ S, ∑ m' ∈ S, f (m, m') * g (m, m') := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro m' hm'
          by_cases hband : |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) <;>
            simp [f, g, hband]
        _ = ∑ p ∈ S.product S, f p * g p :=
          (Finset.sum_product' S S (fun m m' => f (m, m') * g (m, m'))).symm
    _ ≤ (∑ p ∈ S.product S, f p ^ 2) *
        ∑ p ∈ S.product S, g p ^ 2 := hcs
    _ = (∑ m ∈ S, ∑ m' ∈ S,
          if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
            ‖β m‖ ^ 2 * ‖β m'‖ ^ 2
          else 0) *
        (∑ m ∈ S, ∑ m' ∈ S,
          ‖bilinearC X H L P m m'‖ ^ 2) := by
      rw [hf, hg]

private theorem bilinear_large_implies_weightedC_lower
    (X H L M ρ : ℝ)
    (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L)
    (hρ : 0 < ρ)
    (α β : ℕ → ℂ) (P : Polynomial ℝ)
    (hUV : 0 < bilinearU L α * bilinearV M β)
    (hlarge : ρ * H * (bilinearU L α * bilinearV M β) ≤
      ‖bilinearS X H M α β P‖) :
    ρ ^ 2 * H ^ 2 * bilinearV M β ^ 2 ≤
      L * (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖) := by
  let U := bilinearU L α
  let V := bilinearV M β
  let E := ∑ l ∈ bilinearLeftSet L,
    ‖bilinearInnerSum X H M β P l‖ ^ 2
  let W := ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
    ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖
  have hHL : L ≤ H := by
    have h := (le_div_iff₀ hL).mp hr
    simpa using h
  have hH : 0 < H := lt_of_lt_of_le hL hHL
  have hU0 : 0 ≤ U := bilinearU_nonneg L α
  have hV0 : 0 ≤ V := bilinearV_nonneg M β
  have hUpos : 0 < U := pos_of_mul_pos_left hUV hV0
  have hweighted : ρ * H * (U * V) ≤
      ∑ l ∈ bilinearLeftSet L,
        ‖α l‖ * ‖bilinearInnerSum X H M β P l‖ := by
    calc
      ρ * H * (U * V) ≤ ‖bilinearS X H M α β P‖ := hlarge
      _ = ‖∑ l ∈ bilinearLeftSet L,
          α l * bilinearInnerSum X H M β P l‖ := by
        rw [bilinearS_eq_left_inner_sum X H L M hL hM hX hHX α β P]
      _ ≤ ∑ l ∈ bilinearLeftSet L,
          ‖α l * bilinearInnerSum X H M β P l‖ := norm_sum_le _ _
      _ = ∑ l ∈ bilinearLeftSet L,
          ‖α l‖ * ‖bilinearInnerSum X H M β P l‖ := by
        apply Finset.sum_congr rfl
        intro l hl
        exact norm_mul _ _
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq (bilinearLeftSet L)
    (fun l => ‖α l‖) (fun l => ‖bilinearInnerSum X H M β P l‖)
  have hweightedNonneg : 0 ≤ ∑ l ∈ bilinearLeftSet L,
      ‖α l‖ * ‖bilinearInnerSum X H M β P l‖ := by positivity
  have hleftNonneg : 0 ≤ ρ * H * (U * V) := by positivity
  have hsq : (ρ * H * (U * V)) ^ 2 ≤
      (∑ l ∈ bilinearLeftSet L, ‖α l‖ ^ 2) * E := by
    calc
      (ρ * H * (U * V)) ^ 2 ≤
          (∑ l ∈ bilinearLeftSet L,
            ‖α l‖ * ‖bilinearInnerSum X H M β P l‖) ^ 2 :=
        (sq_le_sq₀ hleftNonneg hweightedNonneg).2 hweighted
      _ ≤ (∑ l ∈ bilinearLeftSet L, ‖α l‖ ^ 2) * E := hCauchy
  have hEW : E ≤ W := bilinearInnerEnergy_le_weightedC X H L M β P
  have hsq' : (ρ * H * (U * V)) ^ 2 ≤ (L * U ^ 2) * W := by
    calc
      (ρ * H * (U * V)) ^ 2 ≤
          (∑ l ∈ bilinearLeftSet L, ‖α l‖ ^ 2) * E := hsq
      _ ≤ (∑ l ∈ bilinearLeftSet L, ‖α l‖ ^ 2) * W := by
        exact mul_le_mul_of_nonneg_left hEW (by positivity)
      _ = (L * U ^ 2) * W := by
        rw [bilinear_alpha_square_sum L hL α]
  have hfactor : U ^ 2 * (ρ ^ 2 * H ^ 2 * V ^ 2) ≤
      U ^ 2 * (L * W) := by
    calc
      U ^ 2 * (ρ ^ 2 * H ^ 2 * V ^ 2) =
          (ρ * H * (U * V)) ^ 2 := by ring
      _ ≤ (L * U ^ 2) * W := hsq'
      _ = U ^ 2 * (L * W) := by ring
  have hfactor' : (ρ ^ 2 * H ^ 2 * V ^ 2) * U ^ 2 ≤
      (L * W) * U ^ 2 := by
    simpa [mul_comm] using hfactor
  have hcancel : ρ ^ 2 * H ^ 2 * V ^ 2 ≤ L * W :=
    (mul_le_mul_iff_left₀ (sq_pos_of_pos hUpos)).mp hfactor'
  simpa [V, W] using hcancel

/-- Two finite Cauchy--Schwarz inequalities remove the coefficient weights
from a large scalar bilinear correlation, with the exact source constant. -/
theorem bilinearUnweightedEnergy
    (X H L M ρ : ℝ)
    (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (hρ : 0 < ρ)
    (α β : ℕ → ℂ) (P : Polynomial ℝ)
    (hUV : 0 < bilinearU L α * bilinearV M β)
    (hlarge : ρ * H * (bilinearU L α * bilinearV M β) ≤
      ‖bilinearS X H M α β P‖) :
    (∀ m ∈ bilinearRightSet M, ∀ m' ∈ bilinearRightSet M,
        2 * (H / L) < |(m : ℝ) - (m' : ℝ)| →
          bilinearC X H L P m m' = 0) ∧
    (∀ m ∈ bilinearRightSet M, ∀ m' ∈ bilinearRightSet M,
        ‖bilinearC X H L P m m'‖ ≤ 2 * (H / M)) ∧
    ρ ^ 4 / 5 * M * (H / L) * (H / M) ^ 2 ≤
      ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ‖bilinearC X H L P m m'‖ ^ 2 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro m hm m' hm' hband
    exact bilinearC_eq_zero_of_band_lt X H L M hL hM hr P
      m m' hm hm' hband
  · intro m hm m' hm'
    have hH : 0 ≤ H := by
      have hHM : M ≤ H := by
        have h := (le_div_iff₀ hM).mp hs
        simpa using h
      linarith
    exact norm_bilinearC_le X H L M hM hH hs P m m' hm
  · let V := bilinearV M β
    let W := ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
      ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖
    let A := ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
      if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
        ‖β m‖ ^ 2 * ‖β m'‖ ^ 2
      else 0
    let E := ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
      ‖bilinearC X H L P m m'‖ ^ 2
    have hU0 := bilinearU_nonneg L α
    have hV0 : 0 ≤ V := bilinearV_nonneg M β
    have hVpos : 0 < V := pos_of_mul_pos_right hUV hU0
    have hW0 : 0 ≤ W := by positivity
    have hE0 : 0 ≤ E := by positivity
    have hlower : ρ ^ 2 * H ^ 2 * V ^ 2 ≤ L * W := by
      simpa [V, W] using bilinear_large_implies_weightedC_lower
        X H L M ρ hL hM hX hHX hr hρ α β P hUV hlarge
    have hWsq : W ^ 2 ≤ A * E := by
      calc
        W ^ 2 =
            (∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
              if |(m : ℝ) - (m' : ℝ)| ≤ 2 * (H / L) then
                ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖
              else 0) ^ 2 := by
          rw [show W = ∑ m ∈ bilinearRightSet M,
              ∑ m' ∈ bilinearRightSet M,
                ‖β m‖ * ‖β m'‖ * ‖bilinearC X H L P m m'‖ by rfl,
            bilinear_weightedC_eq_band X H L M hL hM hr β P]
        _ ≤ A * E := bilinear_band_weightedC_sq_le X H L M β P
    have hA : A ≤ 5 * (H / L) * (M * V ^ 4) := by
      simpa [A, V] using bilinear_band_beta_square_le H L M hL hM hr β
    have hleft0 : 0 ≤ ρ ^ 2 * H ^ 2 * V ^ 2 := by positivity
    have hright0 : 0 ≤ L * W := by positivity
    have hlowerSq : (ρ ^ 2 * H ^ 2 * V ^ 2) ^ 2 ≤
        (L * W) ^ 2 := (sq_le_sq₀ hleft0 hright0).2 hlower
    have hbig : (ρ ^ 2 * H ^ 2 * V ^ 2) ^ 2 ≤
        L ^ 2 * (5 * (H / L) * (M * V ^ 4)) * E := by
      calc
        (ρ ^ 2 * H ^ 2 * V ^ 2) ^ 2 ≤ (L * W) ^ 2 := hlowerSq
        _ = L ^ 2 * W ^ 2 := by ring
        _ ≤ L ^ 2 * (A * E) :=
          mul_le_mul_of_nonneg_left hWsq (sq_nonneg L)
        _ ≤ L ^ 2 * ((5 * (H / L) * (M * V ^ 4)) * E) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hA hE0) (sq_nonneg L)
        _ = L ^ 2 * (5 * (H / L) * (M * V ^ 4)) * E := by ring
    have hfactor : V ^ 4 * (ρ ^ 4 * H ^ 4) ≤
        V ^ 4 * (L ^ 2 * (5 * (H / L) * M) * E) := by
      calc
        V ^ 4 * (ρ ^ 4 * H ^ 4) =
            (ρ ^ 2 * H ^ 2 * V ^ 2) ^ 2 := by ring
        _ ≤ L ^ 2 * (5 * (H / L) * (M * V ^ 4)) * E := hbig
        _ = V ^ 4 * (L ^ 2 * (5 * (H / L) * M) * E) := by ring
    have hfactor' : (ρ ^ 4 * H ^ 4) * V ^ 4 ≤
        (L ^ 2 * (5 * (H / L) * M) * E) * V ^ 4 := by
      simpa [mul_comm] using hfactor
    have hcancel : ρ ^ 4 * H ^ 4 ≤
        L ^ 2 * (5 * (H / L) * M) * E :=
      (mul_le_mul_iff_left₀ (pow_pos hVpos 4)).mp hfactor'
    have hdenom : 0 < L ^ 2 * (5 * (H / L) * M) := by positivity
    have hdiv : (ρ ^ 4 * H ^ 4) /
        (L ^ 2 * (5 * (H / L) * M)) ≤ E := by
      apply (div_le_iff₀ hdenom).2
      simpa [mul_comm] using hcancel
    have hidentity : (ρ ^ 4 * H ^ 4) /
          (L ^ 2 * (5 * (H / L) * M)) =
        ρ ^ 4 / 5 * M * (H / L) * (H / M) ^ 2 := by
      field_simp [hL.ne', hM.ne']
      <;> ring
    rw [← hidentity]
    simpa [E] using hdiv

end

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.bilinearC_eq_zero_of_band_lt
#print axioms FractionalPrimes.Literature.Polynomial.norm_bilinearC_le
#print axioms FractionalPrimes.Literature.Polynomial.bilinearUnweightedEnergy
