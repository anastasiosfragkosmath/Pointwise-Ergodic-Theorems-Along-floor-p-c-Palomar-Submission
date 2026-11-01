module

public import FractionalPrimes.ArithmeticBasicsAnalytic

@[expose] public section

namespace FractionalPrimes

theorem derivative_c_three_coefficient_lt_eleven :
    derivativeWeylConstant *
      ((14 / 5 : ℝ) * 8 / derivativeWeylConstant) ^ ((4 : ℝ) / 8) < 11 := by
  let C : ℝ := derivativeWeylConstant *
    ((14 / 5 : ℝ) * 8 / derivativeWeylConstant) ^ ((4 : ℝ) / 8) *
    (1 : ℝ) ^ (2 * (1 : ℝ) / 8)
  have hBpos := derivativeWeylConstant_pos
  have hBlt := derivativeWeylConstant_bounds.2.1
  have hx : 0 ≤ ((14 / 5 : ℝ) * 8 / derivativeWeylConstant) :=
    div_nonneg (by positivity) hBpos.le
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCsq : C ^ 2 = 8 * (14 / 5 : ℝ) * derivativeWeylConstant := by
    dsimp [C]
    rw [show (4 : ℝ) / 8 = 1 / 2 by norm_num,
      show 2 * (1 : ℝ) / 8 = 1 / 4 by norm_num]
    norm_num
    rw [mul_pow, derivative_rpow_half_sq
      (112 / 5 / derivativeWeylConstant) (by positivity)]
    field_simp [hBpos.ne']
    <;> ring
  have hCsqLt : C ^ 2 < 121 := by rw [hCsq]; nlinarith
  have hC : C < 11 := by nlinarith [sq_nonneg (C - 11)]
  simpa [C] using hC

theorem derivative_c_four_coefficient_lt_eleven :
    derivativeWeylConstant *
      ((14 / 5 : ℝ) * 16 / derivativeWeylConstant) ^ ((4 : ℝ) / 16) *
      (2 : ℝ) ^ (2 * (2 : ℝ) / 16) < 11 := by
  let C : ℝ := derivativeWeylConstant *
    ((14 / 5 : ℝ) * 16 / derivativeWeylConstant) ^ ((4 : ℝ) / 16) *
    (2 : ℝ) ^ (2 * (2 : ℝ) / 16)
  have hBpos := derivativeWeylConstant_pos
  have hBlt := derivativeWeylConstant_bounds.2.1
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCfour : C ^ 4 = 32 * (14 / 5 : ℝ) * derivativeWeylConstant ^ 3 := by
    dsimp [C]
    rw [show (4 : ℝ) / 16 = 1 / 4 by norm_num,
      show 2 * (2 : ℝ) / 16 = 1 / 4 by norm_num]
    calc
      (derivativeWeylConstant *
          ((14 / 5 : ℝ) * 16 / derivativeWeylConstant) ^ (1 / 4 : ℝ) *
          (2 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 =
        derivativeWeylConstant ^ 4 *
          (((14 / 5 : ℝ) * 16 / derivativeWeylConstant) ^ (1 / 4 : ℝ)) ^ 4 *
          ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by ring
      _ = derivativeWeylConstant ^ 4 *
          ((14 / 5 : ℝ) * 16 / derivativeWeylConstant) * 2 := by
        have hx1 : 0 ≤ ((14 / 5 : ℝ) * 16 / derivativeWeylConstant) :=
          div_nonneg (by positivity) hBpos.le
        rw [derivative_rpow_quarter_fourth
          (((14 / 5 : ℝ) * 16 / derivativeWeylConstant)) hx1,
          derivative_rpow_quarter_fourth (2 : ℝ) (by norm_num)]
      _ = 32 * (14 / 5 : ℝ) * derivativeWeylConstant ^ 3 := by
        field_simp [hBpos.ne']
        <;> ring
  have hBsq : derivativeWeylConstant ^ 2 < 25 := by
    nlinarith [sq_nonneg (derivativeWeylConstant - 5)]
  have hBcube : derivativeWeylConstant ^ 3 < 125 := by
    calc
      derivativeWeylConstant ^ 3 = derivativeWeylConstant ^ 2 *
          derivativeWeylConstant := by ring
      _ < 25 * derivativeWeylConstant :=
        mul_lt_mul_of_pos_right hBsq hBpos
      _ < 25 * 5 := mul_lt_mul_of_pos_left hBlt (by norm_num)
      _ = 125 := by norm_num
  have hCfourLt : C ^ 4 < 14641 := by rw [hCfour]; nlinarith [hBcube]
  have hC : C < 11 := by nlinarith [sq_nonneg (C ^ 2 - 121)]
  exact hC

theorem derivative_c_coefficient_lt_eleven (d : ℕ) (hd : 3 ≤ d) :
    let h : ℕ := d - 2
    let D : ℝ := (2 : ℝ) ^ d
    derivativeWeylConstant *
      ((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
      (h : ℝ) ^ (2 * (h : ℝ) / D) < 11 := by
  let h : ℕ := d - 2
  let D : ℝ := (2 : ℝ) ^ d
  by_cases hd3 : d = 3
  · subst d
    convert derivative_c_three_coefficient_lt_eleven using 1 <;>
      norm_num [h, D]
  · by_cases hd4 : d = 4
    · subst d
      convert derivative_c_four_coefficient_lt_eleven using 1 <;>
        norm_num [h, D]
    · have hd5 : 5 ≤ d := by omega
      have hhd : h + 2 = d := by dsimp [h]; omega
      have hh : 3 ≤ h := by dsimp [h]; omega
      simpa [h, D] using
        (derivative_c_large_coefficient_lt_eleven hhd hh rfl)

theorem derivative_optimized_constants_lt_eleven (d : ℕ) (hd : 3 ≤ d) :
    let h : ℕ := d - 2
    let D : ℝ := (2 : ℝ) ^ d
    derivativeWeylConstant * Real.sqrt 2 * (h : ℝ) ^ (2 / D) < 11 ∧
    derivativeWeylConstant *
      ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d *
        ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 * D) ^ (2 / D) < 11 ∧
    derivativeWeylConstant *
      ((81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (D / 4) *
        ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2) ^ (1 / (D - 2)) < 11 ∧
    derivativeWeylConstant *
      ((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
      (h : ℝ) ^ (2 * (h : ℝ) / D) < 11 := by
  let h : ℕ := d - 2
  let D : ℝ := (2 : ℝ) ^ d
  have ha := derivative_a_coefficient_lt_eleven d hd
  have hap := derivative_ap_coefficient_lt_eleven d hd
  have hb := derivative_b_coefficient_lt_eleven d hd
  have hc := derivative_c_coefficient_lt_eleven d hd
  exact ⟨by simpa [h, D] using ha,
    by simpa [D] using hap,
    by simpa [D] using hb,
    by simpa [h, D] using hc⟩

/-- A continuous function bounded away from zero on the paper's half-open
interval has one sign throughout that interval. The proof uses compact
subintervals whose endpoints lie in `Ioc`, so no regularity is required at
the excluded left endpoint. -/
theorem continuousOn_fixed_sign_Ioc {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Set.Ioc a b))
    (hnonzero : ∀ t ∈ Set.Ioc a b, 0 < |f t|) :
    (∀ t ∈ Set.Ioc a b, 0 < f t) ∨ (∀ t ∈ Set.Ioc a b, f t < 0) := by
  have hbmem : b ∈ Set.Ioc a b := ⟨hab, le_rfl⟩
  have hbne : f b ≠ 0 := by
    intro hzero
    have h := hnonzero b hbmem
    rw [hzero, abs_zero] at h
    exact (lt_irrefl 0) h
  rcases lt_or_gt_of_ne hbne with hbneg | hbpos
  · right
    intro t ht
    have htne : f t ≠ 0 := by
      intro hzero
      have h := hnonzero t ht
      rw [hzero, abs_zero] at h
      exact (lt_irrefl 0) h
    rcases lt_or_gt_of_ne htne with htneg | htpos
    · exact htneg
    · exfalso
      have hsubset : Set.Icc t b ⊆ Set.Ioc a b := by
        intro z hz
        exact ⟨lt_of_lt_of_le ht.1 hz.1, hz.2⟩
      have hcont' : ContinuousOn f (Set.Icc t b) := hcont.mono hsubset
      have hzeroMem : (0 : ℝ) ∈ Set.Icc ((-f) t) ((-f) b) := by
        constructor <;> simp only [Pi.neg_apply] <;> linarith
      obtain ⟨z, hz, hfz⟩ :=
        intermediate_value_Icc ht.2 hcont'.neg hzeroMem
      have hzm : z ∈ Set.Ioc a b := hsubset hz
      have h := hnonzero z hzm
      have hfz' : f z = 0 := by simpa using congrArg Neg.neg hfz
      rw [hfz', abs_zero] at h
      exact (lt_irrefl 0) h
  · left
    intro t ht
    have htne : f t ≠ 0 := by
      intro hzero
      have h := hnonzero t ht
      rw [hzero, abs_zero] at h
      exact (lt_irrefl 0) h
    rcases lt_or_gt_of_ne htne with htneg | htpos
    · exfalso
      have hsubset : Set.Icc t b ⊆ Set.Ioc a b := by
        intro z hz
        exact ⟨lt_of_lt_of_le ht.1 hz.1, hz.2⟩
      have hcont' : ContinuousOn f (Set.Icc t b) := hcont.mono hsubset
      have hzeroMem : (0 : ℝ) ∈ Set.Icc (f t) (f b) := by
        constructor <;> linarith
      obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc ht.2 hcont' hzeroMem
      have hzm : z ∈ Set.Ioc a b := hsubset hz
      have h := hnonzero z hzm
      rw [hfz, abs_zero] at h
      exact (lt_irrefl 0) h
    · exact htpos

theorem derivative_optimized_estimate_abs
    {x Y lam Lambda : ℝ} {d : ℕ}
    (data : HalfOpenCkData x Y d)
    (hd : 3 ≤ d) (hY : (d : ℝ) < Y)
    (hlam : 0 < lam)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ |data.derivative d t|)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y),
      |data.derivative d t| ≤ Lambda) :
    let h : ℕ := d - 2
    let D : ℝ := (2 : ℝ) ^ d
    ‖∑ n ∈ realIntegerInterval x Y,
      realExponentialPhase (data.derivative 0) n‖ / Y ≤
    max
      (derivativeWeylConstant * Real.sqrt 2 * (h : ℝ) ^ (2 / D) *
        (Lambda / (lam * Y)) ^ (2 / D))
      (max
        (derivativeWeylConstant *
          ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d *
            ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 * D) ^ (2 / D) *
          (Lambda / (lam * Y)) ^ (2 / D))
        (max
          (derivativeWeylConstant *
            ((81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) *
              (2 : ℝ) ^ (D / 4) *
              ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2) ^
                (1 / (D - 2)) *
            (Lambda ^ 2 / lam) ^ (1 / (D - 2)))
          (derivativeWeylConstant *
            ((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
            (h : ℝ) ^ (2 * (h : ℝ) / D) *
            (lam * Y ^ d) ^ (-2 / D)))) := by
  let h : ℕ := d - 2
  let D : ℝ := (2 : ℝ) ^ d
  have hsign := continuousOn_fixed_sign_Ioc
    (a := x) (b := x + Y) (f := data.derivative d)
    (by linarith [data.length_pos]) (data.continuous d (le_rfl))
    (by
      intro t ht
      exact lt_of_lt_of_le hlam (hlower t ht))
  rcases hsign with hpos | hneg
  · have hlower' : ∀ t ∈ Set.Ioc x (x + Y), lam ≤ data.derivative d t := by
      intro t ht
      simpa [abs_of_pos (hpos t ht)] using hlower t ht
    have hupper' : ∀ t ∈ Set.Ioc x (x + Y),
        data.derivative d t ≤ Lambda := by
      intro t ht
      simpa [abs_of_pos (hpos t ht)] using hupper t ht
    exact derivative_optimized_estimate data hd hY hlam hlower' hupper'
  · have hlower' : ∀ t ∈ Set.Ioc x (x + Y),
        lam ≤ (data.neg).derivative d t := by
      intro t ht
      have hval := hlower t ht
      rw [HalfOpenCkData.neg] at *
      simpa [abs_of_neg (hneg t ht)] using hval
    have hupper' : ∀ t ∈ Set.Ioc x (x + Y),
        (data.neg).derivative d t ≤ Lambda := by
      intro t ht
      have hval := hupper t ht
      rw [HalfOpenCkData.neg] at *
      simpa [abs_of_neg (hneg t ht)] using hval
    have hopt := derivative_optimized_estimate (data.neg) hd hY hlam hlower' hupper'
    have hsum :
        (∑ n ∈ realIntegerInterval x Y,
          realExponentialPhase ((data.neg).derivative 0) n) =
          star (∑ n ∈ realIntegerInterval x Y,
            realExponentialPhase (data.derivative 0) n) := by
      simpa [HalfOpenCkData.neg] using
        realExponentialPhase_sum_neg (data.derivative 0) x Y
    have hnorm :
        ‖∑ n ∈ realIntegerInterval x Y,
          realExponentialPhase ((data.neg).derivative 0) n‖ =
          ‖∑ n ∈ realIntegerInterval x Y,
            realExponentialPhase (data.derivative 0) n‖ := by
      rw [hsum, norm_star]
    simpa [h, D, hnorm] using hopt

theorem derivative_four_term_max_le_eleven
    (a b c e X Z W : ℝ)
    (ha : a < 11) (hb : b < 11) (hc : c < 11) (he : e < 11)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hW : 0 ≤ W) :
    max (a * X) (max (b * X) (max (c * Z) (e * W))) ≤
      11 * max X (max Z W) := by
  have hM : 0 ≤ max X (max Z W) := by positivity
  apply max_le
  · calc
      a * X ≤ 11 * X := by nlinarith [mul_nonneg hX (by linarith : 0 ≤ 11 - a)]
      _ ≤ 11 * max X (max Z W) :=
        mul_le_mul_of_nonneg_left (le_max_left X (max Z W)) (by norm_num)
  · apply max_le
    · calc
        b * X ≤ 11 * X := by nlinarith [mul_nonneg hX (by linarith : 0 ≤ 11 - b)]
        _ ≤ 11 * max X (max Z W) :=
          mul_le_mul_of_nonneg_left (le_max_left X (max Z W)) (by norm_num)
    · apply max_le
      · calc
          c * Z ≤ 11 * Z := by nlinarith [mul_nonneg hZ (by linarith : 0 ≤ 11 - c)]
          _ ≤ 11 * max X (max Z W) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact le_trans (le_max_left Z W) (le_max_right X (max Z W))
      · calc
          e * W ≤ 11 * W := by nlinarith [mul_nonneg hW (by linarith : 0 ≤ 11 - e)]
          _ ≤ 11 * max X (max Z W) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact le_trans (le_max_right Z W) (le_max_right X (max Z W))

theorem derivative_test_eleven
    {x Y lam R : ℝ} {d : ℕ}
    (data : HalfOpenCkData x Y d)
    (hd : 3 ≤ d) (hfloor : (d : ℝ) < (Int.floor Y : ℝ))
    (hR : 1 ≤ R) (hlam : 0 < lam)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ |data.derivative d t|)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y),
      |data.derivative d t| ≤ R * lam) :
    ‖∑ n ∈ realIntegerInterval x Y,
      realExponentialPhase (data.derivative 0) n‖ / Y ≤
    11 * max ((R / Y) ^ (2 / (2 : ℝ) ^ d))
      (max ((R ^ 2 * lam) ^ (1 / ((2 : ℝ) ^ d - 2)))
        ((lam * Y ^ d) ^ (-2 / (2 : ℝ) ^ d))) := by
  let h : ℕ := d - 2
  let D : ℝ := (2 : ℝ) ^ d
  let X : ℝ := (R / Y) ^ (2 / D)
  let Z : ℝ := (R ^ 2 * lam) ^ (1 / (D - 2))
  let W : ℝ := (lam * Y ^ d) ^ (-2 / D)
  let c₁ : ℝ := derivativeWeylConstant * Real.sqrt 2 * (h : ℝ) ^ (2 / D)
  let c₂ : ℝ := derivativeWeylConstant *
    ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d *
      ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 * D) ^ (2 / D)
  let c₃ : ℝ := derivativeWeylConstant *
    ((81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (D / 4) *
      ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2) ^ (1 / (D - 2))
  let c₄ : ℝ := derivativeWeylConstant *
    ((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
      (h : ℝ) ^ (2 * (h : ℝ) / D)
  have hY : (d : ℝ) < Y := lt_of_lt_of_le hfloor (Int.floor_le Y)
  have hYpos : 0 < Y := data.length_pos
  have hratio : (R * lam) / (lam * Y) = R / Y := by
    field_simp [ne_of_gt hlam, ne_of_gt hYpos]
    <;> ring
  have hscale2 : ((R * lam) ^ 2 / lam) = R ^ 2 * lam := by
    field_simp [ne_of_gt hlam]
    <;> ring
  have hconstants := derivative_optimized_constants_lt_eleven d hd
  have hc₁ : c₁ < 11 := by simpa [c₁, h, D] using hconstants.1
  have hc₂ : c₂ < 11 := by simpa [c₂, D] using hconstants.2.1
  have hc₃ : c₃ < 11 := by simpa [c₃, D] using hconstants.2.2.1
  have hc₄ : c₄ < 11 := by simpa [c₄, h, D] using hconstants.2.2.2
  have hopt := derivative_optimized_estimate_abs
    (Lambda := R * lam) data hd hY hlam hlower hupper
  have hopt' :
      ‖∑ n ∈ realIntegerInterval x Y,
        realExponentialPhase (data.derivative 0) n‖ / Y ≤
      max (c₁ * X) (max (c₂ * X) (max (c₃ * Z) (c₄ * W))) := by
    rw [hratio, hscale2] at hopt
    simpa only [h, D, X, Z, W, c₁, c₂, c₃, c₄,
      mul_assoc, mul_left_comm, mul_comm] using hopt
  have hX : 0 ≤ X := by
    dsimp [X]
    positivity
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hmax := derivative_four_term_max_le_eleven c₁ c₂ c₃ c₄ X Z W
    hc₁ hc₂ hc₃ hc₄ hX hZ hW
  have hfinal := le_trans hopt' hmax
  simpa [X, Z, W, D, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- The arithmetic blueprint's external derivative-test interface, represented
by the half-open finite-derivative data used in the internal proof. -/
theorem externalDerivativeTest
    {x L lam R : ℝ} {j : ℕ}
    (data : HalfOpenCkData x L j)
    (hj : 3 ≤ j) (hfloor : (j : ℝ) < (Int.floor L : ℝ))
    (hR : 1 ≤ R) (hlam : 0 < lam)
    (hlower : ∀ t ∈ Set.Ioc x (x + L),
      lam ≤ |data.derivative j t|)
    (hupper : ∀ t ∈ Set.Ioc x (x + L),
      |data.derivative j t| ≤ R * lam) :
    ‖∑ n ∈ realIntegerInterval x L,
      realExponentialPhase (data.derivative 0) n‖ / L ≤
    11 * max ((R / L) ^ (2 / (2 : ℝ) ^ j))
      (max ((R ^ 2 * lam) ^ (1 / ((2 : ℝ) ^ j - 2)))
        ((lam * L ^ j) ^ (-2 / (2 : ℝ) ^ j))) := by
  exact derivative_test_eleven data hj hfloor hR hlam hlower hupper

theorem boundaryPhase_longBlock_derivative_test
    (c K a L : ℝ) (j : ℕ) (h : ℤ)
    (hK : 0 < K) (hKa : K ≤ a) (hL : 0 < L)
    (hUpper : a + L ≤ 2 * K) (hj : 3 ≤ j)
    (hfloor : (j : ℝ) < (Int.floor L : ℝ))
    (hcj : c < (j : ℝ)) (hcNon : NonIntegral c) (hh : h ≠ 0) :
    ‖∑ n ∈ realIntegerInterval a L,
      realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ / L ≤
    11 * max (((2 : ℝ) ^ (j - c) / L) ^ (2 / (2 : ℝ) ^ j))
      (max ((((2 : ℝ) ^ (j - c)) ^ 2 *
              (|(h : ℝ)| * |(descPochhammer ℝ j).eval c| * (2 * K) ^ (c - j))) ^
                (1 / ((2 : ℝ) ^ j - 2)))
        (((|(h : ℝ)| * |(descPochhammer ℝ j).eval c| *
              (2 * K) ^ (c - j)) * L ^ j) ^ (-2 / (2 : ℝ) ^ j))) := by
  let lam : ℝ := |(h : ℝ)| * |(descPochhammer ℝ j).eval c| * (2 * K) ^ (c - j)
  let R : ℝ := (2 : ℝ) ^ (j - c)
  let data := scaledRealMonomialHalfOpenData (h : ℝ) c a L j
    (lt_of_lt_of_le hK hKa) hL
  have hdata0 : data.derivative 0 = (fun t => (h : ℝ) * t ^ c) := by
    funext t
    simp [data, scaledRealMonomialHalfOpenData, scaledRealMonomialDerivative]
  have hlam : 0 < lam := by
    dsimp [lam]
    exact scaled_real_rpow_derivative_scale_pos j (by exact_mod_cast hh) hcNon hK
  have hR : 1 ≤ R := by
    dsimp [R]
    apply Real.one_le_rpow (by norm_num)
    linarith
  have hlower : ∀ t ∈ Set.Ioc a (a + L),
      lam ≤ |data.derivative j t| := by
    intro t ht
    have hb := scaledRealMonomialHalfOpenData_derivative_bounds
      c K a L j h hK hKa hL hUpper hcj ht
    simpa [data, lam, scaledRealMonomialHalfOpenData] using hb.1
  have hupper : ∀ t ∈ Set.Ioc a (a + L),
      |data.derivative j t| ≤ R * lam := by
    intro t ht
    have hb := scaledRealMonomialHalfOpenData_derivative_bounds
      c K a L j h hK hKa hL hUpper hcj ht
    simpa [data, lam, R, scaledRealMonomialHalfOpenData] using hb.2
  have htest := externalDerivativeTest data hj hfloor hR hlam hlower hupper
  simpa [hdata0, lam, R, mul_assoc] using htest

/-- Apply the exact derivative test to a scaled monomial on one dyadic
interval `(P,2P]`. -/
theorem scaledRealMonomial_dyadic_phase_sum_bound
    {a c P : ℝ} {j : ℕ}
    (ha : a ≠ 0) (hc : NonIntegral c) (hP : 0 < P)
    (hj : 3 ≤ j) (hcj : c < (j : ℝ))
    (hfloor : (j : ℝ) < (Int.floor P : ℝ)) :
    ‖∑ n ∈ realIntegerInterval P P,
      realExponentialPhase (fun t => a * t ^ c) n‖ / P ≤
      11 * max ((2 ^ (j - c) / P) ^ (2 / (2 : ℝ) ^ j))
        (max (((2 ^ (j - c)) ^ 2 *
              (|a| * |(descPochhammer ℝ j).eval c| * (2 * P) ^ (c - j))) ^
                (1 / ((2 : ℝ) ^ j - 2)))
          (((|a| * |(descPochhammer ℝ j).eval c| *
              (2 * P) ^ (c - j)) * P ^ j) ^ (-2 / (2 : ℝ) ^ j))) := by
  let lam : ℝ := |a| * |(descPochhammer ℝ j).eval c| * (2 * P) ^ (c - j)
  let R : ℝ := (2 : ℝ) ^ (j - c)
  let data : HalfOpenCkData P P j :=
    scaledRealMonomialHalfOpenData a c P P j hP hP
  have hdata0 : data.derivative 0 = (fun t => a * t ^ c) := by
    funext t
    simp [data, scaledRealMonomialHalfOpenData, scaledRealMonomialDerivative]
  have hlam : 0 < lam := by
    dsimp [lam]
    exact scaled_real_rpow_derivative_scale_pos j ha hc hP
  have hR : 1 ≤ R := by
    dsimp [R]
    apply Real.one_le_rpow (by norm_num)
    linarith
  have hlower : ∀ t ∈ Set.Ioc P (P + P), lam ≤ |data.derivative j t| := by
    intro t ht
    have htpos : 0 < t := lt_trans hP ht.1
    have hmodel : data.derivative j t =
        iteratedDeriv j (fun z : ℝ => a * z ^ c) t := by
      change scaledRealMonomialDerivative a c j t = _
      exact scaledRealMonomialDerivative_eq_iteratedDeriv j (ne_of_gt htpos)
    rw [hmodel]
    have ht2 : t ≤ 2 * P := by nlinarith [ht.2]
    exact (abs_iteratedDeriv_scaled_real_rpow_between a c P t j hP
      (le_of_lt ht.1) ht2 (by exact_mod_cast hcj)).1
  have hupper : ∀ t ∈ Set.Ioc P (P + P),
      |data.derivative j t| ≤ R * lam := by
    intro t ht
    have htpos : 0 < t := lt_trans hP ht.1
    have hmodel : data.derivative j t =
        iteratedDeriv j (fun z : ℝ => a * z ^ c) t := by
      change scaledRealMonomialDerivative a c j t = _
      exact scaledRealMonomialDerivative_eq_iteratedDeriv j (ne_of_gt htpos)
    rw [hmodel]
    have ht2 : t ≤ 2 * P := by nlinarith [ht.2]
    exact (abs_iteratedDeriv_scaled_real_rpow_between a c P t j hP
      (le_of_lt ht.1) ht2 (by exact_mod_cast hcj)).2
  have htest := derivative_test_eleven data hj hfloor hR hlam hlower hupper
  simpa [data, hdata0, lam, R, add_comm] using htest

/-- The dyadic derivative estimate in the dilation used by the arithmetic
monomial-cancellation lemma. -/
theorem dilatedRealMonomial_dyadic_phase_sum_bound
    {β c P : ℝ} {d : ℕ} {j : ℕ}
    (hβ : β ≠ 0) (hc : NonIntegral c) (hP : 0 < P) (hd : 0 < d)
    (hj : 3 ≤ j) (hcj : c < (j : ℝ))
    (hfloor : (j : ℝ) < (Int.floor P : ℝ)) :
    ‖∑ n ∈ realIntegerInterval P P,
      realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ / P ≤
      11 * max ((2 ^ (j - c) / P) ^ (2 / (2 : ℝ) ^ j))
        (max (((2 ^ (j - c)) ^ 2 *
              (|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
                (2 * P) ^ (c - j))) ^ (1 / ((2 : ℝ) ^ j - 2)))
          (((|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
              (2 * P) ^ (c - j)) * P ^ j) ^ (-2 / (2 : ℝ) ^ j))) := by
  let a : ℝ := β * (d : ℝ) ^ c
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero hβ (ne_of_gt (Real.rpow_pos_of_pos hdR c))
  have hsum :
      (∑ n ∈ realIntegerInterval P P,
        realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n) =
      ∑ n ∈ realIntegerInterval P P,
        realExponentialPhase (fun t => a * t ^ c) n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnI := (mem_realIntegerInterval_iff P P n).mp hn
    have hnt : 0 < (n : ℝ) := lt_trans hP hnI.1
    have hpow : ((d : ℝ) * (n : ℝ)) ^ c =
        (d : ℝ) ^ c * (n : ℝ) ^ c :=
      Real.mul_rpow (le_of_lt hdR) (le_of_lt hnt)
    rw [realExponentialPhase, hpow]
    dsimp [a]
    congr 1
    ring_nf
  rw [hsum]
  simpa [a] using scaledRealMonomial_dyadic_phase_sum_bound
    (a := a) (c := c) (P := P) (j := j) ha hc hP hj hcj hfloor

/-- Numerical exponent bound for the upper derivative-test term with the
fixed parameters from the blueprint. -/
theorem monomial_fixed_parameter_upper_exponent
    {c : ℝ} {j : ℕ} (hc : 1 < c)
    (hgapLower : 2 < (j : ℝ) - c)
    (hgapUpper : (j : ℝ) - c < 3) :
    let a : ℝ := 1 / 100
    let b : ℝ := 1 / 10000
    let κ : ℝ := a / (10 * (j : ℝ))
    let εd : ℝ := a / (100 * (j : ℝ))
    b + (j : ℝ) * εd - ((j : ℝ) - c) * (1 - κ) < -19 / 10 := by
  dsimp only
  have hj : 3 < (j : ℝ) := by linarith [hc, hgapLower]
  have hκpos : 0 < (1 / 100 : ℝ) / (10 * (j : ℝ)) := by positivity
  have hκsmall : (1 / 100 : ℝ) / (10 * (j : ℝ)) < 1 / 1000 := by
    rw [div_lt_iff₀ (by positivity : 0 < 10 * (j : ℝ))]
    norm_num
    nlinarith
  have hprod : ((j : ℝ) - c) * ((1 / 100 : ℝ) / (10 * (j : ℝ))) <
      1 / 100 := by
    calc
      ((j : ℝ) - c) * ((1 / 100 : ℝ) / (10 * (j : ℝ))) <
          3 * ((1 / 100 : ℝ) / (10 * (j : ℝ))) :=
        mul_lt_mul_of_pos_right hgapUpper hκpos
      _ < 3 * (1 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_left hκsmall (by norm_num)
      _ < 1 / 100 := by norm_num
  have hjε : (j : ℝ) * ((1 / 100 : ℝ) / (100 * (j : ℝ))) =
      1 / 10000 := by
    field_simp
    norm_num
  rw [hjε]
  nlinarith [hgapLower, hprod]

/-- The fixed derivative order gives the lower-scale loss bound `cκ<a/10`. -/
theorem monomial_fixed_parameter_c_kappa_bound
    {c : ℝ} {j : ℕ} (hc : 1 < c)
    (hgapLower : 2 < (j : ℝ) - c) :
    c * ((1 / 100 : ℝ) / (10 * (j : ℝ))) < (1 / 100 : ℝ) / 10 := by
  have hj : 3 < (j : ℝ) := by linarith [hc, hgapLower]
  have hcj : c < (j : ℝ) := by linarith [hgapLower]
  have hcoeff : (1 / 100 : ℝ) / (10 * (j : ℝ)) =
      1 / (1000 * (j : ℝ)) := by
    field_simp
    <;> norm_num
  rw [hcoeff, show (1 / 100 : ℝ) / 10 = 1 / 1000 by norm_num]
  rw [div_eq_mul_inv]
  field_simp
  nlinarith

/-- Every fixed positive constant is eventually dominated by a positive real
power, with a concrete lower threshold suitable for the monomial argument. -/
theorem exists_real_rpow_threshold {C s : ℝ} (hs : 0 < s) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → C ≤ N ^ s := by
  have hlim : Filter.Tendsto (fun N : ℝ => N ^ s) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hs
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp hlim C
  refine ⟨max B 1, le_max_right _ _, ?_⟩
  intro N hN
  exact hB N (le_trans (le_max_left _ _) hN)

theorem exists_int_floor_rpow_threshold (j : ℕ) {ν : ℝ} (hν : ν < 1) :
    ∃ K₀ : ℝ, 2 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      (j : ℤ) < Int.floor (K ^ (1 - ν)) := by
  have hexists := exists_real_rpow_threshold
    (C := (j : ℝ) + 1) (s := 1 - ν) (by linarith)
  obtain ⟨K₁, hK₁, hlarge⟩ := hexists
  let K₀ := max K₁ 2
  refine ⟨K₀, le_max_right _ _, ?_⟩
  intro K hK
  have hK₁' : K₁ ≤ K := le_trans (le_max_left _ _) hK
  have hpower : (j : ℝ) + 1 ≤ K ^ (1 - ν) := hlarge K hK₁'
  have hcast : ((j : ℤ) + 1 : ℝ) ≤ K ^ (1 - ν) := by
    exact_mod_cast hpower
  have hfloor : (j : ℤ) + 1 ≤ Int.floor (K ^ (1 - ν)) :=
    (Int.le_floor).mpr (by
      simpa only [Int.cast_add, Int.cast_one] using hcast)
  omega

theorem boundaryDerivativeOrder_gt_four_mul_c_add_one (c : ℝ) :
    4 * c + 1 < ((Nat.ceil (4 * c) + 2 : ℕ) : ℝ) := by
  calc
    4 * c + 1 < 4 * c + 2 := by norm_num
    _ ≤ (Nat.ceil (4 * c) : ℝ) + 2 := by linarith [Nat.le_ceil (4 * c)]
    _ = ((Nat.ceil (4 * c) + 2 : ℕ) : ℝ) := by push_cast; ring

theorem exists_real_rpow_constant_absorption {A δ : ℝ} (hδ : 0 < δ) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      A * K ^ (-1 - δ) ≤ K ^ (-1 : ℝ) := by
  obtain ⟨K₀, hK₀, hlarge⟩ :=
    exists_real_rpow_threshold (C := max A 1) hδ
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_trans hK₀ hK)
  have hpower : max A 1 ≤ K ^ δ := hlarge K hK
  have hA : A ≤ K ^ δ := le_trans (le_max_left A 1) hpower
  calc
    A * K ^ (-1 - δ) ≤ K ^ δ * K ^ (-1 - δ) :=
      mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (le_of_lt hKpos) _)
    _ = K ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hKpos]
      congr 1
      ring

theorem boundaryFirstDerivativeTerm_decay
    {K L R ν D : ℝ} (hK : 1 ≤ K) (hL : 0 < L) (hR : 0 < R)
    (hLength : K ^ (1 - ν) ≤ L) (hν : ν ≤ 1 / 2) (hD : 0 < D) :
    (R / L) ^ (2 / D) ≤ R ^ (2 / D) * K ^ (-1 / D) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKscale : 0 < K ^ (1 - ν) := Real.rpow_pos_of_pos hKpos _
  have hfrac : R / L ≤ R / K ^ (1 - ν) := by
    apply (div_le_div_iff₀ hL hKscale).2
    nlinarith [mul_nonneg (le_of_lt hR) (sub_nonneg.mpr hLength)]
  have hexp : 0 ≤ 2 / D := by positivity
  have hpow : (R / L) ^ (2 / D) ≤ (R / K ^ (1 - ν)) ^ (2 / D) :=
    Real.rpow_le_rpow (by positivity) hfrac hexp
  have hdenExp : 1 / D ≤ (1 - ν) * (2 / D) := by
    apply (div_le_iff₀ hD).2
    field_simp [ne_of_gt hD]
    nlinarith
  have hden : K ^ (1 / D) ≤ K ^ ((1 - ν) * (2 / D)) :=
    Real.rpow_le_rpow_of_exponent_le hK hdenExp
  have hquot : R ^ (2 / D) / K ^ ((1 - ν) * (2 / D)) ≤
      R ^ (2 / D) / K ^ (1 / D) := by
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hKpos _) (Real.rpow_pos_of_pos hKpos _)).2
    exact mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg (le_of_lt hR) _)
  calc
    (R / L) ^ (2 / D) ≤ (R / K ^ (1 - ν)) ^ (2 / D) := hpow
    _ = R ^ (2 / D) / K ^ ((1 - ν) * (2 / D)) := by
      rw [Real.div_rpow (le_of_lt hR) (le_of_lt hKscale), Real.rpow_mul hKpos.le]
    _ ≤ R ^ (2 / D) / K ^ (1 / D) := hquot
    _ = R ^ (2 / D) * K ^ (-1 / D) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hKpos.le]
      congr 1
      ring

theorem boundarySecondDerivativeTerm_decay
    {K R lam D : ℝ} (hK : 1 ≤ K) (hR : 0 < R)
    (hlam : 0 ≤ lam) (hlamK : lam ≤ K ^ (-1 : ℝ)) (hD : 2 < D) :
    (R ^ 2 * lam) ^ (1 / (D - 2)) ≤
      (R ^ 2) ^ (1 / (D - 2)) * K ^ (-1 / D) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hp : 0 < 1 / (D - 2) := by positivity
  have hbase : R ^ 2 * lam ≤ R ^ 2 * K ^ (-1 : ℝ) :=
    mul_le_mul_of_nonneg_left hlamK (sq_nonneg R)
  have hpow := Real.rpow_le_rpow (by positivity) hbase (le_of_lt hp)
  have hmul : (R ^ 2 * K ^ (-1 : ℝ)) ^ (1 / (D - 2)) =
      (R ^ 2) ^ (1 / (D - 2)) * K ^ (-(1 / (D - 2))) := by
    rw [Real.mul_rpow (sq_nonneg R) (Real.rpow_nonneg (le_of_lt hKpos) _),
      Real.rpow_neg_one, Real.rpow_neg_eq_inv_rpow]
  have hden : 1 / D ≤ 1 / (D - 2) := by
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hexp : -(1 / (D - 2)) ≤ -1 / D := by
    have h := neg_le_neg hden
    convert h using 1 <;> ring
  have hKpow : K ^ (-(1 / (D - 2))) ≤ K ^ (-1 / D) :=
    Real.rpow_le_rpow_of_exponent_le hK hexp
  calc
    (R ^ 2 * lam) ^ (1 / (D - 2)) ≤
        (R ^ 2 * K ^ (-1 : ℝ)) ^ (1 / (D - 2)) := hpow
    _ = (R ^ 2) ^ (1 / (D - 2)) * K ^ (-(1 / (D - 2))) := hmul
    _ ≤ (R ^ 2) ^ (1 / (D - 2)) * K ^ (-1 / D) :=
      mul_le_mul_of_nonneg_left hKpow (Real.rpow_nonneg (sq_nonneg R) _)

theorem boundaryThirdDerivativeTerm_decay
    {K B X D : ℝ} (hK : 1 ≤ K) (hB : 0 < B) (hX : 0 < X)
    (hscale : B * K ^ (3 / 4 : ℝ) ≤ X) (hD : 0 < D) :
    X ^ (-2 / D) ≤ B ^ (-2 / D) * K ^ (-1 / D) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hbase : 0 < B * K ^ (3 / 4 : ℝ) := by positivity
  have hexp : -2 / D ≤ 0 := by
    have hnonneg : 0 ≤ (2 : ℝ) / D := div_nonneg (by norm_num) (le_of_lt hD)
    have hneg : -(2 / D) ≤ 0 := neg_nonpos.mpr hnonneg
    convert hneg using 1 <;> ring
  have hcompare : X ^ (-2 / D) ≤ (B * K ^ (3 / 4 : ℝ)) ^ (-2 / D) :=
    Real.rpow_le_rpow_of_nonpos hbase hscale hexp
  have hmul : (B * K ^ (3 / 4 : ℝ)) ^ (-2 / D) =
      B ^ (-2 / D) * K ^ (-3 / (2 * D)) := by
    rw [Real.mul_rpow (le_of_lt hB) (Real.rpow_nonneg (le_of_lt hKpos) _),
      ← Real.rpow_mul hKpos.le]
    congr 1
    ring
  have hexpK : -3 / (2 * D) ≤ -1 / D := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * D) hD).2
    nlinarith
  have hKpow : K ^ (-3 / (2 * D)) ≤ K ^ (-1 / D) :=
    Real.rpow_le_rpow_of_exponent_le hK hexpK
  calc
    X ^ (-2 / D) ≤ (B * K ^ (3 / 4 : ℝ)) ^ (-2 / D) := hcompare
    _ = B ^ (-2 / D) * K ^ (-3 / (2 * D)) := hmul
    _ ≤ B ^ (-2 / D) * K ^ (-1 / D) :=
      mul_le_mul_of_nonneg_left hKpow (Real.rpow_nonneg (le_of_lt hB) _)

/-- The trivial short-block estimate has the stronger saving `ν`; it therefore
implies the `α` saving used in `ar:easyerror` whenever `α≤ν`. -/
theorem boundaryPhase_shortBlock_alpha_bound
    (f : ℝ → ℝ) (x K L ν α : ℝ)
    (hK : 1 ≤ K) (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hL : 0 ≤ L)
    (hLsmall : L < K ^ (1 - ν)) (hαν : α ≤ ν) :
    ‖∑ n ∈ realIntegerInterval x L, realExponentialPhase f n‖ ≤
      2 * K ^ (1 - α) := by
  have hshort := realIntegerInterval_phase_sum_short_scale_bound
    f x K L ν hK hν hν' hL hLsmall
  have hexp : 1 - ν ≤ 1 - α := by linarith
  have hpow : K ^ (1 - ν) ≤ K ^ (1 - α) :=
    Real.rpow_le_rpow_of_exponent_le hK hexp
  exact hshort.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))

theorem boundaryPhase_longBlock_third_scale
    (c K L : ℝ) (j : ℕ) (h : ℤ)
    (hc : 1 < c) (hcNon : NonIntegral c) (hK : 1 ≤ K)
    (hLength : K ^ (1 - 1 / (4 * (j : ℝ))) ≤ L)
    (hfreq : 1 ≤ |(h : ℝ)|) (horder : 4 * c + 1 < (j : ℝ))
    (hj : 0 < (j : ℝ)) :
    (|(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - j)) * K ^ (3 / 4 : ℝ) ≤
      (|(h : ℝ)| * |(descPochhammer ℝ j).eval c| *
        (2 * K) ^ (c - j)) * L ^ j := by
  let C : ℝ := |(descPochhammer ℝ j).eval c|
  let B : ℝ := C * (2 : ℝ) ^ (c - j)
  let ν : ℝ := 1 / (4 * (j : ℝ))
  let lam : ℝ := |(h : ℝ)| * C * (2 * K) ^ (c - j)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hC : 0 < C := by
    dsimp [C]
    exact abs_pos.mpr (descPochhammer_eval_ne_zero hcNon j)
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hscale : 0 < K ^ (c - (j : ℝ)) := Real.rpow_pos_of_pos hKpos _
  have hdyadic : (2 * K) ^ (c - (j : ℝ)) =
      (2 : ℝ) ^ (c - (j : ℝ)) * K ^ (c - (j : ℝ)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hKpos.le]
  have hlam : B * K ^ (c - (j : ℝ)) ≤ lam := by
    change C * (2 : ℝ) ^ (c - (j : ℝ)) * K ^ (c - (j : ℝ)) ≤
      |(h : ℝ)| * C * (2 * K) ^ (c - (j : ℝ))
    calc
      C * (2 : ℝ) ^ (c - (j : ℝ)) * K ^ (c - (j : ℝ)) =
          C * ((2 : ℝ) ^ (c - (j : ℝ)) * K ^ (c - (j : ℝ))) := by ring
      _ ≤ |(h : ℝ)| * C * ((2 : ℝ) ^ (c - (j : ℝ)) * K ^ (c - (j : ℝ))) := by
        have hfreqC : C ≤ |(h : ℝ)| * C := by
          nlinarith [mul_le_mul_of_nonneg_right hfreq (le_of_lt hC)]
        exact mul_le_mul_of_nonneg_right hfreqC (by positivity)
      _ = |(h : ℝ)| * C * (2 * K) ^ (c - (j : ℝ)) := by
        rw [← hdyadic]
      _ = _ := by ring
  have hLpow : K ^ ((1 - ν) * (j : ℝ)) ≤ L ^ j := by
    have hidentity : K ^ ((1 - ν) * (j : ℝ)) =
        (K ^ (1 - ν)) ^ j := by
      rw [Real.rpow_mul hKpos.le, Real.rpow_natCast]
    rw [hidentity]
    exact pow_le_pow_left₀ (by positivity) hLength j
  have hjν : (j : ℝ) * ν = 1 / 4 := by
    dsimp [ν]
    field_simp [ne_of_gt hj]
  have hgap : 3 / 4 < c - (j : ℝ) * ν := by rw [hjν]; linarith
  have hKpow : K ^ (3 / 4 : ℝ) ≤ K ^ (c - (j : ℝ) * ν) :=
    Real.rpow_le_rpow_of_exponent_le hK hgap.le
  have hmul : (B * K ^ (c - (j : ℝ))) * K ^ ((1 - ν) * (j : ℝ)) =
      B * K ^ (c - (j : ℝ) * ν) := by
    calc
      (B * K ^ (c - (j : ℝ))) * K ^ ((1 - ν) * (j : ℝ)) =
          B * (K ^ (c - (j : ℝ)) * K ^ ((1 - ν) * (j : ℝ))) := by ring
      _ = B * K ^ (c - (j : ℝ) * ν) := by
        rw [← Real.rpow_add hKpos]
        congr 2
        dsimp [ν]
        ring
  have hlampos : 0 < lam := by
    dsimp [lam, C]
    exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one hfreq)
      (abs_pos.mpr (descPochhammer_eval_ne_zero hcNon j)))
      (Real.rpow_pos_of_pos (by positivity) _)
  calc
    B * K ^ (3 / 4 : ℝ) ≤ B * K ^ (c - (j : ℝ) * ν) :=
      mul_le_mul_of_nonneg_left hKpow (by positivity)
    _ = (B * K ^ (c - (j : ℝ))) * K ^ ((1 - ν) * (j : ℝ)) := by rw [hmul]
    _ ≤ lam * L ^ j := mul_le_mul hlam hLpow (by positivity) (le_of_lt hlampos)

theorem exists_boundary_derivative_scale_threshold {c : ℝ} (hc : 1 < c) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ h : ℤ,
      |(h : ℝ)| ≤ K ^ (3 * c) →
      |(h : ℝ)| * |(descPochhammer ℝ (Nat.ceil (4 * c) + 2)).eval c| *
          (2 * K) ^ (c - ((Nat.ceil (4 * c) + 2 : ℕ) : ℝ)) ≤ K ^ (-1 : ℝ) := by
  let j : ℕ := Nat.ceil (4 * c) + 2
  let C : ℝ := |(descPochhammer ℝ j).eval c|
  let δ : ℝ := (j : ℝ) - 4 * c - 1
  have hgap : 0 < δ := by
    dsimp [δ, j]
    have hceil : 4 * c ≤ (Nat.ceil (4 * c) : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  obtain ⟨K₀, hK₀, hlarge⟩ := exists_real_rpow_threshold (C := C) hgap
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK h hfreq
  change |(h : ℝ)| * C * (2 * K) ^ (c - (j : ℝ)) ≤ K ^ (-1 : ℝ)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_trans hK₀ hK)
  have hC : 0 ≤ C := by positivity
  have hCsmall : C ≤ K ^ δ := hlarge K hK
  have hpow : (2 * K) ^ (c - (j : ℝ)) ≤ K ^ (c - (j : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith [hKpos.le]) (by dsimp [δ] at hgap ⊢; linarith)
  calc
    |(h : ℝ)| * C * (2 * K) ^ (c - (j : ℝ)) =
        C * (|(h : ℝ)| * (2 * K) ^ (c - (j : ℝ))) := by ring
    _ ≤ C * (K ^ (3 * c) * (2 * K) ^ (c - (j : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hfreq (Real.rpow_nonneg (by positivity) _)) hC
    _ ≤ C * (K ^ (3 * c) * K ^ (c - (j : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (le_of_lt hKpos) _)) hC
    _ = C * K ^ (4 * c - (j : ℝ)) := by
      rw [← Real.rpow_add hKpos]
      congr 2
      ring
    _ ≤ K ^ δ * K ^ (4 * c - (j : ℝ)) :=
      mul_le_mul_of_nonneg_right hCsmall
        (Real.rpow_nonneg (le_of_lt hKpos) _)
    _ = K ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hKpos]
      congr 1
      dsimp [δ]
      ring

/-- Package the frequency cutoff and strict floor condition for the exact
derivative order used in `ar:easyerror`. -/
theorem exists_boundary_phase_cutoff_bundle {c : ℝ} (hc : 1 < c) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      (∀ h : ℤ, |(h : ℝ)| ≤ K ^ (3 * c) →
        |(h : ℝ)| *
          |(descPochhammer ℝ (Nat.ceil (4 * c) + 2)).eval c| *
          (2 * K) ^ (c - ((Nat.ceil (4 * c) + 2 : ℕ) : ℝ)) ≤ K ^ (-1 : ℝ)) ∧
      ((Nat.ceil (4 * c) + 2 : ℕ) : ℤ) <
        Int.floor (K ^ (1 - 1 /
          (4 * ((Nat.ceil (4 * c) + 2 : ℕ) : ℝ)))) := by
  let j : ℕ := Nat.ceil (4 * c) + 2
  have horder : 4 * c + 1 < (j : ℝ) := by
    simpa [j] using boundaryDerivativeOrder_gt_four_mul_c_add_one c
  have hj : 1 ≤ (j : ℝ) := by linarith [horder, hc]
  have hνlt : 1 / (4 * (j : ℝ)) < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < 4 * (j : ℝ))).2
    nlinarith [hj]
  obtain ⟨Kcut, hKcut, hscale⟩ := exists_boundary_derivative_scale_threshold hc
  obtain ⟨Kf, hKf, hf⟩ := exists_int_floor_rpow_threshold j hνlt
  have hKfOne : 1 ≤ Kf := by linarith
  refine ⟨max Kcut Kf, le_max_of_le_right hKfOne, ?_⟩
  intro K hK
  have hKcut' : Kcut ≤ K := le_trans (le_max_left _ _) hK
  have hKf' : Kf ≤ K := le_trans (le_max_right _ _) hK
  constructor
  · intro h hfreq
    simpa [j] using hscale K hKcut' h hfreq
  · simpa [j] using hf K hKf'

/-- Long-block derivative-test estimate after the cutoff `λ≤K⁻¹` has been
established. The cutoff is discharged by
`exists_boundary_derivative_scale_threshold`. -/
theorem boundaryPhase_longBlock_scaled_bound_of_lambda
    (c K a L : ℝ) (j : ℕ) (h : ℤ)
    (hc : 1 < c) (hcNon : NonIntegral c) (hK : 1 ≤ K)
    (hLength : K ^ (1 - 1 / (4 * (j : ℝ))) ≤ L)
    (hfreq : 1 ≤ |(h : ℝ)|) (horder : 4 * c + 1 < (j : ℝ))
    (hj : 0 < (j : ℝ)) (hLamSmall :
      |(h : ℝ)| * |(descPochhammer ℝ j).eval c| *
          (2 * K) ^ (c - (j : ℝ)) ≤ K ^ (-1 : ℝ))
    (hKa : K ≤ a) (hL : 0 < L) (hUpper : a + L ≤ 2 * K)
    (hfloor : (j : ℝ) < (Int.floor L : ℝ)) :
    let D : ℝ := (2 : ℝ) ^ j
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    ‖∑ n ∈ realIntegerInterval a L,
      realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ / L ≤
      C * K ^ (-1 / D) := by
  dsimp only
  let D : ℝ := (2 : ℝ) ^ j
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
  let lam : ℝ := |(h : ℝ)| * |(descPochhammer ℝ j).eval c| *
    (2 * K) ^ (c - (j : ℝ))
  let C : ℝ := 11 * max (R ^ (2 / D))
    (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hD : 2 < D := by
    dsimp [D]
    have hj3 : 3 ≤ j := by
      have : (3 : ℝ) ≤ (j : ℝ) := by linarith [horder, hc]
      exact_mod_cast this
    calc
      (2 : ℝ) < (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ j := by
        exact_mod_cast (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj3)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hBpos : 0 < B := by
    dsimp [B]
    exact mul_pos (abs_pos.mpr (descPochhammer_eval_ne_zero hcNon j)) (by positivity)
  have hlampos : 0 < lam := by
    dsimp [lam]
    exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one hfreq)
      (abs_pos.mpr (descPochhammer_eval_ne_zero hcNon j))) (by positivity)
  have hlamK : lam ≤ K ^ (-1 : ℝ) := hLamSmall
  have hderiv := boundaryPhase_longBlock_derivative_test
    c K a L j h (lt_of_lt_of_le zero_lt_one hK) hKa hL hUpper
    (by
      have hj3 : 3 ≤ j := by
        have : (3:ℝ) ≤ j := by linarith [horder, hc]
        exact_mod_cast this
      exact hj3)
    hfloor (by linarith [horder]) hcNon (by
      intro heq
      have := hfreq
      norm_num [heq] at this)
  have hfirst := boundaryFirstDerivativeTerm_decay hK hL hRpos
    hLength (by
      have hjge : 2 ≤ (j : ℝ) := by linarith [horder, hc]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (j : ℝ))).2
      nlinarith [hjge]) hDpos
  have hsecond := boundarySecondDerivativeTerm_decay hK hRpos
    (le_of_lt hlampos) hlamK hD
  have hthirdscale := boundaryPhase_longBlock_third_scale c K L j h
    hc hcNon hK hLength hfreq horder hj
  have hthird := boundaryThirdDerivativeTerm_decay
    (K := K) (B := B) (X := lam * L ^ j) (D := D)
    hK hBpos (mul_pos hlampos (by positivity)) (by
      simpa [B, lam] using hthirdscale) hDpos
  have hmax : max ((R / L) ^ (2 / D))
        (max ((R ^ 2 * lam) ^ (1 / (D - 2)))
          ((lam * L ^ j) ^ (-2 / D))) ≤
      max (R ^ (2 / D)) (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D))) *
        K ^ (-1 / D) := by
    have hkpow : 0 ≤ K ^ (-1 / D) := Real.rpow_nonneg (le_of_lt hKpos) _
    have hcoeff1 : R ^ (2 / D) ≤
        max (R ^ (2 / D)) (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D))) :=
      le_max_left _ _
    have hcoeff2 : (R ^ 2) ^ (1 / (D - 2)) ≤
        max (R ^ (2 / D)) (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D))) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hcoeff3 : B ^ (-2 / D) ≤
        max (R ^ (2 / D)) (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D))) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hf' : (R / L) ^ (2 / D) ≤ R ^ (2 / D) * K ^ (-1 / D) := by
      simpa [D] using hfirst
    have hs' : (R ^ 2 * lam) ^ (1 / (D - 2)) ≤
        (R ^ 2) ^ (1 / (D - 2)) * K ^ (-1 / D) := by
      simpa [D] using hsecond
    have ht' : (lam * L ^ j) ^ (-2 / D) ≤ B ^ (-2 / D) * K ^ (-1 / D) := by
      simpa [D] using hthird
    apply max_le
    · exact hf'.trans
        (mul_le_mul_of_nonneg_right hcoeff1 hkpow)
    · apply max_le
      · exact hs'.trans
          (mul_le_mul_of_nonneg_right hcoeff2 hkpow)
      · exact ht'.trans
          (mul_le_mul_of_nonneg_right hcoeff3 hkpow)
  calc
    _ ≤ 11 * max ((R / L) ^ (2 / D))
          (max ((R ^ 2 * lam) ^ (1 / (D - 2))) ((lam * L ^ j) ^ (-2 / D))) := by
      simpa [D, R, lam] using hderiv
    _ ≤ C * K ^ (-1 / D) := by
      dsimp [C]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmax (by norm_num : 0 ≤ (11:ℝ))

/-- Unnormalize the long-block estimate, using that a subinterval of `(K,2K]`
has length at most `K`. -/
theorem boundaryPhase_longBlock_sum_bound_of_lambda
    (c K a L : ℝ) (j : ℕ) (h : ℤ)
    (hc : 1 < c) (hcNon : NonIntegral c) (hK : 1 ≤ K)
    (hLength : K ^ (1 - 1 / (4 * (j : ℝ))) ≤ L)
    (hfreq : 1 ≤ |(h : ℝ)|) (horder : 4 * c + 1 < (j : ℝ))
    (hj : 0 < (j : ℝ)) (hLamSmall :
      |(h : ℝ)| * |(descPochhammer ℝ j).eval c| *
          (2 * K) ^ (c - (j : ℝ)) ≤ K ^ (-1 : ℝ))
    (hKa : K ≤ a) (hL : 0 < L) (hUpper : a + L ≤ 2 * K)
    (hfloor : (j : ℝ) < (Int.floor L : ℝ)) :
    let D : ℝ := (2 : ℝ) ^ j
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    ‖∑ n ∈ realIntegerInterval a L,
      realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤
      C * K ^ (1 - 1 / D) := by
  dsimp only
  let D : ℝ := (2 : ℝ) ^ j
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
  let C : ℝ := 11 * max (R ^ (2 / D))
    (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
  have hnorm := boundaryPhase_longBlock_scaled_bound_of_lambda
    c K a L j h hc hcNon hK hLength hfreq horder hj hLamSmall hKa hL hUpper hfloor
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hLleK : L ≤ K := by linarith
  have hCpos : 0 < C := by
    dsimp [C, R, D, B]
    positivity
  calc
    ‖∑ n ∈ realIntegerInterval a L,
        realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ =
        (‖∑ n ∈ realIntegerInterval a L,
          realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ / L) * L := by
            rw [div_mul_cancel₀ _ (ne_of_gt hL)]
    _ ≤ (C * K ^ (-1 / D)) * L :=
      mul_le_mul_of_nonneg_right (by simpa [D, R, B, C] using hnorm) hL.le
    _ ≤ (C * K ^ (-1 / D)) * K :=
      mul_le_mul_of_nonneg_left hLleK (by positivity)
    _ = C * K ^ (1 - 1 / D) := by
      calc
        (C * K ^ (-1 / D)) * K = C * (K ^ (-1 / D) * K ^ (1 : ℝ)) := by
          rw [Real.rpow_one]
          ring
        _ = C * K ^ (1 - 1 / D) := by
          rw [← Real.rpow_add hKpos]
          congr 1
          ring

/-- Combine the trivial short-block case and the derivative-test long-block
case at a common `K^(1-α)` scale. -/
theorem boundaryPhase_interval_sum_bound_of_lambda
    (c K a L α : ℝ) (j : ℕ) (h : ℤ)
    (hc : 1 < c) (hcNon : NonIntegral c) (hK : 1 ≤ K)
    (hαν : α ≤ 1 / (4 * (j : ℝ))) (hαD : α ≤ 1 / (2 : ℝ) ^ j)
    (hfreq : 1 ≤ |(h : ℝ)|) (horder : 4 * c + 1 < (j : ℝ))
    (hj : 0 < (j : ℝ)) (hLamSmall :
      |(h : ℝ)| * |(descPochhammer ℝ j).eval c| *
          (2 * K) ^ (c - (j : ℝ)) ≤ K ^ (-1 : ℝ))
    (hKa : K ≤ a) (hL : 0 ≤ L) (hUpper : a + L ≤ 2 * K)
    (hfloor : K ^ (1 - 1 / (4 * (j : ℝ))) ≤ L →
      (j : ℝ) < (Int.floor L : ℝ)) :
    let D : ℝ := (2 : ℝ) ^ j
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    ‖∑ n ∈ realIntegerInterval a L,
      realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤
      max 2 C * K ^ (1 - α) := by
  dsimp only
  let D : ℝ := (2 : ℝ) ^ j
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
  let C : ℝ := 11 * max (R ^ (2 / D))
    (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hνpos : 0 < 1 / (4 * (j : ℝ)) := by positivity
  have hνle : 1 / (4 * (j : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * (j : ℝ))]
    norm_num
    nlinarith [hj]
  have hCpos : 0 < C := by
    dsimp [C, R, D, B]
    positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hD : 2 < D := by
    dsimp [D]
    have hj3 : 3 ≤ j := by
      have : (3 : ℝ) ≤ (j : ℝ) := by linarith [horder, hc]
      exact_mod_cast this
    calc
      (2 : ℝ) < (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ j := by
        exact_mod_cast (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj3)
  by_cases hshort : L < K ^ (1 - 1 / (4 * (j : ℝ)))
  · have hshortBound := boundaryPhase_shortBlock_alpha_bound
      (fun t => (h : ℝ) * t ^ c) a K L (1 / (4 * (j : ℝ))) α
      hK hνpos.le hνle hL hshort hαν
    have hpowpos : 0 ≤ K ^ (1 - α) := Real.rpow_nonneg hKpos.le _
    exact hshortBound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpowpos)
  · have hLength : K ^ (1 - 1 / (4 * (j : ℝ))) ≤ L := le_of_not_gt hshort
    have hLpos : 0 < L := lt_of_lt_of_le (Real.rpow_pos_of_pos hKpos _) hLength
    have hlong := boundaryPhase_longBlock_sum_bound_of_lambda
      c K a L j h hc hcNon hK hLength hfreq horder hj hLamSmall hKa hLpos hUpper
      (hfloor hLength)
    have hpow : K ^ (1 - 1 / D) ≤ K ^ (1 - α) :=
      Real.rpow_le_rpow_of_exponent_le hK (by dsimp [D]; linarith [hαD])
    have hpowpos : 0 ≤ K ^ (1 - α) := Real.rpow_nonneg hKpos.le _
    calc
      ‖∑ n ∈ realIntegerInterval a L,
          realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤
          C * K ^ (1 - 1 / D) := by simpa [D, R, B, C] using hlong
      _ ≤ C * K ^ (1 - α) := mul_le_mul_of_nonneg_left hpow hCpos.le
      _ ≤ max 2 C * K ^ (1 - α) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hpowpos

/-- The unified interval estimate specialized to the blueprint's exact order
`j_E=ceil(4c)+2`, subject to its two explicit large-`K` cutoff facts. -/
theorem boundaryPhase_paperOrder_interval_sum_bound_of_cutoffs
    (c K a L : ℝ) (h : ℤ) (hc : 1 < c) (hcNon : NonIntegral c)
    (hK : 1 ≤ K)
    (hLamSmall : |(h : ℝ)| *
      |(descPochhammer ℝ (Nat.ceil (4 * c) + 2)).eval c| *
      (2 * K) ^ (c - ((Nat.ceil (4 * c) + 2 : ℕ) : ℝ)) ≤ K ^ (-1 : ℝ))
    (hfloorK : ((Nat.ceil (4 * c) + 2 : ℕ) : ℤ) <
      Int.floor (K ^ (1 - 1 / (4 * ((Nat.ceil (4 * c) + 2 : ℕ) : ℝ)))))
    (hne : h ≠ 0) (hKa : K ≤ a) (hL : 0 ≤ L) (hUpper : a + L ≤ 2 * K) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    ‖∑ n ∈ realIntegerInterval a L,
      realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤
      max 2 C * K ^ (1 - α) := by
  let j : ℕ := Nat.ceil (4 * c) + 2
  let D : ℝ := (2 : ℝ) ^ j
  let α : ℝ := 1 / (8 * (j : ℝ) * D)
  have hj : 0 < (j : ℝ) := by
    dsimp [j]
    have hceil : 0 ≤ (Nat.ceil (4 * c) : ℝ) := by positivity
    push_cast
    linarith
  have horder : 4 * c + 1 < (j : ℝ) := by
    simpa [j] using boundaryDerivativeOrder_gt_four_mul_c_add_one c
  have hfreq : 1 ≤ |(h : ℝ)| := by
    exact_mod_cast Int.one_le_abs hne
  have hDgt : 2 < D := by
    dsimp [D]
    have hj3 : 3 ≤ j := by
      have : (3 : ℝ) ≤ (j : ℝ) := by linarith [horder, hc]
      exact_mod_cast this
    calc
      (2 : ℝ) < (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ j := by
        exact_mod_cast (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj3)
  have hαν : α ≤ 1 / (4 * (j : ℝ)) := by
    dsimp [α]
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * (j : ℝ) * D)
      (by positivity : 0 < 4 * (j : ℝ))).2
    have hDpos : 0 < D := by dsimp [D]; positivity
    nlinarith [hDpos, horder, hc]
  have hαD : α ≤ 1 / D := by
    dsimp [α]
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * (j : ℝ) * D)
      (by positivity : 0 < D)).2
    nlinarith [hDgt]
  have hfloor : K ^ (1 - 1 / (4 * (j : ℝ))) ≤ L →
      (j : ℝ) < (Int.floor L : ℝ) := by
    intro hLength
    have hfloorInt : (j : ℤ) < Int.floor (K ^ (1 - 1 / (4 * (j : ℝ)))) := by
      simpa [j] using hfloorK
    have hmono := Int.floor_mono hLength
    exact_mod_cast (lt_of_lt_of_le hfloorInt hmono)
  simpa [j, D, α] using
    (boundaryPhase_interval_sum_bound_of_lambda c K a L α j h hc hcNon hK
      hαν hαD hfreq horder hj hLamSmall hKa hL hUpper hfloor)

/-- Paper-order interval estimate with both large-`K` conditions supplied by
one cutoff. This is the local phase-sum input for `ar:easyerror`. -/
theorem exists_boundaryPhase_paperOrder_interval_sum_bound {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ a L : ℝ, ∀ h : ℤ,
      |(h : ℝ)| ≤ K ^ (3 * c) → h ≠ 0 → K ≤ a → 0 ≤ L → a + L ≤ 2 * K →
      ‖∑ n ∈ realIntegerInterval a L,
        realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤
        max 2 C * K ^ (1 - α) := by
  dsimp only
  obtain ⟨K₀, hK₀, hcutoff⟩ := exists_boundary_phase_cutoff_bundle hc
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK a L h hfreqUpper hne hKa hL hUpper
  have hcuts := hcutoff K hK
  have hKone : 1 ≤ K := le_trans hK₀ hK
  have hpaper := boundaryPhase_paperOrder_interval_sum_bound_of_cutoffs
    c K a L h hc hcNon hKone (hcuts.1 h hfreqUpper) hcuts.2
    hne hKa hL hUpper
  simpa [Nat.ceil, div_eq_mul_inv] using hpaper

/-- The paper-order phase estimate holds uniformly over every nonzero
frequency in a symmetric integer cutoff lying below `K^(3c)`. -/
theorem exists_boundaryPhase_symmetric_frequency_set_bound {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ a L : ℝ,
      K ≤ a → 0 ≤ L → a + L ≤ 2 * K → ∀ H : ℕ,
      (H : ℝ) ≤ K ^ (3 * c) →
      ∀ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), h ≠ 0 →
      ‖∑ n ∈ realIntegerInterval a L,
        realExponentialPhase (fun t => (h : ℝ) * t ^ c) n‖ ≤
        max 2 C * K ^ (1 - α) := by
  dsimp only
  obtain ⟨K₀, hK₀, hphase⟩ :=
    exists_boundaryPhase_paperOrder_interval_sum_bound hc hcNon
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK a L hKa hL hUpper H hH h hh hne
  have hmem := Finset.mem_Icc.mp hh
  have hlo : -(H : ℝ) ≤ (h : ℝ) := by exact_mod_cast hmem.1
  have hhi : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hmem.2
  have hfreq : |(h : ℝ)| ≤ K ^ (3 * c) :=
    (abs_le.mpr ⟨hlo, hhi⟩).trans hH
  exact hphase K hK a L h hfreq hne hKa hL hUpper

/-- The positive and negative finite Fourier blocks up to `H` inherit the
paper-order phase saving, multiplied by the global coefficient `ℓ¹` bound. -/
theorem exists_boundaryKernel_monomial_low_frequency_bounds {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ M : ℕ,
      ∀ (hM : 2 ≤ M),
      ∀ a L : ℝ, K ≤ a → 0 ≤ L → a + L ≤ 2 * K →
      ∀ H : ℕ, (H : ℝ) ≤ K ^ (3 * c) →
      (‖∑ k ∈ Finset.range H,
          boundaryKernelFourierCoefficient M hM ((k + 1 : ℕ) : ℤ) *
            ∑ n ∈ realIntegerInterval a L,
              realExponentialPhase
                (fun t => ((k + 1 : ℕ) : ℝ) * t ^ c) n‖ ≤
          (max 2 C * K ^ (1 - α)) *
            ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
              Real.sqrt (Real.log (2 * (M : ℝ)))) ∧
       ‖∑ k ∈ Finset.range H,
          boundaryKernelFourierCoefficient M hM
            (-((k + 1 : ℕ) : ℤ)) *
            ∑ n ∈ realIntegerInterval a L,
              realExponentialPhase
                (fun t => (-((k + 1 : ℕ) : ℝ)) * t ^ c) n‖ ≤
          (max 2 C * K ^ (1 - α)) *
            ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
              Real.sqrt (Real.log (2 * (M : ℝ))))) := by
  dsimp only
  obtain ⟨K₀, hK₀, hphase⟩ :=
    exists_boundaryPhase_symmetric_frequency_set_bound hc hcNon
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK M hM a L hKa hL hUpper H hH
  let j : ℕ := Nat.ceil (4 * c) + 2
  let D : ℝ := (2 : ℝ) ^ j
  let α : ℝ := 1 / (8 * (j : ℝ) * D)
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
  let C : ℝ := 11 * max (R ^ (2 / D))
    (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
  let P : ℝ := max 2 C * K ^ (1 - α)
  let freqPos : ℕ → ℤ := fun k => (k + 1 : ℕ)
  let freqNeg : ℕ → ℤ := fun k => -((k + 1 : ℕ) : ℤ)
  let phasePos : ℕ → ℂ := fun k =>
    ∑ n ∈ realIntegerInterval a L,
      realExponentialPhase (fun t => (freqPos k : ℝ) * t ^ c) n
  let phaseNeg : ℕ → ℂ := fun k =>
    ∑ n ∈ realIntegerInterval a L,
      realExponentialPhase (fun t => (freqNeg k : ℝ) * t ^ c) n
  have hKone : 1 ≤ K := le_trans hK₀ hK
  have hP : 0 ≤ P := by positivity
  have hfreqPosInj : Function.Injective freqPos := by
    intro m n h
    dsimp [freqPos] at h
    have hm : m + 1 = n + 1 := by exact_mod_cast h
    omega
  have hfreqNegInj : Function.Injective freqNeg := by
    intro m n h
    dsimp [freqNeg] at h
    have hc : ((m + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := neg_inj.mp h
    have hm : m + 1 = n + 1 := by exact_mod_cast hc
    omega
  have hphasePos : ∀ k ∈ Finset.range H, ‖phasePos k‖ ≤ P := by
    intro k hk
    have hklt : k < H := Finset.mem_range.mp hk
    have hkH : k + 1 ≤ H := by omega
    have hcast : ((k + 1 : ℕ) : ℤ) ≤ (H : ℤ) := by exact_mod_cast hkH
    have hfreqmem : freqPos k ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
      apply Finset.mem_Icc.mpr
      constructor
      · dsimp [freqPos]
        omega
      · simpa [freqPos] using hcast
    have hfreqne : freqPos k ≠ 0 := by
      dsimp [freqPos]
      omega
    have hbound := hphase K hK a L hKa hL hUpper H hH
      (freqPos k) hfreqmem hfreqne
    simpa [phasePos, P, C, R, D, B, α, j, Nat.ceil, div_eq_mul_inv] using hbound
  have hphaseNeg : ∀ k ∈ Finset.range H, ‖phaseNeg k‖ ≤ P := by
    intro k hk
    have hklt : k < H := Finset.mem_range.mp hk
    have hkH : k + 1 ≤ H := by omega
    have hcast : ((k + 1 : ℕ) : ℤ) ≤ (H : ℤ) := by exact_mod_cast hkH
    have hfreqmem : freqNeg k ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
      apply Finset.mem_Icc.mpr
      constructor
      · have hneg := neg_le_neg hcast
        simpa [freqNeg] using hneg
      · dsimp [freqNeg]
        omega
    have hfreqne : freqNeg k ≠ 0 := by
      dsimp [freqNeg]
      omega
    have hbound := hphase K hK a L hKa hL hUpper H hH
      (freqNeg k) hfreqmem hfreqne
    simpa [phaseNeg, P, C, R, D, B, α, j, Nat.ceil, div_eq_mul_inv] using hbound
  constructor
  · simpa [P, freqPos, phasePos, C, R, D, B, α, j, Nat.ceil,
      div_eq_mul_inv] using
      (boundaryKernel_frequency_sequence_sum_bound M hM (Finset.range H)
        freqPos hfreqPosInj phasePos P hP hphasePos)
  · simpa [P, freqNeg, phaseNeg, C, R, D, B, α, j, Nat.ceil,
      div_eq_mul_inv] using
      (boundaryKernel_frequency_sequence_sum_bound M hM (Finset.range H)
        freqNeg hfreqNegInj phaseNeg P hP hphaseNeg)

/-- One dyadic interval's boundary-kernel sum is bounded by the exact zero,
low-frequency, and high-frequency terms produced by the Fourier cutoff. -/
theorem nat_floor_monomial_tail_ratio_bound {K c M : ℝ}
    (hK : 1 ≤ K) (hc : 1 < c) (hM : 0 ≤ M) :
    let H : ℕ := Nat.floor (K ^ (3 * c))
    1 ≤ H ∧ (K + 1) * (2 * M / (H : ℝ)) ≤
      8 * M * K ^ (1 - 3 * c) := by
  dsimp only
  let X : ℝ := K ^ (3 * c)
  let H : ℕ := Nat.floor X
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hexp : 0 ≤ 3 * c := by positivity
  have hXone : 1 ≤ X := by
    dsimp [X]
    exact Real.one_le_rpow hK hexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hHone : 1 ≤ H := by
    dsimp [H]
    have hXoneCast : (↑(1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hXone
    exact Nat.le_floor hXoneCast
  have hHoneR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHone
  have hXlt : X < (H : ℝ) + 1 := by
    dsimp [H]
    exact Nat.lt_floor_add_one X
  have hXle : (H : ℝ) ≤ X := by
    dsimp [H]
    exact Nat.floor_le hXpos.le
  have hXle2H : X ≤ 2 * (H : ℝ) := by nlinarith
  have hratio : 2 * M / (H : ℝ) ≤ 4 * M / X := by
    apply (div_le_div_iff₀ (by exact_mod_cast hHone : 0 < (H : ℝ)) hXpos).2
    have hmul := mul_le_mul_of_nonneg_left hXle2H
      (by positivity : 0 ≤ 2 * M)
    nlinarith
  have hpow : X * K ^ (1 - 3 * c) = K := by
    dsimp [X]
    rw [← Real.rpow_add hKpos]
    rw [show 3 * c + (1 - 3 * c) = 1 by ring, Real.rpow_one]
  have hfactor : K / X = K ^ (1 - 3 * c) := by
    calc
      K / X = (X * K ^ (1 - 3 * c)) / X :=
        (congrArg (fun y : ℝ => y / X) hpow).symm
      _ = K ^ (1 - 3 * c) := by field_simp [ne_of_gt hXpos]
  have hKplus : K + 1 ≤ 2 * K := by linarith
  constructor
  · exact hHone
  · calc
      (K + 1) * (2 * M / (H : ℝ)) ≤ (2 * K) * (4 * M / X) :=
        mul_le_mul hKplus hratio (by positivity) (by positivity)
      _ = 8 * M * (K / X) := by ring
      _ = 8 * M * K ^ (1 - 3 * c) := by rw [hfactor]

/-- The number of dyadic blocks in the `Nat.log2` partition is bounded by a
constant times `log(2N)`. -/
theorem natLog2_le_log_two_mul (N : ℕ) (hN : 2 ≤ N) :
    (Nat.log2 N : ℝ) ≤ Real.log (2 * (N : ℝ)) / Real.log 2 := by
  have hlog2 := Real.log2_le_logb N
  rw [Real.logb] at hlog2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  exact hlog2.trans (div_le_div_of_nonneg_right hlogN hlog2pos.le)

/-- With `J=Nat.log2 N`, the terminal dyadic remainder has real length in
`[1,2)`, preserving the exact positive-integer endpoint convention. -/
theorem natLog2_dyadic_remainder_bounds (N : ℕ) (hN : 2 ≤ N) :
    1 ≤ (N : ℝ) / (2 : ℝ) ^ Nat.log2 N ∧
      (N : ℝ) / (2 : ℝ) ^ Nat.log2 N < 2 := by
  have hNne : N ≠ 0 := by omega
  have hpowNat : 2 ^ Nat.log2 N ≤ N := by
    simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hNne
  have hpowNat' : N < 2 ^ (Nat.log2 N + 1) := by
    simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hpowReal : ((2 ^ Nat.log2 N : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hpowNat
  have hupperReal : (N : ℝ) < (2 : ℝ) ^ (Nat.log2 N + 1) := by
    exact_mod_cast hpowNat'
  have hdenpos : 0 < (2 : ℝ) ^ Nat.log2 N := by positivity
  constructor
  · exact (le_div_iff₀ hdenpos).2 (by simpa [one_mul] using hpowReal)
  · apply (div_lt_iff₀ hdenpos).2
    have hpowSucc : (2 : ℝ) ^ (Nat.log2 N + 1) =
        (2 : ℝ) ^ Nat.log2 N * 2 := by rw [pow_succ]
    rw [hpowSucc] at hupperReal
    nlinarith

/-- Convert a dyadic block-count bound with a bounded terminal contribution
to the paper's logarithmic loss, without changing the three summands. -/
theorem dyadic_log_absorption
    {N M J U V a q r : ℝ}
    (hN : 2 ≤ N) (hM : 2 ≤ M)
    (hJ : J ≤ Real.log (2 * N) / Real.log 2)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : 0 ≤ a) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    J * (a * U + q * V + r * M) + 2 ≤
      (max 1 (max a (max q r))) * (1 / Real.log 2 + 1) *
        Real.log (2 * N) * (U + V + M) := by
  let L : ℝ := Real.log (2 * N)
  let T : ℝ := U + V + M
  let C : ℝ := max 1 (max a (max q r))
  have hNpos : 0 < N := by linarith
  have hLpos : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC1 : 1 ≤ C := by dsimp [C]; exact le_max_left _ _
  have hCa : a ≤ C := by
    dsimp [C]
    exact (le_max_left a (max q r)).trans (le_max_right 1 (max a (max q r)))
  have hCq : q ≤ C := by
    dsimp [C]
    exact ((le_max_left q r).trans (le_max_right a (max q r))).trans
      (le_max_right 1 (max a (max q r)))
  have hCr : r ≤ C := by
    dsimp [C]
    exact ((le_max_right q r).trans (le_max_right a (max q r))).trans
      (le_max_right 1 (max a (max q r)))
  have hT : 0 ≤ T := by dsimp [T]; linarith
  have hS : 0 ≤ a * U + q * V + r * M := by positivity
  have hcoeff : a * U + q * V + r * M ≤ C * T := by
    have h1 : a * U ≤ C * U := mul_le_mul_of_nonneg_right hCa hU
    have h2 : q * V ≤ C * V := mul_le_mul_of_nonneg_right hCq hV
    have h3 : r * M ≤ C * M := mul_le_mul_of_nonneg_right hCr
      (by linarith : 0 ≤ M)
    dsimp [T]
    nlinarith [h1, h2, h3]
  have hlog4 : (6 / 5 : ℝ) ≤ Real.log 4 := by
    convert Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) using 1 <;>
      norm_num
  have hlogLower : (6 / 5 : ℝ) ≤ L := by
    dsimp [L]
    exact hlog4.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hTtwo : 2 ≤ T := by
    dsimp [T]
    linarith
  have hterminal : 2 ≤ L * (C * T) := by
    have hprod := mul_nonneg (by linarith : 0 ≤ L - 6 / 5)
      (by linarith : 0 ≤ T - 2)
    have hLT : 2 ≤ L * T := by nlinarith
    have hCT : T ≤ C * T := by
      have hprod' := mul_nonneg (by linarith : 0 ≤ C - 1) hT
      nlinarith
    exact hLT.trans (mul_le_mul_of_nonneg_left hCT hLpos.le)
  have hfirst : J * (a * U + q * V + r * M) ≤
      (L / Real.log 2) * (C * T) := by
    calc
      J * (a * U + q * V + r * M) ≤
          (L / Real.log 2) * (a * U + q * V + r * M) :=
        mul_le_mul_of_nonneg_right hJ hS
      _ ≤ (L / Real.log 2) * (C * T) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
  calc
    J * (a * U + q * V + r * M) + 2 ≤
        (L / Real.log 2) * (C * T) + L * (C * T) :=
      add_le_add hfirst hterminal
    _ = C * (1 / Real.log 2 + 1) * L * T := by
      dsimp [L]
      ring

theorem exists_boundaryKernel_monomial_one_interval_bound {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ M : ℕ,
      ∀ (hM : 2 ≤ M),
      ∀ a L : ℝ, K ≤ a → 0 ≤ L → a + L ≤ 2 * K →
      ∀ H : ℕ, 1 ≤ H → (H : ℝ) ≤ K ^ (3 * c) →
      ‖∑ n ∈ realIntegerInterval a L,
        (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤
        ((2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) /
          (M : ℝ)) * (K + 1) +
        2 * (max 2 C * K ^ (1 - α)) *
          ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
            Real.sqrt (Real.log (2 * (M : ℝ)))) +
        (K + 1) * (2 * (M : ℝ) / (H : ℝ)) := by
  dsimp only
  obtain ⟨K₀, hK₀, hlow⟩ :=
    exists_boundaryKernel_monomial_low_frequency_bounds hc hcNon
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK M hM a L hKa hL hUpper H hH hCut
  let j : ℕ := Nat.ceil (4 * c) + 2
  let D : ℝ := (2 : ℝ) ^ j
  let α : ℝ := 1 / (8 * (j : ℝ) * D)
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
  let C : ℝ := 11 * max (R ^ (2 / D))
    (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
  let A : ℝ := (2 * (1 + (Real.log 4)⁻¹)) *
    Real.log (2 * (M : ℝ)) / (M : ℝ)
  let L1 : ℝ := (5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
    Real.sqrt (Real.log (2 * (M : ℝ)))
  let P : ℝ := max 2 C * K ^ (1 - α)
  let s : Finset ℤ := realIntegerInterval a L
  have hKone : 1 ≤ K := le_trans hK₀ hK
  have hLleK : L ≤ K := by linarith
  have hcard : (s.card : ℝ) ≤ K + 1 := by
    have hcard' := realIntegerInterval_card_le_of_nonneg a L hL
    dsimp [s]
    linarith
  have hApos : 0 ≤ A := by
    dsimp [A]
    have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
    have hlog : 0 < Real.log (2 * (M : ℝ)) := by
      apply Real.log_pos
      nlinarith [show (2 : ℝ) ≤ (M : ℝ) by exact_mod_cast hM]
    positivity
  have hPpos : 0 ≤ P := by positivity
  have hL1pos : 0 ≤ L1 := by
    dsimp [L1]
    have hlog : 0 ≤ Real.log (2 * (M : ℝ)) := by
      have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      exact le_of_lt (Real.log_pos (by nlinarith))
    positivity
  have hzero := boundaryKernelMonomial_zero_mode_bound M hM s c
  have hlow' := hlow K hK M hM a L hKa hL hUpper H hCut
  have htail := boundaryKernel_monomial_weighted_two_sided_tail_bound
    M H hM hH s c
  have hdec := sum_floorBoundaryKernel_monomial_cutoff_decomposition
    M H hM s c
  let z : ℂ := boundaryKernelMonomialFourierTerm M hM s c 0
  let p : ℂ := ∑ k ∈ Finset.range H,
    boundaryKernelMonomialFourierTerm M hM s c (k + 1)
  let pt : ℂ := ∑' k : ℕ,
    boundaryKernelMonomialFourierTerm M hM s c (k + H + 1)
  let n : ℂ := ∑ k ∈ Finset.range H,
    boundaryKernelMonomialFourierTerm M hM s c (-(k + 1))
  let nt : ℂ := ∑' k : ℕ,
    boundaryKernelMonomialFourierTerm M hM s c (-(k + H + 1))
  have hdec' :
      (∑ n ∈ s, (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)) =
        z + (p + pt) + (n + nt) := by
    simpa [z, p, pt, n, nt] using hdec
  have htriangle :
      ‖∑ n ∈ s, (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤
        ‖z‖ + ‖p‖ + ‖pt‖ + ‖n‖ + ‖nt‖ := by
    rw [hdec']
    calc
      ‖z + (p + pt) + (n + nt)‖ ≤ ‖z + (p + pt)‖ + ‖n + nt‖ := norm_add_le _ _
      _ ≤ (‖z‖ + ‖p + pt‖) + ‖n + nt‖ := by
        exact add_le_add (norm_add_le z (p + pt)) le_rfl
      _ ≤ (‖z‖ + (‖p‖ + ‖pt‖)) + (‖n‖ + ‖nt‖) := by
        have hp := norm_add_le p pt
        have hn := norm_add_le n nt
        linarith
      _ = ‖z‖ + ‖p‖ + ‖pt‖ + ‖n‖ + ‖nt‖ := by ring
  have hzero' : ‖z‖ ≤ A * (K + 1) := by
    dsimp [A] at hzero ⊢
    exact hzero.trans (mul_le_mul_of_nonneg_left hcard
      (by positivity))
  have hlowPos : ‖p‖ ≤ P * L1 := by
    simpa [p, boundaryKernelMonomialFourierTerm, P, L1, C, R, D, B, α, j,
      Nat.ceil, div_eq_mul_inv] using hlow'.1
  have hlowNeg : ‖n‖ ≤ P * L1 := by
    simpa [n, boundaryKernelMonomialFourierTerm, P, L1, C, R, D, B, α, j,
      Nat.ceil, div_eq_mul_inv] using hlow'.2
  have htail' : ‖pt‖ + ‖nt‖ ≤
      (K + 1) * (2 * (M : ℝ) / (H : ℝ)) := by
    have htail'' := htail
    dsimp [s] at htail''
    exact htail''.trans (mul_le_mul_of_nonneg_right hcard
      (by positivity))
  have hcombined :
      ‖z‖ + ‖p‖ + ‖pt‖ + ‖n‖ + ‖nt‖ ≤ A * (K + 1) + 2 * P * L1 +
              (K + 1) * (2 * (M : ℝ) / (H : ℝ)) := by
    linarith [hzero', hlowPos, hlowNeg, htail']
  calc
    ‖∑ n ∈ realIntegerInterval a L,
        (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤
      A * (K + 1) + 2 * P * L1 + (K + 1) * (2 * (M : ℝ) / (H : ℝ)) := by
        simpa [s] using htriangle.trans hcombined
    _ = ((2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) /
          (M : ℝ)) * (K + 1) +
        2 * (max 2 C * K ^ (1 - α)) *
          ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
            Real.sqrt (Real.log (2 * (M : ℝ)))) +
        (K + 1) * (2 * (M : ℝ) / (H : ℝ)) := by
      simp [A, L1, P]

/-- Uniformize one-interval boundary estimates for every dyadic scale
`K≤X`.  Small scales use only the pointwise kernel bound; large scales use
the checked one-interval estimate. -/
theorem boundaryKernel_uniform_block_bound_of_one_interval
    {c K₀ α A Q X K : ℝ} {M : ℕ}
    (hc : 1 < c) (hK₀ : 1 ≤ K₀) (hα : 0 < α) (hα' : α ≤ 1)
    (hX : 1 ≤ X) (hK : 0 ≤ K) (hKX : K ≤ X)
    (hM : 2 ≤ M) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (hinterval : ∀ K' : ℝ, K₀ ≤ K' →
      ‖∑ n ∈ realIntegerInterval K' K',
        (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤
        A * (K' + 1) + Q * K' ^ (1 - α) +
          8 * (M : ℝ) * K' ^ (1 - 3 * c)) :
    ‖∑ n ∈ realIntegerInterval K K,
      (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤
      max 8 ((K₀ + 1) / 2) *
        (A * X + Q * X ^ (1 - α) + (M : ℝ)) := by
  by_cases hlarge : K₀ ≤ K
  · have hKone : 1 ≤ K := le_trans hK₀ hlarge
    have hKplus : K + 1 ≤ 2 * X := by linarith
    have hKpow : K ^ (1 - α) ≤ X ^ (1 - α) :=
      Real.rpow_le_rpow (by linarith) hKX (by linarith)
    have htailpow : K ^ (1 - 3 * c) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hKone (by linarith)
    have hraw := hinterval K hlarge
    have hlargeBound :
        A * (K + 1) + Q * K ^ (1 - α) +
          8 * (M : ℝ) * K ^ (1 - 3 * c) ≤
        2 * (A * X) + Q * X ^ (1 - α) + 8 * (M : ℝ) := by
      have hAterm : A * (K + 1) ≤ 2 * (A * X) := by
        calc
          A * (K + 1) ≤ A * (2 * X) := mul_le_mul_of_nonneg_left hKplus hA
          _ = 2 * (A * X) := by ring
      have hQterm : Q * K ^ (1 - α) ≤ Q * X ^ (1 - α) :=
        mul_le_mul_of_nonneg_left hKpow hQ
      have htail :
          8 * (M : ℝ) * K ^ (1 - 3 * c) ≤ 8 * (M : ℝ) :=
        (mul_le_mul_of_nonneg_left htailpow
          (show 0 ≤ 8 * (M : ℝ) by positivity)).trans_eq (by ring)
      linarith
    have hcoeff8 : 8 ≤ max 8 ((K₀ + 1) / 2) := le_max_left _ _
    have hcoeff2 : 2 ≤ max 8 ((K₀ + 1) / 2) := by
      exact le_trans (by norm_num) hcoeff8
    have hscaled :
        2 * (A * X) + Q * X ^ (1 - α) + 8 * (M : ℝ) ≤
        max 8 ((K₀ + 1) / 2) *
          (A * X + Q * X ^ (1 - α) + (M : ℝ)) := by
      have hAX : 0 ≤ A * X := by positivity
      have hQX : 0 ≤ Q * X ^ (1 - α) := by positivity
      have hMnon : 0 ≤ (M : ℝ) := by positivity
      nlinarith
    exact (hraw.trans hlargeBound).trans hscaled
  · have hKlt : K < K₀ := lt_of_not_ge hlarge
    have hsum :
        ‖∑ n ∈ realIntegerInterval K K,
          (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤ K + 1 := by
      calc
        _ ≤ ∑ n ∈ realIntegerInterval K K,
            ‖(floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ := norm_sum_le _ _
        _ = ∑ n ∈ realIntegerInterval K K,
            floorBoundaryKernel M hM ((n : ℝ) ^ c) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [Real.norm_eq_abs, abs_of_nonneg
            (floorBoundaryKernel_nonneg M hM ((n : ℝ) ^ c))]
        _ ≤ ∑ _n ∈ realIntegerInterval K K, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          exact floorBoundaryKernel_le_one M hM ((n : ℝ) ^ c)
        _ = (realIntegerInterval K K).card := by simp
        _ ≤ K + 1 := realIntegerInterval_card_le_of_nonneg K K hK
    have hKplus : K + 1 ≤ K₀ + 1 := by linarith
    have htargetLarge : (K₀ + 1) ≤
        max 8 ((K₀ + 1) / 2) *
          (A * X + Q * X ^ (1 - α) + (M : ℝ)) := by
      have hcoeff : (K₀ + 1) / 2 ≤ max 8 ((K₀ + 1) / 2) := le_max_right _ _
      have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hcoeffNon : 0 ≤ (K₀ + 1) / 2 := by positivity
      have hmaxNon : 0 ≤ max 8 ((K₀ + 1) / 2) := by positivity
      have hfactor : ((K₀ + 1) / 2) * 2 ≤
          max 8 ((K₀ + 1) / 2) * (M : ℝ) :=
        mul_le_mul hcoeff hMreal (by norm_num) hmaxNon
      have hother : 0 ≤ A * X + Q * X ^ (1 - α) := by positivity
      nlinarith [hfactor]
    exact hsum.trans (hKplus.trans htargetLarge)

/-- The one-interval estimate with the blueprint cutoff
`H=floor(K^(3c))`, so its final term has the paper's `M K^(1-3c)` scale. -/
theorem exists_boundaryKernel_monomial_one_interval_bound_floor {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ M : ℕ,
      ∀ (hM : 2 ≤ M), ∀ a L : ℝ, K ≤ a → 0 ≤ L → a + L ≤ 2 * K →
      ‖∑ n ∈ realIntegerInterval a L,
        (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤
        ((2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) /
          (M : ℝ)) * (K + 1) +
        2 * (max 2 C * K ^ (1 - α)) *
          ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
            Real.sqrt (Real.log (2 * (M : ℝ)))) +
        8 * (M : ℝ) * K ^ (1 - 3 * c) := by
  dsimp only
  obtain ⟨K₀, hK₀, hblock⟩ :=
    exists_boundaryKernel_monomial_one_interval_bound hc hcNon
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK M hM a L hKa hL hUpper
  let j : ℕ := Nat.ceil (4 * c) + 2
  let D : ℝ := (2 : ℝ) ^ j
  let α : ℝ := 1 / (8 * (j : ℝ) * D)
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
  let C : ℝ := 11 * max (R ^ (2 / D))
    (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
  let A : ℝ := (2 * (1 + (Real.log 4)⁻¹)) *
    Real.log (2 * (M : ℝ)) / (M : ℝ)
  let L1 : ℝ := (5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
    Real.sqrt (Real.log (2 * (M : ℝ)))
  let P : ℝ := max 2 C * K ^ (1 - α)
  let H : ℕ := Nat.floor (K ^ (3 * c))
  have hKone : 1 ≤ K := le_trans hK₀ hK
  have hfloor := nat_floor_monomial_tail_ratio_bound
    (K := K) (c := c) (M := (M : ℝ)) hKone hc (by positivity)
  have hH : 1 ≤ H := by simpa [H] using hfloor.1
  have hHle : (H : ℝ) ≤ K ^ (3 * c) := by
    dsimp [H]
    exact Nat.floor_le (by positivity)
  have hinterval := hblock K hK M hM a L hKa hL hUpper H hH hHle
  have htail := hfloor.2
  calc
    ‖∑ n ∈ realIntegerInterval a L,
        (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤
      A * (K + 1) + 2 * P * L1 + 8 * (M : ℝ) * K ^ (1 - 3 * c) := by
        calc
          _ ≤ A * (K + 1) + 2 * P * L1 +
              (K + 1) * (2 * (M : ℝ) / (H : ℝ)) := by
            simpa [A, L1, P, C, R, D, B, α, j, Nat.ceil,
              div_eq_mul_inv] using hinterval
          _ ≤ A * (K + 1) + 2 * P * L1 +
              8 * (M : ℝ) * K ^ (1 - 3 * c) := by
            simpa [H] using
              add_le_add (le_rfl : A * (K + 1) + 2 * P * L1 ≤
                A * (K + 1) + 2 * P * L1) htail
    _ = ((2 * (1 + (Real.log 4)⁻¹)) * Real.log (2 * (M : ℝ)) /
          (M : ℝ)) * (K + 1) +
        2 * (max 2 C * K ^ (1 - α)) *
          ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
            Real.sqrt (Real.log (2 * (M : ℝ)))) +
        8 * (M : ℝ) * K ^ (1 - 3 * c) := by
      simp [A, L1, P]

/-- Instantiate the abstract uniform block bound with the exact three
coefficients supplied by the paper-order floor-cutoff estimate. -/
theorem exists_boundaryKernel_monomial_uniform_dyadic_block_bound {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    let a : ℝ := 2 * (1 + (Real.log 4)⁻¹)
    let q : ℝ := 2 * (max 2 C) * (5 * a + 2)
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ X : ℝ, 1 ≤ X → ∀ K : ℝ,
      0 ≤ K → K ≤ X → ∀ M : ℕ, ∀ (hM : 2 ≤ M),
      ‖∑ n ∈ realIntegerInterval K K,
        (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤
        max 8 ((K₀ + 1) / 2) *
          (a * X * Real.log (2 * (M : ℝ)) / (M : ℝ) +
            q * X ^ (1 - α) * Real.sqrt (Real.log (2 * (M : ℝ))) +
            (M : ℝ)) := by
  dsimp only
  obtain ⟨K₀, hK₀, hblock⟩ :=
    exists_boundaryKernel_monomial_one_interval_bound_floor hc hcNon
  refine ⟨K₀, hK₀, ?_⟩
  intro X hX K hK hKX M hM
  let j : ℕ := Nat.ceil (4 * c) + 2
  let D : ℝ := (2 : ℝ) ^ j
  let α : ℝ := 1 / (8 * (j : ℝ) * D)
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
  let C : ℝ := 11 * max (R ^ (2 / D))
    (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
  let a : ℝ := 2 * (1 + (Real.log 4)⁻¹)
  let q : ℝ := 2 * (max 2 C) * (5 * a + 2)
  let A : ℝ := a * Real.log (2 * (M : ℝ)) / (M : ℝ)
  let Q : ℝ := q * Real.sqrt (Real.log (2 * (M : ℝ)))
  have hαpos : 0 < α := by dsimp [α, D, j]; positivity
  have hjNat : 2 ≤ Nat.ceil (4 * c) + 2 := by omega
  have hj : 2 ≤ (j : ℝ) := by exact_mod_cast hjNat
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hden : 1 ≤ 8 * (j : ℝ) * D := by nlinarith
  have hαle : α ≤ 1 := by
    dsimp [α]
    exact (div_le_one (by positivity)).2 hden
  have hlogpos : 0 < Real.log (2 * (M : ℝ)) := by
    apply Real.log_pos
    have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith
  have hA : 0 ≤ A := by dsimp [A, a]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q, q]; positivity
  have hraw' : ∀ K' : ℝ, K₀ ≤ K' →
      ‖∑ n ∈ realIntegerInterval K' K',
        (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤
        A * (K' + 1) + Q * K' ^ (1 - α) +
          8 * (M : ℝ) * K' ^ (1 - 3 * c) := by
    intro K' hK'
    have hK'one : 1 ≤ K' := le_trans hK₀ hK'
    have h := hblock K' hK' M hM K' K' le_rfl (by linarith)
      (by nlinarith)
    convert h using 1 <;> dsimp [A, Q, a, q, j, D, α, R, B, C] <;> ring
  have hbound := boundaryKernel_uniform_block_bound_of_one_interval
    hc hK₀ hαpos hαle hX hK hKX hM hA hQ hraw'
  convert hbound using 1 <;> dsimp [A, Q, a, q, j, D, α, R, B, C] <;> ring

/-- Sum the exact uniform block estimate over the manuscript's finite dyadic
partition, with the terminal interval treated separately. -/
theorem exists_boundaryKernel_monomial_dyadic_sum_bound {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    let a : ℝ := 2 * (1 + (Real.log 4)⁻¹)
    let q : ℝ := 2 * (max 2 C) * (5 * a + 2)
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ N : ℕ, 2 ≤ N → ∀ M : ℕ,
      ∀ hM : 2 ≤ M,
      (∑ n ∈ realIntegerInterval 0 (N : ℝ),
        floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤
      (Nat.log2 N : ℝ) *
        (max 8 ((K₀ + 1) / 2) *
          (a * (N : ℝ) * Real.log (2 * (M : ℝ)) / (M : ℝ) +
            q * (N : ℝ) ^ (1 - α) *
              Real.sqrt (Real.log (2 * (M : ℝ))) + (M : ℝ))) + 2 := by
  dsimp only
  obtain ⟨K₀, hK₀, hblock⟩ :=
    exists_boundaryKernel_monomial_uniform_dyadic_block_bound hc hcNon
  refine ⟨K₀, hK₀, ?_⟩
  intro N hN M hM
  let j : ℕ := Nat.ceil (4 * c) + 2
  let D : ℝ := (2 : ℝ) ^ j
  let α : ℝ := 1 / (8 * (j : ℝ) * D)
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
  let C : ℝ := 11 * max (R ^ (2 / D))
    (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
  let a : ℝ := 2 * (1 + (Real.log 4)⁻¹)
  let q : ℝ := 2 * (max 2 C) * (5 * a + 2)
  let X : ℝ := (N : ℝ)
  let J : ℕ := Nat.log2 N
  let Bound : ℝ := max 8 ((K₀ + 1) / 2) *
    (a * X * Real.log (2 * (M : ℝ)) / (M : ℝ) +
      q * X ^ (1 - α) * Real.sqrt (Real.log (2 * (M : ℝ))) + (M : ℝ))
  have hX : 1 ≤ X := by
    dsimp [X]
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hN)
  have hblocks : ∀ v ∈ Finset.range J,
      (∑ n ∈ realDyadicIntegerBlock X v,
        floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤ Bound := by
    intro v hv
    let K : ℝ := X / (2 : ℝ) ^ (v + 1)
    have hden : 1 ≤ (2 : ℝ) ^ (v + 1) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hKX : K ≤ X := by
      apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (v + 1))).2
      calc
        X = X * 1 := by ring
        _ ≤ X * (2 : ℝ) ^ (v + 1) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
    have hpoint := hblock X hX K hK hKX M hM
    have hpoint' :
        ‖∑ n ∈ realIntegerInterval K K,
          (floorBoundaryKernel M hM ((n : ℝ) ^ c) : ℂ)‖ ≤ Bound := by
      simpa [Bound, X, K, j, D, α, R, B, C, a, q] using hpoint
    have hsum := norm_sum_floorBoundaryKernel_monomial_eq_sum
      M hM c (realDyadicIntegerBlock X v)
    simpa [realDyadicIntegerBlock, K] using hsum ▸ hpoint'
  let Y : ℝ := X / (2 : ℝ) ^ J
  have hYnon : 0 ≤ Y := by dsimp [Y, X]; positivity
  have hYlt : Y < 2 := by
    have hrem := natLog2_dyadic_remainder_bounds N hN
    simpa [Y, X, J] using hrem.2
  have hrem :
      (∑ n ∈ realIntegerInterval 0 Y,
        floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤ 2 :=
    sum_floorBoundaryKernel_monomial_terminal_lt_two M hM c Y hYnon hYlt
  have haggr := sum_realIntegerInterval_dyadic_uniform
    (X := X) (B := Bound) (R := 2) (J := J) (by positivity)
    (fun n => floorBoundaryKernel M hM ((n : ℝ) ^ c)) hblocks
    (by simpa [Y] using hrem)
  simpa [X, J, Bound, j, D, α, R, B, C, a, q] using haggr

/-- The complete all-truncation boundary-kernel estimate in the paper's
three-term form, over the exact positive-integer interval `(0,N]`. -/
theorem exists_boundaryKernel_monomial_all_truncation_bound {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    let a : ℝ := 2 * (1 + (Real.log 4)⁻¹)
    let q : ℝ := 2 * (max 2 C) * (5 * a + 2)
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ N : ℕ, 2 ≤ N → ∀ M : ℕ,
      ∀ hM : 2 ≤ M,
      (∑ n ∈ realIntegerInterval 0 (N : ℝ),
        floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤
      Cc * Real.log (2 * (N : ℝ)) *
        ((N : ℝ) * Real.log (2 * (M : ℝ)) / (M : ℝ) +
          (N : ℝ) ^ (1 - α) *
            Real.sqrt (Real.log (2 * (M : ℝ))) + (M : ℝ)) := by
  dsimp only
  obtain ⟨K₀, hK₀, hdyadic⟩ :=
    exists_boundaryKernel_monomial_dyadic_sum_bound hc hcNon
  let j : ℕ := Nat.ceil (4 * c) + 2
  let D : ℝ := (2 : ℝ) ^ j
  let α : ℝ := 1 / (8 * (j : ℝ) * D)
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
  let C : ℝ := 11 * max (R ^ (2 / D))
    (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
  let a : ℝ := 2 * (1 + (Real.log 4)⁻¹)
  let q : ℝ := 2 * (max 2 C) * (5 * a + 2)
  let Kfac : ℝ := max 8 ((K₀ + 1) / 2)
  let a' : ℝ := Kfac * a
  let q' : ℝ := Kfac * q
  let r' : ℝ := Kfac
  let Cc : ℝ := max 1 (max a' (max q' r')) *
    (1 / Real.log 2 + 1)
  refine ⟨Cc, ?_, ?_⟩
  · dsimp [Cc, a', q', r', Kfac, a, q, C, B, R, D, j]
    positivity
  · intro N hN M hM
    let X : ℝ := (N : ℝ)
    let U : ℝ := X * Real.log (2 * (M : ℝ)) / (M : ℝ)
    let V : ℝ := X ^ (1 - α) * Real.sqrt (Real.log (2 * (M : ℝ)))
    let J : ℝ := (Nat.log2 N : ℝ)
    have hNreal : 2 ≤ X := by dsimp [X]; exact_mod_cast hN
    have hMreal : 2 ≤ (M : ℝ) := by exact_mod_cast hM
    have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) :=
      Real.log_nonneg (by nlinarith)
    have hJ : J ≤ Real.log (2 * X) / Real.log 2 := by
      dsimp [J, X]
      exact natLog2_le_log_two_mul N hN
    have hU : 0 ≤ U := by dsimp [U]; positivity
    have hV : 0 ≤ V := by dsimp [V]; positivity
    have ha' : 0 ≤ a' := by dsimp [a', Kfac, a]; positivity
    have hq' : 0 ≤ q' := by dsimp [q', Kfac, q, a, C, B, R, D, j]; positivity
    have hr' : 0 ≤ r' := by dsimp [r', Kfac]; positivity
    have hbound := hdyadic N hN M hM
    have hrewrite :
        J * (a' * U + q' * V + r' * (M : ℝ)) + 2 =
          (Nat.log2 N : ℝ) *
            (Kfac * (a * X * Real.log (2 * (M : ℝ)) / (M : ℝ) +
              q * X ^ (1 - α) * Real.sqrt (Real.log (2 * (M : ℝ))) +
              (M : ℝ))) + 2 := by
      dsimp [J, a', q', r', U, V]
      ring
    have hscaled := dyadic_log_absorption
      (N := X) (M := (M : ℝ)) (J := J) (U := U) (V := V)
      (a := a') (q := q') (r := r') hNreal hMreal hJ hU hV ha' hq' hr'
    calc
      (∑ n ∈ realIntegerInterval 0 (N : ℝ),
          floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤
        (Nat.log2 N : ℝ) *
          (Kfac * (a * X * Real.log (2 * (M : ℝ)) / (M : ℝ) +
            q * X ^ (1 - α) * Real.sqrt (Real.log (2 * (M : ℝ))) +
            (M : ℝ))) + 2 := by
              simpa [Kfac, X, a, q, C, B, R, D, α, j] using hbound
      _ = J * (a' * U + q' * V + r' * (M : ℝ)) + 2 := hrewrite.symm
      _ ≤ Cc * Real.log (2 * X) * (U + V + (M : ℝ)) := by
        simpa [Cc, a', q', r', Kfac, X] using hscaled
      _ = Cc * Real.log (2 * (N : ℝ)) *
          ((N : ℝ) * Real.log (2 * (M : ℝ)) / (M : ℝ) +
            (N : ℝ) ^ (1 - α) *
              Real.sqrt (Real.log (2 * (M : ℝ))) + (M : ℝ)) := by
        simp [X, U, V]

/-- Natural-index form of the manuscript's all-truncation estimate. -/
theorem exists_boundaryKernel_monomial_all_truncation_bound_nat {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil (4 * c) + 2
    let D : ℝ := (2 : ℝ) ^ j
    let α : ℝ := 1 / (8 * (j : ℝ) * D)
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let B : ℝ := |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ))
    let C : ℝ := 11 * max (R ^ (2 / D))
      (max ((R ^ 2) ^ (1 / (D - 2))) (B ^ (-2 / D)))
    let a : ℝ := 2 * (1 + (Real.log 4)⁻¹)
    let q : ℝ := 2 * (max 2 C) * (5 * a + 2)
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ N : ℕ, 2 ≤ N → ∀ M : ℕ,
      ∀ hM : 2 ≤ M,
      (∑ n ∈ Finset.Icc 1 N,
        floorBoundaryKernel M hM ((n : ℝ) ^ c)) ≤
      Cc * Real.log (2 * (N : ℝ)) *
        ((N : ℝ) * Real.log (2 * (M : ℝ)) / (M : ℝ) +
          (N : ℝ) ^ (1 - α) *
            Real.sqrt (Real.log (2 * (M : ℝ))) + (M : ℝ)) := by
  dsimp only
  obtain ⟨Cc, hCc, hall⟩ :=
    exists_boundaryKernel_monomial_all_truncation_bound hc hcNon
  refine ⟨Cc, hCc, ?_⟩
  intro N hN M hM
  have hsum := sum_realIntegerInterval_zero_eq_nat_Icc N
    (fun n => floorBoundaryKernel M hM ((n : ℝ) ^ c))
  have hsum' :
      (∑ z ∈ realIntegerInterval 0 (N : ℝ),
        floorBoundaryKernel M hM ((z : ℝ) ^ c)) =
      ∑ n ∈ Finset.Icc 1 N,
        floorBoundaryKernel M hM ((n : ℝ) ^ c) := by simpa using hsum
  rw [← hsum']
  exact hall N hN M hM

/-- The fixed choices of `κ`, `εd`, and `η` provide the strict savings
relations required when absorbing the three derivative-test terms. -/
theorem monomial_fixed_parameter_savings
    {c : ℝ} {j : ℕ} (hc : 1 < c)
    (hgapLower : 2 < (j : ℝ) - c)
    (hgapUpper : (j : ℝ) - c < 3) :
    let a : ℝ := 1 / 100
    let κ : ℝ := a / (10 * (j : ℝ))
    let εd : ℝ := a / (100 * (j : ℝ))
    let D : ℝ := (2 : ℝ) ^ (j : ℝ)
    let η : ℝ := a / (100 * (j : ℝ) * D)
    κ = 10 * D * η ∧ 16 * η < κ ∧ 16 * η < 1 - εd := by
  dsimp only
  have hj3 : 3 < (j : ℝ) := by linarith [hc, hgapLower]
  have hj1 : 1 ≤ (j : ℝ) := by linarith
  have hD : 4 ≤ (2 : ℝ) ^ (j : ℝ) := by
    calc
      4 = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (j : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hκpos : 0 < (1 / 100 : ℝ) / (10 * (j : ℝ)) := by positivity
  have hκsmall : (1 / 100 : ℝ) / (10 * (j : ℝ)) < 1 / 1000 := by
    rw [div_lt_iff₀ (by positivity : 0 < 10 * (j : ℝ))]
    norm_num
    nlinarith
  have hεsmall : (1 / 100 : ℝ) / (100 * (j : ℝ)) < 1 / 1000 := by
    rw [div_lt_iff₀ (by positivity : 0 < 100 * (j : ℝ))]
    norm_num
    nlinarith
  have hηpos : 0 < (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ)) := by positivity
  have hrelation :
      (1 / 100 : ℝ) / (10 * (j : ℝ)) =
        10 * (2 : ℝ) ^ (j : ℝ) *
          ((1 / 100 : ℝ) / (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))) := by
    field_simp
    <;> ring
  have hηκ : 16 * ((1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))) <
        (1 / 100 : ℝ) / (10 * (j : ℝ)) := by
    rw [hrelation]
    nlinarith [hD, hηpos]
  refine ⟨hrelation, hηκ, ?_⟩
  nlinarith [hηκ, hκsmall, hεsmall]

/-- The three decay exponents in the derivative-test majorant are strictly
larger than the target saving `16η`. -/
theorem monomial_fixed_parameter_term_savings
    {c : ℝ} {j : ℕ} (hc : 1 < c)
    (hgapLower : 2 < (j : ℝ) - c)
    (hgapUpper : (j : ℝ) - c < 3) :
    let a : ℝ := 1 / 100
    let κ : ℝ := a / (10 * (j : ℝ))
    let D : ℝ := (2 : ℝ) ^ (j : ℝ)
    let η : ℝ := a / (100 * (j : ℝ) * D)
    16 * η < 9 / (5 * D) ∧
      16 * η < 1 / (D - 2) ∧
      16 * η < 8 * a / (5 * D) := by
  dsimp only
  have hs := monomial_fixed_parameter_savings hc hgapLower hgapUpper
  dsimp only at hs
  rcases hs with ⟨hrelation, hηκ, _⟩
  have hD : 4 ≤ (2 : ℝ) ^ (j : ℝ) := by
    have hj : 2 ≤ (j : ℝ) := by linarith [hc, hgapLower]
    calc
      4 = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (j : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hj
  have hκsmall : (1 / 100 : ℝ) / (10 * (j : ℝ)) < 1 / 1000 := by
    have hj : 3 < (j : ℝ) := by linarith [hc, hgapLower]
    rw [div_lt_iff₀ (by positivity : 0 < 10 * (j : ℝ))]
    norm_num
    nlinarith
  have hDpos : 0 < (2 : ℝ) ^ (j : ℝ) := by positivity
  have hjpos : 0 < (j : ℝ) := by linarith [hc, hgapLower]
  have hηpos : 0 < (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ)) := by positivity
  have hDη : (2 : ℝ) ^ (j : ℝ) *
      ((1 / 100 : ℝ) / (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))) =
        ((1 / 100 : ℝ) / (10 * (j : ℝ))) / 10 := by
    rw [hrelation]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity : 0 < 5 * (2 : ℝ) ^ (j : ℝ))]
    nlinarith [hDη, hκsmall]
  · rw [lt_div_iff₀ (by linarith : 0 < (2 : ℝ) ^ (j : ℝ) - 2)]
    nlinarith [hDη, hηpos, hκsmall, hD]
  · rw [lt_div_iff₀ (by positivity : 0 < 5 * (2 : ℝ) ^ (j : ℝ))]
    nlinarith [hDη, hκsmall]

/-- The retained-block power exponent left after the divisor cutoff remains
strictly positive for the blueprint's fixed parameters. -/
theorem monomial_fixed_parameter_block_exponent_pos
    {c : ℝ} {j : ℕ} (hc : 1 < c)
    (hgapLower : 2 < (j : ℝ) - c) :
    let a : ℝ := 1 / 100
    let κ : ℝ := a / (10 * (j : ℝ))
    let εd : ℝ := a / (100 * (j : ℝ))
    0 < 1 / 10 - κ - εd := by
  dsimp only
  have hj : 3 < (j : ℝ) := by linarith [hc, hgapLower]
  have hκ : (1 / 100 : ℝ) / (10 * (j : ℝ)) < 1 / 1000 := by
    rw [div_lt_iff₀ (by positivity : 0 < 10 * (j : ℝ))]
    norm_num
    nlinarith
  have hεd : (1 / 100 : ℝ) / (100 * (j : ℝ)) < 1 / 1000 := by
    rw [div_lt_iff₀ (by positivity : 0 < 100 * (j : ℝ))]
    norm_num
    nlinarith
  nlinarith

/-- The divisor cutoff in `ar:monomial` is eventually bounded by the fixed
power `N^εd`. -/
theorem monomial_exp_log_three_tenths_le_power
    {N εd : ℝ} (hN : 1 < N) (hε : 0 < εd)
    (hlarge : 1 / εd ≤ (Real.log N) ^ (7 / 10 : ℝ)) :
    Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) ≤ N ^ εd := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hunit : 1 ≤ εd * (Real.log N) ^ (7 / 10 : ℝ) :=
    by simpa [mul_comm] using (div_le_iff₀ hε).mp hlarge
  have hpower : (Real.log N) ^ (3 / 10 : ℝ) ≤ εd * Real.log N := by
    calc
      (Real.log N) ^ (3 / 10 : ℝ) = 1 * (Real.log N) ^ (3 / 10 : ℝ) := by ring
      _ ≤ (εd * (Real.log N) ^ (7 / 10 : ℝ)) *
            (Real.log N) ^ (3 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right hunit (by positivity)
      _ = εd * Real.log N := by
        rw [mul_assoc]
        rw [← Real.rpow_add hlog]
        rw [show (7 / 10 : ℝ) + (3 / 10 : ℝ) = 1 by norm_num,
          Real.rpow_one]
  calc
    Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) ≤
        Real.exp (εd * Real.log N) := Real.exp_le_exp.mpr hpower
    _ = N ^ εd := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < N)]
      congr 1
      ring

/-- A single threshold makes the exponential divisor cutoff no larger than
`N^εd` for every later scale. -/
theorem exists_monomial_divisor_power_threshold {εd : ℝ} (hε : 0 < εd) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) ≤ N ^ εd := by
  have hlim :
      Filter.Tendsto (fun N : ℝ => (Real.log N) ^ (7 / 10 : ℝ))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).comp Real.tendsto_log_atTop
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp hlim (1 / εd)
  refine ⟨max B 2, le_max_right _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hlarge : 1 / εd ≤ (Real.log N) ^ (7 / 10 : ℝ) := hB N (le_trans
    (le_max_left _ _) hN)
  exact monomial_exp_log_three_tenths_le_power
    (by linarith : 1 < N) hε hlarge

/-- Exact power simplification behind the upper derivative scale. -/
theorem monomial_scaled_rpow_factor_identity
    {N d c j κ : ℝ} (hN : 0 < N) (hd : 0 < d) :
    d ^ c * (N ^ (1 - κ) / d) ^ (c - j) =
      d ^ j * N ^ ((1 - κ) * (c - j)) := by
  rw [Real.div_rpow (by positivity : 0 ≤ N ^ (1 - κ)) (le_of_lt hd)]
  calc
    d ^ c * ((N ^ (1 - κ)) ^ (c - j) / d ^ (c - j)) =
        (d ^ c / d ^ (c - j)) * (N ^ (1 - κ)) ^ (c - j) := by ring
    _ = d ^ (c - (c - j)) * (N ^ (1 - κ)) ^ (c - j) := by
      rw [← Real.rpow_sub hd]
    _ = d ^ j * N ^ ((1 - κ) * (c - j)) := by
      rw [show c - (c - j) = j by ring, Real.rpow_mul (le_of_lt hN)]

/-- Exact combination of the derivative scale with the block length. -/
theorem monomial_dyadic_lambda_length_identity
    {d P c j : ℝ} (hd : 0 < d) (hP : 0 < P) :
    d ^ c * (2 * P) ^ (c - j) * P ^ j =
      (2 : ℝ) ^ (c - j) * (d * P) ^ c := by
  rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (le_of_lt hP)]
  calc
    d ^ c * ((2 : ℝ) ^ (c - j) * P ^ (c - j)) * P ^ j =
        (2 : ℝ) ^ (c - j) * (d ^ c * (P ^ (c - j) * P ^ j)) := by ring
    _ = (2 : ℝ) ^ (c - j) * (d ^ c * P ^ c) := by
      rw [← Real.rpow_add hP]
      congr 2
      ring_nf
    _ = (2 : ℝ) ^ (c - j) * (d * P) ^ c := by
      rw [← Real.mul_rpow (le_of_lt hd) (le_of_lt hP)]

/-- Upper derivative-scale bound under the uniform `N,d,β,P` conditions
used on the retained dyadic blocks. -/
theorem monomial_derivative_scale_upper_bound
    {N β c P d κ εd b : ℝ} {j : ℕ}
    (hN : 1 < N) (hcj : c < (j : ℝ))
    (hβ : |β| ≤ 2 * N ^ b)
    (hd0 : 1 ≤ d) (hd : d ≤ N ^ εd)
    (hP : N ^ (1 - κ) / (2 * d) ≤ P) :
    |β| * d ^ c * |(descPochhammer ℝ j).eval c| *
        (2 * P) ^ (c - j) ≤
      2 * |(descPochhammer ℝ j).eval c| *
        N ^ (b + (j : ℝ) * εd - ((j : ℝ) - c) * (1 - κ)) := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd0
  have hPscale : N ^ (1 - κ) ≤ P * (2 * d) :=
    (div_le_iff₀ (by positivity : 0 < 2 * d)).mp hP
  have hbase : 0 < N ^ (1 - κ) / d := by positivity
  have hscale : N ^ (1 - κ) / d ≤ 2 * P := by
    apply (div_le_iff₀ hdpos).2
    nlinarith [hPscale]
  have hq : c - (j : ℝ) ≤ 0 := by linarith
  have hpow : (2 * P) ^ (c - j) ≤ (N ^ (1 - κ) / d) ^ (c - j) :=
    Real.rpow_le_rpow_of_nonpos hbase hscale hq
  have hfactor := monomial_scaled_rpow_factor_identity
    (N := N) (d := d) (c := c) (j := (j : ℝ)) (κ := κ)
    (by linarith : 0 < N) hdpos
  have hdj : d ^ (j : ℝ) ≤ N ^ (εd * (j : ℝ)) := by
    calc
      d ^ (j : ℝ) ≤ (N ^ εd) ^ (j : ℝ) :=
        Real.rpow_le_rpow (le_of_lt hdpos) hd (by positivity)
      _ = N ^ (εd * (j : ℝ)) :=
        (Real.rpow_mul (le_of_lt (by linarith : 0 < N)) εd (j : ℝ)).symm
  have hleft : 0 ≤ |β| * |(descPochhammer ℝ j).eval c| := by positivity
  calc
    |β| * d ^ c * |(descPochhammer ℝ j).eval c| *
        (2 * P) ^ (c - j)
        = (|β| * |(descPochhammer ℝ j).eval c|) *
            (d ^ c * (2 * P) ^ (c - j)) := by ring
    _ ≤ (|β| * |(descPochhammer ℝ j).eval c|) *
          (d ^ c * (N ^ (1 - κ) / d) ^ (c - j)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    _ = |β| * |(descPochhammer ℝ j).eval c| *
          (d ^ (j : ℝ) * N ^ ((1 - κ) * (c - (j : ℝ)))) := by rw [hfactor]
    _ ≤ (2 * N ^ b) * |(descPochhammer ℝ j).eval c| *
          (N ^ (εd * (j : ℝ)) * N ^ ((1 - κ) * (c - (j : ℝ)))) := by
          gcongr
    _ = 2 * |(descPochhammer ℝ j).eval c| *
          N ^ (b + (j : ℝ) * εd - ((j : ℝ) - c) * (1 - κ)) := by
          calc
            (2 * N ^ b) * |(descPochhammer ℝ j).eval c| *
                (N ^ (εd * (j : ℝ)) * N ^ ((1 - κ) * (c - (j : ℝ))))
                = 2 * |(descPochhammer ℝ j).eval c| *
                    (N ^ b * N ^ (εd * (j : ℝ) + (1 - κ) * (c - (j : ℝ)))) := by
                      rw [← Real.rpow_add (by linarith : 0 < N)]
                      ring
            _ = 2 * |(descPochhammer ℝ j).eval c| *
                  N ^ (b + εd * (j : ℝ) + (1 - κ) * (c - (j : ℝ))) := by
                    rw [← Real.rpow_add (by linarith : 0 < N)]
                    ring_nf
            _ = 2 * |(descPochhammer ℝ j).eval c| *
                  N ^ (b + (j : ℝ) * εd - ((j : ℝ) - c) * (1 - κ)) := by
                    congr 2
                    ring

/-- Lower bound for the derivative scale times the length of its dyadic
block, under the lower frequency restriction from `ar:monomial`. -/
theorem monomial_derivative_scale_lower_times_length
    {N β c P d κ a : ℝ} {j : ℕ}
    (hN : 1 < N) (hc : 0 < c) (hβ : N ^ (a - c) ≤ |β|)
    (hd0 : 1 ≤ d) (hP : N ^ (1 - κ) / (2 * d) ≤ P) :
    |β| * d ^ c * |(descPochhammer ℝ j).eval c| *
        (2 * P) ^ (c - j) * P ^ j ≥
      |(descPochhammer ℝ j).eval c| *
        ((2 : ℝ) ^ (c - (j : ℝ)) / (2 : ℝ) ^ c) *
          N ^ (a - c * κ) := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd0
  have hPscale : N ^ (1 - κ) ≤ P * (2 * d) :=
    (div_le_iff₀ (by positivity : 0 < 2 * d)).mp hP
  have hDP : N ^ (1 - κ) / 2 ≤ d * P := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [hPscale]
  have hPpos : 0 < P := by
    have hpow : 0 < N ^ (1 - κ) := by positivity
    have hden : 0 < 2 * d := by positivity
    exact lt_of_lt_of_le (div_pos hpow hden) hP
  have hDPpow :
      (N ^ (1 - κ) / 2) ^ c ≤ (d * P) ^ c :=
    Real.rpow_le_rpow (by positivity) hDP (le_of_lt hc)
  have hlength := monomial_dyadic_lambda_length_identity
    (d := d) (P := P) (c := c) (j := (j : ℝ)) hdpos hPpos
  have hcoef : 0 ≤ |(descPochhammer ℝ j).eval c| := by positivity
  have hfactor : 0 < (2 : ℝ) ^ (c - (j : ℝ)) := by positivity
  have hbetaNonneg : 0 ≤ N ^ (a - c) := by positivity
  have hcombined :
      N ^ (a - c) * (N ^ (1 - κ) / 2) ^ c =
        (N ^ (a - c * κ)) / (2 : ℝ) ^ c := by
    rw [Real.div_rpow (by positivity : 0 ≤ N ^ (1 - κ)) (by norm_num)]
    rw [(Real.rpow_mul (le_of_lt (by linarith : 0 < N)) (1 - κ) c).symm]
    rw [← mul_div_assoc]
    rw [← Real.rpow_add (by linarith : 0 < N)]
    congr 1
    ring_nf
  calc
    |β| * d ^ c * |(descPochhammer ℝ j).eval c| *
        (2 * P) ^ (c - j) * P ^ j
        = |β| * |(descPochhammer ℝ j).eval c| *
            ((2 : ℝ) ^ (c - (j : ℝ)) * (d * P) ^ c) := by
          calc
            _ = (|β| * |(descPochhammer ℝ j).eval c|) *
                  (d ^ c * (2 * P) ^ (c - (j : ℝ)) * P ^ (j : ℝ)) := by
                    rw [(Real.rpow_natCast P j).symm]
                    ring_nf
            _ = _ := by rw [hlength]
    _ ≥ N ^ (a - c) * |(descPochhammer ℝ j).eval c| *
          ((2 : ℝ) ^ (c - (j : ℝ)) *
            (N ^ (1 - κ) / 2) ^ c) := by
          gcongr
    _ = |(descPochhammer ℝ j).eval c| *
          ((2 : ℝ) ^ (c - (j : ℝ)) *
            (N ^ (a - c * κ) / (2 : ℝ) ^ c)) := by
          calc
            _ = |(descPochhammer ℝ j).eval c| * (2 : ℝ) ^ (c - (j : ℝ)) *
                  (N ^ (a - c) * (N ^ (1 - κ) / 2) ^ c) := by ring
            _ = _ := by rw [hcombined]; ring
    _ = |(descPochhammer ℝ j).eval c| *
          ((2 : ℝ) ^ (c - (j : ℝ)) / (2 : ℝ) ^ c) *
            N ^ (a - c * κ) := by ring

/-- Threshold absorption of the positive coefficient in the lower derivative
scale, leaving the power `N^(4a/5)` used by the third test term. -/
theorem exists_monomial_lower_scale_absorption
    {c : ℝ} {j : ℕ} (hc : 1 < c) (hcNon : NonIntegral c)
    (hgapLower : 2 < (j : ℝ) - c) :
    let a : ℝ := 1 / 100
    let κ : ℝ := a / (10 * (j : ℝ))
    let Q : ℝ := |(descPochhammer ℝ j).eval c| *
      ((2 : ℝ) ^ (c - (j : ℝ)) / (2 : ℝ) ^ c)
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ d P β : ℝ,
      1 ≤ d → N ^ (a - c) ≤ |β| →
      N ^ (1 - κ) / (2 * d) ≤ P →
      |β| * d ^ c * |(descPochhammer ℝ j).eval c| *
        (2 * P) ^ (c - j) * P ^ j ≥ N ^ (4 * a / 5) := by
  let a : ℝ := 1 / 100
  let κ : ℝ := a / (10 * (j : ℝ))
  let Q : ℝ := |(descPochhammer ℝ j).eval c| *
    ((2 : ℝ) ^ (c - (j : ℝ)) / (2 : ℝ) ^ c)
  have hcκ : c * κ < a / 10 := by
    dsimp [a, κ]
    exact monomial_fixed_parameter_c_kappa_bound hc hgapLower
  have hs : 0 < a / 5 - c * κ := by
    dsimp [a]
    linarith
  have hCpos : 0 < |(descPochhammer ℝ j).eval c| :=
    abs_pos.mpr (descPochhammer_eval_ne_zero hcNon j)
  have hpowpos : 0 < (2 : ℝ) ^ (c - (j : ℝ)) := by positivity
  have hdenpos : 0 < (2 : ℝ) ^ c := by positivity
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact mul_pos hCpos (div_pos hpowpos hdenpos)
  obtain ⟨Nbase, _, hNQ⟩ :=
    exists_real_rpow_threshold (C := Q⁻¹) hs
  refine ⟨max 2 Nbase, le_max_left _ _, ?_⟩
  intro N hN d P β hd hβ hP
  have hNbase : Nbase ≤ N := le_trans (le_max_right _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hQinv : Q⁻¹ ≤ N ^ (a / 5 - c * κ) := by
    simpa [a, κ] using hNQ N hNbase
  have hQmul : 1 ≤ Q * N ^ (a / 5 - c * κ) := by
    calc
      1 = Q * Q⁻¹ := by rw [mul_inv_cancel₀ hQpos.ne']
      _ ≤ Q * N ^ (a / 5 - c * κ) :=
        mul_le_mul_of_nonneg_left hQinv (le_of_lt hQpos)
  have hpower : N ^ (a - c * κ) =
      N ^ (4 * a / 5) * N ^ (a / 5 - c * κ) := by
    rw [← Real.rpow_add (by linarith : 0 < N)]
    congr 1
    ring
  have hcombined : Q * N ^ (a - c * κ) ≥ N ^ (4 * a / 5) := by
    calc
      Q * N ^ (a - c * κ) =
          N ^ (4 * a / 5) * (Q * N ^ (a / 5 - c * κ)) := by
            rw [hpower]
            ring
      _ ≥ N ^ (4 * a / 5) :=
        by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hQmul
              (Real.rpow_nonneg (by linarith : 0 ≤ N) _)
  have hscale := monomial_derivative_scale_lower_times_length
    (N := N) (β := β) (c := c) (P := P) (d := d) (κ := κ)
    (a := a) (j := j) (by linarith : 1 < N) (by linarith : 0 < c)
    hβ hd hP
  have hmain :
      |β| * d ^ c * |(descPochhammer ℝ j).eval c| *
        (2 * P) ^ (c - j) * P ^ j ≥ N ^ (4 * a / 5) := by
    exact le_trans hcombined hscale
  simpa [a, κ, Q] using hmain

/-- The retained-block cutoff and divisor power bound imply a block that is
large enough relative to the fixed derivative-test ratio. -/
theorem monomial_retained_block_size_bound
    {N d P κ εd R : ℝ}
    (hN : 1 < N) (hdpos : 0 < d)
    (hd : d ≤ N ^ εd)
    (hP : N ^ (1 - κ) / (2 * d) ≤ P)
    (hR : 2 * R ≤ N ^ (1 / 10 - κ - εd)) :
    R * N ^ (9 / 10 : ℝ) ≤ P := by
  have hpowprod :
      N ^ (1 - κ - εd) * N ^ εd = N ^ (1 - κ) := by
    rw [← Real.rpow_add (by linarith : 0 < N)]
    congr 1
    ring
  have hmul : N ^ (1 - κ - εd) * d ≤ N ^ (1 - κ) := by
    calc
      N ^ (1 - κ - εd) * d ≤ N ^ (1 - κ - εd) * N ^ εd :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = N ^ (1 - κ) := hpowprod
  have hquot : N ^ (1 - κ - εd) / 2 ≤ N ^ (1 - κ) / (2 * d) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (by positivity : 0 < 2 * d)).2
    nlinarith [hmul]
  have hlow : N ^ (1 - κ - εd) / 2 ≤ P := hquot.trans hP
  have hpower :
      R * N ^ (9 / 10 : ℝ) ≤ N ^ (1 - κ - εd) / 2 := by
    have hmul :
        2 * R * N ^ (9 / 10 : ℝ) ≤
          N ^ (1 / 10 - κ - εd) * N ^ (9 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_right hR
        (Real.rpow_nonneg (le_of_lt (by linarith : 0 < N)) (9 / 10 : ℝ))
    have hsum :
        N ^ (1 / 10 - κ - εd) * N ^ (9 / 10 : ℝ) =
          N ^ (1 - κ - εd) := by
      rw [← Real.rpow_add (by linarith : 0 < N)]
      congr 1
      ring
    calc
      R * N ^ (9 / 10 : ℝ) = (2 * R * N ^ (9 / 10 : ℝ)) / 2 := by ring
      _ ≤ (N ^ (1 / 10 - κ - εd) * N ^ (9 / 10 : ℝ)) / 2 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      _ = N ^ (1 - κ - εd) / 2 := by rw [hsum]
  exact hpower.trans hlow

/-- A block lower bound with `R≥1` supplies the exact strict floor condition
required by the derivative test once `N^(9/10)≥j+1`. -/
theorem monomial_floor_condition_from_block_size
    {N P R : ℝ} {j : ℕ}
    (hN : 1 < N) (hR : 1 ≤ R)
    (hNpow : (j : ℝ) + 1 ≤ N ^ (9 / 10 : ℝ))
    (hP : R * N ^ (9 / 10 : ℝ) ≤ P) :
    (j : ℝ) < (Int.floor P : ℝ) := by
  have hpowpos : 0 < N ^ (9 / 10 : ℝ) := by positivity
  have hRpow : N ^ (9 / 10 : ℝ) ≤ R * N ^ (9 / 10 : ℝ) :=
    by simpa using mul_le_mul_of_nonneg_right hR (le_of_lt hpowpos)
  have hjP : (j : ℝ) + 1 ≤ P := hNpow.trans (hRpow.trans hP)
  have hj1P : ((j : ℤ) + 1 : ℤ) ≤ Int.floor P := by
    apply Int.le_floor.mpr
    exact_mod_cast hjP
  have hjfloor : (j : ℤ) < Int.floor P := by omega
  exact_mod_cast hjfloor

/-- The first term of the derivative-test majorant has the claimed saving
from the retained-block size bound. -/
theorem monomial_derivative_test_first_term_bound
    {N P R D η : ℝ}
    (hN : 1 ≤ N) (hD : 0 < D) (hη : 0 ≤ η)
    (hP : 0 < P) (hR : 0 ≤ R)
    (hblock : R * N ^ (9 / 10 : ℝ) ≤ P)
    (hsaving : 16 * η < 9 / (5 * D)) :
    (R / P) ^ (2 / D) ≤ N ^ (-16 * η) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hscaleInv : N ^ (9 / 10 : ℝ) * N ^ (-(9 / 10 : ℝ)) = 1 := by
    rw [← Real.rpow_add hNpos]
    rw [show (9 / 10 : ℝ) + -(9 / 10 : ℝ) = 0 by ring, Real.rpow_zero]
  have hquot : R / P ≤ N ^ (-(9 / 10 : ℝ)) := by
    apply (div_le_iff₀ hP).2
    calc
      R = R * (N ^ (9 / 10 : ℝ) * N ^ (-(9 / 10 : ℝ))) := by rw [hscaleInv, mul_one]
      _ = (R * N ^ (9 / 10 : ℝ)) * N ^ (-(9 / 10 : ℝ)) := by ring
      _ ≤ N ^ (-(9 / 10 : ℝ)) * P := by
        calc
          _ ≤ P * N ^ (-(9 / 10 : ℝ)) :=
            mul_le_mul_of_nonneg_right hblock
              (Real.rpow_nonneg (le_of_lt hNpos) (-(9 / 10 : ℝ)))
          _ = _ := by ring
  have hterm := Real.rpow_le_rpow (by positivity) hquot
    (by positivity : 0 ≤ (2 : ℝ) / D)
  have hid : (N ^ (-(9 / 10 : ℝ))) ^ ((2 : ℝ) / D) =
      N ^ (-9 / (5 * D)) := by
    rw [(Real.rpow_mul (le_of_lt hNpos) (-(9 / 10 : ℝ)) ((2 : ℝ) / D)).symm]
    congr 1
    ring
  have hexp : -9 / (5 * D) ≤ -16 * η := by
    have hneg := neg_lt_neg hsaving
    simpa only [neg_div, neg_mul] using le_of_lt hneg
  calc
    (R / P) ^ (2 / D) ≤ (N ^ (-(9 / 10 : ℝ))) ^ ((2 : ℝ) / D) := hterm
    _ = N ^ (-9 / (5 * D)) := hid
    _ ≤ N ^ (-16 * η) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hexp

/-- The second derivative-test term has the claimed saving once its base is
bounded by `N⁻¹`. -/
theorem monomial_derivative_test_second_term_bound
    {N R lam D η : ℝ}
    (hN : 1 ≤ N) (hD : 2 < D) (hη : 0 ≤ η)
    (hbase0 : 0 ≤ R ^ 2 * lam)
    (hbase : R ^ 2 * lam ≤ N ^ (-1 : ℝ))
    (hsaving : 16 * η < 1 / (D - 2)) :
    (R ^ 2 * lam) ^ (1 / (D - 2)) ≤ N ^ (-16 * η) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hexpBase : 0 < 1 / (D - 2) := by positivity
  have hterm := Real.rpow_le_rpow hbase0 hbase hexpBase.le
  have hid : (N ^ (-1 : ℝ)) ^ (1 / (D - 2)) =
      N ^ (-1 / (D - 2)) := by
    rw [(Real.rpow_mul (le_of_lt hNpos) (-1 : ℝ) (1 / (D - 2))).symm]
    congr 1
    ring
  have hexp : -1 / (D - 2) ≤ -16 * η := by
    have hneg := neg_lt_neg hsaving
    simpa only [neg_div, neg_mul] using le_of_lt hneg
  calc
    (R ^ 2 * lam) ^ (1 / (D - 2)) ≤
        (N ^ (-1 : ℝ)) ^ (1 / (D - 2)) := hterm
    _ = N ^ (-1 / (D - 2)) := hid
    _ ≤ N ^ (-16 * η) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hexp

/-- The third derivative-test term has the claimed saving once its scale is
bounded below by `N^(4a/5)`. -/
theorem monomial_derivative_test_third_term_bound
    {N X D η a : ℝ}
    (hN : 1 ≤ N) (hD : 0 < D) (hη : 0 ≤ η) (ha : 0 < a)
    (hX : N ^ (4 * a / 5) ≤ X)
    (hsaving : 16 * η < 8 * a / (5 * D)) :
    X ^ (-(2 / D)) ≤ N ^ (-16 * η) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hbasepos : 0 < N ^ (4 * a / 5) := by positivity
  have hnegative : -(2 / D) ≤ 0 := neg_nonpos.mpr (by positivity)
  have hmono := Real.rpow_le_rpow_of_nonpos hbasepos hX hnegative
  have hid : (N ^ (4 * a / 5)) ^ (-(2 / D)) =
      N ^ (-(8 * a / (5 * D))) := by
    rw [(Real.rpow_mul (le_of_lt hNpos) (4 * a / 5) (-(2 / D))).symm]
    congr 1
    ring
  have hexp : -(8 * a / (5 * D)) ≤ -16 * η := by
    have hneg := neg_lt_neg hsaving
    simpa only [neg_div, neg_mul] using le_of_lt hneg
  calc
    X ^ (-(2 / D)) ≤ (N ^ (4 * a / 5)) ^ (-(2 / D)) := hmono
    _ = N ^ (-(8 * a / (5 * D))) := hid
    _ ≤ N ^ (-16 * η) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hexp

/-- For a positive dilating factor, the modulus of the dilated frequency
coefficient factors exactly as used in the derivative-test scale. -/
theorem abs_mul_rpow_dilation {β d c : ℝ} (hd : 0 < d) :
    |β * d ^ c| = |β| * d ^ c := by
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hd c)]

/-- Combine the three numerical bounds with the derivative test on one
retained dilated-monomial block. -/
theorem monomial_retained_dilated_block_bound
    {N P β c η : ℝ} {d j : ℕ}
    (hN : 1 ≤ N) (hβ : β ≠ 0) (hc : NonIntegral c)
    (hP : 0 < P) (hd : 0 < d) (hj : 3 ≤ j) (hcj : c < (j : ℝ))
    (hfloor : (j : ℝ) < (Int.floor P : ℝ))
    (hη : 0 ≤ η)
    (hsaving₁ : 16 * η < 9 / (5 * (2 : ℝ) ^ (j : ℝ)))
    (hsaving₂ : 16 * η < 1 / ((2 : ℝ) ^ (j : ℝ) - 2))
    (hsaving₃ : 16 * η < 8 * (1 / 100 : ℝ) /
      (5 * (2 : ℝ) ^ (j : ℝ)))
    (hblock : 2 ^ ((j : ℝ) - c) * N ^ (9 / 10 : ℝ) ≤ P)
    (hupper : (2 ^ ((j : ℝ) - c)) ^ 2 *
      (|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
        (2 * P) ^ (c - j)) ≤ N ^ (-1 : ℝ))
    (hlower : N ^ (4 * (1 / 100 : ℝ) / 5) ≤
      (|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
        (2 * P) ^ (c - j)) * P ^ j) :
    ‖∑ n ∈ realIntegerInterval P P,
      realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ / P ≤
      11 * N ^ (-16 * η) := by
  let R : ℝ := 2 ^ ((j : ℝ) - c)
  let D : ℝ := (2 : ℝ) ^ (j : ℝ)
  let lam : ℝ := |β * (d : ℝ) ^ c| *
    |(descPochhammer ℝ j).eval c| * (2 * P) ^ (c - j)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hjreal : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hDtwo : 2 < D := by
    dsimp [D]
    calc
      2 = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ < (2 : ℝ) ^ (j : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hlampos : 0 < lam := by
    dsimp [lam]
    apply mul_pos
    · apply mul_pos
      · exact abs_pos.mpr (mul_ne_zero hβ
          (ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hd) c)))
      · exact abs_pos.mpr (descPochhammer_eval_ne_zero hc j)
    · exact Real.rpow_pos_of_pos (by linarith : 0 < 2 * P) (c - j)
  have hterm₁ := monomial_derivative_test_first_term_bound
    (N := N) (P := P) (R := R) (D := D) (η := η)
    hN hDpos hη hP (le_of_lt hRpos)
    (by simpa [R] using hblock) (by simpa [D] using hsaving₁)
  have hterm₂ := monomial_derivative_test_second_term_bound
    (N := N) (R := R) (lam := lam) (D := D) (η := η)
    hN hDtwo hη (by positivity)
    (by simpa [R, lam] using hupper) (by simpa [D] using hsaving₂)
  have hterm₃ := monomial_derivative_test_third_term_bound
    (N := N) (X := lam * P ^ j) (D := D) (η := η)
    (a := (1 / 100 : ℝ)) hN hDpos hη (by norm_num)
    (by simpa [lam] using hlower) (by simpa [D] using hsaving₃)
  have htest := dilatedRealMonomial_dyadic_phase_sum_bound
    hβ hc hP hd hj hcj hfloor
  have hmax : max ((R / P) ^ (2 / D))
      (max ((R ^ 2 * lam) ^ (1 / (D - 2)))
        ((lam * P ^ j) ^ (-(2 / D)))) ≤ N ^ (-16 * η) := by
    exact max_le hterm₁ (max_le hterm₂ hterm₃)
  have hmaxActual : max ((2 ^ ((j : ℝ) - c) / P) ^
      (2 / (2 : ℝ) ^ j))
      (max (((2 ^ ((j : ℝ) - c)) ^ 2 *
        (|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
          (2 * P) ^ (c - j))) ^ (1 / ((2 : ℝ) ^ j - 2)))
        (((|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
          (2 * P) ^ (c - j)) * P ^ j) ^ (-2 / (2 : ℝ) ^ j))) ≤
      N ^ (-16 * η) := by
    apply max_le
    · simpa [R, D] using hterm₁
    · apply max_le
      · simpa [R, D, lam] using hterm₂
      · simpa [D, lam, neg_div] using hterm₃
  calc
    _ ≤ 11 * max ((2 ^ ((j : ℝ) - c) / P) ^
        (2 / (2 : ℝ) ^ j))
        (max (((2 ^ ((j : ℝ) - c)) ^ 2 *
          (|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
            (2 * P) ^ (c - j))) ^ (1 / ((2 : ℝ) ^ j - 2)))
          (((|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
            (2 * P) ^ (c - j)) * P ^ j) ^ (-2 / (2 : ℝ) ^ j))) := htest
    _ ≤ 11 * N ^ (-16 * η) := by
      exact mul_le_mul_of_nonneg_left hmaxActual (by norm_num)

/-- Threshold absorption of the upper derivative scale, including the fixed
`R²` factor in the second derivative-test term. -/
theorem exists_monomial_upper_scale_absorption
    {c : ℝ} {j : ℕ} (hc : 1 < c)
    (hgapLower : 2 < (j : ℝ) - c)
    (hgapUpper : (j : ℝ) - c < 3) :
    let κ : ℝ := (1 / 100 : ℝ) / (10 * (j : ℝ))
    let εd : ℝ := (1 / 100 : ℝ) / (100 * (j : ℝ))
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    let C : ℝ := |(descPochhammer ℝ j).eval c|
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ d P β : ℝ,
      1 ≤ d → d ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      N ^ (1 - κ) / (2 * d) ≤ P → |β| ≤ 2 * N ^ (1 / 10000 : ℝ) →
      R ^ 2 * (|β| * d ^ c * C * (2 * P) ^ (c - j)) ≤ N ^ (-1 : ℝ) := by
  let κ : ℝ := (1 / 100 : ℝ) / (10 * (j : ℝ))
  let εd : ℝ := (1 / 100 : ℝ) / (100 * (j : ℝ))
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  let C : ℝ := |(descPochhammer ℝ j).eval c|
  let A : ℝ := 2 * C * R ^ 2
  have hjpos : 0 < (j : ℝ) := by linarith [hc, hgapLower]
  have hepspos : 0 < εd := by dsimp [εd]; positivity
  have hdiv := exists_monomial_divisor_power_threshold hepspos
  obtain ⟨Nd, hNd, hNdiv⟩ := hdiv
  obtain ⟨Na, hNa, hNabs⟩ :=
    exists_real_rpow_threshold (C := A) (by norm_num : 0 < (9 / 10 : ℝ))
  have hE := monomial_fixed_parameter_upper_exponent hc hgapLower hgapUpper
  dsimp only at hE
  have hEbound :
      (1 / 10000 : ℝ) + (j : ℝ) * εd - ((j : ℝ) - c) * (1 - κ) ≤ -19 / 10 :=
    le_of_lt (by simpa [κ, εd] using hE)
  let N₀ : ℝ := max 2 (max Nd Na)
  refine ⟨N₀, ?_, ?_⟩
  · dsimp [N₀]
    exact le_max_left _ _
  · intro N hN d P β hd0 hdcut hP hβ
    have hInner : max Nd Na ≤ N₀ := by dsimp [N₀]; exact le_max_right _ _
    have hNd' : Nd ≤ N := le_trans (le_max_left _ _) (le_trans hInner hN)
    have hNa' : Na ≤ N := le_trans (le_max_right _ _) (le_trans hInner hN)
    have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
    have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd0
    have hdivisor : d ≤ N ^ εd := le_trans hdcut (hNdiv N hNd')
    have hAbsorb : A ≤ N ^ (9 / 10 : ℝ) := hNabs N hNa'
    have hscale := monomial_derivative_scale_upper_bound
      (N := N) (β := β) (c := c) (P := P) (d := d) (j := j)
      (κ := κ) (εd := εd) (b := (1 / 10000 : ℝ))
      (by linarith : 1 < N) (by linarith [hgapLower])
      hβ hd0 hdivisor hP
    have hNpos : 0 < N := by linarith
    have hpow : N ^ ((1 / 10000 : ℝ) + (j : ℝ) * εd -
        ((j : ℝ) - c) * (1 - κ)) ≤ N ^ (-19 / 10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) hEbound
    have hLam :
        |β| * d ^ c * C * (2 * P) ^ (c - j) ≤ 2 * C * N ^ (-19 / 10 : ℝ) :=
      hscale.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hbase :
        R ^ 2 * (|β| * d ^ c * C * (2 * P) ^ (c - j)) ≤ N ^ (-1 : ℝ) := by
      calc
        R ^ 2 * (|β| * d ^ c * C * (2 * P) ^ (c - j)) ≤
            R ^ 2 * (2 * C * N ^ (-19 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_left hLam (by positivity)
        _ = A * N ^ (-19 / 10 : ℝ) := by dsimp [A]; ring
        _ ≤ N ^ (9 / 10 : ℝ) * N ^ (-19 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_right hAbsorb (Real.rpow_nonneg (le_of_lt hNpos) _)
        _ = N ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
    simpa [κ, εd, R, C] using hbase

/-- A single scale threshold makes every retained dyadic block large enough
for the derivative test, uniformly over the permitted divisor cutoff. -/
theorem exists_monomial_retained_block_threshold
    {c : ℝ} {j : ℕ} (hc : 1 < c)
    (hgapLower : 2 < (j : ℝ) - c) :
    let κ : ℝ := (1 / 100 : ℝ) / (10 * (j : ℝ))
    let εd : ℝ := (1 / 100 : ℝ) / (100 * (j : ℝ))
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ d P : ℝ,
      0 < d → d ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      N ^ (1 - κ) / (2 * d) ≤ P → R * N ^ (9 / 10 : ℝ) ≤ P := by
  let κ : ℝ := (1 / 100 : ℝ) / (10 * (j : ℝ))
  let εd : ℝ := (1 / 100 : ℝ) / (100 * (j : ℝ))
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  have hjpos : 0 < (j : ℝ) := by linarith [hc, hgapLower]
  have hepspos : 0 < εd := by dsimp [εd]; positivity
  have hdiv := exists_monomial_divisor_power_threshold hepspos
  obtain ⟨Nd, hNd, hNdiv⟩ := hdiv
  have hspos : 0 < 1 / 10 - κ - εd := by
    simpa [κ, εd] using monomial_fixed_parameter_block_exponent_pos hc hgapLower
  obtain ⟨Nr, hNr, hNrpow⟩ :=
    exists_real_rpow_threshold (C := 2 * R) hspos
  let N₀ : ℝ := max 2 (max Nd Nr)
  refine ⟨N₀, ?_, ?_⟩
  · dsimp [N₀]
    exact le_max_left _ _
  · intro N hN d P hdpos hdcut hP
    have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
    have hInner : max Nd Nr ≤ N₀ := by dsimp [N₀]; exact le_max_right _ _
    have hNd : Nd ≤ N :=
      le_trans (le_max_left _ _) (le_trans hInner hN)
    have hNr : Nr ≤ N :=
      le_trans (le_max_right _ _) (le_trans hInner hN)
    have hdivisor : d ≤ N ^ εd := le_trans hdcut (hNdiv N hNd)
    have hRabs : 2 * R ≤ N ^ (1 / 10 - κ - εd) := hNrpow N hNr
    have hblock := monomial_retained_block_size_bound
      (N := N) (d := d) (P := P) (κ := κ) (εd := εd) (R := R)
      (by linarith : 1 < N) hdpos hdivisor hP hRabs
    simpa [κ, εd, R] using hblock

/-- The retained-block threshold can be enlarged so every permitted block
also satisfies the derivative test's strict floor condition. -/
theorem exists_monomial_derivative_floor_threshold
    {c : ℝ} {j : ℕ} (hc : 1 < c)
    (hgapLower : 2 < (j : ℝ) - c) :
    let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ d P : ℝ,
      0 < d → d ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      N ^ (1 - (1 / 100 : ℝ) / (10 * (j : ℝ))) / (2 * d) ≤ P →
      (j : ℝ) < (Int.floor P : ℝ) := by
  let R : ℝ := (2 : ℝ) ^ ((j : ℝ) - c)
  have hR : 1 ≤ R := by
    dsimp [R]
    apply Real.one_le_rpow (by norm_num)
    linarith
  obtain ⟨Nb, hNb, hblock⟩ :=
    exists_monomial_retained_block_threshold hc hgapLower
  obtain ⟨Nf, hNf, hNfpow⟩ := exists_real_rpow_threshold
    (C := (j : ℝ) + 1) (by norm_num : 0 < (9 / 10 : ℝ))
  let N₀ : ℝ := max 2 (max Nb Nf)
  refine ⟨N₀, ?_, ?_⟩
  · dsimp [N₀]
    exact le_max_left _ _
  · intro N hN d P hdpos hdcut hP
    have hInner : max Nb Nf ≤ N₀ := by dsimp [N₀]; exact le_max_right _ _
    have hNb' : Nb ≤ N := le_trans (le_max_left _ _) (le_trans hInner hN)
    have hNf' : Nf ≤ N := le_trans (le_max_right _ _) (le_trans hInner hN)
    have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
    have hlarge : (j : ℝ) + 1 ≤ N ^ (9 / 10 : ℝ) := hNfpow N hNf'
    have hPblock : R * N ^ (9 / 10 : ℝ) ≤ P := hblock N hNb' d P hdpos hdcut hP
    exact monomial_floor_condition_from_block_size
      (by linarith : 1 < N) hR hlarge hPblock

/-- The paper's derivative order `j_c=ceil(c)+2` lies strictly between the
two required gaps when `c` is nonintegral. -/
theorem monomial_fixed_order_gap
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    2 < (j : ℝ) - c ∧ (j : ℝ) - c < 3 := by
  let j : ℕ := Nat.ceil c + 2
  have hcpos : 0 < c := by linarith
  have hceille : c ≤ (Nat.ceil c : ℝ) := Nat.le_ceil c
  have hceillt : (Nat.ceil c : ℝ) < c + 1 := Nat.ceil_lt_add_one hcpos.le
  have hcast : (Nat.ceil c : ℝ) = (Int.ceil c : ℝ) := by
    exact_mod_cast Int.natCast_ceil_eq_ceil hcpos.le
  have hceilne : c ≠ (Nat.ceil c : ℝ) := by
    intro heq
    apply hcNon (Int.ceil c)
    rw [← hcast]
    exact heq
  have hceilstrict : c < (Nat.ceil c : ℝ) := lt_of_le_of_ne hceille hceilne
  dsimp [j]
  push_cast
  constructor <;> linarith

/-- A common scale threshold makes every permitted retained dyadic block
satisfy the inputs of the derivative-test block estimate. -/
theorem exists_monomial_retained_block_phase_threshold
    {c : ℝ} {j : ℕ} (hc : 1 < c) (hcNon : NonIntegral c)
    (hgapLower : 2 < (j : ℝ) - c)
    (hgapUpper : (j : ℝ) - c < 3) :
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, ∀ P β : ℝ,
        1 ≤ d → d ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
        N ^ ((1 / 100 : ℝ) - c) ≤ |β| →
        |β| ≤ 2 * N ^ (1 / 10000 : ℝ) →
        N ^ (1 - (1 / 100 : ℝ) / (10 * (j : ℝ))) /
          (2 * (d : ℝ)) ≤ P →
        ‖∑ n ∈ realIntegerInterval P P,
          realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ / P ≤
          11 * N ^ (-16 * η) := by
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  obtain ⟨Nu, hNu, hupper⟩ :=
    exists_monomial_upper_scale_absorption hc hgapLower hgapUpper
  obtain ⟨Nl, hNl, hlower⟩ :=
    exists_monomial_lower_scale_absorption hc hcNon hgapLower
  obtain ⟨Nr, hNr, hretained⟩ :=
    exists_monomial_retained_block_threshold hc hgapLower
  obtain ⟨Nf, hNf, hfloor⟩ :=
    exists_monomial_derivative_floor_threshold hc hgapLower
  have hs := monomial_fixed_parameter_term_savings hc hgapLower hgapUpper
  dsimp only at hs
  rcases hs with ⟨hsaving₁, hsaving₂, hsaving₃⟩
  have hηpos : 0 ≤ η := by dsimp [η]; positivity
  have hηsav₁ : 16 * η < 9 /
      (5 * (2 : ℝ) ^ (j : ℝ)) := by simpa [η] using hsaving₁
  have hηsav₂ : 16 * η < 1 /
      ((2 : ℝ) ^ (j : ℝ) - 2) := by simpa [η] using hsaving₂
  have hηsav₃ : 16 * η < 8 * (1 / 100 : ℝ) /
      (5 * (2 : ℝ) ^ (j : ℝ)) := by simpa [η] using hsaving₃
  let N₀ : ℝ := max 2 (max Nu (max Nl (max Nr Nf)))
  refine ⟨N₀, ?_, ?_⟩
  · dsimp [N₀]
    exact le_max_left _ _
  · intro N hN d P β hd hdcut hβlower hβupper hP
    have hInner : max Nu (max Nl (max Nr Nf)) ≤ N₀ := by
      dsimp [N₀]
      exact le_max_right _ _
    have hNuN : Nu ≤ N :=
      le_trans (le_max_left _ _) (le_trans hInner hN)
    have hSubL : max Nl (max Nr Nf) ≤ max Nu (max Nl (max Nr Nf)) :=
      le_max_right _ _
    have hNlN : Nl ≤ N :=
      le_trans (le_max_left _ _) (le_trans hSubL (le_trans hInner hN))
    have hSubR : max Nr Nf ≤ max Nl (max Nr Nf) := le_max_right _ _
    have hNrN : Nr ≤ N :=
      le_trans (le_max_left _ _) (le_trans hSubR (le_trans hSubL (le_trans hInner hN)))
    have hNfN : Nf ≤ N :=
      le_trans (le_max_right _ _)
        (le_trans hSubR (le_trans hSubL (le_trans hInner hN)))
    have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
    have hdreal : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdreal
    have hcut : (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) := hdcut
    have hPbound : N ^ (1 - (1 / 100 : ℝ) / (10 * (j : ℝ))) /
        (2 * (d : ℝ)) ≤ P := hP
    have hU := hupper N hNuN (d : ℝ) P β hdreal hcut hPbound hβupper
    have hL := hlower N hNlN (d : ℝ) P β hdreal hβlower hPbound
    have hB := hretained N hNrN (d : ℝ) P hdpos hcut hPbound
    have hF := hfloor N hNfN (d : ℝ) P hdpos hcut hPbound
    have hcoeff : |β * (d : ℝ) ^ c| = |β| * (d : ℝ) ^ c :=
      abs_mul_rpow_dilation hdpos
    have hU' : ((2 : ℝ) ^ ((j : ℝ) - c)) ^ 2 *
        (|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
          (2 * P) ^ (c - j)) ≤ N ^ (-1 : ℝ) := by
      rw [hcoeff]
      simpa [show (2 : ℝ) ^ ((j : ℝ) - c) =
          (2 : ℝ) ^ ((j : ℝ) - c) by rfl] using hU
    have hL' : N ^ (4 * (1 / 100 : ℝ) / 5) ≤
        (|β * (d : ℝ) ^ c| * |(descPochhammer ℝ j).eval c| *
          (2 * P) ^ (c - j)) * P ^ j := by
      rw [hcoeff]
      simpa using hL
    have hηeq : η = (1 / 100 : ℝ) /
        (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ)) := rfl
    have hNle : 1 ≤ N := le_trans (by norm_num : (1 : ℝ) ≤ 2) hN2
    have hβnon : β ≠ 0 := by
      intro hzero
      have hpow : 0 < N ^ ((1 / 100 : ℝ) - c) := by positivity
      rw [hzero, abs_zero] at hβlower
      linarith
    have hPpos : 0 < P := by
      have hbase : 0 <
          N ^ (1 - (1 / 100 : ℝ) / (10 * (j : ℝ))) /
            (2 * (d : ℝ)) := by positivity
      exact lt_of_lt_of_le hbase hP
    exact monomial_retained_dilated_block_bound
      hNle hβnon hcNon hPpos hd
      (by exact_mod_cast (show (3 : ℝ) ≤ (j : ℝ) by linarith [hc, hgapLower]))
      (by linarith [hc, hgapLower]) hF hηpos hηsav₁ hηsav₂ hηsav₃
      (by simpa using hB) hU' hL'

/-- Unfloored monomial cancellation with the paper's fixed parameters and
the exact finite dyadic decomposition. -/
theorem monomial_cancellation
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, ∀ β : ℝ,
        1 ≤ d → (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
        N ^ ((1 / 100 : ℝ) - c) ≤ |β| →
        |β| ≤ 2 * N ^ (1 / 10000 : ℝ) →
        ((d : ℝ) / N) *
          ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ ≤
          12 * N ^ (-16 * η) := by
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let κ : ℝ := (1 / 100 : ℝ) / (10 * (j : ℝ))
  have hgap := monomial_fixed_order_gap hc hcNon
  have hgapLower : 2 < (j : ℝ) - c := by simpa [j] using hgap.1
  have hgapUpper : (j : ℝ) - c < 3 := by simpa [j] using hgap.2
  have hκpos : 0 < κ := by dsimp [κ]; positivity
  have hηpos : 0 ≤ η := by dsimp [η]; positivity
  have hsavings := monomial_fixed_parameter_savings hc hgapLower hgapUpper
  dsimp only at hsavings
  rcases hsavings with ⟨_, ⟨hηκ, _⟩⟩
  have hηκ' : 16 * η < κ := by simpa [η, κ] using hηκ
  obtain ⟨Nphase, hNphase, hblock⟩ :=
    exists_monomial_retained_block_phase_threshold
      (c := c) (j := j) hc hcNon hgapLower hgapUpper
  let N₀ : ℝ := max 3 Nphase
  refine ⟨N₀, ?_, ?_⟩
  · dsimp [N₀]
    exact le_max_left _ _
  · intro N hN d β hd hdcut hβlower hβupper
    have hNphase' : Nphase ≤ N := le_trans (le_max_right _ _) hN
    have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
    have hNgt : 1 < N := by linarith
    have hNpos : 0 < N := by linarith
    have hdreal : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdreal
    have hκvalue : 0 < κ := hκpos
    have ⟨J, hcut, hretained⟩ :=
      exists_minimal_real_dyadic_cutoff hNgt hdpos hκvalue
    let X : ℝ := N / (d : ℝ)
    let Y : ℝ := X / (2 : ℝ) ^ J
    let C : ℝ := 11 * N ^ (-16 * η)
    have hremNorm :
        ‖∑ n ∈ realIntegerInterval 0 Y,
          realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ ≤ Y := by
      calc
        ‖∑ n ∈ realIntegerInterval 0 Y,
            realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ ≤
          ∑ n ∈ realIntegerInterval 0 Y,
            ‖realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ :=
              norm_sum_le _ _
        _ = (realIntegerInterval 0 Y).card := by simp [norm_realExponentialPhase]
        _ ≤ Y := realIntegerInterval_zero_card_le Y (by dsimp [Y, X]; positivity)
    have hblocks : ∀ v ∈ Finset.range J,
        ‖∑ n ∈ realDyadicIntegerBlock X v,
          realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ ≤
          C * (X / (2 : ℝ) ^ (v + 1)) := by
      intro v hv
      let P : ℝ := X / (2 : ℝ) ^ (v + 1)
      have hPpos : 0 < P := by dsimp [P, X]; positivity
      have hPscale := hretained v (Finset.mem_range.mp hv)
      have hphase := hblock N hNphase' d P β hd hdcut hβlower hβupper hPscale
      have hphase' :
          ‖∑ n ∈ realIntegerInterval P P,
            realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ / P ≤
            11 * N ^ (-16 * η) := by
        simpa [P, X, η, realDyadicIntegerBlock] using hphase
      have hnorm := (div_le_iff₀ hPpos).mp hphase'
      simpa [C, P, X, realDyadicIntegerBlock] using hnorm
    have haggregate := norm_sum_realIntegerInterval_dyadic_aggregate
      (X := X) (C := C) (R := Y) (J := J) (by dsimp [X]; positivity)
      (by dsimp [C]; positivity)
      (fun n => realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n)
      hblocks (by simpa [Y, X] using hremNorm)
    have hremScaleCut : Y ≤ N ^ (1 - κ) / (d : ℝ) := by
      simpa [Y, X] using hcut
    have hremScaleMul := mul_le_mul_of_nonneg_left hremScaleCut
      (le_of_lt (div_pos hdpos hNpos))
    have hfactor : N ^ (1 - κ) = N * N ^ (-κ) := by
      calc
        N ^ (1 - κ) = N ^ (1 + (-κ)) := by congr 1 <;> ring
        _ = N ^ (1 : ℝ) * N ^ (-κ) := Real.rpow_add hNpos 1 (-κ)
        _ = N * N ^ (-κ) := by rw [Real.rpow_one]
    have hremScaleId : ((d : ℝ) / N) *
        (N ^ (1 - κ) / (d : ℝ)) = N ^ (-κ) := by
      field_simp
      exact hfactor
    have hremScaled' : ((d : ℝ) / N) * Y ≤ N ^ (-κ) := by
      calc
        _ ≤ ((d : ℝ) / N) * (N ^ (1 - κ) / (d : ℝ)) := hremScaleMul
        _ = N ^ (-κ) := hremScaleId
    have hscale : ((d : ℝ) / N) *
        ‖∑ n ∈ realIntegerInterval 0 X,
          realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ ≤
        C + ((d : ℝ) / N) * Y := by
      calc
        _ ≤ ((d : ℝ) / N) * (C * X + Y) :=
          mul_le_mul_of_nonneg_left haggregate (by positivity)
        _ = C + ((d : ℝ) / N) * Y := by
          dsimp [X]
          field_simp
          <;> ring
    calc
      ((d : ℝ) / N) *
          ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ ≤
        C + ((d : ℝ) / N) * Y := by simpa [X] using hscale
      _ ≤ C + N ^ (-κ) := add_le_add le_rfl hremScaled'
      _ ≤ 12 * N ^ (-16 * η) := by
        have hpow : N ^ (-κ) ≤ N ^ (-16 * η) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N)
            (by linarith : -κ ≤ -16 * η)
        dsimp [C]
        calc
          11 * N ^ (-16 * η) + N ^ (-κ) ≤
              11 * N ^ (-16 * η) + N ^ (-16 * η) :=
            add_le_add le_rfl hpow
          _ = 12 * N ^ (-16 * η) := by ring

/-- The low-frequency contribution to the boundary error on progressions,
with the exact cutoff and fixed `η(c)` from the blueprint. -/
theorem exists_boundaryKernel_progression_low_modes {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ M : ℕ, ∀ hM : 2 ≤ M,
        let H : ℕ := Nat.floor (N ^ (1 / 10000 : ℝ))
        ‖∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0},
          boundaryKernelFourierCoefficient M hM h *
            (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
              realExponentialPhase
                (fun t => (h : ℝ) * ((d : ℝ) * t) ^ c) n *
                ((((d : ℝ) / N) : ℝ) : ℂ))‖ ≤
          (12 * N ^ (-16 * η)) *
            ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
              Real.sqrt (Real.log (2 * (M : ℝ)))) := by
  dsimp only
  obtain ⟨Nmono, hNmono, hmonomial⟩ := monomial_cancellation hc hcNon
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let N₀ : ℝ := max 3 Nmono
  have hN₀ : 3 ≤ N₀ := by dsimp [N₀]; exact le_max_left _ _
  refine ⟨N₀, hN₀, ?_⟩
  · intro N hN d hd hdcut M hM
    let H : ℕ := Nat.floor (N ^ (1 / 10000 : ℝ))
    have hNmono' : Nmono ≤ N := by
      dsimp [N₀] at hN
      exact le_trans (le_max_right _ _) hN
    have hN1 : 1 ≤ N := le_trans (by norm_num : (1 : ℝ) ≤ 3)
      (le_trans hN₀ hN)
    have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hN1
    have hdreal : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdreal
    have hH : (H : ℝ) ≤ N ^ (1 / 10000 : ℝ) := by
      dsimp [H]
      exact Nat.floor_le (by positivity)
    have hfreq : ∀ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0},
        N ^ ((1 / 100 : ℝ) - c) ≤ |(h : ℝ)| ∧
          |(h : ℝ)| ≤ 2 * N ^ (1 / 10000 : ℝ) := by
      intro h hh
      have hmem := Finset.mem_sdiff.mp hh
      exact monomial_cancellation_frequency_range hN1 hc H hH
        hmem.1 (by simpa using hmem.2)
    have hmono : ∀ β : ℝ,
        N ^ ((1 / 100 : ℝ) - c) ≤ |β| →
        |β| ≤ 2 * N ^ (1 / 10000 : ℝ) →
        ((d : ℝ) / N) * ‖∑ n ∈ realIntegerInterval 0
          (N / (d : ℝ)),
          realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n‖ ≤
          12 * N ^ (-16 * η) := by
      intro β hlo hhi
      have h := hmonomial N hNmono' d β hd hdcut hlo hhi
      simpa [η, j] using h
    have hlow := boundaryKernel_progression_low_modes_of_monomial_bound
      M H hM hNpos hdpos hfreq hmono
    simpa [H, η, j] using hlow

/-- Convert the symmetric low-frequency sum with its scalar normalization
inside each phase sum into the normalized positive and negative blocks. -/
theorem boundaryKernel_low_modes_scaled_of_symmetric_bound
    (M H d : ℕ) (hM : 2 ≤ M) {N c L : ℝ}
    (hN : 0 < N) (hd : 0 < d)
    (hSym : ‖∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0},
      boundaryKernelFourierCoefficient M hM h *
        (∑ n ∈ realIntegerInterval 0 (N / d),
          realExponentialPhase (fun t => (h : ℝ) * (d * t) ^ c) n *
            ((d / N : ℝ) : ℂ))‖ ≤ L) :
    (d / N) * ‖((
        (∑ k ∈ Finset.range H,
          boundaryKernelFourierCoefficient M hM ((k + 1 : ℕ) : ℤ) *
            ∑ n ∈ realIntegerInterval 0 (N / d),
              realExponentialPhase
                (fun t => ((k + 1 : ℕ) : ℝ) * (d * t) ^ c) n) +
        (∑ k ∈ Finset.range H,
          boundaryKernelFourierCoefficient M hM (-((k + 1 : ℕ) : ℤ)) *
            ∑ n ∈ realIntegerInterval 0 (N / d),
              realExponentialPhase
                (fun t => (-((k + 1 : ℕ) : ℤ) : ℝ) * (d * t) ^ c) n)))‖ ≤ L := by
  let s : Finset ℤ := realIntegerInterval 0 (N / d)
  let D : ℂ := ((d / N : ℝ) : ℂ)
  let f : ℤ → ℂ := fun h => boundaryKernelFourierCoefficient M hM h *
    (∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * (d * t) ^ c) n * D)
  have hf (h : ℤ) : f h =
      (boundaryKernelFourierCoefficient M hM h *
        ∑ n ∈ s, realExponentialPhase (fun t => (h : ℝ) * (d * t) ^ c) n) * D := by
    dsimp [f]
    rw [← Finset.sum_mul]
    ring
  have hsym := sum_symmetricIcc_sdiff_zero_eq_range_pos_neg f H
  let pos : ℂ := ∑ k ∈ Finset.range H,
    boundaryKernelFourierCoefficient M hM ((k + 1 : ℕ) : ℤ) *
      ∑ n ∈ s, realExponentialPhase
        (fun t => ((k + 1 : ℕ) : ℝ) * (d * t) ^ c) n
  let neg : ℂ := ∑ k ∈ Finset.range H,
    boundaryKernelFourierCoefficient M hM (-((k + 1 : ℕ) : ℤ)) *
      ∑ n ∈ s, realExponentialPhase
        (fun t => (-((k + 1 : ℕ) : ℤ) : ℝ) * (d * t) ^ c) n
  have hpos : (∑ k ∈ Finset.range H, f ((k + 1 : ℕ) : ℤ)) = pos * D := by
    calc
      _ = ∑ k ∈ Finset.range H,
          (boundaryKernelFourierCoefficient M hM ((k + 1 : ℕ) : ℤ) *
            ∑ n ∈ s, realExponentialPhase
              (fun t => ((k + 1 : ℕ) : ℝ) * (d * t) ^ c) n) * D := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hf ((k + 1 : ℕ) : ℤ)
      _ = pos * D := by
        dsimp [pos]
        rw [Finset.sum_mul]
  have hneg : (∑ k ∈ Finset.range H, f (-((k + 1 : ℕ) : ℤ))) = neg * D := by
    calc
      _ = ∑ k ∈ Finset.range H,
          (boundaryKernelFourierCoefficient M hM (-((k + 1 : ℕ) : ℤ)) *
            ∑ n ∈ s, realExponentialPhase
              (fun t => (-((k + 1 : ℕ) : ℤ) : ℝ) * (d * t) ^ c) n) * D := by
        apply Finset.sum_congr rfl
        intro k hk
        simpa using hf (-((k + 1 : ℕ) : ℤ))
      _ = neg * D := by
        dsimp [neg]
        rw [Finset.sum_mul]
  have hfactor :
      (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0}, f h) = (pos + neg) * D := by
    rw [hsym, hpos, hneg]
    ring
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hscale : 0 ≤ d / N := le_of_lt (div_pos hdR hN)
  have hnorm : ‖(pos + neg) * D‖ = (d / N) * ‖pos + neg‖ := by
    dsimp [D]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscale]
    ring
  calc
    (d / N) * ‖pos + neg‖ = ‖(pos + neg) * D‖ := hnorm.symm
    _ = ‖∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0}, f h‖ := by
      rw [hfactor]
    _ ≤ L := by
      simpa [f, D, s] using hSym

/-- Instantiate the zero/low/high-mode pre-absorption estimate with the
paper's monomial-cancellation theorem and its exact low-frequency cutoff. -/
theorem exists_boundaryKernel_progression_preabs_from_monomial {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ M : ℕ, ∀ hM : 2 ≤ M,
        let H : ℕ := Nat.floor (N ^ (1 / 10000 : ℝ))
        1 ≤ H →
        ((d : ℝ) / N) *
          ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            (floorBoundaryKernel M hM
              (((d : ℝ) * (n : ℝ)) ^ c) : ℂ)‖ ≤
          (2 * (1 + (Real.log 4)⁻¹)) *
              Real.log (2 * (M : ℝ)) / (M : ℝ) +
            (12 * N ^ (-16 * η)) *
              ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
                Real.sqrt (Real.log (2 * (M : ℝ)))) +
            2 * (M : ℝ) / (H : ℝ) := by
  dsimp only
  obtain ⟨Nlow, hNlow, hlow⟩ :=
    exists_boundaryKernel_progression_low_modes hc hcNon
  refine ⟨Nlow, hNlow, ?_⟩
  intro N hN d hd hdcut M hM
  intro hH
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let H : ℕ := Nat.floor (N ^ (1 / 10000 : ℝ))
  have hNpos : 0 < N := by linarith
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  let B : ℝ := (12 * N ^ (-16 * η)) *
    ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
      Real.sqrt (Real.log (2 * (M : ℝ))))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hSym := hlow N hN d hd hdcut M hM
  have hSym' :
      ‖∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) \ {0},
        boundaryKernelFourierCoefficient M hM h *
          (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            realExponentialPhase (fun t => (h : ℝ) * ((d : ℝ) * t) ^ c) n *
              (((d : ℝ) / N : ℝ) : ℂ))‖ ≤ B := by
    simpa [H, η, j, B] using hSym
  have hLow := boundaryKernel_low_modes_scaled_of_symmetric_bound
    M H d hM hNpos (lt_of_lt_of_le (by norm_num) hd) hSym'
  have hpre := boundaryKernel_progression_preabs_bound
    M H d hM hH hd hNpos hB hLow
  simpa [H, B, η, j] using hpre

/-- A natural floor is at least half its argument once that argument is at
least two; this gives the lower half-power bounds for the paper cutoffs. -/
theorem natFloor_cast_ge_half_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hfloor := Nat.lt_floor_add_one x
  have hlow : x - 1 < (Nat.floor x : ℝ) := by linarith
  linarith

/-- A precise eventual logarithm bound obtained from Mathlib's real-power
asymptotic, stated without norm wrappers for use in scale absorption. -/
theorem eventually_log_le_const_mul_rpow {s ε : ℝ}
    (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ ε * x ^ s := by
  have hlittle := (isLittleO_log_rpow_atTop hs).bound hε
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hx => hx⟩, hlittle]
    with x hx hbound
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [Real.norm_of_nonneg hlog,
    Real.norm_of_nonneg (Real.rpow_nonneg hx0 s)] at hbound
  exact hbound

set_option maxHeartbeats 500000
/-- Absorb the three exact terms from the progression Fourier decomposition
at the paper's cutoffs. The coefficient `3` is an explicit admissible
constant depending on the fixed exponent `η`. -/
theorem exists_boundaryKernel_progression_three_term_absorption
    {η : ℝ} (hη : 0 < η)
    (hηsmall : η < (1 / 10000 : ℝ) / 4) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      let M : ℕ := Nat.floor (N ^ η)
      let H : ℕ := Nat.floor (N ^ (1 / 10000 : ℝ))
      2 ≤ M ∧ 1 ≤ H ∧
        (2 * (1 + (Real.log 4)⁻¹)) *
            Real.log (2 * (M : ℝ)) / (M : ℝ) +
          (12 * N ^ (-16 * η)) *
            ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
              Real.sqrt (Real.log (2 * (M : ℝ)))) +
          2 * (M : ℝ) / (H : ℝ) ≤ 3 * N ^ (-η / 2) := by
  have hbpos : 0 < (1 / 10000 : ℝ) := by norm_num
  have htailExp : 0 < (1 / 10000 : ℝ) - 3 * η / 2 := by linarith
  let C₀ : ℝ := 2 * (1 + (Real.log 4)⁻¹)
  let C₁ : ℝ := 5 * (2 * (1 + (Real.log 4)⁻¹)) + 2
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  let ε₁ : ℝ := 1 / (4 * C₀)
  let ε₂ : ℝ := 1 / (36 * C₁)
  have hε₁ : 0 < ε₁ := by dsimp [ε₁]; positivity
  have hε₂ : 0 < ε₂ := by dsimp [ε₂]; positivity
  obtain ⟨Nη, hNη, hlargeη⟩ :=
    exists_real_rpow_threshold (C := 3) (s := η) hη
  obtain ⟨Nb, hNb, hlargeb⟩ :=
    exists_real_rpow_threshold (C := 2) (s := (1 / 10000 : ℝ)) hbpos
  obtain ⟨Ntail, hNtail, hlargeTail⟩ :=
    exists_real_rpow_threshold (C := 4) (s := (1 / 10000 : ℝ) - 3 * η / 2)
      htailExp
  have hlog₁ := eventually_log_le_const_mul_rpow
    (s := η / 2) (ε := ε₁) (by linarith) hε₁
  have hlog₂ := eventually_log_le_const_mul_rpow
    (s := 15 * η) (ε := ε₂) (by positivity) hε₂
  have hgood : ∀ᶠ N : ℝ in Filter.atTop,
      3 ≤ N ^ η ∧ 2 ≤ N ^ (1 / 10000 : ℝ) ∧
        Real.exp 2 ≤ N ∧
        Real.log N ≤ ε₁ * N ^ (η / 2) ∧
        Real.log N ≤ ε₂ * N ^ (15 * η) ∧
        4 ≤ N ^ ((1 / 10000 : ℝ) - 3 * η / 2) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨Nη, fun N hN => hlargeη N hN⟩,
      Filter.eventually_atTop.2 ⟨Nb, fun N hN => hlargeb N hN⟩,
      Filter.eventually_atTop.2 ⟨Ntail, fun N hN => hlargeTail N hN⟩,
      Filter.eventually_atTop.2 ⟨Real.exp 2, fun N hN => hN⟩,
      hlog₁, hlog₂] with N hηN hbN htailN hexpN hlog₁N hlog₂N
    exact ⟨hηN, hbN, hexpN, hlog₁N, hlog₂N, htailN⟩
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hgood
  let N₀ : ℝ := max 3 B
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro N hN
  have hNlarge := hB N (le_trans (le_max_right _ _) hN)
  rcases hNlarge with ⟨hNη, hNb, hexpN, hlog₁N, hlog₂N, htailN⟩
  have hN1 : 1 ≤ N := by
    have hexpOne : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact le_trans (by linarith) hexpN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN1
  have hlogN2 : 2 ≤ Real.log N := by
    calc
      2 = Real.log (Real.exp 2) := by rw [Real.log_exp]
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 2) hexpN
  let M : ℕ := Nat.floor (N ^ η)
  let H : ℕ := Nat.floor (N ^ (1 / 10000 : ℝ))
  have hMlower : N ^ η / 2 ≤ (M : ℝ) :=
    natFloor_cast_ge_half_of_two_le (le_trans (by norm_num) hNη)
  have hHlower : N ^ (1 / 10000 : ℝ) / 2 ≤ (H : ℝ) :=
    natFloor_cast_ge_half_of_two_le hNb
  have hMle : (M : ℝ) ≤ N ^ η := by
    dsimp [M]
    exact Nat.floor_le (by positivity)
  have hHle : (H : ℝ) ≤ N ^ (1 / 10000 : ℝ) := by
    dsimp [H]
    exact Nat.floor_le (by positivity)
  have hMtwo : 2 ≤ M := by
    have hfloor := Nat.lt_floor_add_one (N ^ η)
    dsimp [M]
    exact_mod_cast (by nlinarith [hfloor, hNη] : (2 : ℝ) ≤ (Nat.floor (N ^ η) : ℝ))
  have hHone : 1 ≤ H := by
    have hfloor := Nat.lt_floor_add_one (N ^ (1 / 10000 : ℝ))
    dsimp [H]
    exact_mod_cast (by nlinarith [hfloor, hNb] : (1 : ℝ) ≤ (Nat.floor (N ^ (1 / 10000 : ℝ)) : ℝ))
  have hηle1 : η ≤ 1 := by linarith
  have hNηle : N ^ η ≤ N := by
    calc
      N ^ η ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hηle1
      _ = N := Real.rpow_one N
  have hMleN : (M : ℝ) ≤ N := le_trans hMle hNηle
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hMtwo)
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hHone)
  have hNηpos : 0 < N ^ η := Real.rpow_pos_of_pos hNpos η
  have hNbpos : 0 < N ^ (1 / 10000 : ℝ) :=
    Real.rpow_pos_of_pos hNpos (1 / 10000 : ℝ)
  have hlogNnonneg : 0 ≤ Real.log N := by linarith
  have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_nonneg (by nlinarith [show (2 : ℝ) ≤ (M : ℝ) by exact_mod_cast hMtwo])
  have hlogMle : Real.log (2 * (M : ℝ)) ≤ 2 * Real.log N := by
    calc
      Real.log (2 * (M : ℝ)) ≤ Real.log (2 * N) :=
        Real.log_le_log (by positivity) (by nlinarith [hMleN])
      _ = Real.log 2 + Real.log N := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
      _ ≤ 1 + Real.log N := by
        exact add_le_add
          (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]) le_rfl
      _ ≤ 2 * Real.log N := by nlinarith
  have hfirst : C₀ * Real.log (2 * (M : ℝ)) / (M : ℝ) ≤
      N ^ (-η / 2) := by
    have hdiv : Real.log (2 * (M : ℝ)) / (M : ℝ) ≤
        4 * Real.log N / (N ^ η) := by
      apply (div_le_div_iff₀ hMpos hNηpos).2
      calc
        Real.log (2 * (M : ℝ)) * N ^ η ≤ (2 * Real.log N) * N ^ η :=
          mul_le_mul_of_nonneg_right hlogMle (le_of_lt hNηpos)
        _ ≤ (2 * Real.log N) * (2 * (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hMlower]) (by positivity)
        _ = (4 * Real.log N) * (M : ℝ) := by ring
    have hlog1pow : 4 * C₀ * Real.log N ≤ N ^ (η / 2) := by
      calc
        4 * C₀ * Real.log N ≤
            (4 * C₀) * (ε₁ * N ^ (η / 2)) :=
          mul_le_mul_of_nonneg_left hlog₁N (by positivity)
        _ = N ^ (η / 2) := by dsimp [ε₁]; field_simp
    calc
      _ = C₀ * (Real.log (2 * (M : ℝ)) / (M : ℝ)) := by ring
      _ ≤ C₀ * (4 * Real.log N / N ^ η) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (4 * C₀ * Real.log N) / N ^ η := by ring
      _ ≤ N ^ (η / 2) / N ^ η :=
        (div_le_div_iff₀ hNηpos hNηpos).2 (by nlinarith [hlog1pow])
      _ = N ^ (-η / 2) := by
        rw [← Real.rpow_sub hNpos]
        congr 1
        ring
  have hsqrt : Real.sqrt (Real.log (2 * (M : ℝ))) ≤ 3 * Real.log N := by
    have hsqrt' : Real.sqrt (Real.log (2 * (M : ℝ))) ≤
        Real.log (2 * (M : ℝ)) + 1 := by
      nlinarith [Real.sq_sqrt hlogM]
    linarith [hsqrt', hlogMle, hlogN2]
  have hsecond : (12 * N ^ (-16 * η)) *
      (C₁ * Real.sqrt (Real.log (2 * (M : ℝ)))) ≤ N ^ (-η / 2) := by
    have hlog2pow : 36 * C₁ * Real.log N ≤ N ^ (15 * η) := by
      calc
        36 * C₁ * Real.log N ≤
            (36 * C₁) * (ε₂ * N ^ (15 * η)) :=
          mul_le_mul_of_nonneg_left hlog₂N (by positivity)
        _ = N ^ (15 * η) := by dsimp [ε₂]; field_simp
    have hfactor : N ^ (-16 * η) * N ^ (15 * η) = N ^ (-η) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    calc
      _ = (12 * C₁) * N ^ (-16 * η) *
          Real.sqrt (Real.log (2 * (M : ℝ))) := by ring
      _ ≤ (12 * C₁) * N ^ (-16 * η) * (3 * Real.log N) := by
        gcongr
      _ = N ^ (-16 * η) * (36 * C₁ * Real.log N) := by ring
      _ ≤ N ^ (-16 * η) * N ^ (15 * η) :=
        mul_le_mul_of_nonneg_left hlog2pow (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ = N ^ (-η) := hfactor
      _ ≤ N ^ (-η / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hthird : 2 * (M : ℝ) / (H : ℝ) ≤ N ^ (-η / 2) := by
    have hratio : (M : ℝ) / (H : ℝ) ≤
        N ^ η / (N ^ (1 / 10000 : ℝ) / 2) := by
      apply (div_le_div_iff₀ hHpos (by positivity)).2
      calc
        (M : ℝ) * (N ^ (1 / 10000 : ℝ) / 2) ≤
            N ^ η * (N ^ (1 / 10000 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hMle (by positivity)
        _ ≤ N ^ η * (H : ℝ) :=
          mul_le_mul_of_nonneg_left hHlower (by positivity)
    have hratio' : 2 * (N ^ η / (N ^ (1 / 10000 : ℝ) / 2)) =
        4 * N ^ (η - 1 / 10000 : ℝ) := by
      calc
        2 * (N ^ η / (N ^ (1 / 10000 : ℝ) / 2)) =
            4 * (N ^ η / N ^ (1 / 10000 : ℝ)) := by
          field_simp
          <;> norm_num
        _ = 4 * N ^ (η - 1 / 10000 : ℝ) := by
          rw [← Real.rpow_sub hNpos]
    have hpow : 4 * N ^ (η - 1 / 10000 : ℝ) ≤ N ^ (-η / 2) := by
      calc
        4 * N ^ (η - 1 / 10000 : ℝ) ≤
            N ^ ((1 / 10000 : ℝ) - 3 * η / 2) *
              N ^ (η - 1 / 10000 : ℝ) :=
          mul_le_mul_of_nonneg_right htailN (Real.rpow_nonneg (le_of_lt hNpos) _)
        _ = N ^ (-η / 2) := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
    calc
      2 * (M : ℝ) / (H : ℝ) = 2 * ((M : ℝ) / (H : ℝ)) := by ring
      _ ≤
          2 * (N ^ η / (N ^ (1 / 10000 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)
      _ = 4 * N ^ (η - 1 / 10000 : ℝ) := hratio'
      _ ≤ N ^ (-η / 2) := hpow
  have hC₁pos : 0 ≤ C₁ := le_of_lt hC₁
  have htotal :
      C₀ * Real.log (2 * (M : ℝ)) / (M : ℝ) +
        (12 * N ^ (-16 * η)) *
          (C₁ * Real.sqrt (Real.log (2 * (M : ℝ)))) +
        2 * (M : ℝ) / (H : ℝ) ≤ 3 * N ^ (-η / 2) := by
    linarith [hfirst, hsecond, hthird]
  refine ⟨hMtwo, hHone, ?_⟩
  simpa [C₀, C₁, M, H] using htotal

/-- The blueprint's boundary-error estimate on progressions, with the exact
parameter `η(c)`, cutoff `M=⌊N^η⌋`, divisor range, and sampled integers. -/
theorem boundaryErrorProgression {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      let M : ℕ := Nat.floor (N ^ η)
      ∃ hM : 2 ≤ M, ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
        ((d : ℝ) / N) *
          (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            floorBoundaryKernel M hM
              (((d : ℝ) * (n : ℝ)) ^ c)) ≤ 3 * N ^ (-η / 2) := by
  dsimp only
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  have hgap := monomial_fixed_order_gap hc hcNon
  have hj3 : 3 < (j : ℝ) := by
    have hgapLower : 2 < (j : ℝ) - c := by simpa [j] using hgap.1
    linarith [hc, hgapLower]
  have hjNat : 2 ≤ j := by exact_mod_cast (by linarith : (2 : ℝ) ≤ (j : ℝ))
  have hpow2 : 4 ≤ (2 : ℝ) ^ (j : ℝ) := by
    calc
      4 = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (j : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hjNat)
  have hηpos : 0 < η := by dsimp [η, j]; positivity
  have hden : 400 < 100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ) := by
    have hprod : 12 ≤ (j : ℝ) * (2 : ℝ) ^ (j : ℝ) := by
      calc
        12 = 3 * 4 := by norm_num
        _ ≤ (j : ℝ) * (2 : ℝ) ^ (j : ℝ) :=
          mul_le_mul hj3.le hpow2 (by norm_num) (by positivity)
    nlinarith
  have hηsmall : η < (1 / 10000 : ℝ) / 4 := by
    dsimp [η]
    rw [div_lt_iff₀ (by positivity :
      0 < 100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))]
    norm_num
    have hscaled := mul_lt_mul_of_pos_right hden
      (by norm_num : (0 : ℝ) < (1 / 40000 : ℝ))
    norm_num at hscaled
    linarith
  obtain ⟨Npre, hNpre, hpre⟩ :=
    exists_boundaryKernel_progression_preabs_from_monomial hc hcNon
  obtain ⟨Nabs, hNabs, habs⟩ :=
    exists_boundaryKernel_progression_three_term_absorption hηpos hηsmall
  let N₀ : ℝ := max Npre Nabs
  have hN₀ : 3 ≤ N₀ := by
    dsimp [N₀]
    exact le_max_of_le_left hNpre
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  have hNpre' : Npre ≤ N := le_trans (le_max_left _ _) hN
  have hNabs' : Nabs ≤ N := le_trans (le_max_right _ _) hN
  let M : ℕ := Nat.floor (N ^ η)
  let H : ℕ := Nat.floor (N ^ (1 / 10000 : ℝ))
  have hAbs := habs N hNabs'
  dsimp only at hAbs
  rcases hAbs with ⟨hM, hH, hterms⟩
  refine ⟨hM, ?_⟩
  intro d hd hdcut
  have hNpos : 0 < N := by linarith [hN₀, hN]
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hpre' := hpre N hNpre' d hd hdcut M hM hH
  have hrealnonneg : 0 ≤
        ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
          floorBoundaryKernel M hM
            (((d : ℝ) * (n : ℝ)) ^ c) := by
    exact Finset.sum_nonneg fun n hn =>
      floorBoundaryKernel_nonneg M hM
        (((d : ℝ) * (n : ℝ)) ^ c)
  have hnorm :
        ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            (floorBoundaryKernel M hM
              (((d : ℝ) * (n : ℝ)) ^ c) : ℂ)‖ =
          ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            floorBoundaryKernel M hM
              (((d : ℝ) * (n : ℝ)) ^ c) := by
    rw [← Complex.ofReal_sum]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrealnonneg]
  calc
    ((d : ℝ) / N) *
          (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            floorBoundaryKernel M hM
              (((d : ℝ) * (n : ℝ)) ^ c)) =
        ((d : ℝ) / N) *
          ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
              (floorBoundaryKernel M hM
              (((d : ℝ) * (n : ℝ)) ^ c) : ℂ)‖ := by rw [hnorm]
    _ ≤ (2 * (1 + (Real.log 4)⁻¹)) *
            Real.log (2 * (M : ℝ)) / (M : ℝ) +
          (12 * N ^ (-16 * η)) *
            ((5 * (2 * (1 + (Real.log 4)⁻¹)) + 2) *
              Real.sqrt (Real.log (2 * (M : ℝ)))) +
          2 * (M : ℝ) / (H : ℝ) := hpre'
    _ ≤ 3 * N ^ (-η / 2) := by simpa [M, H] using hterms

/-! ### Continuous fractional-power model -/

/-- The normalized continuous fractional-power Fourier model from the
blueprint, with the paper's convention `e(t) = exp(2π i t)`. -/
noncomputable def continuousFractionalModel (c N ξ : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)

/-- Scaling the continuous model from `[0,N]` to `[0,1]` changes the
frequency to `ξ*N^c`. -/
theorem continuousFractionalModel_eq_unitIntegral {c N ξ : ℝ} (hN : 0 < N) :
    continuousFractionalModel c N ξ =
      ∫ u in (0 : ℝ)..1, unitFrequencyPhase ((ξ * N ^ c) * u ^ c) := by
  let f : ℝ → ℂ := fun t => unitFrequencyPhase (ξ * t ^ c)
  have hcomp :
      (∫ u in (0 : ℝ)..1, f (u * N)) =
        (N : ℂ)⁻¹ * ∫ t in (0 : ℝ)..N, f t := by
    simpa [f] using
      (intervalIntegral.integral_comp_mul_right (a := (0 : ℝ)) (b := 1)
        (f := fun t : ℝ => unitFrequencyPhase (ξ * t ^ c)) (c := N) hN.ne')
  have hphase : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      f (u * N) = unitFrequencyPhase ((ξ * N ^ c) * u ^ c) := by
    intro u hu
    have hu0 : 0 ≤ u := by
      rcases Set.mem_uIcc.mp hu with ⟨hu0, hu1⟩ | ⟨hu1, hu0⟩
      · exact hu0
      · linarith
    dsimp [f]
    congr 1
    rw [Real.mul_rpow hu0 hN.le]
    ring
  rw [continuousFractionalModel]
  calc
    (N : ℂ)⁻¹ * ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c) =
        ∫ u in (0 : ℝ)..1, f (u * N) := hcomp.symm
    _ = ∫ u in (0 : ℝ)..1, unitFrequencyPhase ((ξ * N ^ c) * u ^ c) := by
          apply intervalIntegral.integral_congr
          intro u hu
          exact hphase u hu

/-- At zero frequency the continuous model is exactly normalized to one. -/
theorem continuousFractionalModel_zero {c N : ℝ} (hN : 0 < N) :
    continuousFractionalModel c N 0 = 1 := by
  rw [continuousFractionalModel]
  simp only [zero_mul, unitFrequencyPhase, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero]
  rw [intervalIntegral.integral_const]
  simp [hN.ne']

/-- Pointwise phase displacement, before integrating the small-frequency
bound. -/
theorem norm_unitFrequencyPhase_rpow_sub_one_le (c ξ t : ℝ) :
    ‖unitFrequencyPhase (ξ * t ^ c) - 1‖ ≤
      2 * Real.pi * |ξ| * |t ^ c| := by
  unfold unitFrequencyPhase
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := 2 * Real.pi * (ξ * t ^ c))
  have harg :
      ((↑(2 * Real.pi * (ξ * t ^ c)) : ℂ) * Complex.I) =
        Complex.I * ↑(2 * Real.pi * (ξ * t ^ c)) := by ring
  rw [harg]
  calc
    ‖Complex.exp (Complex.I * ↑(2 * Real.pi * (ξ * t ^ c))) - 1‖ ≤
        ‖(2 * Real.pi * (ξ * t ^ c) : ℝ)‖ := h
    _ = 2 * Real.pi * |ξ| * |t ^ c| := by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (mul_pos (by norm_num) Real.pi_pos), abs_mul]
      ring

/-- The small-frequency Lipschitz estimate for the normalized continuous
model, with the exact constant in the blueprint. -/
theorem continuousFractionalModel_close_to_one {c N ξ : ℝ}
    (hc : 1 < c) (hN : 0 < N) :
    ‖continuousFractionalModel c N ξ - 1‖ ≤
      (2 * Real.pi / (c + 1)) * |ξ| * N ^ c := by
  let f : ℝ → ℂ := fun t => unitFrequencyPhase (ξ * t ^ c)
  have hpow : Continuous (fun t : ℝ => t ^ c) :=
    continuous_real_rpow_of_one_lt hc
  have hf : Continuous f := by
    dsimp [f]
    unfold unitFrequencyPhase
    fun_prop
  have hfi : IntervalIntegrable f MeasureTheory.volume 0 N := hf.intervalIntegrable _ _
  have hone : (∫ t in (0 : ℝ)..N, (1 : ℂ)) = (N : ℂ) := by simp
  have hmul : (N : ℂ)⁻¹ * (N : ℂ) = 1 :=
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hN.ne')
  have hdiff : continuousFractionalModel c N ξ - 1 =
      (N : ℂ)⁻¹ * ∫ t in (0 : ℝ)..N, (f t - 1) := by
    rw [continuousFractionalModel]
    change (N : ℂ)⁻¹ * (∫ t in (0 : ℝ)..N, f t) - 1 = _
    calc
      (N : ℂ)⁻¹ * (∫ t in (0 : ℝ)..N, f t) - 1 =
          (N : ℂ)⁻¹ * (∫ t in (0 : ℝ)..N, f t) - (N : ℂ)⁻¹ * (N : ℂ) := by
            rw [hmul]
      _ = (N : ℂ)⁻¹ * ((∫ t in (0 : ℝ)..N, f t) - (N : ℂ)) := by ring
      _ = (N : ℂ)⁻¹ * ((∫ t in (0 : ℝ)..N, f t) -
          (∫ t in (0 : ℝ)..N, (1 : ℂ))) := by rw [hone]
      _ = (N : ℂ)⁻¹ * ∫ t in (0 : ℝ)..N, (f t - 1) := by
            rw [intervalIntegral.integral_sub hfi intervalIntegrable_const]
  have hrpowInt : IntervalIntegrable (fun t : ℝ => t ^ c) MeasureTheory.volume 0 N :=
    intervalIntegral.intervalIntegrable_rpow (μ := MeasureTheory.volume) (a := 0) (b := N)
      (Or.inl (by linarith))
  have hboundInt : IntervalIntegrable (fun t : ℝ =>
      2 * Real.pi * |ξ| * t ^ c) MeasureTheory.volume 0 N := by
    exact hrpowInt.const_mul (2 * Real.pi * |ξ|)
  have hnormInt := intervalIntegral.norm_integral_le_of_norm_le hN.le
    (f := fun t : ℝ => f t - 1)
    (g := fun t => 2 * Real.pi * |ξ| * t ^ c)
    (by
      filter_upwards [] with t ht
      have ht0 : 0 < t := ht.1
      have hp : 0 ≤ t ^ c := Real.rpow_nonneg (le_of_lt ht0) c
      have hpt := norm_unitFrequencyPhase_rpow_sub_one_le c ξ t
      rw [abs_of_nonneg hp] at hpt
      exact hpt)
    hboundInt
  have hpowInt : (∫ t in (0 : ℝ)..N, t ^ c) =
      N ^ (c + 1) / (c + 1) := by
    rw [integral_rpow (a := 0) (b := N) (r := c) (Or.inl (by linarith))]
    simp [Real.zero_rpow (by linarith : c + 1 ≠ 0)]
  have hnormInv : ‖(N : ℂ)⁻¹‖ = N⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  rw [hdiff, norm_mul, hnormInv]
  have hIntEval : (∫ t in (0 : ℝ)..N,
      2 * Real.pi * |ξ| * t ^ c) =
        2 * Real.pi * |ξ| * (N ^ (c + 1) / (c + 1)) := by
    rw [intervalIntegral.integral_const_mul, hpowInt]
  rw [hIntEval] at hnormInt
  have hNpow : N ^ (c + 1) = N ^ c * N := by
    rw [Real.rpow_add hN, Real.rpow_one]
  rw [hNpow] at hnormInt
  calc
    N⁻¹ * ‖∫ t in (0 : ℝ)..N, (f t - 1)‖ ≤
        N⁻¹ * (2 * Real.pi * |ξ| * (N ^ c * N / (c + 1))) :=
          mul_le_mul_of_nonneg_left hnormInt (by positivity)
    _ = (2 * Real.pi / (c + 1)) * |ξ| * N ^ c := by
      field_simp

/-- Exact power-tail integral on an interval bounded away from zero. -/
theorem integral_rpow_neg_c_on_pos_interval {c a : ℝ}
    (hc : 1 < c) (ha : 0 < a) :
    (∫ t in a..(1 : ℝ), t ^ (-c)) =
      (a ^ (1 - c) - 1) / (c - 1) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc a (1 : ℝ) :=
    Set.notMem_uIcc_of_lt ha (by norm_num)
  rw [integral_rpow (a := a) (b := (1 : ℝ)) (r := -c)
    (Or.inr ⟨by linarith, hzero⟩)]
  rw [show -c + 1 = 1 - c by ring, Real.one_rpow]
  rw [show 1 - c = -(c - 1) by ring]
  field_simp [ne_of_gt (sub_pos.mpr hc)]
  ring

/-- Derivative of the fractional-power phase at a positive point. -/
theorem hasDerivAt_unitFrequencyPhase_rpow {c lam t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => unitFrequencyPhase (lam * x ^ c))
      (unitFrequencyPhase (lam * t ^ c) *
        ((↑(2 * Real.pi * lam * c * t ^ (c - 1)) : ℂ) * Complex.I)) t := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ c) (c * t ^ (c - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht)
  have hargReal : HasDerivAt (fun x : ℝ => (2 * Real.pi * lam) * x ^ c)
      ((2 * Real.pi * lam) * (c * t ^ (c - 1))) t :=
    hpow.const_mul (2 * Real.pi * lam)
  have harg := (hargReal.ofReal_comp).const_mul Complex.I
  have hexp := (Complex.hasDerivAt_exp _).comp t harg
  convert hexp using 1
  · funext x
    unfold unitFrequencyPhase
    change Complex.exp (↑(2 * Real.pi * (lam * x ^ c)) * Complex.I) =
      Complex.exp (Complex.I * ↑(2 * Real.pi * lam * x ^ c))
    push_cast
    ring
  · unfold unitFrequencyPhase
    push_cast
    ring

/-- Cancellation of the two reciprocal powers that occur in the
integration-by-parts amplitude. -/
theorem rpow_one_sub_mul_rpow_sub_one_eq_one {c a : ℝ} (ha : 0 < a) :
    a ^ (1 - c) * a ^ (c - 1) = 1 := by
  rw [← Real.rpow_add ha, show (1 - c) + (c - 1) = 0 by ring]
  exact Real.rpow_zero a

/-- Reciprocal derivative amplitude for integration by parts in the
fractional-power phase. -/
noncomputable def fractionalPhaseAmplitude (c lam t : ℝ) : ℂ :=
  (((2 * Real.pi * lam * c)⁻¹ * t ^ (1 - c) : ℝ) : ℂ) * (-Complex.I)

/-- The derivative of the reciprocal amplitude, in a form suited to
interval integrability. -/
noncomputable def fractionalPhaseAmplitudeDeriv (c lam t : ℝ) : ℂ :=
  (-Complex.I) *
    (((2 * Real.pi * lam * c)⁻¹ * ((1 - c) * t ^ (-c)) : ℝ) : ℂ)

/-- The derivative factor for the fractional-power phase. -/
noncomputable def fractionalPhaseDerivative (c lam t : ℝ) : ℂ :=
  unitFrequencyPhase (lam * t ^ c) *
    ((↑(2 * Real.pi * lam * c * t ^ (c - 1)) : ℂ) * Complex.I)

/-- Continuity of the reciprocal amplitude on any interval with positive
endpoints. -/
theorem continuousOn_fractionalPhaseAmplitude {c lam a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => fractionalPhaseAmplitude c lam t) (Set.uIcc a 1) := by
  have htpos : ∀ t ∈ Set.uIcc a (1 : ℝ), 0 < t := by
    intro t ht
    exact lt_of_lt_of_le (lt_min ha zero_lt_one) ht.1
  have hp : ContinuousOn (fun t : ℝ => t ^ (1 - c)) (Set.uIcc a 1) := by
    apply continuousOn_id.rpow_const
    intro t ht
    exact Or.inl (ne_of_gt (htpos t ht))
  change ContinuousOn (fun t : ℝ =>
      (((2 * Real.pi * lam * c)⁻¹ * t ^ (1 - c) : ℝ) : ℂ) * (-Complex.I)) _
  have hreal : ContinuousOn (fun t : ℝ =>
      (2 * Real.pi * lam * c)⁻¹ * t ^ (1 - c)) (Set.uIcc a 1) := by
    exact continuousOn_const.mul hp
  have hcast : ContinuousOn (fun t : ℝ =>
      (((2 * Real.pi * lam * c)⁻¹ * t ^ (1 - c) : ℝ) : ℂ))
      (Set.uIcc a 1) := Complex.continuous_ofReal.comp_continuousOn hreal
  have hresult := hcast.mul (continuousOn_const :
    ContinuousOn (fun _ : ℝ => (-Complex.I : ℂ)) (Set.uIcc a 1))
  convert hresult using 1 <;> ext t <;> simp <;> ring

/-- The reciprocal amplitude derivative is continuous away from zero. -/
theorem continuousOn_fractionalPhaseAmplitudeDeriv {c lam a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => fractionalPhaseAmplitudeDeriv c lam t)
      (Set.uIcc a 1) := by
  have htpos : ∀ t ∈ Set.uIcc a (1 : ℝ), 0 < t := by
    intro t ht
    exact lt_of_lt_of_le (lt_min ha zero_lt_one) ht.1
  have hp : ContinuousOn (fun t : ℝ => t ^ (-c)) (Set.uIcc a 1) := by
    apply continuousOn_id.rpow_const
    intro t ht
    exact Or.inl (ne_of_gt (htpos t ht))
  change ContinuousOn (fun t : ℝ =>
      (-Complex.I) *
        (((2 * Real.pi * lam * c)⁻¹ * ((1 - c) * t ^ (-c)) : ℝ) : ℂ)) _
  have hreal : ContinuousOn (fun t : ℝ =>
      (2 * Real.pi * lam * c)⁻¹ * ((1 - c) * t ^ (-c))) (Set.uIcc a 1) := by
    exact continuousOn_const.mul (continuousOn_const.mul hp)
  have hcast : ContinuousOn (fun t : ℝ =>
      (((2 * Real.pi * lam * c)⁻¹ * ((1 - c) * t ^ (-c)) : ℝ) : ℂ))
      (Set.uIcc a 1) := Complex.continuous_ofReal.comp_continuousOn hreal
  have hresult := (continuousOn_const :
    ContinuousOn (fun _ : ℝ => (-Complex.I : ℂ)) (Set.uIcc a 1)).mul hcast
  convert hresult using 1 <;> ext t <;> simp <;> ring

/-- The oscillatory phase derivative factor is continuous on the real line
when `c>1`. -/
theorem continuousOn_fractionalPhaseDerivative {c lam a : ℝ} (hc : 1 < c) :
    ContinuousOn (fun t : ℝ => fractionalPhaseDerivative c lam t)
      (Set.uIcc a 1) := by
  have hpow : Continuous (fun t : ℝ => t ^ c) :=
    continuous_real_rpow_of_one_lt hc
  have hphase : Continuous (fun t : ℝ => unitFrequencyPhase (lam * t ^ c)) := by
    unfold unitFrequencyPhase
    fun_prop
  have hpow : Continuous (fun t : ℝ => t ^ (c - 1)) :=
    Real.continuous_rpow_const (by linarith)
  have hcoeffReal : Continuous (fun t : ℝ =>
      (2 * Real.pi * lam * c) * t ^ (c - 1)) :=
    continuous_const.mul hpow
  have hcoeff : Continuous (fun t : ℝ =>
      (↑(2 * Real.pi * lam * c * t ^ (c - 1)) : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp hcoeffReal).mul continuous_const
  change ContinuousOn
    (fun t : ℝ => unitFrequencyPhase (lam * t ^ c) *
      ((↑(2 * Real.pi * lam * c * t ^ (c - 1)) : ℂ) * Complex.I)) _
  exact hphase.continuousOn.mul hcoeff.continuousOn

/-- Continuity of the unit-frequency phase. -/
theorem continuous_unitFrequencyPhase : Continuous unitFrequencyPhase := by
  unfold unitFrequencyPhase
  fun_prop

/-- The phase derivative with the named derivative factor. -/
theorem hasDerivAt_fractionalPhaseDerivative {c lam t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => unitFrequencyPhase (lam * x ^ c))
      (fractionalPhaseDerivative c lam t) t := by
  simpa [fractionalPhaseDerivative] using
    (hasDerivAt_unitFrequencyPhase_rpow (c := c) (lam := lam) (t := t) ht)

/-- Derivative of the reciprocal phase amplitude away from zero. -/
theorem hasDerivAt_fractionalPhaseAmplitude {c lam t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => fractionalPhaseAmplitude c lam x)
      (fractionalPhaseAmplitudeDeriv c lam t) t := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (1 - c))
      ((1 - c) * t ^ ((1 - c) - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht)
  have hreal : HasDerivAt (fun x : ℝ =>
      ((2 * Real.pi * lam * c)⁻¹) * x ^ (1 - c))
      (((2 * Real.pi * lam * c)⁻¹) * ((1 - c) * t ^ ((1 - c) - 1))) t :=
    hpow.const_mul ((2 * Real.pi * lam * c)⁻¹)
  have hcast := (hreal.ofReal_comp).const_mul (-Complex.I)
  have hexp : t ^ ((1 - c) - 1) = t ^ (-c) := by
    congr 1
    ring
  rw [hexp] at hcast
  convert hcast using 1
  · funext x
    simp [fractionalPhaseAmplitude]
    ring
  · rfl

/-- The reciprocal amplitude cancels the phase derivative exactly. -/
theorem fractionalPhaseAmplitude_mul_phaseDerivative_eq_one
    {c lam t : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) (ht : 0 < t) :
    fractionalPhaseAmplitude c lam t *
      ((↑(2 * Real.pi * lam * c * t ^ (c - 1)) : ℂ) * Complex.I) = 1 := by
  let A : ℝ := 2 * Real.pi * lam * c
  have hA : A ≠ 0 := by
    dsimp [A]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hlam)
      hc.ne'
  have hrpow := rpow_one_sub_mul_rpow_sub_one_eq_one (c := c) (a := t) ht
  have hreal : (A⁻¹ * t ^ (1 - c)) * (A * t ^ (c - 1)) = 1 := by
    calc
      (A⁻¹ * t ^ (1 - c)) * (A * t ^ (c - 1)) =
          (A⁻¹ * A) * (t ^ (1 - c) * t ^ (c - 1)) := by ring
      _ = 1 * 1 := by rw [inv_mul_cancel₀ hA, hrpow]
      _ = 1 := by ring
  have hcomplex : ((↑(A⁻¹ * t ^ (1 - c)) : ℂ) *
      ↑(A * t ^ (c - 1))) = 1 := by exact_mod_cast hreal
  change (↑(A⁻¹ * t ^ (1 - c)) : ℂ) * (-Complex.I) *
      (↑(A * t ^ (c - 1)) * Complex.I) = 1
  calc
    (↑(A⁻¹ * t ^ (1 - c)) : ℂ) * (-Complex.I) *
        (↑(A * t ^ (c - 1)) * Complex.I) =
        (↑(A⁻¹ * t ^ (1 - c)) : ℂ) * ↑(A * t ^ (c - 1)) *
          ((-Complex.I) * Complex.I) := by ring
    _ = 1 := by rw [hcomplex]; norm_num [Complex.I_mul_I]

/-- Integration by parts for the oscillatory phase on a positive interval.
This identity is the analytic core of the large-frequency estimate. -/
theorem fractionalPhaseIntegral_integrationByParts
    {c lam a : ℝ} (hc : 1 < c) (hlam : lam ≠ 0) (ha : 0 < a)
    (ha1 : a ≤ 1) :
    (∫ t in a..(1 : ℝ), unitFrequencyPhase (lam * t ^ c)) =
      fractionalPhaseAmplitude c lam 1 * unitFrequencyPhase (lam * 1 ^ c) -
        fractionalPhaseAmplitude c lam a * unitFrequencyPhase (lam * a ^ c) -
        ∫ t in a..(1 : ℝ), fractionalPhaseAmplitudeDeriv c lam t *
          unitFrequencyPhase (lam * t ^ c) := by
  have hAmpCont := continuousOn_fractionalPhaseAmplitude (c := c) (lam := lam) ha
  have hAmpDerivCont :=
    continuousOn_fractionalPhaseAmplitudeDeriv (c := c) (lam := lam) ha
  have hPowCont : Continuous (fun t : ℝ => t ^ c) :=
    Real.continuous_rpow_const (by linarith)
  have hPhaseCont : ContinuousOn (fun t : ℝ => unitFrequencyPhase (lam * t ^ c))
      (Set.uIcc a 1) :=
    (continuous_unitFrequencyPhase.comp (continuous_const.mul hPowCont)).continuousOn
  have hPhaseDerivCont :=
    continuousOn_fractionalPhaseDerivative (c := c) (lam := lam) (a := a) hc
  have hAmpDeriv : ∀ t ∈ Set.Ioo (min a 1) (max a 1),
      HasDerivAt (fun x : ℝ => fractionalPhaseAmplitude c lam x)
        (fractionalPhaseAmplitudeDeriv c lam t) t := by
    intro t ht
    have ht' : t ∈ Set.Ioo a 1 := by
      simpa [min_eq_left ha1, max_eq_right ha1] using ht
    exact hasDerivAt_fractionalPhaseAmplitude (c := c) (lam := lam) (t := t)
      (ne_of_gt (lt_trans ha ht'.1))
  have hPhaseDeriv : ∀ t ∈ Set.Ioo (min a 1) (max a 1),
      HasDerivAt (fun x : ℝ => unitFrequencyPhase (lam * x ^ c))
        (fractionalPhaseDerivative c lam t) t := by
    intro t ht
    have ht' : t ∈ Set.Ioo a 1 := by
      simpa [min_eq_left ha1, max_eq_right ha1] using ht
    exact hasDerivAt_fractionalPhaseDerivative (c := c) (lam := lam) (t := t)
      (ne_of_gt (lt_trans ha ht'.1))
  have hAmpDerivInt : IntervalIntegrable
      (fun t : ℝ => fractionalPhaseAmplitudeDeriv c lam t) MeasureTheory.volume a 1 :=
    hAmpDerivCont.intervalIntegrable
  have hPhaseDerivInt : IntervalIntegrable
      (fun t : ℝ => fractionalPhaseDerivative c lam t) MeasureTheory.volume a 1 :=
    hPhaseDerivCont.intervalIntegrable
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hAmpCont hPhaseCont hAmpDeriv hPhaseDeriv hAmpDerivInt hPhaseDerivInt
  have hprod : ∀ t ∈ Set.uIcc a 1,
      fractionalPhaseAmplitude c lam t * fractionalPhaseDerivative c lam t =
        unitFrequencyPhase (lam * t ^ c) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (lt_min ha zero_lt_one) ht.1
    calc
      fractionalPhaseAmplitude c lam t * fractionalPhaseDerivative c lam t =
          unitFrequencyPhase (lam * t ^ c) *
            (fractionalPhaseAmplitude c lam t *
              ((↑(2 * Real.pi * lam * c * t ^ (c - 1)) : ℂ) * Complex.I)) := by
                simp [fractionalPhaseDerivative]
                ring
      _ = unitFrequencyPhase (lam * t ^ c) := by
        rw [fractionalPhaseAmplitude_mul_phaseDerivative_eq_one
          (lt_trans zero_lt_one hc) hlam htpos]
        simp
  have hcongr :
      (∫ t in a..(1 : ℝ), fractionalPhaseAmplitude c lam t *
        fractionalPhaseDerivative c lam t) =
        (∫ t in a..(1 : ℝ), unitFrequencyPhase (lam * t ^ c)) := by
    apply intervalIntegral.integral_congr
    exact hprod
  calc
    (∫ t in a..(1 : ℝ), unitFrequencyPhase (lam * t ^ c)) =
        (∫ t in a..(1 : ℝ), fractionalPhaseAmplitude c lam t *
          fractionalPhaseDerivative c lam t) := hcongr.symm
    _ = _ := hIBP

/-- Norm of the reciprocal phase amplitude at a positive point. -/
theorem norm_fractionalPhaseAmplitude {c lam t : ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (ht : 0 < t) :
    ‖fractionalPhaseAmplitude c lam t‖ =
      (2 * Real.pi * lam * c)⁻¹ * t ^ (1 - c) := by
  have hA : 0 < 2 * Real.pi * lam * c := by positivity
  have hp : 0 < t ^ (1 - c) := Real.rpow_pos_of_pos ht _
  rw [fractionalPhaseAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_neg, Complex.norm_I, mul_one, abs_mul,
    abs_of_pos (inv_pos.mpr hA), abs_of_pos hp]

/-- Norm of the derivative of the reciprocal phase amplitude. -/
theorem norm_fractionalPhaseAmplitudeDeriv {c lam t : ℝ}
    (hc : 1 < c) (hlam : 0 < lam) (ht : 0 < t) :
    ‖fractionalPhaseAmplitudeDeriv c lam t‖ =
      (2 * Real.pi * lam * c)⁻¹ * (c - 1) * t ^ (-c) := by
  have hA : 0 < 2 * Real.pi * lam * c := by positivity
  have hpow : 0 < t ^ (-c) := Real.rpow_pos_of_pos ht _
  rw [fractionalPhaseAmplitudeDeriv, norm_mul, norm_neg, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hA),
    abs_mul, abs_of_neg (by linarith : 1 - c < 0), abs_of_pos hpow]
  ring

/-- Bound the derivative-amplitude remainder in the integration-by-parts
identity. This standalone estimate is independent of endpoint terms and the
stationary-cutoff algebra. -/
theorem fractionalPhaseAmplitudeDerivIntegral_le
    {c lam a : ℝ} (hc : 1 < c) (hlam : 0 < lam) (ha : 0 < a)
    (ha1 : a ≤ 1) :
    ‖∫ t in a..(1 : ℝ),
      fractionalPhaseAmplitudeDeriv c lam t * unitFrequencyPhase (lam * t ^ c)‖ ≤
      (2 * Real.pi * lam * c)⁻¹ * (a ^ (1 - c) - 1) := by
  let A : ℝ := 2 * Real.pi * lam * c
  have hzero : (0 : ℝ) ∉ Set.uIcc a (1 : ℝ) :=
    Set.notMem_uIcc_of_lt ha (by norm_num)
  have hrpowInt : IntervalIntegrable (fun t : ℝ => t ^ (-c))
      MeasureTheory.volume a 1 :=
    intervalIntegral.intervalIntegrable_rpow (μ := MeasureTheory.volume)
      (a := a) (b := 1) (Or.inr hzero)
  have hboundInt : IntervalIntegrable (fun t : ℝ => A⁻¹ * (c - 1) * t ^ (-c))
      MeasureTheory.volume a 1 := by
    exact hrpowInt.const_mul (A⁻¹ * (c - 1))
  have hremNorm : ‖∫ t in a..(1 : ℝ),
      fractionalPhaseAmplitudeDeriv c lam t * unitFrequencyPhase (lam * t ^ c)‖ ≤
      ∫ t in a..(1 : ℝ), A⁻¹ * (c - 1) * t ^ (-c) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ha1
    · filter_upwards [] with t ht
      have htpos : 0 < t := lt_trans ha ht.1
      have hpoint : ‖fractionalPhaseAmplitudeDeriv c lam t *
          unitFrequencyPhase (lam * t ^ c)‖ = A⁻¹ * (c - 1) * t ^ (-c) := by
        rw [norm_mul, norm_fractionalPhaseAmplitudeDeriv hc hlam htpos,
          norm_unitFrequencyPhase]
        simp [A]
      exact hpoint.le
    · simpa [A] using hboundInt
  have hremEval : (∫ t in a..(1 : ℝ), A⁻¹ * (c - 1) * t ^ (-c)) =
      A⁻¹ * (a ^ (1 - c) - 1) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow_neg_c_on_pos_interval hc ha]
    field_simp [ne_of_gt (sub_pos.mpr hc)]
  calc
    ‖∫ t in a..(1 : ℝ),
        fractionalPhaseAmplitudeDeriv c lam t * unitFrequencyPhase (lam * t ^ c)‖ ≤
        ∫ t in a..(1 : ℝ), A⁻¹ * (c - 1) * t ^ (-c) := hremNorm
    _ = A⁻¹ * (a ^ (1 - c) - 1) := hremEval
    _ = (2 * Real.pi * lam * c)⁻¹ * (a ^ (1 - c) - 1) := by rfl

/-- Exact scalar reduction of the two endpoint terms and the remainder
bound using the stationary cutoff relation. -/
theorem fractionalPhaseEndpointRemainder_eq
    {c lam a : ℝ} (hc : 1 < c) (hlam : 0 < lam) (ha : 0 < a)
    (hstationary : lam * a ^ c = 1) :
    (2 * Real.pi * lam * c)⁻¹ +
      (2 * Real.pi * lam * c)⁻¹ * a ^ (1 - c) +
      (2 * Real.pi * lam * c)⁻¹ * (a ^ (1 - c) - 1) =
      a / (Real.pi * c) := by
  let A : ℝ := 2 * Real.pi * lam * c
  have hcpos : 0 < c := by linarith
  have hLamInv : lam⁻¹ = a ^ c := by
    field_simp [hlam]
    nlinarith [hstationary]
  have hpowadd : a ^ c * a ^ (1 - c) = a := by
    rw [← Real.rpow_add ha, show c + (1 - c) = 1 by ring, Real.rpow_one]
  have hcoeff : A⁻¹ = (2 * Real.pi * c)⁻¹ * lam⁻¹ := by
    dsimp [A]
    field_simp [hlam, Real.pi_ne_zero, hcpos.ne']
  have hscale : A⁻¹ * a ^ (1 - c) = a / (2 * Real.pi * c) := by
    calc
      A⁻¹ * a ^ (1 - c) = (2 * Real.pi * c)⁻¹ *
          (lam⁻¹ * a ^ (1 - c)) := by rw [hcoeff]; ring
      _ = (2 * Real.pi * c)⁻¹ * (a ^ c * a ^ (1 - c)) := by rw [hLamInv]
      _ = (2 * Real.pi * c)⁻¹ * a := by rw [hpowadd]
      _ = a / (2 * Real.pi * c) := by rw [div_eq_mul_inv, mul_comm]
  calc
    (2 * Real.pi * lam * c)⁻¹ +
        (2 * Real.pi * lam * c)⁻¹ * a ^ (1 - c) +
        (2 * Real.pi * lam * c)⁻¹ * (a ^ (1 - c) - 1) =
        2 * (A⁻¹ * a ^ (1 - c)) := by dsimp [A]; ring
    _ = a / (Real.pi * c) := by rw [hscale]; field_simp


/- The assembly theorem is active again now that its derivative-remainder
estimate and endpoint/cutoff scalar reduction have both been isolated and
checked independently. -/
/-- The positive-interval oscillatory tail has the expected endpoint-scale
decay under the stationary cutoff relation `lam * a ^ c = 1`. -/
theorem norm_fractionalPhaseIntegral_tail_le
    {c lam a : ℝ} (hc : 1 < c) (hlam : 0 < lam) (ha : 0 < a)
    (ha1 : a ≤ 1) (hstationary : lam * a ^ c = 1) :
    ‖∫ t in a..(1 : ℝ), unitFrequencyPhase (lam * t ^ c)‖ ≤
      a / (Real.pi * c) := by
  have hcpos : 0 < c := by linarith
  have hrem := fractionalPhaseAmplitudeDerivIntegral_le hc hlam ha ha1
  have hremSet : ‖∫ t in Set.Ioc a (1 : ℝ),
      fractionalPhaseAmplitudeDeriv c lam t * unitFrequencyPhase (lam * t ^ c)‖ ≤
      (2 * Real.pi * lam * c)⁻¹ * (a ^ (1 - c) - 1) := by
    simpa only [intervalIntegral.integral_of_le ha1] using hrem
  have hEndOne : ‖fractionalPhaseAmplitude c lam 1 *
      unitFrequencyPhase (lam * 1 ^ c)‖ = (2 * Real.pi * lam * c)⁻¹ := by
    rw [norm_mul, norm_unitFrequencyPhase,
      norm_fractionalPhaseAmplitude hcpos hlam one_pos]
    simp [Real.one_rpow]
  have hEndA : ‖fractionalPhaseAmplitude c lam a *
      unitFrequencyPhase (lam * a ^ c)‖ =
      (2 * Real.pi * lam * c)⁻¹ * a ^ (1 - c) := by
    rw [norm_mul, norm_unitFrequencyPhase,
      norm_fractionalPhaseAmplitude hcpos hlam ha]
    simp
  have hIBP := fractionalPhaseIntegral_integrationByParts hc hlam.ne' ha ha1
  have hIBPSet := hIBP
  simp only [intervalIntegral.integral_of_le ha1] at hIBPSet
  have hbound : ‖∫ t in a..(1 : ℝ), unitFrequencyPhase (lam * t ^ c)‖ ≤
      (2 * Real.pi * lam * c)⁻¹ +
        (2 * Real.pi * lam * c)⁻¹ * a ^ (1 - c) +
        (2 * Real.pi * lam * c)⁻¹ * (a ^ (1 - c) - 1) := by
    rw [intervalIntegral.integral_of_le ha1, hIBPSet]
    calc
      _ ≤ (‖fractionalPhaseAmplitude c lam 1 *
            unitFrequencyPhase (lam * 1 ^ c)‖ +
          ‖fractionalPhaseAmplitude c lam a *
            unitFrequencyPhase (lam * a ^ c)‖) +
          ‖∫ t in Set.Ioc a (1 : ℝ), fractionalPhaseAmplitudeDeriv c lam t *
            unitFrequencyPhase (lam * t ^ c)‖ := by
              calc
                _ ≤ ‖fractionalPhaseAmplitude c lam 1 *
                      unitFrequencyPhase (lam * 1 ^ c) -
                      fractionalPhaseAmplitude c lam a *
                        unitFrequencyPhase (lam * a ^ c)‖ +
                    ‖∫ t in Set.Ioc a (1 : ℝ), fractionalPhaseAmplitudeDeriv c lam t *
                      unitFrequencyPhase (lam * t ^ c)‖ := norm_sub_le _ _
                _ ≤ _ := add_le_add (norm_sub_le _ _) (le_refl _)
      _ = ((2 * Real.pi * lam * c)⁻¹ +
          (2 * Real.pi * lam * c)⁻¹ * a ^ (1 - c)) +
          ‖∫ t in Set.Ioc a (1 : ℝ), fractionalPhaseAmplitudeDeriv c lam t *
            unitFrequencyPhase (lam * t ^ c)‖ := by rw [hEndOne, hEndA]
      _ ≤ _ := add_le_add (le_refl _) hremSet
  calc
    ‖∫ t in a..(1 : ℝ), unitFrequencyPhase (lam * t ^ c)‖ ≤
        (2 * Real.pi * lam * c)⁻¹ +
          (2 * Real.pi * lam * c)⁻¹ * a ^ (1 - c) +
          (2 * Real.pi * lam * c)⁻¹ * (a ^ (1 - c) - 1) := hbound
    _ = a / (Real.pi * c) :=
      fractionalPhaseEndpointRemainder_eq hc hlam ha hstationary

/-- Splitting the unit interval at a stationary cutoff costs only the length
of the initial segment, in addition to the integration-by-parts tail bound. -/
theorem norm_fractionalPhaseIntegral_unit_cutoff_le
    {c lam a : ℝ} (hc : 1 < c) (hlam : 0 < lam) (ha : 0 < a)
    (ha1 : a ≤ 1) (hstationary : lam * a ^ c = 1) :
    ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase (lam * t ^ c)‖ ≤
      a + a / (Real.pi * c) := by
  let f : ℝ → ℂ := fun t => unitFrequencyPhase (lam * t ^ c)
  have hpow : Continuous (fun t : ℝ => t ^ c) :=
    continuous_real_rpow_of_one_lt hc
  have hf : Continuous f := by
    dsimp [f]
    unfold unitFrequencyPhase
    fun_prop
  have h0a : IntervalIntegrable f MeasureTheory.volume 0 a :=
    hf.intervalIntegrable _ _
  have ha1i : IntervalIntegrable f MeasureTheory.volume a 1 :=
    hf.intervalIntegrable _ _
  have hshort : ‖∫ t in (0 : ℝ)..a, f t‖ ≤ a := by
    have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
        MeasureTheory.volume 0 a := intervalIntegrable_const
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le ha.le
      (f := f) (g := fun _ : ℝ => (1 : ℝ))
      (by
        filter_upwards [] with t ht
        simp [f, norm_unitFrequencyPhase])
      hconst
    calc
      ‖∫ t in (0 : ℝ)..a, f t‖ ≤ ∫ t in (0 : ℝ)..a, (1 : ℝ) := hnorm
      _ = a := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0a ha1i
  have htail := norm_fractionalPhaseIntegral_tail_le hc hlam ha ha1 hstationary
  have htail' : ‖∫ t in a..(1 : ℝ), f t‖ ≤ a / (Real.pi * c) := by
    simpa [f] using htail
  calc
    ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase (lam * t ^ c)‖ =
        ‖(∫ t in (0 : ℝ)..a, f t) + ∫ t in a..1, f t‖ := by
          rw [← hsplit]
    _ ≤ ‖∫ t in (0 : ℝ)..a, f t‖ + ‖∫ t in a..1, f t‖ := norm_add_le _ _
    _ ≤ a + a / (Real.pi * c) := add_le_add hshort htail'

/-- Positive-frequency unit-scale decay obtained from the stationary
cutoff `lam^(-1/c)`. -/
theorem norm_fractionalPhaseIntegral_unit_le_of_one_le
    {c lam : ℝ} (hc : 1 < c) (hlam : 0 < lam) (hlam1 : 1 ≤ lam) :
    ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase (lam * t ^ c)‖ ≤
      (1 + (Real.pi * c)⁻¹) * lam ^ (-c⁻¹) := by
  let a : ℝ := lam ^ (-c⁻¹)
  have hcpos : 0 < c := by linarith
  have ha : 0 < a := by
    dsimp [a]
    exact Real.rpow_pos_of_pos hlam _
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply Real.rpow_le_one_of_one_le_of_nonpos hlam1
    exact neg_nonpos.mpr (inv_nonneg.mpr hcpos.le)
  have hpow : a ^ c = lam⁻¹ := by
    dsimp [a]
    rw [← Real.rpow_mul hlam.le,
      show -c⁻¹ * c = -1 by
        rw [neg_mul, inv_mul_cancel₀ hcpos.ne'],
      Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
  have hstationary : lam * a ^ c = 1 := by
    rw [hpow]
    exact mul_inv_cancel₀ hlam.ne'
  have hunit := norm_fractionalPhaseIntegral_unit_cutoff_le hc hlam ha ha1 hstationary
  calc
    ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase (lam * t ^ c)‖ ≤
        a + a / (Real.pi * c) := hunit
    _ = (1 + (Real.pi * c)⁻¹) * lam ^ (-c⁻¹) := by
      dsimp [a]
      field_simp [Real.pi_ne_zero, hcpos.ne']

/-- The norm of the unit-interval phase integral is even in the frequency. -/
theorem norm_fractionalPhaseIntegral_unit_neg_eq
    (c lam : ℝ) :
    ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase ((-lam) * t ^ c)‖ =
      ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase (lam * t ^ c)‖ := by
  have hphase (t : ℝ) :
      unitFrequencyPhase ((-lam) * t ^ c) =
        starRingEnd ℂ (unitFrequencyPhase (lam * t ^ c)) := by
    calc
      unitFrequencyPhase ((-lam) * t ^ c) =
          unitFrequencyPhase (-(lam * t ^ c)) := by congr 1; ring
      _ = starRingEnd ℂ (unitFrequencyPhase (lam * t ^ c)) :=
        unitFrequencyPhase_neg_eq_conj _
  have hint :
      (∫ t in (0 : ℝ)..1, unitFrequencyPhase ((-lam) * t ^ c)) =
        ∫ t in (0 : ℝ)..1,
          starRingEnd ℂ (unitFrequencyPhase (lam * t ^ c)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hphase t
  calc
    ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase ((-lam) * t ^ c)‖ =
        ‖starRingEnd ℂ (∫ t in (0 : ℝ)..1,
          unitFrequencyPhase (lam * t ^ c))‖ := by
      rw [hint, intervalIntegral.intervalIntegral_conj]
    _ = ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase (lam * t ^ c)‖ := by
      simp

/-- The unit-interval phase integral has the trivial absolute bound one. -/
theorem norm_fractionalPhaseIntegral_unit_le_one (c lam : ℝ) :
    ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase (lam * t ^ c)‖ ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := 1)
    (f := fun t : ℝ => unitFrequencyPhase (lam * t ^ c))
    (by
      intro t ht
      exact (norm_unitFrequencyPhase _).le)
  simpa using h

/-- Unit-scale decay for either sign of a frequency of magnitude at least
one. -/
theorem norm_fractionalPhaseIntegral_unit_le_of_abs_ge_one
    {c lam : ℝ} (hc : 1 < c) (hlam : 1 ≤ |lam|) :
    ‖∫ t in (0 : ℝ)..1, unitFrequencyPhase (lam * t ^ c)‖ ≤
      (1 + (Real.pi * c)⁻¹) * |lam| ^ (-c⁻¹) := by
  rcases lt_or_ge lam 0 with hlamNeg | hlamNonneg
  · have hlamPos : 0 < -lam := by linarith
    have habs : |lam| = -lam := abs_of_neg hlamNeg
    have hlarge : 1 ≤ -lam := by simpa [habs] using hlam
    have hpositive := norm_fractionalPhaseIntegral_unit_le_of_one_le hc hlamPos hlarge
    have hsymm := norm_fractionalPhaseIntegral_unit_neg_eq c (-lam)
    simpa [habs] using hsymm.trans_le hpositive
  · have habs : |lam| = lam := abs_of_nonneg hlamNonneg
    have hlarge : 1 ≤ lam := by simpa [habs] using hlam
    have hlamPos : 0 < lam := lt_of_lt_of_le zero_lt_one hlarge
    have hpositive := norm_fractionalPhaseIntegral_unit_le_of_one_le hc hlamPos
      hlarge
    simpa [habs] using hpositive

/-- The normalized continuous model obeys the blueprint's small- and
large-frequency bound, with an explicit admissible constant. -/
theorem continuousFractionalModel_norm_le_min
    {c N ξ : ℝ} (hc : 1 < c) (hN : 0 < N) (hξ : ξ ≠ 0) :
    ‖continuousFractionalModel c N ξ‖ ≤
      (1 + (Real.pi * c)⁻¹) *
        min 1 ((|ξ| * N ^ c) ^ (-c⁻¹)) := by
  have hcpos : 0 < c := by linarith
  have hNpow : 0 < N ^ c := Real.rpow_pos_of_pos hN c
  let y : ℝ := |ξ| * N ^ c
  have hypos : 0 < y := by
    dsimp [y]
    exact mul_pos (abs_pos.mpr hξ) hNpow
  have hfreqAbs : |ξ * N ^ c| = y := by
    dsimp [y]
    rw [abs_mul, abs_of_pos hNpow]
  have hexp : -c⁻¹ ≤ 0 := neg_nonpos.mpr (inv_nonneg.mpr hcpos.le)
  have hpc : 0 < Real.pi * c := mul_pos Real.pi_pos hcpos
  have hC : 1 ≤ 1 + (Real.pi * c)⁻¹ := by
    have hinv : 0 < (Real.pi * c)⁻¹ := inv_pos.mpr hpc
    linarith
  by_cases hy : y ≤ 1
  · have hpow : 1 ≤ y ^ (-c⁻¹) := by
      rw [← Real.one_rpow (-c⁻¹)]
      exact Real.rpow_le_rpow_of_nonpos hypos hy hexp
    rw [continuousFractionalModel_eq_unitIntegral hN, min_eq_left hpow]
    calc
      ‖∫ u in (0 : ℝ)..1,
          unitFrequencyPhase ((ξ * N ^ c) * u ^ c)‖ ≤ 1 :=
        norm_fractionalPhaseIntegral_unit_le_one c (ξ * N ^ c)
      _ ≤ (1 + (Real.pi * c)⁻¹) * 1 := by simpa using hC
  · have hyone : 1 ≤ y := le_of_not_ge hy
    have hpow : y ^ (-c⁻¹) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hyone hexp
    have hfreqLarge : 1 ≤ |ξ * N ^ c| := by rw [hfreqAbs]; exact hyone
    have hlarge := norm_fractionalPhaseIntegral_unit_le_of_abs_ge_one hc hfreqLarge
    rw [continuousFractionalModel_eq_unitIntegral hN, min_eq_right hpow]
    simpa [hfreqAbs] using hlarge

/-- The blueprint's `1/c` decay implies the paper's weaker
`1/ceil(c)` decay for frequencies of magnitude at least one, and the minima
agree in the small-frequency range. -/
theorem min_one_rpow_neg_inv_le_ceil {c x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    min 1 (x ^ (-c⁻¹)) ≤ min 1 (x ^ (-(Nat.ceil c : ℝ)⁻¹)) := by
  have hcpos : 0 < c := by linarith
  have hceil : c ≤ (Nat.ceil c : ℝ) := Nat.le_ceil c
  have hceilpos : 0 < (Nat.ceil c : ℝ) := lt_of_lt_of_le hcpos hceil
  have hrecip : (Nat.ceil c : ℝ)⁻¹ ≤ c⁻¹ :=
    (inv_le_inv₀ hceilpos hcpos).2 hceil
  have hexp : -c⁻¹ ≤ -(Nat.ceil c : ℝ)⁻¹ := by linarith
  have hcExp : -c⁻¹ ≤ 0 := neg_nonpos.mpr (inv_nonneg.mpr hcpos.le)
  have hceilExp : -(Nat.ceil c : ℝ)⁻¹ ≤ 0 :=
    neg_nonpos.mpr (inv_nonneg.mpr hceilpos.le)
  by_cases hxone : x ≤ 1
  · have hsmallC : 1 ≤ x ^ (-c⁻¹) := by
      rw [← Real.one_rpow (-c⁻¹)]
      exact Real.rpow_le_rpow_of_nonpos hx hxone hcExp
    have hsmallCeil : 1 ≤ x ^ (-(Nat.ceil c : ℝ)⁻¹) := by
      rw [← Real.one_rpow (-(Nat.ceil c : ℝ)⁻¹)]
      exact Real.rpow_le_rpow_of_nonpos hx hxone hceilExp
    rw [min_eq_left hsmallC, min_eq_left hsmallCeil]
  · have hxlarge : 1 ≤ x := le_of_not_ge hxone
    have hlargeC : x ^ (-c⁻¹) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hxlarge hcExp
    have hlargeCeil : x ^ (-(Nat.ceil c : ℝ)⁻¹) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hxlarge hceilExp
    rw [min_eq_right hlargeC, min_eq_right hlargeCeil]
    exact Real.rpow_le_rpow_of_exponent_le hxlarge hexp

/-- Paper-exponent version of the continuous-model estimate, derived without
changing the blueprint's stronger `1/c` theorem. -/
theorem continuousFractionalModel_norm_le_paper_min
    {c N ξ : ℝ} (hc : 1 < c) (hN : 0 < N) (hξ : ξ ≠ 0) :
    ‖continuousFractionalModel c N ξ‖ ≤
      (1 + (Real.pi * c)⁻¹) *
        min 1 ((|ξ| * N ^ c) ^ (-(Nat.ceil c : ℝ)⁻¹)) := by
  have hstrong := continuousFractionalModel_norm_le_min hc hN hξ
  have hmin := min_one_rpow_neg_inv_le_ceil hc
    (mul_pos (abs_pos.mpr hξ) (Real.rpow_pos_of_pos hN c))
  exact hstrong.trans (mul_le_mul_of_nonneg_left hmin (by positivity))

/-- The paper's negative phase convention has the same model norm, by
complex conjugation. -/
theorem continuousFractionalModel_neg_norm_eq {c N ξ : ℝ} (hN : 0 < N) :
    ‖continuousFractionalModel c N (-ξ)‖ =
      ‖continuousFractionalModel c N ξ‖ := by
  have hleft := continuousFractionalModel_eq_unitIntegral
    (c := c) (N := N) (ξ := -ξ) hN
  have hright := continuousFractionalModel_eq_unitIntegral
    (c := c) (N := N) (ξ := ξ) hN
  have harg : -ξ * N ^ c = -(ξ * N ^ c) := by ring
  calc
    ‖continuousFractionalModel c N (-ξ)‖ =
        ‖∫ u in (0 : ℝ)..1,
          unitFrequencyPhase ((-ξ * N ^ c) * u ^ c)‖ := by rw [hleft]
    _ = ‖∫ u in (0 : ℝ)..1,
          unitFrequencyPhase (-(ξ * N ^ c) * u ^ c)‖ := by rw [harg]
    _ = ‖∫ u in (0 : ℝ)..1,
          unitFrequencyPhase ((ξ * N ^ c) * u ^ c)‖ :=
        norm_fractionalPhaseIntegral_unit_neg_eq c (ξ * N ^ c)
    _ = ‖continuousFractionalModel c N ξ‖ := by rw [hright]

/-- On `[0,N]`, the fractional power has the derivative bound needed to
compare a sampled phase with its integral over a block. -/
theorem abs_rpow_sub_le_c_mul_rpow_sub {c x y N : ℝ}
    (hc : 1 < c) (hx : 0 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N) :
    |y ^ c - x ^ c| ≤ c * N ^ (c - 1) * (y - x) := by
  by_cases hxeq : x = y
  · subst y
    simp
  have hxy' : x < y := lt_of_le_of_ne hxy hxeq
  have hNpos : 0 < N := lt_of_lt_of_le (lt_of_le_of_lt hx hxy') hyN
  have hcont : ContinuousOn (fun t : ℝ => t ^ c) (Set.Icc x y) :=
    continuousOn_id.rpow_const (fun t ht =>
      Or.inr (le_of_lt (lt_trans zero_lt_one hc)))
  have hdiff : DifferentiableOn ℝ (fun z : ℝ => z ^ c) (Set.Ioo x y) := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_le_of_lt hx ht.1)))).differentiableAt.differentiableWithinAt
  obtain ⟨z, hz, hderiv⟩ := exists_deriv_eq_slope (fun t : ℝ => t ^ c)
    hxy' hcont hdiff
  have hzpos : 0 < z := lt_of_le_of_lt hx hz.1
  have hzN : z ≤ N := le_trans hz.2.le hyN
  have hderivval : deriv (fun t : ℝ => t ^ c) z = c * z ^ (c - 1) :=
    Real.deriv_rpow_const z c
  have hpowmono : z ^ (c - 1) ≤ N ^ (c - 1) :=
    Real.rpow_le_rpow (le_of_lt hzpos) hzN (by linarith)
  have hnonneg : 0 ≤ c * z ^ (c - 1) := by positivity
  have hbound : |deriv (fun t : ℝ => t ^ c) z| ≤ c * N ^ (c - 1) := by
    rw [hderivval, abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_left hpowmono (le_of_lt (lt_trans zero_lt_one hc))
  rw [hderiv] at hbound
  rw [abs_div, abs_of_pos (sub_pos.mpr hxy')] at hbound
  have hdelta : 0 ≤ y ^ c - x ^ c := by
    exact sub_nonneg.mpr (Real.rpow_le_rpow hx hxy
      (le_of_lt (lt_trans zero_lt_one hc)))
  rw [abs_of_nonneg hdelta] at hbound
  rw [abs_of_nonneg hdelta]
  exact (div_le_iff₀ (sub_pos.mpr hxy')).mp hbound

/-- Unit-frequency phase is Lipschitz in its real argument with the
elementary chord bound used in the low-frequency progression case. -/
theorem norm_unitFrequencyPhase_mul_sub_le (ξ x y : ℝ) :
    ‖unitFrequencyPhase (ξ * x) - unitFrequencyPhase (ξ * y)‖ ≤
      2 * Real.pi * |ξ| * |x - y| := by
  have harg : ξ * x = ξ * y + ξ * (x - y) := by ring
  rw [harg, unitFrequencyPhase_add]
  calc
    ‖unitFrequencyPhase (ξ * y) * unitFrequencyPhase (ξ * (x - y)) -
        unitFrequencyPhase (ξ * y)‖ =
        ‖unitFrequencyPhase (ξ * y) *
          (unitFrequencyPhase (ξ * (x - y)) - 1)‖ := by congr 1 <;> ring
    _ = ‖unitFrequencyPhase (ξ * (x - y)) - 1‖ := by
      rw [norm_mul, norm_unitFrequencyPhase, one_mul]
    _ ≤ 2 * Real.pi * |ξ| * |x - y| := by
      simpa [abs_mul] using
        (norm_unitFrequencyPhase_rpow_sub_one_le 1 ξ (x - y))

/-- Pointwise phase comparison on one low-frequency progression block,
including the integer-floor displacement. -/
theorem norm_floor_monomial_phase_sub_rpow_le
    {c ξ x y d N : ℝ} (hc : 1 < c) (hx : 0 ≤ x) (hyx : y ≤ x)
    (hy : 0 ≤ y) (hxN : x ≤ N) (hgap : x - y ≤ d) (hd : 0 ≤ d) :
    ‖unitFrequencyPhase (ξ * ((Int.floor (x ^ c) : ℤ) : ℝ)) -
        unitFrequencyPhase (ξ * y ^ c)‖ ≤
      2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) := by
  have hfloorLo : ((Int.floor (x ^ c) : ℤ) : ℝ) ≤ x ^ c := by
    exact_mod_cast (Int.floor_le (x ^ c))
  have hfloorHi : x ^ c < ((Int.floor (x ^ c) : ℤ) : ℝ) + 1 := by
    exact_mod_cast (Int.lt_floor_add_one (x ^ c))
  have hfloorAbs :
      |((Int.floor (x ^ c) : ℤ) : ℝ) - x ^ c| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hpow : |x ^ c - y ^ c| ≤ c * N ^ (c - 1) * (x - y) :=
    abs_rpow_sub_le_c_mul_rpow_sub hc hy hyx hxN
  have hcoeff : 0 ≤ c * N ^ (c - 1) := by
    have hN : 0 ≤ N := le_trans hx hxN
    positivity
  have hvalue :
      |((Int.floor (x ^ c) : ℤ) : ℝ) - y ^ c| ≤
        1 + c * N ^ (c - 1) * d := by
    calc
      |((Int.floor (x ^ c) : ℤ) : ℝ) - y ^ c| ≤
          |((Int.floor (x ^ c) : ℤ) : ℝ) - x ^ c| + |x ^ c - y ^ c| :=
        abs_sub_le _ _ _
      _ ≤ 1 + c * N ^ (c - 1) * (x - y) := add_le_add hfloorAbs hpow
      _ ≤ 1 + c * N ^ (c - 1) * d := by
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left hgap hcoeff) 1
  calc
    ‖unitFrequencyPhase (ξ * ((Int.floor (x ^ c) : ℤ) : ℝ)) -
        unitFrequencyPhase (ξ * y ^ c)‖ ≤
      2 * Real.pi * |ξ| *
        |((Int.floor (x ^ c) : ℤ) : ℝ) - y ^ c| :=
      norm_unitFrequencyPhase_mul_sub_le ξ _ _
    _ ≤ 2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) := by
      gcongr

/-- Integral comparison on one complete low-frequency block, with the
sampled endpoint phase and floor error included. -/
theorem norm_floor_monomial_phase_block_integral_le
    {c ξ x y d N : ℝ} (hc : 1 < c) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hxN : x ≤ N) (hgap : x - y ≤ d) (hd : 0 ≤ d) :
    ‖(x - y) • unitFrequencyPhase (ξ * ((Int.floor (x ^ c) : ℤ) : ℝ)) -
        ∫ t in y..x, unitFrequencyPhase (ξ * t ^ c)‖ ≤
      (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * (x - y) := by
  have hx : 0 ≤ x := le_trans hy hyx
  have hpoint := norm_floor_monomial_phase_sub_rpow_le
    (ξ := ξ) hc hx hyx hy hxN hgap hd
  let z : ℂ := unitFrequencyPhase (ξ * ((Int.floor (x ^ c) : ℤ) : ℝ))
  let f : ℝ → ℂ := fun t => z - unitFrequencyPhase (ξ * t ^ c)
  have hpowCont : Continuous (fun t : ℝ => t ^ c) :=
    Real.continuous_rpow_const (by linarith)
  have hphaseCont : ContinuousOn (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c))
      (Set.Icc y x) :=
    (continuous_unitFrequencyPhase.comp (continuous_const.mul hpowCont)).continuousOn
  have hfCont : ContinuousOn f (Set.Icc y x) := by
    dsimp [f]
    exact continuousOn_const.sub hphaseCont
  have hfInt : IntervalIntegrable f MeasureTheory.volume y x :=
    hfCont.intervalIntegrable_of_Icc hyx
  have hpointwise : ∀ t ∈ Set.uIoc y x, ‖f t‖ ≤
      2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) := by
    intro t ht
    have ht' : t ∈ Set.Ioc y x := by simpa [Set.uIoc_of_le hyx] using ht
    have hyt : 0 ≤ t := le_trans hy ht'.1.le
    have h := norm_floor_monomial_phase_sub_rpow_le
      (ξ := ξ) hc hx ht'.2 hyt hxN (by linarith [ht'.1]) hd
    simpa [f, z] using h
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := y) (b := x) (C := 2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d))
    (f := f) hpointwise
  have hconst : (∫ t in y..x, z) = (x - y) • z := by
    rw [intervalIntegral.integral_const]
  have hphaseInt : IntervalIntegrable
      (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c)) MeasureTheory.volume y x := by
    have hphaseCont' : ContinuousOn
        (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c)) (Set.uIcc y x) := by
      simpa [Set.uIcc_of_le hyx] using hphaseCont
    exact hphaseCont'.intervalIntegrable
  have hsplit : (x - y) • z - ∫ t in y..x,
      unitFrequencyPhase (ξ * t ^ c) = ∫ t in y..x, f t := by
    rw [← hconst, intervalIntegral.integral_sub intervalIntegrable_const hphaseInt]
  rw [hsplit]
  simpa [abs_of_nonneg (sub_nonneg.mpr hyx)] using hbound

/-- Sum of the one-block errors over a complete progression prefix. The
terminal interval beyond `d*L` is deliberately left out for separate control. -/
theorem norm_sum_floor_monomial_phase_block_errors_le
    {c ξ d N : ℝ} (hc : 1 < c) (hd : 0 < d) (hN : 0 ≤ N)
    (L : ℕ) (hLN : d * (L : ℝ) ≤ N) :
    ‖(Finset.Ico 0 L : Finset ℕ).sum (fun i : ℕ =>
        (d * ((Nat.succ i : ℕ) : ℝ) - d * (i : ℝ)) • unitFrequencyPhase
            (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ)) -
          ∫ t in (d * (i : ℝ))..(d * ((Nat.succ i : ℕ) : ℝ)),
            unitFrequencyPhase (ξ * t ^ c))‖ ≤
      (L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d := by
  let E : ℕ → ℂ := fun i =>
    (d * ((Nat.succ i : ℕ) : ℝ) - d * (i : ℝ)) • unitFrequencyPhase
        (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ)) -
      ∫ t in (d * (i : ℝ))..(d * ((Nat.succ i : ℕ) : ℝ)),
        unitFrequencyPhase (ξ * t ^ c)
  have hterms : ∀ i ∈ (Finset.Ico 0 L : Finset ℕ),
      ‖E i‖ ≤ (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d := by
    intro i hi
    have hiL : i < L := (Finset.mem_Ico.mp hi).2
    have hy : 0 ≤ d * (i : ℝ) := by positivity
    have hwidth : d * ((Nat.succ i : ℕ) : ℝ) - d * (i : ℝ) = d := by
      have hiCast : ((Nat.succ i : ℕ) : ℝ) = (i : ℝ) + 1 := by exact_mod_cast Nat.succ_eq_add_one i
      rw [hiCast]
      ring
    have hxy : d * (i : ℝ) ≤ d * ((Nat.succ i : ℕ) : ℝ) := by
      nlinarith [hwidth, hd]
    have hxN : d * ((Nat.succ i : ℕ) : ℝ) ≤ N := by
      have hiPlus : Nat.succ i ≤ L := Nat.succ_le_of_lt hiL
      have hmul := mul_le_mul_of_nonneg_left
        (show ((Nat.succ i : ℕ) : ℝ) ≤ L by exact_mod_cast hiPlus) hd.le
      nlinarith
    have hblock := norm_floor_monomial_phase_block_integral_le
      (ξ := ξ) hc hy hxy hxN (by nlinarith [hwidth]) hd.le
    have hC : 0 ≤ 2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) := by
      have hN' : 0 ≤ N := hN
      positivity
    have hscaled := mul_le_mul_of_nonneg_left
      (show d * ((Nat.succ i : ℕ) : ℝ) - d * (i : ℝ) ≤ d by linarith [hwidth]) hC
    have hblock' : ‖E i‖ ≤
        (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d := by
      simpa [E] using hblock.trans hscaled
    exact hblock'
  calc
    ‖(Finset.Ico 0 L : Finset ℕ).sum E‖ ≤
        (Finset.Ico 0 L : Finset ℕ).sum (fun i => ‖E i‖) := norm_sum_le _ _
    _ ≤ (Finset.Ico 0 L : Finset ℕ).sum (fun _i =>
        (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterms i hi
    _ = (L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d := by
      simp [Finset.sum_const, Nat.card_Ico]
      ring

/-- The continuous-phase integrals over the complete adjacent blocks
telescope to the integral over their union. -/
theorem sum_fractionalPhase_integral_blocks_eq
    {c ξ d : ℝ} (hc : 1 < c) (L : ℕ) :
    ∑ i ∈ Finset.range L,
        ∫ t in (d * (i : ℝ))..(d * ((i + 1 : ℕ) : ℝ)),
          unitFrequencyPhase (ξ * t ^ c) =
      ∫ t in (0 : ℝ)..(d * (L : ℝ)), unitFrequencyPhase (ξ * t ^ c) := by
  have hpow : Continuous (fun t : ℝ => t ^ c) :=
    Real.continuous_rpow_const (by linarith)
  have hphase : Continuous (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c)) :=
    continuous_unitFrequencyPhase.comp (continuous_const.mul hpow)
  have hint : ∀ i < L, IntervalIntegrable
      (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c)) MeasureTheory.volume
      (d * (i : ℝ)) (d * ((i + 1 : ℕ) : ℝ)) := by
    intro i hi
    exact hphase.intervalIntegrable (d * (i : ℝ)) (d * ((i + 1 : ℕ) : ℝ))
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ => unitFrequencyPhase (ξ * t ^ c))
    (μ := MeasureTheory.volume) (a := fun i : ℕ => d * (i : ℝ)) (n := L) hint]
  simp

/-- The continuous phase integral over a terminal interval is bounded by
the interval's length. -/
theorem norm_fractionalPhaseIntegral_interval_le_length
    {c ξ a b : ℝ} (hab : a ≤ b) :
    ‖∫ t in a..b, unitFrequencyPhase (ξ * t ^ c)‖ ≤ b - a := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := (1 : ℝ))
    (f := fun t : ℝ => unitFrequencyPhase (ξ * t ^ c))
    (by
      intro t ht
      exact (norm_unitFrequencyPhase _).le)
  simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using h

/-- Low-frequency prefix comparison before normalization. It retains the
exact terminal interval from `d*L` to `N`. -/
theorem norm_floor_monomial_raw_prefix_sub_integral_le
    {c ξ d N : ℝ} (hc : 1 < c) (hd : 0 < d) (hN : 0 ≤ N)
    (L : ℕ) (hLN : d * (L : ℝ) ≤ N) :
    ‖d • (Finset.Ico 0 L : Finset ℕ).sum
        (fun i => unitFrequencyPhase
          (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
      ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)‖ ≤
      (L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d +
        (N - d * (L : ℝ)) := by
  let P : ℕ → ℂ := fun i => unitFrequencyPhase
    (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))
  let J : ℕ → ℂ := fun i => ∫ t in (d * (i : ℝ))..(d * ((Nat.succ i : ℕ) : ℝ)),
    unitFrequencyPhase (ξ * t ^ c)
  let W : ℕ → ℝ := fun i => d * ((Nat.succ i : ℕ) : ℝ) - d * (i : ℝ)
  let E : ℕ → ℂ := fun i => W i • P i - J i
  have hErr := norm_sum_floor_monomial_phase_block_errors_le
    (c := c) (ξ := ξ) (d := d) (N := N) hc hd hN L hLN
  have hErr' : ‖(Finset.Ico 0 L : Finset ℕ).sum E‖ ≤
      (L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d := by
    simpa [E, W, P, J] using hErr
  have hwidth : ∀ i ∈ (Finset.Ico 0 L : Finset ℕ), W i = d := by
    intro i hi
    dsimp [W]
    have hiCast : ((Nat.succ i : ℕ) : ℝ) = (i : ℝ) + 1 := by
      exact_mod_cast Nat.succ_eq_add_one i
    rw [hiCast]
    ring
  have hsample : (Finset.Ico 0 L : Finset ℕ).sum (fun i => W i • P i) =
      d • (Finset.Ico 0 L : Finset ℕ).sum P := by
    calc
      _ = (Finset.Ico 0 L : Finset ℕ).sum (fun i => d • P i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hwidth i hi]
      _ = d • (Finset.Ico 0 L : Finset ℕ).sum P := by
        rw [Finset.smul_sum]
  have hblocks : (Finset.Ico 0 L : Finset ℕ).sum J =
      ∫ t in (0 : ℝ)..(d * (L : ℝ)), unitFrequencyPhase (ξ * t ^ c) := by
    rw [Nat.Ico_zero_eq_range]
    exact sum_fractionalPhase_integral_blocks_eq (c := c) (ξ := ξ) (d := d) hc L
  have hdecomp : (Finset.Ico 0 L : Finset ℕ).sum E =
      d • (Finset.Ico 0 L : Finset ℕ).sum P -
        ∫ t in (0 : ℝ)..(d * (L : ℝ)), unitFrequencyPhase (ξ * t ^ c) := by
    rw [Finset.sum_sub_distrib, hsample, hblocks]
  have hphaseCont : Continuous (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c)) :=
    continuous_unitFrequencyPhase.comp
      (continuous_const.mul (Real.continuous_rpow_const (by linarith)))
  have hfirstInt : IntervalIntegrable
      (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c)) MeasureTheory.volume 0 (d * (L : ℝ)) :=
    hphaseCont.intervalIntegrable 0 (d * (L : ℝ))
  have hlastInt : IntervalIntegrable
      (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c)) MeasureTheory.volume
      (d * (L : ℝ)) N := hphaseCont.intervalIntegrable (d * (L : ℝ)) N
  have htotal : (∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)) =
      (∫ t in (0 : ℝ)..(d * (L : ℝ)), unitFrequencyPhase (ξ * t ^ c)) +
        ∫ t in (d * (L : ℝ))..N, unitFrequencyPhase (ξ * t ^ c) := by
    exact (intervalIntegral.integral_add_adjacent_intervals hfirstInt hlastInt).symm
  have htail := norm_fractionalPhaseIntegral_interval_le_length
    (c := c) (ξ := ξ) hLN
  have htailNonneg : 0 ≤ N - d * (L : ℝ) := sub_nonneg.mpr hLN
  calc
    _ = ‖((Finset.Ico 0 L : Finset ℕ).sum E) -
        ∫ t in (d * (L : ℝ))..N, unitFrequencyPhase (ξ * t ^ c)‖ := by
      rw [hdecomp, htotal]
      congr 1
      simp only [P, smul_eq_mul, neg_one_mul, one_mul]
      abel_nf
    _ ≤ ‖(Finset.Ico 0 L : Finset ℕ).sum E‖ +
        ‖∫ t in (d * (L : ℝ))..N, unitFrequencyPhase (ξ * t ^ c)‖ := norm_sub_le _ _
    _ ≤ (L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d +
        (N - d * (L : ℝ)) := by
      exact add_le_add hErr' (by simpa using htail)

/-- Specialization of the raw comparison to the exact progression cutoff
`L=floor(N/d)`. -/
theorem norm_floor_monomial_raw_floor_prefix_sub_integral_le
    {c ξ d N : ℝ} (hc : 1 < c) (hd : 0 < d) (hN : 0 ≤ N) :
    let L : ℕ := Nat.floor (N / d)
    ‖d • (Finset.Ico 0 L : Finset ℕ).sum
        (fun i => unitFrequencyPhase
          (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
      ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)‖ ≤
      (L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d +
        (N - d * (L : ℝ)) := by
  dsimp only
  let L : ℕ := Nat.floor (N / d)
  have hq : 0 ≤ N / d := div_nonneg hN hd.le
  have hfloor : (L : ℝ) ≤ N / d := by
    dsimp [L]
    exact Nat.floor_le hq
  have hLN : d * (L : ℝ) ≤ N := by
    calc
      d * (L : ℝ) ≤ d * (N / d) := mul_le_mul_of_nonneg_left hfloor hd.le
      _ = N := by field_simp [ne_of_gt hd]
  exact norm_floor_monomial_raw_prefix_sub_integral_le hc hd hN L hLN

/-- Exact floor remainder bounds for the progression cutoff. -/
theorem nat_floor_progression_remainder_bounds {N d : ℝ}
    (hN : 0 ≤ N) (hd : 0 < d) :
    0 ≤ N - d * (Nat.floor (N / d) : ℝ) ∧
      N - d * (Nat.floor (N / d) : ℝ) < d := by
  have hq : 0 ≤ N / d := div_nonneg hN hd.le
  have hfloor : (Nat.floor (N / d) : ℝ) ≤ N / d := Nat.floor_le hq
  have hfloorUpper : N / d < (Nat.floor (N / d) : ℝ) + 1 :=
    Nat.lt_floor_add_one (N / d)
  have hmulLower := mul_le_mul_of_nonneg_left hfloor hd.le
  have hmulUpper := mul_lt_mul_of_pos_left hfloorUpper hd
  have hcancel : d * (N / d) = N := by field_simp [ne_of_gt hd]
  constructor
  · nlinarith [hmulLower, hcancel]
  · nlinarith [hmulUpper, hcancel]

/-- Normalized low-frequency comparison for the exact floor cutoff. The
explicit terminal term `d/N` is retained. -/
theorem norm_floor_monomial_normalized_floor_prefix_sub_model_le
    {c ξ d N : ℝ} (hc : 1 < c) (hN : 0 < N) (hd : 0 < d) :
    let L : ℕ := Nat.floor (N / d)
    ‖(d / N : ℝ) • (Finset.Ico 0 L : Finset ℕ).sum
        (fun i => unitFrequencyPhase
          (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
      continuousFractionalModel c N ξ‖ ≤
      2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) + d / N := by
  dsimp only
  let L : ℕ := Nat.floor (N / d)
  let S : ℂ := (Finset.Ico 0 L : Finset ℕ).sum (fun i => unitFrequencyPhase
    (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ)))
  have hN0 : 0 ≤ N := le_of_lt hN
  have hrem := nat_floor_progression_remainder_bounds hN0 hd
  have hLN : d * (L : ℝ) ≤ N := sub_nonneg.mp hrem.1
  have hraw := norm_floor_monomial_raw_floor_prefix_sub_integral_le
    (c := c) (ξ := ξ) (d := d) (N := N) hc hd hN0
  have hraw' : ‖(d : ℝ) • S -
      ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)‖ ≤
      (L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d +
        (N - d * (L : ℝ)) := by
    simpa [L, S] using hraw
  have hC : 0 ≤ 2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) := by positivity
  have hmain :
      ((L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d) / N ≤
        2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) := by
    rw [div_le_iff₀ hN]
    calc
      (L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d =
          (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * (d * (L : ℝ)) := by ring
      _ ≤ (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * N :=
        mul_le_mul_of_nonneg_left hLN hC
  have htail : (N - d * (L : ℝ)) / N ≤ d / N :=
    div_le_div_of_nonneg_right hrem.2.le hN.le
  have hintegral : continuousFractionalModel c N ξ =
      (N : ℂ)⁻¹ * ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c) := rfl
  have hcoeff : (N : ℂ)⁻¹ * (d : ℂ) = ((d / N : ℝ) : ℂ) := by
    push_cast
    field_simp [ne_of_gt hN]
  have hscale :
      ((d / N : ℝ) : ℂ) * S -
        ((N : ℂ)⁻¹ * ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)) =
      (N : ℂ)⁻¹ * ((d : ℂ) * S -
        ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)) := by
    rw [← hcoeff]
    ring
  rw [hintegral, show (d / N : ℝ) • S = ((d / N : ℝ) : ℂ) * S by simp [smul_eq_mul], hscale,
    norm_mul]
  have hnormInv : ‖(N : ℂ)⁻¹‖ = N⁻¹ := by
    simp [norm_inv, RCLike.norm_ofReal, abs_of_pos hN]
  rw [hnormInv]
  have hrawDiv := div_le_div_of_nonneg_right hraw' (le_of_lt hN)
  have hbound :
      ((L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d +
        (N - d * (L : ℝ))) / N ≤
      2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) + d / N := by
    rw [add_div]
    exact add_le_add hmain htail
  have hInv : N⁻¹ = 1 / N := by simp
  rw [hInv]
  calc
    (1 / N) * ‖(d : ℝ) • S -
        ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)‖ ≤
        ((L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d +
          (N - d * (L : ℝ))) / N := by
      have hmul := mul_le_mul_of_nonneg_left hraw' (by positivity : 0 ≤ 1 / N)
      have hfactor : (1 / N) *
          ((L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d +
            (N - d * (L : ℝ))) =
          ((L : ℝ) * (2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d)) * d +
            (N - d * (L : ℝ))) / N := by ring
      rw [← hfactor]
      exact hmul
    _ ≤ 2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) + d / N := hbound

/-- Convert the normalized floor-prefix estimate into a power saving under
explicit exponent inequalities. -/
theorem lowFrequencyFloorPrefix_powerSaving
    {c ξ d N a ε δ : ℝ} (hc : 1 < c) (hN : 1 ≤ N) (hd : 0 < d)
    (hξ : |ξ| ≤ N ^ (a - c)) (hdN : d ≤ N ^ ε)
    (ha : a - c ≤ -δ) (haε : a + ε - 1 ≤ -δ) (hε : ε - 1 ≤ -δ) :
    ‖(d / N : ℝ) • (Finset.Ico 0 (Nat.floor (N / d)) : Finset ℕ).sum
        (fun i => unitFrequencyPhase
          (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
      continuousFractionalModel c N ξ‖ ≤
      (2 * Real.pi + 2 * Real.pi * c + 1) * N ^ (-δ) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNnonneg : 0 ≤ N := le_trans (by norm_num) hN
  have hmain := norm_floor_monomial_normalized_floor_prefix_sub_model_le
    (c := c) (ξ := ξ) (d := d) (N := N) hc hNpos hd
  have hp1 : N ^ (a - c) ≤ N ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hN ha
  have hp2 : N ^ (a - c) * N ^ (c - 1) * d ≤ N ^ (-δ) := by
    calc
      N ^ (a - c) * N ^ (c - 1) * d = N ^ (a - 1) * d := by
        rw [← Real.rpow_add hNpos]
        congr 1 <;> ring
      _ ≤ N ^ (a - 1) * N ^ ε :=
        mul_le_mul_of_nonneg_left hdN (Real.rpow_nonneg hNnonneg (a - 1))
      _ = N ^ (a + ε - 1) := by
        rw [← Real.rpow_add hNpos]
        congr 1 <;> ring
      _ ≤ N ^ (-δ) := Real.rpow_le_rpow_of_exponent_le hN haε
  have hxiδ : |ξ| ≤ N ^ (-δ) := hξ.trans hp1
  have hsecond : |ξ| * N ^ (c - 1) * d ≤ N ^ (-δ) := by
    calc
      |ξ| * N ^ (c - 1) * d ≤ N ^ (a - c) * N ^ (c - 1) * d := by
        gcongr
      _ ≤ N ^ (-δ) := hp2
  have htail : d / N ≤ N ^ (-δ) := by
    calc
      d / N ≤ N ^ ε / N := div_le_div_of_nonneg_right hdN (le_of_lt hNpos)
      _ = N ^ (ε - 1) := by
        rw [Real.rpow_sub hNpos ε 1, Real.rpow_one]
      _ ≤ N ^ (-δ) := Real.rpow_le_rpow_of_exponent_le hN hε
  have hfreq :
      2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) ≤
        (2 * Real.pi + 2 * Real.pi * c) * N ^ (-δ) := by
    have hcoeff1 : 0 ≤ 2 * Real.pi := by positivity
    have hcoeff2 : 0 ≤ 2 * Real.pi * c := by positivity
    have hpart1 := mul_le_mul_of_nonneg_left hxiδ hcoeff1
    have hpart2 := mul_le_mul_of_nonneg_left hsecond hcoeff2
    nlinarith [hpart1, hpart2]
  calc
    ‖(d / N : ℝ) • (Finset.Ico 0 (Nat.floor (N / d)) : Finset ℕ).sum
        (fun i => unitFrequencyPhase
          (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
        continuousFractionalModel c N ξ‖ ≤
      2 * Real.pi * |ξ| * (1 + c * N ^ (c - 1) * d) + d / N := hmain
    _ ≤ (2 * Real.pi + 2 * Real.pi * c + 1) * N ^ (-δ) := by
      nlinarith [hfreq, htail, Real.rpow_nonneg hNnonneg (-δ)]

/-- The fixed parameters in `ar:parameters` satisfy the exponent-side
conditions required by the low-frequency power-saving lemma. -/
theorem progressionParameters_lowFrequency_exponents {c : ℝ} (hc : 1 < c) :
    let j : ℕ := Nat.ceil c + 2
    let a : ℝ := 1 / 100
    let ε : ℝ := a / (100 * (j : ℝ))
    let η : ℝ := a / (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    a - c ≤ -δ ∧ a + ε - 1 ≤ -δ ∧ ε - 1 ≤ -δ ∧ 0 < ε ∧ 0 < η := by
  dsimp only
  let j : ℕ := Nat.ceil c + 2
  let a : ℝ := 1 / 100
  let ε : ℝ := a / (100 * (j : ℝ))
  let η : ℝ := a / (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  have hceil : 1 < (Nat.ceil c : ℝ) := lt_of_lt_of_le hc (Nat.le_ceil c)
  have hceilNat : 2 ≤ Nat.ceil c := by
    have hceilNat' : 1 < Nat.ceil c := by exact_mod_cast hceil
    omega
  have hj : 4 ≤ (j : ℝ) := by
    dsimp [j]
    exact_mod_cast (show 4 ≤ Nat.ceil c + 2 by omega)
  have hjpos : 0 < (j : ℝ) := by linarith
  have hpow : 1 ≤ (2 : ℝ) ^ (j : ℝ) := by
    calc
      1 = (2 : ℝ) ^ (0 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (j : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hepspos : 0 < ε := by dsimp [ε, a]; positivity
  have hetapos : 0 < η := by dsimp [η, a]; positivity
  have hpowPos : 0 < (2 : ℝ) ^ (j : ℝ) := by positivity
  have hEtaEq : η = ε / (2 : ℝ) ^ (j : ℝ) := by
    dsimp [η, ε]
    field_simp
  have hetale : η ≤ ε := by
    rw [hEtaEq]
    apply (div_le_iff₀ hpowPos).2
    calc
      ε = ε * 1 := by ring
      _ ≤ ε * (2 : ℝ) ^ (j : ℝ) :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hepspos)
  have hepssmall : ε ≤ 1 / 100 := by
    dsimp [ε, a]
    rw [div_le_iff₀ (by positivity : 0 < 100 * (j : ℝ))]
    nlinarith [hj]
  have hetasmall : δ ≤ 1 / 100 := by dsimp [δ]; nlinarith [hetale, hepssmall]
  constructor
  · nlinarith [hc, hetasmall]
  constructor
  · nlinarith [hepssmall, hetasmall]
  constructor
  · nlinarith [hepssmall, hetasmall]
  exact ⟨hepspos, hetapos⟩

/-- The low-frequency case of `ar:progression` has the blueprint's stated
divisor range and a single threshold depending only on `c`. -/
theorem exists_lowFrequency_floorProgression_powerSaving
    {c : ℝ} (hc : 1 < c) :
    let j : ℕ := Nat.ceil c + 2
    let a : ℝ := 1 / 100
    let εd : ℝ := a / (100 * (j : ℝ))
    let η : ℝ := a / (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ d : ℝ, 0 < d →
      d ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) → ∀ ξ : ℝ,
      |ξ| ≤ N ^ (a - c) →
      ‖(d / N : ℝ) • (Finset.Ico 0 (Nat.floor (N / d)) : Finset ℕ).sum
          (fun i => unitFrequencyPhase
            (ξ * ((Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
        continuousFractionalModel c N ξ‖ ≤
        (2 * Real.pi + 2 * Real.pi * c + 1) * N ^ (-δ) := by
  dsimp only
  let j : ℕ := Nat.ceil c + 2
  let a : ℝ := 1 / 100
  let εd : ℝ := a / (100 * (j : ℝ))
  let η : ℝ := a / (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  have hparams := progressionParameters_lowFrequency_exponents hc
  have hparams' : a - c ≤ -δ ∧ a + εd - 1 ≤ -δ ∧ εd - 1 ≤ -δ ∧
      0 < εd ∧ 0 < η := by
    simpa [j, a, εd, η, δ] using hparams
  rcases hparams' with ⟨ha, haε, hε, hεpos, hηpos⟩
  obtain ⟨Ndiv, hNdiv, hdiv⟩ := exists_monomial_divisor_power_threshold hεpos
  let N₀ : ℝ := max 3 Ndiv
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro N hN d hd hcut ξ hξ
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hNdiv' : Ndiv ≤ N := le_trans (le_max_right _ _) hN
  have hdN : d ≤ N ^ εd := hcut.trans (hdiv N hNdiv')
  exact lowFrequencyFloorPrefix_powerSaving hc (by linarith) hd hξ hdN ha haε hε

/-- Retained floor-removal frequencies satisfy the frequency window required
by monomial cancellation in the high-frequency case. -/
theorem progression_shifted_frequency_range
    {N ξ c : ℝ} (hc : 1 < c) (hN : 1 ≤ N)
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (hξhigh : N ^ ((1 / 100 : ℝ) - c) < |ξ|)
    (M : ℕ) (hM : (M : ℝ) ≤ N ^ (1 / 10000 : ℝ))
    {m : ℤ} (hm : m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)) :
    N ^ ((1 / 100 : ℝ) - c) ≤ |(m : ℝ) + ξ| ∧
      |(m : ℝ) + ξ| ≤ 2 * N ^ (1 / 10000 : ℝ) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hpowhi : 1 ≤ N ^ (1 / 10000 : ℝ) := by
    calc
      1 = N ^ (0 : ℝ) := (Real.rpow_zero N).symm
      _ ≤ N ^ (1 / 10000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hmem := Finset.mem_Icc.mp hm
  have hmabs : |(m : ℝ)| ≤ (M : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast hmem.1
    · exact_mod_cast hmem.2
  have hxiabs : |ξ| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hupper : |(m : ℝ) + ξ| ≤ 2 * N ^ (1 / 10000 : ℝ) := by
    calc
      |(m : ℝ) + ξ| ≤ |(m : ℝ)| + |ξ| := by
        simpa [Real.norm_eq_abs] using norm_add_le (m : ℝ) ξ
      _ ≤ (M : ℝ) + 1 / 2 := add_le_add hmabs hxiabs
      _ ≤ N ^ (1 / 10000 : ℝ) + 1 / 2 := add_le_add hM le_rfl
      _ ≤ 2 * N ^ (1 / 10000 : ℝ) := by nlinarith [hpowhi]
  refine ⟨?_, hupper⟩
  by_cases hm0 : m = 0
  · simpa [hm0] using le_of_lt hξhigh
  · have habs_m : 1 ≤ |(m : ℝ)| := by
      have hm_int : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
      exact_mod_cast hm_int
    have htriangle : |(m : ℝ)| ≤ |(m : ℝ) + ξ| + |ξ| := by
      have heq : (m : ℝ) = ((m : ℝ) + ξ) - ξ := by ring
      rw [heq]
      simpa [Real.norm_eq_abs] using norm_sub_le ((m : ℝ) + ξ) ξ
    have hhalf : (1 / 2 : ℝ) ≤ |(m : ℝ) + ξ| := by
      nlinarith [habs_m, htriangle, hxiabs]
    have hsmall : N ^ ((1 / 100 : ℝ) - c) ≤ 1 / 2 := by
      have hle1 : N ^ ((1 / 100 : ℝ) - c) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hN
          (by linarith : (1 / 100 : ℝ) - c ≤ 0)
      nlinarith
    exact hsmall.trans hhalf

/-- Summing the finite shifted floor-Fourier expansion over progression
indices is the same as summing first over the retained frequencies. -/
theorem sum_floorFourierShiftedPartialSum_eq_frequency_sum
    (ξ : ℝ) (M : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) :
    (∑ n ∈ s, floorFourierShiftedPartialSum ξ (t n) M) =
      ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        floorFourierCoefficient m ξ *
          (∑ n ∈ s,
            unitFrequencyPhase (((m : ℝ) + ξ) * t n)) := by
  classical
  simp only [floorFourierShiftedPartialSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]

/-- Summing the pointwise floor-removal remainder over any finite set costs
only the same logarithmic factor times the summed boundary kernel. -/
theorem norm_sum_floorPhase_sub_shiftedPartialSum_le
    (M : ℕ) (hM : 2 ≤ M) {ξ : ℝ}
    (hξlo : -(1 / 2 : ℝ) ≤ ξ) (hξhi : ξ < 1 / 2)
    (s : Finset ℤ) (t : ℤ → ℝ) :
    ‖(∑ n ∈ s, unitFrequencyPhase (ξ * (Int.floor (t n) : ℝ))) -
      ∑ n ∈ s, floorFourierShiftedPartialSum ξ (t n) M‖ ≤
      12 * Real.log (2 * (M : ℝ)) *
        ∑ n ∈ s, floorBoundaryKernel M hM (t n) := by
  have hpoint : ∀ n ∈ s,
      ‖unitFrequencyPhase (ξ * (Int.floor (t n) : ℝ)) -
        floorFourierShiftedPartialSum ξ (t n) M‖ ≤
        12 * Real.log (2 * (M : ℝ)) * floorBoundaryKernel M hM (t n) := by
    intro n hn
    exact (floorFourierRemoval M hM hξlo hξhi).2
  have hsum :
      (∑ n ∈ s, unitFrequencyPhase (ξ * (Int.floor (t n) : ℝ))) -
        ∑ n ∈ s, floorFourierShiftedPartialSum ξ (t n) M =
      ∑ n ∈ s,
        (unitFrequencyPhase (ξ * (Int.floor (t n) : ℝ)) -
          floorFourierShiftedPartialSum ξ (t n) M) := by
    rw [Finset.sum_sub_distrib]
  calc
    _ = ‖∑ n ∈ s,
        (unitFrequencyPhase (ξ * (Int.floor (t n) : ℝ)) -
          floorFourierShiftedPartialSum ξ (t n) M)‖ := by rw [hsum]
    _ ≤ ∑ n ∈ s,
        ‖unitFrequencyPhase (ξ * (Int.floor (t n) : ℝ)) -
          floorFourierShiftedPartialSum ξ (t n) M‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s,
        (12 * Real.log (2 * (M : ℝ)) * floorBoundaryKernel M hM (t n)) :=
          Finset.sum_le_sum hpoint
    _ = 12 * Real.log (2 * (M : ℝ)) *
        ∑ n ∈ s, floorBoundaryKernel M hM (t n) := by rw [Finset.mul_sum]

/-- Aggregate individual phase-sum bounds through a finite family of complex
Fourier coefficients, retaining their exact `ℓ¹` mass. -/
theorem norm_weighted_frequency_sum_le
    (s : Finset ℤ) (coeff phase : ℤ → ℂ) {A B : ℝ}
    (hA : 0 ≤ A)
    (hphase : ∀ m ∈ s, A * ‖phase m‖ ≤ B) :
    A * ‖∑ m ∈ s, coeff m * phase m‖ ≤
      B * ∑ m ∈ s, ‖coeff m‖ := by
  have hterm : ∀ m ∈ s,
      A * (‖coeff m‖ * ‖phase m‖) ≤ B * ‖coeff m‖ := by
    intro m hm
    calc
      A * (‖coeff m‖ * ‖phase m‖) =
          ‖coeff m‖ * (A * ‖phase m‖) := by ring
      _ ≤ ‖coeff m‖ * B :=
        mul_le_mul_of_nonneg_left (hphase m hm) (norm_nonneg _)
      _ = B * ‖coeff m‖ := by ring
  calc
    A * ‖∑ m ∈ s, coeff m * phase m‖ ≤
        A * ∑ m ∈ s, ‖coeff m * phase m‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hA
    _ = ∑ m ∈ s, A * (‖coeff m‖ * ‖phase m‖) := by
          simp only [norm_mul]
          rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ s, B * ‖coeff m‖ := Finset.sum_le_sum hterm
    _ = B * ∑ m ∈ s, ‖coeff m‖ := by rw [← Finset.mul_sum]

/-- The shifted unit-frequency phase sampled at `d*n` is exactly the
derivative-test phase used by `monomial_cancellation`. -/
theorem unitFrequencyPhase_scaled_monomial_eq_realExponentialPhase
    (β d c : ℝ) (n : ℤ) :
    unitFrequencyPhase (β * ((d * (n : ℝ)) ^ c)) =
      realExponentialPhase (fun t => β * (d * t) ^ c) n := by
  unfold unitFrequencyPhase realExponentialPhase
  congr 1

/-- The blueprint's fixed `η(c)` is below the frequency cutoff exponent, so
the floor-removal cutoff `M=floor(N^η)` fits the retained mode range. -/
theorem progressionParameters_eta_le_frequency_cutoff {c : ℝ}
    (hc : 1 < c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    η ≤ 1 / 10000 := by
  dsimp only
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  have hceil : 1 < (Nat.ceil c : ℝ) := lt_of_lt_of_le hc (Nat.le_ceil c)
  have hj : 4 ≤ (j : ℝ) := by
    have hjNat : 2 ≤ Nat.ceil c := by
      have : (1 : ℕ) < Nat.ceil c := by exact_mod_cast hceil
      omega
    dsimp [j]
    exact_mod_cast (show 4 ≤ Nat.ceil c + 2 by omega)
  have hpow : 1 ≤ (2 : ℝ) ^ (j : ℝ) := by
    calc
      1 = (2 : ℝ) ^ (0 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (j : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hj])
  have hden : 400 ≤ 100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ) := by
    have hjnonneg : 0 ≤ (j : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 100 * (j : ℝ))]
  have hdenpos : 0 < 100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ) := by positivity
  rw [div_le_iff₀ hdenpos]
  nlinarith

/-- The natural cutoff `floor(N^η)` lies below the blueprint's retained
frequency cutoff for every scale `N≥1`. -/
theorem progression_floor_cutoff_bound {c N : ℝ}
    (hc : 1 < c) (hN : 1 ≤ N) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ((Nat.floor (N ^ η) : ℕ) : ℝ) ≤ N ^ (1 / 10000 : ℝ) := by
  dsimp only
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  have hη := progressionParameters_eta_le_frequency_cutoff hc
  have hfloor : ((Nat.floor (N ^ η) : ℕ) : ℝ) ≤ N ^ η :=
    Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ N) η)
  exact hfloor.trans (Real.rpow_le_rpow_of_exponent_le hN hη)

/-- Uniform monomial cancellation for each retained shifted frequency in the
high-frequency case of the progression approximation. -/
theorem exists_progression_shifted_mode_cancellation {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        N ^ ((1 / 100 : ℝ) - c) < |ξ| →
      ∀ M : ℕ, (M : ℝ) ≤ N ^ (1 / 10000 : ℝ) →
      ∀ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ((d : ℝ) / N) *
          ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            unitFrequencyPhase
              (((m : ℝ) + ξ) * (((d : ℝ) * (n : ℝ)) ^ c))‖ ≤
          12 * N ^ (-16 * η) := by
  dsimp only
  obtain ⟨Nmono, hNmono, hmonomial⟩ := monomial_cancellation hc hcNon
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let N₀ : ℝ := max 3 Nmono
  have hN₀ : 3 ≤ N₀ := by dsimp [N₀]; exact le_max_left _ _
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN d hd hdcut ξ hξlo hξhi hξhigh M hMcut m hm
  have hNmono' : Nmono ≤ N := by
    dsimp [N₀] at hN
    exact le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_trans hN₀ hN)
  have hfreq := progression_shifted_frequency_range hc hN1 hξlo hξhi
    hξhigh M hMcut hm
  let β : ℝ := (m : ℝ) + ξ
  have hmonomial' := hmonomial N hNmono' d β hd hdcut hfreq.1 hfreq.2
  have hphase :
      (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
        unitFrequencyPhase (β * (((d : ℝ) * (n : ℝ)) ^ c))) =
      ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
        realExponentialPhase (fun t => β * ((d : ℝ) * t) ^ c) n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact unitFrequencyPhase_scaled_monomial_eq_realExponentialPhase β d c n
  have hresult :
      ((d : ℝ) / N) *
        ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
          unitFrequencyPhase (β * (((d : ℝ) * (n : ℝ)) ^ c))‖ ≤
        12 * N ^ (-16 * η) := by
    simpa [hphase, η, j] using hmonomial'
  simpa [β, η, j] using hresult

/-- The retained shifted Fourier modes on a progression have total normalized
contribution bounded by monomial cancellation times the floor coefficients'
logarithmic `ℓ¹` mass. -/
theorem exists_progression_shifted_fourier_sum_bound {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        N ^ ((1 / 100 : ℝ) - c) < |ξ| →
      ∀ M : ℕ, 2 ≤ M → (M : ℝ) ≤ N ^ (1 / 10000 : ℝ) →
        ((d : ℝ) / N) *
          ‖∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            floorFourierCoefficient m ξ *
              (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
                unitFrequencyPhase
                  (((m : ℝ) + ξ) * (((d : ℝ) * (n : ℝ)) ^ c)))‖ ≤
          120 * Real.log (2 * (M : ℝ)) * N ^ (-16 * η) := by
  dsimp only
  obtain ⟨Nmode, hNmode, hmode⟩ :=
    exists_progression_shifted_mode_cancellation hc hcNon
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let N₀ : ℝ := max 3 Nmode
  have hN₀ : 3 ≤ N₀ := by dsimp [N₀]; exact le_max_left _ _
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN d hd hdcut ξ hξlo hξhi hξhigh M hM hMcut
  have hNmode' : Nmode ≤ N := by
    dsimp [N₀] at hN
    exact le_trans (le_max_right _ _) hN
  have hN3 : 3 ≤ N := le_trans hN₀ hN
  have hNpos : 0 < N := by linarith
  let s : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let coeff : ℤ → ℂ := fun m => floorFourierCoefficient m ξ
  let phase : ℤ → ℂ := fun m =>
    ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
      unitFrequencyPhase (((m : ℝ) + ξ) * (((d : ℝ) * (n : ℝ)) ^ c))
  have hA : 0 ≤ (d : ℝ) / N :=
    div_nonneg (by positivity) (le_of_lt hNpos)
  have hB : 0 ≤ 12 * N ^ (-16 * η) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hNpos) _)
  have hphase : ∀ m ∈ s, ((d : ℝ) / N) * ‖phase m‖ ≤
      12 * N ^ (-16 * η) := by
    intro m hm
    have h := hmode N hNmode' d hd hdcut ξ hξlo hξhi hξhigh M hMcut m hm
    simpa [phase, η, j] using h
  have hweighted := norm_weighted_frequency_sum_le s coeff phase hA hphase
  have hcoeff := floorFourierCoefficient_sum_norm_le_log M hM hξlo hξhi
  have hcoeff' : ∑ m ∈ s, ‖coeff m‖ ≤ 10 * Real.log (2 * (M : ℝ)) := by
    simpa [s, coeff] using hcoeff
  calc
    ((d : ℝ) / N) *
        ‖∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          floorFourierCoefficient m ξ *
            (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
              unitFrequencyPhase
                (((m : ℝ) + ξ) * (((d : ℝ) * (n : ℝ)) ^ c)))‖ =
      ((d : ℝ) / N) * ‖∑ m ∈ s, coeff m * phase m‖ := by
        simp [s, coeff, phase]
    _ ≤ (12 * N ^ (-16 * η)) * ∑ m ∈ s, ‖coeff m‖ := hweighted
    _ ≤ (12 * N ^ (-16 * η)) * (10 * Real.log (2 * (M : ℝ))) :=
      mul_le_mul_of_nonneg_left hcoeff' hB
    _ = 120 * Real.log (2 * (M : ℝ)) * N ^ (-16 * η) := by ring

/-- High-frequency cancellation for the complete sampled floor phase on a
progression, before adding the continuous-model integral. -/
theorem exists_highFrequency_progression_floor_sum_bound {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        N ^ ((1 / 100 : ℝ) - c) < |ξ| →
      let M : ℕ := Nat.floor (N ^ η)
      ∃ hM : 2 ≤ M,
        ((d : ℝ) / N) *
          ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            unitFrequencyPhase
              (ξ * (Int.floor ((((d : ℝ) * (n : ℝ)) ^ c)) : ℝ))‖ ≤
          36 * Real.log (2 * (M : ℝ)) * N ^ (-η / 2) +
            120 * Real.log (2 * (M : ℝ)) * N ^ (-16 * η) := by
  dsimp only
  obtain ⟨Nbd, hNbd, hboundary⟩ := boundaryErrorProgression hc hcNon
  obtain ⟨Nmode, hNmode, hmode⟩ :=
    exists_progression_shifted_fourier_sum_bound hc hcNon
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let N₀ : ℝ := max Nbd Nmode
  have hN₀ : 3 ≤ N₀ := by
    dsimp [N₀]
    exact le_max_of_le_left hNbd
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN d hd hdcut ξ hξlo hξhi hξhigh
  have hNbd' : Nbd ≤ N := le_trans (le_max_left _ _) hN
  have hNmode' : Nmode ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_trans hN₀ hN)
  have hNpos : 0 < N := by linarith
  let M : ℕ := Nat.floor (N ^ η)
  have hcutoff := progression_floor_cutoff_bound hc hN1
  have hMcut : (M : ℝ) ≤ N ^ (1 / 10000 : ℝ) := by
    simpa [M, η, j] using hcutoff
  have hbound := hboundary N hNbd'
  dsimp only at hbound
  rcases hbound with ⟨hM, hboundary'⟩
  have hboundary' := hboundary' d hd hdcut
  have hM' : 2 ≤ M := by simpa [M, η, j] using hM
  let s : Finset ℤ := realIntegerInterval 0 (N / (d : ℝ))
  let t : ℤ → ℝ := fun n => ((d : ℝ) * (n : ℝ)) ^ c
  have hmode' := hmode N hNmode' d hd hdcut ξ hξlo hξhi hξhigh M hM' hMcut
  have hrem := norm_sum_floorPhase_sub_shiftedPartialSum_le
    M hM' hξlo hξhi s t
  have hidentity := sum_floorFourierShiftedPartialSum_eq_frequency_sum ξ M s t
  have hscale : 0 ≤ (d : ℝ) / N := by positivity
  have hlog : 0 ≤ Real.log (2 * (M : ℝ)) := by
    apply Real.log_nonneg
    have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM'
    nlinarith
  have hremScaled :
      ((d : ℝ) / N) *
        ‖(∑ n ∈ s, unitFrequencyPhase (ξ * (Int.floor (t n) : ℝ))) -
          ∑ n ∈ s, floorFourierShiftedPartialSum ξ (t n) M‖ ≤
        36 * Real.log (2 * (M : ℝ)) * N ^ (-η / 2) := by
    calc
      _ ≤ ((d : ℝ) / N) *
          (12 * Real.log (2 * (M : ℝ)) *
            ∑ n ∈ s, floorBoundaryKernel M hM (t n)) :=
          mul_le_mul_of_nonneg_left hrem hscale
      _ = 12 * Real.log (2 * (M : ℝ)) *
          (((d : ℝ) / N) *
            ∑ n ∈ s, floorBoundaryKernel M hM (t n)) := by ring
      _ ≤ 12 * Real.log (2 * (M : ℝ)) * (3 * N ^ (-η / 2)) :=
          mul_le_mul_of_nonneg_left hboundary' (by positivity [hlog])
      _ = 36 * Real.log (2 * (M : ℝ)) * N ^ (-η / 2) := by ring
  have hpartial :
      ((d : ℝ) / N) *
        ‖∑ n ∈ s, floorFourierShiftedPartialSum ξ (t n) M‖ ≤
        120 * Real.log (2 * (M : ℝ)) * N ^ (-16 * η) := by
    rw [hidentity]
    simpa [s, t, η, j] using hmode'
  let exactS : ℂ :=
    ∑ n ∈ s, unitFrequencyPhase (ξ * (Int.floor (t n) : ℝ))
  let partialS : ℂ := ∑ n ∈ s, floorFourierShiftedPartialSum ξ (t n) M
  have hsumdecomp : exactS = (exactS - partialS) + partialS := by
    dsimp [exactS, partialS]
    abel
  have hexact := calc
      ((d : ℝ) / N) * ‖exactS‖ ≤
        ((d : ℝ) / N) * (‖exactS - partialS‖ + ‖partialS‖) :=
          mul_le_mul_of_nonneg_left
            (calc
              ‖exactS‖ = ‖(exactS - partialS) + partialS‖ :=
                congrArg norm hsumdecomp
              _ ≤ ‖exactS - partialS‖ + ‖partialS‖ := norm_add_le _ _) hscale
      _ ≤ 36 * Real.log (2 * (M : ℝ)) * N ^ (-η / 2) +
            120 * Real.log (2 * (M : ℝ)) * N ^ (-16 * η) := by
              have hsum := add_le_add hremScaled hpartial
              nlinarith
  have hηfinal : η = (100 : ℝ)⁻¹ /
      (100 * ((Nat.ceil c : ℝ) + 2) *
        (2 : ℝ) ^ ((Nat.ceil c : ℝ) + 2)) := by
    dsimp [η, j]
    push_cast
    norm_num
  have hexactfinal :
      ((d : ℝ) / N) *
        ‖∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
          unitFrequencyPhase
            (ξ * (Int.floor ((((d : ℝ) * (n : ℝ)) ^ c)) : ℝ))‖ ≤
        36 * Real.log (2 *
          ((Nat.floor (N ^ ((1 / 100 : ℝ) /
            (100 * (Nat.ceil c + 2 : ℕ) *
              (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)))) : ℕ) : ℝ)) *
            N ^ (-((1 / 100 : ℝ) /
              (100 * (Nat.ceil c + 2 : ℕ) *
                (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 2) +
          120 * Real.log (2 *
            ((Nat.floor (N ^ ((1 / 100 : ℝ) /
              (100 * (Nat.ceil c + 2 : ℕ) *
                (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)))) : ℕ) : ℝ)) *
              N ^ (-16 * ((1 / 100 : ℝ) /
                (100 * (Nat.ceil c + 2 : ℕ) *
                  (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)))) := by
    simpa [M, s, t, η, j, exactS, partialS, Nat.cast_add, one_div, hηfinal] using
      hexact
  exact ⟨hM, hexactfinal⟩

/-- The continuous model has the required large-frequency power decay when
`|ξ|>N^(a-c)` and `N≥1`, for any nonnegative `a`. -/
theorem continuousFractionalModel_highFrequency_power_bound
    {c N ξ a : ℝ} (hc : 1 < c) (hN : 1 ≤ N) (ha : 0 ≤ a)
    (hξ : N ^ (a - c) < |ξ|) :
    ‖continuousFractionalModel c N ξ‖ ≤
      (1 + (Real.pi * c)⁻¹) * N ^ (-a / c) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hξne : ξ ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hξ
    have hpositive : 0 < N ^ (a - c) := Real.rpow_pos_of_pos hNpos _
    linarith
  let y : ℝ := |ξ| * N ^ c
  have hypos : 0 < y := by
    dsimp [y]
    exact mul_pos (abs_pos.mpr hξne) (Real.rpow_pos_of_pos hNpos c)
  have hpower : N ^ (a - c) * N ^ c = N ^ a := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hbase : N ^ a ≤ y := by
    dsimp [y]
    calc
      N ^ a = N ^ (a - c) * N ^ c := hpower.symm
      _ ≤ |ξ| * N ^ c := le_of_lt (mul_lt_mul_of_pos_right hξ
        (Real.rpow_pos_of_pos hNpos c))
  have hNpower : 1 ≤ N ^ a := Real.one_le_rpow hN ha
  have hyone : 1 ≤ y := hNpower.trans hbase
  have hmodel := continuousFractionalModel_norm_le_min hc hNpos hξne
  have hdecay : y ^ (-c⁻¹) ≤ N ^ (-a / c) := by
    calc
      y ^ (-c⁻¹) ≤ (N ^ a) ^ (-c⁻¹) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNpos a) hbase
          (neg_nonpos.mpr (inv_nonneg.mpr (by linarith : 0 ≤ c)))
      _ = N ^ (-a / c) := by
        rw [← Real.rpow_mul (le_of_lt hNpos)]
        congr 1
        field_simp
  calc
    ‖continuousFractionalModel c N ξ‖ ≤
        (1 + (Real.pi * c)⁻¹) * min 1 (y ^ (-c⁻¹)) := by
          simpa [y] using hmodel
    _ ≤ (1 + (Real.pi * c)⁻¹) * y ^ (-c⁻¹) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ ≤ (1 + (Real.pi * c)⁻¹) * N ^ (-a / c) :=
          mul_le_mul_of_nonneg_left hdecay (by positivity)

/-- Absorb the two logarithmic errors in the high-frequency progression
estimate, using the blueprint's exact exponents `η/2`, `16η`, and `δ=η/4`. -/
theorem exists_progression_log_terms_absorption {η : ℝ}
    (hη : 0 < η) (hηle : η ≤ 1) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ M : ℕ,
      2 ≤ M → (M : ℝ) ≤ N ^ η →
      36 * Real.log (2 * (M : ℝ)) * N ^ (-η / 2) +
        120 * Real.log (2 * (M : ℝ)) * N ^ (-16 * η) ≤
      2 * N ^ (-η / 4) := by
  have hlog₁ := eventually_log_le_const_mul_rpow
    (s := η / 4) (ε := 1 / 72) (by linarith) (by norm_num)
  have hlog₂ := eventually_log_le_const_mul_rpow
    (s := 15 * η) (ε := 1 / 240) (by positivity) (by norm_num)
  have hgood : ∀ᶠ N : ℝ in Filter.atTop,
      3 ≤ N ∧ Real.exp 2 ≤ N ∧
        Real.log N ≤ (1 / 72 : ℝ) * N ^ (η / 4) ∧
        Real.log N ≤ (1 / 240 : ℝ) * N ^ (15 * η) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨3, fun N hN => hN⟩,
      Filter.eventually_atTop.2 ⟨Real.exp 2, fun N hN => hN⟩,
      hlog₁, hlog₂] with N hN3 hNexp hlog₁N hlog₂N
    exact ⟨hN3, hNexp, hlog₁N, hlog₂N⟩
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hgood
  let N₀ : ℝ := max 3 B
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro N hN M hM hMcut
  have hNlarge := hB N (le_trans (le_max_right _ _) hN)
  rcases hNlarge with ⟨hN3, hNexp, hlog₁N, hlog₂N⟩
  have hN1 : 1 ≤ N := by
    have hexpOne : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hNpos : 0 < N := by linarith
  have hlogN2 : 2 ≤ Real.log N := by
    calc
      2 = Real.log (Real.exp 2) := by rw [Real.log_exp]
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 2) hNexp
  have hMreal : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hMleN : (M : ℝ) ≤ N := by
    calc
      (M : ℝ) ≤ N ^ η := hMcut
      _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hηle
      _ = N := Real.rpow_one N
  have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hlogMle : Real.log (2 * (M : ℝ)) ≤ 2 * Real.log N := by
    calc
      Real.log (2 * (M : ℝ)) ≤ Real.log (2 * N) :=
        Real.log_le_log (by positivity) (by nlinarith [hMleN])
      _ = Real.log 2 + Real.log N := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
      _ ≤ 1 + Real.log N := by
        exact add_le_add
          (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]) le_rfl
      _ ≤ 2 * Real.log N := by nlinarith [hlogN2]
  have hfirst :
      36 * Real.log (2 * (M : ℝ)) * N ^ (-η / 2) ≤ N ^ (-η / 4) := by
    calc
      _ ≤ 72 * Real.log N * N ^ (-η / 2) := by
        exact mul_le_mul_of_nonneg_right
          (by nlinarith [hlogMle])
          (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ ≤ 72 * ((1 / 72 : ℝ) * N ^ (η / 4)) * N ^ (-η / 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog₁N (by norm_num))
          (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ = N ^ (-η / 4) := by
        calc
          72 * ((1 / 72 : ℝ) * N ^ (η / 4)) * N ^ (-η / 2) =
              N ^ (η / 4) * N ^ (-η / 2) := by ring
          _ = N ^ (-η / 4) := by
            rw [← Real.rpow_add hNpos]
            congr 1 <;> ring
  have hsecond :
      120 * Real.log (2 * (M : ℝ)) * N ^ (-16 * η) ≤ N ^ (-η / 4) := by
    calc
      _ ≤ 240 * Real.log N * N ^ (-16 * η) := by
        exact mul_le_mul_of_nonneg_right
          (by nlinarith [hlogMle])
          (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ ≤ 240 * ((1 / 240 : ℝ) * N ^ (15 * η)) * N ^ (-16 * η) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog₂N (by norm_num))
          (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ = N ^ (-η) := by
        calc
          240 * ((1 / 240 : ℝ) * N ^ (15 * η)) * N ^ (-16 * η) =
              N ^ (15 * η) * N ^ (-16 * η) := by ring
          _ = N ^ (-η) := by
            rw [← Real.rpow_add hNpos]
            congr 1 <;> ring
      _ ≤ N ^ (-η / 4) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc
    36 * Real.log (2 * (M : ℝ)) * N ^ (-η / 2) +
        120 * Real.log (2 * (M : ℝ)) * N ^ (-16 * η) ≤
      N ^ (-η / 4) + N ^ (-η / 4) := add_le_add hfirst hsecond
    _ = 2 * N ^ (-η / 4) := by ring

/-- The blueprint's target exponent `δ=η/4` is smaller than the continuous
model decay exponent `(1/100)/c`. -/
theorem progressionParameters_delta_lt_model_exponent {c : ℝ}
    (hc : 1 < c) :
    let j : ℕ := Nat.ceil c + 2
    let a : ℝ := 1 / 100
    let η : ℝ := a /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    η / 4 < a / c := by
  dsimp only
  let j : ℕ := Nat.ceil c + 2
  let a : ℝ := 1 / 100
  let η : ℝ := a /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  have hcpos : 0 < c := by linarith
  have hj : c < (j : ℝ) := by
    dsimp [j]
    have hceil : c ≤ (Nat.ceil c : ℝ) := Nat.le_ceil c
    exact lt_of_le_of_lt hceil (by norm_num)
  have hpow : 1 ≤ (2 : ℝ) ^ (j : ℝ) := by
    calc
      1 = (2 : ℝ) ^ (0 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (j : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by exact_mod_cast (Nat.zero_le (Nat.ceil c + 2)))
  have hden : c < 400 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ) := by
    have hjpos : 0 < (j : ℝ) := by linarith
    nlinarith [hj, hpow]
  have hηdiv : η / 4 = a /
      (400 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ)) := by
    dsimp [η]
    field_simp
    ring
  rw [hηdiv]
  apply (div_lt_div_iff₀ (by positivity : 0 <
    400 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ)) hcpos).2
  have ha : 0 < a := by dsimp [a]; norm_num
  exact mul_lt_mul_of_pos_left hden ha

/-- The high-frequency case of the blueprint's normalized progression
approximation, including the continuous model and the final `N^(-η/4)` saving. -/
theorem exists_highFrequency_floorProgression_powerSaving {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        N ^ ((1 / 100 : ℝ) - c) < |ξ| →
      ‖((d : ℝ) / N : ℝ) •
          (∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            unitFrequencyPhase
              (ξ * (Int.floor ((((d : ℝ) * (n : ℝ)) ^ c)) : ℝ))) -
        continuousFractionalModel c N ξ‖ ≤
        (3 + (Real.pi * c)⁻¹) * N ^ (-δ) := by
  dsimp only
  obtain ⟨Nfloor, hNfloor, hfloor⟩ :=
    exists_highFrequency_progression_floor_sum_bound hc hcNon
  obtain ⟨Nabs, hNabs, habsorb⟩ :=
    exists_progression_log_terms_absorption
      (η := (1 / 100 : ℝ) /
        (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
          (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)))
      (by positivity)
      (by have hη := progressionParameters_eta_le_frequency_cutoff hc
          norm_num at hη ⊢
          exact le_trans hη (by norm_num))
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  have hηpos : 0 < η := by dsimp [η, j]; positivity
  have hδmodel := progressionParameters_delta_lt_model_exponent hc
  let N₀ : ℝ := max Nfloor Nabs
  have hN₀ : 3 ≤ N₀ := by
    dsimp [N₀]
    exact le_max_of_le_left hNfloor
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN d hd hdcut ξ hξlo hξhi hξhigh
  have hNfloor' : Nfloor ≤ N := le_trans (le_max_left _ _) hN
  have hNabs' : Nabs ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := le_trans (by norm_num : (1 : ℝ) ≤ 3)
    (le_trans hN₀ hN)
  have hNpos : 0 < N := by linarith
  have hsample := hfloor N hNfloor' d hd hdcut ξ hξlo hξhi hξhigh
  dsimp only at hsample
  rcases hsample with ⟨hM, hsample⟩
  let M : ℕ := Nat.floor (N ^ η)
  have hM' : 2 ≤ M := by simpa [M, η, j, Nat.cast_add] using hM
  have hMη : (M : ℝ) ≤ N ^ η := by
    dsimp [M]
    exact Nat.floor_le (by positivity)
  have hlogAbs := habsorb N hNabs' M hM' hMη
  have hδmodel' : η / 4 < (1 / 100 : ℝ) / c := by
    simpa [η, j] using hδmodel
  have hmodel := continuousFractionalModel_highFrequency_power_bound
    hc hN1 (by norm_num : (0 : ℝ) ≤ 1 / 100) hξhigh
  have hmodel' :
      ‖continuousFractionalModel c N ξ‖ ≤
        (1 + (Real.pi * c)⁻¹) * N ^ (-δ) := by
    have hexp : -(1 / 100 : ℝ) / c ≤ -δ := by
      calc
        -(1 / 100 : ℝ) / c = -((1 / 100 : ℝ) / c) := by ring
        _ ≤ -(η / 4) := neg_le_neg hδmodel'.le
        _ = -δ := by rfl
    calc
      ‖continuousFractionalModel c N ξ‖ ≤
          (1 + (Real.pi * c)⁻¹) * N ^ (-(1 / 100 : ℝ) / c) := by
            simpa using hmodel
      _ ≤ (1 + (Real.pi * c)⁻¹) * N ^ (-δ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hN1 hexp) (by positivity)
  let S : ℂ :=
    ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
      unitFrequencyPhase (ξ * (Int.floor ((((d : ℝ) * (n : ℝ)) ^ c)) : ℝ))
  have hscale : 0 ≤ (d : ℝ) / N := by positivity
  have hnormScale : ‖((d : ℝ) / N : ℝ) • S‖ =
      ((d : ℝ) / N) * ‖S‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  have hsample' : ((d : ℝ) / N) * ‖S‖ ≤ 2 * N ^ (-δ) := by
    calc
      ((d : ℝ) / N) * ‖S‖ ≤ 2 * N ^ ((-η) / 4) := by
        simpa [M, S, η, j, Nat.cast_add] using hsample.trans hlogAbs
      _ = 2 * N ^ (-δ) := by
        congr 2
        dsimp [δ]
        ring
  calc
    ‖((d : ℝ) / N : ℝ) • S - continuousFractionalModel c N ξ‖ ≤
        ‖((d : ℝ) / N : ℝ) • S‖ +
          ‖continuousFractionalModel c N ξ‖ := norm_sub_le _ _
    _ ≤ 2 * N ^ (-δ) +
          (1 + (Real.pi * c)⁻¹) * N ^ (-δ) := by
            rw [hnormScale]
            exact add_le_add hsample' hmodel'
    _ = (3 + (Real.pi * c)⁻¹) * N ^ (-δ) := by ring

/-- Reindex the exact integer interval `(0,Y]` by the natural indices
`0≤i<floor(Y)`, retaining the sample `i+1`. -/
theorem realIntegerInterval_zero_eq_nat_Ico {Y : ℝ} (hY : 0 ≤ Y) :
    realIntegerInterval 0 Y =
      (Finset.Ico 0 (Nat.floor Y)).map
        ⟨fun i : ℕ => ((i + 1 : ℕ) : ℤ), by
          intro i₁ i₂ h
          change ((i₁ + 1 : ℕ) : ℤ) = ((i₂ + 1 : ℕ) : ℤ) at h
          exact Nat.add_right_cancel (Int.ofNat.inj h)⟩ := by
  let e : ℕ ↪ ℤ := ⟨fun i => ((i + 1 : ℕ) : ℤ), by
    intro i₁ i₂ h
    change ((i₁ + 1 : ℕ) : ℤ) = ((i₂ + 1 : ℕ) : ℤ) at h
    exact Nat.add_right_cancel (Int.ofNat.inj h)⟩
  have hfloor : (Nat.floor Y : ℤ) = Int.floor Y := by
    rw [← Int.floor_toNat Y]
    exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr hY)
  ext z
  rw [mem_realIntegerInterval_iff]
  simp only [Finset.mem_map, Finset.mem_Ico, e]
  constructor
  · rintro ⟨hzpos, hzY⟩
    have hzposInt : 0 < z := by exact_mod_cast hzpos
    have hznonneg : 0 ≤ z := le_of_lt hzposInt
    have hzcast : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hznonneg
    have hzfloor : z.toNat ≤ Nat.floor Y := by
      apply Nat.le_floor
      have hcastreal : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
        exact_mod_cast hzcast
      rw [hcastreal]
      simpa using hzY
    have hzNatPos : 1 ≤ z.toNat := by
      have hzposNat : 0 < z.toNat := by
        have : (0 : ℤ) < (z.toNat : ℤ) := by simpa [hzcast] using hzposInt
        exact_mod_cast this
      omega
    refine ⟨z.toNat - 1, ?_, ?_⟩
    · constructor
      · exact Nat.zero_le _
      · omega
    · change ((z.toNat - 1 + 1 : ℕ) : ℤ) = z
      have hsucc : z.toNat - 1 + 1 = z.toNat := by omega
      rw [hsucc]
      exact hzcast
  · rintro ⟨i, hi, hzi⟩
    have hi' : i + 1 ≤ Nat.floor Y := by omega
    have hnatcast : ((i + 1 : ℕ) : ℤ) = z := hzi
    constructor
    · have hzposInt : (0 : ℤ) < z := by
        rw [← hnatcast]
        exact_mod_cast (show (0 : ℕ) < i + 1 by omega)
      exact_mod_cast hzposInt
    · calc
        (z : ℝ) = ((i + 1 : ℕ) : ℝ) := by exact_mod_cast hnatcast.symm
        _ ≤ (Nat.floor Y : ℝ) := by exact_mod_cast hi'
        _ ≤ 0 + Y := by simpa using (Nat.floor_le hY)

/-- Sum form of `realIntegerInterval_zero_eq_nat_Ico`. -/
theorem sum_realIntegerInterval_zero_eq_nat_Ico
    {α : Type*} [AddCommMonoid α] {Y : ℝ} (hY : 0 ≤ Y)
    (f : ℤ → α) :
    (∑ z ∈ realIntegerInterval 0 Y, f z) =
      ∑ i ∈ Finset.Ico 0 (Nat.floor Y), f ((i + 1 : ℕ) : ℤ) := by
  rw [realIntegerInterval_zero_eq_nat_Ico hY]
  rw [Finset.sum_map]
  rfl

/-- Reindex the sampled floor phase on `(0,N/d]` to the exact natural prefix
used by the low-frequency proof. -/
theorem progression_floorPhase_sum_reindex {N d ξ c : ℝ}
    (hY : 0 ≤ N / d) :
    (∑ n ∈ realIntegerInterval 0 (N / d),
      unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) =
    ∑ i ∈ Finset.Ico 0 (Nat.floor (N / d)),
      unitFrequencyPhase
        (ξ * (Int.floor ((d * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℝ)) := by
  rw [sum_realIntegerInterval_zero_eq_nat_Ico hY]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2

/-- The full uniform progression approximation, combining the low- and
high-frequency cases with the blueprint's exact parameters. -/
theorem exists_progression_floorPrefix_powerSaving {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖((d : ℝ) / N : ℝ) •
            (Finset.Ico 0 (Nat.floor (N / (d : ℝ)))).sum
              (fun i => unitFrequencyPhase
                (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
          continuousFractionalModel c N ξ‖ ≤
        ((2 * Real.pi + 2 * Real.pi * c + 1) +
          (3 + (Real.pi * c)⁻¹)) * N ^ (-δ) := by
  dsimp only
  obtain ⟨Nlow, hNlow, hlow⟩ :=
    exists_lowFrequency_floorProgression_powerSaving hc
  obtain ⟨Nhigh, hNhigh, hhigh⟩ :=
    exists_highFrequency_floorProgression_powerSaving hc hcNon
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  let C₀ : ℝ := 2 * Real.pi + 2 * Real.pi * c + 1
  let C₁ : ℝ := 3 + (Real.pi * c)⁻¹
  let C : ℝ := C₀ + C₁
  let N₀ : ℝ := max Nlow Nhigh
  have hN₀ : 3 ≤ N₀ := by
    dsimp [N₀]
    exact le_max_of_le_left hNlow
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN d hd hdcut ξ hξlo hξhi
  have hNlow' : Nlow ≤ N := le_trans (le_max_left _ _) hN
  have hNhigh' : Nhigh ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := le_trans (by norm_num : (1 : ℝ) ≤ 3)
    (le_trans hN₀ hN)
  have hNpos : 0 < N := by linarith
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hpow : 0 ≤ N ^ (-δ) := Real.rpow_nonneg (le_of_lt hNpos) _
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  by_cases hlowfreq : |ξ| ≤ N ^ ((1 / 100 : ℝ) - c)
  · have hcase := hlow N hNlow' (d : ℝ) hdpos hdcut ξ hlowfreq
    have hconst : C₀ ≤ C := by change C₀ ≤ C₀ + C₁; exact le_add_of_nonneg_right hC₁
    calc
      ‖((d : ℝ) / N : ℝ) •
          (Finset.Ico 0 (Nat.floor (N / (d : ℝ)))).sum
            (fun i => unitFrequencyPhase
              (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
          continuousFractionalModel c N ξ‖ ≤ C₀ * N ^ (-δ) := by
            simpa [C₀, η, j, δ, Nat.cast_add, one_div] using hcase
      _ ≤ C * N ^ (-δ) := mul_le_mul_of_nonneg_right hconst hpow
      _ = ((2 * Real.pi + 2 * Real.pi * c + 1) +
          (3 + (Real.pi * c)⁻¹)) * N ^ (-δ) := by rfl
  · have hhighfreq : N ^ ((1 / 100 : ℝ) - c) < |ξ| := lt_of_not_ge hlowfreq
    have hcase := hhigh N hNhigh' d hd hdcut ξ hξlo hξhi hhighfreq
    have hreindex := progression_floorPhase_sum_reindex
      (N := N) (d := (d : ℝ)) (ξ := ξ) (c := c) (by positivity)
    rw [hreindex] at hcase
    have hconst : C₁ ≤ C := by change C₁ ≤ C₀ + C₁; exact le_add_of_nonneg_left hC₀
    calc
      ‖((d : ℝ) / N : ℝ) •
          (Finset.Ico 0 (Nat.floor (N / (d : ℝ)))).sum
            (fun i => unitFrequencyPhase
              (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
          continuousFractionalModel c N ξ‖ ≤ C₁ * N ^ (-δ) := by
            simpa [C₁, η, j, δ, Nat.cast_add, one_div] using hcase
      _ ≤ C * N ^ (-δ) := mul_le_mul_of_nonneg_right hconst hpow
      _ = ((2 * Real.pi + 2 * Real.pi * c + 1) +
          (3 + (Real.pi * c)⁻¹)) * N ^ (-δ) := by rfl

/-- Rescale a normalized progression error into the raw sum form needed for
subtracting estimates at two endpoints. -/
theorem progression_raw_rescaling_identity {d N : ℝ} (hd : 0 < d) (hN : 0 < N)
    (S I : ℂ) :
    (N / d : ℝ) • ((d / N : ℝ) • S - (N : ℂ)⁻¹ * I) =
      S - ((d : ℝ)⁻¹ : ℂ) * I := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  simp only [Complex.real_smul]
  push_cast
  field_simp [hNne, hdne]

/-- Convert a normalized progression error bound into its raw-sum scale. -/
theorem progression_normalized_error_to_raw {d N δ C : ℝ} (hd : 0 < d)
    (hN : 0 < N) (hC : 0 ≤ C) (S I : ℂ)
    (hbound : ‖(d / N : ℝ) • S - (N : ℂ)⁻¹ * I‖ ≤ C * N ^ (-δ)) :
    ‖S - ((d : ℝ)⁻¹ : ℂ) * I‖ ≤ C * (N ^ (1 - δ) / d) := by
  have hpow : N ^ (1 - δ) = N * N ^ (-δ) := by
    rw [show (1 - δ : ℝ) = 1 + (-δ) by ring, Real.rpow_add hN,
      Real.rpow_one]
  have hexact := progression_raw_rescaling_identity hd hN S I
  calc
    ‖S - ((d : ℝ)⁻¹ : ℂ) * I‖ =
        (N / d) * ‖(d / N : ℝ) • S - (N : ℂ)⁻¹ * I‖ := by
          rw [← hexact, norm_smul, Real.norm_eq_abs,
            abs_of_pos (div_pos hN hd)]
    _ ≤ (N / d) * (C * N ^ (-δ)) :=
      mul_le_mul_of_nonneg_left hbound (le_of_lt (div_pos hN hd))
    _ = C * (N ^ (1 - δ) / d) := by rw [hpow]; ring

/-- The blueprint's normalized full-prefix estimate implies its raw prefix
form, with the integral over `[0,N]` and the exact factor `N^(1-δ)/d`. -/
theorem exists_progression_floorPrefix_raw_powerSaving {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖(∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            unitFrequencyPhase
              (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
          ((d : ℝ)⁻¹ : ℂ) *
            (∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c))‖ ≤
          ((2 * Real.pi + 2 * Real.pi * c + 1) +
            (3 + (Real.pi * c)⁻¹)) * (N ^ (1 - δ) / (d : ℝ)) := by
  dsimp only
  obtain ⟨N₀, hN₀, hnormalized⟩ :=
    exists_progression_floorPrefix_powerSaving hc hcNon
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN d hd hdcut ξ hξlo hξhi
  have hNpos : 0 < N := by
    have : (0 : ℝ) < 3 := by norm_num
    exact lt_of_lt_of_le this (le_trans hN₀ hN)
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hd)
  let S : ℂ := ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
    unitFrequencyPhase (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))
  let I : ℂ := ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)
  have hsum : S =
      ∑ i ∈ Finset.Ico 0 (Nat.floor (N / (d : ℝ))),
        unitFrequencyPhase
          (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ)) := by
    dsimp [S]
    exact sum_realIntegerInterval_zero_eq_nat_Ico (by positivity) _
  have hnormalized' := hnormalized N hN d hd hdcut ξ hξlo hξhi
  rw [← hsum] at hnormalized'
  have hbound :
      ‖((d : ℝ) / N : ℝ) • S - (N : ℂ)⁻¹ * I‖ ≤
        ((2 * Real.pi + 2 * Real.pi * c + 1) +
          (3 + (Real.pi * c)⁻¹)) * N ^ (-((1 / 100 : ℝ) /
            (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
              (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4)) := by
    simpa [S, I, continuousFractionalModel] using hnormalized'
  have hδ :
      ((1 / 100 : ℝ) /
        (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
          (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4) =
        ((1 / 100 : ℝ) /
          (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4 := by ring
  have hbound' :
      ‖((d : ℝ) / N : ℝ) • S - (N : ℂ)⁻¹ * I‖ ≤
        ((2 * Real.pi + 2 * Real.pi * c + 1) +
          (3 + (Real.pi * c)⁻¹)) * N ^ (-(((1 / 100 : ℝ) /
            (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
              (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4)) := by
    simpa only [hδ] using hbound
  exact progression_normalized_error_to_raw hdpos hNpos (by positivity)
    S I hbound'

/-- The progression sum over `(X/d,(X+H)/d]` is exactly the difference of its
two positive-prefix sums, with the paper's half-open endpoint convention. -/
theorem progression_floorInterval_eq_prefix_difference
    {X H d ξ c : ℝ} (hd : 0 < d) (hX : 0 ≤ X) (hH : 0 ≤ H) :
    (∑ n ∈ realIntegerInterval (X / d) (H / d),
      unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) =
      (∑ n ∈ realIntegerInterval 0 ((X + H) / d),
        unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) -
      (∑ n ∈ realIntegerInterval 0 (X / d),
        unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) := by
  have hdiv : (X + H) / d = X / d + H / d := by
    field_simp
  have hsplit := sum_realIntegerInterval_split
    (x := 0) (Y := X / d) (Z := H / d)
    (div_nonneg hX hd.le) (div_nonneg hH hd.le)
    (fun n : ℤ =>
      unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ)))
  rw [← hdiv] at hsplit
  calc
    (∑ n ∈ realIntegerInterval (X / d) (H / d),
        unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) =
      (∑ n ∈ realIntegerInterval 0 ((X + H) / d),
        unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) -
      (∑ n ∈ realIntegerInterval 0 (X / d),
        unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) := by
          rw [hsplit]
          abel

/-- Additivity of the continuous phase integral in the same endpoint
subtraction used for progression prefixes. -/
theorem fractionalPhaseIntegral_prefix_difference
    {f : ℝ → ℂ} {X H : ℝ}
    (hleft : IntervalIntegrable f MeasureTheory.volume 0 X)
    (hright : IntervalIntegrable f MeasureTheory.volume X (X + H)) :
    (∫ t in X..(X + H), f t) =
      (∫ t in (0 : ℝ)..(X + H), f t) - (∫ t in (0 : ℝ)..X, f t) := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  calc
    (∫ t in X..(X + H), f t) =
        ((∫ t in (0 : ℝ)..X, f t) +
          (∫ t in X..(X + H), f t)) - (∫ t in (0 : ℝ)..X, f t) := by abel
    _ = (∫ t in (0 : ℝ)..(X + H), f t) -
        (∫ t in (0 : ℝ)..X, f t) := by rw [← hsplit]

/-- Subtracting the two raw progression prefixes gives exactly the short-block
sum minus its matching continuous phase integral. -/
theorem progression_floorInterval_error_eq_prefix_error_difference
    {X H d ξ c : ℝ} (hd : 0 < d) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (hleft : IntervalIntegrable
      (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c)) MeasureTheory.volume 0 X)
    (hright : IntervalIntegrable
      (fun t : ℝ => unitFrequencyPhase (ξ * t ^ c))
        MeasureTheory.volume X (X + H)) :
    (∑ n ∈ realIntegerInterval (X / d) (H / d),
        unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) -
      ((d : ℝ)⁻¹ : ℂ) *
        (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c)) =
      ((∑ n ∈ realIntegerInterval 0 ((X + H) / d),
          unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) -
        ((d : ℝ)⁻¹ : ℂ) *
          (∫ t in (0 : ℝ)..(X + H), unitFrequencyPhase (ξ * t ^ c))) -
      ((∑ n ∈ realIntegerInterval 0 (X / d),
          unitFrequencyPhase (ξ * (Int.floor ((d * (n : ℝ)) ^ c) : ℝ))) -
        ((d : ℝ)⁻¹ : ℂ) *
          (∫ t in (0 : ℝ)..X, unitFrequencyPhase (ξ * t ^ c))) := by
  rw [progression_floorInterval_eq_prefix_difference hd hX hH,
    fractionalPhaseIntegral_prefix_difference hleft hright]
  rw [mul_sub]
  abel

/-- The divisor cutoff `exp((log X)^(3/10))` is increasing on scales above 1. -/
theorem progression_divisorCutoff_mono {X Y : ℝ} (hX : 1 < X) (hXY : X ≤ Y) :
    Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) ≤
      Real.exp ((Real.log Y) ^ (3 / 10 : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog : Real.log X ≤ Real.log Y :=
    Real.log_le_log (by linarith) hXY
  exact Real.rpow_le_rpow hlogX hlog (by norm_num)

/-- The fixed progression saving exponent lies strictly between zero and one. -/
theorem progressionParameters_delta_bounds {c : ℝ} (hc : 1 < c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    0 < δ ∧ δ < 1 := by
  dsimp only
  have hparams := progressionParameters_lowFrequency_exponents hc
  have hηpos : 0 < (1 / 100 : ℝ) /
      (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) := by
    exact hparams.2.2.2.2
  have hηle := progressionParameters_eta_le_frequency_cutoff hc
  constructor
  · positivity
  · have hηbound :
        (1 / 100 : ℝ) /
          (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) ≤ 1 / 10000 := by
      simpa only using hηle
    have hδbound :
        ((1 / 100 : ℝ) /
          (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4 ≤ 1 / 40000 := by
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by norm_num at hηbound ⊢; nlinarith)
    linarith

/-- The difference-of-endpoints progression estimate in the eventual scale
range. The bounded initial scales are handled separately below when
packaging the full blueprint statement. -/
theorem exists_intervalProgressionApproximation_large {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    let A : ℝ := (2 * Real.pi + 2 * Real.pi * c + 1) +
      (3 + (Real.pi * c)⁻¹)
    ∃ K₀ : ℝ, 3 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      ∀ X H : ℝ, K ≤ X → X < X + H → X + H ≤ 2 * K →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖(∑ n ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
            unitFrequencyPhase
              (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
          ((d : ℝ)⁻¹ : ℂ) *
            (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))‖ ≤
          2 * A * (2 : ℝ) ^ (1 - δ) *
            (K ^ (1 - δ) / (d : ℝ)) := by
  dsimp only
  obtain ⟨N₀, hN₀, hraw⟩ :=
    exists_progression_floorPrefix_raw_powerSaving hc hcNon
  have hδparams := progressionParameters_delta_bounds hc
  dsimp only at hδparams
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  let A : ℝ := (2 * Real.pi + 2 * Real.pi * c + 1) +
    (3 + (Real.pi * c)⁻¹)
  have hδpos : 0 < δ := by dsimp [δ, η, j]; positivity
  have hδlt : δ < 1 := by
    have hηle := progressionParameters_eta_le_frequency_cutoff hc
    dsimp [δ, η, j]
    have hηbound :
        (1 / 100 : ℝ) /
          (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) ≤ 1 / 10000 := by
      simpa only using hηle
    nlinarith
  have hqpos : 0 < 1 - δ := by linarith
  have hApos : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨N₀, hN₀, ?_⟩
  intro K hK X H hKX hXH hEnd d hd hdcut ξ hξlo hξhi
  have hKpos : 0 < K := by linarith [hN₀]
  have hXpos : 1 < X := by linarith [hN₀, hK, hKX]
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hd)
  have hXnonneg : 0 ≤ X := le_of_lt (by linarith)
  have hHpos : 0 < H := by linarith
  have hHnonneg : 0 ≤ H := le_of_lt hHpos
  have hNstart : N₀ ≤ X := le_trans hK hKX
  have hNend : N₀ ≤ X + H := le_trans hNstart (le_of_lt hXH)
  have hcutEnd : (d : ℝ) ≤ Real.exp (Real.log (X + H) ^ (3 / 10 : ℝ)) :=
    le_trans hdcut (progression_divisorCutoff_mono hXpos (le_of_lt hXH))
  let f : ℝ → ℂ := fun t => unitFrequencyPhase (ξ * t ^ c)
  have hfcont : Continuous f := by
    dsimp [f]
    exact continuous_unitFrequencyPhase.comp
      (continuous_const.mul (Real.continuous_rpow_const (by linarith [hc])))
  have hleft : IntervalIntegrable f MeasureTheory.volume 0 X :=
    hfcont.intervalIntegrable 0 X
  have hright : IntervalIntegrable f MeasureTheory.volume X (X + H) :=
    hfcont.intervalIntegrable X (X + H)
  have hEend := hraw (X + H) hNend d hd hcutEnd ξ hξlo hξhi
  have hEstart := hraw X hNstart d hd hdcut ξ hξlo hξhi
  have herror := progression_floorInterval_error_eq_prefix_error_difference
    (X := X) (H := H) (d := (d : ℝ)) (ξ := ξ) (c := c)
    hdpos hXnonneg hHnonneg hleft hright
  have hq : 0 ≤ 1 - δ := le_of_lt hqpos
  have hXupper : X ≤ 2 * K := le_trans (le_of_lt hXH) hEnd
  have hEndPower : (X + H) ^ (1 - δ) ≤ (2 * K) ^ (1 - δ) :=
    Real.rpow_le_rpow (le_of_lt (by linarith : 0 < X + H)) hEnd hq
  have hXPower : X ^ (1 - δ) ≤ (2 * K) ^ (1 - δ) :=
    Real.rpow_le_rpow (le_of_lt (by linarith : 0 < X)) hXupper hq
  have hboundEnd :
      A * ((X + H) ^ (1 - δ) / (d : ℝ)) ≤
        A * ((2 * K) ^ (1 - δ) / (d : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hApos
    exact div_le_div_of_nonneg_right hEndPower (le_of_lt hdpos)
  have hboundStart :
      A * (X ^ (1 - δ) / (d : ℝ)) ≤
        A * ((2 * K) ^ (1 - δ) / (d : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hApos
    exact div_le_div_of_nonneg_right hXPower (le_of_lt hdpos)
  calc
    ‖(∑ n ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
        unitFrequencyPhase
          (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
      ((d : ℝ)⁻¹ : ℂ) * (∫ t in X..(X + H), f t)‖ =
        ‖((∑ n ∈ realIntegerInterval 0 ((X + H) / (d : ℝ)),
              unitFrequencyPhase
                (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
            ((d : ℝ)⁻¹ : ℂ) * (∫ t in (0 : ℝ)..(X + H), f t)) -
          ((∑ n ∈ realIntegerInterval 0 (X / (d : ℝ)),
              unitFrequencyPhase
                (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
            ((d : ℝ)⁻¹ : ℂ) * (∫ t in (0 : ℝ)..X, f t))‖ := by
              rw [herror]
    _ ≤
        ‖(∑ n ∈ realIntegerInterval 0 ((X + H) / (d : ℝ)),
              unitFrequencyPhase
                (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
            ((d : ℝ)⁻¹ : ℂ) * (∫ t in (0 : ℝ)..(X + H), f t)‖ +
        ‖(∑ n ∈ realIntegerInterval 0 (X / (d : ℝ)),
              unitFrequencyPhase
                (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
            ((d : ℝ)⁻¹ : ℂ) * (∫ t in (0 : ℝ)..X, f t)‖ := norm_sub_le _ _
    _ ≤ A * ((X + H) ^ (1 - δ) / (d : ℝ)) +
        A * (X ^ (1 - δ) / (d : ℝ)) := add_le_add hEend hEstart
    _ ≤ 2 * A * ((2 * K) ^ (1 - δ) / (d : ℝ)) := by
      linarith [hboundEnd, hboundStart]
    _ = 2 * A * (2 : ℝ) ^ (1 - δ) *
          (K ^ (1 - δ) / (d : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hKpos)]
      ring

/-- A trivial bound handles all bounded scales while retaining the divisor
factor in the blueprint's error term. -/
theorem progressionInterval_bounded_scale_bound
    {K₀ K X H c ξ δ : ℝ} {d : ℕ}
    (hK₀ : 3 ≤ K₀) (hKlo : 3 ≤ K) (hKhi : K ≤ K₀)
    (hKX : K ≤ X) (hXH : X < X + H) (hEnd : X + H ≤ 2 * K)
    (hd : 1 ≤ d) (hdcut : (d : ℝ) ≤ Real.exp (Real.log X ^ (3 / 10 : ℝ)))
    (hδpos : 0 < δ) (hδlt : δ < 1) :
    ‖(∑ n ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
        unitFrequencyPhase (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
      ((d : ℝ)⁻¹ : ℂ) *
        (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))‖ ≤
      ((2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
        (3 : ℝ) ^ (1 - δ)) * (K ^ (1 - δ) / (d : ℝ)) := by
  have hKpos : 0 < K := by linarith
  have hXpos : 1 < X := by linarith
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hd)
  have hHpos : 0 < H := by linarith
  have hHle : H ≤ K := by linarith
  have hXupper : X ≤ 2 * K₀ := by
    exact le_trans (le_of_lt hXH) (le_trans hEnd (by nlinarith [hKhi]))
  have hcutBound :
      Real.exp (Real.log X ^ (3 / 10 : ℝ)) ≤
        Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ)) :=
    progression_divisorCutoff_mono hXpos (by linarith [hXupper])
  have hdBound : (d : ℝ) ≤ Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ)) :=
    le_trans hdcut hcutBound
  have hYnonneg : 0 ≤ H / (d : ℝ) := div_nonneg (le_of_lt hHpos) hdpos.le
  have hsum :
      ‖∑ n ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
        unitFrequencyPhase (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))‖ ≤
      H / (d : ℝ) + 1 := by
    calc
      _ ≤ ∑ n ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
          ‖unitFrequencyPhase (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))‖ :=
        norm_sum_le _ _
      _ = (realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ))).card := by
        simp [norm_unitFrequencyPhase]
      _ ≤ H / (d : ℝ) + 1 :=
        realIntegerInterval_card_le_of_nonneg _ _ hYnonneg
  have hInt := norm_fractionalPhaseIntegral_interval_le_length
    (c := c) (ξ := ξ) (a := X) (b := X + H) (le_of_lt hXH)
  have hInt' :
      ‖∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c)‖ ≤ H := by
    nlinarith [hInt]
  have hinvnorm : ‖((d : ℝ)⁻¹ : ℂ)‖ = (d : ℝ)⁻¹ := by
    simp [Complex.norm_real, abs_of_pos (inv_pos.mpr hdpos)]
  have hIntScaled :
      ‖((d : ℝ)⁻¹ : ℂ) *
          (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))‖ ≤
        H / (d : ℝ) := by
    rw [norm_mul, hinvnorm]
    calc
      (d : ℝ)⁻¹ *
          ‖∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c)‖ ≤
        (d : ℝ)⁻¹ * H :=
          mul_le_mul_of_nonneg_left hInt' (by positivity)
      _ = H / (d : ℝ) := by ring
  have hsumTotal :
      ‖(∑ n ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
          unitFrequencyPhase (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
        ((d : ℝ)⁻¹ : ℂ) *
          (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))‖ ≤
      (2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) / (d : ℝ) := by
    calc
      _ ≤ ‖∑ n ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
            unitFrequencyPhase
              (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))‖ +
          ‖((d : ℝ)⁻¹ : ℂ) *
            (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))‖ := norm_sub_le _ _
      _ ≤ H / (d : ℝ) + 1 + H / (d : ℝ) := add_le_add hsum hIntScaled
      _ ≤ (2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
          (d : ℝ) := by
        have hHd : H / (d : ℝ) ≤ K₀ / (d : ℝ) :=
          div_le_div_of_nonneg_right (le_trans hHle hKhi) hdpos.le
        have hone : 1 ≤ Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ)) / (d : ℝ) :=
          (le_div_iff₀ hdpos).2 (by simpa using hdBound)
        have hsplit :
            (2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
              (d : ℝ) =
            2 * (K₀ / (d : ℝ)) +
              Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ)) / (d : ℝ) := by ring
        rw [hsplit]
        nlinarith [hHd, hone]
  have hqpos : 0 < 1 - δ := by linarith
  have hpow : (3 : ℝ) ^ (1 - δ) ≤ K ^ (1 - δ) :=
    Real.rpow_le_rpow (by norm_num) hKlo (le_of_lt hqpos)
  have hqden : 0 < (3 : ℝ) ^ (1 - δ) := Real.rpow_pos_of_pos (by norm_num) _
  have hconstant : 0 ≤
      (2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) := by positivity
  have hscaled :
      2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ)) ≤
        ((2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
          (3 : ℝ) ^ (1 - δ)) * K ^ (1 - δ) := by
    calc
      _ = ((2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
          (3 : ℝ) ^ (1 - δ)) * (3 : ℝ) ^ (1 - δ) := by
            field_simp
      _ ≤ ((2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
          (3 : ℝ) ^ (1 - δ)) * K ^ (1 - δ) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
  have hscaledDiv :
      (2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) / (d : ℝ) ≤
        (((2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
          (3 : ℝ) ^ (1 - δ)) * K ^ (1 - δ)) / (d : ℝ) :=
    div_le_div_of_nonneg_right hscaled hdpos.le
  calc
    _ ≤ (2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) / (d : ℝ) := hsumTotal
    _ ≤ (((2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
          (3 : ℝ) ^ (1 - δ)) * K ^ (1 - δ)) / (d : ℝ) := hscaledDiv
    _ = ((2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
          (3 : ℝ) ^ (1 - δ)) * (K ^ (1 - δ) / (d : ℝ)) := by ring

/-- The full blueprint short-interval progression approximation, valid from
`K≥3` after combining the eventual analytic estimate with the bounded-scale
trivial estimate. -/
theorem intervalProgressionApproximation {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ K : ℝ, 3 ≤ K →
      ∀ X H : ℝ, K ≤ X → X < X + H → X + H ≤ 2 * K →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖(∑ n ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
            unitFrequencyPhase
              (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
          ((d : ℝ)⁻¹ : ℂ) *
            (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))‖ ≤
          Cc * (K ^ (1 - δ) / (d : ℝ)) := by
  dsimp only
  obtain ⟨K₀, hK₀, hlarge⟩ :=
    exists_intervalProgressionApproximation_large hc hcNon
  have hδparams := progressionParameters_delta_bounds hc
  dsimp only at hδparams
  have hδpos : 0 < (1 / 100 : ℝ) /
      (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4 := by
    exact hδparams.1
  have hδlt : (1 / 100 : ℝ) /
      (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4 < 1 := by
    exact hδparams.2
  let δ : ℝ := ((1 / 100 : ℝ) /
    (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
      (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4
  let A : ℝ := (2 * Real.pi + 2 * Real.pi * c + 1) +
    (3 + (Real.pi * c)⁻¹)
  let Cbig : ℝ := 2 * A * (2 : ℝ) ^ (1 - δ)
  let Csmall : ℝ :=
    (2 * K₀ + Real.exp (Real.log (2 * K₀) ^ (3 / 10 : ℝ))) /
      (3 : ℝ) ^ (1 - δ)
  let Cc : ℝ := max Cbig Csmall
  have hCc : 0 ≤ Cc := by
    dsimp [Cc, Cbig, Csmall, A]
    positivity
  refine ⟨Cc, hCc, ?_⟩
  intro K hK X H hKX hXH hEnd d hd hdcut ξ hξlo hξhi
  have hq : 0 ≤ K ^ (1 - δ) / (d : ℝ) :=
    div_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ K) _) (by positivity)
  by_cases hlargeK : K₀ ≤ K
  · have hbound := hlarge K hlargeK X H hKX hXH hEnd d hd hdcut ξ hξlo hξhi
    calc
      _ ≤ Cbig * (K ^ (1 - δ) / (d : ℝ)) := by
        simpa [Cbig, A, δ, Nat.cast_add, one_div] using hbound
      _ ≤ Cc * (K ^ (1 - δ) / (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hq
  · have hKhi : K ≤ K₀ := le_of_not_ge hlargeK
    have hδpos' : 0 < δ := by simpa [δ] using hδpos
    have hδlt' : δ < 1 := by simpa [δ] using hδlt
    have hbound := progressionInterval_bounded_scale_bound
      (c := c) (ξ := ξ) (δ := δ)
      hK₀ hK hKhi hKX hXH hEnd hd hdcut hδpos' hδlt'
    calc
      _ ≤ Csmall * (K ^ (1 - δ) / (d : ℝ)) := by
        simpa [Csmall, δ, Nat.cast_add, one_div] using hbound
      _ ≤ Cc * (K ^ (1 - δ) / (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hq

/-- The fixed arithmetic parameters from `ar:parameters`, represented without
scale-dependent choices. `j` and `D` are naturals as in the blueprint. -/
structure ArithmeticParameters (c : ℝ) where
  j : ℕ
  D : ℕ
  a : ℝ
  b : ℝ
  κ : ℝ
  εd : ℝ
  η : ℝ
  δ : ℝ
  θ : ℝ
  ε : ℝ
  k : ℕ

/-- The blueprint's exact parameter package for a fixed exponent `c`. -/
noncomputable def arithmeticParameters (c : ℝ) : ArithmeticParameters c := by
  let j : ℕ := Nat.ceil c + 2
  let D : ℕ := 2 ^ j
  let a : ℝ := 1 / 100
  let b : ℝ := 1 / 10000
  let κ : ℝ := a / (10 * (j : ℝ))
  let εd : ℝ := a / (100 * (j : ℝ))
  let η : ℝ := a / (100 * (j : ℝ) * (D : ℝ))
  let δ : ℝ := η / 4
  let θ : ℝ := 1 - δ / 4
  let ε : ℝ := (1 - θ) / 4
  let k : ℕ := Nat.ceil ((c + η + 2) / (1 - θ))
  exact ⟨j, D, a, b, κ, εd, η, δ, θ, ε, k⟩

/-- The chosen Taylor degree has a strict margin over the derivative-order
threshold in `ar:partition`. -/
theorem arithmeticParameters_taylor_degree_margin {c : ℝ} (hc : 1 < c) :
    let p := arithmeticParameters c
    (1 - p.θ) * ((p.k : ℝ) + 1) > c + p.η + 2 := by
  dsimp only
  let p := arithmeticParameters c
  have hηpos : 0 < p.η := by
    dsimp [arithmeticParameters, p]
    positivity
  have hδpos : 0 < p.δ := by
    dsimp [arithmeticParameters, p]
    positivity
  have hθlt : p.θ < 1 := by
    change 1 - p.δ / 4 < 1
    linarith
  have hθden : 1 - p.θ = p.δ / 4 := by
    change 1 - (1 - p.δ / 4) = p.δ / 4
    ring
  have hden : 0 < 1 - p.θ := by
    rw [hθden]
    exact div_pos hδpos (by norm_num)
  have hceil : (c + p.η + 2) / (1 - p.θ) ≤ (p.k : ℝ) := by
    dsimp [arithmeticParameters, p]
    exact Nat.le_ceil _
  have hmul : c + p.η + 2 ≤ (p.k : ℝ) * (1 - p.θ) :=
    (div_le_iff₀ hden).mp hceil
  nlinarith [hmul, hden]

/-- The blueprint's chosen block exponent `theta` is positive, so the
floor-power block threshold applies to the exact parameter package. -/
theorem arithmeticParameters_theta_pos {c : ℝ} (hc : 1 < c) :
    0 < (arithmeticParameters c).θ := by
  let p := arithmeticParameters c
  have hj : 1 ≤ Nat.ceil c + 2 := by omega
  have hD : 1 ≤ 2 ^ (Nat.ceil c + 2) := by
    have hDpos : 0 < 2 ^ (Nat.ceil c + 2) := by positivity
    omega
  have hjR : (1 : ℝ) ≤ ((Nat.ceil c + 2 : ℕ) : ℝ) := by exact_mod_cast hj
  have hDR : (1 : ℝ) ≤ ((2 ^ (Nat.ceil c + 2) : ℕ) : ℝ) := by
    exact_mod_cast hD
  have hden : 100 ≤ 100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
      ((2 ^ (Nat.ceil c + 2) : ℕ) : ℝ) := by
    calc
      100 = 100 * 1 * 1 := by ring
      _ ≤ 100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
          ((2 ^ (Nat.ceil c + 2) : ℕ) : ℝ) := by gcongr
  have hηlt : p.η < 1 := by
    dsimp [p, arithmeticParameters]
    have hdenpos : 0 < 100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
        ((2 ^ (Nat.ceil c + 2) : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hdenpos]
    nlinarith [hden]
  have hθeq : p.θ = 1 - p.η / 16 := by
    dsimp [p, arithmeticParameters]
    ring
  rw [hθeq]
  dsimp [p]
  nlinarith [hηlt]

/-- The explicit small parameter `eta` in the blueprint lies strictly between
zero and one. -/
theorem arithmeticParameters_eta_pos_lt_one {c : ℝ} (hc : 1 < c) :
    let p := arithmeticParameters c
    0 < p.η ∧ p.η < 1 := by
  dsimp only
  let p := arithmeticParameters c
  have hj : 1 ≤ Nat.ceil c + 2 := by omega
  have hD : 1 ≤ 2 ^ (Nat.ceil c + 2) := by
    have hDpos : 0 < 2 ^ (Nat.ceil c + 2) := by positivity
    omega
  have hjR : (1 : ℝ) ≤ ((Nat.ceil c + 2 : ℕ) : ℝ) := by exact_mod_cast hj
  have hDR : (1 : ℝ) ≤ ((2 ^ (Nat.ceil c + 2) : ℕ) : ℝ) := by
    exact_mod_cast hD
  have hden : 100 ≤ 100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
      ((2 ^ (Nat.ceil c + 2) : ℕ) : ℝ) := by
    calc
      100 = 100 * 1 * 1 := by ring
      _ ≤ 100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
          ((2 ^ (Nat.ceil c + 2) : ℕ) : ℝ) := by gcongr
  constructor
  · dsimp [p, arithmeticParameters]
    positivity
  · dsimp [p, arithmeticParameters]
    have hdenpos : 0 < 100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
        ((2 ^ (Nat.ceil c + 2) : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hdenpos]
    nlinarith [hden]

/-- The exact arithmetic parameters place `theta` strictly between the
short-interval exponents required by `ar:partition`. -/
theorem arithmeticParameters_partition_exponent_bounds {c : ℝ}
    (hc : 1 < c) :
    let p := arithmeticParameters c
    5 / 8 + p.ε < p.θ ∧ p.θ < 1 - p.ε := by
  dsimp only
  let p := arithmeticParameters c
  have hη := arithmeticParameters_eta_pos_lt_one hc
  dsimp only at hη
  have hθeq : p.θ = 1 - p.η / 16 := by
    dsimp [p, arithmeticParameters]
    ring
  have hεeq : p.ε = p.η / 64 := by
    change (1 - p.θ) / 4 = p.η / 64
    rw [hθeq]
    ring
  rw [hθeq, hεeq]
  constructor <;> nlinarith [hη.1, hη.2]

/-- A strict exponent gap eventually absorbs the fixed dyadic factor in the
lower block-length comparison. -/
theorem exists_real_rpow_dyadic_scale {α θ : ℝ} (hgap : α < θ) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      (2 * K) ^ α ≤ K ^ θ / 2 := by
  let s := θ - α
  let C := 2 * (2 : ℝ) ^ α
  have hs : 0 < s := by dsimp [s]; linarith
  obtain ⟨K₀, hK₀, hlarge⟩ := exists_real_rpow_threshold (C := C) hs
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) (le_trans hK₀ hK)
  have hlargeK : 2 * (2 : ℝ) ^ α ≤ K ^ (θ - α) := by
    simpa [C, s] using hlarge K hK
  have hhalf : (2 : ℝ) ^ α ≤ K ^ (θ - α) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [hlargeK]
  calc
    (2 * K) ^ α = (2 : ℝ) ^ α * K ^ α :=
      Real.mul_rpow (by norm_num) (le_of_lt hKpos)
    _ ≤ (K ^ (θ - α) / 2) * K ^ α :=
      mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg (le_of_lt hKpos) α)
    _ = K ^ θ / 2 := by
      rw [show (K ^ (θ - α) / 2) * K ^ α =
        (K ^ (θ - α) * K ^ α) / 2 by ring]
      rw [← Real.rpow_add hKpos (θ - α) α]
      rw [show θ - α + α = θ by ring]

/-- The real power lower bound transfers to the natural floor once its
argument is at least two. -/
theorem exists_natFloor_rpow_dyadic_scale {α θ : ℝ}
    (hθ : 0 < θ) (hgap : α < θ) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
      (2 * (K : ℝ)) ^ α ≤ (Nat.floor ((K : ℝ) ^ θ) : ℝ) := by
  obtain ⟨Kf, hKf, hlargeFloor⟩ := exists_real_rpow_threshold (C := 2) hθ
  obtain ⟨Kr, hKr, hscale⟩ := exists_real_rpow_dyadic_scale hgap
  let Kfn : ℕ := Nat.ceil Kf
  let Krn : ℕ := Nat.ceil Kr
  let K₀ : ℕ := max Kfn Krn
  have hKfnCast : (1 : ℝ) ≤ (Kfn : ℝ) :=
    le_trans hKf (by exact_mod_cast (Nat.le_ceil Kf))
  have hK₀ : 1 ≤ K₀ := le_trans (by exact_mod_cast hKfnCast)
    (le_max_left _ _)
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK
  have hKfNat : Kfn ≤ K := le_trans (le_max_left _ _) hK
  have hKrNat : Krn ≤ K := le_trans (le_max_right _ _) hK
  have hKfCast : Kf ≤ (K : ℝ) := by
    have hceil : Kf ≤ (Kfn : ℝ) := by exact_mod_cast (Nat.le_ceil Kf)
    exact hceil.trans (by exact_mod_cast hKfNat)
  have hKrCast : Kr ≤ (K : ℝ) := by
    have hceil : Kr ≤ (Krn : ℝ) := by exact_mod_cast (Nat.le_ceil Kr)
    exact hceil.trans (by exact_mod_cast hKrNat)
  have hx : 2 ≤ (K : ℝ) ^ θ := hlargeFloor (K : ℝ) hKfCast
  have hfl := natFloor_cast_ge_half_of_two_le hx
  calc
    (2 * (K : ℝ)) ^ α ≤ (K : ℝ) ^ θ / 2 := hscale (K : ℝ) hKrCast
    _ ≤ (Nat.floor ((K : ℝ) ^ θ) : ℝ) := hfl

/-- Once `theta≤1-epsilon`, the natural floor block is no longer than the
allowed scale at any block start `X≥K≥1`. -/
theorem natFloor_rpow_upper_le_blockStart {c K X : ℝ}
    (hc : 1 < c) (hK : 1 ≤ K) (hX : K ≤ X) :
    let p := arithmeticParameters c
    (Nat.floor (K ^ p.θ) : ℝ) ≤ X ^ (1 - p.ε) := by
  dsimp only
  let p := arithmeticParameters c
  have hparams : 5 / 8 + p.ε < p.θ ∧ p.θ < 1 - p.ε := by
    simpa [p] using arithmeticParameters_partition_exponent_bounds hc
  have hβpos : 0 ≤ 1 - p.ε := by linarith [hparams.2, arithmeticParameters_theta_pos hc]
  have hfloor : (Nat.floor (K ^ p.θ) : ℝ) ≤ K ^ p.θ :=
    Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ K) p.θ)
  calc
    (Nat.floor (K ^ p.θ) : ℝ) ≤ K ^ p.θ := hfloor
    _ ≤ K ^ (1 - p.ε) :=
      Real.rpow_le_rpow_of_exponent_le hK (by linarith [hparams.2])
    _ ≤ X ^ (1 - p.ε) := Real.rpow_le_rpow (by linarith) hX hβpos

/-- The exact floor block satisfies the short-interval size range uniformly
at every full block start `X∈[K,2K]` once `K` is sufficiently large. -/
theorem exists_arithmetic_floor_interval_length_bounds {c : ℝ}
    (hc : 1 < c) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ X : ℝ,
      (K : ℝ) ≤ X → X ≤ 2 * K →
      X ^ (5 / 8 + (arithmeticParameters c).ε) ≤
          (Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ) : ℝ) ∧
        (Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ) : ℝ) ≤
          X ^ (1 - (arithmeticParameters c).ε) := by
  let p := arithmeticParameters c
  have hθ : 0 < p.θ := by
    simpa [p] using arithmeticParameters_theta_pos hc
  have hparams : 5 / 8 + p.ε < p.θ ∧ p.θ < 1 - p.ε := by
    simpa [p] using arithmeticParameters_partition_exponent_bounds hc
  have hηpos : 0 < p.η := by
    simpa [p] using (arithmeticParameters_eta_pos_lt_one hc).1
  have hθeq : p.θ = 1 - p.η / 16 := by
    dsimp [p, arithmeticParameters]
    ring
  have hεeq : p.ε = p.η / 64 := by
    change (1 - p.θ) / 4 = p.η / 64
    rw [hθeq]
    ring
  obtain ⟨K₀, hK₀, hlower⟩ := exists_natFloor_rpow_dyadic_scale hθ
    (α := 5 / 8 + p.ε) (θ := p.θ) hparams.1
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK X hKX hX2
  have hα : 0 ≤ 5 / 8 + p.ε := by rw [hεeq]; positivity
  have hXnonneg : 0 ≤ X := by
    have hKreal : 1 ≤ (K : ℝ) := by exact_mod_cast (hK₀.trans hK)
    linarith
  have hlow : X ^ (5 / 8 + p.ε) ≤
      (Nat.floor ((K : ℝ) ^ p.θ) : ℝ) := by
    calc
      X ^ (5 / 8 + p.ε) ≤ (2 * (K : ℝ)) ^ (5 / 8 + p.ε) :=
        Real.rpow_le_rpow hXnonneg (by linarith) hα
      _ ≤ (Nat.floor ((K : ℝ) ^ p.θ) : ℝ) := hlower K hK
  have hhigh := natFloor_rpow_upper_le_blockStart hc
    (by exact_mod_cast hK₀.trans hK) hKX
  exact ⟨hlow, by simpa [p] using hhigh⟩

/-- The logarithmic divisor cutoff is eventually below the one-tenth power
of the exact floor block, uniformly for every scale `X` between `K` and `2K`.
This is the sieve-level comparison in `ar:partition`. -/
theorem exists_real_floor_log_sieve_bound {θ : ℝ} (hθ : 0 < θ) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K X : ℝ, K₀ ≤ K → K ≤ X → X ≤ 2 * K →
      Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) ≤
        (Nat.floor (K ^ θ) : ℝ) ^ (1 / 10 : ℝ) := by
  let ε : ℝ := θ / (40 * (2 : ℝ) ^ (3 / 10 : ℝ))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨L₀, hL₀, hlargeL⟩ :=
    exists_real_rpow_threshold (C := ε⁻¹) (s := (7 / 10 : ℝ)) (by norm_num)
  obtain ⟨Kf, hKf, hlargeFloor⟩ :=
    exists_real_rpow_threshold (C := 2) hθ
  let Lreq := max L₀ (4 * Real.log 2 / (3 * θ))
  let Klog := Real.exp Lreq
  let K₀ := max (max 2 Kf) Klog
  have hLreq : 0 ≤ Lreq := by
    dsimp [Lreq]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hKlog : 1 ≤ Klog := by
    dsimp [Klog]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hLreq
  have hK₀ : 1 ≤ K₀ := by
    dsimp [K₀]
    exact le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨K₀, hK₀, ?_⟩
  intro K X hK₀K hKX hX2
  have hK₀K' : max (max 2 Kf) Klog ≤ K := by
    simpa [K₀] using hK₀K
  have hKfK : Kf ≤ K :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hK₀K')
  have hKlogK : Klog ≤ K := le_trans (le_max_right _ _) hK₀K'
  have hKpos : 0 < K := by
    have : 1 ≤ K := le_trans (by norm_num : (1 : ℝ) ≤ 2)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hK₀K'))
    linarith
  have hKge2 : 2 ≤ K := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hK₀K')
  have hLreqK : Lreq ≤ Real.log K := by
    dsimp [Klog] at hKlogK
    rw [← Real.log_exp Lreq]
    exact Real.log_le_log (Real.exp_pos Lreq) hKlogK
  have hL₀K : L₀ ≤ Real.log K := le_trans (le_max_left _ _) hLreqK
  have hLreq₂K : 4 * Real.log 2 / (3 * θ) ≤ Real.log K :=
    le_trans (le_max_right _ _) hLreqK
  have hLpos : 0 < Real.log K := by
    exact Real.log_pos (by linarith : 1 < K)
  have hpowL : ε⁻¹ ≤ (Real.log K) ^ (7 / 10 : ℝ) :=
    hlargeL (Real.log K) hL₀K
  have hconst : 40 * (2 : ℝ) ^ (3 / 10 : ℝ) / θ ≤
      (Real.log K) ^ (7 / 10 : ℝ) := by
    simpa [ε, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpowL
  have hlogXnonneg : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hXpos : 0 < X := by linarith
  have hlogXle : Real.log X ≤ 2 * Real.log K := by
    calc
      Real.log X ≤ Real.log (2 * K) :=
        Real.log_le_log hXpos (by nlinarith [hKpos, hX2])
      _ = Real.log 2 + Real.log K := by rw [Real.log_mul (by norm_num) (ne_of_gt hKpos)]
      _ ≤ 2 * Real.log K := by
        have hlog2 : Real.log 2 ≤ Real.log K :=
          Real.log_le_log (by norm_num) hKge2
        linarith
  have hlogXpow : (Real.log X) ^ (3 / 10 : ℝ) ≤
      (2 * Real.log K) ^ (3 / 10 : ℝ) :=
    Real.rpow_le_rpow hlogXnonneg hlogXle (by norm_num)
  have hlogKpow_nonneg : 0 ≤ (Real.log K) ^ (3 / 10 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hLpos) _
  have hsmall : (2 : ℝ) ^ (3 / 10 : ℝ) *
        (Real.log K) ^ (3 / 10 : ℝ) ≤ θ / 40 * Real.log K := by
    have hmult := mul_le_mul_of_nonneg_right hconst hlogKpow_nonneg
    have hmul : (Real.log K) ^ (7 / 10 : ℝ) *
        (Real.log K) ^ (3 / 10 : ℝ) = Real.log K := by
      rw [← Real.rpow_add hLpos]
      norm_num
    calc
      (2 : ℝ) ^ (3 / 10 : ℝ) * (Real.log K) ^ (3 / 10 : ℝ) ≤
          (θ / 40) * ((Real.log K) ^ (7 / 10 : ℝ) *
            (Real.log K) ^ (3 / 10 : ℝ)) := by
              have hconst' : (2 : ℝ) ^ (3 / 10 : ℝ) ≤
                  (θ / 40) * (Real.log K) ^ (7 / 10 : ℝ) := by
                have h' : 40 * (2 : ℝ) ^ (3 / 10 : ℝ) ≤
                    θ * (Real.log K) ^ (7 / 10 : ℝ) :=
                  by simpa [mul_comm] using (div_le_iff₀ hθ).mp hconst
                calc
                  (2 : ℝ) ^ (3 / 10 : ℝ) ≤
                      (θ * (Real.log K) ^ (7 / 10 : ℝ)) / 40 :=
                    (le_div_iff₀ (by norm_num : (0 : ℝ) < 40)).2 (by nlinarith [h'])
                  _ = θ / 40 * (Real.log K) ^ (7 / 10 : ℝ) := by ring
              simpa [mul_assoc] using
                (mul_le_mul_of_nonneg_right hconst' hlogKpow_nonneg)
      _ = θ / 40 * Real.log K := by rw [hmul]
  have hmulrpow : (2 * Real.log K) ^ (3 / 10 : ℝ) =
      (2 : ℝ) ^ (3 / 10 : ℝ) * (Real.log K) ^ (3 / 10 : ℝ) :=
    Real.mul_rpow (by norm_num) (le_of_lt hLpos)
  have hA : (Real.log X) ^ (3 / 10 : ℝ) ≤ θ / 40 * Real.log K := by
    calc
      (Real.log X) ^ (3 / 10 : ℝ) ≤ (2 * Real.log K) ^ (3 / 10 : ℝ) := hlogXpow
      _ = (2 : ℝ) ^ (3 / 10 : ℝ) * (Real.log K) ^ (3 / 10 : ℝ) := hmulrpow
      _ ≤ θ / 40 * Real.log K := hsmall
  have hreserve : θ / 40 * Real.log K ≤
      θ / 10 * Real.log K - Real.log 2 / 10 := by
    have hθpos : 0 < 3 * θ := by positivity
    have h : 4 * Real.log 2 ≤ 3 * θ * Real.log K :=
      by simpa [mul_comm] using (div_le_iff₀ hθpos).mp hLreq₂K
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hKθge2 : 2 ≤ K ^ θ := hlargeFloor K hKfK
  have hfloor : K ^ θ / 2 ≤ (Nat.floor (K ^ θ) : ℝ) :=
    natFloor_cast_ge_half_of_two_le hKθge2
  have hfloorPos : 0 < (Nat.floor (K ^ θ) : ℝ) := by linarith
  have hlogFloor : θ * Real.log K - Real.log 2 ≤
      Real.log (Nat.floor (K ^ θ) : ℝ) := by
    have hmono := Real.log_le_log (by positivity) hfloor
    have hidentity : Real.log (K ^ θ / 2) = θ * Real.log K - Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hKpos]
    rw [← hidentity]
    exact hmono
  have hlogFinal : (Real.log X) ^ (3 / 10 : ℝ) ≤
      Real.log (Nat.floor (K ^ θ) : ℝ) / 10 := by
    calc
      (Real.log X) ^ (3 / 10 : ℝ) ≤ θ / 40 * Real.log K := hA
      _ ≤ θ / 10 * Real.log K - Real.log 2 / 10 := hreserve
      _ = (θ * Real.log K - Real.log 2) / 10 := by ring
      _ ≤ Real.log (Nat.floor (K ^ θ) : ℝ) / 10 := by linarith
  calc
    Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) ≤
        Real.exp (Real.log (Nat.floor (K ^ θ) : ℝ) / 10) :=
      Real.exp_le_exp.mpr hlogFinal
    _ = (Nat.floor (K ^ θ) : ℝ) ^ (1 / 10 : ℝ) := by
      rw [Real.rpow_def_of_pos hfloorPos]
      congr 1
      ring

/-- The logarithmic cutoff estimate specialized to the blueprint's exact
arithmetic parameter package and natural dyadic scale. -/
theorem exists_arithmetic_floor_log_sieve_bound {c : ℝ} (hc : 1 < c) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ X : ℝ,
      (K : ℝ) ≤ X → X ≤ 2 * K →
      Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) ≤
        (Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ) : ℝ) ^
          (1 / 10 : ℝ) := by
  obtain ⟨R₀, hR₀, hbound⟩ :=
    exists_real_floor_log_sieve_bound (arithmeticParameters_theta_pos hc)
  let K₀ : ℕ := Nat.ceil R₀
  have hK₀ : 1 ≤ K₀ := by
    have hcast : (1 : ℝ) ≤ (K₀ : ℝ) :=
      le_trans hR₀ (by exact_mod_cast (Nat.le_ceil R₀))
    exact_mod_cast hcast
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK X hKX hX2
  have hR₀K : R₀ ≤ (K : ℝ) := by
    have hceil : R₀ ≤ (K₀ : ℝ) := by exact_mod_cast (Nat.le_ceil R₀)
    exact hceil.trans (by exact_mod_cast hK)
  exact hbound (K : ℝ) X hR₀K hKX hX2

/-- The strict degree margin absorbs a block length `H≤K^theta` together
with the `K^eta` coefficient range into a `K^-2` Taylor-scale saving. -/
theorem arithmeticParameters_taylor_scale_absorption {c K H : ℝ}
    {k : ℕ} {θ η : ℝ} (hK : 1 ≤ K) (hH : 0 ≤ H)
    (hHupper : H ≤ K ^ θ) (hmargin : (1 - θ) * ((k : ℝ) + 1) > c + η + 2) :
    K ^ η * K ^ (c - ((k : ℝ) + 1)) * H ^ ((k : ℝ) + 1) ≤ K ^ (-2 : ℝ) := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let n : ℝ := (k : ℝ) + 1
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hHpow : H ^ n ≤ (K ^ θ) ^ n := Real.rpow_le_rpow hH hHupper hn
  have hExp : η + (c - n) + θ * n ≤ -2 := by
    dsimp [n] at hmargin ⊢
    nlinarith
  calc
    K ^ η * K ^ (c - n) * H ^ n ≤
        K ^ η * K ^ (c - n) * (K ^ θ) ^ n := by
          gcongr
    _ = K ^ (η + (c - n) + θ * n) := by
          rw [← Real.rpow_mul (le_of_lt hKpos) θ n,
            ← Real.rpow_add hKpos, ← Real.rpow_add hKpos]
    _ ≤ K ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK hExp

/-- A natural interval of length `q*h+r` splits into `q` consecutive full
blocks of length `h` and the final remainder interval. This is the exact
Euclidean partition identity underlying `ar:partition`. -/
theorem sum_natIco_fixedBlock_partition
    {α : Type*} [AddCommMonoid α] (a h q r : ℕ) (f : ℕ → α) :
    (∑ n ∈ Finset.Ico a (a + q * h + r), f n) =
      (∑ v ∈ Finset.range q,
        ∑ n ∈ Finset.Ico (a + v * h) (a + (v + 1) * h), f n) +
      ∑ n ∈ Finset.Ico (a + q * h) (a + q * h + r), f n := by
  have hfull : ∀ q : ℕ,
      (∑ n ∈ Finset.Ico a (a + q * h), f n) =
        ∑ v ∈ Finset.range q,
          ∑ n ∈ Finset.Ico (a + v * h) (a + (v + 1) * h), f n := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have htop : a + (q + 1) * h = a + q * h + h := by
          rw [Nat.succ_mul]
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        have hleft : a ≤ a + q * h := Nat.le_add_right _ _
        have hright : a + q * h ≤ a + (q + 1) * h := by
          rw [htop]
          exact Nat.le_add_right _ _
        rw [Finset.sum_range_succ]
        rw [← ih]
        calc
          (∑ n ∈ Finset.Ico a (a + (q + 1) * h), f n) =
              (∑ n ∈ Finset.Ico a (a + q * h), f n) +
                ∑ n ∈ Finset.Ico (a + q * h) (a + (q + 1) * h), f n :=
            (Finset.sum_Ico_consecutive f hleft hright).symm
          _ = (∑ n ∈ Finset.Ico a (a + q * h), f n) +
                ∑ n ∈ Finset.Ico (a + q * h) (a + (q + 1) * h), f n := rfl
  have hleft : a ≤ a + q * h := Nat.le_add_right _ _
  have hright : a + q * h ≤ a + q * h + r := Nat.le_add_right _ _
  calc
    (∑ n ∈ Finset.Ico a (a + q * h + r), f n) =
        (∑ n ∈ Finset.Ico a (a + q * h), f n) +
          ∑ n ∈ Finset.Ico (a + q * h) (a + q * h + r), f n :=
      (Finset.sum_Ico_consecutive f hleft hright).symm
    _ = (∑ v ∈ Finset.range q,
          ∑ n ∈ Finset.Ico (a + v * h) (a + (v + 1) * h), f n) +
        ∑ n ∈ Finset.Ico (a + q * h) (a + q * h + r), f n := by rw [hfull q]

/-- Euclidean division supplies the exact block count and a remainder shorter
than one full block. -/
theorem natInterval_division_remainder {a b h : ℕ} (hab : a ≤ b) (hh : 0 < h) :
    let q : ℕ := (b - a) / h
    let r : ℕ := (b - a) % h
    b = a + q * h + r ∧ r < h := by
  dsimp only
  constructor
  · have hdiv := Nat.mod_add_div (b - a) h
    have hdiv' : (b - a) % h + ((b - a) / h) * h = b - a := by
      simpa [Nat.mul_comm] using hdiv
    omega
  · exact Nat.mod_lt _ hh

/-- Two fixed natural blocks with distinct ordered indices are disjoint. -/
theorem natIco_fixedBlock_disjoint_of_lt {a h i j : ℕ}
    (hh : 0 < h) (hij : i < j) :
    Disjoint (Finset.Ico (a + i * h) (a + (i + 1) * h))
      (Finset.Ico (a + j * h) (a + (j + 1) * h)) := by
  have hindex : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
  have hmul := Nat.mul_le_mul_right h hindex
  have hend : a + (i + 1) * h ≤ a + j * h := by omega
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  have hni' := Finset.mem_Ico.mp hni
  have hnj' := Finset.mem_Ico.mp hnj
  omega

/-- The full natural blocks form a pairwise-disjoint family. -/
theorem natIco_fixedBlock_pairwise_disjoint {a h q : ℕ} (hh : 0 < h) :
    ∀ i ∈ Finset.range q, ∀ j ∈ Finset.range q, i ≠ j →
      Disjoint (Finset.Ico (a + i * h) (a + (i + 1) * h))
        (Finset.Ico (a + j * h) (a + (j + 1) * h)) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij' | hji
  · exact natIco_fixedBlock_disjoint_of_lt hh hij'
  · exact (natIco_fixedBlock_disjoint_of_lt hh hji).symm

/-- The final natural remainder interval has exactly `r` integers, so a
Euclidean remainder shorter than `h` leaves fewer than `h` integers. -/
theorem natIco_remainder_card_lt {a h q r : ℕ} (hr : r < h) :
    (Finset.Ico (a + q * h) (a + q * h + r)).card < h := by
  simpa using hr

/-- Mathlib's floor-division identity identifies the real quotient of
natural interval lengths with the Euclidean natural quotient. -/
theorem natFloor_div_natCast_eq_div (m n : ℕ) :
    ⌊(m : ℝ) / (n : ℝ)⌋₊ = m / n := by
  exact Nat.floor_div_eq_div m n

/-- The real-floor block count in `ar:partition` is the Euclidean quotient;
with positive block size it yields the exact natural remainder split. -/
theorem natFloor_intervalQuotient_decomposition {a b h : ℕ}
    (hab : a ≤ b) (hh : 0 < h) :
    let q : ℕ := ⌊((b - a : ℕ) : ℝ) / (h : ℝ)⌋₊
    let r : ℕ := (b - a) % h
    b = a + q * h + r ∧ r < h := by
  dsimp only
  have hq : ⌊((b - a : ℕ) : ℝ) / (h : ℝ)⌋₊ = (b - a) / h :=
    natFloor_div_natCast_eq_div _ _
  simpa [hq] using natInterval_division_remainder hab hh

/-- A positive real power eventually has a positive natural floor, with the
`x/2 ≤ floor x ≤ x` bounds needed for the partition block length. -/
theorem exists_natFloor_rpow_block_threshold {θ : ℝ} (hθ : 0 < θ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      0 < Nat.floor ((K : ℝ) ^ θ) ∧
      (K : ℝ) ^ θ / 2 ≤ (Nat.floor ((K : ℝ) ^ θ) : ℝ) ∧
      (Nat.floor ((K : ℝ) ^ θ) : ℝ) ≤ (K : ℝ) ^ θ := by
  obtain ⟨N₀, hN₀, hlarge⟩ := exists_real_rpow_threshold (C := 2) hθ
  let K₀ : ℕ := Nat.ceil N₀
  refine ⟨K₀, ?_⟩
  intro K hK
  have hK0 : N₀ ≤ (K : ℝ) := by
    have hceil : (N₀ : ℝ) ≤ (K₀ : ℝ) := by
      exact_mod_cast (Nat.le_ceil N₀)
    exact hceil.trans (by exact_mod_cast hK)
  have hx : 2 ≤ (K : ℝ) ^ θ := hlarge (K : ℝ) hK0
  have hfloorHalf :
      (K : ℝ) ^ θ / 2 ≤ (Nat.floor ((K : ℝ) ^ θ) : ℝ) :=
    natFloor_cast_ge_half_of_two_le hx
  have hfloorPos : 0 < Nat.floor ((K : ℝ) ^ θ) := by
    have hcast : (1 : ℝ) ≤ (Nat.floor ((K : ℝ) ^ θ) : ℝ) := by
      have hxhalf : (1 : ℝ) ≤ (K : ℝ) ^ θ / 2 := by linarith
      exact hxhalf.trans hfloorHalf
    exact_mod_cast hcast
  have hfloorUpper : (Nat.floor ((K : ℝ) ^ θ) : ℝ) ≤ (K : ℝ) ^ θ :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg K) θ)
  exact ⟨hfloorPos, hfloorHalf, hfloorUpper⟩

/-- For all sufficiently large natural `K`, Euclidean division by the
blueprint's floor block length `floor(K^theta)` gives the exact remainder
decomposition and a remainder shorter than one block. -/
theorem exists_natFloor_rpow_partition_decomposition {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ K' : ℕ, K ≤ K' →
      let H : ℕ := Nat.floor ((K : ℝ) ^ θ)
      let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
      let r : ℕ := (K' - K) % H
      K' = K + q * H + r ∧ r < H := by
  obtain ⟨K₀, hfloor⟩ := exists_natFloor_rpow_block_threshold hθ
  refine ⟨K₀, ?_⟩
  intro K hK K' hKK'
  have hH : 0 < Nat.floor ((K : ℝ) ^ θ) := (hfloor K hK).1
  simpa using natFloor_intervalQuotient_decomposition hKK' hH

/-- The floor-power Euclidean decomposition expressed as the exact finite
sum partition for the paper's half-open integer interval `(K,K']`. -/
theorem exists_sum_natIco_rpow_partition {θ : ℝ} (hθ : 0 < θ)
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ K' : ℕ, K ≤ K' →
      let H : ℕ := Nat.floor ((K : ℝ) ^ θ)
      let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
      let r : ℕ := (K' - K) % H
      (∑ n ∈ Finset.Ico (K + 1) (K' + 1), f n) =
        (∑ v ∈ Finset.range q,
          ∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H), f n) +
        ∑ n ∈ Finset.Ico (K + 1 + q * H) (K + 1 + q * H + r), f n := by
  obtain ⟨K₀, hdecomp⟩ := exists_natFloor_rpow_partition_decomposition hθ
  refine ⟨K₀, ?_⟩
  intro K hK K' hKK'
  dsimp only
  have hsplit := hdecomp K hK K' hKK'
  dsimp only at hsplit
  rcases hsplit with ⟨hupper, hr⟩
  have hshift : K' + 1 = K + 1 +
      ⌊((K' - K : ℕ) : ℝ) / ((Nat.floor ((K : ℝ) ^ θ) : ℝ))⌋₊ *
        Nat.floor ((K : ℝ) ^ θ) + (K' - K) % Nat.floor ((K : ℝ) ^ θ) := by
    omega
  rw [hshift]
  exact sum_natIco_fixedBlock_partition (K + 1)
    (Nat.floor ((K : ℝ) ^ θ))
    (⌊((K' - K : ℕ) : ℝ) / ((Nat.floor ((K : ℝ) ^ θ) : ℝ))⌋₊)
    ((K' - K) % Nat.floor ((K : ℝ) ^ θ)) f

/-- The exact floor-defined Euclidean block count is at most
`2 K^(1-theta)` once the floor block has reached half its real-power scale.
This is the count estimate in `ar:partition`. -/
theorem natFloor_intervalQuotient_le_two_rpow {θ : ℝ} {K K' : ℕ}
    (hθ : 0 < θ) (hK : 1 ≤ K)
    (hKpow : 2 ≤ (K : ℝ) ^ θ) (hKK' : K ≤ K') (hK' : K' ≤ 2 * K) :
    (⌊((K' - K : ℕ) : ℝ) /
        ((Nat.floor ((K : ℝ) ^ θ) : ℕ) : ℝ)⌋₊ : ℝ) ≤
      2 * (K : ℝ) ^ (1 - θ) := by
  let H : ℕ := Nat.floor ((K : ℝ) ^ θ)
  let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKθpos : 0 < (K : ℝ) ^ θ := Real.rpow_pos_of_pos hKpos θ
  have hHlower : (K : ℝ) ^ θ / 2 ≤ (H : ℝ) :=
    natFloor_cast_ge_half_of_two_le hKpow
  have hHpos : 0 < H := by
    have hHcast : (1 : ℝ) ≤ (H : ℝ) := by linarith
    exact_mod_cast hHcast
  have hqeq : q = (K' - K) / H := by
    dsimp [q, H]
    exact natFloor_div_natCast_eq_div _ _
  have hqHnat : q * H ≤ K' - K := by
    rw [hqeq]
    exact Nat.div_mul_le_self _ _
  have hdiff : K' - K ≤ K := by omega
  have hqH : (q : ℝ) * (H : ℝ) ≤ (K : ℝ) := by
    have hcast : (q : ℝ) * (H : ℝ) ≤ ((K' - K : ℕ) : ℝ) := by
      exact_mod_cast hqHnat
    exact hcast.trans (by exact_mod_cast hdiff)
  have hqnonneg : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hqscaled : (q : ℝ) * (K : ℝ) ^ θ ≤ 2 * (K : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hHlower hqnonneg
    nlinarith [hqH]
  have hpow : (K : ℝ) ^ θ * (K : ℝ) ^ (1 - θ) = (K : ℝ) := by
    rw [← Real.rpow_add hKpos]
    rw [show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  have hqbound : (q : ℝ) ≤ (2 * (K : ℝ)) / (K : ℝ) ^ θ :=
    (le_div_iff₀ hKθpos).2 hqscaled
  have hquot : (2 * (K : ℝ)) / (K : ℝ) ^ θ =
      2 * (K : ℝ) ^ (1 - θ) := by
    apply (div_eq_iff hKθpos.ne').2
    calc
      2 * (K : ℝ) = 2 * ((K : ℝ) ^ θ * (K : ℝ) ^ (1 - θ)) := by rw [hpow]
      _ = (2 * (K : ℝ) ^ (1 - θ)) * (K : ℝ) ^ θ := by ring
  simpa [q, H] using hqbound.trans_eq hquot

/-- Taylor evaluations over two sets agree when all derivatives through the
Taylor order agree at the same center. This isolates the center-independence
step needed to use Mathlib's interval-dependent remainder theorem. -/
theorem taylorWithinEval_eq_of_iteratedDerivWithin_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (n : ℕ) (s t : Set ℝ) (x₀ x : ℝ)
    (hderiv : ∀ i ∈ Finset.range (n + 1),
      iteratedDerivWithin i f s x₀ = iteratedDerivWithin i f t x₀) :
    taylorWithinEval f n s x₀ x = taylorWithinEval f n t x₀ x := by
  simp only [taylorWithinEval, taylorWithin, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [taylorCoeffWithin, hderiv i hi]

/-- For a positive center in a fixed positive interval, the Taylor polynomial
on the varying segment from the center to `t` agrees with the one on the fixed
ambient interval. This gives the single midpoint polynomial required for a
uniform block estimate. -/
theorem taylorWithinEval_rpow_segment_eq_fixed {c K z t : ℝ} {n : ℕ}
    (hK : 0 < K) (hKz : K ≤ z) (hz2 : z ≤ 2 * K)
    (hzt : z ≠ t) :
    taylorWithinEval (fun x : ℝ => x ^ c) n (Set.uIcc z t) z t =
      taylorWithinEval (fun x : ℝ => x ^ c) n (Set.Icc K (2 * K)) z t := by
  apply taylorWithinEval_eq_of_iteratedDerivWithin_eq
  intro i hi
  have hposz : 0 < z := lt_of_lt_of_le hK hKz
  have hcont : ContDiffAt ℝ i (fun x : ℝ => x ^ c) z :=
    Real.contDiffAt_rpow_const (Or.inl (ne_of_gt hposz))
  have hu : UniqueDiffOn ℝ (Set.uIcc z t) := uniqueDiffOn_uIcc hzt
  have hKlt : K < 2 * K := by nlinarith
  have hf : UniqueDiffOn ℝ (Set.Icc K (2 * K)) := uniqueDiffOn_Icc hKlt
  calc
    iteratedDerivWithin i (fun x : ℝ => x ^ c) (Set.uIcc z t) z =
        iteratedDeriv i (fun x : ℝ => x ^ c) z := by
          apply iteratedDerivWithin_eq_iteratedDeriv hu hcont
          simp [Set.uIcc]
    _ = iteratedDerivWithin i (fun x : ℝ => x ^ c) (Set.Icc K (2 * K)) z := by
          symm
          exact iteratedDerivWithin_eq_iteratedDeriv hf hcont ⟨hKz, hz2⟩

/-- Lagrange's Taylor remainder on a positive dyadic interval, expressed
using one fixed ambient Taylor polynomial at `z`. -/
theorem taylorWithinEval_rpow_fixed_remainder_le {c K z t M : ℝ} {n : ℕ}
    (hK : 0 < K) (hz : z ∈ Set.Icc K (2 * K))
    (ht : t ∈ Set.Icc K (2 * K)) (hzt : z ≠ t)
    (hbound : ∀ y ∈ Set.Icc K (2 * K),
      |iteratedDeriv (n + 1) (fun x : ℝ => x ^ c) y| ≤ M) :
    |t ^ c - taylorWithinEval (fun x : ℝ => x ^ c) n
      (Set.Icc K (2 * K)) z t| ≤
        M * |t - z| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  have hKlt : K < 2 * K := by nlinarith
  have hsmooth : ContDiffOn ℝ (n + 1) (fun x : ℝ => x ^ c)
      (Set.Icc K (2 * K)) :=
    contDiffOn_fun_id.rpow_const_of_ne fun y hy =>
      ne_of_gt (lt_of_lt_of_le hK hy.1)
  have hseg : Set.uIcc z t ⊆ Set.Icc K (2 * K) :=
    Set.uIcc_subset_Icc hz ht
  have hsmoothSeg : ContDiffOn ℝ (n + 1) (fun x : ℝ => x ^ c)
      (Set.uIcc z t) := hsmooth.mono hseg
  obtain ⟨y, hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv hzt hsmoothSeg
  have hyIcc : y ∈ Set.Icc K (2 * K) :=
    hseg (Set.uIoo_subset_uIcc_self hy)
  rw [taylorWithinEval_rpow_segment_eq_fixed hK hz.1 hz.2 hzt] at hrem
  rw [hrem]
  have hden : 0 < (Nat.factorial (n + 1) : ℝ) := by positivity
  have hfactorialNonneg : 0 ≤ (Nat.factorial (n + 1) : ℝ) := le_of_lt hden
  simp only [abs_div, abs_mul, abs_pow, abs_of_nonneg hfactorialNonneg]
  apply div_le_div_of_nonneg_right _ hden.le
  exact mul_le_mul_of_nonneg_right (hbound y hyIcc)
    (pow_nonneg (abs_nonneg (t - z)) (n + 1))

/-- The blueprint's derivative order lies above `c`, and the existing dyadic
real-power derivative estimate then gives the uniform `K^(c-j)` bound. -/
theorem arithmeticParameters_taylor_derivative_bound {c K y : ℝ}
    (hc : 1 < c) (hK : 0 < K) (hKy : K ≤ y) (hy2 : y ≤ 2 * K) :
    let p := arithmeticParameters c
    |iteratedDeriv (p.k + 1) (fun x : ℝ => x ^ c) y| ≤
      |(descPochhammer ℝ (p.k + 1)).eval c| * K ^ (c - ((p.k + 1 : ℕ) : ℝ)) := by
  dsimp only
  let p := arithmeticParameters c
  have hmargin : (1 - p.θ) * ((p.k : ℝ) + 1) > c + p.η + 2 := by
    simpa [p] using arithmeticParameters_taylor_degree_margin hc
  have hηpos : 0 < p.η := by
    dsimp [p, arithmeticParameters]
    positivity
  have hnpos : 0 < ((p.k : ℝ) + 1) := by positivity
  have hfactorpos : 0 < 1 - p.θ := by
    by_contra h
    have hnonpos : 1 - p.θ ≤ 0 := le_of_not_gt h
    have hprod : (1 - p.θ) * ((p.k : ℝ) + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt hnpos)
    nlinarith [hmargin]
  have hfactor_lt_one : 1 - p.θ < 1 := by
    have hθ : 0 < p.θ := by simpa [p] using arithmeticParameters_theta_pos hc
    linarith
  have hprod_le : (1 - p.θ) * ((p.k : ℝ) + 1) ≤ (p.k : ℝ) + 1 :=
    calc
      (1 - p.θ) * ((p.k : ℝ) + 1) ≤ 1 * ((p.k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith : 1 - p.θ ≤ 1) (le_of_lt hnpos)
      _ = (p.k : ℝ) + 1 := by ring
  have hcjReal : c < (p.k : ℝ) + 1 := by nlinarith [hmargin, hprod_le, hηpos]
  have hcj : c < ((p.k + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hcjReal
  have hbound := (abs_iteratedDeriv_scaled_real_rpow_bounds
    (1 : ℝ) c K y (p.k + 1) hK hKy hy2 hcj).2
  simpa [abs_one, one_mul] using hbound

/-- Points in a block lie within half the block length of its midpoint. -/
theorem abs_sub_midpoint_le_half_length {X H t : ℝ}
    (hX : X ≤ t) (ht : t ≤ X + H) :
    |t - (X + H / 2)| ≤ H / 2 := by
  rw [abs_le]
  constructor <;> linarith

/-- The frequency coefficient range `natAbs m≤floor(K^eta)` and
`|xi|≤1/2` imply the blueprint's `2*K^eta` coefficient bound. -/
theorem abs_intCast_add_le_two_rpow_floor {m : ℤ} {K η ξ : ℝ}
    (hK : 1 ≤ K) (hη : 0 ≤ η)
    (hm : Int.natAbs m ≤ Nat.floor (K ^ η)) (hξ : |ξ| ≤ 1 / 2) :
    |(m : ℝ) + ξ| ≤ 2 * K ^ η := by
  have hpow : 0 ≤ K ^ η := Real.rpow_nonneg (by linarith) η
  have hfloor : (Nat.floor (K ^ η) : ℝ) ≤ K ^ η := Nat.floor_le hpow
  have hmR : |(m : ℝ)| ≤ (Nat.floor (K ^ η) : ℝ) := by
    calc
      |(m : ℝ)| = (Int.natAbs m : ℝ) := by simp
      _ ≤ (Nat.floor (K ^ η) : ℝ) := by exact_mod_cast hm
  have hone : 1 ≤ K ^ η := Real.one_le_rpow hK hη
  calc
    |(m : ℝ) + ξ| ≤ |(m : ℝ)| + |ξ| := abs_add_le _ _
    _ ≤ (Nat.floor (K ^ η) : ℝ) + 1 / 2 := add_le_add hmR hξ
    _ ≤ 2 * K ^ η := by nlinarith [hfloor, hone]

/-- Pointwise midpoint Taylor approximation with the paper's exact frequency
and block-length scales. The constant is explicit in the Taylor coefficient
and depends only on the fixed exponent package. -/
theorem arithmeticParameters_taylor_midpoint_error
    {c K X H t ξ : ℝ} {m : ℤ}
    (hc : 1 < c) (hK : 1 ≤ K) (hH : 0 ≤ H)
    (hHupper : H ≤ K ^ (arithmeticParameters c).θ)
    (hX : K ≤ X) (hXH : X + H ≤ 2 * K)
    (ht : X ≤ t) (htH : t ≤ X + H)
    (hm : Int.natAbs m ≤ Nat.floor (K ^ (arithmeticParameters c).η))
    (hξ : |ξ| ≤ 1 / 2) :
    let p := arithmeticParameters c
    let z := X + H / 2
    |((m : ℝ) + ξ) *
        (t ^ c - taylorWithinEval (fun x : ℝ => x ^ c) p.k
          (Set.Icc K (2 * K)) z t)| ≤
      2 * |(descPochhammer ℝ (p.k + 1)).eval c| * K ^ (-2 : ℝ) := by
  dsimp only
  let p := arithmeticParameters c
  let z : ℝ := X + H / 2
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hzK : K ≤ z := by dsimp [z]; linarith
  have hz2K : z ≤ 2 * K := by dsimp [z]; linarith
  have htK : K ≤ t := le_trans hX ht
  have ht2K : t ≤ 2 * K := le_trans htH hXH
  have hzIcc : z ∈ Set.Icc K (2 * K) := ⟨hzK, hz2K⟩
  have htIcc : t ∈ Set.Icc K (2 * K) := ⟨htK, ht2K⟩
  have hηpos : 0 < p.η := by
    dsimp [p, arithmeticParameters]
    positivity
  have hmargin :
      (1 - p.θ) * ((p.k : ℝ) + 1) > c + p.η + 2 := by
    simpa [p] using arithmeticParameters_taylor_degree_margin hc
  have hderiv : ∀ y ∈ Set.Icc K (2 * K),
      |iteratedDeriv (p.k + 1) (fun x : ℝ => x ^ c) y| ≤
        |(descPochhammer ℝ (p.k + 1)).eval c| *
          K ^ (c - ((p.k + 1 : ℕ) : ℝ)) := by
    intro y hy
    exact arithmeticParameters_taylor_derivative_bound hc hKpos hy.1 hy.2
  have hdist : |t - z| ≤ H := by
    have hmid := abs_sub_midpoint_le_half_length ht htH
    dsimp [z]
    linarith
  have hfact : 1 ≤ (Nat.factorial (p.k + 1) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hpow : |t - z| ^ (p.k + 1) ≤ H ^ (p.k + 1) := by
    gcongr
  have hfrac : |t - z| ^ (p.k + 1) /
      (Nat.factorial (p.k + 1) : ℝ) ≤ H ^ (p.k + 1) := by
    calc
      |t - z| ^ (p.k + 1) / (Nat.factorial (p.k + 1) : ℝ) ≤
          |t - z| ^ (p.k + 1) :=
            div_le_self (pow_nonneg (abs_nonneg _) _) hfact
      _ ≤ H ^ (p.k + 1) := hpow
  have hrem :
      |t ^ c - taylorWithinEval (fun x : ℝ => x ^ c) p.k
        (Set.Icc K (2 * K)) z t| ≤
        (|(descPochhammer ℝ (p.k + 1)).eval c| *
          K ^ (c - ((p.k + 1 : ℕ) : ℝ))) *
          |t - z| ^ (p.k + 1) / (Nat.factorial (p.k + 1) : ℝ) := by
    by_cases hzt : z = t
    · subst t
      simp [taylorWithinEval_self]
    · exact taylorWithinEval_rpow_fixed_remainder_le
        hKpos hzIcc htIcc hzt hderiv
  have hremBound :
      |t ^ c - taylorWithinEval (fun x : ℝ => x ^ c) p.k
        (Set.Icc K (2 * K)) z t| ≤
        |(descPochhammer ℝ (p.k + 1)).eval c| *
          K ^ (c - ((p.k + 1 : ℕ) : ℝ)) * H ^ (p.k + 1) := by
    calc
      _ ≤ (|(descPochhammer ℝ (p.k + 1)).eval c| *
          K ^ (c - ((p.k + 1 : ℕ) : ℝ))) *
          |t - z| ^ (p.k + 1) / (Nat.factorial (p.k + 1) : ℝ) := hrem
      _ = (|(descPochhammer ℝ (p.k + 1)).eval c| *
          K ^ (c - ((p.k + 1 : ℕ) : ℝ))) *
          (|t - z| ^ (p.k + 1) /
            (Nat.factorial (p.k + 1) : ℝ)) := by ring
      _ ≤ |(descPochhammer ℝ (p.k + 1)).eval c| *
          K ^ (c - ((p.k + 1 : ℕ) : ℝ)) * H ^ (p.k + 1) := by
            gcongr
  have hcoeff := abs_intCast_add_le_two_rpow_floor hK
    (by simpa [p] using hηpos.le) hm hξ
  have hscale := arithmeticParameters_taylor_scale_absorption
    hK hH hHupper hmargin
  have hscaleNat : K ^ p.η * K ^ (c - ((p.k + 1 : ℕ) : ℝ)) *
      H ^ (p.k + 1) ≤ K ^ (-2 : ℝ) := by
    simpa only [← Real.rpow_natCast, Nat.cast_add, Nat.cast_one] using hscale
  calc
    |((m : ℝ) + ξ) *
        (t ^ c - taylorWithinEval (fun x : ℝ => x ^ c) p.k
          (Set.Icc K (2 * K)) z t)| =
        |(m : ℝ) + ξ| *
          |t ^ c - taylorWithinEval (fun x : ℝ => x ^ c) p.k
            (Set.Icc K (2 * K)) z t| := abs_mul _ _
    _ ≤ (2 * K ^ p.η) *
        (|(descPochhammer ℝ (p.k + 1)).eval c| *
          K ^ (c - ((p.k + 1 : ℕ) : ℝ)) * H ^ (p.k + 1)) := by
          exact mul_le_mul hcoeff hremBound (abs_nonneg _) (by positivity)
    _ = (2 * |(descPochhammer ℝ (p.k + 1)).eval c|) *
        (K ^ p.η * K ^ (c - ((p.k + 1 : ℕ) : ℝ)) * H ^ (p.k + 1)) := by ring
    _ ≤ (2 * |(descPochhammer ℝ (p.k + 1)).eval c|) * K ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_left hscaleNat (by positivity)

/-- The complete scale and midpoint-error package for every full block of the
blueprint's short-interval partition. The exact finite-sum partition and
pairwise-disjointness statements are supplied by
`exists_sum_natIco_rpow_partition` and
`natIco_fixedBlock_pairwise_disjoint`. -/
theorem exists_arithmetic_shortBlock_scale_package {c : ℝ} (hc : 1 < c) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ K' : ℕ,
      K ≤ K' → K' ≤ 2 * K →
      let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
      let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
      let r : ℕ := (K' - K) % H
      r < H ∧
      (q : ℝ) ≤ 2 * (K : ℝ) ^ (1 - (arithmeticParameters c).θ) ∧
      (∀ v : ℕ, v < q →
        let Xv : ℕ := K + v * H
        (Xv : ℝ) ^ (5 / 8 + (arithmeticParameters c).ε) ≤ (H : ℝ) ∧
        (H : ℝ) ≤ (Xv : ℝ) ^ (1 - (arithmeticParameters c).ε) ∧
        Real.exp ((Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ)) ≤
          (H : ℝ) ^ (1 / 10 : ℝ) ∧
        (∀ m : ℤ, Int.natAbs m ≤
            Nat.floor ((K : ℝ) ^ (arithmeticParameters c).η) →
          ∀ ξ : ℝ, |ξ| ≤ 1 / 2 →
          ∀ t : ℝ, (Xv : ℝ) ≤ t → t ≤ (Xv : ℝ) + (H : ℝ) →
            |((m : ℝ) + ξ) *
              (t ^ c - taylorWithinEval (fun x : ℝ => x ^ c)
                (arithmeticParameters c).k (Set.Icc (K : ℝ) (2 * K))
                ((Xv : ℝ) + (H : ℝ) / 2) t)| ≤
              2 * |(descPochhammer ℝ
                ((arithmeticParameters c).k + 1)).eval c| *
                (K : ℝ) ^ (-2 : ℝ))) := by
  have hθ : 0 < (arithmeticParameters c).θ := arithmeticParameters_theta_pos hc
  obtain ⟨Klen, hKlen, hlength⟩ :=
    exists_arithmetic_floor_interval_length_bounds hc
  obtain ⟨Ksieve, hKsieve, hsieve⟩ :=
    exists_arithmetic_floor_log_sieve_bound hc
  obtain ⟨Kpart, hpart⟩ :=
    exists_natFloor_rpow_partition_decomposition hθ
  obtain ⟨Rpow, hRpow, hlargePow⟩ :=
    exists_real_rpow_threshold (C := 2) hθ
  let Kpow : ℕ := Nat.ceil Rpow
  have hKpow : 1 ≤ Kpow := by
    have hcast : (1 : ℝ) ≤ (Kpow : ℝ) :=
      le_trans hRpow (by exact_mod_cast (Nat.le_ceil Rpow))
    exact_mod_cast hcast
  let A : ℕ := max 1 Klen
  let B : ℕ := max A Ksieve
  let C : ℕ := max Kpart Kpow
  let K₀ : ℕ := max B C
  have hK₀ : 1 ≤ K₀ := by
    dsimp [K₀, B, A]
    exact le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK K' hKK' hK'2
  have hKparts : B ≤ K := by
    have hbig : max B C ≤ K := by simpa [K₀] using hK
    exact le_trans (le_max_left _ _) hbig
  have hKrest : C ≤ K := by
    have hbig : max B C ≤ K := by simpa [K₀] using hK
    exact le_trans (le_max_right _ _) hbig
  have hKlenK : Klen ≤ K := by
    have hA : A ≤ K := le_trans (le_max_left _ _) hKparts
    exact le_trans (le_max_right _ _) hA
  have hKsieveK : Ksieve ≤ K := le_trans (le_max_right _ _) hKparts
  have hKpartK : Kpart ≤ K := le_trans (le_max_left _ _) hKrest
  have hKpowK : Kpow ≤ K := le_trans (le_max_right _ _) hKrest
  have hRpowK : Rpow ≤ (K : ℝ) := by
    have hceil : Rpow ≤ (Kpow : ℝ) := by exact_mod_cast (Nat.le_ceil Rpow)
    exact hceil.trans (by exact_mod_cast hKpowK)
  have hKθge2 : 2 ≤ (K : ℝ) ^ (arithmeticParameters c).θ :=
    hlargePow (K : ℝ) hRpowK
  let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
  let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
  let r : ℕ := (K' - K) % H
  have hdecomp := hpart K hKpartK K' hKK'
  dsimp only at hdecomp
  rcases hdecomp with ⟨hdecomp, hr⟩
  have hHpos : 0 < H := by
    have hHlower : (K : ℝ) ^ (arithmeticParameters c).θ / 2 ≤ (H : ℝ) :=
      natFloor_cast_ge_half_of_two_le hKθge2
    have hKpowpos : 0 < (K : ℝ) ^ (arithmeticParameters c).θ :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < K)) _
    have hHcast : (1 : ℝ) ≤ (H : ℝ) := by linarith
    exact_mod_cast hHcast
  have hqeq : q = (K' - K) / H := by
    dsimp [q]
    exact natFloor_div_natCast_eq_div _ _
  have hqH : q * H ≤ K' - K := by
    rw [hqeq]
    exact Nat.div_mul_le_self _ _
  have hqbound := natFloor_intervalQuotient_le_two_rpow
    hθ (by omega) hKθge2 hKK' hK'2
  have hlengthK := hlength K hKlenK
  have hsieveK := hsieve K hKsieveK
  refine ⟨hr, ?_, ?_⟩
  · simpa [q, H] using hqbound
  · intro v hv
    let Xv : ℕ := K + v * H
    have hvstep : (v + 1) * H ≤ q * H :=
      Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hv)
    have hXHNat : K + v * H + H ≤ K' := by
      have hstep : K + v * H + H = K + (v + 1) * H := by
        rw [Nat.succ_mul]
        omega
      calc
        K + v * H + H = K + (v + 1) * H := hstep
        _ ≤ K + q * H := Nat.add_le_add_left hvstep K
        _ ≤ K' := by omega
    have hXlowNat : K ≤ Xv := by dsimp [Xv]; omega
    have hXtopNat : Xv ≤ 2 * K := le_trans (by omega) hK'2
    have hXHreal : (Xv : ℝ) + (H : ℝ) ≤ 2 * (K : ℝ) := by
      have hcast : (Xv + H : ℕ) ≤ K' := by dsimp [Xv]; omega
      have hcast' : (Xv + H : ℕ) ≤ 2 * K := le_trans hcast hK'2
      exact_mod_cast hcast'
    have hXlowReal : (K : ℝ) ≤ (Xv : ℝ) := by exact_mod_cast hXlowNat
    have hXtopReal : (Xv : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hXtopNat
    have hlenX := hlengthK (Xv : ℝ) hXlowReal hXtopReal
    have hsieveX := hsieveK (Xv : ℝ) hXlowReal hXtopReal
    have hfloorUpper : (H : ℝ) ≤ (K : ℝ) ^ (arithmeticParameters c).θ :=
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg K) _)
    have hKreal : 1 ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Xv, H] using hlenX.1
    · simpa [Xv, H] using hlenX.2
    · simpa [Xv, H] using hsieveX
    · intro m hm ξ hξ t ht htH
      have htK : (K : ℝ) ≤ t := hXlowReal.trans ht
      have htEnd : t ≤ 2 * (K : ℝ) := htH.trans hXHreal
      have hTaylor := arithmeticParameters_taylor_midpoint_error
        hc hKreal (by exact_mod_cast (Nat.zero_le H))
        hfloorUpper hXlowReal hXHreal ht htH hm hξ
      simpa [Xv, H] using hTaylor

/-- Paper-facing fixed short-block partition theorem. It combines the exact
half-open sum decomposition, pairwise disjoint full blocks, short remainder,
block count, all scale bounds, the sieve cutoff, and the common midpoint
Taylor approximation under one eventual threshold. -/
theorem exists_arithmetic_shortBlock_partition {c : ℝ} (hc : 1 < c) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ K' : ℕ,
      K ≤ K' → K' ≤ 2 * K →
      let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
      let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
      let r : ℕ := (K' - K) % H
      (∀ {α : Type*} [AddCommMonoid α] (f : ℕ → α),
        (∑ n ∈ Finset.Ico (K + 1) (K' + 1), f n) =
          (∑ v ∈ Finset.range q,
            ∑ n ∈ Finset.Ico (K + 1 + v * H) (K + 1 + (v + 1) * H), f n) +
          ∑ n ∈ Finset.Ico (K + 1 + q * H) (K + 1 + q * H + r), f n) ∧
      (∀ i ∈ Finset.range q, ∀ j ∈ Finset.range q, i ≠ j →
        Disjoint (Finset.Ico (K + 1 + i * H) (K + 1 + (i + 1) * H))
          (Finset.Ico (K + 1 + j * H) (K + 1 + (j + 1) * H))) ∧
      (Finset.Ico (K + 1 + q * H) (K + 1 + q * H + r)).card < H ∧
      r < H ∧
      (q : ℝ) ≤ 2 * (K : ℝ) ^ (1 - (arithmeticParameters c).θ) ∧
      (∀ v : ℕ, v < q →
        let Xv : ℕ := K + v * H
        (Xv : ℝ) ^ (5 / 8 + (arithmeticParameters c).ε) ≤ (H : ℝ) ∧
        (H : ℝ) ≤ (Xv : ℝ) ^ (1 - (arithmeticParameters c).ε) ∧
        Real.exp ((Real.log (Xv : ℝ)) ^ (3 / 10 : ℝ)) ≤
          (H : ℝ) ^ (1 / 10 : ℝ) ∧
        (∀ m : ℤ, Int.natAbs m ≤
            Nat.floor ((K : ℝ) ^ (arithmeticParameters c).η) →
          ∀ ξ : ℝ, |ξ| ≤ 1 / 2 →
          ∀ t : ℝ, (Xv : ℝ) ≤ t → t ≤ (Xv : ℝ) + (H : ℝ) →
            |((m : ℝ) + ξ) *
              (t ^ c - taylorWithinEval (fun x : ℝ => x ^ c)
                (arithmeticParameters c).k (Set.Icc (K : ℝ) (2 * K))
                ((Xv : ℝ) + (H : ℝ) / 2) t)| ≤
              2 * |(descPochhammer ℝ
                ((arithmeticParameters c).k + 1)).eval c| *
                (K : ℝ) ^ (-2 : ℝ))) := by
  have hθ : 0 < (arithmeticParameters c).θ := arithmeticParameters_theta_pos hc
  obtain ⟨Kscale, hKscale, hscale⟩ :=
    exists_arithmetic_shortBlock_scale_package hc
  obtain ⟨Kpart, hpart⟩ :=
    exists_natFloor_rpow_partition_decomposition hθ
  obtain ⟨Kfloor, hfloor⟩ := exists_natFloor_rpow_block_threshold hθ
  let K₀ := max 1 (max Kscale (max Kpart Kfloor))
  have hK₀ : 1 ≤ K₀ := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK K' hKK' hK'2
  have hbig : max Kscale (max Kpart Kfloor) ≤ K := by
    have h' : max 1 (max Kscale (max Kpart Kfloor)) ≤ K := by
      simpa [K₀] using hK
    exact le_trans (le_max_right _ _) h'
  have hKscaleK : Kscale ≤ K := le_trans (le_max_left _ _) hbig
  have hrest : max Kpart Kfloor ≤ K := le_trans (le_max_right _ _) hbig
  have hKpartK : Kpart ≤ K := le_trans (le_max_left _ _) hrest
  have hKfloorK : Kfloor ≤ K := le_trans (le_max_right _ _) hrest
  have hdata := hscale K hKscaleK K' hKK' hK'2
  dsimp only at hdata
  rcases hdata with ⟨hr, hqbound, hblocks⟩
  have hdecomp := hpart K hKpartK K' hKK'
  dsimp only at hdecomp
  rcases hdecomp with ⟨hdecomp, _hrdecomp⟩
  have hHpos : 0 < Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ) :=
    (hfloor K hKfloorK).1
  dsimp only
  refine ⟨?_, ?_, ?_, hr, hqbound, hblocks⟩
  · intro α inst f
    have hshift : K' + 1 = K + 1 +
        ⌊((K' - K : ℕ) : ℝ) /
          ((Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ) : ℝ))⌋₊ *
            Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ) +
          (K' - K) % Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ) := by
      omega
    rw [hshift]
    exact sum_natIco_fixedBlock_partition (K + 1)
      (Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ))
      (⌊((K' - K : ℕ) : ℝ) /
        ((Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ) : ℝ))⌋₊)
      ((K' - K) % Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)) f
  · exact natIco_fixedBlock_pairwise_disjoint
      (a := K + 1)
      (h := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ))
      (q := ⌊((K' - K : ℕ) : ℝ) /
        ((Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ) : ℝ))⌋₊)
      hHpos
  · exact natIco_remainder_card_lt hr



end FractionalPrimes

end
