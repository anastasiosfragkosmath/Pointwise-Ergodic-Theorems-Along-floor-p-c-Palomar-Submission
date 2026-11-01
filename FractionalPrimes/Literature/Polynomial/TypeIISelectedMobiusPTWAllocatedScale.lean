module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWDyadicWindowIdentity
public import Mathlib.Tactic

/-! Exact quotient-scale bookkeeping for one retained triple block in the
selected Möbius PTW argument. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletMean

set_option maxHeartbeats 4000000

/-- A retained source block with scale in `[C₀⁻¹ X^γ, C₀ X^γ]` has the
corresponding logarithmic length within `log C₀` of `γ log X`. -/
theorem selectedMobiusPTW_log_of_scaled_block_support
    {X C₀ N γ ℓ : ℝ}
    (hX : 1 < X) (hℓ : ℓ = Real.log X) (hC₀ : 1 ≤ C₀)
    (hNlower : C₀⁻¹ * X ^ γ ≤ N)
    (hNupper : N ≤ C₀ * X ^ γ) :
    |Real.log N - γ * ℓ| ≤ Real.log C₀ := by
  have hXpos : 0 < X := by linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) hC₀
  have hpowpos : 0 < X ^ γ := Real.rpow_pos_of_pos hXpos γ
  have hNpos : 0 < N := by
    have hlow : 0 < C₀⁻¹ * X ^ γ := mul_pos (inv_pos.mpr hC₀pos) hpowpos
    exact lt_of_lt_of_le hlow hNlower
  have hlowpos : 0 < C₀⁻¹ * X ^ γ :=
    mul_pos (inv_pos.mpr hC₀pos) hpowpos
  have hlowlog : Real.log (C₀⁻¹ * X ^ γ) ≤ Real.log N :=
    Real.log_le_log hlowpos hNlower
  have hlowEq : C₀⁻¹ * X ^ γ = X ^ γ / C₀ := by
    field_simp [ne_of_gt hC₀pos]
  rw [hlowEq, Real.log_div hpowpos.ne' hC₀pos.ne',
    Real.log_rpow hXpos, ← hℓ] at hlowlog
  have hhighlog : Real.log N ≤ Real.log (C₀ * X ^ γ) :=
    Real.log_le_log hNpos hNupper
  rw [Real.log_mul hC₀pos.ne' hpowpos.ne', Real.log_rpow hXpos,
    ← hℓ] at hhighlog
  have hC₀log : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  rw [abs_le]
  constructor <;> linarith

/-- The exact source quotient lengths `Mᵢ=Nᵢ/rᵢ` multiply to
`Y=N₁N₂N₃/d` when the allocation satisfies `r₁r₂r₃=d`. -/
theorem selectedMobiusPTW_quotient_length_product
    {N₁ N₂ N₃ r₁ r₂ r₃ d M₁ M₂ M₃ Y : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN₃ : 0 < N₃)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hd : 0 < d) (halloc : r₁ * r₂ * r₃ = d)
    (hM₁ : M₁ = N₁ / r₁) (hM₂ : M₂ = N₂ / r₂)
    (hM₃ : M₃ = N₃ / r₃) (hY : Y = M₁ * M₂ * M₃) :
    Y = (N₁ * N₂ * N₃) / d := by
  rw [hY, hM₁, hM₂, hM₃, ← halloc]
  field_simp [ne_of_gt hr₁, ne_of_gt hr₂, ne_of_gt hr₃]

/-- The source block support and divisor allocation give the exact log-length
comparison used to pass to the normalized exponents `log Mᵢ/log Y`.

The hypotheses `rᵢ≤d≤(log X)^a` and `r₁r₂r₃=d` are kept explicit. The
conclusion records both `|log Y−log X|≤E_X` and the `2E_X/log Y` deviation
for each normalized exponent; the sum of those exponents is exactly one. -/
theorem selectedMobiusPTW_allocated_length_log_geometry
    {X C₀ ℓ a γ₁ γ₂ γ₃ N₁ N₂ N₃ r₁ r₂ r₃ d M₁ M₂ M₃ Y : ℝ}
    (hX : 1 < X) (hℓ : ℓ = Real.log X) (hℓone : 1 ≤ ℓ)
    (ha : 0 ≤ a) (hC₀ : 1 ≤ C₀)
    (hγsum : γ₁ + γ₂ + γ₃ = 1)
    (hN₁lower : C₀⁻¹ * X ^ γ₁ ≤ N₁)
    (hN₁upper : N₁ ≤ C₀ * X ^ γ₁)
    (hN₂lower : C₀⁻¹ * X ^ γ₂ ≤ N₂)
    (hN₂upper : N₂ ≤ C₀ * X ^ γ₂)
    (hN₃lower : C₀⁻¹ * X ^ γ₃ ≤ N₃)
    (hN₃upper : N₃ ≤ C₀ * X ^ γ₃)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hr₁one : 1 ≤ r₁) (hr₂one : 1 ≤ r₂) (hr₃one : 1 ≤ r₃)
    (hd : 1 ≤ d) (halloc : r₁ * r₂ * r₃ = d)
    (hr₁d : r₁ ≤ d) (hr₂d : r₂ ≤ d) (hr₃d : r₃ ≤ d)
    (hdbound : d ≤ ℓ ^ a)
    (hγ₁lo : 0 ≤ γ₁) (hγ₂lo : 0 ≤ γ₂) (hγ₃lo : 0 ≤ γ₃)
    (hM₁ : M₁ = N₁ / r₁) (hM₂ : M₂ = N₂ / r₂)
    (hM₃ : M₃ = N₃ / r₃) (hY : Y = M₁ * M₂ * M₃)
    (hE : 3 * Real.log C₀ + a * Real.log ℓ ≤ ℓ / 2) :
    0 < Y ∧
      X ^ (1 / 2 : ℝ) ≤ Y ∧
      |Real.log Y - ℓ| ≤ 3 * Real.log C₀ + a * Real.log ℓ ∧
      (Real.log M₁ / Real.log Y) +
          (Real.log M₂ / Real.log Y) +
            (Real.log M₃ / Real.log Y) = 1 ∧
      |Real.log M₁ / Real.log Y - γ₁| ≤
        2 * (3 * Real.log C₀ + a * Real.log ℓ) / Real.log Y ∧
      |Real.log M₂ / Real.log Y - γ₂| ≤
        2 * (3 * Real.log C₀ + a * Real.log ℓ) / Real.log Y ∧
      |Real.log M₃ / Real.log Y - γ₃| ≤
        2 * (3 * Real.log C₀ + a * Real.log ℓ) / Real.log Y := by
  have hXpos : 0 < X := by linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) hC₀
  have hℓpos : 0 < ℓ := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hN₁pos : 0 < N₁ := by
    exact lt_of_lt_of_le
      (mul_pos (inv_pos.mpr hC₀pos) (Real.rpow_pos_of_pos hXpos γ₁)) hN₁lower
  have hN₂pos : 0 < N₂ := by
    exact lt_of_lt_of_le
      (mul_pos (inv_pos.mpr hC₀pos) (Real.rpow_pos_of_pos hXpos γ₂)) hN₂lower
  have hN₃pos : 0 < N₃ := by
    exact lt_of_lt_of_le
      (mul_pos (inv_pos.mpr hC₀pos) (Real.rpow_pos_of_pos hXpos γ₃)) hN₃lower
  have hM₁pos : 0 < M₁ := by rw [hM₁]; exact div_pos hN₁pos hr₁
  have hM₂pos : 0 < M₂ := by rw [hM₂]; exact div_pos hN₂pos hr₂
  have hM₃pos : 0 < M₃ := by rw [hM₃]; exact div_pos hN₃pos hr₃
  have hYpos : 0 < Y := by rw [hY]; positivity
  have hN₁log := selectedMobiusPTW_log_of_scaled_block_support
    hX hℓ hC₀ hN₁lower hN₁upper
  have hN₂log := selectedMobiusPTW_log_of_scaled_block_support
    hX hℓ hC₀ hN₂lower hN₂upper
  have hN₃log := selectedMobiusPTW_log_of_scaled_block_support
    hX hℓ hC₀ hN₃lower hN₃upper
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd
  have hlogdle : Real.log d ≤ a * Real.log ℓ := by
    have hlogle := Real.log_le_log hdpos hdbound
    rw [Real.log_rpow hℓpos] at hlogle
    exact hlogle
  have hlogri₁ : 0 ≤ Real.log r₁ := Real.log_nonneg hr₁one
  have hlogri₂ : 0 ≤ Real.log r₂ := Real.log_nonneg hr₂one
  have hlogri₃ : 0 ≤ Real.log r₃ := Real.log_nonneg hr₃one
  have hlogri₁d : Real.log r₁ ≤ Real.log d := Real.log_le_log hr₁ hr₁d
  have hlogri₂d : Real.log r₂ ≤ Real.log d := Real.log_le_log hr₂ hr₂d
  have hlogri₃d : Real.log r₃ ≤ Real.log d := Real.log_le_log hr₃ hr₃d
  have hYrepr := selectedMobiusPTW_quotient_length_product
    hN₁pos hN₂pos hN₃pos hr₁ hr₂ hr₃ hdpos halloc hM₁ hM₂ hM₃ hY
  have hNlogprod :
      Real.log (N₁ * N₂ * N₃) =
        Real.log N₁ + Real.log N₂ + Real.log N₃ := by
    calc
      Real.log (N₁ * N₂ * N₃) = Real.log ((N₁ * N₂) * N₃) := by rfl
      _ = Real.log (N₁ * N₂) + Real.log N₃ :=
        Real.log_mul (ne_of_gt (mul_pos hN₁pos hN₂pos)) hN₃pos.ne'
      _ = Real.log N₁ + Real.log N₂ + Real.log N₃ := by
        rw [Real.log_mul hN₁pos.ne' hN₂pos.ne']
  have hlogdprod :
      Real.log d = Real.log r₁ + Real.log r₂ + Real.log r₃ := by
    calc
      Real.log d = Real.log ((r₁ * r₂) * r₃) := by rw [← halloc]
      _ = Real.log (r₁ * r₂) + Real.log r₃ :=
        Real.log_mul (ne_of_gt (mul_pos hr₁ hr₂)) hr₃.ne'
      _ = Real.log r₁ + Real.log r₂ + Real.log r₃ := by
        rw [Real.log_mul hr₁.ne' hr₂.ne']
  have hnumAssoc : N₁ * N₂ * N₃ = N₁ * (N₂ * N₃) := by ring
  have hlogY :
      Real.log Y = Real.log N₁ + Real.log N₂ + Real.log N₃ - Real.log d := by
    calc
      Real.log Y = Real.log ((N₁ * (N₂ * N₃)) / d) := by
        rw [hYrepr, hnumAssoc]
      _ = Real.log (N₁ * (N₂ * N₃)) - Real.log d :=
        Real.log_div (ne_of_gt (mul_pos hN₁pos
          (mul_pos hN₂pos hN₃pos))) hdpos.ne'
      _ = Real.log N₁ + Real.log N₂ + Real.log N₃ - Real.log d := by
        rw [Real.log_mul hN₁pos.ne' (ne_of_gt (mul_pos hN₂pos hN₃pos)),
          Real.log_mul hN₂pos.ne' hN₃pos.ne']
        ring
  have hlogYdiff :
      Real.log Y - ℓ =
        (Real.log N₁ - γ₁ * ℓ) +
          (Real.log N₂ - γ₂ * ℓ) +
          (Real.log N₃ - γ₃ * ℓ) - Real.log d := by
    rw [hlogY]
    calc
      Real.log N₁ + Real.log N₂ + Real.log N₃ - Real.log d - ℓ =
          Real.log N₁ + Real.log N₂ + Real.log N₃ -
            (γ₁ + γ₂ + γ₃) * ℓ - Real.log d := by rw [hγsum]; ring
      _ = _ := by ring
  have hC₀log : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  have hℓlog : 0 ≤ Real.log ℓ := Real.log_nonneg hℓone
  have hEpos : 0 ≤ 3 * Real.log C₀ + a * Real.log ℓ := by positivity
  have hlogYabs : |Real.log Y - ℓ| ≤ 3 * Real.log C₀ + a * Real.log ℓ := by
    rw [hlogYdiff, abs_le]
    constructor
    · have h1 := abs_le.mp hN₁log
      have h2 := abs_le.mp hN₂log
      have h3 := abs_le.mp hN₃log
      linarith [hlogdle]
    · have h1 := abs_le.mp hN₁log
      have h2 := abs_le.mp hN₂log
      have h3 := abs_le.mp hN₃log
      linarith [hlogd]
  have hlogYlower : ℓ / 2 ≤ Real.log Y := by
    have hlow := (abs_le.mp hlogYabs).1
    nlinarith [hE]
  have hlogYpos : 0 < Real.log Y := by linarith
  have hXhalfpos : 0 < X ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hlogXhalf : Real.log (X ^ (1 / 2 : ℝ)) = ℓ / 2 := by
    rw [Real.log_rpow hXpos, ← hℓ]
    ring
  have hYlower : X ^ (1 / 2 : ℝ) ≤ Y := by
    have hlogle : Real.log (X ^ (1 / 2 : ℝ)) ≤ Real.log Y := by
      rw [hlogXhalf]
      exact hlogYlower
    have hexp := Real.exp_le_exp.mpr hlogle
    rw [Real.exp_log hXhalfpos, Real.exp_log hYpos] at hexp
    exact hexp
  have hlogM₁ : Real.log M₁ = Real.log N₁ - Real.log r₁ := by
    rw [hM₁, Real.log_div hN₁pos.ne' hr₁.ne']
  have hlogM₂ : Real.log M₂ = Real.log N₂ - Real.log r₂ := by
    rw [hM₂, Real.log_div hN₂pos.ne' hr₂.ne']
  have hlogM₃ : Real.log M₃ = Real.log N₃ - Real.log r₃ := by
    rw [hM₃, Real.log_div hN₃pos.ne' hr₃.ne']
  have hlogYfromM :
      Real.log Y = Real.log M₁ + Real.log M₂ + Real.log M₃ := by
    calc
      Real.log Y = Real.log ((M₁ * M₂) * M₃) := by rw [hY]
      _ = Real.log (M₁ * M₂) + Real.log M₃ :=
        Real.log_mul (ne_of_gt (mul_pos hM₁pos hM₂pos)) hM₃pos.ne'
      _ = Real.log M₁ + Real.log M₂ + Real.log M₃ := by
        rw [Real.log_mul hM₁pos.ne' hM₂pos.ne']
  have hsumalpha :
      (Real.log M₁ / Real.log Y) +
          (Real.log M₂ / Real.log Y) +
            (Real.log M₃ / Real.log Y) = 1 := by
    calc
      (Real.log M₁ / Real.log Y) +
          (Real.log M₂ / Real.log Y) +
            (Real.log M₃ / Real.log Y) =
          (Real.log M₁ + Real.log M₂ + Real.log M₃) / Real.log Y := by
            field_simp [ne_of_gt hlogYpos]
      _ = 1 := by rw [← hlogYfromM]; exact div_self (ne_of_gt hlogYpos)
  have hexp₁ :
      Real.log M₁ - γ₁ * Real.log Y =
        (Real.log N₁ - γ₁ * ℓ) - Real.log r₁ - γ₁ * (Real.log Y - ℓ) := by
    rw [hlogM₁]
    ring
  have hexp₂ :
      Real.log M₂ - γ₂ * Real.log Y =
        (Real.log N₂ - γ₂ * ℓ) - Real.log r₂ - γ₂ * (Real.log Y - ℓ) := by
    rw [hlogM₂]
    ring
  have hexp₃ :
      Real.log M₃ - γ₃ * Real.log Y =
        (Real.log N₃ - γ₃ * ℓ) - Real.log r₃ - γ₃ * (Real.log Y - ℓ) := by
    rw [hlogM₃]
    ring
  have hγ₁hi : γ₁ ≤ 1 := by
    linarith [hγsum]
  have hγ₂hi : γ₂ ≤ 1 := by
    linarith [hγsum]
  have hγ₃hi : γ₃ ≤ 1 := by
    linarith [hγsum]
  have hterm₁ : |γ₁ * (Real.log Y - ℓ)| ≤
      3 * Real.log C₀ + a * Real.log ℓ := by
    rw [abs_mul]
    have hγabs : |γ₁| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      |γ₁| * |Real.log Y - ℓ| ≤ 1 *
          (3 * Real.log C₀ + a * Real.log ℓ) :=
        mul_le_mul hγabs hlogYabs (abs_nonneg _) (by norm_num)
      _ = 3 * Real.log C₀ + a * Real.log ℓ := one_mul _
  have hterm₂ : |γ₂ * (Real.log Y - ℓ)| ≤
      3 * Real.log C₀ + a * Real.log ℓ := by
    rw [abs_mul]
    have hγabs : |γ₂| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      |γ₂| * |Real.log Y - ℓ| ≤ 1 *
          (3 * Real.log C₀ + a * Real.log ℓ) :=
        mul_le_mul hγabs hlogYabs (abs_nonneg _) (by norm_num)
      _ = 3 * Real.log C₀ + a * Real.log ℓ := one_mul _
  have hterm₃ : |γ₃ * (Real.log Y - ℓ)| ≤
      3 * Real.log C₀ + a * Real.log ℓ := by
    rw [abs_mul]
    have hγabs : |γ₃| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      |γ₃| * |Real.log Y - ℓ| ≤ 1 *
          (3 * Real.log C₀ + a * Real.log ℓ) :=
        mul_le_mul hγabs hlogYabs (abs_nonneg _) (by norm_num)
      _ = 3 * Real.log C₀ + a * Real.log ℓ := one_mul _
  have hdev₁ : |Real.log M₁ - γ₁ * Real.log Y| ≤
      2 * (3 * Real.log C₀ + a * Real.log ℓ) := by
    rw [hexp₁]
    calc
      |(Real.log N₁ - γ₁ * ℓ) - Real.log r₁ -
          γ₁ * (Real.log Y - ℓ)| ≤
          |Real.log N₁ - γ₁ * ℓ| + |Real.log r₁| +
            |γ₁ * (Real.log Y - ℓ)| := by
              calc
                _ ≤ |(Real.log N₁ - γ₁ * ℓ) - Real.log r₁| +
                    |γ₁ * (Real.log Y - ℓ)| := abs_sub _ _
                _ ≤ |Real.log N₁ - γ₁ * ℓ| + |Real.log r₁| +
                    |γ₁ * (Real.log Y - ℓ)| := by
                  have h := abs_sub (Real.log N₁ - γ₁ * ℓ) (Real.log r₁)
                  linarith
      _ ≤ Real.log C₀ + a * Real.log ℓ +
            (3 * Real.log C₀ + a * Real.log ℓ) := by
              have hNabs := hN₁log
              have hriabs : |Real.log r₁| = Real.log r₁ := abs_of_nonneg hlogri₁
              rw [hriabs]
              nlinarith [hlogri₁d, hlogdle]
      _ ≤ 2 * (3 * Real.log C₀ + a * Real.log ℓ) := by nlinarith [hC₀log, hℓlog, ha]
  have hdev₂ : |Real.log M₂ - γ₂ * Real.log Y| ≤
      2 * (3 * Real.log C₀ + a * Real.log ℓ) := by
    rw [hexp₂]
    calc
      |(Real.log N₂ - γ₂ * ℓ) - Real.log r₂ -
          γ₂ * (Real.log Y - ℓ)| ≤
          |Real.log N₂ - γ₂ * ℓ| + |Real.log r₂| +
            |γ₂ * (Real.log Y - ℓ)| := by
              calc
                _ ≤ |(Real.log N₂ - γ₂ * ℓ) - Real.log r₂| +
                    |γ₂ * (Real.log Y - ℓ)| := abs_sub _ _
                _ ≤ |Real.log N₂ - γ₂ * ℓ| + |Real.log r₂| +
                    |γ₂ * (Real.log Y - ℓ)| := by
                  have h := abs_sub (Real.log N₂ - γ₂ * ℓ) (Real.log r₂)
                  linarith
      _ ≤ Real.log C₀ + a * Real.log ℓ +
            (3 * Real.log C₀ + a * Real.log ℓ) := by
              have hNabs := hN₂log
              have hriabs : |Real.log r₂| = Real.log r₂ := abs_of_nonneg hlogri₂
              rw [hriabs]
              nlinarith [hlogri₂d, hlogdle]
      _ ≤ 2 * (3 * Real.log C₀ + a * Real.log ℓ) := by nlinarith [hC₀log, hℓlog, ha]
  have hdev₃ : |Real.log M₃ - γ₃ * Real.log Y| ≤
      2 * (3 * Real.log C₀ + a * Real.log ℓ) := by
    rw [hexp₃]
    calc
      |(Real.log N₃ - γ₃ * ℓ) - Real.log r₃ -
          γ₃ * (Real.log Y - ℓ)| ≤
          |Real.log N₃ - γ₃ * ℓ| + |Real.log r₃| +
            |γ₃ * (Real.log Y - ℓ)| := by
              calc
                _ ≤ |(Real.log N₃ - γ₃ * ℓ) - Real.log r₃| +
                    |γ₃ * (Real.log Y - ℓ)| := abs_sub _ _
                _ ≤ |Real.log N₃ - γ₃ * ℓ| + |Real.log r₃| +
                    |γ₃ * (Real.log Y - ℓ)| := by
                  have h := abs_sub (Real.log N₃ - γ₃ * ℓ) (Real.log r₃)
                  linarith
      _ ≤ Real.log C₀ + a * Real.log ℓ +
            (3 * Real.log C₀ + a * Real.log ℓ) := by
              have hNabs := hN₃log
              have hriabs : |Real.log r₃| = Real.log r₃ := abs_of_nonneg hlogri₃
              rw [hriabs]
              nlinarith [hlogri₃d, hlogdle]
      _ ≤ 2 * (3 * Real.log C₀ + a * Real.log ℓ) := by nlinarith [hC₀log, hℓlog, ha]
  have halpha₁ : |Real.log M₁ / Real.log Y - γ₁| ≤
      2 * (3 * Real.log C₀ + a * Real.log ℓ) / Real.log Y := by
    have hquot : Real.log M₁ / Real.log Y - γ₁ =
        (Real.log M₁ - γ₁ * Real.log Y) / Real.log Y := by
      field_simp [ne_of_gt hlogYpos]
    rw [hquot, abs_div, abs_of_pos hlogYpos]
    exact div_le_div_of_nonneg_right hdev₁ hlogYpos.le
  have halpha₂ : |Real.log M₂ / Real.log Y - γ₂| ≤
      2 * (3 * Real.log C₀ + a * Real.log ℓ) / Real.log Y := by
    have hquot : Real.log M₂ / Real.log Y - γ₂ =
        (Real.log M₂ - γ₂ * Real.log Y) / Real.log Y := by
      field_simp [ne_of_gt hlogYpos]
    rw [hquot, abs_div, abs_of_pos hlogYpos]
    exact div_le_div_of_nonneg_right hdev₂ hlogYpos.le
  have halpha₃ : |Real.log M₃ / Real.log Y - γ₃| ≤
      2 * (3 * Real.log C₀ + a * Real.log ℓ) / Real.log Y := by
    have hquot : Real.log M₃ / Real.log Y - γ₃ =
        (Real.log M₃ - γ₃ * Real.log Y) / Real.log Y := by
      field_simp [ne_of_gt hlogYpos]
    rw [hquot, abs_div, abs_of_pos hlogYpos]
    exact div_le_div_of_nonneg_right hdev₃ hlogYpos.le
  exact ⟨hYpos, hYlower, hlogYabs, hsumalpha,
    halpha₁, halpha₂, halpha₃⟩

#print axioms selectedMobiusPTW_log_of_scaled_block_support
#print axioms selectedMobiusPTW_quotient_length_product
#print axioms selectedMobiusPTW_allocated_length_log_geometry

end FractionalPrimes.Literature.DirichletMean

end
