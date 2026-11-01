module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FractionalPrimes.Literature.Reciprocal.GlobalCharacterMobius
public import FractionalPrimes.Literature.Reciprocal.GlobalMobiusCharacterInterval
public import FractionalPrimes.Literature.LongArithmetic.ShiftedCharacterMobiusSeries
public import FractionalPrimes.Literature.MobiusToLong.MobiusLargeHalfExponentTransfer
public import FractionalPrimes.Literature.MobiusToLong.MobiusLargeHalfHarmonicBound
@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.Reciprocal
open FractionalPrimes.Literature.LongArithmetic

namespace FractionalPrimes.Literature.MobiusToLong

/-- The large-Möbius half of the square-root hyperbola. The constant is the
witness `C(E,B+1)` supplied by `lml:global-mobius`; the finite sums use the
paper's real cutoffs and `(floor D, floor u]` convention. -/
theorem largeMobiusHyperbolaHalf
    (hMUF : MobiusUniformity) {E B : ℝ} (hE : 0 < E) (hB : 0 < B)
    : ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ {x : ℝ} (_hx : 9 ≤ x)
        (_hlog : (2 : ℝ) ^ (B + 1) ≤ Real.log x)
        {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
        (_hq : (q : ℝ) ≤ (Real.log x) ^ B),
        ‖∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
            dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ) *
              (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
                  (Nat.floor (x / (m : ℝ))),
                globalMobiusCharacterCoefficient χ d)‖ ≤
          (2 : ℝ) ^ (E + 2) * C₁ * x * (Real.log x) ^ (2 - E) := by
  obtain ⟨C₁, hC₁, hglobal⟩ :=
    globalCharacterMobius hMUF hE (by linarith : 0 < B + 1)
  refine ⟨C₁, hC₁, ?_⟩
  intro x hx hlog q inst χ hq
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsqrt3 : 3 ≤ Real.sqrt x := by
    have hroot9 : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc
      (3 : ℝ) = Real.sqrt 9 := hroot9.symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hsqrt_le_x : Real.sqrt x ≤ x :=
    Real.sqrt_le_self_iff.mpr (Or.inr hxone)
  have hx_div_sqrt : x / Real.sqrt x = Real.sqrt x := by
    calc
      x / Real.sqrt x = (Real.sqrt x) ^ 2 / Real.sqrt x := by
        rw [Real.sq_sqrt hxpos.le]
      _ = Real.sqrt x := by field_simp [ne_of_gt hsqrtpos]
  have houter_floor : Nat.floor (x / Real.sqrt x) = Nat.floor (Real.sqrt x) :=
    congrArg Nat.floor hx_div_sqrt
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogD : Real.log (Real.sqrt x) = Real.log x / 2 := by
    rw [Real.log_sqrt hxpos.le]
  have hhalf_pow : (Real.log x / 2) ^ (-E) =
      (2 : ℝ) ^ E * (Real.log x) ^ (-E) := by
    rw [Real.div_rpow hlogxpos.le (by norm_num : (0 : ℝ) ≤ 2) (-E),
      Real.rpow_neg hlogxpos.le E,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) E]
    field_simp
  have hqpos : 1 ≤ q := by
    have hqne : q ≠ 0 := NeZero.ne q
    omega
  have hglobal_scaled {u : ℝ} (huD : Real.sqrt x ≤ u) (hux : u ≤ x) :
      ‖globalMobiusCharacterSum χ u‖ ≤
        (2 : ℝ) ^ E * C₁ * u * (Real.log x) ^ (-E) := by
    have hu3 : 3 ≤ u := hsqrt3.trans huD
    have huPos : 0 < u := by linarith
    have hlogu : Real.log (Real.sqrt x) ≤ Real.log u :=
      Real.log_le_log hsqrtpos huD
    have hlog_half_le : Real.log x / 2 ≤ Real.log u := by
      rw [← hlogD]
      exact hlogu
    have hpow_le : (Real.log u) ^ (-E) ≤ (Real.log x / 2) ^ (-E) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlog_half_le (by linarith)
    have hqu : (q : ℝ) ≤ (Real.log u) ^ (B + 1) :=
      mobius_log_exponent_transfer hx hB hlog huD hux hq
    have hbound := hglobal χ (x := u) hu3 hqpos hqu
    calc
      ‖globalMobiusCharacterSum χ u‖ ≤ C₁ * u * (Real.log u) ^ (-E) := hbound
      _ ≤ C₁ * u * (Real.log x / 2) ^ (-E) :=
        mul_le_mul_of_nonneg_left hpow_le
          (mul_nonneg (by linarith : 0 ≤ C₁) huPos.le)
      _ = (2 : ℝ) ^ E * C₁ * u * (Real.log x) ^ (-E) := by
        rw [hhalf_pow]
        ring
  have hinterval_bound {u : ℝ} (huD : Real.sqrt x ≤ u) (hux : u ≤ x) :
      ‖∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x)) (Nat.floor u),
          globalMobiusCharacterCoefficient χ d‖ ≤
        (2 : ℝ) ^ (E + 1) * C₁ * u * (Real.log x) ^ (-E) := by
    rw [globalMobiusCharacterInterval_eq_sub χ (le_of_lt hsqrtpos) huD]
    have hDscaled := hglobal_scaled le_rfl hsqrt_le_x
    have huscaled := hglobal_scaled huD hux
    have hfactor_nonneg :
        0 ≤ (2 : ℝ) ^ E * C₁ * (Real.log x) ^ (-E) := by positivity
    have huplus : u + Real.sqrt x ≤ 2 * u := by linarith
    calc
      ‖globalMobiusCharacterSum χ u - globalMobiusCharacterSum χ (Real.sqrt x)‖ ≤
          ‖globalMobiusCharacterSum χ u‖ +
            ‖globalMobiusCharacterSum χ (Real.sqrt x)‖ := norm_sub_le _ _
      _ ≤ (2 : ℝ) ^ E * C₁ * u * (Real.log x) ^ (-E) +
            (2 : ℝ) ^ E * C₁ * Real.sqrt x * (Real.log x) ^ (-E) :=
          add_le_add huscaled hDscaled
      _ = ((2 : ℝ) ^ E * C₁ * (Real.log x) ^ (-E)) *
            (u + Real.sqrt x) := by ring
      _ ≤ ((2 : ℝ) ^ E * C₁ * (Real.log x) ^ (-E)) * (2 * u) :=
          mul_le_mul_of_nonneg_left huplus hfactor_nonneg
      _ = (2 : ℝ) ^ (E + 1) * C₁ * u * (Real.log x) ^ (-E) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) E 1, Real.rpow_one]
          ring
  have hterm {m : ℕ}
      (hm : m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x))) :
      ‖dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ) *
          (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
              (Nat.floor (x / (m : ℝ))),
            globalMobiusCharacterCoefficient χ d)‖ ≤
        (2 : ℝ) ^ (E + 1) * C₁ * x * (Real.log x) ^ (-E) *
          (Real.log (m : ℝ) / (m : ℝ)) := by
    have hmIcc := Finset.mem_Icc.mp hm
    have hmreal : 1 ≤ (m : ℝ) := by exact_mod_cast hmIcc.1
    have hmpos : 0 < (m : ℝ) := by linarith
    have hmle : (m : ℝ) ≤ x / Real.sqrt x := by
      calc
        (m : ℝ) ≤ (Nat.floor (x / Real.sqrt x) : ℝ) := by exact_mod_cast hmIcc.2
        _ ≤ x / Real.sqrt x := Nat.floor_le (by positivity)
    have hmd : (m : ℝ) * Real.sqrt x ≤ x := by
      calc
        (m : ℝ) * Real.sqrt x ≤ (x / Real.sqrt x) * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hmle hsqrtpos.le
        _ = x := by field_simp [ne_of_gt hsqrtpos]
    have huLower : Real.sqrt x ≤ x / (m : ℝ) := by
      rw [le_div_iff₀ hmpos]
      nlinarith [hmd]
    have huUpper : x / (m : ℝ) ≤ x := by
      rw [div_le_iff₀ hmpos]
      nlinarith [hmreal, hx]
    have hinner := hinterval_bound huLower huUpper
    have hχnorm : ‖dirichletCharacterNatHom χ m‖ ≤ 1 :=
      dirichletCharacterNatHom_norm_le_one χ (by omega)
    have hlognonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmreal
    have hlognorm : ‖(Real.log (m : ℝ) : ℂ)‖ = Real.log (m : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlognonneg]
    calc
      _ = ‖dirichletCharacterNatHom χ m‖ *
            ‖(Real.log (m : ℝ) : ℂ)‖ *
              ‖∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
                    (Nat.floor (x / (m : ℝ))),
                  globalMobiusCharacterCoefficient χ d‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ 1 * Real.log (m : ℝ) *
            ‖∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
                  (Nat.floor (x / (m : ℝ))),
                globalMobiusCharacterCoefficient χ d‖ := by
        rw [hlognorm]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hχnorm hlognonneg) (norm_nonneg _)
      _ ≤ 1 * Real.log (m : ℝ) *
            ((2 : ℝ) ^ (E + 1) * C₁ * (x / (m : ℝ)) *
              (Real.log x) ^ (-E)) :=
        mul_le_mul_of_nonneg_left hinner (mul_nonneg (by norm_num) hlognonneg)
      _ = (2 : ℝ) ^ (E + 1) * C₁ * x * (Real.log x) ^ (-E) *
            (Real.log (m : ℝ) / (m : ℝ)) := by
        rw [div_eq_mul_inv]
        ring
  have houter_nonneg :
      0 ≤ (2 : ℝ) ^ (E + 1) * C₁ * x * (Real.log x) ^ (-E) := by
    positivity
  have hsum_bound :
      ‖∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
          dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ) *
            (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
                (Nat.floor (x / (m : ℝ))),
              globalMobiusCharacterCoefficient χ d)‖ ≤
        (2 : ℝ) ^ (E + 1) * C₁ * x * (Real.log x) ^ (-E) *
          (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
            Real.log (m : ℝ) / (m : ℝ)) := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
            ‖dirichletCharacterNatHom χ m * (Real.log (m : ℝ) : ℂ) *
              (∑ d ∈ Finset.Ioc (Nat.floor (Real.sqrt x))
                  (Nat.floor (x / (m : ℝ))),
              globalMobiusCharacterCoefficient χ d)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
            ((2 : ℝ) ^ (E + 1) * C₁ * x * (Real.log x) ^ (-E) *
              (Real.log (m : ℝ) / (m : ℝ))) :=
        Finset.sum_le_sum fun m hm => hterm hm
      _ = (2 : ℝ) ^ (E + 1) * C₁ * x * (Real.log x) ^ (-E) *
            (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
              Real.log (m : ℝ) / (m : ℝ)) := by rw [Finset.mul_sum]
  have hharmonic :
      (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
        Real.log (m : ℝ) / (m : ℝ)) ≤ 2 * (Real.log x) ^ 2 := by
    rw [houter_floor]
    exact mobius_large_half_harmonic_bound hx
  have hlog_product :
      (Real.log x) ^ (-E) * (Real.log x) ^ (2 : ℕ) =
        (Real.log x) ^ (2 - E) := by
    calc
      _ = (Real.log x) ^ (-E) * (Real.log x) ^ (2 : ℝ) := by
        congr 1
        exact (Real.rpow_natCast (Real.log x) 2).symm
      _ = (Real.log x) ^ (-E + 2) := by
        rw [← Real.rpow_add hlogxpos]
      _ = (Real.log x) ^ (2 - E) := by
        congr 1
        ring
  calc
    _ ≤ (2 : ℝ) ^ (E + 1) * C₁ * x * (Real.log x) ^ (-E) *
          (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (x / Real.sqrt x)),
            Real.log (m : ℝ) / (m : ℝ)) := hsum_bound
    _ ≤ (2 : ℝ) ^ (E + 1) * C₁ * x * (Real.log x) ^ (-E) *
          (2 * (Real.log x) ^ 2) :=
      mul_le_mul_of_nonneg_left hharmonic houter_nonneg
    _ = (2 : ℝ) ^ (E + 2) * C₁ * x * (Real.log x) ^ (2 - E) := by
      have hpow : (2 : ℝ) ^ (E + 1) * 2 = (2 : ℝ) ^ (E + 2) := by
        calc
          _ = (2 : ℝ) ^ (E + 1) * (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (2 : ℝ) ^ ((E + 1) + 1) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) (E + 1) 1]
          _ = (2 : ℝ) ^ (E + 2) := by congr 1; ring
      calc
        _ = ((2 : ℝ) ^ (E + 1) * 2) * C₁ * x *
              (Real.log x) ^ (-E) * (Real.log x) ^ 2 := by ring
        _ = (2 : ℝ) ^ (E + 2) * C₁ * x *
              ((Real.log x) ^ (-E) * (Real.log x) ^ 2) := by
          rw [hpow]
          ring
        _ = (2 : ℝ) ^ (E + 2) * C₁ * x * (Real.log x) ^ (2 - E) := by
          rw [hlog_product]
        _ = _ := by ring

end FractionalPrimes.Literature.MobiusToLong
