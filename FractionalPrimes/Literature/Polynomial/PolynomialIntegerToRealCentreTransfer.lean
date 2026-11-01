module

public import FractionalPrimes.Literature.Centres.CramerChangeCentre

/-!
# Integer-to-real centre parameters

The scale transfer at the start of blueprint `lc:integer-to-real`, including
the exact floor-indexed integer interval, is isolated here from the
conditional arithmetic cancellation estimate.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Centres

noncomputable def integerToRealThreshold (ε : ℝ) : ℝ := (2 : ℝ) ^ (4 / ε)

/-- At the blueprint threshold `X₀ = 2^(4/ε)`, the real interval floors
produce the exact integer centre/length in the permitted range for applying
the conditional integer estimate with `η = ε/2`. -/
theorem integerToRealFloorParameterTransfer {ε X H : ℝ}
    (hε : 0 < ε) (hεtop : ε < 3 / 16)
    (hX₀ : integerToRealThreshold ε ≤ X)
    (hHlower : X ^ (5 / 8 + ε) ≤ H)
    (hHupper : H ≤ X ^ (1 - ε)) :
    let M : ℕ := Nat.floor X
    let L : ℕ := Nat.floor (X + H) - M
    3 ≤ M ∧
      0 < ε / 2 ∧
      ε / 2 < 3 / 16 ∧
      X / 2 ≤ (M : ℝ) ∧
      (M : ℝ) ≤ X ∧
      H / 2 ≤ (L : ℝ) ∧
      (L : ℝ) ≤ 2 * H ∧
      (M : ℝ) ^ (5 / 8 + ε / 2) ≤ (L : ℝ) ∧
      (L : ℝ) ≤ (M : ℝ) ^ (1 - ε / 2) ∧
      Real.log X ≤ 2 * Real.log (M : ℝ) ∧
      FractionalPrimes.realIntegerInterval X H =
        Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ) := by
  let M : ℕ := Nat.floor X
  let L : ℕ := Nat.floor (X + H) - M
  have hεlt1 : ε < 1 := by linarith
  have hexpLarge : 2 ≤ 4 / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [hεtop]
  have hX₀ge4 : 4 ≤ integerToRealThreshold ε := by
    dsimp [integerToRealThreshold]
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hexpLarge
    norm_num at h ⊢
    exact h
  have hXge4 : 4 ≤ X := hX₀ge4.trans hX₀
  have hXpos : 0 < X := by linarith
  have hXnonneg : 0 ≤ X := le_of_lt hXpos
  have hXone : 1 ≤ X := by linarith
  have hεhalfpos : 0 < ε / 2 := by positivity
  have hX₀pow : integerToRealThreshold ε ^ (ε / 2) = 4 := by
    dsimp [integerToRealThreshold]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hmul : (4 / ε) * (ε / 2) = 2 := by
      field_simp
      ring
    rw [hmul]
    norm_num
  have hXpow4 : 4 ≤ X ^ (ε / 2) := by
    calc
      4 = integerToRealThreshold ε ^ (ε / 2) := hX₀pow.symm
      _ ≤ X ^ (ε / 2) :=
        Real.rpow_le_rpow (by positivity) hX₀ hεhalfpos.le
  have hHge4 : 4 ≤ H := by
    have hexp : ε / 2 ≤ 5 / 8 + ε := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hXone hexp
    exact le_trans hXpow4 (le_trans hpow hHlower)
  have hMcast_le : (M : ℝ) ≤ X := by
    dsimp [M]
    exact Nat.floor_le hXnonneg
  have hX_lt_M_add_one : X < (M : ℝ) + 1 := by
    dsimp [M]
    exact Nat.lt_floor_add_one X
  have hMthree : 3 ≤ M := by
    dsimp [M]
    exact Nat.le_floor (by linarith : (3 : ℝ) ≤ X)
  have hMhalf : X / 2 ≤ (M : ℝ) := by
    nlinarith [hX_lt_M_add_one, hXge4]
  have hlogCompare : Real.log X ≤ 2 * Real.log (M : ℝ) := by
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
      ring
    have hlogXlower : 2 * Real.log 2 ≤ Real.log X := by
      calc
        2 * Real.log 2 = Real.log 4 := hlog4.symm
        _ ≤ Real.log X := Real.log_le_log (by norm_num) hXge4
    have hlogMlower : Real.log (X / 2) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by positivity) hMhalf
    have hlogDiv : Real.log (X / 2) = Real.log X - Real.log 2 := by
      rw [Real.log_div hXpos.ne' (by norm_num)]
    rw [hlogDiv] at hlogMlower
    nlinarith
  have hHpos : 0 < H := by linarith [hHge4]
  have hfloorMono : M ≤ Nat.floor (X + H) := by
    dsimp [M]
    exact Nat.floor_mono (by linarith)
  have hLcast : (L : ℝ) = (Nat.floor (X + H) : ℝ) - (M : ℝ) := by
    dsimp [L]
    exact Nat.cast_sub hfloorMono
  have hfloorEndLe : (Nat.floor (X + H) : ℝ) ≤ X + H :=
    Nat.floor_le (by linarith)
  have hfloorEndLt : X + H < (Nat.floor (X + H) : ℝ) + 1 :=
    Nat.lt_floor_add_one (X + H)
  have hLhalf : H / 2 ≤ (L : ℝ) := by
    rw [hLcast]
    nlinarith [hX_lt_M_add_one, hfloorEndLt, hHge4]
  have hLdouble : (L : ℝ) ≤ 2 * H := by
    rw [hLcast]
    nlinarith [hMhalf, hfloorEndLe, hHge4]
  have hlowPow : X ^ (5 / 8 + ε / 2) ≤ H / 2 := by
    have hexp : (5 / 8 + ε / 2) + ε / 2 = 5 / 8 + ε := by ring
    have hratio : 1 ≤ X ^ (ε / 2) / 2 := by
      nlinarith [hXpow4]
    calc
      X ^ (5 / 8 + ε / 2) =
          X ^ (5 / 8 + ε / 2) * 1 := by ring
      _ ≤ X ^ (5 / 8 + ε / 2) * (X ^ (ε / 2) / 2) := by
          exact mul_le_mul_of_nonneg_left hratio
            (Real.rpow_nonneg hXnonneg _)
      _ = X ^ (5 / 8 + ε) / 2 := by
          rw [← mul_div_assoc, ← hexp,
            ← Real.rpow_add hXpos (5 / 8 + ε / 2) (ε / 2)]
      _ ≤ H / 2 := by nlinarith [hHlower]
  have hMlowPow : (M : ℝ) ^ (5 / 8 + ε / 2) ≤ (L : ℝ) := by
    have hexppos : 0 ≤ 5 / 8 + ε / 2 := by positivity
    calc
      (M : ℝ) ^ (5 / 8 + ε / 2) ≤ X ^ (5 / 8 + ε / 2) :=
        Real.rpow_le_rpow (Nat.cast_nonneg M) hMcast_le hexppos
      _ ≤ H / 2 := hlowPow
      _ ≤ (L : ℝ) := hLhalf
  have hlogUpperPow : (L : ℝ) ≤ (M : ℝ) ^ (1 - ε / 2) := by
    have hexpPos : 0 < 1 - ε := by linarith
    have hXle2M : X ≤ 2 * (M : ℝ) := by nlinarith [hMhalf]
    have hMpos : 0 < (M : ℝ) := by linarith [hMhalf, hXge4]
    have hXpow : X ^ (1 - ε) ≤ (2 * (M : ℝ)) ^ (1 - ε) :=
      Real.rpow_le_rpow hXpos.le hXle2M hexpPos.le
    have hfactor : (2 : ℝ) ^ (2 - ε) ≤ (M : ℝ) ^ (ε / 2) := by
      have hX₀div : integerToRealThreshold ε / 2 ≤ X / 2 := by
        exact div_le_div_of_nonneg_right hX₀ (by norm_num)
      have hMdiv : X / 2 ≤ (M : ℝ) := hMhalf
      have hthresholdPow :
          (integerToRealThreshold ε / 2) ^ (ε / 2) = 2 ^ (2 - ε / 2) := by
        dsimp [integerToRealThreshold]
        rw [Real.div_rpow (by positivity) (by norm_num) (ε / 2)]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hmul : (4 / ε) * (ε / 2) = 2 := by
          field_simp
          ring
        rw [hmul]
        rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2) 2 (ε / 2)]
      calc
        (2 : ℝ) ^ (2 - ε) ≤ 2 ^ (2 - ε / 2) := by
          exact Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
        _ = (integerToRealThreshold ε / 2) ^ (ε / 2) := hthresholdPow.symm
        _ ≤ (X / 2) ^ (ε / 2) :=
          Real.rpow_le_rpow (by positivity) hX₀div hεhalfpos.le
        _ ≤ (M : ℝ) ^ (ε / 2) :=
          Real.rpow_le_rpow (by positivity) hMdiv hεhalfpos.le
    have hMfactor :
        (2 : ℝ) ^ (2 - ε) * (M : ℝ) ^ (1 - ε) ≤
          (M : ℝ) ^ (1 - ε / 2) := by
      have hexp : (1 - ε) + ε / 2 = 1 - ε / 2 := by ring
      calc
        (2 : ℝ) ^ (2 - ε) * (M : ℝ) ^ (1 - ε) ≤
            (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (1 - ε) :=
          mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hMpos.le _)
        _ = (M : ℝ) ^ (1 - ε / 2) := by
          rw [← Real.rpow_add hMpos (ε / 2) (1 - ε), add_comm]
          congr 1
    calc
      (L : ℝ) ≤ 2 * H := hLdouble
      _ ≤ 2 * X ^ (1 - ε) := by nlinarith [hHupper]
      _ ≤ 2 * (2 * (M : ℝ)) ^ (1 - ε) :=
        mul_le_mul_of_nonneg_left hXpow (by norm_num)
      _ = (2 : ℝ) ^ (2 - ε) * (M : ℝ) ^ (1 - ε) := by
        rw [Real.mul_rpow (by norm_num) hMpos.le]
        calc
          2 * (2 ^ (1 - ε) * (M : ℝ) ^ (1 - ε)) =
              (2 * 2 ^ (1 - ε)) * (M : ℝ) ^ (1 - ε) := by ring
          _ = (2 ^ (1 : ℝ) * 2 ^ (1 - ε)) * (M : ℝ) ^ (1 - ε) := by
            rw [Real.rpow_one]
          _ = 2 ^ (1 + (1 - ε)) * (M : ℝ) ^ (1 - ε) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) 1 (1 - ε)]
          _ = 2 ^ (2 - ε) * (M : ℝ) ^ (1 - ε) := by
            rw [show (1 : ℝ) + (1 - ε) = 2 - ε by ring]
      _ ≤ (M : ℝ) ^ (1 - ε / 2) := hMfactor
  have hMintfloor : Int.floor X = (M : ℤ) := by
    dsimp [M]
    exact (Int.natCast_floor_eq_floor hXnonneg).symm
  have hfloorSum : M + L = Nat.floor (X + H) := by
    dsimp [L]
    exact Nat.add_sub_of_le hfloorMono
  have hEndIntfloor : Int.floor (X + H) = ((M + L : ℕ) : ℤ) := by
    rw [← Int.natCast_floor_eq_floor (le_of_lt (by linarith : 0 < X + H))]
    exact_mod_cast hfloorSum.symm
  have hinterval :
      FractionalPrimes.realIntegerInterval X H =
        Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ) := by
    rw [Polynomial.realIntegerInterval_eq_floor_Ioc, hMintfloor, hEndIntfloor]
  exact ⟨hMthree, hεhalfpos, by linarith, hMhalf, hMcast_le, hLhalf, hLdouble,
    hMlowPow, hlogUpperPow, hlogCompare, hinterval⟩

/-- The frozen exact `lc:model-difference` estimate applies at the larger
real-centre scale required by `lc:integer-to-real`; it controls only the
change from the real Cramér model to the floor-centred model. -/
theorem integerToRealCramerModelError {A ε X H : ℝ}
    (hA : 0 < A) (hε : 0 < ε) (hεtop : ε < 3 / 16)
    (hX₀ : integerToRealThreshold ε ≤ X)
    (hHlower : X ^ (5 / 8 + ε) ≤ H) :
    (∑ n ∈ FractionalPrimes.realIntegerInterval X H,
      |FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff X) n -
          FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff (Int.floor X)) n|) ≤
      Real.exp 13 * 2 ^ A *
        (8 * (10 * (A + 2 / 5) / Real.exp 1) ^ (10 * (A + 2 / 5)) +
          4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^ (A + 2 / 5)) *
        H * (Real.log X) ^ (-A : ℝ) := by
  have hexpLarge : 2 ≤ 4 / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [hεtop]
  have hX₀ge4 : 4 ≤ integerToRealThreshold ε := by
    dsimp [integerToRealThreshold]
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hexpLarge
    norm_num at h ⊢
    exact h
  have hXge4 : 4 ≤ X := hX₀ge4.trans hX₀
  have hXone : 1 ≤ X := by linarith
  have hscale : X ^ (5 / 8 : ℝ) ≤ X ^ (5 / 8 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
  exact Polynomial.paperCramerChangeCentre_realIntegerInterval_bound
    hA hXge4 (hscale.trans hHlower)

#print axioms integerToRealFloorParameterTransfer
#print axioms integerToRealCramerModelError

end FractionalPrimes.Literature.Centres

end
