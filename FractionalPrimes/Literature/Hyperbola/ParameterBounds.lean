module

public import FractionalPrimes.Literature.Hyperbola.DirichletApproximation
public import Mathlib.Order.Interval.Finset.Defs

set_option maxHeartbeats 800000

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

/-- The exact line-count budget `R_q=M^3/(X Q^2 q)`. -/
noncomputable def R_q (g : HyperbolaGeometricData) (q : ℕ) : ℝ :=
  g.M ^ 3 / (g.X * (g.Q : ℝ) ^ 2 * (q : ℝ))

/-- The exact point-count budget `S_q=H M^2/(X Q q)`. -/
noncomputable def S_q (g : HyperbolaGeometricData) (q : ℕ) : ℝ :=
  g.H * g.M ^ 2 / (g.X * (g.Q : ℝ) * (q : ℝ))

/-- The exact conclusions available from the admissible parameter range for
one denominator `q` with `1≤q≤Q`. -/
structure AdmissibleParameterBounds (g : HyperbolaGeometricData) (q : ℕ) : Prop where
  r_lower : (g.K₀ ^ 2)⁻¹ ≤ g.r
  L0_lower : 1 ≤ g.L0
  Q_le_M : (g.Q : ℝ) ≤ g.M
  Q_cube_le : (g.Q : ℝ) ^ 3 ≤ g.M ^ 3 / g.X
  Q_sqrt_le : (g.Q : ℝ) ≤ g.M * Real.sqrt (g.H / g.X)
  R_lower : 1 ≤ R_q g q
  S_lower : 1 ≤ S_q g q
  S_div_L0_eq_R : S_q g q / g.L0 = R_q g q
  H_three_halves_le_S : g.H ^ (3 / 2 : ℝ) / Real.sqrt g.X ≤ S_q g q
  qH_div_M_le_S : (q : ℝ) * g.H / g.M ≤ S_q g q
  sqrtH_M_div_q_sqrtX_le_S :
    Real.sqrt g.H * g.M / ((q : ℝ) * Real.sqrt g.X) ≤ S_q g q
  lattice_point_properties :
    ∀ p ∈ g.lattice,
      0 < p.1 ∧ 0 < p.2 ∧
      g.r / 4 < (p.2 : ℝ) / (p.1 : ℝ) ∧
      (p.2 : ℝ) / (p.1 : ℝ) ≤ 2 * g.r
  lattice_finite : g.lattice.Finite

/-- The admissible range gives all exact denominator budgets and the stated
positivity, slope, and finiteness conclusions for the hyperbola lattice set. -/
theorem admissibleParameterBounds (g : HyperbolaGeometricData) (q : ℕ)
    (hqlo : 1 ≤ q) (hqhi : q ≤ g.Q) : AdmissibleParameterBounds g q := by
  let Qr : ℝ := (g.Q : ℝ)
  let qr : ℝ := (q : ℝ)
  let T : ℝ := Real.sqrt (Real.sqrt (g.H * g.X))
  have hKpos : 0 < g.K₀ := by linarith [g.K₀_ge_one]
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have hMpos : 0 < g.M := by linarith [g.M_ge_one]
  have hKnonneg : 0 ≤ g.K₀ := hKpos.le
  have hXnonneg : 0 ≤ g.X := hXpos.le
  have hHnonneg : 0 ≤ g.H := hHpos.le
  have hMnonneg : 0 ≤ g.M := hMpos.le
  have hQpos : 0 < Qr := by dsimp [Qr]; exact_mod_cast g.Q_pos
  have hQnonneg : 0 ≤ Qr := hQpos.le
  have hqrpos : 0 < qr := by
    dsimp [qr]
    exact_mod_cast (show 0 < q by omega)
  have hqrnonneg : 0 ≤ qr := hqrpos.le
  have hqleQr : qr ≤ Qr := by dsimp [qr, Qr]; exact_mod_cast hqhi
  have hHXnonneg : 0 ≤ g.H * g.X := mul_nonneg hHnonneg hXnonneg
  have hHXpos : 0 < g.H * g.X := mul_pos hHpos hXpos
  have hTge1 : 1 ≤ T := by
    have hHXge1 : 1 ≤ g.H * g.X := by nlinarith [g.H_ge_one, g.X_ge_one]
    have hinner := Real.sqrt_le_sqrt hHXge1
    have houter := Real.sqrt_le_sqrt hinner
    simpa [T] using houter
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTge1
  have hTnonneg : 0 ≤ T := hTpos.le
  have hT2 : T ^ 2 = Real.sqrt (g.H * g.X) := by
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hrootHXpos : 0 < Real.sqrt (g.H * g.X) := Real.sqrt_pos.mpr hHXpos
  have hQupper : Qr ≤ g.M / T := by
    simpa [T] using g.Q_le_M_div_fourthRoot
  have hQT : Qr * T ≤ g.M := (le_div_iff₀ hTpos).mp hQupper
  have hMdivT : g.M / T ≤ g.M := by
    apply (div_le_iff₀ hTpos).2
    calc
      g.M = g.M * 1 := by ring
      _ ≤ g.M * T := mul_le_mul_of_nonneg_left hTge1 hMnonneg
  have hQleM : Qr ≤ g.M := hQupper.trans hMdivT

  let c : ℝ := Real.rpow g.X (1 / 3 : ℝ)
  have hcNonneg : 0 ≤ c := by
    dsimp [c]
    exact Real.rpow_nonneg hXnonneg _
  have hc3 : c ^ 3 = g.X := by
    dsimp [c]
    rw [← Real.rpow_mul_natCast hXnonneg (1 / 3 : ℝ) 3]
    norm_num
  have hc_le_H : c ≤ g.H := by simpa [c] using g.X_cuberoot_le_H
  have hHcube : g.X ≤ g.H ^ 3 := by
    calc
      g.X = c ^ 3 := hc3.symm
      _ ≤ g.H ^ 3 := pow_le_pow_left₀ hcNonneg hc_le_H 3
  have hrootc : Real.sqrt (Real.sqrt (c * g.X)) = c := by
    have hc4 : c * g.X = c ^ 4 := by rw [← hc3]; ring
    rw [hc4, show c ^ 4 = (c ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg c), Real.sqrt_sq hcNonneg]
  have hc_le_T : c ≤ T := by
    have hmul := mul_le_mul_of_nonneg_right hc_le_H hXnonneg
    have hroots := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hmul)
    rw [hrootc] at hroots
    simpa [T] using hroots
  have hT3geX : g.X ≤ T ^ 3 := by
    calc
      g.X = c ^ 3 := hc3.symm
      _ ≤ T ^ 3 := pow_le_pow_left₀ hcNonneg hc_le_T 3
  have hQTcube : (Qr * T) ^ 3 ≤ g.M ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hQnonneg hTnonneg) hQT 3
  have hQ3X : Qr ^ 3 * g.X ≤ g.M ^ 3 := by
    calc
      Qr ^ 3 * g.X ≤ Qr ^ 3 * T ^ 3 :=
        mul_le_mul_of_nonneg_left hT3geX (pow_nonneg hQnonneg _)
      _ = (Qr * T) ^ 3 := by ring
      _ ≤ g.M ^ 3 := hQTcube

  have hXleHsqrtHX : g.X ≤ g.H * Real.sqrt (g.H * g.X) := by
    have hmul := mul_le_mul_of_nonneg_right hHcube hXnonneg
    have hsq : g.X ^ 2 ≤
        (g.H * Real.sqrt (g.H * g.X)) ^ 2 := by
      calc
        g.X ^ 2 ≤ g.H ^ 3 * g.X := by simpa [pow_two] using hmul
        _ = (g.H * Real.sqrt (g.H * g.X)) ^ 2 := by
          calc
            g.H ^ 3 * g.X = g.H ^ 2 * (g.H * g.X) := by ring
            _ = g.H ^ 2 * (Real.sqrt (g.H * g.X)) ^ 2 :=
              congrArg (fun x : ℝ => g.H ^ 2 * x) (Real.sq_sqrt hHXnonneg).symm
            _ = (g.H * Real.sqrt (g.H * g.X)) ^ 2 := by ring
    exact (sq_le_sq₀ hXnonneg
      (mul_nonneg hHnonneg (Real.sqrt_nonneg _))).mp hsq
  have hInvT2 : (1 / T) ^ 2 = 1 / Real.sqrt (g.H * g.X) := by
    rw [div_pow, one_pow, hT2]
  have hInvLe : 1 / T ≤ Real.sqrt (g.H / g.X) := by
    have hdiv : 1 / Real.sqrt (g.H * g.X) ≤ g.H / g.X :=
      (div_le_div_iff₀ hrootHXpos hXpos).2 (by simpa using hXleHsqrtHX)
    have hsq : (1 / T) ^ 2 ≤ (Real.sqrt (g.H / g.X)) ^ 2 := by
      rw [hInvT2, Real.sq_sqrt (div_nonneg hHnonneg hXnonneg)]
      exact hdiv
    exact (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hsq
  have hQsqrt : Qr ≤ g.M * Real.sqrt (g.H / g.X) := by
    calc
      Qr ≤ g.M / T := hQupper
      _ = g.M * (1 / T) := by ring
      _ ≤ g.M * Real.sqrt (g.H / g.X) :=
        mul_le_mul_of_nonneg_left hInvLe hMnonneg

  have hM2 : g.M ^ 2 ≤ g.K₀ ^ 2 * g.X := by
    calc
      g.M ^ 2 ≤ (g.K₀ * Real.sqrt g.X) ^ 2 :=
        pow_le_pow_left₀ hMnonneg g.M_le_K₀_sqrtX 2
      _ = g.K₀ ^ 2 * g.X := by
        calc
          (g.K₀ * Real.sqrt g.X) ^ 2 = g.K₀ ^ 2 * (Real.sqrt g.X) ^ 2 := by ring
          _ = g.K₀ ^ 2 * g.X :=
            congrArg (fun x : ℝ => g.K₀ ^ 2 * x) (Real.sq_sqrt hXnonneg)
  have hRden : 0 < g.X * Qr ^ 2 * qr :=
    mul_pos (mul_pos hXpos (sq_pos_of_pos hQpos)) hqrpos
  have hRlower : 1 ≤ R_q g q := by
    rw [R_q]
    apply (le_div_iff₀ hRden).2
    calc
      (1 : ℝ) * (g.X * Qr ^ 2 * qr) ≤ g.X * Qr ^ 2 * Qr := by
        have hqq : Qr ^ 2 * qr ≤ Qr ^ 2 * Qr :=
          mul_le_mul_of_nonneg_left hqleQr (sq_nonneg Qr)
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hqq hXnonneg
      _ = Qr ^ 3 * g.X := by ring
      _ ≤ g.M ^ 3 := hQ3X
  have hQcube : Qr ^ 3 ≤ g.M ^ 3 / g.X :=
    (le_div_iff₀ hXpos).2 hQ3X

  have hSden : 0 < g.X * Qr * qr := by positivity
  have hT2roots : T ^ 2 = Real.sqrt g.H * Real.sqrt g.X := by
    rw [hT2, Real.sqrt_mul hHnonneg]
  have hQ2roots : Qr ^ 2 * Real.sqrt g.H * Real.sqrt g.X ≤ g.M ^ 2 := by
    calc
      Qr ^ 2 * Real.sqrt g.H * Real.sqrt g.X =
          Qr ^ 2 * (Real.sqrt g.H * Real.sqrt g.X) := by ring
      _ = Qr ^ 2 * T ^ 2 := by rw [← hT2roots]
      _ = (Qr * T) ^ 2 := by ring
      _ ≤ g.M ^ 2 := by
        have hpow := pow_le_pow_left₀ (mul_nonneg hQnonneg hTnonneg) hQT 2
        simpa [mul_pow] using hpow
  have hHpow : g.H ^ (3 / 2 : ℝ) = g.H * Real.sqrt g.H := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hHpos]
    simp [Real.rpow_one, Real.sqrt_eq_rpow]
  have hqQ : Qr * qr ≤ Qr ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hqleQr hQnonneg
  have hrootProductLe :
      Real.sqrt g.H * Real.sqrt g.X * (Qr * qr) ≤ g.M ^ 2 := by
    calc
      Real.sqrt g.H * Real.sqrt g.X * (Qr * qr) ≤
          Real.sqrt g.H * Real.sqrt g.X * Qr ^ 2 :=
        mul_le_mul_of_nonneg_left hqQ
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = Qr ^ 2 * Real.sqrt g.H * Real.sqrt g.X := by ring
      _ ≤ g.M ^ 2 := hQ2roots
  have hScross : g.H ^ (3 / 2 : ℝ) * (g.X * Qr * qr) ≤
      (g.H * g.M ^ 2) * Real.sqrt g.X := by
    rw [hHpow]
    have hsqrtX2 : (Real.sqrt g.X) ^ 2 = g.X := Real.sq_sqrt hXnonneg
    have hXprod : g.X * Qr * qr = (Real.sqrt g.X) ^ 2 * Qr * qr :=
      congrArg (fun x : ℝ => x * Qr * qr) hsqrtX2.symm
    calc
      g.H * Real.sqrt g.H * (g.X * Qr * qr) =
          g.H * Real.sqrt g.X *
            (Real.sqrt g.H * Real.sqrt g.X * (Qr * qr)) := by
        rw [hXprod]
        ring
      _ ≤ g.H * Real.sqrt g.X * g.M ^ 2 :=
        mul_le_mul_of_nonneg_left hrootProductLe
          (mul_nonneg hHnonneg (Real.sqrt_nonneg _))
      _ = (g.H * g.M ^ 2) * Real.sqrt g.X := by ring
  have hHpowGeSqrtX : Real.sqrt g.X ≤ g.H ^ (3 / 2 : ℝ) := by
    have hsqrtHcube : Real.sqrt (g.H ^ 3) = g.H * Real.sqrt g.H := by
      rw [show g.H ^ 3 = g.H ^ 2 * g.H by ring,
        Real.sqrt_mul (sq_nonneg g.H), Real.sqrt_sq hHnonneg]
    have h := Real.sqrt_le_sqrt hHcube
    rw [hsqrtHcube, ← hHpow] at h
    exact h
  have hHratio : 1 ≤ g.H ^ (3 / 2 : ℝ) / Real.sqrt g.X :=
    (le_div_iff₀ (Real.sqrt_pos.mpr hXpos)).2 (by simpa using hHpowGeSqrtX)
  have hSlower : 1 ≤ S_q g q := by
    exact hHratio.trans ((div_le_div_iff₀ (Real.sqrt_pos.mpr hXpos) hSden).2 hScross)

  have hq2leQ2 : qr ^ 2 ≤ Qr ^ 2 :=
    pow_le_pow_left₀ hqrnonneg hqleQr 2
  have hQq2 : g.X * Qr * qr ^ 2 ≤ g.M ^ 3 := by
    calc
      g.X * Qr * qr ^ 2 = g.X * (Qr * qr ^ 2) := by ring
      _ ≤ g.X * (Qr * Qr ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hq2leQ2 hQnonneg) hXnonneg
      _ = g.X * Qr ^ 3 := by ring
      _ = Qr ^ 3 * g.X := by ring
      _ ≤ g.M ^ 3 := hQ3X
  have hqHcross : (qr * g.H) * (g.X * Qr * qr) ≤
      (g.H * g.M ^ 2) * g.M := by
    calc
      (qr * g.H) * (g.X * Qr * qr) = g.H * (g.X * Qr * qr ^ 2) := by ring
      _ ≤ g.H * g.M ^ 3 := mul_le_mul_of_nonneg_left hQq2 hHnonneg
      _ = (g.H * g.M ^ 2) * g.M := by ring
  have hqHleS : qr * g.H / g.M ≤ S_q g q :=
    (div_le_div_iff₀ hMpos hSden).2 hqHcross

  have hQ2X : Qr ^ 2 * g.X ≤ g.M ^ 2 * g.H := by
    have hQ2T2 : Qr ^ 2 * T ^ 2 ≤ g.M ^ 2 := by
      have hpow := pow_le_pow_left₀ (mul_nonneg hQnonneg hTnonneg) hQT 2
      simpa [mul_pow] using hpow
    calc
      Qr ^ 2 * g.X ≤ Qr ^ 2 * (g.H * T ^ 2) := by
        rw [hT2]
        exact mul_le_mul_of_nonneg_left hXleHsqrtHX
          (sq_nonneg Qr)
      _ = g.H * (Qr ^ 2 * T ^ 2) := by ring
      _ ≤ g.M ^ 2 * g.H := by
        calc
          g.H * (Qr ^ 2 * T ^ 2) ≤ g.H * g.M ^ 2 :=
            mul_le_mul_of_nonneg_left hQ2T2 hHnonneg
          _ = g.M ^ 2 * g.H := by ring
  have hQsqrtHX : Qr * Real.sqrt g.X ≤ g.M * Real.sqrt g.H := by
    have hleftSq : (Qr * Real.sqrt g.X) ^ 2 = Qr ^ 2 * g.X := by
      calc
        (Qr * Real.sqrt g.X) ^ 2 = Qr ^ 2 * (Real.sqrt g.X) ^ 2 := by ring
        _ = Qr ^ 2 * g.X :=
          congrArg (fun x : ℝ => Qr ^ 2 * x) (Real.sq_sqrt hXnonneg)
    have hrightSq : (g.M * Real.sqrt g.H) ^ 2 = g.M ^ 2 * g.H := by
      calc
        (g.M * Real.sqrt g.H) ^ 2 = g.M ^ 2 * (Real.sqrt g.H) ^ 2 := by ring
        _ = g.M ^ 2 * g.H :=
          congrArg (fun x : ℝ => g.M ^ 2 * x) (Real.sq_sqrt hHnonneg)
    apply (sq_le_sq₀ (mul_nonneg hQnonneg (Real.sqrt_nonneg _))
      (mul_nonneg hMnonneg (Real.sqrt_nonneg _))).mp
    rw [hleftSq, hrightSq]
    exact hQ2X
  have hXQ : g.X * Qr ≤ g.M * Real.sqrt g.H * Real.sqrt g.X := by
    have hsqrtX2 : (Real.sqrt g.X) ^ 2 = g.X := Real.sq_sqrt hXnonneg
    have hXQr : g.X * Qr = (Real.sqrt g.X) ^ 2 * Qr :=
      congrArg (fun x : ℝ => x * Qr) hsqrtX2.symm
    calc
      g.X * Qr = Real.sqrt g.X * (Qr * Real.sqrt g.X) := by rw [hXQr]; ring
      _ ≤ Real.sqrt g.X * (g.M * Real.sqrt g.H) :=
        mul_le_mul_of_nonneg_left hQsqrtHX (Real.sqrt_nonneg _)
      _ = g.M * Real.sqrt g.H * Real.sqrt g.X := by ring
  have hLastCross : (Real.sqrt g.H * g.M) * (g.X * Qr * qr) ≤
      (g.H * g.M ^ 2) * (qr * Real.sqrt g.X) := by
    calc
      (Real.sqrt g.H * g.M) * (g.X * Qr * qr) =
          (qr * (Real.sqrt g.H * g.M)) * (g.X * Qr) := by ring
      _ ≤ (qr * (Real.sqrt g.H * g.M)) *
          (g.M * Real.sqrt g.H * Real.sqrt g.X) :=
        mul_le_mul_of_nonneg_left hXQ
          (mul_nonneg hqrnonneg (mul_nonneg (Real.sqrt_nonneg _) hMnonneg))
      _ = (g.H * g.M ^ 2) * (qr * Real.sqrt g.X) := by
        calc
          qr * (Real.sqrt g.H * g.M) * (g.M * Real.sqrt g.H * Real.sqrt g.X) =
              qr * g.M ^ 2 * (Real.sqrt g.H) ^ 2 * Real.sqrt g.X := by ring
          _ = (g.H * g.M ^ 2) * (qr * Real.sqrt g.X) := by
            rw [Real.sq_sqrt hHnonneg]
            ring
  have hqSqrtXpos : 0 < qr * Real.sqrt g.X :=
    mul_pos hqrpos (Real.sqrt_pos.mpr hXpos)
  have hlast :
      Real.sqrt g.H * g.M / (qr * Real.sqrt g.X) ≤ S_q g q :=
    (div_le_div_iff₀ hqSqrtXpos hSden).2 hLastCross

  have hr_lower : (g.K₀ ^ 2)⁻¹ ≤ g.r := by
    have hM2 : g.M ^ 2 ≤ g.K₀ ^ 2 * g.X := by
      calc
        g.M ^ 2 ≤ (g.K₀ * Real.sqrt g.X) ^ 2 :=
          pow_le_pow_left₀ hMnonneg g.M_le_K₀_sqrtX 2
        _ = g.K₀ ^ 2 * g.X := by
          calc
            (g.K₀ * Real.sqrt g.X) ^ 2 =
                g.K₀ ^ 2 * (Real.sqrt g.X) ^ 2 := by ring
            _ = g.K₀ ^ 2 * g.X :=
              congrArg (fun x : ℝ => g.K₀ ^ 2 * x) (Real.sq_sqrt hXnonneg)
    rw [inv_eq_one_div, HyperbolaGeometricData.r]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    simpa [mul_comm] using hM2
  have hL0_lower : 1 ≤ g.L0 := by
    have hMHQ : g.M ≤ g.H * Qr :=
      by simpa [Qr, mul_comm] using (div_le_iff₀ hHpos).mp g.M_div_H_le_Q
    rw [HyperbolaGeometricData.L0]
    apply (le_div_iff₀ hMpos).2
    simpa [mul_comm] using hMHQ

  have hcoords : ∀ p ∈ g.lattice,
      0 < p.1 ∧ 0 < p.2 ∧
      g.r / 4 < (p.2 : ℝ) / (p.1 : ℝ) ∧
      (p.2 : ℝ) / (p.1 : ℝ) ≤ 2 * g.r := by
    intro p hp
    rcases hp with ⟨hJ, hprodlo, hprodhi⟩
    have hmM := g.J_subset hJ
    have hmposR : 0 < (p.1 : ℝ) := lt_trans hMpos hmM.1
    have hmle : (p.1 : ℝ) ≤ 2 * g.M := hmM.2
    have hprodhi' : (p.1 : ℝ) * (p.2 : ℝ) ≤ 2 * g.X := by
      calc
        (p.1 : ℝ) * (p.2 : ℝ) ≤ g.X + g.H := hprodhi
      _ ≤ 2 * g.X := by nlinarith only [g.H_le_X]
    have hnposR : 0 < (p.2 : ℝ) := by
      by_contra hn
      have hn' : (p.2 : ℝ) ≤ 0 := le_of_not_gt hn
      have : (p.1 : ℝ) * (p.2 : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmposR.le hn'
      linarith [g.X_ge_one, hprodlo]
    have hmpow : (p.1 : ℝ) ^ 2 ≤ (2 * g.M) ^ 2 :=
      pow_le_pow_left₀ hmposR.le hmle 2
    have hMpow : g.M ^ 2 ≤ (p.1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hMnonneg (le_of_lt hmM.1) 2
    have hratioLo : g.r / 4 < (p.2 : ℝ) / (p.1 : ℝ) := by
      have hdenom : (p.1 : ℝ) ^ 2 ≤ 4 * g.M ^ 2 := by nlinarith only [hmpow]
      have hXoverM : g.X / (4 * g.M ^ 2) ≤ g.X / (p.1 : ℝ) ^ 2 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        exact mul_le_mul_of_nonneg_left hdenom hXnonneg
      have hXoverm : g.X / (p.1 : ℝ) ^ 2 <
          (p.2 : ℝ) / (p.1 : ℝ) := by
        apply (div_lt_div_iff₀ (by positivity) hmposR).2
        have hprodscaled := mul_lt_mul_of_pos_right hprodlo hmposR
        nlinarith only [hprodscaled]
      have hrquarter : g.r / 4 = g.X / (4 * g.M ^ 2) := by
        rw [HyperbolaGeometricData.r]
        field_simp
      rw [hrquarter]
      exact hXoverM.trans_lt hXoverm
    have hratioHi : (p.2 : ℝ) / (p.1 : ℝ) ≤ 2 * g.r := by
      have hratioM : (p.2 : ℝ) / (p.1 : ℝ) ≤
          (2 * g.X) / (p.1 : ℝ) ^ 2 := by
        apply (div_le_div_iff₀ hmposR (by positivity)).2
        have hmul := mul_le_mul_of_nonneg_right hprodhi' hmposR.le
        nlinarith only [hmul]
      have hMoverm : (2 * g.X) / (p.1 : ℝ) ^ 2 ≤
          (2 * g.X) / g.M ^ 2 :=
        (div_le_div_iff₀ (by positivity) (by positivity)).2 <| by
          exact mul_le_mul_of_nonneg_left hMpow (by positivity)
      have h2r : (2 * g.X) / g.M ^ 2 = 2 * g.r := by
        rw [HyperbolaGeometricData.r]
        ring
      exact hratioM.trans (hMoverm.trans_eq h2r)
    have hmposZ : 0 < p.1 := by exact_mod_cast hmposR
    have hnposZ : 0 < p.2 := by exact_mod_cast hnposR
    exact ⟨hmposZ, hnposZ, hratioLo, hratioHi⟩

  have hfinite : g.lattice.Finite := by
    let B : Set (ℤ × ℤ) :=
      Set.Icc (1 : ℤ) ⌊2 * g.M⌋ ×ˢ Set.Icc (1 : ℤ) ⌊2 * g.X / g.M⌋
    have hsubset : g.lattice ⊆ B := by
      intro p hp
      have hpoint := hcoords p hp
      rcases hp with ⟨hJ, hprodlo, hprodhi⟩
      have hmM := g.J_subset hJ
      have hmupper : (p.1 : ℝ) ≤ 2 * g.M := hmM.2
      have hprodupper : (p.1 : ℝ) * (p.2 : ℝ) ≤ 2 * g.X := by
        calc
          (p.1 : ℝ) * (p.2 : ℝ) ≤ g.X + g.H := hprodhi
          _ ≤ 2 * g.X := by nlinarith only [g.H_le_X]
      have hnposR : 0 < (p.2 : ℝ) := by exact_mod_cast hpoint.2.1
      have hnupper : (p.2 : ℝ) ≤ 2 * g.X / g.M := by
        apply (le_div_iff₀ hMpos).2
        calc
          (p.2 : ℝ) * g.M ≤ (p.2 : ℝ) * (p.1 : ℝ) :=
            mul_le_mul_of_nonneg_left (le_of_lt hmM.1) hnposR.le
          _ ≤ 2 * g.X := by simpa [mul_comm] using hprodupper
      have hmfloor : p.1 ≤ ⌊2 * g.M⌋ :=
        Int.le_floor.mpr (by exact_mod_cast hmupper)
      have hnfloor : p.2 ≤ ⌊2 * g.X / g.M⌋ :=
        Int.le_floor.mpr (by exact_mod_cast hnupper)
      change p ∈ Set.Icc (1 : ℤ) ⌊2 * g.M⌋ ×ˢ Set.Icc (1 : ℤ) ⌊2 * g.X / g.M⌋
      exact ⟨⟨by omega, hmfloor⟩, ⟨by omega, hnfloor⟩⟩
    have hBfinite : B.Finite := by
      dsimp [B]
      exact (Set.finite_Icc (1 : ℤ) ⌊2 * g.M⌋).prod
        (Set.finite_Icc (1 : ℤ) ⌊2 * g.X / g.M⌋)
    exact hBfinite.subset hsubset

  exact {
    r_lower := hr_lower
    L0_lower := hL0_lower
    Q_le_M := hQleM
    Q_cube_le := hQcube
    Q_sqrt_le := hQsqrt
    R_lower := hRlower
    S_lower := hSlower
    S_div_L0_eq_R := by
      rw [R_q, S_q, HyperbolaGeometricData.L0]
      field_simp
    H_three_halves_le_S :=
      (div_le_div_iff₀ (Real.sqrt_pos.mpr hXpos) hSden).2 hScross
    qH_div_M_le_S := hqHleS
    sqrtH_M_div_q_sqrtX_le_S := hlast
    lattice_point_properties := hcoords
    lattice_finite := hfinite
  }

end FractionalPrimes.Literature.Hyperbola
