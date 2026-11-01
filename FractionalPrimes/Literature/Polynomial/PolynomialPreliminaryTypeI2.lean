module

public import FractionalPrimes.Literature.Polynomial.PolynomialHyperbolaCount
public import FractionalPrimes.Literature.Polynomial.PolynomialTypeIInverse
public import FractionalPrimes.Literature.Polynomial.PolynomialTypeI2Budgets
public import FractionalPrimes.Literature.Polynomial.PolynomialTypeI2SmallScale
public import FractionalPrimes.Literature.Polynomial.PolynomialWeightCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open _root_.Polynomial

private theorem preliminary_natPolynomialEval_nonneg
    (p : Polynomial ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add]
      exact add_nonneg hp hq
  | monomial n a =>
      rw [Polynomial.eval₂_monomial]
      exact mul_nonneg (Nat.cast_nonneg a) (pow_nonneg hx n)

private theorem preliminary_rpow_one_third_cube (X : ℝ) (hX : 0 ≤ X) :
    (Real.rpow X (1 / 3 : ℝ)) ^ 3 = X := by
  have hnat : (Real.rpow X (1 / 3 : ℝ)) ^ 3 =
      Real.rpow (Real.rpow X (1 / 3 : ℝ)) (3 : ℝ) :=
    (Real.rpow_natCast (Real.rpow X (1 / 3 : ℝ)) 3).symm
  have hrpow : Real.rpow (Real.rpow X (1 / 3 : ℝ)) (3 : ℝ) = X := by
    simpa [show (1 / 3 : ℝ)⁻¹ = 3 by norm_num] using
      (Real.rpow_rpow_inv hX (by norm_num : (1 / 3 : ℝ) ≠ 0))
  rw [hnat, hrpow]

private theorem preliminary_exists_int_modEq_nat_residue
    (q : ℕ) (hq : 0 < q) (x : ℤ) :
    ∃ a ∈ Finset.range q, x ≡ (a : ℤ) [ZMOD (q : ℤ)] := by
  let a : ℕ := (x % (q : ℤ)).toNat
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  have hrem0 : 0 ≤ x % (q : ℤ) := Int.emod_nonneg _ hqZ.ne'
  have hremLt : x % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hqZ
  have hcast : (a : ℤ) = x % (q : ℤ) := Int.toNat_of_nonneg hrem0
  have haLtZ : (a : ℤ) < (q : ℤ) := by simpa [hcast] using hremLt
  have haLt : a < q := by exact_mod_cast haLtZ
  have hmod : x ≡ (a : ℤ) [ZMOD (q : ℤ)] := by
    change x % (q : ℤ) = (a : ℤ) % (q : ℤ)
    rw [hcast]
    simp
  exact ⟨a, Finset.mem_range.mpr haLt, hmod⟩

/-- The inhomogeneous residue variation includes the pointwise supremum term,
so it controls each value of a positive-integer weight. -/
theorem preliminary_residueVariation_controls_value
    (β : ComplexPositiveIntegerFunction) (q : ℕ) (hq : 0 < q)
    (δ : ℝ) (hδ : 0 < δ)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹)) (n : PositiveInteger) :
    ‖β n‖ ≤ δ⁻¹ := by
  classical
  obtain ⟨a, ha, hmod⟩ :=
    preliminary_exists_int_modEq_nat_residue q hq (n.1 : ℤ)
  let P : Set ℤ := {z : ℤ | 0 < z} ∩ integerResidueClass q a
  have hnP : (n.1 : ℤ) ∈ P := by
    refine ⟨by change 0 < (n.1 : ℤ); exact_mod_cast n.2, ?_⟩
    change ∃ k : ℤ, (n.1 : ℤ) = (a : ℤ) + (q : ℤ) * k
    exact Int.modEq_iff_add_fac.mp hmod.symm
  let F : Finset ℤ := {((n.1 : ℕ) : ℤ)}
  have hFsubset : ∀ z ∈ F, z ∈ P := by
    intro z hz
    have hzEq : z = (n.1 : ℤ) := by simpa [F] using hz
    simpa [hzEq] using hnP
  have hpoint :
      ENNReal.ofReal
          (finiteOrderedTotalVariation F
            (complexPositiveIntegerZeroExtension β)) ≤
        orderedTotalVariation P (complexPositiveIntegerZeroExtension β) := by
    unfold orderedTotalVariation
    let F' : {F : Finset ℤ // ∀ z ∈ F, z ∈ P} := ⟨F, hFsubset⟩
    exact le_iSup_of_le F' le_rfl
  have hsingle : finiteOrderedTotalVariation F
      (complexPositiveIntegerZeroExtension β) = ‖β n‖ := by
    change finiteOrderedTotalVariation ({(n.1 : ℤ)} : Finset ℤ)
      (complexPositiveIntegerZeroExtension β) = ‖β n‖
    simp [finiteOrderedTotalVariation, listSupNorm, listAdjacentVariation,
      List.consecutivePairs, complexPositiveIntegerZeroExtension_natCast]
  have hterm : orderedTotalVariation P
      (complexPositiveIntegerZeroExtension β) ≤
        complexPositiveIntegerResidueVariation β q hq := by
    unfold complexPositiveIntegerResidueVariation
      positiveIntegerResidueTotalVariation residueClassTotalVariation
    change orderedTotalVariation
        ({z : ℤ | 0 < z} ∩ integerResidueClass q a)
        (complexPositiveIntegerZeroExtension β) ≤
      ∑ b ∈ Finset.range q,
        orderedTotalVariation
          ({z : ℤ | 0 < z} ∩ integerResidueClass q b)
          (complexPositiveIntegerZeroExtension β)
    exact Finset.single_le_sum
      (f := fun b : ℕ => orderedTotalVariation
        ({z : ℤ | 0 < z} ∩ integerResidueClass q b)
        (complexPositiveIntegerZeroExtension β))
      (fun b hb => by positivity) ha
  have hpointTV : ENNReal.ofReal ‖β n‖ ≤ ENNReal.ofReal (δ⁻¹) := by
    simpa [hsingle] using hpoint.trans (hterm.trans hTV)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ δ⁻¹)).mp hpointTV

/-- The interval-truncated first weight has the exact second-moment bound
needed to enter the Type-I inverse theorem. -/
private theorem preliminary_intervalWeight_secondMoment
    (J : Set ℝ) (β : ComplexPositiveIntegerFunction)
    (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ) (hδlt1 : δ < 1)
    (hTV : complexPositiveIntegerResidueVariation β q hq ≤
      ENNReal.ofReal (δ⁻¹)) :
    complexPositiveSecondMomentBound (δ ^ 2)
      (intervalWeightRestriction J β) := by
  intro B hB
  have hbeta := preliminary_residueVariation_controls_value β q hq δ hδ hTV
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 (Nat.floor B)) :
      complexPositiveSecondMomentSummand
          (intervalWeightRestriction J β) k ≤ δ⁻¹ ^ 2 := by
    have hkpos : 0 < k := by
      have := (Finset.mem_Icc.mp hk).1
      omega
    rw [complexPositiveSecondMomentSummand, dif_pos hkpos]
    by_cases hmem : (k : ℝ) ∈ J
    · simp only [intervalWeightRestriction, hmem]
      have hn' : ‖β ⟨k, hkpos⟩‖ ≤ δ⁻¹ := hbeta ⟨k, hkpos⟩
      exact (sq_le_sq₀ (norm_nonneg _) (inv_nonneg.mpr hδ.le)).2 hn'
    · simp [intervalWeightRestriction, hmem]
      positivity
  have hsum : complexPositiveSecondMoment
      (intervalWeightRestriction J β) B ≤
        (Nat.floor B : ℝ) * δ⁻¹ ^ 2 := by
    unfold complexPositiveSecondMoment
    calc
      (∑ k ∈ Finset.Icc 1 (Nat.floor B),
          complexPositiveSecondMomentSummand
            (intervalWeightRestriction J β) k) ≤
        ∑ k ∈ Finset.Icc 1 (Nat.floor B), δ⁻¹ ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k hk
      _ = (Nat.floor B : ℝ) * δ⁻¹ ^ 2 := by
          have hfloor : 1 ≤ Nat.floor B := by
            apply Nat.le_floor
            exact_mod_cast hB
          simp [Finset.sum_const, Nat.card_Icc, hfloor, nsmul_eq_mul]
  have hfloor : (Nat.floor B : ℝ) ≤ B := by
    exact Nat.floor_le (by linarith)
  calc
    complexPositiveSecondMoment (intervalWeightRestriction J β) B ≤
        (Nat.floor B : ℝ) * δ⁻¹ ^ 2 := hsum
    _ ≤ B * δ⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right hfloor (sq_nonneg _)
    _ = (δ ^ 2)⁻¹ * B := by
      rw [show (δ ^ 2)⁻¹ = δ⁻¹ ^ 2 by field_simp [ne_of_gt hδ]]
      ring

/-- The exact small-M Type-I data from the approved preliminary Type-I₂
argument, before applying the inverse theorem. -/
theorem preliminaryTypeI2IntervalWeightTypeI
    (M δ : ℝ) (J : Set ℝ) (hJ : J ⊆ Set.Ioc M (2 * M))
    (hM : (1 / 2 : ℝ) ≤ M)
    (hδ : 0 < δ) (hδlt1 : δ < 1)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (hqbound : (q₀ : ℝ) ≤ δ⁻¹)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q₀ hq₀ ≤
      ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q₀ hq₀ ≤
      ENNReal.ofReal (δ⁻¹)) :
    typeIFunction (δ ^ 2) (2 * M)
      (complexPositiveDirichletConvolution
        (intervalWeightRestriction J β₁) β₂) := by
  have hδsqpos : 0 < δ ^ 2 := pow_pos hδ 2
  have hδsq_lt1 : δ ^ 2 < 1 := by nlinarith
  have hA : 1 ≤ 2 * M := by linarith
  have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have hδinv_gt1 : 1 < δ⁻¹ := (one_lt_inv₀ hδ).2 hδlt1
  have hinvle : δ⁻¹ ≤ (δ ^ 2)⁻¹ := by
    rw [show (δ ^ 2)⁻¹ = (δ⁻¹) ^ 2 by field_simp [ne_of_gt hδ]]
    nlinarith
  have hqbound' : (q₀ : ℝ) ≤ (δ ^ 2)⁻¹ := hqbound.trans hinvle
  have hTV₂' : complexPositiveIntegerResidueVariation β₂ q₀ hq₀ ≤
      ENNReal.ofReal ((δ ^ 2)⁻¹) :=
    hTV₂.trans (ENNReal.ofReal_le_ofReal hinvle)
  refine ⟨hδsqpos, hδsq_lt1, hA, ?_⟩
  refine ⟨intervalWeightRestriction J β₁, β₂, q₀, hq₀, rfl, ?_, ?_, ?_, ?_, hTV₂'⟩
  · intro n hn
    dsimp [intervalWeightRestriction] at hn
    by_cases hmem : (n.1 : ℝ) ∈ J
    · simp only [hmem] at hn
      have hJmem := hJ hmem
      exact ⟨by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr n.2.ne'), hJmem.2⟩
    · simp [hmem] at hn
  · exact preliminary_intervalWeight_secondMoment J β₁ q₀ hq₀ δ hδ hδlt1 hTV₁
  · exact_mod_cast hq₀
  · exact hqbound'

/-- Expand one positive-index convolution phase term into its divisor sum. -/
private theorem preliminary_phaseTerm_convolution
    (α β : ComplexPositiveIntegerFunction) (P : Polynomial ℝ) (n : ℕ)
    (hn : 0 < n) :
    complexPositivePhaseTerm (complexPositiveDirichletConvolution α β) P n =
      ∑ d ∈ n.divisors,
        complexPositiveIntegerNatExtension α d *
          complexPositiveIntegerNatExtension β (n / d) *
          unitFrequencyPhase (P.eval (n : ℝ)) := by
  rw [complexPositivePhaseTerm, dif_pos hn,
    complexPositiveDirichletConvolution_eq_divisor_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [complexDivisorConvolutionSummand_of_mem _ _ _ _ hd]
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hquot : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)) hdpos
  simp [complexPositiveIntegerNatExtension, hdpos, hquot]

/-- In the large-M regime, the exact floor parameter from the approved
proof gives admissible K₀=2 hyperbola data. The fourth-root size hypotheses
are kept explicit so this setup is reusable before the ordinary weighted
pigeonhole step. -/
theorem preliminaryTypeI2LargeMGeometricData
    (X H M : ℝ) (J : Set ℝ)
    (hX : 1 ≤ X) (hH : 1 ≤ H)
    (hroot : Real.rpow X (1 / 3 : ℝ) ≤ H)
    (hHupper : H ≤ X)
    (hMupper : M ≤ 2 * Real.sqrt X)
    (hJconvex : Set.OrdConnected J)
    (hJsubset : J ⊆ Set.Ioc M (2 * M))
    (hMlarge : 2 * Real.sqrt (Real.sqrt (H * X)) ≤ M)
    (hHfourth : 2 * Real.sqrt (Real.sqrt (H * X)) ≤ H) :
    ∃ g : Hyperbola.geometricData,
      g.K₀ = 2 ∧ g.X = X ∧ g.H = H ∧ g.M = M ∧ g.J = J ∧
        g.Q = Nat.floor (M / Real.sqrt (Real.sqrt (H * X))) := by
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < H := by linarith
  have hHXone : 1 ≤ H * X := by nlinarith [mul_le_mul hH hX (by norm_num) (by linarith)]
  have hsqrtHXone : 1 ≤ Real.sqrt (H * X) := by
    have h := Real.sqrt_le_sqrt hHXone
    simpa using h
  have hDfourthone : 1 ≤ Real.sqrt (Real.sqrt (H * X)) := by
    have h := Real.sqrt_le_sqrt hsqrtHXone
    simpa using h
  have hDpos : 0 < Real.sqrt (Real.sqrt (H * X)) := by
    linarith
  have hMone : 1 ≤ M := by nlinarith [hMlarge, hDfourthone]
  have hMpos : 0 < M := by linarith
  let Q : ℕ := Nat.floor (M / Real.sqrt (Real.sqrt (H * X)))
  have hratio0 : 0 ≤ M / Real.sqrt (Real.sqrt (H * X)) :=
    div_nonneg hMpos.le hDpos.le
  have hratio2 : 2 ≤ M / Real.sqrt (Real.sqrt (H * X)) := by
    apply (le_div_iff₀ hDpos).2
    simpa using hMlarge
  have hQtwo : 2 ≤ Q := by
    dsimp [Q]
    exact Nat.le_floor hratio2
  have hQupper : (Q : ℝ) ≤ M / Real.sqrt (Real.sqrt (H * X)) := by
    dsimp [Q]
    exact Nat.floor_le hratio0
  have hfloorlt : M / Real.sqrt (Real.sqrt (H * X)) < (Q : ℝ) + 1 := by
    dsimp [Q]
    exact Nat.lt_floor_add_one _
  have hhalf_le_Q :
      (M / Real.sqrt (Real.sqrt (H * X))) / 2 ≤ (Q : ℝ) := by
    nlinarith [hratio2, hfloorlt]
  have htwoDpos : 0 < 2 * Real.sqrt (Real.sqrt (H * X)) := by positivity
  have hMQhalf : M / H ≤ M / (2 * Real.sqrt (Real.sqrt (H * X))):= by
    apply (div_le_div_iff₀ hHpos htwoDpos).2
    nlinarith [hHfourth, hMpos]
  have hMQleQ : M / H ≤ (Q : ℝ) := by
    calc
      M / H ≤ M / (2 * Real.sqrt (Real.sqrt (H * X))) := hMQhalf
      _ = (M / Real.sqrt (Real.sqrt (H * X))) / 2 := by
        field_simp [ne_of_gt hDpos]
      _ ≤ (Q : ℝ) := hhalf_le_Q
  let g : Hyperbola.geometricData :=
    { K₀ := 2
      X := X
      H := H
      M := M
      Q := Q
      J := J
      K₀_ge_one := by norm_num
      X_ge_one := hX
      H_ge_one := hH
      M_ge_one := hMone
      Q_pos := by omega
      J_orderConvex := hJconvex
      J_subset := hJsubset
      X_cuberoot_le_H := hroot
      H_le_X := hHupper
      M_le_K₀_sqrtX := by simpa using hMupper
      M_div_H_le_Q := hMQleQ
      Q_le_M_div_fourthRoot := by simpa [Q] using hQupper }
  exact ⟨g, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The exact integer-pair sum on a finite representative of the hyperbola
lattice is the Type-I correlation of the interval-restricted convolution.
The phase is constrained only on the lattice, matching the direct finite-sum
form used by the ordinary weighted pigeonhole argument. -/
theorem preliminaryTypeI2_intervalWeight_latticeSum
    (X H M : ℝ) (J : Set ℝ)
    (hX : 0 < X) (hM : (1 / 2 : ℝ) ≤ M)
    (hJ : J ⊆ Set.Ioc M (2 * M))
    (Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) =
      Hyperbola.hyperbolaLatticeSet X H J)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (P : Polynomial ℝ) (f : ℤ × ℤ → ℂ)
    (hphase : ∀ p, p ∈ Λ →
      f p = unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))) :
    typeIScalarPhaseSum
        (complexPositiveDirichletConvolution
          (intervalWeightRestriction J β₁) β₂) P X H =
      ∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension β₂ p.2 * f p := by
  classical
  let s : Finset (Σ n : ℕ, ℕ) :=
    (typeIIntervalSet X H).sigma fun n => n.divisors
  let S : Finset (Σ n : ℕ, ℕ) :=
    s.filter fun x => (x.2 : ℝ) ∈ J
  let g : ℕ → ℕ → ℂ := fun n d =>
    complexPositiveIntegerNatExtension (intervalWeightRestriction J β₁) d *
      complexPositiveIntegerNatExtension β₂ (n / d) *
      unitFrequencyPhase (P.eval (n : ℝ))
  let forward : (Σ n : ℕ, ℕ) → ℤ × ℤ := fun x =>
    ((x.2 : ℤ), ((x.1 / x.2 : ℕ) : ℤ))
  let inverse : (ℤ × ℤ) → (Σ n : ℕ, ℕ) := fun p =>
    ⟨p.1.toNat * p.2.toNat, p.1.toNat⟩
  have hsum : typeIScalarPhaseSum
      (complexPositiveDirichletConvolution
        (intervalWeightRestriction J β₁) β₂) P X H =
      ∑ x ∈ S, g x.1 x.2 := by
    unfold typeIScalarPhaseSum
    calc
      (∑ n ∈ typeIIntervalSet X H,
          complexPositivePhaseTerm
            (complexPositiveDirichletConvolution
              (intervalWeightRestriction J β₁) β₂) P n) =
        ∑ n ∈ typeIIntervalSet X H, ∑ d ∈ n.divisors, g n d := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnpos : 0 < n := by
            have hnmem := (mem_typeIIntervalSet X H n).1 hn
            omega
          exact preliminary_phaseTerm_convolution
            (intervalWeightRestriction J β₁) β₂ P n hnpos
      _ = ∑ x ∈ s, g x.1 x.2 := by
          simpa [s, g] using
            (Finset.sum_sigma' (typeIIntervalSet X H)
              (fun n => n.divisors) (fun n d => g n d))
      _ = ∑ x ∈ S, g x.1 x.2 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxJ : (x.2 : ℝ) ∈ J
          · simp [S, hxJ]
          · simp [S, g, hxJ, complexPositiveIntegerNatExtension,
              intervalWeightRestriction]
  have hforward (x : Σ n : ℕ, ℕ) (hx : x ∈ S) :
      forward x ∈ Λ := by
    rcases Finset.mem_filter.mp hx with ⟨hxS, hxJ⟩
    rcases Finset.mem_sigma.mp (show x ∈ s from hxS) with ⟨hn, hd⟩
    have hdpos : 0 < x.2 := Nat.pos_of_mem_divisors hd
    have hdiv : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hd
    have hquotpos : 0 < x.1 / x.2 :=
      Nat.div_pos (Nat.le_of_dvd (by
        have hnmem := (mem_typeIIntervalSet X H x.1).1 hn
        omega) hdiv) hdpos
    have hprod : x.2 * (x.1 / x.2) = x.1 := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
    have hprodReal :
        ((x.2 : ℤ) : ℝ) * (((x.1 / x.2 : ℕ) : ℤ) : ℝ) =
          (x.1 : ℝ) := by
      exact_mod_cast hprod
    have hband := (mem_typeIIntervalSet X H x.1).1 hn
    have hsource : forward x ∈ Hyperbola.hyperbolaLatticeSet X H J := by
      change ((forward x).1 : ℝ) ∈ J ∧
        X < ((forward x).1 : ℝ) * ((forward x).2 : ℝ) ∧
          ((forward x).1 : ℝ) * ((forward x).2 : ℝ) ≤ X + H
      refine ⟨?_, ?_, ?_⟩
      · exact_mod_cast hxJ
      · rw [hprodReal]
        exact hband.2.1
      · rw [hprodReal]
        exact hband.2.2
    change forward x ∈ (Λ : Set (ℤ × ℤ))
    rw [hΛ]
    exact hsource
  have hinverse (p : ℤ × ℤ) (hp : p ∈ Λ) : inverse p ∈ S := by
    have hsource : p ∈ Hyperbola.hyperbolaLatticeSet X H J := by
      change p ∈ (Λ : Set (ℤ × ℤ)) at hp
      rw [hΛ] at hp
      exact hp
    have hprops := hsource
    change (p.1 : ℝ) ∈ J ∧
      X < (p.1 : ℝ) * (p.2 : ℝ) ∧
        (p.1 : ℝ) * (p.2 : ℝ) ≤ X + H at hprops
    have hJreal : (p.1 : ℝ) ∈ Set.Ioc M (2 * M) := hJ hprops.1
    have hp1real : 0 < (p.1 : ℝ) := by linarith [hM, hJreal.1]
    have hp1 : 0 < p.1 := by exact_mod_cast hp1real
    have hp1nat : 0 < p.1.toNat := by
      have hnatcast : (p.1.toNat : ℤ) = p.1 :=
        Int.toNat_of_nonneg hp1.le
      have hnatpos : 0 < (p.1.toNat : ℤ) := by rw [hnatcast]; exact hp1
      exact_mod_cast hnatpos
    have hprodpos : 0 < (p.1 : ℝ) * (p.2 : ℝ) :=
      lt_trans hX hprops.2.1
    have hp2real : 0 < (p.2 : ℝ) := by
      by_contra hnot
      have hp2le : (p.2 : ℝ) ≤ 0 := le_of_not_gt hnot
      have hprodle : (p.1 : ℝ) * (p.2 : ℝ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp1real.le hp2le
      linarith
    have hp2 : 0 < p.2 := by exact_mod_cast hp2real
    have hp2nat : 0 < p.2.toNat := by
      have hnatcast : (p.2.toNat : ℤ) = p.2 :=
        Int.toNat_of_nonneg hp2.le
      have hnatpos : 0 < (p.2.toNat : ℤ) := by rw [hnatcast]; exact hp2
      exact_mod_cast hnatpos
    have hp1cast : (p.1.toNat : ℝ) = (p.1 : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hp1.le)
    have hp2cast : (p.2.toNat : ℝ) = (p.2 : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hp2.le)
    have hprodcast :
        ((p.1.toNat * p.2.toNat : ℕ) : ℝ) =
          (p.1 : ℝ) * (p.2 : ℝ) := by
      rw [Nat.cast_mul, hp1cast, hp2cast]
    have hnmem : p.1.toNat * p.2.toNat ∈
        typeIIntervalSet X H := by
      apply (mem_typeIIntervalSet X H _).2
      refine ⟨Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero hp1nat.ne' hp2nat.ne'), ?_, ?_⟩
      · rw [hprodcast]
        exact hprops.2.1
      · rw [hprodcast]
        exact hprops.2.2
    have hdmem : p.1.toNat ∈
        (p.1.toNat * p.2.toNat).divisors :=
      Nat.mem_divisors.mpr ⟨dvd_mul_right _ _,
        (Nat.mul_pos hp1nat hp2nat).ne'⟩
    have hfirst : inverse p ∈ s := by
      apply Finset.mem_sigma.mpr
      exact ⟨hnmem, hdmem⟩
    apply Finset.mem_filter.mpr
    refine ⟨hfirst, ?_⟩
    exact hp1cast ▸ hprops.1
  rw [hsum]
  apply Finset.sum_bij'
    (fun x _ => forward x)
    (fun p _ => inverse p)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact hforward x hx
  · intro p hp
    exact hinverse p hp
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxS, _⟩
    rcases Finset.mem_sigma.mp (show x ∈ s from hxS) with ⟨_, hd⟩
    have hdiv : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hd
    have hprod : x.2 * (x.1 / x.2) = x.1 := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
    apply Sigma.ext
    · change x.2 * (((x.1 : ℤ) / (x.2 : ℤ)).toNat) = x.1
      rw [← Int.natCast_div]
      simp
      exact hprod
    · rfl
  · intro p hp
    have hsource : p ∈ Hyperbola.hyperbolaLatticeSet X H J := by
      change p ∈ (Λ : Set (ℤ × ℤ)) at hp
      rw [hΛ] at hp
      exact hp
    have hprops := hsource
    change (p.1 : ℝ) ∈ J ∧
      X < (p.1 : ℝ) * (p.2 : ℝ) ∧
        (p.1 : ℝ) * (p.2 : ℝ) ≤ X + H at hprops
    have hJreal := hJ hprops.1
    have hp1real : 0 < (p.1 : ℝ) := by linarith [hM, hJreal.1]
    have hp1 : 0 < p.1 := by exact_mod_cast hp1real
    have hp1nat : 0 < p.1.toNat := by
      have hnatcast : (p.1.toNat : ℤ) = p.1 :=
        Int.toNat_of_nonneg hp1.le
      have hnatpos : 0 < (p.1.toNat : ℤ) := by rw [hnatcast]; exact hp1
      exact_mod_cast hnatpos
    have hp2real : 0 < (p.2 : ℝ) := by
      have hprodpos : 0 < (p.1 : ℝ) * (p.2 : ℝ) :=
        lt_trans hX hprops.2.1
      by_contra hnot
      have hp2le : (p.2 : ℝ) ≤ 0 := le_of_not_gt hnot
      have hprodle : (p.1 : ℝ) * (p.2 : ℝ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp1real.le hp2le
      linarith
    have hp2 : 0 < p.2 := by exact_mod_cast hp2real
    have hp2nat : 0 < p.2.toNat := by
      have hnatcast : (p.2.toNat : ℤ) = p.2 :=
        Int.toNat_of_nonneg hp2.le
      have hnatpos : 0 < (p.2.toNat : ℤ) := by rw [hnatcast]; exact hp2
      exact_mod_cast hnatpos
    have hnatdiv : p.1.toNat * p.2.toNat / p.1.toNat = p.2.toNat := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_left _ hp1nat
    apply Prod.ext
    · change (p.1.toNat : ℤ) = p.1
      exact Int.toNat_of_nonneg hp1.le
    · change ((p.1.toNat * p.2.toNat / p.1.toNat : ℕ) : ℤ) = p.2
      rw [hnatdiv]
      exact Int.toNat_of_nonneg hp2.le
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxS, hxJ⟩
    rcases Finset.mem_sigma.mp (show x ∈ s from hxS) with ⟨hn, hd⟩
    have hdpos : 0 < x.2 := Nat.pos_of_mem_divisors hd
    have hquotpos : 0 < x.1 / x.2 := by
      have hdiv : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hd
      have hnpos : 0 < x.1 := by
        have hnmem := (mem_typeIIntervalSet X H x.1).1 hn
        omega
      exact Nat.div_pos (Nat.le_of_dvd hnpos (Nat.dvd_of_mem_divisors hd)) hdpos
    have hmemΛ := hforward x hx
    have heq :
        complexPositiveIntegerNatExtension
            (intervalWeightRestriction J β₁) x.2 *
          complexPositiveIntegerNatExtension β₂ (x.1 / x.2) *
          unitFrequencyPhase (P.eval (x.1 : ℝ)) =
        complexPositiveIntegerZeroExtension β₁ (forward x).1 *
          complexPositiveIntegerZeroExtension β₂ (forward x).2 * f (forward x) := by
      have hphase' := hphase (forward x) hmemΛ
      have halpha :
          complexPositiveIntegerNatExtension
            (intervalWeightRestriction J β₁) x.2 =
          complexPositiveIntegerZeroExtension β₁ (x.2 : ℤ) := by
        rw [complexPositiveIntegerNatExtension, dif_pos hdpos]
        simp only [intervalWeightRestriction, hxJ]
        exact (complexPositiveIntegerZeroExtension_natCast
          β₁ ⟨x.2, hdpos⟩).symm
      have hbeta :
          complexPositiveIntegerNatExtension β₂ (x.1 / x.2) =
          complexPositiveIntegerZeroExtension β₂ ((x.1 / x.2 : ℕ) : ℤ) := by
        rw [complexPositiveIntegerNatExtension, dif_pos hquotpos]
        exact (complexPositiveIntegerZeroExtension_natCast
          β₂ ⟨x.1 / x.2, hquotpos⟩).symm
      have hprodReal :
          ((forward x).1 : ℝ) * ((forward x).2 : ℝ) = (x.1 : ℝ) := by
        have hprod : x.2 * (x.1 / x.2) = x.1 := by
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
        change ((x.2 : ℤ) : ℝ) *
          (((x.1 / x.2 : ℕ) : ℤ) : ℝ) = (x.1 : ℝ)
        exact_mod_cast hprod
      have hphaseEq :
          unitFrequencyPhase (P.eval (x.1 : ℝ)) = f (forward x) := by
        calc
          unitFrequencyPhase (P.eval (x.1 : ℝ)) =
              unitFrequencyPhase
                (P.eval (((forward x).1 : ℝ) * ((forward x).2 : ℝ))) := by
                  rw [hprodReal]
          _ = f (forward x) := hphase'.symm
      rw [halpha, hbeta, hphaseEq]
    exact heq

/-- The approved `J_d` budget dominates sixteen times the square of the
Type-I inverse budget at the squared input. -/
theorem typeI2J_dominates_squared_typeI_budget
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : 2 ≤ x) :
    16 * (inverseBoundI d (x ^ 2)) ^ 2 ≤ typeI2J d x := by
  rw [typeI2J_eval]
  have hI : 4 ≤ inverseBoundI d (x ^ 2) := by
    apply inverseBoundI_ge_four d hd
    nlinarith
  have hI0 : 0 ≤ inverseBoundI d (x ^ 2) := by linarith
  have hE : 1 ≤ (inverseBoundEValue d : ℝ) := by
    exact_mod_cast inverseBoundE_ge_one d
  have hW : 0 ≤ typeI2W d d x := by
    exact preliminary_natPolynomialEval_nonneg
      (typeI2WPolynomial d d) x (by linarith)
  have hbracket :
      16 * (inverseBoundI d (x ^ 2)) ^ 2 ≤
        16 * (inverseBoundI d (x ^ 2)) ^ 2 +
          4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
            inverseBoundI d (x ^ 2) + 16 := by
    nlinarith [sq_nonneg (typeI2CapitalZ d x), hW, hI0]
  have hbracket0 : 0 ≤
      16 * (inverseBoundI d (x ^ 2)) ^ 2 +
        4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
          inverseBoundI d (x ^ 2) + 16 := by positivity
  calc
    16 * (inverseBoundI d (x ^ 2)) ^ 2 =
        1 * (16 * (inverseBoundI d (x ^ 2)) ^ 2) := by ring
    _ ≤ (inverseBoundEValue d : ℝ) *
        (16 * (inverseBoundI d (x ^ 2)) ^ 2 +
          4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
            inverseBoundI d (x ^ 2) + 16) :=
      mul_le_mul hE hbracket (by positivity) (by linarith [hE])

private theorem preliminary_smallM_typeI_short_impossible
    (d : ℕ) (hd : 1 ≤ d) (δ X H M : ℝ)
    (hδ : 0 < δ) (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hδhalf : δ < 1 / 2)
    (hMsmall : M < 2 * Real.sqrt (Real.sqrt (H * X)))
    (hshort : H ≤ inverseBoundI d ((δ ^ 2)⁻¹) * (2 * M))
    (hlength : typeI2J d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) < H) :
    False := by
  have hδinv : 2 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hδ).2
    nlinarith
  have hIcast : (δ ^ 2)⁻¹ = (δ⁻¹) ^ 2 := by
    field_simp [ne_of_gt hδ]
  have hJbudget :=
    typeI2J_dominates_squared_typeI_budget d hd δ⁻¹ hδinv
  rw [← hIcast] at hJbudget
  let I : ℝ := inverseBoundI d ((δ ^ 2)⁻¹)
  have hI4 : 4 ≤ I := by
    dsimp [I]
    apply inverseBoundI_ge_four d hd
    rw [hIcast]
    nlinarith [hδinv]
  have hIpos : 0 < I := by linarith
  have hIbudget : 16 * I ^ 2 ≤ typeI2J d δ⁻¹ := by
    simpa [I] using hJbudget
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < H := by linarith
  have hroot0 : 0 ≤ Real.rpow X (1 / 3 : ℝ) :=
    Real.rpow_nonneg (by linarith) _
  have hroot3 : (Real.rpow X (1 / 3 : ℝ)) ^ 3 = X :=
    preliminary_rpow_one_third_cube X (by linarith)
  have hlength' : 16 * I ^ 2 * Real.rpow X (1 / 3 : ℝ) < H := by
    have hmul := mul_le_mul_of_nonneg_right hIbudget hroot0
    nlinarith [hlength]
  let Dfourth : ℝ := Real.sqrt (Real.sqrt (H * X))
  have hD2 : Dfourth ^ 2 = Real.sqrt (H * X) := by
    dsimp [Dfourth]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hD4 : Dfourth ^ 4 = H * X := by
    calc
      Dfourth ^ 4 = (Dfourth ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (H * X)) ^ 2 := by rw [hD2]
      _ = H * X := Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hDpos : 0 < Dfourth := by
    dsimp [Dfourth]
    positivity
  have hHle : H ≤ 4 * I * Dfourth := by
    apply le_of_lt
    calc
      H ≤ I * (2 * M) := by simpa [I, mul_comm] using hshort
      _ < I * (4 * Dfourth) := by
        exact mul_lt_mul_of_pos_left (by linarith [hMsmall]) hIpos
      _ = 4 * I * Dfourth := by ring
  have hbase0 : 0 ≤ H := by linarith
  have hbig0 : 0 ≤ 4 * I * Dfourth := by positivity
  have hHsq : H ^ 2 ≤ (4 * I * Dfourth) ^ 2 :=
    (sq_le_sq₀ hbase0 hbig0).2 hHle
  have hHfourth : H ^ 4 ≤ (4 * I * Dfourth) ^ 4 := by
    calc
      H ^ 4 = (H ^ 2) ^ 2 := by ring
      _ ≤ ((4 * I * Dfourth) ^ 2) ^ 2 :=
        (sq_le_sq₀ (sq_nonneg H) (sq_nonneg (4 * I * Dfourth))).2 hHsq
      _ = (4 * I * Dfourth) ^ 4 := by ring
  have hHcubeupper : H ^ 3 ≤ 256 * I ^ 4 * X := by
    apply (le_of_mul_le_mul_left ?_ hHpos)
    calc
      H * H ^ 3 = H ^ 4 := by ring
      _ ≤ (4 * I * Dfourth) ^ 4 := hHfourth
      _ = 256 * I ^ 4 * Dfourth ^ 4 := by ring
      _ = 256 * I ^ 4 * (H * X) := by rw [hD4]
      _ = H * (256 * I ^ 4 * X) := by ring
  have hlowerCube :
      (16 * I ^ 2 * Real.rpow X (1 / 3 : ℝ)) ^ 3 < H ^ 3 :=
    pow_lt_pow_left₀ hlength' (by positivity) (by norm_num)
  have hlowerCube' : 4096 * I ^ 6 * X < H ^ 3 := by
    rw [show (16 * I ^ 2 * Real.rpow X (1 / 3 : ℝ)) ^ 3 =
      4096 * I ^ 6 * (Real.rpow X (1 / 3 : ℝ)) ^ 3 by ring,
      hroot3] at hlowerCube
    exact hlowerCube
  have hI2 : 1 ≤ I ^ 2 := one_le_pow₀ (by linarith)
  have hIcoeff : 256 * I ^ 4 ≤ 4096 * I ^ 6 := by
    calc
      256 * I ^ 4 = 256 * I ^ 4 * 1 := by ring
      _ ≤ 256 * I ^ 4 * (16 * I ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hI2]) (by positivity)
      _ = 4096 * I ^ 6 := by ring
  have hIcoeffX := mul_le_mul_of_nonneg_right hIcoeff (le_of_lt hXpos)
  linarith

/-- The short-`M` branch of the approved preliminary Type-I₂ theorem, after
the weighted sum has been identified with a Type-I correlation. -/
theorem preliminaryTypeI2SmallMBranch
    (d : ℕ) (hd : 1 ≤ d) (X H M δ : ℝ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hδ : 0 < δ)
    (hδsmall : δ < min (1 / 2) ((Real.log X)⁻¹))
    (hMsmall : M < 2 * Real.sqrt (Real.sqrt (H * X)))
    (f : ComplexPositiveIntegerFunction)
    (hf : typeIFunction (δ ^ 2) (2 * M) f)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hlarge : δ ^ 2 * H ≤ typeIScalarPhaseCorrelation f P X H)
    (hlength : typeI2J d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) < H) :
    ∃ r : ℤ, 1 ≤ r ∧
      (r : ℝ) ≤ typeI2J d δ⁻¹ ∧
      polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
        (Int.floor X) H ≤ typeI2J d δ⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        H ^ j * realDistanceToIntegers
          ((r : ℝ) * (phaseCenteredAt P (Int.floor X)).coeff j) ≤
            typeI2J d δ⁻¹ := by
  have hδhalf : δ < 1 / 2 := lt_of_lt_of_le hδsmall (min_le_left _ _)
  have hδlt1 : δ < 1 := by linarith
  have hδsqpos : 0 < δ ^ 2 := pow_pos hδ 2
  have hδsqsmall : δ ^ 2 < min (1 / 2) ((Real.log X)⁻¹) := by
    apply lt_min
    · have hsquare : δ ^ 2 < δ := by nlinarith
      exact hsquare.trans hδhalf
    · have hsquare : δ ^ 2 < δ := by nlinarith
      exact hsquare.trans (lt_of_lt_of_le hδsmall (min_le_right _ _))
  have h := typeIInverse d hd X H (δ ^ 2) (2 * M) hX hH hHX
    hδsqpos hδsqsmall f hf P hP hlarge
  have hδinv : 2 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hδ).2
    nlinarith [hδhalf]
  have hIcast : (δ ^ 2)⁻¹ = (δ⁻¹) ^ 2 := by
    field_simp [ne_of_gt hδ]
  have hJbudget :=
    typeI2J_dominates_squared_typeI_budget d hd δ⁻¹ hδinv
  rw [← hIcast] at hJbudget
  rcases h with hshort | ⟨r, hr, hrbound, hbin, hmono⟩
  · exact False.elim
      (preliminary_smallM_typeI_short_impossible d hd δ X H M
        hδ hX hH hδhalf hMsmall hshort hlength)
  · have hIcastBudget :
        inverseBoundI d ((δ ^ 2)⁻¹) = inverseBoundI d ((δ⁻¹) ^ 2) := by
      rw [hIcast]
    have hIge : 4 ≤ inverseBoundI d ((δ ^ 2)⁻¹) := by
      rw [hIcast]
      apply inverseBoundI_ge_four d hd
      nlinarith [hδinv]
    have hIbudget :
        inverseBoundI d ((δ ^ 2)⁻¹) ≤ typeI2J d δ⁻¹ := by
      rw [hIcastBudget]
      have hIpos : 0 ≤ inverseBoundI d ((δ⁻¹) ^ 2) := by linarith [hIge]
      nlinarith [hJbudget, hIpos]
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · exact le_trans hrbound hIbudget
    · exact le_trans hbin hIbudget
    · intro j hj hjd
      exact le_trans (hmono j hj hjd) hIbudget

/-- The complete approved short-`M` branch, starting from the direct finite
weighted sum on a representative of the integer hyperbola lattice. -/
theorem preliminaryTypeI2SmallMFromLattice
    (d : ℕ) (hd : 1 ≤ d) (X H M δ : ℝ) (J : Set ℝ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hMhalf : (1 / 2 : ℝ) ≤ M)
    (hδ : 0 < δ)
    (hδsmall : δ < min (1 / 2) ((Real.log X)⁻¹))
    (hMsmall : M < 2 * Real.sqrt (Real.sqrt (H * X)))
    (hJ : J ⊆ Set.Ioc M (2 * M))
    (Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) =
      Hyperbola.hyperbolaLatticeSet X H J)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (hqbound : (q₀ : ℝ) ≤ δ⁻¹)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q₀ hq₀ ≤
      ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q₀ hq₀ ≤
      ENNReal.ofReal (δ⁻¹))
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (f : ℤ × ℤ → ℂ)
    (hphase : ∀ p, p ∈ Λ →
      f p = unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ))))
    (hraw : δ * H ≤ ‖∑ p ∈ Λ,
      complexPositiveIntegerZeroExtension β₁ p.1 *
        complexPositiveIntegerZeroExtension β₂ p.2 * f p‖)
    (hlength : typeI2J d δ⁻¹ * Real.rpow X (1 / 3 : ℝ) < H) :
    ∃ r : ℤ, 1 ≤ r ∧
      (r : ℝ) ≤ typeI2J d δ⁻¹ ∧
      polynomialBinomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
        (Int.floor X) H ≤ typeI2J d δ⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        H ^ j * realDistanceToIntegers
          ((r : ℝ) * (phaseCenteredAt P (Int.floor X)).coeff j) ≤
            typeI2J d δ⁻¹ := by
  have hδlt1 : δ < 1 := by
    have hδhalf : δ < 1 / 2 := lt_of_lt_of_le hδsmall (min_le_left _ _)
    linarith
  let α := intervalWeightRestriction J β₁
  let fI := complexPositiveDirichletConvolution α β₂
  have hf : typeIFunction (δ ^ 2) (2 * M) fI := by
    exact preliminaryTypeI2IntervalWeightTypeI M δ J hJ hMhalf hδ hδlt1
      β₁ β₂ q₀ hq₀ hqbound hTV₁ hTV₂
  have hbridge := preliminaryTypeI2_intervalWeight_latticeSum
    X H M J (by linarith) hMhalf hJ Λ hΛ β₁ β₂ P f hphase
  have hraw' := hraw
  rw [← hbridge] at hraw'
  have hδsquare : δ ^ 2 ≤ δ := by nlinarith [hδsmall]
  have hδH : δ ^ 2 * H ≤ δ * H :=
    mul_le_mul_of_nonneg_right hδsquare (by linarith)
  have hlarge : δ ^ 2 * H ≤
      typeIScalarPhaseCorrelation fI P X H := by
    calc
      δ ^ 2 * H ≤ δ * H := hδH
      _ ≤ ‖typeIScalarPhaseSum fI P X H‖ := by
        simpa [typeIScalarPhaseCorrelation, fI] using hraw'
  exact preliminaryTypeI2SmallMBranch d hd X H M δ hX hH hHX hδ hδsmall
    hMsmall fI hf P hP hlarge hlength

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2IntervalWeightTypeI
#print axioms FractionalPrimes.Literature.Polynomial.preliminary_residueVariation_controls_value
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2_intervalWeight_latticeSum
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2SmallMBranch
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2SmallMFromLattice
