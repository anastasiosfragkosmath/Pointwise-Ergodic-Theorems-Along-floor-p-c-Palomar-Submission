module

public import FractionalPrimes.Literature.Hyperbola.OrdinaryWeightedPigeonhole
public import FractionalPrimes.Literature.Polynomial.PolynomialPreliminaryTypeI2LargeM
public import FractionalPrimes.Literature.Polynomial.PolynomialProductRecurrence
public import FractionalPrimes.Literature.Polynomial.ProgressionPhaseInverse

set_option maxHeartbeats 800000

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Hyperbola
open FractionalPrimes.Literature.Uniformity
open _root_.Polynomial

/-- The direction-count constant `κ=δ^6/(8B₀G²)` from the ordinary
weighted-pigeonhole application. -/
noncomputable def typeI2LargeMKappa (δ : ℝ) : ℝ :=
  δ ^ 6 / (8 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) ^ 2)

/-- The fixed denominator-fiber density parameter
`σ=κ/(2BB₀)`, where `B=G_{2d}(t)` and `t=4B₀Gδ⁻³`. -/
noncomputable def typeI2LargeMSigma (d : ℕ) (δ : ℝ) : ℝ :=
  typeI2LargeMKappa δ /
    (2 * typeI2B d (δ⁻¹) * (typeI2BZeroValue : ℝ))

/-- At the approved value `K₀=2`, the ordinary hyperbola constants are the
Type-I₂ constants `B₀` and `G`. -/
theorem preliminaryTypeI2LargeM_budget_constants_match
    (g : HyperbolaGeometricData) (hK₀ : g.K₀ = 2) :
    ordinaryB0 g = (typeI2BZeroValue : ℝ) ∧
      C_geo g.K₀ = (typeI2GValue : ℝ) := by
  constructor
  · change E g.K₀ + g.K₀ ^ 2 = _
    rw [hK₀]
    norm_num [E, typeI2BZeroValue, typeI2EValue, typeI2KZeroValue]
  · change 2 * (C_point g.K₀ + C_line g.K₀) + 8 + E g.K₀ = _
    rw [hK₀]
    norm_num [C_point, C_line, D, E, typeI2GValue,
      typeI2CPointValue, typeI2CLineValue, typeI2DValue,
      typeI2EValue, typeI2KZeroValue]

/-- The source's large-M application of the ordinary weighted pigeonhole
theorem, with its constants rewritten as the approved Type-I₂ budgets. -/
theorem preliminaryTypeI2LargeMOrdinaryPigeonhole
    (g : HyperbolaGeometricData) (hgK₀ : g.K₀ = 2)
    (d : ℕ) (hd : 1 ≤ d)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (q₀ : ℕ) (hq₀ : 1 ≤ q₀)
    (hq₀bound : (q₀ : ℝ) ≤ δ⁻¹)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (P : Polynomial ℝ)
    (hlarge : δ * g.H ≤
      ‖∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension β₂ p.2 *
            unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖) :
    ∃ good : Finset (ℕ × ℕ),
      (δ ^ 6 /
        (8 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) ^ 2) *
          (g.X * (g.Q : ℝ) ^ 2 / g.M ^ 2)) ≤ (good.card : ℝ) ∧
      ∀ i ∈ good,
        Nat.Coprime i.1 i.2 ∧
        0 < i.1 ∧ 0 < i.2 ∧
        (typeI2T (δ⁻¹))⁻¹ * (g.Q : ℝ) ≤ (i.2 : ℝ) ∧
        i.2 ≤ g.Q ∧
        (g.r / 8) * (i.2 : ℝ) ≤ (i.1 : ℝ) ∧
        (i.1 : ℝ) ≤ E g.K₀ * g.r * (i.2 : ℝ) ∧
        ∃ Ppiece ∈ hyperbolaProgressionFamily g i.1 i.2,
        ∃ z : ℤ × ℤ, ∃ N : ℕ, ∃ hN : 0 < N,
          (↑(latticeProgression z
            ((q₀ : ℤ) * (i.2 : ℤ)) ((q₀ : ℤ) * (i.1 : ℤ)) N hN) :
              Set (ℤ × ℤ)) ⊆ Ppiece ∧
          (↑(latticeProgression z
            ((q₀ : ℤ) * (i.2 : ℤ)) ((q₀ : ℤ) * (i.1 : ℤ)) N hN) :
              Set (ℤ × ℤ)) ⊆ g.lattice ∧
          (typeI2T (δ⁻¹))⁻¹ * g.L0 ≤ (N : ℝ) ∧
          (N : ℝ) ≤ g.L0 ∧
          (typeI2T (δ⁻¹))⁻¹ * g.L0 ≤
            ‖∑ p ∈ latticeProgression z
              ((q₀ : ℤ) * (i.2 : ℤ)) ((q₀ : ℤ) * (i.1 : ℤ)) N hN,
                unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖ := by
  classical
  have hconstants := preliminaryTypeI2LargeM_budget_constants_match g hgK₀
  have hτ : ordinaryTau g δ = (typeI2T (δ⁻¹))⁻¹ := by
    rw [ordinaryTau, typeI2T_eval, hconstants.1, hconstants.2]
    field_simp [ne_of_gt hδ]
  have hphase : ∀ p, p ∈ g.lattice →
      ‖unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖ ≤ 1 := by
    intro p hp
    simp [norm_unitFrequencyPhase]
  obtain ⟨good, hgood, hgoodmem⟩ :=
    ordinaryWeightedPigeonhole g (hyperbolaProgressionPartition g)
      δ hδ hδle q₀ hq₀ hq₀bound β₁ β₂ hTV₁ hTV₂ Λ hΛ
      (fun p => unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ))))
      hphase hlarge
  refine ⟨good, ?_, ?_⟩
  · simpa [hconstants.1, hconstants.2] using hgood
  · intro i hi
    rcases hgoodmem i hi with
      ⟨hcop, hai, hqi, hτq, hqhi, hamlo, hamhi, Ppiece, hPpiece,
        z, N, hN, hsubpiece, hsubLattice, hτN, hNupper, hτsum⟩
    refine ⟨hcop, hai, hqi, ?_, hqhi, hamlo, hamhi, Ppiece, hPpiece,
      z, N, hN, hsubpiece, hsubLattice, ?_, hNupper, ?_⟩
    · simpa [hτ] using hτq
    · simpa [hτ] using hτN
    · simpa [hτ] using hτsum

private theorem latticeProgression_sum_eq_arithmeticProgressionPoints
    (z : ℤ × ℤ) (q a : ℤ) (N : ℕ) (hN : 0 < N) (hq : q ≠ 0)
    (F : ℤ × ℤ → ℂ) :
    (∑ p ∈ latticeProgression z q a N hN, F p) =
      ∑ k ∈ arithmeticProgressionPoints 1 1 (by norm_num) N,
        F (z.1 + ((k : ℤ) - 1) * q,
          z.2 - ((k : ℤ) - 1) * a) := by
  classical
  let φ : Fin N → ℤ × ℤ := fun j =>
    (z.1 + (j.val : ℤ) * q, z.2 - (j.val : ℤ) * a)
  have hinj : Set.InjOn φ
      (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)) := by
    intro i hi j hj hij
    apply Fin.ext
    have hfirst := congrArg Prod.fst hij
    have hmul : (i.val : ℤ) * q = (j.val : ℤ) * q := by
      dsimp [φ] at hfirst
      exact add_left_cancel hfirst
    have hval : (i.val : ℤ) = (j.val : ℤ) :=
      mul_right_cancel₀ hq hmul
    exact_mod_cast hval
  have hleft :
      (∑ p ∈ latticeProgression z q a N hN, F p) =
        ∑ j ∈ Finset.range N,
          F (z.1 + (j : ℤ) * q, z.2 - (j : ℤ) * a) := by
    change (∑ p ∈ Finset.univ.image φ, F p) = _
    rw [Finset.sum_image hinj]
    change (∑ j : Fin N,
      F (z.1 + (j.val : ℤ) * q, z.2 - (j.val : ℤ) * a)) = _
    rw [← Fin.sum_univ_eq_sum_range]
  have hright :
      (∑ k ∈ arithmeticProgressionPoints 1 1 (by norm_num) N,
        F (z.1 + ((k : ℤ) - 1) * q,
          z.2 - ((k : ℤ) - 1) * a)) =
        ∑ j ∈ Finset.range N,
          F (z.1 + (j : ℤ) * q, z.2 - (j : ℤ) * a) := by
    have hAP : arithmeticProgressionPoints 1 1 (by norm_num) N =
        (Finset.range N).image (fun j : ℕ => (1 + (j : ℤ))) := by
      simp [arithmeticProgressionPoints]
    have hshiftInj : Set.InjOn (fun j : ℕ => (1 + (j : ℤ)))
        (↑(Finset.range N) : Set ℕ) := by
      intro i hi j hj hij
      have hcast : (i : ℤ) = (j : ℤ) := add_left_cancel hij
      exact_mod_cast hcast
    rw [hAP]
    rw [Finset.sum_image hshiftInj]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1 <;> push_cast <;> ring
  exact hleft.trans hright.symm

private theorem preliminaryTypeI2LargeM_inverseOnProgression
    (g : HyperbolaGeometricData) (d : ℕ) (hd : 1 ≤ d)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (q₀ q a : ℕ) (hq₀ : 1 ≤ q₀) (hq : 0 < q)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (z : ℤ × ℤ) (N : ℕ) (hN : 0 < N)
    (hNupper : (N : ℝ) ≤ g.L0)
    (hphase : (typeI2T (δ⁻¹))⁻¹ * g.L0 ≤
      ‖∑ p ∈ latticeProgression z
        ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN,
          unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖) :
    ∃ v : ℕ, 1 ≤ v ∧ (v : ℝ) ≤ typeI2B d (δ⁻¹) ∧
      ∀ j, 1 ≤ j → j ≤ 2 * d →
        g.L0 ^ j * realDistanceToIntegers
          ((v : ℝ) *
            ((P.comp (hyperbolaProductPolynomial
              (z.1 - (q₀ : ℤ) * (q : ℤ))
              (z.2 + (q₀ : ℤ) * (a : ℤ))
              ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)))).coeff j)) ≤
          typeI2B d (δ⁻¹) := by
  classical
  have hq₀pos : 0 < q₀ := Nat.lt_of_lt_of_le Nat.zero_lt_one hq₀
  have hstepPos : 0 < (q₀ : ℤ) * (q : ℤ) := by
    exact_mod_cast (Nat.mul_pos hq₀pos hq)
  have hstepNe : (q₀ : ℤ) * (q : ℤ) ≠ 0 := ne_of_gt hstepPos
  have hLlower : 1 ≤ g.L0 := by
    exact (admissibleParameterBounds g 1 (by norm_num)
      (Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne')).L0_lower
  have hδinv : 1 ≤ δ⁻¹ := by
    exact (one_le_inv₀ hδ).2 hδle
  have hTlarge : 2 < typeI2T (δ⁻¹) := by
    rw [typeI2T_eval]
    have hcoef : 2 < 4 * (typeI2BZeroValue : ℝ) *
        (typeI2GValue : ℝ) := by
      norm_num [typeI2BZeroValue, typeI2EValue, typeI2KZeroValue,
        typeI2GValue, typeI2CPointValue, typeI2CLineValue,
        typeI2DValue]
    have hx : 1 ≤ (δ⁻¹) ^ 3 := one_le_pow₀ hδinv
    calc
      2 < 4 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) := hcoef
      _ ≤ 4 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) *
          (δ⁻¹) ^ 3 := by nlinarith
      _ = 4 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) *
          (δ⁻¹) ^ 3 := rfl
  have hρpos : 0 < (typeI2T (δ⁻¹))⁻¹ := inv_pos.mpr (by linarith [hTlarge])
  have hρhalf : (typeI2T (δ⁻¹))⁻¹ < 1 / 2 := by
    rw [inv_eq_one_div]
    apply (div_lt_div_iff₀ (by linarith [hTlarge]) (by norm_num)).2
    norm_num
    linarith [hTlarge]
  let qstep : ℤ := (q₀ : ℤ) * (q : ℤ)
  let astep : ℤ := (q₀ : ℤ) * (a : ℤ)
  let Q : Polynomial ℝ := P.comp
    (hyperbolaProductPolynomial (z.1 - qstep) (z.2 + astep) qstep astep)
  have hQ :
      Q.natDegree ≤ 2 * d := by
    calc
      _ ≤ P.natDegree *
          (hyperbolaProductPolynomial (z.1 - qstep) (z.2 + astep)
            qstep astep).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ d * 2 := Nat.mul_le_mul hP
        (hyperbolaProductPolynomial_natDegree_le_two _ _ _ _)
      _ = 2 * d := by omega
  let Jidx : Finset ℤ := arithmeticProgressionPoints 1 1 (by norm_num) N
  have hJAP : isFiniteArithmeticProgression Jidx := by
    exact ⟨1, 1, by norm_num, N, rfl⟩
  have hJsubset : ∀ n ∈ Jidx,
      0 < (n : ℝ) ∧ (n : ℝ) ≤ g.L0 := by
    intro n hn
    simp only [Jidx, arithmeticProgressionPoints, Finset.mem_image,
      Finset.mem_range] at hn
    rcases hn with ⟨k, hk, rfl⟩
    constructor
    · have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      push_cast
      norm_num
      linarith
    · have hkn : (k : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hk
      norm_num
      linarith
  have hsumEq :
      (∑ n ∈ Jidx,
        unitFrequencyPhase (Q.eval (n : ℝ))) =
        ∑ p ∈ latticeProgression z
          ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN,
          unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ))) := by
    rw [latticeProgression_sum_eq_arithmeticProgressionPoints
      z ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN hstepNe]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Jidx, arithmeticProgressionPoints, Finset.mem_image,
      Finset.mem_range] at hn
    rcases hn with ⟨k, hk, rfl⟩
    dsimp only [Q]
    rw [Polynomial.eval_comp, hyperbolaProductPolynomial_eval]
    simp only [qstep, astep]
    congr 1 <;> push_cast <;> ring_nf
  have hlarge :
      (typeI2T (δ⁻¹))⁻¹ * g.L0 ≤
        ‖∑ n ∈ Jidx, unitFrequencyPhase (Q.eval (n : ℝ))‖ := by
    rw [hsumEq]
    exact hphase
  obtain ⟨v, hv, hvupper, hvcoeff⟩ :=
    progressionPhaseInverse (2 * d) (by omega) g.L0 hLlower 0
      hρpos hρhalf
      Q hQ
      Jidx hJAP (by simpa only [zero_add] using hJsubset) hlarge
  have hB : inverseBoundG (2 * d) (typeI2T (δ⁻¹)) =
      typeI2B d (δ⁻¹) := by
    simpa only [Nat.mul_comm] using (typeI2B_eval d (δ⁻¹)).symm
  refine ⟨v, hv, ?_, ?_⟩
  · simpa [hB] using hvupper
  · intro j hj hjd
    have h := hvcoeff j hj hjd
    simpa [hB, Q, Int.floor_zero] using h

/-- The per-direction output after applying progression inverse. The product
polynomial is based at the first point of the extracted progression, so its
index runs through `1,…,N` exactly as in the scalar inverse theorem. -/
structure TypeI2LargeMInverseProgressionData
    (g : HyperbolaGeometricData) (d : ℕ) (δ : ℝ) (q₀ : ℕ)
    (P : Polynomial ℝ) (a q : ℕ) where
  v : ℕ
  v_pos : 1 ≤ v
  v_upper : (v : ℝ) ≤ typeI2B d (δ⁻¹)
  piece : Set (ℤ × ℤ)
  piece_mem : piece ∈ hyperbolaProgressionFamily g a q
  z : ℤ × ℤ
  N : ℕ
  hN : 0 < N
  progression_subset_piece :
    (↑(latticeProgression z ((q₀ : ℤ) * (q : ℤ))
      ((q₀ : ℤ) * (a : ℤ)) N hN) : Set (ℤ × ℤ)) ⊆ piece
  progression_subset_lattice :
    (↑(latticeProgression z ((q₀ : ℤ) * (q : ℤ))
      ((q₀ : ℤ) * (a : ℤ)) N hN) : Set (ℤ × ℤ)) ⊆ g.lattice
  scale_lower : (typeI2T (δ⁻¹))⁻¹ * g.L0 ≤ (N : ℝ)
  scale_upper : (N : ℝ) ≤ g.L0
  phase_lower : (typeI2T (δ⁻¹))⁻¹ * g.L0 ≤
    ‖∑ p ∈ latticeProgression z ((q₀ : ℤ) * (q : ℤ))
      ((q₀ : ℤ) * (a : ℤ)) N hN,
        unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖
  coefficient_error : ∀ j, 1 ≤ j → j ≤ 2 * d →
    g.L0 ^ j * realDistanceToIntegers
      ((v : ℝ) *
        ((P.comp (hyperbolaProductPolynomial
          (z.1 - (q₀ : ℤ) * (q : ℤ))
          (z.2 + (q₀ : ℤ) * (a : ℤ))
          ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)))).coeff j)) ≤
      typeI2B d (δ⁻¹)

private noncomputable def preliminaryTypeI2LargeM_inverseDirectionData
    (g : HyperbolaGeometricData) (d : ℕ) (hd : 1 ≤ d)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (q₀ : ℕ) (hq₀ : 1 ≤ q₀)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (a q : ℕ) (hq : 0 < q)
    (piece : Set (ℤ × ℤ)) (hpiece : piece ∈ hyperbolaProgressionFamily g a q)
    (z : ℤ × ℤ) (N : ℕ) (hN : 0 < N)
    (hsubpiece :
      (↑(latticeProgression z ((q₀ : ℤ) * (q : ℤ))
        ((q₀ : ℤ) * (a : ℤ)) N hN) : Set (ℤ × ℤ)) ⊆ piece)
    (hsubLattice :
      (↑(latticeProgression z ((q₀ : ℤ) * (q : ℤ))
        ((q₀ : ℤ) * (a : ℤ)) N hN) : Set (ℤ × ℤ)) ⊆ g.lattice)
    (hscale : (typeI2T (δ⁻¹))⁻¹ * g.L0 ≤ (N : ℝ))
    (hNupper : (N : ℝ) ≤ g.L0)
    (hphase : (typeI2T (δ⁻¹))⁻¹ * g.L0 ≤
      ‖∑ p ∈ latticeProgression z ((q₀ : ℤ) * (q : ℤ))
        ((q₀ : ℤ) * (a : ℤ)) N hN,
          unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖) :
    TypeI2LargeMInverseProgressionData g d δ q₀ P a q := by
  let hinv :=
    preliminaryTypeI2LargeM_inverseOnProgression g d hd δ hδ hδle
      q₀ q a hq₀ hq P hP z N hN hNupper hphase
  let v := Classical.choose hinv
  have hvspec := Classical.choose_spec hinv
  refine ⟨v, hvspec.1, hvspec.2.1, piece, hpiece, z, N, hN,
    hsubpiece, hsubLattice, hscale, hNupper, hphase, ?_⟩
  intro j hj hjd
  exact hvspec.2.2 j hj hjd

private theorem typeI2LargeM_exists_large_denominator_fiber
    {α : Type*} [DecidableEq α] (S : Finset α) (rmap : α → ℕ)
    (A : ℝ) (hA : 1 ≤ A)
    (hrpos : ∀ x ∈ S, 1 ≤ rmap x)
    (hrbound : ∀ x ∈ S, (rmap x : ℝ) ≤ A) :
    ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ A ∧
      (S.card : ℝ) / A ≤ ((S.filter fun x => rmap x = r).card : ℝ) := by
  classical
  let T : Finset ℕ := Finset.Icc 1 ⌊A⌋₊
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hfloor : 1 ≤ ⌊A⌋₊ := Nat.le_floor (by simpa using hA)
  have hTnonempty : T.Nonempty := ⟨1, by simp [T, hfloor]⟩
  have hmaps : ∀ x ∈ S, rmap x ∈ T := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hrpos x hx, Nat.le_floor (hrbound x hx)⟩
  have hTcard : (T.card : ℝ) ≤ A := by
    have hcard : T.card = ⌊A⌋₊ := by simp [T, Nat.card_Icc]
    rw [hcard]
    exact Nat.floor_le (le_trans (by norm_num) hA)
  have hsum : T.card • ((S.card : ℝ) / A) ≤
      ∑ _x ∈ S, (1 : ℝ) := by
    rw [nsmul_eq_mul]
    calc
      (T.card : ℝ) * ((S.card : ℝ) / A) ≤
          A * ((S.card : ℝ) / A) :=
        mul_le_mul_of_nonneg_right hTcard (by positivity)
      _ = (S.card : ℝ) := by field_simp [ne_of_gt hApos]
      _ = ∑ _x ∈ S, (1 : ℝ) := by simp
  obtain ⟨r, hrT, hrlarge⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := S) (t := T) (f := rmap) (w := fun _ => (1 : ℝ))
      hmaps hTnonempty hsum
  refine ⟨r, (Finset.mem_Icc.mp hrT).1, ?_, ?_⟩
  · exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hrT).2).trans
      (Nat.floor_le (le_trans (by norm_num) hA))
  · simpa using hrlarge

/-- The common-denominator, positive-direction rectangle conclusion through
the source's fixed-scale density statement, before coefficient descent. -/
theorem preliminaryTypeI2LargeMDenseDirectionRectangle
    (g : HyperbolaGeometricData) (hgK₀ : g.K₀ = 2)
    (d : ℕ) (hd : 1 ≤ d)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (q₀ : ℕ) (hq₀ : 1 ≤ q₀)
    (hq₀bound : (q₀ : ℝ) ≤ δ⁻¹)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hlarge : δ * g.H ≤
      ‖∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension β₂ p.2 *
            unitFrequencyPhase (P.eval ((p.1 : ℝ) * (p.2 : ℝ)))‖) :
    ∃ S : Finset (ℕ × ℕ), ∃ v : ℕ,
      1 ≤ v ∧ (v : ℝ) ≤ typeI2B d (δ⁻¹) ∧
      (2 * typeI2LargeMSigma d δ * (g.Q : ℝ) *
        (typeI2LargeMRecurrenceNTwo g.X g.M g.Q : ℝ)) ≤ (S.card : ℝ) ∧
      S ⊆ Finset.Icc 1 g.Q ×ˢ
        Finset.Icc 1 (typeI2LargeMRecurrenceNTwo g.X g.M g.Q) ∧
      ∀ i ∈ S,
        Nat.Coprime i.2 i.1 ∧
        1 ≤ i.1 ∧ i.1 ≤ g.Q ∧
        1 ≤ i.2 ∧
          i.2 ≤ typeI2LargeMRecurrenceNTwo g.X g.M g.Q ∧
        (typeI2T (δ⁻¹))⁻¹ * (g.Q : ℝ) ≤ (i.1 : ℝ) ∧
        (g.r / 8) * (i.1 : ℝ) ≤ (i.2 : ℝ) ∧
        (i.2 : ℝ) ≤ E g.K₀ * g.r * (i.1 : ℝ) ∧
        ∃ D : TypeI2LargeMInverseProgressionData g d δ q₀ P i.2 i.1,
          D.v = v := by
  classical
  let B : ℝ := typeI2B d (δ⁻¹)
  let N₂ := typeI2LargeMRecurrenceNTwo g.X g.M g.Q
  have hconstants := preliminaryTypeI2LargeM_budget_constants_match g hgK₀
  have hTlarge : 2 < typeI2T (δ⁻¹) := by
    have hδinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδle
    rw [typeI2T_eval]
    have hcoef : 2 < 4 * (typeI2BZeroValue : ℝ) *
        (typeI2GValue : ℝ) := by
      norm_num [typeI2BZeroValue, typeI2EValue, typeI2KZeroValue,
        typeI2GValue, typeI2CPointValue, typeI2CLineValue,
        typeI2DValue]
    have hx : 1 ≤ (δ⁻¹) ^ 3 := one_le_pow₀ hδinv
    calc
      2 < 4 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) := hcoef
      _ ≤ 4 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) *
          (δ⁻¹) ^ 3 := by nlinarith
      _ = 4 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) *
          (δ⁻¹) ^ 3 := rfl
  have hB : 1 ≤ B := by
    change 1 ≤ typeI2B d (δ⁻¹)
    rw [typeI2B_eval]
    exact inverseBoundG_ge_one (2 * d) (typeI2T (δ⁻¹)) (by linarith)
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hgoodData := preliminaryTypeI2LargeMOrdinaryPigeonhole
    g hgK₀ d hd δ hδ hδle q₀ hq₀ hq₀bound β₁ β₂ hTV₁ hTV₂
    Λ hΛ P hlarge
  rcases hgoodData with ⟨good, hgoodLower, hgoodMem⟩
  have hτpos : 0 < (typeI2T (δ⁻¹))⁻¹ := inv_pos.mpr (by linarith [hTlarge])
  have hLpos : 0 < g.L0 := by
    exact lt_of_lt_of_le zero_lt_one
      (admissibleParameterBounds g 1 (by norm_num)
        (Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne')).L0_lower
  have hXpos : 0 < g.X := lt_of_lt_of_le zero_lt_one g.X_ge_one
  have hMpos : 0 < g.M := lt_of_lt_of_le zero_lt_one g.M_ge_one
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hQone : 1 ≤ g.Q := Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne'
  have hrpos : 0 < g.r := by
    dsimp [HyperbolaGeometricData.r]
    exact div_pos hXpos (sq_pos_of_pos hMpos)
  have hκgood :
      typeI2LargeMKappa δ * g.r * (g.Q : ℝ) ^ 2 ≤ (good.card : ℝ) := by
    dsimp [typeI2LargeMKappa, HyperbolaGeometricData.r]
    calc
      δ ^ 6 / (8 * (typeI2BZeroValue : ℝ) *
          (typeI2GValue : ℝ) ^ 2) * (g.X / g.M ^ 2) * (g.Q : ℝ) ^ 2 =
        δ ^ 6 / (8 * (typeI2BZeroValue : ℝ) *
          (typeI2GValue : ℝ) ^ 2) *
          (g.X * (g.Q : ℝ) ^ 2 / g.M ^ 2) := by ring
      _ ≤ (good.card : ℝ) := hgoodLower
  let invData : ∀ i : ℕ × ℕ, i ∈ good →
      TypeI2LargeMInverseProgressionData g d δ q₀ P i.1 i.2 :=
    fun i hi => Classical.choose (show
      ∃ D : TypeI2LargeMInverseProgressionData g d δ q₀ P i.1 i.2, True from by
      rcases hgoodMem i hi with
        ⟨hcop, ha, hq, hτq, hqhi, hamlo, hamhi, piece, hpiece,
          z, N, hN, hsubpiece, hsubLattice, hτN, hNupper, hτsum⟩
      exact ⟨preliminaryTypeI2LargeM_inverseDirectionData
        g d hd δ hδ hδle q₀ hq₀ P hP i.1 i.2 (by omega)
        piece hpiece z N hN hsubpiece hsubLattice hτN hNupper hτsum,
        trivial⟩)
  let rmap : ℕ × ℕ → ℕ := fun i =>
    if hi : i ∈ good then (invData i hi).v else 1
  have hrmapSpec (i : ℕ × ℕ) (hi : i ∈ good) :
      rmap i = (invData i hi).v ∧ 1 ≤ rmap i ∧ (rmap i : ℝ) ≤ B := by
    dsimp [rmap]
    rw [dif_pos hi]
    exact ⟨rfl, (invData i hi).v_pos, (invData i hi).v_upper⟩
  obtain ⟨v, hvpos, hvB, hfiber⟩ :=
    typeI2LargeM_exists_large_denominator_fiber good rmap B hB
      (fun i hi => (hrmapSpec i hi).2.1)
      (fun i hi => by simpa [B] using (hrmapSpec i hi).2.2)
  let sourceFiber := good.filter fun i => rmap i = v
  let S := sourceFiber.image Prod.swap
  have hBzero : 0 < (typeI2BZeroValue : ℝ) := by norm_num [typeI2BZeroValue,
    typeI2EValue, typeI2KZeroValue]
  have hE : E g.K₀ = (typeI2EValue : ℝ) := by
    rw [hgK₀]
    norm_num [E, typeI2EValue, typeI2KZeroValue]
  have hMbound : g.M ≤ 2 * Real.sqrt g.X := by
    simpa [hgK₀] using g.M_le_K₀_sqrtX
  have hMsq : g.M ^ 2 ≤ 4 * g.X := by
    have hsqrt : (Real.sqrt g.X) ^ 2 = g.X := Real.sq_sqrt hXpos.le
    nlinarith [sq_nonneg (2 * Real.sqrt g.X - g.M)]
  have hquarter : (1 / 4 : ℝ) ≤ g.r := by
    change (1 / 4 : ℝ) ≤ g.X / g.M ^ 2
    apply (le_div_iff₀ (sq_pos_of_pos hMpos)).2
    nlinarith [hMsq]
  have huQquarter : (1 / 4 : ℝ) ≤ g.r * (g.Q : ℝ) := by
    calc
      (1 / 4 : ℝ) ≤ g.r := hquarter
      _ ≤ g.r * (g.Q : ℝ) := by
        nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr (show (1 : ℝ) ≤ (g.Q : ℝ) by exact_mod_cast hQone))]
  have hN₂ceil : (N₂ : ℝ) <
      (typeI2EValue : ℝ) * g.r * (g.Q : ℝ) + 1 := by
    dsimp [N₂, typeI2LargeMRecurrenceNTwo, HyperbolaGeometricData.r]
    have harg : 0 ≤ (typeI2EValue : ℝ) * (g.X / g.M ^ 2) * (g.Q : ℝ) := by
      positivity
    exact Nat.ceil_lt_add_one harg
  have hbudget : (typeI2BZeroValue : ℝ) =
      (typeI2EValue : ℝ) + 4 := by
    norm_num [typeI2BZeroValue, typeI2EValue, typeI2KZeroValue]
  have hN₂E_lower :
      (typeI2EValue : ℝ) * g.r * (g.Q : ℝ) ≤ (N₂ : ℝ) := by
    dsimp [N₂, typeI2LargeMRecurrenceNTwo, HyperbolaGeometricData.r]
    exact Nat.le_ceil _
  have hN₂upper :
      (N₂ : ℝ) ≤ (typeI2BZeroValue : ℝ) * g.r * (g.Q : ℝ) := by
    rw [hbudget]
    have hfour : 1 ≤ 4 * (g.r * (g.Q : ℝ)) := by nlinarith [huQquarter]
    nlinarith [hN₂ceil]
  have hN₂lower : g.r * (g.Q : ℝ) ≤ (N₂ : ℝ) := by
    dsimp [N₂]
    exact typeI2LargeMRecurrenceNTwo_lower g.X g.M g.Q hXpos.le hMpos
  have hσB : 0 ≤ typeI2LargeMSigma d δ := by
    dsimp [typeI2LargeMSigma, typeI2LargeMKappa, B]
    positivity
  have hκnonneg : 0 ≤ typeI2LargeMKappa δ := by
    dsimp [typeI2LargeMKappa]
    positivity
  have hscaleCoef :
      0 ≤ (typeI2LargeMKappa δ /
        (B * (typeI2BZeroValue : ℝ))) * (g.Q : ℝ) := by
    apply mul_nonneg
    · exact div_nonneg hκnonneg
        (mul_nonneg hBpos.le (le_of_lt hBzero))
    · exact hQpos.le
  have hdensity :
      2 * typeI2LargeMSigma d δ * (g.Q : ℝ) * (N₂ : ℝ) ≤
        (sourceFiber.card : ℝ) := by
    have hscale := div_le_div_of_nonneg_right hκgood hBpos.le
    have hFiber' : (good.card : ℝ) / B ≤ (sourceFiber.card : ℝ) := by
      simpa [sourceFiber] using hfiber
    calc
      2 * typeI2LargeMSigma d δ * (g.Q : ℝ) * (N₂ : ℝ) =
          (typeI2LargeMKappa δ / (B * (typeI2BZeroValue : ℝ))) *
            (g.Q : ℝ) * (N₂ : ℝ) := by
              dsimp [typeI2LargeMSigma]
              ring
      _ ≤ (typeI2LargeMKappa δ / (B * (typeI2BZeroValue : ℝ))) *
            (g.Q : ℝ) * ((typeI2BZeroValue : ℝ) * g.r * (g.Q : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hN₂upper hscaleCoef
      _ = typeI2LargeMKappa δ * g.r * (g.Q : ℝ) ^ 2 / B := by
              field_simp [ne_of_gt hBpos, ne_of_gt hBzero]
      _ ≤ (good.card : ℝ) / B := hscale
      _ ≤ (sourceFiber.card : ℝ) := hFiber'
  have hswapCard : S.card = sourceFiber.card := by
    dsimp [S]
    exact Finset.card_image_of_injective _ Prod.swap_injective
  have hSsubset : S ⊆ Finset.Icc 1 g.Q ×ˢ Finset.Icc 1 N₂ := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨src, hsrc, hsw⟩
    have hsrc' := Finset.mem_filter.mp hsrc
    have hmem := hgoodMem src hsrc'.1
    rcases hmem with ⟨hcop, ha, hq, hτq, hqhi, hamlo, hamhi,
      piece, hpiece, z, N, hN, hsubpiece, hsubLattice, hτN, hNupper, hτsum⟩
    have hEq : i = (src.2, src.1) := by
      simpa [Prod.swap] using hsw.symm
    subst i
    have hqIcc : src.2 ∈ Finset.Icc 1 g.Q := Finset.mem_Icc.mpr ⟨hq, hqhi⟩
    have hEbound :
        (src.1 : ℝ) ≤ (typeI2EValue : ℝ) * g.r * (src.2 : ℝ) := by
      calc
        (src.1 : ℝ) ≤ E g.K₀ * g.r * (src.2 : ℝ) := hamhi
        _ = (typeI2EValue : ℝ) * g.r * (src.2 : ℝ) := by rw [hE]
    have hqN : (src.2 : ℝ) ≤ (g.Q : ℝ) := by exact_mod_cast hqhi
    have hapos : 0 ≤ (src.1 : ℝ) := by positivity
    have haReal : (src.1 : ℝ) ≤ (N₂ : ℝ) := by
      calc
        (src.1 : ℝ) ≤ (typeI2EValue : ℝ) * g.r * (src.2 : ℝ) := hEbound
        _ ≤ (typeI2EValue : ℝ) * g.r * (g.Q : ℝ) := by
          exact mul_le_mul_of_nonneg_left hqN
            (mul_nonneg (by positivity) hrpos.le)
        _ ≤ (N₂ : ℝ) := hN₂E_lower
    have haNat : src.1 ≤ N₂ := by exact_mod_cast haReal
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq, hqhi⟩,
        Finset.mem_Icc.mpr ⟨ha, haNat⟩⟩
  refine ⟨S, v, hvpos, ?_, ?_, hSsubset, ?_⟩
  · exact hvB
  · simpa [hswapCard] using hdensity
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨src, hsrc, hsw⟩
    have hsrc' := Finset.mem_filter.mp hsrc
    have hmem := hgoodMem src hsrc'.1
    rcases hmem with ⟨hcop, ha, hq, hτq, hqhi, hamlo, hamhi,
      piece, hpiece, z, N, hN, hsubpiece, hsubLattice, hτN, hNupper, hτsum⟩
    have hEq : i = (src.2, src.1) := by
      simpa [Prod.swap] using hsw.symm
    rw [hEq]
    have hmap := (hrmapSpec src hsrc'.1).1
    have hsame : (invData src hsrc'.1).v = v := by
      calc
        (invData src hsrc'.1).v = rmap src := hmap.symm
        _ = v := hsrc'.2
    have hEbound :
        (src.1 : ℝ) ≤ (typeI2EValue : ℝ) * g.r * (src.2 : ℝ) := by
      calc
        (src.1 : ℝ) ≤ E g.K₀ * g.r * (src.2 : ℝ) := hamhi
        _ = (typeI2EValue : ℝ) * g.r * (src.2 : ℝ) := by rw [hE]
    have hqN : (src.2 : ℝ) ≤ (g.Q : ℝ) := by exact_mod_cast hqhi
    have haReal : (src.1 : ℝ) ≤ (N₂ : ℝ) := by
      calc
        (src.1 : ℝ) ≤ (typeI2EValue : ℝ) * g.r * (src.2 : ℝ) := hEbound
        _ ≤ (typeI2EValue : ℝ) * g.r * (g.Q : ℝ) := by
          exact mul_le_mul_of_nonneg_left hqN
            (mul_nonneg (by positivity) hrpos.le)
        _ ≤ (N₂ : ℝ) := hN₂E_lower
    have haNat : src.1 ≤ N₂ := by exact_mod_cast haReal
    have hN₂pos : 0 < N₂ := by
      have hN₂posR : (0 : ℝ) < (N₂ : ℝ) := by
        calc
          0 < g.r * (g.Q : ℝ) := mul_pos hrpos hQpos
          _ ≤ (N₂ : ℝ) := hN₂lower
      exact_mod_cast hN₂posR
    exact ⟨hcop, hq, hqhi, ha, haNat,
      hτq, hamlo, hamhi, invData src hsrc'.1, hsame⟩

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_budget_constants_match
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeMOrdinaryPigeonhole
#print axioms FractionalPrimes.Literature.Polynomial.typeI2LargeMKappa
#print axioms FractionalPrimes.Literature.Polynomial.typeI2LargeMSigma
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeMDenseDirectionRectangle
