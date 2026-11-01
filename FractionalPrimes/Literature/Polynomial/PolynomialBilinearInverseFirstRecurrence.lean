module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInversePigeonhole
public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrence
public import FractionalPrimes.Literature.Polynomial.PolynomialIntegerCompositionError

/-!
# The first recurrence step in the bilinear polynomial inverse theorem

This file continues blueprint item `lbi:inverse-theorem` after the two
pigeonholes.  It first isolates the exact translation of a dense subset of
the window `(u,u+R]` into the one-indexed range expected by
`polynomialRecurrence`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

open _root_.Polynomial

/-- Translating `m in (u,u+R]` to the zero-based index `m-u-1` preserves
cardinality and lands in the filtered range whose polynomial samples are
evaluated at `n+1`. -/
theorem card_le_oneIndexed_range_filter_of_window
    (T : Finset ℕ) (u R : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hbounds : ∀ m ∈ T, u < m ∧ m ≤ u + R)
    (hP : ∀ m ∈ T, P (m - u)) :
    T.card ≤ ((Finset.range R).filter fun n => P (n + 1)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun m => m - (u + 1))
  · intro m hm
    have hmT : m ∈ T := hm
    have hmBounds := hbounds m hmT
    change m - (u + 1) ∈ (Finset.range R).filter (fun n => P (n + 1))
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · have hshift : m - u = (m - (u + 1)) + 1 := by omega
      rw [← hshift]
      exact hP m hmT
  · intro m hm m' hm' heq
    have hmT : m ∈ T := hm
    have hm'T : m' ∈ T := hm'
    have hmBounds := hbounds m hmT
    have hm'Bounds := hbounds m' hm'T
    have hmRecover : (m - (u + 1)) + (u + 1) = m := by omega
    have hm'Recover : (m' - (u + 1)) + (u + 1) = m' := by omega
    change m - (u + 1) = m' - (u + 1) at heq
    calc
      m = (m - (u + 1)) + (u + 1) := hmRecover.symm
      _ = (m' - (u + 1)) + (u + 1) := by rw [heq]
      _ = m' := hm'Recover

/-- The polynomial `Gamma_j` has degree at most the ambient phase degree. -/
theorem bilinearGammaPolynomial_natDegree_le
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (nu : ℕ → ℝ)
    (hjd : j ≤ d) :
    (bilinearGammaPolynomial X ell0 d j nu).natDegree ≤ d := by
  have hlinear :
      (Polynomial.C (ell0 : ℝ) * Polynomial.X -
        Polynomial.C X).natDegree ≤ 1 := by
    have hmul :
        (Polynomial.C (ell0 : ℝ) * Polynomial.X).natDegree ≤ 1 :=
      (Polynomial.natDegree_C_mul_le (ell0 : ℝ) Polynomial.X).trans (by simp)
    have hconst : (Polynomial.C X).natDegree ≤ 1 := by simp
    simpa using Polynomial.natDegree_sub_le_of_le hmul hconst
  have hsum :
      (∑ i ∈ Finset.Icc j d,
        Polynomial.C ((i.choose j : ℝ) * nu i) *
          (Polynomial.C (ell0 : ℝ) * Polynomial.X -
            Polynomial.C X) ^ (i - j)).natDegree ≤ d - j := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hiData := Finset.mem_Icc.mp hi
    calc
      (Polynomial.C ((i.choose j : ℝ) * nu i) *
          (Polynomial.C (ell0 : ℝ) * Polynomial.X -
            Polynomial.C X) ^ (i - j)).natDegree ≤
          ((Polynomial.C (ell0 : ℝ) * Polynomial.X -
            Polynomial.C X) ^ (i - j)).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ (i - j) * 1 :=
        Polynomial.natDegree_pow_le_of_le (i - j) hlinear
      _ ≤ d - j := by omega
  unfold bilinearGammaPolynomial
  calc
    (Polynomial.X ^ j *
        ∑ i ∈ Finset.Icc j d,
          Polynomial.C ((i.choose j : ℝ) * nu i) *
            (Polynomial.C (ell0 : ℝ) * Polynomial.X -
              Polynomial.C X) ^ (i - j)).natDegree ≤
        (Polynomial.X ^ j).natDegree +
          (∑ i ∈ Finset.Icc j d,
            Polynomial.C ((i.choose j : ℝ) * nu i) *
              (Polynomial.C (ell0 : ℝ) * Polynomial.X -
                Polynomial.C X) ^ (i - j)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ j + (d - j) := by
      gcongr
      simp
    _ = d := Nat.add_sub_of_le hjd

/-- The polynomial to which the first recurrence theorem is applied for a
fixed coefficient index `j`. -/
def bilinearFirstRecurrencePolynomial
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (nu : ℕ → ℝ)
    (q u mstar : ℕ) : Polynomial ℝ :=
  Polynomial.C (q : ℝ) *
    ((bilinearGammaPolynomial X ell0 d j nu).comp
        (Polynomial.C (u : ℝ) + Polynomial.X) -
      Polynomial.C
        ((bilinearGammaPolynomial X ell0 d j nu).eval (mstar : ℝ)))

@[simp]
theorem bilinearFirstRecurrencePolynomial_eval
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (nu : ℕ → ℝ)
    (q u mstar : ℕ) (t : ℝ) :
    (bilinearFirstRecurrencePolynomial X ell0 d j nu q u mstar).eval t =
      (q : ℝ) *
        ((bilinearGammaPolynomial X ell0 d j nu).eval ((u : ℝ) + t) -
          (bilinearGammaPolynomial X ell0 d j nu).eval (mstar : ℝ)) := by
  unfold bilinearFirstRecurrencePolynomial
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_C]

/-- The first recurrence polynomial still has degree at most `d`. -/
theorem bilinearFirstRecurrencePolynomial_natDegree_le
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (nu : ℕ → ℝ)
    (q u mstar : ℕ) (hjd : j ≤ d) :
    (bilinearFirstRecurrencePolynomial X ell0 d j nu q u mstar).natDegree ≤ d := by
  let G := bilinearGammaPolynomial X ell0 d j nu
  have hG : G.natDegree ≤ d := by
    simpa [G] using bilinearGammaPolynomial_natDegree_le X ell0 d j nu hjd
  have hshift :
      (Polynomial.C (u : ℝ) + Polynomial.X).natDegree ≤ 1 := by
    rw [add_comm, Polynomial.natDegree_X_add_C]
  have hcomp :
      (G.comp (Polynomial.C (u : ℝ) + Polynomial.X)).natDegree ≤ d := by
    calc
      (G.comp (Polynomial.C (u : ℝ) + Polynomial.X)).natDegree ≤
          G.natDegree *
            (Polynomial.C (u : ℝ) + Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ d * 1 := Nat.mul_le_mul hG hshift
      _ = d := by simp
  have hconst :
      (Polynomial.C (G.eval (mstar : ℝ))).natDegree ≤ d := by simp
  unfold bilinearFirstRecurrencePolynomial
  exact (Polynomial.natDegree_C_mul_le (q : ℝ) _).trans
    ((Polynomial.natDegree_sub_le_of_le hcomp hconst).trans (by simp))

/-- Its linear coefficient is `q` times the linear coefficient of the
translated `Gamma_j`. -/
theorem bilinearFirstRecurrencePolynomial_coeff_one
    (X : ℝ) (ell0 : ℤ) (d j : ℕ) (nu : ℕ → ℝ)
    (q u mstar : ℕ) :
    (bilinearFirstRecurrencePolynomial X ell0 d j nu q u mstar).coeff 1 =
      (q : ℝ) * bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ) := by
  unfold bilinearFirstRecurrencePolynomial bilinearGammaLinearCoefficient
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  simp only [Polynomial.coeff_C, if_neg (by norm_num : (1 : ℕ) ≠ 0),
    sub_zero]

/-- One fixed coefficient index admits the first recurrence multiplier.  This
is the exact per-`j` step between the common-denominator pigeonhole and the
product denominator in blueprint proof `lbi:inverse-theorem`. -/
theorem bilinearFirstRecurrence_for_degree
    (d : ℕ) (hd : 1 ≤ d)
    (X M rho r s : ℝ) (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2)
    (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hZr : bilinearInverseZ d rho⁻¹ ≤ r)
    (hZs : bilinearInverseZ d rho⁻¹ ≤ s)
    (ell0 : ℤ) (nu : ℕ → ℝ) (u q mstar : ℕ) (T : Finset ℕ)
    (hTsub : T ⊆ bilinearWindow M r u)
    (hTcard :
      2 * (bilinearInverseZOne d rho⁻¹)⁻¹ *
          (bilinearWindowRadius r : ℝ) ≤ (T.card : ℝ))
    (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d)
    (happrox : ∀ m ∈ T,
      realDistanceToIntegers
          ((q : ℝ) *
            ((bilinearGammaPolynomial X ell0 d j nu).eval (m : ℝ) -
              (bilinearGammaPolynomial X ell0 d j nu).eval (mstar : ℝ))) ≤
        bilinearInverseB d rho⁻¹ / s ^ j) :
    ∃ t : ℕ, 1 ≤ t ∧
      (t : ℝ) ≤ bilinearInverseVOne d rho⁻¹ ∧
      realDistanceToIntegers
          (((t * q : ℕ) : ℝ) *
            bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ)) ≤
        bilinearInverseVOne d rho⁻¹ *
            (bilinearInverseB d rho⁻¹ / s ^ j) /
          (bilinearWindowRadius r : ℝ) := by
  classical
  let x : ℝ := rho⁻¹
  let B : ℝ := bilinearInverseB d x
  let ZOne : ℝ := bilinearInverseZOne d x
  let VOne : ℝ := bilinearInverseVOne d x
  let Z : ℝ := bilinearInverseZ d x
  let delta : ℝ := ZOne⁻¹
  let eps : ℝ := B / s ^ j
  let N : ℕ := bilinearWindowRadius r
  let P : Polynomial ℝ :=
    bilinearFirstRecurrencePolynomial X ell0 d j nu q u mstar
  have hx : 2 ≤ x := by
    dsimp [x]
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hrho).2
    nlinarith
  rcases bilinearInverseBudget_values d hd x hx with
    ⟨hB, hZOne, hVOne, hA, hZTwo, hVTwo, hC, hE, hZ⟩
  have hBpos : 0 < B := by dsimp [B]; linarith
  have hZOnePos : 0 < ZOne := by dsimp [ZOne]; linarith
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdeltaHalf : delta < 1 / 2 := by
    dsimp [delta]
    simpa only [one_div] using
      ((inv_lt_inv₀ hZOnePos (by norm_num : (0 : ℝ) < 2)).2 hZOne)
  have hsPos : 0 < s := by linarith
  have hspowPos : 0 < s ^ j := pow_pos hsPos j
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hZdom := bilinearInverseZ_dominates d hd x hx
  have hspow : s ≤ s ^ j := by
    nth_rewrite 1 [← pow_one s]
    exact pow_le_pow_right₀ hs hj
  have hbudgetPow : 64 * B * ZOne ≤ s ^ j := by
    calc
      64 * B * ZOne ≤ Z := by
        simpa [B, ZOne, Z] using hZdom.2.2.1
      _ ≤ s := by simpa [Z, x] using hZs
      _ ≤ s ^ j := hspow
  have hepsDelta : eps ≤ delta / 64 := by
    have hraw : B / s ^ j ≤ 1 / (64 * ZOne) := by
      apply (div_le_div_iff₀ hspowPos
        (mul_pos (by norm_num) hZOnePos)).2
      nlinarith
    have hright : delta / 64 = 1 / (64 * ZOne) := by
      dsimp [delta]
      field_simp [ne_of_gt hZOnePos]
    change B / s ^ j ≤ delta / 64
    rw [hright]
    exact hraw
  have hNrealLower : 4 * r ≤ (N : ℝ) := by
    dsimp [N, bilinearWindowRadius]
    exact Nat.le_ceil _
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hdeltaInv : delta⁻¹ = ZOne := by
    dsimp [delta]
    rw [inv_inv]
  have hTleVOne : recurrenceBudgetT d ZOne ≤ VOne := by
    rw [show VOne = bilinearRecurrenceG d ZOne by
      simp [VOne, ZOne, x, bilinearInverseVOne_eval]]
    rw [bilinearRecurrenceG_eval]
    have hRnonneg : 0 ≤ recurrenceBudgetR d ZOne := by
      have := recurrenceBudgetR_ge_one d hd ZOne (by linarith)
      linarith
    linarith
  have hVOneLeZ : VOne ≤ Z := by
    simpa [VOne, Z, x] using hZdom.1
  have hTlarge : recurrenceBudgetT d delta⁻¹ ≤ (N : ℝ) := by
    rw [hdeltaInv]
    calc
      recurrenceBudgetT d ZOne ≤ VOne := hTleVOne
      _ ≤ Z := hVOneLeZ
      _ ≤ r := by simpa [Z, x] using hZr
      _ ≤ (N : ℝ) := by linarith
  have hRleVOne : recurrenceBudgetR d ZOne ≤ VOne := by
    rw [show VOne = bilinearRecurrenceG d ZOne by
      simp [VOne, ZOne, x, bilinearInverseVOne_eval]]
    rw [bilinearRecurrenceG_eval]
    have hTnonneg : 0 ≤ recurrenceBudgetT d ZOne := by
      have := recurrenceBudgetT_ge_one d hd ZOne (by linarith)
      linarith
    linarith
  have hPdeg : P.natDegree ≤ d := by
    simpa [P] using bilinearFirstRecurrencePolynomial_natDegree_le
      X ell0 d j nu q u mstar hjd
  let Good : ℕ → Prop := fun n =>
    realDistanceToIntegers (P.eval (n : ℝ)) ≤ eps
  have hwindowBounds : ∀ m ∈ T, u < m ∧ m ≤ u + N := by
    intro m hm
    have hmWindow := hTsub hm
    have hmData := (mem_bilinearWindow M r u m).mp hmWindow
    simpa [N] using hmData.2
  have hTGood : ∀ m ∈ T, Good (m - u) := by
    intro m hm
    have hmBounds := hwindowBounds m hm
    have huLe : u ≤ m := hmBounds.1.le
    have hcast : (u : ℝ) + ((m - u : ℕ) : ℝ) = (m : ℝ) := by
      rw [Nat.cast_sub huLe]
      ring
    dsimp [Good, P, eps, B]
    rw [bilinearFirstRecurrencePolynomial_eval, hcast]
    exact happrox m hm
  let goodSet : Finset ℕ := (Finset.range N).filter fun n => Good (n + 1)
  have hTcardNat : T.card ≤ goodSet.card := by
    dsimp [goodSet]
    exact card_le_oneIndexed_range_filter_of_window T u N Good
      hwindowBounds hTGood
  have hTcardReal : (T.card : ℝ) ≤ (goodSet.card : ℝ) := by
    exact_mod_cast hTcardNat
  have hgood : delta * (N : ℝ) ≤ (goodSet.card : ℝ) := by
    calc
      delta * (N : ℝ) ≤ 2 * delta * (N : ℝ) := by
        have hnonneg : 0 ≤ delta * (N : ℝ) := by positivity
        linarith
      _ ≤ (T.card : ℝ) := by
        simpa [delta, ZOne, N, x] using hTcard
      _ ≤ (goodSet.card : ℝ) := hTcardReal
  have hgood' : delta * (N : ℝ) ≤
      (((Finset.range N).filter
        (fun n : ℕ => realDistanceToIntegers
          (P.eval ((n + 1 : ℕ) : ℝ)) ≤ eps)).card : ℝ) := by
    simpa [goodSet, Good] using hgood
  obtain ⟨t, ht, htR, htCoeff⟩ :=
    polynomialRecurrence (d := d) (N := N) hN hdelta hdeltaHalf
      heps hepsDelta P hPdeg hgood' hTlarge
  refine ⟨t, ht, ?_, ?_⟩
  · calc
      (t : ℝ) ≤ recurrenceBudgetR d delta⁻¹ := htR
      _ = recurrenceBudgetR d ZOne := by rw [hdeltaInv]
      _ ≤ VOne := hRleVOne
      _ = bilinearInverseVOne d rho⁻¹ := by rfl
  · have hone := htCoeff 1 (by omega)
    rw [bilinearFirstRecurrencePolynomial_coeff_one] at hone
    have hone' :
        (N : ℝ) * realDistanceToIntegers
            (((t * q : ℕ) : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ)) ≤
          recurrenceBudgetR d ZOne * eps := by
      rw [hdeltaInv] at hone
      simpa [Nat.cast_mul, pow_one, mul_assoc] using hone
    have hscaled :
        recurrenceBudgetR d ZOne * eps ≤ VOne * eps :=
      mul_le_mul_of_nonneg_right hRleVOne heps
    apply (le_div_iff₀ hNpos).2
    calc
      realDistanceToIntegers
          (((t * q : ℕ) : ℝ) *
            bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ)) *
          (N : ℝ) =
          (N : ℝ) * realDistanceToIntegers
            (((t * q : ℕ) : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ)) := by ring
      _ ≤ recurrenceBudgetR d ZOne * eps := hone'
      _ ≤ VOne * eps := hscaled
      _ = bilinearInverseVOne d rho⁻¹ *
          (bilinearInverseB d rho⁻¹ / s ^ j) := by rfl

/-- The common denominator supplied by the two pigeonholes admits one first-
stage recurrence multiplier for every `1 ≤ j ≤ d`. -/
theorem bilinearGoodPairFirstRecurrenceMultipliers
    (d : ℕ) (hd : 1 ≤ d)
    (X H L M rho : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (hrZ : bilinearInverseZ d rho⁻¹ ≤ H / L)
    (hsZ : bilinearInverseZ d rho⁻¹ ≤ H / M)
    (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2)
    (u : ℕ) (hu : u ∈ bilinearWindowCenters M)
    (nu : ℕ → ℝ)
    (hgoodCount : rho ^ 4 * (H / L) ^ 2 / 800 ≤
      ((bilinearGoodPairSet X H L M rho d nu u).card : ℝ)) :
    ∃ q : ℕ, ∃ mstar : ℕ, ∃ T : Finset ℕ,
      1 ≤ q ∧ (q : ℝ) ≤ bilinearInverseB d rho⁻¹ ∧
      mstar ∈ bilinearWindow M (H / L) u ∧
      T ⊆ bilinearWindow M (H / L) u ∧
      2 * (bilinearInverseZOne d rho⁻¹)⁻¹ *
          (bilinearWindowRadius (H / L) : ℝ) ≤ (T.card : ℝ) ∧
      ∀ j, 1 ≤ j → j ≤ d →
        ∃ t : ℕ, 1 ≤ t ∧
          (t : ℝ) ≤ bilinearInverseVOne d rho⁻¹ ∧
          realDistanceToIntegers
              (((t * q : ℕ) : ℝ) *
                bilinearGammaLinearCoefficient X
                  (bilinearCommonLeftBase X (H / M) u)
                    d j nu (u : ℝ)) ≤
            bilinearInverseVOne d rho⁻¹ *
                (bilinearInverseB d rho⁻¹ / (H / M) ^ j) /
              (bilinearWindowRadius (H / L) : ℝ) := by
  obtain ⟨q, mstar, T, hq, hqB, hmstar, hTsub, hTcard, hT⟩ :=
    bilinearGoodPairCommonDenominator d hd X H L M rho hL hM hX hHX
      hr hs hrho hrhoHalf u hu nu hgoodCount
  refine ⟨q, mstar, T, hq, hqB, hmstar, hTsub, hTcard, ?_⟩
  intro j hj hjd
  apply bilinearFirstRecurrence_for_degree d hd X M rho (H / L) (H / M)
    hrho hrhoHalf hr hs hrZ hsZ
    (bilinearCommonLeftBase X (H / M) u) nu u q mstar T hTsub hTcard
    j hj hjd
  intro m hm
  exact (hT m hm).2 j hj hjd

/-- Multiplying the `d` recurrence multipliers produces the source's first
common denominator.  The displayed error is deliberately left in its exact
pre-normalization product form. -/
theorem bilinearFirstRecurrence_combine_multipliers
    (d : ℕ) (hd : 1 ≤ d)
    (X rho r s : ℝ) (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2)
    (hr : 1 ≤ r) (hs : 1 ≤ s)
    (ell0 : ℤ) (nu : ℕ → ℝ) (u q : ℕ)
    (hq : 1 ≤ q) (hqB : (q : ℝ) ≤ bilinearInverseB d rho⁻¹)
    (hmultipliers : ∀ j, 1 ≤ j → j ≤ d →
      ∃ t : ℕ, 1 ≤ t ∧
        (t : ℝ) ≤ bilinearInverseVOne d rho⁻¹ ∧
        realDistanceToIntegers
            (((t * q : ℕ) : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ)) ≤
          bilinearInverseVOne d rho⁻¹ *
              (bilinearInverseB d rho⁻¹ / s ^ j) /
            (bilinearWindowRadius r : ℝ)) :
    ∃ q' : ℕ, 1 ≤ q' ∧
      (q' : ℝ) ≤ bilinearInverseA d rho⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        realDistanceToIntegers
            ((q' : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ)) ≤
          bilinearInverseVOne d rho⁻¹ ^ (d - 1) *
            (bilinearInverseVOne d rho⁻¹ *
                (bilinearInverseB d rho⁻¹ / s ^ j) /
              (bilinearWindowRadius r : ℝ)) := by
  classical
  let B := bilinearInverseB d rho⁻¹
  let V := bilinearInverseVOne d rho⁻¹
  let J := Finset.Icc 1 d
  let t : ℕ → ℕ := fun j =>
    if h : 1 ≤ j ∧ j ≤ d then Classical.choose (hmultipliers j h.1 h.2)
    else 1
  have htSpec (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d) :
      1 ≤ t j ∧ (t j : ℝ) ≤ V ∧
        realDistanceToIntegers
            ((((t j) * q : ℕ) : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ)) ≤
          V * (B / s ^ j) / (bilinearWindowRadius r : ℝ) := by
    dsimp [t]
    rw [dif_pos ⟨hj, hjd⟩]
    simpa [B, V] using Classical.choose_spec (hmultipliers j hj hjd)
  let prodT : ℕ := ∏ j ∈ J, t j
  let q' : ℕ := q * prodT
  have hVone : 1 ≤ V := by
    have hx : 2 ≤ rho⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hrho).2
      nlinarith
    have hVtwo := (bilinearInverseBudget_values d hd rho⁻¹ hx).2.2.1
    dsimp [V]
    linarith
  have hprodPos : 1 ≤ prodT := by
    dsimp [prodT]
    apply Finset.one_le_prod
    intro j hjJ
    have hjData := Finset.mem_Icc.mp hjJ
    exact htSpec j hjData.1 hjData.2 |>.1
  have hJcard : J.card = d := by
    simp [J, Nat.card_Icc]
  have hprodBound : (prodT : ℝ) ≤ V ^ d := by
    calc
      (prodT : ℝ) = ∏ j ∈ J, (t j : ℝ) := by
        simp [prodT]
      _ ≤ ∏ _j ∈ J, V := by
        apply Finset.prod_le_prod₀
        · intro j hjJ
          positivity
        · intro j hjJ
          have hjData := Finset.mem_Icc.mp hjJ
          exact htSpec j hjData.1 hjData.2 |>.2.1
      _ = V ^ d := by simp [hJcard]
  refine ⟨q', ?_, ?_, ?_⟩
  · dsimp [q']
    exact one_le_mul hq hprodPos
  · have hBnonneg : 0 ≤ B := by dsimp [B]; linarith
    have hprodNonneg : 0 ≤ (prodT : ℝ) := by positivity
    calc
      (q' : ℝ) = (q : ℝ) * (prodT : ℝ) := by simp [q']
      _ ≤ B * V ^ d :=
        mul_le_mul (by simpa [B] using hqB) hprodBound hprodNonneg hBnonneg
      _ = bilinearInverseA d rho⁻¹ := by
        rw [bilinearInverseA_eval]
  · intro j hj hjd
    have hjJ : j ∈ J := Finset.mem_Icc.mpr ⟨hj, hjd⟩
    let rest : ℕ := ∏ k ∈ J.erase j, t k
    have hfactor : prodT = t j * rest := by
      dsimp [prodT, rest]
      exact (Finset.mul_prod_erase J t hjJ).symm
    have hrestCard : (J.erase j).card = d - 1 := by
      rw [Finset.card_erase_of_mem hjJ, hJcard]
    have hrestBound : (rest : ℝ) ≤ V ^ (d - 1) := by
      calc
        (rest : ℝ) = ∏ k ∈ J.erase j, (t k : ℝ) := by
          simp [rest]
        _ ≤ ∏ _k ∈ J.erase j, V := by
          apply Finset.prod_le_prod₀
          · intro k hk
            positivity
          · intro k hk
            have hkJ := Finset.mem_of_mem_erase hk
            have hkData := Finset.mem_Icc.mp hkJ
            exact htSpec k hkData.1 hkData.2 |>.2.1
        _ = V ^ (d - 1) := by simp [hrestCard]
    have harg :
        (q' : ℝ) * bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ) =
          (rest : ℝ) *
            ((((t j) * q : ℕ) : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ)) := by
      dsimp [q']
      push_cast
      rw [hfactor]
      push_cast
      ring
    rw [harg]
    have hmul := realDistanceToIntegers_int_mul_le (rest : ℤ)
      ((((t j) * q : ℕ) : ℝ) *
        bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ))
    have habs : |(((rest : ℕ) : ℤ) : ℝ)| = (rest : ℝ) := by simp
    rw [habs] at hmul
    have hbaseNonneg : 0 ≤
        V * (B / s ^ j) / (bilinearWindowRadius r : ℝ) := by
      have hx : 2 ≤ rho⁻¹ := by
        rw [inv_eq_one_div]
        apply (le_div_iff₀ hrho).2
        nlinarith
      have hBpos : 0 < B := by
        have := (bilinearInverseBudget_values d hd rho⁻¹ hx).1
        dsimp [B]
        linarith
      have hRpos : 0 < (bilinearWindowRadius r : ℝ) := by
        have hceil : 4 * r ≤ (bilinearWindowRadius r : ℝ) := by
          dsimp [bilinearWindowRadius]
          exact Nat.le_ceil _
        linarith
      positivity
    calc
      realDistanceToIntegers
          ((rest : ℝ) *
            ((((t j) * q : ℕ) : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ))) ≤
          (rest : ℝ) * realDistanceToIntegers
            ((((t j) * q : ℕ) : ℝ) *
              bilinearGammaLinearCoefficient X ell0 d j nu (u : ℝ)) := hmul
      _ ≤ (rest : ℝ) *
          (V * (B / s ^ j) / (bilinearWindowRadius r : ℝ)) :=
        mul_le_mul_of_nonneg_left (htSpec j hj hjd).2.2 (by positivity)
      _ ≤ V ^ (d - 1) *
          (V * (B / s ^ j) / (bilinearWindowRadius r : ℝ)) :=
        mul_le_mul_of_nonneg_right hrestBound hbaseNonneg

/-- The raw product error from the first recurrence is bounded by the compact
source expression `A/(s^j r)`. -/
theorem bilinearFirstRecurrence_product_error_le
    (d : ℕ) (hd : 1 ≤ d) (rho r s : ℝ)
    (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (j : ℕ) :
    bilinearInverseVOne d rho⁻¹ ^ (d - 1) *
        (bilinearInverseVOne d rho⁻¹ *
            (bilinearInverseB d rho⁻¹ / s ^ j) /
          (bilinearWindowRadius r : ℝ)) ≤
      bilinearInverseA d rho⁻¹ / (s ^ j * r) := by
  let B := bilinearInverseB d rho⁻¹
  let V := bilinearInverseVOne d rho⁻¹
  let A := bilinearInverseA d rho⁻¹
  let N : ℕ := bilinearWindowRadius r
  have hx : 2 ≤ rho⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hrho).2
    nlinarith
  have hvalues := bilinearInverseBudget_values d hd rho⁻¹ hx
  have hBpos : 0 < B := by dsimp [B]; linarith [hvalues.1]
  have hVpos : 0 < V := by dsimp [V]; linarith [hvalues.2.2.1]
  have hApos : 0 < A := by dsimp [A]; linarith [hvalues.2.2.2.1]
  have hsPos : 0 < s := by linarith
  have hrPos : 0 < r := by linarith
  have hNlower : r ≤ (N : ℝ) := by
    have hceil : 4 * r ≤ (N : ℝ) := by
      dsimp [N, bilinearWindowRadius]
      exact Nat.le_ceil _
    linarith
  have hNpos : 0 < (N : ℝ) := hrPos.trans_le hNlower
  have hpow : V ^ (d - 1) * V = V ^ d := by
    rw [← pow_succ]
    congr 1
    omega
  have hraw :
      V ^ (d - 1) * (V * (B / s ^ j) / (N : ℝ)) =
        A / (s ^ j * (N : ℝ)) := by
    have hAeval : A = B * V ^ d := by
      dsimp [A, B, V]
      exact bilinearInverseA_eval d rho⁻¹
    rw [hAeval]
    field_simp [ne_of_gt hsPos, ne_of_gt hNpos]
    nlinarith [hpow]
  rw [show bilinearInverseVOne d rho⁻¹ = V by rfl,
    show bilinearInverseB d rho⁻¹ = B by rfl,
    show bilinearInverseA d rho⁻¹ = A by rfl,
    show (bilinearWindowRadius r : ℝ) = (N : ℝ) by rfl,
    hraw]
  have hnumNonneg : 0 ≤ A / s ^ j := by positivity
  have hleft : A / (s ^ j * (N : ℝ)) = (A / s ^ j) / (N : ℝ) := by
    ring
  have hright : A / (s ^ j * r) = (A / s ^ j) / r := by ring
  rw [hleft, hright]
  exact (div_le_div_iff₀ hNpos hrPos).2
    (mul_le_mul_of_nonneg_left hNlower hnumNonneg)

/-- The aspect-ratio normalization used in formula (B2). -/
theorem bilinearAspectRatio_firstRecurrence_identity
    (A X H L M : ℝ) (hH : 0 < H) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (j : ℕ) (hj : 1 ≤ j) :
    A / ((H / M) ^ j * (H / L)) =
      A * M ^ (j - 1) * X / H ^ (j + 1) := by
  have hMpow : M ^ j = M ^ (j - 1) * M := by
    rw [← pow_succ]
    congr 1
    omega
  have hHpow : H ^ (j + 1) = H ^ j * H := by rw [pow_succ]
  rw [hX]
  rw [div_pow]
  field_simp [ne_of_gt hH, ne_of_gt hL, ne_of_gt hM]
  rw [hMpow, hHpow]
  ring

/-- Formula (B2), including the common product denominator and its exact
source normalization.  This completes the first recurrence stage at a fixed
good window centre. -/
theorem bilinearGoodPairFirstRecurrence
    (d : ℕ) (hd : 1 ≤ d)
    (X H L M rho : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (hrZ : bilinearInverseZ d rho⁻¹ ≤ H / L)
    (hsZ : bilinearInverseZ d rho⁻¹ ≤ H / M)
    (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2)
    (u : ℕ) (hu : u ∈ bilinearWindowCenters M)
    (nu : ℕ → ℝ)
    (hgoodCount : rho ^ 4 * (H / L) ^ 2 / 800 ≤
      ((bilinearGoodPairSet X H L M rho d nu u).card : ℝ)) :
    ∃ q' : ℕ, 1 ≤ q' ∧
      (q' : ℝ) ≤ bilinearInverseA d rho⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        realDistanceToIntegers
            ((q' : ℝ) *
              bilinearGammaLinearCoefficient X
                (bilinearCommonLeftBase X (H / M) u)
                  d j nu (u : ℝ)) ≤
          bilinearInverseA d rho⁻¹ * M ^ (j - 1) * X / H ^ (j + 1) := by
  obtain ⟨q, mstar, T, hq, hqB, hmstar, hTsub, hTcard, hmultipliers⟩ :=
    bilinearGoodPairFirstRecurrenceMultipliers d hd X H L M rho hL hM hX hHX
      hr hs hrZ hsZ hrho hrhoHalf u hu nu hgoodCount
  obtain ⟨q', hq', hq'A, hq'Coeff⟩ :=
    bilinearFirstRecurrence_combine_multipliers d hd X rho (H / L) (H / M)
      hrho hrhoHalf hr hs
      (bilinearCommonLeftBase X (H / M) u) nu u q hq hqB hmultipliers
  refine ⟨q', hq', hq'A, ?_⟩
  intro j hj hjd
  have hHpos : 0 < H := by
    have hHM : M ≤ H := by simpa using (le_div_iff₀ hM).mp hs
    linarith
  calc
    realDistanceToIntegers
        ((q' : ℝ) *
          bilinearGammaLinearCoefficient X
            (bilinearCommonLeftBase X (H / M) u) d j nu (u : ℝ)) ≤
      bilinearInverseVOne d rho⁻¹ ^ (d - 1) *
        (bilinearInverseVOne d rho⁻¹ *
            (bilinearInverseB d rho⁻¹ / (H / M) ^ j) /
          (bilinearWindowRadius (H / L) : ℝ)) := hq'Coeff j hj hjd
    _ ≤ bilinearInverseA d rho⁻¹ /
        ((H / M) ^ j * (H / L)) :=
      bilinearFirstRecurrence_product_error_le d hd rho (H / L) (H / M)
        hrho hrhoHalf hr hs j
    _ = bilinearInverseA d rho⁻¹ * M ^ (j - 1) * X / H ^ (j + 1) :=
      bilinearAspectRatio_firstRecurrence_identity
        (bilinearInverseA d rho⁻¹) X H L M hHpos hL hM hX j hj

#print axioms card_le_oneIndexed_range_filter_of_window
#print axioms bilinearGammaPolynomial_natDegree_le
#print axioms bilinearFirstRecurrencePolynomial_natDegree_le
#print axioms bilinearFirstRecurrencePolynomial_coeff_one
#print axioms bilinearFirstRecurrence_for_degree
#print axioms bilinearGoodPairFirstRecurrenceMultipliers
#print axioms bilinearFirstRecurrence_combine_multipliers
#print axioms bilinearFirstRecurrence_product_error_le
#print axioms bilinearAspectRatio_firstRecurrence_identity
#print axioms bilinearGoodPairFirstRecurrence

end

end FractionalPrimes.Literature.Polynomial
