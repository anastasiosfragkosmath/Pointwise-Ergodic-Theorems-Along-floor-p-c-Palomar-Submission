module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorMeanIntegration
public import FractionalPrimes.Literature.DirichletAdapter.SmoothGroupArithmeticFunctionTupleExpansion
public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownComponentPackaging

/-! Source identities between convolution sums and factorized Type-I sums. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- The selected factor's full Mellin phase splits into the common
oscillatory phase and the inverse square-root weight of an outer factor. -/
theorem smoothLongFactor_twist_eq_outerPhase_div_sqrt
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ smoothDyadicTwistExponent t =
      smoothHeathBrownTypeIOuterPhase t n /
        (Real.sqrt (n : ℝ) : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : 0 ≤ (n : ℝ) := by positivity
  have hsqrt : (n : ℂ) ^ (-1 / 2 : ℂ) =
      ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ := by
    calc
      (n : ℂ) ^ (-1 / 2 : ℂ) =
          ((Real.rpow (n : ℝ) (-(1 / 2 : ℝ))) : ℂ) := by
        convert (Complex.ofReal_cpow hnR (-(1 / 2 : ℝ))).symm using 1 <;>
          norm_num
      _ = ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ := by
        have hreal : Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) =
            (Real.sqrt (n : ℝ))⁻¹ := by
          rw [Real.rpow_eq_pow]
          rw [Real.rpow_neg hnR, ← Real.sqrt_eq_rpow]
        rw [hreal, Complex.ofReal_inv]
  have hexp : smoothDyadicTwistExponent t =
      (-1 / 2 : ℂ) + (-(t : ℂ) * Complex.I) := by
    unfold smoothDyadicTwistExponent
    ring
  rw [hexp]
  rw [Complex.cpow_add _ _ hnC, hsqrt]
  unfold smoothHeathBrownTypeIOuterPhase
  ring

/-- Restoring one logarithmic normalization recovers the exact original
smooth Heath--Brown factor coefficient at every natural argument. -/
theorem smoothHeathBrown_normalizedFactor_restore
    {X z : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X) (n : ℕ) :
    (4 * Real.log X) ^
        (if smoothHeathBrownTypeILogFactor f then (1 : ℕ) else 0) *
      smoothHeathBrownNormalizedFactorCoefficient (z := z) f n =
        smoothHeathBrownFactorFunction z f n := by
  have hlog : 4 * Real.log X ≠ 0 := by
    have hpos : 0 < Real.log X := Real.log_pos (by linarith)
    positivity
  cases f with
  | theta i =>
      simp [smoothHeathBrownTypeILogFactor,
        smoothHeathBrownNormalizedFactorCoefficient,
        smoothHeathBrownFactorFunction]
  | logarithm i =>
      simpa [smoothHeathBrownTypeILogFactor,
        smoothHeathBrownNormalizedFactorCoefficient,
        smoothHeathBrownFactorFunction] using
        (mul_div_cancel₀ (smoothHeathBrownLogFactor i n) hlog)
  | mobius i =>
      simp [smoothHeathBrownTypeILogFactor,
        smoothHeathBrownNormalizedFactorCoefficient,
        smoothHeathBrownFactorFunction]

/-- All logarithmic normalizations in one ordered factor tuple cancel
against the source's exact scalar power. -/
theorem smoothHeathBrown_normalizedFactorProduct_restore
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (u : Fin fs.length → ℕ) :
    (4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor *
      (∏ i : Fin fs.length,
        smoothHeathBrownNormalizedFactorCoefficient (z := z) (fs.get i) (u i)) =
      ∏ i : Fin fs.length, smoothHeathBrownFactorFunction z (fs.get i) (u i) := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      have htail := ih (fun i : Fin fs.length => u i.succ)
      have hhead := smoothHeathBrown_normalizedFactor_restore
        (z := z) hX f (u 0)
      have hget (i : Fin fs.length) : (f :: fs).get i.succ = fs.get i := rfl
      calc
        (4 * Real.log X) ^ (f :: fs).countP smoothHeathBrownTypeILogFactor *
            (∏ i : Fin (f :: fs).length,
              smoothHeathBrownNormalizedFactorCoefficient (z := z)
                ((f :: fs).get i) (u i)) =
          ((4 * Real.log X) ^
              (if smoothHeathBrownTypeILogFactor f then 1 else 0) *
              smoothHeathBrownNormalizedFactorCoefficient (z := z) f (u 0)) *
            ((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor *
              ∏ i : Fin fs.length,
                smoothHeathBrownNormalizedFactorCoefficient (z := z)
                  (fs.get i) (u i.succ)) := by
            simp only [List.countP_cons, List.length_cons,
              Fin.prod_univ_succ, List.get_cons_zero]
            simp_rw [hget]
            rw [pow_add]
            ring
        _ = (smoothHeathBrownFactorFunction z f) (u 0) *
              ∏ i : Fin fs.length,
                smoothHeathBrownFactorFunction z (fs.get i) (u i.succ) := by
            rw [hhead, htail]
        _ = ∏ i : Fin (f :: fs).length,
              smoothHeathBrownFactorFunction z ((f :: fs).get i) (u i) := by
            simp [Fin.prod_univ_succ]

/-- The product of the complementary arguments times the selected
argument is the original ordered tuple product. -/
theorem smoothLongFactor_outerProduct_mul_selected
    {k : ℕ} (selected : Fin k) (v : Fin k → ℕ) :
    (∏ i : smoothHeathBrownTypeIOuterIndex selected, v i.1) *
      v selected = ∏ i : Fin k, v i := by
  classical
  calc
    (∏ i : smoothHeathBrownTypeIOuterIndex selected, v i.1) * v selected =
        (∏ i ∈ Finset.univ.erase selected, v i) * v selected := by
      rw [Finset.prod_coe_sort]
    _ = ∏ i : Fin k, v i :=
      Finset.prod_erase_mul Finset.univ v (Finset.mem_univ selected)

/-- In the non-Möbius selected branch, the free-factor coefficient is
exactly the same normalized coefficient used by the other factors. -/
theorem smoothHeathBrownFreeFactorCoefficient_eq_normalized
    {X z : ℝ} (f : SmoothHeathBrownFactor X)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X, f ≠ .mobius i)
    (n : ℕ) :
    smoothHeathBrownFreeFactorCoefficient f n =
      smoothHeathBrownNormalizedFactorCoefficient (z := z) f n := by
  cases f with
  | theta i => rfl
  | logarithm i => rfl
  | mobius i => exact (hfree i rfl).elim

/-- One complementary weighted factor is its normalized source
coefficient times the full Dirichlet Mellin phase. -/
theorem smoothHeathBrownWeightedFactor_eq_normalized_twist
    {X z : ℝ} (f : SmoothHeathBrownFactor X)
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    smoothHeathBrownWeightedFactorCoefficient (z := z) f
      (smoothHeathBrownTypeIOuterPhase t) n =
        (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n : ℂ) *
          (n : ℂ) ^ smoothDyadicTwistExponent t := by
  rw [smoothLongFactor_twist_eq_outerPhase_div_sqrt n hn t]
  unfold smoothHeathBrownWeightedFactorCoefficient
  ring

/-- The paper's ordered real smooth Heath--Brown convolution coefficient
is the exact multiplicative-antidiagonal tuple sum. -/
theorem smoothHeathBrownConvolutionFactors_apply_finMulAntidiag
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X)) (n : ℕ) :
    smoothHeathBrownConvolutionFactors z fs n =
      ∑ v ∈ Nat.finMulAntidiag fs.length n,
        ∏ i : Fin fs.length,
          smoothHeathBrownFactorFunction z (fs.get i) (v i) := by
  have hprod : (fs.map (smoothHeathBrownFactorFunction z)).prod =
      ∏ i : Fin fs.length, smoothHeathBrownFactorFunction z (fs.get i) := by
    rw [← List.prod_ofFn]
    congr 1
    simpa [List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map fs (smoothHeathBrownFactorFunction z)).symm
  rw [smoothHeathBrownConvolutionFactors, hprod]
  exact arithmeticFunctionRealFinProduct_apply_finMulAntidiag
    fs.length (fun i => smoothHeathBrownFactorFunction z (fs.get i)) n

/-- At a full ordered tuple, restoring all log scalars and multiplying
all Mellin phases gives the paper's single convolution summand. -/
theorem smoothHeathBrown_normalizedTuple_mellin_restore
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (v : Fin fs.length → ℕ) (t : ℝ) :
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
      (∏ i : Fin fs.length,
        (smoothHeathBrownNormalizedFactorCoefficient (z := z)
          (fs.get i) (v i) : ℂ) *
          (v i : ℂ) ^ smoothDyadicTwistExponent t) =
    ((∏ i : Fin fs.length,
        smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ) *
      ((∏ i : Fin fs.length, v i : ℕ) : ℂ) ^ smoothDyadicTwistExponent t := by
  have hnorm := congrArg Complex.ofReal
    (smoothHeathBrown_normalizedFactorProduct_restore (z := z) hX fs v)
  have hnormC :
      (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        (∏ i : Fin fs.length,
          (smoothHeathBrownNormalizedFactorCoefficient (z := z)
            (fs.get i) (v i) : ℂ)) =
      ((∏ i : Fin fs.length,
          smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ) := by
    convert hnorm using 1 <;> norm_cast
  rw [Finset.prod_mul_distrib]
  have hphase := smoothGroupCpow_natProduct
    (Finset.univ : Finset (Fin fs.length)) v (smoothDyadicTwistExponent t)
  calc
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        ((∏ i : Fin fs.length,
          (smoothHeathBrownNormalizedFactorCoefficient (z := z)
            (fs.get i) (v i) : ℂ)) *
          (∏ i : Fin fs.length,
            (v i : ℂ) ^ smoothDyadicTwistExponent t)) =
      ((((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        (∏ i : Fin fs.length,
          (smoothHeathBrownNormalizedFactorCoefficient (z := z)
            (fs.get i) (v i) : ℂ))) *
          (∏ i : Fin fs.length,
            (v i : ℂ) ^ smoothDyadicTwistExponent t) := by ring
    _ = _ := by rw [hnormC, ← hphase]

/-- A fixed positive factor tuple contributes exactly the same source
Dirichlet term whether it is evaluated as the selected-factor Type-I
expression or as an ordered Heath--Brown convolution tuple. -/
theorem smoothHeathBrownTypeI_fixedTuple_eq_sourceTerm
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius i)
    (v : Fin fs.length → ℕ) (hpos : ∀ i, 0 < v i) (t : ℝ) :
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        smoothHeathBrownTypeIOuterTupleCoefficient (z := z) selected t
          (fun i => v i.1) *
        smoothHeathBrownFreeFactorDiscreteTerm (fs.get selected)
          (∏ i : smoothHeathBrownTypeIOuterIndex selected, v i.1)
          t (v selected) =
      ((∏ i : Fin fs.length,
        smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ) *
        ((∏ i : Fin fs.length, v i : ℕ) : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff
          (((∏ i : Fin fs.length, v i : ℕ) : ℝ) / X) : ℂ) := by
  classical
  let I := smoothHeathBrownTypeIOuterIndex selected
  let F : Fin fs.length → ℂ := fun i =>
    (smoothHeathBrownNormalizedFactorCoefficient (z := z) (fs.get i) (v i) : ℂ) *
      (v i : ℂ) ^ smoothDyadicTwistExponent t
  have houter :
      smoothHeathBrownTypeIOuterTupleCoefficient (z := z) selected t
          (fun i => v i.1) = ∏ i : I, F i.1 := by
    unfold smoothHeathBrownTypeIOuterTupleCoefficient
    apply Finset.prod_congr rfl
    intro i hi
    exact smoothHeathBrownWeightedFactor_eq_normalized_twist
      (fs.get i.1) (v i.1) (hpos i.1) t
  have hselected :
      smoothHeathBrownFreeFactorDiscreteTerm (fs.get selected)
          (∏ i : I, v i.1) t (v selected) =
        F selected *
          (polynomialOuterCutoff
            (((∏ i : Fin fs.length, v i : ℕ) : ℝ) / X) : ℂ) := by
    unfold smoothHeathBrownFreeFactorDiscreteTerm
    rw [smoothHeathBrownFreeFactorCoefficient_eq_normalized
      (z := z) (fs.get selected) hfree (v selected)]
    rw [smoothLongFactor_outerProduct_mul_selected selected v]
    dsimp [F]
    push_cast
    ring
  have hfull : (∏ i : I, F i.1) * F selected =
      ∏ i : Fin fs.length, F i := by
    calc
      (∏ i : I, F i.1) * F selected =
          (∏ i ∈ Finset.univ.erase selected, F i) * F selected := by
        rw [Finset.prod_coe_sort]
      _ = ∏ i : Fin fs.length, F i :=
        Finset.prod_erase_mul Finset.univ F (Finset.mem_univ selected)
  rw [houter, hselected]
  calc
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        (∏ i : I, F i.1) *
          (F selected *
            (polynomialOuterCutoff
              (((∏ i : Fin fs.length, v i : ℕ) : ℝ) / X) : ℂ)) =
      ((((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        ((∏ i : I, F i.1) * F selected)) *
          (polynomialOuterCutoff
            (((∏ i : Fin fs.length, v i : ℕ) : ℝ) / X) : ℂ) := by ring
    _ = ((((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        (∏ i : Fin fs.length, F i)) *
          (polynomialOuterCutoff
            (((∏ i : Fin fs.length, v i : ℕ) : ℝ) / X) : ℂ) := by rw [hfull]
    _ = _ := by rw [smoothHeathBrown_normalizedTuple_mellin_restore
      (z := z) hX fs v t]

/-- Exchange a finite sum over products with its exact product fibers.
This is the finite reindexing needed between the paper's `n`-sum and the
selected-factor tuple sum. -/
theorem smoothLongFactor_sum_productFibers
    {α : Type*} [DecidableEq α] (A : Finset ℕ) (T : Finset α)
    (p : α → ℕ) (G : α → ℂ) (W : ℕ → ℂ) :
    (∑ n ∈ A, (∑ v ∈ T.filter (fun v => p v = n), G v) * W n) =
      ∑ v ∈ T.filter (fun v => p v ∈ A), G v * W (p v) := by
  classical
  calc
    (∑ n ∈ A, (∑ v ∈ T.filter (fun v => p v = n), G v) * W n) =
      ∑ n ∈ A, ∑ v ∈ T.filter (fun v => p v = n), G v * W (p v) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        have hp := (Finset.mem_filter.mp hv).2
        rw [hp]
    _ = ∑ v ∈ T.filter (fun v => p v ∈ A), G v * W (p v) := by
      exact Finset.sum_fiberwise_eq_sum_filter T A p (fun v => G v * W (p v))

/-- Split a finite supported tuple sum at one selected coordinate. This is
the purely finite bijection underlying the Type-I selected-factor
reindexing; it makes no analytic estimate or extra hypothesis. -/
theorem smoothLongFactor_piFinset_splitAt_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (i : ι) (G : (ι → ℕ) → ℂ) :
    (∑ v ∈ Fintype.piFinset S, G v) =
      ∑ n ∈ S i, ∑ u ∈ Fintype.piFinset
          (fun j : {j : ι // j ≠ i} => S j.1),
        G ((Equiv.piSplitAt i (fun _ => ℕ)).symm (n, u)) := by
  classical
  let e := Equiv.piSplitAt i (fun _ => ℕ)
  have he : ∀ v : ι → ℕ,
      v ∈ Fintype.piFinset S ↔
        e v ∈ (S i) ×ˢ (Fintype.piFinset
          (fun j : {j : ι // j ≠ i} => S j.1)) := by
    intro v
    have hlogical : (∀ j, v j ∈ S j) ↔
        v i ∈ S i ∧ ∀ j : {j : ι // j ≠ i}, v j.1 ∈ S j.1 := by
      constructor
      · intro hv
        exact ⟨hv i, fun j => hv j.1⟩
      · rintro ⟨hi, hu⟩
        intro j
        by_cases h : j = i
        · subst j
          exact hi
        · exact hu ⟨j, h⟩
    simpa [e, Equiv.piSplitAt, Fintype.mem_piFinset] using hlogical
  have hsum := Finset.sum_equiv e he (fun v hv => by simp) (f := G)
    (g := fun p : ℕ × ({j : ι // j ≠ i} → ℕ) => G (e.symm p))
  simpa only [Finset.sum_product, e, Equiv.piSplitAt] using hsum

/-- Split a full smooth Heath--Brown factor tuple into the selected
factor argument and the tuple on the exact complementary source index. -/
noncomputable def smoothHeathBrownTypeISelectedTupleEquiv
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) :
    (Fin fs.length → ℕ) ≃
      ℕ × (smoothHeathBrownTypeIOuterIndex selected → ℕ) :=
  (Equiv.piSplitAt selected (fun _ => ℕ)).trans
    (Equiv.prodCongr (Equiv.refl ℕ)
      (Equiv.piCongrLeft
        (fun _ : smoothHeathBrownTypeIOuterIndex selected => ℕ)
        (Equiv.subtypeEquivRight (fun j => by simp))))

/-- The source's exact finite factor-support sum reindexed by its
selected Type-I factor. -/
theorem smoothHeathBrownTypeI_supportedTuple_splitSelected
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (G : (Fin fs.length → ℕ) → ℂ) :
    (∑ v ∈ Fintype.piFinset
        (fun i : Fin fs.length =>
          smoothHeathBrownFactorFiniteSupport (fs.get i)), G v) =
      ∑ n ∈ smoothHeathBrownFactorFiniteSupport (fs.get selected),
        ∑ u ∈ smoothHeathBrownTypeIOuterTupleSet fs selected,
          G ((smoothHeathBrownTypeISelectedTupleEquiv fs selected).symm (n, u)) := by
  classical
  let ie : {j : Fin fs.length // j ≠ selected} ≃
      smoothHeathBrownTypeIOuterIndex selected :=
    Equiv.subtypeEquivRight (fun j => by simp)
  let e := smoothHeathBrownTypeISelectedTupleEquiv fs selected
  have he : ∀ v : Fin fs.length → ℕ,
      v ∈ Fintype.piFinset
        (fun i : Fin fs.length => smoothHeathBrownFactorFiniteSupport (fs.get i)) ↔
      e v ∈ (smoothHeathBrownFactorFiniteSupport (fs.get selected)) ×ˢ
        smoothHeathBrownTypeIOuterTupleSet fs selected := by
    intro v
    have hlogical :
        (∀ i : Fin fs.length, v i ∈ smoothHeathBrownFactorFiniteSupport (fs.get i)) ↔
          v selected ∈ smoothHeathBrownFactorFiniteSupport (fs.get selected) ∧
            ∀ j : smoothHeathBrownTypeIOuterIndex selected,
              v j.1 ∈ smoothHeathBrownFactorFiniteSupport (fs.get j.1) := by
      constructor
      · intro hv
        exact ⟨hv selected, fun j => hv j.1⟩
      · rintro ⟨hs, ho⟩
        intro j
        by_cases h : j = selected
        · subst j
          exact hs
        · exact ho ⟨j, by simp [h]⟩
    simpa [e, smoothHeathBrownTypeISelectedTupleEquiv, ie, Equiv.piSplitAt,
      Equiv.piCongrLeft, smoothHeathBrownTypeIOuterTupleSet,
      Fintype.mem_piFinset] using hlogical
  have hsum := Finset.sum_equiv e he (fun v hv => by simp) (f := G)
    (g := fun p : ℕ × (smoothHeathBrownTypeIOuterIndex selected → ℕ) =>
      G (e.symm p))
  simpa only [Finset.sum_product, e] using hsum

/-- Recover the selected argument from the source tuple equivalence. -/
theorem smoothHeathBrownTypeISelectedTupleEquiv_symm_selected
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (n : ℕ)
    (u : smoothHeathBrownTypeIOuterIndex selected → ℕ) :
    (smoothHeathBrownTypeISelectedTupleEquiv fs selected).symm
      (n, u) selected = n := by
  simp [smoothHeathBrownTypeISelectedTupleEquiv, Equiv.piSplitAt,
    Equiv.piCongrLeft]

/-- Recover a complementary argument from the source tuple equivalence. -/
theorem smoothHeathBrownTypeISelectedTupleEquiv_symm_outer
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (n : ℕ)
    (u : smoothHeathBrownTypeIOuterIndex selected → ℕ)
    (j : smoothHeathBrownTypeIOuterIndex selected) :
    (smoothHeathBrownTypeISelectedTupleEquiv fs selected).symm
      (n, u) j.1 = u j := by
  have hj : j.1 ≠ selected := (Finset.mem_erase.mp j.2).1
  simp [smoothHeathBrownTypeISelectedTupleEquiv, Equiv.piSplitAt,
    Equiv.piCongrLeft, Equiv.subtypeEquivRight, hj]
  congr 1

/-- The full source tuple product is the selected argument times the
complementary tuple product. This preserves the residue condition. -/
theorem smoothHeathBrownTypeISelectedTupleEquiv_symm_product
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (n : ℕ)
    (u : smoothHeathBrownTypeIOuterIndex selected → ℕ) :
    (∏ j : Fin fs.length,
      (smoothHeathBrownTypeISelectedTupleEquiv fs selected).symm (n, u) j) =
      (∏ j : smoothHeathBrownTypeIOuterIndex selected, u j) * n := by
  let v := (smoothHeathBrownTypeISelectedTupleEquiv fs selected).symm (n, u)
  have h := smoothLongFactor_outerProduct_mul_selected selected v
  have ho : (∏ j : smoothHeathBrownTypeIOuterIndex selected, v j.1) =
      ∏ j : smoothHeathBrownTypeIOuterIndex selected, u j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact smoothHeathBrownTypeISelectedTupleEquiv_symm_outer
      fs selected n u j
  have hs : v selected = n :=
    smoothHeathBrownTypeISelectedTupleEquiv_symm_selected fs selected n u
  rw [ho, hs] at h
  exact h.symm

/-- Every coordinate of a selected factor tuple from the exact source
supports is positive, as required for its Mellin phase identity. -/
theorem smoothHeathBrownTypeISelectedTupleEquiv_symm_pos
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (n : ℕ)
    (hn : n ∈ smoothHeathBrownFactorFiniteSupport (fs.get selected))
    (u : smoothHeathBrownTypeIOuterIndex selected → ℕ)
    (hu : u ∈ smoothHeathBrownTypeIOuterTupleSet fs selected) :
    ∀ i : Fin fs.length,
      0 < (smoothHeathBrownTypeISelectedTupleEquiv fs selected).symm
        (n, u) i := by
  intro i
  by_cases his : i = selected
  · subst i
    rw [smoothHeathBrownTypeISelectedTupleEquiv_symm_selected]
    exact smoothHeathBrownFactorFiniteSupport_pos_for_frequency
      (fs.get selected) hn
  · let j : smoothHeathBrownTypeIOuterIndex selected :=
      ⟨i, by simp [his]⟩
    rw [show i = j.1 by rfl,
      smoothHeathBrownTypeISelectedTupleEquiv_symm_outer]
    exact smoothHeathBrownFactorFiniteSupport_pos_for_frequency
      (fs.get j.1) (Fintype.mem_piFinset.mp hu j)

/-- The source's exact open/closed factor support sits inside the
closed integer scale window used by the free-factor progression. -/
theorem smoothHeathBrownFactorFiniteSupport_subset_freeScaleWindow
    {X : ℝ} (f : SmoothHeathBrownFactor X) :
    smoothHeathBrownFactorFiniteSupport f ⊆
      smoothHeathBrownFreeFactorScaleWindow f := by
  intro n hn
  have hNnonneg : 0 ≤ smoothHeathBrownFactorScale f := by
    have hN := smoothHeathBrownFactorScale_ge_one f
    linarith
  have hwindow : smoothHeathBrownFactorScale f / 2 < (n : ℝ) ∧
      (n : ℝ) ≤ 2 * smoothHeathBrownFactorScale f := by
    rw [smoothHeathBrownFactorFiniteSupport_eq_massWindow] at hn
    exact (mem_smoothFactorMassWindow hNnonneg n).mp hn
  apply Finset.mem_Icc.mpr
  constructor
  · have hfloor :
        (Nat.floor (smoothHeathBrownFactorScale f / 2) : ℝ) ≤ (n : ℝ) :=
      le_trans (Nat.floor_le (by positivity)) hwindow.1.le
    exact_mod_cast hfloor
  · exact Nat.le_floor hwindow.2

/-- A free theta/log sample outside the source's exact factor support
vanishes, even if it lies in the broader closed scale window. -/
theorem smoothHeathBrownFreeFactorDiscreteTerm_eq_zero_outside_exactSupport
    {X z : ℝ} (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m : ℕ) (t : ℝ) {n : ℕ}
    (hn : n ∉ smoothHeathBrownFactorFiniteSupport f) :
    smoothHeathBrownFreeFactorDiscreteTerm f m t n = 0 := by
  have hnorm :
      smoothHeathBrownNormalizedFactorCoefficient (z := z) f n = 0 := by
    by_contra hne
    exact hn (smoothHeathBrownNormalizedFactorCoefficient_support
      (z := z) f hne)
  have hcoeff : smoothHeathBrownFreeFactorCoefficient f n = 0 := by
    rw [smoothHeathBrownFreeFactorCoefficient_eq_normalized
      (z := z) f hfree n]
    exact hnorm
  simp [smoothHeathBrownFreeFactorDiscreteTerm, hcoeff]

/-- Summing over the finite congruence subtype is the same as summing
over the underlying residue-filtered scale window. -/
theorem smoothHeathBrownFreeFactorSupportSolutions_sum
    {X : ℝ} (f : SmoothHeathBrownFactor X)
    (m q a : ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions f m q a, F n.1) =
      ∑ n ∈ smoothHeathBrownFreeFactorResidueWindow f m q a, F n := by
  classical
  simp [smoothHeathBrownFreeFactorSupportSolutions,
    Finset.sum_map, smoothHeathBrownFreeFactorSupportEmbedding]
  exact Finset.sum_attach _ _

/-- The Type-I progression's larger closed scale window contributes
exactly the terms in the source's open/closed factor support. -/
theorem smoothHeathBrownFreeFactorSupportSolutions_sum_eq_exactSupport
    {X z : ℝ} (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m q a : ℕ) (t : ℝ) :
    (∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions f m q a,
      smoothHeathBrownFreeFactorDiscreteTerm f m t n.1) =
      ∑ n ∈ (smoothHeathBrownFactorFiniteSupport f).filter
          (fun n => m * n ≡ a [MOD q]),
        smoothHeathBrownFreeFactorDiscreteTerm f m t n := by
  classical
  rw [smoothHeathBrownFreeFactorSupportSolutions_sum]
  let R := smoothHeathBrownFreeFactorResidueWindow f m q a
  let S := (smoothHeathBrownFactorFiniteSupport f).filter
    (fun n => m * n ≡ a [MOD q])
  have hsub : S ⊆ R := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hs, hr⟩
    exact Finset.mem_filter.mpr
      ⟨smoothHeathBrownFactorFiniteSupport_subset_freeScaleWindow f hs, hr⟩
  have hzero : ∀ n ∈ R, n ∉ S →
      smoothHeathBrownFreeFactorDiscreteTerm f m t n = 0 := by
    intro n hn hnS
    have hr := (Finset.mem_filter.mp hn).2
    have hns : n ∉ smoothHeathBrownFactorFiniteSupport f := by
      intro hs
      exact hnS (Finset.mem_filter.mpr ⟨hs, hr⟩)
    exact smoothHeathBrownFreeFactorDiscreteTerm_eq_zero_outside_exactSupport
      (z := z) f hfree m t hns
  change (∑ n ∈ R, smoothHeathBrownFreeFactorDiscreteTerm f m t n) =
    ∑ n ∈ S, smoothHeathBrownFreeFactorDiscreteTerm f m t n
  exact (Finset.sum_subset hsub hzero).symm

/-- Reindex the source's exact supported tuple sum in one fixed residue
class by the selected factor and its complementary tuple. -/
theorem smoothHeathBrownTypeI_supportedTuple_residueSplitSelected
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (q a : ℕ)
    (G : (Fin fs.length → ℕ) → ℂ) :
    (∑ v ∈ (Fintype.piFinset
        (fun i : Fin fs.length =>
          smoothHeathBrownFactorFiniteSupport (fs.get i))).filter
        (fun v => (∏ i : Fin fs.length, v i) ≡ a [MOD q]), G v) =
      ∑ u ∈ smoothHeathBrownTypeIOuterTupleSet fs selected,
        ∑ n ∈ (smoothHeathBrownFactorFiniteSupport (fs.get selected)).filter
          (fun n => smoothHeathBrownTypeIOuterTupleProduct u * n ≡ a [MOD q]),
          G ((smoothHeathBrownTypeISelectedTupleEquiv fs selected).symm
            (n, u)) := by
  classical
  rw [Finset.sum_filter]
  rw [smoothHeathBrownTypeI_supportedTuple_splitSelected]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [smoothHeathBrownTypeISelectedTupleEquiv_symm_product]
  rw [Finset.sum_filter]
  rfl

/-- Real-valued supported tuple expansion for an ordered arithmetic-function
product. This is the source's finite-support restriction, with no change to
the underlying convolution coefficient. -/
theorem arithmeticFunctionRealFinProduct_apply_supportedTupleSum
    (k : ℕ) (f : Fin k → ArithmeticFunction ℝ)
    (S : Fin k → Finset ℕ)
    (hf : ∀ i n, n ∉ S i → f i n = 0)
    (hpos : ∀ i n, n ∈ S i → 0 < n) (n : ℕ) :
    (∏ i : Fin k, f i) n =
      ∑ v ∈ (Fintype.piFinset S).filter
          (fun v => ∏ i : Fin k, v i = n),
        ∏ i : Fin k, f i (v i) := by
  classical
  let R := (Fintype.piFinset S).filter
    (fun v => ∏ i : Fin k, v i = n)
  have hRsub : R ⊆ Nat.finMulAntidiag k n := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvS, hvprod⟩
    rw [Nat.mem_finMulAntidiag]
    constructor
    · exact hvprod
    · have hvpos : 0 < ∏ i : Fin k, v i :=
        Finset.prod_pos fun i hi => hpos i (v i) (Fintype.mem_piFinset.mp hvS i)
      rw [hvprod] at hvpos
      exact hvpos.ne'
  have hzero : ∀ v ∈ Nat.finMulAntidiag k n, v ∉ R →
      ∏ i : Fin k, f i (v i) = 0 := by
    intro v hv hvR
    have hsome : ∃ i : Fin k, v i ∉ S i := by
      by_contra h
      push Not at h
      apply hvR
      apply Finset.mem_filter.mpr
      exact ⟨Fintype.mem_piFinset.mpr h,
        (Nat.mem_finMulAntidiag.mp hv).1⟩
    rcases hsome with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hf i (v i) hi)
  rw [arithmeticFunctionRealFinProduct_apply_finMulAntidiag]
  change (∑ v ∈ Nat.finMulAntidiag k n, ∏ i : Fin k, f i (v i)) =
    ∑ v ∈ R, ∏ i : Fin k, f i (v i)
  symm
  exact Finset.sum_subset hRsub hzero

/-- The original smooth Heath--Brown convolution coefficient equals the
supported tuple sum over its exact source factor windows. -/
theorem smoothHeathBrownConvolutionFactors_apply_supportedTupleSum
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X)) (n : ℕ) :
    smoothHeathBrownConvolutionFactors z fs n =
      ∑ v ∈ (Fintype.piFinset
          (fun i : Fin fs.length =>
            smoothHeathBrownFactorFiniteSupport (fs.get i))).filter
          (fun v => ∏ i : Fin fs.length, v i = n),
        ∏ i : Fin fs.length,
          smoothHeathBrownFactorFunction z (fs.get i) (v i) := by
  have hprod : (fs.map (smoothHeathBrownFactorFunction z)).prod =
      ∏ i : Fin fs.length, smoothHeathBrownFactorFunction z (fs.get i) := by
    rw [← List.prod_ofFn]
    congr 1
    simpa [List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map fs (smoothHeathBrownFactorFunction z)).symm
  have hsupport : ∀ (i : Fin fs.length) (m : ℕ),
      m ∉ smoothHeathBrownFactorFiniteSupport (fs.get i) →
      smoothHeathBrownFactorFunction z (fs.get i) m = 0 := by
    intro i m hm
    have hnorm0 : smoothHeathBrownNormalizedFactorCoefficient
        (z := z) (fs.get i) m = 0 := by
      by_contra hne
      exact hm (smoothHeathBrownNormalizedFactorCoefficient_support
        (z := z) (fs.get i) hne)
    have hrestore := smoothHeathBrown_normalizedFactor_restore
      (z := z) hX (fs.get i) m
    rw [hnorm0, mul_zero] at hrestore
    exact hrestore.symm
  have hpositive : ∀ (i : Fin fs.length) (m : ℕ),
      m ∈ smoothHeathBrownFactorFiniteSupport (fs.get i) → 0 < m := by
    intro i m hm
    exact smoothHeathBrownFactorFiniteSupport_pos_for_frequency
      (fs.get i) hm
  rw [smoothHeathBrownConvolutionFactors, hprod]
  exact arithmeticFunctionRealFinProduct_apply_supportedTupleSum
    fs.length (fun i => smoothHeathBrownFactorFunction z (fs.get i))
    (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
    hsupport hpositive n

/-- The original smooth Heath--Brown convolution coefficient vanishes
outside the finite product image of the exact factor supports. -/
theorem smoothHeathBrownConvolutionFactors_eq_zero_outside_supportedProduct
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X)) (n : ℕ)
    (hn : n ∉ (Fintype.piFinset
      (fun i : Fin fs.length =>
        smoothHeathBrownFactorFiniteSupport (fs.get i))).image
        (fun v => ∏ i : Fin fs.length, v i)) :
    smoothHeathBrownConvolutionFactors z fs n = 0 := by
  rw [smoothHeathBrownConvolutionFactors_apply_supportedTupleSum hX fs n]
  apply Finset.sum_eq_zero
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hvT, hp⟩
  exact (hn (Finset.mem_image.mpr ⟨v, hvT, hp⟩)).elim

/-- The paper's convolution coefficient Dirichlet sum, on the exact
finite image of its factor supports, equals its ordered supported
tuple sum in the same residue class. -/
theorem smoothHeathBrownTypeI_finiteSourceSum_eq_supportedTupleSum
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X)) (q a : ℕ) (t : ℝ) :
    let T := Fintype.piFinset (fun i : Fin fs.length =>
      smoothHeathBrownFactorFiniteSupport (fs.get i))
    let p : (Fin fs.length → ℕ) → ℕ := fun v => ∏ i : Fin fs.length, v i
    let A := T.image p
    (∑ n ∈ A.filter (fun n => n ≡ a [MOD q]),
      ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
        (n : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff ((n : ℝ) / X) : ℂ)) =
      ∑ v ∈ T.filter (fun v => p v ≡ a [MOD q]),
        ((∏ i : Fin fs.length,
          smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ) *
        ((p v : ℕ) : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff (((p v : ℕ) : ℝ) / X) : ℂ) := by
  classical
  intro T p A
  let G : (Fin fs.length → ℕ) → ℂ := fun v =>
    ((∏ i : Fin fs.length,
      smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ)
  let W : ℕ → ℂ := fun n =>
    (n : ℂ) ^ smoothDyadicTwistExponent t *
      (polynomialOuterCutoff ((n : ℝ) / X) : ℂ)
  have hconv (n : ℕ) :
      ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) =
        ∑ v ∈ T.filter (fun v => p v = n), G v := by
    rw [smoothHeathBrownConvolutionFactors_apply_supportedTupleSum hX fs n]
    simp only [T, p, G]
    push_cast
    rfl
  calc
    (∑ n ∈ A.filter (fun n => n ≡ a [MOD q]),
      ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
        (n : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff ((n : ℝ) / X) : ℂ)) =
      ∑ n ∈ A.filter (fun n => n ≡ a [MOD q]),
        (∑ v ∈ T.filter (fun v => p v = n), G v) * W n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [← mul_assoc, hconv]
    _ = ∑ v ∈ T.filter
        (fun v => p v ∈ A.filter (fun n => n ≡ a [MOD q])),
        G v * W (p v) := by
          exact smoothLongFactor_sum_productFibers
            (A.filter (fun n => n ≡ a [MOD q])) T p G W
    _ = ∑ v ∈ T.filter (fun v => p v ≡ a [MOD q]),
        G v * W (p v) := by
          apply Finset.sum_congr
          · ext v
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hv, hA, hr⟩
              exact ⟨hv, hr⟩
            · rintro ⟨hv, hr⟩
              exact ⟨hv, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hr⟩
          · intro v hv
            rfl
    _ = _ := by simp [G, W, mul_assoc]

/-- The exact residue-filtered source tuple sum is the selected-factor
Type-I component sum with precisely the paper's logarithmic
normalization scalar. -/
theorem smoothHeathBrownTypeI_supportedTupleSum_eq_factorized
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius i)
    (q a : ℕ) (t : ℝ) :
    (∑ v ∈ (Fintype.piFinset
        (fun i : Fin fs.length =>
          smoothHeathBrownFactorFiniteSupport (fs.get i))).filter
        (fun v => (∏ i : Fin fs.length, v i) ≡ a [MOD q]),
      ((∏ i : Fin fs.length,
        smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ) *
        ((∏ i : Fin fs.length, v i : ℕ) : ℂ) ^
          smoothDyadicTwistExponent t *
        (polynomialOuterCutoff
          (((∏ i : Fin fs.length, v i : ℕ) : ℝ) / X) : ℂ)) =
      (((4 * Real.log X) ^
        fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        smoothHeathBrownTypeIFactorizedComponentSum
          (z := z) fs selected q a t := by
  classical
  let C : ℂ := (((4 * Real.log X) ^ fs.countP
    smoothHeathBrownTypeILogFactor : ℝ) : ℂ)
  let G : (Fin fs.length → ℕ) → ℂ := fun v =>
    ((∏ i : Fin fs.length,
      smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ) *
      ((∏ i : Fin fs.length, v i : ℕ) : ℂ) ^
        smoothDyadicTwistExponent t *
      (polynomialOuterCutoff
        (((∏ i : Fin fs.length, v i : ℕ) : ℝ) / X) : ℂ)
  let e := smoothHeathBrownTypeISelectedTupleEquiv fs selected
  calc
    (∑ v ∈ (Fintype.piFinset
        (fun i : Fin fs.length =>
          smoothHeathBrownFactorFiniteSupport (fs.get i))).filter
        (fun v => (∏ i : Fin fs.length, v i) ≡ a [MOD q]), G v) =
      ∑ u ∈ smoothHeathBrownTypeIOuterTupleSet fs selected,
        ∑ n ∈ (smoothHeathBrownFactorFiniteSupport
            (fs.get selected)).filter
          (fun n => smoothHeathBrownTypeIOuterTupleProduct u * n ≡
            a [MOD q]),
          G (e.symm (n, u)) :=
            smoothHeathBrownTypeI_supportedTuple_residueSplitSelected
              fs selected q a G
    _ = ∑ u ∈ smoothHeathBrownTypeIOuterTupleSet fs selected,
        ∑ n ∈ (smoothHeathBrownFactorFiniteSupport
            (fs.get selected)).filter
          (fun n => smoothHeathBrownTypeIOuterTupleProduct u * n ≡
            a [MOD q]),
          C * smoothHeathBrownTypeIOuterTupleCoefficient
              (z := z) selected t u *
            smoothHeathBrownFreeFactorDiscreteTerm
              (fs.get selected)
              (smoothHeathBrownTypeIOuterTupleProduct u) t n := by
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro n hn
          let v := e.symm (n, u)
          have hnS : n ∈ smoothHeathBrownFactorFiniteSupport
              (fs.get selected) := (Finset.mem_filter.mp hn).1
          have hpos := smoothHeathBrownTypeISelectedTupleEquiv_symm_pos
            fs selected n hnS u hu
          have hterm := smoothHeathBrownTypeI_fixedTuple_eq_sourceTerm
            (z := z) hX fs selected hfree v hpos t
          dsimp [v, e] at hterm
          simp only [G, C, e]
          rw [smoothHeathBrownTypeISelectedTupleEquiv_symm_selected]
            at hterm
          have houter :
              (fun i : smoothHeathBrownTypeIOuterIndex selected =>
                  (e.symm (n, u)) i.1) = u := by
            funext i
            exact smoothHeathBrownTypeISelectedTupleEquiv_symm_outer
              fs selected n u i
          rw [houter] at hterm
          simpa [smoothHeathBrownTypeISelectedTupleEquiv_symm_product,
            smoothHeathBrownTypeIOuterTupleProduct,
            smoothHeathBrownTypeIOuterIndex, List.get_eq_getElem]
            using hterm.symm
    _ = C * smoothHeathBrownTypeIFactorizedComponentSum
          (z := z) fs selected q a t := by
          unfold smoothHeathBrownTypeIFactorizedComponentSum
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          rw [smoothHeathBrownFreeFactorSupportSolutions_sum_eq_exactSupport
            (z := z) (fs.get selected) hfree
            (smoothHeathBrownTypeIOuterTupleProduct u) q a t]
          rw [← mul_assoc, Finset.mul_sum]

#print axioms smoothLongFactor_twist_eq_outerPhase_div_sqrt
#print axioms smoothHeathBrown_normalizedFactor_restore
#print axioms smoothHeathBrown_normalizedFactorProduct_restore
#print axioms smoothLongFactor_outerProduct_mul_selected
#print axioms smoothHeathBrownFreeFactorCoefficient_eq_normalized
#print axioms smoothHeathBrownWeightedFactor_eq_normalized_twist
#print axioms smoothHeathBrownConvolutionFactors_apply_finMulAntidiag
#print axioms smoothHeathBrown_normalizedTuple_mellin_restore
#print axioms smoothHeathBrownTypeI_fixedTuple_eq_sourceTerm
#print axioms smoothLongFactor_sum_productFibers
#print axioms smoothLongFactor_piFinset_splitAt_sum
#print axioms smoothHeathBrownTypeI_supportedTuple_splitSelected
#print axioms smoothHeathBrownTypeISelectedTupleEquiv_symm_selected
#print axioms smoothHeathBrownTypeISelectedTupleEquiv_symm_outer
#print axioms smoothHeathBrownTypeISelectedTupleEquiv_symm_product
#print axioms smoothHeathBrownTypeISelectedTupleEquiv_symm_pos
#print axioms smoothHeathBrownFactorFiniteSupport_subset_freeScaleWindow
#print axioms smoothHeathBrownFreeFactorDiscreteTerm_eq_zero_outside_exactSupport
#print axioms smoothHeathBrownFreeFactorSupportSolutions_sum
#print axioms smoothHeathBrownFreeFactorSupportSolutions_sum_eq_exactSupport
#print axioms smoothHeathBrownTypeI_supportedTuple_residueSplitSelected
#print axioms arithmeticFunctionRealFinProduct_apply_supportedTupleSum
#print axioms smoothHeathBrownConvolutionFactors_apply_supportedTupleSum
#print axioms smoothHeathBrownConvolutionFactors_eq_zero_outside_supportedProduct
/-- The exact finite paper convolution sum, including its source coefficient,
coincides with the retained Type-I factorized component. -/
theorem smoothHeathBrownTypeI_finiteSourceSum_eq_factorized {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X)) (s : Fin fs.length)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X, fs.get s ≠ .mobius i)
    (q a : ℕ) (t : ℝ) (c : ℝ) :
    let T := Fintype.piFinset (fun i : Fin fs.length =>
      smoothHeathBrownFactorFiniteSupport (fs.get i))
    let p : (Fin fs.length → ℕ) → ℕ := fun v => ∏ i : Fin fs.length, v i
    let A := T.image p
    (∑ n ∈ A.filter (fun n => n ≡ a [MOD q]),
      (c : ℂ) * ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
        (n : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff ((n : ℝ) / X) : ℂ)) =
      smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs s q a t c := by
  classical
  intro T p A
  have hfiber := smoothHeathBrownTypeI_finiteSourceSum_eq_supportedTupleSum
    (z := z) hX fs q a t
  have hfactor := smoothHeathBrownTypeI_supportedTupleSum_eq_factorized
    (z := z) hX fs s hfree q a t
  dsimp at hfiber
  calc
    (∑ n ∈ A.filter (fun n => n ≡ a [MOD q]),
      (c : ℂ) * ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
        (n : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff ((n : ℝ) / X) : ℂ)) =
      (c : ℂ) * ∑ n ∈ A.filter (fun n => n ≡ a [MOD q]),
        ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
        (n : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ = (c : ℂ) *
      ∑ v ∈ T.filter (fun v => p v ≡ a [MOD q]),
        ((∏ i : Fin fs.length,
          smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ) *
        ((p v : ℕ) : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff (((p v : ℕ) : ℝ) / X) : ℂ) := by
          exact congrArg (fun x : ℂ => (c : ℂ) * x)
            (by simpa [T, p, A, List.get_eq_getElem] using hfiber)
    _ = smoothHeathBrownTypeISourceFactorizedComponentSum
          (z := z) fs s q a t c := by
          rw [show (∑ v ∈ T.filter (fun v => p v ≡ a [MOD q]),
            ((∏ i : Fin fs.length,
              smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ) *
              ((p v : ℕ) : ℂ) ^ smoothDyadicTwistExponent t *
              (polynomialOuterCutoff (((p v : ℕ) : ℝ) / X) : ℂ)) =
              (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
                smoothHeathBrownTypeIFactorizedComponentSum (z := z) fs s q a t by
                  simpa [T, p] using hfactor]
          unfold smoothHeathBrownTypeISourceFactorizedComponentSum
          ring

#print axioms smoothHeathBrownTypeI_finiteSourceSum_eq_supportedTupleSum
/-- The unbounded paper residue sum truncates exactly to the finite
product image because its convolution coefficient vanishes elsewhere. -/
theorem smoothHeathBrownTypeI_sourceTsum_eq_finiteSourceSum {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X)) (q a : ℕ)
    (t c : ℝ) :
    let T := Fintype.piFinset (fun i : Fin fs.length =>
      smoothHeathBrownFactorFiniteSupport (fs.get i))
    let p : (Fin fs.length → ℕ) → ℕ := fun v => ∏ i : Fin fs.length, v i
    let A := T.image p
    (∑' n : ℕ, if n ≡ a [MOD q] then
      (c : ℂ) * ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
        (n : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0) =
      ∑ n ∈ A.filter (fun n => n ≡ a [MOD q]),
        (c : ℂ) * ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
          (n : ℂ) ^ smoothDyadicTwistExponent t *
          (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) := by
  classical
  intro T p A
  rw [tsum_eq_sum (s := A.filter (fun n => n ≡ a [MOD q]))]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [(Finset.mem_filter.mp hn).2]
  · intro n hn
    by_cases hr : n ≡ a [MOD q]
    · have hnA : n ∉ A := by
        intro hA
        exact hn (Finset.mem_filter.mpr ⟨hA, hr⟩)
      have hconv : smoothHeathBrownConvolutionFactors z fs n = 0 := by
        exact smoothHeathBrownConvolutionFactors_eq_zero_outside_supportedProduct
          hX fs n hnA
      simp [hr, hconv]
    · simp [hr]

/-- The literal unbounded source residue sum equals the checked
factorized Type-I component at every frequency. Its summand has the
paper's coefficient, outer cutoff, and `n^(-1/2-it)` Mellin phase. -/
theorem smoothHeathBrownTypeI_sourceTsum_eq_factorized
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius i)
    (q a : ℕ) (t c : ℝ) :
    (∑' n : ℕ, if n ≡ a [MOD q] then
      (c : ℂ) * ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
        (n : ℂ) ^ smoothDyadicTwistExponent t *
        (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0) =
      smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c := by
  have ht := smoothHeathBrownTypeI_sourceTsum_eq_finiteSourceSum
    (z := z) hX fs q a t c
  have hf := smoothHeathBrownTypeI_finiteSourceSum_eq_factorized
    (z := z) hX fs selected hfree q a t c
  dsimp at ht hf
  exact ht.trans hf

/-- The advertised Type-I mean estimate for the literal unbounded
residue sum of the source convolution coefficient. -/
theorem smoothHeathBrownRetainedTypeISourceTsum_mean_le_K
    {X z : ℝ} (hX : 3 ≤ X) (hXexp : Real.exp 1 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ i : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius i)
    (hcount : fs.length ≤ 20)
    (hret : smoothHeathBrownSupportRetained (X := X) (z := z) fs)
    (hlong : (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected))
    (q a : ℕ) (hqpos : 0 < q) (W U η B D : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hj : 2 ≤ j) (hWdef : W = (Real.log X) ^ D)
    (hW : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hq : (q : ℝ) ≤ (Real.log X) ^ B)
    (hlarge :
      (2 / (3 * η / 4)) * Real.log
        ((2 : ℝ) ^ (23 : ℕ) *
          Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D)) ≤ Real.log X)
    (hlog : fs.countP smoothHeathBrownTypeILogFactor ≤ 1)
    (c : ℝ) (hc : |c| ≤ (2 : ℝ) ^ 10) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖∑' n : ℕ, if n ≡ a [MOD q] then
        (c : ℂ) * ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
          (n : ℂ) ^ smoothDyadicTwistExponent t *
          (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0‖) ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) *
        Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  have hmean := smoothHeathBrownRetainedTypeISourceComponent_mean_le_K
    hX hXexp fs selected hfree hcount hret hlong q a hqpos W U η B D j
    hη hB hD hj hWdef hW hWU hU hq hlarge hlog c hc
  have hident :
      (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
        ‖∑' n : ℕ, if n ≡ a [MOD q] then
          (c : ℂ) * ((smoothHeathBrownConvolutionFactors z fs n : ℝ) : ℂ) *
            (n : ℂ) ^ smoothDyadicTwistExponent t *
            (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0‖) =
      ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
        ‖smoothHeathBrownTypeISourceFactorizedComponentSum
          (z := z) fs selected q a t c‖ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    rw [smoothHeathBrownTypeI_sourceTsum_eq_factorized
      (z := z) hX fs selected hfree q a t c]
  rw [hident]
  exact hmean

/-- A retained long selected factor cannot be Möbius once its scale
exceeds twice the actual truncation cutoff. This is the precise
non-Möbius implication used in `lda:type-i`. -/
theorem smoothHeathBrownRetained_longFactor_nonMobius_of_cutoffScale
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hret : smoothHeathBrownSupportRetained (X := X) (z := z) fs)
    (hlong : (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected))
    (hz : 2 * z ≤
      (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ)) :
    ∀ j : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius j := by
  intro j hj
  rcases hret with ⟨n, hnlo, hnhi, hne⟩
  have hconv := smoothHeathBrownConvolutionFactors_apply_supportedTupleSum
    (z := z) hX fs n
  rw [hconv] at hne
  apply hne
  apply Finset.sum_eq_zero
  intro v hv
  have hvS := (Finset.mem_filter.mp hv).1
  have hsS : v selected ∈
      smoothHeathBrownFactorFiniteSupport (fs.get selected) :=
    Fintype.mem_piFinset.mp hvS selected
  rw [hj, smoothHeathBrownFactorFiniteSupport_eq_massWindow] at hsS
  have hNnonneg : 0 ≤ smoothHeathBrownFactorScale (.mobius j) := by
    have h := smoothHeathBrownFactorScale_ge_one (.mobius j)
    linarith
  have hlow := (mem_smoothFactorMassWindow hNnonneg (v selected)).mp hsS
  have hscale : 2 * z ≤ smoothHeathBrownFactorScale (.mobius j) := by
    rw [← hj]
    exact hz.trans hlong
  have hzn : z < (v selected : ℝ) := by linarith [hlow.1]
  have hzero : smoothHeathBrownFactorFunction z
      (fs.get selected) (v selected) = 0 := by
    rw [hj]
    simp [smoothHeathBrownFactorFunction,
      smoothHeathBrownMobiusFactor,
      truncatedMobius_apply_of_not_le (not_le.mpr hzn)]
  exact Finset.prod_eq_zero (Finset.mem_univ selected) hzero

#print axioms smoothHeathBrownTypeI_finiteSourceSum_eq_factorized
#print axioms smoothHeathBrownTypeI_sourceTsum_eq_finiteSourceSum
#print axioms smoothHeathBrownTypeI_sourceTsum_eq_factorized
#print axioms smoothHeathBrownRetainedTypeISourceTsum_mean_le_K
/-- The blueprint cutoff threshold `X ≥ 2^35` forces the retained
long selected factor to be non-Möbius. -/
theorem smoothHeathBrownRetained_longFactor_nonMobius_of_largeX {X : ℝ}
    (hX : (2 : ℝ) ^ 35 ≤ X)
    (fs : List (SmoothHeathBrownFactor X)) (s : Fin fs.length)
    (hcount : fs.length ≤ 20)
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fs)
    (hlong : (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get s)) :
    ∀ j : SmoothHeathBrownScaleIndex X, fs.get s ≠ .mobius j := by
  have hXnonneg : 0 ≤ X := by linarith
  have hXthree : 3 ≤ X := by linarith
  have hfsne : fs ≠ [] := by
    intro h
    subst fs
    exact Fin.elim0 s
  have hPlo := (smoothHeathBrownSupportRetained_scale_bounds
    hcount hfsne hXnonneg hret).1
  have hPnonneg : 0 ≤ smoothHeathBrownScaleProduct fs :=
    (smoothHeathBrownScaleProduct_pos fs).le
  have hcutpow := smoothHeathBrownLarge_cutoff_power_bound hX
  have hpow : (2 * dyadicMobiusCutoff X) ^ 8 ≤
      (smoothHeathBrownScaleProduct fs) ^ 3 := by
    exact hcutpow.trans (pow_le_pow_left₀ (by positivity) hPlo 3)
  have hpow_eq :
      ((smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ)) ^ 8 =
        (smoothHeathBrownScaleProduct fs) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hPnonneg]
    norm_num
  have hz : 2 * dyadicMobiusCutoff X ≤
      (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) := by
    have hznonneg : 0 ≤ 2 * dyadicMobiusCutoff X := by
      dsimp [dyadicMobiusCutoff]
      positivity
    have hrightnonneg : 0 ≤
        (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) := by positivity
    apply (pow_le_pow_iff_left₀ hznonneg hrightnonneg
      (by norm_num : 8 ≠ 0)).mp
    rw [hpow_eq]
    exact hpow
  exact smoothHeathBrownRetained_longFactor_nonMobius_of_cutoffScale
    hXthree fs s hret hlong hz

/-- The blueprint's long free-factor mean estimate for the literal
source sum, with its non-Möbius conclusion derived from retained
support and the explicit absolute cutoff threshold. -/
theorem smoothHeathBrownRetainedTypeISourceTsum_mean_le_K_of_largeX
    {X : ℝ} (hX : (2 : ℝ) ^ 35 ≤ X)
    (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hcount : fs.length ≤ 20)
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X) fs)
    (hlong : (smoothHeathBrownScaleProduct fs) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected))
    (q a : ℕ) (hqpos : 0 < q) (W U η B D : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hj : 2 ≤ j) (hWdef : W = (Real.log X) ^ D)
    (hW : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hq : (q : ℝ) ≤ (Real.log X) ^ B)
    (hlarge :
      (2 / (3 * η / 4)) * Real.log
        ((2 : ℝ) ^ (23 : ℕ) *
          Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D)) ≤ Real.log X)
    (hlog : fs.countP smoothHeathBrownTypeILogFactor ≤ 1)
    (c : ℝ) (hc : |c| ≤ (2 : ℝ) ^ 10) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖∑' n : ℕ, if n ≡ a [MOD q] then
        (c : ℂ) *
          ((smoothHeathBrownConvolutionFactors
              (dyadicMobiusCutoff X) fs n : ℝ) : ℂ) *
          (n : ℂ) ^ smoothDyadicTwistExponent t *
          (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0‖) ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) *
        Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  have hXthree : 3 ≤ X := by linarith
  have hXexp : Real.exp 1 ≤ X := by
    have hExp : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have hfree := smoothHeathBrownRetained_longFactor_nonMobius_of_largeX
    hX fs selected hcount hret hlong
  exact smoothHeathBrownRetainedTypeISourceTsum_mean_le_K
    hXthree hXexp fs selected hfree hcount hret hlong q a hqpos
    W U η B D j hη hB hD hj hWdef hW hWU hU hq hlarge
    hlog c hc

/-- Source Möbius labels have no logarithmic factor in the Type-I
normalization convention. -/
theorem smoothHeathBrownMobiusLabelFactors_typeILogCount_le_one
    {X : ℝ} (ν : SmoothHeathBrownMobiusLabel X) :
    (smoothHeathBrownMobiusLabelFactors ν).countP
      smoothHeathBrownTypeILogFactor ≤ 1 := by
  have hfun :
      (smoothHeathBrownTypeILogFactor : SmoothHeathBrownFactor X → Bool) =
        smoothHeathBrownIsLogarithm := by
    funext f
    cases f <;> rfl
  rw [hfun, smoothHeathBrownMobiusLabelFactors_log_count]
  omega

/-- Source von Mangoldt labels have exactly one logarithmic factor in
the Type-I normalization convention. -/
theorem smoothHeathBrownVonMangoldtLabelFactors_typeILogCount_le_one
    {X : ℝ} (ν : SmoothHeathBrownVonMangoldtLabel X) :
    (smoothHeathBrownVonMangoldtLabelFactors ν).countP
      smoothHeathBrownTypeILogFactor ≤ 1 := by
  have hfun :
      (smoothHeathBrownTypeILogFactor : SmoothHeathBrownFactor X → Bool) =
        smoothHeathBrownIsLogarithm := by
    funext f
    cases f <;> rfl
  rw [hfun, smoothHeathBrownVonMangoldtLabelFactors_log_count]

/-- The long Type-I source estimate for an actual retained Möbius
Heath--Brown label, with its factor count, coefficient bound, and
logarithmic count supplied by the checked decomposition. -/
theorem smoothHeathBrownMobiusLabel_longTypeISourceTsum_mean_le_K
    {X : ℝ} (hX : (2 : ℝ) ^ 35 ≤ X)
    (ν : SmoothHeathBrownMobiusLabel X)
    (selected : Fin (smoothHeathBrownMobiusLabelFactors ν).length)
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownMobiusLabelFactors ν))
    (hlong :
      (smoothHeathBrownScaleProduct
        (smoothHeathBrownMobiusLabelFactors ν)) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale
        ((smoothHeathBrownMobiusLabelFactors ν).get selected))
    (q a : ℕ) (hqpos : 0 < q) (W U η B D : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hj : 2 ≤ j) (hWdef : W = (Real.log X) ^ D)
    (hW : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hq : (q : ℝ) ≤ (Real.log X) ^ B)
    (hlarge :
      (2 / (3 * η / 4)) * Real.log
        ((2 : ℝ) ^ (23 : ℕ) *
          Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D)) ≤ Real.log X) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖∑' n : ℕ, if n ≡ a [MOD q] then
        (dyadicBinomialCoefficient ν.1 : ℂ) *
          ((smoothHeathBrownConvolutionFactors
              (dyadicMobiusCutoff X)
              (smoothHeathBrownMobiusLabelFactors ν) n : ℝ) : ℂ) *
          (n : ℂ) ^ smoothDyadicTwistExponent t *
          (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0‖) ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) *
        Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  exact smoothHeathBrownRetainedTypeISourceTsum_mean_le_K_of_largeX
    hX (smoothHeathBrownMobiusLabelFactors ν) selected
    (smoothHeathBrownMobiusFactorCount ν).2 hret hlong
    q a hqpos W U η B D j hη hB hD hj hWdef hW hWU hU hq hlarge
    (smoothHeathBrownMobiusLabelFactors_typeILogCount_le_one ν)
    (dyadicBinomialCoefficient ν.1)
    (smoothHeathBrownComponentCoefficient_abs_le ν.1)

/-- The long Type-I source estimate for an actual retained von Mangoldt
Heath--Brown label, with its factor count, coefficient bound, and
logarithmic count supplied by the checked decomposition. -/
theorem smoothHeathBrownVonMangoldtLabel_longTypeISourceTsum_mean_le_K
    {X : ℝ} (hX : (2 : ℝ) ^ 35 ≤ X)
    (ν : SmoothHeathBrownVonMangoldtLabel X)
    (selected : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length)
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownVonMangoldtLabelFactors ν))
    (hlong :
      (smoothHeathBrownScaleProduct
        (smoothHeathBrownVonMangoldtLabelFactors ν)) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale
        ((smoothHeathBrownVonMangoldtLabelFactors ν).get selected))
    (q a : ℕ) (hqpos : 0 < q) (W U η B D : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hj : 2 ≤ j) (hWdef : W = (Real.log X) ^ D)
    (hW : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hq : (q : ℝ) ≤ (Real.log X) ^ B)
    (hlarge :
      (2 / (3 * η / 4)) * Real.log
        ((2 : ℝ) ^ (23 : ℕ) *
          Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D)) ≤ Real.log X) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖∑' n : ℕ, if n ≡ a [MOD q] then
        (dyadicBinomialCoefficient ν.1 : ℂ) *
          ((smoothHeathBrownConvolutionFactors
              (dyadicMobiusCutoff X)
              (smoothHeathBrownVonMangoldtLabelFactors ν) n : ℝ) : ℂ) *
          (n : ℂ) ^ smoothDyadicTwistExponent t *
          (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0‖) ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) *
        Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  exact smoothHeathBrownRetainedTypeISourceTsum_mean_le_K_of_largeX
    hX (smoothHeathBrownVonMangoldtLabelFactors ν) selected
    (smoothHeathBrownVonMangoldtFactorCount ν).2 hret hlong
    q a hqpos W U η B D j hη hB hD hj hWdef hW hWU hU hq hlarge
    (smoothHeathBrownVonMangoldtLabelFactors_typeILogCount_le_one ν)
    (dyadicBinomialCoefficient ν.1)
    (smoothHeathBrownComponentCoefficient_abs_le ν.1)

/-- One explicit threshold for the source Type-I large-frequency mean
bound. The advertised blueprint permits dependence on `j`; this
choice is uniform in `j`. -/
noncomputable def smoothLongFactorTypeIThreshold
    (B D η : ℝ) : ℝ :=
  max ((2 : ℝ) ^ 35)
    (Real.exp ((2 / (3 * η / 4)) * Real.log
      ((2 : ℝ) ^ (23 : ℕ) *
        Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D))))

/-- The advertised source constant `K_j=2^40·5^20·C_j` is positive. -/
theorem smoothLongFactorTypeI_advertisedConstant_pos (j : ℕ) :
    0 < ((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) := by
  unfold Twisted.smoothDyadicC
  positivity

/-- Above the explicit Type-I threshold, both the absolute Möbius
cutoff threshold and the logarithmic absorption threshold hold. -/
theorem smoothLongFactorTypeIThreshold_conditions
    (B D η X : ℝ) (hX : smoothLongFactorTypeIThreshold B D η ≤ X) :
    (2 : ℝ) ^ 35 ≤ X ∧
      (2 / (3 * η / 4)) * Real.log
        ((2 : ℝ) ^ (23 : ℕ) *
          Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D)) ≤ Real.log X := by
  have hbase : (2 : ℝ) ^ 35 ≤ X :=
    (le_max_left _ _).trans hX
  have hexp : Real.exp ((2 / (3 * η / 4)) * Real.log
      ((2 : ℝ) ^ (23 : ℕ) *
        Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D))) ≤ X :=
    (le_max_right _ _).trans hX
  constructor
  · exact hbase
  · have hlog := Real.log_le_log (Real.exp_pos _) hexp
    simpa only [Real.log_exp] using hlog

/-- The literal Type-I source mean estimate for a retained Möbius
component above one explicit blueprint threshold. -/
theorem smoothHeathBrownMobiusLabel_longTypeI_mean_aboveThreshold
    {X : ℝ} (B D η : ℝ)
    (hX : smoothLongFactorTypeIThreshold B D η ≤ X)
    (ν : SmoothHeathBrownMobiusLabel X)
    (selected : Fin (smoothHeathBrownMobiusLabelFactors ν).length)
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownMobiusLabelFactors ν))
    (hlong :
      (smoothHeathBrownScaleProduct
        (smoothHeathBrownMobiusLabelFactors ν)) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale
        ((smoothHeathBrownMobiusLabelFactors ν).get selected))
    (q a : ℕ) (hqpos : 0 < q) (W U : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hj : 2 ≤ j) (hWdef : W = (Real.log X) ^ D)
    (hW : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖∑' n : ℕ, if n ≡ a [MOD q] then
        (dyadicBinomialCoefficient ν.1 : ℂ) *
          ((smoothHeathBrownConvolutionFactors
              (dyadicMobiusCutoff X)
              (smoothHeathBrownMobiusLabelFactors ν) n : ℝ) : ℂ) *
          (n : ℂ) ^ smoothDyadicTwistExponent t *
          (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0‖) ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) *
        Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  rcases smoothLongFactorTypeIThreshold_conditions B D η X hX with
    ⟨hXlarge, hlarge⟩
  exact smoothHeathBrownMobiusLabel_longTypeISourceTsum_mean_le_K
    hXlarge ν selected hret hlong q a hqpos W U η B D j
    hη hB hD hj hWdef hW hWU hU hq hlarge

/-- The literal Type-I source mean estimate for a retained von Mangoldt
component above one explicit blueprint threshold. -/
theorem smoothHeathBrownVonMangoldtLabel_longTypeI_mean_aboveThreshold
    {X : ℝ} (B D η : ℝ)
    (hX : smoothLongFactorTypeIThreshold B D η ≤ X)
    (ν : SmoothHeathBrownVonMangoldtLabel X)
    (selected : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length)
    (hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownVonMangoldtLabelFactors ν))
    (hlong :
      (smoothHeathBrownScaleProduct
        (smoothHeathBrownVonMangoldtLabelFactors ν)) ^ (3 / 8 : ℝ) ≤
      smoothHeathBrownFactorScale
        ((smoothHeathBrownVonMangoldtLabelFactors ν).get selected))
    (q a : ℕ) (hqpos : 0 < q) (W U : ℝ) (j : ℕ)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hj : 2 ≤ j) (hWdef : W = (Real.log X) ^ D)
    (hW : 2 ≤ W) (hWU : W ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U},
      ‖∑' n : ℕ, if n ≡ a [MOD q] then
        (dyadicBinomialCoefficient ν.1 : ℂ) *
          ((smoothHeathBrownConvolutionFactors
              (dyadicMobiusCutoff X)
              (smoothHeathBrownVonMangoldtLabelFactors ν) n : ℝ) : ℂ) *
          (n : ℂ) ^ smoothDyadicTwistExponent t *
          (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) else 0‖) ≤
      ((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) *
        Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) := by
  rcases smoothLongFactorTypeIThreshold_conditions B D η X hX with
    ⟨hXlarge, hlarge⟩
  exact smoothHeathBrownVonMangoldtLabel_longTypeISourceTsum_mean_le_K
    hXlarge ν selected hret hlong q a hqpos W U η B D j
    hη hB hD hj hWdef hW hWU hU hq hlarge

#print axioms smoothHeathBrownRetained_longFactor_nonMobius_of_cutoffScale
#print axioms smoothHeathBrownVonMangoldtLabel_longTypeI_mean_aboveThreshold
#print axioms smoothHeathBrownVonMangoldtLabel_longTypeISourceTsum_mean_le_K
#print axioms smoothLongFactorTypeIThreshold_conditions
#print axioms smoothLongFactorTypeI_advertisedConstant_pos
#print axioms smoothHeathBrownMobiusLabel_longTypeI_mean_aboveThreshold
#print axioms smoothHeathBrownRetained_longFactor_nonMobius_of_largeX
#print axioms smoothHeathBrownRetainedTypeISourceTsum_mean_le_K_of_largeX
#print axioms smoothHeathBrownMobiusLabelFactors_typeILogCount_le_one
#print axioms smoothHeathBrownVonMangoldtLabelFactors_typeILogCount_le_one
#print axioms smoothHeathBrownMobiusLabel_longTypeISourceTsum_mean_le_K
#print axioms smoothHeathBrownTypeI_supportedTupleSum_eq_factorized

end FractionalPrimes.Literature.DirichletAdapter

end
