module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorTypeIInnerSum
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorOuterMass
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-! Finite component assembly for the long free-factor branch of `lda:type-i`.
The factor tuple is indexed by an actual smooth Heath--Brown label list;
continuous integration and the large-`X` threshold are separate. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

private theorem smoothHeathBrownTypeICountP_ofFn_eq_zero
    {X : ℝ} {n : ℕ} (f : Fin n → SmoothHeathBrownFactor X)
    (hf : ∀ i, smoothHeathBrownTypeILogFactor (f i) = false) :
    (List.ofFn f).countP smoothHeathBrownTypeILogFactor = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  simp only [List.mem_ofFn'] at ha
  simp only [Set.mem_range] at ha
  rcases ha with ⟨i, rfl⟩
  simp [hf i]

private theorem smoothHeathBrownTypeIMobiusLogCount
    {X : ℝ} (ν : SmoothHeathBrownMobiusLabel X) :
    (smoothHeathBrownMobiusLabelFactors ν).countP
        smoothHeathBrownTypeILogFactor = 0 := by
  rw [smoothHeathBrownMobiusLabelFactors, List.countP_append]
  rw [smoothHeathBrownTypeICountP_ofFn_eq_zero
      (fun i : Fin ν.1.val => SmoothHeathBrownFactor.mobius (ν.2.1 i))
      (by intro i; rfl)]
  rw [smoothHeathBrownTypeICountP_ofFn_eq_zero
      (fun i : Fin (ν.1.val - 1) => SmoothHeathBrownFactor.theta (ν.2.2 i))
      (by intro i; rfl)]

private theorem smoothHeathBrownTypeIVonMangoldtLogCount
    {X : ℝ} (ν : SmoothHeathBrownVonMangoldtLabel X) :
    (smoothHeathBrownVonMangoldtLabelFactors ν).countP
        smoothHeathBrownTypeILogFactor = 1 := by
  rw [smoothHeathBrownVonMangoldtLabelFactors, List.countP_append,
    List.countP_append]
  rw [smoothHeathBrownTypeICountP_ofFn_eq_zero
      (fun i : Fin ν.1.val => SmoothHeathBrownFactor.mobius (ν.2.1.1 i))
      (by intro i; rfl)]
  rw [smoothHeathBrownTypeICountP_ofFn_eq_zero
      (fun i : Fin (ν.1.val - 1) => SmoothHeathBrownFactor.theta (ν.2.1.2 i))
      (by intro i; rfl)]
  simp [smoothHeathBrownTypeILogFactor]

/-- The pure imaginary Mellin phase carried by one complementary factor. -/
def smoothHeathBrownTypeIOuterPhase (t : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (-(t : ℂ) * Complex.I)

theorem smoothHeathBrownTypeIOuterPhase_norm_eq_one
    (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖smoothHeathBrownTypeIOuterPhase t n‖ = 1 := by
  rw [smoothHeathBrownTypeIOuterPhase, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _]
  have hre : (-(t : ℂ) * Complex.I).re = 0 := by simp
  rw [hre]
  simp

private theorem smoothHeathBrownFactorFiniteSupport_pos
    {X : ℝ} (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hn : n ∈ smoothHeathBrownFactorFiniteSupport f) : 0 < n := by
  have hN : 1 ≤ smoothHeathBrownFactorScale f :=
    smoothHeathBrownFactorScale_ge_one f
  have hNnonneg : 0 ≤ smoothHeathBrownFactorScale f := by linarith
  have hnWindow : n ∈ smoothFactorMassWindow (smoothHeathBrownFactorScale f) := by
    rw [← smoothHeathBrownFactorFiniteSupport_eq_massWindow]
    exact hn
  have hnReal :=
    (mem_smoothFactorMassWindow hNnonneg n).mp hnWindow |>.1
  have hhalf : 0 < smoothHeathBrownFactorScale f / 2 := by positivity
  have hnRealPos : 0 < (n : ℝ) := lt_trans hhalf hnReal
  exact_mod_cast hnRealPos

/-- Uniformize the fixed-factor estimate by replacing the reduced modulus by
the original modulus. -/
theorem smoothHeathBrown_freeFactor_finite_inner_sum_norm_le_modulus
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m q a : ℕ) (hq : 0 < q) (t : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (ht : 1 ≤ |t|) :
    ‖∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions f m q a,
        smoothHeathBrownFreeFactorDiscreteTerm f m t n.1‖ ≤
      Twisted.smoothDyadicC j *
        Real.sqrt (smoothHeathBrownFactorScale f) *
          (|t| ^ (-(j : ℝ)) +
            (q : ℝ) ^ (j - 1) *
              ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j) := by
  let q' : ℕ := q / Nat.gcd m q
  have hq'pos : 0 < q' := by
    dsimp [q']
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq (Nat.gcd_dvd_right m q)
    · exact Nat.gcd_pos_of_pos_right m hq
  have hq'one : 1 ≤ q' := by omega
  have hq'le : q' ≤ q := by
    dsimp [q']
    exact Nat.div_le_self _ _
  have hq'realpos : 0 < (q' : ℝ) := by exact_mod_cast hq'pos
  have hq'realone : 1 ≤ (q' : ℝ) := by exact_mod_cast hq'one
  have hq'realle : (q' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'le
  have hInv : (q' : ℝ)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ hq'realone
  have hPow : (q' : ℝ) ^ (j - 1) ≤ (q : ℝ) ^ (j - 1) :=
    pow_le_pow_left₀ (by positivity) hq'realle _
  have hBase := smoothHeathBrown_freeFactor_finite_inner_sum_norm_le
    hX f hfree m q a hq t j hj ht
  have hU : 0 ≤ |t| ^ (-(j : ℝ)) := by positivity
  have hscalePos : 0 < smoothHeathBrownFactorScale f :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (smoothHeathBrownFactorScale_ge_one f)
  have hVbase : 0 ≤ (1 + |t|) / smoothHeathBrownFactorScale f :=
    div_nonneg (by positivity) hscalePos.le
  have hV : 0 ≤ ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j :=
    pow_nonneg hVbase j
  have hbracket :
      (q' : ℝ)⁻¹ * |t| ^ (-(j : ℝ)) +
          (q' : ℝ) ^ (j - 1) *
            ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j ≤
        |t| ^ (-(j : ℝ)) +
          (q : ℝ) ^ (j - 1) *
            ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j := by
    calc
      _ ≤ 1 * |t| ^ (-(j : ℝ)) +
          (q : ℝ) ^ (j - 1) *
            ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j :=
          add_le_add
            (mul_le_mul_of_nonneg_right hInv hU)
            (mul_le_mul_of_nonneg_right hPow hV)
      _ = _ := by ring
  have hC : 0 ≤ Twisted.smoothDyadicC j := by
    unfold Twisted.smoothDyadicC
    positivity
  have hpref : 0 ≤ Twisted.smoothDyadicC j *
      Real.sqrt (smoothHeathBrownFactorScale f) :=
    mul_nonneg hC (Real.sqrt_nonneg _)
  exact hBase.trans (mul_le_mul_of_nonneg_left hbracket hpref)

#print axioms smoothHeathBrown_freeFactor_finite_inner_sum_norm_le_modulus

/-- An index in the factor list other than the selected long factor. -/
abbrev smoothHeathBrownTypeIOuterIndex {k : ℕ} (selected : Fin k) :=
  {i : Fin k // i ∈ Finset.univ.erase selected}

/-- The finite Cartesian product of source support windows for the
complementary factors. -/
noncomputable def smoothHeathBrownTypeIOuterTupleSet
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) :
    Finset (smoothHeathBrownTypeIOuterIndex selected → ℕ) :=
  Fintype.piFinset (fun i : smoothHeathBrownTypeIOuterIndex selected =>
    smoothHeathBrownFactorFiniteSupport (fs.get i.1))

/-- The product of the complementary factor arguments. -/
noncomputable def smoothHeathBrownTypeIOuterTupleProduct
    {X : ℝ} {fs : List (SmoothHeathBrownFactor X)}
    {selected : Fin fs.length}
    (u : smoothHeathBrownTypeIOuterIndex selected → ℕ) : ℕ :=
  ∏ i : smoothHeathBrownTypeIOuterIndex selected, u i

/-- The normalized complementary-factor coefficient, including its exact
pure imaginary frequency. -/
noncomputable def smoothHeathBrownTypeIOuterTupleCoefficient
    {X z : ℝ} {fs : List (SmoothHeathBrownFactor X)}
    (selected : Fin fs.length) (t : ℝ)
    (u : smoothHeathBrownTypeIOuterIndex selected → ℕ) : ℂ :=
  ∏ i : smoothHeathBrownTypeIOuterIndex selected,
    smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get i.1)
      (smoothHeathBrownTypeIOuterPhase t) (u i)

/-- The exact finite factorized Dirichlet sum for one smooth-HB component,
with the selected factor summed on its actual congruence progression. -/
noncomputable def smoothHeathBrownTypeIFactorizedComponentSum
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (q a : ℕ) (t : ℝ) : ℂ :=
  ∑ u ∈ smoothHeathBrownTypeIOuterTupleSet fs selected,
    smoothHeathBrownTypeIOuterTupleCoefficient (z := z) selected t u *
      (∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions
          (fs.get selected) (smoothHeathBrownTypeIOuterTupleProduct u) q a,
        smoothHeathBrownFreeFactorDiscreteTerm (fs.get selected)
          (smoothHeathBrownTypeIOuterTupleProduct u) t n.1)

/-- Finite assembly of the fixed-factor progression estimate against all
complementary source masses. The profile constant, frequency hypotheses, and
the exact scale ratio `P/N` are retained. -/
theorem smoothHeathBrownTypeIFactorizedComponentSum_norm_le
    {X z : ℝ} (hX : 3 ≤ X) (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, fs.get selected ≠ .mobius j)
    (hcount : fs.length ≤ 20)
    (q a : ℕ) (hq : 0 < q) (t : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (ht : 1 ≤ |t|) :
    ‖smoothHeathBrownTypeIFactorizedComponentSum
        (z := z) fs selected q a t‖ ≤
      5 ^ 19 * Real.sqrt
          ((∏ i : Fin fs.length,
              smoothHeathBrownFactorScale (fs.get i)) /
            smoothHeathBrownFactorScale (fs.get selected)) *
        (Twisted.smoothDyadicC j *
          Real.sqrt (smoothHeathBrownFactorScale (fs.get selected)) *
            (|t| ^ (-(j : ℝ)) +
              (q : ℝ) ^ (j - 1) *
                ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j)) := by
  classical
  let I := smoothHeathBrownTypeIOuterIndex selected
  let T := smoothHeathBrownTypeIOuterTupleSet fs selected
  let ω : Fin fs.length → ℕ → ℂ := fun _ n => smoothHeathBrownTypeIOuterPhase t n
  let mass : Fin fs.length → ℝ := fun i =>
    smoothHeathBrownTypeIFactorMass (z := z) (fs.get i) (ω i)
  let B : ℝ := Twisted.smoothDyadicC j *
      Real.sqrt (smoothHeathBrownFactorScale (fs.get selected)) *
        (|t| ^ (-(j : ℝ)) +
          (q : ℝ) ^ (j - 1) *
            ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j)
  have hω : ∀ i n, n ∈ smoothHeathBrownFactorFiniteSupport (fs.get i) →
      ‖ω i n‖ ≤ 1 := by
    intro i n hn
    have hnpos := smoothHeathBrownFactorFiniteSupport_pos (fs.get i) hn
    have hnorm := smoothHeathBrownTypeIOuterPhase_norm_eq_one t hnpos
    simpa [ω] using hnorm.le
  have hN : 1 ≤ smoothHeathBrownFactorScale (fs.get selected) :=
    smoothHeathBrownFactorScale_ge_one (fs.get selected)
  have hC : 0 ≤ Twisted.smoothDyadicC j := by
    unfold Twisted.smoothDyadicC
    positivity
  have hscalePos : 0 < smoothHeathBrownFactorScale (fs.get selected) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hN
  have hbracketNonneg : 0 ≤
      |t| ^ (-(j : ℝ)) +
        (q : ℝ) ^ (j - 1) *
          ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j := by
    apply add_nonneg
    · positivity
    · apply mul_nonneg
      · positivity
      · apply pow_nonneg
        exact div_nonneg (by positivity) hscalePos.le
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hbracketNonneg
  have hInner : ∀ u ∈ T,
      ‖∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions
          (fs.get selected) (smoothHeathBrownTypeIOuterTupleProduct u) q a,
        smoothHeathBrownFreeFactorDiscreteTerm (fs.get selected)
          (smoothHeathBrownTypeIOuterTupleProduct u) t n.1‖ ≤ B := by
    intro u hu
    exact smoothHeathBrown_freeFactor_finite_inner_sum_norm_le_modulus
      hX (fs.get selected) hfree
      (smoothHeathBrownTypeIOuterTupleProduct u) q a hq t j hj ht
  have hsumfactor :
      (∑ u ∈ T,
        ∏ i : I,
          ‖smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get i.1)
              (ω i.1) (u i)‖) =
        ∏ i : I,
          smoothHeathBrownTypeIFactorMass (z := z) (fs.get i.1) (ω i.1) := by
    let S : I → Finset ℕ := fun i => smoothHeathBrownFactorFiniteSupport (fs.get i.1)
    let g : ∀ i : I, ℕ → ℝ := fun i n =>
      ‖smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get i.1)
        (ω i.1) n‖
    calc
      (∑ u ∈ T,
        ∏ i : I,
          ‖smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get i.1)
              (ω i.1) (u i)‖) =
        ∑ u ∈ Fintype.piFinset S, ∏ i : I, g i (u i) := by
          simp [T, I, S, g, smoothHeathBrownTypeIOuterTupleSet]
      _ = ∏ i : I, ∑ n ∈ S i, g i n := by
          symm
          exact Finset.prod_univ_sum S g
      _ = ∏ i : I,
          smoothHeathBrownTypeIFactorMass (z := z) (fs.get i.1) (ω i.1) := by
          simp [g, S, smoothHeathBrownTypeIFactorMass]
  have htupleNorm (u : I → ℕ) :
      ‖smoothHeathBrownTypeIOuterTupleCoefficient (z := z) selected t u‖ =
        ∏ i : I,
          ‖smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get i.1)
              (ω i.1) (u i)‖ := by
    have hI : (Finset.univ : Finset I) = (Finset.univ.erase selected).attach := by
      ext i
      simp [I, smoothHeathBrownTypeIOuterIndex]
    simp [smoothHeathBrownTypeIOuterTupleCoefficient, norm_prod, ω, hI] <;> rfl
  have hmassFin :
      ∏ i : I,
        smoothHeathBrownTypeIFactorMass (z := z) (fs.get i.1) (ω i.1) ≤
      5 ^ 19 * Real.sqrt
        ((∏ i : Fin fs.length,
            smoothHeathBrownFactorScale (fs.get i)) /
          smoothHeathBrownFactorScale (fs.get selected)) := by
    have hbase := smoothHeathBrownTypeIOuterFactorMassProduct
      (z := z) hX hcount (fun i => fs.get i) selected ω hω
    calc
      _ = ∏ i ∈ Finset.univ.erase selected, mass i := by
        simpa [I, smoothHeathBrownTypeIOuterIndex, mass] using
          (Finset.prod_coe_sort (Finset.univ.erase selected) mass)
      _ ≤ 5 ^ 19 * Real.sqrt
            ((∏ i : Fin fs.length,
                smoothHeathBrownFactorScale (fs.get i)) /
              smoothHeathBrownFactorScale (fs.get selected)) := by
        simpa [mass] using hbase
  calc
    ‖smoothHeathBrownTypeIFactorizedComponentSum (z := z) fs selected q a t‖ ≤
        ∑ u ∈ T,
          ‖smoothHeathBrownTypeIOuterTupleCoefficient
              (z := z) selected t u *
            (∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions
                (fs.get selected) (smoothHeathBrownTypeIOuterTupleProduct u) q a,
              smoothHeathBrownFreeFactorDiscreteTerm (fs.get selected)
                (smoothHeathBrownTypeIOuterTupleProduct u) t n.1)‖ := by
          unfold smoothHeathBrownTypeIFactorizedComponentSum
          exact norm_sum_le _ _
    _ = ∑ u ∈ T,
          ‖smoothHeathBrownTypeIOuterTupleCoefficient
              (z := z) selected t u‖ *
            ‖∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions
                (fs.get selected) (smoothHeathBrownTypeIOuterTupleProduct u) q a,
              smoothHeathBrownFreeFactorDiscreteTerm (fs.get selected)
                (smoothHeathBrownTypeIOuterTupleProduct u) t n.1‖ := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [norm_mul]
    _ ≤ ∑ u ∈ T,
          ‖smoothHeathBrownTypeIOuterTupleCoefficient
              (z := z) selected t u‖ * B := by
          apply Finset.sum_le_sum
          intro u hu
          apply mul_le_mul_of_nonneg_left (hInner u hu)
          exact norm_nonneg _
    _ = B * (∑ u ∈ T,
          ‖smoothHeathBrownTypeIOuterTupleCoefficient
              (z := z) selected t u‖) := by
          calc
            (∑ u ∈ T,
              ‖smoothHeathBrownTypeIOuterTupleCoefficient
                  (z := z) selected t u‖ * B) =
                (∑ u ∈ T,
                  ‖smoothHeathBrownTypeIOuterTupleCoefficient
                      (z := z) selected t u‖) * B := by
                    rw [Finset.sum_mul]
            _ = _ := by ring
    _ = B * (∑ u ∈ T,
          ∏ i : I,
            ‖smoothHeathBrownWeightedFactorCoefficient (z := z) (fs.get i.1)
                (ω i.1) (u i)‖) := by
          congr 1
          apply Finset.sum_congr rfl
          intro u hu
          rw [htupleNorm]
    _ = B * ∏ i : I,
          smoothHeathBrownTypeIFactorMass (z := z) (fs.get i.1) (ω i.1) := by
          rw [hsumfactor]
    _ ≤ B * (5 ^ 19 * Real.sqrt
          ((∏ i : Fin fs.length,
              smoothHeathBrownFactorScale (fs.get i)) /
            smoothHeathBrownFactorScale (fs.get selected))) :=
          mul_le_mul_of_nonneg_left hmassFin hBnonneg
    _ = _ := by ring

#print axioms smoothHeathBrownTypeIFactorizedComponentSum_norm_le

/-- Restore the exact source coefficient and every logarithmic normalization
to the factorized Type-I component sum. The exponent is the actual number of
logarithmic tags in the factor list. -/
noncomputable def smoothHeathBrownTypeISourceFactorizedComponentSum
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (q a : ℕ) (t : ℝ) (c : ℝ) : ℂ :=
  (c : ℂ) *
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
      smoothHeathBrownTypeIFactorizedComponentSum
        (z := z) fs selected q a t

/-- Pointwise source-scaled finite-component bound, retaining the exact
coefficient, logarithmic count, scale ratio, modulus, and frequency cost. -/
theorem smoothHeathBrownTypeISourceFactorizedComponentSum_norm_le
    {X z : ℝ} (hX : 3 ≤ X) (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, fs.get selected ≠ .mobius j)
    (hcount : fs.length ≤ 20)
    (q a : ℕ) (hq : 0 < q) (t : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (ht : 1 ≤ |t|) (c : ℝ) :
    ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖ ≤
      |c| * (4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor *
        (5 ^ 19 * Real.sqrt
          ((∏ i : Fin fs.length,
              smoothHeathBrownFactorScale (fs.get i)) /
            smoothHeathBrownFactorScale (fs.get selected))) *
        (Twisted.smoothDyadicC j *
          Real.sqrt (smoothHeathBrownFactorScale (fs.get selected)) *
            (|t| ^ (-(j : ℝ)) +
              (q : ℝ) ^ (j - 1) *
                ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j)) := by
  have hXpos : 0 < X := by linarith
  have hlog : 0 < 4 * Real.log X := by
    apply mul_pos (by norm_num)
    exact Real.log_pos (by linarith)
  have hpow : 0 ≤ (4 * Real.log X) ^
      fs.countP smoothHeathBrownTypeILogFactor := pow_nonneg hlog.le _
  have hsum := smoothHeathBrownTypeIFactorizedComponentSum_norm_le
    (z := z) hX fs selected hfree hcount q a hq t j hj ht
  change ‖(c : ℂ) *
      (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        smoothHeathBrownTypeIFactorizedComponentSum
          (z := z) fs selected q a t‖ ≤ _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpow]
  calc
    |c| * (4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor *
        ‖smoothHeathBrownTypeIFactorizedComponentSum
          (z := z) fs selected q a t‖ ≤
      |c| * (4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor *
        ((5 ^ 19 * Real.sqrt
          ((∏ i : Fin fs.length,
              smoothHeathBrownFactorScale (fs.get i)) /
            smoothHeathBrownFactorScale (fs.get selected))) *
          (Twisted.smoothDyadicC j *
            Real.sqrt (smoothHeathBrownFactorScale (fs.get selected)) *
              (|t| ^ (-(j : ℝ)) +
                (q : ℝ) ^ (j - 1) *
                  ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j))) :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (abs_nonneg _) hpow)
    _ = _ := by ring

#print axioms smoothHeathBrownTypeISourceFactorizedComponentSum_norm_le

/-- Coarse source form using only the source facts that a component has at
most one logarithmic tag and its binomial coefficient is bounded by `2^10`.
The exact label wrappers below supply these two facts. -/
theorem smoothHeathBrownTypeISourceFactorizedComponentSum_norm_le_coarse
    {X z : ℝ} (hX : 3 ≤ X) (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, fs.get selected ≠ .mobius j)
    (hcount : fs.length ≤ 20)
    (q a : ℕ) (hq : 0 < q) (t : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (ht : 1 ≤ |t|)
    (hlog : fs.countP smoothHeathBrownTypeILogFactor ≤ 1)
    (c : ℝ) (hc : |c| ≤ (2 : ℝ) ^ 10) :
    ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖ ≤
      (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt
          ((∏ i : Fin fs.length,
              smoothHeathBrownFactorScale (fs.get i)) /
            smoothHeathBrownFactorScale (fs.get selected))) *
        (Twisted.smoothDyadicC j *
          Real.sqrt (smoothHeathBrownFactorScale (fs.get selected)) *
            (|t| ^ (-(j : ℝ)) +
              (q : ℝ) ^ (j - 1) *
                ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j)) := by
  have hsum := smoothHeathBrownTypeISourceFactorizedComponentSum_norm_le
    (z := z) hX fs selected hfree hcount q a hq t j hj ht c
  have hLpos : 0 < 4 * Real.log X := by
    apply mul_pos (by norm_num)
    exact Real.log_pos (by linarith)
  have hLone : 1 ≤ 4 * Real.log X := by
    have hlogX : 1 ≤ Real.log X := by
      apply (Real.le_log_iff_exp_le (by linarith : 0 < X)).2
      exact le_of_lt (lt_of_lt_of_le Real.exp_one_lt_three hX)
    linarith
  have hpower : (4 * Real.log X) ^
      fs.countP smoothHeathBrownTypeILogFactor ≤ 4 * Real.log X := by
    rcases Nat.eq_zero_or_pos (fs.countP smoothHeathBrownTypeILogFactor) with hz | hp
    · rw [hz]
      simpa using hLone
    · have hone : fs.countP smoothHeathBrownTypeILogFactor = 1 := by omega
      simpa [hone]
  have hscalar : |c| * (4 * Real.log X) ^
      fs.countP smoothHeathBrownTypeILogFactor ≤
        (2 : ℝ) ^ 10 * (4 * Real.log X) := by
    calc
      _ ≤ (2 : ℝ) ^ 10 * (4 * Real.log X) ^
            fs.countP smoothHeathBrownTypeILogFactor :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hLpos.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)
  have hC : 0 ≤ Twisted.smoothDyadicC j := by
    unfold Twisted.smoothDyadicC
    positivity
  have hscalePos : 0 < smoothHeathBrownFactorScale (fs.get selected) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (smoothHeathBrownFactorScale_ge_one (fs.get selected))
  have hbaseNonneg : 0 ≤
      (|t| ^ (-(j : ℝ)) +
        (q : ℝ) ^ (j - 1) *
          ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j) := by
    apply add_nonneg
    · exact Real.rpow_nonneg (abs_nonneg t) _
    · apply mul_nonneg
      · positivity
      · exact pow_nonneg
          (div_nonneg (by positivity) hscalePos.le) j
  have hremain : 0 ≤
      (5 ^ 19 * Real.sqrt
        ((∏ i : Fin fs.length, smoothHeathBrownFactorScale (fs.get i)) /
          smoothHeathBrownFactorScale (fs.get selected))) *
        (Twisted.smoothDyadicC j *
          Real.sqrt (smoothHeathBrownFactorScale (fs.get selected)) *
            (|t| ^ (-(j : ℝ)) +
              (q : ℝ) ^ (j - 1) *
                ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j)) := by
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hbaseNonneg)
  calc
    ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := z) fs selected q a t c‖ ≤
      (|c| * (4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor) *
        ((5 ^ 19 * Real.sqrt
          ((∏ i : Fin fs.length,
              smoothHeathBrownFactorScale (fs.get i)) /
            smoothHeathBrownFactorScale (fs.get selected))) *
          (Twisted.smoothDyadicC j *
            Real.sqrt (smoothHeathBrownFactorScale (fs.get selected)) *
              (|t| ^ (-(j : ℝ)) +
                (q : ℝ) ^ (j - 1) *
                  ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j))) := by
      simpa [mul_assoc] using hsum
    _ ≤ ((2 : ℝ) ^ 10 * (4 * Real.log X)) *
        ((5 ^ 19 * Real.sqrt
          ((∏ i : Fin fs.length,
              smoothHeathBrownFactorScale (fs.get i)) /
            smoothHeathBrownFactorScale (fs.get selected))) *
          (Twisted.smoothDyadicC j *
            Real.sqrt (smoothHeathBrownFactorScale (fs.get selected)) *
              (|t| ^ (-(j : ℝ)) +
                (q : ℝ) ^ (j - 1) *
                  ((1 + |t|) / smoothHeathBrownFactorScale (fs.get selected)) ^ j))) :=
      mul_le_mul_of_nonneg_right hscalar hremain
    _ = _ := by ring

#print axioms smoothHeathBrownTypeISourceFactorizedComponentSum_norm_le_coarse

/-- The actual Möbius label component, with its source coefficient and
zero logarithmic normalization restored. The selected factor remains an
explicit long-factor premise. -/
theorem smoothHeathBrownMobiusLabelTypeIComponent_norm_le
    {X : ℝ} (hX : 3 ≤ X) (ν : SmoothHeathBrownMobiusLabel X)
    (selected : Fin (smoothHeathBrownMobiusLabelFactors ν).length)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X,
      (smoothHeathBrownMobiusLabelFactors ν).get selected ≠ .mobius j)
    (q a : ℕ) (hq : 0 < q) (t : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (ht : 1 ≤ |t|) :
    ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := dyadicMobiusCutoff X)
        (smoothHeathBrownMobiusLabelFactors ν) selected q a t
        (dyadicBinomialCoefficient ν.1)‖ ≤
      (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt
          ((∏ i : Fin (smoothHeathBrownMobiusLabelFactors ν).length,
              smoothHeathBrownFactorScale
                ((smoothHeathBrownMobiusLabelFactors ν).get i)) /
            smoothHeathBrownFactorScale
              ((smoothHeathBrownMobiusLabelFactors ν).get selected))) *
        (Twisted.smoothDyadicC j *
          Real.sqrt (smoothHeathBrownFactorScale
            ((smoothHeathBrownMobiusLabelFactors ν).get selected)) *
            (|t| ^ (-(j : ℝ)) +
              (q : ℝ) ^ (j - 1) *
                ((1 + |t|) / smoothHeathBrownFactorScale
                  ((smoothHeathBrownMobiusLabelFactors ν).get selected)) ^ j)) := by
  have hlogCount := smoothHeathBrownTypeIMobiusLogCount ν
  have hcoeff : |dyadicBinomialCoefficient ν.1| ≤ (2 : ℝ) ^ 10 :=
    dyadicBinomialCoefficient_abs_le ν.1
  have hbound := smoothHeathBrownTypeISourceFactorizedComponentSum_norm_le_coarse
    (z := dyadicMobiusCutoff X) hX (smoothHeathBrownMobiusLabelFactors ν) selected hfree
    (smoothHeathBrownMobiusFactorCount ν).2 q a hq t j hj ht
    (by omega) (dyadicBinomialCoefficient ν.1) hcoeff
  simpa [smoothHeathBrownTypeISourceFactorizedComponentSum, hlogCount] using hbound

#print axioms smoothHeathBrownMobiusLabelTypeIComponent_norm_le

/-- The actual von Mangoldt label component, with the unique source
logarithmic normalization and binomial coefficient restored. -/
theorem smoothHeathBrownVonMangoldtLabelTypeIComponent_norm_le
    {X : ℝ} (hX : 3 ≤ X) (ν : SmoothHeathBrownVonMangoldtLabel X)
    (selected : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X,
      (smoothHeathBrownVonMangoldtLabelFactors ν).get selected ≠ .mobius j)
    (q a : ℕ) (hq : 0 < q) (t : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (ht : 1 ≤ |t|) :
    ‖smoothHeathBrownTypeISourceFactorizedComponentSum
        (z := dyadicMobiusCutoff X)
        (smoothHeathBrownVonMangoldtLabelFactors ν) selected q a t
        (dyadicBinomialCoefficient ν.1)‖ ≤
      (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (5 ^ 19 * Real.sqrt
          ((∏ i : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length,
              smoothHeathBrownFactorScale
                ((smoothHeathBrownVonMangoldtLabelFactors ν).get i)) /
            smoothHeathBrownFactorScale
              ((smoothHeathBrownVonMangoldtLabelFactors ν).get selected))) *
        (Twisted.smoothDyadicC j *
          Real.sqrt (smoothHeathBrownFactorScale
            ((smoothHeathBrownVonMangoldtLabelFactors ν).get selected)) *
            (|t| ^ (-(j : ℝ)) +
              (q : ℝ) ^ (j - 1) *
                ((1 + |t|) / smoothHeathBrownFactorScale
                  ((smoothHeathBrownVonMangoldtLabelFactors ν).get selected)) ^ j)) := by
  have hlogCount := smoothHeathBrownTypeIVonMangoldtLogCount ν
  have hcoeff : |dyadicBinomialCoefficient ν.1| ≤ (2 : ℝ) ^ 10 :=
    dyadicBinomialCoefficient_abs_le ν.1
  have hbound := smoothHeathBrownTypeISourceFactorizedComponentSum_norm_le_coarse
    (z := dyadicMobiusCutoff X) hX (smoothHeathBrownVonMangoldtLabelFactors ν) selected hfree
    (smoothHeathBrownVonMangoldtFactorCount ν).2 q a hq t j hj ht
    (by omega) (dyadicBinomialCoefficient ν.1) hcoeff
  simpa [smoothHeathBrownTypeISourceFactorizedComponentSum, hlogCount] using hbound

#print axioms smoothHeathBrownVonMangoldtLabelTypeIComponent_norm_le

end FractionalPrimes.Literature.DirichletAdapter

end
