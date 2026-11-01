module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorProfileResidueAssembly
public import FractionalPrimes.Literature.DirichletAdapter.SmoothDyadicResidueQuadrature
import Mathlib.Tactic

/-! Source-exact pointwise bound for the fixed-factor inner progression sum
in the long-factor Type-I branch. -/

@[expose] public section

open MeasureTheory
open scoped CompactlySupported

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- If the outer-cutoff parameter is outside its exact interval, the smooth
free-factor profile vanishes identically. -/
theorem smoothHeathBrownFreeFactorProfile_eq_zero_of_parameter_outside
    {v a b : ℝ}
    (hv : ¬ ((3 / 8 : ℝ) ≤ v ∧ v ≤ 5)) :
    ∀ u : ℝ, smoothDyadicH v a b u = 0 := by
  by_cases hvlo : v < 3 / 8
  · intro u
    by_cases hlow : u ≤ (1 / 2 : ℝ)
    · exact smoothDyadicH_eq_zero_of_le_half hlow
    by_cases hhigh : 2 ≤ u
    · exact smoothDyadicH_eq_zero_of_two_le hhigh
    have huHalf : (1 / 2 : ℝ) < u := lt_of_not_ge hlow
    have huTwo : u < 2 := lt_of_not_ge hhigh
    have huPos : 0 < u := by linarith
    have hvu : v * u < 3 / 4 := by
      calc
        v * u < (3 / 8 : ℝ) * u := mul_lt_mul_of_pos_right hvlo huPos
        _ ≤ (3 / 8 : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left (le_of_lt huTwo) (by norm_num)
        _ = 3 / 4 := by norm_num
    have hcut : polynomialOuterCutoff (v * u) = 0 :=
      polynomialOuterCutoff_eq_zero_of_lt_left hvu
    simp [smoothDyadicH, huPos, hcut]
  · have hvlo' : (3 / 8 : ℝ) ≤ v := le_of_not_gt hvlo
    have hvhi : 5 < v := by
      by_contra h
      exact hv ⟨hvlo', le_of_not_gt h⟩
    intro u
    by_cases hlow : u ≤ (1 / 2 : ℝ)
    · exact smoothDyadicH_eq_zero_of_le_half hlow
    by_cases hhigh : 2 ≤ u
    · exact smoothDyadicH_eq_zero_of_two_le hhigh
    have huHalf : (1 / 2 : ℝ) < u := lt_of_not_ge hlow
    have huTwo : u < 2 := lt_of_not_ge hhigh
    have huPos : 0 < u := by linarith
    have hvu : (5 / 2 : ℝ) < v * u := by
      calc
        (5 / 2 : ℝ) = 5 * (1 / 2 : ℝ) := by norm_num
        _ < v * (1 / 2 : ℝ) := mul_lt_mul_of_pos_right hvhi (by norm_num)
        _ ≤ v * u :=
          mul_le_mul_of_nonneg_left huHalf.le (by linarith)
    have hcut : polynomialOuterCutoff (v * u) = 0 :=
      polynomialOuterCutoff_eq_zero_of_lt_right hvu
    simp [smoothDyadicH, huPos, hcut]

#print axioms smoothHeathBrownFreeFactorProfile_eq_zero_of_parameter_outside

/-- Consequently every Mellin-twisted discrete free-factor term vanishes
when its profile parameter is outside `[3/8,5]`. -/
theorem smoothHeathBrownFreeFactorDiscreteTerm_eq_zero_of_parameter_outside
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m : ℕ) (hv :
      ¬ ((3 / 8 : ℝ) ≤ (m : ℝ) * smoothHeathBrownFactorScale f / X ∧
        (m : ℝ) * smoothHeathBrownFactorScale f / X ≤ 5))
    (t : ℝ) (n : ℕ) :
    smoothHeathBrownFreeFactorDiscreteTerm f m t n = 0 := by
  have hcoeff0 : smoothHeathBrownFreeFactorCoefficient f 0 = 0 := by
    cases f <;> simp [smoothHeathBrownFreeFactorCoefficient,
      smoothHeathBrownThetaFactor, smoothHeathBrownLogFactor]
  by_cases hn : n = 0
  · subst n
    simp [smoothHeathBrownFreeFactorDiscreteTerm, hcoeff0]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hsample := smoothHeathBrown_freeFactor_profile_sample
      hX f hfree m n hnpos
    have hprofile := smoothHeathBrownFreeFactorProfile_eq_zero_of_parameter_outside
      (v := (m : ℝ) * smoothHeathBrownFactorScale f / X)
      (a := smoothHeathBrownFreeFactorProfileA f)
      (b := smoothHeathBrownFreeFactorProfileB f) hv
      ((n : ℝ) / smoothHeathBrownFactorScale f)
    have hcoef :
        smoothHeathBrownFreeFactorCoefficient f n *
          polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) = 0 := by
      calc
        _ = smoothDyadicH
            ((m : ℝ) * smoothHeathBrownFactorScale f / X)
            (smoothHeathBrownFreeFactorProfileA f)
            (smoothHeathBrownFreeFactorProfileB f)
            ((n : ℝ) / smoothHeathBrownFactorScale f) := hsample.symm
        _ = 0 := hprofile
    unfold smoothHeathBrownFreeFactorDiscreteTerm
    rw [hcoef]
    simp

#print axioms smoothHeathBrownFreeFactorDiscreteTerm_eq_zero_of_parameter_outside

/-- For every fixed product `m`, the literal finite progression sum of the
normalized long free factor obeys the source's residue-quadrature estimate.
If the cutoff parameter is outside `[3/8,5]`, the sum is zero; inside, the
profile-box lemma and `smoothDyadicResidueQuadrature` apply at the exact
reduced modulus `q / gcd(m,q)`. -/
theorem smoothHeathBrown_freeFactor_finite_inner_sum_norm_le
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m q a : ℕ) (hq : 0 < q) (t : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (ht : 1 ≤ |t|) :
    ‖∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions f m q a,
        smoothHeathBrownFreeFactorDiscreteTerm f m t n.1‖ ≤
      Twisted.smoothDyadicC j *
        Real.sqrt (smoothHeathBrownFactorScale f) *
          (((q / Nat.gcd m q : ℕ) : ℝ)⁻¹ * |t| ^ (-(j : ℝ)) +
            ((q / Nat.gcd m q : ℕ) : ℝ) ^ (j - 1) *
              ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j) := by
  let T := smoothHeathBrownFreeFactorSupportSolutions f m q a
  let q' : ℕ := q / Nat.gcd m q
  have hq'pos : 0 < q' := by
    dsimp [q']
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq (Nat.gcd_dvd_right m q)
    · exact Nat.gcd_pos_of_pos_right m hq
  have hq' : 1 ≤ q' := by omega
  have hN : 1 ≤ smoothHeathBrownFactorScale f :=
    smoothHeathBrownFactorScale_ge_one f
  have hC : 0 ≤ Twisted.smoothDyadicC j := by
    unfold Twisted.smoothDyadicC
    positivity
  have hterm :
      0 ≤ (q' : ℝ)⁻¹ * |t| ^ (-(j : ℝ)) +
        (q' : ℝ) ^ (j - 1) *
          ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j := by
    positivity
  by_cases hv :
      (3 / 8 : ℝ) ≤ (m : ℝ) * smoothHeathBrownFactorScale f / X ∧
        (m : ℝ) * smoothHeathBrownFactorScale f / X ≤ 5
  · by_cases hres : ∃ n₀ : ℕ, m * n₀ ≡ a [MOD q]
    · rcases hres with ⟨n₀, hsol⟩
      have hp : smoothHeathBrownFreeFactorProfileParameters X m f ∈
          smoothDyadicProfileParameterBox :=
        smoothHeathBrownFreeFactorProfileParameters_mem_box hX f hfree m hv
      have hsumtrunc :
          (∑ n ∈ T, smoothHeathBrownFreeFactorDiscreteTerm f m t n.1) =
            ∑' n : {n : ℕ // m * n ≡ a [MOD q]},
              smoothHeathBrownFreeFactorDiscreteTerm f m t n.1 := by
        rw [tsum_eq_sum (s := T)]
        intro n hnT
        by_contra hnterm
        exact hnT (smoothHeathBrownFreeFactorDiscreteTerm_mem_supportSolutions
          hX f hfree m q a t n hnterm)
      rcases smoothHeathBrown_freeFactor_tsum_eq_reducedResidueLattice
          hX f hfree m q a n₀ hq hsol t with ⟨_, _, hsum⟩
      have hfinite :
          (∑ n ∈ T, smoothHeathBrownFreeFactorDiscreteTerm f m t n.1) =
            ∑' x : ResidueLattice (q' : ℤ) (n₀ : ℤ),
              smoothDyadicQuadratureSource
                (smoothHeathBrownFactorScale f) t
                (smoothHeathBrownFreeFactorProfileParameters X m f)
                (x.1 : ℝ) := by
        calc
          _ = ∑' n : {n : ℕ // m * n ≡ a [MOD q]},
                smoothHeathBrownFreeFactorDiscreteTerm f m t n.1 := hsumtrunc
          _ = ∑' x : ResidueLattice (q' : ℤ) (n₀ : ℤ),
                smoothDyadicQuadratureSource
                  (smoothHeathBrownFactorScale f) t
                  (smoothHeathBrownFreeFactorProfileParameters X m f)
                  (x.1 : ℝ) := by simpa [q'] using hsum
      have hquad := smoothDyadicResidueQuadrature
        (smoothHeathBrownFactorScale f) t
        (smoothHeathBrownFreeFactorProfileParameters X m f)
        q' (n₀ : ℤ) j hN hp hq' hj ht
      calc
        ‖∑ n ∈ T, smoothHeathBrownFreeFactorDiscreteTerm f m t n.1‖ =
            ‖∑' x : ResidueLattice (q' : ℤ) (n₀ : ℤ),
              smoothDyadicQuadratureSource
                (smoothHeathBrownFactorScale f) t
                (smoothHeathBrownFreeFactorProfileParameters X m f)
                (x.1 : ℝ)‖ := by rw [hfinite]
        _ ≤ Twisted.smoothDyadicC j *
            Real.sqrt (smoothHeathBrownFactorScale f) *
              ((q' : ℝ)⁻¹ * |t| ^ (-(j : ℝ)) +
                (q' : ℝ) ^ (j - 1) *
                  ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j) := hquad
        _ = Twisted.smoothDyadicC j *
            Real.sqrt (smoothHeathBrownFactorScale f) *
              (((q / Nat.gcd m q : ℕ) : ℝ)⁻¹ * |t| ^ (-(j : ℝ)) +
                ((q / Nat.gcd m q : ℕ) : ℝ) ^ (j - 1) *
                  ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j) := by
              rfl
    · have hsumzero :
          (∑ n ∈ T, smoothHeathBrownFreeFactorDiscreteTerm f m t n.1) = 0 := by
        apply Finset.sum_eq_zero
        intro n hnT
        have hsol : m * n.1 ≡ a [MOD q] := by
          change n ∈
            (smoothHeathBrownFreeFactorResidueWindow f m q a).attach.map
              (smoothHeathBrownFreeFactorSupportEmbedding f m q a) at hnT
          rcases Finset.mem_map.mp hnT with ⟨k, hk, hkn⟩
          have hk' :
              k.1 ∈ smoothHeathBrownFreeFactorResidueWindow f m q a :=
            k.2
          have hkcong : m * k.1 ≡ a [MOD q] :=
            (Finset.mem_filter.mp hk').2
          have hEq : k.1 = n.1 := by
            have := congrArg
              (fun y : {n : ℕ // m * n ≡ a [MOD q]} => y.1) hkn
            exact this
          simpa [hEq] using hkcong
        exact (hres ⟨n.1, hsol⟩).elim
      rw [hsumzero]
      have hnonneg :
          0 ≤ Twisted.smoothDyadicC j *
            Real.sqrt (smoothHeathBrownFactorScale f) *
              ((q' : ℝ)⁻¹ * |t| ^ (-(j : ℝ)) +
                (q' : ℝ) ^ (j - 1) *
                  ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j) :=
        mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hterm
      simpa [q'] using hnonneg
  · have hzero (n : ℕ) :
        smoothHeathBrownFreeFactorDiscreteTerm f m t n = 0 :=
      smoothHeathBrownFreeFactorDiscreteTerm_eq_zero_of_parameter_outside
        hX f hfree m hv t n
    have hsumzero :
        (∑ n ∈ T, smoothHeathBrownFreeFactorDiscreteTerm f m t n.1) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      exact hzero n.1
    rw [hsumzero]
    have hnonneg :
        0 ≤ Twisted.smoothDyadicC j *
          Real.sqrt (smoothHeathBrownFactorScale f) *
            ((q' : ℝ)⁻¹ * |t| ^ (-(j : ℝ)) +
              (q' : ℝ) ^ (j - 1) *
                ((1 + |t|) / smoothHeathBrownFactorScale f) ^ j) :=
      mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hterm
    simpa [q'] using hnonneg

#print axioms smoothHeathBrown_freeFactor_finite_inner_sum_norm_le

end FractionalPrimes.Literature.DirichletAdapter

end
