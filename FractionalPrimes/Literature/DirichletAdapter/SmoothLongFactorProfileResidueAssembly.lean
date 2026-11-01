module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorProfile
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorResidueLattice
public import FractionalPrimes.Literature.DirichletAdapter.SmoothDyadicSourceCompact
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Connect the exact smooth free-factor profile sample to the reduced
residue-lattice sum.  The quadrature error remains an explicit premise in the
resulting norm inequality. -/

@[expose] public section

open MeasureTheory
open scoped CompactlySupported

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- Every dyadic scale occurring in the finite smooth partition is at most
`8X`, with the exact depth convention used in `lda:smooth-hb`. -/
theorem smoothHeathBrownFreeFactorScale_le_eightX_profile
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X) :
    smoothHeathBrownFactorScale f ≤ 8 * X := by
  have hXpos : 0 < X := by linarith
  have harg : 1 ≤ 4 * X := by nlinarith
  have hlogbnonneg : 0 ≤ Real.logb 2 (4 * X) := by
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg harg)
      (Real.log_pos (by norm_num)).le
  have hceil :
      (smoothHeathBrownDepth X : ℝ) < Real.logb 2 (4 * X) + 1 := by
    dsimp [smoothHeathBrownDepth]
    exact Nat.ceil_lt_add_one hlogbnonneg
  have hindexScale (j : SmoothHeathBrownScaleIndex X) :
      (2 : ℝ) ^ j.val ≤ 8 * X := by
    have hjNat : j.val ≤ smoothHeathBrownDepth X := by omega
    have hjReal : (j.val : ℝ) < Real.logb 2 (4 * X) + 1 := by
      exact lt_of_le_of_lt (by exact_mod_cast hjNat) hceil
    have hlog8 : Real.logb 2 (8 * X) = Real.logb 2 (4 * X) + 1 := by
      rw [show 8 * X = (2 : ℝ) * (4 * X) by ring,
        Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by positivity : (4 * X) ≠ 0)]
      rw [Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))]
      ring
    have hjLog : (j.val : ℝ) < Real.logb 2 (8 * X) := by
      rw [hlog8]
      exact hjReal
    have hpow : (2 : ℝ) ^ (j.val : ℝ) < 8 * X :=
      (Real.lt_logb_iff_rpow_lt (by norm_num : 1 < (2 : ℝ))
        (by positivity : 0 < 8 * X)).mp hjLog
    exact le_of_lt (by simpa only [Real.rpow_natCast] using hpow)
  cases f with
  | theta j => exact hindexScale j
  | logarithm j => exact hindexScale j
  | mobius j => exact hindexScale j

#print axioms smoothHeathBrownFreeFactorScale_le_eightX_profile

/-- When `v=mN/X` lies in the source quadrature interval, the exact profile
parameters attached to a non-Möbius smooth factor belong to the compact box
used to define the uniform constants `A_j` and `B_j`. -/
theorem smoothHeathBrownFreeFactorProfileParameters_mem_box
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m : ℕ)
    (hv : (3 / 8 : ℝ) ≤ (m : ℝ) * smoothHeathBrownFactorScale f / X ∧
      (m : ℝ) * smoothHeathBrownFactorScale f / X ≤ 5) :
    smoothHeathBrownFreeFactorProfileParameters X m f ∈
      smoothDyadicProfileParameterBox := by
  have hXpos : 0 < X := by linarith
  have hXlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hXlogone : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact le_of_lt (lt_of_lt_of_le Real.exp_one_lt_three hX)
  rcases hv with ⟨hvlo, hvhi⟩
  cases f with
  | theta j =>
      simp only [smoothHeathBrownFreeFactorProfileParameters,
        smoothHeathBrownFreeFactorProfileA,
        smoothHeathBrownFreeFactorProfileB,
        smoothHeathBrownFactorScale,
        smoothDyadicProfileParameterBox, Set.mem_prod, Set.mem_Icc]
      exact ⟨⟨hvlo, hvhi⟩, ⟨⟨by norm_num, by norm_num⟩,
        ⟨by norm_num, by norm_num⟩⟩⟩
  | logarithm j =>
      have hNge : 1 ≤ smoothHeathBrownFactorScale
          (SmoothHeathBrownFactor.logarithm j) :=
        smoothHeathBrownFactorScale_ge_one _
      have hNle := smoothHeathBrownFreeFactorScale_le_eightX_profile
        hX (SmoothHeathBrownFactor.logarithm j)
      have hXsq : 8 ≤ X ^ 2 := by nlinarith
      have h8X : 8 * X ≤ X ^ 3 := by
        calc
          8 * X = X * 8 := by ring
          _ ≤ X * X ^ 2 := mul_le_mul_of_nonneg_left hXsq hXpos.le
          _ = X ^ 3 := by ring
      have hNcube :
          smoothHeathBrownFactorScale (SmoothHeathBrownFactor.logarithm j) ≤
            X ^ 3 := le_trans hNle h8X
      have hlogNnonneg :
          0 ≤ Real.log (smoothHeathBrownFactorScale
            (SmoothHeathBrownFactor.logarithm j)) :=
        Real.log_nonneg hNge
      have hlogNle :
          Real.log (smoothHeathBrownFactorScale
            (SmoothHeathBrownFactor.logarithm j)) ≤ 4 * Real.log X := by
        have hlog := Real.log_le_log (by positivity) hNcube
        rw [Real.log_pow] at hlog
        calc
          _ ≤ 3 * Real.log X := hlog
          _ ≤ 4 * Real.log X := by nlinarith [hXlog]
      have hden : 0 < 4 * Real.log X := by positivity
      have ha0 : 0 ≤ Real.log (smoothHeathBrownFactorScale
          (SmoothHeathBrownFactor.logarithm j)) / (4 * Real.log X) :=
        div_nonneg hlogNnonneg hden.le
      have ha1 : Real.log (smoothHeathBrownFactorScale
          (SmoothHeathBrownFactor.logarithm j)) / (4 * Real.log X) ≤ 1 :=
        (div_le_one hden).2 hlogNle
      have hb0 : 0 ≤ 1 / (4 * Real.log X) := by positivity
      have hb1 : 1 / (4 * Real.log X) ≤ 1 :=
        (div_le_one hden).2 (by nlinarith [hXlogone])
      simp only [smoothHeathBrownFreeFactorProfileParameters,
        smoothHeathBrownFreeFactorProfileA,
        smoothHeathBrownFreeFactorProfileB,
        smoothHeathBrownFactorScale,
        smoothDyadicProfileParameterBox, Set.mem_prod, Set.mem_Icc]
      exact ⟨⟨hvlo, hvhi⟩, ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩⟩
  | mobius j => exact (hfree j rfl).elim

#print axioms smoothHeathBrownFreeFactorProfileParameters_mem_box

/-- The normalized free-factor sample, including its Mellin twist and the
outer cutoff at the full product `m*n`. -/
noncomputable def smoothHeathBrownFreeFactorDiscreteTerm
    {X : ℝ} (f : SmoothHeathBrownFactor X) (m : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ smoothDyadicTwistExponent t *
    ((smoothHeathBrownFreeFactorCoefficient f n *
      polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) : ℝ) : ℂ)

/-- A finite closed scale window containing the support of the free-factor
profile. -/
noncomputable def smoothHeathBrownFreeFactorScaleWindow
    {X : ℝ} (f : SmoothHeathBrownFactor X) : Finset ℕ :=
  Finset.Icc
    (Nat.floor (smoothHeathBrownFactorScale f / 2))
    (Nat.floor (2 * smoothHeathBrownFactorScale f))

/-- The finite part of a scale window in one fixed reduced residue class. -/
noncomputable def smoothHeathBrownFreeFactorResidueWindow
    {X : ℝ} (f : SmoothHeathBrownFactor X) (m q a : ℕ) : Finset ℕ :=
  (smoothHeathBrownFreeFactorScaleWindow f).filter
    (fun n => m * n ≡ a [MOD q])

/-- The canonical embedding of the finite residue window into the full
congruence subtype. -/
def smoothHeathBrownFreeFactorSupportEmbedding
    {X : ℝ} (f : SmoothHeathBrownFactor X) (m q a : ℕ) :
    {n : ℕ // n ∈ smoothHeathBrownFreeFactorResidueWindow f m q a} ↪
      {n : ℕ // m * n ≡ a [MOD q]} where
  toFun n := ⟨n.1, (Finset.mem_filter.mp n.2).2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg
      (fun z : {n : ℕ // m * n ≡ a [MOD q]} => z.1) h

/-- The compactly supported progression family as an actual finite set of
solutions. -/
noncomputable def smoothHeathBrownFreeFactorSupportSolutions
    {X : ℝ} (f : SmoothHeathBrownFactor X) (m q a : ℕ) :
    Finset {n : ℕ // m * n ≡ a [MOD q]} :=
  (smoothHeathBrownFreeFactorResidueWindow f m q a).attach.map
    (smoothHeathBrownFreeFactorSupportEmbedding f m q a)

/-- Every nonzero discrete free-factor sample lies in the exact finite scale
window determined by the support of the smooth profile. -/
theorem smoothHeathBrownFreeFactorDiscreteTerm_mem_scaleWindow
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m : ℕ) (t : ℝ) {n : ℕ}
    (hn : smoothHeathBrownFreeFactorDiscreteTerm f m t n ≠ 0) :
    n ∈ smoothHeathBrownFreeFactorScaleWindow f := by
  have hterm0 : smoothHeathBrownFreeFactorDiscreteTerm f m t 0 = 0 := by
    cases f <;> simp [smoothHeathBrownFreeFactorDiscreteTerm,
      smoothHeathBrownFreeFactorCoefficient, smoothHeathBrownThetaFactor,
      smoothHeathBrownLogFactor]
  by_cases hn0 : n = 0
  · subst n
    exact False.elim (hn hterm0)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hN : 0 < smoothHeathBrownFactorScale f :=
      lt_of_lt_of_le (by norm_num) (smoothHeathBrownFactorScale_ge_one f)
    have hsource :
        smoothDyadicQuadratureSource (smoothHeathBrownFactorScale f) t
          (smoothHeathBrownFreeFactorProfileParameters X m f) (n : ℝ) ≠ 0 := by
      rw [smoothHeathBrown_freeFactorSource_sample hX f hfree m n hnpos t]
      simpa [smoothHeathBrownFreeFactorDiscreteTerm] using hn
    have hwindow := smoothDyadicQuadratureSource_support_subset
      (smoothHeathBrownFactorScale f) t
      (smoothHeathBrownFreeFactorProfileParameters X m f) hN
      (Function.mem_support.mpr hsource)
    apply Finset.mem_Icc.mpr
    constructor
    · have hfloor :
          (Nat.floor (smoothHeathBrownFactorScale f / 2) : ℝ) ≤ (n : ℝ) :=
        le_trans (Nat.floor_le (by positivity)) hwindow.1
      exact_mod_cast hfloor
    · exact Nat.le_floor hwindow.2

#print axioms smoothHeathBrownFreeFactorDiscreteTerm_mem_scaleWindow

/-- Every nonzero term in the congruence subtype belongs to the finite set
of source-supported solutions. -/
theorem smoothHeathBrownFreeFactorDiscreteTerm_mem_supportSolutions
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m q a : ℕ) (t : ℝ)
    (n : {n : ℕ // m * n ≡ a [MOD q]})
    (hn : smoothHeathBrownFreeFactorDiscreteTerm f m t n.1 ≠ 0) :
    n ∈ smoothHeathBrownFreeFactorSupportSolutions f m q a := by
  let x : {k : ℕ // k ∈ smoothHeathBrownFreeFactorResidueWindow f m q a} :=
    ⟨n.1, Finset.mem_filter.mpr
      ⟨smoothHeathBrownFreeFactorDiscreteTerm_mem_scaleWindow
          hX f hfree m t hn, n.2⟩⟩
  change n ∈
    (smoothHeathBrownFreeFactorResidueWindow f m q a).attach.map
      (smoothHeathBrownFreeFactorSupportEmbedding f m q a)
  apply Finset.mem_map.mpr
  refine ⟨x, Finset.mem_attach _ _, ?_⟩
  apply Subtype.ext
  rfl

#print axioms smoothHeathBrownFreeFactorDiscreteTerm_mem_supportSolutions

/-- The free-factor coefficient sum after fixing the other factors is exactly
the source profile summed over the reduced residue lattice.  This is a pure
reindexing identity; no quadrature estimate is used. -/
theorem smoothHeathBrown_freeFactor_tsum_eq_reducedResidueLattice
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m q a n₀ : ℕ) (hq : 0 < q)
    (hsol : m * n₀ ≡ a [MOD q]) (t : ℝ) :
    1 ≤ q / Nat.gcd m q ∧
      q / Nat.gcd m q ≤ q ∧
        (∑' n : {n : ℕ // m * n ≡ a [MOD q]},
          smoothHeathBrownFreeFactorDiscreteTerm f m t n.1) =
          ∑' x : ResidueLattice
            ((q / Nat.gcd m q : ℕ) : ℤ) (n₀ : ℤ),
              smoothDyadicQuadratureSource
                (smoothHeathBrownFactorScale f) t
                (smoothHeathBrownFreeFactorProfileParameters X m f)
                (x.1 : ℝ) := by
  let N : ℝ := smoothHeathBrownFactorScale f
  let p : ℝ × ℝ × ℝ :=
    smoothHeathBrownFreeFactorProfileParameters X m f
  have hN : 0 < N := by
    dsimp [N]
    exact lt_of_lt_of_le (by norm_num) (smoothHeathBrownFactorScale_ge_one f)
  let F : C_c(ℝ, ℂ) := smoothDyadicQuadratureSourceCompact N t p hN
  have hFneg : ∀ x : ℝ, x < 0 → F x = 0 := by
    intro x hx
    change smoothDyadicQuadratureSource N t p x = 0
    exact smoothHeathBrown_freeFactorSource_eq_zero_of_nonpos N t p (le_of_lt hx)
  have hre := smoothHeathBrown_fixedProduct_tsum_reindex_to_residueLattice
    F m q a n₀ hq hsol hFneg
  rcases hre with ⟨hqred, hqle, hreindex⟩
  refine ⟨hqred, hqle, ?_⟩
  calc
    ∑' n : {n : ℕ // m * n ≡ a [MOD q]},
        smoothHeathBrownFreeFactorDiscreteTerm f m t n.1 =
      ∑' n : {n : ℕ // m * n ≡ a [MOD q]}, F (n.1 : ℝ) := by
        apply tsum_congr
        intro n
        by_cases hn : n.1 = 0
        · rw [hn]
          have hcoeff0 : smoothHeathBrownFreeFactorCoefficient f 0 = 0 := by
            cases f <;> simp [smoothHeathBrownFreeFactorCoefficient,
              smoothHeathBrownThetaFactor, smoothHeathBrownLogFactor]
          have hterm0 : smoothHeathBrownFreeFactorDiscreteTerm f m t 0 = 0 := by
            simp [smoothHeathBrownFreeFactorDiscreteTerm, hcoeff0]
          have hF0 : F (0 : ℝ) = 0 := by
            simp [F, smoothDyadicQuadratureSourceCompact,
              smoothDyadicQuadratureSource]
          rw [hterm0]
          simpa using hF0.symm
        · have hnpos : 0 < n.1 := Nat.pos_of_ne_zero hn
          change smoothHeathBrownFreeFactorDiscreteTerm f m t n.1 =
            smoothDyadicQuadratureSource N t p (n.1 : ℝ)
          simpa [smoothHeathBrownFreeFactorDiscreteTerm, N, p] using
            (smoothHeathBrown_freeFactorSource_sample hX f hfree m n.1 hnpos t).symm
    _ = ∑' x : ResidueLattice
          ((q / Nat.gcd m q : ℕ) : ℤ) (n₀ : ℤ), F (x.1 : ℝ) := hreindex
    _ = ∑' x : ResidueLattice
          ((q / Nat.gcd m q : ℕ) : ℤ) (n₀ : ℤ),
            smoothDyadicQuadratureSource N t p (x.1 : ℝ) := by
        apply tsum_congr
        intro x
        rfl

#print axioms smoothHeathBrown_freeFactor_tsum_eq_reducedResidueLattice

/-- If the exact source profile has residue-lattice quadrature error at most
`ε`, then its fixed-factor progression sum is bounded by the normalized
integral plus that error.  The quadrature estimate is an explicit input. -/
theorem smoothHeathBrown_freeFactor_tsum_norm_le_of_quadrature_error
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m q a n₀ : ℕ) (hq : 0 < q)
    (hsol : m * n₀ ≡ a [MOD q]) (t ε : ℝ)
    (hquad :
      ‖(∑' x : ResidueLattice
          ((q / Nat.gcd m q : ℕ) : ℤ) (n₀ : ℤ),
            smoothDyadicQuadratureSource
              (smoothHeathBrownFactorScale f) t
              (smoothHeathBrownFreeFactorProfileParameters X m f)
              (x.1 : ℝ)) -
        (((q / Nat.gcd m q : ℕ) : ℝ)⁻¹ •
          (∫ x : ℝ, smoothDyadicQuadratureSource
            (smoothHeathBrownFactorScale f) t
            (smoothHeathBrownFreeFactorProfileParameters X m f) x ∂volume))‖ ≤ ε) :
    ‖∑' n : {n : ℕ // m * n ≡ a [MOD q]},
        smoothHeathBrownFreeFactorDiscreteTerm f m t n.1‖ ≤
      ((q / Nat.gcd m q : ℕ) : ℝ)⁻¹ *
        ‖∫ x : ℝ, smoothDyadicQuadratureSource
          (smoothHeathBrownFactorScale f) t
          (smoothHeathBrownFreeFactorProfileParameters X m f) x ∂volume‖ + ε := by
  rcases smoothHeathBrown_freeFactor_tsum_eq_reducedResidueLattice
      hX f hfree m q a n₀ hq hsol t with ⟨hqred, hqle, hsum⟩
  let q' : ℕ := q / Nat.gcd m q
  let F : ℝ → ℂ := smoothDyadicQuadratureSource
    (smoothHeathBrownFactorScale f) t
    (smoothHeathBrownFreeFactorProfileParameters X m f)
  let L : ℂ := ∑' x : ResidueLattice (q' : ℤ) (n₀ : ℤ), F (x.1 : ℝ)
  let I : ℂ := ∫ x : ℝ, F x ∂volume
  have hq'pos : 0 < (q' : ℝ) := by
    dsimp [q']
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hqred)
  have hmain : ‖(q' : ℝ)⁻¹ • I‖ = (q' : ℝ)⁻¹ * ‖I‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hq'pos.le)]
  have hdecomp : L = (L - (q' : ℝ)⁻¹ • I) + (q' : ℝ)⁻¹ • I := by
    abel
  have hbound := norm_add_le (L - (q' : ℝ)⁻¹ • I) ((q' : ℝ)⁻¹ • I)
  have hquad' : ‖L - (q' : ℝ)⁻¹ • I‖ ≤ ε := by
    simpa [L, I, q'] using hquad
  have hsum' :
      (∑' n : {n : ℕ // m * n ≡ a [MOD q]},
          smoothHeathBrownFreeFactorDiscreteTerm f m t n.1) = L := by
    simpa [L, F, q', smoothHeathBrownFreeFactorDiscreteTerm] using hsum
  rw [hsum']
  calc
    ‖L‖ = ‖(L - (q' : ℝ)⁻¹ • I) + (q' : ℝ)⁻¹ • I‖ :=
      congrArg (fun z : ℂ => ‖z‖) hdecomp
    _ ≤ ‖L - (q' : ℝ)⁻¹ • I‖ + ‖(q' : ℝ)⁻¹ • I‖ := hbound
    _ ≤ ε + (q' : ℝ)⁻¹ * ‖I‖ := add_le_add hquad' (le_of_eq hmain)
    _ = (q' : ℝ)⁻¹ * ‖I‖ + ε := by ring

#print axioms smoothHeathBrown_freeFactor_tsum_norm_le_of_quadrature_error

/-- The corresponding literal finite-sum inequality over the source scale
window. Its only analytic input is the displayed residue-lattice quadrature
error premise. -/
theorem smoothHeathBrown_freeFactor_finiteSum_norm_le_of_quadrature_error
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m q a n₀ : ℕ) (hq : 0 < q)
    (hsol : m * n₀ ≡ a [MOD q]) (t ε : ℝ)
    (hquad :
      ‖(∑' x : ResidueLattice
          ((q / Nat.gcd m q : ℕ) : ℤ) (n₀ : ℤ),
            smoothDyadicQuadratureSource
              (smoothHeathBrownFactorScale f) t
              (smoothHeathBrownFreeFactorProfileParameters X m f)
              (x.1 : ℝ)) -
        (((q / Nat.gcd m q : ℕ) : ℝ)⁻¹ •
          (∫ x : ℝ, smoothDyadicQuadratureSource
            (smoothHeathBrownFactorScale f) t
            (smoothHeathBrownFreeFactorProfileParameters X m f) x ∂volume))‖ ≤ ε) :
    ‖∑ n ∈ smoothHeathBrownFreeFactorSupportSolutions f m q a,
        smoothHeathBrownFreeFactorDiscreteTerm f m t n.1‖ ≤
      ((q / Nat.gcd m q : ℕ) : ℝ)⁻¹ *
        ‖∫ x : ℝ, smoothDyadicQuadratureSource
          (smoothHeathBrownFactorScale f) t
          (smoothHeathBrownFreeFactorProfileParameters X m f) x ∂volume‖ + ε := by
  let T := smoothHeathBrownFreeFactorSupportSolutions f m q a
  have htsum :
      (∑' n : {n : ℕ // m * n ≡ a [MOD q]},
        smoothHeathBrownFreeFactorDiscreteTerm f m t n.1) =
      ∑ n ∈ T, smoothHeathBrownFreeFactorDiscreteTerm f m t n.1 := by
    rw [tsum_eq_sum (s := T)]
    intro n hnT
    by_contra hnterm
    exact hnT (smoothHeathBrownFreeFactorDiscreteTerm_mem_supportSolutions
      hX f hfree m q a t n hnterm)
  have htsumbound := smoothHeathBrown_freeFactor_tsum_norm_le_of_quadrature_error
    hX f hfree m q a n₀ hq hsol t ε hquad
  calc
    ‖∑ n ∈ T, smoothHeathBrownFreeFactorDiscreteTerm f m t n.1‖ =
        ‖∑' n : {n : ℕ // m * n ≡ a [MOD q]},
          smoothHeathBrownFreeFactorDiscreteTerm f m t n.1‖ := by
            congr 1
            exact htsum.symm
    _ ≤ ((q / Nat.gcd m q : ℕ) : ℝ)⁻¹ *
          ‖∫ x : ℝ, smoothDyadicQuadratureSource
            (smoothHeathBrownFactorScale f) t
            (smoothHeathBrownFreeFactorProfileParameters X m f) x ∂volume‖ + ε :=
          htsumbound

#print axioms smoothHeathBrown_freeFactor_finiteSum_norm_le_of_quadrature_error

end FractionalPrimes.Literature.DirichletAdapter

end
