module

public import FractionalPrimes.ArithmeticBasicsCore
public import FractionalPrimes.ArithmeticBasicsAnalytic
public import FractionalPrimes.Literature.Polynomial.AffineRecurrence
public import FractionalPrimes.Literature.Uniformity.TotalVariationCalculusPackage
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

/-- The unit-frequency denominator is bounded below by four times the exact
distance to the integer lattice. The centering uses `⌊α+1/2⌋`, so the chord
estimate is applied on its exact centered interval. -/
private theorem four_mul_realDistance_le_phase_denominator (α : ℝ) :
    4 * realDistanceToIntegers α ≤ ‖1 - unitFrequencyPhase α‖ := by
  let m : ℤ := ⌊α + (1 / 2 : ℝ)⌋
  let t : ℝ := α - (m : ℝ)
  have htlo : -(1 / 2 : ℝ) ≤ t := by
    dsimp [t, m]
    have hf := Int.floor_le (α + (1 / 2 : ℝ))
    linarith
  have hthi : t ≤ (1 / 2 : ℝ) := by
    dsimp [t, m]
    have hf := Int.lt_floor_add_one (α + (1 / 2 : ℝ))
    linarith
  have ht : |t| ≤ 1 / 2 := abs_le.mpr ⟨htlo, hthi⟩
  have hα : α = t + (m : ℝ) := by dsimp [t]; ring
  have hdist : realDistanceToIntegers α = realDistanceToIntegers t := by
    rw [hα, realDistanceToIntegers_add_int]
  have hphase : unitFrequencyPhase α = unitFrequencyPhase t := by
    rw [hα, unitFrequencyPhase_add, unitFrequencyPhase_int]
    simp
  rw [hdist, hphase]
  exact four_mul_realDistanceToIntegers_le_norm_one_sub_unitFrequencyPhase ht

/-- Geometric-sum estimate on a half-open integer interval. -/
private theorem linearPhaseIcoBound {a b : ℤ} (α β : ℝ)
    (hα : 0 < realDistanceToIntegers α) :
    ‖∑ n ∈ Finset.Ico a b, unitFrequencyPhase (α * (n : ℝ) + β)‖ ≤
      1 / (2 * realDistanceToIntegers α) := by
  classical
  let N : ℕ := (b - a).toNat
  let z : ℂ := unitFrequencyPhase α
  let c : ℂ := unitFrequencyPhase (α * (a : ℝ) + β)
  have hIco : Finset.Ico a b =
      (Finset.range N).map (Nat.castEmbedding.trans (addLeftEmbedding a)) := by
    simpa [N] using Int.Ico_eq_finset_map a b
  have hsum :
      (∑ n ∈ Finset.Ico a b, unitFrequencyPhase (α * (n : ℝ) + β)) =
        c * ∑ k ∈ Finset.range N, z ^ k := by
    rw [hIco, Finset.sum_map]
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have harg : α * ((a + (k : ℤ) : ℤ) : ℝ) + β =
        (α * (a : ℝ) + β) + (k : ℝ) * α := by
      push_cast
      ring
    rw [harg, unitFrequencyPhase_add, unitFrequencyPhase_nat_mul]
  rw [hsum, norm_mul, norm_unitFrequencyPhase, one_mul]
  have hdist := four_mul_realDistance_le_phase_denominator α
  have hden : 0 < ‖z - 1‖ := by
    have hpos : 0 < ‖1 - z‖ := by
      have hge : 0 < 4 * realDistanceToIntegers α := mul_pos (by norm_num) hα
      exact lt_of_lt_of_le hge (by simpa [z] using hdist)
    have hnorm : ‖1 - z‖ = ‖z - 1‖ := by
      rw [show (1 : ℂ) - z = -(z - 1) by ring, norm_neg]
    rw [← hnorm]
    exact hpos
  have hgeom :
      ‖∑ k ∈ Finset.range N, z ^ k‖ * ‖z - 1‖ = ‖z ^ N - 1‖ := by
    calc
      ‖∑ k ∈ Finset.range N, z ^ k‖ * ‖z - 1‖ =
          ‖(∑ k ∈ Finset.range N, z ^ k) * (z - 1)‖ := by rw [norm_mul]
      _ = ‖z ^ N - 1‖ := by rw [geom_sum_mul]
  have hz : ‖z‖ = 1 := by simp [z, norm_unitFrequencyPhase]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    calc
      ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  have hprod : ‖∑ k ∈ Finset.range N, z ^ k‖ * ‖z - 1‖ ≤ 2 := by
    rw [hgeom]
    exact hnum
  have hgeomBound : ‖∑ k ∈ Finset.range N, z ^ k‖ ≤ 2 / ‖z - 1‖ :=
    (le_div_iff₀ hden).2 hprod
  have hdenLower : 4 * realDistanceToIntegers α ≤ ‖z - 1‖ := by
    have hh := four_mul_realDistance_le_phase_denominator α
    have hnorm : ‖1 - unitFrequencyPhase α‖ =
        ‖unitFrequencyPhase α - 1‖ := by
      rw [show (1 : ℂ) - unitFrequencyPhase α =
        -(unitFrequencyPhase α - 1) by ring, norm_neg]
    change 4 * realDistanceToIntegers α ≤
      ‖unitFrequencyPhase α - 1‖
    rw [← hnorm]
    exact hh
  have hcompare : 2 / ‖z - 1‖ ≤ 1 / (2 * realDistanceToIntegers α) := by
    apply (div_le_div_iff₀ hden (by positivity)).2
    nlinarith [hdenLower]
  exact hgeomBound.trans hcompare

/-- Blueprint `lbi:weyl-linear`, first assertion: every finite integer interval
is represented by a half-open `Ico`, and its linear exponential sum has the
exact reciprocal-distance bound. -/
theorem linearPhaseSumBound (J : Finset ℤ)
    (hJ : ∃ a b : ℤ, J = Finset.Ico a b) (α β : ℝ)
    (hα : 0 < realDistanceToIntegers α) :
    ‖∑ n ∈ J, unitFrequencyPhase (α * (n : ℝ) + β)‖ ≤
      1 / (2 * realDistanceToIntegers α) := by
  rcases hJ with ⟨a, b, rfl⟩
  exact linearPhaseIcoBound α β hα

/-- Blueprint `lbi:weyl-linear`, inverse consequence: a large linear phase
sum on an interval contained in `[1,N]` forces the frequency close to an
integer at the exact scale `1/(2δ)`. -/
theorem linearPhaseInverse {N : ℕ} {J : Finset ℤ}
    (_hN : 1 ≤ N)
    (hJ : ∃ a b : ℤ, J = Finset.Ico a b)
    (_hJsubset : J ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    {α β δ : ℝ} (hδ : 0 < δ)
    (hlarge : δ * (N : ℝ) ≤
      ‖∑ n ∈ J, unitFrequencyPhase (α * (n : ℝ) + β)‖) :
    (N : ℝ) * realDistanceToIntegers α ≤ 1 / (2 * δ) := by
  have hd : 0 ≤ realDistanceToIntegers α := Metric.infDist_nonneg
  by_cases hd0 : realDistanceToIntegers α = 0
  · simp [hd0]
    positivity
  · have hdpos : 0 < realDistanceToIntegers α := lt_of_le_of_ne hd (Ne.symm hd0)
    have hsum := linearPhaseSumBound J hJ α β hdpos
    have hlarge' : δ * (N : ℝ) ≤
        1 / (2 * realDistanceToIntegers α) := hlarge.trans hsum
    have hprod : (2 * realDistanceToIntegers α) * (δ * (N : ℝ)) ≤ 1 := by
      calc
        (2 * realDistanceToIntegers α) * (δ * (N : ℝ)) ≤
            (2 * realDistanceToIntegers α) *
              (1 / (2 * realDistanceToIntegers α)) :=
          mul_le_mul_of_nonneg_left hlarge' (by positivity)
        _ = 1 := by
          have h2d : 0 < (2 : ℝ) * realDistanceToIntegers α :=
            mul_pos (by norm_num) hdpos
          field_simp [ne_of_gt h2d]
    rw [le_div_iff₀ (by positivity : 0 < 2 * δ)]
    ring_nf at hprod ⊢
    nlinarith [hprod]

/-- The threshold-counting step in the finite long-shift argument: a large
total correlation mass, together with the pointwise bound `N`, forces at
least `δ² N / 8` shifts to reach that threshold. -/
private theorem manyLargeShiftCorrelations_count_of_mass
    {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (C : ℕ → ℂ)
    (hmass : δ ^ 2 * (N : ℝ) ^ 2 / 4 ≤
      ∑ h ∈ Finset.Ico 1 N, ‖C h‖)
    (hbound : ∀ h ∈ Finset.Ico 1 N, ‖C h‖ ≤ N) :
    δ ^ 2 * (N : ℝ) / 8 ≤
      ((Finset.Ico 1 N).filter (fun h =>
        δ ^ 2 * (N : ℝ) / 8 ≤ ‖C h‖)).card := by
  classical
  let S : Finset ℕ := Finset.Ico 1 N
  let good : ℕ → Prop := fun h => δ ^ 2 * (N : ℝ) / 8 ≤ ‖C h‖
  let G : Finset ℕ := S.filter good
  let B : Finset ℕ := S.filter (fun h => ¬ good h)
  have hsplit : (∑ h ∈ S, ‖C h‖) =
      (∑ h ∈ G, ‖C h‖) + ∑ h ∈ B, ‖C h‖ := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := S) (p := good)
      (f := fun h => ‖C h‖)]
  have hcardS : (S.card : ℝ) ≤ N := by
    dsimp [S]
    have hcard := Nat.card_Ico 1 N
    rw [hcard]
    exact_mod_cast Nat.sub_le N 1
  by_contra hnot
  have hGlt : (G.card : ℝ) < δ ^ 2 * (N : ℝ) / 8 := by
    have := not_le.mp hnot
    simpa [S, G, good] using this
  have hgoodSum : (∑ h ∈ G, ‖C h‖) ≤ (G.card : ℝ) * N := by
    calc
      (∑ h ∈ G, ‖C h‖) ≤ ∑ _h ∈ G, (N : ℝ) := by
        apply Finset.sum_le_sum
        intro h hh
        exact hbound h (Finset.filter_subset _ _ hh)
      _ = (G.card : ℝ) * N := by simp
  have hbadSum : (∑ h ∈ B, ‖C h‖) ≤
      (B.card : ℝ) * (δ ^ 2 * (N : ℝ) / 8) := by
    calc
      (∑ h ∈ B, ‖C h‖) ≤
          ∑ _h ∈ B, (δ ^ 2 * (N : ℝ) / 8) := by
        apply Finset.sum_le_sum
        intro h hh
        have hnotgood : ¬ good h := Finset.mem_filter.mp hh |>.2
        have hlt : ‖C h‖ < δ ^ 2 * (N : ℝ) / 8 :=
          lt_of_not_ge hnotgood
        exact le_of_lt hlt
      _ = (B.card : ℝ) * (δ ^ 2 * (N : ℝ) / 8) := by simp
  have hcardB : (B.card : ℝ) ≤ N := by
    have hsub : B ⊆ S := Finset.filter_subset _ _
    calc
      (B.card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ N := hcardS
  have hsumUpper : (∑ h ∈ S, ‖C h‖) <
      δ ^ 2 * (N : ℝ) ^ 2 / 4 := by
    rw [hsplit]
    calc
      (∑ h ∈ G, ‖C h‖) + ∑ h ∈ B, ‖C h‖ ≤
          (G.card : ℝ) * N + (B.card : ℝ) *
            (δ ^ 2 * (N : ℝ) / 8) := add_le_add hgoodSum hbadSum
      _ < (δ ^ 2 * (N : ℝ) / 8) * N +
          N * (δ ^ 2 * (N : ℝ) / 8) := by
        apply add_lt_add_of_lt_of_le
        · exact mul_lt_mul_of_pos_right hGlt (by exact_mod_cast hN)
        · exact mul_le_mul_of_nonneg_right hcardB (by positivity)
      _ = δ ^ 2 * (N : ℝ) ^ 2 / 4 := by ring
  linarith

/-- Reindex the strict upper triangle of a finite natural interval by its
positive difference and lower endpoint. -/
private theorem upperTriangle_sum_eq_shiftPairs {M : Type*} [AddCommMonoid M]
    (N : ℕ) (F : ℕ → ℕ → M) :
    (∑ p ∈ ((Finset.range N).product (Finset.range N)).filter
      (fun p => p.1 < p.2),
      F p.1 p.2) =
    ∑ q ∈ (((Finset.Ico 1 N).product (Finset.range N)).filter
      (fun q => q.2 + q.1 < N)),
      F q.2 (q.2 + q.1) := by
  classical
  let P := (Finset.range N).product (Finset.range N)
  let U := P.filter (fun p => p.1 < p.2)
  let T := ((Finset.Ico 1 N).product (Finset.range N)).filter
    (fun q => q.2 + q.1 < N)
  change (∑ p ∈ U, F p.1 p.2) =
    ∑ q ∈ T, F q.2 (q.2 + q.1)
  refine Finset.sum_bij (fun p _ => (p.2 - p.1, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpP, hlt⟩
    rcases Finset.mem_product.mp hpP with ⟨hp1, hp2⟩
    have hp1' : p.1 < N := Finset.mem_range.mp hp1
    have hp2' : p.2 < N := Finset.mem_range.mp hp2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Ico.mpr
        constructor <;> omega
      · exact Finset.mem_range.mpr (by omega)
    · omega
  · intro p hp q hq heq
    have hporder : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hqorder : q.1 < q.2 := (Finset.mem_filter.mp hq).2
    have hsecond : p.1 = q.1 := congrArg Prod.snd heq
    have hfirst : p.2 - p.1 = q.2 - q.1 := congrArg Prod.fst heq
    refine Prod.ext hsecond ?_
    omega
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqT, hqsum⟩
    rcases Finset.mem_product.mp hqT with ⟨hq1, hq2⟩
    rcases Finset.mem_Ico.mp hq1 with ⟨hqlo, hqhi⟩
    have hq2' : q.2 < N := Finset.mem_range.mp hq2
    refine ⟨(q.2, q.2 + q.1), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr hqsum⟩
      · omega
    · exact Prod.ext (Nat.add_sub_cancel_left q.2 q.1) rfl
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpP, hlt⟩
    have hle : p.1 ≤ p.2 := Nat.le_of_lt hlt
    rw [Nat.add_sub_of_le hle]

/-- The real part of a complex product is unchanged when its two factors are
interchanged together with conjugation. -/
private theorem real_mul_star_symmetric (a b : ℂ) :
    RCLike.re (a * star b) = RCLike.re (b * star a) := by
  have hstar : star (a * star b) = b * star a := by simp [mul_comm]
  calc
    RCLike.re (a * star b) = RCLike.re (star (a * star b)) := by simp
    _ = RCLike.re (b * star a) := by rw [hstar]

/-- The diagonal term in the complex correlation expansion. -/
private theorem real_mul_self_star_eq_norm_sq (z : ℂ) :
    RCLike.re (z * star z) = ‖z‖ ^ 2 := by
  have hmul := congrArg RCLike.re (RCLike.mul_conj z)
  simpa [Complex.star_def, ← Complex.ofReal_pow, Complex.ofReal_re] using hmul

/-- A masked sum over a product is the sum over the corresponding filtered
pair family. -/
private theorem sum_product_if_eq_sum_filter
    {α β M : Type*} [AddCommMonoid M]
    (s : Finset α) (t : Finset β) (p : α × β → Prop)
    [DecidablePred p] (F : α → β → M) :
    (∑ a ∈ s, ∑ b ∈ t, if p (a, b) then F a b else 0) =
      ∑ q ∈ (s.product t).filter p, F q.1 q.2 := by
  classical
  let S := s.product t
  let T := S.filter p
  have hzero : ∀ q ∈ S, q ∉ T →
      (if p q then F q.1 q.2 else 0) = 0 := by
    intro q hq hnot
    have hnotp : ¬ p q := by
      intro hp
      exact hnot (Finset.mem_filter.mpr ⟨hq, hp⟩)
    simp [hnotp]
  calc
    (∑ a ∈ s, ∑ b ∈ t, if p (a, b) then F a b else 0) =
        ∑ q ∈ S, if p q then F q.1 q.2 else 0 := by
          change (∑ a ∈ s, ∑ b ∈ t,
            if p (a, b) then F a b else 0) =
              ∑ q ∈ s ×ˢ t, if p q then F q.1 q.2 else 0
          rw [← Finset.sum_product']
    _ = ∑ q ∈ T, if p q then F q.1 q.2 else 0 :=
      (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
    _ = ∑ q ∈ T, F q.1 q.2 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hp : p q := (Finset.mem_filter.mp hq).2
      simp [hp]

/-- The diagonal of a finite natural-index pair sum is its squared-norm
mass. -/
private theorem natDiagonalCorrelationSum (N : ℕ) (z : ℕ → ℂ) :
    (∑ p ∈ ((Finset.range N).product (Finset.range N)).filter
      (fun p => p.1 = p.2),
      RCLike.re (z p.2 * star (z p.1))) =
    ∑ i ∈ Finset.range N, ‖z i‖ ^ 2 := by
  classical
  let P := (Finset.range N).product (Finset.range N)
  let D := P.filter (fun p => p.1 = p.2)
  refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq heq
    rcases Finset.mem_filter.mp hp with ⟨_, hpdiag⟩
    rcases Finset.mem_filter.mp hq with ⟨_, hqdiag⟩
    apply Prod.ext heq
    calc
      p.2 = p.1 := hpdiag.symm
      _ = q.1 := heq
      _ = q.2 := hqdiag
  · intro i hi
    refine ⟨(i, i), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hi, hi⟩, rfl⟩
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpdiag⟩
    dsimp
    rw [hpdiag]
    exact real_mul_self_star_eq_norm_sq (z p.2)

/-- Swapping the two strict triangles preserves the real correlation sum. -/
private theorem natLowerTriangleCorrelationSum_eq_upper (N : ℕ)
    (z : ℕ → ℂ) :
    (∑ p ∈ ((Finset.range N).product (Finset.range N)).filter
      (fun p => p.2 < p.1),
      RCLike.re (z p.2 * star (z p.1))) =
    ∑ p ∈ ((Finset.range N).product (Finset.range N)).filter
      (fun p => p.1 < p.2),
      RCLike.re (z p.2 * star (z p.1)) := by
  classical
  let P := (Finset.range N).product (Finset.range N)
  let L := P.filter (fun p => p.2 < p.1)
  let U := P.filter (fun p => p.1 < p.2)
  change (∑ p ∈ L, RCLike.re (z p.2 * star (z p.1))) =
    ∑ p ∈ U, RCLike.re (z p.2 * star (z p.1))
  refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpP, hlt⟩
    rcases Finset.mem_product.mp hpP with ⟨hp1, hp2⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hp2, hp1⟩, hlt⟩
  · intro p hp q hq heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqP, hlt⟩
    rcases Finset.mem_product.mp hqP with ⟨hq1, hq2⟩
    refine ⟨(q.2, q.1), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hq2, hq1⟩, hlt⟩
    · rfl
  · intro p hp
    exact real_mul_star_symmetric (z p.2) (z p.1)

/-- Exact finite polarization into the diagonal and all positive-shift
correlations. The values beyond the interval are set to zero in each shift. -/
private theorem finiteNatCorrelationIdentity (N : ℕ) (z : ℕ → ℂ) :
    ‖∑ i ∈ Finset.range N, z i‖ ^ 2 =
      (∑ i ∈ Finset.range N, ‖z i‖ ^ 2) +
        2 * ∑ h ∈ Finset.Ico 1 N,
          RCLike.re (∑ i ∈ Finset.range N,
            if i + h < N then z (i + h) * star (z i) else 0) := by
  classical
  let P := (Finset.range N).product (Finset.range N)
  let term : ℕ × ℕ → ℝ := fun p => RCLike.re (z p.2 * star (z p.1))
  let U := P.filter (fun p => p.1 < p.2)
  let V := P.filter (fun p => ¬ p.1 < p.2)
  let D := V.filter (fun p => p.1 = p.2)
  let L := V.filter (fun p => p.1 ≠ p.2)
  let T := ((Finset.Ico 1 N).product (Finset.range N)).filter
    (fun q => q.2 + q.1 < N)
  have hpolar : ‖∑ i ∈ Finset.range N, z i‖ ^ 2 =
      ∑ p ∈ P, term p := by
    calc
      ‖∑ i ∈ Finset.range N, z i‖ ^ 2 =
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            RCLike.re (z i * star (z j)) :=
        FractionalPrimes.complex_norm_sum_sq_eq_re_double_sum
          (Finset.range N) z
      _ = ∑ p ∈ P, term p := by
        symm
        change (∑ p ∈ (Finset.range N ×ˢ Finset.range N), term p) =
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            RCLike.re (z i * star (z j))
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simpa [term] using (real_mul_star_symmetric (z i) (z j)).symm
  have hsplit : (∑ p ∈ P, term p) =
      (∑ p ∈ U, term p) + ∑ p ∈ V, term p := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := P)
      (p := fun p => p.1 < p.2) (f := term)]
  have hVsplit : (∑ p ∈ V, term p) =
      (∑ p ∈ D, term p) + ∑ p ∈ L, term p := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := V)
      (p := fun p => p.1 = p.2) (f := term)]
  have hDset : D = P.filter (fun p => p.1 = p.2) := by
    ext p
    simp [D, V, Finset.mem_filter]
    omega
  have hLset : L = P.filter (fun p => p.2 < p.1) := by
    ext p
    simp only [L, V, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, hnotlt⟩, hne⟩
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hlt⟩
      exact ⟨⟨hp, by omega⟩, by omega⟩
  have hdiag : (∑ p ∈ D, term p) =
      ∑ i ∈ Finset.range N, ‖z i‖ ^ 2 := by
    rw [hDset]
    exact natDiagonalCorrelationSum N z
  have hlower : (∑ p ∈ L, term p) = ∑ p ∈ U, term p := by
    rw [hLset]
    exact natLowerTriangleCorrelationSum_eq_upper N z
  have hupper : (∑ p ∈ U, term p) =
      ∑ q ∈ T, RCLike.re (z (q.2 + q.1) * star (z q.2)) := by
    simpa [U, P, term, T] using
      (upperTriangle_sum_eq_shiftPairs N
        (fun i j => RCLike.re (z j * star (z i))))
  have hmasked :
      (∑ h ∈ Finset.Ico 1 N, ∑ i ∈ Finset.range N,
        if i + h < N then RCLike.re (z (i + h) * star (z i)) else 0) =
      ∑ q ∈ T, RCLike.re (z (q.2 + q.1) * star (z q.2)) := by
    simpa [T] using
      (sum_product_if_eq_sum_filter (Finset.Ico 1 N) (Finset.range N)
        (fun q => q.2 + q.1 < N)
        (fun h i => RCLike.re (z (i + h) * star (z i))))
  have hreal (h : ℕ) :
      RCLike.re (∑ i ∈ Finset.range N,
        if i + h < N then z (i + h) * star (z i) else 0) =
      ∑ i ∈ Finset.range N,
        if i + h < N then RCLike.re (z (i + h) * star (z i)) else 0 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hcond : i + h < N <;> simp [hcond]
  have hcorr :
      ∑ h ∈ Finset.Ico 1 N,
        RCLike.re (∑ i ∈ Finset.range N,
          if i + h < N then z (i + h) * star (z i) else 0) =
      ∑ q ∈ T, RCLike.re (z (q.2 + q.1) * star (z q.2)) := by
    calc
      _ = ∑ h ∈ Finset.Ico 1 N, ∑ i ∈ Finset.range N,
          if i + h < N then RCLike.re (z (i + h) * star (z i)) else 0 := by
            apply Finset.sum_congr rfl
            intro h hh
            exact hreal h
      _ = ∑ q ∈ T, RCLike.re (z (q.2 + q.1) * star (z q.2)) := hmasked
  calc
    ‖∑ i ∈ Finset.range N, z i‖ ^ 2 = ∑ p ∈ P, term p := hpolar
    _ = (∑ p ∈ U, term p) +
        ((∑ p ∈ D, term p) + ∑ p ∈ L, term p) := by rw [hsplit, hVsplit]
    _ = (∑ i ∈ Finset.range N, ‖z i‖ ^ 2) +
        2 * ∑ p ∈ U, term p := by rw [hdiag, hlower]; ring
    _ = (∑ i ∈ Finset.range N, ‖z i‖ ^ 2) +
        2 * ∑ q ∈ T, RCLike.re (z (q.2 + q.1) * star (z q.2)) := by
          rw [hupper]
    _ = (∑ i ∈ Finset.range N, ‖z i‖ ^ 2) +
        2 * ∑ h ∈ Finset.Ico 1 N,
          RCLike.re (∑ i ∈ Finset.range N,
            if i + h < N then z (i + h) * star (z i) else 0) := by
          rw [hcorr]

/-- Reindex the integer interval `[1,N]` by `Fin N`, with the source's
one-based endpoint convention. -/
private theorem sumIcoOne_eq_sumRange {M : Type*} [AddCommMonoid M]
    (N : ℕ) (F : ℤ → M) :
    (∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1), F n) =
      ∑ k ∈ Finset.range N, F (1 + (k : ℤ)) := by
  have hIco : Finset.Ico (1 : ℤ) ((N : ℤ) + 1) =
      (Finset.range N).map
        (Nat.castEmbedding.trans (addLeftEmbedding (1 : ℤ))) := by
    simpa using Int.Ico_eq_finset_map (1 : ℤ) ((N : ℤ) + 1)
  rw [hIco, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]

/-- Summing a function on an interval after extending it by zero gives its
original interval sum. -/
private theorem zeroExtendIntegerIntervalSum (N : ℕ) (J : Finset ℤ)
    (hJ : J ⊆ Finset.Icc (1 : ℤ) (N : ℤ)) (z : ℤ → ℂ) :
    (∑ k ∈ Finset.range N,
      if (1 + (k : ℤ)) ∈ J then z (1 + (k : ℤ)) else 0) =
    ∑ n ∈ J, z n := by
  classical
  have hJI : J ⊆ Finset.Ico (1 : ℤ) ((N : ℤ) + 1) := by
    intro n hn
    rcases Finset.mem_Icc.mp (hJ hn) with ⟨hnlo, hnhi⟩
    exact Finset.mem_Ico.mpr ⟨hnlo, by omega⟩
  have hzero : ∀ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1), n ∉ J →
      (if n ∈ J then z n else 0) = 0 := by
    intro n hn hnot
    simp [hnot]
  calc
    (∑ k ∈ Finset.range N,
      if (1 + (k : ℤ)) ∈ J then z (1 + (k : ℤ)) else 0) =
        ∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1),
          if n ∈ J then z n else 0 := by
            symm
            exact sumIcoOne_eq_sumRange N (fun n => if n ∈ J then z n else 0)
    _ = ∑ n ∈ J, (if n ∈ J then z n else 0) := by
      exact (Finset.sum_subset hJI hzero).symm
    _ = ∑ n ∈ J, z n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [hn]

/-- The zero-extended correlation on `Fin N` is exactly the paper's sum over
those points of `J` whose translate by `h` remains in `J`. -/
private theorem zeroExtendIntegerIntervalCorrelation (N : ℕ) (J : Finset ℤ)
    (hJ : J ⊆ Finset.Icc (1 : ℤ) (N : ℤ)) (z : ℤ → ℂ) (h : ℕ) :
    (∑ k ∈ Finset.range N,
      if k + h < N then
        (if (1 + ((k + h : ℕ) : ℤ)) ∈ J then
          z (1 + ((k + h : ℕ) : ℤ)) else 0) *
          star (if (1 + (k : ℤ)) ∈ J then z (1 + (k : ℤ)) else 0)
      else 0) =
    ∑ n ∈ J.filter (fun n => n + (h : ℤ) ∈ J),
      z (n + (h : ℤ)) * star (z n) := by
  classical
  let u : ℤ → ℂ := fun n => if n ∈ J then z n else 0
  have hJI : J ⊆ Finset.Ico (1 : ℤ) ((N : ℤ) + 1) := by
    intro n hn
    rcases Finset.mem_Icc.mp (hJ hn) with ⟨hnlo, hnhi⟩
    exact Finset.mem_Ico.mpr ⟨hnlo, by omega⟩
  have htail (k : ℕ) (hk : k ∈ Finset.range N) (hkn : ¬ k + h < N) :
      u (1 + (k : ℤ) + (h : ℤ)) = 0 := by
    have hkN : k < N := Finset.mem_range.mp hk
    have hle : N ≤ k + h := by omega
    have hcast : 1 + ((k + h : ℕ) : ℤ) =
        1 + (k : ℤ) + (h : ℤ) := by
      push_cast
      ring
    have hnot : 1 + ((k + h : ℕ) : ℤ) ∉ J := by
      intro hmem
      have hupper := (Finset.mem_Icc.mp (hJ hmem)).2
      have hle' : (N : ℤ) ≤ (k + h : ℤ) := by exact_mod_cast hle
      omega
    have hnot' : 1 + (k : ℤ) + (h : ℤ) ∉ J := by
      rw [← hcast]
      exact hnot
    simp [u, hnot']
  have hmask :
      (∑ k ∈ Finset.range N,
        if k + h < N then
          u (1 + ((k + h : ℕ) : ℤ)) * star (u (1 + (k : ℤ))) else 0) =
      ∑ k ∈ Finset.range N,
        u (1 + ((k + h : ℕ) : ℤ)) * star (u (1 + (k : ℤ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hc : k + h < N
    · simp [hc]
    · have hassoc : 1 + ((k : ℤ) + (h : ℤ)) =
          1 + (k : ℤ) + (h : ℤ) := by ring
      simp [hc, hassoc, htail k hk hc]
  have hmap :
      (∑ k ∈ Finset.range N,
        u (1 + ((k + h : ℕ) : ℤ)) * star (u (1 + (k : ℤ))) =
       ∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1),
        u (n + (h : ℤ)) * star (u n)) := by
    have hbase := (sumIcoOne_eq_sumRange N
      (fun n => u (n + (h : ℤ)) * star (u n))).symm
    calc
      _ = ∑ k ∈ Finset.range N,
          u (1 + (k : ℤ) + (h : ℤ)) * star (u (1 + (k : ℤ))) := by
            apply Finset.sum_congr rfl
            intro k hk
            congr 1
            · push_cast
              ac_rfl
      _ = ∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1),
          u (n + (h : ℤ)) * star (u n) := hbase
  have hsupport :
      (∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1),
        u (n + (h : ℤ)) * star (u n)) =
      ∑ n ∈ J, u (n + (h : ℤ)) * star (u n) := by
    have hzero : ∀ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1), n ∉ J →
        u (n + (h : ℤ)) * star (u n) = 0 := by
      intro n hn hnot
      simp [u, hnot]
    exact (Finset.sum_subset hJI hzero).symm
  have hreduce :
      (∑ n ∈ J, u (n + (h : ℤ)) * star (u n)) =
      ∑ n ∈ J.filter (fun n => n + (h : ℤ) ∈ J),
        z (n + (h : ℤ)) * star (z n) := by
    calc
      _ = ∑ n ∈ J,
          if n + (h : ℤ) ∈ J then z (n + (h : ℤ)) * star (z n) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [u, hn]
      _ = _ := by rw [← Finset.sum_filter]
  calc
    _ = ∑ k ∈ Finset.range N,
        if k + h < N then
          u (1 + ((k + h : ℕ) : ℤ)) * star (u (1 + (k : ℤ))) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [u]
    _ = ∑ k ∈ Finset.range N,
        u (1 + ((k + h : ℕ) : ℤ)) * star (u (1 + (k : ℤ))) := hmask
    _ = ∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1),
        u (n + (h : ℤ)) * star (u n) := hmap
    _ = ∑ n ∈ J, u (n + (h : ℤ)) * star (u n) := hsupport
    _ = _ := hreduce

/-- Blueprint `lbi:weyl-shifts`: a large modulus-one sum on an integer
interval in `[1,N]` forces at least `δ²N/8` shifts in `[1,N)` to have
correlation at least `δ²N/8`. -/
theorem manyLongShiftCorrelations {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (_hδhalf : δ < 1 / 2)
    (hNlarge : 4 / δ ^ 2 ≤ (N : ℝ)) (J : Finset ℤ)
    (_hJinterval : ∃ a b : ℤ, J = Finset.Ico a b)
    (hJ : J ⊆ Finset.Icc (1 : ℤ) (N : ℤ)) (z : ℤ → ℂ)
    (hz : ∀ n ∈ J, ‖z n‖ = 1)
    (hlarge : δ * (N : ℝ) ≤ ‖∑ n ∈ J, z n‖) :
    δ ^ 2 * (N : ℝ) / 8 ≤
      (((Finset.Ico (1 : ℕ) N).filter (fun h : ℕ =>
        δ ^ 2 * (N : ℝ) / 8 ≤
          ‖∑ n ∈ J.filter (fun n => n + (h : ℤ) ∈ J),
            z (n + (h : ℤ)) * star (z n)‖)).card : ℝ) := by
  classical
  let W : ℕ → ℂ := fun k =>
    if (1 + (k : ℤ)) ∈ J then z (1 + (k : ℤ)) else 0
  let C : ℕ → ℂ := fun h =>
    ∑ n ∈ J.filter (fun n => n + (h : ℤ) ∈ J),
      z (n + (h : ℤ)) * star (z n)
  have hJI : J ⊆ Finset.Ico (1 : ℤ) ((N : ℤ) + 1) := by
    intro n hn
    rcases Finset.mem_Icc.mp (hJ hn) with ⟨hnlo, hnhi⟩
    exact Finset.mem_Ico.mpr ⟨hnlo, by omega⟩
  have hsumJ : (∑ k ∈ Finset.range N, W k) = ∑ n ∈ J, z n := by
    simpa [W] using zeroExtendIntegerIntervalSum N J hJ z
  have hWle (k : ℕ) (hk : k ∈ Finset.range N) : ‖W k‖ ≤ 1 := by
    by_cases hmem : (1 + (k : ℤ)) ∈ J
    · simp [W, hmem, hz (1 + (k : ℤ)) hmem]
    · simp [W, hmem]
  have hdiag :
      (∑ k ∈ Finset.range N, ‖W k‖ ^ 2) ≤ (N : ℝ) := by
    calc
      (∑ k ∈ Finset.range N, ‖W k‖ ^ 2) ≤
          ∑ _k ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hnorm0 : 0 ≤ ‖W k‖ := norm_nonneg _
        have hnorm1 := hWle k hk
        nlinarith
      _ = (N : ℝ) := by simp
  have hWsumLarge :
      δ * (N : ℝ) ≤ ‖∑ k ∈ Finset.range N, W k‖ := by
    calc
      δ * (N : ℝ) ≤ ‖∑ n ∈ J, z n‖ := hlarge
      _ = ‖∑ k ∈ Finset.range N, W k‖ := by rw [← hsumJ]
  have hnormsq : δ ^ 2 * (N : ℝ) ^ 2 ≤
      ‖∑ k ∈ Finset.range N, W k‖ ^ 2 := by
    have hsq := (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hWsumLarge
    nlinarith [hsq]
  have hnormsqJ : δ ^ 2 * (N : ℝ) ^ 2 ≤
      ‖∑ n ∈ J, z n‖ ^ 2 := by
    simpa [hsumJ] using hnormsq
  have hscale : 4 ≤ δ ^ 2 * (N : ℝ) := by
    have hmul := (div_le_iff₀ (pow_pos hδ 2)).mp hNlarge
    nlinarith [hmul]
  have hNle : (N : ℝ) ≤ δ ^ 2 * (N : ℝ) ^ 2 / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hmul := mul_le_mul_of_nonneg_right hscale (by positivity : 0 ≤ (N : ℝ))
    nlinarith [hmul]
  have hcor (h : ℕ) :
      (∑ k ∈ Finset.range N,
        if k + h < N then W (k + h) * star (W k) else 0) = C h := by
    simpa [W, C] using zeroExtendIntegerIntervalCorrelation N J hJ z h
  have hpolar :
      ‖∑ n ∈ J, z n‖ ^ 2 =
        (∑ k ∈ Finset.range N, ‖W k‖ ^ 2) +
          2 * ∑ h ∈ Finset.Ico (1 : ℕ) N, RCLike.re (C h) := by
    have hid := finiteNatCorrelationIdentity N W
    rw [hsumJ] at hid
    have hcorrsum :
        (∑ h ∈ Finset.Ico (1 : ℕ) N,
          RCLike.re (∑ k ∈ Finset.range N,
            if k + h < N then W (k + h) * star (W k) else 0)) =
        ∑ h ∈ Finset.Ico (1 : ℕ) N, RCLike.re (C h) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [hcor h]
    rw [hcorrsum] at hid
    exact hid
  have hrealMass : δ ^ 2 * (N : ℝ) ^ 2 / 4 ≤
      ∑ h ∈ Finset.Ico 1 N, RCLike.re (C h) := by
    have hlower : δ ^ 2 * (N : ℝ) ^ 2 - (N : ℝ) ≤
        2 * ∑ h ∈ Finset.Ico 1 N, RCLike.re (C h) := by
      nlinarith [hnormsqJ, hdiag, hpolar]
    nlinarith [hlower, hNle]
  have hmass : δ ^ 2 * (N : ℝ) ^ 2 / 4 ≤
      ∑ h ∈ Finset.Ico 1 N, ‖C h‖ := by
    calc
      δ ^ 2 * (N : ℝ) ^ 2 / 4 ≤
      ∑ h ∈ Finset.Ico (1 : ℕ) N, RCLike.re (C h) := hrealMass
      _ ≤ ∑ h ∈ Finset.Ico (1 : ℕ) N, ‖C h‖ := by
        apply Finset.sum_le_sum
        intro h hh
        exact Complex.re_le_norm (C h)
  have hIcoCard : (Finset.Ico (1 : ℤ) ((N : ℤ) + 1)).card = N := by
    rw [Int.card_Ico]
    simp
  have hJcard : J.card ≤ N := by
    calc
      J.card ≤ (Finset.Ico (1 : ℤ) ((N : ℤ) + 1)).card :=
        Finset.card_le_card hJI
      _ = N := hIcoCard
  have hCbound (h : ℕ) (_hh : h ∈ Finset.Ico (1 : ℕ) N) : ‖C h‖ ≤ N := by
    dsimp [C]
    have hterms :
        (∑ n ∈ J.filter (fun n => n + (h : ℤ) ∈ J),
          ‖z (n + (h : ℤ)) * star (z n)‖) =
        ((J.filter (fun n => n + (h : ℤ) ∈ J)).card : ℝ) := by
      calc
        _ = ∑ _n ∈ J.filter (fun n => n + (h : ℤ) ∈ J), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          rcases Finset.mem_filter.mp hn with ⟨hnJ, htrans⟩
          rw [norm_mul, norm_star, hz (n + (h : ℤ)) htrans, hz n hnJ]
          norm_num
        _ = _ := by simp
    calc
      _ ≤ ∑ n ∈ J.filter (fun n => n + (h : ℤ) ∈ J),
          ‖z (n + (h : ℤ)) * star (z n)‖ := norm_sum_le _ _
      _ = ((J.filter (fun n => n + (h : ℤ) ∈ J)).card : ℝ) := hterms
      _ ≤ (N : ℝ) := by
        have hsub : J.filter (fun n => n + (h : ℤ) ∈ J) ⊆ J :=
          Finset.filter_subset _ _
        exact_mod_cast (Nat.le_trans (Finset.card_le_card hsub) hJcard)
  have hcount := manyLargeShiftCorrelations_count_of_mass hN C hmass hCbound
  simpa [C] using hcount

/-- The recursively defined natural-coefficient polynomial `F_d` from
blueprint `lbi:weyl-constants`. The unused index zero is assigned zero so
that the degree recursion is structural. -/
noncomputable def weylBoundPolynomial : ℕ → Polynomial ℕ
  | 0 => 0
  | 1 => C 2 * X
  | d + 2 =>
      let B := (weylBoundPolynomial (d + 1)).comp (C 8 * X ^ 2)
      let R := C (8192 * (d + 2)) * X ^ 4 * B ^ 3
      let D := (weylBoundPolynomial (d + 1)).comp (C 4 * X * (1 + C 8 * R))
      (C 4 * R) ^ (d + 2) + C (2 ^ (d + 2)) * D * R ^ (d + 1) + 1

/-- The polynomial `B_d` used in the approved scalar Weyl constants. -/
noncomputable def weylBoundPolynomialB (d : ℕ) : Polynomial ℕ :=
  (weylBoundPolynomial (d - 1)).comp (C 8 * X ^ 2)

/-- The polynomial `R_d` used in the approved scalar Weyl constants. -/
noncomputable def weylBoundPolynomialR (d : ℕ) : Polynomial ℕ :=
  C (8192 * d) * X ^ 4 * (weylBoundPolynomialB d) ^ 3

/-- The polynomial `D_d` used in the approved scalar Weyl constants. -/
noncomputable def weylBoundPolynomialD (d : ℕ) : Polynomial ℕ :=
  (weylBoundPolynomial (d - 1)).comp
    (C 4 * X * (1 + C 8 * weylBoundPolynomialR d))

@[simp] theorem weylBoundPolynomial_zero :
    weylBoundPolynomial 0 = 0 := rfl

@[simp] theorem weylBoundPolynomial_one :
    weylBoundPolynomial 1 = C 2 * X := rfl

/-- Exact recursion clause for every degree `d≥2`, with the four
polynomials named as in the approved definition. -/
theorem weylBoundPolynomial_recursion (d : ℕ) :
    weylBoundPolynomial (d + 2) =
      (C 4 * weylBoundPolynomialR (d + 2)) ^ (d + 2) +
        C (2 ^ (d + 2)) * weylBoundPolynomialD (d + 2) *
          weylBoundPolynomialR (d + 2) ^ (d + 1) + 1 := by
  simp [weylBoundPolynomial, weylBoundPolynomialB, weylBoundPolynomialR,
    weylBoundPolynomialD]

/-- `K_d=F_d(1)` as an exact natural number. -/
noncomputable def weylBoundConstant (d : ℕ) : ℕ :=
  (weylBoundPolynomial d).eval 1

/-- The natural-degree representative of `c_d=deg(F_d)`. The later
nonvanishing lemma identifies this with the usual polynomial degree. -/
noncomputable def weylBoundExponent (d : ℕ) : ℕ :=
  (weylBoundPolynomial d).natDegree

/-- Evaluating an approved scalar-Weyl polynomial at one gives a positive
natural number. For degrees at least two, this follows from the literal
constant `+1` in the recursion. -/
theorem weylBoundPolynomial_eval_one_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < (weylBoundPolynomial d).eval 1 := by
  rcases d with _ | d
  · omega
  rcases d with _ | d
  · simp [weylBoundPolynomial]
  · rw [weylBoundPolynomial_recursion d]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_one]
    omega

/-- Every approved scalar-Weyl polynomial in its stated range is nonzero. -/
theorem weylBoundPolynomial_ne_zero (d : ℕ) (hd : 1 ≤ d) :
    weylBoundPolynomial d ≠ 0 := by
  intro hzero
  have hEval : (weylBoundPolynomial d).eval 1 = 0 := by
    simpa using congrArg (fun p : Polynomial ℕ => p.eval 1) hzero
  exact (ne_of_gt (weylBoundPolynomial_eval_one_pos d hd)) hEval

/-- The approved scalar-Weyl constant `K_d=F_d(1)` is positive. -/
theorem weylBoundConstant_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < weylBoundConstant d := by
  change 0 < (weylBoundPolynomial d).eval 1
  exact weylBoundPolynomial_eval_one_pos d hd

/-- On the approved positive-degree range, the natural-degree exponent used
in Lean is exactly Mathlib's usual polynomial degree. -/
theorem weylBoundExponent_eq_degree (d : ℕ) (hd : 1 ≤ d) :
    (weylBoundPolynomial d).degree = (weylBoundExponent d : WithBot ℕ) := by
  exact Polynomial.degree_eq_natDegree (weylBoundPolynomial_ne_zero d hd)

theorem weylBoundPolynomialB_natDegree (d : ℕ) :
    (weylBoundPolynomialB d).natDegree = 2 * weylBoundExponent (d - 1) := by
  rw [weylBoundPolynomialB, Polynomial.natDegree_comp]
  simp only [weylBoundExponent]
  rw [Polynomial.natDegree_C_mul (by norm_num : (8 : ℕ) ≠ 0), Polynomial.natDegree_X_pow]
  exact Nat.mul_comm _ _

theorem weylBoundPolynomialR_natDegree (d : ℕ) (hd : 2 ≤ d)
    (hprev : 0 < weylBoundExponent (d - 1)) :
    (weylBoundPolynomialR d).natDegree = 4 + 6 * weylBoundExponent (d - 1) := by
  have hc : (8192 * d : ℕ) ≠ 0 := by omega
  have hB := weylBoundPolynomialB_natDegree d
  have hBpos : 0 < (weylBoundPolynomialB d).natDegree := by
    rw [hB]
    omega
  have hBne : weylBoundPolynomialB d ≠ 0 := ne_zero_of_natDegree_gt hBpos
  have hC : (Polynomial.C (8192 * d) : Polynomial ℕ) ≠ 0 := C_ne_zero.mpr hc
  have hX : (Polynomial.X : Polynomial ℕ) ^ 4 ≠ 0 := pow_ne_zero _ X_ne_zero
  have hleft : Polynomial.C (8192 * d) * Polynomial.X ^ 4 ≠ 0 := mul_ne_zero hC hX
  have hBpow : (weylBoundPolynomialB d) ^ 3 ≠ 0 := pow_ne_zero _ hBne
  rw [weylBoundPolynomialR,
    Polynomial.natDegree_mul hleft hBpow,
    Polynomial.natDegree_mul hC hX,
    Polynomial.natDegree_C,
    Polynomial.natDegree_X_pow,
    Polynomial.natDegree_pow,
    hB]
  simp only [weylBoundExponent]
  omega

theorem weylBoundPolynomialD_natDegree (d : ℕ) (hd : 2 ≤ d)
    (hprev : 0 < weylBoundExponent (d - 1)) :
    (weylBoundPolynomialD d).natDegree =
      weylBoundExponent (d - 1) * (5 + 6 * weylBoundExponent (d - 1)) := by
  have hR := weylBoundPolynomialR_natDegree d hd hprev
  have hRpos : 0 < (weylBoundPolynomialR d).natDegree := by rw [hR]; omega
  have hRne : weylBoundPolynomialR d ≠ 0 := ne_zero_of_natDegree_gt hRpos
  have hC8 : (Polynomial.C 8 : Polynomial ℕ) ≠ 0 := C_ne_zero.mpr (by norm_num)
  have hC8R : Polynomial.C 8 * weylBoundPolynomialR d ≠ 0 := mul_ne_zero hC8 hRne
  have hOnePlus : (1 + Polynomial.C 8 * weylBoundPolynomialR d).natDegree =
      (weylBoundPolynomialR d).natDegree := by
    rw [add_comm, Polynomial.natDegree_add_one,
      Polynomial.natDegree_C_mul (by norm_num : (8 : ℕ) ≠ 0)]
  have hInnerPos : 0 < (1 + Polynomial.C 8 * weylBoundPolynomialR d).natDegree := by
    rw [hOnePlus, hR]
    omega
  have hInner : 1 + Polynomial.C 8 * weylBoundPolynomialR d ≠ 0 :=
    ne_zero_of_natDegree_gt hInnerPos
  have hC4 : (Polynomial.C 4 : Polynomial ℕ) ≠ 0 := C_ne_zero.mpr (by norm_num)
  have hX : (Polynomial.X : Polynomial ℕ) ≠ 0 := X_ne_zero
  have hLinear : Polynomial.C 4 * Polynomial.X ≠ 0 := mul_ne_zero hC4 hX
  rw [weylBoundPolynomialD, Polynomial.natDegree_comp,
    Polynomial.natDegree_mul hLinear hInner,
    Polynomial.natDegree_mul hC4 hX,
    Polynomial.natDegree_C,
    Polynomial.natDegree_X, hOnePlus, hR]
  simp only [weylBoundExponent]
  ring

theorem weylBoundExponent_recursion_of_pos (k : ℕ)
    (hprev : 0 < weylBoundExponent (k + 1)) :
    weylBoundExponent (k + 2) =
      6 * weylBoundExponent (k + 1) ^ 2 +
        (6 * (k + 2) - 1) * weylBoundExponent (k + 1) + 4 * (k + 2) - 4 := by
  let c : ℕ := weylBoundExponent (k + 1)
  let r : ℕ := 4 + 6 * c
  have hc : 0 < c := hprev
  have hR : (weylBoundPolynomialR (k + 2)).natDegree = r := by
    simpa [r, c] using
      (weylBoundPolynomialR_natDegree (k + 2) (by omega) hprev)
  have hD : (weylBoundPolynomialD (k + 2)).natDegree = c * (5 + 6 * c) := by
    simpa [c] using
      (weylBoundPolynomialD_natDegree (k + 2) (by omega) hprev)
  have hRpos : 0 < (weylBoundPolynomialR (k + 2)).natDegree := by rw [hR]; omega
  have hRne : weylBoundPolynomialR (k + 2) ≠ 0 := ne_zero_of_natDegree_gt hRpos
  have hDpos : 0 < (weylBoundPolynomialD (k + 2)).natDegree := by
    rw [hD]
    exact Nat.mul_pos hc (by omega)
  have hDne : weylBoundPolynomialD (k + 2) ≠ 0 := ne_zero_of_natDegree_gt hDpos
  have hC4 : (Polynomial.C 4 : Polynomial ℕ) ≠ 0 := C_ne_zero.mpr (by norm_num)
  have hC4R : Polynomial.C 4 * weylBoundPolynomialR (k + 2) ≠ 0 :=
    mul_ne_zero hC4 hRne
  have hFirst :
      ((Polynomial.C 4 * weylBoundPolynomialR (k + 2)) ^ (k + 2)).natDegree = (k + 2) * r := by
    rw [Polynomial.natDegree_pow,
      Polynomial.natDegree_mul hC4 hRne,
      Polynomial.natDegree_C, hR]
    simp
  have hCoeff : (Polynomial.C (2 ^ (k + 2)) : Polynomial ℕ) ≠ 0 :=
    C_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
  have hRpow : (weylBoundPolynomialR (k + 2)) ^ (k + 1) ≠ 0 :=
    pow_ne_zero _ hRne
  have hDandR :
      weylBoundPolynomialD (k + 2) * (weylBoundPolynomialR (k + 2)) ^ (k + 1) ≠ 0 :=
    mul_ne_zero hDne hRpow
  have hSecond :
      (Polynomial.C (2 ^ (k + 2)) * weylBoundPolynomialD (k + 2) *
        weylBoundPolynomialR (k + 2) ^ (k + 1)).natDegree =
          c * (5 + 6 * c) + (k + 1) * r := by
    rw [mul_assoc,
      Polynomial.natDegree_mul hCoeff hDandR,
      Polynomial.natDegree_C,
      Polynomial.natDegree_mul hDne hRpow,
      Polynomial.natDegree_pow, hD, hR]
    simp
  have hcSq : c ≤ c * c := by
    simpa using Nat.mul_le_mul_left c (by omega : 1 ≤ c)
  have hFirstLt :
      ((Polynomial.C 4 * weylBoundPolynomialR (k + 2)) ^ (k + 2)).natDegree <
        (Polynomial.C (2 ^ (k + 2)) * weylBoundPolynomialD (k + 2) *
          weylBoundPolynomialR (k + 2) ^ (k + 1)).natDegree := by
    rw [hFirst, hSecond]
    dsimp [r]
    nlinarith [hcSq]
  have hF : (weylBoundPolynomial (k + 2)).natDegree =
      c * (5 + 6 * c) + (k + 1) * r := by
    rw [weylBoundPolynomial_recursion k,
      Polynomial.natDegree_add_one,
      Polynomial.natDegree_add_eq_right_of_natDegree_lt hFirstLt,
      hSecond]
  change (weylBoundPolynomial (k + 2)).natDegree =
    6 * c ^ 2 + (6 * (k + 2) - 1) * c + 4 * (k + 2) - 4
  rw [hF]
  dsimp [r]
  have h6 : 6 * (k + 2) - 1 = 6 * k + 11 := by omega
  have hpoly : c * (5 + 6 * c) + (k + 1) * (4 + 6 * c) =
      6 * c ^ 2 + (6 * k + 11) * c + 4 * k + 4 := by ring
  rw [h6, hpoly]
  omega

theorem weylBoundExponent_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < weylBoundExponent d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    rcases d with _ | d
    · omega
    rcases d with _ | d
    · simp [weylBoundExponent, weylBoundPolynomial]
    · have hprev : 0 < weylBoundExponent (d + 1) :=
        ih (d + 1) (by omega) (by omega)
      rw [weylBoundExponent_recursion_of_pos d hprev]
      omega

theorem weylBoundExponent_recursion (d : ℕ) (hd : 2 ≤ d) :
    weylBoundExponent d =
      6 * weylBoundExponent (d - 1) ^ 2 +
        (6 * d - 1) * weylBoundExponent (d - 1) + 4 * d - 4 := by
  rcases d with _ | d
  · omega
  rcases d with _ | d
  · omega
  have hprev : 0 < weylBoundExponent (d + 1) :=
    weylBoundExponent_pos (d + 1) (by omega)
  simpa using weylBoundExponent_recursion_of_pos d hprev

private theorem natPolynomial_eval_power_bounds (p : Polynomial ℕ) (x : ℝ)
    (hx : 1 ≤ x) :
    ((p.eval (1 : ℕ) : ℕ) : ℝ) ≤ p.eval₂ (Nat.castRingHom ℝ) x ∧
      p.eval₂ (Nat.castRingHom ℝ) x ≤ ((p.eval (1 : ℕ) : ℕ) : ℝ) * x ^ p.natDegree := by
  let s := Finset.range (p.natDegree + 1)
  have hsum : (∑ i ∈ s, (p.coeff i : ℝ)) = ((p.eval (1 : ℕ) : ℕ) : ℝ) := by
    calc
      (∑ i ∈ s, (p.coeff i : ℝ)) = p.eval₂ (Nat.castRingHom ℝ) 1 := by
        symm
        dsimp [s]
        rw [Polynomial.eval₂_eq_sum_range]
        simp
      _ = ((p.eval (1 : ℕ) : ℕ) : ℝ) := by
        rw [Polynomial.eval₂_at_one]
        simp
  have hEvalX : p.eval₂ (Nat.castRingHom ℝ) x =
      ∑ i ∈ s, (p.coeff i : ℝ) * x ^ i := by
    dsimp [s]
    rw [Polynomial.eval₂_eq_sum_range]
    simp
  have hloTerms :
      (∑ i ∈ s, (p.coeff i : ℝ)) ≤
        ∑ i ∈ s, (p.coeff i : ℝ) * x ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    have hiPow := pow_le_pow_right₀ hx (Nat.zero_le i)
    calc
      (p.coeff i : ℝ) = (p.coeff i : ℝ) * 1 := by simp
      _ ≤ (p.coeff i : ℝ) * x ^ i :=
        mul_le_mul_of_nonneg_left hiPow (Nat.cast_nonneg _)
  have hhiTerms :
      (∑ i ∈ s, (p.coeff i : ℝ) * x ^ i) ≤
        ∑ i ∈ s, (p.coeff i : ℝ) * x ^ p.natDegree := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hiDeg : i ≤ p.natDegree := by
      dsimp [s] at hi
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact pow_le_pow_right₀ hx hiDeg
  constructor
  · calc
      ((p.eval (1 : ℕ) : ℕ) : ℝ) = ∑ i ∈ s, (p.coeff i : ℝ) := hsum.symm
      _ ≤ ∑ i ∈ s, (p.coeff i : ℝ) * x ^ i := hloTerms
      _ = p.eval₂ (Nat.castRingHom ℝ) x := hEvalX.symm
  · calc
      p.eval₂ (Nat.castRingHom ℝ) x =
          ∑ i ∈ s, (p.coeff i : ℝ) * x ^ i := hEvalX
      _ ≤ ∑ i ∈ s, (p.coeff i : ℝ) * x ^ p.natDegree := hhiTerms
      _ = (∑ i ∈ s, (p.coeff i : ℝ)) * x ^ p.natDegree := by
        rw [Finset.sum_mul]
      _ = ((p.eval (1 : ℕ) : ℕ) : ℝ) * x ^ p.natDegree := by rw [hsum]

private theorem natPolynomial_eval_one_le_eval (p : Polynomial ℕ) (x : ℕ)
    (hx : 1 ≤ x) : p.eval 1 ≤ p.eval x := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  apply Finset.sum_le_sum
  intro i hi
  have hiPow := pow_le_pow_right' hx (Nat.zero_le i)
  exact Nat.mul_le_mul_left (p.coeff i) (by simpa using hiPow)

theorem weylBoundConstant_ge_two (d : ℕ) (hd : 1 ≤ d) :
    2 ≤ weylBoundConstant d := by
  rcases d with _ | d
  · omega
  rcases d with _ | d
  · simp [weylBoundConstant, weylBoundPolynomial]
  let n := d + 2
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hprev : 1 ≤ weylBoundConstant (n - 1) := by
    have hpos := weylBoundPolynomial_eval_one_pos (n - 1) (by omega)
    simpa [weylBoundConstant] using Nat.succ_le_iff.mpr hpos
  have hB_eval : (weylBoundPolynomialB n).eval 1 =
      (weylBoundPolynomial (n - 1)).eval 8 := by
    rw [weylBoundPolynomialB, Polynomial.eval_comp]
    simp
  have hB_ge : 1 ≤ (weylBoundPolynomialB n).eval 1 := by
    rw [hB_eval]
    exact hprev.trans
      (natPolynomial_eval_one_le_eval (weylBoundPolynomial (n - 1)) 8 (by norm_num))
  have hR_eval : (weylBoundPolynomialR n).eval 1 =
      (8192 * n) * (weylBoundPolynomialB n).eval 1 ^ 3 := by
    simp [weylBoundPolynomialR]
  have hR_ge : 1 ≤ (weylBoundPolynomialR n).eval 1 := by
    have hcoef : 1 ≤ 8192 * n := by omega
    have hpow : 1 ≤ (weylBoundPolynomialB n).eval 1 ^ 3 :=
      Nat.one_le_pow _ _ hB_ge
    rw [hR_eval]
    calc
      1 ≤ 8192 * n := hcoef
      _ ≤ (8192 * n) * (weylBoundPolynomialB n).eval 1 ^ 3 := by
        simpa using Nat.mul_le_mul_left (8192 * n) hpow
  have hbase : 1 ≤ (Polynomial.C 4 * weylBoundPolynomialR n).eval 1 := by
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hfirst : 1 ≤ ((Polynomial.C 4 * weylBoundPolynomialR n) ^ n).eval 1 := by
    simpa [Polynomial.eval_pow] using Nat.one_le_pow _ _ hbase
  have hRecEval : (weylBoundPolynomial n).eval 1 =
      ((Polynomial.C 4 * weylBoundPolynomialR n) ^ n).eval 1 +
        (Polynomial.C (2 ^ n) * weylBoundPolynomialD n *
          weylBoundPolynomialR n ^ (n - 1)).eval 1 + 1 := by
    have h := congrArg (fun p : Polynomial ℕ => p.eval 1)
      (weylBoundPolynomial_recursion (n - 2))
    have hnrec : n - 2 + 2 = n := by omega
    have hnsub : n - 2 + 1 = n - 1 := by omega
    simpa [Polynomial.eval_add, hnrec, hnsub] using h
  have hK : 2 ≤ weylBoundConstant n := by
    rw [weylBoundConstant, hRecEval]
    omega
  simpa [n] using hK

theorem weylBoundExponent_ge_one (d : ℕ) (hd : 1 ≤ d) :
    1 ≤ weylBoundExponent d := by
  exact Nat.succ_le_iff.mpr (weylBoundExponent_pos d hd)

theorem weylBoundPowerControl (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) x ∧
      (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) x ≤
        (weylBoundConstant d : ℝ) * x ^ weylBoundExponent d := by
  have hEval := natPolynomial_eval_power_bounds (weylBoundPolynomial d) x hx
  have hKnat : 1 ≤ weylBoundConstant d := by
    exact le_trans (by decide : 1 ≤ 2) (weylBoundConstant_ge_two d hd)
  have hKreal : (1 : ℝ) ≤ (weylBoundConstant d : ℝ) := by
    exact_mod_cast hKnat
  have hKlower : (1 : ℝ) ≤ (((weylBoundPolynomial d).eval (1 : ℕ) : ℕ) : ℝ) := by
    simpa [weylBoundConstant] using hKreal
  constructor
  · exact hKlower.trans hEval.1
  · simpa [weylBoundConstant, weylBoundExponent] using hEval.2

private theorem natPolynomial_eval₂_nonneg_of_ge_one (p : Polynomial ℕ)
    (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  have hEval := natPolynomial_eval_power_bounds p x hx
  have hp : (0 : ℝ) ≤ ((p.eval (1 : ℕ) : ℕ) : ℝ) := by positivity
  exact hp.trans hEval.1

/-- The first recursive term is a lower bound for the full bound polynomial.
This is the source estimate used in the short-length case of the scalar Weyl
inverse theorem. -/
theorem weylBoundPolynomial_mainTerm_le (d : ℕ) (hd : 2 ≤ d)
    (x : ℝ) (hx : 1 ≤ x) :
    (4 * (weylBoundPolynomialR d).eval₂ (Nat.castRingHom ℝ) x) ^ d ≤
      (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hrec := congrArg
    (fun p : Polynomial ℕ => p.eval₂ (Nat.castRingHom ℝ) x)
    (weylBoundPolynomial_recursion k)
  have hrecEval := hrec
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add] at hrecEval
  simp only [Polynomial.eval₂_one] at hrecEval
  have hmain :
      ((Polynomial.C 4 * weylBoundPolynomialR (k + 2)) ^ (k + 2)).eval₂
          (Nat.castRingHom ℝ) x =
        (4 * (weylBoundPolynomialR (k + 2)).eval₂ (Nat.castRingHom ℝ) x) ^
          (k + 2) := by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_C]
    simp
  have hother :
      0 ≤ (Polynomial.C (2 ^ (k + 2)) * weylBoundPolynomialD (k + 2) *
          weylBoundPolynomialR (k + 2) ^ (k + 1)).eval₂
          (Nat.castRingHom ℝ) x :=
    natPolynomial_eval₂_nonneg_of_ge_one _ x hx
  have htarget :
      (4 * (weylBoundPolynomialR (k + 2)).eval₂ (Nat.castRingHom ℝ) x) ^ (k + 2) ≤
        (weylBoundPolynomial (k + 2)).eval₂ (Nat.castRingHom ℝ) x := by
    rw [hrecEval]
    rw [← hmain]
    nlinarith
  simpa [Nat.add_comm] using htarget

/-- After the affine recurrence step, combine its denominator `q₁` with
`q₀d` to obtain the source denominator `r=dq₀q₁` and the stated top
coefficient bound. -/
theorem scalarWeyl_combineTopCoefficientDenominators
    {d N q0 q1 : ℕ} {B σ αd : ℝ}
    (hd : 2 ≤ d) (hB : 1 ≤ B) (hσ : 0 < σ) (hσle : σ ≤ 1)
    (hq0lo : 1 ≤ q0) (hq0hi : (q0 : ℝ) ≤ B)
    (hq1lo : 1 ≤ q1) (hq1hi : (q1 : ℝ) ≤ 2 / σ)
    (hnear : realDistanceToIntegers
      ((q1 : ℝ) * ((q0 : ℝ) * (d : ℝ) * αd)) ≤
        16 * B * (σ⁻¹)^2 / ((N : ℝ) ^ d)) :
    1 ≤ d * q0 * q1 ∧
      ((d * q0 * q1 : ℕ) : ℝ) ≤
        32 * (d : ℝ) * B * (σ⁻¹)^2 ∧
      realDistanceToIntegers (((d * q0 * q1 : ℕ) : ℝ) * αd) ≤
        32 * (d : ℝ) * B * (σ⁻¹)^2 / ((N : ℝ) ^ d) := by
  have hdR : 0 ≤ (d : ℝ) := by positivity
  have hq0R : 0 ≤ (q0 : ℝ) := by positivity
  have hq1R : 0 ≤ (q1 : ℝ) := by positivity
  have hBR : 0 ≤ B := le_trans (by norm_num) hB
  have hσsq : σ ^ 2 ≤ σ := by
    calc
      σ ^ 2 = σ * σ := by ring
      _ ≤ 1 * σ := mul_le_mul_of_nonneg_right hσle hσ.le
      _ = σ := by ring
  have hscale : 2 / σ ≤ 32 * (σ⁻¹)^2 := by
    calc
      2 / σ ≤ 32 / σ ^ 2 := by
        apply (div_le_div_iff₀ hσ (pow_pos hσ 2)).2
        nlinarith [hσsq, hσle]
      _ = 32 * (σ⁻¹)^2 := by
        field_simp [ne_of_gt hσ] <;> ring
  have hrCast : ((d * q0 * q1 : ℕ) : ℝ) =
      (d : ℝ) * (q0 : ℝ) * (q1 : ℝ) := by
    push_cast
    ring
  have hrUpper : ((d * q0 * q1 : ℕ) : ℝ) ≤
      32 * (d : ℝ) * B * (σ⁻¹)^2 := by
    rw [hrCast]
    calc
      (d : ℝ) * (q0 : ℝ) * (q1 : ℝ) ≤
          ((d : ℝ) * B) * (q1 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq0hi hdR) hq1R
      _ ≤ ((d : ℝ) * B) * (2 / σ) :=
        mul_le_mul_of_nonneg_left hq1hi (mul_nonneg hdR hBR)
      _ ≤ ((d : ℝ) * B) * (32 * (σ⁻¹)^2) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg hdR hBR)
      _ = 32 * (d : ℝ) * B * (σ⁻¹)^2 := by ring
  have hcoef : 16 * B * (σ⁻¹)^2 ≤
      32 * (d : ℝ) * B * (σ⁻¹)^2 := by
    have hdR' : 2 ≤ (d : ℝ) := by exact_mod_cast hd
    have hfactor : 0 ≤ B * (σ⁻¹)^2 := mul_nonneg hBR (sq_nonneg _)
    calc
      16 * B * (σ⁻¹)^2 = 16 * (B * (σ⁻¹)^2) := by ring
      _ ≤ (32 * (d : ℝ)) * (B * (σ⁻¹)^2) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hfactor
      _ = 32 * (d : ℝ) * B * (σ⁻¹)^2 := by ring
  have hdistPhase :
      realDistanceToIntegers (((d * q0 * q1 : ℕ) : ℝ) * αd) ≤
        16 * B * (σ⁻¹)^2 / ((N : ℝ) ^ d) := by
    rw [hrCast]
    convert hnear using 1 <;> ring
  have hdistUpper :
      16 * B * (σ⁻¹)^2 / ((N : ℝ) ^ d) ≤
        32 * (d : ℝ) * B * (σ⁻¹)^2 / ((N : ℝ) ^ d) :=
    div_le_div_of_nonneg_right hcoef (by positivity)
  refine ⟨?_, hrUpper, ?_⟩
  · have hdpos : 0 < d := by omega
    have hq0pos : 0 < q0 := by omega
    have hq1pos : 0 < q1 := by omega
    exact Nat.one_le_iff_ne_zero.mpr (by
      exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos hdpos hq0pos) hq1pos))
  · exact hdistPhase.trans hdistUpper

/-- Convert the top-coefficient distance bound into the rational correction
used before the variation estimate, with the source's denominator `r N^d`. -/
private theorem scalarWeyl_topCoefficient_nearestRationalApproximation
    {r N d : ℕ} {R αd : ℝ}
    (hr : 1 ≤ r) (hN : 1 ≤ N)
    (hdist : realDistanceToIntegers ((r : ℝ) * αd) ≤
      R / ((N : ℝ) ^ d)) :
    ∃ a : ℤ,
      |αd - (a : ℝ) / (r : ℝ)| ≤
        R / ((r : ℝ) * (N : ℝ) ^ d) := by
  have hrNat : 0 < r := by omega
  have hNNat : 0 < N := by omega
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hrNat
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNNat
  have hNpowpos : 0 < (N : ℝ) ^ d := pow_pos hNpos _
  obtain ⟨a, ha⟩ :=
    exists_int_abs_sub_le_of_realDistanceToIntegers_le hdist
  have harg :
      αd - (a : ℝ) / (r : ℝ) =
        ((r : ℝ) * αd - (a : ℝ)) / (r : ℝ) := by
    field_simp [ne_of_gt hrpos] <;> ring
  have habs :
      |αd - (a : ℝ) / (r : ℝ)| =
        |(r : ℝ) * αd - (a : ℝ)| / (r : ℝ) := by
    calc
      |αd - (a : ℝ) / (r : ℝ)| =
          |((r : ℝ) * αd - (a : ℝ)) / (r : ℝ)| := by rw [harg]
      _ = |(r : ℝ) * αd - (a : ℝ)| / |(r : ℝ)| := abs_div _ _
      _ = |(r : ℝ) * αd - (a : ℝ)| / (r : ℝ) := by
        rw [abs_of_pos hrpos]
  have hquot :
      (R / ((N : ℝ) ^ d)) / (r : ℝ) =
        R / ((r : ℝ) * (N : ℝ) ^ d) := by
    field_simp [ne_of_gt hrpos, ne_of_gt hNpowpos] <;> ring
  refine ⟨a, ?_⟩
  calc
    |αd - (a : ℝ) / (r : ℝ)| =
        |(r : ℝ) * αd - (a : ℝ)| / (r : ℝ) := habs
    _ ≤ (R / ((N : ℝ) ^ d)) / (r : ℝ) :=
      div_le_div_of_nonneg_right ha hrpos.le
    _ = R / ((r : ℝ) * (N : ℝ) ^ d) := hquot

/-- A large weighted sum forces a large initial partial sum of its first
factor when the second factor has small endpoint norm plus discrete
variation.  The Abel identity is Mathlib's `Finset.sum_range_by_parts'`;
the finite supremum is attained because `L > 0`. -/
private theorem scalarWeyl_initialPrefix_of_weightedSum
    {L : ℕ} {A W : ℝ} (hA : 0 < A) (hW : 0 < W)
    (u v : ℕ → ℂ)
    (hlarge : A ≤ ‖∑ j ∈ Finset.range L, u j * v j‖)
    (hvariation : ‖v (L - 1)‖ +
      ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖ ≤ W) :
    ∃ k : ℕ, k < L ∧
      A / W ≤ ‖∑ j ∈ Finset.range (k + 1), u j‖ := by
  by_cases hLzero : L = 0
  · subst L
    simp at hlarge
    linarith
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hLzero
    have hLone : 1 ≤ L := hLpos
    have hrange : (Finset.range L).Nonempty :=
      ⟨0, Finset.mem_range.mpr hLpos⟩
    let M : ℝ := (Finset.range L).sup' hrange
      (fun k => ‖∑ j ∈ Finset.range (k + 1), u j‖)
    have hprefix_le (k : ℕ) (hk : k < L) :
        ‖∑ j ∈ Finset.range (k + 1), u j‖ ≤ M := by
      dsimp [M]
      exact Finset.le_sup' (s := Finset.range L)
        (f := fun k => ‖∑ j ∈ Finset.range (k + 1), u j‖)
        (Finset.mem_range.mpr hk)
    obtain ⟨k, hk, hMk⟩ := Finset.exists_mem_eq_sup' hrange
      (fun k => ‖∑ j ∈ Finset.range (k + 1), u j‖)
    have hklt : k < L := Finset.mem_range.mp hk
    have hMnonneg : 0 ≤ M := by
      exact le_trans (norm_nonneg _) (hprefix_le 0 hLpos)
    have hfull : ‖∑ j ∈ Finset.range L, u j‖ ≤ M := by
      have hlen : (L - 1) + 1 = L := Nat.sub_add_cancel hLone
      simpa only [hlen] using hprefix_le (L - 1)
        (Nat.sub_lt hLpos (by norm_num))
    have habel := Finset.sum_range_by_parts' (f := u) (g := v) (n := L)
    have habel' :
        (∑ j ∈ Finset.range L, u j * v j) =
          (∑ j ∈ Finset.range L, u j) * v (L - 1) -
            ∑ i ∈ Finset.range (L - 1),
              (∑ j ∈ Finset.range (i + 1), u j) *
                (v (i + 1) - v i) := by
      simpa only [smul_eq_mul] using habel
    have hterm : ∀ i ∈ Finset.range (L - 1),
        ‖(∑ j ∈ Finset.range (i + 1), u j) *
            (v (i + 1) - v i)‖ ≤ M * ‖v (i + 1) - v i‖ := by
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hprefix_le i (by have := Finset.mem_range.mp hi; omega))
        (norm_nonneg _)
    have hsum :
        ‖∑ i ∈ Finset.range (L - 1),
            (∑ j ∈ Finset.range (i + 1), u j) *
              (v (i + 1) - v i)‖ ≤
          M * ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖ := by
      calc
        _ ≤ ∑ i ∈ Finset.range (L - 1),
            ‖(∑ j ∈ Finset.range (i + 1), u j) *
              (v (i + 1) - v i)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (L - 1),
            M * ‖v (i + 1) - v i‖ :=
          Finset.sum_le_sum fun i hi => hterm i hi
        _ = M * ∑ i ∈ Finset.range (L - 1),
            ‖v (i + 1) - v i‖ := by rw [← Finset.mul_sum]
    have hweighted :
        ‖∑ j ∈ Finset.range L, u j * v j‖ ≤
          M * (‖v (L - 1)‖ +
            ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖) := by
      rw [habel']
      calc
        _ ≤ ‖(∑ j ∈ Finset.range L, u j) * v (L - 1)‖ +
            ‖∑ i ∈ Finset.range (L - 1),
              (∑ j ∈ Finset.range (i + 1), u j) *
                (v (i + 1) - v i)‖ := norm_sub_le _ _
        _ ≤ M * ‖v (L - 1)‖ +
            M * ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖ := by
          apply add_le_add
          · rw [norm_mul]
            exact mul_le_mul_of_nonneg_right hfull (norm_nonneg _)
          · exact hsum
        _ = _ := by ring
    have hlarge' : A ≤ M * W := by
      calc
        A ≤ ‖∑ j ∈ Finset.range L, u j * v j‖ := hlarge
        _ ≤ M * (‖v (L - 1)‖ +
            ∑ i ∈ Finset.range (L - 1), ‖v (i + 1) - v i‖) := hweighted
        _ ≤ M * W :=
          mul_le_mul_of_nonneg_left hvariation hMnonneg
    have hAM : A / W ≤ M := (div_le_iff₀ hW).2 hlarge'
    refine ⟨k, hklt, ?_⟩
    calc
      A / W ≤ M := hAM
      _ = ‖∑ j ∈ Finset.range (k + 1), u j‖ := by
        dsimp [M] at hMk ⊢
        exact hMk

/-- The real monomial unit-frequency phase is continuously differentiable.
This explicit composition avoids relying on `fun_prop` to discover the
real-to-complex inclusion. -/
private theorem scalarWeyl_monomialPhase_contDiff (θ : ℝ) (d : ℕ) :
    ContDiff ℝ 1 (fun t : ℝ => unitFrequencyPhase (θ * t ^ d)) := by
  have hreal : ContDiff ℝ 1
      (fun t : ℝ => 2 * Real.pi * (θ * t ^ d)) := by
    fun_prop
  have hcast : ContDiff ℝ 1
      (fun t : ℝ => ((2 * Real.pi * (θ * t ^ d) : ℝ) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hreal
  have himul : ContDiff ℝ 1
      (fun t : ℝ => ((2 * Real.pi * (θ * t ^ d) : ℝ) : ℂ) * Complex.I) :=
    hcast.mul contDiff_const
  simpa only [unitFrequencyPhase] using himul.cexp

/-- The monomial correction phase has the exact source variation budget
`1 + 2*pi*R` on any finite subset of `{1, ..., N}`.  The second conjunct
records the source's simplification to `1 + 8*R`. -/
theorem scalarWeyl_monomialPhaseVariation
    {N d r : ℕ} {R θ : ℝ}
    (hd : 2 ≤ d) (hN : 1 ≤ N) (hr : 1 ≤ r) (hR : 0 ≤ R)
    (hθ : |θ| ≤ R / ((r : ℝ) * (N : ℝ) ^ d))
    (J : Finset ℤ)
    (hJ : ∀ n ∈ J, (1 : ℤ) ≤ n ∧ n ≤ (N : ℤ)) :
    FractionalPrimes.Literature.Uniformity.finiteOrderedTotalVariation J
        (fun n => unitFrequencyPhase (θ * (n : ℝ) ^ d)) ≤
      1 + 2 * Real.pi * R ∧
    FractionalPrimes.Literature.Uniformity.finiteOrderedTotalVariation J
        (fun n => unitFrequencyPhase (θ * (n : ℝ) ^ d)) ≤
      1 + 8 * R := by
  classical
  let g : ℝ → ℂ := fun t => unitFrequencyPhase (θ * t ^ d)
  let D : ℝ → ℝ := fun t =>
    ‖derivWithin g (Set.Icc 0 (N : ℝ)) t‖
  let C : ℝ → ℝ := fun t =>
    2 * Real.pi * |θ| * (d : ℝ) * t ^ (d - 1)
  have hNpos : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := hNreal.le
  have hNpowpos : 0 < (N : ℝ) ^ d := pow_pos hNreal _
  have hrpos : 0 < (r : ℝ) := by
    exact_mod_cast (show 0 < r by omega)
  have hrge : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hJwithin : ∀ n ∈ (J : Set ℤ),
      (n : ℝ) ∈ Set.Icc 0 (N : ℝ) := by
    intro n hn
    have hnJ := hJ n hn
    refine ⟨?_, ?_⟩
    · have hnnonneg : (0 : ℤ) ≤ n := by omega
      exact_mod_cast hnnonneg
    · exact_mod_cast hnJ.2
  have hg : ContDiffOn ℝ 1 g (Set.Icc 0 (N : ℝ)) := by
    dsimp [g]
    exact (scalarWeyl_monomialPhase_contDiff θ d).contDiffOn
  have hDcont : ContinuousOn D (Set.Icc 0 (N : ℝ)) := by
    dsimp [D]
    exact (hg.continuousOn_derivWithin
      (uniqueDiffOn_Icc hNreal) (by norm_num)).norm
  have hCcont : ContinuousOn C (Set.Icc 0 (N : ℝ)) := by
    dsimp [C]
    fun_prop
  have hDint : IntervalIntegrable D MeasureTheory.volume 0 (N : ℝ) :=
    hDcont.intervalIntegrable_of_Icc hNnonneg
  have hCint : IntervalIntegrable C MeasureTheory.volume 0 (N : ℝ) :=
    hCcont.intervalIntegrable_of_Icc hNnonneg
  have hderiv (t : ℝ) :
      HasDerivAt g
        (g t * ((↑(2 * Real.pi * θ * (d : ℝ) * t ^ (d - 1)) : ℂ) *
          Complex.I)) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ d)
        ((d : ℝ) * t ^ (d - 1)) t := hasDerivAt_pow d t
    have hargReal : HasDerivAt
        (fun x : ℝ => (2 * Real.pi * θ) * x ^ d)
        ((2 * Real.pi * θ) * ((d : ℝ) * t ^ (d - 1))) t :=
      hpow.const_mul (2 * Real.pi * θ)
    have harg := (hargReal.ofReal_comp).const_mul Complex.I
    have hexp := (Complex.hasDerivAt_exp _).comp t harg
    convert hexp using 1
    · funext x
      dsimp [g, unitFrequencyPhase]
      push_cast
      congr 1
      ring
    · dsimp [g, unitFrequencyPhase]
      push_cast
      ring
  have hDle : ∀ t ∈ Set.Ioo 0 (N : ℝ), D t ≤ C t := by
    intro t ht
    have hwithin : derivWithin g (Set.Icc 0 (N : ℝ)) t = deriv g t :=
      derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    have htPowNonneg : 0 ≤ t ^ (d - 1) := pow_nonneg ht.1.le _
    have hTwoPiNonneg : 0 ≤ 2 * Real.pi := by positivity
    have hdNonneg : 0 ≤ (d : ℝ) := by positivity
    have hnormCoeff :
        ‖(↑(2 * Real.pi * θ * (d : ℝ) * t ^ (d - 1)) : ℂ) * Complex.I‖ =
          2 * Real.pi * |θ| * (d : ℝ) * t ^ (d - 1) := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      simp only [abs_mul, abs_of_nonneg hTwoPiNonneg,
        abs_of_nonneg hdNonneg, abs_of_nonneg htPowNonneg]
    change ‖derivWithin g (Set.Icc 0 (N : ℝ)) t‖ ≤ C t
    rw [hwithin, (hderiv t).deriv, norm_mul,
      show ‖g t‖ = 1 by simp [g, norm_unitFrequencyPhase], one_mul,
      hnormCoeff]
  have hDintegral :
      (∫ t in (0 : ℝ)..(N : ℝ), D t) ≤
        2 * Real.pi * |θ| * (N : ℝ) ^ d := by
    have hCintegral :
        (∫ t in (0 : ℝ)..(N : ℝ), C t) =
          2 * Real.pi * |θ| * (N : ℝ) ^ d := by
      have hdpos : 0 < d := by omega
      have hdreal : (d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hdpos)
      have hsub : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
      dsimp [C]
      rw [intervalIntegral.integral_const_mul, integral_pow,
        hsub]
      simp [hdpos]
      field_simp [hdreal]
      simp [zero_pow (Nat.ne_of_gt hdpos)]
    calc
      ∫ t in (0 : ℝ)..(N : ℝ), D t ≤
          ∫ t in (0 : ℝ)..(N : ℝ), C t :=
        intervalIntegral.integral_mono_on_of_le_Ioo hNnonneg hDint hCint hDle
      _ = 2 * Real.pi * |θ| * (N : ℝ) ^ d := hCintegral
  have hθscaled : |θ| * (N : ℝ) ^ d ≤ R / (r : ℝ) := by
    apply (le_div_iff₀ hrpos).2
    have hθ' := (le_div_iff₀ (mul_pos hrpos hNpowpos)).1 hθ
    convert hθ' using 1 <;> ring
  have hRdiv : R / (r : ℝ) ≤ R := by
    apply (div_le_iff₀ hrpos).2
    calc
      R = R * 1 := by ring
      _ ≤ R * (r : ℝ) := mul_le_mul_of_nonneg_left hrge hR
  have hθintegral :
      2 * Real.pi * |θ| * (N : ℝ) ^ d ≤ 2 * Real.pi * R := by
    calc
      2 * Real.pi * |θ| * (N : ℝ) ^ d =
          (2 * Real.pi) * (|θ| * (N : ℝ) ^ d) := by ring
      _ ≤ (2 * Real.pi) * (R / (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hθscaled (by positivity)
      _ ≤ (2 * Real.pi) * R :=
        mul_le_mul_of_nonneg_left hRdiv (by positivity)
      _ = 2 * Real.pi * R := by ring
  have hsup :
      FractionalPrimes.Literature.Uniformity.intervalNormSup
        0 (N : ℝ) g = 1 := by
    have hrange :
        Set.range (fun t : Set.Icc 0 (N : ℝ) => ‖g (t : ℝ)‖) = {1} := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        simp [g, norm_unitFrequencyPhase]
      · intro hy
        have hy' : y = 1 := by simpa using hy
        subst y
        refine ⟨⟨0, ⟨le_rfl, hNnonneg⟩⟩, ?_⟩
        simp [g, norm_unitFrequencyPhase]
    rw [FractionalPrimes.Literature.Uniformity.intervalNormSup, hrange]
    simp
  have hrealBound :
      FractionalPrimes.Literature.Uniformity.intervalNormSup
          0 (N : ℝ) g + ∫ t in (0 : ℝ)..(N : ℝ), D t ≤
        1 + 2 * Real.pi * R := by
    rw [hsup]
    calc
      1 + ∫ t in (0 : ℝ)..(N : ℝ), D t ≤
          1 + 2 * Real.pi * |θ| * (N : ℝ) ^ d :=
        by simpa [add_comm] using add_le_add_left hDintegral 1
      _ ≤ 1 + 2 * Real.pi * R := by
        simpa [add_comm] using add_le_add_left hθintegral 1
  have hfiniteENN :
      ENNReal.ofReal
          (FractionalPrimes.Literature.Uniformity.finiteOrderedTotalVariation J
            (fun n => g (n : ℝ))) ≤
        FractionalPrimes.Literature.Uniformity.orderedTotalVariation
          (J : Set ℤ) (fun n => g n) := by
    unfold FractionalPrimes.Literature.Uniformity.orderedTotalVariation
    exact le_iSup_of_le ⟨J, fun _ hn => hn⟩ le_rfl
  have htv :=
    FractionalPrimes.Literature.Uniformity.orderedTotalVariation_le_sup_add_integral
      hNnonneg g hg (J : Set ℤ) hJwithin
  have hENN :
      ENNReal.ofReal
          (FractionalPrimes.Literature.Uniformity.finiteOrderedTotalVariation J
            (fun n => g (n : ℝ))) ≤
        ENNReal.ofReal (1 + 2 * Real.pi * R) :=
    hfiniteENN.trans (htv.trans (ENNReal.ofReal_le_ofReal hrealBound))
  have hvariation :
      FractionalPrimes.Literature.Uniformity.finiteOrderedTotalVariation J
          (fun n => g (n : ℝ)) ≤ 1 + 2 * Real.pi * R :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN
  have hpi : 2 * Real.pi ≤ 8 := by
    calc
      2 * Real.pi ≤ 2 * 4 := mul_le_mul_of_nonneg_left Real.pi_le_four (by norm_num)
      _ = 8 := by norm_num
  have hconstant : 1 + 2 * Real.pi * R ≤ 1 + 8 * R := by
    calc
      1 + 2 * Real.pi * R = 1 + (2 * Real.pi) * R := by ring
      _ ≤ 1 + 8 * R := by
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hpi hR) 1
  exact ⟨hvariation, hvariation.trans hconstant⟩

/-- The rational top-coefficient phase is constant on each residue class:
congruence of the integer inputs passes through the natural power and the
integer numerator, while division by the modulus changes the phase by an
integer. -/
private theorem scalarWeyl_rationalTopPhase_eq_of_modEq
    {r d : ℕ} {a n b : ℤ} (hr : 0 < r)
    (hmod : n ≡ b [ZMOD (r : ℤ)]) :
    unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d) =
      unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (b : ℝ) ^ d) := by
  have hrRpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hpow : n ^ d ≡ b ^ d [ZMOD (r : ℤ)] := Int.ModEq.pow d hmod
  have hmul : a * n ^ d ≡ a * b ^ d [ZMOD (r : ℤ)] := hpow.mul_left a
  obtain ⟨k, hk⟩ := hmul.dvd
  have hreal :
      (a : ℝ) * (b : ℝ) ^ d - (a : ℝ) * (n : ℝ) ^ d =
        (r : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  have harg :
      ((a : ℝ) / (r : ℝ)) * (b : ℝ) ^ d =
        ((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d + (k : ℝ) := by
    field_simp [ne_of_gt hrRpos]
    nlinarith [hreal]
  calc
    unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d) =
        unitFrequencyPhase
          ((((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d) + (k : ℝ)) := by
            rw [unitFrequencyPhase_add, unitFrequencyPhase_int]
            simp
    _ = unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (b : ℝ) ^ d) := by
          rw [harg]

/-- Split a large sum with a rational top coefficient into one residue class.
The top phase is constant on each class, so the selected low-degree sum
retains the source bound `δ N / (r V)`. -/
private theorem scalarWeyl_selectResidueClass
    {N r d : ℕ} {δ V : ℝ} (J : Finset ℤ) (a : ℤ) (f : ℤ → ℂ)
    (hr : 1 ≤ r) (hV : 0 < V)
    (hlarge : δ * (N : ℝ) / V ≤
      ‖∑ n ∈ J,
        f n * unitFrequencyPhase
          (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d)‖) :
    ∃ b ∈ Finset.Icc (1 : ℤ) (r : ℤ),
      δ * (N : ℝ) / ((r : ℝ) * V) ≤
        ‖∑ n ∈ J.filter (fun n => n ≡ b [ZMOD (r : ℤ)]), f n‖ := by
  classical
  have hrpos : 0 < r := by omega
  have hrZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hrpos
  let fibers : ℕ → Finset ℤ := fun x =>
    J.filter (fun n => n ≡ (x : ℤ) [ZMOD (r : ℤ)])
  let F : ℤ → ℂ := fun n =>
    f n * unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d)
  let mass : ℕ → ℝ := fun x => ‖∑ n ∈ fibers x, f n‖
  have huniq (x y : ℕ) (hx : x < r) (hy : y < r)
      (hxy : (x : ℤ) ≡ (y : ℤ) [ZMOD (r : ℤ)]) : x = y := by
    have hxZ : (x : ℤ) < (r : ℤ) := by exact_mod_cast hx
    have hyZ : (y : ℤ) < (r : ℤ) := by exact_mod_cast hy
    have hrem : (x : ℤ) % (r : ℤ) = (y : ℤ) % (r : ℤ) := by
      change (x : ℤ) % (r : ℤ) = (y : ℤ) % (r : ℤ) at hxy
      exact hxy
    have hxrem : (x : ℤ) % (r : ℤ) = (x : ℤ) :=
      Int.emod_eq_of_lt (Nat.cast_nonneg _) hxZ
    have hyrem : (y : ℤ) % (r : ℤ) = (y : ℤ) :=
      Int.emod_eq_of_lt (Nat.cast_nonneg _) hyZ
    rw [hxrem, hyrem] at hrem
    exact_mod_cast hrem
  have hcover : (Finset.range r).biUnion fibers = J := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_biUnion.mp hn with ⟨x, hx, hxn⟩
      exact (Finset.mem_filter.mp hxn).1
    · intro hn
      let x : ℕ := (n % (r : ℤ)).toNat
      have hrem0 : 0 ≤ n % (r : ℤ) := Int.emod_nonneg _ hrZ.ne'
      have hremLt : n % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos _ hrZ
      have hcast : (x : ℤ) = n % (r : ℤ) := Int.toNat_of_nonneg hrem0
      have hxLtZ : (x : ℤ) < (r : ℤ) := by rw [hcast]; exact hremLt
      have hxLt : x < r := by exact_mod_cast hxLtZ
      have hmod : n ≡ (x : ℤ) [ZMOD (r : ℤ)] := by
        change n % (r : ℤ) = (x : ℤ) % (r : ℤ)
        rw [hcast]
        simp
      exact Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_range.mpr hxLt,
          Finset.mem_filter.mpr ⟨hn, hmod⟩⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range r)) fibers := by
    intro x hx y hy hxy
    have hx' : x ∈ Finset.range r := by simpa using hx
    have hy' : y ∈ Finset.range r := by simpa using hy
    apply Finset.disjoint_left.mpr
    intro n hnx hny
    have hnxMod := (Finset.mem_filter.mp hnx).2
    have hnyMod := (Finset.mem_filter.mp hny).2
    apply hxy
    exact huniq x y (Finset.mem_range.mp hx') (Finset.mem_range.mp hy')
      (hnxMod.symm.trans hnyMod)
  have hpartition :
      (∑ n ∈ J, F n) =
        ∑ x ∈ Finset.range r, ∑ n ∈ fibers x, F n := by
    calc
      (∑ n ∈ J, F n) =
          ∑ n ∈ (Finset.range r).biUnion fibers, F n := by rw [hcover]
      _ = ∑ x ∈ Finset.range r, ∑ n ∈ fibers x, F n :=
        Finset.sum_biUnion hdisj
  have hclass (x : ℕ) :
      ‖∑ n ∈ fibers x, F n‖ = mass x := by
    have hsum :
        (∑ n ∈ fibers x, F n) =
          (∑ n ∈ fibers x, f n) *
            unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (x : ℝ) ^ d) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      change f n *
          unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d) =
        f n * unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (x : ℝ) ^ d)
      have hphase := scalarWeyl_rationalTopPhase_eq_of_modEq
        (a := a) (d := d) hrpos ((Finset.mem_filter.mp hn).2)
      simpa only [Int.cast_natCast] using
        congrArg (fun z : ℂ => f n * z) hphase
    rw [hsum, norm_mul, norm_unitFrequencyPhase, mul_one]
  have hlargeF : δ * (N : ℝ) / V ≤ ‖∑ n ∈ J, F n‖ := by
    simpa [F] using hlarge
  have hmass :
      δ * (N : ℝ) / V ≤ ∑ x ∈ Finset.range r, mass x := by
    calc
      δ * (N : ℝ) / V ≤ ‖∑ n ∈ J, F n‖ := hlargeF
      _ = ‖∑ x ∈ Finset.range r, ∑ n ∈ fibers x, F n‖ := by
        rw [hpartition]
      _ ≤ ∑ x ∈ Finset.range r,
          ‖∑ n ∈ fibers x, F n‖ := norm_sum_le _ _
      _ = ∑ x ∈ Finset.range r, mass x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hclass x
  have hrange : (Finset.range r).Nonempty :=
    ⟨0, Finset.mem_range.mpr hrpos⟩
  let M : ℝ := (Finset.range r).sup' hrange mass
  have hmass_le (x : ℕ) (hx : x ∈ Finset.range r) : mass x ≤ M := by
    dsimp [M]
    exact Finset.le_sup' (s := Finset.range r) (f := mass) hx
  have hsumM :
      (∑ x ∈ Finset.range r, mass x) ≤ (r : ℝ) * M := by
    calc
      (∑ x ∈ Finset.range r, mass x) ≤
          ∑ x ∈ Finset.range r, M :=
        Finset.sum_le_sum fun x hx => hmass_le x hx
      _ = (r : ℝ) * M := by simp [Finset.card_range]
  have hlargeM : δ * (N : ℝ) / V ≤ (r : ℝ) * M := hmass.trans hsumM
  have hprod : δ * (N : ℝ) ≤ ((r : ℝ) * M) * V :=
    (div_le_iff₀ hV).mp hlargeM
  have hmax : δ * (N : ℝ) / ((r : ℝ) * V) ≤ M := by
    apply (div_le_iff₀ (mul_pos (by exact_mod_cast hrpos) hV)).2
    calc
      δ * (N : ℝ) ≤ ((r : ℝ) * M) * V := hprod
      _ = M * ((r : ℝ) * V) := by ring
  obtain ⟨x, hx, hMx⟩ := Finset.exists_mem_eq_sup' hrange mass
  have hxLt : x < r := Finset.mem_range.mp hx
  let b : ℤ := if x = 0 then (r : ℤ) else (x : ℤ)
  have hb : b ∈ Finset.Icc (1 : ℤ) (r : ℤ) := by
    rw [Finset.mem_Icc]
    by_cases hx0 : x = 0
    · have hbval : b = (r : ℤ) := by simp [b, hx0]
      rw [hbval]
      exact ⟨by exact_mod_cast hr, le_rfl⟩
    · have hxlo : 1 ≤ x := by omega
      have hxhi : x ≤ r := Nat.le_of_lt hxLt
      have hbval : b = (x : ℤ) := by simp [b, hx0]
      rw [hbval]
      exact ⟨by exact_mod_cast hxlo, by exact_mod_cast hxhi⟩
  have hxb : (x : ℤ) ≡ b [ZMOD (r : ℤ)] := by
    by_cases hx0 : x = 0
    · have hbval : b = (r : ℤ) := by simp [b, hx0]
      rw [hbval]
      subst x
      change (0 : ℤ) % (r : ℤ) = (r : ℤ) % (r : ℤ)
      simp
    · have hbval : b = (x : ℤ) := by simp [b, hx0]
      rw [hbval]
  have hfilters : fibers x =
      J.filter (fun n => n ≡ b [ZMOD (r : ℤ)]) := by
    ext n
    simp only [fibers, Finset.mem_filter]
    constructor
    · rintro ⟨hn, hmod⟩
      exact ⟨hn, hmod.trans hxb⟩
    · rintro ⟨hn, hmod⟩
      exact ⟨hn, hmod.trans hxb.symm⟩
  have hchosen : δ * (N : ℝ) / ((r : ℝ) * V) ≤ mass x := by
    rw [← hMx]
    exact hmax
  refine ⟨b, hb, ?_⟩
  simpa [mass, hfilters] using hchosen

end FractionalPrimes.Literature.Polynomial
