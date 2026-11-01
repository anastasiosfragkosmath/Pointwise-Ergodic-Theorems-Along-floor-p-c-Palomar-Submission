module

public import FractionalPrimes.Literature.Multiplier.DyadicIntervals
public import FractionalPrimes.FiniteSupportLpNorm
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The integer Calderón–Zygmund decomposition (`lp:cz`)

The proof uses the finite dyadic intervals from `lp:dyadic-intervals` and
the counting-measure norms on finitely supported sequences.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The exact counting-measure `ℓ¹` norm, written as a tsum over the lattice. -/
def discreteL1Norm (f : ℤ → ℂ) : ℝ := ∑' x : ℤ, ‖f x‖

/-- The square of the exact counting-measure `ℓ²` norm. -/
def discreteL2NormSq (f : ℤ → ℂ) : ℝ := ∑' x : ℤ, ‖f x‖ ^ 2

/-- The `ℓ∞` norm, as the supremum of the pointwise norms. -/
def discreteLInfNorm (f : ℤ → ℂ) : ℝ := sSup (Set.range fun x : ℤ => ‖f x‖)

/-- The absolute-value mass of a dyadic interval. -/
def dyadicIntervalMass (f : ℤ → ℂ) (i : ℕ × ℤ) : ℝ :=
  ∑ x ∈ dyadicIntervals i.1 i.2, ‖f x‖

/-- The average of a complex sequence on a nonempty dyadic interval. -/
def dyadicIntervalAverage (f : ℤ → ℂ) (i : ℕ × ℤ) : ℂ :=
  (∑ x ∈ dyadicIntervals i.1 i.2, f x) / (dyadicIntervals i.1 i.2).card

/-- The mean-zero bad piece on a dyadic interval. -/
def dyadicBadPiece (f : ℤ → ℂ) (i : ℕ × ℤ) (x : ℤ) : ℂ :=
  if x ∈ dyadicIntervals i.1 i.2 then
    f x - dyadicIntervalAverage f i else 0

/-- The union of a finite family of dyadic intervals. -/
noncomputable def dyadicCZIntervalUnion (S : Finset (ℕ × ℤ)) : Finset ℤ :=
  S.biUnion (fun i => dyadicIntervals i.1 i.2)

/-- The good part obtained by subtracting all selected bad pieces. -/
noncomputable def dyadicCZGoodPart (f : ℤ → ℂ) (S : Finset (ℕ × ℤ)) (x : ℤ) : ℂ :=
  f x - ∑ i ∈ S, dyadicBadPiece f i x

/-- Data witnessing the exact integer Calderón--Zygmund decomposition. -/
structure DiscreteCZDecompositionData (f : ℤ → ℂ) (α : ℝ) where
  intervals : Finset (ℕ × ℤ)
  goodPart : ℤ → ℂ
  pairwiseDisjoint : ∀ i ∈ intervals, ∀ j ∈ intervals, i ≠ j →
    Disjoint (dyadicIntervals i.1 i.2) (dyadicIntervals j.1 j.2)
  decomposition : ∀ x : ℤ,
    f x = goodPart x + ∑ i ∈ intervals, dyadicBadPiece f i x
  interval_measure_bound :
    (∑ i ∈ intervals, ((dyadicIntervals i.1 i.2).card : ℝ)) ≤
      discreteL1Norm f / α
  good_lInf_bound : discreteLInfNorm goodPart ≤ 2 * α
  good_l1_bound : discreteL1Norm goodPart ≤ discreteL1Norm f
  good_l2_sq_bound : discreteL2NormSq goodPart ≤ 2 * α * discreteL1Norm f
  bad_support : ∀ i ∈ intervals,
    Function.support (dyadicBadPiece f i) ⊆ (dyadicIntervals i.1 i.2 : Set ℤ)
  bad_mean_zero : ∀ i ∈ intervals,
    ∑ x ∈ dyadicIntervals i.1 i.2, dyadicBadPiece f i x = 0
  bad_l1_bound :
    (∑ i ∈ intervals, discreteL1Norm (dyadicBadPiece f i)) ≤
      2 * discreteL1Norm f
  good_finite_support : goodPart.HasFiniteSupport
  bad_finite_support : ∀ i ∈ intervals, (dyadicBadPiece f i).HasFiniteSupport

theorem dyadicCZGoodPart_eq_intervalAverage (f : ℤ → ℂ)
    (S : Finset (ℕ × ℤ)) (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (dyadicIntervals i.1 i.2) (dyadicIntervals j.1 j.2))
    (i : ℕ × ℤ) (hi : i ∈ S) {x : ℤ} (hx : x ∈ dyadicIntervals i.1 i.2) :
    dyadicCZGoodPart f S x = dyadicIntervalAverage f i := by
  have hsum : (∑ j ∈ S, dyadicBadPiece f j x) = dyadicBadPiece f i x := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j hj hji
    have hIj := hdisj i hi j hj hji.symm
    have hxj : x ∉ dyadicIntervals j.1 j.2 := by
      intro hxj
      exact (Finset.disjoint_left.mp hIj) hx hxj
    simp [dyadicBadPiece, hxj]
  rw [dyadicCZGoodPart, hsum]
  simp [dyadicBadPiece, hx]

theorem dyadicCZGoodPart_eq_f_of_not_mem_union (f : ℤ → ℂ)
    (S : Finset (ℕ × ℤ)) {x : ℤ} (hx : x ∉ dyadicCZIntervalUnion S) :
    dyadicCZGoodPart f S x = f x := by
  have hsum : (∑ i ∈ S, dyadicBadPiece f i x) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hxI : x ∉ dyadicIntervals i.1 i.2 := by
      intro hxI
      exact hx (Finset.mem_biUnion.mpr ⟨i, hi, hxI⟩)
    simp [dyadicBadPiece, hxI]
  simp [dyadicCZGoodPart, hsum]

theorem dyadicBadPiece_hasFiniteSupport (f : ℤ → ℂ) (i : ℕ × ℤ) :
    (dyadicBadPiece f i).HasFiniteSupport := by
  apply (Finset.finite_toSet (dyadicIntervals i.1 i.2)).subset
  intro x hx
  change dyadicBadPiece f i x ≠ 0 at hx
  by_contra hxI
  have hxI' : x ∉ dyadicIntervals i.1 i.2 := by simpa using hxI
  simp [dyadicBadPiece, hxI'] at hx

theorem dyadicCZGoodPart_hasFiniteSupport (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (S : Finset (ℕ × ℤ)) : (dyadicCZGoodPart f S).HasFiniteSupport := by
  classical
  have hfinite :
      (Function.support f ∪ (dyadicCZIntervalUnion S : Set ℤ)).Finite :=
    hf.union (Finset.finite_toSet (dyadicCZIntervalUnion S))
  apply hfinite.subset
  intro x hx
  change dyadicCZGoodPart f S x ≠ 0 at hx
  by_contra hmem
  have hxnotF : x ∉ Function.support f := by
    intro hxF
    exact hmem (Set.mem_union_left _ hxF)
  have hxnotU : x ∉ (dyadicCZIntervalUnion S : Set ℤ) := by
    intro hxU
    exact hmem (Set.mem_union_right _ hxU)
  have hfxzero : f x = 0 := by
    by_contra hfx
    exact hxnotF (Function.mem_support.mpr hfx)
  have hsumzero : (∑ i ∈ S, dyadicBadPiece f i x) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hxI : x ∉ dyadicIntervals i.1 i.2 := by
      intro hxI
      exact hxnotU (Finset.mem_biUnion.mpr ⟨i, hi, hxI⟩)
    simp [dyadicBadPiece, hxI]
  simp [dyadicCZGoodPart, hfxzero, hsumzero] at hx

/-- The scale-`k` dyadic interval containing `x`. -/
def dyadicIntervalIndex (k : ℕ) (x : ℤ) : ℤ := x / (2 : ℤ) ^ k

/-- An interval is bad when the average of `‖f‖` strictly exceeds `α`. -/
def dyadicBadInterval (f : ℤ → ℂ) (α : ℝ) (i : ℕ × ℤ) : Prop :=
  α * (dyadicIntervals i.1 i.2).card < dyadicIntervalMass f i

/-- Candidate dyadic intervals meeting the finite support, with scales below `K`. -/
noncomputable def dyadicCZCandidateIndices (f : ℤ → ℂ)
    (hf : f.HasFiniteSupport) (K : ℕ) : Finset (ℕ × ℤ) :=
  ((Finset.range K).product hf.toFinset).image
    (fun p : ℕ × ℤ => (p.1, dyadicIntervalIndex p.1 p.2))

/-- The bad members of a finite candidate family. -/
noncomputable def dyadicCZBadCandidateIndices (f : ℤ → ℂ) (α : ℝ)
    (C : Finset (ℕ × ℤ)) : Finset (ℕ × ℤ) := by
  classical
  exact C.filter (dyadicBadInterval f α)

/-- The inclusion-maximal bad indices in a finite candidate family. -/
noncomputable def dyadicCZMaximalBadIndices (B : Finset (ℕ × ℤ)) :
    Finset (ℕ × ℤ) := by
  classical
  exact B.filter fun i =>
    ∀ j ∈ B, dyadicIntervals i.1 i.2 ⊆ dyadicIntervals j.1 j.2 →
      dyadicIntervals j.1 j.2 ⊆ dyadicIntervals i.1 i.2

theorem dyadicIntervalIndex_mem (k : ℕ) (x : ℤ) :
    x ∈ dyadicIntervals k (dyadicIntervalIndex k x) := by
  let t : ℤ := (2 : ℤ) ^ k
  have htpos : 0 < t := by dsimp [t]; positivity
  let r : ℤ := x % t
  have hr0 : 0 ≤ r := by dsimp [r]; exact Int.emod_nonneg x (ne_of_gt htpos)
  have hrlt : r < t := by dsimp [r]; exact Int.emod_lt_of_pos x htpos
  have hdecomp : x = r + t * (x / t) := by
    dsimp [r]
    exact (Int.emod_add_mul_ediv x t).symm
  rw [mem_dyadicIntervals]
  dsimp [dyadicIntervalIndex, t] at htpos hr0 hrlt hdecomp ⊢
  constructor <;> nlinarith [hdecomp]

theorem dyadicIntervalIndex_eq_of_mem (k : ℕ) (a x : ℤ)
    (hx : x ∈ dyadicIntervals k a) : dyadicIntervalIndex k x = a := by
  let t : ℤ := (2 : ℤ) ^ k
  have htpos : 0 < t := by dsimp [t]; positivity
  let q : ℤ := x / t
  let r : ℤ := x % t
  have hr0 : 0 ≤ r := by dsimp [r]; exact Int.emod_nonneg x (ne_of_gt htpos)
  have hrlt : r < t := by dsimp [r]; exact Int.emod_lt_of_pos x htpos
  have hdecomp : x = r + t * q := by
    dsimp [r, q]
    exact (Int.emod_add_mul_ediv x t).symm
  have hmem : a * t ≤ x ∧ x < (a + 1) * t := by
    simpa [t] using (mem_dyadicIntervals k a x).mp hx
  have hlow : a * t < (q + 1) * t := by
    calc
      a * t ≤ x := hmem.1
      _ = r + t * q := hdecomp
      _ < t * q + t := by nlinarith [hrlt]
      _ = (q + 1) * t := by ring
  have haq : a < q + 1 :=
    (mul_lt_mul_iff_right₀ htpos).mp (by simpa [mul_comm] using hlow)
  have hqt : q * t ≤ x := by
    calc
      q * t = t * q := by ring
      _ ≤ r + t * q := by nlinarith [hr0]
      _ = x := hdecomp.symm
  have hhigh : q * t < (a + 1) * t := lt_of_le_of_lt hqt hmem.2
  have hqa : q < a + 1 :=
    (mul_lt_mul_iff_right₀ htpos).mp (by simpa [mul_comm] using hhigh)
  have haq' : a ≤ q := by omega
  have hqa' : q ≤ a := by omega
  have hqeq : q = a := by omega
  simpa [dyadicIntervalIndex, q, t] using hqeq

theorem exists_dyadicCZ_scale_cutoff (f : ℤ → ℂ) (α : ℝ) (hα : 0 < α) :
    ∃ K : ℕ, discreteL1Norm f < α * (2 : ℝ) ^ K := by
  have hpow : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  obtain ⟨K, hK⟩ :=
    Filter.tendsto_atTop_atTop.mp hpow (discreteL1Norm f / α + 1)
  have hKstrict : discreteL1Norm f / α < (2 : ℝ) ^ K := by
    have := hK K le_rfl
    linarith
  refine ⟨K, ?_⟩
  simpa [mul_comm] using (div_lt_iff₀ hα).mp hKstrict

theorem dyadicIntervals_index_injective {k l : ℕ} {a b : ℤ}
    (heq : dyadicIntervals k a = dyadicIntervals l b) : (k, a) = (l, b) := by
  have hcard := congrArg Finset.card heq
  have hpow : 2 ^ k = 2 ^ l := by
    simpa only [dyadicIntervals_card] using hcard
  have hk : k = l := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  subst l
  have htpos : 0 < (2 : ℤ) ^ k := by positivity
  have hfirst : a * (2 : ℤ) ^ k ∈ dyadicIntervals k a := by
    rw [mem_dyadicIntervals]
    constructor
    · exact le_rfl
    · nlinarith [htpos]
  have hmem : a * (2 : ℤ) ^ k ∈ dyadicIntervals k b := heq ▸ hfirst
  have hmem' : b * (2 : ℤ) ^ k ≤ a * (2 : ℤ) ^ k ∧
      a * (2 : ℤ) ^ k < (b + 1) * (2 : ℤ) ^ k := by
    simpa only [mem_dyadicIntervals] using hmem
  have hba : b ≤ a :=
    (mul_le_mul_iff_right₀ htpos).mp (by simpa [mul_comm] using hmem'.1)
  have hab : a < b + 1 :=
    (mul_lt_mul_iff_right₀ htpos).mp (by simpa [mul_comm] using hmem'.2)
  have hab' : a ≤ b := by omega
  exact Prod.ext rfl (by omega)

theorem discreteL1Norm_eq_sum_support (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    discreteL1Norm f = ∑ x ∈ hf.toFinset, ‖f x‖ := by
  rw [discreteL1Norm]
  apply tsum_eq_sum (s := hf.toFinset)
  intro x hx
  have hxzero : f x = 0 := by
    by_contra hne
    exact hx (hf.mem_toFinset.mpr (Function.mem_support.mpr hne))
  simp [hxzero]

theorem discreteL1Norm_eq_sum_of_support_subset (f : ℤ → ℂ) (s : Finset ℤ)
    (hsub : Function.support f ⊆ (s : Set ℤ)) :
    discreteL1Norm f = ∑ x ∈ s, ‖f x‖ := by
  rw [discreteL1Norm]
  apply tsum_eq_sum (s := s)
  intro x hx
  have hxzero : f x = 0 := by
    by_contra hfx
    exact hx (hsub (Function.mem_support.mpr hfx))
  simp [hxzero]

theorem discreteL2NormSq_eq_sum_support (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    discreteL2NormSq f = ∑ x ∈ hf.toFinset, ‖f x‖ ^ 2 := by
  rw [discreteL2NormSq]
  apply tsum_eq_sum (s := hf.toFinset)
  intro x hx
  have hxzero : f x = 0 := by
    by_contra hne
    exact hx (hf.mem_toFinset.mpr (Function.mem_support.mpr hne))
  simp [hxzero]

theorem dyadicIntervalAverage_norm_le_mass_div_card (f : ℤ → ℂ) (i : ℕ × ℤ) :
    ‖dyadicIntervalAverage f i‖ ≤
      dyadicIntervalMass f i / (dyadicIntervals i.1 i.2).card := by
  have hcard : 0 < (dyadicIntervals i.1 i.2).card := by
    rw [dyadicIntervals_card]
    positivity
  rw [dyadicIntervalAverage, dyadicIntervalMass, norm_div, norm_natCast]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)

theorem dyadicIntervalAverage_card_mul_norm_le_mass (f : ℤ → ℂ) (i : ℕ × ℤ) :
    ((dyadicIntervals i.1 i.2).card : ℝ) * ‖dyadicIntervalAverage f i‖ ≤
      dyadicIntervalMass f i := by
  have hcard : 0 < ((dyadicIntervals i.1 i.2).card : ℝ) := by
    rw [dyadicIntervals_card]
    positivity
  have hbound := dyadicIntervalAverage_norm_le_mass_div_card f i
  have hmul := (le_div_iff₀ hcard).mp hbound
  simpa [mul_comm] using hmul

theorem dyadicIntervalMass_sum_union (f : ℤ → ℂ)
    (S : Finset (ℕ × ℤ))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (dyadicIntervals i.1 i.2) (dyadicIntervals j.1 j.2)) :
    (∑ i ∈ S, dyadicIntervalMass f i) =
      ∑ x ∈ dyadicCZIntervalUnion S, ‖f x‖ := by
  unfold dyadicIntervalMass dyadicCZIntervalUnion
  have hPairwise : Set.PairwiseDisjoint (↑S : Set (ℕ × ℤ))
      (fun i => dyadicIntervals i.1 i.2) := by
    intro i hi j hj hne
    exact hdisj i hi j hj hne
  rw [Finset.sum_biUnion hPairwise]

theorem dyadicCZIntervalUnion_sum_le_discreteL1Norm (f : ℤ → ℂ)
    (hf : f.HasFiniteSupport) (S : Finset (ℕ × ℤ)) :
    (∑ x ∈ dyadicCZIntervalUnion S, ‖f x‖) ≤ discreteL1Norm f := by
  have hnormFinite : (fun x : ℤ => ‖f x‖).HasFiniteSupport := by
    apply hf.subset
    intro x hx
    change ‖f x‖ ≠ 0 at hx
    change f x ≠ 0
    intro hfx
    rw [hfx] at hx
    norm_num at hx
  have hs : Summable fun x : ℤ => ‖f x‖ := summable_of_hasFiniteSupport hnormFinite
  unfold discreteL1Norm
  exact Summable.sum_le_tsum (dyadicCZIntervalUnion S)
    (fun _ _ => norm_nonneg _) hs

theorem dyadicIntervalMass_le_discreteL1Norm (f : ℤ → ℂ)
    (hf : f.HasFiniteSupport) (i : ℕ × ℤ) :
    dyadicIntervalMass f i ≤ discreteL1Norm f := by
  have hnormFinite : (fun x : ℤ => ‖f x‖).HasFiniteSupport := by
    apply hf.subset
    intro x hx
    change ‖f x‖ ≠ 0 at hx
    change f x ≠ 0
    intro hfx
    rw [hfx] at hx
    norm_num at hx
  have hs : Summable fun x : ℤ => ‖f x‖ := summable_of_hasFiniteSupport hnormFinite
  unfold dyadicIntervalMass discreteL1Norm
  exact Summable.sum_le_tsum (dyadicIntervals i.1 i.2)
    (fun _ _ => norm_nonneg _) hs

theorem dyadicBadInterval_scale_lt (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (α : ℝ) (hα : 0 < α) (K : ℕ)
    (hK : discreteL1Norm f < α * (2 : ℝ) ^ K) (i : ℕ × ℤ)
    (hbad : dyadicBadInterval f α i) : i.1 < K := by
  by_contra hk
  have hKle : K ≤ i.1 := by omega
  have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ i.1 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hKle
  have hscale : α * (2 : ℝ) ^ K ≤ α * (2 : ℝ) ^ i.1 :=
    mul_le_mul_of_nonneg_left hpow hα.le
  have hbad' : α * (2 : ℝ) ^ i.1 < dyadicIntervalMass f i := by
    simpa [dyadicBadInterval, dyadicIntervals_card] using hbad
  have hmass := dyadicIntervalMass_le_discreteL1Norm f hf i
  linarith

theorem dyadicBadInterval_hasSupportPoint (f : ℤ → ℂ) (α : ℝ) (hα : 0 < α)
    (i : ℕ × ℤ) (hbad : dyadicBadInterval f α i) :
    ∃ x ∈ dyadicIntervals i.1 i.2, f x ≠ 0 := by
  change α * (dyadicIntervals i.1 i.2).card < dyadicIntervalMass f i at hbad
  have hcard : 0 < (dyadicIntervals i.1 i.2).card := by
    rw [dyadicIntervals_card]
    positivity
  have hcardR : 0 < ((dyadicIntervals i.1 i.2).card : ℝ) := by
    exact_mod_cast hcard
  have hmasspos : 0 < dyadicIntervalMass f i := lt_trans (mul_pos hα hcardR) hbad
  by_contra h
  have hzero : ∀ x ∈ dyadicIntervals i.1 i.2, f x = 0 := by
    intro x hx
    by_contra hfx
    exact h ⟨x, hx, hfx⟩
  have hmasszero : dyadicIntervalMass f i = 0 := by
    unfold dyadicIntervalMass
    rw [Finset.sum_eq_zero]
    intro x hx
    simp [hzero x hx]
  rw [hmasszero] at hmasspos
  exact (lt_irrefl 0) hmasspos

theorem dyadicBadInterval_mem_candidateIndices (f : ℤ → ℂ)
    (hf : f.HasFiniteSupport) (α : ℝ) (hα : 0 < α) (K : ℕ)
    (hK : discreteL1Norm f < α * (2 : ℝ) ^ K) (i : ℕ × ℤ)
    (hbad : dyadicBadInterval f α i) :
    i ∈ dyadicCZCandidateIndices f hf K := by
  classical
  have hscale := dyadicBadInterval_scale_lt f hf α hα K hK i hbad
  obtain ⟨x, hxI, hfx⟩ := dyadicBadInterval_hasSupportPoint f α hα i hbad
  have hxS : x ∈ hf.toFinset :=
    hf.mem_toFinset.mpr (Function.mem_support.mpr hfx)
  refine Finset.mem_image.mpr ⟨(i.1, x), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hscale, hxS⟩
  · change (i.1, dyadicIntervalIndex i.1 x) = (i.1, i.2)
    exact congrArg (fun a : ℤ => (i.1, a))
      (dyadicIntervalIndex_eq_of_mem i.1 i.2 x hxI)

theorem exists_maximal_bad_superinterval (B : Finset (ℕ × ℤ))
    (i : ℕ × ℤ) (hi : i ∈ B) :
    ∃ j ∈ B, dyadicIntervals i.1 i.2 ⊆ dyadicIntervals j.1 j.2 ∧
      ∀ k ∈ B, dyadicIntervals j.1 j.2 ⊆ dyadicIntervals k.1 k.2 →
        dyadicIntervals k.1 k.2 ⊆ dyadicIntervals j.1 j.2 := by
  classical
  let C := B.filter fun j => dyadicIntervals i.1 i.2 ⊆ dyadicIntervals j.1 j.2
  have hne : C.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, Finset.Subset.rfl⟩⟩
  obtain ⟨j, hj⟩ := C.exists_maximalFor (fun j => dyadicIntervals j.1 j.2) hne
  have hjC : j ∈ C := hj.1
  have hjB : j ∈ B := (Finset.mem_filter.mp hjC).1
  have hIj : dyadicIntervals i.1 i.2 ⊆ dyadicIntervals j.1 j.2 :=
    (Finset.mem_filter.mp hjC).2
  refine ⟨j, hjB, hIj, ?_⟩
  intro k hkB hjk
  have hkC : k ∈ C := Finset.mem_filter.mpr ⟨hkB, hIj.trans hjk⟩
  exact hj.2 (j := k) hkC hjk

theorem maximal_bad_indices_cover (B : Finset (ℕ × ℤ))
    (i : ℕ × ℤ) (hi : i ∈ B) :
    ∃ j ∈ dyadicCZMaximalBadIndices B,
      dyadicIntervals i.1 i.2 ⊆ dyadicIntervals j.1 j.2 := by
  obtain ⟨j, hjB, hIj, hjmax⟩ := exists_maximal_bad_superinterval B i hi
  exact ⟨j, Finset.mem_filter.mpr ⟨hjB, hjmax⟩, hIj⟩

theorem maximal_bad_indices_disjoint (B : Finset (ℕ × ℤ))
    {i j : ℕ × ℤ} (hi : i ∈ dyadicCZMaximalBadIndices B)
    (hj : j ∈ dyadicCZMaximalBadIndices B) (hne : i ≠ j) :
    Disjoint (dyadicIntervals i.1 i.2) (dyadicIntervals j.1 j.2) := by
  have hiB := (Finset.mem_filter.mp hi).1
  have hjB := (Finset.mem_filter.mp hj).1
  have hiMax := (Finset.mem_filter.mp hi).2
  have hjMax := (Finset.mem_filter.mp hj).2
  rcases dyadicIntervals_disjoint_or_nested i.1 i.2 j.1 j.2 with hdisj | hsub | hsub
  · exact hdisj
  · have hji := hiMax j hjB hsub
    have hEq := Finset.Subset.antisymm hsub hji
    exact False.elim (hne (dyadicIntervals_index_injective hEq))
  · have hij := hjMax i hiB hsub
    have hEq := Finset.Subset.antisymm hsub hij
    exact False.elim (hne.symm (dyadicIntervals_index_injective hEq))

/-- The maximal bad intervals among the finite support-meeting candidates. -/
noncomputable def dyadicCZSelectedBadIndices (f : ℤ → ℂ)
    (hf : f.HasFiniteSupport) (α : ℝ) (K : ℕ) : Finset (ℕ × ℤ) :=
  dyadicCZMaximalBadIndices
    (dyadicCZBadCandidateIndices f α (dyadicCZCandidateIndices f hf K))

theorem dyadicCZSelected_parent_not_bad (f : ℤ → ℂ)
    (hf : f.HasFiniteSupport) (α : ℝ) (hα : 0 < α) (K : ℕ)
    (hK : discreteL1Norm f < α * (2 : ℝ) ^ K)
    (i : ℕ × ℤ) (hi : i ∈ dyadicCZSelectedBadIndices f hf α K) :
    ¬ dyadicBadInterval f α (i.1 + 1, dyadicParentIndex i.2) := by
  classical
  let B := dyadicCZBadCandidateIndices f α (dyadicCZCandidateIndices f hf K)
  have hiB : i ∈ B := (Finset.mem_filter.mp hi).1
  have hiMax := (Finset.mem_filter.mp hi).2
  have hparent : dyadicIntervals i.1 i.2 ⊆
      dyadicIntervals (i.1 + 1) (dyadicParentIndex i.2) :=
    dyadicIntervals_subset_parent i.1 i.2
  intro hpbad
  have hpC := dyadicBadInterval_mem_candidateIndices f hf α hα K hK
    (i.1 + 1, dyadicParentIndex i.2) hpbad
  have hpB : (i.1 + 1, dyadicParentIndex i.2) ∈ B :=
    Finset.mem_filter.mpr ⟨hpC, hpbad⟩
  have hback := hiMax (i.1 + 1, dyadicParentIndex i.2) hpB hparent
  have heq : dyadicIntervals i.1 i.2 =
      dyadicIntervals (i.1 + 1) (dyadicParentIndex i.2) :=
    Finset.Subset.antisymm hparent hback
  have hcardEq := congrArg Finset.card heq
  have hcardLt : (dyadicIntervals i.1 i.2).card <
      (dyadicIntervals (i.1 + 1) (dyadicParentIndex i.2)).card := by
    rw [dyadicIntervals_card, dyadicIntervals_card, pow_succ]
    nlinarith [Nat.one_le_two_pow (n := i.1)]
  omega

theorem dyadicCZSelected_average_norm_le_two_alpha (f : ℤ → ℂ)
    (hf : f.HasFiniteSupport) (α : ℝ) (hα : 0 < α) (K : ℕ)
    (hK : discreteL1Norm f < α * (2 : ℝ) ^ K)
    (i : ℕ × ℤ) (hi : i ∈ dyadicCZSelectedBadIndices f hf α K) :
    ‖dyadicIntervalAverage f i‖ ≤ 2 * α := by
  have hparentNot := dyadicCZSelected_parent_not_bad f hf α hα K hK i hi
  have hmassSub : dyadicIntervalMass f i ≤
      dyadicIntervalMass f (i.1 + 1, dyadicParentIndex i.2) := by
    unfold dyadicIntervalMass
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (dyadicIntervals_subset_parent i.1 i.2) (by intro x hx hx'; exact norm_nonneg _)
  have hparentBound : dyadicIntervalMass f (i.1 + 1, dyadicParentIndex i.2) ≤
      α * (dyadicIntervals (i.1 + 1) (dyadicParentIndex i.2)).card := by
    have hnot : ¬ (α * (dyadicIntervals (i.1 + 1) (dyadicParentIndex i.2)).card <
        dyadicIntervalMass f (i.1 + 1, dyadicParentIndex i.2)) := by
      simpa [dyadicBadInterval] using hparentNot
    exact le_of_not_gt hnot
  have hcardEq :
      ((dyadicIntervals (i.1 + 1) (dyadicParentIndex i.2)).card : ℝ) =
        2 * ((dyadicIntervals i.1 i.2).card : ℝ) := by
    rw [dyadicIntervals_card, dyadicIntervals_card]
    norm_cast
    rw [pow_succ]
    ring
  have hcardPos : 0 < ((dyadicIntervals i.1 i.2).card : ℝ) := by
    rw [dyadicIntervals_card]
    positivity
  have hmassBound : dyadicIntervalMass f i ≤
      (2 * α) * ((dyadicIntervals i.1 i.2).card : ℝ) := by
    calc
      dyadicIntervalMass f i ≤ dyadicIntervalMass f (i.1 + 1, dyadicParentIndex i.2) := hmassSub
      _ ≤ α * (dyadicIntervals (i.1 + 1) (dyadicParentIndex i.2)).card := hparentBound
      _ = (2 * α) * ((dyadicIntervals i.1 i.2).card : ℝ) := by rw [hcardEq]; ring
  have hfrac : dyadicIntervalMass f i / (dyadicIntervals i.1 i.2).card ≤ 2 * α := by
    exact (div_le_iff₀ hcardPos).2 (by simpa using hmassBound)
  exact (dyadicIntervalAverage_norm_le_mass_div_card f i).trans hfrac

theorem dyadicIntervals_zero_singleton (x : ℤ) :
    dyadicIntervals 0 x = {x} := by
  ext y
  simp only [Finset.mem_singleton]
  rw [mem_dyadicIntervals]
  norm_num
  omega

theorem dyadicIntervalMass_zero_singleton (f : ℤ → ℂ) (x : ℤ) :
    dyadicIntervalMass f (0, x) = ‖f x‖ := by
  simp [dyadicIntervalMass, dyadicIntervals_zero_singleton]

theorem dyadicBadInterval_zero_iff (f : ℤ → ℂ) (α : ℝ) (x : ℤ) :
    dyadicBadInterval f α (0, x) ↔ α < ‖f x‖ := by
  simp [dyadicBadInterval, dyadicIntervalMass_zero_singleton,
    dyadicIntervals_card]

theorem dyadicCZGoodPart_norm_le_two_alpha (f : ℤ → ℂ)
    (hf : f.HasFiniteSupport) (α : ℝ) (hα : 0 < α) (K : ℕ)
    (hK : discreteL1Norm f < α * (2 : ℝ) ^ K) (x : ℤ) :
    ‖dyadicCZGoodPart f (dyadicCZSelectedBadIndices f hf α K) x‖ ≤ 2 * α := by
  classical
  let S := dyadicCZSelectedBadIndices f hf α K
  let B := dyadicCZBadCandidateIndices f α (dyadicCZCandidateIndices f hf K)
  have hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (dyadicIntervals i.1 i.2) (dyadicIntervals j.1 j.2) := by
    intro i hi j hj hne
    exact maximal_bad_indices_disjoint B hi hj hne
  by_cases hx : x ∈ dyadicCZIntervalUnion S
  · obtain ⟨i, hi, hxI⟩ := Finset.mem_biUnion.mp hx
    rw [dyadicCZGoodPart_eq_intervalAverage f S hdisj i hi hxI]
    exact dyadicCZSelected_average_norm_le_two_alpha f hf α hα K hK i hi
  · rw [dyadicCZGoodPart_eq_f_of_not_mem_union f S hx]
    have hfx : ‖f x‖ ≤ α := by
      by_contra hnot
      have hstrict : α < ‖f x‖ := lt_of_not_ge hnot
      have hbad : dyadicBadInterval f α (0, x) :=
        (dyadicBadInterval_zero_iff f α x).2 hstrict
      have hcandidate := dyadicBadInterval_mem_candidateIndices f hf α hα K hK
        (0, x) hbad
      have hB : (0, x) ∈ B := Finset.mem_filter.mpr ⟨hcandidate, hbad⟩
      obtain ⟨j, hj, hsub⟩ := maximal_bad_indices_cover B (0, x) hB
      have hx0 : x ∈ dyadicIntervals 0 x := by
        rw [dyadicIntervals_zero_singleton]
        simp
      have hxj : x ∈ dyadicIntervals j.1 j.2 := hsub hx0
      exact hx (Finset.mem_biUnion.mpr ⟨j, hj, hxj⟩)
    exact hfx.trans (by linarith)

theorem dyadicCZGoodPart_l1_le (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (α : ℝ) (hα : 0 < α) (K : ℕ)
    (hK : discreteL1Norm f < α * (2 : ℝ) ^ K) :
    discreteL1Norm (dyadicCZGoodPart f (dyadicCZSelectedBadIndices f hf α K)) ≤
      discreteL1Norm f := by
  classical
  let S := dyadicCZSelectedBadIndices f hf α K
  let B := dyadicCZBadCandidateIndices f α (dyadicCZCandidateIndices f hf K)
  let U := dyadicCZIntervalUnion S
  let T := U ∪ hf.toFinset
  have hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (dyadicIntervals i.1 i.2) (dyadicIntervals j.1 j.2) := by
    intro i hi j hj hne
    exact maximal_bad_indices_disjoint B hi hj hne
  have hsupport : Function.support (dyadicCZGoodPart f S) ⊆
      Function.support f ∪ (U : Set ℤ) := by
    intro x hx
    change dyadicCZGoodPart f S x ≠ 0 at hx
    by_cases hxf : x ∈ Function.support f
    · exact Set.mem_union_left _ hxf
    · by_cases hxU : x ∈ U
      · exact Set.mem_union_right _ hxU
      · have hfx : f x = 0 := by
          by_contra hfx
          exact hxf (Function.mem_support.mpr hfx)
        rw [dyadicCZGoodPart_eq_f_of_not_mem_union f S hxU, hfx] at hx
        simp at hx
  have hsupportG : Function.support (dyadicCZGoodPart f S) ⊆ (T : Set ℤ) := by
    intro x hx
    rcases hsupport hx with hxf | hxU
    · exact Finset.mem_union_right _ (hf.mem_toFinset.mpr hxf)
    · exact Finset.mem_union_left _ hxU
  have hsupportF : Function.support f ⊆ (T : Set ℤ) := by
    intro x hxf
    exact Finset.mem_union_right _ (hf.mem_toFinset.mpr hxf)
  have hnormG := discreteL1Norm_eq_sum_of_support_subset
    (dyadicCZGoodPart f S) T hsupportG
  have hnormF := discreteL1Norm_eq_sum_of_support_subset f T hsupportF
  rw [hnormG, hnormF]
  have hfilterIn : T.filter (fun x => x ∈ U) = U := by
    ext x
    by_cases hx : x ∈ U <;> simp [T, hx]
  have hfilterOut : T.filter (fun x => x ∉ U) =
      hf.toFinset.filter (fun x => x ∉ U) := by
    ext x
    by_cases hx : x ∈ U <;> simp [T, hx]
  have hinsideEq :
      (∑ x ∈ U, ‖dyadicCZGoodPart f S x‖) =
        ∑ i ∈ S, ((dyadicIntervals i.1 i.2).card : ℝ) *
          ‖dyadicIntervalAverage f i‖ := by
    dsimp [U, dyadicCZIntervalUnion]
    rw [Finset.sum_biUnion (by
      intro i hi j hj hne
      exact hdisj i hi j hj hne)]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∑ x ∈ dyadicIntervals i.1 i.2, ‖dyadicCZGoodPart f S x‖) =
          ∑ x ∈ dyadicIntervals i.1 i.2, ‖dyadicIntervalAverage f i‖ := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [dyadicCZGoodPart_eq_intervalAverage f S hdisj i hi hx]
      _ = ((dyadicIntervals i.1 i.2).card : ℝ) *
          ‖dyadicIntervalAverage f i‖ := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hinsideMass :
      (∑ i ∈ S, ((dyadicIntervals i.1 i.2).card : ℝ) *
          ‖dyadicIntervalAverage f i‖) ≤
        ∑ i ∈ S, dyadicIntervalMass f i := by
    apply Finset.sum_le_sum
    intro i hi
    exact dyadicIntervalAverage_card_mul_norm_le_mass f i
  have hinside :
      (∑ x ∈ U, ‖dyadicCZGoodPart f S x‖) ≤ ∑ x ∈ U, ‖f x‖ := by
    calc
      (∑ x ∈ U, ‖dyadicCZGoodPart f S x‖) =
          ∑ i ∈ S, ((dyadicIntervals i.1 i.2).card : ℝ) *
            ‖dyadicIntervalAverage f i‖ := hinsideEq
      _ ≤ ∑ i ∈ S, dyadicIntervalMass f i := hinsideMass
      _ = ∑ x ∈ U, ‖f x‖ := by
        simpa [U] using dyadicIntervalMass_sum_union f S hdisj
  have houtside :
      (∑ x ∈ hf.toFinset.filter (fun x => x ∉ U),
          ‖dyadicCZGoodPart f S x‖) =
        ∑ x ∈ hf.toFinset.filter (fun x => x ∉ U), ‖f x‖ := by
    apply Finset.sum_congr rfl
    intro x hx
    exact congrArg norm
      (dyadicCZGoodPart_eq_f_of_not_mem_union f S (Finset.mem_filter.mp hx).2)
  calc
    (∑ x ∈ T, ‖dyadicCZGoodPart f S x‖) =
        (∑ x ∈ T.filter (fun x => x ∈ U), ‖dyadicCZGoodPart f S x‖) +
          ∑ x ∈ T.filter (fun x => x ∉ U), ‖dyadicCZGoodPart f S x‖ := by
      rw [← Finset.sum_filter_add_sum_filter_not T (fun x => x ∈ U)]
    _ = (∑ x ∈ U, ‖dyadicCZGoodPart f S x‖) +
          ∑ x ∈ hf.toFinset.filter (fun x => x ∉ U), ‖f x‖ := by
      rw [hfilterIn, hfilterOut, houtside]
    _ ≤ (∑ x ∈ U, ‖f x‖) +
          ∑ x ∈ hf.toFinset.filter (fun x => x ∉ U), ‖f x‖ :=
      by
        calc
          _ = (∑ x ∈ hf.toFinset.filter (fun x => x ∉ U), ‖f x‖) +
              (∑ x ∈ U, ‖dyadicCZGoodPart f S x‖) := by ring
          _ ≤ (∑ x ∈ hf.toFinset.filter (fun x => x ∉ U), ‖f x‖) +
              (∑ x ∈ U, ‖f x‖) := add_le_add_right hinside _
          _ = (∑ x ∈ U, ‖f x‖) +
              ∑ x ∈ hf.toFinset.filter (fun x => x ∉ U), ‖f x‖ := by ring
    _ = ∑ x ∈ T, ‖f x‖ := by
      rw [← Finset.sum_filter_add_sum_filter_not T (fun x => x ∈ U),
        hfilterIn, hfilterOut]

theorem dyadicCZGoodPart_l2_sq_le (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (α : ℝ) (hα : 0 < α) (K : ℕ)
    (hK : discreteL1Norm f < α * (2 : ℝ) ^ K) :
    discreteL2NormSq (dyadicCZGoodPart f
      (dyadicCZSelectedBadIndices f hf α K)) ≤
      2 * α * discreteL1Norm f := by
  let g := dyadicCZGoodPart f (dyadicCZSelectedBadIndices f hf α K)
  have hg : g.HasFiniteSupport := by
    exact dyadicCZGoodPart_hasFiniteSupport f hf
      (dyadicCZSelectedBadIndices f hf α K)
  have hpoint (x : ℤ) : ‖g x‖ ≤ 2 * α := by
    exact dyadicCZGoodPart_norm_le_two_alpha f hf α hα K hK x
  have hsum :
      (∑ x ∈ hg.toFinset, ‖g x‖ ^ 2) ≤
        2 * α * ∑ x ∈ hg.toFinset, ‖g x‖ := by
    calc
      (∑ x ∈ hg.toFinset, ‖g x‖ ^ 2) ≤
          ∑ x ∈ hg.toFinset, (2 * α) * ‖g x‖ := by
        apply Finset.sum_le_sum
        intro x hx
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hpoint x) (norm_nonneg _)
      _ = 2 * α * ∑ x ∈ hg.toFinset, ‖g x‖ := by
        rw [Finset.mul_sum]
  calc
    discreteL2NormSq g = ∑ x ∈ hg.toFinset, ‖g x‖ ^ 2 :=
      discreteL2NormSq_eq_sum_support g hg
    _ ≤ 2 * α * ∑ x ∈ hg.toFinset, ‖g x‖ := hsum
    _ = 2 * α * discreteL1Norm g := by
      rw [← discreteL1Norm_eq_sum_support g hg]
    _ ≤ 2 * α * discreteL1Norm f := by
      exact mul_le_mul_of_nonneg_left
        (dyadicCZGoodPart_l1_le f hf α hα K hK) (by positivity)

theorem dyadicBadPiece_support_subset (f : ℤ → ℂ) (i : ℕ × ℤ) :
    Function.support (dyadicBadPiece f i) ⊆
      (dyadicIntervals i.1 i.2 : Set ℤ) := by
  intro x hx
  change dyadicBadPiece f i x ≠ 0 at hx
  by_contra hxI
  have hxI' : x ∉ dyadicIntervals i.1 i.2 := by simpa using hxI
  apply hx
  simp [dyadicBadPiece, hxI']

theorem dyadicBadPiece_l1_le_two_mass (f : ℤ → ℂ) (i : ℕ × ℤ) :
    discreteL1Norm (dyadicBadPiece f i) ≤ 2 * dyadicIntervalMass f i := by
  have hsupport := dyadicBadPiece_support_subset f i
  rw [discreteL1Norm_eq_sum_of_support_subset
    (dyadicBadPiece f i) (dyadicIntervals i.1 i.2) hsupport]
  calc
    (∑ x ∈ dyadicIntervals i.1 i.2, ‖dyadicBadPiece f i x‖) ≤
        ∑ x ∈ dyadicIntervals i.1 i.2,
          (‖f x‖ + ‖dyadicIntervalAverage f i‖) := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [dyadicBadPiece, if_pos hx]
      exact norm_sub_le _ _
    _ = dyadicIntervalMass f i +
        ((dyadicIntervals i.1 i.2).card : ℝ) *
          ‖dyadicIntervalAverage f i‖ := by
      rw [Finset.sum_add_distrib]
      simp [dyadicIntervalMass, Finset.sum_const, nsmul_eq_mul]
    _ ≤ dyadicIntervalMass f i + dyadicIntervalMass f i := by
      calc
        dyadicIntervalMass f i +
            ((dyadicIntervals i.1 i.2).card : ℝ) *
              ‖dyadicIntervalAverage f i‖ =
            ((dyadicIntervals i.1 i.2).card : ℝ) *
              ‖dyadicIntervalAverage f i‖ + dyadicIntervalMass f i := by ring
        _ ≤ dyadicIntervalMass f i + dyadicIntervalMass f i :=
          add_le_add_left
            (dyadicIntervalAverage_card_mul_norm_le_mass f i) _
    _ = 2 * dyadicIntervalMass f i := by ring

theorem dyadicCZBadPieces_l1_sum_le (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (α : ℝ) (hα : 0 < α) (K : ℕ)
    (hK : discreteL1Norm f < α * (2 : ℝ) ^ K) :
    (∑ i ∈ dyadicCZSelectedBadIndices f hf α K,
      discreteL1Norm (dyadicBadPiece f i)) ≤ 2 * discreteL1Norm f := by
  classical
  let S := dyadicCZSelectedBadIndices f hf α K
  let B := dyadicCZBadCandidateIndices f α (dyadicCZCandidateIndices f hf K)
  have hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (dyadicIntervals i.1 i.2) (dyadicIntervals j.1 j.2) := by
    intro i hi j hj hne
    exact maximal_bad_indices_disjoint B hi hj hne
  have hbadBound :
      (∑ i ∈ S, dyadicIntervalMass f i) ≤ discreteL1Norm f := by
    rw [dyadicIntervalMass_sum_union f S hdisj]
    simpa [S] using dyadicCZIntervalUnion_sum_le_discreteL1Norm f hf S
  calc
    (∑ i ∈ S, discreteL1Norm (dyadicBadPiece f i)) ≤
        ∑ i ∈ S, 2 * dyadicIntervalMass f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact dyadicBadPiece_l1_le_two_mass f i
    _ = 2 * ∑ i ∈ S, dyadicIntervalMass f i := by
      rw [Finset.mul_sum]
    _ ≤ 2 * discreteL1Norm f :=
      mul_le_mul_of_nonneg_left hbadBound (by positivity)

theorem dyadicCZSelected_interval_card_sum_le (f : ℤ → ℂ)
    (hf : f.HasFiniteSupport) (α : ℝ) (hα : 0 < α) (K : ℕ)
    (hK : discreteL1Norm f < α * (2 : ℝ) ^ K) :
    (∑ i ∈ dyadicCZSelectedBadIndices f hf α K,
      ((dyadicIntervals i.1 i.2).card : ℝ)) ≤ discreteL1Norm f / α := by
  classical
  let S := dyadicCZSelectedBadIndices f hf α K
  let B := dyadicCZBadCandidateIndices f α (dyadicCZCandidateIndices f hf K)
  have hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (dyadicIntervals i.1 i.2) (dyadicIntervals j.1 j.2) := by
    intro i hi j hj hne
    exact maximal_bad_indices_disjoint B hi hj hne
  have hmassBound : (∑ i ∈ S,
      α * (dyadicIntervals i.1 i.2).card) ≤
        ∑ i ∈ S, dyadicIntervalMass f i := by
    apply Finset.sum_le_sum
    intro i hi
    have hbad : dyadicBadInterval f α i := by
      have hiB : i ∈ B := (Finset.mem_filter.mp hi).1
      exact (Finset.mem_filter.mp hiB).2
    exact le_of_lt hbad
  have hmassL1 : (∑ i ∈ S, dyadicIntervalMass f i) ≤ discreteL1Norm f := by
    calc
      (∑ i ∈ S, dyadicIntervalMass f i) =
          ∑ x ∈ dyadicCZIntervalUnion S, ‖f x‖ :=
        dyadicIntervalMass_sum_union f S hdisj
      _ ≤ discreteL1Norm f := by
        simpa [S] using dyadicCZIntervalUnion_sum_le_discreteL1Norm f hf S
  have htotal :
      α * (∑ i ∈ S, ((dyadicIntervals i.1 i.2).card : ℝ)) ≤
        discreteL1Norm f := by
    calc
      α * (∑ i ∈ S, ((dyadicIntervals i.1 i.2).card : ℝ)) =
          ∑ i ∈ S, α * (dyadicIntervals i.1 i.2).card := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ S, dyadicIntervalMass f i := hmassBound
      _ ≤ discreteL1Norm f := hmassL1
  apply (le_div_iff₀ hα).2
  simpa [mul_comm] using htotal

theorem dyadicBadPiece_eq_zero_of_not_mem (f : ℤ → ℂ) (i : ℕ × ℤ) {x : ℤ}
    (hx : x ∉ dyadicIntervals i.1 i.2) : dyadicBadPiece f i x = 0 := by
  simp [dyadicBadPiece, hx]

theorem dyadicBadPiece_sum_eq_zero (f : ℤ → ℂ) (i : ℕ × ℤ) :
    ∑ x ∈ dyadicIntervals i.1 i.2, dyadicBadPiece f i x = 0 := by
  have hcard : (dyadicIntervals i.1 i.2).card ≠ 0 := by
    rw [dyadicIntervals_card]
    positivity
  calc
    (∑ x ∈ dyadicIntervals i.1 i.2, dyadicBadPiece f i x) =
        ∑ x ∈ dyadicIntervals i.1 i.2,
          (f x - dyadicIntervalAverage f i) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [dyadicBadPiece, hx]
    _ = 0 := by
      rw [Finset.sum_sub_distrib]
      rw [dyadicIntervalAverage]
      simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
      have hcardC : ((dyadicIntervals i.1 i.2).card : ℂ) ≠ 0 := by
        exact_mod_cast hcard
      calc
        (∑ x ∈ dyadicIntervals i.1 i.2, f x) -
            ↑(dyadicIntervals i.1 i.2).card *
              ((∑ x ∈ dyadicIntervals i.1 i.2, f x) /
                ↑(dyadicIntervals i.1 i.2).card) =
            (∑ x ∈ dyadicIntervals i.1 i.2, f x) -
              ((∑ x ∈ dyadicIntervals i.1 i.2, f x) /
                ↑(dyadicIntervals i.1 i.2).card) *
                  ↑(dyadicIntervals i.1 i.2).card := by ring
        _ = 0 := by rw [div_mul_cancel₀ _ hcardC]; ring

/-- The finite integer Calderón--Zygmund decomposition with the constants
and cancellation clauses in the approved multiplier blueprint. -/
theorem discreteCZDecomposition (f : ℤ → ℂ) (hf : f.HasFiniteSupport)
    (α : ℝ) (hα : 0 < α) : Nonempty (DiscreteCZDecompositionData f α) := by
  obtain ⟨K, hK⟩ := exists_dyadicCZ_scale_cutoff f α hα
  let S := dyadicCZSelectedBadIndices f hf α K
  let g := dyadicCZGoodPart f S
  let B := dyadicCZBadCandidateIndices f α (dyadicCZCandidateIndices f hf K)
  have hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (dyadicIntervals i.1 i.2) (dyadicIntervals j.1 j.2) := by
    intro i hi j hj hne
    exact maximal_bad_indices_disjoint B hi hj hne
  refine ⟨{
    intervals := S
    goodPart := g
    pairwiseDisjoint := hdisj
    decomposition := ?_
    interval_measure_bound := dyadicCZSelected_interval_card_sum_le f hf α hα K hK
    good_lInf_bound := ?_
    good_l1_bound := dyadicCZGoodPart_l1_le f hf α hα K hK
    good_l2_sq_bound := dyadicCZGoodPart_l2_sq_le f hf α hα K hK
    bad_support := ?_
    bad_mean_zero := ?_
    bad_l1_bound := dyadicCZBadPieces_l1_sum_le f hf α hα K hK
    good_finite_support := dyadicCZGoodPart_hasFiniteSupport f hf S
    bad_finite_support := ?_
  }⟩
  · intro x
    simp only [g, dyadicCZGoodPart]
    ring
  · rw [discreteLInfNorm]
    apply csSup_le
    · exact ⟨‖g 0‖, ⟨0, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      exact dyadicCZGoodPart_norm_le_two_alpha f hf α hα K hK x
  · intro i hi
    exact dyadicBadPiece_support_subset f i
  · intro i hi
    exact dyadicBadPiece_sum_eq_zero f i
  · intro i hi
    exact dyadicBadPiece_hasFiniteSupport f i

end

end FractionalPrimes.Literature.Multiplier
