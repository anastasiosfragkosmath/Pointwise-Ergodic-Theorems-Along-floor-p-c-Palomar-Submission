module

public import FractionalPrimes.Literature.Hyperbola.RationalCellPointCount
public import FractionalPrimes.Literature.Hyperbola.ProgressionLengthSplit
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

/-- The natural-index model has exactly the number of indices as points when
the first coordinate advances by a positive integer step. -/
private theorem natIndexedLatticeProgression_ncard
    (base : ℤ × ℤ) (q a : ℤ) (hq : 0 < q) (lo hi : ℕ) :
    (natIndexedLatticeProgression base q a lo hi).ncard = hi + 1 - lo := by
  have hinj : Function.Injective (latticeProgressionPoint base q a) := by
    intro i j hij
    have hfst := congrArg Prod.fst hij
    dsimp [latticeProgressionPoint] at hfst
    have hmul : (i : ℤ) * q = (j : ℤ) * q := add_left_cancel hfst
    exact_mod_cast mul_right_cancel₀ hq.ne' hmul
  unfold natIndexedLatticeProgression
  rw [Set.ncard_image_of_injective _ hinj]
  simp

/-- Exact cardinality of an integer-interval progression with positive
horizontal spacing. -/
theorem cellLatticeIccProgression_ncard
    (base : ℤ × ℤ) (q a lo hi : ℤ) (hq : 0 < q) (hlohi : lo ≤ hi) :
    (cellLatticeIccProgression base q a lo hi).ncard =
      (hi - lo + 1).toNat := by
  let N := (hi - lo + 1).toNat
  have hdiffpos : 0 < hi - lo + 1 := by omega
  have hNcast : (N : ℤ) = hi - lo + 1 := by
    dsimp [N]
    exact Int.toNat_of_nonneg hdiffpos.le
  have hNpos : 0 < N := by
    have h : (0 : ℤ) < (N : ℤ) := by rw [hNcast]; omega
    exact_mod_cast h
  rw [cellLatticeIccProgression_rebase base q a lo hi hlohi]
  rw [natIndexedLatticeProgression_ncard _ _ _ hq 0 (N - 1)]
  simp [N]
  omega

/-- Exact cardinality for both nonempty and empty integer-interval
progressions. -/
theorem cellLatticeIccProgression_ncard_general
    (base : ℤ × ℤ) (q a lo hi : ℤ) (hq : 0 < q) :
    (cellLatticeIccProgression base q a lo hi).ncard =
      (hi - lo + 1).toNat := by
  by_cases hlohi : lo ≤ hi
  · exact cellLatticeIccProgression_ncard base q a lo hi hq hlohi
  · have hempty : cellLatticeIccProgression base q a lo hi = ∅ := by
      ext p
      simp [cellLatticeIccProgression, not_le.mp hlohi]
    have hNzero : (hi - lo + 1).toNat = 0 := by
      apply Int.toNat_of_nonpos
      omega
    simp [hempty, hNzero]

/-- The initial point obtained by rebasing an integer-indexed progression at
its lower endpoint. -/
def progressionIntervalStart (base : ℤ × ℤ) (q a lo : ℤ) : ℤ × ℤ :=
  (base.1 + lo * q, base.2 - lo * a)

/-- Split an integer-interval progression into a finite family of shorter
progressions. If the interval is empty, its natural length is zero and the
family is empty. -/
noncomputable def progressionIntervalSplitFamily
    (base : ℤ × ℤ) (q a lo hi : ℤ) (L : ℝ) : Finset (Set (ℤ × ℤ)) := by
  classical
  exact if lo ≤ hi then
    progressionSplitFamily (progressionIntervalStart base q a lo) q a
      (hi - lo + 1).toNat L
  else ∅

/-- Properties of the deterministic split after rebasing an integer interval.
The integer interval may be empty at the definition level; the theorem applies
to nonempty intervals. -/
theorem progressionIntervalSplitFamilyProperties
    (base : ℤ × ℤ) (q a lo hi : ℤ) (hq : 0 < q) (hlohi : lo ≤ hi)
    (L : ℝ) (hL : 1 ≤ L) :
    (∀ P ∈ progressionIntervalSplitFamily base q a lo hi L, P.Nonempty) ∧
    (∀ P ∈ progressionIntervalSplitFamily base q a lo hi L,
      (P.ncard : ℝ) ≤ L) ∧
    (∀ p, p ∈ cellLatticeIccProgression base q a lo hi ↔
      ∃ P ∈ progressionIntervalSplitFamily base q a lo hi L, p ∈ P) ∧
    (∀ P ∈ progressionIntervalSplitFamily base q a lo hi L,
      ∃ b l h, P = natIndexedLatticeProgression b q a l h ∧ l ≤ h) ∧
    (∀ P ∈ progressionIntervalSplitFamily base q a lo hi L,
      ∀ P' ∈ progressionIntervalSplitFamily base q a lo hi L,
        P ≠ P' → Disjoint P P') ∧
    ((progressionIntervalSplitFamily base q a lo hi L).card : ℝ) ≤
      2 * (((hi - lo + 1).toNat : ℕ) : ℝ) / L + 1 := by
  classical
  let N : ℕ := (hi - lo + 1).toNat
  let b := progressionIntervalStart base q a lo
  have hdiffpos : 0 < hi - lo + 1 := by omega
  have hNcast : (N : ℤ) = hi - lo + 1 := by
    dsimp [N]
    exact Int.toNat_of_nonneg hdiffpos.le
  have hNpos : 0 < N := by
    have h : (0 : ℤ) < (N : ℤ) := by rw [hNcast]; omega
    exact_mod_cast h
  have hrebase : cellLatticeIccProgression base q a lo hi =
      natIndexedLatticeProgression b q a 0 (N - 1) := by
    simpa [b, N, progressionIntervalStart] using
      cellLatticeIccProgression_rebase base q a lo hi hlohi
  have hsplit := splitProgressionFamilyProperties b q a hq N hNpos L hL
  have hfamily : progressionIntervalSplitFamily base q a lo hi L =
      progressionSplitFamily b q a N L := by
    simp [progressionIntervalSplitFamily, hlohi, b, N,
      progressionIntervalStart]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hfamily] using hsplit.1
  · simpa [hfamily] using hsplit.2.1
  · intro p
    rw [hrebase, hfamily]
    exact hsplit.2.2.1 p
  · intro P hP
    rw [hfamily] at hP
    change P ∈ (Finset.range (progressionSplitPieceCount N L)).image
      (progressionSplitPiece b q a N L) at hP
    rcases Finset.mem_image.mp hP with ⟨j, hj, hPj⟩
    subst P
    have hjmem : progressionSplitPiece b q a N L j ∈
        progressionSplitFamily b q a N L :=
      Finset.mem_image.mpr ⟨j, hj, rfl⟩
    have hpieceNonempty := hsplit.1 _ hjmem
    refine ⟨b, progressionSplitBlockLower L j,
      progressionSplitBlockUpper N L j, ?_, ?_⟩
    · rfl
    · have hidxNonempty :
          (Set.Icc (progressionSplitBlockLower L j)
            (progressionSplitBlockUpper N L j)).Nonempty := by
        rcases hpieceNonempty with ⟨p, hp⟩
        change p ∈ latticeProgressionPoint b q a ''
          Set.Icc (progressionSplitBlockLower L j)
            (progressionSplitBlockUpper N L j) at hp
        rcases hp with ⟨n, hn, _⟩
        exact ⟨n, hn⟩
      rcases hidxNonempty with ⟨n, hn⟩
      exact hn.1.trans hn.2
  · simpa [hfamily] using hsplit.2.2.2.1
  · simpa [hfamily, N] using hsplit.2.2.2.2

/-- The interval split properties also cover empty source intervals, whose
family is defined to be empty. -/
theorem progressionIntervalSplitFamilyPropertiesGeneral
    (base : ℤ × ℤ) (q a lo hi : ℤ) (hq : 0 < q)
    (L : ℝ) (hL : 1 ≤ L) :
    (∀ P ∈ progressionIntervalSplitFamily base q a lo hi L, P.Nonempty) ∧
    (∀ P ∈ progressionIntervalSplitFamily base q a lo hi L,
      (P.ncard : ℝ) ≤ L) ∧
    (∀ p, p ∈ cellLatticeIccProgression base q a lo hi ↔
      ∃ P ∈ progressionIntervalSplitFamily base q a lo hi L, p ∈ P) ∧
    (∀ P ∈ progressionIntervalSplitFamily base q a lo hi L,
      ∃ b l h, P = natIndexedLatticeProgression b q a l h ∧ l ≤ h) ∧
    (∀ P ∈ progressionIntervalSplitFamily base q a lo hi L,
      ∀ P' ∈ progressionIntervalSplitFamily base q a lo hi L,
        P ≠ P' → Disjoint P P') ∧
    ((progressionIntervalSplitFamily base q a lo hi L).card : ℝ) ≤
      2 * (((hi - lo + 1).toNat : ℕ) : ℝ) / L + 1 := by
  classical
  by_cases hlohi : lo ≤ hi
  · exact progressionIntervalSplitFamilyProperties base q a lo hi hq hlohi L hL
  · have hempty : cellLatticeIccProgression base q a lo hi = ∅ := by
      ext p
      simp [cellLatticeIccProgression, not_le.mp hlohi]
    have hNzero : (hi - lo + 1).toNat = 0 := by
      apply Int.toNat_of_nonpos
      omega
    have hfamily : progressionIntervalSplitFamily base q a lo hi L = ∅ := by
      simp [progressionIntervalSplitFamily, hlohi]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hfamily]
    · simp [hfamily]
    · intro p
      simp [hfamily, hempty]
    · simp [hfamily]
    · simp [hfamily]
    · simp [hfamily, hNzero]

/-- The two finite interval progressions that represent one linear slice. -/
structure CellSliceProgressionDecomposition
    (g : HyperbolaGeometricData) (a q : ℕ) (c : ℤ) where
  base : ℤ × ℤ
  lo₁ : ℤ
  hi₁ : ℤ
  lo₂ : ℤ
  hi₂ : ℤ
  union_eq : cellLinearSliceOnLine g a q c =
      cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁ ∪
        cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂
  disjoint : Disjoint
      (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁)
      (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂)

/-- Select the exact decomposition supplied by `cellLinearSlices`. -/
noncomputable def cellSliceProgressionDecomposition
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (c : ℤ) :
    CellSliceProgressionDecomposition g a q c := by
  classical
  have hnonempty : Nonempty (CellSliceProgressionDecomposition g a q c) := by
    rcases cellLinearSlices_progression_decomposition g a q hidx c with
      ⟨base, lo₁, hi₁, lo₂, hi₂, hunion, hdisjoint, _, _⟩
    exact ⟨⟨base, lo₁, hi₁, lo₂, hi₂, hunion, hdisjoint⟩⟩
  exact Classical.choice hnonempty

/-- The finite family obtained by splitting both interval progressions on one
linear slice. -/
noncomputable def cellLineProgressionSplitFamily
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (c : ℤ) (L : ℝ) :
    Finset (Set (ℤ × ℤ)) := by
  classical
  let d := cellSliceProgressionDecomposition g a q hidx c
  exact progressionIntervalSplitFamily d.base (q : ℤ) (a : ℤ) d.lo₁ d.hi₁ L ∪
    progressionIntervalSplitFamily d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂ L

/-- A split line family is nonempty piecewise, covers the full line slice,
remains pairwise disjoint, and has the source's summed `2N/L+2` bound. -/
theorem cellLineProgressionSplitFamilyProperties
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (c : ℤ)
    (L : ℝ) (hL : 1 ≤ L) :
    (∀ P ∈ cellLineProgressionSplitFamily g a q hidx c L, P.Nonempty) ∧
    (∀ P ∈ cellLineProgressionSplitFamily g a q hidx c L,
      (P.ncard : ℝ) ≤ L) ∧
    (∀ p, p ∈ cellLinearSliceOnLine g a q c ↔
      ∃ P ∈ cellLineProgressionSplitFamily g a q hidx c L, p ∈ P) ∧
    (∀ P ∈ cellLineProgressionSplitFamily g a q hidx c L,
      ∃ b l h, P = natIndexedLatticeProgression b (q : ℤ) (a : ℤ) l h ∧ l ≤ h) ∧
    (∀ P ∈ cellLineProgressionSplitFamily g a q hidx c L,
      ∀ P' ∈ cellLineProgressionSplitFamily g a q hidx c L,
        P ≠ P' → Disjoint P P') ∧
    ((cellLineProgressionSplitFamily g a q hidx c L).card : ℝ) ≤
      2 * (((cellSliceProgressionDecomposition g a q hidx c).hi₁ -
        (cellSliceProgressionDecomposition g a q hidx c).lo₁ + 1).toNat : ℝ) / L +
      2 * (((cellSliceProgressionDecomposition g a q hidx c).hi₂ -
        (cellSliceProgressionDecomposition g a q hidx c).lo₂ + 1).toNat : ℝ) / L + 2 := by
  classical
  let d := cellSliceProgressionDecomposition g a q hidx c
  let F₁ := progressionIntervalSplitFamily d.base (q : ℤ) (a : ℤ) d.lo₁ d.hi₁ L
  let F₂ := progressionIntervalSplitFamily d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂ L
  have hq : 0 < (q : ℤ) := by
    have hqlo : 1 ≤ q := hidx.1.2.1
    have hqNat : 0 < q := by omega
    norm_cast
  have hprops₁ := progressionIntervalSplitFamilyPropertiesGeneral
    d.base (q : ℤ) (a : ℤ) d.lo₁ d.hi₁ hq L hL
  have hprops₂ := progressionIntervalSplitFamilyPropertiesGeneral
    d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂ hq L hL
  have hfamily : cellLineProgressionSplitFamily g a q hidx c L = F₁ ∪ F₂ := by
    rfl
  rw [hfamily]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact hprops₁.1 P hP
    · exact hprops₂.1 P hP
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact hprops₁.2.1 P hP
    · exact hprops₂.2.1 P hP
  · intro p
    rw [d.union_eq]
    constructor
    · intro hp
      have hpu : p ∈ cellLatticeIccProgression d.base (q : ℤ) (a : ℤ)
          d.lo₁ d.hi₁ ∨
        p ∈ cellLatticeIccProgression d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂ :=
        by simpa only [Set.mem_union] using hp
      rcases hpu with hp | hp
      · rcases (hprops₁.2.2.1 p).mp hp with ⟨P, hP, hpP⟩
        exact ⟨P, Finset.mem_union.mpr (Or.inl hP), hpP⟩
      · rcases (hprops₂.2.2.1 p).mp hp with ⟨P, hP, hpP⟩
        exact ⟨P, Finset.mem_union.mpr (Or.inr hP), hpP⟩
    · rintro ⟨P, hP, hpP⟩
      rcases Finset.mem_union.mp hP with hP | hP
      · simpa only [Set.mem_union] using
          (Or.inl ((hprops₁.2.2.1 p).mpr ⟨P, hP, hpP⟩) :
            p ∈ cellLatticeIccProgression d.base (q : ℤ) (a : ℤ) d.lo₁ d.hi₁ ∨
              p ∈ cellLatticeIccProgression d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂)
      · simpa only [Set.mem_union] using
          (Or.inr ((hprops₂.2.2.1 p).mpr ⟨P, hP, hpP⟩) :
            p ∈ cellLatticeIccProgression d.base (q : ℤ) (a : ℤ) d.lo₁ d.hi₁ ∨
              p ∈ cellLatticeIccProgression d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂)
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact hprops₁.2.2.2.1 P hP
    · exact hprops₂.2.2.2.1 P hP
  · intro P hP P' hP' hneq
    rcases Finset.mem_union.mp hP with hP₁ | hP₂ <;>
      rcases Finset.mem_union.mp hP' with hP'₁ | hP'₂
    · exact hprops₁.2.2.2.2.1 P hP₁ P' hP'₁ hneq
    · have hsub₁ : P ⊆ cellLatticeIccProgression d.base (q : ℤ)
        (a : ℤ) d.lo₁ d.hi₁ := by
        intro p hp
        exact (hprops₁.2.2.1 p).mpr ⟨P, hP₁, hp⟩
      have hsub₂ : P' ⊆ cellLatticeIccProgression d.base (q : ℤ)
        (a : ℤ) d.lo₂ d.hi₂ := by
        intro p hp
        exact (hprops₂.2.2.1 p).mpr ⟨P', hP'₂, hp⟩
      apply Set.disjoint_left.mpr
      intro p hp hp'
      exact (Set.disjoint_left.mp d.disjoint) (hsub₁ hp) (hsub₂ hp')
    · have hsub₁ : P' ⊆ cellLatticeIccProgression d.base (q : ℤ)
        (a : ℤ) d.lo₁ d.hi₁ := by
        intro p hp
        exact (hprops₁.2.2.1 p).mpr ⟨P', hP'₁, hp⟩
      have hsub₂ : P ⊆ cellLatticeIccProgression d.base (q : ℤ)
        (a : ℤ) d.lo₂ d.hi₂ := by
        intro p hp
        exact (hprops₂.2.2.1 p).mpr ⟨P, hP₂, hp⟩
      rw [disjoint_comm]
      apply Set.disjoint_left.mpr
      intro p hp hp'
      exact (Set.disjoint_left.mp d.disjoint) (hsub₁ hp) (hsub₂ hp')
    · exact hprops₂.2.2.2.2.1 P hP₂ P' hP'₂ hneq
  · have hcard : ((F₁ ∪ F₂).card : ℝ) ≤ (F₁.card : ℝ) + (F₂.card : ℝ) := by
      exact_mod_cast Finset.card_union_le F₁ F₂
    have hcount₁ := hprops₁.2.2.2.2.2
    have hcount₂ := hprops₂.2.2.2.2.2
    dsimp [F₁, F₂] at hcount₁ hcount₂ ⊢
    linarith

/-- The direction-family cardinality on one occupied line is at most the
split count predicted from the number of points on that line. -/
theorem cellLineProgressionSplitFamily_card_bound
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (c : ℤ)
    (L : ℝ) (hL : 1 ≤ L) :
    ((cellLineProgressionSplitFamily g a q hidx c L).card : ℝ) ≤
      2 * ((cellLinearSliceOnLine g a q c).ncard : ℝ) / L + 2 := by
  classical
  let d := cellSliceProgressionDecomposition g a q hidx c
  have hq : 0 < (q : ℤ) := by
    have hqlo : 1 ≤ q := hidx.1.2.1
    have hqNat : 0 < q := by omega
    norm_cast
  have hcount := (cellLineProgressionSplitFamilyProperties g a q hidx c L hL).2.2.2.2.2
  have hN₁ := cellLatticeIccProgression_ncard_general
    d.base (q : ℤ) (a : ℤ) d.lo₁ d.hi₁ hq
  have hN₂ := cellLatticeIccProgression_ncard_general
    d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂ hq
  have hlineCard : (cellLinearSliceOnLine g a q c).ncard =
      (cellLatticeIccProgression d.base (q : ℤ) (a : ℤ) d.lo₁ d.hi₁).ncard +
      (cellLatticeIccProgression d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂).ncard := by
    rw [d.union_eq, Set.ncard_union_eq d.disjoint
      (cellLatticeIccProgression_finite d.base (q : ℤ) (a : ℤ) d.lo₁ d.hi₁)
      (cellLatticeIccProgression_finite d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂)]
  have hcount' :
      ((cellLineProgressionSplitFamily g a q hidx c L).card : ℝ) ≤
        2 * (((d.hi₁ - d.lo₁ + 1).toNat : ℕ) : ℝ) / L +
          2 * (((d.hi₂ - d.lo₂ + 1).toNat : ℕ) : ℝ) / L + 2 := by
    simpa [d] using hcount
  have hN₁R : (((d.hi₁ - d.lo₁ + 1).toNat : ℕ) : ℝ) =
      ((cellLatticeIccProgression d.base (q : ℤ) (a : ℤ) d.lo₁ d.hi₁).ncard : ℝ) := by
    exact_mod_cast hN₁.symm
  have hN₂R : (((d.hi₂ - d.lo₂ + 1).toNat : ℕ) : ℝ) =
      ((cellLatticeIccProgression d.base (q : ℤ) (a : ℤ) d.lo₂ d.hi₂).ncard : ℝ) := by
    exact_mod_cast hN₂.symm
  calc
    ((cellLineProgressionSplitFamily g a q hidx c L).card : ℝ) ≤
        2 * (((d.hi₁ - d.lo₁ + 1).toNat : ℕ) : ℝ) / L +
          2 * (((d.hi₂ - d.lo₂ + 1).toNat : ℕ) : ℝ) / L + 2 := hcount'
    _ = 2 * (((cellLatticeIccProgression d.base (q : ℤ) (a : ℤ)
          d.lo₁ d.hi₁).ncard : ℝ) +
        ((cellLatticeIccProgression d.base (q : ℤ) (a : ℤ)
          d.lo₂ d.hi₂).ncard : ℝ)) / L + 2 := by rw [hN₁R, hN₂R]; ring
    _ = 2 * ((cellLinearSliceOnLine g a q c).ncard : ℝ) / L + 2 := by
      rw [hlineCard]
      push_cast
      ring

/-- The occupied line values and finite coverage data chosen from the exact
line-count theorem. -/
structure CellOccupiedSliceData
    (g : HyperbolaGeometricData) (a q : ℕ) where
  values : Finset ℤ
  mem_iff : ∀ c, c ∈ values ↔ c ∈ occupiedSliceValues g a q
  count_bound : (values.card : ℝ) ≤ C_line g.K₀ * R_q g q
  covers : ∀ p, p ∈ cellLinearSlice g a q ↔
    ∃ c ∈ values, p ∈ cellLinearSliceOnLine g a q c
  pairwise_disjoint : ∀ c c', c ∈ values → c' ∈ values → c ≠ c' →
    Disjoint (cellLinearSliceOnLine g a q c) (cellLinearSliceOnLine g a q c')

/-- Select the finite line set from `occupiedSliceCount`. -/
noncomputable def cellOccupiedSliceData
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) :
    CellOccupiedSliceData g a q := by
  classical
  have hnonempty : Nonempty (CellOccupiedSliceData g a q) := by
    rcases occupiedSliceCount g a q hidx with
      ⟨S, hmem, hbound, hcoverage, hdisjoint, _, _⟩
    exact ⟨⟨S, hmem, hbound, hcoverage, hdisjoint⟩⟩
  exact Classical.choice hnonempty

/-- The finite set-family obtained by splitting every occupied line in one
rational cell. -/
noncomputable def cellProgressionSplitFamily
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (L : ℝ) :
    Finset (Set (ℤ × ℤ)) := by
  classical
  let data := cellOccupiedSliceData g a q hidx
  exact data.values.biUnion (fun c => cellLineProgressionSplitFamily g a q hidx c L)

/-- Piecewise coverage, length, progression structure, and disjointness after
splitting all occupied lines in a rational cell. -/
theorem cellProgressionSplitFamilyProperties
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (L : ℝ) (hL : 1 ≤ L) :
    (∀ P ∈ cellProgressionSplitFamily g a q hidx L, P.Nonempty) ∧
    (∀ P ∈ cellProgressionSplitFamily g a q hidx L, (P.ncard : ℝ) ≤ L) ∧
    (∀ p, p ∈ cellLinearSlice g a q ↔
      ∃ P ∈ cellProgressionSplitFamily g a q hidx L, p ∈ P) ∧
    (∀ P ∈ cellProgressionSplitFamily g a q hidx L,
      ∃ b l h, P = natIndexedLatticeProgression b (q : ℤ) (a : ℤ) l h ∧ l ≤ h) ∧
    (∀ P ∈ cellProgressionSplitFamily g a q hidx L,
      ∀ P' ∈ cellProgressionSplitFamily g a q hidx L,
        P ≠ P' → Disjoint P P') ∧
    ((cellProgressionSplitFamily g a q hidx L).card : ℝ) ≤
      ∑ c ∈ (cellOccupiedSliceData g a q hidx).values,
        ((cellLineProgressionSplitFamily g a q hidx c L).card : ℝ) := by
  classical
  let data := cellOccupiedSliceData g a q hidx
  let S := data.values
  let lineFamily := fun c => cellLineProgressionSplitFamily g a q hidx c L
  let F := S.biUnion lineFamily
  have hF : cellProgressionSplitFamily g a q hidx L = F := rfl
  have hq : 0 < (q : ℤ) := by
    have hqlo : 1 ≤ q := hidx.1.2.1
    have hqNat : 0 < q := by omega
    norm_cast
  rw [hF]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    rcases Finset.mem_biUnion.mp hP with ⟨c, hc, hPc⟩
    exact (cellLineProgressionSplitFamilyProperties g a q hidx c L hL).1 P hPc
  · intro P hP
    rcases Finset.mem_biUnion.mp hP with ⟨c, hc, hPc⟩
    exact (cellLineProgressionSplitFamilyProperties g a q hidx c L hL).2.1 P hPc
  · intro p
    constructor
    · intro hp
      rcases data.covers p |>.mp hp with ⟨c, hc, hline⟩
      rcases (cellLineProgressionSplitFamilyProperties g a q hidx c L hL).2.2.1 p |>.mp
          hline with ⟨P, hP, hpP⟩
      exact ⟨P, Finset.mem_biUnion.mpr ⟨c, hc, hP⟩, hpP⟩
    · rintro ⟨P, hP, hpP⟩
      rcases Finset.mem_biUnion.mp hP with ⟨c, hc, hPc⟩
      have hline :=
        (cellLineProgressionSplitFamilyProperties g a q hidx c L hL).2.2.1 p
      exact (data.covers p).mpr
        ⟨c, hc, hline.mpr ⟨P, hPc, hpP⟩⟩
  · intro P hP
    rcases Finset.mem_biUnion.mp hP with ⟨c, hc, hPc⟩
    exact (cellLineProgressionSplitFamilyProperties g a q hidx c L hL).2.2.2.1 P hPc
  · intro P hP P' hP' hneq
    rcases Finset.mem_biUnion.mp hP with ⟨c, hc, hPc⟩
    rcases Finset.mem_biUnion.mp hP' with ⟨c', hc', hP'c'⟩
    by_cases hcc' : c = c'
    · subst c'
      exact (cellLineProgressionSplitFamilyProperties g a q hidx c L hL).2.2.2.2.1
        P hPc P' hP'c' hneq
    · have hlineSub : P ⊆ cellLinearSliceOnLine g a q c := by
        intro p hp
        exact ((cellLineProgressionSplitFamilyProperties g a q hidx c L hL).2.2.1 p).mpr
          ⟨P, hPc, hp⟩
      have hlineSub' : P' ⊆ cellLinearSliceOnLine g a q c' := by
        intro p hp
        exact ((cellLineProgressionSplitFamilyProperties g a q hidx c' L hL).2.2.1 p).mpr
          ⟨P', hP'c', hp⟩
      apply Set.disjoint_left.mpr
      intro p hp hp'
      exact (Set.disjoint_left.mp (data.pairwise_disjoint c c' hc hc' hcc'))
        (hlineSub hp) (hlineSub' hp')
  · have hcardNat : F.card ≤ S.sum fun c => (lineFamily c).card :=
      Finset.card_biUnion_le
    exact_mod_cast hcardNat

/-- The occupied line slices are a finite disjoint partition of a cell, so
their point counts add to the point count of the cell. -/
theorem cellLinearSlice_ncard_eq_sum_lines
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) :
    (cellLinearSlice g a q).ncard =
      ∑ c ∈ (cellOccupiedSliceData g a q hidx).values,
        (cellLinearSliceOnLine g a q c).ncard := by
  classical
  let data := cellOccupiedSliceData g a q hidx
  let S := data.values
  let line := fun c => cellLinearSliceOnLine g a q c
  have hparams := admissibleParameterBounds g q hidx.1.2.1 hidx.1.2.2.1
  have hlineFinite : ∀ c, (line c).Finite := by
    intro c
    apply hparams.lattice_finite.subset
    intro p hp
    exact hp.1.1
  have hpair : (S : Set ℤ).PairwiseDisjoint line := by
    intro c hc c' hc' hcc'
    exact data.pairwise_disjoint c c' (by simpa using hc) (by simpa using hc') hcc'
  have hunion : (⋃ c ∈ (S : Set ℤ), line c) = cellLinearSlice g a q := by
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨c, hc, hp⟩
      exact (data.covers p).mpr ⟨c, by simpa using hc, hp⟩
    · intro hp
      rcases (data.covers p).mp hp with ⟨c, hc, hp⟩
      exact ⟨c, by simpa using hc, hp⟩
  have hSfinite : (S : Set ℤ).Finite := S.finite_toSet
  have hsum := hSfinite.ncard_biUnion (fun c _ => hlineFinite c) hpair
  rw [hunion] at hsum
  rw [finsum_mem_eq_finite_toFinset_sum _ hSfinite] at hsum
  simpa [S, data, line] using hsum

/-- The complete split family in one direction has the exact budget used in
the partition proof: twice the cell point count divided by `L`, plus twice
the occupied-line count. -/
theorem cellProgressionSplitFamily_card_bound
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (L : ℝ) (hL : 1 ≤ L) :
    ((cellProgressionSplitFamily g a q hidx L).card : ℝ) ≤
      2 * ((cellLinearSlice g a q).ncard : ℝ) / L +
        2 * ((cellOccupiedSliceData g a q hidx).values.card : ℝ) := by
  classical
  let data := cellOccupiedSliceData g a q hidx
  let S := data.values
  let lineFamily := fun c => cellLineProgressionSplitFamily g a q hidx c L
  have hfamilyBound := (cellProgressionSplitFamilyProperties g a q hidx L hL).2.2.2.2.2
  have hsumLine :
      ∑ c ∈ S, ((cellLinearSliceOnLine g a q c).ncard : ℝ) =
        ((cellLinearSlice g a q).ncard : ℝ) := by
    have hsumNat := cellLinearSlice_ncard_eq_sum_lines g a q hidx
    exact_mod_cast hsumNat.symm
  have hsumBounds :
      ∑ c ∈ S, ((lineFamily c).card : ℝ) ≤
        ∑ c ∈ S,
          (2 * ((cellLinearSliceOnLine g a q c).ncard : ℝ) / L + 2) := by
    apply Finset.sum_le_sum
    intro c hc
    exact cellLineProgressionSplitFamily_card_bound g a q hidx c L hL
  have hsumRewrite :
      ∑ c ∈ S,
          (2 * ((cellLinearSliceOnLine g a q c).ncard : ℝ) / L + 2) =
        2 * (∑ c ∈ S, ((cellLinearSliceOnLine g a q c).ncard : ℝ)) / L +
          2 * (S.card : ℝ) := by
    rw [Finset.sum_add_distrib]
    have hscale :
        (∑ c ∈ S, 2 * ((cellLinearSliceOnLine g a q c).ncard : ℝ) / L) =
          2 * (∑ c ∈ S, ((cellLinearSliceOnLine g a q c).ncard : ℝ)) / L := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
    rw [hscale]
    simp
    ring
  calc
    ((cellProgressionSplitFamily g a q hidx L).card : ℝ) ≤
        ∑ c ∈ S, ((lineFamily c).card : ℝ) := by simpa [S, lineFamily] using hfamilyBound
    _ ≤ ∑ c ∈ S,
          (2 * ((cellLinearSliceOnLine g a q c).ncard : ℝ) / L + 2) := hsumBounds
    _ = 2 * ((cellLinearSlice g a q).ncard : ℝ) / L + 2 * (S.card : ℝ) := by
      rw [hsumRewrite, hsumLine]
    _ = 2 * ((cellLinearSlice g a q).ncard : ℝ) / L +
        2 * ((cellOccupiedSliceData g a q hidx).values.card : ℝ) := by rfl

/-- The exact geometric direction budget after applying the cell point and
occupied-line counts at the prescribed length `L0`. -/
theorem cellProgressionSplitFamily_geometric_count
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) :
    ((cellProgressionSplitFamily g a q hidx g.L0).card : ℝ) ≤
      C_geo g.K₀ * R_q g q := by
  classical
  let data := cellOccupiedSliceData g a q hidx
  have hparams := admissibleParameterBounds g q hidx.1.2.1 hidx.1.2.2.1
  have hLpos : 0 < g.L0 := lt_of_lt_of_le zero_lt_one hparams.L0_lower
  have hpoint := rationalCellPointCount g a q hidx
  have hline := data.count_bound
  have hsplit := cellProgressionSplitFamily_card_bound g a q hidx g.L0
    hparams.L0_lower
  have hfirst : 2 * ((cellLinearSlice g a q).ncard : ℝ) / g.L0 ≤
      2 * (C_point g.K₀ * S_q g q) / g.L0 := by
    apply div_le_div_of_nonneg_right ?_ hLpos.le
    exact mul_le_mul_of_nonneg_left hpoint (by norm_num)
  have hsecond : 2 * (data.values.card : ℝ) ≤
      2 * (C_line g.K₀ * R_q g q) :=
    mul_le_mul_of_nonneg_left hline (by norm_num)
  have hbudget :
      2 * (C_point g.K₀ * S_q g q) / g.L0 +
        2 * (C_line g.K₀ * R_q g q) =
      2 * (C_point g.K₀ + C_line g.K₀) * R_q g q := by
    calc
      _ = 2 * C_point g.K₀ * (S_q g q / g.L0) +
            2 * C_line g.K₀ * R_q g q := by ring
      _ = 2 * C_point g.K₀ * R_q g q +
            2 * C_line g.K₀ * R_q g q := by rw [hparams.S_div_L0_eq_R]
      _ = 2 * (C_point g.K₀ + C_line g.K₀) * R_q g q := by ring
  have hRqnonneg : 0 ≤ R_q g q := le_trans zero_le_one hparams.R_lower
  have hExtra : 0 ≤ 8 + E g.K₀ := by
    dsimp [E]
    positivity
  calc
    ((cellProgressionSplitFamily g a q hidx g.L0).card : ℝ) ≤
        2 * ((cellLinearSlice g a q).ncard : ℝ) / g.L0 +
          2 * (data.values.card : ℝ) := hsplit
    _ ≤ 2 * (C_point g.K₀ * S_q g q) / g.L0 +
          2 * (C_line g.K₀ * R_q g q) := add_le_add hfirst hsecond
    _ = 2 * (C_point g.K₀ + C_line g.K₀) * R_q g q := hbudget
    _ ≤ C_geo g.K₀ * R_q g q := by
      rw [C_geo]
      nlinarith [mul_nonneg hExtra hRqnonneg]

/-- The partition family at direction `(a,q)`. It is empty outside the finite
set of eligible rational-cell indices. -/
noncomputable def hyperbolaProgressionFamily
    (g : HyperbolaGeometricData) (a q : ℕ) : Finset (Set (ℤ × ℤ)) := by
  classical
  by_cases hidx : positiveRationalCellIndexEligible g a q
  · exact cellProgressionSplitFamily g a q hidx g.L0
  · exact ∅

theorem hyperbolaProgressionFamily_eq_of_eligible
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) :
    hyperbolaProgressionFamily g a q = cellProgressionSplitFamily g a q hidx g.L0 := by
  classical
  simp [hyperbolaProgressionFamily, hidx]

/-- The finite set of all direction-labelled progression pieces in the
hyperbola partition. -/
noncomputable def globalHyperbolaProgressionFamily
    (g : HyperbolaGeometricData) : Finset (Set (ℤ × ℤ)) := by
  classical
  exact (positiveRationalCellIndices g).biUnion fun i =>
    hyperbolaProgressionFamily g i.1 i.2

/-- Exact structural claims of the quantified hyperbola partition. -/
structure HyperbolaProgressionPartitionData
    (g : HyperbolaGeometricData) : Prop where
  direction : ∀ a q, positiveRationalCellIndexEligible g a q →
    Nat.Coprime a q ∧ 1 ≤ q ∧ q ≤ g.Q ∧
      (C_geo g.K₀)⁻¹ * g.r * (q : ℝ) ≤ (a : ℝ) ∧
      (a : ℝ) ≤ C_geo g.K₀ * g.r * (q : ℝ) ∧
      g.r * (q : ℝ) / 8 ≤ (a : ℝ) ∧
      (a : ℝ) ≤ E g.K₀ * g.r * (q : ℝ)
  pieces : ∀ a q, (a, q) ∈ positiveRationalCellIndices g →
    ∀ P ∈ hyperbolaProgressionFamily g a q,
      P.Nonempty ∧ (P.ncard : ℝ) ≤ g.L0 ∧ P ⊆ g.lattice ∧
        ∃ b l h, P = natIndexedLatticeProgression b (q : ℤ) (a : ℤ) l h ∧ l ≤ h
  count : ∀ a q, positiveRationalCellIndexEligible g a q →
    ((hyperbolaProgressionFamily g a q).card : ℝ) ≤ C_geo g.K₀ * R_q g q
  covers : ∀ p, p ∈ g.lattice ↔
    ∃ P ∈ globalHyperbolaProgressionFamily g, p ∈ P
  pairwise_disjoint : ∀ i ∈ positiveRationalCellIndices g,
    ∀ j ∈ positiveRationalCellIndices g,
      ∀ P ∈ hyperbolaProgressionFamily g i.1 i.2,
        ∀ P' ∈ hyperbolaProgressionFamily g j.1 j.2,
          (i ≠ j ∨ P ≠ P') → Disjoint P P'

/-- The exact comparability bounds on a direction index, including the
stronger bounds retained from rational-cell eligibility. -/
private theorem hyperbolaDirectionBounds
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) :
    Nat.Coprime a q ∧ 1 ≤ q ∧ q ≤ g.Q ∧
      (C_geo g.K₀)⁻¹ * g.r * (q : ℝ) ≤ (a : ℝ) ∧
      (a : ℝ) ≤ C_geo g.K₀ * g.r * (q : ℝ) ∧
      g.r * (q : ℝ) / 8 ≤ (a : ℝ) ∧
      (a : ℝ) ≤ E g.K₀ * g.r * (q : ℝ) := by
  rcases hidx.1 with ⟨hcop, hqlo, hqhi, _, hamin, hamax⟩
  have hKnonneg : 0 ≤ g.K₀ := le_trans zero_le_one g.K₀_ge_one
  have hCpos : 0 < C_geo g.K₀ := by
    dsimp [C_geo, C_point, C_line, D, E]
    positivity
  have hC8 : 8 ≤ C_geo g.K₀ := by
    dsimp [C_geo, C_point, C_line, D, E]
    nlinarith [sq_nonneg g.K₀]
  have hCE : E g.K₀ ≤ C_geo g.K₀ := by
    dsimp [C_geo, C_point, C_line, D, E]
    nlinarith [sq_nonneg g.K₀]
  have hinv : (C_geo g.K₀)⁻¹ ≤ (8 : ℝ)⁻¹ :=
    (inv_le_inv₀ hCpos (by norm_num)).2 hC8
  have hqpos : 0 < (q : ℝ) := by
    have hqNat : 0 < q := by omega
    exact_mod_cast hqNat
  have hrpos : 0 < g.r := by
    dsimp [HyperbolaGeometricData.r]
    have hXpos : 0 < g.X := by linarith [g.X_ge_one]
    have hMpos : 0 < g.M := by linarith [g.M_ge_one]
    exact div_pos hXpos (sq_pos_of_pos hMpos)
  have hrqpos : 0 < g.r * (q : ℝ) := mul_pos hrpos hqpos
  have hlo : (C_geo g.K₀)⁻¹ * g.r * (q : ℝ) ≤ (a : ℝ) := by
    calc
      (C_geo g.K₀)⁻¹ * g.r * (q : ℝ) =
          (C_geo g.K₀)⁻¹ * (g.r * (q : ℝ)) := by ring
      _ ≤ (8 : ℝ)⁻¹ * (g.r * (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hinv hrqpos.le
      _ = g.r * (q : ℝ) / 8 := by ring
      _ = (g.r / 8) * (q : ℝ) := by ring
      _ ≤ (a : ℝ) := hamin
  have hhi : (a : ℝ) ≤ C_geo g.K₀ * g.r * (q : ℝ) := by
    calc
      (a : ℝ) ≤ E g.K₀ * g.r * (q : ℝ) := hamax
      _ = E g.K₀ * (g.r * (q : ℝ)) := by ring
      _ ≤ C_geo g.K₀ * (g.r * (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hCE hrqpos.le
      _ = C_geo g.K₀ * g.r * (q : ℝ) := by ring
  exact ⟨hcop, hqlo, hqhi, hlo, hhi, by
    calc
      g.r * (q : ℝ) / 8 = (g.r / 8) * (q : ℝ) := by ring
      _ ≤ (a : ℝ) := hamin, hamax⟩

/-- The exact finite disjoint progression partition of the hyperbola lattice,
with the source's deterministic direction families and constants. -/
theorem hyperbolaProgressionPartition
    (g : HyperbolaGeometricData) : HyperbolaProgressionPartitionData g := by
  classical
  let cells := positiveRationalCellIndices g
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a q hidx
    exact hyperbolaDirectionBounds g a q hidx
  · intro a q hmem P hP
    have hidx := (positiveRationalCellIndices_mem_iff g a q).1 hmem
    have hfamily := hyperbolaProgressionFamily_eq_of_eligible g a q hidx
    have hprops := cellProgressionSplitFamilyProperties g a q hidx g.L0
      (admissibleParameterBounds g q hidx.1.2.1 hidx.1.2.2.1).L0_lower
    have hPcell : P ∈ cellProgressionSplitFamily g a q hidx g.L0 := by
      simpa [hfamily] using hP
    refine ⟨hprops.1 P hPcell, hprops.2.1 P hPcell, ?_,
      hprops.2.2.2.1 P hPcell⟩
    intro p hp
    have hslice : p ∈ cellLinearSlice g a q :=
      (hprops.2.2.1 p).mpr ⟨P, hPcell, hp⟩
    exact hslice.1
  · intro a q hidx
    rw [hyperbolaProgressionFamily_eq_of_eligible g a q hidx]
    exact cellProgressionSplitFamily_geometric_count g a q hidx
  · intro p
    constructor
    · intro hp
      have hQlo : 1 ≤ g.Q := Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne'
      have hpProps :=
        (admissibleParameterBounds g 1 (by norm_num) hQlo).lattice_point_properties p hp
      have hslope : (p.2 : ℝ) / (p.1 : ℝ) ∈ Set.Ioc (g.r / 4) (2 * g.r) :=
        ⟨hpProps.2.2.1, hpProps.2.2.2⟩
      have hcover := (positiveRationalCellPartition g).covers hslope
      rcases Set.mem_iUnion.mp hcover with ⟨i, hcoveri⟩
      rcases Set.mem_iUnion.mp hcoveri with ⟨hi, hcell⟩
      have himem : i ∈ cells := by simpa [cells] using hi
      have hidx := (positiveRationalCellIndices_mem_iff g i.1 i.2).1 himem
      have hprops := cellProgressionSplitFamilyProperties g i.1 i.2 hidx g.L0
        (admissibleParameterBounds g i.2 hidx.1.2.1 hidx.1.2.2.1).L0_lower
      have hslice : p ∈ cellLinearSlice g i.1 i.2 := ⟨hp, hcell⟩
      rcases (hprops.2.2.1 p).mp hslice with ⟨P, hP, hpP⟩
      refine ⟨P, Finset.mem_biUnion.mpr ⟨i, himem, ?_⟩, hpP⟩
      simpa [hyperbolaProgressionFamily, hidx] using hP
    · rintro ⟨P, hP, hp⟩
      rcases Finset.mem_biUnion.mp hP with ⟨i, hi, hP⟩
      have hidx := (positiveRationalCellIndices_mem_iff g i.1 i.2).1 hi
      have hprops := cellProgressionSplitFamilyProperties g i.1 i.2 hidx g.L0
        (admissibleParameterBounds g i.2 hidx.1.2.1 hidx.1.2.2.1).L0_lower
      have hPcell : P ∈ cellProgressionSplitFamily g i.1 i.2 hidx g.L0 := by
        simpa [hyperbolaProgressionFamily, hidx] using hP
      exact ((hprops.2.2.1 p).mpr ⟨P, hPcell, hp⟩).1
  · intro i hi j hj P hP P' hP' hpieces
    have hidxi := (positiveRationalCellIndices_mem_iff g i.1 i.2).1 hi
    have hidxj := (positiveRationalCellIndices_mem_iff g j.1 j.2).1 hj
    have hPi : P ∈ cellProgressionSplitFamily g i.1 i.2 hidxi g.L0 := by
      simpa [hyperbolaProgressionFamily, hidxi] using hP
    have hPj : P' ∈ cellProgressionSplitFamily g j.1 j.2 hidxj g.L0 := by
      simpa [hyperbolaProgressionFamily, hidxj] using hP'
    by_cases hij : i = j
    · subst j
      have hPneq : P ≠ P' := by
        rcases hpieces with hdir | hPneq
        · exact (hdir rfl).elim
        · exact hPneq
      exact (cellProgressionSplitFamilyProperties g i.1 i.2 hidxi g.L0
        (admissibleParameterBounds g i.2 hidxi.1.2.1 hidxi.1.2.2.1).L0_lower).2.2.2.2.1
          P hPi P' hPj hPneq
    · have hdisjCells :=
        (positiveRationalCellPartition g).pairwise_disjoint i hi j hj hij
      have hpropsi := cellProgressionSplitFamilyProperties g i.1 i.2 hidxi g.L0
        (admissibleParameterBounds g i.2 hidxi.1.2.1 hidxi.1.2.2.1).L0_lower
      have hpropsj := cellProgressionSplitFamilyProperties g j.1 j.2 hidxj g.L0
        (admissibleParameterBounds g j.2 hidxj.1.2.1 hidxj.1.2.2.1).L0_lower
      have hsubi : P ⊆ cellLinearSlice g i.1 i.2 := by
        intro p hp
        exact (hpropsi.2.2.1 p).mpr ⟨P, hPi, hp⟩
      have hsubj : P' ⊆ cellLinearSlice g j.1 j.2 := by
        intro p hp
        exact (hpropsj.2.2.1 p).mpr ⟨P', hPj, hp⟩
      apply Set.disjoint_left.mpr
      intro p hp hp'
      exact (Set.disjoint_left.mp hdisjCells) (hsubi hp).2 (hsubj hp').2

end FractionalPrimes.Literature.Hyperbola

#print axioms FractionalPrimes.Literature.Hyperbola.hyperbolaProgressionPartition
