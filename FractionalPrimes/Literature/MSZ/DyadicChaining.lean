module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

/-- Left endpoint, in finest-grid integer coordinates, of the level-`l`
aligned dyadic block with index `m` inside a grid of depth `L`. -/
def dyadicBlockStart (L l m : ℕ) : ℕ := m * 2 ^ (L - l)

/-- Right endpoint, in finest-grid integer coordinates, of the level-`l`
aligned dyadic block with index `m` inside a grid of depth `L`. -/
def dyadicBlockEnd (L l m : ℕ) : ℕ := (m + 1) * 2 ^ (L - l)

/-- Every valid level-`l` block has its right endpoint in the depth-`L` grid. -/
theorem dyadicBlockEnd_le_grid_end {L l m : ℕ} (hl : l ≤ L) (hm : m < 2 ^ l) :
    dyadicBlockEnd L l m ≤ 2 ^ L := by
  calc
    dyadicBlockEnd L l m ≤ 2 ^ l * 2 ^ (L - l) := by
      unfold dyadicBlockEnd
      exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hm)
    _ = 2 ^ L := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hl]

/-- At a fixed level, distinct aligned blocks cannot contain the same
elementary finest-grid interval. -/
theorem dyadicBlockIndex_unique_of_contains_cell
    {L l m n u : ℕ}
    (hmu : dyadicBlockStart L l m ≤ u)
    (hum : u + 1 ≤ dyadicBlockEnd L l m)
    (hnu : dyadicBlockStart L l n ≤ u)
    (hun : u + 1 ≤ dyadicBlockEnd L l n) : m = n := by
  unfold dyadicBlockStart dyadicBlockEnd at *
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hle : m + 1 ≤ n := Nat.succ_le_of_lt hmn
    have hprod := Nat.mul_le_mul_right (2 ^ (L - l)) hle
    have hbad : u + 1 ≤ u := le_trans hum (le_trans hprod hnu)
    exact False.elim (Nat.not_succ_le_self u (by simpa using hbad))
  · exact hmn
  · have hle : n + 1 ≤ m := Nat.succ_le_of_lt hnm
    have hprod := Nat.mul_le_mul_right (2 ^ (L - l)) hle
    have hbad : u + 1 ≤ u := le_trans hun (le_trans hprod hmu)
    exact False.elim (Nat.not_succ_le_self u (by simpa using hbad))

/-- A standard parent block exists for every positive-level dyadic block,
contains it, and is still a valid block in the coarser grid. -/
theorem dyadicBlockParent_contains_child
    {L l m : ℕ} (hl : 0 < l) (hL : l ≤ L) (hm : m < 2 ^ l) :
    m / 2 < 2 ^ (l - 1) ∧
      dyadicBlockStart L (l - 1) (m / 2) ≤ dyadicBlockStart L l m ∧
      dyadicBlockEnd L l m ≤ dyadicBlockEnd L (l - 1) (m / 2) := by
  have hparentLevel : (l - 1) + 1 = l := by omega
  have hparentPow : 2 ^ (l - 1) * 2 = 2 ^ l := by
    calc
      2 ^ (l - 1) * 2 = 2 ^ Nat.succ (l - 1) := (Nat.pow_succ 2 (l - 1)).symm
      _ = 2 ^ l := by congr 1
  have hmParent : m / 2 < 2 ^ (l - 1) := by
    rw [Nat.div_lt_iff_lt_mul Nat.zero_lt_two, hparentPow]
    exact hm
  have hlevel : L - (l - 1) = (L - l) + 1 := by omega
  have hstart :
      dyadicBlockStart L (l - 1) (m / 2) ≤ dyadicBlockStart L l m := by
    unfold dyadicBlockStart
    rw [hlevel, Nat.pow_succ]
    calc
      m / 2 * (2 ^ (L - l) * 2) = (m / 2 * 2) * 2 ^ (L - l) := by ac_rfl
      _ ≤ m * 2 ^ (L - l) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self m 2)
  have hquotientEnd : m + 1 ≤ (m / 2 + 1) * 2 := by
    have hdecomp := Nat.div_add_mod m 2
    have hmod := Nat.mod_lt m Nat.zero_lt_two
    omega
  have hend :
      dyadicBlockEnd L l m ≤ dyadicBlockEnd L (l - 1) (m / 2) := by
    unfold dyadicBlockEnd
    rw [hlevel, Nat.pow_succ]
    calc
      (m + 1) * 2 ^ (L - l) ≤ ((m / 2 + 1) * 2) * 2 ^ (L - l) :=
        Nat.mul_le_mul_right _ hquotientEnd
      _ = (m / 2 + 1) * (2 ^ (L - l) * 2) := by ac_rfl
  exact ⟨hmParent, hstart, hend⟩

/-- The left child shares the left endpoint of its parent. -/
theorem dyadicBlockStart_even_eq_parent
    {L l p : ℕ} (hl : 0 < l) (hL : l ≤ L) :
    dyadicBlockStart L l (2 * p) = dyadicBlockStart L (l - 1) p := by
  have hlevel : L - (l - 1) = (L - l) + 1 := by omega
  unfold dyadicBlockStart
  rw [hlevel, Nat.pow_succ]
  ac_rfl

/-- The right child shares the right endpoint of its parent. -/
theorem dyadicBlockEnd_odd_eq_parent
    {L l p : ℕ} (hl : 0 < l) (hL : l ≤ L) :
    dyadicBlockEnd L l (2 * p + 1) = dyadicBlockEnd L (l - 1) p := by
  have hlevel : L - (l - 1) = (L - l) + 1 := by omega
  unfold dyadicBlockEnd
  rw [hlevel, Nat.pow_succ]
  have hcoef : 2 * p + 1 + 1 = 2 * (p + 1) := by omega
  rw [hcoef]
  ac_rfl

/-- Every natural index is one of the two children of its index at the
preceding dyadic level. -/
theorem nat_eq_two_mul_div_two_or_succ (m : ℕ) :
    m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1 := by
  have hdecomp := Nat.div_add_mod m 2
  have hmod := Nat.mod_lt m Nat.zero_lt_two
  omega

/-- Equal-level half-open dyadic blocks sharing an interior point have the
same index. -/
theorem dyadicBlockIndex_unique_of_contains_point
    {L l m n x : ℕ}
    (hmu : dyadicBlockStart L l m ≤ x)
    (hum : x < dyadicBlockEnd L l m)
    (hnu : dyadicBlockStart L l n ≤ x)
    (hun : x < dyadicBlockEnd L l n) : m = n := by
  unfold dyadicBlockStart dyadicBlockEnd at *
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hle : m + 1 ≤ n := Nat.succ_le_of_lt hmn
    have hprod := Nat.mul_le_mul_right (2 ^ (L - l)) hle
    have hbad : x < x := lt_of_lt_of_le hum (le_trans hprod hnu)
    exact False.elim (Nat.lt_irrefl x hbad)
  · exact hmn
  · have hle : n + 1 ≤ m := Nat.succ_le_of_lt hnm
    have hprod := Nat.mul_le_mul_right (2 ^ (L - l)) hle
    have hbad : x < x := lt_of_lt_of_le hun (le_trans hprod hmu)
    exact False.elim (Nat.lt_irrefl x hbad)

/-- Two aligned dyadic blocks at possibly different levels that contain the
same elementary cell are nested, with the coarser block containing the finer
one. -/
theorem dyadicBlock_nested_of_common_unit
    {L lc lf mc mf u : ℕ} (hlevels : lc ≤ lf) (hLf : lf ≤ L)
    (hmc : mc < 2 ^ lc) (hmf : mf < 2 ^ lf)
    (hcs : dyadicBlockStart L lc mc ≤ u)
    (hce : u + 1 ≤ dyadicBlockEnd L lc mc)
    (hfs : dyadicBlockStart L lf mf ≤ u)
    (hfe : u + 1 ≤ dyadicBlockEnd L lf mf) :
    dyadicBlockStart L lc mc ≤ dyadicBlockStart L lf mf ∧
      dyadicBlockEnd L lf mf ≤ dyadicBlockEnd L lc mc := by
  induction lf generalizing lc mc mf with
  | zero =>
      have hlevel : lc = 0 := by omega
      subst lc
      have hidx := dyadicBlockIndex_unique_of_contains_cell hcs hce hfs hfe
      subst mf
      exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
      by_cases hsame : lc = k + 1
      · subst lc
        have hidx := dyadicBlockIndex_unique_of_contains_cell hcs hce hfs hfe
        subst mf
        exact ⟨le_rfl, le_rfl⟩
      · have hlt : lc ≤ k := by omega
        have hparent := dyadicBlockParent_contains_child
          (Nat.succ_pos k) hLf hmf
        have hnested := ih hlt (Nat.le_trans (Nat.le_succ k) hLf) hmc
          hparent.1 hcs hce (le_trans hparent.2.1 hfs)
          (le_trans hfe hparent.2.2)
        exact ⟨le_trans hnested.1 hparent.2.1,
          le_trans hparent.2.2 hnested.2⟩

/-- A contained child whose parent crosses the left boundary must be the
right child; this makes the child unique once the parent is fixed. -/
theorem dyadicContainedIndex_eq_of_parent_eq_left
    {L a l m n : ℕ} (hl : 0 < l) (hL : l ≤ L)
    (hma : a ≤ dyadicBlockStart L l m)
    (hna : a ≤ dyadicBlockStart L l n)
    (hleftM : dyadicBlockStart L (l - 1) (m / 2) < a)
    (hleftN : dyadicBlockStart L (l - 1) (n / 2) < a)
    (hparent : m / 2 = n / 2) : m = n := by
  rcases nat_eq_two_mul_div_two_or_succ m with hmEven | hmOdd
  · rw [hmEven, dyadicBlockStart_even_eq_parent hl hL] at hma
    exact False.elim (Nat.not_lt_of_ge hma hleftM)
  · rcases nat_eq_two_mul_div_two_or_succ n with hnEven | hnOdd
    · rw [hnEven, dyadicBlockStart_even_eq_parent hl hL] at hna
      exact False.elim (Nat.not_lt_of_ge hna hleftN)
    · rw [hmOdd, hnOdd, hparent]

/-- A contained child whose parent crosses the right boundary must be the
left child; this makes the child unique once the parent is fixed. -/
theorem dyadicContainedIndex_eq_of_parent_eq_right
    {L b l m n : ℕ} (hl : 0 < l) (hL : l ≤ L)
    (hmb : dyadicBlockEnd L l m ≤ b)
    (hnb : dyadicBlockEnd L l n ≤ b)
    (hrightM : b < dyadicBlockEnd L (l - 1) (m / 2))
    (hrightN : b < dyadicBlockEnd L (l - 1) (n / 2))
    (hparent : m / 2 = n / 2) : m = n := by
  rcases nat_eq_two_mul_div_two_or_succ m with hmEven | hmOdd
  · rcases nat_eq_two_mul_div_two_or_succ n with hnEven | hnOdd
    · rw [hmEven, hnEven, hparent]
    · rw [hnOdd, dyadicBlockEnd_odd_eq_parent hl hL] at hnb
      exact False.elim (Nat.not_lt_of_ge hnb hrightN)
  · rw [hmOdd, dyadicBlockEnd_odd_eq_parent hl hL] at hmb
    exact False.elim (Nat.not_lt_of_ge hmb hrightM)

/-- The parent of a coarsest block selected for a unit cell cannot itself
remain inside the ambient interval. This is the maximality fact used in the
source's two-boundary count. -/
theorem dyadicCoarsest_parent_not_inside
    {L a b u l m : ℕ} (hl : 0 < l) (hL : l ≤ L) (hm : m < 2 ^ l)
    (hcellA : dyadicBlockStart L l m ≤ u)
    (hcellB : u + 1 ≤ dyadicBlockEnd L l m)
    (hmin : ∀ l' < l, ¬ ∃ m', m' < 2 ^ l' ∧
      a ≤ dyadicBlockStart L l' m' ∧ dyadicBlockEnd L l' m' ≤ b ∧
      dyadicBlockStart L l' m' ≤ u ∧ u + 1 ≤ dyadicBlockEnd L l' m') :
    ¬ (a ≤ dyadicBlockStart L (l - 1) (m / 2) ∧
      dyadicBlockEnd L (l - 1) (m / 2) ≤ b) := by
  intro hparentInside
  have hparent := dyadicBlockParent_contains_child hl hL hm
  have hprev : l - 1 < l := by omega
  exact hmin (l - 1) hprev ⟨m / 2, hparent.1, hparentInside.1,
    hparentInside.2, le_trans hparent.2.1 hcellA,
    le_trans hcellB hparent.2.2⟩

/-- A level-`l` aligned dyadic block lies inside `[a,b]` and contains the
elementary finest-grid interval `[u,u+1]`. -/
def DyadicCellCandidate (L a b u l : ℕ) : Prop :=
  l ≤ L ∧ ∃ m, m < 2 ^ l ∧
    a ≤ dyadicBlockStart L l m ∧
    dyadicBlockEnd L l m ≤ b ∧
    dyadicBlockStart L l m ≤ u ∧
    u + 1 ≤ dyadicBlockEnd L l m

/-- A standard dyadic block fully contained in the ambient integer interval. -/
def DyadicContainedBlock (L a b l m : ℕ) : Prop :=
  l ≤ L ∧ m < 2 ^ l ∧
    a ≤ dyadicBlockStart L l m ∧ dyadicBlockEnd L l m ≤ b

/-- A contained dyadic block is maximal if it is the root or its parent is
not contained in the ambient interval. -/
def DyadicMaximalBlock (L a b l m : ℕ) : Prop :=
  DyadicContainedBlock L a b l m ∧
    (l = 0 ∨ ¬ (a ≤ dyadicBlockStart L (l - 1) (m / 2) ∧
      dyadicBlockEnd L (l - 1) (m / 2) ≤ b))

/-- Every elementary interval in a finite dyadic-grid interval belongs to a
coarsest aligned dyadic block still contained in that interval. This is the
first covering step in the approved proof of `lm:chaining`; the level is
minimal among all aligned blocks containing the given elementary interval. -/
theorem exists_coarsest_dyadic_block_for_unit
    {L a b u : ℕ} (hb : b ≤ 2 ^ L) (hau : a ≤ u) (hub : u + 1 ≤ b) :
    ∃ l ≤ L, ∃ m, m < 2 ^ l ∧
      a ≤ dyadicBlockStart L l m ∧
      dyadicBlockEnd L l m ≤ b ∧
      dyadicBlockStart L l m ≤ u ∧
      u + 1 ≤ dyadicBlockEnd L l m ∧
      ∀ l' < l, ¬ ∃ m', m' < 2 ^ l' ∧
        a ≤ dyadicBlockStart L l' m' ∧
        dyadicBlockEnd L l' m' ≤ b ∧
        dyadicBlockStart L l' m' ≤ u ∧
        u + 1 ≤ dyadicBlockEnd L l' m' := by
  classical
  have hpow : u < 2 ^ L := by
    have hsucc : Nat.succ u ≤ 2 ^ L := by
      exact le_trans hub hb
    exact Nat.lt_of_succ_le hsucc
  have hCan : ∃ l, DyadicCellCandidate L a b u l := by
    refine ⟨L, Nat.le_refl _, u, hpow, ?_, ?_, ?_, ?_⟩
    · simpa [dyadicBlockStart] using hau
    · simpa [dyadicBlockEnd] using hub
    · simp [dyadicBlockStart]
    · simp [dyadicBlockEnd]
  let l := Nat.find hCan
  have hl : DyadicCellCandidate L a b u l := Nat.find_spec hCan
  rcases hl with ⟨hlL, m, hm, hstart, hend, hcellStart, hcellEnd⟩
  refine ⟨l, hlL, m, hm, hstart, hend, hcellStart, hcellEnd, ?_⟩
  intro l' hl' hex
  dsimp [l] at hl'
  have hnot : ¬ DyadicCellCandidate L a b u l' := Nat.find_min hCan hl'
  exact hnot ⟨Nat.le_trans (Nat.le_of_lt hl') hlL, hex⟩

/-- Every elementary cell in the ambient interval is contained in a maximal
standard dyadic block of that interval. -/
theorem exists_maximal_dyadic_block_for_unit
    {L a b u : ℕ} (hb : b ≤ 2 ^ L) (hau : a ≤ u) (hub : u + 1 ≤ b) :
    ∃ l m, DyadicMaximalBlock L a b l m ∧
      dyadicBlockStart L l m ≤ u ∧ u + 1 ≤ dyadicBlockEnd L l m := by
  obtain ⟨l, hlL, m, hm, hstart, hend, hcellStart, hcellEnd, hmin⟩ :=
    exists_coarsest_dyadic_block_for_unit hb hau hub
  have hmax : l = 0 ∨
      ¬ (a ≤ dyadicBlockStart L (l - 1) (m / 2) ∧
        dyadicBlockEnd L (l - 1) (m / 2) ≤ b) := by
    by_cases hlzero : l = 0
    · exact Or.inl hlzero
    · apply Or.inr
      exact dyadicCoarsest_parent_not_inside (Nat.pos_of_ne_zero hlzero)
        hlL hm hcellStart hcellEnd hmin
  exact ⟨l, m, ⟨⟨hlL, hm, hstart, hend⟩, hmax⟩, hcellStart, hcellEnd⟩

/-- The finite set of level-`l` maximal aligned blocks contained in `[a,b]`. -/
noncomputable def dyadicMaximalIndices (L a b l : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 ^ l)).filter (fun m => DyadicMaximalBlock L a b l m)

/-- At a fixed positive level, two contained maximal blocks whose parents
cross the left boundary must coincide. -/
theorem dyadicMaximalIndex_eq_of_left_parent_crossing
    {L a l m n : ℕ} (hl : 0 < l) (hL : l ≤ L)
    (hm : m < 2 ^ l) (hn : n < 2 ^ l)
    (hma : a ≤ dyadicBlockStart L l m)
    (hna : a ≤ dyadicBlockStart L l n)
    (hleftM : dyadicBlockStart L (l - 1) (m / 2) < a)
    (hleftN : dyadicBlockStart L (l - 1) (n / 2) < a) : m = n := by
  have hparentM := dyadicBlockParent_contains_child hl hL hm
  have hparentN := dyadicBlockParent_contains_child hl hL hn
  have hpositiveM : dyadicBlockStart L l m < dyadicBlockEnd L l m := by
    unfold dyadicBlockStart dyadicBlockEnd
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self m)
      (Nat.pow_pos (by decide : 0 < 2))
  have hpositiveN : dyadicBlockStart L l n < dyadicBlockEnd L l n := by
    unfold dyadicBlockStart dyadicBlockEnd
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self n)
      (Nat.pow_pos (by decide : 0 < 2))
  have hparentEndM : a < dyadicBlockEnd L (l - 1) (m / 2) :=
    lt_of_le_of_lt hma (lt_of_lt_of_le hpositiveM hparentM.2.2)
  have hparentEndN : a < dyadicBlockEnd L (l - 1) (n / 2) :=
    lt_of_le_of_lt hna (lt_of_lt_of_le hpositiveN hparentN.2.2)
  have hparentIndex := dyadicBlockIndex_unique_of_contains_point
    (Nat.le_of_lt hleftM) hparentEndM (Nat.le_of_lt hleftN) hparentEndN
  exact dyadicContainedIndex_eq_of_parent_eq_left hl hL hma hna
    hleftM hleftN hparentIndex

/-- At a fixed positive level, two contained maximal blocks whose parents
cross the right boundary must coincide. -/
theorem dyadicMaximalIndex_eq_of_right_parent_crossing
    {L b l m n : ℕ} (hl : 0 < l) (hL : l ≤ L)
    (hm : m < 2 ^ l) (hn : n < 2 ^ l)
    (hmb : dyadicBlockEnd L l m ≤ b)
    (hnb : dyadicBlockEnd L l n ≤ b)
    (hrightM : b < dyadicBlockEnd L (l - 1) (m / 2))
    (hrightN : b < dyadicBlockEnd L (l - 1) (n / 2)) : m = n := by
  have hparentM := dyadicBlockParent_contains_child hl hL hm
  have hparentN := dyadicBlockParent_contains_child hl hL hn
  have hpositiveM : dyadicBlockStart L l m < dyadicBlockEnd L l m := by
    unfold dyadicBlockStart dyadicBlockEnd
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self m)
      (Nat.pow_pos (by decide : 0 < 2))
  have hpositiveN : dyadicBlockStart L l n < dyadicBlockEnd L l n := by
    unfold dyadicBlockStart dyadicBlockEnd
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self n)
      (Nat.pow_pos (by decide : 0 < 2))
  have hparentStartM : dyadicBlockStart L (l - 1) (m / 2) < b :=
    lt_of_le_of_lt hparentM.2.1 (lt_of_lt_of_le hpositiveM hmb)
  have hparentStartN : dyadicBlockStart L (l - 1) (n / 2) < b :=
    lt_of_le_of_lt hparentN.2.1 (lt_of_lt_of_le hpositiveN hnb)
  have hparentIndex := dyadicBlockIndex_unique_of_contains_point
    (Nat.le_of_lt hparentStartM) hrightM
    (Nat.le_of_lt hparentStartN) hrightN
  exact dyadicContainedIndex_eq_of_parent_eq_right hl hL hmb hnb
    hrightM hrightN hparentIndex

/-- At each fixed level, there are at most two maximal aligned dyadic blocks
inside an integer interval. The two possibilities are the blocks meeting the
left or right boundary. -/
theorem dyadicMaximalIndices_card_le_two (L a b l : ℕ) :
    (dyadicMaximalIndices L a b l).card ≤ 2 := by
  classical
  by_cases hlzero : l = 0
  · have hsubset : dyadicMaximalIndices L a b l ⊆ Finset.range (2 ^ l) := by
      intro m hm
      change m ∈ (Finset.range (2 ^ l)).filter _ at hm
      exact (Finset.mem_filter.mp hm).1
    calc
      (dyadicMaximalIndices L a b l).card ≤ (Finset.range (2 ^ l)).card :=
        Finset.card_le_card hsubset
      _ = 1 := by simp [hlzero]
      _ ≤ 2 := by omega
  · have hl : 0 < l := Nat.pos_of_ne_zero hlzero
    let S := dyadicMaximalIndices L a b l
    let side : ℕ → Bool := fun m =>
      decide (dyadicBlockStart L (l - 1) (m / 2) < a)
    have hinj : (S : Set ℕ).InjOn side := by
      intro m hm n hn hside
      have hmMem : m ∈ S := hm
      have hnMem : n ∈ S := hn
      change m ∈ (Finset.range (2 ^ l)).filter _ at hmMem
      change n ∈ (Finset.range (2 ^ l)).filter _ at hnMem
      rcases Finset.mem_filter.mp hmMem with ⟨_, hmMax⟩
      rcases Finset.mem_filter.mp hnMem with ⟨_, hnMax⟩
      rcases hmMax with ⟨hmContained, hmMaximal⟩
      rcases hnMax with ⟨hnContained, hnMaximal⟩
      rcases hmContained with ⟨hL, hmBound, hma, hmb⟩
      rcases hnContained with ⟨_, hnBound, hna, hnb⟩
      have hnotParentM :
          ¬ (a ≤ dyadicBlockStart L (l - 1) (m / 2) ∧
            dyadicBlockEnd L (l - 1) (m / 2) ≤ b) := by
        rcases hmMaximal with hzero | hnot
        · exact (hlzero hzero).elim
        · exact hnot
      have hnotParentN :
          ¬ (a ≤ dyadicBlockStart L (l - 1) (n / 2) ∧
            dyadicBlockEnd L (l - 1) (n / 2) ≤ b) := by
        rcases hnMaximal with hzero | hnot
        · exact (hlzero hzero).elim
        · exact hnot
      dsimp [side] at hside
      by_cases hleftM : dyadicBlockStart L (l - 1) (m / 2) < a
      · by_cases hleftN : dyadicBlockStart L (l - 1) (n / 2) < a
        · exact dyadicMaximalIndex_eq_of_left_parent_crossing hl hL
            hmBound hnBound hma hna hleftM hleftN
        · have hsideM :
              decide (dyadicBlockStart L (l - 1) (m / 2) < a) = true := by
            simp [hleftM]
          have hsideN :
              decide (dyadicBlockStart L (l - 1) (n / 2) < a) = false :=
            decide_eq_false_iff_not.mpr hleftN
          rw [hsideM, hsideN] at hside
          cases hside
      · by_cases hleftN : dyadicBlockStart L (l - 1) (n / 2) < a
        · have hsideM :
              decide (dyadicBlockStart L (l - 1) (m / 2) < a) = false :=
            decide_eq_false_iff_not.mpr hleftM
          have hsideN :
              decide (dyadicBlockStart L (l - 1) (n / 2) < a) = true := by
            simp [hleftN]
          rw [hsideM, hsideN] at hside
          cases hside
        · have hparentMEnd : b < dyadicBlockEnd L (l - 1) (m / 2) := by
            have hpa : a ≤ dyadicBlockStart L (l - 1) (m / 2) :=
              Nat.le_of_not_gt hleftM
            by_contra h
            exact hnotParentM ⟨hpa, Nat.le_of_not_gt h⟩
          have hparentNEnd : b < dyadicBlockEnd L (l - 1) (n / 2) := by
            have hpa : a ≤ dyadicBlockStart L (l - 1) (n / 2) :=
              Nat.le_of_not_gt hleftN
            by_contra h
            exact hnotParentN ⟨hpa, Nat.le_of_not_gt h⟩
          exact dyadicMaximalIndex_eq_of_right_parent_crossing hl hL
            hmBound hnBound hmb hnb hparentMEnd hparentNEnd
    have hmap : Set.MapsTo side (S : Set ℕ)
        (↑(Finset.univ : Finset Bool) : Set Bool) := by
      intro m hm
      simp
    have hcard : S.card ≤ Finset.univ.card :=
      Finset.card_le_card_of_injOn side hmap hinj
    calc
      (dyadicMaximalIndices L a b l).card = S.card := by rfl
      _ ≤ Finset.univ.card := hcard
      _ = 2 := by decide

/-- A coarser contained dyadic block and a strictly finer contained block
cannot both be maximal if they contain the same elementary cell. -/
theorem dyadicMaximal_no_strictly_finer_common_unit
    {L a b u lc lf mc mf : ℕ}
    (hlf : lf ≤ L)
    (hmc : mc < 2 ^ lc) (hmf : mf < 2 ^ lf)
    (hcs : dyadicBlockStart L lc mc ≤ u)
    (hce : u + 1 ≤ dyadicBlockEnd L lc mc)
    (hfs : dyadicBlockStart L lf mf ≤ u)
    (hfe : u + 1 ≤ dyadicBlockEnd L lf mf)
    (hmaxC : DyadicMaximalBlock L a b lc mc)
    (hmaxF : DyadicMaximalBlock L a b lf mf)
    (hlt : lc < lf) : False := by
  rcases hmaxC with ⟨hcontainedC, _⟩
  rcases hcontainedC with ⟨_, _, haC, hbC⟩
  rcases hmaxF with ⟨hcontainedF, hmaxF⟩
  rcases hcontainedF with ⟨_, _, _, _⟩
  have hlfpos : 0 < lf := lt_of_le_of_lt (Nat.zero_le lc) hlt
  have hparent := dyadicBlockParent_contains_child hlfpos hlf hmf
  have hnest := dyadicBlock_nested_of_common_unit
    (by omega : lc ≤ lf - 1) (by omega : lf - 1 ≤ L) hmc hparent.1
    hcs hce (le_trans hparent.2.1 hfs) (le_trans hfe hparent.2.2)
  have hnotParent :
      ¬ (a ≤ dyadicBlockStart L (lf - 1) (mf / 2) ∧
        dyadicBlockEnd L (lf - 1) (mf / 2) ≤ b) := by
    rcases hmaxF with hroot | hnot
    · omega
    · exact hnot
  exact hnotParent ⟨le_trans haC hnest.1, le_trans hnest.2 hbC⟩

/-- A unit cell can belong to only one maximal contained dyadic block. -/
theorem dyadicMaximalBlock_eq_of_common_unit
    {L a b u l₁ l₂ m₁ m₂ : ℕ}
    (hmax₁ : DyadicMaximalBlock L a b l₁ m₁)
    (hmax₂ : DyadicMaximalBlock L a b l₂ m₂)
    (hcell₁ : dyadicBlockStart L l₁ m₁ ≤ u ∧
      u + 1 ≤ dyadicBlockEnd L l₁ m₁)
    (hcell₂ : dyadicBlockStart L l₂ m₂ ≤ u ∧
      u + 1 ≤ dyadicBlockEnd L l₂ m₂) : l₁ = l₂ ∧ m₁ = m₂ := by
  have hmax1copy := hmax₁
  have hmax2copy := hmax₂
  rcases hmax₁ with ⟨hcontained₁, _⟩
  rcases hmax₂ with ⟨hcontained₂, _⟩
  rcases hcontained₁ with ⟨hl₁, hm₁, _, _⟩
  rcases hcontained₂ with ⟨hl₂, hm₂, _, _⟩
  rcases le_total l₁ l₂ with hle | hle
  · rcases eq_or_lt_of_le hle with heq | hlt
    · subst l₂
      have hidx := dyadicBlockIndex_unique_of_contains_cell
        hcell₁.1 hcell₁.2 hcell₂.1 hcell₂.2
      exact ⟨rfl, hidx⟩
    · exact False.elim (dyadicMaximal_no_strictly_finer_common_unit
        hl₂ hm₁ hm₂ hcell₁.1 hcell₁.2 hcell₂.1 hcell₂.2
        hmax1copy hmax2copy hlt)
  · rcases eq_or_lt_of_le hle with heq | hlt
    · subst l₁
      have hidx := dyadicBlockIndex_unique_of_contains_cell
        hcell₁.1 hcell₁.2 hcell₂.1 hcell₂.2
      exact ⟨rfl, hidx⟩
    · exact False.elim (dyadicMaximal_no_strictly_finer_common_unit
        hl₁ hm₂ hm₁ hcell₂.1 hcell₂.2 hcell₁.1 hcell₁.2
        hmax2copy hmax1copy hlt)

/-- Every standard dyadic block has positive integer length. -/
theorem dyadicBlockStart_lt_end (L l m : ℕ) :
    dyadicBlockStart L l m < dyadicBlockEnd L l m := by
  unfold dyadicBlockStart dyadicBlockEnd
  exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self m)
    (Nat.pow_pos (by decide : 0 < 2))

/-- Two maximal contained blocks whose interiors overlap are identical. Thus
distinct maximal blocks have disjoint interiors. -/
theorem dyadicMaximalBlocks_overlap_eq
    {L a b l₁ l₂ m₁ m₂ : ℕ}
    (hmax₁ : DyadicMaximalBlock L a b l₁ m₁)
    (hmax₂ : DyadicMaximalBlock L a b l₂ m₂)
    (hoverlap₁ : dyadicBlockStart L l₁ m₁ < dyadicBlockEnd L l₂ m₂)
    (hoverlap₂ : dyadicBlockStart L l₂ m₂ < dyadicBlockEnd L l₁ m₁) :
    l₁ = l₂ ∧ m₁ = m₂ := by
  by_cases hstart : dyadicBlockStart L l₁ m₁ ≤ dyadicBlockStart L l₂ m₂
  · exact dyadicMaximalBlock_eq_of_common_unit hmax₁ hmax₂
      ⟨hstart, Nat.succ_le_of_lt hoverlap₂⟩
      ⟨le_rfl, Nat.succ_le_of_lt (dyadicBlockStart_lt_end L l₂ m₂)⟩
  · have hstart' : dyadicBlockStart L l₂ m₂ ≤ dyadicBlockStart L l₁ m₁ :=
      Nat.le_of_lt (lt_of_not_ge hstart)
    exact dyadicMaximalBlock_eq_of_common_unit hmax₁ hmax₂
      ⟨le_rfl, Nat.succ_le_of_lt (dyadicBlockStart_lt_end L l₁ m₁)⟩
      ⟨hstart', Nat.succ_le_of_lt hoverlap₁⟩

/-- The finite family of all maximal standard dyadic blocks in `[a,b]`. -/
noncomputable def dyadicMaximalBlocks (L a b : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (L + 1)).product (Finset.range (2 ^ (L + 1)))).filter
    (fun p => DyadicMaximalBlock L a b p.1 p.2)

/-- A pair in the finite maximal-block family satisfies the maximal-block
contract. -/
theorem dyadicMaximalBlock_of_mem
    {L a b : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ dyadicMaximalBlocks L a b) :
    DyadicMaximalBlock L a b p.1 p.2 := by
  classical
  rw [dyadicMaximalBlocks, Finset.mem_filter] at hp
  exact hp.2

/-- Every maximal block occurs in the finite family. -/
theorem mem_dyadicMaximalBlocks
    {L a b l m : ℕ} (hmax : DyadicMaximalBlock L a b l m) :
    (l, m) ∈ dyadicMaximalBlocks L a b := by
  classical
  have hcontain := hmax.1
  rcases hcontain with ⟨hl, hm, _, _⟩
  have hlRange : l ∈ Finset.range (L + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hl)
  have hmRange : m ∈ Finset.range (2 ^ (L + 1)) := by
    apply Finset.mem_range.mpr
    exact lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.le_trans hl (Nat.le_succ L)))
  rw [dyadicMaximalBlocks, Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr ⟨hlRange, hmRange⟩, hmax⟩

/-- Every unit cell of an ambient interval is covered by a member of the
finite maximal-block family. -/
theorem exists_dyadicMaximalBlocks_covering_unit
    {L a b u : ℕ} (hb : b ≤ 2 ^ L) (hau : a ≤ u) (hub : u + 1 ≤ b) :
    ∃ p ∈ dyadicMaximalBlocks L a b,
      dyadicBlockStart L p.1 p.2 ≤ u ∧ u + 1 ≤ dyadicBlockEnd L p.1 p.2 := by
  obtain ⟨l, m, hmax, hstart, hend⟩ :=
    exists_maximal_dyadic_block_for_unit hb hau hub
  exact ⟨(l, m), mem_dyadicMaximalBlocks hmax, hstart, hend⟩

/-- Each unit cell of an ambient interval belongs to exactly one member of
the finite maximal-block family. -/
theorem existsUnique_dyadicMaximalBlocks_covering_unit
    {L a b u : ℕ} (hb : b ≤ 2 ^ L) (hau : a ≤ u) (hub : u + 1 ≤ b) :
    ∃! p, p ∈ dyadicMaximalBlocks L a b ∧
      dyadicBlockStart L p.1 p.2 ≤ u ∧ u + 1 ≤ dyadicBlockEnd L p.1 p.2 := by
  obtain ⟨p, hp, hstart, hend⟩ :=
    exists_dyadicMaximalBlocks_covering_unit hb hau hub
  refine ⟨p, ⟨hp, hstart, hend⟩, ?_⟩
  intro q hq
  rcases q with ⟨l, m⟩
  rcases hq with ⟨hqmem, hqstart, hqend⟩
  have hpmax := dyadicMaximalBlock_of_mem hp
  have hqmax := dyadicMaximalBlock_of_mem hqmem
  obtain ⟨heqL, heqM⟩ := dyadicMaximalBlock_eq_of_common_unit hpmax hqmax
    ⟨hstart, hend⟩ ⟨hqstart, hqend⟩
  cases heqL
  cases heqM
  rfl

/-- Telescoping over the finest-grid cells of one dyadic block gives its
endpoint increment. -/
theorem dyadicBlock_increment_eq_cell_sum
    {A : Type*} [AddCommGroup A] (g : ℕ → A) (L l m : ℕ) :
    g (dyadicBlockEnd L l m) - g (dyadicBlockStart L l m) =
      ∑ u ∈ Finset.Ico (dyadicBlockStart L l m) (dyadicBlockEnd L l m),
        (g (u + 1) - g u) := by
  have hle : dyadicBlockStart L l m ≤ dyadicBlockEnd L l m :=
    le_of_lt (dyadicBlockStart_lt_end L l m)
  rw [Finset.sum_Ico_eq_sub _ hle, Finset.sum_range_sub, Finset.sum_range_sub]
  simp only [sub_sub_sub_cancel_right]

/-- Summing the increments over all maximal blocks in an interval gives the
full endpoint increment. The proof uses the checked unique cell partition. -/
theorem dyadicMaximalBlocks_increment_sum_eq
    {A : Type*} [AddCommGroup A] (g : ℕ → A)
    {L a b : ℕ} (hb : b ≤ 2 ^ L) (hab : a ≤ b) :
    (∑ p ∈ dyadicMaximalBlocks L a b,
      (g (dyadicBlockEnd L p.1 p.2) - g (dyadicBlockStart L p.1 p.2))) =
      g b - g a := by
  classical
  let blocks := dyadicMaximalBlocks L a b
  let cells (p : ℕ × ℕ) :=
    Finset.Ico (dyadicBlockStart L p.1 p.2) (dyadicBlockEnd L p.1 p.2)
  have hcover : Finset.Ico a b = blocks.biUnion cells := by
    ext u
    constructor
    · intro hu
      rcases Finset.mem_Ico.mp hu with ⟨hau, hub⟩
      obtain ⟨p, hp, hstart, hend⟩ :=
        exists_dyadicMaximalBlocks_covering_unit hb hau (Nat.succ_le_of_lt hub)
      apply Finset.mem_biUnion.mpr
      refine ⟨p, ?_, ?_⟩
      · exact hp
      · exact Finset.mem_Ico.mpr ⟨hstart, Nat.lt_of_succ_le hend⟩
    · intro hu
      rcases Finset.mem_biUnion.mp hu with ⟨p, hp, hpu⟩
      have hmax := dyadicMaximalBlock_of_mem hp
      rcases hmax.1 with ⟨_, _, hblockStart, hblockEnd⟩
      rcases Finset.mem_Ico.mp hpu with ⟨hstart, hend⟩
      exact Finset.mem_Ico.mpr ⟨le_trans hblockStart hstart,
        lt_of_lt_of_le hend hblockEnd⟩
  have hdisj : Set.PairwiseDisjoint (↑blocks : Set (ℕ × ℕ)) cells := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro u hpu hqu
    have hmaxP := dyadicMaximalBlock_of_mem hp
    have hmaxQ := dyadicMaximalBlock_of_mem hq
    rcases Finset.mem_Ico.mp hpu with ⟨hpStart, hpEnd⟩
    rcases Finset.mem_Ico.mp hqu with ⟨hqStart, hqEnd⟩
    obtain ⟨hl, hm⟩ := dyadicMaximalBlock_eq_of_common_unit hmaxP hmaxQ
      ⟨hpStart, Nat.succ_le_of_lt hpEnd⟩ ⟨hqStart, Nat.succ_le_of_lt hqEnd⟩
    exact hpq (Prod.ext hl hm)
  calc
    (∑ p ∈ blocks,
      (g (dyadicBlockEnd L p.1 p.2) - g (dyadicBlockStart L p.1 p.2))) =
        ∑ p ∈ blocks, ∑ u ∈ cells p, (g (u + 1) - g u) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact dyadicBlock_increment_eq_cell_sum g L p.1 p.2
    _ = ∑ u ∈ blocks.biUnion cells, (g (u + 1) - g u) :=
      (Finset.sum_biUnion hdisj).symm
    _ = ∑ u ∈ Finset.Ico a b, (g (u + 1) - g u) := by rw [← hcover]
    _ = g b - g a := by
      rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub, Finset.sum_range_sub]
      simp only [sub_sub_sub_cancel_right]

/-- Reindex the finite maximal-block sum by level and then block index. -/
theorem dyadicMaximalBlocks_sum_eq_levelwise
    {A : Type*} [AddCommMonoid A] {L a b : ℕ} (f : ℕ × ℕ → A) :
    (∑ p ∈ dyadicMaximalBlocks L a b, f p) =
      ∑ l ∈ Finset.range (L + 1),
        ∑ m ∈ dyadicMaximalIndices L a b l, f (l, m) := by
  classical
  have hselected (l : ℕ) (hl : l ∈ Finset.range (L + 1)) :
      (Finset.range (2 ^ (L + 1))).filter
        (fun m => DyadicMaximalBlock L a b l m) =
          dyadicMaximalIndices L a b l := by
    have hlL : l ≤ L := by
      have := Finset.mem_range.mp hl
      omega
    ext m
    rw [dyadicMaximalIndices]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hm, hmax⟩
      rcases hmax.1 with ⟨_, hmbound, _, _⟩
      exact ⟨hmbound, hmax⟩
    · rintro ⟨hm, hmax⟩
      refine ⟨lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide : 0 < 2) ?_), hmax⟩
      exact Nat.le_trans hlL (Nat.le_succ L)
  calc
    (∑ p ∈ dyadicMaximalBlocks L a b, f p) =
        ∑ l ∈ Finset.range (L + 1),
          ∑ m ∈ Finset.range (2 ^ (L + 1)),
            if DyadicMaximalBlock L a b l m then f (l, m) else 0 := by
      rw [dyadicMaximalBlocks, Finset.sum_filter]
      exact Finset.sum_product'
        (Finset.range (L + 1)) (Finset.range (2 ^ (L + 1)))
        (fun l m => if DyadicMaximalBlock L a b l m then f (l, m) else 0)
    _ = ∑ l ∈ Finset.range (L + 1),
          ∑ m ∈ dyadicMaximalIndices L a b l, f (l, m) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [← Finset.sum_filter, ← hselected l hl]

/-- The interval endpoint increment also telescopes when maximal blocks are
grouped by their dyadic levels. -/
theorem dyadicMaximalBlocks_increment_sum_eq_levelwise
    {A : Type*} [AddCommGroup A] (g : ℕ → A)
    {L a b : ℕ} (hb : b ≤ 2 ^ L) (hab : a ≤ b) :
    (∑ l ∈ Finset.range (L + 1),
      ∑ m ∈ dyadicMaximalIndices L a b l,
        (g (dyadicBlockEnd L l m) - g (dyadicBlockStart L l m))) =
      g b - g a := by
  calc
    (∑ l ∈ Finset.range (L + 1),
      ∑ m ∈ dyadicMaximalIndices L a b l,
        (g (dyadicBlockEnd L l m) - g (dyadicBlockStart L l m))) =
      ∑ p ∈ dyadicMaximalBlocks L a b,
        (g (dyadicBlockEnd L p.1 p.2) - g (dyadicBlockStart L p.1 p.2)) :=
      (dyadicMaximalBlocks_sum_eq_levelwise
        (f := fun p =>
          g (dyadicBlockEnd L p.1 p.2) - g (dyadicBlockStart L p.1 p.2))).symm
    _ = g b - g a := dyadicMaximalBlocks_increment_sum_eq g hb hab

/-- At a fixed dyadic level, blocks selected inside distinct edges of a
strict finite chain are disjoint. A common index would give a positive-length
block contained in two disjoint consecutive chain intervals. -/
theorem dyadicMaximalIndices_pairwiseDisjoint_of_strictChain
    {N L : ℕ} (u : Fin (N + 1) → ℕ) (hu : StrictMono u) (l : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)) : Set (Fin N))
      (fun i => dyadicMaximalIndices L (u i.castSucc) (u i.succ) l) := by
  classical
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro m him hjm
  change m ∈ (Finset.range (2 ^ l)).filter _ at him
  change m ∈ (Finset.range (2 ^ l)).filter _ at hjm
  have hmaxI := (Finset.mem_filter.mp him).2
  have hmaxJ := (Finset.mem_filter.mp hjm).2
  rcases hmaxI.1 with ⟨_, _, hiStart, hiEnd⟩
  rcases hmaxJ.1 with ⟨_, _, hjStart, hjEnd⟩
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hindex : i.succ ≤ j.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      simpa only [Fin.val_succ, Fin.val_castSucc] using
        Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hij')
    have horder : u i.succ ≤ u j.castSucc := hu.monotone hindex
    have hcontra : dyadicBlockStart L l m < dyadicBlockStart L l m :=
      lt_of_lt_of_le (dyadicBlockStart_lt_end L l m)
        (le_trans hiEnd (le_trans horder hjStart))
    exact (lt_irrefl _ hcontra)
  · have hindex : j.succ ≤ i.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      simpa only [Fin.val_succ, Fin.val_castSucc] using
        Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hji')
    have horder : u j.succ ≤ u i.castSucc := hu.monotone hindex
    have hcontra : dyadicBlockStart L l m < dyadicBlockStart L l m :=
      lt_of_lt_of_le (dyadicBlockStart_lt_end L l m)
        (le_trans hjEnd (le_trans horder hiStart))
    exact (lt_irrefl _ hcontra)

/-- At one fixed dyadic level, if each chain interval uses at most two
increments and no increment is used by two chain intervals, then the sum of
the squared norms of the interval contributions is at most twice the squared
norm sum over the selected increments. This is the levelwise Cauchy--Schwarz
step in the approved proof of `lm:chaining`. -/
theorem dyadicFiniteLevelEnergy_le_two
    {ι κ E : Type*} [DecidableEq ι] [DecidableEq κ]
    [SeminormedAddCommGroup E]
    (edges : Finset ι) (selected : ι → Finset κ) (increment : κ → E)
    (hcard : ∀ i ∈ edges, (selected i).card ≤ 2)
    (hdisj : Set.PairwiseDisjoint (↑edges : Set ι) selected) :
    (∑ i ∈ edges, ‖∑ k ∈ selected i, increment k‖ ^ 2) ≤
      2 * ∑ k ∈ edges.biUnion selected, ‖increment k‖ ^ 2 := by
  classical
  have hterm : ∀ i ∈ edges,
      ‖∑ k ∈ selected i, increment k‖ ^ 2 ≤
        2 * ∑ k ∈ selected i, ‖increment k‖ ^ 2 := by
    intro i hi
    have hnorm : ‖∑ k ∈ selected i, increment k‖ ≤
        ∑ k ∈ selected i, ‖increment k‖ := norm_sum_le _ _
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (selected i)
      (fun _ => (1 : ℝ)) (fun k => ‖increment k‖)
    have hcs' : (∑ k ∈ selected i, ‖increment k‖) ^ 2 ≤
        (selected i).card * ∑ k ∈ selected i, ‖increment k‖ ^ 2 := by
      simpa using hcs
    have hcardR : ((selected i).card : ℝ) ≤ 2 := by
      exact_mod_cast hcard i hi
    have hnorm_nonneg : 0 ≤ ‖∑ k ∈ selected i, increment k‖ := norm_nonneg _
    have hsum_nonneg : 0 ≤ ∑ k ∈ selected i, ‖increment k‖ :=
      Finset.sum_nonneg fun k hk => norm_nonneg _
    have hsumSq_nonneg : 0 ≤ ∑ k ∈ selected i, ‖increment k‖ ^ 2 :=
      Finset.sum_nonneg fun k hk => sq_nonneg _
    calc
      ‖∑ k ∈ selected i, increment k‖ ^ 2 ≤
          (∑ k ∈ selected i, ‖increment k‖) ^ 2 := by nlinarith
      _ ≤ (selected i).card * ∑ k ∈ selected i, ‖increment k‖ ^ 2 := hcs'
      _ ≤ 2 * ∑ k ∈ selected i, ‖increment k‖ ^ 2 := by nlinarith
  calc
    (∑ i ∈ edges, ‖∑ k ∈ selected i, increment k‖ ^ 2) ≤
        ∑ i ∈ edges, 2 * ∑ k ∈ selected i, ‖increment k‖ ^ 2 := by
      exact Finset.sum_le_sum fun i hi => hterm i hi
    _ = 2 * ∑ i ∈ edges, ∑ k ∈ selected i, ‖increment k‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = 2 * ∑ k ∈ edges.biUnion selected, ‖increment k‖ ^ 2 := by
      rw [Finset.sum_biUnion hdisj]

/-- Finite-chain aggregation of dyadic levels. If each chain increment is
the sum of its selected block increments, each edge selects at most two
blocks at a level, and no block is selected for two edges, then the chain
ℓ² norm is at most `sqrt 2` times the sum of the full level ℓ² norms. This is
the algebraic Minkowski/Cauchy--Schwarz assembly in `lm:chaining`; the dyadic
interval lemmas above supply its hypotheses in the concrete application. -/
theorem dyadicFiniteChain_incrementNorm_le_sqrtTwo_sumLevelNorms
    {ι Level κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq Level] [DecidableEq κ]
    (levels : Finset Level) (selected : Level → ι → Finset κ)
    (blockIncrement : Level → κ → ℂ) (increment : ι → ℂ)
    (allIndices : Level → Finset κ)
    (htelescope : ∀ i, increment i =
      ∑ l ∈ levels, ∑ k ∈ selected l i, blockIncrement l k)
    (hcard : ∀ l ∈ levels, ∀ i, (selected l i).card ≤ 2)
    (hdisj : ∀ l ∈ levels,
      Set.PairwiseDisjoint (↑(Finset.univ : Finset ι) : Set ι) (selected l))
    (hsubset : ∀ l ∈ levels,
      (Finset.univ : Finset ι).biUnion (selected l) ⊆ allIndices l) :
    Real.sqrt (∑ i, ‖increment i‖ ^ 2) ≤
      Real.sqrt 2 * ∑ l ∈ levels,
        Real.sqrt (∑ k ∈ allIndices l, ‖blockIncrement l k‖ ^ 2) := by
  let levelContribution : Level → ι → ℂ := fun l i =>
    ∑ k ∈ selected l i, blockIncrement l k
  have hminkowski :
      Real.sqrt (∑ i, ‖∑ l ∈ levels, levelContribution l i‖ ^ 2) ≤
        ∑ l ∈ levels, Real.sqrt (∑ i, ‖levelContribution l i‖ ^ 2) := by
    calc
      Real.sqrt (∑ i, ‖∑ l ∈ levels, levelContribution l i‖ ^ 2) =
          ‖(WithLp.toLp 2 (fun i => ∑ l ∈ levels, levelContribution l i) :
            EuclideanSpace ℂ ι)‖ := by
        rw [EuclideanSpace.norm_eq]
      _ = ‖∑ l ∈ levels,
          (WithLp.toLp 2 (levelContribution l) : EuclideanSpace ℂ ι)‖ := by
        congr 1
        ext i
        simp
      _ ≤ ∑ l ∈ levels,
          ‖(WithLp.toLp 2 (levelContribution l) : EuclideanSpace ℂ ι)‖ :=
        norm_sum_le _ _
      _ = ∑ l ∈ levels,
          Real.sqrt (∑ i, ‖levelContribution l i‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [EuclideanSpace.norm_eq]
  have hlevel : ∀ l ∈ levels,
      Real.sqrt (∑ i, ‖levelContribution l i‖ ^ 2) ≤
        Real.sqrt 2 * Real.sqrt (∑ k ∈ allIndices l, ‖blockIncrement l k‖ ^ 2) := by
    intro l hl
    have henergy := dyadicFiniteLevelEnergy_le_two
      (edges := (Finset.univ : Finset ι)) (selected := selected l)
      (increment := blockIncrement l)
      (fun i hi => hcard l hl i) (hdisj l hl)
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg (hsubset l hl)
      (fun k hk hnot => sq_nonneg ‖blockIncrement l k‖)
    have htotal : (∑ i, ‖levelContribution l i‖ ^ 2) ≤
        2 * ∑ k ∈ allIndices l, ‖blockIncrement l k‖ ^ 2 := by
      dsimp [levelContribution]
      exact henergy.trans (by nlinarith)
    calc
      Real.sqrt (∑ i, ‖levelContribution l i‖ ^ 2) ≤
          Real.sqrt (2 * ∑ k ∈ allIndices l, ‖blockIncrement l k‖ ^ 2) :=
        Real.sqrt_le_sqrt htotal
      _ = Real.sqrt 2 *
          Real.sqrt (∑ k ∈ allIndices l, ‖blockIncrement l k‖ ^ 2) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Real.sqrt (∑ i, ‖increment i‖ ^ 2) =
        Real.sqrt (∑ i, ‖∑ l ∈ levels, levelContribution l i‖ ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← htelescope i]
    _ ≤ ∑ l ∈ levels, Real.sqrt (∑ i, ‖levelContribution l i‖ ^ 2) := hminkowski
    _ ≤ ∑ l ∈ levels,
        Real.sqrt 2 * Real.sqrt (∑ k ∈ allIndices l, ‖blockIncrement l k‖ ^ 2) := by
      exact Finset.sum_le_sum fun l hl => hlevel l hl
    _ = Real.sqrt 2 * ∑ l ∈ levels,
        Real.sqrt (∑ k ∈ allIndices l, ‖blockIncrement l k‖ ^ 2) := by
      rw [Finset.mul_sum]

/-- The dyadic chaining estimate for one strict finite chain of integer grid
indices. The right side is the sum of the complete dyadic level energies;
this is the finite-grid statement after writing each time as its integer
index in the depth-`L` grid. -/
theorem dyadicFiniteChain_incrementNorm_le_gridSquareSums
    {N L : ℕ} (u : Fin (N + 1) → ℕ) (hu : StrictMono u)
    (hbound : ∀ i, u i ≤ 2 ^ L) (g : ℕ → ℂ) :
    Real.sqrt (∑ i : Fin N,
      ‖g (u i.succ) - g (u i.castSucc)‖ ^ 2) ≤
      Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖g (dyadicBlockEnd L l m) - g (dyadicBlockStart L l m)‖ ^ 2) := by
  classical
  apply dyadicFiniteChain_incrementNorm_le_sqrtTwo_sumLevelNorms
    (ι := Fin N) (Level := ℕ) (κ := ℕ)
    (levels := Finset.range (L + 1))
    (selected := fun l i =>
      dyadicMaximalIndices L (u i.castSucc) (u i.succ) l)
    (blockIncrement := fun l m =>
      g (dyadicBlockEnd L l m) - g (dyadicBlockStart L l m))
    (increment := fun i => g (u i.succ) - g (u i.castSucc))
    (allIndices := fun l => Finset.range (2 ^ l))
  · intro i
    exact (dyadicMaximalBlocks_increment_sum_eq_levelwise g (hbound i.succ)
      (le_of_lt (hu Fin.castSucc_lt_succ))).symm
  · intro l hl i
    exact dyadicMaximalIndices_card_le_two L (u i.castSucc) (u i.succ) l
  · intro l hl
    exact dyadicMaximalIndices_pairwiseDisjoint_of_strictChain u hu l
  · intro l hl m hm
    rcases Finset.mem_biUnion.mp hm with ⟨i, hi, him⟩
    change m ∈ (Finset.range (2 ^ l)).filter _ at him
    exact (Finset.mem_filter.mp him).1

/-- The depth-`L` dyadic grid point with integer index `m`, so that the grid
is exactly the set of these values for `0 ≤ m ≤ 2^L`. -/
def dyadicGridPoint (L m : ℕ) : ℚ := (m : ℚ) / (2 ^ L : ℚ)

/-- The time set `G_L = {m 2^{-L} : 0 ≤ m ≤ 2^L}` from `lm:spaces`. -/
def dyadicGridTimes (L : ℕ) : Set ℚ :=
  {t | ∃ m, m ≤ 2 ^ L ∧ dyadicGridPoint L m = t}

/-- A level-`l` block's left endpoint is its level-`l` grid point. -/
theorem dyadicGridPoint_blockStart {L l m : ℕ} (hl : l ≤ L) :
    dyadicGridPoint L (dyadicBlockStart L l m) = (m : ℚ) / (2 ^ l : ℚ) := by
  unfold dyadicGridPoint dyadicBlockStart
  have hpowNat : 2 ^ l * 2 ^ (L - l) = 2 ^ L := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hl]
  have hpow : (2 : ℚ) ^ l * (2 : ℚ) ^ (L - l) = (2 : ℚ) ^ L := by
    exact_mod_cast hpowNat
  push_cast
  rw [← hpow]
  field_simp

/-- A level-`l` block's right endpoint is its next level-`l` grid point. -/
theorem dyadicGridPoint_blockEnd {L l m : ℕ} (hl : l ≤ L) :
    dyadicGridPoint L (dyadicBlockEnd L l m) =
      ((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ) := by
  unfold dyadicGridPoint dyadicBlockEnd
  have hpowNat : 2 ^ l * 2 ^ (L - l) = 2 ^ L := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hl]
  have hpow : (2 : ℚ) ^ l * (2 : ℚ) ^ (L - l) = (2 : ℚ) ^ L := by
    exact_mod_cast hpowNat
  push_cast
  rw [← hpow]
  field_simp

/-- Each left endpoint of a level-`l` interval lies in the depth-`L` grid. -/
theorem dyadicGridTimes_levelPoint_mem {L l m : ℕ}
    (hl : l ≤ L) (hm : m < 2 ^ l) :
    (m : ℚ) / (2 ^ l : ℚ) ∈ dyadicGridTimes L := by
  rw [← dyadicGridPoint_blockStart hl]
  refine ⟨dyadicBlockStart L l m, ?_, rfl⟩
  exact le_trans (Nat.le_of_lt (dyadicBlockStart_lt_end L l m))
    (dyadicBlockEnd_le_grid_end hl hm)

/-- Each right endpoint of a level-`l` interval lies in the depth-`L` grid. -/
theorem dyadicGridTimes_levelSuccessor_mem {L l m : ℕ}
    (hl : l ≤ L) (hm : m < 2 ^ l) :
    ((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ) ∈ dyadicGridTimes L := by
  rw [← dyadicGridPoint_blockEnd hl]
  exact ⟨dyadicBlockEnd L l m, dyadicBlockEnd_le_grid_end hl hm, rfl⟩

/-- The homogeneous 2-variation on `G_L`, encoded by the canonical strictly
increasing integer indices `0,…,2^L`. The associated times are
`dyadicGridPoint L m = m 2^{-L}`; thus each admissible index chain is exactly
a finite chain in the grid from the statement of `lm:chaining`. -/
noncomputable def dyadicGridVariationTwoIndex (L : ℕ) (g : ℚ → ℂ) : ENNReal :=
  ⨆ N : ℕ, ⨆ u : Fin (N + 1) → ℕ,
    if h : 0 < N ∧ StrictMono u ∧ ∀ i, u i ≤ 2 ^ L then
      ENNReal.ofReal (Real.sqrt (∑ i : Fin N,
        ‖g (dyadicGridPoint L (u i.succ)) -
          g (dyadicGridPoint L (u i.castSucc))‖ ^ 2))
    else 0

/-- The finite-grid dyadic chaining estimate, with the variation expressed
as the exact supremum over finite chains in `G_L`. -/
theorem dyadicGridVariationTwoIndex_le
    (L : ℕ) (g : ℚ → ℂ) :
    dyadicGridVariationTwoIndex L g ≤
      ENNReal.ofReal (Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖g (((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ)) -
            g ((m : ℚ) / (2 ^ l : ℚ))‖ ^ 2)) := by
  unfold dyadicGridVariationTwoIndex
  apply iSup_le
  intro N
  apply iSup_le
  intro u
  by_cases h : 0 < N ∧ StrictMono u ∧ ∀ i, u i ≤ 2 ^ L
  · have hchain := dyadicFiniteChain_incrementNorm_le_gridSquareSums
      u h.2.1 h.2.2 (fun n => g (dyadicGridPoint L n))
    have hlevels :
        (∑ l ∈ Finset.range (L + 1),
          Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
            ‖g (dyadicGridPoint L (dyadicBlockEnd L l m)) -
              g (dyadicGridPoint L (dyadicBlockStart L l m))‖ ^ 2)) =
        ∑ l ∈ Finset.range (L + 1),
          Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
            ‖g (((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ)) -
              g ((m : ℚ) / (2 ^ l : ℚ))‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlL : l ≤ L := by
        have := Finset.mem_range.mp hl
        omega
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      simp [dyadicGridPoint_blockEnd hlL, dyadicGridPoint_blockStart hlL]
    have hreal :
        Real.sqrt (∑ i : Fin N,
          ‖g (dyadicGridPoint L (u i.succ)) -
            g (dyadicGridPoint L (u i.castSucc))‖ ^ 2) ≤
          Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
            Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
              ‖g (((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ)) -
                g ((m : ℚ) / (2 ^ l : ℚ))‖ ^ 2) := by
      calc
        Real.sqrt (∑ i : Fin N,
            ‖g (dyadicGridPoint L (u i.succ)) -
              g (dyadicGridPoint L (u i.castSucc))‖ ^ 2) ≤
            Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
              Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
                ‖(fun n => g (dyadicGridPoint L n)) (dyadicBlockEnd L l m) -
                  (fun n => g (dyadicGridPoint L n))
                    (dyadicBlockStart L l m)‖ ^ 2) := hchain
        _ = Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
              Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
                ‖g (((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ)) -
                  g ((m : ℚ) / (2 ^ l : ℚ))‖ ^ 2) := by
          rw [hlevels]
    simp only [dif_pos h]
    exact ENNReal.ofReal_le_ofReal hreal
  · simp only [dif_neg h]
    exact bot_le

/-- Integer indices preserve strict order on each finite dyadic grid. -/
theorem dyadicGridPoint_strictMono (L : ℕ) :
    StrictMono (dyadicGridPoint L) := by
  intro m n hmn
  unfold dyadicGridPoint
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hmn)
    (inv_pos.mpr (by positivity))

/-- The homogeneous 2-variation defined directly over the rational time set
`G_L`, using exactly the nonempty finite chains from `lm:spaces`. -/
noncomputable def dyadicGridVariationTwo (L : ℕ) (g : ℚ → ℂ) : ENNReal :=
  by
    classical
    exact ⨆ N : ℕ, ⨆ t : Fin (N + 1) → ℚ,
      if h : 0 < N ∧ StrictMono t ∧ ∀ i, t i ∈ dyadicGridTimes L then
        ENNReal.ofReal (Real.sqrt (∑ i : Fin N,
          ‖g (t i.succ) - g (t i.castSucc)‖ ^ 2))
      else 0

/-- The grid variation depends only on a function's values on `G_L`; values
outside the approved time set do not enter its chain supremum. -/
theorem dyadicGridVariationTwo_congr_on_grid
    (L : ℕ) (g h : ℚ → ℂ)
    (hgh : ∀ t, t ∈ dyadicGridTimes L → g t = h t) :
    dyadicGridVariationTwo L g = dyadicGridVariationTwo L h := by
  classical
  unfold dyadicGridVariationTwo
  apply iSup_congr
  intro N
  apply iSup_congr
  intro t
  by_cases hv : 0 < N ∧ StrictMono t ∧ ∀ i, t i ∈ dyadicGridTimes L
  · rw [dif_pos hv, dif_pos hv]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hgh (t i.succ) (hv.2.2 i.succ),
      hgh (t i.castSucc) (hv.2.2 i.castSucc)]
  · rw [dif_neg hv, dif_neg hv]

/-- Reindexing chains by their unique integer grid coordinates preserves the
homogeneous variation exactly. This establishes the semantic bridge between
`dyadicGridVariationTwoIndex` and the source definition on `G_L`. -/
theorem dyadicGridVariationTwo_eq_index
    (L : ℕ) (g : ℚ → ℂ) :
    dyadicGridVariationTwo L g = dyadicGridVariationTwoIndex L g := by
  classical
  apply le_antisymm
  · unfold dyadicGridVariationTwo
    apply iSup_le
    intro N
    apply iSup_le
    intro t
    by_cases h : 0 < N ∧ StrictMono t ∧ ∀ i, t i ∈ dyadicGridTimes L
    · let u : Fin (N + 1) → ℕ := fun i => Classical.choose (h.2.2 i)
      have huBound : ∀ i, u i ≤ 2 ^ L := by
        intro i
        exact (Classical.choose_spec (h.2.2 i)).1
      have hpoint : ∀ i, dyadicGridPoint L (u i) = t i := by
        intro i
        exact (Classical.choose_spec (h.2.2 i)).2
      have huStrict : StrictMono u := by
        intro i j hij
        have htimes : dyadicGridPoint L (u i) < dyadicGridPoint L (u j) := by
          simpa only [hpoint i, hpoint j] using h.2.1 hij
        exact (dyadicGridPoint_strictMono L).lt_iff_lt.mp htimes
      have hindex : 0 < N ∧ StrictMono u ∧ ∀ i, u i ≤ 2 ^ L :=
        ⟨h.1, huStrict, huBound⟩
      have hvalue :
          Real.sqrt (∑ i : Fin N, ‖g (t i.succ) - g (t i.castSucc)‖ ^ 2) =
            Real.sqrt (∑ i : Fin N,
              ‖g (dyadicGridPoint L (u i.succ)) -
                g (dyadicGridPoint L (u i.castSucc))‖ ^ 2) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [hpoint i.succ, hpoint i.castSucc]
      simp only [dif_pos h]
      unfold dyadicGridVariationTwoIndex
      apply le_iSup_of_le N
      apply le_iSup_of_le u
      simp only [dif_pos hindex]
      rw [hvalue]
    · simp only [dif_neg h]
      exact bot_le
  · unfold dyadicGridVariationTwoIndex
    apply iSup_le
    intro N
    apply iSup_le
    intro u
    by_cases h : 0 < N ∧ StrictMono u ∧ ∀ i, u i ≤ 2 ^ L
    · let t : Fin (N + 1) → ℚ := fun i => dyadicGridPoint L (u i)
      have htStrict : StrictMono t := (dyadicGridPoint_strictMono L).comp h.2.1
      have htGrid : ∀ i, t i ∈ dyadicGridTimes L := by
        intro i
        exact ⟨u i, h.2.2 i, rfl⟩
      have htime : 0 < N ∧ StrictMono t ∧ ∀ i, t i ∈ dyadicGridTimes L :=
        ⟨h.1, htStrict, htGrid⟩
      simp only [dif_pos h]
      unfold dyadicGridVariationTwo
      apply le_iSup_of_le N
      apply le_iSup_of_le t
      simp only [dif_pos htime]
      rfl
    · simp only [dif_neg h]
      exact bot_le

/-- The approved finite-grid dyadic chaining inequality `lm:chaining`, with
the variation and time grid given by their explicit source definitions. -/
theorem dyadicGridVariationTwo_le
    (L : ℕ) (g : ℚ → ℂ) :
    dyadicGridVariationTwo L g ≤
      ENNReal.ofReal (Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖g (((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ)) -
            g ((m : ℚ) / (2 ^ l : ℚ))‖ ^ 2)) := by
  rw [dyadicGridVariationTwo_eq_index]
  exact dyadicGridVariationTwoIndex_le L g

/-- Extend data defined only on the approved rational grid by zero away from
that grid. The variation theorem below is independent of this choice of
extension. -/
noncomputable def dyadicGridExtend (L : ℕ)
    (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ) : ℚ → ℂ := by
  classical
  exact fun t => if ht : t ∈ dyadicGridTimes L then g ⟨t, ht⟩ else 0

@[simp]
theorem dyadicGridExtend_of_mem (L : ℕ)
    (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ)
    {t : ℚ} (ht : t ∈ dyadicGridTimes L) :
    dyadicGridExtend L g t = g ⟨t, ht⟩ := by
  simp [dyadicGridExtend, ht]

/-- The source variation with an input whose domain is literally the grid.
It is represented using the canonical zero extension, and the equality theorem
below proves that any rational extension gives the same value. -/
noncomputable def dyadicGridVariationTwoSubtype (L : ℕ)
    (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ) : ENNReal :=
  dyadicGridVariationTwo L (dyadicGridExtend L g)

/-- Any rational-time extension of subtype data on the grid has the same
variation as the canonical extension. This makes the subtype encoding
equivalent to the original restriction-based definition. -/
theorem dyadicGridVariationTwo_eq_subtype
    (L : ℕ) (f : ℚ → ℂ)
    (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ)
    (hfg : ∀ t (ht : t ∈ dyadicGridTimes L), f t = g ⟨t, ht⟩) :
    dyadicGridVariationTwo L f = dyadicGridVariationTwoSubtype L g := by
  apply dyadicGridVariationTwo_congr_on_grid
  intro t ht
  rw [dyadicGridExtend_of_mem L g ht]
  exact hfg t ht

/-- The subtype time of the left endpoint of a valid level interval. The
fallback branch makes the definition total; it is never used by the range
sums in the subtype chaining estimate. -/
noncomputable def dyadicGridLevelPoint (L l m : ℕ) :
    {t : ℚ // t ∈ dyadicGridTimes L} := by
  classical
  exact if h : l ≤ L ∧ m < 2 ^ l then
    ⟨(m : ℚ) / (2 ^ l : ℚ), dyadicGridTimes_levelPoint_mem h.1 h.2⟩
  else ⟨dyadicGridPoint L 0, ⟨0, Nat.zero_le (2 ^ L), rfl⟩⟩

/-- The subtype time of the right endpoint of a valid level interval. -/
noncomputable def dyadicGridLevelSuccessorPoint (L l m : ℕ) :
    {t : ℚ // t ∈ dyadicGridTimes L} := by
  classical
  exact if h : l ≤ L ∧ m < 2 ^ l then
    ⟨((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ),
      dyadicGridTimes_levelSuccessor_mem h.1 h.2⟩
  else ⟨dyadicGridPoint L 0, ⟨0, Nat.zero_le (2 ^ L), rfl⟩⟩

@[simp]
theorem dyadicGridLevelPoint_valid {L l m : ℕ}
    (hl : l ≤ L) (hm : m < 2 ^ l) :
    dyadicGridLevelPoint L l m =
      ⟨(m : ℚ) / (2 ^ l : ℚ), dyadicGridTimes_levelPoint_mem hl hm⟩ := by
  classical
  simp [dyadicGridLevelPoint, hl, hm]

@[simp]
theorem dyadicGridLevelSuccessorPoint_valid {L l m : ℕ}
    (hl : l ≤ L) (hm : m < 2 ^ l) :
    dyadicGridLevelSuccessorPoint L l m =
      ⟨((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ),
        dyadicGridTimes_levelSuccessor_mem hl hm⟩ := by
  classical
  simp [dyadicGridLevelSuccessorPoint, hl, hm]

theorem dyadicGridExtend_levelPoint (L : ℕ)
    (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ)
    {l m : ℕ} (hl : l ≤ L) (hm : m < 2 ^ l) :
    dyadicGridExtend L g ((m : ℚ) / (2 ^ l : ℚ)) =
      g (dyadicGridLevelPoint L l m) := by
  rw [dyadicGridExtend_of_mem L g (dyadicGridTimes_levelPoint_mem hl hm)]
  rw [dyadicGridLevelPoint_valid hl hm]

theorem dyadicGridExtend_levelSuccessorPoint (L : ℕ)
    (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ)
    {l m : ℕ} (hl : l ≤ L) (hm : m < 2 ^ l) :
    dyadicGridExtend L g (((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ)) =
      g (dyadicGridLevelSuccessorPoint L l m) := by
  rw [dyadicGridExtend_of_mem L g (dyadicGridTimes_levelSuccessor_mem hl hm)]
  rw [dyadicGridLevelSuccessorPoint_valid hl hm]

/-- The exact finite-grid chaining estimate with an input whose domain is the
subtype grid. Every increment on the right is evaluated at the corresponding
approved left and right grid-point subtypes. -/
theorem dyadicGridVariationTwoSubtype_le (L : ℕ)
    (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ) :
    dyadicGridVariationTwoSubtype L g ≤
      ENNReal.ofReal (Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖g (dyadicGridLevelSuccessorPoint L l m) -
            g (dyadicGridLevelPoint L l m)‖ ^ 2)) := by
  have hsum :
      (∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖dyadicGridExtend L g (((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ)) -
            dyadicGridExtend L g ((m : ℚ) / (2 ^ l : ℚ))‖ ^ 2)) =
      (∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖g (dyadicGridLevelSuccessorPoint L l m) -
            g (dyadicGridLevelPoint L l m)‖ ^ 2)) := by
    apply Finset.sum_congr rfl
    intro l hl
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    have hlL : l ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hmPow : m < 2 ^ l := Finset.mem_range.mp hm
    rw [dyadicGridExtend_levelSuccessorPoint L g hlL hmPow,
      dyadicGridExtend_levelPoint L g hlL hmPow]
  calc
    dyadicGridVariationTwoSubtype L g =
        dyadicGridVariationTwo L (dyadicGridExtend L g) := rfl
    _ ≤ ENNReal.ofReal (Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
          Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
            ‖dyadicGridExtend L g (((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ)) -
              dyadicGridExtend L g ((m : ℚ) / (2 ^ l : ℚ))‖ ^ 2)) :=
        dyadicGridVariationTwo_le L (dyadicGridExtend L g)
    _ = _ := by rw [hsum]

/-- The same chaining estimate after pulling back along an affine time map.
When `c > 0`, the map `t ↦ a + c*t` is increasing, which is the affine
rescaling case stated in `lm:chaining`. -/
theorem dyadicGridVariationTwo_affine_le
    (L : ℕ) (g : ℚ → ℂ) (a c : ℚ) :
    dyadicGridVariationTwo L (fun t => g (a + c * t)) ≤
      ENNReal.ofReal (Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖g (a + c * (((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ))) -
            g (a + c * ((m : ℚ) / (2 ^ l : ℚ)))‖ ^ 2)) := by
  exact dyadicGridVariationTwo_le L (fun t => g (a + c * t))

end FractionalPrimes.Literature.MSZ
