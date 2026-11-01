module

public import FractionalPrimes.Literature.Hyperbola.CellLinearSlices
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Order.Interval.Set.Nat

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

/-- The point with index `j` in a lattice progression with initial point `base`
and spacing `(q,-a)`. -/
def latticeProgressionPoint (base : ℤ × ℤ) (q a : ℤ) (j : ℕ) : ℤ × ℤ :=
  (base.1 + (j : ℤ) * q, base.2 - (j : ℤ) * a)

/-- A lattice progression indexed by the finite natural interval `[lo,hi]`.
Every such set uses the same spacing `(q,-a)`. -/
def natIndexedLatticeProgression (base : ℤ × ℤ) (q a : ℤ)
    (lo hi : ℕ) : Set (ℤ × ℤ) :=
  (latticeProgressionPoint base q a) '' Set.Icc lo hi

/-- Number of pieces in the deterministic split at real length `L`. -/
noncomputable def progressionSplitPieceCount (N : ℕ) (L : ℝ) : ℕ :=
  N ⌈/⌉ ⌊L⌋₊

/-- Initial index of block `j` in the deterministic split. -/
noncomputable def progressionSplitBlockLower (L : ℝ) (j : ℕ) : ℕ :=
  j * ⌊L⌋₊

/-- Final index of block `j`, clipped to the final index `N-1`. -/
noncomputable def progressionSplitBlockUpper (N : ℕ) (L : ℝ) (j : ℕ) : ℕ :=
  min (N - 1) ((j + 1) * ⌊L⌋₊ - 1)

/-- The `j`th progression in the deterministic split. -/
def progressionSplitPiece (base : ℤ × ℤ) (q a : ℤ)
    (N : ℕ) (L : ℝ) (j : ℕ) : Set (ℤ × ℤ) :=
  natIndexedLatticeProgression base q a
    (progressionSplitBlockLower L j) (progressionSplitBlockUpper N L j)

private theorem latticeProgressionPoint_injective
    (base : ℤ × ℤ) (q a : ℤ) (hq : 0 < q) :
    Function.Injective (latticeProgressionPoint base q a) := by
  intro i j hij
  have hfst := congrArg Prod.fst hij
  dsimp [latticeProgressionPoint] at hfst
  have hmul : (i : ℤ) * q = (j : ℤ) * q := add_left_cancel hfst
  exact_mod_cast mul_right_cancel₀ hq.ne' hmul

private theorem progressionSplitBlock_bounds
    (N : ℕ) (L : ℝ) (hL : 1 ≤ L) (j : ℕ)
    (hj : j < progressionSplitPieceCount N L) :
    progressionSplitBlockLower L j ≤ progressionSplitBlockUpper N L j ∧
      progressionSplitBlockUpper N L j < N ∧
      progressionSplitBlockUpper N L j + 1 -
          progressionSplitBlockLower L j ≤ ⌊L⌋₊ := by
  let k := ⌊L⌋₊
  have hk : 0 < k := Nat.floor_pos.mpr hL
  have hstart : j * k < N := by
    by_contra h
    have hN : N ≤ j * k := by omega
    have hB : progressionSplitPieceCount N L ≤ j := by
      apply (ceilDiv_le_iff_le_mul hk).2
      simpa [Nat.mul_comm] using hN
    dsimp [progressionSplitPieceCount] at hj hB
    omega
  have hmul : (j + 1) * k = j * k + k := by
    rw [Nat.add_mul, Nat.one_mul]
  have hstep : j * k < (j + 1) * k := by
    rw [hmul]
    omega
  have hloN : j * k ≤ N - 1 := by omega
  have hloStep : j * k ≤ (j + 1) * k - 1 := by rw [hmul]; omega
  have hupperLower : j * k ≤ min (N - 1) ((j + 1) * k - 1) :=
    le_min hloN hloStep
  have hupperN : min (N - 1) ((j + 1) * k - 1) < N := by omega
  have hlen : min (N - 1) ((j + 1) * k - 1) + 1 - j * k ≤ k := by
    have hmin : min (N - 1) ((j + 1) * k - 1) ≤ (j + 1) * k - 1 := min_le_right _ _
    rw [hmul] at hmin
    omega
  refine ⟨?_, ?_, ?_⟩
  · change j * ⌊L⌋₊ ≤ min (N - 1) ((j + 1) * ⌊L⌋₊ - 1)
    simpa [k] using hupperLower
  · change min (N - 1) ((j + 1) * ⌊L⌋₊ - 1) < N
    simpa [k] using hupperN
  · change min (N - 1) ((j + 1) * ⌊L⌋₊ - 1) + 1 - j * ⌊L⌋₊ ≤ ⌊L⌋₊
    simpa [k] using hlen

private theorem progressionSplitBlock_disjoint
    (N : ℕ) (L : ℝ) (hL : 1 ≤ L) {i j : ℕ} (hij : i ≠ j) :
    Disjoint
      (Set.Icc (progressionSplitBlockLower L i)
        (progressionSplitBlockUpper N L i))
      (Set.Icc (progressionSplitBlockLower L j)
        (progressionSplitBlockUpper N L j)) := by
  classical
  have hk : 0 < ⌊L⌋₊ := Nat.floor_pos.mpr hL
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · apply Set.disjoint_left.2
    intro x hxi hxj
    have hstart := Nat.mul_le_mul_right ⌊L⌋₊ (Nat.succ_le_of_lt hlt)
    simp only [Set.mem_Icc] at hxi hxj
    change i * ⌊L⌋₊ ≤ x ∧ x ≤ progressionSplitBlockUpper N L i at hxi
    change j * ⌊L⌋₊ ≤ x ∧ x ≤ progressionSplitBlockUpper N L j at hxj
    have hmul : (i + 1) * ⌊L⌋₊ = i * ⌊L⌋₊ + ⌊L⌋₊ := by
      rw [Nat.add_mul, Nat.one_mul]
    have hiextra :
        progressionSplitBlockUpper N L i < (i + 1) * ⌊L⌋₊ := by
      have hcap : progressionSplitBlockUpper N L i ≤ (i + 1) * ⌊L⌋₊ - 1 := by
        exact min_le_right _ _
      rw [hmul] at hcap
      omega
    rw [hmul] at hstart
    omega
  · apply Set.disjoint_left.2
    intro x hxi hxj
    have hstart := Nat.mul_le_mul_right ⌊L⌋₊ (Nat.succ_le_of_lt hgt)
    simp only [Set.mem_Icc] at hxi hxj
    change i * ⌊L⌋₊ ≤ x ∧ x ≤ progressionSplitBlockUpper N L i at hxi
    change j * ⌊L⌋₊ ≤ x ∧ x ≤ progressionSplitBlockUpper N L j at hxj
    have hmul : (j + 1) * ⌊L⌋₊ = j * ⌊L⌋₊ + ⌊L⌋₊ := by
      rw [Nat.add_mul, Nat.one_mul]
    have hjextra :
        progressionSplitBlockUpper N L j < (j + 1) * ⌊L⌋₊ := by
      have hcap : progressionSplitBlockUpper N L j ≤ (j + 1) * ⌊L⌋₊ - 1 := by
        exact min_le_right _ _
      rw [hmul] at hcap
      omega
    rw [hmul] at hstart
    omega

private theorem natIndexedLatticeProgression_ncard
    (base : ℤ × ℤ) (q a : ℤ) (hq : 0 < q) (lo hi : ℕ) :
    (natIndexedLatticeProgression base q a lo hi).ncard = hi + 1 - lo := by
  unfold natIndexedLatticeProgression
  rw [Set.ncard_image_of_injective _ (latticeProgressionPoint_injective base q a hq)]
  simp

/-- Split a finite lattice progression deterministically into consecutive
blocks of `floor L` indices. The blocks use the original spacing `(q,-a)`,
are disjoint and cover the original progression. For a progression of `N`
points, each piece has at most `L` points and the number of pieces is at most
`2N/L+1`. -/
theorem splitProgressionAtRealLength
    (base : ℤ × ℤ) (q a : ℤ) (hq : 0 < q)
    (N : ℕ) (hN : 0 < N) (L : ℝ) (hL : 1 ≤ L) :
    (∀ j ∈ Finset.range (progressionSplitPieceCount N L),
      (progressionSplitPiece base q a N L j).Nonempty) ∧
    (∀ j ∈ Finset.range (progressionSplitPieceCount N L),
      ((progressionSplitPiece base q a N L j).ncard : ℝ) ≤ L) ∧
    (∀ p : ℤ × ℤ,
      p ∈ natIndexedLatticeProgression base q a 0 (N - 1) ↔
        ∃ j ∈ Finset.range (progressionSplitPieceCount N L),
          p ∈ progressionSplitPiece base q a N L j) ∧
    (∀ i ∈ Finset.range (progressionSplitPieceCount N L),
      ∀ j ∈ Finset.range (progressionSplitPieceCount N L), i ≠ j →
        Disjoint (progressionSplitPiece base q a N L i)
          (progressionSplitPiece base q a N L j)) ∧
    ((Finset.range (progressionSplitPieceCount N L)).card : ℝ) ≤
      2 * (N : ℝ) / L + 1 := by
  classical
  let k := ⌊L⌋₊
  let B := progressionSplitPieceCount N L
  have hk : 0 < k := Nat.floor_pos.mpr hL
  have hkReal : (k : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hLlt : L < (k : ℝ) + 1 := Nat.lt_floor_add_one L
  have hKLower : L ≤ 2 * (k : ℝ) := by
    have hkCast : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hBmul : N ≤ k * B := by
    dsimp [B, progressionSplitPieceCount, k]
    simpa [smul_eq_mul] using (le_smul_ceilDiv (a := k) (b := N) hk)
  have hcount : (Finset.range B).card ≤ 2 * (N : ℝ) / L + 1 := by
    have hceil : B ≤ N / k + 1 := by
      dsimp [B, progressionSplitPieceCount, k]
      apply (ceilDiv_le_iff_le_mul hk).2
      have hmod := Nat.mod_lt N hk
      have hdecomp : N % k + k * (N / k) = N := Nat.mod_add_div N k
      calc
        N = N % k + k * (N / k) := hdecomp.symm
        _ ≤ k + k * (N / k) := Nat.add_le_add_right hmod.le _
        _ = k * (N / k + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
    have hceilReal : (B : ℝ) ≤ ((N / k : ℕ) : ℝ) + 1 := by
      exact_mod_cast hceil
    have hkCast : 0 < (k : ℝ) := by exact_mod_cast hk
    have hquot : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / (k : ℝ) := by
      apply (le_div_iff₀ hkCast).2
      exact_mod_cast Nat.div_mul_le_self N k
    have hdivide : (N : ℝ) / (k : ℝ) ≤ 2 * (N : ℝ) / L := by
      apply (div_le_div_iff₀ hkCast (by linarith : 0 < L)).2
      nlinarith [hKLower]
    rw [Finset.card_range]
    have hright : ((N / k : ℕ) : ℝ) + 1 ≤ 2 * (N : ℝ) / L + 1 := by
      simpa [add_comm] using add_le_add_right (le_trans hquot hdivide) 1
    exact hceilReal.trans hright
  refine ⟨?_, ?_, ?_, ?_, hcount⟩
  · intro j hj
    have hj' : j < B := Finset.mem_range.mp hj
    have hbounds := progressionSplitBlock_bounds N L hL j (by simpa [B] using hj')
    refine ⟨latticeProgressionPoint base q a (progressionSplitBlockLower L j), ?_⟩
    change latticeProgressionPoint base q a (progressionSplitBlockLower L j) ∈
      latticeProgressionPoint base q a ''
        Set.Icc (progressionSplitBlockLower L j)
          (progressionSplitBlockUpper N L j)
    exact ⟨progressionSplitBlockLower L j,
      ⟨le_rfl, hbounds.1⟩, rfl⟩
  · intro j hj
    have hj' : j < B := Finset.mem_range.mp hj
    have hbounds := progressionSplitBlock_bounds N L hL j (by simpa [B] using hj')
    have hcard := natIndexedLatticeProgression_ncard base q a hq
      (progressionSplitBlockLower L j) (progressionSplitBlockUpper N L j)
    change ((natIndexedLatticeProgression base q a
      (progressionSplitBlockLower L j) (progressionSplitBlockUpper N L j)).ncard : ℝ) ≤ L
    rw [hcard]
    have hlenCast :
        ((progressionSplitBlockUpper N L j + 1 -
          progressionSplitBlockLower L j : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hbounds.2.2
    exact hlenCast.trans hkReal
  · intro p
    constructor
    · rintro ⟨i, hi, rfl⟩
      simp only [Set.mem_Icc] at hi
      let b := i / k
      have hb : b < B := by
        apply (Nat.div_lt_iff_lt_mul hk).2
        have hiN : i < N := by omega
        have hBmul' : N ≤ B * k := by simpa [Nat.mul_comm] using hBmul
        omega
      have hlow : b * k ≤ i := by
        dsimp [b]
        exact Nat.div_mul_le_self i k
      have hnext : i < (b + 1) * k := by
        have hdiv : i / k < i / k + 1 := Nat.lt_succ_self _
        have h := (Nat.div_lt_iff_lt_mul hk).1 hdiv
        simpa [b, Nat.mul_comm] using h
      have hcap : i ≤ (b + 1) * k - 1 := by omega
      have hiBlock : i ≤ min (N - 1) ((b + 1) * k - 1) :=
        le_min (by omega) hcap
      refine ⟨b, Finset.mem_range.mpr (by simpa [B] using hb), ?_⟩
      change latticeProgressionPoint base q a i ∈
        latticeProgressionPoint base q a ''
          Set.Icc (b * k) (min (N - 1) ((b + 1) * k - 1))
      exact ⟨i, ⟨hlow, hiBlock⟩, rfl⟩
    · rintro ⟨b, hb, hp⟩
      rcases (progressionSplitBlock_bounds N L hL b
          (Finset.mem_range.mp (by simpa [B] using hb))) with ⟨hlo, hhi, _⟩
      change p ∈ latticeProgressionPoint base q a ''
        Set.Icc (progressionSplitBlockLower L b)
          (progressionSplitBlockUpper N L b) at hp
      rcases hp with ⟨i, hi, rfl⟩
      change latticeProgressionPoint base q a i ∈
        latticeProgressionPoint base q a '' Set.Icc 0 (N - 1)
      change progressionSplitBlockLower L b ≤ i ∧
        i ≤ progressionSplitBlockUpper N L b at hi
      have hiN : i < N := lt_of_le_of_lt hi.2 hhi
      have hiFinal : i ≤ N - 1 := by omega
      exact ⟨i, ⟨Nat.zero_le _, hiFinal⟩, rfl⟩
  · intro i hi j hj hij
    have hblocks := progressionSplitBlock_disjoint N L hL hij
    apply Set.disjoint_left.2
    intro p hpi hpj
    rcases hpi with ⟨x, hx, hpx⟩
    rcases hpj with ⟨y, hy, hpy⟩
    have hxy : x = y :=
      latticeProgressionPoint_injective base q a hq (hpx.trans hpy.symm)
    exact Set.disjoint_left.mp hblocks (hxy ▸ hx) hy

/-- The finite family of progression sets produced by
`splitProgressionAtRealLength`. -/
noncomputable def progressionSplitFamily
    (base : ℤ × ℤ) (q a : ℤ) (N : ℕ) (L : ℝ) : Finset (Set (ℤ × ℤ)) := by
  classical
  exact (Finset.range (progressionSplitPieceCount N L)).image
    (progressionSplitPiece base q a N L)

/-- Set-family form of `splitProgressionAtRealLength`, convenient for finite
unions of source progressions. -/
theorem splitProgressionFamilyProperties
    (base : ℤ × ℤ) (q a : ℤ) (hq : 0 < q)
    (N : ℕ) (hN : 0 < N) (L : ℝ) (hL : 1 ≤ L) :
    (∀ P ∈ progressionSplitFamily base q a N L, P.Nonempty) ∧
    (∀ P ∈ progressionSplitFamily base q a N L, (P.ncard : ℝ) ≤ L) ∧
    (∀ p : ℤ × ℤ,
      p ∈ natIndexedLatticeProgression base q a 0 (N - 1) ↔
        ∃ P ∈ progressionSplitFamily base q a N L, p ∈ P) ∧
    (∀ P ∈ progressionSplitFamily base q a N L,
      ∀ P' ∈ progressionSplitFamily base q a N L, P ≠ P' → Disjoint P P') ∧
    ((progressionSplitFamily base q a N L).card : ℝ) ≤ 2 * (N : ℝ) / L + 1 := by
  classical
  have hsplit := splitProgressionAtRealLength base q a hq N hN L hL
  let F := progressionSplitFamily base q a N L
  have hcard : (F.card : ℝ) ≤
      (Finset.range (progressionSplitPieceCount N L)).card := by
    dsimp [F, progressionSplitFamily]
    exact_mod_cast Finset.card_image_le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    change P ∈ (Finset.range (progressionSplitPieceCount N L)).image
      (progressionSplitPiece base q a N L) at hP
    rcases Finset.mem_image.mp hP with ⟨j, hj, hPj⟩
    subst P
    exact hsplit.1 j hj
  · intro P hP
    change P ∈ (Finset.range (progressionSplitPieceCount N L)).image
      (progressionSplitPiece base q a N L) at hP
    rcases Finset.mem_image.mp hP with ⟨j, hj, hPj⟩
    subst P
    exact hsplit.2.1 j hj
  · intro p
    constructor
    · intro hp
      rcases (hsplit.2.2.1 p).mp hp with ⟨j, hj, hpj⟩
      exact ⟨progressionSplitPiece base q a N L j,
        Finset.mem_image.mpr ⟨j, hj, rfl⟩, hpj⟩
    · rintro ⟨P, hP, hp⟩
      change P ∈ (Finset.range (progressionSplitPieceCount N L)).image
        (progressionSplitPiece base q a N L) at hP
      rcases Finset.mem_image.mp hP with ⟨j, hj, hPj⟩
      subst P
      exact (hsplit.2.2.1 p).mpr ⟨j, hj, hp⟩
  · intro P hP P' hP' hneq
    change P ∈ (Finset.range (progressionSplitPieceCount N L)).image
      (progressionSplitPiece base q a N L) at hP
    change P' ∈ (Finset.range (progressionSplitPieceCount N L)).image
      (progressionSplitPiece base q a N L) at hP'
    rcases Finset.mem_image.mp hP with ⟨i, hi, hPi⟩
    rcases Finset.mem_image.mp hP' with ⟨j, hj, hPj⟩
    subst P
    subst P'
    have hij : i ≠ j := by
      intro heq
      subst j
      exact hneq rfl
    exact hsplit.2.2.2.1 i hi j hj hij
  · simpa [F] using le_trans hcard hsplit.2.2.2.2

/-- The natural-index model of a progression is the coercion of the existing
finite `latticeProgression` on `Fin N`. -/
theorem latticeProgression_coe_eq_natIndexed
    (base : ℤ × ℤ) (q a : ℤ) (N : ℕ) (hN : 0 < N) :
    (latticeProgression base q a N hN : Set (ℤ × ℤ)) =
      natIndexedLatticeProgression base q a 0 (N - 1) := by
  classical
  ext p
  change p ∈ latticeProgression base q a N hN ↔
    p ∈ natIndexedLatticeProgression base q a 0 (N - 1)
  rw [latticeProgression, natIndexedLatticeProgression]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_image]
  constructor
  · rintro ⟨j, hp⟩
    refine ⟨j.val, ?_, ?_⟩
    · simp only [Set.mem_Icc]
      omega
    · simpa [latticeProgressionPoint] using hp
  · rintro ⟨j, hj, hp⟩
    have hjle : j ≤ N - 1 := (Set.mem_Icc.mp hj).2
    have hjN : j < N := by omega
    refine ⟨⟨j, hjN⟩, ?_⟩
    simpa [latticeProgressionPoint] using hp

/-- Rebase an integer-indexed progression at its first point and record its
length as a natural index interval. -/
theorem cellLatticeIccProgression_rebase
    (base : ℤ × ℤ) (q a lo hi : ℤ) (hlohi : lo ≤ hi) :
    cellLatticeIccProgression base q a lo hi =
      natIndexedLatticeProgression
        (base.1 + lo * q, base.2 - lo * a) q a 0
        ((hi - lo + 1).toNat - 1) := by
  classical
  let N := (hi - lo + 1).toNat
  have hlenpos : 0 < hi - lo + 1 := by omega
  have hNcast : (N : ℤ) = hi - lo + 1 := by
    dsimp [N]
    exact Int.toNat_of_nonneg hlenpos.le
  have hNpos : 0 < N := by
    have h : (0 : ℤ) < (N : ℤ) := by rw [hNcast]; omega
    exact_mod_cast h
  ext p
  constructor
  · intro hp
    change ∃ j ∈ Set.Icc lo hi,
      p = (base.1 + j * q, base.2 - j * a) at hp
    rcases hp with ⟨j, hj, rfl⟩
    have hjlo : lo ≤ j := hj.1
    have hjhi : j ≤ hi := hj.2
    let k := (j - lo).toNat
    have hkcast : (k : ℤ) = j - lo := by
      dsimp [k]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hjlo)
    have hkUpper : k ≤ N - 1 := by
      have hdiff : j - lo ≤ hi - lo := by omega
      have hcast : (k : ℤ) ≤ (N - 1 : ℕ) := by
        rw [hkcast]
        rw [Nat.cast_sub hNpos, hNcast]
        omega
      exact_mod_cast hcast
    have hjEq : j = lo + (k : ℤ) := by omega
    change (base.1 + j * q, base.2 - j * a) ∈
      latticeProgressionPoint (base.1 + lo * q, base.2 - lo * a) q a ''
        Set.Icc 0 ((hi - lo + 1).toNat - 1)
    refine ⟨k, ⟨Nat.zero_le _, hkUpper⟩, ?_⟩
    dsimp [latticeProgressionPoint]
    rw [hjEq]
    apply Prod.ext <;> ring
  · intro hp
    change p ∈ latticeProgressionPoint (base.1 + lo * q, base.2 - lo * a) q a ''
      Set.Icc 0 (N - 1) at hp
    rcases hp with ⟨k, hk, rfl⟩
    have hkUpper : (k : ℤ) ≤ hi - lo := by
      have hcast : (k : ℤ) ≤ (N - 1 : ℕ) := by exact_mod_cast hk.2
      rw [Nat.cast_sub hNpos, hNcast] at hcast
      omega
    have hjlo : lo ≤ lo + (k : ℤ) := by omega
    have hjhi : lo + (k : ℤ) ≤ hi := by omega
    change ∃ j ∈ Set.Icc lo hi,
      (base.1 + lo * q + (k : ℤ) * q,
        base.2 - lo * a - (k : ℤ) * a) =
          (base.1 + j * q, base.2 - j * a)
    refine ⟨lo + (k : ℤ), ⟨hjlo, hjhi⟩, ?_⟩
    apply Prod.ext <;> ring

/-- A natural-index lattice progression is the existing integer-interval
progression with cast endpoints. -/
theorem natIndexedLatticeProgression_eq_cellLatticeIcc
    (base : ℤ × ℤ) (q a : ℤ) (lo hi : ℕ) :
    natIndexedLatticeProgression base q a lo hi =
      cellLatticeIccProgression base q a (lo : ℤ) (hi : ℤ) := by
  classical
  ext p
  constructor
  · intro hp
    change p ∈ latticeProgressionPoint base q a '' Set.Icc lo hi at hp
    rcases hp with ⟨j, hj, rfl⟩
    refine ⟨(j : ℤ), ?_, rfl⟩
    change (lo : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) ≤ (hi : ℤ)
    exact ⟨by exact_mod_cast hj.1, by exact_mod_cast hj.2⟩
  · intro hp
    change p ∈ cellLatticeIccProgression base q a (lo : ℤ) (hi : ℤ) at hp
    rcases hp with ⟨j, hj, rfl⟩
    have hjnonneg : 0 ≤ j := le_trans (by exact_mod_cast (Nat.zero_le lo)) hj.1
    let k := j.toNat
    have hkcast : (k : ℤ) = j := by
      dsimp [k]
      exact Int.toNat_of_nonneg hjnonneg
    have hklo : lo ≤ k := by
      have h : (lo : ℤ) ≤ (k : ℤ) := by simpa [hkcast] using hj.1
      exact_mod_cast h
    have hkhi : k ≤ hi := by
      have h : (k : ℤ) ≤ (hi : ℤ) := by simpa [hkcast] using hj.2
      exact_mod_cast h
    refine ⟨k, ⟨hklo, hkhi⟩, ?_⟩
    apply Prod.ext <;> simp [latticeProgressionPoint, hkcast]

end FractionalPrimes.Literature.Hyperbola
