module

public import FractionalPrimes.Literature.Hyperbola.ProgressionLengthSplit
public import FractionalPrimes.Literature.Hyperbola.ResiduePrefixSelection
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Coordinate cuts of lattice progressions

This file develops blueprint lemma `lhg:coordinate-cut`.  The first helper is
the exact Bézout step: the two coordinate congruences force the progression
indices into one residue class modulo the coordinate spacing.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

open FractionalPrimes.Literature.Uniformity

/-- If `a` and `q` are coprime and a modulus divides both `a h` and `q h`,
then it divides `h`.  This is the precise Bézout obstruction used in
`lhg:coordinate-cut`. -/
theorem modulus_dvd_indexDifference_of_coprime
    (a q q₀ : ℕ) (hcop : Nat.Coprime a q) (h : ℤ)
    (ha : (q₀ : ℤ) ∣ (a : ℤ) * h)
    (hq : (q₀ : ℤ) ∣ (q : ℤ) * h) :
    (q₀ : ℤ) ∣ h := by
  have hcopZ : IsCoprime (a : ℤ) (q : ℤ) := hcop.isCoprime
  rcases hcopZ with ⟨u, v, huv⟩
  have hcomb : (q₀ : ℤ) ∣
      u * ((a : ℤ) * h) + v * ((q : ℤ) * h) :=
    dvd_add (ha.mul_left u) (hq.mul_left v)
  have heq :
    u * ((a : ℤ) * h) + v * ((q : ℤ) * h) =
        (u * (a : ℤ) + v * (q : ℤ)) * h := by ring
  rw [heq, huv, one_mul] at hcomb
  exact hcomb

/-- A nonempty finite set whose elements lie in one residue class and which
is convex along that residue class is exactly the corresponding residue slice
between its least and greatest elements. -/
theorem finset_eq_Ioc_filter_modEq_min'_max'
    (S : Finset ℤ) (hS : S.Nonempty) (q₀ : ℕ)
    (hmod : ∀ j ∈ S,
      j ≡ S.min' hS [ZMOD (q₀ : ℤ)])
    (hconv : ∀ j : ℤ,
      S.min' hS ≤ j → j ≤ S.max' hS →
      j ≡ S.min' hS [ZMOD (q₀ : ℤ)] → j ∈ S) :
    S = {j ∈ Finset.Ioc (S.min' hS - 1) (S.max' hS) |
      j ≡ S.min' hS [ZMOD (q₀ : ℤ)]} := by
  ext j
  constructor
  · intro hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, Finset.le_max' S j hj⟩, hmod j hj⟩
    have hmin := Finset.min'_le S j hj
    omega
  · intro hj
    rcases Finset.mem_filter.mp hj with ⟨hjIoc, hjmod⟩
    rcases Finset.mem_Ioc.mp hjIoc with ⟨hjlo, hjhi⟩
    exact hconv j (by omega) hjhi hjmod

/-- A finite arithmetic progression is order-convex when one stays in its
residue class: every congruent point between two of its points also belongs
to it. -/
theorem mem_arithmeticProgressionPoints_of_between_of_modEq
    (s : ℤ) (d : ℕ) (hd : 0 < d) (L : ℕ) {x y z : ℤ}
    (hx : x ∈ arithmeticProgressionPoints s d hd L)
    (hy : y ∈ arithmeticProgressionPoints s d hd L)
    (hxz : x ≤ z) (hzy : z ≤ y)
    (hmod : z ≡ x [ZMOD (d : ℤ)]) :
    z ∈ arithmeticProgressionPoints s d hd L := by
  have hL : 0 < L := by
    by_contra hnot
    have hzero : L = 0 := Nat.eq_zero_of_not_pos hnot
    simp [arithmeticProgressionPoints, hzero] at hx
  have hrepr := arithmeticProgressionPoints_eq_Ioc_filter_modEq s d hd L hL
  have hx' : x ∈
      {w ∈ Finset.Ioc (s - 1) (s + ((L - 1 : ℕ) : ℤ) * (d : ℤ)) |
        w ≡ s [ZMOD (d : ℤ)]} := by
    rw [← hrepr]
    exact hx
  have hy' : y ∈
      {w ∈ Finset.Ioc (s - 1) (s + ((L - 1 : ℕ) : ℤ) * (d : ℤ)) |
        w ≡ s [ZMOD (d : ℤ)]} := by
    rw [← hrepr]
    exact hy
  rcases Finset.mem_filter.mp hx' with ⟨hxIoc, hxmod⟩
  rcases Finset.mem_filter.mp hy' with ⟨hyIoc, _⟩
  rcases Finset.mem_Ioc.mp hxIoc with ⟨hxlo, _⟩
  rcases Finset.mem_Ioc.mp hyIoc with ⟨_, hyhi⟩
  rw [hrepr]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨lt_of_lt_of_le hxlo hxz,
      le_trans hzy hyhi⟩, hmod.trans hxmod⟩

/-- Every point of a finite arithmetic progression is congruent to its
initial point modulo the progression spacing. -/
theorem modEq_start_of_mem_arithmeticProgressionPoints
    (s : ℤ) (d : ℕ) (hd : 0 < d) (L : ℕ) {x : ℤ}
    (hx : x ∈ arithmeticProgressionPoints s d hd L) :
    x ≡ s [ZMOD (d : ℤ)] := by
  rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(j : ℤ), ?_⟩
  ring

/-- The finite set of progression indices that survive both coordinate
restrictions. -/
def coordinateProgressionIndexSet
    (base : ℤ × ℤ) (q a lo hi : ℤ)
    (s₁ s₂ : ℤ) (q₀ : ℕ) (hq₀ : 0 < q₀) (L₁ L₂ : ℕ) : Finset ℤ :=
  (Finset.Icc lo hi).filter fun j =>
    base.1 + j * q ∈ arithmeticProgressionPoints s₁ q₀ hq₀ L₁ ∧
      base.2 - j * a ∈ arithmeticProgressionPoints s₂ q₀ hq₀ L₂

/-- The coordinate-restricted part of an integer-indexed lattice
progression. -/
def coordinateProgressionCut
    (base : ℤ × ℤ) (q a lo hi : ℤ)
    (s₁ s₂ : ℤ) (q₀ : ℕ) (hq₀ : 0 < q₀) (L₁ L₂ : ℕ) :
    Set (ℤ × ℤ) :=
  cellLatticeIccProgression base q a lo hi ∩
    {p | p.1 ∈ arithmeticProgressionPoints s₁ q₀ hq₀ L₁ ∧
      p.2 ∈ arithmeticProgressionPoints s₂ q₀ hq₀ L₂}

/-- The coordinate cut is the affine image of its surviving index set. -/
theorem coordinateProgressionCut_eq_image_indexSet
    (base : ℤ × ℤ) (q a lo hi : ℤ)
    (s₁ s₂ : ℤ) (q₀ : ℕ) (hq₀ : 0 < q₀) (L₁ L₂ : ℕ) :
    coordinateProgressionCut base q a lo hi s₁ s₂ q₀ hq₀ L₁ L₂ =
      (fun j : ℤ => (base.1 + j * q, base.2 - j * a)) ''
        (↑(coordinateProgressionIndexSet
          base q a lo hi s₁ s₂ q₀ hq₀ L₁ L₂) : Set ℤ) := by
  classical
  ext p
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hp₁, hp₂⟩
    refine ⟨j, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hj, hp₁, hp₂⟩
  · rintro ⟨j, hj, rfl⟩
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hp₁, hp₂⟩
    exact ⟨⟨j, Finset.mem_Icc.mp hjIcc, rfl⟩, hp₁, hp₂⟩

/-- Mapping an exact integer progression of indices through the lattice
parameterization multiplies its lattice spacing by the index spacing. -/
theorem affine_image_arithmeticProgressionPoints
    (base : ℤ × ℤ) (q a s : ℤ) (d : ℕ) (hd : 0 < d)
    (L : ℕ) (hL : 0 < L) :
    (fun j : ℤ => (base.1 + j * q, base.2 - j * a)) ''
        (↑(arithmeticProgressionPoints s d hd L) : Set ℤ) =
      (↑(latticeProgression
        (base.1 + s * q, base.2 - s * a)
        ((d : ℤ) * q) ((d : ℤ) * a) L hL) : Set (ℤ × ℤ)) := by
  classical
  ext p
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, ?_⟩
    apply Prod.ext <;> simp <;> ring
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨k, _hk, rfl⟩
    refine ⟨s + (k : ℤ) * (d : ℤ), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨k.val, Finset.mem_range.mpr k.isLt, rfl⟩
    · apply Prod.ext <;> simp <;> ring

/-- **Blueprint `lhg:coordinate-cut`.** Restricting a finite lattice
progression of spacing `(q,-a)` to two coordinate progressions of common
spacing `q₀` gives either the empty set or a finite lattice progression of
the exact spacing `q₀(q,-a)`. The output has no more points than the source
progression. -/
theorem coordinateProgressionIntersection
    (a q q₀ : ℕ) (ha : 0 < a) (hq : 0 < q) (hq₀ : 0 < q₀)
    (hcop : Nat.Coprime a q)
    (base : ℤ × ℤ) (lo hi s₁ s₂ : ℤ) (L₁ L₂ : ℕ) :
    let source := cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo hi
    let cut := coordinateProgressionCut
      base (q : ℤ) (a : ℤ) lo hi s₁ s₂ q₀ hq₀ L₁ L₂
    cut = ∅ ∨
      ∃ start : ℤ, ∃ N : ℕ, ∃ hN : 0 < N,
        cut =
          (↑(latticeProgression
            (base.1 + start * (q : ℤ), base.2 - start * (a : ℤ))
            ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN) :
              Set (ℤ × ℤ)) ∧
        cut.ncard ≤ source.ncard := by
  classical
  dsimp only
  let S : Finset ℤ := coordinateProgressionIndexSet
    base (q : ℤ) (a : ℤ) lo hi s₁ s₂ q₀ hq₀ L₁ L₂
  by_cases hSempty : S = ∅
  · left
    rw [coordinateProgressionCut_eq_image_indexSet]
    change (fun j : ℤ =>
      (base.1 + j * (q : ℤ), base.2 - j * (a : ℤ))) ''
        (↑S : Set ℤ) = ∅
    simp [hSempty]
  · right
    have hS : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
    have hindexData : ∀ {j : ℤ}, j ∈ S →
        j ∈ Finset.Icc lo hi ∧
          (base.1 + j * (q : ℤ) ∈
            arithmeticProgressionPoints s₁ q₀ hq₀ L₁ ∧
           base.2 - j * (a : ℤ) ∈
            arithmeticProgressionPoints s₂ q₀ hq₀ L₂) := by
      intro j hj
      simpa [S, coordinateProgressionIndexSet] using hj
    have hjmin : S.min' hS ∈ S := Finset.min'_mem S hS
    have hjmax : S.max' hS ∈ S := Finset.max'_mem S hS
    have hminData := hindexData hjmin
    have hmaxData := hindexData hjmax
    have hmod : ∀ j ∈ S, j ≡ S.min' hS [ZMOD (q₀ : ℤ)] := by
      intro j hj
      have hjData := hindexData hj
      have hxj := modEq_start_of_mem_arithmeticProgressionPoints
        s₁ q₀ hq₀ L₁ hjData.2.1
      have hxmin := modEq_start_of_mem_arithmeticProgressionPoints
        s₁ q₀ hq₀ L₁ hminData.2.1
      have hyj := modEq_start_of_mem_arithmeticProgressionPoints
        s₂ q₀ hq₀ L₂ hjData.2.2
      have hymin := modEq_start_of_mem_arithmeticProgressionPoints
        s₂ q₀ hq₀ L₂ hminData.2.2
      have hqDivRaw := Int.modEq_iff_dvd.mp (hxj.trans hxmin.symm)
      have haDivRaw := Int.modEq_iff_dvd.mp (hymin.trans hyj.symm)
      have hqDiv : (q₀ : ℤ) ∣
          (q : ℤ) * (S.min' hS - j) := by
        convert hqDivRaw using 1 <;> ring
      have haDiv : (q₀ : ℤ) ∣
          (a : ℤ) * (S.min' hS - j) := by
        convert haDivRaw using 1 <;> ring
      exact Int.modEq_iff_dvd.mpr
        (modulus_dvd_indexDifference_of_coprime
          a q q₀ hcop (S.min' hS - j) haDiv hqDiv)
    have hconv : ∀ j : ℤ,
        S.min' hS ≤ j → j ≤ S.max' hS →
        j ≡ S.min' hS [ZMOD (q₀ : ℤ)] → j ∈ S := by
      intro j hjminle hjmaxle hjmod
      have hminIcc := Finset.mem_Icc.mp hminData.1
      have hmaxIcc := Finset.mem_Icc.mp hmaxData.1
      have hjIcc : j ∈ Finset.Icc lo hi :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
      have haZ : 0 < (a : ℤ) := by exact_mod_cast ha
      have hxlo :
          base.1 + S.min' hS * (q : ℤ) ≤
            base.1 + j * (q : ℤ) := by nlinarith
      have hxhi :
          base.1 + j * (q : ℤ) ≤
            base.1 + S.max' hS * (q : ℤ) := by nlinarith
      have hxmod :
          base.1 + j * (q : ℤ) ≡
            base.1 + S.min' hS * (q : ℤ) [ZMOD (q₀ : ℤ)] :=
        (hjmod.mul_right (q : ℤ)).add_left base.1
      have hxmem := mem_arithmeticProgressionPoints_of_between_of_modEq
        s₁ q₀ hq₀ L₁ hminData.2.1 hmaxData.2.1 hxlo hxhi hxmod
      have hjmodMax : j ≡ S.max' hS [ZMOD (q₀ : ℤ)] :=
        hjmod.trans (hmod (S.max' hS) hjmax).symm
      have hylo :
          base.2 - S.max' hS * (a : ℤ) ≤
            base.2 - j * (a : ℤ) := by nlinarith
      have hyhi :
          base.2 - j * (a : ℤ) ≤
            base.2 - S.min' hS * (a : ℤ) := by nlinarith
      have hymod :
          base.2 - j * (a : ℤ) ≡
            base.2 - S.max' hS * (a : ℤ) [ZMOD (q₀ : ℤ)] :=
        (hjmodMax.mul_right (a : ℤ)).sub_left base.2
      have hymem := mem_arithmeticProgressionPoints_of_between_of_modEq
        s₂ q₀ hq₀ L₂ hmaxData.2.2 hminData.2.2 hylo hyhi hymod
      have hjIndex : j ∈ coordinateProgressionIndexSet
          base (q : ℤ) (a : ℤ) lo hi s₁ s₂ q₀ hq₀ L₁ L₂ := by
        apply Finset.mem_filter.mpr
        exact ⟨hjIcc, ⟨hxmem, hymem⟩⟩
      simpa [S] using hjIndex
    have hclass := finset_eq_Ioc_filter_modEq_min'_max'
      S hS q₀ hmod hconv
    rcases filtered_Ioc_modEq_eq_arithmeticProgressionPoints
        (S.min' hS - 1) (S.max' hS) (S.min' hS) q₀ hq₀ with
      ⟨start, N, hrepr⟩
    have hSrepr : S = arithmeticProgressionPoints start q₀ hq₀ N :=
      hclass.trans hrepr.symm
    have hAPnonempty :
        (arithmeticProgressionPoints start q₀ hq₀ N).Nonempty := by
      rw [← hSrepr]
      exact hS
    have hN : 0 < N := by
      apply Nat.pos_of_ne_zero
      intro hNzero
      subst N
      simpa [arithmeticProgressionPoints] using hAPnonempty
    refine ⟨start, N, hN, ?_, ?_⟩
    · rw [coordinateProgressionCut_eq_image_indexSet]
      change (fun j : ℤ =>
        (base.1 + j * (q : ℤ), base.2 - j * (a : ℤ))) ''
          (↑S : Set ℤ) = _
      rw [hSrepr]
      exact affine_image_arithmeticProgressionPoints
        base (q : ℤ) (a : ℤ) start q₀ hq₀ N hN
    · apply Set.ncard_le_ncard
      · intro p hp
        exact hp.1
      · exact cellLatticeIccProgression_finite
          base (q : ℤ) (a : ℤ) lo hi

end FractionalPrimes.Literature.Hyperbola

#print axioms FractionalPrimes.Literature.Hyperbola.modulus_dvd_indexDifference_of_coprime
#print axioms FractionalPrimes.Literature.Hyperbola.finset_eq_Ioc_filter_modEq_min'_max'
#print axioms FractionalPrimes.Literature.Hyperbola.mem_arithmeticProgressionPoints_of_between_of_modEq
#print axioms FractionalPrimes.Literature.Hyperbola.modEq_start_of_mem_arithmeticProgressionPoints
#print axioms FractionalPrimes.Literature.Hyperbola.coordinateProgressionCut_eq_image_indexSet
#print axioms FractionalPrimes.Literature.Hyperbola.affine_image_arithmeticProgressionPoints
#print axioms FractionalPrimes.Literature.Hyperbola.coordinateProgressionIntersection
