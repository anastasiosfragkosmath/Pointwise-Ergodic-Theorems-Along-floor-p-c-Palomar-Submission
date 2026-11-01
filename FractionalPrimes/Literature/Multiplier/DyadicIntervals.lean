module

public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

/-!
# Integer dyadic intervals (`lp:dyadic-intervals`)

This module records the integer intervals and fivefold enlargements used by
the periodic multiplier Calderón–Zygmund argument.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

/-- The integer dyadic interval `I_{k,a} = [a 2^k, (a+1)2^k)`. -/
def dyadicIntervals (k : ℕ) (a : ℤ) : Finset ℤ :=
  Finset.Ico (a * (2 : ℤ) ^ k) ((a + 1) * (2 : ℤ) ^ k)

theorem mem_dyadicIntervals (k : ℕ) (a x : ℤ) :
    x ∈ dyadicIntervals k a ↔
      a * (2 : ℤ) ^ k ≤ x ∧ x < (a + 1) * (2 : ℤ) ^ k := by
  simp [dyadicIntervals]

/-- Every integer dyadic interval has the prescribed cardinality. -/
theorem dyadicIntervals_card (k : ℕ) (a : ℤ) :
    (dyadicIntervals k a).card = 2 ^ k := by
  have hle : a * (2 : ℤ) ^ k ≤ (a + 1) * (2 : ℤ) ^ k :=
    mul_le_mul_of_nonneg_right (by omega) (by positivity)
  have hcard :
      ((Finset.Ico (a * (2 : ℤ) ^ k) ((a + 1) * (2 : ℤ) ^ k)).card : ℤ) =
        (2 : ℤ) ^ k := by
    rw [Int.card_Ico_of_le _ _ hle]
    ring
  exact_mod_cast hcard

/-- The index of the unique scale-`k+1` parent of `I_{k,a}`. -/
def dyadicParentIndex (a : ℤ) : ℤ := a / 2

/-- Every dyadic interval is contained in its scale-`k+1` parent. -/
theorem dyadicIntervals_subset_parent (k : ℕ) (a : ℤ) :
    dyadicIntervals k a ⊆ dyadicIntervals (k + 1) (dyadicParentIndex a) := by
  let q : ℤ := a / 2
  let r : ℤ := a % 2
  have hdecomp : a = r + 2 * q := by
    dsimp [q, r]
    exact (Int.emod_add_mul_ediv a 2).symm
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg a (by norm_num)
  have hrlt : r < 2 := by
    dsimp [r]
    exact Int.emod_lt_of_pos a (by norm_num)
  have hrle : r ≤ 1 := by omega
  have htpos : 0 < (2 : ℤ) ^ k := by positivity
  have hparentLower : q * (2 : ℤ) ^ (k + 1) ≤ a * (2 : ℤ) ^ k := by
    rw [pow_succ]
    nlinarith [hdecomp, hr0, htpos]
  have hchildUpper : (a + 1) * (2 : ℤ) ^ k ≤
      (q + 1) * (2 : ℤ) ^ (k + 1) := by
    rw [pow_succ]
    nlinarith [hdecomp, hrle, htpos]
  intro x hx
  simp only [dyadicIntervals, Finset.mem_Ico, dyadicParentIndex] at hx ⊢
  exact ⟨le_trans hparentLower hx.1, lt_of_lt_of_le hx.2 hchildUpper⟩

/-- A dyadic interval has only one parent at the next scale. -/
theorem dyadicParentIndex_unique (k : ℕ) (a b : ℤ)
    (hsub : dyadicIntervals k a ⊆ dyadicIntervals (k + 1) b) :
    b = dyadicParentIndex a := by
  let t : ℤ := (2 : ℤ) ^ k
  have htpos : 0 < t := by dsimp [t]; positivity
  have hfirst : a * t ∈ dyadicIntervals k a := by
    change a * t ∈ Finset.Ico (a * t) ((a + 1) * t)
    simp only [Finset.mem_Ico]
    exact ⟨le_rfl, by nlinarith [htpos]⟩
  have hfirstParent := hsub hfirst
  change a * t ∈ Finset.Ico (b * (2 : ℤ) ^ (k + 1))
    ((b + 1) * (2 : ℤ) ^ (k + 1)) at hfirstParent
  simp only [Finset.mem_Ico] at hfirstParent
  have hlast : (a + 1) * t - 1 ∈ dyadicIntervals k a := by
    have htge : 1 ≤ t := by
      dsimp [t]
      exact_mod_cast Nat.one_le_two_pow
    change (a + 1) * t - 1 ∈ Finset.Ico (a * t) ((a + 1) * t)
    simp only [Finset.mem_Ico]
    constructor
    · nlinarith
    · omega
  have hlastParent := hsub hlast
  change (a + 1) * t - 1 ∈ Finset.Ico (b * (2 : ℤ) ^ (k + 1))
    ((b + 1) * (2 : ℤ) ^ (k + 1)) at hlastParent
  simp only [Finset.mem_Ico] at hlastParent
  have hlow : (2 * b) * t ≤ a * t := by
    calc
      (2 * b) * t = b * (2 * t) := by ring
      _ = b * (2 : ℤ) ^ (k + 1) := by dsimp [t]; rw [pow_succ]; ring
      _ ≤ a * t := by simpa [t] using hfirstParent.1
  have hlow' : 2 * b ≤ a :=
    (mul_le_mul_iff_right₀ htpos).mp (by simpa [mul_comm] using hlow)
  have hhigh : (a + 1) * t ≤ (2 * (b + 1)) * t := by
    calc
      (a + 1) * t ≤ (b + 1) * (2 : ℤ) ^ (k + 1) := by
        have := hlastParent.2
        omega
      _ = (2 * (b + 1)) * t := by dsimp [t]; rw [pow_succ]; ring
  have hhigh' : a + 1 ≤ 2 * (b + 1) :=
    (mul_le_mul_iff_right₀ htpos).mp (by simpa [mul_comm] using hhigh)
  dsimp [dyadicParentIndex]
  omega

/-- Distinct intervals at one dyadic scale are disjoint. -/
theorem dyadicIntervals_disjoint_of_ne (k : ℕ) (a b : ℤ) (hne : a ≠ b) :
    Disjoint (dyadicIntervals k a) (dyadicIntervals k b) := by
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  let t : ℤ := (2 : ℤ) ^ k
  have htpos : 0 ≤ t := by dsimp [t]; positivity
  change x ∈ Finset.Ico (a * t) ((a + 1) * t) at hxa
  change x ∈ Finset.Ico (b * t) ((b + 1) * t) at hxb
  simp only [Finset.mem_Ico] at hxa hxb
  by_cases hab : a < b
  · have hsep : (a + 1) * t ≤ b * t :=
      mul_le_mul_of_nonneg_right (by omega) htpos
    omega
  · have hba : b < a := by omega
    have hsep : (b + 1) * t ≤ a * t :=
      mul_le_mul_of_nonneg_right (by omega) htpos
    omega

theorem dyadicIntervals_sameScale_eq_or_disjoint (k : ℕ) (a b : ℤ) :
    dyadicIntervals k a = dyadicIntervals k b ∨
      Disjoint (dyadicIntervals k a) (dyadicIntervals k b) := by
  by_cases hab : a = b
  · subst b
    exact Or.inl rfl
  · exact Or.inr (dyadicIntervals_disjoint_of_ne k a b hab)

/-- The index of the ancestor interval `n` scales above the interval at `a`. -/
def dyadicAncestorIndex (a : ℤ) : ℕ → ℤ
  | 0 => a
  | n + 1 => dyadicParentIndex (dyadicAncestorIndex a n)

theorem dyadicIntervals_subset_ancestor (k : ℕ) (a : ℤ) (n : ℕ) :
    dyadicIntervals k a ⊆ dyadicIntervals (k + n) (dyadicAncestorIndex a n) := by
  induction n with
  | zero => simp [dyadicAncestorIndex]
  | succ n ih =>
    exact ih.trans (dyadicIntervals_subset_parent (k + n) (dyadicAncestorIndex a n))

/-- Any two integer dyadic intervals are disjoint or one contains the other. -/
theorem dyadicIntervals_disjoint_or_nested (k : ℕ) (a : ℤ) (l : ℕ) (b : ℤ) :
    Disjoint (dyadicIntervals k a) (dyadicIntervals l b) ∨
      dyadicIntervals k a ⊆ dyadicIntervals l b ∨
        dyadicIntervals l b ⊆ dyadicIntervals k a := by
  by_cases hkl : k ≤ l
  · let d : ℕ := l - k
    have hscale : k + d = l := by dsimp [d]; omega
    have hanc := dyadicIntervals_subset_ancestor k a d
    rw [hscale] at hanc
    rcases dyadicIntervals_sameScale_eq_or_disjoint l (dyadicAncestorIndex a d) b with heq | hdisj
    · exact Or.inr (Or.inl (heq ▸ hanc))
    · apply Or.inl
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact (Finset.disjoint_left.mp hdisj) (hanc hxA) hxB
  · have hlk : l ≤ k := by omega
    let d : ℕ := k - l
    have hscale : l + d = k := by dsimp [d]; omega
    have hanc := dyadicIntervals_subset_ancestor l b d
    rw [hscale] at hanc
    rcases dyadicIntervals_sameScale_eq_or_disjoint k a (dyadicAncestorIndex b d) with heq | hdisj
    · exact Or.inr (Or.inr (heq.symm ▸ hanc))
    · apply Or.inl
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact (Finset.disjoint_left.mp hdisj) hxA (hanc hxB)

/-- The fivefold enlargement of the integer interval `[a,a+L)`. -/
def integerIntervalEnlargement (a : ℤ) (L : ℕ) : Finset ℤ :=
  Finset.Ico (a - 2 * (L : ℤ)) (a + 3 * (L : ℤ))

theorem integerIntervalEnlargement_card (a : ℤ) (L : ℕ) :
    (integerIntervalEnlargement a L).card = 5 * L := by
  have hle : a - 2 * (L : ℤ) ≤ a + 3 * (L : ℤ) := by omega
  have hcard :
      ((Finset.Ico (a - 2 * (L : ℤ)) (a + 3 * (L : ℤ))).card : ℤ) =
        5 * (L : ℤ) := by
    rw [Int.card_Ico_of_le _ _ hle]
    ring
  exact_mod_cast hcard

end FractionalPrimes.Literature.Multiplier
