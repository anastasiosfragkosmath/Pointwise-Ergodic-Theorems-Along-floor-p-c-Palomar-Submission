module

public import FractionalPrimes.Chebyshev
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.RingTheory.Int.Basic

/-!
# Finite Rosser prefix weights

This module begins the blueprint's `ls:weights` construction. Finite subsets
are represented as finsets of natural primes and listed in decreasing order.
The tested-prefix condition uses the paper's strict threshold and parity.
-/

@[expose] public section

namespace FractionalPrimes

noncomputable section

open scoped Nat.Prime
open Classical

/-- The primes in a finite set, listed in strictly decreasing order. -/
def rosserPrimeList (S : Finset ℕ) : List ℕ := S.sort (· ≥ ·)

theorem rosserPrimeList_mem (S : Finset ℕ) (p : ℕ) :
    p ∈ rosserPrimeList S ↔ p ∈ S := by
  simp [rosserPrimeList]

theorem rosserPrimeList_sorted (S : Finset ℕ) :
    (rosserPrimeList S).SortedGT := by
  simpa [rosserPrimeList] using Finset.sortedGT_sort S

theorem rosserPrimeList_nodup (S : Finset ℕ) :
    (rosserPrimeList S).Nodup := by
  simp [rosserPrimeList]

theorem rosserPrimeList_length (S : Finset ℕ) :
    (rosserPrimeList S).length = S.card := by
  have h := congrArg Finset.card (Finset.sort_toFinset S (· ≥ ·))
  rw [List.toFinset_card_of_nodup (Finset.sort_nodup S (· ≥ ·))] at h
  exact h

theorem rosserBeta_eq : (513 : ℝ) = sieveBeta := by
  norm_num [sieveBeta]

/-- The natural product of the first `j` primes in a decreasing prime list. -/
def rosserPrefixProduct (L : List ℕ) (j : ℕ) : ℕ := (L.take j).prod

theorem rosserPrefixProduct_length (L : List ℕ) :
    rosserPrefixProduct L L.length = L.prod := by
  simp [rosserPrefixProduct]

theorem rosserPrefixProduct_succ {L : List ℕ} {j : ℕ}
    (hj : j < L.length) :
    rosserPrefixProduct L (j + 1) = rosserPrefixProduct L j * L[j] := by
  simp only [rosserPrefixProduct, List.take_add_one,
    List.getElem?_eq_getElem hj, Option.toList_some, List.prod_append,
    List.prod_singleton]

/-- The last selected prime in a prefix. The default value is used only outside
the range `1 ≤ j ≤ L.length`, where the prefix condition is never tested. -/
def rosserPrefixLast (L : List ℕ) (j : ℕ) : ℕ := (L[j - 1]?).getD 1

/-- The finite set represented by the first `j` entries of a list. -/
def rosserPrefixFinset (L : List ℕ) (j : ℕ) : Finset ℕ :=
  (L.take j).toFinset

theorem rosserPrefixFinset_card {L : List ℕ} {j : ℕ}
    (hnd : L.Nodup) (hj : j ≤ L.length) :
    (rosserPrefixFinset L j).card = j := by
  have htake : (L.take j).Nodup := hnd.sublist (List.take_sublist j L)
  rw [rosserPrefixFinset, List.toFinset_card_of_nodup htake]
  simp [List.length_take, Nat.min_eq_left hj]

theorem rosserPrefixFinset_union_drop (L : List ℕ) (j : ℕ) :
    rosserPrefixFinset L j ∪ (L.drop j).toFinset = L.toFinset := by
  calc
    rosserPrefixFinset L j ∪ (L.drop j).toFinset =
        (L.take j ++ L.drop j).toFinset := by
      ext p
      simp only [Finset.mem_union, List.mem_toFinset, rosserPrefixFinset,
        List.mem_append]
    _ = L.toFinset := congrArg List.toFinset (List.take_append_drop j L)

theorem rosserPrefixFinset_disjoint_drop {L : List ℕ} {j : ℕ}
    (hnd : L.Nodup) :
    Disjoint (rosserPrefixFinset L j) (L.drop j).toFinset := by
  apply Finset.disjoint_left.mpr
  intro p hpTake hpDrop
  have hlist := List.disjoint_take_drop hnd (le_rfl : j ≤ j)
  exact hlist (List.mem_toFinset.mp hpTake) (List.mem_toFinset.mp hpDrop)

theorem rosserPrimeList_prefixFinset_eq {L : List ℕ} {j : ℕ}
    (hnd : L.Nodup) (hsorted : L.SortedGT) :
    rosserPrimeList (rosserPrefixFinset L j) = L.take j := by
  rw [rosserPrefixFinset]
  apply (List.toFinset_sort (r := (· ≥ ·))
    (hnd.sublist (List.take_sublist j L))).2
  exact List.Pairwise.take (i := j) hsorted.sortedGE.pairwise

/-- If every value in `A` exceeds every value in `B`, the decreasing list of
their union is the concatenation of the two decreasing lists. -/
theorem rosserPrimeList_union_eq_append {A B : Finset ℕ}
    (hcross : ∀ a ∈ A, ∀ b ∈ B, a > b) :
    rosserPrimeList (A ∪ B) = rosserPrimeList A ++ rosserPrimeList B := by
  let LA := rosserPrimeList A
  let LB := rosserPrimeList B
  have hpair : List.Pairwise (· > ·) (LA ++ LB) := by
    rw [List.pairwise_append]
    refine ⟨(rosserPrimeList_sorted A).pairwise,
      (rosserPrimeList_sorted B).pairwise, ?_⟩
    intro a ha b hb
    exact hcross a ((rosserPrimeList_mem A a).mp ha)
      b ((rosserPrimeList_mem B b).mp hb)
  have hsorted : (LA ++ LB).SortedGT := hpair.sortedGT
  have hnd : (LA ++ LB).Nodup := hsorted.nodup
  have hpairGE : List.Pairwise (· ≥ ·) (LA ++ LB) :=
    hsorted.sortedGE.pairwise
  have hsort := (List.toFinset_sort (r := (· ≥ ·)) hnd).2 hpairGE
  have hfin : (LA ++ LB).toFinset = A ∪ B := by
    ext p
    simp [LA, LB, rosserPrimeList_mem, List.mem_append]
  unfold rosserPrimeList
  rw [← hfin]
  exact hsort

theorem rosserPrefixLast_eq_getElem {L : List ℕ} {j : ℕ}
    (hj : 1 ≤ j) (hjlen : j ≤ L.length) :
    rosserPrefixLast L j = L[j - 1] := by
  unfold rosserPrefixLast
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

theorem rosserPrimeList_mem_ge_last {S : Finset ℕ} {p : ℕ}
    (hne : S.Nonempty) (hp : p ∈ S) :
    p ≥ rosserPrefixLast (rosserPrimeList S) S.card := by
  let L := rosserPrimeList S
  have hlen := rosserPrimeList_length S
  have hcard : 1 ≤ S.card := by
    have hpos := Finset.card_pos.mpr hne
    omega
  have hlast : rosserPrefixLast L S.card = L[S.card - 1] :=
    rosserPrefixLast_eq_getElem hcard (by simpa [L] using hlen.ge)
  obtain ⟨i, hi, hpi⟩ :=
    List.mem_iff_getElem.mp ((rosserPrimeList_mem S p).mpr hp)
  have hile : i ≤ S.card - 1 := by omega
  rcases lt_or_eq_of_le hile with hlt | heq
  · have hgt : L[i] > L[S.card - 1] := by
      exact (rosserPrimeList_sorted S).getElem_gt_getElem_of_lt hlt
    rw [← hpi, hlast]
    exact Nat.le_of_lt hgt
  · subst i
    rw [← hpi, hlast]

theorem rosserPrefixProduct_append_left_eq {L M : List ℕ} {k : ℕ}
    (hkl : k ≤ L.length) :
    rosserPrefixProduct (L ++ M) k = rosserPrefixProduct L k := by
  unfold rosserPrefixProduct
  rw [List.take_append_of_le_length hkl]

theorem rosserPrefixLast_append_left_eq {L M : List ℕ} {k : ℕ}
    (hk : 1 ≤ k) (hkl : k ≤ L.length) :
    rosserPrefixLast (L ++ M) k = rosserPrefixLast L k := by
  rw [rosserPrefixLast_eq_getElem hk (by simp; omega),
    rosserPrefixLast_eq_getElem hk hkl]
  exact List.getElem_append_left (by omega)

theorem rosserPrefixProduct_take_eq {L : List ℕ} {j k : ℕ}
    (hkj : k ≤ j) :
    rosserPrefixProduct (L.take j) k = rosserPrefixProduct L k := by
  unfold rosserPrefixProduct
  rw [List.take_take, Nat.min_eq_left hkj]

theorem rosserPrefixLast_take_eq {L : List ℕ} {j k : ℕ}
    (hk : 1 ≤ k) (hkj : k ≤ j) (hj : j ≤ L.length) :
    rosserPrefixLast (L.take j) k = rosserPrefixLast L k := by
  rw [rosserPrefixLast_eq_getElem hk (by simp [List.length_take, Nat.min_eq_left hj]; omega),
    rosserPrefixLast_eq_getElem hk (by omega)]
  simp [List.getElem_take]

/-- The integer `d_j p_j^beta` in the blueprint's tested-prefix condition. -/
def rosserPrefixWeight (L : List ℕ) (j : ℕ) : ℕ :=
  rosserPrefixProduct L j * rosserPrefixLast L j ^ 513

theorem rosserPrefixProduct_succ_le_previous_weight {L : List ℕ} {j : ℕ}
    (hsorted : L.SortedGT) (hpositive : ∀ p ∈ L, 1 ≤ p)
    (hj : 1 ≤ j) (hjlt : j < L.length) :
    rosserPrefixProduct L (j + 1) ≤ rosserPrefixWeight L j := by
  have hjlen : j ≤ L.length := hjlt.le
  have hlast : L[j] ≤ rosserPrefixLast L j := by
    rw [rosserPrefixLast_eq_getElem hj hjlen]
    exact (hsorted.getElem_lt_getElem_iff).2 (by omega) |>.le
  have hlastpos : 0 < rosserPrefixLast L j := by
    rw [rosserPrefixLast_eq_getElem hj hjlen]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (hpositive _ (List.getElem_mem (by omega)))
  have hpowlower : L[j] ≤ rosserPrefixLast L j ^ 513 :=
    le_trans hlast (Nat.le_self_pow (by norm_num : 513 ≠ 0) _)
  rw [rosserPrefixProduct_succ hjlt, rosserPrefixWeight]
  exact Nat.mul_le_mul_left _ hpowlower

theorem rosserPrefixWeight_take_eq {L : List ℕ} {j k : ℕ}
    (hk : 1 ≤ k) (hkj : k ≤ j) (hj : j ≤ L.length) :
    rosserPrefixWeight (L.take j) k = rosserPrefixWeight L k := by
  simp only [rosserPrefixWeight, rosserPrefixProduct_take_eq hkj,
    rosserPrefixLast_take_eq hk hkj hj]

/-- A tested prefix has positive length, lies in the list, and has parity `nu`. -/
def rosserTestedPrefixes (L : List ℕ) (nu : Fin 2) (y : ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ L.length → j % 2 = nu.val →
    (rosserPrefixWeight L j : ℝ) < y

/-- A subset is retained when every tested prefix passes the strict cutoff. -/
def rosserRetained (z y : ℝ) (nu : Fin 2) (S : Finset ℕ) : Prop :=
  S ⊆ sievePrimesBelow z ∧
    rosserTestedPrefixes (rosserPrimeList S) nu y

/-- A nonempty subset whose final prefix is the first failing tested prefix. -/
def rosserStoppingPrefix (z y : ℝ) (nu : Fin 2) (S : Finset ℕ) : Prop :=
  S.Nonempty ∧
    S ⊆ sievePrimesBelow z ∧
    S.card % 2 = nu.val ∧
    (∀ j, 1 ≤ j → j < S.card → j % 2 = nu.val →
      (rosserPrefixWeight (rosserPrimeList S) j : ℝ) < y) ∧
    y ≤ (rosserPrefixWeight (rosserPrimeList S) S.card : ℝ)

theorem rosserPrefixWeight_append_left_eq {L M : List ℕ} {k : ℕ}
    (hk : 1 ≤ k) (hkl : k ≤ L.length) :
    rosserPrefixWeight (L ++ M) k = rosserPrefixWeight L k := by
  simp only [rosserPrefixWeight, rosserPrefixProduct_append_left_eq hkl,
    rosserPrefixLast_append_left_eq hk hkl]

theorem rosserPrimeList_stopping_union_eq_append {z y : ℝ} {nu : Fin 2}
    {P E : Finset ℕ} (hstop : rosserStoppingPrefix z y nu P)
    (hbelow : ∀ q ∈ E, q < rosserPrefixLast (rosserPrimeList P) P.card) :
    rosserPrimeList (P ∪ E) = rosserPrimeList P ++ rosserPrimeList E := by
  apply rosserPrimeList_union_eq_append
  intro p hp q hq
  have hple := rosserPrimeList_mem_ge_last hstop.1 hp
  have hqlt := hbelow q hq
  omega

theorem not_rosserRetained_of_stopping_extension {z y : ℝ} {nu : Fin 2}
    {P E : Finset ℕ} (hstop : rosserStoppingPrefix z y nu P)
    (hE : E ⊆ sievePrimesBelow z)
    (hbelow : ∀ q ∈ E, q < rosserPrefixLast (rosserPrimeList P) P.card) :
    ¬ rosserRetained z y nu (P ∪ E) := by
  have hsub : P ∪ E ⊆ sievePrimesBelow z := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hstop.2.1 hp
    · exact hE hp
  have hlen : P.card ≤ (rosserPrimeList (P ∪ E)).length := by
    rw [rosserPrimeList_length]
    exact Finset.card_le_card (Finset.subset_union_left)
  have hpfx : rosserPrefixWeight (rosserPrimeList (P ∪ E)) P.card =
      rosserPrefixWeight (rosserPrimeList P) P.card := by
    rw [rosserPrimeList_stopping_union_eq_append hstop hbelow]
    apply rosserPrefixWeight_append_left_eq
    · have hpos := Finset.card_pos.mpr hstop.1
      omega
    · rw [rosserPrimeList_length]
  intro hret
  have hbad := hret.2 P.card (by
    have := Finset.card_pos.mpr hstop.1
    omega) hlen hstop.2.2.1
  have hbad' :
      (rosserPrefixWeight (rosserPrimeList P) P.card : ℝ) < y := by
    simpa [hpfx] using hbad

  have hlarge : y ≤ (rosserPrefixWeight (rosserPrimeList P) P.card : ℝ) :=
    hstop.2.2.2.2
  exact (not_lt_of_ge hlarge) hbad'

theorem rosserStoppingPrefix_unique_prefix {z y : ℝ} {nu : Fin 2}
    {S P Q E F : Finset ℕ}
    (hstopP : rosserStoppingPrefix z y nu P)
    (hstopQ : rosserStoppingPrefix z y nu Q)
    (hunionP : S = P ∪ E)
    (hunionQ : S = Q ∪ F)
    (hbelowP : ∀ q ∈ E, q < rosserPrefixLast (rosserPrimeList P) P.card)
    (hbelowQ : ∀ q ∈ F, q < rosserPrefixLast (rosserPrimeList Q) Q.card) :
    P = Q := by
  have hlistP : rosserPrimeList S = rosserPrimeList P ++ rosserPrimeList E := by
    rw [hunionP]
    exact rosserPrimeList_stopping_union_eq_append hstopP hbelowP
  have hlistQ : rosserPrimeList S = rosserPrimeList Q ++ rosserPrimeList F := by
    rw [hunionQ]
    exact rosserPrimeList_stopping_union_eq_append hstopQ hbelowQ
  have hposP : 1 ≤ P.card := by
    have := Finset.card_pos.mpr hstopP.1
    omega
  have hposQ : 1 ≤ Q.card := by
    have := Finset.card_pos.mpr hstopQ.1
    omega
  have hcardEq : P.card = Q.card := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hboundP : P.card ≤ (rosserPrimeList P).length := by
        rw [rosserPrimeList_length]
      have hboundQ : P.card ≤ (rosserPrimeList Q).length := by
        rw [rosserPrimeList_length]
        omega
      have hweight : rosserPrefixWeight (rosserPrimeList P) P.card =
          rosserPrefixWeight (rosserPrimeList Q) P.card := by
        calc
          _ = rosserPrefixWeight
              (rosserPrimeList P ++ rosserPrimeList E) P.card :=
                (rosserPrefixWeight_append_left_eq hposP hboundP).symm
          _ = rosserPrefixWeight (rosserPrimeList S) P.card := by rw [← hlistP]
          _ = rosserPrefixWeight
              (rosserPrimeList Q ++ rosserPrimeList F) P.card := by rw [hlistQ]
          _ = _ := rosserPrefixWeight_append_left_eq hposP hboundQ
      have hstrict := hstopQ.2.2.2.1 P.card hposP hlt hstopP.2.2.1
      have hstrictP :
          (rosserPrefixWeight (rosserPrimeList P) P.card : ℝ) < y := by
        simpa [hweight] using hstrict
      exact (not_lt_of_ge hstopP.2.2.2.2) hstrictP
    · have hboundQ : Q.card ≤ (rosserPrimeList Q).length := by
        rw [rosserPrimeList_length]
      have hboundP : Q.card ≤ (rosserPrimeList P).length := by
        rw [rosserPrimeList_length]
        omega
      have hweight : rosserPrefixWeight (rosserPrimeList Q) Q.card =
          rosserPrefixWeight (rosserPrimeList P) Q.card := by
        calc
          _ = rosserPrefixWeight
              (rosserPrimeList Q ++ rosserPrimeList F) Q.card :=
                (rosserPrefixWeight_append_left_eq hposQ hboundQ).symm
          _ = rosserPrefixWeight (rosserPrimeList S) Q.card := by rw [← hlistQ]
          _ = rosserPrefixWeight
              (rosserPrimeList P ++ rosserPrimeList E) Q.card := by rw [hlistP]
          _ = _ := rosserPrefixWeight_append_left_eq hposQ hboundP
      have hstrict := hstopP.2.2.2.1 Q.card hposQ hgt hstopQ.2.2.1
      have hstrictQ :
          (rosserPrefixWeight (rosserPrimeList Q) Q.card : ℝ) < y := by
        simpa [hweight] using hstrict
      exact (not_lt_of_ge hstopQ.2.2.2.2) hstrictQ
  have hprefixP : rosserPrimeList P = (rosserPrimeList S).take P.card := by
    calc
      rosserPrimeList P = (rosserPrimeList P).take P.card := by
        simp [rosserPrimeList_length]
      _ = (rosserPrimeList P ++ rosserPrimeList E).take P.card :=
        (List.take_append_of_le_length (by rw [rosserPrimeList_length])).symm
      _ = (rosserPrimeList S).take P.card := by rw [← hlistP]
  have hprefixQ : rosserPrimeList Q = (rosserPrimeList S).take Q.card := by
    calc
      rosserPrimeList Q = (rosserPrimeList Q).take Q.card := by
        simp [rosserPrimeList_length]
      _ = (rosserPrimeList Q ++ rosserPrimeList F).take Q.card :=
        (List.take_append_of_le_length (by rw [rosserPrimeList_length])).symm
      _ = (rosserPrimeList S).take Q.card := by rw [← hlistQ]
  have hlistEq : rosserPrimeList P = rosserPrimeList Q := by
    rw [hprefixP, hcardEq, ← hprefixQ]
  have htoFinset := congrArg List.toFinset hlistEq
  simpa [rosserPrimeList] using htoFinset

theorem rosserStoppingPrefix_unique_tail {S P Q E F : Finset ℕ}
    (hunionP : S = P ∪ E) (hunionQ : S = Q ∪ F)
    (hdisjP : Disjoint P E) (hdisjQ : Disjoint Q F) (hPQ : P = Q) :
    E = F := by
  have hE : E = S \ P := by
    rw [hunionP, Finset.union_sdiff_cancel_left hdisjP]
  have hF : F = S \ Q := by
    rw [hunionQ, Finset.union_sdiff_cancel_left hdisjQ]
  rw [hE, hF, hPQ]

/-- The finite family of retained subsets of primes below `z`. -/
def rosserRetainedSubsets (z y : ℝ) (nu : Fin 2) : Finset (Finset ℕ) :=
  (sievePrimesBelow z).powerset.filter (rosserRetained z y nu)

def rosserNonretainedSubsets (z y : ℝ) (nu : Fin 2) : Finset (Finset ℕ) :=
  (sievePrimesBelow z).powerset.filter fun S => ¬ rosserRetained z y nu S

/-- The finite family of first-failing stopping prefixes. -/
def rosserStoppingPrefixes (z y : ℝ) (nu : Fin 2) : Finset (Finset ℕ) :=
  (sievePrimesBelow z).powerset.filter (rosserStoppingPrefix z y nu)

/-- The monomial associated with a finite prime subset in the stopping identity. -/
def rosserSubsetMonomial (x : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, x p

/-- Primes below the final prime of a stopping prefix. -/
def rosserBelowLastPrimes (z : ℝ) (P : Finset ℕ) : Finset ℕ :=
  (sievePrimesBelow z).filter
    (fun q => q < rosserPrefixLast (rosserPrimeList P) P.card)

/-- Pairs consisting of a stopping prefix and any subset of primes below it. -/
def rosserStoppingExtensionPairs (z y : ℝ) (nu : Fin 2) :
    Finset (Σ P : Finset ℕ, Finset ℕ) :=
  (rosserStoppingPrefixes z y nu).sigma
    (fun P => (rosserBelowLastPrimes z P).powerset)

theorem rosserStoppingPrefix_disjoint_below {z y : ℝ} {nu : Fin 2}
    {P : Finset ℕ} (hstop : rosserStoppingPrefix z y nu P) :
    Disjoint P (rosserBelowLastPrimes z P) := by
  apply Finset.disjoint_left.mpr
  intro q hq hqbelow
  have hge := rosserPrimeList_mem_ge_last hstop.1 hq
  have hlt := (Finset.mem_filter.mp hqbelow).2
  omega

theorem rosserStoppingExtensionPair_not_retained {z y : ℝ} {nu : Fin 2}
    {pair : Σ P : Finset ℕ, Finset ℕ}
    (hpair : pair ∈ rosserStoppingExtensionPairs z y nu) :
    ¬ rosserRetained z y nu (pair.1 ∪ pair.2) := by
  rcases Finset.mem_sigma.mp hpair with ⟨hP, hE⟩
  have hstop : rosserStoppingPrefix z y nu pair.1 :=
    (Finset.mem_filter.mp hP).2
  have hEsmall : pair.2 ⊆ rosserBelowLastPrimes z pair.1 :=
    Finset.mem_powerset.mp hE
  have hEsieve : pair.2 ⊆ sievePrimesBelow z := by
    intro q hq
    exact (Finset.mem_filter.mp (hEsmall hq)).1
  have hbelow : ∀ q ∈ pair.2,
      q < rosserPrefixLast (rosserPrimeList pair.1) pair.1.card := by
    intro q hq
    exact (Finset.mem_filter.mp (hEsmall hq)).2
  exact not_rosserRetained_of_stopping_extension hstop hEsieve hbelow

theorem rosserStopping_extension_sum {P A : Finset ℕ} (x : ℕ → ℝ)
    (hdisj : Disjoint P A) :
    (∑ E ∈ A.powerset,
      (-1 : ℝ) ^ (P ∪ E).card * rosserSubsetMonomial x (P ∪ E)) =
      (-1 : ℝ) ^ P.card * rosserSubsetMonomial x P *
        ∏ q ∈ A, (1 - x q) := by
  have hsum :
      (∑ E ∈ A.powerset,
        (-1 : ℝ) ^ (P ∪ E).card * rosserSubsetMonomial x (P ∪ E)) =
        (-1 : ℝ) ^ P.card * rosserSubsetMonomial x P *
          ∑ E ∈ A.powerset,
            (-1 : ℝ) ^ E.card * rosserSubsetMonomial x E := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    have hEA : E ⊆ A := Finset.mem_powerset.mp hE
    have hdisjPE : Disjoint P E := hdisj.mono_right hEA
    simp only [rosserSubsetMonomial]
    rw [Finset.card_union_of_disjoint hdisjPE,
      Finset.prod_union hdisjPE]
    rw [pow_add]
    ring
  have hexp :
      (∑ E ∈ A.powerset,
        (-1 : ℝ) ^ E.card * rosserSubsetMonomial x E) =
        ∏ q ∈ A, (1 - x q) := by
    simpa [rosserSubsetMonomial] using
      (Finset.prod_sub (fun _ => (1 : ℝ)) x A).symm
  rw [hsum, hexp]

/-- The canonical set of primes below `z` dividing `d`. -/
def rosserPrimeSupport (z : ℝ) (d : ℕ) : Finset ℕ :=
  (sievePrimesBelow z).filter fun p => p ∣ d

/-- Rosser's coefficient, evaluated on the canonical prime support of `d`.
The product equality selects precisely the squarefree products represented by
retained subsets. -/
noncomputable def rosserXi (z y : ℝ) (nu : Fin 2) (d : ℕ) : ℝ :=
  if rosserRetained z y nu (rosserPrimeSupport z d) ∧
      (rosserPrimeSupport z d).prod id = d then
    (-1 : ℝ) ^ (rosserPrimeSupport z d).card
  else 0

theorem rosser_empty_retained (z y : ℝ) (nu : Fin 2) :
    rosserRetained z y nu ∅ := by
  constructor
  · exact Finset.empty_subset _
  · intro j hj hjlen _
    have : j ≤ 0 := by simpa [rosserPrimeList] using hjlen
    omega

theorem rosserPrimeSupport_one (z : ℝ) : rosserPrimeSupport z 1 = ∅ := by
  ext p
  simp only [rosserPrimeSupport, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hpd⟩
    have hprime : p.Prime := by
      unfold sievePrimesBelow at hp
      exact (Finset.mem_filter.mp hp).2.1
    exact False.elim (hprime.not_dvd_one hpd)
  · intro h
    simpa using h

theorem rosserXi_one (z y : ℝ) (nu : Fin 2) : rosserXi z y nu 1 = 1 := by
  simp [rosserXi, rosserPrimeSupport_one, rosser_empty_retained]

theorem rosserXi_spec {z y : ℝ} {nu : Fin 2} {d : ℕ}
    (hxi : rosserXi z y nu d ≠ 0) :
    rosserRetained z y nu (rosserPrimeSupport z d) ∧
      (rosserPrimeSupport z d).prod id = d := by
  unfold rosserXi at hxi
  split_ifs at hxi with h
  · exact h
  · simp at hxi

theorem abs_rosserXi_le_one (z y : ℝ) (nu : Fin 2) (d : ℕ) :
    |rosserXi z y nu d| ≤ 1 := by
  unfold rosserXi
  split_ifs <;> simp

theorem rosserPrimeList_prod_eq_finset (S : Finset ℕ) :
    (rosserPrimeList S).prod = S.prod id := by
  calc
    (rosserPrimeList S).prod = ((rosserPrimeList S).map id).prod := by simp
    _ = (rosserPrimeList S).toFinset.prod id :=
      (List.prod_toFinset id (rosserPrimeList_nodup S)).symm
    _ = S.prod id := by simp [rosserPrimeList]

theorem rosserRetained_product_lt_of_final_tested {z y : ℝ}
    {nu : Fin 2} {S : Finset ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y) (hret : rosserRetained z y nu S)
    (hfinal : S.card % 2 = nu.val) : ((S.prod id : ℕ) : ℝ) < y := by
  have hy2 : 2 ≤ y := le_trans hz hzy
  classical
  let L := rosserPrimeList S
  have hlen : L.length = S.card := rosserPrimeList_length S
  by_cases hempty : S.card = 0
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp hempty
    subst S
    simp
    linarith
  · have hpos : 1 ≤ S.card := by omega
    have htest := hret.2 S.card hpos hlen.symm.le hfinal
    have hlastpos : 0 < rosserPrefixLast L S.card := by
      rw [rosserPrefixLast_eq_getElem hpos (by simpa [hlen])]
      have hmem := List.getElem_mem (l := L) (n := S.card - 1) (by omega)
      have hS : L[S.card - 1] ∈ S := (rosserPrimeList_mem S _).mp hmem
      have hp := hret.1 hS
      unfold sievePrimesBelow at hp
      exact (Finset.mem_filter.mp hp).2.1.pos
    have hprefix : rosserPrefixProduct L S.card = S.prod id := by
      rw [← hlen]
      change rosserPrefixProduct L L.length = S.prod id
      rw [rosserPrefixProduct_length, rosserPrimeList_prod_eq_finset]
    have hfactor : S.prod id ≤ rosserPrefixWeight L S.card := by
      rw [rosserPrefixWeight, hprefix]
      exact Nat.le_mul_of_pos_right _ (pow_pos hlastpos _)
    exact lt_of_le_of_lt (by exact_mod_cast hfactor) htest

theorem rosserRetained_product_lt_of_final_untested_ge_two {z y : ℝ}
    {nu : Fin 2} {S : Finset ℕ}
    (hret : rosserRetained z y nu S)
    (hfinal : S.card % 2 ≠ nu.val) (hm : 2 ≤ S.card) :
    ((S.prod id : ℕ) : ℝ) < y := by
  let L := rosserPrimeList S
  have hlen : L.length = S.card := rosserPrimeList_length S
  have hj : 1 ≤ S.card - 1 := by omega
  have hjlen : S.card - 1 ≤ L.length := by
    calc
      S.card - 1 ≤ S.card := by omega
      _ = L.length := hlen.symm
  have hjpar : (S.card - 1) % 2 = nu.val := by omega
  have htest := hret.2 (S.card - 1) hj hjlen hjpar
  have hpositive : ∀ p ∈ L, 1 ≤ p := by
    intro p hp
    have hpS := (rosserPrimeList_mem S p).mp hp
    have hpz := hret.1 hpS
    unfold sievePrimesBelow at hpz
    have hprime := (Finset.mem_filter.mp hpz).2.1
    exact le_trans (by norm_num : 1 ≤ 2) hprime.two_le
  have hjlt : S.card - 1 < L.length := by
    calc
      S.card - 1 < S.card := by omega
      _ = L.length := hlen.symm
  have hbound := rosserPrefixProduct_succ_le_previous_weight
    (rosserPrimeList_sorted S) hpositive hj hjlt
  have hprefix : rosserPrefixProduct L S.card = S.prod id := by
    rw [← hlen]
    rw [rosserPrefixProduct_length, rosserPrimeList_prod_eq_finset]
  have hbound' : S.prod id ≤ rosserPrefixWeight L (S.card - 1) := by
    calc
      S.prod id = rosserPrefixProduct L S.card := hprefix.symm
      _ = rosserPrefixProduct L ((S.card - 1) + 1) := by congr 1 <;> omega
      _ ≤ rosserPrefixWeight L (S.card - 1) := by simpa [L] using hbound
  exact lt_of_le_of_lt (by exact_mod_cast hbound') htest

theorem sieveSubset_product_lt_of_card_eq_one {z : ℝ} {S : Finset ℕ}
    (hS : S ⊆ sievePrimesBelow z) (hcard : S.card = 1) :
    ((S.prod id : ℕ) : ℝ) < z := by
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
  have hp : p ∈ sievePrimesBelow z := hS (by simp)
  unfold sievePrimesBelow at hp
  have hpz := (Finset.mem_filter.mp hp).2.2
  simpa using hpz

theorem rosserRetained_product_lt {z y : ℝ} {nu : Fin 2} {S : Finset ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y) (hret : rosserRetained z y nu S) :
    ((S.prod id : ℕ) : ℝ) < y := by
  by_cases hempty : S.card = 0
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp hempty
    subst S
    simp
    linarith [le_trans hz hzy]
  · by_cases hfinal : S.card % 2 = nu.val
    · exact rosserRetained_product_lt_of_final_tested hz hzy hret hfinal
    · by_cases hsingleton : S.card = 1
      · exact lt_of_lt_of_le
          (sieveSubset_product_lt_of_card_eq_one hret.1 hsingleton) hzy
      · have hnu : nu.val < 2 := nu.isLt
        have hm : 2 ≤ S.card := by omega
        exact rosserRetained_product_lt_of_final_untested_ge_two hret hfinal hm

theorem rosserXi_eq_zero_of_ge {z y : ℝ} {nu : Fin 2} {d : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y) (hdy : y ≤ d) :
    rosserXi z y nu d = 0 := by
  by_contra hne
  obtain ⟨hret, hprod⟩ := rosserXi_spec hne
  have hprodlt := rosserRetained_product_lt hz hzy hret
  rw [hprod] at hprodlt
  exact (not_lt_of_ge (by exact_mod_cast hdy)) hprodlt

theorem primeFinsetProduct_injective {S T : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (hprod : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  ext p
  constructor
  · intro hpS
    have hpprime := hS p hpS
    have hpdiv : p ∣ ∏ q ∈ T, q := by
      rw [← hprod]
      exact Finset.dvd_prod_of_mem (fun q => q) hpS
    obtain ⟨q, hqT, hpq⟩ := (hpprime.prime.dvd_finsetProd_iff (fun q => q)).mp hpdiv
    have hqprime := hT q hqT
    rcases hqprime.eq_one_or_self_of_dvd p hpq with hqone | hqp
    · exact False.elim (hpprime.ne_one hqone)
    · simpa [hqp] using hqT
  · intro hpT
    have hpprime := hT p hpT
    have hpdiv : p ∣ ∏ q ∈ S, q := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem (fun q => q) hpT
    obtain ⟨q, hqS, hpq⟩ := (hpprime.prime.dvd_finsetProd_iff (fun q => q)).mp hpdiv
    have hqprime := hS q hqS
    rcases hqprime.eq_one_or_self_of_dvd p hpq with hqone | hqp
    · exact False.elim (hpprime.ne_one hqone)
    · simpa [hqp] using hqS

theorem rosserPrimeSupport_eq_of_product {z : ℝ} {S : Finset ℕ} {d : ℕ}
    (hS : S ⊆ sievePrimesBelow z) (hprod : (∏ p ∈ S, p) = d) :
    rosserPrimeSupport z d = S := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpz, hpd⟩
    have hpprime : p.Prime := by
      unfold sievePrimesBelow at hpz
      exact (Finset.mem_filter.mp hpz).2.1
    have hpdiv : p ∣ ∏ q ∈ S, q := by
      rw [hprod]
      exact hpd
    obtain ⟨q, hqS, hpq⟩ :=
      (hpprime.prime.dvd_finsetProd_iff (S := S) (fun q => q)).mp hpdiv
    have hqprime : q.Prime := by
      have hqz := hS hqS
      unfold sievePrimesBelow at hqz
      exact (Finset.mem_filter.mp hqz).2.1
    rcases hqprime.eq_one_or_self_of_dvd p hpq with hqone | hqp
    · have hpprime : p.Prime := by
        unfold sievePrimesBelow at hpz
        exact (Finset.mem_filter.mp hpz).2.1
      exact False.elim (hpprime.ne_one hqone)
    · simpa [hqp] using hqS
  · intro hpS
    have hpz := hS hpS
    have hpprime : p.Prime := by
      unfold sievePrimesBelow at hpz
      exact (Finset.mem_filter.mp hpz).2.1
    apply Finset.mem_filter.mpr
    refine ⟨hpz, ?_⟩
    rw [← hprod]
    exact Finset.dvd_prod_of_mem (fun q => q) hpS

theorem rosserXi_eq_sign_of_retained_product {z y : ℝ} {nu : Fin 2}
    {S : Finset ℕ} {d : ℕ} (hret : rosserRetained z y nu S)
    (hprod : (∏ p ∈ S, p) = d) :
    rosserXi z y nu d = (-1 : ℝ) ^ S.card := by
  have hsupport : rosserPrimeSupport z d = S :=
    rosserPrimeSupport_eq_of_product hret.1 hprod
  simp [rosserXi, hsupport, hret, hprod]

theorem exists_min_nat_index {n : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : ∃ j, 1 ≤ j ∧ j ≤ n ∧ P j) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧ P j ∧
      ∀ k, 1 ≤ k → k < j → k ≤ n → ¬ P k := by
  classical
  let F : Finset ℕ := (Finset.range (n + 1)).filter fun j => 1 ≤ j ∧ P j
  have hF : F.Nonempty := by
    rcases h with ⟨j, hj, hjn, hP⟩
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj, hP⟩⟩
  let j := F.min' hF
  have hjF : j ∈ F := Finset.min'_mem F hF
  have hj : 1 ≤ j := (Finset.mem_filter.mp hjF).2.1
  have hjP : P j := (Finset.mem_filter.mp hjF).2.2
  have hjn : j ≤ n := by
    have hrange := (Finset.mem_range.mp (Finset.mem_filter.mp hjF).1)
    omega
  refine ⟨j, hj, hjn, hjP, ?_⟩
  intro k hk hkj hkn hPk
  have hkF : k ∈ F := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hk, hPk⟩
  have hmin := F.min'_le k hkF
  omega

theorem exists_first_failing_rosserPrefix {L : List ℕ} {nu : Fin 2} {y : ℝ}
    (hfail : ¬ rosserTestedPrefixes L nu y) :
    ∃ j, 1 ≤ j ∧ j ≤ L.length ∧ j % 2 = nu.val ∧
      y ≤ (rosserPrefixWeight L j : ℝ) ∧
      ∀ k, 1 ≤ k → k < j → k ≤ L.length → k % 2 = nu.val →
        (rosserPrefixWeight L k : ℝ) < y := by
  have hex : ∃ j, 1 ≤ j ∧ j ≤ L.length ∧
      j % 2 = nu.val ∧ y ≤ (rosserPrefixWeight L j : ℝ) := by
    by_contra hno
    apply hfail
    intro j hj hjlen hpar
    by_contra hweight
    exact hno ⟨j, hj, hjlen, hpar, le_of_not_gt hweight⟩
  let P : ℕ → Prop := fun j =>
    j % 2 = nu.val ∧ y ≤ (rosserPrefixWeight L j : ℝ)
  obtain ⟨j, hj, hjlen, hjP, hmin⟩ := exists_min_nat_index (P := P) hex
  refine ⟨j, hj, hjlen, hjP.1, hjP.2, ?_⟩
  intro k hk hkj hklen hkpar
  have hnot : ¬ P k := hmin k hk hkj hklen
  have hnotge : ¬ y ≤ (rosserPrefixWeight L k : ℝ) := by
    intro hle
    exact hnot ⟨hkpar, hle⟩
  exact lt_of_not_ge hnotge

/-- In a strictly decreasing prime list, every element after a prefix is
strictly smaller than the last prime in that prefix. -/
theorem rosserPrimeList_drop_lt_prefixLast {L : List ℕ} {j q : ℕ}
    (hsorted : L.SortedGT) (hj : 1 ≤ j) (hjlen : j ≤ L.length)
    (hq : q ∈ L.drop j) : q < rosserPrefixLast L j := by
  obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hq
  have hidx : i + j < L.length := by
    simp only [List.length_drop] at hi
    omega
  have hpos : j - 1 < i + j := by omega
  have hval : L[i + j] < L[j - 1] :=
    (hsorted.getElem_lt_getElem_iff).2 hpos
  rw [← hqi, List.getElem_drop, rosserPrefixLast_eq_getElem hj hjlen]
  simpa [Nat.add_comm] using hval

/-- A nonretained subset has a canonical finite prefix that satisfies the
blueprint's stopping-prefix conditions. -/
theorem exists_rosserStoppingPrefix_of_not_retained {z y : ℝ} {nu : Fin 2}
    {S : Finset ℕ} (hS : S ⊆ sievePrimesBelow z)
    (hnot : ¬ rosserRetained z y nu S) :
    ∃ P E, P ⊆ S ∧ rosserStoppingPrefix z y nu P ∧ S = P ∪ E ∧
      Disjoint P E ∧
      ∀ q ∈ E, q < rosserPrefixLast (rosserPrimeList P) P.card := by
  let L := rosserPrimeList S
  have hfail : ¬ rosserTestedPrefixes L nu y := by
    intro htested
    exact hnot ⟨hS, htested⟩
  obtain ⟨j, hj, hjlen, hjpar, hjweight, hjmin⟩ :=
    exists_first_failing_rosserPrefix hfail
  let P := rosserPrefixFinset L j
  have hnd : L.Nodup := rosserPrimeList_nodup S
  have hsorted : L.SortedGT := rosserPrimeList_sorted S
  have hcard : P.card = j := rosserPrefixFinset_card hnd hjlen
  have hPnon : P.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hPS : P ⊆ S := by
    intro p hp
    apply (rosserPrimeList_mem S p).mp
    exact (List.take_sublist j L).subset (List.mem_toFinset.mp hp)
  have hstop : rosserStoppingPrefix z y nu P := by
    refine ⟨hPnon, hPS.trans hS, ?_, ?_, ?_⟩
    · simpa [hcard] using hjpar
    · intro k hk hkj hpar
      have hkj' : k < j := by simpa [hcard] using hkj
      rw [rosserPrimeList_prefixFinset_eq hnd hsorted]
      rw [rosserPrefixWeight_take_eq hk (by omega) hjlen]
      exact hjmin k hk hkj' (by omega) hpar
    · rw [rosserPrimeList_prefixFinset_eq hnd hsorted, hcard,
        rosserPrefixWeight_take_eq hj le_rfl hjlen]
      exact hjweight
  let E := (L.drop j).toFinset
  have hunion : P ∪ E = S := by
    have h := rosserPrefixFinset_union_drop L j
    have hsortto : (rosserPrimeList S).toFinset = S := by
      simp [rosserPrimeList]
    simpa [P, E, L, rosserPrefixFinset, hsortto] using h
  have hdisj : Disjoint P E := by
    have h := rosserPrefixFinset_disjoint_drop (L := L) (j := j) hnd
    simpa [P, E] using h
  have hbelow : ∀ q ∈ E,
      q < rosserPrefixLast (rosserPrimeList P) P.card := by
    have hPList : rosserPrimeList P = L.take j := by
      simpa [P] using rosserPrimeList_prefixFinset_eq
        (L := L) (j := j) hnd hsorted
    have hlast : rosserPrefixLast (rosserPrimeList P) P.card =
        rosserPrefixLast L j := by
      rw [hPList, hcard]
      exact rosserPrefixLast_take_eq hj le_rfl hjlen
    intro q hq
    rw [hlast]
    exact rosserPrimeList_drop_lt_prefixLast hsorted hj hjlen
      (List.mem_toFinset.mp hq)
  exact ⟨P, E, hPS, hstop, hunion.symm, hdisj, hbelow⟩

theorem exists_rosserStoppingExtensionPair_of_not_retained
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ}
    (hS : S ⊆ sievePrimesBelow z)
    (hnot : ¬ rosserRetained z y nu S) :
    ∃ pair ∈ rosserStoppingExtensionPairs z y nu,
      pair.1 ∪ pair.2 = S := by
  obtain ⟨P, E, hPS, hstop, hunion, hdisj, hbelow⟩ :=
    exists_rosserStoppingPrefix_of_not_retained hS hnot
  have hPmem : P ∈ rosserStoppingPrefixes z y nu := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr hstop.2.1, hstop⟩
  have hEsubS : E ⊆ S := by
    intro q hq
    rw [hunion]
    exact Finset.mem_union.mpr (Or.inr hq)
  have hEsieve : E ⊆ sievePrimesBelow z := hEsubS.trans hS
  have hEsmall : E ⊆ rosserBelowLastPrimes z P := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨hEsieve hq, hbelow q hq⟩
  have hpair : (⟨P, E⟩ : Σ P : Finset ℕ, Finset ℕ) ∈
      rosserStoppingExtensionPairs z y nu := by
    exact Finset.mem_sigma.mpr ⟨hPmem, Finset.mem_powerset.mpr hEsmall⟩
  exact ⟨⟨P, E⟩, hpair, hunion.symm⟩

theorem rosserStoppingExtensionPair_union_injective {z y : ℝ} {nu : Fin 2}
    {pair₁ pair₂ : Σ P : Finset ℕ, Finset ℕ}
    (h₁ : pair₁ ∈ rosserStoppingExtensionPairs z y nu)
    (h₂ : pair₂ ∈ rosserStoppingExtensionPairs z y nu)
    (hunions : pair₁.1 ∪ pair₁.2 = pair₂.1 ∪ pair₂.2) :
    pair₁ = pair₂ := by
  rcases Finset.mem_sigma.mp h₁ with ⟨hP₁, hE₁⟩
  rcases Finset.mem_sigma.mp h₂ with ⟨hP₂, hE₂⟩
  have hstop₁ : rosserStoppingPrefix z y nu pair₁.1 :=
    (Finset.mem_filter.mp hP₁).2
  have hstop₂ : rosserStoppingPrefix z y nu pair₂.1 :=
    (Finset.mem_filter.mp hP₂).2
  have hbelow₁ : ∀ q ∈ pair₁.2,
      q < rosserPrefixLast (rosserPrimeList pair₁.1) pair₁.1.card := by
    intro q hq
    exact (Finset.mem_filter.mp
      (Finset.mem_powerset.mp hE₁ hq)).2
  have hbelow₂ : ∀ q ∈ pair₂.2,
      q < rosserPrefixLast (rosserPrimeList pair₂.1) pair₂.1.card := by
    intro q hq
    exact (Finset.mem_filter.mp
      (Finset.mem_powerset.mp hE₂ hq)).2
  have hP : pair₁.1 = pair₂.1 :=
    rosserStoppingPrefix_unique_prefix hstop₁ hstop₂ rfl hunions hbelow₁ hbelow₂
  have hE : pair₁.2 = pair₂.2 :=
    rosserStoppingPrefix_unique_tail rfl hunions
      ((rosserStoppingPrefix_disjoint_below hstop₁).mono_right
        (Finset.mem_powerset.mp hE₁))
      ((rosserStoppingPrefix_disjoint_below hstop₂).mono_right
        (Finset.mem_powerset.mp hE₂)) hP
  cases pair₁ with
  | mk P₁ E₁ =>
    cases pair₂ with
    | mk P₂ E₂ =>
      simp only [Sigma.mk.injEq]
      exact ⟨hP, heq_of_eq hE⟩

theorem rosserStoppingExtensionPairs_sum_eq_nonretained {z y : ℝ}
    {nu : Fin 2} (x : ℕ → ℝ) :
    (∑ pair ∈ rosserStoppingExtensionPairs z y nu,
      (-1 : ℝ) ^ (pair.1 ∪ pair.2).card *
        rosserSubsetMonomial x (pair.1 ∪ pair.2)) =
      ∑ S ∈ rosserNonretainedSubsets z y nu,
        (-1 : ℝ) ^ S.card * rosserSubsetMonomial x S := by
  apply Finset.sum_bij (fun pair _ => pair.1 ∪ pair.2)
  · intro pair hpair
    rcases Finset.mem_sigma.mp hpair with ⟨hP, hE⟩
    have hstop : rosserStoppingPrefix z y nu pair.1 :=
      (Finset.mem_filter.mp hP).2
    have hPsub : pair.1 ⊆ sievePrimesBelow z := hstop.2.1
    have hEsub : pair.2 ⊆ sievePrimesBelow z := by
      intro q hq
      exact (Finset.mem_filter.mp
        (Finset.mem_powerset.mp hE hq)).1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (Finset.union_subset hPsub hEsub),
      rosserStoppingExtensionPair_not_retained hpair⟩
  · intro pair₁ hpair₁ pair₂ hpair₂ heq
    exact rosserStoppingExtensionPair_union_injective hpair₁ hpair₂ heq
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSpow, hSnot⟩
    obtain ⟨pair, hpair, heq⟩ :=
      exists_rosserStoppingExtensionPair_of_not_retained
        (Finset.mem_powerset.mp hSpow) hSnot
    exact ⟨pair, hpair, heq⟩
  · intro pair hpair
    rfl

theorem rosserStoppingExtensionPairs_sum_eq_stopping {z y : ℝ}
    {nu : Fin 2} (x : ℕ → ℝ) :
    (∑ pair ∈ rosserStoppingExtensionPairs z y nu,
      (-1 : ℝ) ^ (pair.1 ∪ pair.2).card *
        rosserSubsetMonomial x (pair.1 ∪ pair.2)) =
      ∑ P ∈ rosserStoppingPrefixes z y nu,
        (-1 : ℝ) ^ P.card * rosserSubsetMonomial x P *
          ∏ q ∈ rosserBelowLastPrimes z P, (1 - x q) := by
  rw [rosserStoppingExtensionPairs, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro P hP
  have hstop : rosserStoppingPrefix z y nu P :=
    (Finset.mem_filter.mp hP).2
  have hdisj := rosserStoppingPrefix_disjoint_below hstop
  exact rosserStopping_extension_sum x hdisj

theorem negOne_pow_eq_of_mod_two {n : ℕ} {nu : Fin 2}
    (h : n % 2 = nu.val) :
    (-1 : ℝ) ^ n = (-1 : ℝ) ^ nu.val := by
  have heven : Even n ↔ Even nu.val := by
    rw [even_iff_two_dvd, even_iff_two_dvd,
      Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
    omega
  exact neg_one_pow_congr heven

/-- The exact finite Rosser stopping identity from blueprint lemma `ls:stopping`. -/
theorem rosserStoppingIdentity (z y : ℝ) (nu : Fin 2) (x : ℕ → ℝ) :
    ∏ p ∈ sievePrimesBelow z, (1 - x p) =
      (∑ S ∈ rosserRetainedSubsets z y nu,
        (-1 : ℝ) ^ S.card * rosserSubsetMonomial x S) +
        (-1 : ℝ) ^ nu.val *
          ∑ P ∈ rosserStoppingPrefixes z y nu,
            rosserSubsetMonomial x P *
              ∏ q ∈ rosserBelowLastPrimes z P, (1 - x q) := by
  let f : Finset ℕ → ℝ := fun S =>
    (-1 : ℝ) ^ S.card * rosserSubsetMonomial x S
  have hexp :
      ∏ p ∈ sievePrimesBelow z, (1 - x p) =
        ∑ S ∈ (sievePrimesBelow z).powerset, f S := by
    simpa [f, rosserSubsetMonomial] using
      (Finset.prod_sub (fun _ => (1 : ℝ)) x (sievePrimesBelow z))
  have hsplit :
      (∑ S ∈ (sievePrimesBelow z).powerset, f S) =
        (∑ S ∈ rosserRetainedSubsets z y nu, f S) +
          ∑ S ∈ rosserNonretainedSubsets z y nu, f S := by
    simpa [rosserRetainedSubsets, rosserNonretainedSubsets] using
      (Finset.sum_filter_add_sum_filter_not
        ((sievePrimesBelow z).powerset) (rosserRetained z y nu) f).symm
  have hnonret := rosserStoppingExtensionPairs_sum_eq_nonretained
    (z := z) (y := y) (nu := nu) x
  have hpair := rosserStoppingExtensionPairs_sum_eq_stopping
    (z := z) (y := y) (nu := nu) x
  calc
    ∏ p ∈ sievePrimesBelow z, (1 - x p) =
        ∑ S ∈ (sievePrimesBelow z).powerset, f S := hexp
    _ = (∑ S ∈ rosserRetainedSubsets z y nu, f S) +
          ∑ S ∈ rosserNonretainedSubsets z y nu, f S := hsplit
    _ = (∑ S ∈ rosserRetainedSubsets z y nu, f S) +
          ∑ pair ∈ rosserStoppingExtensionPairs z y nu,
            (-1 : ℝ) ^ (pair.1 ∪ pair.2).card *
              rosserSubsetMonomial x (pair.1 ∪ pair.2) := by
      congr 1
      exact hnonret.symm
    _ = (∑ S ∈ rosserRetainedSubsets z y nu, f S) +
          ∑ P ∈ rosserStoppingPrefixes z y nu,
            (-1 : ℝ) ^ P.card * rosserSubsetMonomial x P *
              ∏ q ∈ rosserBelowLastPrimes z P, (1 - x q) := by
      congr 1
    _ = (∑ S ∈ rosserRetainedSubsets z y nu, f S) +
          (-1 : ℝ) ^ nu.val *
            ∑ P ∈ rosserStoppingPrefixes z y nu,
              rosserSubsetMonomial x P *
                ∏ q ∈ rosserBelowLastPrimes z P, (1 - x q) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      have hstop : rosserStoppingPrefix z y nu P :=
        (Finset.mem_filter.mp hP).2
      rw [negOne_pow_eq_of_mod_two hstop.2.2.1]
      ring

theorem natCoprime_sievePrimeProduct_iff {z : ℝ} {n : ℕ} :
    Nat.Coprime n (sievePrimeProduct z) ↔
      ∀ p ∈ sievePrimesBelow z, ¬ p ∣ n := by
  rw [sievePrimeProduct, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp hpd
    have hprime : p.Prime := by
      unfold sievePrimesBelow at hp
      exact (Finset.mem_filter.mp hp).2.1
    exact (hprime.coprime_iff_not_dvd).mp (Nat.coprime_comm.mp (h p hp)) hpd
  · intro h p hp
    have hprime : p.Prime := by
      unfold sievePrimesBelow at hp
      exact (Finset.mem_filter.mp hp).2.1
    exact Nat.coprime_comm.mp ((hprime.coprime_iff_not_dvd).2 (h p hp))

theorem rosserPrimeSubset_product_dvd_iff {z : ℝ} {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ sievePrimesBelow z) :
    S.prod id ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  constructor
  · intro hprod p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun q => q) hp) hprod
  · intro hall
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
        have hpz := hS (Finset.mem_insert_self p S)
        have hpp : p.Prime := by
          unfold sievePrimesBelow at hpz
          exact (Finset.mem_filter.mp hpz).2.1
        have hrest : S.prod id ∣ n := ih (by
          intro q hq
          exact hS (Finset.mem_insert_of_mem hq)) (by
          intro q hq
          exact hall q (Finset.mem_insert_of_mem hq))
        have hpdiv : p ∣ n := hall p (Finset.mem_insert_self p S)
        have hcop : p.Coprime (S.prod id) := by
          rw [Nat.coprime_prod_right_iff]
          intro q hq
          have hqz := hS (Finset.mem_insert_of_mem hq)
          have hqp : q.Prime := by
            unfold sievePrimesBelow at hqz
            exact (Finset.mem_filter.mp hqz).2.1
          apply (hpp.coprime_iff_not_dvd).2
          intro hpq
          rcases hqp.eq_one_or_self_of_dvd p hpq with hqone | hqp_eq
          · exact hpp.ne_one hqone
          · exact hp (hqp_eq ▸ hq)
        have hmul : p * S.prod id ∣ n :=
          Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpdiv hrest
        simpa [Finset.prod_insert, hp] using hmul

theorem rosserSubsetMonomial_divisibility_indicator {z : ℝ} {n : ℕ}
    {S : Finset ℕ} (hS : S ⊆ sievePrimesBelow z) :
    rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) S =
      if S.prod id ∣ n then 1 else 0 := by
  classical
  have hmon :
      rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) S =
        if ∀ p ∈ S, p ∣ n then 1 else 0 := by
    have hgeneric : ∀ T : Finset ℕ,
        rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) T =
          if ∀ p ∈ T, p ∣ n then 1 else 0 := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp [rosserSubsetMonomial]
      | @insert p T hp ih =>
          rw [rosserSubsetMonomial, Finset.prod_insert hp]
          simp only [Finset.forall_mem_insert]
          have ih' :
              (∏ q ∈ T, (if q ∣ n then (1 : ℝ) else 0)) =
                if ∀ q ∈ T, q ∣ n then 1 else 0 := by
            simpa [rosserSubsetMonomial] using ih
          by_cases hdiv : p ∣ n <;> simp [hdiv, ih']
    exact hgeneric S
  by_cases hall : ∀ p ∈ S, p ∣ n
  · have hdiv := (rosserPrimeSubset_product_dvd_iff hS).2 hall
    rw [hmon]
    rw [if_pos hall, if_pos hdiv]
  · have hdiv : ¬ S.prod id ∣ n := fun hd =>
      hall ((rosserPrimeSubset_product_dvd_iff hS).1 hd)
    rw [hmon]
    rw [if_neg hall, if_neg hdiv]

def rosserRetainedProductValues (z y : ℝ) (nu : Fin 2) : Finset ℕ :=
  (rosserRetainedSubsets z y nu).image (fun S => S.prod id)

theorem rosserRetainedProductValues_injOn {z y : ℝ} {nu : Fin 2} :
    Set.InjOn (fun S : Finset ℕ => S.prod id)
      (rosserRetainedSubsets z y nu : Set (Finset ℕ)) := by
  intro S hS T hT hprod
  apply primeFinsetProduct_injective
  · intro p hp
    have hpz := (Finset.mem_filter.mp hS).2.1 hp
    unfold sievePrimesBelow at hpz
    exact (Finset.mem_filter.mp hpz).2.1
  · intro p hp
    have hpz := (Finset.mem_filter.mp hT).2.1 hp
    unfold sievePrimesBelow at hpz
    exact (Finset.mem_filter.mp hpz).2.1
  · exact hprod

theorem rosserRetainedSubset_sum_eq_productValues {z y : ℝ}
    {nu : Fin 2} (n : ℕ) :
    (∑ S ∈ rosserRetainedSubsets z y nu,
      (-1 : ℝ) ^ S.card *
        rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) S) =
      ∑ d ∈ rosserRetainedProductValues z y nu,
        if d ∣ n then rosserXi z y nu d else 0 := by
  let f : ℕ → ℝ := fun d => if d ∣ n then rosserXi z y nu d else 0
  have hterm : ∀ S ∈ rosserRetainedSubsets z y nu,
      (-1 : ℝ) ^ S.card *
        rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) S =
          f (S.prod id) := by
    intro S hS
    have hret : rosserRetained z y nu S := (Finset.mem_filter.mp hS).2
    rw [rosserSubsetMonomial_divisibility_indicator hret.1]
    by_cases hd : (∏ p ∈ S, p) ∣ n
    · have hd' : S.prod id ∣ n := by simpa using hd
      simp [f, hd, hd', rosserXi_eq_sign_of_retained_product hret rfl]
    · have hd' : ¬ S.prod id ∣ n := by simpa using hd
      simp [f, hd, hd']
  calc
    (∑ S ∈ rosserRetainedSubsets z y nu,
      (-1 : ℝ) ^ S.card *
        rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) S) =
      ∑ S ∈ rosserRetainedSubsets z y nu, f (S.prod id) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact hterm S hS
    _ = ∑ d ∈ rosserRetainedProductValues z y nu, f d :=
      (Finset.sum_image rosserRetainedProductValues_injOn).symm
    _ = ∑ d ∈ rosserRetainedProductValues z y nu,
        if d ∣ n then rosserXi z y nu d else 0 := by
          simp [f]

theorem rosserXi_ne_zero_iff_mem_retainedProductValues {z y : ℝ}
    {nu : Fin 2} {d : ℕ} :
    rosserXi z y nu d ≠ 0 ↔ d ∈ rosserRetainedProductValues z y nu := by
  constructor
  · intro hxi
    obtain ⟨hret, hprod⟩ := rosserXi_spec hxi
    have hS : rosserPrimeSupport z d ∈ rosserRetainedSubsets z y nu := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hret.1, hret⟩
    apply Finset.mem_image.mpr
    exact ⟨rosserPrimeSupport z d, hS, hprod⟩
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨S, hS, hprod⟩
    have hret : rosserRetained z y nu S := (Finset.mem_filter.mp hS).2
    rw [rosserXi_eq_sign_of_retained_product hret hprod]
    exact pow_ne_zero _ (by norm_num)

theorem rosserRetainedProductValues_lt_y {z y : ℝ} {nu : Fin 2}
    {d : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hd : d ∈ rosserRetainedProductValues z y nu) : (d : ℝ) < y := by
  rcases Finset.mem_image.mp hd with ⟨S, hS, hprod⟩
  have hret : rosserRetained z y nu S := (Finset.mem_filter.mp hS).2
  have hbound := rosserRetained_product_lt hz hzy hret
  rw [hprod] at hbound
  exact hbound

theorem rosserXi_zero {z y : ℝ} {nu : Fin 2} : rosserXi z y nu 0 = 0 := by
  by_contra hxi
  obtain ⟨hret, hprod⟩ := rosserXi_spec hxi
  have hpos : 0 < (rosserPrimeSupport z 0).prod id := by
    apply Finset.prod_pos
    intro p hp
    have hpz := hret.1 hp
    unfold sievePrimesBelow at hpz
    exact (Finset.mem_filter.mp hpz).2.1.pos
  rw [hprod] at hpos
  omega

theorem nat_lt_y_le_floor {y : ℝ} {d : ℕ} (hdy : (d : ℝ) < y) :
    d ≤ ⌊y⌋₊ := by
  apply Nat.le_floor
  exact_mod_cast le_of_lt hdy

theorem rosserRetainedProductValues_subset_range {z y : ℝ} {nu : Fin 2}
    (hz : 2 ≤ z) (hzy : z ≤ y) :
    rosserRetainedProductValues z y nu ⊆ Finset.range (⌊y⌋₊ + 1) := by
  intro d hd
  apply Finset.mem_range.mpr
  have hdy := nat_lt_y_le_floor (rosserRetainedProductValues_lt_y hz hzy hd)
  omega

theorem rosserRetained_sum_eq_finite_divisor_sum {z y : ℝ}
    {nu : Fin 2} (hz : 2 ≤ z) (hzy : z ≤ y) (n : ℕ) :
    (∑ d ∈ rosserRetainedProductValues z y nu,
      if d ∣ n then rosserXi z y nu d else 0) =
      ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        if d ∣ n then rosserXi z y nu d else 0 := by
  apply Finset.sum_subset (rosserRetainedProductValues_subset_range hz hzy)
  intro d hd hnot
  by_cases hdiv : d ∣ n
  · have hzero : rosserXi z y nu d = 0 := by
      by_contra hxi
      exact hnot ((rosserXi_ne_zero_iff_mem_retainedProductValues).mp hxi)
    simp [hdiv, hzero]
  · simp [hdiv]

def rosserPositiveDivisorsBelow (y : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range (⌊y⌋₊ + 1)).filter fun d => 0 < d ∧ d ∣ n

def rosserDivisorSum (z y : ℝ) (nu : Fin 2) (n : ℕ) : ℝ :=
  ∑ d ∈ rosserPositiveDivisorsBelow y n, rosserXi z y nu d

theorem rosserFiniteDivisorSum_eq_range_sum {z y : ℝ} {nu : Fin 2}
    (n : ℕ) :
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
      if d ∣ n then rosserXi z y nu d else 0) =
      ∑ d ∈ rosserPositiveDivisorsBelow y n, rosserXi z y nu d := by
  rw [rosserPositiveDivisorsBelow, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hzero : d = 0
  · subst d
    simp [rosserXi_zero]
  · have hpos : 0 < d := Nat.pos_of_ne_zero hzero
    by_cases hdiv : d ∣ n <;> simp [hpos, hdiv]

theorem rosserRetainedSubset_sum_eq_divisorSum {z y : ℝ}
    {nu : Fin 2} (hz : 2 ≤ z) (hzy : z ≤ y) (n : ℕ) :
    (∑ S ∈ rosserRetainedSubsets z y nu,
      (-1 : ℝ) ^ S.card *
        rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) S) =
      rosserDivisorSum z y nu n := by
  calc
    (∑ S ∈ rosserRetainedSubsets z y nu,
      (-1 : ℝ) ^ S.card *
        rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) S) =
      ∑ d ∈ rosserRetainedProductValues z y nu,
        if d ∣ n then rosserXi z y nu d else 0 :=
          rosserRetainedSubset_sum_eq_productValues n
    _ = ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        if d ∣ n then rosserXi z y nu d else 0 :=
          rosserRetained_sum_eq_finite_divisor_sum hz hzy n
    _ = rosserDivisorSum z y nu n := by
          rw [rosserFiniteDivisorSum_eq_range_sum]
          rfl

def rosserStoppingRemainder (z y : ℝ) (nu : Fin 2) (n : ℕ) : ℝ :=
  ∑ P ∈ rosserStoppingPrefixes z y nu,
    rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) P *
      ∏ q ∈ rosserBelowLastPrimes z P,
        (1 - (if q ∣ n then (1 : ℝ) else 0))

theorem rosserStoppingRemainder_nonneg (z y : ℝ) (nu : Fin 2) (n : ℕ) :
    0 ≤ rosserStoppingRemainder z y nu n := by
  classical
  apply Finset.sum_nonneg
  intro P hP
  have hstop : rosserStoppingPrefix z y nu P := (Finset.mem_filter.mp hP).2
  have hmono : 0 ≤ rosserSubsetMonomial
      (fun p => if p ∣ n then (1 : ℝ) else 0) P := by
    rw [rosserSubsetMonomial_divisibility_indicator hstop.2.1]
    split_ifs <;> norm_num
  have hres : 0 ≤ ∏ q ∈ rosserBelowLastPrimes z P,
      (1 - (if q ∣ n then (1 : ℝ) else 0)) := by
    apply Finset.prod_nonneg
    intro q hq
    by_cases hdiv : q ∣ n <;> simp [hdiv]
  exact mul_nonneg hmono hres

theorem sieveProduct_divisibility_indicator {z : ℝ} {n : ℕ} :
    ∏ p ∈ sievePrimesBelow z,
      (1 - (if p ∣ n then (1 : ℝ) else 0)) =
      if Nat.Coprime n (sievePrimeProduct z) then 1 else 0 := by
  classical
  let S := sievePrimesBelow z
  have hfactor :
      (∏ p ∈ S, (1 - (if p ∣ n then (1 : ℝ) else 0))) =
        ∏ p ∈ S, (if p ∣ n then (0 : ℝ) else 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    by_cases h : p ∣ n <;> simp [h]
  have hprod :
      (∏ p ∈ S, (if p ∣ n then (0 : ℝ) else 1)) =
        if ∀ p ∈ S, ¬ p ∣ n then 1 else 0 := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
        by_cases hdiv : p ∣ n <;> simp [Finset.prod_insert, hp, hdiv, ih]
  rw [show sievePrimesBelow z = S from rfl, hfactor, hprod]
  have hcop : Nat.Coprime n (sievePrimeProduct z) ↔
      ∀ p ∈ S, ¬ p ∣ n := by
    simpa [S] using (natCoprime_sievePrimeProduct_iff (z := z) (n := n))
  by_cases h : ∀ p ∈ S, ¬ p ∣ n
  · have hnc : Nat.Coprime n (sievePrimeProduct z) := hcop.symm.mp h
    simp only [if_pos h, if_pos hnc]
  · have hnc : ¬ Nat.Coprime n (sievePrimeProduct z) := fun hc => h (hcop.mp hc)
    simp only [if_neg h, if_neg hnc]

theorem rosserPointwiseSandwich_nat {z y : ℝ} (hz : 2 ≤ z)
    (hzy : z ≤ y) (n : ℕ) :
    rosserDivisorSum z y (0 : Fin 2) n ≤
        (if Nat.Coprime n (sievePrimeProduct z) then (1 : ℝ) else 0) ∧
      (if Nat.Coprime n (sievePrimeProduct z) then (1 : ℝ) else 0) ≤
        rosserDivisorSum z y (1 : Fin 2) n := by
  have hcop :
      (∏ p ∈ sievePrimesBelow z,
        (1 - (if p ∣ n then (1 : ℝ) else 0))) =
        if Nat.Coprime n (sievePrimeProduct z) then 1 else 0 :=
    sieveProduct_divisibility_indicator
  have hid0 :
      (if Nat.Coprime n (sievePrimeProduct z) then (1 : ℝ) else 0) =
        rosserDivisorSum z y (0 : Fin 2) n +
          rosserStoppingRemainder z y (0 : Fin 2) n := by
    rw [← hcop,
      rosserStoppingIdentity (z := z) (y := y) (nu := (0 : Fin 2))
        (x := fun p => if p ∣ n then (1 : ℝ) else 0),
      rosserRetainedSubset_sum_eq_divisorSum hz hzy n]
    simp [rosserStoppingRemainder] <;> ring
  have hid1 :
      (if Nat.Coprime n (sievePrimeProduct z) then (1 : ℝ) else 0) =
        rosserDivisorSum z y (1 : Fin 2) n -
          rosserStoppingRemainder z y (1 : Fin 2) n := by
    rw [← hcop,
      rosserStoppingIdentity (z := z) (y := y) (nu := (1 : Fin 2))
        (x := fun p => if p ∣ n then (1 : ℝ) else 0),
      rosserRetainedSubset_sum_eq_divisorSum hz hzy n]
    simp [rosserStoppingRemainder] <;> ring
  have hR0 := rosserStoppingRemainder_nonneg z y (0 : Fin 2) n
  have hR1 := rosserStoppingRemainder_nonneg z y (1 : Fin 2) n
  constructor <;> linarith

theorem intGcd_sieveIndicator_eq_natAbs {z : ℝ} (n : ℤ) :
    (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) =
      if Nat.Coprime n.natAbs (sievePrimeProduct z) then 1 else 0 := by
  have hcop : Int.gcd n (sievePrimeProduct z : ℤ) = 1 ↔
      Nat.Coprime n.natAbs (sievePrimeProduct z) := by
    rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime]
    simp
  by_cases h : Int.gcd n (sievePrimeProduct z : ℤ) = 1
  · have hnat := hcop.mp h
    simp only [if_pos h, if_pos hnat]
  · have hnat : ¬ Nat.Coprime n.natAbs (sievePrimeProduct z) :=
      fun hn => h (hcop.mpr hn)
    simp only [if_neg h, if_neg hnat]

theorem rosserPointwiseSandwich_int {z y : ℝ} (hz : 2 ≤ z)
    (hzy : z ≤ y) (n : ℤ) :
    rosserDivisorSum z y (0 : Fin 2) n.natAbs ≤
        (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) ∧
      (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) ≤
        rosserDivisorSum z y (1 : Fin 2) n.natAbs := by
  have hnat := rosserPointwiseSandwich_nat hz hzy n.natAbs
  rw [← intGcd_sieveIndicator_eq_natAbs (z := z) n] at hnat
  exact hnat

theorem list_nat_prod_cast_le_pow {z : ℝ} (hz : 0 ≤ z) (L : List ℕ)
    (hL : ∀ p ∈ L, (p : ℝ) ≤ z) :
    (L.prod : ℝ) ≤ z ^ L.length := by
  induction L with
  | nil => simp
  | cons p L ih =>
      have hp := hL p (by simp)
      have htail := ih (fun q hq => hL q (by simp [hq]))
      rw [List.prod_cons, List.length_cons, Nat.cast_mul]
      calc
        (p : ℝ) * (L.prod : ℝ) ≤ z * z ^ L.length :=
          mul_le_mul hp htail (by positivity) (by positivity)
        _ = z ^ (L.length + 1) := by rw [pow_succ]; ring

theorem rosserStopping_length_plus_beta_gt_s {z y : ℝ} {nu : Fin 2}
    {S : Finset ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hstop : rosserStoppingPrefix z y nu S) :
    (S.card : ℝ) + 513 > Real.log y / Real.log z := by
  let L := rosserPrimeList S
  have hlen : L.length = S.card := rosserPrimeList_length S
  have hmpos : 1 ≤ S.card := by
    have := hstop.1
    exact Finset.card_pos.mpr this
  have hLbound : ∀ p ∈ L, (p : ℝ) ≤ z := by
    intro p hp
    have hpS := (rosserPrimeList_mem S p).mp hp
    have hpz := hstop.2.1 hpS
    unfold sievePrimesBelow at hpz
    exact le_of_lt (Finset.mem_filter.mp hpz).2.2
  have hprefix :
      (rosserPrefixProduct L S.card : ℝ) ≤ z ^ S.card := by
    have htakebound := list_nat_prod_cast_le_pow (le_trans (by norm_num : 0 ≤ (2:ℝ)) hz)
      (L.take S.card) (by
        intro p hp
        exact hLbound p ((List.take_sublist S.card L).subset hp))
    have htake_length : (L.take S.card).length = S.card := by
      simp [List.length_take, Nat.min_eq_left hlen.symm.le]
    simpa [rosserPrefixProduct, htake_length] using htakebound
  have hlastpos : 1 ≤ rosserPrefixLast L S.card := by
    rw [rosserPrefixLast_eq_getElem hmpos (by rw [hlen])]
    have hmem := List.getElem_mem (l := L) (n := S.card - 1) (by rw [hlen]; omega)
    have hpS := (rosserPrimeList_mem S _).mp hmem
    have hpz := hstop.2.1 hpS
    unfold sievePrimesBelow at hpz
    have hprime := (Finset.mem_filter.mp hpz).2.1
    exact le_trans (by norm_num : 1 ≤ 2) hprime.two_le
  have hlastlt : (rosserPrefixLast L S.card : ℝ) < z := by
    rw [rosserPrefixLast_eq_getElem hmpos (by rw [hlen])]
    have hmem := List.getElem_mem (l := L) (n := S.card - 1) (by rw [hlen]; omega)
    have hpS := (rosserPrimeList_mem S _).mp hmem
    have hpz := hstop.2.1 hpS
    unfold sievePrimesBelow at hpz
    exact (Finset.mem_filter.mp hpz).2.2
  have hlastpow : (rosserPrefixLast L S.card : ℝ) ^ 513 < z ^ 513 :=
    pow_lt_pow_left₀ hlastlt (by positivity) (by norm_num)
  have hweightlt :
      (rosserPrefixWeight L S.card : ℝ) < z ^ (S.card + 513) := by
    rw [rosserPrefixWeight, Nat.cast_mul, Nat.cast_pow]
    calc
      (rosserPrefixProduct L S.card : ℝ) *
          (rosserPrefixLast L S.card : ℝ) ^ 513 ≤
        z ^ S.card * (rosserPrefixLast L S.card : ℝ) ^ 513 :=
          mul_le_mul_of_nonneg_right hprefix (by positivity)
      _ < z ^ S.card * z ^ 513 :=
          mul_lt_mul_of_pos_left hlastpow (by positivity)
      _ = z ^ (S.card + 513) := by rw [← pow_add]
  have hstopweight : y ≤ (rosserPrefixWeight L S.card : ℝ) := hstop.2.2.2.2
  have hylt : y < z ^ (S.card + 513) := lt_of_le_of_lt hstopweight hweightlt
  have hzpos : 0 < z := by linarith
  have hypos : 0 < y := lt_of_lt_of_le hzpos hzy
  have hzlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog := Real.log_lt_log hypos hylt
  rw [Real.log_pow] at hlog
  have hratio : Real.log y / Real.log z < (S.card + 513 : ℕ) :=
    (div_lt_iff₀ hzlog).2 (by simpa [Nat.cast_add] using hlog)
  simpa [Nat.cast_add] using hratio

theorem sieve_log_residual_contraction {Y S t u : ℝ}
    (hcut : S + 514 * t < Y) (hu : u ≤ t) :
    Y - S - t - u ≥ sieveQ * (Y - S) := by
  have hq : sieveQ = (256 : ℝ) / 257 := by
    norm_num [sieveQ, sieveBeta]
  rw [hq]
  nlinarith

theorem rosserPrefixProduct_pos {L : List ℕ} {j : ℕ}
    (hpositive : ∀ p ∈ L, 0 < p) :
    0 < rosserPrefixProduct L j := by
  unfold rosserPrefixProduct
  apply List.prod_pos
  intro p hp
  exact hpositive p ((List.take_sublist j L).subset hp)

theorem log_rosserPrefixProduct_succ {L : List ℕ} {j : ℕ}
    (hj : j < L.length) (hpositive : ∀ p ∈ L, 0 < p) :
    Real.log (rosserPrefixProduct L (j + 1) : ℝ) =
      Real.log (rosserPrefixProduct L j : ℝ) + Real.log (L[j] : ℝ) := by
  have hprev : (rosserPrefixProduct L j : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast rosserPrefixProduct_pos hpositive)
  have hcur : (L[j] : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hpositive _ (List.getElem_mem hj))
  rw [rosserPrefixProduct_succ hj, Nat.cast_mul]
  exact Real.log_mul hprev hcur

theorem rosserTestedPrefix_log_bound {L : List ℕ} {j : ℕ} {y : ℝ}
    (hj : 1 ≤ j) (hjlen : j ≤ L.length)
    (hpositive : ∀ p ∈ L, 0 < p)
    (hweight : (rosserPrefixWeight L j : ℝ) < y) :
    Real.log (rosserPrefixProduct L (j - 1) : ℝ) +
      514 * Real.log (rosserPrefixLast L j : ℝ) < Real.log y := by
  have hlast_eq : rosserPrefixLast L j = L[j - 1] :=
    rosserPrefixLast_eq_getElem hj hjlen
  have hlastpos : 0 < (rosserPrefixLast L j : ℝ) := by
    rw [hlast_eq]
    exact_mod_cast hpositive _ (List.getElem_mem (by omega))
  have hprodpos : 0 < (rosserPrefixProduct L j : ℝ) := by
    exact_mod_cast rosserPrefixProduct_pos hpositive
  have hweight_eq :
      (rosserPrefixWeight L j : ℝ) =
        (rosserPrefixProduct L j : ℝ) *
          (rosserPrefixLast L j : ℝ) ^ 513 := by
    simp [rosserPrefixWeight, Nat.cast_mul, Nat.cast_pow]
  have hweightpos : 0 < (rosserPrefixWeight L j : ℝ) := by
    rw [hweight_eq]
    exact mul_pos hprodpos (pow_pos hlastpos _)
  have hlogweight :
      Real.log (rosserPrefixWeight L j : ℝ) =
        Real.log (rosserPrefixProduct L j : ℝ) +
          513 * Real.log (rosserPrefixLast L j : ℝ) := by
    rw [hweight_eq, Real.log_mul (ne_of_gt hprodpos)
      (ne_of_gt (pow_pos hlastpos _)), Real.log_pow]
    norm_num
  have hlogsucc :
      Real.log (rosserPrefixProduct L j : ℝ) =
        Real.log (rosserPrefixProduct L (j - 1) : ℝ) +
          Real.log (rosserPrefixLast L j : ℝ) := by
    have hrec := log_rosserPrefixProduct_succ
      (L := L) (j := j - 1) (by omega) hpositive
    rw [show (j - 1) + 1 = j by omega,
      show L[j - 1] = rosserPrefixLast L j by rw [hlast_eq]] at hrec
    exact hrec
  have hlog := Real.log_lt_log hweightpos hweight
  rw [hlogweight, hlogsucc] at hlog
  linarith

theorem rosserPrefix_log_residual_contraction {L : List ℕ} {j : ℕ} {y : ℝ}
    (hsorted : L.SortedGT)
    (hj : 1 ≤ j) (hjnext : j + 1 ≤ L.length)
    (hpositive : ∀ p ∈ L, 0 < p)
    (hweight : (rosserPrefixWeight L j : ℝ) < y) :
    Real.log y - Real.log (rosserPrefixProduct L (j + 1) : ℝ) ≥
      sieveQ * (Real.log y -
        Real.log (rosserPrefixProduct L (j - 1) : ℝ)) := by
  have hjlen : j ≤ L.length := by omega
  have hcut := rosserTestedPrefix_log_bound hj hjlen hpositive hweight
  have hdecrease : L[j] < L[j - 1] := by
    exact hsorted.getElem_gt_getElem_of_lt (by omega)
  have hcurpos : 0 < (L[j] : ℝ) := by
    exact_mod_cast hpositive _ (List.getElem_mem (by omega))
  have hnextidx : j + 1 - 1 = j := by omega
  have hlastnext : rosserPrefixLast L (j + 1) = L[j] := by
    rw [rosserPrefixLast_eq_getElem (by omega) hjnext]
    simpa [hnextidx]
  have hlogorder :
      Real.log (rosserPrefixLast L (j + 1) : ℝ) ≤
        Real.log (rosserPrefixLast L j : ℝ) := by
    rw [hlastnext, rosserPrefixLast_eq_getElem hj hjlen]
    apply Real.log_le_log hcurpos
    exact_mod_cast le_of_lt hdecrease
  have hcontract := sieve_log_residual_contraction hcut hlogorder
  have hstepPrev :
      Real.log (rosserPrefixProduct L j : ℝ) =
        Real.log (rosserPrefixProduct L (j - 1) : ℝ) +
          Real.log (rosserPrefixLast L j : ℝ) := by
    have h := log_rosserPrefixProduct_succ (L := L) (j := j - 1)
      (by omega) hpositive
    rw [show j - 1 + 1 = j by omega,
      show L[j - 1] = rosserPrefixLast L j by
        rw [rosserPrefixLast_eq_getElem hj hjlen]] at h
    exact h
  have hstepNext :
      Real.log (rosserPrefixProduct L (j + 1) : ℝ) =
        Real.log (rosserPrefixProduct L j : ℝ) +
          Real.log (rosserPrefixLast L (j + 1) : ℝ) := by
    have h := log_rosserPrefixProduct_succ (L := L) (j := j)
      (by omega) hpositive
    rw [← hlastnext] at h
    exact h
  have hidentity :
      Real.log (rosserPrefixProduct L (j + 1) : ℝ) =
        Real.log (rosserPrefixProduct L (j - 1) : ℝ) +
          Real.log (rosserPrefixLast L j : ℝ) +
            Real.log (rosserPrefixLast L (j + 1) : ℝ) := by
    calc
      _ = Real.log (rosserPrefixProduct L j : ℝ) +
          Real.log (rosserPrefixLast L (j + 1) : ℝ) := hstepNext
      _ = _ := by rw [hstepPrev]
  rw [hidentity]
  linarith

theorem rosserOddPrefix_residual_ge {L : List ℕ} {y : ℝ} {r : ℕ}
    (hrec : ∀ k < r,
      Real.log y - Real.log (rosserPrefixProduct L (2 * k + 2) : ℝ) ≥
        sieveQ * (Real.log y -
          Real.log (rosserPrefixProduct L (2 * k) : ℝ))) :
    Real.log y - Real.log (rosserPrefixProduct L (2 * r) : ℝ) ≥
      sieveQ ^ r * Real.log y := by
  have hq : 0 ≤ sieveQ := by norm_num [sieveQ, sieveBeta]
  induction r with
  | zero => simp [rosserPrefixProduct]
  | succ r ih =>
      have ih' := ih (fun k hk => hrec k (by omega))
      have hstep := hrec r (by omega)
      have hstep' :
          Real.log y - Real.log (rosserPrefixProduct L (2 * (r + 1)) : ℝ) ≥
            sieveQ * (Real.log y -
              Real.log (rosserPrefixProduct L (2 * r) : ℝ)) := by
        simpa [Nat.mul_add] using hstep
      calc
        _ ≥ sieveQ * (Real.log y -
            Real.log (rosserPrefixProduct L (2 * r) : ℝ)) := hstep'
        _ ≥ sieveQ * (sieveQ ^ r * Real.log y) :=
          mul_le_mul_of_nonneg_left ih' hq
        _ = sieveQ ^ (r + 1) * Real.log y := by rw [pow_succ]; ring

theorem rosserEvenPrefix_residual_ge {L : List ℕ} {y : ℝ} {n : ℕ}
    (hbase : Real.log y -
        Real.log (rosserPrefixProduct L 1 : ℝ) ≥ Real.log y / 2)
    (hrec : ∀ k < n,
      Real.log y - Real.log (rosserPrefixProduct L (2 * k + 3) : ℝ) ≥
        sieveQ * (Real.log y -
          Real.log (rosserPrefixProduct L (2 * k + 1) : ℝ))) :
    Real.log y - Real.log (rosserPrefixProduct L (2 * n + 1) : ℝ) ≥
      sieveQ ^ n * (Real.log y / 2) := by
  have hq : 0 ≤ sieveQ := by norm_num [sieveQ, sieveBeta]
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
      have ih' := ih (fun k hk => hrec k (by omega))
      have hstep := hrec n (by omega)
      have hstep' :
          Real.log y -
              Real.log (rosserPrefixProduct L (2 * (n + 1) + 1) : ℝ) ≥
            sieveQ * (Real.log y -
              Real.log (rosserPrefixProduct L (2 * n + 1) : ℝ)) := by
        simpa [Nat.mul_add, Nat.add_assoc] using hstep
      calc
        _ ≥ sieveQ * (Real.log y -
            Real.log (rosserPrefixProduct L (2 * n + 1) : ℝ)) := hstep'
        _ ≥ sieveQ * (sieveQ ^ n * (Real.log y / 2)) :=
          mul_le_mul_of_nonneg_left ih' hq
        _ = sieveQ ^ (n + 1) * (Real.log y / 2) := by
          rw [pow_succ]
          ring

theorem rosserStopping_final_log_bound {L : List ℕ} {m : ℕ}
    {y B : ℝ} (hm : 1 ≤ m) (hmle : m ≤ L.length)
    (hpositive : ∀ p ∈ L, 0 < p) (hy : 0 < y)
    (hfinal : y ≤ (rosserPrefixWeight L m : ℝ))
    (hresidual : B ≤ Real.log y -
      Real.log (rosserPrefixProduct L (m - 1) : ℝ)) :
    B / 514 ≤ Real.log (rosserPrefixLast L m : ℝ) := by
  have hlast_eq : rosserPrefixLast L m = L[m - 1] :=
    rosserPrefixLast_eq_getElem hm hmle
  have hlastpos : 0 < (rosserPrefixLast L m : ℝ) := by
    rw [hlast_eq]
    exact_mod_cast hpositive _ (List.getElem_mem (by omega))
  have hprodpos : 0 < (rosserPrefixProduct L m : ℝ) := by
    exact_mod_cast rosserPrefixProduct_pos hpositive
  have hweight_eq :
      (rosserPrefixWeight L m : ℝ) =
        (rosserPrefixProduct L m : ℝ) *
          (rosserPrefixLast L m : ℝ) ^ 513 := by
    simp [rosserPrefixWeight, Nat.cast_mul, Nat.cast_pow]
  have hlogweight :
      Real.log (rosserPrefixWeight L m : ℝ) =
        Real.log (rosserPrefixProduct L m : ℝ) +
          513 * Real.log (rosserPrefixLast L m : ℝ) := by
    rw [hweight_eq, Real.log_mul (ne_of_gt hprodpos)
      (ne_of_gt (pow_pos hlastpos _)), Real.log_pow]
    norm_num
  have hlogstep :
      Real.log (rosserPrefixProduct L m : ℝ) =
        Real.log (rosserPrefixProduct L (m - 1) : ℝ) +
          Real.log (rosserPrefixLast L m : ℝ) := by
    have h := log_rosserPrefixProduct_succ (L := L) (j := m - 1)
      (by omega) hpositive
    rw [show m - 1 + 1 = m by omega,
      show L[m - 1] = rosserPrefixLast L m by rw [hlast_eq]] at h
    exact h
  have hlog := Real.log_le_log hy hfinal
  rw [hlogweight, hlogstep] at hlog
  have hmain : B ≤ 514 * Real.log (rosserPrefixLast L m : ℝ) := by
    linarith
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 514)).2
  nlinarith [hmain]

theorem rosserStopping_odd_last_prime_bound {z y : ℝ} {r : ℕ}
    {S : Finset ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hstop : rosserStoppingPrefix z y (1 : Fin 2) S)
    (hcard : S.card = 2 * r + 1) :
    Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))) ≤
      (rosserPrefixLast (rosserPrimeList S) S.card : ℝ) := by
  let L := rosserPrimeList S
  have hlen : L.length = S.card := rosserPrimeList_length S
  have hpositive : ∀ p ∈ L, 0 < p := by
    intro p hp
    have hpS := (rosserPrimeList_mem S p).mp hp
    have hpz := hstop.2.1 hpS
    have hprime := (Finset.mem_filter.mp hpz).2.1
    exact hprime.pos
  have hYpos : 0 < Real.log y := by
    have hy : 2 ≤ y := le_trans hz hzy
    exact Real.log_pos (by linarith)
  have hrec : ∀ k < r,
      Real.log y - Real.log (rosserPrefixProduct L (2 * k + 2) : ℝ) ≥
        sieveQ * (Real.log y -
          Real.log (rosserPrefixProduct L (2 * k) : ℝ)) := by
    intro k hk
    have hj : 1 ≤ 2 * k + 1 := by omega
    have hjlt : 2 * k + 1 < S.card := by rw [hcard]; omega
    have hpar : (2 * k + 1) % 2 = 1 := by omega
    have hweight := hstop.2.2.2.1 (2 * k + 1) hj hjlt hpar
    have hstep := rosserPrefix_log_residual_contraction
      (L := L) (j := 2 * k + 1) (y := y)
      (rosserPrimeList_sorted S) hj (by rw [hlen, hcard]; omega)
      hpositive hweight
    simpa [show 2 * k + 1 + 1 = 2 * k + 2 by omega,
      show 2 * k + 1 - 1 = 2 * k by omega] using hstep
  have hiterate := rosserOddPrefix_residual_ge (L := L) (y := y) hrec
  have hmpos : 1 ≤ S.card := by rw [hcard]; omega
  have hfinal : y ≤ (rosserPrefixWeight L S.card : ℝ) := hstop.2.2.2.2
  have hresidual : sieveQ ^ r * Real.log y ≤
      Real.log y - Real.log (rosserPrefixProduct L (S.card - 1) : ℝ) := by
    simpa [hcard, show 2 * r + 1 - 1 = 2 * r by omega] using hiterate
  have hlogp := rosserStopping_final_log_bound hmpos (by rw [hlen])
    hpositive (by linarith) hfinal hresidual
  have hqnonneg : 0 ≤ sieveQ ^ r := pow_nonneg (by norm_num [sieveQ, sieveBeta]) _
  have htargetlog :
      Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1)) ≤
        Real.log (rosserPrefixLast L S.card : ℝ) := by
    have hden : 0 < 2 * (sieveBeta + 1) := by norm_num [sieveBeta]
    have hlogp' : sieveQ ^ r * Real.log y / 514 ≤
        Real.log (rosserPrefixLast L S.card : ℝ) := by
      simpa using hlogp
    have hbeta : 2 * (sieveBeta + 1) = 1028 := by norm_num [sieveBeta]
    rw [hbeta]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1028)).2
    have hprod : 0 ≤ sieveQ ^ r * Real.log y := mul_nonneg hqnonneg (le_of_lt hYpos)
    nlinarith [hlogp']
  have hlastpos : 0 < (rosserPrefixLast L S.card : ℝ) := by
    rw [rosserPrefixLast_eq_getElem hmpos (by rw [hlen])]
    exact_mod_cast hpositive _ (List.getElem_mem (by rw [hlen]; omega))
  calc
    Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))) ≤
        Real.exp (Real.log (rosserPrefixLast L S.card : ℝ)) :=
      Real.exp_le_exp.mpr htargetlog
    _ = (rosserPrefixLast L S.card : ℝ) := Real.exp_log hlastpos

theorem rosserStopping_even_last_prime_bound {z y : ℝ} {r : ℕ}
    {S : Finset ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hs : 2 ≤ Real.log y / Real.log z)
    (hstop : rosserStoppingPrefix z y (0 : Fin 2) S)
    (hcard : S.card = 2 * r) :
    Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))) ≤
      (rosserPrefixLast (rosserPrimeList S) S.card : ℝ) := by
  let L := rosserPrimeList S
  have hlen : L.length = S.card := rosserPrimeList_length S
  have hcardpos : 0 < S.card := Finset.card_pos.mpr hstop.1
  have hrpos : 1 ≤ r := by rw [hcard] at hcardpos; omega
  have hLpos : 0 < L.length := by rw [hlen, hcard]; omega
  have hpositive : ∀ p ∈ L, 0 < p := by
    intro p hp
    have hpS := (rosserPrimeList_mem S p).mp hp
    have hpz := hstop.2.1 hpS
    exact (Finset.mem_filter.mp hpz).2.1.pos
  have hYpos : 0 < Real.log y := by
    have hy : 2 ≤ y := le_trans hz hzy
    exact Real.log_pos (by linarith)
  have hzlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hratio : 2 * Real.log z ≤ Real.log y :=
    (le_div_iff₀ hzlog).mp hs
  have hfirstidx : L[0] ∈ L := List.getElem_mem hLpos
  have hfirstS : L[0] ∈ S := (rosserPrimeList_mem S _).mp hfirstidx
  have hfirstz : (L[0] : ℝ) < z := by
    have hpz := hstop.2.1 hfirstS
    exact (Finset.mem_filter.mp hpz).2.2
  have hfirstlog : Real.log (L[0] : ℝ) < Real.log z := by
    apply Real.log_lt_log
    · exact_mod_cast hpositive _ hfirstidx
    · exact_mod_cast hfirstz
  have hbase : Real.log y -
      Real.log (rosserPrefixProduct L 1 : ℝ) ≥ Real.log y / 2 := by
    have hfirstprod : rosserPrefixProduct L 1 = L[0] := by
      rw [rosserPrefixProduct_succ hLpos]
      simp [rosserPrefixProduct]
    rw [hfirstprod]
    nlinarith
  have hrec : ∀ k < r - 1,
      Real.log y - Real.log (rosserPrefixProduct L (2 * k + 3) : ℝ) ≥
        sieveQ * (Real.log y -
          Real.log (rosserPrefixProduct L (2 * k + 1) : ℝ)) := by
    intro k hk
    have hj : 1 ≤ 2 * k + 2 := by omega
    have hjlt : 2 * k + 2 < S.card := by rw [hcard]; omega
    have hpar : (2 * k + 2) % 2 = 0 := by omega
    have hweight := hstop.2.2.2.1 (2 * k + 2) hj hjlt hpar
    have hstep := rosserPrefix_log_residual_contraction
      (L := L) (j := 2 * k + 2) (y := y)
      (rosserPrimeList_sorted S) hj (by rw [hlen, hcard]; omega)
      hpositive hweight
    simpa [show 2 * k + 2 + 1 = 2 * k + 3 by omega,
      show 2 * k + 2 - 1 = 2 * k + 1 by omega] using hstep
  have hiterate := rosserEvenPrefix_residual_ge
    (L := L) (y := y) (n := r - 1) hbase hrec
  have hmpos : 1 ≤ S.card := by omega
  have hfinal : y ≤ (rosserPrefixWeight L S.card : ℝ) := hstop.2.2.2.2
  have hidx : 2 * (r - 1) + 1 = S.card - 1 := by rw [hcard]; omega
  have hresidual : sieveQ ^ (r - 1) * (Real.log y / 2) ≤
      Real.log y - Real.log (rosserPrefixProduct L (S.card - 1) : ℝ) := by
    simpa [hidx] using hiterate
  have hlogp := rosserStopping_final_log_bound hmpos (by rw [hlen])
    hpositive (by linarith) hfinal hresidual
  have hqnonneg : 0 ≤ sieveQ := by norm_num [sieveQ, sieveBeta]
  have hqleone : sieveQ ≤ 1 := by norm_num [sieveQ, sieveBeta]
  have hpowle : sieveQ ^ r ≤ sieveQ ^ (r - 1) := by
    have hpow : sieveQ ^ r = sieveQ ^ (r - 1) * sieveQ := by
      calc
        sieveQ ^ r = sieveQ ^ ((r - 1) + 1) := by
          exact congrArg (fun n : ℕ => sieveQ ^ n) (by omega)
        _ = sieveQ ^ (r - 1) * sieveQ := by rw [pow_succ]
    rw [hpow]
    calc
      sieveQ ^ (r - 1) * sieveQ ≤ sieveQ ^ (r - 1) * 1 :=
        mul_le_mul_of_nonneg_left hqleone (pow_nonneg hqnonneg _)
      _ = sieveQ ^ (r - 1) := by ring
  have htargetlog :
      Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1)) ≤
        Real.log (rosserPrefixLast L S.card : ℝ) := by
    have hden : 2 * (sieveBeta + 1) = 1028 := by norm_num [sieveBeta]
    have hlogp' : sieveQ ^ (r - 1) * (Real.log y / 2) / 514 ≤
        Real.log (rosserPrefixLast L S.card : ℝ) := by
      simpa using hlogp
    rw [hden]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1028)).2
    have hscaled : sieveQ ^ r * Real.log y ≤
        sieveQ ^ (r - 1) * Real.log y :=
      mul_le_mul_of_nonneg_right hpowle (le_of_lt hYpos)
    nlinarith [hlogp', hscaled]
  have hlastpos : 0 < (rosserPrefixLast L S.card : ℝ) := by
    rw [rosserPrefixLast_eq_getElem hmpos (by rw [hlen])]
    exact_mod_cast hpositive _ (List.getElem_mem (by rw [hlen]; omega))
  calc
    Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))) ≤
        Real.exp (Real.log (rosserPrefixLast L S.card : ℝ)) :=
      Real.exp_le_exp.mpr htargetlog
    _ = (rosserPrefixLast L S.card : ℝ) := Real.exp_log hlastpos

theorem rosserStopping_least_prime_bound {z y : ℝ} {nu : Fin 2}
    {S : Finset ℕ} {r : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z)
    (hstop : rosserStoppingPrefix z y nu S)
    (hcard : S.card = 2 * r + nu.val) :
    (S.card : ℝ) + 513 > Real.log y / Real.log z ∧
      Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))) ≤
        (rosserPrefixLast (rosserPrimeList S) S.card : ℝ) ∧
      1 < Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))) := by
  have hlength := rosserStopping_length_plus_beta_gt_s hz hzy hstop
  have hprimebound :
      Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))) ≤
        (rosserPrefixLast (rosserPrimeList S) S.card : ℝ) := by
    fin_cases nu
    · have hs : 2 ≤ Real.log y / Real.log z := hscale
      have hcard' : S.card = 2 * r := by simpa using hcard
      exact rosserStopping_even_last_prime_bound hz hzy hs hstop hcard'
    · have hcard' : S.card = 2 * r + 1 := by simpa using hcard
      exact rosserStopping_odd_last_prime_bound hz hzy hstop hcard'
  have hYpos : 0 < Real.log y := by
    have hy : 2 ≤ y := le_trans hz hzy
    exact Real.log_pos (by linarith)
  have hqpos : 0 < sieveQ := sieveQ_bounds.1
  have hden : 0 < 2 * (sieveBeta + 1) := by norm_num [sieveBeta]
  have hexppos :
      0 < Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1)) := by
    apply div_pos
    · exact mul_pos hYpos (pow_pos hqpos _)
    · exact hden
  exact ⟨hlength, hprimebound,
    (Real.one_lt_exp_iff).2 hexppos⟩

def rosserDensitySum (z y : ℝ) (nu : Fin 2) : ℝ :=
  ∑ d ∈ Finset.range (⌊y⌋₊ + 1), rosserXi z y nu d / (d : ℝ)

theorem rosserSubsetMonomial_inv_eq (S : Finset ℕ) :
    rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) S =
      (((S.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) := by
  simp [rosserSubsetMonomial, Finset.prod_inv_distrib, Nat.cast_prod]

theorem rosserDensitySum_eq_retained {z y : ℝ} {nu : Fin 2}
    (hz : 2 ≤ z) (hzy : z ≤ y) :
    rosserDensitySum z y nu =
      ∑ S ∈ rosserRetainedSubsets z y nu,
        (-1 : ℝ) ^ S.card *
          rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) S := by
  classical
  let f : ℕ → ℝ := fun d => rosserXi z y nu d / (d : ℝ)
  have himageSubset :
      rosserRetainedProductValues z y nu ⊆ Finset.range (⌊y⌋₊ + 1) :=
    rosserRetainedProductValues_subset_range hz hzy
  have hsumSubset :
      (∑ d ∈ rosserRetainedProductValues z y nu, f d) =
        (∑ d ∈ Finset.range (⌊y⌋₊ + 1), f d) := by
    apply Finset.sum_subset himageSubset
    intro d hd hnot
    have hzero : rosserXi z y nu d = 0 := by
      by_contra hne
      exact hnot ((rosserXi_ne_zero_iff_mem_retainedProductValues).mp hne)
    simp [f, hzero]
  have hsumImage :
      (∑ S ∈ rosserRetainedSubsets z y nu, f (S.prod id)) =
        (∑ d ∈ rosserRetainedProductValues z y nu, f d) :=
    (Finset.sum_image rosserRetainedProductValues_injOn).symm
  have hterm : ∀ S ∈ rosserRetainedSubsets z y nu,
      f (S.prod id) =
        (-1 : ℝ) ^ S.card *
          rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) S := by
    intro S hS
    have hret : rosserRetained z y nu S := (Finset.mem_filter.mp hS).2
    have hxi := rosserXi_eq_sign_of_retained_product hret rfl
    have hxi' : rosserXi z y nu (S.prod id) = (-1 : ℝ) ^ S.card := by
      change rosserXi z y nu (∏ p ∈ S, p) = _
      exact hxi
    simp only [f, hxi', div_eq_mul_inv]
    rw [rosserSubsetMonomial_inv_eq]
    simp only [Nat.cast_prod]
    simp only [id_eq]
  unfold rosserDensitySum
  calc
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
      rosserXi z y nu d / (d : ℝ)) =
        ∑ d ∈ rosserRetainedProductValues z y nu, f d := by
          symm
          exact hsumSubset
    _ = ∑ S ∈ rosserRetainedSubsets z y nu, f (S.prod id) := hsumImage.symm
    _ = ∑ S ∈ rosserRetainedSubsets z y nu,
          (-1 : ℝ) ^ S.card *
            rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) S := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hterm S hS

theorem rosserStopping_last_mem_sieve {z y : ℝ} {nu : Fin 2}
    {P : Finset ℕ} (hstop : rosserStoppingPrefix z y nu P) :
    rosserPrefixLast (rosserPrimeList P) P.card ∈ sievePrimesBelow z := by
  have hlen := rosserPrimeList_length P
  have hmpos : 1 ≤ P.card := Finset.card_pos.mpr hstop.1
  have hlast_eq := rosserPrefixLast_eq_getElem hmpos (by rw [hlen])
  rw [hlast_eq]
  have hmem : (rosserPrimeList P)[P.card - 1] ∈ rosserPrimeList P :=
    List.getElem_mem (by rw [hlen]; omega)
  exact hstop.2.1 ((rosserPrimeList_mem P _).mp hmem)

theorem rosserBelowLastPrimes_eq_sievePrimesBelow_last {z y : ℝ}
    {nu : Fin 2} {P : Finset ℕ}
    (hstop : rosserStoppingPrefix z y nu P) :
    rosserBelowLastPrimes z P =
      sievePrimesBelow (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) := by
  have hlast_mem := rosserStopping_last_mem_sieve hstop
  have hlast_lt :
      (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) < z := by
    unfold sievePrimesBelow at hlast_mem
    exact (Finset.mem_filter.mp hlast_mem).2.2
  ext q
  constructor
  · intro hq
    have hq' := Finset.mem_filter.mp hq
    have hprime := (Finset.mem_filter.mp hq'.1).2.1
    have hqreal : (q : ℝ) <
        (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) := by exact_mod_cast hq'.2
    unfold sievePrimesBelow
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      exact Nat.le_floor (by exact_mod_cast hq'.2.le)
    · exact ⟨hprime, hqreal⟩
  · intro hq
    unfold sievePrimesBelow at hq
    have hq' := (Finset.mem_filter.mp hq).2
    have hqz : (q : ℝ) < z := lt_trans hq'.2 hlast_lt
    have hqnat : q < rosserPrefixLast (rosserPrimeList P) P.card := by
      exact_mod_cast hq'.2
    have hqmem : q ∈ sievePrimesBelow z := by
      unfold sievePrimesBelow
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        apply Nat.lt_succ_of_le
        exact Nat.le_floor (by exact_mod_cast hqz.le)
      · exact ⟨hq'.1, hqz⟩
    exact Finset.mem_filter.mpr ⟨hqmem, hqnat⟩

def rosserStoppingDensityRemainder (z y : ℝ) (nu : Fin 2) : ℝ :=
  ∑ P ∈ rosserStoppingPrefixes z y nu,
    (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
      sieveDensityProduct
        (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)

theorem rosserDensity_stopping_identity {z y : ℝ} {nu : Fin 2}
    (hz : 2 ≤ z) (hzy : z ≤ y) :
    sieveDensityProduct z = rosserDensitySum z y nu +
      (-1 : ℝ) ^ nu.val * rosserStoppingDensityRemainder z y nu := by
  classical
  have hid := rosserStoppingIdentity z y nu (fun p => 1 / (p : ℝ))
  have hret := rosserDensitySum_eq_retained (nu := nu) hz hzy
  have hrem :
      (∑ P ∈ rosserStoppingPrefixes z y nu,
        rosserSubsetMonomial (fun p => 1 / (p : ℝ)) P *
          ∏ q ∈ rosserBelowLastPrimes z P,
            (1 - 1 / (q : ℝ))) =
        rosserStoppingDensityRemainder z y nu := by
    unfold rosserStoppingDensityRemainder
    apply Finset.sum_congr rfl
    intro P hP
    have hstop : rosserStoppingPrefix z y nu P := (Finset.mem_filter.mp hP).2
    have hmon :
        rosserSubsetMonomial (fun p => 1 / (p : ℝ)) P =
          (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) := by
      simpa [one_div] using rosserSubsetMonomial_inv_eq P
    have hbelow := rosserBelowLastPrimes_eq_sievePrimesBelow_last hstop
    rw [hmon, hbelow, sieveDensityProduct]
  have hid' :
      sieveDensityProduct z =
        (∑ S ∈ rosserRetainedSubsets z y nu,
          (-1 : ℝ) ^ S.card *
            rosserSubsetMonomial (fun p => 1 / (p : ℝ)) S) +
          (-1 : ℝ) ^ nu.val *
            ∑ P ∈ rosserStoppingPrefixes z y nu,
              rosserSubsetMonomial (fun p => 1 / (p : ℝ)) P *
                ∏ q ∈ rosserBelowLastPrimes z P,
                  (1 - 1 / (q : ℝ)) := by
    simpa [sieveDensityProduct] using hid
  have hret' : rosserDensitySum z y nu =
      ∑ S ∈ rosserRetainedSubsets z y nu,
        (-1 : ℝ) ^ S.card *
          rosserSubsetMonomial (fun p => 1 / (p : ℝ)) S := by
    simpa [one_div] using hret
  rw [hret'.symm, hrem] at hid'
  exact hid'

theorem sum_powersetCard_prod_succ_insert {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (ha : a ∉ s) {n : ℕ} (f : α → ℝ) :
    (∑ A ∈ (insert a s).powersetCard (n + 1), ∏ x ∈ A, f x) =
      (∑ A ∈ s.powersetCard (n + 1), ∏ x ∈ A, f x) +
        f a * ∑ A ∈ s.powersetCard n, ∏ x ∈ A, f x := by
  classical
  have hdisj : Disjoint (s.powersetCard (n + 1))
      ((s.powersetCard n).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro A hA hB
    rcases Finset.mem_image.mp hB with ⟨B, hB, rfl⟩
    have hAsub := (Finset.mem_powersetCard.mp hA).1
    exact ha (hAsub (Finset.mem_insert_self a B))
  rw [Finset.powersetCard_succ_insert ha n, Finset.sum_union hdisj,
    Finset.sum_image]
  · have hterm : ∀ A ∈ s.powersetCard n,
        (∏ x ∈ insert a A, f x) = f a * ∏ x ∈ A, f x := by
      intro A hA
      have hAsub := (Finset.mem_powersetCard.mp hA).1
      rw [Finset.prod_insert (fun haA => ha (hAsub haA))]
    rw [Finset.sum_congr rfl hterm, Finset.mul_sum]
  · intro A hA B hB hEq
    have haA : a ∉ A := fun hx => ha ((Finset.mem_powersetCard.mp hA).1 hx)
    have haB : a ∉ B := fun hx => ha ((Finset.mem_powersetCard.mp hB).1 hx)
    apply Finset.ext
    intro x
    have hx := congrArg (fun T : Finset α => x ∈ T) hEq
    simp only [Finset.mem_insert] at hx
    constructor
    · intro hxA
      have hxa : x ≠ a := by
        intro h
        subst x
        exact haA hxA
      rcases hx.mp (Or.inr hxA) with h | hxB
      · exact False.elim (hxa h)
      · exact hxB
    · intro hxB
      have hxa : x ≠ a := by
        intro h
        subst x
        exact haB hxB
      rcases hx.mpr (Or.inr hxB) with h | hxA
      · exact False.elim (hxa h)
      · exact hxA

theorem pow_add_first_two_terms_aux {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (n : ℕ) :
    x ^ (n + 1) + (n + 1 : ℝ) * x ^ n * y ≤ (x + y) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hextra : 0 ≤ (n + 1 : ℝ) * x ^ n * y ^ 2 := by positivity
      have halgebra :
          (x ^ (n + 1) + (n + 1 : ℝ) * x ^ n * y) * (x + y) =
            x ^ ((n + 1) + 1) + ((n + 1) + 1 : ℝ) * x ^ (n + 1) * y +
              (n + 1 : ℝ) * x ^ n * y ^ 2 := by
        push_cast
        ring
      have hfirst :
          x ^ ((n + 1) + 1) + (((n + 1 : ℕ) : ℝ) + 1) *
            x ^ (n + 1) * y ≤
            (x ^ (n + 1) + (n + 1 : ℝ) * x ^ n * y) * (x + y) := by
        rw [halgebra]
        push_cast
        exact le_add_of_nonneg_right hextra
      have hstep := mul_le_mul_of_nonneg_right ih (add_nonneg hx hy)
      calc
        x ^ ((n + 1) + 1) + (((n + 1 : ℕ) : ℝ) + 1) *
            x ^ (n + 1) * y ≤
            (x ^ (n + 1) + (n + 1 : ℝ) * x ^ n * y) * (x + y) := hfirst
        _ ≤ (x + y) ^ (n + 1) * (x + y) := hstep
        _ = (x + y) ^ ((n + 1) + 1) := by
          conv_rhs => rw [pow_succ]

theorem pow_add_ge_first_two_terms {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {m : ℕ} (hm : 1 ≤ m) :
    x ^ m + (m : ℝ) * x ^ (m - 1) * y ≤ (x + y) ^ m := by
  cases m with
  | zero => omega
  | succ n =>
      simpa using pow_add_first_two_terms_aux hx hy n

theorem factorial_mul_sum_powersetCard_prod_le_pow {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (hf : ∀ a ∈ s, 0 ≤ f a) (m : ℕ) :
    (Nat.factorial m : ℝ) * (∑ A ∈ s.powersetCard m, ∏ x ∈ A, f x) ≤
      (∑ x ∈ s, f x) ^ m := by
  classical
  revert m
  induction s using Finset.induction_on with
  | empty =>
      intro m
      cases m with
      | zero => simp
      | succ m =>
          have hps : (∅ : Finset α).powersetCard (m + 1) = ∅ := by
            rw [Finset.powersetCard_eq_empty]
            simp
          simp [hps]
  | @insert a s ha ih =>
      intro m
      cases m with
      | zero => simp
      | succ n =>
          let X : ℝ := ∑ x ∈ s, f x
          have hX : 0 ≤ X := by
            dsimp [X]
            exact Finset.sum_nonneg fun b hb => hf b (Finset.mem_insert_of_mem hb)
          have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
          have ih₁ : (Nat.factorial (n + 1) : ℝ) *
              (∑ A ∈ s.powersetCard (n + 1), ∏ x ∈ A, f x) ≤ X ^ (n + 1) := by
            simpa [X] using ih (by
              intro b hb
              exact hf b (Finset.mem_insert_of_mem hb)) (n + 1)
          have ih₀ : (Nat.factorial n : ℝ) *
              (∑ A ∈ s.powersetCard n, ∏ x ∈ A, f x) ≤ X ^ n := by
            simpa [X] using ih (by
              intro b hb
              exact hf b (Finset.mem_insert_of_mem hb)) n
          have hrec := sum_powersetCard_prod_succ_insert ha f (n := n)
          have hscale : (Nat.factorial (n + 1) : ℝ) *
              (∑ A ∈ s.powersetCard (n + 1), ∏ x ∈ A, f x) +
                (n + 1 : ℝ) * f a *
                  ((Nat.factorial n : ℝ) *
                    (∑ A ∈ s.powersetCard n, ∏ x ∈ A, f x)) ≤
              X ^ (n + 1) + (n + 1 : ℝ) * f a * X ^ n := by
            exact add_le_add ih₁ (by
              have hmul := mul_le_mul_of_nonneg_left ih₀ ((show 0 ≤ (n + 1 : ℝ) * f a by positivity))
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
          have hmain : (Nat.factorial (n + 1) : ℝ) *
              (∑ A ∈ s.powersetCard (n + 1), ∏ x ∈ A, f x) +
                (Nat.factorial (n + 1) : ℝ) *
                  (f a * ∑ A ∈ s.powersetCard n, ∏ x ∈ A, f x) ≤
              (X + f a) ^ (n + 1) := by
            have hfac : (Nat.factorial (n + 1) : ℝ) =
                (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
              simp [Nat.factorial_succ, Nat.cast_mul, mul_comm]
            have hleft :
                (Nat.factorial (n + 1) : ℝ) *
                    (∑ A ∈ s.powersetCard (n + 1), ∏ x ∈ A, f x) +
                  (Nat.factorial (n + 1) : ℝ) *
                    (f a * ∑ A ∈ s.powersetCard n, ∏ x ∈ A, f x) =
                (Nat.factorial (n + 1) : ℝ) *
                    (∑ A ∈ s.powersetCard (n + 1), ∏ x ∈ A, f x) +
                  (n + 1 : ℝ) * f a *
                    ((Nat.factorial n : ℝ) *
                      (∑ A ∈ s.powersetCard n, ∏ x ∈ A, f x)) := by
              rw [hfac]
              ring
            rw [hleft]
            have hbinom := pow_add_ge_first_two_terms hX hfa (m := n + 1) (by omega)
            have hscaled := hscale
            calc
              _ ≤ X ^ (n + 1) + (n + 1 : ℝ) * f a * X ^ n := hscaled
              _ = X ^ (n + 1) + (n + 1 : ℝ) * X ^ ((n + 1) - 1) * f a := by
                congr 1
                simp
                ring
              _ ≤ (X + f a) ^ (n + 1) := by
                push_cast at hbinom ⊢
                exact hbinom
          rw [hrec]
          simpa [X, Finset.sum_insert, ha, add_comm, mul_add, mul_assoc] using hmain

theorem sum_prod_over_powersetCard_subset_le {α : Type*} [DecidableEq α]
    (t : Finset (Finset α)) (u : Finset α) (m : ℕ) (f : α → ℝ)
    (ht : t ⊆ u.powersetCard m) (hf : ∀ a, 0 ≤ f a) :
    (∑ A ∈ t, ∏ x ∈ A, f x) ≤
      ∑ A ∈ u.powersetCard m, ∏ x ∈ A, f x := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg ht
  intro A hA hnot
  apply Finset.prod_nonneg
  intro x hx
  exact hf x

theorem rosserStoppingPrefixes_card_subset_primeInterval {z y : ℝ} {nu : Fin 2}
    {r : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z) :
    (rosserStoppingPrefixes z y nu).filter
        (fun P => P.card = 2 * r + nu.val) ⊆
      (primeReciprocalSet
        (Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1)))) z).powersetCard
          (2 * r + nu.val) := by
  intro P hP
  have hP' := Finset.mem_filter.mp hP
  have hstop : rosserStoppingPrefix z y nu P :=
    (Finset.mem_filter.mp hP'.1).2
  have hcard : P.card = 2 * r + nu.val := hP'.2
  have hleast := rosserStopping_least_prime_bound hz hzy hscale hstop hcard
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro p hp
    have hmem : p ∈ sievePrimesBelow z := hstop.2.1 hp
    have hprime : p.Prime := (Finset.mem_filter.mp hmem).2.1
    have hpz : (p : ℝ) < z := (Finset.mem_filter.mp hmem).2.2
    have hpge := rosserPrimeList_mem_ge_last hstop.1 hp
    have hplower :
        Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))) ≤ (p : ℝ) := by
      exact le_trans hleast.2.1 (by exact_mod_cast hpge)
    rw [primeReciprocalSet, Finset.mem_filter]
    exact ⟨hmem, hplower⟩
  · exact hcard

theorem rosserStoppingPrefixes_reciprocal_sum_factorial_bound
    {z y a : ℝ} {nu : Fin 2} {r : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z)
    (ha : a = Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1)))) :
    (Nat.factorial (2 * r + nu.val) : ℝ) *
        (∑ P ∈ (rosserStoppingPrefixes z y nu).filter
          (fun P => P.card = 2 * r + nu.val),
            ∏ p ∈ P, 1 / (p : ℝ)) ≤
      (∑ p ∈ primeReciprocalSet a z, 1 / (p : ℝ)) ^ (2 * r + nu.val) := by
  let I := primeReciprocalSet a z
  let T := (rosserStoppingPrefixes z y nu).filter
    (fun P => P.card = 2 * r + nu.val)
  have hsubset := rosserStoppingPrefixes_card_subset_primeInterval
    (r := r) hz hzy hscale
  have hsubset' : T ⊆ I.powersetCard (2 * r + nu.val) := by
    simpa [T, I, ha] using hsubset
  have hsum := sum_prod_over_powersetCard_subset_le T I (2 * r + nu.val)
    (fun p => 1 / (p : ℝ)) hsubset' (by intro p; positivity)
  have hsym := factorial_mul_sum_powersetCard_prod_le_pow I
    (fun p => 1 / (p : ℝ)) (by intro p hp; positivity) (2 * r + nu.val)
  calc
    (Nat.factorial (2 * r + nu.val) : ℝ) *
        (∑ P ∈ T, ∏ p ∈ P, 1 / (p : ℝ)) ≤
      (Nat.factorial (2 * r + nu.val) : ℝ) *
        (∑ P ∈ I.powersetCard (2 * r + nu.val), ∏ p ∈ P, 1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ ≤ (∑ p ∈ I, 1 / (p : ℝ)) ^ (2 * r + nu.val) := by
          simpa [I, Finset.mul_sum] using hsym

theorem rosserStoppingPrefixes_density_length_bound
    {z y a : ℝ} {nu : Fin 2} {r : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z)
    (ha : a = Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))))
    (ha1 : 1 < a) (haz : a < z) :
    (∑ P ∈ (rosserStoppingPrefixes z y nu).filter
        (fun P => P.card = 2 * r + nu.val),
      (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
        sieveDensityProduct
          (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)) /
        sieveDensityProduct z ≤
      (sieveDensityProduct a / sieveDensityProduct z) *
        (∑ p ∈ primeReciprocalSet a z, 1 / (p : ℝ)) ^ (2 * r + nu.val) /
          (Nat.factorial (2 * r + nu.val) : ℝ) := by
  let T := (rosserStoppingPrefixes z y nu).filter
    (fun P => P.card = 2 * r + nu.val)
  let H := ∑ p ∈ primeReciprocalSet a z, 1 / (p : ℝ)
  let m := 2 * r + nu.val
  have hfac := rosserStoppingPrefixes_reciprocal_sum_factorial_bound
    hz hzy hscale ha
  have hS :
      (∑ P ∈ T, ∏ p ∈ P, 1 / (p : ℝ)) ≤
        H ^ m / (Nat.factorial m : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos m))).2
    simpa [T, H, m, mul_comm] using hfac
  have hsum :
      (∑ P ∈ T,
        (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
          sieveDensityProduct
            (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)) ≤
        sieveDensityProduct a * ∑ P ∈ T, ∏ p ∈ P, 1 / (p : ℝ) := by
    calc
      _ = ∑ P ∈ T,
          rosserSubsetMonomial (fun p => 1 / (p : ℝ)) P *
            sieveDensityProduct
              (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) := by
            apply Finset.sum_congr rfl
            intro P hP
            have hmon : rosserSubsetMonomial (fun p => 1 / (p : ℝ)) P =
                (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) := by
              simpa [one_div] using rosserSubsetMonomial_inv_eq P
            rw [← hmon]
      _ ≤ ∑ P ∈ T,
          sieveDensityProduct a * rosserSubsetMonomial (fun p => 1 / (p : ℝ)) P := by
            apply Finset.sum_le_sum
            intro P hP
            have hstop := (Finset.mem_filter.mp hP).1
            have hstop' := (Finset.mem_filter.mp hstop).2
            have hcard : P.card = m := (Finset.mem_filter.mp hP).2
            have hleast := rosserStopping_least_prime_bound hz hzy hscale hstop' (by
              simpa [m] using hcard)
            have hlast : a ≤
                (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) := by
              simpa [ha] using hleast.2.1
            have hV := sieveDensityProduct_antitone hlast
            have hmon : 0 ≤ rosserSubsetMonomial (fun p => 1 / (p : ℝ)) P := by
              apply Finset.prod_nonneg
              intro p hp
              positivity
            calc
              _ ≤ rosserSubsetMonomial (fun p => 1 / (p : ℝ)) P * sieveDensityProduct a :=
                mul_le_mul_of_nonneg_left hV hmon
              _ = sieveDensityProduct a * rosserSubsetMonomial
                    (fun p => 1 / (p : ℝ)) P := by ring
      _ = sieveDensityProduct a * ∑ P ∈ T,
            rosserSubsetMonomial (fun p => 1 / (p : ℝ)) P := by
            rw [Finset.mul_sum]
      _ = sieveDensityProduct a * ∑ P ∈ T, ∏ p ∈ P, 1 / (p : ℝ) := by
            rfl
  have hnorm :
      (∑ P ∈ T,
        (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
          sieveDensityProduct
            (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)) /
        sieveDensityProduct z ≤
      (sieveDensityProduct a / sieveDensityProduct z) *
        (H ^ m / (Nat.factorial m : ℝ)) := by
    calc
      _ ≤ (sieveDensityProduct a *
          ∑ P ∈ T, ∏ p ∈ P, 1 / (p : ℝ)) / sieveDensityProduct z :=
            div_le_div_of_nonneg_right hsum (sieveDensityProduct_pos.le)
      _ = (sieveDensityProduct a / sieveDensityProduct z) *
          (∑ P ∈ T, ∏ p ∈ P, 1 / (p : ℝ)) := by ring
      _ ≤ (sieveDensityProduct a / sieveDensityProduct z) *
          (H ^ m / (Nat.factorial m : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hS
            exact div_nonneg (sieveDensityProduct_pos.le) (sieveDensityProduct_pos.le)
  convert hnorm using 1 <;> simp [T, H, m] <;> ring

theorem sieveCutoff_log_ratio_bound {z y a : ℝ} {r : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hs : 1 ≤ Real.log y / Real.log z)
    (ha : a = Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1)))) :
    Real.log z / Real.log a =
        2 * (sieveBeta + 1) / ((Real.log y / Real.log z) * sieveQ ^ r) ∧
      Real.log z / Real.log a ≤ 2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r := by
  have hzlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hylog : 0 < Real.log y := Real.log_pos (by linarith)
  have hqpos : 0 < sieveQ := sieveQ_bounds.1
  have hqpow : 0 < sieveQ ^ r := pow_pos hqpos r
  have hden : 0 < 2 * (sieveBeta + 1) := by norm_num [sieveBeta]
  have hlogA : Real.log a =
      Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1)) := by
    rw [ha, Real.log_exp]
  have hexact : Real.log z / Real.log a =
      2 * (sieveBeta + 1) / ((Real.log y / Real.log z) * sieveQ ^ r) := by
    rw [hlogA]
    field_simp [ne_of_gt hzlog, ne_of_gt hylog, ne_of_gt hqpow,
      ne_of_gt hden]
    <;> ring
  have hscaleDen : sieveQ ^ r ≤
      (Real.log y / Real.log z) * sieveQ ^ r := by
    have h := mul_le_mul_of_nonneg_right hs hqpow.le
    simpa using h
  have hfrac : 2 * (sieveBeta + 1) /
      ((Real.log y / Real.log z) * sieveQ ^ r) ≤
        2 * (sieveBeta + 1) / sieveQ ^ r := by
    rw [div_le_div_iff₀ (mul_pos (div_pos hylog hzlog) hqpow) hqpow]
    nlinarith [mul_le_mul_of_nonneg_left hscaleDen (le_of_lt hden)]
  constructor
  · exact hexact
  · calc
      Real.log z / Real.log a ≤
          2 * (sieveBeta + 1) / sieveQ ^ r := by rw [hexact]; exact hfrac
      _ = 2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r := by
        simp [div_eq_mul_inv, inv_pow]

theorem primeReciprocal_sum_cutoff_le_A_add_Br {z y a : ℝ} {r : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hs : 1 ≤ Real.log y / Real.log z)
    (ha : a = Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))))
    (ha1 : 1 < a) (haz : a < z) :
    (∑ p ∈ primeReciprocalSet a z, 1 / (p : ℝ)) ≤ sieveA + sieveB * r := by
  have hratio := sieveCutoff_log_ratio_bound hz hzy hs ha
  have hzlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hloga : 0 < Real.log a := Real.log_pos ha1
  have hratioPos : 0 < Real.log z / Real.log a :=
    div_pos hzlog hloga
  have hk : 0 ≤ sieveK := by norm_num [sieveK]
  calc
    (∑ p ∈ primeReciprocalSet a z, 1 / (p : ℝ)) ≤
        Real.log sieveConstantC + sieveK *
          Real.log (Real.log z / Real.log a) :=
      primeReciprocal_sum_dimension_bound ha1 haz hz
    _ ≤ Real.log sieveConstantC + sieveK *
          Real.log (2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r) := by
      have hscaled := mul_le_mul_of_nonneg_left
        (Real.log_le_log hratioPos hratio.2) hk
      calc
        _ = sieveK * Real.log (Real.log z / Real.log a) +
            Real.log sieveConstantC := by ring
        _ ≤ sieveK * Real.log (2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r) +
            Real.log sieveConstantC := add_le_add_left hscaled (Real.log sieveConstantC)
        _ = _ := by ring
    _ ≤ sieveA + sieveB * r := sieveLogExponentialScaleBound r

theorem rosserStoppingPrefixes_density_length_dimension_bound
    {z y a : ℝ} {nu : Fin 2} {r : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z)
    (ha : a = Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))))
    (ha1 : 1 < a) (haz : a < z) :
    (∑ P ∈ (rosserStoppingPrefixes z y nu).filter
        (fun P => P.card = 2 * r + nu.val),
      (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
        sieveDensityProduct
          (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)) /
        sieveDensityProduct z ≤
      sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK * Real.exp (sieveB * r) *
        (sieveA + sieveB * r) ^ (2 * r + nu.val) /
          (Nat.factorial (2 * r + nu.val) : ℝ) := by
  let H := ∑ p ∈ primeReciprocalSet a z, 1 / (p : ℝ)
  let m := 2 * r + nu.val
  have hfixed := rosserStoppingPrefixes_density_length_bound
    hz hzy hscale ha ha1 haz
  have hratio := sieveCutoff_log_ratio_bound hz hzy (by
    fin_cases nu
    · exact le_trans (by norm_num) hscale
    · exact hscale) ha
  have hdimension := sieveDensityProduct_dimension_bound ha1 haz hz
  have hzlog : 0 < Real.log z := Real.log_pos (by linarith)
  have halog : 0 < Real.log a := Real.log_pos ha1
  have hratioPos : 0 < Real.log z / Real.log a := div_pos hzlog halog
  have hratioPow : (Real.log z / Real.log a) ^ sieveK ≤
      (2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r) ^ sieveK := by
    apply Real.rpow_le_rpow hratioPos.le hratio.2
    norm_num [sieveK]
  have hdim : sieveDensityProduct a / sieveDensityProduct z ≤
      sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK * Real.exp (sieveB * r) := by
    calc
      sieveDensityProduct a / sieveDensityProduct z ≤
          sieveConstantC * (Real.log z / Real.log a) ^ sieveK := hdimension
      _ ≤ sieveConstantC *
          (2 * (sieveBeta + 1) * sieveQ⁻¹ ^ r) ^ sieveK :=
        mul_le_mul_of_nonneg_left hratioPow (Real.exp_pos 13).le
      _ = sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
          Real.exp (sieveB * r) := by rw [sieveScalePower_factor]; ring
  have hH : H ≤ sieveA + sieveB * r := by
    simpa [H] using primeReciprocal_sum_cutoff_le_A_add_Br hz hzy
      (by
        fin_cases nu
        · exact le_trans (by norm_num) hscale
        · exact hscale) ha ha1 haz
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    apply Finset.sum_nonneg
    intro p hp
    positivity
  have hABnonneg : 0 ≤ sieveA + sieveB * r :=
    add_nonneg sieveA_pos.le (mul_nonneg sieveB_bounds.1.le (Nat.cast_nonneg r))
  have hpow : H ^ m ≤ (sieveA + sieveB * r) ^ m := by
    exact pow_le_pow_left₀ hHnonneg hH m
  have hfacpos : 0 < (Nat.factorial m : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have hquotPow : H ^ m / (Nat.factorial m : ℝ) ≤
      (sieveA + sieveB * r) ^ m / (Nat.factorial m : ℝ) :=
    div_le_div_of_nonneg_right hpow hfacpos.le
  have hfactor : 0 ≤ H ^ m / (Nat.factorial m : ℝ) := by positivity
  have hdimNonneg : 0 ≤ sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
      Real.exp (sieveB * r) := by
    apply mul_nonneg
    · apply mul_nonneg (Real.exp_pos 13).le
      exact (Real.rpow_pos_of_pos (by norm_num [sieveBeta]) _).le
    · exact (Real.exp_pos _).le
  calc
    _ ≤ (sieveDensityProduct a / sieveDensityProduct z) *
        (H ^ m / (Nat.factorial m : ℝ)) := by
          simpa [H, m, div_eq_mul_inv, mul_assoc] using hfixed
    _ ≤ (sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
          Real.exp (sieveB * r)) *
        (H ^ m / (Nat.factorial m : ℝ)) :=
          mul_le_mul_of_nonneg_right hdim hfactor
    _ ≤ (sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
          Real.exp (sieveB * r)) *
        ((sieveA + sieveB * r) ^ m / (Nat.factorial m : ℝ)) :=
          mul_le_mul_of_nonneg_left hquotPow hdimNonneg
    _ = _ := by simp [m, div_eq_mul_inv, mul_assoc]

theorem rosserStoppingPrefixes_density_length_decay_bound
    {z y a : ℝ} {nu : Fin 2} {r : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z)
    (ha : a = Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))))
    (ha1 : 1 < a) (haz : a < z) (hm : 1 ≤ 2 * r + nu.val) :
    (∑ P ∈ (rosserStoppingPrefixes z y nu).filter
        (fun P => P.card = 2 * r + nu.val),
      (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
        sieveDensityProduct
          (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)) /
        sieveDensityProduct z ≤
      sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
        Real.exp (sieveA / sieveB) * Real.exp (-(2 * r + nu.val : ℝ)) := by
  let m := 2 * r + nu.val
  have hdimension := rosserStoppingPrefixes_density_length_dimension_bound
    hz hzy hscale ha ha1 haz
  have hmpos : 1 ≤ m := by simpa [m] using hm
  have hrm : r ≤ m := by dsimp [m]; omega
  have hfact := sieveFactorialExponentialBound hmpos hrm
  have hdecay : 2 * r ≤ m := by dsimp [m]; omega
  have hlenDecay := sieveExponentialLengthDecay hdecay
  have hpref : 0 ≤ sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
      Real.exp (sieveB * r) := by
    apply mul_nonneg
    · apply mul_nonneg (Real.exp_pos 13).le
      exact (Real.rpow_pos_of_pos (by norm_num [sieveBeta]) _).le
    · exact (Real.exp_pos _).le
  have hconst : 0 ≤ sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
      Real.exp (sieveA / sieveB) := by
    apply mul_nonneg
    · apply mul_nonneg (Real.exp_pos 13).le
      exact (Real.rpow_pos_of_pos (by norm_num [sieveBeta]) _).le
    · exact (Real.exp_pos _).le
  calc
    _ ≤ (sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
        Real.exp (sieveB * r)) *
          ((sieveA + sieveB * r) ^ m / (m.factorial : ℕ)) := by
      simpa [m, div_eq_mul_inv, mul_assoc] using hdimension
    _ ≤ (sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
        Real.exp (sieveB * r)) *
          (Real.exp (sieveA / sieveB) * (Real.exp 1 * sieveB) ^ m) :=
      mul_le_mul_of_nonneg_left hfact hpref
    _ = (sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
        Real.exp (sieveA / sieveB)) *
          (Real.exp (sieveB * r) * (Real.exp 1 * sieveB) ^ m) := by ring
    _ ≤ (sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
        Real.exp (sieveA / sieveB)) * Real.exp (-(m : ℝ)) :=
      mul_le_mul_of_nonneg_left hlenDecay hconst
    _ = _ := by simp [m, mul_assoc]

theorem rosserStoppingDensityRemainder_sum_by_card (z y : ℝ) (nu : Fin 2) :
    rosserStoppingDensityRemainder z y nu =
      ∑ m ∈ Finset.range ((sievePrimesBelow z).card + 1),
        ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P.card = m),
          (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
            sieveDensityProduct
              (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) := by
  let stops := rosserStoppingPrefixes z y nu
  let lengths := Finset.range ((sievePrimesBelow z).card + 1)
  let w : Finset ℕ → ℝ := fun P =>
    (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
      sieveDensityProduct (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)
  have hmap : ∀ P ∈ stops, P.card ∈ lengths := by
    intro P hP
    have hsub : P ⊆ sievePrimesBelow z :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
    have hcard : P.card ≤ (sievePrimesBelow z).card := Finset.card_le_card hsub
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hcard)
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := stops) (t := lengths) (g := fun P => P.card) hmap w
  unfold rosserStoppingDensityRemainder
  dsimp [stops, lengths, w] at hfiber
  exact hfiber.symm

theorem rosserStoppingPrefixes_empty_of_cutoff_ge {z y a : ℝ}
    {nu : Fin 2} {r : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z)
    (ha : a = Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))))
    (hza : z ≤ a) :
    (rosserStoppingPrefixes z y nu).filter
        (fun P => P.card = 2 * r + nu.val) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro P hP hcard
  have hstop : rosserStoppingPrefix z y nu P := (Finset.mem_filter.mp hP).2
  have hleast := rosserStopping_least_prime_bound hz hzy hscale hstop hcard
  have hlastmem := rosserStopping_last_mem_sieve hstop
  have hlastlt :
      (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) < z :=
    (Finset.mem_filter.mp hlastmem).2.2
  have hlastlower : a ≤
      (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) := by
    simpa [ha] using hleast.2.1
  linarith

theorem rosserStoppingPrefix_length_gt_scale {z y : ℝ} {nu : Fin 2}
    {P : Finset ℕ} {r : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z)
    (hstop : rosserStoppingPrefix z y nu P)
    (hcard : P.card = 2 * r + nu.val) :
    (P.card : ℝ) + sieveBeta > Real.log y / Real.log z := by
  exact (rosserStopping_least_prime_bound hz hzy hscale hstop hcard).1

theorem rosserStoppingPrefixes_density_length_decay_bound_of_scale
    {z y : ℝ} {nu : Fin 2} {r : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z) :
    (∑ P ∈ (rosserStoppingPrefixes z y nu).filter
        (fun P => P.card = 2 * r + nu.val),
      (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
        sieveDensityProduct
          (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)) /
        sieveDensityProduct z ≤
      sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
        Real.exp (sieveA / sieveB) * Real.exp (-(2 * r + nu.val : ℝ)) := by
  let a := Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1)))
  have ha : a = Real.exp (Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1))) := rfl
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hq : 0 < sieveQ := sieveQ_bounds.1
  have hden : 0 < 2 * (sieveBeta + 1) := by norm_num [sieveBeta]
  have harg : 0 < Real.log y * sieveQ ^ r / (2 * (sieveBeta + 1)) :=
    div_pos (mul_pos hly (pow_pos hq r)) hden
  have ha1 : 1 < a := by
    dsimp [a]
    exact (Real.one_lt_exp_iff).2 harg
  have hconst : 0 < sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
      Real.exp (sieveA / sieveB) := by
    apply mul_pos
    · apply mul_pos (Real.exp_pos 13)
      exact Real.rpow_pos_of_pos (by norm_num [sieveBeta]) _
    · exact Real.exp_pos _
  by_cases hza : z ≤ a
  · have hempty := rosserStoppingPrefixes_empty_of_cutoff_ge
      hz hzy hscale ha hza
    rw [hempty]
    simp
    exact le_of_lt (mul_pos hconst (Real.exp_pos _))
  · have haz : a < z := lt_of_not_ge hza
    by_cases hm : 1 ≤ 2 * r + nu.val
    · exact rosserStoppingPrefixes_density_length_decay_bound
        hz hzy hscale ha ha1 haz hm
    · have hzero : 2 * r + nu.val = 0 := by omega
      have hempty : (rosserStoppingPrefixes z y nu).filter
          (fun P => P.card = 2 * r + nu.val) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro P hP hcard
        have hstop := (Finset.mem_filter.mp hP).2
        have hpos : 1 ≤ P.card := Finset.card_pos.mpr hstop.1
        omega
      rw [hempty]
      simp
      exact le_of_lt (mul_pos hconst (Real.exp_pos _))

theorem rosserStoppingPrefixes_empty_of_not_tail_length
    {z y s : ℝ} {nu : Fin 2} {r : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z)
    (hs : s = Real.log y / Real.log z)
    (hnot : ¬ s - sieveBeta < (2 * r + nu.val : ℝ)) :
    (rosserStoppingPrefixes z y nu).filter
        (fun P => P.card = 2 * r + nu.val) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro P hP hcard
  have hstop := (Finset.mem_filter.mp hP).2
  have hlength := rosserStoppingPrefix_length_gt_scale hz hzy hscale hstop hcard
  rw [hs] at hnot
  have hnot' : (2 * r + nu.val : ℝ) ≤ Real.log y / Real.log z - sieveBeta :=
    le_of_not_gt hnot
  have hmcast : (P.card : ℝ) = (2 * r + nu.val : ℝ) := by exact_mod_cast hcard
  rw [hmcast] at hlength
  linarith

theorem rosserStoppingDensityRemainder_sum_by_half_card (z y : ℝ) (nu : Fin 2) :
    rosserStoppingDensityRemainder z y nu =
      ∑ r ∈ Finset.range ((sievePrimesBelow z).card + 1),
        ∑ P ∈ (rosserStoppingPrefixes z y nu).filter
          (fun P => P.card = 2 * r + nu.val),
          (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
            sieveDensityProduct
              (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) := by
  let stops := rosserStoppingPrefixes z y nu
  let lengths := Finset.range ((sievePrimesBelow z).card + 1)
  let w : Finset ℕ → ℝ := fun P =>
    (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
      sieveDensityProduct (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)
  have hmap : ∀ P ∈ stops, P.card / 2 ∈ lengths := by
    intro P hP
    have hsub : P ⊆ sievePrimesBelow z :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
    have hcard : P.card ≤ (sievePrimesBelow z).card := Finset.card_le_card hsub
    exact Finset.mem_range.mpr (by omega)
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := stops) (t := lengths) (g := fun P => P.card / 2) hmap w
  have hfilter (r : ℕ) :
      stops.filter (fun P => P.card / 2 = r) =
        stops.filter (fun P => P.card = 2 * r + nu.val) := by
    ext P
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hP, hdiv⟩
      have hstop : rosserStoppingPrefix z y nu P := (Finset.mem_filter.mp hP).2
      have hpar : P.card % 2 = nu.val := hstop.2.2.1
      exact ⟨hP, by omega⟩
    · rintro ⟨hP, hcard⟩
      have hstop : rosserStoppingPrefix z y nu P := (Finset.mem_filter.mp hP).2
      have hpar : P.card % 2 = nu.val := hstop.2.2.1
      exact ⟨hP, by omega⟩
  unfold rosserStoppingDensityRemainder
  dsimp [stops, lengths, w] at hfiber ⊢
  calc
    _ = ∑ r ∈ Finset.range ((sievePrimesBelow z).card + 1),
          ∑ P ∈ (rosserStoppingPrefixes z y nu).filter
            (fun P => P.card / 2 = r),
            (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
              sieveDensityProduct
                (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) := hfiber.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hfilter r]

theorem rosserStoppingDensityRemainder_tail_bound {z y s : ℝ} {nu : Fin 2}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z)
    (hs : s = Real.log y / Real.log z) :
    rosserStoppingDensityRemainder z y nu / sieveDensityProduct z ≤
      sieveD₀ * Real.exp (-s) := by
  let R := Finset.range ((sievePrimesBelow z).card + 1)
  let m : ℕ → ℕ := fun r => 2 * r + nu.val
  let T := R.filter (fun r => 1 ≤ m r ∧ s - sieveBeta < (m r : ℝ))
  let F : ℕ → ℝ := fun r =>
    (∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P.card = m r),
      (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
        sieveDensityProduct (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)) /
      sieveDensityProduct z
  have hVpos : 0 < sieveDensityProduct z := sieveDensityProduct_pos
  have hR : rosserStoppingDensityRemainder z y nu / sieveDensityProduct z =
      ∑ r ∈ R, F r := by
    rw [rosserStoppingDensityRemainder_sum_by_half_card]
    simp [R, F, m, Finset.sum_div]
  have hzero (r : ℕ) (hr : r ∈ R) (hnot : r ∉ T) : F r = 0 := by
    have hbad : ¬ (1 ≤ m r ∧ s - sieveBeta < (m r : ℝ)) := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hr, h⟩)
    have hbad := not_and_or.mp hbad
    rcases hbad with hmzero | hlength
    · have hm : m r = 0 := by omega
      have hempty : (rosserStoppingPrefixes z y nu).filter
          (fun P => P.card = m r) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro P hP hcard
        have hstop := (Finset.mem_filter.mp hP).2
        have hpos : 1 ≤ P.card := Finset.card_pos.mpr hstop.1
        omega
      simp [F, m, hempty, ne_of_gt hVpos]
    · have hs' : s = Real.log y / Real.log z := hs
      have hempty := rosserStoppingPrefixes_empty_of_not_tail_length
        hz hzy hscale hs' (by simpa [m] using hlength)
      have hemptyM : (rosserStoppingPrefixes z y nu).filter
          (fun P => P.card = m r) = ∅ := by simpa [m] using hempty
      simp [F, hemptyM, ne_of_gt hVpos]
  have hfilterSum : ∑ r ∈ R, F r = ∑ r ∈ T, F r := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hnot
    exact hzero r hr hnot
  have hbound (r : ℕ) : F r ≤
      sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
        Real.exp (sieveA / sieveB) * Real.exp (-(m r : ℝ)) := by
    simpa [F, m] using
      rosserStoppingPrefixes_density_length_decay_bound_of_scale hz hzy hscale
  have hfinite : ∑ r ∈ T, F r ≤
      sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
        Real.exp (sieveA / sieveB) *
          ∑ r ∈ T, Real.exp (-(m r : ℝ)) := by
    calc
      ∑ r ∈ T, F r ≤ ∑ r ∈ T,
          (sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
            Real.exp (sieveA / sieveB) * Real.exp (-(m r : ℝ))) :=
        Finset.sum_le_sum fun r hr => hbound r
      _ = _ := by rw [Finset.mul_sum]
  let Tail := {n : ℕ // 1 ≤ n ∧ s - sieveBeta < (n : ℝ)}
  let φ : {r // r ∈ T} → Tail := fun r =>
    ⟨m r.1, by
      have hmem : r.1 ∈ R.filter
          (fun q => 1 ≤ m q ∧ s - sieveBeta < (m q : ℝ)) := by
        simpa [T] using r.2
      exact (Finset.mem_filter.mp hmem).2⟩
  let S : Finset Tail := T.attach.image φ
  have hφinj : Function.Injective φ := by
    intro r₁ r₂ h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    dsimp [φ, m] at hv
    omega
  have hφinjOn : Set.InjOn φ (↑T.attach : Set {r // r ∈ T}) := by
    intro r₁ hr₁ r₂ hr₂ h
    exact hφinj h
  have hsumMap :
      (∑ r ∈ T, Real.exp (-(m r : ℝ))) =
        ∑ n ∈ S, Real.exp (-(n.1 : ℝ)) := by
    calc
      (∑ r ∈ T, Real.exp (-(m r : ℝ))) =
          ∑ r ∈ T.attach, Real.exp (-(m r.1 : ℝ)) := by
            rw [← Finset.sum_attach]
      _ = ∑ n ∈ S, Real.exp (-(n.1 : ℝ)) := by
            dsimp [S]
            simpa [φ] using
              (Finset.sum_image
                (f := fun n : Tail => Real.exp (-(n.1 : ℝ))) hφinjOn).symm
  have hqpos : 0 < Real.exp (-1) := Real.exp_pos _
  have hqlt : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hsummableNat : Summable (fun n : ℕ => Real.exp (-(n : ℝ))) := by
    have hg := summable_geometric_of_lt_one hqpos.le hqlt
    simpa [sieveExp_neg_nat] using hg
  have hsummableTail : Summable (fun n : Tail => Real.exp (-(n.1 : ℝ))) :=
    hsummableNat.subtype (fun n => 1 ≤ n ∧ s - sieveBeta < (n : ℝ))
  have hsumTsum :
      (∑ n ∈ S, Real.exp (-(n.1 : ℝ))) ≤
        ∑' n : Tail, Real.exp (-(n.1 : ℝ)) :=
    hsummableTail.sum_le_tsum S (by intro n hn; positivity)
  have hgeom := sieveScalarGeometricTail s
  have hconstNonneg : 0 ≤ sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
      Real.exp (sieveA / sieveB) := by
    apply mul_nonneg
    · apply mul_nonneg (Real.exp_pos 13).le
      exact (Real.rpow_pos_of_pos (by norm_num [sieveBeta]) _).le
    · exact (Real.exp_pos _).le
  have hgeomfactor : 0 < 1 - Real.exp (-1) := sub_pos.mpr hqlt
  have hclose :
      sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
        Real.exp (sieveA / sieveB) *
          (Real.exp (sieveBeta - s) / (1 - Real.exp (-1))) =
      sieveD₀ * Real.exp (-s) := by
    rw [sieveD₀, Real.exp_add]
    have hsub : Real.exp (sieveBeta - s) =
        Real.exp sieveBeta * Real.exp (-s) := by
      rw [sub_eq_add_neg, Real.exp_add]
    rw [hsub]
    ring
  calc
    rosserStoppingDensityRemainder z y nu / sieveDensityProduct z =
        ∑ r ∈ R, F r := hR
    _ = ∑ r ∈ T, F r := hfilterSum
    _ ≤ sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
          Real.exp (sieveA / sieveB) *
            ∑ r ∈ T, Real.exp (-(m r : ℝ)) := hfinite
    _ ≤ sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
          Real.exp (sieveA / sieveB) *
            ∑' n : Tail, Real.exp (-(n.1 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by simpa [hsumMap] using hsumTsum) hconstNonneg
    _ ≤ sieveConstantC * (2 * (sieveBeta + 1)) ^ sieveK *
          Real.exp (sieveA / sieveB) *
            (Real.exp (sieveBeta - s) / (1 - Real.exp (-1))) :=
      mul_le_mul_of_nonneg_left hgeom hconstNonneg
    _ = sieveD₀ * Real.exp (-s) := hclose

theorem rosserDensityError {z y : ℝ} {nu : Fin 2}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hscale : if nu.val = 0 then 2 ≤ Real.log y / Real.log z
      else 1 ≤ Real.log y / Real.log z) :
    |rosserDensitySum z y nu - sieveDensityProduct z| ≤
      sieveD₀ * sieveDensityProduct z *
        Real.exp (-(Real.log y / Real.log z)) := by
  let s := Real.log y / Real.log z
  have hs : s = Real.log y / Real.log z := rfl
  have hVpos : 0 < sieveDensityProduct z := sieveDensityProduct_pos
  have hremNonneg : 0 ≤ rosserStoppingDensityRemainder z y nu := by
    unfold rosserStoppingDensityRemainder
    apply Finset.sum_nonneg
    intro P hP
    apply mul_nonneg
    · positivity
    · exact (sieveDensityProduct_pos).le
  have hid := rosserDensity_stopping_identity (nu := nu) hz hzy
  have htail := rosserStoppingDensityRemainder_tail_bound
    (nu := nu) hz hzy hscale hs
  have hremBound : rosserStoppingDensityRemainder z y nu ≤
      sieveD₀ * Real.exp (-s) * sieveDensityProduct z :=
    (div_le_iff₀ hVpos).1 htail
  have hremBound' : rosserStoppingDensityRemainder z y nu ≤
      sieveD₀ * sieveDensityProduct z * Real.exp (-s) := by
    calc
      _ ≤ sieveD₀ * Real.exp (-s) * sieveDensityProduct z := hremBound
      _ = sieveD₀ * sieveDensityProduct z * Real.exp (-s) := by ring
  have hnu : nu.val = 0 ∨ nu.val = 1 := by omega
  have habs : |rosserDensitySum z y nu - sieveDensityProduct z| =
      rosserStoppingDensityRemainder z y nu := by
    rcases hnu with hnu | hnu
    · have hid' : sieveDensityProduct z = rosserDensitySum z y nu +
          rosserStoppingDensityRemainder z y nu := by
        simpa [hnu] using hid
      have hdiff : rosserDensitySum z y nu - sieveDensityProduct z =
          -rosserStoppingDensityRemainder z y nu := by linarith
      rw [hdiff, abs_neg, abs_of_nonneg hremNonneg]
    · have hid' : sieveDensityProduct z = rosserDensitySum z y nu -
          rosserStoppingDensityRemainder z y nu := by
        simpa [hnu, sub_eq_add_neg] using hid
      have hdiff : rosserDensitySum z y nu - sieveDensityProduct z =
          rosserStoppingDensityRemainder z y nu := by linarith
      rw [hdiff, abs_of_nonneg hremNonneg]
  rw [habs]
  calc
    rosserStoppingDensityRemainder z y nu ≤
        sieveD₀ * sieveDensityProduct z * Real.exp (-s) := hremBound'
    _ = sieveD₀ * sieveDensityProduct z *
        Real.exp (-(Real.log y / Real.log z)) := by rw [hs]

/-- Each finite Rosser coefficient is either zero or a sign, hence lies in
the coefficient range required by the all-scale weight proposition. -/
theorem rosserXi_abs_le_one (z y : ℝ) (nu : Fin 2) (d : ℕ) :
    |rosserXi z y nu d| ≤ 1 := by
  unfold rosserXi
  split_ifs <;> norm_num [abs_pow]

/-- The scale parameter in the sieve construction is at least one whenever
`z ≤ y` and `z ≥ 2`. -/
theorem rosserLogScale_ge_one {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y) :
    1 ≤ Real.log y / Real.log z := by
  have hzpos : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog : Real.log z ≤ Real.log y :=
    Real.log_le_log (by linarith) hzy
  rw [one_le_div hzpos]
  exact hlog

/-- Lower coefficient in the all-scale construction. The short-scale case
uses the zero lower weight specified in the blueprint. -/
def rosserAllSLowerCoefficient (z y : ℝ) (d : ℕ) : ℝ :=
  if Real.log y / Real.log z < 2 then 0
  else rosserXi z y (0 : Fin 2) d

/-- Upper coefficient in the all-scale construction. -/
def rosserAllSUpperCoefficient (z y : ℝ) (d : ℕ) : ℝ :=
  rosserXi z y (1 : Fin 2) d

theorem rosserAllSLowerDivisorSum {z y : ℝ} (n : ℕ) :
    (∑ d ∈ rosserPositiveDivisorsBelow y n,
        rosserAllSLowerCoefficient z y d) =
      if Real.log y / Real.log z < 2 then 0
      else rosserDivisorSum z y (0 : Fin 2) n := by
  by_cases hs : Real.log y / Real.log z < 2
  · simp [rosserAllSLowerCoefficient, hs]
  · simp [rosserAllSLowerCoefficient, hs, rosserDivisorSum]

theorem rosserAllSUpperDivisorSum {z y : ℝ} (n : ℕ) :
    (∑ d ∈ rosserPositiveDivisorsBelow y n,
        rosserAllSUpperCoefficient z y d) =
      rosserDivisorSum z y (1 : Fin 2) n := by
  rfl

theorem rosserAllSLowerDensitySum {z y : ℝ} :
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSLowerCoefficient z y d / (d : ℝ)) =
      if Real.log y / Real.log z < 2 then 0
      else rosserDensitySum z y (0 : Fin 2) := by
  by_cases hs : Real.log y / Real.log z < 2
  · simp [rosserAllSLowerCoefficient, hs]
  · simp [rosserAllSLowerCoefficient, hs, rosserDensitySum]

theorem rosserAllSUpperDensitySum {z y : ℝ} :
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSUpperCoefficient z y d / (d : ℝ)) =
      rosserDensitySum z y (1 : Fin 2) := by
  rfl

theorem rosserAllSCoefficient_bounds {z y : ℝ} (d : ℕ) :
    -1 ≤ rosserAllSLowerCoefficient z y d ∧
      rosserAllSLowerCoefficient z y d ≤ 1 ∧
      -1 ≤ rosserAllSUpperCoefficient z y d ∧
      rosserAllSUpperCoefficient z y d ≤ 1 := by
  have h0 := rosserXi_abs_le_one z y (0 : Fin 2) d
  have h1 := rosserXi_abs_le_one z y (1 : Fin 2) d
  constructor
  · unfold rosserAllSLowerCoefficient
    split_ifs
    · norm_num
    · exact (abs_le.mp h0).1
  constructor
  · unfold rosserAllSLowerCoefficient
    split_ifs
    · norm_num
    · exact (abs_le.mp h0).2
  constructor
  · exact (abs_le.mp (by simpa [rosserAllSUpperCoefficient] using h1)).1
  · exact (abs_le.mp (by simpa [rosserAllSUpperCoefficient] using h1)).2

theorem rosserAllSCoefficient_eq_zero_of_ge {z y : ℝ}
    (hz : 2 ≤ z) (hzy : z ≤ y) (d : ℕ)
    (hdy : y ≤ (d : ℝ)) :
    rosserAllSLowerCoefficient z y d = 0 ∧
      rosserAllSUpperCoefficient z y d = 0 := by
  constructor
  · unfold rosserAllSLowerCoefficient
    split_ifs with hs
    · rfl
    · exact rosserXi_eq_zero_of_ge hz hzy hdy
  · exact rosserXi_eq_zero_of_ge hz hzy hdy

theorem rosserAllSPointwise {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (n : ℤ) :
    (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSLowerCoefficient z y d) ≤
      (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) ∧
      (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) ≤
    (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSUpperCoefficient z y d) := by
  by_cases hshort : Real.log y / Real.log z < 2
  · rw [rosserAllSLowerDivisorSum, if_pos hshort]
    have hupper := (rosserPointwiseSandwich_int hz hzy n).2
    rw [rosserAllSUpperDivisorSum]
    constructor
    · by_cases hcop : Int.gcd n (sievePrimeProduct z : ℤ) = 1 <;>
        simp [hcop]
    · exact hupper
  · have hlong := rosserPointwiseSandwich_int hz hzy n
    rw [rosserAllSLowerDivisorSum, rosserAllSUpperDivisorSum]
    simp only [if_neg hshort]
    exact hlong

theorem rosserAllSDensityError {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y) :
    |(∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSLowerCoefficient z y d / (d : ℝ)) -
        sieveDensityProduct z| ≤
      sieveD * sieveDensityProduct z *
        Real.exp (-(Real.log y / Real.log z)) ∧
    |(∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSUpperCoefficient z y d / (d : ℝ)) -
        sieveDensityProduct z| ≤
      sieveD * sieveDensityProduct z *
        Real.exp (-(Real.log y / Real.log z)) := by
  let s : ℝ := Real.log y / Real.log z
  have hs : s = Real.log y / Real.log z := rfl
  have hsone : 1 ≤ s := by
    rw [hs]
    exact rosserLogScale_ge_one hz hzy
  have hD0 : sieveD₀ ≤ sieveD := le_max_left _ _
  have hDexp : Real.exp 2 ≤ sieveD := le_max_right _ _
  have hVpos : 0 < sieveDensityProduct z := sieveDensityProduct_pos
  have hscale1 : if (1 : Fin 2).val = 0 then
      2 ≤ Real.log y / Real.log z else
      1 ≤ Real.log y / Real.log z := by
    norm_num
    exact hsone
  have hupper := rosserDensityError (nu := (1 : Fin 2)) hz hzy hscale1
  have hupper' : |rosserDensitySum z y (1 : Fin 2) -
      sieveDensityProduct z| ≤ sieveD * sieveDensityProduct z * Real.exp (-s) := by
    rw [hs]
    calc
      _ ≤ sieveD₀ * sieveDensityProduct z * Real.exp (-s) := by
        simpa [hs] using hupper
      _ ≤ sieveD * sieveDensityProduct z * Real.exp (-s) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hD0 hVpos.le
        · exact (Real.exp_pos _).le
  have hlower : |(∑ d ∈ Finset.range (⌊y⌋₊ + 1),
      rosserAllSLowerCoefficient z y d / (d : ℝ)) -
      sieveDensityProduct z| ≤ sieveD * sieveDensityProduct z * Real.exp (-s) := by
    by_cases hshort : s < 2
    · rw [rosserAllSLowerDensitySum]
      rw [show Real.log y / Real.log z = s by rw [hs]]
      simp only [if_pos hshort]
      rw [zero_sub, abs_neg, abs_of_pos hVpos]
      have he : 1 ≤ Real.exp 2 * Real.exp (-s) := by
        rw [← Real.exp_add]
        apply (Real.one_le_exp_iff).2
        linarith
      have hprod : 1 ≤ sieveD * Real.exp (-s) := by
        calc
          1 ≤ Real.exp 2 * Real.exp (-s) := he
          _ ≤ sieveD * Real.exp (-s) :=
            mul_le_mul_of_nonneg_right hDexp (Real.exp_pos _).le
      calc
        sieveDensityProduct z = 1 * sieveDensityProduct z := by ring
        _ ≤ (sieveD * Real.exp (-s)) * sieveDensityProduct z :=
          mul_le_mul_of_nonneg_right hprod hVpos.le
        _ = sieveD * sieveDensityProduct z * Real.exp (-s) := by ring
    · have hsge : 2 ≤ s := le_of_not_gt hshort
      have hscale0 : if (0 : Fin 2).val = 0 then
          2 ≤ Real.log y / Real.log z else
          1 ≤ Real.log y / Real.log z := by
        norm_num
        simpa [hs] using hsge
      have herr := rosserDensityError (nu := (0 : Fin 2)) hz hzy hscale0
      rw [rosserAllSLowerDensitySum]
      rw [show Real.log y / Real.log z = s by rw [hs], if_neg hshort]
      rw [hs]
      calc
        _ ≤ sieveD₀ * sieveDensityProduct z * Real.exp (-s) := by
          simpa [hs] using herr
        _ ≤ sieveD * sieveDensityProduct z * Real.exp (-s) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hD0 hVpos.le
          · exact (Real.exp_pos _).le
  constructor
  · simpa [hs] using hlower
  · rw [rosserAllSUpperDensitySum]
    exact hupper'

/-- Blueprint proposition `ls:all-s`, with the two coefficient functions
chosen explicitly according to its parity and short-scale cases. -/
theorem rosserAllS {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y) :
    (∀ d : ℕ, -1 ≤ rosserAllSLowerCoefficient z y d ∧
      rosserAllSLowerCoefficient z y d ≤ 1 ∧
      -1 ≤ rosserAllSUpperCoefficient z y d ∧
      rosserAllSUpperCoefficient z y d ≤ 1) ∧
    (∀ d : ℕ, y ≤ (d : ℝ) →
      rosserAllSLowerCoefficient z y d = 0 ∧
      rosserAllSUpperCoefficient z y d = 0) ∧
    (∀ n : ℤ,
      (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSLowerCoefficient z y d) ≤
          (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) ∧
        (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) ≤
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient z y d)) ∧
    (|(∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSLowerCoefficient z y d / (d : ℝ)) -
        sieveDensityProduct z| ≤
        sieveD * sieveDensityProduct z *
          Real.exp (-(Real.log y / Real.log z))) ∧
    (|(∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSUpperCoefficient z y d / (d : ℝ)) -
        sieveDensityProduct z| ≤
        sieveD * sieveDensityProduct z *
          Real.exp (-(Real.log y / Real.log z))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d
    exact rosserAllSCoefficient_bounds (z := z) (y := y) d
  · intro d hdy
    exact rosserAllSCoefficient_eq_zero_of_ge hz hzy d hdy
  · intro n
    exact rosserAllSPointwise hz hzy n
  · exact rosserAllSDensityError hz hzy

/-- The ceiling error in a difference of rational endpoints is at most one;
this is the scalar estimate behind the interval multiple count. -/
theorem rat_ceil_difference_error (a b : ℚ) (hab : a ≤ b) :
    |((⌈b⌉ : ℚ) - ⌈a⌉) - (b - a)| ≤ 1 := by
  have ha0 : 0 ≤ (⌈a⌉ : ℚ) - a := by
    exact sub_nonneg.mpr (Int.le_ceil a)
  have ha1 : (⌈a⌉ : ℚ) - a ≤ 1 := by
    have h := Int.ceil_lt_add_one a
    linarith
  have hb0 : 0 ≤ (⌈b⌉ : ℚ) - b := by
    exact sub_nonneg.mpr (Int.le_ceil b)
  have hb1 : (⌈b⌉ : ℚ) - b ≤ 1 := by
    have h := Int.ceil_lt_add_one b
    linarith
  have hrewrite : ((⌈b⌉ : ℚ) - ⌈a⌉) - (b - a) =
      ((⌈b⌉ : ℚ) - b) - ((⌈a⌉ : ℚ) - a) := by ring
  rw [hrewrite]
  rw [abs_le]
  constructor <;> linarith

/-- Exact multiples count in a finite integer interval, with error at most
one from its length divided by the positive modulus. This allows negative
interval endpoints. -/
theorem intIco_multiples_count_error {a b : ℤ} (hab : a ≤ b)
    {d : ℕ} (hd : 0 < d) :
    |((Finset.Ico a b).filter (fun n : ℤ => (d : ℤ) ∣ n)).card -
        ((b - a : ℤ) : ℝ) / (d : ℝ)| ≤ 1 := by
  let qa : ℚ := (a : ℚ) / (d : ℚ)
  let qb : ℚ := (b : ℚ) / (d : ℚ)
  have hdInt : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hqorder : qa ≤ qb := by
    dsimp [qa, qb]
    exact (div_le_div_iff_of_pos_right (by exact_mod_cast hd : (0 : ℚ) < (d : ℚ))).2
      (by exact_mod_cast hab)
  have hceil : ⌈qa⌉ ≤ ⌈qb⌉ := Int.ceil_le_ceil hqorder
  have hcard : (((Finset.Ico a b).filter
      (fun n : ℤ => (d : ℤ) ∣ n)).card : ℤ) = ⌈qb⌉ - ⌈qa⌉ := by
    rw [Int.Ico_filter_dvd_card a b hdInt]
    change max (⌈qb⌉ - ⌈qa⌉) 0 = ⌈qb⌉ - ⌈qa⌉
    exact max_eq_left (sub_nonneg.mpr hceil)
  have hcardCast : (((Finset.Ico a b).filter
      (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) =
        (⌈qb⌉ : ℝ) - ⌈qa⌉ := by
    exact_mod_cast hcard
  have hrat := rat_ceil_difference_error qa qb hqorder
  have hreal : |((⌈qb⌉ : ℝ) - ⌈qa⌉) -
      (((b - a : ℤ) : ℝ) / (d : ℝ))| ≤ 1 := by
    have hratReal : |((⌈qb⌉ : ℝ) - ⌈qa⌉) -
        ((qb : ℝ) - (qa : ℝ))| ≤ 1 := by
      exact_mod_cast hrat
    have hquot : (qb : ℝ) - (qa : ℝ) =
        (((b - a : ℤ) : ℝ) / (d : ℝ)) := by
      dsimp [qa, qb]
      push_cast
      field_simp
    rw [← hquot]
    exact hratReal
  rw [hcardCast]
  exact hreal

/-- A nonempty finite convex set of integers is a consecutive half-open
integer interval, with its exact cardinality as the interval length. -/
theorem finset_int_convex_eq_Ico (S : Finset ℤ) (hS : S.Nonempty)
    (hconv : ∀ a ∈ S, ∀ b ∈ S, ∀ x : ℤ, a ≤ x → x ≤ b → x ∈ S) :
    ∃ a : ℤ, S = Finset.Ico a (a + (S.card : ℤ)) := by
  let a := S.min' hS
  let b := S.max' hS
  have ha : a ∈ S := Finset.min'_mem S hS
  have hb : b ∈ S := Finset.max'_mem S hS
  have hab : a ≤ b := Finset.min'_le S b hb
  have hinterval : S = Finset.Icc a b := by
    ext x
    rw [Finset.mem_Icc]
    constructor
    · intro hx
      exact ⟨Finset.min'_le S x hx, Finset.le_max' S x hx⟩
    · intro hx
      exact hconv a ha b hb x hx.1 hx.2
  have hcard : (S.card : ℤ) = b + 1 - a := by
    calc
      (S.card : ℤ) = (Finset.Icc a b).card := by rw [hinterval]
      _ = b + 1 - a := Int.card_Icc_of_le (a := a) (b := b) (by omega)
  have htop : b + 1 = a + (S.card : ℤ) := by omega
  have hIccIco : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  refine ⟨a, ?_⟩
  calc
    S = Finset.Icc a b := hinterval
    _ = Finset.Ico a (b + 1) := hIccIco
    _ = Finset.Ico a (a + (S.card : ℤ)) := by rw [htop]

/-- Multiples count in the integer points of any order-convex real interval.
The finite set `S` is required to be exactly those integer points; this
formulation covers every endpoint convention and allows intervals on either
side of zero. -/
theorem realInterval_integer_multiples_count_error {J : Set ℝ}
    (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ (n : ℝ) ∈ J)
    (hJconv : ∀ x ∈ J, ∀ y ∈ J, ∀ t : ℝ,
      x ≤ t → t ≤ y → t ∈ J)
    (hSnonempty : S.Nonempty) (L : ℕ) (hcard : S.card = L)
    {d : ℕ} (hd : 0 < d) :
    |((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) -
        (L : ℝ) / (d : ℝ)| ≤ 1 := by
  have hconv : ∀ a ∈ S, ∀ b ∈ S, ∀ x : ℤ,
      a ≤ x → x ≤ b → x ∈ S := by
    intro a ha b hb x hax hxb
    apply (hS x).2
    apply hJconv (a : ℝ) ((hS a).1 ha) (b : ℝ) ((hS b).1 hb) (x : ℝ)
    · exact_mod_cast hax
    · exact_mod_cast hxb
  obtain ⟨a, hSinterval⟩ := finset_int_convex_eq_Ico S hSnonempty hconv
  have hlen : ((a + (S.card : ℤ) - a : ℤ) : ℝ) = (S.card : ℝ) := by
    push_cast
    ring
  have hcount := intIco_multiples_count_error
    (a := a) (b := a + (S.card : ℤ)) (by omega) hd
  have hcount' :
      |((Finset.Ico a (a + (S.card : ℤ))).filter
          (fun n : ℤ => (d : ℤ) ∣ n)).card -
        (S.card : ℝ) / (d : ℝ)| ≤ 1 := by
    simpa [hlen] using hcount
  have hfilterEq : (S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card =
      ((Finset.Ico a (a + (S.card : ℤ))).filter
        (fun n : ℤ => (d : ℤ) ∣ n)).card := by
    exact congrArg (fun T : Finset ℤ =>
      (T.filter (fun n : ℤ => (d : ℤ) ∣ n)).card) hSinterval
  calc
    |((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) -
        (L : ℝ) / (d : ℝ)| =
      |((Finset.Ico a (a + (S.card : ℤ))).filter
          (fun n : ℤ => (d : ℤ) ∣ n)).card -
        (S.card : ℝ) / (d : ℝ)| := by rw [hfilterEq, ← hcard]
    _ ≤ 1 := hcount'

/-- Summing a constant over the points satisfying a predicate gives the
constant times the cardinality of that filtered set. -/
theorem sum_ite_eq_filter_card_mul {α : Type*} [DecidableEq α]
    (S : Finset α) (P : α → Prop) [DecidablePred P] (c : ℝ) :
    (∑ x ∈ S, if P x then c else 0) = ((S.filter P).card : ℝ) * c := by
  rw [← Finset.sum_filter]
  simp

/-- Interchange the finite interval and divisor sums, exposing the exact
multiple counts needed for the weighted error estimate. -/
theorem finite_interval_divisor_sum_eq_count_sum
    (S : Finset ℤ) (D : Finset ℕ) (lambda : ℕ → ℝ) :
    (∑ n ∈ S, ∑ d ∈ D,
      if (d : ℤ) ∣ n then lambda d else 0) =
    ∑ d ∈ D, lambda d *
      ((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_ite_eq_filter_card_mul]
  ring

/-- After normalization by the number of interval points, each positive
modulus contributes at most `1/L` of density error. -/
theorem realInterval_normalized_multiples_error {J : Set ℝ}
    (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ (n : ℝ) ∈ J)
    (hJconv : ∀ x ∈ J, ∀ y ∈ J, ∀ t : ℝ,
      x ≤ t → t ≤ y → t ∈ J)
    (hSnonempty : S.Nonempty) (L : ℕ) (hcard : S.card = L)
    (hL : 0 < L) {d : ℕ} (hd : 0 < d) :
    |((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) / (L : ℝ) -
      1 / (d : ℝ)| ≤ 1 / (L : ℝ) := by
  have hcount := realInterval_integer_multiples_count_error
    S hS hJconv hSnonempty L hcard hd
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  let c : ℝ := (S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card
  have hidentity : c / (L : ℝ) - 1 / (d : ℝ) =
      (c - (L : ℝ) / (d : ℝ)) / (L : ℝ) := by
    dsimp [c]
    field_simp
  change |c / (L : ℝ) - 1 / (d : ℝ)| ≤ 1 / (L : ℝ)
  rw [hidentity, abs_div, abs_of_pos hLpos]
  exact (div_le_div_iff_of_pos_right hLpos).2 (by simpa [c] using hcount)

/-- A finite set of positive integer moduli below `y` has cardinal at most
`y`, with `y` interpreted as a real number. -/
theorem finset_positive_moduli_card_le {y : ℝ} (hy : 1 ≤ y)
    (D : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) < y) :
    (D.card : ℝ) ≤ y := by
  let f := ⌊y⌋₊
  have hsub : D ⊆ Finset.Icc 1 f := by
    intro d hd
    have hdpos := (hD d hd).1
    have hdlt := (hD d hd).2
    have hdfloor : d ≤ f := Nat.le_floor (le_of_lt hdlt)
    exact Finset.mem_Icc.mpr ⟨hdpos, hdfloor⟩
  have hcard := Finset.card_le_card hsub
  have hIcc : (Finset.Icc 1 f).card = f := by simp
  have hfloor : (f : ℝ) ≤ y := by
    dsimp [f]
    exact Nat.floor_le (by linarith)
  have hcardD : D.card ≤ f := by
    calc
      D.card ≤ (Finset.Icc 1 f).card := hcard
      _ = f := hIcc
  have hcardDReal : (D.card : ℝ) ≤ (f : ℝ) := by exact_mod_cast hcardD
  exact le_trans hcardDReal hfloor

/-- Weighted divisor sums over an arbitrary real interval differ from their
mean density by at most `y/L`, when the coefficients are bounded by one and
supported on positive moduli below `y`. -/
theorem realInterval_weighted_divisor_error {J : Set ℝ}
    (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ (n : ℝ) ∈ J)
    (hJconv : ∀ x ∈ J, ∀ y ∈ J, ∀ t : ℝ,
      x ≤ t → t ≤ y → t ∈ J)
    (hSnonempty : S.Nonempty) (L : ℕ) (hcard : S.card = L)
    (hL : 0 < L) {y : ℝ} (hy : 1 ≤ y)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) < y)
    (lambda : ℕ → ℝ)
    (hlambda : ∀ d ∈ D, -1 ≤ lambda d ∧ lambda d ≤ 1) :
    |(∑ n ∈ S, ∑ d ∈ D,
        if (d : ℤ) ∣ n then lambda d else 0) / (L : ℝ) -
      ∑ d ∈ D, lambda d / (d : ℝ)| ≤ y / (L : ℝ) := by
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
  have hcountSum := finite_interval_divisor_sum_eq_count_sum S D lambda
  have hidentity :
      (∑ n ∈ S, ∑ d ∈ D,
        if (d : ℤ) ∣ n then lambda d else 0) / (L : ℝ) -
          ∑ d ∈ D, lambda d / (d : ℝ) =
        ∑ d ∈ D, lambda d *
          (((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) /
            (L : ℝ) - 1 / (d : ℝ)) := by
    rw [hcountSum, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn : (d : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (hD d hd).1)
    have hLn : (L : ℝ) ≠ 0 := ne_of_gt hLpos
    field_simp
  have hterm : ∀ d ∈ D,
      |lambda d *
          (((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) /
            (L : ℝ) - 1 / (d : ℝ))| ≤ 1 / (L : ℝ) := by
    intro d hd
    have hdelta := realInterval_normalized_multiples_error
      S hS hJconv hSnonempty L hcard hL (hD d hd).1
    have hcoeff : |lambda d| ≤ 1 := abs_le.mpr (hlambda d hd)
    rw [abs_mul]
    calc
      |lambda d| *
          |((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) /
            (L : ℝ) - 1 / (d : ℝ)| ≤ 1 * (1 / (L : ℝ)) :=
        mul_le_mul hcoeff hdelta (abs_nonneg _) (by positivity)
      _ = 1 / (L : ℝ) := by ring
  have hDcard := finset_positive_moduli_card_le hy D hD
  rw [hidentity]
  calc
    |∑ d ∈ D, lambda d *
        (((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) /
          (L : ℝ) - 1 / (d : ℝ))| ≤
      ∑ d ∈ D, |lambda d *
        (((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) /
          (L : ℝ) - 1 / (d : ℝ))| :=
            Finset.abs_sum_le_sum_abs
              (fun d => lambda d *
                (((S.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) /
                  (L : ℝ) - 1 / (d : ℝ))) D
    _ ≤ ∑ d ∈ D, 1 / (L : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact hterm d hd
    _ = (D.card : ℝ) / (L : ℝ) := by simp [div_eq_mul_inv, mul_comm]
    _ ≤ y / (L : ℝ) := (div_le_div_iff_of_pos_right hLpos).2 hDcard

/-- The positive integer moduli strictly below the sieve level. -/
def rosserAllSModuli (y : ℝ) : Finset ℕ :=
  (Finset.range (⌊y⌋₊ + 1)).filter fun d => 0 < d ∧ (d : ℝ) < y

theorem rosserAllSCoefficients_zero_of_not_mem_moduli
    {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y) {d : ℕ}
    (hd : d ∈ Finset.range (⌊y⌋₊ + 1))
    (hnot : d ∉ rosserAllSModuli y) :
    rosserAllSLowerCoefficient z y d = 0 ∧
      rosserAllSUpperCoefficient z y d = 0 := by
  have hzero : rosserXi z y (0 : Fin 2) 0 = 0 := rosserXi_zero
  have hzero1 : rosserXi z y (1 : Fin 2) 0 = 0 := rosserXi_zero
  by_cases hdpos : 0 < d
  · have hnotlt : ¬ (d : ℝ) < y := by
      intro hlt
      apply hnot
      exact Finset.mem_filter.mpr ⟨hd, hdpos, hlt⟩
    have hdy : y ≤ (d : ℝ) := le_of_not_gt hnotlt
    exact rosserAllSCoefficient_eq_zero_of_ge hz hzy d hdy
  · have hd0 : d = 0 := by omega
    subst d
    constructor
    · unfold rosserAllSLowerCoefficient
      split_ifs <;> simp [hzero]
    · simp [rosserAllSUpperCoefficient, hzero1]

theorem rosserAllSDensitySum_eq_moduli {z y : ℝ}
    (hz : 2 ≤ z) (hzy : z ≤ y) :
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSLowerCoefficient z y d / (d : ℝ)) =
      ∑ d ∈ rosserAllSModuli y,
        rosserAllSLowerCoefficient z y d / (d : ℝ) ∧
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSUpperCoefficient z y d / (d : ℝ)) =
      ∑ d ∈ rosserAllSModuli y,
        rosserAllSUpperCoefficient z y d / (d : ℝ) := by
  have hsub : rosserAllSModuli y ⊆ Finset.range (⌊y⌋₊ + 1) := by
    intro d hd
    exact (Finset.mem_filter.mp hd).1
  constructor
  · symm
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hzero := rosserAllSCoefficients_zero_of_not_mem_moduli hz hzy hd hnot
    rcases hzero with ⟨hzero, _⟩
    simp [hzero]
  · symm
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hzero := rosserAllSCoefficients_zero_of_not_mem_moduli hz hzy hd hnot
    rcases hzero with ⟨_, hzero⟩
    simp [hzero]

theorem rosserPositiveDivisorSum_eq_moduliSum {y : ℝ} (n : ℕ)
    (f : ℕ → ℝ)
    (hzero : ∀ d ∈ rosserPositiveDivisorsBelow y n,
      y ≤ (d : ℝ) → f d = 0) :
    (∑ d ∈ rosserPositiveDivisorsBelow y n, f d) =
      ∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ (n : ℤ) then f d else 0 := by
  let T : Finset ℕ :=
    (rosserPositiveDivisorsBelow y n).filter fun d => (d : ℝ) < y
  have hleft : (∑ d ∈ rosserPositiveDivisorsBelow y n, f d) =
      ∑ d ∈ T, f d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hdy : y ≤ (d : ℝ) := le_of_not_gt (by
      intro hlt
      exact hnot (Finset.mem_filter.mpr ⟨hd, hlt⟩))
    exact hzero d hd hdy
  have hfilters : T = (rosserAllSModuli y).filter
      (fun d : ℕ => (d : ℤ) ∣ (n : ℤ)) := by
    ext d
    constructor
    · intro hd
      have hdT := Finset.mem_filter.mp hd
      have hdpos := Finset.mem_filter.mp hdT.1
      have hdivNat := hdpos.2.2
      apply Finset.mem_filter.mpr
      constructor
      · unfold rosserAllSModuli
        apply Finset.mem_filter.mpr
        exact ⟨hdpos.1, hdpos.2.1, hdT.2⟩
      · exact Int.natCast_dvd_natCast.mpr hdivNat
    · intro hd
      have hdT := Finset.mem_filter.mp hd
      have hdmod := Finset.mem_filter.mp hdT.1
      apply Finset.mem_filter.mpr
      constructor
      · unfold rosserPositiveDivisorsBelow
        apply Finset.mem_filter.mpr
        refine ⟨hdmod.1, ?_⟩
        exact ⟨hdmod.2.1, Int.natCast_dvd_natCast.mp hdT.2⟩
      · exact hdmod.2.2
  calc
    (∑ d ∈ rosserPositiveDivisorsBelow y n, f d) = ∑ d ∈ T, f d := hleft
    _ = ∑ d ∈ (rosserAllSModuli y).filter
        (fun d : ℕ => (d : ℤ) ∣ (n : ℤ)), f d := by rw [hfilters]
    _ = ∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ (n : ℤ) then f d else 0 := by
          rw [← Finset.sum_filter]

theorem rosserPositiveDivisorSum_eq_moduliSum_int {y : ℝ} (n : ℤ)
    (f : ℕ → ℝ)
    (hzero : ∀ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
      y ≤ (d : ℝ) → f d = 0) :
    (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs, f d) =
      ∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ n then f d else 0 := by
  have hnat := rosserPositiveDivisorSum_eq_moduliSum
    (y := y) n.natAbs f hzero
  simpa [Int.natCast_dvd_natCast] using hnat

theorem rosserAllSDivisorSum_eq_moduli {z y : ℝ}
    (hz : 2 ≤ z) (hzy : z ≤ y) (n : ℕ) :
    ((∑ d ∈ rosserPositiveDivisorsBelow y n,
        rosserAllSLowerCoefficient z y d) =
      ∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ (n : ℤ) then rosserAllSLowerCoefficient z y d else 0) ∧
    ((∑ d ∈ rosserPositiveDivisorsBelow y n,
        rosserAllSUpperCoefficient z y d) =
      ∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ (n : ℤ) then rosserAllSUpperCoefficient z y d else 0) := by
  constructor
  · apply rosserPositiveDivisorSum_eq_moduliSum (y := y) n
    intro d hd hdy
    exact (rosserAllSCoefficient_eq_zero_of_ge hz hzy d hdy).1
  · apply rosserPositiveDivisorSum_eq_moduliSum (y := y) n
    intro d hd hdy
    exact (rosserAllSCoefficient_eq_zero_of_ge hz hzy d hdy).2

theorem rosserAllSDivisorSum_eq_moduli_int {z y : ℝ}
    (hz : 2 ≤ z) (hzy : z ≤ y) (n : ℤ) :
    ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSLowerCoefficient z y d) =
      ∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ n then rosserAllSLowerCoefficient z y d else 0) ∧
    ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSUpperCoefficient z y d) =
      ∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ n then rosserAllSUpperCoefficient z y d else 0) := by
  constructor
  · apply rosserPositiveDivisorSum_eq_moduliSum_int (y := y) n
    intro d hd hdy
    exact (rosserAllSCoefficient_eq_zero_of_ge hz hzy d hdy).1
  · apply rosserPositiveDivisorSum_eq_moduliSum_int (y := y) n
    intro d hd hdy
    exact (rosserAllSCoefficient_eq_zero_of_ge hz hzy d hdy).2

theorem rosserAllSIntervalCountingError {J : Set ℝ}
    (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ (n : ℝ) ∈ J)
    (hJconv : ∀ x ∈ J, ∀ y ∈ J, ∀ t : ℝ,
      x ≤ t → t ≤ y → t ∈ J)
    (hSnonempty : S.Nonempty) (L : ℕ) (hcard : S.card = L)
    (hL : 0 < L) {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y) :
    (|(∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSLowerCoefficient z y d) / (L : ℝ) -
      ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSLowerCoefficient z y d / (d : ℝ)| ≤ y / (L : ℝ)) ∧
    (|(∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSUpperCoefficient z y d) / (L : ℝ) -
      ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSUpperCoefficient z y d / (d : ℝ)| ≤ y / (L : ℝ)) := by
  have hy : 1 ≤ y := le_trans (by norm_num : (1:ℝ) ≤ 2) (le_trans hz hzy)
  have hD : ∀ d ∈ rosserAllSModuli y, 0 < d ∧ (d : ℝ) < y := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  have hbound : ∀ d ∈ rosserAllSModuli y,
      -1 ≤ rosserAllSLowerCoefficient z y d ∧
        rosserAllSLowerCoefficient z y d ≤ 1 := by
    intro d hd
    exact ⟨(rosserAllSCoefficient_bounds (z := z) (y := y) d).1,
      (rosserAllSCoefficient_bounds (z := z) (y := y) d).2.1⟩
  have hbound' : ∀ d ∈ rosserAllSModuli y,
      -1 ≤ rosserAllSUpperCoefficient z y d ∧
        rosserAllSUpperCoefficient z y d ≤ 1 := by
    intro d hd
    exact ⟨(rosserAllSCoefficient_bounds (z := z) (y := y) d).2.2.1,
      (rosserAllSCoefficient_bounds (z := z) (y := y) d).2.2.2⟩
  have hsumLower :
      (∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSLowerCoefficient z y d) =
      ∑ n ∈ S, ∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ n then rosserAllSLowerCoefficient z y d else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    exact (rosserAllSDivisorSum_eq_moduli_int hz hzy n).1
  have hsumUpper :
      (∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSUpperCoefficient z y d) =
      ∑ n ∈ S, ∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ n then rosserAllSUpperCoefficient z y d else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    exact (rosserAllSDivisorSum_eq_moduli_int hz hzy n).2
  have hlow := realInterval_weighted_divisor_error
    S hS hJconv hSnonempty L hcard hL hy (rosserAllSModuli y) hD
    (rosserAllSLowerCoefficient z y) hbound
  have hupp := realInterval_weighted_divisor_error
    S hS hJconv hSnonempty L hcard hL hy (rosserAllSModuli y) hD
    (rosserAllSUpperCoefficient z y) hbound'
  have hdensity := rosserAllSDensitySum_eq_moduli hz hzy
  constructor
  · simpa [hsumLower, hdensity.1] using hlow
  · simpa [hsumUpper, hdensity.2] using hupp

/-- Euler's totient product formula identifies the finite sieve density with
`φ(W)/W` for the paper's squarefree prime product `W`. -/
theorem sieveDensity_eq_totient_div_primeProduct {w : ℝ} :
    sieveDensityProduct w =
      (Nat.totient (sievePrimeProduct w) : ℝ) /
        (sievePrimeProduct w : ℝ) := by
  let S := sievePrimesBelow w
  let W := sievePrimeProduct w
  have hprimeFactors : W.primeFactors = S := by
    rw [show W = ∏ p ∈ S, p by rfl]
    apply Nat.primeFactors_prod
    intro p hp
    have hpS : p ∈ S := hp
    change p ∈ sievePrimesBelow w at hpS
    simp only [sievePrimesBelow, Finset.mem_filter] at hpS
    exact hpS.2.1
  have hformula : (Nat.totient W : ℚ) =
      (W : ℚ) * ∏ p ∈ S, (1 - (p : ℚ)⁻¹) := by
    simpa [hprimeFactors, W, S] using Nat.totient_eq_mul_prod_factors W
  have hformulaRealQ : ((Nat.totient W : ℚ) : ℝ) =
      ((W : ℚ) : ℝ) * ∏ p ∈ S,
        (1 - (((p : ℚ)⁻¹ : ℚ) : ℝ)) := by
    exact_mod_cast hformula
  have hformulaReal : (Nat.totient W : ℝ) =
      (W : ℝ) * ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
    simpa using hformulaRealQ
  have hWnat : 0 < W := by
    dsimp [W, sievePrimeProduct]
    apply Finset.prod_pos
    intro p hp
    have hmem : p ∈ sievePrimesBelow w := hp
    simp only [sievePrimesBelow, Finset.mem_filter] at hmem
    exact hmem.2.1.pos
  have hWpos : 0 < (W : ℝ) := by exact_mod_cast hWnat
  have hVpos : 0 < sieveDensityProduct w := sieveDensityProduct_pos
  have hV : sieveDensityProduct w =
      ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
    unfold sieveDensityProduct
    simp [S]
  rw [hV]
  calc
    (∏ p ∈ S, (1 - (p : ℝ)⁻¹)) =
        ((W : ℝ) * ∏ p ∈ S, (1 - (p : ℝ)⁻¹)) / (W : ℝ) := by
          field_simp [ne_of_gt hWpos]
    _ = (Nat.totient W : ℝ) / (W : ℝ) := by
          simpa [W] using
            (congrArg (fun x : ℝ => x / (W : ℝ)) hformulaReal).symm

/-- The paper's ratio `W/φ(W)` is exactly the reciprocal sieve density. -/
theorem sievePrimeRatio_eq_inv_density {w : ℝ} :
    (sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ) =
      (sieveDensityProduct w)⁻¹ := by
  have hV := sieveDensity_eq_totient_div_primeProduct (w := w)
  have hWnat : 0 < sievePrimeProduct w := by
    dsimp [sievePrimeProduct]
    apply Finset.prod_pos
    intro p hp
    have hmem : p ∈ sievePrimesBelow w := hp
    simp only [sievePrimesBelow, Finset.mem_filter] at hmem
    exact hmem.2.1.pos
  have hWpos : 0 < (sievePrimeProduct w : ℝ) := by exact_mod_cast hWnat
  have hVpos : 0 < sieveDensityProduct w := sieveDensityProduct_pos
  have hWnat : 0 < sievePrimeProduct w := by exact_mod_cast hWpos
  have hφpos : 0 < (Nat.totient (sievePrimeProduct w) : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hWnat)
  rw [hV]
  field_simp [ne_of_gt hWpos, ne_of_gt hφpos]

/-- The comparison product over every integer from `2` through `N` telescopes
to `N`. This is the finite majorant used for the prime ratio. -/
theorem sieveIntegerRatioProduct_eq {N : ℕ} (hN : 2 ≤ N) :
    (∏ n ∈ Finset.Icc 2 N,
      (n : ℝ) / ((n : ℝ) - 1)) = (N : ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h : 2 ≤ N
    · rw [Finset.prod_Icc_succ_top (by omega)]
      rw [ih h]
      push_cast
      have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have hN1pos : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hNpos, hN1pos]
      <;> ring_nf
    · interval_cases N <;> norm_num [Finset.prod_Icc_succ_top]

/-- The finite totient ratio is bounded by the telescoping product over all
integers up to the strict prime cutoff. -/
theorem sievePrimeRatio_le_floor {w : ℝ} (hw : 2 ≤ w) :
    (sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ) ≤ (⌊w⌋₊ : ℝ) := by
  let S := sievePrimesBelow w
  let N := ⌊w⌋₊
  have hN : 2 ≤ N := Nat.le_floor (by exact_mod_cast hw)
  have hS : S ⊆ Finset.Icc 2 N := by
    intro p hp
    have hpS : p ∈ sievePrimesBelow w := hp
    simp only [sievePrimesBelow, Finset.mem_filter, Finset.mem_range] at hpS
    have hpLower : 2 ≤ p := hpS.2.1.two_le
    have hpUpper : p ≤ N := Nat.le_floor (by exact_mod_cast hpS.2.2.le)
    exact Finset.mem_Icc.mpr ⟨hpLower, hpUpper⟩
  have hratioProduct :
      (sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ) =
        ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
    rw [sievePrimeRatio_eq_inv_density, show sieveDensityProduct w =
      ∏ p ∈ S, (1 - 1 / (p : ℝ)) by simp [S, sieveDensityProduct]]
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpS : p ∈ sievePrimesBelow w := hp
    simp only [sievePrimesBelow, Finset.mem_filter, Finset.mem_range] at hpS
    have hpPrime := hpS.2.1
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hpSubPos : (0 : ℝ) < (p : ℝ) - 1 := by
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
      linarith
    field_simp
    <;> ring
  calc
    (sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ) =
        ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := hratioProduct
    _ ≤ ∏ n ∈ Finset.Icc 2 N, (n : ℝ) / ((n : ℝ) - 1) := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hS
      · intro p hp
        have hpS : p ∈ sievePrimesBelow w := hp
        simp only [sievePrimesBelow, Finset.mem_filter, Finset.mem_range] at hpS
        have hp2 : 2 ≤ p := hpS.2.1.two_le
        have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        have hpSub : 0 < (p : ℝ) - 1 := by linarith
        positivity
      · intro n hn hnotS
        have hnIcc := Finset.mem_Icc.mp hn
        have hnLower : (2 : ℝ) ≤ n := by exact_mod_cast hnIcc.1
        have hnSubPos : 0 < (n : ℝ) - 1 := by linarith
        have hfactor :
            (n : ℝ) / ((n : ℝ) - 1) = 1 + 1 / ((n : ℝ) - 1) := by
          field_simp
          <;> ring
        rw [hfactor]
        have hrecip : 0 ≤ 1 / ((n : ℝ) - 1) := by positivity
        linarith
    _ = (N : ℝ) := sieveIntegerRatioProduct_eq hN

/-- The finite prime ratio is at most the real sieve cutoff. -/
theorem sievePrimeRatio_le {w : ℝ} (hw : 2 ≤ w) :
    (sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ) ≤ w := by
  calc
    (sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ) ≤ (⌊w⌋₊ : ℝ) :=
          sievePrimeRatio_le_floor hw
    _ ≤ w := Nat.floor_le (by linarith)

/-- The blueprint's elementary bounds `1 ≤ R_w ≤ w` for the exact Cramér
density ratio `W(w)/φ(W(w))`. -/
theorem paperCramerDensity_bounds {w : ℝ} (hw : 2 ≤ w) :
    1 ≤ paperCramerDensity w ∧ paperCramerDensity w ≤ w := by
  have hWnat : 0 < sievePrimeProduct w := by
    dsimp [sievePrimeProduct]
    apply Finset.prod_pos
    intro p hp
    have hpS : p ∈ sievePrimesBelow w := hp
    simp only [sievePrimesBelow, Finset.mem_filter] at hpS
    exact hpS.2.1.pos
  have hWpos : 0 < (sievePrimeProduct w : ℝ) := by exact_mod_cast hWnat
  have hφpos : 0 < (Nat.totient (sievePrimeProduct w) : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hWnat)
  have hφleW : (Nat.totient (sievePrimeProduct w) : ℝ) ≤
      (sievePrimeProduct w : ℝ) := by
    exact_mod_cast Nat.totient_le (sievePrimeProduct w)
  constructor
  · change 1 ≤ (sievePrimeProduct w : ℝ) /
      (Nat.totient (sievePrimeProduct w) : ℝ)
    exact (le_div_iff₀ hφpos).2 (by simpa using hφleW)
  · change (sievePrimeProduct w : ℝ) /
      (Nat.totient (sievePrimeProduct w) : ℝ) ≤ w
    exact sievePrimeRatio_le hw

/-- The complete elementary arithmetic, growth, phase, and derivative package
from blueprint `lem:elementary`, assembled from the checked component results.
The asymptotic assertions use Mathlib's `little-o`/`big-O` filters, and the
prime-power sum is the explicit finite pair sum with `p^j ≤ N`. -/
theorem elementaryBounds :
    (∀ n : ℤ, 1 ≤ n →
      0 ≤ paperLambda n ∧ paperLambda n ≤ Real.log (n : ℝ)) ∧
    (∀ n : ℤ, 1 ≤ n → |paperMu n| ≤ 1) ∧
    (∀ w : ℝ, 2 ≤ w →
      1 ≤ paperCramerDensity w ∧ paperCramerDensity w ≤ w) ∧
    (∀ N : ℕ, 2 ≤ N →
      (N : ℝ)⁻¹ * paperHigherPrimePowerPairSum N ≤
        (Real.log (N : ℝ)) ^ 2 /
          (Real.log 2 * Real.sqrt (N : ℝ))) ∧
    (∀ a b : ℝ, 0 < a → 0 < b →
      (fun x : ℝ => Real.log x ^ a) =o[Filter.atTop] fun x => x ^ b) ∧
    (∀ ρ b : ℝ, 0 < ρ → ρ < 1 → 0 < b →
      (fun x : ℝ => Real.exp ((Real.log x) ^ ρ)) =o[Filter.atTop]
        fun x => x ^ b) ∧
    (∀ a b D : ℝ, 0 < a → 0 < b → 0 < D →
      (fun x : ℝ => x ^ (-b) * (Real.log x) ^ a) =O[Filter.atTop]
        fun x => (Real.log x) ^ (-D)) ∧
    (∀ u v : ℝ,
      ‖unitFrequencyPhase u - unitFrequencyPhase v‖ ≤
        2 * Real.pi * |u - v|) ∧
    (∀ c t : ℝ, 0 < t → ∀ j : ℕ,
      iteratedDeriv j (fun s : ℝ => s ^ c) t =
        (descPochhammer ℝ j).eval c * t ^ (c - (j : ℝ))) ∧
    (∀ c : ℝ, ∀ j : ℕ,
      (descPochhammer ℝ j).eval c =
        ∏ h ∈ Finset.range j, (c - (h : ℝ))) ∧
    (∀ c t : ℝ, NonIntegral c → 0 < t → ∀ j : ℕ,
      iteratedDeriv j (fun s : ℝ => s ^ c) t ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n hn => paperLambda_bounds hn
  · exact fun n hn => paperMu_abs_le_one hn
  · exact fun w hw => paperCramerDensity_bounds hw
  · exact fun N hN => paperHigherPrimePowerPairSum_normalized_le_of_two_le hN
  · exact fun a b _ha hb => paper_log_rpow_isLittleO_rpow hb
  · exact fun ρ b hρ hρlt hb =>
      paper_exp_log_rpow_isLittleO_rpow hρ hρlt hb
  · exact fun a b D ha hb hD => paper_inverse_power_log_isBigO ha hb hD
  · exact fun u v => paper_unitFrequencyPhase_lipschitz u v
  · exact fun c t ht j => paper_rpow_iterated_derivative_formula ht j
  · exact fun c j => paper_fallingFactorial_eq_product c j
  · exact fun c t hc ht j => paper_rpow_iterated_derivative_ne_zero hc ht j

/-- The interval counting error is absorbed by the finite sieve density and
the exponential term under the blueprint's original size hypotheses. -/
theorem sieveIntervalError_absorbed {L : ℕ} {w y : ℝ}
    (hL : 1 ≤ L) (hw : 2 ≤ w) (hwy : w ≤ y)
    (hyL : y ≤ (L : ℝ) ^ (1 / 10 : ℝ)) :
    y / L ≤ sieveDensityProduct w * Real.exp (-Real.log y / Real.log w) := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hy : 0 < y := by linarith
  have hlogw : (2 : ℝ) / 3 ≤ Real.log w :=
    (sieveLogTwo_bounds).1.trans (Real.log_le_log (by norm_num) hw)
  have hlogwpos : 0 < Real.log w := by linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith : (1 : ℝ) ≤ y)
  have hLpow : y ^ (10 : ℝ) ≤ L := by
    have hpow := Real.rpow_le_rpow (le_of_lt hy) hyL (by norm_num : (0 : ℝ) ≤ 10)
    have hpow' : y ^ (10 : ℝ) ≤ ((L : ℝ) ^ (1 / 10 : ℝ)) ^ (10 : ℝ) := hpow
    rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ L)] at hpow'
    norm_num at hpow'
    simpa using hpow'
  have hL10 : y ^ 10 ≤ L := by
    simpa [Real.rpow_natCast] using hLpow
  have hRle :
      (sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ) ≤ w := sievePrimeRatio_le hw
  have hRbound :
      ((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) * (y / L) ≤ y ^ 2 / L := by
    calc
      ((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) * (y / L) =
        (((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) * y) / L := by ring
      _ ≤ (w * y) / L := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hRle (le_of_lt hy)) (by positivity)
      _ ≤ (y * y) / L := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hwy (le_of_lt hy)) (by positivity)
      _ = y ^ 2 / L := by ring
  have hy2L : y ^ 2 / L ≤ y ^ (-8 : ℝ) := by
    have hLpos : 0 < (L : ℝ) := by linarith
    have hpowPos : 0 < y ^ 2 := by positivity
    have hLpowPos : 0 < y ^ 10 := by positivity
    have hratio : y ^ 2 / L ≤ y ^ 2 / y ^ 10 :=
      div_le_div_of_nonneg_left (by positivity) hLpowPos hL10
    calc
      y ^ 2 / L ≤ y ^ 2 / y ^ 10 := hratio
      _ = y ^ (-8 : ℝ) := by
        rw [← Real.rpow_natCast y 2, ← Real.rpow_natCast y 10,
          ← Real.rpow_sub hy]
        norm_num
  have hInvLog : (Real.log w)⁻¹ ≤ 3 / 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 / 3) hlogw
    norm_num at this ⊢
    linarith
  have hLogExp : y ^ (-8 : ℝ) ≤ Real.exp (-Real.log y / Real.log w) := by
    rw [Real.rpow_def_of_pos hy]
    apply Real.exp_le_exp.mpr
    have hInvLog8 : (Real.log w)⁻¹ ≤ 8 := hInvLog.trans (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hInvLog8 hlogy
    rw [div_eq_mul_inv]
    nlinarith
  have hRE :
      ((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) * (y / L) ≤
        Real.exp (-Real.log y / Real.log w) := hRbound.trans (hy2L.trans hLogExp)
  have hratio :
      (sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ) =
        (sieveDensityProduct w)⁻¹ := sievePrimeRatio_eq_inv_density
  rw [hratio] at hRE
  have hVpos : 0 < sieveDensityProduct w := sieveDensityProduct_pos
  calc
    y / L = sieveDensityProduct w *
        ((sieveDensityProduct w)⁻¹ * (y / L)) := by
          field_simp [ne_of_gt hVpos]
    _ ≤ sieveDensityProduct w * Real.exp (-Real.log y / Real.log w) :=
      mul_le_mul_of_nonneg_left hRE hVpos.le

/-- Combine the finite density approximation with the interval counting error
for each of the two explicit Rosser coefficient choices. -/
theorem rosserAllSIntervalMeanError {J : Set ℝ} (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ (n : ℝ) ∈ J)
    (hJconv : ∀ x ∈ J, ∀ y ∈ J, ∀ t : ℝ,
      x ≤ t → t ≤ y → t ∈ J)
    (hSnonempty : S.Nonempty) (L : ℕ) (hcard : S.card = L)
    (hL : 1 ≤ L) {w y : ℝ} (hw : 2 ≤ w) (hwy : w ≤ y)
    (hyL : y ≤ (L : ℝ) ^ (1 / 10 : ℝ)) :
    (|(∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSLowerCoefficient w y d) / (L : ℝ) -
      sieveDensityProduct w| ≤
        (sieveD + 1) * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w)) ∧
    (|(∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSUpperCoefficient w y d) / (L : ℝ) -
      sieveDensityProduct w| ≤
        (sieveD + 1) * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w)) := by
  have hcount := rosserAllSIntervalCountingError
    S hS hJconv hSnonempty L hcard (by omega) hw hwy
  have hdensity := rosserAllSDensityError hw hwy
  have habsorb := sieveIntervalError_absorbed hL hw hwy hyL
  have hVpos : 0 < sieveDensityProduct w := sieveDensityProduct_pos
  have hEpos : 0 < Real.exp (-Real.log y / Real.log w) := Real.exp_pos _
  have hDnonneg : 0 ≤ sieveD * sieveDensityProduct w *
      Real.exp (-Real.log y / Real.log w) :=
    mul_nonneg (mul_nonneg (le_trans (Real.exp_pos 2).le (le_max_right _ _)) hVpos.le)
      hEpos.le
  have hexp : Real.exp (-(Real.log y / Real.log w)) =
      Real.exp (-Real.log y / Real.log w) := by
    congr 1
    ring
  have hsumBound : y / L +
      sieveD * sieveDensityProduct w *
        Real.exp (-Real.log y / Real.log w) ≤
      (sieveD + 1) * sieveDensityProduct w *
        Real.exp (-Real.log y / Real.log w) := by
    calc
      y / L + (sieveD * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w)) ≤
        sieveDensityProduct w * Real.exp (-Real.log y / Real.log w) +
          sieveD * sieveDensityProduct w * Real.exp (-Real.log y / Real.log w) :=
            add_le_add habsorb le_rfl
      _ = (sieveD + 1) * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w) := by ring
  constructor
  · let A := (∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSLowerCoefficient w y d) / (L : ℝ)
    let B := ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSLowerCoefficient w y d / (d : ℝ)
    have hden : |B - sieveDensityProduct w| ≤
        sieveD * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w) := by
      simpa [B, hexp] using hdensity.1
    have hsum : |A - sieveDensityProduct w| ≤
        y / L + sieveD * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w) := by
      calc
        |A - sieveDensityProduct w| = |(A - B) +
            (B - sieveDensityProduct w)| := by congr 1 <;> ring
        _ ≤ |A - B| + |B - sieveDensityProduct w| := abs_add_le _ _
        _ ≤ y / L + sieveD * sieveDensityProduct w *
            Real.exp (-Real.log y / Real.log w) := add_le_add hcount.1 hden
    exact (hsum.trans hsumBound)
  · let A := (∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSUpperCoefficient w y d) / (L : ℝ)
    let B := ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        rosserAllSUpperCoefficient w y d / (d : ℝ)
    have hden : |B - sieveDensityProduct w| ≤
        sieveD * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w) := by
      simpa [B, hexp] using hdensity.2
    have hsum : |A - sieveDensityProduct w| ≤
        y / L + sieveD * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w) := by
      calc
        |A - sieveDensityProduct w| = |(A - B) +
            (B - sieveDensityProduct w)| := by congr 1 <;> ring
        _ ≤ |A - B| + |B - sieveDensityProduct w| := abs_add_le _ _
        _ ≤ y / L + sieveD * sieveDensityProduct w *
            Real.exp (-Real.log y / Real.log w) := add_le_add hcount.2 hden
    exact (hsum.trans hsumBound)

/-- The pointwise Rosser sandwich controls the averaged scaled absolute error
for each sign, with the blueprint's constant `C_S = 2(D+1)`. -/
theorem rosserAllSIntervalAbsoluteError {J : Set ℝ} (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ (n : ℝ) ∈ J)
    (hJconv : ∀ x ∈ J, ∀ y ∈ J, ∀ t : ℝ,
      x ≤ t → t ≤ y → t ∈ J)
    (hSnonempty : S.Nonempty) (L : ℕ) (hcard : S.card = L)
    (hL : 1 ≤ L) {w y : ℝ} (hw : 2 ≤ w) (hwy : w ≤ y)
    (hyL : y ≤ (L : ℝ) ^ (1 / 10 : ℝ)) :
    (∑ n ∈ S, |((sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        ((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d)|) / (L : ℝ) ≤
      sieveConstant * Real.exp (-Real.log y / Real.log w) ∧
    (∑ n ∈ S, |((sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        ((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d)|) / (L : ℝ) ≤
      sieveConstant * Real.exp (-Real.log y / Real.log w) := by
  have hmean := rosserAllSIntervalMeanError
    S hS hJconv hSnonempty L hcard hL hw hwy hyL
  have hRpos : 0 < (sievePrimeProduct w : ℝ) /
      (Nat.totient (sievePrimeProduct w) : ℝ) := by
    rw [sievePrimeRatio_eq_inv_density]
    exact inv_pos.mpr sieveDensityProduct_pos
  have hVpos : 0 < sieveDensityProduct w := sieveDensityProduct_pos
  let R := (sievePrimeProduct w : ℝ) /
    (Nat.totient (sievePrimeProduct w) : ℝ)
  let E := Real.exp (-Real.log y / Real.log w)
  let lowMean := (∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
    rosserAllSLowerCoefficient w y d) / (L : ℝ)
  let upMean := (∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
    rosserAllSUpperCoefficient w y d) / (L : ℝ)
  have hlowMean : |lowMean - sieveDensityProduct w| ≤
      (sieveD + 1) * sieveDensityProduct w * E := by
    simpa [lowMean, E] using hmean.1
  have hupMean : |upMean - sieveDensityProduct w| ≤
      (sieveD + 1) * sieveDensityProduct w * E := by
    simpa [upMean, E] using hmean.2
  have hgap : upMean - lowMean ≤
      2 * ((sieveD + 1) * sieveDensityProduct w * E) := by
    rw [abs_le] at hlowMean hupMean
    linarith
  have hscaleGap : R * (upMean - lowMean) ≤ sieveConstant * E := by
    have hR : R = (sieveDensityProduct w)⁻¹ := by
      dsimp [R]
      exact sievePrimeRatio_eq_inv_density
    rw [hR]
    have hmul := mul_le_mul_of_nonneg_left hgap (inv_pos.mpr hVpos).le
    have hcancel : (sieveDensityProduct w)⁻¹ *
        (2 * ((sieveD + 1) * sieveDensityProduct w * E)) =
        2 * (sieveD + 1) * E := by
      field_simp [ne_of_gt hVpos]
      <;> ring
    calc
      (sieveDensityProduct w)⁻¹ * (upMean - lowMean) ≤
          (sieveDensityProduct w)⁻¹ *
            (2 * ((sieveD + 1) * sieveDensityProduct w * E)) := hmul
      _ = 2 * (sieveD + 1) * E := hcancel
      _ = sieveConstant * E := by simp [sieveConstant]
  have hpointLower : ∀ n : ℤ,
      |R * (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        R * (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSLowerCoefficient w y d)| ≤
      R * ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSUpperCoefficient w y d) -
        (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSLowerCoefficient w y d)) := by
    intro n
    have hsand := rosserAllSPointwise hw hwy n
    have hR : 0 ≤ R := le_of_lt hRpos
    have hleft : 0 ≤ R *
        ((if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d)) :=
      mul_nonneg hR (sub_nonneg.mpr hsand.1)
    have hright : R *
        ((if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d)) ≤
        R * ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hsand.2 _) hR
    rw [show R * (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        R * (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSLowerCoefficient w y d) = R *
          ((if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
            (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
              rosserAllSLowerCoefficient w y d)) by ring]
    rw [abs_of_nonneg hleft]
    exact hright
  have hpointUpper : ∀ n : ℤ,
      |R * (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        R * (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSUpperCoefficient w y d)| ≤
      R * ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSUpperCoefficient w y d) -
        (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSLowerCoefficient w y d)) := by
    intro n
    have hsand := rosserAllSPointwise hw hwy n
    have hR : 0 ≤ R := le_of_lt hRpos
    let I := if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0
    let U := ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
      rosserAllSUpperCoefficient w y d
    let D := ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
      rosserAllSLowerCoefficient w y d
    have hraw : R * I - R * U ≤ 0 := by
      dsimp [I, U]
      exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hsand.2 hR)
    have hraw' : R * (I - U) ≤ 0 := by
      rw [mul_sub]
      exact hraw
    have hgapnonneg : 0 ≤ U - D := sub_nonneg.mpr (le_trans hsand.1 hsand.2)
    have hgaple : U - I ≤ U - D := sub_le_sub_left hsand.1 U
    have hscaled : R * (U - I) ≤ R * (U - D) :=
      mul_le_mul_of_nonneg_left hgaple hR
    rw [show R * (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        R * (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSUpperCoefficient w y d) = R *
          ((if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
            (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
              rosserAllSUpperCoefficient w y d)) by ring]
    rw [abs_of_nonpos hraw']
    dsimp [I, U, D] at hscaled ⊢
    convert hscaled using 1 <;> ring
  have hgapSum :
      (∑ n ∈ S,
        ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSUpperCoefficient w y d) -
        (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSLowerCoefficient w y d))) =
      (upMean - lowMean) * (L : ℝ) := by
    have hLpos : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
    dsimp [upMean, lowMean]
    rw [Finset.sum_sub_distrib]
    field_simp [ne_of_gt hLpos]
    <;> ring
  have hsumLower :
      (∑ n ∈ S, |R * (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        R * (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSLowerCoefficient w y d)|) ≤
        R * (∑ n ∈ S,
          ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d))) := by
    calc
      _ ≤ ∑ n ∈ S, R * ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d)) :=
        Finset.sum_le_sum fun n hn => hpointLower n
      _ = R * (∑ n ∈ S,
          ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d))) := by rw [Finset.mul_sum]
  have hsumUpper :
      (∑ n ∈ S, |R * (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        R * (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSUpperCoefficient w y d)|) ≤
        R * (∑ n ∈ S,
          ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d))) := by
    calc
      _ ≤ ∑ n ∈ S, R * ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d)) :=
        Finset.sum_le_sum fun n hn => hpointUpper n
      _ = R * (∑ n ∈ S,
          ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d))) := by rw [Finset.mul_sum]
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hfinal : R * (upMean - lowMean) ≤ sieveConstant * E := by
    simpa [R, E, sieveConstant, upMean, lowMean, hgapSum] using hscaleGap
  constructor <;>
    calc
      _ ≤ (R * (∑ n ∈ S,
          ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d) -
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d)))) / (L : ℝ) :=
          div_le_div_of_nonneg_right (by assumption) (le_of_lt hLpos)
      _ = R * (upMean - lowMean) := by rw [hgapSum]; field_simp [ne_of_gt hLpos]
      _ ≤ sieveConstant * E := hfinal

/-- The blueprint's full interval sieve contract `ls:fundamental`, using the
explicit lower and upper coefficients constructed by `rosserAllS`. -/
theorem rosserFundamentalInterval {J : Set ℝ} (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ (n : ℝ) ∈ J)
    (hJconv : ∀ x ∈ J, ∀ y ∈ J, ∀ t : ℝ,
      x ≤ t → t ≤ y → t ∈ J)
    {L : ℕ} (hcard : S.card = L) (hL : 1 ≤ L) {w y : ℝ}
    (hw : 2 ≤ w) (hwy : w ≤ y)
    (hyL : y ≤ (L : ℝ) ^ (1 / 10 : ℝ)) :
    (∀ d : ℕ,
      (-1 ≤ rosserAllSLowerCoefficient w y d ∧
        rosserAllSLowerCoefficient w y d ≤ 1) ∧
      (-1 ≤ rosserAllSUpperCoefficient w y d ∧
        rosserAllSUpperCoefficient w y d ≤ 1)) ∧
    (∀ d : ℕ,
      (rosserAllSLowerCoefficient w y d ≠ 0 →
        0 < d ∧ (d : ℝ) ≤ y) ∧
      (rosserAllSUpperCoefficient w y d ≠ 0 →
        0 < d ∧ (d : ℝ) ≤ y)) ∧
    (∀ n : ℤ,
      (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSLowerCoefficient w y d) ≤
        (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) ∧
      (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) ≤
        (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSUpperCoefficient w y d)) ∧
    (|(∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSLowerCoefficient w y d) / (L : ℝ) -
      sieveDensityProduct w| ≤
        sieveConstant * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w) ∧
     |(∑ n ∈ S, ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSUpperCoefficient w y d) / (L : ℝ) -
      sieveDensityProduct w| ≤
        sieveConstant * sieveDensityProduct w *
          Real.exp (-Real.log y / Real.log w)) ∧
    (∑ n ∈ S, |((sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        ((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSLowerCoefficient w y d)|) / (L : ℝ) ≤
      sieveConstant * Real.exp (-Real.log y / Real.log w) ∧
    (∑ n ∈ S, |((sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
        ((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d)|) / (L : ℝ) ≤
      sieveConstant * Real.exp (-Real.log y / Real.log w) := by
  have hLpos : 0 < L := by omega
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hLpos)
  have hcoeff := rosserAllSCoefficient_bounds (z := w) (y := y)
  have hmeans := rosserAllSIntervalMeanError
    S hS hJconv hSnonempty L hcard hL hw hwy hyL
  have habs := rosserAllSIntervalAbsoluteError
    S hS hJconv hSnonempty L hcard hL hw hwy hyL
  have hVpos : 0 < sieveDensityProduct w := sieveDensityProduct_pos
  have hEpos : 0 < Real.exp (-Real.log y / Real.log w) := Real.exp_pos _
  have hDpos : 0 < sieveD := lt_of_lt_of_le (Real.exp_pos 2) (le_max_right _ _)
  have hC : sieveD + 1 ≤ sieveConstant := by
    simp [sieveConstant]
    linarith
  have hmore : (sieveD + 1) * sieveDensityProduct w *
      Real.exp (-Real.log y / Real.log w) ≤
      sieveConstant * sieveDensityProduct w *
        Real.exp (-Real.log y / Real.log w) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC hVpos.le) hEpos.le
  refine ⟨?_, ?_, ?_, ?_, habs.1, habs.2⟩
  · intro d
    exact ⟨⟨hcoeff d |>.1, hcoeff d |>.2.1⟩,
      ⟨hcoeff d |>.2.2.1, hcoeff d |>.2.2.2⟩⟩
  · intro d
    constructor
    · intro hne
      have hzero : rosserAllSLowerCoefficient w y 0 = 0 := by
        unfold rosserAllSLowerCoefficient
        split_ifs <;> simp [rosserXi_zero]
      have hdne : d ≠ 0 := by
        intro hd
        subst d
        exact hne hzero
      have hdpos : 0 < d := Nat.pos_of_ne_zero hdne
      have hnot : ¬ y ≤ (d : ℝ) := by
        intro hdy
        exact hne ((rosserAllSCoefficient_eq_zero_of_ge hw hwy d hdy).1)
      exact ⟨hdpos, le_of_lt (lt_of_not_ge hnot)⟩
    · intro hne
      have hzero : rosserAllSUpperCoefficient w y 0 = 0 := by
        simp [rosserAllSUpperCoefficient, rosserXi_zero]
      have hdne : d ≠ 0 := by
        intro hd
        subst d
        exact hne hzero
      have hdpos : 0 < d := Nat.pos_of_ne_zero hdne
      have hnot : ¬ y ≤ (d : ℝ) := by
        intro hdy
        exact hne ((rosserAllSCoefficient_eq_zero_of_ge hw hwy d hdy).2)
      exact ⟨hdpos, le_of_lt (lt_of_not_ge hnot)⟩
  · intro n
    exact rosserAllSPointwise hw hwy n
  · constructor
    · exact hmeans.1.trans hmore
    · exact hmeans.2.trans hmore

end

end FractionalPrimes

end
