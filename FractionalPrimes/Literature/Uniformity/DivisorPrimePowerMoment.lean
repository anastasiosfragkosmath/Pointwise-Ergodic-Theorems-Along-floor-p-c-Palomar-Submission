module

public import FractionalPrimes.Literature.Uniformity.DivisorMomentBounds
public import Mathlib.Data.Sym.NatCard
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Multiset.MapFold

/-!
# Prime-power divisor moments

The proof encodes a tuple of weak compositions by aligning their positions and
recording the resulting tuples of labels. Coordinate marginals recover every
input composition, giving the exact injection described in the Astra source.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

noncomputable section

private def symPositionValue {α : Type*} {a : ℕ} (s : Sym α a) (j : Fin a) : α :=
  s.1.toList.get (Fin.cast ((Multiset.length_toList s.1).trans s.2).symm j)

private def encodeSymRows {k r a : ℕ}
    (v : Fin r → Sym (Fin k) a) : Sym (Fin r → Fin k) a :=
  ⟨Multiset.ofList (List.ofFn fun j : Fin a => fun i => symPositionValue (v i) j), by simp⟩

private theorem ofFn_symPositionValue {α : Type*} {a : ℕ} (s : Sym α a) :
    List.ofFn (fun j : Fin a => symPositionValue s j) = s.1.toList := by
  let hlen : s.1.toList.length = a := (Multiset.length_toList s.1).trans s.2
  calc
    List.ofFn (fun j : Fin a => symPositionValue s j) = List.ofFn s.1.toList.get := by
      exact (List.ofFn_congr hlen s.1.toList.get).symm
    _ = s.1.toList := List.ofFn_get _

private theorem encodeSymRows_map_coord {k r a : ℕ}
    (v : Fin r → Sym (Fin k) a) (i : Fin r) :
    (encodeSymRows v).1.map (fun row => row i) = (v i).1 := by
  change (Multiset.ofList (List.ofFn fun j : Fin a => fun jx =>
    symPositionValue (v jx) j)).map (fun row => row i) = (v i).1
  rw [Multiset.map_coe, List.map_ofFn]
  change Multiset.ofList (List.ofFn fun j : Fin a => symPositionValue (v i) j) = (v i).1
  rw [ofFn_symPositionValue]
  exact Multiset.coe_toList (v i).1

private theorem encodeSymRows_injective {k r a : ℕ} :
    Function.Injective (@encodeSymRows k r a) := by
  intro v w h
  funext i
  apply Sym.ext
  have hmap := congrArg (fun s : Sym (Fin r → Fin k) a => s.1.map (fun row => row i)) h
  rw [encodeSymRows_map_coord, encodeSymRows_map_coord] at hmap
  exact hmap

/-- The stars-and-bars inequality obtained from the explicit aligned-position
injection: the `r`-fold product of `a`-multisets from `Fin k` injects into the
multisets of size `a` from the `r`-tuples of labels. -/
theorem multichoose_power_le_multichoose_power (k r a : ℕ) :
    (Nat.card (Sym (Fin k) a)) ^ r ≤ Nat.card (Sym (Fin r → Fin k) a) := by
  have h := Nat.card_le_card_of_injective
    (@encodeSymRows k r a) (@encodeSymRows_injective k r a)
  simpa only [Nat.card_fun, Nat.card_fin] using h

/-- Binomial form of the exact weak-composition injection. -/
theorem choose_power_le_choose_power (k r a : ℕ) :
    ((a + k - 1).choose a) ^ r ≤ (a + k ^ r - 1).choose a := by
  have h := multichoose_power_le_multichoose_power k r a
  rw [Sym.natCard_sym_eq_choose, Sym.natCard_sym_eq_choose] at h
  simp only [Nat.card_fin] at h
  have hlabels : Nat.card (Fin r → Fin k) = k ^ r := by
    simp
  rw [hlabels] at h
  simpa [Nat.add_comm] using h

/-- Exact prime-power case of `d_k(n)^r ≤ d_{k^r}(n)`. -/
theorem divisorFunction_prime_pow_moment
    (p k r a : ℕ) (hp : p.Prime) (hk : 0 < k) (_hr : 0 < r) :
    (divisorFunction k ⟨p ^ a, Nat.pow_pos hp.pos⟩) ^ r ≤
      divisorFunction (k ^ r) ⟨p ^ a, Nat.pow_pos hp.pos⟩ := by
  have hkr : 0 < k ^ r := Nat.pow_pos hk
  have hleft : divisorFunction k ⟨p ^ a, Nat.pow_pos hp.pos⟩ =
      (a + k - 1).choose a := by
    have hkEq : k = k - 1 + 1 := by omega
    calc
      divisorFunction k ⟨p ^ a, Nat.pow_pos hp.pos⟩ =
          divisorFunction (k - 1 + 1) ⟨p ^ a, Nat.pow_pos hp.pos⟩ :=
        congrArg (fun m => divisorFunction m ⟨p ^ a, Nat.pow_pos hp.pos⟩) hkEq
      _ = (a + (k - 1)).choose (k - 1) :=
        positiveDivisorFunction_prime_pow p (k - 1) a hp
      _ = (a + (k - 1)).choose a := (Nat.choose_symm_add).symm
      _ = (a + k - 1).choose a := by
        congr 1
        omega
  have hright : divisorFunction (k ^ r) ⟨p ^ a, Nat.pow_pos hp.pos⟩ =
      (a + k ^ r - 1).choose a := by
    have hkrEq : k ^ r = k ^ r - 1 + 1 := by omega
    calc
      divisorFunction (k ^ r) ⟨p ^ a, Nat.pow_pos hp.pos⟩ =
          divisorFunction (k ^ r - 1 + 1) ⟨p ^ a, Nat.pow_pos hp.pos⟩ :=
        congrArg (fun m => divisorFunction m ⟨p ^ a, Nat.pow_pos hp.pos⟩) hkrEq
      _ = (a + (k ^ r - 1)).choose (k ^ r - 1) :=
        positiveDivisorFunction_prime_pow p (k ^ r - 1) a hp
      _ = (a + (k ^ r - 1)).choose a := (Nat.choose_symm_add).symm
      _ = (a + k ^ r - 1).choose a := by
        congr 1
        omega
  rw [hleft, hright]
  exact choose_power_le_choose_power k r a

end

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.multichoose_power_le_multichoose_power
#print axioms FractionalPrimes.Literature.Uniformity.choose_power_le_choose_power
#print axioms FractionalPrimes.Literature.Uniformity.divisorFunction_prime_pow_moment
