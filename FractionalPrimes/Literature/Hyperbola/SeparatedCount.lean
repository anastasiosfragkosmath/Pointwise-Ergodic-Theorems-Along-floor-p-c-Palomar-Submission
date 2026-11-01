module

public import FractionalPrimes.Literature.Hyperbola.GeometricData
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.NatAbs

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

open Set

/-- A finite set of points separated by at least `h` inside an order-convex
interval contained in `[a,b]` has at most `(b-a)/h+1` points. The enclosing
interval may have either endpoint included or excluded. -/
theorem separatedIntervalCount
    (I : Set ℝ) (_hI : Set.OrdConnected I)
    (S : Finset ℝ) (a b B h : ℝ)
    (_hab : a ≤ b) (hB : 0 ≤ B) (hlen : b - a ≤ B)
    (hIab : I ⊆ Set.Icc a b)
    (hSI : ∀ x ∈ S, x ∈ I)
    (hh : 0 < h)
    (hsep : ∀ ⦃x y : ℝ⦄, x ∈ S → y ∈ S → x ≠ y → h ≤ |x - y|) :
    (S.card : ℝ) ≤ B / h + 1 := by
  classical
  let f : ℝ → ℕ := fun x => Nat.floor ((x - a) / h)
  have hnorm_nonneg (x : ℝ) (hx : x ∈ S) : 0 ≤ (x - a) / h := by
    have hxI := hIab (hSI x hx)
    exact div_nonneg (sub_nonneg.mpr hxI.1) hh.le
  have hstrict (x y : ℝ) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
      f x < f y := by
    have hdist : h ≤ y - x := by
      have := hsep hx hy (ne_of_lt hxy)
      simpa [abs_of_neg (sub_neg.mpr hxy)] using this
    have hnorm : (x - a) / h + 1 ≤ (y - a) / h := by
      have hrewrite : (x - a) / h + 1 = ((x - a) + h) / h := by
        field_simp [ne_of_gt hh]
      rw [hrewrite]
      exact (div_le_div_iff_of_pos_right hh).2 (by linarith)
    dsimp [f]
    have hfloor := Nat.floor_mono hnorm
    rw [Nat.floor_add_one (hnorm_nonneg x hx)] at hfloor
    omega
  have hinj : Set.InjOn f S := by
    intro x hx y hy hfxfy
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact (Nat.ne_of_lt (hstrict x y hx hy hlt)) hfxfy
    · exact (Nat.ne_of_gt (hstrict y x hy hx hgt)) hfxfy
  have himage : S.image f ⊆ Finset.range (Nat.floor (B / h) + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    have hxI := hIab (hSI x hx)
    have hnum : x - a ≤ B := (sub_le_sub_right hxI.2 a).trans hlen
    exact div_le_div_of_nonneg_right hnum hh.le
  have hcard : S.card ≤ Nat.floor (B / h) + 1 := by
    calc
      S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (Nat.floor (B / h) + 1)).card := Finset.card_le_card himage
      _ = Nat.floor (B / h) + 1 := Finset.card_range _
  have hfloor : (Nat.floor (B / h) : ℝ) ≤ B / h := by
    exact Nat.floor_le (div_nonneg hB hh.le)
  have hcardReal : (S.card : ℝ) ≤ (Nat.floor (B / h) : ℝ) + 1 := by
    exact_mod_cast hcard
  exact hcardReal.trans (by simpa [add_comm] using add_le_add_right hfloor 1)

/-- A fixed integer residue class modulo positive `u` contributes at most
`B/u+1` points to an order-convex interval of length at most `B`. -/
theorem residueClassIntervalCount
    (I : Set ℝ) (hI : Set.OrdConnected I)
    (S : Finset ℤ) (residue : ℤ) (u : ℕ)
    (a b B : ℝ) (hab : a ≤ b) (hB : 0 ≤ B) (hlen : b - a ≤ B)
    (hIab : I ⊆ Set.Icc a b)
    (hSI : ∀ n ∈ S, (n : ℝ) ∈ I)
    (hu : 0 < u)
    (hres : ∀ n ∈ S, n ≡ residue [ZMOD (u : ℤ)]) :
    (S.card : ℝ) ≤ B / (u : ℝ) + 1 := by
  classical
  let T : Finset ℝ := S.image fun n : ℤ => (n : ℝ)
  have hcast_inj : Set.InjOn (fun n : ℤ => (n : ℝ)) S := by
    intro m hm n hn hmn
    exact Int.cast_injective hmn
  have hcardT : T.card = S.card := by
    simp [T, Finset.card_image_of_injOn hcast_inj]
  have hTI : ∀ x ∈ T, x ∈ I := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
    exact hSI n hn
  have hTsep :
      ∀ ⦃x y : ℝ⦄, x ∈ T → y ∈ T → x ≠ y → (u : ℝ) ≤ |x - y| := by
    intro x y hx hy hxy
    rcases Finset.mem_image.mp hx with ⟨m, hm, hxm⟩
    rcases Finset.mem_image.mp hy with ⟨n, hn, hyn⟩
    subst x
    subst y
    have hmn : m ≠ n := by
      intro h
      subst n
      exact hxy rfl
    have hmod : m ≡ n [ZMOD (u : ℤ)] := (hres m hm).trans (hres n hn).symm
    have hdiv : (u : ℤ) ∣ n - m := Int.ModEq.dvd hmod
    have hdiff : n - m ≠ 0 := by omega
    have hspacingInt : (u : ℤ) ≤ |n - m| := Int.le_abs_of_dvd hdiff hdiv
    have hspacingReal : (u : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by
      exact_mod_cast hspacingInt
    simpa [abs_sub_comm] using hspacingReal
  have hcount := separatedIntervalCount I hI T a b B (u : ℝ)
    hab hB hlen hIab hTI (by exact_mod_cast hu) hTsep
  rw [hcardT] at hcount
  exact hcount

/-- The exact nonnegative-root inequality for a difference of square roots. -/
theorem sqrtDifference_le_sqrtSub
    (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    Real.sqrt B - Real.sqrt A ≤ Real.sqrt (B - A) := by
  have hB : 0 ≤ B := le_trans hA hAB
  have hBA : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hroot : Real.sqrt A ≤ Real.sqrt B := Real.sqrt_le_sqrt hAB
  have hprod : A ≤ Real.sqrt A * Real.sqrt B := by
    calc
      A = (Real.sqrt A) ^ 2 := (Real.sq_sqrt hA).symm
      _ ≤ Real.sqrt A * Real.sqrt B := by
        simpa [pow_two] using
          (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg A))
  have hsq : (Real.sqrt B - Real.sqrt A) ^ 2 ≤ B - A := by
    rw [sub_sq]
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB, hprod]
  have hsq' : (Real.sqrt B - Real.sqrt A) ^ 2 ≤ (Real.sqrt (B - A)) ^ 2 := by
    rw [Real.sq_sqrt hBA]
    exact hsq
  exact (sq_le_sq₀ (sub_nonneg.mpr hroot) (Real.sqrt_nonneg _)).mp hsq'

end FractionalPrimes.Literature.Hyperbola
