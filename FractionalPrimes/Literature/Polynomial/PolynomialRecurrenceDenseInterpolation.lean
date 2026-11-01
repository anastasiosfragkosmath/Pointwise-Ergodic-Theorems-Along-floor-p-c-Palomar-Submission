module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Finset.Sort
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

private theorem strictMono_fin_nat_gap {m : ℕ} (f : Fin m → ℕ)
    (hf : StrictMono f) (a b : Fin m) (hab : a.1 ≤ b.1) :
    f a + (b.1 - a.1) ≤ f b := by
  have hstep : ∀ k, ∀ hk : a.1 + k < m,
      f a + k ≤ f ⟨a.1 + k, hk⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp
    | succ k ih =>
        intro hk
        have hk' : a.1 + k < m := by omega
        have hinc : f ⟨a.1 + k, hk'⟩ < f ⟨a.1 + (k + 1), hk⟩ := by
          apply hf
          exact Fin.mk_lt_mk.mpr (by omega)
        have hprev := ih hk'
        calc
          f a + (k + 1) = (f a + k) + 1 := by omega
          _ ≤ f ⟨a.1 + k, hk'⟩ + 1 := Nat.add_le_add_right hprev 1
          _ ≤ f ⟨a.1 + (k + 1), hk⟩ := Nat.succ_le_iff.mpr hinc
  have hidxlt : a.1 + (b.1 - a.1) < m := by omega
  have hidx : (⟨a.1 + (b.1 - a.1), hidxlt⟩ : Fin m) = b := by
    apply Fin.ext
    simp
    omega
  simpa only [hidx] using hstep (b.1 - a.1) hidxlt

private theorem exists_dense_separated_nodes
    {d N : ℕ} {η : ℝ} (hd : 1 ≤ d)
    (hsize : (4 : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 ≤ η * (N : ℝ))
    (S : Finset ℕ) (hScard : η * (N : ℝ) ≤ (S.card : ℝ)) :
    ∃ t : Fin (d + 1) → ℕ,
      (∀ i, t i ∈ S) ∧
      (∀ i j, i ≠ j →
        η * (N : ℝ) / (2 * ((d + 1 : ℕ) : ℝ)) ≤
          |(t i : ℝ) - (t j : ℝ)|) := by
  classical
  let m : ℕ := S.card
  have hmR : (4 : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by
    exact hsize.trans (by simpa [m] using hScard)
  have hm : 4 * (d + 1) ^ 2 ≤ m := by exact_mod_cast hmR
  have hdpos : 0 < d := by omega
  let h : ℕ := (m - 1) / d
  have hdbound : d + 1 ≤ 4 * (d + 1) ^ 2 := by nlinarith
  have hmD : d ≤ m - 1 := by omega
  have hhpos : 1 ≤ h := by
    dsimp [h]
    rw [Nat.le_div_iff_mul_le hdpos]
    simpa using hmD
  have hfloor : m - 1 < (h + 1) * d := by
    dsimp [h]
    exact (Nat.div_lt_iff_lt_mul hdpos).mp (Nat.lt_succ_self ((m - 1) / d))
  have hcompareR : (((h + 1) * d : ℕ) : ℝ) ≤
      2 * ((d + 1 : ℕ) : ℝ) * (h : ℝ) := by
    push_cast
    have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    have hhR : 1 ≤ (h : ℝ) := by exact_mod_cast hhpos
    have hdh : (d : ℝ) ≤ (d : ℝ) * (h : ℝ) := by
      calc
        (d : ℝ) = (d : ℝ) * 1 := by ring
        _ ≤ (d : ℝ) * (h : ℝ) := mul_le_mul_of_nonneg_left hhR (by positivity)
    nlinarith
  have hcompare : (h + 1) * d ≤ 2 * (d + 1) * h := by
    exact_mod_cast hcompareR
  have hspread : m ≤ 2 * (d + 1) * h := by omega
  have hspreadR : (S.card : ℝ) ≤
      2 * ((d + 1 : ℕ) : ℝ) * (h : ℝ) := by
    exact_mod_cast hspread
  have hrealGap : η * (N : ℝ) / (2 * ((d + 1 : ℕ) : ℝ)) ≤ (h : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * ((d + 1 : ℕ) : ℝ))).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hScard.trans hspreadR
  have hdivTop : d * h ≤ m - 1 := by
    dsimp [h]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (m - 1) d
  have hnodeIdx (i : Fin (d + 1)) : i.1 * h < m := by
    have hi : i.1 ≤ d := Nat.le_of_lt_succ i.2
    have hmul := Nat.mul_le_mul_right h hi
    omega
  let e : Fin m ↪o ℕ := S.orderEmbOfFin (show S.card = m from rfl)
  let nodeIdx (i : Fin (d + 1)) : Fin m := ⟨i.1 * h, hnodeIdx i⟩
  let t : Fin (d + 1) → ℕ := fun i => e (nodeIdx i)
  have hmem (i : Fin (d + 1)) : t i ∈ S := by
    exact Finset.orderEmbOfFin_mem _ _ _
  have hstep (i j : Fin (d + 1)) (hij : i.1 < j.1) :
      t i + h ≤ t j := by
    have hidx : (nodeIdx i).1 + h ≤ (nodeIdx j).1 := by
      dsimp [nodeIdx]
      have hsucc : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hij
      have hmul := Nat.mul_le_mul_right h hsucc
      simpa [Nat.add_mul] using hmul
    have hidxle : (nodeIdx i).1 ≤ (nodeIdx j).1 := by omega
    have hgap := strictMono_fin_nat_gap e e.strictMono (nodeIdx i) (nodeIdx j) hidxle
    have hidx' : h + (nodeIdx i).1 ≤ (nodeIdx j).1 := by omega
    have hgap' : h ≤ (nodeIdx j).1 - (nodeIdx i).1 :=
      Nat.le_sub_of_add_le hidx'
    dsimp [t]
    omega
  refine ⟨t, hmem, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hnat := hstep i j hij'
    have hle : (t i : ℝ) ≤ (t j : ℝ) := by exact_mod_cast (Nat.le_of_lt (by omega))
    have hsub : h ≤ t j - t i := Nat.le_sub_of_add_le (by omega)
    have hdiff : (h : ℝ) ≤ (t j : ℝ) - (t i : ℝ) := by
      have hdiffNat : (h : ℝ) ≤ ((t j - t i : ℕ) : ℝ) := by exact_mod_cast hsub
      rw [Nat.cast_sub (by omega)] at hdiffNat
      exact hdiffNat
    calc
      η * (N : ℝ) / (2 * ((d + 1 : ℕ) : ℝ)) ≤ (h : ℝ) := hrealGap
      _ ≤ (t j : ℝ) - (t i : ℝ) := hdiff
      _ = |(t i : ℝ) - (t j : ℝ)| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        ring
  · have hnat := hstep j i hji'
    have hle : (t j : ℝ) ≤ (t i : ℝ) := by exact_mod_cast (Nat.le_of_lt (by omega))
    have hsub : h ≤ t i - t j := Nat.le_sub_of_add_le (by omega)
    have hdiff : (h : ℝ) ≤ (t i : ℝ) - (t j : ℝ) := by
      have hdiffNat : (h : ℝ) ≤ ((t i - t j : ℕ) : ℝ) := by exact_mod_cast hsub
      rw [Nat.cast_sub (by omega)] at hdiffNat
      exact hdiffNat
    calc
      η * (N : ℝ) / (2 * ((d + 1 : ℕ) : ℝ)) ≤ (h : ℝ) := hrealGap
      _ ≤ (t i : ℝ) - (t j : ℝ) := hdiff
      _ = |(t i : ℝ) - (t j : ℝ)| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hle)]

private theorem prod_X_sub_C_coeff_bound
    {α : Type*} [DecidableEq α] {d j : ℕ} (s : Finset α)
    (hs : s.card = d) (a : α → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (ha : ∀ i ∈ s, |a i| ≤ B) (hj : j ≤ d) :
    |(∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff j|
      ≤ (2 : ℝ) ^ d * B ^ (d - j) := by
  classical
  let k : ℕ := d - j
  have hj' : j ≤ s.card := by simpa [hs] using hj
  have hcoeff :
      (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff j =
        ∑ t ∈ s.powersetCard k,
          ∏ i ∈ t, -a i := by
    simpa [k, hs, sub_eq_add_neg] using
      (Finset.prod_X_add_C_coeff s (fun i => -a i) hj')
  have hsumBound :
      |∑ t ∈ s.powersetCard k,
          ∏ i ∈ t, -a i|
        ≤ ∑ t ∈ s.powersetCard k, B ^ k := by
    calc
      |∑ t ∈ s.powersetCard k,
          ∏ i ∈ t, -a i|
          ≤ ∑ t ∈ s.powersetCard k, |∏ i ∈ t, -a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ s.powersetCard k, B ^ k := by
        apply Finset.sum_le_sum
        intro t ht
        have htk : t.card = k := (Finset.mem_powersetCard.mp ht).2
        calc
          |∏ i ∈ t, -a i| = ∏ i ∈ t, |a i| := by simp [Finset.abs_prod]
          _ ≤ ∏ _i ∈ t, B := by
            apply Finset.prod_le_prod₀
            · intro i hi
              exact abs_nonneg _
            · intro i hi
              exact ha i ((Finset.mem_powersetCard.mp ht).1 hi)
          _ = B ^ k := by simp [htk]
  have hcard : (s.powersetCard k).card ≤ 2 ^ d := by
    rw [Finset.card_powersetCard, hs]
    exact Nat.choose_le_two_pow d k
  have hcardR :
      ((s.powersetCard k).card : ℝ) ≤
        (2 : ℝ) ^ d := by exact_mod_cast hcard
  calc
    |(∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff j|
        = |∑ t ∈ s.powersetCard k, ∏ i ∈ t, -a i| := by rw [hcoeff]
    _ ≤ ∑ t ∈ s.powersetCard k, B ^ k := hsumBound
    _ = ((s.powersetCard k).card : ℝ) * B ^ k := by simp
    _ ≤ (2 : ℝ) ^ d * B ^ k := mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = (2 : ℝ) ^ d * B ^ (d - j) := by simp [k]

/-- A polynomial that is small on a positive-density subset of a long integer
interval has quantitatively bounded coefficients. The length hypothesis is
the one needed to select `d + 1` well-separated interpolation nodes. -/
theorem interpolateDenseSet
    {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N)
    {η E : ℝ} (hη : 0 < η) (_hηle : η ≤ 1)
    (hlen : (4 : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 / η ≤ (N : ℝ))
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N)
    (hScard : η * (N : ℝ) ≤ (S.card : ℝ))
    (V : Polynomial ℝ) (hVdeg : V.natDegree ≤ d)
    (hEval : ∀ n ∈ S, |V.eval (n : ℝ)| ≤ E) (hE : 0 ≤ E) :
    ∀ j ≤ d,
      (N : ℝ) ^ j * |V.coeff j| ≤
        ((d + 1 : ℕ) : ℝ) * (4 * ((d + 1 : ℕ) : ℝ)) ^ d * E / η ^ d := by
  classical
  have hsize :
      (4 : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 ≤ η * (N : ℝ) :=
    by simpa [mul_comm] using (div_le_iff₀ hη).mp hlen
  obtain ⟨t, htmem, htsep⟩ :=
    exists_dense_separated_nodes hd hsize S hScard
  let τ : Fin (d + 1) → ℝ := fun i => (t i : ℝ)
  let g : ℝ := η * (N : ℝ) / (2 * ((d + 1 : ℕ) : ℝ))
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hg : 0 < g := by dsimp [g]; positivity
  have hτsep (i j : Fin (d + 1)) (hij : i ≠ j) :
      g ≤ |τ i - τ j| := by
    simpa [g, τ] using htsep i j hij
  have hτinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have h := hτsep i j hne
    rw [hij, sub_self, abs_zero] at h
    exact (not_le_of_gt hg) h
  have hτinjOn : Set.InjOn τ (Finset.univ : Finset (Fin (d + 1))) := by
    intro i hi j hj hij
    exact hτinj hij
  have hdegLe : V.degree ≤ (d : WithBot ℕ) :=
    Polynomial.degree_le_of_natDegree_le hVdeg
  have hdegLt : V.degree < ((d + 1 : ℕ) : WithBot ℕ) := by
    calc
      V.degree ≤ (d : WithBot ℕ) := hdegLe
      _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self d
  have hVeq : V = Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1)))
      τ (fun i => V.eval (τ i)) := by
    apply Lagrange.eq_interpolate hτinjOn
    simpa using hdegLt
  let den : Fin (d + 1) → ℝ := fun i =>
    ∏ l ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, (τ i - τ l)
  let num : Fin (d + 1) → Polynomial ℝ := fun i =>
    ∏ l ∈ (Finset.univ : Finset (Fin (d + 1))).erase i,
      (Polynomial.X - Polynomial.C (τ l))
  have hVexpand : V = ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))),
      Polynomial.C (V.eval (τ i) / den i) * num i := by
    calc
      V = Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1)))
          τ (fun i => V.eval (τ i)) := hVeq
      _ = ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))),
          Polynomial.C (V.eval (τ i) / den i) * num i := by
        simpa [den, num] using
          (Lagrange.interpolate_eq_sum
            (s := (Finset.univ : Finset (Fin (d + 1)))) (v := τ)
            (r := fun i => V.eval (τ i)))
  intro j hj
  have hcoeff : V.coeff j =
      ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))),
        (V.eval (τ i) / den i) * (num i).coeff j := by
    calc
      V.coeff j =
          (∑ i ∈ (Finset.univ : Finset (Fin (d + 1))),
            Polynomial.C (V.eval (τ i) / den i) * num i).coeff j :=
              congrArg (fun p : Polynomial ℝ => p.coeff j) hVexpand
      _ = ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))),
          (Polynomial.C (V.eval (τ i) / den i) * num i).coeff j :=
            Polynomial.finsetSum_coeff _ _ _
      _ = ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))),
          (V.eval (τ i) / den i) * (num i).coeff j := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Polynomial.coeff_C_mul]
  have hnodeBound (i : Fin (d + 1)) : |τ i| ≤ (N : ℝ) := by
    have hi := Finset.mem_Icc.mp (hS (htmem i))
    have hnonneg : 0 ≤ τ i := by
      change 0 ≤ (t i : ℝ)
      exact Nat.cast_nonneg _
    have hupper : τ i ≤ (N : ℝ) := by
      change (t i : ℝ) ≤ (N : ℝ)
      exact_mod_cast hi.2
    rw [abs_of_nonneg hnonneg]
    exact hupper
  have hnumBound (i : Fin (d + 1)) :
      |(num i).coeff j| ≤ (2 : ℝ) ^ d * (N : ℝ) ^ (d - j) := by
    have hcardErase : ((Finset.univ : Finset (Fin (d + 1))).erase i).card = d := by
      simp
    simpa [num] using
      prod_X_sub_C_coeff_bound ((Finset.univ : Finset (Fin (d + 1))).erase i)
        hcardErase τ (by exact_mod_cast hN) (fun l hl => hnodeBound l) hj
  have hdenLower (i : Fin (d + 1)) : g ^ d ≤ |den i| := by
    have hcardErase : ((Finset.univ : Finset (Fin (d + 1))).erase i).card = d := by
      simp
    calc
      g ^ d = ∏ l ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, g := by
        simp [hcardErase]
      _ ≤ ∏ l ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, |τ i - τ l| := by
        apply Finset.prod_le_prod₀
        · intro l hl
          exact hg.le
        · intro l hl
          exact hτsep i l (by
            intro heq
            exact (Finset.mem_erase.mp hl).1 heq.symm)
      _ = |den i| := by simp [den, Finset.abs_prod]
  have hdenPos (i : Fin (d + 1)) : 0 < |den i| :=
    lt_of_lt_of_le (pow_pos hg d) (hdenLower i)
  have hEvalBound (i : Fin (d + 1)) : |V.eval (τ i)| ≤ E := by
    exact hEval (t i) (htmem i)
  have hterm (i : Fin (d + 1)) :
      |(V.eval (τ i) / den i) * (num i).coeff j| ≤
        E / g ^ d * ((2 : ℝ) ^ d * (N : ℝ) ^ (d - j)) := by
    rw [abs_mul, abs_div]
    have hfrac : |V.eval (τ i)| / |den i| ≤ E / g ^ d :=
      div_le_div₀ hE (hEvalBound i) (pow_pos hg d) (hdenLower i)
    exact mul_le_mul hfrac (hnumBound i) (abs_nonneg _) (by positivity)
  have hsumBound :
      |V.coeff j| ≤ ((d + 1 : ℕ) : ℝ) *
        (E / g ^ d * ((2 : ℝ) ^ d * (N : ℝ) ^ (d - j))) := by
    rw [hcoeff]
    calc
      |∑ i ∈ (Finset.univ : Finset (Fin (d + 1))),
          (V.eval (τ i) / den i) * (num i).coeff j|
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))),
              |(V.eval (τ i) / den i) * (num i).coeff j| :=
                Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin (d + 1))),
            E / g ^ d * ((2 : ℝ) ^ d * (N : ℝ) ^ (d - j)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hterm i
      _ = ((d + 1 : ℕ) : ℝ) *
            (E / g ^ d * ((2 : ℝ) ^ d * (N : ℝ) ^ (d - j))) := by simp
  have hpow : (N : ℝ) ^ j * (N : ℝ) ^ (d - j) = (N : ℝ) ^ d := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  let D : ℝ := ((d + 1 : ℕ) : ℝ)
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by norm_num) hNreal
  have hgpow : g ^ d = η ^ d * (N : ℝ) ^ d / (2 * D) ^ d := by
    dsimp [g, D]
    rw [div_pow, mul_pow]
  have hfracSimpl :
      E / g ^ d * ((2 : ℝ) ^ d * (N : ℝ) ^ d) =
        E * ((2 : ℝ) ^ d * (2 * D) ^ d) / η ^ d := by
    rw [hgpow]
    field_simp [ne_of_gt hη, ne_of_gt hNpos]
  have hconst : (2 : ℝ) ^ d * (2 * D) ^ d = (4 * D) ^ d := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    (N : ℝ) ^ j * |V.coeff j| ≤
        (N : ℝ) ^ j * (((d + 1 : ℕ) : ℝ) *
          (E / g ^ d * ((2 : ℝ) ^ d * (N : ℝ) ^ (d - j)))) :=
      mul_le_mul_of_nonneg_left hsumBound (by positivity)
    _ = D * (E / g ^ d * ((2 : ℝ) ^ d *
          ((N : ℝ) ^ j * (N : ℝ) ^ (d - j)))) := by
      dsimp [D]
      ring
    _ = D * (E / g ^ d * ((2 : ℝ) ^ d * (N : ℝ) ^ d)) := by rw [hpow]
    _ = D * (E * ((2 : ℝ) ^ d * (2 * D) ^ d) / η ^ d) := by rw [hfracSimpl]
    _ = D * (4 * D) ^ d * E / η ^ d := by rw [hconst]; ring
    _ = ((d + 1 : ℕ) : ℝ) * (4 * ((d + 1 : ℕ) : ℝ)) ^ d *
        E / η ^ d := by rfl

end FractionalPrimes.Literature.Polynomial
