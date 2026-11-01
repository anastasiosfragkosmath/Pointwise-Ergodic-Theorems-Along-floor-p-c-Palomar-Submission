module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylInductionReindex

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- A large sum with a factor constant on residue classes has a residue fiber
whose unfactored sum retains the average lower bound. -/
private theorem finiteResidueFiber_hasLargeNorm
    {r : ℕ} {A : ℝ} (hr : 0 < r)
    (J : Finset ℤ) (f g : ℤ → ℂ)
    (hgNorm : ∀ n, ‖g n‖ = 1)
    (hgPeriodic : ∀ {n b : ℤ}, n ≡ b [ZMOD (r : ℤ)] → g n = g b)
    (hlarge : A ≤ ‖∑ n ∈ J, f n * g n‖) :
    ∃ b ∈ Finset.Icc (1 : ℤ) (r : ℤ),
      A / (r : ℝ) ≤
        ‖∑ n ∈ J.filter (fun n => n ≡ b [ZMOD (r : ℤ)]), f n‖ := by
  classical
  have hrZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
  let fibers : ℕ → Finset ℤ := fun x =>
    J.filter (fun n => n ≡ (x : ℤ) [ZMOD (r : ℤ)])
  let F : ℤ → ℂ := fun n => f n * g n
  let mass : ℕ → ℝ := fun x => ‖∑ n ∈ fibers x, f n‖
  have huniq (x y : ℕ) (hx : x < r) (hy : y < r)
      (hxy : (x : ℤ) ≡ (y : ℤ) [ZMOD (r : ℤ)]) : x = y := by
    have hxZ : (x : ℤ) < (r : ℤ) := by exact_mod_cast hx
    have hyZ : (y : ℤ) < (r : ℤ) := by exact_mod_cast hy
    have hrem : (x : ℤ) % (r : ℤ) = (y : ℤ) % (r : ℤ) := by
      change (x : ℤ) % (r : ℤ) = (y : ℤ) % (r : ℤ) at hxy
      exact hxy
    have hxrem : (x : ℤ) % (r : ℤ) = (x : ℤ) :=
      Int.emod_eq_of_lt (Nat.cast_nonneg _) hxZ
    have hyrem : (y : ℤ) % (r : ℤ) = (y : ℤ) :=
      Int.emod_eq_of_lt (Nat.cast_nonneg _) hyZ
    rw [hxrem, hyrem] at hrem
    exact_mod_cast hrem
  have hcover : (Finset.range r).biUnion fibers = J := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_biUnion.mp hn with ⟨x, hx, hxn⟩
      exact (Finset.mem_filter.mp hxn).1
    · intro hn
      let x : ℕ := (n % (r : ℤ)).toNat
      have hrem0 : 0 ≤ n % (r : ℤ) := Int.emod_nonneg _ hrZ.ne'
      have hremLt : n % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos _ hrZ
      have hcast : (x : ℤ) = n % (r : ℤ) := Int.toNat_of_nonneg hrem0
      have hxLtZ : (x : ℤ) < (r : ℤ) := by rw [hcast]; exact hremLt
      have hxLt : x < r := by exact_mod_cast hxLtZ
      have hmod : n ≡ (x : ℤ) [ZMOD (r : ℤ)] := by
        change n % (r : ℤ) = (x : ℤ) % (r : ℤ)
        rw [hcast]
        simp
      exact Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_range.mpr hxLt,
          Finset.mem_filter.mpr ⟨hn, hmod⟩⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range r)) fibers := by
    intro x hx y hy hxy
    have hx' : x ∈ Finset.range r := by simpa using hx
    have hy' : y ∈ Finset.range r := by simpa using hy
    apply Finset.disjoint_left.mpr
    intro n hnx hny
    have hnxMod := (Finset.mem_filter.mp hnx).2
    have hnyMod := (Finset.mem_filter.mp hny).2
    apply hxy
    exact huniq x y (Finset.mem_range.mp hx') (Finset.mem_range.mp hy')
      (hnxMod.symm.trans hnyMod)
  have hpartition :
      (∑ n ∈ J, F n) =
        ∑ x ∈ Finset.range r, ∑ n ∈ fibers x, F n := by
    calc
      (∑ n ∈ J, F n) =
          ∑ n ∈ (Finset.range r).biUnion fibers, F n := by rw [hcover]
      _ = ∑ x ∈ Finset.range r, ∑ n ∈ fibers x, F n :=
        Finset.sum_biUnion hdisj
  have hclass (x : ℕ) :
      ‖∑ n ∈ fibers x, F n‖ = mass x := by
    have hsum :
        (∑ n ∈ fibers x, F n) =
          (∑ n ∈ fibers x, f n) * g (x : ℤ) := by
      dsimp [F]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      change f n * g n = f n * g (x : ℤ)
      rw [hgPeriodic (Finset.mem_filter.mp hn).2]
    rw [hsum, norm_mul, hgNorm, mul_one]
  have hlargeF : A ≤ ‖∑ n ∈ J, F n‖ := by
    simpa [F] using hlarge
  have hmass : A ≤ ∑ x ∈ Finset.range r, mass x := by
    calc
      A ≤ ‖∑ n ∈ J, F n‖ := hlargeF
      _ = ‖∑ x ∈ Finset.range r, ∑ n ∈ fibers x, F n‖ := by rw [hpartition]
      _ ≤ ∑ x ∈ Finset.range r, ‖∑ n ∈ fibers x, F n‖ := norm_sum_le _ _
      _ = ∑ x ∈ Finset.range r, mass x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hclass x
  have hrange : (Finset.range r).Nonempty :=
    ⟨0, Finset.mem_range.mpr hr⟩
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  let M : ℝ := (Finset.range r).sup' hrange mass
  have hmassLe (x : ℕ) (hx : x ∈ Finset.range r) : mass x ≤ M := by
    dsimp [M]
    exact Finset.le_sup' (s := Finset.range r) (f := mass) hx
  have hsumM :
      (∑ x ∈ Finset.range r, mass x) ≤ (r : ℝ) * M := by
    calc
      (∑ x ∈ Finset.range r, mass x) ≤
          ∑ x ∈ Finset.range r, M :=
        Finset.sum_le_sum fun x hx => hmassLe x hx
      _ = (r : ℝ) * M := by simp [Finset.card_range]
  have hAM : A / (r : ℝ) ≤ M := by
    apply (div_le_iff₀ hrR).2
    calc
      A ≤ (r : ℝ) * M := hmass.trans hsumM
      _ = M * (r : ℝ) := by ring
  obtain ⟨x, hx, hMx⟩ := Finset.exists_mem_eq_sup' hrange mass
  have hxLt : x < r := Finset.mem_range.mp hx
  let b : ℤ := if x = 0 then (r : ℤ) else (x : ℤ)
  have hb : b ∈ Finset.Icc (1 : ℤ) (r : ℤ) := by
    rw [Finset.mem_Icc]
    by_cases hx0 : x = 0
    · have hbval : b = (r : ℤ) := by simp [b, hx0]
      rw [hbval]
      exact ⟨by exact_mod_cast hr, le_rfl⟩
    · have hxlo : 1 ≤ x := by omega
      have hxhi : x ≤ r := Nat.le_of_lt hxLt
      have hbval : b = (x : ℤ) := by simp [b, hx0]
      rw [hbval]
      exact ⟨by exact_mod_cast hxlo, by exact_mod_cast hxhi⟩
  have hxb : (x : ℤ) ≡ b [ZMOD (r : ℤ)] := by
    by_cases hx0 : x = 0
    · have hbval : b = (r : ℤ) := by simp [b, hx0]
      rw [hbval]
      subst x
      change (0 : ℤ) % (r : ℤ) = (r : ℤ) % (r : ℤ)
      simp
    · have hbval : b = (x : ℤ) := by simp [b, hx0]
      rw [hbval]
  have hfilters : fibers x =
      J.filter (fun n => n ≡ b [ZMOD (r : ℤ)]) := by
    ext n
    simp only [fibers, Finset.mem_filter]
    constructor
    · rintro ⟨hn, hmod⟩
      exact ⟨hn, hmod.trans hxb⟩
    · rintro ⟨hn, hmod⟩
      exact ⟨hn, hmod.trans hxb.symm⟩
  have hchosen : A / (r : ℝ) ≤ mass x := by
    rw [← hMx]
    exact hAM
  refine ⟨b, hb, ?_⟩
  simpa [mass, hfilters] using hchosen

/-- The rational top-frequency is constant on an integer residue class. -/
private theorem rationalTopPhase_eq_of_modEq
    {r d : ℕ} {a n b : ℤ} (hr : 0 < r)
    (hmod : n ≡ b [ZMOD (r : ℤ)]) :
    unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d) =
      unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (b : ℝ) ^ d) := by
  have hrRpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hpow : n ^ d ≡ b ^ d [ZMOD (r : ℤ)] := Int.ModEq.pow d hmod
  have hmul : a * n ^ d ≡ a * b ^ d [ZMOD (r : ℤ)] := hpow.mul_left a
  obtain ⟨k, hk⟩ := hmul.dvd
  have hreal :
      (a : ℝ) * (b : ℝ) ^ d - (a : ℝ) * (n : ℝ) ^ d =
        (r : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  have harg :
      ((a : ℝ) / (r : ℝ)) * (b : ℝ) ^ d =
        ((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d + (k : ℝ) := by
    field_simp [ne_of_gt hrRpos]
    nlinarith [hreal]
  calc
    unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d) =
        unitFrequencyPhase
          ((((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d) + (k : ℝ)) := by
            rw [unitFrequencyPhase_add, unitFrequencyPhase_int]
            simp
    _ = unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (b : ℝ) ^ d) := by
          rw [harg]

/-- From a large Abel-prefix sum with rational top coefficient, obtain the
source's large low-degree residue sum and the ceiling scale for `N'`. The
denominator bound and long-branch cutoff give `4r≤N`, so `N'` is positive and
the exact ceiling bounds needed by the induction-density transfer hold. -/
theorem scalarWeyl_selectedResidueAndCeilingPrerequisites
    {N r N' d : ℕ} {δ V R : ℝ}
    (hr : 1 ≤ r) (hrR : (r : ℝ) ≤ R)
    (hRlong : 4 * R ≤ (N : ℝ)) (hV : 1 ≤ V)
    (hN'ceil : N' = N ⌈/⌉ r)
    (lo hi : ℤ)
    (hJsubset : Finset.Ico lo hi ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    (a : ℤ) (f : ℤ → ℂ)
    (hlarge : δ * (N : ℝ) / V ≤
      ‖∑ n ∈ Finset.Ico lo hi,
        f n * unitFrequencyPhase
          (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d)‖) :
    ∃ b ∈ Finset.Icc (1 : ℤ) (r : ℤ),
      δ * (N : ℝ) / ((r : ℝ) * V) ≤
        ‖∑ n ∈ (Finset.Ico lo hi).filter
          (fun n => n ≡ b [ZMOD (r : ℤ)]), f n‖ ∧
      1 ≤ N' ∧
      (N : ℝ) / (r : ℝ) ≤ (N' : ℝ) ∧
      (N' : ℝ) ≤ 2 * (N : ℝ) / (r : ℝ) := by
  classical
  have hrpos : 0 < r := by omega
  have hrRpos : 0 < (r : ℝ) := by exact_mod_cast hrpos
  have h4rReal : 4 * (r : ℝ) ≤ (N : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hrR (by norm_num : 0 ≤ (4 : ℝ))).trans hRlong
  have h4r : 4 * r ≤ N := by exact_mod_cast h4rReal
  have hceil := scalarWeyl_ceilDiv_bounds hrpos h4r
  have hceilLower : (N : ℝ) / (r : ℝ) ≤ (N' : ℝ) := by
    simpa [hN'ceil] using hceil.1
  have hceilUpper : (N' : ℝ) ≤ 2 * (N : ℝ) / (r : ℝ) := by
    simpa [hN'ceil] using hceil.2
  have h4quot : (4 : ℝ) ≤ (N : ℝ) / (r : ℝ) := by
    apply (le_div_iff₀ hrRpos).2
    exact h4rReal
  have hN'one : 1 ≤ N' := by
    have hfour : (4 : ℝ) ≤ (N' : ℝ) := h4quot.trans hceilLower
    exact_mod_cast (show (1 : ℝ) ≤ (N' : ℝ) by linarith)
  let g : ℤ → ℂ := fun n =>
    unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d)
  have hgNorm : ∀ n, ‖g n‖ = 1 := by
    intro n
    simp [g, norm_unitFrequencyPhase]
  have hgPeriodic : ∀ {n b : ℤ}, n ≡ b [ZMOD (r : ℤ)] → g n = g b := by
    intro n b hmod
    exact rationalTopPhase_eq_of_modEq hrpos hmod
  have hlarge' : δ * (N : ℝ) / V ≤
      ‖∑ n ∈ Finset.Ico lo hi, f n * g n‖ := by
    simpa [g] using hlarge
  obtain ⟨b, hb, hselected⟩ :=
    finiteResidueFiber_hasLargeNorm hrpos (Finset.Ico lo hi) f g
      hgNorm hgPeriodic hlarge'
  have hratio :
      δ * (N : ℝ) / ((r : ℝ) * V) =
        (δ * (N : ℝ) / V) / (r : ℝ) := by
    field_simp [ne_of_gt hrRpos, ne_of_gt (by linarith : 0 < V)]
    <;> ring
  refine ⟨b, hb, ?_, hN'one, hceilLower, hceilUpper⟩
  rw [hratio]
  exact hselected

end FractionalPrimes.Literature.Polynomial
