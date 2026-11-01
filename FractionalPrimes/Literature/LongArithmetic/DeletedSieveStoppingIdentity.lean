module

public import FractionalPrimes.RosserWeights

/-!
# Subset-restricted Rosser stopping identity

This is the zero-padding adapter used in the source proof of `lal:deleted-sieve`.
It only restricts the finite stopping identity to a chosen subset of the
ambient sieve primes; it does not include the deleted-sieve density estimate.
-/

@[expose] public section

namespace FractionalPrimes.Literature.LongArithmetic

open Classical

/-- Restrict the checked Rosser stopping identity to `S` by setting the test
weight to zero outside `S`. The retained prefixes and stopping prefixes are
those of the original ambient sieve; the displayed filters keep precisely
the terms supported on `S`, and the stopping tail is intersected with `S`.

This is the structural stopping-identity step in the source proof of
`lal:deleted-sieve`; it is not the complete deleted-prime sieve theorem. -/
theorem rosserStoppingIdentity_subset
    (z y : ℝ) (nu : Fin 2) (x : ℕ → ℝ) (S : Finset ℕ)
    (hS : S ⊆ sievePrimesBelow z) :
    ∏ p ∈ S, (1 - x p) =
      (∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
        (-1 : ℝ) ^ U.card * rosserSubsetMonomial x U) +
        (-1 : ℝ) ^ nu.val *
          ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
            rosserSubsetMonomial x P *
              ∏ q ∈ (rosserBelowLastPrimes z P).filter (fun q => q ∈ S),
                (1 - x q) := by
  classical
  let xS : ℕ → ℝ := fun p => if p ∈ S then x p else 0
  let retainedTerm : (ℕ → ℝ) → Finset ℕ → ℝ := fun w U =>
    (-1 : ℝ) ^ U.card * rosserSubsetMonomial w U
  let stoppingTerm : (ℕ → ℝ) → Finset ℕ → ℝ := fun w P =>
    rosserSubsetMonomial w P *
      ∏ q ∈ rosserBelowLastPrimes z P, (1 - w q)
  let restrictedStoppingTerm : Finset ℕ → ℝ := fun P =>
    rosserSubsetMonomial x P *
      ∏ q ∈ (rosserBelowLastPrimes z P).filter (fun q => q ∈ S), (1 - x q)

  have hmonomial_eq {U : Finset ℕ} (hU : U ⊆ S) :
      rosserSubsetMonomial xS U = rosserSubsetMonomial x U := by
    unfold rosserSubsetMonomial
    apply Finset.prod_congr rfl
    intro p hp
    simp [xS, hU hp]

  have hmonomial_zero {U : Finset ℕ} (hU : ¬ U ⊆ S) :
      rosserSubsetMonomial xS U = 0 := by
    obtain ⟨p, hpU, hpS⟩ := Finset.not_subset.mp hU
    unfold rosserSubsetMonomial
    exact Finset.prod_eq_zero hpU (by simp [xS, hpS])

  have htail (P : Finset ℕ) :
      ∏ q ∈ rosserBelowLastPrimes z P, (1 - xS q) =
        ∏ q ∈ (rosserBelowLastPrimes z P).filter (fun q => q ∈ S),
          (1 - x q) := by
    symm
    apply Finset.prod_subset_one_on_sdiff (Finset.filter_subset _ _)
    · intro q hq
      have hqnot : q ∉ S := by
        intro hqS
        have hq' := Finset.mem_sdiff.mp hq
        exact hq'.2 (Finset.mem_filter.mpr ⟨hq'.1, hqS⟩)
      simp [xS, hqnot]
    · intro q hq
      have hqS : q ∈ S := (Finset.mem_filter.mp hq).2
      simp [xS, hqS]

  have hprod :
      ∏ p ∈ sievePrimesBelow z, (1 - xS p) = ∏ p ∈ S, (1 - x p) := by
    symm
    apply Finset.prod_subset_one_on_sdiff hS
    · intro p hp
      have hpnot : p ∉ S := (Finset.mem_sdiff.mp hp).2
      simp [xS, hpnot]
    · intro p hp
      simp [xS, hp]

  have hretained :
      (∑ U ∈ rosserRetainedSubsets z y nu, retainedTerm xS U) =
        ∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
          retainedTerm x U := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (rosserRetainedSubsets z y nu) (fun U => U ⊆ S) (retainedTerm xS)
    have hbad :
        (∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => ¬ U ⊆ S),
          retainedTerm xS U) = 0 := by
      apply Finset.sum_eq_zero
      intro U hU
      have hUnot : ¬ U ⊆ S := (Finset.mem_filter.mp hU).2
      simp [retainedTerm, hmonomial_zero hUnot]
    have hgood :
        (∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
          retainedTerm xS U) =
          ∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
            retainedTerm x U := by
      apply Finset.sum_congr rfl
      intro U hU
      have hUsmall : U ⊆ S := (Finset.mem_filter.mp hU).2
      simp [retainedTerm, hmonomial_eq hUsmall]
    calc
      (∑ U ∈ rosserRetainedSubsets z y nu, retainedTerm xS U) =
          (∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
            retainedTerm xS U) +
            ∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => ¬ U ⊆ S),
              retainedTerm xS U := hsplit.symm
      _ = ∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
            retainedTerm x U := by rw [hbad, add_zero, hgood]

  have hstopping :
      (∑ P ∈ rosserStoppingPrefixes z y nu, stoppingTerm xS P) =
        ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
          restrictedStoppingTerm P := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (rosserStoppingPrefixes z y nu) (fun P => P ⊆ S) (stoppingTerm xS)
    have hbad :
        (∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => ¬ P ⊆ S),
          stoppingTerm xS P) = 0 := by
      apply Finset.sum_eq_zero
      intro P hP
      have hPnot : ¬ P ⊆ S := (Finset.mem_filter.mp hP).2
      simp [stoppingTerm, hmonomial_zero hPnot]
    have hgood :
        (∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
          stoppingTerm xS P) =
          ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
            restrictedStoppingTerm P := by
      apply Finset.sum_congr rfl
      intro P hP
      have hPsmall : P ⊆ S := (Finset.mem_filter.mp hP).2
      simp [stoppingTerm, restrictedStoppingTerm, hmonomial_eq hPsmall, htail]
    calc
      (∑ P ∈ rosserStoppingPrefixes z y nu, stoppingTerm xS P) =
          (∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
            stoppingTerm xS P) +
            ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => ¬ P ⊆ S),
              stoppingTerm xS P := hsplit.symm
      _ = ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
            restrictedStoppingTerm P := by rw [hbad, add_zero, hgood]

  have hidentity := rosserStoppingIdentity z y nu xS
  calc
    ∏ p ∈ S, (1 - x p) = ∏ p ∈ sievePrimesBelow z, (1 - xS p) := hprod.symm
    _ =
        (∑ U ∈ rosserRetainedSubsets z y nu,
          (-1 : ℝ) ^ U.card * rosserSubsetMonomial xS U) +
          (-1 : ℝ) ^ nu.val *
            ∑ P ∈ rosserStoppingPrefixes z y nu,
              rosserSubsetMonomial xS P *
                ∏ q ∈ rosserBelowLastPrimes z P, (1 - xS q) := hidentity
    _ =
        (∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
          (-1 : ℝ) ^ U.card * rosserSubsetMonomial x U) +
          (-1 : ℝ) ^ nu.val *
            ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
              rosserSubsetMonomial x P *
                ∏ q ∈ (rosserBelowLastPrimes z P).filter (fun q => q ∈ S),
                  (1 - x q) := by
      rw [hretained, hstopping]

/-- The density product over the selected primes strictly below `u`, as in
the `V_S(u)` notation of the `lal:deleted-sieve` proof. -/
noncomputable def deletedPrimeSieveDensityProduct
    (S : Finset ℕ) (u : ℝ) : ℝ :=
  ∏ p ∈ (S.filter (fun p : ℕ => (p : ℝ) < u)), (1 - 1 / (p : ℝ))

/-- Deleting primes can only decrease the normalized density ratio across a
strict interval: the omitted prime factors contribute inverse factors at
least one. This is the first density comparison in the approved
`lal:deleted-sieve` proof. -/
theorem deletedPrimeSieveDensityRatio_le_sieveDensityProduct
    {u z : ℝ} {S : Finset ℕ}
    (hS : S ⊆ sievePrimesBelow z) (_hu : 1 < u) (huz : u < z) :
    deletedPrimeSieveDensityProduct S u /
        deletedPrimeSieveDensityProduct S z ≤
      sieveDensityProduct u / sieveDensityProduct z := by
  classical
  let f : ℕ → ℝ := fun p => 1 - 1 / (p : ℝ)
  let U : Finset ℕ := S.filter (fun p => (p : ℝ) < u)
  let A : Finset ℕ := S.filter (fun p => u ≤ (p : ℝ))
  let I : Finset ℕ := primeReciprocalSet u z

  have hUsub : U ⊆ S := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1

  have hAdiff : S \ U = A := by
    ext p
    simp only [Finset.mem_sdiff, U, A, Finset.mem_filter]
    constructor
    · rintro ⟨hpS, hnot⟩
      refine ⟨hpS, ?_⟩
      by_contra hpu
      exact hnot ⟨hpS, lt_of_not_ge hpu⟩
    · rintro ⟨hpS, hpu⟩
      refine ⟨hpS, ?_⟩
      rintro ⟨_, hlt⟩
      exact (not_lt_of_ge hpu) hlt

  have hfilterSz : S.filter (fun p : ℕ => (p : ℝ) < z) = S := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro hp
      exact hp.1
    · intro hp
      have hpz : (p : ℝ) < z :=
        ((sievePrimesBelow_iff z p).mp (hS hp)).2
      exact ⟨hp, hpz⟩

  have hAsubI : A ⊆ I := by
    intro p hp
    simp only [A, I, primeReciprocalSet, Finset.mem_filter] at hp ⊢
    exact ⟨hS hp.1, hp.2⟩

  have hfactor_ge_one : ∀ p ∈ I, 1 ≤ (f p)⁻¹ := by
    intro p hp
    simp only [I, primeReciprocalSet, Finset.mem_filter] at hp
    have hpprime : p.Prime :=
      ((sievePrimesBelow_iff z p).mp hp.1).1
    have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hpRone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.one_lt
    have hrecip : 1 / (p : ℝ) < 1 := by
      rw [div_lt_iff₀ hpRpos]
      norm_num at hpRone ⊢
      linarith
    have hfpos : 0 < f p := by dsimp [f]; linarith
    have hfle : f p ≤ 1 := by
      dsimp [f]
      have hrecip_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith
    exact (one_le_inv₀ hfpos).2 hfle

  have hVSuEq : deletedPrimeSieveDensityProduct S u = ∏ p ∈ U, f p := rfl
  have hVSzEq : deletedPrimeSieveDensityProduct S z = ∏ p ∈ S, f p := by
    unfold deletedPrimeSieveDensityProduct
    rw [hfilterSz]

  have hfactor_pos_S : ∀ p ∈ S, 0 < f p := by
    intro p hpS
    have hpprime : p.Prime :=
      ((sievePrimesBelow_iff z p).mp (hS hpS)).1
    have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hpRone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.one_lt
    have hrecip : 1 / (p : ℝ) < 1 := by
      rw [div_lt_iff₀ hpRpos]
      norm_num at hpRone ⊢
      linarith
    dsimp [f]
    linarith

  have hVSuPos : 0 < deletedPrimeSieveDensityProduct S u := by
    rw [hVSuEq]
    apply Finset.prod_pos
    intro p hp
    exact hfactor_pos_S p (Finset.mem_filter.mp hp).1

  have hVSzPos : 0 < deletedPrimeSieveDensityProduct S z := by
    rw [hVSzEq]
    apply Finset.prod_pos
    intro p hp
    exact hfactor_pos_S p hp

  have hAprodPos : 0 < ∏ p ∈ A, f p := by
    apply Finset.prod_pos
    intro p hp
    have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
    exact hfactor_pos_S p hpS

  have hdecompS :
      (∏ p ∈ A, f p) * deletedPrimeSieveDensityProduct S u =
        deletedPrimeSieveDensityProduct S z := by
    calc
      (∏ p ∈ A, f p) * deletedPrimeSieveDensityProduct S u =
          (∏ p ∈ S \ U, f p) * (∏ p ∈ U, f p) := by
            rw [← hAdiff, hVSuEq]
      _ = ∏ p ∈ S, f p :=
        Finset.prod_sdiff (s₁ := U) (s₂ := S) (f := f) hUsub
      _ = deletedPrimeSieveDensityProduct S z := by rw [hVSzEq]

  have hratioS :
      deletedPrimeSieveDensityProduct S u /
          deletedPrimeSieveDensityProduct S z =
        ∏ p ∈ A, (f p)⁻¹ := by
    calc
      deletedPrimeSieveDensityProduct S u /
          deletedPrimeSieveDensityProduct S z = (∏ p ∈ A, f p)⁻¹ := by
            rw [← hdecompS]
            field_simp [ne_of_gt hVSuPos, ne_of_gt hAprodPos]
            <;> ring
      _ = ∏ p ∈ A, (f p)⁻¹ := by rw [← Finset.prod_inv_distrib]

  have hfullsubset : sievePrimesBelow u ⊆ sievePrimesBelow z := by
    intro p hp
    rw [sievePrimesBelow_iff] at hp ⊢
    exact ⟨hp.1, lt_trans hp.2 huz⟩

  have hfullDiff : sievePrimesBelow z \ sievePrimesBelow u = I := by
    ext p
    dsimp only [I]
    rw [Finset.mem_sdiff, sievePrimesBelow_iff, sievePrimesBelow_iff,
      primeReciprocalSet, Finset.mem_filter, sievePrimesBelow_iff]
    constructor
    · rintro ⟨⟨hp, hpz⟩, hnot⟩
      refine ⟨⟨hp, hpz⟩, ?_⟩
      by_contra hpu
      exact hnot ⟨hp, lt_of_not_ge hpu⟩
    · rintro ⟨⟨hp, hpz⟩, hpu⟩
      refine ⟨⟨hp, hpz⟩, ?_⟩
      rintro ⟨_, hlt⟩
      exact (not_lt_of_ge hpu) hlt

  have hdecompFull :
      (∏ p ∈ sievePrimesBelow z \ sievePrimesBelow u, f p) *
          sieveDensityProduct u = sieveDensityProduct z := by
    simpa [sieveDensityProduct, f] using
      (Finset.prod_sdiff (s₁ := sievePrimesBelow u)
        (s₂ := sievePrimesBelow z) (f := f) hfullsubset)

  have hprodDiffFull :
      (∏ p ∈ sievePrimesBelow z \ sievePrimesBelow u, f p) =
        sieveDensityProduct z / sieveDensityProduct u := by
    calc
      _ = (∏ p ∈ sievePrimesBelow z \ sievePrimesBelow u, f p) *
            sieveDensityProduct u / sieveDensityProduct u := by
              field_simp [ne_of_gt (sieveDensityProduct_pos (z := u))]
      _ = _ := by rw [hdecompFull]

  have hprodI : (∏ p ∈ I, f p) =
      sieveDensityProduct z / sieveDensityProduct u := by
    rw [← hfullDiff]
    exact hprodDiffFull

  have hratioFull : sieveDensityProduct u / sieveDensityProduct z =
      ∏ p ∈ I, (f p)⁻¹ := by
    calc
      sieveDensityProduct u / sieveDensityProduct z =
          (sieveDensityProduct z / sieveDensityProduct u)⁻¹ := by
            field_simp [ne_of_gt (sieveDensityProduct_pos (z := u)),
              ne_of_gt (sieveDensityProduct_pos (z := z))]
      _ = (∏ p ∈ I, f p)⁻¹ := by rw [← hprodI]
      _ = ∏ p ∈ I, (f p)⁻¹ := by rw [← Finset.prod_inv_distrib]

  rw [hratioS, hratioFull]
  apply Finset.prod_le_prod_of_subset_of_one_le₀ hAsubI
  · intro p hp
    exact le_trans (by norm_num) (hfactor_ge_one p (hAsubI hp))
  · intro p hp hnotA
    exact hfactor_ge_one p hp

/-- The coefficient obtained from the original Rosser coefficient by keeping
only prime support contained in the selected set `S`. -/
noncomputable def deletedPrimeSieveCoefficient
    (z y : ℝ) (nu : Fin 2) (S : Finset ℕ) (d : ℕ) : ℝ :=
  if rosserPrimeSupport z d ⊆ S then rosserXi z y nu d else 0

/-- The lower coefficient for the deleted-prime sieve, including the
source-prescribed zero lower weight on the short scale. -/
noncomputable def deletedPrimeSieveLowerCoefficient
    (z y : ℝ) (S : Finset ℕ) (d : ℕ) : ℝ :=
  if Real.log y / Real.log z < 2 then 0
  else deletedPrimeSieveCoefficient z y (0 : Fin 2) S d

/-- The upper coefficient for the deleted-prime sieve. -/
noncomputable def deletedPrimeSieveUpperCoefficient
    (z y : ℝ) (S : Finset ℕ) (d : ℕ) : ℝ :=
  deletedPrimeSieveCoefficient z y (1 : Fin 2) S d

/-- Products of retained prime subsets supported in `S`. -/
noncomputable def deletedPrimeSieveRetainedProductValues
    (z y : ℝ) (nu : Fin 2) (S : Finset ℕ) : Finset ℕ :=
  ((rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S)).image
    (fun U => U.prod id)

theorem deletedPrimeSieveCoefficient_abs_le_one
    (z y : ℝ) (nu : Fin 2) (S : Finset ℕ) (d : ℕ) :
    |deletedPrimeSieveCoefficient z y nu S d| ≤ 1 := by
  unfold deletedPrimeSieveCoefficient
  split_ifs
  · exact rosserXi_abs_le_one z y nu d
  · norm_num

theorem deletedPrimeSieveLowerCoefficient_bounds
    (z y : ℝ) (S : Finset ℕ) (d : ℕ) :
    -1 ≤ deletedPrimeSieveLowerCoefficient z y S d ∧
      deletedPrimeSieveLowerCoefficient z y S d ≤ 1 := by
  unfold deletedPrimeSieveLowerCoefficient
  split_ifs
  · norm_num
  · have h := deletedPrimeSieveCoefficient_abs_le_one z y (0 : Fin 2) S d
    exact abs_le.mp h

theorem deletedPrimeSieveUpperCoefficient_bounds
    (z y : ℝ) (S : Finset ℕ) (d : ℕ) :
    -1 ≤ deletedPrimeSieveUpperCoefficient z y S d ∧
      deletedPrimeSieveUpperCoefficient z y S d ≤ 1 := by
  have h := deletedPrimeSieveCoefficient_abs_le_one z y (1 : Fin 2) S d
  simpa [deletedPrimeSieveUpperCoefficient] using (abs_le.mp h)

theorem deletedPrimeSieveCoefficient_eq_zero_of_not_mem_productValues
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ} {d : ℕ}
    (hnot : d ∉ deletedPrimeSieveRetainedProductValues z y nu S) :
    deletedPrimeSieveCoefficient z y nu S d = 0 := by
  classical
  by_cases hsub : rosserPrimeSupport z d ⊆ S
  · simp only [deletedPrimeSieveCoefficient, if_pos hsub]
    by_contra hxi
    have hspec := rosserXi_spec hxi
    have hretained : rosserPrimeSupport z d ∈ rosserRetainedSubsets z y nu :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hspec.1.1, hspec.1⟩
    have hfiltered : rosserPrimeSupport z d ∈
        (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S) :=
      Finset.mem_filter.mpr ⟨hretained, hsub⟩
    exact hnot (Finset.mem_image.mpr ⟨rosserPrimeSupport z d, hfiltered, hspec.2⟩)
  · simp [deletedPrimeSieveCoefficient, hsub]

theorem deletedPrimeSieveCoefficient_ne_zero_mem_productValues
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ} {d : ℕ}
    (hcoeff : deletedPrimeSieveCoefficient z y nu S d ≠ 0) :
    d ∈ deletedPrimeSieveRetainedProductValues z y nu S := by
  classical
  unfold deletedPrimeSieveCoefficient at hcoeff
  split_ifs at hcoeff with hsub
  · have hspec := rosserXi_spec hcoeff
    have hretained : rosserPrimeSupport z d ∈ rosserRetainedSubsets z y nu :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hspec.1.1, hspec.1⟩
    have hfiltered : rosserPrimeSupport z d ∈
        (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S) :=
      Finset.mem_filter.mpr ⟨hretained, hsub⟩
    exact Finset.mem_image.mpr ⟨rosserPrimeSupport z d, hfiltered, hspec.2⟩
  · simp at hcoeff

theorem deletedPrimeSieveProduct_squarefree_of_primes
    {z : ℝ} {S : Finset ℕ} (hS : S ⊆ sievePrimesBelow z) :
    Squarefree (S.prod id) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) ?_
  · change IsRelPrime p q
    have hpz := hS hp
    have hqz := hS hq
    unfold sievePrimesBelow at hpz hqz
    have hpprime : p.Prime := (Finset.mem_filter.mp hpz).2.1
    have hqprime : q.Prime := (Finset.mem_filter.mp hqz).2.1
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes hpprime hqprime).mpr hpq)
  · intro p hp
    have hpz := hS hp
    unfold sievePrimesBelow at hpz
    exact ((Finset.mem_filter.mp hpz).2.1).squarefree

theorem deletedPrimeSieveCoefficient_support
    {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y) {nu : Fin 2}
    {S : Finset ℕ} (hS : S ⊆ sievePrimesBelow z) {d : ℕ}
    (hcoeff : deletedPrimeSieveCoefficient z y nu S d ≠ 0) :
    0 < d ∧ (d : ℝ) < y ∧ Squarefree d ∧ d ∣ S.prod id := by
  have hvalue := deletedPrimeSieveCoefficient_ne_zero_mem_productValues hcoeff
  rcases Finset.mem_image.mp hvalue with ⟨U, hU, hprod⟩
  have hUsmall := (Finset.mem_filter.mp hU).2
  have hUmem := Finset.mem_filter.mp (Finset.mem_filter.mp hU).1
  have hUbase : U ⊆ sievePrimesBelow z := Finset.mem_powerset.mp hUmem.1
  have hret : rosserRetained z y nu U := hUmem.2
  have hdpos : 0 < d := by
    have hUprodpos : 0 < U.prod id := Finset.prod_pos fun p hp =>
      (show p.Prime from by
        have hpz := hUbase hp
        unfold sievePrimesBelow at hpz
        exact (Finset.mem_filter.mp hpz).2.1).pos
    rw [← hprod]
    exact hUprodpos
  have hdlt : (d : ℝ) < y := by
    rw [← hprod]
    exact rosserRetained_product_lt hz hzy hret
  have hdsq : Squarefree d := by
    rw [← hprod]
    exact deletedPrimeSieveProduct_squarefree_of_primes hUbase
  have hdvd : d ∣ S.prod id := by
    rw [← hprod]
    exact Finset.prod_dvd_prod_of_subset U S id hUsmall
  exact ⟨hdpos, hdlt, hdsq, hdvd⟩

theorem deletedPrimeSieveLowerCoefficient_support
    {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y) {S : Finset ℕ}
    (hS : S ⊆ sievePrimesBelow z) {d : ℕ}
    (hcoeff : deletedPrimeSieveLowerCoefficient z y S d ≠ 0) :
    0 < d ∧ (d : ℝ) < y ∧ Squarefree d ∧ d ∣ S.prod id := by
  unfold deletedPrimeSieveLowerCoefficient at hcoeff
  split_ifs at hcoeff with hshort
  · simp at hcoeff
  · exact deletedPrimeSieveCoefficient_support hz hzy hS hcoeff

theorem deletedPrimeSieveUpperCoefficient_support
    {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y) {S : Finset ℕ}
    (hS : S ⊆ sievePrimesBelow z) {d : ℕ}
    (hcoeff : deletedPrimeSieveUpperCoefficient z y S d ≠ 0) :
    0 < d ∧ (d : ℝ) < y ∧ Squarefree d ∧ d ∣ S.prod id := by
  exact deletedPrimeSieveCoefficient_support hz hzy hS
    (by simpa [deletedPrimeSieveUpperCoefficient] using hcoeff)

theorem deletedPrimeSieveRetainedProductValues_subset_range
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y) :
    deletedPrimeSieveRetainedProductValues z y nu S ⊆
      Finset.range (⌊y⌋₊ + 1) := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨U, hU, rfl⟩
  have hUret : U ∈ rosserRetainedSubsets z y nu :=
    (Finset.mem_filter.mp hU).1
  exact rosserRetainedProductValues_subset_range hz hzy
    (Finset.mem_image.mpr ⟨U, hUret, rfl⟩)

theorem deletedPrimeSieveRetainedSubsets_product_injOn
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ} :
    Set.InjOn (fun U : Finset ℕ => U.prod id)
      (((rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S)) :
        Set (Finset ℕ)) := by
  intro U hU V hV hprod
  apply rosserRetainedProductValues_injOn
  · exact (Finset.mem_filter.mp hU).1
  · exact (Finset.mem_filter.mp hV).1
  · exact hprod

/-- The deleted-prime reciprocal divisor sum is the retained-prefix sum
restricted to subsets of `S`. The range keeps the exact real-floor cutoff;
the zero coefficient outside the retained product set handles `d = 0`. -/
theorem deletedPrimeSieveReciprocalSum_eq_retained
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y) :
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
      deletedPrimeSieveCoefficient z y nu S d / (d : ℝ)) =
      ∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
        (-1 : ℝ) ^ U.card *
          rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) U := by
  classical
  let family := (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S)
  let values := deletedPrimeSieveRetainedProductValues z y nu S
  let f : ℕ → ℝ := fun d => deletedPrimeSieveCoefficient z y nu S d / (d : ℝ)
  have hvaluesSubset : values ⊆ Finset.range (⌊y⌋₊ + 1) :=
    deletedPrimeSieveRetainedProductValues_subset_range hz hzy
  have hsumSubset :
      (∑ d ∈ values, f d) =
        ∑ d ∈ Finset.range (⌊y⌋₊ + 1), f d := by
    apply Finset.sum_subset hvaluesSubset
    intro d hd hnot
    have hzero : deletedPrimeSieveCoefficient z y nu S d = 0 :=
      deletedPrimeSieveCoefficient_eq_zero_of_not_mem_productValues hnot
    simp [f, hzero]
  have hsumImage :
      (∑ U ∈ family, f (U.prod id)) = ∑ d ∈ values, f d := by
    simpa [family, values, deletedPrimeSieveRetainedProductValues] using
      (Finset.sum_image deletedPrimeSieveRetainedSubsets_product_injOn).symm
  have hterm : ∀ U ∈ family,
      f (U.prod id) =
        (-1 : ℝ) ^ U.card *
          rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) U := by
    intro U hU
    have hUmem := Finset.mem_filter.mp hU
    have hret : rosserRetained z y nu U :=
      (Finset.mem_filter.mp hUmem.1).2
    have hbase : U ⊆ sievePrimesBelow z :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hUmem.1).1
    have hsupport : rosserPrimeSupport z (U.prod id) ⊆ S := by
      rw [rosserPrimeSupport_eq_of_product
        (z := z) (S := U) (d := U.prod id) hbase rfl]
      exact hUmem.2
    have hcoef : deletedPrimeSieveCoefficient z y nu S (U.prod id) =
        (-1 : ℝ) ^ U.card := by
      unfold deletedPrimeSieveCoefficient
      rw [if_pos hsupport]
      exact rosserXi_eq_sign_of_retained_product hret rfl
    simp only [f, hcoef, div_eq_mul_inv]
    rw [rosserSubsetMonomial_inv_eq]
    simp only [Nat.cast_prod, id_eq]
  calc
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        deletedPrimeSieveCoefficient z y nu S d / (d : ℝ)) =
        ∑ d ∈ values, f d := by
          symm
          exact hsumSubset
    _ = ∑ U ∈ family, f (U.prod id) := hsumImage.symm
    _ = ∑ U ∈ family,
          (-1 : ℝ) ^ U.card *
            rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) U := by
          apply Finset.sum_congr rfl
          intro U hU
          exact hterm U hU
    _ = ∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
          (-1 : ℝ) ^ U.card *
            rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) U := by rfl

/-- The reciprocal-weight stopping remainder for the sieve restricted to `S`.
The last-prime factor uses the strict cutoff in `deletedPrimeSieveDensityProduct`.
-/
noncomputable def deletedPrimeSieveStoppingDensityRemainder
    (z y : ℝ) (nu : Fin 2) (S : Finset ℕ) : ℝ :=
  ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
    (((P.prod id : ℕ) : ℝ)⁻¹) *
      deletedPrimeSieveDensityProduct S
        (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)

/-- The subset-restricted reciprocal stopping identity: the full subset density
is its retained reciprocal divisor sum plus the signed stopping remainder. -/
theorem deletedPrimeSieveDensity_stopping_identity
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hS : S ⊆ sievePrimesBelow z) :
    deletedPrimeSieveDensityProduct S z =
      (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        deletedPrimeSieveCoefficient z y nu S d / (d : ℝ)) +
        (-1 : ℝ) ^ nu.val *
          deletedPrimeSieveStoppingDensityRemainder z y nu S := by
  classical
  have hfilterSz : S.filter (fun p : ℕ => (p : ℝ) < z) = S := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro hp
      exact hp.1
    · intro hp
      exact ⟨hp, ((sievePrimesBelow_iff z p).mp (hS hp)).2⟩
  have hbaseDensity : deletedPrimeSieveDensityProduct S z =
      ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
    unfold deletedPrimeSieveDensityProduct
    rw [hfilterSz]
    simp only [one_div]
  have hret := deletedPrimeSieveReciprocalSum_eq_retained
    (nu := nu) (S := S) hz hzy
  have hid := rosserStoppingIdentity_subset z y nu
    (fun p => (p : ℝ)⁻¹) S hS
  have hrem :
      (∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
        rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) P *
          ∏ q ∈ (rosserBelowLastPrimes z P).filter (fun q => q ∈ S),
            (1 - (q : ℝ)⁻¹)) =
        deletedPrimeSieveStoppingDensityRemainder z y nu S := by
    unfold deletedPrimeSieveStoppingDensityRemainder
    apply Finset.sum_congr rfl
    intro P hP
    have hstopmem := Finset.mem_filter.mp (Finset.mem_filter.mp hP).1
    have hstop : rosserStoppingPrefix z y nu P := hstopmem.2
    have hbelow := rosserBelowLastPrimes_eq_sievePrimesBelow_last hstop
    let last : ℝ :=
      (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)
    have htailSet :
        (rosserBelowLastPrimes z P).filter (fun q => q ∈ S) =
          S.filter (fun q : ℕ => (q : ℝ) < last) := by
      rw [hbelow]
      ext q
      simp only [Finset.mem_filter, sievePrimesBelow_iff]
      constructor
      · rintro ⟨⟨_, hqlast⟩, hqS⟩
        exact ⟨hqS, by simpa [last] using hqlast⟩
      · rintro ⟨hqS, hqlast⟩
        have hqprime : q.Prime :=
          ((sievePrimesBelow_iff z q).mp (hS hqS)).1
        exact ⟨⟨hqprime, by simpa [last] using hqlast⟩, hqS⟩
    have hmon : rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) P =
        (((P.prod id : ℕ) : ℝ)⁻¹) := by
      simpa only [id_eq] using rosserSubsetMonomial_inv_eq P
    rw [hmon, htailSet]
    simp only [deletedPrimeSieveDensityProduct, last, one_div]
  calc
    deletedPrimeSieveDensityProduct S z =
        ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := hbaseDensity
    _ =
        (∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
          (-1 : ℝ) ^ U.card *
            rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) U) +
          (-1 : ℝ) ^ nu.val *
            ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
              rosserSubsetMonomial (fun p => (p : ℝ)⁻¹) P *
                ∏ q ∈ (rosserBelowLastPrimes z P).filter (fun q => q ∈ S),
                  (1 - (q : ℝ)⁻¹) := hid
    _ =
        (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
          deletedPrimeSieveCoefficient z y nu S d / (d : ℝ)) +
          (-1 : ℝ) ^ nu.val *
            deletedPrimeSieveStoppingDensityRemainder z y nu S := by
      rw [← hret, hrem]

/-- After normalization by the selected density, the restricted stopping
remainder is bounded by the corresponding full-prime remainder. -/
theorem deletedPrimeSieveStoppingDensityRemainder_div_le
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hS : S ⊆ sievePrimesBelow z) :
    deletedPrimeSieveStoppingDensityRemainder z y nu S /
        deletedPrimeSieveDensityProduct S z ≤
      rosserStoppingDensityRemainder z y nu / sieveDensityProduct z := by
  classical
  have hVSpos : 0 < deletedPrimeSieveDensityProduct S z := by
    unfold deletedPrimeSieveDensityProduct
    apply Finset.prod_pos
    intro p hp
    have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime :=
      ((sievePrimesBelow_iff z p).mp (hS hpS)).1
    have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hpRone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.one_lt
    have hrecip : 1 / (p : ℝ) < 1 := by
      rw [div_lt_iff₀ hpRpos]
      norm_num at hpRone ⊢
      linarith
    linarith
  let fullTerm : Finset ℕ → ℝ := fun P =>
    (((P.prod (fun p : ℕ => p) : ℕ) : ℝ)⁻¹) *
      (sieveDensityProduct
        (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) /
        sieveDensityProduct z)
  let selectedTerm : Finset ℕ → ℝ := fun P =>
    (((P.prod id : ℕ) : ℝ)⁻¹) *
      (deletedPrimeSieveDensityProduct S
        (rosserPrefixLast (rosserPrimeList P) P.card : ℝ) /
        deletedPrimeSieveDensityProduct S z)
  have hselectedDiv :
      deletedPrimeSieveStoppingDensityRemainder z y nu S /
          deletedPrimeSieveDensityProduct S z =
        ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
          selectedTerm P := by
    unfold deletedPrimeSieveStoppingDensityRemainder
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    dsimp [selectedTerm]
    ring
  have hfullDiv :
      rosserStoppingDensityRemainder z y nu / sieveDensityProduct z =
        ∑ P ∈ rosserStoppingPrefixes z y nu, fullTerm P := by
    unfold rosserStoppingDensityRemainder
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    dsimp [fullTerm]
    ring
  have hterm : ∀ P ∈ (rosserStoppingPrefixes z y nu).filter
      (fun P => P ⊆ S), selectedTerm P ≤ fullTerm P := by
    intro P hP
    have hstopmem := Finset.mem_filter.mp (Finset.mem_filter.mp hP).1
    have hstop : rosserStoppingPrefix z y nu P := hstopmem.2
    have hlastmem := rosserStopping_last_mem_sieve hstop
    have hlastInfo :=
      (sievePrimesBelow_iff z (rosserPrefixLast (rosserPrimeList P) P.card)).mp
        hlastmem
    let last : ℝ :=
      (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)
    have hlast_gt : 1 < last := by
      dsimp [last]
      exact_mod_cast hlastInfo.1.one_lt
    have hlast_lt : last < z := by
      simpa [last] using hlastInfo.2
    have hratio :
        deletedPrimeSieveDensityProduct S last /
            deletedPrimeSieveDensityProduct S z ≤
          sieveDensityProduct last / sieveDensityProduct z :=
      deletedPrimeSieveDensityRatio_le_sieveDensityProduct hS hlast_gt hlast_lt
    have hweight : 0 ≤ (((P.prod id : ℕ) : ℝ)⁻¹) := by positivity
    simpa [selectedTerm, fullTerm, last] using
      (mul_le_mul_of_nonneg_left hratio hweight)
  have hnonneg : ∀ P ∈ rosserStoppingPrefixes z y nu,
      P ∉ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S) →
        0 ≤ fullTerm P := by
    intro P hP hnot
    dsimp [fullTerm]
    apply mul_nonneg
    · positivity
    · exact div_nonneg
        (sieveDensityProduct_pos.le)
        (sieveDensityProduct_pos.le)
  have hselectedLeFull :
      (∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
        selectedTerm P) ≤
        ∑ P ∈ rosserStoppingPrefixes z y nu, fullTerm P := by
    calc
      (∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
          selectedTerm P) ≤
        ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
          fullTerm P := by
            apply Finset.sum_le_sum
            intro P hP
            exact hterm P hP
      _ ≤ ∑ P ∈ rosserStoppingPrefixes z y nu, fullTerm P :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) hnonneg
  calc
    deletedPrimeSieveStoppingDensityRemainder z y nu S /
        deletedPrimeSieveDensityProduct S z =
      ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
        selectedTerm P := hselectedDiv
    _ ≤ ∑ P ∈ rosserStoppingPrefixes z y nu, fullTerm P := hselectedLeFull
    _ = rosserStoppingDensityRemainder z y nu / sieveDensityProduct z :=
      hfullDiv.symm

/-- The lower and upper deleted-prime reciprocal coefficient sums have the
same density error constant `sieveD` as the full-prime sieve. The lower
coefficient is zero on the source's short range `1 ≤ s < 2`. -/
theorem deletedPrimeSieveDensityError
    {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y)
    {S : Finset ℕ} (hS : S ⊆ sievePrimesBelow z) :
    |(∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        deletedPrimeSieveLowerCoefficient z y S d / (d : ℝ)) -
        deletedPrimeSieveDensityProduct S z| ≤
      sieveD * deletedPrimeSieveDensityProduct S z *
        Real.exp (-(Real.log y / Real.log z)) ∧
    |(∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        deletedPrimeSieveUpperCoefficient z y S d / (d : ℝ)) -
        deletedPrimeSieveDensityProduct S z| ≤
      sieveD * deletedPrimeSieveDensityProduct S z *
        Real.exp (-(Real.log y / Real.log z)) := by
  classical
  let s : ℝ := Real.log y / Real.log z
  have hs : s = Real.log y / Real.log z := rfl
  have hsone : 1 ≤ s := by
    rw [hs]
    exact rosserLogScale_ge_one hz hzy
  have hD0 : sieveD₀ ≤ sieveD := le_max_left _ _
  have hDexp : Real.exp 2 ≤ sieveD := le_max_right _ _
  have hVposAt (u : ℝ) : 0 < deletedPrimeSieveDensityProduct S u := by
    unfold deletedPrimeSieveDensityProduct
    apply Finset.prod_pos
    intro p hp
    have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime :=
      ((sievePrimesBelow_iff z p).mp (hS hpS)).1
    have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hpRone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.one_lt
    have hrecip : 1 / (p : ℝ) < 1 := by
      rw [div_lt_iff₀ hpRpos]
      norm_num at hpRone ⊢
      linarith
    linarith
  let densitySum : Fin 2 → ℝ := fun m =>
    ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
      deletedPrimeSieveCoefficient z y m S d / (d : ℝ)
  have hrawError {m : Fin 2}
      (hscale : if m.val = 0 then 2 ≤ Real.log y / Real.log z
        else 1 ≤ Real.log y / Real.log z) :
      |densitySum m - deletedPrimeSieveDensityProduct S z| ≤
        sieveD * deletedPrimeSieveDensityProduct S z *
          Real.exp (-(Real.log y / Real.log z)) := by
    have hremNonneg :
        0 ≤ deletedPrimeSieveStoppingDensityRemainder z y m S := by
      unfold deletedPrimeSieveStoppingDensityRemainder
      apply Finset.sum_nonneg
      intro P hP
      apply mul_nonneg
      · positivity
      · exact (hVposAt
          (rosserPrefixLast (rosserPrimeList P) P.card : ℝ)).le
    have hid : deletedPrimeSieveDensityProduct S z =
        densitySum m + (-1 : ℝ) ^ m.val *
          deletedPrimeSieveStoppingDensityRemainder z y m S := by
      simpa [densitySum] using
        deletedPrimeSieveDensity_stopping_identity
          (nu := m) (S := S) hz hzy hS
    have htail := rosserStoppingDensityRemainder_tail_bound
      (nu := m) hz hzy hscale hs
    have hdom := deletedPrimeSieveStoppingDensityRemainder_div_le
      (nu := m) (S := S) hz hzy hS
    have hnorm :
        deletedPrimeSieveStoppingDensityRemainder z y m S /
            deletedPrimeSieveDensityProduct S z ≤
          sieveD₀ * Real.exp (-s) := le_trans hdom htail
    have hremBound0 :
        deletedPrimeSieveStoppingDensityRemainder z y m S ≤
          sieveD₀ * Real.exp (-s) * deletedPrimeSieveDensityProduct S z :=
      (div_le_iff₀ (hVposAt z)).mp hnorm
    have hremBound :
        deletedPrimeSieveStoppingDensityRemainder z y m S ≤
          sieveD * deletedPrimeSieveDensityProduct S z * Real.exp (-s) := by
      calc
        _ ≤ sieveD₀ * Real.exp (-s) * deletedPrimeSieveDensityProduct S z :=
          hremBound0
        _ = sieveD₀ * deletedPrimeSieveDensityProduct S z * Real.exp (-s) := by
          ring
        _ ≤ sieveD * deletedPrimeSieveDensityProduct S z * Real.exp (-s) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hD0 (hVposAt z).le
          · exact (Real.exp_pos _).le
    have hnu : m.val = 0 ∨ m.val = 1 := by omega
    have habs :
        |densitySum m - deletedPrimeSieveDensityProduct S z| =
          deletedPrimeSieveStoppingDensityRemainder z y m S := by
      rcases hnu with hzero | hone
      · have hid' : deletedPrimeSieveDensityProduct S z =
            densitySum m + deletedPrimeSieveStoppingDensityRemainder z y m S := by
          simpa [hzero] using hid
        have hdiff : densitySum m - deletedPrimeSieveDensityProduct S z =
            -deletedPrimeSieveStoppingDensityRemainder z y m S := by
          linarith
        rw [hdiff, abs_neg, abs_of_nonneg hremNonneg]
      · have hid' : deletedPrimeSieveDensityProduct S z =
            densitySum m - deletedPrimeSieveStoppingDensityRemainder z y m S := by
          simpa [hone, sub_eq_add_neg] using hid
        have hdiff : densitySum m - deletedPrimeSieveDensityProduct S z =
            deletedPrimeSieveStoppingDensityRemainder z y m S := by
          linarith
        rw [hdiff, abs_of_nonneg hremNonneg]
    rw [habs]
    calc
      deletedPrimeSieveStoppingDensityRemainder z y m S ≤
          sieveD * deletedPrimeSieveDensityProduct S z * Real.exp (-s) :=
        hremBound
      _ = sieveD * deletedPrimeSieveDensityProduct S z *
          Real.exp (-(Real.log y / Real.log z)) := by rw [hs]
  have hscale1 : if (1 : Fin 2).val = 0 then
      2 ≤ Real.log y / Real.log z else
      1 ≤ Real.log y / Real.log z := by
    norm_num
    exact hsone
  have hupper := hrawError (m := (1 : Fin 2)) hscale1
  have hshort : s < 2 ∨ 2 ≤ s := by
    rcases lt_or_ge s 2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  constructor
  · rcases hshort with hshort | hlong
    · have hshort' : Real.log y / Real.log z < 2 := by simpa [hs] using hshort
      have hzero :
          (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
            deletedPrimeSieveLowerCoefficient z y S d / (d : ℝ)) = 0 := by
        simp [deletedPrimeSieveLowerCoefficient, hshort']
      rw [hzero, zero_sub, abs_neg, abs_of_pos (hVposAt z)]
      have he : 1 ≤ Real.exp 2 * Real.exp (-s) := by
        rw [← Real.exp_add]
        exact (Real.one_le_exp_iff).2 (by linarith)
      have hprod : 1 ≤ sieveD * Real.exp (-s) := by
        calc
          1 ≤ Real.exp 2 * Real.exp (-s) := he
          _ ≤ sieveD * Real.exp (-s) :=
            mul_le_mul_of_nonneg_right hDexp (Real.exp_pos _).le
      calc
        deletedPrimeSieveDensityProduct S z =
            1 * deletedPrimeSieveDensityProduct S z := by ring
        _ ≤ (sieveD * Real.exp (-s)) * deletedPrimeSieveDensityProduct S z :=
          mul_le_mul_of_nonneg_right hprod (hVposAt z).le
        _ = sieveD * deletedPrimeSieveDensityProduct S z * Real.exp (-s) := by
          ring
        _ = sieveD * deletedPrimeSieveDensityProduct S z *
            Real.exp (-(Real.log y / Real.log z)) := by rw [hs]
    · have hnotshort : ¬ Real.log y / Real.log z < 2 := by
        rw [← hs]
        exact not_lt_of_ge hlong
      have hscale0 : if (0 : Fin 2).val = 0 then
          2 ≤ Real.log y / Real.log z else
          1 ≤ Real.log y / Real.log z := by
        norm_num
        simpa [hs] using hlong
      have hlower := hrawError (m := (0 : Fin 2)) hscale0
      simpa [densitySum, deletedPrimeSieveLowerCoefficient, hnotshort] using hlower
  · simpa [densitySum, deletedPrimeSieveUpperCoefficient] using hupper

/-- The retained part of the subset stopping identity, expressed as a finite
sum over the corresponding supported divisor coefficients. -/
theorem deletedPrimeSieveRetainedSum_eq_divisorRangeSum
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y) (n : ℕ) :
    (∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
      (-1 : ℝ) ^ U.card *
        rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) U) =
      ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        if d ∣ n then deletedPrimeSieveCoefficient z y nu S d else 0 := by
  classical
  let family := (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S)
  let values := deletedPrimeSieveRetainedProductValues z y nu S
  let f : ℕ → ℝ := fun d => if d ∣ n then deletedPrimeSieveCoefficient z y nu S d else 0
  have hterm : ∀ U ∈ family,
      (-1 : ℝ) ^ U.card *
        rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) U =
          f (U.prod id) := by
    intro U hU
    have hUmem := Finset.mem_filter.mp hU
    have hret : rosserRetained z y nu U :=
      (Finset.mem_filter.mp hUmem.1).2
    have hbase : U ⊆ sievePrimesBelow z :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hUmem.1).1
    have hprodValue : (∏ p ∈ U, p) = U.prod id := rfl
    have hsupport : rosserPrimeSupport z (U.prod id) ⊆ S := by
      rw [rosserPrimeSupport_eq_of_product
        (z := z) (S := U) (d := U.prod id) hbase rfl]
      exact hUmem.2
    have hcoef : deletedPrimeSieveCoefficient z y nu S (U.prod id) =
        (-1 : ℝ) ^ U.card := by
      unfold deletedPrimeSieveCoefficient
      rw [if_pos hsupport]
      exact rosserXi_eq_sign_of_retained_product hret rfl
    have hcoef' : deletedPrimeSieveCoefficient z y nu S (∏ p ∈ U, p) =
        (-1 : ℝ) ^ U.card := by
      rw [hprodValue]
      exact hcoef
    rw [rosserSubsetMonomial_divisibility_indicator hbase]
    by_cases hd : (∏ p ∈ U, p) ∣ n
    · have hd' : U.prod id ∣ n := by rw [← hprodValue]; exact hd
      simp [f, hd, hd', hcoef, hcoef']
    · have hd' : ¬ U.prod id ∣ n := by
        intro h
        exact hd (by rw [hprodValue]; exact h)
      simp [f, hd, hd']
  have hsumImage :
      (∑ U ∈ family,
        (-1 : ℝ) ^ U.card *
          rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) U) =
        ∑ d ∈ values, f d := by
    calc
      _ = ∑ U ∈ family, f (U.prod id) := by
        apply Finset.sum_congr rfl
        intro U hU
        exact hterm U hU
      _ = ∑ d ∈ values, f d :=
        (Finset.sum_image deletedPrimeSieveRetainedSubsets_product_injOn).symm
  have hsumRange :
      (∑ d ∈ values, f d) =
        ∑ d ∈ Finset.range (⌊y⌋₊ + 1), f d := by
    apply Finset.sum_subset
      (deletedPrimeSieveRetainedProductValues_subset_range hz hzy)
    intro d hd hnot
    by_cases hdiv : d ∣ n
    · simp [f, hdiv,
        deletedPrimeSieveCoefficient_eq_zero_of_not_mem_productValues hnot]
    · simp [f, hdiv]
  simpa [family, values, f] using hsumImage.trans hsumRange

theorem deletedPrimeSieveFiniteDivisorSum_eq_rangeSum
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ} (n : ℕ) :
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1),
      if d ∣ n then deletedPrimeSieveCoefficient z y nu S d else 0) =
      ∑ d ∈ rosserPositiveDivisorsBelow y n,
        deletedPrimeSieveCoefficient z y nu S d := by
  rw [rosserPositiveDivisorsBelow, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hzero : d = 0
  · subst d
    simp [deletedPrimeSieveCoefficient, rosserXi_zero]
  · have hpos : 0 < d := Nat.pos_of_ne_zero hzero
    by_cases hdiv : d ∣ n <;> simp [hpos, hdiv]

theorem deletedPrimeSieveRetainedSum_eq_divisorSum
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y) (n : ℕ) :
    (∑ U ∈ (rosserRetainedSubsets z y nu).filter (fun U => U ⊆ S),
      (-1 : ℝ) ^ U.card *
        rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) U) =
      ∑ d ∈ rosserPositiveDivisorsBelow y n,
        deletedPrimeSieveCoefficient z y nu S d := by
  calc
    _ = ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
          if d ∣ n then deletedPrimeSieveCoefficient z y nu S d else 0 :=
      deletedPrimeSieveRetainedSum_eq_divisorRangeSum hz hzy n
    _ = ∑ d ∈ rosserPositiveDivisorsBelow y n,
          deletedPrimeSieveCoefficient z y nu S d :=
      deletedPrimeSieveFiniteDivisorSum_eq_rangeSum n

/-- The nonnegative stopping remainder for the sieve restricted to `S`. -/
noncomputable def deletedPrimeSieveStoppingRemainder
    (z y : ℝ) (nu : Fin 2) (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ P ∈ (rosserStoppingPrefixes z y nu).filter (fun P => P ⊆ S),
    rosserSubsetMonomial (fun p => if p ∣ n then (1 : ℝ) else 0) P *
      ∏ q ∈ (rosserBelowLastPrimes z P).filter (fun q => q ∈ S),
        (1 - (if q ∣ n then (1 : ℝ) else 0))

theorem deletedPrimeSieveStoppingRemainder_nonneg
    {z y : ℝ} {nu : Fin 2} {S : Finset ℕ} (hS : S ⊆ sievePrimesBelow z)
    (n : ℕ) : 0 ≤ deletedPrimeSieveStoppingRemainder z y nu S n := by
  classical
  unfold deletedPrimeSieveStoppingRemainder
  apply Finset.sum_nonneg
  intro P hP
  have hstopmem := Finset.mem_filter.mp (Finset.mem_filter.mp hP).1
  have hstop : rosserStoppingPrefix z y nu P := hstopmem.2
  have hPbase : P ⊆ sievePrimesBelow z := Finset.mem_powerset.mp hstopmem.1
  have hmon : 0 ≤ rosserSubsetMonomial
      (fun p => if p ∣ n then (1 : ℝ) else 0) P := by
    rw [rosserSubsetMonomial_divisibility_indicator hPbase]
    split_ifs <;> norm_num
  have htail : 0 ≤ ∏ q ∈ (rosserBelowLastPrimes z P).filter (fun q => q ∈ S),
      (1 - (if q ∣ n then (1 : ℝ) else 0)) := by
    apply Finset.prod_nonneg
    intro q hq
    by_cases hdiv : q ∣ n <;> simp [hdiv]
  exact mul_nonneg hmon htail

theorem deletedPrimeSieveProduct_divisibility_indicator
    {z : ℝ} {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ sievePrimesBelow z) :
    ∏ p ∈ S, (1 - (if p ∣ n then (1 : ℝ) else 0)) =
      if Nat.Coprime n (S.prod id) then 1 else 0 := by
  classical
  have hfactor :
      (∏ p ∈ S, (1 - (if p ∣ n then (1 : ℝ) else 0))) =
        ∏ p ∈ S, (if p ∣ n then (0 : ℝ) else 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hdiv : p ∣ n <;> simp [hdiv]
  have hprod : ∀ T : Finset ℕ,
      (∏ p ∈ T, (if p ∣ n then (0 : ℝ) else 1)) =
        if ∀ p ∈ T, ¬ p ∣ n then 1 else 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
        by_cases hdiv : p ∣ n <;> simp [Finset.prod_insert, hp, hdiv, ih]
  have hcop : Nat.Coprime n (S.prod id) ↔ ∀ p ∈ S, ¬ p ∣ n := by
    rw [Nat.coprime_prod_right_iff]
    constructor
    · intro h p hp hpd
      have hpz := hS hp
      unfold sievePrimesBelow at hpz
      have hpprime : p.Prime := (Finset.mem_filter.mp hpz).2.1
      exact (hpprime.coprime_iff_not_dvd).mp
        (Nat.coprime_comm.mp (h p hp)) hpd
    · intro h p hp
      have hpz := hS hp
      unfold sievePrimesBelow at hpz
      have hpprime : p.Prime := (Finset.mem_filter.mp hpz).2.1
      exact Nat.coprime_comm.mp
        ((hpprime.coprime_iff_not_dvd).2 (h p hp))
  have hprodValue : (∏ p ∈ S, p) = S.prod id := rfl
  have hcopNested : Nat.Coprime n (∏ p ∈ S, p) ↔ ∀ p ∈ S, ¬ p ∣ n := by
    rw [hprodValue]
    exact hcop
  rw [hfactor, hprod S]
  by_cases hall : ∀ p ∈ S, ¬ p ∣ n
  · have hcop' : Nat.Coprime n (∏ p ∈ S, p) := hcopNested.mpr hall
    rw [if_pos hall, ← hprodValue, if_pos hcop']
  · have hnotcop : ¬ Nat.Coprime n (∏ p ∈ S, p) := fun hc => hall (hcopNested.mp hc)
    rw [if_neg hall, ← hprodValue, if_neg hnotcop]

theorem intGcd_deletedPrimeProduct_eq_natAbs
    (n : ℤ) (S : Finset ℕ) :
    (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) =
      if Nat.Coprime n.natAbs (S.prod id) then 1 else 0 := by
  have hcop : Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 ↔
      Nat.Coprime n.natAbs (S.prod id) := by
    rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime]
    rw [Int.natAbs_natCast]
  by_cases hg : Int.gcd n ((S.prod id : ℕ) : ℤ) = 1
  · rw [if_pos hg, if_pos (hcop.mp hg)]
  · have hnat : ¬ Nat.Coprime n.natAbs (S.prod id) := fun h => hg (hcop.mpr h)
    rw [if_neg hg, if_neg hnat]

/-- The exact pointwise lower and upper divisor-sum sandwich for a selected
subset of the primes below `z`. -/
theorem deletedPrimeSievePointwise
    {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y) {S : Finset ℕ}
    (hS : S ⊆ sievePrimesBelow z) (n : ℤ) :
    (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
      deletedPrimeSieveLowerCoefficient z y S d) ≤
        (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) ∧
      (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) ≤
        (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          deletedPrimeSieveUpperCoefficient z y S d) := by
  classical
  let m := n.natAbs
  let x : ℕ → ℝ := fun p => if p ∣ m then (1 : ℝ) else 0
  have hproduct :
      ∏ p ∈ S, (1 - x p) =
        if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0 := by
    calc
      ∏ p ∈ S, (1 - x p) =
          if Nat.Coprime m (S.prod id) then (1 : ℝ) else 0 := by
        simpa [x, m] using
          (deletedPrimeSieveProduct_divisibility_indicator (n := m) hS)
      _ = if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0 :=
        (intGcd_deletedPrimeProduct_eq_natAbs n S).symm

  have hrem (nu : Fin 2) :
      0 ≤ deletedPrimeSieveStoppingRemainder z y nu S m :=
    deletedPrimeSieveStoppingRemainder_nonneg hS m

  have hupperRetained :
      (∑ U ∈ (rosserRetainedSubsets z y (1 : Fin 2)).filter (fun U => U ⊆ S),
        (-1 : ℝ) ^ U.card * rosserSubsetMonomial x U) =
        ∑ d ∈ rosserPositiveDivisorsBelow y m,
          deletedPrimeSieveUpperCoefficient z y S d := by
    simpa [x, deletedPrimeSieveUpperCoefficient] using
      (deletedPrimeSieveRetainedSum_eq_divisorSum
        (z := z) (y := y) (nu := (1 : Fin 2)) (S := S) hz hzy m)

  have hupperIdentity :
      (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) =
        (∑ d ∈ rosserPositiveDivisorsBelow y m,
          deletedPrimeSieveUpperCoefficient z y S d) -
          deletedPrimeSieveStoppingRemainder z y (1 : Fin 2) S m := by
    calc
      (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) =
          ∏ p ∈ S, (1 - x p) := hproduct.symm
      _ =
          (∑ U ∈ (rosserRetainedSubsets z y (1 : Fin 2)).filter
            (fun U => U ⊆ S),
            (-1 : ℝ) ^ U.card * rosserSubsetMonomial x U) +
            (-1 : ℝ) ^ (1 : Fin 2).val *
              deletedPrimeSieveStoppingRemainder z y (1 : Fin 2) S m := by
        simpa [x, deletedPrimeSieveStoppingRemainder] using
          (rosserStoppingIdentity_subset z y (1 : Fin 2) x S hS)
      _ =
          (∑ d ∈ rosserPositiveDivisorsBelow y m,
            deletedPrimeSieveUpperCoefficient z y S d) -
            deletedPrimeSieveStoppingRemainder z y (1 : Fin 2) S m := by
        rw [hupperRetained]
        norm_num [Fin.val] <;> ring

  by_cases hshort : Real.log y / Real.log z < 2
  · have hlowerZero :
        (∑ d ∈ rosserPositiveDivisorsBelow y m,
          deletedPrimeSieveLowerCoefficient z y S d) = 0 := by
      simp [deletedPrimeSieveLowerCoefficient, hshort]
    constructor
    · rw [hlowerZero]
      split_ifs <;> norm_num
    · rw [hupperIdentity]
      linarith [hrem (1 : Fin 2)]
  · have hlowerRetained :
        (∑ U ∈ (rosserRetainedSubsets z y (0 : Fin 2)).filter
          (fun U => U ⊆ S),
          (-1 : ℝ) ^ U.card * rosserSubsetMonomial x U) =
          ∑ d ∈ rosserPositiveDivisorsBelow y m,
            deletedPrimeSieveLowerCoefficient z y S d := by
      simpa [x, deletedPrimeSieveLowerCoefficient, hshort] using
        (deletedPrimeSieveRetainedSum_eq_divisorSum
          (z := z) (y := y) (nu := (0 : Fin 2)) (S := S) hz hzy m)
    have hlowerIdentity :
        (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) =
          (∑ d ∈ rosserPositiveDivisorsBelow y m,
            deletedPrimeSieveLowerCoefficient z y S d) +
            deletedPrimeSieveStoppingRemainder z y (0 : Fin 2) S m := by
      calc
        (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) =
            ∏ p ∈ S, (1 - x p) := hproduct.symm
        _ =
            (∑ U ∈ (rosserRetainedSubsets z y (0 : Fin 2)).filter
              (fun U => U ⊆ S),
              (-1 : ℝ) ^ U.card * rosserSubsetMonomial x U) +
              (-1 : ℝ) ^ (0 : Fin 2).val *
                deletedPrimeSieveStoppingRemainder z y (0 : Fin 2) S m := by
          simpa [x, deletedPrimeSieveStoppingRemainder] using
            (rosserStoppingIdentity_subset z y (0 : Fin 2) x S hS)
        _ =
            (∑ d ∈ rosserPositiveDivisorsBelow y m,
              deletedPrimeSieveLowerCoefficient z y S d) +
              deletedPrimeSieveStoppingRemainder z y (0 : Fin 2) S m := by
          rw [hlowerRetained]
          norm_num
    constructor
    · linarith [hlowerIdentity, hrem (0 : Fin 2)]
    · rw [hupperIdentity]
      linarith [hrem (1 : Fin 2)]

/-- Blueprint aggregate for `lal:deleted-sieve`: the selected lower and upper
coefficients have the exact coefficient range, squarefree-divisor support,
all-integer pointwise sandwich, and density errors with the unchanged constant
`sieveD`. -/
theorem deletedPrimeSieve
    {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y)
    {S : Finset ℕ} (hS : S ⊆ sievePrimesBelow z) :
    (∀ d : ℕ,
      -1 ≤ deletedPrimeSieveLowerCoefficient z y S d ∧
        deletedPrimeSieveLowerCoefficient z y S d ≤ 1 ∧
        -1 ≤ deletedPrimeSieveUpperCoefficient z y S d ∧
        deletedPrimeSieveUpperCoefficient z y S d ≤ 1) ∧
    (∀ d : ℕ,
      (deletedPrimeSieveLowerCoefficient z y S d ≠ 0 →
        0 < d ∧ (d : ℝ) < y ∧ Squarefree d ∧ d ∣ S.prod id) ∧
      (deletedPrimeSieveUpperCoefficient z y S d ≠ 0 →
        0 < d ∧ (d : ℝ) < y ∧ Squarefree d ∧ d ∣ S.prod id)) ∧
    (∀ n : ℤ,
      (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        deletedPrimeSieveLowerCoefficient z y S d) ≤
          (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) ∧
        (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) ≤
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            deletedPrimeSieveUpperCoefficient z y S d)) ∧
    (|(∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        deletedPrimeSieveLowerCoefficient z y S d / (d : ℝ)) -
        deletedPrimeSieveDensityProduct S z| ≤
        sieveD * deletedPrimeSieveDensityProduct S z *
          Real.exp (-(Real.log y / Real.log z)) ∧
      |(∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        deletedPrimeSieveUpperCoefficient z y S d / (d : ℝ)) -
        deletedPrimeSieveDensityProduct S z| ≤
        sieveD * deletedPrimeSieveDensityProduct S z *
          Real.exp (-(Real.log y / Real.log z))) := by
  refine ⟨?_, ?_, ?_, deletedPrimeSieveDensityError hz hzy hS⟩
  · intro d
    have hlower := deletedPrimeSieveLowerCoefficient_bounds z y S d
    have hupper := deletedPrimeSieveUpperCoefficient_bounds z y S d
    exact ⟨hlower.1, hlower.2, hupper.1, hupper.2⟩
  · intro d
    exact ⟨deletedPrimeSieveLowerCoefficient_support hz hzy hS,
      deletedPrimeSieveUpperCoefficient_support hz hzy hS⟩
  · intro n
    exact deletedPrimeSievePointwise hz hzy hS n

end FractionalPrimes.Literature.LongArithmetic
