module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownFreeFactorPeriodicInterval
public import FractionalPrimes.Literature.DirichletAdapter.SmoothFactorMass
public import FractionalPrimes.Literature.DirichletAdapter.SmoothSmallGroupFiniteAssembly
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownSmallGroupData
public import FractionalPrimes.Literature.DirichletAdapter.SmoothGroupSubsetReindex
public import FractionalPrimes.Literature.Twisted.ShiftedConvolutionFactorExtraction
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
import Mathlib.Tactic

/-! Finite outer-factor summation of the checked fixed-product theta/log
free-factor estimate.  The source absolute mass of the remaining factors is
kept as the exact `5^19 * sqrt(P/L)` input. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The exact source mass of the tuple of all factors except the selected
one.  It follows from the `5 * sqrt(N_i)` mass of each complementary factor
and the source bound of at most twenty factors. -/
theorem smoothHeathBrownOuterTupleMass_le
    {k : ℕ} (hk : k ≤ 20) (selected : Fin k)
    (N : Fin k → ℝ) (S : Fin k → Finset ℕ) (a : Fin k → ℕ → ℂ)
    (hN : ∀ i, 0 < N i)
    (hMass : ∀ i, i ≠ selected →
      (∑ n ∈ S i, ‖a i n‖) ≤ 5 * Real.sqrt (N i)) :
    ∑ tuple ∈ Fintype.piFinset
        (fun i : Fin k => if i = selected then ({1} : Finset ℕ) else S i),
      ‖∏ i : Fin k,
        (if i = selected then 1 else a i (tuple i))‖ ≤
      5 ^ 19 * Real.sqrt ((∏ i : Fin k, N i) / N selected) := by
  classical
  let Sfull : Fin k → Finset ℕ := fun i =>
    if i = selected then {1} else S i
  let afull : Fin k → ℕ → ℂ := fun i n =>
    if i = selected then 1 else a i n
  let mass : Fin k → ℝ := fun i => ∑ n ∈ Sfull i, ‖afull i n‖
  have hmassNonneg : ∀ i, 0 ≤ mass i := by
    intro i
    dsimp [mass]
    apply Finset.sum_nonneg
    intro n hn
    exact norm_nonneg _
  have hmassBound : ∀ i, i ≠ selected → mass i ≤ 5 * Real.sqrt (N i) := by
    intro i hi
    simpa [mass, Sfull, afull, hi] using hMass i hi
  have hmassSelected : mass selected = 1 := by
    simp [mass, Sfull, afull]
  have htuple :
      (∑ tuple ∈ Fintype.piFinset
          Sfull,
        ‖∏ i : Fin k, afull i (tuple i)‖) =
        ∏ i : Fin k, mass i := by
    calc
      _ = ∑ tuple ∈ Fintype.piFinset Sfull,
          ∏ i : Fin k, ‖afull i (tuple i)‖ := by
            apply Finset.sum_congr rfl
            intro tuple htuple
            rw [norm_prod]
      _ = ∏ i : Fin k, ∑ n ∈ Sfull i, ‖afull i n‖ := by
            exact (Finset.prod_univ_sum Sfull
              (fun i n => ‖afull i n‖)).symm
      _ = ∏ i : Fin k, mass i := by simp [mass]
  calc
    _ = ∏ i : Fin k, mass i := htuple
    _ = ∏ i ∈ Finset.univ.erase selected, mass i := by
          symm
          exact Finset.prod_erase (Finset.univ : Finset (Fin k)) hmassSelected
    _ ≤ 5 ^ 19 * Real.sqrt ((∏ i : Fin k, N i) / N selected) :=
      smoothOtherFactorMassProduct hk selected N mass hN hmassNonneg hmassBound

#print axioms smoothHeathBrownOuterTupleMass_le

/-- Exact factorization of the coefficient mass over all complementary
factor tuples.  The selected coordinate is pinned to `1`, so its mass is
exactly one and the tuple sum is the product of the other individual masses. -/
theorem smoothHeathBrownOuterTupleMass_eq_otherFactorProduct
    {k : ℕ} (selected : Fin k)
    (S : Fin k → Finset ℕ) (a : Fin k → ℕ → ℂ) :
    (∑ tuple ∈ Fintype.piFinset
        (fun i : Fin k => if i = selected then ({1} : Finset ℕ) else S i),
      ‖∏ i : Fin k,
        (if i = selected then 1 else a i (tuple i))‖) =
      ∏ i ∈ Finset.univ.erase selected,
        ∑ n ∈ S i, ‖a i n‖ := by
  classical
  let Sfull : Fin k → Finset ℕ := fun i =>
    if i = selected then {1} else S i
  let afull : Fin k → ℕ → ℂ := fun i n =>
    if i = selected then 1 else a i n
  let mass : Fin k → ℝ := fun i => ∑ n ∈ Sfull i, ‖afull i n‖
  have htuple :
      (∑ tuple ∈ Fintype.piFinset Sfull,
        ‖∏ i : Fin k, afull i (tuple i)‖) = ∏ i : Fin k, mass i := by
    calc
      _ = ∑ tuple ∈ Fintype.piFinset Sfull,
          ∏ i : Fin k, ‖afull i (tuple i)‖ := by
            apply Finset.sum_congr rfl
            intro tuple htuple
            rw [norm_prod]
      _ = ∏ i : Fin k, ∑ n ∈ Sfull i, ‖afull i n‖ := by
            exact (Finset.prod_univ_sum Sfull
              (fun i n => ‖afull i n‖)).symm
      _ = ∏ i : Fin k, mass i := by simp [mass]
  have hmassSelected : mass selected = 1 := by
    simp [mass, Sfull, afull]
  calc
    _ = ∏ i : Fin k, mass i := by
      simpa [Sfull, afull] using htuple
    _ = ∏ i ∈ Finset.univ.erase selected, mass i := by
      symm
      exact Finset.prod_erase (Finset.univ : Finset (Fin k)) hmassSelected
    _ = ∏ i ∈ Finset.univ.erase selected,
        ∑ n ∈ S i, ‖a i n‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ selected := (Finset.mem_erase.mp hi).1
      simp [mass, Sfull, afull, hne]

#print axioms smoothHeathBrownOuterTupleMass_eq_otherFactorProduct

/-- After fixing a positive outer product, the global product window cuts the
selected factor's two source support pieces into the exact two quotient
intervals used by `lda:small-group`.  Their endpoint containment is included
so each interval is immediately admissible for the `N/2` or `N` local bound. -/
theorem smoothHeathBrownSelectedSupport_productWindow_split
    {N M x y : ℝ} (hN : 0 < N) (hM : 0 < M)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    ((factorExtractionDyadicInterval (N / 2) ∪
        factorExtractionDyadicInterval N).filter
      (fun n : ℕ => M * (n : ℝ) ∈ Set.Ioc x y)) =
        factorExtractionRealInterval
          (max (N / 2) (x / M)) (min N (y / M)) ∪
        factorExtractionRealInterval
          (max N (x / M)) (min (2 * N) (y / M)) ∧
      Set.Ioc (max (N / 2) (x / M)) (min N (y / M)) ⊆
        Set.Ioc (N / 2) N ∧
      Set.Ioc (max N (x / M)) (min (2 * N) (y / M)) ⊆
        Set.Ioc N (2 * N) := by
  have hNhalf : 0 < N / 2 := by positivity
  have hdouble : 2 * (N / 2) = N := by ring
  have hlow :
      (factorExtractionDyadicInterval (N / 2)).filter
          (fun n : ℕ => M * (n : ℝ) ∈ Set.Ioc x y) =
        factorExtractionRealInterval
          (max (N / 2) (x / M)) (min N (y / M)) := by
    ext n
    simp only [Finset.mem_filter]
    simpa [hdouble] using
      (factorExtractionDyadicProductInterval_iff
        hNhalf hM hx hxy n)
  have hhigh :
      (factorExtractionDyadicInterval N).filter
          (fun n : ℕ => M * (n : ℝ) ∈ Set.Ioc x y) =
        factorExtractionRealInterval
          (max N (x / M)) (min (2 * N) (y / M)) := by
    ext n
    simp only [Finset.mem_filter]
    exact factorExtractionDyadicProductInterval_iff hN hM hx hxy n
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.filter_union, hlow, hhigh]
  · intro z hz
    rcases hz with ⟨hzlo, hzhi⟩
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hzlo,
      le_trans hzhi (min_le_left _ _)⟩
  · intro z hz
    rcases hz with ⟨hzlo, hzhi⟩
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hzlo,
      le_trans hzhi (min_le_left _ _)⟩

#print axioms smoothHeathBrownSelectedSupport_productWindow_split

/-- For a fixed positive outer factor product, the original global product
window and residue condition split exactly into the two quotient intervals.
This equality preserves the source's `(u,v]` endpoints and keeps the full
product-dependent free-factor term in both pieces. -/
theorem smoothHeathBrownSelectedSupport_globalWindow_sum_split
    {N x y : ℝ} {m q a : ℕ} (hN : 0 < N) (hm : 0 < m)
    (hx : 0 ≤ x) (hxy : x ≤ y) (g : ℕ → ℂ) :
    (∑ n ∈ (factorExtractionDyadicInterval (N / 2) ∪
          factorExtractionDyadicInterval N).filter
        (fun n : ℕ =>
          (((m * n : ℕ) : ℝ) ∈ Set.Ioc x y) ∧ m * n ≡ a [MOD q]),
      g n) =
      (∑ n ∈ (factorExtractionRealInterval
          (max (N / 2) (x / (m : ℝ)))
          (min N (y / (m : ℝ)))).filter
            (fun n => m * n ≡ a [MOD q]), g n) +
      ∑ n ∈ (factorExtractionRealInterval
          (max N (x / (m : ℝ)))
          (min (2 * N) (y / (m : ℝ)))).filter
            (fun n => m * n ≡ a [MOD q]), g n := by
  classical
  let support : Finset ℕ :=
    factorExtractionDyadicInterval (N / 2) ∪ factorExtractionDyadicInterval N
  let window : ℕ → Prop := fun n =>
    (((m * n : ℕ) : ℝ) ∈ Set.Ioc x y)
  let congruent : ℕ → Prop := fun n => m * n ≡ a [MOD q]
  let low : Finset ℕ := factorExtractionRealInterval
    (max (N / 2) (x / (m : ℝ))) (min N (y / (m : ℝ)))
  let high : Finset ℕ := factorExtractionRealInterval
    (max N (x / (m : ℝ))) (min (2 * N) (y / (m : ℝ)))
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsplit := smoothHeathBrownSelectedSupport_productWindow_split
    hN hmreal hx hxy
  have hwindow : support.filter window = low ∪ high := by
    simpa [support, window, low, high, Nat.cast_mul] using hsplit.1
  have hfilter : support.filter (fun n => window n ∧ congruent n) =
      low.filter congruent ∪ high.filter congruent := by
    calc
      support.filter (fun n => window n ∧ congruent n) =
          (support.filter window).filter congruent := by
            ext n
            simp only [Finset.mem_filter]
            tauto
      _ = (low ∪ high).filter congruent := by rw [hwindow]
      _ = low.filter congruent ∪ high.filter congruent := by
            rw [Finset.filter_union]
  have huLow : 0 ≤ max (N / 2) (x / (m : ℝ)) :=
    le_max_of_le_left (by positivity)
  have hvLow : 0 ≤ min N (y / (m : ℝ)) :=
    le_min (by positivity)
      (div_nonneg (le_trans hx hxy) hmreal.le)
  have huHigh : 0 ≤ max N (x / (m : ℝ)) :=
    le_max_of_le_left hN.le
  have hvHigh : 0 ≤ min (2 * N) (y / (m : ℝ)) :=
    le_min (by positivity) (div_nonneg (le_trans hx hxy) hmreal.le)
  have hdisjoint : Disjoint (low.filter congruent) (high.filter congruent) := by
    rw [Finset.disjoint_left]
    intro n hnLow hnHigh
    have hLowReal : (n : ℝ) ∈ Set.Ioc
        (max (N / 2) (x / (m : ℝ))) (min N (y / (m : ℝ))) :=
      (mem_factorExtractionRealInterval huLow hvLow n).mp
        (Finset.mem_filter.mp hnLow).1
    have hHighReal : (n : ℝ) ∈ Set.Ioc
        (max N (x / (m : ℝ))) (min (2 * N) (y / (m : ℝ))) :=
      (mem_factorExtractionRealInterval huHigh hvHigh n).mp
        (Finset.mem_filter.mp hnHigh).1
    have hnle : (n : ℝ) ≤ N := (hsplit.2.1 hLowReal).2
    have hNlt : N < (n : ℝ) := (hsplit.2.2 hHighReal).1
    linarith
  calc
    _ = ∑ n ∈ support.filter (fun n => window n ∧ congruent n), g n := by
          simp [support, window, congruent]
    _ = ∑ n ∈ low.filter congruent ∪ high.filter congruent, g n := by
          rw [hfilter]
    _ = (∑ n ∈ low.filter congruent, g n) +
        ∑ n ∈ high.filter congruent, g n := Finset.sum_union hdisjoint

#print axioms smoothHeathBrownSelectedSupport_globalWindow_sum_split

/-- The fixed-product periodic estimate needs a residue representative only
when the filtered interval is nonempty.  Any point in that finite filter is
the required representative; if the filter is empty, the source sum is zero.
This is the tuplewise witness extraction used after the global product window
has been divided by the fixed positive outer product. -/
theorem smoothHeathBrownFreeFactor_productResidueInterval_bound_noWitness
    {alpha A X L T0 t x y : ℝ} {q a m : ℕ}
    (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hxL : L ≤ x) (hxy : x ≤ y) (hy2 : y ≤ 2 * L) :
    ‖∑ n ∈ (Finset.Ioc (Nat.floor x) (Nat.floor y)).filter
        (fun n => m * n ≡ a [MOD q]),
      smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ ≤
      smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A * Real.sqrt L *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  classical
  let S : Finset ℕ :=
    (Finset.Ioc (Nat.floor x) (Nat.floor y)).filter
      (fun n => m * n ≡ a [MOD q])
  have hcost : 0 ≤ smoothHeathBrownFreeFactorIntervalCost f := by
    cases f <;> simp [smoothHeathBrownFreeFactorIntervalCost]
  have hphase : 0 ≤ periodicLogPhaseConstant alpha A := by
    unfold periodicLogPhaseConstant
    exact le_trans (by norm_num) (le_max_left _ _)
  have herror : 0 ≤
      X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ) := by
    have hXpos : 0 < X := by linarith
    have hT0pos : 0 < T0 := by linarith
    exact add_nonneg (Real.rpow_nonneg hXpos.le _)
      (Real.rpow_nonneg hT0pos.le _)
  have hbound : 0 ≤ smoothHeathBrownFreeFactorIntervalCost f *
      periodicLogPhaseConstant alpha A * Real.sqrt L *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hcost hphase)
      (Real.sqrt_nonneg _)) herror
  by_cases hS : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hS
    have hmem : n₀ ∈ (Finset.Ioc (Nat.floor x) (Nat.floor y)).filter
        (fun n => m * n ≡ a [MOD q]) := by
      simpa [S] using hn₀
    have hsolution : m * n₀ ≡ a [MOD q] :=
      (Finset.mem_filter.mp hmem).2
    exact smoothHeathBrownFreeFactor_productResidueInterval_bound
      hX f hfree halpha halpha1 hA hLlower hLupper hq hqBound
      hT0 hT0t htX hxL hxy hy2 hsolution
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [show (Finset.Ioc (Nat.floor x) (Nat.floor y)).filter
        (fun n => m * n ≡ a [MOD q]) = S by rfl, hEmpty]
    simp
    exact hbound

#print axioms smoothHeathBrownFreeFactor_productResidueInterval_bound_noWitness

/-- Bound the selected free-factor sum after imposing the original global
product window.  The preceding exact split produces the two source quotient
intervals; each receives its own periodic bound at scale `N/2` or `N`, while
the discrete term retains its dependence on the fixed outer product `m`. -/
theorem smoothHeathBrownFreeFactor_globalProductWindow_bound
    {alpha A X T0 t x y : ℝ} {q a m : ℕ}
    (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hNlower : X ^ alpha ≤ smoothHeathBrownFactorScale f / 2)
    (hNupper : smoothHeathBrownFactorScale f ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hm : 0 < m) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖∑ n ∈ (factorExtractionDyadicInterval
          (smoothHeathBrownFactorScale f / 2) ∪
        factorExtractionDyadicInterval (smoothHeathBrownFactorScale f)).filter
        (fun n : ℕ =>
          (((m * n : ℕ) : ℝ) ∈ Set.Ioc x y) ∧ m * n ≡ a [MOD q]),
      smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ ≤
      smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A *
          (Real.sqrt (smoothHeathBrownFactorScale f / 2) +
            Real.sqrt (smoothHeathBrownFactorScale f)) *
            (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  let N : ℝ := smoothHeathBrownFactorScale f
  let M : ℝ := (m : ℝ)
  let xLow : ℝ := max (N / 2) (x / M)
  let yLow : ℝ := min N (y / M)
  let xHigh : ℝ := max N (x / M)
  let yHigh : ℝ := min (2 * N) (y / M)
  let C : ℝ := smoothHeathBrownFreeFactorIntervalCost f *
    periodicLogPhaseConstant alpha A *
      (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ))
  have hXpos : 0 < X := by linarith
  have hNlower' : X ^ alpha ≤ N / 2 := by simpa [N] using hNlower
  have hNpos : 0 < N := by
    have hrpow : 0 < X ^ alpha := Real.rpow_pos_of_pos hXpos _
    dsimp [N]
    linarith
  have hNupper' : N ≤ X := by simpa [N] using hNupper
  have hNhalfUpper : N / 2 ≤ X := le_trans (by linarith) hNupper'
  have hNfullLower : X ^ alpha ≤ N := le_trans hNlower' (by linarith)
  have hMpos : 0 < M := by dsimp [M]; exact_mod_cast hm
  have hsplit := smoothHeathBrownSelectedSupport_productWindow_split
    hNpos hMpos hx hxy
  have hcost : 0 ≤ smoothHeathBrownFreeFactorIntervalCost f := by
    cases f <;> simp [smoothHeathBrownFreeFactorIntervalCost]
  have hphase : 0 ≤ periodicLogPhaseConstant alpha A := by
    unfold periodicLogPhaseConstant
    exact le_trans (by norm_num) (le_max_left _ _)
  have herror : 0 ≤
      X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ) := by
    exact add_nonneg (Real.rpow_nonneg hXpos.le _)
      (Real.rpow_nonneg (by linarith : 0 ≤ T0) _)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hcost hphase) herror
  have hxLow : N / 2 ≤ xLow := by
    exact le_max_left _ _
  have hyLow : yLow ≤ N := by
    exact min_le_left _ _
  have hxHigh : N ≤ xHigh := by
    exact le_max_left _ _
  have hyHigh : yHigh ≤ 2 * N := by
    exact min_le_left _ _
  have hlow :
      ‖∑ n ∈ (factorExtractionRealInterval xLow yLow).filter
          (fun n => m * n ≡ a [MOD q]),
        smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ ≤
        C * Real.sqrt (N / 2) := by
    by_cases hxyLow : xLow ≤ yLow
    · have hbound := smoothHeathBrownFreeFactor_productResidueInterval_bound_noWitness
        (alpha := alpha) (A := A) (X := X) (L := N / 2) (T0 := T0)
        (t := t) (x := xLow) (y := yLow) (q := q) (a := a) (m := m)
        hX f hfree halpha halpha1 hA hNlower' hNhalfUpper
        hq hqBound hT0 hT0t htX hxLow hxyLow (by
          calc
            yLow ≤ N := hyLow
            _ = 2 * (N / 2) := by ring)
      calc
        _ ≤ smoothHeathBrownFreeFactorIntervalCost f *
              periodicLogPhaseConstant alpha A * Real.sqrt (N / 2) *
                (X ^ (-(periodicLogPhaseSaving alpha A)) +
                  T0 ^ (-1 / 2 : ℝ)) := by
                simpa [factorExtractionRealInterval] using hbound
        _ = C * Real.sqrt (N / 2) := by dsimp [C]; ring
    · have hxyLow' : yLow ≤ xLow := by linarith
      have hfloor : Nat.floor yLow ≤ Nat.floor xLow := Nat.floor_mono hxyLow'
      have hEmpty : factorExtractionRealInterval xLow yLow = ∅ := by
        unfold factorExtractionRealInterval
        exact Finset.Ioc_eq_empty_of_le hfloor
      rw [hEmpty]
      simp only [Finset.filter_empty, Finset.sum_empty, norm_zero]
      exact mul_nonneg hC (Real.sqrt_nonneg (N / 2))
  have hhigh :
      ‖∑ n ∈ (factorExtractionRealInterval xHigh yHigh).filter
          (fun n => m * n ≡ a [MOD q]),
        smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ ≤
        C * Real.sqrt N := by
    by_cases hxyHigh : xHigh ≤ yHigh
    · have hbound := smoothHeathBrownFreeFactor_productResidueInterval_bound_noWitness
        (alpha := alpha) (A := A) (X := X) (L := N) (T0 := T0)
        (t := t) (x := xHigh) (y := yHigh) (q := q) (a := a) (m := m)
        hX f hfree halpha halpha1 hA hNfullLower hNupper'
        hq hqBound hT0 hT0t htX hxHigh hxyHigh hyHigh
      calc
        _ ≤ smoothHeathBrownFreeFactorIntervalCost f *
              periodicLogPhaseConstant alpha A * Real.sqrt N *
                (X ^ (-(periodicLogPhaseSaving alpha A)) +
                  T0 ^ (-1 / 2 : ℝ)) := by
                simpa [factorExtractionRealInterval] using hbound
        _ = C * Real.sqrt N := by dsimp [C]; ring
    · have hxyHigh' : yHigh ≤ xHigh := by linarith
      have hfloor : Nat.floor yHigh ≤ Nat.floor xHigh := Nat.floor_mono hxyHigh'
      have hEmpty : factorExtractionRealInterval xHigh yHigh = ∅ := by
        unfold factorExtractionRealInterval
        exact Finset.Ioc_eq_empty_of_le hfloor
      rw [hEmpty]
      simp only [Finset.filter_empty, Finset.sum_empty, norm_zero]
      exact mul_nonneg hC (Real.sqrt_nonneg N)
  have hsplitSum := smoothHeathBrownSelectedSupport_globalWindow_sum_split
    (N := N) (x := x) (y := y) (m := m) (q := q) (a := a)
    hNpos hm hx hxy
    (fun n => smoothHeathBrownFreeFactorDiscreteTerm f m t n)
  have hlowNorm := hlow
  have hhighNorm := hhigh
  have hsumNorm :
      ‖(∑ n ∈ (factorExtractionRealInterval xLow yLow).filter
            (fun n => m * n ≡ a [MOD q]),
          smoothHeathBrownFreeFactorDiscreteTerm f m t n) +
        ∑ n ∈ (factorExtractionRealInterval xHigh yHigh).filter
            (fun n => m * n ≡ a [MOD q]),
          smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ ≤
      C * (Real.sqrt (N / 2) + Real.sqrt N) := by
    calc
      _ ≤ ‖∑ n ∈ (factorExtractionRealInterval xLow yLow).filter
              (fun n => m * n ≡ a [MOD q]),
            smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ +
            ‖∑ n ∈ (factorExtractionRealInterval xHigh yHigh).filter
              (fun n => m * n ≡ a [MOD q]),
            smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ := norm_add_le _ _
      _ ≤ C * Real.sqrt (N / 2) + C * Real.sqrt N := add_le_add hlowNorm hhighNorm
      _ = C * (Real.sqrt (N / 2) + Real.sqrt N) := by ring
  calc
    _ = ‖(∑ n ∈ (factorExtractionRealInterval xLow yLow).filter
            (fun n => m * n ≡ a [MOD q]),
          smoothHeathBrownFreeFactorDiscreteTerm f m t n) +
        ∑ n ∈ (factorExtractionRealInterval xHigh yHigh).filter
            (fun n => m * n ≡ a [MOD q]),
          smoothHeathBrownFreeFactorDiscreteTerm f m t n‖ := by
            simpa [N, M, xLow, yLow, xHigh, yHigh, Nat.cast_mul] using
              congrArg norm hsplitSum
    _ ≤ C * (Real.sqrt (N / 2) + Real.sqrt N) := hsumNorm
    _ = smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A *
          (Real.sqrt (smoothHeathBrownFactorScale f / 2) +
            Real.sqrt (smoothHeathBrownFactorScale f)) *
              (X ^ (-(periodicLogPhaseSaving alpha A)) +
                T0 ^ (-1 / 2 : ℝ)) := by
          dsimp [C, N]
          ring

#print axioms smoothHeathBrownFreeFactor_globalProductWindow_bound

/-- Sum the fixed-product theta/log estimate over the exact outer-factor
tuples, using their coefficient mass, and convert the product of source
scales to the component block scale.  The source exponent range
`-k ≤ h < k` and `k ≤ 20` give the exact loss `2^11 * 5^19` after the two
selected-factor support pieces are combined. -/
theorem smoothHeathBrownFreeFactor_selectedGroupGlobalWindow_blockBound
    {k : ℕ} (hk : k ≤ 20) (selected : Fin k)
    {alpha A X L T0 t x y : ℝ} {q a : ℕ}
    (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hNlower : X ^ alpha ≤ smoothHeathBrownFactorScale f / 2)
    (hNupper : smoothHeathBrownFactorScale f ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (h : ℤ) (N : Fin k → ℝ) (S : Fin k → Finset ℕ)
    (aFactor : Fin k → ℕ → ℂ)
    (hN : ∀ i, 0 < N i)
    (hSelectedScaleEq : N selected = smoothHeathBrownFactorScale f)
    (hMass : ∀ i, i ≠ selected →
      (∑ n ∈ S i, ‖aFactor i n‖) ≤ 5 * Real.sqrt (N i))
    (hOtherPositive : ∀ i, i ≠ selected → ∀ n ∈ S i, 0 < n)
    (hL : L = (2 : ℝ) ^ h * (∏ i : Fin k, N i))
    (hh : -(k : ℤ) ≤ h ∧ h < (k : ℤ))
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖∑ tuple ∈ Fintype.piFinset
        (fun i : Fin k => if i = selected then ({1} : Finset ℕ) else S i),
        (∏ i : Fin k,
          (if i = selected then 1 else aFactor i (tuple i))) *
          (∑ n ∈ (factorExtractionDyadicInterval
              (smoothHeathBrownFactorScale f / 2) ∪
            factorExtractionDyadicInterval (smoothHeathBrownFactorScale f)).filter
              (fun n : ℕ =>
                (((((∏ i : Fin k, tuple i) * n : ℕ) : ℝ) ∈ Set.Ioc x y) ∧
                  (∏ i : Fin k, tuple i) * n ≡ a [MOD q])),
            smoothHeathBrownFreeFactorDiscreteTerm f
              (∏ i : Fin k, tuple i) t n)‖ ≤
      (2 : ℝ) ^ 11 * 5 ^ 19 *
        smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A * Real.sqrt L *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  classical
  let support : Fin k → Finset ℕ := fun i =>
    if i = selected then {1} else S i
  let weight : (Fin k → ℕ) → ℂ := fun tuple =>
    ∏ i : Fin k, (if i = selected then 1 else aFactor i (tuple i))
  let mass : Fin k → ℝ := fun i =>
    ∑ n ∈ support i,
      ‖if i = selected then (1 : ℂ) else aFactor i n‖
  let K : ℝ := smoothHeathBrownFreeFactorIntervalCost f *
    periodicLogPhaseConstant alpha A *
      (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ))
  let R : Finset (Fin k → ℕ) := Fintype.piFinset support
  have hXpos : 0 < X := by linarith
  have hPpos : 0 < ∏ i : Fin k, N i :=
    Finset.prod_pos fun i hi => hN i
  have hNselected : 0 < N selected := hN selected
  have hscaleLower : X ^ alpha ≤ smoothHeathBrownFactorScale f / 2 := hNlower
  have hscaleUpper : smoothHeathBrownFactorScale f ≤ X := hNupper
  have hcost : 0 ≤ smoothHeathBrownFreeFactorIntervalCost f := by
    cases f <;> simp [smoothHeathBrownFreeFactorIntervalCost]
  have hphase : 0 ≤ periodicLogPhaseConstant alpha A := by
    unfold periodicLogPhaseConstant
    exact le_trans (by norm_num) (le_max_left _ _)
  have herror : 0 ≤
      X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ) := by
    exact add_nonneg (Real.rpow_nonneg hXpos.le _)
      (Real.rpow_nonneg (by linarith : 0 ≤ T0) _)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hcost hphase) herror
  have hmassNonneg : ∀ i, 0 ≤ mass i := by
    intro i
    dsimp [mass]
    apply Finset.sum_nonneg
    intro n hn
    exact norm_nonneg _
  have hmassBound : ∀ i, i ≠ selected →
      mass i ≤ 5 * Real.sqrt (N i) := by
    intro i hi
    simpa [mass, support, hi] using hMass i hi
  have htupleMass := smoothHeathBrownOuterTupleMass_eq_otherFactorProduct
    selected S aFactor
  have hscale := smoothGroupSelectedMassScale hk selected h N mass L hN
    hmassNonneg hmassBound hL hh
  have hlocal : ∀ tuple ∈ R,
      ‖∑ n ∈ (factorExtractionDyadicInterval
          (smoothHeathBrownFactorScale f / 2) ∪
        factorExtractionDyadicInterval (smoothHeathBrownFactorScale f)).filter
          (fun n : ℕ =>
            (((((∏ i : Fin k, tuple i) * n : ℕ) : ℝ) ∈ Set.Ioc x y) ∧
              (∏ i : Fin k, tuple i) * n ≡ a [MOD q])),
        smoothHeathBrownFreeFactorDiscreteTerm f
          (∏ i : Fin k, tuple i) t n‖ ≤
        2 * K * Real.sqrt (N selected) := by
    intro tuple htuple
    have hcoords := Fintype.mem_piFinset.mp (by simpa [R] using htuple)
    have hselectedMem : tuple selected ∈ ({1} : Finset ℕ) := by
      simpa [support] using hcoords selected
    have hselectedOne : tuple selected = 1 := Finset.mem_singleton.mp hselectedMem
    have htuplePositive : ∀ i, 0 < tuple i := by
      intro i
      by_cases hi : i = selected
      · subst i
        rw [hselectedOne]
        norm_num
      · have hcoord : tuple i ∈ S i := by
          simpa [support, hi] using hcoords i
        exact hOtherPositive i hi (tuple i) hcoord
    have hmTuple : 0 < ∏ i : Fin k, tuple i :=
      Finset.prod_pos fun i hi => htuplePositive i
    have hbound := smoothHeathBrownFreeFactor_globalProductWindow_bound
      (q := q) (a := a) (m := ∏ i : Fin k, tuple i)
      hX f hfree halpha halpha1 hA hNlower hNupper hq hqBound
      hT0 hT0t htX hmTuple hx hxy
    have hroot :
        Real.sqrt (N selected / 2) + Real.sqrt (N selected) ≤
          2 * Real.sqrt (N selected) := by
      have hsmall : Real.sqrt (N selected / 2) ≤ Real.sqrt (N selected) := by
        apply Real.sqrt_le_sqrt
        linarith
      nlinarith [hsmall, Real.sqrt_nonneg (N selected)]
    have hboundK :
        ‖∑ n ∈ (factorExtractionDyadicInterval
            (smoothHeathBrownFactorScale f / 2) ∪
          factorExtractionDyadicInterval (smoothHeathBrownFactorScale f)).filter
            (fun n : ℕ =>
              (((((∏ i : Fin k, tuple i) * n : ℕ) : ℝ) ∈ Set.Ioc x y) ∧
                (∏ i : Fin k, tuple i) * n ≡ a [MOD q])),
          smoothHeathBrownFreeFactorDiscreteTerm f
            (∏ i : Fin k, tuple i) t n‖ ≤
          K * (Real.sqrt (N selected / 2) + Real.sqrt (N selected)) := by
      have hbound' :
          ‖∑ n ∈ (factorExtractionDyadicInterval
              (smoothHeathBrownFactorScale f / 2) ∪
            factorExtractionDyadicInterval (smoothHeathBrownFactorScale f)).filter
              (fun n : ℕ =>
                (((((∏ i : Fin k, tuple i) * n : ℕ) : ℝ) ∈ Set.Ioc x y) ∧
                  (∏ i : Fin k, tuple i) * n ≡ a [MOD q])),
            smoothHeathBrownFreeFactorDiscreteTerm f
              (∏ i : Fin k, tuple i) t n‖ ≤
          smoothHeathBrownFreeFactorIntervalCost f *
            periodicLogPhaseConstant alpha A *
              (Real.sqrt (N selected / 2) + Real.sqrt (N selected)) *
                (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
        simpa only [hSelectedScaleEq] using hbound
      calc
        _ ≤ smoothHeathBrownFreeFactorIntervalCost f *
              periodicLogPhaseConstant alpha A *
                (Real.sqrt (N selected / 2) + Real.sqrt (N selected)) *
                  (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := hbound'
        _ = K * (Real.sqrt (N selected / 2) + Real.sqrt (N selected)) := by
          dsimp [K]
          ring
    calc
      _ ≤ K * (Real.sqrt (N selected / 2) + Real.sqrt (N selected)) := hboundK
      _ ≤ K * (2 * Real.sqrt (N selected)) :=
        mul_le_mul_of_nonneg_left hroot hK
      _ = 2 * K * Real.sqrt (N selected) := by ring
  have hweightMass :
      (∑ tuple ∈ R, ‖weight tuple‖) =
        ∏ i ∈ Finset.univ.erase selected, mass i := by
    have h := htupleMass
    calc
      (∑ tuple ∈ R, ‖weight tuple‖) =
          ∏ i ∈ Finset.univ.erase selected,
            ∑ n ∈ S i, ‖aFactor i n‖ := by
              simpa [R, support, weight] using h
      _ = ∏ i ∈ Finset.univ.erase selected, mass i := by
            apply Finset.prod_congr rfl
            intro i hi
            have hne : i ≠ selected := (Finset.mem_erase.mp hi).1
            simp [mass, support, hne]
  have hsumBound :
      ‖∑ tuple ∈ R, weight tuple *
          (∑ n ∈ (factorExtractionDyadicInterval
              (smoothHeathBrownFactorScale f / 2) ∪
            factorExtractionDyadicInterval (smoothHeathBrownFactorScale f)).filter
              (fun n : ℕ =>
                (((((∏ i : Fin k, tuple i) * n : ℕ) : ℝ) ∈ Set.Ioc x y) ∧
                  (∏ i : Fin k, tuple i) * n ≡ a [MOD q])),
            smoothHeathBrownFreeFactorDiscreteTerm f
              (∏ i : Fin k, tuple i) t n)‖ ≤
        (∏ i ∈ Finset.univ.erase selected, mass i) *
          (2 * K * Real.sqrt (N selected)) := by
    calc
      _ ≤ ∑ tuple ∈ R, ‖weight tuple *
          (∑ n ∈ (factorExtractionDyadicInterval
              (smoothHeathBrownFactorScale f / 2) ∪
            factorExtractionDyadicInterval (smoothHeathBrownFactorScale f)).filter
              (fun n : ℕ =>
                (((((∏ i : Fin k, tuple i) * n : ℕ) : ℝ) ∈ Set.Ioc x y) ∧
                  (∏ i : Fin k, tuple i) * n ≡ a [MOD q])),
            smoothHeathBrownFreeFactorDiscreteTerm f
              (∏ i : Fin k, tuple i) t n)‖ := norm_sum_le _ _
      _ ≤ ∑ tuple ∈ R, ‖weight tuple‖ *
          (2 * K * Real.sqrt (N selected)) := by
            apply Finset.sum_le_sum
            intro tuple htuple
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hlocal tuple htuple) (norm_nonneg _)
      _ = (∑ tuple ∈ R, ‖weight tuple‖) *
          (2 * K * Real.sqrt (N selected)) := by rw [Finset.sum_mul]
      _ = _ := by rw [hweightMass]
  have hsumScale :
      (∏ i ∈ Finset.univ.erase selected, mass i) *
          (2 * K * Real.sqrt (N selected)) ≤
        2 * K * ((2 : ℝ) ^ 10 * 5 ^ 19 * Real.sqrt L) := by
    calc
      _ = 2 * K *
          (Real.sqrt (N selected) *
            (∏ i ∈ Finset.univ.erase selected, mass i)) := by ring
      _ ≤ 2 * K * ((2 : ℝ) ^ 10 * 5 ^ 19 * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
  calc
    _ ≤ (∏ i ∈ Finset.univ.erase selected, mass i) *
          (2 * K * Real.sqrt (N selected)) := hsumBound
    _ ≤ 2 * K * ((2 : ℝ) ^ 10 * 5 ^ 19 * Real.sqrt L) := hsumScale
    _ = (2 : ℝ) ^ 11 * 5 ^ 19 *
        smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A * Real.sqrt L *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
            dsimp [K]
            ring

#print axioms smoothHeathBrownFreeFactor_selectedGroupGlobalWindow_blockBound

/-- The selected-group global-window estimate instantiated with the actual
normalized smooth Heath--Brown coefficients.  Complementary-factor mass and
support positivity are discharged from the checked coefficient and support
lemmas, leaving only the selected free-factor periodic estimate and the exact
component-scale hypotheses as inputs. -/
theorem smoothHeathBrownFreeFactor_selectedGroupGlobalWindow_blockBound_of_factors
    {X z : ℝ} {fs : List (SmoothHeathBrownFactor X)}
    (hk : fs.length ≤ 20) (selected : Fin fs.length)
    {alpha A L T0 t x y : ℝ} {q a : ℕ}
    (hX : 3 ≤ X) (hfree : ∀ j : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius j)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hNlower : X ^ alpha ≤
      smoothHeathBrownFactorScale (fs.get selected) / 2)
    (hNupper : smoothHeathBrownFactorScale (fs.get selected) ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (h : ℤ) (ω : Fin fs.length → ℕ → ℂ)
    (hω : ∀ i n, ‖ω i n‖ ≤ 1)
    (hL : L = (2 : ℝ) ^ h *
      (∏ i : Fin fs.length,
        smoothHeathBrownFactorScale (fs.get i)))
    (hh : -(fs.length : ℤ) ≤ h ∧ h < (fs.length : ℤ))
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖∑ tuple ∈ Fintype.piFinset
        (fun i : Fin fs.length =>
          if i = selected then ({1} : Finset ℕ)
          else smoothHeathBrownFactorFiniteSupport (fs.get i)),
        (∏ i : Fin fs.length,
          if i = selected then (1 : ℂ) else
            smoothHeathBrownWeightedFactorCoefficient (z := z)
              (fs.get i) (ω i) (tuple i)) *
          (∑ n ∈ (factorExtractionDyadicInterval
              (smoothHeathBrownFactorScale (fs.get selected) / 2) ∪
            factorExtractionDyadicInterval
              (smoothHeathBrownFactorScale (fs.get selected))).filter
              (fun n : ℕ =>
                (((((∏ i : Fin fs.length, tuple i) * n : ℕ) : ℝ) ∈
                    Set.Ioc x y) ∧
                  (∏ i : Fin fs.length, tuple i) * n ≡ a [MOD q])),
            smoothHeathBrownFreeFactorDiscreteTerm
              (fs.get selected) (∏ i : Fin fs.length, tuple i) t n)‖ ≤
      (2 : ℝ) ^ 11 * 5 ^ 19 *
        smoothHeathBrownFreeFactorIntervalCost (fs.get selected) *
        periodicLogPhaseConstant alpha A * Real.sqrt L *
          (X ^ (-(periodicLogPhaseSaving alpha A)) +
            T0 ^ (-1 / 2 : ℝ)) := by
  classical
  let N : Fin fs.length → ℝ :=
    fun i => smoothHeathBrownFactorScale (fs.get i)
  let S : Fin fs.length → Finset ℕ :=
    fun i => smoothHeathBrownFactorFiniteSupport (fs.get i)
  let aFactor : Fin fs.length → ℕ → ℂ :=
    fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
      (fs.get i) (ω i) n
  have hN : ∀ i, 0 < N i := by
    intro i
    dsimp [N]
    have hscale := smoothHeathBrownFactorScale_ge_one (fs.get i)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale
  have hMass : ∀ i, i ≠ selected →
      (∑ n ∈ S i, ‖aFactor i n‖) ≤ 5 * Real.sqrt (N i) := by
    intro i hi
    have hweight : ∀ n ∈ smoothHeathBrownFactorFiniteSupport (fs.get i),
        ‖ω i n‖ ≤ 1 := by
      intro n hn
      exact hω i n
    simpa [S, aFactor, N] using
      smoothHeathBrownWeightedFactorMass hX (fs.get i) (ω i) hweight
  have hOtherPositive : ∀ i, i ≠ selected → ∀ n ∈ S i, 0 < n := by
    intro i hi n hn
    change n ∈ smoothHeathBrownFactorFiniteSupport (fs.get i) at hn
    have hmem : n ∈ smoothFactorMassWindow
        (smoothHeathBrownFactorScale (fs.get i)) := by
      rw [← smoothHeathBrownFactorFiniteSupport_eq_massWindow]
      exact hn
    have hwindow := (mem_smoothFactorMassWindow
      (le_of_lt (hN i)) n).mp hmem
    have hNi : 0 < smoothHeathBrownFactorScale (fs.get i) := by
      simpa [N] using hN i
    have hnreal : 0 < (n : ℝ) := by
      have hhalf : 0 < smoothHeathBrownFactorScale (fs.get i) / 2 :=
        div_pos hNi (by norm_num)
      linarith
    exact_mod_cast hnreal
  simpa [N, S, aFactor] using
    (smoothHeathBrownFreeFactor_selectedGroupGlobalWindow_blockBound
      (hk := hk) (selected := selected) (alpha := alpha) (A := A)
      (X := X) (L := L) (T0 := T0) (t := t) (x := x) (y := y)
      (q := q) (a := a) hX (fs.get selected) hfree halpha halpha1 hA
      hNlower hNupper hq hqBound hT0 hT0t htX h N S aFactor hN
      rfl hMass hOtherPositive hL hh hx hxy)

#print axioms smoothHeathBrownFreeFactor_selectedGroupGlobalWindow_blockBound_of_factors

/-- Explicit logarithmic absorption for the two periodic free-factor error
terms.  The first threshold is exactly the hypothesis of
`log_absorption_bound` with saving exponent `delta` and power `K`; the second
absorbs the `sqrt(2) (log X)^(-D/2)` tail using the full five-log margin from
`D ≥ 2K+10`. -/
theorem smoothHeathBrownFreeFactor_logError_absorption
    {X K D C delta : ℝ}
    (hX : 1 ≤ X) (hlog : 1 ≤ Real.log X)
    (hK : 0 ≤ K) (hD : 2 * K + 10 ≤ D)
    (hC : 1 ≤ C) (hdelta : 0 < delta)
    (hpolyLarge : (2 / delta) *
      Real.log (2 * C * logAbsorptionM delta K) ≤ Real.log X)
    (htailLarge : (2 * Real.sqrt 2 * C) ^ (1 / 5 : ℝ) ≤ Real.log X) :
    C * (X ^ (-delta) +
      Real.sqrt 2 * (Real.log X) ^ (-D / 2)) ≤
        (Real.log X) ^ (-K) := by
  have hXpos : 0 < X := by linarith
  have hu : 0 < Real.log X := by linarith
  have huNonneg : 0 ≤ Real.log X := le_of_lt hu
  have hCpos : 0 < C := by linarith
  have hpoly := log_absorption_bound
    (a := delta) (b := K) (K := 2 * C) (X := X)
    hdelta hK (by nlinarith) hX hpolyLarge
  have hpolySplit : C * X ^ (-delta) ≤
      (1 / 2 : ℝ) * (Real.log X) ^ (-K) := by
    have hden : 0 < X ^ delta := Real.rpow_pos_of_pos hXpos _
    have hnum : 0 < 2 * C * (Real.log X) ^ K := by positivity
    have hinv : 1 / (X ^ delta) ≤
        1 / (2 * C * (Real.log X) ^ K) :=
      one_div_le_one_div_of_le hnum hpoly
    calc
      C * X ^ (-delta) = C * (1 / (X ^ delta)) := by
        rw [Real.rpow_neg hXpos.le]
        ring
      _ ≤ C * (1 / (2 * C * (Real.log X) ^ K)) :=
        mul_le_mul_of_nonneg_left hinv hCpos.le
      _ = (1 / 2 : ℝ) * (Real.log X) ^ (-K) := by
        rw [Real.rpow_neg huNonneg K]
        field_simp
  let H : ℝ := 2 * Real.sqrt 2 * C
  have hHpos : 0 < H := by dsimp [H]; positivity
  have hHpow : H ≤ (Real.log X) ^ (5 : ℝ) := by
    have hpowIdent : H ^ ((1 / 5 : ℝ) * 5) =
        (H ^ (1 / 5 : ℝ)) ^ (5 : ℝ) := by
      rw [Real.rpow_mul hHpos.le]
    calc
      H = H ^ ((1 / 5 : ℝ) * 5) := by
        rw [show (1 / 5 : ℝ) * 5 = 1 by norm_num, Real.rpow_one]
      _ = (H ^ (1 / 5 : ℝ)) ^ (5 : ℝ) := hpowIdent
      _ ≤ (Real.log X) ^ (5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) htailLarge (by norm_num)
  have htailInv : (Real.log X) ^ (-(5 : ℝ)) ≤ 1 / H := by
    rw [Real.rpow_neg huNonneg (5 : ℝ)]
    simpa [one_div] using one_div_le_one_div_of_le hHpos hHpow
  have hDhalf : K + 5 ≤ D / 2 := by linarith
  have hExp : -(D / 2) ≤ -(K + 5) := by linarith
  have htailPower : (Real.log X) ^ (-(D / 2)) ≤
      (Real.log X) ^ (-(K + 5)) :=
    Real.rpow_le_rpow_of_exponent_le hlog hExp
  have hsplitPower : (Real.log X) ^ (-(K + 5)) =
      (Real.log X) ^ (-K) * (Real.log X) ^ (-(5 : ℝ)) := by
    rw [show -(K + 5) = (-K) + (-(5 : ℝ)) by ring,
      Real.rpow_add hu]
  have htailSplit : C * Real.sqrt 2 *
        (Real.log X) ^ (-(D / 2)) ≤
      (1 / 2 : ℝ) * (Real.log X) ^ (-K) := by
    calc
      _ ≤ C * Real.sqrt 2 * (Real.log X) ^ (-(K + 5)) :=
        mul_le_mul_of_nonneg_left htailPower (by positivity)
      _ = C * Real.sqrt 2 *
          ((Real.log X) ^ (-K) * (Real.log X) ^ (-(5 : ℝ))) := by
        rw [hsplitPower]
      _ ≤ C * Real.sqrt 2 *
          ((Real.log X) ^ (-K) * (1 / H)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left htailInv
            (Real.rpow_nonneg huNonneg _)
        · positivity
      _ = (1 / 2 : ℝ) * (Real.log X) ^ (-K) := by
        dsimp [H]
        field_simp
  calc
    _ = C * X ^ (-delta) +
        C * Real.sqrt 2 * (Real.log X) ^ (-(D / 2)) := by ring_nf
    _ ≤ (1 / 2 : ℝ) * (Real.log X) ^ (-K) +
        (1 / 2 : ℝ) * (Real.log X) ^ (-K) :=
      add_le_add hpolySplit htailSplit
    _ = (Real.log X) ^ (-K) := by ring

#print axioms smoothHeathBrownFreeFactor_logError_absorption

/-- The source choice `T0 = (log X)^D / 2` contributes exactly the
`sqrt(2) (log X)^(-D/2)` term used in the absorption estimate. -/
theorem smoothHeathBrownFreeFactor_sourceFrequencyTail_eq
    {u D T0 : ℝ} (hu : 0 < u)
    (hT0 : T0 = u ^ D / 2) :
    T0 ^ (-1 / 2 : ℝ) = Real.sqrt 2 * u ^ (-D / 2) := by
  have hbase : 0 ≤ u ^ D := Real.rpow_nonneg hu.le _
  have hpow : (u ^ D) ^ (-1 / 2 : ℝ) = u ^ (-D / 2) := by
    rw [← Real.rpow_mul hu.le]
    congr 1
    ring
  have htwo : (2 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    calc
      (2 : ℝ) ^ (-1 / 2 : ℝ) =
          (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by congr 1 <;> ring
      _ = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ :=
        Real.rpow_neg (by norm_num) (1 / 2 : ℝ)
      _ = (Real.sqrt 2)⁻¹ := by rw [← Real.sqrt_eq_rpow]
  rw [hT0, Real.div_rpow hbase (by norm_num) (-1 / 2 : ℝ), hpow, htwo]
  field_simp

#print axioms smoothHeathBrownFreeFactor_sourceFrequencyTail_eq

/-- The previous absorption lemma with the source frequency cutoff
`T0 = (log X)^D/2` substituted exactly. -/
theorem smoothHeathBrownFreeFactor_sourceLogError_absorption
    {X K D C delta T0 : ℝ}
    (hX : 1 ≤ X) (hlog : 1 ≤ Real.log X)
    (hK : 0 ≤ K) (hD : 2 * K + 10 ≤ D)
    (hC : 1 ≤ C) (hdelta : 0 < delta)
    (hT0 : T0 = (Real.log X) ^ D / 2)
    (hpolyLarge : (2 / delta) *
      Real.log (2 * C * logAbsorptionM delta K) ≤ Real.log X)
    (htailLarge : (2 * Real.sqrt 2 * C) ^ (1 / 5 : ℝ) ≤ Real.log X) :
    C * (X ^ (-delta) + T0 ^ (-1 / 2 : ℝ)) ≤
      (Real.log X) ^ (-K) := by
  have hu : 0 < Real.log X := by linarith
  have htail := smoothHeathBrownFreeFactor_sourceFrequencyTail_eq hu hT0
  rw [htail]
  exact smoothHeathBrownFreeFactor_logError_absorption hX hlog hK hD hC
    hdelta hpolyLarge htailLarge

#print axioms smoothHeathBrownFreeFactor_sourceLogError_absorption

/-- Exact source prefactor of the selected theta/log block estimate at
`(alpha,A)=(1/200,1)`. -/
noncomputable def smoothHeathBrownFreeFactorBlockConstant
    {X : ℝ} (f : SmoothHeathBrownFactor X) : ℝ :=
  (2 : ℝ) ^ 11 * 5 ^ 19 *
    smoothHeathBrownFreeFactorIntervalCost f *
    periodicLogPhaseConstant (1 / 200) 1

/-- The exact free-factor block prefactor exceeds one for either source
branch; the Mobius tag is excluded as in the theta/log branch. -/
theorem smoothHeathBrownFreeFactorBlockConstant_ge_one
    {X : ℝ} (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j) :
    1 ≤ smoothHeathBrownFreeFactorBlockConstant f := by
  have hphase : 64 ≤ periodicLogPhaseConstant (1 / 200) 1 := by
    unfold periodicLogPhaseConstant
    exact le_max_left _ _
  cases f with
  | theta j =>
      norm_num [smoothHeathBrownFreeFactorBlockConstant,
        smoothHeathBrownFreeFactorIntervalCost]
      nlinarith [hphase]
  | logarithm j =>
      norm_num [smoothHeathBrownFreeFactorBlockConstant,
        smoothHeathBrownFreeFactorIntervalCost]
      nlinarith [hphase]
  | mobius j => exact (hfree j rfl).elim

#print axioms smoothHeathBrownFreeFactorBlockConstant_ge_one

/-- The source cutoff `T0=(log X)^D/2` is at least one once `log X≥2`
and `D≥10`, as required by the periodic-factor theorem. -/
theorem smoothHeathBrownFreeFactor_sourceT0_ge_one
    {u D T0 : ℝ} (hu : 2 ≤ u) (hD : 10 ≤ D)
    (hT0 : T0 = u ^ D / 2) : 1 ≤ T0 := by
  have hpow10 : (2 : ℝ) ^ (10 : ℝ) ≤ u ^ (10 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hu (by norm_num)
  have hpowD : u ^ (10 : ℝ) ≤ u ^ D :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hD
  rw [hT0]
  nlinarith

#print axioms smoothHeathBrownFreeFactor_sourceT0_ge_one

/-- Logarithmically sized moduli meet the periodic theorem's exact
`X^(1/400)` modulus hypothesis after the source elementary-growth
threshold. -/
theorem smoothHeathBrownFreeFactor_modulus_log_bound
    {X B : ℝ} {q : ℕ}
    (hX : 1 ≤ X) (hB : 0 ≤ B)
    (hqLog : (q : ℝ) ≤ (Real.log X) ^ B)
    (hlarge : (2 / (1 / 400 : ℝ)) *
      Real.log (logAbsorptionM (1 / 400) B) ≤ Real.log X) :
    (q : ℝ) ≤ X ^ (1 / 400 : ℝ) := by
  have hmod := log_absorption_bound
    (a := (1 / 400 : ℝ)) (b := B) (K := (1 : ℝ)) (X := X)
    (by norm_num) hB (by norm_num) hX (by simpa using hlarge)
  exact hqLog.trans (by simpa only [one_mul] using hmod)

#print axioms smoothHeathBrownFreeFactor_modulus_log_bound

/-- The selected-group scale bounds in `lda:small-group` imply the exact
`(alpha,A)=(1/200,1)` window required by the periodic free-factor estimate
once `X≥2^200`. -/
theorem smoothHeathBrownFreeFactor_sourceScale_meetsPeriodicWindow
    {X N : ℝ} (hX : (2 : ℝ) ^ 200 ≤ X)
    (hNlower : X ^ (1 / 100 : ℝ) ≤ N)
    (hNupper : N ≤ (2 : ℝ) ^ 11 * Real.sqrt X) :
    X ^ (1 / 200 : ℝ) ≤ N / 2 ∧ N ≤ X := by
  have hXpos : 0 < X := by
    have : 0 < (2 : ℝ) ^ 200 := by positivity
    linarith
  have hroot : 2 ≤ X ^ (1 / 200 : ℝ) := by
    have hpow := Real.rpow_le_rpow
      (by positivity : 0 ≤ (2 : ℝ) ^ 200) hX
      (by norm_num : 0 ≤ (1 / 200 : ℝ))
    have htwo : ((2 : ℝ) ^ 200) ^ (1 / 200 : ℝ) = 2 := by
      rw [← Real.rpow_natCast (2 : ℝ) 200,
        ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num
    calc
      2 = ((2 : ℝ) ^ 200) ^ (1 / 200 : ℝ) := htwo.symm
      _ ≤ X ^ (1 / 200 : ℝ) := hpow
  have hscaleRpow : X ^ (1 / 100 : ℝ) =
      (X ^ (1 / 200 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast (X ^ (1 / 200 : ℝ)) 2,
      ← Real.rpow_mul hXpos.le]
    congr 1
    norm_num
  have hsmall : X ^ (1 / 200 : ℝ) ≤ N / 2 := by
    rw [hscaleRpow] at hNlower
    nlinarith [hroot]
  have hXpow : (2 : ℝ) ^ 22 ≤ X := by
    calc
      (2 : ℝ) ^ 22 ≤ (2 : ℝ) ^ 200 := by norm_num
      _ ≤ X := hX
  have hrootUpper : (2 : ℝ) ^ 11 ≤ Real.sqrt X := by
    have hsquare : Real.sqrt ((2 : ℝ) ^ 22) = (2 : ℝ) ^ 11 := by
      rw [show (2 : ℝ) ^ 22 = ((2 : ℝ) ^ 11) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs]
      norm_num
    calc
      (2 : ℝ) ^ 11 = Real.sqrt ((2 : ℝ) ^ 22) := hsquare.symm
      _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hXpow
  have hXeq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hXpos.le
  have hlarge : N ≤ X := by
    nlinarith [hNupper, hrootUpper, hXeq]
  exact ⟨hsmall, hlarge⟩

#print axioms smoothHeathBrownFreeFactor_sourceScale_meetsPeriodicWindow

/-- Source-shaped theta/log selected-group bound after both periodic-error
terms have been absorbed.  The explicit scale, frequency, modulus and
large-`X` hypotheses are precisely those used by the checked block estimate
and its source logarithmic absorption; the factor coefficients are the
normalized smooth Heath--Brown coefficients. -/
theorem smoothHeathBrownFreeFactor_selectedGroupGlobalWindow_logDecay_of_factors
    {X z B K D L T0 t x y : ℝ}
    {fs : List (SmoothHeathBrownFactor X)}
    (hk : fs.length ≤ 20) (selected : Fin fs.length)
    {q a : ℕ}
    (hX : 3 ≤ X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X,
      fs.get selected ≠ .mobius j)
    (hB : 0 < B) (hK : 0 < K) (hD : 2 * K + 10 ≤ D)
    (hlog : 2 ≤ Real.log X)
    (hq : 0 < q) (hqLog : (q : ℝ) ≤ (Real.log X) ^ B)
    (hqLarge : (2 / (1 / 400 : ℝ)) *
      Real.log (logAbsorptionM (1 / 400) B) ≤ Real.log X)
    (hT0Eq : T0 = (Real.log X) ^ D / 2)
    (hT0t : T0 ≤ |t|) (htX : |t| ≤ X)
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hNlower : X ^ (1 / 100 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected))
    (hNupper : smoothHeathBrownFactorScale (fs.get selected) ≤
      (2 : ℝ) ^ 11 * Real.sqrt X)
    (h : ℤ) (ω : Fin fs.length → ℕ → ℂ)
    (hω : ∀ i n, ‖ω i n‖ ≤ 1)
    (hL : L = (2 : ℝ) ^ h *
      (∏ i : Fin fs.length,
        smoothHeathBrownFactorScale (fs.get i)))
    (hh : -(fs.length : ℤ) ≤ h ∧ h < (fs.length : ℤ))
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hpolyLarge : (2 / periodicLogPhaseSaving (1 / 200) 1) *
      Real.log (2 * smoothHeathBrownFreeFactorBlockConstant
          (fs.get selected) *
        logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) ≤
          Real.log X)
    (htailLarge : (2 * Real.sqrt 2 *
      smoothHeathBrownFreeFactorBlockConstant (fs.get selected)) ^
        (1 / 5 : ℝ) ≤ Real.log X) :
    ‖∑ tuple ∈ Fintype.piFinset
        (fun i : Fin fs.length =>
          if i = selected then ({1} : Finset ℕ)
          else smoothHeathBrownFactorFiniteSupport (fs.get i)),
        (∏ i : Fin fs.length,
          if i = selected then (1 : ℂ) else
            smoothHeathBrownWeightedFactorCoefficient (z := z)
              (fs.get i) (ω i) (tuple i)) *
          (∑ n ∈ (factorExtractionDyadicInterval
              (smoothHeathBrownFactorScale (fs.get selected) / 2) ∪
            factorExtractionDyadicInterval
              (smoothHeathBrownFactorScale (fs.get selected))).filter
              (fun n : ℕ =>
                (((((∏ i : Fin fs.length, tuple i) * n : ℕ) : ℝ) ∈
                    Set.Ioc x y) ∧
                  (∏ i : Fin fs.length, tuple i) * n ≡ a [MOD q])),
            smoothHeathBrownFreeFactorDiscreteTerm
              (fs.get selected) (∏ i : Fin fs.length, tuple i) t n)‖ ≤
      Real.sqrt L * (Real.log X) ^ (-K) := by
  have hXone : 1 ≤ X := by linarith
  have hKnonneg : 0 ≤ K := le_of_lt hK
  have hD10 : 10 ≤ D := by linarith
  have hlogone : 1 ≤ Real.log X := by linarith
  have hT0 : 1 ≤ T0 :=
    smoothHeathBrownFreeFactor_sourceT0_ge_one hlog hD10 hT0Eq
  have hqBound : (q : ℝ) ≤ X ^ (1 / 400 : ℝ) :=
    smoothHeathBrownFreeFactor_modulus_log_bound hXone hB.le hqLog hqLarge
  have hqBound' : (q : ℝ) ≤ X ^ ((1 / 200 : ℝ) / 2) := by
    have heq : (1 / 200 : ℝ) / 2 = (1 / 400 : ℝ) := by norm_num
    rw [heq]
    exact hqBound
  have hselectedWindow := smoothHeathBrownFreeFactor_sourceScale_meetsPeriodicWindow
    hXscale hNlower hNupper
  have hC : 1 ≤ smoothHeathBrownFreeFactorBlockConstant
      (fs.get selected) :=
    smoothHeathBrownFreeFactorBlockConstant_ge_one
      (fs.get selected) hfree
  have hdelta : 0 < periodicLogPhaseSaving (1 / 200) 1 := by
    unfold periodicLogPhaseSaving
    positivity
  have herr := smoothHeathBrownFreeFactor_sourceLogError_absorption
    hXone hlogone hKnonneg hD hC hdelta hT0Eq hpolyLarge htailLarge
  have hblock := smoothHeathBrownFreeFactor_selectedGroupGlobalWindow_blockBound_of_factors
    (hk := hk) (selected := selected) (X := X) (z := z) (alpha := (1 / 200 : ℝ))
    (A := 1) (L := L) (T0 := T0) (t := t) (x := x) (y := y)
    (q := q) (a := a) hX hfree (by norm_num) (by norm_num) (by norm_num)
    hselectedWindow.1 hselectedWindow.2 hq hqBound' hT0 hT0t
    (by simpa using htX) h ω hω hL hh hx hxy
  calc
    _ ≤ smoothHeathBrownFreeFactorBlockConstant (fs.get selected) *
        Real.sqrt L *
          (X ^ (-(periodicLogPhaseSaving (1 / 200) 1)) +
            T0 ^ (-1 / 2 : ℝ)) := by
      simpa [smoothHeathBrownFreeFactorBlockConstant, mul_assoc] using hblock
    _ = Real.sqrt L *
        (smoothHeathBrownFreeFactorBlockConstant (fs.get selected) *
          (X ^ (-(periodicLogPhaseSaving (1 / 200) 1)) +
            T0 ^ (-1 / 2 : ℝ))) := by ring
    _ ≤ Real.sqrt L * (Real.log X) ^ (-K) :=
      mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg L)

#print axioms smoothHeathBrownFreeFactor_selectedGroupGlobalWindow_logDecay_of_factors

/-- The ordered concrete factor list of a selected group, obtained by
enumerating its ambient index set in the canonical order used by the subset
reindexing API. -/
noncomputable def smoothHeathBrownSelectedGroupFactorList
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fs.length)) : List (SmoothHeathBrownFactor X) :=
  List.ofFn (fun j : Fin I.card =>
    fs.get (smoothGroupSubsetFinEquiv I j).val)

theorem smoothHeathBrownSelectedGroupFactorList_length
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fs.length)) :
    (smoothHeathBrownSelectedGroupFactorList fs I).length = I.card := by
  simp [smoothHeathBrownSelectedGroupFactorList]

/-- At every canonical group index, the reindexed factor is the original
ambient factor at the corresponding element of the selected subset. -/
theorem smoothHeathBrownSelectedGroupFactorList_get
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fs.length)) (j : Fin I.card) :
    (smoothHeathBrownSelectedGroupFactorList fs I).get
        (Fin.cast (smoothHeathBrownSelectedGroupFactorList_length fs I).symm j) =
      fs.get (smoothGroupSubsetFinEquiv I j).val := by
  let hlen := smoothHeathBrownSelectedGroupFactorList_length fs I
  have hi : j.val < (smoothHeathBrownSelectedGroupFactorList fs I).length := by
    simpa [hlen] using j.isLt
  have hcast : Fin.cast hlen.symm j = ⟨j.val, hi⟩ := by
    apply Fin.ext
    rfl
  rw [hcast]
  simp [smoothHeathBrownSelectedGroupFactorList, hlen]

/-- The selected ambient factor appears at the reindexed group position
corresponding to the unique index of `I`. -/
theorem smoothHeathBrownSelectedGroupFactorList_selected_get
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fs.length)) (selected : Fin fs.length)
    (hselected : selected ∈ I) :
    (smoothHeathBrownSelectedGroupFactorList fs I).get
        (Fin.cast (smoothHeathBrownSelectedGroupFactorList_length fs I).symm
          ((smoothGroupSubsetFinEquiv I).symm ⟨selected, hselected⟩)) =
      fs.get selected := by
  simpa using smoothHeathBrownSelectedGroupFactorList_get fs I
    ((smoothGroupSubsetFinEquiv I).symm ⟨selected, hselected⟩)

/-- The concrete selected-group factor has exactly one of the three source
tags. This is the branch point in `lda:small-group`: theta and normalized log
use the checked periodic estimate; a Möbius tag remains on the separate MUF
route. -/
theorem smoothHeathBrownSelectedGroupFactorList_selected_branch
    {X : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fs.length)) (selected : Fin fs.length)
    (hselected : selected ∈ I) :
    (∃ j, (smoothHeathBrownSelectedGroupFactorList fs I).get
      (Fin.cast (smoothHeathBrownSelectedGroupFactorList_length fs I).symm
        ((smoothGroupSubsetFinEquiv I).symm ⟨selected, hselected⟩)) = .theta j) ∨
    (∃ j, (smoothHeathBrownSelectedGroupFactorList fs I).get
      (Fin.cast (smoothHeathBrownSelectedGroupFactorList_length fs I).symm
        ((smoothGroupSubsetFinEquiv I).symm ⟨selected, hselected⟩)) = .logarithm j) ∨
    (∃ j, (smoothHeathBrownSelectedGroupFactorList fs I).get
      (Fin.cast (smoothHeathBrownSelectedGroupFactorList_length fs I).symm
        ((smoothGroupSubsetFinEquiv I).symm ⟨selected, hselected⟩)) = .mobius j) := by
  have hget := smoothHeathBrownSelectedGroupFactorList_selected_get
    fs I selected hselected
  cases hfactor : fs.get selected with
  | theta j =>
      exact Or.inl ⟨j, hget.trans hfactor⟩
  | logarithm j =>
      exact Or.inr (Or.inl ⟨j, hget.trans hfactor⟩)
  | mobius j =>
      exact Or.inr (Or.inr ⟨j, hget.trans hfactor⟩)

/-- The exact finite group block sum attached to a concrete factor list.
The selected coordinate is pinned to one in the outer tuple and its actual
theta/logarithm term is summed over the original product window. -/
noncomputable def smoothHeathBrownSelectedGroupGlobalWindowSum
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (selected : Fin fs.length) (ω : Fin fs.length → ℕ → ℂ)
    (q a : ℕ) (t x y : ℝ) : ℂ :=
  ∑ tuple ∈ Fintype.piFinset
      (fun i : Fin fs.length =>
        if i = selected then ({1} : Finset ℕ)
        else smoothHeathBrownFactorFiniteSupport (fs.get i)),
      (∏ i : Fin fs.length,
        if i = selected then (1 : ℂ) else
          smoothHeathBrownWeightedFactorCoefficient (z := z)
            (fs.get i) (ω i) (tuple i)) *
        (∑ n ∈ (factorExtractionDyadicInterval
            (smoothHeathBrownFactorScale (fs.get selected) / 2) ∪
          factorExtractionDyadicInterval
            (smoothHeathBrownFactorScale (fs.get selected))).filter
            (fun n : ℕ =>
              (((((∏ i : Fin fs.length, tuple i) * n : ℕ) : ℝ) ∈
                  Set.Ioc x y) ∧
                (∏ i : Fin fs.length, tuple i) * n ≡ a [MOD q])),
          smoothHeathBrownFreeFactorDiscreteTerm
            (fs.get selected) (∏ i : Fin fs.length, tuple i) t n)

/-- The finite selected-group block sum is obtained from the concrete
ambient component factor list by canonical subset enumeration. -/
noncomputable def smoothHeathBrownSelectedSubsetGlobalWindowSum
    {X z : ℝ} (fs : List (SmoothHeathBrownFactor X))
    (I : Finset (Fin fs.length)) (selected : Fin fs.length)
    (hselected : selected ∈ I)
    (ω : Fin fs.length → ℕ → ℂ) (q a : ℕ) (t x y : ℝ) : ℂ :=
  smoothHeathBrownSelectedGroupGlobalWindowSum (z := z)
    (smoothHeathBrownSelectedGroupFactorList fs I)
    (Fin.cast (smoothHeathBrownSelectedGroupFactorList_length fs I).symm
      ((smoothGroupSubsetFinEquiv I).symm ⟨selected, hselected⟩))
    (fun j n => ω
      ((smoothGroupSubsetFinEquiv I
        (Fin.cast (smoothHeathBrownSelectedGroupFactorList_length fs I) j)).val) n)
    q a t x y

/-- Source assembly for the theta/logarithm branch of `lda:small-group`.
The ambient factor indices in the source grouping are canonically enumerated
as the concrete selected-group list.  The selected ambient theta or
normalized-logarithm tag is transported to that list, which discharges the
free-factor hypothesis of the checked periodic log-decay estimate.  The
Möbius tag is intentionally excluded and remains on the separate MUF route. -/
theorem smoothHeathBrownSelectedSubset_thetaLog_globalWindow_logDecay
    {X z B K D L T0 t x y : ℝ}
    {fs : List (SmoothHeathBrownFactor X)}
    (I : Finset (Fin fs.length)) (selected : Fin fs.length)
    (hselected : selected ∈ I) (hIcard : I.card ≤ 20)
    {q a : ℕ}
    (hX : 3 ≤ X)
    (hbranch : (∃ j : SmoothHeathBrownScaleIndex X,
        fs.get selected = .theta j) ∨
      (∃ j : SmoothHeathBrownScaleIndex X,
        fs.get selected = .logarithm j))
    (hB : 0 < B) (hK : 0 < K) (hD : 2 * K + 10 ≤ D)
    (hlog : 2 ≤ Real.log X)
    (hq : 0 < q) (hqLog : (q : ℝ) ≤ (Real.log X) ^ B)
    (hqLarge : (2 / (1 / 400 : ℝ)) *
      Real.log (logAbsorptionM (1 / 400) B) ≤ Real.log X)
    (hT0Eq : T0 = (Real.log X) ^ D / 2)
    (hT0t : T0 ≤ |t|) (htX : |t| ≤ X)
    (hXscale : (2 : ℝ) ^ 200 ≤ X)
    (hNlower : X ^ (1 / 100 : ℝ) ≤
      smoothHeathBrownFactorScale (fs.get selected))
    (hNupper : smoothHeathBrownFactorScale (fs.get selected) ≤
      (2 : ℝ) ^ 11 * Real.sqrt X)
    (h : ℤ) (ω : Fin fs.length → ℕ → ℂ)
    (hω : ∀ i n, ‖ω i n‖ ≤ 1)
    (hL : L = (2 : ℝ) ^ h *
      (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)))
    (hh : -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ))
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hpolyLarge : (2 / periodicLogPhaseSaving (1 / 200) 1) *
      Real.log (2 * smoothHeathBrownFreeFactorBlockConstant
          (fs.get selected) *
        logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) ≤
          Real.log X)
    (htailLarge : (2 * Real.sqrt 2 *
      smoothHeathBrownFreeFactorBlockConstant (fs.get selected)) ^
        (1 / 5 : ℝ) ≤ Real.log X) :
    ‖smoothHeathBrownSelectedSubsetGlobalWindowSum (z := z)
      fs I selected hselected ω q a t x y‖ ≤
      Real.sqrt L * (Real.log X) ^ (-K) := by
  classical
  let grouped := smoothHeathBrownSelectedGroupFactorList fs I
  let hlen : grouped.length = I.card :=
    smoothHeathBrownSelectedGroupFactorList_length fs I
  let e := smoothGroupSubsetFinEquiv I
  let selectedGroup : Fin grouped.length :=
    Fin.cast hlen.symm (e.symm ⟨selected, hselected⟩)
  let groupWeight : Fin grouped.length → ℕ → ℂ := fun j n =>
    ω (e (Fin.cast hlen j)).val n
  have hselectedFactor : grouped.get selectedGroup = fs.get selected := by
    simpa [grouped, selectedGroup, hlen, e] using
      smoothHeathBrownSelectedGroupFactorList_selected_get
        fs I selected hselected
  have hbranchGroup :
      (∃ j : SmoothHeathBrownScaleIndex X,
        grouped.get selectedGroup = .theta j) ∨
      (∃ j : SmoothHeathBrownScaleIndex X,
        grouped.get selectedGroup = .logarithm j) := by
    rcases hbranch with htheta | hlogarithm
    · rcases htheta with ⟨j, hj⟩
      exact Or.inl ⟨j, hselectedFactor.trans hj⟩
    · rcases hlogarithm with ⟨j, hj⟩
      exact Or.inr ⟨j, hselectedFactor.trans hj⟩
  have hfree : ∀ j : SmoothHeathBrownScaleIndex X,
      grouped.get selectedGroup ≠ .mobius j := by
    intro j hmobius
    rcases hbranchGroup with ⟨jθ, htheta⟩ | ⟨jlog, hlogarithm⟩
    · rw [htheta] at hmobius
      cases hmobius
    · rw [hlogarithm] at hmobius
      cases hmobius
  have hNlowerGroup : X ^ (1 / 100 : ℝ) ≤
      smoothHeathBrownFactorScale (grouped.get selectedGroup) := by
    rw [hselectedFactor]
    exact hNlower
  have hNupperGroup :
      smoothHeathBrownFactorScale (grouped.get selectedGroup) ≤
        (2 : ℝ) ^ 11 * Real.sqrt X := by
    rw [hselectedFactor]
    exact hNupper
  have hfactorGet (j : Fin I.card) :
      grouped.get (Fin.cast hlen.symm j) = fs.get (e j).val := by
    simpa [grouped, hlen, e] using
      smoothHeathBrownSelectedGroupFactorList_get fs I j
  have hscaleProduct :
      (∏ j : Fin grouped.length,
        smoothHeathBrownFactorScale (grouped.get j)) =
        ∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i) := by
    calc
      (∏ j : Fin grouped.length,
          smoothHeathBrownFactorScale (grouped.get j)) =
          ∏ j : Fin I.card,
            smoothHeathBrownFactorScale
              (grouped.get (Fin.cast hlen.symm j)) := by
        symm
        simpa using
          (Equiv.prod_comp ((finCongr hlen).symm)
            (fun j : Fin grouped.length =>
              smoothHeathBrownFactorScale (grouped.get j)))
      _ = ∏ j : Fin I.card,
            smoothHeathBrownFactorScale (fs.get (e j).val) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hfactorGet]
      _ = ∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i) :=
        smoothGroupSubsetScaleProductReindex I
          (fun i => smoothHeathBrownFactorScale (fs.get i))
  have hLgroup : L = (2 : ℝ) ^ h *
      (∏ j : Fin grouped.length,
        smoothHeathBrownFactorScale (grouped.get j)) := by
    calc
      L = (2 : ℝ) ^ h *
          (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)) := hL
      _ = (2 : ℝ) ^ h *
          (∏ j : Fin grouped.length,
            smoothHeathBrownFactorScale (grouped.get j)) := by
        rw [hscaleProduct]
  have hhgroup : -(grouped.length : ℤ) ≤ h ∧
      h < (grouped.length : ℤ) := by
    simpa [hlen] using hh
  have hweight : ∀ j n, ‖groupWeight j n‖ ≤ 1 := by
    intro j n
    exact hω (e (Fin.cast hlen j)).val n
  have hgroupCard : grouped.length ≤ 20 := by
    simpa [hlen] using hIcard
  have hpolyLargeGroup :
      (2 / periodicLogPhaseSaving (1 / 200) 1) *
        Real.log (2 * smoothHeathBrownFreeFactorBlockConstant
          (grouped.get selectedGroup) *
          logAbsorptionM (periodicLogPhaseSaving (1 / 200) 1) K) ≤
        Real.log X := by
    rw [hselectedFactor]
    exact hpolyLarge
  have htailLargeGroup :
      (2 * Real.sqrt 2 *
        smoothHeathBrownFreeFactorBlockConstant
          (grouped.get selectedGroup)) ^ (1 / 5 : ℝ) ≤ Real.log X := by
    rw [hselectedFactor]
    exact htailLarge
  have hdecay := smoothHeathBrownFreeFactor_selectedGroupGlobalWindow_logDecay_of_factors
    (hk := hgroupCard) (selected := selectedGroup) (X := X) (z := z)
    (B := B) (K := K) (D := D) (L := L) (T0 := T0) (t := t)
    (x := x) (y := y) (fs := grouped) (q := q) (a := a)
    hX hfree hB hK hD hlog hq hqLog hqLarge hT0Eq hT0t htX hXscale
    hNlowerGroup hNupperGroup h groupWeight hweight hLgroup hhgroup hx hxy
    hpolyLargeGroup htailLargeGroup
  have hsum :
      smoothHeathBrownSelectedSubsetGlobalWindowSum (z := z)
          fs I selected hselected ω q a t x y =
        smoothHeathBrownSelectedGroupGlobalWindowSum (z := z)
          grouped selectedGroup groupWeight q a t x y := by
    simp [smoothHeathBrownSelectedSubsetGlobalWindowSum,
      smoothHeathBrownSelectedGroupFactorList, grouped, selectedGroup,
      groupWeight, hlen, e]
  rw [hsum]
  simpa [smoothHeathBrownSelectedGroupGlobalWindowSum] using hdecay

#print axioms smoothHeathBrownSelectedSubset_thetaLog_globalWindow_logDecay

#print axioms smoothHeathBrownSelectedGroupFactorList_length
#print axioms smoothHeathBrownSelectedGroupFactorList_get
#print axioms smoothHeathBrownSelectedGroupFactorList_selected_get
#print axioms smoothHeathBrownSelectedGroupFactorList_selected_branch

/-- Sum the fixed-product free-factor estimate over a finite family of the
remaining factor tuples.  The local interval may depend on the tuple, as it
does after fixing the other elementary arguments in the source proof.  The
source outer-factor mass `5^19 * sqrt(P/L)` cancels the selected scale and
leaves the exact `sqrt P` normalization. -/
theorem smoothHeathBrownFreeFactor_outerFactorMassSummation
    {ι : Type*} {alpha A X L T0 t : ℝ} {q a : ℕ}
    (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (P : ℝ) (hP : 0 ≤ P)
    (J : Finset ι) (weight : ι → ℂ) (otherProduct : ι → ℕ)
    (x y : ι → ℝ)
    (hinterval : ∀ i ∈ J,
      L ≤ x i ∧ x i ≤ y i ∧ y i ≤ 2 * L)
    (hmass : (∑ i ∈ J, ‖weight i‖) ≤
      5 ^ 19 * Real.sqrt (P / L)) :
    ‖∑ i ∈ J, weight i *
        (∑ n ∈ (Finset.Ioc (Nat.floor (x i)) (Nat.floor (y i))).filter
            (fun n => otherProduct i * n ≡ a [MOD q]),
          smoothHeathBrownFreeFactorDiscreteTerm f (otherProduct i) t n)‖ ≤
      5 ^ 19 * smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A * Real.sqrt P *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := by
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hLlower
  have hcost : 0 ≤ smoothHeathBrownFreeFactorIntervalCost f := by
    cases f <;> simp [smoothHeathBrownFreeFactorIntervalCost]
  have hphase : 0 ≤ periodicLogPhaseConstant alpha A := by
    unfold periodicLogPhaseConstant
    exact le_trans (by norm_num) (le_max_left _ _)
  have herror : 0 ≤
      X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ) := by
    exact add_nonneg (Real.rpow_nonneg hXpos.le _)
      (Real.rpow_nonneg (by linarith : 0 ≤ T0) _)
  let C : ℝ := smoothHeathBrownFreeFactorIntervalCost f *
    periodicLogPhaseConstant alpha A * Real.sqrt L *
      (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hcost hphase) (Real.sqrt_nonneg _)) herror
  have hlocal : ∀ i ∈ J,
      ‖∑ n ∈ (Finset.Ioc (Nat.floor (x i)) (Nat.floor (y i))).filter
          (fun n => otherProduct i * n ≡ a [MOD q]),
        smoothHeathBrownFreeFactorDiscreteTerm f (otherProduct i) t n‖ ≤ C := by
    intro i hi
    have h := smoothHeathBrownFreeFactor_productResidueInterval_bound_noWitness
      (alpha := alpha) (A := A) (X := X) (L := L) (T0 := T0)
      (t := t) (x := x i) (y := y i) (q := q) (a := a)
      (m := otherProduct i)
      hX f hfree halpha halpha1 hA hLlower hLupper hq hqBound
      hT0 hT0t htX (hinterval i hi).1 (hinterval i hi).2.1
      (hinterval i hi).2.2
    simpa [C] using h
  calc
    ‖∑ i ∈ J, weight i *
        (∑ n ∈ (Finset.Ioc (Nat.floor (x i)) (Nat.floor (y i))).filter
            (fun n => otherProduct i * n ≡ a [MOD q]),
          smoothHeathBrownFreeFactorDiscreteTerm f (otherProduct i) t n)‖ ≤
      ∑ i ∈ J, ‖weight i *
        (∑ n ∈ (Finset.Ioc (Nat.floor (x i)) (Nat.floor (y i))).filter
            (fun n => otherProduct i * n ≡ a [MOD q]),
          smoothHeathBrownFreeFactorDiscreteTerm f (otherProduct i) t n)‖ :=
            norm_sum_le _ _
    _ ≤ ∑ i ∈ J, ‖weight i‖ * C := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hlocal i hi) (norm_nonneg _)
    _ = (∑ i ∈ J, ‖weight i‖) * C := by rw [Finset.sum_mul]
    _ ≤ (5 ^ 19 * Real.sqrt (P / L)) * C :=
      mul_le_mul_of_nonneg_right hmass hC
    _ = 5 ^ 19 * smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A * Real.sqrt P *
          (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
      have hroot : Real.sqrt (P / L) * Real.sqrt L = Real.sqrt P := by
        rw [Real.sqrt_div hP]
        exact div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 hLpos))
      dsimp [C]
      calc
        _ = 5 ^ 19 * smoothHeathBrownFreeFactorIntervalCost f *
            periodicLogPhaseConstant alpha A *
              (Real.sqrt (P / L) * Real.sqrt L) *
                (X ^ (-(periodicLogPhaseSaving alpha A)) +
                  T0 ^ (-1 / 2 : ℝ)) := by ring
        _ = 5 ^ 19 * smoothHeathBrownFreeFactorIntervalCost f *
            periodicLogPhaseConstant alpha A * Real.sqrt P *
              (X ^ (-(periodicLogPhaseSaving alpha A)) +
                T0 ^ (-1 / 2 : ℝ)) := by rw [hroot]

#print axioms smoothHeathBrownFreeFactor_outerFactorMassSummation

/-- Source-shaped outer sum for one selected theta/logarithmic factor.
The selected coordinate is pinned to `1`; all other coordinates range over
their exact finite supports.  The complementary-factor mass is derived from
the individual `5 * sqrt (N i)` inputs, so the resulting scale is the product
of all factor scales.  An empty residue filter contributes zero, and a
nonempty one supplies its own representative.  The interval restrictions and
local periodic cancellation estimate remain explicit. -/
theorem smoothHeathBrownFreeFactor_outerFactorMassSummation_of_factorMass
    {k : ℕ} (hk : k ≤ 20) (selected : Fin k)
    {alpha A X T0 t : ℝ} {q a : ℕ}
    (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hselectedLower : X ^ alpha ≤ smoothHeathBrownFactorScale f)
    (hselectedUpper : smoothHeathBrownFactorScale f ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (N : Fin k → ℝ) (S : Fin k → Finset ℕ) (aFactor : Fin k → ℕ → ℂ)
    (hN : ∀ i, 0 < N i)
    (hSelectedScaleEq : N selected = smoothHeathBrownFactorScale f)
    (hMass : ∀ i, i ≠ selected →
      (∑ n ∈ S i, ‖aFactor i n‖) ≤ 5 * Real.sqrt (N i))
    (x y : (Fin k → ℕ) → ℝ)
    (hinterval : ∀ tuple ∈ Fintype.piFinset
        (fun i : Fin k => if i = selected then ({1} : Finset ℕ) else S i),
      smoothHeathBrownFactorScale f ≤ x tuple ∧
        x tuple ≤ y tuple ∧ y tuple ≤ 2 * smoothHeathBrownFactorScale f) :
    ‖∑ tuple ∈ Fintype.piFinset
        (fun i : Fin k => if i = selected then ({1} : Finset ℕ) else S i),
        (∏ i : Fin k,
          (if i = selected then 1 else aFactor i (tuple i))) *
          (∑ n ∈ (Finset.Ioc (Nat.floor (x tuple)) (Nat.floor (y tuple))).filter
              (fun n => (∏ i : Fin k, tuple i) * n ≡ a [MOD q]),
            smoothHeathBrownFreeFactorDiscreteTerm f (∏ i : Fin k, tuple i) t n)‖ ≤
      5 ^ 19 * smoothHeathBrownFreeFactorIntervalCost f *
        periodicLogPhaseConstant alpha A *
          Real.sqrt (∏ i : Fin k, N i) *
            (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  have hP : 0 ≤ ∏ i : Fin k, N i := by
    exact le_of_lt (Finset.prod_pos fun i hi => hN i)
  have hmass := smoothHeathBrownOuterTupleMass_le
    hk selected N S aFactor hN hMass
  have hmassSource :
      (∑ tuple ∈ Fintype.piFinset
          (fun i : Fin k => if i = selected then ({1} : Finset ℕ) else S i),
        ‖∏ i : Fin k,
          (if i = selected then 1 else aFactor i (tuple i))‖) ≤
        5 ^ 19 * Real.sqrt ((∏ i : Fin k, N i) /
          smoothHeathBrownFactorScale f) := by
    simpa [hSelectedScaleEq] using hmass
  have hsum := smoothHeathBrownFreeFactor_outerFactorMassSummation
    (alpha := alpha) (A := A) (X := X)
    (L := smoothHeathBrownFactorScale f) (T0 := T0) (t := t)
    (q := q) (a := a) hX f hfree halpha halpha1 hA
    hselectedLower hselectedUpper hq hqBound hT0 hT0t htX
    (P := ∏ i : Fin k, N i) hP
    (J := Fintype.piFinset
      (fun i : Fin k => if i = selected then ({1} : Finset ℕ) else S i))
    (weight := fun tuple => ∏ i : Fin k,
      (if i = selected then 1 else aFactor i (tuple i)))
    (otherProduct := fun tuple => ∏ i : Fin k, tuple i)
    x y hinterval hmassSource
  simpa [hSelectedScaleEq] using hsum

#print axioms smoothHeathBrownFreeFactor_outerFactorMassSummation_of_factorMass

end FractionalPrimes.Literature.DirichletAdapter

end
