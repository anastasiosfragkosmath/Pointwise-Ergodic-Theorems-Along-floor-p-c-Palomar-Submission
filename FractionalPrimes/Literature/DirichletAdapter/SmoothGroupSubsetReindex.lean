module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothSmallGroupFiniteAssembly
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic

/-!
# Reindexing a selected smooth group

The grouping theorem records a group as a finite subset of the ambient factor
indices, while the finite mass transfer uses `Fin k`.  These lemmas transport
the component scale and the selected complementary mass product across that
reindexing.  They are finite identities and do not instantiate the local
short-interval cancellation estimate.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The canonical finite indexing of a selected subset by `Fin I.card`. -/
def smoothGroupSubsetFinEquiv {K : ℕ} (I : Finset (Fin K)) :
    Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv

/-- Transport an argument tuple indexed by the selected finite subset to a
tuple indexed by `Fin I.card`. -/
def smoothGroupSubsetTupleEquiv {K : ℕ} (I : Finset (Fin K)) :
    (Fin I.card → ℕ) ≃ (I → ℕ) where
  toFun m i := m ((smoothGroupSubsetFinEquiv I).symm i)
  invFun m j := m (smoothGroupSubsetFinEquiv I j)
  left_inv m := by
    funext j
    simp
  right_inv m := by
    funext i
    simp

/-- The finite convolution sum associated with a group indexed by its
ambient subset. -/
noncomputable def smoothGroupSubsetConvolutionSum
    {K : ℕ} (I : Finset (Fin K)) (S : Fin K → Finset ℕ)
    (a : Fin K → ℕ → ℂ) (x y : ℝ) : ℂ :=
  ∑ m ∈ (Fintype.piFinset (fun i : I => S i.val)).filter
      (fun m => x < (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ∧
        (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ≤ y),
    ∏ i : I, a i.val (m i)

/-- The same finite convolution sum after reindexing its factors by `Fin k`. -/
noncomputable def smoothGroupFinConvolutionSum
    {k : ℕ} (S : Fin k → Finset ℕ) (a : Fin k → ℕ → ℂ)
    (x y : ℝ) : ℂ :=
  ∑ m ∈ (Fintype.piFinset S).filter
      (fun m => x < (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ∧
        (((∏ i : Fin k, m i : ℕ) : ℕ) : ℝ) ≤ y),
    ∏ i : Fin k, a i (m i)

/-- The group convolution sum is unchanged by the canonical finite-subset
reindexing.  This is the exact tuple transport needed before applying the
`Fin k` wide-support transfer. -/
theorem smoothGroupSubsetConvolutionSumReindex
    {K : ℕ} (I : Finset (Fin K)) (S : Fin K → Finset ℕ)
    (a : Fin K → ℕ → ℂ) (x y : ℝ) :
    smoothGroupFinConvolutionSum
        (fun j : Fin I.card => S (smoothGroupSubsetFinEquiv I j).val)
        (fun j n => a (smoothGroupSubsetFinEquiv I j).val n) x y =
      smoothGroupSubsetConvolutionSum I S a x y := by
  classical
  let e := smoothGroupSubsetFinEquiv I
  let E := smoothGroupSubsetTupleEquiv I
  let SFin : Fin I.card → Finset ℕ := fun j => S (e j).val
  let SSub : I → Finset ℕ := fun i => S i.val
  let aFin : Fin I.card → ℕ → ℂ := fun j n => a (e j).val n
  let PF : (Fin I.card → ℕ) → Prop := fun m =>
    x < (((∏ j : Fin I.card, m j : ℕ) : ℕ) : ℝ) ∧
      (((∏ j : Fin I.card, m j : ℕ) : ℕ) : ℝ) ≤ y
  let PS : (I → ℕ) → Prop := fun m =>
    x < (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ∧
      (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ≤ y
  let CF : (Fin I.card → ℕ) → ℂ := fun m => ∏ j, aFin j (m j)
  let CS : (I → ℕ) → ℂ := fun m => ∏ i : I, a i.val (m i)
  have htupleProduct (m : Fin I.card → ℕ) :
      (∏ i : I, E m i) = ∏ j : Fin I.card, m j := by
    simpa [E, smoothGroupSubsetTupleEquiv, e] using
      (Equiv.prod_comp e.symm m)
  have hcoefficientProduct (m : Fin I.card → ℕ) :
      CS (E m) = CF m := by
    let g : Fin I.card → ℂ := fun j => a (e j).val (m j)
    calc
      CS (E m) = ∏ i : I, g (e.symm i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [g, E, smoothGroupSubsetTupleEquiv, e]
      _ = ∏ j : Fin I.card, g j := Equiv.prod_comp e.symm g
      _ = CF m := by simp [CF, g, aFin]
  change
    (∑ m ∈ (Fintype.piFinset SFin).filter PF, CF m) =
      ∑ m ∈ (Fintype.piFinset SSub).filter PS, CS m
  refine Finset.sum_bij (fun m _ => E m) ?_ ?_ ?_ ?_
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmSupport, hmProduct⟩
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro i
      have hcoord := (Fintype.mem_piFinset.mp hmSupport) (e.symm i)
      simpa [E, SFin, SSub, smoothGroupSubsetTupleEquiv, e] using hcoord
    · change x < (((∏ j : Fin I.card, m j : ℕ) : ℕ) : ℝ) ∧
        (((∏ j : Fin I.card, m j : ℕ) : ℕ) : ℝ) ≤ y at hmProduct
      change x < (((∏ i : I, E m i : ℕ) : ℕ) : ℝ) ∧
        (((∏ i : I, E m i : ℕ) : ℕ) : ℝ) ≤ y
      rw [htupleProduct m]
      exact hmProduct
  · intro m₁ hm₁ m₂ hm₂ heq
    exact E.injective heq
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmSupport, hmProduct⟩
    refine ⟨E.symm m, ?_, E.apply_symm_apply m⟩
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro j
      have hcoord := (Fintype.mem_piFinset.mp hmSupport) (e j)
      simpa [SFin, SSub, E, smoothGroupSubsetTupleEquiv, e] using hcoord
    · have hproductBack : (∏ i : I, m i) =
          ∏ j : Fin I.card, E.symm m j := by
        calc
          (∏ i : I, m i) = ∏ i : I, E (E.symm m) i := by
            apply Finset.prod_congr rfl
            intro i hi
            exact (congrFun (E.apply_symm_apply m) i).symm
          _ = ∏ j : Fin I.card, E.symm m j := htupleProduct (E.symm m)
      change x < (((∏ j : Fin I.card, E.symm m j : ℕ) : ℕ) : ℝ) ∧
        (((∏ j : Fin I.card, E.symm m j : ℕ) : ℕ) : ℝ) ≤ y
      change x < (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ∧
        (((∏ i : I, m i : ℕ) : ℕ) : ℝ) ≤ y at hmProduct
      rw [← hproductBack]
      exact hmProduct
  · intro m hm
    exact (hcoefficientProduct m).symm

/-- Apply the checked wide-support finite transfer directly to a selected
group represented as an ambient subset.  The selected factor's local
cancellation estimate remains the explicit `hShort` premise. -/
theorem smoothGroupSubsetWideSupportFiniteTransfer
    {K : ℕ} (I : Finset (Fin K)) (selected : Fin K)
    (hselected : selected ∈ I) (hcount : I.card ≤ 20) (h : ℤ)
    (N : Fin K → ℝ) (L ε x y : ℝ)
    (S : Fin K → Finset ℕ) (a : Fin K → ℕ → ℂ)
    (hN : ∀ i ∈ I, 0 < N i)
    (hL : L = (2 : ℝ) ^ h * (∏ i ∈ I, N i))
    (hh : -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ))
    (hε : 0 ≤ ε) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hSelected : S selected =
      FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
          (N selected / 2) ∪
        FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
          (N selected))
    (hPositive : ∀ i ∈ I, ∀ n, n ∈ S i → 0 < n)
    (hOtherMass : ∀ i ∈ I.erase selected,
      (∑ n ∈ S i, ‖a i n‖) ≤ 5 * Real.sqrt (N i))
    (hShort : ∀ M : ℝ, (M = N selected / 2 ∨ M = N selected) →
      ∀ u v : ℝ, 0 ≤ u →
        Set.Ioc u v ⊆ Set.Ioc M (2 * M) →
        ‖∑ n ∈
            FractionalPrimes.Literature.Twisted.factorExtractionRealInterval
              u v, a selected n‖ ≤ ε * Real.sqrt M) :
    ‖smoothGroupSubsetConvolutionSum I S a x y‖ ≤
      (2 : ℝ) ^ 11 * 5 ^ 19 * ε * Real.sqrt L := by
  let e := smoothGroupSubsetFinEquiv I
  let selectedFin := e.symm ⟨selected, hselected⟩
  let NFin : Fin I.card → ℝ := fun j => N (e j).val
  let SFin : Fin I.card → Finset ℕ := fun j => S (e j).val
  let aFin : Fin I.card → ℕ → ℂ := fun j n => a (e j).val n
  have hNFin : ∀ j, 0 < NFin j := by
    intro j
    exact hN (e j).val (e j).property
  have hScaleProductFin :
      (∏ j : Fin I.card, NFin j) = ∏ i ∈ I, N i := by
    calc
      (∏ j : Fin I.card, NFin j) = ∏ i : I, N i.val :=
        Equiv.prod_comp e (fun i : I => N i.val)
      _ = ∏ i ∈ I, N i := Finset.prod_coe_sort I N
  have hLFin : L = (2 : ℝ) ^ h * (∏ j : Fin I.card, NFin j) := by
    calc
      L = (2 : ℝ) ^ h * (∏ i ∈ I, N i) := hL
      _ = (2 : ℝ) ^ h * (∏ j : Fin I.card, NFin j) := by
        rw [hScaleProductFin]
  have hSelectedScale : NFin selectedFin = N selected := by
    simp [NFin, selectedFin, e]
  have hSelectedIndex : (e selectedFin).val = selected := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨selected, hselected⟩)
  have hSelectedFin : SFin selectedFin =
      FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
          (NFin selectedFin / 2) ∪
        FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
          (NFin selectedFin) := by
    calc
      SFin selectedFin = S selected := by simp [SFin, selectedFin, e]
      _ =
          FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
              (N selected / 2) ∪
            FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
              (N selected) := hSelected
      _ =
          FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
              (NFin selectedFin / 2) ∪
            FractionalPrimes.Literature.Twisted.factorExtractionDyadicInterval
              (NFin selectedFin) := by rw [← hSelectedScale]
  have hPositiveFin : ∀ j n, n ∈ SFin j → 0 < n := by
    intro j n hn
    exact hPositive (e j).val (e j).property n (by simpa [SFin] using hn)
  have hOtherMassFin : ∀ j ∈ Finset.univ.erase selectedFin,
      (∑ n ∈ SFin j, ‖aFin j n‖) ≤ 5 * Real.sqrt (NFin j) := by
    intro j hj
    have hmem : (e j).val ∈ I.erase selected := by
      refine Finset.mem_erase.mpr ⟨?_, (e j).property⟩
      intro hval
      have heq : e j = (⟨selected, hselected⟩ : I) := Subtype.ext hval
      have hidx : j = selectedFin := by
        calc
          j = e.symm (e j) := by simp [e]
          _ = selectedFin := congrArg e.symm heq
      exact (Finset.mem_erase.mp hj).1 hidx
    simpa [SFin, aFin, NFin, e] using hOtherMass (e j).val hmem
  have hShortFin : ∀ M : ℝ, (M = NFin selectedFin / 2 ∨
      M = NFin selectedFin) → ∀ u v : ℝ, 0 ≤ u →
        Set.Ioc u v ⊆ Set.Ioc M (2 * M) →
        ‖∑ n ∈
            FractionalPrimes.Literature.Twisted.factorExtractionRealInterval
              u v, aFin selectedFin n‖ ≤ ε * Real.sqrt M := by
    intro M hM u v hu hI
    have hMsource : M = N selected / 2 ∨ M = N selected := by
      simpa [hSelectedScale] using hM
    simpa [aFin, hSelectedIndex] using hShort M hMsource u v hu hI
  have hFinite := smoothGroupWideSupportFiniteTransfer
    (k := I.card) hcount selectedFin h NFin L ε x y SFin aFin hNFin hLFin
    hh hε hx hxy hSelectedFin hPositiveFin hOtherMassFin hShortFin
  have hReindex := smoothGroupSubsetConvolutionSumReindex I S a x y
  calc
    ‖smoothGroupSubsetConvolutionSum I S a x y‖ =
        ‖smoothGroupFinConvolutionSum
          (fun j : Fin I.card => S (e j).val)
          (fun j n => a (e j).val n) x y‖ := by
            rw [← hReindex]
    _ ≤ (2 : ℝ) ^ 11 * 5 ^ 19 * ε * Real.sqrt L := by
      simpa [smoothGroupFinConvolutionSum, SFin, aFin, e] using hFinite

/-- Reindex the product of all factor scales in a selected group. -/
theorem smoothGroupSubsetScaleProductReindex
    {K : ℕ} (I : Finset (Fin K)) (N : Fin K → ℝ) :
    (∏ j : Fin I.card, N (smoothGroupSubsetFinEquiv I j).val) =
      ∏ i ∈ I, N i := by
  calc
    (∏ j : Fin I.card, N (smoothGroupSubsetFinEquiv I j).val) =
        ∏ i : I, N i.val :=
      Equiv.prod_comp (smoothGroupSubsetFinEquiv I) (fun i : I => N i.val)
    _ = ∏ i ∈ I, N i := Finset.prod_coe_sort I N

/-- Reindex the absolute masses of all factors except the selected one. -/
theorem smoothGroupSubsetEraseMassProductReindex
    {K : ℕ} (I : Finset (Fin K)) (selected : Fin K)
    (hselected : selected ∈ I) (mass : Fin K → ℝ) :
    (∏ j ∈ (Finset.univ : Finset (Fin I.card)).erase
        ((smoothGroupSubsetFinEquiv I).symm ⟨selected, hselected⟩),
      mass (smoothGroupSubsetFinEquiv I j).val) =
      ∏ i ∈ I.erase selected, mass i := by
  classical
  let e := smoothGroupSubsetFinEquiv I
  let selectedFin := e.symm ⟨selected, hselected⟩
  refine Finset.prod_bij (fun j _ => (e j).val) ?_ ?_ ?_ ?_
  · intro j hj
    have hne : (e j).val ≠ selected := by
      intro hval
      have heq : e j = (⟨selected, hselected⟩ : I) := Subtype.ext hval
      have hidx : j = selectedFin := by
        calc
          j = e.symm (e j) := by simp [e]
          _ = selectedFin := congrArg e.symm heq
      exact (Finset.mem_erase.mp hj).1 hidx
    exact Finset.mem_erase.mpr ⟨hne, (e j).property⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    apply e.injective
    exact Subtype.ext heq
  · intro b hb
    have hb' := Finset.mem_erase.mp hb
    let j := e.symm ⟨b, hb'.2⟩
    refine ⟨j, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · intro hj
      have heq : e j = (⟨b, hb'.2⟩ : I) := e.apply_symm_apply _
      rw [hj] at heq
      have hval := congrArg Subtype.val heq
      have hval' : selected = b := by simpa [selectedFin, e] using hval
      exact hb'.1 hval'.symm
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb'.2⟩)
  · intro j hj
    rfl

/-- The finite selected-mass estimate applies directly to a group presented
as a subset of ambient factors.  Its block scale is the subset product, and
the local analytic estimate is not part of this arithmetic statement. -/
theorem smoothGroupSubsetSelectedMassScale
    {K : ℕ} (I : Finset (Fin K)) (selected : Fin K)
    (hselected : selected ∈ I) (hcount : I.card ≤ 20) (h : ℤ)
    (N mass : Fin K → ℝ) (L : ℝ)
    (hN : ∀ i ∈ I, 0 < N i)
    (hmass : ∀ i ∈ I, 0 ≤ mass i)
    (hmassBound : ∀ i ∈ I, i ≠ selected →
      mass i ≤ 5 * Real.sqrt (N i))
    (hL : L = (2 : ℝ) ^ h * (∏ i ∈ I, N i))
    (hh : -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ)) :
    Real.sqrt (N selected) *
        (∏ i ∈ I.erase selected, mass i) ≤
      (2 : ℝ) ^ 10 * 5 ^ 19 * Real.sqrt L := by
  let e := smoothGroupSubsetFinEquiv I
  let selectedFin := e.symm ⟨selected, hselected⟩
  let NFin : Fin I.card → ℝ := fun j => N (e j).val
  let massFin : Fin I.card → ℝ := fun j => mass (e j).val
  have hNFin : ∀ j, 0 < NFin j := by
    intro j
    exact hN (e j).val (e j).property
  have hmassFin : ∀ j, 0 ≤ massFin j := by
    intro j
    exact hmass (e j).val (e j).property
  have hmassBoundFin : ∀ j, j ≠ selectedFin →
      massFin j ≤ 5 * Real.sqrt (NFin j) := by
    intro j hj
    have hne : (e j).val ≠ selected := by
      intro hEq
      apply hj
      apply e.injective
      apply Subtype.ext
      simpa [selectedFin] using hEq
    exact hmassBound (e j).val (e j).property hne
  have hScaleProduct := smoothGroupSubsetScaleProductReindex I N
  have hScaleProductFin :
      (∏ j : Fin I.card, NFin j) = ∏ i ∈ I, N i := by
    simpa [NFin, e] using hScaleProduct
  have hLFin : L = (2 : ℝ) ^ h * (∏ j : Fin I.card, NFin j) := by
    calc
      L = (2 : ℝ) ^ h * (∏ i ∈ I, N i) := hL
      _ = (2 : ℝ) ^ h * (∏ j : Fin I.card, NFin j) := by
        rw [hScaleProductFin]
  have hFinite := smoothGroupSelectedMassScale hcount selectedFin h
    NFin massFin L hNFin hmassFin hmassBoundFin hLFin hh
  have hSelectedScale : NFin selectedFin = N selected := by
    simp [NFin, selectedFin, e]
  have hEraseProduct :=
    smoothGroupSubsetEraseMassProductReindex I selected hselected mass
  calc
    Real.sqrt (N selected) * (∏ i ∈ I.erase selected, mass i) =
        Real.sqrt (NFin selectedFin) *
          (∏ j ∈ (Finset.univ : Finset (Fin I.card)).erase selectedFin,
            massFin j) := by
          rw [hSelectedScale]
          simpa [massFin, e, selectedFin] using congrArg
            (fun z : ℝ => Real.sqrt (N selected) * z) hEraseProduct.symm
    _ ≤ (2 : ℝ) ^ 10 * 5 ^ 19 * Real.sqrt L := hFinite

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothGroupSubsetScaleProductReindex
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothGroupSubsetConvolutionSumReindex
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothGroupSubsetWideSupportFiniteTransfer
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothGroupSubsetEraseMassProductReindex
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothGroupSubsetSelectedMassScale
