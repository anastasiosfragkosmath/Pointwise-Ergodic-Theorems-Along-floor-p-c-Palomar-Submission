module

public import FractionalPrimes.Literature.Hyperbola.Cells
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Set.OrdConnectedLinear

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

open Set HyperbolaGeometricData

/-- The points of the hyperbola strip whose slope lies in the selected
rational cell. -/
def cellLinearSlice (g : HyperbolaGeometricData) (a q : ℕ) : Set (ℤ × ℤ) :=
  {p | p ∈ g.lattice ∧
    (p.2 : ℝ) / (p.1 : ℝ) ∈ positiveRationalCell g a q}

/-- The part of a cell slice on the line `q*n+a*m=c`. -/
def cellLinearSliceOnLine (g : HyperbolaGeometricData) (a q : ℕ)
    (c : ℤ) : Set (ℤ × ℤ) :=
  {p | p ∈ cellLinearSlice g a q ∧
    (q : ℤ) * p.2 + (a : ℤ) * p.1 = c}

/-- The two linear coordinates used to describe a point in a cell slice. -/
def cellLinearCoordinate (a q : ℕ) (p : ℤ × ℤ) : ℤ :=
  (q : ℤ) * p.2 + (a : ℤ) * p.1

def cellTransverseCoordinate (a q : ℕ) (p : ℤ × ℤ) : ℤ :=
  (q : ℤ) * p.2 - (a : ℤ) * p.1

/-- A progression on a fixed line, indexed over a finite integer interval.
Using an integer interval records the endpoints exactly and also permits an
empty progression when the lower endpoint exceeds the upper endpoint. -/
def cellLatticeIccProgression (base : ℤ × ℤ) (q a : ℤ)
    (lo hi : ℤ) : Set (ℤ × ℤ) :=
  {p | ∃ j ∈ Set.Icc lo hi,
    p = (base.1 + j * q, base.2 - j * a)}

/-- Every integer-interval progression is finite. -/
theorem cellLatticeIccProgression_finite (base : ℤ × ℤ) (q a : ℤ)
    (lo hi : ℤ) : (cellLatticeIccProgression base q a lo hi).Finite := by
  classical
  have heq : cellLatticeIccProgression base q a lo hi =
      (fun j : ℤ => (base.1 + j * q, base.2 - j * a)) '' Set.Icc lo hi := by
    ext p
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
  rw [heq]
  have hIcc : (Set.Icc lo hi).Finite := Set.finite_Icc lo hi
  exact hIcc.image _

private theorem cellLinearLine_parameterize
    {a q : ℕ} {c : ℤ} {p p₀ : ℤ × ℤ}
    (hcop : Nat.Coprime a q) (hq : 0 < q)
    (hp : cellLinearCoordinate a q p = c)
    (hp₀ : cellLinearCoordinate a q p₀ = c) :
    ∃ j : ℤ, p = (p₀.1 + j * (q : ℤ), p₀.2 - j * (a : ℤ)) := by
  have hqInt : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hcopInt : IsCoprime (q : ℤ) (a : ℤ) :=
    (Nat.Coprime.cast hcop).symm
  have hline : (q : ℤ) * (p.2 - p₀.2) =
      -(a : ℤ) * (p.1 - p₀.1) := by
    dsimp [cellLinearCoordinate] at hp hp₀
    linarith
  have hdiv : (q : ℤ) ∣ (a : ℤ) * (p.1 - p₀.1) := by
    refine ⟨-(p.2 - p₀.2), ?_⟩
    nlinarith [hline]
  obtain ⟨j, hj⟩ := hcopInt.dvd_of_dvd_mul_left hdiv
  have hm : p.1 - p₀.1 = (q : ℤ) * j := hj
  have hqdiff : (q : ℤ) * (p.2 - p₀.2) =
      (q : ℤ) * (-(a : ℤ) * j) := by
    calc
      (q : ℤ) * (p.2 - p₀.2) = -(a : ℤ) * (p.1 - p₀.1) := hline
      _ = -(a : ℤ) * ((q : ℤ) * j) := by rw [hm]
      _ = (q : ℤ) * (-(a : ℤ) * j) := by ring
  have hn : p.2 - p₀.2 = -(a : ℤ) * j :=
    mul_left_cancel₀ hqInt hqdiff
  refine ⟨j, Prod.ext ?_ ?_⟩
  · calc
      p.1 = p₀.1 + (p.1 - p₀.1) := by ring
      _ = p₀.1 + (q : ℤ) * j := by rw [hm]
      _ = p₀.1 + j * (q : ℤ) := by ring
  · calc
      p.2 = p₀.2 + (p.2 - p₀.2) := by ring
      _ = p₀.2 - (a : ℤ) * j := by rw [hn]; ring
      _ = p₀.2 - j * (a : ℤ) := by ring

private noncomputable def cellLineProduct (a q : ℕ) (c : ℤ) (m : ℝ) : ℝ :=
  m * ((c : ℝ) - (a : ℝ) * m) / (q : ℝ)

private theorem cellLine_slope_formula
    {a q : ℕ} {c : ℤ} {p : ℤ × ℤ}
    (hq : 0 < q) (hm : 0 < p.1)
    (hline : cellLinearCoordinate a q p = c) :
    (p.2 : ℝ) / (p.1 : ℝ) =
      (c : ℝ) / ((q : ℝ) * (p.1 : ℝ)) - (a : ℝ) / (q : ℝ) := by
  have hlineR : (c : ℝ) =
      (q : ℝ) * (p.2 : ℝ) + (a : ℝ) * (p.1 : ℝ) := by
    dsimp [cellLinearCoordinate] at hline
    exact_mod_cast hline.symm
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnum : (q : ℝ) * (p.2 : ℝ) =
      (c : ℝ) - (a : ℝ) * (p.1 : ℝ) := by linarith [hlineR]
  have hn : (p.2 : ℝ) =
      ((c : ℝ) - (a : ℝ) * (p.1 : ℝ)) / (q : ℝ) :=
    (eq_div_iff hqR).2 (by calc
      (p.2 : ℝ) * (q : ℝ) = (q : ℝ) * (p.2 : ℝ) := by ring
      _ = (c : ℝ) - (a : ℝ) * (p.1 : ℝ) := hnum)
  rw [hn]
  field_simp [hqR, hmR]

private theorem cellLine_product_formula
    {a q : ℕ} {c : ℤ} {p : ℤ × ℤ}
    (hq : 0 < q) (hline : cellLinearCoordinate a q p = c) :
    (p.1 : ℝ) * (p.2 : ℝ) =
      cellLineProduct a q c (p.1 : ℝ) := by
  have hlineR : (c : ℝ) =
      (q : ℝ) * (p.2 : ℝ) + (a : ℝ) * (p.1 : ℝ) := by
    dsimp [cellLinearCoordinate] at hline
    exact_mod_cast hline.symm
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hnum : (q : ℝ) * (p.2 : ℝ) =
      (c : ℝ) - (a : ℝ) * (p.1 : ℝ) := by linarith [hlineR]
  have hn : (p.2 : ℝ) =
      ((c : ℝ) - (a : ℝ) * (p.1 : ℝ)) / (q : ℝ) :=
    (eq_div_iff hqR).2 (by calc
      (p.2 : ℝ) * (q : ℝ) = (q : ℝ) * (p.2 : ℝ) := by ring
      _ = (c : ℝ) - (a : ℝ) * (p.1 : ℝ) := hnum)
  dsimp [cellLineProduct]
  rw [hn]
  field_simp [hqR]

private theorem cellLineProduct_sub
    (a q : ℕ) (c : ℤ) (hq : 0 < q) (x y : ℝ) :
    cellLineProduct a q c y - cellLineProduct a q c x =
      (y - x) * ((c : ℝ) - (a : ℝ) * (x + y)) / (q : ℝ) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  dsimp [cellLineProduct]
  field_simp [hqR]
  ring

private theorem cellLineProduct_mono_left
    (a q : ℕ) (c : ℤ) (hq : 0 < q) (ha : 0 < a)
    {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ (c : ℝ) / (2 * (a : ℝ))) :
    cellLineProduct a q c x ≤ cellLineProduct a q c y := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hden : 0 < 2 * (a : ℝ) := by positivity
  have hvertex' : y * (2 * (a : ℝ)) ≤ (c : ℝ) :=
    (le_div_iff₀ hden).mp hy
  have hvertex : 2 * (a : ℝ) * y ≤ (c : ℝ) := by nlinarith [hvertex']
  have haxy : (a : ℝ) * x ≤ (a : ℝ) * y :=
    mul_le_mul_of_nonneg_left hxy haR.le
  have hfactor : 0 ≤ (c : ℝ) - (a : ℝ) * (x + y) := by
    nlinarith [hvertex, haxy]
  have hdiff := cellLineProduct_sub a q c hq x y
  apply (sub_nonneg).mp
  rw [hdiff]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hxy) hfactor) hqR.le

private theorem cellLineProduct_mono_right
    (a q : ℕ) (c : ℤ) (hq : 0 < q) (ha : 0 < a)
    {x y : ℝ} (hxy : x ≤ y)
    (hx : (c : ℝ) / (2 * (a : ℝ)) < x) :
    cellLineProduct a q c y ≤ cellLineProduct a q c x := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hden : 0 < 2 * (a : ℝ) := by positivity
  have hvertex' : (c : ℝ) < x * (2 * (a : ℝ)) :=
    (div_lt_iff₀ hden).mp hx
  have hvertex : (c : ℝ) < 2 * (a : ℝ) * x := by nlinarith [hvertex']
  have haxy : (a : ℝ) * x ≤ (a : ℝ) * y :=
    mul_le_mul_of_nonneg_left hxy haR.le
  have hfactor : (c : ℝ) - (a : ℝ) * (x + y) ≤ 0 := by
    nlinarith [hvertex, haxy]
  have hdiff := cellLineProduct_sub a q c hq x y
  apply (sub_nonpos).mp
  rw [hdiff]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hfactor) hqR.le

private theorem cellLinearSlice_intermediate
    (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (c : ℤ)
    {pL p pR : ℤ × ℤ}
    (hpL : pL ∈ cellLinearSliceOnLine g a q c)
    (hpR : pR ∈ cellLinearSliceOnLine g a q c)
    (hline : cellLinearCoordinate a q p = c)
    (hm : (pL.1 : ℝ) ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ (pR.1 : ℝ))
    (hbranch :
      2 * (a : ℝ) * (pR.1 : ℝ) ≤ (c : ℝ) ∨
        (c : ℝ) < 2 * (a : ℝ) * (pL.1 : ℝ)) :
    p ∈ cellLinearSlice g a q := by
  rcases hidx.1 with ⟨hcop, hqlo, hqhi, halo, _, _⟩
  have hcellEligible : rationalCellEligible g a q := hidx.1
  have hq : 0 < q := by omega
  have ha : 0 < a := by omega
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  rcases hpL with ⟨hpLslice, hLline⟩
  rcases hpR with ⟨hpRslice, hRline⟩
  have hparams := admissibleParameterBounds g q hqlo hqhi
  have hLlat : pL ∈ g.lattice := hpLslice.1
  have hRlat : pR ∈ g.lattice := hpRslice.1
  have hLprops := hparams.lattice_point_properties pL hLlat
  have hRprops := hparams.lattice_point_properties pR hRlat
  have hmLpos : 0 < (pL.1 : ℝ) := by exact_mod_cast hLprops.1
  have hmRpos : 0 < (pR.1 : ℝ) := by exact_mod_cast hRprops.1
  have hmPos : 0 < (p.1 : ℝ) := lt_of_lt_of_le hmLpos hm.1
  have hLJ : (pL.1 : ℝ) ∈ g.J := by
    dsimp [HyperbolaGeometricData.lattice, hyperbolaLatticeSet] at hLlat
    exact hLlat.1
  have hRJ : (pR.1 : ℝ) ∈ g.J := by
    dsimp [HyperbolaGeometricData.lattice, hyperbolaLatticeSet] at hRlat
    exact hRlat.1
  have hmJ : (p.1 : ℝ) ∈ g.J :=
    g.J_orderConvex.out hLJ hRJ (by simpa [Set.mem_Icc] using hm)
  have hcL : (c : ℝ) =
      (q : ℝ) * (pL.2 : ℝ) + (a : ℝ) * (pL.1 : ℝ) := by
    exact_mod_cast hLline.symm
  have hcPos : 0 < (c : ℝ) := by
    have hnLpos : 0 < (pL.2 : ℝ) := by exact_mod_cast hLprops.2.1
    nlinarith [hcL, hqR, haR, hmLpos, hnLpos]
  have hLformula := cellLine_slope_formula hq hLprops.1 hLline
  have hRformula := cellLine_slope_formula hq hRprops.1 hRline
  have hPformula := cellLine_slope_formula hq (by exact_mod_cast
    (show 0 < p.1 by exact_mod_cast hmPos)) hline
  have hdenL : 0 < (q : ℝ) * (pL.1 : ℝ) := mul_pos hqR hmLpos
  have hden : 0 < (q : ℝ) * (p.1 : ℝ) := mul_pos hqR hmPos
  have hdenR : 0 < (q : ℝ) * (pR.1 : ℝ) := mul_pos hqR hmRpos
  have hdenLle : (q : ℝ) * (pL.1 : ℝ) ≤ (q : ℝ) * (p.1 : ℝ) :=
    mul_le_mul_of_nonneg_left hm.1 hqR.le
  have hdenleR : (q : ℝ) * (p.1 : ℝ) ≤ (q : ℝ) * (pR.1 : ℝ) :=
    mul_le_mul_of_nonneg_left hm.2 hqR.le
  have hfracLow :
      (c : ℝ) / ((q : ℝ) * (pR.1 : ℝ)) ≤
        (c : ℝ) / ((q : ℝ) * (p.1 : ℝ)) := by
    apply (div_le_div_iff₀ hdenR hden).2
    exact mul_le_mul_of_nonneg_left hdenleR hcPos.le
  have hfracHigh :
      (c : ℝ) / ((q : ℝ) * (p.1 : ℝ)) ≤
        (c : ℝ) / ((q : ℝ) * (pL.1 : ℝ)) := by
    apply (div_le_div_iff₀ hden hdenL).2
    exact mul_le_mul_of_nonneg_left hdenLle hcPos.le
  have hslopes :
      (p.2 : ℝ) / (p.1 : ℝ) ∈ Set.Icc
        ((pR.2 : ℝ) / (pR.1 : ℝ)) ((pL.2 : ℝ) / (pL.1 : ℝ)) := by
    rw [hPformula, hRformula, hLformula]
    constructor <;> linarith [hfracLow, hfracHigh]
  have hcellOrd := (positiveRationalCellPartition g).interval a q
    hcellEligible
  have hcell : (p.2 : ℝ) / (p.1 : ℝ) ∈ positiveRationalCell g a q :=
    hcellOrd.out hpRslice.2 hpLslice.2 hslopes
  have hLprod := cellLine_product_formula hq hLline
  have hRprod := cellLine_product_formula hq hRline
  have hPprod := cellLine_product_formula hq hline
  have hLstrip : g.X < cellLineProduct a q c (pL.1 : ℝ) ∧
      cellLineProduct a q c (pL.1 : ℝ) ≤ g.X + g.H := by
    constructor
    · rw [← hLprod]
      exact hLlat.2.1
    · rw [← hLprod]
      exact hLlat.2.2
  have hRstrip : g.X < cellLineProduct a q c (pR.1 : ℝ) ∧
      cellLineProduct a q c (pR.1 : ℝ) ≤ g.X + g.H := by
    constructor
    · rw [← hRprod]
      exact hRlat.2.1
    · rw [← hRprod]
      exact hRlat.2.2
  have hFstrip : g.X < cellLineProduct a q c (p.1 : ℝ) ∧
      cellLineProduct a q c (p.1 : ℝ) ≤ g.X + g.H := by
    rcases hbranch with hleft | hright
    · have hmRvert : (pR.1 : ℝ) ≤
          (c : ℝ) / (2 * (a : ℝ)) := by
        apply (le_div_iff₀ (by positivity)).2
        nlinarith [hleft]
      have hmvert : (p.1 : ℝ) ≤
          (c : ℝ) / (2 * (a : ℝ)) := le_trans hm.2 hmRvert
      have hmonoL := cellLineProduct_mono_left a q c hq ha hm.1 hmvert
      have hmonoR := cellLineProduct_mono_left a q c hq ha hm.2 hmRvert
      constructor
      · exact lt_of_lt_of_le hLstrip.1 hmonoL
      · exact le_trans hmonoR hRstrip.2
    · have hmvertL :
          (c : ℝ) / (2 * (a : ℝ)) < (pL.1 : ℝ) := by
        apply (div_lt_iff₀ (by positivity)).2
        nlinarith [hright]
      have hmvert :
          (c : ℝ) / (2 * (a : ℝ)) < (p.1 : ℝ) := lt_of_lt_of_le hmvertL hm.1
      have hmonoL := cellLineProduct_mono_right a q c hq ha hm.1 hmvertL
      have hmonoR := cellLineProduct_mono_right a q c hq ha hm.2 hmvert
      constructor
      · exact lt_of_lt_of_le hRstrip.1 hmonoR
      · exact le_trans hmonoL hLstrip.2
  have hprodFormula := hPprod
  rw [← hPprod] at hFstrip
  have hlattice : p ∈ g.lattice := by
    dsimp [HyperbolaGeometricData.lattice, hyperbolaLatticeSet]
    exact ⟨hmJ, hFstrip.1, hFstrip.2⟩
  change p ∈ g.lattice ∧
    (p.2 : ℝ) / (p.1 : ℝ) ∈ positiveRationalCell g a q
  exact ⟨hlattice, hcell⟩

private theorem finiteOrdConnectedInt_eqIcc {S : Set ℤ}
    (hfinite : S.Finite) (hne : S.Nonempty) (hord : S.OrdConnected) :
    S = Set.Icc (sInf S) (sSup S) := by
  exact (Set.Nonempty.ordConnected_iff_of_bdd hne
    hfinite.bddBelow hfinite.bddAbove).mp hord

/-- For every fixed line, a rational-cell slice is the disjoint union of at
most two finite progressions with step `(q,-a)`. Empty components are
represented by integer intervals whose lower endpoint exceeds the upper one. -/
theorem cellLinearSlices_progression_decomposition (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (c : ℤ) :
    ∃ base : ℤ × ℤ, ∃ lo₁ hi₁ lo₂ hi₂ : ℤ,
      cellLinearSliceOnLine g a q c =
        cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁ ∪
          cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂ ∧
      Disjoint
        (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁)
        (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂) ∧
      (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁).Finite ∧
      (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂).Finite := by
  classical
  rcases hidx.1 with ⟨hcop, hqlo, hqhi, halo, hamin, hamax⟩
  have hcellEligible : rationalCellEligible g a q :=
    ⟨hcop, hqlo, hqhi, halo, hamin, hamax⟩
  have hq : 0 < q := by omega
  have ha : 0 < a := by omega
  have hqIntPos : 0 < (q : ℤ) := by exact_mod_cast hq
  have hSliceFinite : (cellLinearSliceOnLine g a q c).Finite := by
    have hparams := admissibleParameterBounds g q hqlo hqhi
    apply hparams.lattice_finite.subset
    intro p hp
    exact hp.1.1
  by_cases hne : (cellLinearSliceOnLine g a q c).Nonempty
  · obtain ⟨base, hbase⟩ := hne
    let φ : ℤ → ℤ × ℤ := fun j =>
      (base.1 + j * (q : ℤ), base.2 - j * (a : ℤ))
    let P : Set ℤ := {j | φ j ∈ cellLinearSliceOnLine g a q c}
    let P₁ : Set ℤ := {j | j ∈ P ∧
      2 * (a : ℝ) * (φ j).1 ≤ (c : ℝ)}
    let P₂ : Set ℤ := {j | j ∈ P ∧
      (c : ℝ) < 2 * (a : ℝ) * (φ j).1}
    have hbaseLine : cellLinearCoordinate a q base = c := hbase.2
    have hφline (j : ℤ) : cellLinearCoordinate a q (φ j) = c := by
      dsimp [φ, cellLinearCoordinate]
      have hb := hbaseLine
      dsimp [cellLinearCoordinate] at hb
      rw [← hb]
      ring
    have hφinj : Function.Injective φ := by
      intro j k hjk
      have hfst := congrArg Prod.fst hjk
      dsimp [φ] at hfst
      have hmul : j * (q : ℤ) = k * (q : ℤ) := add_left_cancel hfst
      exact (mul_right_cancel₀ (show (q : ℤ) ≠ 0 by exact_mod_cast hq.ne') hmul)
    have hPfinite : P.Finite := by
      have hpre : (φ ⁻¹' cellLinearSliceOnLine g a q c).Finite :=
        hSliceFinite.preimage hφinj.injOn
      change (φ ⁻¹' cellLinearSliceOnLine g a q c).Finite
      exact hpre
    have hP₁finite : P₁.Finite := hPfinite.subset (by
      intro j hj
      exact hj.1)
    have hP₂finite : P₂.Finite := hPfinite.subset (by
      intro j hj
      exact hj.1)
    have hP₁Ord : P₁.OrdConnected := by
      rw [Set.ordConnected_iff]
      intro j hj k hk hjk l hl
      rcases hj with ⟨hjP, hjSide⟩
      rcases hk with ⟨hkP, hkSide⟩
      have hjmem : φ j ∈ cellLinearSliceOnLine g a q c := by simpa [P] using hjP
      have hkMem : φ k ∈ cellLinearSliceOnLine g a q c := by simpa [P] using hkP
      have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
      rcases Set.mem_Icc.mp hl with ⟨hjl, hlk⟩
      have hjml : base.1 + j * (q : ℤ) ≤ base.1 + l * (q : ℤ) :=
        by nlinarith [mul_le_mul_of_nonneg_right hjl hqIntPos.le]
      have hlmk : base.1 + l * (q : ℤ) ≤ base.1 + k * (q : ℤ) :=
        by nlinarith [mul_le_mul_of_nonneg_right hlk hqIntPos.le]
      have hm : ((φ j).1 : ℝ) ≤ ((φ l).1 : ℝ) ∧
          ((φ l).1 : ℝ) ≤ ((φ k).1 : ℝ) := by
        dsimp [φ]
        exact ⟨by exact_mod_cast hjml, by exact_mod_cast hlmk⟩
      have hmiddle : 2 * (a : ℝ) * (φ l).1 ≤ (c : ℝ) := by
        have hstep := mul_le_mul_of_nonneg_left hm.2 (by positivity :
          0 ≤ 2 * (a : ℝ))
        exact hstep.trans hkSide
      have hslice := cellLinearSlice_intermediate g a q hidx c hjmem hkMem
        (hφline l) hm (Or.inl hkSide)
      have hlP : l ∈ P := by
        change φ l ∈ cellLinearSliceOnLine g a q c
        exact ⟨hslice, hφline l⟩
      exact ⟨hlP, hmiddle⟩
    have hP₂Ord : P₂.OrdConnected := by
      rw [Set.ordConnected_iff]
      intro j hj k hk hjk l hl
      rcases hj with ⟨hjP, hjSide⟩
      rcases hk with ⟨hkP, hkSide⟩
      have hjmem : φ j ∈ cellLinearSliceOnLine g a q c := by simpa [P] using hjP
      have hkMem : φ k ∈ cellLinearSliceOnLine g a q c := by simpa [P] using hkP
      have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
      rcases Set.mem_Icc.mp hl with ⟨hjl, hlk⟩
      have hjml : base.1 + j * (q : ℤ) ≤ base.1 + l * (q : ℤ) :=
        by nlinarith [mul_le_mul_of_nonneg_right hjl hqIntPos.le]
      have hlmk : base.1 + l * (q : ℤ) ≤ base.1 + k * (q : ℤ) :=
        by nlinarith [mul_le_mul_of_nonneg_right hlk hqIntPos.le]
      have hm : ((φ j).1 : ℝ) ≤ ((φ l).1 : ℝ) ∧
          ((φ l).1 : ℝ) ≤ ((φ k).1 : ℝ) := by
        dsimp [φ]
        exact ⟨by exact_mod_cast hjml, by exact_mod_cast hlmk⟩
      have hmiddle : (c : ℝ) < 2 * (a : ℝ) * (φ l).1 := by
        have hstep := mul_le_mul_of_nonneg_left hm.1 (by positivity :
          0 ≤ 2 * (a : ℝ))
        exact lt_of_lt_of_le hjSide hstep
      have hslice := cellLinearSlice_intermediate g a q hidx c hjmem hkMem
        (hφline l) hm (Or.inr hjSide)
      have hlP : l ∈ P := by
        change φ l ∈ cellLinearSliceOnLine g a q c
        exact ⟨hslice, hφline l⟩
      exact ⟨hlP, hmiddle⟩
    have hP₁interval : ∃ lo hi : ℤ, P₁ = Set.Icc lo hi := by
      by_cases hnonempty : P₁.Nonempty
      · exact ⟨sInf P₁, sSup P₁,
          finiteOrdConnectedInt_eqIcc hP₁finite hnonempty hP₁Ord⟩
      · have hEq : P₁ = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
        exact ⟨1, 0, by simp [hEq]⟩
    have hP₂interval : ∃ lo hi : ℤ, P₂ = Set.Icc lo hi := by
      by_cases hnonempty : P₂.Nonempty
      · exact ⟨sInf P₂, sSup P₂,
          finiteOrdConnectedInt_eqIcc hP₂finite hnonempty hP₂Ord⟩
      · have hEq : P₂ = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
        exact ⟨1, 0, by simp [hEq]⟩
    obtain ⟨lo₁, hi₁, hI₁⟩ := hP₁interval
    obtain ⟨lo₂, hi₂, hI₂⟩ := hP₂interval
    have hPunion : P = P₁ ∪ P₂ := by
      ext j
      constructor
      · intro hjP
        by_cases hside : 2 * (a : ℝ) * (φ j).1 ≤ (c : ℝ)
        · left
          exact ⟨hjP, hside⟩
        · right
          exact ⟨hjP, lt_of_not_ge hside⟩
      · intro hj
        rcases hj with hj1 | hj2
        · exact hj1.1
        · exact hj2.1
    have hdecomp :
        cellLinearSliceOnLine g a q c =
          cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁ ∪
            cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂ := by
      ext p
      constructor
      · intro hp
        have hpLine : cellLinearCoordinate a q p = c := by
          simpa [cellLinearCoordinate] using hp.2
        obtain ⟨j, hpj⟩ := cellLinearLine_parameterize hcop hq hpLine hbaseLine
        have hjP : j ∈ P := by
          change (base.1 + j * (q : ℤ), base.2 - j * (a : ℤ)) ∈
            cellLinearSliceOnLine g a q c
          rw [← hpj]
          exact hp
        have hjUnion : j ∈ P₁ ∪ P₂ := by rw [← hPunion]; exact hjP
        have hjUnion' : j ∈ P₁ ∨ j ∈ P₂ := by simpa only [Set.mem_union] using hjUnion
        rcases hjUnion' with hj1 | hj2
        · left
          change ∃ k ∈ Set.Icc lo₁ hi₁,
            p = (base.1 + k * (q : ℤ), base.2 - k * (a : ℤ))
          refine ⟨j, ?_, hpj⟩
          rw [← hI₁]
          exact hj1
        · right
          change ∃ k ∈ Set.Icc lo₂ hi₂,
            p = (base.1 + k * (q : ℤ), base.2 - k * (a : ℤ))
          refine ⟨j, ?_, hpj⟩
          rw [← hI₂]
          exact hj2
      · intro hp
        rcases hp with hp1 | hp2
        · change ∃ j ∈ Set.Icc lo₁ hi₁, p = φ j at hp1
          rcases hp1 with ⟨j, hj, rfl⟩
          have hjP₁ : j ∈ P₁ := by rw [hI₁]; exact hj
          change φ j ∈ cellLinearSliceOnLine g a q c
          exact hjP₁.1
        · change ∃ j ∈ Set.Icc lo₂ hi₂, p = φ j at hp2
          rcases hp2 with ⟨j, hj, rfl⟩
          have hjP₂ : j ∈ P₂ := by rw [hI₂]; exact hj
          change φ j ∈ cellLinearSliceOnLine g a q c
          exact hjP₂.1
    have hdisj : Disjoint
        (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁)
        (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂) := by
      rw [Set.disjoint_left]
      intro p hp1 hp2
      change (∃ j ∈ Set.Icc lo₁ hi₁, p = φ j) at hp1
      change (∃ j ∈ Set.Icc lo₂ hi₂, p = φ j) at hp2
      obtain ⟨j, hj, rfl⟩ := hp1
      obtain ⟨k, hk, hEq⟩ := hp2
      have hEqjk : j = k := hφinj hEq
      have hj₁ : j ∈ P₁ := by rw [hI₁]; exact hj
      have hk₂ : k ∈ P₂ := by rw [hI₂]; exact hk
      have hj₂ : j ∈ P₂ := by simpa [hEqjk] using hk₂
      exact (not_lt_of_ge hj₁.2) hj₂.2
    exact ⟨base, lo₁, hi₁, lo₂, hi₂, hdecomp, hdisj,
      cellLatticeIccProgression_finite base (q : ℤ) (a : ℤ) lo₁ hi₁,
      cellLatticeIccProgression_finite base (q : ℤ) (a : ℤ) lo₂ hi₂⟩
  · have hprog : cellLatticeIccProgression (0, 0) (q : ℤ) (a : ℤ) 1 0 = ∅ := by
      ext p
      simp [cellLatticeIccProgression]
    refine ⟨(0, 0), 1, 0, 1, 0, ?_, ?_, ?_, ?_⟩
    · ext p
      constructor
      · intro hp
        exact (hne ⟨p, hp⟩).elim
      · intro hp
        rw [hprog] at hp
        simp at hp
    · rw [hprog]
      simp
    · rw [hprog]
      simp
    · rw [hprog]
      simp

/-- The geometric bounds and exact quadratic identity for every point in a
selected rational cell. -/
theorem cellLinearPointBounds (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q)
    (p : ℤ × ℤ) (hp : p ∈ cellLinearSlice g a q) :
    let u : ℝ := (a : ℝ) * (q : ℝ)
    let t : ℝ := 2 * Real.sqrt (u * g.X)
    let Z : ℝ := 2 * D g.K₀ * g.M / (g.Q : ℝ)
    (cellLinearCoordinate a q p : ℝ) > t ∧
      0 < t ∧
      |(cellTransverseCoordinate a q p : ℝ)| ≤ Z ∧
      (cellLinearCoordinate a q p : ℝ) ^ 2 -
          (cellTransverseCoordinate a q p : ℝ) ^ 2 =
        4 * u * (p.1 : ℝ) * (p.2 : ℝ) ∧
      (g.r * (q : ℝ) ^ 2 / 8 ≤ u ∧
        u ≤ E g.K₀ * g.r * (q : ℝ) ^ 2) := by
  classical
  dsimp
  dsimp [cellLinearSlice] at hp
  have hcellEligible : rationalCellEligible g a q := hidx.1
  rcases hcellEligible with ⟨hcop, hqlo, hqhi, halo, hamin, hamax⟩
  have hcellEligible' : rationalCellEligible g a q :=
    ⟨hcop, hqlo, hqhi, halo, hamin, hamax⟩
  have hparams := admissibleParameterBounds g q hqlo hqhi
  obtain ⟨hmpos, hnpos, _, _⟩ := hparams.lattice_point_properties p hp.1
  have hmPosReal : 0 < (p.1 : ℝ) := by exact_mod_cast hmpos
  have hnPosReal : 0 < (p.2 : ℝ) := by exact_mod_cast hnpos
  have hqpos : 0 < q := by omega
  have hqPosReal : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hMnonneg : 0 ≤ g.M := by linarith [g.M_ge_one]
  have hMupper : (p.1 : ℝ) ≤ 2 * g.M := g.J_subset hp.1.1 |>.2
  have happrox := (positiveRationalCellPartition g).approximation a q hcellEligible'
    ((p.2 : ℝ) / (p.1 : ℝ)) hp.2
  let u : ℝ := (a : ℝ) * (q : ℝ)
  let t : ℝ := 2 * Real.sqrt (u * g.X)
  let Z : ℝ := 2 * D g.K₀ * g.M / (g.Q : ℝ)
  have huLower : g.r * (q : ℝ) ^ 2 / 8 ≤ u := by
    dsimp [u]
    have hmul := mul_le_mul_of_nonneg_right hamin (show 0 ≤ (q : ℝ) by positivity)
    nlinarith [hqPosReal]
  have huUpper : u ≤ E g.K₀ * g.r * (q : ℝ) ^ 2 := by
    dsimp [u]
    have hmul := mul_le_mul_of_nonneg_right hamax (show 0 ≤ (q : ℝ) by positivity)
    nlinarith
  have huPos : 0 < u := by
    dsimp [u]
    have haPos : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
    exact mul_pos haPos hqPosReal
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have huXpos : 0 < u * g.X := mul_pos huPos hXpos
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have htSq : t ^ 2 = 4 * u * g.X := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt (le_of_lt huXpos)]
    ring
  have hqIntPos : (q : ℤ) > 0 := by exact_mod_cast hqpos
  have haIntPos : (a : ℤ) > 0 := by exact_mod_cast (show 0 < a by omega)
  have hlinePos :
      (cellLinearCoordinate a q p : ℝ) > 0 := by
    dsimp [cellLinearCoordinate]
    push_cast
    positivity
  have hprod : g.X < (p.1 : ℝ) * (p.2 : ℝ) := hp.1.2.1
  have hidentity :
      (cellLinearCoordinate a q p : ℝ) ^ 2 -
          (cellTransverseCoordinate a q p : ℝ) ^ 2 =
        4 * u * (p.1 : ℝ) * (p.2 : ℝ) := by
    dsimp [cellLinearCoordinate, cellTransverseCoordinate, u]
    push_cast
    ring
  have hcsq :
      t ^ 2 < (cellLinearCoordinate a q p : ℝ) ^ 2 := by
    calc
      t ^ 2 = 4 * u * g.X := htSq
      _ < 4 * u * ((p.1 : ℝ) * (p.2 : ℝ)) := by
        nlinarith [hprod, huPos]
      _ ≤ (cellLinearCoordinate a q p : ℝ) ^ 2 := by
        calc
          4 * u * ((p.1 : ℝ) * (p.2 : ℝ)) =
              4 * u * (p.1 : ℝ) * (p.2 : ℝ) := by ring
          _ = (cellLinearCoordinate a q p : ℝ) ^ 2 -
              (cellTransverseCoordinate a q p : ℝ) ^ 2 := hidentity.symm
          _ ≤ (cellLinearCoordinate a q p : ℝ) ^ 2 := by
            nlinarith [sq_nonneg (cellTransverseCoordinate a q p : ℝ)]
  have hct : t < (cellLinearCoordinate a q p : ℝ) :=
    (sq_lt_sq₀ htpos.le hlinePos.le).mp hcsq
  have hZ : |(cellTransverseCoordinate a q p : ℝ)| ≤ Z := by
    have hcoord :
        (cellTransverseCoordinate a q p : ℝ) =
          (p.1 : ℝ) * (q : ℝ) *
            (((p.2 : ℝ) / (p.1 : ℝ)) - (a : ℝ) / (q : ℝ)) := by
      dsimp [cellTransverseCoordinate]
      push_cast
      field_simp
    rw [hcoord, abs_mul, abs_mul, abs_of_pos hmPosReal,
      abs_of_pos hqPosReal]
    calc
      (p.1 : ℝ) * (q : ℝ) *
          |(p.2 : ℝ) / (p.1 : ℝ) - (a : ℝ) / (q : ℝ)| ≤
        (2 * g.M) * (q : ℝ) *
          (D g.K₀ / ((g.Q : ℝ) * (q : ℝ))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right hMupper hqPosReal.le
            · exact happrox
            · exact abs_nonneg _
            · exact mul_nonneg (mul_nonneg (by norm_num) hMnonneg) hqPosReal.le
      _ = Z := by
        dsimp [Z]
        field_simp
  refine ⟨hct, htpos, ?_, hidentity, huLower, huUpper⟩
  simpa [Z] using hZ

/-- On a fixed linear slice the transverse coordinate determines the lattice
point. -/
theorem cellLinearSlice_z_injective (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    (c : ℤ) :
    Set.InjOn (cellTransverseCoordinate a q)
      (cellLinearSliceOnLine g a q c) := by
  intro p hp p' hp' hz
  rcases hidx.1 with ⟨_, hqlo, _, halo, _, _⟩
  have hqpos : 0 < q := by
    omega
  have hapos : 0 < a := by
    omega
  have hqInt : (q : ℤ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have haInt : (a : ℤ) ≠ 0 := by exact_mod_cast hapos.ne'
  rcases hp with ⟨_, hc⟩
  rcases hp' with ⟨_, hc'⟩
  dsimp [cellLinearCoordinate, cellTransverseCoordinate] at hc hc' hz
  have hqn : (q : ℤ) * p.2 = (q : ℤ) * p'.2 := by
    linarith [hc, hc', hz]
  have ham : (a : ℤ) * p.1 = (a : ℤ) * p'.1 := by
    linarith [hc, hc', hz]
  have hn : p.2 = p'.2 := mul_left_cancel₀ hqInt hqn
  have hm : p.1 = p'.1 := mul_left_cancel₀ haInt ham
  exact Prod.ext hm hn

/-- All transverse coordinates on a fixed cell line have one residue modulo
the product of the reduced numerator and denominator. -/
theorem cellLinearSlice_z_modEq (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    (c : ℤ) {p p' : ℤ × ℤ}
    (hp : p ∈ cellLinearSliceOnLine g a q c)
    (hp' : p' ∈ cellLinearSliceOnLine g a q c) :
    cellTransverseCoordinate a q p ≡
      cellTransverseCoordinate a q p' [ZMOD ((a * q : ℕ) : ℤ)] := by
  classical
  have hcop : Nat.Coprime a q := hidx.1.1
  have hcopInt : (a : ℤ).natAbs.Coprime (q : ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using hcop
  rcases hp with ⟨_, hc⟩
  rcases hp' with ⟨_, hc'⟩
  have hmoda : cellTransverseCoordinate a q p ≡
      cellTransverseCoordinate a q p' [ZMOD (a : ℤ)] := by
    apply Int.modEq_of_dvd
    refine ⟨2 * (p.1 - p'.1), ?_⟩
    dsimp [cellTransverseCoordinate, cellLinearCoordinate] at hc hc' ⊢
    nlinarith
  have hmodq : cellTransverseCoordinate a q p ≡
      cellTransverseCoordinate a q p' [ZMOD (q : ℤ)] := by
    apply Int.modEq_of_dvd
    refine ⟨2 * (p'.2 - p.2), ?_⟩
    dsimp [cellTransverseCoordinate, cellLinearCoordinate] at hc hc' ⊢
    nlinarith
  have hmodmul :=
    (Int.modEq_and_modEq_iff_modEq_mul hcopInt).mp ⟨hmoda, hmodq⟩
  have hcastmul : ((a * q : ℕ) : ℤ) = (a : ℤ) * (q : ℤ) := by push_cast; rfl
  rw [← hcastmul] at hmodmul
  exact hmodmul

/-- The exact linear-slice conclusions: the c/t/z bounds and quadratic
identity, a disjoint decomposition into at most two finite progressions with
step `(q,-a)`, injectivity of the transverse coordinate, and one residue
class modulo `u=aq`. -/
theorem cellLinearSlices (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) (c : ℤ) :
    (∀ p ∈ cellLinearSliceOnLine g a q c,
      let u : ℝ := (a : ℝ) * (q : ℝ)
      let t : ℝ := 2 * Real.sqrt (u * g.X)
      let Z : ℝ := 2 * D g.K₀ * g.M / (g.Q : ℝ)
      (cellLinearCoordinate a q p : ℝ) > t ∧
        0 < t ∧
        |(cellTransverseCoordinate a q p : ℝ)| ≤ Z ∧
        (cellLinearCoordinate a q p : ℝ) ^ 2 -
            (cellTransverseCoordinate a q p : ℝ) ^ 2 =
          4 * u * (p.1 : ℝ) * (p.2 : ℝ) ∧
        (g.r * (q : ℝ) ^ 2 / 8 ≤ u ∧
          u ≤ E g.K₀ * g.r * (q : ℝ) ^ 2)) ∧
    Set.InjOn (cellTransverseCoordinate a q) (cellLinearSliceOnLine g a q c) ∧
    (∀ {p p'}, p ∈ cellLinearSliceOnLine g a q c →
      p' ∈ cellLinearSliceOnLine g a q c →
      cellTransverseCoordinate a q p ≡
        cellTransverseCoordinate a q p' [ZMOD ((a * q : ℕ) : ℤ)]) ∧
    (∃ base : ℤ × ℤ, ∃ lo₁ hi₁ lo₂ hi₂ : ℤ,
      cellLinearSliceOnLine g a q c =
        cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁ ∪
          cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂ ∧
      Disjoint
        (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁)
        (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂) ∧
      (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁).Finite ∧
      (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂).Finite) := by
  refine ⟨?_, cellLinearSlice_z_injective g a q hidx c, ?_,
    cellLinearSlices_progression_decomposition g a q hidx c⟩
  · intro p hp
    exact cellLinearPointBounds g a q hidx p hp.1
  · intro p p' hp hp'
    exact cellLinearSlice_z_modEq g a q hidx c hp hp'

end FractionalPrimes.Literature.Hyperbola
