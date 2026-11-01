module

public import FractionalPrimes.Literature.Hyperbola.ParameterBounds
import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

open Set

/-- Eligibility for the rational centers in the positive-slope cell lemma. -/
def rationalCellEligible (g : HyperbolaGeometricData) (a q : ℕ) : Prop :=
  Nat.Coprime a q ∧ 1 ≤ q ∧ q ≤ g.Q ∧ 1 ≤ a ∧
    (g.r / 8) * (q : ℝ) ≤ (a : ℝ) ∧
    (a : ℝ) ≤ E g.K₀ * g.r * (q : ℝ)

/-- The closed Dirichlet window about `a/q` with its exact source radius. -/
noncomputable def rationalCellWindow (g : HyperbolaGeometricData)
    (a q : ℕ) : Set ℝ :=
  Set.Icc
    ((a : ℝ) / (q : ℝ) - 1 / ((g.Q : ℝ) * (q : ℝ)))
    ((a : ℝ) / (q : ℝ) + 1 / ((g.Q : ℝ) * (q : ℝ)))

/-- The low-denominator nearest-integer cell before restriction to the slope
interval. The first cell has the source's open left endpoint and open right
endpoint; all later cells are left-closed and right-open. -/
noncomputable def nearestIntegerRationalCell (a : ℕ) : Set ℝ :=
  if a = 1 then Set.Ioo 0 (3 / 2 : ℝ)
  else Set.Ico ((a : ℝ) - 1 / 2) ((a : ℝ) + 1 / 2)

/-- The union of all eligible lower-denominator windows removed from one
high-regime cell. -/
noncomputable def lowerRationalCellWindows (g : HyperbolaGeometricData)
    (q : ℕ) : Set ℝ :=
  {s : ℝ | ∃ a' q' : ℕ,
      rationalCellEligible g a' q' ∧ q' < q ∧
        s ∈ rationalCellWindow g a' q'}

/-- The literal piecewise cells from `lhg:cells`. For `Q < D`, only the
nearest-integer denominator-one cells are used. For `Q ≥ D`, the closed
Dirichlet window is cut by every eligible window with smaller denominator;
this fixes ties by the smallest available denominator. -/
noncomputable def positiveRationalCell (g : HyperbolaGeometricData)
    (a q : ℕ) : Set ℝ := by
  classical
  by_cases hlow : (g.Q : ℝ) < D g.K₀
  · exact if hq : q = 1 then
      Set.Ioc (g.r / 4) (2 * g.r) ∩ nearestIntegerRationalCell a
    else ∅
  · exact Set.Ioc (g.r / 4) (2 * g.r) ∩
      (rationalCellWindow g a q \ lowerRationalCellWindows g q)

/-- The finite set of all eligible indices. Its explicit bounds follow from
`q ≤ Q` and `a ≤ E r q` in the high-denominator regime, and from the
corresponding `q=1` bound in the low-denominator regime. -/
noncomputable def positiveRationalCellIndices (g : HyperbolaGeometricData) :
    Finset (ℕ × ℕ) := by
  classical
  by_cases hlow : (g.Q : ℝ) < D g.K₀
  · exact ((Finset.Icc 1 (Nat.floor (E g.K₀ * g.r))) ×ˢ {1}).filter
      (fun p => rationalCellEligible g p.1 p.2)
  · exact ((Finset.Icc 1 (Nat.floor (E g.K₀ * g.r * (g.Q : ℝ)))) ×ˢ
      (Finset.Icc 1 g.Q)).filter (fun p =>
        rationalCellEligible g p.1 p.2)

/-- The actual index convention used by the piecewise construction: in the
low-denominator case only denominator one occurs. -/
def positiveRationalCellIndexEligible (g : HyperbolaGeometricData)
    (a q : ℕ) : Prop :=
  rationalCellEligible g a q ∧
    ((g.Q : ℝ) < D g.K₀ → q = 1)

/-- The explicit finite index set contains exactly the indices used by the
piecewise cell construction. -/
theorem positiveRationalCellIndices_mem_iff (g : HyperbolaGeometricData)
    (a q : ℕ) :
    (a, q) ∈ positiveRationalCellIndices g ↔
      positiveRationalCellIndexEligible g a q := by
  classical
  have hrpos : 0 < g.r := by
    have hXpos : 0 < g.X := by linarith [g.X_ge_one]
    have hMpos : 0 < g.M := by linarith [g.M_ge_one]
    dsimp [HyperbolaGeometricData.r]
    exact div_pos hXpos (sq_pos_of_pos hMpos)
  have hEpos : 0 < E g.K₀ := by
    dsimp [E]
    nlinarith [g.K₀_ge_one]
  by_cases hlow : (g.Q : ℝ) < D g.K₀
  · rw [positiveRationalCellIndices, dite_eq_left hlow]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨haLo, haHi⟩, hqEq⟩, helig⟩
      exact ⟨helig, fun _ => by simpa using hqEq⟩
    · rintro ⟨helig, hqEq⟩
      rcases helig with ⟨hcop, hqLo, hqHi, haLo, hamin, hamax⟩
      have hq1 : q = 1 := hqEq hlow
      subst q
      have haFloor : a ≤ Nat.floor (E g.K₀ * g.r) :=
        Nat.le_floor (by simpa using hamax)
      exact ⟨⟨⟨haLo, haFloor⟩, rfl⟩,
        ⟨hcop, hqLo, hqHi, haLo, hamin, hamax⟩⟩
  · rw [positiveRationalCellIndices, dite_eq_right hlow]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨haLo, haHi⟩, ⟨hqLo, hqHi⟩⟩, helig⟩
      exact ⟨helig, fun h => (hlow h).elim⟩
    · rintro ⟨helig, hqEq⟩
      rcases helig with ⟨hcop, hqLo, hqHi, haLo, hamin, hamax⟩
      have haUpper : (a : ℝ) ≤ E g.K₀ * g.r * (g.Q : ℝ) := by
        calc
          (a : ℝ) ≤ E g.K₀ * g.r * (q : ℝ) := hamax
          _ ≤ E g.K₀ * g.r * (g.Q : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hqHi)
              (mul_nonneg hEpos.le hrpos.le)
      have haFloor : a ≤ Nat.floor (E g.K₀ * g.r * (g.Q : ℝ)) :=
        Nat.le_floor (by simpa using haUpper)
      exact ⟨⟨⟨haLo, haFloor⟩, ⟨hqLo, hqHi⟩⟩,
        ⟨hcop, hqLo, hqHi, haLo, hamin, hamax⟩⟩

/-- The exact family of deterministic cells supplied by the positive
rational partition lemma. -/
structure PositiveRationalCellPartition (g : HyperbolaGeometricData) : Prop where
  index_mem_iff : ∀ a q, (a, q) ∈ positiveRationalCellIndices g ↔
    positiveRationalCellIndexEligible g a q
  interval : ∀ a q, rationalCellEligible g a q →
    (positiveRationalCell g a q).OrdConnected
  slope_subset : ∀ a q, rationalCellEligible g a q →
    positiveRationalCell g a q ⊆ Set.Ioc (g.r / 4) (2 * g.r)
  approximation : ∀ a q, rationalCellEligible g a q →
    ∀ s ∈ positiveRationalCell g a q,
      |s - (a : ℝ) / (q : ℝ)| ≤ D g.K₀ / ((g.Q : ℝ) * (q : ℝ))
  pairwise_disjoint : ∀ i ∈ positiveRationalCellIndices g,
    ∀ j ∈ positiveRationalCellIndices g, i ≠ j →
      Disjoint (positiveRationalCell g i.1 i.2)
        (positiveRationalCell g j.1 j.2)
  covers : Set.Ioc (g.r / 4) (2 * g.r) ⊆
    ⋃ i ∈ (positiveRationalCellIndices g : Set (ℕ × ℕ)),
      positiveRationalCell g i.1 i.2

/-- Distinct reduced positive fractions with unequal denominators have
distinct cross products. -/
private theorem reduced_cross_products_ne {a q a' q' : ℕ}
    (haq : Nat.Coprime a q) (_ha'q' : Nat.Coprime a' q')
    (_hqpos : 0 < q) (hq'pos : 0 < q') (hqq' : q' < q) :
    a * q' ≠ a' * q := by
  intro hcross
  have hdivqa : q ∣ q' * a := by
    rw [Nat.mul_comm, hcross]
    exact ⟨a', by ac_rfl⟩
  have hqdiv : q ∣ q' := (haq.symm.dvd_mul_right).mp hdivqa
  have hqle : q ≤ q' := Nat.le_of_dvd (by omega) hqdiv
  omega

/-- The cross-product separation bound for two different reduced fractions. -/
private theorem reduced_fraction_separation {a q a' q' : ℕ}
    (haq : Nat.Coprime a q) (ha'q' : Nat.Coprime a' q')
    (hqpos : 0 < q) (hq'pos : 0 < q') (hqq' : q' < q) :
    1 / ((q : ℝ) * (q' : ℝ)) ≤
      |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)| := by
  have hcross := reduced_cross_products_ne haq ha'q' hqpos hq'pos hqq'
  have hqposR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hq'posR : 0 < (q' : ℝ) := by exact_mod_cast hq'pos
  have hden : 0 < (q : ℝ) * (q' : ℝ) := mul_pos hqposR hq'posR
  have hfrac :
      (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ) =
        (((a * q' : ℕ) : ℝ) - ((a' * q : ℕ) : ℝ)) /
          ((q : ℝ) * (q' : ℝ)) := by
    field_simp
    push_cast
    ring
  have hcrossR : ((a * q' : ℕ) : ℝ) ≠ ((a' * q : ℕ) : ℝ) := by
    exact_mod_cast hcross
  have hnum :
      (1 : ℝ) ≤ |((a * q' : ℕ) : ℝ) - ((a' * q : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hcrossR with hlt | hgt
    · rw [abs_of_neg (sub_neg.mpr hlt)]
      have hnat : a * q' + 1 ≤ a' * q :=
        Nat.succ_le_of_lt (by exact_mod_cast hlt)
      have hnatR : ((a * q' : ℕ) : ℝ) + 1 ≤ ((a' * q : ℕ) : ℝ) := by
        exact_mod_cast hnat
      linarith
    · rw [abs_of_pos (sub_pos.mpr hgt)]
      have hnat : a' * q + 1 ≤ a * q' :=
        Nat.succ_le_of_lt (by exact_mod_cast hgt)
      have hnatR : ((a' * q : ℕ) : ℝ) + 1 ≤ ((a * q' : ℕ) : ℝ) := by
        exact_mod_cast hnat
      linarith
  rw [hfrac, abs_div, abs_of_pos hden]
  rw [div_le_div_iff₀ hden hden]
  simpa using (mul_le_mul_of_nonneg_right hnum hden.le)

/-- If a closed interval of at least the current radius has its center outside
the interior of the current interval, then a blocked intermediate point also
blocks one of the two endpoints. -/
private theorem blocked_endpoint_of_between
    {c ρ d σ x y z : ℝ}
    (hρσ : ρ ≤ σ)
    (hσ : 0 ≤ σ)
    (hside : c ≤ d - σ ∨ d + σ ≤ c)
    (hx : x ∈ Set.Icc (c - ρ) (c + ρ))
    (hz : z ∈ Set.Icc (c - ρ) (c + ρ))
    (hy : y ∈ Set.Icc (d - σ) (d + σ))
    (hxy : x ≤ y) (hyz : y ≤ z) :
    x ∈ Set.Icc (d - σ) (d + σ) ∨
      z ∈ Set.Icc (d - σ) (d + σ) := by
  rcases hside with hright | hleft
  · right
    constructor
    · exact (le_trans hy.1 hyz)
    · calc
        z ≤ c + ρ := hz.2
        _ ≤ c + σ := by linarith
        _ ≤ d := by linarith
        _ ≤ d + σ := by linarith
  · left
    constructor
    · calc
        d - σ ≤ d := by linarith
        _ ≤ c - ρ := by linarith
        _ ≤ x := hx.1
    · exact (le_trans hxy hy.2)

/-- Every eligible lower-denominator window meets a current eligible window
only as a prefix or suffix. Consequently subtracting all such windows leaves
an order-convex set. -/
private theorem highRationalCell_interval
    (g : HyperbolaGeometricData) {a q : ℕ}
    (hnotLow : ¬ (g.Q : ℝ) < D g.K₀)
    (hcur : rationalCellEligible g a q) :
    (positiveRationalCell g a q).OrdConnected := by
  classical
  simp only [positiveRationalCell, hnotLow]
  rw [Set.ordConnected_iff]
  intro x hx y hy hxy z hz
  rcases hx with ⟨hxbase, hxrest⟩
  rcases hxrest with ⟨hxwindow, hxnot⟩
  rcases hy with ⟨hybase, hyrest⟩
  rcases hyrest with ⟨hywindow, hynot⟩
  have hzbase : z ∈ Set.Ioc (g.r / 4) (2 * g.r) := by
    exact Set.ordConnected_Ioc.out hxbase hybase hz
  have hzwindow : z ∈ rationalCellWindow g a q := by
    exact Set.ordConnected_Icc.out hxwindow hywindow hz
  have hznot : z ∉ lowerRationalCellWindows g q := by
    intro hblocked
    rcases hblocked with ⟨a', q', hprev, hqprev, hzblock⟩
    rcases hcur with ⟨hcop, hqlo, hqhi, halo, hamin, hamax⟩
    rcases hprev with ⟨hcop', hq'lo, hq'hi, ha'lo, ha'min, ha'max⟩
    let ρ : ℝ := 1 / ((g.Q : ℝ) * (q : ℝ))
    let σ : ℝ := 1 / ((g.Q : ℝ) * (q' : ℝ))
    let c : ℝ := (a : ℝ) / (q : ℝ)
    let d : ℝ := (a' : ℝ) / (q' : ℝ)
    have hqpos : 0 < q := by omega
    have hq'pos : 0 < q' := by omega
    have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
    have hqposR : 0 < (q : ℝ) := by exact_mod_cast hqpos
    have hq'posR : 0 < (q' : ℝ) := by exact_mod_cast hq'pos
    have hQq : (q : ℝ) ≤ (g.Q : ℝ) := by exact_mod_cast hqhi
    have hdenpos : 0 < (g.Q : ℝ) * (q : ℝ) := mul_pos hQpos hqposR
    have hden'pos : 0 < (g.Q : ℝ) * (q' : ℝ) := mul_pos hQpos hq'posR
    have hρnonneg : 0 ≤ ρ := by dsimp [ρ]; positivity
    have hσpos : 0 < σ := by dsimp [σ]; positivity
    have hρσ : ρ ≤ σ := by
      dsimp [ρ, σ]
      apply one_div_le_one_div_of_le (mul_pos hQpos hq'posR)
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast hqprev.le) hQpos.le
    have hsep : σ ≤ |c - d| := by
      dsimp [σ, c, d]
      have hsep' := reduced_fraction_separation hcop hcop' hqpos hq'pos hqprev
      have hdenle : (q : ℝ) * (q' : ℝ) ≤
          (g.Q : ℝ) * (q' : ℝ) := by
        exact mul_le_mul_of_nonneg_right hQq hq'posR.le
      have hrecip : 1 / ((g.Q : ℝ) * (q' : ℝ)) ≤
          1 / ((q : ℝ) * (q' : ℝ)) :=
        one_div_le_one_div_of_le (mul_pos hqposR hq'posR) hdenle
      exact le_trans hrecip hsep'
    have hside : c ≤ d - σ ∨ d + σ ≤ c := by
      rcases le_total c d with hcd | hdc
      · left
        have habs : |c - d| = d - c := by
          calc
            |c - d| = -(c - d) := abs_of_nonpos (sub_nonpos.mpr hcd)
            _ = d - c := by ring
        rw [habs] at hsep
        linarith
      · right
        have habs : |c - d| = c - d := abs_of_nonneg (sub_nonneg.mpr hdc)
        rw [habs] at hsep
        linarith
    have hxwindow' : x ∈ Set.Icc (c - ρ) (c + ρ) := by
      simpa [rationalCellWindow, c, ρ] using hxwindow
    have hywindow' : y ∈ Set.Icc (c - ρ) (c + ρ) := by
      simpa [rationalCellWindow, c, ρ] using hywindow
    have hzblock' : z ∈ Set.Icc (d - σ) (d + σ) := by
      simpa [rationalCellWindow, d, σ] using hzblock
    have hend := blocked_endpoint_of_between hρσ hσpos.le hside
      hxwindow' hywindow' hzblock' hz.1 hz.2
    have hprev' : rationalCellEligible g a' q' :=
      ⟨hcop', hq'lo, hq'hi, ha'lo, ha'min, ha'max⟩
    rcases hend with hxblock | hyblock
    · exact hxnot ⟨a', q', hprev', hqprev, by
        simpa [rationalCellWindow, d, σ] using hxblock⟩
    · exact hynot ⟨a', q', hprev', hqprev, by
        simpa [rationalCellWindow, d, σ] using hyblock⟩
  exact ⟨hzbase, hzwindow, hznot⟩

/-- The nearest-integer cells have the source's disjoint tie convention. -/
private theorem nearestIntegerRationalCell_disjoint {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b) :
    Disjoint (nearestIntegerRationalCell a) (nearestIntegerRationalCell b) := by
  have ordered {u v : ℕ} (huv : u < v) (hu : 1 ≤ u) (hv : 1 ≤ v) :
      Disjoint (nearestIntegerRationalCell u) (nearestIntegerRationalCell v) := by
    rw [Set.disjoint_left]
    intro s hs ht
    by_cases hu1 : u = 1
    · have hs' : s ∈ Set.Ioo 0 (3 / 2 : ℝ) := by
        simpa [nearestIntegerRationalCell, hu1] using hs
      have hv1 : v ≠ 1 := by omega
      have ht' : s ∈ Set.Ico ((v : ℝ) - 1 / 2) ((v : ℝ) + 1 / 2) := by
        simpa [nearestIntegerRationalCell, hv1] using ht
      have hv2 : 2 ≤ v := by omega
      have hv2R : (2 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv2
      have hleft : (3 / 2 : ℝ) ≤ (v : ℝ) - 1 / 2 := by linarith
      linarith [hs'.2, ht'.1]
    · have hs' : s ∈ Set.Ico ((u : ℝ) - 1 / 2) ((u : ℝ) + 1 / 2) := by
        simpa [nearestIntegerRationalCell, hu1] using hs
      have hv1 : v ≠ 1 := by omega
      have ht' : s ∈ Set.Ico ((v : ℝ) - 1 / 2) ((v : ℝ) + 1 / 2) := by
        simpa [nearestIntegerRationalCell, hv1] using ht
      have hgap : u + 1 ≤ v := by omega
      have hgapR : (u : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast hgap
      linarith [hs'.2, ht'.1]
  rcases lt_or_gt_of_ne hab with hablt | habgt
  · exact ordered hablt ha hb
  · rw [disjoint_comm]
    exact ordered habgt hb ha

/-- In the low-denominator regime every nearest-integer cell is an interval. -/
private theorem lowRationalCell_interval
    (g : HyperbolaGeometricData) {a q : ℕ}
    (hlow : (g.Q : ℝ) < D g.K₀)
    (hindex : positiveRationalCellIndexEligible g a q) :
    (positiveRationalCell g a q).OrdConnected := by
  rcases hindex with ⟨_, hqone⟩
  have hq : q = 1 := hqone hlow
  simp only [positiveRationalCell, hlow, hq]
  apply Set.OrdConnected.inter Set.ordConnected_Ioc
  by_cases ha : a = 1
  · simpa [nearestIntegerRationalCell, ha] using Set.ordConnected_Ioo
  · simpa [nearestIntegerRationalCell, ha] using Set.ordConnected_Ico

/-- Points in a low-regime nearest-integer cell are within one of its integer
center. -/
private theorem nearestIntegerRationalCell_error {a : ℕ}
    (ha : 1 ≤ a) {s : ℝ} (hs : s ∈ nearestIntegerRationalCell a) :
    |s - (a : ℝ)| ≤ 1 := by
  by_cases ha1 : a = 1
  · have hs' : s ∈ Set.Ioo 0 (3 / 2 : ℝ) := by
      simpa [nearestIntegerRationalCell, ha1] using hs
    subst a
    have hlo : -1 ≤ s - (1 : ℝ) := by linarith [hs'.1]
    have hhi : s - (1 : ℝ) ≤ 1 := by linarith [hs'.2]
    simpa using (abs_le.mpr ⟨hlo, hhi⟩)
  · have hs' : s ∈ Set.Ico ((a : ℝ) - 1 / 2) ((a : ℝ) + 1 / 2) := by
      simpa [nearestIntegerRationalCell, ha1] using hs
    have hlo : -1 ≤ s - (a : ℝ) := by linarith [hs'.1]
    have hhi : s - (a : ℝ) ≤ 1 := by linarith [hs'.2]
    exact (abs_le.mpr ⟨hlo, hhi⟩)

/-- Every positive real has its deterministic nearest-integer cell, with the
source assignment `max(1, floor(s+1/2))`. -/
private theorem nearestIntegerRationalCell_assignment {s : ℝ}
    (hs : 0 < s) :
    ∃ a : ℕ, a = max 1 (Nat.floor (s + 1 / 2 : ℝ)) ∧
      1 ≤ a ∧ s ∈ nearestIntegerRationalCell a := by
  let n : ℕ := Nat.floor (s + 1 / 2 : ℝ)
  let a : ℕ := max 1 n
  have ha : a = max 1 (Nat.floor (s + 1 / 2 : ℝ)) := rfl
  have haPos : 1 ≤ a := Nat.le_max_left _ _
  have hxnonneg : 0 ≤ s + 1 / 2 := by linarith
  by_cases hn : n ≤ 1
  · have haOne : a = 1 := by
      dsimp [a]
      exact Nat.max_eq_left hn
    have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast hn
    have hfloorlt := Nat.lt_floor_add_one (s + 1 / 2 : ℝ)
    have hsupper : s < 3 / 2 := by
      dsimp [n] at hnR hfloorlt
      linarith
    refine ⟨a, ha, haPos, ?_⟩
    rw [haOne]
    simpa [nearestIntegerRationalCell] using
      (show s ∈ Set.Ioo (0 : ℝ) (3 / 2) from ⟨hs, hsupper⟩)
  · have hnLower : 2 ≤ n := by omega
    have haN : a = n := by
      dsimp [a]
      exact Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    have hnFloor : (n : ℝ) ≤ s + 1 / 2 := Nat.floor_le hxnonneg
    have hnFloorLt : s + 1 / 2 < (n : ℝ) + 1 :=
      Nat.lt_floor_add_one (s + 1 / 2 : ℝ)
    have haLo : (a : ℝ) - 1 / 2 ≤ s := by
      have haCast : (a : ℝ) = (n : ℝ) := by exact_mod_cast haN
      rw [haCast]
      linarith
    have haHi : s < (a : ℝ) + 1 / 2 := by
      have haCast : (a : ℝ) = (n : ℝ) := by exact_mod_cast haN
      rw [haCast]
      linarith
    have haNotOne : a ≠ 1 := by omega
    refine ⟨a, ha, haPos, ?_⟩
    have hsCell : s ∈ Set.Ico ((a : ℝ) - 1 / 2) ((a : ℝ) + 1 / 2) :=
      ⟨haLo, haHi⟩
    simpa [nearestIntegerRationalCell, haNotOne] using hsCell

/-- The admissible lower bound on `r` implies `K₀² r ≥ 1`. -/
private theorem scaleProduct_ge_one (g : HyperbolaGeometricData) :
    1 ≤ g.K₀ ^ 2 * g.r := by
  have hQlo : 1 ≤ g.Q := Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne'
  have hbounds := admissibleParameterBounds g 1 (by omega) hQlo
  have hKpos : 0 < g.K₀ ^ 2 := by nlinarith [g.K₀_ge_one]
  have hrlo : (g.K₀ ^ 2)⁻¹ ≤ g.r := hbounds.r_lower
  have hrlo' : 1 / (g.K₀ ^ 2) ≤ g.r := by simpa [one_div] using hrlo
  have hmul := (div_le_iff₀ hKpos).1 hrlo'
  simpa [mul_comm] using hmul

/-- The low-regime nearest-integer center associated to a slope is an
eligible denominator-one index. -/
private theorem lowNearestCenter_eligible
    (g : HyperbolaGeometricData) {s : ℝ}
    (hs : s ∈ Set.Ioc (g.r / 4) (2 * g.r))
    (a : ℕ) (ha : 1 ≤ a)
    (hcell : s ∈ nearestIntegerRationalCell a) :
    rationalCellEligible g a 1 := by
  have hrpos : 0 < g.r := by
    have hXpos : 0 < g.X := by linarith [g.X_ge_one]
    have hMpos : 0 < g.M := by linarith [g.M_ge_one]
    dsimp [HyperbolaGeometricData.r]
    exact div_pos hXpos (sq_pos_of_pos hMpos)
  have hQlo : 1 ≤ g.Q := Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne'
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hrK : 1 ≤ g.K₀ ^ 2 * g.r := scaleProduct_ge_one g
  have herr := nearestIntegerRationalCell_error ha hcell
  have hcenter : s / 2 ≤ (a : ℝ) := by
    by_cases hsLarge : 2 ≤ s
    · have hst : s - 1 ≤ (a : ℝ) := by
        have h := abs_le.mp herr
        linarith [h.1]
      linarith
    · have hsSmall : s ≤ 2 := le_of_not_ge hsLarge
      have haReal : 1 ≤ (a : ℝ) := by exact_mod_cast ha
      linarith
  have hamin : (g.r / 8) * (1 : ℝ) ≤ (a : ℝ) := by
    have hsHalf : g.r / 8 < s / 2 := by linarith [hs.1]
    linarith
  have hupper : (a : ℝ) ≤ E g.K₀ * g.r := by
    have hcenterUpper : (a : ℝ) ≤ s + 1 := by
      have h := abs_le.mp herr
      linarith [h.2]
    have hsum : 2 * g.r + 1 ≤ (2 + g.K₀ ^ 2) * g.r := by
      nlinarith [hrK]
    have hcoeff : (2 + g.K₀ ^ 2) * g.r ≤ E g.K₀ * g.r := by
      dsimp [E]
      nlinarith [le_of_lt hrpos]
    calc
      (a : ℝ) ≤ s + 1 := hcenterUpper
      _ ≤ 2 * g.r + 1 := by linarith [hs.2]
      _ ≤ (2 + g.K₀ ^ 2) * g.r := hsum
      _ ≤ E g.K₀ * g.r := hcoeff
  refine ⟨by simp, by norm_num, hQlo, ha, ?_, ?_⟩
  · simpa using hamin
  · simpa using hupper

/-- The nearest-integer cells cover the entire source slope interval in the
low-denominator case. -/
private theorem lowRationalCell_covers
    (g : HyperbolaGeometricData)
    (hlow : (g.Q : ℝ) < D g.K₀) :
    Set.Ioc (g.r / 4) (2 * g.r) ⊆
      ⋃ i ∈ (positiveRationalCellIndices g : Set (ℕ × ℕ)),
        positiveRationalCell g i.1 i.2 := by
  classical
  intro s hs
  have hrpos : 0 < g.r := by
    have hXpos : 0 < g.X := by linarith [g.X_ge_one]
    have hMpos : 0 < g.M := by linarith [g.M_ge_one]
    dsimp [HyperbolaGeometricData.r]
    exact div_pos hXpos (sq_pos_of_pos hMpos)
  have hspos : 0 < s := by linarith [hs.1, hrpos]
  obtain ⟨a, haAssign, ha, hnearest⟩ :=
    nearestIntegerRationalCell_assignment hspos
  have helig := lowNearestCenter_eligible g hs a ha hnearest
  have hindex : positiveRationalCellIndexEligible g a 1 :=
    ⟨helig, fun _ => rfl⟩
  have hmem := (positiveRationalCellIndices_mem_iff g a 1).2 hindex
  have hcell : s ∈ positiveRationalCell g a 1 := by
    have hcellEq : positiveRationalCell g a 1 =
        Set.Ioc (g.r / 4) (2 * g.r) ∩ nearestIntegerRationalCell a := by
      simp [positiveRationalCell, hlow]
    rw [hcellEq]
    exact ⟨hs, hnearest⟩
  refine Set.mem_iUnion.mpr ⟨(a, 1), ?_⟩
  simp only [Set.mem_iUnion]
  exact ⟨hmem, hcell⟩

/-- Dirichlet approximation supplies at least one eligible high-regime window
through every slope in the source interval. -/
private theorem exists_highRationalCellWindow
    (g : HyperbolaGeometricData)
    (hnotLow : ¬ (g.Q : ℝ) < D g.K₀)
    {s : ℝ} (hs : s ∈ Set.Ioc (g.r / 4) (2 * g.r)) :
    ∃ a q : ℕ, rationalCellEligible g a q ∧
      s ∈ rationalCellWindow g a q := by
  obtain ⟨aZ, qZ, hcop, hqlo, hqhi, happrox⟩ :=
    finiteDirichletApproximation s g.Q g.Q_pos
  have hKpos : 0 < g.K₀ := by linarith [g.K₀_ge_one]
  have hK2pos : 0 < g.K₀ ^ 2 := by nlinarith
  have hrpos : 0 < g.r := by
    have hXpos : 0 < g.X := by linarith [g.X_ge_one]
    have hMpos : 0 < g.M := by linarith [g.M_ge_one]
    dsimp [HyperbolaGeometricData.r]
    exact div_pos hXpos (sq_pos_of_pos hMpos)
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hDpos : 0 < D g.K₀ := by
    dsimp [D]
    positivity
  have hDge8 : (8 : ℝ) ≤ D g.K₀ := by
    dsimp [D]
    nlinarith [g.K₀_ge_one]
  have hQgeD : D g.K₀ ≤ (g.Q : ℝ) := le_of_not_gt hnotLow
  have hrlo : (g.K₀ ^ 2)⁻¹ ≤ g.r := by
    have hQlo : 1 ≤ g.Q := Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne'
    exact (admissibleParameterBounds g 1 (by omega) hQlo).r_lower
  have hDinv : (D g.K₀)⁻¹ = (g.K₀ ^ 2)⁻¹ / 8 := by
    dsimp [D]
    field_simp
  have hQradius : 1 / (g.Q : ℝ) ≤ g.r / 8 := by
    calc
      1 / (g.Q : ℝ) ≤ (D g.K₀)⁻¹ :=
        by simpa [one_div] using one_div_le_one_div_of_le hDpos hQgeD
      _ = (g.K₀ ^ 2)⁻¹ / 8 := hDinv
      _ ≤ g.r / 8 := div_le_div_of_nonneg_right hrlo (by norm_num)
  have hqReal : (1 : ℝ) ≤ (qZ : ℝ) := by exact_mod_cast hqlo
  have hqRealPos : 0 < (qZ : ℝ) := by linarith
  have hqRealUpper : (qZ : ℝ) ≤ (g.Q : ℝ) := by exact_mod_cast hqhi
  have hQqPos : 0 < (g.Q : ℝ) * (qZ : ℝ) := mul_pos hQpos hqRealPos
  have hwindowRadius :
      1 / ((g.Q : ℝ) * (qZ : ℝ)) ≤ g.r / 8 := by
    have hprod : (g.Q : ℝ) ≤ (g.Q : ℝ) * (qZ : ℝ) := by
      calc
        (g.Q : ℝ) = (g.Q : ℝ) * 1 := by ring
        _ ≤ (g.Q : ℝ) * (qZ : ℝ) :=
          mul_le_mul_of_nonneg_left hqReal hQpos.le
    exact (one_div_le_one_div hQqPos hQpos).2 hprod |>.trans hQradius
  have habs := abs_lt.mp happrox
  have hscenterLower :
      s - 1 / ((g.Q : ℝ) * (qZ : ℝ)) < (aZ : ℝ) / (qZ : ℝ) := by
    linarith [habs.2]
  have hcenterLower : g.r / 8 < (aZ : ℝ) / (qZ : ℝ) := by
    linarith [hs.1, hwindowRadius]
  have hcenterUpper :
      (aZ : ℝ) / (qZ : ℝ) < 3 * g.r := by
    have hcenter_lt_s :
        (aZ : ℝ) / (qZ : ℝ) < s +
          1 / ((g.Q : ℝ) * (qZ : ℝ)) := by
      linarith [habs.1]
    linarith [hwindowRadius, hs.2, hrpos]
  have haZpos : 0 < aZ := by
    have hcenterPos : (0 : ℝ) < (aZ : ℝ) / (qZ : ℝ) :=
      lt_trans (by positivity : (0 : ℝ) < g.r / 8) hcenterLower
    have hreal : (0 : ℝ) < (aZ : ℝ) := by
      have := (lt_div_iff₀ hqRealPos).mp hcenterPos
      nlinarith
    exact_mod_cast hreal
  have hqZposInt : 0 < qZ := by omega
  have hqZposReal : (0 : ℝ) ≤ (qZ : ℝ) := by exact_mod_cast (le_of_lt hqZposInt)
  have hqCast : (qZ.natAbs : ℝ) = (qZ : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hqZposReal]
  have haNpos : 1 ≤ aZ.natAbs := by
    have haEq : (aZ.natAbs : ℤ) = aZ := Int.natAbs_of_nonneg haZpos.le
    rw [← haEq]
    omega
  have hqNpos : 1 ≤ qZ.natAbs := by
    have hnatR : (1 : ℝ) ≤ (qZ.natAbs : ℝ) := by
      rw [hqCast]
      exact_mod_cast hqlo
    exact_mod_cast hnatR
  have hqNle : qZ.natAbs ≤ g.Q := by
    have hnatR : (qZ.natAbs : ℝ) ≤ (g.Q : ℝ) := by
      rw [hqCast]
      exact_mod_cast hqhi
    exact_mod_cast hnatR
  have haCast : (aZ.natAbs : ℝ) = (aZ : ℝ) := by
    have haZposReal : (0 : ℝ) ≤ (aZ : ℝ) := by exact_mod_cast haZpos.le
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg haZposReal]
  have hqNatRealPos : (0 : ℝ) < (qZ.natAbs : ℝ) := by
    exact_mod_cast (show 0 < qZ.natAbs by omega)
  have hcenterLowerN : g.r / 8 <
      (aZ.natAbs : ℝ) / (qZ.natAbs : ℝ) := by
    rw [haCast, hqCast]
    exact hcenterLower
  have hcenterUpperN :
      (aZ.natAbs : ℝ) / (qZ.natAbs : ℝ) < 3 * g.r := by
    rw [haCast, hqCast]
    exact hcenterUpper
  have hamin :
      (g.r / 8) * (qZ.natAbs : ℝ) ≤ (aZ.natAbs : ℝ) := by
    have hmul := (lt_div_iff₀ hqNatRealPos).1 hcenterLowerN
    linarith
  have hEge3 : 3 ≤ E g.K₀ := by
    dsimp [E]
    nlinarith [sq_nonneg g.K₀]
  have hcenterUpperE :
      (aZ.natAbs : ℝ) / (qZ.natAbs : ℝ) ≤ E g.K₀ * g.r := by
    have : 3 * g.r ≤ E g.K₀ * g.r :=
      mul_le_mul_of_nonneg_right hEge3 hrpos.le
    exact hcenterUpperN.le.trans this
  have hamax :
      (aZ.natAbs : ℝ) ≤ E g.K₀ * g.r * (qZ.natAbs : ℝ) := by
    exact (div_le_iff₀ hqNatRealPos).1 hcenterUpperE
  have hEligible : rationalCellEligible g aZ.natAbs qZ.natAbs := by
    refine ⟨hcop, hqNpos, hqNle, haNpos, hamin, hamax⟩
  have hwindow :
      s ∈ rationalCellWindow g aZ.natAbs qZ.natAbs := by
    have happrox' :
        |s - (aZ.natAbs : ℝ) / (qZ.natAbs : ℝ)| <
          1 / ((g.Q : ℝ) * (qZ.natAbs : ℝ)) := by
      simpa [haCast, hqCast] using happrox
    have habs := abs_lt.mp happrox'
    have hIcc :
        ((aZ.natAbs : ℝ) / (qZ.natAbs : ℝ) -
            1 / ((g.Q : ℝ) * (qZ.natAbs : ℝ))) ≤ s ∧
          s ≤ (aZ.natAbs : ℝ) / (qZ.natAbs : ℝ) +
            1 / ((g.Q : ℝ) * (qZ.natAbs : ℝ)) := by
      constructor <;> linarith [habs.1, habs.2]
    simpa [rationalCellWindow] using hIcc
  exact ⟨aZ.natAbs, qZ.natAbs, hEligible, hwindow⟩

/-- In the low-denominator construction, distinct denominator-one cells are
disjoint with their exact half-open endpoint convention. -/
private theorem lowRationalCell_pairwiseDisjoint
    (g : HyperbolaGeometricData)
    (hlow : (g.Q : ℝ) < D g.K₀)
    {a q b q' : ℕ}
    (hi : positiveRationalCellIndexEligible g a q)
    (hj : positiveRationalCellIndexEligible g b q')
    (hij : (a, q) ≠ (b, q')) :
    Disjoint (positiveRationalCell g a q)
      (positiveRationalCell g b q') := by
  rcases hi with ⟨helig, hqone⟩
  rcases hj with ⟨helig', hq'one⟩
  have hq : q = 1 := hqone hlow
  have hq' : q' = 1 := hq'one hlow
  subst q
  subst q'
  rcases helig with ⟨_, _, _, halo, _, _⟩
  rcases helig' with ⟨_, _, _, hbLo, _, _⟩
  have hab : a ≠ b := by
    intro hab
    exact hij (Prod.ext hab rfl)
  rw [Set.disjoint_left]
  intro s hs ht
  have hs' : s ∈ nearestIntegerRationalCell a := by
    have h := hs
    simp only [positiveRationalCell, hlow] at h
    exact h.2
  have ht' : s ∈ nearestIntegerRationalCell b := by
    have h := ht
    simp only [positiveRationalCell, hlow] at h
    exact h.2
  exact (Set.disjoint_left.mp
    (nearestIntegerRationalCell_disjoint halo hbLo hab)) hs' ht'

/-- The high-regime construction covers the slope interval by assigning each
point to its least eligible denominator. -/
private theorem highRationalCell_covers
    (g : HyperbolaGeometricData)
    (hnotLow : ¬ (g.Q : ℝ) < D g.K₀) :
    Set.Ioc (g.r / 4) (2 * g.r) ⊆
      ⋃ i ∈ (positiveRationalCellIndices g : Set (ℕ × ℕ)),
        positiveRationalCell g i.1 i.2 := by
  classical
  intro s hs
  obtain ⟨a, q, helig, hswindow⟩ :=
    exists_highRationalCellWindow g hnotLow hs
  let P : ℕ → Prop := fun q =>
    ∃ a, rationalCellEligible g a q ∧ s ∈ rationalCellWindow g a q
  have hP : ∃ q, P q := ⟨q, a, helig, hswindow⟩
  let q₀ := Nat.find hP
  have hP₀ : P q₀ := Nat.find_spec hP
  rcases hP₀ with ⟨a₀, helig₀, hswindow₀⟩
  have hmin : ∀ q', q' < q₀ → ¬ P q' := by
    intro q' hq' hP'
    have hle := Nat.find_min' hP hP'
    omega
  have hsnot : s ∉ lowerRationalCellWindows g q₀ := by
    intro hblocked
    rcases hblocked with ⟨a', q', helig', hq', hswindow'⟩
    exact hmin q' hq' ⟨a', helig', hswindow'⟩
  have hcell : s ∈ positiveRationalCell g a₀ q₀ := by
    simp only [positiveRationalCell, hnotLow]
    exact ⟨hs, hswindow₀, hsnot⟩
  have hindex : positiveRationalCellIndexEligible g a₀ q₀ :=
    ⟨helig₀, fun hlow => (hnotLow hlow).elim⟩
  have hmem := (positiveRationalCellIndices_mem_iff g a₀ q₀).2 hindex
  refine Set.mem_iUnion.mpr ⟨(a₀, q₀), ?_⟩
  simp only [Set.mem_iUnion]
  exact ⟨hmem, hcell⟩

/-- Low-regime cells satisfy the exact displayed approximation bound. -/
private theorem lowRationalCell_approximation
    (g : HyperbolaGeometricData) {a q : ℕ}
    (hlow : (g.Q : ℝ) < D g.K₀)
    (hindex : positiveRationalCellIndexEligible g a q)
    {s : ℝ} (hs : s ∈ positiveRationalCell g a q) :
    |s - (a : ℝ) / (q : ℝ)| ≤
      D g.K₀ / ((g.Q : ℝ) * (q : ℝ)) := by
  rcases hindex with ⟨helig, hqone⟩
  rcases helig with ⟨_, hqlo, _, halo, _, _⟩
  have hq : q = 1 := hqone hlow
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hKpos : 0 < g.K₀ := by linarith [g.K₀_ge_one]
  have hDpos : 0 < D g.K₀ := by
    dsimp [D]
    positivity
  have hQltD : (g.Q : ℝ) < D g.K₀ := hlow
  have honele : 1 ≤ D g.K₀ / (g.Q : ℝ) := by
    apply (le_div_iff₀ hQpos).2
    nlinarith
  have hs' : s ∈ nearestIntegerRationalCell a := by
    have hs' := hs
    simp [positiveRationalCell, hlow, hq] at hs'
    exact hs'.2
  have herr := nearestIntegerRationalCell_error halo hs'
  rw [hq]
  simpa [mul_one, one_div] using le_trans herr (by
    have hqpos : (0 : ℝ) < 1 := by norm_num
    have hbound : 1 ≤ D g.K₀ / (g.Q : ℝ) := honele
    nlinarith [herr])

/-- High-regime window membership gives the stated enlarged error bound. -/
private theorem highRationalCell_approximation
    (g : HyperbolaGeometricData) {a q : ℕ}
    (hnotLow : ¬ (g.Q : ℝ) < D g.K₀)
    (helig : rationalCellEligible g a q)
    {s : ℝ} (hs : s ∈ positiveRationalCell g a q) :
    |s - (a : ℝ) / (q : ℝ)| ≤
      D g.K₀ / ((g.Q : ℝ) * (q : ℝ)) := by
  classical
  rcases helig with ⟨_, hqlo, hqhi, _, _, _⟩
  have hqpos : 0 < q := by omega
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hqposR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hdenpos : 0 < (g.Q : ℝ) * (q : ℝ) := mul_pos hQpos hqposR
  have hDge : 1 ≤ D g.K₀ := by
    dsimp [D]
    nlinarith [g.K₀_ge_one]
  have hs' : s ∈ rationalCellWindow g a q := by
    have hs' := hs
    simp only [positiveRationalCell, hnotLow] at hs'
    exact hs'.2.1
  have hsWin :
      (a : ℝ) / (q : ℝ) - 1 / ((g.Q : ℝ) * (q : ℝ)) ≤ s ∧
      s ≤ (a : ℝ) / (q : ℝ) + 1 / ((g.Q : ℝ) * (q : ℝ)) := by
    simpa [rationalCellWindow] using hs'
  have herr : |s - (a : ℝ) / (q : ℝ)| ≤
      1 / ((g.Q : ℝ) * (q : ℝ)) := by
    apply abs_le.mpr
    constructor <;> linarith [hsWin.1, hsWin.2]
  apply le_trans herr
  rw [div_le_div_iff₀ hdenpos hdenpos]
  nlinarith [hDge, hdenpos]

/-- At one denominator, distinct eligible numerators have separated centers. -/
private theorem sameDenominatorCenter_separation {a b q : ℕ}
    (hq : 0 < q) (hab : a ≠ b) :
    1 / (q : ℝ) ≤ |(a : ℝ) / (q : ℝ) - (b : ℝ) / (q : ℝ)| := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  rcases lt_or_gt_of_ne hab with hablt | habgt
  · have hgap : (a : ℝ) + 1 ≤ (b : ℝ) := by
      have hn : a + 1 ≤ b := Nat.succ_le_of_lt hablt
      exact_mod_cast hn
    have hdiff :
        (a : ℝ) / (q : ℝ) - (b : ℝ) / (q : ℝ) =
          ((a : ℝ) - (b : ℝ)) / (q : ℝ) := by
      field_simp
    have hnum : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
      rw [abs_of_neg (sub_neg.mpr (by linarith))]
      linarith
    rw [hdiff, abs_div, abs_of_pos hqR]
    rw [div_le_div_iff₀ hqR hqR]
    simpa using (mul_le_mul_of_nonneg_right hnum hqR.le)
  · have hgap : (b : ℝ) + 1 ≤ (a : ℝ) := by
      have hn : b + 1 ≤ a := Nat.succ_le_of_lt habgt
      exact_mod_cast hn
    have hdiff :
        (a : ℝ) / (q : ℝ) - (b : ℝ) / (q : ℝ) =
          ((a : ℝ) - (b : ℝ)) / (q : ℝ) := by
      field_simp
    have hnum : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
      rw [abs_of_pos (sub_pos.mpr (by linarith))]
      linarith
    rw [hdiff, abs_div, abs_of_pos hqR]
    rw [div_le_div_iff₀ hqR hqR]
    simpa using (mul_le_mul_of_nonneg_right hnum hqR.le)

/-- High-regime cells are pairwise disjoint: different denominators are
resolved by smallest-denominator ownership, and equal-denominator windows do
not overlap. -/
private theorem highRationalCell_pairwiseDisjoint
    (g : HyperbolaGeometricData)
    (hnotLow : ¬ (g.Q : ℝ) < D g.K₀)
    {a q b q' : ℕ}
    (hi : rationalCellEligible g a q)
    (hj : rationalCellEligible g b q')
    (hij : (a, q) ≠ (b, q')) :
    Disjoint (positiveRationalCell g a q)
      (positiveRationalCell g b q') := by
  classical
  rcases hi with ⟨hcop, hqlo, hqhi, halo, hamin, hamax⟩
  rcases hj with ⟨hcop', hq'lo, hq'hi, hbLo, hbmin, hbmax⟩
  rw [Set.disjoint_left]
  intro s hs ht
  by_cases hqq' : q = q'
  · subst q'
    have hab : a ≠ b := by
      intro hab
      exact hij (Prod.ext hab rfl)
    have hqpos : 0 < q := by omega
    have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
    have hqposR : 0 < (q : ℝ) := by exact_mod_cast hqpos
    have hQge8 : (8 : ℝ) ≤ (g.Q : ℝ) := by
      have hDge8 : (8 : ℝ) ≤ D g.K₀ := by
        dsimp [D]
        nlinarith [g.K₀_ge_one]
      exact hDge8.trans (le_of_not_gt hnotLow)
    have hsep := sameDenominatorCenter_separation hqpos hab
    have hrad :
        2 / ((g.Q : ℝ) * (q : ℝ)) < 1 / (q : ℝ) := by
      apply (div_lt_div_iff₀
        (mul_pos hQpos hqposR) hqposR).2
      nlinarith [hQge8, hqposR]
    have hs' : s ∈ rationalCellWindow g a q := by
      have h := hs
      simp only [positiveRationalCell, hnotLow] at h
      exact h.2.1
    have ht' : s ∈ rationalCellWindow g b q := by
      have h := ht
      simp only [positiveRationalCell, hnotLow] at h
      exact h.2.1
    have hsWin :
        (a : ℝ) / (q : ℝ) - 1 / ((g.Q : ℝ) * (q : ℝ)) ≤ s ∧
        s ≤ (a : ℝ) / (q : ℝ) + 1 / ((g.Q : ℝ) * (q : ℝ)) := by
      simpa [rationalCellWindow] using hs'
    have htWin :
        (b : ℝ) / (q : ℝ) - 1 / ((g.Q : ℝ) * (q : ℝ)) ≤ s ∧
        s ≤ (b : ℝ) / (q : ℝ) + 1 / ((g.Q : ℝ) * (q : ℝ)) := by
      simpa [rationalCellWindow] using ht'
    have hdist :
        |(a : ℝ) / (q : ℝ) - (b : ℝ) / (q : ℝ)| ≤
          2 / ((g.Q : ℝ) * (q : ℝ)) := by
      calc
        |(a : ℝ) / (q : ℝ) - (b : ℝ) / (q : ℝ)| ≤
            2 * (1 / ((g.Q : ℝ) * (q : ℝ))) := by
          apply abs_le.mpr
          constructor
          · linarith [htWin.1, hsWin.2]
          · linarith [hsWin.1, htWin.2]
        _ = 2 / ((g.Q : ℝ) * (q : ℝ)) := by ring
    linarith
  · rcases lt_or_gt_of_ne hqq' with hqLt | hqGt
    · have hsWin : s ∈ rationalCellWindow g a q := by
        have h := hs
        simp only [positiveRationalCell, hnotLow] at h
        exact h.2.1
      have htNot :
          s ∉ lowerRationalCellWindows g q' := by
        have h := ht
        simp only [positiveRationalCell, hnotLow] at h
        exact h.2.2
      exact htNot ⟨a, q, ⟨hcop, hqlo, hqhi, halo, hamin, hamax⟩,
        hqLt, hsWin⟩
    · have htWin : s ∈ rationalCellWindow g b q' := by
        have h := ht
        simp only [positiveRationalCell, hnotLow] at h
        exact h.2.1
      have hsNot :
          s ∉ lowerRationalCellWindows g q := by
        have h := hs
        simp only [positiveRationalCell, hnotLow] at h
        exact h.2.2
      exact hsNot ⟨b, q', ⟨hcop', hq'lo, hq'hi, hbLo, hbmin, hbmax⟩,
        hqGt, htWin⟩

/-- The finite deterministic partition of `(r/4,2r]` into positive rational
cells from `lhg:cells`, with the exact low/high denominator constructions. -/
theorem positiveRationalCellPartition (g : HyperbolaGeometricData) :
    PositiveRationalCellPartition g := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact positiveRationalCellIndices_mem_iff g
  · intro a q helig
    by_cases hlow : (g.Q : ℝ) < D g.K₀
    · by_cases hq : q = 1
      · exact lowRationalCell_interval g hlow ⟨helig, fun _ => hq⟩
      · simp [positiveRationalCell, hlow, hq]
        exact Set.ordConnected_empty
    · exact highRationalCell_interval g hlow helig
  · intro a q helig
    by_cases hlow : (g.Q : ℝ) < D g.K₀
    · by_cases hq : q = 1
      · simp [positiveRationalCell, hlow, hq]
      · simp [positiveRationalCell, hlow, hq]
    · simp [positiveRationalCell, hlow]
  · intro a q helig s hs
    by_cases hlow : (g.Q : ℝ) < D g.K₀
    · by_cases hq : q = 1
      · have hindex : positiveRationalCellIndexEligible g a q :=
          ⟨helig, fun _ => hq⟩
        exact lowRationalCell_approximation g hlow hindex hs
      · have hcell : positiveRationalCell g a q = ∅ := by
          simp [positiveRationalCell, hlow, hq]
        rw [hcell] at hs
        exact hs.elim
    · exact highRationalCell_approximation g hlow helig hs
  · intro i hi j hj hij
    have hIndexI :=
      (positiveRationalCellIndices_mem_iff g i.1 i.2).1 hi
    have hIndexJ :=
      (positiveRationalCellIndices_mem_iff g j.1 j.2).1 hj
    by_cases hlow : (g.Q : ℝ) < D g.K₀
    · exact lowRationalCell_pairwiseDisjoint g hlow hIndexI hIndexJ hij
    · exact highRationalCell_pairwiseDisjoint g hlow
        hIndexI.1 hIndexJ.1 hij
  · by_cases hlow : (g.Q : ℝ) < D g.K₀
    · exact lowRationalCell_covers g hlow
    · exact highRationalCell_covers g hlow

end FractionalPrimes.Literature.Hyperbola
