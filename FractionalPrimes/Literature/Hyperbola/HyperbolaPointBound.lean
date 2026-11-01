module

public import FractionalPrimes.Literature.Hyperbola.HyperbolaProgressionPartition

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

/-- The positive numerators eligible at a fixed denominator. -/
noncomputable def hyperbolaEligibleNumerators
    (g : HyperbolaGeometricData) (q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (Nat.floor (E g.K₀ * g.r * (q : ℝ)))).filter
    (fun a => positiveRationalCellIndexEligible g a q)

/-- The set of all eligible direction pairs is the finite union, over
denominators, of the eligible numerator sets. -/
private theorem positiveRationalCellIndices_eq_numerator_biUnion
    (g : HyperbolaGeometricData) :
    positiveRationalCellIndices g =
      (Finset.Icc 1 g.Q).biUnion (fun q =>
        (hyperbolaEligibleNumerators g q).image (fun a => (a, q))) := by
  classical
  ext ⟨a, q⟩
  constructor
  · intro hmem
    have hidx := (positiveRationalCellIndices_mem_iff g a q).1 hmem
    rcases hidx.1 with ⟨_, hqlo, hqhi, halo, _, hamax⟩
    have haFloor : a ≤ Nat.floor (E g.K₀ * g.r * (q : ℝ)) :=
      Nat.le_floor (by simpa using hamax)
    refine Finset.mem_biUnion.mpr ⟨q, Finset.mem_Icc.mpr ⟨hqlo, hqhi⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨halo, haFloor⟩, hidx⟩, ?_⟩
    rfl
  · intro hmem
    rcases Finset.mem_biUnion.mp hmem with ⟨q', hq', himage⟩
    rcases Finset.mem_image.mp himage with ⟨a', ha', heq⟩
    rcases Finset.mem_filter.mp ha' with ⟨_, hidx⟩
    have hpair : (a', q') = (a, q) := heq
    cases hpair
    exact (positiveRationalCellIndices_mem_iff g a q).2 hidx

/-- The selected rational cells form a finite disjoint cover of the complete
hyperbola lattice. -/
private theorem hyperbolaLattice_ncard_eq_sum_cell_ncards
    (g : HyperbolaGeometricData) :
    g.lattice.ncard =
      ∑ i ∈ positiveRationalCellIndices g,
        (cellLinearSlice g i.1 i.2).ncard := by
  classical
  let I := positiveRationalCellIndices g
  let cell := fun i : ℕ × ℕ => cellLinearSlice g i.1 i.2
  have hQlo : 1 ≤ g.Q := Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne'
  have hcellFinite : ∀ i ∈ I, (cell i).Finite := by
    intro i hi
    have hidx := (positiveRationalCellIndices_mem_iff g i.1 i.2).1 (by simpa [I] using hi)
    have hparams := admissibleParameterBounds g i.2 hidx.1.2.1 hidx.1.2.2.1
    apply hparams.lattice_finite.subset
    intro p hp
    exact hp.1
  have hpair : (I : Set (ℕ × ℕ)).PairwiseDisjoint cell := by
    intro i hi j hj hij
    have hidxi := (positiveRationalCellIndices_mem_iff g i.1 i.2).1 (by simpa [I] using hi)
    have hidxj := (positiveRationalCellIndices_mem_iff g j.1 j.2).1 (by simpa [I] using hj)
    have hdisj :=
      (positiveRationalCellPartition g).pairwise_disjoint i (by simpa [I] using hi)
        j (by simpa [I] using hj) hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    change p ∈ g.lattice ∧
      ((p.2 : ℝ) / (p.1 : ℝ)) ∈ positiveRationalCell g i.1 i.2 at hpi
    change p ∈ g.lattice ∧
      ((p.2 : ℝ) / (p.1 : ℝ)) ∈ positiveRationalCell g j.1 j.2 at hpj
    exact (Set.disjoint_left.mp hdisj) hpi.2 hpj.2
  have hQcover : (⋃ i ∈ (I : Set (ℕ × ℕ)), cell i) = g.lattice := by
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hp⟩
      exact hp.1
    · intro hp
      have hpProps :=
        (admissibleParameterBounds g 1 (by norm_num) hQlo).lattice_point_properties p hp
      have hslope : (p.2 : ℝ) / (p.1 : ℝ) ∈ Set.Ioc (g.r / 4) (2 * g.r) :=
        ⟨hpProps.2.2.1, hpProps.2.2.2⟩
      rcases Set.mem_iUnion.mp
          ((positiveRationalCellPartition g).covers hslope) with ⟨i, hiUnion⟩
      rcases Set.mem_iUnion.mp hiUnion with ⟨hi, hcell⟩
      have hiI : i ∈ I := by simpa [I] using hi
      exact ⟨i, by simpa [I] using hiI, ⟨hp, hcell⟩⟩
  have hIfinite : (I : Set (ℕ × ℕ)).Finite := I.finite_toSet
  have hsum := hIfinite.ncard_biUnion (fun i hi => hcellFinite i (by simpa using hi)) hpair
  rw [hQcover] at hsum
  rw [finsum_mem_eq_finite_toFinset_sum _ hIfinite] at hsum
  simpa [I, cell] using hsum

/-- The numerator set in one denominator direction is no larger than the
source's `E*r*q+1` count. -/
private theorem hyperbolaEligibleNumerators_card_bound
    (g : HyperbolaGeometricData) (q : ℕ) :
    ((hyperbolaEligibleNumerators g q).card : ℝ) ≤
      E g.K₀ * g.r * (q : ℝ) + 1 := by
  classical
  let n := Nat.floor (E g.K₀ * g.r * (q : ℝ))
  have hsubset : hyperbolaEligibleNumerators g q ⊆ Finset.Icc 1 n := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hIccSubset : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro a ha
    rcases Finset.mem_Icc.mp ha with ⟨_, han⟩
    exact Finset.mem_range.mpr (by omega)
  have hcard : (hyperbolaEligibleNumerators g q).card ≤ n + 1 := by
    calc
      (hyperbolaEligibleNumerators g q).card ≤ (Finset.Icc 1 n).card :=
        Finset.card_le_card hsubset
      _ ≤ (Finset.range (n + 1)).card := Finset.card_le_card hIccSubset
      _ = n + 1 := Finset.card_range _
  have hErqNonneg : 0 ≤ E g.K₀ * g.r * (q : ℝ) := by
    have hE : 0 ≤ E g.K₀ := by dsimp [E]; positivity
    have hr : 0 ≤ g.r := by
      have hX : 0 < g.X := by linarith [g.X_ge_one]
      have hM : 0 < g.M := by linarith [g.M_ge_one]
      dsimp [HyperbolaGeometricData.r]
      exact le_of_lt (div_pos hX (sq_pos_of_pos hM))
    positivity
  have hfloor : (n : ℝ) ≤ E g.K₀ * g.r * (q : ℝ) := by
    dsimp [n]
    exact Nat.floor_le hErqNonneg
  have hcardReal : ((hyperbolaEligibleNumerators g q).card : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast hcard
  simpa [n] using hcardReal.trans (add_le_add hfloor (le_refl (1 : ℝ)))

/-- The two point-count budgets in the approved total-count summation
collapse to `H/Q` after multiplying by `r*q`. -/
private theorem hyperbola_rq_mul_Sq
    (g : HyperbolaGeometricData) (q : ℕ) (hq : 1 ≤ q) :
    g.r * (q : ℝ) * S_q g q = g.H / (g.Q : ℝ) := by
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have hMpos : 0 < g.M := by linarith [g.M_ge_one]
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hqpos : 0 < (q : ℝ) := by
    have hqNat : 0 < q := by omega
    exact_mod_cast hqNat
  dsimp [HyperbolaGeometricData.r, S_q]
  field_simp [ne_of_gt hXpos, ne_of_gt hMpos, ne_of_gt hQpos, ne_of_gt hqpos]

/-- The total cell-count contribution of one denominator direction is bounded
by the source's uniform summand. -/
private theorem hyperbolaPointBound_direction_contribution
    (g : HyperbolaGeometricData) (q : ℕ)
    (hqlo : 1 ≤ q) (hqhi : q ≤ g.Q) :
    (((hyperbolaEligibleNumerators g q).image (fun a => (a, q))).card : ℝ) *
        (C_point g.K₀ * S_q g q) ≤
      C_point g.K₀ * (E g.K₀ + g.K₀ ^ 2) * g.H / (g.Q : ℝ) := by
  classical
  let B := (hyperbolaEligibleNumerators g q).image (fun a => (a, q))
  have hparams := admissibleParameterBounds g q hqlo hqhi
  have hBcard : B.card ≤ (hyperbolaEligibleNumerators g q).card := by
    dsimp [B]
    exact Finset.card_image_le
  have hBcardReal : (B.card : ℝ) ≤
      ((hyperbolaEligibleNumerators g q).card : ℝ) := by
    exact_mod_cast hBcard
  have hBbound : (B.card : ℝ) ≤ E g.K₀ * g.r * (q : ℝ) + 1 := by
    exact hBcardReal.trans (hyperbolaEligibleNumerators_card_bound g q)
  have hKpos : 0 < g.K₀ := by linarith [g.K₀_ge_one]
  have hK2pos : 0 < g.K₀ ^ 2 := by positivity
  have hRscale : 1 ≤ g.K₀ ^ 2 * g.r := by
    have hdiv : 1 / (g.K₀ ^ 2) ≤ g.r := by
      simpa [one_div] using hparams.r_lower
    have hmul := (div_le_iff₀ hK2pos).mp hdiv
    simpa [mul_comm] using hmul
  have hqReal : 1 ≤ (q : ℝ) := by exact_mod_cast hqlo
  have hRscaleNonneg : 0 ≤ g.K₀ ^ 2 * g.r :=
    le_trans (by norm_num) hRscale
  have hK2rq : 1 ≤ g.K₀ ^ 2 * g.r * (q : ℝ) := by
    calc
      1 ≤ g.K₀ ^ 2 * g.r := hRscale
      _ = (g.K₀ ^ 2 * g.r) * 1 := by ring
      _ ≤ (g.K₀ ^ 2 * g.r) * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hqReal hRscaleNonneg
  have hAbsorb :
      E g.K₀ * g.r * (q : ℝ) + 1 ≤
        (E g.K₀ + g.K₀ ^ 2) * g.r * (q : ℝ) := by
    have hE : 0 ≤ E g.K₀ := by dsimp [E]; positivity
    nlinarith [hK2rq]
  have hCnonneg : 0 ≤ C_point g.K₀ := by
    dsimp [C_point, D, E]
    positivity
  have hSqnonneg : 0 ≤ S_q g q := le_trans zero_le_one hparams.S_lower
  have hCSnonneg : 0 ≤ C_point g.K₀ * S_q g q :=
    mul_nonneg hCnonneg hSqnonneg
  calc
    (B.card : ℝ) * (C_point g.K₀ * S_q g q) ≤
        (E g.K₀ * g.r * (q : ℝ) + 1) *
          (C_point g.K₀ * S_q g q) :=
      mul_le_mul_of_nonneg_right hBbound hCSnonneg
    _ ≤ (E g.K₀ + g.K₀ ^ 2) * g.r * (q : ℝ) *
          (C_point g.K₀ * S_q g q) :=
      mul_le_mul_of_nonneg_right hAbsorb hCSnonneg
    _ = C_point g.K₀ * (E g.K₀ + g.K₀ ^ 2) * g.H / (g.Q : ℝ) := by
      rw [show (E g.K₀ + g.K₀ ^ 2) * g.r * (q : ℝ) *
          (C_point g.K₀ * S_q g q) =
          C_point g.K₀ * (E g.K₀ + g.K₀ ^ 2) *
            (g.r * (q : ℝ) * S_q g q) by ring,
        hyperbola_rq_mul_Sq g q hqlo]
      ring

/-- The exact uniform lattice-point bound in the approved hyperbola
closure: the sum of the rational-cell point counts is at most
`C_point (E + K₀²) H`. -/
theorem hyperbolaPointBound (g : HyperbolaGeometricData) :
    (g.lattice.ncard : ℝ) ≤
      C_point g.K₀ * (E g.K₀ + g.K₀ ^ 2) * g.H := by
  classical
  let qSet := Finset.Icc 1 g.Q
  let B := fun q =>
    (hyperbolaEligibleNumerators g q).image (fun a => (a, q))
  have hlattice_real :
      (g.lattice.ncard : ℝ) =
        ∑ i ∈ positiveRationalCellIndices g,
          ((cellLinearSlice g i.1 i.2).ncard : ℝ) := by
    exact_mod_cast hyperbolaLattice_ncard_eq_sum_cell_ncards g
  have hcell_sum :
      (∑ i ∈ positiveRationalCellIndices g,
          ((cellLinearSlice g i.1 i.2).ncard : ℝ)) ≤
        ∑ i ∈ positiveRationalCellIndices g,
          C_point g.K₀ * S_q g i.2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact rationalCellPointCount g i.1 i.2
      ((positiveRationalCellIndices_mem_iff g i.1 i.2).1 hi)
  have hB_disjoint : Set.PairwiseDisjoint (↑qSet : Set ℕ) B := by
    intro q hq q' hq' hne
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    rcases Finset.mem_image.mp hp with ⟨a, _, hpa⟩
    rcases Finset.mem_image.mp hp' with ⟨a', _, hpa'⟩
    have hpair : (a, q) = (a', q') := hpa.trans hpa'.symm
    exact hne (congrArg Prod.snd hpair)
  have hsum_split :
      (∑ i ∈ positiveRationalCellIndices g,
          C_point g.K₀ * S_q g i.2) =
        ∑ q ∈ qSet, ∑ p ∈ B q, C_point g.K₀ * S_q g p.2 := by
    rw [positiveRationalCellIndices_eq_numerator_biUnion]
    exact Finset.sum_biUnion hB_disjoint
  have hinner (q : ℕ) :
      (∑ p ∈ B q, C_point g.K₀ * S_q g p.2) =
        (B q).card * (C_point g.K₀ * S_q g q) := by
    calc
      (∑ p ∈ B q, C_point g.K₀ * S_q g p.2) =
          ∑ p ∈ B q, C_point g.K₀ * S_q g q := by
        apply Finset.sum_congr rfl
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨a, _, rfl⟩
        rfl
      _ = (B q).card * (C_point g.K₀ * S_q g q) := by simp
  have hsum_direction :
      (∑ q ∈ qSet,
          (B q).card * (C_point g.K₀ * S_q g q)) ≤
        ∑ q ∈ qSet,
          C_point g.K₀ * (E g.K₀ + g.K₀ ^ 2) * g.H /
            (g.Q : ℝ) := by
    apply Finset.sum_le_sum
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨hqlo, hqhi⟩
    simpa [B] using
      hyperbolaPointBound_direction_contribution g q hqlo hqhi
  have hqSet_card : qSet.card = g.Q := by
    dsimp [qSet]
    simp
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hsum_constant :
      (∑ q ∈ qSet,
          C_point g.K₀ * (E g.K₀ + g.K₀ ^ 2) * g.H /
            (g.Q : ℝ)) =
        C_point g.K₀ * (E g.K₀ + g.K₀ ^ 2) * g.H := by
    simp only [Finset.sum_const, hqSet_card, nsmul_eq_mul]
    field_simp [ne_of_gt hQpos]
  calc
    (g.lattice.ncard : ℝ) =
        ∑ i ∈ positiveRationalCellIndices g,
          ((cellLinearSlice g i.1 i.2).ncard : ℝ) := hlattice_real
    _ ≤ ∑ i ∈ positiveRationalCellIndices g,
          C_point g.K₀ * S_q g i.2 := hcell_sum
    _ = ∑ q ∈ qSet, ∑ p ∈ B q, C_point g.K₀ * S_q g p.2 := hsum_split
    _ = ∑ q ∈ qSet,
          (B q).card * (C_point g.K₀ * S_q g q) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hinner q
    _ ≤ ∑ q ∈ qSet,
          C_point g.K₀ * (E g.K₀ + g.K₀ ^ 2) * g.H /
            (g.Q : ℝ) := hsum_direction
    _ = C_point g.K₀ * (E g.K₀ + g.K₀ ^ 2) * g.H := hsum_constant

#print axioms FractionalPrimes.Literature.Hyperbola.hyperbolaPointBound
