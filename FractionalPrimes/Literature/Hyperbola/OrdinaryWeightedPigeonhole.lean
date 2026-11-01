module

public import FractionalPrimes.Literature.Hyperbola.HyperbolaProgressionPartition
public import FractionalPrimes.Literature.Hyperbola.ResiduePrefixSelection
public import FractionalPrimes.Literature.Hyperbola.CoordinateProgressionIntersection
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import FractionalPrimes.Literature.Uniformity.TotalVariationCalculusPackage

set_option maxHeartbeats 800000

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

open FractionalPrimes.Literature.Uniformity

private theorem listAdjacentVariation_cons (g : ℤ → ℂ) (a : ℤ)
    (l : List ℤ) :
    listAdjacentVariation g (a :: l) =
      (match l with
       | [] => 0
       | b :: _ => ‖g b - g a‖) + listAdjacentVariation g l := by
  cases l <;> simp [listAdjacentVariation, List.consecutivePairs,
    List.zip, List.tail]

private theorem listAdjacentVariation_cons_cons
    (g : ℤ → ℂ) (a b : ℤ) (l : List ℤ) :
    listAdjacentVariation g (a :: b :: l) =
      ‖g b - g a‖ + listAdjacentVariation g (b :: l) := by
  simpa using listAdjacentVariation_cons g a (b :: l)

private theorem listSupNorm_congr_on (g h : ℤ → ℂ) (l : List ℤ)
    (heq : ∀ n ∈ l, g n = h n) :
    listSupNorm g l = listSupNorm h l := by
  unfold listSupNorm
  have hmap : l.map (fun n => ‖g n‖) = l.map (fun n => ‖h n‖) := by
    apply List.map_congr_left
    intro n hn
    rw [heq n hn]
  rw [hmap]

private theorem listAdjacentVariation_congr_on
    (g h : ℤ → ℂ) (l : List ℤ)
    (heq : ∀ n ∈ l, g n = h n) :
    listAdjacentVariation g l = listAdjacentVariation h l := by
  induction l with
  | nil => simp [listAdjacentVariation, List.consecutivePairs,
      List.zip, List.tail]
  | cons a l ih =>
      cases l with
      | nil => simp [listAdjacentVariation, List.consecutivePairs,
          List.zip, List.tail]
      | cons b l =>
          have hab : ‖g b - g a‖ = ‖h b - h a‖ := by
            rw [heq b (by simp), heq a (by simp)]
          rw [listAdjacentVariation_cons_cons, listAdjacentVariation_cons_cons,
            hab, ih (fun n hn => heq n (by simp [hn]))]

private theorem finiteOrderedTotalVariation_congr_on
    (A : Finset ℤ) (g h : ℤ → ℂ)
    (heq : ∀ n ∈ A, g n = h n) :
    finiteOrderedTotalVariation A g = finiteOrderedTotalVariation A h := by
  unfold finiteOrderedTotalVariation
  rw [listSupNorm_congr_on g h (A.sort (· ≤ ·))
      (fun n hn => heq n
        ((Finset.mem_sort (s := A) (r := (· ≤ ·))).1 hn)),
    listAdjacentVariation_congr_on g h (A.sort (· ≤ ·))
      (fun n hn => heq n
        ((Finset.mem_sort (s := A) (r := (· ≤ ·))).1 hn))]

private theorem finiteIntegerInterval_one_mem (N : ℕ) (n : ℤ) :
    n ∈ (⟨1, N⟩ : FiniteIntegerInterval).points ↔
      1 ≤ n ∧ n ≤ (N : ℤ) := by
  change n ∈ arithmeticProgressionPoints 1 1 (by norm_num) N ↔ _
  simp only [arithmeticProgressionPoints, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hjval⟩
    have hjval' : n = 1 + (j : ℤ) := by simpa using hjval.symm
    constructor
    · rw [hjval']
      omega
    · rw [hjval']
      omega
  · rintro ⟨hnlo, hnhi⟩
    let j : ℕ := (n - 1).toNat
    have hjcast : (j : ℤ) = n - 1 := by
      dsimp [j]
      exact Int.toNat_of_nonneg (by omega)
    have hjltInt : (j : ℤ) < (N : ℤ) := by
      rw [hjcast]
      omega
    have hjlt : j < N := by exact_mod_cast hjltInt
    refine ⟨j, hjlt, ?_⟩
    rw [hjcast]
    ring

private noncomputable def ordinaryFirstInterval
    (g : HyperbolaGeometricData) : FiniteIntegerInterval :=
  ⟨1, Nat.floor (2 * g.M)⟩

private noncomputable def ordinarySecondInterval
    (g : HyperbolaGeometricData) : FiniteIntegerInterval :=
  ⟨1, Nat.floor (2 * g.X / g.M)⟩

private theorem ordinaryFirstInterval_positive
    (g : HyperbolaGeometricData) :
    ∀ n ∈ (ordinaryFirstInterval g).points, 0 < n := by
  intro n hn
  have hn' := (finiteIntegerInterval_one_mem _ n).1 hn
  exact_mod_cast hn'.1

private theorem ordinarySecondInterval_positive
    (g : HyperbolaGeometricData) :
    ∀ n ∈ (ordinarySecondInterval g).points, 0 < n := by
  intro n hn
  have hn' := (finiteIntegerInterval_one_mem _ n).1 hn
  exact_mod_cast hn'.1

private theorem ordinary_lattice_subset_rectangle
    (g : HyperbolaGeometricData) (Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice) :
    Λ ⊆ (ordinaryFirstInterval g).points ×ˢ
      (ordinarySecondInterval g).points := by
  classical
  intro p hp
  have hpL : p ∈ g.lattice := by
    have : p ∈ (Λ : Set (ℤ × ℤ)) := by simpa using hp
    rw [hΛ] at this
    exact this
  have hQlo : 1 ≤ g.Q := Nat.one_le_iff_ne_zero.mpr g.Q_pos.ne'
  have hgeom := (admissibleParameterBounds g 1 (by norm_num) hQlo)
  have hpdata := hgeom.lattice_point_properties p hpL
  have hpJ := g.J_subset hpL.1
  have hfirstLe : (p.1 : ℝ) ≤ 2 * g.M := hpJ.2
  have hp1nonneg : 0 ≤ p.1 := by omega
  have hp1cast : (p.1.toNat : ℝ) = (p.1 : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hp1nonneg)
  have hfirstNat : p.1.toNat ≤ Nat.floor (2 * g.M) := by
    apply Nat.le_floor
    rw [hp1cast]
    exact hfirstLe
  have hp1intcast : (p.1.toNat : ℤ) = p.1 := Int.toNat_of_nonneg hp1nonneg
  have hfirstInt : p.1 ≤ (Nat.floor (2 * g.M) : ℤ) := by
    rw [← hp1intcast]
    exact_mod_cast hfirstNat
  have hMpos : 0 < g.M := by linarith [g.M_ge_one]
  have hMlt : g.M < (p.1 : ℝ) := hpJ.1
  have hp2nonneg : 0 ≤ (p.2 : ℝ) := by exact_mod_cast hpdata.2.1.le
  have hproductLe :
      (p.1 : ℝ) * (p.2 : ℝ) ≤ 2 * g.X := by
    nlinarith [hpL.2.2, g.H_le_X]
  have hMproduct :
      g.M * (p.2 : ℝ) ≤ (p.1 : ℝ) * (p.2 : ℝ) :=
    mul_le_mul_of_nonneg_right hMlt.le hp2nonneg
  have hsecondLe : (p.2 : ℝ) ≤ 2 * g.X / g.M := by
    apply (le_div_iff₀ hMpos).2
    nlinarith [hMproduct, hproductLe]
  have hp2nonnegInt : 0 ≤ p.2 := by exact_mod_cast hpdata.2.1.le
  have hp2cast : (p.2.toNat : ℝ) = (p.2 : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hp2nonnegInt)
  have hsecondNat : p.2.toNat ≤ Nat.floor (2 * g.X / g.M) := by
    apply Nat.le_floor
    rw [hp2cast]
    exact hsecondLe
  have hp2intcast : (p.2.toNat : ℤ) = p.2 := Int.toNat_of_nonneg hp2nonnegInt
  have hsecondInt : p.2 ≤ (Nat.floor (2 * g.X / g.M) : ℤ) := by
    rw [← hp2intcast]
    exact_mod_cast hsecondNat
  apply Finset.mem_product.mpr
  constructor
  · exact (finiteIntegerInterval_one_mem _ _).2
      ⟨by exact_mod_cast hpdata.1, hfirstInt⟩
  · exact (finiteIntegerInterval_one_mem _ _).2
      ⟨by exact_mod_cast hpdata.2.1, hsecondInt⟩

private noncomputable def ordinaryPiecePoints
    (Λ' : Finset (ℤ × ℤ)) (P : Set (ℤ × ℤ)) : Finset (ℤ × ℤ) := by
  classical
  exact Λ'.filter fun p => p ∈ P

private noncomputable def ordinaryPieceAbsoluteSum
    (Λ' : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℂ)
    (P : Set (ℤ × ℤ)) : ℝ :=
  ‖∑ p ∈ ordinaryPiecePoints Λ' P, f p‖

private noncomputable def ordinaryDirectionMaximum
    (g : HyperbolaGeometricData) (Λ' : Finset (ℤ × ℤ))
    (f : ℤ × ℤ → ℂ) (a q : ℕ) : ℝ :=
  let vals := (hyperbolaProgressionFamily g a q).image
    (ordinaryPieceAbsoluteSum Λ' f)
  (insert 0 vals).sup' (by simp [vals]) id

private noncomputable def ordinaryDirectionContribution
    (g : HyperbolaGeometricData) (Λ' : Finset (ℤ × ℤ))
    (f : ℤ × ℤ → ℂ) (i : ℕ × ℕ) : ℝ :=
  (hyperbolaProgressionFamily g i.1 i.2).card *
    ordinaryDirectionMaximum g Λ' f i.1 i.2

private theorem ordinaryPieceAbsoluteSum_le_L0
    (g : HyperbolaGeometricData) (part : HyperbolaProgressionPartitionData g)
    (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q)
    (Λ' Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (hΛ' : Λ' ⊆ Λ)
    (f : ℤ × ℤ → ℂ)
    (hf : ∀ p, p ∈ g.lattice → ‖f p‖ ≤ 1)
    (P : Set (ℤ × ℤ)) (hP : P ∈ hyperbolaProgressionFamily g a q) :
    ordinaryPieceAbsoluteSum Λ' f P ≤ g.L0 := by
  classical
  let piece := ordinaryPiecePoints Λ' P
  have hpieces := part.pieces a q
    ((positiveRationalCellIndices_mem_iff g a q).2 hidx) P hP
  have hparams := admissibleParameterBounds g q hidx.1.2.1 hidx.1.2.2.1
  have hPfinite : P.Finite := hparams.lattice_finite.subset hpieces.2.2.1
  have hpieceSubset : (piece : Set (ℤ × ℤ)) ⊆ P := by
    intro p hp
    change p ∈ piece at hp
    dsimp [piece, ordinaryPiecePoints] at hp
    exact (Finset.mem_filter.mp hp).2
  have hcard : (piece.card : ℝ) ≤ P.ncard := by
    have hncard := Set.ncard_le_ncard hpieceSubset hPfinite
    rw [Set.ncard_coe_finset] at hncard
    exact_mod_cast hncard
  have hsum :
      ‖∑ p ∈ piece, f p‖ ≤ (piece.card : ℝ) := by
    calc
      ‖∑ p ∈ piece, f p‖ ≤ ∑ p ∈ piece, ‖f p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ piece, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpL : p ∈ g.lattice := by
          have hpFilter : p ∈ Λ' ∧ p ∈ P := by
            dsimp [piece, ordinaryPiecePoints] at hp
            exact Finset.mem_filter.mp hp
          have hpΛ : p ∈ Λ := hΛ' hpFilter.1
          have hpSet : p ∈ (Λ : Set (ℤ × ℤ)) := by simpa using hpΛ
          rw [hΛ] at hpSet
          exact hpSet
        exact hf p hpL
      _ = (piece.card : ℝ) := by simp
  calc
    ordinaryPieceAbsoluteSum Λ' f P = ‖∑ p ∈ piece, f p‖ := by rfl
    _ ≤ (piece.card : ℝ) := hsum
    _ ≤ P.ncard := hcard
    _ ≤ g.L0 := hpieces.2.1

private theorem ordinaryPieceAbsoluteSum_le_directionMaximum
    (g : HyperbolaGeometricData) (Λ' : Finset (ℤ × ℤ))
    (f : ℤ × ℤ → ℂ) (a q : ℕ)
    (P : Set (ℤ × ℤ)) (hP : P ∈ hyperbolaProgressionFamily g a q) :
    ordinaryPieceAbsoluteSum Λ' f P ≤
      ordinaryDirectionMaximum g Λ' f a q := by
  classical
  unfold ordinaryDirectionMaximum
  let vals := (hyperbolaProgressionFamily g a q).image
    (ordinaryPieceAbsoluteSum Λ' f)
  have hmem : ordinaryPieceAbsoluteSum Λ' f P ∈ insert 0 vals :=
    Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨P, hP, rfl⟩)
  exact Finset.le_sup' id hmem

private theorem zero_le_ordinaryDirectionMaximum
    (g : HyperbolaGeometricData) (Λ' : Finset (ℤ × ℤ))
    (f : ℤ × ℤ → ℂ) (a q : ℕ) :
    0 ≤ ordinaryDirectionMaximum g Λ' f a q := by
  classical
  unfold ordinaryDirectionMaximum
  let vals := (hyperbolaProgressionFamily g a q).image
    (ordinaryPieceAbsoluteSum Λ' f)
  exact Finset.le_sup' id (Finset.mem_insert_self 0 vals)

private theorem ordinaryDirectionMaximum_le_L0
    (g : HyperbolaGeometricData) (part : HyperbolaProgressionPartitionData g)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    (Λ' Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (hΛ' : Λ' ⊆ Λ)
    (f : ℤ × ℤ → ℂ)
    (hf : ∀ p, p ∈ g.lattice → ‖f p‖ ≤ 1) :
    ordinaryDirectionMaximum g Λ' f a q ≤ g.L0 := by
  classical
  unfold ordinaryDirectionMaximum
  let vals := (hyperbolaProgressionFamily g a q).image
    (ordinaryPieceAbsoluteSum Λ' f)
  have hparams := admissibleParameterBounds g q hidx.1.2.1 hidx.1.2.2.1
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with hxzero | hxval
  · have hL0nonneg : 0 ≤ g.L0 := le_trans (by norm_num) hparams.L0_lower
    simpa [hxzero] using hL0nonneg
  · rcases Finset.mem_image.mp hxval with ⟨P, hP, rfl⟩
    exact ordinaryPieceAbsoluteSum_le_L0 g part a q hidx Λ' Λ
      hΛ hΛ' f hf P hP

private theorem ordinary_norm_sum_le_partitionPieces
    (g : HyperbolaGeometricData)
    (part : HyperbolaProgressionPartitionData g)
    (Λ' : Finset (ℤ × ℤ))
    (hΛ' : ∀ p, p ∈ Λ' → p ∈ g.lattice)
    (f : ℤ × ℤ → ℂ) :
    ‖∑ p ∈ Λ', f p‖ ≤
      ∑ i ∈ positiveRationalCellIndices g,
        ∑ P ∈ hyperbolaProgressionFamily g i.1 i.2,
          ordinaryPieceAbsoluteSum Λ' f P := by
  classical
  let I := positiveRationalCellIndices g
  let F := globalHyperbolaProgressionFamily g
  let piece := fun P : Set (ℤ × ℤ) => ordinaryPiecePoints Λ' P
  have hcover :
      F.biUnion piece = Λ' := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨P, hP, hpP⟩
      have hpFilter : p ∈ Λ' ∧ p ∈ P := by
        dsimp [piece, ordinaryPiecePoints] at hpP
        exact Finset.mem_filter.mp hpP
      exact hpFilter.1
    · intro hpΛ
      have hpL : p ∈ g.lattice := hΛ' p hpΛ
      rcases (part.covers p).mp hpL with ⟨P, hP, hpP⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨P, hP, Finset.mem_filter.mpr ⟨hpΛ, hpP⟩⟩
  have hpiecePair : Set.PairwiseDisjoint (↑F : Set (Set (ℤ × ℤ))) piece := by
    intro P hP Q hQ hPQ
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    rcases Finset.mem_biUnion.mp hP with ⟨i, hi, hPi⟩
    rcases Finset.mem_biUnion.mp hQ with ⟨j, hj, hQj⟩
    have hpP : p ∈ P := by
      dsimp [piece, ordinaryPiecePoints] at hp
      exact (Finset.mem_filter.mp hp).2
    have hpQ : p ∈ Q := by
      dsimp [piece, ordinaryPiecePoints] at hp'
      exact (Finset.mem_filter.mp hp').2
    have hij : i ≠ j ∨ P ≠ Q := Or.inr hPQ
    have hdisj := part.pairwise_disjoint i hi j hj P hPi Q hQj hij
    exact (Set.disjoint_left.mp hdisj) hpP hpQ
  have hsumPiece :
      (∑ p ∈ Λ', f p) =
        ∑ P ∈ F, ∑ p ∈ piece P, f p := by
    calc
      (∑ p ∈ Λ', f p) = ∑ p ∈ F.biUnion piece, f p := by rw [hcover]
      _ = ∑ P ∈ F, ∑ p ∈ piece P, f p := Finset.sum_biUnion hpiecePair
  have hfamPair :
      Set.PairwiseDisjoint (↑I : Set (ℕ × ℕ))
        (fun i => hyperbolaProgressionFamily g i.1 i.2) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro P hP hP'
    have hdisj := part.pairwise_disjoint i hi j hj P hP P hP'
      (Or.inl hij)
    obtain ⟨p, hp⟩ := (part.pieces i.1 i.2 hi P hP).1
    exact (Set.disjoint_left.mp hdisj) hp hp
  have hsumFam :
      (∑ P ∈ F, ordinaryPieceAbsoluteSum Λ' f P) =
        ∑ i ∈ I,
          ∑ P ∈ hyperbolaProgressionFamily g i.1 i.2,
            ordinaryPieceAbsoluteSum Λ' f P := by
    dsimp [F, globalHyperbolaProgressionFamily, I]
    exact Finset.sum_biUnion hfamPair
  calc
    ‖∑ p ∈ Λ', f p‖ =
        ‖∑ P ∈ F, ∑ p ∈ piece P, f p‖ := by rw [hsumPiece]
    _ ≤ ∑ P ∈ F, ‖∑ p ∈ piece P, f p‖ := norm_sum_le _ _
    _ = ∑ P ∈ F, ordinaryPieceAbsoluteSum Λ' f P := by
      apply Finset.sum_congr rfl
      intro P hP
      rfl
    _ = ∑ i ∈ I,
        ∑ P ∈ hyperbolaProgressionFamily g i.1 i.2,
          ordinaryPieceAbsoluteSum Λ' f P := hsumFam

/-- The exact numerator-count constant `B₀=E+K₀²` in the ordinary
weighted hyperbola pigeonhole argument. -/
def ordinaryB0 (g : HyperbolaGeometricData) : ℝ :=
  E g.K₀ + g.K₀ ^ 2

/-- The exact threshold `τ=δ³/(4B₀C_geo)` in the ordinary weighted
hyperbola pigeonhole argument. -/
noncomputable def ordinaryTau
    (g : HyperbolaGeometricData) (δ : ℝ) : ℝ :=
  δ ^ 3 / (4 * ordinaryB0 g * C_geo g.K₀)

private noncomputable def ordinaryDirectionsAtDenominator
    (g : HyperbolaGeometricData) (q : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (positiveRationalCellIndices g).filter fun i => i.2 = q

private theorem ordinaryDirectionsAtDenominator_card_le
    (g : HyperbolaGeometricData) (q : ℕ)
    (hqlo : 1 ≤ q) (hqhi : q ≤ g.Q) :
    ((ordinaryDirectionsAtDenominator g q).card : ℝ) ≤
      E g.K₀ * g.r * (q : ℝ) + 1 := by
  classical
  let A := ordinaryDirectionsAtDenominator g q
  let n := Nat.floor (E g.K₀ * g.r * (q : ℝ))
  have hinj : Set.InjOn Prod.fst (A : Set (ℕ × ℕ)) := by
    intro i hi j hj hfirst
    have hiq := (Finset.mem_filter.mp (show i ∈ A from hi)).2
    have hjq := (Finset.mem_filter.mp (show j ∈ A from hj)).2
    apply Prod.ext
    · exact hfirst
    · exact hiq.trans hjq.symm
  have himage : A.image Prod.fst ⊆ Finset.Icc 1 n := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
    have hi' := (Finset.mem_filter.mp hi).1
    have hidx := (positiveRationalCellIndices_mem_iff g i.1 i.2).1 hi'
    rcases hidx.1 with ⟨_, _, _, haLo, _, haHi⟩
    have hiq : i.2 = q := (Finset.mem_filter.mp hi).2
    have haFloor : i.1 ≤ n := by
      apply Nat.le_floor
      simpa [n, hiq] using haHi
    exact Finset.mem_Icc.mpr ⟨haLo, haFloor⟩
  have hIccRange : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro a ha
    rcases Finset.mem_Icc.mp ha with ⟨_, han⟩
    exact Finset.mem_range.mpr (by omega)
  have hcard : A.card ≤ n + 1 := by
    calc
      A.card = (A.image Prod.fst).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 n).card := Finset.card_le_card himage
      _ ≤ (Finset.range (n + 1)).card := Finset.card_le_card hIccRange
      _ = n + 1 := Finset.card_range _
  have hErqNonneg : 0 ≤ E g.K₀ * g.r * (q : ℝ) := by
    have hE : 0 ≤ E g.K₀ := by dsimp [E]; positivity
    have hr : 0 < g.r := by
      dsimp [HyperbolaGeometricData.r]
      have hX : 0 < g.X := by linarith [g.X_ge_one]
      have hM : 0 < g.M := by linarith [g.M_ge_one]
      exact div_pos hX (sq_pos_of_pos hM)
    positivity
  have hnFloor : (n : ℝ) ≤ E g.K₀ * g.r * (q : ℝ) := by
    dsimp [n]
    exact Nat.floor_le hErqNonneg
  have hcardR : (A.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
  dsimp [A, ordinaryDirectionsAtDenominator]
  calc
    ((ordinaryDirectionsAtDenominator g q).card : ℝ) ≤ (n : ℝ) + 1 := hcardR
    _ ≤ E g.K₀ * g.r * (q : ℝ) + 1 := add_le_add hnFloor le_rfl

private theorem ordinaryDirectionsAtDenominator_card_le_B0
    (g : HyperbolaGeometricData) (q : ℕ)
    (hqlo : 1 ≤ q) (hqhi : q ≤ g.Q) :
    ((ordinaryDirectionsAtDenominator g q).card : ℝ) ≤
      ordinaryB0 g * g.r * (q : ℝ) := by
  have hparams := admissibleParameterBounds g q hqlo hqhi
  have hqReal : 1 ≤ (q : ℝ) := by exact_mod_cast hqlo
  have hKpos : 0 < g.K₀ := by linarith [g.K₀_ge_one]
  have hK2pos : 0 < g.K₀ ^ 2 := sq_pos_of_pos hKpos
  have hK2rq : 1 ≤ g.K₀ ^ 2 * g.r * (q : ℝ) := by
    have hbase : 1 ≤ g.K₀ ^ 2 * g.r := by
      have h := hparams.r_lower
      rw [inv_eq_one_div] at h
      simpa [mul_comm] using (div_le_iff₀ hK2pos).mp h
    have hbase0 : 0 ≤ g.K₀ ^ 2 * g.r := le_trans (by norm_num) hbase
    calc
      1 ≤ g.K₀ ^ 2 * g.r := hbase
      _ = (g.K₀ ^ 2 * g.r) * 1 := by ring
      _ ≤ (g.K₀ ^ 2 * g.r) * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hqReal hbase0
  have hE : 0 ≤ E g.K₀ := by dsimp [E]; positivity
  have hAbsorb : E g.K₀ * g.r * (q : ℝ) + 1 ≤
      ordinaryB0 g * g.r * (q : ℝ) := by
    dsimp [ordinaryB0]
    nlinarith [hK2rq]
  exact (ordinaryDirectionsAtDenominator_card_le g q hqlo hqhi).trans hAbsorb

private theorem ordinary_rq_mul_Sq
    (g : HyperbolaGeometricData) (q : ℕ) (hqlo : 1 ≤ q) :
    g.r * (q : ℝ) * S_q g q = g.H / (g.Q : ℝ) := by
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have hMpos : 0 < g.M := by linarith [g.M_ge_one]
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hqpos : 0 < (q : ℝ) := by
    have hq : 0 < q := by omega
    exact_mod_cast hq
  dsimp [HyperbolaGeometricData.r, S_q]
  field_simp [ne_of_gt hXpos, ne_of_gt hMpos,
    ne_of_gt hQpos, ne_of_gt hqpos]

private theorem ordinary_directionFiberContribution_le
    (g : HyperbolaGeometricData)
    (part : HyperbolaProgressionPartitionData g)
    (q : ℕ) (hqlo : 1 ≤ q) (hqhi : q ≤ g.Q)
    (Λ' Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (hΛ' : Λ' ⊆ Λ)
    (f : ℤ × ℤ → ℂ)
    (hf : ∀ p, p ∈ g.lattice → ‖f p‖ ≤ 1) :
    (∑ i ∈ ordinaryDirectionsAtDenominator g q,
      (hyperbolaProgressionFamily g i.1 i.2).card *
        ordinaryDirectionMaximum g Λ' f i.1 i.2) ≤
      ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ) := by
  classical
  let A := ordinaryDirectionsAtDenominator g q
  let G := C_geo g.K₀
  let B₀ := ordinaryB0 g
  let S := S_q g q
  have hparams := admissibleParameterBounds g q hqlo hqhi
  have hGpos : 0 < G := by
    dsimp [G, C_geo, C_point, C_line, D, E]
    positivity
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hparams.S_lower
  have hL0pos : 0 < g.L0 := lt_of_lt_of_le zero_lt_one hparams.L0_lower
  have hRL : R_q g q * g.L0 = S := by
    have hEq := hparams.S_div_L0_eq_R
    field_simp [ne_of_gt hL0pos] at hEq
    nlinarith [hEq]
  have hterm : ∀ i ∈ A,
      (hyperbolaProgressionFamily g i.1 i.2).card *
        ordinaryDirectionMaximum g Λ' f i.1 i.2 ≤ G * S := by
    intro i hi
    rcases i with ⟨a, q'⟩
    have hq' : q' = q := (Finset.mem_filter.mp hi).2
    subst q'
    have hidx := (positiveRationalCellIndices_mem_iff g a q).1
      (Finset.mem_filter.mp hi).1
    have hcount := part.count a q hidx
    have hU := ordinaryDirectionMaximum_le_L0 g part a q hidx
      Λ' Λ hΛ hΛ' f hf
    have hU0 := zero_le_ordinaryDirectionMaximum g Λ' f a q
    have hRqnonneg : 0 ≤ R_q g q := le_trans zero_le_one hparams.R_lower
    have hGnonneg : 0 ≤ G := hGpos.le
    calc
      (hyperbolaProgressionFamily g a q).card *
          ordinaryDirectionMaximum g Λ' f a q ≤
        (G * R_q g q) * ordinaryDirectionMaximum g Λ' f a q := by
          simpa [G] using mul_le_mul_of_nonneg_right hcount hU0
      _ ≤ (G * R_q g q) * g.L0 :=
          mul_le_mul_of_nonneg_left hU (mul_nonneg hGnonneg hRqnonneg)
      _ = G * (R_q g q * g.L0) := by ring
      _ = G * S := by rw [hRL]
  have hsumTerm :
      (∑ i ∈ A,
        (hyperbolaProgressionFamily g i.1 i.2).card *
          ordinaryDirectionMaximum g Λ' f i.1 i.2) ≤
        (A.card : ℝ) * (G * S) := by
    calc
      _ ≤ ∑ i ∈ A, G * S := by
        apply Finset.sum_le_sum
        intro i hi
        exact hterm i hi
      _ = (A.card : ℝ) * (G * S) := by simp [Finset.sum_const, nsmul_eq_mul]
  have hAcard := ordinaryDirectionsAtDenominator_card_le_B0 g q hqlo hqhi
  have hAterm := mul_le_mul_of_nonneg_right hAcard
    (mul_nonneg hGpos.le hSpos.le)
  have hfinal :
      (A.card : ℝ) * (G * S) ≤ B₀ * G * g.H / (g.Q : ℝ) := by
    calc
      (A.card : ℝ) * (G * S) ≤ (B₀ * g.r * (q : ℝ)) * (G * S) := hAterm
      _ = B₀ * G * (g.r * (q : ℝ) * S) := by ring
      _ = B₀ * G * g.H / (g.Q : ℝ) := by
        rw [ordinary_rq_mul_Sq g q hqlo]
        ring
  exact hsumTerm.trans hfinal

private theorem ordinary_totalContribution_le
    (g : HyperbolaGeometricData)
    (part : HyperbolaProgressionPartitionData g)
    (Λ' Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (hΛ' : Λ' ⊆ Λ)
    (f : ℤ × ℤ → ℂ)
    (hf : ∀ p, p ∈ g.lattice → ‖f p‖ ≤ 1) :
    (∑ i ∈ positiveRationalCellIndices g,
      (hyperbolaProgressionFamily g i.1 i.2).card *
        ordinaryDirectionMaximum g Λ' f i.1 i.2) ≤
      ordinaryB0 g * C_geo g.K₀ * g.H := by
  classical
  let I := positiveRationalCellIndices g
  let qset := Finset.Icc 1 g.Q
  let A := fun q => ordinaryDirectionsAtDenominator g q
  let contribution := fun i : ℕ × ℕ =>
    (hyperbolaProgressionFamily g i.1 i.2).card *
      ordinaryDirectionMaximum g Λ' f i.1 i.2
  have hdecomp : I = qset.biUnion A := by
    ext ⟨a, q⟩
    constructor
    · intro hi
      have hidx := (positiveRationalCellIndices_mem_iff g a q).1 hi
      rcases hidx.1 with ⟨_, hqlo, hqhi, _, _, _⟩
      refine Finset.mem_biUnion.mpr ⟨q, Finset.mem_Icc.mpr ⟨hqlo, hqhi⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hi, rfl⟩
    · intro hi
      rcases Finset.mem_biUnion.mp hi with ⟨q', hq', hmem⟩
      have hmem' := Finset.mem_filter.mp hmem
      have hpair : (a, q') = (a, q) := by
        apply Prod.ext
        · rfl
        · exact hmem'.2.symm
      have : (a, q') ∈ I := by simpa [hpair] using hmem'.1
      simpa [hpair] using this
  have hA_disjoint : Set.PairwiseDisjoint (↑qset : Set ℕ) A := by
    intro q hq q' hq' hneq
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    have hqmem := (Finset.mem_filter.mp hi).2
    have hqmem' := (Finset.mem_filter.mp hi').2
    exact hneq (hqmem.symm.trans hqmem')
  have hsumdecomp :
      (∑ i ∈ I, contribution i) =
        ∑ q ∈ qset, ∑ i ∈ A q, contribution i := by
    rw [hdecomp]
    exact Finset.sum_biUnion hA_disjoint
  have hsumBound :
      (∑ q ∈ qset, ∑ i ∈ A q, contribution i) ≤
        ∑ q ∈ qset, ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ) := by
    apply Finset.sum_le_sum
    intro q hq
    have hqmem := Finset.mem_Icc.mp hq
    exact ordinary_directionFiberContribution_le g part q hqmem.1 hqmem.2
      Λ' Λ hΛ hΛ' f hf
  have hcardQ : qset.card = g.Q := by
    simp [qset, Nat.card_Icc]
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hconst :
      (∑ q ∈ qset,
        ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ)) =
          ordinaryB0 g * C_geo g.K₀ * g.H := by
    rw [Finset.sum_const, nsmul_eq_mul, hcardQ]
    field_simp [ne_of_gt hQpos]
  calc
    (∑ i ∈ I, contribution i) =
        ∑ q ∈ qset, ∑ i ∈ A q, contribution i := hsumdecomp
    _ ≤ ∑ q ∈ qset,
        ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ) := hsumBound
    _ = ordinaryB0 g * C_geo g.K₀ * g.H := hconst

private theorem ordinary_directionFiberPieceCount_mul_L0_le
    (g : HyperbolaGeometricData)
    (part : HyperbolaProgressionPartitionData g)
    (q : ℕ) (hqlo : 1 ≤ q) (hqhi : q ≤ g.Q) :
    (∑ i ∈ ordinaryDirectionsAtDenominator g q,
      (hyperbolaProgressionFamily g i.1 i.2).card * g.L0) ≤
      ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ) := by
  classical
  let A := ordinaryDirectionsAtDenominator g q
  let G := C_geo g.K₀
  let B₀ := ordinaryB0 g
  let S := S_q g q
  have hparams := admissibleParameterBounds g q hqlo hqhi
  have hGpos : 0 < G := by
    dsimp [G, C_geo, C_point, C_line, D, E]
    positivity
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hparams.S_lower
  have hL0pos : 0 < g.L0 := lt_of_lt_of_le zero_lt_one hparams.L0_lower
  have hRL : R_q g q * g.L0 = S := by
    have hEq := hparams.S_div_L0_eq_R
    field_simp [ne_of_gt hL0pos] at hEq
    nlinarith [hEq]
  have hterm : ∀ i ∈ A,
      (hyperbolaProgressionFamily g i.1 i.2).card * g.L0 ≤ G * S := by
    intro i hi
    rcases i with ⟨a, q'⟩
    have hq' : q' = q := (Finset.mem_filter.mp hi).2
    subst q'
    have hidx := (positiveRationalCellIndices_mem_iff g a q).1
      (Finset.mem_filter.mp hi).1
    have hcount := part.count a q hidx
    have hRqnonneg : 0 ≤ R_q g q := le_trans zero_le_one hparams.R_lower
    have hGnonneg : 0 ≤ G := hGpos.le
    calc
      (hyperbolaProgressionFamily g a q).card * g.L0 ≤
          (G * R_q g q) * g.L0 :=
        mul_le_mul_of_nonneg_right hcount hL0pos.le
      _ = G * (R_q g q * g.L0) := by ring
      _ = G * S := by rw [hRL]
  have hsumTerm :
      (∑ i ∈ A,
        (hyperbolaProgressionFamily g i.1 i.2).card * g.L0) ≤
        (A.card : ℝ) * (G * S) := by
    calc
      _ ≤ ∑ i ∈ A, G * S := by
        apply Finset.sum_le_sum
        intro i hi
        exact hterm i hi
      _ = (A.card : ℝ) * (G * S) := by simp [Finset.sum_const, nsmul_eq_mul]
  have hAcard := ordinaryDirectionsAtDenominator_card_le_B0 g q hqlo hqhi
  have hAterm := mul_le_mul_of_nonneg_right hAcard
    (mul_nonneg hGpos.le hSpos.le)
  have hfinal :
      (A.card : ℝ) * (G * S) ≤ B₀ * G * g.H / (g.Q : ℝ) := by
    calc
      (A.card : ℝ) * (G * S) ≤ (B₀ * g.r * (q : ℝ)) * (G * S) := hAterm
      _ = B₀ * G * (g.r * (q : ℝ) * S) := by ring
      _ = B₀ * G * g.H / (g.Q : ℝ) := by
        rw [ordinary_rq_mul_Sq g q hqlo]
        ring
  exact hsumTerm.trans hfinal

private theorem ordinary_totalPieceCount_mul_L0_le
    (g : HyperbolaGeometricData)
    (part : HyperbolaProgressionPartitionData g) :
    (∑ i ∈ positiveRationalCellIndices g,
      (hyperbolaProgressionFamily g i.1 i.2).card * g.L0) ≤
      ordinaryB0 g * C_geo g.K₀ * g.H := by
  classical
  let I := positiveRationalCellIndices g
  let qset := Finset.Icc 1 g.Q
  let A := fun q => ordinaryDirectionsAtDenominator g q
  let contribution := fun i : ℕ × ℕ =>
    (hyperbolaProgressionFamily g i.1 i.2).card * g.L0
  have hdecomp : I = qset.biUnion A := by
    ext ⟨a, q⟩
    constructor
    · intro hi
      have hidx := (positiveRationalCellIndices_mem_iff g a q).1 hi
      rcases hidx.1 with ⟨_, hqlo, hqhi, _, _, _⟩
      refine Finset.mem_biUnion.mpr ⟨q, Finset.mem_Icc.mpr ⟨hqlo, hqhi⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hi, rfl⟩
    · intro hi
      rcases Finset.mem_biUnion.mp hi with ⟨q', hq', hmem⟩
      have hmem' := Finset.mem_filter.mp hmem
      have hpair : (a, q') = (a, q) := by
        apply Prod.ext
        · rfl
        · exact hmem'.2.symm
      have : (a, q') ∈ I := by simpa [hpair] using hmem'.1
      simpa [hpair] using this
  have hA_disjoint : Set.PairwiseDisjoint (↑qset : Set ℕ) A := by
    intro q hq q' hq' hneq
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    have hqmem := (Finset.mem_filter.mp hi).2
    have hqmem' := (Finset.mem_filter.mp hi').2
    exact hneq (hqmem.symm.trans hqmem')
  have hsumdecomp :
      (∑ i ∈ I, contribution i) =
        ∑ q ∈ qset, ∑ i ∈ A q, contribution i := by
    rw [hdecomp]
    exact Finset.sum_biUnion hA_disjoint
  have hsumBound :
      (∑ q ∈ qset, ∑ i ∈ A q, contribution i) ≤
        ∑ q ∈ qset, ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ) := by
    apply Finset.sum_le_sum
    intro q hq
    have hqmem := Finset.mem_Icc.mp hq
    exact ordinary_directionFiberPieceCount_mul_L0_le g part q hqmem.1 hqmem.2
  have hcardQ : qset.card = g.Q := by simp [qset, Nat.card_Icc]
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hconst :
      (∑ q ∈ qset,
        ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ)) =
          ordinaryB0 g * C_geo g.K₀ * g.H := by
    rw [Finset.sum_const, nsmul_eq_mul, hcardQ]
    field_simp [ne_of_gt hQpos]
  calc
    (∑ i ∈ I, contribution i) =
        ∑ q ∈ qset, ∑ i ∈ A q, contribution i := hsumdecomp
    _ ≤ ∑ q ∈ qset,
        ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ) := hsumBound
    _ = ordinaryB0 g * C_geo g.K₀ * g.H := hconst

private theorem ordinary_smallDenominatorCard_le
    (g : HyperbolaGeometricData) (τ : ℝ) (hτ : 0 ≤ τ) :
    (((Finset.Icc 1 g.Q).filter
        (fun q : ℕ => (q : ℝ) < τ * (g.Q : ℝ))).card : ℝ) ≤
      τ * (g.Q : ℝ) := by
  classical
  let qset := Finset.Icc 1 g.Q
  let small := qset.filter (fun q : ℕ => (q : ℝ) < τ * (g.Q : ℝ))
  let T := τ * (g.Q : ℝ)
  have hTnonneg : 0 ≤ T := mul_nonneg hτ (by positivity)
  have hsubset : small ⊆ Finset.Icc 1 (Nat.floor T) := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqFloor : q ≤ Nat.floor T := Nat.le_floor (le_of_lt hq'.2)
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq'.1).1, hqFloor⟩
  have hcard : small.card ≤ Nat.floor T := by
    calc
      small.card ≤ (Finset.Icc 1 (Nat.floor T)).card := Finset.card_le_card hsubset
      _ = Nat.floor T := by simp [Nat.card_Icc]
  have hfloor : (Nat.floor T : ℝ) ≤ T := Nat.floor_le hTnonneg
  have hcardR : (small.card : ℝ) ≤ (Nat.floor T : ℝ) := by exact_mod_cast hcard
  simpa [small, qset, T] using hcardR.trans hfloor

private theorem ordinary_smallDenominatorContribution_le
    (g : HyperbolaGeometricData)
    (part : HyperbolaProgressionPartitionData g)
    (Λ' Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (hΛ' : Λ' ⊆ Λ)
    (f : ℤ × ℤ → ℂ)
    (hf : ∀ p, p ∈ g.lattice → ‖f p‖ ≤ 1)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ i ∈ (positiveRationalCellIndices g).filter
        (fun i => (i.2 : ℝ) < τ * (g.Q : ℝ)),
      ordinaryDirectionContribution g Λ' f i) ≤
      τ * ordinaryB0 g * C_geo g.K₀ * g.H := by
  classical
  let I := positiveRationalCellIndices g
  let qset := (Finset.Icc 1 g.Q).filter
    (fun q : ℕ => (q : ℝ) < τ * (g.Q : ℝ))
  let A := fun q => ordinaryDirectionsAtDenominator g q
  let contribution := ordinaryDirectionContribution g Λ' f
  have hsmallUnion : qset.biUnion A = I.filter
      (fun i => (i.2 : ℝ) < τ * (g.Q : ℝ)) := by
    ext ⟨a, q⟩
    constructor
    · intro hi
      rcases Finset.mem_biUnion.mp hi with ⟨q', hq', hmem⟩
      have hmem' := Finset.mem_filter.mp hmem
      have hqeq : q = q' := by simpa using hmem'.2
      subst q'
      exact Finset.mem_filter.mpr ⟨hmem'.1,
        (Finset.mem_filter.mp hq').2⟩
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨hiI, hsmall⟩
      have hidx := (positiveRationalCellIndices_mem_iff g a q).1 hiI
      rcases hidx.1 with ⟨_, hqlo, hqhi, _, _, _⟩
      have hqset : q ∈ qset := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hqlo, hqhi⟩, hsmall⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨q, hqset, Finset.mem_filter.mpr ⟨hiI, rfl⟩⟩
  have hA_disjoint : Set.PairwiseDisjoint (↑qset : Set ℕ) A := by
    intro q hq q' hq' hneq
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    have hqmem := (Finset.mem_filter.mp hi).2
    have hqmem' := (Finset.mem_filter.mp hi').2
    exact hneq (hqmem.symm.trans hqmem')
  have hsumdecomp :
      (∑ i ∈ I.filter (fun i => (i.2 : ℝ) < τ * (g.Q : ℝ)), contribution i) =
        ∑ q ∈ qset, ∑ i ∈ A q, contribution i := by
    rw [← hsmallUnion]
    exact Finset.sum_biUnion hA_disjoint
  have hsumBound :
      (∑ q ∈ qset, ∑ i ∈ A q, contribution i) ≤
        ∑ q ∈ qset, ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ) := by
    apply Finset.sum_le_sum
    intro q hq
    have hqmem := Finset.mem_filter.mp hq
    have hqIcc := Finset.mem_Icc.mp hqmem.1
    exact ordinary_directionFiberContribution_le g part q hqIcc.1 hqIcc.2
      Λ' Λ hΛ hΛ' f hf
  have hcardQ := ordinary_smallDenominatorCard_le g τ hτ
  have hB0pos : 0 < ordinaryB0 g := by
    dsimp [ordinaryB0, E]
    positivity
  have hCpos : 0 < C_geo g.K₀ := by
    dsimp [C_geo, C_point, C_line, D, E]
    positivity
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hconstNonneg : 0 ≤
      ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ) := by
    positivity
  have hcardmul := mul_le_mul_of_nonneg_right hcardQ hconstNonneg
  have hscale :
      (((Finset.Icc 1 g.Q).filter
        (fun q : ℕ => (q : ℝ) < τ * (g.Q : ℝ))).card : ℝ) *
        (ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ)) ≤
          τ * ordinaryB0 g * C_geo g.K₀ * g.H := by
    calc
      _ ≤ (τ * (g.Q : ℝ)) *
          (ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ)) := hcardmul
      _ = τ * ordinaryB0 g * C_geo g.K₀ * g.H := by
        field_simp [ne_of_gt hQpos]
  have hsumConst :
      (∑ q ∈ qset,
        ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ)) =
          (qset.card : ℝ) *
            (ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ)) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ i ∈ I.filter (fun i => (i.2 : ℝ) < τ * (g.Q : ℝ)), contribution i) =
        ∑ q ∈ qset, ∑ i ∈ A q, contribution i := hsumdecomp
    _ ≤ ∑ q ∈ qset,
        ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ) := hsumBound
    _ = (qset.card : ℝ) *
        (ordinaryB0 g * C_geo g.K₀ * g.H / (g.Q : ℝ)) := hsumConst
    _ ≤ τ * ordinaryB0 g * C_geo g.K₀ * g.H := by
      simpa [qset] using hscale

private theorem ordinary_smallMaximumContribution_le
    (g : HyperbolaGeometricData)
    (part : HyperbolaProgressionPartitionData g)
    (Λ' Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (hΛ' : Λ' ⊆ Λ)
    (f : ℤ × ℤ → ℂ)
    (hf : ∀ p, p ∈ g.lattice → ‖f p‖ ≤ 1)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ i ∈ (positiveRationalCellIndices g).filter
        (fun i => ordinaryDirectionMaximum g Λ' f i.1 i.2 < τ * g.L0),
      ordinaryDirectionContribution g Λ' f i) ≤
      τ * ordinaryB0 g * C_geo g.K₀ * g.H := by
  classical
  let I := positiveRationalCellIndices g
  let small := I.filter
    (fun i => ordinaryDirectionMaximum g Λ' f i.1 i.2 < τ * g.L0)
  let pieceCount := fun i : ℕ × ℕ =>
    (hyperbolaProgressionFamily g i.1 i.2).card * g.L0
  have hsmallSubset : small ⊆ I := Finset.filter_subset _ _
  have hpoint : ∀ i ∈ small,
      ordinaryDirectionContribution g Λ' f i ≤ τ * pieceCount i := by
    intro i hi
    have hU := (Finset.mem_filter.mp hi).2
    have hNnonneg :
        0 ≤ ((hyperbolaProgressionFamily g i.1 i.2).card : ℝ) := Nat.cast_nonneg _
    dsimp [ordinaryDirectionContribution, pieceCount]
    calc
      (hyperbolaProgressionFamily g i.1 i.2).card *
          ordinaryDirectionMaximum g Λ' f i.1 i.2 ≤
        (hyperbolaProgressionFamily g i.1 i.2).card * (τ * g.L0) :=
          mul_le_mul_of_nonneg_left hU.le hNnonneg
      _ = τ * ((hyperbolaProgressionFamily g i.1 i.2).card * g.L0) := by ring
  have hsumSmall :
      (∑ i ∈ small, ordinaryDirectionContribution g Λ' f i) ≤
        ∑ i ∈ small, τ * pieceCount i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i hi
  have hsumSubset :
      (∑ i ∈ small, τ * pieceCount i) ≤
        ∑ i ∈ I, τ * pieceCount i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsmallSubset (by
      intro i hi hnot
      have hidx := (positiveRationalCellIndices_mem_iff g i.1 i.2).1 hi
      have hparams := admissibleParameterBounds g i.2
        hidx.1.2.1 hidx.1.2.2.1
      have hL0nonneg : 0 ≤ g.L0 := le_trans (by norm_num) hparams.L0_lower
      dsimp [pieceCount]
      positivity)
  have hsumScale :
      (∑ i ∈ I, τ * pieceCount i) =
        τ * (∑ i ∈ I, pieceCount i) := by
    rw [Finset.mul_sum]
  have hpiece := ordinary_totalPieceCount_mul_L0_le g part
  have htotal := mul_le_mul_of_nonneg_left hpiece hτ
  calc
    (∑ i ∈ I.filter
        (fun i => ordinaryDirectionMaximum g Λ' f i.1 i.2 < τ * g.L0),
      ordinaryDirectionContribution g Λ' f i) =
        ∑ i ∈ small, ordinaryDirectionContribution g Λ' f i := by
          rfl
    _ ≤ ∑ i ∈ small, τ * pieceCount i := hsumSmall
    _ ≤ ∑ i ∈ I, τ * pieceCount i := hsumSubset
    _ = τ * (∑ i ∈ I, pieceCount i) := hsumScale
    _ ≤ τ * (ordinaryB0 g * C_geo g.K₀ * g.H) := by
      simpa [pieceCount] using htotal
    _ = τ * ordinaryB0 g * C_geo g.K₀ * g.H := by ring

private theorem ordinary_sumPieceAbsoluteSum_le_directionContribution
    (g : HyperbolaGeometricData) (Λ' : Finset (ℤ × ℤ))
    (f : ℤ × ℤ → ℂ) (a q : ℕ) :
    (∑ P ∈ hyperbolaProgressionFamily g a q,
      ordinaryPieceAbsoluteSum Λ' f P) ≤
      ordinaryDirectionContribution g Λ' f (a, q) := by
  classical
  calc
    (∑ P ∈ hyperbolaProgressionFamily g a q,
        ordinaryPieceAbsoluteSum Λ' f P) ≤
      ∑ P ∈ hyperbolaProgressionFamily g a q,
        ordinaryDirectionMaximum g Λ' f a q := by
          apply Finset.sum_le_sum
          intro P hP
          exact ordinaryPieceAbsoluteSum_le_directionMaximum
            g Λ' f a q P hP
    _ = ordinaryDirectionContribution g Λ' f (a, q) := by
      simp [ordinaryDirectionContribution, Finset.sum_const, nsmul_eq_mul]

/-- A finite set supported in a rectangle can be summed by first summing in
the second coordinate.  Membership in the finite set is retained as an
indicator, so no extension-by-zero convention is implicit. -/
theorem finiteRectangleSum_eq
    {Λ : Finset (ℤ × ℤ)} {I J : Finset ℤ}
    (hΛ : Λ ⊆ I ×ˢ J) (F : ℤ × ℤ → ℂ) :
    (∑ p ∈ Λ, F p) =
      ∑ m ∈ I, ∑ n ∈ J,
        if (m, n) ∈ Λ then F (m, n) else 0 := by
  classical
  have hfilter : (I ×ˢ J).filter (fun p => p ∈ Λ) = Λ := by
    ext ⟨m, n⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨_, _⟩, hp⟩
      exact hp
    · intro hp
      exact ⟨Finset.mem_product.mp (hΛ hp), hp⟩
  calc
    (∑ p ∈ Λ, F p) =
        ∑ p ∈ (I ×ˢ J).filter (fun p => p ∈ Λ), F p := by rw [hfilter]
    _ = ∑ p ∈ I ×ˢ J, (if p ∈ Λ then F p else 0) := by
      rw [Finset.sum_filter]
    _ = ∑ m ∈ I, ∑ n ∈ J,
        if (m, n) ∈ Λ then F (m, n) else 0 := by
      rw [Finset.sum_product]

/-- The finite residue variation of a positive-integer weight on an interval
of positive integers is bounded by its global positive-integer residue
variation. -/
theorem finiteResidueVariation_le_global
    (I : FiniteIntegerInterval)
    (hI : ∀ n ∈ I.points, 0 < n)
    (β : ComplexPositiveIntegerFunction) (q : ℕ) (hq : 0 < q) :
    ENNReal.ofReal
        (finiteResidueClassVariation I
          (complexPositiveIntegerZeroExtension β) q) ≤
      complexPositiveIntegerResidueVariation β q hq := by
  classical
  let b : ℤ → ℂ := complexPositiveIntegerZeroExtension β
  have hterms : ∀ a, a ∈ Finset.range q →
      0 ≤ finiteOrderedTotalVariation
        (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) b := by
    intro a ha
    exact finiteOrderedTotalVariation_nonneg _ _
  rw [finiteResidueClassVariation,
    ENNReal.ofReal_sum_of_nonneg hterms]
  unfold complexPositiveIntegerResidueVariation
    positiveIntegerResidueTotalVariation residueClassTotalVariation
  apply Finset.sum_le_sum
  intro a ha
  let A := I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]
  let P := {n : ℤ | 0 < n} ∩ integerResidueClass q a
  have hA : ∀ n ∈ A, n ∈ P := by
    intro n hn
    have hnA : n ∈ I.points ∧ n ≡ (a : ℤ) [ZMOD (q : ℤ)] := by
      simpa [A] using hn
    refine ⟨hI n hnA.1, ?_⟩
    change ∃ k : ℤ, n = (a : ℤ) + (q : ℤ) * k
    exact Int.modEq_iff_add_fac.mp hnA.2.symm
  have hfinite :
      ENNReal.ofReal (finiteOrderedTotalVariation A b) ≤
        orderedTotalVariation P b := by
    unfold orderedTotalVariation
    let A' : {F : Finset ℤ // ∀ n ∈ F, n ∈ P} := ⟨A, hA⟩
    exact le_iSup_of_le A' le_rfl
  simpa [A, P, b] using hfinite

/-- The local variation bound remains valid for any interval extension that
agrees with the positive-integer weight on the interval points. -/
theorem finiteResidueVariation_le_global_of_eqOn
    (I : FiniteIntegerInterval)
    (hI : ∀ n ∈ I.points, 0 < n)
    (β : ComplexPositiveIntegerFunction) (q : ℕ) (hq : 0 < q)
    (b : ℤ → ℂ)
    (hb : ∀ n ∈ I.points,
      b n = complexPositiveIntegerZeroExtension β n) :
    ENNReal.ofReal (finiteResidueClassVariation I b q) ≤
      complexPositiveIntegerResidueVariation β q hq := by
  classical
  have hvariationEq : finiteResidueClassVariation I b q =
      finiteResidueClassVariation I
        (complexPositiveIntegerZeroExtension β) q := by
    unfold finiteResidueClassVariation
    apply Finset.sum_congr rfl
    intro a ha
    apply finiteOrderedTotalVariation_congr_on
    intro n hn
    exact hb n (Finset.mem_filter.mp hn).1
  rw [hvariationEq]
  exact finiteResidueVariation_le_global I hI β q hq

/-- Two applications of the residue-prefix selection lemma remove the two
weights from a finite lattice correlation, losing the exact factor
`δ^2` in each prefix step. -/
theorem ordinaryTwoResiduePrefixSelection
    (I₁ I₂ : FiniteIntegerInterval)
    (hI₁ : ∀ n ∈ I₁.points, 0 < n)
    (hI₂ : ∀ n ∈ I₂.points, 0 < n)
    (Λ : Finset (ℤ × ℤ))
    (hΛ : Λ ⊆ I₁.points ×ˢ I₂.points)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (δ H : ℝ) (hδ : 0 < δ) (hH : 0 < H)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q₀ hq₀ ≤
      ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q₀ hq₀ ≤
      ENNReal.ofReal (δ⁻¹))
    (f : ℤ × ℤ → ℂ)
    (hlarge : δ * H ≤
      ‖∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension β₂ p.2 * f p‖) :
    ∃ P₁ : ResiduePrefixData I₁ q₀ hq₀,
    ∃ P₂ : ResiduePrefixData I₂ q₀ hq₀,
      P₁.points.Nonempty ∧ P₂.points.Nonempty ∧
        δ ^ 3 * H ≤
          ‖∑ p ∈ Λ.filter (fun p =>
              p.1 ∈ P₁.points ∧ p.2 ∈ P₂.points), f p‖ := by
  classical
  let b₁ : {n : ℤ // n ∈ I₁.points} → ℂ :=
    fun n => complexPositiveIntegerZeroExtension β₁ n.1
  let F₁ : {n : ℤ // n ∈ I₁.points} → ℂ := fun m =>
    ∑ n ∈ I₂.points,
      if (m.1, n) ∈ Λ then
        complexPositiveIntegerZeroExtension β₂ n * f (m.1, n)
      else 0
  have hb₁ (m : ℤ) (hm : m ∈ I₁.points) :
      extendByZero I₁.points b₁ m =
        complexPositiveIntegerZeroExtension β₁ m := by
    simp [extendByZero, b₁, hm]
  have hF₁ (m : ℤ) (hm : m ∈ I₁.points) :
      extendByZero I₁.points F₁ m =
        ∑ n ∈ I₂.points,
          if (m, n) ∈ Λ then
            complexPositiveIntegerZeroExtension β₂ n * f (m, n)
          else 0 := by
    simp [extendByZero, F₁, hm]
  have hrawEq :
      (∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension β₂ p.2 * f p) =
      ∑ m ∈ I₁.points,
        extendByZero I₁.points b₁ m * extendByZero I₁.points F₁ m := by
    rw [finiteRectangleSum_eq hΛ]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hb₁ m hm, hF₁ m hm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hmn : (m, n) ∈ Λ <;> simp [hmn] <;> ring
  have hvariation₁ :
      finiteResidueClassVariation I₁
        (extendByZero I₁.points b₁) q₀ ≤ δ⁻¹ := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ δ⁻¹)).mp
    exact (finiteResidueVariation_le_global_of_eqOn I₁ hI₁ β₁ q₀ hq₀
      (extendByZero I₁.points b₁) (fun n hn => hb₁ n hn)).trans hTV₁
  obtain ⟨P₁, hP₁subset, hP₁bound, hP₁positive⟩ :=
    selectResiduePrefix I₁ b₁ F₁ q₀ hq₀
  have hrawPositive : 0 <
      ‖∑ m ∈ I₁.points,
        extendByZero I₁.points b₁ m * extendByZero I₁.points F₁ m‖ := by
    rw [← hrawEq]
    exact lt_of_lt_of_le (mul_pos hδ hH) hlarge
  have hδinvPos : 0 < δ⁻¹ := inv_pos.mpr hδ
  obtain ⟨hP₁nonempty, hP₁lower⟩ := hP₁positive δ⁻¹ hδinvPos
    hrawPositive hvariation₁
  have hweighted₁ : δ * H ≤ δ⁻¹ *
      ‖∑ m ∈ P₁.points, extendByZero I₁.points F₁ m‖ := by
    calc
      δ * H ≤ ‖∑ m ∈ I₁.points,
          extendByZero I₁.points b₁ m * extendByZero I₁.points F₁ m‖ := by
            rw [← hrawEq]
            exact hlarge
      _ ≤ δ⁻¹ *
          ‖∑ m ∈ P₁.points, extendByZero I₁.points F₁ m‖ := by
            calc
              _ ≤ finiteResidueClassVariation I₁
                    (extendByZero I₁.points b₁) q₀ *
                  ‖∑ m ∈ P₁.points,
                    extendByZero I₁.points F₁ m‖ := hP₁bound
              _ ≤ δ⁻¹ *
                  ‖∑ m ∈ P₁.points,
                    extendByZero I₁.points F₁ m‖ := by
                    apply mul_le_mul_of_nonneg_right hvariation₁
                    exact norm_nonneg _
  have hP₁sumLower : δ ^ 2 * H ≤
      ‖∑ m ∈ P₁.points, extendByZero I₁.points F₁ m‖ := by
    have hmul := mul_le_mul_of_nonneg_left hweighted₁ hδ.le
    have hcancel : δ * (δ * H) = δ ^ 2 * H := by ring
    have hcancel' : δ * (δ⁻¹ *
        ‖∑ m ∈ P₁.points, extendByZero I₁.points F₁ m‖) =
        ‖∑ m ∈ P₁.points, extendByZero I₁.points F₁ m‖ := by
      field_simp [ne_of_gt hδ]
    rw [hcancel, hcancel'] at hmul
    exact hmul
  let b₂ : {n : ℤ // n ∈ I₂.points} → ℂ :=
    fun n => complexPositiveIntegerZeroExtension β₂ n.1
  let F₂ : {n : ℤ // n ∈ I₂.points} → ℂ := fun n =>
    ∑ m ∈ P₁.points,
      if (m, n.1) ∈ Λ then f (m, n.1) else 0
  have hb₂ (n : ℤ) (hn : n ∈ I₂.points) :
      extendByZero I₂.points b₂ n =
        complexPositiveIntegerZeroExtension β₂ n := by
    simp [extendByZero, b₂, hn]
  have hF₂ (n : ℤ) (hn : n ∈ I₂.points) :
      extendByZero I₂.points F₂ n =
        ∑ m ∈ P₁.points,
          if (m, n) ∈ Λ then f (m, n) else 0 := by
    simp [extendByZero, F₂, hn]
  have hmiddleEq :
      (∑ m ∈ P₁.points, extendByZero I₁.points F₁ m) =
      ∑ n ∈ I₂.points,
        extendByZero I₂.points b₂ n * extendByZero I₂.points F₂ n := by
    have hleft :
        (∑ m ∈ P₁.points, extendByZero I₁.points F₁ m) =
          ∑ m ∈ P₁.points, ∑ n ∈ I₂.points,
            if (m, n) ∈ Λ then
              complexPositiveIntegerZeroExtension β₂ n * f (m, n)
            else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      simp [extendByZero, F₁, hP₁subset hm]
    rw [hleft, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hb₂ n hn, hF₂ n hn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmn : (m, n) ∈ Λ <;> simp [F₁, hmn] <;> ring
  have hvariation₂ :
      finiteResidueClassVariation I₂
        (extendByZero I₂.points b₂) q₀ ≤ δ⁻¹ := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ δ⁻¹)).mp
    exact (finiteResidueVariation_le_global_of_eqOn I₂ hI₂ β₂ q₀ hq₀
      (extendByZero I₂.points b₂) (fun n hn => hb₂ n hn)).trans hTV₂
  obtain ⟨P₂, hP₂subset, hP₂bound, hP₂positive⟩ :=
    selectResiduePrefix I₂ b₂ F₂ q₀ hq₀
  have hmiddlePositive : 0 <
      ‖∑ n ∈ I₂.points,
        extendByZero I₂.points b₂ n * extendByZero I₂.points F₂ n‖ := by
    rw [← hmiddleEq]
    exact lt_of_lt_of_le (mul_pos (sq_pos_of_pos hδ) hH) hP₁sumLower
  obtain ⟨hP₂nonempty, hP₂lower⟩ := hP₂positive δ⁻¹ hδinvPos
    hmiddlePositive hvariation₂
  have hweighted₂ : δ ^ 2 * H ≤ δ⁻¹ *
      ‖∑ n ∈ P₂.points, extendByZero I₂.points F₂ n‖ := by
    calc
      δ ^ 2 * H ≤ ‖∑ n ∈ I₂.points,
          extendByZero I₂.points b₂ n * extendByZero I₂.points F₂ n‖ := by
            rw [← hmiddleEq]
            exact hP₁sumLower
      _ ≤ δ⁻¹ *
          ‖∑ n ∈ P₂.points, extendByZero I₂.points F₂ n‖ := by
            calc
              _ ≤ finiteResidueClassVariation I₂
                    (extendByZero I₂.points b₂) q₀ *
                  ‖∑ n ∈ P₂.points,
                    extendByZero I₂.points F₂ n‖ := hP₂bound
              _ ≤ δ⁻¹ *
                  ‖∑ n ∈ P₂.points,
                    extendByZero I₂.points F₂ n‖ := by
                    apply mul_le_mul_of_nonneg_right hvariation₂
                    exact norm_nonneg _
  have hP₂sumLower : δ ^ 3 * H ≤
      ‖∑ n ∈ P₂.points, extendByZero I₂.points F₂ n‖ := by
    have hmul := mul_le_mul_of_nonneg_left hweighted₂ hδ.le
    have hcancel : δ * (δ ^ 2 * H) = δ ^ 3 * H := by ring
    have hcancel' : δ * (δ⁻¹ *
        ‖∑ n ∈ P₂.points, extendByZero I₂.points F₂ n‖) =
        ‖∑ n ∈ P₂.points, extendByZero I₂.points F₂ n‖ := by
      field_simp [ne_of_gt hδ]
    rw [hcancel, hcancel'] at hmul
    exact hmul
  let Λ' := Λ.filter (fun p => p.1 ∈ P₁.points ∧ p.2 ∈ P₂.points)
  have hΛ' : Λ' ⊆ P₁.points ×ˢ P₂.points := by
    intro p hp
    exact Finset.mem_product.mpr (Finset.mem_filter.mp hp).2
  have hsumFiltered :
      (∑ n ∈ P₂.points, extendByZero I₂.points F₂ n) =
        ∑ p ∈ Λ', f p := by
    have hrect := finiteRectangleSum_eq (Λ := Λ') hΛ' f
    have hsumF₂ :
        (∑ n ∈ P₂.points, extendByZero I₂.points F₂ n) =
          ∑ n ∈ P₂.points, ∑ m ∈ P₁.points,
            if (m, n) ∈ Λ then f (m, n) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [extendByZero, F₂, hP₂subset hn]
    rw [hrect]
    rw [hsumF₂, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    simp [Λ', hm, hn]
  refine ⟨P₁, P₂, hP₁nonempty, hP₂nonempty, ?_⟩
  rw [← hsumFiltered]
  exact hP₂sumLower

private theorem ordinary_goodDirectionWitness
    (g : HyperbolaGeometricData)
    (part : HyperbolaProgressionPartitionData g)
    (Λ Λ' : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (P₁ : ResiduePrefixData (ordinaryFirstInterval g) q₀ hq₀)
    (P₂ : ResiduePrefixData (ordinarySecondInterval g) q₀ hq₀)
    (hΛprime : Λ' = Λ.filter (fun p =>
      p.1 ∈ P₁.points ∧ p.2 ∈ P₂.points))
    (f : ℤ × ℤ → ℂ)
    (hf : ∀ p, p ∈ g.lattice → ‖f p‖ ≤ 1)
    (τ : ℝ) (hτ : 0 < τ)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    (hthreshold : τ * g.L0 ≤
      ordinaryDirectionMaximum g Λ' f a q) :
    ∃ P ∈ hyperbolaProgressionFamily g a q,
    ∃ z : ℤ × ℤ, ∃ N : ℕ, ∃ hN : 0 < N,
      (↑(latticeProgression z
        ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN) :
          Set (ℤ × ℤ)) ⊆ P ∧
      (↑(latticeProgression z
        ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN) :
          Set (ℤ × ℤ)) ⊆ g.lattice ∧
      τ * g.L0 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ g.L0 ∧
      τ * g.L0 ≤ ‖∑ p ∈ latticeProgression z
        ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN, f p‖ := by
  classical
  let vals := (hyperbolaProgressionFamily g a q).image
    (ordinaryPieceAbsoluteSum Λ' f)
  have hvals : (insert 0 vals).Nonempty := by simp
  obtain ⟨v, hv, hvEq⟩ := Finset.exists_mem_eq_sup' hvals id
  have hvMaximum : v = ordinaryDirectionMaximum g Λ' f a q := by
    simpa [ordinaryDirectionMaximum, vals] using hvEq.symm
  have hthresholdPos : 0 < τ * g.L0 := by
    have hparams := admissibleParameterBounds g q hidx.1.2.1 hidx.1.2.2.1
    exact mul_pos hτ (lt_of_lt_of_le zero_lt_one hparams.L0_lower)
  have hpiece : ∃ P ∈ hyperbolaProgressionFamily g a q,
      ordinaryPieceAbsoluteSum Λ' f P =
        ordinaryDirectionMaximum g Λ' f a q := by
    rcases Finset.mem_insert.mp hv with hvzero | hvinsert
    · exfalso
      rw [hvzero] at hvMaximum
      linarith
    · rcases Finset.mem_image.mp hvinsert with ⟨P, hP, hval⟩
      refine ⟨P, hP, ?_⟩
      rw [hval, hvMaximum]
  obtain ⟨P, hP, hPmax⟩ := hpiece
  have hPsumPos : 0 < ordinaryPieceAbsoluteSum Λ' f P :=
    lt_of_lt_of_le hthresholdPos (hPmax.symm ▸ hthreshold)
  have hpieceData := part.pieces a q
    ((positiveRationalCellIndices_mem_iff g a q).2 hidx) P hP
  rcases hpieceData with ⟨hPnonempty, hPL0, hPlattice,
    ⟨base, lo, hi, hPmodel, hlohi⟩⟩
  have hPsource : P =
      cellLatticeIccProgression base (q : ℤ) (a : ℤ)
        (lo : ℤ) (hi : ℤ) := by
    rw [hPmodel, natIndexedLatticeProgression_eq_cellLatticeIcc]
  let cut := coordinateProgressionCut base (q : ℤ) (a : ℤ)
    (lo : ℤ) (hi : ℤ) P₁.start P₂.start q₀ hq₀
    P₁.prefixLength P₂.prefixLength
  have hpoints :
      (ordinaryPiecePoints Λ' P : Set (ℤ × ℤ)) = cut := by
    ext p
    constructor
    · intro hp
      have hpFin : p ∈ ordinaryPiecePoints Λ' P := by simpa using hp
      dsimp [ordinaryPiecePoints] at hpFin
      rcases Finset.mem_filter.mp hpFin with ⟨hpΛ', hpP⟩
      rw [hΛprime] at hpΛ'
      rcases Finset.mem_filter.mp hpΛ' with ⟨hpΛ, hpcoord⟩
      have hpSet : p ∈ (Λ : Set (ℤ × ℤ)) := by simpa using hpΛ
      have hpL : p ∈ g.lattice := by rw [hΛ] at hpSet; exact hpSet
      have hpPsource : p ∈
          cellLatticeIccProgression base (q : ℤ) (a : ℤ)
            (lo : ℤ) (hi : ℤ) := by simpa [hPsource] using hpP
      exact ⟨hpPsource, hpcoord.1, hpcoord.2⟩
    · intro hp
      rcases hp with ⟨hpCut, hpcoords⟩
      have hpP : p ∈ P := by simpa [hPsource] using hpCut
      have hpL : p ∈ g.lattice := hPlattice hpP
      have hpΛSet : p ∈ (Λ : Set (ℤ × ℤ)) := by rw [hΛ]; exact hpL
      have hpΛ : p ∈ Λ := by simpa using hpΛSet
      have hpΛprime : p ∈ Λ' := by
        rw [hΛprime]
        exact Finset.mem_filter.mpr ⟨hpΛ, hpcoords⟩
      have hpFin : p ∈ ordinaryPiecePoints Λ' P := by
        dsimp [ordinaryPiecePoints]
        exact Finset.mem_filter.mpr ⟨hpΛprime, hpP⟩
      simpa using hpFin
  have ha : 0 < a := Nat.lt_of_lt_of_le Nat.zero_lt_one hidx.1.2.2.2.1
  have hq : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hidx.1.2.1
  have hcoord := coordinateProgressionIntersection
    a q q₀ ha hq hq₀ hidx.1.1
    base (lo : ℤ) (hi : ℤ) P₁.start P₂.start
    P₁.prefixLength P₂.prefixLength
  have hcoord' : cut = ∅ ∨ ∃ start : ℤ, ∃ N : ℕ, ∃ hN : 0 < N,
      cut = (↑(latticeProgression
        (base.1 + start * (q : ℤ), base.2 - start * (a : ℤ))
        ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN) :
          Set (ℤ × ℤ)) ∧
      cut.ncard ≤
        (cellLatticeIccProgression base (q : ℤ) (a : ℤ)
          (lo : ℤ) (hi : ℤ)).ncard := by
    simpa [cut] using hcoord
  rcases hcoord' with hempty | ⟨start, N, hN, hcutEq, hcutCard⟩
  · have hpieceEmpty : ordinaryPiecePoints Λ' P = ∅ := by
      apply Finset.coe_injective
      simpa [hpoints] using hempty
    have hzero : ordinaryPieceAbsoluteSum Λ' f P = 0 := by
      simp [ordinaryPieceAbsoluteSum, hpieceEmpty]
    linarith [hPsumPos]
  · let z : ℤ × ℤ :=
      (base.1 + start * (q : ℤ), base.2 - start * (a : ℤ))
    let prog := latticeProgression z
      ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN
    have hprogSet : (↑prog : Set (ℤ × ℤ)) = cut := by
      simpa [prog, z] using hcutEq.symm
    have hpiecePointsEq : ordinaryPiecePoints Λ' P = prog :=
      Finset.coe_injective (hpoints.trans hprogSet.symm)
    have hprogSubP : (↑prog : Set (ℤ × ℤ)) ⊆ P := by
      rw [hprogSet]
      change coordinateProgressionCut base (q : ℤ) (a : ℤ)
        (lo : ℤ) (hi : ℤ) P₁.start P₂.start q₀ hq₀
        P₁.prefixLength P₂.prefixLength ⊆ P
      rw [hPsource]
      exact Set.inter_subset_left
    have hprogSubLattice : (↑prog : Set (ℤ × ℤ)) ⊆ g.lattice :=
      hprogSubP.trans hPlattice
    have hstep :
        ((q₀ : ℤ) * (q : ℤ) ≠ 0 ∨
          (q₀ : ℤ) * (a : ℤ) ≠ 0) := by
      left
      exact mul_ne_zero (by exact_mod_cast hq₀.ne') (by exact_mod_cast hq.ne')
    have hprogCard : prog.card = N := by
      dsimp [prog]
      exact latticeProgression_card_of_nonzero_spacing z
        ((q₀ : ℤ) * (q : ℤ)) ((q₀ : ℤ) * (a : ℤ)) N hN hstep
    have hcutNcard : cut.ncard = N := by
      calc
        cut.ncard = (↑prog : Set (ℤ × ℤ)).ncard := by rw [hprogSet.symm]
        _ = prog.card := Set.ncard_coe_finset prog
        _ = N := hprogCard
    have hNleP : N ≤ P.ncard := by
      have h := hcutCard
      rw [hcutNcard, hPsource.symm] at h
      exact h
    have hNle : (N : ℝ) ≤ g.L0 := by
      exact (by exact_mod_cast hNleP : (N : ℝ) ≤ (P.ncard : ℝ)).trans hPL0
    have hsumLower : τ * g.L0 ≤ ‖∑ p ∈ prog, f p‖ := by
      rw [← hpiecePointsEq]
      calc
        τ * g.L0 ≤ ordinaryDirectionMaximum g Λ' f a q := hthreshold
        _ = ordinaryPieceAbsoluteSum Λ' f P := hPmax.symm
    have hnormCard : ‖∑ p ∈ prog, f p‖ ≤ (N : ℝ) := by
      calc
        ‖∑ p ∈ prog, f p‖ ≤ ∑ p ∈ prog, ‖f p‖ := norm_sum_le _ _
        _ ≤ ∑ p ∈ prog, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpL : p ∈ g.lattice := hprogSubLattice (by simpa using hp)
          exact hf p hpL
        _ = (prog.card : ℝ) := by simp
        _ = (N : ℝ) := by exact_mod_cast hprogCard
    have hlengthLower : τ * g.L0 ≤ (N : ℝ) := hsumLower.trans hnormCard
    exact ⟨P, hP, z, N, hN, hprogSubP, hprogSubLattice,
      hlengthLower, hNle, hsumLower⟩

/-- **Blueprint `lhg:ordinary-pigeonhole`.** Two coordinatewise residue
prefix selections remove the two variation-controlled weights. The
partition contributions then yield the exact source count of distinct
coprime directions, each carrying a nonempty subprogression of spacing
`q₀(q,-a)` with the stated length and unweighted-sum bounds. -/
theorem ordinaryWeightedPigeonhole
    (g : HyperbolaGeometricData)
    (part : HyperbolaProgressionPartitionData g)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (q₀ : ℕ) (hq₀ : 1 ≤ q₀) (hq₀bound : (q₀ : ℝ) ≤ δ⁻¹)
    (β₁ β₂ : ComplexPositiveIntegerFunction)
    (hTV₁ : complexPositiveIntegerResidueVariation β₁ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (hTV₂ : complexPositiveIntegerResidueVariation β₂ q₀
      (by omega : 0 < q₀) ≤ ENNReal.ofReal (δ⁻¹))
    (Λ : Finset (ℤ × ℤ))
    (hΛ : (Λ : Set (ℤ × ℤ)) = g.lattice)
    (f : ℤ × ℤ → ℂ)
    (hf : ∀ p, p ∈ g.lattice → ‖f p‖ ≤ 1)
    (hlarge : δ * g.H ≤
      ‖∑ p ∈ Λ,
        complexPositiveIntegerZeroExtension β₁ p.1 *
          complexPositiveIntegerZeroExtension β₂ p.2 * f p‖) :
    ∃ good : Finset (ℕ × ℕ),
      (δ ^ 6 / (8 * ordinaryB0 g * (C_geo g.K₀) ^ 2) *
        (g.X * (g.Q : ℝ) ^ 2 / g.M ^ 2)) ≤ (good.card : ℝ) ∧
      ∀ i ∈ good,
        Nat.Coprime i.1 i.2 ∧
        0 < i.1 ∧ 0 < i.2 ∧
        ordinaryTau g δ * (g.Q : ℝ) ≤ (i.2 : ℝ) ∧
        i.2 ≤ g.Q ∧
        (g.r / 8) * (i.2 : ℝ) ≤ (i.1 : ℝ) ∧
        (i.1 : ℝ) ≤ E g.K₀ * g.r * (i.2 : ℝ) ∧
        ∃ P ∈ hyperbolaProgressionFamily g i.1 i.2,
        ∃ z : ℤ × ℤ, ∃ N : ℕ, ∃ hN : 0 < N,
          (↑(latticeProgression z
            ((q₀ : ℤ) * (i.2 : ℤ)) ((q₀ : ℤ) * (i.1 : ℤ)) N hN) :
              Set (ℤ × ℤ)) ⊆ P ∧
          (↑(latticeProgression z
            ((q₀ : ℤ) * (i.2 : ℤ)) ((q₀ : ℤ) * (i.1 : ℤ)) N hN) :
              Set (ℤ × ℤ)) ⊆ g.lattice ∧
          ordinaryTau g δ * g.L0 ≤ (N : ℝ) ∧
          (N : ℝ) ≤ g.L0 ∧
          ordinaryTau g δ * g.L0 ≤
            ‖∑ p ∈ latticeProgression z
              ((q₀ : ℤ) * (i.2 : ℤ)) ((q₀ : ℤ) * (i.1 : ℤ)) N hN, f p‖ := by
  classical
  let τ := ordinaryTau g δ
  let I := positiveRationalCellIndices g
  let G := C_geo g.K₀
  have hq₀pos : 0 < q₀ := Nat.lt_of_lt_of_le Nat.zero_lt_one hq₀
  have hB₀pos : 0 < ordinaryB0 g := by
    dsimp [ordinaryB0, E]
    positivity
  have hGpos : 0 < C_geo g.K₀ := by
    dsimp [C_geo, C_point, C_line, D, E]
    positivity
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have hMpos : 0 < g.M := by linarith [g.M_ge_one]
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hrpos : 0 < g.r := by
    dsimp [HyperbolaGeometricData.r]
    exact div_pos hXpos (sq_pos_of_pos hMpos)
  have hτpos : 0 < τ := by
    dsimp [τ, ordinaryTau]
    positivity
  have hτnonneg : 0 ≤ τ := hτpos.le
  have hτcancel : τ * ordinaryB0 g * C_geo g.K₀ * g.H =
      δ ^ 3 * g.H / 4 := by
    dsimp [τ, ordinaryTau]
    field_simp [ne_of_gt hB₀pos, ne_of_gt hGpos] <;> ring
  let I₁ := ordinaryFirstInterval g
  let I₂ := ordinarySecondInterval g
  have hI₁pos : ∀ n ∈ I₁.points, 0 < n :=
    ordinaryFirstInterval_positive g
  have hI₂pos : ∀ n ∈ I₂.points, 0 < n :=
    ordinarySecondInterval_positive g
  have hrectangle := ordinary_lattice_subset_rectangle g Λ hΛ
  obtain ⟨P₁, P₂, hP₁nonempty, hP₂nonempty, hprefix⟩ :=
    ordinaryTwoResiduePrefixSelection I₁ I₂ hI₁pos hI₂pos Λ hrectangle
      β₁ β₂ q₀ hq₀pos δ g.H hδ hHpos hTV₁ hTV₂ f hlarge
  let Λ' := Λ.filter (fun p => p.1 ∈ P₁.points ∧ p.2 ∈ P₂.points)
  have hΛ'subset : Λ' ⊆ Λ := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hΛ'support : ∀ p, p ∈ Λ' → p ∈ g.lattice := by
    intro p hp
    have hpSet : p ∈ (Λ : Set (ℤ × ℤ)) := by
      simpa using hΛ'subset hp
    rw [hΛ] at hpSet
    exact hpSet
  have hprefixNorm : δ ^ 3 * g.H ≤ ‖∑ p ∈ Λ', f p‖ := by
    simpa [Λ'] using hprefix
  have hpartitionNorm := ordinary_norm_sum_le_partitionPieces
    g part Λ' hΛ'support f
  have hpieceContribution :
      (∑ i ∈ I,
        ∑ P ∈ hyperbolaProgressionFamily g i.1 i.2,
          ordinaryPieceAbsoluteSum Λ' f P) ≤
        ∑ i ∈ I, ordinaryDirectionContribution g Λ' f i := by
    apply Finset.sum_le_sum
    intro i hi
    exact ordinary_sumPieceAbsoluteSum_le_directionContribution
      g Λ' f i.1 i.2
  have htotalLower : δ ^ 3 * g.H ≤
      ∑ i ∈ I, ordinaryDirectionContribution g Λ' f i :=
    hprefixNorm.trans (hpartitionNorm.trans hpieceContribution)
  have hsmallQ := ordinary_smallDenominatorContribution_le
    g part Λ' Λ hΛ hΛ'subset f hf τ hτnonneg
  have hsmallU := ordinary_smallMaximumContribution_le
    g part Λ' Λ hΛ hΛ'subset f hf τ hτnonneg
  let qBad : ℕ × ℕ → Prop := fun i => (i.2 : ℝ) < τ * (g.Q : ℝ)
  let uBad : ℕ × ℕ → Prop := fun i =>
    ordinaryDirectionMaximum g Λ' f i.1 i.2 < τ * g.L0
  let goodPred : ℕ × ℕ → Prop := fun i =>
    τ * (g.Q : ℝ) ≤ (i.2 : ℝ) ∧
      τ * g.L0 ≤ ordinaryDirectionMaximum g Λ' f i.1 i.2
  let good := I.filter goodPred
  let contribution := ordinaryDirectionContribution g Λ' f
  have hgoodCover :
      (∑ i ∈ I, contribution i) ≤
        (∑ i ∈ I.filter qBad, contribution i) +
          (∑ i ∈ I.filter uBad, contribution i) +
          (∑ i ∈ good, contribution i) := by
    calc
      (∑ i ∈ I, contribution i) ≤
          ∑ i ∈ I, (
            (if qBad i then contribution i else 0) +
              (if uBad i then contribution i else 0) +
              (if goodPred i then contribution i else 0)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hU0 : 0 ≤ ordinaryDirectionMaximum g Λ' f i.1 i.2 :=
          zero_le_ordinaryDirectionMaximum g Λ' f i.1 i.2
        have hcontrib0 : 0 ≤ contribution i := by
          dsimp [contribution, ordinaryDirectionContribution]
          positivity
        by_cases hqbad : qBad i
        · have huif : 0 ≤ (if uBad i then contribution i else 0) := by
            split_ifs <;> positivity
          have hgif : 0 ≤ (if goodPred i then contribution i else 0) := by
            split_ifs <;> positivity
          simp [qBad, hqbad]
          nlinarith [huif, hgif]
        · by_cases hubad : uBad i
          · have hgif : 0 ≤ (if goodPred i then contribution i else 0) := by
              split_ifs <;> positivity
            simp [uBad, hubad, qBad, hqbad]
            nlinarith [hgif]
          · have hgood : goodPred i := by
              simp only [goodPred, qBad, uBad] at *
              exact ⟨le_of_not_gt hqbad, le_of_not_gt hubad⟩
            simp [qBad, uBad, goodPred, hqbad, hubad, hgood]
      _ = (∑ i ∈ I.filter qBad, contribution i) +
          (∑ i ∈ I.filter uBad, contribution i) +
          (∑ i ∈ good, contribution i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
  have hgoodLower : δ ^ 3 * g.H / 2 ≤
      ∑ i ∈ good, contribution i := by
    have hqbad := hsmallQ
    have hubad := hsmallU
    dsimp [qBad, uBad, good, I, contribution] at hgoodCover htotalLower hqbad hubad ⊢
    nlinarith [hgoodCover, htotalLower, hqbad, hubad, hτcancel]
  let factor := G * g.H / (τ * g.r * (g.Q : ℝ) ^ 2)
  have hfactorPos : 0 < factor := by
    dsimp [factor, G]
    positivity
  have hgoodTerm : ∀ i ∈ good, contribution i ≤ factor := by
    intro i hi
    have hgoodi := (Finset.mem_filter.mp hi).2
    have hidx := (positiveRationalCellIndices_mem_iff g i.1 i.2).1
      (Finset.mem_filter.mp hi).1
    rcases hidx.1 with ⟨hcop, hqlo, hqhi, haLo, hamin, hamax⟩
    have hparams := admissibleParameterBounds g i.2 hqlo hqhi
    have hcount := part.count i.1 i.2 hidx
    have hU := ordinaryDirectionMaximum_le_L0 g part i.1 i.2 hidx
      Λ' Λ hΛ hΛ'subset f hf
    have hU0 := zero_le_ordinaryDirectionMaximum g Λ' f i.1 i.2
    have hRL : R_q g i.2 * g.L0 = S_q g i.2 := by
      have hEq := hparams.S_div_L0_eq_R
      have hL0pos : 0 < g.L0 :=
        lt_of_lt_of_le zero_lt_one hparams.L0_lower
      field_simp [ne_of_gt hL0pos] at hEq
      nlinarith [hEq]
    have hGnonneg : 0 ≤ G := hGpos.le
    have hRnonneg : 0 ≤ R_q g i.2 := le_trans zero_le_one hparams.R_lower
    have htermS : contribution i ≤ G * S_q g i.2 := by
      dsimp [contribution, ordinaryDirectionContribution]
      calc
        (hyperbolaProgressionFamily g i.1 i.2).card *
            ordinaryDirectionMaximum g Λ' f i.1 i.2 ≤
          (G * R_q g i.2) *
            ordinaryDirectionMaximum g Λ' f i.1 i.2 := by
              simpa [G] using mul_le_mul_of_nonneg_right hcount hU0
        _ ≤ (G * R_q g i.2) * g.L0 :=
          mul_le_mul_of_nonneg_left hU (mul_nonneg hGnonneg hRnonneg)
        _ = G * S_q g i.2 := by
          calc
            _ = G * (R_q g i.2 * g.L0) := by ring
            _ = G * S_q g i.2 := by rw [hRL]
    have hqRealPos : 0 < (i.2 : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hqlo)
    have hτQle : τ * (g.Q : ℝ) ≤ (i.2 : ℝ) := hgoodi.1
    have hdenLower : τ * (g.Q : ℝ) ^ 2 ≤
        (g.Q : ℝ) * (i.2 : ℝ) := by
      calc
        τ * (g.Q : ℝ) ^ 2 = (τ * (g.Q : ℝ)) * (g.Q : ℝ) := by ring
        _ ≤ (i.2 : ℝ) * (g.Q : ℝ) :=
          mul_le_mul_of_nonneg_right hτQle (le_of_lt hQpos)
        _ = (g.Q : ℝ) * (i.2 : ℝ) := by ring
    have hdenS₁ : 0 < g.X * (g.Q : ℝ) * (i.2 : ℝ) := by positivity
    have hdenS₂ : 0 < τ * g.r * (g.Q : ℝ) ^ 2 := by positivity
    have hcross :
        (g.H * g.M ^ 2) * (τ * g.r * (g.Q : ℝ) ^ 2) ≤
          g.H * (g.X * (g.Q : ℝ) * (i.2 : ℝ)) := by
      calc
        (g.H * g.M ^ 2) * (τ * g.r * (g.Q : ℝ) ^ 2) =
            g.H * g.X * (τ * (g.Q : ℝ) ^ 2) := by
              dsimp [HyperbolaGeometricData.r]
              field_simp [ne_of_gt hMpos] <;> ring
        _ ≤ g.H * g.X * ((g.Q : ℝ) * (i.2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hdenLower
            (mul_nonneg hHpos.le hXpos.le)
        _ = g.H * (g.X * (g.Q : ℝ) * (i.2 : ℝ)) := by ring
    have hSupper : S_q g i.2 ≤
        g.H / (τ * g.r * (g.Q : ℝ) ^ 2) := by
      dsimp [S_q]
      exact (div_le_div_iff₀ hdenS₁ hdenS₂).2 hcross
    calc
      contribution i ≤ G * S_q g i.2 := htermS
      _ ≤ G * (g.H / (τ * g.r * (g.Q : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hSupper hGnonneg
      _ = factor := by dsimp [factor]; ring
  have hgoodUpper :
      (∑ i ∈ good, contribution i) ≤ (good.card : ℝ) * factor := by
    calc
      (∑ i ∈ good, contribution i) ≤ ∑ i ∈ good, factor := by
        apply Finset.sum_le_sum
        intro i hi
        exact hgoodTerm i hi
      _ = (good.card : ℝ) * factor := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hratio : δ ^ 3 * g.H / 2 ≤ (good.card : ℝ) * factor :=
    hgoodLower.trans hgoodUpper
  have hmultPos : 0 <
      τ * g.r * (g.Q : ℝ) ^ 2 / (G * g.H) := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_right hratio hmultPos.le
  have hleftScale :
      (δ ^ 3 * g.H / 2) *
        (τ * g.r * (g.Q : ℝ) ^ 2 / (G * g.H)) =
      δ ^ 3 * τ * g.r * (g.Q : ℝ) ^ 2 / (2 * G) := by
    field_simp [ne_of_gt hGpos, ne_of_gt hHpos] <;> ring
  have hGpos' : 0 < G := by simpa [G] using hGpos
  have hrightScale :
      ((good.card : ℝ) * factor) *
        (τ * g.r * (g.Q : ℝ) ^ 2 / (G * g.H)) =
      (good.card : ℝ) := by
    dsimp [factor]
    field_simp [ne_of_gt hτpos, ne_of_gt hrpos, ne_of_gt hQpos,
      ne_of_gt hGpos', ne_of_gt hHpos] <;> ring
  rw [hleftScale, hrightScale] at hscaled
  have hcountAlgebra :
      δ ^ 3 * τ * g.r * (g.Q : ℝ) ^ 2 / (2 * G) =
        δ ^ 6 / (8 * ordinaryB0 g * (C_geo g.K₀) ^ 2) *
          (g.X * (g.Q : ℝ) ^ 2 / g.M ^ 2) := by
    dsimp [τ, ordinaryTau, G, HyperbolaGeometricData.r]
    field_simp [ne_of_gt hB₀pos, ne_of_gt hGpos, ne_of_gt hMpos] <;> ring
  rw [hcountAlgebra] at hscaled
  refine ⟨good, hscaled, ?_⟩
  intro i hi
  have hidx := (positiveRationalCellIndices_mem_iff g i.1 i.2).1
    (Finset.mem_filter.mp hi).1
  have hgoodi := (Finset.mem_filter.mp hi).2
  rcases hidx.1 with ⟨hcop, hqlo, hqhi, haLo, hamin, hamax⟩
  have haPos : 0 < i.1 := Nat.lt_of_lt_of_le Nat.zero_lt_one haLo
  have hqPos : 0 < i.2 := Nat.lt_of_lt_of_le Nat.zero_lt_one hqlo
  have hwitness := ordinary_goodDirectionWitness g part Λ Λ' hΛ q₀ hq₀pos
    P₁ P₂ (by rfl) f hf τ hτpos i.1 i.2 hidx hgoodi.2
  exact ⟨hcop, haPos, hqPos, hgoodi.1, hqhi, hamin, hamax, hwitness⟩


end FractionalPrimes.Literature.Hyperbola

#print axioms FractionalPrimes.Literature.Hyperbola.ordinaryTwoResiduePrefixSelection
#print axioms FractionalPrimes.Literature.Hyperbola.ordinaryWeightedPigeonhole
