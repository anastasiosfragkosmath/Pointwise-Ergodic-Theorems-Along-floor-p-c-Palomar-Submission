module

public import FractionalPrimes.Literature.Hyperbola.CellLinearSlices
public import FractionalPrimes.Literature.Hyperbola.SeparatedCount

set_option maxHeartbeats 800000

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

open Set HyperbolaGeometricData

/-- The set of integers indexing nonempty slices of one rational cell. -/
def occupiedSliceValues (g : HyperbolaGeometricData) (a q : ℕ) : Set ℤ :=
  {c | (cellLinearSliceOnLine g a q c).Nonempty}

/-- The exact interval length used to count occupied line values. -/
noncomputable def occupiedSliceWindowWidth (g : HyperbolaGeometricData)
    (q : ℕ) : ℝ :=
  8 * (E g.K₀ + (D g.K₀) ^ 2) * R_q g q

/-- An occupied linear slice lies in the short interval starting at `t`. -/
theorem occupiedSliceValue_mem_Ioc (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    {c : ℤ} (hc : c ∈ occupiedSliceValues g a q) :
    let u : ℝ := (a : ℝ) * (q : ℝ)
    let t : ℝ := 2 * Real.sqrt (u * g.X)
    (c : ℝ) ∈ Set.Ioc t (t + occupiedSliceWindowWidth g q) := by
  classical
  dsimp [occupiedSliceValues] at hc
  rcases hc with ⟨p, hp⟩
  rcases hp with ⟨hpCell, hcLine⟩
  let u : ℝ := (a : ℝ) * (q : ℝ)
  let t : ℝ := 2 * Real.sqrt (u * g.X)
  let Z : ℝ := 2 * D g.K₀ * g.M / (g.Q : ℝ)
  have hpoint := cellLinearPointBounds g a q hidx p hpCell
  change
    (cellLinearCoordinate a q p : ℝ) > t ∧
      0 < t ∧ |(cellTransverseCoordinate a q p : ℝ)| ≤ Z ∧
      (cellLinearCoordinate a q p : ℝ) ^ 2 -
          (cellTransverseCoordinate a q p : ℝ) ^ 2 =
        4 * u * (p.1 : ℝ) * (p.2 : ℝ) ∧
      (g.r * (q : ℝ) ^ 2 / 8 ≤ u ∧
        u ≤ E g.K₀ * g.r * (q : ℝ) ^ 2) at hpoint
  rcases hpoint with ⟨hcgt, htpos, hzbound, hidentity, huLower, huUpper⟩
  have hqlo : 1 ≤ q := hidx.1.2.1
  have hqhi : q ≤ g.Q := hidx.1.2.2.1
  have hparams := admissibleParameterBounds g q hqlo hqhi
  have hproductLower := hparams.lattice_point_properties p hpCell.1
  have hproductUpper :
      (p.1 : ℝ) * (p.2 : ℝ) ≤ g.X + g.H := hpCell.1.2.2
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have hMpos : 0 < g.M := by linarith [g.M_ge_one]
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hKpos : 0 < g.K₀ := by linarith [g.K₀_ge_one]
  have hDnonneg : 0 ≤ D g.K₀ := by
    dsimp [D]
    positivity
  have hEnonneg : 0 ≤ E g.K₀ := by
    dsimp [E]
    positivity
  have hKnonneg : 0 ≤ E g.K₀ + (D g.K₀) ^ 2 := by positivity
  have hRqpos : 0 < R_q g q := by
    have := hparams.R_lower
    dsimp [R_q]
    positivity
  have hQnonneg : 0 ≤ (g.Q : ℝ) := hQpos.le
  have hMnonneg : 0 ≤ g.M := hMpos.le
  have hHnonneg : 0 ≤ g.H := hHpos.le
  have hXnonneg : 0 ≤ g.X := hXpos.le
  have hqnonneg : 0 ≤ (q : ℝ) := hqpos.le
  have hRnonneg : 0 ≤ g.r := by
    dsimp [HyperbolaGeometricData.r]
    positivity
  have hM2pos : 0 < g.M ^ 2 := sq_pos_of_pos hMpos
  have hQupper : (g.Q : ℝ) * Real.sqrt (Real.sqrt (g.H * g.X)) ≤ g.M := by
    have hroot : 0 < Real.sqrt (Real.sqrt (g.H * g.X)) := by
      positivity
    exact (le_div_iff₀ hroot).mp g.Q_le_M_div_fourthRoot
  have hQ4 : (g.Q : ℝ) ^ 4 * (g.H * g.X) ≤ g.M ^ 4 := by
    let T : ℝ := Real.sqrt (Real.sqrt (g.H * g.X))
    have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
    have hT2 : T ^ 2 = Real.sqrt (g.H * g.X) := by
      dsimp [T]
      exact Real.sq_sqrt (Real.sqrt_nonneg _)
    have hT4 : T ^ 4 = g.H * g.X := by
      calc
        T ^ 4 = (T ^ 2) ^ 2 := by ring
        _ = (Real.sqrt (g.H * g.X)) ^ 2 := by rw [hT2]
        _ = g.H * g.X := Real.sq_sqrt (mul_nonneg hHnonneg hXnonneg)
    have hpow := pow_le_pow_left₀
      (mul_nonneg hQnonneg hTnonneg) hQupper 4
    calc
      (g.Q : ℝ) ^ 4 * (g.H * g.X) =
          ((g.Q : ℝ) * T) ^ 4 := by rw [← hT4]; ring
      _ ≤ g.M ^ 4 := by simpa [mul_pow] using hpow
  have hq2 : (q : ℝ) ^ 2 ≤ (g.Q : ℝ) ^ 2 :=
    pow_le_pow_left₀ hqnonneg (by exact_mod_cast hqhi) 2
  have hcore :
      g.X * g.H * (q : ℝ) ^ 2 * (g.Q : ℝ) ^ 2 ≤ g.M ^ 4 := by
    calc
      g.X * g.H * (q : ℝ) ^ 2 * (g.Q : ℝ) ^ 2 =
          g.X * g.H * ((q : ℝ) ^ 2 * (g.Q : ℝ) ^ 2) := by ring
      _ ≤ g.X * g.H * (g.Q : ℝ) ^ 4 := by
            have hmul : (q : ℝ) ^ 2 * (g.Q : ℝ) ^ 2 ≤ (g.Q : ℝ) ^ 4 := by
              calc
                (q : ℝ) ^ 2 * (g.Q : ℝ) ^ 2 ≤
                    (g.Q : ℝ) ^ 2 * (g.Q : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
                _ = (g.Q : ℝ) ^ 4 := by ring
            exact mul_le_mul_of_nonneg_left hmul
              (mul_nonneg hXnonneg hHnonneg)
      _ = (g.Q : ℝ) ^ 4 * (g.H * g.X) := by ring
      _ ≤ g.M ^ 4 := hQ4
  have hcoreDiv :
      g.X * g.H * (q : ℝ) ^ 2 * (g.Q : ℝ) ^ 2 / g.M ^ 2 ≤ g.M ^ 2 := by
    apply (div_le_iff₀ hM2pos).2
    nlinarith [hcore]
  have hUH : u * g.H ≤ E g.K₀ * g.M ^ 2 / (g.Q : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hQpos)).2
    calc
      u * g.H * (g.Q : ℝ) ^ 2 = u * (g.H * (g.Q : ℝ) ^ 2) := by ring
      _ ≤ (E g.K₀ * g.r * (q : ℝ) ^ 2) *
          (g.H * (g.Q : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right huUpper
              (mul_nonneg hHnonneg (sq_nonneg _))
      _ = E g.K₀ *
          (g.X * g.H * (q : ℝ) ^ 2 * (g.Q : ℝ) ^ 2 / g.M ^ 2) := by
            dsimp [HyperbolaGeometricData.r]
            field_simp [ne_of_gt hMpos]
      _ ≤ E g.K₀ * g.M ^ 2 :=
          mul_le_mul_of_nonneg_left hcoreDiv hEnonneg
  have hZsq : Z ^ 2 ≤ 4 * (D g.K₀) ^ 2 * g.M ^ 2 / (g.Q : ℝ) ^ 2 := by
    dsimp [Z]
    exact le_of_eq (by ring)
  have hdeltaUpper :
      (cellLinearCoordinate a q p : ℝ) ^ 2 - t ^ 2 ≤
        4 * (E g.K₀ + (D g.K₀) ^ 2) * g.M ^ 2 / (g.Q : ℝ) ^ 2 := by
    have hmnX :
        (p.1 : ℝ) * (p.2 : ℝ) - g.X ≤ g.H := by linarith [hproductUpper]
    have huLowerNonneg : 0 ≤ g.r * (q : ℝ) ^ 2 / 8 :=
      div_nonneg (mul_nonneg hRnonneg (sq_nonneg _)) (by norm_num)
    have huNonneg : 0 ≤ u := le_trans huLowerNonneg huLower
    have hprodBound := mul_le_mul_of_nonneg_left hmnX
      (show 0 ≤ 4 * u by positivity)
    have hzSq :
        (cellTransverseCoordinate a q p : ℝ) ^ 2 ≤ Z ^ 2 := by
      have hZnonneg : 0 ≤ Z := le_trans (abs_nonneg _) hzbound
      have habsSq := (sq_le_sq₀ (abs_nonneg _) hZnonneg).2 hzbound
      simpa [sq_abs] using habsSq
    have htSq : t ^ 2 = 4 * u * g.X := by
      dsimp [t]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    calc
      (cellLinearCoordinate a q p : ℝ) ^ 2 - t ^ 2 =
          ((cellLinearCoordinate a q p : ℝ) ^ 2 -
            (cellTransverseCoordinate a q p : ℝ) ^ 2) +
            (cellTransverseCoordinate a q p : ℝ) ^ 2 - t ^ 2 := by ring
      _ = 4 * u * (p.1 : ℝ) * (p.2 : ℝ) +
          (cellTransverseCoordinate a q p : ℝ) ^ 2 - 4 * u * g.X := by
            rw [hidentity, htSq]
      _ ≤ 4 * u * g.H + Z ^ 2 := by
        nlinarith [hprodBound, hzSq]
      _ ≤ 4 * (E g.K₀ + (D g.K₀) ^ 2) * g.M ^ 2 /
          (g.Q : ℝ) ^ 2 := by
            have h4uh : 4 * u * g.H ≤
                4 * E g.K₀ * g.M ^ 2 / (g.Q : ℝ) ^ 2 := by
              calc
                4 * u * g.H = 4 * (u * g.H) := by ring
                _ ≤ 4 * (E g.K₀ * g.M ^ 2 / (g.Q : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left hUH (by norm_num)
                _ = 4 * E g.K₀ * g.M ^ 2 / (g.Q : ℝ) ^ 2 := by ring
            calc
              4 * u * g.H + Z ^ 2 ≤
                  4 * E g.K₀ * g.M ^ 2 / (g.Q : ℝ) ^ 2 +
                    4 * (D g.K₀) ^ 2 * g.M ^ 2 / (g.Q : ℝ) ^ 2 :=
                add_le_add h4uh hZsq
              _ = 4 * (E g.K₀ + (D g.K₀) ^ 2) * g.M ^ 2 /
                    (g.Q : ℝ) ^ 2 := by ring
  have huLowerR :
      g.X * (q : ℝ) ^ 2 / (8 * g.M ^ 2) ≤ u := by
    have hrewrite : g.r * (q : ℝ) ^ 2 / 8 =
        g.X * (q : ℝ) ^ 2 / (8 * g.M ^ 2) := by
      dsimp [HyperbolaGeometricData.r]
      field_simp [ne_of_gt hMpos]
    rw [hrewrite] at huLower
    exact huLower
  have htLower : g.X * (q : ℝ) / (2 * g.M) ≤ t := by
    have htSq : t ^ 2 = 4 * u * g.X := by
      dsimp [t]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hlowNonneg : 0 ≤ g.X * (q : ℝ) / (2 * g.M) := by positivity
    have htNonneg : 0 ≤ t := le_of_lt htpos
    have hlowSq :
        (g.X * (q : ℝ) / (2 * g.M)) ^ 2 ≤ t ^ 2 := by
      rw [htSq]
      have hmul := mul_le_mul_of_nonneg_right huLowerR
        (show 0 ≤ 4 * g.X by positivity)
      have hlowSq' :
          (g.X * (q : ℝ) / (2 * g.M)) ^ 2 =
            g.X ^ 2 * (q : ℝ) ^ 2 / (4 * g.M ^ 2) := by
        field_simp [ne_of_gt hMpos]
        norm_num
      rw [hlowSq']
      field_simp [ne_of_gt hMpos] at hmul
      have hnumNonneg : 0 ≤ g.X ^ 2 * (q : ℝ) ^ 2 := by positivity
      have hcmp :
          g.X ^ 2 * (q : ℝ) ^ 2 / (4 * g.M ^ 2) ≤
            g.X ^ 2 * (q : ℝ) ^ 2 / (2 * g.M ^ 2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [hnumNonneg, hM2pos]
      calc
        g.X ^ 2 * (q : ℝ) ^ 2 / (4 * g.M ^ 2) ≤
            g.X ^ 2 * (q : ℝ) ^ 2 / (2 * g.M ^ 2) := hcmp
        _ = (g.X * (q : ℝ) ^ 2) * (g.X / (2 * g.M ^ 2)) := by
          field_simp [ne_of_gt hMpos]
        _ ≤ (8 * g.M ^ 2 * u) * (g.X / (2 * g.M ^ 2)) :=
          mul_le_mul_of_nonneg_right hmul (by positivity)
        _ = 4 * u * g.X := by
          field_simp [ne_of_gt hMpos]
          ring
    exact (sq_le_sq₀ hlowNonneg htNonneg).mp hlowSq
  have hwidth :
      (cellLinearCoordinate a q p : ℝ) - t ≤
        occupiedSliceWindowWidth g q := by
    have hcgt : t < (cellLinearCoordinate a q p : ℝ) := hcgt
    have hcpos : 0 < (cellLinearCoordinate a q p : ℝ) := by linarith [htpos]
    have hden : 0 < (cellLinearCoordinate a q p : ℝ) + t := by linarith
    have hfactor :
        ((cellLinearCoordinate a q p : ℝ) - t) *
            ((cellLinearCoordinate a q p : ℝ) + t) =
          (cellLinearCoordinate a q p : ℝ) ^ 2 - t ^ 2 := by ring
    have hdenLower :
        g.X * (q : ℝ) / g.M ≤
          (cellLinearCoordinate a q p : ℝ) + t := by
      have : 2 * t ≤ (cellLinearCoordinate a q p : ℝ) + t := by linarith
      have htwice := mul_le_mul_of_nonneg_left htLower (by norm_num : 0 ≤ (2 : ℝ))
      have htwiceEq :
          2 * (g.X * (q : ℝ) / (2 * g.M)) = g.X * (q : ℝ) / g.M := by
        field_simp [ne_of_gt hMpos]
      calc
        g.X * (q : ℝ) / g.M =
            2 * (g.X * (q : ℝ) / (2 * g.M)) := htwiceEq.symm
        _ ≤ 2 * t := htwice
        _ ≤ (cellLinearCoordinate a q p : ℝ) + t := this
    have hWnonneg :
        0 ≤ 4 * (E g.K₀ + (D g.K₀) ^ 2) * g.M ^ 2 /
          (g.Q : ℝ) ^ 2 := by positivity
    have hratio :
        ((cellLinearCoordinate a q p : ℝ) ^ 2 - t ^ 2) /
            ((cellLinearCoordinate a q p : ℝ) + t) ≤
          (4 * (E g.K₀ + (D g.K₀) ^ 2) * g.M ^ 2 /
              (g.Q : ℝ) ^ 2) / (g.X * (q : ℝ) / g.M) := by
      apply (div_le_div_iff₀ hden (div_pos (mul_pos hXpos hqpos) hMpos)).2
      exact mul_le_mul hdeltaUpper hdenLower (by positivity) hWnonneg
    have hquotient :
        (4 * (E g.K₀ + (D g.K₀) ^ 2) * g.M ^ 2 /
            (g.Q : ℝ) ^ 2) / (g.X * (q : ℝ) / g.M) =
          4 * (E g.K₀ + (D g.K₀) ^ 2) * R_q g q := by
      rw [R_q]
      field_simp [ne_of_gt hXpos, ne_of_gt hqpos, ne_of_gt hQpos,
        ne_of_gt hMpos]
      
    have hratioLine :
        (cellLinearCoordinate a q p : ℝ) - t ≤
          4 * (E g.K₀ + (D g.K₀) ^ 2) * R_q g q := by
      have hlinequot :
          (cellLinearCoordinate a q p : ℝ) - t =
            ((cellLinearCoordinate a q p : ℝ) ^ 2 - t ^ 2) /
              ((cellLinearCoordinate a q p : ℝ) + t) := by
        rw [← hfactor]
        field_simp [ne_of_gt hden]
      calc
        (cellLinearCoordinate a q p : ℝ) - t =
            ((cellLinearCoordinate a q p : ℝ) ^ 2 - t ^ 2) /
              ((cellLinearCoordinate a q p : ℝ) + t) := hlinequot
        _ ≤ (4 * (E g.K₀ + (D g.K₀) ^ 2) * g.M ^ 2 /
              (g.Q : ℝ) ^ 2) / (g.X * (q : ℝ) / g.M) := hratio
        _ = 4 * (E g.K₀ + (D g.K₀) ^ 2) * R_q g q := hquotient
    dsimp [occupiedSliceWindowWidth]
    nlinarith [hratioLine, hKnonneg, hRqpos]
  have hcCast : (cellLinearCoordinate a q p : ℝ) = (c : ℝ) := by
    exact_mod_cast hcLine
  change (c : ℝ) ∈ Set.Ioc t (t + occupiedSliceWindowWidth g q)
  rw [← hcCast]
  constructor
  · exact hcgt
  · linarith [hwidth]

/-- A rational cell has at most `C_line * R_q` occupied linear slices. Each
occupied slice is the disjoint union of two finite interval progressions
with spacing `(q,-a)`, so the total number of progressions is at most
`2 * C_line * R_q`. -/
theorem occupiedSliceCount (g : HyperbolaGeometricData) (a q : ℕ)
    (hidx : positiveRationalCellIndexEligible g a q) :
    ∃ S : Finset ℤ,
      (∀ c, c ∈ S ↔ c ∈ occupiedSliceValues g a q) ∧
      (S.card : ℝ) ≤ C_line g.K₀ * R_q g q ∧
      (∀ p, p ∈ cellLinearSlice g a q ↔
        ∃ c ∈ S, p ∈ cellLinearSliceOnLine g a q c) ∧
      (∀ c c', c ∈ S → c' ∈ S → c ≠ c' →
        Disjoint (cellLinearSliceOnLine g a q c)
          (cellLinearSliceOnLine g a q c')) ∧
      (∀ c ∈ S,
        ∃ base : ℤ × ℤ, ∃ lo₁ hi₁ lo₂ hi₂ : ℤ,
          cellLinearSliceOnLine g a q c =
            cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁ ∪
              cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂ ∧
          Disjoint
            (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁)
            (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂) ∧
          (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁).Finite ∧
          (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂).Finite) ∧
      2 * (S.card : ℝ) ≤ 2 * C_line g.K₀ * R_q g q := by
  classical
  have hqlo : 1 ≤ q := hidx.1.2.1
  have hqhi : q ≤ g.Q := hidx.1.2.2.1
  have hparams := admissibleParameterBounds g q hqlo hqhi
  have hSliceFinite : (cellLinearSlice g a q).Finite := by
    apply hparams.lattice_finite.subset
    intro p hp
    exact hp.1
  have hImage : occupiedSliceValues g a q =
      (cellLinearCoordinate a q) '' cellLinearSlice g a q := by
    ext c
    change (cellLinearSliceOnLine g a q c).Nonempty ↔
      ∃ p ∈ cellLinearSlice g a q, cellLinearCoordinate a q p = c
    simp [cellLinearSliceOnLine, cellLinearCoordinate, Set.Nonempty, eq_comm]
  have hOccupiedFinite : (occupiedSliceValues g a q).Finite := by
    rw [hImage]
    exact hSliceFinite.image _
  let S : Finset ℤ := hOccupiedFinite.toFinset
  have hSmem : ∀ c, c ∈ S ↔ c ∈ occupiedSliceValues g a q := by
    intro c
    simp [S]
  let t : ℝ := 2 * Real.sqrt ((a : ℝ) * (q : ℝ) * g.X)
  let B : ℝ := occupiedSliceWindowWidth g q
  have hKnonneg : 0 ≤ E g.K₀ + (D g.K₀) ^ 2 := by
    dsimp [E, D]
    positivity
  have hRqge : 1 ≤ R_q g q := hparams.R_lower
  have hBnonneg : 0 ≤ B := by
    dsimp [B, occupiedSliceWindowWidth]
    positivity
  have hlen : (t + B) - t ≤ B := by linarith
  have hcardBasic : (S.card : ℝ) ≤ B + 1 := by
    have hcount := residueClassIntervalCount
      (Set.Ioc t (t + B)) Set.ordConnected_Ioc S 0 1 t (t + B) B
      (by linarith) hBnonneg hlen
      (by
        intro x hx
        rcases Set.mem_Ioc.mp hx with ⟨hlt, hle⟩
        exact ⟨hlt.le, hle⟩)
      (by
        intro c hc
        have hcOcc : c ∈ occupiedSliceValues g a q := (hSmem c).mp hc
        have hcIoc := occupiedSliceValue_mem_Ioc g a q hidx hcOcc
        simpa [t, B, occupiedSliceWindowWidth] using hcIoc)
      (by norm_num)
      (by
        intro c hc
        norm_num [Int.ModEq])
    simpa [B] using hcount
  have hcard : (S.card : ℝ) ≤ C_line g.K₀ * R_q g q := by
    have hBudget : B + 1 ≤ C_line g.K₀ * R_q g q := by
      dsimp [B, occupiedSliceWindowWidth, C_line]
      calc
        8 * (E g.K₀ + (D g.K₀) ^ 2) * R_q g q + 1 ≤
            8 * (E g.K₀ + (D g.K₀) ^ 2) * R_q g q + R_q g q := by
              nlinarith [hRqge]
        _ = (8 * (E g.K₀ + (D g.K₀) ^ 2) + 1) * R_q g q := by ring
    exact hcardBasic.trans hBudget
  have hcoverage : ∀ p, p ∈ cellLinearSlice g a q ↔
      ∃ c ∈ S, p ∈ cellLinearSliceOnLine g a q c := by
    intro p
    constructor
    · intro hp
      let c := cellLinearCoordinate a q p
      have hcOcc : c ∈ occupiedSliceValues g a q := by
        change (cellLinearSliceOnLine g a q c).Nonempty
        exact ⟨p, hp, rfl⟩
      have hcS : c ∈ S := (hSmem c).mpr hcOcc
      exact ⟨c, hcS, hp, rfl⟩
    · rintro ⟨c, _, hp⟩
      change p ∈ cellLinearSlice g a q ∧
        cellLinearCoordinate a q p = c at hp
      exact hp.1
  have hdisjoint : ∀ c c', c ∈ S → c' ∈ S → c ≠ c' →
      Disjoint (cellLinearSliceOnLine g a q c)
        (cellLinearSliceOnLine g a q c') := by
    intro c c' _ _ hcc'
    apply Set.disjoint_left.mpr
    intro p hp hp'
    exact hcc' (hp.2.symm.trans hp'.2)
  have hdecomp : ∀ c ∈ S,
      ∃ base : ℤ × ℤ, ∃ lo₁ hi₁ lo₂ hi₂ : ℤ,
        cellLinearSliceOnLine g a q c =
          cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁ ∪
            cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂ ∧
        Disjoint
          (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁)
          (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂) ∧
        (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₁ hi₁).Finite ∧
        (cellLatticeIccProgression base (q : ℤ) (a : ℤ) lo₂ hi₂).Finite := by
    intro c hc
    exact cellLinearSlices_progression_decomposition g a q hidx c
  have hprogressions : 2 * (S.card : ℝ) ≤
      2 * C_line g.K₀ * R_q g q := by
    calc
      2 * (S.card : ℝ) ≤ 2 * (C_line g.K₀ * R_q g q) :=
        mul_le_mul_of_nonneg_left hcard (by norm_num)
      _ = 2 * C_line g.K₀ * R_q g q := by ring
  exact ⟨S, hSmem, hcard, hcoverage, hdisjoint, hdecomp, hprogressions⟩

end FractionalPrimes.Literature.Hyperbola
