module

public import FractionalPrimes.Literature.Ergodic.SparseScaleSummability
public import FractionalPrimes.SparseScales
public import FractionalPrimes.GeneralDiscreteLpBridge
public import FractionalPrimes.LongShortVariationFacts
public import FractionalPrimes.ScalePartitions
public import FractionalPrimes.VariationAbsoluteSum
public import FractionalPrimes.MixedNorm
import Mathlib.Data.Finset.Sort

/-!
# Logarithmic perturbation of a bounded variation family

This module formalizes the abstract long/short perturbation proposition
`er:perturbation` for operators on counting-measure `ℓᵖ(ℤ)`.
-/

public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Positive scales are indexed by their offset from one. -/
def scaleIndexEquiv : Scale ≃ ℕ where
  toFun N := N.1 - 1
  invFun k := ⟨k + 1, by omega⟩
  left_inv N := by
    apply Subtype.ext
    exact Nat.sub_add_cancel N.2
  right_inv k := by simp

/-- The counting-measure sequence space with exponent `p`. -/
abbrev IntegerSequenceLp (p : ℝ) :=
  lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)

/-- The counting-measure `Lᵖ` norm of a sequence is the ordinary `ℓᵖ`
norm of its sequence-space representative. -/
theorem eLpNorm_integerSequenceLp_eq {p : ℝ}
    (hp0 : ENNReal.ofReal p ≠ 0) (hpTop : ENNReal.ofReal p ≠ ∞)
    [Fact (1 ≤ ENNReal.ofReal p)] (f : IntegerSequenceLp p) :
    eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count =
      ENNReal.ofReal ‖f‖ := by
  let hf := memLp_count_of_memlp_seq_finite hp0 hpTop f
  calc
    eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count =
      ‖hf.toLp (f : ℤ → ℂ)‖ₑ := (Lp.enorm_toLp hf).symm
    _ = ‖generalLpToCountLp hp0 hpTop f‖ₑ := by rfl
    _ = ENNReal.ofReal ‖generalLpToCountLp hp0 hpTop f‖ := by simp
    _ = ENNReal.ofReal ‖f‖ := by rw [generalLpToCountLp_norm]

/-- Counting measure on the integers viewed as an identity-preserving system,
used to instantiate the project finite-block `Lᵖ` estimate. -/
def integerCountIdentitySystem : InvertibleSystem ℤ where
  μ := Measure.count
  sigmaFinite := by infer_instance
  T := MeasurableEquiv.refl ℤ
  preserves := MeasurePreserving.id Measure.count

/-- A continuous operator norm bound passes to its pointwise counting-measure
representatives. -/
theorem eLpNorm_integerSequenceLp_map_le {p : ℝ}
    (hp0 : ENNReal.ofReal p ≠ 0) (hpTop : ENNReal.ofReal p ≠ ∞)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (T : IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (f : IntegerSequenceLp p) :
    eLpNorm (T f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal ‖T‖ * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  rw [eLpNorm_integerSequenceLp_eq hp0 hpTop (T f),
    eLpNorm_integerSequenceLp_eq hp0 hpTop f]
  calc
    ENNReal.ofReal ‖T f‖ ≤ ENNReal.ofReal (‖T‖ * ‖f‖) :=
      ENNReal.ofReal_le_ofReal (T.le_opNorm f)
    _ = ENNReal.ofReal ‖T‖ * ENNReal.ofReal ‖f‖ := by
      rw [ENNReal.ofReal_mul (norm_nonneg T)]

/-- Operator-norm decay on the sparse scales is summable; the finitely many
values below `3` are controlled by the two small-scale operator norms. -/
theorem summable_sparseScaleOperatorDistance {p : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (Q P : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (hdecay : ∀ D : ℝ, 0 < D →
      ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ N : Scale, 3 ≤ N.1 →
        ‖Q N - P N‖ ≤ C_D *
          Real.rpow (Real.log (N.1 : ℝ)) (-D)) :
    Summable (fun k : ℕ =>
      ‖Q (sparseScaleAsScale hp k) - P (sparseScaleAsScale hp k)‖) := by
  let e : ℕ → ℝ := fun k =>
    ‖Q (sparseScaleAsScale hp k) - P (sparseScaleAsScale hp k)‖
  let B : ℝ := max
    ‖Q ⟨1, by norm_num⟩ - P ⟨1, by norm_num⟩‖
    ‖Q ⟨2, by norm_num⟩ - P ⟨2, by norm_num⟩‖
  let D : ℝ := 2 / sparseScaleTau p
  have hτpos : 0 < sparseScaleTau p := sparseScaleTau_pos hp
  have hDpos : 0 < D := by dsimp [D]; positivity
  obtain ⟨C_D, hC_D, hdecayD⟩ := hdecay D hDpos
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he_nonneg (k : ℕ) : 0 ≤ e k := by
    dsimp [e]
    exact norm_nonneg _
  have he_small (k : ℕ) (hk : sparseScale p k < 3) : e k ≤ B := by
    have hkpos : 1 ≤ sparseScale p k := by
      calc
        1 = sparseScale p 0 := (sparseScale_zero hp).symm
        _ ≤ sparseScale p k := sparseScale_monotone hp (Nat.zero_le k)
    have hkval : (sparseScaleAsScale hp k).1 = sparseScale p k := by
      rfl
    have hklt : (sparseScaleAsScale hp k).1 < 3 := by simpa [hkval] using hk
    have hcase : (sparseScaleAsScale hp k).1 = 1 ∨
        (sparseScaleAsScale hp k).1 = 2 := by omega
    rcases hcase with hone | htwo
    · have hscale : sparseScaleAsScale hp k = ⟨1, by norm_num⟩ :=
        Subtype.ext hone
      dsimp [e]
      rw [hscale]
      exact le_max_left _ _
    · have hscale : sparseScaleAsScale hp k = ⟨2, by norm_num⟩ :=
        Subtype.ext htwo
      dsimp [e]
      rw [hscale]
      exact le_max_right _ _
  have he_decay (k : ℕ) (hk : 3 ≤ sparseScale p k) :
      e k ≤ C_D * Real.rpow (Real.log (sparseScale p k : ℝ))
        (-(2 / sparseScaleTau p)) := by
    have hkval : (sparseScaleAsScale hp k).1 = sparseScale p k := rfl
    have hbound := hdecayD (sparseScaleAsScale hp k) (by omega)
    simpa [e, D, hkval] using hbound
  exact summable_sparseScale_error_of_log_decay hp e B C_D hB hC_D
    he_nonneg he_small he_decay

/-- Reindexing a variation by a nondecreasing scale map cannot increase it,
even when the map has plateaus.  The finite proof compresses each sampled
chain to its ordered image; plateau increments vanish. -/
private theorem rVariation_comp_monotone_le {r : ℝ} (hr : 1 ≤ r)
    (u : Scale → ℂ) (φ : Scale → Scale) (hφ : Monotone φ) :
    rVariation r (fun N => u (φ N)) ≤ rVariation r u := by
  classical
  rw [rVariation_eq]
  apply iSup_le
  intro n
  apply iSup_le
  intro chain
  let f : Fin (n + 1) → Scale := fun i => φ (chain.index i)
  have hf : Monotone f := hφ.comp chain.strictMono.monotone
  let S : Finset Scale := Finset.univ.image f
  let m : ℕ := S.card - 1
  have hScard : 0 < S.card := by
    apply Finset.card_pos.mpr
    refine ⟨f 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  have hcard : S.card = m + 1 := by
    dsimp [m]
    exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hScard.ne')).symm
  let e : Fin (m + 1) ↪o Scale := S.orderEmbOfFin hcard
  let imageChain : StrictScaleChain m := ⟨e, e.strictMono⟩
  let indexOf : (i : Fin (n + 1)) → Fin (m + 1) := fun i =>
    (S.orderIsoOfFin hcard).symm ⟨f i,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have heq (i : Fin (n + 1)) : e (indexOf i) = f i := by
    change ↑((S.orderIsoOfFin hcard)
      ((S.orderIsoOfFin hcard).symm ⟨f i,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)) = f i
    simp
  have hindexMono : Monotone indexOf := by
    intro i j hij
    apply (S.orderIsoOfFin hcard).symm.monotone
    exact hf hij
  let sourceTerm : Fin n → ℝ≥0∞ := fun i =>
    (ENNReal.ofReal ‖u (f i.succ) - u (f i.castSucc)‖).rpow r
  let targetTerm : Fin m → ℝ≥0∞ := fun j =>
    (ENNReal.ofReal ‖u (e j.succ) - u (e j.castSucc)‖).rpow r
  let transitions : Finset (Fin n) :=
    Finset.univ.filter (fun i => f i.castSucc < f i.succ)
  have hsourceZero (i : Fin n) (hi : i ∉ transitions) : sourceTerm i = 0 := by
    have hle : f i.castSucc ≤ f i.succ := hf (le_of_lt i.castSucc_lt_succ)
    have hnot : ¬ f i.castSucc < f i.succ := by
      simpa [transitions] using hi
    have heq : f i.castSucc = f i.succ := le_antisymm hle (le_of_not_gt hnot)
    simp [sourceTerm, heq, ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hr)]
  have hzero :
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin n => ¬ f i.castSucc < f i.succ), sourceTerm i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hsourceZero i (by simpa [transitions] using hi)
  have hsumFilter :
      (∑ i : Fin n, sourceTerm i) = ∑ i ∈ transitions, sourceTerm i := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun i : Fin n => f i.castSucc < f i.succ) (f := sourceTerm)]
    rw [hzero, add_zero]
  have hAdjacent (i : Fin n) (hi : i ∈ transitions) :
      (indexOf i.succ).val = (indexOf i.castSucc).val + 1 := by
    have hstep : f i.castSucc < f i.succ := by
      simpa [transitions] using hi
    have hidx : indexOf i.castSucc < indexOf i.succ := by
      apply (S.orderIsoOfFin hcard).symm.strictMono
      change (⟨f i.castSucc,
        Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩⟩ : S) <
        ⟨f i.succ, Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, rfl⟩⟩
      exact hstep
    by_contra hnot
    have hgap : (indexOf i.castSucc).val + 1 < (indexOf i.succ).val := by omega
    let mid : Fin (m + 1) := ⟨(indexOf i.castSucc).val + 1, by omega⟩
    have hleft : e (indexOf i.castSucc) < e mid := by
      apply e.strictMono
      apply Fin.lt_def.mpr
      simp only [mid]
      omega
    have hright : e mid < e (indexOf i.succ) := by
      apply e.strictMono
      apply Fin.lt_def.mpr
      simp only [mid]
      omega
    have hmidmem : e mid ∈ S := Finset.orderEmbOfFin_mem S hcard mid
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmidmem
    have hfj : f j = e mid := hj
    have houter : f i.castSucc < f j ∧ f j < f i.succ := by
      constructor
      · calc
          f i.castSucc = e (indexOf i.castSucc) := (heq _).symm
          _ < e mid := hleft
          _ = f j := hfj.symm
      · calc
          f j = e mid := hfj
          _ < e (indexOf i.succ) := hright
          _ = f i.succ := heq _
    have hjloc : j ≤ i.castSucc ∨ i.succ ≤ j := by
      have hjval : (j : ℕ) ≤ (i : ℕ) ∨ (i : ℕ) + 1 ≤ (j : ℕ) := by omega
      rcases hjval with hjval | hjval
      · exact Or.inl (Fin.le_iff_val_le_val.mpr (by simpa using hjval))
      · exact Or.inr (Fin.le_iff_val_le_val.mpr (by simpa using hjval))
    rcases hjloc with hjle | hle
    · have hmono := hf hjle
      exact (not_lt_of_ge hmono) houter.1
    · have hmono := hf hle
      exact (not_lt_of_ge hmono) houter.2
  let edgeIndex : (i : ↥transitions) → Fin m := fun i =>
    ⟨(indexOf i.val.castSucc).val, by
      have hadj := hAdjacent i.val i.property
      have hright := (indexOf i.val.succ).isLt
      omega⟩
  have hleftEdge (i : ↥transitions) :
      e (edgeIndex i).castSucc = f i.val.castSucc := by
    have hidx : (edgeIndex i).castSucc = indexOf i.val.castSucc := by
      apply Fin.ext
      rfl
    rw [hidx]
    exact heq _
  have hrightEdge (i : ↥transitions) :
      e (edgeIndex i).succ = f i.val.succ := by
    have hadj := hAdjacent i.val i.property
    have hidx : (edgeIndex i).succ = indexOf i.val.succ := by
      apply Fin.ext
      change (indexOf i.val.castSucc).val + 1 = (indexOf i.val.succ).val
      exact hadj.symm
    rw [hidx]
    exact heq _
  have hedgeTerm (i : ↥transitions) :
      sourceTerm i.val = targetTerm (edgeIndex i) := by
    simp only [sourceTerm, targetTerm]
    rw [← hleftEdge i, ← hrightEdge i]
  have hedgeIndexInj : Function.Injective edgeIndex := by
    intro a b hab
    apply Subtype.ext
    have hstart : f a.val.castSucc = f b.val.castSucc := by
      calc
        f a.val.castSucc = e (edgeIndex a).castSucc := (hleftEdge a).symm
        _ = e (edgeIndex b).castSucc := by rw [hab]
        _ = f b.val.castSucc := hleftEdge b
    have hend : f a.val.succ = f b.val.succ := by
      calc
        f a.val.succ = e (edgeIndex a).succ := (hrightEdge a).symm
        _ = e (edgeIndex b).succ := by rw [hab]
        _ = f b.val.succ := hrightEdge b
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbetween : a.val.succ ≤ b.val.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hlt)
      have hmon := hf hbetween
      rw [hend] at hmon
      have htransB : f b.val.castSucc < f b.val.succ :=
        (Finset.mem_filter.mp b.property).2
      exact (not_lt_of_ge hmon) htransB
    · have hbetween : b.val.succ ≤ a.val.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hgt)
      have hmon := hf hbetween
      rw [← hend] at hmon
      have htransA : f a.val.castSucc < f a.val.succ :=
        (Finset.mem_filter.mp a.property).2
      exact (not_lt_of_ge hmon) htransA
  have hinjOn : Set.InjOn edgeIndex (↑transitions.attach : Set (↥transitions)) := by
    intro a _ b _ hab
    exact hedgeIndexInj hab
  have hsumImage :
      (∑ i ∈ transitions, sourceTerm i) =
        ∑ j ∈ transitions.attach.image edgeIndex, targetTerm j := by
    calc
      (∑ i ∈ transitions, sourceTerm i) =
          ∑ i ∈ transitions.attach, sourceTerm i.val := by
        rw [← Finset.sum_attach]
      _ = ∑ i ∈ transitions.attach, targetTerm (edgeIndex i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hedgeTerm i
      _ = ∑ j ∈ transitions.attach.image edgeIndex, targetTerm j :=
        (Finset.sum_image (f := targetTerm) hinjOn).symm
  have hsubset : transitions.attach.image edgeIndex ⊆ Finset.univ := by
    intro j hj
    simp
  have hsumLe :
      (∑ i : Fin n, sourceTerm i) ≤ ∑ j : Fin m, targetTerm j := by
    rw [hsumFilter, hsumImage]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro j hj _
      exact bot_le)
  have hroot :
      (∑ i : Fin n, sourceTerm i).rpow r⁻¹ ≤
        (∑ j : Fin m, targetTerm j).rpow r⁻¹ :=
    ENNReal.rpow_le_rpow hsumLe (inv_nonneg.mpr (le_trans zero_le_one hr))
  change chainVariation r (fun N => u (φ N)) chain ≤ rVariation r u
  calc
    chainVariation r (fun N => u (φ N)) chain =
        (∑ i : Fin n, sourceTerm i).rpow r⁻¹ := by
      simp [chainVariation, sourceTerm, f]
    _ ≤ (∑ j : Fin m, targetTerm j).rpow r⁻¹ := hroot
    _ = chainVariation r u imageChain := by
      simp [chainVariation, targetTerm, imageChain]
    _ ≤ rVariation r u := chainVariation_le_rVariation r u imageChain

/-- The finite-block estimate for an abstract family with the source
consecutive-increment bound.  Its coefficient is exactly the half-open
logarithmic block error `h_k`. -/
private theorem eLpNorm_sparseOperatorBlock_le {p : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (Q : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hinc : ∀ (m : ℕ) (hm : 1 ≤ m),
      ‖Q ⟨m + 1, by omega⟩ - Q ⟨m, hm⟩‖ ≤
        C0 * (Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)))
    (f : IntegerSequenceLp p) (k : ℕ) :
    eLpNorm (rVariationOnFun 2 (fun N => (Q N f : ℤ → ℂ))
      (Set.Icc (sparseScaleAsScale hp k) (sparseScaleAsScale hp (k + 1))))
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (C0 * sparseScaleBlockError p k) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hp)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := by simp
  let a : Scale := sparseScaleAsScale hp k
  let b : Scale := sparseScaleAsScale hp (k + 1)
  have hab : a ≤ b := by
    change sparseScale p k ≤ sparseScale p (k + 1)
    exact sparseScale_monotone hp (Nat.le_succ k)
  have hF : ∀ N, MemLp (fun x : ℤ => (Q N f : ℤ → ℂ) x)
      (ENNReal.ofReal p) Measure.count := by
    intro N
    exact memLp_count_of_memlp_seq_finite hp0 hpTop (Q N f)
  have hbase := eLpNorm_rVariationOnFun_scaleInterval_le_sum
    integerCountIdentitySystem p 2 hp.le (by norm_num)
    (fun N x => (Q N f : ℤ → ℂ) x) a b hab hF
  have hcoeff_nonneg (m : ℕ) (hm : 1 ≤ m) :
      0 ≤ Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1) := by
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * m by omega)
    · positivity
  have hterm (i : ℕ) (hi : i < b.1 - a.1) :
      eLpNorm (fun x : ℤ =>
        (Q (scaleOffset a (i + 1)) f : ℤ → ℂ) x -
          (Q (scaleOffset a i) f : ℤ → ℂ) x)
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (C0 *
        (Real.log (2 * ((scaleOffset a i).1 : ℝ)) /
          ((scaleOffset a i).1 + 1 : ℝ))) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    let m := (scaleOffset a i).1
    have hm : 1 ≤ m := (scaleOffset a i).2
    have hnext : scaleOffset a (i + 1) = ⟨m + 1, by omega⟩ := by
      apply Subtype.ext
      simp [m, scaleOffset, Nat.add_assoc]
    have hcurr : scaleOffset a i = ⟨m, hm⟩ := by
      apply Subtype.ext
      rfl
    have hmap := eLpNorm_integerSequenceLp_map_le hp0 hpTop
      (Q (scaleOffset a (i + 1)) - Q (scaleOffset a i)) f
    have hfun :
        (fun x : ℤ =>
          (Q (scaleOffset a (i + 1)) f : ℤ → ℂ) x -
            (Q (scaleOffset a i) f : ℤ → ℂ) x) =
          ((Q (scaleOffset a (i + 1)) - Q (scaleOffset a i)) f : ℤ → ℂ) := by
      funext x
      simp
    rw [hfun]
    have hbound := hinc m hm
    have hcoeff :
        ‖Q (scaleOffset a (i + 1)) - Q (scaleOffset a i)‖ ≤
          C0 * (Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)) := by
      simpa only [hnext, hcurr, Subtype.coe_mk] using hbound
    exact hmap.trans (mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal hcoeff) bot_le)
  have hrealCoeff :
      (∑ i ∈ Finset.range (b.1 - a.1),
        Real.log (2 * ((scaleOffset a i).1 : ℝ)) /
          ((scaleOffset a i).1 + 1 : ℝ)) = sparseScaleBlockError p k := by
    have ha : a.1 = sparseScale p k := rfl
    have hb : b.1 = sparseScale p (k + 1) := rfl
    calc
      (∑ i ∈ Finset.range (b.1 - a.1),
          Real.log (2 * ((scaleOffset a i).1 : ℝ)) /
            ((scaleOffset a i).1 + 1 : ℝ)) =
        ∑ i ∈ Finset.range
            (sparseScale p (k + 1) - sparseScale p k),
          Real.log (2 * (((sparseScale p k + i : ℕ) : ℝ))) /
            ((sparseScale p k + i : ℕ) + 1 : ℝ) := by
          rw [ha, hb]
          apply Finset.sum_congr rfl
          intro i hi
          simp [scaleOffset, ha]
      _ = ∑ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
          Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1) :=
        sum_range_add_eq_sum_Ico (sparseScale p k)
          (sparseScale p (k + 1))
          (fun m => Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1))
      _ = sparseScaleBlockError p k := by
        rw [← sparseScaleBlockError_eq_sum]
  have hcoefSum :
      (∑ i ∈ Finset.range (b.1 - a.1),
        ENNReal.ofReal (C0 *
          (Real.log (2 * ((scaleOffset a i).1 : ℝ)) /
            ((scaleOffset a i).1 + 1 : ℝ)))) =
        ENNReal.ofReal (C0 * sparseScaleBlockError p k) := by
    have hblocknonneg := sparseScaleBlockError_nonneg hp k
    calc
      (∑ i ∈ Finset.range (b.1 - a.1),
          ENNReal.ofReal (C0 *
            (Real.log (2 * ((scaleOffset a i).1 : ℝ)) /
              ((scaleOffset a i).1 + 1 : ℝ)))) =
        ∑ i ∈ Finset.range (b.1 - a.1),
          ENNReal.ofReal C0 * ENNReal.ofReal
            (Real.log (2 * ((scaleOffset a i).1 : ℝ)) /
              ((scaleOffset a i).1 + 1 : ℝ)) := by
          apply Finset.sum_congr
          · rfl
          · intro i hi
            rw [ENNReal.ofReal_mul hC0]
      _ = ENNReal.ofReal C0 *
          ∑ i ∈ Finset.range (b.1 - a.1),
            ENNReal.ofReal
              (Real.log (2 * ((scaleOffset a i).1 : ℝ)) /
                ((scaleOffset a i).1 + 1 : ℝ)) := by
          rw [Finset.mul_sum]
      _ = ENNReal.ofReal C0 *
          ENNReal.ofReal
            (∑ i ∈ Finset.range (b.1 - a.1),
              Real.log (2 * ((scaleOffset a i).1 : ℝ)) /
                ((scaleOffset a i).1 + 1 : ℝ)) := by
          congr 1
          exact (ENNReal.ofReal_sum_of_nonneg (fun i hi =>
            hcoeff_nonneg (scaleOffset a i).1 (scaleOffset a i).2)).symm
      _ = ENNReal.ofReal C0 * ENNReal.ofReal (sparseScaleBlockError p k) := by
          rw [hrealCoeff]
      _ = ENNReal.ofReal (C0 * sparseScaleBlockError p k) := by
          rw [ENNReal.ofReal_mul hC0]
  calc
    _ ≤ ∑ i ∈ Finset.range (b.1 - a.1),
        eLpNorm (fun x : ℤ =>
          (Q (scaleOffset a (i + 1)) f : ℤ → ℂ) x -
            (Q (scaleOffset a i) f : ℤ → ℂ) x)
          (ENNReal.ofReal p) Measure.count := hbase
    _ ≤ ∑ i ∈ Finset.range (b.1 - a.1),
        ENNReal.ofReal (C0 *
          (Real.log (2 * ((scaleOffset a i).1 : ℝ)) /
            ((scaleOffset a i).1 + 1 : ℝ))) *
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i (Finset.mem_range.mp hi)
    _ = ENNReal.ofReal (C0 * sparseScaleBlockError p k) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      rw [← Finset.sum_mul, hcoefSum]

/-- Summing a summable family of operator errors in pointwise norm is bounded
in `Lᵖ` by the sum of the operator norms. -/
private theorem eLpNorm_tsum_operatorError_le {p : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (E : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (hE : Summable (fun N : Scale => ‖E N‖))
    (f : IntegerSequenceLp p) :
    eLpNorm (fun x : ℤ => ∑' N : Scale,
      ‖((E N) f : ℤ → ℂ) x‖)
      (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (∑' N : Scale, ‖E N‖) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hp)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := by simp
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  let H : Scale → ℤ → ℂ := fun N x => ((E N) f : ℤ → ℂ) x
  have hmem (N : Scale) :
      MemLp (H N) (ENNReal.ofReal p) Measure.count := by
    exact memLp_count_of_memlp_seq_finite hp0 hpTop (E N f)
  have hterm (N : Scale) :
      eLpNorm (H N) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal ‖E N‖ *
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    exact eLpNorm_integerSequenceLp_map_le hp0 hpTop (E N) f
  have hsumCompare :
      (∑' N : Scale, eLpNorm (H N) (ENNReal.ofReal p) Measure.count) ≤
        ENNReal.ofReal (∑' N : Scale, ‖E N‖) *
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    calc
      _ ≤ ∑' N : Scale, ENNReal.ofReal ‖E N‖ *
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count :=
        ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' N : Scale, ‖E N‖) *
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
          (fun N => norm_nonneg (E N)) hE]
  have hsumTop :
      (∑' N : Scale, eLpNorm (H N) (ENNReal.ofReal p) Measure.count) ≠ ∞ := by
    have hOpTop : ENNReal.ofReal (∑' N : Scale, ‖E N‖) ≠ ∞ := by
      exact ENNReal.ofReal_ne_top
    have hfTop :
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count ≠ ∞ := by
      rw [eLpNorm_integerSequenceLp_eq hp0 hpTop f]
      exact ENNReal.ofReal_ne_top
    apply ne_of_lt
    exact lt_of_le_of_lt hsumCompare
      (ENNReal.mul_ne_top hOpTop hfTop |>.lt_top)
  calc
    eLpNorm (fun x : ℤ => ∑' N : Scale, ‖H N x‖)
        (ENNReal.ofReal p) Measure.count ≤
      ∑' N : Scale, eLpNorm (H N) (ENNReal.ofReal p) Measure.count :=
        eLpNorm_tsum_norm_le_tsum_eLpNorm hpENN H hmem hsumTop
    _ ≤ ENNReal.ofReal (∑' N : Scale, ‖E N‖) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := hsumCompare

/-- The sparse long variation is controlled by the reference variation and
the summable operator errors. -/
private theorem eLpNorm_sparseLongVariation_le {p r : ℝ}
    (hp : 1 < p) (hr2 : 2 ≤ r) [Fact (1 ≤ ENNReal.ofReal p)]
    (S : Scale → Scale) (hS : Monotone S)
    (Q P : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (CP : ℝ)
    (hP : ∀ f : IntegerSequenceLp p,
      eLpNorm (rVariationFun r (fun N => (P N f : ℤ → ℂ)))
        (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal CP * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count)
    (hE : Summable (fun N : Scale => ‖Q (S N) - P (S N)‖))
    (f : IntegerSequenceLp p) :
    eLpNorm (rVariationFun r (fun N => (Q (S N) f : ℤ → ℂ)))
        (ENNReal.ofReal p) Measure.count ≤
      (ENNReal.ofReal CP +
        2 * ENNReal.ofReal (∑' N : Scale, ‖Q (S N) - P (S N)‖)) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hp)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := by simp
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hr1 : 1 ≤ r := by linarith
  let E : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p :=
    fun N => Q (S N) - P (S N)
  let FQ : Scale → ℤ → ℂ := fun N => (Q (S N) f : ℤ → ℂ)
  let FP : Scale → ℤ → ℂ := fun N => (P (S N) f : ℤ → ℂ)
  let FE : Scale → ℤ → ℂ := fun N => (E N f : ℤ → ℂ)
  let G : ℤ → ℝ := fun x => ∑' N : Scale, ‖FE N x‖
  have hFQ (N : Scale) : MemLp (FQ N) (ENNReal.ofReal p) Measure.count := by
    exact memLp_count_of_memlp_seq_finite hp0 hpTop (Q (S N) f)
  have hFP (N : Scale) : MemLp (FP N) (ENNReal.ofReal p) Measure.count := by
    exact memLp_count_of_memlp_seq_finite hp0 hpTop (P (S N) f)
  have hFE (N : Scale) : MemLp (FE N) (ENNReal.ofReal p) Measure.count := by
    exact memLp_count_of_memlp_seq_finite hp0 hpTop (E N f)
  have hGmeas : AEMeasurable G Measure.count := by
    apply AEMeasurable.tsum
    intro N
    exact (measurable_of_countable _).aemeasurable
  have hGasm : AEStronglyMeasurable G Measure.count := hGmeas.aestronglyMeasurable
  have hGnonneg (x : ℤ) : 0 ≤ G x := tsum_nonneg fun N => norm_nonneg (FE N x)
  have hpointSummable (x : ℤ) : Summable (fun N : Scale => ‖FE N x‖) := by
    apply Summable.of_nonneg_of_le (fun N => norm_nonneg (FE N x))
    · intro N
      calc
        ‖FE N x‖ ≤ ‖E N f‖ := lp.norm_apply_le_norm hp0 (E N f) x
        _ ≤ ‖E N‖ * ‖f‖ := (E N).le_opNorm f
    · exact hE.mul_right ‖f‖
  have herrorPoint (x : ℤ) :
      ∑' N : Scale, ENNReal.ofReal ‖FE N x‖ = ENNReal.ofReal (G x) := by
    dsimp [G]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun N => norm_nonneg (FE N x)) (hpointSummable x)).symm
  have hQmeas : ∀ N, AEMeasurable (FQ N) Measure.count := by
    intro N
    exact (hFQ N).aestronglyMeasurable.aemeasurable
  have hPmeas : ∀ N, AEMeasurable (FP N) Measure.count := by
    intro N
    exact (hFP N).aestronglyMeasurable.aemeasurable
  have hLongQ : AEStronglyMeasurable (rVariationFun r FQ) Measure.count :=
    (aemeasurable_rVariationFun Measure.count r FQ hQmeas).aestronglyMeasurable
  have hLongP : AEStronglyMeasurable (rVariationFun r FP) Measure.count :=
    (aemeasurable_rVariationFun Measure.count r FP hPmeas).aestronglyMeasurable
  have hpoint (x : ℤ) :
      rVariationFun r FQ x ≤
        rVariationFun r FP x + ENNReal.ofReal (G x) + ENNReal.ofReal (G x) := by
    have hvariation := rVariation_le_of_pointwise_error r hr1
      (fun N => FQ N x) (fun N => FP N x) (fun N => FE N x) (by
        intro N
        simp [FQ, FP, FE, E])
    rw [rVariationFun_apply, rVariationFun_apply]
    calc
      rVariation r (fun N => FQ N x) ≤
          rVariation r (fun N => FP N x) +
            2 * ∑' N : Scale, ENNReal.ofReal ‖FE N x‖ := hvariation
      _ = rVariationFun r FP x +
          ENNReal.ofReal (G x) + ENNReal.ofReal (G x) := by
        rw [herrorPoint x]
        rw [rVariationFun_apply]
        simp [two_mul, add_assoc]
  have hmajor :
      eLpNorm (rVariationFun r FQ) (ENNReal.ofReal p) Measure.count ≤
        eLpNorm (fun x => rVariationFun r FP x +
          (ENNReal.ofReal (G x) + ENNReal.ofReal (G x)))
          (ENNReal.ofReal p) Measure.count := by
    apply eLpNorm_mono_enorm_ae hLongQ
    filter_upwards with x
    simpa only [enorm_eq_self, Pi.add_apply, add_assoc] using hpoint x
  have hGenn : AEStronglyMeasurable (fun x => ENNReal.ofReal (G x)) Measure.count := by
    exact ENNReal.continuous_ofReal.comp_aestronglyMeasurable hGasm
  have hGnorm :
      eLpNorm (fun x => ENNReal.ofReal (G x)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (∑' N : Scale, ‖E N‖) *
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    have hGofReal :
        eLpNorm (fun x => ENNReal.ofReal (G x)) (ENNReal.ofReal p) Measure.count =
          eLpNorm G (ENNReal.ofReal p) Measure.count := by
      exact eLpNorm_ofReal G (ae_of_all _ hGnonneg)
    rw [hGofReal]
    exact eLpNorm_tsum_operatorError_le hp E hE f
  have hPsample :
      eLpNorm (rVariationFun r FP) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal CP * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count := by
    calc
      eLpNorm (rVariationFun r FP) (ENNReal.ofReal p) Measure.count ≤
          eLpNorm (rVariationFun r (fun N => (P N f : ℤ → ℂ)))
            (ENNReal.ofReal p) Measure.count := by
        apply eLpNorm_mono_enorm_ae hLongP
        filter_upwards with x
        have hcomp := rVariation_comp_monotone_le hr1
          (fun N => (P N f : ℤ → ℂ) x) S hS
        simpa [FP, rVariationFun_apply] using hcomp
      _ ≤ ENNReal.ofReal CP * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count := hP f
  have hsumAdd := eLpNorm_add_le (p := ENNReal.ofReal p)
    (μ := Measure.count) hpENN
    (f := fun x => rVariationFun r FP x)
    (g := fun x => ENNReal.ofReal (G x) + ENNReal.ofReal (G x))
  have hdouble := eLpNorm_add_le (p := ENNReal.ofReal p)
    (μ := Measure.count) hpENN
    (f := fun x => ENNReal.ofReal (G x))
    (g := fun x => ENNReal.ofReal (G x))
  calc
    eLpNorm (rVariationFun r FQ) (ENNReal.ofReal p) Measure.count ≤
        eLpNorm (fun x => rVariationFun r FP x +
          (ENNReal.ofReal (G x) + ENNReal.ofReal (G x)))
          (ENNReal.ofReal p) Measure.count := hmajor
    _ ≤ eLpNorm (rVariationFun r FP) (ENNReal.ofReal p) Measure.count +
        eLpNorm (fun x => ENNReal.ofReal (G x) + ENNReal.ofReal (G x))
          (ENNReal.ofReal p) Measure.count := hsumAdd
    _ ≤ eLpNorm (rVariationFun r FP) (ENNReal.ofReal p) Measure.count +
        (eLpNorm (fun x => ENNReal.ofReal (G x)) (ENNReal.ofReal p) Measure.count +
          eLpNorm (fun x => ENNReal.ofReal (G x)) (ENNReal.ofReal p) Measure.count) :=
      add_le_add le_rfl hdouble
    _ ≤ ENNReal.ofReal CP * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count +
        (ENNReal.ofReal (∑' N : Scale, ‖E N‖) *
            eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count +
          ENNReal.ofReal (∑' N : Scale, ‖E N‖) *
            eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count) := by
      exact add_le_add hPsample (add_le_add hGnorm hGnorm)
    _ = (ENNReal.ofReal CP +
          2 * ENNReal.ofReal (∑' N : Scale, ‖E N‖)) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      simp [add_mul, two_mul]

/-- The sparse-block square function is bounded using the `q=min(p,2)`
summability of the logarithmic block errors. -/
private theorem eLpNorm_sparseBlockSquare_le {p : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (Q : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hinc : ∀ (m : ℕ) (hm : 1 ≤ m),
      ‖Q ⟨m + 1, by omega⟩ - Q ⟨m, hm⟩‖ ≤
        C0 * (Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)))
    (f : IntegerSequenceLp p) :
    eLpNorm (fun x : ℤ =>
      (∑' k : ℕ,
        (rVariationOnFun 2 (fun N => (Q N f : ℤ → ℂ))
          (Set.Icc (sparseScaleAsScale hp k)
            (sparseScaleAsScale hp (k + 1))) x) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ)) (ENNReal.ofReal p) Measure.count ≤
      ((ENNReal.ofReal C0 ^ sparseScaleQ p *
        ∑' k : ℕ, (ENNReal.ofReal (sparseScaleBlockError p k)) ^
          sparseScaleQ p) ^ (1 / sparseScaleQ p)) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hp)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := by simp
  let q : ℝ := sparseScaleQ p
  let s : ℕ → Scale := sparseScaleAsScale hp
  let F : Scale → ℤ → ℂ := fun N => (Q N f : ℤ → ℂ)
  let Block : ℕ → ℤ → ℝ≥0∞ := fun k =>
    rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1)))
  let c0 : ℝ≥0∞ := ENNReal.ofReal C0
  let hk : ℕ → ℝ := fun k => sparseScaleBlockError p k
  let Hk : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (hk k)
  let inputNorm : ℝ≥0∞ :=
    eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count
  let coeffSum : ℝ≥0∞ := ∑' k : ℕ, (c0 * Hk k) ^ q
  have hqpos : 1 < q := by
    dsimp [q]
    exact sparseScaleQ_gt_one hp
  have hqnonneg : 0 ≤ q := le_trans zero_le_one hqpos.le
  have hqne : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hqpos)
  have hrealSummable : Summable (fun k : ℕ => (hk k) ^ q) := by
    simpa [hk, q] using summable_sparseScaleBlockError_q hp
  have hhkNonneg (k : ℕ) : 0 ≤ hk k := by
    exact sparseScaleBlockError_nonneg hp k
  have hpowNonneg (k : ℕ) : 0 ≤ (hk k) ^ q :=
    Real.rpow_nonneg (hhkNonneg k) q
  have hHsum : (∑' k : ℕ, (Hk k) ^ q) ≠ ∞ := by
    have hsumEq :
        (∑' k : ℕ, (Hk k) ^ q) = ENNReal.ofReal (∑' k : ℕ, (hk k) ^ q) := by
      calc
        (∑' k : ℕ, (Hk k) ^ q) =
            ∑' k : ℕ, ENNReal.ofReal ((hk k) ^ q) := by
          apply tsum_congr
          intro k
          exact ENNReal.ofReal_rpow_of_nonneg (hhkNonneg k) hqnonneg
        _ = ENNReal.ofReal (∑' k : ℕ, (hk k) ^ q) :=
          (ENNReal.ofReal_tsum_of_nonneg hpowNonneg hrealSummable).symm
    rw [hsumEq]
    exact ENNReal.ofReal_ne_top
  have hc0top : c0 ^ q ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg hqnonneg
    simp [c0]
  have hcoeffSumEq : coeffSum = c0 ^ q * ∑' k : ℕ, (Hk k) ^ q := by
    calc
      coeffSum = ∑' k : ℕ, c0 ^ q * (Hk k) ^ q := by
        apply tsum_congr
        intro k
        rw [ENNReal.mul_rpow_of_nonneg c0 (Hk k) hqnonneg]
      _ = c0 ^ q * ∑' k : ℕ, (Hk k) ^ q := ENNReal.tsum_mul_left
  have hcoeffTop : coeffSum ≠ ∞ := by
    rw [hcoeffSumEq]
    exact ENNReal.mul_ne_top hc0top hHsum
  have hFmeas : ∀ N, AEMeasurable (F N) Measure.count := by
    intro N
    exact (memLp_count_of_memlp_seq_finite hp0 hpTop (Q N f)).aestronglyMeasurable.aemeasurable
  have hBlockMeas (k : ℕ) :
      AEStronglyMeasurable (Block k) Measure.count := by
    exact (aemeasurable_rVariationOnFun Measure.count 2 F
      (Set.Icc (s k) (s (k + 1))) hFmeas).aestronglyMeasurable
  have hBlockBound (k : ℕ) :
      eLpNorm (Block k) (ENNReal.ofReal p) Measure.count ≤
        (c0 * Hk k) * inputNorm := by
    have h := eLpNorm_sparseOperatorBlock_le hp Q C0 hC0 hinc f k
    simpa [Block, F, s, c0, Hk, hk, inputNorm, ENNReal.ofReal_mul hC0] using h
  have hBlockPow (k : ℕ) :
      (eLpNorm (Block k) (ENNReal.ofReal p) Measure.count) ^ q ≤
        ((c0 * Hk k) * inputNorm) ^ q :=
    ENNReal.rpow_le_rpow (hBlockBound k) hqnonneg
  have hScaledSum :
      (∑' k : ℕ, ((c0 * Hk k) * inputNorm) ^ q) = coeffSum * inputNorm ^ q := by
    calc
      (∑' k : ℕ, ((c0 * Hk k) * inputNorm) ^ q) =
          ∑' k : ℕ, ((c0 * Hk k) ^ q) * inputNorm ^ q := by
        apply tsum_congr
        intro k
        exact ENNReal.mul_rpow_of_nonneg (c0 * Hk k) inputNorm hqnonneg
      _ = coeffSum * inputNorm ^ q := ENNReal.tsum_mul_right
  have hroot (B : ℝ≥0∞) :
      (B * inputNorm ^ q) ^ (1 / q) = B ^ (1 / q) * inputNorm := by
    have hqmul : q * (1 / q) = 1 := by field_simp [hqne]
    calc
      (B * inputNorm ^ q) ^ (1 / q) =
          B ^ (1 / q) * (inputNorm ^ q) ^ (1 / q) :=
        ENNReal.mul_rpow_of_nonneg B (inputNorm ^ q) (by positivity)
      _ = B ^ (1 / q) * inputNorm := by
        rw [← ENNReal.rpow_mul, hqmul, ENNReal.rpow_one]
  have hmixed := eLpNorm_sparseBlockSquare_mixed Measure.count s F hp hFmeas
  calc
    eLpNorm (fun x : ℤ =>
        (∑' k : ℕ, (Block k x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) Measure.count ≤
      (∑' k : ℕ,
        (eLpNorm (Block k) (ENNReal.ofReal p) Measure.count) ^ q) ^ (1 / q) := by
          simpa [q, Block, F, s, sparseScaleQ_eq_min] using hmixed
    _ ≤ (coeffSum * inputNorm ^ q) ^ (1 / q) := by
      apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ 1 / q)
      calc
        (∑' k : ℕ,
            (eLpNorm (Block k) (ENNReal.ofReal p) Measure.count) ^ q) ≤
          ∑' k : ℕ, ((c0 * Hk k) * inputNorm) ^ q :=
            ENNReal.tsum_le_tsum hBlockPow
        _ = coeffSum * inputNorm ^ q := hScaledSum
    _ = coeffSum ^ (1 / q) * inputNorm := hroot coeffSum
    _ = ((ENNReal.ofReal C0 ^ sparseScaleQ p *
          ∑' k : ℕ, (ENNReal.ofReal (sparseScaleBlockError p k)) ^
            sparseScaleQ p) ^ (1 / sparseScaleQ p)) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      rw [hcoeffSumEq]

/-- The sparse-scale operator errors remain summable after reindexing them by
the positive scale type. -/
private theorem summable_sparseScaleOperatorError_scale {p : ℝ}
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (Q P : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (hdecay : ∀ D : ℝ, 0 < D →
      ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ N : Scale, 3 ≤ N.1 →
        ‖Q N - P N‖ ≤ C_D *
          Real.rpow (Real.log (N.1 : ℝ)) (-D)) :
    Summable (fun N : Scale =>
      ‖Q (sparseScaleAsScale hp (N.1 - 1)) -
        P (sparseScaleAsScale hp (N.1 - 1))‖) := by
  have hNat := summable_sparseScaleOperatorDistance hp Q P hdecay
  have hReindex := (scaleIndexEquiv.summable_iff).mpr hNat
  simpa [scaleIndexEquiv, Function.comp_def] using hReindex

/-- Logarithmic perturbations preserve the `r`-variation bound.  The
constant is constructed from the reference variation constant, the summable
sparse operator errors, and the `q=min(p,2)` block-error series. -/
theorem variationOfLogarithmicPerturbation_continuous {p r : ℝ}
    (hp : 1 < p) (hr2 : 2 ≤ r) [Fact (1 ≤ ENNReal.ofReal p)]
    (Q P : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p)
    (CP C0 : ℝ) (_hCP : 0 ≤ CP) (hC0 : 0 ≤ C0)
    (hP : ∀ f : IntegerSequenceLp p,
      eLpNorm (rVariationFun r (fun N => (P N f : ℤ → ℂ)))
        (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal CP * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count)
    (hdecay : ∀ D : ℝ, 0 < D →
      ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ N : Scale, 3 ≤ N.1 →
        ‖Q N - P N‖ ≤ C_D *
          Real.rpow (Real.log (N.1 : ℝ)) (-D))
    (hinc : ∀ (m : ℕ) (hm : 1 ≤ m),
      ‖Q ⟨m + 1, by omega⟩ - Q ⟨m, hm⟩‖ ≤
        C0 * (Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1))) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : IntegerSequenceLp p,
        eLpNorm (rVariationFun r (fun N => (Q N f : ℤ → ℂ)))
          (ENNReal.ofReal p) Measure.count ≤
          C * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  let s : ℕ → Scale := sparseScaleAsScale hp
  let S : Scale → Scale := fun N => sparseScaleAsScale hp (N.1 - 1)
  let opErrorSum : ℝ := ∑' N : Scale, ‖Q (S N) - P (S N)‖
  let q : ℝ := sparseScaleQ p
  let blockConstant : ℝ≥0∞ :=
    (ENNReal.ofReal C0 ^ q *
      ∑' k : ℕ,
        (ENNReal.ofReal (sparseScaleBlockError p k)) ^ q) ^ (1 / q)
  let longConstant : ℝ≥0∞ :=
    ENNReal.ofReal CP + 2 * ENNReal.ofReal opErrorSum
  let C : ℝ≥0∞ := 3 * longConstant + 3 * blockConstant
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hp)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := by simp
  have hqpos : 1 < q := by
    dsimp [q]
    exact sparseScaleQ_gt_one hp
  have hqnonneg : 0 ≤ q := le_trans zero_le_one hqpos.le
  have hqne : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hqpos)
  have hSmono : Monotone S := by
    intro A B hAB
    change A.1 ≤ B.1 at hAB
    dsimp [S]
    exact sparseScaleAsScale_monotone hp (Nat.sub_le_sub_right hAB 1)
  have hscale0 : s 0 = ⟨1, Nat.succ_pos 0⟩ := by
    dsimp [s]
    exact sparseScaleAsScale_zero hp
  have hscaleMono : Monotone s := by
    dsimp [s]
    exact sparseScaleAsScale_monotone hp
  have hscaleUnbounded :
      Filter.Tendsto s (Filter.atTop : Filter ℕ)
        (Filter.atTop : Filter Scale) := by
    dsimp [s]
    exact sparseScaleAsScale_tendsto_atTop hp
  have hE : Summable (fun N : Scale => ‖Q (S N) - P (S N)‖) := by
    simpa [S] using summable_sparseScaleOperatorError_scale hp Q P hdecay
  have hopErrorTop : ENNReal.ofReal opErrorSum ≠ ∞ := by
    have hsumEq : ENNReal.ofReal opErrorSum =
        ∑' N : Scale, ENNReal.ofReal ‖Q (S N) - P (S N)‖ := by
      dsimp [opErrorSum]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun N => norm_nonneg (Q (S N) - P (S N))) hE
    rw [hsumEq]
    exact hE.tsum_ofReal_ne_top
  have hrealBlockSummable :
      Summable (fun k : ℕ => (sparseScaleBlockError p k) ^ q) := by
    simpa [q] using summable_sparseScaleBlockError_q hp
  have hblockTermNonneg (k : ℕ) : 0 ≤ sparseScaleBlockError p k :=
    sparseScaleBlockError_nonneg hp k
  have hblockPowNonneg (k : ℕ) :
      0 ≤ (sparseScaleBlockError p k) ^ q :=
    Real.rpow_nonneg (hblockTermNonneg k) q
  have hblockSeriesTop :
      (∑' k : ℕ,
        (ENNReal.ofReal (sparseScaleBlockError p k)) ^ q) ≠ ∞ := by
    have hseriesEq :
        (∑' k : ℕ,
          (ENNReal.ofReal (sparseScaleBlockError p k)) ^ q) =
          ENNReal.ofReal
            (∑' k : ℕ, (sparseScaleBlockError p k) ^ q) := by
      calc
        _ = ∑' k : ℕ,
            ENNReal.ofReal ((sparseScaleBlockError p k) ^ q) := by
          apply tsum_congr
          intro k
          exact ENNReal.ofReal_rpow_of_nonneg
            (hblockTermNonneg k) hqnonneg
        _ = ENNReal.ofReal
            (∑' k : ℕ, (sparseScaleBlockError p k) ^ q) :=
          (ENNReal.ofReal_tsum_of_nonneg hblockPowNonneg
            hrealBlockSummable).symm
    rw [hseriesEq]
    exact ENNReal.ofReal_ne_top
  have hC0powTop : (ENNReal.ofReal C0) ^ q ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg hqnonneg ENNReal.ofReal_ne_top
  have hblockCoeffTop :
      ENNReal.ofReal C0 ^ q *
        ∑' k : ℕ,
          (ENNReal.ofReal (sparseScaleBlockError p k)) ^ q ≠ ∞ :=
    ENNReal.mul_ne_top hC0powTop hblockSeriesTop
  have hblockConstantTop : blockConstant ≠ ∞ := by
    dsimp [blockConstant]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ 1 / q)
      hblockCoeffTop
  have hlongConstantTop : longConstant ≠ ∞ := by
    dsimp [longConstant]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top (by norm_num) hopErrorTop
  have hCTop : C ≠ ∞ := by
    dsimp [C]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top (by norm_num) hlongConstantTop
    · exact ENNReal.mul_ne_top (by norm_num) hblockConstantTop
  refine ⟨C, hCTop, ?_⟩
  intro f
  let F : Scale → ℤ → ℂ := fun N => (Q N f : ℤ → ℂ)
  have hFmeas : ∀ N, AEMeasurable (F N) Measure.count := by
    intro N
    exact (memLp_count_of_memlp_seq_finite hp0 hpTop (Q N f)).aestronglyMeasurable.aemeasurable
  have hlong := eLpNorm_sparseLongVariation_le hp hr2 S hSmono Q P CP hP hE f
  have hblocks := eLpNorm_sparseBlockSquare_le hp Q C0 hC0 hinc f
  have hlongBound :
      eLpNorm (rVariationFun r (fun K : Scale => F (s (K.1 - 1))))
          (ENNReal.ofReal p) Measure.count ≤
        longConstant * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count := by
    simpa [F, S, longConstant, opErrorSum] using hlong
  have hblocksBound :
      eLpNorm (fun x : ℤ =>
        (∑' k : ℕ,
          (rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1))) x) ^
            (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) Measure.count ≤
        blockConstant * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count := by
    simpa [F, blockConstant, q] using hblocks
  have hlongShort := eLpNorm_longShort_reduction_direct Measure.count s
    hscale0 hscaleMono hscaleUnbounded F hp hr2 hFmeas
  calc
    eLpNorm (rVariationFun r F) (ENNReal.ofReal p) Measure.count ≤
        3 * eLpNorm
            (rVariationFun r (fun K : Scale => F (s (K.1 - 1))))
            (ENNReal.ofReal p) Measure.count +
          3 * eLpNorm (fun x : ℤ =>
            (∑' k : ℕ,
              (rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1))) x) ^
                (2 : ℝ)) ^ (1 / 2 : ℝ))
            (ENNReal.ofReal p) Measure.count := hlongShort
    _ ≤ 3 * (longConstant * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count) +
        3 * (blockConstant * eLpNorm (f : ℤ → ℂ)
          (ENNReal.ofReal p) Measure.count) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlongBound (by norm_num))
        (mul_le_mul_of_nonneg_left hblocksBound (by norm_num))
    _ = C * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      dsimp [C]
      calc
        3 * (longConstant * eLpNorm (f : ℤ → ℂ)
            (ENNReal.ofReal p) Measure.count) +
          3 * (blockConstant * eLpNorm (f : ℤ → ℂ)
            (ENNReal.ofReal p) Measure.count) =
          (3 * longConstant) * eLpNorm (f : ℤ → ℂ)
              (ENNReal.ofReal p) Measure.count +
            (3 * blockConstant) * eLpNorm (f : ℤ → ℂ)
              (ENNReal.ofReal p) Measure.count := by
                rw [← mul_assoc, ← mul_assoc]
        _ = (3 * longConstant + 3 * blockConstant) *
            eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
              rw [← add_mul]

end

end FractionalPrimes

end
