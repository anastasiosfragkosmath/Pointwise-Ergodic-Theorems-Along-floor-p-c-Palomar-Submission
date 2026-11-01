module

public import FractionalPrimes.Literature.MSZ.VectorConvolutionUpper
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace FractionalPrimes.Literature.MSZ

noncomputable section

/-- On a finite spatial set, a mixed `ℓ^p(ℤ;ℓ²(E))` vector has a norming
dual vector supported on that same set. This is the finite-support norming
step in the approved `lm:duality` proof. -/
theorem exists_finite_mixed_norming_dual
    {ι : Type*} [Fintype ι]
    (s : Finset ℤ) (F : ℤ → PiLp 2 (fun _ : ι => ℂ))
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∃ G : ℤ → PiLp 2 (fun _ : ι => ℂ),
      (∀ x, x ∉ s → G x = 0) ∧
      (∑ x ∈ s, ‖G x‖₊ ^ q ≤ 1) ∧
      (∑ x ∈ s, inner ℂ (G x) (F x) =
        (((∑ x ∈ s, ‖F x‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℂ)) := by
  classical
  rcases (NNReal.isGreatest_Lp s (fun x : ℤ => ‖F x‖₊) hpq).1 with
    ⟨a, ha, hnorm⟩
  let G : ℤ → PiLp 2 (fun _ : ι => ℂ) := fun x =>
    if hx : x ∈ s then
      if hz : ‖F x‖ = 0 then 0 else ((a x : ℝ) / ‖F x‖) • F x
    else 0
  refine ⟨G, ?_, ?_, ?_⟩
  · intro x hx
    simp [G, hx]
  · calc
      ∑ x ∈ s, ‖G x‖₊ ^ q ≤ ∑ x ∈ s, a x ^ q := by
        apply Finset.sum_le_sum
        intro x hx
        have hnormG : ‖G x‖₊ ≤ a x := by
          by_cases hz : ‖F x‖ = 0
          · simp [G, hx, hz]
          · have hscale : 0 ≤ (a x : ℝ) / ‖F x‖ :=
              div_nonneg NNReal.zero_le_coe (norm_nonneg _)
            have hnormEq : ‖G x‖₊ = a x := by
              apply NNReal.coe_injective
              change ‖G x‖ = (a x : ℝ)
              dsimp [G]
              simp only [if_pos hx, if_neg hz]
              rw [norm_smul, Real.norm_of_nonneg hscale]
              exact div_mul_cancel₀ _ hz
            rw [hnormEq]
        exact NNReal.rpow_le_rpow hnormG hpq.symm.nonneg
      _ ≤ 1 := ha
  · have hpair (x : ℤ) (hx : x ∈ s) :
        inner ℂ (G x) (F x) = ((‖F x‖₊ * a x : ℝ≥0) : ℂ) := by
      by_cases hz : ‖F x‖ = 0
      · have hFx : F x = 0 := norm_eq_zero.mp hz
        simp [G, hx, hz, hFx]
      · dsimp [G]
        simp only [if_pos hx, if_neg hz]
        simp only [← algebraMap_smul ℂ ((a x : ℝ) / ‖F x‖) (F x),
          RCLike.algebraMap_eq_ofReal, inner_smul_real_left,
          inner_self_eq_norm_sq_to_K, Algebra.smul_def]
        have hreal : (a x : ℝ) / ‖F x‖ * ‖F x‖ ^ 2 =
            ‖F x‖ * (a x : ℝ) := by
          field_simp [hz]
        norm_cast
        exact congrArg (fun z : ℝ => (z : ℂ)) hreal
    calc
      (∑ x ∈ s, inner ℂ (G x) (F x)) =
          ∑ x ∈ s, (((‖F x‖₊ * a x : ℝ≥0) : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hpair x hx
      _ = (((∑ x ∈ s, ‖F x‖₊ * a x : ℝ≥0) : ℝ) : ℂ) := by
            norm_cast
      _ = (((∑ x ∈ s, ‖F x‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℂ) := by
            change ((((fun g : ℤ → ℝ≥0 =>
              ∑ i ∈ s, ‖F i‖₊ * g i) a : ℝ≥0) : ℝ) : ℂ) =
              (((∑ x ∈ s, ‖F x‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℂ)
            exact congrArg (fun z : ℝ≥0 => (z : ℂ)) hnorm

/-- The `ℓ²(E)` norm on one fiber, written in the coordinate form used in
the approved blueprint. -/
theorem mszVectorFiberNorm_eq_l2
    {ι : Type*} [Fintype ι] (v : PiLp 2 (fun _ : ι => ℂ)) :
    ‖v‖₊ = (∑ i : ι, ‖v i‖₊ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  simpa using
    (PiLp.nnnorm_eq_sum (p := (2 : ℝ≥0∞)) (by norm_num) v)

/-- The inner-product pairing used below is the coordinate pairing
`∑ᵢ Fᵢ(x) * conj (Gᵢ(x))` from the blueprint. -/
theorem mszVectorFinitePairing_eq_coordinates
    {ι : Type*} [Fintype ι]
    (s : Finset ℤ) (G F : ℤ → PiLp 2 (fun _ : ι => ℂ)) :
    (∑ x ∈ s, inner ℂ (G x) (F x)) =
      ∑ x ∈ s, ∑ i : ι, F x i * starRingEnd ℂ (G x i) := by
  apply Finset.sum_congr rfl
  intro x hx
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-- The `p`-power of the fiber norm, as an extended nonnegative real. -/
noncomputable def mszVectorLpTerm
    {ι : Type*} [Fintype ι] (p : ℝ)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) (x : ℤ) : ℝ≥0∞ :=
  ENNReal.ofNNReal (‖F x‖₊ ^ p)

/-- The extended mixed `ℓ^p(ℤ;ℓ²(E))` norm from `lm:spaces`. The ENNReal
sum preserves the value `+∞`. By `mszVectorFiberNorm_eq_l2`, its summands
are exactly the coordinate `ℓ²(E)` norms appearing in the blueprint. -/
noncomputable def mszVectorLpNorm
    {ι : Type*} [Fintype ι] (p : ℝ)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) : ℝ≥0∞ :=
  (∑' x : ℤ, mszVectorLpTerm p F x) ^ (1 / p)

/-- The finite-spatial-set mixed norm used in the exhaustion proof. -/
noncomputable def mszVectorFiniteLpNorm
    {ι : Type*} [Fintype ι] (p : ℝ) (s : Finset ℤ)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) : ℝ≥0∞ :=
  (∑ x ∈ s, mszVectorLpTerm p F x) ^ (1 / p)

theorem mszVectorFiniteLpNorm_eq_nnreal
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p)
    (s : Finset ℤ) (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) :
    mszVectorFiniteLpNorm p s F =
      ENNReal.ofNNReal ((∑ x ∈ s, ‖F x‖₊ ^ p) ^ (1 / p)) := by
  change (∑ x ∈ s, ENNReal.ofNNReal (‖F x‖₊ ^ p)) ^ (1 / p) =
    ENNReal.ofNNReal ((∑ x ∈ s, ‖F x‖₊ ^ p) ^ (1 / p))
  rw [← ENNReal.ofNNReal_finsetSum]
  exact (ENNReal.coe_rpow_of_nonneg _ (one_div_nonneg.mpr hp.le)).symm

/-- Finite truncations exhaust the extended mixed norm, including when the
norm is infinite. -/
theorem mszVectorLpNorm_eq_iSup_finite
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) :
    mszVectorLpNorm p F = ⨆ s : Finset ℤ, mszVectorFiniteLpNorm p s F := by
  rw [mszVectorLpNorm, ENNReal.tsum_eq_iSup_sum]
  have hroot : 0 < 1 / p := one_div_pos.mpr hp
  let iso : ℝ≥0∞ ≃o ℝ≥0∞ :=
    (ENNReal.strictMono_rpow_of_pos hroot).orderIsoOfSurjective _
      (ENNReal.rpow_left_bijective hroot.ne').2
  change iso (⨆ s : Finset ℤ, ∑ x ∈ s, mszVectorLpTerm p F x) =
    ⨆ s : Finset ℤ, iso (∑ x ∈ s, mszVectorLpTerm p F x)
  exact iso.map_iSup fun s => ∑ x ∈ s, mszVectorLpTerm p F x

theorem mszVectorLpNorm_eq_finiteSupport
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p)
    (s : Finset ℤ) (F : ℤ → PiLp 2 (fun _ : ι => ℂ))
    (hF : ∀ x, x ∉ s → F x = 0) :
    mszVectorLpNorm p F = mszVectorFiniteLpNorm p s F := by
  rw [mszVectorLpNorm, tsum_eq_sum (s := s)]
  · rfl
  · intro x hx
    simp [mszVectorLpTerm, hF x hx, NNReal.zero_rpow (ne_of_gt hp)]

theorem mszVectorFiniteLpNorm_le
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p)
    (s : Finset ℤ) (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) :
    mszVectorFiniteLpNorm p s F ≤ mszVectorLpNorm p F := by
  calc
    mszVectorFiniteLpNorm p s F ≤
        (∑' x : ℤ, mszVectorLpTerm p F x) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s)
            (one_div_nonneg.mpr hp.le)
    _ = mszVectorLpNorm p F := rfl

/-- The mixed-norm dual supremum, indexed by a finite support set `s` and
all witnesses vanishing outside `s`. This is an exact encoding of the
finite-spatial-support supremum in `lm:duality`. -/
noncomputable def mszVectorDualitySup
    {ι : Type*} [Fintype ι] (q : ℝ)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) : ℝ≥0∞ := by
  classical
  exact ⨆ s : Finset ℤ, ⨆ G : ℤ → PiLp 2 (fun _ : ι => ℂ),
    if (∀ x, x ∉ s → G x = 0) ∧ mszVectorLpNorm q G ≤ 1 then
      ENNReal.ofReal ‖∑ x ∈ s, inner ℂ (G x) (F x)‖
    else 0

theorem mszVectorSupportFinite_iff
    {ι : Type*} [Fintype ι] (G : ℤ → PiLp 2 (fun _ : ι => ℂ)) :
    (Function.support G).Finite ↔
      ∃ s : Finset ℤ, ∀ x, x ∉ s → G x = 0 := by
  constructor
  · intro hG
    exact ⟨hG.toFinset, fun x hx => by
      by_contra hGx
      exact hx (hG.mem_toFinset.mpr (Function.mem_support.mpr hGx))⟩
  · rintro ⟨s, hs⟩
    refine s.finite_toSet.subset ?_
    intro x hx
    by_contra hxs
    exact (Function.mem_support.mp hx) (hs x hxs)

/-- The dual supremum stated directly over all finitely-supported `G`. Its
pairing is summed over the exact support of `G`; the subtype witness carries
the finiteness proof and the unit-ball condition. -/
noncomputable def mszVectorFiniteSupportDualSup
    {ι : Type*} [Fintype ι] (q : ℝ)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) : ℝ≥0∞ :=
  ⨆ G : {G : ℤ → PiLp 2 (fun _ : ι => ℂ) //
      (Function.support G).Finite ∧ mszVectorLpNorm q G ≤ 1},
    ENNReal.ofReal ‖∑ x ∈ G.2.1.toFinset, inner ℂ (G.1 x) (F x)‖

/-- Replacing the support-set encoding of the dual unit ball by the subtype
of all finitely-supported test vectors leaves the supremum unchanged. -/
theorem mszVectorDualitySup_eq_finiteSupportSup
    {ι : Type*} [Fintype ι] (q : ℝ)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) :
    mszVectorDualitySup q F = mszVectorFiniteSupportDualSup q F := by
  classical
  apply le_antisymm
  · unfold mszVectorDualitySup
    apply iSup_le
    intro s
    apply iSup_le
    intro G
    by_cases hG :
        (∀ x, x ∉ s → G x = 0) ∧ mszVectorLpNorm q G ≤ 1
    · rw [if_pos hG]
      have hfinite : (Function.support G).Finite := by
        refine s.finite_toSet.subset ?_
        intro x hx
        by_contra hxs
        exact (Function.mem_support.mp hx) (hG.1 x hxs)
      have hsubset : hfinite.toFinset ⊆ s := by
        intro x hx
        by_contra hxs
        exact (Function.mem_support.mp (hfinite.mem_toFinset.mp hx))
          (hG.1 x hxs)
      have hpair :
          (∑ x ∈ s, inner ℂ (G x) (F x)) =
            ∑ x ∈ hfinite.toFinset, inner ℂ (G x) (F x) := by
        symm
        apply Finset.sum_subset hsubset
        intro x hx hxnot
        have hxnotSupport : x ∉ Function.support G := by
          intro hxSupport
          exact hxnot (hfinite.mem_toFinset.mpr hxSupport)
        have hGx : G x = 0 := by
          by_contra hGx
          exact hxnotSupport (Function.mem_support.mpr hGx)
        simp [hGx]
      let G' : {G : ℤ → PiLp 2 (fun _ : ι => ℂ) //
          (Function.support G).Finite ∧ mszVectorLpNorm q G ≤ 1} :=
        ⟨G, hfinite, hG.2⟩
      calc
        ENNReal.ofReal ‖∑ x ∈ s, inner ℂ (G x) (F x)‖ =
            ENNReal.ofReal ‖∑ x ∈ hfinite.toFinset,
              inner ℂ (G x) (F x)‖ := by rw [hpair]
        _ ≤ mszVectorFiniteSupportDualSup q F :=
          le_iSup_of_le G' le_rfl
    · simp [hG]
  · unfold mszVectorFiniteSupportDualSup
    apply iSup_le
    intro G'
    obtain ⟨hfinite, hnorm⟩ := G'.2
    let s : Finset ℤ := hfinite.toFinset
    have hsupport : ∀ x, x ∉ s → G'.1 x = 0 := by
      intro x hx
      by_contra hGx
      exact hx (hfinite.mem_toFinset.mpr (Function.mem_support.mpr hGx))
    unfold mszVectorDualitySup
    exact le_iSup_of_le s <| le_iSup_of_le G'.1 <| by
      rw [if_pos ⟨hsupport, hnorm⟩]

private theorem mszVectorFinitePairing_le
    {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (hp : 0 < p) (hq : 0 < q)
    (s : Finset ℤ) (G F : ℤ → PiLp 2 (fun _ : ι => ℂ))
    (hG : mszVectorLpNorm q G ≤ 1) :
    ENNReal.ofReal ‖∑ x ∈ s, inner ℂ (G x) (F x)‖ ≤
      mszVectorLpNorm p F := by
  have hpairNN :
      ‖∑ x ∈ s, inner ℂ (G x) (F x)‖₊ ≤
        ∑ x ∈ s, ‖G x‖₊ * ‖F x‖₊ := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm]
    calc
      ‖∑ x ∈ s, inner ℂ (G x) (F x)‖ ≤
          ∑ x ∈ s, ‖inner ℂ (G x) (F x)‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ s, ‖G x‖ * ‖F x‖ := by
        apply Finset.sum_le_sum
        intro x hx
        exact norm_inner_le_norm _ _
  have hholder :=
    NNReal.inner_le_Lp_mul_Lq s (fun x : ℤ => ‖G x‖₊)
      (fun x : ℤ => ‖F x‖₊) hpq.symm
  have hholderENN :
      ENNReal.ofNNReal (∑ x ∈ s, ‖G x‖₊ * ‖F x‖₊) ≤
        mszVectorFiniteLpNorm q s G * mszVectorFiniteLpNorm p s F := by
    rw [mszVectorFiniteLpNorm_eq_nnreal hq,
      mszVectorFiniteLpNorm_eq_nnreal hp]
    calc
      ENNReal.ofNNReal (∑ x ∈ s, ‖G x‖₊ * ‖F x‖₊) ≤
          ENNReal.ofNNReal
            ((∑ x ∈ s, ‖G x‖₊ ^ q) ^ (1 / q) *
              (∑ x ∈ s, ‖F x‖₊ ^ p) ^ (1 / p)) :=
        ENNReal.coe_le_coe.mpr hholder
      _ = ENNReal.ofNNReal ((∑ x ∈ s, ‖G x‖₊ ^ q) ^ (1 / q)) *
            ENNReal.ofNNReal ((∑ x ∈ s, ‖F x‖₊ ^ p) ^ (1 / p)) := by simp
  have hqfin := mszVectorFiniteLpNorm_le hq s G
  have hpfin := mszVectorFiniteLpNorm_le hp s F
  rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
  calc
    ENNReal.ofNNReal ‖∑ x ∈ s, inner ℂ (G x) (F x)‖₊ ≤
        ENNReal.ofNNReal (∑ x ∈ s, ‖G x‖₊ * ‖F x‖₊) :=
      ENNReal.coe_le_coe.mpr hpairNN
    _ ≤ mszVectorFiniteLpNorm q s G * mszVectorFiniteLpNorm p s F := hholderENN
    _ ≤ mszVectorLpNorm q G * mszVectorLpNorm p F := by
      exact mul_le_mul hqfin hpfin (by positivity) (by positivity)
    _ ≤ 1 * mszVectorLpNorm p F := by gcongr
    _ = mszVectorLpNorm p F := one_mul _

/-- The exact mixed `ℓ^p(ℤ;ℓ²(E))` duality identity from approved
blueprint `lm:duality`. The sum-defined norm is extended-valued, and the
finite-support supremum is encoded by pairs `(s,G)` with `G` zero off `s`. -/
theorem mszVectorNormDuality
    {ι : Type*} [Fintype ι] (p : ℝ) (hp : 1 < p)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) :
    mszVectorLpNorm p F = mszVectorDualitySup (p / (p - 1)) F := by
  classical
  let q : ℝ := p / (p - 1)
  have hp_pos : 0 < p := by linarith
  have hpq : p.HolderConjugate q := by
    simpa [q, Real.conjExponent] using
      (Real.HolderConjugate.conjExponent hp)
  have hq_pos : 0 < q := hpq.symm.pos
  have hlower : mszVectorLpNorm p F ≤ mszVectorDualitySup q F := by
    rw [mszVectorLpNorm_eq_iSup_finite hp_pos F]
    apply iSup_le
    intro s
    rcases exists_finite_mixed_norming_dual s F hpq with
      ⟨G, hGsupport, hGmoment, hpair⟩
    have hGnorm : mszVectorLpNorm q G ≤ 1 := by
      rw [mszVectorLpNorm_eq_finiteSupport hq_pos s G hGsupport,
        mszVectorFiniteLpNorm_eq_nnreal hq_pos s G]
      have hroot : (∑ x ∈ s, ‖G x‖₊ ^ q) ^ (1 / q) ≤ 1 := by
        calc
          (∑ x ∈ s, ‖G x‖₊ ^ q) ^ (1 / q) ≤ 1 ^ (1 / q) :=
            NNReal.rpow_le_rpow hGmoment (one_div_nonneg.mpr hq_pos.le)
          _ = 1 := by simp
      exact ENNReal.coe_le_coe.mpr hroot
    have hpairValue :
        ENNReal.ofReal ‖∑ x ∈ s, inner ℂ (G x) (F x)‖ =
          mszVectorFiniteLpNorm p s F := by
      rw [hpair, mszVectorFiniteLpNorm_eq_nnreal hp_pos s F]
      rw [Complex.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact ENNReal.ofReal_coe_nnreal
    unfold mszVectorDualitySup
    exact le_iSup_of_le s <| le_iSup_of_le G <| by
      rw [if_pos ⟨hGsupport, hGnorm⟩]
      exact le_of_eq hpairValue.symm
  have hupper : mszVectorDualitySup q F ≤ mszVectorLpNorm p F := by
    unfold mszVectorDualitySup
    apply iSup_le
    intro s
    apply iSup_le
    intro G
    by_cases hG : (∀ x, x ∉ s → G x = 0) ∧ mszVectorLpNorm q G ≤ 1
    · rw [if_pos hG]
      exact mszVectorFinitePairing_le hpq hp_pos hq_pos s G F hG.2
    · simp [hG]
  exact le_antisymm hlower hupper

/-- The blueprint's presentation of `lm:duality`, with the supremum taken
directly over finite-spatial-support test vectors. -/
theorem mszVectorNormDuality_paper
    {ι : Type*} [Fintype ι] (p : ℝ) (hp : 1 < p)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) :
    mszVectorLpNorm p F =
      mszVectorFiniteSupportDualSup (p / (p - 1)) F := by
  rw [← mszVectorDualitySup_eq_finiteSupportSup]
  exact mszVectorNormDuality p hp F

end

end FractionalPrimes.Literature.MSZ

end
