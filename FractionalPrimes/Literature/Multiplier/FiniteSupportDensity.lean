module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.DenseEmbedding

/-!
# Finite-support subspace density in sequence `lp`

For every finite exponent `P ≥ 1`, finitely supported sequences form a dense
linear subspace of sequence `lp P`. The symmetric finite truncations are the
canonical finite sums of coordinate vectors supplied by `lp.hasSum_single`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open Filter
open scoped Topology ENNReal

variable {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- The linear subspace of sequence `lp P` consisting of finitely supported
sequences. -/
def finiteSupportSequenceLpSubmodule :
    Submodule ℂ (lp (fun _ : ℤ => ℂ) P) where
  carrier := {f | (Function.support (f : ℤ → ℂ)).Finite}
  zero_mem' := by
    change (Function.support (fun _ : ℤ => (0 : ℂ))).Finite
    simp
  add_mem' := by
    intro f g hf hg
    apply (hf.union hg).subset
    intro k hk
    by_contra hnot
    have hfk : f k = 0 := by
      have : k ∉ Function.support (f : ℤ → ℂ) := fun h => hnot (Or.inl h)
      simpa only [Function.mem_support, not_not] using this
    have hgk : g k = 0 := by
      have : k ∉ Function.support (g : ℤ → ℂ) := fun h => hnot (Or.inr h)
      simpa only [Function.mem_support, not_not] using this
    have hzero : (f + g) k = 0 := by simp [lp.coeFn_add, hfk, hgk]
    exact (Function.mem_support.mp hk) hzero
  smul_mem' := by
    intro c f hf
    apply hf.subset
    intro k hk
    by_contra hnot
    have hfk : f k = 0 := by
      have : k ∉ Function.support (f : ℤ → ℂ) := hnot
      simpa only [Function.mem_support, not_not] using this
    have hzero : (c • f) k = 0 := by simp [lp.coeFn_smul, hfk]
    exact (Function.mem_support.mp hk) hzero

/-- The canonical finite truncation of an `lp` sequence, expressed as the
finite sum of its coordinate vectors. -/
noncomputable def finiteSupportLpTruncation (s : Finset ℤ)
    (f : lp (fun _ : ℤ => ℂ) P) : lp (fun _ : ℤ => ℂ) P :=
  ∑ k ∈ s, lp.single P k (f k)

/-- At each coordinate, the finite `lp` truncation is the expected restriction
to its defining finite set. -/
theorem finiteSupportLpTruncation_apply (s : Finset ℤ)
    (f : lp (fun _ : ℤ => ℂ) P) (k : ℤ) :
    finiteSupportLpTruncation (P := P) s f k = if k ∈ s then f k else 0 := by
  simp only [finiteSupportLpTruncation, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_single, Finset.sum_pi_single]

/-- The support of a finite `lp` truncation is contained in the truncation
set. -/
theorem finiteSupportLpTruncation_support_subset (s : Finset ℤ)
    (f : lp (fun _ : ℤ => ℂ) P) :
    Function.support (finiteSupportLpTruncation (P := P) s f : ℤ → ℂ) ⊆
      (s : Set ℤ) := by
  intro k hk
  by_contra hks
  have hks' : k ∉ s := by simpa using hks
  have hzero : finiteSupportLpTruncation (P := P) s f k = 0 := by
    simp [finiteSupportLpTruncation_apply, hks']
  exact (Function.mem_support.mp hk) hzero

/-- Every canonical finite truncation belongs to the finite-support
submodule. -/
theorem finiteSupportLpTruncation_mem (s : Finset ℤ)
    (f : lp (fun _ : ℤ => ℂ) P) :
    finiteSupportLpTruncation (P := P) s f ∈ finiteSupportSequenceLpSubmodule := by
  change (Function.support
    (finiteSupportLpTruncation (P := P) s f : ℤ → ℂ)).Finite
  exact s.finite_toSet.subset (finiteSupportLpTruncation_support_subset (P := P) s f)

/-- Symmetric finite truncations converge to every element of finite-exponent
sequence `lp`. -/
theorem finiteSupportLpTruncation_Icc_tendsto (hPtop : P ≠ ∞)
    (f : lp (fun _ : ℤ => ℂ) P) :
    Tendsto
      (fun N : ℕ => finiteSupportLpTruncation (P := P)
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) f)
      atTop (𝓝 f) := by
  classical
  have hsum : HasSum (fun k : ℤ => lp.single P k (f k)) f :=
    lp.hasSum_single hPtop f
  have hmono : Monotone
      (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro n k hnk
    apply Finset.Icc_subset_Icc
    · exact neg_le_neg (Int.ofNat_le.mpr hnk)
    · exact Int.ofNat_le.mpr hnk
  have hcofinal : ∀ z : ℤ, ∃ N : ℕ,
      z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro z
    refine ⟨z.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    have habs := abs_le.mp (le_rfl : |z| ≤ |z|)
    rw [Int.abs_eq_natAbs] at habs
    exact habs
  have hfilter : Tendsto
      (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop :=
    hmono.tendsto_atTop_finset hcofinal
  have hsumFilter : Tendsto
      (fun s : Finset ℤ => ∑ k ∈ s, lp.single P k (f k))
      atTop (𝓝 f) := hsum
  have hcomp := hsumFilter.comp hfilter
  apply hcomp.congr'
  filter_upwards with N
  rfl

/-- Finitely supported sequences are dense in sequence `lp P` for every
finite exponent `P ≥ 1`. -/
theorem finiteSupportSequenceLpSubmodule_dense (hPtop : P ≠ ∞) :
    Dense (finiteSupportSequenceLpSubmodule (P := P) :
      Set (lp (fun _ : ℤ => ℂ) P)) := by
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  have htend := finiteSupportLpTruncation_Icc_tendsto (P := P) hPtop f
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist (finiteSupportLpTruncation (P := P)
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) f) f < ε :=
    (Metric.tendsto_nhds.mp htend) ε hε
  obtain ⟨N, hN⟩ := hnear.exists
  refine ⟨finiteSupportLpTruncation (P := P)
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) f,
    finiteSupportLpTruncation_mem (P := P)
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) f, ?_⟩
  simpa only [dist_comm] using hN

/-- The subtype inclusion of the finite-support submodule into sequence
`lp P` has dense range. This is the dense linear map used by
`LinearMap.extendOfNorm`. -/
theorem finiteSupportSequenceLpSubmodule_subtype_denseRange (hPtop : P ≠ ∞) :
    DenseRange (finiteSupportSequenceLpSubmodule (P := P)).subtype := by
  exact (finiteSupportSequenceLpSubmodule_dense (P := P) hPtop).denseRange_val

end FractionalPrimes.Literature.Multiplier
