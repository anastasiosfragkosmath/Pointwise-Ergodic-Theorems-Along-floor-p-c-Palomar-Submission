module

public import FractionalPrimes.Literature.Multiplier.FiniteSupportDensity

/-!
# The dense inclusion of finitely supported sequences into sequence `lp`

The canonical map from finitely supported sequences to `lp P` has range
exactly the finite-support submodule. Combining this with the density result
for that submodule gives the dense linear map used by the multiplier
extension theorem.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open scoped ENNReal

variable {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- A finitely supported sequence belongs to `lp P`: its support is finite,
so it belongs to `ℓ⁰`, and `Memℓp.of_exponent_ge` includes it in every
exponent `P ≥ 1`. -/
theorem finsupp_memLp (f : ℤ →₀ ℂ) : Memℓp (f : ℤ → ℂ) P := by
  have hfinite : Set.Finite {k : ℤ | (f : ℤ → ℂ) k ≠ 0} := by
    apply f.support.finite_toSet.subset
    intro k hk
    change k ∈ f.support
    exact Finsupp.mem_support_iff.mpr hk
  exact (memℓp_zero hfinite).of_exponent_ge (zero_le_one.trans Fact.out)

/-- The canonical linear inclusion of finitely supported sequences into
sequence `lp P`. This is the dense map `e_P` for `LinearMap.extendOfNorm`. -/
def finiteSupportLpInclusion :
    (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) P where
  toFun f := ⟨(f : ℤ → ℂ), finsupp_memLp (P := P) f⟩
  map_add' f g := by
    apply lp.ext
    funext k
    simp only [lp.coeFn_add, Finsupp.coe_add,
      Pi.add_apply]
  map_smul' c f := by
    apply lp.ext
    funext k
    simp

/-- The inclusion preserves the original sequence at every coordinate. -/
@[simp] theorem finiteSupportLpInclusion_apply (f : ℤ →₀ ℂ) (k : ℤ) :
    finiteSupportLpInclusion (P := P) f k = f k := rfl

/-- The range of the Finsupp inclusion is precisely the finite-support
submodule. -/
theorem finiteSupportLpInclusion_range :
    LinearMap.range (finiteSupportLpInclusion (P := P)) =
      finiteSupportSequenceLpSubmodule (P := P) := by
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    change (Function.support (f : ℤ → ℂ)).Finite
    apply f.support.finite_toSet.subset
    intro k hk
    change k ∈ f.support
    exact Finsupp.mem_support_iff.mpr hk
  · intro x hx
    change (Function.support (x : ℤ → ℂ)).Finite at hx
    let f : ℤ →₀ ℂ := Finsupp.ofSupportFinite (x : ℤ → ℂ) hx
    refine ⟨f, ?_⟩
    apply lp.ext
    exact Finsupp.ofSupportFinite_coe

/-- Finitely supported sequences map densely into sequence `lp P` for every
finite exponent `P ≥ 1`. -/
theorem finiteSupportLpInclusion_denseRange (hPtop : P ≠ ∞) :
    DenseRange (finiteSupportLpInclusion (P := P)) := by
  rw [denseRange_iff_closure_range]
  change closure (LinearMap.range (finiteSupportLpInclusion (P := P)) :
    Set (lp (fun _ : ℤ => ℂ) P)) = Set.univ
  rw [finiteSupportLpInclusion_range (P := P)]
  exact (finiteSupportSequenceLpSubmodule_dense (P := P) hPtop).closure_eq

end FractionalPrimes.Literature.Multiplier
