module

public import FractionalPrimes.Literature.DirichletAdapter.MellinProfileFourierBound

/-! Compact support of the literal source profile used by residue quadrature. -/

@[expose] public section

open scoped ContDiff CompactlySupported

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The zero-extended source is supported in the scaled profile annulus. -/
theorem smoothDyadicQuadratureSource_support_subset
    (N t : ℝ) (p : ℝ × ℝ × ℝ) (hN : 0 < N) :
    Function.support (Twisted.smoothDyadicQuadratureSource N t p) ⊆
      Set.Icc (N / 2) (2 * N) := by
  intro x hx
  by_cases hpos : 0 < x
  · have hH : Twisted.smoothDyadicH p.1 p.2.1 p.2.2 (x / N) ≠ 0 := by
      intro hzero
      change Twisted.smoothDyadicQuadratureSource N t p x ≠ 0 at hx
      simp [Twisted.smoothDyadicQuadratureSource, hpos, hzero] at hx
    have hbox := Twisted.smoothDyadicH_support_subset p.1 p.2.1 p.2.2 hH
    constructor
    · have h := (le_div_iff₀ hN).mp hbox.1
      nlinarith
    · have h := (div_le_iff₀ hN).mp hbox.2
      nlinarith
  · change Twisted.smoothDyadicQuadratureSource N t p x ≠ 0 at hx
    simp [Twisted.smoothDyadicQuadratureSource, not_lt.mpr (le_of_not_gt hpos)] at hx

/-- Compact support of the literal source, without changing its definition. -/
theorem smoothDyadicQuadratureSource_hasCompactSupport
    (N t : ℝ) (p : ℝ × ℝ × ℝ) (hN : 0 < N) :
    HasCompactSupport (Twisted.smoothDyadicQuadratureSource N t p) := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (smoothDyadicQuadratureSource_support_subset N t p hN)

/-- The source as a compactly supported continuous map for the generic
residue quadrature theorem. -/
noncomputable def smoothDyadicQuadratureSourceCompact
    (N t : ℝ) (p : ℝ × ℝ × ℝ) (hN : 0 < N) : C_c(ℝ, ℂ) :=
  ⟨⟨Twisted.smoothDyadicQuadratureSource N t p,
      (Twisted.smoothDyadicQuadratureSource_contDiff p hN).continuous⟩,
    smoothDyadicQuadratureSource_hasCompactSupport N t p hN⟩

@[simp] theorem smoothDyadicQuadratureSourceCompact_apply
    (N t : ℝ) (p : ℝ × ℝ × ℝ) (hN : 0 < N) (x : ℝ) :
    smoothDyadicQuadratureSourceCompact N t p hN x =
      Twisted.smoothDyadicQuadratureSource N t p x := rfl

#print axioms smoothDyadicQuadratureSource_hasCompactSupport

end FractionalPrimes.Literature.DirichletAdapter

end
