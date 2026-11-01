module

public import FractionalPrimes.Literature.Multiplier.FiniteSupportInclusion
public import FractionalPrimes.Literature.Multiplier.HighExponentFinite

/-!
# The finite-input multiplier map into sequence `lp`

The pointwise Fourier multiplier output belongs to `lp P` for every real
`p > 1`, with the proof split across the zero-size, lower-exponent, `p = 2`,
and upper-exponent cases. The resulting `lp` representative keeps the actual
pointwise multiplier output, so the finite-input map is canonical and linear.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open scoped ENNReal

noncomputable section

/-- The canonical embedding of a finitely supported sequence into `ℓ²` is
linear. -/
private def finiteSequenceL2Linear :
    (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun := finiteSequenceL2
  map_add' f g := by
    apply lp.ext
    funext k
    simp
  map_smul' c f := by
    apply lp.ext
    funext k
    simp

/-- The raw `ℓ²` multiplier output on finite inputs is additive. The proof
uses the already defined continuous `ℓ²` multiplier. -/
theorem TmL2_finiteSequenceL2_add
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D)
    (f g : ℤ →₀ ℂ) :
    TmL2 h (finiteSequenceL2 (f + g)) =
      TmL2 h (finiteSequenceL2 f) + TmL2 h (finiteSequenceL2 g) := by
  have hseq := finiteSequenceL2Linear.map_add f g
  change finiteSequenceL2 (f + g) =
    finiteSequenceL2 f + finiteSequenceL2 g at hseq
  calc
    TmL2 h (finiteSequenceL2 (f + g)) =
        TmL2CLM h (finiteSequenceL2 (f + g)) :=
      TmL2_eq_TmL2CLM h _
    _ = TmL2CLM h
        (finiteSequenceL2 f + finiteSequenceL2 g) := by rw [hseq]
    _ = TmL2CLM h (finiteSequenceL2 f) +
        TmL2CLM h (finiteSequenceL2 g) := map_add (TmL2CLM h) _ _
    _ = TmL2 h (finiteSequenceL2 f) + TmL2 h (finiteSequenceL2 g) := by
      rw [← TmL2_eq_TmL2CLM h (finiteSequenceL2 f),
        ← TmL2_eq_TmL2CLM h (finiteSequenceL2 g)]

/-- The raw `ℓ²` multiplier output on finite inputs commutes with complex
scalar multiplication. -/
theorem TmL2_finiteSequenceL2_smul
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D)
    (c : ℂ) (f : ℤ →₀ ℂ) :
    TmL2 h (finiteSequenceL2 (c • f)) =
      c • TmL2 h (finiteSequenceL2 f) := by
  have hseq := finiteSequenceL2Linear.map_smul c f
  change finiteSequenceL2 (c • f) = c • finiteSequenceL2 f at hseq
  calc
    TmL2 h (finiteSequenceL2 (c • f)) =
        TmL2CLM h (finiteSequenceL2 (c • f)) :=
      TmL2_eq_TmL2CLM h _
    _ = TmL2CLM h (c • finiteSequenceL2 f) := by rw [hseq]
    _ = c • TmL2CLM h (finiteSequenceL2 f) := map_smul (TmL2CLM h) c _
    _ = c • TmL2 h (finiteSequenceL2 f) := by
      rw [← TmL2_eq_TmL2CLM h (finiteSequenceL2 f)]

/-- For every `p > 1`, the pointwise multiplier output on a finite input
belongs to `ℓᵖ`. The proof uses the zero-symbol case, the checked lower and
upper exponent estimates, and the direct `p = 2` output. -/
theorem TmL2_finiteSequenceL2_memLp
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D)
    (hp1 : 1 < p) (f : ℤ →₀ ℂ) :
    Memℓp (fun k : ℤ => TmL2 h (finiteSequenceL2 f) k)
      (ENNReal.ofReal p) := by
  classical
  by_cases hDzero : D = 0
  · have hzero : TmL2 h (finiteSequenceL2 f) = 0 :=
      TmL2_eq_zero_of_D_eq_zero h hDzero (finiteSequenceL2 f)
    have hraw :
        (fun k : ℤ => TmL2 h (finiteSequenceL2 f) k) = fun _ => (0 : ℂ) := by
      funext k
      rw [hzero]
      rfl
    rw [hraw]
    exact zero_memℓp
  · have hDpos : 0 < D := lt_of_le_of_ne h.D_nonneg (Ne.symm hDzero)
    rcases lt_trichotomy p 2 with hp2 | hpEq | hp2
    · obtain ⟨F, hF, _hFnorm⟩ :=
        exists_TmL2_lp_of_finsupp h hDpos hp1 hp2 f
      rw [← hF]
      exact lp.memℓp F
    · have hP : ENNReal.ofReal p = (2 : ℝ≥0∞) := by
        rw [hpEq]
        norm_num
      rw [hP]
      exact lp.memℓp (TmL2 h (finiteSequenceL2 f))
    · obtain ⟨F, hF, _hFnorm⟩ :=
        exists_TmL2_lp_of_finsupp_high h hDpos hp2 f
      rw [← hF]
      exact lp.memℓp F

/-- The canonical finite-input multiplier map into `lp P`. Its underlying
function is exactly `TmL2 h (finiteSequenceL2 f)`, and the preceding
membership theorem supplies the subtype proof. -/
def finiteMultiplierLpMap
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p) :
    (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) where
  toFun f :=
    ⟨(fun k : ℤ => TmL2 h (finiteSequenceL2 f) k),
      TmL2_finiteSequenceL2_memLp h hp1 f⟩
  map_add' f g := by
    apply lp.ext
    funext k
    have hk := congrArg (fun u : lp (fun _ : ℤ => ℂ) 2 => u k)
      (TmL2_finiteSequenceL2_add h f g)
    simpa only [lp.coeFn_add] using hk
  map_smul' c f := by
    apply lp.ext
    funext k
    have hk := congrArg (fun u : lp (fun _ : ℤ => ℂ) 2 => u k)
      (TmL2_finiteSequenceL2_smul h c f)
    simpa only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply] using hk

/-- The canonical finite-input map preserves the actual Fourier multiplier
output at every integer. -/
@[simp] theorem finiteMultiplierLpMap_apply
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p)
    (f : ℤ →₀ ℂ) (k : ℤ) :
    finiteMultiplierLpMap (p := p) h hp1 f k =
      TmL2 h (finiteSequenceL2 f) k := rfl

end

end FractionalPrimes.Literature.Multiplier
