module

public import FractionalPrimes.Literature.Multiplier.FiniteMultiplierExtension

/-!
# Agreement with the `ℓ²` multiplier on the intersection

The bounded `ℓᵖ` extension agrees with the Fourier-defined `ℓ²` multiplier
whenever the same sequence belongs to both spaces. The proof uses symmetric
finite truncations in both norms and coordinatewise uniqueness of limits.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open Filter
open scoped ENNReal Topology

noncomputable section

/-- On a sequence that belongs to both `ℓᵖ` and `ℓ²`, the bounded `ℓᵖ`
extension agrees pointwise with the Fourier-defined `ℓ²` multiplier. -/
theorem finiteMultiplierLpExtension_eq_TmL2_of_lp2
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))
    (u : lp (fun _ : ℤ => ℂ) 2)
    (hFU : (F : ℤ → ℂ) = (u : ℤ → ℂ)) :
    (finiteMultiplierLpExtension h hp1 F : ℤ → ℂ) =
      (TmL2 h u : ℤ → ℂ) := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let S := finiteMultiplierLpExtension h hp1
  let truncP (N : ℕ) : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
    finiteSupportLpTruncation (P := ENNReal.ofReal p)
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) F
  let trunc2 (N : ℕ) : lp (fun _ : ℤ => ℂ) 2 :=
    finiteSupportLpTruncation (P := (2 : ℝ≥0∞))
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) u
  have htruncP_mem (N : ℕ) :
      truncP N ∈ finiteSupportSequenceLpSubmodule
        (P := ENNReal.ofReal p) := by
    exact finiteSupportLpTruncation_mem (P := ENNReal.ofReal p)
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) F
  have htruncP_support (N : ℕ) :
      (Function.support (truncP N : ℤ → ℂ)).Finite := htruncP_mem N
  let fN (N : ℕ) : ℤ →₀ ℂ :=
    Finsupp.ofSupportFinite (truncP N : ℤ → ℂ) (htruncP_support N)
  have htruncP_eq_inclusion (N : ℕ) :
      finiteSupportLpInclusion (P := ENNReal.ofReal p) (fN N) = truncP N := by
    apply lp.ext
    exact Finsupp.ofSupportFinite_coe
  have hfN_apply (N : ℕ) (k : ℤ) : fN N k = truncP N k := by
    have hk := congrArg (fun z : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) => z k)
      (htruncP_eq_inclusion N)
    simpa only [finiteSupportLpInclusion_apply] using hk
  have hfiniteInput_eq_trunc2 (N : ℕ) :
      finiteSequenceL2 (fN N) = trunc2 N := by
    apply lp.ext
    funext k
    rw [finiteSequenceL2_apply, hfN_apply,
      finiteSupportLpTruncation_apply, finiteSupportLpTruncation_apply]
    by_cases hk : k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
    · simp [hk, congrFun hFU k]
    · simp [hk]
  have htruncP_tendsto : Tendsto truncP atTop (𝓝 F) := by
    exact finiteSupportLpTruncation_Icc_tendsto
      (P := ENNReal.ofReal p) ENNReal.ofReal_ne_top F
  have htrunc2_tendsto : Tendsto trunc2 atTop (𝓝 u) := by
    exact finiteSupportLpTruncation_Icc_tendsto
      (P := (2 : ℝ≥0∞)) (by norm_num) u
  have hS_tendsto : Tendsto (fun N => S (truncP N)) atTop (𝓝 (S F)) :=
    (S.continuous.tendsto F).comp htruncP_tendsto
  have hTclm_tendsto :
      Tendsto (fun N => TmL2CLM h (trunc2 N)) atTop
        (𝓝 (TmL2CLM h u)) :=
    (TmL2CLM h).continuous.tendsto u |>.comp htrunc2_tendsto
  have hT_tendsto : Tendsto (fun N => TmL2 h (trunc2 N)) atTop
      (𝓝 (TmL2 h u)) := by
    have hseq : (fun N => TmL2 h (trunc2 N)) =
        (fun N => TmL2CLM h (trunc2 N)) := by
      funext N
      exact TmL2_eq_TmL2CLM h (trunc2 N)
    rw [hseq, TmL2_eq_TmL2CLM h u]
    exact hTclm_tendsto
  have hS_fun_tendsto :
      Tendsto (fun N => (S (truncP N) : ℤ → ℂ)) atTop
        (𝓝 (S F : ℤ → ℂ)) :=
    (lp.uniformContinuous_coe (p := ENNReal.ofReal p)).continuous
      |>.continuousAt.tendsto.comp hS_tendsto
  have hT_fun_tendsto :
      Tendsto (fun N => (TmL2 h (trunc2 N) : ℤ → ℂ)) atTop
        (𝓝 (TmL2 h u : ℤ → ℂ)) :=
    (lp.uniformContinuous_coe (p := (2 : ℝ≥0∞))).continuous
      |>.continuousAt.tendsto.comp hT_tendsto
  have hS_approx (N : ℕ) : S (truncP N) =
      finiteMultiplierLpMap (p := p) h hp1 (fN N) := by
    rw [← htruncP_eq_inclusion N]
    exact finiteMultiplierLpExtension_apply_finite h hp1 (fN N)
  have hT_approx (N : ℕ) :
      TmL2 h (finiteSequenceL2 (fN N)) = TmL2 h (trunc2 N) :=
    congrArg (TmL2 h) (hfiniteInput_eq_trunc2 N)
  have happrox (N : ℕ) (k : ℤ) :
      (S (truncP N) : ℤ → ℂ) k = (TmL2 h (trunc2 N) : ℤ → ℂ) k := by
    calc
      (S (truncP N) : ℤ → ℂ) k =
          finiteMultiplierLpMap (p := p) h hp1 (fN N) k :=
        congrArg (fun z : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) => z k)
          (hS_approx N)
      _ = TmL2 h (finiteSequenceL2 (fN N)) k := by simp
      _ = TmL2 h (trunc2 N) k :=
        congrArg (fun z : lp (fun _ : ℤ => ℂ) 2 => z k) (hT_approx N)
  have hS_coord (k : ℤ) :
      Tendsto (fun N => (S (truncP N) : ℤ → ℂ) k) atTop
        (𝓝 ((S F : ℤ → ℂ) k)) :=
    (continuous_apply k).continuousAt.tendsto.comp hS_fun_tendsto
  have hT_coord (k : ℤ) :
      Tendsto (fun N => (TmL2 h (trunc2 N) : ℤ → ℂ) k) atTop
        (𝓝 ((TmL2 h u : ℤ → ℂ) k)) :=
    (continuous_apply k).continuousAt.tendsto.comp hT_fun_tendsto
  funext k
  exact tendsto_nhds_unique (hS_coord k)
    ((Filter.tendsto_congr' (Filter.Eventually.of_forall (fun N => happrox N k))).2
      (hT_coord k))

end

end FractionalPrimes.Literature.Multiplier
