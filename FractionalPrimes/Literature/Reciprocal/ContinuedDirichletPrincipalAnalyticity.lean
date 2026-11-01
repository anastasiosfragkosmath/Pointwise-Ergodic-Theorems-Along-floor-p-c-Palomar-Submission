module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletData
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

open Complex Set Filter
open scoped Topology

namespace FractionalPrimes.Literature.Reciprocal

/-- Since the blueprint's definition of `I` carries its half-plane proof as an
argument, this total function is the exact principal continuation on its open
punctured domain and is zero outside that domain. -/
noncomputable def continuedDirichletZTotal (s : ℂ) : ℂ :=
  if hs : 0 < s.re then
    if hs1 : s ≠ 1 then continuedDirichletZ s hs hs1 else 0
  else 0

/-- The regularized `H₀` totalization agrees exactly with the blueprint on
the whole open right half-plane, including at `s = 1`. -/
noncomputable def continuedDirichletH0Total (s : ℂ) : ℂ :=
  if hs : 0 < s.re then continuedDirichletH0 s hs else 0

/-- Totalization of the exact principal branch, retaining the blueprint's
pole exclusion. -/
noncomputable def principalContinuedDirichletLTotal {q : ℕ} [NeZero q]
    (s : ℂ) : ℂ :=
  if hs : 0 < s.re then
    if hs1 : s ≠ 1 then principalContinuedDirichletL (q := q) s hs hs1 else 0
  else 0

theorem continuedDirichletZTotal_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    continuedDirichletZTotal s = continuedDirichletZ s hs hs1 := by
  simp [continuedDirichletZTotal, hs, hs1]

theorem continuedDirichletH0Total_eq {s : ℂ} (hs : 0 < s.re) :
    continuedDirichletH0Total s = continuedDirichletH0 s hs := by
  simp [continuedDirichletH0Total, hs]

theorem principalContinuedDirichletLTotal_eq {q : ℕ} [NeZero q] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    principalContinuedDirichletLTotal (q := q) s = principalContinuedDirichletL (q := q) s hs hs1 := by
  simp [principalContinuedDirichletLTotal, hs, hs1]

theorem analyticAt_zetaFloorCorrectionIntegral {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ zetaFloorCorrectionIntegral s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact differentiableAt_zetaFloorCorrectionIntegral hz

private theorem analyticAt_continuedDirichletZ_formula {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => z / (z - 1) - z * zetaFloorCorrectionIntegral z) s := by
  have hsminus : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hrat : AnalyticAt ℂ (fun z : ℂ => z / (z - 1)) s :=
    analyticAt_id.div (analyticAt_id.sub analyticAt_const) hsminus
  have hI := analyticAt_zetaFloorCorrectionIntegral hs
  exact hrat.sub (analyticAt_id.mul hI)

/-- The principal zeta continuation is analytic at each point of the exact
punctured half-plane `Re(s)>0`, `s ≠ 1`. -/
theorem analyticAt_continuedDirichletZTotal {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ continuedDirichletZTotal s := by
  let Ω : Set ℂ := {z | 0 < z.re ∧ z ≠ 1}
  have hΩopen : IsOpen Ω := by
    dsimp [Ω]
    exact (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  have hΩs : s ∈ Ω := ⟨hs, hs1⟩
  have heq : continuedDirichletZTotal =ᶠ[𝓝 s]
      (fun z : ℂ => z / (z - 1) - z * zetaFloorCorrectionIntegral z) := by
    filter_upwards [hΩopen.mem_nhds hΩs] with z hz
    simp [continuedDirichletZTotal, hz.1, hz.2, continuedDirichletZ,
      continuedDirichletI]
  exact (analyticAt_continuedDirichletZ_formula hs hs1).congr heq.symm

private theorem analyticAt_continuedDirichletH0_formula {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ
      (fun z : ℂ => z / (z + 1) - (z * (z - 1) / (z + 1)) *
        zetaFloorCorrectionIntegral z) s := by
  have hsplus : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hden : AnalyticAt ℂ (fun z : ℂ => z + 1) s :=
    analyticAt_id.add analyticAt_const
  have hrat₁ : AnalyticAt ℂ (fun z : ℂ => z / (z + 1)) s :=
    analyticAt_id.div hden hsplus
  have hrat₂ : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / (z + 1)) s := by
    exact (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div hden hsplus
  have hI := analyticAt_zetaFloorCorrectionIntegral hs
  exact hrat₁.sub (hrat₂.mul hI)

/-- `H₀` is analytic throughout `Re(s)>0`; unlike `Z`, this includes `s=1`. -/
theorem analyticAt_continuedDirichletH0Total {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ continuedDirichletH0Total s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const continuous_re
  have hUs : s ∈ U := hs
  have heq : continuedDirichletH0Total =ᶠ[𝓝 s]
      (fun z : ℂ => z / (z + 1) - (z * (z - 1) / (z + 1)) *
        zetaFloorCorrectionIntegral z) := by
    filter_upwards [hUopen.mem_nhds hUs] with z hz
    change 0 < z.re at hz
    simp [continuedDirichletH0Total, hz, continuedDirichletH0, continuedDirichletI]
  exact (analyticAt_continuedDirichletH0_formula hs).congr heq.symm

/-- The value assigned at the pole is exactly the blueprint's value. -/
theorem continuedDirichletH0Total_one :
    continuedDirichletH0Total 1 = (1 / 2 : ℂ) := by
  simpa [continuedDirichletH0Total, continuedDirichletH0] using
    continuedDirichletH0_one

private theorem analyticAt_nat_cpow {p : ℕ} (hp : (p : ℂ) ≠ 0) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [] with z
  exact (differentiableAt_id.neg).const_cpow (Or.inl hp)

private theorem analyticAt_principalEulerProduct {q : ℕ} [NeZero q] (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s := by
  classical
  refine Finset.analyticAt_fun_prod (𝕜 := ℂ) (E := ℂ) (A := ℂ)
    (N := q.primeFactors) (f := fun (p : ℕ) (z : ℂ) =>
      (1 : ℂ) - (p : ℂ) ^ (-z)) (c := s) ?_
  intro p hp
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  exact analyticAt_const.sub (analyticAt_nat_cpow hp0 s)

/-- The principal continued Dirichlet function is analytic on the precise
pole-excluded half-plane in the blueprint. -/
theorem analyticAt_principalContinuedDirichletLTotal {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (principalContinuedDirichletLTotal (q := q)) s := by
  let Ω : Set ℂ := {z | 0 < z.re ∧ z ≠ 1}
  have hΩopen : IsOpen Ω := by
    dsimp [Ω]
    exact (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  have hΩs : s ∈ Ω := ⟨hs, hs1⟩
  have heq : (principalContinuedDirichletLTotal (q := q)) =ᶠ[𝓝 s]
      (fun z : ℂ => continuedDirichletZTotal z *
        ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) := by
    filter_upwards [hΩopen.mem_nhds hΩs] with z hz
    simp [principalContinuedDirichletLTotal, hz.1, hz.2,
      principalContinuedDirichletL, continuedDirichletZTotal, continuedDirichletZ,
      continuedDirichletI]
  have hprod := analyticAt_principalEulerProduct (q := q) s
  exact (analyticAt_continuedDirichletZTotal hs hs1).mul hprod |>.congr heq.symm

theorem differentiableAt_continuedDirichletZTotal {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ continuedDirichletZTotal s :=
  (analyticAt_continuedDirichletZTotal hs hs1).differentiableAt

theorem differentiableAt_continuedDirichletH0Total {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ continuedDirichletH0Total s :=
  (analyticAt_continuedDirichletH0Total hs).differentiableAt

theorem differentiableAt_principalContinuedDirichletLTotal {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (principalContinuedDirichletLTotal (q := q)) s :=
  (analyticAt_principalContinuedDirichletLTotal hs hs1).differentiableAt

theorem analyticOnNhd_continuedDirichletZTotal :
    AnalyticOnNhd ℂ continuedDirichletZTotal {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  intro s hs
  exact analyticAt_continuedDirichletZTotal hs.1 hs.2

theorem analyticOnNhd_continuedDirichletH0Total :
    AnalyticOnNhd ℂ continuedDirichletH0Total {s : ℂ | 0 < s.re} := by
  intro s hs
  exact analyticAt_continuedDirichletH0Total hs

theorem analyticOnNhd_principalContinuedDirichletLTotal {q : ℕ} [NeZero q] :
    AnalyticOnNhd ℂ (principalContinuedDirichletLTotal (q := q))
      {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  intro s hs
  exact analyticAt_principalContinuedDirichletLTotal hs.1 hs.2

theorem analyticAt_continuedDirichletH0Total_one :
    AnalyticAt ℂ continuedDirichletH0Total 1 :=
  analyticAt_continuedDirichletH0Total (by norm_num)

#print axioms analyticOnNhd_continuedDirichletZTotal
#print axioms analyticOnNhd_continuedDirichletH0Total
#print axioms analyticOnNhd_principalContinuedDirichletLTotal
#print axioms continuedDirichletH0Total_one

end FractionalPrimes.Literature.Reciprocal
