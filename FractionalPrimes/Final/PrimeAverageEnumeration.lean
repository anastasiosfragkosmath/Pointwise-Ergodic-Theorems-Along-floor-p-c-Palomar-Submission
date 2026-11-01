module
public import FractionalPrimes.Final.ForwardAverageFacts

public import FractionalPrimes.Literature.Ergodic.PrimeEnumeration
public import FractionalPrimes.Literature.Ergodic.ScaleConvergenceBridge


@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace FractionalPrimes.Final
noncomputable section

section

-- Keep the instance arguments identical to the independent Challenge.
attribute [local instance 2000] NormedSpace.complexToReal NormedField.toNormedSpace NormedField.toNormedCommRing

/-- The paper's average over p₁,...,pⱼ. Mathlib's nth prime starts at zero. -/
def enumeratedPrimeAverage {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (f : X → ℂ) (J : Scale) : X → ℂ :=
  enumeratedPrimeMean (fun n => S.shift (floorTime c n) f) J.val

end

theorem primeCutoffMean_orbit_eq
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) (f : X → ℂ) (N : ℕ) (hN : 2 ≤ N) :
    primeCutoffMean (fun n => S.shift (floorTime c n) f) N =
      primeCutoffAverage S c f N hN := by
  funext x
  simp only [primeCutoffMean, primeCutoffAverage, primeAverage, Pi.smul_apply, Finset.sum_apply,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
    smul_eq_mul, InvertibleSystem.shift]

theorem enumeratedPrimeAverage_eq_cutoff_at_nth_prime
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) (f : X → ℂ) (j : ℕ) :
    enumeratedPrimeAverage S c f ⟨j + 1, by omega⟩ =
      primeCutoffAverage S c f (Nat.nth Nat.Prime j) (Nat.prime_nth_prime j).two_le := by
  rw [enumeratedPrimeAverage, enumeratedPrimeMean_succ_eq_cutoff,
    primeCutoffMean_orbit_eq]

theorem primeAverage_eq_enumerated_at_primeCounting
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) (f : X → ℂ) (N : ℕ) (hN : 2 ≤ N) :
    primeCutoffAverage S c f N hN = enumeratedPrimeAverage S c f
      ⟨Nat.primeCounting N, primeCounting_pos_of_two_le hN⟩ := by
  rw [← primeCutoffMean_orbit_eq S c f N hN, primeCutoffMean_eq_enumerated]
  rfl

private theorem tendsto_natSucc_positiveScale :
    Tendsto (fun n : ℕ => (⟨n + 1, by omega⟩ : Scale)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro J
  filter_upwards [eventually_ge_atTop J.val] with n hn
  change J.val ≤ n + 1
  omega

/-- The two actual prime formulations are equivalent for any observable,
including point evaluation and the Lp error seminorm. -/
theorem primeAverage_tendsto_iff_enumerated
    {X F : Type*} [MeasurableSpace X] [TopologicalSpace F]
    (S : System X) (c : ℝ) (f : X → ℂ)
    (H : (X → ℂ) → F) (l : F) :
    Tendsto (fun n : ℕ => H (primeCutoffAverage S c f (n + 2) (by omega))) atTop (𝓝 l) ↔
      Tendsto (fun J : Scale => H (enumeratedPrimeAverage S c f J)) atTop (𝓝 l) := by
  have h := primeMean_tendsto_iff_enumerated
    (fun n => S.shift (floorTime c n) f) H l
  have hcut : (fun n : ℕ => H (primeCutoffMean
      (fun k => S.shift (floorTime c k) f) (n + 2))) =
      (fun n : ℕ => H (primeCutoffAverage S c f (n + 2) (by omega))) := by
    funext n
    rw [primeCutoffMean_orbit_eq S c f (n + 2) (by omega)]
  rw [hcut] at h
  constructor
  · intro hc
    have hs : Tendsto (fun j : ℕ => H (enumeratedPrimeMean
        (fun k => S.shift (floorTime c k) f) (j + 1))) atTop (𝓝 l) := h.mp hc
    exact tendsto_scale_of_natSucc (fun J => H (enumeratedPrimeAverage S c f J)) hs
  · intro he
    have hs : Tendsto (fun j : ℕ =>
        H (enumeratedPrimeAverage S c f ⟨j + 1, by omega⟩)) atTop (𝓝 l) :=
      he.comp tendsto_natSucc_positiveScale
    change Tendsto (fun j : ℕ => H (enumeratedPrimeMean
      (fun k => S.shift (floorTime c k) f) (j + 1))) atTop (𝓝 l) at hs
    exact h.mpr hs

theorem primeAverage_ae_tendsto_iff_enumerated
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) (f g : X → ℂ) :
    (∀ᵐ x ∂S.μ, Tendsto (fun n : ℕ => primeCutoffAverage S c f (n + 2) (by omega) x)
      atTop (𝓝 (g x))) ↔
    (∀ᵐ x ∂S.μ, Tendsto (fun J : Scale => enumeratedPrimeAverage S c f J x)
      atTop (𝓝 (g x))) := by
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun x =>
    primeAverage_tendsto_iff_enumerated S c f (fun a => a x) (g x))

theorem primeAverage_eLpNorm_tendsto_iff_enumerated
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) (f g : X → ℂ) (p : ℝ≥0∞) :
    Tendsto (fun n : ℕ => eLpNorm (primeCutoffAverage S c f (n + 2) (by omega) - g) p S.μ)
      atTop (𝓝 0) ↔
    Tendsto (fun J : Scale => eLpNorm (enumeratedPrimeAverage S c f J - g) p S.μ)
      atTop (𝓝 0) :=
  primeAverage_tendsto_iff_enumerated S c f (fun a => eLpNorm (a - g) p S.μ) 0

#print axioms enumeratedPrimeAverage_eq_cutoff_at_nth_prime
#print axioms primeAverage_ae_tendsto_iff_enumerated
#print axioms primeAverage_eLpNorm_tendsto_iff_enumerated
end
end FractionalPrimes.Final
