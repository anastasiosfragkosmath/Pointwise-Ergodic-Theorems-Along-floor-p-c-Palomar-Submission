module

public import FractionalPrimes.Literature.Ergodic.PrimeOrbitAbel
public import FractionalPrimes.LpAverages

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
noncomputable section

theorem primePartialSum_Lp_ae
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (g : ℕ → Lp ℂ p μ) (N : ℕ) :
    ((primePartialSum g N : Lp ℂ p μ) : X → ℂ) =ᵐ[μ]
      fun x => primePartialSum (fun n => g n x) N := by
  filter_upwards [Lp.coeFn_finsetSum ((Finset.Icc 1 N).filter Nat.Prime) g] with x hx
  simp only [primePartialSum_eq_prime_filter]
  rw [hx]
  simp only [Finset.sum_apply]

theorem primeLogPartialSum_Lp_ae
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (g : ℕ → Lp ℂ p μ) (N : ℕ) :
    ((primeLogPartialSum g N : Lp ℂ p μ) : X → ℂ) =ᵐ[μ]
      fun x => primeLogPartialSum (fun n => g n x) N := by
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      (Real.log (n : ℝ) • g n : Lp ℂ p μ) x = Real.log (n : ℝ) • g n x :=
    ae_all_iff.mpr (fun n => Lp.coeFn_smul (Real.log (n : ℝ)) (g n))
  filter_upwards [Lp.coeFn_finsetSum ((Finset.Icc 1 N).filter Nat.Prime)
    (fun n => Real.log (n : ℝ) • g n), hall] with x hsum hscalar
  simp only [primeLogPartialSum_eq_prime_filter]
  rw [hsum]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun n _ => hscalar n)

def primeOrbitLp
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) {p : ℝ≥0∞} (hf : MemLp f p S.μ) (n : ℕ) : Lp ℂ p S.μ :=
  (memLp_shift_floorPower S c n hf).toLp (S.shift (floorPower c n) f)

theorem primeOrbitLp_apply_ae
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) {p : ℝ≥0∞} (hf : MemLp f p S.μ) (n : ℕ) :
    (primeOrbitLp S c f hf n : X → ℂ) =ᵐ[S.μ]
      fun x => f (S.iterate (floorPower c n) x) := by
  filter_upwards [(memLp_shift_floorPower S c n hf).coeFn_toLp] with x hx
  change ((memLp_shift_floorPower S c n hf).toLp (S.shift (floorPower c n) f) : X → ℂ) x = _
  rw [hx]
  rfl

theorem primeLogMeanLp_orbit_ae
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hf : MemLp f p S.μ) (N : Scale) :
    (((N.val : ℝ)⁻¹ • primeLogPartialSum (primeOrbitLp S c f hf) N.val : Lp ℂ p S.μ) : X → ℂ)
      =ᵐ[S.μ] paperPrimeOnlyPart S c f N := by
  have hall : ∀ᵐ x ∂S.μ, ∀ n : ℕ,
      primeOrbitLp S c f hf n x = f (S.iterate (floorPower c n) x) :=
    ae_all_iff.mpr (fun n => primeOrbitLp_apply_ae S c f hf n)
  filter_upwards [Lp.coeFn_smul (N.val : ℝ)⁻¹
      (primeLogPartialSum (primeOrbitLp S c f hf) N.val),
    primeLogPartialSum_Lp_ae (primeOrbitLp S c f hf) N.val, hall] with x hmean hlog horbit
  rw [hmean]
  change (N.val : ℝ)⁻¹ •
    ((primeLogPartialSum (primeOrbitLp S c f hf) N.val : Lp ℂ p S.μ) : X → ℂ) x = _
  rw [hlog]
  have hvalues : (fun n => primeOrbitLp S c f hf n x) =
      (fun n => f (S.iterate (floorPower c n) x)) := funext horbit
  rw [hvalues, primeLogMean_orbit_eq]

#print axioms primeLogMeanLp_orbit_ae

theorem primeMeanLp_orbit_ae
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hf : MemLp f p S.μ) (N : ℕ) (hN : 2 ≤ N) :
    ((((Nat.primeCounting N : ℝ)⁻¹ • primePartialSum (primeOrbitLp S c f hf) N : Lp ℂ p S.μ)) : X → ℂ)
      =ᵐ[S.μ] primeAverage S c f N hN := by
  have hall : ∀ᵐ x ∂S.μ, ∀ n : ℕ,
      primeOrbitLp S c f hf n x = f (S.iterate (floorPower c n) x) :=
    ae_all_iff.mpr (fun n => primeOrbitLp_apply_ae S c f hf n)
  filter_upwards [Lp.coeFn_smul (Nat.primeCounting N : ℝ)⁻¹
      (primePartialSum (primeOrbitLp S c f hf) N),
    primePartialSum_Lp_ae (primeOrbitLp S c f hf) N, hall] with x hmean hsum horbit
  rw [hmean]
  change (Nat.primeCounting N : ℝ)⁻¹ •
    ((primePartialSum (primeOrbitLp S c f hf) N : Lp ℂ p S.μ) : X → ℂ) x = _
  rw [hsum]
  have hvalues : (fun n => primeOrbitLp S c f hf n x) =
      (fun n => f (S.iterate (floorPower c n) x)) := funext horbit
  rw [hvalues, primeMean_orbit_eq]

#print axioms primeMeanLp_orbit_ae
end
end FractionalPrimes
