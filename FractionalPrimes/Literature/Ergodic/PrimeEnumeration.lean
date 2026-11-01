module

public import FractionalPrimes.Literature.Ergodic.PrimeOrbitAbel
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section
open Filter
open scoped Topology
namespace FractionalPrimes
noncomputable section

/-- Reindex the primes through N by Mathlib's zero-based increasing enumeration. -/
theorem sum_primes_eq_sum_nth_prime
    {E : Type*} [AddCommMonoid E] (g : ℕ → E) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, g n =
      ∑ j ∈ Finset.range (Nat.primeCounting N), g (Nat.nth Nat.Prime j) := by
  classical
  symm
  apply Finset.sum_bij (fun j _ => Nat.nth Nat.Prime j)
  · intro j hj
    have hj' : j < Nat.count Nat.Prime (N + 1) := Finset.mem_range.mp hj
    have hle : Nat.nth Nat.Prime j ≤ N := by
      have := Nat.nth_lt_of_lt_count hj'
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Nat.prime_nth_prime j).one_lt.le, hle⟩, Nat.prime_nth_prime j⟩
  · intro i hi j hj hij
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
  · intro n hn
    obtain ⟨hnI, hnp⟩ := Finset.mem_filter.mp hn
    refine ⟨Nat.count Nat.Prime n, Finset.mem_range.mpr ?_, Nat.nth_count hnp⟩
    exact Nat.count_strict_mono hnp (by have := (Finset.mem_Icc.mp hnI).2; omega)
  · intro j hj
    rfl

theorem primeCounting_nth_prime (j : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime j) = j + 1 :=
  Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime j

/-- A normalized prime prefix, with the harmless totalized value at N < 2. -/
def primeCutoffMean {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (g : ℕ → E) (N : ℕ) : E :=
  (Nat.primeCounting N : ℝ)⁻¹ • ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, g n

/-- The first J primes; j=0 here is the paper's prime p₁. -/
def enumeratedPrimeMean {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (g : ℕ → E) (J : ℕ) : E :=
  (J : ℝ)⁻¹ • ∑ j ∈ Finset.range J, g (Nat.nth Nat.Prime j)

theorem primeCutoffMean_eq_enumerated
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (g : ℕ → E) (N : ℕ) :
    primeCutoffMean g N = enumeratedPrimeMean g (Nat.primeCounting N) := by
  simp only [primeCutoffMean, enumeratedPrimeMean, sum_primes_eq_sum_nth_prime]

theorem enumeratedPrimeMean_succ_eq_cutoff
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (g : ℕ → E) (j : ℕ) :
    enumeratedPrimeMean g (j + 1) = primeCutoffMean g (Nat.nth Nat.Prime j) := by
  rw [primeCutoffMean_eq_enumerated, primeCounting_nth_prime]

theorem tendsto_nth_prime_sub_two :
    Tendsto (fun j : ℕ => Nat.nth Nat.Prime j - 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with j hj
  have := Nat.add_two_le_nth_prime j
  omega

theorem tendsto_primeCounting_add_two_sub_one :
    Tendsto (fun n : ℕ => Nat.primeCounting (n + 2) - 1) atTop atTop := by
  have h := Nat.tendsto_primeCounting.comp (tendsto_add_atTop_nat 2)
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [h.eventually (eventually_ge_atTop (b + 1))] with n hn
  dsimp only [Function.comp_apply] at hn
  omega

/-- Exact cofinal equivalence, also applicable to a seminorm or any other
observable of the averages. No analytic convergence hypothesis is added. -/
theorem primeMean_tendsto_iff_enumerated
    {E F : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace F]
    (g : ℕ → E) (H : E → F) (l : F) :
    Tendsto (fun n : ℕ => H (primeCutoffMean g (n + 2))) atTop (𝓝 l) ↔
      Tendsto (fun j : ℕ => H (enumeratedPrimeMean g (j + 1))) atTop (𝓝 l) := by
  constructor
  · intro h
    have hc := h.comp tendsto_nth_prime_sub_two
    apply hc.congr'
    exact Eventually.of_forall fun j => by
      dsimp only [Function.comp_apply]
      rw [Nat.sub_add_cancel (Nat.prime_nth_prime j).two_le,
        enumeratedPrimeMean_succ_eq_cutoff]
  · intro h
    have hc := h.comp tendsto_primeCounting_add_two_sub_one
    apply hc.congr'
    filter_upwards [Nat.tendsto_primeCounting.comp (tendsto_add_atTop_nat 2) |>.eventually
      (eventually_ge_atTop (1 : ℕ))] with n hn
    dsimp only [Function.comp_apply] at hn ⊢
    rw [Nat.sub_add_cancel hn, primeCutoffMean_eq_enumerated]

#print axioms sum_primes_eq_sum_nth_prime
#print axioms primeMean_tendsto_iff_enumerated
end
end FractionalPrimes
