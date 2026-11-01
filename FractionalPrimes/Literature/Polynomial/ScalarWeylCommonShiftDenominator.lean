module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylShiftInduction
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- Pigeonhole the shift-dependent induction denominators into one common
denominator. The conclusion retains the source count `2 * σ * N = η * N / B`.
The auxiliary predicate can record the top-coefficient distance estimate for
each selected shift. -/
theorem scalarWeyl_commonShiftDenominator
    {N : ℕ} {η B σ : ℝ} (H : Finset ℕ)
    (hη : 0 < η) (hB : 1 ≤ B) (hσ : σ = η / (2 * B))
    (hcount : η * (N : ℝ) ≤ (H.card : ℝ))
    (P : ℕ → ℕ → Prop)
    (hden : ∀ h ∈ H, ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ B ∧ P q h) :
    ∃ q₀ : ℕ, ∃ H₀ : Finset ℕ,
      1 ≤ q₀ ∧ (q₀ : ℝ) ≤ B ∧
      2 * σ * (N : ℝ) ≤ (H₀.card : ℝ) ∧
      H₀ ⊆ H ∧ ∀ h ∈ H₀, P q₀ h := by
  classical
  let K : ℕ := ⌊B⌋₊
  let Q : Finset ℕ := Finset.Ico 1 (K + 1)
  let den : ℕ → ℕ := fun h =>
    if hh : h ∈ H then Classical.choose (hden h hh) else 0
  let fiber : ℕ → Finset ℕ := fun q => H.filter (fun h => den h = q)
  let mass : ℕ → ℝ := fun q => (fiber q).card

  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hKpos : 1 ≤ K := by
    dsimp [K]
    exact Nat.le_floor (by exact_mod_cast hB)
  have hQnonempty : Q.Nonempty := by
    refine ⟨1, ?_⟩
    simp only [Q, Finset.mem_Ico]
    exact ⟨by omega, by omega⟩

  have hden_spec (h : ℕ) (hh : h ∈ H) :
      1 ≤ den h ∧ (den h : ℝ) ≤ B ∧ P (den h) h := by
    simp only [den, dite_eq_left hh]
    exact Classical.choose_spec (hden h hh)

  have hmap : ∀ h ∈ H, den h ∈ Q := by
    intro h hh
    have hspec := hden_spec h hh
    have hfloor : den h ≤ K := by
      dsimp [K]
      exact Nat.le_floor hspec.2.1
    simp only [Q, Finset.mem_Ico]
    exact ⟨hspec.1, by omega⟩

  have hcardEq : H.card = ∑ q ∈ Q, (fiber q).card := by
    dsimp [fiber]
    exact Finset.card_eq_sum_card_fiberwise hmap

  have hQcard : (Q.card : ℝ) = (K : ℝ) := by
    simp [Q]

  have hcardCast : (H.card : ℝ) = ∑ q ∈ Q, mass q := by
    rw [hcardEq]
    simp [mass, fiber]

  let M : ℝ := Q.sup' hQnonempty mass
  have hmassLe (q : ℕ) (hq : q ∈ Q) : mass q ≤ M := by
    dsimp [M]
    exact Finset.le_sup' (s := Q) (f := mass) hq
  have hsumM : (∑ q ∈ Q, mass q) ≤ (K : ℝ) * M := by
    calc
      (∑ q ∈ Q, mass q) ≤ ∑ q ∈ Q, M :=
        Finset.sum_le_sum fun q hq => hmassLe q hq
      _ = (Q.card : ℝ) * M := by simp
      _ = (K : ℝ) * M := by rw [hQcard]

  obtain ⟨q₀, hq₀, hq₀max⟩ := Finset.exists_mem_eq_sup' hQnonempty mass
  have hmax : mass q₀ = M := by simpa [M] using hq₀max.symm
  have hMnonneg : 0 ≤ M := by
    rw [← hmax]
    positivity

  have hKleB : (K : ℝ) ≤ B := by
    dsimp [K]
    exact Nat.floor_le (by linarith)
  have hηtoM : η * (N : ℝ) ≤ B * M := by
    calc
      η * (N : ℝ) ≤ (H.card : ℝ) := hcount
      _ = ∑ q ∈ Q, mass q := hcardCast
      _ ≤ (K : ℝ) * M := hsumM
      _ ≤ B * M := mul_le_mul_of_nonneg_right hKleB hMnonneg
  have hratio : 2 * σ * (N : ℝ) = η * (N : ℝ) / B := by
    rw [hσ]
    field_simp
  have hηdiv : η * (N : ℝ) / B ≤ M := by
    apply (div_le_iff₀ hBpos).2
    nlinarith [hηtoM]
  have hcountFiber : 2 * σ * (N : ℝ) ≤ M := by
    rw [hratio]
    exact hηdiv

  let H₀ := fiber q₀
  have hH₀card : (H₀.card : ℝ) = M := by
    simpa [H₀, mass, fiber] using hmax
  have hq₀bounds : 1 ≤ q₀ ∧ (q₀ : ℝ) ≤ B := by
    have hq₀Ico := Finset.mem_Ico.mp hq₀
    have hq₀K : q₀ ≤ K := by omega
    constructor
    · exact hq₀Ico.1
    · exact (Nat.cast_le.mpr hq₀K).trans hKleB
  refine ⟨q₀, H₀, hq₀bounds.1, hq₀bounds.2, ?_, ?_, ?_⟩
  · rw [hH₀card]
    exact hcountFiber
  · exact Finset.filter_subset _ _
  · intro h hh₀
    have hhfilter := Finset.mem_filter.mp hh₀
    have hspec := hden_spec h hhfilter.1
    rw [hhfilter.2] at hspec
    exact hspec.2.2

end FractionalPrimes.Literature.Polynomial
