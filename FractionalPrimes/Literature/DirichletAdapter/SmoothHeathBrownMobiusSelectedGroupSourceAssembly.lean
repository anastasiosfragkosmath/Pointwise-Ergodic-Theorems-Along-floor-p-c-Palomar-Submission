module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownMobiusSubsetAssembly
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownMobiusSubsetScaleAssembly
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownMobiusSelectedGroupSourceBridge
public import FractionalPrimes.Literature.Reciprocal.MobiusUniformityOfE1
public import Mathlib.Tactic
@[expose] public section

/-!
# MUF assembly for the selected-group source interval

This adapter composes the selected Möbius-factor MUF estimate with the exact
finite source-to-tuple identity. It preserves the source threshold, scale
hypotheses, and both the finite-factor and logarithm-absorbed bounds.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The MUF small-group assembly controls the exact source interval sum for
the residue-restricted smooth Heath--Brown factors. The first bound retains
the factor `2^11 * 5^19` and the `K + 4` saving; the second is its checked
logarithm-absorbed consequence. -/
theorem smoothHeathBrownMobiusSelectedGroupSourceInterval_from_MUF
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {B K : ℝ} (hB : 0 < B) (hK : 0 < K) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fs : List (SmoothHeathBrownFactor X)) →
        (I : Finset (Fin fs.length)) →
        (selected : Fin fs.length) →
        (j : SmoothHeathBrownScaleIndex X) →
        fs.get selected = .mobius j →
        selected ∈ I → I.card ≤ 20 →
        (h : ℤ) → (L x y : ℝ) →
        {q : ℕ} → 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
        (residue : Fin fs.length → ℕ) →
        residue selected < q →
        (t : ℝ) → |t| ≤ X →
        (hMrange : ∀ M : ℝ,
          (M = smoothHeathBrownFactorScale (.mobius j) / 2 ∨
            M = smoothHeathBrownFactorScale (.mobius j)) →
          X ^ (1 / 400 : ℝ) ≤ M ∧ M ≤ X) →
        L = (2 : ℝ) ^ h *
          (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)) →
        -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ) →
        0 ≤ x → x ≤ y →
        ‖∑ n ∈ factorExtractionRealInterval x y,
            (∏ i : I,
              smoothHeathBrownResidueFactorArithmeticFunction (z := z)
                q (residue i.val) (fs.get i.val)) n *
              (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
          (2 : ℝ) ^ 11 * 5 ^ 19 *
            (3 * Cμ * (Real.log X) ^ (-(K + 4))) * Real.sqrt L ∧
        ‖∑ n ∈ factorExtractionRealInterval x y,
            (∏ i : I,
              smoothHeathBrownResidueFactorArithmeticFunction (z := z)
                q (residue i.val) (fs.get i.val)) n *
              (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
          (Real.log X) ^ (-K) * Real.sqrt L := by
  obtain ⟨Cμ, X₀, hCμ, hX₀three, hassembly⟩ :=
    smoothHeathBrownMobiusSubsetAssembly_from_MUF hMUF hB hK
  refine ⟨Cμ, X₀, hCμ, hX₀three, ?_⟩
  intro X z hX₀X hz fs I selected j htag hselected hcount h L x y
    q hq hqlog residue hresidue t ht hMrange hL hh hx hxy
  let ω : Fin fs.length → ℕ → ℂ := fun i n =>
    smoothHeathBrownMobiusResiduePhaseWeight q (residue i) t n
  have hω : ∀ i n, ‖ω i n‖ ≤ 1 := by
    intro i n
    exact smoothHeathBrownMobiusResiduePhaseWeight_norm_le_one
      q (residue i) t n
  have hωselected : ∀ n,
      ω selected n =
        smoothHeathBrownMobiusResiduePhaseWeight q (residue selected) t n := by
    intro n
    rfl
  have htuple := hassembly
    (X := X) (z := z) hX₀X hz fs I selected j htag hselected hcount h L x y
      hq hqlog (b := residue selected) hresidue t ht ω hω hωselected
      hMrange hL hh hx hxy
  have hy : 0 ≤ y := le_trans hx hxy
  have hsource := smoothHeathBrownMobiusSelectedGroupSourceInterval_eq_tupleSum
    (z := z) fs I q residue t x y hx hy
  have hsourceω :
      (∑ n ∈ factorExtractionRealInterval x y,
        (∏ i : I,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (fs.get i.val)) n *
          (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) =
        smoothGroupSubsetConvolutionSum I
          (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
          (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
            (fs.get i) (ω i) n) x y := by
    simpa [ω] using hsource
  constructor
  · rw [hsourceω]
    exact htuple.1
  · rw [hsourceω]
    exact htuple.2

/-- The accepted E1 fixed-half-plane route supplies the MUF premise, so the
same exact source-interval bounds follow without an extra uniformity input. -/
theorem smoothHeathBrownMobiusSelectedGroupSourceInterval_of_OAISource
    {B K : ℝ} (hB : 0 < B) (hK : 0 < K) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fs : List (SmoothHeathBrownFactor X)) →
        (I : Finset (Fin fs.length)) →
        (selected : Fin fs.length) →
        (j : SmoothHeathBrownScaleIndex X) →
        fs.get selected = .mobius j →
        selected ∈ I → I.card ≤ 20 →
        (h : ℤ) → (L x y : ℝ) →
        {q : ℕ} → 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
        (residue : Fin fs.length → ℕ) →
        residue selected < q →
        (t : ℝ) → |t| ≤ X →
        (hMrange : ∀ M : ℝ,
          (M = smoothHeathBrownFactorScale (.mobius j) / 2 ∨
            M = smoothHeathBrownFactorScale (.mobius j)) →
          X ^ (1 / 400 : ℝ) ≤ M ∧ M ≤ X) →
        L = (2 : ℝ) ^ h *
          (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)) →
        -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ) →
        0 ≤ x → x ≤ y →
        ‖∑ n ∈ factorExtractionRealInterval x y,
            (∏ i : I,
              smoothHeathBrownResidueFactorArithmeticFunction (z := z)
                q (residue i.val) (fs.get i.val)) n *
              (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
          (2 : ℝ) ^ 11 * 5 ^ 19 *
            (3 * Cμ * (Real.log X) ^ (-(K + 4))) * Real.sqrt L ∧
        ‖∑ n ∈ factorExtractionRealInterval x y,
            (∏ i : I,
              smoothHeathBrownResidueFactorArithmeticFunction (z := z)
                q (residue i.val) (fs.get i.val)) n *
              (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
          (Real.log X) ^ (-K) * Real.sqrt L := by
  exact smoothHeathBrownMobiusSelectedGroupSourceInterval_from_MUF
    FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource hB hK

/-- The three-group factor scale bounds discharge the exact MUF window and
give the OAISource source-interval estimate with the threshold used by the
approved selected-group argument. -/
theorem smoothHeathBrownMobiusSelectedGroupSourceInterval_of_scaleBounds_OAISource
    {B K : ℝ} (hB : 0 < B) (hK : 0 < K) :
    ∃ Cμ X₀ : ℝ, 0 < Cμ ∧ 3 ≤ X₀ ∧
      ∀ {X z : ℝ}, X₀ ≤ X → 0 ≤ z →
        (fs : List (SmoothHeathBrownFactor X)) →
        (I : Finset (Fin fs.length)) →
        (selected : Fin fs.length) →
        (j : SmoothHeathBrownScaleIndex X) →
        fs.get selected = .mobius j →
        selected ∈ I → I.card ≤ 20 →
        (h : ℤ) → (L x y : ℝ) →
        {q : ℕ} → 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
        (residue : Fin fs.length → ℕ) →
        residue selected < q →
        (t : ℝ) → |t| ≤ X →
        X ^ (1 / 100 : ℝ) ≤ smoothHeathBrownFactorScale (.mobius j) →
        smoothHeathBrownFactorScale (.mobius j) ≤
          (2 : ℝ) ^ 11 * Real.sqrt X →
        L = (2 : ℝ) ^ h *
          (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)) →
        -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ) →
        0 ≤ x → x ≤ y →
        ‖∑ n ∈ factorExtractionRealInterval x y,
            (∏ i : I,
              smoothHeathBrownResidueFactorArithmeticFunction (z := z)
                q (residue i.val) (fs.get i.val)) n *
              (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
          (2 : ℝ) ^ 11 * 5 ^ 19 *
            (3 * Cμ * (Real.log X) ^ (-(K + 4))) * Real.sqrt L ∧
        ‖∑ n ∈ factorExtractionRealInterval x y,
            (∏ i : I,
              smoothHeathBrownResidueFactorArithmeticFunction (z := z)
                q (residue i.val) (fs.get i.val)) n *
              (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ ≤
          (Real.log X) ^ (-K) * Real.sqrt L := by
  obtain ⟨Cμ, X₀, hCμ, hX₀three, hassembly⟩ :=
    smoothHeathBrownMobiusSubsetAssembly_from_MUF_of_scaleBounds
      FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource hB hK
  refine ⟨Cμ, X₀, hCμ, hX₀three, ?_⟩
  intro X z hX₀X hz fs I selected j htag hselected hcount h L x y
    q hq hqlog residue hresidue t ht hscaleLo hscaleHi hL hh hx hxy
  let ω : Fin fs.length → ℕ → ℂ := fun i n =>
    smoothHeathBrownMobiusResiduePhaseWeight q (residue i) t n
  have hω : ∀ i n, ‖ω i n‖ ≤ 1 := by
    intro i n
    exact smoothHeathBrownMobiusResiduePhaseWeight_norm_le_one
      q (residue i) t n
  have hωselected : ∀ n,
      ω selected n =
        smoothHeathBrownMobiusResiduePhaseWeight q (residue selected) t n := by
    intro n
    rfl
  have htuple := hassembly
    (X := X) (z := z) hX₀X hz fs I selected j htag hselected hcount h L x y
      hq hqlog (b := residue selected) hresidue t ht ω hω hωselected
      hscaleLo hscaleHi hL hh hx hxy
  have hy : 0 ≤ y := le_trans hx hxy
  have hsource := smoothHeathBrownMobiusSelectedGroupSourceInterval_eq_tupleSum
    (z := z) fs I q residue t x y hx hy
  have hsourceω :
      (∑ n ∈ factorExtractionRealInterval x y,
        (∏ i : I,
          smoothHeathBrownResidueFactorArithmeticFunction (z := z)
            q (residue i.val) (fs.get i.val)) n *
          (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) =
        smoothGroupSubsetConvolutionSum I
          (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
          (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
            (fs.get i) (ω i) n) x y := by
    simpa [ω] using hsource
  constructor
  · rw [hsourceω]
    exact htuple.1
  · rw [hsourceω]
    exact htuple.2

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusSelectedGroupSourceInterval_from_MUF
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusSelectedGroupSourceInterval_of_OAISource
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusSelectedGroupSourceInterval_of_scaleBounds_OAISource
