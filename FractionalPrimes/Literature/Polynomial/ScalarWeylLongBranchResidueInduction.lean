module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylLongBranchTopCorrection
public import FractionalPrimes.Literature.Polynomial.ScalarWeylSelectedResidueData
public import FractionalPrimes.Literature.Polynomial.ScalarWeylResidueInductionInput
public import FractionalPrimes.Literature.Polynomial.ScalarWeylInductionApplication

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

set_option maxHeartbeats 600000 in
/-- Continue the long branch from its Abel prefix through residue selection,
affine reindexing, and the degree-`d-1` induction hypothesis. The fixed-`η`
callback supplies the shift denominators; the full density callback supplies
the final residue-polynomial denominator `s`. -/
theorem scalarWeyl_longBranch_residueInductionInput
    {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    {δ η B σ R : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hη : η = δ ^ 2 / 8) (hB : 1 ≤ B)
    (hσ : σ = η / (2 * B))
    (hR : R = 32 * (d : ℝ) * B * (σ⁻¹) ^ 2)
    (hNlong : 4 * R ≤ (N : ℝ))
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (lo hi : ℤ)
    (hJsubset : Finset.Ico lo hi ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    (hlarge : δ * (N : ℝ) ≤
      ‖∑ n ∈ Finset.Ico lo hi, unitFrequencyPhase (P.eval (n : ℝ))‖)
    (hIHη : ∀ {M : ℕ}, 1 ≤ M →
      ∀ (Q : Polynomial ℝ), Q.natDegree ≤ d - 1 →
        ∀ K : Finset ℤ,
          (∃ a b : ℤ, K = Finset.Ico a b) →
          K ⊆ Finset.Icc (1 : ℤ) (M : ℤ) →
          0 < η → η < 1 / 2 →
          η * (M : ℝ) ≤
            ‖∑ n ∈ K, unitFrequencyPhase (Q.eval (n : ℝ))‖ →
          ∃ q : ℕ,
            1 ≤ q ∧ (q : ℝ) ≤ B ∧
            (∀ j, 1 ≤ j → j ≤ d - 1 →
              (M : ℝ) ^ j * realDistanceToIntegers
                ((q : ℝ) * Q.coeff j) ≤ B))
    (hIHfull : ∀ {M : ℕ}, 1 ≤ M →
      ∀ {ε : ℝ}, 0 < ε → ε < 1 / 2 →
      ∀ (Q : Polynomial ℝ), Q.natDegree ≤ d - 1 →
        ∀ K : Finset ℤ,
          (∃ a b : ℤ, K = Finset.Ico a b) →
          K ⊆ Finset.Icc (1 : ℤ) (M : ℤ) →
          ε * (M : ℝ) ≤
            ‖∑ n ∈ K, unitFrequencyPhase (Q.eval (n : ℝ))‖ →
          ∃ s : ℕ,
            1 ≤ s ∧
            (s : ℝ) ≤
              (weylBoundPolynomial (d - 1)).eval₂
                (Nat.castRingHom ℝ) ε⁻¹ ∧
            (∀ i, 1 ≤ i → i ≤ d - 1 →
              (M : ℝ) ^ i * realDistanceToIntegers
                ((s : ℝ) * Q.coeff i) ≤
                  (weylBoundPolynomial (d - 1)).eval₂
                    (Nat.castRingHom ℝ) ε⁻¹)) :
    ∃ r : ℕ, ∃ a : ℤ, ∃ k : ℕ, ∃ b : ℤ, ∃ N' : ℕ,
      ∃ c : ℤ, ∃ K : Finset ℤ, ∃ Q : Polynomial ℝ, ∃ s : ℕ,
        1 ≤ r ∧ (r : ℝ) ≤ R ∧
        realDistanceToIntegers ((r : ℝ) * P.coeff d) ≤
          R / ((N : ℝ) ^ d) ∧
        k < (hi - lo).toNat ∧
        Finset.Ico lo (lo + ((k + 1 : ℕ) : ℤ)) ⊆ Finset.Ico lo hi ∧
        |P.coeff d - (a : ℝ) / (r : ℝ)| ≤
          R / ((r : ℝ) * (N : ℝ) ^ d) ∧
        δ * (N : ℝ) / (1 + 8 * R) ≤
          ‖∑ n ∈ Finset.Ico lo (lo + ((k + 1 : ℕ) : ℤ)),
            unitFrequencyPhase
              ((scalarWeyl_topMonomialTruncation d P).eval (n : ℝ)) *
            unitFrequencyPhase
              (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d)‖ ∧
        b ∈ Finset.Icc (1 : ℤ) (r : ℤ) ∧
        δ * (N : ℝ) / ((r : ℝ) * (1 + 8 * R)) ≤
          ‖∑ n ∈ (Finset.Ico lo (lo + ((k + 1 : ℕ) : ℤ))).filter
            (fun n => n ≡ b [ZMOD (r : ℤ)]),
              unitFrequencyPhase
                ((scalarWeyl_topMonomialTruncation d P).eval (n : ℝ))‖ ∧
        N' = N ⌈/⌉ r ∧
        1 ≤ N' ∧
        (N : ℝ) / (r : ℝ) ≤ (N' : ℝ) ∧
        (N' : ℝ) ≤ 2 * (N : ℝ) / (r : ℝ) ∧
        c = b - (r : ℤ) ∧
        K = Finset.Ico
          (Int.ceil (((lo - c : ℤ) : ℚ) / (r : ℚ)))
          (Int.ceil (((lo + ((k + 1 : ℕ) : ℤ) - c : ℤ) : ℚ) / (r : ℚ))) ∧
        Q = (scalarWeyl_topMonomialTruncation d P).comp
          (Polynomial.C (r : ℝ) * Polynomial.X + Polynomial.C (c : ℝ)) ∧
        K ⊆ Finset.Icc (1 : ℤ) (N' : ℤ) ∧
        Q.natDegree ≤ d - 1 ∧
        (∃ a' b' : ℤ, K = Finset.Ico a' b') ∧
        1 ≤ s ∧
        (s : ℝ) ≤
          (weylBoundPolynomial (d - 1)).eval₂
            (Nat.castRingHom ℝ) (4 * (1 + 8 * R) / δ) ∧
        (∀ i, 1 ≤ i → i < d →
          realDistanceToIntegers ((s : ℝ) * Q.coeff i) ≤
            ((weylBoundPolynomial (d - 1)).eval₂
              (Nat.castRingHom ℝ) (4 * (1 + 8 * R) / δ)) /
              ((N' : ℝ) ^ i)) := by
  classical
  let Plo : Polynomial ℝ := scalarWeyl_topMonomialTruncation d P
  let V : ℝ := 1 + 8 * R
  have hRnonneg : 0 ≤ R := by rw [hR]; positivity
  have hV : 1 ≤ V := by dsimp [V]; nlinarith [hRnonneg]
  have hPlo : Plo.natDegree ≤ d - 1 := by
    have hspec := scalarWeyl_topMonomialTruncation_spec d P hP
    simpa [Plo] using hspec.1
  obtain ⟨r, a, k, hr, hrR, hdist, hk, hprefixSubset, happrox, hprefix⟩ :=
    scalarWeyl_longBranch_topCorrectionPrefix
      hd hN hδ hδhalf hη hB hσ hR hNlong P hP lo hi hJsubset hlarge hIHη
  let hi' : ℤ := lo + ((k + 1 : ℕ) : ℤ)
  have hprefixSubsetN :
      Finset.Ico lo hi' ⊆ Finset.Icc (1 : ℤ) (N : ℤ) := by
    simpa [hi'] using hprefixSubset.trans hJsubset
  let f : ℤ → ℂ := fun n => unitFrequencyPhase (Plo.eval (n : ℝ))
  have hprefixLarge : δ * (N : ℝ) / V ≤
      ‖∑ n ∈ Finset.Ico lo hi',
        f n * unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d)‖ := by
    simpa [V, hi', f, Plo] using hprefix
  let N' : ℕ := N ⌈/⌉ r
  obtain ⟨b, hb, hselected, hN'pos, hN'lower, hN'upper⟩ :=
    scalarWeyl_selectedResidueAndCeilingPrerequisites
      hr hrR hNlong hV (by rfl) lo hi' hprefixSubsetN a f hprefixLarge
  have hrpos : 0 < r := by omega
  let c : ℤ := b - (r : ℤ)
  let K : Finset ℤ := Finset.Ico
    (Int.ceil (((lo - c : ℤ) : ℚ) / (r : ℚ)))
    (Int.ceil (((hi' - c : ℤ) : ℚ) / (r : ℚ)))
  let Q : Polynomial ℝ :=
    Plo.comp (Polynomial.C (r : ℝ) * Polynomial.X +
      Polynomial.C (c : ℝ))
  have hreindex := scalarWeyl_selectedResidue_reindexForInduction
    hrpos (by rfl) lo hi' b hb hprefixSubsetN Plo hPlo hselected
  have hreindex' :
      K ⊆ Finset.Icc (1 : ℤ) (N' : ℤ) ∧
      Q.natDegree ≤ d - 1 ∧
      (∀ t : ℤ,
        Q.eval (t : ℝ) =
          Plo.eval ((c : ℝ) + (r : ℝ) * (t : ℝ))) ∧
      (∃ a' b' : ℤ, K = Finset.Ico a' b') ∧
      δ * (N : ℝ) / ((r : ℝ) * V) ≤
        ‖∑ t ∈ K, unitFrequencyPhase (Q.eval (t : ℝ))‖ := by
    simpa [c, K, Q, hi', N', Plo] using hreindex
  rcases hreindex' with ⟨hKsubset, hQdegree, _hQeval, hKinterval, hQlarge⟩
  have hrReal : 0 < (r : ℝ) := by exact_mod_cast hrpos
  obtain ⟨s, hs, hsBound, hβscaled⟩ :=
    scalarWeyl_selectedResidue_inductionApplication
      hd hN'pos hδ hδhalf hV hrReal hN'upper Q hQdegree K hKinterval
      hKsubset hQlarge hIHfull
  have hN'posReal : 0 < (N' : ℝ) := by
    exact_mod_cast (show 0 < N' by omega)
  have hβ : ∀ i, 1 ≤ i → i < d →
      realDistanceToIntegers ((s : ℝ) * Q.coeff i) ≤
        ((weylBoundPolynomial (d - 1)).eval₂
          (Nat.castRingHom ℝ) (4 * V / δ)) / ((N' : ℝ) ^ i) := by
    intro i hi hid
    apply (le_div_iff₀ (pow_pos hN'posReal i)).2
    have hscaled := hβscaled i hi (by omega)
    nlinarith [hscaled]
  refine ⟨r, a, k, b, N', c, K, Q, s,
    hr, hrR, hdist, hk, hprefixSubset, happrox, ?_, hb, ?_, rfl,
    hN'pos, hN'lower, hN'upper, rfl, rfl, rfl,
    hKsubset, hQdegree, hKinterval, hs, ?_, ?_⟩
  · simpa [V, hi', f, Plo] using hprefix
  · simpa [V, hi', f, Plo, N'] using hselected
  · simpa [V] using hsBound
  · simpa [V] using hβ

end FractionalPrimes.Literature.Polynomial
