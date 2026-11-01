module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylIntervalTopCorrectionPrefix
public import FractionalPrimes.Literature.Polynomial.ScalarWeylLongShiftToAffine
public import FractionalPrimes.Literature.Polynomial.ScalarWeylPhaseFactorization

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open FractionalPrimes.Literature.Uniformity
open _root_.Polynomial

set_option maxHeartbeats 600000 in
/-- Assemble the long-shift, affine-recurrence, and Abel-prefix steps of the
long branch. The top-monomial truncation supplies the first factor, while the
checked monomial variation estimate controls the exact `1 + 8R` loss. -/
theorem scalarWeyl_longBranch_topCorrectionPrefix
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
    (hIH : ∀ {M : ℕ}, 1 ≤ M →
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
                ((q : ℝ) * Q.coeff j) ≤ B)) :
    ∃ r : ℕ, ∃ a : ℤ, ∃ k : ℕ,
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
            (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d)‖ := by
  classical
  let J : Finset ℤ := Finset.Ico lo hi
  have hJinterval : ∃ a b : ℤ, J = Finset.Ico a b := ⟨lo, hi, rfl⟩
  have hlong := scalarWeyl_longShiftToAffine hd hN hδ hδhalf hη hB hσ hR
    hNlong P hP J hJinterval hJsubset hlarge hIH
  obtain ⟨q₀, q₁, hq₀, hq₀B, hq₁, hq₁upper, hqnear⟩ := hlong

  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηhalf : η < 1 / 2 := by
    rw [hη]
    nlinarith [hδhalf]
  have hσpos : 0 < σ := by rw [hσ]; positivity
  have hσle : σ ≤ 1 := by
    rw [hσ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * B)).2
    nlinarith [hηhalf, hB]
  have hcombine := scalarWeyl_combineTopCoefficientDenominators
    hd hB hσpos hσle hq₀ hq₀B hq₁ hq₁upper hqnear
  let r : ℕ := d * q₀ * q₁
  have hr : 1 ≤ r := by simpa [r] using hcombine.1
  have hrR : (r : ℝ) ≤ R := by simpa [r, hR] using hcombine.2.1
  have hdist : realDistanceToIntegers ((r : ℝ) * P.coeff d) ≤
      R / ((N : ℝ) ^ d) := by
    simpa [r, hR] using hcombine.2.2

  let Plo : Polynomial ℝ := scalarWeyl_topMonomialTruncation d P
  have htrunc := scalarWeyl_topMonomialTruncation_spec d P hP
  have hPlo : Plo.natDegree ≤ d - 1 := by simpa [Plo] using htrunc.1
  let f : ℤ → ℂ := fun n => unitFrequencyPhase (Plo.eval (n : ℝ))
  have hphaseSum :
      (∑ n ∈ J, unitFrequencyPhase (P.eval (n : ℝ))) =
        ∑ n ∈ J, f n *
          unitFrequencyPhase (P.coeff d * (n : ℝ) ^ d) := by
    apply Finset.sum_congr rfl
    intro n hn
    simpa [J, f, Plo] using
      scalarWeyl_topTruncationPhase_factorization d P hP n
  have hlargeFactor : δ * (N : ℝ) ≤
      ‖∑ n ∈ J, f n *
          unitFrequencyPhase (P.coeff d * (n : ℝ) ^ d)‖ := by
    calc
      δ * (N : ℝ) ≤ ‖∑ n ∈ J, unitFrequencyPhase (P.eval (n : ℝ))‖ := by
        simpa [J] using hlarge
      _ = ‖∑ n ∈ J, f n *
          unitFrequencyPhase (P.coeff d * (n : ℝ) ^ d)‖ :=
        congrArg norm hphaseSum

  have hRnonneg : 0 ≤ R := by rw [hR]; positivity
  have hJbounds : ∀ n ∈ J, (1 : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by
    intro n hn
    exact Finset.mem_Icc.mp (hJsubset (by simpa [J] using hn))
  have hTV : ∀ θ : ℝ,
      |θ| ≤ R / ((r : ℝ) * (N : ℝ) ^ d) →
        finiteOrderedTotalVariation J
          (fun n => unitFrequencyPhase (θ * (n : ℝ) ^ d)) ≤ 1 + 8 * R := by
    intro θ hθ
    have hvar := scalarWeyl_monomialPhaseVariation
      hd hN hr hRnonneg hθ J hJbounds
    simpa [J] using hvar.2
  have hA : 0 < δ * (N : ℝ) :=
    mul_pos hδ (by exact_mod_cast (show 0 < N by omega))
  obtain ⟨a, k, hk, hprefixSubset, happrox, hprefix⟩ :=
    scalarWeyl_Ico_topCorrection_initialPrefix
      lo hi hr hN hRnonneg hA hdist f hlargeFactor hTV
  refine ⟨r, a, k, hr, hrR, hdist, hk, hprefixSubset, happrox, ?_⟩
  simpa [J, f, Plo] using hprefix

end FractionalPrimes.Literature.Polynomial
