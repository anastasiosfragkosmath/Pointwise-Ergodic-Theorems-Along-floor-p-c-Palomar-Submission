module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylShiftDifference
public import FractionalPrimes.Literature.Polynomial.ScalarWeylShiftedInterval

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- Apply the degree-`d-1` scalar-Weyl induction hypothesis to one large
shift correlation. The callback is the full source induction-hypothesis
contract, with `B` standing for `F_{d-1}(η⁻¹)`. -/
theorem scalarWeyl_largeShiftCorrelation_induction
    {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    {η B : ℝ}
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    {J : Finset ℤ}
    (hJinterval : ∃ lo hi : ℤ, J = Finset.Ico lo hi)
    (hJsubset : J ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    (hη : 0 < η) (hηhalf : η < 1 / 2)
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
                ((q : ℝ) * Q.coeff j) ≤ B))
    (h : ℕ) (hh : h ∈ Finset.Ico 1 N)
    (hlarge : η * (N : ℝ) ≤
      ‖∑ n ∈ J.filter (fun n => n + (h : ℤ) ∈ J),
        unitFrequencyPhase (P.eval ((n : ℝ) + (h : ℝ))) *
          star (unitFrequencyPhase (P.eval (n : ℝ)))‖) :
    ∃ q : ℕ,
      1 ≤ q ∧ (q : ℝ) ≤ B ∧
      realDistanceToIntegers
        ((q : ℝ) * (d : ℝ) * P.coeff d * (h : ℝ)) ≤
          B / (N : ℝ) ^ (d - 1) := by
  classical
  rcases hJinterval with ⟨lo, hi, rfl⟩
  let ΔP : Polynomial ℝ := Polynomial.taylor (h : ℝ) P - P
  have hΔspec := scalarWeyl_shiftDifference_spec d hd P hP (h : ℤ)
  have hΔdegree : ΔP.natDegree ≤ d - 1 := by
    simpa [ΔP] using hΔspec.1
  have hΔcoeff : ΔP.coeff (d - 1) =
      (d : ℝ) * P.coeff d * (h : ℝ) := by
    simpa [ΔP] using hΔspec.2
  rcases scalarWeyl_shiftedIco_taylorPhase N h hh lo hi hJsubset P with
    ⟨_, hfilter, hKsubset, hTaylorPhase⟩
  have hphaseProduct (x y : ℝ) :
      unitFrequencyPhase x * star (unitFrequencyPhase y) =
        unitFrequencyPhase (x - y) := by
    have hconj : star (unitFrequencyPhase y) =
        unitFrequencyPhase (-y) := by
      simpa using (unitFrequencyPhase_neg_eq_conj y).symm
    calc
      unitFrequencyPhase x * star (unitFrequencyPhase y) =
          unitFrequencyPhase x * unitFrequencyPhase (-y) := by rw [hconj]
      _ = unitFrequencyPhase (x + -y) := by
        rw [← unitFrequencyPhase_add]
      _ = unitFrequencyPhase (x - y) := by congr 1 <;> ring
  have hsum :
      (∑ n ∈ (Finset.Ico lo hi).filter
          (fun n => n + (h : ℤ) ∈ Finset.Ico lo hi),
        unitFrequencyPhase (P.eval ((n : ℝ) + (h : ℝ))) *
          star (unitFrequencyPhase (P.eval (n : ℝ)))) =
        ∑ n ∈ (Finset.Ico lo hi).filter
          (fun n => n + (h : ℤ) ∈ Finset.Ico lo hi),
          unitFrequencyPhase (ΔP.eval (n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    calc
      unitFrequencyPhase (P.eval ((n : ℝ) + (h : ℝ))) *
          star (unitFrequencyPhase (P.eval (n : ℝ))) =
        unitFrequencyPhase
          (P.eval ((n : ℝ) + (h : ℝ)) - P.eval (n : ℝ)) :=
            hphaseProduct _ _
      _ = unitFrequencyPhase (ΔP.eval (n : ℝ)) := by
        simpa [ΔP] using (hTaylorPhase n).symm
  have hlargeΔ : η * (N : ℝ) ≤
      ‖∑ n ∈ Finset.Ico lo (hi - (h : ℤ)),
        unitFrequencyPhase (ΔP.eval (n : ℝ))‖ := by
    have hlarge' := hlarge
    rw [hsum, hfilter] at hlarge'
    exact hlarge'
  obtain ⟨q, hq, hqB, hqcoeff⟩ :=
    hIH (M := N) hN ΔP hΔdegree
      (Finset.Ico lo (hi - (h : ℤ)))
      ⟨lo, hi - (h : ℤ), rfl⟩ hKsubset hη hηhalf hlargeΔ
  have htop := hqcoeff (d - 1) (by omega) (by omega)
  have htop' :
      (N : ℝ) ^ (d - 1) * realDistanceToIntegers
        ((q : ℝ) * (d : ℝ) * P.coeff d * (h : ℝ)) ≤ B := by
    simpa [hΔcoeff, mul_assoc] using htop
  have hNpow : 0 < (N : ℝ) ^ (d - 1) :=
    pow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) _
  refine ⟨q, hq, hqB, ?_⟩
  apply (le_div_iff₀ hNpow).2
  nlinarith [htop']

end FractionalPrimes.Literature.Polynomial
