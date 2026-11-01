module

public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter
public import FractionalPrimes.Literature.Twisted.CharacterEvalNorm
public import FractionalPrimes.Literature.Reciprocal.ZetaFloorIdentity

@[expose] public section

noncomputable section

open MeasureTheory Set Complex

namespace FractionalPrimes.Literature.Reciprocal

/-- The finite partial sum `S_χ(u)` from blueprint element `lrc:dirichlet-data`.
The domain argument records the blueprint's condition `u ≥ 1`; the upper
endpoint `Nat.floor u` is exactly the integer cutoff `n ≤ u`. -/
def continuedDirichletPartialSum {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (u : ℝ) (_hu : 1 ≤ u) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor u),
    FractionalPrimes.Literature.Twisted.evalInt χ (n : ℤ)

/-- The integrand's finite-sum formula, totalized outside `u ≥ 1` only to make
it convenient as a measurable-function argument. On the integration domain
`u > 1`, it agrees definitionally with `continuedDirichletPartialSum`. -/
def continuedDirichletPartialSumFormula {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor u),
    FractionalPrimes.Literature.Twisted.evalInt χ (n : ℤ)

/-- One complete period of a nonprincipal character has sum zero. This is the
period-cancellation step in the proof of `lrc:continued-lseries`; the block
contains the `q` consecutive integers `a, ..., a + q - 1`. -/
theorem nonprincipalCharacter_sum_one_period {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    (a : ℕ) :
    (∑ n ∈ Finset.range q,
      FractionalPrimes.Literature.Twisted.evalInt χ ((a + n : ℕ) : ℤ)) = 0 := by
  classical
  have hχ' : χ ≠ (1 : _root_.DirichletCharacter ℂ q) := by
    simpa [FractionalPrimes.Literature.Twisted.principalCharacter] using hχ
  have hsum : (∑ z : ZMod q, χ z) = 0 :=
    MulChar.sum_eq_zero_of_ne_one hχ'
  calc
    (∑ n ∈ Finset.range q,
        FractionalPrimes.Literature.Twisted.evalInt χ ((a + n : ℕ) : ℤ)) =
        ∑ z : ZMod q, χ z := by
      unfold FractionalPrimes.Literature.Twisted.evalInt
      refine Finset.sum_bij (fun n _ => ((a + n : ℕ) : ZMod q)) ?_ ?_ ?_ ?_
      · intro n hn
        exact Finset.mem_univ _
      · intro n hn m hm hnm
        have hcast : (a : ZMod q) + (n : ZMod q) = (a : ZMod q) + (m : ZMod q) := by
          simpa only [Nat.cast_add] using hnm
        have hnm' : (n : ZMod q) = (m : ZMod q) := add_left_cancel hcast
        have hmod := (ZMod.natCast_eq_natCast_iff' n m q).mp hnm'
        rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hn),
          Nat.mod_eq_of_lt (Finset.mem_range.mp hm)] at hmod
        exact hmod
      · intro z hz
        let w : ZMod q := z - (a : ZMod q)
        refine ⟨w.val, Finset.mem_range.mpr (ZMod.val_lt w), ?_⟩
        rw [Nat.cast_add]
        rw [ZMod.natCast_zmod_val w]
        dsimp [w]
        abel
      · intro n hn
        simp [Nat.cast_add]
    _ = 0 := hsum

/-- A nonprincipal character's partial sums have modulus at most the modulus.
Repeatedly remove complete periods; the final block has fewer than `q` terms. -/
theorem continuedDirichletPartialSum_norm_le_modulus {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    (u : ℝ) (hu : 1 ≤ u) :
    ‖continuedDirichletPartialSum χ u hu‖ ≤ q := by
  classical
  let f : ℕ → ℂ := fun n => FractionalPrimes.Literature.Twisted.evalInt χ (n : ℤ)
  have hsumIcc_eq_range (N : ℕ) :
      (∑ n ∈ Finset.Icc 1 N, f n) =
        ∑ k ∈ Finset.range N, f (1 + k) := by
    calc
      (∑ n ∈ Finset.Icc 1 N, f n) =
          ∑ n ∈ Finset.Ico 1 (N + 1), f n := by
            rw [← Finset.Ico_add_one_right_eq_Icc]
      _ = ∑ k ∈ Finset.range N, f (1 + k) := by
            simpa using (Finset.sum_Ico_eq_sum_range f 1 (N + 1))
  have hsplit (N : ℕ) (hNq : q ≤ N) :
      (∑ n ∈ Finset.Icc 1 N, f n) =
        (∑ n ∈ Finset.Icc 1 (N - q), f n) +
          ∑ k ∈ Finset.range q, f (N - q + 1 + k) := by
    calc
      (∑ n ∈ Finset.Icc 1 N, f n) =
          ∑ n ∈ Finset.Ico 1 (N + 1), f n := by
            rw [← Finset.Ico_add_one_right_eq_Icc]
      _ = (∑ n ∈ Finset.Ico 1 (N - q + 1), f n) +
            ∑ n ∈ Finset.Ico (N - q + 1) (N + 1), f n := by
              symm
              exact Finset.sum_Ico_consecutive f (by omega) (by omega)
      _ = (∑ n ∈ Finset.Icc 1 (N - q), f n) +
            ∑ k ∈ Finset.range q, f (N - q + 1 + k) := by
              rw [Finset.Ico_add_one_right_eq_Icc]
              rw [Finset.sum_Ico_eq_sum_range]
              rw [show N + 1 - (N - q + 1) = q by omega]
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hbound : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ (q : ℝ) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        by_cases hNq : N < q
        · calc
            ‖∑ n ∈ Finset.Icc 1 N, f n‖ =
                ‖∑ k ∈ Finset.range N, f (1 + k)‖ := by rw [hsumIcc_eq_range N]
            _ ≤ (q : ℝ) := by
              simpa [f] using
                (FractionalPrimes.Literature.Twisted.evalInt_sum_range_norm_le_modulus
                  χ 1 (Nat.le_of_lt hNq))
        · have hqN : q ≤ N := by omega
          have hblock : (∑ k ∈ Finset.range q, f (N - q + 1 + k)) = 0 := by
            simpa [f] using
              (nonprincipalCharacter_sum_one_period χ hχ (N - q + 1))
          have hrec : (∑ n ∈ Finset.Icc 1 N, f n) =
              ∑ n ∈ Finset.Icc 1 (N - q), f n := by
            rw [hsplit N hqN, hblock, add_zero]
          have hlt : N - q < N := Nat.sub_lt (by omega) hqpos
          calc
            ‖∑ n ∈ Finset.Icc 1 N, f n‖ =
                ‖∑ n ∈ Finset.Icc 1 (N - q), f n‖ := by rw [hrec]
            _ ≤ (q : ℝ) := ih (N - q) hlt
  simpa [continuedDirichletPartialSum, f] using hbound (Nat.floor u)

/-- The blueprint's `I(s) = ∫₁∞ {u}u^(-s-1)du`, on `Re(s) > 0`.
Its value reuses the checked Mellin integral representation. -/
def continuedDirichletI (s : ℂ) (_hs : 0 < s.re) : ℂ :=
  zetaFloorCorrectionIntegral s

/-- The nonsingular regular part `H₀(s)` from `lrc:dirichlet-data`.
The formula is also defined at `s = 1`, as in the blueprint. -/
def continuedDirichletH0 (s : ℂ) (hs : 0 < s.re) : ℂ :=
  s / (s + 1) - (s * (s - 1) / (s + 1)) * continuedDirichletI s hs

/-- The continuation `Z(s) = s/(s-1) - s I(s)`, with the pole excluded. -/
def continuedDirichletZ (s : ℂ) (hs : 0 < s.re) (_hs1 : s ≠ 1) : ℂ :=
  s / (s - 1) - s * continuedDirichletI s hs

/-- Mathlib's complex power on a positive real base is exponentiation using
the real logarithm, as required by the blueprint's convention. -/
theorem continuedComplexPower_eq_exp_realLog {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = Complex.exp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.ofReal_log hx.le]
  congr 1
  ring

/-- The nonprincipal branch of the continued Dirichlet function, exactly the
partial-sum integral in `lrc:dirichlet-data`. -/
def nonprincipalContinuedDirichletL {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q)
    (_hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    (s : ℂ) (_hs : 0 < s.re) : ℂ :=
  s * ∫ t : ℝ in Ioi (1 : ℝ),
    continuedDirichletPartialSumFormula χ t * (t : ℂ) ^ (-(s + 1))

/-- The principal branch of the continued Dirichlet function, with the pole
excluded and the finite Euler factors indexed by the prime divisors of `q`. -/
def principalContinuedDirichletL {q : ℕ} [NeZero q] (s : ℂ) (hs : 0 < s.re)
    (hs1 : s ≠ 1) : ℂ :=
  continuedDirichletZ s hs hs1 *
    ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))

/-- The two approved branches, with only the principal pole excluded. -/
def continuedDirichletL {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (s : ℂ) (hs : 0 < s.re)
    (hnotpole : ¬ (χ = FractionalPrimes.Literature.Twisted.principalCharacter q ∧ s = 1)) : ℂ :=
  if hχ : χ = FractionalPrimes.Literature.Twisted.principalCharacter q then
    principalContinuedDirichletL (q := q) s hs (by
      intro hs1
      exact hnotpole ⟨hχ, hs1⟩)
  else
    nonprincipalContinuedDirichletL χ hχ s hs

theorem continuedDirichletPartialSum_eq_formula {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (u : ℝ) (hu : 1 ≤ u) :
    continuedDirichletPartialSum χ u hu = continuedDirichletPartialSumFormula χ u := rfl

/-- The checked zeta-floor integral is the blueprint's fractional-part integral. -/
theorem continuedDirichletI_eq_integral (s : ℂ) (hs : 0 < s.re) :
    continuedDirichletI s hs =
      ∫ t : ℝ in Ioi (1 : ℝ),
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  exact zetaFloorCorrectionIntegral_eq_setIntegral s

/-- The approved nonsingular formula fixes `H₀(1) = 1/2`. -/
theorem continuedDirichletH0_one :
    continuedDirichletH0 1 (by norm_num : 0 < (1 : ℂ).re) = (1 / 2 : ℂ) := by
  norm_num [continuedDirichletH0, continuedDirichletI]

/-- Away from `s = 1`, `H₀` and `Z` have the exact algebraic relation in the
reciprocal-closure source. -/
theorem continuedDirichletH0_eq_mul_Z {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    continuedDirichletH0 s hs = ((s - 1) / (s + 1)) * continuedDirichletZ s hs hs1 := by
  have hsplus : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  unfold continuedDirichletH0 continuedDirichletZ
  field_simp [hs1, hsplus]

end FractionalPrimes.Literature.Reciprocal

end
