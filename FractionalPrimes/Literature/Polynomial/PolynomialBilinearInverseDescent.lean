module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseSecondRecurrence

/-!
# Descending coefficient state for the bilinear polynomial inverse theorem

The source proof descends through `j=d,d-1,...,2`.  This file packages the
finite invariant and its exact multiplier update.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The multiplicative loss at each second-recurrence step. -/
def bilinearInverseDescentFactor (d : ℕ) (ρ : ℝ) : ℝ :=
  bilinearInverseVTwo d ρ⁻¹ * (bilinearInverseCValue d : ℝ) *
    bilinearInverseA d ρ⁻¹

theorem bilinearInverseDescentFactor_ge_one
    (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    1 ≤ bilinearInverseDescentFactor d ρ := by
  have hx : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  rcases bilinearInverseBudget_values d hd ρ⁻¹ hx with
    ⟨hB, hZOne, hVOne, hA, hZTwo, hVTwo, hC, hE, hZ⟩
  dsimp [bilinearInverseDescentFactor]
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith) hC) hA

theorem bilinearInverseVTwo_le_descentFactor
    (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    bilinearInverseVTwo d ρ⁻¹ ≤ bilinearInverseDescentFactor d ρ := by
  have hx : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  rcases bilinearInverseBudget_values d hd ρ⁻¹ hx with
    ⟨hB, hZOne, hVOne, hA, hZTwo, hVTwo, hC, hE, hZ⟩
  have hV0 : 0 ≤ bilinearInverseVTwo d ρ⁻¹ := by linarith
  dsimp [bilinearInverseDescentFactor]
  calc
    bilinearInverseVTwo d ρ⁻¹ =
        bilinearInverseVTwo d ρ⁻¹ * 1 * 1 := by ring
    _ ≤ bilinearInverseVTwo d ρ⁻¹ *
          (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ := by
      gcongr

/-- After all `d-1` steps the iterated loss is exactly the source budget
`E`, up to commutativity of its three factors. -/
theorem bilinearInverseDescentFactor_pow_eq_E
    (d : ℕ) (ρ : ℝ) :
    bilinearInverseDescentFactor d ρ ^ (d - 1) =
      bilinearInverseE d ρ⁻¹ := by
  rw [bilinearInverseE_eval]
  congr 1
  dsimp [bilinearInverseDescentFactor]
  ring

/-- At degree `j`, every coefficient strictly above `j` is controlled with
the loss accumulated in `step` recurrence updates. -/
structure BilinearInverseDescentState
    (d j step q₀ : ℕ) (X H ρ : ℝ) (coeff : ℕ → ℝ) where
  t : ℕ
  t_pos : 1 ≤ t
  t_upper : (t : ℝ) ≤ bilinearInverseDescentFactor d ρ ^ step
  higher_error : ∀ i ∈ Finset.Icc (j + 1) d,
    realDistanceToIntegers (((t * q₀ : ℕ) : ℝ) * coeff i) ≤
      bilinearInverseDescentFactor d ρ ^ step * X / H ^ (i + 1)

/-- The descent begins at the top degree with multiplier one and an empty set
of already-treated coefficients. -/
def bilinearInverseDescentState_initial
    (d q₀ : ℕ) (X H ρ : ℝ) (coeff : ℕ → ℝ) :
    BilinearInverseDescentState d d 0 q₀ X H ρ coeff := by
  refine
    { t := 1
      t_pos := by norm_num
      t_upper := by norm_num
      higher_error := ?_ }
  intro i hi
  simp only [Finset.mem_Icc] at hi
  omega

/-- Multiplication by the recurrence output preserves all previously treated
coefficients and adds the current degree to the invariant. -/
def BilinearInverseDescentState.mulSecondRecurrence
    {d j step q₀ : ℕ} {X H ρ : ℝ} {coeff : ℕ → ℝ}
    (state : BilinearInverseDescentState d j step q₀ X H ρ coeff)
    (hd : 1 ≤ d) (hj : 2 ≤ j) (hjd : j ≤ d)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (hX : 0 ≤ X) (hH : 0 < H)
    (b : ℕ) (hb : 1 ≤ b)
    (hbV : (b : ℝ) ≤ bilinearInverseVTwo d ρ⁻¹)
    (hnew :
      realDistanceToIntegers
          ((b : ℝ) * (((state.t * q₀ : ℕ) : ℝ) * coeff j)) ≤
        bilinearInverseDescentFactor d ρ ^ (step + 1) *
          X / H ^ (j + 1)) :
    BilinearInverseDescentState d (j - 1) (step + 1) q₀ X H ρ coeff := by
  let t' : ℕ := b * state.t
  have hfactorOne :=
    bilinearInverseDescentFactor_ge_one d hd ρ hρ hρhalf
  have hfactor0 : 0 ≤ bilinearInverseDescentFactor d ρ := by linarith
  have hbFactor : (b : ℝ) ≤ bilinearInverseDescentFactor d ρ :=
    hbV.trans (bilinearInverseVTwo_le_descentFactor d hd ρ hρ hρhalf)
  have htUpper :
      (t' : ℝ) ≤ bilinearInverseDescentFactor d ρ ^ (step + 1) := by
    calc
      (t' : ℝ) = (b : ℝ) * (state.t : ℝ) := by simp [t']
      _ ≤ bilinearInverseDescentFactor d ρ *
          bilinearInverseDescentFactor d ρ ^ step :=
        mul_le_mul hbFactor state.t_upper (Nat.cast_nonneg _) hfactor0
      _ = bilinearInverseDescentFactor d ρ ^ (step + 1) := by
        rw [pow_succ]
        ring
  refine
    { t := t'
      t_pos := Nat.mul_pos hb state.t_pos
      t_upper := htUpper
      higher_error := ?_ }
  intro i hi
  have hiRange : j ≤ i ∧ i ≤ d := by
    simp only [Finset.mem_Icc] at hi
    omega
  by_cases hij : i = j
  · subst i
    simpa [t', Nat.cast_mul, mul_assoc] using hnew
  · have hiOld : i ∈ Finset.Icc (j + 1) d := by
      simp only [Finset.mem_Icc]
      omega
    have hdist := realDistanceToIntegers_int_mul_le (b : ℤ)
      (((state.t * q₀ : ℕ) : ℝ) * coeff i)
    have hscale0 : 0 ≤
        bilinearInverseDescentFactor d ρ ^ step * X / H ^ (i + 1) := by
      positivity
    have harg :
        (((t' * q₀ : ℕ) : ℝ) * coeff i) =
          (b : ℝ) * (((state.t * q₀ : ℕ) : ℝ) * coeff i) := by
      dsimp [t']
      push_cast
      ring
    calc
      realDistanceToIntegers (((t' * q₀ : ℕ) : ℝ) * coeff i) =
          realDistanceToIntegers
            ((b : ℝ) * (((state.t * q₀ : ℕ) : ℝ) * coeff i)) := by
        rw [harg]
      _ ≤ |(b : ℝ)| * realDistanceToIntegers
          (((state.t * q₀ : ℕ) : ℝ) * coeff i) := hdist
      _ = (b : ℝ) * realDistanceToIntegers
          (((state.t * q₀ : ℕ) : ℝ) * coeff i) := by
        rw [abs_of_nonneg (Nat.cast_nonneg b)]
      _ ≤ (b : ℝ) *
          (bilinearInverseDescentFactor d ρ ^ step * X / H ^ (i + 1)) :=
        mul_le_mul_of_nonneg_left (state.higher_error i hiOld)
          (Nat.cast_nonneg b)
      _ ≤ bilinearInverseDescentFactor d ρ *
          (bilinearInverseDescentFactor d ρ ^ step * X / H ^ (i + 1)) :=
        mul_le_mul_of_nonneg_right hbFactor hscale0
      _ = bilinearInverseDescentFactor d ρ ^ (step + 1) *
          X / H ^ (i + 1) := by
        rw [pow_succ]
        ring

/-- One complete source-specific descent step: formula (B3) holds on every
selected centre, polynomial recurrence chooses `b`, and the finite state is
updated from degree `j` to degree `j-1`. -/
theorem bilinearInverseDescent_step
    (d j step q₀ : ℕ) (hd : 1 ≤ d) (hj : 2 ≤ j) (hjd : j ≤ d)
    (hstep : step ≤ d - 1)
    (X H L M ρ : ℝ)
    (hL : 0 < L) (hM : 1 ≤ M) (hH : 0 < H)
    (hX : X = L * M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (hZr : bilinearInverseZ d ρ⁻¹ ≤ H / L)
    (hZs : bilinearInverseZ d ρ⁻¹ ≤ H / M)
    (hrM : H / L ≤ M)
    (ν : ℕ → ℝ) (hνtop : ν (d + 1) = 0)
    (ell0 : ℕ → ℤ)
    (U : Finset ℕ)
    (hUrange : U ⊆ Finset.Icc 1 (bilinearSecondRecurrenceLength M))
    (hUcard :
      2 * (bilinearInverseZTwo d ρ⁻¹)⁻¹ *
          (bilinearSecondRecurrenceLength M : ℝ) ≤ (U.card : ℝ))
    (hUupper : ∀ u ∈ U, (u : ℝ) ≤ 2 * M)
    (hoffset : ∀ u ∈ U, ∃ h0 : ℤ,
      (ell0 u : ℝ) * (u : ℝ) - X = (h0 : ℝ) ∧
        |(h0 : ℝ)| ≤ 44 * H)
    (hfirst : ∀ u ∈ U,
      realDistanceToIntegers
          ((q₀ : ℝ) *
            bilinearGammaLinearCoefficient X (ell0 u) d j ν (u : ℝ)) ≤
        bilinearInverseA d ρ⁻¹ * M ^ (j - 1) * X / H ^ (j + 1))
    (state : BilinearInverseDescentState d j step q₀ X H ρ
      (bilinearDerivativeCoefficient X ν)) :
    Nonempty (BilinearInverseDescentState d (j - 1) (step + 1) q₀ X H ρ
      (bilinearDerivativeCoefficient X ν)) := by
  let F : ℝ := bilinearInverseDescentFactor d ρ
  let e : ℝ := F ^ step
  let a : ℝ := ((state.t * q₀ : ℕ) : ℝ) *
    bilinearDerivativeCoefficient X ν j
  have hMpos : 0 < M := by linarith
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hfactorOne : 1 ≤ F := by
    simpa [F] using bilinearInverseDescentFactor_ge_one d hd ρ hρ hρhalf
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hte : (state.t : ℝ) ≤ e := by simpa [e, F] using state.t_upper
  have heE : e ≤ bilinearInverseE d ρ⁻¹ := by
    calc
      e ≤ F ^ (d - 1) := by
        dsimp [e]
        exact pow_le_pow_right₀ hfactorOne hstep
      _ = bilinearInverseE d ρ⁻¹ := by
        simpa [F] using bilinearInverseDescentFactor_pow_eq_E d ρ
  have hx : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hA : 1 ≤ bilinearInverseA d ρ⁻¹ :=
    (bilinearInverseBudget_values d hd ρ⁻¹ hx).2.2.2.1
  have happrox : ∀ u ∈ U,
      realDistanceToIntegers (a * (u : ℝ) ^ (j - 1)) ≤
        (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ * e *
          M ^ (j - 1) * X / H ^ (j + 1) := by
    intro u hu
    obtain ⟨h0, h0eq, h0bound⟩ := hoffset u hu
    have hB3 := bilinearFirstToSecondRecurrence_error
      d j u state.t q₀ X H M (bilinearInverseA d ρ⁻¹) e
      (ell0 u) h0 ν (by omega) hjd hνtop hH hMpos hX0 hA he hte
      (hUupper u hu) h0eq h0bound (hfirst u hu)
      (fun i hi => by simpa [e, F] using state.higher_error i hi)
    calc
      realDistanceToIntegers (a * (u : ℝ) ^ (j - 1)) =
          realDistanceToIntegers
            (((state.t * q₀ : ℕ) : ℝ) * (u : ℝ) ^ (j - 1) *
              bilinearDerivativeCoefficient X ν j) := by
        congr 1
        dsimp [a]
        ring
      _ ≤ (bilinearInverseCValue d : ℝ) *
          bilinearInverseA d ρ⁻¹ * e * M ^ (j - 1) * X /
            H ^ (j + 1) := hB3
  obtain ⟨b, hb, hbV, hberror⟩ :=
    bilinearSecondRecurrence_for_degree d j hd hj hjd X H L M ρ e a
      hL hM hH hX hρ hρhalf hZr hZs hrM he heE U hUrange hUcard happrox
  have hnew :
      realDistanceToIntegers
          ((b : ℝ) *
            (((state.t * q₀ : ℕ) : ℝ) *
              bilinearDerivativeCoefficient X ν j)) ≤
        bilinearInverseDescentFactor d ρ ^ (step + 1) *
          X / H ^ (j + 1) := by
    calc
      realDistanceToIntegers
          ((b : ℝ) *
            (((state.t * q₀ : ℕ) : ℝ) *
              bilinearDerivativeCoefficient X ν j)) =
        realDistanceToIntegers ((b : ℝ) * a) := by rfl
      _ ≤ bilinearInverseVTwo d ρ⁻¹ *
          (bilinearInverseCValue d : ℝ) *
            bilinearInverseA d ρ⁻¹ * e * X / H ^ (j + 1) := hberror
      _ = bilinearInverseDescentFactor d ρ ^ (step + 1) *
          X / H ^ (j + 1) := by
        dsimp [e, F, bilinearInverseDescentFactor]
        rw [pow_succ]
        ring
  exact ⟨state.mulSecondRecurrence hd hj hjd hρ hρhalf hX0 hH b hb hbV hnew⟩

/-- Iterating the checked one-step transition through
`j=d,d-1,...,2` produces the final state at degree one after exactly `d-1`
steps. -/
theorem bilinearInverseDescent_exists_finalState
    (d q₀ : ℕ) (hd : 1 ≤ d)
    (X H L M ρ : ℝ)
    (hL : 0 < L) (hM : 1 ≤ M) (hH : 0 < H)
    (hX : X = L * M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (hZr : bilinearInverseZ d ρ⁻¹ ≤ H / L)
    (hZs : bilinearInverseZ d ρ⁻¹ ≤ H / M)
    (hrM : H / L ≤ M)
    (ν : ℕ → ℝ) (hνtop : ν (d + 1) = 0)
    (ell0 : ℕ → ℤ)
    (U : Finset ℕ)
    (hUrange : U ⊆ Finset.Icc 1 (bilinearSecondRecurrenceLength M))
    (hUcard :
      2 * (bilinearInverseZTwo d ρ⁻¹)⁻¹ *
          (bilinearSecondRecurrenceLength M : ℝ) ≤ (U.card : ℝ))
    (hUupper : ∀ u ∈ U, (u : ℝ) ≤ 2 * M)
    (hoffset : ∀ u ∈ U, ∃ h0 : ℤ,
      (ell0 u : ℝ) * (u : ℝ) - X = (h0 : ℝ) ∧
        |(h0 : ℝ)| ≤ 44 * H)
    (hfirst : ∀ j ∈ Finset.Icc 1 d, ∀ u ∈ U,
      realDistanceToIntegers
          ((q₀ : ℝ) *
            bilinearGammaLinearCoefficient X (ell0 u) d j ν (u : ℝ)) ≤
        bilinearInverseA d ρ⁻¹ * M ^ (j - 1) * X / H ^ (j + 1)) :
    Nonempty (BilinearInverseDescentState d 1 (d - 1) q₀ X H ρ
      (bilinearDerivativeCoefficient X ν)) := by
  have hstates : ∀ k, k ≤ d - 1 →
      Nonempty (BilinearInverseDescentState d (d - k) k q₀ X H ρ
        (bilinearDerivativeCoefficient X ν)) := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa using Nonempty.intro
          (bilinearInverseDescentState_initial d q₀ X H ρ
            (bilinearDerivativeCoefficient X ν))
    | succ k ih =>
        intro hk
        have hk' : k ≤ d - 1 := by omega
        obtain ⟨state⟩ := ih hk'
        have hj : 2 ≤ d - k := by omega
        have hjd : d - k ≤ d := Nat.sub_le d k
        have hcurrent : d - k ∈ Finset.Icc 1 d := by
          exact Finset.mem_Icc.mpr ⟨by omega, hjd⟩
        have hnext := bilinearInverseDescent_step
          d (d - k) k q₀ hd hj hjd hk' X H L M ρ hL hM hH hX
          hρ hρhalf hZr hZs hrM ν hνtop ell0 U hUrange hUcard
          hUupper hoffset (hfirst (d - k) hcurrent) state
        have hdegree : d - (k + 1) = d - k - 1 := by omega
        simpa only [Nat.succ_eq_add_one, hdegree] using hnext
  have hfinal := hstates (d - 1) le_rfl
  have hdegree : d - (d - 1) = 1 := by omega
  simpa [hdegree] using hfinal

/-- The terminal descent state controls every coefficient, including degree
one, where the source proof uses formula (B3) directly at one selected
centre rather than applying recurrence to a constant polynomial. -/
theorem BilinearInverseDescentState.final_coefficients
    {d q₀ : ℕ} (hd : 1 ≤ d)
    {X H M ρ : ℝ} (hM : 1 ≤ M) (hH : 0 < H) (hX : 0 ≤ X)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (ν : ℕ → ℝ) (hνtop : ν (d + 1) = 0)
    (ell0 : ℕ → ℤ)
    (U : Finset ℕ) (hUnonempty : U.Nonempty)
    (hUupper : ∀ u ∈ U, (u : ℝ) ≤ 2 * M)
    (hoffset : ∀ u ∈ U, ∃ h0 : ℤ,
      (ell0 u : ℝ) * (u : ℝ) - X = (h0 : ℝ) ∧
        |(h0 : ℝ)| ≤ 44 * H)
    (hfirstOne : ∀ u ∈ U,
      realDistanceToIntegers
          ((q₀ : ℝ) *
            bilinearGammaLinearCoefficient X (ell0 u) d 1 ν (u : ℝ)) ≤
        bilinearInverseA d ρ⁻¹ * X / H ^ 2)
    (state : BilinearInverseDescentState d 1 (d - 1) q₀ X H ρ
      (bilinearDerivativeCoefficient X ν)) :
    (state.t : ℝ) ≤ bilinearInverseE d ρ⁻¹ ∧
      ∀ i ∈ Finset.Icc 1 d,
        realDistanceToIntegers
            (((state.t * q₀ : ℕ) : ℝ) *
              bilinearDerivativeCoefficient X ν i) ≤
          (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ *
            bilinearInverseE d ρ⁻¹ * X / H ^ (i + 1) := by
  have hfactorE := bilinearInverseDescentFactor_pow_eq_E d ρ
  have htE : (state.t : ℝ) ≤ bilinearInverseE d ρ⁻¹ := by
    calc
      (state.t : ℝ) ≤ bilinearInverseDescentFactor d ρ ^ (d - 1) :=
        state.t_upper
      _ = bilinearInverseE d ρ⁻¹ := hfactorE
  refine ⟨htE, ?_⟩
  have hMpos : 0 < M := by linarith
  have hx : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  rcases bilinearInverseBudget_values d hd ρ⁻¹ hx with
    ⟨hB, hZOne, hVOne, hA, hZTwo, hVTwo, hC, hE, hZ⟩
  have hCA : 1 ≤
      (bilinearInverseCValue d : ℝ) * bilinearInverseA d ρ⁻¹ :=
    one_le_mul_of_one_le_of_one_le hC hA
  obtain ⟨u, hu⟩ := hUnonempty
  obtain ⟨h0, h0eq, h0bound⟩ := hoffset u hu
  have honeB3 := bilinearFirstToSecondRecurrence_error
    d 1 u state.t q₀ X H M (bilinearInverseA d ρ⁻¹)
    (bilinearInverseE d ρ⁻¹) (ell0 u) h0 ν (by omega) hd hνtop
    hH hMpos hX hA (by linarith) htE (hUupper u hu) h0eq h0bound
    (by simpa using hfirstOne u hu)
    (fun i hi => by
      have hstate := state.higher_error i (by simpa using hi)
      simpa [hfactorE] using hstate)
  intro i hi
  have hiData := Finset.mem_Icc.mp hi
  by_cases hiOne : i = 1
  · subst i
    simpa using honeB3
  · have hiHigh : i ∈ Finset.Icc 2 d := by
      exact Finset.mem_Icc.mpr ⟨by omega, hiData.2⟩
    have hstate := state.higher_error i (by simpa using hiHigh)
    have hscale0 : 0 ≤ bilinearInverseE d ρ⁻¹ * X / H ^ (i + 1) := by
      positivity
    calc
      realDistanceToIntegers
          (((state.t * q₀ : ℕ) : ℝ) *
            bilinearDerivativeCoefficient X ν i) ≤
        bilinearInverseDescentFactor d ρ ^ (d - 1) * X /
          H ^ (i + 1) := hstate
      _ = bilinearInverseE d ρ⁻¹ * X / H ^ (i + 1) := by
        rw [hfactorE]
      _ ≤ ((bilinearInverseCValue d : ℝ) *
            bilinearInverseA d ρ⁻¹) *
          (bilinearInverseE d ρ⁻¹ * X / H ^ (i + 1)) := by
        calc
          bilinearInverseE d ρ⁻¹ * X / H ^ (i + 1) =
              1 * (bilinearInverseE d ρ⁻¹ * X / H ^ (i + 1)) := by ring
          _ ≤ ((bilinearInverseCValue d : ℝ) *
                bilinearInverseA d ρ⁻¹) *
              (bilinearInverseE d ρ⁻¹ * X / H ^ (i + 1)) :=
            mul_le_mul_of_nonneg_right hCA hscale0
      _ = (bilinearInverseCValue d : ℝ) *
          bilinearInverseA d ρ⁻¹ * bilinearInverseE d ρ⁻¹ * X /
            H ^ (i + 1) := by ring

#print axioms bilinearInverseDescentFactor_ge_one
#print axioms bilinearInverseVTwo_le_descentFactor
#print axioms bilinearInverseDescentFactor_pow_eq_E
#print axioms bilinearInverseDescentState_initial
#print axioms BilinearInverseDescentState.mulSecondRecurrence
#print axioms bilinearInverseDescent_step
#print axioms bilinearInverseDescent_exists_finalState
#print axioms BilinearInverseDescentState.final_coefficients

end

end FractionalPrimes.Literature.Polynomial
