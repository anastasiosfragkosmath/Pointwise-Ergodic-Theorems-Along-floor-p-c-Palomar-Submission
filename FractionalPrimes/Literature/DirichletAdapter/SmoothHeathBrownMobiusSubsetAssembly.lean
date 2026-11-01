module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownSmallGroupData
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownMobiusMUFShortInterval
public import Mathlib.Tactic
@[expose] public section

/-!
# Selected Möbius factor in the finite small-group assembly

This file instantiates the checked subset assembly with the selected-factor
short-interval estimate obtained from `MobiusUniformity`. It retains the
assembly's exact `2^11 * 5^19` factor and the source `K + 4` saving; an
explicitly enlarged threshold absorbs that fixed factor into `log X`. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Twisted

/-- Insert the MUF-selected Möbius short-interval estimate into the actual
smooth Heath--Brown subset assembly. The first conjunct records the exact
finite factor and exponent `K+4`; the second uses only the displayed
logarithmic threshold, incorporated into `X₀`. The selected tag is required
to be Möbius, while all other factor masses and supports are discharged by
the existing finite assembly. -/
theorem smoothHeathBrownMobiusSubsetAssembly_from_MUF
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
        {b : ℕ} → b < q → (t : ℝ) → |t| ≤ X →
        (ω : Fin fs.length → ℕ → ℂ) →
        (hω : ∀ i n, ‖ω i n‖ ≤ 1) →
        (hωselected : ∀ n,
          ω selected n = smoothHeathBrownMobiusResiduePhaseWeight q b t n) →
        (hMrange : ∀ M : ℝ,
          (M = smoothHeathBrownFactorScale (.mobius j) / 2 ∨
            M = smoothHeathBrownFactorScale (.mobius j)) →
          X ^ (1 / 400 : ℝ) ≤ M ∧ M ≤ X) →
        L = (2 : ℝ) ^ h *
          (∏ i ∈ I, smoothHeathBrownFactorScale (fs.get i)) →
        -(I.card : ℤ) ≤ h ∧ h < (I.card : ℤ) →
        0 ≤ x → x ≤ y →
          ‖smoothGroupSubsetConvolutionSum I
              (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
              (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
                (fs.get i) (ω i) n)
              x y‖ ≤
            (2 : ℝ) ^ 11 * 5 ^ 19 *
                (3 * Cμ * (Real.log X) ^ (-(K + 4))) * Real.sqrt L ∧
          ‖smoothGroupSubsetConvolutionSum I
              (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
              (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
                (fs.get i) (ω i) n)
              x y‖ ≤ (Real.log X) ^ (-K) * Real.sqrt L := by
  have hκ : 0 < K + 4 := by linarith
  obtain ⟨Cμ, Xμ, hCμ, hXμthree, hshort⟩ :=
    smoothHeathBrownMobiusResidueFactor_shortInterval_of_MUF
      hMUF (B := B) (κ := K + 4) hB hκ
  let T : ℝ := (2 : ℝ) ^ 11 * 5 ^ 19 * 3 * Cμ
  let Xlog : ℝ := Real.exp (T + 1)
  let X₀ : ℝ := max Xμ Xlog
  have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
  have hX₀three : 3 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans hXμthree (le_max_left Xμ Xlog)
  refine ⟨Cμ, X₀, hCμ, hX₀three, ?_⟩
  intro X z hX₀X hz fs I selected j htag hselected hcount h L x y
    q hq hqlog b hb t ht ω hω hωselected hMrange hL hh hx hxy
  have hXμX : Xμ ≤ X :=
    le_trans (le_max_left Xμ Xlog) hX₀X
  have hXlogX : Xlog ≤ X :=
    le_trans (le_max_right Xμ Xlog) hX₀X
  have hXthree : 3 ≤ X := le_trans hX₀three hX₀X
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hloglower : T + 1 ≤ Real.log X := by
    calc
      T + 1 = Real.log Xlog := by simp [Xlog]
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos _) hXlogX
  have hlogone : 1 ≤ Real.log X := by linarith [hTnonneg]
  have hTlelog : T ≤ Real.log X := by linarith
  have hloglepow : Real.log X ≤ (Real.log X) ^ 4 := by
    calc
      Real.log X = Real.log X * 1 := by ring
      _ ≤ Real.log X * (Real.log X) ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogone) hlogpos.le
      _ = (Real.log X) ^ 4 := by ring
  have hTlepow : T ≤ (Real.log X) ^ 4 := le_trans hTlelog hloglepow
  have hrpowNat :
      (Real.log X) ^ (4 : ℝ) = (Real.log X) ^ (4 : ℕ) :=
    Real.rpow_natCast _ _
  have hlogpowneg :
      (Real.log X) ^ (-4 : ℝ) = ((Real.log X) ^ 4)⁻¹ := by
    calc
      (Real.log X) ^ (-4 : ℝ) =
          ((Real.log X) ^ (4 : ℝ))⁻¹ := Real.rpow_neg hlogpos.le (4 : ℝ)
      _ = ((Real.log X) ^ 4)⁻¹ := by rw [hrpowNat]
  have hAbsorb : T * (Real.log X) ^ (-4 : ℝ) ≤ 1 := by
    rw [hlogpowneg]
    calc
      T * ((Real.log X) ^ 4)⁻¹ = T / (Real.log X) ^ 4 := by
        rw [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one (by positivity)).2 hTlepow
  let ε : ℝ := 3 * Cμ * (Real.log X) ^ (-(K + 4))
  have hε : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hωselectedFun :
      ω selected = smoothHeathBrownMobiusResiduePhaseWeight q b t :=
    funext hωselected
  have hShort : ∀ M : ℝ,
      (M = smoothHeathBrownFactorScale (fs.get selected) / 2 ∨
        M = smoothHeathBrownFactorScale (fs.get selected)) →
      ∀ u v : ℝ, 0 ≤ u → Set.Ioc u v ⊆ Set.Ioc M (2 * M) →
        ‖∑ n ∈ factorExtractionRealInterval u v,
          smoothHeathBrownWeightedFactorCoefficient (z := z)
            (fs.get selected) (ω selected) n‖ ≤ ε * Real.sqrt M := by
    intro M hM u v hu hI
    have hM' :
        M = smoothHeathBrownFactorScale (.mobius j) / 2 ∨
          M = smoothHeathBrownFactorScale (.mobius j) := by
      rw [htag] at hM
      exact hM
    have hMrange := hMrange M hM'
    have hbound := hshort hXμX hMrange.1 hMrange.2 j hq hqlog hb t ht hz hu hI
    rw [htag]
    have hsum :
        (∑ n ∈ factorExtractionRealInterval u v,
          smoothHeathBrownWeightedFactorCoefficient (z := z) (.mobius j)
            (ω selected) n) =
          ∑ n ∈ factorExtractionRealInterval u v,
            smoothHeathBrownWeightedFactorCoefficient (z := z) (.mobius j)
              (smoothHeathBrownMobiusResiduePhaseWeight q b t) n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hωselectedFun]
    rw [hsum]
    calc
      _ ≤ 3 * Cμ * Real.sqrt M * (Real.log X) ^ (-(K + 4)) := hbound
      _ = ε * Real.sqrt M := by dsimp [ε]; ring
  have hfinite := smoothHeathBrownSubsetWideSupportFiniteTransfer
    hXthree fs I selected hselected hcount h L ε x y ω hL hh hε hx hxy hω hShort
  have hraw :
      ‖smoothGroupSubsetConvolutionSum I
          (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
          (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
            (fs.get i) (ω i) n)
          x y‖ ≤
        (2 : ℝ) ^ 11 * 5 ^ 19 *
          (3 * Cμ * (Real.log X) ^ (-(K + 4))) * Real.sqrt L := by
    simpa [ε] using hfinite
  have hlogsplit :
      (Real.log X) ^ (-(K + 4)) =
        (Real.log X) ^ (-K) * (Real.log X) ^ (-4 : ℝ) := by
    rw [show -(K + 4) = (-K) + (-4 : ℝ) by ring,
      Real.rpow_add hlogpos]
  have hscalar :
      (2 : ℝ) ^ 11 * 5 ^ 19 *
          (3 * Cμ * (Real.log X) ^ (-(K + 4))) ≤
        (Real.log X) ^ (-K) := by
    rw [hlogsplit]
    calc
      (2 : ℝ) ^ 11 * 5 ^ 19 *
          (3 * Cμ * ((Real.log X) ^ (-K) * (Real.log X) ^ (-4 : ℝ))) =
        (T * (Real.log X) ^ (-4 : ℝ)) * (Real.log X) ^ (-K) := by
          dsimp [T]
          ring
      _ ≤ 1 * (Real.log X) ^ (-K) :=
        mul_le_mul_of_nonneg_right hAbsorb
          (Real.rpow_nonneg hlogpos.le _)
      _ = (Real.log X) ^ (-K) := by ring
  have hfinal :
      ‖smoothGroupSubsetConvolutionSum I
          (fun i => smoothHeathBrownFactorFiniteSupport (fs.get i))
          (fun i n => smoothHeathBrownWeightedFactorCoefficient (z := z)
            (fs.get i) (ω i) n)
          x y‖ ≤ (Real.log X) ^ (-K) * Real.sqrt L := by
    calc
      _ ≤ (2 : ℝ) ^ 11 * 5 ^ 19 *
          (3 * Cμ * (Real.log X) ^ (-(K + 4))) * Real.sqrt L := hraw
      _ ≤ (Real.log X) ^ (-K) * Real.sqrt L :=
        mul_le_mul_of_nonneg_right hscalar (Real.sqrt_nonneg L)
  exact ⟨hraw, hfinal⟩

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusSubsetAssembly_from_MUF
