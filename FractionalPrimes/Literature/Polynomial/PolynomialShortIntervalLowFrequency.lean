module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalVariationAdapter
public import FractionalPrimes.Literature.Uniformity.ArchimedeanTwistVariation
public import FractionalPrimes.Literature.Uniformity.ENNRealVariationProduct

/-!
# Low-frequency untwisting for the polynomial short-interval reduction

This is the discrete low-frequency step in the proof of
`lupo:conditional-integer`: remove the archimedean twist from a Type-II
variation bound, then apply the exact residue-prefix Abel estimate.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open scoped BigOperators ENNReal

noncomputable section

private theorem lowFrequencyInterval_points_eq_Ioc
    (X H : ℕ) (hH : 0 < H) :
    (residuePrefixFiniteInterval X H).points =
      Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) := by
  have hprog := arithmeticProgressionPoints_eq_Ioc_filter_modEq
    ((X : ℤ) + 1) 1 (by norm_num) H hH
  have hleft : ((X : ℤ) + 1) - 1 = (X : ℤ) := by omega
  have hright : ((X : ℤ) + 1) + ((H - 1 : ℕ) : ℤ) * (1 : ℤ) =
      ((X + H : ℕ) : ℤ) := by
    have hH' : H - 1 + 1 = H := Nat.sub_add_cancel (by omega)
    norm_cast
    omega
  have hright' : ((X : ℤ) + 1) + ((H - 1 : ℕ) : ℤ) =
      ((X + H : ℕ) : ℤ) := by
    simpa using hright
  rw [show (residuePrefixFiniteInterval X H).points =
      arithmeticProgressionPoints ((X : ℤ) + 1) 1 (by norm_num) H by rfl]
  rw [hprog, hleft]
  simp only [Int.natCast_one, mul_one]
  rw [hright']
  ext n
  simp [Int.ModEq]

private theorem lowFrequencyInterval_as_set
    (X H : ℕ) (hH : 0 < H) :
    ((residuePrefixFiniteInterval X H).points : Set ℤ) =
      logPhaseIntegerInterval (X : ℝ) (H : ℝ) := by
  ext n
  rw [lowFrequencyInterval_points_eq_Ioc X H hH]
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Ioc,
    logPhaseIntegerInterval]
  constructor
  · rintro ⟨hn₁, hn₂⟩
    exact ⟨by exact_mod_cast hn₁, by exact_mod_cast hn₂⟩
  · rintro ⟨hn₁, hn₂⟩
    exact ⟨by exact_mod_cast hn₁, by exact_mod_cast hn₂⟩

private theorem archimedeanTwist_neg_mul_eq_one (T x : ℝ) :
    archimedeanTwist (-T) x * archimedeanTwist T x = 1 := by
  unfold archimedeanTwist
  rw [← Complex.exp_add]
  have harg : Complex.I * ((-T : ℝ) : ℂ) * (Real.log x : ℂ) +
      Complex.I * (T : ℂ) * (Real.log x : ℂ) = 0 := by
    push_cast
    ring
  rw [harg, Complex.exp_zero]

/-- The exact low-frequency Type-II branch of the polynomial short-interval
argument.  From the twisted residue variation bound at level `L^E` and
`|T| < (X/H)L^(50a)`, it removes the twist and bounds the original weighted
sum by the residue-prefix envelope times `L^(2E+50a+1)`.  The interval is
exactly `(X,X+H]`; the conclusion is the one used with the polynomial major
arc task in `lupo:conditional-integer`. -/
theorem lowFrequencyTypeII_residuePrefixBound
    (X H : ℕ) (E a : ℕ) (L T : ℝ) (q : ℕ)
    (hX : 3 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hL : 2 ≤ L) (hEa : E < a) (hq : 0 < q)
    (hqBound : (q : ℝ) ≤ L ^ E)
    (hTlow : |T| < (X : ℝ) / (H : ℝ) * L ^ (50 * a))
    (g w : ℤ → ℂ)
    (hTwisted :
      residueClassTotalVariation (logPhaseIntegerInterval (X : ℝ) (H : ℝ))
        (fun n => g n * archimedeanTwist (-T) (n : ℝ)) q hq ≤
          ENNReal.ofReal (L ^ E)) :
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n * g n‖ ≤
      residuePrefixEnvelope X H w (L ^ a) * L ^ (2 * E + 50 * a + 1) := by
  classical
  let I := residuePrefixFiniteInterval X H
  let Pset := logPhaseIntegerInterval (X : ℝ) (H : ℝ)
  have hXpos : (1 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast hH
  have hHXreal : (H : ℝ) ≤ (X : ℝ) := by exact_mod_cast hHX
  have hIoc := lowFrequencyInterval_points_eq_Ioc X H (by omega)
  have hP : ∀ n ∈ I.points,
      (X : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (X : ℝ) + (H : ℝ) := by
    intro n hn
    have hnIoc : n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) := by
      rw [← hIoc]
      simpa [I] using hn
    rcases Finset.mem_Ioc.mp hnIoc with ⟨hn₁, hn₂⟩
    exact ⟨by exact_mod_cast hn₁, by exact_mod_cast hn₂⟩
  have hTwistFinite := residueClassTotalVariation_archimedeanTwist_le
    (T := T) hXpos hHpos hHXreal I.points I.points_isFiniteArithmeticProgression
      hP q hq
  have hTwist : residueClassTotalVariation Pset
      (fun n => archimedeanTwist T (n : ℝ)) q hq ≤
        ENNReal.ofReal ((q : ℝ) *
          (1 + |T| * (H : ℝ) / (X : ℝ))) := by
    rw [show Pset = (I.points : Set ℤ) from by
      simpa [I, Pset] using (lowFrequencyInterval_as_set X H (by omega)).symm]
    simpa [I] using hTwistFinite
  have hmul : |T| * (H : ℝ) < (X : ℝ) * L ^ (50 * a) := by
    calc
      |T| * (H : ℝ) <
          ((X : ℝ) / (H : ℝ) * L ^ (50 * a)) * (H : ℝ) :=
        mul_lt_mul_of_pos_right hTlow hHpos
      _ = (X : ℝ) * L ^ (50 * a) := by
        field_simp [ne_of_gt hHpos]
  have hTnormalized : |T| * (H : ℝ) / (X : ℝ) < L ^ (50 * a) := by
    exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (X : ℝ))).2 <| by
      simpa [mul_comm] using hmul
  have hpowOne : 1 ≤ L ^ (50 * a) := one_le_pow₀ (by linarith : (1 : ℝ) ≤ L)
  have hsmallFactor :
      1 + |T| * (H : ℝ) / (X : ℝ) ≤ 2 * L ^ (50 * a) := by
    linarith [hTnormalized]
  have harchFactor :
      (q : ℝ) * (1 + |T| * (H : ℝ) / (X : ℝ)) ≤
        2 * L ^ (E + 50 * a) := by
    calc
      _ ≤ L ^ E * (1 + |T| * (H : ℝ) / (X : ℝ)) :=
        mul_le_mul_of_nonneg_right hqBound (by positivity)
      _ ≤ L ^ E * (2 * L ^ (50 * a)) :=
        mul_le_mul_of_nonneg_left hsmallFactor (by positivity)
      _ = 2 * L ^ (E + 50 * a) := by
        rw [pow_add]
        ring
  have hTwistBound : residueClassTotalVariation Pset
      (fun n => archimedeanTwist T (n : ℝ)) q hq ≤
        ENNReal.ofReal (2 * L ^ (E + 50 * a)) :=
    hTwist.trans (ENNReal.ofReal_le_ofReal harchFactor)
  have hcancel : ∀ n : ℤ,
      archimedeanTwist (-T) (n : ℝ) * archimedeanTwist T (n : ℝ) = 1 :=
    fun n => archimedeanTwist_neg_mul_eq_one T (n : ℝ)
  have hfactor : (fun n : ℤ => g n) =
      (fun n => (g n * archimedeanTwist (-T) (n : ℝ)) *
        archimedeanTwist T (n : ℝ)) := by
    funext n
    calc
      g n = g n * 1 := by ring
      _ = g n * (archimedeanTwist (-T) (n : ℝ) *
          archimedeanTwist T (n : ℝ)) := by rw [hcancel n]
      _ = (g n * archimedeanTwist (-T) (n : ℝ)) *
          archimedeanTwist T (n : ℝ) := by ring
  have hvariation : residueClassTotalVariation Pset g q hq ≤
      residueClassTotalVariation Pset
        (fun n => g n * archimedeanTwist (-T) (n : ℝ)) q hq *
      residueClassTotalVariation Pset
        (fun n => archimedeanTwist T (n : ℝ)) q hq := by
    calc
      residueClassTotalVariation Pset g q hq =
          residueClassTotalVariation Pset
            (fun n => (g n * archimedeanTwist (-T) (n : ℝ)) *
              archimedeanTwist T (n : ℝ)) q hq := by
        congr 1
      _ ≤ residueClassTotalVariation Pset
            (fun n => g n * archimedeanTwist (-T) (n : ℝ)) q hq *
          residueClassTotalVariation Pset
            (fun n => archimedeanTwist T (n : ℝ)) q hq :=
        residueClassTotalVariation_mul_le Pset
          (fun n => g n * archimedeanTwist (-T) (n : ℝ))
          (fun n => archimedeanTwist T (n : ℝ)) q hq
  let m := 2 * E + 50 * a
  have hTV : residueClassTotalVariation Pset g q hq ≤
      ENNReal.ofReal (2 * L ^ m) := by
    calc
      _ ≤ residueClassTotalVariation Pset
          (fun n => g n * archimedeanTwist (-T) (n : ℝ)) q hq *
          residueClassTotalVariation Pset
            (fun n => archimedeanTwist T (n : ℝ)) q hq := hvariation
      _ ≤ ENNReal.ofReal (L ^ E) *
          ENNReal.ofReal (2 * L ^ (E + 50 * a)) :=
        mul_le_mul hTwisted hTwistBound (by simp) (by simp)
      _ = ENNReal.ofReal (2 * L ^ m) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ E)]
        congr 1
        dsimp [m]
        rw [pow_add]
        ring
  have htwoPow : 2 * L ^ m ≤ L ^ (m + 1) := by
    calc
      2 * L ^ m ≤ L * L ^ m := by
        have hmnonneg : 0 ≤ L ^ m := by positivity
        nlinarith [hL]
      _ = L ^ (m + 1) := by rw [pow_succ]; ring
  have hTVfinal : residueClassTotalVariation Pset g q hq ≤
      ENNReal.ofReal (L ^ (m + 1)) :=
    hTV.trans (ENNReal.ofReal_le_ofReal htwoPow)
  have hpoints : ∀ n ∈ I.points, n ∈ Pset := by
    intro n hn
    change n ∈ logPhaseIntegerInterval (X : ℝ) (H : ℝ)
    rw [← lowFrequencyInterval_as_set X H (by omega)]
    simpa [I] using hn
  have hfiniteENN : ENNReal.ofReal (finiteResidueClassVariation I g q) ≤
      ENNReal.ofReal (L ^ (m + 1)) :=
    (finiteResidueClassVariation_le_of_subset I Pset g q hq hpoints).trans hTVfinal
  have hfinite : finiteResidueClassVariation I g q ≤ L ^ (m + 1) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfiniteENN
  have hpowMono : L ^ E ≤ L ^ a :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ L) (Nat.le_of_lt hEa)
  have hqQ : (q : ℝ) ≤ L ^ a := hqBound.trans hpowMono
  have htest := testByResiduePrefixes q X H (L ^ a) w g hq
    (by omega : 0 < X) hH hqQ
  have hEnv : 0 ≤ residuePrefixEnvelope X H w (L ^ a) := by
    unfold residuePrefixEnvelope
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  calc
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n * g n‖ ≤
        residuePrefixEnvelope X H w (L ^ a) *
          finiteResidueClassVariation I g q := by
      simpa [I] using htest
    _ ≤ residuePrefixEnvelope X H w (L ^ a) * L ^ (m + 1) :=
      mul_le_mul_of_nonneg_left hfinite hEnv
    _ = _ := by
      simp [m]

end

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.lowFrequencyTypeII_residuePrefixBound
