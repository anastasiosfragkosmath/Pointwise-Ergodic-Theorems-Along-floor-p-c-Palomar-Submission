module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalLocalLargeValues
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The finite partition and packing argument for the separated-family
large-value estimate `lgv:separated`.

Blueprint: `expanded-blueprint.tex:5557-5592`.
Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-large-values.tex:158-201`.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.LargeValues

open scoped BigOperators

private lemma shifted_natFloor_interval (x T S : ℝ) (hS : 0 < S)
    (hx : 0 ≤ (x + T) / S) :
    (Nat.floor ((x + T) / S) : ℝ) * S - T ≤ x ∧
      x ≤ (Nat.floor ((x + T) / S) : ℝ) * S - T + S := by
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one ((x + T) / S)
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hlo hS.le
    have hdiv : ((x + T) / S) * S = x + T := by
      field_simp
    rw [hdiv] at hmul
    linarith
  · have hmul := mul_lt_mul_of_pos_right hhi hS
    have hdiv : ((x + T) / S) * S = x + T := by
      field_simp
    rw [hdiv] at hmul
    linarith

private lemma separated_family_packing (T : ℝ) (R : ℕ) (t : Fin R → ℝ)
    (hT : 0 ≤ T) (htime : ∀ j, -T ≤ t j ∧ t j ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|) :
    (R : ℝ) ≤ 2 * T + 1 := by
  classical
  let point : Fin R → Fin (Nat.floor (2 * T) + 1) := fun j =>
    ⟨Nat.floor (t j + T), by
      have hj := htime j
      have hshift : 0 ≤ t j + T := by linarith
      have hupper : t j + T ≤ 2 * T := by linarith
      have hfloor := Nat.floor_mono hupper
      exact Nat.lt_succ_of_le hfloor⟩
  have hinj : Function.Injective point := by
    intro i j hij
    by_contra hne
    have hfloor : Nat.floor (t i + T) = Nat.floor (t j + T) := by
      exact congrArg Fin.val hij
    have hleft := Nat.floor_le (show 0 ≤ t i + T by linarith [htime i])
    have hright := Nat.lt_floor_add_one (t j + T)
    have hleft' := Nat.floor_le (show 0 ≤ t j + T by linarith [htime j])
    have hright' := Nat.lt_floor_add_one (t i + T)
    have hsmall₁ : t j + T - (t i + T) < 1 := by
      rw [← hfloor] at hright
      linarith
    have hsmall₂ : t i + T - (t j + T) < 1 := by
      rw [hfloor] at hright'
      linarith
    have hdistlt : |t i - t j| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have := hsep i j hne
    linarith
  have hcard : Fintype.card (Fin R) ≤ Fintype.card (Fin (Nat.floor (2 * T) + 1)) :=
    Fintype.card_le_of_injective point hinj
  have hcard' : R ≤ Nat.floor (2 * T) + 1 := by simpa using hcard
  have hcast : (R : ℝ) ≤ (Nat.floor (2 * T) : ℝ) + 1 := by exact_mod_cast hcard'
  have hfloor : (Nat.floor (2 * T) : ℝ) ≤ 2 * T :=
    Nat.floor_le (by positivity)
  exact hcast.trans (by linarith)

private lemma huxley_log_factor (N T : ℝ) (R : ℕ)
    (hN : 2 ≤ N) (hT : 2 ≤ T) (hR : 1 ≤ R)
    (hRbound : (R : ℝ) ≤ 2 * T + 1) :
    1 + 2 * Real.log (R : ℝ) ≤ 3 * Real.log (4 * N * T) := by
  have harg : 0 < 4 * N * T := by positivity
  have hbig : (R : ℝ) ≤ 4 * N * T := by nlinarith
  have hlog : Real.log (R : ℝ) ≤ Real.log (4 * N * T) :=
    Real.log_le_log (by exact_mod_cast hR) hbig
  have hexp : Real.exp 1 < 4 * N * T := by
    have hsmall : Real.exp 1 < 16 := by
      exact lt_of_lt_of_le Real.exp_one_lt_three (by norm_num)
    nlinarith
  have hL : 1 ≤ Real.log (4 * N * T) := by
    apply (Real.le_log_iff_exp_le harg).2
    exact hexp.le
  linarith

private lemma dirichletEnergy_nonneg (N : ℝ) (a : ℕ → ℂ) :
    0 ≤ dirichletEnergy N a := by
  unfold dirichletEnergy
  exact Finset.sum_nonneg fun n _ => sq_nonneg ‖a n‖

/-- The finite Huxley separated-family bound `lgv:separated`. -/
theorem huxleyFiniteBound
    (N T V : ℝ) (a : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hN : 2 ≤ N) (hT : 2 ≤ T) (hV : 0 < V)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (htime : ∀ j, -T ≤ t j ∧ t j ≤ T)
    (hlarge : ∀ j, V ≤ ‖dirichletPolynomial N a (t j)‖) :
    (R : ℝ) ≤ 2 ^ 24 * Real.log (4 * N * T) *
      (N * dirichletEnergy N a / V ^ 2 +
        T * N * (dirichletEnergy N a) ^ 3 / V ^ 6) := by
  classical
  let G : ℝ := dirichletEnergy N a
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    exact dirichletEnergy_nonneg N a
  by_cases hGzero : G = 0
  · have hRzero : R = 0 := by
      by_contra hRne
      have hRpos : 0 < R := Nat.pos_of_ne_zero hRne
      have hcoeffzero (n : ℕ) (hn : n ∈ dirichletIndices N) : a n = 0 := by
        have hsumzero :
            (∑ n ∈ dirichletIndices N, ‖a n‖ ^ 2) = 0 := by
          simpa [G, dirichletEnergy] using hGzero
        have htermzero :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun m _ => sq_nonneg ‖a m‖)).mp hsumzero n hn
        have hnormzero : ‖a n‖ = 0 := by nlinarith [norm_nonneg (a n)]
        exact norm_eq_zero.mp hnormzero
      have hpolyzero (x : ℝ) : dirichletPolynomial N a x = 0 := by
        unfold dirichletPolynomial
        apply Finset.sum_eq_zero
        intro n hn
        simp [dirichletTerm, hcoeffzero n hn]
      let j : Fin R := ⟨0, hRpos⟩
      have hj := hlarge j
      rw [hpolyzero] at hj
      simp at hj
      linarith
    simp [hRzero, hGzero, G]
  · have hGpos : 0 < G := lt_of_le_of_ne hGnonneg (Ne.symm hGzero)
    let S : ℝ := (V ^ 2 / (128 * G)) ^ 2
    have hSpos : 0 < S := by
      dsimp [S]
      positivity
    have hSnonneg : 0 ≤ S := hSpos.le
    have hqpos : 0 < V ^ 2 / (128 * G) := by positivity
    have hsqrtS : Real.sqrt S = V ^ 2 / (128 * G) := by
      dsimp [S]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hqpos]
    let K : ℕ := Nat.floor (2 * T / S) + 1
    let bucket : Fin R → ℕ := fun j => Nat.floor ((t j + T) / S)
    have hKbound : (K : ℝ) ≤ 1 + 2 * T / S := by
      dsimp [K]
      have hfloor := Nat.floor_le (show 0 ≤ 2 * T / S by positivity)
      push_cast
      linarith
    have hbucketRange (j : Fin R) : bucket j < K := by
      dsimp [bucket, K]
      have hj := htime j
      have hratio : (t j + T) / S ≤ 2 * T / S := by
        apply div_le_div_of_nonneg_right _ hSnonneg
        linarith
      exact Nat.lt_succ_of_le (Nat.floor_mono hratio)
    let fiber (b : ℕ) : Finset (Fin R) :=
      Finset.univ.filter fun j => bucket j = b
    have hpacking := separated_family_packing T R t (by linarith) htime hsep
    have hlogfactor (r : ℕ) (hr : 1 ≤ r)
        (hrbound : (r : ℝ) ≤ 2 * T + 1) :
        1 + 2 * Real.log (r : ℝ) ≤ 3 * Real.log (4 * N * T) :=
      huxley_log_factor N T r hN hT hr hrbound
    have hLpos : 0 < Real.log (4 * N * T) := by
      have harg : 0 < 4 * N * T := by positivity
      have hexp : Real.exp 1 < 4 * N * T := by
        have hsmall : Real.exp 1 < 16 := by
          exact lt_of_lt_of_le Real.exp_one_lt_three (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left hT (by linarith : 0 ≤ N)]
      have hone : 1 ≤ Real.log (4 * N * T) :=
        (Real.le_log_iff_exp_le harg).2 hexp.le
      linarith
    let A : ℝ := 384 * N * G * Real.log (4 * N * T) / V ^ 2
    have hAnonneg : 0 ≤ A := by
      dsimp [A]
      positivity
    have hfiberBound (b : ℕ) : (fiber b).card ≤ (A : ℝ) := by
      by_cases hcard : 0 < (fiber b).card
      · let r : ℕ := (fiber b).card
        have hrEq : (fiber b).card = r := by rfl
        let e : Fin r ↪o Fin R := (fiber b).orderEmbOfFin (k := r) hrEq
        let tf : Fin r → ℝ := fun j => t (e j)
        have hRfiber : 1 ≤ r := by dsimp [r]; omega
        have hmem (j : Fin r) : e j ∈ fiber b := by
          exact Finset.orderEmbOfFin_mem (fiber b) hrEq j
        have hbucket (j : Fin r) : bucket (e j) = b := by
          exact (Finset.mem_filter.mp (hmem j)).2
        have hsepFiber : ∀ i j, i ≠ j → 1 ≤ |tf i - tf j| := by
          intro i j hij
          apply hsep (e i) (e j)
          intro heq
          exact hij (e.injective heq)
        have htimeFiber : ∀ j, -T ≤ tf j ∧ tf j ≤ T := by
          intro j
          exact htime (e j)
        have htimeWindow : ∀ j, (b : ℝ) * S - T ≤ tf j ∧
            tf j ≤ (b : ℝ) * S - T + S := by
          intro j
          have hj := htime (e j)
          have hinterval := shifted_natFloor_interval (t (e j)) T S hSpos
            (div_nonneg (by linarith) hSnonneg)
          have hbucketEq : Nat.floor ((t (e j) + T) / S) = b := by
            have hb := hbucket j
            change Nat.floor ((t (e j) + T) / S) = b at hb
            exact hb
          rw [hbucketEq] at hinterval
          simpa [tf] using hinterval
        have hlargeFiber : ∀ j, V ≤ ‖dirichletPolynomial N a (tf j)‖ := by
          intro j
          exact hlarge (e j)
        have hshort : Real.sqrt S ≤ V ^ 2 / (128 * G) := by
          rw [hsqrtS]
        have hlocal := localLargeValueBound N ((b : ℝ) * S - T) S V a r tf
          hN hRfiber hV hSnonneg hGpos hsepFiber htimeWindow hlargeFiber hshort
        have hrpack : (r : ℝ) ≤ 2 * T + 1 :=
          separated_family_packing T r tf (by linarith) htimeFiber hsepFiber
        have hlogr := hlogfactor r hRfiber hrpack
        have hcoeff : 0 ≤ 128 * N * G / V ^ 2 := by positivity
        have hlocbound : (r : ℝ) ≤ 384 * N * G *
            Real.log (4 * N * T) / V ^ 2 := by
          calc
            (r : ℝ) ≤ 128 * N * G / V ^ 2 *
                (1 + 2 * Real.log (r : ℝ)) := hlocal
            _ ≤ 128 * N * G / V ^ 2 *
                (3 * Real.log (4 * N * T)) :=
                  mul_le_mul_of_nonneg_left hlogr hcoeff
            _ = 384 * N * G * Real.log (4 * N * T) / V ^ 2 := by ring
        simpa [r, A] using hlocbound
      · have hcardzero : (fiber b).card = 0 := Nat.eq_zero_of_not_pos hcard
        simp [hcardzero, hAnonneg]
    have hcardPartition :
        R = ∑ b ∈ Finset.range K, (fiber b).card := by
      have hmaps : Set.MapsTo bucket
          (Finset.univ : Finset (Fin R)) (Finset.range K) := by
        intro j hj
        exact Finset.mem_range.mpr (hbucketRange j)
      simpa [fiber] using
        (Finset.card_eq_sum_card_fiberwise (f := bucket)
          (s := (Finset.univ : Finset (Fin R)))
          (t := Finset.range K) hmaps)
    have hsumCast : (R : ℝ) =
        ∑ b ∈ Finset.range K, ((fiber b).card : ℝ) := by
      calc
        (R : ℝ) = ((∑ b ∈ Finset.range K, (fiber b).card : ℕ) : ℝ) := by
          exact_mod_cast hcardPartition
        _ = ∑ b ∈ Finset.range K, ((fiber b).card : ℝ) := by simp
    have hsumBound :
        (∑ b ∈ Finset.range K, ((fiber b).card : ℝ)) ≤
          (K : ℝ) * A := by
      calc
        (∑ b ∈ Finset.range K, ((fiber b).card : ℝ)) ≤
            ∑ b ∈ Finset.range K, A := by
          apply Finset.sum_le_sum
          intro b hb
          exact hfiberBound b
        _ = (K : ℝ) * A := by simp [Finset.sum_const, Finset.card_range]
    have htotal : (R : ℝ) ≤ (1 + 2 * T / S) * A := by
      calc
        (R : ℝ) = ∑ b ∈ Finset.range K, ((fiber b).card : ℝ) := hsumCast
        _ ≤ (K : ℝ) * A := hsumBound
        _ ≤ (1 + 2 * T / S) * A :=
          mul_le_mul_of_nonneg_right hKbound hAnonneg
    have hS_ne : S ≠ 0 := ne_of_gt hSpos
    have hV_ne : V ≠ 0 := ne_of_gt hV
    have hG_ne : G ≠ 0 := ne_of_gt hGpos
    have hexpand : (1 + 2 * T / S) * A =
        384 * N * G * Real.log (4 * N * T) / V ^ 2 +
          (384 * 2 * 128 ^ 2) * T * N * G ^ 3 *
            Real.log (4 * N * T) / V ^ 6 := by
      dsimp [A, S]
      field_simp [hV_ne, hG_ne]
    have hfirst : 0 ≤ N * G / V ^ 2 := by positivity
    have hsecond : 0 ≤ T * N * G ^ 3 / V ^ 6 := by positivity
    have hcoeff1 : (384 : ℝ) ≤ 2 ^ 24 := by norm_num
    have hcoeff2 : (384 : ℝ) * 2 * 128 ^ 2 ≤ 2 ^ 24 := by norm_num
    have hfinalCoeff :
        384 * N * G * Real.log (4 * N * T) / V ^ 2 +
          (384 * 2 * 128 ^ 2) * T * N * G ^ 3 *
            Real.log (4 * N * T) / V ^ 6 ≤
          2 ^ 24 * Real.log (4 * N * T) *
            (N * G / V ^ 2 + T * N * G ^ 3 / V ^ 6) := by
      have hterm1 : 384 * N * G * Real.log (4 * N * T) / V ^ 2 =
          384 * (Real.log (4 * N * T) * (N * G / V ^ 2)) := by ring
      have hterm2 : (384 * 2 * 128 ^ 2) * T * N * G ^ 3 *
          Real.log (4 * N * T) / V ^ 6 =
          (384 * 2 * 128 ^ 2) *
            (Real.log (4 * N * T) * (T * N * G ^ 3 / V ^ 6)) := by ring
      rw [hterm1, hterm2]
      have hfirst' : 0 ≤ Real.log (4 * N * T) * (N * G / V ^ 2) :=
        mul_nonneg (le_of_lt hLpos) hfirst
      have hsecond' : 0 ≤ Real.log (4 * N * T) *
          (T * N * G ^ 3 / V ^ 6) :=
        mul_nonneg (le_of_lt hLpos) hsecond
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 ^ 24 - 384) hfirst',
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 ^ 24 - 384 * 2 * 128 ^ 2) hsecond']
    exact htotal.trans (hexpand ▸ hfinalCoeff)

/-- A zero-energy polynomial has no separated large-value sample. This is
the explicit empty-family clause accompanying `lgv:separated`. -/
theorem huxleyFiniteBound_empty_of_zeroEnergy
    (N T V : ℝ) (a : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hN : 2 ≤ N) (hT : 2 ≤ T) (hV : 0 < V)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (htime : ∀ j, -T ≤ t j ∧ t j ≤ T)
    (hlarge : ∀ j, V ≤ ‖dirichletPolynomial N a (t j)‖)
    (henergy : dirichletEnergy N a = 0) :
    R = 0 := by
  have hbound := huxleyFiniteBound N T V a R t hN hT hV hsep htime hlarge
  have hRle : (R : ℝ) ≤ 0 := by
    simpa [henergy] using hbound
  have hReq : (R : ℝ) = 0 := le_antisymm hRle (Nat.cast_nonneg R)
  exact_mod_cast hReq

end FractionalPrimes.Literature.LargeValues

#print axioms FractionalPrimes.Literature.LargeValues.huxleyFiniteBound
#print axioms FractionalPrimes.Literature.LargeValues.huxleyFiniteBound_empty_of_zeroEnergy

end
