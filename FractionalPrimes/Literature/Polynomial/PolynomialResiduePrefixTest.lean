module

public import FractionalPrimes.Literature.Polynomial.ResiduePrefixEnvelope
public import FractionalPrimes.Literature.Uniformity.VariationAbelMultiplier
public import Mathlib.Data.Int.CardIntervalMod

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open scoped BigOperators

private theorem residuePrefixEnvelope_nonneg
    (X H : ℕ) (w : ℤ → ℂ) (Q : ℝ) :
    0 ≤ residuePrefixEnvelope X H w Q := by
  unfold residuePrefixEnvelope
  exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)

private theorem residuePrefixEnvelope_bounds_prefix
    (X H q a m : ℕ) (w : ℤ → ℂ) (Q : ℝ)
    (hq : 0 < q) (hqQ : (q : ℝ) ≤ Q) (ha : a < q) (hm : m ≤ H) :
    ‖residuePrefixSum X m q a w‖ ≤ residuePrefixEnvelope X H w Q := by
  classical
  have hQ : 0 ≤ Q := le_trans (Nat.cast_nonneg q) hqQ
  have hqfloor : q ≤ Nat.floor Q := (nat_le_real_iff_le_natFloor Q q hQ).mp hqQ
  have hmem : ((q, a), m) ∈ residuePrefixParameters H Q := by
    exact (residuePrefixParameters_mem_iff H Q q a m).mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq), hqfloor, ha, hm⟩
  let values := (residuePrefixParameters H Q).image fun t =>
    ‖residuePrefixSum X t.2 t.1.1 t.1.2 w‖
  have hvalue : ‖residuePrefixSum X m q a w‖ ∈ insert 0 values := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨((q, a), m), hmem, rfl⟩
  unfold residuePrefixEnvelope
  exact Finset.le_max' _ _ hvalue

def residuePrefixFiniteInterval (X H : ℕ) : FiniteIntegerInterval :=
  ⟨(X : ℤ) + 1, H⟩

private theorem realIntegerInterval_nat_eq_Ioc (X H : ℕ) :
    realIntegerInterval (X : ℝ) (H : ℝ) =
      Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) := by
  ext n
  rw [mem_realIntegerInterval_iff]
  simp only [Finset.mem_Ioc]
  constructor
  · rintro ⟨hnlo, hnhi⟩
    exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩
  · rintro ⟨hnlo, hnhi⟩
    exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩

private theorem residuePrefixFiniteInterval_points_eq_Ioc
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

private theorem arithmeticProgressionPrefix_eq_residueIntervalPrefix
    (X H q a : ℕ) (hq : 0 < q) (start : ℤ) (L K : ℕ)
    (hK : 0 < K) (hKL : K ≤ L)
    (hfull : arithmeticProgressionPoints start q hq L =
      (Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).filter
        (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)])) :
    ∃ m : ℕ, m ≤ H ∧
      arithmeticProgressionPoints start q hq K =
        (Finset.Ioc (X : ℤ) ((X + m : ℕ) : ℤ)).filter
          (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)] ) := by
  classical
  let last : ℤ := start + ((K - 1 : ℕ) : ℤ) * (q : ℤ)
  have hprefixSubset : arithmeticProgressionPoints start q hq K ⊆
      arithmeticProgressionPoints start q hq L := by
    intro n hn
    simp only [arithmeticProgressionPoints, Finset.mem_image,
      Finset.mem_range] at hn ⊢
    rcases hn with ⟨j, hj, rfl⟩
    exact ⟨j, lt_of_lt_of_le hj hKL, rfl⟩
  have hlastMem : last ∈ arithmeticProgressionPoints start q hq K := by
    apply Finset.mem_image.mpr
    refine ⟨K - 1, Finset.mem_range.mpr (Nat.sub_lt hK (by decide)), ?_⟩
    simp [last]
  have hlastFull := hprefixSubset hlastMem
  rw [hfull] at hlastFull
  have hlastBounds : (X : ℤ) < last ∧ last ≤ ((X + H : ℕ) : ℤ) :=
    Finset.mem_Ioc.mp (Finset.mem_filter.mp hlastFull).1
  let m : ℕ := (last - (X : ℤ)).toNat
  have hdiffNonneg : 0 ≤ last - (X : ℤ) := by omega
  have hmcast : (m : ℤ) = last - (X : ℤ) := by
    exact Int.toNat_of_nonneg hdiffNonneg
  have hmle : m ≤ H := by
    have hleZ : (m : ℤ) ≤ (H : ℤ) := by
      rw [hmcast]
      omega
    exact_mod_cast hleZ
  have hlastEq : last = ((X + m : ℕ) : ℤ) := by
    have hcast : ((X + m : ℕ) : ℤ) = (X : ℤ) + (m : ℤ) := by norm_cast
    rw [hcast]
    omega
  have hset : arithmeticProgressionPoints start q hq K =
      (Finset.Ioc (X : ℤ) ((X + m : ℕ) : ℤ)).filter
        (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) := by
    ext n
    simp only [arithmeticProgressionPoints, Finset.mem_image,
      Finset.mem_range, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hfullMem : start + (j : ℤ) * (q : ℤ) ∈
          arithmeticProgressionPoints start q hq L := by
        apply hprefixSubset
        apply Finset.mem_image.mpr
        exact ⟨j, Finset.mem_range.mpr hj, rfl⟩
      rw [hfull] at hfullMem
      have hfullBounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hfullMem).1
      have hmod := (Finset.mem_filter.mp hfullMem).2
      have hjle : j ≤ K - 1 := Nat.le_pred_of_lt hj
      have hmul : (j : ℤ) * (q : ℤ) ≤ ((K - 1 : ℕ) : ℤ) * (q : ℤ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjle)
          (Int.natCast_nonneg q)
      refine ⟨⟨hfullBounds.1, ?_⟩, hmod⟩
      have htop : start + (j : ℤ) * (q : ℤ) ≤ last := by
        dsimp [last]
        linarith
      exact le_trans htop (by rw [hlastEq])
    · rintro ⟨⟨hlo, htop⟩, hmod⟩
      have hnfull : n ∈ arithmeticProgressionPoints start q hq L := by
        rw [hfull]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨hlo, htop.trans (by
            rw [← hlastEq]
            exact hlastBounds.2)⟩, hmod⟩
      simp only [arithmeticProgressionPoints, Finset.mem_image,
        Finset.mem_range] at hnfull
      rcases hnfull with ⟨j, hjL, hjEq⟩
      have hmul : (j : ℤ) * (q : ℤ) ≤
          ((K - 1 : ℕ) : ℤ) * (q : ℤ) := by
        have hjEq' : start + (j : ℤ) * (q : ℤ) = n := hjEq
        rw [← hlastEq] at htop
        dsimp [last] at htop
        linarith
      have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
      have hjleZ : (j : ℤ) ≤ ((K - 1 : ℕ) : ℤ) :=
        (mul_le_mul_iff_of_pos_right hqZ).mp hmul
      have hjle : j ≤ K - 1 := by exact_mod_cast hjleZ
      have hKsub : K - 1 + 1 = K := Nat.sub_add_cancel (by omega)
      have hjK : j < K := by omega
      exact ⟨j, hjK, hjEq⟩
  exact ⟨m, hmle, hset⟩

/-- Summation by parts on each residue slice is controlled by the maximum of
the initial residue prefixes and the inhomogeneous residue-class variation. -/
theorem testByResiduePrefixes
    (q X H : ℕ) (Q : ℝ) (w g : ℤ → ℂ)
    (hq : 0 < q) (hX : 0 < X) (hH : 0 < H)
    (hqQ : (q : ℝ) ≤ Q) :
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n * g n‖ ≤
      residuePrefixEnvelope X H w Q *
        finiteResidueClassVariation (residuePrefixFiniteInterval X H) g q := by
  classical
  let I := residuePrefixFiniteInterval X H
  have hIpoints : I.points = realIntegerInterval (X : ℝ) (H : ℝ) := by
    calc
      I.points = Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) :=
        residuePrefixFiniteInterval_points_eq_Ioc X H hH
      _ = realIntegerInterval (X : ℝ) (H : ℝ) :=
        (realIntegerInterval_nat_eq_Ioc X H).symm
  have hsplit := sum_eq_sum_residue_filters I.points q hq
    (fun n => w n * g n)
  have hclassBound : ∀ a ∈ Finset.range q,
      ‖∑ n ∈ I.points.filter
          (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), w n * g n‖ ≤
        finiteOrderedTotalVariation
          (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g *
          residuePrefixEnvelope X H w Q := by
    intro a ha
    rcases finiteInterval_residueFilter_eq_arithmeticProgressionPoints
        I (a : ℤ) q hq with ⟨start, L, hfull⟩
    obtain ⟨K, hKL, habel⟩ :=
      exists_arithmeticProgressionPrefix_sum_mul_bound start q hq L w g
    have habel' :
        ‖∑ n ∈ arithmeticProgressionPoints start q hq L, w n * g n‖ ≤
          finiteOrderedTotalVariation
            (arithmeticProgressionPoints start q hq L) g *
            ‖∑ n ∈ arithmeticProgressionPoints start q hq K, w n‖ := by
      have hcomm :
          (∑ n ∈ arithmeticProgressionPoints start q hq L, g n * w n) =
            ∑ n ∈ arithmeticProgressionPoints start q hq L, w n * g n := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
      rw [hcomm] at habel
      exact habel
    have hprefixNorm :
        ‖∑ n ∈ arithmeticProgressionPoints start q hq K, w n‖ ≤
          residuePrefixEnvelope X H w Q := by
      by_cases hK : K = 0
      · subst K
        simp [arithmeticProgressionPoints]
        exact residuePrefixEnvelope_nonneg X H w Q
      · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
        have hfullIoc :
            arithmeticProgressionPoints start q hq L =
              (Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).filter
                (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) := by
          calc
            arithmeticProgressionPoints start q hq L =
                I.points.filter
                  (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) := hfull
            _ = (realIntegerInterval (X : ℝ) (H : ℝ)).filter
                  (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) := by
                rw [hIpoints]
            _ = (Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).filter
                  (fun n : ℤ => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) := by
                rw [realIntegerInterval_nat_eq_Ioc]
        have hprefix := arithmeticProgressionPrefix_eq_residueIntervalPrefix
          X H q a hq start L K hKpos hKL hfullIoc
        obtain ⟨m, hm, hprefixEq⟩ := hprefix
        have hsumEq :
            (∑ n ∈ arithmeticProgressionPoints start q hq K, w n) =
              residuePrefixSum X m q a w := by
          rw [hprefixEq]
          unfold residuePrefixSum
          rw [realIntegerInterval_nat_eq_Ioc X m]
        rw [hsumEq]
        exact residuePrefixEnvelope_bounds_prefix X H q a m w Q
          hq hqQ (Finset.mem_range.mp ha) hm
    have habelClass :
        ‖∑ n ∈ I.points.filter
            (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), w n * g n‖ ≤
          finiteOrderedTotalVariation
            (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g *
            ‖∑ n ∈ arithmeticProgressionPoints start q hq K, w n‖ := by
      simpa [hfull] using habel'
    calc
      ‖∑ n ∈ I.points.filter
          (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), w n * g n‖ ≤
        finiteOrderedTotalVariation
          (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g *
          ‖∑ n ∈ arithmeticProgressionPoints start q hq K, w n‖ := habelClass
      _ ≤ finiteOrderedTotalVariation
          (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g *
          residuePrefixEnvelope X H w Q :=
        mul_le_mul_of_nonneg_left hprefixNorm
          (finiteOrderedTotalVariation_nonneg _ _)
  have hsumBound :
      ‖∑ n ∈ I.points, w n * g n‖ ≤
        residuePrefixEnvelope X H w Q *
          finiteResidueClassVariation I g q := by
    calc
      ‖∑ n ∈ I.points, w n * g n‖ =
          ‖∑ a ∈ Finset.range q,
            ∑ n ∈ I.points.filter
              (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), w n * g n‖ :=
        congrArg norm hsplit
      _ ≤ ∑ a ∈ Finset.range q,
          ‖∑ n ∈ I.points.filter
            (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), w n * g n‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ Finset.range q,
          finiteOrderedTotalVariation
            (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g *
            residuePrefixEnvelope X H w Q :=
        Finset.sum_le_sum fun a ha => hclassBound a ha
      _ = residuePrefixEnvelope X H w Q *
          finiteResidueClassVariation I g q := by
        unfold finiteResidueClassVariation
        calc
          (∑ a ∈ Finset.range q,
              finiteOrderedTotalVariation
                (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g *
                residuePrefixEnvelope X H w Q) =
              ∑ a ∈ Finset.range q,
                residuePrefixEnvelope X H w Q *
                  finiteOrderedTotalVariation
                    (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = residuePrefixEnvelope X H w Q *
                ∑ a ∈ Finset.range q,
                  finiteOrderedTotalVariation
                    (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g := by
            rw [Finset.mul_sum]
  rw [← hIpoints]
  exact hsumBound

#print axioms testByResiduePrefixes

