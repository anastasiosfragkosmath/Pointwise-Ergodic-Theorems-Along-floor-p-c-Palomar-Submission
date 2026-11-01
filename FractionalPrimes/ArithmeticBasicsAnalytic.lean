module

public import FractionalPrimes.ArithmeticBasicsCore

@[expose] public section

namespace FractionalPrimes

theorem positiveShiftBox_card_le_bound_product (bounds : List ℕ) :
    (positiveShiftBox bounds).card ≤ bounds.prod := by
  rw [positiveShiftBox_card]
  induction bounds with
  | nil => simp
  | cons H rest ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul (Nat.sub_le H 1) ih


theorem sum_positiveShiftBox_cons {M : Type*} [AddCommMonoid M]
    (H : ℕ) (rest : List ℕ) (g : List ℕ → M) :
    (∑ a ∈ positiveShiftBox (H :: rest), g a) =
      ∑ a ∈ Finset.Ico 1 H, ∑ b ∈ positiveShiftBox rest, g (a :: b) := by
  have hinj : Set.InjOn (fun p : ℕ × List ℕ => p.1 :: p.2)
      ↑((Finset.Ico 1 H).product (positiveShiftBox rest)) := by
    intro p hp q hq heq
    cases p with
    | mk a as =>
      cases q with
      | mk b bs =>
        simp only [List.cons.injEq] at heq
        cases heq.1
        cases heq.2
        rfl
  rw [positiveShiftBox, Finset.sum_image hinj]
  change (∑ p ∈ (Finset.Ico 1 H ×ˢ positiveShiftBox rest),
      g (p.1 :: p.2)) = _
  rw [Finset.sum_product]

theorem sum_positiveShiftBox_prod_map (bounds : List ℕ) (f : ℕ → ℝ) :
    (∑ shifts ∈ positiveShiftBox bounds, (shifts.map f).prod) =
      (bounds.map (fun H => ∑ a ∈ Finset.Ico 1 H, f a)).prod := by
  induction bounds with
  | nil => simp [positiveShiftBox]
  | cons H rest ih =>
      rw [sum_positiveShiftBox_cons]
      simp only [List.map_cons, List.prod_cons]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [ih]

theorem sum_sqrt_nat_Ico_le (H : ℕ) (hH : 1 ≤ H) :
    (∑ a ∈ Finset.Ico 1 H, Real.sqrt (a : ℝ)) ≤
      (2 / 3) * (H : ℝ) ^ (3 / 2 : ℝ) := by
  have hsum : (∑ a ∈ Finset.Ico 1 H, Real.sqrt (a : ℝ)) ≤
      ∫ t in (1 : ℝ)..(H : ℝ), Real.sqrt t := by
    have hmono := MonotoneOn.sum_le_integral_Ico (a := 1) (b := H)
      (f := Real.sqrt) hH (fun a ha b hb hab => Real.sqrt_le_sqrt hab)
    simpa using hmono
  have hinterval : ∫ t in (1 : ℝ)..(H : ℝ), Real.sqrt t =
      (2 / 3) * ((H : ℝ) ^ (3 / 2 : ℝ) - 1) := by
    rw [show (fun t : ℝ => Real.sqrt t) = fun t => t ^ (1 / (2 : ℝ)) by
      funext t
      exact Real.sqrt_eq_rpow t]
    rw [integral_rpow (a := (1 : ℝ)) (b := (H : ℝ))
      (r := (1 / 2 : ℝ)) (Or.inl (by norm_num))]
    norm_num
    ring
  rw [hinterval] at hsum
  have hpow : 0 ≤ (H : ℝ) ^ (3 / 2 : ℝ) := by positivity
  nlinarith

theorem inv_sqrt_nat_le_twice_sqrt_sub (a : ℕ) (ha : 0 < a) :
    1 / Real.sqrt (a : ℝ) ≤
      2 * (Real.sqrt (a : ℝ) - Real.sqrt ((a - 1 : ℕ) : ℝ)) := by
  have haR : 1 ≤ (a : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr ha)
  have hsub : 0 ≤ ((a - 1 : ℕ) : ℝ) := by positivity
  have hsuble : ((a - 1 : ℕ) : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast Nat.sub_le a 1
  have hu : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hv : 0 ≤ Real.sqrt ((a - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have huv : Real.sqrt ((a - 1 : ℕ) : ℝ) ≤ Real.sqrt (a : ℝ) :=
    Real.sqrt_le_sqrt hsuble
  have hsqU : Real.sqrt (a : ℝ) ^ 2 = a := Real.sq_sqrt (by positivity)
  have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    norm_num
  have hsqV : Real.sqrt ((a - 1 : ℕ) : ℝ) ^ 2 = (a : ℝ) - 1 := by
    rw [Real.sq_sqrt hsub, hcast]
  have hden : Real.sqrt (a : ℝ) + Real.sqrt ((a - 1 : ℕ) : ℝ) > 0 := by positivity
  have hdiff : Real.sqrt (a : ℝ) - Real.sqrt ((a - 1 : ℕ) : ℝ) =
      1 / (Real.sqrt (a : ℝ) + Real.sqrt ((a - 1 : ℕ) : ℝ)) := by
    apply (eq_div_iff hden.ne').2
    nlinarith [hsqU, hsqV]
  rw [hdiff, mul_one_div]
  apply (div_le_div_iff₀ hu hden).2
  nlinarith

theorem sum_inv_sqrt_nat_Ico_le (H : ℕ) (hH : 1 ≤ H) :
    (∑ a ∈ Finset.Ico 1 H, 1 / Real.sqrt (a : ℝ)) ≤
      2 * Real.sqrt ((H - 1 : ℕ) : ℝ) := by
  have hpoint : ∀ a ∈ Finset.Ico 1 H,
      1 / Real.sqrt (a : ℝ) ≤
        2 * (Real.sqrt (a : ℝ) - Real.sqrt ((a - 1 : ℕ) : ℝ)) := by
    intro a ha
    exact inv_sqrt_nat_le_twice_sqrt_sub a (Finset.mem_Ico.mp ha).1
  calc
    (∑ a ∈ Finset.Ico 1 H, 1 / Real.sqrt (a : ℝ)) ≤
        ∑ a ∈ Finset.Ico 1 H,
          2 * (Real.sqrt (a : ℝ) - Real.sqrt ((a - 1 : ℕ) : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = 2 * Real.sqrt ((H - 1 : ℕ) : ℝ) := by
      rw [← Finset.mul_sum]
      rw [Finset.sum_Ico_eq_sum_range]
      have htel := Finset.sum_range_tsub
        (f := fun n : ℕ => Real.sqrt (n : ℝ))
        (fun m n hmn => Real.sqrt_le_sqrt (by exact_mod_cast hmn)) (H - 1)
      simpa [Nat.cast_add, Nat.cast_one, add_comm] using
        congrArg (fun z : ℝ => 2 * z) htel

theorem two_sqrt_sub_le_two_mul_div (H : ℕ) (hH : 1 ≤ H) :
    2 * Real.sqrt ((H - 1 : ℕ) : ℝ) ≤
      2 * (H : ℝ) / Real.sqrt ((H + 1 : ℕ) : ℝ) := by
  have hHm1 : 0 ≤ ((H - 1 : ℕ) : ℝ) := by positivity
  have hHp1 : 0 ≤ ((H + 1 : ℕ) : ℝ) := by positivity
  have hHreal : 1 ≤ (H : ℝ) := by exact_mod_cast hH
  have hU : 0 ≤ Real.sqrt ((H - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hV : 0 < Real.sqrt ((H + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hUsq : Real.sqrt ((H - 1 : ℕ) : ℝ) ^ 2 = (H : ℝ) - 1 := by
    rw [Real.sq_sqrt hHm1, Nat.cast_sub (by omega : 1 ≤ H)]
    norm_num
  have hVsq : Real.sqrt ((H + 1 : ℕ) : ℝ) ^ 2 = (H : ℝ) + 1 := by
    rw [Real.sq_sqrt hHp1, Nat.cast_add]
    norm_num
  have hprodSq : (Real.sqrt ((H - 1 : ℕ) : ℝ) *
      Real.sqrt ((H + 1 : ℕ) : ℝ)) ^ 2 = (H : ℝ) ^ 2 - 1 := by
    rw [mul_pow, hUsq, hVsq]
    ring
  have hprod : Real.sqrt ((H - 1 : ℕ) : ℝ) *
      Real.sqrt ((H + 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt ((H - 1 : ℕ) : ℝ) *
      Real.sqrt ((H + 1 : ℕ) : ℝ) - (H : ℝ))]
  apply (le_div_iff₀ hV).2
  nlinarith

theorem real_sum_sq_div_le_sum_sq_div
    {ι : Type*} (s : Finset ι) (b : ι → ℝ) (P : ℝ)
    (hcard : (s.card : ℝ) ≤ P) (hP : 0 < P) :
    (∑ i ∈ s, b i / P) ^ 2 ≤ (∑ i ∈ s, b i ^ 2) / P := by
  have hcs : (∑ i ∈ s, b i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, b i ^ 2 := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq s
      (fun _ : ι => (1 : ℝ)) b)
  have hsq : 0 ≤ ∑ i ∈ s, b i ^ 2 := by positivity
  have hcs' : (∑ i ∈ s, b i) ^ 2 ≤ P * ∑ i ∈ s, b i ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hcard hsq)
  rw [← Finset.sum_div, div_pow]
  apply (div_le_div_iff₀ (by positivity) hP).2
  calc
    (∑ i ∈ s, b i) ^ 2 * P ≤
        (P * ∑ i ∈ s, b i ^ 2) * P :=
      mul_le_mul_of_nonneg_right hcs' (le_of_lt hP)
    _ = (∑ i ∈ s, b i ^ 2) * P ^ 2 := by ring

/-- The total real shift of a tuple of natural shifts. -/
def realShiftTotal (shifts : List ℕ) : ℝ :=
  (shifts.map fun a => (a : ℝ)).sum

theorem list_map_eq_flatMap_singleton {α β : Type*} (l : List α) (f : α → β) :
    l.map f = l.flatMap (fun a => [f a]) := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [ih]

/-- The product of the integer differencing bounds, viewed in `ℝ`. -/
def realShiftNormalizer (bounds : List ℕ) : ℝ :=
  (bounds.map fun H => (H : ℝ)).prod

/-- The upper product `P₊=∏(H_i+1)` used in the correlation estimate. -/
def realShiftPlusNormalizer (bounds : List ℕ) : ℝ :=
  (List.map (fun H : ℕ => ((H + 1 : ℕ) : ℝ)) bounds).prod

/-- The shortened real interval associated with a tuple of shifts. -/
noncomputable def iteratedDifferenceInterval (x Y : ℝ) (shifts : List ℕ) : Finset ℤ :=
  realIntegerInterval x (Y - realShiftTotal shifts)

theorem iteratedRealForwardDifference_append_singleton
    (f : ℝ → ℝ) (shifts : List ℕ) (d : ℕ) :
    iteratedRealForwardDifference f (shifts ++ [d]) =
      realForwardDifference d (iteratedRealForwardDifference f shifts) := by
  induction shifts generalizing f with
  | nil => simp [iteratedRealForwardDifference]
  | cons a rest ih =>
      simp only [List.cons_append, iteratedRealForwardDifference]
      rw [ih]

theorem realShiftTotal_append (left right : List ℕ) :
    realShiftTotal (left ++ right) =
      realShiftTotal left + realShiftTotal right := by
  simp [realShiftTotal, List.map_append, List.sum_append]

theorem realShiftTotal_prepend_append_commute
    (H : ℕ) (rest processed : List ℕ) :
    realShiftTotal ((H :: rest) ++ processed) =
      realShiftTotal (rest ++ (H :: processed)) := by
  simp [realShiftTotal, List.map_append, List.sum_append]
  ring

theorem realShiftTotal_cons (H : ℕ) (rest : List ℕ) :
    realShiftTotal (H :: rest) = (H : ℝ) + realShiftTotal rest := by
  simp [realShiftTotal]

theorem realShiftTotal_append_singleton (shifts : List ℕ) (d : ℕ) :
    realShiftTotal (shifts ++ [d]) = realShiftTotal shifts + d := by
  simp [realShiftTotal, List.map_append]

theorem realShiftTotal_reverse (shifts : List ℕ) :
    realShiftTotal shifts.reverse = realShiftTotal shifts := by
  induction shifts with
  | nil => simp [realShiftTotal]
  | cons a rest ih =>
      rw [List.reverse_cons, realShiftTotal_append, ih]
      simp [realShiftTotal]
      ring

/-- The normalized averaged iterated correlation quantity `T_s` from the
blueprint, parameterized by the list of its first `s` differencing bounds. -/
noncomputable def averagedIteratedCorrelation
    (f : ℝ → ℝ) (x Y : ℝ) (bounds : List ℕ) : ℝ :=
  (Y * realShiftNormalizer bounds)⁻¹ *
    ∑ shifts ∈ positiveShiftBox bounds,
      ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
        realExponentialPhase (iteratedRealForwardDifference f shifts) n‖

theorem averagedIteratedCorrelation_eq_normalized_sum
    (f : ℝ → ℝ) (x Y : ℝ) (bounds : List ℕ)
    (hY : 0 < Y) (hP : 0 < realShiftNormalizer bounds) :
    averagedIteratedCorrelation f x Y bounds =
      (realShiftNormalizer bounds)⁻¹ *
        ∑ shifts ∈ positiveShiftBox bounds,
          (‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
            realExponentialPhase (iteratedRealForwardDifference f shifts) n‖ / Y) := by
  let a : List ℕ → ℝ := fun shifts =>
    ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
      realExponentialPhase (iteratedRealForwardDifference f shifts) n‖
  have hsum : (∑ shifts ∈ positiveShiftBox bounds, a shifts / Y) =
      (∑ shifts ∈ positiveShiftBox bounds, a shifts) / Y := by
    rw [Finset.sum_div]
  have hsum' :
      (∑ shifts ∈ positiveShiftBox bounds,
        ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
          realExponentialPhase (iteratedRealForwardDifference f shifts) n‖ / Y) =
      (∑ shifts ∈ positiveShiftBox bounds,
        ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
          realExponentialPhase (iteratedRealForwardDifference f shifts) n‖) / Y := by
    simpa [a] using hsum
  unfold averagedIteratedCorrelation
  rw [hsum']
  field_simp [ne_of_gt hY, ne_of_gt hP]

theorem realShiftNormalizer_eq_natCast_prod (bounds : List ℕ) :
    realShiftNormalizer bounds = (bounds.prod : ℝ) := by
  induction bounds with
  | nil => simp [realShiftNormalizer]
  | cons H rest ih =>
      change (H : ℝ) * realShiftNormalizer rest = ((H * rest.prod : ℕ) : ℝ)
      rw [ih, Nat.cast_mul]

theorem realShiftPlusNormalizer_eq_natCast_shiftProduct (bounds : List ℕ) :
    realShiftPlusNormalizer bounds =
      ((bounds.map fun H : ℕ => H + 1).prod : ℝ) := by
  induction bounds with
  | nil => simp [realShiftPlusNormalizer]
  | cons H rest ih =>
      change ((H + 1 : ℕ) : ℝ) * realShiftPlusNormalizer rest =
        (((H + 1 : ℕ) * (rest.map fun K : ℕ => K + 1).prod : ℕ) : ℝ)
      rw [ih, Nat.cast_mul]


theorem iteratedDifferenceInterval_head
    (x Y : ℝ) (d : ℕ) (tail : List ℕ) :
    iteratedDifferenceInterval x Y (d :: tail) =
      realIntegerInterval x ((Y - realShiftTotal tail) - d) := by
  simp [iteratedDifferenceInterval, realShiftTotal]
  congr 1
  ring

theorem averagedIteratedCorrelation_nil (f : ℝ → ℝ) (x Y : ℝ)
    (hY : 0 < Y) :
    averagedIteratedCorrelation f x Y [] =
      ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ / Y := by
  simp [averagedIteratedCorrelation, realShiftNormalizer, positiveShiftBox,
    iteratedDifferenceInterval, realShiftTotal, iteratedRealForwardDifference,
    realIntegerInterval]
  field_simp [ne_of_gt hY]

theorem positiveShiftBox_mem_cons_iff
    (H : ℕ) (rest : List ℕ) (shifts : List ℕ) :
    shifts ∈ positiveShiftBox (H :: rest) ↔
      ∃ d ∈ Finset.Ico 1 H, ∃ tail ∈ positiveShiftBox rest,
        shifts = d :: tail := by
  simp [positiveShiftBox, Finset.product, Finset.mem_image,
    and_assoc, eq_comm]

theorem positiveShiftBox_entries_pos
    (bounds shifts : List ℕ) (hpos : ∀ H ∈ bounds, 0 < H)
    (hshifts : shifts ∈ positiveShiftBox bounds) :
    ∀ a ∈ shifts, 0 < a := by
  induction bounds generalizing shifts with
  | nil =>
      simp only [positiveShiftBox, Finset.mem_singleton] at hshifts
      subst shifts
      simp
  | cons H rest ih =>
      obtain ⟨d, hd, tail, htail, rfl⟩ :=
        (positiveShiftBox_mem_cons_iff H rest shifts).mp hshifts
      have hposRest : ∀ K ∈ rest, 0 < K := by
        intro K hK
        exact hpos K (by simp [hK])
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Nat.zero_lt_of_lt (Finset.mem_Ico.mp hd).1
      · exact ih tail hposRest htail a ha

theorem positiveShiftBox_length
    (bounds shifts : List ℕ) (hshifts : shifts ∈ positiveShiftBox bounds) :
    shifts.length = bounds.length := by
  induction bounds generalizing shifts with
  | nil =>
      simp only [positiveShiftBox, Finset.mem_singleton] at hshifts
      subst shifts
      simp
  | cons H rest ih =>
      obtain ⟨d, hd, tail, htail, rfl⟩ :=
        (positiveShiftBox_mem_cons_iff H rest shifts).mp hshifts
      simp only [List.length_cons]
      rw [ih tail htail]

theorem positiveShiftBox_mem_iff_forall₂ (bounds shifts : List ℕ) :
    shifts ∈ positiveShiftBox bounds ↔
      List.Forall₂ (fun H a => a ∈ Finset.Ico 1 H) bounds shifts := by
  induction bounds generalizing shifts with
  | nil => simp [positiveShiftBox]
  | cons H rest ih =>
      rw [positiveShiftBox_mem_cons_iff, List.forall₂_cons_left_iff]
      constructor
      · rintro ⟨d, hd, tail, htail, rfl⟩
        exact ⟨d, tail, hd, (ih tail).mp htail, rfl⟩
      · rintro ⟨d, tail, hd, htail, rfl⟩
        exact ⟨d, hd, tail, (ih tail).mpr htail, rfl⟩

theorem positiveShiftBox_reverse (bounds : List ℕ) :
    (positiveShiftBox bounds).image List.reverse =
      positiveShiftBox bounds.reverse := by
  ext shifts
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨tuple, htuple, rfl⟩
    apply (positiveShiftBox_mem_iff_forall₂ bounds.reverse tuple.reverse).mpr
    have hrel := (positiveShiftBox_mem_iff_forall₂ bounds tuple).mp htuple
    exact List.forall₂_reverse_iff.mpr hrel
  · intro hshifts
    refine ⟨shifts.reverse, ?_, by simp⟩
    apply (positiveShiftBox_mem_iff_forall₂ bounds shifts.reverse).mpr
    have hrel :=
      (positiveShiftBox_mem_iff_forall₂ bounds.reverse shifts).mp hshifts
    simpa only [List.reverse_reverse] using
      (List.forall₂_reverse_iff (R := fun H a => a ∈ Finset.Ico 1 H)
        (l₁ := bounds.reverse) (l₂ := shifts)).mpr hrel

theorem sum_positiveShiftBox_reverse {M : Type*} [AddCommMonoid M]
    (bounds : List ℕ) (g : List ℕ → M) :
    (∑ shifts ∈ positiveShiftBox bounds, g shifts.reverse) =
      ∑ shifts ∈ positiveShiftBox bounds.reverse, g shifts := by
  have hinj : Function.Injective (List.reverse : List ℕ → List ℕ) := by
    intro a b hab
    simpa using congrArg List.reverse hab
  have hinjOn : Set.InjOn (List.reverse : List ℕ → List ℕ)
      ↑(positiveShiftBox bounds) := by
    intro a ha b hb hab
    exact hinj hab
  calc
    (∑ shifts ∈ positiveShiftBox bounds, g shifts.reverse) =
        ∑ shifts ∈ (positiveShiftBox bounds).image List.reverse, g shifts := by
      symm
      rw [Finset.sum_image hinjOn]
    _ = ∑ shifts ∈ positiveShiftBox bounds.reverse, g shifts := by
      rw [positiveShiftBox_reverse]

theorem realShiftTotal_le_bounds
    (bounds shifts : List ℕ) (hshifts : shifts ∈ positiveShiftBox bounds) :
    realShiftTotal shifts ≤ realShiftTotal bounds := by
  induction bounds generalizing shifts with
  | nil =>
      simp only [positiveShiftBox] at hshifts
      simp only [Finset.mem_singleton] at hshifts
      subst shifts
      simp [realShiftTotal]
  | cons H rest ih =>
      obtain ⟨d, hd, tail, htail, rfl⟩ :=
        (positiveShiftBox_mem_cons_iff H rest shifts).mp hshifts
      have hdle : (d : ℝ) ≤ (H : ℝ) := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_Ico.mp hd).2)
      have htailbound := ih tail htail
      simpa [realShiftTotal] using add_le_add hdle htailbound

theorem realShiftTotal_add_length_le_bounds
    (bounds shifts : List ℕ) (hshifts : shifts ∈ positiveShiftBox bounds) :
    realShiftTotal shifts + (shifts.length : ℝ) ≤ realShiftTotal bounds := by
  induction bounds generalizing shifts with
  | nil =>
      simp only [positiveShiftBox] at hshifts
      simp only [Finset.mem_singleton] at hshifts
      subst shifts
      simp [realShiftTotal]
  | cons H rest ih =>
      obtain ⟨d, hd, tail, htail, rfl⟩ :=
        (positiveShiftBox_mem_cons_iff H rest shifts).mp hshifts
      have hdle : (d : ℝ) + 1 ≤ (H : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Finset.mem_Ico.mp hd).2)
      have htailbound := ih tail htail
      rw [realShiftTotal_cons, realShiftTotal_cons]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

theorem list_prod_sqrt_natCast (shifts : List ℕ) :
    (List.map (fun a : ℕ => Real.sqrt (a : ℝ)) shifts).prod =
      Real.sqrt ((List.map (fun a : ℕ => (a : ℝ)) shifts).prod) := by
  induction shifts with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih, Real.sqrt_mul (by positivity)]

theorem list_prod_inv_sqrt_natCast (shifts : List ℕ) :
    (List.map (fun a : ℕ => 1 / Real.sqrt (a : ℝ)) shifts).prod =
      1 / Real.sqrt ((List.map (fun a : ℕ => (a : ℝ)) shifts).prod) := by
  induction shifts with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [Real.sqrt_mul (by positivity), ih]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem list_prod_map_nonneg (bounds : List ℕ) (f : ℕ → ℝ)
    (hf : ∀ a ∈ bounds, 0 ≤ f a) : 0 ≤ (List.map f bounds).prod := by
  induction bounds with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.prod_cons]
      apply mul_nonneg (hf a (by simp))
      apply ih
      intro b hb
      exact hf b (by simp [hb])

theorem list_prod_map_mono {bounds : List ℕ} (f g : ℕ → ℝ)
    (hf : ∀ a ∈ bounds, 0 ≤ f a) (hg : ∀ a ∈ bounds, 0 ≤ g a)
    (hle : ∀ a ∈ bounds, f a ≤ g a) :
    (List.map f bounds).prod ≤ (List.map g bounds).prod := by
  induction bounds with
  | nil => simp
  | cons a rest ih =>
      have hfa := hf a (by simp)
      have hga := hg a (by simp)
      have hlea := hle a (by simp)
      have hfr : ∀ b ∈ rest, 0 ≤ f b := by
        intro b hb
        exact hf b (by simp [hb])
      have hgr : ∀ b ∈ rest, 0 ≤ g b := by
        intro b hb
        exact hg b (by simp [hb])
      have hler : ∀ b ∈ rest, f b ≤ g b := by
        intro b hb
        exact hle b (by simp [hb])
      have hih := ih hfr hgr hler
      have hprodF := list_prod_map_nonneg rest f hfr
      simp only [List.map_cons, List.prod_cons]
      calc
        f a * (List.map f rest).prod ≤ g a * (List.map f rest).prod :=
          mul_le_mul_of_nonneg_right hlea hprodF
        _ ≤ g a * (List.map g rest).prod :=
          mul_le_mul_of_nonneg_left hih hga

theorem reciprocal_sqrt_positiveShiftBox_sum_bound
    (bounds : List ℕ) (hpos : ∀ H ∈ bounds, 0 < H) :
    (∑ shifts ∈ positiveShiftBox bounds,
      1 / Real.sqrt ((List.map (fun a : ℕ => (a : ℝ)) shifts).prod)) ≤
      (List.map (fun H : ℕ =>
        2 * (H : ℝ) / Real.sqrt ((H + 1 : ℕ) : ℝ)) bounds).prod := by
  simp_rw [← list_prod_inv_sqrt_natCast]
  rw [sum_positiveShiftBox_prod_map]
  apply list_prod_map_mono
  · intro H hH
    exact Finset.sum_nonneg fun a ha => by positivity
  · intro H hH
    positivity
  · intro H hH
    have hHpos := hpos H hH
    have hHone : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hHpos)
    have hsum := sum_inv_sqrt_nat_Ico_le H hHone
    have hend := two_sqrt_sub_le_two_mul_div H hHone
    simpa using hsum.trans hend

theorem sqrt_positiveShiftBox_sum_bound
    (bounds : List ℕ) (hpos : ∀ H ∈ bounds, 0 < H) :
    (∑ shifts ∈ positiveShiftBox bounds,
      Real.sqrt ((List.map (fun a : ℕ => (a : ℝ)) shifts).prod)) ≤
      (List.map (fun H : ℕ =>
        (2 / 3) * (H : ℝ) ^ (3 / 2 : ℝ)) bounds).prod := by
  simp_rw [← list_prod_sqrt_natCast]
  rw [sum_positiveShiftBox_prod_map]
  apply list_prod_map_mono
  · intro H hH
    positivity
  · intro H hH
    positivity
  · intro H hH
    have hHpos := hpos H hH
    have hHone : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hHpos)
    exact sum_sqrt_nat_Ico_le H hHone

theorem sqrt_coordinate_product_normalization (bounds : List ℕ) :
    (List.map (fun H : ℕ =>
      (2 / 3) * (H : ℝ) ^ (3 / 2 : ℝ)) bounds).prod =
      (2 / 3 : ℝ) ^ bounds.length *
        (List.map (fun H : ℕ => (H : ℝ)) bounds).prod ^ (3 / 2 : ℝ) := by
  have castProdNonneg : ∀ l : List ℕ,
      0 ≤ (List.map (fun H : ℕ => (H : ℝ)) l).prod := by
    intro l
    induction l with
    | nil => simp
    | cons H rest ih =>
        simp only [List.map_cons, List.prod_cons]
        exact mul_nonneg (by positivity) ih
  induction bounds with
  | nil => simp [realShiftNormalizer]
  | cons H rest ih =>
      have hnorm := castProdNonneg rest
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [Real.mul_rpow (by positivity : 0 ≤ (H : ℝ)) hnorm, ih]
      rw [pow_succ]
      ring

theorem realShiftNormalizer_append_singleton
    (bounds : List ℕ) (H : ℕ) :
    realShiftNormalizer (bounds ++ [H]) =
      realShiftNormalizer bounds * (H : ℝ) := by
  simp [realShiftNormalizer, List.map_append, List.prod_append]

theorem realShiftNormalizer_reverse (bounds : List ℕ) :
    realShiftNormalizer bounds.reverse = realShiftNormalizer bounds := by
  induction bounds with
  | nil => simp [realShiftNormalizer]
  | cons H rest ih =>
      calc
        realShiftNormalizer (H :: rest).reverse =
            realShiftNormalizer rest * (H : ℝ) := by
              rw [List.reverse_cons, realShiftNormalizer_append_singleton, ih]
        _ = (H : ℝ) * realShiftNormalizer rest := by ring
        _ = realShiftNormalizer (H :: rest) := by simp [realShiftNormalizer]

theorem real_weyl_rescale_normalization
    {S2 C H L Y : ℝ}
    (hlocal : S2 / L ^ 2 ≤ 4 / H + 4 / (H * L) * C)
    (hC : 0 ≤ C) (hH : 0 < H)
    (hL : 0 < L) (hLY : L ≤ Y) :
    S2 / Y ^ 2 ≤ 4 / H + 4 / (H * Y) * C := by
  have hY : 0 < Y := lt_of_lt_of_le hL hLY
  have hratio : 0 ≤ (L / Y) ^ 2 := by positivity
  have hratio_le : (L / Y) ^ 2 ≤ 1 := by
    rw [div_pow]
    apply (div_le_one₀ (by positivity)).2
    nlinarith [sq_nonneg (Y - L)]
  have hidentity : S2 / Y ^ 2 = (S2 / L ^ 2) * (L / Y) ^ 2 := by
    field_simp [ne_of_gt hL, ne_of_gt hY]
  rw [hidentity]
  calc
    (S2 / L ^ 2) * (L / Y) ^ 2 ≤
        (4 / H + 4 / (H * L) * C) * (L / Y) ^ 2 :=
      mul_le_mul_of_nonneg_right hlocal hratio
    _ ≤ 4 / H + 4 / (H * Y) * C := by
      have hconst : (4 / H) * (L / Y) ^ 2 ≤ 4 / H :=
        mul_le_of_le_one_right (by positivity) hratio_le
      have hcorr : (4 / (H * L) * C) * (L / Y) ^ 2 ≤
          4 / (H * Y) * C := by
        field_simp [ne_of_gt hH, ne_of_gt hL, ne_of_gt hY]
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hLY)]
      nlinarith

theorem realForwardDifference_commute (a b : ℕ) (f : ℝ → ℝ) :
    realForwardDifference a (realForwardDifference b f) =
      realForwardDifference b (realForwardDifference a f) := by
  funext t
  simp only [realForwardDifference]
  have hshift : t + (a : ℝ) + (b : ℝ) = t + (b : ℝ) + (a : ℝ) := by ring
  rw [hshift]
  ring

theorem iteratedRealForwardDifference_head
    (f : ℝ → ℝ) (d : ℕ) (tail : List ℕ) :
    iteratedRealForwardDifference f (d :: tail) =
      realForwardDifference d (iteratedRealForwardDifference f tail) := by
  change iteratedRealForwardDifference (realForwardDifference d f) tail = _
  induction tail generalizing f with
  | nil => rfl
  | cons a rest ih =>
      simp only [iteratedRealForwardDifference]
      rw [show realForwardDifference a (realForwardDifference d f) =
          realForwardDifference d (realForwardDifference a f) from
            realForwardDifference_commute a d f]
      exact ih (realForwardDifference a f)

theorem iteratedRealForwardDifference_commute_single
    (f : ℝ → ℝ) (d : ℕ) (shifts : List ℕ) :
    iteratedRealForwardDifference (realForwardDifference d f) shifts =
      realForwardDifference d (iteratedRealForwardDifference f shifts) := by
  induction shifts generalizing f with
  | nil => rfl
  | cons a rest ih =>
      simp only [iteratedRealForwardDifference]
      rw [realForwardDifference_commute a d f, ih]

theorem iteratedRealForwardDifference_reverse
    (f : ℝ → ℝ) (shifts : List ℕ) :
    iteratedRealForwardDifference f shifts.reverse =
      iteratedRealForwardDifference f shifts := by
  induction shifts generalizing f with
  | nil => rfl
  | cons a rest ih =>
      calc
        iteratedRealForwardDifference f (a :: rest).reverse =
            realForwardDifference a
              (iteratedRealForwardDifference f rest.reverse) := by
                rw [List.reverse_cons, iteratedRealForwardDifference_append_singleton]
        _ = realForwardDifference a (iteratedRealForwardDifference f rest) := by
          rw [ih]
        _ = iteratedRealForwardDifference (realForwardDifference a f) rest :=
          (iteratedRealForwardDifference_commute_single f a rest).symm
        _ = iteratedRealForwardDifference f (a :: rest) := rfl

theorem averagedIteratedCorrelation_reverse
    (f : ℝ → ℝ) (x Y : ℝ) (bounds : List ℕ) :
    averagedIteratedCorrelation f x Y bounds.reverse =
      averagedIteratedCorrelation f x Y bounds := by
  let g : List ℕ → ℝ := fun shifts =>
    ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
      realExponentialPhase (iteratedRealForwardDifference f shifts) n‖
  have hterm (shifts : List ℕ) : g shifts.reverse = g shifts := by
    simp [g, iteratedDifferenceInterval, realShiftTotal_reverse,
      iteratedRealForwardDifference_reverse]
  have hsum : (∑ shifts ∈ positiveShiftBox bounds.reverse, g shifts) =
      ∑ shifts ∈ positiveShiftBox bounds, g shifts := by
    rw [← sum_positiveShiftBox_reverse bounds g]
    apply Finset.sum_congr rfl
    intro shifts hshifts
    exact hterm shifts
  unfold averagedIteratedCorrelation
  change (Y * realShiftNormalizer bounds.reverse)⁻¹ *
      (∑ shifts ∈ positiveShiftBox bounds.reverse, g shifts) =
    (Y * realShiftNormalizer bounds)⁻¹ *
      (∑ shifts ∈ positiveShiftBox bounds, g shifts)
  rw [realShiftNormalizer_reverse, hsum]

theorem realShiftTotal_nonneg (shifts : List ℕ) : 0 ≤ realShiftTotal shifts := by
  induction shifts with
  | nil => simp [realShiftTotal]
  | cons a rest ih =>
      change 0 ≤ (a : ℝ) + realShiftTotal rest
      exact add_nonneg (Nat.cast_nonneg a) ih

theorem realShiftNormalizer_pos (bounds : List ℕ)
    (hpos : ∀ H ∈ bounds, 0 < H) : 0 < realShiftNormalizer bounds := by
  induction bounds with
  | nil => simp [realShiftNormalizer]
  | cons H rest ih =>
      have hH : 0 < (H : ℝ) := by exact_mod_cast hpos H (by simp)
      have hrest : ∀ K ∈ rest, 0 < K := by
        intro K hK
        exact hpos K (by simp [hK])
      have hprod := ih hrest
      change 0 < (H : ℝ) * realShiftNormalizer rest
      exact mul_pos hH hprod

theorem realShiftNormalizer_cons (H : ℕ) (bounds : List ℕ) :
    realShiftNormalizer (H :: bounds) =
      (H : ℝ) * realShiftNormalizer bounds := by
  simp [realShiftNormalizer]

theorem realShiftPlusNormalizer_cons (H : ℕ) (bounds : List ℕ) :
    realShiftPlusNormalizer (H :: bounds) =
      ((H + 1 : ℕ) : ℝ) * realShiftPlusNormalizer bounds := by
  simp [realShiftPlusNormalizer, List.map_cons]

theorem realShiftPlusNormalizer_pos (bounds : List ℕ)
    (hpos : ∀ H ∈ bounds, 0 < H) : 0 < realShiftPlusNormalizer bounds := by
  induction bounds with
  | nil => simp [realShiftPlusNormalizer]
  | cons H rest ih =>
      have hH := hpos H (by simp)
      have hrest : ∀ K ∈ rest, 0 < K := by
        intro K hK
        exact hpos K (by simp [hK])
      rw [realShiftPlusNormalizer_cons]
      exact mul_pos (by positivity) (ih hrest)

theorem reciprocal_coordinate_product_normalization (bounds : List ℕ)
    (hpos : ∀ H ∈ bounds, 0 < H) :
    (List.map (fun H : ℕ =>
      2 * (H : ℝ) / Real.sqrt ((H + 1 : ℕ) : ℝ)) bounds).prod =
      (2 : ℝ) ^ bounds.length * realShiftNormalizer bounds /
        Real.sqrt (realShiftPlusNormalizer bounds) := by
  induction bounds with
  | nil => simp [realShiftNormalizer, realShiftPlusNormalizer]
  | cons H rest ih =>
      have hHpos := hpos H (by simp)
      have hrest : ∀ K ∈ rest, 0 < K := by
        intro K hK
        exact hpos K (by simp [hK])
      have hqpos := realShiftPlusNormalizer_pos rest hrest
      have hsqrtH : 0 < Real.sqrt ((H + 1 : ℕ) : ℝ) := by positivity
      have hsqrtQ : 0 < Real.sqrt (realShiftPlusNormalizer rest) :=
        Real.sqrt_pos.2 hqpos
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [realShiftPlusNormalizer_cons, realShiftNormalizer_cons,
        Real.sqrt_mul (by positivity)]
      rw [ih hrest, pow_succ]
      field_simp [ne_of_gt hsqrtH, ne_of_gt hsqrtQ]

theorem norm_realIntervalPhase_le_one
    (f : ℝ → ℝ) (x L : ℝ) (n : ℤ) :
    ‖realIntervalPhase f x L n‖ ≤ 1 := by
  by_cases hn : n ∈ realIntegerInterval x L
  · simp [realIntervalPhase, hn, norm_realExponentialPhase]
  · simp [realIntervalPhase, hn]

theorem realIntervalPhase_zero_of_not_mem
    (f : ℝ → ℝ) (x L : ℝ) (n : ℤ)
    (hn : n ∉ realIntegerInterval x L) : realIntervalPhase f x L n = 0 := by
  simp [realIntervalPhase, hn]

theorem realIntervalPhase_sum (f : ℝ → ℝ) (x L : ℝ) :
    (∑ n ∈ realIntegerInterval x L, realIntervalPhase f x L n) =
      ∑ n ∈ realIntegerInterval x L, realExponentialPhase f n := by
  apply Finset.sum_congr rfl
  intro n hn
  simp [realIntervalPhase, hn]

theorem complex_norm_div_real_sq (z : ℂ) (y : ℝ) (hy : 0 < y) :
    ‖z / (y : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / y ^ 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  ring


/-- The constant used in the blueprint's repeated Weyl differencing step. -/
noncomputable def derivativeWeylConstant : ℝ := 2 + 2 * Real.sqrt 2

theorem derivativeWeylConstant_pos : 0 < derivativeWeylConstant := by
  rw [derivativeWeylConstant]
  positivity

theorem derivativeWeylConstant_identity :
    4 / derivativeWeylConstant ^ 2 + 4 / derivativeWeylConstant = 1 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos := derivativeWeylConstant_pos
  dsimp [derivativeWeylConstant]
  field_simp
  nlinarith [hsqrt]

/-- Scalar max estimate that turns one Weyl correlation recurrence into the
next repeated-differencing bound. -/
theorem derivativeWeyl_scalar_step {B H T : ℝ} (hB : 0 < B) (hH : 0 < H)
    (hT : 0 ≤ T) (hidentity : 4 / B ^ 2 + 4 / B = 1) :
    4 / H + 4 * T ≤ max (B ^ 2 / H) (B * T) := by
  have hmax₁ : B ^ 2 / H ≤ max (B ^ 2 / H) (B * T) := le_max_left _ _
  have hmax₂ : B * T ≤ max (B ^ 2 / H) (B * T) := le_max_right _ _
  have hcoeff₁ : 0 ≤ 4 / B ^ 2 := by positivity
  have hcoeff₂ : 0 ≤ 4 / B := by positivity
  calc
    4 / H + 4 * T = (4 / B ^ 2) * (B ^ 2 / H) + (4 / B) * (B * T) := by
      field_simp
    _ ≤ (4 / B ^ 2) * max (B ^ 2 / H) (B * T) +
        (4 / B) * max (B ^ 2 / H) (B * T) :=
      add_le_add (mul_le_mul_of_nonneg_left hmax₁ hcoeff₁)
        (mul_le_mul_of_nonneg_left hmax₂ hcoeff₂)
    _ = max (B ^ 2 / H) (B * T) := by
      rw [← add_mul, hidentity, one_mul]

/-- Finite Cauchy--Schwarz for complex sums, expressed using the sum of
squared moduli. -/
theorem complex_norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hre : (∑ i ∈ s, Complex.re (f i)) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, (Complex.re (f i)) ^ 2 := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ι => (1 : ℝ))
      (fun i => Complex.re (f i)))
  have him : (∑ i ∈ s, Complex.im (f i)) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, (Complex.im (f i)) ^ 2 := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ι => (1 : ℝ))
      (fun i => Complex.im (f i)))
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 =
        (∑ i ∈ s, Complex.re (f i)) ^ 2 +
          (∑ i ∈ s, Complex.im (f i)) ^ 2 := by
            rw [RCLike.norm_sq_eq_def, map_sum, map_sum]
            have hre : (∑ i ∈ s, Complex.re (f i)) =
                ∑ i ∈ s, RCLike.re (f i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rfl
            have him : (∑ i ∈ s, Complex.im (f i)) =
                ∑ i ∈ s, RCLike.im (f i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rfl
            rw [hre, him]
            ring_nf
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (Complex.re (f i)) ^ 2 +
        (s.card : ℝ) * ∑ i ∈ s, (Complex.im (f i)) ^ 2 := add_le_add hre him
    _ = (s.card : ℝ) * ∑ i ∈ s,
          ((Complex.re (f i)) ^ 2 + (Complex.im (f i)) ^ 2) := by
            rw [Finset.sum_add_distrib, ← mul_add]
    _ = (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [RCLike.norm_sq_eq_def]
          change (f i).re ^ 2 + (f i).im ^ 2 =
            (f i).re * (f i).re + (f i).im * (f i).im
          ring

/-- Exact polarization expansion of the squared modulus of a finite complex
sum. -/
theorem complex_norm_sum_sq_eq_re_double_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (f i * star (f j)).re := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [RCLike.inner_apply]
  rw [map_sum]
  rw [Finset.sum_mul_sum]
  simp_rw [map_sum]
  rfl

/-- Translation invariance of a finite integer interval sum, in the form used
to move a correlation sum back to the original support interval. -/
theorem sum_Ico_int_translate (u : ℤ → ℂ) (l r a : ℤ) :
    (∑ n ∈ Finset.Ico (l + a) (r + a), u (n - a)) =
      ∑ n ∈ Finset.Ico l r, u n := by
  simpa only [add_sub_cancel_right] using
    (Finset.sum_Ico_add' (fun n : ℤ => u (n - a)) l r a).symm

/-- A finite forward convolution of a sequence supported on an integer
interval is supported on the interval extended by its shift range. -/
theorem int_intervalConvolution_zero_of_not_mem {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (H : ℕ) {n : ℤ}
    (hn : n ∉ Finset.Ico l (r + H)) :
    (∑ a ∈ Finset.range H, u (n - (a : ℤ))) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  apply hsupp
  intro hmem
  have hmem' : n - (a : ℤ) ∈ Finset.Ico l r := hmem
  have ha0 : 0 ≤ (a : ℤ) := by exact_mod_cast Nat.zero_le a
  have haH : (a : ℤ) < (H : ℤ) := by
    exact_mod_cast Finset.mem_range.mp ha
  have hnmem : n ∈ Finset.Ico l (r + H) := by
    simp only [Finset.mem_Ico]
    simp only [Finset.mem_Ico] at hmem'
    constructor <;> omega
  exact hn hnmem

/-- The final nonzero output of the convolution is one point before `r+H`;
this sharp support bound is needed for the `N+H-1` Cauchy--Schwarz factor. -/
theorem int_intervalConvolution_zero_of_not_mem_tight {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (H : ℕ) (hH : 1 ≤ H)
    {n : ℤ} (hn : n ∉ Finset.Ico l (r + (H - 1 : ℕ))) :
    (∑ a ∈ Finset.range H, u (n - (a : ℤ))) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  apply hsupp
  intro hmem
  have hmem' : n - (a : ℤ) ∈ Finset.Ico l r := hmem
  have haH : (a : ℤ) ≤ (H - 1 : ℤ) := by
    exact_mod_cast (Nat.le_pred_of_lt (Finset.mem_range.mp ha))
  simp only [Finset.mem_Ico] at hmem'
  have hnmem : n ∈ Finset.Ico l (r + (H - 1 : ℕ)) := by
    simp only [Finset.mem_Ico]
    constructor <;> omega
  exact hn hnmem

/-- The squared energy on the wider bookkeeping interval equals the energy on
the exact support interval. -/
theorem int_intervalConvolution_energy_eq_tight {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (H : ℕ) (hH : 1 ≤ H) :
    (∑ n ∈ Finset.Ico l (r + H),
      ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2) =
      ∑ n ∈ Finset.Ico l (r + (H - 1 : ℕ)),
        ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2 := by
  let f : ℤ → ℝ := fun n => ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2
  have hsub : Finset.Ico l (r + (H - 1 : ℕ)) ⊆ Finset.Ico l (r + H) := by
    intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    constructor
    · exact hn.1
    · omega
  have hsum : (∑ n ∈ Finset.Ico l (r + (H - 1 : ℕ)), f n) =
      ∑ n ∈ Finset.Ico l (r + H), f n := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hz := int_intervalConvolution_zero_of_not_mem_tight hsupp H hH hnot
    simp [f, hz]
  simpa [f] using hsum.symm


/-- The sum of the finite forward convolution over its containing interval is
the shift count times the original sum. -/
theorem int_intervalConvolution_sum {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (H : ℕ) :
    (∑ n ∈ Finset.Ico l (r + H), ∑ a ∈ Finset.range H,
      u (n - (a : ℤ))) =
      (H : ℂ) * ∑ n ∈ Finset.Ico l r, u n := by
  calc
    (∑ n ∈ Finset.Ico l (r + H), ∑ a ∈ Finset.range H,
        u (n - (a : ℤ))) =
      ∑ a ∈ Finset.range H, ∑ n ∈ Finset.Ico l (r + H),
        u (n - (a : ℤ)) := Finset.sum_comm
    _ = ∑ a ∈ Finset.range H, ∑ n ∈ Finset.Ico l r, u n := by
      apply Finset.sum_congr rfl
      intro a ha
      have haH : (a : ℤ) < (H : ℤ) := by
        exact_mod_cast Finset.mem_range.mp ha
      have ha0 : 0 ≤ (a : ℤ) := by exact_mod_cast Nat.zero_le a
      have hsub : Finset.Ico (l + (a : ℤ)) (r + (a : ℤ)) ⊆
          Finset.Ico l (r + H) := by
        intro n hn
        simp only [Finset.mem_Ico] at hn ⊢
        constructor <;> omega
      have hzero : ∀ n ∈ Finset.Ico l (r + H),
          n ∉ Finset.Ico (l + (a : ℤ)) (r + (a : ℤ)) →
          u (n - (a : ℤ)) = 0 := by
        intro n hn hnot
        apply hsupp
        intro hmem
        simp only [Finset.mem_Ico] at hmem
        apply hnot
        simp only [Finset.mem_Ico]
        constructor <;> omega
      have hsum : (∑ n ∈ Finset.Ico (l + (a : ℤ)) (r + (a : ℤ)),
          u (n - (a : ℤ))) = ∑ n ∈ Finset.Ico l (r + H),
            u (n - (a : ℤ)) :=
        Finset.sum_subset hsub hzero
      rw [← hsum, sum_Ico_int_translate]
    _ = (H : ℂ) * ∑ n ∈ Finset.Ico l r, u n := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The convolution mass can also be summed over its exact support interval. -/
theorem int_intervalConvolution_sum_eq_tight {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (H : ℕ) (hH : 1 ≤ H) :
    (∑ n ∈ Finset.Ico l (r + (H - 1 : ℕ)),
      ∑ a ∈ Finset.range H, u (n - (a : ℤ))) =
      (H : ℂ) * ∑ n ∈ Finset.Ico l r, u n := by
  calc
    (∑ n ∈ Finset.Ico l (r + (H - 1 : ℕ)),
        ∑ a ∈ Finset.range H, u (n - (a : ℤ))) =
      ∑ n ∈ Finset.Ico l (r + H),
        ∑ a ∈ Finset.range H, u (n - (a : ℤ)) := by
          let f : ℤ → ℂ := fun n => ∑ a ∈ Finset.range H, u (n - (a : ℤ))
          have hsub : Finset.Ico l (r + (H - 1 : ℕ)) ⊆ Finset.Ico l (r + H) := by
            intro n hn
            simp only [Finset.mem_Ico] at hn ⊢
            constructor
            · exact hn.1
            · omega
          have hsum : (∑ n ∈ Finset.Ico l (r + (H - 1 : ℕ)), f n) =
              ∑ n ∈ Finset.Ico l (r + H), f n := by
            apply Finset.sum_subset hsub
            intro n hn hnot
            have hz := int_intervalConvolution_zero_of_not_mem_tight hsupp H hH hnot
            simp [f, hz]
          simpa [f] using hsum
    _ = (H : ℂ) * ∑ n ∈ Finset.Ico l r, u n :=
      int_intervalConvolution_sum hsupp H

/-- A translated finite correlation sum reduces to the original support
interval when the unshifted sequence is supported there. -/
theorem int_intervalCorrelation_shift_sum {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (H b : ℕ)
    (hb : b < H) (d : ℤ) :
    (∑ n ∈ Finset.Ico l (r + H),
      u (n - (b : ℤ) + d) * star (u (n - (b : ℤ)))) =
      ∑ n ∈ Finset.Ico l r, u (n + d) * star (u n) := by
  let F : ℤ → ℂ := fun m => u (m + d) * star (u m)
  have hb0 : 0 ≤ (b : ℤ) := by exact_mod_cast Nat.zero_le b
  have hbH : (b : ℤ) < (H : ℤ) := by exact_mod_cast hb
  have htrans : (∑ n ∈ Finset.Ico l (r + H), F (n - (b : ℤ))) =
      ∑ n ∈ Finset.Ico (l - (b : ℤ)) (r + H - (b : ℤ)), F n := by
    simpa [F, sub_add_cancel] using
      (Finset.sum_Ico_add_right_sub_eq (f := F) (l - (b : ℤ))
        (r + H - (b : ℤ)) (b : ℤ))
  have hsub : Finset.Ico l r ⊆
      Finset.Ico (l - (b : ℤ)) (r + H - (b : ℤ)) := by
    intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    constructor <;> omega
  have hzero : ∀ n ∈ Finset.Ico (l - (b : ℤ)) (r + H - (b : ℤ)),
      n ∉ Finset.Ico l r → F n = 0 := by
    intro n hn hnot
    have hUn : u n = 0 := hsupp n hnot
    simp [F, hUn]
  calc
    (∑ n ∈ Finset.Ico l (r + H),
        u (n - (b : ℤ) + d) * star (u (n - (b : ℤ)))) =
      ∑ n ∈ Finset.Ico (l - (b : ℤ)) (r + H - (b : ℤ)), F n := by
        simpa [F, add_assoc] using htrans
    _ = ∑ n ∈ Finset.Ico l r, F n :=
      (Finset.sum_subset hsub hzero).symm
    _ = ∑ n ∈ Finset.Ico l r, u (n + d) * star (u n) := by rfl

/-- Opposite correlations of an interval-supported sequence are complex
conjugates. -/
theorem int_intervalCorrelation_neg_eq_star {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (d : ℤ) :
    (∑ n ∈ Finset.Ico l r, u (n - d) * star (u n)) =
      star (∑ n ∈ Finset.Ico l r, u (n + d) * star (u n)) := by
  let S : Finset ℤ := Finset.Ico l r
  let Sd : Finset ℤ := Finset.Ico (l + d) (r + d)
  let G : ℤ → ℂ := fun n => u (n - d) * star (u n)
  have htrans : (∑ n ∈ S, u (n + d) * star (u n)) =
      ∑ n ∈ Sd, u n * star (u (n - d)) := by
    simpa [S, Sd, sub_add_cancel] using
      (Finset.sum_Ico_add' (fun n : ℤ => u n * star (u (n - d))) l r d)
  have hsubS : S ∩ Sd ⊆ S := Finset.inter_subset_left
  have hsubSd : S ∩ Sd ⊆ Sd := Finset.inter_subset_right
  have hzeroS : ∀ n ∈ S, n ∉ S ∩ Sd → G n = 0 := by
    intro n hn hnot
    have hnSd : n ∉ Sd := by
      intro hn'
      exact hnot (Finset.mem_inter.mpr ⟨hn, hn'⟩)
    have hnd : n - d ∉ S := by
      intro hmem
      have hn' : n ∈ Finset.Ico (l + d) (r + d) := by
        change n ∈ Finset.Ico l r at hn
        change n - d ∈ Finset.Ico l r at hmem
        rw [Finset.mem_Ico] at hn hmem ⊢
        constructor <;> omega
      exact hnSd (by simpa [Sd] using hn')
    have hu := hsupp (n - d) hnd
    simp [G, hu]
  have hzeroSd : ∀ n ∈ Sd, n ∉ S ∩ Sd → G n = 0 := by
    intro n hn hnot
    have hnS : n ∉ S := by
      intro hn'
      exact hnot (Finset.mem_inter.mpr ⟨hn', hn⟩)
    have hu := hsupp n hnS
    simp [G, hu]
  have hleft : (∑ n ∈ S, G n) = ∑ n ∈ S ∩ Sd, G n := by
    symm
    exact Finset.sum_subset hsubS hzeroS
  have hright : (∑ n ∈ Sd, G n) = ∑ n ∈ S ∩ Sd, G n := by
    symm
    exact Finset.sum_subset hsubSd hzeroSd
  calc
    (∑ n ∈ S, G n) = ∑ n ∈ Sd, G n := hleft.trans hright.symm
    _ = ∑ n ∈ Sd, star (u n * star (u (n - d))) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [G, mul_comm]
    _ = star (∑ n ∈ Sd, u n * star (u (n - d))) := by
      exact (map_sum (starRingEnd ℂ)
        (fun n : ℤ => u n * star (u (n - d))) Sd).symm
    _ = star (∑ n ∈ S, u (n + d) * star (u n)) := by
      exact congrArg star htrans.symm

/-- Exact all-pairs energy expansion for a finite forward convolution. Each
pair of shifts contributes the correlation at its difference. -/
theorem int_intervalConvolution_energy_eq_doubleCorrelation
    {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (H : ℕ) :
    (∑ n ∈ Finset.Ico l (r + H),
      ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2) =
      ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        RCLike.re (∑ m ∈ Finset.Ico l r,
          u (m + (j : ℤ) - (i : ℤ)) * star (u m)) := by
  calc
    (∑ n ∈ Finset.Ico l (r + H),
        ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2) =
      ∑ n ∈ Finset.Ico l (r + H),
        ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
          RCLike.re (u (n - (i : ℤ)) * star (u (n - (j : ℤ)))) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact complex_norm_sum_sq_eq_re_double_sum (Finset.range H)
          (fun a => u (n - (a : ℤ)))
    _ = ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        ∑ n ∈ Finset.Ico l (r + H),
          RCLike.re (u (n - (i : ℤ)) * star (u (n - (j : ℤ)))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        RCLike.re (∑ m ∈ Finset.Ico l r,
          u (m + (j : ℤ) - (i : ℤ)) * star (u m)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        have hcorr := int_intervalCorrelation_shift_sum hsupp H j
          (Finset.mem_range.mp hj) ((j : ℤ) - (i : ℤ))
        rw [← map_sum]
        congr 1
        calc
          (∑ n ∈ Finset.Ico l (r + H),
              u (n - (i : ℤ)) * star (u (n - (j : ℤ)))) =
            ∑ n ∈ Finset.Ico l (r + H),
              u (n - (j : ℤ) + ((j : ℤ) - (i : ℤ))) * star (u (n - (j : ℤ))) := by
                apply Finset.sum_congr rfl
                intro n hn
                congr 2; ring

          _ = ∑ n ∈ Finset.Ico l r,
              u (n + ((j : ℤ) - (i : ℤ))) * star (u n) := hcorr
          _ = ∑ n ∈ Finset.Ico l r,
              u (n + (j : ℤ) - (i : ℤ)) * star (u n) := by
                apply Finset.sum_congr rfl
                intro n hn
                congr 2; ring

/-- The pairs `(i,i+d)` with `i < H-d` are exactly the ordered shift pairs
in `[0,H)` whose second coordinate exceeds the first by `d`. -/
theorem mem_natShiftPair_image_iff (H d : ℕ) (p : ℕ × ℕ) :
    p ∈ (Finset.range (H - d)).image (fun i : ℕ => (i, i + d)) ↔
      p.1 < H ∧ p.2 < H ∧ p.2 = p.1 + d := by
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hp⟩
    have hp₁ : p.1 = i := congrArg Prod.fst hp.symm
    have hp₂ : p.2 = i + d := congrArg Prod.snd hp.symm
    subst p
    omega
  · rintro ⟨hp₁, hp₂, hdiff⟩
    refine ⟨p.1, ?_, Prod.ext rfl hdiff.symm⟩
    omega

/-- Count ordered shift pairs in `[0,H)` whose second coordinate exceeds the
first by a fixed natural offset. -/
theorem natShiftPair_card (H d : ℕ) :
    ((Finset.range (H - d)).image (fun i : ℕ => (i, i + d))).card = H - d := by
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj hij
    exact congrArg Prod.fst hij

/-- Mathlib's diagonal-flip theorem reindexes the triangular range that
appears before difference fibers are collected. -/
theorem nat_triangle_shift_sum_flip (H : ℕ) (F : ℕ → ℝ) :
    (∑ d ∈ Finset.Ico 1 H, ∑ i ∈ Finset.range d, F (d - i)) =
      ∑ m ∈ Finset.range (H - 1),
        ∑ k ∈ Finset.range ((H - 1) - m), F (k + 1) := by
  calc
    (∑ d ∈ Finset.Ico 1 H, ∑ i ∈ Finset.range d, F (d - i)) =
        ∑ m ∈ Finset.range (H - 1),
          ∑ i ∈ Finset.range (m + 1), F ((m + 1) - i) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.one_add, Nat.add_one]
    _ = ∑ m ∈ Finset.range (H - 1),
          ∑ k ∈ Finset.range ((H - 1) - m), F (k + 1) := by
      have h := Finset.sum_range_diag_flip (H - 1)
        (fun k q => F (q + 1))
      calc
        (∑ m ∈ Finset.range (H - 1),
            ∑ i ∈ Finset.range (m + 1), F ((m + 1) - i)) =
          ∑ m ∈ Finset.range (H - 1),
            ∑ i ∈ Finset.range (m + 1), F ((m - i) + 1) := by
              apply Finset.sum_congr rfl
              intro m hm
              apply Finset.sum_congr rfl
              intro i hi
              congr 1
              have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              omega
        _ = ∑ m ∈ Finset.range (H - 1),
            ∑ i ∈ Finset.range (m + 1), F (m - i + 1) := rfl
        _ = ∑ m ∈ Finset.range (H - 1),
            ∑ k ∈ Finset.range ((H - 1) - m), F (k + 1) := h

/-- Transpose a finite triangle and collect a term by its second index. -/
theorem nat_triangle_transpose_sum {M : Type*} [AddCommMonoid M]
    (n : ℕ) (G : ℕ → M) :
    (∑ m ∈ Finset.range n, ∑ k ∈ Finset.range (n - m), G k) =
      ∑ k ∈ Finset.range n, (n - k) • G k := by
  calc
    (∑ m ∈ Finset.range n, ∑ k ∈ Finset.range (n - m), G k) =
        ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range (m + 1), G (m - k) := by
      rw [← Finset.sum_range_diag_flip n (fun _ k => G k)]
    _ = ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range (m + 1), G k := by
      apply Finset.sum_congr rfl
      intro m hm
      simpa [Nat.sub_sub] using (Finset.sum_range_reflect G (m + 1))
    _ = ∑ k ∈ Finset.range n, ∑ m ∈ Finset.Ico k n, G k := by
      simp only [Finset.range_eq_Ico]
      exact (Finset.sum_Ico_Ico_comm 0 n (fun i j => G i)).symm
    _ = ∑ k ∈ Finset.range n, (n - k) • G k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.sum_const, Nat.card_Ico]

/-- Collect the positive differences in the strict shift triangle with their
exact multiplicities. -/
theorem nat_triangle_shift_sum (H : ℕ) (F : ℕ → ℝ) :
    (∑ d ∈ Finset.Ico 1 H, ∑ i ∈ Finset.range d, F (d - i)) =
      ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * F d := by
  calc
    (∑ d ∈ Finset.Ico 1 H, ∑ i ∈ Finset.range d, F (d - i)) =
        ∑ m ∈ Finset.range (H - 1),
          ∑ k ∈ Finset.range ((H - 1) - m), F (k + 1) :=
      nat_triangle_shift_sum_flip H F
    _ = ∑ k ∈ Finset.range (H - 1),
          ((H - 1 - k : ℕ) : ℝ) * F (k + 1) := by
      rw [nat_triangle_transpose_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [nsmul_eq_mul]
    _ = ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * F d := by
      symm
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hsub : H - (1 + k) = H - 1 - k := by omega
      rw [hsub]
      simp only [Nat.one_add, Nat.add_one]

/-- Positive off-diagonal differences in a square of shifts have multiplicity
`H-d`. -/
theorem real_upperTriangle_shift_sum (H : ℕ) (hH : 1 ≤ H)
    (F : ℤ → ℝ) :
    (∑ i ∈ Finset.range H, ∑ j ∈ Finset.Ico (i + 1) H,
      F ((j : ℤ) - (i : ℤ))) =
      ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * F d := by
  have hcomm := Finset.sum_Ico_Ico_comm' 0 H
    (fun i j => F ((j : ℤ) - (i : ℤ)))
  have htriangle :
      (∑ i ∈ Finset.range H, ∑ j ∈ Finset.Ico (i + 1) H,
        F ((j : ℤ) - (i : ℤ))) =
      ∑ j ∈ Finset.range H, ∑ i ∈ Finset.range j,
        F ((j : ℤ) - (i : ℤ)) := by
    simpa only [Finset.range_eq_Ico] using hcomm
  have hremoveZero :
      (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range j,
        F ((j : ℤ) - (i : ℤ))) =
      ∑ d ∈ Finset.Ico 1 H, ∑ i ∈ Finset.range d,
        F ((d : ℤ) - (i : ℤ)) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hH]
    simp only [Finset.range_eq_Ico, Finset.Ico_self, Finset.sum_empty,
      zero_add]
  rw [htriangle, hremoveZero]
  calc
    (∑ d ∈ Finset.Ico 1 H, ∑ i ∈ Finset.range d,
        F ((d : ℤ) - (i : ℤ))) =
      ∑ d ∈ Finset.Ico 1 H, ∑ i ∈ Finset.range d,
        (fun n : ℕ => F (n : ℤ)) (d - i) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          symm
          exact_mod_cast (Nat.cast_sub (Nat.le_of_lt (Finset.mem_range.mp hi)))
    _ = ∑ d ∈ Finset.Ico 1 H,
          ((H - d : ℕ) : ℝ) * (fun n : ℕ => F (n : ℤ)) d :=
        nat_triangle_shift_sum H (fun n => F (n : ℤ))
    _ = ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * F d := by
      rfl

/-- Under opposite-difference symmetry, the lower and upper shift triangles
have equal sums. -/
theorem real_lowerTriangle_eq_upper {H : ℕ} (F : ℤ → ℝ)
    (hsym : ∀ d, F (-d) = F d) :
    (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range i,
      F ((j : ℤ) - (i : ℤ))) =
      ∑ i ∈ Finset.range H, ∑ j ∈ Finset.Ico (i + 1) H,
        F ((j : ℤ) - (i : ℤ)) := by
  let lower := ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range i,
    F ((j : ℤ) - (i : ℤ))
  let upper := ∑ i ∈ Finset.range H, ∑ j ∈ Finset.Ico (i + 1) H,
    F ((j : ℤ) - (i : ℤ))
  let swappedUpper := ∑ i ∈ Finset.Ico 0 H, ∑ j ∈ Finset.Ico (i + 1) H,
    F ((i : ℤ) - (j : ℤ))
  have hsymUpper : upper = swappedUpper := by
    dsimp [upper, swappedUpper]
    rw [Finset.range_eq_Ico]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have h := hsym ((j : ℤ) - (i : ℤ))
    rw [show (i : ℤ) - (j : ℤ) = -((j : ℤ) - (i : ℤ)) by ring]
    exact h.symm
  have hcomm := Finset.sum_Ico_Ico_comm' 0 H
    (fun i j => F ((i : ℤ) - (j : ℤ)))
  have hcomm' : swappedUpper = lower := by
    simpa only [Finset.range_eq_Ico, lower] using hcomm
  calc
    lower = upper := by
      rw [← hcomm', ← hsymUpper]

/-- Exact sum over all ordered shift pairs, grouped into the diagonal and the
two strict triangles. -/
theorem real_allPairs_shift_sum (H : ℕ) (hH : 1 ≤ H)
    (F : ℤ → ℝ) (hsym : ∀ d, F (-d) = F d) :
    (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
      F ((j : ℤ) - (i : ℤ))) =
      (H : ℝ) * F 0 +
        2 * ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * F d := by
  have hsplit (i : ℕ) (hi : i < H) :
      (∑ j ∈ Finset.range H, F ((j : ℤ) - (i : ℤ))) =
        (∑ j ∈ Finset.range i, F ((j : ℤ) - (i : ℤ))) +
          F 0 + ∑ j ∈ Finset.Ico (i + 1) H, F ((j : ℤ) - (i : ℤ)) := by
    rw [← Finset.sum_range_add_sum_Ico (fun j => F ((j : ℤ) - (i : ℤ)))
      (Nat.succ_le_of_lt hi)]
    rw [Finset.sum_range_succ]
    simp only [sub_self]
  calc
    (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        F ((j : ℤ) - (i : ℤ))) =
      ∑ i ∈ Finset.range H,
        ((∑ j ∈ Finset.range i, F ((j : ℤ) - (i : ℤ))) + F 0 +
          ∑ j ∈ Finset.Ico (i + 1) H, F ((j : ℤ) - (i : ℤ))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsplit i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range i,
          F ((j : ℤ) - (i : ℤ))) +
        (H : ℝ) * F 0 +
        ∑ i ∈ Finset.range H, ∑ j ∈ Finset.Ico (i + 1) H,
          F ((j : ℤ) - (i : ℤ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (H : ℝ) * F 0 +
        2 * ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * F d := by
        rw [real_lowerTriangle_eq_upper F hsym,
          real_upperTriangle_shift_sum H hH F]
        ring

/-- The convolution energy has the exact diagonal and positive-correlation
expansion used in the safe Weyl estimate. -/
theorem int_intervalConvolution_energy_eq_weightedCorrelation
    {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (H : ℕ) (hH : 1 ≤ H) :
    (∑ n ∈ Finset.Ico l (r + H),
      ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2) =
      (H : ℝ) * ∑ m ∈ Finset.Ico l r, ‖u m‖ ^ 2 +
        2 * ∑ d ∈ Finset.Ico 1 H,
          ((H - d : ℕ) : ℝ) * RCLike.re
            (∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)) := by
  let C : ℤ → ℂ := fun d =>
    ∑ m ∈ Finset.Ico l r, u (m + d) * star (u m)
  let F : ℤ → ℝ := fun d => RCLike.re (C d)
  have hsym : ∀ d, F (-d) = F d := by
    intro d
    have h := int_intervalCorrelation_neg_eq_star hsupp d
    dsimp [F, C]
    have h' := congrArg RCLike.re h
    simpa [Complex.star_def, map_sum, sub_eq_add_neg] using h'
  have hdiag : F 0 = ∑ m ∈ Finset.Ico l r, ‖u m‖ ^ 2 := by
    dsimp [F, C]
    simp only [add_zero]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmul := congrArg RCLike.re (RCLike.mul_conj (u m))
    simpa [Complex.star_def, ← Complex.ofReal_pow, Complex.ofReal_re] using hmul
  have henergy := int_intervalConvolution_energy_eq_doubleCorrelation hsupp H
  calc
    (∑ n ∈ Finset.Ico l (r + H),
        ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2) =
      ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        F ((j : ℤ) - (i : ℤ)) := by
          rw [henergy]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [F, C]
          congr 1
          apply Finset.sum_congr rfl
          intro m hm
          congr 2; ring
    _ = (H : ℝ) * F 0 +
        2 * ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * F d :=
      real_allPairs_shift_sum H hH F hsym
    _ = (H : ℝ) * ∑ m ∈ Finset.Ico l r, ‖u m‖ ^ 2 +
        2 * ∑ d ∈ Finset.Ico 1 H,
          ((H - d : ℕ) : ℝ) * RCLike.re
            (∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)) := by
      rw [hdiag]

/-- Cauchy--Schwarz on the exact convolution support bounds the squared
convolution mass by support cardinality times convolution energy. -/
theorem int_intervalConvolution_mass_sq_le_card_energy
    {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0) (H : ℕ) (hH : 1 ≤ H) :
    ‖(H : ℂ) * ∑ n ∈ Finset.Ico l r, u n‖ ^ 2 ≤
      (Finset.Ico l (r + (H - 1 : ℕ))).card *
        (∑ n ∈ Finset.Ico l (r + H),
          ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2) := by
  let T := Finset.Ico l (r + (H - 1 : ℕ))
  let v : ℤ → ℂ := fun n => ∑ a ∈ Finset.range H, u (n - (a : ℤ))
  have hmass := int_intervalConvolution_sum_eq_tight hsupp H hH
  have henergy := int_intervalConvolution_energy_eq_tight hsupp H hH
  have hcs := complex_norm_sum_sq_le_card_mul_sum_norm_sq T v
  calc
    ‖(H : ℂ) * ∑ n ∈ Finset.Ico l r, u n‖ ^ 2 =
        ‖∑ n ∈ T, v n‖ ^ 2 := by rw [← hmass]
    _ ≤ (T.card : ℝ) * ∑ n ∈ T, ‖v n‖ ^ 2 := hcs
    _ = (Finset.Ico l (r + (H - 1 : ℕ))).card *
        (∑ n ∈ Finset.Ico l (r + H),
          ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2) := by
          rw [← henergy]

/-- The cardinality of a half-open integer interval, viewed in the reals, is
its endpoint difference. -/
theorem int_Ico_card_real {l r : ℤ} (hlr : l ≤ r) :
    ((Finset.Ico l r).card : ℝ) = (r : ℝ) - (l : ℝ) := by
  have h := Int.card_Ico_of_le l r hlr
  exact_mod_cast h

/-- The exact cardinality of the finite convolution support interval. -/
theorem int_intervalConvolution_support_card_real {l r : ℤ} (hlr : l ≤ r)
    (H : ℕ) :
    ((Finset.Ico l (r + (H - 1 : ℕ))).card : ℝ) =
      ((Finset.Ico l r).card : ℝ) + ((H - 1 : ℕ) : ℝ) := by
  have hupper : l ≤ r + (H - 1 : ℕ) := by omega
  rw [int_Ico_card_real hupper, int_Ico_card_real hlr]
  push_cast
  ring

/-- The support of the convolution has at most `2Y` points under the exact
interval-length and shift-range hypotheses used in `ld:weyl-positive`. -/
theorem int_intervalConvolution_support_card_le_two_mul
    {l r : ℤ} {H : ℕ} {Y : ℝ}
    (hlr : l ≤ r) (hH : 1 ≤ H)
    (hHY : (H : ℝ) ≤ Y)
    (hN : ((Finset.Ico l r).card : ℝ) ≤ Y + 1) :
    ((Finset.Ico l (r + (H - 1 : ℕ))).card : ℝ) ≤ 2 * Y := by
  rw [int_intervalConvolution_support_card_real hlr H]
  have hpred : ((H - 1 : ℕ) : ℝ) ≤ Y - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ H)]
    norm_num at *
    linarith
  linarith

/-- The exact weighted correlation identity is bounded above by its diagonal
mass and the absolute values of its positive-shift correlations. -/
theorem int_intervalConvolution_energy_le_absCorrelations
    {u : ℤ → ℂ} {l r : ℤ}
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0)
    (hunit : ∀ n ∈ Finset.Ico l r, ‖u n‖ ≤ 1)
    (H : ℕ) (hH : 1 ≤ H) :
    (∑ n ∈ Finset.Ico l (r + H),
      ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2) ≤
      (H : ℝ) * (Finset.Ico l r).card +
        2 * ∑ d ∈ Finset.Ico 1 H,
          ((H - d : ℕ) : ℝ) *
            ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖ := by
  rw [int_intervalConvolution_energy_eq_weightedCorrelation hsupp H hH]
  have hdiag : ∑ m ∈ Finset.Ico l r, ‖u m‖ ^ 2 ≤
      (Finset.Ico l r).card := by
    calc
      ∑ m ∈ Finset.Ico l r, ‖u m‖ ^ 2 ≤
          ∑ _m ∈ Finset.Ico l r, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro m hm
            have hn := hunit m hm
            have hnonneg : 0 ≤ ‖u m‖ := norm_nonneg _
            nlinarith
      _ = (Finset.Ico l r).card := by simp
  have hcorr : ∑ d ∈ Finset.Ico 1 H,
      ((H - d : ℕ) : ℝ) * RCLike.re
        (∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)) ≤
      ∑ d ∈ Finset.Ico 1 H,
        ((H - d : ℕ) : ℝ) *
          ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖ := by
    apply Finset.sum_le_sum
    intro d hd
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (le_abs_self _).trans (RCLike.norm_re_le_norm _)
  have hHnonneg : 0 ≤ (H : ℝ) := by positivity
  calc
    (H : ℝ) * ∑ m ∈ Finset.Ico l r, ‖u m‖ ^ 2 +
        2 * ∑ d ∈ Finset.Ico 1 H,
          ((H - d : ℕ) : ℝ) * RCLike.re
            (∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m))
      ≤ (H : ℝ) * (Finset.Ico l r).card +
        2 * ∑ d ∈ Finset.Ico 1 H,
          ((H - d : ℕ) : ℝ) *
            ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hdiag hHnonneg)
            (mul_le_mul_of_nonneg_left hcorr (by norm_num))

/-- Each weighted absolute correlation is bounded by `H` times the same
unweighted correlation. -/
theorem int_triangle_weighted_norm_sum_le
    {u : ℤ → ℂ} {l r : ℤ} (H : ℕ) :
    (∑ d ∈ Finset.Ico 1 H,
      ((H - d : ℕ) : ℝ) *
        ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖) ≤
      (H : ℝ) * ∑ d ∈ Finset.Ico 1 H,
        ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖ := by
  calc
    _ ≤ ∑ d ∈ Finset.Ico 1 H,
        (H : ℝ) *
          ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖ := by
          apply Finset.sum_le_sum
          intro d hd
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact_mod_cast Nat.sub_le H d
    _ = (H : ℝ) * ∑ d ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖ := by
          rw [Finset.mul_sum]

/-- The finite-support form of the blueprint's safe Weyl correlation
inequality, with the interval cardinality kept as an explicit hypothesis. -/
theorem int_intervalConvolution_weyl_bound
    {u : ℤ → ℂ} {l r : ℤ} {H : ℕ} {Y : ℝ}
    (hlr : l ≤ r)
    (hsupp : ∀ n, n ∉ Finset.Ico l r → u n = 0)
    (hunit : ∀ n ∈ Finset.Ico l r, ‖u n‖ ≤ 1)
    (hN : ((Finset.Ico l r).card : ℝ) ≤ Y + 1)
    (hH : 1 ≤ H) (hHY : (H : ℝ) ≤ Y) :
    ‖(∑ n ∈ Finset.Ico l r, u n) / (Y : ℂ)‖ ^ 2 ≤
      4 / (H : ℝ) + 4 / ((H : ℝ) * Y) *
        ∑ d ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖ := by
  have hHreal1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hY : 1 ≤ Y := hHreal1.trans hHY
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hHreal : 0 < (H : ℝ) := lt_of_lt_of_le zero_lt_one hHreal1
  have hTcard := int_intervalConvolution_support_card_le_two_mul
    hlr hH hHY hN
  have hNtwo : ((Finset.Ico l r).card : ℝ) ≤ 2 * Y := by linarith
  have hmass := int_intervalConvolution_mass_sq_le_card_energy hsupp H hH
  have henergy := int_intervalConvolution_energy_le_absCorrelations hsupp hunit H hH
  have hweighted := int_triangle_weighted_norm_sum_le (u := u) (l := l) (r := r) H
  let C : ℝ := ∑ d ∈ Finset.Ico 1 H,
    ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖
  have henergy' :
      (∑ n ∈ Finset.Ico l (r + H),
        ‖∑ a ∈ Finset.range H, u (n - (a : ℤ))‖ ^ 2) ≤
      2 * (H : ℝ) * Y + 2 * (H : ℝ) * C := by
    dsimp [C]
    calc
      _ ≤ (H : ℝ) * (Finset.Ico l r).card +
          2 * ((H : ℝ) * ∑ d ∈ Finset.Ico 1 H,
            ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖) := by
            exact le_trans henergy (add_le_add (le_refl _)
              (mul_le_mul_of_nonneg_left hweighted (by norm_num : (0 : ℝ) ≤ 2)))
      _ ≤ 2 * (H : ℝ) * Y + 2 * (H : ℝ) *
          ∑ d ∈ Finset.Ico 1 H,
            ‖∑ m ∈ Finset.Ico l r, u (m + (d : ℤ)) * star (u m)‖ := by
            have hHnonneg : 0 ≤ (H : ℝ) := le_of_lt hHreal
            nlinarith [mul_le_mul_of_nonneg_left hNtwo hHnonneg]
  have hBnonneg : 0 ≤ 2 * (H : ℝ) * Y + 2 * (H : ℝ) * C := by positivity
  have hmain :
      (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico l r, u n‖ ^ 2 ≤
        4 * (H : ℝ) * Y ^ 2 +
          4 * (H : ℝ) * Y * C := by
    have hmul := le_trans hmass (mul_le_mul_of_nonneg_left henergy' (by positivity))
    have hprod := mul_le_mul_of_nonneg_right hTcard hBnonneg
    have hnorm : ‖(H : ℂ) * ∑ n ∈ Finset.Ico l r, u n‖ ^ 2 =
        (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico l r, u n‖ ^ 2 := by
      rw [norm_mul]
      simp only [Complex.norm_natCast]
      ring
    rw [hnorm] at hmul
    calc
      (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico l r, u n‖ ^ 2 ≤
          (Finset.Ico l (r + (H - 1 : ℕ))).card *
            (2 * (H : ℝ) * Y + 2 * (H : ℝ) * C) := hmul
      _ ≤ 2 * Y * (2 * (H : ℝ) * Y + 2 * (H : ℝ) * C) := hprod
      _ = 4 * (H : ℝ) * Y ^ 2 + 4 * (H : ℝ) * Y * C := by ring
  have hnorm_div :
      ‖(∑ n ∈ Finset.Ico l r, u n) / (Y : ℂ)‖ ^ 2 =
        ‖∑ n ∈ Finset.Ico l r, u n‖ ^ 2 / Y ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hYpos]
    ring
  have hscaled :
      ‖∑ n ∈ Finset.Ico l r, u n‖ ^ 2 / Y ^ 2 ≤
        4 / (H : ℝ) + 4 / ((H : ℝ) * Y) * C := by
    have hden : 0 < (H : ℝ) ^ 2 * Y ^ 2 := by positivity
    field_simp [ne_of_gt hHreal, ne_of_gt hYpos]
    nlinarith [hmain]
  rw [hnorm_div]
  simpa [C, div_eq_mul_inv] using hscaled

/-- The safe Weyl inequality on the paper's exact real-endpoint interval
`I(x,Y) = {n : ℤ | x < n ≤ x+Y}`. -/
theorem realIntegerInterval_weyl_bound
    {u : ℤ → ℂ} {x Y : ℝ} {H : ℕ}
    (hY : 1 ≤ Y)
    (hsupp : ∀ n : ℤ, ¬ (x < (n : ℝ) ∧ (n : ℝ) ≤ x + Y) → u n = 0)
    (hunit : ∀ n : ℤ, x < (n : ℝ) ∧ (n : ℝ) ≤ x + Y → ‖u n‖ ≤ 1)
    (hH : 1 ≤ H) (hHY : (H : ℝ) ≤ Y) :
    ‖(∑ n ∈ realIntegerInterval x Y, u n) / (Y : ℂ)‖ ^ 2 ≤
      4 / (H : ℝ) + 4 / ((H : ℝ) * Y) *
        ∑ d ∈ Finset.Ico 1 H,
          ‖∑ m ∈ realIntegerInterval x Y,
            u (m + (d : ℤ)) * star (u m)‖ := by
  let l : ℤ := ⌊x⌋ + 1
  let r : ℤ := ⌊x + Y⌋ + 1
  have hlr : l ≤ r := by
    dsimp [l, r]
    exact Int.add_le_add_right (Int.floor_mono (by linarith)) 1
  have hmem (n : ℤ) : n ∈ realIntegerInterval x Y ↔ n ∈ Finset.Ico l r := by
    rw [mem_realIntegerInterval_iff]
    simp only [l, r, Finset.mem_Ico]
    constructor
    · rintro ⟨hlo, hhi⟩
      have hfloorLo : ⌊x⌋ < n := (Int.floor_lt).mpr hlo
      have hfloorHi : n ≤ ⌊x + Y⌋ := (Int.le_floor).mpr hhi
      omega
    · intro hn
      constructor
      · have hfloor : ⌊x⌋ < n := by omega
        exact (Int.floor_lt).mp hfloor
      · have hfloor : n ≤ ⌊x + Y⌋ := by omega
        exact (Int.le_floor).mp hfloor
  have hsupp' : ∀ n, n ∉ Finset.Ico l r → u n = 0 := by
    intro n hn
    apply hsupp n
    intro hmem'
    exact hn ((hmem n).mpr ((mem_realIntegerInterval_iff x Y n).mpr hmem'))
  have hunit' : ∀ n ∈ Finset.Ico l r, ‖u n‖ ≤ 1 := by
    intro n hn
    apply hunit n
    exact (mem_realIntegerInterval_iff x Y n).mp ((hmem n).mp hn)
  have hN : ((Finset.Ico l r).card : ℝ) ≤ Y + 1 := by
    have hc := realIntegerInterval_card_le x Y hY
    simpa [l, r, realIntegerInterval] using hc
  have hfinite := int_intervalConvolution_weyl_bound hlr hsupp' hunit' hN hH hHY
  simpa [l, r, realIntegerInterval] using hfinite

theorem averagedCorrelation_prefix_local_bound
    (f : ℝ → ℝ) (x Y : ℝ) (H : ℕ) (bounds shifts : List ℕ)
    (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hTotal : realShiftTotal (H :: bounds) ≤ Y)
    (hshifts : shifts ∈ positiveShiftBox bounds) :
    let L := Y - realShiftTotal shifts
    let g := iteratedRealForwardDifference f shifts
    ‖(∑ n ∈ realIntegerInterval x L, realExponentialPhase g n) / (Y : ℂ)‖ ^ 2 ≤
      4 / (H : ℝ) + 4 / ((H : ℝ) * Y) *
        ∑ d ∈ Finset.Ico 1 H,
          ‖∑ n ∈ realIntegerInterval x (L - d),
            realExponentialPhase (realForwardDifference d g) n‖ := by
  dsimp
  let L := Y - realShiftTotal shifts
  let g := iteratedRealForwardDifference f shifts
  let u : ℤ → ℂ := realIntervalPhase g x L
  let S : ℂ := ∑ n ∈ realIntegerInterval x L, realExponentialPhase g n
  let C : ℝ := ∑ d ∈ Finset.Ico 1 H,
    ‖∑ n ∈ realIntegerInterval x (L - d),
      realExponentialPhase (realForwardDifference d g) n‖
  have hboundsTotal : (H : ℝ) + realShiftTotal bounds ≤ Y := by
    simpa [realShiftTotal] using hTotal
  have hshiftTotal := realShiftTotal_le_bounds bounds shifts hshifts
  have hHL : (H : ℝ) ≤ L := by
    dsimp [L]
    linarith
  have hLpos : 0 < L := by
    have hHreal : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    dsimp [L]
    linarith
  have hLY : L ≤ Y := by
    dsimp [L]
    linarith [realShiftTotal_nonneg shifts]
  have hHreal1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hLone : 1 ≤ L := hHreal1.trans hHL
  have hlocal := realIntegerInterval_weyl_bound hLone
      (fun n hn => realIntervalPhase_zero_of_not_mem g x L n (by
        intro hmem
        exact hn ((mem_realIntegerInterval_iff x L n).mp hmem)))
      (fun n hn => norm_realIntervalPhase_le_one g x L n) hH hHL
  have hcor (d : ℕ) :
      ‖∑ n ∈ realIntegerInterval x L,
          u (n + (d : ℤ)) * star (u n)‖ =
        ‖∑ n ∈ realIntegerInterval x (L - d),
          realExponentialPhase (realForwardDifference d g) n‖ := by
    have h := realIntervalPhase_correlation_eq_difference_sum g x L d
    exact congrArg norm (by simpa [u] using h)
  have hcorr :
      (∑ d ∈ Finset.Ico 1 H,
        ‖∑ n ∈ realIntegerInterval x L,
          u (n + (d : ℤ)) * star (u n)‖) = C := by
    dsimp [C]
    apply Finset.sum_congr rfl
    intro d hd
    exact hcor d
  have hlocal' : ‖S‖ ^ 2 / L ^ 2 ≤ 4 / (H : ℝ) +
      4 / ((H : ℝ) * L) * C := by
    have hnorm := complex_norm_div_real_sq
      (∑ n ∈ realIntegerInterval x L, realExponentialPhase g n) L hLpos
    calc
      ‖S‖ ^ 2 / L ^ 2 =
          ‖(∑ n ∈ realIntegerInterval x L, realExponentialPhase g n) /
            (L : ℂ)‖ ^ 2 := by simpa [S] using hnorm.symm
      _ ≤ 4 / (H : ℝ) + 4 / ((H : ℝ) * L) *
          ∑ d ∈ Finset.Ico 1 H,
            ‖∑ n ∈ realIntegerInterval x L,
              u (n + (d : ℤ)) * star (u n)‖ := by
            have hsum := realIntervalPhase_sum g x L
            rw [← hsum]
            have habs : |L| = L := abs_of_pos hLpos
            simpa [u, habs] using hlocal
      _ = 4 / (H : ℝ) + 4 / ((H : ℝ) * L) * C := by rw [hcorr]
  have hC : 0 ≤ C := by positivity
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  have hrescaled := real_weyl_rescale_normalization hlocal' hC hHpos hLpos hLY
  have hnormY := complex_norm_div_real_sq S Y (lt_of_lt_of_le zero_lt_one hY)
  calc
    ‖(∑ n ∈ realIntegerInterval x L, realExponentialPhase g n) / (Y : ℂ)‖ ^ 2 =
        ‖S / (Y : ℂ)‖ ^ 2 := by simp [S]
    _ = ‖S‖ ^ 2 / Y ^ 2 := hnormY
    _ ≤ 4 / (H : ℝ) + 4 / ((H : ℝ) * Y) * C := hrescaled


theorem averagedIteratedCorrelation_recurrence
    (f : ℝ → ℝ) (x Y : ℝ) (H : ℕ) (bounds : List ℕ)
    (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hpos : ∀ K ∈ bounds, 0 < K)
    (hTotal : realShiftTotal (H :: bounds) ≤ Y) :
    (averagedIteratedCorrelation f x Y bounds) ^ 2 ≤
      4 / (H : ℝ) + 4 * averagedIteratedCorrelation f x Y (H :: bounds) := by
  let P := realShiftNormalizer bounds
  let B := positiveShiftBox bounds
  let b : List ℕ → ℝ := fun shifts =>
    ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
      realExponentialPhase (iteratedRealForwardDifference f shifts) n‖ / Y
  let c : List ℕ → ℝ := fun shifts =>
    ∑ d ∈ Finset.Ico 1 H,
      ‖∑ n ∈ iteratedDifferenceInterval x Y (d :: shifts),
        realExponentialPhase (iteratedRealForwardDifference f (d :: shifts)) n‖
  let a : List ℕ → ℝ := fun shifts =>
    ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
      realExponentialPhase (iteratedRealForwardDifference f shifts) n‖
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hPpos : 0 < P := by
    dsimp [P]
    exact realShiftNormalizer_pos bounds hpos
  have hcard : (B.card : ℝ) ≤ P := by
    dsimp [B, P]
    rw [realShiftNormalizer_eq_natCast_prod]
    exact_mod_cast positiveShiftBox_card_le_bound_product bounds
  have hTform : averagedIteratedCorrelation f x Y bounds =
      ∑ shifts ∈ B, b shifts / P := by
    rw [averagedIteratedCorrelation_eq_normalized_sum f x Y bounds hYpos hPpos]
    change P⁻¹ * (∑ shifts ∈ B, b shifts) = ∑ shifts ∈ B, b shifts / P
    calc
      P⁻¹ * (∑ shifts ∈ B, b shifts) =
          (∑ shifts ∈ B, b shifts) / P := by rw [div_eq_mul_inv]; ring
      _ = ∑ shifts ∈ B, b shifts / P := Finset.sum_div B b P
  have hcs := real_sum_sq_div_le_sum_sq_div B b P hcard hPpos
  have hTcs : (averagedIteratedCorrelation f x Y bounds) ^ 2 ≤
      (∑ shifts ∈ B, b shifts ^ 2) / P := by
    rw [hTform]
    exact hcs
  have hlocal : ∀ shifts ∈ B,
      b shifts ^ 2 ≤ 4 / (H : ℝ) + 4 / ((H : ℝ) * Y) * c shifts := by
    intro shifts hshifts
    have h := averagedCorrelation_prefix_local_bound f x Y H bounds shifts
      hY hH hTotal hshifts
    dsimp at h
    have hinterval (d : ℕ) :
        iteratedDifferenceInterval x Y (d :: shifts) =
          realIntegerInterval x
            ((Y - realShiftTotal shifts) - d) :=
      iteratedDifferenceInterval_head x Y d shifts
    have hphase (d : ℕ) :
        iteratedRealForwardDifference f (d :: shifts) =
          realForwardDifference d (iteratedRealForwardDifference f shifts) :=
      iteratedRealForwardDifference_head f d shifts
    have hright : c shifts =
        ∑ d ∈ Finset.Ico 1 H,
          ‖∑ n ∈ realIntegerInterval x
              ((Y - realShiftTotal shifts) - d),
            realExponentialPhase
              (realForwardDifference d (iteratedRealForwardDifference f shifts)) n‖ := by
      dsimp [c]
      apply Finset.sum_congr rfl
      intro d hd
      rw [hinterval, hphase]
    rw [← hright] at h
    have hleft := complex_norm_div_real_sq
      (∑ n ∈ realIntegerInterval x (Y - realShiftTotal shifts),
        realExponentialPhase (iteratedRealForwardDifference f shifts) n) Y hYpos
    rw [hleft] at h
    have hb : b shifts ^ 2 =
        ‖∑ n ∈ realIntegerInterval x (Y - realShiftTotal shifts),
          realExponentialPhase (iteratedRealForwardDifference f shifts) n‖ ^ 2 / Y ^ 2 := by
      dsimp [b, iteratedDifferenceInterval]
      ring
    rw [hb]
    exact h
  have hsumLocal : (∑ shifts ∈ B, b shifts ^ 2) ≤
      ∑ shifts ∈ B,
        (4 / (H : ℝ) + 4 / ((H : ℝ) * Y) * c shifts) := by
    apply Finset.sum_le_sum
    intro shifts hshifts
    exact hlocal shifts hshifts
  have hsumDiv := div_le_div_of_nonneg_right hsumLocal (le_of_lt hPpos)
  have hdouble : (∑ shifts ∈ B, c shifts) =
      ∑ shifts ∈ positiveShiftBox (H :: bounds), a shifts := by
    dsimp [c, a, B]
    rw [Finset.sum_comm]
    rw [← sum_positiveShiftBox_cons H bounds a]
  have hsumSplit :
      (∑ shifts ∈ B,
        (4 / (H : ℝ) + 4 / ((H : ℝ) * Y) * c shifts)) =
        (B.card : ℝ) * (4 / (H : ℝ)) +
          (4 / ((H : ℝ) * Y)) * (∑ shifts ∈ B, c shifts) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hsplit :
      (∑ shifts ∈ B,
        (4 / (H : ℝ) + 4 / ((H : ℝ) * Y) * c shifts)) / P =
      ((B.card : ℝ) / P) * (4 / (H : ℝ)) +
        (4 / ((H : ℝ) * Y)) *
          ((∑ shifts ∈ positiveShiftBox (H :: bounds), a shifts) / P) := by
    rw [hsumSplit, hdouble]
    field_simp [ne_of_gt hPpos]
  have hratio : (B.card : ℝ) / P ≤ 1 := (div_le_one₀ hPpos).2 hcard
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  have hconstant : ((B.card : ℝ) / P) * (4 / (H : ℝ)) ≤
      4 / (H : ℝ) := by
    calc
      ((B.card : ℝ) / P) * (4 / (H : ℝ)) ≤ 1 * (4 / (H : ℝ)) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = 4 / (H : ℝ) := by ring
  have hnew : averagedIteratedCorrelation f x Y (H :: bounds) =
      (Y * ((H : ℝ) * P))⁻¹ *
        ∑ shifts ∈ positiveShiftBox (H :: bounds), a shifts := by
    rfl
  have hcorrelation :
      (4 / ((H : ℝ) * Y)) *
          ((∑ shifts ∈ positiveShiftBox (H :: bounds), a shifts) / P) =
        4 * averagedIteratedCorrelation f x Y (H :: bounds) := by
    rw [hnew]
    field_simp [ne_of_gt hHpos, ne_of_gt hYpos, ne_of_gt hPpos]
  calc
    (averagedIteratedCorrelation f x Y bounds) ^ 2 ≤
        (∑ shifts ∈ B, b shifts ^ 2) / P := hTcs
    _ ≤ ((B.card : ℝ) / P) * (4 / (H : ℝ)) +
        (4 / ((H : ℝ) * Y)) *
          ((∑ shifts ∈ positiveShiftBox (H :: bounds), a shifts) / P) :=
      hsumDiv.trans_eq hsplit
    _ ≤ 4 / (H : ℝ) + 4 * averagedIteratedCorrelation f x Y (H :: bounds) := by
      rw [hcorrelation]
      exact add_le_add hconstant (le_refl _)

/-- Recursive form of the repeated-Weyl maximum from `ld:iterated-weyl`.
The list is the order in which bounds are prepended to the shift tuple. -/
noncomputable def derivativeWeylEnvelope : List ℕ → ℝ → ℝ
  | [], T => T
  | H :: rest, T => Real.sqrt (max
      (derivativeWeylConstant ^ 2 / (H : ℝ))
      (derivativeWeylConstant * derivativeWeylEnvelope rest T))

/-- The same recursive maximum after factoring out the blueprint constant.
Each prepended bound contributes one additional square root. -/
noncomputable def normalizedDerivativeWeylEnvelope : List ℕ → ℝ → ℝ
  | [], T => T / derivativeWeylConstant
  | H :: rest, T => Real.sqrt (max (1 / (H : ℝ))
      (normalizedDerivativeWeylEnvelope rest T))

/-- Maximum form of the normalized envelope. Its successive square roots
produce the powers `1/2`, `1/4`, and so on in `ld:iterated-weyl`. -/
noncomputable def derivativeWeylFiniteMaximum : List ℕ → ℝ → ℝ
  | [], T => T / derivativeWeylConstant
  | H :: rest, T => max (Real.sqrt (1 / (H : ℝ)))
      (Real.sqrt (derivativeWeylFiniteMaximum rest T))

/-- The actual finite list of candidates whose maximum is the normalized
repeated-Weyl envelope. The terminal candidate is carried through every
successive square root. -/
noncomputable def derivativeWeylCandidates : List ℕ → ℝ → List ℝ
  | [], T => [T / derivativeWeylConstant]
  | H :: rest, T => Real.sqrt (1 / (H : ℝ)) ::
      (derivativeWeylCandidates rest T).map Real.sqrt

/-- Maximum of a finite real list, with zero as the empty-list convention. -/
def realListMaximum : List ℝ → ℝ
  | [] => 0
  | a :: rest => max a (realListMaximum rest)

theorem realListMaximum_le_of_forall_le (values : List ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hvalues : ∀ a ∈ values, a ≤ R) :
    realListMaximum values ≤ R := by
  induction values with
  | nil => simpa [realListMaximum] using hR
  | cons a rest ih =>
    apply max_le
    · exact hvalues a (by simp)
    · apply ih
      intro b hb
      exact hvalues b (by simp [hb])

/-- Apply the real square root `n` times. -/
noncomputable def iteratedRealSqrt : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => Real.sqrt (iteratedRealSqrt n x)

/-- Candidate list with an explicit root count, so that coordinate `i` is
obtained after `i+1` roots and the terminal term after one root per bound. -/
noncomputable def indexedDerivativeWeylCandidates : ℕ → List ℕ → ℝ → List ℝ
  | depth, [], T => [iteratedRealSqrt depth (T / derivativeWeylConstant)]
  | depth, H :: rest, T =>
      iteratedRealSqrt (depth + 1) (1 / (H : ℝ)) ::
        indexedDerivativeWeylCandidates (depth + 1) rest T

/-- The same candidates written with the fractional powers appearing in
`ld:iterated-weyl`. The terminal entry is the exact `B^(-1/2^r) T_r^(1/2^r)`.
-/
noncomputable def derivativeWeylPowerCandidates : ℕ → List ℕ → ℝ → List ℝ
  | depth, [], T =>
      [T ^ (((2 : ℝ) ^ depth)⁻¹) *
        derivativeWeylConstant ^ (-((2 : ℝ) ^ depth)⁻¹)]
  | depth, H :: rest, T =>
      (H : ℝ) ^ (-((2 : ℝ) ^ (depth + 1))⁻¹) ::
        derivativeWeylPowerCandidates (depth + 1) rest T

def derivativeWeylCoordinateBounds (depth : ℕ) : List ℕ → ℝ → Prop
  | [] => fun _ => True
  | H :: rest => fun R =>
      (H : ℝ) ^ (-((2 : ℝ) ^ (depth + 1))⁻¹) ≤ R ∧
        derivativeWeylCoordinateBounds (depth + 1) rest R

theorem derivativeWeyl_allocated_coordinate_bound
    (h : ℕ) (i : Fin h) {V ξ x : ℝ}
    (hV : 1 ≤ V) (hξ : 1 ≤ ξ) (hx : 1 ≤ x)
    (halloc : min
      (ξ ^ ((2 : ℝ) ^ (i.val + 1) / ((2 : ℝ) ^ (h + 1) - 2)))
      (V ^ ((2 : ℝ) ^ (i.val + 1) / (2 : ℝ) ^ h)) ≤ x) :
    (⌊x⌋₊ : ℝ) ^ (-((2 : ℝ) ^ (i.val + 1))⁻¹) ≤
      Real.sqrt 2 * max
        (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
        (V ^ (-4 / (2 : ℝ) ^ (h + 2))) := by
  let a : ℝ := ((2 : ℝ) ^ (i.val + 1))⁻¹
  let eξ : ℝ := (2 : ℝ) ^ (i.val + 1) / ((2 : ℝ) ^ (h + 1) - 2)
  let eV : ℝ := (2 : ℝ) ^ (i.val + 1) / (2 : ℝ) ^ h
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hξpos : 0 < ξ := lt_of_lt_of_le zero_lt_one hξ
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (i.val + 1) := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ (i.val + 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have ha : 0 ≤ a := by positivity
  have haHalf : a ≤ 1 / 2 := by
    dsimp [a]
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow)
  have hh : 1 ≤ h := Nat.succ_le_of_lt
    (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hpowD : (2 : ℝ) ^ (h + 2) = 4 * (2 : ℝ) ^ h := by
    calc
      (2 : ℝ) ^ (h + 2) = (2 : ℝ) ^ (h + 1 + 1) := by congr 1 <;> omega
      _ = (2 : ℝ) ^ (h + 1) * 2 := by rw [pow_succ]
      _ = ((2 : ℝ) ^ h * 2) * 2 := by rw [pow_succ]
      _ = 4 * (2 : ℝ) ^ h := by ring
  have hξbase : 0 < ξ ^ eξ := Real.rpow_pos_of_pos hξpos _
  have hVbase : 0 < V ^ eV := Real.rpow_pos_of_pos hVpos _
  have hnegative := rpow_neg_le_max_of_min_le hξbase hVbase hxpos ha halloc
  have hξpower : (ξ ^ eξ) ^ (-a) = ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)) := by
    rw [← Real.rpow_mul (le_of_lt hξpos)]
    congr 1
    dsimp [a, eξ]
    have hge : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (h + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hdenPos : 0 < (2 : ℝ) ^ (h + 1) - 2 := by nlinarith
    have hden : (2 : ℝ) ^ (h + 1) - 2 ≠ 0 := ne_of_gt hdenPos
    rw [hpowD]
    rw [show (2 : ℝ) ^ (h + 1) = 2 * (2 : ℝ) ^ h by rw [pow_succ]; ring]
    field_simp [hden]
    ring
  have hVpower : (V ^ eV) ^ (-a) = V ^ (-4 / (2 : ℝ) ^ (h + 2)) := by
    rw [← Real.rpow_mul (le_of_lt hVpos)]
    congr 1
    dsimp [a, eV]
    have hden : (2 : ℝ) ^ h ≠ 0 := (pow_ne_zero _ (by norm_num))
    rw [hpowD]
    field_simp [hden]
  have hfloor := natFloor_rpow_neg_le_sqrt_two_of_one_le hx ha haHalf
  calc
    (⌊x⌋₊ : ℝ) ^ (-((2 : ℝ) ^ (i.val + 1))⁻¹) ≤ Real.sqrt 2 * x ^ (-a) := by
      simpa [a] using hfloor
    _ ≤ Real.sqrt 2 * max
          ((ξ ^ eξ) ^ (-a)) ((V ^ eV) ^ (-a)) :=
      mul_le_mul_of_nonneg_left hnegative (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))) := by rw [hξpower, hVpower]

theorem derivativeWeylPowerCandidates_max_le
    (depth : ℕ) (bounds : List ℕ) (T R : ℝ) (hR : 0 ≤ R)
    (hcoords : derivativeWeylCoordinateBounds depth bounds R)
    (hterminal : T ^ (((2 : ℝ) ^ (depth + bounds.length))⁻¹) *
        derivativeWeylConstant ^ (-((2 : ℝ) ^ (depth + bounds.length))⁻¹) ≤ R) :
    realListMaximum (derivativeWeylPowerCandidates depth bounds T) ≤ R := by
  induction bounds generalizing depth with
  | nil =>
      simpa [derivativeWeylPowerCandidates, realListMaximum] using
        (show T ^ (((2 : ℝ) ^ depth)⁻¹) *
          derivativeWeylConstant ^ (-((2 : ℝ) ^ depth)⁻¹) ≤ R ∧ 0 ≤ R from
            ⟨hterminal, hR⟩)
  | cons H rest ih =>
      rcases hcoords with ⟨hhead, htail⟩
      have hterminal' :
          T ^ (((2 : ℝ) ^ (depth + 1 + rest.length))⁻¹) *
            derivativeWeylConstant ^ (-((2 : ℝ) ^ (depth + 1 + rest.length))⁻¹) ≤ R := by
        simpa [List.length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hterminal
      have htailBound := ih (depth + 1) htail hterminal'
      simpa [derivativeWeylPowerCandidates, realListMaximum] using
        (max_le hhead htailBound)

theorem derivativeWeylCoordinateBounds_ofFn_floor
    (depth h : ℕ) (scales : Fin h → ℝ) (R : ℝ)
    (hcoord : ∀ i : Fin h,
      (⌊scales i⌋₊ : ℝ) ^ (-((2 : ℝ) ^ (depth + i.val + 1))⁻¹) ≤ R) :
    derivativeWeylCoordinateBounds depth
      (List.ofFn fun i : Fin h => ⌊scales i⌋₊) R := by
  induction h generalizing depth with
  | zero => simp [derivativeWeylCoordinateBounds]
  | succ h ih =>
      rw [List.ofFn_succ]
      simp only [derivativeWeylCoordinateBounds]
      constructor
      · simpa using hcoord 0
      · apply ih (depth + 1) (fun i => scales i.succ)
        intro i
        have hi := hcoord i.succ
        simpa [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

theorem derivativeWeylCoordinateBounds_from_allocation
    (h : ℕ) (hh : 1 ≤ h) {V ξ : ℝ}
    (hV : 1 ≤ V) (hξ : 1 ≤ ξ) (hξV : ξ ≤ V ^ h) :
    ∃ allocation : ℕ → ℝ,
      (∀ i ∈ Finset.range h, allocation i ∈ Set.Icc 1 V) ∧
      (∏ i ∈ Finset.range h, allocation i) = ξ ∧
      derivativeWeylCoordinateBounds 0
        (List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊)
        (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2)))) := by
  obtain ⟨allocation, hallocationRange, hallocationProd, hallocationLower⟩ :=
    derivativeShiftAllocation h hh hV hξ hξV
  let scales : Fin h → ℝ := fun i => allocation i.val
  let R : ℝ := Real.sqrt 2 * max
    (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
    (V ^ (-4 / (2 : ℝ) ^ (h + 2)))
  have hcoord : ∀ i : Fin h,
      (⌊scales i⌋₊ : ℝ) ^ (-((2 : ℝ) ^ (i.val + 1))⁻¹) ≤ R := by
    intro i
    have hi : i.val ∈ Finset.range h := Finset.mem_range.mpr i.isLt
    have hscale := (hallocationRange i.val hi).1
    have hmin := hallocationLower i.val hi
    simpa [scales, R] using
      derivativeWeyl_allocated_coordinate_bound h i hV hξ hscale hmin
  have hcoord0 : ∀ i : Fin h,
      (⌊scales i⌋₊ : ℝ) ^ (-((2 : ℝ) ^ (0 + i.val + 1))⁻¹) ≤ R := by
    intro i
    simpa using hcoord i
  refine ⟨allocation, hallocationRange, hallocationProd, ?_⟩
  simpa [scales, R] using derivativeWeylCoordinateBounds_ofFn_floor 0 h scales R hcoord0

theorem realShiftNormalizer_ofFn_floor_le
    (h : ℕ) (scales : Fin h → ℝ) (hscales : ∀ i, 1 ≤ scales i) :
    realShiftNormalizer (List.ofFn fun i : Fin h => ⌊scales i⌋₊) ≤
      ∏ i : Fin h, scales i := by
  rw [realShiftNormalizer_eq_natCast_prod]
  have hnat : (List.ofFn fun i : Fin h => ⌊scales i⌋₊).prod =
      ∏ i : Fin h, ⌊scales i⌋₊ := Fin.prod_ofFn _
  rw [hnat]
  have hprod : (∏ i : Fin h, (⌊scales i⌋₊ : ℝ)) ≤ ∏ i : Fin h, scales i := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact Nat.cast_nonneg _
    · intro i hi
      exact Nat.floor_le (by linarith [hscales i])
  exact_mod_cast hprod

theorem realShiftPlusNormalizer_ofFn_floor_ge
    (h : ℕ) (scales : Fin h → ℝ) (hscales : ∀ i, 1 ≤ scales i) :
    ∏ i : Fin h, scales i ≤
      realShiftPlusNormalizer (List.ofFn fun i : Fin h => ⌊scales i⌋₊) := by
  rw [realShiftPlusNormalizer_eq_natCast_shiftProduct]
  have hnat :
      ((List.ofFn fun i : Fin h => ⌊scales i⌋₊).map fun H => H + 1).prod =
        ∏ i : Fin h, (⌊scales i⌋₊ + 1) := by
    rw [← List.ofFn_comp' (fun i : Fin h => ⌊scales i⌋₊)
      (fun H : ℕ => H + 1), Fin.prod_ofFn]
  rw [hnat]
  have hprod : (∏ i : Fin h, scales i) ≤
      ∏ i : Fin h, ((⌊scales i⌋₊ + 1 : ℕ) : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (hscales i)
    · intro i hi
      exact_mod_cast (Nat.lt_floor_add_one (scales i)).le
  exact_mod_cast hprod

theorem derivativeWeylNormalizerBounds_from_allocation
    (h : ℕ) (hh : 1 ≤ h) {V ξ : ℝ}
    (hV : 1 ≤ V) (hξ : 1 ≤ ξ) (hξV : ξ ≤ V ^ h) :
    ∃ allocation : ℕ → ℝ,
      (∀ i ∈ Finset.range h, allocation i ∈ Set.Icc 1 V) ∧
      (∏ i ∈ Finset.range h, allocation i) = ξ ∧
      realShiftNormalizer
        (List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊) ≤ ξ ∧
      ξ ≤ realShiftPlusNormalizer
        (List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊) := by
  obtain ⟨allocation, hallocationRange, hallocationProd, _hallocationLower⟩ :=
    derivativeShiftAllocation h hh hV hξ hξV
  let scales : Fin h → ℝ := fun i => allocation i.val
  have hscalePos : ∀ i : Fin h, 1 ≤ scales i := by
    intro i
    have hi : i.val ∈ Finset.range h := Finset.mem_range.mpr i.isLt
    exact (hallocationRange i.val hi).1
  have hfiniteProd : (∏ i : Fin h, scales i) = ξ := by
    have hindex : (∏ i : Fin h, scales i) =
        ∏ i ∈ Finset.range h, allocation i := by
      simpa [scales] using (Finset.prod_range (fun i : ℕ => allocation i)).symm
    exact hindex.trans hallocationProd
  refine ⟨allocation, hallocationRange, hallocationProd, ?_, ?_⟩
  · rw [← hfiniteProd]
    exact realShiftNormalizer_ofFn_floor_le h scales hscalePos
  · rw [← hfiniteProd]
    exact realShiftPlusNormalizer_ofFn_floor_ge h scales hscalePos

theorem indexedDerivativeWeylCandidates_succ (depth : ℕ) (bounds : List ℕ)
    (T : ℝ) :
    indexedDerivativeWeylCandidates (depth + 1) bounds T =
      (indexedDerivativeWeylCandidates depth bounds T).map Real.sqrt := by
  induction bounds generalizing depth with
  | nil => simp [indexedDerivativeWeylCandidates, iteratedRealSqrt]
  | cons H rest ih =>
      simp only [indexedDerivativeWeylCandidates, List.map_cons,
        iteratedRealSqrt]
      rw [ih (depth + 1)]

theorem indexedDerivativeWeylCandidates_zero_eq
    (bounds : List ℕ) (T : ℝ) :
    indexedDerivativeWeylCandidates 0 bounds T =
      derivativeWeylCandidates bounds T := by
  induction bounds with
  | nil => simp [indexedDerivativeWeylCandidates, derivativeWeylCandidates,
      iteratedRealSqrt]
  | cons H rest ih =>
      simp only [indexedDerivativeWeylCandidates, derivativeWeylCandidates,
        iteratedRealSqrt]
      rw [indexedDerivativeWeylCandidates_succ 0 rest T, ih]

theorem iteratedRealSqrt_eq_rpow (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    iteratedRealSqrt n x = x ^ (((2 : ℝ) ^ n)⁻¹) := by
  induction n with
  | zero => simp [iteratedRealSqrt]
  | succ n ih =>
      have hpow : ((2 : ℝ) ^ (n + 1))⁻¹ =
          ((2 : ℝ) ^ n)⁻¹ * (1 / 2 : ℝ) := by
        rw [pow_succ]
        field_simp
      calc
        iteratedRealSqrt (n + 1) x =
            Real.sqrt (x ^ ((2 : ℝ) ^ n)⁻¹) := by rw [iteratedRealSqrt, ih]
        _ = (x ^ ((2 : ℝ) ^ n)⁻¹) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        _ = x ^ (((2 : ℝ) ^ n)⁻¹ * (1 / 2 : ℝ)) := by
          rw [← Real.rpow_mul hx]
        _ = x ^ (((2 : ℝ) ^ (n + 1))⁻¹) := by rw [hpow]

theorem indexedDerivativeWeylCandidates_eq_powerCandidates
    (depth : ℕ) (bounds : List ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hpos : ∀ H ∈ bounds, 0 < H) :
    indexedDerivativeWeylCandidates depth bounds T =
      derivativeWeylPowerCandidates depth bounds T := by
  induction bounds generalizing depth with
  | nil =>
      simp only [indexedDerivativeWeylCandidates, derivativeWeylPowerCandidates,
        List.cons.injEq]
      constructor
      ·
        rw [iteratedRealSqrt_eq_rpow depth _
          (div_nonneg hT (le_of_lt derivativeWeylConstant_pos))]
        rw [Real.div_rpow hT (le_of_lt derivativeWeylConstant_pos)]
        rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt derivativeWeylConstant_pos)]
      · trivial
  | cons H rest ih =>
      have hposRest : ∀ K ∈ rest, 0 < K := by
        intro K hK
        exact hpos K (by simp [hK])
      simp only [indexedDerivativeWeylCandidates, derivativeWeylPowerCandidates]
      rw [iteratedRealSqrt_eq_rpow (depth + 1) _ (by positivity)]
      have hhead : (1 / (H : ℝ)) ^ (((2 : ℝ) ^ (depth + 1))⁻¹) =
          (H : ℝ) ^ (-((2 : ℝ) ^ (depth + 1))⁻¹) := by
        rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
      rw [hhead, ih (depth + 1) hposRest]

theorem derivativeWeylCandidates_eq_powerCandidates
    (bounds : List ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hpos : ∀ H ∈ bounds, 0 < H) :
    derivativeWeylCandidates bounds T =
      derivativeWeylPowerCandidates 0 bounds T := by
  rw [← indexedDerivativeWeylCandidates_zero_eq]
  exact indexedDerivativeWeylCandidates_eq_powerCandidates 0 bounds T hT hpos

private theorem real_sqrt_max (a b : ℝ) :
    Real.sqrt (max a b) = max (Real.sqrt a) (Real.sqrt b) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right (Real.sqrt_le_sqrt hab)]
  · rw [max_eq_left hba, max_eq_left (Real.sqrt_le_sqrt hba)]

theorem normalizedDerivativeWeylEnvelope_eq_finiteMaximum
    (bounds : List ℕ) (T : ℝ) :
    normalizedDerivativeWeylEnvelope bounds T =
      derivativeWeylFiniteMaximum bounds T := by
  induction bounds with
  | nil => rfl
  | cons H rest ih =>
      rw [normalizedDerivativeWeylEnvelope, derivativeWeylFiniteMaximum,
        real_sqrt_max, ih]

theorem realListMaximum_map_sqrt (values : List ℝ)
    (hnonneg : ∀ a ∈ values, 0 ≤ a) :
    realListMaximum (values.map Real.sqrt) = Real.sqrt (realListMaximum values) := by
  induction values with
  | nil => simp [realListMaximum]
  | cons a rest ih =>
      have ha := hnonneg a (by simp)
      have hrest : ∀ b ∈ rest, 0 ≤ b := by
        intro b hb
        exact hnonneg b (by simp [hb])
      simp only [List.map_cons, realListMaximum]
      rw [real_sqrt_max, ih hrest]

theorem derivativeWeylCandidates_nonneg (bounds : List ℕ) (T : ℝ)
    (hT : 0 ≤ T) : ∀ a ∈ derivativeWeylCandidates bounds T, 0 ≤ a := by
  induction bounds with
  | nil =>
      intro a ha
      simp only [derivativeWeylCandidates, List.mem_singleton] at ha
      rw [ha]
      exact div_nonneg hT (le_of_lt derivativeWeylConstant_pos)
  | cons H rest ih =>
      intro a ha
      simp only [derivativeWeylCandidates, List.mem_cons, List.mem_map] at ha
      rcases ha with ha | ⟨b, hb, rfl⟩
      · rw [ha]
        exact Real.sqrt_nonneg _
      · exact Real.sqrt_nonneg _

theorem derivativeWeylCandidates_max_eq_finiteMaximum
    (bounds : List ℕ) (T : ℝ) (hT : 0 ≤ T) :
    realListMaximum (derivativeWeylCandidates bounds T) =
      derivativeWeylFiniteMaximum bounds T := by
  induction bounds with
  | nil =>
      simp [realListMaximum, derivativeWeylCandidates,
        derivativeWeylFiniteMaximum,
        div_nonneg hT (le_of_lt derivativeWeylConstant_pos)]
  | cons H rest ih =>
      have hrest := derivativeWeylCandidates_nonneg rest T hT
      simp only [derivativeWeylCandidates, realListMaximum]
      rw [realListMaximum_map_sqrt _ hrest, ih]
      rw [derivativeWeylFiniteMaximum]

private theorem real_sqrt_sq_mul (B z : ℝ) (hB : 0 ≤ B) (hz : 0 ≤ z) :
    Real.sqrt (B ^ 2 * z) = B * Real.sqrt z := by
  have hmul : B ^ 2 * z = (B * Real.sqrt z) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hz]
  rw [hmul, Real.sqrt_sq (mul_nonneg hB (Real.sqrt_nonneg z))]

theorem derivativeWeylEnvelope_eq_constant_mul_normalized
    (bounds : List ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hpos : ∀ H ∈ bounds, 0 < H) :
    derivativeWeylEnvelope bounds T =
      derivativeWeylConstant * normalizedDerivativeWeylEnvelope bounds T := by
  induction bounds with
  | nil =>
      simp only [derivativeWeylEnvelope, normalizedDerivativeWeylEnvelope]
      field_simp [derivativeWeylConstant_pos.ne']
  | cons H rest ih =>
      have hH : 0 < (H : ℝ) := by exact_mod_cast hpos H (by simp)
      have hposRest : ∀ K ∈ rest, 0 < K := by
        intro K hK
        exact hpos K (by simp [hK])
      have hFnonneg : 0 ≤ normalizedDerivativeWeylEnvelope rest T := by
        induction rest with
        | nil => exact div_nonneg hT (le_of_lt derivativeWeylConstant_pos)
        | cons K tail ih' => exact Real.sqrt_nonneg _
      have hmax :
          max (derivativeWeylConstant ^ 2 / (H : ℝ))
              (derivativeWeylConstant ^ 2 *
                normalizedDerivativeWeylEnvelope rest T) =
            derivativeWeylConstant ^ 2 *
              max (1 / (H : ℝ)) (normalizedDerivativeWeylEnvelope rest T) := by
        have hB2 : 0 ≤ derivativeWeylConstant ^ 2 := sq_nonneg _
        have hleft : derivativeWeylConstant ^ 2 / (H : ℝ) =
            derivativeWeylConstant ^ 2 * (1 / (H : ℝ)) := by ring
        rw [hleft]
        rcases le_total (1 / (H : ℝ))
            (normalizedDerivativeWeylEnvelope rest T) with hab | hba
        · rw [max_eq_right (mul_le_mul_of_nonneg_left hab hB2),
            max_eq_right hab]
        · rw [max_eq_left (mul_le_mul_of_nonneg_left hba hB2),
            max_eq_left hba]
      rw [derivativeWeylEnvelope, ih hposRest]
      rw [show derivativeWeylConstant *
          (derivativeWeylConstant * normalizedDerivativeWeylEnvelope rest T) =
            derivativeWeylConstant ^ 2 *
              normalizedDerivativeWeylEnvelope rest T by ring]
      rw [hmax, normalizedDerivativeWeylEnvelope]
      have hBpos := derivativeWeylConstant_pos
      rw [real_sqrt_sq_mul derivativeWeylConstant _ (le_of_lt hBpos)
        (le_of_lt (lt_of_lt_of_le (by positivity) (le_max_left _ _)))]

theorem derivativeWeylEnvelope_eq_constant_mul_candidateMaximum
    (bounds : List ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hpos : ∀ H ∈ bounds, 0 < H) :
    derivativeWeylEnvelope bounds T =
      derivativeWeylConstant *
        realListMaximum (derivativeWeylCandidates bounds T) := by
  rw [derivativeWeylEnvelope_eq_constant_mul_normalized bounds T hT hpos,
    normalizedDerivativeWeylEnvelope_eq_finiteMaximum,
    ← derivativeWeylCandidates_max_eq_finiteMaximum bounds T hT]

theorem derivativeWeylEnvelope_nonneg (bounds : List ℕ) {T : ℝ}
    (hT : 0 ≤ T) : 0 ≤ derivativeWeylEnvelope bounds T := by
  cases bounds with
  | nil => simpa [derivativeWeylEnvelope] using hT
  | cons H rest => exact Real.sqrt_nonneg _

theorem iteratedWeylEnvelope_bound
    (q : List ℕ → ℝ)
    (hq : ∀ bounds, 0 ≤ q bounds)
    (hrec : ∀ (H : ℕ) bounds, 1 ≤ H →
      (q bounds) ^ 2 ≤ 4 / (H : ℝ) + 4 * q (H :: bounds))
    (todo pre : List ℕ) (hpos : ∀ H ∈ todo, 1 ≤ H) :
    q pre ≤ derivativeWeylEnvelope todo (q (todo.reverse ++ pre)) := by
  induction todo generalizing pre with
  | nil => simp [derivativeWeylEnvelope]
  | cons H rest ih =>
      have hHnat : 1 ≤ H := hpos H (by simp)
      have hposRest : ∀ K ∈ rest, 1 ≤ K := by
        intro K hK
        exact hpos K (by simp [hK])
      have hH : 0 < (H : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hHnat)
      have hB := derivativeWeylConstant_pos
      have hid := derivativeWeylConstant_identity
      have hstep := derivativeWeyl_scalar_step hB hH (hq (H :: pre)) hid
      have hrec' := hrec H pre hHnat
      have hsq : (q pre) ^ 2 ≤
          max (derivativeWeylConstant ^ 2 / (H : ℝ))
            (derivativeWeylConstant * q (H :: pre)) := hrec'.trans hstep
      have hroot : q pre ≤ Real.sqrt (max
          (derivativeWeylConstant ^ 2 / (H : ℝ))
          (derivativeWeylConstant * q (H :: pre))) :=
        (Real.le_sqrt (hq pre) (by positivity)).2 hsq
      have hih := ih (H :: pre) hposRest
      have hmax : max (derivativeWeylConstant ^ 2 / (H : ℝ))
          (derivativeWeylConstant * q (H :: pre)) ≤
          max (derivativeWeylConstant ^ 2 / (H : ℝ))
            (derivativeWeylConstant *
              derivativeWeylEnvelope rest (q (rest.reverse ++ (H :: pre)))) := by
        apply max_le_max le_rfl
        exact mul_le_mul_of_nonneg_left hih (le_of_lt hB)
      have hroot' := Real.sqrt_le_sqrt hmax
      simpa [derivativeWeylEnvelope, List.reverse_cons, List.append_assoc] using
        hroot.trans hroot'

theorem averagedIteratedCorrelation_envelope
    (f : ℝ → ℝ) (x Y : ℝ) (todo processed : List ℕ)
    (hY : 1 ≤ Y)
    (hposTodo : ∀ H ∈ todo, 0 < H)
    (hposProcessed : ∀ H ∈ processed, 0 < H)
    (hTotal : realShiftTotal (todo ++ processed) ≤ Y) :
    averagedIteratedCorrelation f x Y processed ≤
      derivativeWeylEnvelope todo
        (averagedIteratedCorrelation f x Y (todo.reverse ++ processed)) := by
  induction todo generalizing processed hposProcessed with
  | nil => simp [derivativeWeylEnvelope]
  | cons head rest ih =>
      have hHnat : 1 ≤ head := hposTodo head (by simp)
      have hposRest : ∀ K ∈ rest, 0 < K := by
        intro K hK
        exact hposTodo K (by simp [hK])
      have hposNew : ∀ K ∈ head :: processed, 0 < K := by
        intro K hK
        simp only [List.mem_cons] at hK
        rcases hK with hK | hK
        · rw [hK]
          exact hposTodo head (by simp)
        · exact hposProcessed K hK
      have htotalNew : realShiftTotal (head :: processed) ≤ Y := by
        have hdecomp : realShiftTotal ((head :: rest) ++ processed) =
            realShiftTotal (head :: processed) + realShiftTotal rest := by
          calc
            _ = realShiftTotal (rest ++ (head :: processed)) :=
              realShiftTotal_prepend_append_commute head rest processed
            _ = realShiftTotal rest + realShiftTotal (head :: processed) :=
              realShiftTotal_append rest (head :: processed)
            _ = realShiftTotal (head :: processed) + realShiftTotal rest := by ring
        linarith [hdecomp, realShiftTotal_nonneg rest]
      have htotalIH : realShiftTotal (rest ++ (head :: processed)) ≤ Y := by
        calc
          realShiftTotal (rest ++ (head :: processed)) =
              realShiftTotal ((head :: rest) ++ processed) :=
            (realShiftTotal_prepend_append_commute head rest processed).symm
          _ ≤ Y := hTotal
      have hrec := averagedIteratedCorrelation_recurrence f x Y head processed
        hY hHnat hposProcessed htotalNew
      have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
      have hPpos := realShiftNormalizer_pos processed hposProcessed
      have hqnew : 0 ≤ averagedIteratedCorrelation f x Y (head :: processed) := by
        rw [averagedIteratedCorrelation_eq_normalized_sum f x Y (head :: processed)
          hYpos (realShiftNormalizer_pos (head :: processed) hposNew)]
        apply mul_nonneg (inv_nonneg.mpr
          (le_of_lt (realShiftNormalizer_pos (head :: processed) hposNew)))
        apply Finset.sum_nonneg
        intro shifts hshifts
        exact div_nonneg (norm_nonneg _) (le_of_lt hYpos)
      have hqpre : 0 ≤ averagedIteratedCorrelation f x Y processed := by
        rw [averagedIteratedCorrelation_eq_normalized_sum f x Y processed hYpos hPpos]
        apply mul_nonneg (inv_nonneg.mpr (le_of_lt hPpos))
        apply Finset.sum_nonneg
        intro shifts hshifts
        exact div_nonneg (norm_nonneg _) (le_of_lt hYpos)
      have hscalar := derivativeWeyl_scalar_step derivativeWeylConstant_pos
        (by exact_mod_cast (Nat.zero_lt_of_lt hHnat) : 0 < (head : ℝ)) hqnew
        derivativeWeylConstant_identity
      have hsq := hrec.trans hscalar
      have hroot : averagedIteratedCorrelation f x Y processed ≤
          Real.sqrt (max (derivativeWeylConstant ^ 2 / (head : ℝ))
            (derivativeWeylConstant * averagedIteratedCorrelation f x Y (head :: processed))) :=
        (Real.le_sqrt hqpre (by positivity)).2 hsq
      have hih := ih (head :: processed) hposRest hposNew htotalIH
      have hmax : max (derivativeWeylConstant ^ 2 / (head : ℝ))
          (derivativeWeylConstant * averagedIteratedCorrelation f x Y (head :: processed)) ≤
          max (derivativeWeylConstant ^ 2 / (head : ℝ))
            (derivativeWeylConstant *
              derivativeWeylEnvelope rest
                (averagedIteratedCorrelation f x Y (rest.reverse ++ (head :: processed)))) := by
        apply max_le_max le_rfl
        exact mul_le_mul_of_nonneg_left hih (le_of_lt derivativeWeylConstant_pos)
      have hroot' := Real.sqrt_le_sqrt hmax
      simpa [derivativeWeylEnvelope, List.reverse_cons, List.append_assoc] using
        hroot.trans hroot'

theorem averagedIteratedCorrelation_candidateMaximum_bound
    (f : ℝ → ℝ) (x Y : ℝ) (todo processed : List ℕ)
    (hY : 1 ≤ Y)
    (hposTodo : ∀ H ∈ todo, 0 < H)
    (hposProcessed : ∀ H ∈ processed, 0 < H)
    (hTotal : realShiftTotal (todo ++ processed) ≤ Y) :
    averagedIteratedCorrelation f x Y processed ≤
      derivativeWeylConstant * realListMaximum
        (derivativeWeylCandidates todo
          (averagedIteratedCorrelation f x Y (todo.reverse ++ processed))) := by
  have hfinalPos : ∀ H ∈ todo.reverse ++ processed, 0 < H := by
    intro H hH
    simp only [List.mem_append, List.mem_reverse] at hH
    rcases hH with hH | hH
    · exact hposTodo H hH
    · exact hposProcessed H hH
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hPpos := realShiftNormalizer_pos (todo.reverse ++ processed) hfinalPos
  have hTnonneg : 0 ≤ averagedIteratedCorrelation f x Y
      (todo.reverse ++ processed) := by
    rw [averagedIteratedCorrelation_eq_normalized_sum f x Y
      (todo.reverse ++ processed) hYpos hPpos]
    apply mul_nonneg (inv_nonneg.mpr (le_of_lt hPpos))
    apply Finset.sum_nonneg
    intro shifts hshifts
    exact div_nonneg (norm_nonneg _) (le_of_lt hYpos)
  calc
    averagedIteratedCorrelation f x Y processed ≤
        derivativeWeylEnvelope todo
          (averagedIteratedCorrelation f x Y (todo.reverse ++ processed)) :=
      averagedIteratedCorrelation_envelope f x Y todo processed hY
        hposTodo hposProcessed hTotal
    _ = derivativeWeylConstant * realListMaximum
        (derivativeWeylCandidates todo
          (averagedIteratedCorrelation f x Y (todo.reverse ++ processed))) :=
      derivativeWeylEnvelope_eq_constant_mul_candidateMaximum todo _ hTnonneg hposTodo

theorem averagedIteratedCorrelation_powerMaximum_bound
    (f : ℝ → ℝ) (x Y : ℝ) (todo processed : List ℕ)
    (hY : 1 ≤ Y)
    (hposTodo : ∀ H ∈ todo, 0 < H)
    (hposProcessed : ∀ H ∈ processed, 0 < H)
    (hTotal : realShiftTotal (todo ++ processed) ≤ Y) :
    averagedIteratedCorrelation f x Y processed ≤
      derivativeWeylConstant * realListMaximum
        (derivativeWeylPowerCandidates 0 todo
          (averagedIteratedCorrelation f x Y (todo.reverse ++ processed))) := by
  have hfinalPos : ∀ H ∈ todo.reverse ++ processed, 0 < H := by
    intro H hH
    simp only [List.mem_append, List.mem_reverse] at hH
    rcases hH with hH | hH
    · exact hposTodo H hH
    · exact hposProcessed H hH
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hPpos := realShiftNormalizer_pos (todo.reverse ++ processed) hfinalPos
  have hTnonneg : 0 ≤ averagedIteratedCorrelation f x Y
      (todo.reverse ++ processed) := by
    rw [averagedIteratedCorrelation_eq_normalized_sum f x Y
      (todo.reverse ++ processed) hYpos hPpos]
    apply mul_nonneg (inv_nonneg.mpr (le_of_lt hPpos))
    apply Finset.sum_nonneg
    intro shifts hshifts
    exact div_nonneg (norm_nonneg _) (le_of_lt hYpos)
  calc
    averagedIteratedCorrelation f x Y processed ≤
        derivativeWeylConstant * realListMaximum
          (derivativeWeylCandidates todo
            (averagedIteratedCorrelation f x Y (todo.reverse ++ processed))) :=
      averagedIteratedCorrelation_candidateMaximum_bound f x Y todo processed hY
        hposTodo hposProcessed hTotal
    _ = derivativeWeylConstant * realListMaximum
        (derivativeWeylPowerCandidates 0 todo
          (averagedIteratedCorrelation f x Y (todo.reverse ++ processed))) := by
      rw [derivativeWeylCandidates_eq_powerCandidates todo _ hTnonneg hposTodo]

theorem repeatedWeyl_difference_bound
    (f : ℝ → ℝ) (x Y : ℝ) (bounds : List ℕ)
    (hY : 1 ≤ Y) (hpos : ∀ H ∈ bounds, 0 < H)
    (hTotal : realShiftTotal bounds ≤ Y) :
    averagedIteratedCorrelation f x Y [] ≤
      derivativeWeylConstant * realListMaximum
        (derivativeWeylPowerCandidates 0 bounds
          (averagedIteratedCorrelation f x Y bounds)) := by
  have hTotal' : realShiftTotal (bounds ++ []) ≤ Y := by
    simpa using hTotal
  have hbound := averagedIteratedCorrelation_powerMaximum_bound
    f x Y bounds [] hY hpos (by simp) hTotal'
  simpa [List.append_nil, averagedIteratedCorrelation_reverse f x Y bounds] using hbound

/-- The unit rotation associated to an increment in the Kusmin--Landau
summation-by-parts argument. -/
noncomputable def kusminRotation (δ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I)

noncomputable def kusminPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem kusminPhase_sum_norm_le_card (S : Finset ℤ) (f : ℝ → ℝ) :
    ‖∑ n ∈ S, kusminPhase (f (n : ℝ))‖ ≤ S.card := by
  calc
    ‖∑ n ∈ S, kusminPhase (f (n : ℝ))‖ ≤
        ∑ n ∈ S, ‖kusminPhase (f (n : ℝ))‖ := norm_sum_le S _
    _ = ∑ n ∈ S, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [kusminPhase, Complex.norm_exp]
      simp
    _ = S.card := by simp

theorem kusminPhase_add (x y : ℝ) :
    kusminPhase (x + y) = kusminPhase x * kusminPhase y := by
  unfold kusminPhase
  rw [show (((2 * Real.pi * (x + y) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_add]

theorem kusminPhase_int (k : ℤ) : kusminPhase (k : ℝ) = 1 := by
  unfold kusminPhase
  rw [show (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I]

theorem kusminPhase_add_int (k : ℤ) (x : ℝ) :
    kusminPhase ((k : ℝ) + x) = kusminPhase x := by
  rw [kusminPhase_add, kusminPhase_int, one_mul]

theorem kusminRotation_ne_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    kusminRotation δ ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := (Complex.exp_eq_one_iff).mp h
  rw [← Complex.ofReal_intCast] at hk
  have him := congrArg Complex.im hk
  simp [Complex.mul_im, Complex.mul_re] at him
  have hcast : (k : ℝ) = δ := by
    nlinarith [Real.pi_pos]
  have hk0 : 0 < k := by exact_mod_cast (by linarith : (0:ℝ) < (k:ℝ))
  have hk1 : k < 1 := by exact_mod_cast (by linarith : (k:ℝ) < 1)
  omega

theorem kusmin_summand_identity {z znext : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hstep : znext = z * kusminRotation δ) :
    (1 - kusminRotation δ)⁻¹ * (z - znext) = z := by
  have hne := kusminRotation_ne_one hδ hδ1
  rw [hstep]
  field_simp [sub_ne_zero.mpr hne]

theorem kusminRotation_inv_eq_cot {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - kusminRotation δ)⁻¹ =
      (1 / 2 : ℂ) + (Complex.I / 2) * Complex.cot (Real.pi * (δ : ℂ)) := by
  have hne := kusminRotation_ne_one hδ hδ1
  have hphase : Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ)) =
      kusminRotation δ := by
    unfold kusminRotation
    congr 1
    push_cast
    ring
  rw [← hphase, Complex.cot_pi_eq_exp_ratio]
  have hden : 1 - Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ)) ≠ 0 := by
    intro hz
    have hz' : Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ)) - 1 = 0 := by
      linear_combination -hz
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ)) = 1 :=
      sub_eq_zero.mp hz'
    apply hne
    rw [← hphase]
    exact hexp
  field_simp [hden]
  ring

theorem kusminRotation_inv_norm {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖(1 - kusminRotation δ)⁻¹‖ = 1 / (2 * Real.sin (Real.pi * δ)) := by
  have hphase : kusminRotation δ =
      Complex.exp (Complex.I * (2 * Real.pi * δ : ℝ)) := by
    unfold kusminRotation
    congr 1
    push_cast
    ring
  have hargPos : 0 < Real.pi * δ := mul_pos Real.pi_pos hδ
  have hargLt : Real.pi * δ < Real.pi := by
    nlinarith [Real.pi_pos, hδ1]
  have hsin : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi hargPos hargLt
  rw [norm_inv]
  rw [show 1 - kusminRotation δ =
      -(Complex.exp (Complex.I * (2 * Real.pi * δ : ℝ)) - 1) by rw [hphase]; ring]
  rw [norm_neg, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * δ : ℝ) / 2 = Real.pi * δ by ring]
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hsin)]
  simp [one_div]

theorem kusminRotation_inv_sub_norm {u v : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1) :
    ‖(1 - kusminRotation u)⁻¹ - (1 - kusminRotation v)⁻¹‖ =
      |Real.cot (Real.pi * u) - Real.cot (Real.pi * v)| / 2 := by
  have huForm := kusminRotation_inv_eq_cot hu hu1
  have hvForm := kusminRotation_inv_eq_cot hv hv1
  have huArg : Real.pi * (u : ℂ) = ((Real.pi * u : ℝ) : ℂ) := by
    push_cast
    ring
  have hvArg : Real.pi * (v : ℂ) = ((Real.pi * v : ℝ) : ℂ) := by
    push_cast
    ring
  rw [huArg] at huForm
  rw [← Complex.ofReal_cot] at huForm
  rw [hvArg] at hvForm
  rw [← Complex.ofReal_cot] at hvForm
  calc
    ‖(1 - kusminRotation u)⁻¹ - (1 - kusminRotation v)⁻¹‖ =
        ‖(Complex.I / 2) *
          (((Real.cot (Real.pi * u) - Real.cot (Real.pi * v) : ℝ) : ℂ))‖ := by
            rw [huForm, hvForm]
            congr 1
            push_cast
            ring
    _ = ‖Complex.I / 2‖ *
          ‖((Real.cot (Real.pi * u) - Real.cot (Real.pi * v) : ℝ) : ℂ)‖ := norm_mul _ _
    _ = |Real.cot (Real.pi * u) - Real.cot (Real.pi * v)| / 2 := by
      rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [htwo]
      ring

theorem real_cot_sub_eq_sin_diff_div {a b : ℝ}
    (ha : 0 < a) (haπ : a < Real.pi)
    (hb : 0 < b) (hbπ : b < Real.pi) :
    Real.cot a - Real.cot b =
      Real.sin (b - a) / (Real.sin a * Real.sin b) := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha haπ
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  field_simp [ne_of_gt hsa, ne_of_gt hsb]
  rw [Real.sin_sub]
  ring

theorem real_cot_antitone_on_Ioo {a b : ℝ}
    (ha : 0 < a) (haπ : a < Real.pi)
    (hb : 0 < b) (hbπ : b < Real.pi) (hab : a ≤ b) :
    Real.cot b ≤ Real.cot a := by
  have hsinDiff : 0 ≤ Real.sin (b - a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hab) (by linarith)
  have hsinA : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha haπ
  have hsinB : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  have hdiff := real_cot_sub_eq_sin_diff_div ha haπ hb hbπ
  have hnonneg : 0 ≤ Real.cot a - Real.cot b := by
    rw [hdiff]
    exact div_nonneg hsinDiff (le_of_lt (mul_pos hsinA hsinB))
  linarith

theorem real_sin_pi_mul_lower_bound {θ δ : ℝ}
    (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2)
    (hlo : θ ≤ δ) (hhi : δ ≤ 1 - θ) :
    Real.sin (Real.pi * θ) ≤ Real.sin (Real.pi * δ) := by
  have hθarg : 0 ≤ Real.pi * θ := le_of_lt (mul_pos Real.pi_pos hθ)
  have hθargTop : Real.pi * θ ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos, hθhalf]
  by_cases hδhalf : δ ≤ 1 / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hδhalf])
      (by nlinarith [Real.pi_pos, hlo])
  · have hδ'lo : θ ≤ 1 - δ := by linarith
    have hδ'hi : 1 - δ ≤ 1 / 2 := by linarith
    have hsym : Real.sin (Real.pi * δ) =
        Real.sin (Real.pi * (1 - δ)) := by
      rw [show Real.pi * (1 - δ) = Real.pi - Real.pi * δ by ring,
        Real.sin_pi_sub]
    rw [hsym]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hδ'hi])
      (by nlinarith [Real.pi_pos, hδ'lo])

theorem real_cot_pi_one_sub {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    Real.cot (Real.pi * (1 - θ)) = -Real.cot (Real.pi * θ) := by
  have hθarg : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ
  have hθargLt : Real.pi * θ < Real.pi := by nlinarith [Real.pi_pos, hθ1]
  rw [show Real.pi * (1 - θ) = Real.pi - Real.pi * θ by ring,
    Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    Real.cos_pi_sub, Real.sin_pi_sub]
  ring

theorem real_cot_pi_nonneg {θ : ℝ} (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) :
    0 ≤ Real.cot (Real.pi * θ) := by
  rw [Real.cot_eq_cos_div_sin]
  have hargPos : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ
  have hargLe : Real.pi * θ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hθhalf]
  have hsin : 0 < Real.sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi hargPos (by linarith [Real.pi_pos, hθhalf])
  have hcos : 0 ≤ Real.cos (Real.pi * θ) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, hargLe⟩
  exact div_nonneg hcos hsin.le

theorem sum_range_abs_diff_succ_eq_sub_of_antitone (f : ℕ → ℝ) :
    ∀ n : ℕ, (∀ i, i < n → f (i + 1) ≤ f i) →
      (∑ i ∈ Finset.range n, |f (i + 1) - f i|) = f 0 - f n
  | 0, _ => by simp
  | n + 1, h => by
      rw [Finset.sum_range_succ]
      rw [sum_range_abs_diff_succ_eq_sub_of_antitone f n
        (fun i hi => h i (by omega))]
      rw [abs_of_nonpos (sub_nonpos.mpr (h n (by omega)))]
      ring

theorem sum_range_abs_diff_succ_eq_sub_of_monotone (f : ℕ → ℝ) :
    ∀ n : ℕ, (∀ i, i < n → f i ≤ f (i + 1)) →
      (∑ i ∈ Finset.range n, |f (i + 1) - f i|) = f n - f 0
  | 0, _ => by simp
  | n + 1, h => by
      rw [Finset.sum_range_succ]
      rw [sum_range_abs_diff_succ_eq_sub_of_monotone f n
        (fun i hi => h i (by omega))]
      rw [abs_of_nonneg (sub_nonneg.mpr (h n (by omega)))]
      ring

theorem kusmin_cot_variation_le {θ : ℝ} (hθ : 0 < θ)
    (hθhalf : θ ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m)
    (δ : ℕ → ℝ)
    (hlo : ∀ i, i < m → θ ≤ δ i)
    (hhi : ∀ i, i < m → δ i ≤ 1 - θ)
    (hmono : (∀ i, i < m - 1 → δ i ≤ δ (i + 1)) ∨
      (∀ i, i < m - 1 → δ (i + 1) ≤ δ i)) :
    (∑ i ∈ Finset.range (m - 1),
      |Real.cot (Real.pi * δ (i + 1)) - Real.cot (Real.pi * δ i)|) / 2 ≤
        Real.cot (Real.pi * θ) := by
  let g : ℕ → ℝ := fun i => Real.cot (Real.pi * δ i)
  have hθ1 : θ < 1 := by nlinarith [hθhalf]
  have hcotNonneg := real_cot_pi_nonneg hθ hθhalf
  have hδpos (i : ℕ) (hi : i < m) : 0 < δ i := lt_of_lt_of_le hθ (hlo i hi)
  have hδlt (i : ℕ) (hi : i < m) : δ i < 1 := by
    have := hhi i hi
    linarith
  have hargpos (i : ℕ) (hi : i < m) : 0 < Real.pi * δ i :=
    mul_pos Real.pi_pos (hδpos i hi)
  have harglt (i : ℕ) (hi : i < m) : Real.pi * δ i < Real.pi := by
    nlinarith [Real.pi_pos, hδlt i hi]
  have hthetaArgPos : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ
  have hthetaArgLt : Real.pi * θ < Real.pi := by
    nlinarith [Real.pi_pos, hθhalf]
  have hreflectArgPos : 0 < Real.pi * (1 - θ) :=
    mul_pos Real.pi_pos (by linarith [hθhalf])
  have hreflectArgLt : Real.pi * (1 - θ) < Real.pi := by
    nlinarith [Real.pi_pos, hθ]
  have hlowcot (i : ℕ) (hi : i < m) : -Real.cot (Real.pi * θ) ≤ g i := by
    have hendpoint : Real.cot (Real.pi * (1 - θ)) ≤ g i := by
      apply real_cot_antitone_on_Ioo
      · exact hargpos i hi
      · exact harglt i hi
      · exact hreflectArgPos
      · exact hreflectArgLt
      · exact mul_le_mul_of_nonneg_left (hhi i hi) Real.pi_pos.le
    rw [real_cot_pi_one_sub hθ hθ1] at hendpoint
    exact hendpoint
  have hhighcot (i : ℕ) (hi : i < m) : g i ≤ Real.cot (Real.pi * θ) := by
    apply real_cot_antitone_on_Ioo
    · exact hthetaArgPos
    · exact hthetaArgLt
    · exact hargpos i hi
    · exact harglt i hi
    · exact mul_le_mul_of_nonneg_left (hlo i hi) Real.pi_pos.le
  have hfirst : 0 < m := by omega
  have hlast : m - 1 < m := by omega
  have hends : |g (m - 1) - g 0| ≤ 2 * Real.cot (Real.pi * θ) := by
    have hlastLow := hlowcot (m - 1) hlast
    have hlastHigh := hhighcot (m - 1) hlast
    have hfirstLow := hlowcot 0 hfirst
    have hfirstHigh := hhighcot 0 hfirst
    rw [abs_le]
    constructor <;> linarith
  have hvariation :
      (∑ i ∈ Finset.range (m - 1), |g (i + 1) - g i|) ≤
        2 * Real.cot (Real.pi * θ) := by
    rcases hmono with hinc | hdec
    · have hgmono : ∀ i, i < m - 1 → g (i + 1) ≤ g i := by
        intro i hi
        apply real_cot_antitone_on_Ioo
        · exact hargpos i (by omega)
        · exact harglt i (by omega)
        · exact hargpos (i + 1) (by omega)
        · exact harglt (i + 1) (by omega)
        · exact mul_le_mul_of_nonneg_left (hinc i hi) Real.pi_pos.le
      rw [sum_range_abs_diff_succ_eq_sub_of_antitone g (m - 1) hgmono]
      have hdiff := hends
      rw [abs_le] at hdiff
      linarith
    · have hgmono : ∀ i, i < m - 1 → g i ≤ g (i + 1) := by
        intro i hi
        apply real_cot_antitone_on_Ioo
        · exact hargpos (i + 1) (by omega)
        · exact harglt (i + 1) (by omega)
        · exact hargpos i (by omega)
        · exact harglt i (by omega)
        · exact mul_le_mul_of_nonneg_left (hdec i hi) Real.pi_pos.le
      rw [sum_range_abs_diff_succ_eq_sub_of_monotone g (m - 1) hgmono]
      have hdiff := hends
      rw [abs_le] at hdiff
      linarith
  have hsum :
      (∑ i ∈ Finset.range (m - 1),
        |Real.cot (Real.pi * δ (i + 1)) - Real.cot (Real.pi * δ i)|) =
        ∑ i ∈ Finset.range (m - 1), |g (i + 1) - g i| := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [g, abs_sub_comm]
  rw [hsum]
  nlinarith

theorem kusminRotation_inv_norm_le_of_mem_Icc {θ δ : ℝ}
    (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2)
    (hδlo : θ ≤ δ) (hδhi : δ ≤ 1 - θ) :
    ‖(1 - kusminRotation δ)⁻¹‖ ≤
      1 / (2 * Real.sin (Real.pi * θ)) := by
  have hδ : 0 < δ := lt_of_lt_of_le hθ hδlo
  have hδ1 : δ < 1 := by linarith
  have hsin := real_sin_pi_mul_lower_bound hθ hθhalf hδlo hδhi
  have hsinθ : 0 < Real.sin (Real.pi * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos hθ
    · nlinarith [Real.pi_pos, hθhalf]
  have hsinδ : 0 < Real.sin (Real.pi * δ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos hδ
    · nlinarith [Real.pi_pos, hδhi, hθ]
  rw [kusminRotation_inv_norm hδ hδ1]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem kusminRotation_one_sub_inv_norm_le_of_mem_Icc {θ δ : ℝ}
    (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2)
    (hδlo : θ ≤ δ) (hδhi : δ ≤ 1 - θ) :
    ‖1 - (1 - kusminRotation δ)⁻¹‖ ≤
      1 / (2 * Real.sin (Real.pi * θ)) := by
  have hδ : 0 < δ := lt_of_lt_of_le hθ hδlo
  have hδ1 : δ < 1 := by linarith
  have hunit : ‖kusminRotation δ‖ = 1 := by
    rw [kusminRotation, Complex.norm_exp]
    simp
  have hden : 1 - kusminRotation δ ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (kusminRotation_ne_one hδ hδ1))
  have halgebra : 1 - (1 - kusminRotation δ)⁻¹ =
      -kusminRotation δ * (1 - kusminRotation δ)⁻¹ := by
    field_simp [hden]
    ring
  rw [halgebra, norm_mul, norm_neg, hunit, one_mul]
  exact kusminRotation_inv_norm_le_of_mem_Icc hθ hθhalf hδlo hδhi

/-- Finite summation by parts in the exact indexing used by the
Kusmin--Landau sequence estimate. -/
theorem kusmin_finite_summation_by_parts
    (m : ℕ) (z q : ℕ → ℂ)
    (hrel : ∀ i ∈ Finset.range m,
      q i * (z i - z (i + 1)) = z i) :
    (∑ i ∈ Finset.range (m + 1), z i) =
      q 0 * z 0 +
        (∑ i ∈ Finset.range (m - 1),
          (q (i + 1) - q i) * z (i + 1)) +
        (1 - q (m - 1)) * z m := by
  have htel (n : ℕ) :
      (∑ i ∈ Finset.range n, (z i - z (i + 1))) = z 0 - z n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hsum :
      (∑ i ∈ Finset.range m, z i) =
        q (m - 1) * (z 0 - z m) -
          ∑ i ∈ Finset.range (m - 1),
            (q (i + 1) - q i) * (z 0 - z (i + 1)) := by
    calc
      (∑ i ∈ Finset.range m, z i) =
          ∑ i ∈ Finset.range m, q i * (z i - z (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hrel i hi).symm
      _ = q (m - 1) * (z 0 - z m) -
          ∑ i ∈ Finset.range (m - 1),
            (q (i + 1) - q i) * (z 0 - z (i + 1)) := by
        have hparts := Finset.sum_range_by_parts q
          (fun i => z i - z (i + 1)) m
        simp only [smul_eq_mul] at hparts
        simpa [htel] using hparts
  have htelQ :
      (∑ i ∈ Finset.range (m - 1), (q (i + 1) - q i)) =
        q (m - 1) - q 0 := by
    simpa using Finset.sum_range_sub q (m - 1)
  rw [Finset.sum_range_succ, hsum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, htelQ]
  ring

theorem kusmin_sequence_bound_aux {θ : ℝ} (hθ : 0 < θ)
    (hθhalf : θ ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m)
    (z : ℕ → ℂ) (δ : ℕ → ℝ)
    (hz : ∀ i, i ≤ m → ‖z i‖ = 1)
    (hstep : ∀ i, i < m → z (i + 1) = z i * kusminRotation (δ i))
    (hlo : ∀ i, i < m → θ ≤ δ i)
    (hhi : ∀ i, i < m → δ i ≤ 1 - θ)
    (hmono : (∀ i, i < m - 1 → δ i ≤ δ (i + 1)) ∨
      (∀ i, i < m - 1 → δ (i + 1) ≤ δ i)) :
    ‖∑ i ∈ Finset.range (m + 1), z i‖ ≤
      1 / Real.sin (Real.pi * θ) + Real.cot (Real.pi * θ) := by
  let q : ℕ → ℂ := fun i => (1 - kusminRotation (δ i))⁻¹
  have hqrel : ∀ i ∈ Finset.range m, q i * (z i - z (i + 1)) = z i := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    dsimp [q]
    exact kusmin_summand_identity
      (lt_of_lt_of_le hθ (hlo i hi'))
      (by have := hhi i hi'; linarith)
      (hstep i hi')
  have hparts := kusmin_finite_summation_by_parts m z q hqrel
  have hqfirst := kusminRotation_inv_norm_le_of_mem_Icc hθ hθhalf
    (hlo 0 (by omega)) (hhi 0 (by omega))
  have hqfinal := kusminRotation_one_sub_inv_norm_le_of_mem_Icc hθ hθhalf
    (hlo (m - 1) (by omega)) (hhi (m - 1) (by omega))
  have hvariation :
      (∑ i ∈ Finset.range (m - 1), ‖q (i + 1) - q i‖) ≤
        Real.cot (Real.pi * θ) := by
    calc
      (∑ i ∈ Finset.range (m - 1), ‖q (i + 1) - q i‖) =
          (∑ i ∈ Finset.range (m - 1),
            |Real.cot (Real.pi * δ (i + 1)) - Real.cot (Real.pi * δ i)|) / 2 := by
        calc
          (∑ i ∈ Finset.range (m - 1), ‖q (i + 1) - q i‖) =
              ∑ i ∈ Finset.range (m - 1),
                |Real.cot (Real.pi * δ (i + 1)) - Real.cot (Real.pi * δ i)| / 2 := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  have hi' : i < m - 1 := Finset.mem_range.mp hi
                  have hip : 0 < δ (i + 1) := lt_of_lt_of_le hθ (hlo (i + 1) (by omega))
                  have hip1 : δ (i + 1) < 1 := by have := hhi (i + 1) (by omega); linarith
                  have hiq : 0 < δ i := lt_of_lt_of_le hθ (hlo i (by omega))
                  have hiq1 : δ i < 1 := by have := hhi i (by omega); linarith
                  simpa [q] using (kusminRotation_inv_sub_norm hip hip1 hiq hiq1)
          _ = (∑ i ∈ Finset.range (m - 1),
                |Real.cot (Real.pi * δ (i + 1)) - Real.cot (Real.pi * δ i)|) / 2 := by
                  simp_rw [div_eq_mul_inv]
                  rw [Finset.sum_mul]
      _ ≤ Real.cot (Real.pi * θ) :=
        kusmin_cot_variation_le hθ hθhalf hm δ hlo hhi hmono
  rw [hparts]
  calc
    ‖q 0 * z 0 +
        (∑ i ∈ Finset.range (m - 1), (q (i + 1) - q i) * z (i + 1)) +
        (1 - q (m - 1)) * z m‖ ≤
      ‖q 0 * z 0‖ +
        ‖∑ i ∈ Finset.range (m - 1), (q (i + 1) - q i) * z (i + 1)‖ +
        ‖(1 - q (m - 1)) * z m‖ := by
          calc
            ‖(q 0 * z 0 +
                (∑ i ∈ Finset.range (m - 1), (q (i + 1) - q i) * z (i + 1)) +
                (1 - q (m - 1)) * z m)‖ ≤
              ‖q 0 * z 0 +
                (∑ i ∈ Finset.range (m - 1), (q (i + 1) - q i) * z (i + 1))‖ +
                ‖(1 - q (m - 1)) * z m‖ := norm_add_le _ _
            _ ≤ ‖q 0 * z 0‖ +
                ‖∑ i ∈ Finset.range (m - 1), (q (i + 1) - q i) * z (i + 1)‖ +
                ‖(1 - q (m - 1)) * z m‖ := by
                  exact add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ ‖q 0‖ +
        (∑ i ∈ Finset.range (m - 1), ‖(q (i + 1) - q i) * z (i + 1)‖) +
        ‖1 - q (m - 1)‖ := by
          have hsumNorm := norm_sum_le (Finset.range (m - 1)) (fun i : ℕ =>
            (q (i + 1) - q i) * z (i + 1))
          calc
            ‖q 0 * z 0‖ +
                ‖∑ i ∈ Finset.range (m - 1), (q (i + 1) - q i) * z (i + 1)‖ +
                ‖(1 - q (m - 1)) * z m‖ =
              ‖q 0‖ +
                ‖∑ i ∈ Finset.range (m - 1), (q (i + 1) - q i) * z (i + 1)‖ +
                ‖1 - q (m - 1)‖ := by
                  rw [norm_mul, hz 0 (by omega), mul_one,
                    norm_mul, hz m (by omega), mul_one]
            _ ≤ ‖q 0‖ +
                (∑ i ∈ Finset.range (m - 1), ‖(q (i + 1) - q i) * z (i + 1)‖) +
                ‖1 - q (m - 1)‖ := by
                  gcongr
    _ ≤ 1 / (2 * Real.sin (Real.pi * θ)) +
        Real.cot (Real.pi * θ) +
        1 / (2 * Real.sin (Real.pi * θ)) := by
          have hsumNorm :
              (∑ i ∈ Finset.range (m - 1), ‖(q (i + 1) - q i) * z (i + 1)‖) ≤
                ∑ i ∈ Finset.range (m - 1), ‖q (i + 1) - q i‖ := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' : i < m - 1 := Finset.mem_range.mp hi
            rw [norm_mul, hz (i + 1) (by omega), mul_one]
          have hqfirst' : ‖q 0‖ ≤ 1 / (2 * Real.sin (Real.pi * θ)) := by
            simpa [q] using hqfirst
          have hqfinal' : ‖1 - q (m - 1)‖ ≤
              1 / (2 * Real.sin (Real.pi * θ)) := by
            simpa [q] using hqfinal
          exact add_le_add
            (add_le_add hqfirst' (le_trans hsumNorm hvariation)) hqfinal'
    _ = 1 / Real.sin (Real.pi * θ) + Real.cot (Real.pi * θ) := by
      have hsin : Real.sin (Real.pi * θ) ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hθ)
          (by nlinarith [Real.pi_pos, hθhalf]))
      field_simp [hsin]
      ring

theorem real_csc_add_cot_eq_cot_half {θ : ℝ}
    (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) :
    1 / Real.sin (Real.pi * θ) + Real.cot (Real.pi * θ) =
      Real.cot (Real.pi * θ / 2) := by
  have hxpos : 0 < Real.pi * θ / 2 := by positivity
  have hxlt : Real.pi * θ / 2 < Real.pi / 2 := by
    nlinarith [Real.pi_pos, hθhalf]
  have hsinx : Real.sin (Real.pi * θ / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact hxpos
    · linarith [Real.pi_pos]
  have hcosx : Real.cos (Real.pi * θ / 2) ≠ 0 := by
    apply ne_of_gt
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt⟩
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    show Real.pi * θ = 2 * (Real.pi * θ / 2) by ring,
    Real.sin_two_mul, Real.cos_two_mul]
  field_simp [hsinx, hcosx]
  ring

theorem kusmin_sequence_bound {θ : ℝ} (hθ : 0 < θ)
    (hθhalf : θ ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m)
    (z : ℕ → ℂ) (δ : ℕ → ℝ)
    (hz : ∀ i, i ≤ m → ‖z i‖ = 1)
    (hstep : ∀ i, i < m → z (i + 1) = z i * kusminRotation (δ i))
    (hlo : ∀ i, i < m → θ ≤ δ i)
    (hhi : ∀ i, i < m → δ i ≤ 1 - θ)
    (hmono : (∀ i, i < m - 1 → δ i ≤ δ (i + 1)) ∨
      (∀ i, i < m - 1 → δ (i + 1) ≤ δ i)) :
    ‖∑ i ∈ Finset.range (m + 1), z i‖ ≤ Real.cot (Real.pi * θ / 2) := by
  calc
    ‖∑ i ∈ Finset.range (m + 1), z i‖ ≤
        1 / Real.sin (Real.pi * θ) + Real.cot (Real.pi * θ) :=
      kusmin_sequence_bound_aux hθ hθhalf hm z δ hz hstep hlo hhi hmono
    _ = Real.cot (Real.pi * θ / 2) :=
      real_csc_add_cot_eq_cot_half hθ hθhalf

theorem real_cot_pi_theta_div_two_ge_one {θ : ℝ}
    (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) :
    1 ≤ Real.cot (Real.pi * θ / 2) := by
  have hargPos : 0 < Real.pi * θ / 2 := by positivity
  have hargLt : Real.pi * θ / 2 < Real.pi := by
    nlinarith [Real.pi_pos, hθhalf]
  have hquarterPos : 0 < Real.pi / 4 := by positivity
  have hquarterLt : Real.pi / 4 < Real.pi := by nlinarith [Real.pi_pos]
  have hargLe : Real.pi * θ / 2 ≤ Real.pi / 4 := by
    nlinarith [Real.pi_pos, hθhalf]
  have hcot := real_cot_antitone_on_Ioo hargPos hargLt
    hquarterPos hquarterLt hargLe
  rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_four, Real.sin_pi_div_four] at hcot
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hsqrt] at hcot
  exact hcot

theorem real_cot_le_inv_of_mem_Ioc {u : ℝ}
    (hu : 0 < u) (huπ : u ≤ Real.pi / 2) : Real.cot u ≤ 1 / u := by
  let g : ℝ → ℝ := fun t => Real.sin t - t * Real.cos t
  have hgcont : ContinuousOn g (Set.Icc 0 (Real.pi / 2)) := by
    fun_prop
  have hgdiff : DifferentiableOn ℝ g (interior (Set.Icc 0 (Real.pi / 2))) := by
    fun_prop
  have hgderiv : ∀ t ∈ interior (Set.Icc 0 (Real.pi / 2)),
      0 ≤ deriv g t := by
    intro t ht
    have ht' : t ∈ Set.Ioo 0 (Real.pi / 2) := by
      simpa [interior_Icc] using ht
    have hformula : deriv g t = t * Real.sin t := by
      have hsinD : HasDerivAt Real.sin (Real.cos t) t := Real.hasDerivAt_sin t
      have hmulD : HasDerivAt (fun x : ℝ => x * Real.cos x)
          (Real.cos t - t * Real.sin t) t := by
        convert (hasDerivAt_id t).mul (Real.hasDerivAt_cos t) using 1
        · rfl
        · simp [id]
          ring
      have hgD : HasDerivAt g (t * Real.sin t) t := by
        dsimp [g]
        convert hsinD.sub hmulD using 1
        ring
      exact hgD.deriv
    rw [hformula]
    apply mul_nonneg (le_of_lt ht'.1)
    exact Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt ht'.1)
      (by nlinarith [Real.pi_pos, ht'.2])
  have hgmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2))
    hgcont hgdiff hgderiv
  have hgu : 0 ≤ g u := by
    have huIcc : u ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hu, huπ⟩
    have hzero : g 0 = 0 := by simp [g]
    rw [← hzero]
    exact hgmono ⟨le_rfl, by positivity⟩ huIcc hu.le
  have hsin : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos, huπ])
  rw [Real.cot_eq_cos_div_sin]
  rw [div_le_div_iff₀ hsin hu]
  have hmul : u * Real.cos u ≤ Real.sin u := by
    dsimp [g] at hgu
    nlinarith
  nlinarith [hmul]

theorem real_derivativeBand_partition_cover {A B : ℤ} {θ t : ℝ}
    (hAB : A < B) (hθ : 0 < θ)
    (htA : (A : ℝ) ≤ t) (htB : t ≤ (B : ℝ)) :
    t ∈ Set.Icc (A : ℝ) ((A : ℝ) + θ) ∨
    t ∈ Set.Ioc ((B : ℝ) - θ) (B : ℝ) ∨
    (∃ k : ℤ, A < k ∧ k < B ∧
      t ∈ Set.Ioc ((k : ℝ) - θ) ((k : ℝ) + θ)) ∨
    (∃ k : ℤ, A ≤ k ∧ k < B ∧
      t ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ)) := by
  by_cases hteq : t = (B : ℝ)
  · right
    left
    rw [Set.mem_Ioc]
    constructor
    · rw [hteq]
      have hAB' : (A : ℝ) < (B : ℝ) := by exact_mod_cast hAB
      linarith
    · exact le_of_eq hteq
  · have htB' : t < (B : ℝ) := lt_of_le_of_ne htB hteq
    let j : ℤ := Int.floor t
    let r : ℝ := Int.fract t
    have hjA : A ≤ j := (Int.le_floor).mpr htA
    have hjB : j < B := (Int.floor_lt).mpr htB'
    have hr0 : 0 ≤ r := by dsimp [r]; exact Int.fract_nonneg t
    have hr1 : r < 1 := by dsimp [r]; exact Int.fract_lt_one t
    have htr : t = (j : ℝ) + r := by
      dsimp [j, r]
      exact (Int.floor_add_fract t).symm
    by_cases hrθ : r ≤ θ
    · by_cases hjEq : j = A
      · left
        rw [Set.mem_Icc]
        constructor
        · exact htA
        · rw [htr, hjEq]
          linarith
      · right
        right
        left
        refine ⟨j, ?_, hjB, ?_⟩
        · omega
        · rw [Set.mem_Ioc, htr]
          constructor
          · have hjAcast : (A : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjA
            linarith [hθ]
          · linarith
    · have hθr : θ < r := lt_of_not_ge hrθ
      by_cases hrUpper : r ≤ 1 - θ
      · right
        right
        right
        refine ⟨j, hjA, hjB, ?_⟩
        rw [Set.mem_Ioc, htr]
        constructor <;> linarith
      · have hrNear : 1 - θ < r := lt_of_not_ge hrUpper
        have hjSuccLe : j + 1 ≤ B := by omega
        by_cases hjSuccEq : j + 1 = B
        · right
          left
          rw [Set.mem_Ioc]
          constructor
          · have hjSuccCast : (j : ℝ) + 1 = (B : ℝ) := by exact_mod_cast hjSuccEq
            rw [htr]
            linarith
          · exact htB
        · right
          right
          left
          refine ⟨j + 1, ?_, ?_, ?_⟩
          · omega
          · omega
          · rw [Set.mem_Ioc, htr]
            push_cast
            constructor <;> linarith

inductive DerivativeBandLabel (A B : ℤ) where
  | low
  | high
  | resonant (k : ℤ) (hkA : A < k) (hkB : k < B)
  | good (k : ℤ) (hkA : A ≤ k) (hkB : k < B)
  deriving DecidableEq

def derivativeBandMem {A B : ℤ} (θ t : ℝ) : DerivativeBandLabel A B → Prop
  | .low => t ∈ Set.Icc (A : ℝ) ((A : ℝ) + θ)
  | .high => t ∈ Set.Ioc ((B : ℝ) - θ) (B : ℝ)
  | .resonant k _ _ => t ∈ Set.Ioc ((k : ℝ) - θ) ((k : ℝ) + θ)
  | .good k _ _ => t ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ)

def derivativeBandLabelFinset {A B : ℤ} : Finset (DerivativeBandLabel A B) :=
  let resonantLabels := (Finset.Ico (A + 1) B).attach.image fun k =>
    DerivativeBandLabel.resonant k.1
      (by have hk := Finset.mem_Ico.mp k.2; omega)
      (by have hk := Finset.mem_Ico.mp k.2; omega)
  let goodLabels := (Finset.Ico A B).attach.image fun k =>
    DerivativeBandLabel.good k.1
      (by have hk := Finset.mem_Ico.mp k.2; omega)
      (by have hk := Finset.mem_Ico.mp k.2; omega)
  insert DerivativeBandLabel.low (insert DerivativeBandLabel.high
    (resonantLabels ∪ goodLabels))

def resonantDerivativeBandLabelMap {A B : ℤ}
    (i : {k // k ∈ Finset.Ico (A + 1) B}) : DerivativeBandLabel A B :=
  .resonant i.1
    (by have hi := Finset.mem_Ico.mp i.2; omega)
    (by have hi := Finset.mem_Ico.mp i.2; omega)

theorem resonantDerivativeBandLabelMap_injective {A B : ℤ} :
    Function.Injective (@resonantDerivativeBandLabelMap A B) := by
  intro i j hij
  apply Subtype.ext
  injection hij

theorem resonantDerivativeBandLabelMap_const_sum {A B : ℤ}
    (hAB : A < B) (c : ℝ) :
    (∑ _band ∈ (Finset.Ico (A + 1) B).attach.image
      (@resonantDerivativeBandLabelMap A B), c) =
      ((B - A - 1 : ℤ) : ℝ) * c := by
  have hinj : Set.InjOn (@resonantDerivativeBandLabelMap A B)
      ↑(Finset.Ico (A + 1) B).attach := by
    intro i hi j hj hij
    exact resonantDerivativeBandLabelMap_injective hij
  rw [Finset.sum_image hinj, Finset.sum_const]
  simp only [Finset.card_attach, nsmul_eq_mul]
  have hcardInt : ((Finset.Ico (A + 1) B).card : ℤ) = B - A - 1 := by
    rw [Int.card_Ico_of_le (A + 1) B (by omega)]
    omega
  have hcardReal : ((Finset.Ico (A + 1) B).card : ℝ) =
      ((B - A - 1 : ℤ) : ℝ) := by exact_mod_cast hcardInt
  rw [hcardReal]

def goodDerivativeBandLabelMap {A B : ℤ}
    (i : {k // k ∈ Finset.Ico A B}) : DerivativeBandLabel A B :=
  .good i.1
    (by have hi := Finset.mem_Ico.mp i.2; omega)
    (by have hi := Finset.mem_Ico.mp i.2; omega)

theorem goodDerivativeBandLabelMap_injective {A B : ℤ} :
    Function.Injective (@goodDerivativeBandLabelMap A B) := by
  intro i j hij
  apply Subtype.ext
  injection hij

theorem goodDerivativeBandLabelMap_const_sum {A B : ℤ}
    (hAB : A < B) (c : ℝ) :
    (∑ _band ∈ (Finset.Ico A B).attach.image
      (@goodDerivativeBandLabelMap A B), c) =
      ((B - A : ℤ) : ℝ) * c := by
  have hinj : Set.InjOn (@goodDerivativeBandLabelMap A B)
      ↑(Finset.Ico A B).attach := by
    intro i hi j hj hij
    exact goodDerivativeBandLabelMap_injective hij
  rw [Finset.sum_image hinj, Finset.sum_const]
  simp only [Finset.card_attach, nsmul_eq_mul]
  have hcardInt : ((Finset.Ico A B).card : ℤ) = B - A :=
    Int.card_Ico_of_le A B hAB.le
  have hcardReal : ((Finset.Ico A B).card : ℝ) = ((B - A : ℤ) : ℝ) :=
    by exact_mod_cast hcardInt
  rw [hcardReal]

theorem derivativeBandLabelFinset_bound_sum {A B : ℤ} (hAB : A < B)
    (θ lam : ℝ) :
    (∑ band ∈ derivativeBandLabelFinset (A := A) (B := B),
      (match band with
       | .low => 1 + θ / lam
       | .high => 1 + θ / lam
       | .resonant _ _ _ => 1 + 2 * θ / lam
       | .good _ _ _ => Real.cot (Real.pi * θ / 2))) =
      ((B - A : ℤ) : ℝ) *
        (1 + 2 * θ / lam + Real.cot (Real.pi * θ / 2)) + 1 := by
  classical
  let R : Finset (DerivativeBandLabel A B) :=
    (Finset.Ico (A + 1) B).attach.image
      (@resonantDerivativeBandLabelMap A B)
  let G : Finset (DerivativeBandLabel A B) :=
    (Finset.Ico A B).attach.image (@goodDerivativeBandLabelMap A B)
  have hdis : Disjoint R G := by
    rw [Finset.disjoint_left]
    intro z hzR hzG
    rcases Finset.mem_image.mp hzR with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hzG with ⟨g, hg, hEq⟩
    cases hEq
  have hlow : DerivativeBandLabel.low ∉ insert DerivativeBandLabel.high (R ∪ G) := by
    simp [R, G, resonantDerivativeBandLabelMap, goodDerivativeBandLabelMap]
  have hhigh : DerivativeBandLabel.high ∉ R ∪ G := by
    simp [R, G, resonantDerivativeBandLabelMap, goodDerivativeBandLabelMap]
  have hlabels : derivativeBandLabelFinset (A := A) (B := B) =
      insert DerivativeBandLabel.low (insert DerivativeBandLabel.high (R ∪ G)) := by
    ext z
    simp [derivativeBandLabelFinset, R, G,
      resonantDerivativeBandLabelMap, goodDerivativeBandLabelMap]
  rw [hlabels, Finset.sum_insert hlow, Finset.sum_insert hhigh,
    Finset.sum_union hdis]
  have hR := resonantDerivativeBandLabelMap_const_sum hAB
    (1 + 2 * θ / lam)
  have hG := goodDerivativeBandLabelMap_const_sum hAB
    (Real.cot (Real.pi * θ / 2))
  have hR' : (∑ band ∈ R, (1 + 2 * θ / lam)) =
      ((B - A - 1 : ℤ) : ℝ) * (1 + 2 * θ / lam) := by
    simpa [R] using hR
  have hG' : (∑ band ∈ G, Real.cot (Real.pi * θ / 2)) =
      ((B - A : ℤ) : ℝ) * Real.cot (Real.pi * θ / 2) := by
    simpa [G] using hG
  have hsumR : (∑ band ∈ R,
          (match band with
           | .low => 1 + θ / lam
           | .high => 1 + θ / lam
           | .resonant _ _ _ => 1 + 2 * θ / lam
           | .good _ _ _ => Real.cot (Real.pi * θ / 2))) =
      ∑ band ∈ R, (1 + 2 * θ / lam) := by
    apply Finset.sum_congr rfl
    intro band hband
    rcases Finset.mem_image.mp hband with ⟨i, hi, rfl⟩
    rfl
  have hsumG : (∑ band ∈ G,
          (match band with
           | .low => 1 + θ / lam
           | .high => 1 + θ / lam
           | .resonant _ _ _ => 1 + 2 * θ / lam
           | .good _ _ _ => Real.cot (Real.pi * θ / 2))) =
      ∑ band ∈ G, Real.cot (Real.pi * θ / 2) := by
    apply Finset.sum_congr rfl
    intro band hband
    rcases Finset.mem_image.mp hband with ⟨i, hi, rfl⟩
    rfl
  rw [hsumR, hsumG]
  rw [hR', hG']
  push_cast
  ring

theorem derivativeBandLabel_mem_finset {A B : ℤ}
    (band : DerivativeBandLabel A B) : band ∈ derivativeBandLabelFinset := by
  cases band with
  | low => simp [derivativeBandLabelFinset]
  | high => simp [derivativeBandLabelFinset]
  | resonant k hkA hkB =>
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_image.mpr
    refine ⟨⟨k, Finset.mem_Ico.mpr ⟨?_, hkB⟩⟩, Finset.mem_attach _ _, ?_⟩
    · omega
    · congr
  | good k hkA hkB =>
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨⟨k, Finset.mem_Ico.mpr ⟨hkA, hkB⟩⟩, Finset.mem_attach _ _, ?_⟩
    congr

theorem derivativeBandLabelFinset_filter_card_sum {A B : ℤ}
    (S : Finset ℤ) (label : ℤ → DerivativeBandLabel A B) :
    ∑ band ∈ derivativeBandLabelFinset,
      (S.filter fun n => label n = band).card = S.card := by
  classical
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter : S.filter (fun n => label n ∈ derivativeBandLabelFinset) = S := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hn
      exact ⟨hn, derivativeBandLabel_mem_finset (label n)⟩
  rw [hfilter]

theorem derivativeBandLabelFinset_biUnion_eq {A B : ℤ}
    (S : Finset ℤ) (label : ℤ → DerivativeBandLabel A B) :
    (derivativeBandLabelFinset).biUnion
      (fun band => S.filter fun n => label n = band) = S := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_biUnion.mp hn with ⟨band, hband, hnmem⟩
    exact (Finset.mem_filter.mp hnmem).1
  · intro hn
    refine Finset.mem_biUnion.mpr ⟨label n,
      derivativeBandLabel_mem_finset (label n), ?_⟩
    exact Finset.mem_filter.mpr ⟨hn, rfl⟩

theorem derivativeBandLabelFinset_sum_fiberwise {A B : ℤ}
    (S : Finset ℤ) (label : ℤ → DerivativeBandLabel A B)
    (z : ℤ → ℂ) :
    (∑ n ∈ S, z n) =
      ∑ band ∈ derivativeBandLabelFinset,
        ∑ n ∈ S.filter (fun n => label n = band), z n := by
  classical
  have hdis : (↑(derivativeBandLabelFinset (A := A) (B := B)) :
      Set (DerivativeBandLabel A B)).PairwiseDisjoint
      (fun band => S.filter fun n => label n = band) := by
    intro band hband other hother hne
    change Disjoint (S.filter fun n => label n = band)
      (S.filter fun n => label n = other)
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    have h₁ := (Finset.mem_filter.mp hn₁).2
    have h₂ := (Finset.mem_filter.mp hn₂).2
    exact hne (h₁.symm.trans h₂)
  calc
    (∑ n ∈ S, z n) =
        ∑ n ∈ (derivativeBandLabelFinset (A := A) (B := B)).biUnion
          (fun band => S.filter fun n => label n = band), z n := by
      rw [derivativeBandLabelFinset_biUnion_eq S label]
    _ = ∑ band ∈ derivativeBandLabelFinset,
        ∑ n ∈ S.filter (fun n => label n = band), z n :=
      Finset.sum_biUnion hdis

theorem real_derivativeBand_exists_label {A B : ℤ} {θ t : ℝ}
    (hAB : A < B) (hθ : 0 < θ) (htA : (A : ℝ) ≤ t) (htB : t ≤ (B : ℝ)) :
    ∃ band : DerivativeBandLabel A B, derivativeBandMem θ t band := by
  rcases real_derivativeBand_partition_cover hAB hθ htA htB with hlow | hhigh | hres | hgood
  · exact ⟨.low, hlow⟩
  · exact ⟨.high, hhigh⟩
  · rcases hres with ⟨k, hkA, hkB, hmem⟩
    exact ⟨.resonant k hkA hkB, hmem⟩
  · rcases hgood with ⟨k, hkA, hkB, hmem⟩
    exact ⟨.good k hkA hkB, hmem⟩

theorem derivativeLowBand_disjoint_highBand {A B : ℤ} {θ : ℝ}
    (hAB : A < B) (hθhalf : θ < 1 / 2) :
    Disjoint (Set.Icc (A : ℝ) ((A : ℝ) + θ))
      (Set.Ioc ((B : ℝ) - θ) (B : ℝ)) := by
  rw [Set.disjoint_left]
  intro t htlo hthi
  have hAB' : (A : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hAB
  rcases htlo with ⟨_, htlo⟩
  rcases hthi with ⟨hthi, _⟩
  linarith

theorem derivativeGoodBand_disjoint_resonantBand {k l : ℤ} {θ : ℝ}
    (hkl : k ≤ l) :
    Disjoint (Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))
      (Set.Ioc ((l : ℝ) - θ) ((l : ℝ) + θ)) := by
  rw [Set.disjoint_left]
  intro t hgood hres
  rcases hgood with ⟨hgood, _⟩
  rcases hres with ⟨_, hres⟩
  have hkl' : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
  by_cases hEq : k = l
  · subst l
    linarith
  · have hSucc : k + 1 ≤ l := by omega
    have hSucc' : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hSucc
    linarith

theorem derivativeGoodBand_disjoint_resonantBand_of_lt {k l : ℤ} {θ : ℝ}
    (hkl : k < l) :
    Disjoint (Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))
      (Set.Ioc ((l : ℝ) - θ) ((l : ℝ) + θ)) := by
  exact derivativeGoodBand_disjoint_resonantBand (le_of_lt hkl)

theorem derivativeGoodBand_disjoint_resonantBand_of_gt {k l : ℤ} {θ : ℝ}
    (hlk : l < k) :
    Disjoint (Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))
      (Set.Ioc ((l : ℝ) - θ) ((l : ℝ) + θ)) := by
  rw [Set.disjoint_left]
  intro t hgood hres
  rcases hgood with ⟨hgood, _⟩
  rcases hres with ⟨_, hres⟩
  have hlk' : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlk
  linarith

theorem derivativeGoodBand_disjoint_resonantBand_any {k l : ℤ} {θ : ℝ}
    : Disjoint (Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))
      (Set.Ioc ((l : ℝ) - θ) ((l : ℝ) + θ)) := by
  by_cases hkl : k ≤ l
  · exact derivativeGoodBand_disjoint_resonantBand hkl
  · have hlk : l < k := by omega
    exact derivativeGoodBand_disjoint_resonantBand_of_gt hlk

theorem derivativeLowBand_disjoint_goodBand {A k : ℤ} {θ : ℝ}
    (hAk : A ≤ k) :
    Disjoint (Set.Icc (A : ℝ) ((A : ℝ) + θ))
      (Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ)) := by
  rw [Set.disjoint_left]
  intro t htlo hgood
  rcases htlo with ⟨_, htlo⟩
  rcases hgood with ⟨hgood, _⟩
  have hAk' : (A : ℝ) ≤ (k : ℝ) := by exact_mod_cast hAk
  linarith

theorem derivativeLowBand_disjoint_resonantBand {A k : ℤ} {θ : ℝ}
    (hAk : A < k) (hθhalf : θ < 1 / 2) :
    Disjoint (Set.Icc (A : ℝ) ((A : ℝ) + θ))
      (Set.Ioc ((k : ℝ) - θ) ((k : ℝ) + θ)) := by
  rw [Set.disjoint_left]
  intro t htlo hres
  rcases htlo with ⟨_, htlo⟩
  rcases hres with ⟨hres, _⟩
  have hAk' : (A : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hAk
  linarith

theorem derivativeHighBand_disjoint_resonantBand {B k : ℤ} {θ : ℝ}
    (hkB : k < B) (hθhalf : θ < 1 / 2) :
    Disjoint (Set.Ioc ((B : ℝ) - θ) (B : ℝ))
      (Set.Ioc ((k : ℝ) - θ) ((k : ℝ) + θ)) := by
  rw [Set.disjoint_left]
  intro t hhi hres
  rcases hhi with ⟨hhi, _⟩
  rcases hres with ⟨_, hres⟩
  have hkB' : (k : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hkB
  linarith

theorem derivativeHighBand_disjoint_goodBand {B k : ℤ} {θ : ℝ}
    (hkB : k < B) :
    Disjoint (Set.Ioc ((B : ℝ) - θ) (B : ℝ))
      (Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ)) := by
  rw [Set.disjoint_left]
  intro t hhi hgood
  rcases hhi with ⟨hhi, _⟩
  rcases hgood with ⟨_, hgood⟩
  have hkB' : (k : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hkB
  linarith

theorem derivativeResonantBand_disjoint_of_lt {k l : ℤ} {θ : ℝ}
    (hkl : k < l) (hθhalf : θ < 1 / 2) :
    Disjoint (Set.Ioc ((k : ℝ) - θ) ((k : ℝ) + θ))
      (Set.Ioc ((l : ℝ) - θ) ((l : ℝ) + θ)) := by
  rw [Set.disjoint_left]
  intro t hres₁ hres₂
  rcases hres₁ with ⟨_, hres₁⟩
  rcases hres₂ with ⟨hres₂, _⟩
  have hkl' : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hkl
  linarith

theorem derivativeGoodBand_disjoint_of_lt {k l : ℤ} {θ : ℝ}
    (hkl : k < l) (hθ : 0 < θ) :
    Disjoint (Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))
      (Set.Ioc ((l : ℝ) + θ) ((l : ℝ) + 1 - θ)) := by
  rw [Set.disjoint_left]
  intro t hgood₁ hgood₂
  rcases hgood₁ with ⟨_, hgood₁⟩
  rcases hgood₂ with ⟨hgood₂, _⟩
  have hkl' : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hkl
  linarith

theorem real_derivativeBand_label_unique {A B : ℤ} {θ t : ℝ}
    (hAB : A < B) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (b₁ b₂ : DerivativeBandLabel A B)
    (hb₁ : derivativeBandMem θ t b₁) (hb₂ : derivativeBandMem θ t b₂)
    : b₁ = b₂ := by
  cases b₁ with
  | low =>
    cases b₂ with
    | low => rfl
    | high =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeLowBand_disjoint_highBand hAB hθhalf)) hb₁ hb₂)
    | resonant k hkA hkB =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeLowBand_disjoint_resonantBand hkA hθhalf)) hb₁ hb₂)
    | good k hkA hkB =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeLowBand_disjoint_goodBand hkA)) hb₁ hb₂)
  | high =>
    cases b₂ with
    | low =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeLowBand_disjoint_highBand hAB hθhalf).symm) hb₁ hb₂)
    | high => rfl
    | resonant k hkA hkB =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeHighBand_disjoint_resonantBand hkB hθhalf)) hb₁ hb₂)
    | good k hkA hkB =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeHighBand_disjoint_goodBand hkB)) hb₁ hb₂)
  | resonant k₁ hkA₁ hkB₁ =>
    cases b₂ with
    | low =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeLowBand_disjoint_resonantBand hkA₁ hθhalf).symm) hb₁ hb₂)
    | high =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeHighBand_disjoint_resonantBand hkB₁ hθhalf).symm) hb₁ hb₂)
    | resonant k₂ hkA₂ hkB₂ =>
      by_cases hEq : k₁ = k₂
      · subst k₂
        rfl
      · by_cases hlt : k₁ < k₂
        · exact False.elim ((Set.disjoint_left.mp
            (derivativeResonantBand_disjoint_of_lt hlt hθhalf)) hb₁ hb₂)
        · have hlt' : k₂ < k₁ := by omega
          exact False.elim ((Set.disjoint_left.mp
            (derivativeResonantBand_disjoint_of_lt hlt' hθhalf).symm) hb₁ hb₂)
    | good k₂ hkA₂ hkB₂ =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeGoodBand_disjoint_resonantBand_any (k := k₂) (l := k₁)).symm)
        hb₁ hb₂)
  | good k₁ hkA₁ hkB₁ =>
    cases b₂ with
    | low =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeLowBand_disjoint_goodBand hkA₁).symm) hb₁ hb₂)
    | high =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeHighBand_disjoint_goodBand hkB₁).symm) hb₁ hb₂)
    | resonant k₂ hkA₂ hkB₂ =>
      exact False.elim ((Set.disjoint_left.mp
        (derivativeGoodBand_disjoint_resonantBand_any (k := k₁) (l := k₂))
        hb₁ hb₂))
    | good k₂ hkA₂ hkB₂ =>
      by_cases hEq : k₁ = k₂
      · subst k₂
        rfl
      · by_cases hlt : k₁ < k₂
        · exact False.elim ((Set.disjoint_left.mp
            (derivativeGoodBand_disjoint_of_lt hlt hθ)) hb₁ hb₂)
        · have hlt' : k₂ < k₁ := by omega
          exact False.elim ((Set.disjoint_left.mp
            (derivativeGoodBand_disjoint_of_lt hlt' hθ).symm) hb₁ hb₂)

noncomputable def derivativeBandLabelOf {A B : ℤ} (θ : ℝ) (D : ℤ → ℝ)
    (hAB : A < B) (hθ : 0 < θ) (n : ℤ) : DerivativeBandLabel A B :=
  if hDn : (A : ℝ) ≤ D n ∧ D n ≤ (B : ℝ) then
    Classical.choose (real_derivativeBand_exists_label hAB hθ hDn.1 hDn.2)
  else .low

theorem derivativeBandLabelOf_mem {A B : ℤ} {θ : ℝ} {D : ℤ → ℝ}
    (hAB : A < B) (hθ : 0 < θ) (n : ℤ)
    (hDn : (A : ℝ) ≤ D n ∧ D n ≤ (B : ℝ)) :
    derivativeBandMem θ (D n) (derivativeBandLabelOf θ D hAB hθ n) := by
  simpa [derivativeBandLabelOf, hDn] using Classical.choose_spec
    (real_derivativeBand_exists_label hAB hθ hDn.1 hDn.2)

theorem derivativeBandLabelOf_eq_iff_mem {A B : ℤ} {θ : ℝ} {D : ℤ → ℝ}
    (hAB : A < B) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (n : ℤ) (hDn : (A : ℝ) ≤ D n ∧ D n ≤ (B : ℝ))
    (band : DerivativeBandLabel A B) :
    derivativeBandLabelOf θ D hAB hθ n = band ↔
      derivativeBandMem θ (D n) band := by
  constructor
  · intro hEq
    subst band
    exact derivativeBandLabelOf_mem hAB hθ n hDn
  · intro hmem
    exact real_derivativeBand_label_unique hAB hθ hθhalf
      (derivativeBandLabelOf θ D hAB hθ n) band
      (derivativeBandLabelOf_mem hAB hθ n hDn) hmem

noncomputable def derivativeBandSamplesForLabel {A B : ℤ}
    (θ : ℝ) (D : ℤ → ℝ) (S : Finset ℤ)
    (band : DerivativeBandLabel A B) : Finset ℤ := by
  classical
  exact S.filter (fun n => derivativeBandMem θ (D n) band)

theorem derivativeBandLabelOf_filter_eq {A B : ℤ} {θ : ℝ} {D : ℤ → ℝ}
    (hAB : A < B) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (S : Finset ℤ) (hS : ∀ n ∈ S, (A : ℝ) ≤ D n ∧ D n ≤ (B : ℝ))
    (band : DerivativeBandLabel A B) :
    S.filter (fun n => derivativeBandLabelOf θ D hAB hθ n = band) =
      derivativeBandSamplesForLabel θ D S band := by
  classical
  ext n
  simp only [Finset.mem_filter, derivativeBandSamplesForLabel]
  constructor
  · rintro ⟨hn, hEq⟩
    exact ⟨hn, (derivativeBandLabelOf_eq_iff_mem hAB hθ hθhalf n
      (hS n hn) band).mp hEq⟩
  · rintro ⟨hn, hmem⟩
    exact ⟨hn, (derivativeBandLabelOf_eq_iff_mem hAB hθ hθhalf n
      (hS n hn) band).mpr hmem⟩

theorem derivativeBand_filter_card_sum {A B : ℤ} {θ : ℝ} {D : ℤ → ℝ}
    (hAB : A < B) (hθ : 0 < θ) (S : Finset ℤ) :
    ∑ b ∈ S.image (derivativeBandLabelOf θ D hAB hθ),
      (S.filter fun n => derivativeBandLabelOf θ D hAB hθ n = b).card = S.card := by
  classical
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      S.filter (fun n => derivativeBandLabelOf θ D hAB hθ n ∈
        S.image (derivativeBandLabelOf θ D hAB hθ)) = S := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hn
      exact ⟨hn, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
  rw [hfilter]

theorem derivativeGoodBand_mem_between_of_monotone {D : ℤ → ℝ}
    {k : ℤ} {θ : ℝ} {m j n : ℤ} (hmono : Monotone D)
    (hmj : m ≤ j) (hjn : j ≤ n)
    (hm : D m ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))
    (hn : D n ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ)) :
    D j ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ) := by
  rw [Set.mem_Ioc] at hm hn ⊢
  constructor
  · exact lt_of_lt_of_le hm.1 (hmono hmj)
  · exact le_trans (hmono hjn) hn.2

theorem finset_eq_Icc_min'_max'_of_orderConvex
    (s : Finset ℤ) (hs : s.Nonempty)
    (hconv : ∀ m ∈ s, ∀ n ∈ s, m ≤ n → ∀ j, m ≤ j → j ≤ n → j ∈ s) :
    s = Finset.Icc (s.min' hs) (s.max' hs) := by
  ext j
  constructor
  · intro hj
    rw [Finset.mem_Icc]
    exact ⟨Finset.min'_le s j hj, Finset.le_max' s j hj⟩
  · intro hj
    rw [Finset.mem_Icc] at hj
    exact hconv (s.min' hs) (Finset.min'_mem s hs)
      (s.max' hs) (Finset.max'_mem s hs)
      (Finset.min'_le_max' s hs) j hj.1 hj.2

theorem sum_int_Icc_eq_sum_range_translate {α : Type*} [AddCommMonoid α]
    (f : ℤ → α) (l u : ℤ) (hlu : l ≤ u) :
    (∑ n ∈ Finset.Icc l u, f n) =
      ∑ i ∈ Finset.range ((u - l).toNat + 1), f (l + (i : ℤ)) := by
  let m : ℕ := (u - l).toNat
  have hmcast : (m : ℤ) = u - l := by
    dsimp [m]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hlu)
  have hlast : l + (m : ℤ) = u := by omega
  calc
    (∑ n ∈ Finset.Icc l u, f n) =
        (∑ n ∈ Finset.Ico l u, f n) + f u :=
      Finset.sum_Icc_eq_sum_Ico_add f hlu
    _ = (∑ i ∈ Finset.range m, f (l + (i : ℤ))) + f u := by
      congr 1
      rw [Int.Ico_eq_finset_map, Finset.sum_map]
      rfl
    _ = ∑ i ∈ Finset.range (m + 1), f (l + (i : ℤ)) := by
      rw [Finset.sum_range_succ]
      rw [hlast]

theorem realIntegerInterval_goodBand_filter_eq_Icc
    {x Y θ : ℝ} {k : ℤ} (D : ℝ → ℝ)
    (hDmono : ∀ u v, x < u → v ≤ x + Y → u ≤ v → D u ≤ D v)
    (hs : ((realIntegerInterval x Y).filter
      (fun n : ℤ => D (n : ℝ) ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))).Nonempty) :
    (realIntegerInterval x Y).filter
      (fun n : ℤ => D (n : ℝ) ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ)) =
      Finset.Icc
        (((realIntegerInterval x Y).filter
          (fun n : ℤ => D (n : ℝ) ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))).min' hs)
        (((realIntegerInterval x Y).filter
          (fun n : ℤ => D (n : ℝ) ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))).max' hs) := by
  let s := (realIntegerInterval x Y).filter
    (fun n : ℤ => D (n : ℝ) ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))
  apply finset_eq_Icc_min'_max'_of_orderConvex s hs
  intro m hm n hn hmn j hmj hjn
  have hmS : m ∈ realIntegerInterval x Y := (Finset.mem_filter.mp hm).1
  have hnS : n ∈ realIntegerInterval x Y := (Finset.mem_filter.mp hn).1
  have hmB : D (m : ℝ) ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ) :=
    (Finset.mem_filter.mp hm).2
  have hnB : D (n : ℝ) ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ) :=
    (Finset.mem_filter.mp hn).2
  have hmI := (mem_realIntegerInterval_iff x Y m).mp hmS
  have hnI := (mem_realIntegerInterval_iff x Y n).mp hnS
  have hjS : j ∈ realIntegerInterval x Y := by
    apply (mem_realIntegerInterval_iff x Y j).mpr
    constructor
    · have hmjR : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast hmj
      exact lt_of_lt_of_le hmI.1 hmjR
    · have hjnR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
      exact le_trans hjnR hnI.2
  have hjI := (mem_realIntegerInterval_iff x Y j).mp hjS
  have hmjR : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast hmj
  have hjnR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
  have hmjD := hDmono (m : ℝ) (j : ℝ) hmI.1 hjI.2 hmjR
  have hjnD := hDmono (j : ℝ) (n : ℝ) hjI.1 hnI.2 hjnR
  rw [Set.mem_Ioc] at hmB hnB
  have hjB : (k : ℝ) + θ < D (j : ℝ) ∧
      D (j : ℝ) ≤ (k : ℝ) + 1 - θ :=
    ⟨lt_of_lt_of_le hmB.1 hmjD, le_trans hjnD hnB.2⟩
  change j ∈ (realIntegerInterval x Y).filter
    (fun n : ℤ => D (n : ℝ) ∈ Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ))
  exact Finset.mem_filter.mpr ⟨hjS, hjB⟩

theorem kusmin_sequence_bound_all {θ : ℝ} (hθ : 0 < θ)
    (hθhalf : θ ≤ 1 / 2) (m : ℕ)
    (z : ℕ → ℂ) (δ : ℕ → ℝ)
    (hz : ∀ i, i ≤ m → ‖z i‖ = 1)
    (hstep : ∀ i, i < m → z (i + 1) = z i * kusminRotation (δ i))
    (hlo : ∀ i, i < m → θ ≤ δ i)
    (hhi : ∀ i, i < m → δ i ≤ 1 - θ)
    (hmono : (∀ i, i < m - 1 → δ i ≤ δ (i + 1)) ∨
      (∀ i, i < m - 1 → δ (i + 1) ≤ δ i)) :
    ‖∑ i ∈ Finset.range (m + 1), z i‖ ≤ Real.cot (Real.pi * θ / 2) := by
  by_cases hm : m = 0
  · subst m
    simp only [Nat.zero_add, Finset.sum_range_succ, Finset.sum_range_zero]
    simpa [hz 0 (by omega)] using real_cot_pi_theta_div_two_ge_one hθ hθhalf
  · exact kusmin_sequence_bound hθ hθhalf (by omega) z δ hz hstep hlo hhi hmono

theorem kusmin_discrete_first_derivative {θ : ℝ} (hθ : 0 < θ)
    (hθhalf : θ ≤ 1 / 2) (m : ℕ) (k : ℤ) (f : ℕ → ℝ)
    (hband : ∀ i, i < m →
      (k : ℝ) + θ ≤ f (i + 1) - f i ∧
        f (i + 1) - f i ≤ (k : ℝ) + 1 - θ)
    (hmono : (∀ i, i < m - 1 →
        f (i + 1) - f i ≤ f (i + 2) - f (i + 1)) ∨
      (∀ i, i < m - 1 →
        f (i + 2) - f (i + 1) ≤ f (i + 1) - f i)) :
    ‖∑ i ∈ Finset.range (m + 1), kusminPhase (f i)‖ ≤
      Real.cot (Real.pi * θ / 2) := by
  let δ : ℕ → ℝ := fun i => f (i + 1) - f i - (k : ℝ)
  have hlo : ∀ i, i < m → θ ≤ δ i := by
    intro i hi
    dsimp [δ]
    linarith [(hband i hi).1]
  have hhi : ∀ i, i < m → δ i ≤ 1 - θ := by
    intro i hi
    dsimp [δ]
    linarith [(hband i hi).2]
  have hmono' : (∀ i, i < m - 1 → δ i ≤ δ (i + 1)) ∨
      (∀ i, i < m - 1 → δ (i + 1) ≤ δ i) := by
    rcases hmono with hinc | hdec
    · left
      intro i hi
      dsimp [δ]
      linarith [hinc i hi]
    · right
      intro i hi
      dsimp [δ]
      linarith [hdec i hi]
  have hunit : ∀ i, i ≤ m → ‖kusminPhase (f i)‖ = 1 := by
    intro i hi
    rw [kusminPhase, Complex.norm_exp]
    simp
  have hstep : ∀ i, i < m →
      kusminPhase (f (i + 1)) = kusminPhase (f i) * kusminRotation (δ i) := by
    intro i hi
    have hdecomp : f (i + 1) = f i + ((k : ℝ) + δ i) := by
      dsimp [δ]
      ring
    calc
      kusminPhase (f (i + 1)) = kusminPhase (f i + ((k : ℝ) + δ i)) := by rw [hdecomp]
      _ = kusminPhase (f i) * kusminPhase ((k : ℝ) + δ i) := kusminPhase_add _ _
      _ = kusminPhase (f i) * kusminPhase (δ i) := by rw [kusminPhase_add_int]
      _ = kusminPhase (f i) * kusminRotation (δ i) := by rfl
  exact kusmin_sequence_bound_all hθ hθhalf m
    (kusminPhase ∘ f) δ hunit hstep hlo hhi hmono'

theorem intervalIntegral_mono_shift_one {D : ℝ → ℝ}
    (hDcont : Continuous D) (hDmono : Monotone D) (a : ℝ) :
    (∫ t in a..a + 1, D t) ≤ ∫ t in a + 1..a + 2, D t := by
  rw [show a + 2 = (a + 1) + 1 by ring,
    ← intervalIntegral.integral_comp_add_right (f := D) 1]
  apply intervalIntegral.integral_mono_on
  · linarith
  · exact hDcont.intervalIntegrable _ _
  · exact (hDcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  · intro t ht
    exact hDmono (by linarith [ht.1])

theorem intervalIntegral_mono_shift_one_local {D : ℝ → ℝ} {a : ℝ}
    (hDcont : ContinuousOn D (Set.Icc a (a + 2)))
    (hDmono : MonotoneOn D (Set.Icc a (a + 2))) :
    (∫ t in a..a + 1, D t) ≤ ∫ t in a + 1..a + 2, D t := by
  have hleft : Set.Icc a (a + 1) ⊆ Set.Icc a (a + 2) := by
    apply Set.Icc_subset_Icc_right
    linarith
  have hright : Set.Icc (a + 1) (a + 2) ⊆ Set.Icc a (a + 2) := by
    apply Set.Icc_subset_Icc_left
    linarith
  have hDleft : ContinuousOn D (Set.Icc a (a + 1)) := hDcont.mono hleft
  have hDright : ContinuousOn D (Set.Icc (a + 1) (a + 2)) := hDcont.mono hright
  have hshiftCont : ContinuousOn (fun t : ℝ => D (t + 1)) (Set.Icc a (a + 1)) := by
    refine hDright.comp (continuousOn_id.add continuousOn_const) ?_
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  rw [show a + 2 = (a + 1) + 1 by ring,
    ← intervalIntegral.integral_comp_add_right (f := D) 1]
  apply intervalIntegral.integral_mono_on
  · linarith
  · exact hDleft.intervalIntegrable_of_Icc (by linarith)
  · exact hshiftCont.intervalIntegrable_of_Icc (by linarith)
  · intro t ht
    exact hDmono (hleft ht) (by
      constructor
      · linarith [ht.1]
      · linarith [ht.2]) (by linarith)

theorem intervalIntegral_between_const_of_continuous {D : ℝ → ℝ}
    (hDcont : Continuous D) (a lower upper : ℝ)
    (hbound : ∀ t ∈ Set.Icc a (a + 1), lower ≤ D t ∧ D t ≤ upper) :
    lower ≤ (∫ t in a..a + 1, D t) ∧
      (∫ t in a..a + 1, D t) ≤ upper := by
  have hDint : IntervalIntegrable D MeasureTheory.volume a (a + 1) :=
    hDcont.intervalIntegrable a (a + 1)
  have hconstInt (c : ℝ) :
    IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a (a + 1) :=
    continuous_const.intervalIntegrable _ _
  have hlow := intervalIntegral.integral_mono_on (a := a) (b := a + 1)
    (by linarith) (hconstInt lower) hDint
    (fun t ht => (hbound t ht).1)
  have hhigh := intervalIntegral.integral_mono_on (a := a) (b := a + 1)
    (by linarith) hDint (hconstInt upper)
    (fun t ht => (hbound t ht).2)
  have hlowerIntegral : (∫ t in a..a + 1, (fun _ : ℝ => lower) t) = lower := by
    simp
  have hupperIntegral : (∫ t in a..a + 1, (fun _ : ℝ => upper) t) = upper := by
    simp
  rw [hlowerIntegral] at hlow
  rw [hupperIntegral] at hhigh
  exact ⟨hlow, hhigh⟩

theorem intervalIntegral_eq_sub_of_local_derivative {f D : ℝ → ℝ}
    {a b : ℝ}
    (hDcont : ContinuousOn D (Set.uIcc a b))
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt f (D t) t) :
    (∫ t in a..b, D t) = f b - f a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hDcont.intervalIntegrable

theorem intervalIntegral_eq_sub_of_local_derivative_on_Icc {f D : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hDcont : ContinuousOn D (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt f (D t) t) :
    (∫ t in a..b, D t) = f b - f a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hfcont hderiv
  exact hDcont.intervalIntegrable_of_Icc hab

theorem intervalIntegral_between_const_local {D : ℝ → ℝ} {a : ℝ}
    (lower upper : ℝ)
    (hDcont : ContinuousOn D (Set.Icc a (a + 1)))
    (hbound : ∀ t ∈ Set.Icc a (a + 1), lower ≤ D t ∧ D t ≤ upper)
    :
    lower ≤ (∫ t in a..a + 1, D t) ∧
      (∫ t in a..a + 1, D t) ≤ upper := by
  have hDint : IntervalIntegrable D MeasureTheory.volume a (a + 1) :=
    hDcont.intervalIntegrable_of_Icc (by linarith)
  have hconstInt (c : ℝ) :
      IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a (a + 1) :=
    continuous_const.intervalIntegrable _ _
  have hlow := intervalIntegral.integral_mono_on (a := a) (b := a + 1)
    (by linarith) (hconstInt lower) hDint
    (fun t ht => (hbound t ht).1)
  have hhigh := intervalIntegral.integral_mono_on (a := a) (b := a + 1)
    (by linarith) hDint (hconstInt upper)
    (fun t ht => (hbound t ht).2)
  have hlowerIntegral : (∫ t in a..a + 1, (fun _ : ℝ => lower) t) = lower := by simp
  have hupperIntegral : (∫ t in a..a + 1, (fun _ : ℝ => upper) t) = upper := by simp
  rw [hlowerIntegral] at hlow
  rw [hupperIntegral] at hhigh
  exact ⟨hlow, hhigh⟩

theorem kusmin_first_derivative_local_block {θ : ℝ} (hθ : 0 < θ)
    (hθhalf : θ ≤ 1 / 2) (a : ℝ) (m : ℕ) (k : ℤ)
    (f D : ℝ → ℝ)
    (hfcont : ContinuousOn f (Set.Icc a (a + (m : ℝ))))
    (hDcont : ContinuousOn D (Set.Icc a (a + (m : ℝ))))
    (hDmono : MonotoneOn D (Set.Icc a (a + (m : ℝ))))
    (hderiv : ∀ t ∈ Set.Ioo a (a + (m : ℝ)), HasDerivAt f (D t) t)
    (hband : ∀ t ∈ Set.Icc a (a + (m : ℝ)),
      (k : ℝ) + θ ≤ D t ∧ D t ≤ (k : ℝ) + 1 - θ) :
    ‖∑ i ∈ Finset.range (m + 1), kusminPhase (f (a + (i : ℝ)))‖ ≤
      Real.cot (Real.pi * θ / 2) := by
  let p : ℕ → ℝ := fun i => a + (i : ℝ)
  have hpsucc (i : ℕ) : p (i + 1) = p i + 1 := by
    simp [p]
    ring
  have hpsucc2 (i : ℕ) : p (i + 2) = p (i + 1) + 1 := by
    rw [hpsucc, hpsucc]
  have hpoint (i : ℕ) (hi : i ≤ m) : p i ∈ Set.Icc a (a + (m : ℝ)) := by
    constructor
    · dsimp [p]
      linarith [show (0 : ℝ) ≤ (i : ℝ) by positivity]
    · dsimp [p]
      have hi' : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
      nlinarith [hi']
  have hinc_eq (i : ℕ) (hi : i < m) :
      f (p (i + 1)) - f (p i) = ∫ t in p i..p (i + 1), D t := by
    have hsub : Set.Icc (p i) (p (i + 1)) ⊆ Set.Icc a (a + (m : ℝ)) := by
      intro t ht
      constructor
      · exact le_trans (hpoint i (by omega)).1 ht.1
      · exact ht.2.trans (hpoint (i + 1) (by omega)).2
    have hlocalFcont : ContinuousOn f (Set.Icc (p i) (p (i + 1))) := hfcont.mono hsub
    have hlocalDcont : ContinuousOn D (Set.Icc (p i) (p (i + 1))) := hDcont.mono hsub
    have hlocalDeriv : ∀ t ∈ Set.Ioo (p i) (p (i + 1)), HasDerivAt f (D t) t := by
      intro t ht
      apply hderiv t
      exact ⟨lt_of_le_of_lt (hpoint i (by omega)).1 ht.1,
        lt_of_lt_of_le ht.2 (hpoint (i + 1) (by omega)).2⟩
    have hpile : p i ≤ p (i + 1) := by rw [hpsucc i]; linarith
    exact (intervalIntegral_eq_sub_of_local_derivative_on_Icc hpile
      hlocalFcont hlocalDcont hlocalDeriv).symm
  have hincrementBand (i : ℕ) (hi : i < m) :
      (k : ℝ) + θ ≤ f (p (i + 1)) - f (p i) ∧
        f (p (i + 1)) - f (p i) ≤ (k : ℝ) + 1 - θ := by
    rw [hinc_eq i hi]
    rw [hpsucc i]
    have hsub : Set.Icc (p i) (p i + 1) ⊆ Set.Icc a (a + (m : ℝ)) := by
      intro t ht
      constructor
      · exact le_trans (hpoint i (by omega)).1 ht.1
      · have hpnext := (hpoint (i + 1) (by omega)).2
        rw [hpsucc i] at hpnext
        exact ht.2.trans hpnext
    have hlocalCont : ContinuousOn D (Set.Icc (p i) (p i + 1)) := hDcont.mono hsub
    have hlocalBand : ∀ t ∈ Set.Icc (p i) (p i + 1),
        (k : ℝ) + θ ≤ D t ∧ D t ≤ (k : ℝ) + 1 - θ := by
      intro t ht
      exact hband t (hsub ht)
    exact intervalIntegral_between_const_local ((k : ℝ) + θ)
      ((k : ℝ) + 1 - θ) hlocalCont hlocalBand
  have hincrementMono : (∀ i, i < m - 1 →
        f (p (i + 1)) - f (p i) ≤ f (p (i + 2)) - f (p (i + 1))) ∨
      (∀ i, i < m - 1 →
        f (p (i + 2)) - f (p (i + 1)) ≤ f (p (i + 1)) - f (p i)) := by
    left
    intro i hi
    rw [hinc_eq i (by omega), hinc_eq (i + 1) (by omega), hpsucc i, hpsucc (i + 1)]
    have hsub : Set.Icc (p i) (p i + 2) ⊆ Set.Icc a (a + (m : ℝ)) := by
      intro t ht
      constructor
      · exact le_trans (hpoint i (by omega)).1 ht.1
      · have hpEnd := (hpoint (i + 2) (by omega)).2
        have hpEnd' : p i + 2 ≤ a + (m : ℝ) := by
          calc
            p i + 2 = p (i + 1) + 1 := by rw [hpsucc]; ring
            _ = p (i + 2) := hpsucc2 i |>.symm
            _ ≤ a + (m : ℝ) := hpEnd
        exact ht.2.trans hpEnd'
    have hlocalCont := hDcont.mono hsub
    have hlocalMono : MonotoneOn D (Set.Icc (p i) (p i + 2)) := by
      intro x hx y hy hxy
      exact hDmono (hsub hx) (hsub hy) hxy
    have hshift := intervalIntegral_mono_shift_one_local hlocalCont hlocalMono
    have hpEnd : p (i + 2) = p i + 2 := by
      calc
        p (i + 2) = p (i + 1) + 1 := hpsucc2 i
        _ = p i + 2 := by rw [hpsucc]; ring
    rw [show p i + 2 = p i + 1 + 1 by ring] at hshift
    rw [hpsucc i]
    exact hshift
  have hseqBand : ∀ i, i < m →
      (k : ℝ) + θ ≤ f (p (i + 1)) - f (p i) ∧
        f (p (i + 1)) - f (p i) ≤ (k : ℝ) + 1 - θ := hincrementBand
  have hseqMono : (∀ i, i < m - 1 →
        f (p (i + 1)) - f (p i) ≤ f (p (i + 2)) - f (p (i + 1))) ∨
      (∀ i, i < m - 1 →
        f (p (i + 2)) - f (p (i + 1)) ≤ f (p (i + 1)) - f (p i)) :=
    hincrementMono
  simpa [p] using kusmin_discrete_first_derivative hθ hθhalf m k
    (fun i => f (p i)) hseqBand hseqMono

theorem finset_card_le_one_add_width_div_of_separation
    (s : Finset ℕ) (d : ℕ → ℝ) (lower upper lam : ℝ)
    (hs : s.Nonempty) (hlam : 0 < lam) (hwidth : lower ≤ upper)
    (hband : ∀ n ∈ s, lower ≤ d n ∧ d n ≤ upper)
    (hsep : ∀ m ∈ s, ∀ n ∈ s, m < n →
      lam * ((n - m : ℕ) : ℝ) ≤ d n - d m) :
    (s.card : ℝ) ≤ 1 + (upper - lower) / lam := by
  let n₀ := s.min' hs
  let q : ℕ := ⌊(upper - lower) / lam⌋₊
  have hn₀ : n₀ ∈ s := Finset.min'_mem s hs
  have hratio_nonneg : 0 ≤ (upper - lower) / lam :=
    div_nonneg (sub_nonneg.mpr hwidth) (le_of_lt hlam)
  have hsubset : s ⊆ Finset.Icc n₀ (n₀ + q) := by
    intro n hn
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.min'_le s n hn
    · by_cases hEq : n = n₀
      · subst n
        omega
      · have hlt : n₀ < n := by
          have hle := Finset.min'_le s n hn
          omega
        have hdist := hsep n₀ hn₀ n hn hlt
        have hwidth' : d n - d n₀ ≤ upper - lower := by
          have hnBand := hband n hn
          have hminBand := hband n₀ hn₀
          linarith
        have hdist' : ((n - n₀ : ℕ) : ℝ) ≤ (upper - lower) / lam := by
          apply (le_div_iff₀ hlam).2
          nlinarith
        have hq : n - n₀ ≤ q := Nat.le_floor hdist'
        omega
  have hcardNat : s.card ≤ (Finset.Icc n₀ (n₀ + q)).card :=
    Finset.card_le_card hsubset
  have hcardReal : (s.card : ℝ) ≤ ((Finset.Icc n₀ (n₀ + q)).card : ℝ) := by
    exact_mod_cast hcardNat
  have hqbound : (q : ℝ) ≤ (upper - lower) / lam := Nat.floor_le hratio_nonneg
  rw [Nat.card_Icc] at hcardReal
  have hNat : n₀ + q + 1 - n₀ = q + 1 := by omega
  rw [hNat] at hcardReal
  rw [Nat.cast_add, Nat.cast_one] at hcardReal
  nlinarith [hcardReal, hqbound]

theorem finset_int_card_le_one_add_width_div_of_separation
    (s : Finset ℤ) (d : ℤ → ℝ) (lower upper lam : ℝ)
    (hs : s.Nonempty) (hlam : 0 < lam) (hwidth : lower ≤ upper)
    (hband : ∀ n ∈ s, lower ≤ d n ∧ d n ≤ upper)
    (hsep : ∀ m ∈ s, ∀ n ∈ s, m < n →
      lam * ((n - m : ℤ) : ℝ) ≤ d n - d m) :
    (s.card : ℝ) ≤ 1 + (upper - lower) / lam := by
  let n₀ := s.min' hs
  let q : ℕ := ⌊(upper - lower) / lam⌋₊
  have hn₀ : n₀ ∈ s := Finset.min'_mem s hs
  have hratio_nonneg : 0 ≤ (upper - lower) / lam :=
    div_nonneg (sub_nonneg.mpr hwidth) (le_of_lt hlam)
  have hsubset : s ⊆ Finset.Icc n₀ (n₀ + (q : ℤ)) := by
    intro n hn
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.min'_le s n hn
    · by_cases hEq : n = n₀
      · subst n
        simp
      · have hlt : n₀ < n := by
          have hle := Finset.min'_le s n hn
          omega
        have hdist := hsep n₀ hn₀ n hn hlt
        have hwidth' : d n - d n₀ ≤ upper - lower := by
          have hnBand := hband n hn
          have hminBand := hband n₀ hn₀
          linarith
        have hdist' : ((n - n₀ : ℤ) : ℝ) ≤ (upper - lower) / lam := by
          apply (le_div_iff₀ hlam).2
          nlinarith
        have hnatCast : (((n - n₀).toNat : ℕ) : ℝ) =
            ((n - n₀ : ℤ) : ℝ) := by
          have hnonneg : 0 ≤ n - n₀ := sub_nonneg.mpr (le_of_lt hlt)
          have hcast : (((n - n₀).toNat : ℕ) : ℤ) = n - n₀ :=
            Int.toNat_of_nonneg hnonneg
          exact_mod_cast hcast
        have hdistNat : (((n - n₀).toNat : ℕ) : ℝ) ≤
            (upper - lower) / lam := by rw [hnatCast]; exact hdist'
        have hq : (n - n₀).toNat ≤ q := Nat.le_floor hdistNat
        have hqInt : ((n - n₀).toNat : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
        have hdiff : n - n₀ ≤ (q : ℤ) := by rw [Int.toNat_of_nonneg
          (sub_nonneg.mpr (le_of_lt hlt))] at hqInt; exact hqInt
        omega
  have hcardNat : s.card ≤ (Finset.Icc n₀ (n₀ + (q : ℤ))).card :=
    Finset.card_le_card hsubset
  have hcardReal : (s.card : ℝ) ≤
      ((Finset.Icc n₀ (n₀ + (q : ℤ))).card : ℝ) := by exact_mod_cast hcardNat
  have hcardInterval : (Finset.Icc n₀ (n₀ + (q : ℤ))).card = q + 1 := by
    rw [Int.card_Icc]
    have harg : n₀ + (q : ℤ) + 1 - n₀ = (q : ℤ) + 1 := by ring
    rw [harg]
    simp
  rw [hcardInterval] at hcardReal
  have hqbound : (q : ℝ) ≤ (upper - lower) / lam := Nat.floor_le hratio_nonneg
  push_cast at hcardReal
  nlinarith [hcardReal, hqbound]

theorem secondDerivative_separation_local {D E : ℝ → ℝ} {a b lam : ℝ}
    (hab : a < b) (hDcont : ContinuousOn D (Set.Icc a b))
    (hDderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt D (E x) x)
    (hElower : ∀ x ∈ Set.Ioo a b, lam ≤ E x) :
    lam * (b - a) ≤ D b - D a := by
  have hDdiff : DifferentiableOn ℝ D (Set.Ioo a b) := by
    intro x hx
    exact ((hDderiv x hx).differentiableAt).differentiableWithinAt
  obtain ⟨c, hc, hcEq⟩ := exists_hasDerivAt_eq_slope D E hab hDcont hDderiv
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hquot : lam ≤ (D b - D a) / (b - a) := by
    rw [← hcEq]
    exact hElower c hc
  exact (le_div_iff₀ hlen).mp hquot

theorem HalfOpenC2Data.firstDerivative_sample_separation
    {x Y lam : ℝ} (data : HalfOpenC2Data x Y)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    {m n : ℤ} (hm : m ∈ realIntegerInterval x Y)
    (hn : n ∈ realIntegerInterval x Y) (hmn : m < n) :
    lam * ((n - m : ℤ) : ℝ) ≤
      data.firstDerivative (n : ℝ) - data.firstDerivative (m : ℝ) := by
  have hmI := (mem_realIntegerInterval_iff x Y m).mp hm
  have hnI := (mem_realIntegerInterval_iff x Y n).mp hn
  let a : ℝ := (m : ℝ)
  let b : ℝ := (n : ℝ)
  have hab : a < b := by
    dsimp [a, b]
    exact_mod_cast hmn
  have hcompact := data.restrict_compact hmI.1 hnI.2
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt data.firstDerivative (data.secondDerivative t) t := by
    intro t ht
    apply hcompact.2.2.2.2 t
    constructor
    · simpa [a] using ht.1
    · simpa [b] using ht.2
  have hlower : ∀ t ∈ Set.Ioo a b, lam ≤ data.secondDerivative t := by
    intro t ht
    apply hsecond t
    constructor
    · have := hmI.1
      dsimp [a] at ht
      exact lt_trans this ht.1
    · have := hnI.2
      dsimp [b] at ht
      exact le_of_lt (lt_of_lt_of_le ht.2 this)
  have hgap := secondDerivative_separation_local hab hcompact.2.1 hderiv hlower
  have hcast : ((n - m : ℤ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast
    ring
  simpa [a, b, hcast] using hgap

theorem HalfOpenC2Data.sample_band_card_bound
    {x Y lam lower upper : ℝ} (data : HalfOpenC2Data x Y)
    (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (S : Finset ℤ) (hS : S ⊆ realIntegerInterval x Y)
    (hs : S.Nonempty)
    (hband : ∀ n ∈ S,
      lower ≤ data.firstDerivative (n : ℝ) ∧
        data.firstDerivative (n : ℝ) ≤ upper) :
    (S.card : ℝ) ≤ 1 + (upper - lower) / lam := by
  have hwidth : lower ≤ upper := by
    obtain ⟨n, hn⟩ := hs
    exact (hband n hn).1.trans (hband n hn).2
  have hsep : ∀ m ∈ S, ∀ n ∈ S, m < n →
      lam * ((n - m : ℤ) : ℝ) ≤
        data.firstDerivative (n : ℝ) - data.firstDerivative (m : ℝ) := by
    intro m hm n hn hmn
    exact data.firstDerivative_sample_separation hsecond
      (hS hm) (hS hn) hmn
  exact finset_int_card_le_one_add_width_div_of_separation S
    (fun n => data.firstDerivative (n : ℝ)) lower upper lam hs hlam
    hwidth hband hsep

theorem HalfOpenC2Data.lowDerivativeBandSamples_norm_bound
    {x Y θ : ℝ} {A : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hθ : 0 < θ) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t) :
    ‖∑ n ∈ (realIntegerInterval x Y).filter
        (fun n : ℤ => data.firstDerivative (n : ℝ) ∈
          Set.Icc (A : ℝ) ((A : ℝ) + θ)),
        kusminPhase (data.f (n : ℝ))‖ ≤ 1 + θ / lam := by
  classical
  let T := (realIntegerInterval x Y).filter
    (fun n : ℤ => data.firstDerivative (n : ℝ) ∈
      Set.Icc (A : ℝ) ((A : ℝ) + θ))
  change ‖∑ n ∈ T, kusminPhase (data.f (n : ℝ))‖ ≤ 1 + θ / lam
  by_cases hne : T.Nonempty
  · have hbandT : ∀ n ∈ T,
        (A : ℝ) ≤ data.firstDerivative (n : ℝ) ∧
          data.firstDerivative (n : ℝ) ≤ (A : ℝ) + θ := by
      intro n hn
      exact Set.mem_Icc.mp (Finset.mem_filter.mp hn).2
    have hcount := data.sample_band_card_bound hlam hsecond T
      (Finset.filter_subset _ _) hne hbandT
    have hcount' : (T.card : ℝ) ≤ 1 + θ / lam := by
      simpa [show ((A : ℝ) + θ) - (A : ℝ) = θ by ring] using hcount
    exact (kusminPhase_sum_norm_le_card T data.f).trans hcount'
  · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hT]
    simp
    positivity

theorem HalfOpenC2Data.highDerivativeBandSamples_norm_bound
    {x Y θ : ℝ} {B : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hθ : 0 < θ) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t) :
    ‖∑ n ∈ (realIntegerInterval x Y).filter
        (fun n : ℤ => data.firstDerivative (n : ℝ) ∈
          Set.Ioc ((B : ℝ) - θ) (B : ℝ)),
        kusminPhase (data.f (n : ℝ))‖ ≤ 1 + θ / lam := by
  classical
  let T := (realIntegerInterval x Y).filter
    (fun n : ℤ => data.firstDerivative (n : ℝ) ∈
      Set.Ioc ((B : ℝ) - θ) (B : ℝ))
  change ‖∑ n ∈ T, kusminPhase (data.f (n : ℝ))‖ ≤ 1 + θ / lam
  by_cases hne : T.Nonempty
  · have hbandT : ∀ n ∈ T,
        (B : ℝ) - θ ≤ data.firstDerivative (n : ℝ) ∧
          data.firstDerivative (n : ℝ) ≤ (B : ℝ) := by
      intro n hn
      exact ⟨(Set.mem_Ioc.mp (Finset.mem_filter.mp hn).2).1.le,
        (Set.mem_Ioc.mp (Finset.mem_filter.mp hn).2).2⟩
    have hcount := data.sample_band_card_bound hlam hsecond T
      (Finset.filter_subset _ _) hne hbandT
    have hcount' : (T.card : ℝ) ≤ 1 + θ / lam := by
      simpa [show (B : ℝ) - ((B : ℝ) - θ) = θ by ring] using hcount
    exact (kusminPhase_sum_norm_le_card T data.f).trans hcount'
  · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hT]
    simp
    positivity

theorem HalfOpenC2Data.resonantDerivativeBandSamples_norm_bound
    {x Y θ : ℝ} {k : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hθ : 0 < θ) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t) :
    ‖∑ n ∈ (realIntegerInterval x Y).filter
        (fun n : ℤ => data.firstDerivative (n : ℝ) ∈
          Set.Ioc ((k : ℝ) - θ) ((k : ℝ) + θ)),
        kusminPhase (data.f (n : ℝ))‖ ≤ 1 + 2 * θ / lam := by
  classical
  let T := (realIntegerInterval x Y).filter
    (fun n : ℤ => data.firstDerivative (n : ℝ) ∈
      Set.Ioc ((k : ℝ) - θ) ((k : ℝ) + θ))
  change ‖∑ n ∈ T, kusminPhase (data.f (n : ℝ))‖ ≤ 1 + 2 * θ / lam
  by_cases hne : T.Nonempty
  · have hbandT : ∀ n ∈ T,
        (k : ℝ) - θ ≤ data.firstDerivative (n : ℝ) ∧
          data.firstDerivative (n : ℝ) ≤ (k : ℝ) + θ := by
      intro n hn
      exact ⟨(Set.mem_Ioc.mp (Finset.mem_filter.mp hn).2).1.le,
        (Set.mem_Ioc.mp (Finset.mem_filter.mp hn).2).2⟩
    have hcount := data.sample_band_card_bound hlam hsecond T
      (Finset.filter_subset _ _) hne hbandT
    have hcount' : (T.card : ℝ) ≤ 1 + 2 * θ / lam := by
      simpa [show ((k : ℝ) + θ) - ((k : ℝ) - θ) = 2 * θ by ring] using hcount
    exact (kusminPhase_sum_norm_le_card T data.f).trans hcount'
  · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hT]
    simp
    positivity

theorem HalfOpenC2Data.lowDerivativeBandLabelFiber_norm_bound
    {x Y θ : ℝ} {A B : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hAB : A < B)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hRange : ∀ n ∈ realIntegerInterval x Y,
      (A : ℝ) ≤ data.firstDerivative (n : ℝ) ∧
        data.firstDerivative (n : ℝ) ≤ (B : ℝ)) :
    ‖∑ n ∈ (realIntegerInterval x Y).filter
        (fun n => derivativeBandLabelOf θ
          (fun m => data.firstDerivative (m : ℝ)) hAB hθ n =
            DerivativeBandLabel.low),
        kusminPhase (data.f (n : ℝ))‖ ≤ 1 + θ / lam := by
  classical
  rw [derivativeBandLabelOf_filter_eq hAB hθ hθhalf
    (realIntegerInterval x Y) hRange DerivativeBandLabel.low]
  have hfilter : @derivativeBandSamplesForLabel A B θ
      (fun n : ℤ => data.firstDerivative (n : ℝ))
      (realIntegerInterval x Y) (@DerivativeBandLabel.low A B) =
    (realIntegerInterval x Y).filter
      (fun n : ℤ => data.firstDerivative (n : ℝ) ∈
        Set.Icc (A : ℝ) ((A : ℝ) + θ)) := by
    unfold derivativeBandSamplesForLabel
    apply Finset.filter_congr
    intro n hn
    rfl
  rw [hfilter]
  exact data.lowDerivativeBandSamples_norm_bound hθ hlam hsecond

theorem HalfOpenC2Data.highDerivativeBandLabelFiber_norm_bound
    {x Y θ : ℝ} {A B : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hAB : A < B)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hRange : ∀ n ∈ realIntegerInterval x Y,
      (A : ℝ) ≤ data.firstDerivative (n : ℝ) ∧
        data.firstDerivative (n : ℝ) ≤ (B : ℝ)) :
    ‖∑ n ∈ (realIntegerInterval x Y).filter
        (fun n => derivativeBandLabelOf θ
          (fun m => data.firstDerivative (m : ℝ)) hAB hθ n =
            DerivativeBandLabel.high),
        kusminPhase (data.f (n : ℝ))‖ ≤ 1 + θ / lam := by
  classical
  rw [derivativeBandLabelOf_filter_eq hAB hθ hθhalf
    (realIntegerInterval x Y) hRange DerivativeBandLabel.high]
  have hfilter : @derivativeBandSamplesForLabel A B θ
      (fun n : ℤ => data.firstDerivative (n : ℝ))
      (realIntegerInterval x Y) (@DerivativeBandLabel.high A B) =
    (realIntegerInterval x Y).filter
      (fun n : ℤ => data.firstDerivative (n : ℝ) ∈
        Set.Ioc ((B : ℝ) - θ) (B : ℝ)) := by
    unfold derivativeBandSamplesForLabel
    apply Finset.filter_congr
    intro n hn
    rfl
  rw [hfilter]
  exact data.highDerivativeBandSamples_norm_bound hθ hlam hsecond

theorem HalfOpenC2Data.resonantDerivativeBandLabelFiber_norm_bound
    {x Y θ : ℝ} {A B k : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hAB : A < B)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hRange : ∀ n ∈ realIntegerInterval x Y,
      (A : ℝ) ≤ data.firstDerivative (n : ℝ) ∧
        data.firstDerivative (n : ℝ) ≤ (B : ℝ))
    (hkA : A < k) (hkB : k < B) :
    ‖∑ n ∈ (realIntegerInterval x Y).filter
        (fun n => derivativeBandLabelOf θ
          (fun m => data.firstDerivative (m : ℝ)) hAB hθ n =
            DerivativeBandLabel.resonant k hkA hkB),
        kusminPhase (data.f (n : ℝ))‖ ≤ 1 + 2 * θ / lam := by
  classical
  rw [derivativeBandLabelOf_filter_eq hAB hθ hθhalf
    (realIntegerInterval x Y) hRange (DerivativeBandLabel.resonant k hkA hkB)]
  have hfilter : @derivativeBandSamplesForLabel A B θ
      (fun n : ℤ => data.firstDerivative (n : ℝ))
      (realIntegerInterval x Y) (DerivativeBandLabel.resonant k hkA hkB) =
    (realIntegerInterval x Y).filter
      (fun n : ℤ => data.firstDerivative (n : ℝ) ∈
        Set.Ioc ((k : ℝ) - θ) ((k : ℝ) + θ)) := by
    unfold derivativeBandSamplesForLabel
    apply Finset.filter_congr
    intro n hn
    rfl
  rw [hfilter]
  exact data.resonantDerivativeBandSamples_norm_bound hθ hlam hsecond

theorem secondDerivative_positive_monotone_between
    {D E : ℝ → ℝ} {x Y lam : ℝ} (hlam : 0 < lam)
    (hDcont : ∀ a b, x < a → b ≤ x + Y → a ≤ b →
      ContinuousOn D (Set.Icc a b))
    (hDderiv : ∀ t, x < t → t < x + Y → HasDerivAt D (E t) t)
    (hElower : ∀ t, x < t → t < x + Y → lam ≤ E t) :
    ∀ a b, x < a → b ≤ x + Y → a ≤ b → D a ≤ D b := by
  intro a b hxa hbx hab
  by_cases hab' : a = b
  · simp [hab']
  · have hablt : a < b := lt_of_le_of_ne hab hab'
    have hcont := hDcont a b hxa hbx hab
    have hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt D (E t) t := by
      intro t ht
      exact hDderiv t (lt_trans hxa ht.1) (lt_of_lt_of_le ht.2 hbx)
    have hlower : ∀ t ∈ Set.Ioo a b, lam ≤ E t := by
      intro t ht
      exact hElower t (lt_trans hxa ht.1) (lt_of_lt_of_le ht.2 hbx)
    have hgap := secondDerivative_separation_local hablt hcont hderiv hlower
    have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
    nlinarith

theorem realIntegerGoodBandSamples_hull_control
    {x Y θ : ℝ} {k : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hs : (realIntegerGoodBandSamples x Y θ k data.firstDerivative).Nonempty) :
    let s := realIntegerGoodBandSamples x Y θ k data.firstDerivative
    let a : ℝ := ((s.min' hs : ℤ) : ℝ)
    let b : ℝ := ((s.max' hs : ℤ) : ℝ)
    s = Finset.Icc (s.min' hs) (s.max' hs) ∧
      MonotoneOn data.firstDerivative (Set.Icc a b) ∧
      ∀ t ∈ Set.Icc a b,
        (k : ℝ) + θ ≤ data.firstDerivative t ∧
          data.firstDerivative t ≤ (k : ℝ) + 1 - θ := by
  dsimp
  let s := realIntegerGoodBandSamples x Y θ k data.firstDerivative
  let a : ℝ := ((s.min' hs : ℤ) : ℝ)
  let b : ℝ := ((s.max' hs : ℤ) : ℝ)
  have hmS : s.min' hs ∈ s := Finset.min'_mem s hs
  have hnS : s.max' hs ∈ s := Finset.max'_mem s hs
  have hmB : data.firstDerivative ((s.min' hs : ℤ) : ℝ) ∈
      Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ) := by
    exact (Finset.mem_filter.mp hmS).2
  have hnB : data.firstDerivative ((s.max' hs : ℤ) : ℝ) ∈
      Set.Ioc ((k : ℝ) + θ) ((k : ℝ) + 1 - θ) := by
    exact (Finset.mem_filter.mp hnS).2
  have hmSample : s.min' hs ∈ realIntegerInterval x Y :=
    (Finset.mem_filter.mp hmS).1
  have hnSample : s.max' hs ∈ realIntegerInterval x Y :=
    (Finset.mem_filter.mp hnS).1
  have hmI := (mem_realIntegerInterval_iff x Y (s.min' hs)).mp hmSample
  have hnI := (mem_realIntegerInterval_iff x Y (s.max' hs)).mp hnSample
  have hxa : x < a := by simpa [a] using hmI.1
  have hbx : b ≤ x + Y := by simpa [b] using hnI.2
  have hmonoBetween := secondDerivative_positive_monotone_between hlam
    (fun u v hxu hvx huv =>
      (data.restrict_compact hxu hvx).2.1)
    (fun t hxt htx => data.first_hasDerivAt t ⟨hxt, htx⟩)
    (fun t hxt htx => hsecond t ⟨hxt, le_of_lt htx⟩)
  have hmono : MonotoneOn data.firstDerivative (Set.Icc a b) := by
    intro u hu v hv huv
    apply hmonoBetween u v
    · exact lt_of_lt_of_le hxa hu.1
    · exact le_trans hv.2 hbx
    · exact huv
  have hfilter_eq : s = Finset.Icc (s.min' hs) (s.max' hs) := by
    simpa [s, realIntegerGoodBandSamples] using
      realIntegerInterval_goodBand_filter_eq_Icc data.firstDerivative
        hmonoBetween (by simpa [realIntegerGoodBandSamples] using hs)
  have hband : ∀ t ∈ Set.Icc a b,
      (k : ℝ) + θ ≤ data.firstDerivative t ∧
        data.firstDerivative t ≤ (k : ℝ) + 1 - θ := by
    intro t ht
    have hleft := hmonoBetween a t hxa (le_trans ht.2 hbx) ht.1
    have hright := hmonoBetween t b (lt_of_lt_of_le hxa ht.1) hbx ht.2
    rw [Set.mem_Ioc] at hmB hnB
    constructor
    · exact le_trans (le_of_lt hmB.1) hleft
    · exact le_trans hright hnB.2
  exact ⟨hfilter_eq, hmono, hband⟩

theorem realIntegerGoodBandSamples_sum_bound
    {x Y θ : ℝ} {k : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2)
    (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hs : (realIntegerGoodBandSamples x Y θ k data.firstDerivative).Nonempty) :
    ‖∑ n ∈ realIntegerGoodBandSamples x Y θ k data.firstDerivative,
        kusminPhase (data.f (n : ℝ))‖ ≤ Real.cot (Real.pi * θ / 2) := by
  let s := realIntegerGoodBandSamples x Y θ k data.firstDerivative
  let lo : ℤ := s.min' hs
  let hi : ℤ := s.max' hs
  let a : ℝ := (lo : ℝ)
  let b : ℝ := (hi : ℝ)
  let m : ℕ := (hi - lo).toNat
  have hle : lo ≤ hi := Finset.min'_le_max' s hs
  have hmcast : (m : ℤ) = hi - lo := by
    dsimp [m]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hle)
  have hend : a + (m : ℝ) = b := by
    dsimp [a, b]
    have hmcastR : (m : ℝ) = (hi : ℝ) - (lo : ℝ) := by exact_mod_cast hmcast
    rw [hmcastR]
    ring
  have hcontrol := realIntegerGoodBandSamples_hull_control
    data hlam hsecond (by simpa [s] using hs)
  dsimp [s, lo, hi, a, b] at hcontrol
  rcases hcontrol with ⟨hfilter, hmono, hband⟩
  have hloS : lo ∈ s := by simpa [lo] using Finset.min'_mem s hs
  have hhiS : hi ∈ s := by simpa [hi] using Finset.max'_mem s hs
  have hloSample : lo ∈ realIntegerInterval x Y := (Finset.mem_filter.mp hloS).1
  have hhiSample : hi ∈ realIntegerInterval x Y := (Finset.mem_filter.mp hhiS).1
  have hloBounds := (mem_realIntegerInterval_iff x Y lo).mp hloSample
  have hhiBounds := (mem_realIntegerInterval_iff x Y hi).mp hhiSample
  have hxa : x < a := by simpa [a] using hloBounds.1
  have hbx : b ≤ x + Y := by simpa [b] using hhiBounds.2
  have hcompact := data.restrict_compact hxa hbx
  have hfcont : ContinuousOn data.f (Set.Icc a (a + (m : ℝ))) := by
    rw [hend]
    exact hcompact.1
  have hDcont : ContinuousOn data.firstDerivative (Set.Icc a (a + (m : ℝ))) := by
    rw [hend]
    exact hcompact.2.1
  have hDmono : MonotoneOn data.firstDerivative
      (Set.Icc a (a + (m : ℝ))) := by
    simpa [hend] using hmono
  have hderiv : ∀ t ∈ Set.Ioo a (a + (m : ℝ)),
      HasDerivAt data.f (data.firstDerivative t) t := by
    intro t ht
    rw [hend] at ht
    exact hcompact.2.2.2.1 t ht
  have hband' : ∀ t ∈ Set.Icc a (a + (m : ℝ)),
      (k : ℝ) + θ ≤ data.firstDerivative t ∧
        data.firstDerivative t ≤ (k : ℝ) + 1 - θ := by
    intro t ht
    rw [hend] at ht
    exact hband t ht
  have hblock := kusmin_first_derivative_local_block
    hθ hθhalf a m k data.f data.firstDerivative hfcont hDcont hDmono hderiv hband'
  have hsum :
      (∑ n ∈ s, kusminPhase (data.f (n : ℝ))) =
        ∑ i ∈ Finset.range (m + 1),
          kusminPhase (data.f (a + (i : ℝ))) := by
    have hfilter' : s = Finset.Icc lo hi := by simpa [s, lo, hi] using hfilter
    rw [hfilter']
    have hsum' := sum_int_Icc_eq_sum_range_translate
      (fun n : ℤ => kusminPhase (data.f (n : ℝ))) lo hi hle
    simpa [m, a, lo, hi, Int.cast_add] using hsum'
  rw [hsum]
  exact hblock

theorem HalfOpenC2Data.goodDerivativeBandLabelFiber_norm_bound
    {x Y θ : ℝ} {A B k : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hAB : A < B)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hRange : ∀ n ∈ realIntegerInterval x Y,
      (A : ℝ) ≤ data.firstDerivative (n : ℝ) ∧
        data.firstDerivative (n : ℝ) ≤ (B : ℝ))
    (hkA : A ≤ k) (hkB : k < B) :
    ‖∑ n ∈ (realIntegerInterval x Y).filter
        (fun n => derivativeBandLabelOf θ
          (fun m => data.firstDerivative (m : ℝ)) hAB hθ n =
            DerivativeBandLabel.good k hkA hkB),
        kusminPhase (data.f (n : ℝ))‖ ≤ Real.cot (Real.pi * θ / 2) := by
  classical
  rw [derivativeBandLabelOf_filter_eq hAB hθ hθhalf
    (realIntegerInterval x Y) hRange (DerivativeBandLabel.good k hkA hkB)]
  have hfilter : @derivativeBandSamplesForLabel A B θ
      (fun n : ℤ => data.firstDerivative (n : ℝ))
      (realIntegerInterval x Y) (DerivativeBandLabel.good k hkA hkB) =
    realIntegerGoodBandSamples x Y θ k data.firstDerivative := by
    unfold derivativeBandSamplesForLabel realIntegerGoodBandSamples
    apply Finset.filter_congr
    intro n hn
    rfl
  rw [hfilter]
  by_cases hne : (realIntegerGoodBandSamples x Y θ k data.firstDerivative).Nonempty
  · exact realIntegerGoodBandSamples_sum_bound data hθ
      (le_of_lt hθhalf) hlam hsecond hne
  · have hT : realIntegerGoodBandSamples x Y θ k data.firstDerivative = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hT]
    simp
    have harg0 : 0 < Real.pi * θ / 2 := by positivity
    have hargpi : Real.pi * θ / 2 < Real.pi := by
      nlinarith [Real.pi_pos, hθ, hθhalf]
    rw [Real.cot_eq_cos_div_sin]
    have hcos : 0 < Real.cos (Real.pi * θ / 2) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos, harg0, hargpi]
    have hsin : 0 < Real.sin (Real.pi * θ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi harg0 hargpi
    exact (div_pos hcos hsin).le

theorem HalfOpenC2Data.derivativeBandLabelFiber_norm_bound
    {x Y θ : ℝ} {A B : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hAB : A < B)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hRange : ∀ n ∈ realIntegerInterval x Y,
      (A : ℝ) ≤ data.firstDerivative (n : ℝ) ∧
        data.firstDerivative (n : ℝ) ≤ (B : ℝ))
    (band : DerivativeBandLabel A B) :
    ‖∑ n ∈ (realIntegerInterval x Y).filter
        (fun n => derivativeBandLabelOf θ
          (fun m => data.firstDerivative (m : ℝ)) hAB hθ n = band),
        kusminPhase (data.f (n : ℝ))‖ ≤
      match band with
      | .low => 1 + θ / lam
      | .high => 1 + θ / lam
      | .resonant _ _ _ => 1 + 2 * θ / lam
      | .good _ _ _ => Real.cot (Real.pi * θ / 2) := by
  cases band with
  | low => simpa using (data.lowDerivativeBandLabelFiber_norm_bound
      (A := A) (B := B) hAB hθ hθhalf hlam hsecond hRange)
  | high => simpa using (data.highDerivativeBandLabelFiber_norm_bound
      (A := A) (B := B) hAB hθ hθhalf hlam hsecond hRange)
  | resonant k hkA hkB => simpa using
      (data.resonantDerivativeBandLabelFiber_norm_bound
        (A := A) (B := B) hAB hθ hθhalf hlam hsecond hRange hkA hkB)
  | good k hkA hkB => simpa using
      (data.goodDerivativeBandLabelFiber_norm_bound
        (A := A) (B := B) hAB hθ hθhalf hlam hsecond hRange hkA hkB)

theorem HalfOpenC2Data.derivativeBand_sum_norm_bound
    {x Y θ : ℝ} {A B : ℤ} {lam : ℝ}
    (data : HalfOpenC2Data x Y) (hAB : A < B)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hlam : 0 < lam)
    (hsecond : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hRange : ∀ n ∈ realIntegerInterval x Y,
      (A : ℝ) ≤ data.firstDerivative (n : ℝ) ∧
        data.firstDerivative (n : ℝ) ≤ (B : ℝ)) :
    ‖∑ n ∈ realIntegerInterval x Y, kusminPhase (data.f (n : ℝ))‖ ≤
      ((B - A : ℤ) : ℝ) *
        (1 + 2 * θ / lam + Real.cot (Real.pi * θ / 2)) + 1 := by
  classical
  let label := fun n : ℤ => derivativeBandLabelOf θ
    (fun m => data.firstDerivative (m : ℝ)) hAB hθ n
  have hdecomp := derivativeBandLabelFinset_sum_fiberwise
    (realIntegerInterval x Y) label (fun n => kusminPhase (data.f (n : ℝ)))
  calc
    ‖∑ n ∈ realIntegerInterval x Y, kusminPhase (data.f (n : ℝ))‖ =
        ‖∑ band ∈ derivativeBandLabelFinset,
          ∑ n ∈ (realIntegerInterval x Y).filter
            (fun n => label n = band), kusminPhase (data.f (n : ℝ))‖ := by
      rw [← hdecomp]
    _ ≤ ∑ band ∈ derivativeBandLabelFinset,
        ‖∑ n ∈ (realIntegerInterval x Y).filter
          (fun n => label n = band), kusminPhase (data.f (n : ℝ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ band ∈ derivativeBandLabelFinset,
        (match (band : DerivativeBandLabel A B) with
         | .low => 1 + θ / lam
         | .high => 1 + θ / lam
         | .resonant _ _ _ => 1 + 2 * θ / lam
         | .good _ _ _ => Real.cot (Real.pi * θ / 2)) := by
      apply Finset.sum_le_sum
      intro band hband
      exact data.derivativeBandLabelFiber_norm_bound hAB hθ hθhalf
        hlam hsecond hRange band
    _ = ((B - A : ℤ) : ℝ) *
          (1 + 2 * θ / lam + Real.cot (Real.pi * θ / 2)) + 1 :=
      derivativeBandLabelFinset_bound_sum (A := A) (B := B) hAB θ lam

theorem secondDerivative_positive_implies_monotoneOn
    {D E : ℝ → ℝ} {a b lam : ℝ} (hlam : 0 < lam)
    (hDcont : ContinuousOn D (Set.Icc a b))
    (hDderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt D (E x) x)
    (hElower : ∀ x ∈ Set.Ioo a b, lam ≤ E x) :
    MonotoneOn D (Set.Icc a b) := by
  intro x hx y hy hxy
  by_cases hEq : x = y
  · simp [hEq]
  · have hlt : x < y := lt_of_le_of_ne hxy hEq
    have hsubset : Set.Icc x y ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc hx.1 hy.2
    have hcontLocal : ContinuousOn D (Set.Icc x y) := hDcont.mono hsubset
    have hderivLocal : ∀ t ∈ Set.Ioo x y, HasDerivAt D (E t) t := by
      intro t ht
      apply hDderiv t
      constructor
      · exact lt_of_le_of_lt hx.1 ht.1
      · exact lt_of_lt_of_le ht.2 hy.2
    have hlowerLocal : ∀ t ∈ Set.Ioo x y, lam ≤ E t := by
      intro t ht
      apply hElower t
      constructor
      · exact lt_of_le_of_lt hx.1 ht.1
      · exact lt_of_lt_of_le ht.2 hy.2
    have hgap := secondDerivative_separation_local hlt hcontLocal
      hderivLocal hlowerLocal
    have hlen : 0 ≤ y - x := sub_nonneg.mpr hxy
    nlinarith

theorem secondDerivative_upper_increment_local {D E : ℝ → ℝ} {a b upper : ℝ}
    (hab : a < b) (hDcont : ContinuousOn D (Set.Icc a b))
    (hDderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt D (E x) x)
    (hEupper : ∀ x ∈ Set.Ioo a b, E x ≤ upper) :
    D b - D a ≤ upper * (b - a) := by
  obtain ⟨c, hc, hcEq⟩ := exists_hasDerivAt_eq_slope D E hab hDcont hDderiv
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hquot : (D b - D a) / (b - a) ≤ upper := by
    rw [← hcEq]
    exact hEupper c hc
  have hmul := (div_le_iff₀ hlen).mp hquot
  nlinarith

theorem HalfOpenC2Data.sample_derivative_integer_envelope
    {x Y lam Lambda : ℝ} (data : HalfOpenC2Data x Y)
    (hlam : 0 < lam)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y),
      data.secondDerivative t ≤ Lambda)
    (S : Finset ℤ) (hS : S ⊆ realIntegerInterval x Y)
    (hSne : S.Nonempty) :
    ∃ A B : ℤ, A < B ∧
      (∀ n ∈ S,
        (A : ℝ) ≤ data.firstDerivative (n : ℝ) ∧
          data.firstDerivative (n : ℝ) ≤ (B : ℝ)) ∧
      ((B - A : ℤ) : ℝ) ≤ Lambda * Y + 2 := by
  let lo : ℤ := S.min' hSne
  let hi : ℤ := S.max' hSne
  have hle : lo ≤ hi := Finset.min'_le_max' S hSne
  have hloS' : lo ∈ S := by simpa [lo] using Finset.min'_mem S hSne
  have hhiS : hi ∈ S := by simpa [hi] using Finset.max'_mem S hSne
  have hloInt := (mem_realIntegerInterval_iff x Y lo).mp (hS hloS')
  have hhiInt := (mem_realIntegerInterval_iff x Y hi).mp (hS hhiS)
  have hxa : x < (lo : ℝ) := by exact_mod_cast hloInt.1
  have hbx : (hi : ℝ) ≤ x + Y := by exact_mod_cast hhiInt.2
  have hcompact := data.restrict_compact hxa hbx
  have hDderiv : ∀ t ∈ Set.Ioo (lo : ℝ) (hi : ℝ),
      HasDerivAt data.firstDerivative (data.secondDerivative t) t :=
    hcompact.2.2.2.2
  have hDlower : ∀ t ∈ Set.Ioo (lo : ℝ) (hi : ℝ),
      lam ≤ data.secondDerivative t := by
    intro t ht
    exact hlower t ⟨lt_trans hxa ht.1,
      le_of_lt (lt_of_lt_of_le ht.2 hbx)⟩
  have hDupper : ∀ t ∈ Set.Ioo (lo : ℝ) (hi : ℝ),
      data.secondDerivative t ≤ Lambda := by
    intro t ht
    exact hupper t ⟨lt_trans hxa ht.1,
      le_of_lt (lt_of_lt_of_le ht.2 hbx)⟩
  have hmono := secondDerivative_positive_implies_monotoneOn hlam
    hcompact.2.1 hDderiv hDlower
  have hDloHi : data.firstDerivative (lo : ℝ) ≤
      data.firstDerivative (hi : ℝ) := by
    apply hmono
    · exact ⟨le_rfl, by exact_mod_cast hle⟩
    · exact ⟨by exact_mod_cast hle, le_rfl⟩
    · exact_mod_cast hle
  have hdiff : data.firstDerivative (hi : ℝ) -
      data.firstDerivative (lo : ℝ) ≤ Lambda * Y := by
    by_cases hEq : lo = hi
    · simp [hEq]
      have hLambda : 0 ≤ Lambda := by
        let t := x + Y / 2
        have htIoc : t ∈ Set.Ioc x (x + Y) := by
          dsimp [t]
          constructor <;> nlinarith [data.length_pos]
        have hlamLambda := (hlower t htIoc).trans (hupper t htIoc)
        exact le_trans (le_of_lt hlam) hlamLambda
      exact mul_nonneg hLambda (le_of_lt data.length_pos)
    · have hlt : (lo : ℝ) < (hi : ℝ) := by
        exact_mod_cast (lt_of_le_of_ne hle hEq)
      have hinc := secondDerivative_upper_increment_local hlt
        hcompact.2.1 hDderiv hDupper
      have hlen : (hi : ℝ) - (lo : ℝ) ≤ Y := by nlinarith
      have hLambda : 0 ≤ Lambda := by
        let t := x + Y / 2
        have htIoc : t ∈ Set.Ioc x (x + Y) := by
          dsimp [t]
          constructor <;> nlinarith [data.length_pos]
        have hlamLambda := (hlower t htIoc).trans (hupper t htIoc)
        exact le_trans (le_of_lt hlam) hlamLambda
      nlinarith
  let A : ℤ := Int.ceil (data.firstDerivative (lo : ℝ)) - 1
  let B : ℤ := Int.ceil (data.firstDerivative (hi : ℝ))
  have hAlo : (A : ℝ) ≤ data.firstDerivative (lo : ℝ) := by
    dsimp [A]
    push_cast
    have hceil := Int.ceil_lt_add_one (data.firstDerivative (lo : ℝ))
    linarith
  have hhiB : data.firstDerivative (hi : ℝ) ≤ (B : ℝ) := by
    dsimp [B]
    exact Int.le_ceil _
  have hABreal : (A : ℝ) < (B : ℝ) := by
    dsimp [A, B]
    have hceilA : ((Int.ceil (data.firstDerivative (lo : ℝ)) - 1 : ℤ) : ℝ) <
        data.firstDerivative (lo : ℝ) := by
      have hceil := Int.ceil_lt_add_one (data.firstDerivative (lo : ℝ))
      push_cast at hceil ⊢
      linarith
    exact lt_of_lt_of_le hceilA (le_trans hDloHi hhiB)
  have hAB : A < B := by exact_mod_cast hABreal
  have hRange : ∀ n ∈ S,
      (A : ℝ) ≤ data.firstDerivative (n : ℝ) ∧
        data.firstDerivative (n : ℝ) ≤ (B : ℝ) := by
    intro n hn
    have hloN : lo ≤ n := Finset.min'_le S n hn
    have hnHi : n ≤ hi := Finset.le_max' S n hn
    have hloN' : (lo : ℝ) ≤ (n : ℝ) := by exact_mod_cast hloN
    have hnHi' : (n : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hnHi
    have hDloN : data.firstDerivative (lo : ℝ) ≤
        data.firstDerivative (n : ℝ) := by
      apply hmono
      · exact ⟨le_rfl, by exact_mod_cast hle⟩
      · exact ⟨hloN', hnHi'⟩
      · exact hloN'
    have hDnHi : data.firstDerivative (n : ℝ) ≤
        data.firstDerivative (hi : ℝ) := by
      apply hmono
      · exact ⟨hloN', hnHi'⟩
      · exact ⟨by exact_mod_cast hle, le_rfl⟩
      · exact hnHi'
    exact ⟨hAlo.trans hDloN, hDnHi.trans hhiB⟩
  have hwidth : ((B - A : ℤ) : ℝ) ≤ Lambda * Y + 2 := by
    have hceilHi : (B : ℝ) < data.firstDerivative (hi : ℝ) + 1 := by
      dsimp [B]
      exact Int.ceil_lt_add_one _
    have hceilLo : data.firstDerivative (lo : ℝ) ≤
        (Int.ceil (data.firstDerivative (lo : ℝ)) : ℝ) := Int.le_ceil _
    dsimp [A, B]
    push_cast
    nlinarith
  exact ⟨A, B, hAB, hRange, hwidth⟩

theorem HalfOpenC2Data.secondDerivative_raw_bound
    {x Y θ lam Lambda : ℝ} (data : HalfOpenC2Data x Y)
    (hlam : 0 < lam)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y),
      data.secondDerivative t ≤ Lambda)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    ‖∑ n ∈ realIntegerInterval x Y, kusminPhase (data.f (n : ℝ))‖ ≤
      (Lambda * Y + 2) * (1 + 2 * θ / lam + 2 / (Real.pi * θ)) + 1 := by
  classical
  by_cases hS : (realIntegerInterval x Y).Nonempty
  · obtain ⟨A, B, hAB, hRange, hwidth⟩ :=
      data.sample_derivative_integer_envelope hlam hlower hupper
        (realIntegerInterval x Y) (by intro n hn; exact hn) hS
    have hagg := data.derivativeBand_sum_norm_bound hAB hθ hθhalf
      hlam hlower hRange
    have harg0 : 0 < Real.pi * θ / 2 := by positivity
    have hargHalf : Real.pi * θ / 2 ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos, hθhalf]
    have hcot := real_cot_le_inv_of_mem_Ioc harg0 hargHalf
    have hcot' : Real.cot (Real.pi * θ / 2) ≤ 2 / (Real.pi * θ) := by
      have hiden : 1 / (Real.pi * θ / 2) = 2 / (Real.pi * θ) := by
        field_simp
      rw [← hiden]
      exact hcot
    have hcotNonneg : 0 ≤ Real.cot (Real.pi * θ / 2) := by
      have h := real_cot_pi_nonneg (θ := θ / 2) (by positivity)
        (by nlinarith [hθhalf])
      simpa [show Real.pi * (θ / 2) = Real.pi * θ / 2 by ring] using h
    have hwidthNonneg : 0 ≤ ((B - A : ℤ) : ℝ) := by
      exact_mod_cast (sub_nonneg.mpr hAB.le)
    have hcoefNonneg : 0 ≤ 1 + 2 * θ / lam +
        Real.cot (Real.pi * θ / 2) := by
      positivity
    have hcoefCmp : 1 + 2 * θ / lam + Real.cot (Real.pi * θ / 2) ≤
        1 + 2 * θ / lam + 2 / (Real.pi * θ) := by linarith
    have hLambda : 0 ≤ Lambda := by
      let t := x + Y / 2
      have ht : t ∈ Set.Ioc x (x + Y) := by
        dsimp [t]
        constructor <;> nlinarith [data.length_pos]
      exact le_trans (le_of_lt hlam) ((hlower t ht).trans (hupper t ht))
    have hfactorNonneg : 0 ≤ Lambda * Y + 2 := by
      have hY : 0 ≤ Y := le_of_lt data.length_pos
      nlinarith [mul_nonneg hLambda hY]
    have hfirst := mul_le_mul_of_nonneg_right hwidth hcoefNonneg
    have hsecond := mul_le_mul_of_nonneg_left hcoefCmp hfactorNonneg
    calc
      ‖∑ n ∈ realIntegerInterval x Y, kusminPhase (data.f (n : ℝ))‖ ≤
          ((B - A : ℤ) : ℝ) *
            (1 + 2 * θ / lam + Real.cot (Real.pi * θ / 2)) + 1 := hagg
      _ ≤ (Lambda * Y + 2) *
            (1 + 2 * θ / lam + Real.cot (Real.pi * θ / 2)) + 1 := by
          linarith
      _ ≤ (Lambda * Y + 2) *
            (1 + 2 * θ / lam + 2 / (Real.pi * θ)) + 1 := by
          linarith
  · have hEmpty : realIntegerInterval x Y = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty]
    simp
    have hLambda : 0 ≤ Lambda := by
      let t := x + Y / 2
      have ht : t ∈ Set.Ioc x (x + Y) := by
        dsimp [t]
        constructor <;> nlinarith [data.length_pos]
      exact le_trans (le_of_lt hlam) ((hlower t ht).trans (hupper t ht))
    have hY : 0 ≤ Y := le_of_lt data.length_pos
    have hpiθ : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ
    positivity

theorem HalfOpenC2Data.secondDerivative_bound_14_over_5
    {x Y lam Lambda : ℝ} (data : HalfOpenC2Data x Y)
    (hY : 1 ≤ Y) (hlam : 0 < lam)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y),
      lam ≤ data.secondDerivative t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y),
      data.secondDerivative t ≤ Lambda) :
    ‖∑ n ∈ realIntegerInterval x Y, kusminPhase (data.f (n : ℝ))‖ ≤
      (14 / 5) / Real.sqrt lam * (Lambda * Y + 2) := by
  have hLambda : lam ≤ Lambda := by
    let t := x + Y / 2
    have ht : t ∈ Set.Ioc x (x + Y) := by
      dsimp [t]
      constructor <;> nlinarith [data.length_pos]
    exact (hlower t ht).trans (hupper t ht)
  have hLambdaNonneg : 0 ≤ Lambda := le_trans (le_of_lt hlam) hLambda
  have hFactor : 2 ≤ Lambda * Y + 2 := by
    have hY0 : 0 ≤ Y := by linarith
    nlinarith [mul_nonneg hLambdaNonneg hY0]
  by_cases hSmall : lam ≤ (5 / 14 : ℝ) ^ 2
  · let θ := Real.sqrt (lam / Real.pi)
    have hθpos : 0 < θ := by
      dsimp [θ]
      exact Real.sqrt_pos.2 (div_pos hlam Real.pi_pos)
    have hθsq : θ ^ 2 = lam / Real.pi := by
      dsimp [θ]
      rw [Real.sq_sqrt (le_of_lt (div_pos hlam Real.pi_pos))]
    have hθhalf : θ < 1 / 2 := by
      have hratio : lam / Real.pi < (1 / 2 : ℝ) ^ 2 := by
        apply (div_lt_iff₀ Real.pi_pos).2
        nlinarith [hSmall, Real.pi_gt_three]
      nlinarith [sq_nonneg (θ - 1 / 2), hθsq]
    have hraw := data.secondDerivative_raw_bound hlam hlower hupper
      hθpos hθhalf
    let s := Real.sqrt lam
    let M := Lambda * Y + 2
    let C := 1 + 2 * θ / lam + 2 / (Real.pi * θ)
    have hspos : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 hlam
    have hsSq : s ^ 2 = lam := by
      dsimp [s]
      rw [Real.sq_sqrt (le_of_lt hlam)]
    have hM : 2 ≤ M := by dsimp [M]; exact hFactor
    have hrootPi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    have hthetaForm : θ = s / Real.sqrt Real.pi := by
      dsimp [θ, s]
      rw [Real.sqrt_div (le_of_lt hlam)]
    have hcoeffIdentity : s * C = s + 4 / Real.sqrt Real.pi := by
      dsimp [C]
      rw [hthetaForm]
      field_simp [ne_of_gt hlam, ne_of_gt hθpos,
        ne_of_gt Real.pi_pos, ne_of_gt hspos, ne_of_gt hrootPi]
      nlinarith [hsSq, Real.sq_sqrt (le_of_lt Real.pi_pos)]
    have hsUpper : s ≤ 5 / 14 := by
      dsimp [s]
      have hh := Real.sqrt_le_sqrt hSmall
      rw [Real.sqrt_sq_eq_abs] at hh
      have hnonneg : 0 ≤ (5 : ℝ) / 14 := by positivity
      simpa [abs_of_nonneg hnonneg] using hh
    have hnum : (560 : ℝ) ^ 2 < (317 : ℝ) ^ 2 * (157 / 50) := by norm_num
    have hpiApprox : 4 / Real.sqrt Real.pi < 317 / 140 := by
      have hsq : (4 / Real.sqrt Real.pi) ^ 2 < (317 / 140 : ℝ) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (le_of_lt Real.pi_pos)]
        norm_num
        apply (div_lt_iff₀ Real.pi_pos).2
        have hpi : (157 / 50 : ℝ) < Real.pi := by
          have hpi0 := Real.pi_gt_d2
          norm_num at hpi0
          linarith
        nlinarith [hnum, hpi]
      have hleft : 0 ≤ 4 / Real.sqrt Real.pi := by positivity
      have hright : 0 ≤ (317 / 140 : ℝ) := by positivity
      nlinarith
    have hscaled : s * C + s / M ≤ 14 / 5 := by
      have hsM : s / M ≤ s / 2 := by
        have hMpos : 0 < M := by linarith [hM]
        apply (div_le_div_iff₀ hMpos (by norm_num : (0 : ℝ) < 2)).2
        nlinarith [hM]
      rw [hcoeffIdentity]
      have : s + s / 2 + 4 / Real.sqrt Real.pi ≤
          15 / 28 + 317 / 140 := by
        nlinarith [hsUpper, hpiApprox]
      nlinarith
    have hrawScaled : s * ‖∑ n ∈ realIntegerInterval x Y,
        kusminPhase (data.f (n : ℝ))‖ ≤ s * (M * C + 1) :=
      mul_le_mul_of_nonneg_left hraw (le_of_lt hspos)
    have hfactor : s * (M * C + 1) = M * (s * (C + 1 / M)) := by
      dsimp [M]
      field_simp [ne_of_gt (by linarith : 0 < Lambda * Y + 2)]
    rw [hfactor] at hrawScaled
    have hscaled' : s * (C + 1 / M) ≤ 14 / 5 := by
      have hsum : s * (C + 1 / M) = s * C + s / M := by
        field_simp [ne_of_gt (by linarith : 0 < M)]
      rw [hsum]
      exact hscaled
    have hrawScaled' : s * ‖∑ n ∈ realIntegerInterval x Y,
        kusminPhase (data.f (n : ℝ))‖ ≤ M * (14 / 5) :=
      le_trans hrawScaled (mul_le_mul_of_nonneg_left hscaled' (by linarith [hM]))
    have htarget : ‖∑ n ∈ realIntegerInterval x Y,
        kusminPhase (data.f (n : ℝ))‖ ≤ ((14 / 5 : ℝ) * M) / s := by
      apply (le_div_iff₀ hspos).2
      calc
        ‖∑ n ∈ realIntegerInterval x Y,
            kusminPhase (data.f (n : ℝ))‖ * s ≤ M * (14 / 5) := by
          simpa [mul_comm] using hrawScaled'
        _ = (14 / 5) * M := by ring
    have htargetEq : ((14 / 5 : ℝ) * M) / s =
        (14 / 5) / Real.sqrt lam * (Lambda * Y + 2) := by
      dsimp [M, s]
      field_simp [ne_of_gt hspos]
    rw [htargetEq] at htarget
    exact htarget
  · have hLarge : (5 / 14 : ℝ) ^ 2 ≤ lam := (not_le.mp hSmall).le
    let s := Real.sqrt lam
    let M := (14 / 5 : ℝ) / s
    have hspos : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 hlam
    have hsSq : s ^ 2 = lam := by
      dsimp [s]
      rw [Real.sq_sqrt (le_of_lt hlam)]
    have hsLower : 5 / 14 ≤ s := by
      dsimp [s]
      have hroot : Real.sqrt ((5 / 14 : ℝ) ^ 2) = 5 / 14 := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (5 : ℝ) / 14)]
      rw [← hroot]
      exact Real.sqrt_le_sqrt hLarge
    have hM1 : 1 / lam ≤ M := by
      dsimp [M]
      apply (div_le_div_iff₀ hlam hspos).2
      nlinarith [mul_nonneg (le_of_lt hspos)
        (show 0 ≤ 14 * s - 5 by nlinarith [hsLower, hsSq])]
    have hM2 : 2 / (lam + 2) ≤ M := by
      dsimp [M]
      apply (div_le_div_iff₀ (by positivity) hspos).2
      nlinarith [sq_nonneg (s - 5 / 14), hsSq]
    have hcard := realIntegerInterval_card_le x Y hY
    have htrivial : ‖∑ n ∈ realIntegerInterval x Y,
        kusminPhase (data.f (n : ℝ))‖ ≤ Y + 1 :=
      (kusminPhase_sum_norm_le_card (realIntegerInterval x Y) data.f).trans hcard
    have hden : lam * Y + 2 ≤ Lambda * Y + 2 := by
      have hY0 : 0 ≤ Y := by linarith
      have hmul := mul_le_mul_of_nonneg_right hLambda hY0
      linarith
    have hbound : Y + 1 ≤ M * (Lambda * Y + 2) := by
      by_cases hLam2 : lam ≤ 2
      · have hbase : Y + 1 ≤ (1 / lam) * (lam * Y + 2) := by
          have hrecip : 1 ≤ 2 / lam := by
            exact (le_div_iff₀ hlam).2 (by nlinarith [hLam2])
          field_simp [ne_of_gt hlam]
          nlinarith [hrecip]
        calc
          Y + 1 ≤ (1 / lam) * (lam * Y + 2) := hbase
          _ ≤ M * (lam * Y + 2) :=
            mul_le_mul_of_nonneg_right hM1 (by positivity)
          _ ≤ M * (Lambda * Y + 2) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
      · have hLam2 : 2 ≤ lam := le_of_not_ge hLam2
        have hbase : Y + 1 ≤ (2 / (lam + 2)) * (lam * Y + 2) := by
          have hprod : 0 ≤ (lam - 2) * (Y - 1) :=
            mul_nonneg (sub_nonneg.mpr hLam2) (sub_nonneg.mpr (by linarith))
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ (by positivity)).2
          nlinarith [hprod]
        calc
          Y + 1 ≤ (2 / (lam + 2)) * (lam * Y + 2) := hbase
          _ ≤ M * (lam * Y + 2) :=
            mul_le_mul_of_nonneg_right hM2 (by positivity)
          _ ≤ M * (Lambda * Y + 2) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
    have hscaled : ‖∑ n ∈ realIntegerInterval x Y,
        kusminPhase (data.f (n : ℝ))‖ ≤ M * (Lambda * Y + 2) :=
      htrivial.trans hbound
    dsimp [M, s] at hscaled ⊢
    exact hscaled

theorem iteratedTuple_secondDerivative_sum_bound
    {x Y lower upper : ℝ} {order : ℕ}
    (data : HalfOpenCkData x Y order) (shifts : List ℕ)
    (hlen : shifts.length + 2 = order)
    (hpos : ∀ a ∈ shifts, 0 < a)
    (hTotal : realShiftTotal shifts + 1 ≤ Y)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y), lower ≤ data.derivative order t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y), data.derivative order t ≤ upper)
    (hlowerPos : 0 < lower) (hupperLower : lower ≤ upper) :
    ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
        realExponentialPhase (iteratedRealForwardDifference (data.derivative 0) shifts) n‖ ≤
      (14 / 5) / Real.sqrt lower *
        (2 / Real.sqrt ((shifts.flatMap fun a => [(a : ℝ)]).prod) +
          Y * upper * Real.sqrt ((shifts.flatMap fun a => [(a : ℝ)]).prod)) := by
  let rshifts : List ℝ := List.map (fun a : ℕ => (a : ℝ)) shifts
  let L := Y - realShiftTotal shifts
  let p := rshifts.prod
  have hrshift : List.map (fun a : ℕ => (a : ℝ)) shifts =
      List.flatMap (fun a : ℕ => [(a : ℝ)]) shifts :=
    list_map_eq_flatMap_singleton shifts (fun a => (a : ℝ))
  have hsumEq : rshifts.sum = realShiftTotal shifts := by
    simpa [rshifts, realShiftTotal, List.map_id] using congrArg List.sum hrshift
  have hposR : ∀ a ∈ rshifts, 0 < a := by
    intro a ha
    dsimp only [rshifts] at ha
    rw [List.mem_map] at ha
    rcases ha with ⟨b, hb, hba⟩
    rw [← hba]
    exact_mod_cast hpos b hb
  have hsumlt : rshifts.sum < Y := by rw [hsumEq]; linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := by linarith
  have hLY : L ≤ Y := by dsimp [L]; linarith [realShiftTotal_nonneg shifts]
  have hp : 0 < p := by
    dsimp [p, rshifts]
    apply List.prod_pos
    intro a ha
    change a ∈ shifts.map (fun b : ℕ => (b : ℝ)) at ha
    rw [List.mem_map] at ha
    rcases ha with ⟨b, hb, hba⟩
    rw [← hba]
    exact_mod_cast hpos b hb
  have hlenR : rshifts.length + 2 = order := by simpa [rshifts] using hlen
  let diffData := data.iteratedDifferenceData rshifts hposR hsumlt (by omega)
  have hsecond (t : ℝ) (ht : t ∈ Set.Ioc x (x + L)) :
      lower * p ≤ diffData.derivative 2 t ∧ diffData.derivative 2 t ≤ upper * p := by
    have htUpper : t ≤ x + (Y - rshifts.sum) := by
      simpa [L, hsumEq] using ht.2
    have htend : t + rshifts.sum ≤ x + Y := by
      linarith
    have hbounds := data.iteratedSecondDerivative_product_bounds rshifts hlenR
      hposR ht.1 htend (fun s hs => ⟨hlower s hs, hupper s hs⟩)
    simpa [diffData, p] using hbounds
  let c2 := diffData.toC2Data (by omega)
  have hsecondLower : ∀ t ∈ Set.Ioc x (x + L), lower * p ≤ c2.secondDerivative t := by
    intro t ht
    exact hsecond t ht |>.1
  have hsecondUpper : ∀ t ∈ Set.Ioc x (x + L), c2.secondDerivative t ≤ upper * p := by
    intro t ht
    exact hsecond t ht |>.2
  have hsecondLower' : ∀ t ∈ Set.Ioc x (x + (Y - rshifts.sum)),
      lower * p ≤ c2.secondDerivative t := by
    simpa [L, hsumEq] using hsecondLower
  have hsecondUpper' : ∀ t ∈ Set.Ioc x (x + (Y - rshifts.sum)),
      c2.secondDerivative t ≤ upper * p := by
    simpa [L, hsumEq] using hsecondUpper
  have hlowprod : 0 < lower * p := mul_pos hlowerPos hp
  have hL' : 1 ≤ Y - rshifts.sum := by simpa [hsumEq] using hL
  have htest := c2.secondDerivative_bound_14_over_5 hL' hlowprod hsecondLower' hsecondUpper'
  have htestL :
      ‖∑ n ∈ realIntegerInterval x L, kusminPhase (c2.f (n : ℝ))‖ ≤
        (14 / 5) / Real.sqrt (lower * p) * (upper * p * L + 2) := by
    simpa [L, hsumEq] using htest
  have hfunc : diffData.derivative 0 =
      iteratedRealForwardDifference (data.derivative 0) shifts := by
    have hderiv := data.iteratedDifferenceData_derivative rshifts hposR hsumlt
      (by omega) (k := 0) (by omega)
    have hcast : iteratedRealForwardDifference (data.derivative 0) shifts =
        iteratedRealForwardDifferenceR (data.derivative 0) rshifts := by
      have hc := iteratedRealForwardDifference_cast (data.derivative 0) shifts
      simpa [rshifts, Function.comp_def, id_eq, ← hrshift] using hc
    exact hderiv.trans hcast.symm
  have hsumEqInterval : iteratedDifferenceInterval x Y shifts =
      realIntegerInterval x L := by
    simp [iteratedDifferenceInterval, L]
  have hphaseSum :
      ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
          realExponentialPhase (iteratedRealForwardDifference (data.derivative 0) shifts) n‖ =
        ‖∑ n ∈ realIntegerInterval x L,
          kusminPhase (c2.f (n : ℝ))‖ := by
    rw [hsumEqInterval]
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro n hn
    change realExponentialPhase
        (iteratedRealForwardDifference (data.derivative 0) shifts) n =
      kusminPhase (diffData.derivative 0 (n : ℝ))
    rw [← hfunc]
    rfl
  have hsqrtP : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsqrtL : 0 < Real.sqrt lower := Real.sqrt_pos.mpr hlowerPos
  have hscale : (14 / 5) / Real.sqrt (lower * p) * (upper * p * L + 2) =
      (14 / 5) / Real.sqrt lower * (upper * Real.sqrt p * L + 2 / Real.sqrt p) := by
    rw [Real.sqrt_mul (le_of_lt hlowerPos)]
    have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (le_of_lt hp)
    field_simp [ne_of_gt hsqrtP, ne_of_gt hsqrtL]
    rw [hsq]
    ring
  have hupperNonneg : 0 ≤ upper := le_trans (le_of_lt hlowerPos) hupperLower
  have hcoefNonneg : 0 ≤ upper * Real.sqrt p := mul_nonneg hupperNonneg (le_of_lt hsqrtP)
  have hsumBound : upper * Real.sqrt p * L + 2 / Real.sqrt p ≤
      2 / Real.sqrt p + Y * upper * Real.sqrt p := by
    nlinarith [mul_le_mul_of_nonneg_left hLY hcoefNonneg]
  have hresult :
      ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
          realExponentialPhase (iteratedRealForwardDifference (data.derivative 0) shifts) n‖ ≤
        (14 / 5) / Real.sqrt lower * (2 / Real.sqrt p + Y * upper * Real.sqrt p) := by
    rw [hphaseSum]
    calc
      ‖∑ n ∈ realIntegerInterval x L, kusminPhase (c2.f (n : ℝ))‖ ≤
          (14 / 5) / Real.sqrt (lower * p) * (upper * p * L + 2) := htestL
      _ = (14 / 5) / Real.sqrt lower * (upper * Real.sqrt p * L + 2 / Real.sqrt p) := hscale
      _ ≤ (14 / 5) / Real.sqrt lower * (2 / Real.sqrt p + Y * upper * Real.sqrt p) := by
        apply mul_le_mul_of_nonneg_left hsumBound
        positivity
  simpa [p, rshifts, hrshift, List.map_id] using hresult

theorem derivativeCorrelationBound
    {x Y lower upper : ℝ} {order : ℕ}
    (data : HalfOpenCkData x Y order)
    (horder : 3 ≤ order) (hY : (order : ℝ) < Y)
    (bounds : List ℕ) (hlen : bounds.length + 2 = order)
    (hBoundsPos : ∀ H ∈ bounds, 0 < H)
    (hBoundsTotal : realShiftTotal bounds ≤ Y)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y), lower ≤ data.derivative order t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y), data.derivative order t ≤ upper)
    (hlowerPos : 0 < lower) :
    averagedIteratedCorrelation (data.derivative 0) x Y bounds ≤
      (14 / 5) / (Y * Real.sqrt lower) *
        ((2 : ℝ) ^ (bounds.length + 1) /
            Real.sqrt (realShiftPlusNormalizer bounds) +
          (2 / 3 : ℝ) ^ bounds.length * Y * upper *
            Real.sqrt (realShiftNormalizer bounds)) := by
  let P := realShiftNormalizer bounds
  let Pplus := realShiftPlusNormalizer bounds
  let C := (14 / 5 : ℝ) / Real.sqrt lower
  let box := positiveShiftBox bounds
  let normTerm : List ℕ → ℝ := fun shifts =>
    ‖∑ n ∈ iteratedDifferenceInterval x Y shifts,
      realExponentialPhase (iteratedRealForwardDifference (data.derivative 0) shifts) n‖
  let recipWeight : List ℕ → ℝ := fun shifts =>
    1 / Real.sqrt ((List.map (fun a : ℕ => (a : ℝ)) shifts).prod)
  let sqrtWeight : List ℕ → ℝ := fun shifts =>
    Real.sqrt ((List.map (fun a : ℕ => (a : ℝ)) shifts).prod)
  have hlenPos : 1 ≤ bounds.length := by omega
  have hlenReal : (1 : ℝ) ≤ (bounds.length : ℝ) := by exact_mod_cast hlenPos
  have hYpos : 0 < Y := by
    have horderReal : (3 : ℝ) ≤ (order : ℝ) := by exact_mod_cast horder
    linarith
  have hPpos : 0 < P := by
    dsimp [P]
    exact realShiftNormalizer_pos bounds hBoundsPos
  have hPplusPos : 0 < Pplus := by
    dsimp [Pplus]
    exact realShiftPlusNormalizer_pos bounds hBoundsPos
  have hlowerUpper : lower ≤ upper := by
    have hend : x + Y ∈ Set.Ioc x (x + Y) := by constructor <;> linarith
    exact le_trans (hlower (x + Y) hend) (hupper (x + Y) hend)
  have htuple : ∀ shifts ∈ box,
      normTerm shifts ≤ C * (2 * recipWeight shifts + Y * upper * sqrtWeight shifts) := by
    intro shifts hshifts
    have hshiftPos := positiveShiftBox_entries_pos bounds shifts hBoundsPos hshifts
    have hshiftLength := positiveShiftBox_length bounds shifts hshifts
    have hshiftLenOne : (1 : ℝ) ≤ (shifts.length : ℝ) := by
      rw [hshiftLength]
      exact hlenReal
    have hshiftMargin := realShiftTotal_add_length_le_bounds bounds shifts hshifts
    have hshiftTotal : realShiftTotal shifts + 1 ≤ Y := by
      have hbound := hshiftMargin.trans hBoundsTotal
      linarith
    have hshiftOrder : shifts.length + 2 = order := by
      rw [hshiftLength]
      exact hlen
    have htupleRaw := iteratedTuple_secondDerivative_sum_bound data shifts
      hshiftOrder hshiftPos hshiftTotal hlower hupper hlowerPos hlowerUpper
    have hmap : List.map (fun a : ℕ => (a : ℝ)) shifts =
        List.flatMap (fun a : ℕ => [(a : ℝ)]) shifts :=
      list_map_eq_flatMap_singleton shifts (fun a => (a : ℝ))
    dsimp [normTerm, recipWeight, sqrtWeight, C]
    simpa [hmap, div_eq_mul_inv, mul_assoc] using htupleRaw
  have hsumEstimate :
      (∑ shifts ∈ box, normTerm shifts) ≤
        C * (2 * (∑ shifts ∈ box, recipWeight shifts) +
          Y * upper * (∑ shifts ∈ box, sqrtWeight shifts)) := by
    calc
      (∑ shifts ∈ box, normTerm shifts) ≤
          ∑ shifts ∈ box,
            C * (2 * recipWeight shifts + Y * upper * sqrtWeight shifts) := by
        apply Finset.sum_le_sum
        intro shifts hshifts
        exact htuple shifts hshifts
      _ = C * (2 * (∑ shifts ∈ box, recipWeight shifts) +
            Y * upper * (∑ shifts ∈ box, sqrtWeight shifts)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  have hrecip := reciprocal_sqrt_positiveShiftBox_sum_bound bounds hBoundsPos
  have hsqrts := sqrt_positiveShiftBox_sum_bound bounds hBoundsPos
  rw [reciprocal_coordinate_product_normalization bounds hBoundsPos] at hrecip
  rw [sqrt_coordinate_product_normalization] at hsqrts
  have hPmap : P = (List.map (fun H : ℕ => (H : ℝ)) bounds).prod := by
    have hrshift : List.map (fun H : ℕ => (H : ℝ)) bounds =
        List.flatMap (fun H : ℕ => [(H : ℝ)]) bounds :=
      list_map_eq_flatMap_singleton bounds (fun H => (H : ℝ))
    dsimp [P, realShiftNormalizer]
    simpa using congrArg List.prod hrshift.symm
  rw [← hPmap] at hsqrts
  have hupperPos : 0 < upper := lt_of_lt_of_le hlowerPos hlowerUpper
  have hscaleTerms :
      2 * (∑ shifts ∈ box, recipWeight shifts) +
          Y * upper * (∑ shifts ∈ box, sqrtWeight shifts) ≤
        2 * ((2 : ℝ) ^ bounds.length * P / Real.sqrt Pplus) +
          Y * upper * ((2 / 3 : ℝ) ^ bounds.length * P ^ (3 / 2 : ℝ)) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hrecip (by norm_num)
    · exact mul_le_mul_of_nonneg_left hsqrts (by positivity)
  have hsumFinal : (∑ shifts ∈ box, normTerm shifts) ≤
      C * (2 * ((2 : ℝ) ^ bounds.length * P / Real.sqrt Pplus) +
        Y * upper * ((2 / 3 : ℝ) ^ bounds.length * P ^ (3 / 2 : ℝ))) :=
    hsumEstimate.trans (mul_le_mul_of_nonneg_left hscaleTerms (by positivity))
  have hsqrtLower : 0 < Real.sqrt lower := Real.sqrt_pos.2 hlowerPos
  have hsqrtP : 0 < Real.sqrt P := Real.sqrt_pos.2 hPpos
  have hsqrtPplus : 0 < Real.sqrt Pplus := Real.sqrt_pos.2 hPplusPos
  have hpowP : P ^ (3 / 2 : ℝ) = P * Real.sqrt P := by
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num,
      Real.rpow_add_one (ne_of_gt hPpos), Real.sqrt_eq_rpow]
    ring
  have hYP : 0 < Y * P := mul_pos hYpos hPpos
  have hdiv :
      (∑ shifts ∈ box, normTerm shifts) / (Y * P) ≤
        (14 / 5) / (Y * Real.sqrt lower) *
          ((2 : ℝ) ^ (bounds.length + 1) / Real.sqrt Pplus +
            (2 / 3 : ℝ) ^ bounds.length * Y * upper * Real.sqrt P) := by
    apply (div_le_iff₀ hYP).2
    calc
      (∑ shifts ∈ box, normTerm shifts) ≤
          C * (2 * ((2 : ℝ) ^ bounds.length * P / Real.sqrt Pplus) +
            Y * upper * ((2 / 3 : ℝ) ^ bounds.length * P ^ (3 / 2 : ℝ))) := hsumFinal
      _ = ((14 / 5) / (Y * Real.sqrt lower) *
          ((2 : ℝ) ^ (bounds.length + 1) / Real.sqrt Pplus +
            (2 / 3 : ℝ) ^ bounds.length * Y * upper * Real.sqrt P)) * (Y * P) := by
        rw [hpowP]
        dsimp [C]
        field_simp [ne_of_gt hYpos, ne_of_gt hPpos, ne_of_gt hsqrtLower,
          ne_of_gt hsqrtP, ne_of_gt hsqrtPplus]
        ring
  unfold averagedIteratedCorrelation
  rw [show (Y * P)⁻¹ * (∑ shifts ∈ box, normTerm shifts) =
      (∑ shifts ∈ box, normTerm shifts) / (Y * P) by
        rw [div_eq_mul_inv]
        ring]
  simpa [P, box, normTerm] using hdiv

theorem secondDerivative_band_card_bound
    (s : Finset ℕ) (N : ℕ) (a lower upper lam : ℝ)
    (D E : ℝ → ℝ) (hlam : 0 < lam) (hs : s.Nonempty)
    (hsupport : s ⊆ Finset.range (N + 1))
    (hDcont : ContinuousOn D (Set.Icc a (a + (N : ℝ))))
    (hDderiv : ∀ x ∈ Set.Ioo a (a + (N : ℝ)), HasDerivAt D (E x) x)
    (hElower : ∀ x ∈ Set.Ioo a (a + (N : ℝ)), lam ≤ E x)
    (hband : ∀ n ∈ s,
      lower ≤ D (a + (n : ℝ)) ∧ D (a + (n : ℝ)) ≤ upper) :
    (s.card : ℝ) ≤ 1 + (upper - lower) / lam := by
  have hsep : ∀ m ∈ s, ∀ n ∈ s, m < n →
      lam * ((n - m : ℕ) : ℝ) ≤
        D (a + (n : ℝ)) - D (a + (m : ℝ)) := by
    intro m hm n hn hmn
    have hmN : m ≤ N := by
      have := Finset.mem_range.mp (hsupport hm)
      omega
    have hnN : n ≤ N := by
      have := Finset.mem_range.mp (hsupport hn)
      omega
    have hmR : 0 ≤ (m : ℝ) := by positivity
    have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    let x := a + (m : ℝ)
    let y := a + (n : ℝ)
    have hxy : x < y := by
      have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
      dsimp [x, y]
      nlinarith
    have hxLower : a ≤ x := by dsimp [x]; nlinarith
    have hyUpper : y ≤ a + (N : ℝ) := by dsimp [y]; nlinarith
    have hsub : Set.Icc x y ⊆ Set.Icc a (a + (N : ℝ)) := by
      intro t ht
      constructor
      · exact le_trans hxLower ht.1
      · exact ht.2.trans hyUpper
    have hDloc : ContinuousOn D (Set.Icc x y) := hDcont.mono hsub
    have hDderivLoc : ∀ t ∈ Set.Ioo x y, HasDerivAt D (E t) t := by
      intro t ht
      apply hDderiv t
      constructor
      · exact lt_of_le_of_lt hxLower ht.1
      · exact lt_of_lt_of_le ht.2 hyUpper
    have hElowerLoc : ∀ t ∈ Set.Ioo x y, lam ≤ E t := by
      intro t ht
      apply hElower t
      constructor
      · exact lt_of_le_of_lt hxLower ht.1
      · exact lt_of_lt_of_le ht.2 hyUpper
    have hgap := secondDerivative_separation_local hxy hDloc hDderivLoc hElowerLoc
    have hrealGap : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
      rw [Nat.cast_sub (by omega)]
    dsimp [x, y] at hgap
    rw [show a + (n : ℝ) - (a + (m : ℝ)) = (n : ℝ) - (m : ℝ) by ring] at hgap
    rw [hrealGap]
    exact hgap
  have hwidth : lower ≤ upper := by
    obtain ⟨n, hn⟩ := hs
    exact (hband n hn).1.trans (hband n hn).2
  exact finset_card_le_one_add_width_div_of_separation s
    (fun n => D (a + (n : ℝ))) lower upper lam hs hlam
    hwidth hband hsep

/-- Mathlib's closed form for every iterated derivative of a real power,
rewritten in the `iteratedDeriv` interface used by the exponential-sum
derivative test. -/
theorem iteratedDeriv_real_rpow (c x : ℝ) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => t ^ c) x =
      (descPochhammer ℝ j).eval c * x ^ (c - j) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

/-- Constant scaling commutes with iterated differentiation of a real power. -/
theorem iteratedDeriv_scaled_real_rpow (a c x : ℝ) (j : ℕ) (hx : x ≠ 0) :
    iteratedDeriv j (fun t : ℝ => a * t ^ c) x =
      a * ((descPochhammer ℝ j).eval c * x ^ (c - j)) := by
  rw [iteratedDeriv_const_mul a (Real.contDiffAt_rpow_const (Or.inl hx))]
  rw [iteratedDeriv_real_rpow]

/-- The explicit half-open monomial derivative model agrees with Mathlib's
iterated derivative on the positive half-line. -/
theorem scaledRealMonomialDerivative_eq_iteratedDeriv {a c t : ℝ} (k : ℕ)
    (ht : t ≠ 0) :
    scaledRealMonomialDerivative a c k t =
      iteratedDeriv k (fun z : ℝ => a * z ^ c) t := by
  simpa [scaledRealMonomialDerivative, mul_assoc] using
    (iteratedDeriv_scaled_real_rpow a c t k ht).symm

/-- The falling-factorial coefficient is the product of the successive
derivative factors. -/
theorem descPochhammer_eval_eq_prod (c : ℝ) (j : ℕ) :
    (descPochhammer ℝ j).eval c = ∏ h ∈ Finset.range j, (c - (h : ℝ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [descPochhammer_succ_eval, ih, Finset.prod_range_succ]

/-- Nonintegrality prevents any derivative factor in the falling factorial
from vanishing. -/
theorem descPochhammer_eval_ne_zero {c : ℝ} (hc : NonIntegral c) (j : ℕ) :
    (descPochhammer ℝ j).eval c ≠ 0 := by
  rw [descPochhammer_eval_eq_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro h hh
  apply sub_ne_zero.mpr
  intro heq
  exact hc (h : ℤ) (by exact_mod_cast heq)

/-- On a dyadic interval, a negative real power is bounded by its two
endpoint values. -/
theorem real_rpow_dyadic_bounds {q P x : ℝ} (hP : 0 < P) (hPx : P ≤ x)
    (hx2 : x ≤ 2 * P) (hq : q ≤ 0) :
    (2 * P) ^ q ≤ x ^ q ∧ x ^ q ≤ P ^ q := by
  constructor
  · exact Real.rpow_le_rpow_of_nonpos (by linarith) hx2 hq
  · exact Real.rpow_le_rpow_of_nonpos hP hPx hq

/-- The ratio between the endpoint powers on a dyadic interval is exactly
`2^(j-c)`, as in the blueprint's derivative-test application. -/
theorem real_rpow_dyadic_endpoint_ratio (P c j : ℝ) (hP : 0 < P) :
    P ^ (c - j) = (2 : ℝ) ^ (j - c) * (2 * P) ^ (c - j) := by
  have hexp : j - c = -(c - j) := by ring
  rw [hexp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) (le_of_lt hP)]
  have hpow : (2 : ℝ) ^ (c - j) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp [hpow]

/-- The exact jth derivative of a scaled monomial is controlled on a dyadic
interval by the endpoint powers used in the derivative-test application. -/
theorem abs_iteratedDeriv_scaled_real_rpow_bounds (a c P x : ℝ) (j : ℕ)
    (hP : 0 < P) (hPx : P ≤ x) (hx2 : x ≤ 2 * P)
    (hcj : c < j) :
    |a| * |(descPochhammer ℝ j).eval c| * (2 * P) ^ (c - j) ≤
        |iteratedDeriv j (fun t : ℝ => a * t ^ c) x| ∧
      |iteratedDeriv j (fun t : ℝ => a * t ^ c) x| ≤
        |a| * |(descPochhammer ℝ j).eval c| * P ^ (c - j) := by
  have hx : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hP hPx)
  have hq : c - (j : ℝ) ≤ 0 := by exact sub_nonpos.mpr (by exact_mod_cast hcj.le)
  have hpow := real_rpow_dyadic_bounds hP hPx hx2 hq
  rw [iteratedDeriv_scaled_real_rpow a c x j hx]
  have hfactor : 0 ≤ |a| * |(descPochhammer ℝ j).eval c| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hformula : |a * ((descPochhammer ℝ j).eval c * x ^ (c - j))| =
      |a| * |(descPochhammer ℝ j).eval c| * x ^ (c - j) := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le hP hPx) _)]
    ring
  rw [hformula]
  constructor
  · exact mul_le_mul_of_nonneg_left hpow.1 hfactor
  · exact mul_le_mul_of_nonneg_left hpow.2 hfactor

/-- The monomial's jth derivative satisfies the exact two-sided variation
bound on a dyadic interval, with ratio `2^(j-c)`. -/
theorem abs_iteratedDeriv_scaled_real_rpow_between (a c P x : ℝ) (j : ℕ)
    (hP : 0 < P) (hPx : P ≤ x) (hx2 : x ≤ 2 * P) (hcj : c < j) :
    |a| * |(descPochhammer ℝ j).eval c| * (2 * P) ^ (c - j) ≤
        |iteratedDeriv j (fun t : ℝ => a * t ^ c) x| ∧
      |iteratedDeriv j (fun t : ℝ => a * t ^ c) x| ≤
        (2 : ℝ) ^ (j - c) *
          (|a| * |(descPochhammer ℝ j).eval c| * (2 * P) ^ (c - j)) := by
  have hbounds := abs_iteratedDeriv_scaled_real_rpow_bounds
    a c P x j hP hPx hx2 hcj
  constructor
  · exact hbounds.1
  · calc
      |iteratedDeriv j (fun t : ℝ => a * t ^ c) x|
          ≤ |a| * |(descPochhammer ℝ j).eval c| * P ^ (c - j) := hbounds.2
      _ = (2 : ℝ) ^ (j - c) *
          (|a| * |(descPochhammer ℝ j).eval c| * (2 * P) ^ (c - j)) := by
            rw [real_rpow_dyadic_endpoint_ratio P c j hP]
            ring

theorem boundaryPhase_derivative_bounds_on_interval
    (c K a L : ℝ) (j : ℕ) (h : ℤ)
    (hK : 0 < K) (hKa : K ≤ a) (hUpper : a + L ≤ 2 * K)
    (hcj : c < (j : ℝ)) {t : ℝ} (ht : t ∈ Set.Ioc a (a + L)) :
    |(h : ℝ)| * |(descPochhammer ℝ j).eval c| * (2 * K) ^ (c - j) ≤
        |iteratedDeriv j (fun x : ℝ => (h : ℝ) * x ^ c) t| ∧
      |iteratedDeriv j (fun x : ℝ => (h : ℝ) * x ^ c) t| ≤
        (2 : ℝ) ^ (j - c) *
          (|(h : ℝ)| * |(descPochhammer ℝ j).eval c| * (2 * K) ^ (c - j)) := by
  have htK : K ≤ t := le_trans hKa ht.1.le
  have ht2 : t ≤ 2 * K := le_trans ht.2 hUpper
  exact abs_iteratedDeriv_scaled_real_rpow_between
    (h : ℝ) c K t j hK htK ht2 hcj

theorem scaledRealMonomialHalfOpenData_derivative_bounds
    (c K a L : ℝ) (j : ℕ) (h : ℤ)
    (hK : 0 < K) (hKa : K ≤ a) (hL : 0 < L)
    (hUpper : a + L ≤ 2 * K) (hcj : c < (j : ℝ))
    {t : ℝ} (ht : t ∈ Set.Ioc a (a + L)) :
    |(h : ℝ)| * |(descPochhammer ℝ j).eval c| * (2 * K) ^ (c - j) ≤
        |(scaledRealMonomialHalfOpenData (h : ℝ) c a L j
          (lt_of_lt_of_le hK hKa) hL).derivative j t| ∧
      |(scaledRealMonomialHalfOpenData (h : ℝ) c a L j
          (lt_of_lt_of_le hK hKa) hL).derivative j t| ≤
        (2 : ℝ) ^ (j - c) *
          (|(h : ℝ)| * |(descPochhammer ℝ j).eval c| * (2 * K) ^ (c - j)) := by
  let data := scaledRealMonomialHalfOpenData (h : ℝ) c a L j
    (lt_of_lt_of_le hK hKa) hL
  have htpos : 0 < t := lt_trans (lt_of_lt_of_le hK hKa) ht.1
  have hmodel : data.derivative j t =
      iteratedDeriv j (fun x : ℝ => (h : ℝ) * x ^ c) t := by
    dsimp [data, scaledRealMonomialHalfOpenData]
    exact scaledRealMonomialDerivative_eq_iteratedDeriv j (ne_of_gt htpos)
  rw [hmodel]
  exact boundaryPhase_derivative_bounds_on_interval
    c K a L j h hK hKa hUpper hcj ht

/-- For a nonzero amplitude and nonintegral exponent, the dyadic lower
derivative scale is strictly positive. -/
theorem scaled_real_rpow_derivative_scale_pos {a c P : ℝ} (j : ℕ)
    (ha : a ≠ 0) (hc : NonIntegral c) (hP : 0 < P) :
    0 < |a| * |(descPochhammer ℝ j).eval c| * (2 * P) ^ (c - j) := by
  apply mul_pos
  · apply mul_pos
    · exact abs_pos.mpr ha
    · exact abs_pos.mpr (descPochhammer_eval_ne_zero hc j)
  · exact Real.rpow_pos_of_pos (by linarith) _

/-- The von Mangoldt weight vanishes at the first averaging index. -/
theorem vonMangoldtWeight_one : vonMangoldtWeight 1 = 0 := by
  simp [vonMangoldtWeight]

/-- The von Mangoldt coefficient is bounded by the logarithm of its index. -/
theorem vonMangoldtWeight_le_log {n : ℕ} :
    vonMangoldtWeight n ≤ Real.log (n : ℝ) := by
  exact ArithmeticFunction.vonMangoldt_le_log

/-- Nonnegativity of the von Mangoldt coefficients. -/
theorem vonMangoldtWeight_nonneg (n : ℕ) : 0 ≤ vonMangoldtWeight n := by
  exact ArithmeticFunction.vonMangoldt_nonneg

/-- The first von Mangoldt average is zero because its only coefficient is
the vanishing weight at one. -/
theorem vonMangoldtAverage_one {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) :
    vonMangoldtAverage S c f ⟨1, Nat.succ_pos 0⟩ = 0 := by
  funext x
  simp [vonMangoldtAverage, weightedAverage]

/-- The total von Mangoldt weight up to a positive integer is at most the
number of terms times the logarithm of the endpoint. -/
theorem vonMangoldtWeight_sum_le_size_mul_log (N : Scale) :
    (∑ n ∈ Finset.Icc 1 N.1, vonMangoldtWeight n) ≤
      (N.1 : ℝ) * Real.log (N.1 : ℝ) := by
  calc
    (∑ n ∈ Finset.Icc 1 N.1, vonMangoldtWeight n) ≤
        ∑ _n ∈ Finset.Icc 1 N.1, Real.log (N.1 : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn' := Finset.mem_Icc.mp hn
          have hnPos : (0 : ℝ) < (n : ℝ) := by
            exact_mod_cast Nat.zero_lt_of_lt hn'.1
          have hnN : (n : ℝ) ≤ (N.1 : ℝ) := by exact_mod_cast hn'.2
          exact (vonMangoldtWeight_le_log (n := n)).trans
            (Real.log_le_log hnPos hnN)
    _ = (N.1 : ℝ) * Real.log (N.1 : ℝ) := by
      simp [Finset.sum_const, Nat.card_Icc]

/-- The average scalar von Mangoldt coefficient is bounded by the logarithm
of the averaging scale. -/
theorem normalizedVonMangoldtWeight_sum_le_log (N : Scale) :
    (N.1 : ℝ)⁻¹ * (∑ n ∈ Finset.Icc 1 N.1, vonMangoldtWeight n) ≤
      Real.log (N.1 : ℝ) := by
  have hNpos : (0 : ℝ) < (N.1 : ℝ) := by exact_mod_cast N.2
  have hsum := vonMangoldtWeight_sum_le_size_mul_log N
  calc
    (N.1 : ℝ)⁻¹ * (∑ n ∈ Finset.Icc 1 N.1, vonMangoldtWeight n) ≤
        (N.1 : ℝ)⁻¹ * ((N.1 : ℝ) * Real.log (N.1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hNpos))
    _ = Real.log (N.1 : ℝ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]

/-- For a nonnegative power, the power of a sum is bounded by the exact
`2^q` factor times the larger powered summand. -/
theorem real_rpow_add_le_two_rpow_max {a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    (a + b) ^ q ≤ (2 : ℝ) ^ q * max (a ^ q) (b ^ q) := by
  have hmax : 0 ≤ max a b := le_max_of_le_left ha
  have hsum : a + b ≤ 2 * max a b := by
    have ha' : a ≤ max a b := le_max_left a b
    have hb' : b ≤ max a b := le_max_right a b
    nlinarith
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ a + b) hsum hq
  have hmul : (2 * max a b) ^ q = (2 : ℝ) ^ q * (max a b) ^ q := by
    rw [Real.mul_rpow (by norm_num) hmax]
  have hmaxpow : (max a b) ^ q = max (a ^ q) (b ^ q) := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, max_eq_right (Real.rpow_le_rpow ha hab hq)]
    · rw [max_eq_left hba, max_eq_left (Real.rpow_le_rpow hb hba hq)]
  calc
    (a + b) ^ q ≤ (2 * max a b) ^ q := hpow
    _ = (2 : ℝ) ^ q * max (a ^ q) (b ^ q) := by rw [hmul, hmaxpow]

/-- For a power at most one half, `2^q≤√2`, giving the convenient
`√2` version of `real_rpow_add_le_two_rpow_max`. -/
theorem real_rpow_add_le_sqrt_two_max {a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    (a + b) ^ q ≤ Real.sqrt 2 * max (a ^ q) (b ^ q) := by
  have h2q : (2 : ℝ) ^ q ≤ Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hqhalf
  have hpow := real_rpow_add_le_two_rpow_max ha hb hq hqhalf
  exact hpow.trans (mul_le_mul_of_nonneg_right h2q
    (le_max_of_le_left (Real.rpow_nonneg ha q)))

/-- Raise a nonnegative two-term estimate to a small real power while
retaining its exact `2^q` loss and the common coefficient. -/
theorem real_rpow_scaled_add_le_two_rpow
    {T C a b q : ℝ} (hT : T ≤ C * (a + b))
    (hTnonneg : 0 ≤ T) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    T ^ q ≤ (2 : ℝ) ^ q * C ^ q * max (a ^ q) (b ^ q) := by
  have huppernonneg : 0 ≤ C * (a + b) := by positivity
  have hmono := Real.rpow_le_rpow hTnonneg hT hq
  have hmul : (C * (a + b)) ^ q = C ^ q * (a + b) ^ q := by
    rw [Real.mul_rpow hC (by positivity)]
  rw [hmul] at hmono
  have hadd := real_rpow_add_le_two_rpow_max ha hb hq hqhalf
  calc
    T ^ q ≤ C ^ q * (a + b) ^ q := hmono
    _ ≤ C ^ q * ((2 : ℝ) ^ q * max (a ^ q) (b ^ q)) :=
      mul_le_mul_of_nonneg_left hadd (Real.rpow_nonneg hC q)
    _ = (2 : ℝ) ^ q * C ^ q * max (a ^ q) (b ^ q) := by ring

/-- The first correlation summand's dyadic coefficient becomes `D` after
combining the exact factor `2^q` with `2^(h+1)`. -/
theorem derivativeCorrelation_dyadic_coefficient (h : ℕ) (q : ℝ) :
    (2 : ℝ) ^ q * ((2 : ℝ) ^ (h + 1)) ^ q =
      ((2 : ℝ) ^ (h + 2)) ^ q := by
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  congr 1
  rw [pow_succ]
  ring

/-- Reindex the second correlation coefficient from `h` to the paper's
derivative order `d=h+2`. -/
theorem derivativeCorrelation_threeHalves_coefficient (h : ℕ) :
    (2 : ℝ) * (2 / 3 : ℝ) ^ h =
      (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ (h + 2) := by
  rw [pow_add]
  norm_num
  ring

/-- Raising a square root to a real power halves the exponent. -/
theorem real_sqrt_rpow_identity {P q : ℝ} (hP : 0 < P) :
    (Real.sqrt P) ^ q = P ^ (q / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hP)]
  congr 1
  ring

/-- The reciprocal square root in the first correlation term contributes
the exact negative half exponent. -/
theorem real_inv_sqrt_rpow_identity {P q : ℝ} (hP : 0 < P) :
    (1 / Real.sqrt P) ^ q = P ^ (-q / 2) := by
  have hsqrt : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hexp : -q / 2 = -(q / 2) := by ring
  rw [Real.div_rpow (by norm_num) (le_of_lt hsqrt), Real.one_rpow,
    real_sqrt_rpow_identity hP, one_div, hexp,
    Real.rpow_neg (le_of_lt hP) (q / 2)]

/-- The first terminal correlation summand combines its dyadic factors
exactly, leaving the inverse normalizer at exponent `-q/2`. -/
theorem derivativeCorrelation_first_normalizer_term
    {h : ℕ} {C P q : ℝ} (hC : 0 ≤ C) (hP : 0 < P) :
    (2 : ℝ) ^ q * C ^ q * (((2 : ℝ) ^ (h + 1)) / Real.sqrt P) ^ q =
      (((2 : ℝ) ^ (h + 2)) * C) ^ q * P ^ (-q / 2) := by
  have hsqrt : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hpowP : P ^ (q / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hP _)
  rw [Real.div_rpow (by positivity) (le_of_lt hsqrt),
    real_sqrt_rpow_identity hP]
  calc
    (2 : ℝ) ^ q * C ^ q * (((2 : ℝ) ^ (h + 1)) ^ q / P ^ (q / 2)) =
        C ^ q * ((2 : ℝ) ^ q * ((2 : ℝ) ^ (h + 1)) ^ q) /
          P ^ (q / 2) := by
      field_simp [hpowP]
    _ = C ^ q * (((2 : ℝ) ^ (h + 2)) ^ q / P ^ (q / 2)) := by
      rw [derivativeCorrelation_dyadic_coefficient]
      ring
    _ = C ^ q * (((2 : ℝ) ^ (h + 2)) ^ q * P ^ (-q / 2)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hP) (q / 2)]
      rw [show -q / 2 = -(q / 2) by ring]
    _ = (((2 : ℝ) ^ (h + 2)) * C) ^ q * P ^ (-q / 2) := by
      calc
        C ^ q * (((2 : ℝ) ^ (h + 2)) ^ q * P ^ (-q / 2)) =
            ((2 : ℝ) ^ (h + 2)) ^ q * C ^ q * P ^ (-q / 2) := by ring
        _ = (((2 : ℝ) ^ (h + 2)) * C) ^ q * P ^ (-q / 2) := by
          rw [← Real.mul_rpow (by positivity) hC]

/-- A squared positive base raised to half an exponent recovers the
original real power. -/
theorem real_rpow_square_half {x q : ℝ} (hx : 0 ≤ x) :
    (x ^ 2) ^ (q / 2) = x ^ q := by
  rw [← Real.rpow_natCast_mul hx 2 (q / 2)]
  congr 1
  ring

/-- The square-root form of the exact coefficient defining `M` in the
optimized derivative estimate. -/
theorem derivativeCorrelation_M_coefficient_identity
    {A B D Y lam : ℝ} (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hY : 0 < Y) (hlam : 0 < lam) :
    (A ^ 2 * (B⁻¹) ^ 2 * D ^ 2 * (Y⁻¹) ^ 2 * lam⁻¹) ^ (2 / D) =
      (A * D / (B * Y * Real.sqrt lam)) ^ (4 / D) := by
  let X : ℝ := A * D / (B * Y * Real.sqrt lam)
  have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt (le_of_lt hlam)
  have hbase :
      A ^ 2 * (B⁻¹) ^ 2 * D ^ 2 * (Y⁻¹) ^ 2 * lam⁻¹ = X ^ 2 := by
    dsimp [X]
    field_simp [ne_of_gt hB, ne_of_gt hY, ne_of_gt hsqrt, ne_of_gt hlam]
    rw [hsq]
  have hX : 0 < X := by dsimp [X]; positivity
  have hexp : 2 / D = (4 / D) / 2 := by
    field_simp [ne_of_gt hD]
    ring
  rw [hbase, hexp]
  exact real_rpow_square_half (le_of_lt hX)

/-- The first powered correlation summand is exactly the `M P₊^(-2/D)`
term in the optimized estimate. -/
theorem derivativeCorrelation_first_M_term
    {h d : ℕ} {D q A B Y lam P M : ℝ}
    (hhd : h + 2 = d) (hD : D = (2 : ℝ) ^ d) (hDpos : 0 < D)
    (hq : q = 4 / D) (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y)
    (hlam : 0 < lam) (hP : 0 < P)
    (hM : Real.sqrt 2 * M =
      (A ^ 2 * (B⁻¹) ^ 2 * D ^ 2 * (Y⁻¹) ^ 2 * lam⁻¹) ^ (2 / D)) :
    (2 : ℝ) ^ q * (A / (B * Y * Real.sqrt lam)) ^ q *
        (((2 : ℝ) ^ (h + 1)) / Real.sqrt P) ^ q =
      Real.sqrt 2 * M * P ^ (-2 / D) := by
  let C : ℝ := A / (B * Y * Real.sqrt lam)
  have hC : 0 < C := by dsimp [C]; positivity
  have hdyad : (2 : ℝ) ^ (h + 2) = D := by
    rw [hD]
    congr 1
  have hcoef : (D * C) ^ q = Real.sqrt 2 * M := by
    have hbase : D * C = A * D / (B * Y * Real.sqrt lam) := by
      dsimp [C]
      field_simp [ne_of_gt hB, ne_of_gt hY, ne_of_gt hlam]
    rw [hbase, hq]
    rw [← derivativeCorrelation_M_coefficient_identity hA hB hDpos hY hlam]
    exact hM.symm
  have hexp : -q / 2 = -2 / D := by
    rw [hq]
    field_simp [ne_of_gt hDpos]
    ring
  calc
    (2 : ℝ) ^ q * (A / (B * Y * Real.sqrt lam)) ^ q *
        (((2 : ℝ) ^ (h + 1)) / Real.sqrt P) ^ q =
      (((2 : ℝ) ^ (h + 2)) * C) ^ q * P ^ (-q / 2) := by
        simpa [C] using derivativeCorrelation_first_normalizer_term
          (hC.le) hP
    _ = Real.sqrt 2 * M * P ^ (-2 / D) := by
      rw [hdyad, hcoef, hexp]

/-- The square-root form of the exact coefficient defining `N` in the
optimized derivative estimate. -/
theorem derivativeCorrelation_N_coefficient_identity
    {d : ℕ} {A B D lam Lambda : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hD : 0 < D) (hlam : 0 < lam) (hLambda : 0 < Lambda) :
    ((9 / 2 : ℝ) * (A / B) * (2 / 3 : ℝ) ^ d * Lambda /
        Real.sqrt lam) ^ (4 / D) =
      ((81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d) *
        Lambda ^ 2 * lam⁻¹) ^ (2 / D) := by
  let X : ℝ := (9 / 2 : ℝ) * (A / B) * (2 / 3 : ℝ) ^ d * Lambda /
    Real.sqrt lam
  have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt (le_of_lt hlam)
  have hpow : ((2 / 3 : ℝ) ^ d) ^ 2 = (2 / 3 : ℝ) ^ (2 * d) := by
    rw [← pow_mul]
    congr 1
    omega
  have hbase :
      (81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d) *
        Lambda ^ 2 * lam⁻¹ = X ^ 2 := by
    dsimp [X]
    field_simp [ne_of_gt hB, ne_of_gt hsqrt, ne_of_gt hlam]
    rw [hpow, hsq]
    ring
  have hX : 0 < X := by dsimp [X]; positivity
  have hexp : 2 / D = (4 / D) / 2 := by
    field_simp [ne_of_gt hD]
    ring
  rw [hbase, hexp]
  exact (real_rpow_square_half (le_of_lt hX)).symm

/-- The second terminal correlation summand combines the `2^q` loss,
the three-halves factor, and the square-root normalizer exactly. -/
theorem derivativeCorrelation_second_normalizer_term
    {h : ℕ} {C Y Lambda P q : ℝ} (hC : 0 ≤ C) (hY : 0 < Y)
    (hLambda : 0 < Lambda) (hP : 0 < P) :
    (2 : ℝ) ^ q * C ^ q *
        ((2 / 3 : ℝ) ^ h * Y * Lambda * Real.sqrt P) ^ q =
      ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ (h + 2) * C * Y * Lambda) ^ q *
        P ^ (q / 2) := by
  let U : ℝ := (2 / 3 : ℝ) ^ h * Y * Lambda
  let K : ℝ := (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ (h + 2) * C * Y * Lambda
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsqrt : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hbase : (2 : ℝ) * C * U = K := by
    dsimp [U, K]
    calc
      2 * C * ((2 / 3 : ℝ) ^ h * Y * Lambda) =
          (2 * (2 / 3 : ℝ) ^ h) * C * Y * Lambda := by ring
      _ = (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ (h + 2) * C * Y * Lambda := by
        rw [derivativeCorrelation_threeHalves_coefficient]
  have hmul : (2 * C * (U * Real.sqrt P)) ^ q =
      (2 : ℝ) ^ q * C ^ q * (U * Real.sqrt P) ^ q := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) hC]
  calc
    (2 : ℝ) ^ q * C ^ q *
        ((2 / 3 : ℝ) ^ h * Y * Lambda * Real.sqrt P) ^ q =
      (2 * C * (U * Real.sqrt P)) ^ q := by
        rw [← hmul]
    _ = (K * Real.sqrt P) ^ q := by
      congr 1
      rw [← mul_assoc, hbase]
    _ = K ^ q * P ^ (q / 2) := by
      rw [Real.mul_rpow hK (le_of_lt hsqrt), real_sqrt_rpow_identity hP]

/-- The second powered correlation summand is exactly the `N P^(2/D)`
term in the optimized estimate. -/
theorem derivativeCorrelation_second_N_term
    {h d : ℕ} {D q A B Y lam Lambda P N : ℝ}
    (hhd : h + 2 = d) (hD : D = (2 : ℝ) ^ d) (hDpos : 0 < D)
    (hq : q = 4 / D) (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y)
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (hP : 0 < P)
    (hN : Real.sqrt 2 * N =
      ((81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d) *
        Lambda ^ 2 * lam⁻¹) ^ (2 / D)) :
    (2 : ℝ) ^ q * (A / (B * Y * Real.sqrt lam)) ^ q *
        ((2 / 3 : ℝ) ^ h * Y * Lambda * Real.sqrt P) ^ q =
      Real.sqrt 2 * N * P ^ (2 / D) := by
  let C : ℝ := A / (B * Y * Real.sqrt lam)
  let K : ℝ := (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ (h + 2) * C * Y * Lambda
  have hC : 0 < C := by dsimp [C]; positivity
  have hKbase : K =
      (9 / 2 : ℝ) * (A / B) * (2 / 3 : ℝ) ^ d * Lambda / Real.sqrt lam := by
    dsimp [K, C]
    rw [hhd]
    field_simp [ne_of_gt hB, ne_of_gt hY, ne_of_gt hlam]
  have hK : K ^ q = Real.sqrt 2 * N := by
    rw [hKbase, hq]
    rw [derivativeCorrelation_N_coefficient_identity
      hA hB hDpos hlam hLambda]
    exact hN.symm
  have hexp : q / 2 = 2 / D := by
    rw [hq]
    field_simp [ne_of_gt hDpos]
    ring
  calc
    (2 : ℝ) ^ q * (A / (B * Y * Real.sqrt lam)) ^ q *
        ((2 / 3 : ℝ) ^ h * Y * Lambda * Real.sqrt P) ^ q =
      K ^ q * P ^ (q / 2) := by
        have hgeneric := derivativeCorrelation_second_normalizer_term
          (h := h) (q := q) (C := C) hC.le hY hLambda hP
        simpa [C, K] using hgeneric
    _ = Real.sqrt 2 * N * P ^ (2 / D) := by rw [hK, hexp]

/-- The two exact powered terms from the correlation estimate combine into
the terminal M/N maximum used by the optimized derivative bound. -/
theorem derivativeCorrelation_terminal_MN_bound
    {h d : ℕ} {D q Y lam Lambda B T Pplus P M N : ℝ}
    (hd : 3 ≤ d) (hhd : h + 2 = d) (hD : D = (2 : ℝ) ^ d)
    (hDpos : 0 < D) (hq : q = 4 / D) (hB : 0 < B) (hY : (d : ℝ) < Y)
    (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hTnonneg : 0 ≤ T) (hPplus : 0 < Pplus) (hP : 0 < P)
    (hcorr : T ≤ (14 / 5 : ℝ) / (Y * Real.sqrt lam) *
      ((2 : ℝ) ^ (h + 1) / Real.sqrt Pplus +
        (2 / 3 : ℝ) ^ h * Y * Lambda * Real.sqrt P))
    (hM : Real.sqrt 2 * M =
      ((14 / 5 : ℝ) ^ 2 * (B⁻¹) ^ 2 * D ^ 2 * (Y⁻¹) ^ 2 * lam⁻¹) ^ (2 / D))
    (hN : Real.sqrt 2 * N =
      ((81 / 4 : ℝ) * ((14 / 5 : ℝ) / B) ^ 2 *
        (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) :
    (T / B) ^ q ≤ Real.sqrt 2 *
      max (M * Pplus ^ (-2 / D)) (N * P ^ (2 / D)) := by
  let A : ℝ := 14 / 5
  let C : ℝ := A / (Y * Real.sqrt lam)
  let Cbar : ℝ := C / B
  let u : ℝ := (2 : ℝ) ^ (h + 1) / Real.sqrt Pplus
  let v : ℝ := (2 / 3 : ℝ) ^ h * Y * Lambda * Real.sqrt P
  have hD8 : 8 ≤ D := by
    rw [hD]
    calc
      (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hqpos : 0 < q := by rw [hq]; positivity
  have hqhalf : q ≤ 1 / 2 := by
    rw [hq]
    rw [div_le_iff₀ hDpos]
    nlinarith
  have hAspos : 0 < A := by dsimp [A]; norm_num
  have hYpos : 0 < Y := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hCbar : 0 < Cbar := by dsimp [Cbar]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hnormalized : T / B ≤ Cbar * (u + v) := by
    have hmul := mul_le_mul_of_nonneg_left hcorr (le_of_lt (inv_pos.mpr hB))
    calc
      T / B = B⁻¹ * T := by ring
      _ ≤ B⁻¹ * ((14 / 5 : ℝ) / (Y * Real.sqrt lam) *
          ((2 : ℝ) ^ (h + 1) / Real.sqrt Pplus +
            (2 / 3 : ℝ) ^ h * Y * Lambda * Real.sqrt P)) := hmul
      _ = Cbar * (u + v) := by
        dsimp [Cbar, C, u, v, A]
        field_simp [ne_of_gt hB, ne_of_gt hYpos, ne_of_lt hlam,
          ne_of_lt hPplus]
  have hscaled := real_rpow_scaled_add_le_two_rpow
    hnormalized (div_nonneg hTnonneg (le_of_lt hB)) (le_of_lt hCbar)
    hu hv (le_of_lt hqpos) hqhalf
  have hCnorm : Cbar = (14 / 5 : ℝ) / (B * Y * Real.sqrt lam) := by
    dsimp [Cbar, C, A]
    field_simp [ne_of_gt hB, ne_of_gt hYpos, ne_of_lt hlam]
  have hMterm := derivativeCorrelation_first_M_term
    (h := h) (d := d) (D := D) (q := q) (A := 14 / 5) (B := B)
    (Y := Y) (lam := lam) (P := Pplus) (M := M)
    hhd hD hDpos hq (by norm_num) hB hYpos hlam hPplus hM
  have hNterm := derivativeCorrelation_second_N_term
    (h := h) (d := d) (D := D) (q := q) (A := 14 / 5) (B := B)
    (Y := Y) (lam := lam) (Lambda := Lambda) (P := P) (N := N)
    hhd hD hDpos hq (by norm_num) hB hYpos hlam hLambda hP hN
  have huTerm : (2 : ℝ) ^ q * Cbar ^ q * u ^ q =
      Real.sqrt 2 * M * Pplus ^ (-2 / D) := by
    rw [hCnorm]
    simpa [u] using hMterm
  have hvTerm : (2 : ℝ) ^ q * Cbar ^ q * v ^ q =
      Real.sqrt 2 * N * P ^ (2 / D) := by
    rw [hCnorm]
    simpa [v] using hNterm
  have hfactor : 0 ≤ (2 : ℝ) ^ q * Cbar ^ q := by positivity
  have hmax : (2 : ℝ) ^ q * Cbar ^ q * max (u ^ q) (v ^ q) =
      max ((2 : ℝ) ^ q * Cbar ^ q * u ^ q)
          ((2 : ℝ) ^ q * Cbar ^ q * v ^ q) := by
    rcases le_total (u ^ q) (v ^ q) with huv | hvu
    · rw [max_eq_right huv,
        max_eq_right (mul_le_mul_of_nonneg_left huv hfactor)]
    · rw [max_eq_left hvu,
        max_eq_left (mul_le_mul_of_nonneg_left hvu hfactor)]
  have hsqrt2 : 0 ≤ Real.sqrt 2 := le_of_lt (Real.sqrt_pos.mpr (by norm_num))
  have htargetMax :
      max (Real.sqrt 2 * M * Pplus ^ (-2 / D))
          (Real.sqrt 2 * N * P ^ (2 / D)) =
        Real.sqrt 2 * max (M * Pplus ^ (-2 / D)) (N * P ^ (2 / D)) := by
    rcases le_total (M * Pplus ^ (-2 / D)) (N * P ^ (2 / D)) with hMN | hNM
    · have hterm : Real.sqrt 2 * M * Pplus ^ (-2 / D) ≤
          Real.sqrt 2 * N * P ^ (2 / D) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hMN hsqrt2
      rw [max_eq_right hterm, max_eq_right hMN]
      ring
    · have hterm : Real.sqrt 2 * N * P ^ (2 / D) ≤
          Real.sqrt 2 * M * Pplus ^ (-2 / D) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hNM hsqrt2
      rw [max_eq_left hterm, max_eq_left hNM]
      ring
  calc
    (T / B) ^ q ≤ (2 : ℝ) ^ q * Cbar ^ q * max (u ^ q) (v ^ q) := hscaled
    _ = Real.sqrt 2 * max (M * Pplus ^ (-2 / D)) (N * P ^ (2 / D)) := by
      rw [hmax, huTerm, hvTerm, htargetMax]

/-- The terminal correlation power is exactly the terminal candidate in the
repeated-Weyl list when the number of shifts is `d - 2`. -/
theorem derivativeCorrelation_terminal_candidate_identity
    {h d : ℕ} {D q T : ℝ}
    (hhd : h + 2 = d) (hD : D = (2 : ℝ) ^ d)
    (hq : q = 4 / D) (hT : 0 ≤ T) :
    T ^ (((2 : ℝ) ^ (0 + h))⁻¹) *
        derivativeWeylConstant ^ (-((2 : ℝ) ^ (0 + h))⁻¹) =
      (T / derivativeWeylConstant) ^ q := by
  have hexp : ((2 : ℝ) ^ (0 + h))⁻¹ = q := by
    rw [Nat.zero_add, hq, hD]
    rw [show (2 : ℝ) ^ d = 4 * (2 : ℝ) ^ h by
      rw [← hhd, show h + 2 = h + 1 + 1 by omega, pow_add, pow_succ]
      norm_num
      ring]
    field_simp
    <;> norm_num
  rw [hexp, Real.div_rpow hT (le_of_lt derivativeWeylConstant_pos)]
  simp only [div_eq_mul_inv, ← Real.rpow_neg
    (le_of_lt derivativeWeylConstant_pos)]

/-- Feed a normalized terminal correlation estimate into the exact final
candidate of the repeated-Weyl list. -/
theorem derivativeWeylPowerCandidates_max_le_of_terminal_correlation
    {h : ℕ} (bounds : List ℕ) (T R : ℝ)
    (hlen : bounds.length = h) (hR : 0 ≤ R)
    (hcoords : derivativeWeylCoordinateBounds 0 bounds R)
    (hT : 0 ≤ T)
    (hterminal : (T / derivativeWeylConstant) ^
      (4 / (2 : ℝ) ^ (h + 2)) ≤ R) :
    realListMaximum (derivativeWeylPowerCandidates 0 bounds T) ≤ R := by
  have hid := derivativeCorrelation_terminal_candidate_identity
    (h := h) (d := h + 2) (D := (2 : ℝ) ^ (h + 2))
    (q := 4 / (2 : ℝ) ^ (h + 2)) (T := T) rfl rfl rfl hT
  have hterminal' :
      T ^ (((2 : ℝ) ^ (0 + bounds.length))⁻¹) *
        derivativeWeylConstant ^ (-((2 : ℝ) ^ (0 + bounds.length))⁻¹) ≤ R := by
    rw [hlen]
    rw [← hid] at hterminal
    simpa [Nat.zero_add] using hterminal
  exact derivativeWeylPowerCandidates_max_le 0 bounds T R hR hcoords hterminal'

theorem derivativeWeylCoordinateBounds_mono
    (depth : ℕ) (bounds : List ℕ) {R S : ℝ} (hRS : R ≤ S)
    (hcoords : derivativeWeylCoordinateBounds depth bounds R) :
    derivativeWeylCoordinateBounds depth bounds S := by
  induction bounds generalizing depth with
  | nil => trivial
  | cons H rest ih =>
      rcases hcoords with ⟨hhead, htail⟩
      exact ⟨hhead.trans hRS, ih (depth + 1) htail⟩

/-- Allocate real shift sizes, floor them to the exact integer shifts, and
bound every repeated-Weyl candidate by the larger of the allocation and
terminal-correlation bounds. -/
theorem derivativeWeyl_allocated_candidates_bound
    (h : ℕ) (hh : 1 ≤ h) {V ξ T Rterminal : ℝ}
    (hV : 1 ≤ V) (hξ : 1 ≤ ξ) (hξV : ξ ≤ V ^ h)
    (hT : 0 ≤ T)
    (hterminal : (T / derivativeWeylConstant) ^
      (4 / (2 : ℝ) ^ (h + 2)) ≤ Rterminal) :
    ∃ allocation : ℕ → ℝ,
      (∀ i ∈ Finset.range h, allocation i ∈ Set.Icc 1 V) ∧
      (∏ i ∈ Finset.range h, allocation i) = ξ ∧
      realListMaximum
        (derivativeWeylPowerCandidates 0
          (List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊) T) ≤
        max
          (Real.sqrt 2 * max
            (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
            (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
          Rterminal := by
  obtain ⟨allocation, hallocRange, hallocProd, hcoords⟩ :=
    derivativeWeylCoordinateBounds_from_allocation h hh hV hξ hξV
  let Rcoord : ℝ := Real.sqrt 2 * max
    (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
    (V ^ (-4 / (2 : ℝ) ^ (h + 2)))
  have hRcoord : 0 ≤ Rcoord := by
    dsimp [Rcoord]
    positivity
  have hcoords' : derivativeWeylCoordinateBounds 0
      (List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊)
      (max Rcoord Rterminal) :=
    derivativeWeylCoordinateBounds_mono 0 _ (le_max_left _ _) hcoords
  have hterminal' : (T / derivativeWeylConstant) ^
      (4 / (2 : ℝ) ^ (h + 2)) ≤ max Rcoord Rterminal :=
    hterminal.trans (le_max_right _ _)
  have hlenBounds :
      (List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊).length = h := by simp
  refine ⟨allocation, hallocRange, hallocProd, ?_⟩
  simpa [Rcoord] using
    derivativeWeylPowerCandidates_max_le_of_terminal_correlation
      (h := h) (bounds := List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊)
      (T := T) (R := max Rcoord Rterminal) hlenBounds
      (le_trans hRcoord (le_max_left _ _)) hcoords' hT hterminal'

/-- Combine the exact correlation estimate with the allocation lemma and the
repeated-Weyl candidate maximum. -/
theorem derivativeCorrelation_allocated_candidates_bound
    {h d : ℕ} {D q Y lam Lambda B T Pplus P M N V ξ : ℝ}
    (hd : 3 ≤ d) (hhd : h + 2 = d) (hD : D = (2 : ℝ) ^ d)
    (hDpos : 0 < D) (hq : q = 4 / D) (hBpos : 0 < B)
    (hB : B = derivativeWeylConstant) (hY : (d : ℝ) < Y)
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (hT : 0 ≤ T)
    (hPplus : 0 < Pplus) (hP : 0 < P)
    (hcorr : T ≤ (14 / 5 : ℝ) / (Y * Real.sqrt lam) *
      ((2 : ℝ) ^ (h + 1) / Real.sqrt Pplus +
        (2 / 3 : ℝ) ^ h * Y * Lambda * Real.sqrt P))
    (hM : Real.sqrt 2 * M =
      ((14 / 5 : ℝ) ^ 2 * (B⁻¹) ^ 2 * D ^ 2 *
        (Y⁻¹) ^ 2 * lam⁻¹) ^ (2 / D))
    (hN : Real.sqrt 2 * N =
      ((81 / 4 : ℝ) * ((14 / 5 : ℝ) / B) ^ 2 *
        (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D))
    (hh : 1 ≤ h) (hV : 1 ≤ V) (hξ : 1 ≤ ξ) (hξV : ξ ≤ V ^ h) :
    ∃ allocation : ℕ → ℝ,
      (∀ i ∈ Finset.range h, allocation i ∈ Set.Icc 1 V) ∧
      (∏ i ∈ Finset.range h, allocation i) = ξ ∧
      realListMaximum
        (derivativeWeylPowerCandidates 0
          (List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊) T) ≤
        max
          (Real.sqrt 2 * max
            (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
            (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
          (Real.sqrt 2 * max (M * Pplus ^ (-2 / D)) (N * P ^ (2 / D))) := by
  have hterminal := derivativeCorrelation_terminal_MN_bound
    (h := h) (d := d) (D := D) (q := q) (Y := Y) (lam := lam)
    (Lambda := Lambda) (B := B) (T := T) (Pplus := Pplus) (P := P)
    (M := M) (N := N) hd hhd hD hDpos hq hBpos hY hlam hLambda hT
    hPplus hP hcorr hM hN
  have hexp : q = 4 / (2 : ℝ) ^ (h + 2) := by
    rw [hq, hD, ← hhd]
  have hterminal' : (T / derivativeWeylConstant) ^
      (4 / (2 : ℝ) ^ (h + 2)) ≤
        Real.sqrt 2 * max (M * Pplus ^ (-2 / D)) (N * P ^ (2 / D)) := by
    simpa [hB, hexp] using hterminal
  exact derivativeWeyl_allocated_candidates_bound h hh hV hξ hξV hT hterminal'

theorem realShiftTotal_ofFn_floor_le
    (h : ℕ) (scales : Fin h → ℝ) (hscales : ∀ i, 0 ≤ scales i) :
    realShiftTotal (List.ofFn fun i : Fin h => ⌊scales i⌋₊) ≤
      ∑ i : Fin h, scales i := by
  have hsum : realShiftTotal
      (List.ofFn fun i : Fin h => ⌊scales i⌋₊) =
      ∑ i : Fin h, (⌊scales i⌋₊ : ℝ) := by
    simp [realShiftTotal, ← list_map_eq_flatMap_singleton, List.sum_ofFn]
  rw [hsum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.floor_le (hscales i)

theorem realShiftTotal_of_allocated_floors_le
    (h : ℕ) (V Y : ℝ) (allocation : ℕ → ℝ)
    (halloc : ∀ i ∈ Finset.range h, allocation i ∈ Set.Icc 1 V)
    (hcapacity : (h : ℝ) * V ≤ Y) :
    realShiftTotal (List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊) ≤ Y := by
  have hscales : ∀ i : Fin h, 0 ≤ allocation i.val := by
    intro i
    have hi : i.val ∈ Finset.range h := Finset.mem_range.mpr i.isLt
    exact le_trans (by norm_num) (halloc i.val hi).1
  have hfloor := realShiftTotal_ofFn_floor_le h
    (fun i : Fin h => allocation i.val) hscales
  have hsum : (∑ i : Fin h, allocation i.val) ≤ (h : ℝ) * V := by
    calc
      (∑ i : Fin h, allocation i.val) ≤ ∑ _i : Fin h, V := by
        apply Finset.sum_le_sum
        intro i hi
        have hii : i.val ∈ Finset.range h := Finset.mem_range.mpr i.isLt
        exact (halloc i.val hii).2
      _ = (h : ℝ) * V := by simp
  exact hfloor.trans (hsum.trans hcapacity)

theorem realIntegerInterval_phase_sum_div_le_of_candidates
    (f : ℝ → ℝ) (x Y : ℝ) (bounds : List ℕ) (R : ℝ)
    (hY : 1 ≤ Y) (hpos : ∀ H ∈ bounds, 0 < H)
    (hTotal : realShiftTotal bounds ≤ Y)
    (hCandidates : realListMaximum
      (derivativeWeylPowerCandidates 0 bounds
        (averagedIteratedCorrelation f x Y bounds)) ≤ R) :
    ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ / Y ≤
      derivativeWeylConstant * R := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  calc
    ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ / Y =
        averagedIteratedCorrelation f x Y [] :=
      (averagedIteratedCorrelation_nil f x Y hYpos).symm
    _ ≤ derivativeWeylConstant * realListMaximum
        (derivativeWeylPowerCandidates 0 bounds
          (averagedIteratedCorrelation f x Y bounds)) :=
      repeatedWeyl_difference_bound f x Y bounds hY hpos hTotal
    _ ≤ derivativeWeylConstant * R :=
      mul_le_mul_of_nonneg_left hCandidates
        (le_of_lt derivativeWeylConstant_pos)

theorem averagedIteratedCorrelation_nonneg
    (f : ℝ → ℝ) (x Y : ℝ) (bounds : List ℕ)
    (hY : 0 < Y) (hpos : ∀ H ∈ bounds, 0 < H) :
    0 ≤ averagedIteratedCorrelation f x Y bounds := by
  have hPpos := realShiftNormalizer_pos bounds hpos
  rw [averagedIteratedCorrelation_eq_normalized_sum f x Y bounds hY hPpos]
  apply mul_nonneg (inv_nonneg.mpr (le_of_lt hPpos))
  apply Finset.sum_nonneg
  intro shifts hshifts
  exact div_nonneg (norm_nonneg _) (le_of_lt hY)

theorem realIntegerInterval_phase_sum_div_le_two
    (f : ℝ → ℝ) (x Y : ℝ) (hY : 1 ≤ Y) :
    ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ / Y ≤ 2 := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hnorm : ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ ≤
      (realIntegerInterval x Y).card := by
    calc
      ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ ≤
          ∑ n ∈ realIntegerInterval x Y, ‖realExponentialPhase f n‖ := norm_sum_le _ _
      _ = (realIntegerInterval x Y).card := by
        simp [norm_realExponentialPhase]
  have hcard := realIntegerInterval_card_le x Y hY
  calc
    ‖∑ n ∈ realIntegerInterval x Y, realExponentialPhase f n‖ / Y ≤
        ((realIntegerInterval x Y).card : ℝ) / Y :=
      div_le_div_of_nonneg_right hnorm (le_of_lt hYpos)
    _ ≤ (Y + 1) / Y := div_le_div_of_nonneg_right hcard (le_of_lt hYpos)
    _ ≤ 2 := by
      rw [div_le_iff₀ hYpos]
      nlinarith

/-- The paper's derivative-correlation and Weyl steps for one fixed real
shift allocation, with its exact floored integer shifts used throughout. -/
theorem derivativeCorrelation_sum_bound_of_allocation
    {x Y lam Lambda : ℝ} {d h : ℕ}
    (data : HalfOpenCkData x Y d)
    (hd : 3 ≤ d) (hhd : h + 2 = d) (hY : (d : ℝ) < Y)
    (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y), lam ≤ data.derivative d t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y), data.derivative d t ≤ Lambda)
    (hh : 1 ≤ h) (V ξ : ℝ)
    (hV : 1 ≤ V) (hξ : 1 ≤ ξ) (hξV : ξ ≤ V ^ h)
    (hcapacity : (h : ℝ) * V ≤ Y)
    (allocation : ℕ → ℝ)
    (hallocRange : ∀ i ∈ Finset.range h,
      allocation i ∈ Set.Icc 1 V)
    (hallocProd : (∏ i ∈ Finset.range h, allocation i) = ξ)
    (hallocLower : ∀ i ∈ Finset.range h,
      min (ξ ^ ((2 : ℝ) ^ (i + 1) /
          ((2 : ℝ) ^ (h + 1) - 2)))
          (V ^ ((2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ h)) ≤ allocation i) :
    let bounds : List ℕ :=
      List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊
    let D : ℝ := (2 : ℝ) ^ d
    let M : ℝ :=
      (((14 / 5 : ℝ) ^ 2 * derivativeWeylConstant⁻¹ ^ 2 * D ^ 2 *
        Y⁻¹ ^ 2 * lam⁻¹) ^ (2 / D)) / Real.sqrt 2
    let N : ℝ :=
      (((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
        (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) /
        Real.sqrt 2
    ‖∑ n ∈ realIntegerInterval x Y,
      realExponentialPhase (data.derivative 0) n‖ / Y ≤
      derivativeWeylConstant * max
        (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
        (Real.sqrt 2 * max
          (M * (realShiftPlusNormalizer bounds) ^ (-2 / D))
          (N * (realShiftNormalizer bounds) ^ (2 / D))) := by
  let bounds : List ℕ :=
    List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊
  let D : ℝ := (2 : ℝ) ^ d
  let q : ℝ := 4 / D
  let Pplus : ℝ := realShiftPlusNormalizer bounds
  let P : ℝ := realShiftNormalizer bounds
  let M : ℝ :=
    (((14 / 5 : ℝ) ^ 2 * derivativeWeylConstant⁻¹ ^ 2 * D ^ 2 *
      Y⁻¹ ^ 2 * lam⁻¹) ^ (2 / D)) / Real.sqrt 2
  let N : ℝ :=
    (((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
      (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) /
      Real.sqrt 2
  have hYpos : 0 < Y := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (show 0 < d by omega)
    linarith
  have hlen : bounds.length + 2 = d := by
    simp [bounds, hhd]
  have hpos : ∀ H ∈ bounds, 0 < H := by
    intro H hH
    have hmem : ∃ i : Fin h, ⌊allocation i.val⌋₊ = H := by
      simpa [bounds] using hH
    rcases hmem with ⟨i, rfl⟩
    have hi : i.val ∈ Finset.range h := Finset.mem_range.mpr i.isLt
    have hfloor : 1 ≤ ⌊allocation i.val⌋₊ :=
      (Nat.one_le_floor_iff _).mpr (hallocRange i.val hi).1
    omega
  have htotal : realShiftTotal bounds ≤ Y := by
    dsimp [bounds]
    exact realShiftTotal_of_allocated_floors_le h V Y allocation
      hallocRange hcapacity
  have hcorrelation := derivativeCorrelationBound data hd hY bounds hlen
    hpos htotal hlower hupper hlam
  have hPpos : 0 < P := by
    dsimp [P]
    exact realShiftNormalizer_pos bounds hpos
  have hPplusPos : 0 < Pplus := by
    dsimp [Pplus]
    exact realShiftPlusNormalizer_pos bounds hpos
  let T : ℝ := averagedIteratedCorrelation (data.derivative 0) x Y bounds
  have hT : 0 ≤ T := by
    dsimp [T]
    exact averagedIteratedCorrelation_nonneg (data.derivative 0) x Y bounds
      hYpos hpos
  have hcorr : T ≤ (14 / 5 : ℝ) / (Y * Real.sqrt lam) *
      ((2 : ℝ) ^ (h + 1) / Real.sqrt Pplus +
        (2 / 3 : ℝ) ^ h * Y * Lambda * Real.sqrt P) := by
    dsimp [T, Pplus, P]
    simpa [bounds, hhd] using hcorrelation
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hD : D = (2 : ℝ) ^ d := rfl
  have hq : q = 4 / D := rfl
  have hM : Real.sqrt 2 * M =
      ((14 / 5 : ℝ) ^ 2 * (derivativeWeylConstant⁻¹) ^ 2 * D ^ 2 *
        (Y⁻¹) ^ 2 * lam⁻¹) ^ (2 / D) := by
    dsimp [M]
    have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hsqrt]
  have hN : Real.sqrt 2 * N =
      ((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
        (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D) := by
    dsimp [N]
    have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hsqrt]
  have hterminal := derivativeCorrelation_terminal_MN_bound
    (h := h) (d := d) (D := D) (q := q) (Y := Y) (lam := lam)
    (Lambda := Lambda) (B := derivativeWeylConstant) (T := T)
    (Pplus := Pplus) (P := P) (M := M) (N := N)
    hd hhd hD hDpos hq derivativeWeylConstant_pos hY hlam hLambda hT
    hPplusPos hPpos hcorr hM hN
  let scales : Fin h → ℝ := fun i => allocation i.val
  let Rcoord : ℝ := Real.sqrt 2 * max
    (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
    (V ^ (-4 / (2 : ℝ) ^ (h + 2)))
  have hcoord : ∀ i : Fin h,
      (⌊scales i⌋₊ : ℝ) ^ (-((2 : ℝ) ^ (i.val + 1))⁻¹) ≤ Rcoord := by
    intro i
    have hi : i.val ∈ Finset.range h := Finset.mem_range.mpr i.isLt
    have hscale := (hallocRange i.val hi).1
    have hmin := hallocLower i.val hi
    simpa [scales, Rcoord] using
      derivativeWeyl_allocated_coordinate_bound h i hV hξ hscale hmin
  have hcoord' : ∀ i : Fin h,
      (⌊scales i⌋₊ : ℝ) ^ (-((2 : ℝ) ^ (0 + i.val + 1))⁻¹) ≤ Rcoord := by
    intro i
    simpa [Nat.zero_add] using hcoord i
  have hcoords := derivativeWeylCoordinateBounds_ofFn_floor 0 h scales
    Rcoord hcoord'
  have hexp : q = 4 / (2 : ℝ) ^ (h + 2) := by
    rw [hq, hD, ← hhd]
  have hterminal' : (T / derivativeWeylConstant) ^
      (4 / (2 : ℝ) ^ (h + 2)) ≤
      Real.sqrt 2 * max (M * Pplus ^ (-2 / D)) (N * P ^ (2 / D)) := by
    simpa [hexp] using hterminal
  have hlenBounds : bounds.length = h := by simp [bounds]
  have hmax := derivativeWeylPowerCandidates_max_le_of_terminal_correlation
    (h := h) bounds T
    (max Rcoord
      (Real.sqrt 2 * max (M * Pplus ^ (-2 / D)) (N * P ^ (2 / D))))
    hlenBounds
    (le_trans (by dsimp [Rcoord]; positivity) (le_max_left _ _))
    (derivativeWeylCoordinateBounds_mono 0 bounds (le_max_left _ _) hcoords)
    hT
    (hterminal'.trans (le_max_right _ _))
  have hsum := realIntegerInterval_phase_sum_div_le_of_candidates
    (data.derivative 0) x Y bounds
    (max Rcoord
      (Real.sqrt 2 * max (M * Pplus ^ (-2 / D)) (N * P ^ (2 / D))))
    (by
      have hYlower : (1 : ℝ) ≤ Y := by
        have hdle : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      exact hYlower)
    hpos htotal hmax
  simpa [bounds, D, M, N, Pplus, P, Rcoord] using hsum

/-- Replace the floor-shift normalizers by the exact real allocation product
using `P ≤ ξ ≤ P₊`, retaining the paper's powers and constants. -/
theorem derivativeCorrelation_sum_bound_of_allocation_product
    {x Y lam Lambda : ℝ} {d h : ℕ}
    (data : HalfOpenCkData x Y d)
    (hd : 3 ≤ d) (hhd : h + 2 = d) (hY : (d : ℝ) < Y)
    (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y), lam ≤ data.derivative d t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y), data.derivative d t ≤ Lambda)
    (hh : 1 ≤ h) (V ξ : ℝ)
    (hV : 1 ≤ V) (hξ : 1 ≤ ξ) (hξV : ξ ≤ V ^ h)
    (hcapacity : (h : ℝ) * V ≤ Y)
    (allocation : ℕ → ℝ)
    (hallocRange : ∀ i ∈ Finset.range h,
      allocation i ∈ Set.Icc 1 V)
    (hallocProd : (∏ i ∈ Finset.range h, allocation i) = ξ)
    (hallocLower : ∀ i ∈ Finset.range h,
      min (ξ ^ ((2 : ℝ) ^ (i + 1) /
          ((2 : ℝ) ^ (h + 1) - 2)))
          (V ^ ((2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ h)) ≤ allocation i) :
    let D : ℝ := (2 : ℝ) ^ d
    let M : ℝ :=
      (((14 / 5 : ℝ) ^ 2 * derivativeWeylConstant⁻¹ ^ 2 * D ^ 2 *
        Y⁻¹ ^ 2 * lam⁻¹) ^ (2 / D)) / Real.sqrt 2
    let N : ℝ :=
      (((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
        (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) /
        Real.sqrt 2
    ‖∑ n ∈ realIntegerInterval x Y,
      realExponentialPhase (data.derivative 0) n‖ / Y ≤
      derivativeWeylConstant * max
        (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
        (Real.sqrt 2 * max
          (M * ξ ^ (-2 / D))
          (N * ξ ^ (2 / D))) := by
  let bounds : List ℕ :=
    List.ofFn fun i : Fin h => ⌊allocation i.val⌋₊
  let D : ℝ := (2 : ℝ) ^ d
  let M : ℝ :=
    (((14 / 5 : ℝ) ^ 2 * derivativeWeylConstant⁻¹ ^ 2 * D ^ 2 *
      Y⁻¹ ^ 2 * lam⁻¹) ^ (2 / D)) / Real.sqrt 2
  let N : ℝ :=
    (((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
      (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) /
      Real.sqrt 2
  let scales : Fin h → ℝ := fun i => allocation i.val
  have hscalePos : ∀ i : Fin h, 1 ≤ scales i := by
    intro i
    have hi : i.val ∈ Finset.range h := Finset.mem_range.mpr i.isLt
    exact (hallocRange i.val hi).1
  have hfiniteProd : (∏ i : Fin h, scales i) = ξ := by
    have hindex : (∏ i : Fin h, scales i) =
        ∏ i ∈ Finset.range h, allocation i := by
      simpa [scales] using (Finset.prod_range (fun i : ℕ => allocation i)).symm
    exact hindex.trans hallocProd
  have hPle : realShiftNormalizer bounds ≤ ξ := by
    rw [← hfiniteProd]
    exact realShiftNormalizer_ofFn_floor_le h scales hscalePos
  have hξlePplus : ξ ≤ realShiftPlusNormalizer bounds := by
    rw [← hfiniteProd]
    exact realShiftPlusNormalizer_ofFn_floor_ge h scales hscalePos
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hboundsPos : ∀ H ∈ bounds, 0 < H := by
    intro H hH
    have hmem : ∃ i : Fin h, ⌊allocation i.val⌋₊ = H := by
      simpa [bounds] using hH
    rcases hmem with ⟨i, rfl⟩
    have hi : i.val ∈ Finset.range h := Finset.mem_range.mpr i.isLt
    have hfloor : 1 ≤ ⌊allocation i.val⌋₊ :=
      (Nat.one_le_floor_iff _).mpr (hallocRange i.val hi).1
    omega
  have hPpos := realShiftNormalizer_pos bounds hboundsPos
  have hpowNeg :
      realShiftPlusNormalizer bounds ^ (-2 / D) ≤ ξ ^ (-2 / D) :=
    Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hξ)
      hξlePplus (div_nonpos_of_nonpos_of_nonneg (by norm_num) (le_of_lt hDpos))
  have hpowPos :
      realShiftNormalizer bounds ^ (2 / D) ≤ ξ ^ (2 / D) :=
    Real.rpow_le_rpow (le_of_lt hPpos) hPle
      (div_nonneg (by norm_num) (le_of_lt hDpos))
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hNnonneg : 0 ≤ N := by
    dsimp [N]
    positivity
  have htermM := mul_le_mul_of_nonneg_left hpowNeg hMnonneg
  have htermN := mul_le_mul_of_nonneg_left hpowPos hNnonneg
  have htermMax :
      max (M * realShiftPlusNormalizer bounds ^ (-2 / D))
          (N * realShiftNormalizer bounds ^ (2 / D)) ≤
        max (M * ξ ^ (-2 / D)) (N * ξ ^ (2 / D)) :=
    max_le_max htermM htermN
  have htermScaled : Real.sqrt 2 *
      max (M * realShiftPlusNormalizer bounds ^ (-2 / D))
        (N * realShiftNormalizer bounds ^ (2 / D)) ≤
      Real.sqrt 2 * max (M * ξ ^ (-2 / D)) (N * ξ ^ (2 / D)) :=
    mul_le_mul_of_nonneg_left htermMax (Real.sqrt_nonneg _)
  have hfixed := derivativeCorrelation_sum_bound_of_allocation
    (data := data) hd hhd hY hlam hLambda hlower hupper hh V ξ hV hξ hξV
    hcapacity allocation hallocRange hallocProd hallocLower
  have hcombined :
      max (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
        (Real.sqrt 2 * max
          (M * realShiftPlusNormalizer bounds ^ (-2 / D))
          (N * realShiftNormalizer bounds ^ (2 / D))) ≤
      max (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
        (Real.sqrt 2 * max (M * ξ ^ (-2 / D)) (N * ξ ^ (2 / D))) :=
    max_le_max (le_refl _) htermScaled
  have hcombined' := mul_le_mul_of_nonneg_left hcombined
    (le_of_lt derivativeWeylConstant_pos)
  exact hfixed.trans (by simpa [bounds, D, M, N] using hcombined')

/-- The optimized correlation/Weyl estimate for every scale product
`0 < ξ ≤ V^h`: use the exact allocation for `ξ ≥ 1` and the paper's trivial
integer-count bound when `ξ < 1`. -/
theorem derivativeCorrelation_sum_bound_for_xi
    {x Y lam Lambda : ℝ} {d h : ℕ}
    (data : HalfOpenCkData x Y d)
    (hd : 3 ≤ d) (hhd : h + 2 = d) (hY : (d : ℝ) < Y)
    (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y), lam ≤ data.derivative d t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y), data.derivative d t ≤ Lambda)
    (hh : 1 ≤ h) (V ξ : ℝ)
    (hV : 1 ≤ V) (hξ : 0 < ξ) (hξV : ξ ≤ V ^ h)
    (hcapacity : (h : ℝ) * V ≤ Y) :
    let D : ℝ := (2 : ℝ) ^ d
    let M : ℝ :=
      (((14 / 5 : ℝ) ^ 2 * derivativeWeylConstant⁻¹ ^ 2 * D ^ 2 *
        Y⁻¹ ^ 2 * lam⁻¹) ^ (2 / D)) / Real.sqrt 2
    let N : ℝ :=
      (((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
        (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) /
        Real.sqrt 2
    ‖∑ n ∈ realIntegerInterval x Y,
      realExponentialPhase (data.derivative 0) n‖ / Y ≤
      derivativeWeylConstant * max
        (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
        (Real.sqrt 2 * max
          (M * ξ ^ (-2 / D))
          (N * ξ ^ (2 / D))) := by
  let D : ℝ := (2 : ℝ) ^ d
  let M : ℝ :=
    (((14 / 5 : ℝ) ^ 2 * derivativeWeylConstant⁻¹ ^ 2 * D ^ 2 *
      Y⁻¹ ^ 2 * lam⁻¹) ^ (2 / D)) / Real.sqrt 2
  let N : ℝ :=
    (((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
      (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) /
      Real.sqrt 2
  by_cases hξone : 1 ≤ ξ
  · obtain ⟨allocation, hallocRange, hallocProd, hallocLower⟩ :=
      derivativeShiftAllocation h hh hV hξone hξV
    exact derivativeCorrelation_sum_bound_of_allocation_product
      data hd hhd hY hlam hLambda hlower hupper hh V ξ hV hξone hξV
      hcapacity allocation hallocRange hallocProd hallocLower
  · have hξlt : ξ < 1 := lt_of_not_ge hξone
    have hYpos : 0 < Y := by
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast (show 0 < d by omega)
      linarith
    have hDpos : 0 < D := by dsimp [D]; positivity
    have hden : 0 < (2 : ℝ) ^ (h + 2) - 4 := by
      have hhpow : (8 : ℝ) ≤ (2 : ℝ) ^ (h + 2) := by
        calc
          (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
          _ ≤ (2 : ℝ) ^ (h + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have halpha : 0 < 2 / ((2 : ℝ) ^ (h + 2) - 4) :=
      div_pos (by norm_num) hden
    have hxiPow : 1 ≤ ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)) := by
      have hmono := Real.rpow_le_rpow_of_nonpos hξ (le_of_lt hξlt)
        (neg_nonpos.mpr halpha.le)
      have hexp : -(2 / ((2 : ℝ) ^ (h + 2) - 4)) =
          -2 / ((2 : ℝ) ^ (h + 2) - 4) := by ring
      rw [hexp] at hmono
      simpa using hmono
    have hinner : 1 ≤ max
        (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
        (Real.sqrt 2 * max (M * ξ ^ (-2 / D)) (N * ξ ^ (2 / D))) := by
      have hcoord : 1 ≤ max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))) :=
        le_trans hxiPow (le_max_left _ _)
      have hsqrt : 1 ≤ Real.sqrt 2 := le_of_lt Real.one_lt_sqrt_two
      have hscaled : 1 ≤ Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))) := by
        calc
          (1 : ℝ) ≤ 1 * 1 := by norm_num
          _ ≤ Real.sqrt 2 * max
              (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
              (V ^ (-4 / (2 : ℝ) ^ (h + 2))) :=
            mul_le_mul hsqrt hcoord (by norm_num) (by positivity)
      exact hscaled.trans (le_max_left _ _)
    have hBtwo : 2 ≤ derivativeWeylConstant := by
      rw [derivativeWeylConstant]
      nlinarith [Real.one_lt_sqrt_two]
    have hlarge : 2 ≤ derivativeWeylConstant * max
        (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
        (Real.sqrt 2 * max (M * ξ ^ (-2 / D)) (N * ξ ^ (2 / D))) := by
      calc
        (2 : ℝ) ≤ derivativeWeylConstant := hBtwo
        _ ≤ derivativeWeylConstant * max
            (Real.sqrt 2 * max
              (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
              (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
            (Real.sqrt 2 * max (M * ξ ^ (-2 / D)) (N * ξ ^ (2 / D))) := by
          simpa using mul_le_mul_of_nonneg_left hinner
            (le_of_lt derivativeWeylConstant_pos)
    have htrivial := realIntegerInterval_phase_sum_div_le_two
      (data.derivative 0) x Y (by
        have hdle : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith)
    exact htrivial.trans hlarge

theorem derivativeBalance_cap_term_le_V_term
    (h : ℕ) (hh : 1 ≤ h) {V : ℝ} (hV : 1 ≤ V) :
    (V ^ h) ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)) ≤
      V ^ (-4 / (2 : ℝ) ^ (h + 2)) := by
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hpowD : (2 : ℝ) ^ (h + 2) = 4 * (2 : ℝ) ^ h := by
    rw [show h + 2 = h + 1 + 1 by omega, pow_add, pow_succ, pow_succ]
    norm_num
    ring
  have hden : 0 < (2 : ℝ) ^ (h + 2) - 4 := by
    rw [hpowD]
    have h2h : 2 ≤ (2 : ℝ) ^ h := by
      calc
        (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
        _ ≤ (2 : ℝ) ^ h := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hexp : (h : ℝ) * (-2 / ((2 : ℝ) ^ (h + 2) - 4)) ≤
      -4 / (2 : ℝ) ^ (h + 2) := by
    rw [hpowD]
    have hn : 0 < (2 : ℝ) ^ h := by positivity
    have hden' : 0 < 4 * (2 : ℝ) ^ h - 4 := by
      have h2h : 2 ≤ (2 : ℝ) ^ h := by
        calc
          (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
          _ ≤ (2 : ℝ) ^ h := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have hdenR : 0 < 4 * (2 : ℝ) ^ h := by positivity
    have hnumer : (h : ℝ) * (2 : ℝ) ^ h ≥
        2 * ((2 : ℝ) ^ h - 1) := by
      by_cases htwo : h = 1
      · subst h
        norm_num
      · have htwoNat : 2 ≤ h := by omega
        have hfactor : 0 ≤ ((h : ℝ) - 2) * (2 : ℝ) ^ h :=
          mul_nonneg (by exact_mod_cast (show 0 ≤ h - 2 by omega)) (by positivity)
        nlinarith
    have hleft : (h : ℝ) * (-2 / (4 * (2 : ℝ) ^ h - 4)) =
        (-2 * (h : ℝ)) / (4 * (2 : ℝ) ^ h - 4) := by ring
    rw [hleft]
    apply (div_le_div_iff₀ hden' hdenR).2
    nlinarith [hnumer]
  rw [← Real.rpow_natCast V h, ← Real.rpow_mul (le_of_lt hVpos)]
  exact Real.rpow_le_rpow_of_exponent_le hV hexp

theorem derivativeBalance_four_term_envelope
    (h : ℕ) (hh : 1 ≤ h) {V M N S : ℝ}
    (hV : 1 ≤ V) (hM : 0 < M) (hN : 0 < N)
    (hbound : ∀ ξ : ℝ, 0 < ξ → ξ ≤ V ^ h →
      S ≤ derivativeWeylConstant * max
        (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
        (Real.sqrt 2 * max
          (M * ξ ^ (-2 / (2 : ℝ) ^ (h + 2)))
          (N * ξ ^ (2 / (2 : ℝ) ^ (h + 2))))) :
    let α : ℝ := 2 / ((2 : ℝ) ^ (h + 2) - 4)
    let β : ℝ := 2 / (2 : ℝ) ^ (h + 2)
    let Z : ℝ := V ^ h
    let Q : ℝ := max (Z ^ (-α))
      (max (M * Z ^ (-β))
        (max (Real.sqrt (M * N)) (N ^ (α / (α + β)))))
    let W : ℝ := V ^ (-4 / (2 : ℝ) ^ (h + 2))
    S ≤ derivativeWeylConstant * (Real.sqrt 2 * max Q W) := by
  let α : ℝ := 2 / ((2 : ℝ) ^ (h + 2) - 4)
  let β : ℝ := 2 / (2 : ℝ) ^ (h + 2)
  let Z : ℝ := V ^ h
  let Q : ℝ := max (Z ^ (-α))
    (max (M * Z ^ (-β))
      (max (Real.sqrt (M * N)) (N ^ (α / (α + β)))))
  let W : ℝ := V ^ (-4 / (2 : ℝ) ^ (h + 2))
  have hden : 0 < (2 : ℝ) ^ (h + 2) - 4 := by
    have hpow : (8 : ℝ) ≤ (2 : ℝ) ^ (h + 2) := by
      calc
        (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ (2 : ℝ) ^ (h + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hα : 0 < α := by dsimp [α]; exact div_pos (by norm_num) hden
  have hβ : 0 < β := by dsimp [β]; positivity
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  obtain ⟨ξ, hξ, hξZ, hbalanced⟩ :=
    derivativeBalanceThreePowers M N Z α β hM hN hZpos hα hβ
  have hbalanceQ :
      max (ξ ^ (-α)) (max (M * ξ ^ (-β)) (N * ξ ^ β)) ≤ Q := by
    simpa [Q, Z] using hbalanced
  have hparts := max_le_iff.mp hbalanceQ
  have hxiTerm : ξ ^ (-α) ≤ Q := hparts.1
  have hmnParts := max_le_iff.mp hparts.2
  have hmnTerm : max (M * ξ ^ (-β)) (N * ξ ^ β) ≤ Q := hparts.2
  have hnegα : -α = -2 / ((2 : ℝ) ^ (h + 2) - 4) := by
    dsimp [α]
    ring
  have hβ : β = 2 / (2 : ℝ) ^ (h + 2) := rfl
  have hnegβ : -β = -2 / (2 : ℝ) ^ (h + 2) := by
    rw [hβ]
    ring
  rw [hnegα] at hxiTerm
  rw [hnegβ, hβ] at hmnTerm
  have hqnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hcoordCmp :
      max (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))) ≤
        max Q (V ^ (-4 / (2 : ℝ) ^ (h + 2))) :=
    max_le_max hxiTerm (le_refl _)
  have hmnCmp :
      max (M * ξ ^ (-2 / (2 : ℝ) ^ (h + 2)))
          (N * ξ ^ (2 / (2 : ℝ) ^ (h + 2))) ≤
      max Q (V ^ (-4 / (2 : ℝ) ^ (h + 2))) :=
    le_trans hmnTerm (le_max_left _ _)
  have hcoordScaled := mul_le_mul_of_nonneg_left hcoordCmp hqnonneg
  have hmnScaled := mul_le_mul_of_nonneg_left hmnCmp hqnonneg
  have houter := max_le_max hcoordScaled hmnScaled
  have hxiBound := hbound ξ hξ (by simpa [Z] using hξZ)
  have hcoeff : 0 ≤ derivativeWeylConstant :=
    le_of_lt derivativeWeylConstant_pos
  have hfinal := mul_le_mul_of_nonneg_left houter hcoeff
  have hresult : S ≤ derivativeWeylConstant *
      (Real.sqrt 2 * max Q (V ^ (-4 / (2 : ℝ) ^ (h + 2)))) :=
    hxiBound.trans (by simpa using hfinal)
  simpa [Q, Z, W, α, β] using hresult

theorem derivativeBalance_M_cap_identity
    {A B Y lam : ℝ} {h d : ℕ} {D : ℝ}
    (hhd : h + 2 = d) (hDpos : 0 < D)
    (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) (hlam : 0 < lam) :
    ((A ^ 2 * (B⁻¹) ^ 2 * D ^ 2 * (Y⁻¹) ^ 2 * lam⁻¹) ^ (2 / D)) *
      (Y / (h : ℝ)) ^ (-2 * (h : ℝ) / D) =
    (A * D / B) ^ (4 / D) * (h : ℝ) ^ (2 * (h : ℝ) / D) *
      (lam * Y ^ d) ^ (-2 / D) := by
  have hcoef := derivativeCorrelation_M_coefficient_identity
    hA hB hDpos hY hlam
  by_cases hzero : h = 0
  · subst h
    have hd : d = 2 := by omega
    subst d
    have hzeroexp : (2 : ℝ) * 0 / D = 0 := by ring
    simp [hzeroexp]
    have hcoeffbase :
        A ^ 2 * (B ^ 2)⁻¹ * D ^ 2 * (Y ^ 2)⁻¹ * lam⁻¹ =
          (A * D / B) ^ 2 * (lam * Y ^ 2)⁻¹ := by
      field_simp [ne_of_gt hB, ne_of_gt hY, ne_of_gt hlam]
    rw [hcoeffbase, Real.mul_rpow (sq_nonneg (A * D / B))
      (inv_nonneg.mpr (le_of_lt (mul_pos hlam (pow_pos hY 2))))]
    have hhalf : (4 / D) / 2 = 2 / D := by
      field_simp [ne_of_gt hDpos]
      ring
    rw [← hhalf, real_rpow_square_half (x := A * D / B) (q := 4 / D)
      (le_of_lt (div_pos (mul_pos hA hDpos) hB))]
    rw [show -2 / D = -(2 / D) by ring, Real.rpow_neg_eq_inv_rpow]
    rw [hhalf]
  have hhpos : 0 < (h : ℝ) := by
    exact_mod_cast (show 0 < h by omega)
  let X : ℝ := A * D / (B * Y * Real.sqrt lam)
  have hXpos : 0 < X := by
    dsimp [X]
    positivity
  have hXsq : X ^ (4 / D) = (X ^ 2) ^ (2 / D) := by
    rw [show 4 / D = 2 * (2 / D) by ring,
      Real.rpow_mul (le_of_lt hXpos)]
    exact congrArg (fun t : ℝ => t ^ (2 / D)) (Real.rpow_natCast X 2)
  have hYdivPos : 0 < Y / (h : ℝ) := div_pos hY hhpos
  have hshiftPower :
      (Y / (h : ℝ)) ^ (-2 * (h : ℝ) / D) =
        (((h : ℝ) / Y) ^ h) ^ (2 / D) := by
    have hexp : -2 * (h : ℝ) / D = (h : ℝ) * (-2 / D) := by ring
    have hnegq : -2 / D = -(2 / D) := by ring
    rw [hexp, Real.rpow_mul (le_of_lt hYdivPos), Real.rpow_natCast,
      hnegq, Real.rpow_neg_eq_inv_rpow]
    have hinv : ((Y / (h : ℝ)) ^ h)⁻¹ = ((h : ℝ) / Y) ^ h := by
      rw [div_pow, div_pow]
      field_simp [ne_of_gt hY, ne_of_gt hhpos]
    rw [hinv]
  have hbase : X ^ 2 * (((h : ℝ) / Y) ^ h) =
      (A * D / B) ^ 2 * (h : ℝ) ^ h * (lam * Y ^ d)⁻¹ := by
    dsimp [X]
    rw [div_pow, div_pow]
    simp only [mul_pow]
    rw [Real.sq_sqrt (le_of_lt hlam), ← hhd]
    field_simp [ne_of_gt hB, ne_of_gt hY, ne_of_gt hlam]
    ring
  have haPos : 0 < A * D / B := div_pos (mul_pos hA hDpos) hB
  have hhpowPos : 0 < (h : ℝ) ^ h := pow_pos hhpos _
  have hlamYPos : 0 < lam * Y ^ d := mul_pos hlam (pow_pos hY _)
  have hfirst : (A * D / B) ^ (4 / D) =
      ((A * D / B) ^ 2) ^ (2 / D) := by
    rw [show 4 / D = 2 * (2 / D) by ring,
      Real.rpow_mul (le_of_lt haPos)]
    exact congrArg (fun t : ℝ => t ^ (2 / D)) (Real.rpow_natCast (A * D / B) 2)
  have hsecond : (h : ℝ) ^ (2 * (h : ℝ) / D) =
      ((h : ℝ) ^ h) ^ (2 / D) := by
    have hexp : 2 * (h : ℝ) / D = (h : ℝ) * (2 / D) := by ring
    rw [hexp, Real.rpow_mul (le_of_lt hhpos), Real.rpow_natCast]
  have hthird : (lam * Y ^ d) ^ (-2 / D) =
      ((lam * Y ^ d)⁻¹) ^ (2 / D) := by
    rw [show -2 / D = -(2 / D) by ring, Real.rpow_neg_eq_inv_rpow]
  calc
    _ = X ^ (4 / D) * (Y / (h : ℝ)) ^ (-2 * (h : ℝ) / D) := by
      rw [← hcoef]
    _ = (X ^ 2) ^ (2 / D) *
        (((h : ℝ) / Y) ^ h) ^ (2 / D) := by rw [hXsq, hshiftPower]
    _ = (X ^ 2 * (((h : ℝ) / Y) ^ h)) ^ (2 / D) := by
      rw [← Real.mul_rpow (sq_nonneg X) (pow_nonneg (div_nonneg
        (le_of_lt hhpos) (le_of_lt hY)) h)]
    _ = ((A * D / B) ^ 2 * (h : ℝ) ^ h * (lam * Y ^ d)⁻¹) ^ (2 / D) := by
      rw [hbase]
    _ = (A * D / B) ^ (4 / D) *
        (h : ℝ) ^ (2 * (h : ℝ) / D) *
          (lam * Y ^ d) ^ (-2 / D) := by
      rw [hfirst, hsecond, hthird]
      rw [← Real.mul_rpow (sq_nonneg (A * D / B)) hhpowPos.le]
      rw [← Real.mul_rpow (mul_nonneg (sq_nonneg (A * D / B))
        (pow_nonneg (le_of_lt hhpos) h)) (inv_nonneg.mpr (le_of_lt hlamYPos))]

/-- Exact conversion of the mixed balanced term `sqrt (M*N)` to the
coefficient `a'_d` and its paper normalization. -/
theorem derivativeBalance_mixed_sqrtMN_identity
    {A B Y lam Lambda D M N : ℝ} {d : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) (hlam : 0 < lam)
    (hLambda : 0 < Lambda) (hD : 0 < D)
    (hM : Real.sqrt 2 * M =
      (A ^ 2 * (B⁻¹) ^ 2 * D ^ 2 * (Y⁻¹) ^ 2 * lam⁻¹) ^ (2 / D))
    (hN : Real.sqrt 2 * N =
      ((81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d) *
        Lambda ^ 2 * lam⁻¹) ^ (2 / D)) :
    Real.sqrt 2 * Real.sqrt (M * N) =
      ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d * (A / B) ^ 2 * D *
        Lambda / (lam * Y)) ^ (2 / D) := by
  let mBase : ℝ := A ^ 2 * (B⁻¹) ^ 2 * D ^ 2 * (Y⁻¹) ^ 2 * lam⁻¹
  let nBase : ℝ :=
    (81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d) *
      Lambda ^ 2 * lam⁻¹
  let C : ℝ := (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d * (A / B) ^ 2 * D *
    Lambda / (lam * Y)
  have hmBase : 0 < mBase := by dsimp [mBase]; positivity
  have hnBase : 0 < nBase := by dsimp [nBase]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hprodNat : mBase * nBase = C ^ 2 := by
    dsimp [mBase, nBase, C]
    field_simp [ne_of_gt hB, ne_of_gt hY, ne_of_gt hlam]
    <;> ring_nf
  have hprod : mBase * nBase = C ^ 2 := hprodNat
  have hpower : 2 * M * N = C ^ (4 / D) := by
    have hmul :
        (Real.sqrt 2 * M) * (Real.sqrt 2 * N) =
          (mBase * nBase) ^ (2 / D) := by
      rw [hM, hN, ← Real.mul_rpow (le_of_lt hmBase) (le_of_lt hnBase)]
    have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * M * N = (Real.sqrt 2 * M) * (Real.sqrt 2 * N) := by
        calc
          2 * M * N = (Real.sqrt 2 * Real.sqrt 2) * M * N := by
            nth_rw 1 [← hsqrt2]
          _ = (Real.sqrt 2 * M) * (Real.sqrt 2 * N) := by ring
      _ = (mBase * nBase) ^ (2 / D) := hmul
      _ = (C ^ 2) ^ (2 / D) := by rw [hprod]
      _ = C ^ (4 / D) := by
        calc
          (C ^ 2) ^ (2 / D) = C ^ (2 * (2 / D)) :=
            (Real.rpow_natCast_mul (le_of_lt hC) 2 (2 / D)).symm
          _ = C ^ (4 / D) := by congr 1 <;> ring
  calc
    Real.sqrt 2 * Real.sqrt (M * N) = Real.sqrt (2 * (M * N)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (M * N)]
    _ = Real.sqrt (C ^ (4 / D)) := by rw [← hpower]; ring_nf
    _ = C ^ (2 / D) := by
      rw [Real.sqrt_eq_rpow]
      calc
        (C ^ (4 / D)) ^ (1 / 2) = C ^ ((4 / D) * (1 / 2)) :=
          (Real.rpow_mul (le_of_lt hC) (4 / D) (1 / 2)).symm
        _ = C ^ (2 / D) := by congr 1 <;> ring

/-- The exact exponents needed when converting the N-balance term to the
`1/(D-2)` scale in the optimized derivative estimate. -/
theorem derivativeBalance_N_exponent_identities {D : ℝ} (hD : 4 < D) :
    (2 / D) * (D / (2 * D - 4)) = 1 / (D - 2) ∧
    1 / 2 + (-1 / 2) * (D / (2 * D - 4)) =
      (D - 4) / (4 * (D - 2)) := by
  constructor
  · have hDpos : 0 < D := by linarith
    have hD2 : 0 < D - 2 := by linarith
    have hden : 0 < 2 * D - 4 := by linarith
    field_simp [ne_of_gt hDpos, ne_of_gt hD2, ne_of_gt hden]
    <;> ring
  · have hD2 : 0 < D - 2 := by linarith
    have hden : 0 < 2 * D - 4 := by linarith
    field_simp [ne_of_gt hD2, ne_of_gt hden]
    <;> ring

/-- Solving the defining `sqrt(2)` normalization for the scale `N`. -/
theorem derivativeBalance_solve_sqrtTwo_scale {N X : ℝ}
    (hN : Real.sqrt 2 * N = X) :
    N = X / Real.sqrt 2 := by
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  calc
    N = (Real.sqrt 2 * N) / Real.sqrt 2 := by
      field_simp [hsqrt]
      <;> ring
    _ = X / Real.sqrt 2 := by rw [hN]

/-- The nested N coefficient power has the exact `1/(D-2)` exponent. -/
theorem derivativeBalance_nested_N_power {X D : ℝ}
    (hX : 0 < X) (hD : 4 < D) :
    (X ^ (2 / D)) ^ (D / (2 * D - 4)) = X ^ (1 / (D - 2)) := by
  rw [← Real.rpow_mul (le_of_lt hX) (2 / D) (D / (2 * D - 4)),
    (derivativeBalance_N_exponent_identities hD).1]

/-- The remaining square-root normalization contributes precisely the
`2^((D-4)/(4(D-2)))` factor used in `b_d`. -/
theorem derivativeBalance_sqrtTwo_inverse_power {D : ℝ} (hD : 4 < D) :
    Real.sqrt 2 * (Real.sqrt 2⁻¹) ^ (D / (2 * D - 4)) =
      (2 : ℝ) ^ ((D - 4) / (4 * (D - 2))) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_neg_eq_inv_rpow]
  rw [show -(1 / 2 : ℝ) = -1 / 2 by ring]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (-1 / 2)
      (D / (2 * D - 4)),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  exact (derivativeBalance_N_exponent_identities hD).2

/-- The numerical base in the N term regroups to the exact `b_d` base. -/
theorem derivativeBalance_N_constant_base_identity {A B D : ℝ} {d : ℕ} :
    (81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d) *
        (2 : ℝ) ^ ((D - 4) / 4) =
      (81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (D / 4) *
        (A / B) ^ 2 := by
  rw [show D / 4 = 1 + (D - 4) / 4 by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  <;> ring

/-- Complete exact substitution of the N-only balanced term by the
`b_d (Lambda^2/lam)^(1/(D-2))` expression. -/
theorem derivativeBalance_N_power_identity
    {A B lam Lambda D N : ℝ} {d : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hlam : 0 < lam)
    (hLambda : 0 < Lambda) (hD : 4 < D)
    (hN : Real.sqrt 2 * N =
      ((81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d) *
        Lambda ^ 2 * lam⁻¹) ^ (2 / D)) :
    Real.sqrt 2 * N ^ (D / (2 * D - 4)) =
      ((81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (D / 4) *
        (A / B) ^ 2) ^ (1 / (D - 2)) *
        (Lambda ^ 2 / lam) ^ (1 / (D - 2)) := by
  let K : ℝ := (81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d)
  let R : ℝ := Lambda ^ 2 / lam
  let nBase : ℝ := K * R
  let e : ℝ := D / (2 * D - 4)
  let t : ℝ := 1 / (D - 2)
  let s : ℝ := (D - 4) / (4 * (D - 2))
  let Kfinal : ℝ := (81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) *
    (2 : ℝ) ^ (D / 4) * (A / B) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hnBase : 0 < nBase := mul_pos hK hR
  have hNbase :
      (81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d) *
          Lambda ^ 2 * lam⁻¹ = nBase := by
    dsimp [nBase, K, R]
    rw [div_eq_mul_inv]
    ring
  have hN' : Real.sqrt 2 * N = nBase ^ (2 / D) := by
    rw [hNbase] at hN
    exact hN
  have hNsolve := derivativeBalance_solve_sqrtTwo_scale hN'
  have hScale := derivativeBalance_sqrtTwo_inverse_power hD
  have hNpow : N ^ e = nBase ^ t * (Real.sqrt 2⁻¹) ^ e := by
    rw [hNsolve, div_eq_mul_inv, Real.mul_rpow
      (le_of_lt (Real.rpow_pos_of_pos hnBase _))
      (inv_nonneg.mpr (Real.sqrt_pos.mpr (by norm_num)).le),
      ← Real.rpow_mul hnBase.le (2 / D) e]
    rw [derivativeBalance_N_exponent_identities hD |>.1]
    simpa [t]
  have hsplit : nBase ^ t = K ^ t * R ^ t := by
    dsimp [nBase]
    rw [Real.mul_rpow hK.le hR.le]
  have hsPower : (2 : ℝ) ^ s = ((2 : ℝ) ^ ((D - 4) / 4)) ^ t := by
    calc
      (2 : ℝ) ^ s = (2 : ℝ) ^ (((D - 4) / 4) * t) := by
        congr 1
        dsimp [s, t]
        field_simp [ne_of_gt (sub_pos.mpr hD)]
      _ = ((2 : ℝ) ^ ((D - 4) / 4)) ^ t :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
  have hKbase : K * (2 : ℝ) ^ ((D - 4) / 4) = Kfinal := by
    dsimp [K, Kfinal]
    exact derivativeBalance_N_constant_base_identity
  have hKcombine : K ^ t * (2 : ℝ) ^ s = Kfinal ^ t := by
    rw [hsPower, ← Real.mul_rpow hK.le
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _), hKbase]
  calc
    Real.sqrt 2 * N ^ (D / (2 * D - 4)) = Real.sqrt 2 * N ^ e := by rfl
    _ = Real.sqrt 2 * (nBase ^ t * (Real.sqrt 2⁻¹) ^ e) := by rw [hNpow]
    _ = nBase ^ t * (Real.sqrt 2 * (Real.sqrt 2⁻¹) ^ e) := by ring
    _ = nBase ^ t * (2 : ℝ) ^ s := by rw [hScale]
    _ = Kfinal ^ t * R ^ t := by
      rw [hsplit]
      calc
        K ^ t * R ^ t * (2 : ℝ) ^ s =
            (K ^ t * (2 : ℝ) ^ s) * R ^ t := by ring
        _ = Kfinal ^ t * R ^ t := by rw [hKcombine]
    _ = Kfinal ^ (1 / (D - 2)) * (Lambda ^ 2 / lam) ^
        (1 / (D - 2)) := by rfl

/-- The baseline `V^(-4/D)` term is bounded by the paper's `a_d` scale
when `V=Y/h`, `Y>d=h+2`, and `lam≤Lambda`. -/
theorem derivativeBalance_baseline_to_a_term
    {h d : ℕ} {D Y lam Lambda V : ℝ}
    (hhd : h + 2 = d) (hD : 0 < D) (hh : 1 ≤ h)
    (hY : (d : ℝ) < Y) (hlam : 0 < lam) (hLambda : lam ≤ Lambda)
    (hV : V = Y / (h : ℝ)) :
    V ^ (-4 / D) ≤ (h : ℝ) ^ (2 / D) *
      (Lambda / (lam * Y)) ^ (2 / D) := by
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
  have hYpos : 0 < Y := by
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    linarith
  have hLambdaPos : 0 < Lambda := lt_of_lt_of_le hlam hLambda
  have hhY : (h : ℝ) ≤ Y := by
    have hhle : (h : ℝ) < (d : ℝ) := by
      exact_mod_cast (show h < d by omega)
    linarith
  have hratioPos : 0 < (h : ℝ) / Y := div_pos hhpos hYpos
  have hratioNonneg : 0 ≤ (h : ℝ) / Y := le_of_lt hratioPos
  have hrightBasePos : 0 < (h : ℝ) * (Lambda / (lam * Y)) :=
    mul_pos hhpos (div_pos hLambdaPos (mul_pos hlam hYpos))
  have hbase : ((h : ℝ) / Y) ^ 2 ≤
      (h : ℝ) * (Lambda / (lam * Y)) := by
    have hcross : (h : ℝ) * lam ≤ Lambda * Y := by
      calc
        (h : ℝ) * lam ≤ Y * lam := mul_le_mul_of_nonneg_right hhY hlam.le
        _ ≤ Y * Lambda := mul_le_mul_of_nonneg_left hLambda hYpos.le
        _ = Lambda * Y := by ring
    have hden : 0 < lam * Y := mul_pos hlam hYpos
    field_simp [ne_of_gt hYpos, ne_of_gt hden]
    nlinarith
  have hleft : V ^ (-4 / D) = (((h : ℝ) / Y) ^ 2) ^ (2 / D) := by
    rw [hV, show -4 / D = -(4 / D) by ring, Real.rpow_neg_eq_inv_rpow,
      show (Y / (h : ℝ))⁻¹ = (h : ℝ) / Y by
        field_simp [ne_of_gt hYpos, ne_of_gt hhpos],
      show 4 / D = 2 * (2 / D) by ring,
      ← Real.rpow_natCast_mul hratioNonneg 2 (2 / D)]
    congr 1
  have hpow : (((h : ℝ) / Y) ^ 2) ^ (2 / D) ≤
      ((h : ℝ) * (Lambda / (lam * Y))) ^ (2 / D) :=
    Real.rpow_le_rpow (sq_nonneg ((h : ℝ) / Y)) hbase
      (div_nonneg (by norm_num) hD.le)
  have hright :
      ((h : ℝ) * (Lambda / (lam * Y))) ^ (2 / D) =
        (h : ℝ) ^ (2 / D) * (Lambda / (lam * Y)) ^ (2 / D) :=
    Real.mul_rpow hhpos.le (div_nonneg hLambdaPos.le (mul_nonneg hlam.le hYpos.le))
  have hpow' := hpow
  rw [hright] at hpow'
  rw [hleft]
  exact hpow'

/-- Substitute the exact four balanced contributions in the envelope by
the four constants and scales of blueprint Proposition `ld:optimized`. -/
theorem derivativeBalance_balanced_terms_to_paper_constants
    {h d : ℕ} {A B Y lam Lambda D V M N : ℝ}
    (hhd : h + 2 = d) (hD : D = (2 : ℝ) ^ d) (hh : 1 ≤ h)
    (hA : 0 < A) (hB : 0 < B) (hY : (d : ℝ) < Y)
    (hlam : 0 < lam) (hLambda : lam ≤ Lambda)
    (hV : V = Y / (h : ℝ))
    (hM : Real.sqrt 2 * M =
      (A ^ 2 * (B⁻¹) ^ 2 * D ^ 2 * (Y⁻¹) ^ 2 * lam⁻¹) ^ (2 / D))
    (hN : Real.sqrt 2 * N =
      ((81 / 4 : ℝ) * (A / B) ^ 2 * (2 / 3 : ℝ) ^ (2 * d) *
        Lambda ^ 2 * lam⁻¹) ^ (2 / D)) :
    let T1 : ℝ := (V ^ h) ^ (-2 / (D - 4))
    let T2 : ℝ := M * (V ^ h) ^ (-2 / D)
    let T3 : ℝ := Real.sqrt (M * N)
    let T4 : ℝ := N ^ (D / (2 * D - 4))
    let W : ℝ := V ^ (-4 / D)
    B * (Real.sqrt 2 * max (max T1 (max T2 (max T3 T4))) W) ≤
    max (B * Real.sqrt 2 * (h : ℝ) ^ (2 / D) *
          (Lambda / (lam * Y)) ^ (2 / D))
      (max
        (B * ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d * (A / B) ^ 2 * D) ^
          (2 / D) * (Lambda / (lam * Y)) ^ (2 / D))
        (max
          (B * ((81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) *
            (2 : ℝ) ^ (D / 4) * (A / B) ^ 2) ^ (1 / (D - 2)) *
            (Lambda ^ 2 / lam) ^ (1 / (D - 2)))
          (B * (A * D / B) ^ (4 / D) * (h : ℝ) ^
            (2 * (h : ℝ) / D) * (lam * Y ^ d) ^ (-2 / D)))) := by
  dsimp only
  let scale : ℝ := B * Real.sqrt 2
  let T1 : ℝ := (V ^ h) ^ (-2 / (D - 4))
  let T2 : ℝ := M * (V ^ h) ^ (-2 / D)
  let T3 : ℝ := Real.sqrt (M * N)
  let T4 : ℝ := N ^ (D / (2 * D - 4))
  let W : ℝ := V ^ (-4 / D)
  let a : ℝ := B * Real.sqrt 2 * (h : ℝ) ^ (2 / D) *
    (Lambda / (lam * Y)) ^ (2 / D)
  let ap : ℝ := B * ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d * (A / B) ^ 2 * D) ^
    (2 / D) * (Lambda / (lam * Y)) ^ (2 / D)
  let b : ℝ := B * ((81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) *
    (2 : ℝ) ^ (D / 4) * (A / B) ^ 2) ^ (1 / (D - 2)) *
    (Lambda ^ 2 / lam) ^ (1 / (D - 2))
  let c : ℝ := B * (A * D / B) ^ (4 / D) * (h : ℝ) ^
    (2 * (h : ℝ) / D) * (lam * Y ^ d) ^ (-2 / D)
  have hDpos : 0 < D := by rw [hD]; positivity
  have hDfour : 4 < D := by
    rw [hD]
    have hd : 3 ≤ d := by omega
    have hdPow : (8 : ℝ) ≤ (2 : ℝ) ^ d := by
      calc
        (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
    linarith
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
  have hYpos : 0 < Y := by
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    linarith
  have hhle : (h : ℝ) ≤ Y := by
    have hhd' : (h : ℝ) + 2 = (d : ℝ) := by exact_mod_cast hhd
    linarith
  have hVpos : 0 < V := by rw [hV]; exact div_pos hYpos hhpos
  have hVone : 1 ≤ V := by
    rw [hV]
    exact (le_div_iff₀ hhpos).2 (by linarith)
  have hLambdaPos : 0 < Lambda := lt_of_lt_of_le hlam hLambda
  have hscaleNonneg : 0 ≤ scale := by dsimp [scale]; positivity
  have hbaseline := derivativeBalance_baseline_to_a_term
    hhd hDpos hh hY hlam hLambda hV
  have hcap0 := derivativeBalance_cap_term_le_V_term h hh hVone
  have hcap : T1 ≤ W := by
    dsimp [T1, W]
    have hpow : (2 : ℝ) ^ (h + 2) = D := by
      rw [hD]
      congr 1
    simpa [hpow] using hcap0
  have hW : scale * W ≤ a := by
    dsimp [scale, W, a]
    have hle := mul_le_mul_of_nonneg_left hbaseline
      (mul_nonneg hB.le (Real.sqrt_nonneg (2 : ℝ)))
    nlinarith [hle]
  have hMcap := derivativeBalance_M_cap_identity
    hhd hDpos hA hB hYpos hlam
  have hT2eq : scale * T2 =
      B * ((Real.sqrt 2 * M) * (V ^ h) ^ (-2 / D)) := by
    dsimp [scale, T2]
    ring
  have hT2 : scale * T2 ≤ c := by
    have hVpow : (V ^ h) ^ (-2 / D) = V ^ (-2 * (h : ℝ) / D) := by
      rw [← Real.rpow_natCast_mul hVpos.le h (-2 / D)]
      congr 1
      push_cast
      ring
    rw [hT2eq, hVpow, hV, hM, hMcap]
    dsimp [c]
    ring_nf
    exact le_rfl
  have hmix := derivativeBalance_mixed_sqrtMN_identity
    hA hB hYpos hlam hLambdaPos hDpos hM hN
  have hT3eq : scale * T3 = B * (Real.sqrt 2 * Real.sqrt (M * N)) := by
    dsimp [scale, T3]
    ring
  have hT3 : scale * T3 ≤ ap := by
    rw [hT3eq, hmix]
    dsimp [ap]
    have hcoef : 0 < (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d *
        (A / B) ^ 2 * D := by positivity
    rw [show (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d * (A / B) ^ 2 * D *
        Lambda / (lam * Y) =
        ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d * (A / B) ^ 2 * D) *
          (Lambda / (lam * Y)) by ring]
    rw [Real.mul_rpow hcoef.le
      (div_nonneg hLambdaPos.le (mul_nonneg hlam.le hYpos.le))]
    ring_nf
    exact le_rfl
  have hNterm := derivativeBalance_N_power_identity
    hA hB hlam hLambdaPos hDfour hN
  have hT4eq : scale * T4 = B * (Real.sqrt 2 * N ^ (D / (2 * D - 4))) := by
    dsimp [scale, T4]
    ring
  have hT4 : scale * T4 ≤ b := by
    rw [hT4eq, hNterm]
    dsimp [b]
    ring_nf
    exact le_rfl
  have hT1 : scale * T1 ≤ a := (mul_le_mul_of_nonneg_left hcap hscaleNonneg).trans hW
  have hinner : max (max (scale * T1) (max (scale * T2)
      (max (scale * T3) (scale * T4)))) (scale * W) ≤
      max a (max c (max ap b)) := by
    apply max_le
    · apply max_le
      · exact hT1.trans (le_max_left a (max c (max ap b)))
      · apply max_le
        · exact hT2.trans (le_trans (le_max_left c (max ap b))
            (le_max_right a (max c (max ap b))))
        · apply max_le
          · exact hT3.trans (le_trans (le_max_left ap b)
              (le_trans (le_max_right c (max ap b))
                (le_max_right a (max c (max ap b)))))
          · exact hT4.trans (le_trans (le_max_right ap b)
              (le_trans (le_max_right c (max ap b))
                (le_max_right a (max c (max ap b)))))
    · exact hW.trans (le_max_left a (max c (max ap b)))
  have hstart : B * (Real.sqrt 2 * max
      (max T1 (max T2 (max T3 T4))) W) =
        scale * max (max T1 (max T2 (max T3 T4))) W := by
    dsimp [scale]
    ring
  have htarget : max a (max c (max ap b)) = max a (max ap (max b c)) := by
    congr 1
    calc
      max c (max ap b) = max (max c ap) b := (max_assoc c ap b).symm
      _ = max (max ap c) b := by rw [max_comm c ap]
      _ = max ap (max c b) := max_assoc ap c b
      _ = max ap (max b c) := by rw [max_comm c b]
  have hmaxscale : scale * max (max T1 (max T2 (max T3 T4))) W =
      max (max (scale * T1) (max (scale * T2)
        (max (scale * T3) (scale * T4)))) (scale * W) := by
    rw [mul_max_of_nonneg _ _ hscaleNonneg,
      mul_max_of_nonneg _ _ hscaleNonneg,
      mul_max_of_nonneg _ _ hscaleNonneg,
      mul_max_of_nonneg _ _ hscaleNonneg]
  calc
    B * (Real.sqrt 2 * max (max T1 (max T2 (max T3 T4))) W) =
        scale * max (max T1 (max T2 (max T3 T4))) W := hstart
    _ = max (max (scale * T1) (max (scale * T2)
          (max (scale * T3) (scale * T4)))) (scale * W) := hmaxscale
    _ ≤ max a (max c (max ap b)) := hinner
    _ = max a (max ap (max b c)) := htarget
  

 /-- The exponents and four-term grouping used by the generic envelope agree
with the notation used in the optimized-constant comparison. -/
theorem derivativeBalance_envelope_shape
    {h d : ℕ} {D V M N : ℝ}
    (hhd : h + 2 = d) (hD : D = (2 : ℝ) ^ d) (hDfour : 4 < D) :
    let α : ℝ := 2 / ((2 : ℝ) ^ (h + 2) - 4)
    let β : ℝ := 2 / (2 : ℝ) ^ (h + 2)
    let Z : ℝ := V ^ h
    let Q : ℝ := max (Z ^ (-α))
      (max (M * Z ^ (-β))
        (max (Real.sqrt (M * N)) (N ^ (α / (α + β)))))
    (Q = max ((V ^ h) ^ (-2 / (D - 4)))
      (max (M * (V ^ h) ^ (-2 / D))
        (max (Real.sqrt (M * N)) (N ^ (D / (2 * D - 4)))))) ∧
    V ^ (-4 / (2 : ℝ) ^ (h + 2)) = V ^ (-4 / D) := by
  let α : ℝ := 2 / ((2 : ℝ) ^ (h + 2) - 4)
  let β : ℝ := 2 / (2 : ℝ) ^ (h + 2)
  let Z : ℝ := V ^ h
  let Q : ℝ := max (Z ^ (-α))
    (max (M * Z ^ (-β))
      (max (Real.sqrt (M * N)) (N ^ (α / (α + β)))))
  have hα : α = 2 / (D - 4) := by
    dsimp [α]
    rw [hhd, hD]
  have hβ : β = 2 / D := by
    dsimp [β]
    rw [hhd, hD]
  have hexp : α / (α + β) = D / (2 * D - 4) := by
    rw [hα, hβ]
    have hDpos : 0 < D := by linarith
    have hD2pos : 0 < D - 2 := by linarith
    have hD4pos : 0 < D - 4 := by linarith
    have hden : 0 < 2 * D - 4 := by linarith
    field_simp [ne_of_gt hDpos, ne_of_gt hD2pos, ne_of_gt hD4pos,
      ne_of_gt hden]
    <;> ring
  constructor
  · change max ((V ^ h) ^ (-α))
      (max (M * (V ^ h) ^ (-β))
        (max (Real.sqrt (M * N)) (N ^ (α / (α + β))))) =
      max ((V ^ h) ^ (-2 / (D - 4)))
        (max (M * (V ^ h) ^ (-2 / D))
          (max (Real.sqrt (M * N)) (N ^ (D / (2 * D - 4)))))
    rw [hα, hβ]
    have hexp' : (2 / (D - 4)) / (2 / (D - 4) + 2 / D) =
        D / (2 * D - 4) := by
      have hDpos : 0 < D := by linarith
      have hD2pos : 0 < D - 2 := by linarith
      have hD4pos : 0 < D - 4 := by linarith
      have hden : 0 < 2 * D - 4 := by linarith
      field_simp [ne_of_gt hDpos, ne_of_gt hD2pos, ne_of_gt hD4pos,
        ne_of_gt hden]
      <;> ring
    rw [hexp']
    rw [show -(2 / (D - 4)) = -2 / (D - 4) by ring,
      show -(2 / D) = -2 / D by ring]
  · rw [hhd, hD]

/-- Specialize the all-scales derivative correlation estimate to the exact
`V=Y/(d-2)` scale in the optimized derivative proposition, then feed it to
the balanced four-term envelope. -/
theorem derivativeBalance_envelope_of_data
    {x Y lam Lambda : ℝ} {d : ℕ}
    (data : HalfOpenCkData x Y d)
    (hd : 3 ≤ d) (hY : (d : ℝ) < Y)
    (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y), lam ≤ data.derivative d t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y), data.derivative d t ≤ Lambda) :
    let h : ℕ := d - 2
    let D : ℝ := (2 : ℝ) ^ d
    let V : ℝ := Y / (h : ℝ)
    let M : ℝ :=
      (((14 / 5 : ℝ) ^ 2 * derivativeWeylConstant⁻¹ ^ 2 * D ^ 2 *
        Y⁻¹ ^ 2 * lam⁻¹) ^ (2 / D)) / Real.sqrt 2
    let N : ℝ :=
      (((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
        (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) /
        Real.sqrt 2
    let S : ℝ :=
      ‖∑ n ∈ realIntegerInterval x Y,
        realExponentialPhase (data.derivative 0) n‖ / Y
    let α : ℝ := 2 / ((2 : ℝ) ^ (h + 2) - 4)
    let β : ℝ := 2 / (2 : ℝ) ^ (h + 2)
    let Z : ℝ := V ^ h
    let Q : ℝ := max (Z ^ (-α))
      (max (M * Z ^ (-β))
        (max (Real.sqrt (M * N)) (N ^ (α / (α + β)))))
    let W : ℝ := V ^ (-4 / (2 : ℝ) ^ (h + 2))
    S ≤ derivativeWeylConstant * (Real.sqrt 2 * max Q W) := by
  let h : ℕ := d - 2
  let D : ℝ := (2 : ℝ) ^ d
  let V : ℝ := Y / (h : ℝ)
  let M : ℝ :=
    (((14 / 5 : ℝ) ^ 2 * derivativeWeylConstant⁻¹ ^ 2 * D ^ 2 *
      Y⁻¹ ^ 2 * lam⁻¹) ^ (2 / D)) / Real.sqrt 2
  let N : ℝ :=
    (((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
      (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) /
      Real.sqrt 2
  let S : ℝ :=
    ‖∑ n ∈ realIntegerInterval x Y,
      realExponentialPhase (data.derivative 0) n‖ / Y
  have hhd : h + 2 = d := by dsimp [h]; omega
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hYpos : 0 < Y := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (show 0 < d by omega)
    linarith
  have hhpos : 0 < (h : ℝ) := by
    exact_mod_cast (show 0 < h by omega)
  have hVone : 1 ≤ V := by
    dsimp [V]
    rw [le_div_iff₀ hhpos]
    have hhdR : (h : ℝ) + 2 = (d : ℝ) := by exact_mod_cast hhd
    linarith
  have hcapacity : (h : ℝ) * V ≤ Y := by
    dsimp [V]
    rw [mul_div_cancel₀ Y (ne_of_gt hhpos)]
  have hMpos : 0 < M := by dsimp [M]; positivity [derivativeWeylConstant_pos]
  have hNpos : 0 < N := by dsimp [N]; positivity [derivativeWeylConstant_pos]
  have hbound : ∀ ξ : ℝ, 0 < ξ → ξ ≤ V ^ h →
      S ≤ derivativeWeylConstant * max
        (Real.sqrt 2 * max
          (ξ ^ (-2 / ((2 : ℝ) ^ (h + 2) - 4)))
          (V ^ (-4 / (2 : ℝ) ^ (h + 2))))
        (Real.sqrt 2 * max
          (M * ξ ^ (-2 / (2 : ℝ) ^ (h + 2)))
          (N * ξ ^ (2 / (2 : ℝ) ^ (h + 2)))) := by
    intro ξ hξ hξV
    have hcorr := derivativeCorrelation_sum_bound_for_xi
      (data := data) hd hhd hY hlam hLambda hlower hupper hh V ξ
      hVone hξ hξV hcapacity
    simpa [S, D, M, N, hhd] using hcorr
  simpa [h, D, V, M, N, S] using
    (derivativeBalance_four_term_envelope h hh hVone hMpos hNpos hbound)

 /-- The optimized derivative estimate from blueprint Proposition
`ld:optimized`, with the paper's exact constants and half-open interval. -/
theorem derivative_optimized_estimate
    {x Y lam Lambda : ℝ} {d : ℕ}
    (data : HalfOpenCkData x Y d)
    (hd : 3 ≤ d) (hY : (d : ℝ) < Y)
    (hlam : 0 < lam)
    (hlower : ∀ t ∈ Set.Ioc x (x + Y), lam ≤ data.derivative d t)
    (hupper : ∀ t ∈ Set.Ioc x (x + Y), data.derivative d t ≤ Lambda) :
    let h : ℕ := d - 2
    let D : ℝ := (2 : ℝ) ^ d
    ‖∑ n ∈ realIntegerInterval x Y,
      realExponentialPhase (data.derivative 0) n‖ / Y ≤
    max
      (derivativeWeylConstant * Real.sqrt 2 * (h : ℝ) ^ (2 / D) *
        (Lambda / (lam * Y)) ^ (2 / D))
      (max
        (derivativeWeylConstant *
          ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d *
            ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 * D) ^ (2 / D) *
          (Lambda / (lam * Y)) ^ (2 / D))
        (max
          (derivativeWeylConstant *
            ((81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) *
              (2 : ℝ) ^ (D / 4) *
              ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2) ^
                (1 / (D - 2)) *
            (Lambda ^ 2 / lam) ^ (1 / (D - 2)))
          (derivativeWeylConstant *
            ((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
            (h : ℝ) ^ (2 * (h : ℝ) / D) *
            (lam * Y ^ d) ^ (-2 / D)))) := by
  let h : ℕ := d - 2
  let D : ℝ := (2 : ℝ) ^ d
  have hhd : h + 2 = d := by dsimp [h]; omega
  have hYpos : 0 < Y := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (show 0 < d by omega)
    linarith
  have hLambda : 0 < Lambda := by
    have hpoint : x + Y ∈ Set.Ioc x (x + Y) := by
      constructor <;> linarith
    have hlower' := hlower (x + Y) hpoint
    have hupper' := hupper (x + Y) hpoint
    linarith
  have hLambdaLe : lam ≤ Lambda := by
    have hpoint : x + Y ∈ Set.Ioc x (x + Y) := by
      constructor <;> linarith
    exact (hlower (x + Y) hpoint).trans (hupper (x + Y) hpoint)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hDfour : 4 < D := by
    dsimp [D]
    have hd' : 3 ≤ d := hd
    have hpow : (8 : ℝ) ≤ (2 : ℝ) ^ d := by
      calc
        (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd'
    linarith
  have hA : 0 < (14 / 5 : ℝ) := by norm_num
  have hB : 0 < derivativeWeylConstant := derivativeWeylConstant_pos
  let V : ℝ := Y / (h : ℝ)
  let M : ℝ :=
    (((14 / 5 : ℝ) ^ 2 * derivativeWeylConstant⁻¹ ^ 2 * D ^ 2 *
      Y⁻¹ ^ 2 * lam⁻¹) ^ (2 / D)) / Real.sqrt 2
  let N : ℝ :=
    (((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
      (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D)) /
      Real.sqrt 2
  let S : ℝ :=
    ‖∑ n ∈ realIntegerInterval x Y,
      realExponentialPhase (data.derivative 0) n‖ / Y
  let α : ℝ := 2 / ((2 : ℝ) ^ (h + 2) - 4)
  let β : ℝ := 2 / (2 : ℝ) ^ (h + 2)
  let Z : ℝ := V ^ h
  let Q : ℝ := max (Z ^ (-α))
    (max (M * Z ^ (-β))
      (max (Real.sqrt (M * N)) (N ^ (α / (α + β)))))
  let W : ℝ := V ^ (-4 / (2 : ℝ) ^ (h + 2))
  have hMnorm : Real.sqrt 2 * M =
      ((14 / 5 : ℝ) ^ 2 * (derivativeWeylConstant⁻¹) ^ 2 *
        D ^ 2 * (Y⁻¹) ^ 2 * lam⁻¹) ^ (2 / D) := by
    dsimp [M]
    have hsqrt : Real.sqrt 2 ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hsqrt]
  have hNnorm : Real.sqrt 2 * N =
      ((81 / 4 : ℝ) * ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
        (2 / 3 : ℝ) ^ (2 * d) * Lambda ^ 2 * lam⁻¹) ^ (2 / D) := by
    dsimp [N]
    have hsqrt : Real.sqrt 2 ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hsqrt]
  have henv := derivativeBalance_envelope_of_data
    (data := data) hd hY hlam hLambda hlower hupper
  have hshape := derivativeBalance_envelope_shape (h := h) (d := d)
    (D := D) (V := V) (M := M) (N := N) hhd (by rfl) hDfour
  have hcomparison := derivativeBalance_balanced_terms_to_paper_constants
    hhd (by rfl) (by omega) hA hB hY hlam hLambdaLe (by rfl)
    hMnorm hNnorm
  change S ≤ derivativeWeylConstant * (Real.sqrt 2 * max Q W) at henv
  change Q = max ((V ^ h) ^ (-2 / (D - 4)))
      (max (M * (V ^ h) ^ (-2 / D))
        (max (Real.sqrt (M * N)) (N ^ (D / (2 * D - 4))))) ∧
    W = V ^ (-4 / D) at hshape
  rw [hshape.1, hshape.2] at henv
  have hfinal := henv.trans hcomparison
  simpa [h, D, S, V, M, N] using hfinal

/-- Exact rational bounds on the repeated-differencing constant. -/
theorem derivativeWeylConstant_bounds :
    (14 / 3 : ℝ) < derivativeWeylConstant ∧
    derivativeWeylConstant < 5 ∧
    (14 / 5 : ℝ) / derivativeWeylConstant < 3 / 5 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsquare : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLow : (4 / 3 : ℝ) < Real.sqrt 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 4 / 3)]
  have hsqrtHigh : Real.sqrt 2 < (3 / 2 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 3 / 2)]
  rw [derivativeWeylConstant]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · have hBpositive : 0 < 2 + 2 * Real.sqrt 2 := by positivity
    rw [div_lt_iff₀ hBpositive]
    nlinarith

/-- Elementary integer growth estimates used for the uniform constant bounds. -/
theorem derivative_constants_nat_growth (d h : ℕ) :
    (3 ≤ d → 2 * d + 2 ≤ 2 ^ d) ∧
    (3 ≤ h → 2 * h ^ 2 + 2 * h + 8 ≤ 2 ^ (h + 2)) := by
  constructor
  · intro hd
    induction d with
    | zero => omega
    | succ d ih =>
        by_cases hd' : d < 3
        · interval_cases d <;> norm_num at *
        · have hi := ih (by omega)
          rw [pow_succ]
          omega
  · intro hh
    induction h with
    | zero => omega
    | succ h ih =>
        by_cases hh' : h < 3
        · interval_cases h <;> norm_num at *
        · have hi := ih (by omega)
          rw [show h + 1 + 2 = (h + 2) + 1 by omega, pow_succ]
          have hpoly : 2 * (h + 1) ^ 2 + 2 * (h + 1) + 8 ≤
              2 * (2 * h ^ 2 + 2 * h + 8) := by nlinarith
          calc
            2 * (h + 1) ^ 2 + 2 * (h + 1) + 8 ≤
                2 * (2 * h ^ 2 + 2 * h + 8) := hpoly
            _ ≤ 2 * 2 ^ (h + 2) := Nat.mul_le_mul_left 2 hi
            _ = 2 ^ (h + 2) * 2 := by omega

theorem derivative_nat_le_two_pow (h : ℕ) : h ≤ 2 ^ h := by
  have hmul := Nat.mul_le_pow (by decide : 2 ≠ 1) h
  omega

theorem derivative_a_power_factor_le_sqrt_two
    {h d : ℕ} {D : ℝ} (hhd : h + 2 = d)
    (hh : 1 ≤ h) (hD : D = (2 : ℝ) ^ d) :
    (h : ℝ) ^ (2 / D) ≤ Real.sqrt 2 := by
  have hpowD : D / 4 = (2 : ℝ) ^ h := by
    rw [hD, ← hhd, pow_add]
    norm_num
  have hnat : h ≤ 2 ^ (2 ^ h) := by
    have h1 := derivative_nat_le_two_pow h
    have h2 := Nat.pow_le_pow_right (by decide : 0 < 2) h1
    exact h1.trans h2
  have hbase : (h : ℝ) ≤ (2 : ℝ) ^ (2 ^ h) := by exact_mod_cast hnat
  have hDpos : 0 < D := by rw [hD]; positivity
  have hE : ((2 : ℕ) ^ h : ℝ) = D / 4 := by
    simpa [Nat.cast_pow] using hpowD.symm
  have hE' : ((2 ^ h : ℕ) : ℝ) = D / 4 := by
    simpa [Nat.cast_pow] using hE
  have hNatToReal : (2 : ℝ) ^ (2 ^ h) = Real.rpow 2 (D / 4) := by
    calc
      (2 : ℝ) ^ (2 ^ h) = Real.rpow 2 ((2 ^ h : ℕ) : ℝ) :=
        (Real.rpow_natCast 2 (2 ^ h)).symm
      _ = Real.rpow 2 (D / 4) := by rw [hE']
  have hbase' : (h : ℝ) ≤ Real.rpow 2 (D / 4) := by
    rw [← hNatToReal]
    exact hbase
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg h) hbase'
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hDpos.le)
  have hrhs : (Real.rpow 2 (D / 4)) ^ (2 / D) = Real.sqrt 2 := by
    have hexp' : (D / 4) * (2 / D) = 1 / 2 := by
      field_simp [ne_of_gt hDpos]
      <;> ring
    calc
      (Real.rpow 2 (D / 4)) ^ (2 / D) =
          Real.rpow 2 ((D / 4) * (2 / D)) :=
        (Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) (D / 4) (2 / D)).symm
      _ = Real.rpow 2 (1 / 2) := by rw [hexp']
      _ = Real.sqrt 2 := by rw [Real.sqrt_eq_rpow]; rfl
  rw [hrhs] at hpow
  exact hpow

theorem derivative_a_coefficient_lt_eleven (d : ℕ) (hd : 3 ≤ d) :
    let h : ℕ := d - 2
    let D : ℝ := (2 : ℝ) ^ d
    derivativeWeylConstant * Real.sqrt 2 * (h : ℝ) ^ (2 / D) < 11 := by
  let h : ℕ := d - 2
  let D : ℝ := (2 : ℝ) ^ d
  have hhd : h + 2 = d := by dsimp [h]; omega
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hD : D = (2 : ℝ) ^ d := rfl
  have hfactor := derivative_a_power_factor_le_sqrt_two hhd hh hD
  have hBpos := derivativeWeylConstant_pos
  have hBlt := derivativeWeylConstant_bounds.2.1
  have hscale : 0 ≤ derivativeWeylConstant * Real.sqrt 2 := by positivity
  calc
    derivativeWeylConstant * Real.sqrt 2 * (h : ℝ) ^ (2 / D) ≤
        derivativeWeylConstant * Real.sqrt 2 * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_left hfactor hscale
    _ = 2 * derivativeWeylConstant := by
      have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        derivativeWeylConstant * Real.sqrt 2 * Real.sqrt 2 =
            derivativeWeylConstant * (Real.sqrt 2 * Real.sqrt 2) := by ring
        _ = derivativeWeylConstant * 2 := by rw [hsqrt2]
        _ = 2 * derivativeWeylConstant := by ring
    _ < 11 := by nlinarith

theorem derivative_ap_base_lt_two_pow (d : ℕ) (hd : 3 ≤ d) :
    ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d *
      ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 *
      (2 : ℝ) ^ d) < (2 : ℝ) ^ (d + 1) := by
  have hB := derivativeWeylConstant_bounds
  have hratio : (14 / 5 : ℝ) / derivativeWeylConstant < 3 / 5 := hB.2.2
  have hratioPos : 0 < (14 / 5 : ℝ) / derivativeWeylConstant := by
    exact div_pos (by norm_num) derivativeWeylConstant_pos
  have hratioSq : ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 <
      (3 / 5 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((14 / 5 : ℝ) / derivativeWeylConstant - 3 / 5)]
  have hpow : (2 / 3 : ℝ) ^ d ≤ 8 / 27 := by
    rw [show d = 3 + (d - 3) by omega, pow_add]
    have htail : (2 / 3 : ℝ) ^ (d - 3) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    calc
      (2 / 3 : ℝ) ^ 3 * (2 / 3 : ℝ) ^ (d - 3) ≤
          (2 / 3 : ℝ) ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = 8 / 27 := by norm_num
  have hD : 0 < (2 : ℝ) ^ d := by positivity
  have hfactor : 0 < (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d * (2 : ℝ) ^ d :=
    by positivity
  have hfirst :
      (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d *
        ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 * (2 : ℝ) ^ d <
      (81 / 50 : ℝ) * (2 / 3 : ℝ) ^ d * (2 : ℝ) ^ d := by
    calc
      _ = ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d * (2 : ℝ) ^ d) *
          ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 := by ring
      _ < ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d * (2 : ℝ) ^ d) *
          ((3 / 5 : ℝ) ^ 2) := mul_lt_mul_of_pos_left hratioSq hfactor
      _ = (81 / 50 : ℝ) * (2 / 3 : ℝ) ^ d * (2 : ℝ) ^ d := by ring
  have hsecond : (81 / 50 : ℝ) * (2 / 3 : ℝ) ^ d * (2 : ℝ) ^ d ≤
      (12 / 25 : ℝ) * (2 : ℝ) ^ d := by
    calc
      (81 / 50 : ℝ) * (2 / 3 : ℝ) ^ d * (2 : ℝ) ^ d ≤
          (81 / 50 : ℝ) * (8 / 27) * (2 : ℝ) ^ d := by
        gcongr
      _ = (12 / 25 : ℝ) * (2 : ℝ) ^ d := by norm_num
  calc
    _ < (81 / 50 : ℝ) * (2 / 3 : ℝ) ^ d * (2 : ℝ) ^ d := hfirst
    _ ≤ (12 / 25 : ℝ) * (2 : ℝ) ^ d := hsecond
    _ < 2 * (2 : ℝ) ^ d := by
      exact mul_lt_mul_of_pos_right (by norm_num) hD
    _ = (2 : ℝ) ^ (d + 1) := by rw [pow_succ]; ring

theorem derivative_ap_coefficient_lt_eleven (d : ℕ) (hd : 3 ≤ d) :
    let D : ℝ := (2 : ℝ) ^ d
    derivativeWeylConstant *
      ((9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d *
        ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 * D) ^ (2 / D) < 11 := by
  let D : ℝ := (2 : ℝ) ^ d
  have hD : D = (2 : ℝ) ^ d := rfl
  have hDpos : 0 < D := by rw [hD]; positivity
  have hBpos := derivativeWeylConstant_pos
  have hBlt := derivativeWeylConstant_bounds.2.1
  let C : ℝ := (9 / 2 : ℝ) * (2 / 3 : ℝ) ^ d *
    ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 * D
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCbound : C < (2 : ℝ) ^ (d + 1) := by
    dsimp [C]
    exact derivative_ap_base_lt_two_pow d hd
  have hpower : C ^ (2 / D) < ((2 : ℝ) ^ (d + 1)) ^ (2 / D) :=
    Real.rpow_lt_rpow hCpos.le hCbound
      (div_pos (by norm_num) hDpos)
  have hgrowth := (derivative_constants_nat_growth d 0).1 hd
  have hnum : 2 * ((d : ℝ) + 1) ≤ D := by
    rw [hD]
    exact_mod_cast hgrowth
  have hexp : ((d : ℝ) + 1) * (2 / D) ≤ 1 := by
    rw [show ((d : ℝ) + 1) * (2 / D) =
        (2 * ((d : ℝ) + 1)) / D by ring]
    exact (div_le_iff₀ hDpos).2 (by simpa using hnum)
  have hpowerBound : ((2 : ℝ) ^ (d + 1)) ^ (2 / D) ≤ 2 := by
    calc
      ((2 : ℝ) ^ (d + 1)) ^ (2 / D) =
          (2 : ℝ) ^ (((d : ℝ) + 1) * (2 / D)) :=
        by
          simpa [Nat.cast_add] using
            (Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ))
              (d + 1) (2 / D)).symm
      _ ≤ (2 : ℝ) ^ 1 := Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) hexp
      _ = 2 := by norm_num
  calc
    derivativeWeylConstant * C ^ (2 / D) <
        derivativeWeylConstant * ((2 : ℝ) ^ (d + 1)) ^ (2 / D) :=
      mul_lt_mul_of_pos_left hpower hBpos
    _ ≤ derivativeWeylConstant * 2 :=
      mul_le_mul_of_nonneg_left hpowerBound hBpos.le
    _ < 11 := by nlinarith

theorem derivative_b_coefficient_lt_eleven (d : ℕ) (hd : 3 ≤ d) :
    let D : ℝ := (2 : ℝ) ^ d
    derivativeWeylConstant *
      ((81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) *
        (2 : ℝ) ^ (D / 4) *
        ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2) ^ (1 / (D - 2)) < 11 := by
  let D : ℝ := (2 : ℝ) ^ d
  let K : ℝ := (81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) *
    ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2
  have hD : D = (2 : ℝ) ^ d := rfl
  have hDge8 : 8 ≤ D := by
    rw [hD]
    have hd' : 3 ≤ d := hd
    have hpow : (8 : ℝ) ≤ (2 : ℝ) ^ d := by
      calc
        (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd'
    exact hpow
  have hDpos : 0 < D := by linarith
  have hDsub : 0 < D - 2 := by linarith
  have hratio := derivativeWeylConstant_bounds.2.2
  have hratioPos : 0 < (14 / 5 : ℝ) / derivativeWeylConstant :=
    div_pos (by norm_num) derivativeWeylConstant_pos
  have hratioSq : ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 <
      (3 / 5 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((14 / 5 : ℝ) / derivativeWeylConstant - 3 / 5)]
  have hpow : (2 / 3 : ℝ) ^ (2 * d) ≤ (2 / 3 : ℝ) ^ 6 := by
    have hddecomp : 2 * d = 6 + (2 * d - 6) := by omega
    rw [hddecomp, pow_add]
    have htail : (2 / 3 : ℝ) ^ (2 * d - 6) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    calc
      (2 / 3 : ℝ) ^ 6 * (2 / 3 : ℝ) ^ (2 * d - 6) ≤
          (2 / 3 : ℝ) ^ 6 * 1 :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (2 / 3 : ℝ) ^ 6 := by ring
  have hK : K < 1 := by
    dsimp [K]
    calc
      (81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) *
          ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 ≤
        (81 / 8 : ℝ) * (2 / 3 : ℝ) ^ 6 * (3 / 5 : ℝ) ^ 2 := by
          gcongr
      _ = 8 / 25 := by norm_num
      _ < 1 := by norm_num
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hbase : 0 < K * (2 : ℝ) ^ (D / 4) := by positivity
  have hbaseLt : K * (2 : ℝ) ^ (D / 4) < (2 : ℝ) ^ (D / 4) := by
    calc
      K * (2 : ℝ) ^ (D / 4) < 1 * (2 : ℝ) ^ (D / 4) :=
        mul_lt_mul_of_pos_right hK (Real.rpow_pos_of_pos (by norm_num) _)
      _ = (2 : ℝ) ^ (D / 4) := by ring
  have hpowLt :
      (K * (2 : ℝ) ^ (D / 4)) ^ (1 / (D - 2)) <
        ((2 : ℝ) ^ (D / 4)) ^ (1 / (D - 2)) :=
    Real.rpow_lt_rpow hbase.le hbaseLt (div_pos (by norm_num) hDsub)
  have hexp : (D / 4) * (1 / (D - 2)) ≤ 1 := by
    have hden : 0 < 4 * (D - 2) := by positivity
    have hfrac : (D / 4) * (1 / (D - 2)) = D / (4 * (D - 2)) := by
      field_simp [ne_of_gt hDsub]
      <;> ring
    rw [hfrac]
    apply (div_le_iff₀ hden).2
    nlinarith [hDge8]
  have hdyadic : ((2 : ℝ) ^ (D / 4)) ^ (1 / (D - 2)) ≤ 2 := by
    calc
      ((2 : ℝ) ^ (D / 4)) ^ (1 / (D - 2)) =
          (2 : ℝ) ^ ((D / 4) * (1 / (D - 2))) :=
        (Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) (D / 4)
          (1 / (D - 2))).symm
      _ ≤ (2 : ℝ) ^ 1 := Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) hexp
      _ = 2 := by norm_num
  have hBlt := derivativeWeylConstant_bounds.2.1
  have hBpos := derivativeWeylConstant_pos
  have hresult : derivativeWeylConstant *
      (K * (2 : ℝ) ^ (D / 4)) ^ (1 / (D - 2)) < 11 := by
    calc
      derivativeWeylConstant *
          (K * (2 : ℝ) ^ (D / 4)) ^ (1 / (D - 2)) <
        derivativeWeylConstant * ((2 : ℝ) ^ (D / 4)) ^ (1 / (D - 2)) :=
        mul_lt_mul_of_pos_left hpowLt hBpos
      _ ≤ derivativeWeylConstant * 2 :=
        mul_le_mul_of_nonneg_left hdyadic hBpos.le
      _ < 11 := by nlinarith
  have hbaseeq : K * (2 : ℝ) ^ (D / 4) =
      (81 / 8 : ℝ) * (2 / 3 : ℝ) ^ (2 * d) *
        (2 : ℝ) ^ (D / 4) *
        ((14 / 5 : ℝ) / derivativeWeylConstant) ^ 2 := by
    dsimp [K]
    ring
  rw [hbaseeq] at hresult
  simpa [D] using hresult

theorem derivative_c_large_coefficient_lt_eleven
    {h d : ℕ} {D : ℝ} (hhd : h + 2 = d) (hh : 3 ≤ h)
    (hD : D = (2 : ℝ) ^ d) :
    (derivativeWeylConstant *
      ((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
      (h : ℝ) ^ (2 * (h : ℝ) / D)) < 11 := by
  have hB := derivativeWeylConstant_bounds
  have hratio : (14 / 5 : ℝ) / derivativeWeylConstant < 1 :=
    lt_trans hB.2.2 (by norm_num)
  have hratioPos : 0 < (14 / 5 : ℝ) / derivativeWeylConstant :=
    div_pos (by norm_num) derivativeWeylConstant_pos
  have hDpos : 0 < D := by rw [hD]; positivity
  have hA : 0 < (14 / 5 : ℝ) := by norm_num
  have hbase : 0 < (14 / 5 : ℝ) * D / derivativeWeylConstant :=
    div_pos (mul_pos hA hDpos) derivativeWeylConstant_pos
  have hbaseLt : (14 / 5 : ℝ) * D / derivativeWeylConstant < D := by
    calc
      (14 / 5 : ℝ) * D / derivativeWeylConstant =
          ((14 / 5 : ℝ) / derivativeWeylConstant) * D := by ring
      _ < 1 * D := mul_lt_mul_of_pos_right hratio hDpos
      _ = D := by ring
  have hfirst :
      ((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) <
        D ^ (4 / D) :=
    Real.rpow_lt_rpow hbase.le hbaseLt (div_pos (by norm_num) hDpos)
  have hnat : h ≤ 2 ^ (h - 1) := by
    have hmul := Nat.mul_le_pow (by decide : 2 ≠ 1) (h - 1)
    omega
  have hcast : (h : ℝ) ≤ (2 : ℝ) ^ (h - 1) := by exact_mod_cast hnat
  have hqnonneg : 0 ≤ 2 * (h : ℝ) / D := by positivity
  have hsecond := Real.rpow_le_rpow (Nat.cast_nonneg h) hcast hqnonneg
  have hsecondPos : 0 < (h : ℝ) ^ (2 * (h : ℝ) / D) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < h by omega)) _
  let E₁ : ℝ := (d : ℝ) * (4 / D)
  let E₂ : ℝ := ((h - 1 : ℕ) : ℝ) * (2 * (h : ℝ) / D)
  let E : ℝ := E₁ + E₂
  have hDpower : D ^ (4 / D) = (2 : ℝ) ^ E₁ := by
    calc
      D ^ (4 / D) = ((2 : ℝ) ^ d) ^ (4 / D) :=
        congrArg (fun z : ℝ => z ^ (4 / D)) hD
      _ = (2 : ℝ) ^ ((d : ℝ) * (4 / D)) :=
        (Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) d
          (4 / D)).symm
      _ = (2 : ℝ) ^ E₁ := by rfl
  have hsecondPower : ((2 : ℝ) ^ (h - 1)) ^ (2 * (h : ℝ) / D) =
      (2 : ℝ) ^ E₂ := by
    dsimp [E₂]
    exact (Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) (h - 1)
      (2 * (h : ℝ) / D)).symm
  have hcastSub : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
    have hhpos : 1 ≤ h := by omega
    rw [Nat.cast_sub hhpos]
    norm_num
  have hE : E = (2 * (h : ℝ) ^ 2 + 2 * (h : ℝ) + 8) / D := by
    dsimp [E, E₁, E₂]
    field_simp [ne_of_gt hDpos]
    rw [← hhd, hcastSub]
    push_cast
    ring
  have hnumNat := (derivative_constants_nat_growth d h).2 hh
  have hnum : 2 * (h : ℝ) ^ 2 + 2 * (h : ℝ) + 8 ≤ D := by
    rw [hD, ← hhd]
    exact_mod_cast hnumNat
  have hEone : E ≤ 1 := by
    rw [hE]
    exact (div_le_one₀ hDpos).2 hnum
  have hpowProduct :
      D ^ (4 / D) * ((2 : ℝ) ^ (h - 1)) ^ (2 * (h : ℝ) / D) =
        (2 : ℝ) ^ E := by
    rw [hDpower, hsecondPower]
    dsimp [E]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hfactor :
      ((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
          (h : ℝ) ^ (2 * (h : ℝ) / D) <
        (2 : ℝ) ^ E := by
    calc
      _ < D ^ (4 / D) * (h : ℝ) ^ (2 * (h : ℝ) / D) :=
        mul_lt_mul_of_pos_right hfirst hsecondPos
      _ ≤ D ^ (4 / D) * ((2 : ℝ) ^ (h - 1)) ^
          (2 * (h : ℝ) / D) :=
        mul_le_mul_of_nonneg_left hsecond
          (le_of_lt (Real.rpow_pos_of_pos hDpos _))
      _ = (2 : ℝ) ^ E := hpowProduct
  have hfactorLe : (2 : ℝ) ^ E ≤ 2 := by
    calc
      (2 : ℝ) ^ E ≤ (2 : ℝ) ^ 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hEone
      _ = 2 := by norm_num
  have hBlt := hB.2.1
  calc
    derivativeWeylConstant *
        ((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
        (h : ℝ) ^ (2 * (h : ℝ) / D) =
      derivativeWeylConstant *
        (((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
          (h : ℝ) ^ (2 * (h : ℝ) / D)) := by ring
    derivativeWeylConstant *
        (((14 / 5 : ℝ) * D / derivativeWeylConstant) ^ (4 / D) *
          (h : ℝ) ^ (2 * (h : ℝ) / D)) <
        derivativeWeylConstant * (2 : ℝ) ^ E :=
      mul_lt_mul_of_pos_left hfactor derivativeWeylConstant_pos
    _ ≤ derivativeWeylConstant * 2 :=
      mul_le_mul_of_nonneg_left hfactorLe derivativeWeylConstant_pos.le
    _ < 11 := by nlinarith

theorem derivative_rpow_half_sq (z : ℝ) (hz : 0 ≤ z) :
    (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
  calc
    (z ^ (1 / 2 : ℝ)) ^ 2 = (z ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
      (Real.rpow_natCast (z ^ (1 / 2 : ℝ)) 2).symm
    _ = z ^ ((1 / 2 : ℝ) * 2) :=
      (Real.rpow_mul hz (1 / 2 : ℝ) 2).symm
    _ = z := by norm_num [Real.rpow_one]

theorem derivative_rpow_quarter_fourth (z : ℝ) (hz : 0 ≤ z) :
    (z ^ (1 / 4 : ℝ)) ^ 4 = z := by
  calc
    (z ^ (1 / 4 : ℝ)) ^ 4 = (z ^ (1 / 4 : ℝ)) ^ (4 : ℝ) :=
      (Real.rpow_natCast (z ^ (1 / 4 : ℝ)) 4).symm
    _ = z ^ ((1 / 4 : ℝ) * 4) :=
      (Real.rpow_mul hz (1 / 4 : ℝ) 4).symm
    _ = z := by norm_num [Real.rpow_one]


end FractionalPrimes

end
