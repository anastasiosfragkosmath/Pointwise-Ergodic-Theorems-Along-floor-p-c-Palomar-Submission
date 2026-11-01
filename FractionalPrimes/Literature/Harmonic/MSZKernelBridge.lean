module

public import FractionalPrimes.Literature.Harmonic.LocalizedSquareEstimate
public import FractionalPrimes.Literature.Harmonic.DyadicSpectralError
public import FractionalPrimes.Literature.MSZ.AdmissibleData

/-! The exact finite unweighted kernel as positive MSZ data. -/

@[expose] public section

open scoped ENNReal BigOperators

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

open FractionalPrimes.Literature.MSZ

theorem integerL1Kernel_ext (K L : IntegerL1Kernel)
    (h : K.coeff = L.coeff) : K = L := by
  cases K with
  | mk a ha =>
    cases L with
    | mk b hb =>
      cases h
      rfl

/-- Real nonnegative coefficient of the paper's finite unweighted kernel. -/
noncomputable def floorPowerRealKernelCoeff
    (c : ℝ) (N : Scale) (m : ℤ) : ℝ :=
  (N.1 : ℝ)⁻¹ *
    ∑ n ∈ Finset.Icc 1 N.1,
      if floorPower c n = m then (1 : ℝ) else 0

theorem floorPowerRealKernelCoeff_nonneg
    (c : ℝ) (N : Scale) (m : ℤ) :
    0 ≤ floorPowerRealKernelCoeff c N m := by
  dsimp [floorPowerRealKernelCoeff]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n hn => by split_ifs <;> norm_num)

theorem floorPowerRealKernelCoeff_complex
    (c : ℝ) (N : Scale) (m : ℤ) :
    (floorPowerRealKernelCoeff c N m : ℂ) =
      (floorPowerKernel c N).coeff m := by
  classical
  simp [floorPowerRealKernelCoeff, floorPowerKernel,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum]

theorem floorPowerRealKernelCoeff_eq_complexNorm
    (c : ℝ) (N : Scale) (m : ℤ) :
    floorPowerRealKernelCoeff c N m =
      ‖(floorPowerKernel c N).coeff m‖ := by
  rw [← floorPowerRealKernelCoeff_complex c N m, Complex.norm_real,
    Real.norm_of_nonneg (floorPowerRealKernelCoeff_nonneg c N m)]

/-- The paper's finite unweighted average gives a positive probability
kernel in the exact MSZ representation. -/
noncomputable def floorPowerMSZKernel (c : ℝ) (N : Scale) : MSZKernel where
  coeff := floorPowerRealKernelCoeff c N
  nonneg := floorPowerRealKernelCoeff_nonneg c N
  summable_norm := by
    have h : Summable (fun m : ℤ => floorPowerRealKernelCoeff c N m) := by
      simpa only [floorPowerRealKernelCoeff_eq_complexNorm] using
        (floorPowerKernel c N).summable_norm
    simpa only [Real.norm_of_nonneg (floorPowerRealKernelCoeff_nonneg c N _)] using h
  mass_le_one := by
    calc
      (∑' m : ℤ, floorPowerRealKernelCoeff c N m) =
          ∑' m : ℤ, ‖(floorPowerKernel c N).coeff m‖ := by
            apply tsum_congr
            intro m
            exact floorPowerRealKernelCoeff_eq_complexNorm c N m
      _ ≤ 1 := floorPowerKernel_norm_tsum_le_one c N

/-- The MSZ positive kernel is exactly the already verified complex
kernel, not a new averaging definition. -/
theorem floorPowerMSZKernel_toIntegerL1Kernel
    (c : ℝ) (N : Scale) :
    (floorPowerMSZKernel c N).toIntegerL1Kernel = floorPowerKernel c N := by
  apply integerL1Kernel_ext
  funext m
  exact floorPowerRealKernelCoeff_complex c N m

#print axioms floorPowerMSZKernel_toIntegerL1Kernel

/-- Convex combinations preserve the exact positive mass-one MSZ
kernel interface. -/
noncomputable def convexMSZKernel (K L : MSZKernel) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : MSZKernel where
  coeff m := (1 - a) * K.coeff m + a * L.coeff m
  nonneg m := by
    exact add_nonneg
      (mul_nonneg (by linarith) (K.nonneg m))
      (mul_nonneg ha0 (L.nonneg m))
  summable_norm := by
    have hK : Summable K.coeff := by
      apply K.summable_norm.congr
      intro m
      rw [Real.norm_of_nonneg (K.nonneg m)]
    have hL : Summable L.coeff := by
      apply L.summable_norm.congr
      intro m
      rw [Real.norm_of_nonneg (L.nonneg m)]
    have hsum : Summable (fun m : ℤ =>
        (1 - a) * K.coeff m + a * L.coeff m) :=
      (hK.mul_left _).add (hL.mul_left _)
    apply hsum.congr
    intro m
    rw [Real.norm_of_nonneg (add_nonneg
      (mul_nonneg (by linarith) (K.nonneg m))
      (mul_nonneg ha0 (L.nonneg m)))]
  mass_le_one := by
    have hK : Summable K.coeff := by
      apply K.summable_norm.congr
      intro m
      rw [Real.norm_of_nonneg (K.nonneg m)]
    have hL : Summable L.coeff := by
      apply L.summable_norm.congr
      intro m
      rw [Real.norm_of_nonneg (L.nonneg m)]
    have hsum : (∑' m : ℤ,
        ((1 - a) * K.coeff m + a * L.coeff m)) =
        (1 - a) * (∑' m : ℤ, K.coeff m) +
          a * (∑' m : ℤ, L.coeff m) := by
      rw [(hK.mul_left _).tsum_add (hL.mul_left _),
        tsum_mul_left, tsum_mul_left]
    rw [hsum]
    have hKbound := mul_le_mul_of_nonneg_left K.mass_le_one (by linarith : 0 ≤ 1 - a)
    have hLbound := mul_le_mul_of_nonneg_left L.mass_le_one ha0
    nlinarith

#print axioms convexMSZKernel

/-- The paper's time-interpolated finite averaging kernel at every
positive dyadic rational MSZ time. -/
noncomputable def interpolatedFloorPowerMSZKernel
    (c : ℝ) (t : MSZTime) : MSZKernel := by
  let s : ℝ := (t.val : ℝ)
  by_cases hs1 : s ≤ 1
  · exact floorPowerMSZKernel c ⟨1, by norm_num⟩
  · have hspos : 0 < s := by
      dsimp [s]
      exact_mod_cast mszTime_pos t
    have hs : 1 < s := lt_of_not_ge hs1
    let N : ℕ := ⌊s⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      exact Nat.le_floor (by exact_mod_cast hs.le)
    let a : ℝ := s - (N : ℝ)
    have ha0 : 0 ≤ a := by
      dsimp [a, N]
      exact sub_nonneg.mpr (Nat.floor_le (by linarith))
    have ha1 : a ≤ 1 := by
      dsimp [a, N]
      have hnext := Nat.lt_floor_add_one s
      exact (sub_le_iff_le_add).2 (by linarith)
    exact convexMSZKernel
      (floorPowerMSZKernel c ⟨N, by omega⟩)
      (floorPowerMSZKernel c ⟨N + 1, by omega⟩)
      a ha0 ha1

#print axioms interpolatedFloorPowerMSZKernel

/-- The abstract MSZ dyadic grid time is exactly the time used by the
paper's localized increment operator after casting to reals. -/
theorem mszGridTime_real_eq_localizedDyadicLeftTime
    (k : ℤ) (l m : ℕ) :
    ((mszGridTime k l m).val : ℝ) =
      localizedDyadicLeftTime k l m := by
  have hpow : (2 : ℝ) ^ l * (2 : ℝ) ^ (k - (l : ℤ)) =
      (2 : ℝ) ^ k := by
    calc
      (2 : ℝ) ^ l * (2 : ℝ) ^ (k - (l : ℤ)) =
          (2 : ℝ) ^ (l : ℤ) * (2 : ℝ) ^ (k - (l : ℤ)) := by
            rw [zpow_natCast]
      _ = (2 : ℝ) ^ ((l : ℤ) + (k - (l : ℤ))) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (2 : ℝ) ^ k := by congr 1 <;> omega
  rw [mszGridTime_val]
  norm_cast
  unfold localizedDyadicLeftTime
  push_cast
  calc
    ((2 : ℝ) ^ l + (m : ℝ)) * (2 : ℝ) ^ (k - (l : ℤ)) =
        (2 : ℝ) ^ l * (2 : ℝ) ^ (k - (l : ℤ)) +
          (2 : ℝ) ^ (k - (l : ℤ)) * (m : ℝ) := by ring
    _ = _ := by rw [hpow]

#print axioms mszGridTime_real_eq_localizedDyadicLeftTime

/-- At every positive integer time, the MSZ kernel acts exactly as
the existing transferred unweighted `ℓ²` average. -/
theorem floorPowerMSZKernel_average_eq_localizedInteger
    (c : ℝ) (N : Scale) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    mszKernelAverage (floorPowerMSZKernel c N) (f : ℤ → ℂ) x =
      localizedIntegerUnweightedAverageL2 c N f x := by
  rw [mszKernelAverage, floorPowerMSZKernel_toIntegerL1Kernel]
  rw [← unweightedAverage_integerShift_eq_integerKernelConvolution]
  rw [localizedIntegerUnweightedAverageL2_apply]
  simp [unweightedAverage, weightedAverage, integerShiftSystem_iterate_apply]

#print axioms floorPowerMSZKernel_average_eq_localizedInteger

/-- Exact pointwise linearity of positive-kernel convolution in the
kernel argument on `ℓ²` inputs. -/
theorem convexMSZKernel_average_eq
    (K L : MSZKernel) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    mszKernelAverage (convexMSZKernel K L a ha0 ha1) (f : ℤ → ℂ) x =
      ((1 - a : ℝ) : ℂ) * mszKernelAverage K (f : ℤ → ℂ) x +
        (a : ℂ) * mszKernelAverage L (f : ℤ → ℂ) x := by
  let Kc := (convexMSZKernel K L a ha0 ha1).toIntegerL1Kernel
  let K₁ := K.toIntegerL1Kernel
  let K₂ := L.toIntegerL1Kernel
  have hKc := integerKernelConvolutionExistsAt_of_lpL2 Kc f x
  have hK₁ := integerKernelConvolutionExistsAt_of_lpL2 K₁ f x
  have hK₂ := integerKernelConvolutionExistsAt_of_lpL2 K₂ f x
  have hs₁ : Summable (fun m : ℤ => K₁.coeff m * f (x - m)) :=
    (MeasureTheory.integrable_count_iff.mp hK₁).of_norm
  have hs₂ : Summable (fun m : ℤ => K₂.coeff m * f (x - m)) :=
    (MeasureTheory.integrable_count_iff.mp hK₂).of_norm
  have hcoeff (m : ℤ) : Kc.coeff m =
      ((1 - a : ℝ) : ℂ) * K₁.coeff m + (a : ℂ) * K₂.coeff m := by
    simp [Kc, K₁, K₂, convexMSZKernel, MSZKernel.toIntegerL1Kernel,
      Complex.ofReal_add, Complex.ofReal_mul]
  rw [mszKernelAverage, mszKernelAverage, mszKernelAverage]
  rw [integerKernelConvolution_eq_tsum Kc _ x hKc,
    integerKernelConvolution_eq_tsum K₁ _ x hK₁,
    integerKernelConvolution_eq_tsum K₂ _ x hK₂]
  calc
    (∑' m : ℤ, Kc.coeff m * f (x - m)) =
        ∑' m : ℤ,
          (((1 - a : ℝ) : ℂ) * (K₁.coeff m * f (x - m)) +
            (a : ℂ) * (K₂.coeff m * f (x - m))) := by
      apply tsum_congr
      intro m
      rw [hcoeff]
      ring
    _ = ((1 - a : ℝ) : ℂ) *
          (∑' m : ℤ, K₁.coeff m * f (x - m)) +
        (a : ℂ) * (∑' m : ℤ, K₂.coeff m * f (x - m)) := by
      rw [(hs₁.mul_left _).tsum_add (hs₂.mul_left _),
        tsum_mul_left, tsum_mul_left]

#print axioms convexMSZKernel_average_eq

/-- The positive MSZ kernel at a dyadic rational time acts exactly as the
paper's piecewise interpolated averaging operator on `ℓ²`. -/
theorem interpolatedFloorPowerMSZKernel_average_eq_localized
    (c : ℝ) (t : MSZTime) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    mszKernelAverage (interpolatedFloorPowerMSZKernel c t) (f : ℤ → ℂ) x =
      localizedInterpolatedAverageL2 c (t.val : ℝ)
        (by exact_mod_cast mszTime_pos t) f x := by
  let s : ℝ := (t.val : ℝ)
  have hspos : 0 < s := by
    dsimp [s]
    exact_mod_cast mszTime_pos t
  by_cases hs1 : s ≤ 1
  · have hkernel : interpolatedFloorPowerMSZKernel c t =
        floorPowerMSZKernel c ⟨1, by norm_num⟩ := by
      simp [interpolatedFloorPowerMSZKernel, s, hs1]
    rw [hkernel, floorPowerMSZKernel_average_eq_localizedInteger]
    simp [localizedInterpolatedAverageL2, interpolatedUnweightedAverage,
      localizedIntegerUnweightedAverageL2,
      show (t.val : ℝ) ≤ 1 from hs1]
  · have hs : 1 < s := lt_of_not_ge hs1
    let N : ℕ := ⌊s⌋₊
    let a : ℝ := s - (N : ℝ)
    have ha0 : 0 ≤ a := by
      dsimp [a, N]
      exact sub_nonneg.mpr (Nat.floor_le (by linarith))
    have ha1 : a ≤ 1 := by
      dsimp [a, N]
      have hnext := Nat.lt_floor_add_one s
      exact (sub_le_iff_le_add).2 (by linarith)
    have hkernel : interpolatedFloorPowerMSZKernel c t =
        convexMSZKernel
          (floorPowerMSZKernel c ⟨N, by
            dsimp [N]
            exact Nat.le_floor (by exact_mod_cast hs.le)⟩)
          (floorPowerMSZKernel c ⟨N + 1, by omega⟩)
          a ha0 ha1 := by
      simp [interpolatedFloorPowerMSZKernel, s, hs1, N, a]
    rw [hkernel, convexMSZKernel_average_eq,
      floorPowerMSZKernel_average_eq_localizedInteger,
      floorPowerMSZKernel_average_eq_localizedInteger]
    have hcombo := localizedInterpolatedAverageL2_eq_convex_combo c s hs f
    have hpoint := congrArg (fun g : lp (fun _ : ℤ => ℂ) 2 => g x) hcombo
    simp only [lp.coeFn_add, lp.coeFn_smul] at hpoint
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply] at hpoint
    simpa [s, N, a, smul_eq_mul, Complex.real_smul] using hpoint.symm

#print axioms interpolatedFloorPowerMSZKernel_average_eq_localized

/-- Each finite MSZ grid increment is exactly the existing localized
interpolated `ℓ²` increment, with the source endpoint convention. -/
theorem mszGridIncrement_floorPower_eq_localized
    (c : ℝ) (k : ℤ) (l m : ℕ)
    (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    mszGridIncrement (interpolatedFloorPowerMSZKernel c)
      k l m (f : ℤ → ℂ) x =
      (localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
          (localizedDyadicRightTime_pos k l m) f -
        localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m)
          (localizedDyadicLeftTime_pos k l m) f) x := by
  have hright : ((mszGridTime k l (m + 1)).val : ℝ) =
      localizedDyadicLeftTime k l m + localizedDyadicMesh k l := by
    rw [mszGridTime_real_eq_localizedDyadicLeftTime]
    unfold localizedDyadicLeftTime localizedDyadicMesh
    push_cast
    ring
  simp only [mszGridIncrement, Pi.sub_apply]
  rw [interpolatedFloorPowerMSZKernel_average_eq_localized,
    interpolatedFloorPowerMSZKernel_average_eq_localized]
  simpa only [hright, mszGridTime_real_eq_localizedDyadicLeftTime,
    lp.coeFn_sub, Pi.sub_apply]

#print axioms mszGridIncrement_floorPower_eq_localized

/-- The exact kernel-grid component with the paper's signed frequency
projection agrees with the already checked localized square family. -/
theorem mszGridIncrement_projected_eq_localizedFamily
    (c : ℝ) (hc : 1 < c) (j : ℤ) (l : ℕ)
    (f : lp (fun _ : ℤ => ℂ) 2)
    (i : ℤ × Fin (2 ^ l)) (x : ℤ) :
    mszGridIncrement (interpolatedFloorPowerMSZKernel c)
      i.1 l i.2.val
      (localizedSignedFrequencyProjectionL2 c hc (j + i.1) f : ℤ → ℂ) x =
      localizedIncrementFamily c hc j l f i x := by
  rw [mszGridIncrement_floorPower_eq_localized]
  rfl

#print axioms mszGridIncrement_projected_eq_localizedFamily

/-- The paper's projected MSZ grid increments are square-summable at
every sequence coordinate; this is the pointwise summability field
required by the abstract short-variation data. -/
theorem mszGridIncrement_projected_square_summable
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    Summable (fun i : ℤ × Fin (2 ^ l) =>
      ‖mszGridIncrement (interpolatedFloorPowerMSZKernel c)
        i.1 l i.2.val
        (localizedSignedFrequencyProjectionL2 c hc (j + i.1) f : ℤ → ℂ) x‖ ^ 2) := by
  have henergy := (localizedIncrementFamily_energy c hc hcNon j l f).1
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) henergy
  rw [mszGridIncrement_projected_eq_localizedFamily]
  have hpoint := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (localizedIncrementFamily c hc j l f i) x
  nlinarith [norm_nonneg (localizedIncrementFamily c hc j l f i),
    norm_nonneg (localizedIncrementFamily c hc j l f i x)]

#print axioms mszGridIncrement_projected_square_summable

end

end FractionalPrimes.Literature.Harmonic

end
