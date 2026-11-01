module

public import FractionalPrimes.Literature.DirichletAdapter.ResidueAffineSchwartz

/-! Removing the constant term from an absolutely summable integer Fourier series. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

theorem norm_tsum_sub_zero_le
    (a : ℤ → ℂ) (ha : Summable a) :
    ‖(∑' k : ℤ, a k) - a 0‖ ≤
      ∑' k : ℤ, if k = 0 then (0 : ℝ) else ‖a k‖ := by
  have hrest : Summable (fun k : ℤ => if k = 0 then (0 : ℂ) else a k) :=
    ha.congr_cofinite (by
      filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with k hk
      simp [hk])
  have hnorm : Summable (fun k : ℤ =>
      ‖if k = 0 then (0 : ℂ) else a k‖) := hrest.norm
  rw [ha.tsum_eq_add_tsum_ite 0]
  simp only [add_sub_cancel_left]
  calc
    ‖∑' k : ℤ, if k = 0 then (0 : ℂ) else a k‖ ≤
        ∑' k : ℤ, ‖if k = 0 then (0 : ℂ) else a k‖ :=
          norm_tsum_le_tsum_norm hnorm
    _ = ∑' k : ℤ, if k = 0 then (0 : ℝ) else ‖a k‖ := by
          congr 1
          funext k
          split_ifs <;> simp

#print axioms norm_tsum_sub_zero_le

end FractionalPrimes.Literature.DirichletAdapter

end
