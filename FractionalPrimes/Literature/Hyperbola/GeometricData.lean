module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Set.OrdConnected

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

open Set

/-- The exact constant `D=8K₀²` from the hyperbola geometry package. -/
def D (K₀ : ℝ) : ℝ := 8 * K₀ ^ 2

/-- The exact constant `E=3+K₀²` from the hyperbola geometry package. -/
def E (K₀ : ℝ) : ℝ := 3 + K₀ ^ 2

/-- The exact line-count constant `C_line=8(E+D²)+1`. -/
def C_line (K₀ : ℝ) : ℝ := 8 * (E K₀ + (D K₀) ^ 2) + 1

/-- The exact point-count constant `C_point=64(1+E)+144D(1+D)`. -/
def C_point (K₀ : ℝ) : ℝ :=
  64 * (1 + E K₀) + 144 * D K₀ * (1 + D K₀)

/-- The exact total geometric constant `C_geo=2(C_point+C_line)+8+E`. -/
def C_geo (K₀ : ℝ) : ℝ :=
  2 * (C_point K₀ + C_line K₀) + 8 + E K₀

/-- The lattice points in the source's hyperbola strip, with integer
coordinates cast into the real membership and product inequalities. -/
def hyperbolaLatticeSet (X H : ℝ) (J : Set ℝ) : Set (ℤ × ℤ) :=
  {p | (p.1 : ℝ) ∈ J ∧ X < (p.1 : ℝ) * (p.2 : ℝ) ∧
    (p.1 : ℝ) * (p.2 : ℝ) ≤ X + H}

/-- The finite set of points in a progression of spacing `(q,-a)` and
positive point-count length `N`, indexed by `j=0,…,N-1`. -/
def latticeProgression (z : ℤ × ℤ) (q a : ℤ) (N : ℕ) (_hN : 0 < N) :
    Finset (ℤ × ℤ) :=
  Finset.univ.image fun j : Fin N =>
    (z.1 + (j.val : ℤ) * q, z.2 - (j.val : ℤ) * a)

/-- A nonzero spacing vector makes the progression's point count exactly its
length. In particular, this holds for the positive `q` used by the rational
cells. -/
theorem latticeProgression_card_of_nonzero_spacing
    (z : ℤ × ℤ) (q a : ℤ) (N : ℕ) (hN : 0 < N)
    (hstep : q ≠ 0 ∨ a ≠ 0) :
    (latticeProgression z q a N hN).card = N := by
  classical
  have hinj : Set.InjOn
      (fun j : Fin N =>
        (z.1 + (j.val : ℤ) * q, z.2 - (j.val : ℤ) * a))
      (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)) := by
    intro i hi j hj hij
    apply Fin.ext
    rcases hstep with hq | ha
    · have hfst := congrArg Prod.fst hij
      have hmul : (i.val : ℤ) * q = (j.val : ℤ) * q := add_left_cancel hfst
      have hval : (i.val : ℤ) = (j.val : ℤ) :=
        mul_right_cancel₀ hq hmul
      exact_mod_cast hval
    · have hsnd := congrArg Prod.snd hij
      have hmul : (i.val : ℤ) * a = (j.val : ℤ) * a := by linarith [hsnd]
      have hval : (i.val : ℤ) = (j.val : ℤ) :=
        mul_right_cancel₀ ha hmul
      exact_mod_cast hval
  unfold latticeProgression
  rw [Finset.card_image_of_injOn hinj]
  simp

/-- Admissible geometric data from `lhg:data`. The order-convex set `J` may
be empty; no nonemptiness assumption is included. -/
structure HyperbolaGeometricData where
  K₀ : ℝ
  X : ℝ
  H : ℝ
  M : ℝ
  Q : ℕ
  J : Set ℝ
  K₀_ge_one : 1 ≤ K₀
  X_ge_one : 1 ≤ X
  H_ge_one : 1 ≤ H
  M_ge_one : 1 ≤ M
  Q_pos : 0 < Q
  J_orderConvex : Set.OrdConnected J
  J_subset : J ⊆ Set.Ioc M (2 * M)
  X_cuberoot_le_H : Real.rpow X (1 / 3 : ℝ) ≤ H
  H_le_X : H ≤ X
  M_le_K₀_sqrtX : M ≤ K₀ * Real.sqrt X
  M_div_H_le_Q : M / H ≤ (Q : ℝ)
  Q_le_M_div_fourthRoot : (Q : ℝ) ≤ M / Real.sqrt (Real.sqrt (H * X))

/-- The blueprint name for the package of admissible hyperbola geometry. -/
abbrev geometricData := HyperbolaGeometricData

namespace HyperbolaGeometricData

/-- The exact ratio `r=X/M²`. -/
noncomputable def r (g : HyperbolaGeometricData) : ℝ := g.X / g.M ^ 2

/-- The exact scale `L₀=HQ/M`, with the integer `Q` cast to the reals. -/
noncomputable def L0 (g : HyperbolaGeometricData) : ℝ :=
  g.H * (g.Q : ℝ) / g.M

/-- The source's lattice set `𝓗` for admissible data. -/
def lattice (g : HyperbolaGeometricData) : Set (ℤ × ℤ) :=
  hyperbolaLatticeSet g.X g.H g.J

end HyperbolaGeometricData

end FractionalPrimes.Literature.Hyperbola
