module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import Mathlib.Data.Nat.GCD.Basic

/-!
# Sequential gcd allocation for Dirichlet convolution

The first step is the exact finite divisor reindexing which separates the
part of a divisor allocated to a modulus from the residual divisor of the
input.  This is the arithmetic core of `ltw:gcd-allocation`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity

def gcdAllocationPairFinset (r n : ℕ) : Finset (ℕ × ℕ) :=
  ((r.divisors ×ˢ n.divisors).filter fun z => Nat.Coprime z.2 (r / z.1))

private theorem mem_gcdAllocationPairFinset {r n : ℕ} (z : ℕ × ℕ) :
    z ∈ gcdAllocationPairFinset r n ↔
      z.1 ∈ r.divisors ∧ z.2 ∈ n.divisors ∧ Nat.Coprime z.2 (r / z.1) := by
  simp [gcdAllocationPairFinset, and_assoc, and_left_comm]

private theorem gcd_mul_div_left (d r : ℕ) :
    Nat.gcd d r * (d / Nat.gcd d r) = d := by
  calc
    Nat.gcd d r * (d / Nat.gcd d r) =
        (d / Nat.gcd d r) * Nat.gcd d r := by ac_rfl
    _ = d := Nat.div_mul_cancel (Nat.gcd_dvd_left d r)

private theorem gcd_mul_div_right (d r : ℕ) :
    Nat.gcd d r * (r / Nat.gcd d r) = r := by
  calc
    Nat.gcd d r * (r / Nat.gcd d r) =
        (r / Nat.gcd d r) * Nat.gcd d r := by ac_rfl
    _ = r := Nat.div_mul_cancel (Nat.gcd_dvd_right d r)

private theorem nat_min_mul_split (a b c : ℕ) :
    min (a + b) c = min a c + min b (c - min a c) := by
  omega

/-- Binary form of the sequential gcd allocation rule. -/
private theorem gcd_mul_split {a b r : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    Nat.gcd (a * b) r = Nat.gcd a r * Nat.gcd b (r / Nat.gcd a r) := by
  have hrespos : 0 < r / Nat.gcd a r :=
    Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right a r))
      (Nat.gcd_pos_of_pos_right a hr)
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_right (a * b) hr).ne'
    (mul_pos (Nat.gcd_pos_of_pos_right a hr)
      (Nat.gcd_pos_of_pos_right b hrespos)).ne'
  intro p
  conv_lhs =>
    rw [Nat.factorization_gcd (mul_ne_zero ha.ne' hb.ne') hr.ne',
      Nat.factorization_mul ha.ne' hb.ne']
  conv_rhs =>
    rw [Nat.factorization_mul (Nat.gcd_pos_of_pos_right a hr).ne'
        (Nat.gcd_pos_of_pos_right b hrespos).ne',
      Nat.factorization_gcd ha.ne' hr.ne',
      Nat.factorization_gcd hb.ne' hrespos.ne',
      Nat.factorization_div (Nat.gcd_dvd_right a r)]
  simp only [Nat.factorization_gcd ha.ne' hr.ne']
  change min (a.factorization p + b.factorization p) (r.factorization p) =
    min (a.factorization p) (r.factorization p) +
      min (b.factorization p)
        (r.factorization p - min (a.factorization p) (r.factorization p))
  exact nat_min_mul_split _ _ _

/-- Reindex a divisor of `r*n` by its exact gcd allocation to `r` and the
coprime residual divisor of `n`. -/
private theorem sum_divisors_gcdAllocationPairs
    {r n : ℕ} (hr : 0 < r) (hn : 0 < n) (F : ℕ → ℂ) :
    (∑ d ∈ (r * n).divisors, F d) =
      ∑ z ∈ gcdAllocationPairFinset r n, F (z.1 * z.2) := by
  classical
  refine Finset.sum_bij
    (fun d _ => (Nat.gcd d r, d / Nat.gcd d r)) ?_ ?_ ?_ ?_
  · intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hgcdpos : 0 < Nat.gcd d r := Nat.gcd_pos_of_pos_left r hdpos
    let g := Nat.gcd d r
    let m := d / g
    let s := r / g
    have hcop : Nat.Coprime m s := by
      simpa [m, s, g] using Nat.coprime_div_gcd_div_gcd hgcdpos
    have hdivrn : d ∣ r * n := (Nat.mem_divisors.mp hd).1
    have hgFactor : g * m = d := by
      simpa [g, m] using gcd_mul_div_left d r
    have hrFactor : g * s = r := by
      simpa [g, s] using gcd_mul_div_right d r
    have hresdiv : m ∣ n := by
      have hdivrn' := hdivrn
      rw [← hgFactor, ← hrFactor] at hdivrn'
      have hscaled : g * m ∣ g * (s * n) := by
        simpa [Nat.mul_assoc] using hdivrn'
      have hcancel := (Nat.mul_dvd_mul_iff_left hgcdpos).mp hscaled
      exact hcop.dvd_of_dvd_mul_left hcancel
    rw [mem_gcdAllocationPairFinset]
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d r, Nat.ne_of_gt hr⟩,
      Nat.mem_divisors.mpr ⟨hresdiv, Nat.ne_of_gt hn⟩,
      hcop⟩
  · intro d hd e he heq
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    change Nat.gcd d r = Nat.gcd e r at hfst
    change d / Nat.gcd d r = e / Nat.gcd e r at hsnd
    have hsnd' : d / Nat.gcd e r = e / Nat.gcd e r := by
      simpa [hfst] using hsnd
    calc
      d = Nat.gcd d r * (d / Nat.gcd d r) := (gcd_mul_div_left d r).symm
      _ = Nat.gcd e r * (e / Nat.gcd e r) := by rw [hfst, hsnd']
      _ = e := gcd_mul_div_left e r
  · intro z hz
    rcases (mem_gcdAllocationPairFinset z).mp hz with ⟨hzr, hzn, hcop⟩
    have hzrdiv : z.1 ∣ r := (Nat.mem_divisors.mp hzr).1
    have hzndiv : z.2 ∣ n := (Nat.mem_divisors.mp hzn).1
    have hzrpos : 0 < z.1 := Nat.pos_of_mem_divisors hzr
    have hzpos : 0 < z.2 := Nat.pos_of_mem_divisors hzn
    have hrFac : r = z.1 * (r / z.1) := by
      calc
        r = (r / z.1) * z.1 := (Nat.div_mul_cancel hzrdiv).symm
        _ = z.1 * (r / z.1) := by ac_rfl
    have hnFac : n = z.2 * (n / z.2) := by
      calc
        n = (n / z.2) * z.2 := (Nat.div_mul_cancel hzndiv).symm
        _ = z.2 * (n / z.2) := by ac_rfl
    have hprodDvd : z.1 * z.2 ∣ r * n := by
      refine ⟨(r / z.1) * (n / z.2), ?_⟩
      calc
        r * n = (z.1 * (r / z.1)) * (z.2 * (n / z.2)) := by
          conv_lhs => rw [hrFac, hnFac]
        _ = (z.1 * z.2) * ((r / z.1) * (n / z.2)) := by ac_rfl
    have hgcd : Nat.gcd (z.1 * z.2) r = z.1 := by
      rw [hrFac, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
    have hquot : (z.1 * z.2) / Nat.gcd (z.1 * z.2) r = z.2 := by
      rw [hgcd]
      exact Nat.mul_div_right z.2 hzrpos
    refine ⟨z.1 * z.2, Nat.mem_divisors.mpr ⟨hprodDvd,
      Nat.ne_of_gt (mul_pos hr hn)⟩, ?_⟩
    apply Prod.ext
    · exact hgcd
    · exact hquot
  · intro d hd
    change F d = F (Nat.gcd d r * (d / Nat.gcd d r))
    exact congrArg F (gcd_mul_div_left d r).symm

private noncomputable def complexArithmeticConvolutionTerm
    (f g : ArithmeticFunction ℂ) (N d : ℕ) : ℂ :=
  if _hd : d ∈ N.divisors then f d * g (N / d) else 0

private theorem complexArithmeticConvolution_apply_divisors
    (f g : ArithmeticFunction ℂ) (N : ℕ) :
    (f * g) N =
      ∑ d ∈ N.divisors, complexArithmeticConvolutionTerm f g N d := by
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (f := fun a b => f a * g b)]
  apply Finset.sum_congr rfl
  intro d hd
  simp [complexArithmeticConvolutionTerm, hd]

private theorem nat_mul_divisor_quotient_split
    {r n d m : ℕ} (hd : d ∈ r.divisors) (hm : m ∈ n.divisors) :
    (r * n) / (d * m) = (r / d) * (n / m) := by
  have hrdvd : d ∣ r := (Nat.mem_divisors.mp hd).1
  have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hmpos : 0 < m := Nat.pos_of_mem_divisors hm
  have hrFac : r = d * (r / d) := by
    calc
      r = (r / d) * d := (Nat.div_mul_cancel hrdvd).symm
      _ = d * (r / d) := by ac_rfl
  have hnFac : n = m * (n / m) := by
    calc
      n = (n / m) * m := (Nat.div_mul_cancel hmdvd).symm
      _ = m * (n / m) := by ac_rfl
  calc
    (r * n) / (d * m) = ((d * m) * ((r / d) * (n / m))) / (d * m) := by
      congr 1
      calc
        r * n = (d * (r / d)) * (m * (n / m)) := by
          conv_lhs => rw [hrFac, hnFac]
        _ = (d * m) * ((r / d) * (n / m)) := by ac_rfl
    _ = (r / d) * (n / m) :=
      Nat.mul_div_cancel_left _ (mul_pos hdpos hmpos)

private theorem complexArithmeticConvolutionTerm_gcdPair
    (f g : ArithmeticFunction ℂ) {r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (z : ℕ × ℕ) (hz : z ∈ gcdAllocationPairFinset r n) :
    complexArithmeticConvolutionTerm f g (r * n) (z.1 * z.2) =
      f (z.1 * z.2) * g ((r / z.1) * (n / z.2)) := by
  rcases (mem_gcdAllocationPairFinset z).mp hz with ⟨hzr, hzn, _⟩
  have hzrdiv : z.1 ∣ r := (Nat.mem_divisors.mp hzr).1
  have hzndiv : z.2 ∣ n := (Nat.mem_divisors.mp hzn).1
  have hzrpos : 0 < z.1 := Nat.pos_of_mem_divisors hzr
  have hzpos : 0 < z.2 := Nat.pos_of_mem_divisors hzn
  have hrFac : r = z.1 * (r / z.1) := by
    calc
      r = (r / z.1) * z.1 := (Nat.div_mul_cancel hzrdiv).symm
      _ = z.1 * (r / z.1) := by ac_rfl
  have hnFac : n = z.2 * (n / z.2) := by
    calc
      n = (n / z.2) * z.2 := (Nat.div_mul_cancel hzndiv).symm
      _ = z.2 * (n / z.2) := by ac_rfl
  have hprodDvd : z.1 * z.2 ∣ r * n := by
    refine ⟨(r / z.1) * (n / z.2), ?_⟩
    calc
      r * n = (z.1 * (r / z.1)) * (z.2 * (n / z.2)) := by
        conv_lhs => rw [hrFac, hnFac]
      _ = (z.1 * z.2) * ((r / z.1) * (n / z.2)) := by ac_rfl
  have hmem : z.1 * z.2 ∈ (r * n).divisors :=
    Nat.mem_divisors.mpr ⟨hprodDvd, Nat.ne_of_gt (mul_pos hr hn)⟩
  have hquot := nat_mul_divisor_quotient_split hzr hzn
  simp [complexArithmeticConvolutionTerm, hmem, hquot]

/-- The recursively expanded right side of exact sequential gcd allocation.
Each step chooses the factor allocated to the current convolution factor and
the coprime residual divisor of the remaining input. -/
noncomputable def sequentialGcdAllocatedExpansion :
    List (ArithmeticFunction ℂ) → ℕ → ℕ → ℂ
  | [], r, n => if r * n = 1 then 1 else 0
  | f :: fs, r, n =>
      ∑ z ∈ gcdAllocationPairFinset r n,
        f (z.1 * z.2) * sequentialGcdAllocatedExpansion fs (r / z.1) (n / z.2)

/-- The exact allocated factor `m ↦ a(d*m) 1_{(m,s)=1}` appearing in
`ltw:gcd-allocation`. -/
noncomputable def sequentialGcdAllocatedFactor
    (f : ArithmeticFunction ℂ) (d s : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun m => if Nat.Coprime m s then f (d * m) else 0, by simp⟩

/-- Finite divisor-sum form of Dirichlet convolution, used to expose each
allocated factor without losing its label. -/
def complexNaturalDirichletConvolution
    (f : ℕ → ℂ) (g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ m ∈ n.divisors, f m * g (n / m)

/-- Source-style recursive sum over ordered factorizations.  The recursion
chooses the first labeled factor `d` of `r`; the summand is the convolution
of its exact coprime-cutoff factor with the allocation of the remaining
labeled factors. -/
noncomputable def sequentialGcdAllocatedConvolution :
    List (ArithmeticFunction ℂ) → ℕ → ℕ → ℂ
  | [], r, n => if r * n = 1 then 1 else 0
  | f :: fs, r, n =>
      ∑ d ∈ r.divisors,
        complexNaturalDirichletConvolution
          (sequentialGcdAllocatedFactor f d (r / d))
          (fun m => sequentialGcdAllocatedConvolution fs (r / d) m) n

private theorem sum_gcdAllocationPairFinset_eq_nested
    {r n : ℕ} (F : ℕ → ℕ → ℂ) :
    (∑ z ∈ gcdAllocationPairFinset r n, F z.1 z.2) =
      ∑ d ∈ r.divisors, ∑ m ∈ n.divisors,
        if Nat.Coprime m (r / d) then F d m else 0 := by
  classical
  simp only [gcdAllocationPairFinset, Finset.sum_filter, Finset.sum_product]

/-- Exact sequential gcd allocation, in the recursively expanded form of the
source's sum over ordered factorizations and the corresponding convolutions.
The identity holds for arbitrary arithmetic functions, so in particular for
the finitely supported coefficients of `ltw:gcd-allocation`. -/
private theorem sequentialGcdAllocation_expanded
    (fs : List (ArithmeticFunction ℂ)) {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    (fs.prod) (r * n) = sequentialGcdAllocatedExpansion fs r n := by
  induction fs generalizing r n with
  | nil =>
      simp only [List.prod_nil, ArithmeticFunction.one_apply,
        sequentialGcdAllocatedExpansion]
  | cons f fs ih =>
      rw [List.prod_cons, complexArithmeticConvolution_apply_divisors]
      rw [sum_divisors_gcdAllocationPairs hr hn
        (complexArithmeticConvolutionTerm f fs.prod (r * n))]
      apply Finset.sum_congr rfl
      intro z hz
      rw [complexArithmeticConvolutionTerm_gcdPair f fs.prod hr hn z hz]
      rcases (mem_gcdAllocationPairFinset z).mp hz with ⟨hzr, hzn, _⟩
      have hzrpos : 0 < z.1 := Nat.pos_of_mem_divisors hzr
      have hzpos : 0 < z.2 := Nat.pos_of_mem_divisors hzn
      have hzrdiv : z.1 ∣ r := (Nat.mem_divisors.mp hzr).1
      have hzndiv : z.2 ∣ n := (Nat.mem_divisors.mp hzn).1
      have hresr : 0 < r / z.1 :=
        Nat.div_pos (Nat.le_of_dvd hr hzrdiv) hzrpos
      have hresn : 0 < n / z.2 :=
        Nat.div_pos (Nat.le_of_dvd hn hzndiv) hzpos
      exact congrArg (fun w => f (z.1 * z.2) * w) (ih hresr hresn)

private theorem sequentialGcdAllocatedConvolution_eq_expansion
    (fs : List (ArithmeticFunction ℂ)) {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    sequentialGcdAllocatedConvolution fs r n = sequentialGcdAllocatedExpansion fs r n := by
  induction fs generalizing r n with
  | nil =>
      rfl
  | cons f fs ih =>
      calc
        sequentialGcdAllocatedConvolution (f :: fs) r n =
            ∑ d ∈ r.divisors, ∑ m ∈ n.divisors,
              sequentialGcdAllocatedFactor f d (r / d) m *
                sequentialGcdAllocatedConvolution fs (r / d) (n / m) := by
          simp only [sequentialGcdAllocatedConvolution]
          apply Finset.sum_congr rfl
          intro d hd
          rw [complexNaturalDirichletConvolution]
        _ = ∑ d ∈ r.divisors, ∑ m ∈ n.divisors,
              if Nat.Coprime m (r / d) then
                f (d * m) * sequentialGcdAllocatedExpansion fs (r / d) (n / m)
              else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro m hm
          have hrdvd : d ∣ r := (Nat.mem_divisors.mp hd).1
          have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
          have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
          have hmpos : 0 < m := Nat.pos_of_mem_divisors hm
          have hresr : 0 < r / d := Nat.div_pos (Nat.le_of_dvd hr hrdvd) hdpos
          have hresn : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmdvd) hmpos
          by_cases hcop' : Nat.Coprime m (r / d)
          · simp [sequentialGcdAllocatedFactor, ih hresr hresn]
          · simp [sequentialGcdAllocatedFactor, hcop']
        _ = ∑ z ∈ gcdAllocationPairFinset r n,
              f (z.1 * z.2) * sequentialGcdAllocatedExpansion fs (r / z.1) (n / z.2) := by
          exact (sum_gcdAllocationPairFinset_eq_nested
            (fun d m => f (d * m) *
              sequentialGcdAllocatedExpansion fs (r / d) (n / m))).symm

/-- Exact sequential gcd allocation: the convolution product at `r*n` is the
source-style sum over labeled ordered factorizations of `r`, with each factor
replaced by its exact allocated cutoff. -/
theorem sequentialGcdAllocation
    (fs : List (ArithmeticFunction ℂ)) {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    (fs.prod) (r * n) = sequentialGcdAllocatedConvolution fs r n := by
  rw [sequentialGcdAllocation_expanded fs hr hn]
  exact (sequentialGcdAllocatedConvolution_eq_expansion fs hr hn).symm

/-- The deterministic ordered allocation produced by successively taking
`gcd(nᵢ, rᵢ₋₁)`. -/
def sequentialGcdAllocationParts (r : ℕ) : List PositiveInteger → List ℕ
  | [] => []
  | n :: ns =>
      Nat.gcd n.1 r :: sequentialGcdAllocationParts (r / Nat.gcd n.1 r) ns

private theorem positiveIntegerListProduct_pos (ns : List PositiveInteger) :
    0 < (ns.map Subtype.val).prod := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_pos n.2 ih

/-- The sequential allocated factors have product exactly
`gcd(n₁⋯nₖ,r)`, the second assertion in `ltw:gcd-allocation`. -/
theorem sequentialGcdAllocationParts_product
    (r : ℕ) (hr : 0 < r) (ns : List PositiveInteger) :
    (sequentialGcdAllocationParts r ns).prod =
      Nat.gcd (ns.map Subtype.val).prod r := by
  induction ns generalizing r with
  | nil => simp [sequentialGcdAllocationParts]
  | cons n ns ih =>
      have htailpos := positiveIntegerListProduct_pos ns
      have hrespos : 0 < r / Nat.gcd n.1 r :=
        Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right n.1 r))
          (Nat.gcd_pos_of_pos_right n.1 hr)
      simp only [sequentialGcdAllocationParts, List.prod_cons, List.map_cons]
      calc
        Nat.gcd n.1 r *
            (sequentialGcdAllocationParts (r / Nat.gcd n.1 r) ns).prod =
            Nat.gcd n.1 r * Nat.gcd (ns.map Subtype.val).prod
              (r / Nat.gcd n.1 r) := by
                rw [ih (r / Nat.gcd n.1 r) hrespos]
        _ = Nat.gcd (n.1 * (ns.map Subtype.val).prod) r :=
          (gcd_mul_split n.2 htailpos hr).symm

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.sequentialGcdAllocation
#print axioms FractionalPrimes.Literature.Twisted.sequentialGcdAllocationParts_product
