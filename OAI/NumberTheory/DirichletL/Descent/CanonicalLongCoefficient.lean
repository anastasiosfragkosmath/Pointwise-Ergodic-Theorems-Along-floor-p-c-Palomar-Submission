/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Descent/CanonicalLongCoefficient.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongSource
@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

def actualLongCoefficient {ι:Type*}(p:ι→O)(Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)
    (I:Ideal O)(v:ι→₀ℕ) : ℂ :=
  separatedCubeCoefficient
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ v

theorem actualLongCoefficient_uniform (eps:ℝ)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}(p:ι→O)(_hp:∀i,p i≠0)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)
      (m:O)(H₀ B ξ:ℝ)(I:Ideal O)(v:ι→₀ℕ),0<B→
      B≤‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2→
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B→
      ‖actualLongCoefficient p Ψ m H₀ B ξ I v‖≤C*(Real.exp 1*B)^eps := by
  obtain ⟨C,hC,hbound⟩:=reopenedCubeCoefficient_small_power eps heps
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro ι p hp Ψ hΨ m H₀ B ξ I v hB hlo hhi
  have hne:Ideal.span {primeProduct p v.support v}≠0 := by
    apply Ideal.span_singleton_eq_bot.not.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun i hi=>pow_ne_zero _ (hp i))
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hlo hhi
  have hh:=hbound H₀ (rowTwist Ψ m (idealGenerator I) 1)
    (rowTwist_norm Ψ hΨ m (idealGenerator I) 1) _ hne
  have hb:‖reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p v.support v})‖≤C*(Real.exp 1*B)^eps :=
    hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhi heps.le) hC.le)
  have hs:=separatedCubeCoefficient_bound
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ
    (C*(Real.exp 1*B)^eps) hB (by positivity) v hlo hhi hb
  unfold actualLongCoefficient
  convert hs using 1 ; ring

theorem actualLongCoefficient_complete
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)(I:Ideal O)
    (v:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ) :
    actualLongCoefficient (poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D))
      Ψ (m*excludedGenerator S) H₀ B ξ I v=
    separatedCubeCoefficient
      (fun u=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1)
        (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
      (fun u=>(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u):ℝ)) B ξ v := by
  simp only [actualLongCoefficient,cubeIdeal_eq_primeProduct_span _
    (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]

end SevenEighths.InverseMoment

end

end OAI
