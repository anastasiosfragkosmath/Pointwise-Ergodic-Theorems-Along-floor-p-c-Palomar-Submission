import Lake
open Lake DSL
package FractionalPrimesSubmission where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"
lean_lib OAI where
  roots := #[`OAI.NumberTheory.DirichletL.Nonvanishing]
  globs := #[`OAI.+]
lean_lib RellichKondrachov
lean_lib PrimeNumberTheoremAnd
lean_lib FractionalPrimes
@[default_target]
lean_lib Solution where
  roots := #[`Solution]

@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib FinalDevelopment where
  roots := #[`FinalDevelopment]

@[default_target]
lean_lib FinalSolution where
  roots := #[`FinalSolution]

@[default_target]
lean_lib FinalChallengeStatements where
  roots := #[`FinalChallengeStatements]
