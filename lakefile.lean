import Lake
open Lake DSL

package "lean4-formal-proofs" where
  version := v!"0.1.0"
  keywords := #["lean4", "formal-methods", "theorem-proving", "mathematics"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Lean4Foundations» where
  -- Module roots: Lean4Foundations.lean, BasicLogic, NumberTheory, DataStructures
