import Lake
open Lake DSL

package «matheye-proof-builder» {
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
}

-- Use upstream mathlib pinned to the Lean toolchain version for portability
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

@[default_target]
lean_lib «MathEye»

lean_lib «Services»
