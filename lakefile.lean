import Lake
open Lake DSL

package «matheye-proof-builder» {
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
}

require mathlib from "/Users/sjm/miniconda3/lib/python3.13/site-packages/lean_interact/cache/tmp_projects/v4.20.0/da1210be658679d7172bc04a3004ec5d183702c1e1890268233e2755c5247945/.lake/packages/mathlib"

@[default_target]
lean_lib «MathEye»

lean_lib «Services»
