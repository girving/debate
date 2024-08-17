import Lake
open Lake DSL

package debate where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.10.0"

@[default_target]
lean_lib Debate

lean_lib Prob

lean_lib Comp

lean_lib Misc
