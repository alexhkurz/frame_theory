import Lake
open Lake DSL

package «FrameTheory» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib «FrameTheory» where
  -- add any library configuration options here

@[default_target]
target «docs» {
  cmd := "lake exe doc-gen4 FrameTheory"
}
