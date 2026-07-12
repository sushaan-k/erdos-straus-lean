import Lake
open Lake DSL

package esc_formalization

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

lean_lib EscLeanChecks

lean_lib EscAnalytic where
  globs := #[Glob.submodules `EscAnalytic]
