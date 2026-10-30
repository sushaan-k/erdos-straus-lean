import Lake
open Lake DSL

package erdos_straus

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"

@[default_target]
lean_lib ErdosStraus where
  globs := #[Glob.submodules `ErdosStraus]
