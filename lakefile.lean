import Lake
open Lake DSL

package «FourDStickyKakeya» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

require LeanFormalizations from git
  "https://github.com/mysticflounder/lean-formalizations.git" @
  "dd46c17a2a034d7bfa0df02e7f77834d35592864"

lean_lib «Definitions» where
  globs := #[.submodules `Definitions]

@[default_target]
lean_lib «Theorems» where
  globs := #[.submodules `Theorems]

@[default_target]
lean_lib «Solutions» where
  globs := #[.submodules `Solutions]
