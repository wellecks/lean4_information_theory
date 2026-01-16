import Lake
open Lake DSL

package «information_theory» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

@[default_target]
lean_lib «InformationTheory» {
  -- add library configuration options here
}

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
