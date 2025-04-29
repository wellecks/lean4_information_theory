import Lake
open Lake DSL

package «information_theory» where

require llmlean from git
  "https://github.com/cmu-l3/llmlean.git" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.18.0"


@[default_target]
lean_lib «InformationTheory» {
  -- add library configuration options here
}
