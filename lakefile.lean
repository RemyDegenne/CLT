import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-Dpp.proofs.withType=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

-- These are additional settings which do not affect the lake hash,
-- so they can be enabled in CI and disabled locally or vice versa.
-- Warning: Do not put any options here that actually change the olean files,
-- or inconsistent behavior may result
def weakLeanArgs : Array String :=
  if get_config? CI |>.isSome then
    #["-DwarningAsError=true"]
  else
    #[]

package «clt» where
  moreServerArgs := moreServerArgs
  leanOptions := #[
    ⟨`relaxedAutoImplicit, true⟩, -- prevents typos to be interpreted as new free variables
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩]
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib «Clt» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  -- add any library configuration options here
