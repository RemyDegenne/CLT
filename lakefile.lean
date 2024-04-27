import Lake
open Lake DSL

package «clt»

lean_lib «CLT»
lean_lib «MathlibExt»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
