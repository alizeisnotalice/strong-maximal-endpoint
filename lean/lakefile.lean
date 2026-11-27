import Lake
open Lake DSL

/-- Formalisation of the endpoint-constant bounds of the v1 manuscript.

`mathlib` is pinned to the same revision used by the sibling archived project. -/
package «strong-maximal-endpoint»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

@[default_target]
lean_lib StrongMaximal
