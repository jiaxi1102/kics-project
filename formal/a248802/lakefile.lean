import Lake
open Lake DSL

package «a248802_counterexample» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

lean_lib A248802Counterexample where
  roots := #[`A248802Counterexample]
