import Mathbin.Tactic.Abel

namespace Tactic

namespace Interactive

-- ././Mathport/Syntax/Translate/Basic.lean:686:4: warning: unsupported (TODO): `[tacs]
/-- A tactic for simplifying identities in not-necessarily-commutative rings.

An example:
```lean
example {R : Type*} [ring R] (a b c : R) : a * (b + c + c - b) = 2*a*c :=
by noncomm_ring
```
-/
unsafe def noncomm_ring :=
  sorry

add_tactic_doc
  { Name := "noncomm_ring", category := DocCategory.tactic, declNames := [`tactic.interactive.noncomm_ring],
    tags := ["arithmetic", "simplification", "decision procedure"] }

end Interactive

end Tactic

