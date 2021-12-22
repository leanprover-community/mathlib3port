import Mathbin.Tactic.PiInstances

/-!
# Bundled types

`bundled c` provides a uniform structure for bundling a type equipped with a type class.

We provide `category` instances for these in `category_theory/unbundled_hom.lean`
(for categories with unbundled homs, e.g. topological spaces)
and in `category_theory/bundled_hom.lean` (for categories with bundled homs, e.g. monoids).
-/


universe u v

namespace CategoryTheory

variable {c d : Type u → Type v} {α : Type u}

/--  `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
@[nolint has_inhabited_instance]
structure bundled (c : Type u → Type v) : Type max (u + 1) v where
  α : Type u
  str : c α := by
    run_tac
      tactic.apply_instance

namespace Bundled

/--  A generic function for lifting a type equipped with an instance to a bundled object. -/
def of {c : Type u → Type v} (α : Type u) [str : c α] : bundled c :=
  ⟨α, str⟩

instance : CoeSort (bundled c) (Type u) :=
  ⟨bundled.α⟩

@[simp]
theorem coe_mk α str : (@bundled.mk c α str : Type u) = α :=
  rfl

/--  Map over the bundled structure -/
@[reducible]
def map (f : ∀ {α}, c α → d α) (b : bundled c) : bundled d :=
  ⟨b, f b.str⟩

end Bundled

end CategoryTheory

