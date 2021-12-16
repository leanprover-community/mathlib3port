import Mathbin.Data.Equiv.Basic

/-!
# Extra lemmas about `ulift` and `plift`

In this file we provide `subsingleton`, `unique`, `decidable_eq`, and `is_empty` instances for
`ulift α` and `plift α`. We also prove `ulift.forall`, `ulift.exists`, `plift.forall`, and
`plift.exists`.
-/


universe u v

namespace Plift

variable {α : Sort u} {β : Sort v}

instance [Subsingleton α] : Subsingleton (Plift α) :=
  Equivₓ.plift.Subsingleton

instance [Unique α] : Unique (Plift α) :=
  Equivₓ.plift.unique

instance [DecidableEq α] : DecidableEq (Plift α) :=
  Equivₓ.plift.DecidableEq

instance [IsEmpty α] : IsEmpty (Plift α) :=
  Equivₓ.plift.isEmpty

@[simp]
theorem forall {p : Plift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (Plift.up x) :=
  Equivₓ.plift.forall_congr_left'

@[simp]
theorem exists {p : Plift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (Plift.up x) :=
  Equivₓ.plift.exists_congr_left

end Plift

namespace Ulift

variable {α : Type u} {β : Type v}

instance [Subsingleton α] : Subsingleton (Ulift α) :=
  Equivₓ.ulift.Subsingleton

instance [Unique α] : Unique (Ulift α) :=
  Equivₓ.ulift.unique

instance [DecidableEq α] : DecidableEq (Ulift α) :=
  Equivₓ.ulift.DecidableEq

instance [IsEmpty α] : IsEmpty (Ulift α) :=
  Equivₓ.ulift.isEmpty

@[simp]
theorem forall {p : Ulift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (Ulift.up x) :=
  Equivₓ.ulift.forall_congr_left'

@[simp]
theorem exists {p : Ulift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (Ulift.up x) :=
  Equivₓ.ulift.exists_congr_left

end Ulift

