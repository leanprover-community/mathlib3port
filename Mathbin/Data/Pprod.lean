
/-!
# Extra facts about `pprod`
-/


variable{α : Sort _}{β : Sort _}

namespace PProd

@[simp]
theorem mk.eta {p : PProd α β} : PProd.mk p.1 p.2 = p :=
  PProd.casesOn p fun a b => rfl

@[simp]
theorem forall {p : PProd α β → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]
theorem exists {p : PProd α β → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

theorem forall' {p : α → β → Prop} : (∀ (x : PProd α β), p x.1 x.2) ↔ ∀ a b, p a b :=
  PProd.forall

theorem exists' {p : α → β → Prop} : (∃ x : PProd α β, p x.1 x.2) ↔ ∃ a b, p a b :=
  PProd.exists

end PProd

