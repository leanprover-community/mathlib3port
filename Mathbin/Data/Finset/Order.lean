import Mathbin.Data.Finset.Basic

/-!
# Finsets of ordered types
-/


universe u v w

variable{α : Type u}

theorem Directed.finset_le {r : α → α → Prop} [IsTrans α r] {ι} [hι : Nonempty ι] {f : ι → α} (D : Directed r f)
  (s : Finset ι) : ∃ z, ∀ i (_ : i ∈ s), r (f i) (f z) :=
  show ∃ z, ∀ i (_ : i ∈ s.1), r (f i) (f z) from
    Multiset.induction_on s.1
        (let ⟨z⟩ := hι
        ⟨z, fun _ => False.elim⟩)$
      fun i s ⟨j, H⟩ =>
        let ⟨k, h₁, h₂⟩ := D i j
        ⟨k, fun a h => Or.cases_on (Multiset.mem_cons.1 h) (fun h => h.symm ▸ h₁) fun h => trans (H _ h) h₂⟩

theorem Finset.exists_le {α : Type u} [Nonempty α] [DirectedOrder α] (s : Finset α) : ∃ M, ∀ i (_ : i ∈ s), i ≤ M :=
  Directed.finset_le DirectedOrder.directed s

