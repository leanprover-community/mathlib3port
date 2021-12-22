import Mathbin.Order.Lattice
import Mathbin.Data.Set.Basic

/-!
# Directed indexed families and sets

This file defines directed indexed families and directed sets. An indexed family/set is
directed iff each pair of elements has a shared upper bound.

## Main declarations

* `directed r f`: Predicate stating that the indexed family `f` is `r`-directed.
* `directed_on r s`: Predicate stating that the set `s` is `r`-directed.
* `directed_order α`: Typeclass extending `preorder` for stating that `α` is `≤`-directed.
-/


universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w} (r : α → α → Prop)

local infixl:50 " ≼ " => r

/--  A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def Directed (f : ι → α) :=
  ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z

/--  A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def DirectedOn (s : Set α) :=
  ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, ∃ z ∈ s, x ≼ z ∧ y ≼ z

variable {r}

theorem directed_on_iff_directed {s} : @DirectedOn α r s ↔ Directed r (coeₓ : s → α) := by
  simp [Directed, DirectedOn] <;>
    refine'
      ball_congr fun x hx => by
        simp <;> rfl

alias directed_on_iff_directed ↔ DirectedOn.directed_coe _

theorem directed_on_image {s} {f : β → α} : DirectedOn r (f '' s) ↔ DirectedOn (f ⁻¹'o r) s := by
  simp only [DirectedOn, Set.ball_image_iff, Set.bex_image_iff, Order.Preimage]

theorem DirectedOn.mono {s : Set α} (h : DirectedOn r s) {r' : α → α → Prop} (H : ∀ {a b}, r a b → r' a b) :
    DirectedOn r' s := fun x hx y hy =>
  let ⟨z, zs, xz, yz⟩ := h x hx y hy
  ⟨z, zs, H xz, H yz⟩

theorem directed_comp {ι} {f : ι → β} {g : β → α} : Directed r (g ∘ f) ↔ Directed (g ⁻¹'o r) f :=
  Iff.rfl

theorem Directed.mono {s : α → α → Prop} {ι} {f : ι → α} (H : ∀ a b, r a b → s a b) (h : Directed r f) : Directed s f :=
  fun a b =>
  let ⟨c, h₁, h₂⟩ := h a b
  ⟨c, H _ _ h₁, H _ _ h₂⟩

theorem Directed.mono_comp {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α} (hg : ∀ ⦃x y⦄, x ≼ y → rb (g x) (g y))
    (hf : Directed r f) : Directed rb (g ∘ f) :=
  directed_comp.2 $ hf.mono hg

/--  A monotone function on a sup-semilattice is directed. -/
theorem directed_of_sup [SemilatticeSup α] {f : α → β} {r : β → β → Prop} (H : ∀ ⦃i j⦄, i ≤ j → r (f i) (f j)) :
    Directed r f := fun a b => ⟨a⊔b, H le_sup_left, H le_sup_right⟩

theorem Monotone.directed_le [SemilatticeSup α] [Preorderₓ β] {f : α → β} : Monotone f → Directed (· ≤ ·) f :=
  directed_of_sup

/--  An antitone function on an inf-semilattice is directed. -/
theorem directed_of_inf [SemilatticeInf α] {r : β → β → Prop} {f : α → β} (hf : ∀ a₁ a₂, a₁ ≤ a₂ → r (f a₂) (f a₁)) :
    Directed r f := fun x y => ⟨x⊓y, hf _ _ inf_le_left, hf _ _ inf_le_right⟩

/--  A `preorder` is a `directed_order` if for any two elements `i`, `j`
there is an element `k` such that `i ≤ k` and `j ≤ k`. -/
class DirectedOrder (α : Type u) extends Preorderₓ α where
  Directed : ∀ i j : α, ∃ k, i ≤ k ∧ j ≤ k

instance (priority := 100) LinearOrderₓ.toDirectedOrder α [LinearOrderₓ α] : DirectedOrder α :=
  ⟨fun i j => Or.cases_on (le_totalₓ i j) (fun hij => ⟨j, hij, le_reflₓ j⟩) fun hji => ⟨i, le_reflₓ i, hji⟩⟩

