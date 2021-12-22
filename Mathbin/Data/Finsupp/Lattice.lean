import Mathbin.Data.Finsupp.Basic

/-!
# Lattice structure on finsupps

This file provides instances of ordered structures on finsupps.

-/


noncomputable section

variable {α : Type _} {β : Type _} [HasZero β] {μ : Type _} [CanonicallyOrderedAddMonoid μ]

variable {γ : Type _} [CanonicallyLinearOrderedAddMonoid γ]

namespace Finsupp

instance [SemilatticeInf β] : SemilatticeInf (α →₀ β) :=
  { Finsupp.partialOrder with inf := zip_with (·⊓·) inf_idem, inf_le_left := fun a b c => inf_le_left,
    inf_le_right := fun a b c => inf_le_right, le_inf := fun a b c h1 h2 s => le_inf (h1 s) (h2 s) }

@[simp]
theorem inf_apply [SemilatticeInf β] {a : α} {f g : α →₀ β} : (f⊓g) a = f a⊓g a :=
  rfl

@[simp]
theorem support_inf [DecidableEq α] {f g : α →₀ γ} : (f⊓g).Support = f.support ∩ g.support := by
  ext
  simp only [inf_apply, mem_support_iff, Ne.def, Finset.mem_union, Finset.mem_filter, Finset.mem_inter]
  simp only [inf_eq_min, ← nonpos_iff_eq_zero, min_le_iff, not_or_distrib]

instance [SemilatticeSup β] : SemilatticeSup (α →₀ β) :=
  { Finsupp.partialOrder with sup := zip_with (·⊔·) sup_idem, le_sup_left := fun a b c => le_sup_left,
    le_sup_right := fun a b c => le_sup_right, sup_le := fun a b c h1 h2 s => sup_le (h1 s) (h2 s) }

@[simp]
theorem sup_apply [SemilatticeSup β] {a : α} {f g : α →₀ β} : (f⊔g) a = f a⊔g a :=
  rfl

@[simp]
theorem support_sup [DecidableEq α] {f g : α →₀ γ} : (f⊔g).Support = f.support ∪ g.support := by
  ext
  simp only [Finset.mem_union, mem_support_iff, sup_apply, Ne.def, ← bot_eq_zero]
  rw [sup_eq_bot_iff]
  tauto

instance Lattice [Lattice β] : Lattice (α →₀ β) :=
  { Finsupp.semilatticeInf, Finsupp.semilatticeSup with }

theorem bot_eq_zero : (⊥ : α →₀ γ) = 0 :=
  rfl

theorem disjoint_iff [DecidableEq α] {x y : α →₀ γ} : Disjoint x y ↔ Disjoint x.support y.support := by
  unfold Disjoint
  repeat'
    rw [le_bot_iff]
  rw [Finsupp.bot_eq_zero, ← Finsupp.support_eq_empty, Finsupp.support_inf]
  rfl

variable [PartialOrderₓ β]

/--  The order on `finsupp`s over a partial order embeds into the order on functions -/
def order_embedding_to_fun : (α →₀ β) ↪o (α → β) :=
  ⟨⟨fun f : α →₀ β a : α => f a, fun f g h =>
      Finsupp.ext fun a => by
        dsimp  at h
        rw [h]⟩,
    fun a b => (@le_def _ _ _ _ a b).symm⟩

@[simp]
theorem order_embedding_to_fun_apply {f : α →₀ β} {a : α} : order_embedding_to_fun f a = f a :=
  rfl

theorem monotone_to_fun : Monotone (Finsupp.toFun : (α →₀ β) → α → β) := fun f g h a => le_def.1 h a

end Finsupp

