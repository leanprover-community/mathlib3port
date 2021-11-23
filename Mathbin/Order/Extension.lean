import Mathbin.Data.Set.Lattice 
import Mathbin.Order.Zorn

/-!
# Extend a partial order to a linear order

This file constructs a linear order which is an extension of the given partial order, using Zorn's
lemma.
-/


universe u

open Set Classical

open_locale Classical

-- error in Order.Extension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Any partial order can be extended to a linear order.
-/
theorem extend_partial_order
{α : Type u}
(r : α → α → exprProp())
[is_partial_order α r] : «expr∃ , »((s : α → α → exprProp()) (_ : is_linear_order α s), «expr ≤ »(r, s)) :=
begin
  let [ident S] [] [":=", expr {s | is_partial_order α s}],
  have [ident hS] [":", expr ∀
   c, «expr ⊆ »(c, S) → zorn.chain ((«expr ≤ »)) c → ∀
   y «expr ∈ » c, «expr∃ , »((ub «expr ∈ » S), ∀ z «expr ∈ » c, «expr ≤ »(z, ub))] [],
  { rintro [ident c, ident hc₁, ident hc₂, ident s, ident hs],
    haveI [] [] [":=", expr (hc₁ hs).1],
    refine [expr ⟨Sup c, _, λ z hz, le_Sup hz⟩],
    refine [expr { refl := _, trans := _, antisymm := _ }]; simp_rw [expr binary_relation_Sup_iff] [],
    { intro [ident x],
      exact [expr ⟨s, hs, refl x⟩] },
    { rintro [ident x, ident y, ident z, "⟨", ident s₁, ",", ident h₁s₁, ",", ident h₂s₁, "⟩", "⟨", ident s₂, ",", ident h₁s₂, ",", ident h₂s₂, "⟩"],
      haveI [] [":", expr is_partial_order _ _] [":=", expr hc₁ h₁s₁],
      haveI [] [":", expr is_partial_order _ _] [":=", expr hc₁ h₁s₂],
      cases [expr hc₂.total_of_refl h₁s₁ h₁s₂] [],
      { exact [expr ⟨s₂, h₁s₂, trans (h _ _ h₂s₁) h₂s₂⟩] },
      { exact [expr ⟨s₁, h₁s₁, trans h₂s₁ (h _ _ h₂s₂)⟩] } },
    { rintro [ident x, ident y, "⟨", ident s₁, ",", ident h₁s₁, ",", ident h₂s₁, "⟩", "⟨", ident s₂, ",", ident h₁s₂, ",", ident h₂s₂, "⟩"],
      haveI [] [":", expr is_partial_order _ _] [":=", expr hc₁ h₁s₁],
      haveI [] [":", expr is_partial_order _ _] [":=", expr hc₁ h₁s₂],
      cases [expr hc₂.total_of_refl h₁s₁ h₁s₂] [],
      { exact [expr antisymm (h _ _ h₂s₁) h₂s₂] },
      { apply [expr antisymm h₂s₁ (h _ _ h₂s₂)] } } },
  obtain ["⟨", ident s, ",", ident hs₁, ":", expr is_partial_order _ _, ",", ident rs, ",", ident hs₂, "⟩", ":=", expr zorn.zorn_nonempty_partial_order₀ S hS r «expr‹ ›»(_)],
  resetI,
  refine [expr ⟨s, { total := _ }, rs⟩],
  intros [ident x, ident y],
  by_contra [ident h],
  push_neg ["at", ident h],
  let [ident s'] [] [":=", expr λ x' y', «expr ∨ »(s x' y', «expr ∧ »(s x' x, s y y'))],
  rw ["<-", expr hs₂ s' _ (λ _ _, or.inl)] ["at", ident h],
  { apply [expr h.1 (or.inr ⟨refl _, refl _⟩)] },
  { refine [expr { refl := λ x, or.inl (refl _), trans := _, antisymm := _ }],
    { rintro [ident a, ident b, ident c, "(", ident ab, "|", "⟨", ident ax, ":", expr s a x, ",", ident yb, ":", expr s y b, "⟩", ")", "(", ident bc, "|", "⟨", ident bx, ":", expr s b x, ",", ident yc, ":", expr s y c, "⟩", ")"],
      { exact [expr or.inl (trans ab bc)] },
      { exact [expr or.inr ⟨trans ab bx, yc⟩] },
      { exact [expr or.inr ⟨ax, trans yb bc⟩] },
      { exact [expr or.inr ⟨ax, yc⟩] } },
    { rintro [ident a, ident b, "(", ident ab, "|", "⟨", ident ax, ":", expr s a x, ",", ident yb, ":", expr s y b, "⟩", ")", "(", ident ba, "|", "⟨", ident bx, ":", expr s b x, ",", ident ya, ":", expr s y a, "⟩", ")"],
      { exact [expr antisymm ab ba] },
      { exact [expr (h.2 (trans ya (trans ab bx))).elim] },
      { exact [expr (h.2 (trans yb (trans ba ax))).elim] },
      { exact [expr (h.2 (trans yb bx)).elim] } } }
end

/-- A type alias for `α`, intended to extend a partial order on `α` to a linear order. -/
def LinearExtension (α : Type u) : Type u :=
  α

noncomputable instance  {α : Type u} [PartialOrderₓ α] : LinearOrderₓ (LinearExtension α) :=
  { le := (extend_partial_order (· ≤ · : α → α → Prop)).some,
    le_refl := (extend_partial_order (· ≤ · : α → α → Prop)).some_spec.some.1.1.1.1,
    le_trans := (extend_partial_order (· ≤ · : α → α → Prop)).some_spec.some.1.1.2.1,
    le_antisymm := (extend_partial_order (· ≤ · : α → α → Prop)).some_spec.some.1.2.1,
    le_total := (extend_partial_order (· ≤ · : α → α → Prop)).some_spec.some.2.1, decidableLe := Classical.decRel _ }

/-- The embedding of `α` into `linear_extension α` as a relation homomorphism. -/
def toLinearExtension {α : Type u} [PartialOrderₓ α] :
  (· ≤ · : α → α → Prop) →r (· ≤ · : LinearExtension α → LinearExtension α → Prop) :=
  { toFun := fun x => x, map_rel' := fun a b => (extend_partial_order (· ≤ · : α → α → Prop)).some_spec.some_spec _ _ }

instance  {α : Type u} [Inhabited α] : Inhabited (LinearExtension α) :=
  ⟨(default _ : α)⟩

