/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Mario Carneiro

! This file was ported from Lean 3 source module computability.reduce
! leanprover-community/mathlib commit bd15ff41b70f5e2cc210f26f25a8d5c53b20d3de
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Computability.Halting

/-!
# Strong reducibility and degrees.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notations

This file uses the local notation `⊕'` for `sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/


universe u v w

open Function

#print ManyOneReducible /-
/--
`p` is many-one reducible to `q` if there is a computable function translating questions about `p`
to questions about `q`.
-/
def ManyOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ ∀ a, p a ↔ q (f a)
#align many_one_reducible ManyOneReducible
-/

-- mathport name: «expr ≤₀ »
infixl:1000 " ≤₀ " => ManyOneReducible

/- warning: many_one_reducible.mk -> ManyOneReducible.mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {f : α -> β} (q : β -> Prop), (Computable.{u1, u2} α β _inst_1 _inst_2 f) -> (ManyOneReducible.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => q (f a)) q)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {f : α -> β} (q : β -> Prop), (Computable.{u2, u1} α β _inst_1 _inst_2 f) -> (ManyOneReducible.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => q (f a)) q)
Case conversion may be inaccurate. Consider using '#align many_one_reducible.mk ManyOneReducible.mkₓ'. -/
theorem ManyOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) : (fun a => q (f a)) ≤₀ q :=
  ⟨f, h, fun a => Iff.rfl⟩
#align many_one_reducible.mk ManyOneReducible.mk

#print manyOneReducible_refl /-
@[refl]
theorem manyOneReducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₀ p :=
  ⟨id, Computable.id, by simp⟩
#align many_one_reducible_refl manyOneReducible_refl
-/

/- warning: many_one_reducible.trans -> ManyOneReducible.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneReducible.{u1, u2} α β _inst_1 _inst_2 p q) -> (ManyOneReducible.{u2, u3} β γ _inst_2 _inst_3 q r) -> (ManyOneReducible.{u1, u3} α γ _inst_1 _inst_3 p r)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneReducible.{u3, u2} α β _inst_1 _inst_2 p q) -> (ManyOneReducible.{u2, u1} β γ _inst_2 _inst_3 q r) -> (ManyOneReducible.{u3, u1} α γ _inst_1 _inst_3 p r)
Case conversion may be inaccurate. Consider using '#align many_one_reducible.trans ManyOneReducible.transₓ'. -/
@[trans]
theorem ManyOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ q → q ≤₀ r → p ≤₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, fun a => ⟨fun h => by rwa [← h₂, ← h₁], fun h => by rwa [h₁, h₂]⟩⟩
#align many_one_reducible.trans ManyOneReducible.trans

#print reflexive_manyOneReducible /-
theorem reflexive_manyOneReducible {α} [Primcodable α] : Reflexive (@ManyOneReducible α α _ _) :=
  manyOneReducible_refl
#align reflexive_many_one_reducible reflexive_manyOneReducible
-/

#print transitive_manyOneReducible /-
theorem transitive_manyOneReducible {α} [Primcodable α] : Transitive (@ManyOneReducible α α _ _) :=
  fun p q r => ManyOneReducible.trans
#align transitive_many_one_reducible transitive_manyOneReducible
-/

#print OneOneReducible /-
/--
`p` is one-one reducible to `q` if there is an injective computable function translating questions
about `p` to questions about `q`.
-/
def OneOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ Injective f ∧ ∀ a, p a ↔ q (f a)
#align one_one_reducible OneOneReducible
-/

-- mathport name: «expr ≤₁ »
infixl:1000 " ≤₁ " => OneOneReducible

/- warning: one_one_reducible.mk -> OneOneReducible.mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {f : α -> β} (q : β -> Prop), (Computable.{u1, u2} α β _inst_1 _inst_2 f) -> (Function.Injective.{succ u1, succ u2} α β f) -> (OneOneReducible.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => q (f a)) q)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {f : α -> β} (q : β -> Prop), (Computable.{u2, u1} α β _inst_1 _inst_2 f) -> (Function.Injective.{succ u2, succ u1} α β f) -> (OneOneReducible.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => q (f a)) q)
Case conversion may be inaccurate. Consider using '#align one_one_reducible.mk OneOneReducible.mkₓ'. -/
theorem OneOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) (i : Injective f) : (fun a => q (f a)) ≤₁ q :=
  ⟨f, h, i, fun a => Iff.rfl⟩
#align one_one_reducible.mk OneOneReducible.mk

#print oneOneReducible_refl /-
@[refl]
theorem oneOneReducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₁ p :=
  ⟨id, Computable.id, injective_id, by simp⟩
#align one_one_reducible_refl oneOneReducible_refl
-/

/- warning: one_one_reducible.trans -> OneOneReducible.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneReducible.{u1, u2} α β _inst_1 _inst_2 p q) -> (OneOneReducible.{u2, u3} β γ _inst_2 _inst_3 q r) -> (OneOneReducible.{u1, u3} α γ _inst_1 _inst_3 p r)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneReducible.{u3, u2} α β _inst_1 _inst_2 p q) -> (OneOneReducible.{u2, u1} β γ _inst_2 _inst_3 q r) -> (OneOneReducible.{u3, u1} α γ _inst_1 _inst_3 p r)
Case conversion may be inaccurate. Consider using '#align one_one_reducible.trans OneOneReducible.transₓ'. -/
@[trans]
theorem OneOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : p ≤₁ q → q ≤₁ r → p ≤₁ r
  | ⟨f, c₁, i₁, h₁⟩, ⟨g, c₂, i₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, i₂.comp i₁, fun a =>
      ⟨fun h => by rwa [← h₂, ← h₁], fun h => by rwa [h₁, h₂]⟩⟩
#align one_one_reducible.trans OneOneReducible.trans

/- warning: one_one_reducible.to_many_one -> OneOneReducible.to_many_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> Prop} {q : β -> Prop}, (OneOneReducible.{u1, u2} α β _inst_1 _inst_2 p q) -> (ManyOneReducible.{u1, u2} α β _inst_1 _inst_2 p q)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> Prop} {q : β -> Prop}, (OneOneReducible.{u2, u1} α β _inst_1 _inst_2 p q) -> (ManyOneReducible.{u2, u1} α β _inst_1 _inst_2 p q)
Case conversion may be inaccurate. Consider using '#align one_one_reducible.to_many_one OneOneReducible.to_many_oneₓ'. -/
theorem OneOneReducible.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : p ≤₁ q → p ≤₀ q
  | ⟨f, c, i, h⟩ => ⟨f, c, h⟩
#align one_one_reducible.to_many_one OneOneReducible.to_many_one

/- warning: one_one_reducible.of_equiv -> OneOneReducible.of_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {e : Equiv.{succ u1, succ u2} α β} (q : β -> Prop), (Computable.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e)) -> (OneOneReducible.{u1, u2} α β _inst_1 _inst_2 (Function.comp.{succ u1, succ u2, 1} α β Prop q (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e)) q)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {e : Equiv.{succ u2, succ u1} α β} (q : β -> Prop), (Computable.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e)) -> (OneOneReducible.{u2, u1} α β _inst_1 _inst_2 (Function.comp.{succ u2, succ u1, 1} α β Prop q (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e)) q)
Case conversion may be inaccurate. Consider using '#align one_one_reducible.of_equiv OneOneReducible.of_equivₓ'. -/
theorem OneOneReducible.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β → Prop)
    (h : Computable e) : (q ∘ e) ≤₁ q :=
  OneOneReducible.mk _ h e.Injective
#align one_one_reducible.of_equiv OneOneReducible.of_equiv

/- warning: one_one_reducible.of_equiv_symm -> OneOneReducible.of_equiv_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {e : Equiv.{succ u1, succ u2} α β} (q : β -> Prop), (Computable.{u2, u1} β α _inst_2 _inst_1 (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β e))) -> (OneOneReducible.{u2, u1} β α _inst_2 _inst_1 q (Function.comp.{succ u1, succ u2, 1} α β Prop q (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {e : Equiv.{succ u2, succ u1} α β} (q : β -> Prop), (Computable.{u1, u2} β α _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β e))) -> (OneOneReducible.{u1, u2} β α _inst_2 _inst_1 q (Function.comp.{succ u2, succ u1, 1} α β Prop q (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e)))
Case conversion may be inaccurate. Consider using '#align one_one_reducible.of_equiv_symm OneOneReducible.of_equiv_symmₓ'. -/
theorem OneOneReducible.of_equiv_symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
    (q : β → Prop) (h : Computable e.symm) : q ≤₁ (q ∘ e) := by
  convert OneOneReducible.of_equiv _ h <;> funext <;> simp
#align one_one_reducible.of_equiv_symm OneOneReducible.of_equiv_symm

#print reflexive_oneOneReducible /-
theorem reflexive_oneOneReducible {α} [Primcodable α] : Reflexive (@OneOneReducible α α _ _) :=
  oneOneReducible_refl
#align reflexive_one_one_reducible reflexive_oneOneReducible
-/

#print transitive_oneOneReducible /-
theorem transitive_oneOneReducible {α} [Primcodable α] : Transitive (@OneOneReducible α α _ _) :=
  fun p q r => OneOneReducible.trans
#align transitive_one_one_reducible transitive_oneOneReducible
-/

namespace ComputablePred

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Computable

/- warning: computable_pred.computable_of_many_one_reducible -> ComputablePred.computable_of_manyOneReducible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> Prop} {q : β -> Prop}, (ManyOneReducible.{u1, u2} α β _inst_1 _inst_2 p q) -> (ComputablePred.{u2} β _inst_2 q) -> (ComputablePred.{u1} α _inst_1 p)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> Prop} {q : β -> Prop}, (ManyOneReducible.{u2, u1} α β _inst_1 _inst_2 p q) -> (ComputablePred.{u1} β _inst_2 q) -> (ComputablePred.{u2} α _inst_1 p)
Case conversion may be inaccurate. Consider using '#align computable_pred.computable_of_many_one_reducible ComputablePred.computable_of_manyOneReducibleₓ'. -/
theorem computable_of_manyOneReducible {p : α → Prop} {q : β → Prop} (h₁ : p ≤₀ q)
    (h₂ : ComputablePred q) : ComputablePred p :=
  by
  rcases h₁ with ⟨f, c, hf⟩
  rw [show p = fun a => q (f a) from Set.ext hf]
  rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩
  exact ⟨by infer_instance, by simpa using hg.comp c⟩
#align computable_pred.computable_of_many_one_reducible ComputablePred.computable_of_manyOneReducible

/- warning: computable_pred.computable_of_one_one_reducible -> ComputablePred.computable_of_oneOneReducible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> Prop} {q : β -> Prop}, (OneOneReducible.{u1, u2} α β _inst_1 _inst_2 p q) -> (ComputablePred.{u2} β _inst_2 q) -> (ComputablePred.{u1} α _inst_1 p)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> Prop} {q : β -> Prop}, (OneOneReducible.{u2, u1} α β _inst_1 _inst_2 p q) -> (ComputablePred.{u1} β _inst_2 q) -> (ComputablePred.{u2} α _inst_1 p)
Case conversion may be inaccurate. Consider using '#align computable_pred.computable_of_one_one_reducible ComputablePred.computable_of_oneOneReducibleₓ'. -/
theorem computable_of_oneOneReducible {p : α → Prop} {q : β → Prop} (h : p ≤₁ q) :
    ComputablePred q → ComputablePred p :=
  computable_of_manyOneReducible h.to_many_one
#align computable_pred.computable_of_one_one_reducible ComputablePred.computable_of_oneOneReducible

end ComputablePred

#print ManyOneEquiv /-
/-- `p` and `q` are many-one equivalent if each one is many-one reducible to the other. -/
def ManyOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₀ q ∧ q ≤₀ p
#align many_one_equiv ManyOneEquiv
-/

#print OneOneEquiv /-
/-- `p` and `q` are one-one equivalent if each one is one-one reducible to the other. -/
def OneOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₁ q ∧ q ≤₁ p
#align one_one_equiv OneOneEquiv
-/

#print manyOneEquiv_refl /-
@[refl]
theorem manyOneEquiv_refl {α} [Primcodable α] (p : α → Prop) : ManyOneEquiv p p :=
  ⟨manyOneReducible_refl _, manyOneReducible_refl _⟩
#align many_one_equiv_refl manyOneEquiv_refl
-/

/- warning: many_one_equiv.symm -> ManyOneEquiv.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> Prop} {q : β -> Prop}, (ManyOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) -> (ManyOneEquiv.{u2, u1} β α _inst_2 _inst_1 q p)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> Prop} {q : β -> Prop}, (ManyOneEquiv.{u2, u1} α β _inst_1 _inst_2 p q) -> (ManyOneEquiv.{u1, u2} β α _inst_2 _inst_1 q p)
Case conversion may be inaccurate. Consider using '#align many_one_equiv.symm ManyOneEquiv.symmₓ'. -/
@[symm]
theorem ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    ManyOneEquiv p q → ManyOneEquiv q p :=
  And.symm
#align many_one_equiv.symm ManyOneEquiv.symm

/- warning: many_one_equiv.trans -> ManyOneEquiv.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) -> (ManyOneEquiv.{u2, u3} β γ _inst_2 _inst_3 q r) -> (ManyOneEquiv.{u1, u3} α γ _inst_1 _inst_3 p r)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u3, u2} α β _inst_1 _inst_2 p q) -> (ManyOneEquiv.{u2, u1} β γ _inst_2 _inst_3 q r) -> (ManyOneEquiv.{u3, u1} α γ _inst_1 _inst_3 p r)
Case conversion may be inaccurate. Consider using '#align many_one_equiv.trans ManyOneEquiv.transₓ'. -/
@[trans]
theorem ManyOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : ManyOneEquiv p q → ManyOneEquiv q r → ManyOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩
#align many_one_equiv.trans ManyOneEquiv.trans

#print equivalence_of_manyOneEquiv /-
theorem equivalence_of_manyOneEquiv {α} [Primcodable α] : Equivalence (@ManyOneEquiv α α _ _) :=
  ⟨manyOneEquiv_refl, fun x y => ManyOneEquiv.symm, fun x y z => ManyOneEquiv.trans⟩
#align equivalence_of_many_one_equiv equivalence_of_manyOneEquiv
-/

#print oneOneEquiv_refl /-
@[refl]
theorem oneOneEquiv_refl {α} [Primcodable α] (p : α → Prop) : OneOneEquiv p p :=
  ⟨oneOneReducible_refl _, oneOneReducible_refl _⟩
#align one_one_equiv_refl oneOneEquiv_refl
-/

/- warning: one_one_equiv.symm -> OneOneEquiv.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> Prop} {q : β -> Prop}, (OneOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) -> (OneOneEquiv.{u2, u1} β α _inst_2 _inst_1 q p)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> Prop} {q : β -> Prop}, (OneOneEquiv.{u2, u1} α β _inst_1 _inst_2 p q) -> (OneOneEquiv.{u1, u2} β α _inst_2 _inst_1 q p)
Case conversion may be inaccurate. Consider using '#align one_one_equiv.symm OneOneEquiv.symmₓ'. -/
@[symm]
theorem OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    OneOneEquiv p q → OneOneEquiv q p :=
  And.symm
#align one_one_equiv.symm OneOneEquiv.symm

/- warning: one_one_equiv.trans -> OneOneEquiv.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) -> (OneOneEquiv.{u2, u3} β γ _inst_2 _inst_3 q r) -> (OneOneEquiv.{u1, u3} α γ _inst_1 _inst_3 p r)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u3, u2} α β _inst_1 _inst_2 p q) -> (OneOneEquiv.{u2, u1} β γ _inst_2 _inst_3 q r) -> (OneOneEquiv.{u3, u1} α γ _inst_1 _inst_3 p r)
Case conversion may be inaccurate. Consider using '#align one_one_equiv.trans OneOneEquiv.transₓ'. -/
@[trans]
theorem OneOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : OneOneEquiv p q → OneOneEquiv q r → OneOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩
#align one_one_equiv.trans OneOneEquiv.trans

#print equivalence_of_oneOneEquiv /-
theorem equivalence_of_oneOneEquiv {α} [Primcodable α] : Equivalence (@OneOneEquiv α α _ _) :=
  ⟨oneOneEquiv_refl, fun x y => OneOneEquiv.symm, fun x y z => OneOneEquiv.trans⟩
#align equivalence_of_one_one_equiv equivalence_of_oneOneEquiv
-/

/- warning: one_one_equiv.to_many_one -> OneOneEquiv.to_many_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> Prop} {q : β -> Prop}, (OneOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) -> (ManyOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> Prop} {q : β -> Prop}, (OneOneEquiv.{u2, u1} α β _inst_1 _inst_2 p q) -> (ManyOneEquiv.{u2, u1} α β _inst_1 _inst_2 p q)
Case conversion may be inaccurate. Consider using '#align one_one_equiv.to_many_one OneOneEquiv.to_many_oneₓ'. -/
theorem OneOneEquiv.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : OneOneEquiv p q → ManyOneEquiv p q
  | ⟨pq, qp⟩ => ⟨pq.to_many_one, qp.to_many_one⟩
#align one_one_equiv.to_many_one OneOneEquiv.to_many_one

#print Equiv.Computable /-
/-- a computable bijection -/
def Equiv.Computable {α β} [Primcodable α] [Primcodable β] (e : α ≃ β) :=
  Computable e ∧ Computable e.symm
#align equiv.computable Equiv.Computable
-/

/- warning: equiv.computable.symm -> Equiv.Computable.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {e : Equiv.{succ u1, succ u2} α β}, (Equiv.Computable.{u1, u2} α β _inst_1 _inst_2 e) -> (Equiv.Computable.{u2, u1} β α _inst_2 _inst_1 (Equiv.symm.{succ u1, succ u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {e : Equiv.{succ u2, succ u1} α β}, (Equiv.Computable.{u2, u1} α β _inst_1 _inst_2 e) -> (Equiv.Computable.{u1, u2} β α _inst_2 _inst_1 (Equiv.symm.{succ u2, succ u1} α β e))
Case conversion may be inaccurate. Consider using '#align equiv.computable.symm Equiv.Computable.symmₓ'. -/
theorem Equiv.Computable.symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} :
    e.Computable → e.symm.Computable :=
  And.symm
#align equiv.computable.symm Equiv.Computable.symm

/- warning: equiv.computable.trans -> Equiv.Computable.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {e₁ : Equiv.{succ u1, succ u2} α β} {e₂ : Equiv.{succ u2, succ u3} β γ}, (Equiv.Computable.{u1, u2} α β _inst_1 _inst_2 e₁) -> (Equiv.Computable.{u2, u3} β γ _inst_2 _inst_3 e₂) -> (Equiv.Computable.{u1, u3} α γ _inst_1 _inst_3 (Equiv.trans.{succ u1, succ u2, succ u3} α β γ e₁ e₂))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {e₁ : Equiv.{succ u3, succ u2} α β} {e₂ : Equiv.{succ u2, succ u1} β γ}, (Equiv.Computable.{u3, u2} α β _inst_1 _inst_2 e₁) -> (Equiv.Computable.{u2, u1} β γ _inst_2 _inst_3 e₂) -> (Equiv.Computable.{u3, u1} α γ _inst_1 _inst_3 (Equiv.trans.{succ u3, succ u2, succ u1} α β γ e₁ e₂))
Case conversion may be inaccurate. Consider using '#align equiv.computable.trans Equiv.Computable.transₓ'. -/
theorem Equiv.Computable.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β}
    {e₂ : β ≃ γ} : e₁.Computable → e₂.Computable → (e₁.trans e₂).Computable
  | ⟨l₁, r₁⟩, ⟨l₂, r₂⟩ => ⟨l₂.comp l₁, r₁.comp r₂⟩
#align equiv.computable.trans Equiv.Computable.trans

#print Computable.eqv /-
theorem Computable.eqv (α) [Denumerable α] : (Denumerable.eqv α).Computable :=
  ⟨Computable.encode, Computable.ofNat _⟩
#align computable.eqv Computable.eqv
-/

/- warning: computable.equiv₂ -> Computable.equiv₂ is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Denumerable.{u1} α] [_inst_2 : Denumerable.{u2} β], Equiv.Computable.{u1, u2} α β (Primcodable.ofDenumerable.{u1} α _inst_1) (Primcodable.ofDenumerable.{u2} β _inst_2) (Denumerable.equiv₂.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [_inst_1 : Denumerable.{u2} α] [_inst_2 : Denumerable.{u1} β], Equiv.Computable.{u2, u1} α β (Primcodable.ofDenumerable.{u2} α _inst_1) (Primcodable.ofDenumerable.{u1} β _inst_2) (Denumerable.equiv₂.{u2, u1} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align computable.equiv₂ Computable.equiv₂ₓ'. -/
theorem Computable.equiv₂ (α β) [Denumerable α] [Denumerable β] :
    (Denumerable.equiv₂ α β).Computable :=
  (Computable.eqv _).trans (Computable.eqv _).symm
#align computable.equiv₂ Computable.equiv₂

/- warning: one_one_equiv.of_equiv -> OneOneEquiv.of_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {e : Equiv.{succ u1, succ u2} α β}, (Equiv.Computable.{u1, u2} α β _inst_1 _inst_2 e) -> (forall {p : β -> Prop}, OneOneEquiv.{u1, u2} α β _inst_1 _inst_2 (Function.comp.{succ u1, succ u2, 1} α β Prop p (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e)) p)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {e : Equiv.{succ u2, succ u1} α β}, (Equiv.Computable.{u2, u1} α β _inst_1 _inst_2 e) -> (forall {p : β -> Prop}, OneOneEquiv.{u2, u1} α β _inst_1 _inst_2 (Function.comp.{succ u2, succ u1, 1} α β Prop p (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e)) p)
Case conversion may be inaccurate. Consider using '#align one_one_equiv.of_equiv OneOneEquiv.of_equivₓ'. -/
theorem OneOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : OneOneEquiv (p ∘ e) p :=
  ⟨OneOneReducible.of_equiv _ h.1, OneOneReducible.of_equiv_symm _ h.2⟩
#align one_one_equiv.of_equiv OneOneEquiv.of_equiv

/- warning: many_one_equiv.of_equiv -> ManyOneEquiv.of_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {e : Equiv.{succ u1, succ u2} α β}, (Equiv.Computable.{u1, u2} α β _inst_1 _inst_2 e) -> (forall {p : β -> Prop}, ManyOneEquiv.{u1, u2} α β _inst_1 _inst_2 (Function.comp.{succ u1, succ u2, 1} α β Prop p (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e)) p)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {e : Equiv.{succ u2, succ u1} α β}, (Equiv.Computable.{u2, u1} α β _inst_1 _inst_2 e) -> (forall {p : β -> Prop}, ManyOneEquiv.{u2, u1} α β _inst_1 _inst_2 (Function.comp.{succ u2, succ u1, 1} α β Prop p (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e)) p)
Case conversion may be inaccurate. Consider using '#align many_one_equiv.of_equiv ManyOneEquiv.of_equivₓ'. -/
theorem ManyOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : ManyOneEquiv (p ∘ e) p :=
  (OneOneEquiv.of_equiv h).to_many_one
#align many_one_equiv.of_equiv ManyOneEquiv.of_equiv

/- warning: many_one_equiv.le_congr_left -> ManyOneEquiv.le_congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) -> (Iff (ManyOneReducible.{u1, u3} α γ _inst_1 _inst_3 p r) (ManyOneReducible.{u2, u3} β γ _inst_2 _inst_3 q r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u3, u2} α β _inst_1 _inst_2 p q) -> (Iff (ManyOneReducible.{u3, u1} α γ _inst_1 _inst_3 p r) (ManyOneReducible.{u2, u1} β γ _inst_2 _inst_3 q r))
Case conversion may be inaccurate. Consider using '#align many_one_equiv.le_congr_left ManyOneEquiv.le_congr_leftₓ'. -/
theorem ManyOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) : p ≤₀ r ↔ q ≤₀ r :=
  ⟨h.2.trans, h.1.trans⟩
#align many_one_equiv.le_congr_left ManyOneEquiv.le_congr_left

/- warning: many_one_equiv.le_congr_right -> ManyOneEquiv.le_congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u2, u3} β γ _inst_2 _inst_3 q r) -> (Iff (ManyOneReducible.{u1, u2} α β _inst_1 _inst_2 p q) (ManyOneReducible.{u1, u3} α γ _inst_1 _inst_3 p r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u2, u1} β γ _inst_2 _inst_3 q r) -> (Iff (ManyOneReducible.{u3, u2} α β _inst_1 _inst_2 p q) (ManyOneReducible.{u3, u1} α γ _inst_1 _inst_3 p r))
Case conversion may be inaccurate. Consider using '#align many_one_equiv.le_congr_right ManyOneEquiv.le_congr_rightₓ'. -/
theorem ManyOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) : p ≤₀ q ↔ p ≤₀ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
#align many_one_equiv.le_congr_right ManyOneEquiv.le_congr_right

/- warning: one_one_equiv.le_congr_left -> OneOneEquiv.le_congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) -> (Iff (OneOneReducible.{u1, u3} α γ _inst_1 _inst_3 p r) (OneOneReducible.{u2, u3} β γ _inst_2 _inst_3 q r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u3, u2} α β _inst_1 _inst_2 p q) -> (Iff (OneOneReducible.{u3, u1} α γ _inst_1 _inst_3 p r) (OneOneReducible.{u2, u1} β γ _inst_2 _inst_3 q r))
Case conversion may be inaccurate. Consider using '#align one_one_equiv.le_congr_left OneOneEquiv.le_congr_leftₓ'. -/
theorem OneOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) : p ≤₁ r ↔ q ≤₁ r :=
  ⟨h.2.trans, h.1.trans⟩
#align one_one_equiv.le_congr_left OneOneEquiv.le_congr_left

/- warning: one_one_equiv.le_congr_right -> OneOneEquiv.le_congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u2, u3} β γ _inst_2 _inst_3 q r) -> (Iff (OneOneReducible.{u1, u2} α β _inst_1 _inst_2 p q) (OneOneReducible.{u1, u3} α γ _inst_1 _inst_3 p r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u2, u1} β γ _inst_2 _inst_3 q r) -> (Iff (OneOneReducible.{u3, u2} α β _inst_1 _inst_2 p q) (OneOneReducible.{u3, u1} α γ _inst_1 _inst_3 p r))
Case conversion may be inaccurate. Consider using '#align one_one_equiv.le_congr_right OneOneEquiv.le_congr_rightₓ'. -/
theorem OneOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) : p ≤₁ q ↔ p ≤₁ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
#align one_one_equiv.le_congr_right OneOneEquiv.le_congr_right

/- warning: many_one_equiv.congr_left -> ManyOneEquiv.congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) -> (Iff (ManyOneEquiv.{u1, u3} α γ _inst_1 _inst_3 p r) (ManyOneEquiv.{u2, u3} β γ _inst_2 _inst_3 q r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u3, u2} α β _inst_1 _inst_2 p q) -> (Iff (ManyOneEquiv.{u3, u1} α γ _inst_1 _inst_3 p r) (ManyOneEquiv.{u2, u1} β γ _inst_2 _inst_3 q r))
Case conversion may be inaccurate. Consider using '#align many_one_equiv.congr_left ManyOneEquiv.congr_leftₓ'. -/
theorem ManyOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) :
    ManyOneEquiv p r ↔ ManyOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right
#align many_one_equiv.congr_left ManyOneEquiv.congr_left

/- warning: many_one_equiv.congr_right -> ManyOneEquiv.congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u2, u3} β γ _inst_2 _inst_3 q r) -> (Iff (ManyOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) (ManyOneEquiv.{u1, u3} α γ _inst_1 _inst_3 p r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneEquiv.{u2, u1} β γ _inst_2 _inst_3 q r) -> (Iff (ManyOneEquiv.{u3, u2} α β _inst_1 _inst_2 p q) (ManyOneEquiv.{u3, u1} α γ _inst_1 _inst_3 p r))
Case conversion may be inaccurate. Consider using '#align many_one_equiv.congr_right ManyOneEquiv.congr_rightₓ'. -/
theorem ManyOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) :
    ManyOneEquiv p q ↔ ManyOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left
#align many_one_equiv.congr_right ManyOneEquiv.congr_right

/- warning: one_one_equiv.congr_left -> OneOneEquiv.congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) -> (Iff (OneOneEquiv.{u1, u3} α γ _inst_1 _inst_3 p r) (OneOneEquiv.{u2, u3} β γ _inst_2 _inst_3 q r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u3, u2} α β _inst_1 _inst_2 p q) -> (Iff (OneOneEquiv.{u3, u1} α γ _inst_1 _inst_3 p r) (OneOneEquiv.{u2, u1} β γ _inst_2 _inst_3 q r))
Case conversion may be inaccurate. Consider using '#align one_one_equiv.congr_left OneOneEquiv.congr_leftₓ'. -/
theorem OneOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) :
    OneOneEquiv p r ↔ OneOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right
#align one_one_equiv.congr_left OneOneEquiv.congr_left

/- warning: one_one_equiv.congr_right -> OneOneEquiv.congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u2, u3} β γ _inst_2 _inst_3 q r) -> (Iff (OneOneEquiv.{u1, u2} α β _inst_1 _inst_2 p q) (OneOneEquiv.{u1, u3} α γ _inst_1 _inst_3 p r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (OneOneEquiv.{u2, u1} β γ _inst_2 _inst_3 q r) -> (Iff (OneOneEquiv.{u3, u2} α β _inst_1 _inst_2 p q) (OneOneEquiv.{u3, u1} α γ _inst_1 _inst_3 p r))
Case conversion may be inaccurate. Consider using '#align one_one_equiv.congr_right OneOneEquiv.congr_rightₓ'. -/
theorem OneOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) :
    OneOneEquiv p q ↔ OneOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left
#align one_one_equiv.congr_right OneOneEquiv.congr_right

#print Ulower.down_computable /-
@[simp]
theorem Ulower.down_computable {α} [Primcodable α] : (Ulower.equiv α).Computable :=
  ⟨Primrec.ulower_down.to_comp, Primrec.ulower_up.to_comp⟩
#align ulower.down_computable Ulower.down_computable
-/

#print manyOneEquiv_up /-
theorem manyOneEquiv_up {α} [Primcodable α] {p : α → Prop} : ManyOneEquiv (p ∘ Ulower.up) p :=
  ManyOneEquiv.of_equiv Ulower.down_computable.symm
#align many_one_equiv_up manyOneEquiv_up
-/

-- mathport name: «expr ⊕' »
local infixl:1001 " ⊕' " => Sum.elim

open Nat.Primrec

/- warning: one_one_reducible.disjoin_left -> OneOneReducible.disjoin_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> Prop} {q : β -> Prop}, OneOneReducible.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (Primcodable.sum.{u1, u2} α β _inst_1 _inst_2) p (Sum.elim.{u1, u2, 1} α β Prop p q)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> Prop} {q : β -> Prop}, OneOneReducible.{u2, max u1 u2} α (Sum.{u2, u1} α β) _inst_1 (Primcodable.sum.{u2, u1} α β _inst_1 _inst_2) p (Sum.elim.{u2, u1, 1} α β Prop p q)
Case conversion may be inaccurate. Consider using '#align one_one_reducible.disjoin_left OneOneReducible.disjoin_leftₓ'. -/
theorem OneOneReducible.disjoin_left {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : p ≤₁ p ⊕' q :=
  ⟨Sum.inl, Computable.sum_inl, fun x y => Sum.inl.inj_iff.1, fun a => Iff.rfl⟩
#align one_one_reducible.disjoin_left OneOneReducible.disjoin_left

/- warning: one_one_reducible.disjoin_right -> OneOneReducible.disjoin_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> Prop} {q : β -> Prop}, OneOneReducible.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (Primcodable.sum.{u1, u2} α β _inst_1 _inst_2) q (Sum.elim.{u1, u2, 1} α β Prop p q)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> Prop} {q : β -> Prop}, OneOneReducible.{u1, max u1 u2} β (Sum.{u2, u1} α β) _inst_2 (Primcodable.sum.{u2, u1} α β _inst_1 _inst_2) q (Sum.elim.{u2, u1, 1} α β Prop p q)
Case conversion may be inaccurate. Consider using '#align one_one_reducible.disjoin_right OneOneReducible.disjoin_rightₓ'. -/
theorem OneOneReducible.disjoin_right {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : q ≤₁ p ⊕' q :=
  ⟨Sum.inr, Computable.sum_inr, fun x y => Sum.inr.inj_iff.1, fun a => Iff.rfl⟩
#align one_one_reducible.disjoin_right OneOneReducible.disjoin_right

/- warning: disjoin_many_one_reducible -> disjoin_manyOneReducible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneReducible.{u1, u3} α γ _inst_1 _inst_3 p r) -> (ManyOneReducible.{u2, u3} β γ _inst_2 _inst_3 q r) -> (ManyOneReducible.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Primcodable.sum.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u1, u2, 1} α β Prop p q) r)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, (ManyOneReducible.{u3, u1} α γ _inst_1 _inst_3 p r) -> (ManyOneReducible.{u2, u1} β γ _inst_2 _inst_3 q r) -> (ManyOneReducible.{max u2 u3, u1} (Sum.{u3, u2} α β) γ (Primcodable.sum.{u3, u2} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u3, u2, 1} α β Prop p q) r)
Case conversion may be inaccurate. Consider using '#align disjoin_many_one_reducible disjoin_manyOneReducibleₓ'. -/
theorem disjoin_manyOneReducible {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ r → q ≤₀ r → p ⊕' q ≤₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨Sum.elim f g,
      Computable.id.sum_casesOn (c₁.comp Computable.snd).to₂ (c₂.comp Computable.snd).to₂, fun x =>
      by cases x <;> [apply h₁;apply h₂]⟩
#align disjoin_many_one_reducible disjoin_manyOneReducible

/- warning: disjoin_le -> disjoin_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, Iff (ManyOneReducible.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Primcodable.sum.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u1, u2, 1} α β Prop p q) r) (And (ManyOneReducible.{u1, u3} α γ _inst_1 _inst_3 p r) (ManyOneReducible.{u2, u3} β γ _inst_2 _inst_3 q r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop}, Iff (ManyOneReducible.{max u2 u3, u1} (Sum.{u3, u2} α β) γ (Primcodable.sum.{u3, u2} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u3, u2, 1} α β Prop p q) r) (And (ManyOneReducible.{u3, u1} α γ _inst_1 _inst_3 p r) (ManyOneReducible.{u2, u1} β γ _inst_2 _inst_3 q r))
Case conversion may be inaccurate. Consider using '#align disjoin_le disjoin_leₓ'. -/
theorem disjoin_le {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : p ⊕' q ≤₀ r ↔ p ≤₀ r ∧ q ≤₀ r :=
  ⟨fun h =>
    ⟨OneOneReducible.disjoin_left.to_many_one.trans h,
      OneOneReducible.disjoin_right.to_many_one.trans h⟩,
    fun ⟨h₁, h₂⟩ => disjoin_manyOneReducible h₁ h₂⟩
#align disjoin_le disjoin_le

variable {α : Type u} [Primcodable α] [Inhabited α]

variable {β : Type v} [Primcodable β] [Inhabited β]

variable {γ : Type w} [Primcodable γ] [Inhabited γ]

#print toNat /-
/-- Computable and injective mapping of predicates to sets of natural numbers.
-/
def toNat (p : Set α) : Set ℕ :=
  { n | p ((Encodable.decode α n).getD default) }
#align to_nat toNat
-/

#print toNat_manyOneReducible /-
@[simp]
theorem toNat_manyOneReducible {p : Set α} : toNat p ≤₀ p :=
  ⟨fun n => (Encodable.decode α n).getD default,
    Computable.option_getD Computable.decode (Computable.const _), fun _ => Iff.rfl⟩
#align to_nat_many_one_reducible toNat_manyOneReducible
-/

#print manyOneReducible_toNat /-
@[simp]
theorem manyOneReducible_toNat {p : Set α} : p ≤₀ toNat p :=
  ⟨Encodable.encode, Computable.encode, by simp [toNat, setOf]⟩
#align many_one_reducible_to_nat manyOneReducible_toNat
-/

#print manyOneReducible_toNat_toNat /-
@[simp]
theorem manyOneReducible_toNat_toNat {p : Set α} {q : Set β} : toNat p ≤₀ toNat q ↔ p ≤₀ q :=
  ⟨fun h => manyOneReducible_toNat.trans (h.trans toNat_manyOneReducible), fun h =>
    toNat_manyOneReducible.trans (h.trans manyOneReducible_toNat)⟩
#align many_one_reducible_to_nat_to_nat manyOneReducible_toNat_toNat
-/

#print toNat_manyOneEquiv /-
@[simp]
theorem toNat_manyOneEquiv {p : Set α} : ManyOneEquiv (toNat p) p := by simp [ManyOneEquiv]
#align to_nat_many_one_equiv toNat_manyOneEquiv
-/

#print manyOneEquiv_toNat /-
@[simp]
theorem manyOneEquiv_toNat (p : Set α) (q : Set β) :
    ManyOneEquiv (toNat p) (toNat q) ↔ ManyOneEquiv p q := by simp [ManyOneEquiv]
#align many_one_equiv_to_nat manyOneEquiv_toNat
-/

#print ManyOneDegree /-
/-- A many-one degree is an equivalence class of sets up to many-one equivalence. -/
def ManyOneDegree : Type :=
  Quotient (⟨ManyOneEquiv, equivalence_of_manyOneEquiv⟩ : Setoid (Set ℕ))
#align many_one_degree ManyOneDegree
-/

namespace ManyOneDegree

#print ManyOneDegree.of /-
/-- The many-one degree of a set on a primcodable type. -/
def of (p : α → Prop) : ManyOneDegree :=
  Quotient.mk'' (toNat p)
#align many_one_degree.of ManyOneDegree.of
-/

#print ManyOneDegree.ind_on /-
@[elab_as_elim]
protected theorem ind_on {C : ManyOneDegree → Prop} (d : ManyOneDegree)
    (h : ∀ p : Set ℕ, C (of p)) : C d :=
  Quotient.inductionOn' d h
#align many_one_degree.ind_on ManyOneDegree.ind_on
-/

#print ManyOneDegree.liftOn /-
/-- Lifts a function on sets of natural numbers to many-one degrees.
-/
@[elab_as_elim, reducible]
protected def liftOn {φ} (d : ManyOneDegree) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : φ :=
  Quotient.liftOn' d f h
#align many_one_degree.lift_on ManyOneDegree.liftOn
-/

#print ManyOneDegree.liftOn_eq /-
@[simp]
protected theorem liftOn_eq {φ} (p : Set ℕ) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : (of p).liftOn f h = f p :=
  rfl
#align many_one_degree.lift_on_eq ManyOneDegree.liftOn_eq
-/

#print ManyOneDegree.liftOn₂ /-
/-- Lifts a binary function on sets of natural numbers to many-one degrees.
-/
@[elab_as_elim, reducible, simp]
protected def liftOn₂ {φ} (d₁ d₂ : ManyOneDegree) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) : φ :=
  d₁.liftOn (fun p => d₂.liftOn (f p) fun q₁ q₂ hq => h _ _ _ _ (by rfl) hq)
    (by
      intro p₁ p₂ hp
      induction d₂ using ManyOneDegree.ind_on
      apply h
      assumption
      rfl)
#align many_one_degree.lift_on₂ ManyOneDegree.liftOn₂
-/

#print ManyOneDegree.liftOn₂_eq /-
@[simp]
protected theorem liftOn₂_eq {φ} (p q : Set ℕ) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) :
    (of p).liftOn₂ (of q) f h = f p q :=
  rfl
#align many_one_degree.lift_on₂_eq ManyOneDegree.liftOn₂_eq
-/

#print ManyOneDegree.of_eq_of /-
@[simp]
theorem of_eq_of {p : α → Prop} {q : β → Prop} : of p = of q ↔ ManyOneEquiv p q := by
  simp [of, Quotient.eq'']
#align many_one_degree.of_eq_of ManyOneDegree.of_eq_of
-/

instance : Inhabited ManyOneDegree :=
  ⟨of (∅ : Set ℕ)⟩

/-- For many-one degrees `d₁` and `d₂`, `d₁ ≤ d₂` if the sets in `d₁` are many-one reducible to the
sets in `d₂`.
-/
instance : LE ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    ManyOneDegree.liftOn₂ d₁ d₂ (· ≤₀ ·) fun p₁ p₂ q₁ q₂ hp hq =>
      propext (hp.le_congr_left.trans hq.le_congr_right)⟩

#print ManyOneDegree.of_le_of /-
@[simp]
theorem of_le_of {p : α → Prop} {q : β → Prop} : of p ≤ of q ↔ p ≤₀ q :=
  manyOneReducible_toNat_toNat
#align many_one_degree.of_le_of ManyOneDegree.of_le_of
-/

private theorem le_refl (d : ManyOneDegree) : d ≤ d := by
  induction d using ManyOneDegree.ind_on <;> simp
#align many_one_degree.le_refl many_one_degree.le_refl

private theorem le_antisymm {d₁ d₂ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ :=
  by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  intro hp hq
  simp_all only [ManyOneEquiv, of_le_of, of_eq_of, true_and_iff]
#align many_one_degree.le_antisymm many_one_degree.le_antisymm

private theorem le_trans {d₁ d₂ d₃ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ :=
  by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  apply ManyOneReducible.trans
#align many_one_degree.le_trans many_one_degree.le_trans

instance : PartialOrder ManyOneDegree where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

/-- The join of two degrees, induced by the disjoint union of two underlying sets. -/
instance : Add ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    d₁.liftOn₂ d₂ (fun a b => of (a ⊕' b))
      (by
        rintro a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩
        rw [of_eq_of]
        exact
          ⟨disjoin_manyOneReducible (hl₁.trans one_one_reducible.disjoin_left.to_many_one)
              (hl₂.trans one_one_reducible.disjoin_right.to_many_one),
            disjoin_manyOneReducible (hr₁.trans one_one_reducible.disjoin_left.to_many_one)
              (hr₂.trans one_one_reducible.disjoin_right.to_many_one)⟩)⟩

#print ManyOneDegree.add_of /-
@[simp]
theorem add_of (p : Set α) (q : Set β) : of (p ⊕' q) = of p + of q :=
  of_eq_of.mpr
    ⟨disjoin_manyOneReducible
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_left.to_many_one)
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_right.to_many_one),
      disjoin_manyOneReducible
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_left.to_many_one)
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_right.to_many_one)⟩
#align many_one_degree.add_of ManyOneDegree.add_of
-/

#print ManyOneDegree.add_le /-
@[simp]
protected theorem add_le {d₁ d₂ d₃ : ManyOneDegree} : d₁ + d₂ ≤ d₃ ↔ d₁ ≤ d₃ ∧ d₂ ≤ d₃ :=
  by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  simpa only [← add_of, of_le_of] using disjoin_le
#align many_one_degree.add_le ManyOneDegree.add_le
-/

#print ManyOneDegree.le_add_left /-
@[simp]
protected theorem le_add_left (d₁ d₂ : ManyOneDegree) : d₁ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (by rfl)).1
#align many_one_degree.le_add_left ManyOneDegree.le_add_left
-/

#print ManyOneDegree.le_add_right /-
@[simp]
protected theorem le_add_right (d₁ d₂ : ManyOneDegree) : d₂ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (by rfl)).2
#align many_one_degree.le_add_right ManyOneDegree.le_add_right
-/

instance : SemilatticeSup ManyOneDegree :=
  { ManyOneDegree.instPartialOrder with
    sup := (· + ·)
    le_sup_left := ManyOneDegree.le_add_left
    le_sup_right := ManyOneDegree.le_add_right
    sup_le := fun a b c h₁ h₂ => ManyOneDegree.add_le.2 ⟨h₁, h₂⟩ }

end ManyOneDegree

