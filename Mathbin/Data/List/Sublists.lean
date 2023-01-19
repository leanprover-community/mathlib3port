/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.sublists
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Choose.Basic
import Mathbin.Data.List.Perm

/-! # sublists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`list.sublists` gives a list of all (not necessarily contiguous) sublists of a list.

This file contains basic results on this function.
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Nat

namespace List

/-! ### sublists -/


#print List.sublists'_nil /-
@[simp]
theorem sublists'_nil : sublists' (@nil α) = [[]] :=
  rfl
#align list.sublists'_nil List.sublists'_nil
-/

#print List.sublists'_singleton /-
@[simp]
theorem sublists'_singleton (a : α) : sublists' [a] = [[], [a]] :=
  rfl
#align list.sublists'_singleton List.sublists'_singleton
-/

/- warning: list.map_sublists'_aux clashes with [anonymous] -> [anonymous]
warning: list.map_sublists'_aux -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} (g : (List.{v} β) -> (List.{w} γ)) (l : List.{u} α) (f : (List.{u} α) -> (List.{v} β)) (r : List.{v} (List.{v} β)), Eq.{succ w} (List.{w} (List.{w} γ)) (List.map.{v, w} (List.{v} β) (List.{w} γ) g (List.sublists'Aux.{u, v} α β l f r)) (List.sublists'Aux.{u, w} α γ l (Function.comp.{succ u, succ v, succ w} (List.{u} α) (List.{v} β) (List.{w} γ) g f) (List.map.{v, w} (List.{v} β) (List.{w} γ) g r))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}}, (Nat -> α -> β) -> Nat -> (List.{u} α) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align list.map_sublists'_aux [anonymous]ₓ'. -/
theorem [anonymous] (g : List β → List γ) (l : List α) (f r) :
    map g (sublists'Aux l f r) = sublists'Aux l (g ∘ f) (map g r) := by
  induction l generalizing f r <;> [rfl, simp only [*, sublists'_aux]]
#align list.map_sublists'_aux[anonymous]

/- warning: list.sublists'_aux_append clashes with [anonymous] -> [anonymous]
warning: list.sublists'_aux_append -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r' : List.{u2} (List.{u2} β)) (l : List.{u1} α) (f : (List.{u1} α) -> (List.{u2} β)) (r : List.{u2} (List.{u2} β)), Eq.{succ u2} (List.{u2} (List.{u2} β)) (List.sublists'Aux.{u1, u2} α β l f (Append.append.{u2} (List.{u2} (List.{u2} β)) (List.hasAppend.{u2} (List.{u2} β)) r r')) (Append.append.{u2} (List.{u2} (List.{u2} β)) (List.hasAppend.{u2} (List.{u2} β)) (List.sublists'Aux.{u1, u2} α β l f r) r')
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.sublists'_aux_append [anonymous]ₓ'. -/
theorem [anonymous] (r' : List (List β)) (l : List α) (f r) :
    sublists'Aux l f (r ++ r') = sublists'Aux l f r ++ r' := by
  induction l generalizing f r <;> [rfl, simp only [*, sublists'_aux]]
#align list.sublists'_aux_append[anonymous]

/- warning: list.sublists'_aux_eq_sublists' clashes with [anonymous] -> [anonymous]
warning: list.sublists'_aux_eq_sublists' -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : (List.{u1} α) -> (List.{u2} β)) (r : List.{u2} (List.{u2} β)), Eq.{succ u2} (List.{u2} (List.{u2} β)) (List.sublists'Aux.{u1, u2} α β l f r) (Append.append.{u2} (List.{u2} (List.{u2} β)) (List.hasAppend.{u2} (List.{u2} β)) (List.map.{u1, u2} (List.{u1} α) (List.{u2} β) f (List.sublists'.{u1} α l)) r)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.sublists'_aux_eq_sublists' [anonymous]ₓ'. -/
theorem [anonymous] (l f r) : @sublists'Aux α β l f r = map f (sublists' l) ++ r := by
  rw [sublists', map_sublists'_aux, ← sublists'_aux_append] <;> rfl
#align list.sublists'_aux_eq_sublists'[anonymous]

#print List.sublists'_cons /-
@[simp]
theorem sublists'_cons (a : α) (l : List α) :
    sublists' (a :: l) = sublists' l ++ map (cons a) (sublists' l) := by
  rw [sublists', sublists'_aux] <;> simp only [sublists'_aux_eq_sublists', map_id, append_nil] <;>
    rfl
#align list.sublists'_cons List.sublists'_cons
-/

#print List.mem_sublists' /-
@[simp]
theorem mem_sublists' {s t : List α} : s ∈ sublists' t ↔ s <+ t :=
  by
  induction' t with a t IH generalizing s
  · simp only [sublists'_nil, mem_singleton]
    exact ⟨fun h => by rw [h], eq_nil_of_sublist_nil⟩
  simp only [sublists'_cons, mem_append, IH, mem_map]
  constructor <;> intro h; rcases h with (h | ⟨s, h, rfl⟩)
  · exact sublist_cons_of_sublist _ h
  · exact h.cons_cons _
  · cases' h with _ _ _ h s _ _ h
    · exact Or.inl h
    · exact Or.inr ⟨s, h, rfl⟩
#align list.mem_sublists' List.mem_sublists'
-/

#print List.length_sublists' /-
@[simp]
theorem length_sublists' : ∀ l : List α, length (sublists' l) = 2 ^ length l
  | [] => rfl
  | a :: l => by
    simp only [sublists'_cons, length_append, length_sublists' l, length_map, length, pow_succ',
      mul_succ, mul_zero, zero_add]
#align list.length_sublists' List.length_sublists'
-/

#print List.sublists_nil /-
@[simp]
theorem sublists_nil : sublists (@nil α) = [[]] :=
  rfl
#align list.sublists_nil List.sublists_nil
-/

#print List.sublists_singleton /-
@[simp]
theorem sublists_singleton (a : α) : sublists [a] = [[], [a]] :=
  rfl
#align list.sublists_singleton List.sublists_singleton
-/

/- warning: list.sublists_aux₁_eq_sublists_aux clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux₁_eq_sublists_aux -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : (List.{u1} α) -> (List.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.sublistsAux₁.{u1, u2} α β l f) (List.sublistsAux.{u1, u2} α β l (fun (ys : List.{u1} α) (r : List.{u2} β) => Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (f ys) r))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux₁_eq_sublists_aux [anonymous]ₓ'. -/
theorem [anonymous] :
    ∀ (l) (f : List α → List β), sublistsAux₁ l f = sublistsAux l fun ys r => f ys ++ r
  | [], f => rfl
  | a :: l, f => by rw [sublists_aux₁, sublists_aux] <;> simp only [*, append_assoc]
#align list.sublists_aux₁_eq_sublists_aux[anonymous]

/- warning: list.sublists_aux_cons_eq_sublists_aux₁ clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux_cons_eq_sublists_aux₁ -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (l : List.{u} α), Eq.{succ u} (List.{u} (List.{u} α)) (List.sublistsAux.{u, u} α (List.{u} α) l (List.cons.{u} (List.{u} α))) (List.sublistsAux₁.{u, u} α (List.{u} α) l (fun (x : List.{u} α) => List.cons.{u} (List.{u} α) x (List.nil.{u} (List.{u} α))))
but is expected to have type
  forall {α : Type.{u}} {l : Type.{v}}, (Nat -> α -> l) -> Nat -> (List.{u} α) -> (List.{v} l)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux_cons_eq_sublists_aux₁ [anonymous]ₓ'. -/
theorem [anonymous] (l : List α) : sublistsAux l cons = sublistsAux₁ l fun x => [x] := by
  rw [sublists_aux₁_eq_sublists_aux] <;> rfl
#align list.sublists_aux_cons_eq_sublists_aux₁[anonymous]

/- warning: list.sublists_aux_eq_foldr.aux clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux_eq_foldr.aux -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {a : α} {l : List.{u1} α}, (forall (f : (List.{u1} α) -> (List.{u2} β) -> (List.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.sublistsAux.{u1, u2} α β l f) (List.foldr.{u1, u2} (List.{u1} α) (List.{u2} β) f (List.nil.{u2} β) (List.sublistsAux.{u1, u1} α (List.{u1} α) l (List.cons.{u1} (List.{u1} α))))) -> (forall (f : (List.{u1} α) -> (List.{u1} (List.{u1} α)) -> (List.{u1} (List.{u1} α))), Eq.{succ u1} (List.{u1} (List.{u1} α)) (List.sublistsAux.{u1, u1} α (List.{u1} α) l f) (List.foldr.{u1, u1} (List.{u1} α) (List.{u1} (List.{u1} α)) f (List.nil.{u1} (List.{u1} α)) (List.sublistsAux.{u1, u1} α (List.{u1} α) l (List.cons.{u1} (List.{u1} α))))) -> (forall (f : (List.{u1} α) -> (List.{u2} β) -> (List.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.sublistsAux.{u1, u2} α β (List.cons.{u1} α a l) f) (List.foldr.{u1, u2} (List.{u1} α) (List.{u2} β) f (List.nil.{u2} β) (List.sublistsAux.{u1, u1} α (List.{u1} α) (List.cons.{u1} α a l) (List.cons.{u1} (List.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux_eq_foldr.aux [anonymous]ₓ'. -/
theorem [anonymous] {a : α} {l : List α}
    (IH₁ : ∀ f : List α → List β → List β, sublistsAux l f = foldr f [] (sublistsAux l cons))
    (IH₂ :
      ∀ f : List α → List (List α) → List (List α),
        sublistsAux l f = foldr f [] (sublistsAux l cons))
    (f : List α → List β → List β) :
    sublistsAux (a :: l) f = foldr f [] (sublistsAux (a :: l) cons) :=
  by
  simp only [sublists_aux, foldr_cons]; rw [IH₂, IH₁]; congr 1
  induction' sublists_aux l cons with _ _ ih; · rfl
  simp only [ih, foldr_cons]
#align list.sublists_aux_eq_foldr.aux[anonymous]

/- warning: list.sublists_aux_eq_foldr clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux_eq_foldr -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : (List.{u1} α) -> (List.{u2} β) -> (List.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.sublistsAux.{u1, u2} α β l f) (List.foldr.{u1, u2} (List.{u1} α) (List.{u2} β) f (List.nil.{u2} β) (List.sublistsAux.{u1, u1} α (List.{u1} α) l (List.cons.{u1} (List.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux_eq_foldr [anonymous]ₓ'. -/
theorem [anonymous] (l : List α) :
    ∀ f : List α → List β → List β, sublistsAux l f = foldr f [] (sublistsAux l cons) :=
  by
  suffices
    _ ∧
      ∀ f : List α → List (List α) → List (List α),
        sublistsAux l f = foldr f [] (sublistsAux l cons)
    from this.1
  induction' l with a l IH; · constructor <;> intro <;> rfl
  exact ⟨sublists_aux_eq_foldr.aux IH.1 IH.2, sublists_aux_eq_foldr.aux IH.2 IH.2⟩
#align list.sublists_aux_eq_foldr[anonymous]

/- warning: list.sublists_aux_cons_cons clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux_cons_cons -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (l : List.{u} α) (a : α), Eq.{succ u} (List.{u} (List.{u} α)) (List.sublistsAux.{u, u} α (List.{u} α) (List.cons.{u} α a l) (List.cons.{u} (List.{u} α))) (List.cons.{u} (List.{u} α) (List.cons.{u} α a (List.nil.{u} α)) (List.foldr.{u, u} (List.{u} α) (List.{u} (List.{u} α)) (fun (ys : List.{u} α) (r : List.{u} (List.{u} α)) => List.cons.{u} (List.{u} α) ys (List.cons.{u} (List.{u} α) (List.cons.{u} α a ys) r)) (List.nil.{u} (List.{u} α)) (List.sublistsAux.{u, u} α (List.{u} α) l (List.cons.{u} (List.{u} α)))))
but is expected to have type
  forall {α : Type.{u}} {l : Type.{v}}, (Nat -> α -> l) -> Nat -> (List.{u} α) -> (List.{v} l)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux_cons_cons [anonymous]ₓ'. -/
theorem [anonymous] (l : List α) (a : α) :
    sublistsAux (a :: l) cons =
      [a] :: foldr (fun ys r => ys :: (a :: ys) :: r) [] (sublistsAux l cons) :=
  by rw [← sublists_aux_eq_foldr] <;> rfl
#align list.sublists_aux_cons_cons[anonymous]

/- warning: list.sublists_aux₁_append clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux₁_append -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l₁ : List.{u1} α) (l₂ : List.{u1} α) (f : (List.{u1} α) -> (List.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.sublistsAux₁.{u1, u2} α β (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂) f) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (List.sublistsAux₁.{u1, u2} α β l₁ f) (List.sublistsAux₁.{u1, u2} α β l₂ (fun (x : List.{u1} α) => Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (f x) (List.sublistsAux₁.{u1, u2} α β l₁ (Function.comp.{succ u1, succ u1, succ u2} (List.{u1} α) (List.{u1} α) (List.{u2} β) f (fun (_x : List.{u1} α) => Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) _x x))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux₁_append [anonymous]ₓ'. -/
theorem [anonymous] :
    ∀ (l₁ l₂ : List α) (f : List α → List β),
      sublistsAux₁ (l₁ ++ l₂) f =
        sublistsAux₁ l₁ f ++ sublistsAux₁ l₂ fun x => f x ++ sublistsAux₁ l₁ (f ∘ (· ++ x))
  | [], l₂, f => by simp only [sublists_aux₁, nil_append, append_nil]
  | a :: l₁, l₂, f => by
    simp only [sublists_aux₁, cons_append, sublists_aux₁_append l₁, append_assoc] <;> rfl
#align list.sublists_aux₁_append[anonymous]

/- warning: list.sublists_aux₁_concat clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux₁_concat -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (a : α) (f : (List.{u1} α) -> (List.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.sublistsAux₁.{u1, u2} α β (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l (List.cons.{u1} α a (List.nil.{u1} α))) f) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (List.sublistsAux₁.{u1, u2} α β l f) (f (List.cons.{u1} α a (List.nil.{u1} α)))) (List.sublistsAux₁.{u1, u2} α β l (fun (x : List.{u1} α) => f (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) x (List.cons.{u1} α a (List.nil.{u1} α))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux₁_concat [anonymous]ₓ'. -/
theorem [anonymous] (l : List α) (a : α) (f : List α → List β) :
    sublistsAux₁ (l ++ [a]) f = sublistsAux₁ l f ++ f [a] ++ sublistsAux₁ l fun x => f (x ++ [a]) :=
  by simp only [sublists_aux₁_append, sublists_aux₁, append_assoc, append_nil]
#align list.sublists_aux₁_concat[anonymous]

/- warning: list.sublists_aux₁_bind clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux₁_bind -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} (l : List.{u} α) (f : (List.{u} α) -> (List.{v} β)) (g : β -> (List.{w} γ)), Eq.{succ w} (List.{w} γ) (List.bind.{v, w} β γ (List.sublistsAux₁.{u, v} α β l f) g) (List.sublistsAux₁.{u, w} α γ l (fun (x : List.{u} α) => List.bind.{v, w} β γ (f x) g))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}}, (Nat -> α -> β) -> Nat -> (List.{u} α) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux₁_bind [anonymous]ₓ'. -/
theorem [anonymous] :
    ∀ (l : List α) (f : List α → List β) (g : β → List γ),
      (sublistsAux₁ l f).bind g = sublistsAux₁ l fun x => (f x).bind g
  | [], f, g => rfl
  | a :: l, f, g => by simp only [sublists_aux₁, bind_append, sublists_aux₁_bind l]
#align list.sublists_aux₁_bind[anonymous]

/- warning: list.sublists_aux_cons_append clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux_cons_append -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (l₁ : List.{u} α) (l₂ : List.{u} α), Eq.{succ u} (List.{u} (List.{u} α)) (List.sublistsAux.{u, u} α (List.{u} α) (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l₁ l₂) (List.cons.{u} (List.{u} α))) (Append.append.{u} (List.{u} (List.{u} α)) (List.hasAppend.{u} (List.{u} α)) (List.sublistsAux.{u, u} α (List.{u} α) l₁ (List.cons.{u} (List.{u} α))) (Bind.bind.{u, u} List.{u} (Monad.toHasBind.{u, u} List.{u} List.monad.{u}) (List.{u} α) (List.{u} α) (List.sublistsAux.{u, u} α (List.{u} α) l₂ (List.cons.{u} (List.{u} α))) (fun (x : List.{u} α) => Functor.map.{u, u} List.{u} (Traversable.toFunctor.{u} List.{u} List.traversable.{u}) (List.{u} α) (List.{u} α) (fun (_x : List.{u} α) => Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) _x x) (List.sublists.{u} α l₁))))
but is expected to have type
  forall {α : Type.{u}} {l₁ : Type.{v}}, (Nat -> α -> l₁) -> Nat -> (List.{u} α) -> (List.{v} l₁)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux_cons_append [anonymous]ₓ'. -/
theorem [anonymous] (l₁ l₂ : List α) :
    sublistsAux (l₁ ++ l₂) cons =
      sublistsAux l₁ cons ++ do
        let x ← sublistsAux l₂ cons
        (· ++ x) <$> sublists l₁ :=
  by
  simp only [sublists, sublists_aux_cons_eq_sublists_aux₁, sublists_aux₁_append, bind_eq_bind,
    sublists_aux₁_bind]
  congr ; funext x; apply congr_arg _
  rw [← bind_ret_eq_map, sublists_aux₁_bind]; exact (append_nil _).symm
#align list.sublists_aux_cons_append[anonymous]

/- warning: list.sublists_append -> List.sublists_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u1} (List.{u1} (List.{u1} α)) (List.sublists.{u1} α (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (Bind.bind.{u1, u1} List.{u1} (Monad.toHasBind.{u1, u1} List.{u1} List.monad.{u1}) (List.{u1} α) (List.{u1} α) (List.sublists.{u1} α l₂) (fun (x : List.{u1} α) => Functor.map.{u1, u1} List.{u1} (Traversable.toFunctor.{u1} List.{u1} List.traversable.{u1}) (List.{u1} α) (List.{u1} α) (fun (_x : List.{u1} α) => Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) _x x) (List.sublists.{u1} α l₁)))
but is expected to have type
  forall {α : Type.{u1}} (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u1} (List.{u1} (List.{u1} α)) (List.sublists.{u1} α (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) l₁ l₂)) (Bind.bind.{u1, u1} List.{u1} (Monad.toBind.{u1, u1} List.{u1} List.instMonadList.{u1}) (List.{u1} α) (List.{u1} α) (List.sublists.{u1} α l₂) (fun (x : List.{u1} α) => List.map.{u1, u1} (List.{u1} α) (List.{u1} α) (fun (_x : List.{u1} α) => HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) _x x) (List.sublists.{u1} α l₁)))
Case conversion may be inaccurate. Consider using '#align list.sublists_append List.sublists_appendₓ'. -/
theorem sublists_append (l₁ l₂ : List α) :
    sublists (l₁ ++ l₂) = do
      let x ← sublists l₂
      (· ++ x) <$> sublists l₁ :=
  by
  simp only [map, sublists, sublists_aux_cons_append, map_eq_map, bind_eq_bind, cons_bind, map_id',
        append_nil, cons_append, map_id' fun _ => rfl] <;>
      constructor <;>
    rfl
#align list.sublists_append List.sublists_append

#print List.sublists_concat /-
@[simp]
theorem sublists_concat (l : List α) (a : α) :
    sublists (l ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l) := by
  rw [sublists_append, sublists_singleton, bind_eq_bind, cons_bind, cons_bind, nil_bind, map_eq_map,
    map_eq_map, map_id' append_nil, append_nil]
#align list.sublists_concat List.sublists_concat
-/

#print List.sublists_reverse /-
theorem sublists_reverse (l : List α) : sublists (reverse l) = map reverse (sublists' l) := by
  induction' l with hd tl ih <;> [rfl,
    simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
      map_eq_map, bind_eq_bind, map_map, cons_bind, append_nil, nil_bind, (· ∘ ·)]]
#align list.sublists_reverse List.sublists_reverse
-/

#print List.sublists_eq_sublists' /-
theorem sublists_eq_sublists' (l : List α) : sublists l = map reverse (sublists' (reverse l)) := by
  rw [← sublists_reverse, reverse_reverse]
#align list.sublists_eq_sublists' List.sublists_eq_sublists'
-/

#print List.sublists'_reverse /-
theorem sublists'_reverse (l : List α) : sublists' (reverse l) = map reverse (sublists l) := by
  simp only [sublists_eq_sublists', map_map, map_id' reverse_reverse]
#align list.sublists'_reverse List.sublists'_reverse
-/

#print List.sublists'_eq_sublists /-
theorem sublists'_eq_sublists (l : List α) : sublists' l = map reverse (sublists (reverse l)) := by
  rw [← sublists'_reverse, reverse_reverse]
#align list.sublists'_eq_sublists List.sublists'_eq_sublists
-/

/- warning: list.sublists_aux_ne_nil clashes with [anonymous] -> [anonymous]
warning: list.sublists_aux_ne_nil -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (l : List.{u} α), Not (Membership.Mem.{u, u} (List.{u} α) (List.{u} (List.{u} α)) (List.hasMem.{u} (List.{u} α)) (List.nil.{u} α) (List.sublistsAux.{u, u} α (List.{u} α) l (List.cons.{u} (List.{u} α))))
but is expected to have type
  forall {α : Type.{u}} {l : Type.{v}}, (Nat -> α -> l) -> Nat -> (List.{u} α) -> (List.{v} l)
Case conversion may be inaccurate. Consider using '#align list.sublists_aux_ne_nil [anonymous]ₓ'. -/
theorem [anonymous] : ∀ l : List α, [] ∉ sublistsAux l cons
  | [] => id
  | a :: l => by
    rw [sublists_aux_cons_cons]
    refine' not_mem_cons_of_ne_of_not_mem (cons_ne_nil _ _).symm _
    have := sublists_aux_ne_nil l; revert this
    induction sublists_aux l cons <;> intro ; · rwa [foldr]
    simp only [foldr, mem_cons_iff, false_or_iff, not_or]
    exact ⟨ne_of_not_mem_cons this, ih (not_mem_of_not_mem_cons this)⟩
#align list.sublists_aux_ne_nil[anonymous]

#print List.mem_sublists /-
@[simp]
theorem mem_sublists {s t : List α} : s ∈ sublists t ↔ s <+ t := by
  rw [← reverse_sublist_iff, ← mem_sublists', sublists'_reverse,
    mem_map_of_injective reverse_injective]
#align list.mem_sublists List.mem_sublists
-/

#print List.length_sublists /-
@[simp]
theorem length_sublists (l : List α) : length (sublists l) = 2 ^ length l := by
  simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]
#align list.length_sublists List.length_sublists
-/

#print List.map_ret_sublist_sublists /-
theorem map_ret_sublist_sublists (l : List α) : map List.ret l <+ sublists l :=
  reverseRecOn l (nil_sublist _) fun l a IH => by
    simp only [map, map_append, sublists_concat] <;>
      exact
        ((append_sublist_append_left _).2 <|
              singleton_sublist.2 <| mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by rfl⟩).trans
          ((append_sublist_append_right _).2 IH)
#align list.map_ret_sublist_sublists List.map_ret_sublist_sublists
-/

/-! ### sublists_len -/


#print List.sublistsLenAux /-
/-- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
of `f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
def sublistsLenAux {α β : Type _} : ℕ → List α → (List α → β) → List β → List β
  | 0, l, f, r => f [] :: r
  | n + 1, [], f, r => r
  | n + 1, a :: l, f, r => sublists_len_aux (n + 1) l f (sublists_len_aux n l (f ∘ List.cons a) r)
#align list.sublists_len_aux List.sublistsLenAux
-/

#print List.sublistsLen /-
/-- The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`. -/
def sublistsLen {α : Type _} (n : ℕ) (l : List α) : List (List α) :=
  sublistsLenAux n l id []
#align list.sublists_len List.sublistsLen
-/

/- warning: list.sublists_len_aux_append -> List.sublistsLenAux_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (n : Nat) (l : List.{u1} α) (f : (List.{u1} α) -> β) (g : β -> γ) (r : List.{u2} β) (s : List.{u3} γ), Eq.{succ u3} (List.{u3} γ) (List.sublistsLenAux.{u1, u3} α γ n l (Function.comp.{succ u1, succ u2, succ u3} (List.{u1} α) β γ g f) (Append.append.{u3} (List.{u3} γ) (List.hasAppend.{u3} γ) (List.map.{u2, u3} β γ g r) s)) (Append.append.{u3} (List.{u3} γ) (List.hasAppend.{u3} γ) (List.map.{u2, u3} β γ g (List.sublistsLenAux.{u1, u2} α β n l f r)) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (n : Nat) (l : List.{u3} α) (f : (List.{u3} α) -> β) (g : β -> γ) (r : List.{u2} β) (s : List.{u1} γ), Eq.{succ u1} (List.{u1} γ) (List.sublistsLenAux.{u3, u1} α γ n l (Function.comp.{succ u3, succ u2, succ u1} (List.{u3} α) β γ g f) (HAppend.hAppend.{u1, u1, u1} (List.{u1} γ) (List.{u1} γ) (List.{u1} γ) (instHAppend.{u1} (List.{u1} γ) (List.instAppendList.{u1} γ)) (List.map.{u2, u1} β γ g r) s)) (HAppend.hAppend.{u1, u1, u1} (List.{u1} γ) (List.{u1} γ) (List.{u1} γ) (instHAppend.{u1} (List.{u1} γ) (List.instAppendList.{u1} γ)) (List.map.{u2, u1} β γ g (List.sublistsLenAux.{u3, u2} α β n l f r)) s)
Case conversion may be inaccurate. Consider using '#align list.sublists_len_aux_append List.sublistsLenAux_appendₓ'. -/
theorem sublistsLenAux_append {α β γ : Type _} :
    ∀ (n : ℕ) (l : List α) (f : List α → β) (g : β → γ) (r : List β) (s : List γ),
      sublistsLenAux n l (g ∘ f) (r.map g ++ s) = (sublistsLenAux n l f r).map g ++ s
  | 0, l, f, g, r, s => rfl
  | n + 1, [], f, g, r, s => rfl
  | n + 1, a :: l, f, g, r, s => by
    unfold sublists_len_aux
    rw [show (g ∘ f) ∘ List.cons a = g ∘ f ∘ List.cons a by rfl, sublists_len_aux_append,
      sublists_len_aux_append]
#align list.sublists_len_aux_append List.sublistsLenAux_append

/- warning: list.sublists_len_aux_eq -> List.sublistsLenAux_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (n : Nat) (f : (List.{u1} α) -> β) (r : List.{u2} β), Eq.{succ u2} (List.{u2} β) (List.sublistsLenAux.{u1, u2} α β n l f r) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (List.map.{u1, u2} (List.{u1} α) β f (List.sublistsLen.{u1} α n l)) r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α) (n : Nat) (f : (List.{u2} α) -> β) (r : List.{u1} β), Eq.{succ u1} (List.{u1} β) (List.sublistsLenAux.{u2, u1} α β n l f r) (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) (List.map.{u2, u1} (List.{u2} α) β f (List.sublistsLen.{u2} α n l)) r)
Case conversion may be inaccurate. Consider using '#align list.sublists_len_aux_eq List.sublistsLenAux_eqₓ'. -/
theorem sublistsLenAux_eq {α β : Type _} (l : List α) (n) (f : List α → β) (r) :
    sublistsLenAux n l f r = (sublistsLen n l).map f ++ r := by
  rw [sublists_len, ← sublists_len_aux_append] <;> rfl
#align list.sublists_len_aux_eq List.sublistsLenAux_eq

/- warning: list.sublists_len_aux_zero -> List.sublistsLenAux_zero is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} (l : List.{u2} α) (f : (List.{u2} α) -> β) (r : List.{u1} β), Eq.{succ u1} (List.{u1} β) (List.sublistsLenAux.{u2, u1} α β (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) l f r) (List.cons.{u1} β (f (List.nil.{u2} α)) r)
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} (l : List.{u1} α) (f : (List.{u1} α) -> β) (r : List.{u2} β), Eq.{succ u2} (List.{u2} β) (List.sublistsLenAux.{u1, u2} α β (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) l f r) (List.cons.{u2} β (f (List.nil.{u1} α)) r)
Case conversion may be inaccurate. Consider using '#align list.sublists_len_aux_zero List.sublistsLenAux_zeroₓ'. -/
theorem sublistsLenAux_zero {α : Type _} (l : List α) (f : List α → β) (r) :
    sublistsLenAux 0 l f r = f [] :: r := by cases l <;> rfl
#align list.sublists_len_aux_zero List.sublistsLenAux_zero

#print List.sublistsLen_zero /-
@[simp]
theorem sublistsLen_zero {α : Type _} (l : List α) : sublistsLen 0 l = [[]] :=
  sublistsLenAux_zero _ _ _
#align list.sublists_len_zero List.sublistsLen_zero
-/

#print List.sublistsLen_succ_nil /-
@[simp]
theorem sublistsLen_succ_nil {α : Type _} (n) : sublistsLen (n + 1) (@nil α) = [] :=
  rfl
#align list.sublists_len_succ_nil List.sublistsLen_succ_nil
-/

#print List.sublistsLen_succ_cons /-
@[simp]
theorem sublistsLen_succ_cons {α : Type _} (n) (a : α) (l) :
    sublistsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons a) := by
  rw [sublists_len, sublists_len_aux, sublists_len_aux_eq, sublists_len_aux_eq, map_id,
      append_nil] <;>
    rfl
#align list.sublists_len_succ_cons List.sublistsLen_succ_cons
-/

#print List.length_sublistsLen /-
@[simp]
theorem length_sublistsLen {α : Type _} :
    ∀ (n) (l : List α), length (sublistsLen n l) = Nat.choose (length l) n
  | 0, l => by simp
  | n + 1, [] => by simp
  | n + 1, a :: l => by simp [-add_comm, Nat.choose, *] <;> apply add_comm
#align list.length_sublists_len List.length_sublistsLen
-/

#print List.sublistsLen_sublist_sublists' /-
theorem sublistsLen_sublist_sublists' {α : Type _} :
    ∀ (n) (l : List α), sublistsLen n l <+ sublists' l
  | 0, l => singleton_sublist.2 (mem_sublists'.2 (nil_sublist _))
  | n + 1, [] => nil_sublist _
  | n + 1, a :: l => by
    rw [sublists_len_succ_cons, sublists'_cons]
    exact (sublists_len_sublist_sublists' _ _).append ((sublists_len_sublist_sublists' _ _).map _)
#align list.sublists_len_sublist_sublists' List.sublistsLen_sublist_sublists'
-/

#print List.sublistsLen_sublist_of_sublist /-
theorem sublistsLen_sublist_of_sublist {α : Type _} (n) {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    sublistsLen n l₁ <+ sublistsLen n l₂ :=
  by
  induction' n with n IHn generalizing l₁ l₂; · simp
  induction' h with l₁ l₂ a s IH l₁ l₂ a s IH; · rfl
  · refine' IH.trans _
    rw [sublists_len_succ_cons]
    apply sublist_append_left
  · simp [sublists_len_succ_cons]
    exact IH.append ((IHn s).map _)
#align list.sublists_len_sublist_of_sublist List.sublistsLen_sublist_of_sublist
-/

#print List.length_of_sublistsLen /-
theorem length_of_sublistsLen {α : Type _} :
    ∀ {n} {l l' : List α}, l' ∈ sublistsLen n l → length l' = n
  | 0, l, l', Or.inl rfl => rfl
  | n + 1, a :: l, l', h =>
    by
    rw [sublists_len_succ_cons, mem_append, mem_map] at h
    rcases h with (h | ⟨l', h, rfl⟩)
    · exact length_of_sublists_len h
    · exact congr_arg (· + 1) (length_of_sublists_len h)
#align list.length_of_sublists_len List.length_of_sublistsLen
-/

#print List.mem_sublistsLen_self /-
theorem mem_sublistsLen_self {α : Type _} {l l' : List α} (h : l' <+ l) :
    l' ∈ sublistsLen (length l') l :=
  by
  induction' h with l₁ l₂ a s IH l₁ l₂ a s IH
  · exact Or.inl rfl
  · cases' l₁ with b l₁
    · exact Or.inl rfl
    · rw [length, sublists_len_succ_cons]
      exact mem_append_left _ IH
  · rw [length, sublists_len_succ_cons]
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩)
#align list.mem_sublists_len_self List.mem_sublistsLen_self
-/

#print List.mem_sublistsLen /-
@[simp]
theorem mem_sublistsLen {α : Type _} {n} {l l' : List α} :
    l' ∈ sublistsLen n l ↔ l' <+ l ∧ length l' = n :=
  ⟨fun h =>
    ⟨mem_sublists'.1 ((sublistsLen_sublist_sublists' _ _).Subset h), length_of_sublistsLen h⟩,
    fun ⟨h₁, h₂⟩ => h₂ ▸ mem_sublistsLen_self h₁⟩
#align list.mem_sublists_len List.mem_sublistsLen
-/

#print List.sublistsLen_of_length_lt /-
theorem sublistsLen_of_length_lt {n} {l : List α} (h : l.length < n) : sublistsLen n l = [] :=
  eq_nil_iff_forall_not_mem.mpr fun x =>
    mem_sublistsLen.Not.mpr fun ⟨hs, hl⟩ => (h.trans_eq hl.symm).not_le (Sublist.length_le hs)
#align list.sublists_len_of_length_lt List.sublistsLen_of_length_lt
-/

#print List.sublistsLen_length /-
@[simp]
theorem sublistsLen_length : ∀ l : List α, sublistsLen l.length l = [l]
  | [] => rfl
  | a :: l => by
    rw [length, sublists_len_succ_cons, sublists_len_length, map_singleton,
      sublists_len_of_length_lt (lt_succ_self _), nil_append]
#align list.sublists_len_length List.sublistsLen_length
-/

open Function

#print List.Pairwise.sublists' /-
theorem Pairwise.sublists' {R} :
    ∀ {l : List α}, Pairwise R l → Pairwise (Lex (swap R)) (sublists' l)
  | _, pairwise.nil => pairwise_singleton _ _
  | _, @pairwise.cons _ _ a l H₁ H₂ =>
    by
    simp only [sublists'_cons, pairwise_append, pairwise_map, mem_sublists', mem_map, exists_imp,
      and_imp]
    refine' ⟨H₂.sublists', H₂.sublists'.imp fun l₁ l₂ => lex.cons, _⟩
    rintro l₁ sl₁ x l₂ sl₂ rfl
    cases' l₁ with b l₁; · constructor
    exact lex.rel (H₁ _ <| sl₁.subset <| mem_cons_self _ _)
#align list.pairwise.sublists' List.Pairwise.sublists'
-/

#print List.pairwise_sublists /-
theorem pairwise_sublists {R} {l : List α} (H : Pairwise R l) :
    Pairwise (fun l₁ l₂ => Lex R (reverse l₁) (reverse l₂)) (sublists l) :=
  by
  have := (pairwise_reverse.2 H).sublists'
  rwa [sublists'_reverse, pairwise_map] at this
#align list.pairwise_sublists List.pairwise_sublists
-/

#print List.nodup_sublists /-
@[simp]
theorem nodup_sublists {l : List α} : Nodup (sublists l) ↔ Nodup l :=
  ⟨fun h => (h.Sublist (map_ret_sublist_sublists _)).of_map _, fun h =>
    (pairwise_sublists h).imp fun _ _ h => mt reverse_inj.2 h.to_ne⟩
#align list.nodup_sublists List.nodup_sublists
-/

#print List.nodup_sublists' /-
@[simp]
theorem nodup_sublists' {l : List α} : Nodup (sublists' l) ↔ Nodup l := by
  rw [sublists'_eq_sublists, nodup_map_iff reverse_injective, nodup_sublists, nodup_reverse]
#align list.nodup_sublists' List.nodup_sublists'
-/

alias nodup_sublists ↔ nodup.of_sublists nodup.sublists
#align list.nodup.of_sublists List.nodup.of_sublists
#align list.nodup.sublists List.nodup.sublists

alias nodup_sublists' ↔ nodup.of_sublists' nodup.sublists'
#align list.nodup.of_sublists' List.nodup.of_sublists'
#align list.nodup.sublists' List.nodup.sublists'

attribute [protected] nodup.sublists nodup.sublists'

#print List.nodup_sublistsLen /-
theorem nodup_sublistsLen (n : ℕ) {l : List α} (h : Nodup l) : (sublistsLen n l).Nodup :=
  h.sublists'.Sublist <| sublistsLen_sublist_sublists' _ _
#align list.nodup_sublists_len List.nodup_sublistsLen
-/

#print List.sublists_cons_perm_append /-
theorem sublists_cons_perm_append (a : α) (l : List α) :
    sublists (a :: l) ~ sublists l ++ map (cons a) (sublists l) :=
  by
  simp only [sublists, sublists_aux_cons_cons, cons_append, perm_cons]
  refine' (perm.cons _ _).trans perm_middle.symm
  induction' sublists_aux l cons with b l IH <;> simp
  exact (IH.cons _).trans perm_middle.symm
#align list.sublists_cons_perm_append List.sublists_cons_perm_append
-/

#print List.sublists_perm_sublists' /-
theorem sublists_perm_sublists' : ∀ l : List α, sublists l ~ sublists' l
  | [] => Perm.refl _
  | a :: l => by
    let IH := sublists_perm_sublists' l
    rw [sublists'_cons] <;> exact (sublists_cons_perm_append _ _).trans (IH.append (IH.map _))
#align list.sublists_perm_sublists' List.sublists_perm_sublists'
-/

#print List.revzip_sublists /-
theorem revzip_sublists (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists → l₁ ++ l₂ ~ l :=
  by
  rw [revzip]
  apply List.reverseRecOn l
  · intro l₁ l₂ h
    simp at h
    simp [h]
  · intro l a IH l₁ l₂ h
    rw [sublists_concat, reverse_append, zip_append, ← map_reverse, zip_map_right, zip_map_left] at
        h <;>
      [skip, · simp]
    simp only [Prod.mk.inj_iff, mem_map, mem_append, Prod.map_mk, Prod.exists] at h
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩)
    · rw [← append_assoc]
      exact (IH _ _ h).append_right _
    · rw [append_assoc]
      apply (perm_append_comm.append_left _).trans
      rw [← append_assoc]
      exact (IH _ _ h).append_right _
#align list.revzip_sublists List.revzip_sublists
-/

#print List.revzip_sublists' /-
theorem revzip_sublists' (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists' → l₁ ++ l₂ ~ l :=
  by
  rw [revzip]
  induction' l with a l IH <;> intro l₁ l₂ h
  · simp at h
    simp [h]
  · rw [sublists'_cons, reverse_append, zip_append, ← map_reverse, zip_map_right, zip_map_left] at
        h <;> [simp at h, simp]
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', h, rfl⟩)
    · exact perm_middle.trans ((IH _ _ h).cons _)
    · exact (IH _ _ h).cons _
#align list.revzip_sublists' List.revzip_sublists'
-/

#print List.range_bind_sublistsLen_perm /-
theorem range_bind_sublistsLen_perm {α : Type _} (l : List α) :
    ((List.range (l.length + 1)).bind fun n => sublistsLen n l) ~ sublists' l :=
  by
  induction' l with h tl
  · simp [range_succ]
  · simp_rw [range_succ_eq_map, length, cons_bind, map_bind, sublists_len_succ_cons, sublists'_cons,
      List.sublistsLen_zero, List.singleton_append]
    refine' ((bind_append_perm (range (tl.length + 1)) _ _).symm.cons _).trans _
    simp_rw [← List.bind_map, ← cons_append]
    rw [← List.singleton_append, ← List.sublistsLen_zero tl]
    refine' perm.append _ (l_ih.map _)
    rw [List.range_succ, append_bind, bind_singleton,
      sublists_len_of_length_lt (Nat.lt_succ_self _), append_nil, ←
      List.map_bind (fun n => sublists_len n tl) Nat.succ, ←
      cons_bind 0 _ fun n => sublists_len n tl, ← range_succ_eq_map]
    exact l_ih
#align list.range_bind_sublists_len_perm List.range_bind_sublistsLen_perm
-/

end List

