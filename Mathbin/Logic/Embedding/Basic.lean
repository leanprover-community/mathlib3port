/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.FunLike.Embedding
import Mathbin.Data.Prod.Pprod
import Mathbin.Data.Sigma.Basic
import Mathbin.Data.Option.Basic
import Mathbin.Data.Subtype
import Mathbin.Logic.Equiv.Basic

/-!
# Injective functions
-/


universe u v w x

namespace Function

/- warning: function.embedding -> Function.Embedding is a dubious translation:
lean 3 declaration is
  Sort.{u_1} -> Sort.{u_2} -> Sort.{max 1 (imax u_1 u_2)}
but is expected to have type
  Sort.{u_1} -> Sort.{u_2} -> Sort.{max (max 1 u_1) u_2}
Case conversion may be inaccurate. Consider using '#align function.embedding Function.Embeddingₓ'. -/
-- depending on cardinalities, an injective function may not exist
/-- `α ↪ β` is a bundled injective function. -/
@[nolint has_nonempty_instance]
structure Embedding (α : Sort _) (β : Sort _) where
  toFun : α → β
  inj' : Injective to_fun
#align function.embedding Function.Embedding

-- mathport name: «expr ↪ »
infixr:25 " ↪ " => Embedding

instance {α : Sort u} {β : Sort v} : CoeFun (α ↪ β) fun _ => α → β :=
  ⟨Embedding.toFun⟩

initialize_simps_projections Embedding (toFun → apply)

instance {α : Sort u} {β : Sort v} :
    EmbeddingLike (α ↪ β) α β where 
  coe := Embedding.toFun
  injective' := Embedding.inj'
  coe_injective' f g h := by 
    cases f
    cases g
    congr

instance {α β : Sort _} : CanLift (α → β) (α ↪ β) coeFn Injective where prf f hf := ⟨⟨f, hf⟩, rfl⟩

end Function

section Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

#print Equiv.toEmbedding /-
/-- Convert an `α ≃ β` to `α ↪ β`.

This is also available as a coercion `equiv.coe_embedding`.
The explicit `equiv.to_embedding` version is preferred though, since the coercion can have issues
inferring the type of the resulting embedding. For example:

```lean
-- Works:
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f.to_embedding = s.map f := by simp
-- Error, `f` has type `fin 3 ≃ fin 3` but is expected to have type `fin 3 ↪ ?m_1 : Type ?`
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f = s.map f.to_embedding := by simp
```
-/
protected def Equiv.toEmbedding : α ↪ β :=
  ⟨f, f.Injective⟩
#align equiv.to_embedding Equiv.toEmbedding
-/

#print Equiv.coe_toEmbedding /-
@[simp]
theorem Equiv.coe_toEmbedding : ⇑f.toEmbedding = f :=
  rfl
#align equiv.coe_to_embedding Equiv.coe_toEmbedding
-/

#print Equiv.toEmbedding_apply /-
theorem Equiv.toEmbedding_apply (a : α) : f.toEmbedding a = f a :=
  rfl
#align equiv.to_embedding_apply Equiv.toEmbedding_apply
-/

/- warning: equiv.coe_embedding -> Equiv.coeEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u}} {β : Sort.{v}}, Coe.{max 1 (imax u v) (imax v u), max 1 (imax u v)} (Equiv.{u, v} α β) (Function.Embedding.{u, v} α β)
but is expected to have type
  forall {α : Sort.{u}} {β : Sort.{v}}, Coe.{max (max 1 v) u, max (max 1 v) u} (Equiv.{u, v} α β) (Function.Embedding.{u, v} α β)
Case conversion may be inaccurate. Consider using '#align equiv.coe_embedding Equiv.coeEmbeddingₓ'. -/
instance Equiv.coeEmbedding : Coe (α ≃ β) (α ↪ β) :=
  ⟨Equiv.toEmbedding⟩
#align equiv.coe_embedding Equiv.coeEmbedding

#print Equiv.Perm.coeEmbedding /-
@[reducible]
instance Equiv.Perm.coeEmbedding : Coe (Equiv.Perm α) (α ↪ α) :=
  Equiv.coeEmbedding
#align equiv.perm.coe_embedding Equiv.Perm.coeEmbedding
-/

@[simp]
theorem Equiv.coe_eq_to_embedding : ↑f = f.toEmbedding :=
  rfl
#align equiv.coe_eq_to_embedding Equiv.coe_eq_to_embedding

/- warning: equiv.as_embedding -> Equiv.asEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u}} {β : Sort.{v}} {p : β -> Prop}, (Equiv.{u, max 1 v} α (Subtype.{v} β p)) -> (Function.Embedding.{u, v} α β)
but is expected to have type
  forall {β : Sort.{u_1}} {α : Sort.{u_2}} {p : β -> Prop}, (Equiv.{u_2, max 1 u_1} α (Subtype.{u_1} β p)) -> (Function.Embedding.{u_2, u_1} α β)
Case conversion may be inaccurate. Consider using '#align equiv.as_embedding Equiv.asEmbeddingₓ'. -/
/-- Given an equivalence to a subtype, produce an embedding to the elements of the corresponding
set. -/
@[simps]
def Equiv.asEmbedding {p : β → Prop} (e : α ≃ Subtype p) : α ↪ β :=
  ⟨coe ∘ e, Subtype.coe_injective.comp e.Injective⟩
#align equiv.as_embedding Equiv.asEmbedding

end Equiv

namespace Function

namespace Embedding

/- warning: function.embedding.coe_injective -> Function.Embedding.coe_injective is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Function.Injective.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (α -> β) (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (ᾰ : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Function.Injective.{max (max 1 u_2) u_1, imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (α -> β) (fun (f : Function.Embedding.{u_1, u_2} α β) => FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) f)
Case conversion may be inaccurate. Consider using '#align function.embedding.coe_injective Function.Embedding.coe_injectiveₓ'. -/
theorem coe_injective {α β} : @Function.Injective (α ↪ β) (α → β) coeFn :=
  FunLike.coe_injective
#align function.embedding.coe_injective Function.Embedding.coe_injective

/- warning: function.embedding.ext -> Function.Embedding.ext is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {f : Function.Embedding.{u_1, u_2} α β} {g : Function.Embedding.{u_1, u_2} α β}, (forall (x : α), Eq.{u_2} β (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) f x) (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) g x)) -> (Eq.{max 1 (imax u_1 u_2)} (Function.Embedding.{u_1, u_2} α β) f g)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {f : Function.Embedding.{u_1, u_2} α β} {g : Function.Embedding.{u_1, u_2} α β}, (forall (x : α), Eq.{u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) f x) (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) g x)) -> (Eq.{max (max 1 u_2) u_1} (Function.Embedding.{u_1, u_2} α β) f g)
Case conversion may be inaccurate. Consider using '#align function.embedding.ext Function.Embedding.extₓ'. -/
@[ext]
theorem ext {α β} {f g : Embedding α β} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align function.embedding.ext Function.Embedding.ext

/- warning: function.embedding.ext_iff -> Function.Embedding.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {f : Function.Embedding.{u_1, u_2} α β} {g : Function.Embedding.{u_1, u_2} α β}, Iff (forall (x : α), Eq.{u_2} β (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) f x) (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) g x)) (Eq.{max 1 (imax u_1 u_2)} (Function.Embedding.{u_1, u_2} α β) f g)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {f : Function.Embedding.{u_1, u_2} α β} {g : Function.Embedding.{u_1, u_2} α β}, Iff (forall (x : α), Eq.{u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) f x) (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) g x)) (Eq.{max (max 1 u_2) u_1} (Function.Embedding.{u_1, u_2} α β) f g)
Case conversion may be inaccurate. Consider using '#align function.embedding.ext_iff Function.Embedding.ext_iffₓ'. -/
theorem ext_iff {α β} {f g : Embedding α β} : (∀ x, f x = g x) ↔ f = g :=
  FunLike.ext_iff.symm
#align function.embedding.ext_iff Function.Embedding.ext_iff

/- warning: function.embedding.to_fun_eq_coe -> Function.Embedding.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : Function.Embedding.{u_1, u_2} α β), Eq.{imax u_1 u_2} (α -> β) (Function.Embedding.toFun.{u_1, u_2} α β f) (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) f)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : Function.Embedding.{u_1, u_2} α β), Eq.{imax u_1 u_2} (α -> β) (Function.Embedding.toFun.{u_1, u_2} α β f) (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) f)
Case conversion may be inaccurate. Consider using '#align function.embedding.to_fun_eq_coe Function.Embedding.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {α β} (f : α ↪ β) : toFun f = f :=
  rfl
#align function.embedding.to_fun_eq_coe Function.Embedding.toFun_eq_coe

/- warning: function.embedding.coe_fn_mk -> Function.Embedding.coeFn_mk is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (i : Function.Injective.{u_1, u_2} α β f), Eq.{imax u_1 u_2} ((fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.mk.{u_1, u_2} α β f i)) (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) (Function.Embedding.mk.{u_1, u_2} α β f i)) f
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (i : Function.Injective.{u_1, u_2} α β f), Eq.{imax u_1 u_2} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (FunLike.coe.{max (max 1 u_1) u_2, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_1) u_2, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) (Function.Embedding.mk.{u_1, u_2} α β f i)) f
Case conversion may be inaccurate. Consider using '#align function.embedding.coe_fn_mk Function.Embedding.coeFn_mkₓ'. -/
@[simp]
theorem coeFn_mk {α β} (f : α → β) (i) : (@mk _ _ f i : α → β) = f :=
  rfl
#align function.embedding.coe_fn_mk Function.Embedding.coeFn_mk

/- warning: function.embedding.mk_coe -> Function.Embedding.mk_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : Function.Embedding.{succ u_1, succ u_2} α β) (inj : Function.Injective.{succ u_1, succ u_2} α β (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f)), Eq.{max 1 (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (Function.Embedding.mk.{succ u_1, succ u_2} α β (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f) inj) f
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : Function.Embedding.{succ u_1, succ u_2} α β) (inj : Function.Injective.{succ u_1, succ u_2} α β (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f)), Eq.{max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (Function.Embedding.mk.{succ u_1, succ u_2} α β (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f) inj) f
Case conversion may be inaccurate. Consider using '#align function.embedding.mk_coe Function.Embedding.mk_coeₓ'. -/
@[simp]
theorem mk_coe {α β : Type _} (f : α ↪ β) (inj) : (⟨f, inj⟩ : α ↪ β) = f := by
  ext
  simp
#align function.embedding.mk_coe Function.Embedding.mk_coe

/- warning: function.embedding.injective -> Function.Embedding.injective is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : Function.Embedding.{u_1, u_2} α β), Function.Injective.{u_1, u_2} α β (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) f)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : Function.Embedding.{u_1, u_2} α β), Function.Injective.{u_1, u_2} α β (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) f)
Case conversion may be inaccurate. Consider using '#align function.embedding.injective Function.Embedding.injectiveₓ'. -/
protected theorem injective {α β} (f : α ↪ β) : Injective f :=
  EmbeddingLike.injective f
#align function.embedding.injective Function.Embedding.injective

/- warning: function.embedding.apply_eq_iff_eq -> Function.Embedding.apply_eq_iff_eq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : Function.Embedding.{u_1, u_2} α β) (x : α) (y : α), Iff (Eq.{u_2} β (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) f x) (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) f y)) (Eq.{u_1} α x y)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : Function.Embedding.{u_1, u_2} α β) (x : α) (y : α), Iff (Eq.{u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) f x) (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) f y)) (Eq.{u_1} α x y)
Case conversion may be inaccurate. Consider using '#align function.embedding.apply_eq_iff_eq Function.Embedding.apply_eq_iff_eqₓ'. -/
theorem apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f
#align function.embedding.apply_eq_iff_eq Function.Embedding.apply_eq_iff_eq

#print Function.Embedding.refl /-
/-- The identity map as a `function.embedding`. -/
@[refl, simps (config := { simpRhs := true })]
protected def refl (α : Sort _) : α ↪ α :=
  ⟨id, injective_id⟩
#align function.embedding.refl Function.Embedding.refl
-/

#print Function.Embedding.trans /-
/-- Composition of `f : α ↪ β` and `g : β ↪ γ`. -/
@[trans, simps (config := { simpRhs := true })]
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
  ⟨g ∘ f, g.Injective.comp f.Injective⟩
#align function.embedding.trans Function.Embedding.trans
-/

/- warning: function.embedding.equiv_to_embedding_trans_symm_to_embedding -> Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (e : Equiv.{u_1, u_2} α β), Eq.{max 1 u_1} (Function.Embedding.{u_1, u_1} α α) (Function.Embedding.trans.{u_1, u_2, u_1} α β α (Equiv.toEmbedding.{u_1, u_2} α β e) (Equiv.toEmbedding.{u_2, u_1} β α (Equiv.symm.{u_1, u_2} α β e))) (Function.Embedding.refl.{u_1} α)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (e : Equiv.{u_1, u_2} α β), Eq.{max 1 u_1} (Function.Embedding.{u_1, u_1} α α) (Function.Embedding.trans.{u_1, u_2, u_1} α β α (Equiv.toEmbedding.{u_1, u_2} α β e) (Equiv.toEmbedding.{u_2, u_1} β α (Equiv.symm.{u_1, u_2} α β e))) (Function.Embedding.refl.{u_1} α)
Case conversion may be inaccurate. Consider using '#align function.embedding.equiv_to_embedding_trans_symm_to_embedding Function.Embedding.equiv_toEmbedding_trans_symm_toEmbeddingₓ'. -/
@[simp]
theorem equiv_toEmbedding_trans_symm_toEmbedding {α β : Sort _} (e : α ≃ β) :
    e.toEmbedding.trans e.symm.toEmbedding = Embedding.refl _ := by
  ext
  simp
#align
  function.embedding.equiv_to_embedding_trans_symm_to_embedding Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding

/- warning: function.embedding.equiv_symm_to_embedding_trans_to_embedding -> Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (e : Equiv.{u_1, u_2} α β), Eq.{max 1 u_2} (Function.Embedding.{u_2, u_2} β β) (Function.Embedding.trans.{u_2, u_1, u_2} β α β (Equiv.toEmbedding.{u_2, u_1} β α (Equiv.symm.{u_1, u_2} α β e)) (Equiv.toEmbedding.{u_1, u_2} α β e)) (Function.Embedding.refl.{u_2} β)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (e : Equiv.{u_1, u_2} α β), Eq.{max 1 u_2} (Function.Embedding.{u_2, u_2} β β) (Function.Embedding.trans.{u_2, u_1, u_2} β α β (Equiv.toEmbedding.{u_2, u_1} β α (Equiv.symm.{u_1, u_2} α β e)) (Equiv.toEmbedding.{u_1, u_2} α β e)) (Function.Embedding.refl.{u_2} β)
Case conversion may be inaccurate. Consider using '#align function.embedding.equiv_symm_to_embedding_trans_to_embedding Function.Embedding.equiv_symm_toEmbedding_trans_toEmbeddingₓ'. -/
@[simp]
theorem equiv_symm_toEmbedding_trans_toEmbedding {α β : Sort _} (e : α ≃ β) :
    e.symm.toEmbedding.trans e.toEmbedding = Embedding.refl _ := by
  ext
  simp
#align
  function.embedding.equiv_symm_to_embedding_trans_to_embedding Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

#print Function.Embedding.congr /-
/-- Transfer an embedding along a pair of equivalences. -/
@[simps (config := { fullyApplied := false })]
protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
    (f : α ↪ γ) : β ↪ δ :=
  (Equiv.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)
#align function.embedding.congr Function.Embedding.congr
-/

#print Function.Embedding.ofSurjective /-
/-- A right inverse `surj_inv` of a surjective function as an `embedding`. -/
protected noncomputable def ofSurjective {α β} (f : β → α) (hf : Surjective f) : α ↪ β :=
  ⟨surjInv hf, injective_surjInv _⟩
#align function.embedding.of_surjective Function.Embedding.ofSurjective
-/

#print Function.Embedding.equivOfSurjective /-
/-- Convert a surjective `embedding` to an `equiv` -/
protected noncomputable def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f) : α ≃ β :=
  Equiv.ofBijective f ⟨f.Injective, hf⟩
#align function.embedding.equiv_of_surjective Function.Embedding.equivOfSurjective
-/

#print Function.Embedding.ofIsEmpty /-
/-- There is always an embedding from an empty type. -/
protected def ofIsEmpty {α β} [IsEmpty α] : α ↪ β :=
  ⟨isEmptyElim, isEmptyElim⟩
#align function.embedding.of_is_empty Function.Embedding.ofIsEmpty
-/

#print Function.Embedding.setValue /-
/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
def setValue {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y h
    dsimp at h
    split_ifs  at h <;> try subst b <;> try simp only [f.injective.eq_iff] at * <;> cc⟩
#align function.embedding.set_value Function.Embedding.setValue
-/

/- warning: function.embedding.set_value_eq -> Function.Embedding.setValue_eq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : Function.Embedding.{u_1, u_2} α β) (a : α) (b : β) [_inst_1 : forall (a' : α), Decidable (Eq.{u_1} α a' a)] [_inst_2 : forall (a' : α), Decidable (Eq.{u_2} β (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) f a') b)], Eq.{u_2} β (coeFn.{max 1 (imax u_1 u_2), imax u_1 u_2} (Function.Embedding.{u_1, u_2} α β) (fun (_x : Function.Embedding.{u_1, u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{u_1, u_2} α β) (Function.Embedding.setValue.{u_1, u_2} α β f a b (fun (a' : α) => _inst_1 a') (fun (a' : α) => _inst_2 a')) a) b
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : Function.Embedding.{u_1, u_2} α β) (a : α) (b : β) [inst._@.Mathlib.Logic.Embedding.Basic._hyg.1591 : forall (a' : α), Decidable (Eq.{u_1} α a' a)] [inst._@.Mathlib.Logic.Embedding.Basic._hyg.1603 : forall (a' : α), Decidable (Eq.{u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a') (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) f a') b)], Eq.{u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (FunLike.coe.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u_2) u_1, u_1, u_2} (Function.Embedding.{u_1, u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{u_1, u_2} α β)) (Function.Embedding.setValue.{u_1, u_2} α β f a b (fun (a' : α) => inst._@.Mathlib.Logic.Embedding.Basic._hyg.1591 a') (fun (a' : α) => inst._@.Mathlib.Logic.Embedding.Basic._hyg.1603 a')) a) b
Case conversion may be inaccurate. Consider using '#align function.embedding.set_value_eq Function.Embedding.setValue_eqₓ'. -/
theorem setValue_eq {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : setValue f a b a = b := by simp [set_value]
#align function.embedding.set_value_eq Function.Embedding.setValue_eq

#print Function.Embedding.some /-
/-- Embedding into `option α` using `some`. -/
@[simps (config := { fullyApplied := false })]
protected def some {α} : α ↪ Option α :=
  ⟨some, Option.some_injective α⟩
#align function.embedding.some Function.Embedding.some
-/

/- warning: function.embedding.coe_option clashes with function.embedding.some -> Function.Embedding.some
Case conversion may be inaccurate. Consider using '#align function.embedding.coe_option Function.Embedding.someₓ'. -/
#print Function.Embedding.some /-
/-- Embedding into `option α` using `coe`. Usually the correct synctatical form for `simp`. -/
@[simps (config := { fullyApplied := false })]
def some {α} : α ↪ Option α :=
  ⟨coe, Option.some_injective α⟩
#align function.embedding.coe_option Function.Embedding.some
-/

#print Function.Embedding.optionMap /-
/-- A version of `option.map` for `function.embedding`s. -/
@[simps (config := { fullyApplied := false })]
def optionMap {α β} (f : α ↪ β) : Option α ↪ Option β :=
  ⟨Option.map f, Option.map_injective f.Injective⟩
#align function.embedding.option_map Function.Embedding.optionMap
-/

#print Function.Embedding.subtype /-
/-- Embedding of a `subtype`. -/
def subtype {α} (p : α → Prop) : Subtype p ↪ α :=
  ⟨coe, fun _ _ => Subtype.ext_val⟩
#align function.embedding.subtype Function.Embedding.subtype
-/

#print Function.Embedding.coe_subtype /-
@[simp]
theorem coe_subtype {α} (p : α → Prop) : ⇑(subtype p) = coe :=
  rfl
#align function.embedding.coe_subtype Function.Embedding.coe_subtype
-/

#print Function.Embedding.quotientOut /-
/-- `quotient.out` as an embedding. -/
noncomputable def quotientOut (α) [s : Setoid α] : Quotient s ↪ α :=
  ⟨_, Quotient.out_injective⟩
#align function.embedding.quotient_out Function.Embedding.quotientOut
-/

#print Function.Embedding.coe_quotientOut /-
@[simp]
theorem coe_quotientOut (α) [s : Setoid α] : ⇑(quotientOut α) = Quotient.out :=
  rfl
#align function.embedding.coe_quotient_out Function.Embedding.coe_quotientOut
-/

#print Function.Embedding.punit /-
/-- Choosing an element `b : β` gives an embedding of `punit` into `β`. -/
def punit {β : Sort _} (b : β) : PUnit ↪ β :=
  ⟨fun _ => b, by 
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩
#align function.embedding.punit Function.Embedding.punit
-/

#print Function.Embedding.sectl /-
/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
@[simps]
def sectl (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β :=
  ⟨fun a => (a, b), fun a a' h => congr_arg Prod.fst h⟩
#align function.embedding.sectl Function.Embedding.sectl
-/

#print Function.Embedding.sectr /-
/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
@[simps]
def sectr {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β :=
  ⟨fun b => (a, b), fun b b' h => congr_arg Prod.snd h⟩
#align function.embedding.sectr Function.Embedding.sectr
-/

#print Function.Embedding.prodMap /-
/-- If `e₁` and `e₂` are embeddings, then so is `prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
def prodMap {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  ⟨Prod.map e₁ e₂, e₁.Injective.prod_map e₂.Injective⟩
#align function.embedding.prod_map Function.Embedding.prodMap
-/

/- warning: function.embedding.coe_prod_map -> Function.Embedding.coe_prodMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (e₁ : Function.Embedding.{succ u_1, succ u_2} α β) (e₂ : Function.Embedding.{succ u_3, succ u_4} γ δ), Eq.{max (max (succ u_1) (succ u_3)) (succ u_2) (succ u_4)} ((Prod.{u_1, u_3} α γ) -> (Prod.{u_2, u_4} β δ)) (coeFn.{max 1 (max (succ u_1) (succ u_3)) (succ u_2) (succ u_4), max (max (succ u_1) (succ u_3)) (succ u_2) (succ u_4)} (Function.Embedding.{max (succ u_1) (succ u_3), max (succ u_2) (succ u_4)} (Prod.{u_1, u_3} α γ) (Prod.{u_2, u_4} β δ)) (fun (_x : Function.Embedding.{max (succ u_1) (succ u_3), max (succ u_2) (succ u_4)} (Prod.{u_1, u_3} α γ) (Prod.{u_2, u_4} β δ)) => (Prod.{u_1, u_3} α γ) -> (Prod.{u_2, u_4} β δ)) (Function.Embedding.hasCoeToFun.{max (succ u_1) (succ u_3), max (succ u_2) (succ u_4)} (Prod.{u_1, u_3} α γ) (Prod.{u_2, u_4} β δ)) (Function.Embedding.prodMap.{u_1, u_2, u_3, u_4} α β γ δ e₁ e₂)) (Prod.map.{u_1, u_2, u_3, u_4} α β γ δ (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) e₁) (coeFn.{max 1 (succ u_3) (succ u_4), max (succ u_3) (succ u_4)} (Function.Embedding.{succ u_3, succ u_4} γ δ) (fun (_x : Function.Embedding.{succ u_3, succ u_4} γ δ) => γ -> δ) (Function.Embedding.hasCoeToFun.{succ u_3, succ u_4} γ δ) e₂))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (e₁ : Function.Embedding.{succ u_1, succ u_2} α β) (e₂ : Function.Embedding.{succ u_3, succ u_4} γ δ), Eq.{max (max (max (succ u_1) (succ u_2)) (succ u_3)) (succ u_4)} (forall (a : Prod.{u_1, u_3} α γ), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Prod.{u_1, u_3} α γ) => Prod.{u_2, u_4} β δ) a) (FunLike.coe.{max (max (max (succ u_1) (succ u_2)) (succ u_3)) (succ u_4), max (succ u_1) (succ u_3), max (succ u_2) (succ u_4)} (Function.Embedding.{max (succ u_3) (succ u_1), max (succ u_4) (succ u_2)} (Prod.{u_1, u_3} α γ) (Prod.{u_2, u_4} β δ)) (Prod.{u_1, u_3} α γ) (fun (a : Prod.{u_1, u_3} α γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Prod.{u_1, u_3} α γ) => Prod.{u_2, u_4} β δ) a) (EmbeddingLike.toFunLike.{max (max (max (succ u_1) (succ u_2)) (succ u_3)) (succ u_4), max (succ u_1) (succ u_3), max (succ u_2) (succ u_4)} (Function.Embedding.{max (succ u_3) (succ u_1), max (succ u_4) (succ u_2)} (Prod.{u_1, u_3} α γ) (Prod.{u_2, u_4} β δ)) (Prod.{u_1, u_3} α γ) (Prod.{u_2, u_4} β δ) (Function.instEmbeddingLikeEmbedding.{max (succ u_1) (succ u_3), max (succ u_2) (succ u_4)} (Prod.{u_1, u_3} α γ) (Prod.{u_2, u_4} β δ))) (Function.Embedding.prodMap.{u_1, u_2, u_3, u_4} α β γ δ e₁ e₂)) (Prod.map.{u_1, u_2, u_3, u_4} α β γ δ (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) e₁) (FunLike.coe.{max (succ u_3) (succ u_4), succ u_3, succ u_4} (Function.Embedding.{succ u_3, succ u_4} γ δ) γ (fun (a : γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : γ) => δ) a) (EmbeddingLike.toFunLike.{max (succ u_3) (succ u_4), succ u_3, succ u_4} (Function.Embedding.{succ u_3, succ u_4} γ δ) γ δ (Function.instEmbeddingLikeEmbedding.{succ u_3, succ u_4} γ δ)) e₂))
Case conversion may be inaccurate. Consider using '#align function.embedding.coe_prod_map Function.Embedding.coe_prodMapₓ'. -/
@[simp]
theorem coe_prodMap {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
    ⇑(e₁.prod_map e₂) = Prod.map e₁ e₂ :=
  rfl
#align function.embedding.coe_prod_map Function.Embedding.coe_prodMap

#print Function.Embedding.pprodMap /-
/-- If `e₁` and `e₂` are embeddings, then so is `λ ⟨a, b⟩, ⟨e₁ a, e₂ b⟩ : pprod α γ → pprod β δ`. -/
def pprodMap {α β γ δ : Sort _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β δ :=
  ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.Injective.pprod_map e₂.Injective⟩
#align function.embedding.pprod_map Function.Embedding.pprodMap
-/

section Sum

open Sum

#print Function.Embedding.sumMap /-
/-- If `e₁` and `e₂` are embeddings, then so is `sum.map e₁ e₂`. -/
def sumMap {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : Sum α γ ↪ Sum β δ :=
  ⟨Sum.map e₁ e₂, fun s₁ s₂ h =>
    match s₁, s₂, h with
    | inl a₁, inl a₂, h => congr_arg inl <| e₁.Injective <| inl.inj h
    | inr b₁, inr b₂, h => congr_arg inr <| e₂.Injective <| inr.inj h⟩
#align function.embedding.sum_map Function.Embedding.sumMap
-/

/- warning: function.embedding.coe_sum_map -> Function.Embedding.coe_sumMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (e₁ : Function.Embedding.{succ u_1, succ u_2} α β) (e₂ : Function.Embedding.{succ u_3, succ u_4} γ δ), Eq.{max (max (succ u_1) (succ u_3)) (succ u_2) (succ u_4)} ((Sum.{u_1, u_3} α γ) -> (Sum.{u_2, u_4} β δ)) (coeFn.{max 1 (max (succ u_1) (succ u_3)) (succ u_2) (succ u_4), max (max (succ u_1) (succ u_3)) (succ u_2) (succ u_4)} (Function.Embedding.{max (succ u_1) (succ u_3), max (succ u_2) (succ u_4)} (Sum.{u_1, u_3} α γ) (Sum.{u_2, u_4} β δ)) (fun (_x : Function.Embedding.{max (succ u_1) (succ u_3), max (succ u_2) (succ u_4)} (Sum.{u_1, u_3} α γ) (Sum.{u_2, u_4} β δ)) => (Sum.{u_1, u_3} α γ) -> (Sum.{u_2, u_4} β δ)) (Function.Embedding.hasCoeToFun.{max (succ u_1) (succ u_3), max (succ u_2) (succ u_4)} (Sum.{u_1, u_3} α γ) (Sum.{u_2, u_4} β δ)) (Function.Embedding.sumMap.{u_1, u_2, u_3, u_4} α β γ δ e₁ e₂)) (Sum.map.{u_1, u_3, u_2, u_4} α β γ δ (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) e₁) (coeFn.{max 1 (succ u_3) (succ u_4), max (succ u_3) (succ u_4)} (Function.Embedding.{succ u_3, succ u_4} γ δ) (fun (_x : Function.Embedding.{succ u_3, succ u_4} γ δ) => γ -> δ) (Function.Embedding.hasCoeToFun.{succ u_3, succ u_4} γ δ) e₂))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (e₁ : Function.Embedding.{succ u_1, succ u_2} α β) (e₂ : Function.Embedding.{succ u_3, succ u_4} γ δ), Eq.{max (max (max (succ u_4) (succ u_3)) (succ u_2)) (succ u_1)} (forall (a : Sum.{u_1, u_3} α γ), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Sum.{u_1, u_3} α γ) => Sum.{u_2, u_4} β δ) a) (FunLike.coe.{max (max (max (succ u_4) (succ u_3)) (succ u_2)) (succ u_1), max (succ u_3) (succ u_1), max (succ u_4) (succ u_2)} (Function.Embedding.{max (succ u_3) (succ u_1), max (succ u_4) (succ u_2)} (Sum.{u_1, u_3} α γ) (Sum.{u_2, u_4} β δ)) (Sum.{u_1, u_3} α γ) (fun (a : Sum.{u_1, u_3} α γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Sum.{u_1, u_3} α γ) => Sum.{u_2, u_4} β δ) a) (EmbeddingLike.toFunLike.{max (max (max (succ u_4) (succ u_3)) (succ u_2)) (succ u_1), max (succ u_3) (succ u_1), max (succ u_4) (succ u_2)} (Function.Embedding.{max (succ u_3) (succ u_1), max (succ u_4) (succ u_2)} (Sum.{u_1, u_3} α γ) (Sum.{u_2, u_4} β δ)) (Sum.{u_1, u_3} α γ) (Sum.{u_2, u_4} β δ) (Function.instEmbeddingLikeEmbedding.{max (succ u_3) (succ u_1), max (succ u_4) (succ u_2)} (Sum.{u_1, u_3} α γ) (Sum.{u_2, u_4} β δ))) (Function.Embedding.sumMap.{u_1, u_2, u_3, u_4} α β γ δ e₁ e₂)) (Sum.map.{u_1, u_3, u_2, u_4} α β γ δ (FunLike.coe.{max (succ u_2) (succ u_1), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_2) (succ u_1), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) e₁) (FunLike.coe.{max (succ u_4) (succ u_3), succ u_3, succ u_4} (Function.Embedding.{succ u_3, succ u_4} γ δ) γ (fun (a : γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : γ) => δ) a) (EmbeddingLike.toFunLike.{max (succ u_4) (succ u_3), succ u_3, succ u_4} (Function.Embedding.{succ u_3, succ u_4} γ δ) γ δ (Function.instEmbeddingLikeEmbedding.{succ u_3, succ u_4} γ δ)) e₂))
Case conversion may be inaccurate. Consider using '#align function.embedding.coe_sum_map Function.Embedding.coe_sumMapₓ'. -/
@[simp]
theorem coe_sumMap {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : ⇑(sumMap e₁ e₂) = Sum.map e₁ e₂ :=
  rfl
#align function.embedding.coe_sum_map Function.Embedding.coe_sumMap

#print Function.Embedding.inl /-
/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps]
def inl {α β : Type _} : α ↪ Sum α β :=
  ⟨Sum.inl, fun a b => Sum.inl.inj⟩
#align function.embedding.inl Function.Embedding.inl
-/

#print Function.Embedding.inr /-
/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps]
def inr {α β : Type _} : β ↪ Sum α β :=
  ⟨Sum.inr, fun a b => Sum.inr.inj⟩
#align function.embedding.inr Function.Embedding.inr
-/

end Sum

section Sigma

variable {α α' : Type _} {β : α → Type _} {β' : α' → Type _}

#print Function.Embedding.sigmaMk /-
/-- `sigma.mk` as an `function.embedding`. -/
@[simps apply]
def sigmaMk (a : α) : β a ↪ Σx, β x :=
  ⟨Sigma.mk a, sigma_mk_injective⟩
#align function.embedding.sigma_mk Function.Embedding.sigmaMk
-/

#print Function.Embedding.sigmaMap /-
/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `sigma.map f g` is an embedding. -/
@[simps apply]
def sigmaMap (f : α ↪ α') (g : ∀ a, β a ↪ β' (f a)) : (Σa, β a) ↪ Σa', β' a' :=
  ⟨Sigma.map f fun a => g a, f.Injective.sigma_map fun a => (g a).Injective⟩
#align function.embedding.sigma_map Function.Embedding.sigmaMap
-/

end Sigma

#print Function.Embedding.piCongrRight /-
/-- Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embeddings
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `λ a, e a (f a)`. -/
@[simps]
def piCongrRight {α : Sort _} {β γ : α → Sort _} (e : ∀ a, β a ↪ γ a) : (∀ a, β a) ↪ ∀ a, γ a :=
  ⟨fun f a => e a (f a), fun f₁ f₂ h => funext fun a => (e a).Injective (congr_fun h a)⟩
#align function.embedding.Pi_congr_right Function.Embedding.piCongrRight
-/

#print Function.Embedding.arrowCongrRight /-
/-- An embedding `e : α ↪ β` defines an embedding `(γ → α) ↪ (γ → β)` that sends each `f`
to `e ∘ f`. -/
def arrowCongrRight {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ → α) ↪ γ → β :=
  piCongrRight fun _ => e
#align function.embedding.arrow_congr_right Function.Embedding.arrowCongrRight
-/

#print Function.Embedding.arrowCongrRight_apply /-
@[simp]
theorem arrowCongrRight_apply {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ ↪ α) :
    arrowCongrRight e f = e ∘ f :=
  rfl
#align function.embedding.arrow_congr_right_apply Function.Embedding.arrowCongrRight_apply
-/

#print Function.Embedding.arrowCongrLeft /-
/-- An embedding `e : α ↪ β` defines an embedding `(α → γ) ↪ (β → γ)` for any inhabited type `γ`.
This embedding sends each `f : α → γ` to a function `g : β → γ` such that `g ∘ e = f` and
`g y = default` whenever `y ∉ range e`. -/
noncomputable def arrowCongrLeft {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) :
    (α → γ) ↪ β → γ :=
  ⟨fun f => extend e f default, fun f₁ f₂ h =>
    funext fun x => by simpa only [e.injective.extend_apply] using congr_fun h (e x)⟩
#align function.embedding.arrow_congr_left Function.Embedding.arrowCongrLeft
-/

#print Function.Embedding.subtypeMap /-
/-- Restrict both domain and codomain of an embedding. -/
protected def subtypeMap {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β)
    (h : ∀ ⦃x⦄, p x → q (f x)) : { x : α // p x } ↪ { y : β // q y } :=
  ⟨Subtype.map f h, Subtype.map_injective h f.2⟩
#align function.embedding.subtype_map Function.Embedding.subtypeMap
-/

open Set

/- warning: function.embedding.swap_apply -> Function.Embedding.swap_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : DecidableEq.{succ u_1} α] [_inst_2 : DecidableEq.{succ u_2} β] (f : Function.Embedding.{succ u_1, succ u_2} α β) (x : α) (y : α) (z : α), Eq.{succ u_2} β (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.Perm.{succ u_2} β) (fun (_x : Equiv.{succ u_2, succ u_2} β β) => β -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β β) (Equiv.swap.{succ u_2} β (fun (a : β) (b : β) => _inst_2 a b) (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f x) (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f y)) (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f z)) (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.Perm.{succ u_1} α) (fun (_x : Equiv.{succ u_1, succ u_1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α α) (Equiv.swap.{succ u_1} α (fun (a : α) (b : α) => _inst_1 a b) x y) z))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Logic.Embedding.Basic._hyg.2639 : DecidableEq.{succ u_1} α] [inst._@.Mathlib.Logic.Embedding.Basic._hyg.2642 : DecidableEq.{succ u_2} β] (f : Function.Embedding.{succ u_1, succ u_2} α β) (x : α) (y : α) (z : α), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f z)) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.Perm.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x)) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.Perm.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x)) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.Perm.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x)) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x)))) (Equiv.swap.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (fun (a : β) (b : β) => inst._@.Mathlib.Logic.Embedding.Basic._hyg.2642 a b) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f x) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f y)) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f z)) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.Perm.{succ u_1} α) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.Perm.{succ u_1} α) α α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.Perm.{succ u_1} α) α α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α α))) (Equiv.swap.{succ u_1} α (fun (a : α) (b : α) => inst._@.Mathlib.Logic.Embedding.Basic._hyg.2639 a b) x y) z))
Case conversion may be inaccurate. Consider using '#align function.embedding.swap_apply Function.Embedding.swap_applyₓ'. -/
theorem swap_apply {α β : Type _} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  f.Injective.swap_apply x y z
#align function.embedding.swap_apply Function.Embedding.swap_apply

/- warning: function.embedding.swap_comp -> Function.Embedding.swap_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : DecidableEq.{succ u_1} α] [_inst_2 : DecidableEq.{succ u_2} β] (f : Function.Embedding.{succ u_1, succ u_2} α β) (x : α) (y : α), Eq.{max (succ u_1) (succ u_2)} (α -> β) (Function.comp.{succ u_1, succ u_2, succ u_2} α β β (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.Perm.{succ u_2} β) (fun (_x : Equiv.{succ u_2, succ u_2} β β) => β -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β β) (Equiv.swap.{succ u_2} β (fun (a : β) (b : β) => _inst_2 a b) (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f x) (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f y))) (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f)) (Function.comp.{succ u_1, succ u_1, succ u_2} α α β (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Function.Embedding.{succ u_1, succ u_2} α β) (fun (_x : Function.Embedding.{succ u_1, succ u_2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u_1, succ u_2} α β) f) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.Perm.{succ u_1} α) (fun (_x : Equiv.{succ u_1, succ u_1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α α) (Equiv.swap.{succ u_1} α (fun (a : α) (b : α) => _inst_1 a b) x y)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Logic.Embedding.Basic._hyg.2684 : DecidableEq.{succ u_1} α] [inst._@.Mathlib.Logic.Embedding.Basic._hyg.2687 : DecidableEq.{succ u_2} β] (f : Function.Embedding.{succ u_1, succ u_2} α β) (x : α) (y : α), Eq.{max (succ u_1) (succ u_2)} (α -> β) (Function.comp.{succ u_1, succ u_2, succ u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) β (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.Perm.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x)) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.Perm.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x)) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.Perm.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x)) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x)))) (Equiv.swap.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (fun (a : β) (b : β) => inst._@.Mathlib.Logic.Embedding.Basic._hyg.2687 a b) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f x) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f y))) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f)) (Function.comp.{succ u_1, succ u_1, succ u_2} α α β (FunLike.coe.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_1, succ u_2} (Function.Embedding.{succ u_1, succ u_2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u_1, succ u_2} α β)) f) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.Perm.{succ u_1} α) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.Perm.{succ u_1} α) α α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.Perm.{succ u_1} α) α α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α α))) (Equiv.swap.{succ u_1} α (fun (a : α) (b : α) => inst._@.Mathlib.Logic.Embedding.Basic._hyg.2684 a b) x y)))
Case conversion may be inaccurate. Consider using '#align function.embedding.swap_comp Function.Embedding.swap_compₓ'. -/
theorem swap_comp {α β : Type _} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  f.Injective.swap_comp x y
#align function.embedding.swap_comp Function.Embedding.swap_comp

end Embedding

end Function

namespace Equiv

open Function.Embedding

/- warning: equiv.subtype_injective_equiv_embedding -> Equiv.subtypeInjectiveEquivEmbedding is a dubious translation:
lean 3 declaration is
  forall (α : Sort.{u_1}) (β : Sort.{u_2}), Equiv.{max 1 (imax u_1 u_2), max 1 (imax u_1 u_2)} (Subtype.{imax u_1 u_2} (α -> β) (fun (f : α -> β) => Function.Injective.{u_1, u_2} α β f)) (Function.Embedding.{u_1, u_2} α β)
but is expected to have type
  forall (α : Sort.{u_1}) (β : Sort.{u_2}), Equiv.{max 1 (imax u_1 u_2), max (max 1 u_2) u_1} (Subtype.{imax u_1 u_2} (α -> β) (fun (f : α -> β) => Function.Injective.{u_1, u_2} α β f)) (Function.Embedding.{u_1, u_2} α β)
Case conversion may be inaccurate. Consider using '#align equiv.subtype_injective_equiv_embedding Equiv.subtypeInjectiveEquivEmbeddingₓ'. -/
/-- The type of embeddings `α ↪ β` is equivalent to
    the subtype of all injective functions `α → β`. -/
def subtypeInjectiveEquivEmbedding (α β : Sort _) :
    { f : α → β // Function.Injective f } ≃
      (α ↪ β) where 
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f, f.Injective⟩
  left_inv f := by simp
  right_inv f := by 
    ext
    rfl
#align equiv.subtype_injective_equiv_embedding Equiv.subtypeInjectiveEquivEmbedding

/- warning: equiv.embedding_congr -> Equiv.embeddingCongr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} {δ : Sort.{u_4}}, (Equiv.{u_1, u_2} α β) -> (Equiv.{u_3, u_4} γ δ) -> (Equiv.{max 1 (imax u_1 u_3), max 1 (imax u_2 u_4)} (Function.Embedding.{u_1, u_3} α γ) (Function.Embedding.{u_2, u_4} β δ))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} {δ : Sort.{u_4}}, (Equiv.{u_1, u_2} α β) -> (Equiv.{u_3, u_4} γ δ) -> (Equiv.{max (max 1 u_3) u_1, max (max 1 u_4) u_2} (Function.Embedding.{u_1, u_3} α γ) (Function.Embedding.{u_2, u_4} β δ))
Case conversion may be inaccurate. Consider using '#align equiv.embedding_congr Equiv.embeddingCongrₓ'. -/
/-- If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`. -/
@[congr, simps apply]
def embeddingCongr {α β γ δ : Sort _} (h : α ≃ β) (h' : γ ≃ δ) :
    (α ↪ γ) ≃ (β ↪ δ) where 
  toFun f := f.congr h h'
  invFun f := f.congr h.symm h'.symm
  left_inv x := by 
    ext
    simp
  right_inv x := by 
    ext
    simp
#align equiv.embedding_congr Equiv.embeddingCongr

/- warning: equiv.embedding_congr_refl -> Equiv.embeddingCongr_refl is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Eq.{max 1 (imax u_1 u_2)} (Equiv.{max 1 (imax u_1 u_2), max 1 (imax u_1 u_2)} (Function.Embedding.{u_1, u_2} α β) (Function.Embedding.{u_1, u_2} α β)) (Equiv.embeddingCongr.{u_1, u_1, u_2, u_2} α α β β (Equiv.refl.{u_1} α) (Equiv.refl.{u_2} β)) (Equiv.refl.{max 1 (imax u_1 u_2)} (Function.Embedding.{u_1, u_2} α β))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Eq.{max (max 1 u_1) u_2} (Equiv.{max (max 1 u_2) u_1, max (max 1 u_2) u_1} (Function.Embedding.{u_1, u_2} α β) (Function.Embedding.{u_1, u_2} α β)) (Equiv.embeddingCongr.{u_1, u_1, u_2, u_2} α α β β (Equiv.refl.{u_1} α) (Equiv.refl.{u_2} β)) (Equiv.refl.{max (max 1 u_2) u_1} (Function.Embedding.{u_1, u_2} α β))
Case conversion may be inaccurate. Consider using '#align equiv.embedding_congr_refl Equiv.embeddingCongr_reflₓ'. -/
@[simp]
theorem embeddingCongr_refl {α β : Sort _} :
    embeddingCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α ↪ β) := by
  ext
  rfl
#align equiv.embedding_congr_refl Equiv.embeddingCongr_refl

/- warning: equiv.embedding_congr_trans -> Equiv.embeddingCongr_trans is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u_1}} {β₁ : Sort.{u_2}} {α₂ : Sort.{u_3}} {β₂ : Sort.{u_4}} {α₃ : Sort.{u_5}} {β₃ : Sort.{u_6}} (e₁ : Equiv.{u_1, u_3} α₁ α₂) (e₁' : Equiv.{u_2, u_4} β₁ β₂) (e₂ : Equiv.{u_3, u_5} α₂ α₃) (e₂' : Equiv.{u_4, u_6} β₂ β₃), Eq.{max 1 (max (max 1 (imax u_1 u_2)) 1 (imax u_5 u_6)) (max 1 (imax u_5 u_6)) 1 (imax u_1 u_2)} (Equiv.{max 1 (imax u_1 u_2), max 1 (imax u_5 u_6)} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_5, u_6} α₃ β₃)) (Equiv.embeddingCongr.{u_1, u_5, u_2, u_6} α₁ α₃ β₁ β₃ (Equiv.trans.{u_1, u_3, u_5} α₁ α₂ α₃ e₁ e₂) (Equiv.trans.{u_2, u_4, u_6} β₁ β₂ β₃ e₁' e₂')) (Equiv.trans.{max 1 (imax u_1 u_2), max 1 (imax u_3 u_4), max 1 (imax u_5 u_6)} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_3, u_4} α₂ β₂) (Function.Embedding.{u_5, u_6} α₃ β₃) (Equiv.embeddingCongr.{u_1, u_3, u_2, u_4} α₁ α₂ β₁ β₂ e₁ e₁') (Equiv.embeddingCongr.{u_3, u_5, u_4, u_6} α₂ α₃ β₂ β₃ e₂ e₂'))
but is expected to have type
  forall {α₁ : Sort.{u_1}} {β₁ : Sort.{u_2}} {α₂ : Sort.{u_3}} {β₂ : Sort.{u_4}} {α₃ : Sort.{u_5}} {β₃ : Sort.{u_6}} (e₁ : Equiv.{u_1, u_3} α₁ α₂) (e₁' : Equiv.{u_2, u_4} β₁ β₂) (e₂ : Equiv.{u_3, u_5} α₂ α₃) (e₂' : Equiv.{u_4, u_6} β₂ β₃), Eq.{max (max (max (max 1 u_1) u_2) u_5) u_6} (Equiv.{max (max 1 u_2) u_1, max (max 1 u_6) u_5} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_5, u_6} α₃ β₃)) (Equiv.embeddingCongr.{u_1, u_5, u_2, u_6} α₁ α₃ β₁ β₃ (Equiv.trans.{u_1, u_3, u_5} α₁ α₂ α₃ e₁ e₂) (Equiv.trans.{u_2, u_4, u_6} β₁ β₂ β₃ e₁' e₂')) (Equiv.trans.{max (max 1 u_1) u_2, max (max 1 u_3) u_4, max (max 1 u_6) u_5} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_3, u_4} α₂ β₂) (Function.Embedding.{u_5, u_6} α₃ β₃) (Equiv.embeddingCongr.{u_1, u_3, u_2, u_4} α₁ α₂ β₁ β₂ e₁ e₁') (Equiv.embeddingCongr.{u_3, u_5, u_4, u_6} α₂ α₃ β₂ β₃ e₂ e₂'))
Case conversion may be inaccurate. Consider using '#align equiv.embedding_congr_trans Equiv.embeddingCongr_transₓ'. -/
@[simp]
theorem embeddingCongr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂)
    (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    embeddingCongr (e₁.trans e₂) (e₁'.trans e₂') =
      (embeddingCongr e₁ e₁').trans (embeddingCongr e₂ e₂') :=
  rfl
#align equiv.embedding_congr_trans Equiv.embeddingCongr_trans

/- warning: equiv.embedding_congr_symm -> Equiv.embeddingCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u_1}} {β₁ : Sort.{u_2}} {α₂ : Sort.{u_3}} {β₂ : Sort.{u_4}} (e₁ : Equiv.{u_1, u_3} α₁ α₂) (e₂ : Equiv.{u_2, u_4} β₁ β₂), Eq.{max 1 (max (max 1 (imax u_3 u_4)) 1 (imax u_1 u_2)) (max 1 (imax u_1 u_2)) 1 (imax u_3 u_4)} (Equiv.{max 1 (imax u_3 u_4), max 1 (imax u_1 u_2)} (Function.Embedding.{u_3, u_4} α₂ β₂) (Function.Embedding.{u_1, u_2} α₁ β₁)) (Equiv.symm.{max 1 (imax u_1 u_2), max 1 (imax u_3 u_4)} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_3, u_4} α₂ β₂) (Equiv.embeddingCongr.{u_1, u_3, u_2, u_4} α₁ α₂ β₁ β₂ e₁ e₂)) (Equiv.embeddingCongr.{u_3, u_1, u_4, u_2} α₂ α₁ β₂ β₁ (Equiv.symm.{u_1, u_3} α₁ α₂ e₁) (Equiv.symm.{u_2, u_4} β₁ β₂ e₂))
but is expected to have type
  forall {α₁ : Sort.{u_1}} {β₁ : Sort.{u_2}} {α₂ : Sort.{u_3}} {β₂ : Sort.{u_4}} (e₁ : Equiv.{u_1, u_3} α₁ α₂) (e₂ : Equiv.{u_2, u_4} β₁ β₂), Eq.{max (max (max (max 1 u_1) u_2) u_3) u_4} (Equiv.{max (max 1 u_3) u_4, max (max 1 u_1) u_2} (Function.Embedding.{u_3, u_4} α₂ β₂) (Function.Embedding.{u_1, u_2} α₁ β₁)) (Equiv.symm.{max (max 1 u_1) u_2, max (max 1 u_3) u_4} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_3, u_4} α₂ β₂) (Equiv.embeddingCongr.{u_1, u_3, u_2, u_4} α₁ α₂ β₁ β₂ e₁ e₂)) (Equiv.embeddingCongr.{u_3, u_1, u_4, u_2} α₂ α₁ β₂ β₁ (Equiv.symm.{u_1, u_3} α₁ α₂ e₁) (Equiv.symm.{u_2, u_4} β₁ β₂ e₂))
Case conversion may be inaccurate. Consider using '#align equiv.embedding_congr_symm Equiv.embeddingCongr_symmₓ'. -/
@[simp]
theorem embeddingCongr_symm {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (embeddingCongr e₁ e₂).symm = embeddingCongr e₁.symm e₂.symm :=
  rfl
#align equiv.embedding_congr_symm Equiv.embeddingCongr_symm

/- warning: equiv.embedding_congr_apply_trans -> Equiv.embeddingCongr_apply_trans is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u_1}} {β₁ : Sort.{u_2}} {γ₁ : Sort.{u_3}} {α₂ : Sort.{u_4}} {β₂ : Sort.{u_5}} {γ₂ : Sort.{u_6}} (ea : Equiv.{u_1, u_4} α₁ α₂) (eb : Equiv.{u_2, u_5} β₁ β₂) (ec : Equiv.{u_3, u_6} γ₁ γ₂) (f : Function.Embedding.{u_1, u_2} α₁ β₁) (g : Function.Embedding.{u_2, u_3} β₁ γ₁), Eq.{max 1 (imax u_4 u_6)} (Function.Embedding.{u_4, u_6} α₂ γ₂) (coeFn.{max 1 (max (max 1 (imax u_1 u_3)) 1 (imax u_4 u_6)) (max 1 (imax u_4 u_6)) 1 (imax u_1 u_3), max (max 1 (imax u_1 u_3)) 1 (imax u_4 u_6)} (Equiv.{max 1 (imax u_1 u_3), max 1 (imax u_4 u_6)} (Function.Embedding.{u_1, u_3} α₁ γ₁) (Function.Embedding.{u_4, u_6} α₂ γ₂)) (fun (_x : Equiv.{max 1 (imax u_1 u_3), max 1 (imax u_4 u_6)} (Function.Embedding.{u_1, u_3} α₁ γ₁) (Function.Embedding.{u_4, u_6} α₂ γ₂)) => (Function.Embedding.{u_1, u_3} α₁ γ₁) -> (Function.Embedding.{u_4, u_6} α₂ γ₂)) (Equiv.hasCoeToFun.{max 1 (imax u_1 u_3), max 1 (imax u_4 u_6)} (Function.Embedding.{u_1, u_3} α₁ γ₁) (Function.Embedding.{u_4, u_6} α₂ γ₂)) (Equiv.embeddingCongr.{u_1, u_4, u_3, u_6} α₁ α₂ γ₁ γ₂ ea ec) (Function.Embedding.trans.{u_1, u_2, u_3} α₁ β₁ γ₁ f g)) (Function.Embedding.trans.{u_4, u_5, u_6} α₂ β₂ γ₂ (coeFn.{max 1 (max (max 1 (imax u_1 u_2)) 1 (imax u_4 u_5)) (max 1 (imax u_4 u_5)) 1 (imax u_1 u_2), max (max 1 (imax u_1 u_2)) 1 (imax u_4 u_5)} (Equiv.{max 1 (imax u_1 u_2), max 1 (imax u_4 u_5)} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_4, u_5} α₂ β₂)) (fun (_x : Equiv.{max 1 (imax u_1 u_2), max 1 (imax u_4 u_5)} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_4, u_5} α₂ β₂)) => (Function.Embedding.{u_1, u_2} α₁ β₁) -> (Function.Embedding.{u_4, u_5} α₂ β₂)) (Equiv.hasCoeToFun.{max 1 (imax u_1 u_2), max 1 (imax u_4 u_5)} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_4, u_5} α₂ β₂)) (Equiv.embeddingCongr.{u_1, u_4, u_2, u_5} α₁ α₂ β₁ β₂ ea eb) f) (coeFn.{max 1 (max (max 1 (imax u_2 u_3)) 1 (imax u_5 u_6)) (max 1 (imax u_5 u_6)) 1 (imax u_2 u_3), max (max 1 (imax u_2 u_3)) 1 (imax u_5 u_6)} (Equiv.{max 1 (imax u_2 u_3), max 1 (imax u_5 u_6)} (Function.Embedding.{u_2, u_3} β₁ γ₁) (Function.Embedding.{u_5, u_6} β₂ γ₂)) (fun (_x : Equiv.{max 1 (imax u_2 u_3), max 1 (imax u_5 u_6)} (Function.Embedding.{u_2, u_3} β₁ γ₁) (Function.Embedding.{u_5, u_6} β₂ γ₂)) => (Function.Embedding.{u_2, u_3} β₁ γ₁) -> (Function.Embedding.{u_5, u_6} β₂ γ₂)) (Equiv.hasCoeToFun.{max 1 (imax u_2 u_3), max 1 (imax u_5 u_6)} (Function.Embedding.{u_2, u_3} β₁ γ₁) (Function.Embedding.{u_5, u_6} β₂ γ₂)) (Equiv.embeddingCongr.{u_2, u_5, u_3, u_6} β₁ β₂ γ₁ γ₂ eb ec) g))
but is expected to have type
  forall {α₁ : Sort.{u_1}} {β₁ : Sort.{u_2}} {γ₁ : Sort.{u_3}} {α₂ : Sort.{u_4}} {β₂ : Sort.{u_5}} {γ₂ : Sort.{u_6}} (ea : Equiv.{u_1, u_4} α₁ α₂) (eb : Equiv.{u_2, u_5} β₁ β₂) (ec : Equiv.{u_3, u_6} γ₁ γ₂) (f : Function.Embedding.{u_1, u_2} α₁ β₁) (g : Function.Embedding.{u_2, u_3} β₁ γ₁), Eq.{max (max 1 u_4) u_6} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Function.Embedding.{u_1, u_3} α₁ γ₁) => Function.Embedding.{u_4, u_6} α₂ γ₂) (Function.Embedding.trans.{u_1, u_2, u_3} α₁ β₁ γ₁ f g)) (FunLike.coe.{max (max (max (max 1 u_1) u_3) u_4) u_6, max (max 1 u_1) u_3, max (max 1 u_4) u_6} (Equiv.{max (max 1 u_3) u_1, max (max 1 u_6) u_4} (Function.Embedding.{u_1, u_3} α₁ γ₁) (Function.Embedding.{u_4, u_6} α₂ γ₂)) (Function.Embedding.{u_1, u_3} α₁ γ₁) (fun (a : Function.Embedding.{u_1, u_3} α₁ γ₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Function.Embedding.{u_1, u_3} α₁ γ₁) => Function.Embedding.{u_4, u_6} α₂ γ₂) a) (EmbeddingLike.toFunLike.{max (max (max (max 1 u_1) u_3) u_4) u_6, max (max 1 u_1) u_3, max (max 1 u_4) u_6} (Equiv.{max (max 1 u_3) u_1, max (max 1 u_6) u_4} (Function.Embedding.{u_1, u_3} α₁ γ₁) (Function.Embedding.{u_4, u_6} α₂ γ₂)) (Function.Embedding.{u_1, u_3} α₁ γ₁) (Function.Embedding.{u_4, u_6} α₂ γ₂) (EquivLike.toEmbeddingLike.{max (max (max (max 1 u_1) u_3) u_4) u_6, max (max 1 u_1) u_3, max (max 1 u_4) u_6} (Equiv.{max (max 1 u_3) u_1, max (max 1 u_6) u_4} (Function.Embedding.{u_1, u_3} α₁ γ₁) (Function.Embedding.{u_4, u_6} α₂ γ₂)) (Function.Embedding.{u_1, u_3} α₁ γ₁) (Function.Embedding.{u_4, u_6} α₂ γ₂) (Equiv.instEquivLikeEquiv.{max (max 1 u_1) u_3, max (max 1 u_4) u_6} (Function.Embedding.{u_1, u_3} α₁ γ₁) (Function.Embedding.{u_4, u_6} α₂ γ₂)))) (Equiv.embeddingCongr.{u_1, u_4, u_3, u_6} α₁ α₂ γ₁ γ₂ ea ec) (Function.Embedding.trans.{u_1, u_2, u_3} α₁ β₁ γ₁ f g)) (Function.Embedding.trans.{u_4, u_5, u_6} α₂ β₂ γ₂ (FunLike.coe.{max (max (max (max 1 u_1) u_2) u_4) u_5, max (max 1 u_1) u_2, max (max 1 u_4) u_5} (Equiv.{max (max 1 u_2) u_1, max (max 1 u_5) u_4} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_4, u_5} α₂ β₂)) (Function.Embedding.{u_1, u_2} α₁ β₁) (fun (a : Function.Embedding.{u_1, u_2} α₁ β₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Function.Embedding.{u_1, u_2} α₁ β₁) => Function.Embedding.{u_4, u_5} α₂ β₂) a) (EmbeddingLike.toFunLike.{max (max (max (max 1 u_1) u_2) u_4) u_5, max (max 1 u_1) u_2, max (max 1 u_4) u_5} (Equiv.{max (max 1 u_2) u_1, max (max 1 u_5) u_4} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_4, u_5} α₂ β₂)) (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_4, u_5} α₂ β₂) (EquivLike.toEmbeddingLike.{max (max (max (max 1 u_1) u_2) u_4) u_5, max (max 1 u_1) u_2, max (max 1 u_4) u_5} (Equiv.{max (max 1 u_2) u_1, max (max 1 u_5) u_4} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_4, u_5} α₂ β₂)) (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_4, u_5} α₂ β₂) (Equiv.instEquivLikeEquiv.{max (max 1 u_1) u_2, max (max 1 u_4) u_5} (Function.Embedding.{u_1, u_2} α₁ β₁) (Function.Embedding.{u_4, u_5} α₂ β₂)))) (Equiv.embeddingCongr.{u_1, u_4, u_2, u_5} α₁ α₂ β₁ β₂ ea eb) f) (FunLike.coe.{max (max (max (max 1 u_2) u_3) u_5) u_6, max (max 1 u_2) u_3, max (max 1 u_5) u_6} (Equiv.{max (max 1 u_3) u_2, max (max 1 u_6) u_5} (Function.Embedding.{u_2, u_3} β₁ γ₁) (Function.Embedding.{u_5, u_6} β₂ γ₂)) (Function.Embedding.{u_2, u_3} β₁ γ₁) (fun (a : Function.Embedding.{u_2, u_3} β₁ γ₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Function.Embedding.{u_2, u_3} β₁ γ₁) => Function.Embedding.{u_5, u_6} β₂ γ₂) a) (EmbeddingLike.toFunLike.{max (max (max (max 1 u_2) u_3) u_5) u_6, max (max 1 u_2) u_3, max (max 1 u_5) u_6} (Equiv.{max (max 1 u_3) u_2, max (max 1 u_6) u_5} (Function.Embedding.{u_2, u_3} β₁ γ₁) (Function.Embedding.{u_5, u_6} β₂ γ₂)) (Function.Embedding.{u_2, u_3} β₁ γ₁) (Function.Embedding.{u_5, u_6} β₂ γ₂) (EquivLike.toEmbeddingLike.{max (max (max (max 1 u_2) u_3) u_5) u_6, max (max 1 u_2) u_3, max (max 1 u_5) u_6} (Equiv.{max (max 1 u_3) u_2, max (max 1 u_6) u_5} (Function.Embedding.{u_2, u_3} β₁ γ₁) (Function.Embedding.{u_5, u_6} β₂ γ₂)) (Function.Embedding.{u_2, u_3} β₁ γ₁) (Function.Embedding.{u_5, u_6} β₂ γ₂) (Equiv.instEquivLikeEquiv.{max (max 1 u_2) u_3, max (max 1 u_5) u_6} (Function.Embedding.{u_2, u_3} β₁ γ₁) (Function.Embedding.{u_5, u_6} β₂ γ₂)))) (Equiv.embeddingCongr.{u_2, u_5, u_3, u_6} β₁ β₂ γ₁ γ₂ eb ec) g))
Case conversion may be inaccurate. Consider using '#align equiv.embedding_congr_apply_trans Equiv.embeddingCongr_apply_transₓ'. -/
theorem embeddingCongr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
    (ec : γ₁ ≃ γ₂) (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) :
    Equiv.embeddingCongr ea ec (f.trans g) =
      (Equiv.embeddingCongr ea eb f).trans (Equiv.embeddingCongr eb ec g) :=
  by 
  ext
  simp
#align equiv.embedding_congr_apply_trans Equiv.embeddingCongr_apply_trans

#print Equiv.refl_toEmbedding /-
@[simp]
theorem refl_toEmbedding {α : Type _} : (Equiv.refl α).toEmbedding = Function.Embedding.refl α :=
  rfl
#align equiv.refl_to_embedding Equiv.refl_toEmbedding
-/

/- warning: equiv.trans_to_embedding -> Equiv.trans_toEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (e : Equiv.{succ u_1, succ u_2} α β) (f : Equiv.{succ u_2, succ u_3} β γ), Eq.{max 1 (succ u_1) (succ u_3)} (Function.Embedding.{succ u_1, succ u_3} α γ) (Equiv.toEmbedding.{succ u_1, succ u_3} α γ (Equiv.trans.{succ u_1, succ u_2, succ u_3} α β γ e f)) (Function.Embedding.trans.{succ u_1, succ u_2, succ u_3} α β γ (Equiv.toEmbedding.{succ u_1, succ u_2} α β e) (Equiv.toEmbedding.{succ u_2, succ u_3} β γ f))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (e : Equiv.{succ u_1, succ u_2} α β) (f : Equiv.{succ u_2, succ u_3} β γ), Eq.{max (succ u_1) (succ u_3)} (Function.Embedding.{succ u_1, succ u_3} α γ) (Equiv.toEmbedding.{succ u_1, succ u_3} α γ (Equiv.trans.{succ u_1, succ u_2, succ u_3} α β γ e f)) (Function.Embedding.trans.{succ u_1, succ u_2, succ u_3} α β γ (Equiv.toEmbedding.{succ u_1, succ u_2} α β e) (Equiv.toEmbedding.{succ u_2, succ u_3} β γ f))
Case conversion may be inaccurate. Consider using '#align equiv.trans_to_embedding Equiv.trans_toEmbeddingₓ'. -/
@[simp]
theorem trans_toEmbedding {α β γ : Type _} (e : α ≃ β) (f : β ≃ γ) :
    (e.trans f).toEmbedding = e.toEmbedding.trans f.toEmbedding :=
  rfl
#align equiv.trans_to_embedding Equiv.trans_toEmbedding

end Equiv

section Subtype

variable {α : Type _}

#print subtypeOrLeftEmbedding /-
/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` can be injectively split
into a sum of subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right. -/
def subtypeOrLeftEmbedding (p q : α → Prop) [DecidablePred p] :
    { x // p x ∨ q x } ↪ Sum { x // p x } { x // q x } :=
  ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.Prop.resolve_left h⟩, by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩
#align subtype_or_left_embedding subtypeOrLeftEmbedding
-/

#print subtypeOrLeftEmbedding_apply_left /-
theorem subtypeOrLeftEmbedding_apply_left {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : p x) : subtypeOrLeftEmbedding p q x = Sum.inl ⟨x, hx⟩ :=
  dif_pos hx
#align subtype_or_left_embedding_apply_left subtypeOrLeftEmbedding_apply_left
-/

#print subtypeOrLeftEmbedding_apply_right /-
theorem subtypeOrLeftEmbedding_apply_right {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : ¬p x) :
    subtypeOrLeftEmbedding p q x = Sum.inr ⟨x, x.Prop.resolve_left hx⟩ :=
  dif_neg hx
#align subtype_or_left_embedding_apply_right subtypeOrLeftEmbedding_apply_right
-/

#print Subtype.impEmbedding /-
/-- A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`. -/
@[simps]
def Subtype.impEmbedding (p q : α → Prop) (h : ∀ x, p x → q x) : { x // p x } ↪ { x // q x } :=
  ⟨fun x => ⟨x, h x x.Prop⟩, fun x y => by simp [Subtype.ext_iff]⟩
#align subtype.imp_embedding Subtype.impEmbedding
-/

end Subtype

