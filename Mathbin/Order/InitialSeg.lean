/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module order.initial_seg
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.RelIso.Set
import Mathbin.Order.WellFounded

/-!
# Initial and principal segments

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines initial and principal segments.

## Main definitions

* `initial_seg r s`: type of order embeddings of `r` into `s` for which the range is an initial
  segment (i.e., if `b` belongs to the range, then any `b' < b` also belongs to the range).
  It is denoted by `r ≼i s`.
* `principal_seg r s`: Type of order embeddings of `r` into `s` for which the range is a principal
  segment, i.e., an interval of the form `(-∞, top)` for some element `top`. It is denoted by
  `r ≺i s`.

## Notations

These notations belong to the `initial_seg` locale.

* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
-/


/-!
### Initial segments

Order embeddings whose range is an initial segment of `s` (i.e., if `b` belongs to the range, then
any `b' < b` also belongs to the range). The type of these embeddings from `r` to `s` is called
`initial_seg r s`, and denoted by `r ≼i s`.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop}

open Function

#print InitialSeg /-
/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
structure InitialSeg {α β : Type _} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  init : ∀ a b, s b (to_rel_embedding a) → ∃ a', to_rel_embedding a' = b
#align initial_seg InitialSeg
-/

-- mathport name: initial_seg
scoped[InitialSeg] infixl:25 " ≼i " => InitialSeg

namespace InitialSeg

instance : Coe (r ≼i s) (r ↪r s) :=
  ⟨InitialSeg.toRelEmbedding⟩

instance : EmbeddingLike (r ≼i s) α β where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr with x
    exact congr_fun h x
  injective' f := f.inj'

/- warning: initial_seg.ext -> InitialSeg.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : InitialSeg.{u1, u2} α β r s} {g : InitialSeg.{u1, u2} α β r s}, (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) g x)) -> (Eq.{max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : InitialSeg.{u2, u1} α β r s} {g : InitialSeg.{u2, u1} α β r s}, (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) g x)) -> (Eq.{max (succ u2) (succ u1)} (InitialSeg.{u2, u1} α β r s) f g)
Case conversion may be inaccurate. Consider using '#align initial_seg.ext InitialSeg.extₓ'. -/
@[ext]
theorem ext {f g : r ≼i s} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align initial_seg.ext InitialSeg.ext

@[simp]
theorem coeFn_mk (f : r ↪r s) (o) : (@InitialSeg.mk _ _ r s f o : α → β) = f :=
  rfl
#align initial_seg.coe_fn_mk InitialSeg.coeFn_mk

@[simp]
theorem coeFn_toRelEmbedding (f : r ≼i s) : (f.toRelEmbedding : α → β) = f :=
  rfl
#align initial_seg.coe_fn_to_rel_embedding InitialSeg.coeFn_toRelEmbedding

/- warning: initial_seg.coe_coe_fn -> InitialSeg.coe_coe_fn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : InitialSeg.{u1, u2} α β r s), Eq.{max (succ u1) (succ u2)} ((fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (InitialSeg.{u1, u2} α β r s) (RelEmbedding.{u1, u2} α β r s) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (RelEmbedding.{u1, u2} α β r s) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (RelEmbedding.{u1, u2} α β r s) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (RelEmbedding.{u1, u2} α β r s) (InitialSeg.RelEmbedding.hasCoe.{u1, u2} α β r s)))) f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (InitialSeg.{u1, u2} α β r s) (RelEmbedding.{u1, u2} α β r s) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (RelEmbedding.{u1, u2} α β r s) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (RelEmbedding.{u1, u2} α β r s) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (RelEmbedding.{u1, u2} α β r s) (InitialSeg.RelEmbedding.hasCoe.{u1, u2} α β r s)))) f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : InitialSeg.{u2, u1} α β r s), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (InitialSeg.toRelEmbedding.{u2, u1} α β r s f))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) f)
Case conversion may be inaccurate. Consider using '#align initial_seg.coe_coe_fn InitialSeg.coe_coe_fnₓ'. -/
@[simp]
theorem coe_coe_fn (f : r ≼i s) : ((f : r ↪r s) : α → β) = f :=
  rfl
#align initial_seg.coe_coe_fn InitialSeg.coe_coe_fn

/- warning: initial_seg.init' -> InitialSeg.init' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : InitialSeg.{u1, u2} α β r s) {a : α} {b : β}, (s b (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a)) -> (Exists.{succ u1} α (fun (a' : α) => Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a') b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : InitialSeg.{u2, u1} α β r s) {a : α} {b : β}, (s b (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) f a)) -> (Exists.{succ u2} α (fun (a' : α) => Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a') (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) f a') b))
Case conversion may be inaccurate. Consider using '#align initial_seg.init' InitialSeg.init'ₓ'. -/
theorem init' (f : r ≼i s) {a : α} {b : β} : s b (f a) → ∃ a', f a' = b :=
  f.init _ _
#align initial_seg.init' InitialSeg.init'

/- warning: initial_seg.map_rel_iff -> InitialSeg.map_rel_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : InitialSeg.{u1, u2} α β r s) {a : α} {b : α}, Iff (s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f b)) (r a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : α} {a : α} (b : InitialSeg.{u2, u1} α β r s), Iff (s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) b f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) b a)) (r f a)
Case conversion may be inaccurate. Consider using '#align initial_seg.map_rel_iff InitialSeg.map_rel_iffₓ'. -/
theorem map_rel_iff (f : r ≼i s) {a b : α} : s (f a) (f b) ↔ r a b :=
  f.1.map_rel_iff
#align initial_seg.map_rel_iff InitialSeg.map_rel_iff

/- warning: initial_seg.init_iff -> InitialSeg.init_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : InitialSeg.{u1, u2} α β r s) {a : α} {b : β}, Iff (s b (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a)) (Exists.{succ u1} α (fun (a' : α) => And (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a') b) (r a' a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : InitialSeg.{u2, u1} α β r s) {a : α} {b : β}, Iff (s b (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) f a)) (Exists.{succ u2} α (fun (a' : α) => And (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a') (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) f a') b) (r a' a)))
Case conversion may be inaccurate. Consider using '#align initial_seg.init_iff InitialSeg.init_iffₓ'. -/
theorem init_iff (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  ⟨fun h =>
    let ⟨a', e⟩ := f.init' h
    ⟨a', e, f.map_rel_iff.1 (e.symm ▸ h)⟩,
    fun ⟨a', e, h⟩ => e ▸ f.map_rel_iff.2 h⟩
#align initial_seg.init_iff InitialSeg.init_iff

#print InitialSeg.ofIso /-
/-- An order isomorphism is an initial segment -/
def ofIso (f : r ≃r s) : r ≼i s :=
  ⟨f, fun a b h => ⟨f.symm b, RelIso.apply_symm_apply f _⟩⟩
#align initial_seg.of_iso InitialSeg.ofIso
-/

#print InitialSeg.refl /-
/-- The identity function shows that `≼i` is reflexive -/
@[refl]
protected def refl (r : α → α → Prop) : r ≼i r :=
  ⟨RelEmbedding.refl _, fun a b h => ⟨_, rfl⟩⟩
#align initial_seg.refl InitialSeg.refl
-/

instance (r : α → α → Prop) : Inhabited (r ≼i r) :=
  ⟨InitialSeg.refl r⟩

#print InitialSeg.trans /-
/-- Composition of functions shows that `≼i` is transitive -/
@[trans]
protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
  ⟨f.1.trans g.1, fun a c h => by
    simp at h⊢
    rcases g.2 _ _ h with ⟨b, rfl⟩; have h := g.map_rel_iff.1 h
    rcases f.2 _ _ h with ⟨a', rfl⟩; exact ⟨a', rfl⟩⟩
#align initial_seg.trans InitialSeg.trans
-/

/- warning: initial_seg.refl_apply -> InitialSeg.refl_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} (x : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (InitialSeg.{u1, u1} α α r r) (fun (_x : InitialSeg.{u1, u1} α α r r) => α -> α) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (InitialSeg.{u1, u1} α α r r) α (fun (_x : α) => α) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (InitialSeg.{u1, u1} α α r r) α α (InitialSeg.embeddingLike.{u1, u1} α α r r))) (InitialSeg.refl.{u1} α r) x) x
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) x) (FunLike.coe.{succ u1, succ u1, succ u1} (InitialSeg.{u1, u1} α α r r) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (InitialSeg.{u1, u1} α α r r) α α (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u1} α α r r)) (InitialSeg.refl.{u1} α r) x) x
Case conversion may be inaccurate. Consider using '#align initial_seg.refl_apply InitialSeg.refl_applyₓ'. -/
@[simp]
theorem refl_apply (x : α) : InitialSeg.refl r x = x :=
  rfl
#align initial_seg.refl_apply InitialSeg.refl_apply

/- warning: initial_seg.trans_apply -> InitialSeg.trans_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : InitialSeg.{u1, u2} α β r s) (g : InitialSeg.{u2, u3} β γ s t) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InitialSeg.{u1, u3} α γ r t) (fun (_x : InitialSeg.{u1, u3} α γ r t) => α -> γ) (FunLike.hasCoeToFun.{max (succ u1) (succ u3), succ u1, succ u3} (InitialSeg.{u1, u3} α γ r t) α (fun (_x : α) => γ) (EmbeddingLike.toFunLike.{max (succ u1) (succ u3), succ u1, succ u3} (InitialSeg.{u1, u3} α γ r t) α γ (InitialSeg.embeddingLike.{u1, u3} α γ r t))) (InitialSeg.trans.{u1, u2, u3} α β γ r s t f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InitialSeg.{u2, u3} β γ s t) (fun (_x : InitialSeg.{u2, u3} β γ s t) => β -> γ) (FunLike.hasCoeToFun.{max (succ u2) (succ u3), succ u2, succ u3} (InitialSeg.{u2, u3} β γ s t) β (fun (_x : β) => γ) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (InitialSeg.{u2, u3} β γ s t) β γ (InitialSeg.embeddingLike.{u2, u3} β γ s t))) g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : InitialSeg.{u3, u2} α β r s) (g : InitialSeg.{u2, u1} β γ s t) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) a) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (InitialSeg.{u3, u1} α γ r t) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (InitialSeg.{u3, u1} α γ r t) α γ (InitialSeg.instEmbeddingLikeInitialSeg.{u3, u1} α γ r t)) (InitialSeg.trans.{u3, u2, u1} α β γ r s t f g) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} β γ s t) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} β γ s t) β γ (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} β γ s t)) g (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (InitialSeg.{u3, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (InitialSeg.{u3, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u3, u2} α β r s)) f a))
Case conversion may be inaccurate. Consider using '#align initial_seg.trans_apply InitialSeg.trans_applyₓ'. -/
@[simp]
theorem trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a) :=
  rfl
#align initial_seg.trans_apply InitialSeg.trans_apply

#print InitialSeg.unique_of_trichotomous_of_irrefl /-
theorem unique_of_trichotomous_of_irrefl [IsTrichotomous β s] [IsIrrefl β s] :
    WellFounded r → Subsingleton (r ≼i s)
  | ⟨h⟩ =>
    ⟨fun f g => by
      ext a
      have := h a; induction' this with a H IH
      refine' extensional_of_trichotomous_of_irrefl s fun x => _
      simp only [f.init_iff, g.init_iff]
      exact exists_congr fun x => and_congr_left fun hx => IH _ hx ▸ Iff.rfl⟩
#align initial_seg.unique_of_trichotomous_of_irrefl InitialSeg.unique_of_trichotomous_of_irrefl
-/

instance [IsWellOrder β s] : Subsingleton (r ≼i s) :=
  ⟨fun a =>
    @Subsingleton.elim _
      (unique_of_trichotomous_of_irrefl (@RelEmbedding.wellFounded _ _ r s a IsWellFounded.wf)) a⟩

/- warning: initial_seg.eq -> InitialSeg.eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s) (g : InitialSeg.{u1, u2} α β r s) (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) g a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s) (g : InitialSeg.{u1, u2} α β r s) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) f a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) g a)
Case conversion may be inaccurate. Consider using '#align initial_seg.eq InitialSeg.eqₓ'. -/
protected theorem eq [IsWellOrder β s] (f g : r ≼i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]
#align initial_seg.eq InitialSeg.eq

/- warning: initial_seg.antisymm.aux -> InitialSeg.Antisymm.aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u1} α r] (f : InitialSeg.{u1, u2} α β r s) (g : InitialSeg.{u2, u1} β α s r), Function.LeftInverse.{succ u1, succ u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (InitialSeg.{u2, u1} β α s r) (fun (_x : InitialSeg.{u2, u1} β α s r) => β -> α) (FunLike.hasCoeToFun.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} β α s r) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} β α s r) β α (InitialSeg.embeddingLike.{u2, u1} β α s r))) g) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} α r] (f : InitialSeg.{u2, u1} α β r s) (g : InitialSeg.{u1, u2} β α s r), Function.LeftInverse.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (InitialSeg.{u1, u2} β α s r) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (InitialSeg.{u1, u2} β α s r) β α (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} β α s r)) g) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} α β r s)) f)
Case conversion may be inaccurate. Consider using '#align initial_seg.antisymm.aux InitialSeg.Antisymm.auxₓ'. -/
theorem Antisymm.aux [IsWellOrder α r] (f : r ≼i s) (g : s ≼i r) : LeftInverse g f :=
  InitialSeg.eq (f.trans g) (InitialSeg.refl _)
#align initial_seg.antisymm.aux InitialSeg.Antisymm.aux

#print InitialSeg.antisymm /-
/-- If we have order embeddings between `α` and `β` whose images are initial segments, and `β`
is a well-order then `α` and `β` are order-isomorphic. -/
def antisymm [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
  haveI := f.to_rel_embedding.is_well_order
  ⟨⟨f, g, antisymm.aux f g, antisymm.aux g f⟩, fun _ _ => f.map_rel_iff'⟩
#align initial_seg.antisymm InitialSeg.antisymm
-/

/- warning: initial_seg.antisymm_to_fun -> InitialSeg.antisymm_toFun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s) (g : InitialSeg.{u2, u1} β α s r), Eq.{max (succ u1) (succ u2)} ((fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (InitialSeg.antisymm.{u1, u2} α β r s _inst_1 f g)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) (InitialSeg.antisymm.{u1, u2} α β r s _inst_1 f g)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s) (g : InitialSeg.{u2, u1} β α s r), Eq.{max (succ u1) (succ u2)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (RelIso.toRelEmbedding.{u1, u2} α β r s (InitialSeg.antisymm.{u1, u2} α β r s _inst_1 f g)))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) f)
Case conversion may be inaccurate. Consider using '#align initial_seg.antisymm_to_fun InitialSeg.antisymm_toFunₓ'. -/
@[simp]
theorem antisymm_toFun [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f :=
  rfl
#align initial_seg.antisymm_to_fun InitialSeg.antisymm_toFun

/- warning: initial_seg.antisymm_symm -> InitialSeg.antisymm_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u1} α r] [_inst_2 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s) (g : InitialSeg.{u2, u1} β α s r), Eq.{max (succ u2) (succ u1)} (RelIso.{u2, u1} β α s r) (RelIso.symm.{u1, u2} α β r s (InitialSeg.antisymm.{u1, u2} α β r s _inst_2 f g)) (InitialSeg.antisymm.{u2, u1} β α s r _inst_1 g f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} α r] [_inst_2 : IsWellOrder.{u1} β s] (f : InitialSeg.{u2, u1} α β r s) (g : InitialSeg.{u1, u2} β α s r), Eq.{max (succ u2) (succ u1)} (RelIso.{u1, u2} β α s r) (RelIso.symm.{u2, u1} α β r s (InitialSeg.antisymm.{u2, u1} α β r s _inst_2 f g)) (InitialSeg.antisymm.{u1, u2} β α s r _inst_1 g f)
Case conversion may be inaccurate. Consider using '#align initial_seg.antisymm_symm InitialSeg.antisymm_symmₓ'. -/
@[simp]
theorem antisymm_symm [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) :
    (antisymm f g).symm = antisymm g f :=
  RelIso.coe_fn_injective rfl
#align initial_seg.antisymm_symm InitialSeg.antisymm_symm

/- warning: initial_seg.eq_or_principal -> InitialSeg.eq_or_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s), Or (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f)) (Exists.{succ u2} β (fun (b : β) => forall (x : β), Iff (s x b) (Exists.{succ u1} α (fun (y : α) => Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f y) x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s), Or (Function.Surjective.{succ u1, succ u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) f)) (Exists.{succ u2} β (fun (b : β) => forall (x : β), Iff (s x b) (Exists.{succ u1} α (fun (y : α) => Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) y) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) f y) x))))
Case conversion may be inaccurate. Consider using '#align initial_seg.eq_or_principal InitialSeg.eq_or_principalₓ'. -/
theorem eq_or_principal [IsWellOrder β s] (f : r ≼i s) :
    Surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x :=
  or_iff_not_imp_right.2 fun h b =>
    Acc.recOn (IsWellFounded.wf.apply b : Acc s b) fun x H IH =>
      not_forall_not.1 fun hn =>
        h
          ⟨x, fun y =>
            ⟨IH _, fun ⟨a, e⟩ => by
              rw [← e] <;>
                exact
                  (trichotomous _ _).resolve_right
                    (not_or_of_not (hn a) fun hl => not_exists.2 hn (f.init' hl))⟩⟩
#align initial_seg.eq_or_principal InitialSeg.eq_or_principal

/- warning: initial_seg.cod_restrict -> InitialSeg.codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : InitialSeg.{u1, u2} α β r s), (forall (a : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a) p) -> (InitialSeg.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : InitialSeg.{u1, u2} α β r s), (forall (a : α), Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Set.{u2} β) (Set.instMembershipSet.{u2} β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) f a) p) -> (InitialSeg.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p))
Case conversion may be inaccurate. Consider using '#align initial_seg.cod_restrict InitialSeg.codRestrictₓ'. -/
/-- Restrict the codomain of an initial segment -/
def codRestrict (p : Set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, fun a ⟨b, m⟩ (h : s b (f a)) =>
    let ⟨a', e⟩ := f.init' h
    ⟨a', by clear _let_match <;> subst e <;> rfl⟩⟩
#align initial_seg.cod_restrict InitialSeg.codRestrict

/- warning: initial_seg.cod_restrict_apply -> InitialSeg.codRestrict_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : InitialSeg.{u1, u2} α β r s) (H : forall (a : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a) p) (a : α), Eq.{succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) (fun (_x : InitialSeg.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) => α -> (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p)) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) α (fun (_x : α) => coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) (InitialSeg.embeddingLike.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)))) (InitialSeg.codRestrict.{u1, u2} α β r s p f H) a) (Subtype.mk.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x p) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a) (H a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : InitialSeg.{u1, u2} α β r s) (H : forall (a : α), Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Set.{u2} β) (Set.instMembershipSet.{u2} β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) f a) p) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Set.Elem.{u2} β p) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Set.Elem.{u2} β p) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p)) α (Set.Elem.{u2} β p) (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p))) (InitialSeg.codRestrict.{u1, u2} α β r s p f H) a) (Subtype.mk.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x p) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) f a) (H a))
Case conversion may be inaccurate. Consider using '#align initial_seg.cod_restrict_apply InitialSeg.codRestrict_applyₓ'. -/
@[simp]
theorem codRestrict_apply (p) (f : r ≼i s) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl
#align initial_seg.cod_restrict_apply InitialSeg.codRestrict_apply

#print InitialSeg.ofIsEmpty /-
/-- Initial segment from an empty type. -/
def ofIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : r ≼i s :=
  ⟨RelEmbedding.ofIsEmpty r s, isEmptyElim⟩
#align initial_seg.of_is_empty InitialSeg.ofIsEmpty
-/

#print InitialSeg.leAdd /-
/-- Initial segment embedding of an order `r` into the disjoint union of `r` and `s`. -/
def leAdd (r : α → α → Prop) (s : β → β → Prop) : r ≼i Sum.Lex r s :=
  ⟨⟨⟨Sum.inl, fun _ _ => Sum.inl.inj⟩, fun a b => Sum.lex_inl_inl⟩, fun a b => by
    cases b <;> [exact fun _ => ⟨_, rfl⟩, exact False.elim ∘ Sum.lex_inr_inl]⟩
#align initial_seg.le_add InitialSeg.leAdd
-/

/- warning: initial_seg.le_add_apply -> InitialSeg.leAdd_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> α -> Prop) (s : β -> β -> Prop) (a : α), Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (coeFn.{max (succ u1) (succ (max u1 u2)), max (succ u1) (succ (max u1 u2))} (InitialSeg.{u1, max u1 u2} α (Sum.{u1, u2} α β) r (Sum.Lex.{u1, u2} α β r s)) (fun (_x : InitialSeg.{u1, max u1 u2} α (Sum.{u1, u2} α β) r (Sum.Lex.{u1, u2} α β r s)) => α -> (Sum.{u1, u2} α β)) (FunLike.hasCoeToFun.{max (succ u1) (succ (max u1 u2)), succ u1, succ (max u1 u2)} (InitialSeg.{u1, max u1 u2} α (Sum.{u1, u2} α β) r (Sum.Lex.{u1, u2} α β r s)) α (fun (_x : α) => Sum.{u1, u2} α β) (EmbeddingLike.toFunLike.{max (succ u1) (succ (max u1 u2)), succ u1, succ (max u1 u2)} (InitialSeg.{u1, max u1 u2} α (Sum.{u1, u2} α β) r (Sum.Lex.{u1, u2} α β r s)) α (Sum.{u1, u2} α β) (InitialSeg.embeddingLike.{u1, max u1 u2} α (Sum.{u1, u2} α β) r (Sum.Lex.{u1, u2} α β r s)))) (InitialSeg.leAdd.{u1, u2} α β r s) a) (Sum.inl.{u1, u2} α β a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> α -> Prop) (s : β -> β -> Prop) (a : α), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Sum.{u2, u1} α β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, max (succ u2) (succ u1)} (InitialSeg.{u2, max u1 u2} α (Sum.{u2, u1} α β) r (Sum.Lex.{u2, u1} α β r s)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Sum.{u2, u1} α β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, max (succ u2) (succ u1)} (InitialSeg.{u2, max u1 u2} α (Sum.{u2, u1} α β) r (Sum.Lex.{u2, u1} α β r s)) α (Sum.{u2, u1} α β) (InitialSeg.instEmbeddingLikeInitialSeg.{u2, max u2 u1} α (Sum.{u2, u1} α β) r (Sum.Lex.{u2, u1} α β r s))) (InitialSeg.leAdd.{u2, u1} α β r s) a) (Sum.inl.{u2, u1} α β a)
Case conversion may be inaccurate. Consider using '#align initial_seg.le_add_apply InitialSeg.leAdd_applyₓ'. -/
@[simp]
theorem leAdd_apply (r : α → α → Prop) (s : β → β → Prop) (a) : leAdd r s a = Sum.inl a :=
  rfl
#align initial_seg.le_add_apply InitialSeg.leAdd_apply

end InitialSeg

/-!
### Principal segments

Order embeddings whose range is a principal segment of `s` (i.e., an interval of the form
`(-∞, top)` for some element `top` of `β`). The type of these embeddings from `r` to `s` is called
`principal_seg r s`, and denoted by `r ≺i s`. Principal segments are in particular initial
segments.
-/


#print PrincipalSeg /-
/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an order
embedding whose range is an open interval `(-∞, top)` for some element `top` of `β`. Such order
embeddings are called principal segments -/
@[nolint has_nonempty_instance]
structure PrincipalSeg {α β : Type _} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  top : β
  down' : ∀ b, s b top ↔ ∃ a, to_rel_embedding a = b
#align principal_seg PrincipalSeg
-/

-- mathport name: principal_seg
scoped[InitialSeg] infixl:25 " ≺i " => PrincipalSeg

namespace PrincipalSeg

instance : Coe (r ≺i s) (r ↪r s) :=
  ⟨PrincipalSeg.toRelEmbedding⟩

instance : CoeFun (r ≺i s) fun _ => α → β :=
  ⟨fun f => f⟩

/- warning: principal_seg.coe_fn_mk -> PrincipalSeg.coe_fn_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u1, u2} α β r s) (t : β) (o : forall (b : β), Iff (s b t) (Exists.{succ u1} α (fun (a : α) => Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a) b))), Eq.{max (succ u1) (succ u2)} ((fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.mk.{u1, u2} α β r s f t o)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) (PrincipalSeg.mk.{u1, u2} α β r s f t o)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u2, u1} α β r s) (t : β) (o : forall (b : β), Iff (s b t) (Exists.{succ u2} α (fun (a : α) => Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f) a) b))), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (PrincipalSeg.toRelEmbedding.{u2, u1} α β r s (PrincipalSeg.mk.{u2, u1} α β r s f t o)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f))
Case conversion may be inaccurate. Consider using '#align principal_seg.coe_fn_mk PrincipalSeg.coe_fn_mkₓ'. -/
@[simp]
theorem coe_fn_mk (f : r ↪r s) (t o) : (@PrincipalSeg.mk _ _ r s f t o : α → β) = f :=
  rfl
#align principal_seg.coe_fn_mk PrincipalSeg.coe_fn_mk

@[simp]
theorem coeFn_toRelEmbedding (f : r ≺i s) : (f.toRelEmbedding : α → β) = f :=
  rfl
#align principal_seg.coe_fn_to_rel_embedding PrincipalSeg.coeFn_toRelEmbedding

@[simp]
theorem coe_coeFn (f : r ≺i s) : ((f : r ↪r s) : α → β) = f :=
  rfl
#align principal_seg.coe_coe_fn PrincipalSeg.coe_coeFn

/- warning: principal_seg.down -> PrincipalSeg.down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : PrincipalSeg.{u1, u2} α β r s) {b : β}, Iff (s b (PrincipalSeg.top.{u1, u2} α β r s f)) (Exists.{succ u1} α (fun (a : α) => Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : PrincipalSeg.{u2, u1} α β r s) {b : β}, Iff (s b (PrincipalSeg.top.{u2, u1} α β r s f)) (Exists.{succ u2} α (fun (a : α) => Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (PrincipalSeg.toRelEmbedding.{u2, u1} α β r s f)) a) b))
Case conversion may be inaccurate. Consider using '#align principal_seg.down PrincipalSeg.downₓ'. -/
theorem down (f : r ≺i s) : ∀ {b : β}, s b f.top ↔ ∃ a, f a = b :=
  f.down'
#align principal_seg.down PrincipalSeg.down

/- warning: principal_seg.lt_top -> PrincipalSeg.lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : PrincipalSeg.{u1, u2} α β r s) (a : α), s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a) (PrincipalSeg.top.{u1, u2} α β r s f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : PrincipalSeg.{u2, u1} α β r s) (a : α), s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (PrincipalSeg.toRelEmbedding.{u2, u1} α β r s f)) a) (PrincipalSeg.top.{u2, u1} α β r s f)
Case conversion may be inaccurate. Consider using '#align principal_seg.lt_top PrincipalSeg.lt_topₓ'. -/
theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
  f.down.2 ⟨_, rfl⟩
#align principal_seg.lt_top PrincipalSeg.lt_top

/- warning: principal_seg.init -> PrincipalSeg.init is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrans.{u2} β s] (f : PrincipalSeg.{u1, u2} α β r s) {a : α} {b : β}, (s b (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a)) -> (Exists.{succ u1} α (fun (a' : α) => Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a') b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrans.{u2} β s] (f : PrincipalSeg.{u1, u2} α β r s) {a : α} {b : β}, (s b (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f)) a)) -> (Exists.{succ u1} α (fun (a' : α) => Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a') (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f)) a') b))
Case conversion may be inaccurate. Consider using '#align principal_seg.init PrincipalSeg.initₓ'. -/
theorem init [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) : ∃ a', f a' = b :=
  f.down.1 <| trans h <| f.lt_top _
#align principal_seg.init PrincipalSeg.init

#print PrincipalSeg.hasCoeInitialSeg /-
/-- A principal segment is in particular an initial segment. -/
instance hasCoeInitialSeg [IsTrans β s] : Coe (r ≺i s) (r ≼i s) :=
  ⟨fun f => ⟨f.toRelEmbedding, fun a b => f.init⟩⟩
#align principal_seg.has_coe_initial_seg PrincipalSeg.hasCoeInitialSeg
-/

/- warning: principal_seg.coe_coe_fn' -> PrincipalSeg.coe_coe_fn' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrans.{u2} β s] (f : PrincipalSeg.{u1, u2} α β r s), Eq.{max (succ u1) (succ u2)} ((fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (PrincipalSeg.{u1, u2} α β r s) (InitialSeg.{u1, u2} α β r s) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (InitialSeg.{u1, u2} α β r s) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (InitialSeg.{u1, u2} α β r s) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (InitialSeg.{u1, u2} α β r s) (PrincipalSeg.hasCoeInitialSeg.{u1, u2} α β r s _inst_1)))) f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (PrincipalSeg.{u1, u2} α β r s) (InitialSeg.{u1, u2} α β r s) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (InitialSeg.{u1, u2} α β r s) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (InitialSeg.{u1, u2} α β r s) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (InitialSeg.{u1, u2} α β r s) (PrincipalSeg.hasCoeInitialSeg.{u1, u2} α β r s _inst_1)))) f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrans.{u2} β s] (f : PrincipalSeg.{u1, u2} α β r s), Eq.{max (succ u1) (succ u2)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) (InitialSeg.mk.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f) (PrincipalSeg.hasCoeInitialSeg.proof_1.{u1, u2} α β r s _inst_1 f))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f)))
Case conversion may be inaccurate. Consider using '#align principal_seg.coe_coe_fn' PrincipalSeg.coe_coe_fn'ₓ'. -/
theorem coe_coe_fn' [IsTrans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f :=
  rfl
#align principal_seg.coe_coe_fn' PrincipalSeg.coe_coe_fn'

/- warning: principal_seg.init_iff -> PrincipalSeg.init_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrans.{u2} β s] (f : PrincipalSeg.{u1, u2} α β r s) {a : α} {b : β}, Iff (s b (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a)) (Exists.{succ u1} α (fun (a' : α) => And (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a') b) (r a' a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrans.{u2} β s] (f : PrincipalSeg.{u1, u2} α β r s) {a : α} {b : β}, Iff (s b (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f)) a)) (Exists.{succ u1} α (fun (a' : α) => And (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a') (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f)) a') b) (r a' a)))
Case conversion may be inaccurate. Consider using '#align principal_seg.init_iff PrincipalSeg.init_iffₓ'. -/
theorem init_iff [IsTrans β s] (f : r ≺i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  @InitialSeg.init_iff α β r s f a b
#align principal_seg.init_iff PrincipalSeg.init_iff

#print PrincipalSeg.irrefl /-
theorem irrefl {r : α → α → Prop} [IsWellOrder α r] (f : r ≺i r) : False :=
  by
  have := f.lt_top f.top
  rw [show f f.top = f.top from InitialSeg.eq (↑f) (InitialSeg.refl r) f.top] at this
  exact irrefl _ this
#align principal_seg.irrefl PrincipalSeg.irrefl
-/

instance (r : α → α → Prop) [IsWellOrder α r] : IsEmpty (r ≺i r) :=
  ⟨fun f => f.irrefl⟩

#print PrincipalSeg.ltLe /-
/-- Composition of a principal segment with an initial segment, as a principal segment -/
def ltLe (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, fun a => by
    simp only [g.init_iff, f.down', exists_and_distrib_left.symm, exists_swap,
        RelEmbedding.trans_apply, exists_eq_right'] <;>
      rfl⟩
#align principal_seg.lt_le PrincipalSeg.ltLe
-/

/- warning: principal_seg.lt_le_apply -> PrincipalSeg.lt_le_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : PrincipalSeg.{u1, u2} α β r s) (g : InitialSeg.{u2, u3} β γ s t) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (PrincipalSeg.{u1, u3} α γ r t) (fun (_x : PrincipalSeg.{u1, u3} α γ r t) => α -> γ) (PrincipalSeg.hasCoeToFun.{u1, u3} α γ r t) (PrincipalSeg.ltLe.{u1, u2, u3} α β γ r s t f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InitialSeg.{u2, u3} β γ s t) (fun (_x : InitialSeg.{u2, u3} β γ s t) => β -> γ) (FunLike.hasCoeToFun.{max (succ u2) (succ u3), succ u2, succ u3} (InitialSeg.{u2, u3} β γ s t) β (fun (_x : β) => γ) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (InitialSeg.{u2, u3} β γ s t) β γ (InitialSeg.embeddingLike.{u2, u3} β γ s t))) g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : PrincipalSeg.{u3, u2} α β r s) (g : InitialSeg.{u2, u1} β γ s t) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) a) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α γ) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α γ) α γ (Function.instEmbeddingLikeEmbedding.{succ u3, succ u1} α γ)) (RelEmbedding.toEmbedding.{u3, u1} α γ r t (PrincipalSeg.toRelEmbedding.{u3, u1} α γ r t (PrincipalSeg.ltLe.{u3, u2, u1} α β γ r s t f g))) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} β γ s t) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} β γ s t) β γ (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} β γ s t)) g (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β r s (PrincipalSeg.toRelEmbedding.{u3, u2} α β r s f)) a))
Case conversion may be inaccurate. Consider using '#align principal_seg.lt_le_apply PrincipalSeg.lt_le_applyₓ'. -/
@[simp]
theorem lt_le_apply (f : r ≺i s) (g : s ≼i t) (a : α) : (f.ltLe g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _
#align principal_seg.lt_le_apply PrincipalSeg.lt_le_apply

/- warning: principal_seg.lt_le_top -> PrincipalSeg.lt_le_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : PrincipalSeg.{u1, u2} α β r s) (g : InitialSeg.{u2, u3} β γ s t), Eq.{succ u3} γ (PrincipalSeg.top.{u1, u3} α γ r t (PrincipalSeg.ltLe.{u1, u2, u3} α β γ r s t f g)) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InitialSeg.{u2, u3} β γ s t) (fun (_x : InitialSeg.{u2, u3} β γ s t) => β -> γ) (FunLike.hasCoeToFun.{max (succ u2) (succ u3), succ u2, succ u3} (InitialSeg.{u2, u3} β γ s t) β (fun (_x : β) => γ) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (InitialSeg.{u2, u3} β γ s t) β γ (InitialSeg.embeddingLike.{u2, u3} β γ s t))) g (PrincipalSeg.top.{u1, u2} α β r s f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : PrincipalSeg.{u3, u2} α β r s) (g : InitialSeg.{u2, u1} β γ s t), Eq.{succ u1} γ (PrincipalSeg.top.{u3, u1} α γ r t (PrincipalSeg.ltLe.{u3, u2, u1} α β γ r s t f g)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} β γ s t) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (InitialSeg.{u2, u1} β γ s t) β γ (InitialSeg.instEmbeddingLikeInitialSeg.{u2, u1} β γ s t)) g (PrincipalSeg.top.{u3, u2} α β r s f))
Case conversion may be inaccurate. Consider using '#align principal_seg.lt_le_top PrincipalSeg.lt_le_topₓ'. -/
@[simp]
theorem lt_le_top (f : r ≺i s) (g : s ≼i t) : (f.ltLe g).top = g f.top :=
  rfl
#align principal_seg.lt_le_top PrincipalSeg.lt_le_top

#print PrincipalSeg.trans /-
/-- Composition of two principal segments as a principal segment -/
@[trans]
protected def trans [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
  ltLe f g
#align principal_seg.trans PrincipalSeg.trans
-/

/- warning: principal_seg.trans_apply -> PrincipalSeg.trans_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsTrans.{u3} γ t] (f : PrincipalSeg.{u1, u2} α β r s) (g : PrincipalSeg.{u2, u3} β γ s t) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (PrincipalSeg.{u1, u3} α γ r t) (fun (_x : PrincipalSeg.{u1, u3} α γ r t) => α -> γ) (PrincipalSeg.hasCoeToFun.{u1, u3} α γ r t) (PrincipalSeg.trans.{u1, u2, u3} α β γ r s t _inst_1 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (PrincipalSeg.{u2, u3} β γ s t) (fun (_x : PrincipalSeg.{u2, u3} β γ s t) => β -> γ) (PrincipalSeg.hasCoeToFun.{u2, u3} β γ s t) g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsTrans.{u3} γ t] (f : PrincipalSeg.{u2, u1} α β r s) (g : PrincipalSeg.{u1, u3} β γ s t) (a : α), Eq.{succ u3} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) a) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α γ) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α γ) α γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u3} α γ)) (RelEmbedding.toEmbedding.{u2, u3} α γ r t (PrincipalSeg.toRelEmbedding.{u2, u3} α γ r t (PrincipalSeg.trans.{u2, u1, u3} α β γ r s t _inst_1 f g))) a) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u1, succ u3} β γ)) (RelEmbedding.toEmbedding.{u1, u3} β γ s t (PrincipalSeg.toRelEmbedding.{u1, u3} β γ s t g)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (PrincipalSeg.toRelEmbedding.{u2, u1} α β r s f)) a))
Case conversion may be inaccurate. Consider using '#align principal_seg.trans_apply PrincipalSeg.trans_applyₓ'. -/
@[simp]
theorem trans_apply [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : (f.trans g) a = g (f a) :=
  lt_le_apply _ _ _
#align principal_seg.trans_apply PrincipalSeg.trans_apply

/- warning: principal_seg.trans_top -> PrincipalSeg.trans_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsTrans.{u3} γ t] (f : PrincipalSeg.{u1, u2} α β r s) (g : PrincipalSeg.{u2, u3} β γ s t), Eq.{succ u3} γ (PrincipalSeg.top.{u1, u3} α γ r t (PrincipalSeg.trans.{u1, u2, u3} α β γ r s t _inst_1 f g)) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (PrincipalSeg.{u2, u3} β γ s t) (fun (_x : PrincipalSeg.{u2, u3} β γ s t) => β -> γ) (PrincipalSeg.hasCoeToFun.{u2, u3} β γ s t) g (PrincipalSeg.top.{u1, u2} α β r s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsTrans.{u3} γ t] (f : PrincipalSeg.{u2, u1} α β r s) (g : PrincipalSeg.{u1, u3} β γ s t), Eq.{succ u3} γ (PrincipalSeg.top.{u2, u3} α γ r t (PrincipalSeg.trans.{u2, u1, u3} α β γ r s t _inst_1 f g)) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u1, succ u3} β γ)) (RelEmbedding.toEmbedding.{u1, u3} β γ s t (PrincipalSeg.toRelEmbedding.{u1, u3} β γ s t g)) (PrincipalSeg.top.{u2, u1} α β r s f))
Case conversion may be inaccurate. Consider using '#align principal_seg.trans_top PrincipalSeg.trans_topₓ'. -/
@[simp]
theorem trans_top [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : (f.trans g).top = g f.top :=
  rfl
#align principal_seg.trans_top PrincipalSeg.trans_top

#print PrincipalSeg.equivLT /-
/-- Composition of an order isomorphism with a principal segment, as a principal segment -/
def equivLT (f : r ≃r s) (g : s ≺i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g.top, fun c =>
    suffices (∃ a : β, g a = c) ↔ ∃ a : α, g (f a) = c by simpa [g.down]
    ⟨fun ⟨b, h⟩ => ⟨f.symm b, by simp only [h, RelIso.apply_symm_apply, RelIso.coe_coeFn]⟩,
      fun ⟨a, h⟩ => ⟨f a, h⟩⟩⟩
#align principal_seg.equiv_lt PrincipalSeg.equivLT
-/

#print PrincipalSeg.ltEquiv /-
/-- Composition of a principal segment with an order isomorphism, as a principal segment -/
def ltEquiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : PrincipalSeg r s)
    (g : s ≃r t) : PrincipalSeg r t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top,
    by
    intro x
    rw [← g.apply_symm_apply x, g.map_rel_iff, f.down', exists_congr]
    intro y; exact ⟨congr_arg g, fun h => g.to_equiv.bijective.1 h⟩⟩
#align principal_seg.lt_equiv PrincipalSeg.ltEquiv
-/

/- warning: principal_seg.equiv_lt_apply -> PrincipalSeg.equivLT_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : RelIso.{u1, u2} α β r s) (g : PrincipalSeg.{u2, u3} β γ s t) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (PrincipalSeg.{u1, u3} α γ r t) (fun (_x : PrincipalSeg.{u1, u3} α γ r t) => α -> γ) (PrincipalSeg.hasCoeToFun.{u1, u3} α γ r t) (PrincipalSeg.equivLT.{u1, u2, u3} α β γ r s t f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (PrincipalSeg.{u2, u3} β γ s t) (fun (_x : PrincipalSeg.{u2, u3} β γ s t) => β -> γ) (PrincipalSeg.hasCoeToFun.{u2, u3} β γ s t) g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) f a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : RelIso.{u3, u2} α β r s) (g : PrincipalSeg.{u2, u1} β γ s t) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) a) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α γ) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α γ) α γ (Function.instEmbeddingLikeEmbedding.{succ u3, succ u1} α γ)) (RelEmbedding.toEmbedding.{u3, u1} α γ r t (PrincipalSeg.toRelEmbedding.{u3, u1} α γ r t (PrincipalSeg.equivLT.{u3, u2, u1} α β γ r s t f g))) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) (RelEmbedding.toEmbedding.{u2, u1} β γ s t (PrincipalSeg.toRelEmbedding.{u2, u1} β γ s t g)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β r s (RelIso.toRelEmbedding.{u3, u2} α β r s f)) a))
Case conversion may be inaccurate. Consider using '#align principal_seg.equiv_lt_apply PrincipalSeg.equivLT_applyₓ'. -/
@[simp]
theorem equivLT_apply (f : r ≃r s) (g : s ≺i t) (a : α) : (equivLT f g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _
#align principal_seg.equiv_lt_apply PrincipalSeg.equivLT_apply

/- warning: principal_seg.equiv_lt_top -> PrincipalSeg.equivLT_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : RelIso.{u1, u2} α β r s) (g : PrincipalSeg.{u2, u3} β γ s t), Eq.{succ u3} γ (PrincipalSeg.top.{u1, u3} α γ r t (PrincipalSeg.equivLT.{u1, u2, u3} α β γ r s t f g)) (PrincipalSeg.top.{u2, u3} β γ s t g)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : RelIso.{u3, u2} α β r s) (g : PrincipalSeg.{u2, u1} β γ s t), Eq.{succ u1} γ (PrincipalSeg.top.{u3, u1} α γ r t (PrincipalSeg.equivLT.{u3, u2, u1} α β γ r s t f g)) (PrincipalSeg.top.{u2, u1} β γ s t g)
Case conversion may be inaccurate. Consider using '#align principal_seg.equiv_lt_top PrincipalSeg.equivLT_topₓ'. -/
@[simp]
theorem equivLT_top (f : r ≃r s) (g : s ≺i t) : (equivLT f g).top = g.top :=
  rfl
#align principal_seg.equiv_lt_top PrincipalSeg.equivLT_top

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
instance [IsWellOrder β s] : Subsingleton (r ≺i s) :=
  ⟨fun f g =>
    by
    have ef : (f : α → β) = g := by
      show ((f : r ≼i s) : α → β) = g
      rw [@Subsingleton.elim _ _ (f : r ≼i s) g]
      rfl
    have et : f.top = g.top :=
      by
      refine' extensional_of_trichotomous_of_irrefl s fun x => _
      simp only [f.down, g.down, ef, coe_fn_to_rel_embedding]
    cases f
    cases g
    have := RelEmbedding.coe_fn_injective ef <;> congr ⟩

/- warning: principal_seg.top_eq -> PrincipalSeg.top_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsWellOrder.{u3} γ t], (RelIso.{u1, u2} α β r s) -> (forall (f : PrincipalSeg.{u1, u3} α γ r t) (g : PrincipalSeg.{u2, u3} β γ s t), Eq.{succ u3} γ (PrincipalSeg.top.{u1, u3} α γ r t f) (PrincipalSeg.top.{u2, u3} β γ s t g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsWellOrder.{u3} γ t], (RelIso.{u2, u1} α β r s) -> (forall (f : PrincipalSeg.{u2, u3} α γ r t) (g : PrincipalSeg.{u1, u3} β γ s t), Eq.{succ u3} γ (PrincipalSeg.top.{u2, u3} α γ r t f) (PrincipalSeg.top.{u1, u3} β γ s t g))
Case conversion may be inaccurate. Consider using '#align principal_seg.top_eq PrincipalSeg.top_eqₓ'. -/
theorem top_eq [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top := by
  rw [Subsingleton.elim f (PrincipalSeg.equivLT e g)] <;> rfl
#align principal_seg.top_eq PrincipalSeg.top_eq

/- warning: principal_seg.top_lt_top -> PrincipalSeg.topLTTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsWellOrder.{u3} γ t], (PrincipalSeg.{u1, u2} α β r s) -> (forall (g : PrincipalSeg.{u2, u3} β γ s t) (h : PrincipalSeg.{u1, u3} α γ r t), t (PrincipalSeg.top.{u1, u3} α γ r t h) (PrincipalSeg.top.{u2, u3} β γ s t g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsWellOrder.{u3} γ t], (PrincipalSeg.{u2, u1} α β r s) -> (forall (g : PrincipalSeg.{u1, u3} β γ s t) (h : PrincipalSeg.{u2, u3} α γ r t), t (PrincipalSeg.top.{u2, u3} α γ r t h) (PrincipalSeg.top.{u1, u3} β γ s t g))
Case conversion may be inaccurate. Consider using '#align principal_seg.top_lt_top PrincipalSeg.topLTTopₓ'. -/
theorem topLTTop {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} [IsWellOrder γ t]
    (f : PrincipalSeg r s) (g : PrincipalSeg s t) (h : PrincipalSeg r t) : t h.top g.top :=
  by
  rw [Subsingleton.elim h (f.trans g)]
  apply PrincipalSeg.lt_top
#align principal_seg.top_lt_top PrincipalSeg.topLTTop

#print PrincipalSeg.ofElement /-
/-- Any element of a well order yields a principal segment -/
def ofElement {α : Type _} (r : α → α → Prop) (a : α) : Subrel r { b | r b a } ≺i r :=
  ⟨Subrel.relEmbedding _ _, a, fun b => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨⟨_, h⟩, rfl⟩ => h⟩⟩
#align principal_seg.of_element PrincipalSeg.ofElement
-/

/- warning: principal_seg.of_element_apply -> PrincipalSeg.ofElement_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (r : α -> α -> Prop) (a : α) (b : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (setOf.{u1} α (fun (b : α) => r b a))), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (PrincipalSeg.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (setOf.{u1} α (fun (b : α) => r b a))) α (Subrel.{u1} α r (setOf.{u1} α (fun (b : α) => r b a))) r) (fun (_x : PrincipalSeg.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (setOf.{u1} α (fun (b : α) => r b a))) α (Subrel.{u1} α r (setOf.{u1} α (fun (b : α) => r b a))) r) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (setOf.{u1} α (fun (b : α) => r b a))) -> α) (PrincipalSeg.hasCoeToFun.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (setOf.{u1} α (fun (b : α) => r b a))) α (Subrel.{u1} α r (setOf.{u1} α (fun (b : α) => r b a))) r) (PrincipalSeg.ofElement.{u1} α r a) b) (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (setOf.{u1} α (fun (b : α) => r b a))) b)
but is expected to have type
  forall {α : Type.{u1}} (r : α -> α -> Prop) (a : α) (b : Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) => α) b) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) α) (Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) (fun (_x : Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) α) (Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) α)) (RelEmbedding.toEmbedding.{u1, u1} (Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) α (Subrel.{u1} α r (setOf.{u1} α (fun (b : α) => r b a))) r (PrincipalSeg.toRelEmbedding.{u1, u1} (Set.Elem.{u1} α (setOf.{u1} α (fun (b : α) => r b a))) α (Subrel.{u1} α r (setOf.{u1} α (fun (b : α) => r b a))) r (PrincipalSeg.ofElement.{u1} α r a))) b) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (setOf.{u1} α (fun (b : α) => r b a))) b)
Case conversion may be inaccurate. Consider using '#align principal_seg.of_element_apply PrincipalSeg.ofElement_applyₓ'. -/
@[simp]
theorem ofElement_apply {α : Type _} (r : α → α → Prop) (a : α) (b) : ofElement r a b = b.1 :=
  rfl
#align principal_seg.of_element_apply PrincipalSeg.ofElement_apply

#print PrincipalSeg.ofElement_top /-
@[simp]
theorem ofElement_top {α : Type _} (r : α → α → Prop) (a : α) : (ofElement r a).top = a :=
  rfl
#align principal_seg.of_element_top PrincipalSeg.ofElement_top
-/

/- warning: principal_seg.cod_restrict -> PrincipalSeg.codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : PrincipalSeg.{u1, u2} α β r s), (forall (a : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a) p) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (PrincipalSeg.top.{u1, u2} α β r s f) p) -> (PrincipalSeg.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : PrincipalSeg.{u1, u2} α β r s), (forall (a : α), Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Set.{u2} β) (Set.instMembershipSet.{u2} β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f)) a) p) -> (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (PrincipalSeg.top.{u1, u2} α β r s f) p) -> (PrincipalSeg.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p))
Case conversion may be inaccurate. Consider using '#align principal_seg.cod_restrict PrincipalSeg.codRestrictₓ'. -/
/-- Restrict the codomain of a principal segment -/
def codRestrict (p : Set β) (f : r ≺i s) (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) : r ≺i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, ⟨f.top, H₂⟩, fun ⟨b, h⟩ =>
    f.down.trans <|
      exists_congr fun a => show (⟨f a, H a⟩ : p).1 = _ ↔ _ from ⟨Subtype.eq, congr_arg _⟩⟩
#align principal_seg.cod_restrict PrincipalSeg.codRestrict

/- warning: principal_seg.cod_restrict_apply -> PrincipalSeg.codRestrict_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : PrincipalSeg.{u1, u2} α β r s) (H : forall (a : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a) p) (H₂ : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (PrincipalSeg.top.{u1, u2} α β r s f) p) (a : α), Eq.{succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) (fun (_x : PrincipalSeg.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) => α -> (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p)) (PrincipalSeg.hasCoeToFun.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) (PrincipalSeg.codRestrict.{u1, u2} α β r s p f H H₂) a) (Subtype.mk.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x p) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a) (H a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : PrincipalSeg.{u1, u2} α β r s) (H : forall (a : α), Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Set.{u2} β) (Set.instMembershipSet.{u2} β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f)) a) p) (H₂ : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (PrincipalSeg.top.{u1, u2} α β r s f) p) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Set.Elem.{u2} β p) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α (Set.Elem.{u2} β p)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Set.Elem.{u2} β p) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α (Set.Elem.{u2} β p)) α (Set.Elem.{u2} β p) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α (Set.Elem.{u2} β p))) (RelEmbedding.toEmbedding.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p) (PrincipalSeg.toRelEmbedding.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p) (PrincipalSeg.codRestrict.{u1, u2} α β r s p f H H₂))) a) (Subtype.mk.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x p) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f)) a) (H a))
Case conversion may be inaccurate. Consider using '#align principal_seg.cod_restrict_apply PrincipalSeg.codRestrict_applyₓ'. -/
@[simp]
theorem codRestrict_apply (p) (f : r ≺i s) (H H₂ a) : codRestrict p f H H₂ a = ⟨f a, H a⟩ :=
  rfl
#align principal_seg.cod_restrict_apply PrincipalSeg.codRestrict_apply

/- warning: principal_seg.cod_restrict_top -> PrincipalSeg.codRestrict_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : PrincipalSeg.{u1, u2} α β r s) (H : forall (a : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) f a) p) (H₂ : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (PrincipalSeg.top.{u1, u2} α β r s f) p), Eq.{succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) (PrincipalSeg.top.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p) (PrincipalSeg.codRestrict.{u1, u2} α β r s p f H H₂)) (Subtype.mk.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x p) (PrincipalSeg.top.{u1, u2} α β r s f) H₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : PrincipalSeg.{u1, u2} α β r s) (H : forall (a : α), Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Set.{u2} β) (Set.instMembershipSet.{u2} β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s f)) a) p) (H₂ : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (PrincipalSeg.top.{u1, u2} α β r s f) p), Eq.{succ u2} (Set.Elem.{u2} β p) (PrincipalSeg.top.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p) (PrincipalSeg.codRestrict.{u1, u2} α β r s p f H H₂)) (Subtype.mk.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x p) (PrincipalSeg.top.{u1, u2} α β r s f) H₂)
Case conversion may be inaccurate. Consider using '#align principal_seg.cod_restrict_top PrincipalSeg.codRestrict_topₓ'. -/
@[simp]
theorem codRestrict_top (p) (f : r ≺i s) (H H₂) : (codRestrict p f H H₂).top = ⟨f.top, H₂⟩ :=
  rfl
#align principal_seg.cod_restrict_top PrincipalSeg.codRestrict_top

#print PrincipalSeg.ofIsEmpty /-
/-- Principal segment from an empty type into a type with a minimal element. -/
def ofIsEmpty (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) : r ≺i s :=
  { RelEmbedding.ofIsEmpty r s with
    top := b
    down' := by simp [H] }
#align principal_seg.of_is_empty PrincipalSeg.ofIsEmpty
-/

/- warning: principal_seg.of_is_empty_top -> PrincipalSeg.ofIsEmpty_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : β -> β -> Prop} (r : α -> α -> Prop) [_inst_1 : IsEmpty.{succ u1} α] {b : β} (H : forall (b' : β), Not (s b' b)), Eq.{succ u2} β (PrincipalSeg.top.{u1, u2} α β r s (PrincipalSeg.ofIsEmpty.{u1, u2} α β s r _inst_1 b H)) b
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : β -> β -> Prop} (r : α -> α -> Prop) [_inst_1 : IsEmpty.{succ u2} α] {b : β} (H : forall (b' : β), Not (s b' b)), Eq.{succ u1} β (PrincipalSeg.top.{u2, u1} α β r (fun (b' : β) => s b') (PrincipalSeg.ofIsEmpty.{u2, u1} α β (fun (b' : β) => s b') r _inst_1 b H)) b
Case conversion may be inaccurate. Consider using '#align principal_seg.of_is_empty_top PrincipalSeg.ofIsEmpty_topₓ'. -/
@[simp]
theorem ofIsEmpty_top (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) :
    (ofIsEmpty r H).top = b :=
  rfl
#align principal_seg.of_is_empty_top PrincipalSeg.ofIsEmpty_top

#print PrincipalSeg.pemptyToPunit /-
/-- Principal segment from the empty relation on `pempty` to the empty relation on `punit`. -/
@[reducible]
def pemptyToPunit : @EmptyRelation PEmpty ≺i @EmptyRelation PUnit :=
  @ofIsEmpty _ _ EmptyRelation _ _ PUnit.unit fun x => not_false
#align principal_seg.pempty_to_punit PrincipalSeg.pemptyToPunit
-/

end PrincipalSeg

/-! ### Properties of initial and principal segments -/


#print InitialSeg.ltOrEq /-
/-- To an initial segment taking values in a well order, one can associate either a principal
segment (if the range is not everything, hence one can take as top the minimum of the complement
of the range) or an order isomorphism (if the range is everything). -/
noncomputable def InitialSeg.ltOrEq [IsWellOrder β s] (f : r ≼i s) : Sum (r ≺i s) (r ≃r s) :=
  by
  by_cases h : surjective f
  · exact Sum.inr (RelIso.ofSurjective f h)
  · have h' : _ := (InitialSeg.eq_or_principal f).resolve_left h
    exact Sum.inl ⟨f, Classical.choose h', Classical.choose_spec h'⟩
#align initial_seg.lt_or_eq InitialSeg.ltOrEq
-/

/- warning: initial_seg.lt_or_eq_apply_left -> InitialSeg.ltOrEq_apply_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s) (g : PrincipalSeg.{u1, u2} α β r s) (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (PrincipalSeg.{u1, u2} α β r s) (fun (_x : PrincipalSeg.{u1, u2} α β r s) => α -> β) (PrincipalSeg.hasCoeToFun.{u1, u2} α β r s) g a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s) (g : PrincipalSeg.{u1, u2} α β r s) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (PrincipalSeg.toRelEmbedding.{u1, u2} α β r s g)) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) f a)
Case conversion may be inaccurate. Consider using '#align initial_seg.lt_or_eq_apply_left InitialSeg.ltOrEq_apply_leftₓ'. -/
theorem InitialSeg.ltOrEq_apply_left [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α) :
    g a = f a :=
  @InitialSeg.eq α β r s _ g f a
#align initial_seg.lt_or_eq_apply_left InitialSeg.ltOrEq_apply_left

/- warning: initial_seg.lt_or_eq_apply_right -> InitialSeg.ltOrEq_apply_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s) (g : RelIso.{u1, u2} α β r s) (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) g a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : InitialSeg.{u1, u2} α β r s) (g : RelIso.{u1, u2} α β r s) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s (RelIso.toRelEmbedding.{u1, u2} α β r s g)) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) f a)
Case conversion may be inaccurate. Consider using '#align initial_seg.lt_or_eq_apply_right InitialSeg.ltOrEq_apply_rightₓ'. -/
theorem InitialSeg.ltOrEq_apply_right [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α) :
    g a = f a :=
  InitialSeg.eq (InitialSeg.ofIso g) f a
#align initial_seg.lt_or_eq_apply_right InitialSeg.ltOrEq_apply_right

#print InitialSeg.leLT /-
/-- Composition of an initial segment taking values in a well order and a principal segment. -/
noncomputable def InitialSeg.leLT [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) :
    r ≺i t :=
  match f.lt_or_eq with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.equivLT f' g
#align initial_seg.le_lt InitialSeg.leLT
-/

/- warning: initial_seg.le_lt_apply -> InitialSeg.leLT_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsWellOrder.{u2} β s] [_inst_2 : IsTrans.{u3} γ t] (f : InitialSeg.{u1, u2} α β r s) (g : PrincipalSeg.{u2, u3} β γ s t) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (PrincipalSeg.{u1, u3} α γ r t) (fun (_x : PrincipalSeg.{u1, u3} α γ r t) => α -> γ) (PrincipalSeg.hasCoeToFun.{u1, u3} α γ r t) (InitialSeg.leLT.{u1, u2, u3} α β γ r s t _inst_1 _inst_2 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (PrincipalSeg.{u2, u3} β γ s t) (fun (_x : PrincipalSeg.{u2, u3} β γ s t) => β -> γ) (PrincipalSeg.hasCoeToFun.{u2, u3} β γ s t) g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) f a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [_inst_1 : IsWellOrder.{u3} β s] [_inst_2 : IsTrans.{u2} γ t] (f : InitialSeg.{u1, u3} α β r s) (g : PrincipalSeg.{u3, u2} β γ s t) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α γ) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α γ) α γ (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α γ)) (RelEmbedding.toEmbedding.{u1, u2} α γ r t (PrincipalSeg.toRelEmbedding.{u1, u2} α γ r t (InitialSeg.leLT.{u1, u3, u2} α β γ r s t _inst_1 _inst_2 f g))) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} β γ)) (RelEmbedding.toEmbedding.{u3, u2} β γ s t (PrincipalSeg.toRelEmbedding.{u3, u2} β γ s t g)) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (InitialSeg.{u1, u3} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u3), succ u1, succ u3} (InitialSeg.{u1, u3} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u3} α β r s)) f a))
Case conversion may be inaccurate. Consider using '#align initial_seg.le_lt_apply InitialSeg.leLT_applyₓ'. -/
@[simp]
theorem InitialSeg.leLT_apply [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) :
    (f.leLt g) a = g (f a) := by
  delta InitialSeg.leLT; cases' h : f.lt_or_eq with f' f'
  · simp only [PrincipalSeg.trans_apply, f.lt_or_eq_apply_left]
  · simp only [PrincipalSeg.equivLT_apply, f.lt_or_eq_apply_right]
#align initial_seg.le_lt_apply InitialSeg.leLT_apply

namespace RelEmbedding

/- warning: rel_embedding.collapse_F -> RelEmbedding.collapseF is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : RelEmbedding.{u1, u2} α β r s) (a : α), Subtype.{succ u2} β (fun (b : β) => Not (s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a) b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : RelEmbedding.{u1, u2} α β r s) (a : α), Subtype.{succ u2} β (fun (b : β) => Not (s (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s f) a) b))
Case conversion may be inaccurate. Consider using '#align rel_embedding.collapse_F RelEmbedding.collapseFₓ'. -/
/-- Given an order embedding into a well order, collapse the order embedding by filling the
gaps, to obtain an initial segment. Here, we construct the collapsed order embedding pointwise,
but the proof of the fact that it is an initial segment will be given in `collapse`. -/
noncomputable def collapseF [IsWellOrder β s] (f : r ↪r s) : ∀ a, { b // ¬s (f a) b } :=
  (RelEmbedding.wellFounded f <| IsWellFounded.wf).fix fun a IH =>
    by
    let S := { b | ∀ a h, s (IH a h).1 b }
    have : f a ∈ S := fun a' h =>
      ((trichotomous _ _).resolve_left fun h' =>
            (IH a' h).2 <| trans (f.map_rel_iff.2 h) h').resolve_left
        fun h' => (IH a' h).2 <| h' ▸ f.map_rel_iff.2 h
    exact ⟨is_well_founded.wf.min S ⟨_, this⟩, is_well_founded.wf.not_lt_min _ _ this⟩
#align rel_embedding.collapse_F RelEmbedding.collapseF

#print RelEmbedding.collapseF.lt /-
theorem collapseF.lt [IsWellOrder β s] (f : r ↪r s) {a : α} :
    ∀ {a'}, r a' a → s (collapseF f a').1 (collapseF f a).1 :=
  show (collapseF f a).1 ∈ { b | ∀ (a') (h : r a' a), s (collapseF f a').1 b }
    by
    unfold collapse_F; rw [WellFounded.fix_eq]
    apply WellFounded.min_mem _ _
#align rel_embedding.collapse_F.lt RelEmbedding.collapseF.lt
-/

#print RelEmbedding.collapseF.not_lt /-
theorem collapseF.not_lt [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
    (h : ∀ (a') (h : r a' a), s (collapseF f a').1 b) : ¬s b (collapseF f a).1 :=
  by
  unfold collapse_F; rw [WellFounded.fix_eq]
  exact
    WellFounded.not_lt_min _ _ _
      (show b ∈ { b | ∀ (a') (h : r a' a), s (collapse_F f a').1 b } from h)
#align rel_embedding.collapse_F.not_lt RelEmbedding.collapseF.not_lt
-/

#print RelEmbedding.collapse /-
/-- Construct an initial segment from an order embedding into a well order, by collapsing it
to fill the gaps. -/
noncomputable def collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s :=
  haveI := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone (fun a => (collapse_F f a).1) fun a b => collapse_F.lt f, fun a b =>
    Acc.recOn (is_well_founded.wf.apply b : Acc s b)
      (fun b H IH a h => by
        let S := { a | ¬s (collapse_F f a).1 b }
        have : S.nonempty := ⟨_, asymm h⟩
        exists (IsWellFounded.wf : WellFounded r).min S this
        refine' ((@trichotomous _ s _ _ _).resolve_left _).resolve_right _
        · exact (IsWellFounded.wf : WellFounded r).min_mem S this
        · refine' collapse_F.not_lt f _ fun a' h' => _
          by_contra hn
          exact is_well_founded.wf.not_lt_min S this hn h')
      a⟩
#align rel_embedding.collapse RelEmbedding.collapse
-/

/- warning: rel_embedding.collapse_apply -> RelEmbedding.collapse_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : RelEmbedding.{u1, u2} α β r s) (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InitialSeg.{u1, u2} α β r s) (fun (_x : InitialSeg.{u1, u2} α β r s) => α -> β) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.embeddingLike.{u1, u2} α β r s))) (RelEmbedding.collapse.{u1, u2} α β r s _inst_1 f) a) (Subtype.val.{succ u2} β (fun (b : β) => Not (s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a) b)) (RelEmbedding.collapseF.{u1, u2} α β r s _inst_1 f a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u2} β s] (f : RelEmbedding.{u1, u2} α β r s) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (InitialSeg.{u1, u2} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u2} α β r s)) (RelEmbedding.collapse.{u1, u2} α β r s _inst_1 f) a) (Subtype.val.{succ u2} β (fun (b : β) => Not (s (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s f) a) b)) (RelEmbedding.collapseF.{u1, u2} α β r s _inst_1 f a))
Case conversion may be inaccurate. Consider using '#align rel_embedding.collapse_apply RelEmbedding.collapse_applyₓ'. -/
theorem collapse_apply [IsWellOrder β s] (f : r ↪r s) (a) : collapse f a = (collapseF f a).1 :=
  rfl
#align rel_embedding.collapse_apply RelEmbedding.collapse_apply

end RelEmbedding

