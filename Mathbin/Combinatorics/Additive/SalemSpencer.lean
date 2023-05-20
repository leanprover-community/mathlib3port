/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.additive.salem_spencer
! leanprover-community/mathlib commit acf5258c81d0bc7cb254ed026c1352e685df306c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Freiman
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Analysis.Convex.StrictConvexSpace

/-!
# Salem-Spencer sets and Roth numbers

This file defines Salem-Spencer sets and the Roth number of a set.

A Salem-Spencer set is a set without arithmetic progressions of length `3`. Equivalently, the
average of any two distinct elements is not in the set.

The Roth number of a finset is the size of its biggest Salem-Spencer subset. This is a more general
definition than the one often found in mathematical litterature, where the `n`-th Roth number is
the size of the biggest Salem-Spencer subset of `{0, ..., n - 1}`.

## Main declarations

* `mul_salem_spencer`: Predicate for a set to be multiplicative Salem-Spencer.
* `add_salem_spencer`: Predicate for a set to be additive Salem-Spencer.
* `mul_roth_number`: The multiplicative Roth number of a finset.
* `add_roth_number`: The additive Roth number of a finset.
* `roth_number_nat`: The Roth number of a natural. This corresponds to
  `add_roth_number (finset.range n)`.

## TODO

* Can `add_salem_spencer_iff_eq_right` be made more general?
* Generalize `mul_salem_spencer.image` to Freiman homs

## Tags

Salem-Spencer, Roth, arithmetic progression, average, three-free
-/


open Finset Function Metric Nat

open Pointwise

variable {F α β 𝕜 E : Type _}

section SalemSpencer

open Set

section Monoid

variable [Monoid α] [Monoid β] (s t : Set α)

#print MulSalemSpencer /-
/-- A multiplicative Salem-Spencer, aka non averaging, set `s` in a monoid is a set such that the
multiplicative average of any two distinct elements is not in the set. -/
@[to_additive
      "A Salem-Spencer, aka non averaging, set `s` in an additive monoid\nis a set such that the average of any two distinct elements is not in the set."]
def MulSalemSpencer : Prop :=
  ∀ ⦃a b c⦄, a ∈ s → b ∈ s → c ∈ s → a * b = c * c → a = b
#align mul_salem_spencer MulSalemSpencer
#align add_salem_spencer AddSalemSpencer
-/

/-- Whether a given finset is Salem-Spencer is decidable. -/
@[to_additive "Whether a given finset is Salem-Spencer is decidable."]
instance {α : Type _} [DecidableEq α] [Monoid α] {s : Finset α} :
    Decidable (MulSalemSpencer (s : Set α)) :=
  decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a * b = c * c → a = b)
    ⟨fun h a b c ha hb hc => h a ha b hb c hc, fun h a ha b hb c hc => h ha hb hc⟩

variable {s t}

#print MulSalemSpencer.mono /-
@[to_additive]
theorem MulSalemSpencer.mono (h : t ⊆ s) (hs : MulSalemSpencer s) : MulSalemSpencer t :=
  fun a b c ha hb hc => hs (h ha) (h hb) (h hc)
#align mul_salem_spencer.mono MulSalemSpencer.mono
#align add_salem_spencer.mono AddSalemSpencer.mono
-/

#print mulSalemSpencer_empty /-
@[simp, to_additive]
theorem mulSalemSpencer_empty : MulSalemSpencer (∅ : Set α) := fun a _ _ ha => ha.elim
#align mul_salem_spencer_empty mulSalemSpencer_empty
#align add_salem_spencer_empty addSalemSpencer_empty
-/

#print Set.Subsingleton.mulSalemSpencer /-
@[to_additive]
theorem Set.Subsingleton.mulSalemSpencer (hs : s.Subsingleton) : MulSalemSpencer s :=
  fun a b _ ha hb _ _ => hs ha hb
#align set.subsingleton.mul_salem_spencer Set.Subsingleton.mulSalemSpencer
#align set.subsingleton.add_salem_spencer Set.Subsingleton.addSalemSpencer
-/

#print mulSalemSpencer_singleton /-
@[simp, to_additive]
theorem mulSalemSpencer_singleton (a : α) : MulSalemSpencer ({a} : Set α) :=
  subsingleton_singleton.MulSalemSpencer
#align mul_salem_spencer_singleton mulSalemSpencer_singleton
#align add_salem_spencer_singleton addSalemSpencer_singleton
-/

/- warning: mul_salem_spencer.prod -> MulSalemSpencer.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (MulSalemSpencer.{u1} α _inst_1 s) -> (MulSalemSpencer.{u2} β _inst_2 t) -> (MulSalemSpencer.{max u1 u2} (Prod.{u1, u2} α β) (Prod.monoid.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (MulSalemSpencer.{u1} α _inst_1 s) -> (MulSalemSpencer.{u2} β _inst_2 t) -> (MulSalemSpencer.{max u2 u1} (Prod.{u1, u2} α β) (Prod.instMonoidProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer.prod MulSalemSpencer.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive AddSalemSpencer.prod]
theorem MulSalemSpencer.prod {t : Set β} (hs : MulSalemSpencer s) (ht : MulSalemSpencer t) :
    MulSalemSpencer (s ×ˢ t) := fun a b c ha hb hc h =>
  Prod.ext (hs ha.1 hb.1 hc.1 (Prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (Prod.ext_iff.1 h).2)
#align mul_salem_spencer.prod MulSalemSpencer.prod
#align add_salem_spencer.prod AddSalemSpencer.prod

/- warning: mul_salem_spencer_pi -> mulSalemSpencer_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_3 : forall (i : ι), Monoid.{u2} (α i)] {s : forall (i : ι), Set.{u2} (α i)}, (forall (i : ι), MulSalemSpencer.{u2} (α i) (_inst_3 i) (s i)) -> (MulSalemSpencer.{max u1 u2} (forall (i : ι), α i) (Pi.monoid.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) s))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_3 : forall (i : ι), Monoid.{u1} (α i)] {s : forall (i : ι), Set.{u1} (α i)}, (forall (i : ι), MulSalemSpencer.{u1} (α i) (_inst_3 i) (s i)) -> (MulSalemSpencer.{max u2 u1} (forall (i : ι), α i) (Pi.monoid.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) s))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer_pi mulSalemSpencer_piₓ'. -/
@[to_additive]
theorem mulSalemSpencer_pi {ι : Type _} {α : ι → Type _} [∀ i, Monoid (α i)] {s : ∀ i, Set (α i)}
    (hs : ∀ i, MulSalemSpencer (s i)) : MulSalemSpencer ((univ : Set ι).pi s) :=
  fun a b c ha hb hc h =>
  funext fun i => hs i (ha i trivial) (hb i trivial) (hc i trivial) <| congr_fun h i
#align mul_salem_spencer_pi mulSalemSpencer_pi
#align add_salem_spencer_pi addSalemSpencer_pi

end Monoid

section CommMonoid

variable [CommMonoid α] [CommMonoid β] {s : Set α} {a : α}

/- warning: mul_salem_spencer.of_image -> MulSalemSpencer.of_image is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u3} β] {s : Set.{u2} α} [_inst_3 : FunLike.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β)] [_inst_4 : FreimanHomClass.{u2, u1, u3} α F s β _inst_1 _inst_2 (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) _inst_3] (f : F), (Set.InjOn.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) _inst_3) f) s) -> (MulSalemSpencer.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2) (Set.image.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) _inst_3) f) s)) -> (MulSalemSpencer.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1) s)
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u1} β] {s : Set.{u2} α} [_inst_3 : FunLike.{succ u3, succ u2, succ u1} F α (fun (_x : α) => β)] [_inst_4 : FreimanHomClass.{u2, u3, u1} α F s β _inst_1 _inst_2 (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) _inst_3] (f : F), (Set.InjOn.{u2, u1} α β (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.694 : α) => β) _x) _inst_3 f) s) -> (MulSalemSpencer.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2) (Set.image.{u2, u1} α β (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.694 : α) => β) _x) _inst_3 f) s)) -> (MulSalemSpencer.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer.of_image MulSalemSpencer.of_imageₓ'. -/
@[to_additive]
theorem MulSalemSpencer.of_image [FunLike F α fun _ => β] [FreimanHomClass F s β 2] (f : F)
    (hf : s.InjOn f) (h : MulSalemSpencer (f '' s)) : MulSalemSpencer s :=
  fun a b c ha hb hc habc =>
  hf ha hb <|
    h (mem_image_of_mem _ ha) (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) <|
      map_mul_map_eq_map_mul_map f ha hb hc hc habc
#align mul_salem_spencer.of_image MulSalemSpencer.of_image
#align add_salem_spencer.of_image AddSalemSpencer.of_image

/- warning: mul_salem_spencer.image -> MulSalemSpencer.image is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u3} β] {s : Set.{u2} α} [_inst_3 : MulHomClass.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)))] (f : F), (Set.InjOn.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))) _inst_3)) f) (HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))))) s s)) -> (MulSalemSpencer.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1) s) -> (MulSalemSpencer.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2) (Set.image.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))) _inst_3)) f) s))
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u1} β] {s : Set.{u2} α} [_inst_3 : MulHomClass.{u3, u2, u1} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2)))] (f : F), (Set.InjOn.{u2, u1} α β (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u3, u2, u1} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) _inst_3) f) (HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))))) s s)) -> (MulSalemSpencer.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1) s) -> (MulSalemSpencer.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2) (Set.image.{u2, u1} α β (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u3, u2, u1} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) _inst_3) f) s))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer.image MulSalemSpencer.imageₓ'. -/
-- TODO: Generalize to Freiman homs
@[to_additive]
theorem MulSalemSpencer.image [MulHomClass F α β] (f : F) (hf : (s * s).InjOn f)
    (h : MulSalemSpencer s) : MulSalemSpencer (f '' s) :=
  by
  rintro _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ habc
  rw [h ha hb hc (hf (mul_mem_mul ha hb) (mul_mem_mul hc hc) <| by rwa [map_mul, map_mul])]
#align mul_salem_spencer.image MulSalemSpencer.image
#align add_salem_spencer.image AddSalemSpencer.image

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid α] {s : Set α} {a : α}

/- warning: mul_salem_spencer_insert -> mulSalemSpencer_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, Iff (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (And (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s) (And (forall {{b : α}} {{c : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) c c)) -> (Eq.{succ u1} α a b)) (forall {{b : α}} {{c : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) b c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) a a)) -> (Eq.{succ u1} α b c))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, Iff (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (And (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s) (And (forall {{b : α}} {{c : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) c s) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) c c)) -> (Eq.{succ u1} α a b)) (forall {{b : α}} {{c : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) c s) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) b c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) a a)) -> (Eq.{succ u1} α b c))))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer_insert mulSalemSpencer_insertₓ'. -/
@[to_additive]
theorem mulSalemSpencer_insert :
    MulSalemSpencer (insert a s) ↔
      MulSalemSpencer s ∧
        (∀ ⦃b c⦄, b ∈ s → c ∈ s → a * b = c * c → a = b) ∧
          ∀ ⦃b c⦄, b ∈ s → c ∈ s → b * c = a * a → b = c :=
  by
  refine'
    ⟨fun hs =>
      ⟨hs.mono (subset_insert _ _), fun b c hb hc => hs (Or.inl rfl) (Or.inr hb) (Or.inr hc),
        fun b c hb hc => hs (Or.inr hb) (Or.inr hc) (Or.inl rfl)⟩,
      _⟩
  rintro ⟨hs, ha, ha'⟩ b c d hb hc hd h
  rw [mem_insert_iff] at hb hc hd
  obtain rfl | hb := hb <;> obtain rfl | hc := hc
  · rfl
  all_goals obtain rfl | hd := hd
  · exact (mul_left_cancel h).symm
  · exact ha hc hd h
  · exact mul_right_cancel h
  · exact (ha hb hd <| (mul_comm _ _).trans h).symm
  · exact ha' hb hc h
  · exact hs hb hc hd h
#align mul_salem_spencer_insert mulSalemSpencer_insert
#align add_salem_spencer_insert addSalemSpencer_insert

#print mulSalemSpencer_pair /-
@[simp, to_additive]
theorem mulSalemSpencer_pair (a b : α) : MulSalemSpencer ({a, b} : Set α) :=
  by
  rw [mulSalemSpencer_insert]
  refine' ⟨mulSalemSpencer_singleton _, _, _⟩
  · rintro c d (rfl : c = b) (rfl : d = c)
    exact mul_right_cancel
  · rintro c d (rfl : c = b) (rfl : d = c) _
    rfl
#align mul_salem_spencer_pair mulSalemSpencer_pair
#align add_salem_spencer_pair addSalemSpencer_pair
-/

/- warning: mul_salem_spencer.mul_left -> MulSalemSpencer.mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s) -> (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Set.image.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) a) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s) -> (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Set.image.{u1, u1} α α ((fun (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.1366 : α) (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.1368 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.1366 x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.1368) a) s))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer.mul_left MulSalemSpencer.mul_leftₓ'. -/
@[to_additive]
theorem MulSalemSpencer.mul_left (hs : MulSalemSpencer s) : MulSalemSpencer ((· * ·) a '' s) :=
  by
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  rw [mul_mul_mul_comm, mul_mul_mul_comm a d] at h
  rw [hs hb hc hd (mul_left_cancel h)]
#align mul_salem_spencer.mul_left MulSalemSpencer.mul_left
#align add_salem_spencer.add_left AddSalemSpencer.add_left

/- warning: mul_salem_spencer.mul_right -> MulSalemSpencer.mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s) -> (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) _x a) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s) -> (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) _x a) s))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer.mul_right MulSalemSpencer.mul_rightₓ'. -/
@[to_additive]
theorem MulSalemSpencer.mul_right (hs : MulSalemSpencer s) : MulSalemSpencer ((· * a) '' s) :=
  by
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  rw [mul_mul_mul_comm, mul_mul_mul_comm d] at h
  rw [hs hb hc hd (mul_right_cancel h)]
#align mul_salem_spencer.mul_right MulSalemSpencer.mul_right
#align add_salem_spencer.add_right AddSalemSpencer.add_right

/- warning: mul_salem_spencer_mul_left_iff -> mulSalemSpencer_mul_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, Iff (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Set.image.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) a) s)) (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, Iff (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Set.image.{u1, u1} α α ((fun (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.1608 : α) (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.1610 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.1608 x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.1610) a) s)) (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s)
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer_mul_left_iff mulSalemSpencer_mul_left_iffₓ'. -/
@[to_additive]
theorem mulSalemSpencer_mul_left_iff : MulSalemSpencer ((· * ·) a '' s) ↔ MulSalemSpencer s :=
  ⟨fun hs b c d hb hc hd h =>
    mul_left_cancel
      (hs (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) (mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
    MulSalemSpencer.mul_left⟩
#align mul_salem_spencer_mul_left_iff mulSalemSpencer_mul_left_iff
#align add_salem_spencer_add_left_iff addSalemSpencer_add_left_iff

/- warning: mul_salem_spencer_mul_right_iff -> mulSalemSpencer_mul_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, Iff (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) _x a) s)) (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, Iff (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1)))))) _x a) s)) (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))) s)
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer_mul_right_iff mulSalemSpencer_mul_right_iffₓ'. -/
@[to_additive]
theorem mulSalemSpencer_mul_right_iff : MulSalemSpencer ((· * a) '' s) ↔ MulSalemSpencer s :=
  ⟨fun hs b c d hb hc hd h =>
    mul_right_cancel
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
    MulSalemSpencer.mul_right⟩
#align mul_salem_spencer_mul_right_iff mulSalemSpencer_mul_right_iff
#align add_salem_spencer_add_right_iff addSalemSpencer_add_right_iff

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {s : Set α} {a : α}

/- warning: mul_salem_spencer_insert_of_lt -> mulSalemSpencer_insert_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, (forall (i : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1))) i a)) -> (Iff (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (And (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))) s) (forall {{b : α}} {{c : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1))))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1))))))) c c)) -> (Eq.{succ u1} α a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α] {s : Set.{u1} α} {a : α}, (forall (i : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1))) i a)) -> (Iff (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (And (MulSalemSpencer.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))) s) (forall {{b : α}} {{c : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) c s) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1))))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1))))))) c c)) -> (Eq.{succ u1} α a b))))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer_insert_of_lt mulSalemSpencer_insert_of_ltₓ'. -/
@[to_additive]
theorem mulSalemSpencer_insert_of_lt (hs : ∀ i ∈ s, i < a) :
    MulSalemSpencer (insert a s) ↔
      MulSalemSpencer s ∧ ∀ ⦃b c⦄, b ∈ s → c ∈ s → a * b = c * c → a = b :=
  by
  refine' mul_salem_spencer_insert.trans _
  rw [← and_assoc']
  exact and_iff_left fun b c hb hc h => ((mul_lt_mul_of_lt_of_lt (hs _ hb) (hs _ hc)).Ne h).elim
#align mul_salem_spencer_insert_of_lt mulSalemSpencer_insert_of_lt
#align add_salem_spencer_insert_of_lt addSalemSpencer_insert_of_lt

end OrderedCancelCommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α] [NoZeroDivisors α] {s : Set α} {a : α}

/- warning: mul_salem_spencer.mul_left₀ -> MulSalemSpencer.mul_left₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))] {s : Set.{u1} α} {a : α}, (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s) -> (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (Set.image.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))] {s : Set.{u1} α} {a : α}, (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s) -> (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (Set.image.{u1, u1} α α ((fun (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.2012 : α) (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.2014 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.2012 x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.2014) a) s))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer.mul_left₀ MulSalemSpencer.mul_left₀ₓ'. -/
theorem MulSalemSpencer.mul_left₀ (hs : MulSalemSpencer s) (ha : a ≠ 0) :
    MulSalemSpencer ((· * ·) a '' s) :=
  by
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  rw [mul_mul_mul_comm, mul_mul_mul_comm a d] at h
  rw [hs hb hc hd (mul_left_cancel₀ (mul_ne_zero ha ha) h)]
#align mul_salem_spencer.mul_left₀ MulSalemSpencer.mul_left₀

/- warning: mul_salem_spencer.mul_right₀ -> MulSalemSpencer.mul_right₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))] {s : Set.{u1} α} {a : α}, (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s) -> (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) _x a) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))] {s : Set.{u1} α} {a : α}, (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s) -> (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) _x a) s))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer.mul_right₀ MulSalemSpencer.mul_right₀ₓ'. -/
theorem MulSalemSpencer.mul_right₀ (hs : MulSalemSpencer s) (ha : a ≠ 0) :
    MulSalemSpencer ((· * a) '' s) :=
  by
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  rw [mul_mul_mul_comm, mul_mul_mul_comm d] at h
  rw [hs hb hc hd (mul_right_cancel₀ (mul_ne_zero ha ha) h)]
#align mul_salem_spencer.mul_right₀ MulSalemSpencer.mul_right₀

/- warning: mul_salem_spencer_mul_left_iff₀ -> mulSalemSpencer_mul_left_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))] {s : Set.{u1} α} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (Iff (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (Set.image.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a) s)) (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))] {s : Set.{u1} α} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (Iff (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (Set.image.{u1, u1} α α ((fun (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.2278 : α) (x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.2280 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.2278 x._@.Mathlib.Combinatorics.Additive.SalemSpencer._hyg.2280) a) s)) (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer_mul_left_iff₀ mulSalemSpencer_mul_left_iff₀ₓ'. -/
theorem mulSalemSpencer_mul_left_iff₀ (ha : a ≠ 0) :
    MulSalemSpencer ((· * ·) a '' s) ↔ MulSalemSpencer s :=
  ⟨fun hs b c d hb hc hd h =>
    mul_left_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
    fun hs => hs.mulLeft₀ ha⟩
#align mul_salem_spencer_mul_left_iff₀ mulSalemSpencer_mul_left_iff₀

/- warning: mul_salem_spencer_mul_right_iff₀ -> mulSalemSpencer_mul_right_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))] {s : Set.{u1} α} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (Iff (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) _x a) s)) (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))] {s : Set.{u1} α} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (Iff (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) _x a) s)) (MulSalemSpencer.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s))
Case conversion may be inaccurate. Consider using '#align mul_salem_spencer_mul_right_iff₀ mulSalemSpencer_mul_right_iff₀ₓ'. -/
theorem mulSalemSpencer_mul_right_iff₀ (ha : a ≠ 0) :
    MulSalemSpencer ((· * a) '' s) ↔ MulSalemSpencer s :=
  ⟨fun hs b c d hb hc hd h =>
    mul_right_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
    fun hs => hs.mulRight₀ ha⟩
#align mul_salem_spencer_mul_right_iff₀ mulSalemSpencer_mul_right_iff₀

end CancelCommMonoidWithZero

section Nat

#print addSalemSpencer_iff_eq_right /-
theorem addSalemSpencer_iff_eq_right {s : Set ℕ} :
    AddSalemSpencer s ↔ ∀ ⦃a b c⦄, a ∈ s → b ∈ s → c ∈ s → a + b = c + c → a = c :=
  by
  refine' forall₄_congr fun a b c _ => forall₃_congr fun _ _ habc => ⟨_, _⟩
  · rintro rfl
    simp_rw [← two_mul] at habc
    exact mul_left_cancel₀ two_ne_zero habc
  · rintro rfl
    exact (add_left_cancel habc).symm
#align add_salem_spencer_iff_eq_right addSalemSpencer_iff_eq_right
-/

end Nat

/- warning: add_salem_spencer_frontier -> addSalemSpencer_frontier is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : TopologicalSpace.{u2} E] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_3] {s : Set.{u2} E}, (IsClosed.{u2} E _inst_2 s) -> (StrictConvex.{u1, u2} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))) _inst_2 _inst_3 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_3 _inst_4)))) s) -> (AddSalemSpencer.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3) (frontier.{u2} E _inst_2 s))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : TopologicalSpace.{u1} E] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : Module.{u2, u1} 𝕜 E (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1)))) _inst_3] {s : Set.{u1} E}, (IsClosed.{u1} E _inst_2 s) -> (StrictConvex.{u2, u1} 𝕜 E (OrderedCommSemiring.toOrderedSemiring.{u2} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 _inst_3 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1)))) _inst_3 _inst_4)))) s) -> (AddSalemSpencer.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3) (frontier.{u1} E _inst_2 s))
Case conversion may be inaccurate. Consider using '#align add_salem_spencer_frontier addSalemSpencer_frontierₓ'. -/
/-- The frontier of a closed strictly convex set only contains trivial arithmetic progressions.
The idea is that an arithmetic progression is contained on a line and the frontier of a strictly
convex set does not contain lines. -/
theorem addSalemSpencer_frontier [LinearOrderedField 𝕜] [TopologicalSpace E] [AddCommMonoid E]
    [Module 𝕜 E] {s : Set E} (hs₀ : IsClosed s) (hs₁ : StrictConvex 𝕜 s) :
    AddSalemSpencer (frontier s) := by
  intro a b c ha hb hc habc
  obtain rfl : (1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • b = c := by
    rwa [← smul_add, one_div, inv_smul_eq_iff₀ (show (2 : 𝕜) ≠ 0 by norm_num), two_smul]
  exact
    hs₁.eq (hs₀.frontier_subset ha) (hs₀.frontier_subset hb) one_half_pos one_half_pos
      (add_halves _) hc.2
#align add_salem_spencer_frontier addSalemSpencer_frontier

#print addSalemSpencer_sphere /-
theorem addSalemSpencer_sphere [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
    (x : E) (r : ℝ) : AddSalemSpencer (sphere x r) :=
  by
  obtain rfl | hr := eq_or_ne r 0
  · rw [sphere_zero]
    exact addSalemSpencer_singleton _
  · convert addSalemSpencer_frontier is_closed_ball (strictConvex_closedBall ℝ x r)
    exact (frontier_closedBall _ hr).symm
#align add_salem_spencer_sphere addSalemSpencer_sphere
-/

end SalemSpencer

open Finset

section RothNumber

variable [DecidableEq α]

section Monoid

variable [Monoid α] [DecidableEq β] [Monoid β] (s t : Finset α)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print mulRothNumber /-
/-- The multiplicative Roth number of a finset is the cardinality of its biggest multiplicative
Salem-Spencer subset. -/
@[to_additive
      "The additive Roth number of a finset is the cardinality of its biggest additive\nSalem-Spencer subset. The usual Roth number corresponds to `add_roth_number (finset.range n)`, see\n`roth_number_nat`. "]
def mulRothNumber : Finset α →o ℕ :=
  ⟨fun s =>
    Nat.findGreatest (fun m => ∃ (t : _)(_ : t ⊆ s), t.card = m ∧ MulSalemSpencer (t : Set α))
      s.card,
    by
    rintro t u htu
    refine' Nat.findGreatest_mono (fun m => _) (card_le_of_subset htu)
    rintro ⟨v, hvt, hv⟩
    exact ⟨v, hvt.trans htu, hv⟩⟩
#align mul_roth_number mulRothNumber
#align add_roth_number addRothNumber
-/

#print mulRothNumber_le /-
@[to_additive]
theorem mulRothNumber_le : mulRothNumber s ≤ s.card := by convert Nat.findGreatest_le s.card
#align mul_roth_number_le mulRothNumber_le
#align add_roth_number_le addRothNumber_le
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print mulRothNumber_spec /-
@[to_additive]
theorem mulRothNumber_spec :
    ∃ (t : _)(_ : t ⊆ s), t.card = mulRothNumber s ∧ MulSalemSpencer (t : Set α) :=
  @Nat.findGreatest_spec _ _
    (fun m => ∃ (t : _)(_ : t ⊆ s), t.card = m ∧ MulSalemSpencer (t : Set α)) _ (Nat.zero_le _)
    ⟨∅, empty_subset _, card_empty, mulSalemSpencer_empty⟩
#align mul_roth_number_spec mulRothNumber_spec
#align add_roth_number_spec addRothNumber_spec
-/

variable {s t} {n : ℕ}

#print MulSalemSpencer.le_mulRothNumber /-
@[to_additive]
theorem MulSalemSpencer.le_mulRothNumber (hs : MulSalemSpencer (s : Set α)) (h : s ⊆ t) :
    s.card ≤ mulRothNumber t :=
  le_findGreatest (card_le_of_subset h) ⟨s, h, rfl, hs⟩
#align mul_salem_spencer.le_mul_roth_number MulSalemSpencer.le_mulRothNumber
#align add_salem_spencer.le_add_roth_number AddSalemSpencer.le_addRothNumber
-/

#print MulSalemSpencer.roth_number_eq /-
@[to_additive]
theorem MulSalemSpencer.roth_number_eq (hs : MulSalemSpencer (s : Set α)) :
    mulRothNumber s = s.card :=
  (mulRothNumber_le _).antisymm <| hs.le_mulRothNumber <| Subset.refl _
#align mul_salem_spencer.roth_number_eq MulSalemSpencer.roth_number_eq
#align add_salem_spencer.roth_number_eq AddSalemSpencer.roth_number_eq
-/

#print mulRothNumber_empty /-
@[simp, to_additive]
theorem mulRothNumber_empty : mulRothNumber (∅ : Finset α) = 0 :=
  Nat.eq_zero_of_le_zero <| (mulRothNumber_le _).trans card_empty.le
#align mul_roth_number_empty mulRothNumber_empty
#align add_roth_number_empty addRothNumber_empty
-/

#print mulRothNumber_singleton /-
@[simp, to_additive]
theorem mulRothNumber_singleton (a : α) : mulRothNumber ({a} : Finset α) = 1 :=
  by
  convert MulSalemSpencer.roth_number_eq _
  rw [coe_singleton]
  exact mulSalemSpencer_singleton a
#align mul_roth_number_singleton mulRothNumber_singleton
#align add_roth_number_singleton addRothNumber_singleton
-/

#print mulRothNumber_union_le /-
@[to_additive]
theorem mulRothNumber_union_le (s t : Finset α) :
    mulRothNumber (s ∪ t) ≤ mulRothNumber s + mulRothNumber t :=
  let ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s ∪ t)
  calc
    mulRothNumber (s ∪ t) = u.card := hcard.symm
    _ = (u ∩ s ∪ u ∩ t).card := by rw [← inter_distrib_left, (inter_eq_left_iff_subset _ _).2 hus]
    _ ≤ (u ∩ s).card + (u ∩ t).card := (card_union_le _ _)
    _ ≤ mulRothNumber s + mulRothNumber t :=
      add_le_add ((hu.mono <| inter_subset_left _ _).le_mulRothNumber <| inter_subset_right _ _)
        ((hu.mono <| inter_subset_left _ _).le_mulRothNumber <| inter_subset_right _ _)
    
#align mul_roth_number_union_le mulRothNumber_union_le
#align add_roth_number_union_le addRothNumber_union_le
-/

/- warning: le_mul_roth_number_product -> le_mulRothNumber_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Monoid.{u1} α] [_inst_3 : DecidableEq.{succ u2} β] [_inst_4 : Monoid.{u2} β] (s : Finset.{u1} α) (t : Finset.{u2} β), LE.le.{0} Nat Nat.hasLe (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} (Finset.{u1} α) Nat (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (_x : OrderHom.{u1, 0} (Finset.{u1} α) Nat (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) => (Finset.{u1} α) -> Nat) (OrderHom.hasCoeToFun.{u1, 0} (Finset.{u1} α) Nat (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (mulRothNumber.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s) (coeFn.{succ u2, succ u2} (OrderHom.{u2, 0} (Finset.{u2} β) Nat (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (_x : OrderHom.{u2, 0} (Finset.{u2} β) Nat (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) => (Finset.{u2} β) -> Nat) (OrderHom.hasCoeToFun.{u2, 0} (Finset.{u2} β) Nat (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (mulRothNumber.{u2} β (fun (a : β) (b : β) => _inst_3 a b) _inst_4) t)) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (OrderHom.{max u1 u2, 0} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) Nat (PartialOrder.toPreorder.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (_x : OrderHom.{max u1 u2, 0} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) Nat (PartialOrder.toPreorder.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) => (Finset.{max u1 u2} (Prod.{u1, u2} α β)) -> Nat) (OrderHom.hasCoeToFun.{max u1 u2, 0} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) Nat (PartialOrder.toPreorder.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (mulRothNumber.{max u1 u2} (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.Lex.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_3 a b) a b) (Prod.monoid.{u1, u2} α β _inst_2 _inst_4)) (Finset.product.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Monoid.{u2} α] [_inst_3 : DecidableEq.{succ u1} β] [_inst_4 : Monoid.{u1} β] (s : Finset.{u2} α) (t : Finset.{u1} β), LE.le.{0} Nat instLENat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OrderHom.toFun.{u2, 0} (Finset.{u2} α) Nat (PartialOrder.toPreorder.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α)) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (mulRothNumber.{u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s) (OrderHom.toFun.{u1, 0} (Finset.{u1} β) Nat (PartialOrder.toPreorder.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β)) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (mulRothNumber.{u1} β (fun (a : β) (b : β) => _inst_3 a b) _inst_4) t)) (OrderHom.toFun.{max u1 u2, 0} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) Nat (PartialOrder.toPreorder.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u2, u1} α β))) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (mulRothNumber.{max u1 u2} (Prod.{u2, u1} α β) (fun (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β) => instDecidableEqProd.{u2, u1} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_3 a b) a b) (Prod.instMonoidProd.{u2, u1} α β _inst_2 _inst_4)) (Finset.product.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align le_mul_roth_number_product le_mulRothNumber_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem le_mulRothNumber_product (s : Finset α) (t : Finset β) :
    mulRothNumber s * mulRothNumber t ≤ mulRothNumber (s ×ˢ t) :=
  by
  obtain ⟨u, hus, hucard, hu⟩ := mulRothNumber_spec s
  obtain ⟨v, hvt, hvcard, hv⟩ := mulRothNumber_spec t
  rw [← hucard, ← hvcard, ← card_product]
  refine' MulSalemSpencer.le_mulRothNumber _ (product_subset_product hus hvt)
  rw [coe_product]
  exact hu.prod hv
#align le_mul_roth_number_product le_mulRothNumber_product
#align le_add_roth_number_product le_addRothNumber_product

#print mulRothNumber_lt_of_forall_not_mulSalemSpencer /-
@[to_additive]
theorem mulRothNumber_lt_of_forall_not_mulSalemSpencer
    (h : ∀ t ∈ powersetLen n s, ¬MulSalemSpencer ((t : Finset α) : Set α)) : mulRothNumber s < n :=
  by
  obtain ⟨t, hts, hcard, ht⟩ := mulRothNumber_spec s
  rw [← hcard, ← not_le]
  intro hn
  obtain ⟨u, hut, rfl⟩ := exists_smaller_set t n hn
  exact h _ (mem_powerset_len.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut)
#align mul_roth_number_lt_of_forall_not_mul_salem_spencer mulRothNumber_lt_of_forall_not_mulSalemSpencer
#align add_roth_number_lt_of_forall_not_add_salem_spencer addRothNumber_lt_of_forall_not_addSalemSpencer
-/

end Monoid

section CancelCommMonoid

variable [CancelCommMonoid α] (s : Finset α) (a : α)

#print mulRothNumber_map_mul_left /-
@[simp, to_additive]
theorem mulRothNumber_map_mul_left :
    mulRothNumber (s.map <| mulLeftEmbedding a) = mulRothNumber s :=
  by
  refine' le_antisymm _ _
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s.map <| mulLeftEmbedding a)
    rw [subset_map_iff] at hus
    obtain ⟨u, hus, rfl⟩ := hus
    rw [coe_map] at hu
    rw [← hcard, card_map]
    exact (mulSalemSpencer_mul_left_iff.1 hu).le_mulRothNumber hus
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec s
    have h : MulSalemSpencer (u.map <| mulLeftEmbedding a : Set α) :=
      by
      rw [coe_map]
      exact hu.mul_left
    convert h.le_mul_roth_number (map_subset_map.2 hus)
    rw [card_map, hcard]
#align mul_roth_number_map_mul_left mulRothNumber_map_mul_left
#align add_roth_number_map_add_left addRothNumber_map_add_left
-/

#print mulRothNumber_map_mul_right /-
@[simp, to_additive]
theorem mulRothNumber_map_mul_right :
    mulRothNumber (s.map <| mulRightEmbedding a) = mulRothNumber s := by
  rw [← mul_left_embedding_eq_mul_right_embedding, mulRothNumber_map_mul_left s a]
#align mul_roth_number_map_mul_right mulRothNumber_map_mul_right
#align add_roth_number_map_add_right addRothNumber_map_add_right
-/

end CancelCommMonoid

end RothNumber

section rothNumberNat

variable {s : Finset ℕ} {k n : ℕ}

#print rothNumberNat /-
/-- The Roth number of a natural `N` is the largest integer `m` for which there is a subset of
`range N` of size `m` with no arithmetic progression of length 3.
Trivially, `roth_number_nat N ≤ N`, but Roth's theorem (proved in 1953) shows that
`roth_number_nat N = o(N)` and the construction by Behrend gives a lower bound of the form
`N * exp(-C sqrt(log(N))) ≤ roth_number_nat N`.
A significant refinement of Roth's theorem by Bloom and Sisask announced in 2020 gives
`roth_number_nat N = O(N / (log N)^(1+c))` for an absolute constant `c`. -/
def rothNumberNat : ℕ →o ℕ :=
  ⟨fun n => addRothNumber (range n), addRothNumber.mono.comp range_mono⟩
#align roth_number_nat rothNumberNat
-/

#print rothNumberNat_def /-
theorem rothNumberNat_def (n : ℕ) : rothNumberNat n = addRothNumber (range n) :=
  rfl
#align roth_number_nat_def rothNumberNat_def
-/

#print rothNumberNat_le /-
theorem rothNumberNat_le (N : ℕ) : rothNumberNat N ≤ N :=
  (addRothNumber_le _).trans (card_range _).le
#align roth_number_nat_le rothNumberNat_le
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » range[finset.range] n) -/
#print rothNumberNat_spec /-
theorem rothNumberNat_spec (n : ℕ) :
    ∃ (t : _)(_ : t ⊆ range n), t.card = rothNumberNat n ∧ AddSalemSpencer (t : Set ℕ) :=
  addRothNumber_spec _
#align roth_number_nat_spec rothNumberNat_spec
-/

#print AddSalemSpencer.le_rothNumberNat /-
/-- A verbose specialization of `add_salem_spencer.le_add_roth_number`, sometimes convenient in
practice. -/
theorem AddSalemSpencer.le_rothNumberNat (s : Finset ℕ) (hs : AddSalemSpencer (s : Set ℕ))
    (hsn : ∀ x ∈ s, x < n) (hsk : s.card = k) : k ≤ rothNumberNat n :=
  hsk.ge.trans <| hs.le_addRothNumber fun x hx => mem_range.2 <| hsn x hx
#align add_salem_spencer.le_roth_number_nat AddSalemSpencer.le_rothNumberNat
-/

#print rothNumberNat_add_le /-
/-- The Roth number is a subadditive function. Note that by Fekete's lemma this shows that
the limit `roth_number_nat N / N` exists, but Roth's theorem gives the stronger result that this
limit is actually `0`. -/
theorem rothNumberNat_add_le (M N : ℕ) :
    rothNumberNat (M + N) ≤ rothNumberNat M + rothNumberNat N :=
  by
  simp_rw [rothNumberNat_def]
  rw [range_add_eq_union, ← addRothNumber_map_add_left (range N) M]
  exact addRothNumber_union_le _ _
#align roth_number_nat_add_le rothNumberNat_add_le
-/

#print rothNumberNat_zero /-
@[simp]
theorem rothNumberNat_zero : rothNumberNat 0 = 0 :=
  rfl
#align roth_number_nat_zero rothNumberNat_zero
-/

/- warning: add_roth_number_Ico -> addRothNumber_Ico is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (b : Nat), Eq.{1} Nat (coeFn.{1, 1} (OrderHom.{0, 0} (Finset.{0} Nat) Nat (PartialOrder.toPreorder.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (_x : OrderHom.{0, 0} (Finset.{0} Nat) Nat (PartialOrder.toPreorder.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) => (Finset.{0} Nat) -> Nat) (OrderHom.hasCoeToFun.{0, 0} (Finset.{0} Nat) Nat (PartialOrder.toPreorder.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (addRothNumber.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) Nat.addMonoid) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b)) (coeFn.{1, 1} (OrderHom.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (_x : OrderHom.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) => Nat -> Nat) (OrderHom.hasCoeToFun.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) rothNumberNat (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) b a))
but is expected to have type
  forall (a : Nat) (b : Nat), Eq.{1} Nat (OrderHom.toFun.{0, 0} (Finset.{0} Nat) Nat (PartialOrder.toPreorder.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat)) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (addRothNumber.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.addMonoid) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b)) (OrderHom.toFun.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) rothNumberNat (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) b a))
Case conversion may be inaccurate. Consider using '#align add_roth_number_Ico addRothNumber_Icoₓ'. -/
theorem addRothNumber_Ico (a b : ℕ) : addRothNumber (Ico a b) = rothNumberNat (b - a) :=
  by
  obtain h | h := le_total b a
  · rw [tsub_eq_zero_of_le h, Ico_eq_empty_of_le h, rothNumberNat_zero, addRothNumber_empty]
  convert addRothNumber_map_add_left _ a
  rw [range_eq_Ico, map_eq_image]
  convert(image_add_left_Ico 0 (b - a) _).symm
  exact (add_tsub_cancel_of_le h).symm
#align add_roth_number_Ico addRothNumber_Ico

open Asymptotics Filter

/- warning: roth_number_nat_is_O_with_id -> rothNumberNat_isBigOWith_id is a dubious translation:
lean 3 declaration is
  Asymptotics.IsBigOWith.{0, 0, 0} Nat Real Real Real.hasNorm Real.hasNorm (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (N : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (coeFn.{1, 1} (OrderHom.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (_x : OrderHom.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) => Nat -> Nat) (OrderHom.hasCoeToFun.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) rothNumberNat N)) (fun (N : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) N)
but is expected to have type
  Asymptotics.IsBigOWith.{0, 0, 0} Nat Real Real Real.norm Real.norm (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (fun (N : Nat) => Nat.cast.{0} Real Real.natCast (OrderHom.toFun.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) rothNumberNat N)) (fun (N : Nat) => Nat.cast.{0} Real Real.natCast N)
Case conversion may be inaccurate. Consider using '#align roth_number_nat_is_O_with_id rothNumberNat_isBigOWith_idₓ'. -/
theorem rothNumberNat_isBigOWith_id :
    IsBigOWith 1 atTop (fun N => (rothNumberNat N : ℝ)) fun N => (N : ℝ) :=
  isBigOWith_of_le _ <| by simpa only [Real.norm_coe_nat, Nat.cast_le] using rothNumberNat_le
#align roth_number_nat_is_O_with_id rothNumberNat_isBigOWith_id

/- warning: roth_number_nat_is_O_id -> rothNumberNat_isBigO_id is a dubious translation:
lean 3 declaration is
  Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (N : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (coeFn.{1, 1} (OrderHom.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (_x : OrderHom.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) => Nat -> Nat) (OrderHom.hasCoeToFun.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) rothNumberNat N)) (fun (N : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) N)
but is expected to have type
  Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (fun (N : Nat) => Nat.cast.{0} Real Real.natCast (OrderHom.toFun.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) rothNumberNat N)) (fun (N : Nat) => Nat.cast.{0} Real Real.natCast N)
Case conversion may be inaccurate. Consider using '#align roth_number_nat_is_O_id rothNumberNat_isBigO_idₓ'. -/
/-- The Roth number has the trivial bound `roth_number_nat N = O(N)`. -/
theorem rothNumberNat_isBigO_id : (fun N => (rothNumberNat N : ℝ)) =O[atTop] fun N => (N : ℝ) :=
  rothNumberNat_isBigOWith_id.IsBigO
#align roth_number_nat_is_O_id rothNumberNat_isBigO_id

end rothNumberNat

