/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module data.bundle
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic

/-!
# Bundle

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
Basic data structure to implement fiber bundles, vector bundles (maybe fibrations?), etc. This file
should contain all possible results that do not involve any topology.

We represent a bundle `E` over a base space `B` as a dependent type `E : B → Type*`.

We provide a type synonym of `Σ x, E x` as `bundle.total_space E`, to be able to endow it with
a topology which is not the disjoint union topology `sigma.topological_space`. In general, the
constructions of fiber bundles we will make will be of this form.

## Main Definitions

* `bundle.total_space` the total space of a bundle.
* `bundle.total_space.proj` the projection from the total space to the base space.
* `bundle.total_space_mk` the constructor for the total space.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/


namespace Bundle

variable {B : Type _} (E : B → Type _)

#print Bundle.TotalSpace /-
/-- `bundle.total_space E` is the total space of the bundle `Σ x, E x`.
This type synonym is used to avoid conflicts with general sigma types.
-/
def TotalSpace :=
  Σx, E x
#align bundle.total_space Bundle.TotalSpace
-/

instance [Inhabited B] [Inhabited (E default)] : Inhabited (TotalSpace E) :=
  ⟨⟨default, default⟩⟩

variable {E}

#print Bundle.TotalSpace.proj /-
/-- `bundle.total_space.proj` is the canonical projection `bundle.total_space E → B` from the
total space to the base space. -/
@[simp, reducible]
def TotalSpace.proj : TotalSpace E → B :=
  Sigma.fst
#align bundle.total_space.proj Bundle.TotalSpace.proj
-/

-- mathport name: exprπ
-- this notation won't be used in the pretty-printer
scoped notation "π" => @Bundle.TotalSpace.proj _

#print Bundle.totalSpaceMk /-
/-- Constructor for the total space of a bundle. -/
@[simp, reducible]
def totalSpaceMk (b : B) (a : E b) : Bundle.TotalSpace E :=
  ⟨b, a⟩
#align bundle.total_space_mk Bundle.totalSpaceMk
-/

/- warning: bundle.total_space.proj_mk -> Bundle.TotalSpace.proj_mk is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {E : B -> Type.{u2}} {x : B} {y : E x}, Eq.{succ u1} B (Bundle.TotalSpace.proj.{u1, u2} B (fun {x : B} => E x) (Bundle.totalSpaceMk.{u1, u2} B (fun {x : B} => E x) x y)) x
but is expected to have type
  forall {B : Type.{u2}} {E : B -> Type.{u1}} {x : B} {y : E x}, Eq.{succ u2} B (Bundle.TotalSpace.proj.{u2, u1} B E (Bundle.totalSpaceMk.{u2, u1} B E x y)) x
Case conversion may be inaccurate. Consider using '#align bundle.total_space.proj_mk Bundle.TotalSpace.proj_mkₓ'. -/
theorem TotalSpace.proj_mk {x : B} {y : E x} : (totalSpaceMk x y).proj = x :=
  rfl
#align bundle.total_space.proj_mk Bundle.TotalSpace.proj_mk

/- warning: bundle.sigma_mk_eq_total_space_mk -> Bundle.sigma_mk_eq_totalSpaceMk is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {E : B -> Type.{u2}} {x : B} {y : E x}, Eq.{max (succ u1) (succ u2)} (Sigma.{u1, u2} B (fun {x : B} => E x)) (Sigma.mk.{u1, u2} B (fun {x : B} => E x) x y) (Bundle.totalSpaceMk.{u1, u2} B (fun (x : B) => E x) x y)
but is expected to have type
  forall {B : Type.{u2}} {E : B -> Type.{u1}} {x : B} {y : E x}, Eq.{max (succ u2) (succ u1)} (Sigma.{u2, u1} B E) (Sigma.mk.{u2, u1} B E x y) (Bundle.totalSpaceMk.{u2, u1} B E x y)
Case conversion may be inaccurate. Consider using '#align bundle.sigma_mk_eq_total_space_mk Bundle.sigma_mk_eq_totalSpaceMkₓ'. -/
theorem sigma_mk_eq_totalSpaceMk {x : B} {y : E x} : Sigma.mk x y = totalSpaceMk x y :=
  rfl
#align bundle.sigma_mk_eq_total_space_mk Bundle.sigma_mk_eq_totalSpaceMk

/- warning: bundle.total_space.mk_cast -> Bundle.TotalSpace.mk_cast is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {E : B -> Type.{u2}} {x : B} {x' : B} (h : Eq.{succ u1} B x x') (b : E x), Eq.{max (succ u1) (succ u2)} (Bundle.TotalSpace.{u1, u2} B E) (Bundle.totalSpaceMk.{u1, u2} B E x' (cast.{succ u2} (E x) (E x') (congr_arg.{succ u1, succ (succ u2)} B Type.{u2} x x' E h) b)) (Bundle.totalSpaceMk.{u1, u2} B E x b)
but is expected to have type
  forall {B : Type.{u2}} {E : B -> Type.{u1}} {x : B} {x' : B} (h : Eq.{succ u2} B x x') (b : E x), Eq.{max (succ u2) (succ u1)} (Bundle.TotalSpace.{u2, u1} B E) (Bundle.totalSpaceMk.{u2, u1} B E x' (cast.{succ u1} (E x) (E x') (congr_arg.{succ u2, succ (succ u1)} B Type.{u1} x x' E h) b)) (Bundle.totalSpaceMk.{u2, u1} B E x b)
Case conversion may be inaccurate. Consider using '#align bundle.total_space.mk_cast Bundle.TotalSpace.mk_castₓ'. -/
theorem TotalSpace.mk_cast {x x' : B} (h : x = x') (b : E x) :
    totalSpaceMk x' (cast (congr_arg E h) b) = totalSpaceMk x b :=
  by
  subst h
  rfl
#align bundle.total_space.mk_cast Bundle.TotalSpace.mk_cast

/- warning: bundle.total_space.eta -> Bundle.TotalSpace.eta is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {E : B -> Type.{u2}} (z : Bundle.TotalSpace.{u1, u2} B E), Eq.{max (succ u1) (succ u2)} (Bundle.TotalSpace.{u1, u2} B E) (Bundle.totalSpaceMk.{u1, u2} B E (Bundle.TotalSpace.proj.{u1, u2} B E z) (Sigma.snd.{u1, u2} B (fun (x : B) => E x) z)) z
but is expected to have type
  forall {B : Type.{u2}} {E : B -> Type.{u1}} (z : Bundle.TotalSpace.{u2, u1} B E), Eq.{max (succ u2) (succ u1)} (Bundle.TotalSpace.{u2, u1} B E) (Bundle.totalSpaceMk.{u2, u1} B E (Bundle.TotalSpace.proj.{u2, u1} B E z) (Sigma.snd.{u2, u1} B (fun (x : B) => E x) z)) z
Case conversion may be inaccurate. Consider using '#align bundle.total_space.eta Bundle.TotalSpace.etaₓ'. -/
theorem TotalSpace.eta (z : TotalSpace E) : totalSpaceMk z.proj z.2 = z :=
  Sigma.eta z
#align bundle.total_space.eta Bundle.TotalSpace.eta

instance {x : B} : CoeTC (E x) (TotalSpace E) :=
  ⟨totalSpaceMk x⟩

/- warning: bundle.coe_fst -> Bundle.coe_fst is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {E : B -> Type.{u2}} (x : B) (v : E x), Eq.{succ u1} B (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) v)) x
but is expected to have type
  forall {B : Type.{u2}} {E : B -> Type.{u1}} (x : B) (v : E x), Eq.{succ u2} B (Sigma.fst.{u2, u1} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u1} B E x v)) x
Case conversion may be inaccurate. Consider using '#align bundle.coe_fst Bundle.coe_fstₓ'. -/
@[simp]
theorem coe_fst (x : B) (v : E x) : (v : TotalSpace E).fst = x :=
  rfl
#align bundle.coe_fst Bundle.coe_fst

#print Bundle.coe_snd /-
@[simp]
theorem coe_snd {x : B} {y : E x} : (y : TotalSpace E).snd = y :=
  rfl
#align bundle.coe_snd Bundle.coe_snd
-/

/- warning: bundle.to_total_space_coe clashes with [anonymous] -> [anonymous]
warning: bundle.to_total_space_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {E : B -> Type.{u2}} {x : B} (v : E x), Eq.{max (succ u1) (succ u2)} (Bundle.TotalSpace.{u1, u2} B E) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) v) (Bundle.totalSpaceMk.{u1, u2} B E x v)
but is expected to have type
  forall {B : Type.{u1}} {E : Type.{u2}}, (Nat -> B -> E) -> Nat -> (List.{u1} B) -> (List.{u2} E)
Case conversion may be inaccurate. Consider using '#align bundle.to_total_space_coe [anonymous]ₓ'. -/
theorem [anonymous] {x : B} (v : E x) : (v : TotalSpace E) = totalSpaceMk x v :=
  rfl
#align bundle.to_total_space_coe [anonymous]

-- mathport name: «expr ×ᵇ »
notation:100 -- notation for the direct sum of two bundles over the same base
E₁ " ×ᵇ " E₂ => fun x => E₁ x × E₂ x

#print Bundle.Trivial /-
/-- `bundle.trivial B F` is the trivial bundle over `B` of fiber `F`. -/
def Trivial (B : Type _) (F : Type _) : B → Type _ :=
  Function.const B F
#align bundle.trivial Bundle.Trivial
-/

instance {F : Type _} [Inhabited F] {b : B} : Inhabited (Bundle.Trivial B F b) :=
  ⟨(default : F)⟩

#print Bundle.Trivial.projSnd /-
/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def Trivial.projSnd (B : Type _) (F : Type _) : TotalSpace (Bundle.Trivial B F) → F :=
  Sigma.snd
#align bundle.trivial.proj_snd Bundle.Trivial.projSnd
-/

section Pullback

variable {B' : Type _}

#print Bundle.Pullback /-
/-- The pullback of a bundle `E` over a base `B` under a map `f : B' → B`, denoted by `pullback f E`
or `f *ᵖ E`,  is the bundle over `B'` whose fiber over `b'` is `E (f b')`. -/
@[nolint has_nonempty_instance]
def Pullback (f : B' → B) (E : B → Type _) := fun x => E (f x)
#align bundle.pullback Bundle.Pullback
-/

-- mathport name: «expr *ᵖ »
notation f " *ᵖ " E => Pullback f E

#print Bundle.pullbackTotalSpaceEmbedding /-
/-- Natural embedding of the total space of `f *ᵖ E` into `B' × total_space E`. -/
@[simp]
def pullbackTotalSpaceEmbedding (f : B' → B) : TotalSpace (f *ᵖ E) → B' × TotalSpace E := fun z =>
  (z.proj, totalSpaceMk (f z.proj) z.2)
#align bundle.pullback_total_space_embedding Bundle.pullbackTotalSpaceEmbedding
-/

#print Bundle.Pullback.lift /-
/-- The base map `f : B' → B` lifts to a canonical map on the total spaces. -/
def Pullback.lift (f : B' → B) : TotalSpace (f *ᵖ E) → TotalSpace E := fun z =>
  totalSpaceMk (f z.proj) z.2
#align bundle.pullback.lift Bundle.Pullback.lift
-/

#print Bundle.Pullback.proj_lift /-
@[simp]
theorem Pullback.proj_lift (f : B' → B) (x : TotalSpace (f *ᵖ E)) :
    (Pullback.lift f x).proj = f x.1 :=
  rfl
#align bundle.pullback.proj_lift Bundle.Pullback.proj_lift
-/

/- warning: bundle.pullback.lift_mk -> Bundle.Pullback.lift_mk is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {E : B -> Type.{u2}} {B' : Type.{u3}} (f : B' -> B) (x : B') (y : E (f x)), Eq.{max (succ u1) (succ u2)} (Bundle.TotalSpace.{u1, u2} B E) (Bundle.Pullback.lift.{u1, u2, u3} B E B' f (Bundle.totalSpaceMk.{u3, u2} B' (Bundle.Pullback.{u1, u3, u2} B B' f E) x y)) (Bundle.totalSpaceMk.{u1, u2} B E (f x) y)
but is expected to have type
  forall {B : Type.{u3}} {E : B -> Type.{u2}} {B' : Type.{u1}} (f : B' -> B) (x : B') (y : E (f x)), Eq.{max (succ u3) (succ u2)} (Bundle.TotalSpace.{u3, u2} B E) (Bundle.Pullback.lift.{u3, u2, u1} B E B' f (Bundle.totalSpaceMk.{u1, u2} B' (Bundle.Pullback.{u3, u1, u2} B B' f E) x y)) (Bundle.totalSpaceMk.{u3, u2} B E (f x) y)
Case conversion may be inaccurate. Consider using '#align bundle.pullback.lift_mk Bundle.Pullback.lift_mkₓ'. -/
@[simp]
theorem Pullback.lift_mk (f : B' → B) (x : B') (y : E (f x)) :
    Pullback.lift f (totalSpaceMk x y) = totalSpaceMk (f x) y :=
  rfl
#align bundle.pullback.lift_mk Bundle.Pullback.lift_mk

#print Bundle.pullbackTotalSpaceEmbedding_snd /-
theorem pullbackTotalSpaceEmbedding_snd (f : B' → B) (x : TotalSpace (f *ᵖ E)) :
    (pullbackTotalSpaceEmbedding f x).2 = Pullback.lift f x :=
  rfl
#align bundle.pullback_total_space_embedding_snd Bundle.pullbackTotalSpaceEmbedding_snd
-/

end Pullback

section FiberStructures

variable [∀ x, AddCommMonoid (E x)]

/- warning: bundle.coe_snd_map_apply -> Bundle.coe_snd_map_apply is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {E : B -> Type.{u2}} [_inst_1 : forall (x : B), AddCommMonoid.{u2} (E x)] (x : B) (v : E x) (w : E x), Eq.{succ u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))) (Sigma.snd.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w))) (HAdd.hAdd.{u2, u2, u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))) (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))) (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))) (instHAdd.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))) (AddZeroClass.toHasAdd.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))) (AddMonoid.toAddZeroClass.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))) (AddCommMonoid.toAddMonoid.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))) (_inst_1 (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toHasAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))))))) (Sigma.snd.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) v)) (Sigma.snd.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) w)))
but is expected to have type
  forall {B : Type.{u1}} {E : B -> Type.{u2}} [_inst_1 : forall (x : B), AddCommMonoid.{u2} (E x)] (x : B) (v : E x) (w : E x), Eq.{succ u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w)))) (Sigma.snd.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x (HAdd.hAdd.{u2, u2, u2} (E x) (E x) (E x) (instHAdd.{u2} (E x) (AddZeroClass.toAdd.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x))))) v w))) (HAdd.hAdd.{u2, u2, u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x v))) (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x w))) (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x v))) (instHAdd.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x v))) (AddZeroClass.toAdd.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x v))) (AddMonoid.toAddZeroClass.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x v))) (AddCommMonoid.toAddMonoid.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x v))) (_inst_1 (Sigma.fst.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x v))))))) (Sigma.snd.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x v)) (Sigma.snd.{u1, u2} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u1, u2} B E x w)))
Case conversion may be inaccurate. Consider using '#align bundle.coe_snd_map_apply Bundle.coe_snd_map_applyₓ'. -/
@[simp]
theorem coe_snd_map_apply (x : B) (v w : E x) :
    (↑(v + w) : TotalSpace E).snd = (v : TotalSpace E).snd + (w : TotalSpace E).snd :=
  rfl
#align bundle.coe_snd_map_apply Bundle.coe_snd_map_apply

variable (R : Type _) [Semiring R] [∀ x, Module R (E x)]

/- warning: bundle.coe_snd_map_smul -> Bundle.coe_snd_map_smul is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {E : B -> Type.{u2}} [_inst_1 : forall (x : B), AddCommMonoid.{u2} (E x)] (R : Type.{u3}) [_inst_2 : Semiring.{u3} R] [_inst_3 : forall (x : B), Module.{u3, u2} R (E x) _inst_2 (_inst_1 x)] (x : B) (r : R) (v : E x), Eq.{succ u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (Sigma.snd.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v))) (SMul.smul.{u3, u2} R (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (SMulZeroClass.toHasSmul.{u3, u2} R (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (AddZeroClass.toHasZero.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (AddMonoid.toAddZeroClass.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (AddCommMonoid.toAddMonoid.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (_inst_1 (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v))))))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (AddMonoid.toAddZeroClass.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (AddCommMonoid.toAddMonoid.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (_inst_1 (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v))))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (AddMonoid.toAddZeroClass.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (AddCommMonoid.toAddMonoid.{u2} (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (_inst_1 (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v))))))) (Module.toMulActionWithZero.{u3, u2} R (E (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) _inst_2 (_inst_1 (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))) (_inst_3 (Sigma.fst.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) (SMul.smul.{u3, u2} R (E x) (SMulZeroClass.toHasSmul.{u3, u2} R (E x) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (SMulWithZero.toSmulZeroClass.{u3, u2} R (E x) (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)))) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (MulActionWithZero.toSMulWithZero.{u3, u2} R (E x) (Semiring.toMonoidWithZero.{u3} R _inst_2) (AddZeroClass.toHasZero.{u2} (E x) (AddMonoid.toAddZeroClass.{u2} (E x) (AddCommMonoid.toAddMonoid.{u2} (E x) (_inst_1 x)))) (Module.toMulActionWithZero.{u3, u2} R (E x) _inst_2 (_inst_1 x) (_inst_3 x))))) r v)))))))) r (Sigma.snd.{u1, u2} B (fun (x : B) => E x) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) (E x) (Bundle.TotalSpace.{u1, u2} B E) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} (E x) (Bundle.TotalSpace.{u1, u2} B E) (Bundle.TotalSpace.hasCoeT.{u1, u2} B E x))) v)))
but is expected to have type
  forall {B : Type.{u2}} {E : B -> Type.{u3}} [_inst_1 : forall (x : B), AddCommMonoid.{u3} (E x)] (R : Type.{u1}) [_inst_2 : Semiring.{u1} R] [_inst_3 : forall (x : B), Module.{u1, u3} R (E x) _inst_2 (_inst_1 x)] (x : B) (r : R) (v : E x), Eq.{succ u3} (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x (HSMul.hSMul.{u1, u3, u3} R (E x) (E x) (instHSMul.{u1, u3} R (E x) (SMulZeroClass.toSMul.{u1, u3} R (E x) (AddMonoid.toZero.{u3} (E x) (AddCommMonoid.toAddMonoid.{u3} (E x) (_inst_1 x))) (SMulWithZero.toSMulZeroClass.{u1, u3} R (E x) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_2)) (AddMonoid.toZero.{u3} (E x) (AddCommMonoid.toAddMonoid.{u3} (E x) (_inst_1 x))) (MulActionWithZero.toSMulWithZero.{u1, u3} R (E x) (Semiring.toMonoidWithZero.{u1} R _inst_2) (AddMonoid.toZero.{u3} (E x) (AddCommMonoid.toAddMonoid.{u3} (E x) (_inst_1 x))) (Module.toMulActionWithZero.{u1, u3} R (E x) _inst_2 (_inst_1 x) (_inst_3 x)))))) r v)))) (Sigma.snd.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x (HSMul.hSMul.{u1, u3, u3} R (E x) (E x) (instHSMul.{u1, u3} R (E x) (SMulZeroClass.toSMul.{u1, u3} R (E x) (AddMonoid.toZero.{u3} (E x) (AddCommMonoid.toAddMonoid.{u3} (E x) (_inst_1 x))) (SMulWithZero.toSMulZeroClass.{u1, u3} R (E x) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_2)) (AddMonoid.toZero.{u3} (E x) (AddCommMonoid.toAddMonoid.{u3} (E x) (_inst_1 x))) (MulActionWithZero.toSMulWithZero.{u1, u3} R (E x) (Semiring.toMonoidWithZero.{u1} R _inst_2) (AddMonoid.toZero.{u3} (E x) (AddCommMonoid.toAddMonoid.{u3} (E x) (_inst_1 x))) (Module.toMulActionWithZero.{u1, u3} R (E x) _inst_2 (_inst_1 x) (_inst_3 x)))))) r v))) (HSMul.hSMul.{u1, u3, u3} R (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (instHSMul.{u1, u3} R (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (SMulZeroClass.toSMul.{u1, u3} R (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (AddMonoid.toZero.{u3} (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (AddCommMonoid.toAddMonoid.{u3} (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (_inst_1 (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))))) (SMulWithZero.toSMulZeroClass.{u1, u3} R (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_2)) (AddMonoid.toZero.{u3} (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (AddCommMonoid.toAddMonoid.{u3} (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (_inst_1 (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))))) (MulActionWithZero.toSMulWithZero.{u1, u3} R (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (Semiring.toMonoidWithZero.{u1} R _inst_2) (AddMonoid.toZero.{u3} (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (AddCommMonoid.toAddMonoid.{u3} (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (_inst_1 (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))))) (Module.toMulActionWithZero.{u1, u3} R (E (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) _inst_2 (_inst_1 (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v))) (_inst_3 (Sigma.fst.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v)))))))) r (Sigma.snd.{u2, u3} B (fun (x : B) => E x) (Bundle.totalSpaceMk.{u2, u3} B E x v)))
Case conversion may be inaccurate. Consider using '#align bundle.coe_snd_map_smul Bundle.coe_snd_map_smulₓ'. -/
@[simp]
theorem coe_snd_map_smul (x : B) (r : R) (v : E x) :
    (↑(r • v) : TotalSpace E).snd = r • (v : TotalSpace E).snd :=
  rfl
#align bundle.coe_snd_map_smul Bundle.coe_snd_map_smul

end FiberStructures

section TrivialInstances

variable {F : Type _} {R : Type _} [Semiring R] (b : B)

instance [AddCommMonoid F] : AddCommMonoid (Bundle.Trivial B F b) :=
  ‹AddCommMonoid F›

instance [AddCommGroup F] : AddCommGroup (Bundle.Trivial B F b) :=
  ‹AddCommGroup F›

instance [AddCommMonoid F] [Module R F] : Module R (Bundle.Trivial B F b) :=
  ‹Module R F›

end TrivialInstances

end Bundle

