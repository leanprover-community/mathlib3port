/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.hom.group_action
! leanprover-community/mathlib commit e04043d6bf7264a3c84bc69711dc354958ca4516
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.Algebra.Module.Basic

/-!
# Equivariant homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `mul_action_hom M X Y`, the type of equivariant functions from `X` to `Y`, where `M` is a monoid
  that acts on the types `X` and `Y`.
* `distrib_mul_action_hom M A B`, the type of equivariant additive monoid homomorphisms
  from `A` to `B`, where `M` is a monoid that acts on the additive monoids `A` and `B`.
* `mul_semiring_action_hom M R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `M` is a monoid that acts on the rings `R` and `S`.

The above types have corresponding classes:
* `smul_hom_class F M X Y` states that `F` is a type of bundled `X → Y` homs
  preserving scalar multiplication by `M`
* `distrib_mul_action_hom_class F M A B` states that `F` is a type of bundled `A → B` homs
  preserving the additive monoid structure and scalar multiplication by `M`
* `mul_semiring_action_hom_class F M R S` states that `F` is a type of bundled `R → S` homs
  preserving the ring structure and scalar multiplication by `M`

## Notations

* `X →[M] Y` is `mul_action_hom M X Y`.
* `A →+[M] B` is `distrib_mul_action_hom M A B`.
* `R →+*[M] S` is `mul_semiring_action_hom M R S`.

-/


assert_not_exists Submonoid

variable (M' : Type _)

variable (X : Type _) [SMul M' X]

variable (Y : Type _) [SMul M' Y]

variable (Z : Type _) [SMul M' Z]

variable (M : Type _) [Monoid M]

variable (A : Type _) [AddMonoid A] [DistribMulAction M A]

variable (A' : Type _) [AddGroup A'] [DistribMulAction M A']

variable (B : Type _) [AddMonoid B] [DistribMulAction M B]

variable (B' : Type _) [AddGroup B'] [DistribMulAction M B']

variable (C : Type _) [AddMonoid C] [DistribMulAction M C]

variable (R : Type _) [Semiring R] [MulSemiringAction M R]

variable (R' : Type _) [Ring R'] [MulSemiringAction M R']

variable (S : Type _) [Semiring S] [MulSemiringAction M S]

variable (S' : Type _) [Ring S'] [MulSemiringAction M S']

variable (T : Type _) [Semiring T] [MulSemiringAction M T]

#print MulActionHom /-
/-- Equivariant functions. -/
@[nolint has_nonempty_instance]
structure MulActionHom where
  toFun : X → Y
  map_smul' : ∀ (m : M') (x : X), to_fun (m • x) = m • to_fun x
#align mul_action_hom MulActionHom
-/

-- mathport name: mul_action_hom
notation:25 X " →[" M:25 "] " Y:0 => MulActionHom M X Y

#print SMulHomClass /-
/-- `smul_hom_class F M X Y` states that `F` is a type of morphisms preserving
scalar multiplication by `M`.

You should extend this class when you extend `mul_action_hom`. -/
class SMulHomClass (F : Type _) (M X Y : outParam <| Type _) [SMul M X] [SMul M Y] extends
  FunLike F X fun _ => Y where
  map_smul : ∀ (f : F) (c : M) (x : X), f (c • x) = c • f x
#align smul_hom_class SMulHomClass
-/

-- `M` becomes a metavariable but it's an `out_param` so it's not a problem.
attribute [nolint dangerous_instance] SMulHomClass.toFunLike

export SMulHomClass (map_smul)

attribute [simp] map_smul

namespace MulActionHom

instance : CoeFun (X →[M'] Y) fun _ => X → Y :=
  ⟨MulActionHom.toFun⟩

instance : SMulHomClass (X →[M'] Y) M' X Y
    where
  coe := MulActionHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_smul := MulActionHom.map_smul'

variable {M M' X Y}

/- warning: mul_action_hom.map_smul -> MulActionHom.map_smul is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {X : Type.{u2}} [_inst_1 : SMul.{u1, u2} M' X] {Y : Type.{u3}} [_inst_2 : SMul.{u1, u3} M' Y] (f : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (m : M') (x : X), Eq.{succ u3} Y (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (fun (_x : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) => X -> Y) ([anonymous].{u1, u2, u3} M' X _inst_1 Y _inst_2) f (SMul.smul.{u1, u2} M' X _inst_1 m x)) (SMul.smul.{u1, u3} M' Y _inst_2 m (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (fun (_x : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) => X -> Y) ([anonymous].{u1, u2, u3} M' X _inst_1 Y _inst_2) f x))
but is expected to have type
  forall {M' : Type.{u3}} {X : Type.{u2}} [_inst_1 : SMul.{u3, u2} M' X] {Y : Type.{u1}} [_inst_2 : SMul.{u3, u1} M' Y] (f : MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) (m : M') (x : X), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) (HSMul.hSMul.{u3, u2, u2} M' X X (instHSMul.{u3, u2} M' X _inst_1) m x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) _x) (SMulHomClass.toFunLike.{max u2 u1, u3, u2, u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) M' X Y _inst_1 _inst_2 (instSMulHomClassMulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2)) f (HSMul.hSMul.{u3, u2, u2} M' X X (instHSMul.{u3, u2} M' X _inst_1) m x)) (HSMul.hSMul.{u3, u1, u1} M' ((fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) x) ((fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) x) (instHSMul.{u3, u1} M' ((fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) x) _inst_2) m (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) _x) (SMulHomClass.toFunLike.{max u2 u1, u3, u2, u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) M' X Y _inst_1 _inst_2 (instSMulHomClassMulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2)) f x))
Case conversion may be inaccurate. Consider using '#align mul_action_hom.map_smul MulActionHom.map_smulₓ'. -/
protected theorem map_smul (f : X →[M'] Y) (m : M') (x : X) : f (m • x) = m • f x :=
  map_smul _ _ _
#align mul_action_hom.map_smul MulActionHom.map_smul

/- warning: mul_action_hom.ext -> MulActionHom.ext is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {X : Type.{u2}} [_inst_1 : SMul.{u1, u2} M' X] {Y : Type.{u3}} [_inst_2 : SMul.{u1, u3} M' Y] {f : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2} {g : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2}, (forall (x : X), Eq.{succ u3} Y (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (fun (_x : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) => X -> Y) ([anonymous].{u1, u2, u3} M' X _inst_1 Y _inst_2) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (fun (_x : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) => X -> Y) ([anonymous].{u1, u2, u3} M' X _inst_1 Y _inst_2) g x)) -> (Eq.{max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) f g)
but is expected to have type
  forall {M' : Type.{u3}} {X : Type.{u2}} [_inst_1 : SMul.{u3, u2} M' X] {Y : Type.{u1}} [_inst_2 : SMul.{u3, u1} M' Y] {f : MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2} {g : MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2}, (forall (x : X), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) _x) (SMulHomClass.toFunLike.{max u2 u1, u3, u2, u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) M' X Y _inst_1 _inst_2 (instSMulHomClassMulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) _x) (SMulHomClass.toFunLike.{max u2 u1, u3, u2, u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) M' X Y _inst_1 _inst_2 (instSMulHomClassMulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2)) g x)) -> (Eq.{max (succ u2) (succ u1)} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align mul_action_hom.ext MulActionHom.extₓ'. -/
@[ext]
theorem ext : ∀ {f g : X →[M'] Y}, (∀ x, f x = g x) → f = g :=
  FunLike.ext
#align mul_action_hom.ext MulActionHom.ext

/- warning: mul_action_hom.ext_iff -> MulActionHom.ext_iff is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {X : Type.{u2}} [_inst_1 : SMul.{u1, u2} M' X] {Y : Type.{u3}} [_inst_2 : SMul.{u1, u3} M' Y] {f : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2} {g : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2}, Iff (Eq.{max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) f g) (forall (x : X), Eq.{succ u3} Y (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (fun (_x : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) => X -> Y) ([anonymous].{u1, u2, u3} M' X _inst_1 Y _inst_2) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (fun (_x : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) => X -> Y) ([anonymous].{u1, u2, u3} M' X _inst_1 Y _inst_2) g x))
but is expected to have type
  forall {M' : Type.{u3}} {X : Type.{u2}} [_inst_1 : SMul.{u3, u2} M' X] {Y : Type.{u1}} [_inst_2 : SMul.{u3, u1} M' Y] {f : MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2} {g : MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) f g) (forall (x : X), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) _x) (SMulHomClass.toFunLike.{max u2 u1, u3, u2, u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) M' X Y _inst_1 _inst_2 (instSMulHomClassMulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) _x) (SMulHomClass.toFunLike.{max u2 u1, u3, u2, u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) M' X Y _inst_1 _inst_2 (instSMulHomClassMulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align mul_action_hom.ext_iff MulActionHom.ext_iffₓ'. -/
theorem ext_iff {f g : X →[M'] Y} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_action_hom.ext_iff MulActionHom.ext_iff

/- warning: mul_action_hom.congr_fun -> MulActionHom.congr_fun is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {X : Type.{u2}} [_inst_1 : SMul.{u1, u2} M' X] {Y : Type.{u3}} [_inst_2 : SMul.{u1, u3} M' Y] {f : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2} {g : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2}, (Eq.{max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) f g) -> (forall (x : X), Eq.{succ u3} Y (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (fun (_x : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) => X -> Y) ([anonymous].{u1, u2, u3} M' X _inst_1 Y _inst_2) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (fun (_x : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) => X -> Y) ([anonymous].{u1, u2, u3} M' X _inst_1 Y _inst_2) g x))
but is expected to have type
  forall {M' : Type.{u3}} {X : Type.{u2}} [_inst_1 : SMul.{u3, u2} M' X] {Y : Type.{u1}} [_inst_2 : SMul.{u3, u1} M' Y] {f : MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2} {g : MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2}, (Eq.{max (succ u2) (succ u1)} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) f g) -> (forall (x : X), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) _x) (SMulHomClass.toFunLike.{max u2 u1, u3, u2, u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) M' X Y _inst_1 _inst_2 (instSMulHomClassMulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) _x) (SMulHomClass.toFunLike.{max u2 u1, u3, u2, u1} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) M' X Y _inst_1 _inst_2 (instSMulHomClassMulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align mul_action_hom.congr_fun MulActionHom.congr_funₓ'. -/
protected theorem congr_fun {f g : X →[M'] Y} (h : f = g) (x : X) : f x = g x :=
  FunLike.congr_fun h _
#align mul_action_hom.congr_fun MulActionHom.congr_fun

variable (M M') {X}

#print MulActionHom.id /-
/-- The identity map as an equivariant map. -/
protected def id : X →[M'] X :=
  ⟨id, fun _ _ => rfl⟩
#align mul_action_hom.id MulActionHom.id
-/

#print MulActionHom.id_apply /-
@[simp]
theorem id_apply (x : X) : MulActionHom.id M' x = x :=
  rfl
#align mul_action_hom.id_apply MulActionHom.id_apply
-/

variable {M M' X Y Z}

#print MulActionHom.comp /-
/-- Composition of two equivariant maps. -/
def comp (g : Y →[M'] Z) (f : X →[M'] Y) : X →[M'] Z :=
  ⟨g ∘ f, fun m x =>
    calc
      g (f (m • x)) = g (m • f x) := by rw [f.map_smul]
      _ = m • g (f x) := g.map_smul _ _
      ⟩
#align mul_action_hom.comp MulActionHom.comp
-/

/- warning: mul_action_hom.comp_apply -> MulActionHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {X : Type.{u2}} [_inst_1 : SMul.{u1, u2} M' X] {Y : Type.{u3}} [_inst_2 : SMul.{u1, u3} M' Y] {Z : Type.{u4}} [_inst_3 : SMul.{u1, u4} M' Z] (g : MulActionHom.{u1, u3, u4} M' Y _inst_2 Z _inst_3) (f : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (x : X), Eq.{succ u4} Z (coeFn.{max (succ u2) (succ u4), max (succ u2) (succ u4)} (MulActionHom.{u1, u2, u4} M' X _inst_1 Z _inst_3) (fun (_x : MulActionHom.{u1, u2, u4} M' X _inst_1 Z _inst_3) => X -> Z) ([anonymous].{u1, u2, u4} M' X _inst_1 Z _inst_3) (MulActionHom.comp.{u1, u2, u3, u4} M' X _inst_1 Y _inst_2 Z _inst_3 g f) x) (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (MulActionHom.{u1, u3, u4} M' Y _inst_2 Z _inst_3) (fun (_x : MulActionHom.{u1, u3, u4} M' Y _inst_2 Z _inst_3) => Y -> Z) ([anonymous].{u1, u3, u4} M' Y _inst_2 Z _inst_3) g (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (fun (_x : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) => X -> Y) ([anonymous].{u1, u2, u3} M' X _inst_1 Y _inst_2) f x))
but is expected to have type
  forall {M' : Type.{u4}} {X : Type.{u1}} [_inst_1 : SMul.{u4, u1} M' X] {Y : Type.{u3}} [_inst_2 : SMul.{u4, u3} M' Y] {Z : Type.{u2}} [_inst_3 : SMul.{u4, u2} M' Z] (g : MulActionHom.{u4, u3, u2} M' Y _inst_2 Z _inst_3) (f : MulActionHom.{u4, u1, u3} M' X _inst_1 Y _inst_2) (x : X), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Z) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulActionHom.{u4, u1, u2} M' X _inst_1 Z _inst_3) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Z) _x) (SMulHomClass.toFunLike.{max u1 u2, u4, u1, u2} (MulActionHom.{u4, u1, u2} M' X _inst_1 Z _inst_3) M' X Z _inst_1 _inst_3 (instSMulHomClassMulActionHom.{u4, u1, u2} M' X _inst_1 Z _inst_3)) (MulActionHom.comp.{u4, u1, u3, u2} M' X _inst_1 Y _inst_2 Z _inst_3 g f) x) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulActionHom.{u4, u3, u2} M' Y _inst_2 Z _inst_3) Y (fun (_x : Y) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : Y) => Z) _x) (SMulHomClass.toFunLike.{max u3 u2, u4, u3, u2} (MulActionHom.{u4, u3, u2} M' Y _inst_2 Z _inst_3) M' Y Z _inst_2 _inst_3 (instSMulHomClassMulActionHom.{u4, u3, u2} M' Y _inst_2 Z _inst_3)) g (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MulActionHom.{u4, u1, u3} M' X _inst_1 Y _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2187 : X) => Y) _x) (SMulHomClass.toFunLike.{max u1 u3, u4, u1, u3} (MulActionHom.{u4, u1, u3} M' X _inst_1 Y _inst_2) M' X Y _inst_1 _inst_2 (instSMulHomClassMulActionHom.{u4, u1, u3} M' X _inst_1 Y _inst_2)) f x))
Case conversion may be inaccurate. Consider using '#align mul_action_hom.comp_apply MulActionHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (g : Y →[M'] Z) (f : X →[M'] Y) (x : X) : g.comp f x = g (f x) :=
  rfl
#align mul_action_hom.comp_apply MulActionHom.comp_apply

/- warning: mul_action_hom.id_comp -> MulActionHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {X : Type.{u2}} [_inst_1 : SMul.{u1, u2} M' X] {Y : Type.{u3}} [_inst_2 : SMul.{u1, u3} M' Y] (f : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2), Eq.{max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (MulActionHom.comp.{u1, u2, u3, u3} M' X _inst_1 Y _inst_2 Y _inst_2 (MulActionHom.id.{u1, u3} M' Y _inst_2) f) f
but is expected to have type
  forall {M' : Type.{u3}} {X : Type.{u2}} [_inst_1 : SMul.{u3, u2} M' X] {Y : Type.{u1}} [_inst_2 : SMul.{u3, u1} M' Y] (f : MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2), Eq.{max (succ u2) (succ u1)} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) (MulActionHom.comp.{u3, u2, u1, u1} M' X _inst_1 Y _inst_2 Y _inst_2 (MulActionHom.id.{u3, u1} M' Y _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align mul_action_hom.id_comp MulActionHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : X →[M'] Y) : (MulActionHom.id M').comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align mul_action_hom.id_comp MulActionHom.id_comp

/- warning: mul_action_hom.comp_id -> MulActionHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {X : Type.{u2}} [_inst_1 : SMul.{u1, u2} M' X] {Y : Type.{u3}} [_inst_2 : SMul.{u1, u3} M' Y] (f : MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2), Eq.{max (succ u2) (succ u3)} (MulActionHom.{u1, u2, u3} M' X _inst_1 Y _inst_2) (MulActionHom.comp.{u1, u2, u2, u3} M' X _inst_1 X _inst_1 Y _inst_2 f (MulActionHom.id.{u1, u2} M' X _inst_1)) f
but is expected to have type
  forall {M' : Type.{u3}} {X : Type.{u2}} [_inst_1 : SMul.{u3, u2} M' X] {Y : Type.{u1}} [_inst_2 : SMul.{u3, u1} M' Y] (f : MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2), Eq.{max (succ u2) (succ u1)} (MulActionHom.{u3, u2, u1} M' X _inst_1 Y _inst_2) (MulActionHom.comp.{u3, u2, u2, u1} M' X _inst_1 X _inst_1 Y _inst_2 f (MulActionHom.id.{u3, u2} M' X _inst_1)) f
Case conversion may be inaccurate. Consider using '#align mul_action_hom.comp_id MulActionHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : X →[M'] Y) : f.comp (MulActionHom.id M') = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align mul_action_hom.comp_id MulActionHom.comp_id

variable {A B}

/- warning: mul_action_hom.inverse -> MulActionHom.inverse is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_action_hom.inverse MulActionHom.inverseₓ'. -/
/-- The inverse of a bijective equivariant map is equivariant. -/
@[simps]
def inverse (f : A →[M] B) (g : B → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B →[M] A
    where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g (f (m • g x)) := by rw [f.map_smul]
      _ = m • g x := by rw [h₁]
      
#align mul_action_hom.inverse MulActionHom.inverse

end MulActionHom

#print DistribMulActionHom /-
/-- Equivariant additive monoid homomorphisms. -/
structure DistribMulActionHom extends A →[M] B, A →+ B
#align distrib_mul_action_hom DistribMulActionHom
-/

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
add_decl_doc DistribMulActionHom.toAddMonoidHom

/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
add_decl_doc DistribMulActionHom.toMulActionHom

-- mathport name: «expr →+[ ] »
notation:25 A " →+[" M:25 "] " B:0 => DistribMulActionHom M A B

#print DistribMulActionHomClass /-
/-- `distrib_mul_action_hom_class F M A B` states that `F` is a type of morphisms preserving
the additive monoid structure and scalar multiplication by `M`.

You should extend this class when you extend `distrib_mul_action_hom`. -/
class DistribMulActionHomClass (F : Type _) (M A B : outParam <| Type _) [Monoid M] [AddMonoid A]
  [AddMonoid B] [DistribMulAction M A] [DistribMulAction M B] extends SMulHomClass F M A B,
  AddMonoidHomClass F A B
#align distrib_mul_action_hom_class DistribMulActionHomClass
-/

-- `M` becomes a metavariable but it's an `out_param` so it's not a problem.
attribute [nolint dangerous_instance] DistribMulActionHomClass.toAddMonoidHomClass

namespace DistribMulActionHom

/- warning: distrib_mul_action_hom.has_coe clashes with [anonymous] -> [anonymous]
warning: distrib_mul_action_hom.has_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_5}) [_inst_4 : Monoid.{u_5} M] (A : Type.{u_6}) [_inst_5 : AddMonoid.{u_6} A] [_inst_6 : DistribMulAction.{u_5, u_6} M A _inst_4 _inst_5] (B : Type.{u_8}) [_inst_9 : AddMonoid.{u_8} B] [_inst_10 : DistribMulAction.{u_5, u_8} M B _inst_4 _inst_9], Coe.{max (succ u_6) (succ u_8), max (succ u_8) (succ u_6)} (DistribMulActionHom.{u_5, u_6, u_8} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10) (AddMonoidHom.{u_6, u_8} A B (AddMonoid.toAddZeroClass.{u_6} A _inst_5) (AddMonoid.toAddZeroClass.{u_8} B _inst_9))
but is expected to have type
  forall {M : Type.{u}} {_inst_4 : Type.{v}}, (Nat -> M -> _inst_4) -> Nat -> (List.{u} M) -> (List.{v} _inst_4)
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.has_coe [anonymous]ₓ'. -/
instance [anonymous] : Coe (A →+[M] B) (A →+ B) :=
  ⟨toAddMonoidHom⟩
#align distrib_mul_action_hom.has_coe [anonymous]

/- warning: distrib_mul_action_hom.has_coe' clashes with [anonymous] -> [anonymous]
warning: distrib_mul_action_hom.has_coe' -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_5}) [_inst_4 : Monoid.{u_5} M] (A : Type.{u_6}) [_inst_5 : AddMonoid.{u_6} A] [_inst_6 : DistribMulAction.{u_5, u_6} M A _inst_4 _inst_5] (B : Type.{u_8}) [_inst_9 : AddMonoid.{u_8} B] [_inst_10 : DistribMulAction.{u_5, u_8} M B _inst_4 _inst_9], Coe.{max (succ u_6) (succ u_8), max (succ u_6) (succ u_8)} (DistribMulActionHom.{u_5, u_6, u_8} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10) (MulActionHom.{u_5, u_6, u_8} M A (SMulZeroClass.toHasSmul.{u_5, u_6} M A (AddZeroClass.toHasZero.{u_6} A (AddMonoid.toAddZeroClass.{u_6} A _inst_5)) (DistribSMul.toSmulZeroClass.{u_5, u_6} M A (AddMonoid.toAddZeroClass.{u_6} A _inst_5) (DistribMulAction.toDistribSMul.{u_5, u_6} M A _inst_4 _inst_5 _inst_6))) B (SMulZeroClass.toHasSmul.{u_5, u_8} M B (AddZeroClass.toHasZero.{u_8} B (AddMonoid.toAddZeroClass.{u_8} B _inst_9)) (DistribSMul.toSmulZeroClass.{u_5, u_8} M B (AddMonoid.toAddZeroClass.{u_8} B _inst_9) (DistribMulAction.toDistribSMul.{u_5, u_8} M B _inst_4 _inst_9 _inst_10))))
but is expected to have type
  forall {M : Type.{u}} {_inst_4 : Type.{v}}, (Nat -> M -> _inst_4) -> Nat -> (List.{u} M) -> (List.{v} _inst_4)
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.has_coe' [anonymous]ₓ'. -/
instance [anonymous] : Coe (A →+[M] B) (A →[M] B) :=
  ⟨toMulActionHom⟩
#align distrib_mul_action_hom.has_coe' [anonymous]

instance : CoeFun (A →+[M] B) fun _ => A → B :=
  ⟨toFun⟩

instance : DistribMulActionHomClass (A →+[M] B) M A B
    where
  coe := DistribMulActionHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_smul := DistribMulActionHom.map_smul'
  map_zero := DistribMulActionHom.map_zero'
  map_add := DistribMulActionHom.map_add'

variable {M A B}

/- warning: distrib_mul_action_hom.to_fun_eq_coe -> DistribMulActionHom.toFun_eq_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.to_fun_eq_coe DistribMulActionHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe (f : A →+[M] B) : f.toFun = ⇑f :=
  rfl
#align distrib_mul_action_hom.to_fun_eq_coe DistribMulActionHom.toFun_eq_coe

/- warning: distrib_mul_action_hom.coe_fn_coe -> DistribMulActionHom.coe_fn_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.coe_fn_coe DistribMulActionHom.coe_fn_coeₓ'. -/
@[norm_cast]
theorem coe_fn_coe (f : A →+[M] B) : ((f : A →+ B) : A → B) = f :=
  rfl
#align distrib_mul_action_hom.coe_fn_coe DistribMulActionHom.coe_fn_coe

/- warning: distrib_mul_action_hom.coe_fn_coe' -> DistribMulActionHom.coe_fn_coe' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.coe_fn_coe' DistribMulActionHom.coe_fn_coe'ₓ'. -/
@[norm_cast]
theorem coe_fn_coe' (f : A →+[M] B) : ((f : A →[M] B) : A → B) = f :=
  rfl
#align distrib_mul_action_hom.coe_fn_coe' DistribMulActionHom.coe_fn_coe'

/- warning: distrib_mul_action_hom.ext -> DistribMulActionHom.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.ext DistribMulActionHom.extₓ'. -/
@[ext]
theorem ext : ∀ {f g : A →+[M] B}, (∀ x, f x = g x) → f = g :=
  FunLike.ext
#align distrib_mul_action_hom.ext DistribMulActionHom.ext

/- warning: distrib_mul_action_hom.ext_iff -> DistribMulActionHom.ext_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.ext_iff DistribMulActionHom.ext_iffₓ'. -/
theorem ext_iff {f g : A →+[M] B} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align distrib_mul_action_hom.ext_iff DistribMulActionHom.ext_iff

/- warning: distrib_mul_action_hom.congr_fun -> DistribMulActionHom.congr_fun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.congr_fun DistribMulActionHom.congr_funₓ'. -/
protected theorem congr_fun {f g : A →+[M] B} (h : f = g) (x : A) : f x = g x :=
  FunLike.congr_fun h _
#align distrib_mul_action_hom.congr_fun DistribMulActionHom.congr_fun

/- warning: distrib_mul_action_hom.to_mul_action_hom_injective -> DistribMulActionHom.toMulActionHom_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.to_mul_action_hom_injective DistribMulActionHom.toMulActionHom_injectiveₓ'. -/
theorem toMulActionHom_injective {f g : A →+[M] B} (h : (f : A →[M] B) = (g : A →[M] B)) : f = g :=
  by ext a; exact MulActionHom.congr_fun h a
#align distrib_mul_action_hom.to_mul_action_hom_injective DistribMulActionHom.toMulActionHom_injective

/- warning: distrib_mul_action_hom.to_add_monoid_hom_injective -> DistribMulActionHom.toAddMonoidHom_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.to_add_monoid_hom_injective DistribMulActionHom.toAddMonoidHom_injectiveₓ'. -/
theorem toAddMonoidHom_injective {f g : A →+[M] B} (h : (f : A →+ B) = (g : A →+ B)) : f = g := by
  ext a; exact AddMonoidHom.congr_fun h a
#align distrib_mul_action_hom.to_add_monoid_hom_injective DistribMulActionHom.toAddMonoidHom_injective

/- warning: distrib_mul_action_hom.map_zero -> DistribMulActionHom.map_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.map_zero DistribMulActionHom.map_zeroₓ'. -/
protected theorem map_zero (f : A →+[M] B) : f 0 = 0 :=
  map_zero _
#align distrib_mul_action_hom.map_zero DistribMulActionHom.map_zero

/- warning: distrib_mul_action_hom.map_add -> DistribMulActionHom.map_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.map_add DistribMulActionHom.map_addₓ'. -/
protected theorem map_add (f : A →+[M] B) (x y : A) : f (x + y) = f x + f y :=
  map_add _ _ _
#align distrib_mul_action_hom.map_add DistribMulActionHom.map_add

/- warning: distrib_mul_action_hom.map_neg -> DistribMulActionHom.map_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.map_neg DistribMulActionHom.map_negₓ'. -/
protected theorem map_neg (f : A' →+[M] B') (x : A') : f (-x) = -f x :=
  map_neg _ _
#align distrib_mul_action_hom.map_neg DistribMulActionHom.map_neg

/- warning: distrib_mul_action_hom.map_sub -> DistribMulActionHom.map_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.map_sub DistribMulActionHom.map_subₓ'. -/
protected theorem map_sub (f : A' →+[M] B') (x y : A') : f (x - y) = f x - f y :=
  map_sub _ _ _
#align distrib_mul_action_hom.map_sub DistribMulActionHom.map_sub

/- warning: distrib_mul_action_hom.map_smul -> DistribMulActionHom.map_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.map_smul DistribMulActionHom.map_smulₓ'. -/
protected theorem map_smul (f : A →+[M] B) (m : M) (x : A) : f (m • x) = m • f x :=
  map_smul _ _ _
#align distrib_mul_action_hom.map_smul DistribMulActionHom.map_smul

variable (M) {A}

#print DistribMulActionHom.id /-
/-- The identity map as an equivariant additive monoid homomorphism. -/
protected def id : A →+[M] A :=
  ⟨id, fun _ _ => rfl, rfl, fun _ _ => rfl⟩
#align distrib_mul_action_hom.id DistribMulActionHom.id
-/

#print DistribMulActionHom.id_apply /-
@[simp]
theorem id_apply (x : A) : DistribMulActionHom.id M x = x :=
  rfl
#align distrib_mul_action_hom.id_apply DistribMulActionHom.id_apply
-/

variable {M A B C}

instance : Zero (A →+[M] B) :=
  ⟨{ (0 : A →+ B) with map_smul' := by simp }⟩

instance : One (A →+[M] A) :=
  ⟨DistribMulActionHom.id M⟩

/- warning: distrib_mul_action_hom.coe_zero -> DistribMulActionHom.coe_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.coe_zero DistribMulActionHom.coe_zeroₓ'. -/
@[simp]
theorem coe_zero : ((0 : A →+[M] B) : A → B) = 0 :=
  rfl
#align distrib_mul_action_hom.coe_zero DistribMulActionHom.coe_zero

#print DistribMulActionHom.coe_one /-
@[simp]
theorem coe_one : ((1 : A →+[M] A) : A → A) = id :=
  rfl
#align distrib_mul_action_hom.coe_one DistribMulActionHom.coe_one
-/

#print DistribMulActionHom.zero_apply /-
theorem zero_apply (a : A) : (0 : A →+[M] B) a = 0 :=
  rfl
#align distrib_mul_action_hom.zero_apply DistribMulActionHom.zero_apply
-/

#print DistribMulActionHom.one_apply /-
theorem one_apply (a : A) : (1 : A →+[M] A) a = a :=
  rfl
#align distrib_mul_action_hom.one_apply DistribMulActionHom.one_apply
-/

instance : Inhabited (A →+[M] B) :=
  ⟨0⟩

#print DistribMulActionHom.comp /-
/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : B →+[M] C) (f : A →+[M] B) : A →+[M] C :=
  { MulActionHom.comp (g : B →[M] C) (f : A →[M] B),
    AddMonoidHom.comp (g : B →+ C) (f : A →+ B) with }
#align distrib_mul_action_hom.comp DistribMulActionHom.comp
-/

/- warning: distrib_mul_action_hom.comp_apply -> DistribMulActionHom.comp_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.comp_apply DistribMulActionHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (g : B →+[M] C) (f : A →+[M] B) (x : A) : g.comp f x = g (f x) :=
  rfl
#align distrib_mul_action_hom.comp_apply DistribMulActionHom.comp_apply

/- warning: distrib_mul_action_hom.id_comp -> DistribMulActionHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] {A : Type.{u2}} [_inst_5 : AddMonoid.{u2} A] [_inst_6 : DistribMulAction.{u1, u2} M A _inst_4 _inst_5] {B : Type.{u3}} [_inst_9 : AddMonoid.{u3} B] [_inst_10 : DistribMulAction.{u1, u3} M B _inst_4 _inst_9] (f : DistribMulActionHom.{u1, u2, u3} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10), Eq.{max (succ u2) (succ u3)} (DistribMulActionHom.{u1, u2, u3} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10) (DistribMulActionHom.comp.{u1, u2, u3, u3} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10 B _inst_9 _inst_10 (DistribMulActionHom.id.{u1, u3} M _inst_4 B _inst_9 _inst_10) f) f
but is expected to have type
  forall {M : Type.{u3}} [_inst_4 : Monoid.{u3} M] {A : Type.{u2}} [_inst_5 : AddMonoid.{u2} A] [_inst_6 : DistribMulAction.{u3, u2} M A _inst_4 _inst_5] {B : Type.{u1}} [_inst_9 : AddMonoid.{u1} B] [_inst_10 : DistribMulAction.{u3, u1} M B _inst_4 _inst_9] (f : DistribMulActionHom.{u3, u2, u1} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10), Eq.{max (succ u2) (succ u1)} (DistribMulActionHom.{u3, u2, u1} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10) (DistribMulActionHom.comp.{u3, u2, u1, u1} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10 B _inst_9 _inst_10 (DistribMulActionHom.id.{u3, u1} M _inst_4 B _inst_9 _inst_10) f) f
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.id_comp DistribMulActionHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : A →+[M] B) : (DistribMulActionHom.id M).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align distrib_mul_action_hom.id_comp DistribMulActionHom.id_comp

/- warning: distrib_mul_action_hom.comp_id -> DistribMulActionHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] {A : Type.{u2}} [_inst_5 : AddMonoid.{u2} A] [_inst_6 : DistribMulAction.{u1, u2} M A _inst_4 _inst_5] {B : Type.{u3}} [_inst_9 : AddMonoid.{u3} B] [_inst_10 : DistribMulAction.{u1, u3} M B _inst_4 _inst_9] (f : DistribMulActionHom.{u1, u2, u3} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10), Eq.{max (succ u2) (succ u3)} (DistribMulActionHom.{u1, u2, u3} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10) (DistribMulActionHom.comp.{u1, u2, u2, u3} M _inst_4 A _inst_5 _inst_6 A _inst_5 _inst_6 B _inst_9 _inst_10 f (DistribMulActionHom.id.{u1, u2} M _inst_4 A _inst_5 _inst_6)) f
but is expected to have type
  forall {M : Type.{u3}} [_inst_4 : Monoid.{u3} M] {A : Type.{u2}} [_inst_5 : AddMonoid.{u2} A] [_inst_6 : DistribMulAction.{u3, u2} M A _inst_4 _inst_5] {B : Type.{u1}} [_inst_9 : AddMonoid.{u1} B] [_inst_10 : DistribMulAction.{u3, u1} M B _inst_4 _inst_9] (f : DistribMulActionHom.{u3, u2, u1} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10), Eq.{max (succ u2) (succ u1)} (DistribMulActionHom.{u3, u2, u1} M _inst_4 A _inst_5 _inst_6 B _inst_9 _inst_10) (DistribMulActionHom.comp.{u3, u2, u2, u1} M _inst_4 A _inst_5 _inst_6 A _inst_5 _inst_6 B _inst_9 _inst_10 f (DistribMulActionHom.id.{u3, u2} M _inst_4 A _inst_5 _inst_6)) f
Case conversion may be inaccurate. Consider using '#align distrib_mul_action_hom.comp_id DistribMulActionHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : A →+[M] B) : f.comp (DistribMulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align distrib_mul_action_hom.comp_id DistribMulActionHom.comp_id

#print DistribMulActionHom.inverse /-
/-- The inverse of a bijective `distrib_mul_action_hom` is a `distrib_mul_action_hom`. -/
@[simps]
def inverse (f : A →+[M] B) (g : B → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B →+[M] A :=
  { (f : A →+ B).inverse g h₁ h₂, (f : A →[M] B).inverse g h₁ h₂ with toFun := g }
#align distrib_mul_action_hom.inverse DistribMulActionHom.inverse
-/

section Semiring

variable {R M'} [AddMonoid M'] [DistribMulAction R M']

#print DistribMulActionHom.ext_ring /-
@[ext]
theorem ext_ring {f g : R →+[R] M'} (h : f 1 = g 1) : f = g := by ext x;
  rw [← mul_one x, ← smul_eq_mul R, f.map_smul, g.map_smul, h]
#align distrib_mul_action_hom.ext_ring DistribMulActionHom.ext_ring
-/

#print DistribMulActionHom.ext_ring_iff /-
theorem ext_ring_iff {f g : R →+[R] M'} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩
#align distrib_mul_action_hom.ext_ring_iff DistribMulActionHom.ext_ring_iff
-/

end Semiring

end DistribMulActionHom

#print MulSemiringActionHom /-
/-- Equivariant ring homomorphisms. -/
@[nolint has_nonempty_instance]
structure MulSemiringActionHom extends R →+[M] S, R →+* S
#align mul_semiring_action_hom MulSemiringActionHom
-/

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc MulSemiringActionHom.toRingHom

/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
add_decl_doc MulSemiringActionHom.toDistribMulActionHom

-- mathport name: «expr →+*[ ] »
notation:25 R " →+*[" M:25 "] " S:0 => MulSemiringActionHom M R S

#print MulSemiringActionHomClass /-
/-- `mul_semiring_action_hom_class F M R S` states that `F` is a type of morphisms preserving
the ring structure and scalar multiplication by `M`.

You should extend this class when you extend `mul_semiring_action_hom`. -/
class MulSemiringActionHomClass (F : Type _) (M R S : outParam <| Type _) [Monoid M] [Semiring R]
  [Semiring S] [DistribMulAction M R] [DistribMulAction M S] extends
  DistribMulActionHomClass F M R S, RingHomClass F R S
#align mul_semiring_action_hom_class MulSemiringActionHomClass
-/

-- `M` becomes a metavariable but it's an `out_param` so it's not a problem.
attribute [nolint dangerous_instance] MulSemiringActionHomClass.toRingHomClass

namespace MulSemiringActionHom

/- warning: mul_semiring_action_hom.has_coe clashes with [anonymous] -> [anonymous]
warning: mul_semiring_action_hom.has_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_5}) [_inst_4 : Monoid.{u_5} M] (R : Type.{u_11}) [_inst_15 : Semiring.{u_11} R] [_inst_16 : MulSemiringAction.{u_5, u_11} M R _inst_4 _inst_15] (S : Type.{u_13}) [_inst_19 : Semiring.{u_13} S] [_inst_20 : MulSemiringAction.{u_5, u_13} M S _inst_4 _inst_19], Coe.{max (succ u_11) (succ u_13), max (succ u_11) (succ u_13)} (MulSemiringActionHom.{u_5, u_11, u_13} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20) (RingHom.{u_11, u_13} R S (Semiring.toNonAssocSemiring.{u_11} R _inst_15) (Semiring.toNonAssocSemiring.{u_13} S _inst_19))
but is expected to have type
  forall {M : Type.{u}} {_inst_4 : Type.{v}}, (Nat -> M -> _inst_4) -> Nat -> (List.{u} M) -> (List.{v} _inst_4)
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.has_coe [anonymous]ₓ'. -/
instance [anonymous] : Coe (R →+*[M] S) (R →+* S) :=
  ⟨toRingHom⟩
#align mul_semiring_action_hom.has_coe [anonymous]

/- warning: mul_semiring_action_hom.has_coe' clashes with [anonymous] -> [anonymous]
warning: mul_semiring_action_hom.has_coe' -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_5}) [_inst_4 : Monoid.{u_5} M] (R : Type.{u_11}) [_inst_15 : Semiring.{u_11} R] [_inst_16 : MulSemiringAction.{u_5, u_11} M R _inst_4 _inst_15] (S : Type.{u_13}) [_inst_19 : Semiring.{u_13} S] [_inst_20 : MulSemiringAction.{u_5, u_13} M S _inst_4 _inst_19], Coe.{max (succ u_11) (succ u_13), max (succ u_11) (succ u_13)} (MulSemiringActionHom.{u_5, u_11, u_13} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20) (DistribMulActionHom.{u_5, u_11, u_13} M _inst_4 R (AddMonoidWithOne.toAddMonoid.{u_11} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u_11} R (NonAssocSemiring.toAddCommMonoidWithOne.{u_11} R (Semiring.toNonAssocSemiring.{u_11} R _inst_15)))) (MulSemiringAction.toDistribMulAction.{u_5, u_11} M R _inst_4 _inst_15 _inst_16) S (AddMonoidWithOne.toAddMonoid.{u_13} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u_13} S (NonAssocSemiring.toAddCommMonoidWithOne.{u_13} S (Semiring.toNonAssocSemiring.{u_13} S _inst_19)))) (MulSemiringAction.toDistribMulAction.{u_5, u_13} M S _inst_4 _inst_19 _inst_20))
but is expected to have type
  forall {M : Type.{u}} {_inst_4 : Type.{v}}, (Nat -> M -> _inst_4) -> Nat -> (List.{u} M) -> (List.{v} _inst_4)
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.has_coe' [anonymous]ₓ'. -/
instance [anonymous] : Coe (R →+*[M] S) (R →+[M] S) :=
  ⟨toDistribMulActionHom⟩
#align mul_semiring_action_hom.has_coe' [anonymous]

instance : CoeFun (R →+*[M] S) fun _ => R → S :=
  ⟨fun c => c.toFun⟩

instance : MulSemiringActionHomClass (R →+*[M] S) M R S
    where
  coe := MulSemiringActionHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_smul := MulSemiringActionHom.map_smul'
  map_zero := MulSemiringActionHom.map_zero'
  map_add := MulSemiringActionHom.map_add'
  map_one := MulSemiringActionHom.map_one'
  map_mul := MulSemiringActionHom.map_mul'

variable {M R S}

/- warning: mul_semiring_action_hom.coe_fn_coe -> MulSemiringActionHom.coe_fn_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.coe_fn_coe MulSemiringActionHom.coe_fn_coeₓ'. -/
@[norm_cast]
theorem coe_fn_coe (f : R →+*[M] S) : ((f : R →+* S) : R → S) = f :=
  rfl
#align mul_semiring_action_hom.coe_fn_coe MulSemiringActionHom.coe_fn_coe

/- warning: mul_semiring_action_hom.coe_fn_coe' -> MulSemiringActionHom.coe_fn_coe' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.coe_fn_coe' MulSemiringActionHom.coe_fn_coe'ₓ'. -/
@[norm_cast]
theorem coe_fn_coe' (f : R →+*[M] S) : ((f : R →+[M] S) : R → S) = f :=
  rfl
#align mul_semiring_action_hom.coe_fn_coe' MulSemiringActionHom.coe_fn_coe'

/- warning: mul_semiring_action_hom.ext -> MulSemiringActionHom.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.ext MulSemiringActionHom.extₓ'. -/
@[ext]
theorem ext : ∀ {f g : R →+*[M] S}, (∀ x, f x = g x) → f = g :=
  FunLike.ext
#align mul_semiring_action_hom.ext MulSemiringActionHom.ext

/- warning: mul_semiring_action_hom.ext_iff -> MulSemiringActionHom.ext_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.ext_iff MulSemiringActionHom.ext_iffₓ'. -/
theorem ext_iff {f g : R →+*[M] S} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_semiring_action_hom.ext_iff MulSemiringActionHom.ext_iff

/- warning: mul_semiring_action_hom.map_zero -> MulSemiringActionHom.map_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.map_zero MulSemiringActionHom.map_zeroₓ'. -/
protected theorem map_zero (f : R →+*[M] S) : f 0 = 0 :=
  map_zero _
#align mul_semiring_action_hom.map_zero MulSemiringActionHom.map_zero

/- warning: mul_semiring_action_hom.map_add -> MulSemiringActionHom.map_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.map_add MulSemiringActionHom.map_addₓ'. -/
protected theorem map_add (f : R →+*[M] S) (x y : R) : f (x + y) = f x + f y :=
  map_add _ _ _
#align mul_semiring_action_hom.map_add MulSemiringActionHom.map_add

/- warning: mul_semiring_action_hom.map_neg -> MulSemiringActionHom.map_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.map_neg MulSemiringActionHom.map_negₓ'. -/
protected theorem map_neg (f : R' →+*[M] S') (x : R') : f (-x) = -f x :=
  map_neg _ _
#align mul_semiring_action_hom.map_neg MulSemiringActionHom.map_neg

/- warning: mul_semiring_action_hom.map_sub -> MulSemiringActionHom.map_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.map_sub MulSemiringActionHom.map_subₓ'. -/
protected theorem map_sub (f : R' →+*[M] S') (x y : R') : f (x - y) = f x - f y :=
  map_sub _ _ _
#align mul_semiring_action_hom.map_sub MulSemiringActionHom.map_sub

/- warning: mul_semiring_action_hom.map_one -> MulSemiringActionHom.map_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.map_one MulSemiringActionHom.map_oneₓ'. -/
protected theorem map_one (f : R →+*[M] S) : f 1 = 1 :=
  map_one _
#align mul_semiring_action_hom.map_one MulSemiringActionHom.map_one

/- warning: mul_semiring_action_hom.map_mul -> MulSemiringActionHom.map_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.map_mul MulSemiringActionHom.map_mulₓ'. -/
protected theorem map_mul (f : R →+*[M] S) (x y : R) : f (x * y) = f x * f y :=
  map_mul _ _ _
#align mul_semiring_action_hom.map_mul MulSemiringActionHom.map_mul

/- warning: mul_semiring_action_hom.map_smul -> MulSemiringActionHom.map_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.map_smul MulSemiringActionHom.map_smulₓ'. -/
protected theorem map_smul (f : R →+*[M] S) (m : M) (x : R) : f (m • x) = m • f x :=
  map_smul _ _ _
#align mul_semiring_action_hom.map_smul MulSemiringActionHom.map_smul

variable (M) {R}

#print MulSemiringActionHom.id /-
/-- The identity map as an equivariant ring homomorphism. -/
protected def id : R →+*[M] R :=
  ⟨id, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩
#align mul_semiring_action_hom.id MulSemiringActionHom.id
-/

#print MulSemiringActionHom.id_apply /-
@[simp]
theorem id_apply (x : R) : MulSemiringActionHom.id M x = x :=
  rfl
#align mul_semiring_action_hom.id_apply MulSemiringActionHom.id_apply
-/

variable {M R S T}

#print MulSemiringActionHom.comp /-
/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : S →+*[M] T) (f : R →+*[M] S) : R →+*[M] T :=
  { DistribMulActionHom.comp (g : S →+[M] T) (f : R →+[M] S),
    RingHom.comp (g : S →+* T) (f : R →+* S) with }
#align mul_semiring_action_hom.comp MulSemiringActionHom.comp
-/

/- warning: mul_semiring_action_hom.comp_apply -> MulSemiringActionHom.comp_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.comp_apply MulSemiringActionHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (g : S →+*[M] T) (f : R →+*[M] S) (x : R) : g.comp f x = g (f x) :=
  rfl
#align mul_semiring_action_hom.comp_apply MulSemiringActionHom.comp_apply

/- warning: mul_semiring_action_hom.id_comp -> MulSemiringActionHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] {R : Type.{u2}} [_inst_15 : Semiring.{u2} R] [_inst_16 : MulSemiringAction.{u1, u2} M R _inst_4 _inst_15] {S : Type.{u3}} [_inst_19 : Semiring.{u3} S] [_inst_20 : MulSemiringAction.{u1, u3} M S _inst_4 _inst_19] (f : MulSemiringActionHom.{u1, u2, u3} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20), Eq.{max (succ u2) (succ u3)} (MulSemiringActionHom.{u1, u2, u3} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20) (MulSemiringActionHom.comp.{u1, u2, u3, u3} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20 S _inst_19 _inst_20 (MulSemiringActionHom.id.{u1, u3} M _inst_4 S _inst_19 _inst_20) f) f
but is expected to have type
  forall {M : Type.{u3}} [_inst_4 : Monoid.{u3} M] {R : Type.{u2}} [_inst_15 : Semiring.{u2} R] [_inst_16 : MulSemiringAction.{u3, u2} M R _inst_4 _inst_15] {S : Type.{u1}} [_inst_19 : Semiring.{u1} S] [_inst_20 : MulSemiringAction.{u3, u1} M S _inst_4 _inst_19] (f : MulSemiringActionHom.{u3, u2, u1} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20), Eq.{max (succ u2) (succ u1)} (MulSemiringActionHom.{u3, u2, u1} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20) (MulSemiringActionHom.comp.{u3, u2, u1, u1} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20 S _inst_19 _inst_20 (MulSemiringActionHom.id.{u3, u1} M _inst_4 S _inst_19 _inst_20) f) f
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.id_comp MulSemiringActionHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : R →+*[M] S) : (MulSemiringActionHom.id M).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align mul_semiring_action_hom.id_comp MulSemiringActionHom.id_comp

/- warning: mul_semiring_action_hom.comp_id -> MulSemiringActionHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] {R : Type.{u2}} [_inst_15 : Semiring.{u2} R] [_inst_16 : MulSemiringAction.{u1, u2} M R _inst_4 _inst_15] {S : Type.{u3}} [_inst_19 : Semiring.{u3} S] [_inst_20 : MulSemiringAction.{u1, u3} M S _inst_4 _inst_19] (f : MulSemiringActionHom.{u1, u2, u3} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20), Eq.{max (succ u2) (succ u3)} (MulSemiringActionHom.{u1, u2, u3} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20) (MulSemiringActionHom.comp.{u1, u2, u2, u3} M _inst_4 R _inst_15 _inst_16 R _inst_15 _inst_16 S _inst_19 _inst_20 f (MulSemiringActionHom.id.{u1, u2} M _inst_4 R _inst_15 _inst_16)) f
but is expected to have type
  forall {M : Type.{u3}} [_inst_4 : Monoid.{u3} M] {R : Type.{u2}} [_inst_15 : Semiring.{u2} R] [_inst_16 : MulSemiringAction.{u3, u2} M R _inst_4 _inst_15] {S : Type.{u1}} [_inst_19 : Semiring.{u1} S] [_inst_20 : MulSemiringAction.{u3, u1} M S _inst_4 _inst_19] (f : MulSemiringActionHom.{u3, u2, u1} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20), Eq.{max (succ u2) (succ u1)} (MulSemiringActionHom.{u3, u2, u1} M _inst_4 R _inst_15 _inst_16 S _inst_19 _inst_20) (MulSemiringActionHom.comp.{u3, u2, u2, u1} M _inst_4 R _inst_15 _inst_16 R _inst_15 _inst_16 S _inst_19 _inst_20 f (MulSemiringActionHom.id.{u3, u2} M _inst_4 R _inst_15 _inst_16)) f
Case conversion may be inaccurate. Consider using '#align mul_semiring_action_hom.comp_id MulSemiringActionHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : R →+*[M] S) : f.comp (MulSemiringActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align mul_semiring_action_hom.comp_id MulSemiringActionHom.comp_id

end MulSemiringActionHom

