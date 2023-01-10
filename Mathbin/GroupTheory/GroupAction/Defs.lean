/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov

! This file was ported from Lean 3 source module group_theory.group_action.defs
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.TypeTags
import Mathbin.Algebra.Group.Commute
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Opposites
import Mathbin.Logic.Embedding.Basic

/-!
# Definitions of group actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `has_smul` and its additive version `has_vadd`:

* `mul_action M α` and its additive version `add_action G P` are typeclasses used for
  actions of multiplicative and additive monoids and groups; they extend notation classes
  `has_smul` and `has_vadd` that are defined in `algebra.group.defs`;
* `distrib_mul_action M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `module`, defined elsewhere.

Also provided are typeclasses for faithful and transitive actions, and typeclasses regarding the
interaction of different group actions,

* `smul_comm_class M N α` and its additive version `vadd_comm_class M N α`;
* `is_scalar_tower M N α` (no additive version).
* `is_central_scalar M α` (no additive version).

## Notation

- `a • b` is used as notation for `has_smul.smul a b`.
- `a +ᵥ b` is used as notation for `has_vadd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `group_theory`, to avoid import cycles.
More sophisticated lemmas belong in `group_theory.group_action`.

## Tags

group action
-/


variable {M N G A B α β γ δ : Type _}

open Function (Injective Surjective)

/-!
### Faithful actions
-/


#print FaithfulVAdd /-
/-- Typeclass for faithful actions. -/
class FaithfulVAdd (G : Type _) (P : Type _) [VAdd G P] : Prop where
  eq_of_vadd_eq_vadd : ∀ {g₁ g₂ : G}, (∀ p : P, g₁ +ᵥ p = g₂ +ᵥ p) → g₁ = g₂
#align has_faithful_vadd FaithfulVAdd
-/

/- warning: has_faithful_smul -> FaithfulSMul is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : HasSmul.{u1, u2} M α], Prop
but is expected to have type
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : SMul.{u1, u2} M α], Prop
Case conversion may be inaccurate. Consider using '#align has_faithful_smul FaithfulSMulₓ'. -/
/-- Typeclass for faithful actions. -/
@[to_additive]
class FaithfulSMul (M : Type _) (α : Type _) [HasSmul M α] : Prop where
  eq_of_smul_eq_smul : ∀ {m₁ m₂ : M}, (∀ a : α, m₁ • a = m₂ • a) → m₁ = m₂
#align has_faithful_smul FaithfulSMul

export FaithfulSMul (eq_of_smul_eq_smul)

export FaithfulVAdd (eq_of_vadd_eq_vadd)

/- warning: smul_left_injective' -> smul_left_injective' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] [_inst_2 : FaithfulSMul.{u1, u2} M α _inst_1], Function.Injective.{succ u1, succ u2} M (α -> α) (HasSmul.smul.{u1, u2} M α _inst_1)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : SMul.{u2, u1} M α] [_inst_2 : FaithfulSMul.{u2, u1} M α _inst_1], Function.Injective.{succ u2, succ u1} M (α -> α) (fun (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.173 : M) (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.175 : α) => HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α _inst_1) x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.173 x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.175)
Case conversion may be inaccurate. Consider using '#align smul_left_injective' smul_left_injective'ₓ'. -/
@[to_additive]
theorem smul_left_injective' [HasSmul M α] [FaithfulSMul M α] :
    Function.Injective ((· • ·) : M → α → α) := fun m₁ m₂ h =>
  FaithfulSMul.eq_of_smul_eq_smul (congr_fun h)
#align smul_left_injective' smul_left_injective'

/- warning: has_mul.to_has_smul -> Mul.toSMul is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Mul.{u1} α], HasSmul.{u1, u1} α α
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Mul.{u1} α], SMul.{u1, u1} α α
Case conversion may be inaccurate. Consider using '#align has_mul.to_has_smul Mul.toSMulₓ'. -/
-- see Note [lower instance priority]
/-- See also `monoid.to_mul_action` and `mul_zero_class.to_smul_with_zero`. -/
@[to_additive "See also `add_monoid.to_add_action`"]
instance (priority := 910) Mul.toSMul (α : Type _) [Mul α] : HasSmul α α :=
  ⟨(· * ·)⟩
#align has_mul.to_has_smul Mul.toSMul

#print smul_eq_mul /-
@[simp, to_additive]
theorem smul_eq_mul (α : Type _) [Mul α] {a a' : α} : a • a' = a * a' :=
  rfl
#align smul_eq_mul smul_eq_mul
-/

#print AddAction /-
/-- Type class for additive monoid actions. -/
@[ext, protect_proj]
class AddAction (G : Type _) (P : Type _) [AddMonoid G] extends VAdd G P where
  zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  add_vadd : ∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)
#align add_action AddAction
-/

#print MulAction /-
/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[ext, protect_proj, to_additive]
class MulAction (α : Type _) (β : Type _) [Monoid α] extends HasSmul α β where
  one_smul : ∀ b : β, (1 : α) • b = b
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b
#align mul_action MulAction
-/

/-!
### (Pre)transitive action

`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y` (or `g +ᵥ x = y`
for an additive action). A transitive action should furthermore have `α` nonempty.

In this section we define typeclasses `mul_action.is_pretransitive` and
`add_action.is_pretransitive` and provide `mul_action.exists_smul_eq`/`add_action.exists_vadd_eq`,
`mul_action.surjective_smul`/`add_action.surjective_vadd` as public interface to access this
property. We do not provide typeclasses `*_action.is_transitive`; users should assume
`[mul_action.is_pretransitive M α] [nonempty α]` instead. -/


#print AddAction.IsPretransitive /-
/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g +ᵥ x = y`.
  A transitive action should furthermore have `α` nonempty. -/
class AddAction.IsPretransitive (M α : Type _) [VAdd M α] : Prop where
  exists_vadd_eq : ∀ x y : α, ∃ g : M, g +ᵥ x = y
#align add_action.is_pretransitive AddAction.IsPretransitive
-/

/- warning: mul_action.is_pretransitive -> MulAction.IsPretransitive is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : HasSmul.{u1, u2} M α], Prop
but is expected to have type
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : SMul.{u1, u2} M α], Prop
Case conversion may be inaccurate. Consider using '#align mul_action.is_pretransitive MulAction.IsPretransitiveₓ'. -/
/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `α` nonempty. -/
@[to_additive]
class MulAction.IsPretransitive (M α : Type _) [HasSmul M α] : Prop where
  exists_smul_eq : ∀ x y : α, ∃ g : M, g • x = y
#align mul_action.is_pretransitive MulAction.IsPretransitive

namespace MulAction

variable (M) {α} [HasSmul M α] [IsPretransitive M α]

/- warning: mul_action.exists_smul_eq -> MulAction.exists_smul_eq is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] [_inst_2 : MulAction.IsPretransitive.{u1, u2} M α _inst_1] (x : α) (y : α), Exists.{succ u1} M (fun (m : M) => Eq.{succ u2} α (HasSmul.smul.{u1, u2} M α _inst_1 m x) y)
but is expected to have type
  forall (M : Type.{u2}) {α : Type.{u1}} [_inst_1 : SMul.{u2, u1} M α] [_inst_2 : MulAction.IsPretransitive.{u2, u1} M α _inst_1] (x : α) (y : α), Exists.{succ u2} M (fun (m : M) => Eq.{succ u1} α (HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α _inst_1) m x) y)
Case conversion may be inaccurate. Consider using '#align mul_action.exists_smul_eq MulAction.exists_smul_eqₓ'. -/
@[to_additive]
theorem exists_smul_eq (x y : α) : ∃ m : M, m • x = y :=
  IsPretransitive.exists_smul_eq x y
#align mul_action.exists_smul_eq MulAction.exists_smul_eq

/- warning: mul_action.surjective_smul -> MulAction.surjective_smul is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] [_inst_2 : MulAction.IsPretransitive.{u1, u2} M α _inst_1] (x : α), Function.Surjective.{succ u1, succ u2} M α (fun (c : M) => HasSmul.smul.{u1, u2} M α _inst_1 c x)
but is expected to have type
  forall (M : Type.{u2}) {α : Type.{u1}} [_inst_1 : SMul.{u2, u1} M α] [_inst_2 : MulAction.IsPretransitive.{u2, u1} M α _inst_1] (x : α), Function.Surjective.{succ u2, succ u1} M α (fun (c : M) => HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α _inst_1) c x)
Case conversion may be inaccurate. Consider using '#align mul_action.surjective_smul MulAction.surjective_smulₓ'. -/
@[to_additive]
theorem surjective_smul (x : α) : Surjective fun c : M => c • x :=
  exists_smul_eq M x
#align mul_action.surjective_smul MulAction.surjective_smul

/- warning: mul_action.regular.is_pretransitive -> MulAction.Regular.isPretransitive is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G], MulAction.IsPretransitive.{u1, u1} G G (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G], MulAction.IsPretransitive.{u1, u1} G G (Mul.toSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))))
Case conversion may be inaccurate. Consider using '#align mul_action.regular.is_pretransitive MulAction.Regular.isPretransitiveₓ'. -/
/-- The regular action of a group on itself is transitive. -/
@[to_additive "The regular action of a group on itself is transitive."]
instance Regular.isPretransitive [Group G] : IsPretransitive G G :=
  ⟨fun x y => ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩
#align mul_action.regular.is_pretransitive MulAction.Regular.isPretransitive

end MulAction

/-!
### Scalar tower and commuting actions
-/


#print VAddCommClass /-
/-- A typeclass mixin saying that two additive actions on the same space commute. -/
class VAddCommClass (M N α : Type _) [VAdd M α] [VAdd N α] : Prop where
  vadd_comm : ∀ (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a)
#align vadd_comm_class VAddCommClass
-/

/- warning: smul_comm_class -> SMulCommClass is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (N : Type.{u2}) (α : Type.{u3}) [_inst_1 : HasSmul.{u1, u3} M α] [_inst_2 : HasSmul.{u2, u3} N α], Prop
but is expected to have type
  forall (M : Type.{u1}) (N : Type.{u2}) (α : Type.{u3}) [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u2, u3} N α], Prop
Case conversion may be inaccurate. Consider using '#align smul_comm_class SMulCommClassₓ'. -/
/-- A typeclass mixin saying that two multiplicative actions on the same space commute. -/
@[to_additive]
class SMulCommClass (M N α : Type _) [HasSmul M α] [HasSmul N α] : Prop where
  smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a
#align smul_comm_class SMulCommClass

export MulAction (mul_smul)

export AddAction (add_vadd)

export SMulCommClass (smul_comm)

export VAddCommClass (vadd_comm)

library_note "bundled maps over different rings"/--
Frequently, we find ourselves wanting to express a bilinear map `M →ₗ[R] N →ₗ[R] P` or an
equivalence between maps `(M →ₗ[R] N) ≃ₗ[R] (M' →ₗ[R] N')` where the maps have an associated ring
`R`. Unfortunately, using definitions like these requires that `R` satisfy `comm_semiring R`, and
not just `semiring R`. Using `M →ₗ[R] N →+ P` and `(M →ₗ[R] N) ≃+ (M' →ₗ[R] N')` avoids this
problem, but throws away structure that is useful for when we _do_ have a commutative (semi)ring.

To avoid making this compromise, we instead state these definitions as `M →ₗ[R] N →ₗ[S] P` or
`(M →ₗ[R] N) ≃ₗ[S] (M' →ₗ[R] N')` and require `smul_comm_class S R` on the appropriate modules. When
the caller has `comm_semiring R`, they can set `S = R` and `smul_comm_class_self` will populate the
instance. If the caller only has `semiring R` they can still set either `R = ℕ` or `S = ℕ`, and
`add_comm_monoid.nat_smul_comm_class` or `add_comm_monoid.nat_smul_comm_class'` will populate
the typeclass, which is still sufficient to recover a `≃+` or `→+` structure.

An example of where this is used is `linear_map.prod_equiv`.
-/


/- warning: smul_comm_class.symm -> SMulCommClass.symm is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (N : Type.{u2}) (α : Type.{u3}) [_inst_1 : HasSmul.{u1, u3} M α] [_inst_2 : HasSmul.{u2, u3} N α] [_inst_3 : SMulCommClass.{u1, u2, u3} M N α _inst_1 _inst_2], SMulCommClass.{u2, u1, u3} N M α _inst_2 _inst_1
but is expected to have type
  forall (M : Type.{u3}) (N : Type.{u2}) (α : Type.{u1}) [_inst_1 : SMul.{u3, u1} M α] [_inst_2 : SMul.{u2, u1} N α] [_inst_3 : SMulCommClass.{u3, u2, u1} M N α _inst_1 _inst_2], SMulCommClass.{u2, u3, u1} N M α _inst_2 _inst_1
Case conversion may be inaccurate. Consider using '#align smul_comm_class.symm SMulCommClass.symmₓ'. -/
/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
@[to_additive]
theorem SMulCommClass.symm (M N α : Type _) [HasSmul M α] [HasSmul N α] [SMulCommClass M N α] :
    SMulCommClass N M α :=
  ⟨fun a' a b => (smul_comm a a' b).symm⟩
#align smul_comm_class.symm SMulCommClass.symm

/-- Commutativity of additive actions is a symmetric relation. This lemma can't be an instance
because this would cause a loop in the instance search graph. -/
add_decl_doc VAddCommClass.symm

/- warning: smul_comm_class_self -> smulCommClass_self is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (CommMonoid.toMonoid.{u1} M _inst_1)], SMulCommClass.{u1, u1, u2} M M α (MulAction.toHasSmul.{u1, u2} M α (CommMonoid.toMonoid.{u1} M _inst_1) _inst_2) (MulAction.toHasSmul.{u1, u2} M α (CommMonoid.toMonoid.{u1} M _inst_1) _inst_2)
but is expected to have type
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (CommMonoid.toMonoid.{u1} M _inst_1)], SMulCommClass.{u1, u1, u2} M M α (MulAction.toSMul.{u1, u2} M α (CommMonoid.toMonoid.{u1} M _inst_1) _inst_2) (MulAction.toSMul.{u1, u2} M α (CommMonoid.toMonoid.{u1} M _inst_1) _inst_2)
Case conversion may be inaccurate. Consider using '#align smul_comm_class_self smulCommClass_selfₓ'. -/
@[to_additive]
instance smulCommClass_self (M α : Type _) [CommMonoid M] [MulAction M α] : SMulCommClass M M α :=
  ⟨fun a a' b => by rw [← mul_smul, mul_comm, mul_smul]⟩
#align smul_comm_class_self smulCommClass_self

#print VAddAssocClass /-
/-- An instance of `vadd_assoc_class M N α` states that the additive action of `M` on `α` is
determined by the additive actions of `M` on `N` and `N` on `α`. -/
class VAddAssocClass (M N α : Type _) [VAdd M N] [VAdd N α] [VAdd M α] : Prop where
  vadd_assoc : ∀ (x : M) (y : N) (z : α), x +ᵥ y +ᵥ z = x +ᵥ (y +ᵥ z)
#align vadd_assoc_class VAddAssocClass
-/

/- warning: is_scalar_tower -> IsScalarTower is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (N : Type.{u2}) (α : Type.{u3}) [_inst_1 : HasSmul.{u1, u2} M N] [_inst_2 : HasSmul.{u2, u3} N α] [_inst_3 : HasSmul.{u1, u3} M α], Prop
but is expected to have type
  forall (M : Type.{u1}) (N : Type.{u2}) (α : Type.{u3}) [_inst_1 : SMul.{u1, u2} M N] [_inst_2 : SMul.{u2, u3} N α] [_inst_3 : SMul.{u1, u3} M α], Prop
Case conversion may be inaccurate. Consider using '#align is_scalar_tower IsScalarTowerₓ'. -/
/-- An instance of `is_scalar_tower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
@[to_additive]
class IsScalarTower (M N α : Type _) [HasSmul M N] [HasSmul N α] [HasSmul M α] : Prop where
  smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • y • z
#align is_scalar_tower IsScalarTower

/- warning: smul_assoc -> smul_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : HasSmul.{u2, u3} M N] [_inst_2 : HasSmul.{u3, u1} N α] [_inst_3 : HasSmul.{u2, u1} M α] [_inst_4 : IsScalarTower.{u2, u3, u1} M N α _inst_1 _inst_2 _inst_3] (x : M) (y : N) (z : α), Eq.{succ u1} α (HasSmul.smul.{u3, u1} N α _inst_2 (HasSmul.smul.{u2, u3} M N _inst_1 x y) z) (HasSmul.smul.{u2, u1} M α _inst_3 x (HasSmul.smul.{u3, u1} N α _inst_2 y z))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : SMul.{u3, u2} M N] [_inst_2 : SMul.{u2, u1} N α] [_inst_3 : SMul.{u3, u1} M α] [_inst_4 : IsScalarTower.{u3, u2, u1} M N α _inst_1 _inst_2 _inst_3] (x : M) (y : N) (z : α), Eq.{succ u1} α (HSMul.hSMul.{u2, u1, u1} N α α (instHSMul.{u2, u1} N α _inst_2) (HSMul.hSMul.{u3, u2, u2} M N N (instHSMul.{u3, u2} M N _inst_1) x y) z) (HSMul.hSMul.{u3, u1, u1} M α α (instHSMul.{u3, u1} M α _inst_3) x (HSMul.hSMul.{u2, u1, u1} N α α (instHSMul.{u2, u1} N α _inst_2) y z))
Case conversion may be inaccurate. Consider using '#align smul_assoc smul_assocₓ'. -/
@[simp, to_additive]
theorem smul_assoc {M N} [HasSmul M N] [HasSmul N α] [HasSmul M α] [IsScalarTower M N α] (x : M)
    (y : N) (z : α) : (x • y) • z = x • y • z :=
  IsScalarTower.smul_assoc x y z
#align smul_assoc smul_assoc

/- warning: semigroup.is_scalar_tower -> Semigroup.isScalarTower is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α], IsScalarTower.{u1, u1, u1} α α α (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α], IsScalarTower.{u1, u1, u1} α α α (Mul.toSMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) (Mul.toSMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) (Mul.toSMul.{u1} α (Semigroup.toMul.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align semigroup.is_scalar_tower Semigroup.isScalarTowerₓ'. -/
@[to_additive]
instance Semigroup.isScalarTower [Semigroup α] : IsScalarTower α α α :=
  ⟨mul_assoc⟩
#align semigroup.is_scalar_tower Semigroup.isScalarTower

#print IsCentralVAdd /-
/-- A typeclass indicating that the right (aka `add_opposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `+ᵥ`. -/
class IsCentralVAdd (M α : Type _) [VAdd M α] [VAdd Mᵃᵒᵖ α] : Prop where
  op_vadd_eq_vadd : ∀ (m : M) (a : α), AddOpposite.op m +ᵥ a = m +ᵥ a
#align is_central_vadd IsCentralVAdd
-/

/- warning: is_central_scalar -> IsCentralScalar is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : HasSmul.{u1, u2} M α] [_inst_2 : HasSmul.{u1, u2} (MulOpposite.{u1} M) α], Prop
but is expected to have type
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : SMul.{u1, u2} (MulOpposite.{u1} M) α], Prop
Case conversion may be inaccurate. Consider using '#align is_central_scalar IsCentralScalarₓ'. -/
/-- A typeclass indicating that the right (aka `mul_opposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `•`. -/
@[to_additive]
class IsCentralScalar (M α : Type _) [HasSmul M α] [HasSmul Mᵐᵒᵖ α] : Prop where
  op_smul_eq_smul : ∀ (m : M) (a : α), MulOpposite.op m • a = m • a
#align is_central_scalar IsCentralScalar

/- warning: is_central_scalar.unop_smul_eq_smul -> IsCentralScalar.unop_smul_eq_smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] [_inst_2 : HasSmul.{u1, u2} (MulOpposite.{u1} M) α] [_inst_3 : IsCentralScalar.{u1, u2} M α _inst_1 _inst_2] (m : MulOpposite.{u1} M) (a : α), Eq.{succ u2} α (HasSmul.smul.{u1, u2} M α _inst_1 (MulOpposite.unop.{u1} M m) a) (HasSmul.smul.{u1, u2} (MulOpposite.{u1} M) α _inst_2 m a)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : SMul.{u2, u1} M α] [_inst_2 : SMul.{u2, u1} (MulOpposite.{u2} M) α] [_inst_3 : IsCentralScalar.{u2, u1} M α _inst_1 _inst_2] (m : MulOpposite.{u2} M) (a : α), Eq.{succ u1} α (HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α _inst_1) (MulOpposite.unop.{u2} M m) a) (HSMul.hSMul.{u2, u1, u1} (MulOpposite.{u2} M) α α (instHSMul.{u2, u1} (MulOpposite.{u2} M) α _inst_2) m a)
Case conversion may be inaccurate. Consider using '#align is_central_scalar.unop_smul_eq_smul IsCentralScalar.unop_smul_eq_smulₓ'. -/
@[to_additive]
theorem IsCentralScalar.unop_smul_eq_smul {M α : Type _} [HasSmul M α] [HasSmul Mᵐᵒᵖ α]
    [IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : MulOpposite.unop m • a = m • a :=
  MulOpposite.rec' (fun m => (IsCentralScalar.op_smul_eq_smul _ _).symm) m
#align is_central_scalar.unop_smul_eq_smul IsCentralScalar.unop_smul_eq_smul

export IsCentralVAdd (op_vadd_eq_vadd unop_vadd_eq_vadd)

export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)

/- warning: smul_comm_class.op_left -> SMulCommClass.op_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : HasSmul.{u1, u3} M α] [_inst_2 : HasSmul.{u1, u3} (MulOpposite.{u1} M) α] [_inst_3 : IsCentralScalar.{u1, u3} M α _inst_1 _inst_2] [_inst_4 : HasSmul.{u2, u3} N α] [_inst_5 : SMulCommClass.{u1, u2, u3} M N α _inst_1 _inst_4], SMulCommClass.{u1, u2, u3} (MulOpposite.{u1} M) N α _inst_2 _inst_4
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u3} (MulOpposite.{u1} M) α] [_inst_3 : IsCentralScalar.{u1, u3} M α _inst_1 _inst_2] [_inst_4 : SMul.{u2, u3} N α] [_inst_5 : SMulCommClass.{u1, u2, u3} M N α _inst_1 _inst_4], SMulCommClass.{u1, u2, u3} (MulOpposite.{u1} M) N α _inst_2 _inst_4
Case conversion may be inaccurate. Consider using '#align smul_comm_class.op_left SMulCommClass.op_leftₓ'. -/
-- these instances are very low priority, as there is usually a faster way to find these instances
@[to_additive]
instance (priority := 50) SMulCommClass.op_left [HasSmul M α] [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [HasSmul N α] [SMulCommClass M N α] : SMulCommClass Mᵐᵒᵖ N α :=
  ⟨fun m n a => by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m a, smul_comm]⟩
#align smul_comm_class.op_left SMulCommClass.op_left

/- warning: smul_comm_class.op_right -> SMulCommClass.op_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : HasSmul.{u1, u3} M α] [_inst_2 : HasSmul.{u2, u3} N α] [_inst_3 : HasSmul.{u2, u3} (MulOpposite.{u2} N) α] [_inst_4 : IsCentralScalar.{u2, u3} N α _inst_2 _inst_3] [_inst_5 : SMulCommClass.{u1, u2, u3} M N α _inst_1 _inst_2], SMulCommClass.{u1, u2, u3} M (MulOpposite.{u2} N) α _inst_1 _inst_3
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u2, u3} N α] [_inst_3 : SMul.{u2, u3} (MulOpposite.{u2} N) α] [_inst_4 : IsCentralScalar.{u2, u3} N α _inst_2 _inst_3] [_inst_5 : SMulCommClass.{u1, u2, u3} M N α _inst_1 _inst_2], SMulCommClass.{u1, u2, u3} M (MulOpposite.{u2} N) α _inst_1 _inst_3
Case conversion may be inaccurate. Consider using '#align smul_comm_class.op_right SMulCommClass.op_rightₓ'. -/
@[to_additive]
instance (priority := 50) SMulCommClass.op_right [HasSmul M α] [HasSmul N α] [HasSmul Nᵐᵒᵖ α]
    [IsCentralScalar N α] [SMulCommClass M N α] : SMulCommClass M Nᵐᵒᵖ α :=
  ⟨fun m n a => by rw [← unop_smul_eq_smul n (m • a), ← unop_smul_eq_smul n a, smul_comm]⟩
#align smul_comm_class.op_right SMulCommClass.op_right

/- warning: is_scalar_tower.op_left -> IsScalarTower.op_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : HasSmul.{u1, u3} M α] [_inst_2 : HasSmul.{u1, u3} (MulOpposite.{u1} M) α] [_inst_3 : IsCentralScalar.{u1, u3} M α _inst_1 _inst_2] [_inst_4 : HasSmul.{u1, u2} M N] [_inst_5 : HasSmul.{u1, u2} (MulOpposite.{u1} M) N] [_inst_6 : IsCentralScalar.{u1, u2} M N _inst_4 _inst_5] [_inst_7 : HasSmul.{u2, u3} N α] [_inst_8 : IsScalarTower.{u1, u2, u3} M N α _inst_4 _inst_7 _inst_1], IsScalarTower.{u1, u2, u3} (MulOpposite.{u1} M) N α _inst_5 _inst_7 _inst_2
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u3} (MulOpposite.{u1} M) α] [_inst_3 : IsCentralScalar.{u1, u3} M α _inst_1 _inst_2] [_inst_4 : SMul.{u1, u2} M N] [_inst_5 : SMul.{u1, u2} (MulOpposite.{u1} M) N] [_inst_6 : IsCentralScalar.{u1, u2} M N _inst_4 _inst_5] [_inst_7 : SMul.{u2, u3} N α] [_inst_8 : IsScalarTower.{u1, u2, u3} M N α _inst_4 _inst_7 _inst_1], IsScalarTower.{u1, u2, u3} (MulOpposite.{u1} M) N α _inst_5 _inst_7 _inst_2
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.op_left IsScalarTower.op_leftₓ'. -/
@[to_additive]
instance (priority := 50) IsScalarTower.op_left [HasSmul M α] [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [HasSmul M N] [HasSmul Mᵐᵒᵖ N] [IsCentralScalar M N] [HasSmul N α] [IsScalarTower M N α] :
    IsScalarTower Mᵐᵒᵖ N α :=
  ⟨fun m n a => by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m n, smul_assoc]⟩
#align is_scalar_tower.op_left IsScalarTower.op_left

/- warning: is_scalar_tower.op_right -> IsScalarTower.op_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : HasSmul.{u1, u3} M α] [_inst_2 : HasSmul.{u1, u2} M N] [_inst_3 : HasSmul.{u2, u3} N α] [_inst_4 : HasSmul.{u2, u3} (MulOpposite.{u2} N) α] [_inst_5 : IsCentralScalar.{u2, u3} N α _inst_3 _inst_4] [_inst_6 : IsScalarTower.{u1, u2, u3} M N α _inst_2 _inst_3 _inst_1], IsScalarTower.{u1, u2, u3} M (MulOpposite.{u2} N) α (MulOpposite.hasSmul.{u2, u1} N M _inst_2) _inst_4 _inst_1
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u2} M N] [_inst_3 : SMul.{u2, u3} N α] [_inst_4 : SMul.{u2, u3} (MulOpposite.{u2} N) α] [_inst_5 : IsCentralScalar.{u2, u3} N α _inst_3 _inst_4] [_inst_6 : IsScalarTower.{u1, u2, u3} M N α _inst_2 _inst_3 _inst_1], IsScalarTower.{u1, u2, u3} M (MulOpposite.{u2} N) α (MulOpposite.instSMulMulOpposite.{u2, u1} N M _inst_2) _inst_4 _inst_1
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.op_right IsScalarTower.op_rightₓ'. -/
@[to_additive]
instance (priority := 50) IsScalarTower.op_right [HasSmul M α] [HasSmul M N] [HasSmul N α]
    [HasSmul Nᵐᵒᵖ α] [IsCentralScalar N α] [IsScalarTower M N α] : IsScalarTower M Nᵐᵒᵖ α :=
  ⟨fun m n a => by
    rw [← unop_smul_eq_smul n a, ← unop_smul_eq_smul (m • n) a, MulOpposite.unop_smul, smul_assoc]⟩
#align is_scalar_tower.op_right IsScalarTower.op_right

namespace HasSmul

variable [HasSmul M α]

/- warning: has_smul.comp.smul -> SMul.comp.smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : HasSmul.{u1, u3} M α], (N -> M) -> N -> α -> α
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : SMul.{u1, u3} M α], (N -> M) -> N -> α -> α
Case conversion may be inaccurate. Consider using '#align has_smul.comp.smul SMul.comp.smulₓ'. -/
/-- Auxiliary definition for `has_smul.comp`, `mul_action.comp_hom`,
`distrib_mul_action.comp_hom`, `module.comp_hom`, etc. -/
@[simp, to_additive " Auxiliary definition for `has_vadd.comp`, `add_action.comp_hom`, etc. "]
def comp.smul (g : N → M) (n : N) (a : α) : α :=
  g n • a
#align has_smul.comp.smul SMul.comp.smul

variable (α)

/- warning: has_smul.comp -> SMul.comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} (α : Type.{u3}) [_inst_1 : HasSmul.{u1, u3} M α], (N -> M) -> (HasSmul.{u2, u3} N α)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} (α : Type.{u3}) [_inst_1 : SMul.{u1, u3} M α], (N -> M) -> (SMul.{u2, u3} N α)
Case conversion may be inaccurate. Consider using '#align has_smul.comp SMul.compₓ'. -/
/-- An action of `M` on `α` and a function `N → M` induces an action of `N` on `α`.

See note [reducible non-instances]. Since this is reducible, we make sure to go via
`has_smul.comp.smul` to prevent typeclass inference unfolding too far. -/
@[reducible,
  to_additive
      " An additive action of `M` on `α` and a function `N → M` induces\n  an additive action of `N` on `α` "]
def comp (g : N → M) : HasSmul N α where smul := SMul.comp.smul g
#align has_smul.comp SMul.comp

variable {α}

/- warning: has_smul.comp.is_scalar_tower -> SMul.comp.isScalarTower is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : HasSmul.{u1, u3} M α] [_inst_2 : HasSmul.{u1, u4} M β] [_inst_3 : HasSmul.{u3, u4} α β] [_inst_4 : IsScalarTower.{u1, u3, u4} M α β _inst_1 _inst_3 _inst_2] (g : N -> M), IsScalarTower.{u2, u3, u4} N α β (SMul.comp.{u1, u2, u3} M N α _inst_1 g) _inst_3 (SMul.comp.{u1, u2, u4} M N β _inst_2 g)
but is expected to have type
  forall {M : Type.{u4}} {N : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u4, u2} M α] [_inst_2 : SMul.{u4, u3} M β] [_inst_3 : SMul.{u2, u3} α β] [_inst_4 : IsScalarTower.{u4, u2, u3} M α β _inst_1 _inst_3 _inst_2] (g : N -> M), IsScalarTower.{u1, u2, u3} N α β (SMul.comp.{u4, u1, u2} M N α _inst_1 g) _inst_3 (SMul.comp.{u4, u1, u3} M N β _inst_2 g)
Case conversion may be inaccurate. Consider using '#align has_smul.comp.is_scalar_tower SMul.comp.isScalarTowerₓ'. -/
/-- Given a tower of scalar actions `M → α → β`, if we use `has_smul.comp`
to pull back both of `M`'s actions by a map `g : N → M`, then we obtain a new
tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `has_smul` arguments
are still metavariables.
-/
@[to_additive
      "Given a tower of additive actions `M → α → β`, if we use\n`has_smul.comp` to pull back both of `M`'s actions by a map `g : N → M`, then we obtain a new tower\nof scalar actions `N → α → β`.\n\nThis cannot be an instance because it can cause infinite loops whenever the `has_smul` arguments\nare still metavariables."]
theorem comp.isScalarTower [HasSmul M β] [HasSmul α β] [IsScalarTower M α β] (g : N → M) : by
    haveI := comp α g <;> haveI := comp β g <;> exact IsScalarTower N α β :=
  { smul_assoc := fun n => @smul_assoc _ _ _ _ _ _ _ (g n) }
#align has_smul.comp.is_scalar_tower SMul.comp.isScalarTower

/- warning: has_smul.comp.smul_comm_class -> SMul.comp.smulCommClass is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : HasSmul.{u1, u3} M α] [_inst_2 : HasSmul.{u4, u3} β α] [_inst_3 : SMulCommClass.{u1, u4, u3} M β α _inst_1 _inst_2] (g : N -> M), SMulCommClass.{u2, u4, u3} N β α (SMul.comp.{u1, u2, u3} M N α _inst_1 g) _inst_2
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : SMul.{u2, u3} M α] [_inst_2 : SMul.{u4, u3} β α] [_inst_3 : SMulCommClass.{u2, u4, u3} M β α _inst_1 _inst_2] (g : N -> M), SMulCommClass.{u1, u4, u3} N β α (SMul.comp.{u2, u1, u3} M N α _inst_1 g) _inst_2
Case conversion may be inaccurate. Consider using '#align has_smul.comp.smul_comm_class SMul.comp.smulCommClassₓ'. -/
/-- This cannot be an instance because it can cause infinite loops whenever the `has_smul` arguments
are still metavariables.
-/
@[to_additive
      "This cannot be an instance because it can cause infinite loops whenever\nthe `has_vadd` arguments are still metavariables."]
theorem comp.smulCommClass [HasSmul β α] [SMulCommClass M β α] (g : N → M) :
    haveI := comp α g
    SMulCommClass N β α :=
  { smul_comm := fun n => @smul_comm _ _ _ _ _ _ (g n) }
#align has_smul.comp.smul_comm_class SMul.comp.smulCommClass

/- warning: has_smul.comp.smul_comm_class' -> SMul.comp.smulCommClass' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : HasSmul.{u1, u3} M α] [_inst_2 : HasSmul.{u4, u3} β α] [_inst_3 : SMulCommClass.{u4, u1, u3} β M α _inst_2 _inst_1] (g : N -> M), SMulCommClass.{u4, u2, u3} β N α _inst_2 (SMul.comp.{u1, u2, u3} M N α _inst_1 g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : SMul.{u2, u3} M α] [_inst_2 : SMul.{u4, u3} β α] [_inst_3 : SMulCommClass.{u4, u2, u3} β M α _inst_2 _inst_1] (g : N -> M), SMulCommClass.{u4, u1, u3} β N α _inst_2 (SMul.comp.{u2, u1, u3} M N α _inst_1 g)
Case conversion may be inaccurate. Consider using '#align has_smul.comp.smul_comm_class' SMul.comp.smulCommClass'ₓ'. -/
/-- This cannot be an instance because it can cause infinite loops whenever the `has_smul` arguments
are still metavariables.
-/
@[to_additive
      "This cannot be an instance because it can cause infinite loops whenever\nthe `has_vadd` arguments are still metavariables."]
theorem comp.smulCommClass' [HasSmul β α] [SMulCommClass β M α] (g : N → M) :
    haveI := comp α g
    SMulCommClass β N α :=
  { smul_comm := fun _ n => @smul_comm _ _ _ _ _ _ _ (g n) }
#align has_smul.comp.smul_comm_class' SMul.comp.smulCommClass'

end HasSmul

section

/- warning: mul_smul_comm -> mul_smul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] [_inst_2 : HasSmul.{u1, u2} α β] [_inst_3 : SMulCommClass.{u1, u2, u2} α β β _inst_2 (Mul.toSMul.{u2} β _inst_1)] (s : α) (x : β) (y : β), Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_1) x (HasSmul.smul.{u1, u2} α β _inst_2 s y)) (HasSmul.smul.{u1, u2} α β _inst_2 s (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_1) x y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] [_inst_2 : SMul.{u1, u2} α β] [_inst_3 : SMulCommClass.{u1, u2, u2} α β β _inst_2 (Mul.toSMul.{u2} β _inst_1)] (s : α) (x : β) (y : β), Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_1) x (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β _inst_2) s y)) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β _inst_2) s (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_1) x y))
Case conversion may be inaccurate. Consider using '#align mul_smul_comm mul_smul_commₓ'. -/
/-- Note that the `smul_comm_class α β β` typeclass argument is usually satisfied by `algebra α β`.
-/
@[to_additive, nolint to_additive_doc]
theorem mul_smul_comm [Mul β] [HasSmul α β] [SMulCommClass α β β] (s : α) (x y : β) :
    x * s • y = s • (x * y) :=
  (smul_comm s x y).symm
#align mul_smul_comm mul_smul_comm

/- warning: smul_mul_assoc -> smul_mul_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] [_inst_2 : HasSmul.{u1, u2} α β] [_inst_3 : IsScalarTower.{u1, u2, u2} α β β _inst_2 (Mul.toSMul.{u2} β _inst_1) _inst_2] (r : α) (x : β) (y : β), Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_1) (HasSmul.smul.{u1, u2} α β _inst_2 r x) y) (HasSmul.smul.{u1, u2} α β _inst_2 r (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_1) x y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] [_inst_2 : SMul.{u1, u2} α β] [_inst_3 : IsScalarTower.{u1, u2, u2} α β β _inst_2 (Mul.toSMul.{u2} β _inst_1) _inst_2] (r : α) (x : β) (y : β), Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_1) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β _inst_2) r x) y) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β _inst_2) r (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_1) x y))
Case conversion may be inaccurate. Consider using '#align smul_mul_assoc smul_mul_assocₓ'. -/
/-- Note that the `is_scalar_tower α β β` typeclass argument is usually satisfied by `algebra α β`.
-/
@[to_additive, nolint to_additive_doc]
theorem smul_mul_assoc [Mul β] [HasSmul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x * y = r • (x * y) :=
  smul_assoc r x y
#align smul_mul_assoc smul_mul_assoc

/- warning: smul_smul_smul_comm -> smul_smul_smul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : HasSmul.{u1, u2} α β] [_inst_2 : HasSmul.{u1, u3} α γ] [_inst_3 : HasSmul.{u2, u4} β δ] [_inst_4 : HasSmul.{u1, u4} α δ] [_inst_5 : HasSmul.{u3, u4} γ δ] [_inst_6 : IsScalarTower.{u1, u2, u4} α β δ _inst_1 _inst_3 _inst_4] [_inst_7 : IsScalarTower.{u1, u3, u4} α γ δ _inst_2 _inst_5 _inst_4] [_inst_8 : SMulCommClass.{u2, u3, u4} β γ δ _inst_3 _inst_5] (a : α) (b : β) (c : γ) (d : δ), Eq.{succ u4} δ (HasSmul.smul.{u2, u4} β δ _inst_3 (HasSmul.smul.{u1, u2} α β _inst_1 a b) (HasSmul.smul.{u3, u4} γ δ _inst_5 c d)) (HasSmul.smul.{u3, u4} γ δ _inst_5 (HasSmul.smul.{u1, u3} α γ _inst_2 a c) (HasSmul.smul.{u2, u4} β δ _inst_3 b d))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : SMul.{u4, u3} α β] [_inst_2 : SMul.{u4, u2} α γ] [_inst_3 : SMul.{u3, u1} β δ] [_inst_4 : SMul.{u4, u1} α δ] [_inst_5 : SMul.{u2, u1} γ δ] [_inst_6 : IsScalarTower.{u4, u3, u1} α β δ _inst_1 _inst_3 _inst_4] [_inst_7 : IsScalarTower.{u4, u2, u1} α γ δ _inst_2 _inst_5 _inst_4] [_inst_8 : SMulCommClass.{u3, u2, u1} β γ δ _inst_3 _inst_5] (a : α) (b : β) (c : γ) (d : δ), Eq.{succ u1} δ (HSMul.hSMul.{u3, u1, u1} β δ δ (instHSMul.{u3, u1} β δ _inst_3) (HSMul.hSMul.{u4, u3, u3} α β β (instHSMul.{u4, u3} α β _inst_1) a b) (HSMul.hSMul.{u2, u1, u1} γ δ δ (instHSMul.{u2, u1} γ δ _inst_5) c d)) (HSMul.hSMul.{u2, u1, u1} γ δ δ (instHSMul.{u2, u1} γ δ _inst_5) (HSMul.hSMul.{u4, u2, u2} α γ γ (instHSMul.{u4, u2} α γ _inst_2) a c) (HSMul.hSMul.{u3, u1, u1} β δ δ (instHSMul.{u3, u1} β δ _inst_3) b d))
Case conversion may be inaccurate. Consider using '#align smul_smul_smul_comm smul_smul_smul_commₓ'. -/
@[to_additive]
theorem smul_smul_smul_comm [HasSmul α β] [HasSmul α γ] [HasSmul β δ] [HasSmul α δ] [HasSmul γ δ]
    [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommClass β γ δ] (a : α) (b : β) (c : γ)
    (d : δ) : (a • b) • c • d = (a • c) • b • d :=
  by
  rw [smul_assoc, smul_assoc, smul_comm b]
  infer_instance
#align smul_smul_smul_comm smul_smul_smul_comm

variable [HasSmul M α]

/- warning: commute.smul_right -> Commute.smul_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] [_inst_2 : Mul.{u2} α] [_inst_3 : SMulCommClass.{u1, u2, u2} M α α _inst_1 (Mul.toSMul.{u2} α _inst_2)] [_inst_4 : IsScalarTower.{u1, u2, u2} M α α _inst_1 (Mul.toSMul.{u2} α _inst_2) _inst_1] {a : α} {b : α}, (Commute.{u2} α _inst_2 a b) -> (forall (r : M), Commute.{u2} α _inst_2 a (HasSmul.smul.{u1, u2} M α _inst_1 r b))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : Mul.{u2} α] [_inst_3 : SMulCommClass.{u1, u2, u2} M α α _inst_1 (Mul.toSMul.{u2} α _inst_2)] [_inst_4 : IsScalarTower.{u1, u2, u2} M α α _inst_1 (Mul.toSMul.{u2} α _inst_2) _inst_1] {a : α} {b : α}, (Commute.{u2} α _inst_2 a b) -> (forall (r : M), Commute.{u2} α _inst_2 a (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) r b))
Case conversion may be inaccurate. Consider using '#align commute.smul_right Commute.smul_rightₓ'. -/
@[to_additive]
theorem Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute a (r • b) :=
  (mul_smul_comm _ _ _).trans ((congr_arg _ h).trans <| (smul_mul_assoc _ _ _).symm)
#align commute.smul_right Commute.smul_right

/- warning: commute.smul_left -> Commute.smul_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] [_inst_2 : Mul.{u2} α] [_inst_3 : SMulCommClass.{u1, u2, u2} M α α _inst_1 (Mul.toSMul.{u2} α _inst_2)] [_inst_4 : IsScalarTower.{u1, u2, u2} M α α _inst_1 (Mul.toSMul.{u2} α _inst_2) _inst_1] {a : α} {b : α}, (Commute.{u2} α _inst_2 a b) -> (forall (r : M), Commute.{u2} α _inst_2 (HasSmul.smul.{u1, u2} M α _inst_1 r a) b)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : Mul.{u2} α] [_inst_3 : SMulCommClass.{u1, u2, u2} M α α _inst_1 (Mul.toSMul.{u2} α _inst_2)] [_inst_4 : IsScalarTower.{u1, u2, u2} M α α _inst_1 (Mul.toSMul.{u2} α _inst_2) _inst_1] {a : α} {b : α}, (Commute.{u2} α _inst_2 a b) -> (forall (r : M), Commute.{u2} α _inst_2 (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) r a) b)
Case conversion may be inaccurate. Consider using '#align commute.smul_left Commute.smul_leftₓ'. -/
@[to_additive]
theorem Commute.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute (r • a) b :=
  (h.symm.smul_right r).symm
#align commute.smul_left Commute.smul_left

end

section ite

variable [HasSmul M α] (p : Prop) [Decidable p]

/- warning: ite_smul -> ite_smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] (p : Prop) [_inst_2 : Decidable p] (a₁ : M) (a₂ : M) (b : α), Eq.{succ u2} α (HasSmul.smul.{u1, u2} M α _inst_1 (ite.{succ u1} M p _inst_2 a₁ a₂) b) (ite.{succ u2} α p _inst_2 (HasSmul.smul.{u1, u2} M α _inst_1 a₁ b) (HasSmul.smul.{u1, u2} M α _inst_1 a₂ b))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u1, u2} M α] (p : Prop) [_inst_2 : Decidable p] (a₁ : M) (a₂ : M) (b : α), Eq.{succ u2} α (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) (ite.{succ u1} M p _inst_2 a₁ a₂) b) (ite.{succ u2} α p _inst_2 (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) a₁ b) (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) a₂ b))
Case conversion may be inaccurate. Consider using '#align ite_smul ite_smulₓ'. -/
@[to_additive]
theorem ite_smul (a₁ a₂ : M) (b : α) : ite p a₁ a₂ • b = ite p (a₁ • b) (a₂ • b) := by
  split_ifs <;> rfl
#align ite_smul ite_smul

/- warning: smul_ite -> smul_ite is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] (p : Prop) [_inst_2 : Decidable p] (a : M) (b₁ : α) (b₂ : α), Eq.{succ u2} α (HasSmul.smul.{u1, u2} M α _inst_1 a (ite.{succ u2} α p _inst_2 b₁ b₂)) (ite.{succ u2} α p _inst_2 (HasSmul.smul.{u1, u2} M α _inst_1 a b₁) (HasSmul.smul.{u1, u2} M α _inst_1 a b₂))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u1, u2} M α] (p : Prop) [_inst_2 : Decidable p] (a : M) (b₁ : α) (b₂ : α), Eq.{succ u2} α (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) a (ite.{succ u2} α p _inst_2 b₁ b₂)) (ite.{succ u2} α p _inst_2 (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) a b₁) (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) a b₂))
Case conversion may be inaccurate. Consider using '#align smul_ite smul_iteₓ'. -/
@[to_additive]
theorem smul_ite (a : M) (b₁ b₂ : α) : a • ite p b₁ b₂ = ite p (a • b₁) (a • b₂) := by
  split_ifs <;> rfl
#align smul_ite smul_ite

end ite

section

variable [Monoid M] [MulAction M α]

/- warning: smul_smul -> smul_smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] (a₁ : M) (a₂ : M) (b : α), Eq.{succ u2} α (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) a₁ (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) a₂ b)) (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a₁ a₂) b)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] (a₁ : M) (a₂ : M) (b : α), Eq.{succ u2} α (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) a₁ (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) a₂ b)) (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a₁ a₂) b)
Case conversion may be inaccurate. Consider using '#align smul_smul smul_smulₓ'. -/
@[to_additive]
theorem smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b :=
  (mul_smul _ _ _).symm
#align smul_smul smul_smul

variable (M)

/- warning: one_smul -> one_smul is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] (b : α), Eq.{succ u2} α (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) b) b
but is expected to have type
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] (b : α), Eq.{succ u2} α (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))) b) b
Case conversion may be inaccurate. Consider using '#align one_smul one_smulₓ'. -/
@[simp, to_additive]
theorem one_smul (b : α) : (1 : M) • b = b :=
  MulAction.one_smul _
#align one_smul one_smul

/- warning: one_smul_eq_id -> one_smul_eq_id is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1], Eq.{succ u2} (α -> α) (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (id.{succ u2} α)
but is expected to have type
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1], Eq.{succ u2} (α -> α) ((fun (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2767 : M) (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2769 : α) => HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2767 x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2769) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) (id.{succ u2} α)
Case conversion may be inaccurate. Consider using '#align one_smul_eq_id one_smul_eq_idₓ'. -/
/-- `has_smul` version of `one_mul_eq_id` -/
@[to_additive "`has_vadd` version of `zero_add_eq_id`"]
theorem one_smul_eq_id : ((· • ·) (1 : M) : α → α) = id :=
  funext <| one_smul _
#align one_smul_eq_id one_smul_eq_id

/- warning: comp_smul_left -> comp_smul_left is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] (a₁ : M) (a₂ : M), Eq.{succ u2} (α -> α) (Function.comp.{succ u2, succ u2, succ u2} α α α (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) a₁) (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) a₂)) (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a₁ a₂))
but is expected to have type
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] (a₁ : M) (a₂ : M), Eq.{succ u2} (α -> α) (Function.comp.{succ u2, succ u2, succ u2} α α α ((fun (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2820 : M) (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2822 : α) => HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2820 x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2822) a₁) ((fun (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2837 : M) (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2839 : α) => HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2837 x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2839) a₂)) ((fun (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2860 : M) (x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2862 : α) => HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2860 x._@.Mathlib.GroupTheory.GroupAction.Defs._hyg.2862) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a₁ a₂))
Case conversion may be inaccurate. Consider using '#align comp_smul_left comp_smul_leftₓ'. -/
/-- `has_smul` version of `comp_mul_left` -/
@[to_additive "`has_vadd` version of `comp_add_left`"]
theorem comp_smul_left (a₁ a₂ : M) : (· • ·) a₁ ∘ (· • ·) a₂ = ((· • ·) (a₁ * a₂) : α → α) :=
  funext fun _ => (mul_smul _ _ _).symm
#align comp_smul_left comp_smul_left

variable {M}

/- warning: function.injective.mul_action -> Function.Injective.mulAction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] [_inst_3 : HasSmul.{u1, u3} M β] (f : β -> α), (Function.Injective.{succ u3, succ u2} β α f) -> (forall (c : M) (x : β), Eq.{succ u2} α (f (HasSmul.smul.{u1, u3} M β _inst_3 c x)) (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) c (f x))) -> (MulAction.{u1, u3} M β _inst_1)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] [_inst_3 : SMul.{u1, u3} M β] (f : β -> α), (Function.Injective.{succ u3, succ u2} β α f) -> (forall (c : M) (x : β), Eq.{succ u2} α (f (HSMul.hSMul.{u1, u3, u3} M β β (instHSMul.{u1, u3} M β _inst_3) c x)) (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) c (f x))) -> (MulAction.{u1, u3} M β _inst_1)
Case conversion may be inaccurate. Consider using '#align function.injective.mul_action Function.Injective.mulActionₓ'. -/
/-- Pullback a multiplicative action along an injective map respecting `•`.
See note [reducible non-instances]. -/
@[reducible, to_additive "Pullback an additive action along an injective map respecting `+ᵥ`."]
protected def Function.Injective.mulAction [HasSmul M β] (f : β → α) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β
    where
  smul := (· • ·)
  one_smul x := hf <| (smul _ _).trans <| one_smul _ (f x)
  mul_smul c₁ c₂ x := hf <| by simp only [smul, mul_smul]
#align function.injective.mul_action Function.Injective.mulAction

/- warning: function.surjective.mul_action -> Function.Surjective.mulAction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] [_inst_3 : HasSmul.{u1, u3} M β] (f : α -> β), (Function.Surjective.{succ u2, succ u3} α β f) -> (forall (c : M) (x : α), Eq.{succ u3} β (f (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) c x)) (HasSmul.smul.{u1, u3} M β _inst_3 c (f x))) -> (MulAction.{u1, u3} M β _inst_1)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] [_inst_3 : SMul.{u1, u3} M β] (f : α -> β), (Function.Surjective.{succ u2, succ u3} α β f) -> (forall (c : M) (x : α), Eq.{succ u3} β (f (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) c x)) (HSMul.hSMul.{u1, u3, u3} M β β (instHSMul.{u1, u3} M β _inst_3) c (f x))) -> (MulAction.{u1, u3} M β _inst_1)
Case conversion may be inaccurate. Consider using '#align function.surjective.mul_action Function.Surjective.mulActionₓ'. -/
/-- Pushforward a multiplicative action along a surjective map respecting `•`.
See note [reducible non-instances]. -/
@[reducible, to_additive "Pushforward an additive action along a surjective map respecting `+ᵥ`."]
protected def Function.Surjective.mulAction [HasSmul M β] (f : α → β) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β
    where
  smul := (· • ·)
  one_smul y := by
    rcases hf y with ⟨x, rfl⟩
    rw [← smul, one_smul]
  mul_smul c₁ c₂ y := by
    rcases hf y with ⟨x, rfl⟩
    simp only [← smul, mul_smul]
#align function.surjective.mul_action Function.Surjective.mulAction

/- warning: function.surjective.mul_action_left -> Function.Surjective.mulActionLeft is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} [_inst_3 : Monoid.{u1} R] [_inst_4 : MulAction.{u1, u3} R M _inst_3] [_inst_5 : Monoid.{u2} S] [_inst_6 : HasSmul.{u2, u3} S M] (f : MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)), (Function.Surjective.{succ u1, succ u2} R S (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) (fun (_x : MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) => R -> S) (MonoidHom.hasCoeToFun.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) f)) -> (forall (c : R) (x : M), Eq.{succ u3} M (HasSmul.smul.{u2, u3} S M _inst_6 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) (fun (_x : MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) => R -> S) (MonoidHom.hasCoeToFun.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) f c) x) (HasSmul.smul.{u1, u3} R M (MulAction.toHasSmul.{u1, u3} R M _inst_3 _inst_4) c x)) -> (MulAction.{u2, u3} S M _inst_5)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} [_inst_3 : Monoid.{u1} R] [_inst_4 : MulAction.{u1, u3} R M _inst_3] [_inst_5 : Monoid.{u2} S] [_inst_6 : SMul.{u2, u3} S M] (f : MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)), (Function.Surjective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) R S (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_3)) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_5)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5) (MonoidHom.monoidHomClass.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)))) f)) -> (forall (c : R) (x : M), Eq.{succ u3} M (HSMul.hSMul.{u2, u3, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) c) M M (instHSMul.{u2, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) c) M _inst_6) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) R S (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_3)) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_5)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)) R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5) (MonoidHom.monoidHomClass.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_3) (Monoid.toMulOneClass.{u2} S _inst_5)))) f c) x) (HSMul.hSMul.{u1, u3, u3} R M M (instHSMul.{u1, u3} R M (MulAction.toSMul.{u1, u3} R M _inst_3 _inst_4)) c x)) -> (MulAction.{u2, u3} S M _inst_5)
Case conversion may be inaccurate. Consider using '#align function.surjective.mul_action_left Function.Surjective.mulActionLeftₓ'. -/
/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `function.surjective.distrib_mul_action_left` and `function.surjective.module_left`.
-/
@[reducible,
  to_additive
      "Push forward the action of `R` on `M` along a compatible\nsurjective map `f : R →+ S`."]
def Function.Surjective.mulActionLeft {R S M : Type _} [Monoid R] [MulAction R M] [Monoid S]
    [HasSmul S M] (f : R →* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : MulAction S M
    where
  smul := (· • ·)
  one_smul b := by rw [← f.map_one, hsmul, one_smul]
  mul_smul := hf.Forall₂.mpr fun a b x => by simp only [← f.map_mul, hsmul, mul_smul]
#align function.surjective.mul_action_left Function.Surjective.mulActionLeft

section

variable (M)

#print Monoid.toMulAction /-
-- see Note [lower instance priority]
/-- The regular action of a monoid on itself by left multiplication.

This is promoted to a module by `semiring.to_module`. -/
@[to_additive]
instance (priority := 910) Monoid.toMulAction : MulAction M M
    where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := mul_assoc
#align monoid.to_mul_action Monoid.toMulAction
-/

/-- The regular action of a monoid on itself by left addition.

This is promoted to an `add_torsor` by `add_group_is_add_torsor`. -/
add_decl_doc AddMonoid.toAddAction

/- warning: is_scalar_tower.left -> IsScalarTower.left is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1], IsScalarTower.{u1, u1, u2} M M α (Mul.toSMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2)
but is expected to have type
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1], IsScalarTower.{u1, u1, u2} M M α (MulAction.toSMul.{u1, u1} M M _inst_1 (Monoid.toMulAction.{u1} M _inst_1)) (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2) (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.left IsScalarTower.leftₓ'. -/
@[to_additive]
instance IsScalarTower.left : IsScalarTower M M α :=
  ⟨fun x y z => mul_smul x y z⟩
#align is_scalar_tower.left IsScalarTower.left

variable {M}

/- warning: smul_mul_smul -> smul_mul_smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] [_inst_3 : Mul.{u2} α] (r : M) (s : M) (x : α) (y : α) [_inst_4 : IsScalarTower.{u1, u2, u2} M α α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) (Mul.toSMul.{u2} α _inst_3) (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2)] [_inst_5 : SMulCommClass.{u1, u2, u2} M α α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) (Mul.toSMul.{u2} α _inst_3)], Eq.{succ u2} α (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_3) (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) r x) (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) s y)) (HasSmul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) r s) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_3) x y))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] [_inst_3 : Mul.{u2} α] (r : M) (s : M) (x : α) (y : α) [_inst_4 : IsScalarTower.{u1, u2, u2} M α α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2) (Mul.toSMul.{u2} α _inst_3) (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)] [_inst_5 : SMulCommClass.{u1, u2, u2} M α α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2) (Mul.toSMul.{u2} α _inst_3)], Eq.{succ u2} α (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_3) (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) r x) (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) s y)) (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) r s) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_3) x y))
Case conversion may be inaccurate. Consider using '#align smul_mul_smul smul_mul_smulₓ'. -/
/-- Note that the `is_scalar_tower M α α` and `smul_comm_class M α α` typeclass arguments are
usually satisfied by `algebra M α`. -/
@[to_additive, nolint to_additive_doc]
theorem smul_mul_smul [Mul α] (r s : M) (x y : α) [IsScalarTower M α α] [SMulCommClass M α α] :
    r • x * s • y = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_assoc, smul_eq_mul]
#align smul_mul_smul smul_mul_smul

end

namespace MulAction

variable (M α)

#print MulAction.toFun /-
/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive]
def toFun : α ↪ M → α :=
  ⟨fun y x => x • y, fun y₁ y₂ H => one_smul M y₁ ▸ one_smul M y₂ ▸ by convert congr_fun H 1⟩
#align mul_action.to_fun MulAction.toFun
-/

/-- Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`. -/
add_decl_doc AddAction.toFun

variable {M α}

#print MulAction.toFun_apply /-
@[simp, to_additive]
theorem toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y :=
  rfl
#align mul_action.to_fun_apply MulAction.toFun_apply
-/

variable (α)

#print MulAction.compHom /-
/-- A multiplicative action of `M` on `α` and a monoid homomorphism `N → M` induce
a multiplicative action of `N` on `α`.

See note [reducible non-instances]. -/
@[reducible, to_additive]
def compHom [Monoid N] (g : N →* M) : MulAction N α
    where
  smul := SMul.comp.smul g
  one_smul := by simp [g.map_one, MulAction.one_smul]
  mul_smul := by simp [g.map_mul, MulAction.mul_smul]
#align mul_action.comp_hom MulAction.compHom
-/

/-- An additive action of `M` on `α` and an additive monoid homomorphism `N → M` induce
an additive action of `N` on `α`.

See note [reducible non-instances]. -/
add_decl_doc AddAction.compHom

end MulAction

end

section CompatibleScalar

/- warning: smul_one_smul -> smul_one_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} (N : Type.{u3}) [_inst_1 : Monoid.{u3} N] [_inst_2 : HasSmul.{u2, u3} M N] [_inst_3 : MulAction.{u3, u1} N α _inst_1] [_inst_4 : HasSmul.{u2, u1} M α] [_inst_5 : IsScalarTower.{u2, u3, u1} M N α _inst_2 (MulAction.toHasSmul.{u3, u1} N α _inst_1 _inst_3) _inst_4] (x : M) (y : α), Eq.{succ u1} α (HasSmul.smul.{u3, u1} N α (MulAction.toHasSmul.{u3, u1} N α _inst_1 _inst_3) (HasSmul.smul.{u2, u3} M N _inst_2 x (OfNat.ofNat.{u3} N 1 (OfNat.mk.{u3} N 1 (One.one.{u3} N (MulOneClass.toHasOne.{u3} N (Monoid.toMulOneClass.{u3} N _inst_1)))))) y) (HasSmul.smul.{u2, u1} M α _inst_4 x y)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} (N : Type.{u2}) [_inst_1 : Monoid.{u2} N] [_inst_2 : SMul.{u3, u2} M N] [_inst_3 : MulAction.{u2, u1} N α _inst_1] [_inst_4 : SMul.{u3, u1} M α] [_inst_5 : IsScalarTower.{u3, u2, u1} M N α _inst_2 (MulAction.toSMul.{u2, u1} N α _inst_1 _inst_3) _inst_4] (x : M) (y : α), Eq.{succ u1} α (HSMul.hSMul.{u2, u1, u1} N α α (instHSMul.{u2, u1} N α (MulAction.toSMul.{u2, u1} N α _inst_1 _inst_3)) (HSMul.hSMul.{u3, u2, u2} M N N (instHSMul.{u3, u2} M N _inst_2) x (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N (Monoid.toOne.{u2} N _inst_1)))) y) (HSMul.hSMul.{u3, u1, u1} M α α (instHSMul.{u3, u1} M α _inst_4) x y)
Case conversion may be inaccurate. Consider using '#align smul_one_smul smul_one_smulₓ'. -/
@[simp, to_additive]
theorem smul_one_smul {M} (N) [Monoid N] [HasSmul M N] [MulAction N α] [HasSmul M α]
    [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc, one_smul]
#align smul_one_smul smul_one_smul

/- warning: smul_one_mul -> smul_one_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u2} N] [_inst_2 : HasSmul.{u1, u2} M N] [_inst_3 : IsScalarTower.{u1, u2, u2} M N N _inst_2 (Mul.toSMul.{u2} N (MulOneClass.toHasMul.{u2} N _inst_1)) _inst_2] (x : M) (y : N), Eq.{succ u2} N (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N _inst_1)) (HasSmul.smul.{u1, u2} M N _inst_2 x (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_1))))) y) (HasSmul.smul.{u1, u2} M N _inst_2 x y)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u1} N] [_inst_2 : SMul.{u2, u1} M N] [_inst_3 : IsScalarTower.{u2, u1, u1} M N N _inst_2 (Mul.toSMul.{u1} N (MulOneClass.toMul.{u1} N _inst_1)) _inst_2] (x : M) (y : N), Eq.{succ u1} N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N _inst_1)) (HSMul.hSMul.{u2, u1, u1} M N N (instHSMul.{u2, u1} M N _inst_2) x (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (MulOneClass.toOne.{u1} N _inst_1)))) y) (HSMul.hSMul.{u2, u1, u1} M N N (instHSMul.{u2, u1} M N _inst_2) x y)
Case conversion may be inaccurate. Consider using '#align smul_one_mul smul_one_mulₓ'. -/
@[simp, to_additive]
theorem smul_one_mul {M N} [MulOneClass N] [HasSmul M N] [IsScalarTower M N N] (x : M) (y : N) :
    x • 1 * y = x • y := by rw [smul_mul_assoc, one_mul]
#align smul_one_mul smul_one_mul

/- warning: mul_smul_one -> mul_smul_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u2} N] [_inst_2 : HasSmul.{u1, u2} M N] [_inst_3 : SMulCommClass.{u1, u2, u2} M N N _inst_2 (Mul.toSMul.{u2} N (MulOneClass.toHasMul.{u2} N _inst_1))] (x : M) (y : N), Eq.{succ u2} N (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N _inst_1)) y (HasSmul.smul.{u1, u2} M N _inst_2 x (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_1)))))) (HasSmul.smul.{u1, u2} M N _inst_2 x y)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u1} N] [_inst_2 : SMul.{u2, u1} M N] [_inst_3 : SMulCommClass.{u2, u1, u1} M N N _inst_2 (Mul.toSMul.{u1} N (MulOneClass.toMul.{u1} N _inst_1))] (x : M) (y : N), Eq.{succ u1} N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N _inst_1)) y (HSMul.hSMul.{u2, u1, u1} M N N (instHSMul.{u2, u1} M N _inst_2) x (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (MulOneClass.toOne.{u1} N _inst_1))))) (HSMul.hSMul.{u2, u1, u1} M N N (instHSMul.{u2, u1} M N _inst_2) x y)
Case conversion may be inaccurate. Consider using '#align mul_smul_one mul_smul_oneₓ'. -/
@[simp, to_additive]
theorem mul_smul_one {M N} [MulOneClass N] [HasSmul M N] [SMulCommClass M N N] (x : M) (y : N) :
    y * x • 1 = x • y := by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]
#align mul_smul_one mul_smul_one

/- warning: is_scalar_tower.of_smul_one_mul -> IsScalarTower.of_smul_one_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u2} N] [_inst_2 : HasSmul.{u1, u2} M N], (forall (x : M) (y : N), Eq.{succ u2} N (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_1))) (HasSmul.smul.{u1, u2} M N _inst_2 x (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_1)))))) y) (HasSmul.smul.{u1, u2} M N _inst_2 x y)) -> (IsScalarTower.{u1, u2, u2} M N N _inst_2 (Mul.toSMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_1))) _inst_2)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u1} N] [_inst_2 : SMul.{u2, u1} M N], (forall (x : M) (y : N), Eq.{succ u1} N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_1))) (HSMul.hSMul.{u2, u1, u1} M N N (instHSMul.{u2, u1} M N _inst_2) x (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N _inst_1)))) y) (HSMul.hSMul.{u2, u1, u1} M N N (instHSMul.{u2, u1} M N _inst_2) x y)) -> (IsScalarTower.{u2, u1, u1} M N N _inst_2 (MulAction.toSMul.{u1, u1} N N _inst_1 (Monoid.toMulAction.{u1} N _inst_1)) _inst_2)
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.of_smul_one_mul IsScalarTower.of_smul_one_mulₓ'. -/
@[to_additive]
theorem IsScalarTower.of_smul_one_mul {M N} [Monoid N] [HasSmul M N]
    (h : ∀ (x : M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N :=
  ⟨fun x y z => by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩
#align is_scalar_tower.of_smul_one_mul IsScalarTower.of_smul_one_mul

/- warning: smul_comm_class.of_mul_smul_one -> SMulCommClass.of_mul_smul_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u2} N] [_inst_2 : HasSmul.{u1, u2} M N], (forall (x : M) (y : N), Eq.{succ u2} N (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_1))) y (HasSmul.smul.{u1, u2} M N _inst_2 x (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_1))))))) (HasSmul.smul.{u1, u2} M N _inst_2 x y)) -> (SMulCommClass.{u1, u2, u2} M N N _inst_2 (Mul.toSMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_1))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u1} N] [_inst_2 : SMul.{u2, u1} M N], (forall (x : M) (y : N), Eq.{succ u1} N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_1))) y (HSMul.hSMul.{u2, u1, u1} M N N (instHSMul.{u2, u1} M N _inst_2) x (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N _inst_1))))) (HSMul.hSMul.{u2, u1, u1} M N N (instHSMul.{u2, u1} M N _inst_2) x y)) -> (SMulCommClass.{u2, u1, u1} M N N _inst_2 (MulAction.toSMul.{u1, u1} N N _inst_1 (Monoid.toMulAction.{u1} N _inst_1)))
Case conversion may be inaccurate. Consider using '#align smul_comm_class.of_mul_smul_one SMulCommClass.of_mul_smul_oneₓ'. -/
@[to_additive]
theorem SMulCommClass.of_mul_smul_one {M N} [Monoid N] [HasSmul M N]
    (H : ∀ (x : M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N :=
  ⟨fun x y z => by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩
#align smul_comm_class.of_mul_smul_one SMulCommClass.of_mul_smul_one

/- warning: smul_one_hom -> smulOneHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] [_inst_3 : MulAction.{u1, u2} M N _inst_1] [_inst_4 : IsScalarTower.{u1, u2, u2} M N N (MulAction.toHasSmul.{u1, u2} M N _inst_1 _inst_3) (Mul.toSMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (MulAction.toHasSmul.{u1, u2} M N _inst_1 _inst_3)], MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] [_inst_3 : MulAction.{u1, u2} M N _inst_1] [_inst_4 : IsScalarTower.{u1, u2, u2} M N N (MulAction.toSMul.{u1, u2} M N _inst_1 _inst_3) (MulAction.toSMul.{u2, u2} N N _inst_2 (Monoid.toMulAction.{u2} N _inst_2)) (MulAction.toSMul.{u1, u2} M N _inst_1 _inst_3)], MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)
Case conversion may be inaccurate. Consider using '#align smul_one_hom smulOneHomₓ'. -/
/-- If the multiplicative action of `M` on `N` is compatible with multiplication on `N`, then
`λ x, x • 1` is a monoid homomorphism from `M` to `N`. -/
@[to_additive
      "If the additive action of `M` on `N` is compatible with addition on `N`, then\n`λ x, x +ᵥ 0` is an additive monoid homomorphism from `M` to `N`.",
  simps]
def smulOneHom {M N} [Monoid M] [Monoid N] [MulAction M N] [IsScalarTower M N N] : M →* N
    where
  toFun x := x • 1
  map_one' := one_smul _ _
  map_mul' x y := by rw [smul_one_mul, smul_smul]
#align smul_one_hom smulOneHom

end CompatibleScalar

#print SMulZeroClass /-
/-- Typeclass for scalar multiplication that preserves `0` on the right. -/
class SMulZeroClass (M A : Type _) [Zero A] extends HasSmul M A where
  smul_zero : ∀ a : M, a • (0 : A) = 0
#align smul_zero_class SMulZeroClass
-/

section smul_zero

variable [Zero A] [SMulZeroClass M A]

/- warning: smul_zero -> smul_zero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Zero.{u2} A] [_inst_2 : SMulZeroClass.{u1, u2} M A _inst_1] (a : M), Eq.{succ u2} A (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A _inst_1 _inst_2) a (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A _inst_1)))) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Zero.{u2} A] [_inst_2 : SMulZeroClass.{u1, u2} M A _inst_1] (a : M), Eq.{succ u2} A (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A _inst_1 _inst_2)) a (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A _inst_1))) (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A _inst_1))
Case conversion may be inaccurate. Consider using '#align smul_zero smul_zeroₓ'. -/
@[simp]
theorem smul_zero (a : M) : a • (0 : A) = 0 :=
  SMulZeroClass.smul_zero _
#align smul_zero smul_zero

/- warning: function.injective.smul_zero_class -> Function.Injective.smulZeroClass is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Zero.{u2} A] [_inst_2 : SMulZeroClass.{u1, u2} M A _inst_1] [_inst_3 : Zero.{u3} B] [_inst_4 : HasSmul.{u1, u3} M B] (f : ZeroHom.{u3, u2} B A _inst_3 _inst_1), (Function.Injective.{succ u3, succ u2} B A (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (ZeroHom.{u3, u2} B A _inst_3 _inst_1) (fun (_x : ZeroHom.{u3, u2} B A _inst_3 _inst_1) => B -> A) (ZeroHom.hasCoeToFun.{u3, u2} B A _inst_3 _inst_1) f)) -> (forall (c : M) (x : B), Eq.{succ u2} A (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (ZeroHom.{u3, u2} B A _inst_3 _inst_1) (fun (_x : ZeroHom.{u3, u2} B A _inst_3 _inst_1) => B -> A) (ZeroHom.hasCoeToFun.{u3, u2} B A _inst_3 _inst_1) f (HasSmul.smul.{u1, u3} M B _inst_4 c x)) (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A _inst_1 _inst_2) c (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (ZeroHom.{u3, u2} B A _inst_3 _inst_1) (fun (_x : ZeroHom.{u3, u2} B A _inst_3 _inst_1) => B -> A) (ZeroHom.hasCoeToFun.{u3, u2} B A _inst_3 _inst_1) f x))) -> (SMulZeroClass.{u1, u3} M B _inst_3)
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Zero.{u2} A] [_inst_2 : SMulZeroClass.{u1, u2} M A _inst_1] [_inst_3 : Zero.{u3} B] [_inst_4 : SMul.{u1, u3} M B] (f : ZeroHom.{u3, u2} B A _inst_3 _inst_1), (Function.Injective.{succ u3, succ u2} B A (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ZeroHom.{u3, u2} B A _inst_3 _inst_1) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : B) => A) _x) (ZeroHomClass.toFunLike.{max u2 u3, u3, u2} (ZeroHom.{u3, u2} B A _inst_3 _inst_1) B A _inst_3 _inst_1 (ZeroHom.zeroHomClass.{u3, u2} B A _inst_3 _inst_1)) f)) -> (forall (c : M) (x : B), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : B) => A) (HSMul.hSMul.{u1, u3, u3} M B B (instHSMul.{u1, u3} M B _inst_4) c x)) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ZeroHom.{u3, u2} B A _inst_3 _inst_1) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : B) => A) _x) (ZeroHomClass.toFunLike.{max u2 u3, u3, u2} (ZeroHom.{u3, u2} B A _inst_3 _inst_1) B A _inst_3 _inst_1 (ZeroHom.zeroHomClass.{u3, u2} B A _inst_3 _inst_1)) f (HSMul.hSMul.{u1, u3, u3} M B B (instHSMul.{u1, u3} M B _inst_4) c x)) (HSMul.hSMul.{u1, u2, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : B) => A) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : B) => A) x) (instHSMul.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : B) => A) x) (SMulZeroClass.toSMul.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : B) => A) x) _inst_1 _inst_2)) c (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ZeroHom.{u3, u2} B A _inst_3 _inst_1) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : B) => A) _x) (ZeroHomClass.toFunLike.{max u2 u3, u3, u2} (ZeroHom.{u3, u2} B A _inst_3 _inst_1) B A _inst_3 _inst_1 (ZeroHom.zeroHomClass.{u3, u2} B A _inst_3 _inst_1)) f x))) -> (SMulZeroClass.{u1, u3} M B _inst_3)
Case conversion may be inaccurate. Consider using '#align function.injective.smul_zero_class Function.Injective.smulZeroClassₓ'. -/
/-- Pullback a zero-preserving scalar multiplication along an injective zero-preserving map.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.smulZeroClass [Zero B] [HasSmul M B] (f : ZeroHom B A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : SMulZeroClass M B
    where
  smul := (· • ·)
  smul_zero c := hf <| by simp only [smul, map_zero, smul_zero]
#align function.injective.smul_zero_class Function.Injective.smulZeroClass

/- warning: zero_hom.smul_zero_class -> ZeroHom.smulZeroClass is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Zero.{u2} A] [_inst_2 : SMulZeroClass.{u1, u2} M A _inst_1] [_inst_3 : Zero.{u3} B] [_inst_4 : HasSmul.{u1, u3} M B] (f : ZeroHom.{u2, u3} A B _inst_1 _inst_3), (forall (c : M) (x : A), Eq.{succ u3} B (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (ZeroHom.{u2, u3} A B _inst_1 _inst_3) (fun (_x : ZeroHom.{u2, u3} A B _inst_1 _inst_3) => A -> B) (ZeroHom.hasCoeToFun.{u2, u3} A B _inst_1 _inst_3) f (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A _inst_1 _inst_2) c x)) (HasSmul.smul.{u1, u3} M B _inst_4 c (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (ZeroHom.{u2, u3} A B _inst_1 _inst_3) (fun (_x : ZeroHom.{u2, u3} A B _inst_1 _inst_3) => A -> B) (ZeroHom.hasCoeToFun.{u2, u3} A B _inst_1 _inst_3) f x))) -> (SMulZeroClass.{u1, u3} M B _inst_3)
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Zero.{u2} A] [_inst_2 : SMulZeroClass.{u1, u2} M A _inst_1] [_inst_3 : Zero.{u3} B] [_inst_4 : SMul.{u1, u3} M B] (f : ZeroHom.{u2, u3} A B _inst_1 _inst_3), (forall (c : M) (x : A), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : A) => B) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A _inst_1 _inst_2)) c x)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (ZeroHom.{u2, u3} A B _inst_1 _inst_3) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : A) => B) _x) (ZeroHomClass.toFunLike.{max u2 u3, u2, u3} (ZeroHom.{u2, u3} A B _inst_1 _inst_3) A B _inst_1 _inst_3 (ZeroHom.zeroHomClass.{u2, u3} A B _inst_1 _inst_3)) f (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A _inst_1 _inst_2)) c x)) (HSMul.hSMul.{u1, u3, u3} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : A) => B) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : A) => B) x) (instHSMul.{u1, u3} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : A) => B) x) _inst_4) c (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (ZeroHom.{u2, u3} A B _inst_1 _inst_3) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : A) => B) _x) (ZeroHomClass.toFunLike.{max u2 u3, u2, u3} (ZeroHom.{u2, u3} A B _inst_1 _inst_3) A B _inst_1 _inst_3 (ZeroHom.zeroHomClass.{u2, u3} A B _inst_1 _inst_3)) f x))) -> (SMulZeroClass.{u1, u3} M B _inst_3)
Case conversion may be inaccurate. Consider using '#align zero_hom.smul_zero_class ZeroHom.smulZeroClassₓ'. -/
/-- Pushforward a zero-preserving scalar multiplication along a zero-preserving map.
See note [reducible non-instances]. -/
@[reducible]
protected def ZeroHom.smulZeroClass [Zero B] [HasSmul M B] (f : ZeroHom A B)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : SMulZeroClass M B
    where
  smul := (· • ·)
  smul_zero c := by simp only [← map_zero f, ← smul, smul_zero]
#align zero_hom.smul_zero_class ZeroHom.smulZeroClass

/- warning: function.surjective.smul_zero_class_left -> Function.Surjective.smulZeroClassLeft is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} [_inst_3 : Zero.{u3} M] [_inst_4 : SMulZeroClass.{u1, u3} R M _inst_3] [_inst_5 : HasSmul.{u2, u3} S M] (f : R -> S), (Function.Surjective.{succ u1, succ u2} R S f) -> (forall (c : R) (x : M), Eq.{succ u3} M (HasSmul.smul.{u2, u3} S M _inst_5 (f c) x) (HasSmul.smul.{u1, u3} R M (SMulZeroClass.toHasSmul.{u1, u3} R M _inst_3 _inst_4) c x)) -> (SMulZeroClass.{u2, u3} S M _inst_3)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} [_inst_3 : Zero.{u3} M] [_inst_4 : SMulZeroClass.{u1, u3} R M _inst_3] [_inst_5 : SMul.{u2, u3} S M] (f : R -> S), (Function.Surjective.{succ u1, succ u2} R S f) -> (forall (c : R) (x : M), Eq.{succ u3} M (HSMul.hSMul.{u2, u3, u3} S M M (instHSMul.{u2, u3} S M _inst_5) (f c) x) (HSMul.hSMul.{u1, u3, u3} R M M (instHSMul.{u1, u3} R M (SMulZeroClass.toSMul.{u1, u3} R M _inst_3 _inst_4)) c x)) -> (SMulZeroClass.{u2, u3} S M _inst_3)
Case conversion may be inaccurate. Consider using '#align function.surjective.smul_zero_class_left Function.Surjective.smulZeroClassLeftₓ'. -/
/-- Push forward the multiplication of `R` on `M` along a compatible surjective map `f : R → S`.

See also `function.surjective.distrib_mul_action_left`.
-/
@[reducible]
def Function.Surjective.smulZeroClassLeft {R S M : Type _} [Zero M] [SMulZeroClass R M]
    [HasSmul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : SMulZeroClass S M
    where
  smul := (· • ·)
  smul_zero := hf.forall.mpr fun c => by rw [hsmul, smul_zero]
#align function.surjective.smul_zero_class_left Function.Surjective.smulZeroClassLeft

variable (A)

#print SMulZeroClass.compFun /-
/-- Compose a `smul_zero_class` with a function, with scalar multiplication `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def SMulZeroClass.compFun (f : N → M) : SMulZeroClass N A
    where
  smul := SMul.comp.smul f
  smul_zero x := smul_zero (f x)
#align smul_zero_class.comp_fun SMulZeroClass.compFun
-/

#print SMulZeroClass.toZeroHom /-
/-- Each element of the scalars defines a zero-preserving map. -/
@[simps]
def SMulZeroClass.toZeroHom (x : M) : ZeroHom A A
    where
  toFun := (· • ·) x
  map_zero' := smul_zero x
#align smul_zero_class.to_zero_hom SMulZeroClass.toZeroHom
-/

end smul_zero

#print DistribSMul /-
/-- Typeclass for scalar multiplication that preserves `0` and `+` on the right.

This is exactly `distrib_mul_action` without the `mul_action` part.
-/
@[ext]
class DistribSMul (M A : Type _) [AddZeroClass A] extends SMulZeroClass M A where
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y
#align distrib_smul DistribSMul
-/

section DistribSMul

variable [AddZeroClass A] [DistribSMul M A]

/- warning: smul_add -> smul_add is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddZeroClass.{u2} A] [_inst_2 : DistribSMul.{u1, u2} M A _inst_1] (a : M) (b₁ : A) (b₂ : A), Eq.{succ u2} A (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A _inst_1) (DistribSMul.toSmulZeroClass.{u1, u2} M A _inst_1 _inst_2)) a (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddZeroClass.toHasAdd.{u2} A _inst_1)) b₁ b₂)) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddZeroClass.toHasAdd.{u2} A _inst_1)) (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A _inst_1) (DistribSMul.toSmulZeroClass.{u1, u2} M A _inst_1 _inst_2)) a b₁) (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A _inst_1) (DistribSMul.toSmulZeroClass.{u1, u2} M A _inst_1 _inst_2)) a b₂))
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddZeroClass.{u2} A] [_inst_2 : DistribSMul.{u1, u2} M A _inst_1] (a : M) (b₁ : A) (b₂ : A), Eq.{succ u2} A (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddZeroClass.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A _inst_1 _inst_2))) a (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddZeroClass.toAdd.{u2} A _inst_1)) b₁ b₂)) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddZeroClass.toAdd.{u2} A _inst_1)) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddZeroClass.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A _inst_1 _inst_2))) a b₁) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddZeroClass.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A _inst_1 _inst_2))) a b₂))
Case conversion may be inaccurate. Consider using '#align smul_add smul_addₓ'. -/
theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
  DistribSMul.smul_add _ _ _
#align smul_add smul_add

/- warning: function.injective.distrib_smul -> Function.Injective.distribSMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : AddZeroClass.{u2} A] [_inst_2 : DistribSMul.{u1, u2} M A _inst_1] [_inst_3 : AddZeroClass.{u3} B] [_inst_4 : HasSmul.{u1, u3} M B] (f : AddMonoidHom.{u3, u2} B A _inst_3 _inst_1), (Function.Injective.{succ u3, succ u2} B A (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) (fun (_x : AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) => B -> A) (AddMonoidHom.hasCoeToFun.{u3, u2} B A _inst_3 _inst_1) f)) -> (forall (c : M) (x : B), Eq.{succ u2} A (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) (fun (_x : AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) => B -> A) (AddMonoidHom.hasCoeToFun.{u3, u2} B A _inst_3 _inst_1) f (HasSmul.smul.{u1, u3} M B _inst_4 c x)) (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A _inst_1) (DistribSMul.toSmulZeroClass.{u1, u2} M A _inst_1 _inst_2)) c (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) (fun (_x : AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) => B -> A) (AddMonoidHom.hasCoeToFun.{u3, u2} B A _inst_3 _inst_1) f x))) -> (DistribSMul.{u1, u3} M B _inst_3)
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : AddZeroClass.{u2} A] [_inst_2 : DistribSMul.{u1, u2} M A _inst_1] [_inst_3 : AddZeroClass.{u3} B] [_inst_4 : SMul.{u1, u3} M B] (f : AddMonoidHom.{u3, u2} B A _inst_3 _inst_1), (Function.Injective.{succ u3, succ u2} B A (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) _x) (AddHomClass.toFunLike.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) B A (AddZeroClass.toAdd.{u3} B _inst_3) (AddZeroClass.toAdd.{u2} A _inst_1) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) B A _inst_3 _inst_1 (AddMonoidHom.addMonoidHomClass.{u3, u2} B A _inst_3 _inst_1))) f)) -> (forall (c : M) (x : B), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) (HSMul.hSMul.{u1, u3, u3} M B B (instHSMul.{u1, u3} M B _inst_4) c x)) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) _x) (AddHomClass.toFunLike.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) B A (AddZeroClass.toAdd.{u3} B _inst_3) (AddZeroClass.toAdd.{u2} A _inst_1) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) B A _inst_3 _inst_1 (AddMonoidHom.addMonoidHomClass.{u3, u2} B A _inst_3 _inst_1))) f (HSMul.hSMul.{u1, u3, u3} M B B (instHSMul.{u1, u3} M B _inst_4) c x)) (HSMul.hSMul.{u1, u2, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) (instHSMul.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) (SMulZeroClass.toSMul.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) (AddZeroClass.toZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) _inst_1 _inst_2))) c (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) _x) (AddHomClass.toFunLike.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) B A (AddZeroClass.toAdd.{u3} B _inst_3) (AddZeroClass.toAdd.{u2} A _inst_1) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A _inst_3 _inst_1) B A _inst_3 _inst_1 (AddMonoidHom.addMonoidHomClass.{u3, u2} B A _inst_3 _inst_1))) f x))) -> (DistribSMul.{u1, u3} M B _inst_3)
Case conversion may be inaccurate. Consider using '#align function.injective.distrib_smul Function.Injective.distribSMulₓ'. -/
/-- Pullback a distributive scalar multiplication along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distribSMul [AddZeroClass B] [HasSmul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { hf.SmulZeroClass f.toZeroHom smul with
    smul := (· • ·)
    smul_add := fun c x y => hf <| by simp only [smul, map_add, smul_add] }
#align function.injective.distrib_smul Function.Injective.distribSMul

/- warning: function.surjective.distrib_smul -> Function.Surjective.distribSMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : AddZeroClass.{u2} A] [_inst_2 : DistribSMul.{u1, u2} M A _inst_1] [_inst_3 : AddZeroClass.{u3} B] [_inst_4 : HasSmul.{u1, u3} M B] (f : AddMonoidHom.{u2, u3} A B _inst_1 _inst_3), (Function.Surjective.{succ u2, succ u3} A B (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) (fun (_x : AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) => A -> B) (AddMonoidHom.hasCoeToFun.{u2, u3} A B _inst_1 _inst_3) f)) -> (forall (c : M) (x : A), Eq.{succ u3} B (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) (fun (_x : AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) => A -> B) (AddMonoidHom.hasCoeToFun.{u2, u3} A B _inst_1 _inst_3) f (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A _inst_1) (DistribSMul.toSmulZeroClass.{u1, u2} M A _inst_1 _inst_2)) c x)) (HasSmul.smul.{u1, u3} M B _inst_4 c (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) (fun (_x : AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) => A -> B) (AddMonoidHom.hasCoeToFun.{u2, u3} A B _inst_1 _inst_3) f x))) -> (DistribSMul.{u1, u3} M B _inst_3)
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : AddZeroClass.{u2} A] [_inst_2 : DistribSMul.{u1, u2} M A _inst_1] [_inst_3 : AddZeroClass.{u3} B] [_inst_4 : SMul.{u1, u3} M B] (f : AddMonoidHom.{u2, u3} A B _inst_1 _inst_3), (Function.Surjective.{succ u2, succ u3} A B (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) _x) (AddHomClass.toFunLike.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) A B (AddZeroClass.toAdd.{u2} A _inst_1) (AddZeroClass.toAdd.{u3} B _inst_3) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) A B _inst_1 _inst_3 (AddMonoidHom.addMonoidHomClass.{u2, u3} A B _inst_1 _inst_3))) f)) -> (forall (c : M) (x : A), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddZeroClass.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A _inst_1 _inst_2))) c x)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) _x) (AddHomClass.toFunLike.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) A B (AddZeroClass.toAdd.{u2} A _inst_1) (AddZeroClass.toAdd.{u3} B _inst_3) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) A B _inst_1 _inst_3 (AddMonoidHom.addMonoidHomClass.{u2, u3} A B _inst_1 _inst_3))) f (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddZeroClass.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A _inst_1 _inst_2))) c x)) (HSMul.hSMul.{u1, u3, u3} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) (instHSMul.{u1, u3} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) _inst_4) c (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) _x) (AddHomClass.toFunLike.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) A B (AddZeroClass.toAdd.{u2} A _inst_1) (AddZeroClass.toAdd.{u3} B _inst_3) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B _inst_1 _inst_3) A B _inst_1 _inst_3 (AddMonoidHom.addMonoidHomClass.{u2, u3} A B _inst_1 _inst_3))) f x))) -> (DistribSMul.{u1, u3} M B _inst_3)
Case conversion may be inaccurate. Consider using '#align function.surjective.distrib_smul Function.Surjective.distribSMulₓ'. -/
/-- Pushforward a distributive scalar multiplication along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distribSMul [AddZeroClass B] [HasSmul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { f.toZeroHom.SmulZeroClass smul with
    smul := (· • ·)
    smul_add := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_add, ← smul, ← map_add] }
#align function.surjective.distrib_smul Function.Surjective.distribSMul

/- warning: function.surjective.distrib_smul_left -> Function.Surjective.distribSMulLeft is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} [_inst_3 : AddZeroClass.{u3} M] [_inst_4 : DistribSMul.{u1, u3} R M _inst_3] [_inst_5 : HasSmul.{u2, u3} S M] (f : R -> S), (Function.Surjective.{succ u1, succ u2} R S f) -> (forall (c : R) (x : M), Eq.{succ u3} M (HasSmul.smul.{u2, u3} S M _inst_5 (f c) x) (HasSmul.smul.{u1, u3} R M (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M _inst_3) (DistribSMul.toSmulZeroClass.{u1, u3} R M _inst_3 _inst_4)) c x)) -> (DistribSMul.{u2, u3} S M _inst_3)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} [_inst_3 : AddZeroClass.{u3} M] [_inst_4 : DistribSMul.{u1, u3} R M _inst_3] [_inst_5 : SMul.{u2, u3} S M] (f : R -> S), (Function.Surjective.{succ u1, succ u2} R S f) -> (forall (c : R) (x : M), Eq.{succ u3} M (HSMul.hSMul.{u2, u3, u3} S M M (instHSMul.{u2, u3} S M _inst_5) (f c) x) (HSMul.hSMul.{u1, u3, u3} R M M (instHSMul.{u1, u3} R M (SMulZeroClass.toSMul.{u1, u3} R M (AddZeroClass.toZero.{u3} M _inst_3) (DistribSMul.toSMulZeroClass.{u1, u3} R M _inst_3 _inst_4))) c x)) -> (DistribSMul.{u2, u3} S M _inst_3)
Case conversion may be inaccurate. Consider using '#align function.surjective.distrib_smul_left Function.Surjective.distribSMulLeftₓ'. -/
/-- Push forward the multiplication of `R` on `M` along a compatible surjective map `f : R → S`.

See also `function.surjective.distrib_mul_action_left`.
-/
@[reducible]
def Function.Surjective.distribSMulLeft {R S M : Type _} [AddZeroClass M] [DistribSMul R M]
    [HasSmul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribSMul S M :=
  { hf.smulZeroClassLeft f hsmul with
    smul := (· • ·)
    smul_add := hf.forall.mpr fun c x y => by simp only [hsmul, smul_add] }
#align function.surjective.distrib_smul_left Function.Surjective.distribSMulLeft

variable (A)

#print DistribSMul.compFun /-
/-- Compose a `distrib_smul` with a function, with scalar multiplication `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def DistribSMul.compFun (f : N → M) : DistribSMul N A :=
  { SMulZeroClass.compFun A f with
    smul := SMul.comp.smul f
    smul_add := fun x => smul_add (f x) }
#align distrib_smul.comp_fun DistribSMul.compFun
-/

#print DistribSMul.toAddMonoidHom /-
/-- Each element of the scalars defines a additive monoid homomorphism. -/
@[simps]
def DistribSMul.toAddMonoidHom (x : M) : A →+ A :=
  { SMulZeroClass.toZeroHom A x with
    toFun := (· • ·) x
    map_add' := smul_add x }
#align distrib_smul.to_add_monoid_hom DistribSMul.toAddMonoidHom
-/

end DistribSMul

#print DistribMulAction /-
/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
@[ext]
class DistribMulAction (M A : Type _) [Monoid M] [AddMonoid A] extends MulAction M A where
  smul_zero : ∀ a : M, a • (0 : A) = 0
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y
#align distrib_mul_action DistribMulAction
-/

section

variable [Monoid M] [AddMonoid A] [DistribMulAction M A]

#print DistribMulAction.toDistribSMul /-
-- See note [lower instance priority]
instance (priority := 100) DistribMulAction.toDistribSMul : DistribSMul M A :=
  { ‹DistribMulAction M A› with }
#align distrib_mul_action.to_distrib_smul DistribMulAction.toDistribSMul
-/

/-! Since Lean 3 does not have definitional eta for structures, we have to make sure
that the definition of `distrib_mul_action.to_distrib_smul` was done correctly,
and the two paths from `distrib_mul_action` to `has_smul` are indeed definitionally equal. -/


example :
    (DistribMulAction.toMulAction.toHasSmul : HasSmul M A) =
      DistribMulAction.toDistribSMul.toHasSmul :=
  rfl

/- warning: function.injective.distrib_mul_action -> Function.Injective.distribMulAction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 _inst_2] [_inst_4 : AddMonoid.{u3} B] [_inst_5 : HasSmul.{u1, u3} M B] (f : AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)), (Function.Injective.{succ u3, succ u2} B A (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (fun (_x : AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) => B -> A) (AddMonoidHom.hasCoeToFun.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) f)) -> (forall (c : M) (x : B), Eq.{succ u2} A (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (fun (_x : AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) => B -> A) (AddMonoidHom.hasCoeToFun.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) f (HasSmul.smul.{u1, u3} M B _inst_5 c x)) (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 _inst_2 _inst_3))) c (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (fun (_x : AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) => B -> A) (AddMonoidHom.hasCoeToFun.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) f x))) -> (DistribMulAction.{u1, u3} M B _inst_1 _inst_4)
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 _inst_2] [_inst_4 : AddMonoid.{u3} B] [_inst_5 : SMul.{u1, u3} M B] (f : AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)), (Function.Injective.{succ u3, succ u2} B A (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) _x) (AddHomClass.toFunLike.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) B A (AddZeroClass.toAdd.{u3} B (AddMonoid.toAddZeroClass.{u3} B _inst_4)) (AddZeroClass.toAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoidHom.addMonoidHomClass.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)))) f)) -> (forall (c : M) (x : B), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) (HSMul.hSMul.{u1, u3, u3} M B B (instHSMul.{u1, u3} M B _inst_5) c x)) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) _x) (AddHomClass.toFunLike.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) B A (AddZeroClass.toAdd.{u3} B (AddMonoid.toAddZeroClass.{u3} B _inst_4)) (AddZeroClass.toAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoidHom.addMonoidHomClass.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)))) f (HSMul.hSMul.{u1, u3, u3} M B B (instHSMul.{u1, u3} M B _inst_5) c x)) (HSMul.hSMul.{u1, u2, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) (instHSMul.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) (SMulZeroClass.toSMul.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) (AddMonoid.toZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) (AddMonoid.toAddZeroClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) x) _inst_1 _inst_2 _inst_3)))) c (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : B) => A) _x) (AddHomClass.toFunLike.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) B A (AddZeroClass.toAdd.{u3} B (AddMonoid.toAddZeroClass.{u3} B _inst_4)) (AddZeroClass.toAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u3, u2} (AddMonoidHom.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)) B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoidHom.addMonoidHomClass.{u3, u2} B A (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoid.toAddZeroClass.{u2} A _inst_2)))) f x))) -> (DistribMulAction.{u1, u3} M B _inst_1 _inst_4)
Case conversion may be inaccurate. Consider using '#align function.injective.distrib_mul_action Function.Injective.distribMulActionₓ'. -/
/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distribMulAction [AddMonoid B] [HasSmul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.DistribSmul f smul, hf.MulAction f smul with smul := (· • ·) }
#align function.injective.distrib_mul_action Function.Injective.distribMulAction

/- warning: function.surjective.distrib_mul_action -> Function.Surjective.distribMulAction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 _inst_2] [_inst_4 : AddMonoid.{u3} B] [_inst_5 : HasSmul.{u1, u3} M B] (f : AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)), (Function.Surjective.{succ u2, succ u3} A B (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) (fun (_x : AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) => A -> B) (AddMonoidHom.hasCoeToFun.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) f)) -> (forall (c : M) (x : A), Eq.{succ u3} B (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) (fun (_x : AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) => A -> B) (AddMonoidHom.hasCoeToFun.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) f (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 _inst_2 _inst_3))) c x)) (HasSmul.smul.{u1, u3} M B _inst_5 c (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) (fun (_x : AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) => A -> B) (AddMonoidHom.hasCoeToFun.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) f x))) -> (DistribMulAction.{u1, u3} M B _inst_1 _inst_4)
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 _inst_2] [_inst_4 : AddMonoid.{u3} B] [_inst_5 : SMul.{u1, u3} M B] (f : AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)), (Function.Surjective.{succ u2, succ u3} A B (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) _x) (AddHomClass.toFunLike.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) A B (AddZeroClass.toAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (AddZeroClass.toAdd.{u3} B (AddMonoid.toAddZeroClass.{u3} B _inst_4)) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoidHom.addMonoidHomClass.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)))) f)) -> (forall (c : M) (x : A), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 _inst_2 _inst_3)))) c x)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) _x) (AddHomClass.toFunLike.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) A B (AddZeroClass.toAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (AddZeroClass.toAdd.{u3} B (AddMonoid.toAddZeroClass.{u3} B _inst_4)) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoidHom.addMonoidHomClass.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)))) f (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 _inst_2 _inst_3)))) c x)) (HSMul.hSMul.{u1, u3, u3} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) (instHSMul.{u1, u3} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) _inst_5) c (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) _x) (AddHomClass.toFunLike.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) A B (AddZeroClass.toAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (AddZeroClass.toAdd.{u3} B (AddMonoid.toAddZeroClass.{u3} B _inst_4)) (AddMonoidHomClass.toAddHomClass.{max u2 u3, u2, u3} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)) A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4) (AddMonoidHom.addMonoidHomClass.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_2) (AddMonoid.toAddZeroClass.{u3} B _inst_4)))) f x))) -> (DistribMulAction.{u1, u3} M B _inst_1 _inst_4)
Case conversion may be inaccurate. Consider using '#align function.surjective.distrib_mul_action Function.Surjective.distribMulActionₓ'. -/
/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distribMulAction [AddMonoid B] [HasSmul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.DistribSmul f smul, hf.MulAction f smul with smul := (· • ·) }
#align function.surjective.distrib_mul_action Function.Surjective.distribMulAction

/- warning: function.surjective.distrib_mul_action_left -> Function.Surjective.distribMulActionLeft is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} [_inst_4 : Monoid.{u1} R] [_inst_5 : AddMonoid.{u3} M] [_inst_6 : DistribMulAction.{u1, u3} R M _inst_4 _inst_5] [_inst_7 : Monoid.{u2} S] [_inst_8 : HasSmul.{u2, u3} S M] (f : MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)), (Function.Surjective.{succ u1, succ u2} R S (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) (fun (_x : MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) => R -> S) (MonoidHom.hasCoeToFun.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) f)) -> (forall (c : R) (x : M), Eq.{succ u3} M (HasSmul.smul.{u2, u3} S M _inst_8 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) (fun (_x : MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) => R -> S) (MonoidHom.hasCoeToFun.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) f c) x) (HasSmul.smul.{u1, u3} R M (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M _inst_5)) (DistribSMul.toSmulZeroClass.{u1, u3} R M (AddMonoid.toAddZeroClass.{u3} M _inst_5) (DistribMulAction.toDistribSMul.{u1, u3} R M _inst_4 _inst_5 _inst_6))) c x)) -> (DistribMulAction.{u2, u3} S M _inst_7 _inst_5)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} [_inst_4 : Monoid.{u1} R] [_inst_5 : AddMonoid.{u3} M] [_inst_6 : DistribMulAction.{u1, u3} R M _inst_4 _inst_5] [_inst_7 : Monoid.{u2} S] [_inst_8 : SMul.{u2, u3} S M] (f : MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)), (Function.Surjective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) R S (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_4)) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_7)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7) (MonoidHom.monoidHomClass.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)))) f)) -> (forall (c : R) (x : M), Eq.{succ u3} M (HSMul.hSMul.{u2, u3, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) c) M M (instHSMul.{u2, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) c) M _inst_8) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) R S (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_4)) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_7)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)) R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7) (MonoidHom.monoidHomClass.{u1, u2} R S (Monoid.toMulOneClass.{u1} R _inst_4) (Monoid.toMulOneClass.{u2} S _inst_7)))) f c) x) (HSMul.hSMul.{u1, u3, u3} R M M (instHSMul.{u1, u3} R M (SMulZeroClass.toSMul.{u1, u3} R M (AddMonoid.toZero.{u3} M _inst_5) (DistribSMul.toSMulZeroClass.{u1, u3} R M (AddMonoid.toAddZeroClass.{u3} M _inst_5) (DistribMulAction.toDistribSMul.{u1, u3} R M _inst_4 _inst_5 _inst_6)))) c x)) -> (DistribMulAction.{u2, u3} S M _inst_7 _inst_5)
Case conversion may be inaccurate. Consider using '#align function.surjective.distrib_mul_action_left Function.Surjective.distribMulActionLeftₓ'. -/
/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `function.surjective.mul_action_left` and `function.surjective.module_left`.
-/
@[reducible]
def Function.Surjective.distribMulActionLeft {R S M : Type _} [Monoid R] [AddMonoid M]
    [DistribMulAction R M] [Monoid S] [HasSmul S M] (f : R →* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribMulAction S M :=
  { hf.distribSmulLeft f hsmul, hf.mulActionLeft f hsmul with smul := (· • ·) }
#align function.surjective.distrib_mul_action_left Function.Surjective.distribMulActionLeft

variable (A)

#print DistribMulAction.compHom /-
/-- Compose a `distrib_mul_action` with a `monoid_hom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def DistribMulAction.compHom [Monoid N] (f : N →* M) : DistribMulAction N A :=
  { DistribSMul.compFun A f, MulAction.compHom A f with smul := SMul.comp.smul f }
#align distrib_mul_action.comp_hom DistribMulAction.compHom
-/

#print DistribMulAction.toAddMonoidHom /-
/-- Each element of the monoid defines a additive monoid homomorphism. -/
@[simps]
def DistribMulAction.toAddMonoidHom (x : M) : A →+ A :=
  DistribSMul.toAddMonoidHom A x
#align distrib_mul_action.to_add_monoid_hom DistribMulAction.toAddMonoidHom
-/

variable (M)

#print DistribMulAction.toAddMonoidEnd /-
/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps]
def DistribMulAction.toAddMonoidEnd : M →* AddMonoid.End A
    where
  toFun := DistribMulAction.toAddMonoidHom A
  map_one' := AddMonoidHom.ext <| one_smul M
  map_mul' x y := AddMonoidHom.ext <| mul_smul x y
#align distrib_mul_action.to_add_monoid_End DistribMulAction.toAddMonoidEnd
-/

/- warning: add_monoid.nat_smul_comm_class -> AddMonoid.nat_smulCommClass is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (A : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 _inst_2], SMulCommClass.{0, u1, u2} Nat M A (AddMonoid.SMul.{u2} A _inst_2) (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 _inst_2 _inst_3)))
but is expected to have type
  forall (M : Type.{u1}) (A : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 _inst_2], SMulCommClass.{0, u1, u2} Nat M A (AddMonoid.SMul.{u2} A _inst_2) (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align add_monoid.nat_smul_comm_class AddMonoid.nat_smulCommClassₓ'. -/
instance AddMonoid.nat_smulCommClass : SMulCommClass ℕ M A
    where smul_comm n x y := ((DistribMulAction.toAddMonoidHom A x).map_nsmul y n).symm
#align add_monoid.nat_smul_comm_class AddMonoid.nat_smulCommClass

/- warning: add_monoid.nat_smul_comm_class' -> AddMonoid.nat_smulCommClass' is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (A : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 _inst_2], SMulCommClass.{u1, 0, u2} M Nat A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 _inst_2 _inst_3))) (AddMonoid.SMul.{u2} A _inst_2)
but is expected to have type
  forall (M : Type.{u1}) (A : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 _inst_2], SMulCommClass.{u1, 0, u2} M Nat A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 _inst_2 _inst_3))) (AddMonoid.SMul.{u2} A _inst_2)
Case conversion may be inaccurate. Consider using '#align add_monoid.nat_smul_comm_class' AddMonoid.nat_smulCommClass'ₓ'. -/
-- `smul_comm_class.symm` is not registered as an instance, as it would cause a loop
instance AddMonoid.nat_smulCommClass' : SMulCommClass M ℕ A :=
  SMulCommClass.symm _ _ _
#align add_monoid.nat_smul_comm_class' AddMonoid.nat_smulCommClass'

end

section

variable [Monoid M] [AddGroup A] [DistribMulAction M A]

/- warning: add_group.int_smul_comm_class -> AddGroup.int_smulCommClass is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddGroup.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))], SMulCommClass.{0, u1, u2} Int M A (SubNegMonoid.hasSmulInt.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3)))
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddGroup.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))], SMulCommClass.{0, u1, u2} Int M A (SubNegMonoid.SMulInt.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) (SMulZeroClass.toSMul.{u1, u2} M A (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (AddGroup.toSubtractionMonoid.{u2} A _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3)))
Case conversion may be inaccurate. Consider using '#align add_group.int_smul_comm_class AddGroup.int_smulCommClassₓ'. -/
instance AddGroup.int_smulCommClass : SMulCommClass ℤ M A
    where smul_comm n x y := ((DistribMulAction.toAddMonoidHom A x).map_zsmul y n).symm
#align add_group.int_smul_comm_class AddGroup.int_smulCommClass

/- warning: add_group.int_smul_comm_class' -> AddGroup.int_smulCommClass' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddGroup.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))], SMulCommClass.{u1, 0, u2} M Int A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3))) (SubNegMonoid.hasSmulInt.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddGroup.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))], SMulCommClass.{u1, 0, u2} M Int A (SMulZeroClass.toSMul.{u1, u2} M A (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (AddGroup.toSubtractionMonoid.{u2} A _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3))) (SubNegMonoid.SMulInt.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))
Case conversion may be inaccurate. Consider using '#align add_group.int_smul_comm_class' AddGroup.int_smulCommClass'ₓ'. -/
-- `smul_comm_class.symm` is not registered as an instance, as it would cause a loop
instance AddGroup.int_smulCommClass' : SMulCommClass M ℤ A :=
  SMulCommClass.symm _ _ _
#align add_group.int_smul_comm_class' AddGroup.int_smulCommClass'

/- warning: smul_neg -> smul_neg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddGroup.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))] (r : M) (x : A), Eq.{succ u2} A (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3))) r (Neg.neg.{u2} A (SubNegMonoid.toHasNeg.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) x)) (Neg.neg.{u2} A (SubNegMonoid.toHasNeg.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3))) r x))
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddGroup.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))] (r : M) (x : A), Eq.{succ u2} A (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (AddGroup.toSubtractionMonoid.{u2} A _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3)))) r (Neg.neg.{u2} A (NegZeroClass.toNeg.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (AddGroup.toSubtractionMonoid.{u2} A _inst_2)))) x)) (Neg.neg.{u2} A (NegZeroClass.toNeg.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (AddGroup.toSubtractionMonoid.{u2} A _inst_2)))) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (AddGroup.toSubtractionMonoid.{u2} A _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3)))) r x))
Case conversion may be inaccurate. Consider using '#align smul_neg smul_negₓ'. -/
@[simp]
theorem smul_neg (r : M) (x : A) : r • -x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by rw [← smul_add, neg_add_self, smul_zero]
#align smul_neg smul_neg

/- warning: smul_sub -> smul_sub is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddGroup.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))] (r : M) (x : A) (y : A), Eq.{succ u2} A (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3))) r (HSub.hSub.{u2, u2, u2} A A A (instHSub.{u2} A (SubNegMonoid.toHasSub.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) x y)) (HSub.hSub.{u2, u2, u2} A A A (instHSub.{u2} A (SubNegMonoid.toHasSub.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3))) r x) (HasSmul.smul.{u1, u2} M A (SMulZeroClass.toHasSmul.{u1, u2} M A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3))) r y))
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : AddGroup.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))] (r : M) (x : A) (y : A), Eq.{succ u2} A (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (AddGroup.toSubtractionMonoid.{u2} A _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3)))) r (HSub.hSub.{u2, u2, u2} A A A (instHSub.{u2} A (SubNegMonoid.toSub.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) x y)) (HSub.hSub.{u2, u2, u2} A A A (instHSub.{u2} A (SubNegMonoid.toSub.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (AddGroup.toSubtractionMonoid.{u2} A _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3)))) r x) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (AddGroup.toSubtractionMonoid.{u2} A _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_1 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)) _inst_3)))) r y))
Case conversion may be inaccurate. Consider using '#align smul_sub smul_subₓ'. -/
theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]
#align smul_sub smul_sub

end

#print MulDistribMulAction /-
/-- Typeclass for multiplicative actions on multiplicative structures. This generalizes
conjugation actions. -/
@[ext]
class MulDistribMulAction (M : Type _) (A : Type _) [Monoid M] [Monoid A] extends
  MulAction M A where
  smul_mul : ∀ (r : M) (x y : A), r • (x * y) = r • x * r • y
  smul_one : ∀ r : M, r • (1 : A) = 1
#align mul_distrib_mul_action MulDistribMulAction
-/

export MulDistribMulAction (smul_one)

section

variable [Monoid M] [Monoid A] [MulDistribMulAction M A]

/- warning: smul_mul' -> smul_mul' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2] (a : M) (b₁ : A) (b₂ : A), Eq.{succ u2} A (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3)) a (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (MulOneClass.toHasMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2))) b₁ b₂)) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (MulOneClass.toHasMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2))) (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3)) a b₁) (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3)) a b₂))
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2] (a : M) (b₁ : A) (b₂ : A), Eq.{succ u2} A (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3))) a (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2))) b₁ b₂)) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2))) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3))) a b₁) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3))) a b₂))
Case conversion may be inaccurate. Consider using '#align smul_mul' smul_mul'ₓ'. -/
theorem smul_mul' (a : M) (b₁ b₂ : A) : a • (b₁ * b₂) = a • b₁ * a • b₂ :=
  MulDistribMulAction.smul_mul _ _ _
#align smul_mul' smul_mul'

/- warning: function.injective.mul_distrib_mul_action -> Function.Injective.mulDistribMulAction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2] [_inst_4 : Monoid.{u3} B] [_inst_5 : HasSmul.{u1, u3} M B] (f : MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)), (Function.Injective.{succ u3, succ u2} B A (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) (fun (_x : MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) => B -> A) (MonoidHom.hasCoeToFun.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) f)) -> (forall (c : M) (x : B), Eq.{succ u2} A (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) (fun (_x : MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) => B -> A) (MonoidHom.hasCoeToFun.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) f (HasSmul.smul.{u1, u3} M B _inst_5 c x)) (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3)) c (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) (fun (_x : MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) => B -> A) (MonoidHom.hasCoeToFun.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) f x))) -> (MulDistribMulAction.{u1, u3} M B _inst_1 _inst_4)
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2] [_inst_4 : Monoid.{u3} B] [_inst_5 : SMul.{u1, u3} M B] (f : MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)), (Function.Injective.{succ u3, succ u2} B A (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : B) => A) _x) (MulHomClass.toFunLike.{max u2 u3, u3, u2} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) B A (MulOneClass.toMul.{u3} B (Monoid.toMulOneClass.{u3} B _inst_4)) (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u3, u3, u2} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2) (MonoidHom.monoidHomClass.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)))) f)) -> (forall (c : M) (x : B), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : B) => A) (HSMul.hSMul.{u1, u3, u3} M B B (instHSMul.{u1, u3} M B _inst_5) c x)) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : B) => A) _x) (MulHomClass.toFunLike.{max u2 u3, u3, u2} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) B A (MulOneClass.toMul.{u3} B (Monoid.toMulOneClass.{u3} B _inst_4)) (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u3, u3, u2} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2) (MonoidHom.monoidHomClass.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)))) f (HSMul.hSMul.{u1, u3, u3} M B B (instHSMul.{u1, u3} M B _inst_5) c x)) (HSMul.hSMul.{u1, u2, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : B) => A) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : B) => A) x) (instHSMul.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : B) => A) x) (MulAction.toSMul.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : B) => A) x) _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : B) => A) x) _inst_1 _inst_2 _inst_3))) c (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : B) => A) _x) (MulHomClass.toFunLike.{max u2 u3, u3, u2} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) B A (MulOneClass.toMul.{u3} B (Monoid.toMulOneClass.{u3} B _inst_4)) (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u3, u3, u2} (MonoidHom.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)) B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2) (MonoidHom.monoidHomClass.{u3, u2} B A (Monoid.toMulOneClass.{u3} B _inst_4) (Monoid.toMulOneClass.{u2} A _inst_2)))) f x))) -> (MulDistribMulAction.{u1, u3} M B _inst_1 _inst_4)
Case conversion may be inaccurate. Consider using '#align function.injective.mul_distrib_mul_action Function.Injective.mulDistribMulActionₓ'. -/
/-- Pullback a multiplicative distributive multiplicative action along an injective monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulDistribMulAction [Monoid B] [HasSmul M B] (f : B →* A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.MulAction f smul with
    smul := (· • ·)
    smul_mul := fun c x y => hf <| by simp only [smul, f.map_mul, smul_mul']
    smul_one := fun c => hf <| by simp only [smul, f.map_one, smul_one] }
#align function.injective.mul_distrib_mul_action Function.Injective.mulDistribMulAction

/- warning: function.surjective.mul_distrib_mul_action -> Function.Surjective.mulDistribMulAction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2] [_inst_4 : Monoid.{u3} B] [_inst_5 : HasSmul.{u1, u3} M B] (f : MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)), (Function.Surjective.{succ u2, succ u3} A B (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) (fun (_x : MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) => A -> B) (MonoidHom.hasCoeToFun.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) f)) -> (forall (c : M) (x : A), Eq.{succ u3} B (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) (fun (_x : MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) => A -> B) (MonoidHom.hasCoeToFun.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) f (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3)) c x)) (HasSmul.smul.{u1, u3} M B _inst_5 c (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) (fun (_x : MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) => A -> B) (MonoidHom.hasCoeToFun.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) f x))) -> (MulDistribMulAction.{u1, u3} M B _inst_1 _inst_4)
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2] [_inst_4 : Monoid.{u3} B] [_inst_5 : SMul.{u1, u3} M B] (f : MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)), (Function.Surjective.{succ u2, succ u3} A B (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : A) => B) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) A B (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (MulOneClass.toMul.{u3} B (Monoid.toMulOneClass.{u3} B _inst_4)) (MonoidHomClass.toMulHomClass.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4) (MonoidHom.monoidHomClass.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)))) f)) -> (forall (c : M) (x : A), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : A) => B) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3))) c x)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : A) => B) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) A B (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (MulOneClass.toMul.{u3} B (Monoid.toMulOneClass.{u3} B _inst_4)) (MonoidHomClass.toMulHomClass.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4) (MonoidHom.monoidHomClass.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)))) f (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3))) c x)) (HSMul.hSMul.{u1, u3, u3} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : A) => B) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : A) => B) x) (instHSMul.{u1, u3} M ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : A) => B) x) _inst_5) c (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : A) => B) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) A B (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (MulOneClass.toMul.{u3} B (Monoid.toMulOneClass.{u3} B _inst_4)) (MonoidHomClass.toMulHomClass.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)) A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4) (MonoidHom.monoidHomClass.{u2, u3} A B (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u3} B _inst_4)))) f x))) -> (MulDistribMulAction.{u1, u3} M B _inst_1 _inst_4)
Case conversion may be inaccurate. Consider using '#align function.surjective.mul_distrib_mul_action Function.Surjective.mulDistribMulActionₓ'. -/
/-- Pushforward a multiplicative distributive multiplicative action along a surjective monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulDistribMulAction [Monoid B] [HasSmul M B] (f : A →* B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.MulAction f smul with
    smul := (· • ·)
    smul_mul := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_mul', ← smul, ← f.map_mul]
    smul_one := fun c => by simp only [← f.map_one, ← smul, smul_one] }
#align function.surjective.mul_distrib_mul_action Function.Surjective.mulDistribMulAction

variable (A)

#print MulDistribMulAction.compHom /-
/-- Compose a `mul_distrib_mul_action` with a `monoid_hom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def MulDistribMulAction.compHom [Monoid N] (f : N →* M) : MulDistribMulAction N A :=
  { MulAction.compHom A f with
    smul := SMul.comp.smul f
    smul_one := fun x => smul_one (f x)
    smul_mul := fun x => smul_mul' (f x) }
#align mul_distrib_mul_action.comp_hom MulDistribMulAction.compHom
-/

#print MulDistribMulAction.toMonoidHom /-
/-- Scalar multiplication by `r` as a `monoid_hom`. -/
def MulDistribMulAction.toMonoidHom (r : M) : A →* A
    where
  toFun := (· • ·) r
  map_one' := smul_one r
  map_mul' := smul_mul' r
#align mul_distrib_mul_action.to_monoid_hom MulDistribMulAction.toMonoidHom
-/

variable {A}

/- warning: mul_distrib_mul_action.to_monoid_hom_apply -> MulDistribMulAction.toMonoidHom_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2] (r : M) (x : A), Eq.{succ u2} A (coeFn.{succ u2, succ u2} (MonoidHom.{u2, u2} A A (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u2} A _inst_2)) (fun (_x : MonoidHom.{u2, u2} A A (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u2} A _inst_2)) => A -> A) (MonoidHom.hasCoeToFun.{u2, u2} A A (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u2} A _inst_2)) (MulDistribMulAction.toMonoidHom.{u1, u2} M A _inst_1 _inst_2 _inst_3 r) x) (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3)) r x)
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2] (r : M) (x : A), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : A) => A) x) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidHom.{u2, u2} A A (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u2} A _inst_2)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : A) => A) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidHom.{u2, u2} A A (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u2} A _inst_2)) A A (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidHom.{u2, u2} A A (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u2} A _inst_2)) A A (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u2} A _inst_2) (MonoidHom.monoidHomClass.{u2, u2} A A (Monoid.toMulOneClass.{u2} A _inst_2) (Monoid.toMulOneClass.{u2} A _inst_2)))) (MulDistribMulAction.toMonoidHom.{u1, u2} M A _inst_1 _inst_2 _inst_3 r) x) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 _inst_2 _inst_3))) r x)
Case conversion may be inaccurate. Consider using '#align mul_distrib_mul_action.to_monoid_hom_apply MulDistribMulAction.toMonoidHom_applyₓ'. -/
@[simp]
theorem MulDistribMulAction.toMonoidHom_apply (r : M) (x : A) :
    MulDistribMulAction.toMonoidHom A r x = r • x :=
  rfl
#align mul_distrib_mul_action.to_monoid_hom_apply MulDistribMulAction.toMonoidHom_apply

variable (M A)

/- warning: mul_distrib_mul_action.to_monoid_End -> MulDistribMulAction.toMonoidEnd is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (A : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2], MonoidHom.{u1, u2} M (Monoid.End.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} (Monoid.End.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (Monoid.End.monoid.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)))
but is expected to have type
  forall (M : Type.{u1}) (A : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 _inst_2], MonoidHom.{u1, u2} M (Monoid.End.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} (Monoid.End.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)) (Monoid.End.instMonoidEnd.{u2} A (Monoid.toMulOneClass.{u2} A _inst_2)))
Case conversion may be inaccurate. Consider using '#align mul_distrib_mul_action.to_monoid_End MulDistribMulAction.toMonoidEndₓ'. -/
/-- Each element of the monoid defines a monoid homomorphism. -/
@[simps]
def MulDistribMulAction.toMonoidEnd : M →* Monoid.End A
    where
  toFun := MulDistribMulAction.toMonoidHom A
  map_one' := MonoidHom.ext <| one_smul M
  map_mul' x y := MonoidHom.ext <| mul_smul x y
#align mul_distrib_mul_action.to_monoid_End MulDistribMulAction.toMonoidEnd

end

section

variable [Monoid M] [Group A] [MulDistribMulAction M A]

/- warning: smul_inv' -> smul_inv' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Group.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2))] (r : M) (x : A), Eq.{succ u2} A (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3)) r (Inv.inv.{u2} A (DivInvMonoid.toHasInv.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) x)) (Inv.inv.{u2} A (DivInvMonoid.toHasInv.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3)) r x))
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Group.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2))] (r : M) (x : A), Eq.{succ u2} A (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3))) r (Inv.inv.{u2} A (InvOneClass.toInv.{u2} A (DivInvOneMonoid.toInvOneClass.{u2} A (DivisionMonoid.toDivInvOneMonoid.{u2} A (Group.toDivisionMonoid.{u2} A _inst_2)))) x)) (Inv.inv.{u2} A (InvOneClass.toInv.{u2} A (DivInvOneMonoid.toInvOneClass.{u2} A (DivisionMonoid.toDivInvOneMonoid.{u2} A (Group.toDivisionMonoid.{u2} A _inst_2)))) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3))) r x))
Case conversion may be inaccurate. Consider using '#align smul_inv' smul_inv'ₓ'. -/
@[simp]
theorem smul_inv' (r : M) (x : A) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom A r).map_inv x
#align smul_inv' smul_inv'

/- warning: smul_div' -> smul_div' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Group.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2))] (r : M) (x : A) (y : A), Eq.{succ u2} A (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3)) r (HDiv.hDiv.{u2, u2, u2} A A A (instHDiv.{u2} A (DivInvMonoid.toHasDiv.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2))) x y)) (HDiv.hDiv.{u2, u2, u2} A A A (instHDiv.{u2} A (DivInvMonoid.toHasDiv.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2))) (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3)) r x) (HasSmul.smul.{u1, u2} M A (MulAction.toHasSmul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3)) r y))
but is expected to have type
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Group.{u2} A] [_inst_3 : MulDistribMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2))] (r : M) (x : A) (y : A), Eq.{succ u2} A (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3))) r (HDiv.hDiv.{u2, u2, u2} A A A (instHDiv.{u2} A (DivInvMonoid.toDiv.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2))) x y)) (HDiv.hDiv.{u2, u2, u2} A A A (instHDiv.{u2} A (DivInvMonoid.toDiv.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2))) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3))) r x) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (MulAction.toSMul.{u1, u2} M A _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} M A _inst_1 (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A _inst_2)) _inst_3))) r y))
Case conversion may be inaccurate. Consider using '#align smul_div' smul_div'ₓ'. -/
theorem smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y :=
  map_div (MulDistribMulAction.toMonoidHom A r) x y
#align smul_div' smul_div'

end

variable (α)

#print Function.End /-
/-- The monoid of endomorphisms.

Note that this is generalized by `category_theory.End` to categories other than `Type u`. -/
protected def Function.End :=
  α → α
#align function.End Function.End
-/

instance : Monoid (Function.End α) where
  one := id
  mul := (· ∘ ·)
  mul_assoc f g h := rfl
  mul_one f := rfl
  one_mul f := rfl

instance : Inhabited (Function.End α) :=
  ⟨1⟩

variable {α}

/- warning: function.End.apply_mul_action -> Function.End.applyMulAction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, MulAction.{u1, u1} (Function.End.{u1} α) α (Function.End.monoid.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, MulAction.{u1, u1} (Function.End.{u1} α) α (instMonoidEnd.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.End.apply_mul_action Function.End.applyMulActionₓ'. -/
/-- The tautological action by `function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `equiv.perm.apply_mul_action`
* `add_monoid.End.apply_distrib_mul_action`
* `add_aut.apply_distrib_mul_action`
* `mul_aut.apply_mul_distrib_mul_action`
* `ring_hom.apply_distrib_mul_action`
* `linear_equiv.apply_distrib_mul_action`
* `linear_map.apply_module`
* `ring_hom.apply_mul_semiring_action`
* `alg_equiv.apply_mul_semiring_action`
-/
instance Function.End.applyMulAction : MulAction (Function.End α) α
    where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align function.End.apply_mul_action Function.End.applyMulAction

/- warning: function.End.smul_def -> Function.End.smul_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Function.End.{u1} α) (a : α), Eq.{succ u1} α (HasSmul.smul.{u1, u1} (Function.End.{u1} α) α (MulAction.toHasSmul.{u1, u1} (Function.End.{u1} α) α (Function.End.monoid.{u1} α) (Function.End.applyMulAction.{u1} α)) f a) (f a)
but is expected to have type
  forall {α : Type.{u1}} (f : Function.End.{u1} α) (a : α), Eq.{succ u1} α (HSMul.hSMul.{u1, u1, u1} (Function.End.{u1} α) α α (instHSMul.{u1, u1} (Function.End.{u1} α) α (MulAction.toSMul.{u1, u1} (Function.End.{u1} α) α (instMonoidEnd.{u1} α) (Function.End.applyMulAction.{u1} α))) f a) (f a)
Case conversion may be inaccurate. Consider using '#align function.End.smul_def Function.End.smul_defₓ'. -/
@[simp]
theorem Function.End.smul_def (f : Function.End α) (a : α) : f • a = f a :=
  rfl
#align function.End.smul_def Function.End.smul_def

/- warning: function.End.apply_has_faithful_smul -> Function.End.apply_FaithfulSMul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, FaithfulSMul.{u1, u1} (Function.End.{u1} α) α (MulAction.toHasSmul.{u1, u1} (Function.End.{u1} α) α (Function.End.monoid.{u1} α) (Function.End.applyMulAction.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, FaithfulSMul.{u1, u1} (Function.End.{u1} α) α (MulAction.toSMul.{u1, u1} (Function.End.{u1} α) α (instMonoidEnd.{u1} α) (Function.End.applyMulAction.{u1} α))
Case conversion may be inaccurate. Consider using '#align function.End.apply_has_faithful_smul Function.End.apply_FaithfulSMulₓ'. -/
/-- `function.End.apply_mul_action` is faithful. -/
instance Function.End.apply_FaithfulSMul : FaithfulSMul (Function.End α) α :=
  ⟨fun x y => funext⟩
#align function.End.apply_has_faithful_smul Function.End.apply_FaithfulSMul

#print AddMonoid.End.applyDistribMulAction /-
/-- The tautological action by `add_monoid.End α` on `α`.

This generalizes `function.End.apply_mul_action`. -/
instance AddMonoid.End.applyDistribMulAction [AddMonoid α] : DistribMulAction (AddMonoid.End α) α
    where
  smul := (· <| ·)
  smul_zero := AddMonoidHom.map_zero
  smul_add := AddMonoidHom.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align add_monoid.End.apply_distrib_mul_action AddMonoid.End.applyDistribMulAction
-/

/- warning: add_monoid.End.smul_def -> AddMonoid.End.smul_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (f : AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (a : α), Eq.{succ u1} α (HasSmul.smul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (SMulZeroClass.toHasSmul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (DistribSMul.toSmulZeroClass.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.toAddZeroClass.{u1} α _inst_1) (DistribMulAction.toDistribSMul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.End.monoid.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) _inst_1 (AddMonoid.End.applyDistribMulAction.{u1} α _inst_1)))) f a) (coeFn.{succ u1, succ u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (fun (_x : AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) => α -> α) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (fun (_x : α) => α) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α α (AddMonoid.toAddZeroClass.{u1} α _inst_1) (AddMonoid.toAddZeroClass.{u1} α _inst_1) (AddMonoid.End.addMonoidHomClass.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))))) f a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (f : AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (a : α), Eq.{succ u1} α (HSMul.hSMul.{u1, u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α α (instHSMul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (SMulZeroClass.toSMul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.toZero.{u1} α _inst_1) (DistribSMul.toSMulZeroClass.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.toAddZeroClass.{u1} α _inst_1) (DistribMulAction.toDistribSMul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.End.monoid.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) _inst_1 (AddMonoid.End.applyDistribMulAction.{u1} α _inst_1))))) f a) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => α) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α α (AddMonoid.toAddZeroClass.{u1} α _inst_1) (AddMonoid.toAddZeroClass.{u1} α _inst_1) (AddMonoid.End.instAddMonoidHomClassEnd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))) f a)
Case conversion may be inaccurate. Consider using '#align add_monoid.End.smul_def AddMonoid.End.smul_defₓ'. -/
@[simp]
theorem AddMonoid.End.smul_def [AddMonoid α] (f : AddMonoid.End α) (a : α) : f • a = f a :=
  rfl
#align add_monoid.End.smul_def AddMonoid.End.smul_def

/- warning: add_monoid.End.apply_has_faithful_smul -> AddMonoid.End.applyFaithfulSMul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α], FaithfulSMul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (SMulZeroClass.toHasSmul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (DistribSMul.toSmulZeroClass.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.toAddZeroClass.{u1} α _inst_1) (DistribMulAction.toDistribSMul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.End.monoid.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) _inst_1 (AddMonoid.End.applyDistribMulAction.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α], FaithfulSMul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (SMulZeroClass.toSMul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.toZero.{u1} α _inst_1) (DistribSMul.toSMulZeroClass.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.toAddZeroClass.{u1} α _inst_1) (DistribMulAction.toDistribSMul.{u1, u1} (AddMonoid.End.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) α (AddMonoid.End.monoid.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) _inst_1 (AddMonoid.End.applyDistribMulAction.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align add_monoid.End.apply_has_faithful_smul AddMonoid.End.applyFaithfulSMulₓ'. -/
/-- `add_monoid.End.apply_distrib_mul_action` is faithful. -/
instance AddMonoid.End.applyFaithfulSMul [AddMonoid α] : FaithfulSMul (AddMonoid.End α) α :=
  ⟨AddMonoidHom.ext⟩
#align add_monoid.End.apply_has_faithful_smul AddMonoid.End.applyFaithfulSMul

/- warning: mul_action.to_End_hom -> MulAction.toEndHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1], MonoidHom.{u1, u2} M (Function.End.{u2} α) (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} (Function.End.{u2} α) (Function.End.monoid.{u2} α))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1], MonoidHom.{u1, u2} M (Function.End.{u2} α) (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} (Function.End.{u2} α) (instMonoidEnd.{u2} α))
Case conversion may be inaccurate. Consider using '#align mul_action.to_End_hom MulAction.toEndHomₓ'. -/
/-- The monoid hom representing a monoid action.

When `M` is a group, see `mul_action.to_perm_hom`. -/
def MulAction.toEndHom [Monoid M] [MulAction M α] : M →* Function.End α
    where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)
#align mul_action.to_End_hom MulAction.toEndHom

/- warning: mul_action.of_End_hom -> MulAction.ofEndHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M], (MonoidHom.{u1, u2} M (Function.End.{u2} α) (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} (Function.End.{u2} α) (Function.End.monoid.{u2} α))) -> (MulAction.{u1, u2} M α _inst_1)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M], (MonoidHom.{u1, u2} M (Function.End.{u2} α) (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} (Function.End.{u2} α) (instMonoidEnd.{u2} α))) -> (MulAction.{u1, u2} M α _inst_1)
Case conversion may be inaccurate. Consider using '#align mul_action.of_End_hom MulAction.ofEndHomₓ'. -/
/-- The monoid action induced by a monoid hom to `function.End α`

See note [reducible non-instances]. -/
@[reducible]
def MulAction.ofEndHom [Monoid M] (f : M →* Function.End α) : MulAction M α :=
  MulAction.compHom α f
#align mul_action.of_End_hom MulAction.ofEndHom

/- warning: add_action.function_End -> AddAction.functionEnd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, AddAction.{u1, u1} (Additive.{u1} (Function.End.{u1} α)) α (Additive.addMonoid.{u1} (Function.End.{u1} α) (Function.End.monoid.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, AddAction.{u1, u1} (Additive.{u1} (Function.End.{u1} α)) α (Additive.addMonoid.{u1} (Function.End.{u1} α) (instMonoidEnd.{u1} α))
Case conversion may be inaccurate. Consider using '#align add_action.function_End AddAction.functionEndₓ'. -/
/-- The tautological additive action by `additive (function.End α)` on `α`. -/
instance AddAction.functionEnd : AddAction (Additive (Function.End α)) α
    where
  vadd := (· <| ·)
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl
#align add_action.function_End AddAction.functionEnd

/- warning: add_action.to_End_hom -> AddAction.toEndHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u1} M] [_inst_2 : AddAction.{u1, u2} M α _inst_1], AddMonoidHom.{u1, u2} M (Additive.{u2} (Function.End.{u2} α)) (AddMonoid.toAddZeroClass.{u1} M _inst_1) (Additive.addZeroClass.{u2} (Function.End.{u2} α) (Monoid.toMulOneClass.{u2} (Function.End.{u2} α) (Function.End.monoid.{u2} α)))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u1} M] [_inst_2 : AddAction.{u1, u2} M α _inst_1], AddMonoidHom.{u1, u2} M (Additive.{u2} (Function.End.{u2} α)) (AddMonoid.toAddZeroClass.{u1} M _inst_1) (Additive.addZeroClass.{u2} (Function.End.{u2} α) (Monoid.toMulOneClass.{u2} (Function.End.{u2} α) (instMonoidEnd.{u2} α)))
Case conversion may be inaccurate. Consider using '#align add_action.to_End_hom AddAction.toEndHomₓ'. -/
/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `add_action.to_perm_hom`. -/
def AddAction.toEndHom [AddMonoid M] [AddAction M α] : M →+ Additive (Function.End α)
    where
  toFun := (· +ᵥ ·)
  map_zero' := funext (zero_vadd M)
  map_add' x y := funext (add_vadd x y)
#align add_action.to_End_hom AddAction.toEndHom

/- warning: add_action.of_End_hom -> AddAction.ofEndHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u1} M], (AddMonoidHom.{u1, u2} M (Additive.{u2} (Function.End.{u2} α)) (AddMonoid.toAddZeroClass.{u1} M _inst_1) (Additive.addZeroClass.{u2} (Function.End.{u2} α) (Monoid.toMulOneClass.{u2} (Function.End.{u2} α) (Function.End.monoid.{u2} α)))) -> (AddAction.{u1, u2} M α _inst_1)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u1} M], (AddMonoidHom.{u1, u2} M (Additive.{u2} (Function.End.{u2} α)) (AddMonoid.toAddZeroClass.{u1} M _inst_1) (Additive.addZeroClass.{u2} (Function.End.{u2} α) (Monoid.toMulOneClass.{u2} (Function.End.{u2} α) (instMonoidEnd.{u2} α)))) -> (AddAction.{u1, u2} M α _inst_1)
Case conversion may be inaccurate. Consider using '#align add_action.of_End_hom AddAction.ofEndHomₓ'. -/
/-- The additive action induced by a hom to `additive (function.End α)`

See note [reducible non-instances]. -/
@[reducible]
def AddAction.ofEndHom [AddMonoid M] (f : M →+ Additive (Function.End α)) : AddAction M α :=
  AddAction.compHom α f
#align add_action.of_End_hom AddAction.ofEndHom

/-! ### `additive`, `multiplicative` -/


section

open Additive Multiplicative

/- warning: additive.has_vadd -> Additive.vadd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} α β], VAdd.{u1, u2} (Additive.{u1} α) β
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β], VAdd.{u1, u2} (Additive.{u1} α) β
Case conversion may be inaccurate. Consider using '#align additive.has_vadd Additive.vaddₓ'. -/
instance Additive.vadd [HasSmul α β] : VAdd (Additive α) β :=
  ⟨fun a => (· • ·) (toMul a)⟩
#align additive.has_vadd Additive.vadd

/- warning: multiplicative.has_smul -> Multiplicative.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VAdd.{u1, u2} α β], HasSmul.{u1, u2} (Multiplicative.{u1} α) β
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VAdd.{u1, u2} α β], SMul.{u1, u2} (Multiplicative.{u1} α) β
Case conversion may be inaccurate. Consider using '#align multiplicative.has_smul Multiplicative.smulₓ'. -/
instance Multiplicative.smul [VAdd α β] : HasSmul (Multiplicative α) β :=
  ⟨fun a => (· +ᵥ ·) (toAdd a)⟩
#align multiplicative.has_smul Multiplicative.smul

/- warning: to_mul_smul -> toMul_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} α β] (a : Additive.{u1} α) (b : β), Eq.{succ u2} β (HasSmul.smul.{u1, u2} α β _inst_1 (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Additive.{u1} α) α) => (Additive.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) a) b) (VAdd.vadd.{u1, u2} (Additive.{u1} α) β (Additive.vadd.{u1, u2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : Additive.{u2} α) (b : β), Eq.{succ u1} β (HSMul.hSMul.{u2, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Additive.{u2} α) => α) a) β β (instHSMul.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Additive.{u2} α) => α) a) β _inst_1) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Additive.{u2} α) α) (Additive.{u2} α) (fun (_x : Additive.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Additive.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Additive.{u2} α) α) (Additive.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Additive.{u2} α) α) (Additive.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (Additive.{u2} α) α))) (Additive.toMul.{u2} α) a) b) (HVAdd.hVAdd.{u2, u1, u1} (Additive.{u2} α) β β (instHVAdd.{u2, u1} (Additive.{u2} α) β (Additive.vadd.{u2, u1} α β _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align to_mul_smul toMul_smulₓ'. -/
@[simp]
theorem toMul_smul [HasSmul α β] (a) (b : β) : (toMul a : α) • b = a +ᵥ b :=
  rfl
#align to_mul_smul toMul_smul

/- warning: of_mul_vadd -> ofMul_vadd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} α β] (a : α) (b : β), Eq.{succ u2} β (VAdd.vadd.{u1, u2} (Additive.{u1} α) β (Additive.vadd.{u1, u2} α β _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Additive.{u1} α)) => α -> (Additive.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) a) b) (HasSmul.smul.{u1, u2} α β _inst_1 a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : α) (b : β), Eq.{succ u1} β (HVAdd.hVAdd.{u2, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Additive.{u2} α) a) β β (instHVAdd.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Additive.{u2} α) a) β (Additive.vadd.{u2, u1} α β _inst_1)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Additive.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Additive.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Additive.{u2} α)) α (Additive.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Additive.{u2} α)) α (Additive.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (Additive.{u2} α)))) (Additive.ofMul.{u2} α) a) b) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align of_mul_vadd ofMul_vaddₓ'. -/
@[simp]
theorem ofMul_vadd [HasSmul α β] (a : α) (b : β) : ofMul a +ᵥ b = a • b :=
  rfl
#align of_mul_vadd ofMul_vadd

/- warning: to_add_vadd -> toAdd_vadd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VAdd.{u1, u2} α β] (a : Multiplicative.{u1} α) (b : β), Eq.{succ u2} β (VAdd.vadd.{u1, u2} α β _inst_1 (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) => (Multiplicative.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) a) b) (HasSmul.smul.{u1, u2} (Multiplicative.{u1} α) β (Multiplicative.smul.{u1, u2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VAdd.{u2, u1} α β] (a : Multiplicative.{u2} α) (b : β), Eq.{succ u1} β (HVAdd.hVAdd.{u2, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Multiplicative.{u2} α) => α) a) β β (instHVAdd.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Multiplicative.{u2} α) => α) a) β _inst_1) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Multiplicative.{u2} α) α) (Multiplicative.{u2} α) (fun (_x : Multiplicative.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Multiplicative.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Multiplicative.{u2} α) α) (Multiplicative.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Multiplicative.{u2} α) α) (Multiplicative.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (Multiplicative.{u2} α) α))) (Multiplicative.toAdd.{u2} α) a) b) (HSMul.hSMul.{u2, u1, u1} (Multiplicative.{u2} α) β β (instHSMul.{u2, u1} (Multiplicative.{u2} α) β (Multiplicative.smul.{u2, u1} α β _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align to_add_vadd toAdd_vaddₓ'. -/
@[simp]
theorem toAdd_vadd [VAdd α β] (a) (b : β) : (toAdd a : α) +ᵥ b = a • b :=
  rfl
#align to_add_vadd toAdd_vadd

/- warning: of_add_smul -> ofAdd_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VAdd.{u1, u2} α β] (a : α) (b : β), Eq.{succ u2} β (HasSmul.smul.{u1, u2} (Multiplicative.{u1} α) β (Multiplicative.smul.{u1, u2} α β _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) => α -> (Multiplicative.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) a) b) (VAdd.vadd.{u1, u2} α β _inst_1 a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VAdd.{u2, u1} α β] (a : α) (b : β), Eq.{succ u1} β (HSMul.hSMul.{u2, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Multiplicative.{u2} α) a) β β (instHSMul.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Multiplicative.{u2} α) a) β (Multiplicative.smul.{u2, u1} α β _inst_1)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Multiplicative.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Multiplicative.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Multiplicative.{u2} α)) α (Multiplicative.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Multiplicative.{u2} α)) α (Multiplicative.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (Multiplicative.{u2} α)))) (Multiplicative.ofAdd.{u2} α) a) b) (HVAdd.hVAdd.{u2, u1, u1} α β β (instHVAdd.{u2, u1} α β _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align of_add_smul ofAdd_smulₓ'. -/
@[simp]
theorem ofAdd_smul [VAdd α β] (a : α) (b : β) : ofAdd a • b = a +ᵥ b :=
  rfl
#align of_add_smul ofAdd_smul

#print Additive.addAction /-
instance Additive.addAction [Monoid α] [MulAction α β] : AddAction (Additive α) β
    where
  zero_vadd := MulAction.one_smul
  add_vadd := MulAction.mul_smul
#align additive.add_action Additive.addAction
-/

#print Multiplicative.mulAction /-
instance Multiplicative.mulAction [AddMonoid α] [AddAction α β] : MulAction (Multiplicative α) β
    where
  one_smul := AddAction.zero_vadd
  mul_smul := AddAction.add_vadd
#align multiplicative.mul_action Multiplicative.mulAction
-/

/- warning: additive.add_action_is_pretransitive -> Additive.addAction_isPretransitive is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulAction.{u1, u2} α β _inst_1] [_inst_3 : MulAction.IsPretransitive.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_2)], AddAction.IsPretransitive.{u1, u2} (Additive.{u1} α) β (Additive.vadd.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulAction.{u1, u2} α β _inst_1] [_inst_3 : MulAction.IsPretransitive.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_2)], AddAction.IsPretransitive.{u1, u2} (Additive.{u1} α) β (Additive.vadd.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align additive.add_action_is_pretransitive Additive.addAction_isPretransitiveₓ'. -/
instance Additive.addAction_isPretransitive [Monoid α] [MulAction α β]
    [MulAction.IsPretransitive α β] : AddAction.IsPretransitive (Additive α) β :=
  ⟨@MulAction.exists_smul_eq α _ _ _⟩
#align additive.add_action_is_pretransitive Additive.addAction_isPretransitive

#print Multiplicative.mulAction_isPretransitive /-
instance Multiplicative.mulAction_isPretransitive [AddMonoid α] [AddAction α β]
    [AddAction.IsPretransitive α β] : MulAction.IsPretransitive (Multiplicative α) β :=
  ⟨@AddAction.exists_vadd_eq α _ _ _⟩
#align multiplicative.add_action_is_pretransitive Multiplicative.mulAction_isPretransitive
-/

/- warning: additive.vadd_comm_class -> Additive.vaddCommClass is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : HasSmul.{u1, u3} α γ] [_inst_2 : HasSmul.{u2, u3} β γ] [_inst_3 : SMulCommClass.{u1, u2, u3} α β γ _inst_1 _inst_2], VAddCommClass.{u1, u2, u3} (Additive.{u1} α) (Additive.{u2} β) γ (Additive.vadd.{u1, u3} α γ _inst_1) (Additive.vadd.{u2, u3} β γ _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SMul.{u1, u3} α γ] [_inst_2 : SMul.{u2, u3} β γ] [_inst_3 : SMulCommClass.{u1, u2, u3} α β γ _inst_1 _inst_2], VAddCommClass.{u1, u2, u3} (Additive.{u1} α) (Additive.{u2} β) γ (Additive.vadd.{u1, u3} α γ _inst_1) (Additive.vadd.{u2, u3} β γ _inst_2)
Case conversion may be inaccurate. Consider using '#align additive.vadd_comm_class Additive.vaddCommClassₓ'. -/
instance Additive.vaddCommClass [HasSmul α γ] [HasSmul β γ] [SMulCommClass α β γ] :
    VAddCommClass (Additive α) (Additive β) γ :=
  ⟨@smul_comm α β _ _ _ _⟩
#align additive.vadd_comm_class Additive.vaddCommClass

#print Multiplicative.smulCommClass /-
instance Multiplicative.smulCommClass [VAdd α γ] [VAdd β γ] [VAddCommClass α β γ] :
    SMulCommClass (Multiplicative α) (Multiplicative β) γ :=
  ⟨@vadd_comm α β _ _ _ _⟩
#align multiplicative.smul_comm_class Multiplicative.smulCommClass
-/

end

