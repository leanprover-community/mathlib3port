/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro

! This file was ported from Lean 3 source module algebra.group.defs
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Basic
import Mathbin.Logic.Function.Basic

/-!
# Typeclasses for (semi)groups and monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(add_)?(comm_)?(semigroup|monoid|group)`, where `add_` means that
the class uses additive notation and `comm_` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `algebra.group.basic`.

We also introduce notation classes `has_smul` and `has_vadd` for multiplicative and additive
actions and register the following instances:

- `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`;
- `has_smul ℕ M` for additive monoids `M`, and `has_smul ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `has_add.add`, `has_neg.neg`/`has_sub.sub`, `has_mul.mul`, `has_div.div`, and `has_pow.pow`.
- `a • b` is used as notation for `has_smul.smul a b`.
- `a +ᵥ b` is used as notation for `has_vadd.vadd a b`.

-/


open Function

#print VAdd /-
/-- Type class for the `+ᵥ` notation. -/
class VAdd (G : Type _) (P : Type _) where
  vadd : G → P → P
#align has_vadd VAdd
-/

#print VSub /-
/-- Type class for the `-ᵥ` notation. -/
class VSub (G : outParam (Type _)) (P : Type _) where
  vsub : P → P → G
#align has_vsub VSub
-/

#print SMul /-
/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
@[ext, to_additive]
class SMul (M : Type _) (α : Type _) where
  smul : M → α → α
#align has_smul SMul
#align has_vadd VAdd
-/

-- mathport name: «expr +ᵥ »
infixl:65 " +ᵥ " => VAdd.vadd

-- mathport name: «expr -ᵥ »
infixl:65 " -ᵥ " => VSub.vsub

-- mathport name: «expr • »
infixr:73 " • " => SMul.smul

attribute [to_additive_reorder 1] Pow

attribute [to_additive_reorder 1 4] Pow.pow

attribute [to_additive SMul] Pow

attribute [to_additive SMul.smul] Pow.pow

universe u

variable {G : Type _}

/- failed to parenthesize: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
[PrettyPrinter.parenthesize.input] (Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr
     [(Command.docComment
       "/--"
       "The simpset `field_simps` is used by the tactic `field_simp` to\nreduce an expression in a field to an expression of the form `n / d` where `n` and `d` are\ndivision-free. -/")]
     "register_simp_attr"
     `field_simps)-/-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/--
    The simpset `field_simps` is used by the tactic `field_simp` to
    reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
    division-free. -/
  register_simp_attr
  field_simps

section Mul

variable [Mul G]

#print leftMul /-
/-- `left_mul g` denotes left multiplication by `g` -/
@[to_additive "`left_add g` denotes left addition by `g`"]
def leftMul : G → G → G := fun g : G => fun x : G => g * x
#align left_mul leftMul
#align left_add leftAdd
-/

#print rightMul /-
/-- `right_mul g` denotes right multiplication by `g` -/
@[to_additive "`right_add g` denotes right addition by `g`"]
def rightMul : G → G → G := fun g : G => fun x : G => x * g
#align right_mul rightMul
#align right_add rightAdd
-/

#print IsLeftCancelMul /-
/-- A mixin for left cancellative multiplication. -/
@[protect_proj]
class IsLeftCancelMul (G : Type u) [Mul G] : Prop where
  mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c
#align is_left_cancel_mul IsLeftCancelMul
-/

#print IsRightCancelMul /-
/-- A mixin for right cancellative multiplication. -/
@[protect_proj]
class IsRightCancelMul (G : Type u) [Mul G] : Prop where
  mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c
#align is_right_cancel_mul IsRightCancelMul
-/

#print IsCancelMul /-
/-- A mixin for cancellative multiplication. -/
@[protect_proj]
class IsCancelMul (G : Type u) [Mul G] extends IsLeftCancelMul G, IsRightCancelMul G : Prop
#align is_cancel_mul IsCancelMul
-/

#print IsLeftCancelAdd /-
/-- A mixin for left cancellative addition. -/
@[protect_proj]
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  add_left_cancel : ∀ a b c : G, a + b = a + c → b = c
#align is_left_cancel_add IsLeftCancelAdd
-/

attribute [to_additive] IsLeftCancelMul

#print IsRightCancelAdd /-
/-- A mixin for right cancellative addition. -/
@[protect_proj]
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  add_right_cancel : ∀ a b c : G, a + b = c + b → a = c
#align is_right_cancel_add IsRightCancelAdd
-/

attribute [to_additive] IsRightCancelMul

#print IsCancelAdd /-
/-- A mixin for cancellative addition. -/
class IsCancelAdd (G : Type u) [Add G] extends IsLeftCancelAdd G, IsRightCancelAdd G : Prop
#align is_cancel_add IsCancelAdd
-/

attribute [to_additive] IsCancelMul

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

#print mul_left_cancel /-
@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  IsLeftCancelMul.mul_left_cancel a b c
#align mul_left_cancel mul_left_cancel
#align add_left_cancel add_left_cancel
-/

#print mul_left_cancel_iff /-
@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congr_arg _⟩
#align mul_left_cancel_iff mul_left_cancel_iff
#align add_left_cancel_iff add_left_cancel_iff
-/

#print mul_right_injective /-
@[to_additive]
theorem mul_right_injective (a : G) : Function.Injective ((· * ·) a) := fun b c => mul_left_cancel
#align mul_right_injective mul_right_injective
#align add_right_injective add_right_injective
-/

#print mul_right_inj /-
@[simp, to_additive]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff
#align mul_right_inj mul_right_inj
#align add_right_inj add_right_inj
-/

#print mul_ne_mul_right /-
@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff
#align mul_ne_mul_right mul_ne_mul_right
#align add_ne_add_right add_ne_add_right
-/

end IsLeftCancelMul

section IsRightCancelMul

variable [IsRightCancelMul G] {a b c : G}

#print mul_right_cancel /-
@[to_additive]
theorem mul_right_cancel : a * b = c * b → a = c :=
  IsRightCancelMul.mul_right_cancel a b c
#align mul_right_cancel mul_right_cancel
#align add_right_cancel add_right_cancel
-/

#print mul_right_cancel_iff /-
@[to_additive]
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congr_arg _⟩
#align mul_right_cancel_iff mul_right_cancel_iff
#align add_right_cancel_iff add_right_cancel_iff
-/

#print mul_left_injective /-
@[to_additive]
theorem mul_left_injective (a : G) : Function.Injective fun x => x * a := fun b c =>
  mul_right_cancel
#align mul_left_injective mul_left_injective
#align add_left_injective add_left_injective
-/

#print mul_left_inj /-
@[simp, to_additive]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff
#align mul_left_inj mul_left_inj
#align add_left_inj add_left_inj
-/

#print mul_ne_mul_left /-
@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff
#align mul_ne_mul_left mul_ne_mul_left
#align add_ne_add_left add_ne_add_left
-/

end IsRightCancelMul

end Mul

#print Semigroup /-
/-- A semigroup is a type with an associative `(*)`. -/
@[protect_proj, ext]
class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
#align semigroup Semigroup
-/

#print AddSemigroup /-
/-- An additive semigroup is a type with an associative `(+)`. -/
@[protect_proj, ext]
class AddSemigroup (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
#align add_semigroup AddSemigroup
-/

attribute [to_additive] Semigroup

section Semigroup

variable [Semigroup G]

/- warning: mul_assoc -> mul_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Semigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G _inst_1)) a b) c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G _inst_1)) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G _inst_1)) b c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Semigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G _inst_1)) a b) c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G _inst_1)) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G _inst_1)) b c))
Case conversion may be inaccurate. Consider using '#align mul_assoc mul_assocₓ'. -/
@[no_rsimp, to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc
#align mul_assoc mul_assoc
#align add_assoc add_assoc

/- warning: semigroup.to_is_associative -> Semigroup.to_isAssociative is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Semigroup.{u1} G], IsAssociative.{u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Semigroup.{u1} G], IsAssociative.{u1} G (fun (x._@.Mathlib.Algebra.Group.Defs._hyg.3041 : G) (x._@.Mathlib.Algebra.Group.Defs._hyg.3043 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G _inst_1)) x._@.Mathlib.Algebra.Group.Defs._hyg.3041 x._@.Mathlib.Algebra.Group.Defs._hyg.3043)
Case conversion may be inaccurate. Consider using '#align semigroup.to_is_associative Semigroup.to_isAssociativeₓ'. -/
@[to_additive]
instance Semigroup.to_isAssociative : IsAssociative G (· * ·) :=
  ⟨mul_assoc⟩
#align semigroup.to_is_associative Semigroup.to_isAssociative
#align add_semigroup.to_is_associative AddSemigroup.to_isAssociative

end Semigroup

#print CommSemigroup /-
/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[protect_proj, ext]
class CommSemigroup (G : Type u) extends Semigroup G where
  mul_comm : ∀ a b : G, a * b = b * a
#align comm_semigroup CommSemigroup
-/

#print AddCommSemigroup /-
/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[protect_proj, ext]
class AddCommSemigroup (G : Type u) extends AddSemigroup G where
  add_comm : ∀ a b : G, a + b = b + a
#align add_comm_semigroup AddCommSemigroup
-/

attribute [to_additive] CommSemigroup

section CommSemigroup

variable [CommSemigroup G]

/- warning: mul_comm -> mul_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align mul_comm mul_commₓ'. -/
@[no_rsimp, to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a :=
  CommSemigroup.mul_comm
#align mul_comm mul_comm
#align add_comm add_comm

/- warning: comm_semigroup.to_is_commutative -> CommSemigroup.to_isCommutative is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G], IsCommutative.{u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G], IsCommutative.{u1} G (fun (x._@.Mathlib.Algebra.Group.Defs._hyg.3154 : G) (x._@.Mathlib.Algebra.Group.Defs._hyg.3156 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) x._@.Mathlib.Algebra.Group.Defs._hyg.3154 x._@.Mathlib.Algebra.Group.Defs._hyg.3156)
Case conversion may be inaccurate. Consider using '#align comm_semigroup.to_is_commutative CommSemigroup.to_isCommutativeₓ'. -/
@[to_additive]
instance CommSemigroup.to_isCommutative : IsCommutative G (· * ·) :=
  ⟨mul_comm⟩
#align comm_semigroup.to_is_commutative CommSemigroup.to_isCommutative
#align add_comm_semigroup.to_is_commutative AddCommSemigroup.to_isCommutative

/- warning: comm_semigroup.is_right_cancel_mul.to_is_left_cancel_mul -> CommSemigroup.IsRightCancelMul.toIsLeftCancelMul is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_2 : CommSemigroup.{u1} G] [_inst_3 : IsRightCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))], IsLeftCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))
but is expected to have type
  forall (G : Type.{u1}) [_inst_2 : CommSemigroup.{u1} G] [_inst_3 : IsRightCancelMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))], IsLeftCancelMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))
Case conversion may be inaccurate. Consider using '#align comm_semigroup.is_right_cancel_mul.to_is_left_cancel_mul CommSemigroup.IsRightCancelMul.toIsLeftCancelMulₓ'. -/
/-- Any `comm_semigroup G` that satisfies `is_right_cancel_mul G` also satisfies
`is_left_cancel_mul G`. -/
@[to_additive AddCommSemigroup.IsRightCancelAdd.toIsLeftCancelAdd
      "Any\n`add_comm_semigroup G` that satisfies `is_right_cancel_add G` also satisfies\n`is_right_cancel_add G`."]
theorem CommSemigroup.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommSemigroup G]
    [IsRightCancelMul G] : IsLeftCancelMul G :=
  ⟨fun a b c h => mul_right_cancel <| (mul_comm _ _).trans (h.trans <| mul_comm _ _)⟩
#align comm_semigroup.is_right_cancel_mul.to_is_left_cancel_mul CommSemigroup.IsRightCancelMul.toIsLeftCancelMul
#align add_comm_semigroup.is_right_cancel_add.to_is_left_cancel_add AddCommSemigroup.IsRightCancelAdd.toIsLeftCancelAdd

/- warning: comm_semigroup.is_left_cancel_mul.to_is_right_cancel_mul -> CommSemigroup.IsLeftCancelMul.toIsRightCancelMul is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_2 : CommSemigroup.{u1} G] [_inst_3 : IsLeftCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))], IsRightCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))
but is expected to have type
  forall (G : Type.{u1}) [_inst_2 : CommSemigroup.{u1} G] [_inst_3 : IsLeftCancelMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))], IsRightCancelMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))
Case conversion may be inaccurate. Consider using '#align comm_semigroup.is_left_cancel_mul.to_is_right_cancel_mul CommSemigroup.IsLeftCancelMul.toIsRightCancelMulₓ'. -/
/-- Any `comm_semigroup G` that satisfies `is_left_cancel_mul G` also satisfies
`is_right_cancel_mul G`. -/
@[to_additive AddCommSemigroup.IsLeftCancelAdd.toIsRightCancelAdd
      "Any\n`add_comm_semigroup G` that satisfies `is_left_cancel_add G` also satisfies\n`is_left_cancel_add G`."]
theorem CommSemigroup.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommSemigroup G]
    [IsLeftCancelMul G] : IsRightCancelMul G :=
  ⟨fun a b c h => mul_left_cancel <| (mul_comm _ _).trans (h.trans <| mul_comm _ _)⟩
#align comm_semigroup.is_left_cancel_mul.to_is_right_cancel_mul CommSemigroup.IsLeftCancelMul.toIsRightCancelMul
#align add_comm_semigroup.is_left_cancel_add.to_is_right_cancel_add AddCommSemigroup.IsLeftCancelAdd.toIsRightCancelAdd

/- warning: comm_semigroup.is_left_cancel_mul.to_is_cancel_mul -> CommSemigroup.IsLeftCancelMul.toIsCancelMul is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_2 : CommSemigroup.{u1} G] [_inst_3 : IsLeftCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))], IsCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))
but is expected to have type
  forall (G : Type.{u1}) [_inst_2 : CommSemigroup.{u1} G] [_inst_3 : IsLeftCancelMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))], IsCancelMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))
Case conversion may be inaccurate. Consider using '#align comm_semigroup.is_left_cancel_mul.to_is_cancel_mul CommSemigroup.IsLeftCancelMul.toIsCancelMulₓ'. -/
/-- Any `comm_semigroup G` that satisfies `is_left_cancel_mul G` also satisfies
`is_cancel_mul G`. -/
@[to_additive AddCommSemigroup.IsLeftCancelAdd.toIsCancelAdd
      "Any `add_comm_semigroup G`\nthat satisfies `is_left_cancel_add G` also satisfies `is_cancel_add G`."]
theorem CommSemigroup.IsLeftCancelMul.toIsCancelMul (G : Type u) [CommSemigroup G]
    [IsLeftCancelMul G] : IsCancelMul G :=
  { ‹IsLeftCancelMul G›, CommSemigroup.IsLeftCancelMul.toIsRightCancelMul G with }
#align comm_semigroup.is_left_cancel_mul.to_is_cancel_mul CommSemigroup.IsLeftCancelMul.toIsCancelMul
#align add_comm_semigroup.is_left_cancel_add.to_is_cancel_add AddCommSemigroup.IsLeftCancelAdd.toIsCancelAdd

/- warning: comm_semigroup.is_right_cancel_mul.to_is_cancel_mul -> CommSemigroup.IsRightCancelMul.toIsCancelMul is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_2 : CommSemigroup.{u1} G] [_inst_3 : IsRightCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))], IsCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))
but is expected to have type
  forall (G : Type.{u1}) [_inst_2 : CommSemigroup.{u1} G] [_inst_3 : IsRightCancelMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))], IsCancelMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_2))
Case conversion may be inaccurate. Consider using '#align comm_semigroup.is_right_cancel_mul.to_is_cancel_mul CommSemigroup.IsRightCancelMul.toIsCancelMulₓ'. -/
/-- Any `comm_semigroup G` that satisfies `is_right_cancel_mul G` also satisfies
`is_cancel_mul G`. -/
@[to_additive AddCommSemigroup.IsRightCancelAdd.toIsCancelAdd
      "Any `add_comm_semigroup G`\nthat satisfies `is_right_cancel_add G` also satisfies `is_cancel_add G`."]
theorem CommSemigroup.IsRightCancelMul.toIsCancelMul (G : Type u) [CommSemigroup G]
    [IsRightCancelMul G] : IsCancelMul G :=
  { ‹IsRightCancelMul G›, CommSemigroup.IsRightCancelMul.toIsLeftCancelMul G with }
#align comm_semigroup.is_right_cancel_mul.to_is_cancel_mul CommSemigroup.IsRightCancelMul.toIsCancelMul
#align add_comm_semigroup.is_right_cancel_add.to_is_cancel_add AddCommSemigroup.IsRightCancelAdd.toIsCancelAdd

end CommSemigroup

#print LeftCancelSemigroup /-
/-- A `left_cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[protect_proj, ext]
class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c
#align left_cancel_semigroup LeftCancelSemigroup
-/

#print AddLeftCancelSemigroup /-
/-- An `add_left_cancel_semigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[protect_proj, ext]
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_left_cancel : ∀ a b c : G, a + b = a + c → b = c
#align add_left_cancel_semigroup AddLeftCancelSemigroup
-/

attribute [to_additive AddLeftCancelSemigroup] LeftCancelSemigroup

/- warning: left_cancel_semigroup.to_is_left_cancel_mul -> LeftCancelSemigroup.toIsLeftCancelMul is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : LeftCancelSemigroup.{u1} G], IsLeftCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (LeftCancelSemigroup.toSemigroup.{u1} G _inst_1))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : LeftCancelSemigroup.{u1} G], IsLeftCancelMul.{u1} G (Semigroup.toMul.{u1} G (LeftCancelSemigroup.toSemigroup.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align left_cancel_semigroup.to_is_left_cancel_mul LeftCancelSemigroup.toIsLeftCancelMulₓ'. -/
/-- Any `left_cancel_semigroup` satisfies `is_left_cancel_mul`. -/
@[to_additive "Any `add_left_cancel_semigroup` satisfies `is_left_cancel_add`."]
instance (priority := 100) LeftCancelSemigroup.toIsLeftCancelMul (G : Type u)
    [LeftCancelSemigroup G] : IsLeftCancelMul G
    where mul_left_cancel := LeftCancelSemigroup.mul_left_cancel
#align left_cancel_semigroup.to_is_left_cancel_mul LeftCancelSemigroup.toIsLeftCancelMul
#align add_left_cancel_semigroup.to_is_left_cancel_add AddLeftCancelSemigroup.toIsLeftCancelAdd

#print RightCancelSemigroup /-
/-- A `right_cancel_semigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[protect_proj, ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G where
  mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c
#align right_cancel_semigroup RightCancelSemigroup
-/

#print AddRightCancelSemigroup /-
/-- An `add_right_cancel_semigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[protect_proj, ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_right_cancel : ∀ a b c : G, a + b = c + b → a = c
#align add_right_cancel_semigroup AddRightCancelSemigroup
-/

attribute [to_additive AddRightCancelSemigroup] RightCancelSemigroup

/- warning: right_cancel_semigroup.to_is_right_cancel_mul -> RightCancelSemigroup.toIsRightCancelMul is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : RightCancelSemigroup.{u1} G], IsRightCancelMul.{u1} G (Semigroup.toHasMul.{u1} G (RightCancelSemigroup.toSemigroup.{u1} G _inst_1))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : RightCancelSemigroup.{u1} G], IsRightCancelMul.{u1} G (Semigroup.toMul.{u1} G (RightCancelSemigroup.toSemigroup.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align right_cancel_semigroup.to_is_right_cancel_mul RightCancelSemigroup.toIsRightCancelMulₓ'. -/
/-- Any `right_cancel_semigroup` satisfies `is_right_cancel_mul`. -/
@[to_additive "Any `add_right_cancel_semigroup` satisfies `is_right_cancel_add`."]
instance (priority := 100) RightCancelSemigroup.toIsRightCancelMul (G : Type u)
    [RightCancelSemigroup G] : IsRightCancelMul G
    where mul_right_cancel := RightCancelSemigroup.mul_right_cancel
#align right_cancel_semigroup.to_is_right_cancel_mul RightCancelSemigroup.toIsRightCancelMul
#align add_right_cancel_semigroup.to_is_right_cancel_add AddRightCancelSemigroup.toIsRightCancelAdd

#print MulOneClass /-
/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a
#align mul_one_class MulOneClass
-/

#print AddZeroClass /-
/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (M : Type u) extends Zero M, Add M where
  zero_add : ∀ a : M, 0 + a = a
  add_zero : ∀ a : M, a + 0 = a
#align add_zero_class AddZeroClass
-/

attribute [to_additive] MulOneClass

/- warning: mul_one_class.ext -> MulOneClass.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {{m₁ : MulOneClass.{u1} M}} {{m₂ : MulOneClass.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (MulOneClass.mul.{u1} M m₁) (MulOneClass.mul.{u1} M m₂)) -> (Eq.{succ u1} (MulOneClass.{u1} M) m₁ m₂)
but is expected to have type
  forall {M : Type.{u1}} {{m₁ : MulOneClass.{u1} M}} {{m₂ : MulOneClass.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (Mul.mul.{u1} M (MulOneClass.toMul.{u1} M m₁)) (Mul.mul.{u1} M (MulOneClass.toMul.{u1} M m₂))) -> (Eq.{succ u1} (MulOneClass.{u1} M) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align mul_one_class.ext MulOneClass.extₓ'. -/
@[ext, to_additive]
theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ :=
  by
  rintro ⟨one₁, mul₁, one_mul₁, mul_one₁⟩ ⟨one₂, mul₂, one_mul₂, mul_one₂⟩ (rfl : mul₁ = mul₂)
  congr
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)
#align mul_one_class.ext MulOneClass.ext
#align add_zero_class.ext AddZeroClass.ext

section MulOneClass

variable {M : Type u} [MulOneClass M]

/- warning: one_mul -> one_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (a : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) a) a
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (a : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) a) a
Case conversion may be inaccurate. Consider using '#align one_mul one_mulₓ'. -/
@[ematch, simp, to_additive]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul
#align one_mul one_mul
#align zero_add zero_add

/- warning: mul_one -> mul_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (a : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) a
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (a : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) a (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) a
Case conversion may be inaccurate. Consider using '#align mul_one mul_oneₓ'. -/
@[ematch, simp, to_additive]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one
#align mul_one mul_one
#align add_zero add_zero

@[to_additive]
instance MulOneClass.to_isLeftId : IsLeftId M (· * ·) 1 :=
  ⟨MulOneClass.one_mul⟩
#align mul_one_class.to_is_left_id MulOneClass.to_isLeftId
#align add_zero_class.to_is_left_id AddZeroClass.to_isLeftId

@[to_additive]
instance MulOneClass.to_isRightId : IsRightId M (· * ·) 1 :=
  ⟨MulOneClass.mul_one⟩
#align mul_one_class.to_is_right_id MulOneClass.to_isRightId
#align add_zero_class.to_is_right_id AddZeroClass.to_isRightId

end MulOneClass

section

variable {M : Type u}

#print npowRec /-
-- use `x * npow_rec n x` and not `npow_rec n x * x` in the definition to make sure that
-- definitional unfolding of `npow_rec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `npow_rec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, a => 1
  | n + 1, a => a * npowRec n a
#align npow_rec npowRec
-/

#print nsmulRec /-
/-- The fundamental scalar multiplication in an additive monoid. `nsmul_rec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, a => 0
  | n + 1, a => a + nsmulRec n a
#align nsmul_rec nsmulRec
-/

attribute [to_additive] npowRec

end

library_note "forgetful inheritance"/--
Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = metric_space` and `P = topological_space`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `metric_space` / `topological_space`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `topological_space`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `metric_space` and
`topological_space` called `uniform_space`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`uniform_space.of_core` or `real_inner_product.of_core`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- `try_refl_tac` solves goals of the form `∀ a b, f a b = g a b`,
if they hold by definition. -/
unsafe def try_refl_tac : tactic Unit :=
  sorry
#align try_refl_tac try_refl_tac

/-!
### Design note on `add_monoid` and `monoid`

An `add_monoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`R[X]` has a natural `R`-action defined by multiplication on the coefficients. This means
that `ℕ[X]` would have two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself).

To solve this issue, we embed an `ℕ`-action in the definition of an `add_monoid` (which is by
default equal to the naive action `a + ... + a`, but can be adjusted when needed), and declare
a `has_smul ℕ α` instance using this action. See Note [forgetful inheritance] for more
explanations on this pattern.

For example, when we define `R[X]`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `add_monoid`). In this way, the two natural `has_smul ℕ ℕ[X]` instances are defeq.

The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.

A basic theory for the power function on monoids and the `ℕ`-action on additive monoids is built in
the file `algebra.group_power.basic`. For now, we only register the most basic properties that we
need right away.

In the definition, we use `n.succ` instead of `n + 1` in the `nsmul_succ'` and `npow_succ'` fields
to make sure that `to_additive` is not confused (otherwise, it would try to convert `1 : ℕ`
to `0 : ℕ`).
-/


#print AddMonoid /-
/-- An `add_monoid` is an `add_semigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  nsmul : ℕ → M → M := nsmulRec
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by
    intros
    rfl
  nsmul_succ :
    ∀ (n : ℕ) (x), nsmul n.succ x = x +
          nsmul n x := by
    intros
    rfl
#align add_monoid AddMonoid
-/

#print Monoid /-
/-- A `monoid` is a `semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  npow : ℕ → M → M := npowRec
  npow_zero : ∀ x, npow 0 x = 1 := by
    intros
    rfl
  npow_succ :
    ∀ (n : ℕ) (x), npow n.succ x = x * npow n
            x := by
    intros
    rfl
#align monoid Monoid
#align add_monoid AddMonoid
-/

#print Monoid.Pow /-
instance Monoid.Pow {M : Type _} [Monoid M] : Pow M ℕ :=
  ⟨fun x n => Monoid.npow n x⟩
#align monoid.has_pow Monoid.Pow
-/

#print AddMonoid.SMul /-
instance AddMonoid.SMul {M : Type _} [AddMonoid M] : SMul ℕ M :=
  ⟨AddMonoid.nsmul⟩
#align add_monoid.has_smul_nat AddMonoid.SMul
-/

attribute [to_additive AddMonoid.SMul] Monoid.Pow

section

variable {M : Type _} [Monoid M]

#print npow_eq_pow /-
@[simp, to_additive nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n :=
  rfl
#align npow_eq_pow npow_eq_pow
#align nsmul_eq_smul nsmul_eq_smul
-/

/- warning: pow_zero -> pow_zero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M), Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M), Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align pow_zero pow_zeroₓ'. -/
-- the attributes are intentionally out of order. `zero_smul` proves `zero_nsmul`.
@[to_additive zero_nsmul, simp]
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero _
#align pow_zero pow_zero
#align zero_nsmul zero_nsmul

/- warning: pow_succ -> pow_succ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M) (n : Nat), Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a n))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M) (n : Nat), Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a n))
Case conversion may be inaccurate. Consider using '#align pow_succ pow_succₓ'. -/
@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n :=
  Monoid.npow_succ n a
#align pow_succ pow_succ
#align succ_nsmul succ_nsmul

end

section Monoid

variable {M : Type u} [Monoid M]

/- warning: left_inv_eq_right_inv -> left_inv_eq_right_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {b : M} {c : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) b a) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a c) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (Eq.{succ u1} M b c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {b : M} {c : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) b a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a c) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (Eq.{succ u1} M b c)
Case conversion may be inaccurate. Consider using '#align left_inv_eq_right_inv left_inv_eq_right_invₓ'. -/
@[to_additive]
theorem left_inv_eq_right_inv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]
#align left_inv_eq_right_inv left_inv_eq_right_inv
#align left_neg_eq_right_neg left_neg_eq_right_neg

end Monoid

#print AddCommMonoid /-
/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj]
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M
#align add_comm_monoid AddCommMonoid
-/

#print CommMonoid /-
/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[protect_proj, to_additive]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M
#align comm_monoid CommMonoid
#align add_comm_monoid AddCommMonoid
-/

section LeftCancelMonoid

#print AddLeftCancelMonoid /-
/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
@[protect_proj]
class AddLeftCancelMonoid (M : Type u) extends AddLeftCancelSemigroup M, AddMonoid M
#align add_left_cancel_monoid AddLeftCancelMonoid
-/

#print LeftCancelMonoid /-
/-- A monoid in which multiplication is left-cancellative. -/
@[protect_proj, to_additive AddLeftCancelMonoid]
class LeftCancelMonoid (M : Type u) extends LeftCancelSemigroup M, Monoid M
#align left_cancel_monoid LeftCancelMonoid
#align add_left_cancel_monoid AddLeftCancelMonoid
-/

end LeftCancelMonoid

section RightCancelMonoid

#print AddRightCancelMonoid /-
/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj]
class AddRightCancelMonoid (M : Type u) extends AddRightCancelSemigroup M, AddMonoid M
#align add_right_cancel_monoid AddRightCancelMonoid
-/

#print RightCancelMonoid /-
/-- A monoid in which multiplication is right-cancellative. -/
@[protect_proj, to_additive AddRightCancelMonoid]
class RightCancelMonoid (M : Type u) extends RightCancelSemigroup M, Monoid M
#align right_cancel_monoid RightCancelMonoid
#align add_right_cancel_monoid AddRightCancelMonoid
-/

end RightCancelMonoid

section CancelMonoid

#print AddCancelMonoid /-
/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj]
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M
#align add_cancel_monoid AddCancelMonoid
-/

#print CancelMonoid /-
/-- A monoid in which multiplication is cancellative. -/
@[protect_proj, to_additive AddCancelMonoid]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M
#align cancel_monoid CancelMonoid
#align add_cancel_monoid AddCancelMonoid
-/

#print AddCancelCommMonoid /-
/-- Commutative version of `add_cancel_monoid`. -/
@[protect_proj]
class AddCancelCommMonoid (M : Type u) extends AddLeftCancelMonoid M, AddCommMonoid M
#align add_cancel_comm_monoid AddCancelCommMonoid
-/

#print CancelCommMonoid /-
/-- Commutative version of `cancel_monoid`. -/
@[protect_proj, to_additive AddCancelCommMonoid]
class CancelCommMonoid (M : Type u) extends LeftCancelMonoid M, CommMonoid M
#align cancel_comm_monoid CancelCommMonoid
#align add_cancel_comm_monoid AddCancelCommMonoid
-/

#print CancelCommMonoid.toCancelMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] :
    CancelMonoid M :=
  { ‹CancelCommMonoid M›, CommSemigroup.IsLeftCancelMul.toIsRightCancelMul M with }
#align cancel_comm_monoid.to_cancel_monoid CancelCommMonoid.toCancelMonoid
#align add_cancel_comm_monoid.to_cancel_add_monoid AddCancelCommMonoid.toAddCancelMonoid
-/

/- warning: cancel_monoid.to_is_cancel_mul -> CancelMonoid.toIsCancelMul is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : CancelMonoid.{u1} M], IsCancelMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M _inst_1))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : CancelMonoid.{u1} M], IsCancelMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align cancel_monoid.to_is_cancel_mul CancelMonoid.toIsCancelMulₓ'. -/
/-- Any `cancel_monoid M` satisfies `is_cancel_mul M`. -/
@[to_additive "Any `add_cancel_monoid M` satisfies `is_cancel_add M`."]
instance (priority := 100) CancelMonoid.toIsCancelMul (M : Type u) [CancelMonoid M] : IsCancelMul M
    where
  mul_left_cancel := CancelMonoid.mul_left_cancel
  mul_right_cancel := CancelMonoid.mul_right_cancel
#align cancel_monoid.to_is_cancel_mul CancelMonoid.toIsCancelMul
#align add_cancel_monoid.to_is_cancel_add AddCancelMonoid.toIsCancelAdd

end CancelMonoid

#print zpowRec /-
/-- The fundamental power operation in a group. `zpow_rec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`,  which has better definitional behavior. -/
def zpowRec {M : Type _} [One M] [Mul M] [Inv M] : ℤ → M → M
  | Int.ofNat n, a => npowRec n a
  | -[n+1], a => (npowRec n.succ a)⁻¹
#align zpow_rec zpowRec
-/

#print zsmulRec /-
/-- The fundamental scalar multiplication in an additive group. `zsmul_rec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmulRec {M : Type _} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmulRec n a
  | -[n+1], a => -nsmulRec n.succ a
#align zsmul_rec zsmulRec
-/

attribute [to_additive] zpowRec

section InvolutiveInv

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option extends_priority -/
-- ensure that we don't go via these typeclasses to find `has_inv` on groups and groups with zero
set_option extends_priority 50

#print InvolutiveNeg /-
/-- Auxiliary typeclass for types with an involutive `has_neg`. -/
class InvolutiveNeg (A : Type _) extends Neg A where
  neg_neg : ∀ x : A, - -x = x
#align has_involutive_neg InvolutiveNeg
-/

#print InvolutiveInv /-
/-- Auxiliary typeclass for types with an involutive `has_inv`. -/
@[to_additive]
class InvolutiveInv (G : Type _) extends Inv G where
  inv_inv : ∀ x : G, x⁻¹⁻¹ = x
#align has_involutive_inv InvolutiveInv
#align has_involutive_neg InvolutiveNeg
-/

variable [InvolutiveInv G]

/- warning: inv_inv -> inv_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] (a : G), Eq.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) a)) a
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] (a : G), Eq.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) a)) a
Case conversion may be inaccurate. Consider using '#align inv_inv inv_invₓ'. -/
@[simp, to_additive]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  InvolutiveInv.inv_inv _
#align inv_inv inv_inv
#align neg_neg neg_neg

end InvolutiveInv

/-!
### Design note on `div_inv_monoid`/`sub_neg_monoid` and `division_monoid`/`subtraction_monoid`

Those two pairs of made-up classes fulfill slightly different roles.

`div_inv_monoid`/`sub_neg_monoid` provides the minimum amount of information to define the
`ℤ` action (`zpow` or `zsmul`). Further, it provides a `div` field, matching the forgetful
inheritance pattern. This is useful to shorten extension clauses of stronger structures (`group`,
`group_with_zero`, `division_ring`, `field`) and for a few structures with a rather weak
pseudo-inverse (`matrix`).

`division_monoid`/`subtraction_monoid` is targeted at structures with stronger pseudo-inverses. It
is an ad hoc collection of axioms that are mainly respected by three things:
* Groups
* Groups with zero
* The pointwise monoids `set α`, `finset α`, `filter α`

It acts as a middle ground for structures with an inversion operator that plays well with
multiplication, except for the fact that it might not be a true inverse (`a / a ≠ 1` in general).
The axioms are pretty arbitrary (many other combinations are equivalent to it), but they are
independent:
* Without `division_monoid.div_eq_mul_inv`, you can define `/` arbitrarily.
* Without `division_monoid.inv_inv`, you can consider `with_top unit` with `a⁻¹ = ⊤` for all `a`.
* Without `division_monoid.mul_inv_rev`, you can consider `with_top α` with `a⁻¹ = a` for all `a`
  where `α` non commutative.
* Without `division_monoid.inv_eq_of_mul`, you can consider any `comm_monoid` with `a⁻¹ = a` for all
  `a`.

As a consequence, a few natural structures do not fit in this framework. For example, `ennreal`
respects everything except for the fact that `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0 * ∞ = 0`.
-/


#print DivInvMonoid /-
/-- A `div_inv_monoid` is a `monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no
`∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we
also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the
`(/)` coming from `group_with_zero_has_div` cannot be definitionally equal to
the `(/)` coming from `foo.has_div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj]
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  div := fun a b => a * b⁻¹
  div_eq_mul_inv :
    ∀ a b : G, a / b = a * b⁻¹ := by
    intros
    rfl
  zpow : ℤ → G → G := zpowRec
  zpow_zero' : ∀ a : G, zpow 0 a = 1 := by
    intros
    rfl
  zpow_succ' :
    ∀ (n : ℕ) (a : G),
      zpow (Int.ofNat n.succ) a =
        a * zpow (Int.ofNat n) a := by
    intros
    rfl
  zpow_neg' :
    ∀ (n : ℕ) (a : G), zpow -[n+1] a =
        (zpow n.succ a)⁻¹ := by
    intros
    rfl
#align div_inv_monoid DivInvMonoid
-/

#print SubNegMonoid /-
/-- A `sub_neg_monoid` is an `add_monoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_sub (foo X)` instance but no
`∀ X, has_neg (foo X)`. Suppose we also have an instance
`∀ X [cromulent X], add_group (foo X)`. Then the `(-)` coming from
`add_group.has_sub` cannot be definitionally equal to the `(-)` coming from
`foo.has_sub`.

In the same way, adding a `zsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `add_monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj]
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  sub := fun a b => a + -b
  sub_eq_add_neg :
    ∀ a b : G, a - b = a + -b := by
    intros
    rfl
  zsmul : ℤ → G → G := zsmulRec
  zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by
    intros
    rfl
  zsmul_succ' :
    ∀ (n : ℕ) (a : G),
      zsmul (Int.ofNat n.succ) a =
        a + zsmul (Int.ofNat n) a := by
    intros
    rfl
  zsmul_neg' :
    ∀ (n : ℕ) (a : G), zsmul -[n+1] a =
        -zsmul n.succ a := by
    intros
    rfl
#align sub_neg_monoid SubNegMonoid
-/

attribute [to_additive SubNegMonoid] DivInvMonoid

#print DivInvMonoid.Pow /-
instance DivInvMonoid.Pow {M} [DivInvMonoid M] : Pow M ℤ :=
  ⟨fun x n => DivInvMonoid.zpow n x⟩
#align div_inv_monoid.has_pow DivInvMonoid.Pow
-/

#print SubNegMonoid.SMulInt /-
instance SubNegMonoid.SMulInt {M} [SubNegMonoid M] : SMul ℤ M :=
  ⟨SubNegMonoid.zsmul⟩
#align sub_neg_monoid.has_smul_int SubNegMonoid.SMulInt
-/

attribute [to_additive SubNegMonoid.SMulInt] DivInvMonoid.Pow

section DivInvMonoid

variable [DivInvMonoid G] {a b : G}

#print zpow_eq_pow /-
@[simp, to_additive zsmul_eq_smul]
theorem zpow_eq_pow (n : ℤ) (x : G) : DivInvMonoid.zpow n x = x ^ n :=
  rfl
#align zpow_eq_pow zpow_eq_pow
#align zsmul_eq_smul zsmul_eq_smul
-/

/- warning: zpow_zero -> zpow_zero is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G _inst_1)) a (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G _inst_1)) a (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align zpow_zero zpow_zeroₓ'. -/
@[simp, to_additive zero_zsmul]
theorem zpow_zero (a : G) : a ^ (0 : ℤ) = 1 :=
  DivInvMonoid.zpow_zero' a
#align zpow_zero zpow_zero
#align zero_zsmul zero_zsmul

#print zpow_ofNat /-
@[simp, norm_cast, to_additive coe_nat_zsmul]
theorem zpow_ofNat (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 =>
    calc
      a ^ (↑(n + 1) : ℤ) = a * a ^ (n : ℤ) := DivInvMonoid.zpow_succ' _ _
      _ = a * a ^ n := congr_arg ((· * ·) a) (zpow_ofNat n)
      _ = a ^ (n + 1) := (pow_succ _ _).symm
      
#align zpow_coe_nat zpow_ofNat
#align of_nat_zsmul ofNat_zsmul
-/

/- warning: zpow_of_nat clashes with zpow_coe_nat -> zpow_ofNat
Case conversion may be inaccurate. Consider using '#align zpow_of_nat zpow_ofNatₓ'. -/
#print zpow_ofNat /-
@[to_additive ofNat_zsmul]
theorem zpow_ofNat (a : G) (n : ℕ) : a ^ Int.ofNat n = a ^ n :=
  zpow_ofNat a n
#align zpow_of_nat zpow_ofNat
#align of_nat_zsmul ofNat_zsmul
-/

/- warning: zpow_neg_succ_of_nat -> zpow_negSucc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (n : Nat), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G _inst_1)) a (Int.negSucc n)) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_1) (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1))) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (n : Nat), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G _inst_1)) a (Int.negSucc n)) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G _inst_1) (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1))) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align zpow_neg_succ_of_nat zpow_negSuccₓ'. -/
@[simp, to_additive]
theorem zpow_negSucc (a : G) (n : ℕ) : a ^ -[n+1] = (a ^ (n + 1))⁻¹ :=
  by
  rw [← zpow_ofNat]
  exact DivInvMonoid.zpow_neg' n a
#align zpow_neg_succ_of_nat zpow_negSucc
#align zsmul_neg_succ_of_nat negSucc_zsmul

/- warning: div_eq_mul_inv -> div_eq_mul_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_1) b))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G _inst_1) b))
Case conversion may be inaccurate. Consider using '#align div_eq_mul_inv div_eq_mul_invₓ'. -/
/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `div_inv_monoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive
      "Subtracting an element is the same as adding by its negative.\n\nThis is a duplicate of `sub_neg_monoid.sub_eq_mul_neg` ensuring that the types unfold better."]
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _
#align div_eq_mul_inv div_eq_mul_inv
#align sub_eq_add_neg sub_eq_add_neg

/- warning: division_def -> division_def is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_1) b))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G _inst_1) b))
Case conversion may be inaccurate. Consider using '#align division_def division_defₓ'. -/
alias div_eq_mul_inv ← division_def
#align division_def division_def

end DivInvMonoid

section InvOneClass

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option extends_priority -/
set_option extends_priority 50

#print NegZeroClass /-
/-- Typeclass for expressing that `-0 = 0`. -/
class NegZeroClass (G : Type _) extends Zero G, Neg G where
  neg_zero : -(0 : G) = 0
#align neg_zero_class NegZeroClass
-/

#print SubNegZeroMonoid /-
/-- A `sub_neg_monoid` where `-0 = 0`. -/
class SubNegZeroMonoid (G : Type _) extends SubNegMonoid G, NegZeroClass G
#align sub_neg_zero_monoid SubNegZeroMonoid
-/

#print InvOneClass /-
/-- Typeclass for expressing that `1⁻¹ = 1`. -/
@[to_additive]
class InvOneClass (G : Type _) extends One G, Inv G where
  inv_one : (1 : G)⁻¹ = 1
#align inv_one_class InvOneClass
#align neg_zero_class NegZeroClass
-/

attribute [to_additive NegZeroClass.toHasNeg] InvOneClass.toHasInv

attribute [to_additive NegZeroClass.toHasZero] InvOneClass.toHasOne

#print DivInvOneMonoid /-
/-- A `div_inv_monoid` where `1⁻¹ = 1`. -/
@[to_additive SubNegZeroMonoid]
class DivInvOneMonoid (G : Type _) extends DivInvMonoid G, InvOneClass G
#align div_inv_one_monoid DivInvOneMonoid
#align sub_neg_zero_monoid SubNegZeroMonoid
-/

attribute [to_additive SubNegZeroMonoid.toSubNegMonoid] DivInvOneMonoid.toDivInvMonoid

attribute [to_additive SubNegZeroMonoid.toNegZeroClass] DivInvOneMonoid.toInvOneClass

variable [InvOneClass G]

/- warning: inv_one -> inv_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : InvOneClass.{u1} G], Eq.{succ u1} G (Inv.inv.{u1} G (InvOneClass.toHasInv.{u1} G _inst_1) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (InvOneClass.toHasOne.{u1} G _inst_1))))) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (InvOneClass.toHasOne.{u1} G _inst_1))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : InvOneClass.{u1} G], Eq.{succ u1} G (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G _inst_1) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G _inst_1)))) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align inv_one inv_oneₓ'. -/
@[simp, to_additive]
theorem inv_one : (1 : G)⁻¹ = 1 :=
  InvOneClass.inv_one
#align inv_one inv_one
#align neg_zero neg_zero

end InvOneClass

#print SubtractionMonoid /-
/-- A `subtraction_monoid` is a `sub_neg_monoid` with involutive negation and such that
`-(a + b) = -b + -a` and `a + b = 0 → -a = b`. -/
@[protect_proj]
class SubtractionMonoid (G : Type u) extends SubNegMonoid G, InvolutiveNeg G where
  neg_add_rev (a b : G) : -(a + b) = -b + -a
  /- Despite the asymmetry of `neg_eq_of_add`, the symmetric version is true thanks to the
  involutivity of negation. -/
  neg_eq_of_add (a b : G) : a + b = 0 → -a = b
#align subtraction_monoid SubtractionMonoid
-/

#print DivisionMonoid /-
/-- A `division_monoid` is a `div_inv_monoid` with involutive inversion and such that
`(a * b)⁻¹ = b⁻¹ * a⁻¹` and `a * b = 1 → a⁻¹ = b`.

This is the immediate common ancestor of `group` and `group_with_zero`. -/
@[protect_proj, to_additive]
class DivisionMonoid (G : Type u) extends DivInvMonoid G, InvolutiveInv G where
  mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  /- Despite the asymmetry of `inv_eq_of_mul`, the symmetric version is true thanks to the
  involutivity of inversion. -/
  inv_eq_of_mul (a b : G) : a * b = 1 → a⁻¹ = b
#align division_monoid DivisionMonoid
#align subtraction_monoid SubtractionMonoid
-/

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

/- warning: mul_inv_rev -> mul_inv_rev is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] (a : G) (b : G), Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) b) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] (a : G) (b : G), Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) b) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) a))
Case conversion may be inaccurate. Consider using '#align mul_inv_rev mul_inv_revₓ'. -/
@[simp, to_additive neg_add_rev]
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  DivisionMonoid.mul_inv_rev _ _
#align mul_inv_rev mul_inv_rev
#align neg_add_rev neg_add_rev

/- warning: inv_eq_of_mul_eq_one_right -> inv_eq_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] {a : G} {b : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))))))) -> (Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) a) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] {a : G} {b : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))))) -> (Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) a) b)
Case conversion may be inaccurate. Consider using '#align inv_eq_of_mul_eq_one_right inv_eq_of_mul_eq_one_rightₓ'. -/
@[to_additive]
theorem inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b :=
  DivisionMonoid.inv_eq_of_mul _ _
#align inv_eq_of_mul_eq_one_right inv_eq_of_mul_eq_one_right
#align neg_eq_of_add_eq_zero_right neg_eq_of_add_eq_zero_right

end DivisionMonoid

#print SubtractionCommMonoid /-
/-- Commutative `subtraction_monoid`. -/
@[protect_proj]
class SubtractionCommMonoid (G : Type u) extends SubtractionMonoid G, AddCommMonoid G
#align subtraction_comm_monoid SubtractionCommMonoid
-/

#print DivisionCommMonoid /-
/-- Commutative `division_monoid`.

This is the immediate common ancestor of `comm_group` and `comm_group_with_zero`. -/
@[protect_proj, to_additive SubtractionCommMonoid]
class DivisionCommMonoid (G : Type u) extends DivisionMonoid G, CommMonoid G
#align division_comm_monoid DivisionCommMonoid
#align subtraction_comm_monoid SubtractionCommMonoid
-/

#print Group /-
/-- A `group` is a `monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.
-/
@[protect_proj]
class Group (G : Type u) extends DivInvMonoid G where
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1
#align group Group
-/

#print AddGroup /-
/-- An `add_group` is an `add_monoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.
-/
@[protect_proj]
class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg : ∀ a : A, -a + a = 0
#align add_group AddGroup
-/

attribute [to_additive] Group

/-- Abbreviation for `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.

Useful because it corresponds to the fact that `Grp` is a subcategory of `Mon`.
Not an instance since it duplicates `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "Abbreviation for `@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`.\n\nUseful because it corresponds to the fact that `AddGroup` is a subcategory of `AddMon`.\nNot an instance since it duplicates\n`@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`."]
def Group.toMonoid (G : Type u) [Group G] : Monoid G :=
  @DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _ _)
#align group.to_monoid Group.toMonoid
#align add_group.to_add_monoid AddGroup.toAddMonoid

section Group

variable [Group G] {a b c : G}

/- warning: mul_left_inv -> mul_left_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) a) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) a) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))
Case conversion may be inaccurate. Consider using '#align mul_left_inv mul_left_invₓ'. -/
@[simp, to_additive]
theorem mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
  Group.mul_left_inv
#align mul_left_inv mul_left_inv
#align add_left_neg add_left_neg

/- warning: inv_mul_self -> inv_mul_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) a) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) a) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))
Case conversion may be inaccurate. Consider using '#align inv_mul_self inv_mul_selfₓ'. -/
@[to_additive]
theorem inv_mul_self (a : G) : a⁻¹ * a = 1 :=
  mul_left_inv a
#align inv_mul_self inv_mul_self
#align neg_add_self neg_add_self

@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_self a) h
#align inv_eq_of_mul inv_eq_of_mul

/- warning: mul_right_inv -> mul_right_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a)) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a)) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))
Case conversion may be inaccurate. Consider using '#align mul_right_inv mul_right_invₓ'. -/
@[simp, to_additive]
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  rw [← mul_left_inv a⁻¹, inv_eq_of_mul (mul_left_inv a)]
#align mul_right_inv mul_right_inv
#align add_right_neg add_right_neg

/- warning: mul_inv_self -> mul_inv_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a)) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a)) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))
Case conversion may be inaccurate. Consider using '#align mul_inv_self mul_inv_selfₓ'. -/
@[to_additive]
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 :=
  mul_right_inv a
#align mul_inv_self mul_inv_self
#align add_neg_self add_neg_self

/- warning: inv_mul_cancel_left -> inv_mul_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b)) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b)) b
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel_left inv_mul_cancel_leftₓ'. -/
@[simp, to_additive]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, mul_left_inv, one_mul]
#align inv_mul_cancel_left inv_mul_cancel_left
#align neg_add_cancel_left neg_add_cancel_left

/- warning: mul_inv_cancel_left -> mul_inv_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b)) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b)) b
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel_left mul_inv_cancel_leftₓ'. -/
@[simp, to_additive]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_right_inv, one_mul]
#align mul_inv_cancel_left mul_inv_cancel_left
#align add_neg_cancel_left add_neg_cancel_left

/- warning: mul_inv_cancel_right -> mul_inv_cancel_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) a
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) a
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel_right mul_inv_cancel_rightₓ'. -/
@[simp, to_additive]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_right_inv, mul_one]
#align mul_inv_cancel_right mul_inv_cancel_right
#align add_neg_cancel_right add_neg_cancel_right

/- warning: inv_mul_cancel_right -> inv_mul_cancel_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) b) a
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) b) a
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel_right inv_mul_cancel_rightₓ'. -/
@[simp, to_additive]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by rw [mul_assoc, mul_left_inv, mul_one]
#align inv_mul_cancel_right inv_mul_cancel_right
#align neg_add_cancel_right neg_add_cancel_right

#print Group.toDivisionMonoid /-
@[to_additive AddGroup.toSubtractionMonoid]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G :=
  { ‹Group G› with
    inv_inv := fun a => inv_eq_of_mul (mul_left_inv a)
    mul_inv_rev := fun a b => inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_right_inv]
    inv_eq_of_mul := fun _ _ => inv_eq_of_mul }
#align group.to_division_monoid Group.toDivisionMonoid
#align add_group.to_subtraction_monoid AddGroup.toSubtractionMonoid
-/

#print Group.toCancelMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G :=
  {
    ‹Group
        G› with
    mul_right_cancel := fun a b c h => by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]
    mul_left_cancel := fun a b c h => by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left] }
#align group.to_cancel_monoid Group.toCancelMonoid
-/

end Group

#print Group.toDivInvMonoid_injective /-
@[to_additive]
theorem Group.toDivInvMonoid_injective {G : Type _} :
    Function.Injective (@Group.toDivInvMonoid G) :=
  by
  rintro ⟨⟩ ⟨⟩ ⟨⟩
  rfl
#align group.to_div_inv_monoid_injective Group.toDivInvMonoid_injective
#align add_group.to_sub_neg_add_monoid_injective AddGroup.toSubNegAddMonoid_injective
-/

#print CommGroup /-
/-- A commutative group is a group with commutative `(*)`. -/
@[protect_proj]
class CommGroup (G : Type u) extends Group G, CommMonoid G
#align comm_group CommGroup
-/

#print AddCommGroup /-
/-- An additive commutative group is an additive group with commutative `(+)`. -/
@[protect_proj]
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G
#align add_comm_group AddCommGroup
-/

attribute [to_additive] CommGroup

attribute [instance] AddCommGroup.toAddCommMonoid

#print CommGroup.toGroup_injective /-
@[to_additive]
theorem CommGroup.toGroup_injective {G : Type u} : Function.Injective (@CommGroup.toGroup G) :=
  by
  rintro ⟨⟩ ⟨⟩ ⟨⟩
  rfl
#align comm_group.to_group_injective CommGroup.toGroup_injective
#align add_comm_group.to_add_group_injective AddCommGroup.toAddGroup_injective
-/

section CommGroup

variable [CommGroup G]

#print CommGroup.toCancelCommMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toCancelCommMonoid : CancelCommMonoid G :=
  { ‹CommGroup G›, Group.toCancelMonoid with }
#align comm_group.to_cancel_comm_monoid CommGroup.toCancelCommMonoid
-/

#print CommGroup.toDivisionCommMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toDivisionCommMonoid : DivisionCommMonoid G :=
  { ‹CommGroup G›, Group.toDivisionMonoid with }
#align comm_group.to_division_comm_monoid CommGroup.toDivisionCommMonoid
#align add_comm_group.to_division_add_comm_monoid AddCommGroup.toDivisionAddCommMonoid
-/

end CommGroup

