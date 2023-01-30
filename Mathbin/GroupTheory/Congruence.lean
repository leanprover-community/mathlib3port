/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston

! This file was ported from Lean 3 source module group_theory.congruence
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Data.Setoid.Basic
import Mathbin.GroupTheory.Submonoid.Operations

/-!
# Congruence relations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines congruence relations: equivalence relations that preserve a binary operation,
which in this case is multiplication or addition. The principal definition is a `structure`
extending a `setoid` (an equivalence relation), and the inductive definition of the smallest
congruence relation containing a binary relation is also given (see `con_gen`).

The file also proves basic properties of the quotient of a type by a congruence relation, and the
complete lattice of congruence relations on a type. We then establish an order-preserving bijection
between the set of congruence relations containing a congruence relation `c` and the set of
congruence relations on the quotient by `c`.

The second half of the file concerns congruence relations on monoids, in which case the
quotient by the congruence relation is also a monoid. There are results about the universal
property of quotients of monoids, and the isomorphism theorems for monoids.

## Implementation notes

The inductive definition of a congruence relation could be a nested inductive type, defined using
the equivalence closure of a binary relation `eqv_gen`, but the recursor generated does not work.
A nested inductive definition could conceivably shorten proofs, because they would allow invocation
of the corresponding lemmas about `eqv_gen`.

The lemmas `refl`, `symm` and `trans` are not tagged with `@[refl]`, `@[symm]`, and `@[trans]`
respectively as these tags do not work on a structure coerced to a binary relation.

There is a coercion from elements of a type to the element's equivalence class under a
congruence relation.

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid, isomorphism theorems
-/


variable (M : Type _) {N : Type _} {P : Type _}

open Function Setoid

#print AddCon /-
/-- A congruence relation on a type with an addition is an equivalence relation which
    preserves addition. -/
structure AddCon [Add M] extends Setoid M where
  add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z)
#align add_con AddCon
-/

#print Con /-
/-- A congruence relation on a type with a multiplication is an equivalence relation which
    preserves multiplication. -/
@[to_additive AddCon]
structure Con [Mul M] extends Setoid M where
  mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z)
#align con Con
#align add_con AddCon
-/

/-- The equivalence relation underlying an additive congruence relation. -/
add_decl_doc AddCon.toSetoid

/-- The equivalence relation underlying a multiplicative congruence relation. -/
add_decl_doc Con.toSetoid

variable {M}

#print AddConGen.Rel /-
/-- The inductively defined smallest additive congruence relation containing a given binary
    relation. -/
inductive AddConGen.Rel [Add M] (r : M → M → Prop) : M → M → Prop
  | of : ∀ x y, r x y → AddConGen.Rel x y
  | refl : ∀ x, AddConGen.Rel x x
  | symm : ∀ x y, AddConGen.Rel x y → AddConGen.Rel y x
  | trans : ∀ x y z, AddConGen.Rel x y → AddConGen.Rel y z → AddConGen.Rel x z
  | add : ∀ w x y z, AddConGen.Rel w x → AddConGen.Rel y z → AddConGen.Rel (w + y) (x + z)
#align add_con_gen.rel AddConGen.Rel
-/

#print ConGen.Rel /-
/-- The inductively defined smallest multiplicative congruence relation containing a given binary
    relation. -/
@[to_additive AddConGen.Rel]
inductive ConGen.Rel [Mul M] (r : M → M → Prop) : M → M → Prop
  | of : ∀ x y, r x y → ConGen.Rel x y
  | refl : ∀ x, ConGen.Rel x x
  | symm : ∀ x y, ConGen.Rel x y → ConGen.Rel y x
  | trans : ∀ x y z, ConGen.Rel x y → ConGen.Rel y z → ConGen.Rel x z
  | mul : ∀ w x y z, ConGen.Rel w x → ConGen.Rel y z → ConGen.Rel (w * y) (x * z)
#align con_gen.rel ConGen.Rel
#align add_con_gen.rel AddConGen.Rel
-/

#print conGen /-
/-- The inductively defined smallest multiplicative congruence relation containing a given binary
    relation. -/
@[to_additive addConGen
      "The inductively defined smallest additive congruence relation containing\na given binary relation."]
def conGen [Mul M] (r : M → M → Prop) : Con M :=
  ⟨⟨ConGen.Rel r, ⟨ConGen.Rel.refl, ConGen.Rel.symm, ConGen.Rel.trans⟩⟩, ConGen.Rel.mul⟩
#align con_gen conGen
#align add_con_gen addConGen
-/

namespace Con

section

variable [Mul M] [Mul N] [Mul P] (c : Con M)

@[to_additive]
instance : Inhabited (Con M) :=
  ⟨conGen EmptyRelation⟩

/-- A coercion from a congruence relation to its underlying binary relation. -/
@[to_additive "A coercion from an additive congruence relation to its underlying binary relation."]
instance : CoeFun (Con M) fun _ => M → M → Prop :=
  ⟨fun c => fun x y => @Setoid.r _ c.toSetoid x y⟩

#print Con.rel_eq_coe /-
@[simp, to_additive]
theorem rel_eq_coe (c : Con M) : c.R = c :=
  rfl
#align con.rel_eq_coe Con.rel_eq_coe
#align add_con.rel_eq_coe AddCon.rel_eq_coe
-/

#print Con.refl /-
/-- Congruence relations are reflexive. -/
@[to_additive "Additive congruence relations are reflexive."]
protected theorem refl (x) : c x x :=
  c.toSetoid.refl' x
#align con.refl Con.refl
#align add_con.refl AddCon.refl
-/

#print Con.symm /-
/-- Congruence relations are symmetric. -/
@[to_additive "Additive congruence relations are symmetric."]
protected theorem symm : ∀ {x y}, c x y → c y x := fun _ _ h => c.toSetoid.symm' h
#align con.symm Con.symm
#align add_con.symm AddCon.symm
-/

#print Con.trans /-
/-- Congruence relations are transitive. -/
@[to_additive "Additive congruence relations are transitive."]
protected theorem trans : ∀ {x y z}, c x y → c y z → c x z := fun _ _ _ h => c.toSetoid.trans' h
#align con.trans Con.trans
#align add_con.trans AddCon.trans
-/

#print Con.mul /-
/-- Multiplicative congruence relations preserve multiplication. -/
@[to_additive "Additive congruence relations preserve addition."]
protected theorem mul : ∀ {w x y z}, c w x → c y z → c (w * y) (x * z) := fun _ _ _ _ h1 h2 =>
  c.mul' h1 h2
#align con.mul Con.mul
#align add_con.add AddCon.add
-/

#print Con.rel_mk /-
@[simp, to_additive]
theorem rel_mk {s : Setoid M} {h a b} : Con.mk s h a b ↔ r a b :=
  Iff.rfl
#align con.rel_mk Con.rel_mk
#align add_con.rel_mk AddCon.rel_mk
-/

/-- Given a type `M` with a multiplication, a congruence relation `c` on `M`, and elements of `M`
    `x, y`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`. -/
@[to_additive
      "Given a type `M` with an addition, `x, y ∈ M`, and an additive congruence relation\n`c` on `M`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`."]
instance : Membership (M × M) (Con M) :=
  ⟨fun x c => c x.1 x.2⟩

variable {c}

#print Con.ext' /-
/-- The map sending a congruence relation to its underlying binary relation is injective. -/
@[to_additive
      "The map sending an additive congruence relation to its underlying binary relation\nis injective."]
theorem ext' {c d : Con M} (H : c.R = d.R) : c = d :=
  by
  rcases c with ⟨⟨⟩⟩
  rcases d with ⟨⟨⟩⟩
  cases H
  congr
#align con.ext' Con.ext'
#align add_con.ext' AddCon.ext'
-/

#print Con.ext /-
/-- Extensionality rule for congruence relations. -/
@[ext, to_additive "Extensionality rule for additive congruence relations."]
theorem ext {c d : Con M} (H : ∀ x y, c x y ↔ d x y) : c = d :=
  ext' <| by ext <;> apply H
#align con.ext Con.ext
#align add_con.ext AddCon.ext
-/

#print Con.toSetoid_inj /-
/-- The map sending a congruence relation to its underlying equivalence relation is injective. -/
@[to_additive
      "The map sending an additive congruence relation to its underlying equivalence\nrelation is injective."]
theorem toSetoid_inj {c d : Con M} (H : c.toSetoid = d.toSetoid) : c = d :=
  ext <| ext_iff.1 H
#align con.to_setoid_inj Con.toSetoid_inj
#align add_con.to_setoid_inj AddCon.toSetoid_inj
-/

#print Con.ext_iff /-
/-- Iff version of extensionality rule for congruence relations. -/
@[to_additive "Iff version of extensionality rule for additive congruence relations."]
theorem ext_iff {c d : Con M} : (∀ x y, c x y ↔ d x y) ↔ c = d :=
  ⟨ext, fun h _ _ => h ▸ Iff.rfl⟩
#align con.ext_iff Con.ext_iff
#align add_con.ext_iff AddCon.ext_iff
-/

#print Con.ext'_iff /-
/-- Two congruence relations are equal iff their underlying binary relations are equal. -/
@[to_additive
      "Two additive congruence relations are equal iff their underlying binary relations\nare equal."]
theorem ext'_iff {c d : Con M} : c.R = d.R ↔ c = d :=
  ⟨ext', fun h => h ▸ rfl⟩
#align con.ext'_iff Con.ext'_iff
#align add_con.ext'_iff AddCon.ext'_iff
-/

#print Con.mulKer /-
/-- The kernel of a multiplication-preserving function as a congruence relation. -/
@[to_additive "The kernel of an addition-preserving function as an additive congruence relation."]
def mulKer (f : M → P) (h : ∀ x y, f (x * y) = f x * f y) : Con M
    where
  toSetoid := Setoid.ker f
  mul' _ _ _ _ h1 h2 := by
    dsimp [Setoid.ker, on_fun] at *
    rw [h, h1, h2, h]
#align con.mul_ker Con.mulKer
#align add_con.add_ker AddCon.addKer
-/

#print Con.prod /-
/-- Given types with multiplications `M, N`, the product of two congruence relations `c` on `M` and
    `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁` is related to `y₁`
    by `c` and `x₂` is related to `y₂` by `d`. -/
@[to_additive Prod
      "Given types with additions `M, N`, the product of two congruence relations\n`c` on `M` and `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁`\nis related to `y₁` by `c` and `x₂` is related to `y₂` by `d`."]
protected def prod (c : Con M) (d : Con N) : Con (M × N) :=
  { c.toSetoid.Prod d.toSetoid with
    mul' := fun _ _ _ _ h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }
#align con.prod Con.prod
#align add_con.prod AddCon.prod
-/

#print Con.pi /-
/-- The product of an indexed collection of congruence relations. -/
@[to_additive "The product of an indexed collection of additive congruence relations."]
def pi {ι : Type _} {f : ι → Type _} [∀ i, Mul (f i)] (C : ∀ i, Con (f i)) : Con (∀ i, f i) :=
  { @piSetoid _ _ fun i => (C i).toSetoid with
    mul' := fun _ _ _ _ h1 h2 i => (C i).mul (h1 i) (h2 i) }
#align con.pi Con.pi
#align add_con.pi AddCon.pi
-/

variable (c)

#print Con.Quotient /-
-- Quotients
/-- Defining the quotient by a congruence relation of a type with a multiplication. -/
@[to_additive
      "Defining the quotient by an additive congruence relation of a type with\nan addition."]
protected def Quotient :=
  Quotient <| c.toSetoid
#align con.quotient Con.Quotient
#align add_con.quotient AddCon.Quotient
-/

/-- Coercion from a type with a multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
@[to_additive
      "Coercion from a type with an addition to its quotient by an additive congruence\nrelation"]
instance (priority := 0) : CoeTC M c.Quotient :=
  ⟨@Quotient.mk' _ c.toSetoid⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
@[to_additive "The quotient by a decidable additive congruence relation has decidable equality."]
instance (priority := 500) [d : ∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  @Quotient.decidableEq M c.toSetoid d

#print Con.quot_mk_eq_coe /-
@[simp, to_additive]
theorem quot_mk_eq_coe {M : Type _} [Mul M] (c : Con M) (x : M) : Quot.mk c x = (x : c.Quotient) :=
  rfl
#align con.quot_mk_eq_coe Con.quot_mk_eq_coe
#align add_con.quot_mk_eq_coe AddCon.quot_mk_eq_coe
-/

#print Con.liftOn /-
/-- The function on the quotient by a congruence relation `c` induced by a function that is
    constant on `c`'s equivalence classes. -/
@[elab_as_elim,
  to_additive
      "The function on the quotient by a congruence relation `c`\ninduced by a function that is constant on `c`'s equivalence classes."]
protected def liftOn {β} {c : Con M} (q : c.Quotient) (f : M → β) (h : ∀ a b, c a b → f a = f b) :
    β :=
  Quotient.liftOn' q f h
#align con.lift_on Con.liftOn
#align add_con.lift_on AddCon.liftOn
-/

#print Con.liftOn₂ /-
/-- The binary function on the quotient by a congruence relation `c` induced by a binary function
    that is constant on `c`'s equivalence classes. -/
@[elab_as_elim,
  to_additive
      "The binary function on the quotient by a congruence relation `c`\ninduced by a binary function that is constant on `c`'s equivalence classes."]
protected def liftOn₂ {β} {c : Con M} (q r : c.Quotient) (f : M → M → β)
    (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → c a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β :=
  Quotient.liftOn₂' q r f h
#align con.lift_on₂ Con.liftOn₂
#align add_con.lift_on₂ AddCon.liftOn₂
-/

#print Con.hrecOn₂ /-
/-- A version of `quotient.hrec_on₂'` for quotients by `con`. -/
@[to_additive "A version of `quotient.hrec_on₂'` for quotients by `add_con`."]
protected def hrecOn₂ {cM : Con M} {cN : Con N} {φ : cM.Quotient → cN.Quotient → Sort _}
    (a : cM.Quotient) (b : cN.Quotient) (f : ∀ (x : M) (y : N), φ x y)
    (h : ∀ x y x' y', cM x x' → cN y y' → HEq (f x y) (f x' y')) : φ a b :=
  Quotient.hrecOn₂' a b f h
#align con.hrec_on₂ Con.hrecOn₂
#align add_con.hrec_on₂ AddCon.hrecOn₂
-/

/- warning: con.hrec_on₂_coe -> Con.hrec_on₂_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {cM : Con.{u1} M _inst_1} {cN : Con.{u2} N _inst_2} {φ : (Con.Quotient.{u1} M _inst_1 cM) -> (Con.Quotient.{u2} N _inst_2 cN) -> Sort.{u3}} (a : M) (b : N) (f : forall (x : M) (y : N), φ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M _inst_1 cM) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (Con.Quotient.hasCoeT.{u1} M _inst_1 cM))) x) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) N (Con.Quotient.{u2} N _inst_2 cN) (HasLiftT.mk.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (CoeTCₓ.coe.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (Con.Quotient.hasCoeT.{u2} N _inst_2 cN))) y)) (h : forall (x : M) (y : N) (x' : M) (y' : N), (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (_x : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1) cM x x') -> (coeFn.{succ u2, succ u2} (Con.{u2} N _inst_2) (fun (_x : Con.{u2} N _inst_2) => N -> N -> Prop) (Con.hasCoeToFun.{u2} N _inst_2) cN y y') -> (HEq.{u3} (φ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M _inst_1 cM) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (Con.Quotient.hasCoeT.{u1} M _inst_1 cM))) x) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) N (Con.Quotient.{u2} N _inst_2 cN) (HasLiftT.mk.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (CoeTCₓ.coe.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (Con.Quotient.hasCoeT.{u2} N _inst_2 cN))) y)) (f x y) (φ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M _inst_1 cM) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (Con.Quotient.hasCoeT.{u1} M _inst_1 cM))) x') ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) N (Con.Quotient.{u2} N _inst_2 cN) (HasLiftT.mk.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (CoeTCₓ.coe.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (Con.Quotient.hasCoeT.{u2} N _inst_2 cN))) y')) (f x' y'))), Eq.{u3} (φ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M _inst_1 cM) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (Con.Quotient.hasCoeT.{u1} M _inst_1 cM))) a) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) N (Con.Quotient.{u2} N _inst_2 cN) (HasLiftT.mk.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (CoeTCₓ.coe.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (Con.Quotient.hasCoeT.{u2} N _inst_2 cN))) b)) (Con.hrecOn₂.{u1, u2, u3} M N _inst_1 _inst_2 cM cN φ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M _inst_1 cM) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M _inst_1 cM) (Con.Quotient.hasCoeT.{u1} M _inst_1 cM))) a) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) N (Con.Quotient.{u2} N _inst_2 cN) (HasLiftT.mk.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (CoeTCₓ.coe.{succ u2, succ u2} N (Con.Quotient.{u2} N _inst_2 cN) (Con.Quotient.hasCoeT.{u2} N _inst_2 cN))) b) f h) (f a b)
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] {cM : Con.{u3} M _inst_1} {cN : Con.{u2} N _inst_2} {φ : (Con.Quotient.{u3} M _inst_1 cM) -> (Con.Quotient.{u2} N _inst_2 cN) -> Sort.{u1}} (a : M) (b : N) (f : forall (x : M) (y : N), φ (Con.toQuotient.{u3} M _inst_1 cM x) (Con.toQuotient.{u2} N _inst_2 cN y)) (h : forall (x : M) (y : N) (x' : M) (y' : N), (FunLike.coe.{succ u3, succ u3, succ u3} (Con.{u3} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u3} M _inst_1) cM x x') -> (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} N _inst_2) N (fun (_x : N) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : N) => N -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} N _inst_2) cN y y') -> (HEq.{u1} (φ (Con.toQuotient.{u3} M _inst_1 cM x) (Con.toQuotient.{u2} N _inst_2 cN y)) (f x y) (φ (Con.toQuotient.{u3} M _inst_1 cM x') (Con.toQuotient.{u2} N _inst_2 cN y')) (f x' y'))), Eq.{u1} (φ (Con.toQuotient.{u3} M _inst_1 cM a) (Con.toQuotient.{u2} N _inst_2 cN b)) (Con.hrecOn₂.{u3, u2, u1} M N _inst_1 _inst_2 cM cN φ (Con.toQuotient.{u3} M _inst_1 cM a) (Con.toQuotient.{u2} N _inst_2 cN b) f h) (f a b)
Case conversion may be inaccurate. Consider using '#align con.hrec_on₂_coe Con.hrec_on₂_coeₓ'. -/
@[simp, to_additive]
theorem hrec_on₂_coe {cM : Con M} {cN : Con N} {φ : cM.Quotient → cN.Quotient → Sort _} (a : M)
    (b : N) (f : ∀ (x : M) (y : N), φ x y)
    (h : ∀ x y x' y', cM x x' → cN y y' → HEq (f x y) (f x' y')) :
    Con.hrecOn₂ (↑a) (↑b) f h = f a b :=
  rfl
#align con.hrec_on₂_coe Con.hrec_on₂_coe
#align add_con.hrec_on₂_coe AddCon.hrec_on₂_coe

variable {c}

#print Con.induction_on /-
/-- The inductive principle used to prove propositions about the elements of a quotient by a
    congruence relation. -/
@[elab_as_elim,
  to_additive
      "The inductive principle used to prove propositions about\nthe elements of a quotient by an additive congruence relation."]
protected theorem induction_on {C : c.Quotient → Prop} (q : c.Quotient) (H : ∀ x : M, C x) : C q :=
  Quotient.inductionOn' q H
#align con.induction_on Con.induction_on
#align add_con.induction_on AddCon.induction_on
-/

#print Con.induction_on₂ /-
/-- A version of `con.induction_on` for predicates which take two arguments. -/
@[elab_as_elim,
  to_additive "A version of `add_con.induction_on` for predicates which take\ntwo arguments."]
protected theorem induction_on₂ {d : Con N} {C : c.Quotient → d.Quotient → Prop} (p : c.Quotient)
    (q : d.Quotient) (H : ∀ (x : M) (y : N), C x y) : C p q :=
  Quotient.inductionOn₂' p q H
#align con.induction_on₂ Con.induction_on₂
#align add_con.induction_on₂ AddCon.induction_on₂
-/

variable (c)

#print Con.eq /-
/-- Two elements are related by a congruence relation `c` iff they are represented by the same
    element of the quotient by `c`. -/
@[simp,
  to_additive
      "Two elements are related by an additive congruence relation `c` iff they\nare represented by the same element of the quotient by `c`."]
protected theorem eq {a b : M} : (a : c.Quotient) = b ↔ c a b :=
  Quotient.eq''
#align con.eq Con.eq
#align add_con.eq AddCon.eq
-/

#print Con.hasMul /-
/-- The multiplication induced on the quotient by a congruence relation on a type with a
    multiplication. -/
@[to_additive
      "The addition induced on the quotient by an additive congruence relation on a type\nwith an addition."]
instance hasMul : Mul c.Quotient :=
  ⟨Quotient.map₂' (· * ·) fun _ _ h1 _ _ h2 => c.mul h1 h2⟩
#align con.has_mul Con.hasMul
#align add_con.has_add AddCon.hasAdd
-/

#print Con.mul_ker_mk_eq /-
/-- The kernel of the quotient map induced by a congruence relation `c` equals `c`. -/
@[simp,
  to_additive
      "The kernel of the quotient map induced by an additive congruence relation\n`c` equals `c`."]
theorem mul_ker_mk_eq : (mulKer (coe : M → c.Quotient) fun x y => rfl) = c :=
  ext fun x y => Quotient.eq''
#align con.mul_ker_mk_eq Con.mul_ker_mk_eq
#align add_con.add_ker_mk_eq AddCon.add_ker_mk_eq
-/

variable {c}

#print Con.coe_mul /-
/-- The coercion to the quotient of a congruence relation commutes with multiplication (by
    definition). -/
@[simp,
  to_additive
      "The coercion to the quotient of an additive congruence relation commutes with\naddition (by definition)."]
theorem coe_mul (x y : M) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl
#align con.coe_mul Con.coe_mul
#align add_con.coe_add AddCon.coe_add
-/

#print Con.liftOn_coe /-
/-- Definition of the function on the quotient by a congruence relation `c` induced by a function
    that is constant on `c`'s equivalence classes. -/
@[simp,
  to_additive
      "Definition of the function on the quotient by an additive congruence\nrelation `c` induced by a function that is constant on `c`'s equivalence classes."]
protected theorem liftOn_coe {β} (c : Con M) (f : M → β) (h : ∀ a b, c a b → f a = f b) (x : M) :
    Con.liftOn (x : c.Quotient) f h = f x :=
  rfl
#align con.lift_on_coe Con.liftOn_coe
#align add_con.lift_on_coe AddCon.liftOn_coe
-/

#print Con.congr /-
/-- Makes an isomorphism of quotients by two congruence relations, given that the relations are
    equal. -/
@[to_additive
      "Makes an additive isomorphism of quotients by two additive congruence relations,\ngiven that the relations are equal."]
protected def congr {c d : Con M} (h : c = d) : c.Quotient ≃* d.Quotient :=
  { Quotient.congr (Equiv.refl M) <| by apply ext_iff.2 h with
    map_mul' := fun x y => by rcases x with ⟨⟩ <;> rcases y with ⟨⟩ <;> rfl }
#align con.congr Con.congr
#align add_con.congr AddCon.congr
-/

-- The complete lattice of congruence relations on a type
/-- For congruence relations `c, d` on a type `M` with a multiplication, `c ≤ d` iff `∀ x y ∈ M`,
    `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
@[to_additive
      "For additive congruence relations `c, d` on a type `M` with an addition, `c ≤ d` iff\n`∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`."]
instance : LE (Con M) :=
  ⟨fun c d => ∀ ⦃x y⦄, c x y → d x y⟩

#print Con.le_def /-
/-- Definition of `≤` for congruence relations. -/
@[to_additive "Definition of `≤` for additive congruence relations."]
theorem le_def {c d : Con M} : c ≤ d ↔ ∀ {x y}, c x y → d x y :=
  Iff.rfl
#align con.le_def Con.le_def
#align add_con.le_def AddCon.le_def
-/

/-- The infimum of a set of congruence relations on a given type with a multiplication. -/
@[to_additive
      "The infimum of a set of additive congruence relations on a given type with\nan addition."]
instance : InfSet (Con M) :=
  ⟨fun S =>
    ⟨⟨fun x y => ∀ c : Con M, c ∈ S → c x y,
        ⟨fun x c hc => c.refl x, fun _ _ h c hc => c.symm <| h c hc, fun _ _ _ h1 h2 c hc =>
          c.trans (h1 c hc) <| h2 c hc⟩⟩,
      fun _ _ _ _ h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc⟩⟩

/- warning: con.Inf_to_setoid -> Con.infₛ_toSetoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Con.{u1} M _inst_1)), Eq.{succ u1} (Setoid.{succ u1} M) (Con.toSetoid.{u1} M _inst_1 (InfSet.infₛ.{u1} (Con.{u1} M _inst_1) (Con.hasInf.{u1} M _inst_1) S)) (InfSet.infₛ.{u1} (Setoid.{succ u1} M) (Setoid.hasInf.{u1} M) (Set.image.{u1, u1} (Con.{u1} M _inst_1) (Setoid.{succ u1} M) (Con.toSetoid.{u1} M _inst_1) S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Con.{u1} M _inst_1)), Eq.{succ u1} (Setoid.{succ u1} M) (Con.toSetoid.{u1} M _inst_1 (InfSet.infₛ.{u1} (Con.{u1} M _inst_1) (Con.instInfSetCon.{u1} M _inst_1) S)) (InfSet.infₛ.{u1} (Setoid.{succ u1} M) (Setoid.instInfSetSetoid.{u1} M) (Set.image.{u1, u1} (Con.{u1} M _inst_1) (Setoid.{succ u1} M) (Con.toSetoid.{u1} M _inst_1) S))
Case conversion may be inaccurate. Consider using '#align con.Inf_to_setoid Con.infₛ_toSetoidₓ'. -/
/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
@[to_additive
      "The infimum of a set of additive congruence relations is the same as the infimum of\nthe set's image under the map to the underlying equivalence relation."]
theorem infₛ_toSetoid (S : Set (Con M)) : (infₛ S).toSetoid = infₛ (to_setoid '' S) :=
  Setoid.ext' fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr] <;> exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩
#align con.Inf_to_setoid Con.infₛ_toSetoid
#align add_con.Inf_to_setoid AddCon.infₛ_toSetoid

/- warning: con.Inf_def -> Con.infₛ_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Con.{u1} M _inst_1)), Eq.{succ u1} (M -> M -> Prop) (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (_x : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1) (InfSet.infₛ.{u1} (Con.{u1} M _inst_1) (Con.hasInf.{u1} M _inst_1) S)) (InfSet.infₛ.{u1} (M -> M -> Prop) (Pi.infSet.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.infSet.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => CompleteSemilatticeInf.toHasInf.{0} Prop (CompleteLattice.toCompleteSemilatticeInf.{0} Prop Prop.completeLattice)))) (Set.image.{u1, u1} (Con.{u1} M _inst_1) (M -> M -> Prop) (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (ᾰ : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1)) S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Con.{u1} M _inst_1)), Eq.{succ u1} (forall (ᾰ : M), (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M _inst_1) (InfSet.infₛ.{u1} (Con.{u1} M _inst_1) (Con.instInfSetCon.{u1} M _inst_1) S)) (InfSet.infₛ.{u1} (M -> M -> Prop) (Pi.infSet.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.infSet.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => CompleteBooleanAlgebra.toInfSet.{0} Prop Prop.completeBooleanAlgebra))) (Set.image.{u1, u1} (Con.{u1} M _inst_1) (M -> M -> Prop) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (ᾰ : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) ᾰ) (Con.instFunLikeConForAllProp.{u1} M _inst_1)) S))
Case conversion may be inaccurate. Consider using '#align con.Inf_def Con.infₛ_defₓ'. -/
/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying binary relation. -/
@[to_additive
      "The infimum of a set of additive congruence relations is the same as the infimum\nof the set's image under the map to the underlying binary relation."]
theorem infₛ_def (S : Set (Con M)) : ⇑(infₛ S) = infₛ (@Set.image (Con M) (M → M → Prop) coeFn S) :=
  by
  ext
  simp only [infₛ_image, infᵢ_apply, infᵢ_Prop_eq]
  rfl
#align con.Inf_def Con.infₛ_def
#align add_con.Inf_def AddCon.infₛ_def

@[to_additive]
instance : PartialOrder (Con M) where
  le := (· ≤ ·)
  lt c d := c ≤ d ∧ ¬d ≤ c
  le_refl c _ _ := id
  le_trans c1 c2 c3 h1 h2 x y h := h2 <| h1 h
  lt_iff_le_not_le _ _ := Iff.rfl
  le_antisymm c d hc hd := ext fun x y => ⟨fun h => hc h, fun h => hd h⟩

/-- The complete lattice of congruence relations on a given type with a multiplication. -/
@[to_additive
      "The complete lattice of additive congruence relations on a given type with\nan addition."]
instance : CompleteLattice (Con M) :=
  {
    completeLatticeOfInf (Con M) fun s =>
      ⟨fun r hr x y h => (h : ∀ r ∈ s, (r : Con M) x y) r hr, fun r hr x y h r' hr' =>
        hr hr'
          h⟩ with
    inf := fun c d =>
      ⟨c.toSetoid ⊓ d.toSetoid, fun _ _ _ _ h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩⟩
    inf_le_left := fun _ _ _ _ h => h.1
    inf_le_right := fun _ _ _ _ h => h.2
    le_inf := fun _ _ _ hb hc _ _ h => ⟨hb h, hc h⟩
    top := { Setoid.completeLattice.top with mul' := by tauto }
    le_top := fun _ _ _ h => trivial
    bot := { Setoid.completeLattice.bot with mul' := fun _ _ _ _ h1 h2 => h1 ▸ h2 ▸ rfl }
    bot_le := fun c x y h => h ▸ c.refl x }

/- warning: con.inf_def -> Con.inf_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {c : Con.{u1} M _inst_1} {d : Con.{u1} M _inst_1}, Eq.{succ u1} (M -> M -> Prop) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 (HasInf.inf.{u1} (Con.{u1} M _inst_1) (SemilatticeInf.toHasInf.{u1} (Con.{u1} M _inst_1) (Lattice.toSemilatticeInf.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Con.{u1} M _inst_1) (Con.completeLattice.{u1} M _inst_1)))) c d))) (HasInf.inf.{u1} (M -> M -> Prop) (Pi.hasInf.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.hasInf.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => SemilatticeInf.toHasInf.{0} Prop (Lattice.toSemilatticeInf.{0} Prop (CompleteLattice.toLattice.{0} Prop Prop.completeLattice))))) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 c)) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 d)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {c : Con.{u1} M _inst_1} {d : Con.{u1} M _inst_1}, Eq.{succ u1} (M -> M -> Prop) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 (HasInf.inf.{u1} (Con.{u1} M _inst_1) (Lattice.toHasInf.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Con.{u1} M _inst_1) (Con.instCompleteLatticeCon.{u1} M _inst_1))) c d))) (HasInf.inf.{u1} (M -> M -> Prop) (Pi.instHasInfForAll.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.instHasInfForAll.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => Lattice.toHasInf.{0} Prop (CompleteLattice.toLattice.{0} Prop Prop.completeLattice)))) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 c)) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 d)))
Case conversion may be inaccurate. Consider using '#align con.inf_def Con.inf_defₓ'. -/
/-- The infimum of two congruence relations equals the infimum of the underlying binary
    operations. -/
@[to_additive
      "The infimum of two additive congruence relations equals the infimum of the\nunderlying binary operations."]
theorem inf_def {c d : Con M} : (c ⊓ d).R = c.R ⊓ d.R :=
  rfl
#align con.inf_def Con.inf_def
#align add_con.inf_def AddCon.inf_def

/- warning: con.inf_iff_and -> Con.inf_iff_and is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {c : Con.{u1} M _inst_1} {d : Con.{u1} M _inst_1} {x : M} {y : M}, Iff (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (_x : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1) (HasInf.inf.{u1} (Con.{u1} M _inst_1) (SemilatticeInf.toHasInf.{u1} (Con.{u1} M _inst_1) (Lattice.toSemilatticeInf.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Con.{u1} M _inst_1) (Con.completeLattice.{u1} M _inst_1)))) c d) x y) (And (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (_x : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1) c x y) (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (_x : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1) d x y))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {c : Con.{u1} M _inst_1} {d : Con.{u1} M _inst_1} {x : M} {y : M}, Iff (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M _inst_1) (HasInf.inf.{u1} (Con.{u1} M _inst_1) (Lattice.toHasInf.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Con.{u1} M _inst_1) (Con.instCompleteLatticeCon.{u1} M _inst_1))) c d) x y) (And (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M _inst_1) c x y) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M _inst_1) d x y))
Case conversion may be inaccurate. Consider using '#align con.inf_iff_and Con.inf_iff_andₓ'. -/
/-- Definition of the infimum of two congruence relations. -/
@[to_additive "Definition of the infimum of two additive congruence relations."]
theorem inf_iff_and {c d : Con M} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y :=
  Iff.rfl
#align con.inf_iff_and Con.inf_iff_and
#align add_con.inf_iff_and AddCon.inf_iff_and

/- warning: con.con_gen_eq -> Con.conGen_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (r : M -> M -> Prop), Eq.{succ u1} (Con.{u1} M _inst_1) (conGen.{u1} M _inst_1 r) (InfSet.infₛ.{u1} (Con.{u1} M _inst_1) (Con.hasInf.{u1} M _inst_1) (setOf.{u1} (Con.{u1} M _inst_1) (fun (s : Con.{u1} M _inst_1) => forall (x : M) (y : M), (r x y) -> (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (_x : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1) s x y))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (r : M -> M -> Prop), Eq.{succ u1} (Con.{u1} M _inst_1) (conGen.{u1} M _inst_1 r) (InfSet.infₛ.{u1} (Con.{u1} M _inst_1) (Con.instInfSetCon.{u1} M _inst_1) (setOf.{u1} (Con.{u1} M _inst_1) (fun (s : Con.{u1} M _inst_1) => forall (x : M) (y : M), (r x y) -> (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M _inst_1) s x y))))
Case conversion may be inaccurate. Consider using '#align con.con_gen_eq Con.conGen_eqₓ'. -/
/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
    the infimum of the set of congruence relations containing `r`. -/
@[to_additive add_con_gen_eq
      "The inductively defined smallest additive congruence relation\ncontaining a binary relation `r` equals the infimum of the set of additive congruence relations\ncontaining `r`."]
theorem conGen_eq (r : M → M → Prop) : conGen r = infₛ { s : Con M | ∀ x y, r x y → s x y } :=
  le_antisymm
    (fun x y H =>
      ConGen.Rel.rec_on H (fun _ _ h _ hs => hs _ _ h) (Con.refl _) (fun _ _ _ => Con.symm _)
        (fun _ _ _ _ _ => Con.trans _) fun w x y z _ _ h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc)
    (infₛ_le fun _ _ => ConGen.Rel.of _ _)
#align con.con_gen_eq Con.conGen_eq
#align add_con.add_con_gen_eq AddCon.addConGen_eq

#print Con.conGen_le /-
/-- The smallest congruence relation containing a binary relation `r` is contained in any
    congruence relation containing `r`. -/
@[to_additive add_con_gen_le
      "The smallest additive congruence relation containing a binary\nrelation `r` is contained in any additive congruence relation containing `r`."]
theorem conGen_le {r : M → M → Prop} {c : Con M} (h : ∀ x y, r x y → @Setoid.r _ c.toSetoid x y) :
    conGen r ≤ c := by rw [con_gen_eq] <;> exact infₛ_le h
#align con.con_gen_le Con.conGen_le
#align add_con.add_con_gen_le AddCon.addConGen_le
-/

#print Con.conGen_mono /-
/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
    containing `s` contains the smallest congruence relation containing `r`. -/
@[to_additive add_con_gen_mono
      "Given binary relations `r, s` with `r` contained in `s`, the\nsmallest additive congruence relation containing `s` contains the smallest additive congruence\nrelation containing `r`."]
theorem conGen_mono {r s : M → M → Prop} (h : ∀ x y, r x y → s x y) : conGen r ≤ conGen s :=
  con_gen_le fun x y hr => ConGen.Rel.of _ _ <| h x y hr
#align con.con_gen_mono Con.conGen_mono
#align add_con.add_con_gen_mono AddCon.addConGen_mono
-/

#print Con.conGen_of_con /-
/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
@[simp,
  to_additive add_con_gen_of_add_con
      "Additive congruence relations equal the smallest\nadditive congruence relation in which they are contained."]
theorem conGen_of_con (c : Con M) : conGen c = c :=
  le_antisymm (by rw [con_gen_eq] <;> exact infₛ_le fun _ _ => id) ConGen.Rel.of
#align con.con_gen_of_con Con.conGen_of_con
#align add_con.add_con_gen_of_con AddCon.addConGen_of_addCon
-/

#print Con.conGen_idem /-
/-- The map sending a binary relation to the smallest congruence relation in which it is
    contained is idempotent. -/
@[simp,
  to_additive add_con_gen_idem
      "The map sending a binary relation to the smallest additive\ncongruence relation in which it is contained is idempotent."]
theorem conGen_idem (r : M → M → Prop) : conGen (conGen r) = conGen r :=
  conGen_of_con _
#align con.con_gen_idem Con.conGen_idem
#align add_con.add_con_gen_idem AddCon.addConGen_idem
-/

/- warning: con.sup_eq_con_gen -> Con.sup_eq_conGen is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (c : Con.{u1} M _inst_1) (d : Con.{u1} M _inst_1), Eq.{succ u1} (Con.{u1} M _inst_1) (HasSup.sup.{u1} (Con.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Con.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Con.{u1} M _inst_1) (Con.completeLattice.{u1} M _inst_1)))) c d) (conGen.{u1} M _inst_1 (fun (x : M) (y : M) => Or (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (_x : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1) c x y) (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (_x : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1) d x y)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (c : Con.{u1} M _inst_1) (d : Con.{u1} M _inst_1), Eq.{succ u1} (Con.{u1} M _inst_1) (HasSup.sup.{u1} (Con.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Con.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Con.{u1} M _inst_1) (Con.instCompleteLatticeCon.{u1} M _inst_1)))) c d) (conGen.{u1} M _inst_1 (fun (x : M) (y : M) => Or (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M _inst_1) c x y) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M _inst_1) d x y)))
Case conversion may be inaccurate. Consider using '#align con.sup_eq_con_gen Con.sup_eq_conGenₓ'. -/
/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
    the binary relation '`x` is related to `y` by `c` or `d`'. -/
@[to_additive sup_eq_add_con_gen
      "The supremum of additive congruence relations `c, d` equals the\nsmallest additive congruence relation containing the binary relation '`x` is related to `y`\nby `c` or `d`'."]
theorem sup_eq_conGen (c d : Con M) : c ⊔ d = conGen fun x y => c x y ∨ d x y :=
  by
  rw [con_gen_eq]
  apply congr_arg Inf
  simp only [le_def, or_imp, ← forall_and]
#align con.sup_eq_con_gen Con.sup_eq_conGen
#align add_con.sup_eq_add_con_gen AddCon.sup_eq_addConGen

/- warning: con.sup_def -> Con.sup_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {c : Con.{u1} M _inst_1} {d : Con.{u1} M _inst_1}, Eq.{succ u1} (Con.{u1} M _inst_1) (HasSup.sup.{u1} (Con.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Con.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Con.{u1} M _inst_1) (Con.completeLattice.{u1} M _inst_1)))) c d) (conGen.{u1} M _inst_1 (HasSup.sup.{u1} (M -> M -> Prop) (Pi.hasSup.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.hasSup.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => SemilatticeSup.toHasSup.{0} Prop (Lattice.toSemilatticeSup.{0} Prop (CompleteLattice.toLattice.{0} Prop Prop.completeLattice))))) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 c)) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 d))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {c : Con.{u1} M _inst_1} {d : Con.{u1} M _inst_1}, Eq.{succ u1} (Con.{u1} M _inst_1) (HasSup.sup.{u1} (Con.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Con.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Con.{u1} M _inst_1) (Con.instCompleteLatticeCon.{u1} M _inst_1)))) c d) (conGen.{u1} M _inst_1 (HasSup.sup.{u1} (M -> M -> Prop) (Pi.instHasSupForAll.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.instHasSupForAll.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => SemilatticeSup.toHasSup.{0} Prop (Lattice.toSemilatticeSup.{0} Prop (CompleteLattice.toLattice.{0} Prop Prop.completeLattice))))) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 c)) (Setoid.r.{succ u1} M (Con.toSetoid.{u1} M _inst_1 d))))
Case conversion may be inaccurate. Consider using '#align con.sup_def Con.sup_defₓ'. -/
/-- The supremum of two congruence relations equals the smallest congruence relation containing
    the supremum of the underlying binary operations. -/
@[to_additive
      "The supremum of two additive congruence relations equals the smallest additive\ncongruence relation containing the supremum of the underlying binary operations."]
theorem sup_def {c d : Con M} : c ⊔ d = conGen (c.R ⊔ d.R) := by rw [sup_eq_con_gen] <;> rfl
#align con.sup_def Con.sup_def
#align add_con.sup_def AddCon.sup_def

/- warning: con.Sup_eq_con_gen -> Con.supₛ_eq_conGen is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Con.{u1} M _inst_1)), Eq.{succ u1} (Con.{u1} M _inst_1) (SupSet.supₛ.{u1} (Con.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Con.{u1} M _inst_1) (Con.completeLattice.{u1} M _inst_1))) S) (conGen.{u1} M _inst_1 (fun (x : M) (y : M) => Exists.{succ u1} (Con.{u1} M _inst_1) (fun (c : Con.{u1} M _inst_1) => And (Membership.Mem.{u1, u1} (Con.{u1} M _inst_1) (Set.{u1} (Con.{u1} M _inst_1)) (Set.hasMem.{u1} (Con.{u1} M _inst_1)) c S) (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (_x : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1) c x y))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Con.{u1} M _inst_1)), Eq.{succ u1} (Con.{u1} M _inst_1) (SupSet.supₛ.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Con.{u1} M _inst_1) (Con.instCompleteLatticeCon.{u1} M _inst_1)) S) (conGen.{u1} M _inst_1 (fun (x : M) (y : M) => Exists.{succ u1} (Con.{u1} M _inst_1) (fun (c : Con.{u1} M _inst_1) => And (Membership.mem.{u1, u1} (Con.{u1} M _inst_1) (Set.{u1} (Con.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Con.{u1} M _inst_1)) c S) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M _inst_1) c x y))))
Case conversion may be inaccurate. Consider using '#align con.Sup_eq_con_gen Con.supₛ_eq_conGenₓ'. -/
/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
    containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by
    `c`'. -/
@[to_additive Sup_eq_add_con_gen
      "The supremum of a set of additive congruence relations `S` equals\nthe smallest additive congruence relation containing the binary relation 'there exists `c ∈ S`\nsuch that `x` is related to `y` by `c`'."]
theorem supₛ_eq_conGen (S : Set (Con M)) : supₛ S = conGen fun x y => ∃ c : Con M, c ∈ S ∧ c x y :=
  by
  rw [con_gen_eq]
  apply congr_arg Inf
  ext
  exact ⟨fun h _ _ ⟨r, hr⟩ => h hr.1 hr.2, fun h r hS _ _ hr => h _ _ ⟨r, hS, hr⟩⟩
#align con.Sup_eq_con_gen Con.supₛ_eq_conGen
#align add_con.Sup_eq_add_con_gen AddCon.supₛ_eq_addConGen

/- warning: con.Sup_def -> Con.supₛ_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {S : Set.{u1} (Con.{u1} M _inst_1)}, Eq.{succ u1} (Con.{u1} M _inst_1) (SupSet.supₛ.{u1} (Con.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Con.{u1} M _inst_1) (Con.completeLattice.{u1} M _inst_1))) S) (conGen.{u1} M _inst_1 (SupSet.supₛ.{u1} (M -> M -> Prop) (Pi.supSet.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.supSet.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice)))) (Set.image.{u1, u1} (Con.{u1} M _inst_1) (M -> M -> Prop) (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (ᾰ : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1)) S)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {S : Set.{u1} (Con.{u1} M _inst_1)}, Eq.{succ u1} (Con.{u1} M _inst_1) (SupSet.supₛ.{u1} (Con.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Con.{u1} M _inst_1) (Con.instCompleteLatticeCon.{u1} M _inst_1)) S) (conGen.{u1} M _inst_1 (SupSet.supₛ.{u1} (M -> M -> Prop) (Pi.supSet.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.supSet.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => CompleteBooleanAlgebra.toSupSet.{0} Prop Prop.completeBooleanAlgebra))) (Set.image.{u1, u1} (Con.{u1} M _inst_1) (M -> M -> Prop) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (ᾰ : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) ᾰ) (Con.instFunLikeConForAllProp.{u1} M _inst_1)) S)))
Case conversion may be inaccurate. Consider using '#align con.Sup_def Con.supₛ_defₓ'. -/
/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
    containing the supremum of the set's image under the map to the underlying binary relation. -/
@[to_additive
      "The supremum of a set of additive congruence relations is the same as the smallest\nadditive congruence relation containing the supremum of the set's image under the map to the\nunderlying binary relation."]
theorem supₛ_def {S : Set (Con M)} :
    supₛ S = conGen (supₛ (@Set.image (Con M) (M → M → Prop) coeFn S)) :=
  by
  rw [Sup_eq_con_gen, supₛ_image]
  congr with (x y)
  simp only [supₛ_image, supᵢ_apply, supᵢ_Prop_eq, exists_prop, rel_eq_coe]
#align con.Sup_def Con.supₛ_def
#align add_con.Sup_def AddCon.supₛ_def

variable (M)

/- warning: con.gi -> Con.gi is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : Mul.{u1} M], GaloisInsertion.{u1, u1} (M -> M -> Prop) (Con.{u1} M _inst_1) (Pi.preorder.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.preorder.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => PartialOrder.toPreorder.{0} Prop Prop.partialOrder))) (PartialOrder.toPreorder.{u1} (Con.{u1} M _inst_1) (Con.partialOrder.{u1} M _inst_1)) (conGen.{u1} M _inst_1) (coeFn.{succ u1, succ u1} (Con.{u1} M _inst_1) (fun (ᾰ : Con.{u1} M _inst_1) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M _inst_1))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Mul.{u1} M], GaloisInsertion.{u1, u1} (M -> M -> Prop) (Con.{u1} M _inst_1) (Pi.preorder.{u1, u1} M (fun (ᾰ : M) => M -> Prop) (fun (i : M) => Pi.preorder.{u1, 0} M (fun (ᾰ : M) => Prop) (fun (i : M) => PartialOrder.toPreorder.{0} Prop Prop.partialOrder))) (PartialOrder.toPreorder.{u1} (Con.{u1} M _inst_1) (Con.instPartialOrderCon.{u1} M _inst_1)) (conGen.{u1} M _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M _inst_1) M (fun (ᾰ : M) => M -> Prop) (Con.instFunLikeConForAllProp.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align con.gi Con.giₓ'. -/
/-- There is a Galois insertion of congruence relations on a type with a multiplication `M` into
    binary relations on `M`. -/
@[to_additive
      "There is a Galois insertion of additive congruence relations on a type with\nan addition `M` into binary relations on `M`."]
protected def gi : @GaloisInsertion (M → M → Prop) (Con M) _ _ conGen coeFn
    where
  choice r h := conGen r
  gc r c := ⟨fun H _ _ h => H <| ConGen.Rel.of _ _ h, fun H => conGen_of_con c ▸ conGen_mono H⟩
  le_l_u x := (conGen_of_con x).symm ▸ le_refl x
  choice_eq _ _ := rfl
#align con.gi Con.gi
#align add_con.gi AddCon.gi

variable {M} (c)

#print Con.mapGen /-
/-- Given a function `f`, the smallest congruence relation containing the binary relation on `f`'s
    image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)`
    by a congruence relation `c`.' -/
@[to_additive
      "Given a function `f`, the smallest additive congruence relation containing the\nbinary relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the\nelements of `f⁻¹(y)` by an additive congruence relation `c`.'"]
def mapGen (f : M → N) : Con N :=
  conGen fun x y => ∃ a b, f a = x ∧ f b = y ∧ c a b
#align con.map_gen Con.mapGen
#align add_con.map_gen AddCon.mapGen
-/

#print Con.mapOfSurjective /-
/-- Given a surjective multiplicative-preserving function `f` whose kernel is contained in a
    congruence relation `c`, the congruence relation on `f`'s codomain defined by '`x ≈ y` iff the
    elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/
@[to_additive
      "Given a surjective addition-preserving function `f` whose kernel is contained in\nan additive congruence relation `c`, the additive congruence relation on `f`'s codomain defined\nby '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.'"]
def mapOfSurjective (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (h : mulKer f H ≤ c)
    (hf : Surjective f) : Con N :=
  { c.toSetoid.mapOfSurjective f h hf with
    mul' := fun w x y z ⟨a, b, hw, hx, h1⟩ ⟨p, q, hy, hz, h2⟩ =>
      ⟨a * p, b * q, by rw [H, hw, hy], by rw [H, hx, hz], c.mul h1 h2⟩ }
#align con.map_of_surjective Con.mapOfSurjective
#align add_con.map_of_surjective AddCon.mapOfSurjective
-/

/- warning: con.map_of_surjective_eq_map_gen -> Con.mapOfSurjective_eq_mapGen is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {c : Con.{u1} M _inst_1} {f : M -> N} (H : forall (x : M) (y : M), Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (f x) (f y))) (h : LE.le.{u1} (Con.{u1} M _inst_1) (Con.hasLe.{u1} M _inst_1) (Con.mulKer.{u1, u2} M N _inst_1 _inst_2 f H) c) (hf : Function.Surjective.{succ u1, succ u2} M N f), Eq.{succ u2} (Con.{u2} N _inst_2) (Con.mapGen.{u1, u2} M N _inst_1 _inst_2 c f) (Con.mapOfSurjective.{u1, u2} M N _inst_1 _inst_2 c f H h hf)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {c : Con.{u2} M _inst_1} {f : M -> N} (H : forall (x : M) (y : M), Eq.{succ u1} N (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N _inst_2) (f x) (f y))) (h : LE.le.{u2} (Con.{u2} M _inst_1) (Con.instLECon.{u2} M _inst_1) (Con.mulKer.{u2, u1} M N _inst_1 _inst_2 f H) c) (hf : Function.Surjective.{succ u2, succ u1} M N f), Eq.{succ u1} (Con.{u1} N _inst_2) (Con.mapGen.{u2, u1} M N _inst_1 _inst_2 c f) (Con.mapOfSurjective.{u2, u1} M N _inst_1 _inst_2 c f H h hf)
Case conversion may be inaccurate. Consider using '#align con.map_of_surjective_eq_map_gen Con.mapOfSurjective_eq_mapGenₓ'. -/
/-- A specialization of 'the smallest congruence relation containing a congruence relation `c`
    equals `c`'. -/
@[to_additive
      "A specialization of 'the smallest additive congruence relation containing\nan additive congruence relation `c` equals `c`'."]
theorem mapOfSurjective_eq_mapGen {c : Con M} {f : M → N} (H : ∀ x y, f (x * y) = f x * f y)
    (h : mulKer f H ≤ c) (hf : Surjective f) : c.mapGen f = c.mapOfSurjective f H h hf := by
  rw [← con_gen_of_con (c.map_of_surjective f H h hf)] <;> rfl
#align con.map_of_surjective_eq_map_gen Con.mapOfSurjective_eq_mapGen
#align add_con.map_of_surjective_eq_map_gen AddCon.mapOfSurjective_eq_mapGen

#print Con.comap /-
/-- Given types with multiplications `M, N` and a congruence relation `c` on `N`, a
    multiplication-preserving map `f : M → N` induces a congruence relation on `f`'s domain
    defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' -/
@[to_additive
      "Given types with additions `M, N` and an additive congruence relation `c` on `N`,\nan addition-preserving map `f : M → N` induces an additive congruence relation on `f`'s domain\ndefined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' "]
def comap (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (c : Con N) : Con M :=
  { c.toSetoid.comap f with
    mul' := fun w x y z h1 h2 => show c (f (w * y)) (f (x * z)) by rw [H, H] <;> exact c.mul h1 h2 }
#align con.comap Con.comap
#align add_con.comap AddCon.comap
-/

#print Con.comap_rel /-
@[simp, to_additive]
theorem comap_rel {f : M → N} (H : ∀ x y, f (x * y) = f x * f y) {c : Con N} {x y : M} :
    comap f H c x y ↔ c (f x) (f y) :=
  Iff.rfl
#align con.comap_rel Con.comap_rel
#align add_con.comap_rel AddCon.comap_rel
-/

section

open _Root_.Quotient

#print Con.correspondence /-
/-- Given a congruence relation `c` on a type `M` with a multiplication, the order-preserving
    bijection between the set of congruence relations containing `c` and the congruence relations
    on the quotient of `M` by `c`. -/
@[to_additive
      "Given an additive congruence relation `c` on a type `M` with an addition,\nthe order-preserving bijection between the set of additive congruence relations containing `c` and\nthe additive congruence relations on the quotient of `M` by `c`."]
def correspondence : { d // c ≤ d } ≃o Con c.Quotient
    where
  toFun d :=
    d.1.mapOfSurjective coe _ (by rw [mul_ker_mk_eq] <;> exact d.2) <| @exists_rep _ c.toSetoid
  invFun d :=
    ⟨comap (coe : M → c.Quotient) (fun x y => rfl) d, fun _ _ h =>
      show d _ _ by rw [c.eq.2 h] <;> exact d.refl _⟩
  left_inv d :=
    Subtype.ext_iff_val.2 <|
      ext fun _ _ =>
        ⟨fun h =>
          let ⟨a, b, hx, hy, H⟩ := h
          d.1.trans (d.1.symm <| d.2 <| c.Eq.1 hx) <| d.1.trans H <| d.2 <| c.Eq.1 hy,
          fun h => ⟨_, _, rfl, rfl, h⟩⟩
  right_inv d :=
    let Hm :
      (mulKer (coe : M → c.Quotient) fun x y => rfl) ≤
        comap (coe : M → c.Quotient) (fun x y => rfl) d :=
      fun x y h => show d _ _ by rw [mul_ker_mk_eq] at h <;> exact c.eq.2 h ▸ d.refl _
    ext fun x y =>
      ⟨fun h =>
        let ⟨a, b, hx, hy, H⟩ := h
        hx ▸ hy ▸ H,
        Con.induction_on₂ x y fun w z h => ⟨w, z, rfl, rfl, h⟩⟩
  map_rel_iff' s t :=
    ⟨fun h _ _ hs =>
      let ⟨a, b, hx, hy, ht⟩ := h ⟨_, _, rfl, rfl, hs⟩
      t.1.trans (t.1.symm <| t.2 <| eq_rel.1 hx) <| t.1.trans ht <| t.2 <| eq_rel.1 hy,
      fun h _ _ hs =>
      let ⟨a, b, hx, hy, Hs⟩ := hs
      ⟨a, b, hx, hy, h Hs⟩⟩
#align con.correspondence Con.correspondence
#align add_con.correspondence AddCon.correspondence
-/

end

end

section MulOneClass

variable {M} [MulOneClass M] [MulOneClass N] [MulOneClass P] (c : Con M)

/- warning: con.mul_one_class -> Con.mulOneClass is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)), MulOneClass.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)), MulOneClass.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c)
Case conversion may be inaccurate. Consider using '#align con.mul_one_class Con.mulOneClassₓ'. -/
/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive
      "The quotient of an `add_monoid` by an additive congruence relation is\nan `add_monoid`."]
instance mulOneClass : MulOneClass c.Quotient
    where
  one := ((1 : M) : c.Quotient)
  mul := (· * ·)
  mul_one x := Quotient.inductionOn' x fun _ => congr_arg (coe : M → c.Quotient) <| mul_one _
  one_mul x := Quotient.inductionOn' x fun _ => congr_arg (coe : M → c.Quotient) <| one_mul _
#align con.mul_one_class Con.mulOneClass
#align add_con.add_zero_class AddCon.addZeroClass

variable {c}

/- warning: con.coe_one -> Con.coe_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)}, Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) (OfNat.ofNat.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) 1 (OfNat.mk.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) 1 (One.one.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (MulOneClass.toHasOne.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)}, Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (OfNat.ofNat.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) 1 (One.toOfNat1.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (MulOneClass.toOne.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c))))
Case conversion may be inaccurate. Consider using '#align con.coe_one Con.coe_oneₓ'. -/
/-- The 1 of the quotient of a monoid by a congruence relation is the equivalence class of the
    monoid's 1. -/
@[simp,
  to_additive
      "The 0 of the quotient of an `add_monoid` by an additive congruence relation\nis the equivalence class of the `add_monoid`'s 0."]
theorem coe_one : ((1 : M) : c.Quotient) = 1 :=
  rfl
#align con.coe_one Con.coe_one
#align add_con.coe_zero AddCon.coe_zero

variable (M c)

/- warning: con.submonoid -> Con.submonoid is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : MulOneClass.{u1} M], (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) -> (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) -> (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1))
Case conversion may be inaccurate. Consider using '#align con.submonoid Con.submonoidₓ'. -/
/-- The submonoid of `M × M` defined by a congruence relation on a monoid `M`. -/
@[to_additive
      "The `add_submonoid` of `M × M` defined by an additive congruence\nrelation on an `add_monoid` `M`."]
protected def submonoid : Submonoid (M × M)
    where
  carrier := { x | c x.1 x.2 }
  one_mem' := c.iseqv.1 1
  mul_mem' _ _ := c.mul
#align con.submonoid Con.submonoid
#align add_con.add_submonoid AddCon.addSubmonoid

variable {M c}

/- warning: con.of_submonoid -> Con.ofSubmonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (N : Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)), (Equivalence.{succ u1} M (fun (x : M) (y : M) => Membership.Mem.{u1, u1} (Prod.{u1, u1} M M) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (Prod.{u1, u1} M M) (Submonoid.setLike.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1))) (Prod.mk.{u1, u1} M M x y) N)) -> (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (N : Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)), (Equivalence.{succ u1} M (fun (x : M) (y : M) => Membership.mem.{u1, u1} (Prod.{u1, u1} M M) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (Prod.{u1, u1} M M) (Submonoid.instSetLikeSubmonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1))) (Prod.mk.{u1, u1} M M x y) N)) -> (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align con.of_submonoid Con.ofSubmonoidₓ'. -/
/-- The congruence relation on a monoid `M` from a submonoid of `M × M` for which membership
    is an equivalence relation. -/
@[to_additive
      "The additive congruence relation on an `add_monoid` `M` from\nan `add_submonoid` of `M × M` for which membership is an equivalence relation."]
def ofSubmonoid (N : Submonoid (M × M)) (H : Equivalence fun x y => (x, y) ∈ N) : Con M
    where
  R x y := (x, y) ∈ N
  iseqv := H
  mul' _ _ _ _ := N.mul_mem
#align con.of_submonoid Con.ofSubmonoid
#align add_con.of_add_submonoid AddCon.ofAddSubmonoid

/- warning: con.to_submonoid -> Con.toSubmonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Coe.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Coe.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1))
Case conversion may be inaccurate. Consider using '#align con.to_submonoid Con.toSubmonoidₓ'. -/
/-- Coercion from a congruence relation `c` on a monoid `M` to the submonoid of `M × M` whose
    elements are `(x, y)` such that `x` is related to `y` by `c`. -/
@[to_additive
      "Coercion from a congruence relation `c` on an `add_monoid` `M`\nto the `add_submonoid` of `M × M` whose elements are `(x, y)` such that `x`\nis related to `y` by `c`."]
instance toSubmonoid : Coe (Con M) (Submonoid (M × M)) :=
  ⟨fun c => c.Submonoid M⟩
#align con.to_submonoid Con.toSubmonoid
#align add_con.to_add_submonoid AddCon.toAddSubmonoid

/- warning: con.mem_coe -> Con.mem_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {x : M} {y : M}, Iff (Membership.Mem.{u1, u1} (Prod.{u1, u1} M M) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (Prod.{u1, u1} M M) (Submonoid.setLike.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1))) (Prod.mk.{u1, u1} M M x y) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (HasLiftT.mk.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (CoeTCₓ.coe.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (coeBase.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (Con.toSubmonoid.{u1} M _inst_1)))) c)) (Membership.Mem.{u1, u1} (Prod.{u1, u1} M M) (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasMem.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Prod.mk.{u1, u1} M M x y) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)} {x : M} {y : M}, Iff (Membership.mem.{u1, u1} (Prod.{u1, u1} M M) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (Prod.{u1, u1} M M) (Submonoid.instSetLikeSubmonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1))) (Prod.mk.{u1, u1} M M x y) (Con.submonoid.{u1} M _inst_1 c)) (Membership.mem.{u1, u1} (Prod.{u1, u1} M M) (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Con.instMembershipProdCon.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Prod.mk.{u1, u1} M M x y) c)
Case conversion may be inaccurate. Consider using '#align con.mem_coe Con.mem_coeₓ'. -/
@[to_additive]
theorem mem_coe {c : Con M} {x y} : (x, y) ∈ (↑c : Submonoid (M × M)) ↔ (x, y) ∈ c :=
  Iff.rfl
#align con.mem_coe Con.mem_coe
#align add_con.mem_coe AddCon.mem_coe

/- warning: con.to_submonoid_inj -> Con.to_submonoid_inj is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (d : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)), (Eq.{succ u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (HasLiftT.mk.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (CoeTCₓ.coe.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (coeBase.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (Con.toSubmonoid.{u1} M _inst_1)))) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (HasLiftT.mk.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (CoeTCₓ.coe.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (coeBase.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (Con.toSubmonoid.{u1} M _inst_1)))) d)) -> (Eq.{succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c d)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (d : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)), (Eq.{succ u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (Con.submonoid.{u1} M _inst_1 c) (Con.submonoid.{u1} M _inst_1 d)) -> (Eq.{succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) c d)
Case conversion may be inaccurate. Consider using '#align con.to_submonoid_inj Con.to_submonoid_injₓ'. -/
@[to_additive]
theorem to_submonoid_inj (c d : Con M) (H : (c : Submonoid (M × M)) = d) : c = d :=
  ext fun x y => show (x, y) ∈ (c : Submonoid (M × M)) ↔ (x, y) ∈ ↑d by rw [H]
#align con.to_submonoid_inj Con.to_submonoid_inj
#align add_con.to_add_submonoid_inj AddCon.to_addSubmonoid_inj

/- warning: con.le_iff -> Con.le_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {d : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)}, Iff (LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c d) (LE.le.{u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (Preorder.toLE.{u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (Prod.{u1, u1} M M) (Submonoid.setLike.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (HasLiftT.mk.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (CoeTCₓ.coe.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (coeBase.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (Con.toSubmonoid.{u1} M _inst_1)))) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (HasLiftT.mk.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (CoeTCₓ.coe.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (coeBase.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.mulOneClass.{u1, u1} M M _inst_1 _inst_1)) (Con.toSubmonoid.{u1} M _inst_1)))) d))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)} {d : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)}, Iff (LE.le.{u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Con.instLECon.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) c d) (LE.le.{u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (Preorder.toLE.{u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u1} (Prod.{u1, u1} M M) (Prod.instMulOneClassProd.{u1, u1} M M _inst_1 _inst_1)))))) (Con.submonoid.{u1} M _inst_1 c) (Con.submonoid.{u1} M _inst_1 d))
Case conversion may be inaccurate. Consider using '#align con.le_iff Con.le_iffₓ'. -/
@[to_additive]
theorem le_iff {c d : Con M} : c ≤ d ↔ (c : Submonoid (M × M)) ≤ d :=
  ⟨fun h x H => h H, fun h x y hc => h <| show (x, y) ∈ c from hc⟩
#align con.le_iff Con.le_iff
#align add_con.le_iff AddCon.le_iff

/- warning: con.ker -> Con.ker is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P], (MonoidHom.{u1, u2} M P _inst_1 _inst_3) -> (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P], (MonoidHom.{u1, u2} M P _inst_1 _inst_3) -> (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align con.ker Con.kerₓ'. -/
/-- The kernel of a monoid homomorphism as a congruence relation. -/
@[to_additive "The kernel of an `add_monoid` homomorphism as an additive congruence relation."]
def ker (f : M →* P) : Con M :=
  mulKer f f.3
#align con.ker Con.ker
#align add_con.ker AddCon.ker

/- warning: con.ker_rel -> Con.ker_rel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3) {x : M} {y : M}, Iff (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f) x y) (Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f y))
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] (f : MonoidHom.{u2, u1} M P _inst_1 _inst_3) {x : M} {y : M}, Iff (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f) x y) (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M P _inst_1 _inst_3))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M P _inst_1 _inst_3))) f y))
Case conversion may be inaccurate. Consider using '#align con.ker_rel Con.ker_relₓ'. -/
/-- The definition of the congruence relation defined by a monoid homomorphism's kernel. -/
@[simp,
  to_additive
      "The definition of the additive congruence relation defined by an `add_monoid`\nhomomorphism's kernel."]
theorem ker_rel (f : M →* P) {x y} : ker f x y ↔ f x = f y :=
  Iff.rfl
#align con.ker_rel Con.ker_rel
#align add_con.ker_rel AddCon.ker_rel

/- warning: con.quotient.inhabited -> Con.Quotient.inhabited is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)}, Inhabited.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)}, Inhabited.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c)
Case conversion may be inaccurate. Consider using '#align con.quotient.inhabited Con.Quotient.inhabitedₓ'. -/
/-- There exists an element of the quotient of a monoid by a congruence relation (namely 1). -/
@[to_additive
      "There exists an element of the quotient of an `add_monoid` by a congruence relation\n(namely 0)."]
instance Quotient.inhabited : Inhabited c.Quotient :=
  ⟨((1 : M) : c.Quotient)⟩
#align con.quotient.inhabited Con.Quotient.inhabited
#align add_con.quotient.inhabited AddCon.Quotient.inhabited

variable (c)

/- warning: con.mk' -> Con.mk' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)), MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)), MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)
Case conversion may be inaccurate. Consider using '#align con.mk' Con.mk'ₓ'. -/
/-- The natural homomorphism from a monoid to its quotient by a congruence relation. -/
@[to_additive
      "The natural homomorphism from an `add_monoid` to its quotient by an additive\ncongruence relation."]
def mk' : M →* c.Quotient :=
  ⟨coe, rfl, fun _ _ => rfl⟩
#align con.mk' Con.mk'
#align add_con.mk' AddCon.mk'

variable (x y : M)

/- warning: con.mk'_ker -> Con.mk'_ker is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)), Eq.{succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.ker.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (Con.mk'.{u1} M _inst_1 c)) c
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)), Eq.{succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Con.ker.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (Con.mk'.{u1} M _inst_1 c)) c
Case conversion may be inaccurate. Consider using '#align con.mk'_ker Con.mk'_kerₓ'. -/
/-- The kernel of the natural homomorphism from a monoid to its quotient by a congruence
    relation `c` equals `c`. -/
@[simp,
  to_additive
      "The kernel of the natural homomorphism from an `add_monoid` to its quotient by\nan additive congruence relation `c` equals `c`."]
theorem mk'_ker : ker c.mk' = c :=
  ext fun _ _ => c.Eq
#align con.mk'_ker Con.mk'_ker
#align add_con.mk'_ker AddCon.mk'_ker

variable {c}

/- warning: con.mk'_surjective -> Con.mk'_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)}, Function.Surjective.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (fun (_x : MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) => M -> (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c)) (MonoidHom.hasCoeToFun.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (Con.mk'.{u1} M _inst_1 c))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)}, Function.Surjective.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.monoidHomClass.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)))) (Con.mk'.{u1} M _inst_1 c))
Case conversion may be inaccurate. Consider using '#align con.mk'_surjective Con.mk'_surjectiveₓ'. -/
/-- The natural homomorphism from a monoid to its quotient by a congruence relation is
    surjective. -/
@[to_additive
      "The natural homomorphism from an `add_monoid` to its quotient by a congruence\nrelation is surjective."]
theorem mk'_surjective : Surjective c.mk' :=
  Quotient.surjective_Quotient_mk''
#align con.mk'_surjective Con.mk'_surjective
#align add_con.mk'_surjective AddCon.mk'_surjective

/- warning: con.coe_mk' -> Con.coe_mk' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)}, Eq.{succ u1} ((fun (_x : MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) => M -> (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c)) (Con.mk'.{u1} M _inst_1 c)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (fun (_x : MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) => M -> (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c)) (MonoidHom.hasCoeToFun.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (Con.mk'.{u1} M _inst_1 c)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)}, Eq.{succ u1} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) a) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.monoidHomClass.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)))) (Con.mk'.{u1} M _inst_1 c)) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c)
Case conversion may be inaccurate. Consider using '#align con.coe_mk' Con.coe_mk'ₓ'. -/
@[simp, to_additive]
theorem coe_mk' : (c.mk' : M → c.Quotient) = coe :=
  rfl
#align con.coe_mk' Con.coe_mk'
#align add_con.coe_mk' AddCon.coe_mk'

/- warning: con.mrange_mk' -> Con.mrange_mk' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)}, Eq.{succ u1} (Submonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.mrange.{u1, u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.monoidHomClass.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (Con.mk'.{u1} M _inst_1 c)) (Top.top.{u1} (Submonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (Submonoid.hasTop.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)}, Eq.{succ u1} (Submonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.mrange.{u1, u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.monoidHomClass.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (Con.mk'.{u1} M _inst_1 c)) (Top.top.{u1} (Submonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (Submonoid.instTopSubmonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)))
Case conversion may be inaccurate. Consider using '#align con.mrange_mk' Con.mrange_mk'ₓ'. -/
@[simp, to_additive]
theorem mrange_mk' : c.mk'.mrange = ⊤ :=
  MonoidHom.mrange_top_iff_surjective.2 mk'_surjective
#align con.mrange_mk' Con.mrange_mk'
#align add_con.mrange_mk' AddCon.mrange_mk'

/- warning: con.ker_apply_eq_preimage -> Con.ker_apply_eq_preimage is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {f : MonoidHom.{u1, u2} M P _inst_1 _inst_3} (x : M), Eq.{succ u1} (M -> Prop) (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f) x) (Set.preimage.{u1, u2} M P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f) (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f x)))
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] {f : MonoidHom.{u2, u1} M P _inst_1 _inst_3} (x : M), Eq.{succ u2} ((fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) x) (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f) x) (Set.preimage.{u2, u1} M P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M P _inst_1 _inst_3))) f) (Singleton.singleton.{u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) x) (Set.{u1} P) (Set.instSingletonSet.{u1} P) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M P _inst_1 _inst_3))) f x)))
Case conversion may be inaccurate. Consider using '#align con.ker_apply_eq_preimage Con.ker_apply_eq_preimageₓ'. -/
/-- The elements related to `x ∈ M`, `M` a monoid, by the kernel of a monoid homomorphism are
    those in the preimage of `f(x)` under `f`. -/
@[to_additive
      "The elements related to `x ∈ M`, `M` an `add_monoid`, by the kernel of\nan `add_monoid` homomorphism are those in the preimage of `f(x)` under `f`. "]
theorem ker_apply_eq_preimage {f : M →* P} (x) : (ker f) x = f ⁻¹' {f x} :=
  Set.ext fun x =>
    ⟨fun h => Set.mem_preimage.2 <| Set.mem_singleton_iff.2 h.symm, fun h =>
      (Set.mem_singleton_iff.1 <| Set.mem_preimage.1 h).symm⟩
#align con.ker_apply_eq_preimage Con.ker_apply_eq_preimage
#align add_con.ker_apply_eq_preimage AddCon.ker_apply_eq_preimage

/- warning: con.comap_eq -> Con.comap_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {f : MonoidHom.{u2, u1} N M _inst_2 _inst_1}, Eq.{succ u2} (Con.{u2} N (MulOneClass.toHasMul.{u2} N _inst_2)) (Con.comap.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MonoidHom.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MonoidHom.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) f) (MonoidHom.map_mul.{u2, u1} N M _inst_2 _inst_1 f) c) (Con.ker.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.comp.{u2, u1, u1} N M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (Con.mk'.{u1} M _inst_1 c) f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)} {f : MonoidHom.{u2, u1} N M _inst_2 _inst_1}, Eq.{succ u2} (Con.{u2} N (MulOneClass.toMul.{u2} N _inst_2)) (Con.comap.{u2, u1} N M (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} M _inst_1) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => M) _x) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) N M (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MonoidHom.monoidHomClass.{u2, u1} N M _inst_2 _inst_1))) f) (MonoidHom.map_mul.{u1, u2} N M _inst_2 _inst_1 f) c) (Con.ker.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.comp.{u2, u1, u1} N M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (Con.mk'.{u1} M _inst_1 c) f))
Case conversion may be inaccurate. Consider using '#align con.comap_eq Con.comap_eqₓ'. -/
/-- Given a monoid homomorphism `f : N → M` and a congruence relation `c` on `M`, the congruence
    relation induced on `N` by `f` equals the kernel of `c`'s quotient homomorphism composed with
    `f`. -/
@[to_additive
      "Given an `add_monoid` homomorphism `f : N → M` and an additive congruence relation\n`c` on `M`, the additive congruence relation induced on `N` by `f` equals the kernel of `c`'s\nquotient homomorphism composed with `f`."]
theorem comap_eq {f : N →* M} : comap f f.map_mul c = ker (c.mk'.comp f) :=
  ext fun x y => show c _ _ ↔ c.mk' _ = c.mk' _ by rw [← c.eq] <;> rfl
#align con.comap_eq Con.comap_eq
#align add_con.comap_eq AddCon.comap_eq

variable (c) (f : M →* P)

/- warning: con.lift -> Con.lift is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3), (LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) -> (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3)
but is expected to have type
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3), (LE.le.{u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Con.instLECon.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) c (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) -> (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3)
Case conversion may be inaccurate. Consider using '#align con.lift Con.liftₓ'. -/
/-- The homomorphism on the quotient of a monoid by a congruence relation `c` induced by a
    homomorphism constant on `c`'s equivalence classes. -/
@[to_additive
      "The homomorphism on the quotient of an `add_monoid` by an additive congruence\nrelation `c` induced by a homomorphism constant on `c`'s equivalence classes."]
def lift (H : c ≤ ker f) : c.Quotient →* P
    where
  toFun x := Con.liftOn x f fun _ _ h => H h
  map_one' := by rw [← f.map_one] <;> rfl
  map_mul' x y := Con.induction_on₂ x y fun m n => f.map_mul m n ▸ rfl
#align con.lift Con.lift
#align add_con.lift AddCon.lift

variable {c f}

/- warning: con.lift_mk' -> Con.lift_mk' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {f : MonoidHom.{u1, u2} M P _inst_1 _inst_3} (H : LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (x : M), Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (Con.lift.{u1, u2} M P _inst_1 _inst_3 c f H) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (fun (_x : MonoidHom.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) => M -> (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c)) (MonoidHom.hasCoeToFun.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_1 (Con.mulOneClass.{u1} M _inst_1 c)) (Con.mk'.{u1} M _inst_1 c) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f x)
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] {c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)} {f : MonoidHom.{u2, u1} M P _inst_1 _inst_3} (H : LE.le.{u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.instLECon.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) c (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidHom.{u2, u2} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c)) M (fun (a : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) a) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidHom.{u2, u2} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c)) M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidHom.{u2, u2} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c)) M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c) (MonoidHom.monoidHomClass.{u2, u2} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c)))) (Con.mk'.{u2} M _inst_1 c) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) (Con.lift.{u2, u1} M P _inst_1 _inst_3 c f H) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidHom.{u2, u2} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidHom.{u2, u2} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c)) M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidHom.{u2, u2} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c)) M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c) (MonoidHom.monoidHomClass.{u2, u2} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) _inst_1 (Con.mulOneClass.{u2} M _inst_1 c)))) (Con.mk'.{u2} M _inst_1 c) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M P _inst_1 _inst_3))) f x)
Case conversion may be inaccurate. Consider using '#align con.lift_mk' Con.lift_mk'ₓ'. -/
/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive
      "The diagram describing the universal property for quotients of `add_monoid`s\ncommutes."]
theorem lift_mk' (H : c ≤ ker f) (x) : c.lift f H (c.mk' x) = f x :=
  rfl
#align con.lift_mk' Con.lift_mk'
#align add_con.lift_mk' AddCon.lift_mk'

/- warning: con.lift_coe -> Con.lift_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {f : MonoidHom.{u1, u2} M P _inst_1 _inst_3} (H : LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (x : M), Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (Con.lift.{u1, u2} M P _inst_1 _inst_3 c f H) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f x)
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] {c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)} {f : MonoidHom.{u2, u1} M P _inst_1 _inst_3} (H : LE.le.{u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.instLECon.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) c (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) (Con.lift.{u2, u1} M P _inst_1 _inst_3 c f H) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M P _inst_1 _inst_3))) f x)
Case conversion may be inaccurate. Consider using '#align con.lift_coe Con.lift_coeₓ'. -/
/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[simp,
  to_additive
      "The diagram describing the universal property for quotients of `add_monoid`s\ncommutes."]
theorem lift_coe (H : c ≤ ker f) (x : M) : c.lift f H x = f x :=
  rfl
#align con.lift_coe Con.lift_coe
#align add_con.lift_coe AddCon.lift_coe

/- warning: con.lift_comp_mk' -> Con.lift_comp_mk' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {f : MonoidHom.{u1, u2} M P _inst_1 _inst_3} (H : LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u1, u2} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) _inst_3 (Con.lift.{u1, u2} M P _inst_1 _inst_3 c f H) (Con.mk'.{u1} M _inst_1 c)) f
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] {c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)} {f : MonoidHom.{u2, u1} M P _inst_1 _inst_3} (H : LE.le.{u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.instLECon.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) c (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) (MonoidHom.comp.{u2, u2, u1} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P _inst_1 (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (Con.lift.{u2, u1} M P _inst_1 _inst_3 c f H) (Con.mk'.{u2} M _inst_1 c)) f
Case conversion may be inaccurate. Consider using '#align con.lift_comp_mk' Con.lift_comp_mk'ₓ'. -/
/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[simp,
  to_additive
      "The diagram describing the universal property for quotients of `add_monoid`s\ncommutes."]
theorem lift_comp_mk' (H : c ≤ ker f) : (c.lift f H).comp c.mk' = f := by ext <;> rfl
#align con.lift_comp_mk' Con.lift_comp_mk'
#align add_con.lift_comp_mk' AddCon.lift_comp_mk'

/- warning: con.lift_apply_mk' -> Con.lift_apply_mk' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} (f : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (Con.lift.{u1, u2} M P _inst_1 _inst_3 c (MonoidHom.comp.{u1, u1, u2} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) _inst_3 f (Con.mk'.{u1} M _inst_1 c)) (fun (x : M) (y : M) (h : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c x y) => (fun (this : Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y))) => this) (Eq.mpr.{0} (Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y))) (Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y))) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y))) (Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y)))) (Eq.ndrec.{0, succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) x) (fun (_a : Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) => Eq.{1} Prop (Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y))) (Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f _a) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y)))) (rfl.{1} Prop (Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y) (Iff.mpr (Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y)) (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c x y) (Con.eq.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c x y) h))) (rfl.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) y)))))) f
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] {c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)} (f : MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.lift.{u2, u1} M P _inst_1 _inst_3 c (MonoidHom.comp.{u2, u2, u1} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P _inst_1 (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 f (Con.mk'.{u2} M _inst_1 c)) (fun (x : M) (y : M) (h : FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) c x y) => [mdata let_fun:1 (fun (this : Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y))) => this) (Eq.mpr.{0} (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y))) (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y))) (id.{0} (Eq.{1} Prop (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y))) (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y)))) (Eq.ndrec.{0, succ u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x) (fun (_a : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => Eq.{1} Prop (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y))) (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f _a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y)))) (Eq.refl.{1} Prop (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y)))) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y) (Iff.mpr (Eq.{succ u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y)) (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) c x y) (Con.eq.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c x y) h))) (Eq.refl.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c y))))])) f
Case conversion may be inaccurate. Consider using '#align con.lift_apply_mk' Con.lift_apply_mk'ₓ'. -/
/-- Given a homomorphism `f` from the quotient of a monoid by a congruence relation, `f` equals the
    homomorphism on the quotient induced by `f` composed with the natural map from the monoid to
    the quotient. -/
@[simp,
  to_additive
      "Given a homomorphism `f` from the quotient of an `add_monoid` by an additive\ncongruence relation, `f` equals the homomorphism on the quotient induced by `f` composed with the\nnatural map from the `add_monoid` to the quotient."]
theorem lift_apply_mk' (f : c.Quotient →* P) :
    (c.lift (f.comp c.mk') fun x y h => show f ↑x = f ↑y by rw [c.eq.2 h]) = f := by
  ext <;> rcases x with ⟨⟩ <;> rfl
#align con.lift_apply_mk' Con.lift_apply_mk'
#align add_con.lift_apply_mk' AddCon.lift_apply_mk'

/- warning: con.lift_funext -> Con.lift_funext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} (f : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (g : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3), (forall (a : M), Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) a)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c))) a))) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) f g)
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] {c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)} (f : MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (g : MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3), (forall (a : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c a)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) f (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c a)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) g (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c a))) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) f g)
Case conversion may be inaccurate. Consider using '#align con.lift_funext Con.lift_funextₓ'. -/
/-- Homomorphisms on the quotient of a monoid by a congruence relation are equal if they
    are equal on elements that are coercions from the monoid. -/
@[to_additive
      "Homomorphisms on the quotient of an `add_monoid` by an additive congruence relation\nare equal if they are equal on elements that are coercions from the `add_monoid`."]
theorem lift_funext (f g : c.Quotient →* P) (h : ∀ a : M, f a = g a) : f = g :=
  by
  rw [← lift_apply_mk' f, ← lift_apply_mk' g]
  congr 1
  exact MonoidHom.ext_iff.2 h
#align con.lift_funext Con.lift_funext
#align add_con.lift_funext AddCon.lift_funext

/- warning: con.lift_unique -> Con.lift_unique is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {f : MonoidHom.{u1, u2} M P _inst_1 _inst_3} (H : LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (g : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3), (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u1, u2} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) _inst_3 g (Con.mk'.{u1} M _inst_1 c)) f) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) g (Con.lift.{u1, u2} M P _inst_1 _inst_3 c f H))
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] {c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)} {f : MonoidHom.{u2, u1} M P _inst_1 _inst_3} (H : LE.le.{u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.instLECon.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) c (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) (g : MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3), (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) (MonoidHom.comp.{u2, u2, u1} M (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P _inst_1 (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 g (Con.mk'.{u2} M _inst_1 c)) f) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) g (Con.lift.{u2, u1} M P _inst_1 _inst_3 c f H))
Case conversion may be inaccurate. Consider using '#align con.lift_unique Con.lift_uniqueₓ'. -/
/-- The uniqueness part of the universal property for quotients of monoids. -/
@[to_additive "The uniqueness part of the universal property for quotients of `add_monoid`s."]
theorem lift_unique (H : c ≤ ker f) (g : c.Quotient →* P) (Hg : g.comp c.mk' = f) :
    g = c.lift f H :=
  lift_funext g (c.lift f H) fun x => by
    subst f
    rfl
#align con.lift_unique Con.lift_unique
#align add_con.lift_unique AddCon.lift_unique

/- warning: con.lift_range -> Con.lift_range is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {f : MonoidHom.{u1, u2} M P _inst_1 _inst_3} (H : LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)), Eq.{succ u2} (Submonoid.{u2} P _inst_3) (MonoidHom.mrange.{u1, u2, max u2 u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3 (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (MonoidHom.monoidHomClass.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (Con.lift.{u1, u2} M P _inst_1 _inst_3 c f H)) (MonoidHom.mrange.{u1, u2, max u2 u1} M P _inst_1 _inst_3 (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3) f)
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] {c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)} {f : MonoidHom.{u2, u1} M P _inst_1 _inst_3} (H : LE.le.{u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.instLECon.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) c (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)), Eq.{succ u1} (Submonoid.{u1} P _inst_3) (MonoidHom.mrange.{u2, u1, max u2 u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.lift.{u2, u1} M P _inst_1 _inst_3 c f H)) (MonoidHom.mrange.{u2, u1, max u2 u1} M P _inst_1 _inst_3 (MonoidHom.{u2, u1} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u2, u1} M P _inst_1 _inst_3) f)
Case conversion may be inaccurate. Consider using '#align con.lift_range Con.lift_rangeₓ'. -/
/-- Given a congruence relation `c` on a monoid and a homomorphism `f` constant on `c`'s
    equivalence classes, `f` has the same image as the homomorphism that `f` induces on the
    quotient. -/
@[to_additive
      "Given an additive congruence relation `c` on an `add_monoid` and a homomorphism `f`\nconstant on `c`'s equivalence classes, `f` has the same image as the homomorphism that `f` induces\non the quotient."]
theorem lift_range (H : c ≤ ker f) : (c.lift f H).mrange = f.mrange :=
  Submonoid.ext fun x => ⟨by rintro ⟨⟨y⟩, hy⟩ <;> exact ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨↑y, hy⟩⟩
#align con.lift_range Con.lift_range
#align add_con.lift_range AddCon.lift_range

/- warning: con.lift_surjective_of_surjective -> Con.lift_surjective_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {f : MonoidHom.{u1, u2} M P _inst_1 _inst_3} (h : LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)), (Function.Surjective.{succ u1, succ u2} M P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f)) -> (Function.Surjective.{succ u1, succ u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (Con.lift.{u1, u2} M P _inst_1 _inst_3 c f h)))
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] {c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)} {f : MonoidHom.{u2, u1} M P _inst_1 _inst_3} (h : LE.le.{u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.instLECon.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) c (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)), (Function.Surjective.{succ u2, succ u1} M P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M P _inst_1 _inst_3))) f)) -> (Function.Surjective.{succ u2, succ u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) (Con.lift.{u2, u1} M P _inst_1 _inst_3 c f h)))
Case conversion may be inaccurate. Consider using '#align con.lift_surjective_of_surjective Con.lift_surjective_of_surjectiveₓ'. -/
/-- Surjective monoid homomorphisms constant on a congruence relation `c`'s equivalence classes
    induce a surjective homomorphism on `c`'s quotient. -/
@[to_additive
      "Surjective `add_monoid` homomorphisms constant on an additive congruence\nrelation `c`'s equivalence classes induce a surjective homomorphism on `c`'s quotient."]
theorem lift_surjective_of_surjective (h : c ≤ ker f) (hf : Surjective f) :
    Surjective (c.lift f h) := fun y => Exists.elim (hf y) fun w hw => ⟨w, (lift_mk' h w).symm ▸ hw⟩
#align con.lift_surjective_of_surjective Con.lift_surjective_of_surjective
#align add_con.lift_surjective_of_surjective AddCon.lift_surjective_of_surjective

variable (c f)

/- warning: con.ker_eq_lift_of_injective -> Con.ker_eq_lift_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3) (H : LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)), (Function.Injective.{succ u1, succ u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) P (Con.mulOneClass.{u1} M _inst_1 c) _inst_3) (Con.lift.{u1, u2} M P _inst_1 _inst_3 c f H))) -> (Eq.{succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f) c)
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] (c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (f : MonoidHom.{u2, u1} M P _inst_1 _inst_3) (H : LE.le.{u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.instLECon.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) c (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)), (Function.Injective.{succ u2, succ u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) (Con.mulOneClass.{u2} M _inst_1 c)) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c) P (Con.mulOneClass.{u2} M _inst_1 c) _inst_3))) (Con.lift.{u2, u1} M P _inst_1 _inst_3 c f H))) -> (Eq.{succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f) c)
Case conversion may be inaccurate. Consider using '#align con.ker_eq_lift_of_injective Con.ker_eq_lift_of_injectiveₓ'. -/
/-- Given a monoid homomorphism `f` from `M` to `P`, the kernel of `f` is the unique congruence
    relation on `M` whose induced map from the quotient of `M` to `P` is injective. -/
@[to_additive
      "Given an `add_monoid` homomorphism `f` from `M` to `P`, the kernel of `f`\nis the unique additive congruence relation on `M` whose induced map from the quotient of `M`\nto `P` is injective."]
theorem ker_eq_lift_of_injective (H : c ≤ ker f) (h : Injective (c.lift f H)) : ker f = c :=
  to_setoid_inj <| ker_eq_lift_of_injective f H h
#align con.ker_eq_lift_of_injective Con.ker_eq_lift_of_injective
#align add_con.ker_eq_lift_of_injective AddCon.ker_eq_lift_of_injective

variable {c}

#print Con.kerLift /-
/-- The homomorphism induced on the quotient of a monoid by the kernel of a monoid homomorphism. -/
@[to_additive
      "The homomorphism induced on the quotient of an `add_monoid` by the kernel\nof an `add_monoid` homomorphism."]
def kerLift : (ker f).Quotient →* P :=
  (ker f).lift f fun _ _ => id
#align con.ker_lift Con.kerLift
#align add_con.ker_lift AddCon.kerLift
-/

variable {f}

/- warning: con.ker_lift_mk -> Con.kerLift_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {f : MonoidHom.{u1, u2} M P _inst_1 _inst_3} (x : M), Eq.{succ u2} P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3) (Con.kerLift.{u1, u2} M P _inst_1 _inst_3 f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)))) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f x)
but is expected to have type
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] {f : MonoidHom.{u1, u2} M P _inst_1 _inst_3} (x : M), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) => P) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f) x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (fun (_x : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) => P) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (MulOneClass.toMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f))) (MulOneClass.toMul.{u2} P _inst_3) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3 (MonoidHom.monoidHomClass.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3))) (Con.kerLift.{u1, u2} M P _inst_1 _inst_3 f) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f) x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} P _inst_3) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3))) f x)
Case conversion may be inaccurate. Consider using '#align con.ker_lift_mk Con.kerLift_mkₓ'. -/
/-- The diagram described by the universal property for quotients of monoids, when the congruence
    relation is the kernel of the homomorphism, commutes. -/
@[simp,
  to_additive
      "The diagram described by the universal property for quotients\nof `add_monoid`s, when the additive congruence relation is the kernel of the homomorphism,\ncommutes."]
theorem kerLift_mk (x : M) : kerLift f x = f x :=
  rfl
#align con.ker_lift_mk Con.kerLift_mk
#align add_con.ker_lift_mk AddCon.kerLift_mk

#print Con.kerLift_range_eq /-
/-- Given a monoid homomorphism `f`, the induced homomorphism on the quotient by `f`'s kernel has
    the same image as `f`. -/
@[simp,
  to_additive
      "Given an `add_monoid` homomorphism `f`, the induced homomorphism\non the quotient by `f`'s kernel has the same image as `f`."]
theorem kerLift_range_eq : (kerLift f).mrange = f.mrange :=
  lift_range fun _ _ => id
#align con.ker_lift_range_eq Con.kerLift_range_eq
#align add_con.ker_lift_range_eq AddCon.kerLift_range_eq
-/

/- warning: con.ker_lift_injective -> Con.kerLift_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3), Function.Injective.{succ u1, succ u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3) (fun (_x : MonoidHom.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) -> P) (MonoidHom.hasCoeToFun.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u1} M _inst_1 (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) _inst_3) (Con.kerLift.{u1, u2} M P _inst_1 _inst_3 f))
but is expected to have type
  forall {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} P] (f : MonoidHom.{u2, u1} M P _inst_1 _inst_3), Function.Injective.{succ u2, succ u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u2} M _inst_1 (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) (fun (_x : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u2} M _inst_1 (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) P (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) (Con.mulOneClass.{u2} M _inst_1 (Con.ker.{u2, u1} M P _inst_1 _inst_3 f))) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u2} M _inst_1 (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) _inst_3) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u2} M _inst_1 (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) _inst_3 (MonoidHom.monoidHomClass.{u2, u1} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) P (Con.mulOneClass.{u2} M _inst_1 (Con.ker.{u2, u1} M P _inst_1 _inst_3 f)) _inst_3))) (Con.kerLift.{u2, u1} M P _inst_1 _inst_3 f))
Case conversion may be inaccurate. Consider using '#align con.ker_lift_injective Con.kerLift_injectiveₓ'. -/
/-- A monoid homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
@[to_additive
      "An `add_monoid` homomorphism `f` induces an injective homomorphism on the quotient\nby `f`'s kernel."]
theorem kerLift_injective (f : M →* P) : Injective (kerLift f) := fun x y =>
  Quotient.inductionOn₂' x y fun _ _ => (ker f).Eq.2
#align con.ker_lift_injective Con.kerLift_injective
#align add_con.ker_lift_injective AddCon.kerLift_injective

/- warning: con.map -> Con.map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (d : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)), (LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c d) -> (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (d : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)), (LE.le.{u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Con.instLECon.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) c d) -> (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d))
Case conversion may be inaccurate. Consider using '#align con.map Con.mapₓ'. -/
/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, `d`'s quotient
    map induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
@[to_additive
      "Given additive congruence relations `c, d` on an `add_monoid` such that `d`\ncontains `c`, `d`'s quotient map induces a homomorphism from the quotient by `c` to the quotient\nby `d`."]
def map (c d : Con M) (h : c ≤ d) : c.Quotient →* d.Quotient :=
  c.lift d.mk' fun x y hc => show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc
#align con.map Con.map
#align add_con.map AddCon.map

/- warning: con.map_apply -> Con.map_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} {d : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)} (h : LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c d) (x : Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c), Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (fun (_x : MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d)) (MonoidHom.hasCoeToFun.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (Con.map.{u1} M _inst_1 c d h) x) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (fun (_x : MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) => (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) -> (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d)) (MonoidHom.hasCoeToFun.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (Con.lift.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) _inst_1 (Con.mulOneClass.{u1} M _inst_1 d) c (Con.mk'.{u1} M _inst_1 d) (fun (x : M) (y : M) (hc : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c x y) => Iff.mpr (Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d))) y)) (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) d x y) (Con.eq.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d x y) (h x y hc))) x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)} {d : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)} (h : LE.le.{u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Con.instLECon.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) c d) (x : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) => Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) x) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (fun (_x : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) => Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (MulOneClass.toMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (MulOneClass.toMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 d)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d) (MonoidHom.monoidHomClass.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)))) (Con.map.{u1} M _inst_1 c d h) x) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (fun (_x : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) => Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (MulOneClass.toMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (MulOneClass.toMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 d)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d) (MonoidHom.monoidHomClass.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d)))) (Con.lift.{u1, u1} M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) _inst_1 (Con.mulOneClass.{u1} M _inst_1 d) c (Con.mk'.{u1} M _inst_1 d) (fun (x : M) (y : M) (hc : FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) c x y) => Iff.mpr (Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d x) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d y)) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) d x y) (Con.eq.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d x y) (h x y hc))) x)
Case conversion may be inaccurate. Consider using '#align con.map_apply Con.map_applyₓ'. -/
/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, the definition of
    the homomorphism from the quotient by `c` to the quotient by `d` induced by `d`'s quotient
    map. -/
@[to_additive
      "Given additive congruence relations `c, d` on an `add_monoid` such that `d`\ncontains `c`, the definition of the homomorphism from the quotient by `c` to the quotient by `d`\ninduced by `d`'s quotient map."]
theorem map_apply {c d : Con M} (h : c ≤ d) (x) :
    c.map d h x = c.lift d.mk' (fun x y hc => d.Eq.2 <| h hc) x :=
  rfl
#align con.map_apply Con.map_apply
#align add_con.map_apply AddCon.map_apply

variable (c)

/- warning: con.quotient_ker_equiv_range -> Con.quotientKerEquivRange is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3), MulEquiv.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} P _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} P _inst_3) P (Submonoid.setLike.{u2} P _inst_3)) (MonoidHom.mrange.{u1, u2, max u2 u1} M P _inst_1 _inst_3 (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3) f)) (Con.hasMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (Submonoid.mul.{u2} P _inst_3 (MonoidHom.mrange.{u1, u2, max u2 u1} M P _inst_1 _inst_3 (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3) f))
but is expected to have type
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3), MulEquiv.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (Subtype.{succ u2} P (fun (x : P) => Membership.mem.{u2, u2} P (Submonoid.{u2} P _inst_3) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} P _inst_3) P (Submonoid.instSetLikeSubmonoid.{u2} P _inst_3)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M P _inst_1 _inst_3 (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3) f))) (Con.hasMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (Submonoid.mul.{u2} P _inst_3 (MonoidHom.mrange.{u1, u2, max u1 u2} M P _inst_1 _inst_3 (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3) f))
Case conversion may be inaccurate. Consider using '#align con.quotient_ker_equiv_range Con.quotientKerEquivRangeₓ'. -/
/-- The first isomorphism theorem for monoids. -/
@[to_additive "The first isomorphism theorem for `add_monoid`s."]
noncomputable def quotientKerEquivRange (f : M →* P) : (ker f).Quotient ≃* f.mrange :=
  {
    Equiv.ofBijective
        ((@MulEquiv.toMonoidHom (kerLift f).mrange _ _ _ <|
              MulEquiv.submonoidCongr kerLift_range_eq).comp
          (kerLift f).mrangeRestrict) <|
      (Equiv.bijective _).comp
        ⟨fun x y h =>
          kerLift_injective f <| by rcases x with ⟨⟩ <;> rcases y with ⟨⟩ <;> injections,
          fun ⟨w, z, hz⟩ => ⟨z, by rcases hz with ⟨⟩ <;> rcases _x with ⟨⟩ <;> rfl⟩⟩ with
    map_mul' := MonoidHom.map_mul _ }
#align con.quotient_ker_equiv_range Con.quotientKerEquivRange
#align add_con.quotient_ker_equiv_range AddCon.quotientKerEquivRange

/- warning: con.quotient_ker_equiv_of_right_inverse -> Con.quotientKerEquivOfRightInverse is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3) (g : P -> M), (Function.RightInverse.{succ u1, succ u2} M P g (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f)) -> (MulEquiv.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.hasMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (MulOneClass.toHasMul.{u2} P _inst_3))
but is expected to have type
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3) (g : P -> M), (Function.RightInverse.{succ u1, succ u2} M P g (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} P _inst_3) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3))) f)) -> (MulEquiv.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.hasMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (MulOneClass.toMul.{u2} P _inst_3))
Case conversion may be inaccurate. Consider using '#align con.quotient_ker_equiv_of_right_inverse Con.quotientKerEquivOfRightInverseₓ'. -/
/-- The first isomorphism theorem for monoids in the case of a homomorphism with right inverse. -/
@[to_additive
      "The first isomorphism theorem for `add_monoid`s in the case of a homomorphism\nwith right inverse.",
  simps]
def quotientKerEquivOfRightInverse (f : M →* P) (g : P → M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃* P :=
  { kerLift f with
    toFun := kerLift f
    invFun := coe ∘ g
    left_inv := fun x => kerLift_injective _ (by rw [Function.comp_apply, ker_lift_mk, hf])
    right_inv := hf }
#align con.quotient_ker_equiv_of_right_inverse Con.quotientKerEquivOfRightInverse
#align add_con.quotient_ker_equiv_of_right_inverse AddCon.quotientKerEquivOfRightInverse

/- warning: con.quotient_ker_equiv_of_surjective -> Con.quotientKerEquivOfSurjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3), (Function.Surjective.{succ u1, succ u2} M P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u2} M P _inst_1 _inst_3) f)) -> (MulEquiv.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.hasMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (MulOneClass.toHasMul.{u2} P _inst_3))
but is expected to have type
  forall {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} P] (f : MonoidHom.{u1, u2} M P _inst_1 _inst_3), (Function.Surjective.{succ u1, succ u2} M P (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} P _inst_3) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3))) f)) -> (MulEquiv.{u1, u2} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) P (Con.hasMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Con.ker.{u1, u2} M P _inst_1 _inst_3 f)) (MulOneClass.toMul.{u2} P _inst_3))
Case conversion may be inaccurate. Consider using '#align con.quotient_ker_equiv_of_surjective Con.quotientKerEquivOfSurjectiveₓ'. -/
/-- The first isomorphism theorem for monoids in the case of a surjective homomorphism.

For a `computable` version, see `con.quotient_ker_equiv_of_right_inverse`.
-/
@[to_additive
      "The first isomorphism theorem for `add_monoid`s in the case of a surjective\nhomomorphism.\n\nFor a `computable` version, see `add_con.quotient_ker_equiv_of_right_inverse`.\n"]
noncomputable def quotientKerEquivOfSurjective (f : M →* P) (hf : Surjective f) :
    (ker f).Quotient ≃* P :=
  quotientKerEquivOfRightInverse _ _ hf.HasRightInverse.some_spec
#align con.quotient_ker_equiv_of_surjective Con.quotientKerEquivOfSurjective
#align add_con.quotient_ker_equiv_of_surjective AddCon.quotientKerEquivOfSurjective

/- warning: con.comap_quotient_equiv -> Con.comapQuotientEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (f : MonoidHom.{u2, u1} N M _inst_2 _inst_1), MulEquiv.{u2, u1} (Con.Quotient.{u2} N (MulOneClass.toHasMul.{u2} N _inst_2) (Con.comap.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MonoidHom.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MonoidHom.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) f) (MonoidHom.map_mul.{u2, u1} N M _inst_2 _inst_1 f) c)) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Submonoid.setLike.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c))) (MonoidHom.mrange.{u2, u1, max u1 u2} N (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.monoidHomClass.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.comp.{u2, u1, u1} N M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (Con.mk'.{u1} M _inst_1 c) f))) (Con.hasMul.{u2} N (MulOneClass.toHasMul.{u2} N _inst_2) (Con.comap.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MonoidHom.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MonoidHom.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) f) (MonoidHom.map_mul.{u2, u1} N M _inst_2 _inst_1 f) c)) (Submonoid.mul.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.mrange.{u2, u1, max u1 u2} N (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.monoidHomClass.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.comp.{u2, u1, u1} N M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) _inst_2 _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (Con.mk'.{u1} M _inst_1 c) f)))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (f : MonoidHom.{u2, u1} N M _inst_2 _inst_1), MulEquiv.{u2, u1} (Con.Quotient.{u2} N (MulOneClass.toMul.{u2} N _inst_2) (Con.comap.{u2, u1} N M (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} M _inst_1) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => M) _x) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) N M (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MonoidHom.monoidHomClass.{u2, u1} N M _inst_2 _inst_1))) f) (MonoidHom.map_mul.{u1, u2} N M _inst_2 _inst_1 f) c)) (Subtype.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (fun (x : Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) => Membership.mem.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Submonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Submonoid.instSetLikeSubmonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c))) x (MonoidHom.mrange.{u2, u1, max u1 u2} N (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.monoidHomClass.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.comp.{u2, u1, u1} N M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (Con.mk'.{u1} M _inst_1 c) f)))) (Con.hasMul.{u2} N (MulOneClass.toMul.{u2} N _inst_2) (Con.comap.{u2, u1} N M (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} M _inst_1) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => M) _x) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) N M (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MonoidHom.monoidHomClass.{u2, u1} N M _inst_2 _inst_1))) f) (MonoidHom.map_mul.{u1, u2} N M _inst_2 _inst_1 f) c)) (Submonoid.mul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.mrange.{u2, u1, max u1 u2} N (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c) (MonoidHom.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.monoidHomClass.{u2, u1} N (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 (Con.mulOneClass.{u1} M _inst_1 c)) (MonoidHom.comp.{u2, u1, u1} N M (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) _inst_2 _inst_1 (Con.mulOneClass.{u1} M _inst_1 c) (Con.mk'.{u1} M _inst_1 c) f)))
Case conversion may be inaccurate. Consider using '#align con.comap_quotient_equiv Con.comapQuotientEquivₓ'. -/
/-- The second isomorphism theorem for monoids. -/
@[to_additive "The second isomorphism theorem for `add_monoid`s."]
noncomputable def comapQuotientEquiv (f : N →* M) :
    (comap f f.map_mul c).Quotient ≃* (c.mk'.comp f).mrange :=
  (Con.congr comap_eq).trans <| quotient_ker_equiv_range <| c.mk'.comp f
#align con.comap_quotient_equiv Con.comapQuotientEquiv
#align add_con.comap_quotient_equiv AddCon.comapQuotientEquiv

/- warning: con.quotient_quotient_equiv_quotient -> Con.quotientQuotientEquivQuotient is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (d : Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (h : LE.le.{u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (Con.hasLe.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) c d), MulEquiv.{u1, u1} (Con.Quotient.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (MulOneClass.toHasMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (Con.ker.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d) (Con.map.{u1} M _inst_1 c d h))) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.hasMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (MulOneClass.toHasMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (Con.ker.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d) (Con.map.{u1} M _inst_1 c d h))) (Con.hasMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1) d)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (d : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (h : LE.le.{u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Con.instLECon.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) c d), MulEquiv.{u1, u1} (Con.Quotient.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (MulOneClass.toMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (Con.ker.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d) (Con.map.{u1} M _inst_1 c d h))) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.hasMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (MulOneClass.toMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.mulOneClass.{u1} M _inst_1 c)) (Con.ker.{u1, u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d) (Con.mulOneClass.{u1} M _inst_1 c) (Con.mulOneClass.{u1} M _inst_1 d) (Con.map.{u1} M _inst_1 c d h))) (Con.hasMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1) d)
Case conversion may be inaccurate. Consider using '#align con.quotient_quotient_equiv_quotient Con.quotientQuotientEquivQuotientₓ'. -/
/-- The third isomorphism theorem for monoids. -/
@[to_additive "The third isomorphism theorem for `add_monoid`s."]
def quotientQuotientEquivQuotient (c d : Con M) (h : c ≤ d) :
    (ker (c.map d h)).Quotient ≃* d.Quotient :=
  { quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_mul' := fun x y =>
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul] <;> rfl }
#align con.quotient_quotient_equiv_quotient Con.quotientQuotientEquivQuotient
#align add_con.quotient_quotient_equiv_quotient AddCon.quotientQuotientEquivQuotient

end MulOneClass

section Monoids

/- warning: con.pow -> Con.pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (n : Nat) {w : M} {x : M}, (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c w x) -> (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) w n) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) x n))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (n : Nat) {w : M} {x : M}, (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c w x) -> (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) w n) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) x n))
Case conversion may be inaccurate. Consider using '#align con.pow Con.powₓ'. -/
/-- Multiplicative congruence relations preserve natural powers. -/
@[to_additive AddCon.nsmul "Additive congruence relations preserve natural scaling."]
protected theorem pow {M : Type _} [Monoid M] (c : Con M) :
    ∀ (n : ℕ) {w x}, c w x → c (w ^ n) (x ^ n)
  | 0, w, x, h => by simpa using c.refl _
  | Nat.succ n, w, x, h => by simpa [pow_succ] using c.mul h (pow n h)
#align con.pow Con.pow
#align add_con.nsmul AddCon.nsmul

@[to_additive]
instance {M : Type _} [MulOneClass M] (c : Con M) : One c.Quotient
    where one := ((1 : M) : c.Quotient)

/- warning: con.smul -> Con.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : SMul.{u1, u2} α M] [_inst_3 : IsScalarTower.{u1, u2, u2} α M M _inst_2 (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) _inst_2] (c : Con.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (a : α) {w : M} {x : M}, (coeFn.{succ u2, succ u2} (Con.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (fun (_x : Con.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) => M -> M -> Prop) (Con.hasCoeToFun.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) c w x) -> (coeFn.{succ u2, succ u2} (Con.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (fun (_x : Con.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) => M -> M -> Prop) (Con.hasCoeToFun.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) c (SMul.smul.{u1, u2} α M _inst_2 a w) (SMul.smul.{u1, u2} α M _inst_2 a x))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : SMul.{u2, u1} α M] [_inst_3 : IsScalarTower.{u2, u1, u1} α M M _inst_2 (Mul.toSMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) _inst_2] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (a : α) {w : M} {x : M}, (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) c w x) -> (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) c (HSMul.hSMul.{u2, u1, u1} α M M (instHSMul.{u2, u1} α M _inst_2) a w) (HSMul.hSMul.{u2, u1, u1} α M M (instHSMul.{u2, u1} α M _inst_2) a x))
Case conversion may be inaccurate. Consider using '#align con.smul Con.smulₓ'. -/
@[to_additive]
theorem smul {α M : Type _} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) (a : α)
    {w x : M} (h : c w x) : c (a • w) (a • x) := by
  simpa only [smul_one_mul] using c.mul (c.refl' (a • 1 : M)) h
#align con.smul Con.smul
#align add_con.vadd AddCon.vadd

/- warning: add_con.quotient.has_nsmul -> AddCon.Quotient.nsmul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : AddMonoid.{u1} M] (c : AddCon.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1))), SMul.{0, u1} Nat (AddCon.Quotient.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : AddMonoid.{u1} M] (c : AddCon.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1))), SMul.{0, u1} Nat (AddCon.Quotient.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)) c)
Case conversion may be inaccurate. Consider using '#align add_con.quotient.has_nsmul AddCon.Quotient.nsmulₓ'. -/
instance AddCon.Quotient.nsmul {M : Type _} [AddMonoid M] (c : AddCon M) : SMul ℕ c.Quotient
    where smul n := Quotient.map' ((· • ·) n) fun x y => c.nsmul n
#align add_con.quotient.has_nsmul AddCon.Quotient.nsmul

@[to_additive AddCon.Quotient.nsmul]
instance {M : Type _} [Monoid M] (c : Con M) : Pow c.Quotient ℕ
    where pow x n := Quotient.map' (fun x => x ^ n) (fun x y => c.pow n) x

/- warning: con.semigroup -> Con.semigroup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Semigroup.{u1} M] (c : Con.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)), Semigroup.{u1} (Con.Quotient.{u1} M (Semigroup.toHasMul.{u1} M _inst_1) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Semigroup.{u1} M] (c : Con.{u1} M (Semigroup.toMul.{u1} M _inst_1)), Semigroup.{u1} (Con.Quotient.{u1} M (Semigroup.toMul.{u1} M _inst_1) c)
Case conversion may be inaccurate. Consider using '#align con.semigroup Con.semigroupₓ'. -/
/-- The quotient of a semigroup by a congruence relation is a semigroup. -/
@[to_additive
      "The quotient of an `add_semigroup` by an additive congruence relation is\nan `add_semigroup`."]
instance semigroup {M : Type _} [Semigroup M] (c : Con M) : Semigroup c.Quotient :=
  Function.Surjective.semigroup _ Quotient.surjective_Quotient_mk'' fun _ _ => rfl
#align con.semigroup Con.semigroup
#align add_con.add_semigroup AddCon.addSemigroup

/- warning: con.comm_semigroup -> Con.commSemigroup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommSemigroup.{u1} M] (c : Con.{u1} M (Semigroup.toHasMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))), CommSemigroup.{u1} (Con.Quotient.{u1} M (Semigroup.toHasMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1)) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommSemigroup.{u1} M] (c : Con.{u1} M (Semigroup.toMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))), CommSemigroup.{u1} (Con.Quotient.{u1} M (Semigroup.toMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1)) c)
Case conversion may be inaccurate. Consider using '#align con.comm_semigroup Con.commSemigroupₓ'. -/
/-- The quotient of a commutative semigroup by a congruence relation is a semigroup. -/
@[to_additive
      "The quotient of an `add_comm_semigroup` by an additive congruence relation is\nan `add_semigroup`."]
instance commSemigroup {M : Type _} [CommSemigroup M] (c : Con M) : CommSemigroup c.Quotient :=
  Function.Surjective.commSemigroup _ Quotient.surjective_Quotient_mk'' fun _ _ => rfl
#align con.comm_semigroup Con.commSemigroup
#align add_con.add_comm_semigroup AddCon.addCommSemigroup

/- warning: con.monoid -> Con.monoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))), Monoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))), Monoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c)
Case conversion may be inaccurate. Consider using '#align con.monoid Con.monoidₓ'. -/
/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive
      "The quotient of an `add_monoid` by an additive congruence relation is\nan `add_monoid`."]
instance monoid {M : Type _} [Monoid M] (c : Con M) : Monoid c.Quotient :=
  Function.Surjective.monoid _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl) fun _ _ => rfl
#align con.monoid Con.monoid
#align add_con.add_monoid AddCon.addMonoid

/- warning: con.comm_monoid -> Con.commMonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))), CommMonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))), CommMonoid.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) c)
Case conversion may be inaccurate. Consider using '#align con.comm_monoid Con.commMonoidₓ'. -/
/-- The quotient of a `comm_monoid` by a congruence relation is a `comm_monoid`. -/
@[to_additive
      "The quotient of an `add_comm_monoid` by an additive congruence\nrelation is an `add_comm_monoid`."]
instance commMonoid {M : Type _} [CommMonoid M] (c : Con M) : CommMonoid c.Quotient :=
  Function.Surjective.commMonoid _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl) fun _ _ =>
    rfl
#align con.comm_monoid Con.commMonoid
#align add_con.add_comm_monoid AddCon.addCommMonoid

end Monoids

section Groups

variable {M} [Group M] [Group N] [Group P] (c : Con M)

/- warning: con.inv -> Con.inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) {w : M} {x : M}, (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c w x) -> (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c (Inv.inv.{u1} M (DivInvMonoid.toHasInv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)) w) (Inv.inv.{u1} M (DivInvMonoid.toHasInv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)) x))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) {w : M} {x : M}, (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c w x) -> (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c (Inv.inv.{u1} M (InvOneClass.toInv.{u1} M (DivInvOneMonoid.toInvOneClass.{u1} M (DivisionMonoid.toDivInvOneMonoid.{u1} M (Group.toDivisionMonoid.{u1} M _inst_1)))) w) (Inv.inv.{u1} M (InvOneClass.toInv.{u1} M (DivInvOneMonoid.toInvOneClass.{u1} M (DivisionMonoid.toDivInvOneMonoid.{u1} M (Group.toDivisionMonoid.{u1} M _inst_1)))) x))
Case conversion may be inaccurate. Consider using '#align con.inv Con.invₓ'. -/
/-- Multiplicative congruence relations preserve inversion. -/
@[to_additive "Additive congruence relations preserve negation."]
protected theorem inv : ∀ {w x}, c w x → c w⁻¹ x⁻¹ := fun x y h => by
  simpa using c.symm (c.mul (c.mul (c.refl x⁻¹) h) (c.refl y⁻¹))
#align con.inv Con.inv
#align add_con.neg AddCon.neg

/- warning: con.div -> Con.div is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) {w : M} {x : M} {y : M} {z : M}, (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c w x) -> (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c y z) -> (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) w y) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) x z))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) {w : M} {x : M} {y : M} {z : M}, (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c w x) -> (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c y z) -> (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) w y) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) x z))
Case conversion may be inaccurate. Consider using '#align con.div Con.divₓ'. -/
/-- Multiplicative congruence relations preserve division. -/
@[to_additive "Additive congruence relations preserve subtraction."]
protected theorem div : ∀ {w x y z}, c w x → c y z → c (w / y) (x / z) := fun w x y z h1 h2 => by
  simpa only [div_eq_mul_inv] using c.mul h1 (c.inv h2)
#align con.div Con.div
#align add_con.sub AddCon.sub

/- warning: con.zpow -> Con.zpow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) (n : Int) {w : M} {x : M}, (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c w x) -> (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c (HPow.hPow.{u1, 0, u1} M Int M (instHPow.{u1, 0} M Int (DivInvMonoid.Pow.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) w n) (HPow.hPow.{u1, 0, u1} M Int M (instHPow.{u1, 0} M Int (DivInvMonoid.Pow.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) x n))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) (n : Int) {w : M} {x : M}, (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c w x) -> (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))) c (HPow.hPow.{u1, 0, u1} M Int M (instHPow.{u1, 0} M Int (DivInvMonoid.Pow.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) w n) (HPow.hPow.{u1, 0, u1} M Int M (instHPow.{u1, 0} M Int (DivInvMonoid.Pow.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) x n))
Case conversion may be inaccurate. Consider using '#align con.zpow Con.zpowₓ'. -/
/-- Multiplicative congruence relations preserve integer powers. -/
@[to_additive AddCon.zsmul "Additive congruence relations preserve integer scaling."]
protected theorem zpow : ∀ (n : ℤ) {w x}, c w x → c (w ^ n) (x ^ n)
  | Int.ofNat n, w, x, h => by simpa only [zpow_ofNat] using c.pow _ h
  | -[n+1], w, x, h => by simpa only [zpow_negSucc] using c.inv (c.pow _ h)
#align con.zpow Con.zpow
#align add_con.zsmul AddCon.zsmul

/- warning: con.has_inv -> Con.hasInv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))), Inv.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))), Inv.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))) c)
Case conversion may be inaccurate. Consider using '#align con.has_inv Con.hasInvₓ'. -/
/-- The inversion induced on the quotient by a congruence relation on a type with a
    inversion. -/
@[to_additive
      "The negation induced on the quotient by an additive congruence relation on a type\nwith an negation."]
instance hasInv : Inv c.Quotient :=
  ⟨Quotient.map' Inv.inv fun a b => c.inv⟩
#align con.has_inv Con.hasInv
#align add_con.has_neg AddCon.hasNeg

/- warning: con.has_div -> Con.hasDiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))), Div.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))), Div.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))) c)
Case conversion may be inaccurate. Consider using '#align con.has_div Con.hasDivₓ'. -/
/-- The division induced on the quotient by a congruence relation on a type with a
    division. -/
@[to_additive
      "The subtraction induced on the quotient by an additive congruence relation on a type\nwith a subtraction."]
instance hasDiv : Div c.Quotient :=
  ⟨Quotient.map₂' (· / ·) fun _ _ h₁ _ _ h₂ => c.div h₁ h₂⟩
#align con.has_div Con.hasDiv
#align add_con.has_sub AddCon.hasSub

/- warning: add_con.quotient.has_zsmul -> AddCon.Quotient.zsmul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : AddGroup.{u1} M] (c : AddCon.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M _inst_4))))), SMul.{0, u1} Int (AddCon.Quotient.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M _inst_4)))) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : AddGroup.{u1} M] (c : AddCon.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M _inst_4))))), SMul.{0, u1} Int (AddCon.Quotient.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M _inst_4)))) c)
Case conversion may be inaccurate. Consider using '#align add_con.quotient.has_zsmul AddCon.Quotient.zsmulₓ'. -/
/-- The integer scaling induced on the quotient by a congruence relation on a type with a
    subtraction. -/
instance AddCon.Quotient.zsmul {M : Type _} [AddGroup M] (c : AddCon M) : SMul ℤ c.Quotient :=
  ⟨fun z => Quotient.map' ((· • ·) z) fun x y => c.zsmul z⟩
#align add_con.quotient.has_zsmul AddCon.Quotient.zsmul

/- warning: con.has_zpow -> Con.zpowinst is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))), Pow.{u1, 0} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))) c) Int
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))), Pow.{u1, 0} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))) c) Int
Case conversion may be inaccurate. Consider using '#align con.has_zpow Con.zpowinstₓ'. -/
/-- The integer power induced on the quotient by a congruence relation on a type with a
    division. -/
@[to_additive AddCon.Quotient.zsmul]
instance zpowinst : Pow c.Quotient ℤ :=
  ⟨fun x z => Quotient.map' (fun x => x ^ z) (fun x y h => c.zpow z h) x⟩
#align con.has_zpow Con.zpowinst
#align add_con.quotient.has_zsmul AddCon.Quotient.zsmul

/- warning: con.group -> Con.group is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))), Group.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))) c)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] (c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))), Group.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))) c)
Case conversion may be inaccurate. Consider using '#align con.group Con.groupₓ'. -/
/-- The quotient of a group by a congruence relation is a group. -/
@[to_additive
      "The quotient of an `add_group` by an additive congruence relation is\nan `add_group`."]
instance group : Group c.Quotient :=
  Function.Surjective.group _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align con.group Con.group
#align add_con.add_group AddCon.addGroup

end Groups

section Units

variable {α : Type _} [Monoid M] {c : Con M}

/- warning: con.lift_on_units -> Con.liftOnUnits is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))}, (Units.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c)) -> (forall (f : forall (x : M) (y : M), (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> α), (forall (x : M) (y : M) (hxy : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (hyx : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (x' : M) (y' : M) (hxy' : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x' y') (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (hyx' : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y' x') (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))), (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c x x') -> (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c y y') -> (Eq.{succ u2} α (f x y hxy hyx) (f x' y' hxy' hyx'))) -> α)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))}, (Units.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c)) -> (forall (f : forall (x : M) (y : M), (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> α), (forall (x : M) (y : M) (hxy : FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) (hyx : FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) (x' : M) (y' : M) (hxy' : FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x' y') (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) (hyx' : FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y' x') (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))), (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c x x') -> (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c y y') -> (Eq.{succ u2} α (f x y hxy hyx) (f x' y' hxy' hyx'))) -> α)
Case conversion may be inaccurate. Consider using '#align con.lift_on_units Con.liftOnUnitsₓ'. -/
/-- In order to define a function `(con.quotient c)ˣ → α` on the units of `con.quotient c`,
where `c : con M` is a multiplicative congruence on a monoid, it suffices to define a function `f`
that takes elements `x y : M` with proofs of `c (x * y) 1` and `c (y * x) 1`, and returns an element
of `α` provided that `f x y _ _ = f x' y' _ _` whenever `c x x'` and `c y y'`. -/
@[to_additive]
def liftOnUnits (u : Units c.Quotient) (f : ∀ x y : M, c (x * y) 1 → c (y * x) 1 → α)
    (Hf : ∀ x y hxy hyx x' y' hxy' hyx', c x x' → c y y' → f x y hxy hyx = f x' y' hxy' hyx') : α :=
  by
  refine'
    @Con.hrecOn₂ M M _ _ c c (fun x y => x * y = 1 → y * x = 1 → α) (u : c.quotient)
      (↑u⁻¹ : c.quotient)
      (fun (x y : M) (hxy : (x * y : c.quotient) = 1) (hyx : (y * x : c.quotient) = 1) =>
        f x y (c.eq.1 hxy) (c.eq.1 hyx))
      (fun x y x' y' hx hy => _) u.3 u.4
  ext1; · rw [c.eq.2 hx, c.eq.2 hy]
  rintro Hxy Hxy' -
  ext1; · rw [c.eq.2 hx, c.eq.2 hy]
  rintro Hyx Hyx' -
  exact hEq_of_eq (Hf _ _ _ _ _ _ _ _ hx hy)
#align con.lift_on_units Con.liftOnUnits
#align add_con.lift_on_add_units AddCon.liftOnAddUnits

/-- In order to define a function `(con.quotient c)ˣ → α` on the units of `con.quotient c`,
where `c : con M` is a multiplicative congruence on a monoid, it suffices to define a function `f`
that takes elements `x y : M` with proofs of `c (x * y) 1` and `c (y * x) 1`, and returns an element
of `α` provided that `f x y _ _ = f x' y' _ _` whenever `c x x'` and `c y y'`. -/
add_decl_doc AddCon.liftOnAddUnits

/- warning: con.lift_on_units_mk -> Con.liftOnUnits_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))} (f : forall (x : M) (y : M), (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> α) (Hf : forall (x : M) (y : M) (hxy : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (hyx : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (x' : M) (y' : M) (hxy' : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x' y') (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (hyx' : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y' x') (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))), (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c x x') -> (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c y y') -> (Eq.{succ u2} α (f x y hxy hyx) (f x' y' hxy' hyx'))) (x : M) (y : M) (hxy : Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HMul.hMul.{u1, u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (instHMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (MulOneClass.toHasMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Monoid.toMulOneClass.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) y)) (OfNat.ofNat.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) 1 (OfNat.mk.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) 1 (One.one.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (MulOneClass.toHasOne.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Monoid.toMulOneClass.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c))))))) (hyx : Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HMul.hMul.{u1, u1, u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (instHMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (MulOneClass.toHasMul.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Monoid.toMulOneClass.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) y) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) x)) (OfNat.ofNat.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) 1 (OfNat.mk.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) 1 (One.one.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (MulOneClass.toHasOne.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Monoid.toMulOneClass.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c))))))), Eq.{succ u2} α (Con.liftOnUnits.{u1, u2} M α _inst_1 c (Units.mk.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) y) hxy hyx) f Hf) (f x y (Iff.mp (Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))))) (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (Con.eq.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) hxy) (Iff.mp (Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))))) (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (Con.eq.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) hyx))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] {c : Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))} (f : forall (x : M) (y : M), (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x y) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) -> (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) y x) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) -> α) (Hf : forall (x : M) (y : M) (hxy : FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x y) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) (hyx : FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) y x) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) (x' : M) (y' : M) (hxy' : FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x' y') (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) (hyx' : FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) y' x') (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))), (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c x x') -> (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c y y') -> (Eq.{succ u1} α (f x y hxy hyx) (f x' y' hxy' hyx'))) (x : M) (y : M) (hxy : Eq.{succ u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (HMul.hMul.{u2, u2, u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (instHMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Monoid.toMulOneClass.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.monoid.{u2} M _inst_1 c)))) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c x) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c y)) (OfNat.ofNat.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) 1 (One.toOfNat1.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Monoid.toOne.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.monoid.{u2} M _inst_1 c))))) (hyx : Eq.{succ u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (HMul.hMul.{u2, u2, u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (instHMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (MulOneClass.toMul.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Monoid.toMulOneClass.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.monoid.{u2} M _inst_1 c)))) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c y) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c x)) (OfNat.ofNat.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) 1 (One.toOfNat1.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Monoid.toOne.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.monoid.{u2} M _inst_1 c))))), Eq.{succ u1} α (Con.liftOnUnits.{u2, u1} M α _inst_1 c (Units.mk.{u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.monoid.{u2} M _inst_1 c) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c x) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c y) hxy hyx) f Hf) (f x y (Iff.mp (Eq.{succ u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x y)) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1))))) (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x y) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) (Con.eq.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x y) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) hxy) (Iff.mp (Eq.{succ u2} (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) y x)) (Con.toQuotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1))))) (FunLike.coe.{succ u2, succ u2, succ u2} (Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) y x) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) (Con.eq.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) c (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) y x) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) hyx))
Case conversion may be inaccurate. Consider using '#align con.lift_on_units_mk Con.liftOnUnits_mkₓ'. -/
@[simp, to_additive]
theorem liftOnUnits_mk (f : ∀ x y : M, c (x * y) 1 → c (y * x) 1 → α)
    (Hf : ∀ x y hxy hyx x' y' hxy' hyx', c x x' → c y y' → f x y hxy hyx = f x' y' hxy' hyx')
    (x y : M) (hxy hyx) :
    liftOnUnits ⟨(x : c.Quotient), y, hxy, hyx⟩ f Hf = f x y (c.Eq.1 hxy) (c.Eq.1 hyx) :=
  rfl
#align con.lift_on_units_mk Con.liftOnUnits_mk
#align add_con.lift_on_add_units_mk AddCon.liftOnAddUnits_mk

/- warning: con.induction_on_units -> Con.induction_on_units is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {c : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))} {p : (Units.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c)) -> Prop} (u : Units.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c)), (forall (x : M) (y : M) (hxy : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (hyx : coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))), p (Units.mk.{u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) y) (Iff.mpr (Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))))) (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (Con.eq.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) hxy) (Iff.mpr (Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (HasLiftT.mk.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (CoeTCₓ.coe.{succ u1, succ u1} M (Con.Quotient.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.Quotient.hasCoeT.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))))) (coeFn.{succ u1, succ u1} (Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (fun (_x : Con.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) => M -> M -> Prop) (Con.hasCoeToFun.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (Con.eq.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) hyx))) -> (p u)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {c : Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))} {p : (Units.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c)) -> Prop} (u : Units.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c)), (forall (x : M) (y : M) (hxy : FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) (hyx : FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))), p (Units.mk.{u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.monoid.{u1} M _inst_1 c) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c x) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c y) (Iff.mpr (Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c ((fun (x._@.Mathlib.GroupTheory.Congruence._hyg.1889 : M) (x._@.Mathlib.GroupTheory.Congruence._hyg.1891 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.GroupTheory.Congruence._hyg.1889 x._@.Mathlib.GroupTheory.Congruence._hyg.1891) x y)) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c ((fun (x._@.Mathlib.GroupTheory.Congruence._hyg.1889 : M) (x._@.Mathlib.GroupTheory.Congruence._hyg.1891 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.GroupTheory.Congruence._hyg.1889 x._@.Mathlib.GroupTheory.Congruence._hyg.1891) x y) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (Con.eq.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c ((fun (x._@.Mathlib.GroupTheory.Congruence._hyg.1889 : M) (x._@.Mathlib.GroupTheory.Congruence._hyg.1891 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.GroupTheory.Congruence._hyg.1889 x._@.Mathlib.GroupTheory.Congruence._hyg.1891) x y) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) hxy) (Iff.mpr (Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c ((fun (x._@.Mathlib.GroupTheory.Congruence._hyg.1889 : M) (x._@.Mathlib.GroupTheory.Congruence._hyg.1891 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.GroupTheory.Congruence._hyg.1889 x._@.Mathlib.GroupTheory.Congruence._hyg.1891) y x)) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (FunLike.coe.{succ u1, succ u1, succ u1} (Con.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.GroupTheory.Congruence._hyg.479 : M) => M -> Prop) _x) (Con.instFunLikeConForAllProp.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) c ((fun (x._@.Mathlib.GroupTheory.Congruence._hyg.1889 : M) (x._@.Mathlib.GroupTheory.Congruence._hyg.1891 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.GroupTheory.Congruence._hyg.1889 x._@.Mathlib.GroupTheory.Congruence._hyg.1891) y x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (Con.eq.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) c ((fun (x._@.Mathlib.GroupTheory.Congruence._hyg.1889 : M) (x._@.Mathlib.GroupTheory.Congruence._hyg.1891 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.GroupTheory.Congruence._hyg.1889 x._@.Mathlib.GroupTheory.Congruence._hyg.1891) y x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) hyx))) -> (p u)
Case conversion may be inaccurate. Consider using '#align con.induction_on_units Con.induction_on_unitsₓ'. -/
@[elab_as_elim, to_additive]
theorem induction_on_units {p : Units c.Quotient → Prop} (u : Units c.Quotient)
    (H : ∀ (x y : M) (hxy : c (x * y) 1) (hyx : c (y * x) 1), p ⟨x, y, c.Eq.2 hxy, c.Eq.2 hyx⟩) :
    p u := by
  rcases u with ⟨⟨x⟩, ⟨y⟩, h₁, h₂⟩
  exact H x y (c.eq.1 h₁) (c.eq.1 h₂)
#align con.induction_on_units Con.induction_on_units
#align add_con.induction_on_add_units AddCon.induction_on_addUnits

end Units

section Actions

/- warning: con.has_smul -> Con.smulinst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : SMul.{u1, u2} α M] [_inst_3 : IsScalarTower.{u1, u2, u2} α M M _inst_2 (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) _inst_2] (c : Con.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)), SMul.{u1, u2} α (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : SMul.{u1, u2} α M] [_inst_3 : IsScalarTower.{u1, u2, u2} α M M _inst_2 (Mul.toSMul.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) _inst_2] (c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_1)), SMul.{u1, u2} α (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_1) c)
Case conversion may be inaccurate. Consider using '#align con.has_smul Con.smulinstₓ'. -/
@[to_additive]
instance smulinst {α M : Type _} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) :
    SMul α c.Quotient where smul a := Quotient.map' ((· • ·) a) fun x y => c.smul a
#align con.has_smul Con.smulinst
#align add_con.has_vadd AddCon.smulinst

/- warning: con.coe_smul -> Con.coe_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : SMul.{u1, u2} α M] [_inst_3 : IsScalarTower.{u1, u2, u2} α M M _inst_2 (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) _inst_2] (c : Con.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (a : α) (x : M), Eq.{succ u2} (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) M (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c) (HasLiftT.mk.{succ u2, succ u2} M (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c) (CoeTCₓ.coe.{succ u2, succ u2} M (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c) (Con.Quotient.hasCoeT.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c))) (SMul.smul.{u1, u2} α M _inst_2 a x)) (SMul.smul.{u1, u2} α (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c) (Con.smulinst.{u1, u2} α M _inst_1 _inst_2 _inst_3 c) a ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) M (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c) (HasLiftT.mk.{succ u2, succ u2} M (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c) (CoeTCₓ.coe.{succ u2, succ u2} M (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c) (Con.Quotient.hasCoeT.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1) c))) x))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : SMul.{u2, u1} α M] [_inst_3 : IsScalarTower.{u2, u1, u1} α M M _inst_2 (Mul.toSMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) _inst_2] (c : Con.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (a : α) (x : M), Eq.{succ u1} (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c (HSMul.hSMul.{u2, u1, u1} α M M (instHSMul.{u2, u1} α M _inst_2) a x)) (HSMul.hSMul.{u2, u1, u1} α (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (instHSMul.{u2, u1} α (Con.Quotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c) (Con.smulinst.{u2, u1} α M _inst_1 _inst_2 _inst_3 c)) a (Con.toQuotient.{u1} M (MulOneClass.toMul.{u1} M _inst_1) c x))
Case conversion may be inaccurate. Consider using '#align con.coe_smul Con.coe_smulₓ'. -/
@[to_additive]
theorem coe_smul {α M : Type _} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) (a : α)
    (x : M) : (↑(a • x) : c.Quotient) = a • ↑x :=
  rfl
#align con.coe_smul Con.coe_smul
#align add_con.coe_vadd AddCon.coe_vadd

/- warning: con.mul_action -> Con.mulAction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulOneClass.{u2} M] [_inst_3 : MulAction.{u1, u2} α M _inst_1] [_inst_4 : IsScalarTower.{u1, u2, u2} α M M (MulAction.toHasSmul.{u1, u2} α M _inst_1 _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_2)) (MulAction.toHasSmul.{u1, u2} α M _inst_1 _inst_3)] (c : Con.{u2} M (MulOneClass.toHasMul.{u2} M _inst_2)), MulAction.{u1, u2} α (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M _inst_2) c) _inst_1
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulOneClass.{u2} M] [_inst_3 : MulAction.{u1, u2} α M _inst_1] [_inst_4 : IsScalarTower.{u1, u2, u2} α M M (MulAction.toSMul.{u1, u2} α M _inst_1 _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toMul.{u2} M _inst_2)) (MulAction.toSMul.{u1, u2} α M _inst_1 _inst_3)] (c : Con.{u2} M (MulOneClass.toMul.{u2} M _inst_2)), MulAction.{u1, u2} α (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M _inst_2) c) _inst_1
Case conversion may be inaccurate. Consider using '#align con.mul_action Con.mulActionₓ'. -/
@[to_additive]
instance mulAction {α M : Type _} [Monoid α] [MulOneClass M] [MulAction α M] [IsScalarTower α M M]
    (c : Con M) : MulAction α c.Quotient
    where
  smul := (· • ·)
  one_smul := Quotient.ind' fun x => congr_arg Quotient.mk'' <| one_smul _ _
  mul_smul a₁ a₂ := Quotient.ind' fun x => congr_arg Quotient.mk'' <| mul_smul _ _ _
#align con.mul_action Con.mulAction
#align add_con.add_action AddCon.addAction

/- warning: con.mul_distrib_mul_action -> Con.mulDistribMulAction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulDistribMulAction.{u1, u2} α M _inst_1 _inst_2] [_inst_4 : IsScalarTower.{u1, u2, u2} α M M (MulAction.toHasSmul.{u1, u2} α M _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} α M _inst_1 _inst_2 _inst_3)) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))) (MulAction.toHasSmul.{u1, u2} α M _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} α M _inst_1 _inst_2 _inst_3))] (c : Con.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))), MulDistribMulAction.{u1, u2} α (Con.Quotient.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) c) _inst_1 (Con.monoid.{u2} M _inst_2 c)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulDistribMulAction.{u1, u2} α M _inst_1 _inst_2] [_inst_4 : IsScalarTower.{u1, u2, u2} α M M (MulAction.toSMul.{u1, u2} α M _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} α M _inst_1 _inst_2 _inst_3)) (MulAction.toSMul.{u2, u2} M M _inst_2 (Monoid.toMulAction.{u2} M _inst_2)) (MulAction.toSMul.{u1, u2} α M _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} α M _inst_1 _inst_2 _inst_3))] (c : Con.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))), MulDistribMulAction.{u1, u2} α (Con.Quotient.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) c) _inst_1 (Con.monoid.{u2} M _inst_2 c)
Case conversion may be inaccurate. Consider using '#align con.mul_distrib_mul_action Con.mulDistribMulActionₓ'. -/
instance mulDistribMulAction {α M : Type _} [Monoid α] [Monoid M] [MulDistribMulAction α M]
    [IsScalarTower α M M] (c : Con M) : MulDistribMulAction α c.Quotient :=
  { c.MulAction with
    smul := (· • ·)
    smul_one := fun r => congr_arg Quotient.mk'' <| smul_one _
    smul_mul := fun r => Quotient.ind₂' fun m₁ m₂ => congr_arg Quotient.mk'' <| smul_mul' _ _ _ }
#align con.mul_distrib_mul_action Con.mulDistribMulAction

end Actions

end Con

