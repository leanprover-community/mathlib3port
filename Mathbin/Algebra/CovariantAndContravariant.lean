/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Order.Basic
import Mathbin.Order.Monotone

/-!

# Covariants and contravariants

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/467
> Any changes to this file require a corresponding PR to mathlib4.

This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.

The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `ordered_[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, `covariant_class` and
`contravariant_class`:

* `covariant_class` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `contravariant_class` models the implication `a * b < a * c → b < c`.

Since `co(ntra)variant_class` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.

The general approach is to formulate the lemma that you are interested in and prove it, with the
`ordered_[...]` typeclass of your liking.  After that, you convert the single typeclass,
say `[ordered_cancel_monoid M]`, into three typeclasses, e.g.
`[left_cancel_semigroup M] [partial_order M] [covariant_class M M (function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several co(ntra)variant_class assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[covariant_class M M (*) (≤)] [contravariant_class M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `covariant_class` uses the `(≤)`-relation, while
`contravariant_class` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[semigroup α] [partial_order α] [contravariant_class α α (*) (≤)] => left_cancel_semigroup α
```
holds -- note the `co*ntra*` assumption on the `(≤)`-relation.

# Formalization notes

We stick to the convention of using `function.swap (*)` (or `function.swap (+)`), for the
typeclass assumptions, since `function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use. -/


-- TODO: convert `has_exists_mul_of_le`, `has_exists_add_of_le`?
-- TODO: relationship with `con/add_con`
-- TODO: include equivalence of `left_cancel_semigroup` with
-- `semigroup partial_order contravariant_class α α (*) (≤)`?
-- TODO : use ⇒, as per Eric's suggestion?  See
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff/near/236148738
-- for a discussion.
open Function

section Variants

variable {M N : Type _} (μ : M → N → N) (r : N → N → Prop)

variable (M N)

#print Covariant /-
/-- `covariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `covariant_class` doc-string for its meaning. -/
def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)
#align covariant Covariant
-/

#print Contravariant /-
/-- `contravariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `contravariant_class` doc-string for its meaning. -/
def Contravariant : Prop :=
  ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂
#align contravariant Contravariant
-/

#print CovariantClass /-
/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`covariant_class` says that "the action `μ` preserves the relation `r`."

More precisely, the `covariant_class` is a class taking two Types `M N`, together with an "action"
`μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)`,
obtained from `(n₁, n₂)` by acting upon it by `m`.

If `m : M` and `h : r n₁ n₂`, then `covariant_class.elim m h : r (μ m n₁) (μ m n₂)`.
-/
@[protect_proj]
class CovariantClass : Prop where
  elim : Covariant M N μ r
#align covariant_class CovariantClass
-/

#print ContravariantClass /-
/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`contravariant_class` says that "if the result of the action `μ` on a pair satisfies the
relation `r`, then the initial pair satisfied the relation `r`."

More precisely, the `contravariant_class` is a class taking two Types `M N`, together with an
"action" `μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the
assertion that for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
`r` also holds for the pair `(n₁, n₂)`.

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `contravariant_class.elim m h : r n₁ n₂`.
-/
@[protect_proj]
class ContravariantClass : Prop where
  elim : Contravariant M N μ r
#align contravariant_class ContravariantClass
-/

/- warning: rel_iff_cov -> rel_iff_cov is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_1}) (N : Type.{u_2}) (μ : M -> N -> N) (r : N -> N -> Prop) [_inst_1 : CovariantClass.{u_1 u_2} M N μ r] [_inst_2 : ContravariantClass.{u_1 u_2} M N μ r] (m : M) {a : N} {b : N}, Iff (r (μ m a) (μ m b)) (r a b)
but is expected to have type
  forall (M : Type.{u_1}) (N : Type.{u_2}) (μ : M -> N -> N) (r : N -> N -> Prop) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.180 : CovariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.186 : ContravariantClass.{u_1 u_2} M N μ r] (m : M) {a : N} {b : N}, Iff (r (μ m a) (μ m b)) (r a b)
Case conversion may be inaccurate. Consider using '#align rel_iff_cov rel_iff_covₓ'. -/
theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  ⟨ContravariantClass.elim _, CovariantClass.elim _⟩
#align rel_iff_cov rel_iff_cov

section flip

variable {M N μ r}

/- warning: covariant.flip -> Covariant.flip is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Covariant.{u_1 u_2} M N μ r) -> (Covariant.{u_1 u_2} M N μ (flip.{succ u_2 succ u_2 1} N N Prop r))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Covariant.{u_1 u_2} M N μ r) -> (Covariant.{u_1 u_2} M N μ (flip.{succ u_2 succ u_2 1} N N Prop r))
Case conversion may be inaccurate. Consider using '#align covariant.flip Covariant.flipₓ'. -/
theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) := fun a b c hbc => h a hbc
#align covariant.flip Covariant.flip

/- warning: contravariant.flip -> Contravariant.flip is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Contravariant.{u_1 u_2} M N μ r) -> (Contravariant.{u_1 u_2} M N μ (flip.{succ u_2 succ u_2 1} N N Prop r))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Contravariant.{u_1 u_2} M N μ r) -> (Contravariant.{u_1 u_2} M N μ (flip.{succ u_2 succ u_2 1} N N Prop r))
Case conversion may be inaccurate. Consider using '#align contravariant.flip Contravariant.flipₓ'. -/
theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) := fun a b c hbc => h a hbc
#align contravariant.flip Contravariant.flip

end flip

section Covariant

variable {M N μ r} [CovariantClass M N μ r]

#print act_rel_act_of_rel /-
theorem act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  CovariantClass.elim _ ab
#align act_rel_act_of_rel act_rel_act_of_rel
-/

/- warning: group.covariant_iff_contravariant -> Group.covariant_iff_contravariant is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} [_inst_2 : Group.{u_2} N], Iff (Covariant.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2)))))) r) (Contravariant.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2)))))) r)
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.405 : Group.{u_1} N], Iff (Covariant.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.417 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.419 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.405))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.417 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.419) r) (Contravariant.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.436 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.438 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.405))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.436 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.438) r)
Case conversion may be inaccurate. Consider using '#align group.covariant_iff_contravariant Group.covariant_iff_contravariantₓ'. -/
@[to_additive]
theorem Group.covariant_iff_contravariant [Group N] : Covariant N N (· * ·) r ↔ Contravariant N N (· * ·) r := by
  refine' ⟨fun h a b c bc => _, fun h a b c bc => _⟩
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c]
    exact h a⁻¹ bc
    
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc
    exact h a⁻¹ bc
    
#align group.covariant_iff_contravariant Group.covariant_iff_contravariant

/- warning: group.covconv -> Group.covconv is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} [_inst_2 : Group.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2)))))) r], ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2)))))) r
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.584 : Group.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.587 : CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.594 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.596 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.584))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.594 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.596) r], ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.613 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.615 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.584))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.613 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.615) r
Case conversion may be inaccurate. Consider using '#align group.covconv Group.covconvₓ'. -/
@[to_additive]
instance (priority := 100) Group.covconv [Group N] [CovariantClass N N (· * ·) r] : ContravariantClass N N (· * ·) r :=
  ⟨Group.covariant_iff_contravariant.mp CovariantClass.elim⟩
#align group.covconv Group.covconv

/- warning: group.covariant_swap_iff_contravariant_swap -> Group.covariant_swap_iff_contravariant_swap is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} [_inst_2 : Group.{u_2} N], Iff (Covariant.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r) (Contravariant.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r)
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.654 : Group.{u_1} N], Iff (Covariant.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.42 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.40 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.669 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.671 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.654))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.669 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.671)) r) (Contravariant.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.76 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.74 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.691 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.693 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.654))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.691 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.693)) r)
Case conversion may be inaccurate. Consider using '#align group.covariant_swap_iff_contravariant_swap Group.covariant_swap_iff_contravariant_swapₓ'. -/
@[to_additive]
theorem Group.covariant_swap_iff_contravariant_swap [Group N] :
    Covariant N N (swap (· * ·)) r ↔ Contravariant N N (swap (· * ·)) r := by
  refine' ⟨fun h a b c bc => _, fun h a b c bc => _⟩
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a]
    exact h a⁻¹ bc
    
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a] at bc
    exact h a⁻¹ bc
    
#align group.covariant_swap_iff_contravariant_swap Group.covariant_swap_iff_contravariant_swap

/- warning: group.covconv_swap -> Group.covconv_swap is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} [_inst_2 : Group.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r], ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.839 : Group.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.842 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.852 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.854 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.839))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.852 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.854)) r], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.874 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.876 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.839))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.874 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.876)) r
Case conversion may be inaccurate. Consider using '#align group.covconv_swap Group.covconv_swapₓ'. -/
@[to_additive]
instance (priority := 100) Group.covconv_swap [Group N] [CovariantClass N N (swap (· * ·)) r] :
    ContravariantClass N N (swap (· * ·)) r :=
  ⟨Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim⟩
#align group.covconv_swap Group.covconv_swap

section IsTrans

variable [IsTrans N r] (m n : M) {a b c d : N}

/- warning: act_rel_of_rel_of_act_rel -> act_rel_of_rel_of_act_rel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : CovariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r (μ m b) c) -> (r (μ m a) c)
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.944 : CovariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.950 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r (μ m b) c) -> (r (μ m a) c)
Case conversion may be inaccurate. Consider using '#align act_rel_of_rel_of_act_rel act_rel_of_rel_of_act_relₓ'. -/
--  Lemmas with 3 elements.
theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  trans (act_rel_act_of_rel m ab) rl
#align act_rel_of_rel_of_act_rel act_rel_of_rel_of_act_rel

/- warning: rel_act_of_rel_of_rel_act -> rel_act_of_rel_of_rel_act is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : CovariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r c (μ m a)) -> (r c (μ m b))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1004 : CovariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1010 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r c (μ m a)) -> (r c (μ m b))
Case conversion may be inaccurate. Consider using '#align rel_act_of_rel_of_rel_act rel_act_of_rel_of_rel_actₓ'. -/
theorem rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  trans rr (act_rel_act_of_rel _ ab)
#align rel_act_of_rel_of_rel_act rel_act_of_rel_of_rel_act

end IsTrans

end Covariant

--  Lemma with 4 elements.
section MEqN

variable {M N μ r} {mu : N → N → N} [IsTrans N r] [CovariantClass N N mu r] [CovariantClass N N (swap mu) r]
  {a b c d : N}

/- warning: act_rel_act_of_rel_of_rel -> act_rel_act_of_rel_of_rel is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} {mu : N -> N -> N} [_inst_1 : IsTrans.{u_2} N r] [_inst_2 : CovariantClass.{u_2 u_2} N N mu r] [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) mu) r] {a : N} {b : N} {c : N} {d : N}, (r a b) -> (r c d) -> (r (mu a c) (mu b d))
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} {mu : N -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1124 : Trans.{0 0 0 succ u_1 succ u_1 succ u_1} N N N r r r] [i : CovariantClass.{u_1 u_1} N N mu r] [i' : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) mu) r] {a : N} {b : N} {c : N} {d : N}, (r a b) -> (r c d) -> (r (mu a c) (mu b d))
Case conversion may be inaccurate. Consider using '#align act_rel_act_of_rel_of_rel act_rel_act_of_rel_of_relₓ'. -/
theorem act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) :=
  trans (act_rel_act_of_rel c ab : _) (act_rel_act_of_rel b cd)
#align act_rel_act_of_rel_of_rel act_rel_act_of_rel_of_rel

end MEqN

section Contravariant

variable {M N μ r} [ContravariantClass M N μ r]

#print rel_of_act_rel_act /-
theorem rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b :=
  ContravariantClass.elim _ ab
#align rel_of_act_rel_act rel_of_act_rel_act
-/

section IsTrans

variable [IsTrans N r] (m n : M) {a b c d : N}

/- warning: act_rel_of_act_rel_of_rel_act_rel -> act_rel_of_act_rel_of_rel_act_rel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : ContravariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) b) -> (r (μ m b) (μ m c)) -> (r (μ m a) c)
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1318 : ContravariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1324 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) b) -> (r (μ m b) (μ m c)) -> (r (μ m a) c)
Case conversion may be inaccurate. Consider using '#align act_rel_of_act_rel_of_rel_act_rel act_rel_of_act_rel_of_rel_act_relₓ'. -/
--  Lemmas with 3 elements.
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) : r (μ m a) c :=
  trans ab (rel_of_act_rel_act m rl)
#align act_rel_of_act_rel_of_rel_act_rel act_rel_of_act_rel_of_rel_act_rel

/- warning: rel_act_of_act_rel_act_of_rel_act -> rel_act_of_act_rel_act_of_rel_act is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : ContravariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) (μ m b)) -> (r b (μ m c)) -> (r a (μ m c))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1386 : ContravariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1392 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) (μ m b)) -> (r b (μ m c)) -> (r a (μ m c))
Case conversion may be inaccurate. Consider using '#align rel_act_of_act_rel_act_of_rel_act rel_act_of_act_rel_act_of_rel_actₓ'. -/
theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) : r a (μ m c) :=
  trans (rel_of_act_rel_act m ab) rr
#align rel_act_of_act_rel_act_of_rel_act rel_act_of_act_rel_act_of_rel_act

end IsTrans

end Contravariant

section Monotone

variable {α : Type _} {M N μ} [Preorder α] [Preorder N]

variable {f : N → α}

/- warning: covariant.monotone_of_const -> Covariant.monotone_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} [_inst_2 : Preorder.{u_2} N] [_inst_3 : CovariantClass.{u_1 u_2} M N μ (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))] (m : M), Monotone.{u_2 u_2} N N _inst_2 _inst_2 (μ m)
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1514 : Preorder.{u_2} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1520 : CovariantClass.{u_1 u_2} M N μ (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1528 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1530 : N) => LE.le.{u_2} N (Preorder.toLE.{u_2} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1514) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1528 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1530)] (m : M), Monotone.{u_2 u_2} N N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1514 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1514 (μ m)
Case conversion may be inaccurate. Consider using '#align covariant.monotone_of_const Covariant.monotone_of_constₓ'. -/
/-- The partial application of a constant to a covariant operator is monotone. -/
theorem Covariant.monotone_of_const [CovariantClass M N μ (· ≤ ·)] (m : M) : Monotone (μ m) := fun a b ha =>
  CovariantClass.elim m ha
#align covariant.monotone_of_const Covariant.monotone_of_const

/- warning: monotone.covariant_of_const -> Monotone.covariant_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [_inst_1 : Preorder.{u_3} α] [_inst_2 : Preorder.{u_2} N] {f : N -> α} [_inst_3 : CovariantClass.{u_1 u_2} M N μ (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))], (Monotone.{u_2 u_3} N α _inst_2 _inst_1 f) -> (forall (m : M), Monotone.{u_2 u_3} N α _inst_2 _inst_1 (fun (n : N) => f (μ m n)))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1574 : Preorder.{u_3} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1577 : Preorder.{u_2} N] {f : N -> α} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1583 : CovariantClass.{u_1 u_2} M N μ (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1591 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1593 : N) => LE.le.{u_2} N (Preorder.toLE.{u_2} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1577) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1591 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1593)], (Monotone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1577 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1574 f) -> (forall (m : M), Monotone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1577 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1574 (fun (n : N) => f (μ m n)))
Case conversion may be inaccurate. Consider using '#align monotone.covariant_of_const Monotone.covariant_of_constₓ'. -/
/-- A monotone function remains monotone when composed with the partial application
of a covariant operator. E.g., `∀ (m : ℕ), monotone f → monotone (λ n, f (m + n))`. -/
theorem Monotone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Monotone f) (m : M) :
    Monotone fun n => f (μ m n) :=
  hf.comp <| Covariant.monotone_of_const m
#align monotone.covariant_of_const Monotone.covariant_of_const

/- warning: monotone.covariant_of_const' -> Monotone.covariant_of_const' is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {α : Type.{u_3}} [_inst_1 : Preorder.{u_3} α] [_inst_2 : Preorder.{u_2} N] {f : N -> α} {μ : N -> N -> N} [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) μ) (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))], (Monotone.{u_2 u_3} N α _inst_2 _inst_1 f) -> (forall (m : N), Monotone.{u_2 u_3} N α _inst_2 _inst_1 (fun (n : N) => f (μ n m)))
but is expected to have type
  forall {N : Type.{u_1}} {α : Type.{u_2}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1647 : Preorder.{u_2} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1650 : Preorder.{u_1} N] {f : N -> α} {μ : N -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1661 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) μ) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1672 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1674 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1650) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1672 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1674)], (Monotone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1650 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1647 f) -> (forall (m : N), Monotone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1650 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1647 (fun (n : N) => f (μ n m)))
Case conversion may be inaccurate. Consider using '#align monotone.covariant_of_const' Monotone.covariant_of_const'ₓ'. -/
/-- Same as `monotone.covariant_of_const`, but with the constant on the other side of
the operator.  E.g., `∀ (m : ℕ), monotone f → monotone (λ n, f (n + m))`. -/
theorem Monotone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)] (hf : Monotone f) (m : N) :
    Monotone fun n => f (μ n m) :=
  hf.comp <| Covariant.monotone_of_const m
#align monotone.covariant_of_const' Monotone.covariant_of_const'

/- warning: antitone.covariant_of_const -> Antitone.covariant_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [_inst_1 : Preorder.{u_3} α] [_inst_2 : Preorder.{u_2} N] {f : N -> α} [_inst_3 : CovariantClass.{u_1 u_2} M N μ (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))], (Antitone.{u_2 u_3} N α _inst_2 _inst_1 f) -> (forall (m : M), Antitone.{u_2 u_3} N α _inst_2 _inst_1 (fun (n : N) => f (μ m n)))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1736 : Preorder.{u_3} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1739 : Preorder.{u_2} N] {f : N -> α} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1745 : CovariantClass.{u_1 u_2} M N μ (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1753 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1755 : N) => LE.le.{u_2} N (Preorder.toLE.{u_2} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1739) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1753 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1755)], (Antitone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1739 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1736 f) -> (forall (m : M), Antitone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1739 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1736 (fun (n : N) => f (μ m n)))
Case conversion may be inaccurate. Consider using '#align antitone.covariant_of_const Antitone.covariant_of_constₓ'. -/
/-- Dual of `monotone.covariant_of_const` -/
theorem Antitone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Antitone f) (m : M) :
    Antitone fun n => f (μ m n) :=
  hf.comp_monotone <| Covariant.monotone_of_const m
#align antitone.covariant_of_const Antitone.covariant_of_const

/- warning: antitone.covariant_of_const' -> Antitone.covariant_of_const' is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {α : Type.{u_3}} [_inst_1 : Preorder.{u_3} α] [_inst_2 : Preorder.{u_2} N] {f : N -> α} {μ : N -> N -> N} [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) μ) (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))], (Antitone.{u_2 u_3} N α _inst_2 _inst_1 f) -> (forall (m : N), Antitone.{u_2 u_3} N α _inst_2 _inst_1 (fun (n : N) => f (μ n m)))
but is expected to have type
  forall {N : Type.{u_1}} {α : Type.{u_2}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1801 : Preorder.{u_2} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1804 : Preorder.{u_1} N] {f : N -> α} {μ : N -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1815 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) μ) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1826 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1828 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1804) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1826 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1828)], (Antitone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1804 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1801 f) -> (forall (m : N), Antitone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1804 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1801 (fun (n : N) => f (μ n m)))
Case conversion may be inaccurate. Consider using '#align antitone.covariant_of_const' Antitone.covariant_of_const'ₓ'. -/
/-- Dual of `monotone.covariant_of_const'` -/
theorem Antitone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)] (hf : Antitone f) (m : N) :
    Antitone fun n => f (μ n m) :=
  hf.comp_monotone <| Covariant.monotone_of_const m
#align antitone.covariant_of_const' Antitone.covariant_of_const'

end Monotone

#print covariant_le_of_covariant_lt /-
theorem covariant_le_of_covariant_lt [PartialOrder N] : Covariant M N μ (· < ·) → Covariant M N μ (· ≤ ·) := by
  refine' fun h a b c bc => _
  rcases le_iff_eq_or_lt.mp bc with (rfl | bc)
  · exact rfl.le
    
  · exact (h _ bc).le
    
#align covariant_le_of_covariant_lt covariant_le_of_covariant_lt
-/

#print contravariant_lt_of_contravariant_le /-
theorem contravariant_lt_of_contravariant_le [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) → Contravariant M N μ (· < ·) := by
  refine' fun h a b c bc => lt_iff_le_and_ne.mpr ⟨h a bc.le, _⟩
  rintro rfl
  exact lt_irrefl _ bc
#align contravariant_lt_of_contravariant_le contravariant_lt_of_contravariant_le
-/

#print covariant_le_iff_contravariant_lt /-
theorem covariant_le_iff_contravariant_lt [LinearOrder N] : Covariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) :=
  ⟨fun h a b c bc => not_le.mp fun k => not_le.mpr bc (h _ k), fun h a b c bc =>
    not_lt.mp fun k => not_lt.mpr bc (h _ k)⟩
#align covariant_le_iff_contravariant_lt covariant_le_iff_contravariant_lt
-/

#print covariant_lt_iff_contravariant_le /-
theorem covariant_lt_iff_contravariant_le [LinearOrder N] : Covariant M N μ (· < ·) ↔ Contravariant M N μ (· ≤ ·) :=
  ⟨fun h a b c bc => not_lt.mp fun k => not_lt.mpr bc (h _ k), fun h a b c bc =>
    not_le.mp fun k => not_le.mpr bc (h _ k)⟩
#align covariant_lt_iff_contravariant_le covariant_lt_iff_contravariant_le
-/

/- warning: covariant_flip_mul_iff -> covariant_flip_mul_iff is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) (r : N -> N -> Prop) [_inst_1 : CommSemigroup.{u_2} N], Iff (Covariant.{u_2 u_2} N N (flip.{succ u_2 succ u_2 succ u_2} N N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) r) (Covariant.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) r)
but is expected to have type
  forall (N : Type.{u_1}) (r : N -> N -> Prop) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2322 : CommSemigroup.{u_1} N], Iff (Covariant.{u_1 u_1} N N (flip.{succ u_1 succ u_1 succ u_1} N N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2337 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2339 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2322))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2337 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2339)) r) (Covariant.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2356 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2358 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2322))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2356 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2358) r)
Case conversion may be inaccurate. Consider using '#align covariant_flip_mul_iff covariant_flip_mul_iffₓ'. -/
@[to_additive]
theorem covariant_flip_mul_iff [CommSemigroup N] : Covariant N N (flip (· * ·)) r ↔ Covariant N N (· * ·) r := by
  rw [IsSymmOp.flip_eq]
#align covariant_flip_mul_iff covariant_flip_mul_iff

/- warning: contravariant_flip_mul_iff -> contravariant_flip_mul_iff is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) (r : N -> N -> Prop) [_inst_1 : CommSemigroup.{u_2} N], Iff (Contravariant.{u_2 u_2} N N (flip.{succ u_2 succ u_2 succ u_2} N N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) r) (Contravariant.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) r)
but is expected to have type
  forall (N : Type.{u_1}) (r : N -> N -> Prop) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2410 : CommSemigroup.{u_1} N], Iff (Contravariant.{u_1 u_1} N N (flip.{succ u_1 succ u_1 succ u_1} N N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2425 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2427 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2410))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2425 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2427)) r) (Contravariant.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2444 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2446 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2410))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2444 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2446) r)
Case conversion may be inaccurate. Consider using '#align contravariant_flip_mul_iff contravariant_flip_mul_iffₓ'. -/
@[to_additive]
theorem contravariant_flip_mul_iff [CommSemigroup N] :
    Contravariant N N (flip (· * ·)) r ↔ Contravariant N N (· * ·) r := by rw [IsSymmOp.flip_eq]
#align contravariant_flip_mul_iff contravariant_flip_mul_iff

#print contravariant_mul_lt_of_covariant_mul_le /-
@[to_additive]
instance contravariant_mul_lt_of_covariant_mul_le [Mul N] [LinearOrder N] [CovariantClass N N (· * ·) (· ≤ ·)] :
    ContravariantClass N N (· * ·)
      (· < ·) where elim := (covariant_le_iff_contravariant_lt N N (· * ·)).mp CovariantClass.elim
#align contravariant_mul_lt_of_covariant_mul_le contravariant_mul_lt_of_covariant_mul_le
-/

#print covariant_mul_lt_of_contravariant_mul_le /-
@[to_additive]
instance covariant_mul_lt_of_contravariant_mul_le [Mul N] [LinearOrder N] [ContravariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (· * ·)
      (· < ·) where elim := (covariant_lt_iff_contravariant_le N N (· * ·)).mpr ContravariantClass.elim
#align covariant_mul_lt_of_contravariant_mul_le covariant_mul_lt_of_contravariant_mul_le
-/

/- warning: covariant_swap_mul_le_of_covariant_mul_le -> covariant_swap_mul_le_of_covariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : CommSemigroup.{u_2} N] [_inst_2 : LE.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N _inst_2)], CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) (LE.le.{u_2} N _inst_2)
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2724 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2727 : LE.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2730 : CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2737 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2739 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2724))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2737 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2739) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2752 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2754 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2727 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2752 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2754)], CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2773 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2775 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2724))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2773 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2775)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2788 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2790 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2727 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2788 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2790)
Case conversion may be inaccurate. Consider using '#align covariant_swap_mul_le_of_covariant_mul_le covariant_swap_mul_le_of_covariant_mul_leₓ'. -/
@[to_additive]
instance covariant_swap_mul_le_of_covariant_mul_le [CommSemigroup N] [LE N] [CovariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (swap (· * ·)) (· ≤ ·) where elim := (covariant_flip_mul_iff N (· ≤ ·)).mpr CovariantClass.elim
#align covariant_swap_mul_le_of_covariant_mul_le covariant_swap_mul_le_of_covariant_mul_le

/- warning: contravariant_swap_mul_le_of_contravariant_mul_le -> contravariant_swap_mul_le_of_contravariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : CommSemigroup.{u_2} N] [_inst_2 : LE.{u_2} N] [_inst_3 : ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N _inst_2)], ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) (LE.le.{u_2} N _inst_2)
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2839 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2842 : LE.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2845 : ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2852 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2854 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2839))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2852 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2854) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2867 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2869 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2842 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2867 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2869)], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2888 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2890 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2839))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2888 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2890)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2903 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2905 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2842 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2903 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2905)
Case conversion may be inaccurate. Consider using '#align contravariant_swap_mul_le_of_contravariant_mul_le contravariant_swap_mul_le_of_contravariant_mul_leₓ'. -/
@[to_additive]
instance contravariant_swap_mul_le_of_contravariant_mul_le [CommSemigroup N] [LE N]
    [ContravariantClass N N (· * ·) (· ≤ ·)] :
    ContravariantClass N N (swap (· * ·))
      (· ≤ ·) where elim := (contravariant_flip_mul_iff N (· ≤ ·)).mpr ContravariantClass.elim
#align contravariant_swap_mul_le_of_contravariant_mul_le contravariant_swap_mul_le_of_contravariant_mul_le

/- warning: contravariant_swap_mul_lt_of_contravariant_mul_lt -> contravariant_swap_mul_lt_of_contravariant_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : CommSemigroup.{u_2} N] [_inst_2 : LT.{u_2} N] [_inst_3 : ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) (LT.lt.{u_2} N _inst_2)], ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) (LT.lt.{u_2} N _inst_2)
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2954 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2957 : LT.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2960 : ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2967 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2969 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2954))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2967 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2969) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2982 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2984 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2957 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2982 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2984)], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3003 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3005 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2954))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3003 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3005)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3018 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3020 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2957 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3018 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3020)
Case conversion may be inaccurate. Consider using '#align contravariant_swap_mul_lt_of_contravariant_mul_lt contravariant_swap_mul_lt_of_contravariant_mul_ltₓ'. -/
@[to_additive]
instance contravariant_swap_mul_lt_of_contravariant_mul_lt [CommSemigroup N] [LT N]
    [ContravariantClass N N (· * ·) (· < ·)] :
    ContravariantClass N N (swap (· * ·))
      (· < ·) where elim := (contravariant_flip_mul_iff N (· < ·)).mpr ContravariantClass.elim
#align contravariant_swap_mul_lt_of_contravariant_mul_lt contravariant_swap_mul_lt_of_contravariant_mul_lt

/- warning: covariant_swap_mul_lt_of_covariant_mul_lt -> covariant_swap_mul_lt_of_covariant_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : CommSemigroup.{u_2} N] [_inst_2 : LT.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) (LT.lt.{u_2} N _inst_2)], CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) (LT.lt.{u_2} N _inst_2)
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3069 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3072 : LT.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3075 : CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3082 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3084 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3069))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3082 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3084) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3097 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3099 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3072 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3097 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3099)], CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3118 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3120 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3069))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3118 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3120)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3133 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3135 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3072 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3133 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3135)
Case conversion may be inaccurate. Consider using '#align covariant_swap_mul_lt_of_covariant_mul_lt covariant_swap_mul_lt_of_covariant_mul_ltₓ'. -/
@[to_additive]
instance covariant_swap_mul_lt_of_covariant_mul_lt [CommSemigroup N] [LT N] [CovariantClass N N (· * ·) (· < ·)] :
    CovariantClass N N (swap (· * ·)) (· < ·) where elim := (covariant_flip_mul_iff N (· < ·)).mpr CovariantClass.elim
#align covariant_swap_mul_lt_of_covariant_mul_lt covariant_swap_mul_lt_of_covariant_mul_lt

/- warning: left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le -> LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : LeftCancelSemigroup.{u_2} N] [_inst_2 : PartialOrder.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N (Preorder.toLE.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))], CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LT.lt.{u_2} N (Preorder.toLT.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3187 : LeftCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3190 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3193 : CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3200 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3202 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3187))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3200 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3202) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3215 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3217 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3190)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3215 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3217)], CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3233 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3235 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3187))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3233 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3235) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3248 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3250 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3190)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3248 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3250)
Case conversion may be inaccurate. Consider using '#align left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_leₓ'. -/
@[to_additive]
instance LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le [LeftCancelSemigroup N] [PartialOrder N]
    [CovariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (· * ·) (· < ·) where elim a b c bc := by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_right a).mpr cb⟩
#align
  left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le

/- warning: right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le -> RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : RightCancelSemigroup.{u_2} N] [_inst_2 : PartialOrder.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (RightCancelSemigroup.toSemigroup.{u_2} N _inst_1))))) (LE.le.{u_2} N (Preorder.toLE.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))], CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (RightCancelSemigroup.toSemigroup.{u_2} N _inst_1))))) (LT.lt.{u_2} N (Preorder.toLT.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3310 : RightCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3313 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3316 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3326 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3328 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3310))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3326 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3328)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3341 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3343 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3313)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3341 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3343)], CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3362 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3364 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3310))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3362 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3364)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3377 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3379 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3313)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3377 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3379)
Case conversion may be inaccurate. Consider using '#align right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_leₓ'. -/
@[to_additive]
instance RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le [RightCancelSemigroup N] [PartialOrder N]
    [CovariantClass N N (swap (· * ·)) (· ≤ ·)] :
    CovariantClass N N (swap (· * ·)) (· < ·) where elim a b c bc := by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_left a).mpr cb⟩
#align
  right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le

/- warning: left_cancel_semigroup.contravariant_mul_le_of_contravariant_mul_lt -> LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : LeftCancelSemigroup.{u_2} N] [_inst_2 : PartialOrder.{u_2} N] [_inst_3 : ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LT.lt.{u_2} N (Preorder.toLT.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))], ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N (Preorder.toLE.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3439 : LeftCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3442 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3445 : ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3452 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3454 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3439))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3452 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3454) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3467 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3469 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3442)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3467 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3469)], ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3485 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3487 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3439))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3485 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3487) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3500 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3502 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3442)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3500 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3502)
Case conversion may be inaccurate. Consider using '#align left_cancel_semigroup.contravariant_mul_le_of_contravariant_mul_lt LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_ltₓ'. -/
@[to_additive]
instance LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt [LeftCancelSemigroup N] [PartialOrder N]
    [ContravariantClass N N (· * ·) (· < ·)] :
    ContravariantClass N N (· * ·) (· ≤ ·) where elim a b c bc := by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_right_inj a).mp h).le
      
    · exact (ContravariantClass.elim _ h).le
      
#align
  left_cancel_semigroup.contravariant_mul_le_of_contravariant_mul_lt LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt

/- warning: right_cancel_semigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt -> RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : RightCancelSemigroup.{u_2} N] [_inst_2 : PartialOrder.{u_2} N] [_inst_3 : ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (RightCancelSemigroup.toSemigroup.{u_2} N _inst_1))))) (LT.lt.{u_2} N (Preorder.toLT.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))], ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (RightCancelSemigroup.toSemigroup.{u_2} N _inst_1))))) (LE.le.{u_2} N (Preorder.toLE.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3575 : RightCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3578 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3581 : ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3591 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3593 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3575))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3591 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3593)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3606 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3608 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3578)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3606 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3608)], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3627 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3629 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3575))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3627 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3629)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3642 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3644 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3578)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3642 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3644)
Case conversion may be inaccurate. Consider using '#align right_cancel_semigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_ltₓ'. -/
@[to_additive]
instance RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt [RightCancelSemigroup N]
    [PartialOrder N] [ContravariantClass N N (swap (· * ·)) (· < ·)] :
    ContravariantClass N N (swap (· * ·)) (· ≤ ·) where elim a b c bc := by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_left_inj a).mp h).le
      
    · exact (ContravariantClass.elim _ h).le
      
#align
  right_cancel_semigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt

end Variants

