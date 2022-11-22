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
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.409 : Group.{u_1} N], Iff (Covariant.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.421 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.423 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.409))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.421 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.423) r) (Contravariant.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.440 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.442 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.409))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.440 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.442) r)
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
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.592 : Group.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.595 : CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.602 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.604 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.592))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.602 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.604) r], ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.621 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.623 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.592))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.621 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.623) r
Case conversion may be inaccurate. Consider using '#align group.covconv Group.covconvₓ'. -/
@[to_additive]
instance (priority := 100) Group.covconv [Group N] [CovariantClass N N (· * ·) r] : ContravariantClass N N (· * ·) r :=
  ⟨Group.covariant_iff_contravariant.mp CovariantClass.elim⟩
#align group.covconv Group.covconv

/- warning: group.covariant_swap_iff_contravariant_swap -> Group.covariant_swap_iff_contravariant_swap is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} [_inst_2 : Group.{u_2} N], Iff (Covariant.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r) (Contravariant.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r)
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.662 : Group.{u_1} N], Iff (Covariant.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.42 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.40 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.677 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.679 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.662))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.677 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.679)) r) (Contravariant.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.76 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.74 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.699 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.701 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.662))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.699 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.701)) r)
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
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.851 : Group.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.854 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.864 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.866 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.851))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.864 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.866)) r], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.886 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.888 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.851))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.886 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.888)) r
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
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.956 : CovariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.962 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r (μ m b) c) -> (r (μ m a) c)
Case conversion may be inaccurate. Consider using '#align act_rel_of_rel_of_act_rel act_rel_of_rel_of_act_relₓ'. -/
--  Lemmas with 3 elements.
theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  trans (act_rel_act_of_rel m ab) rl
#align act_rel_of_rel_of_act_rel act_rel_of_rel_of_act_rel

/- warning: rel_act_of_rel_of_rel_act -> rel_act_of_rel_of_rel_act is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : CovariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r c (μ m a)) -> (r c (μ m b))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1016 : CovariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1022 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r c (μ m a)) -> (r c (μ m b))
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
  forall {N : Type.{u_1}} {r : N -> N -> Prop} {mu : N -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1136 : Trans.{0 0 0 succ u_1 succ u_1 succ u_1} N N N r r r] [i : CovariantClass.{u_1 u_1} N N mu r] [i' : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) mu) r] {a : N} {b : N} {c : N} {d : N}, (r a b) -> (r c d) -> (r (mu a c) (mu b d))
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
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1330 : ContravariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1336 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) b) -> (r (μ m b) (μ m c)) -> (r (μ m a) c)
Case conversion may be inaccurate. Consider using '#align act_rel_of_act_rel_of_rel_act_rel act_rel_of_act_rel_of_rel_act_relₓ'. -/
--  Lemmas with 3 elements.
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) : r (μ m a) c :=
  trans ab (rel_of_act_rel_act m rl)
#align act_rel_of_act_rel_of_rel_act_rel act_rel_of_act_rel_of_rel_act_rel

/- warning: rel_act_of_act_rel_act_of_rel_act -> rel_act_of_act_rel_act_of_rel_act is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : ContravariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) (μ m b)) -> (r b (μ m c)) -> (r a (μ m c))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1398 : ContravariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1404 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) (μ m b)) -> (r b (μ m c)) -> (r a (μ m c))
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
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1526 : Preorder.{u_2} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1532 : CovariantClass.{u_1 u_2} M N μ (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1540 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1542 : N) => LE.le.{u_2} N (Preorder.toLE.{u_2} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1526) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1540 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1542)] (m : M), Monotone.{u_2 u_2} N N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1526 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1526 (μ m)
Case conversion may be inaccurate. Consider using '#align covariant.monotone_of_const Covariant.monotone_of_constₓ'. -/
/-- The partial application of a constant to a covariant operator is monotone. -/
theorem Covariant.monotone_of_const [CovariantClass M N μ (· ≤ ·)] (m : M) : Monotone (μ m) := fun a b ha =>
  CovariantClass.elim m ha
#align covariant.monotone_of_const Covariant.monotone_of_const

/- warning: monotone.covariant_of_const -> Monotone.covariant_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [_inst_1 : Preorder.{u_3} α] [_inst_2 : Preorder.{u_2} N] {f : N -> α} [_inst_3 : CovariantClass.{u_1 u_2} M N μ (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))], (Monotone.{u_2 u_3} N α _inst_2 _inst_1 f) -> (forall (m : M), Monotone.{u_2 u_3} N α _inst_2 _inst_1 (fun (n : N) => f (μ m n)))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1588 : Preorder.{u_3} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1591 : Preorder.{u_2} N] {f : N -> α} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1597 : CovariantClass.{u_1 u_2} M N μ (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1605 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1607 : N) => LE.le.{u_2} N (Preorder.toLE.{u_2} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1591) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1605 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1607)], (Monotone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1591 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1588 f) -> (forall (m : M), Monotone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1591 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1588 (fun (n : N) => f (μ m n)))
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
  forall {N : Type.{u_1}} {α : Type.{u_2}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1665 : Preorder.{u_2} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1668 : Preorder.{u_1} N] {f : N -> α} {μ : N -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1679 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) μ) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1690 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1692 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1668) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1690 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1692)], (Monotone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1668 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1665 f) -> (forall (m : N), Monotone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1668 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1665 (fun (n : N) => f (μ n m)))
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
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1758 : Preorder.{u_3} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1761 : Preorder.{u_2} N] {f : N -> α} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1767 : CovariantClass.{u_1 u_2} M N μ (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1775 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1777 : N) => LE.le.{u_2} N (Preorder.toLE.{u_2} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1761) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1775 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1777)], (Antitone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1761 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1758 f) -> (forall (m : M), Antitone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1761 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1758 (fun (n : N) => f (μ m n)))
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
  forall {N : Type.{u_1}} {α : Type.{u_2}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1825 : Preorder.{u_2} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1828 : Preorder.{u_1} N] {f : N -> α} {μ : N -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1839 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) μ) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1850 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1852 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1828) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1850 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1852)], (Antitone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1828 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1825 f) -> (forall (m : N), Antitone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1828 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1825 (fun (n : N) => f (μ n m)))
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
  forall (N : Type.{u_1}) (r : N -> N -> Prop) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2370 : CommSemigroup.{u_1} N], Iff (Covariant.{u_1 u_1} N N (flip.{succ u_1 succ u_1 succ u_1} N N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2385 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2387 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2370))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2385 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2387)) r) (Covariant.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2404 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2406 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2370))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2404 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2406) r)
Case conversion may be inaccurate. Consider using '#align covariant_flip_mul_iff covariant_flip_mul_iffₓ'. -/
@[to_additive]
theorem covariant_flip_mul_iff [CommSemigroup N] : Covariant N N (flip (· * ·)) r ↔ Covariant N N (· * ·) r := by
  rw [IsSymmOp.flip_eq]
#align covariant_flip_mul_iff covariant_flip_mul_iff

/- warning: contravariant_flip_mul_iff -> contravariant_flip_mul_iff is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) (r : N -> N -> Prop) [_inst_1 : CommSemigroup.{u_2} N], Iff (Contravariant.{u_2 u_2} N N (flip.{succ u_2 succ u_2 succ u_2} N N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) r) (Contravariant.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) r)
but is expected to have type
  forall (N : Type.{u_1}) (r : N -> N -> Prop) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2458 : CommSemigroup.{u_1} N], Iff (Contravariant.{u_1 u_1} N N (flip.{succ u_1 succ u_1 succ u_1} N N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2473 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2475 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2458))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2473 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2475)) r) (Contravariant.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2492 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2494 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2458))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2492 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2494) r)
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
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2772 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2775 : LE.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2778 : CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2785 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2787 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2772))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2785 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2787) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2800 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2802 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2775 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2800 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2802)], CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2821 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2823 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2772))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2821 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2823)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2836 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2838 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2775 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2836 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2838)
Case conversion may be inaccurate. Consider using '#align covariant_swap_mul_le_of_covariant_mul_le covariant_swap_mul_le_of_covariant_mul_leₓ'. -/
@[to_additive]
instance covariant_swap_mul_le_of_covariant_mul_le [CommSemigroup N] [LE N] [CovariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (swap (· * ·)) (· ≤ ·) where elim := (covariant_flip_mul_iff N (· ≤ ·)).mpr CovariantClass.elim
#align covariant_swap_mul_le_of_covariant_mul_le covariant_swap_mul_le_of_covariant_mul_le

/- warning: contravariant_swap_mul_le_of_contravariant_mul_le -> contravariant_swap_mul_le_of_contravariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : CommSemigroup.{u_2} N] [_inst_2 : LE.{u_2} N] [_inst_3 : ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N _inst_2)], ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) (LE.le.{u_2} N _inst_2)
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2887 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2890 : LE.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2893 : ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2900 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2902 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2887))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2900 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2902) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2915 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2917 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2890 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2915 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2917)], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2936 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2938 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2887))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2936 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2938)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2951 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2953 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2890 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2951 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2953)
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
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3002 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3005 : LT.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3008 : ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3015 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3017 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3002))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3015 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3017) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3030 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3032 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3005 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3030 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3032)], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3051 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3053 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3002))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3051 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3053)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3066 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3068 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3005 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3066 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3068)
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
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3117 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3120 : LT.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3123 : CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3130 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3132 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3117))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3130 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3132) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3145 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3147 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3120 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3145 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3147)], CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3166 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3168 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3117))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3166 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3168)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3181 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3183 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3120 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3181 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3183)
Case conversion may be inaccurate. Consider using '#align covariant_swap_mul_lt_of_covariant_mul_lt covariant_swap_mul_lt_of_covariant_mul_ltₓ'. -/
@[to_additive]
instance covariant_swap_mul_lt_of_covariant_mul_lt [CommSemigroup N] [LT N] [CovariantClass N N (· * ·) (· < ·)] :
    CovariantClass N N (swap (· * ·)) (· < ·) where elim := (covariant_flip_mul_iff N (· < ·)).mpr CovariantClass.elim
#align covariant_swap_mul_lt_of_covariant_mul_lt covariant_swap_mul_lt_of_covariant_mul_lt

/- warning: left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le -> LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : LeftCancelSemigroup.{u_2} N] [_inst_2 : PartialOrder.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N (Preorder.toLE.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))], CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LT.lt.{u_2} N (Preorder.toLT.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3235 : LeftCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3238 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3241 : CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3248 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3250 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3235))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3248 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3250) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3263 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3265 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3238)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3263 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3265)], CovariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3281 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3283 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3235))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3281 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3283) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3296 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3298 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3238)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3296 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3298)
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
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3358 : RightCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3361 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3364 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3374 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3376 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3358))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3374 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3376)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3389 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3391 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3361)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3389 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3391)], CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3410 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3412 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3358))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3410 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3412)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3425 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3427 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3361)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3425 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3427)
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
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3487 : LeftCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3490 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3493 : ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3500 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3502 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3487))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3500 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3502) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3515 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3517 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3490)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3515 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3517)], ContravariantClass.{u_1 u_1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3533 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3535 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3487))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3533 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3535) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3548 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3550 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3490)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3548 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3550)
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
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3623 : RightCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3626 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3629 : ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3639 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3641 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3623))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3639 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3641)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3654 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3656 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3626)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3654 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3656)], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3675 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3677 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3623))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3675 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3677)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3690 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3692 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3626)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3690 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3692)
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

